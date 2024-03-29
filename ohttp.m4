dnl Copyright (c) 2017-2021 Cloudflare, Inc.
dnl Licensed under the BSD-3-Clause license found in the LICENSE file or at https://opensource.org/licenses/BSD-3-Clause
changequote(<!,!>)
changecom(<!/*!>,<!*/!>)

include(msgs.m4i)
include(crypto.m4i)

theory OHTTP begin

builtins: diffie-hellman, hashing, symmetric-encryption, signing

functions: Expand/3, Extract/2, hmac/1, seal/4, open/4

restriction Eq_check_succeed: "All x y #i. Eq(x,y) @ i ==> x = y"
restriction Neq_check_succeed: "All x y #i. Neq(x,y) @ i ==> not (x = y)"
restriction VerifyPSKInputs_succeed: "All mode psk psk_id #i. VerifyPSKInputs(mode, psk, psk_id)@i ==> (((psk = DefaultPSK) & (psk_id = DefaultPSKID)) & mode = ModeBase) | ((not(psk = DefaultPSK) & not(psk_id = DefaultPSKID)) & mode = ModePSK)"

/* One shot aead property */
equations: open(k, n, a, seal(k, n, a, p)) = p

/* The Starter rule establishes an authentic shared key between two actors, and produces the KeyExI Fact, which the attacker can use to compromise said key. */
rule Starter:
  [ Fr(~kxy) ]
--[ Channel($X, $Y) ]->
  [ KeyExC($X, $Y, ~kxy)
  , KeyExS($X, $Y, ~kxy)
  , KeyExI($X, $Y, ~kxy)
  ]

/* The Generate_DH_key_pair rule simulates the PKI necessary for distributing the target's keys. */
rule Generate_DH_key_pair:
  [ Fr(~x)
  , Fr(~key_id)
  ]
-->
  [ !Pk($A, <~key_id, $kem_id, $kdf_id, $aead_id>, 'g'^~x)
  , Out(<~key_id, 'g'^~x>)
  , !Ltk($A, <~key_id, $kem_id, $kdf_id, $aead_id>, ~x)
  ]

/* The C_QueryGeneration rule simulates a client constructing a fresh request and sending it to the proxy */
rule C_QueryGeneration:
let
  x = ~x
  gx = 'g'^~x
  key_id = ~key_id
  request = ~req
  shared_secret = Encap_SS(gy, x)
  key = KeyScheduleS_Key(ModeBase, shared_secret, <!MessageInfo!>, DefaultPSK, DefaultPSKID)
  nonce = KeyScheduleS_Base_Nonce(ModeBase, shared_secret, <!MessageInfo!>, DefaultPSK, DefaultPSKID)
in
  [ KeyExC($C, $P, ~k)
  , !Pk($T, SigAlgs, gy)
  , Fr(~x)
  , Fr(~req)
    /* The ~cid, or connection id, represents the unique channel between the client and the proxy. */
  , Fr(~cid)
  ]
--[ /* The proxy and the target may not be the same entity. */
    Neq($P, $T)
  , MsgSource(senc(<~cid, OHTTPRequestS>, ~k), ~k, OHTTPRequestS)
  , SealSources(OHTTPEBody)
  , C_SS(gx, gy, shared_secret)
    /* C_QG signifies that the client successfully completed the request. */
  , C_QG($C, gx, $P, ~k, $T, gy, ~cid, request)
    /* This doesn't actually check anything. Inputs need to be from the message. */
  , VerifyPSKInputs(ModeBase, DefaultPSK, DefaultPSKID)
  ]->
  [ /* The ~cid is sent on the same encrypted channel as the OHTTP request. If the attacker can learn this value it means the channel has been compromised. */
    Out(senc(<~cid, OHTTPRequestS>, ~k))
    /* C_ResponseHandler stores all the state the client needs to handle the response. */
  , C_ResponseHandler(request, $C, gx, $P, ~k, $T, gy, shared_secret, MessageInfo)
  ]

/* The P_HandleQuery rule simulates a proxy forwarding a request from a client to a target. We assume that the link between the proxy and the target is unencrypted. This is a fault-preserving simplification. */
rule P_HandleQuery:
  [ KeyExS($C, $P, ~k)
  , In(senc(<cid, <OHTTPHeader, gx, opaque>>, ~k))
    /* The proxy consumes the target's 'certificate' to ensure that the target's key is unique. */
  , !Pk($T, SigAlgs, gy)
  , Fr(~ptid)
  ]
--[ /* The PHQ action is linked to the MsgSources action. Using a sources lemma, we can tell Tamarin that if there is a PHQ action then either the
       attacker constructed the reqeuest, or an honest actor did. */
    PHQ(senc(<cid, <OHTTPHeader, gx, opaque>>, ~k), gx, <OHTTPHeader, gx, opaque>)
  ]->
  [ /* The ~cid is stripped and the target's identity is added. */
    Out(<$T, <OHTTPHeader, gx, opaque>>)
    /* This Fact stores the proxy's state. */
  , P_ResponseHandler(~ptid, $C, $P, ~k)
  ]

/* The T_HandleQuery rule simulates a target receiving a request and sending a fresh response. */
rule T_HandleQuery:
let
  key_id = ~key_id
  gy = 'g'^~y
  shared_secret = Decap(gx, ~y)
  key = KeyScheduleR_Key(ModeBase, shared_secret, <!<!MessageInfo!>!>, DefaultPSK, DefaultPSKID)
  nonce = KeyScheduleR_Base_Nonce(ModeBase, shared_secret, <!<!MessageInfo!>!>, DefaultPSK, DefaultPSKID)
  exporter_secret = KeyScheduleR_Exporter_Secret(ModeBase, shared_secret, <!<!MessageInfo!>!>, DefaultPSK, DefaultPSKID)


  msg = ContextROpen(<!MessageInfo!>, seal(ckey, cnonce, aad, request), key, nonce)

  response = ~resp
  response_nonce = ~resp_nonce

  secret = ContextExport(MessageTypeRespStr, Nk, exporter_secret)
  prk = Extract(<!<gx, ~resp_nonce>!>, secret)
  aead_key = Expand(prk, KeyStr, Nk)
  aead_nonce = Expand(prk, NonceStr, Nn)
  ct = seal(aead_key, aead_nonce, EmptyStr, response)
in
  [ In(<$T, OHTTPRequestR>)
  , !Ltk($T, SigAlgs, ~y)
  , Fr(~ttid)
  , Fr(~resp)
  , Fr(~resp_nonce)
  ]
--[ /* This action ensures that the message decrypts correctly. */
    Eq(msg, request)
    /* This action uniquely specifies the target completing the protcol. */
  , T_Done(~ttid)
  , T_SS(gx, gy, shared_secret)
  , T_Answer(~ttid, $T, gx, gy, request, response)
  , VerifyPSKInputs(ModeBase, DefaultPSK, DefaultPSKID)
  , SealSources(OHTTPRespEBody)
  ]->
  [ Out(OHTTPResponse) ]

/* The P_HandleResponse rule simulates a proxy receiving a response and forwarding it to the client. */
rule P_HandleResponse:
  [ /* The proxy consumes its previous state. */
    P_ResponseHandler(~ptid, $C, $P, ~k)
  , In(<nonce, opaque>)
  ]
--[ /* This actions uniquely specifies the proxy completing the protocol. */
    P_Done(~ptid)
  , MsgSource(senc(<nonce, opaque>, ~k), ~k, opaque)
  ]->
  [ Out(senc(<nonce, opaque>, ~k)) ]

/* The C_HandleResponse rule simulates a client receiving a response.
   As we are only examining the security of OHTTP here we simply parse the response and drop it. */
rule C_HandleResponse:
let
  request = ~request
  secret = ContextExport(MessageTypeRespStr, Nk, KeyScheduleS_Exporter_Secret(ModeBase, shared_secret, <!MessageInfo!>, DefaultPSK, DefaultPSKID))
  prk = Extract(<!<gx, response_nonce>!>, secret)
  caead_key = Expand(prk, KeyStr, Nk)
  caead_nonce = Expand(prk, NonceStr, Nn)
  msg = open(caead_key, caead_nonce, EmptyStr, OHTTPRespEBody)
in
  [ /* The client consumes its previous state. */
    C_ResponseHandler(request, $C, gx, $P, ~k,  $T, gy, shared_secret, MessageInfo)
  , In(senc(OHTTPResponse, ~k)) ]
--[ /* This action uniquely specifies the client completing the protcol. */
    C_Done(~request, response, $C, gx,  $T, gy)
    /* This action ensures that the message decrypts correctly. */
  , Eq(msg, response)
  ]->
  []

/* This rule allows the attacker perform the RevSk action to reveal a connection handshake key. */
rule RevSK:
  [ KeyExI($X, $Y, ~kxy) ]
--[ RevSk(~kxy) ]->
  [ Out(~kxy) ]

/* This rule allows the attacker to perform the RevDH action to reveal a target's key share. */
rule RevDH:
  [ !Ltk($A,~key_id, ~x) ]
--[ RevDH($A, ~key_id, 'g'^~x) ]->
  [ Out(~x) ]

/* This rule allows an attacker to inject two AEAD encrypted blobs with the same key and nonce, but different plaintexts, and receive the plaintext of the left blob.
This is more powerful than the reality of such an attack, and thus if the protocol is secure against this more powerful attacker then we can be sure it is secure against a more realistic attacker. */
rule NonceReuse:
  [ In(seal(k, n, a1, p1))
  , In(seal(k, n, a2, p2))
  ]
--[ Neq(p1, p2)
  , NonceReuse(seal(k, n, a1, p1), p1)
  , ReuseNonce(k, n, p1, p2) ]->
  [ Out(p1) ]


lemma MsgSources[sources]:
  "(
    All nonce msg k gx #j.
      PHQ(senc(<nonce, msg>, k), gx, msg)@j
    ==>
      (Ex #i .
          MsgSource(senc(<nonce, msg>,k), k, msg)@i
        & #i < #j)
      |
      ((Ex #i #h.
          KU(gx)@h
        & #h < #j
        & KU(msg)@i
        & #i < #j))
  )
  &
  (
    All k n a p #j. NonceReuse(seal(k,n,a,p),p)@j
    ==>
      (Ex #i .
          SealSources(seal(k,n,a,p))@i
        & #i < #j)
      |
      (Ex #i .
          KU(p)@i
        & #i < #j)
  )
  "



/* This lemma is an existance lemma, and checks that it is possible for the protocol to complete.
   This reduces the risk that the model is satisfied trivially, because some bug renders it unable to run. */
lemma end_to_end:
  exists-trace
  "Ex req resp C gx T gy #i. C_Done(req, resp, C, gx, T, gy)@i"


/* This lemma states that if a target responds to a request then either it has derived the same shared secret, ss, as the client, or the attacker knew ss before the request arrived. */
lemma ss_match:
  "All gx gy ss #j. T_SS(gx, gy, ss)@j ==> (Ex #i. C_SS(gx, gy, ss)@i & #i < #j) | (Ex #i. KU(ss)@i & #i < #j)"

/* This lemma states that if the attacker learns the request then it must have previously compromised the target. */
lemma secret_request[reuse]:
  "All C gx P key T gy cid req #j #k.
    C_QG(C, gx, P, key, T, gy, cid, req)@j &
    KU(req)@k
==>
  (Ex sig_algs #i.
    RevDH(T, sig_algs, gy)@i &
    #i < #k)"

/* This lemma states that if the attacker learns the response, then either it compromised the target or it knew the request in advance. */
lemma secret_response:
  "All tid T gx gy req resp #j #k. T_Answer(tid, T, gx, gy, req, resp)@j &
    KU(resp)@k
  ==>
    (Ex sig_algs #i. RevDH(T, sig_algs, gy)@i & #i < #k) |
    (Ex #i. KU(req)@i & #i < #k)"


/* This lemma states that if the attacker learns the connection id then it must have previously compromised the proxy. */
lemma secret_cid[reuse]:
  "All C gx P key T gy cid req #j #k.
    C_QG(C, gx, P, key, T, gy, cid, req)@j &
    KU(cid)@k
==>
  (Ex #i. RevSk(key)@i & #i < #k)"


/* This lemma states that if the attacker learns both the connection id and the request then it must have previously compromised the target and the proxy. */
lemma request_binding:
  "All C gx P key T gy cid req #j #k #l.
    C_QG(C, gx, P, key, T, gy, cid, req)@j &
    KU(req)@k &
    KU(cid)@l
==>
  Ex sig_algs #h #i.
    RevDH(T, sig_algs, gy)@h &
    #h < #k &
    RevSk(key)@i &
    #i < #l"

/* This lemma states that if the client and target both complete the protocol then either they agree on
      the target's identity,
      the DH key shares,
      the request, and
      the response,
   or the attacker previously compromised the target. */
lemma consistency:
  "All req resp C gx T gy #j. C_Done(req, resp, C, gx, T, gy)@j
==>
  (Ex tid #i. T_Answer(tid, T, gx, gy, req, resp)@i & #i < #j) |
  (Ex sig_algs #i. RevDH(T, sig_algs, gy)@i & #i < #j)"

/* This lemma states that there is no way to have a Target produce two distinct
    responses with the same AEAD key and nonce */
lemma reach_nonce_reuse:
  "All ttid T gx gy query answer key n a #j #k.
    T_Answer(ttid, T, gx, gy, query, answer)@j &
    ReuseNonce(key, n, a, answer)@k ==>
  (Ex kid #i. RevDH(T, kid, gy)@i & #i < #k) |
  (Ex #i. KU(query)@i & #i < #k)"

end
