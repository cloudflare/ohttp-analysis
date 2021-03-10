dnl Copyright (c) 2017-2021 Cloudflare, Inc.
dnl Licensed under the BSD-3-Clause license found in the LICENSE file or at https://opensource.org/licenses/BSD-3-Clause
changequote(<!,!>)
changecom(<!/*!>,<!*/!>)

include(msgs.m4i)
include(crypto.m4i)

theory OHTTP begin

builtins: diffie-hellman, hashing, symmetric-encryption, signing

functions: Expand/3, Extract/2, hmac/1, aead/4, decrypt/3, aead_verify/4

restriction Eq_check_succeed: "All x y #i. Eq(x,y) @ i ==> x = y"
restriction Neq_check_succeed: "All x y #i. Neq(x,y) @ i ==> not (x = y)"


/* The plaintext can be recovered with the key */
equations: decrypt(k, n, aead(k, n, a, p)) = p
/* The authentication can be checked with the key and AAD */
equations: aead_verify(k, n, a, aead(k, n, a, p)) = true

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
  [ !Pk($A, <~key_id, $kdf_id, $aead_id>, 'g'^~x)
  , Out(<~key_id, 'g'^~x>)
  , !Ltk($A,<~key_id,$kdf_id, $aead_id>, ~x)
  ]

/* The C_QueryGeneration rule simulates a client constructing a fresh request and sending it to the proxy */
rule C_QueryGeneration:
let
  gx = 'g'^~x
  kem_context = <gx, gy>
  dh = gy^~x

  shared_secret = ExtractAndExpand(dh, kem_context)
  info_hash = Labeled_Extract('blank', 'info_hash', 'request')

  nonce = KSNonce(shared_secret)
  key_id = ~key_id
  request = ~req
  
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
    /* This marks the source of the client's public key and the encrypted message. This allows Tamarin to reason about their construction. */
  , CQG_sources(gx, OHTTPEBody)
  , C_SS(gx, gy, shared_secret)
    /* C_QG signifies that the client successfully completed the request. */
  , C_QG($C, gx, $P, ~k, $T, gy, ~cid, request)
  ]->
  [ /* The ~cid is sent on the same encrypted channel as the OHTTP request. If the attacker can learn this value it means the channel has been compromised. */
    Out(senc(<~cid, OHTTPRequest>, ~k))
    /* C_ResponseHandler stores all the state the client needs to handle the response. */
  , C_ResponseHandler(request, $C, gx, $P, ~k, $T, gy, shared_secret)
  ]

/* The P_HandleQuery rule simulates a proxy forwarding a request from a client to a target. We assume that the link between the proxy and the target is unencrypted. This is a fault-preserving simplification. */ 
rule P_HandleQuery:
  [ KeyExS($C, $P, ~k)
  , In(senc(<cid, <OHTTPHeader, gx, opaque>>, ~k))
    /* The proxy consumes the target's 'certificate' to ensure that the target's key is unique. */
  , !Pk($T, SigAlgs, gy)
  , Fr(~ptid)
  ]
--[ /* The PHQ action is linked to the CQG_Sources action. Using a sources lemma, we can tell Tamarin that if there is a PHQ action then either the
       attacker constructed the reqeuest, or an honest client did. */
    PHQ(gx, opaque)
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

  kem_context = <gx, gy>
  dh = gx^~y

  shared_secret = ExtractAndExpand(dh, kem_context)
  info_hash = Labeled_Extract('blank', 'info_hash', 'request')

  nonce = KSNonce(shared_secret) 
  response_nonce = ~resp_nonce
  salt = <shared_secret, response_nonce>
  aead_secret = DeriveSecretsK(salt, request) 
  aead_nonce = DeriveSecretsN(salt, request)

  expected_aad = OHTTPHeader 
  response = ~resp
in
  [ In(<$T, OHTTPRequest>)
  , !Ltk($T, SigAlgs, ~y)
  , Fr(~ttid)
  , Fr(~resp)
  , Fr(~resp_nonce)
  ]
--[ /* This action ensures that the message decrypts correctly. 
       This requirement is also enforced by the rule's pattern matching, but we make it explicit here. */
    Eq(aead_verify(shared_secret, nonce, expected_aad, OHTTPEBody), true) 
    /* This action uniquely specifies the target completing the protcol. */
  , T_Done(~ttid)
  , T_SS(gx, gy, shared_secret)
  , T_Answer(~ttid, $T, gx, gy, request, response)
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
  ]->
  [ Out(senc(<nonce, opaque>, ~k)) ]

/* The C_HandleResponse rule simulates a client receiving a response. 
   As we are only examining the security of OHTTP here we simply parse the response and drop it. */
rule C_HandleResponse:
let
  request = ~request
  info_hash = Labeled_Extract('blank', 'info_hash', 'request')
  salt = <shared_secret, response_nonce>

  aead_secret = DeriveSecretsK(salt, request) 
  aead_nonce = DeriveSecretsN(salt, request)
in
  [ /* The client consumes its previous state. */
    C_ResponseHandler(request, $C, gx, $P, ~k,  $T, gy, shared_secret) 
  , In(senc(OHTTPResponse, ~k)) ]
--[ /* This action uniquely specifies the client completing the protcol. */
    C_Done(~request, response, $C, gx,  $T, gy)
    /* This action ensures that the message decrypts correctly. 
       This requirement is also enforced by the rule's pattern matching, but we make it explicit here. */
  , Eq(aead_verify(aead_secret, aead_nonce, 'blank', OHTTPRespEBody), true)
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
  [ In(aead(k, n, a1, p1))
  , In(aead(k, n, a2, p2))
  ]
--[ Neq(p1, p2)
  , ReuseNonce(k, n, p1, p2) ]->
  [ Out(p1) ]

/* This lemma is used by Tamarin's preprocessor to refine the outputs of the P_HandleQuery rule. 
   It can understood as "Either the inputs to the P_HandleQuery rule are from an honest client, or the attacker knew them before the rule was triggered." */
lemma CQG_sources[sources]:
  "All gx op #j. PHQ(gx, op)@j
==>
  (Ex #i. CQG_sources(gx, op)@i & #i < #j) |
  ((Ex #i. KU(gx)@i & #i < #j) &
   (Ex #i. KU(op)@i & #i < #j))"

/* This lemma is used by Tamarin's preprocessor to refine sources of AEADs.
   It can be understood as "Either the attacker knows the plaintext of the AEAD, or it was generated honestly by either the target or the client." */
lemma aead_sources[sources]:
  "All k n a p #j. KU(aead(k,n,a,p))@j
==>
  (Ex #i. KU(p)@i & #i < #j) |
  (Ex tid T gx gy req #i. T_Answer(tid, T, gx, gy, req, p)@i & #i < #j) |
  (Ex C gx P k T gy cid #i. C_QG(C, gx, P, k, T, gy, cid, p)@i & #i < #j)"

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

end 
