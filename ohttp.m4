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
  , Fr(~cid)
  ]
--[ Neq($P, $T)
  , CQG_sources(gx, OHTTPEBody)
  , C_SS(gx, gy, shared_secret)
  , C_QG($C, gx, $P, ~k, $T, gy, ~cid, request)
  ]->
  [ Out(senc(<~cid, OHTTPRequest>, ~k))
  , C_ResponseHandler(request, $C, gx, $P, ~k, $T, gy, shared_secret)
  ]

 
rule P_HandleQuery:
  [ KeyExS($C, $P, ~k)
  , In(senc(<cid, <OHTTPHeader, gx, opaque>>, ~k))
  , !Pk($T, SigAlgs, gy)
  , Fr(~ptid)
  ]
--[ PHQ(gx, opaque)  ]->
  [Out(<$T, <OHTTPHeader, gx, opaque>>)
  /* This Fact stores the proxy's state. */
  , P_ResponseHandler(~ptid, $C, $P, ~k)
  ]


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
--[ Eq(aead_verify(shared_secret, nonce, expected_aad, OHTTPEBody), true) 
  /* This action uniquely specifies the target completing the protcol. */
  , T_Done(~ttid)
  , T_SS(gx, gy, shared_secret)
  , T_Answer(~ttid, $T, gx, gy, request, response)
  ]->
  [ Out(OHTTPResponse) ]
  
rule P_HandleResponse:
  [ /* The proxy consumes its previous state. */
    P_ResponseHandler(~ptid, $C, $P, ~k) 
  , In(<nonce, opaque>)
  ]
--[ /* This actions uniquely specifies the proxy completing the protocol. */
    P_Done(~ptid) 
  ]->
  [ Out(senc(<nonce, opaque>, ~k)) ]


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
--[   /* This action uniquely specifies the client completing the protcol. */
    C_Done(~request, response, $C, gx,  $T, gy)
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

lemma CQG_sources[sources]:
  "All gx op #j. PHQ(gx, op)@j
==>
  (Ex #i. CQG_sources(gx, op)@i & #i < #j) |
  ((Ex #i. KU(gx)@i & #i < #j) &
   (Ex #i. KU(op)@i & #i < #j))"

lemma aead_sources[sources]:
  "All k n a p #j. KU(aead(k,n,a,p))@j
==>
  (Ex #i. KU(p)@i & #i < #j) |
  (Ex tid T gx gy req #i. T_Answer(tid, T, gx, gy, req, p)@i & #i < #j) |
  (Ex C gx P k T gy cid #i. C_QG(C, gx, P, k, T, gy, cid, p)@i & #i < #j)"

lemma end_to_end:
  exists-trace
  "Ex req resp C gx T gy #i. C_Done(req, resp, C, gx, T, gy)@i"

lemma ss_match:
  "All gx gy ss #j. T_SS(gx, gy, ss)@j ==> (Ex #i. C_SS(gx, gy, ss)@i & #i < #j) | (Ex #i. KU(ss)@i & #i < #j)"

lemma secret_request[reuse]:
  "All C gx P key T gy cid req #j #k.
    C_QG(C, gx, P, key, T, gy, cid, req)@j &
    KU(req)@k
==>
  (Ex sig_algs #i.
    RevDH(T, sig_algs, gy)@i &
    #i < #k)"

lemma secret_response:
  "All tid T gx gy req resp #j #k. T_Answer(tid, T, gx, gy, req, resp)@j &
    KU(resp)@k
  ==>
    (Ex sig_algs #i. RevDH(T, sig_algs, gy)@i & #i < #k) |
    (Ex #i. KU(req)@i & #i < #k)"


lemma secret_cid[reuse]:
  "All C gx P key T gy cid req #j #k.
    C_QG(C, gx, P, key, T, gy, cid, req)@j &
    KU(cid)@k
==>
  (Ex #i. RevSk(key)@i & #i < #k)"


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

lemma consistency:
  "All req resp C gx T gy #j. C_Done(req, resp, C, gx, T, gy)@j
==>
  (Ex tid #i. T_Answer(tid, T, gx, gy, req, resp)@i & #i < #j) |
  (Ex sig_algs #i. RevDH(T, sig_algs, gy)@i & #i < #j)"

end 
