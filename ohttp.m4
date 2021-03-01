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
  ]
--[ Neq($P, $T)
  , CQG_sources(gx, OHTTPEBody)
  , C_SS(gx, gy, shared_secret)
  ]->
  [ Out(senc(OHTTPRequest, ~k))
  , C_ResponseHandler(request, $C, gx, $P, ~k, $T, gy, shared_secret)
  ]

 
rule P_HandleQuery:
  [ KeyExS($C, $P, ~k)
  , In(senc(<OHTTPHeader, gx, opaque>, ~k))
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
  , T_Answer($T, gx, gy, request, response)
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


lemma CQG_sources[sources]:
  "All gx op #j. PHQ(gx, op)@j
==>
  (Ex #i. CQG_sources(gx, op)@i & #i < #j) |
  ((Ex #i. KU(gx)@i & #i < #j) &
   (Ex #i. KU(op)@i & #i < #j))"

lemma end_to_end:
  exists-trace
  "Ex req resp C gx T gy #i. C_Done(req, resp, C, gx, T, gy)@i"

lemma ss_match:
  "All gx gy ss #j. T_SS(gx, gy, ss)@j ==> (Ex #i. C_SS(gx, gy, ss)@i & #i < #j) | (Ex #i. KU(ss)@i & #i < #j)"
end 
