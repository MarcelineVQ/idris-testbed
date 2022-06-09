module Network.OAuth2

-- Authorization is not authentication. Authorization is the act of allowing
-- some agent to use certain resources, not making sure the agent is who they
-- say they are.

data ResourceOwner a = MkRO a
data ResourceServer a = MkRS a
data Client a = MkC a
data AuthorizationServer a = MkAS a

data State a = Request a | Grant a

{-
     +--------+                               +---------------+
     |        |--(A)- Authorization Request ->|   Resource    |
     |        |                               |     Owner     |
     |        |<-(B)-- Authorization Grant ---|               |
     |        |                               +---------------+
     |        |
     |        |                               +---------------+
     |        |--(C)-- Authorization Grant -->| Authorization |
     | Client |                               |     Server    |
     |        |<-(D)----- Access Token -------|               |
     |        |                               +---------------+
     |        |
     |        |                               +---------------+
     |        |--(E)----- Access Token ------>|    Resource   |
     |        |                               |     Server    |
     |        |<-(F)--- Protected Resource ---|               |
     +--------+                               +---------------+
-}

-- data ClientFlow : (a -> State b) -> a -> Type where
  -- ResGet : 