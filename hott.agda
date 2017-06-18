-- CHAPTER 1. Type theory

-- SECTION 1.4. Dependent function types
-- The identity function is a polymorphic function
id : {A : Set} -> A -> A
id a = a

-- Swapping function
swap : {A B C : Set} -> (A -> B -> C) -> (B -> A -> C)
swap f y x = f x y


-- SECTION 1.5. Product types
rec-prod : {A B : Set} -> {C : Set} -> (A -> B -> C) -> (A,B) -> C
rec-prod = ?
