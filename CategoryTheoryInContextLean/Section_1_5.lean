import CategoryTheoryInContextLean.Section_1_4

namespace CategoryInContext
open Category

universe u

instance Category.walkingArrow : Category (Fin 2) where
  Hom X Y := match X, Y with
    | 0, 0 => Unit
    | 0, 1 => Unit
    | 1, 1 => Unit
    | 1, 0 => Empty
  id X := match X with
    | 0 => ()
    | 1 => ()
  comp {X Y Z} f g := match X, Y, Z with
    | 0, 0, 0 => ()
    | 1, 1, 1 => ()
    | 0, 0, 1 => ()
    | 0, 1, 1 => ()
  id_comp {X Y} f := by match X, Y with | 0, 0 | 0, 1 | 1, 1 => rfl
  comp_id {X Y} f := by match X, Y with | 0, 0 | 0, 1 | 1, 1 => rfl
  assoc {W X Y Z} f g h := by
    match W, X, Y, Z with
    | 0, 0, 0, 0 | 0, 0, 0, 1 | 0, 0, 1, 1 | 0, 1, 1, 1 | 1, 1, 1, 1 => rfl
