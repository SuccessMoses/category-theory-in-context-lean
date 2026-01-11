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

def nonidHom : (0 : Fin 2) ⟶ 1 := ()

scoped infixr:26 " ⥤ " => Functor -- type as \func

variable {C : Type*} [Category C] {D : Type*} [Category D]

instance prod : Category (C × D) where
  Hom X Y := (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id X := ⟨𝟙 X.1, 𝟙 X.2⟩
  comp f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp f := sorry
  comp_id f := sorry
  assoc f g h := sorry

lemma hom_ext {X Y : C × D} {f g : X ⟶ Y} (h₁ : f.1 = g.1) (h₂ : f.2 = g.2) : f = g :=
  Prod.ext h₁ h₂

lemma comp_fst {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).1 = f.1 ≫ g.1 :=
rfl

lemma comp_snd {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).2 = f.2 ≫ g.2 :=
rfl

def i₀ : C ⥤ C × (Fin 2) where
  F X := (X, 0)
  homF f := (f, Category.id _)
  map_id := sorry
  map_comp := sorry

def i₁ : C ⥤ C × (Fin 2) where
  F X := (X, 1)
  homF f := (f, Category.id _)
  map_id := sorry
  map_comp := sorry

lemma i₀_obj (X : C) : i₀.F X = (X, 0) := rfl

lemma i₁_obj (X : C) : i₁.F X = (X, 1) := rfl

lemma i₀_map {X Y : C} (f : X ⟶ Y) : i₀.homF f = (f, 𝟙 _) := rfl

lemma i₁_map {X Y : C} (f : X ⟶ Y) : i₁.homF f = (f, 𝟙 _) := rfl

scoped infixr:81 " ⋙ " => Functor.comp -- type as \ggg

variable {E : Type*} [Category E]

lemma comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : C) : (F ⋙ G).F X = G.F (F.F X) := rfl

lemma comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
  (F ⋙ G).homF f = G.homF (F.homF f) := rfl

variable (F G : C ⥤ D)

def nattransToFunctor (H : C × (Fin 2) ⥤ D) : NaturalTransformation (i₀ ⋙ H) (i₁ ⋙ H) where
  arrow X := H.homF <| ((𝟙 X, nonidHom) : (X, (0 : Fin 2)) ⟶ (X, 1))
  naturality := by
    intro X Y f
    simp [comp_map, i₁_map, ←Functor.map_comp, i₀_map]
    apply congrArg _
    apply hom_ext
    · simp [comp_fst, comp_id f, id_comp f]
    simp [comp_snd, i₀_obj, i₁_obj, id_comp, comp_id]
