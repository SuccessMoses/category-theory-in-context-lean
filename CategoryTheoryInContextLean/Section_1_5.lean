import CategoryTheoryInContextLean.Section_1_4
/-!
# Category Theory in Context - Section 1.5

TODO : Some examples in section 1.5 of the book are not yt formalised.
-/

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

/--
The single non-identity arrow in the 𝟚 category.
-/
def nonidHom : (0 : Fin 2) ⟶ 1 := ()

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
  map_id := by aesop
  map_comp := by aesop

def i₁ : C ⥤ C × (Fin 2) where
  F X := (X, 1)
  homF f := (f, Category.id _)
  map_id := by aesop
  map_comp := by aesop

lemma i₀_obj (X : C) : i₀.F X = (X, 0) := rfl

lemma i₁_obj (X : C) : i₁.F X = (X, 1) := rfl

lemma i₀_map {X Y : C} (f : X ⟶ Y) : i₀.homF f = (f, 𝟙 _) := rfl

lemma i₁_map {X Y : C} (f : X ⟶ Y) : i₁.homF f = (f, 𝟙 _) := rfl

variable (F G : C ⥤ D)

/--
Lemma 1.5.1
Fixing a pair of parallel functors F, G : C ⥤ D, natural transformations α : F → G corressponds
bijectively to functors H : C × 𝟚 ⟶ D such that H restricts along i₀ and i₁ to the functors F and G,
and diagram (1.5.2) commutes.

Exercise 1.5.1 : Show the other direction and define the equivalence.
-/
def nattransToFunctor (H : C × (Fin 2) ⥤ D) : NaturalTransformation (i₀ ⋙ H) (i₁ ⋙ H) where
  arrow X := H.homF <| ((𝟙 X, nonidHom) : (X, (0 : Fin 2)) ⟶ (X, 1))
  naturality := by
    intro X Y f
    simp [comp_map, i₁_map, ←Functor.map_comp, i₀_map]
    apply congrArg _
    apply hom_ext
    · simp [comp_fst, comp_id f, id_comp f]
    simp [comp_snd, i₀_obj, i₁_obj, id_comp, comp_id]

instance : Category (C ⥤ D) where
  Hom := NaturalTransformation
  id F := {
    arrow X := 𝟙 _
    naturality f := by rw [id_comp, comp_id]
  }
  comp := sorry
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/--
Definition 1.5.4:
An equivalence of categories consists of functors `F : C → D`, `G : D → C` together with natural
isomorphisms `η : 𝟙 C ≅ F ⋙ G`, `ϵ : G ⋙ F ≅ 𝟭 D`.
-/
structure Equivalence (C : Type) [Category C] (D : Type) [Category D] where
  hom : C ⥤ D
  inv : D ⥤ C
  hom_inv_iso : 𝟭 C ≅ hom ⋙ inv
  inv_hom_iso : 𝟭 D ≅ inv ⋙ hom

-- TODO: Define `IsEquivalent C D`.

/-
Lemma 1.5.5. The notion of equivalence of categories defines an equivalence relation. In particular,
if C ≃ D and D ≃ E, then C ≃ E.

Proof : Exercise 1.5.vi
-/


/-
Example 1.5.6
-/


/-
Definition 1.5.7
-/
class Full (F : C ⥤ D) : Prop where
  map_surjective {X Y : C} : Function.Surjective (F.homF : (X ⟶ Y) → (F.F X ⟶ F.F Y))

class FaithFul (F : C ⥤ D) : Prop where
  map_injective {X Y : C} : Function.Injective (F.homF : (X ⟶ Y) → (F.F X ⟶ F.F Y))

class EssentiallySurjective (F : C ⥤ D) : Prop where
  mem (Y : D) : ∃ X, Nonempty (F.F X ≅ Y)

/-
Theorem 1.5.9
A functor defining an eqiuvalence of categories if full, faithful and essentially surjective on
objects. Assuming the axiom of choice, any functor with these properties defines an equivalence
of categories.
-/



end CategoryInContext
