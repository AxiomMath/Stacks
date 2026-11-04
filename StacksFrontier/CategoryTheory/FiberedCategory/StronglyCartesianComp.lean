module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import StacksCore.Tactic.StacksAttribute

/-!
# Strongly cartesian morphisms compose along a composite functor (Stacks 09WU)

For a functor `p : 𝒳 ⥤ 𝒮`, Mathlib records "`φ` lies over `f`" by the `Prop`-valued class
`Functor.IsHomLift p f φ`, and "`φ` is a strongly cartesian lift of `f`" by
`Functor.IsStronglyCartesian p f φ`.  Stacks 09WU says that strong cartesianness is stable
under composing the two functors: if `θ` is strongly cartesian for `F : A ⥤ B` and its
image `F.map θ` is strongly cartesian for `G : B ⥤ C`, then `θ` is strongly cartesian for
`F ⋙ G`.

## Main results

* `CategoryTheory.Functor.IsStronglyCartesian.comp_functor`: if `θ` is a strongly cartesian lift
  of `φ` along `F` and `φ` is a strongly cartesian lift of `f` along `G`, then `θ` is a strongly
  cartesian lift of `f` along `F ⋙ G`.

## Implementation notes

`IsStronglyCartesian.comp_functor` is stated at arbitrary base morphisms `φ : b ⟶ F.obj a` and
`f : R ⟶ G.obj (F.obj a)` rather than at the canonical ones `F.map θ` and `G.map (F.map θ)`, which
are recovered by instantiating `φ := F.map θ` and `f := G.map (F.map θ)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {A B C : Type*} [Category A] [Category B] [Category C]

/-- If a morphism lifts `f` via `F ⋙ G`, then its image under `F` lifts `f` via `G`. -/
private lemma isHomLift_of_isHomLift_comp_left (F : A ⥤ B) (G : B ⥤ C) {a b : A}
    {S R : C} {f : S ⟶ R} (φ : a ⟶ b) [(F ⋙ G).IsHomLift f φ] :
    G.IsHomLift f (F.map φ) :=
  IsHomLift.of_fac G f (F.map φ)
    (IsHomLift.domain_eq (F ⋙ G) f φ)
    (IsHomLift.codomain_eq (F ⋙ G) f φ)
    (IsHomLift.fac (F ⋙ G) f φ)

/-- If `φ` lifts `β` via `F` and `β` lifts `g` via `G`, then `φ` lifts `g` via `F ⋙ G`. -/
private lemma isHomLift_comp_of_isHomLift (F : A ⥤ B) (G : B ⥤ C) {a a' : A} {b b' : B}
    {S R : C} (g : S ⟶ R) (β : b ⟶ b') (φ : a ⟶ a') (hF : F.IsHomLift β φ)
    (hG : G.IsHomLift g β) : (F ⋙ G).IsHomLift g φ := by
  obtain rfl : F.obj a = b := IsHomLift.domain_eq F β φ
  obtain rfl : F.obj a' = b' := IsHomLift.codomain_eq F β φ
  obtain rfl : G.obj (F.obj a) = S := IsHomLift.domain_eq G g β
  obtain rfl : G.obj (F.obj a') = R := IsHomLift.codomain_eq G g β
  rw [IsHomLift.eq_of_isHomLift G g β, IsHomLift.eq_of_isHomLift F β φ]
  exact CategoryTheory.IsHomLift.map (F ⋙ G) φ

/-- If `θ : a' ⟶ a` is a strongly cartesian lift of `φ : b ⟶ F.obj a` along `F : A ⥤ B`, and `φ`
is in turn a strongly cartesian lift of `f : R ⟶ G.obj (F.obj a)` along `G : B ⥤ C`, then `θ` is a
strongly cartesian lift of `f` along `F ⋙ G`.

Taking `φ := F.map θ` and `f := G.map (F.map θ)`: strong cartesianness of `θ` for `F` together with
strong cartesianness of `F.map θ` for `G` implies strong cartesianness of `θ` for `F ⋙ G`. -/
@[stacks 09WU]
lemma IsStronglyCartesian.comp_functor (F : A ⥤ B) (G : B ⥤ C)
    {a' a : A} {b : B} {R : C}
    (f : R ⟶ G.obj (F.obj a)) (φ : b ⟶ F.obj a) (θ : a' ⟶ a)
    [F.IsStronglyCartesian φ θ] [G.IsStronglyCartesian f φ] :
    (F ⋙ G).IsStronglyCartesian f θ where
  toIsHomLift := isHomLift_comp_of_isHomLift F G f φ θ inferInstance inferInstance
  universal_property' := fun {_} g φ' _ => by
    have : G.IsHomLift (g ≫ f) (F.map φ') := isHomLift_of_isHomLift_comp_left F G φ'
    obtain ⟨k, ⟨hGk, hkφ⟩, uniqK⟩ :=
      IsStronglyCartesian.universal_property G f φ g (g ≫ f) rfl (F.map φ')
    have : F.IsHomLift (k ≫ φ) φ' := hkφ ▸ inferInstance
    obtain ⟨χ, ⟨hFkχ, hχθ⟩, uniqχ⟩ :=
      IsStronglyCartesian.universal_property F φ θ k (k ≫ φ) rfl φ'
    refine ⟨χ, ⟨isHomLift_comp_of_isHomLift F G g k χ hFkχ hGk, hχθ⟩, ?_⟩
    rintro χ' ⟨hχ'comp, hχ'θ⟩
    have hGχ' : G.IsHomLift g (F.map χ') := isHomLift_of_isHomLift_comp_left F G χ'
    obtain rfl : F.obj a' = b := IsHomLift.domain_eq F φ θ
    have hFmap_eq_k : F.map χ' = k := uniqK (F.map χ') ⟨hGχ', by
      rw [IsHomLift.eq_of_isHomLift F φ θ, ← F.map_comp, hχ'θ]⟩
    exact uniqχ χ' ⟨IsHomLift.of_fac' F k χ' rfl rfl (by simp [hFmap_eq_k]), hχ'θ⟩

end CategoryTheory.Functor
