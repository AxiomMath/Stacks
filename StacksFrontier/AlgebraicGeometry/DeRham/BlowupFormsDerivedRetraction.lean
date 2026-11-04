module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Retracting the derived direct image of relative forms along a blowup

Let `S` be a scheme, let `f : X ⟶ S` be smooth, let `Z ⊆ X` be a closed subscheme which is
smooth over `S`, and let `b : X' ⟶ X` be the blowing up of `X` along `Z`.  For `a ≥ 0` there is
a canonical map

`Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}`

in `D(𝒪_X)`, and [Stacks, Tag 0G5J] asserts that it has a *unique* retraction.  This file
constructs that canonical map and reduces both halves of the assertion — existence and
uniqueness of the retraction — to the two inputs the source uses, each carried here as a
hypothesis.

## Main definitions

* `Stacks.DeRham.formsSingle`:  the sheaf `Ω^a_{X/S}` of relative differential `a`-forms,
  placed in degree `0` of `D(𝒪_X)`.
* `Stacks.DeRham.formsDerivedDirectImage`:  **the canonical map** `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}`
  in `D(𝒪_X)`, for an arbitrary morphism `b : X' ⟶ X` over `S`.
* `Stacks.DeRham.blowUpFormsDerivedDirectImage`:  the same map for `b` the blowing up of a
  quasi-coherent ideal sheaf, which is the map [Stacks, Tag 0G5J] is about.

## Main results

* `Stacks.DeRham.Retraction.eq_of_comp_eq_id`:  a morphism `u : A ⟶ B` of a pre-triangulated
  category has at most one retraction as soon as the third term `Z` of a distinguished triangle
  on `u` admits no nonzero morphism to `A`.
* `Stacks.DeRham.Retraction.exists_comp_eq_id_of_isIso_comp`:  `u` has a retraction as soon as
  it has an invertible factorization, i.e. there is `v : B ⟶ D` with `u ≫ v` invertible.  This
  is the route the source takes to existence.
* `Stacks.DeRham.Retraction.exists_comp_eq_id_of_hom_shift_eq_zero`:  a second, independent
  criterion for existence, from the vanishing of `Hom(Z⟦-1⟧, A)`.  The source does *not* use
  this one, and in the situation of [Stacks, Tag 0G5J] its hypothesis is not expected to hold:
  the Ext-vanishing available there stops one degree short.
* `Stacks.DeRham.Retraction.existsUnique_comp_eq_id`:  the two together.
* `Stacks.DeRham.existsUnique_blowUpFormsRetraction`:  **[Stacks, Tag 0G5J] granted its two
  inputs.**  See the next section.

## The two inputs

The two inputs of [Stacks, Tag 0G5J] appear as the hypotheses `hcone` and `hv` of
`Stacks.DeRham.existsUnique_blowUpFormsRetraction`.

* `hcone` — that the third term of a distinguished triangle on the canonical map admits no
  nonzero morphism to `Ω^a_{X/S}`.  The source obtains this from [Stacks, Tag 0FUU] part (3),
  which identifies `R^qb_*Ω^a_{X'/S}` with `i_*R^qp_*Ω^a_{E/S}` for `q ≥ 1`, together with the
  fibre-dimension vanishing of [Stacks, Tag 0E7D] and the Ext-vanishing of
  [Stacks, Tag 0G5I], which is
  `Stacks.RegularSequence.subsingleton_ext_pushforward_of_isRegularClosedImmersionOfCodim`.
  Tag 0FUU in turn rests on the étale-local input [Stacks, Tag 0FUR].
* `hv` — an invertible factorization of the canonical map.  The source produces it from the
  twist isomorphism
  `Ω^a_{X/S} ≅ Rb_*(b^*Ω^a_{X/S} ⊗ 𝒪_{X'}(Σ(N - m - 1)E_m))` of [Stacks, Tags 0G5G and 0G5H].

Nothing in this file is specific to the centre being smooth over `S`, and the two smoothness
hypotheses of the setting of [Stacks, Tag 0FUT] are carried on
`Stacks.DeRham.existsUnique_blowUpFormsRetraction` only to state it in the generality of the
source; the proof does not use them.

## Implementation notes

The canonical map is assembled from the *underived* comparison
`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`, which is `b_*` of the canonical map
`b^*Ω^a_{X/S} ⟶ Ω^a_{X'/S}` transposed along `b^* ⊣ b_*`, followed by the comparison
`b_*K ⟶ Rb_*K` belonging to the right-derived-functor structure of
`AlgebraicGeometry.schemeDerivedPushforward`, which is [Stacks, Tag 079W] read for a morphism of
schemes.  The two identifications of `K ↦ K[0]` with its homotopy-category and
cochain-complex spellings — `CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` and
`DerivedCategory.singleFunctorIsoCompQh` — are what make the composite type-check; no appeal to
reduced transparency is needed, because the bridge between `X.Modules` and
`SheafOfModules (ringSheaf X.toRingedSpace)` is made explicit by
`AlgebraicGeometry.pushforwardToDerivedCategory_scheme_eq` and the instances beside it.

`HasDerivedCategory.standard` is installed with a raised priority:  the import closure also
carries the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as a
global instance, and with both in play at equal priority instance search no longer resolves
`HasDerivedCategory.{u + 1} X.Modules`.

The three criteria of `Stacks.DeRham.Retraction` are stated for an arbitrary pre-triangulated
category, and the first of them — existence from an invertible factorization — for an arbitrary
category:  none of them sees the derived category of a scheme, and the hypothesis of each is
exactly one clause of the source's argument.  The third term of the triangle is taken as
explicit data `(Z, p, q)` rather than as a chosen cone, so that the statements apply to whatever
triangle a caller has in hand.

## References

* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0G5I](https://stacks.math.columbia.edu/tag/0G5I)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.DeRham.Retraction

/-! ### Retractions in a pre-triangulated category

A *retraction* of `u : A ⟶ B` is an `r : B ⟶ A` with `u ≫ r = 𝟙 A`.  The three statements
below are the two halves of [Stacks, Tag 0G5J] with all the geometry removed:  existence of a
retraction from an invertible factorization of `u`, uniqueness from a Hom-vanishing against the
third term of a distinguished triangle on `u`, and the two combined.
-/

section Category

variable {C : Type u} [Category.{v} C]

/-- **Existence of a retraction from an invertible factorization.**  If `u : A ⟶ B` factors
through `v : B ⟶ D` with `u ≫ v` invertible, then `v ≫ (u ≫ v)⁻¹` is a retraction of `u`.

This is how [Stacks, Tag 0G5J] produces its arrow:  there `u` is `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}`,
`v` is `Rb_*` of the inclusion of `Ω^a_{X'/S}` into its twist by the exceptional divisors, and
the invertibility of the composite is the content of [Stacks, Tags 0G5G and 0G5H]. -/
theorem exists_comp_eq_id_of_isIso_comp {A B D : C} (u : A ⟶ B) (v : B ⟶ D)
    (hv : IsIso (u ≫ v)) : ∃ r : B ⟶ A, u ≫ r = 𝟙 A :=
  ⟨v ≫ inv (u ≫ v), by rw [← Category.assoc, IsIso.hom_inv_id]⟩

end Category

section Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Uniqueness of a retraction.**  Let `A ⟶ B ⟶ Z ⟶ A⟦1⟧` be a distinguished triangle.  If
no nonzero morphism `Z ⟶ A` exists then `u = T.mor₁` has at most one retraction:  the difference
of two retractions kills `u`, hence factors through `Z` by exactness of `Hom(-, A)` on the
triangle, hence vanishes.

In [Stacks, Tag 0G5J] the vanishing of `Hom(Z, Ω^a_{X/S})` is the vanishing of
`Hom(τ_{≥1}Rb_*Ω^a_{X'/S}, Ω^a_{X/S})`, which the source deduces from [Stacks, Tag 0FUU]
part (3), [Stacks, Tag 0E7D] and [Stacks, Tag 0G5I]. -/
theorem eq_of_comp_eq_id {A B Z : C} {u : A ⟶ B} {p : B ⟶ Z} {q : Z ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk u p q ∈ distTriang C) (hvanish : ∀ g : Z ⟶ A, g = 0)
    {r r' : B ⟶ A} (hr : u ≫ r = 𝟙 A) (hr' : u ≫ r' = 𝟙 A) : r = r' := by
  obtain ⟨g, hg⟩ := (Triangle.mk u p q).yoneda_exact₂ hT (r - r')
    (by simpa only [Triangle.mk_mor₁, Preadditive.comp_sub, hr, hr'] using sub_self _)
  rw [hvanish g, comp_zero] at hg
  exact sub_eq_zero.mp hg

/-- **Existence of a retraction from a Hom-vanishing.**  Let `A ⟶ B ⟶ Z ⟶ A⟦1⟧` be a
distinguished triangle.  If no nonzero morphism `Z⟦-1⟧ ⟶ A` exists then `𝟙 A` lifts through
`u = T.mor₁`:  apply exactness of `Hom(-, A)` to the inverse rotation of the triangle.

This criterion is *not* the one [Stacks, Tag 0G5J] uses, and its hypothesis is not expected to
hold there:  the Ext-vanishing of [Stacks, Tag 0G5I] against a module pushed forward from a
regular immersion of codimension `c` covers degrees `< c`, while the top nonvanishing
`R^qb_*Ω^a_{X'/S}` sits in degree `c - 1`, so the shifted Hom-group is exactly one degree out of
range.  It is recorded because it is the other half of the long exact sequence and costs
nothing. -/
theorem exists_comp_eq_id_of_hom_shift_eq_zero {A B Z : C} {u : A ⟶ B} {p : B ⟶ Z}
    {q : Z ⟶ A⟦(1 : ℤ)⟧} (hT : Triangle.mk u p q ∈ distTriang C)
    (hvanish : ∀ g : Z⟦(-1 : ℤ)⟧ ⟶ A, g = 0) : ∃ r : B ⟶ A, u ≫ r = 𝟙 A := by
  obtain ⟨g, hg⟩ := (Triangle.mk u p q).invRotate.yoneda_exact₂
    (inv_rot_of_distTriang _ hT) (𝟙 A) (hvanish _)
  exact ⟨g, hg.symm⟩

/-- **A unique retraction.**  Combining the two criteria:  if `A ⟶ B ⟶ Z ⟶ A⟦1⟧` is a
distinguished triangle, no nonzero morphism `Z ⟶ A` exists, and `u = T.mor₁` has an invertible
factorization through some `v : B ⟶ D`, then `u` has exactly one retraction. -/
theorem existsUnique_comp_eq_id {A B Z D : C} {u : A ⟶ B} {p : B ⟶ Z} {q : Z ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk u p q ∈ distTriang C) (hvanish : ∀ g : Z ⟶ A, g = 0)
    (v : B ⟶ D) (hv : IsIso (u ≫ v)) : ∃! r : B ⟶ A, u ≫ r = 𝟙 A := by
  obtain ⟨r, hr⟩ := exists_comp_eq_id_of_isIso_comp u v hv
  exact ⟨r, hr, fun r' hr' => eq_of_comp_eq_id hT hvanish hr' hr⟩

end Triangulated

end Stacks.DeRham.Retraction

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

/-! ### The canonical map `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` in `D(𝒪_X)` -/

variable {S X X' : Scheme.{u}} (f : X ⟶ S) (b : X' ⟶ X)

/-- The sheaf `Ω^a_{X/S}` of relative differential `a`-forms of `f : X ⟶ S`, placed in degree
`0` of the derived category of `𝒪_X`-modules. -/
abbrev formsSingle (a : ℤ) : DerivedCategory X.Modules :=
  (DerivedCategory.singleFunctor X.Modules 0).obj
    (Scheme.Hom.relativeDifferentialForms f a)

/-- The derived direct image `Rb_*Ω^a_{X'/S}` along `b : X' ⟶ X` of the sheaf of relative
differential `a`-forms of `X'` over `S`, as an object of `D(𝒪_X)`.  Here `X'` carries the
structure morphism `b ≫ f` to the base. -/
abbrev formsDerivedDirectImageObj (a : ℤ) : DerivedCategory X.Modules :=
  (schemeDerivedPushforward b).obj (formsSingle (b ≫ f) a)

/-- **The canonical map `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` in `D(𝒪_X)`**, for a morphism
`b : X' ⟶ X` of schemes over `S`.

It is the underived comparison `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` of
`AlgebraicGeometry.Scheme.Hom.formsDirectImageComparison`, read in the derived category and
followed by the comparison `b_*(-) ⟶ Rb_*(-)` of the right-derived-functor structure of
`AlgebraicGeometry.schemeDerivedPushforward`.  The two identifications of `K ↦ K[0]` across the
homotopy category are what transport the one into the source of the other. -/
def formsDerivedDirectImage (a : ℤ) :
    formsSingle f a ⟶ formsDerivedDirectImageObj f b a :=
  let F := Scheme.Modules.pushforward b
  let N := Scheme.Hom.relativeDifferentialForms (b ≫ f) a
  (DerivedCategory.singleFunctor X.Modules 0).map
      (Scheme.Hom.formsDirectImageComparison b f a) ≫
    (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app (F.obj N) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategorySingleFunctor 0).inv.app N) ≫
    (schemeDerivedPushforwardUnit b).app
      ((HomotopyCategory.singleFunctor X'.Modules 0).obj N) ≫
    (schemeDerivedPushforward b).map
      ((DerivedCategory.singleFunctorIsoCompQh X'.Modules 0).inv.app N)

/-! ### The retraction along a blowup -/

variable (I : X.IdealSheafData)

/-- The derived direct image `Rb_*Ω^a_{X'/S}` for `b : X' ⟶ X` the blowing up of `X` along the
closed subscheme cut out by `I`. -/
abbrev blowUpFormsObj (a : ℤ) : DerivedCategory X.Modules :=
  formsDerivedDirectImageObj f (blowUpToBase I) a

/-- The canonical map `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` of `D(𝒪_X)` for `b : X' ⟶ X` the blowing up
of `X` along the closed subscheme cut out by `I`.  This is the arrow whose retraction
[Stacks, Tag 0G5J] is about. -/
abbrev blowUpFormsDerivedDirectImage (a : ℤ) : formsSingle f a ⟶ blowUpFormsObj f I a :=
  formsDerivedDirectImage f (blowUpToBase I) a

/-- **Stacks Project, Tag 0G5J**, granted its two inputs.  Let `f : X ⟶ S` be smooth, let
`I` cut out a closed subscheme of `X` smooth over `S`, and let `b : X' ⟶ X` be the blowing up of
`X` along it.  For `a ≥ 0` there is exactly one arrow `Rb_*Ω^a_{X'/S} ⟶ Ω^a_{X/S}` in `D(𝒪_X)`
whose composition with the canonical `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` is the identity, provided:

* `hcone`:  the third term `Z` of a distinguished triangle on the canonical map admits no
  nonzero morphism to `Ω^a_{X/S}`.  This is the hypothesis discharged in the source by
  [Stacks, Tag 0FUU] part (3), [Stacks, Tag 0E7D] and [Stacks, Tag 0G5I].
* `hv`:  an invertible factorization of the canonical map.  This is the hypothesis discharged in
  the source by the twist isomorphism of [Stacks, Tags 0G5G and 0G5H].

The two smoothness hypotheses are those of the setting of [Stacks, Tag 0FUT] and are not used by
the proof. -/
@[stacks 0G5J "both clauses reduced to the two inputs the source uses, for the canonical map \
Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S} in D(𝒪_X) constructed here. NOT proved: either input. `hcone` is \
the source's Tag 0FUU (3) + 0E7D + 0G5I vanishing, and Tag 0FUU is not proved here; `hv` is its \
twist isomorphism of Tags 0G5G and 0G5H, proved only for the coordinate model"]
theorem existsUnique_blowUpFormsRetraction [Smooth f] [Smooth (I.subschemeι ≫ f)] (a : ℕ)
    {Z : DerivedCategory X.Modules}
    {p : blowUpFormsObj f I (a : ℤ) ⟶ Z} {q : Z ⟶ (formsSingle f (a : ℤ))⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (blowUpFormsDerivedDirectImage f I (a : ℤ)) p q ∈
      distTriang (DerivedCategory X.Modules))
    (hcone : ∀ g : Z ⟶ formsSingle f (a : ℤ), g = 0)
    {D : DerivedCategory X.Modules} (v : blowUpFormsObj f I (a : ℤ) ⟶ D)
    (hv : IsIso (blowUpFormsDerivedDirectImage f I (a : ℤ) ≫ v)) :
    ∃! r : blowUpFormsObj f I (a : ℤ) ⟶ formsSingle f (a : ℤ),
      blowUpFormsDerivedDirectImage f I (a : ℤ) ≫ r = 𝟙 (formsSingle f (a : ℤ)) :=
  Retraction.existsUnique_comp_eq_id hT hcone v hv

end Stacks.DeRham

end
