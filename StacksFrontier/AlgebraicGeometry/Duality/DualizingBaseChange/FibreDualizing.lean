module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing

/-!
# The relative dualizing complex restricts to a dualizing complex on each fibre

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a flat morphism of
`AlgebraicGeometry.FTS S`, the category of schemes separated and of finite type over `S` of
[Stacks, Tag 0F42]. The relative dualizing complex of `f` is `ω^•_{X/Y} = f^!𝒪_Y`, where `f^!`
is `Stacks.Duality.upperShriek` ([Stacks, Tag 0A9Y]) and `𝒪_Y` is
`Stacks.Duality.DerivedPushforward.derivedStructureSheaf`; it lies in `D^b_Coh(𝒪_X)` by
[Stacks, Tag 0B6U] part (a),
`Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf`.

For `y ∈ Y` let `h = f.fiberι y : X_y ⟶ X` be the projection from the scheme-theoretic fibre
`X_y = X ×_Y Spec κ(y)` of `AlgebraicGeometry.Scheme.Hom.fiber`. That `Lh^*ω^•_{X/Y}` is a
dualizing complex on `X_y` is [Stacks, Tag 0BZZ] (Lemma 48.18.4); it is proved, with no
hypothesis beyond flatness, as
`Stacks.Duality.isDualizingComplex_derivedPullback_fibreι_upperShriek_unconditional` in
`StacksFrontier/AlgebraicGeometry/Duality/DualizingBaseChange/FibreDualizingCharts.lean`. This file
provides the objects that statement is written with, and the chart lemmas below.

## Main definitions

* `Stacks.Duality.HasFieldShriekModelOn` — the chart condition the source's proof produces: over
  an affine open `U` of a scheme, the complex is the associated sheaf of the *algebraic* upper
  shriek, along a polynomial presentation of a ring map out of a field `κ`, of `κ` placed in
  degree zero. This is `Stacks.Duality.HasDualizingModelOn` with the dualizing complex over
  `Γ(Z, U)` named as the algebraic upper shriek of the field, and with the requirement that it
  be dualizing *dropped* — nothing in it asserts that any complex is dualizing.

## Main results

* `Stacks.Duality.hasDualizingModelOn_of_hasFieldShriekModelOn` — such a chart is a dualizing
  chart. This is where all the content of this file sits: a field is its own dualizing complex,
  and [Stacks, Tag 0BZL] carries that to the algebraic upper shriek.
* `Stacks.Duality.isDualizingComplex_fieldModel` — a field, in degree zero, is a dualizing
  complex over itself.
* `Stacks.Duality.relativeDualizingComplexObj` — `ω^•_{X/Y} = f^!𝒪_Y` as an object of `D(𝒪_X)`.
* `Stacks.Duality.isLocallyNoetherian_fibre` — the fibre `X_y` is locally Noetherian.

## Implementation notes

*Noetherianness of `S`.* Situation 48.16.1 takes `S` Noetherian, and the section variable records
it; it is used to form `f^!`, whose construction asks for a quasi-compact quasi-separated base.

*The fibre.* `X_y` is Mathlib's `AlgebraicGeometry.Scheme.Hom.fiber`, so `h` is literally the
source's projection and no cartesian square has to be assumed. The fibre is not placed in
`AlgebraicGeometry.FTS` of anything: `Spec κ(y) ⟶ Y` is of finite type only when `{y}` is closed
([Stacks, Tag 01TB]), whereas `X_y ⟶ Spec κ(y)` is of finite type for every `y` by base change,
and that is what `Stacks.Duality.isLocallyNoetherian_fibre`, proved here, uses.

*The derived categories.* `Stacks.Duality.upperShriek` lives at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and so therefore does `Lh^*ω^•_{X/Y}`.
`Stacks.Duality.IsDualizingComplex` carries a free `HasDerivedCategory` binder, so it is read at
that same model and nothing has to be transported. The two derived categories that
`Stacks.Duality.HasDualizingModelOn` seals inside its body, `D(𝒪_U)` and `D(Γ(Z, U))`, are at
`CategoryTheory.HasDerivedCategory.standard`; `Stacks.Duality.HasFieldShriekModelOn` seals the
same two, together with `D(κ)`, so that the two conditions compose.

## References

* [Stacks Project, Tag 0BZZ](https://stacks.math.columbia.edu/tag/0BZZ)
* [Stacks Project, Tag 0BZY](https://stacks.math.columbia.edu/tag/0BZY)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
* [Stacks Project, Tag 0DW7](https://stacks.math.columbia.edu/tag/0DW7)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] HasDerivedCategory.standard
attribute [local instance 10000] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

universe u w

namespace Stacks.Duality

open DerivedPushforward

/-! ### A field is its own dualizing complex -/

/-- **A field, in degree zero, is a dualizing complex over itself.** A field is a regular local
ring, hence Gorenstein by [Stacks, Tag 0AWX], and being Gorenstein local *is* the
assertion that the ring in degree zero is dualizing, by the definition of
`Dualizing.IsGorensteinLocalRing` as [Stacks, Tag 0DW7] (1). -/
theorem isDualizingComplex_fieldModel (κ : Type u) [Field κ] :
    Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} κ) 0).obj (ModuleCat.of κ κ)) :=
  Dualizing.IsRegularLocalRing.isGorensteinLocalRing κ

/-! ### Chart models by the algebraic upper shriek of a field -/

section FieldChart

variable {Z : Scheme.{u}} [IsLocallyNoetherian Z] [HasDerivedCategory.{w} Z.Modules]

/-- An affine open `U` of a locally Noetherian scheme carries a *field shriek model* of
`K ∈ D(𝒪_Z)` over the field `κ` when `K|_U`, transported along `U ≅ Spec Γ(Z, U)`, is the
associated sheaf of the algebraic upper shriek, along a polynomial presentation of some ring map
`κ →+* Γ(Z, U)`, of `κ` placed in degree zero.

This is `Stacks.Duality.HasDualizingModelOn` with the model over `Γ(Z, U)` named as that upper
shriek and with the requirement that it be dualizing dropped: the condition asserts only that an
isomorphism exists. That the named model *is* dualizing is
`Stacks.Duality.hasDualizingModelOn_of_hasFieldShriekModelOn`.

The three derived categories not appearing in the type are introduced at
`CategoryTheory.HasDerivedCategory.standard`, matching the choice sealed inside the body of
`Stacks.Duality.HasDualizingModelOn`. -/
def HasFieldShriekModelOn (κ : Type u) [Field κ] (K : DerivedCategory Z.Modules) (U : Z.Opens)
    (hU : IsAffineOpen U) : Prop :=
  letI : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := HasDerivedCategory.standard U.toScheme.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(Z, U))
  letI := HasDerivedCategory.standard (ModuleCat.{u} κ)
  ∃ (φ : κ →+* Γ(Z, U)) (p : Dualizing.PolynomialPresentation φ),
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (tilde.functor Γ(Z, U) ⋙
        Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
          (p.upperShriekFunctor.{u, u}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} κ) 0).obj (ModuleCat.of κ κ))))

/-- **A field shriek model is a dualizing model.** The field `κ` in degree zero is a dualizing
complex over `κ` by `Stacks.Duality.isDualizingComplex_fieldModel`, and
[Stacks, Tag 0BZL] says the algebraic upper shriek along a finite type homomorphism of Noetherian
rings carries a dualizing complex to a dualizing complex; so the model named by
`Stacks.Duality.HasFieldShriekModelOn` is dualizing over `Γ(Z, U)`. -/
theorem hasDualizingModelOn_of_hasFieldShriekModelOn (κ : Type u) [Field κ]
    {K : DerivedCategory Z.Modules} {U : Z.Opens} {hU : IsAffineOpen U}
    (h : HasFieldShriekModelOn κ K U hU) :
    HasDualizingModelOn K U hU := by
  let : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Z, U))
  let := HasDerivedCategory.standard (ModuleCat.{u} κ)
  obtain ⟨φ, p, he⟩ := h
  exact ⟨_, Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex p _
    (isDualizingComplex_fieldModel κ), he⟩

end FieldChart

/-! ### The fibre of a morphism of `FTS S` is locally Noetherian -/

section Fibre

variable {S : Scheme.{u}} {X Y : AlgebraicGeometry.FTS S}

/-- A morphism of `AlgebraicGeometry.FTS S` is locally of finite type: it is a morphism over `S`
whose source is of finite type over `S`, and finite type descends along a composite. -/
theorem locallyOfFiniteType_left (f : X ⟶ Y) : LocallyOfFiniteType f.left := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [MorphismProperty.Over.w f]
    exact AlgebraicGeometry.FTS.locallyOfFiniteType_hom X
  exact locallyOfFiniteType_of_comp f.left Y.hom

/-- **The scheme-theoretic fibre of a morphism of `AlgebraicGeometry.FTS S` is locally
Noetherian.** The fibre is of finite type over `Spec κ(y)` because finite type is stable under
base change, and `κ(y)` is a field, hence a Noetherian ring. -/
instance isLocallyNoetherian_fibre (f : X ⟶ Y) (y : Y.left) :
    IsLocallyNoetherian (f.left.fiber y) := by
  have := locallyOfFiniteType_left f
  have : LocallyOfFiniteType (f.left.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType
      (Limits.pullback.snd f.left (Y.left.fromSpecResidueField y)))
  exact LocallyOfFiniteType.isLocallyNoetherian (f.left.fiberToSpecResidueField y)

end Fibre

/-! ### The relative dualizing complex -/

section Shriek

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)
  (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- The relative dualizing complex `ω^•_{X/Y} = f^!𝒪_Y` of a morphism of
`AlgebraicGeometry.FTS S`, as an object of `D(𝒪_X)`. By [Stacks, Tag 0B6U] part (a) it
lies in `D^b_Coh(𝒪_X)` when `f` is flat and of finite presentation. -/
abbrev relativeDualizingComplexObj : DerivedCategory X.left.Modules :=
  ((upperShriek f j).obj (derivedStructureSheaf Y.left)).obj

end Shriek

end Stacks.Duality

end
