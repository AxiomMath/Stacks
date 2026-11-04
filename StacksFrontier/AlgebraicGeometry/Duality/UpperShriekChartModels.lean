module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelowPlus
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing

/-!
# Affine models of a complex at any derived model, and dualizing complexes from charts

Let `f : X ⟶ Y` be a morphism of schemes separated and of finite type over a Noetherian base,
that is, a morphism of the category `AlgebraicGeometry.FTS` of [Stacks, Tag 0F42], and let `K`
be a dualizing complex on `Y`. The proof of [Stacks, Tag 0AA3] (Lemma 48.17.7) shows that `f^!K`
is dualizing by computing it on affine charts: over an affine `V ⊆ Y` and an affine
`U ⊆ f⁻¹(V)` it is the associated sheaf of the algebraic upper shriek, along a polynomial
presentation of `Γ(Y, V) → Γ(X, U)`, of a model of `K` on `V` ([Stacks, Tag 0BV2]); and the
algebraic upper shriek of a dualizing complex is dualizing ([Stacks, Tag 0BZL]).

This file proves the second half of that argument for an arbitrary complex `L` on `X` having
such chart models: `L` is a dualizing complex. The first half, that `f^!K` has chart models, is
[Stacks, Tag 0BV2]; the two together are [Stacks, Tag 0AA3].

## Main definitions

* `Stacks.Duality.IsTildeModelOnAnyModel` — the modelling condition of
  `Stacks.Duality.HasDualizingModelOn` with the model named and with no requirement that the
  model be dualizing: `K|_U` is the associated sheaf of `ω ∈ D(Γ(X, U))`.

## Main results

* `Stacks.Duality.hasDualizingModelOn_of_isTildeModelOnAnyModel` and
  `Stacks.Duality.exists_isTildeModelOnAnyModel_of_hasDualizingModelOn` — the two halves of the
  identification of `Stacks.Duality.HasDualizingModelOn` with the existence of a dualizing
  `Stacks.Duality.IsTildeModelOnAnyModel` model.
* `Stacks.Duality.isDualizingComplex_of_isTildeModelOn_upperShriekFunctor` — a complex on `X`
  which over every affine chart of a morphism `f : X ⟶ Y` of locally Noetherian schemes is
  modelled by the algebraic upper shriek of a model of a dualizing complex on `Y` is a
  dualizing complex.

## Implementation notes

`D(𝒪_X)` is a free `HasDerivedCategory` binder, as in `Stacks.Duality.IsDualizingComplex`, so the
statements apply at the locally small model on which `Stacks.Duality.upperShriek` lives. The
derived categories of a ring and of an affine open are read at `HasDerivedCategory.standard`,
which is the instance sealed inside the body of `Stacks.Duality.HasDualizingModelOn`. The local
attribute carries priority `10000` because the import closure reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose `HasDerivedCategory` instances are
global and would otherwise displace that choice for those two categories; the binder for
`D(𝒪_X)` is a local hypothesis and takes precedence over both.

The gluing of the local models is [Stacks, Tag 0A86],
`Stacks.Duality.isDualizingComplex_iff_exists_affineOpenCover`, applied to the cover of `X` by
the charts through its points.

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe w w' u

namespace Stacks.Duality

section TildeModel

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

omit [HasDerivedCategory.{w} X.Modules] in
/-- `K` restricted to an affine open `U` is the associated sheaf of the complex `ω` over
`Γ(X, U)`, transported along `U ≅ Spec Γ(X, U)`.

This is the modelling condition inside `Stacks.Duality.HasDualizingModelOn` with the model `ω`
named as an argument, and with the requirement that `ω` be dualizing dropped. Naming the model
is what lets the chart description of `f^!` be stated separately from the statement that what it
produces is dualizing. -/
def IsTildeModelOnAnyModel [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) : Prop :=
  Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
    (tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)

/-- A dualizing model is a dualizing model: an `ω` which is a dualizing complex over `Γ(X, U)`
and models `K` on `U` witnesses `Stacks.Duality.HasDualizingModelOn`. -/
theorem hasDualizingModelOn_of_isTildeModelOnAnyModel {K : DerivedCategory X.Modules} {U : X.Opens}
    {hU : IsAffineOpen U} [IsNoetherianRing Γ(X, U)]
    {ω : DerivedCategory (ModuleCat.{u} Γ(X, U))}
    (hω : Dualizing.IsDualizingComplex ω) (h : IsTildeModelOnAnyModel K U hU ω) :
    HasDualizingModelOn K U hU :=
  ⟨ω, hω, h⟩

/-- Conversely, `Stacks.Duality.HasDualizingModelOn` hands back the model it asserts to exist,
together with the fact that it is a dualizing complex over `Γ(X, U)`. -/
theorem exists_isTildeModelOnAnyModel_of_hasDualizingModelOn {K : DerivedCategory X.Modules}
    {U : X.Opens} {hU : IsAffineOpen U} [IsNoetherianRing Γ(X, U)]
    (h : HasDualizingModelOn K U hU) :
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
      Dualizing.IsDualizingComplex ω ∧ IsTildeModelOnAnyModel K U hU ω :=
  h

omit [IsLocallyNoetherian X] in
/-- Being modelled by `ω` on `U` depends on `K` only through its isomorphism class. -/
theorem isTildeModelOnAnyModel_of_iso {K K' : DerivedCategory X.Modules} (e : K ≅ K') {U : X.Opens}
    {hU : IsAffineOpen U} {ω : DerivedCategory (ModuleCat.{u} Γ(X, U))}
    (h : IsTildeModelOnAnyModel K U hU ω) : IsTildeModelOnAnyModel K' U hU ω :=
  let ⟨i⟩ := h
  ⟨(Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.mapIso e.symm ≪≫ i⟩

omit [IsLocallyNoetherian X] in
/-- **The structure sheaf is modelled by the ring of sections.** On an affine open `U`, the
structure sheaf in degree zero is the associated sheaf of `Γ(X, U)` in degree zero. -/
theorem isTildeModelOnAnyModel_unit (U : X.Opens) (hU : IsAffineOpen U) :
    IsTildeModelOnAnyModel ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)) U hU
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U))) :=
  ⟨((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor U.toScheme.Modules 0).mapIso
      (Scheme.Modules.restrictUnitIso U.ι ≪≫
        (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
          (tildeSelf (R := Γ(X, U))).symm) ≪≫
    (((tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategorySingleFunctor 0).app
        _).symm⟩

end TildeModel

/-- **The affine chart description of a complex `L` on `X` relative to `K` on `Y`**, the shape of
[Stacks, Tag 0BV2] for `L = f^!K`: over every affine `V ⊆ Y` and affine `U ⊆ f⁻¹(V)`, each model
`ω` of `K` on `V` is carried to a model of `L` on `U` by the algebraic upper shriek along some
polynomial presentation of `Γ(Y, V) → Γ(X, U)`. -/
def HasUpperShriekCharts {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} Y.Modules]
    (K : DerivedCategory Y.Modules) (L : DerivedCategory X.Modules) : Prop :=
  ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (ω : DerivedCategory (ModuleCat.{u} Γ(Y, V))),
    IsTildeModelOnAnyModel K V hV ω →
    ∃ p : Dualizing.PolynomialPresentation (f.appLE V U hUV).hom,
      IsTildeModelOnAnyModel L U hU (p.upperShriekFunctor.{u, u}.obj ω)

/-- The chart description depends on `L` only through its isomorphism class. -/
theorem HasUpperShriekCharts.of_iso {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {f : X ⟶ Y} [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w'} Y.Modules] {K : DerivedCategory Y.Modules}
    {L L' : DerivedCategory X.Modules} (h : HasUpperShriekCharts f K L) (e : L ≅ L') :
    HasUpperShriekCharts f K L' := fun U hU V hV hUV ω hω =>
  let ⟨p, hp⟩ := h U hU V hV hUV ω hω
  ⟨p, isTildeModelOnAnyModel_of_iso e hp⟩

/-- **A complex with upper shriek chart models of a dualizing complex is dualizing.** Let
`f : X ⟶ Y` be a morphism of locally Noetherian schemes and `K` a dualizing complex on `Y`.
Suppose `L ∈ D(𝒪_X)` is, over every affine `V ⊆ Y` and affine `U ⊆ f⁻¹(V)`, the associated sheaf
of the algebraic upper shriek, along some polynomial presentation of `Γ(Y, V) → Γ(X, U)`, of
each model of `K` on `V`. Then `L` is a dualizing complex.

This is the proof of [Stacks, Tag 0AA3] after its reduction to affine charts: the charts through
the points of `X` cover `X`, the model of `K` over `V` is dualizing, its upper shriek is dualizing
by [Stacks, Tag 0BZL], and [Stacks, Tag 0A86] glues. -/
theorem isDualizingComplex_of_isTildeModelOn_upperShriekFunctor {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} Y.Modules]
    (K : DerivedCategory Y.Modules) (L : DerivedCategory X.Modules)
    (hchart : HasUpperShriekCharts f K L)
    (hK : IsDualizingComplex K) :
    IsDualizingComplex L := by
  have hpt : ∀ x : X, ∃ (U : X.Opens) (hU : IsAffineOpen U),
      x ∈ U ∧ HasDualizingModelOn L U hU := fun x => by
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := f.base x) (U := ⊤) (by simp)
    obtain ⟨U, hU, hxU, hUV⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
    have hVnoeth : IsNoetherianRing Γ(Y, V) :=
      IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    have hUnoeth : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨ω, hω, hmodel⟩ := exists_isTildeModelOnAnyModel_of_hasDualizingModelOn (hK V hV)
    obtain ⟨p, hp⟩ := hchart U hU V hV hUV ω hmodel
    exact ⟨U, hU, hxU, hasDualizingModelOn_of_isTildeModelOnAnyModel
      (Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex p ω hω) hp⟩
  choose U hU hxU hmod using hpt
  refine isDualizingComplex_iff_exists_affineOpenCover.mpr
    ⟨X, U, hU, ?_, hmod⟩
  exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩

end Stacks.Duality

end
