module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFunctorLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of a module on a base change descends to a stage

In the situation of Stacks 082M let `T = lim T_i` be a cofiltered limit of affine test schemes
over `Y`, fix a stage `j`, and let `N` be a module of finite presentation on the base change
`X_{T_j}`.  If `f` is quasi-compact and locally of finite presentation and the pullback of `N` to
`X_T` is flat over `T`, then the pullback of `N` to `X_{T_{j'}}` is flat over `T_{j'}` for some
stage `j' ⟶ j`.  This is the step of the proof of Stacks 082Q which cites Stacks 02JO: the
flatness of a descended quotient is achieved at a finite stage.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_modulePullback_congr_of_isPullback`: flatness over the
  base of the pullback of a quasi-coherent module to a fibre product does not depend on the
  cartesian square chosen.
* `AlgebraicGeometry.Space.QuotientSituation.exists_isFlatOver_modulePullback_relativeMap`: the
  descent of flatness to a stage.

## Implementation notes

The geometric input is part (2) of Stacks 0CWZ,
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving`, read through
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_limitPreserving_iff`.  It is applied to the
flattening situation `AlgebraicGeometry.Space.QuotientSituation.stageFlatnessSituation` of the
projection `X_{T_j} ⟶ T_j` with the module `N`, whose test schemes are the schemes over `T_j`.
The stages beyond `j` are read as such test schemes by
`AlgebraicGeometry.Space.schemesOverStage`, and the restricted system is still a limit because
`CategoryTheory.Over.forget` is initial for a cofiltered index category.

For a test scheme `T_i` over `T_j` the flattening situation tests the pullback of `N` to the fibre
product `X_{T_j} ×_{T_j} T_i`, while the statement asks about its pullback to `X_{T_i}` along
`X_{T_i} ⟶ X_{T_j}`.  Both squares over `T_i ⟶ T_j` are cartesian (the second by
`AlgebraicGeometry.Space.isPullback_baseChangeMap`), so the two conditions agree by
`AlgebraicGeometry.Space.isFlatOver_modulePullback_congr_of_isPullback`.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
* [Stacks Project, Tag 0CWZ](https://stacks.math.columbia.edu/tag/0CWZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Flatness of a pulled back module does not depend on the cartesian square.**  Two cartesian
squares on the same cospan `P ⟶ T₀ ⟵ T` differ by an isomorphism of their apexes compatible with
both projections, and flatness over `T` of the pullback of a quasi-coherent module on `P` is
invariant under such an isomorphism. -/
theorem isFlatOver_modulePullback_congr_of_isPullback
    {P T₀ T P₁ P₂ : AlgebraicSpaces B S hS} {q : P ⟶ T₀} {b : T ⟶ T₀}
    {a₁ : P₁ ⟶ P} {q₁ : P₁ ⟶ T} {a₂ : P₂ ⟶ P} {q₂ : P₂ ⟶ T}
    (h₁ : IsPullback a₁ q₁ q b) (h₂ : IsPullback a₂ q₂ q b)
    (N : Modules.{u, u} B S hS P.1 P.2) (hN : N.IsQuasicoherentOnSite) :
    IsFlatOver B S hS P₁.2 q₁.hom ((modulePullback B S hS a₁).obj N) ↔
      IsFlatOver B S hS P₂.2 q₂.hom ((modulePullback B S hS a₂).obj N) := by
  obtain ⟨e, rfl, rfl⟩ : ∃ e : P₁ ≅ P₂, e.hom ≫ a₂ = a₁ ∧ e.hom ≫ q₂ = q₁ :=
    ⟨h₁.isoIsPullback _ _ h₂, h₁.isoIsPullback_hom_fst _ _ h₂, h₁.isoIsPullback_hom_snd _ _ h₂⟩
  exact (isFlatOver_iff_of_iso B S hS P₁.2 _ ((modulePullbackTriangle B S hS rfl).app N)).trans
    (isFlatOver_modulePullback_iso_iff e q₂ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a₂ N hN))

/-- **A test scheme over a chosen test scheme `T₀`, read as a test scheme over the algebraic space
of `T₀`.**  The underlying object of the big fppf category is unchanged; the structure morphism
is the image of the morphism to `T₀`. -/
def schemesOverStage {Y : AlgebraicSpaces B S hS} (T₀ : SchemesOver Y) :
    Over T₀ ⥤ SchemesOver ((schemeSpaceFunctor B S hS).obj T₀.left) where
  obj A := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map A.hom.left)
  map {A A'} k := CostructuredArrow.homMk k.left.left (by
    have h : k.left.left ≫ A'.hom.left = A.hom.left :=
      congrArg (fun g : A.left ⟶ T₀ => g.left) (Over.w k)
    change (schemeSpaceFunctor B S hS).map k.left.left ≫
      (schemeSpaceFunctor B S hS).map A'.hom.left =
        (schemeSpaceFunctor B S hS).map A.hom.left
    rw [← Functor.map_comp, h])
  map_id A := by apply CostructuredArrow.hom_ext; rfl
  map_comp k k' := by apply CostructuredArrow.hom_ext; rfl

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- **The flattening situation of a module on a base change.**  For a test scheme `T₀` over `Y`
and a quasi-coherent module `N` on `X_{T₀}`, the situation of Stacks 0CWX for the projection
`X_{T₀} ⟶ T₀` and the module `N`. -/
def stageFlatnessSituation (T₀ : SchemesOver D.Y)
    (N : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2) (hN : N.IsQuasicoherentOnSite) :
    FlatnessSituation B S hS where
  X := D.space T₀
  Y := (schemeSpaceFunctor B S hS).obj T₀.left
  f := D.projection T₀
  F := N
  quasicoherent := hN

/-- **Flatness for the stage situation is flatness of the pullback along `X_A ⟶ X_{T₀}`.**  For a
test scheme `A` over `T₀`, the stage situation tests the pullback of `N` to the fibre product
`X_{T₀} ×_{T₀} A`, and this is equivalent to flatness over `A` of the pullback of `N` to `X_A`
along the morphism of base changes: both squares over `A ⟶ T₀` are cartesian. -/
theorem stageFlatnessSituation_isFlatAfterBaseChange_iff (T₀ : SchemesOver D.Y)
    (N : Modules.{u, u} B S hS (D.space T₀).1 (D.space T₀).2) (hN : N.IsQuasicoherentOnSite)
    (A : Over T₀) :
    (D.stageFlatnessSituation T₀ N hN).IsFlatAfterBaseChange ((schemesOverStage T₀).obj A) ↔
      IsFlatOver B S hS (D.space A.left).2 (D.projection A.left).hom
        ((modulePullback B S hS (D.relativeMap A.hom)).obj N) :=
  isFlatOver_modulePullback_congr_of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (D.projection T₀)
      ((schemeSpaceFunctor B S hS).map A.hom.left))
    (isPullback_baseChangeMap D.f A.hom) N hN

/-- **Flatness descends to a stage (the step of Stacks 082Q citing Stacks 02JO).**  Let `f` be
quasi-compact and locally of finite presentation, let `T = lim T_i` be a cofiltered limit of
affine test schemes over `Y`, and let `N` be a module of finite presentation on `X_{T_j}`.  If the
pullback of `N` to `X_T` is flat over `T`, then its pullback to `X_{T_{j'}}` is flat over
`T_{j'}` for some stage `j' ⟶ j`.

This is part (2) of Stacks 0CWZ for the projection `X_{T_j} ⟶ T_j` and the module `N`, applied to
the stages over `j`; the projection is quasi-compact and locally of finite presentation as a
base change of `f`. -/
@[ega "IV 11.2.6.1" "(ii), necessity"]
theorem exists_isFlatOver_modulePullback_relativeMap
    (hqc : IsQuasiCompact B S hS D.f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ SchemesOver D.Y) (c : Cone E)
    (hc : IsLimit (D.testScheme.mapCone c)) (hE : ∀ i, IsAffine (D.testScheme.obj (E.obj i)))
    (hpt : IsAffine (D.testScheme.obj c.pt)) (j : I)
    (N : Modules.{u, u} B S hS (D.space (E.obj j)).1 (D.space (E.obj j)).2)
    (hN : N.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space c.pt).2 (D.projection c.pt).hom
      ((modulePullback B S hS (D.relativeMap (c.π.app j))).obj N)) :
    ∃ (j' : I) (e : j' ⟶ j), IsFlatOver B S hS (D.space (E.obj j')).2
      (D.projection (E.obj j')).hom ((modulePullback B S hS (D.relativeMap (E.map e))).obj N) := by
  have := hN
  have hNq : N.IsQuasicoherentOnSite := inferInstance
  let D₀ := D.stageFlatnessSituation (E.obj j) N hNq
  have hqc₀ : IsQuasiCompact B S hS D₀.f.hom :=
    isQuasiCompact_pullback_snd_of_isQuasiCompact B S hS hqc (E.obj j).left (E.obj j).hom.hom
  have hlfp₀ : IsLocallyOfFinitePresentation B S hS D₀.f.hom :=
    FlatnessSituation.isLocallyOfFinitePresentation_baseChangeInclusion
      ⟨D.X, D.Y, D.f, D.F, D.quasicoherent⟩ hlfp (E.obj j)
  let K : Cone (Over.post E : Over j ⥤ Over (E.obj j)) :=
    { pt := Over.mk (c.π.app j)
      π :=
        { app := fun A => Over.homMk (c.π.app A.left) (c.w A.hom)
          naturality := fun A A' k => by
            apply Over.OverMorphism.ext
            change 𝟙 c.pt ≫ c.π.app A'.left = c.π.app A.left ≫ E.map k.left
            rw [Category.id_comp, c.w k.left] } }
  let E' := Over.post E ⋙ schemesOverStage (E.obj j)
  let c' := (schemesOverStage (E.obj j)).mapCone K
  have hc' : IsLimit (D₀.testScheme.mapCone c') :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j) (D.testScheme.mapCone c)).symm hc
  have hflat₀ : D₀.IsFlatAfterBaseChange c'.pt :=
    (D.stageFlatnessSituation_isFlatAfterBaseChange_iff (E.obj j) N hNq K.pt).mpr hflat
  obtain ⟨A, hA⟩ := D₀.flatFunctor_limitPreserving_iff.mp
    (D₀.flatFunctor_limitPreserving hqc₀ hlfp₀ hN) (Over j) E' c' hc' (fun A => hE A.left) hpt
    hflat₀
  exact ⟨A.left, A.hom,
    (D.stageFlatnessSituation_isFlatAfterBaseChange_iff (E.obj j) N hNq
      ((Over.post E).obj A)).mp hA⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
