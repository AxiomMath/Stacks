module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.Datum
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsHenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceUnitNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# The kernel of a derived Chow datum restricted to `V` (Stacks 0CTS)

Let `X` be an algebraic space over `S` and let `(n, Z, z, V, E)` be a datum of the derived Chow
lemma at a point of `X` (`AlgebraicGeometry.Space.DerivedChowDatum`), with projections
`p : X ×_S ℙⁿ_S ⟶ X` and `q : X ×_S ℙⁿ_S ⟶ ℙⁿ_S`, `W = c⁻¹(V) ⊂ Z`, `b : W ⟶ X` étale and
`c|_W : W ⟶ V` a closed immersion. Stacks 0CTS: for `K ∈ D_QCoh(𝒪_X)`,

`Rq_*(Lp^*K ⊗^𝐋 E)|_V ≅ R(W ⟶ V)_* K|_W`,

and `c|_W : W ⟶ V` is a closed immersion of finite presentation when `X` is of finite
presentation over `S`.

The proof is the source's. Restriction to `V` commutes with `Rq_*` (étale base change). Over
`X ×_S V` the complex `E` is `(b, c)_*𝒪_Z`, whose restriction is `Ri_*𝒪_W` for the closed
immersion `i : W ⟶ X ×_S V` (étale base change again, `i` being affine). The projection formula
(Stacks 08IN) turns `M ⊗^𝐋 Ri_*𝒪_W` into `Ri_*Li^*M`, and composing direct images and
pullbacks gives `R(c|_W)_* Lb^*K`. As `W` is étale over `X`, `Lb^*K` is the restriction `K|_W`.

## Main definitions

* `AlgebraicGeometry.Space.DerivedChow.overOpenToProductOver`: the closed immersion
  `i : W ⟶ X ×_S V`.

## Main results

* `AlgebraicGeometry.Space.DerivedChow.isPullback_overOpenToProductOver`: `W` is the part
  of `Z` over `X ×_S V`.
* `AlgebraicGeometry.Space.DerivedChowDatum.isFinitePresentation_overOpenToOpen`: the first
  assertion of Stacks 0CTS.
* `AlgebraicGeometry.Space.DerivedChowDatum.nonempty_restrict_derivedPushforward_tensor_iso`:
  the isomorphism of Stacks 0CTS.

## References

* [Stacks Project, Tag 0CTS](https://stacks.math.columbia.edu/tag/0CTS)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

open DerivedChow

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DerivedChow

variable {X Z V : AlgebraicSpaces B S hS} {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)}
  (i : Z ⟶ product B S hS X n hP) (v : V ⟶ schemeSpace (projectiveSpaceSiteObj B S hS n hP))

/-- The cartesian square exhibiting `X ×_S V` as the base change of `ℙⁿ_S` along `V`. -/
theorem isPullback_productOver :
    IsPullback (productOverι X n hP v)
      (ObjectProperty.homMk (pullback.snd _ _) : productOver X n hP v ⟶ V)
      (productSnd X n hP) v :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The cartesian square exhibiting `W` as the base change of `Z` along `V`. -/
theorem isPullback_overOpen :
    IsPullback (overOpenι i v) (overOpenToOpen i v) (i ≫ productSnd X n hP) v :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The closed immersion `W ⟶ X ×_S V`, the restriction of `(b, c) : Z ⟶ X ×_S ℙⁿ_S`. -/
def overOpenToProductOver : overOpen i v ⟶ productOver X n hP v :=
  (isPullback_productOver v).lift (overOpenι i v ≫ i) (overOpenToOpen i v)
    (by rw [Category.assoc]; exact (isPullback_overOpen i v).w)

/-- The composite of `W ⟶ X ×_S V` with the inclusion `X ×_S V ⟶ X ×_S ℙⁿ_S` is the composite
of the inclusion `W ⟶ Z` with `Z ⟶ X ×_S ℙⁿ_S`. -/
@[reassoc (attr := simp)]
theorem overOpenToProductOver_ι :
    overOpenToProductOver i v ≫ productOverι X n hP v = overOpenι i v ≫ i :=
  (isPullback_productOver v).lift_fst _ _ _

/-- The composite of `W ⟶ X ×_S V` with the projection `X ×_S V ⟶ V` is `c|_W : W ⟶ V`. -/
@[reassoc (attr := simp)]
theorem overOpenToProductOver_snd :
    overOpenToProductOver i v ≫
        (ObjectProperty.homMk (pullback.snd _ _) : productOver X n hP v ⟶ V) =
      overOpenToOpen i v :=
  (isPullback_productOver v).lift_snd _ _ _

/-- `W` is the part of `Z` lying over `X ×_S V`. -/
theorem isPullback_overOpenToProductOver :
    IsPullback (overOpenι i v) (overOpenToProductOver i v) i (productOverι X n hP v) :=
  (IsPullback.of_right (h₁₁ := overOpenToProductOver i v) (h₂₁ := i)
    (by rw [overOpenToProductOver_snd]; exact (isPullback_overOpen i v).flip)
    (overOpenToProductOver_ι i v) (isPullback_productOver v).flip).flip

/-- If `v : V ⟶ ℙⁿ_S` is an open immersion, then so is `X ×_S V ⟶ X ×_S ℙⁿ_S`. -/
theorem isOpenImmersion_productOverι (hv : IsOpenImmersion B S hS v.hom) :
    IsOpenImmersion B S hS (productOverι X n hP v).hom :=
  isOpenImmersion_of_isPullback B S hS (isPullback_productOver v).flip hv

/-- If `Z ⟶ X ×_S ℙⁿ_S` is a closed immersion, then so is `W ⟶ X ×_S V`. -/
theorem isClosedImmersion_overOpenToProductOver (hi : IsClosedImmersion B S hS i.hom) :
    IsClosedImmersion B S hS (overOpenToProductOver i v).hom :=
  isClosedImmersion_of_isPullback B S hS (isPullback_overOpenToProductOver i v) hi

/-- **`(i_*𝒪_Z)|_{X ×_S V} ≅ R(W ⟶ X ×_S V)_*𝒪_W`** for a closed immersion
`i : Z ⟶ X ×_S ℙⁿ_S` and an open immersion `v : V ⟶ ℙⁿ_S`, where `W` is the part of `Z` lying
over `X ×_S V`: étale base change along the open immersion `X ×_S V ⟶ X ×_S ℙⁿ_S`, `i` being
affine. -/
def restrictSinglePushforwardIso (hi : IsClosedImmersion B S hS i.hom)
    (hv : IsOpenImmersion B S hS v.hom) :
    (smallEtaleDerivedModulePullback B S hS (productOverι X n hP v)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureSheafPushforward B S hS i)) ≅
      (derivedModulePushforward B S hS (overOpenToProductOver i v)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS (overOpen i v)))) :=
  haveI := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS _ _ _ _
    (isPullback_overOpenToProductOver i v)
    (isEtale_of_isOpenImmersion B S hS (isOpenImmersion_productOverι v hv))
    (isOpenImmersion_productOverι v hv).rep
    ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Z.1 Z.2) 0).obj (structureModule Z))
  (smallEtaleDerivedModulePullback B S hS (productOverι X n hP v)).mapIso
      (derivedModulePushforwardStructureModuleIso B S hS i
        (isAffineHom_of_isClosedImmersion B S hS _ hi)).symm ≪≫
    asIso (smallEtaleDerivedModuleBaseChangeMap B S hS i (productOverι X n hP v)
      (overOpenToProductOver i v) (overOpenι i v) (isPullback_overOpenToProductOver i v).w _) ≪≫
    (derivedModulePushforward B S hS (overOpenToProductOver i v)).mapIso
      (smallEtaleDerivedModulePullbackUnitIso (overOpenι i v))

end DerivedChow

namespace DerivedChowDatum

variable {X : AlgebraicSpaces B S hS} {x : points B S hS X.1} (D : DerivedChowDatum X x)

/-- **Stacks 0CTS, first assertion.** For `X` of finite presentation over `S`, the closed
immersion `c|_W : W ⟶ V` is of finite presentation. -/
@[stacks 0CTS "the closed immersion c|_W : W ⟶ V of the statement is of finite presentation"]
theorem isFinitePresentation_overOpenToOpen
    (hfp : IsFinitePresentation B S hS (toBase B S hS X).hom) :
    IsFinitePresentation B S hS (overOpenToOpen D.i D.v).hom := by
  have hq : IsFinitePresentation B S hS (productSnd X D.n D.contains).hom :=
    isFinitePresentation_pullback_snd B S hS _ _ X.2 (isAlgebraicSpace_yoneda _ _ _ _)
      (isAlgebraicSpace_yoneda _ _ _ _) hfp
  have hc : IsFinitePresentation B S hS (D.i ≫ productSnd X D.n D.contains).hom :=
    isFinitePresentation_comp B S hS D.Z.2 (product B S hS X D.n D.contains).2
      (isAlgebraicSpace_yoneda _ _ _ _) _ _ D.isFinitePresentation_i hq
  exact (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_overOpen D.i D.v) hc

/-- **Stacks 0CTS.** For a datum `(n, Z, z, V, E)` of the derived Chow lemma on `X` and
`K ∈ D_QCoh(𝒪_X)`, `Rq_*(Lp^*K ⊗^𝐋 E)|_V ≅ R(c|_W)_* K|_W`, where `p` and `q` are the two
projections of `X ×_S ℙⁿ_S`, `c|_W : W ⟶ V` is the closed immersion of the datum and `K|_W` is
the derived pullback along the étale morphism `b : W ⟶ X`. -/
@[stacks 0CTS]
theorem nonempty_restrict_derivedPushforward_tensor_iso
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS D.v).obj
        ((derivedModulePushforward B S hS (productSnd X D.n D.contains)).obj
          (((smallEtaleDerivedTensor B S hS (product B S hS X D.n D.contains)).obj
            ((smallEtaleDerivedModulePullback B S hS (productFst X D.n D.contains)).obj K)).obj
              D.E)) ≅
      (derivedModulePushforward B S hS (overOpenToOpen D.i D.v)).obj
        ((smallEtaleDerivedModulePullback B S hS
          (overOpenι D.i D.v ≫ D.i ≫ productFst X D.n D.contains)).obj K)) := by
  let ι := productOverι X D.n D.contains D.v
  let q' : productOver X D.n D.contains D.v ⟶ D.V := ObjectProperty.homMk (pullback.snd _ _)
  let i' := overOpenToProductOver D.i D.v
  let p := productFst X D.n D.contains
  let W := overOpen D.i D.v
  let TV := productOver X D.n D.contains D.v
  have hvet : IsEtale B S hS D.v.hom := isEtale_of_isOpenImmersion B S hS D.isOpenImmersion_v
  have hi'cl := (isClosedImmersion_overOpenToProductOver D.i D.v D.isClosedImmersion_i)
  let M := ((smallEtaleDerivedTensor B S hS (product B S hS X D.n D.contains)).obj
    ((smallEtaleDerivedModulePullback B S hS p).obj K)).obj D.E
  -- Restriction to `V` commutes with `Rq_*`.
  have := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS _ _ _ _
    (isPullback_productOver D.v) hvet D.isOpenImmersion_v.rep M
  let e₁ := asIso (smallEtaleDerivedModuleBaseChangeMap B S hS (productSnd X D.n D.contains) D.v
    q' ι (isPullback_productOver D.v).w M)
  -- `E|_{X ×_S V} ≅ Ri'_* 𝒪_W`.
  let OW : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)) :=
    (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)
  let eE : (smallEtaleDerivedModulePullback B S hS ι).obj D.E ≅
      (derivedModulePushforward B S hS i').obj OW :=
    D.restrictIso.some ≪≫
      restrictSinglePushforwardIso D.i D.v D.isClosedImmersion_i D.isOpenImmersion_v
  -- The projection formula along `i'`.
  let N := (smallEtaleDerivedModulePullback B S hS (ι ≫ p)).obj K
  have hN : QcohDerived B S hS TV N :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K hK
  have := isIso_smallEtaleProjectionFormulaMapSnd B S hS i'
    (isQuasiCompact_of_isClosedImmersion' B S hS hi'cl)
    (isQuasiSeparated_of_isClosedImmersion B S hS hi'cl) N hN OW
    (derivedStructureSheaf B S hS W.1 W.2).property
  let e₈ := asIso (smallEtaleProjectionFormulaMapSnd i' N OW)
  let e₉ : ((smallEtaleDerivedTensor B S hS W).obj
      ((smallEtaleDerivedModulePullback B S hS i').obj N)).obj OW ≅
      (smallEtaleDerivedModulePullback B S hS i').obj N :=
    (Stacks.SheafOfModules.DerivedTensorProduct.unitNatIso _
      (smallEtaleDerivedTensorProduct B S hS W)).app _
  let e₁₀ : (smallEtaleDerivedModulePullback B S hS i').obj N ≅
      (smallEtaleDerivedModulePullback B S hS (overOpenι D.i D.v ≫ D.i ≫ p)).obj K :=
    (smallEtaleDerivedModulePullbackCompIso B S hS i' (ι ≫ p)).app K ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS (by simp [i', ι, p])).app K
  let e₁₁ : (derivedModulePushforward B S hS i' ⋙ derivedModulePushforward B S hS q').obj
      ((smallEtaleDerivedModulePullback B S hS (overOpenι D.i D.v ≫ D.i ≫ p)).obj K) ≅
      (derivedModulePushforward B S hS (overOpenToOpen D.i D.v)).obj
        ((smallEtaleDerivedModulePullback B S hS (overOpenι D.i D.v ≫ D.i ≫ p)).obj K) :=
    (smallEtaleDerivedPushforwardCompIsoToposHom B S hS i' q').app _ ≪≫
      eqToIso (by rw [overOpenToProductOver_snd D.i D.v])
  refine ⟨e₁ ≪≫ (derivedModulePushforward B S hS q').mapIso
    ((smallEtaleDerivedPullbackTensorIso ι).app (_, D.E) ≪≫
      ((smallEtaleDerivedTensor B S hS TV).mapIso
        ((smallEtaleDerivedModulePullbackCompIso B S hS ι p).app K)).app _ ≪≫
      ((smallEtaleDerivedTensor B S hS TV).obj N).mapIso eE ≪≫ e₈ ≪≫
      (derivedModulePushforward B S hS i').mapIso (e₉ ≪≫ e₁₀)) ≪≫ e₁₁⟩

end DerivedChowDatum

end AlgebraicGeometry.Space

end
