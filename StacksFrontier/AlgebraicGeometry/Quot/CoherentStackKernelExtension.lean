module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTangentKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionTransferExtension
public import StacksFrontier.RingTheory.Flat.TrivSqZeroExtRelation

/-!
# The extension attached to a deformation of `Coh_{X/Y}` with trivial base

Let `D` be the situation of Stacks 08KB, `x₀ = (Spec k, g₀, 𝒢₀)` an object of `Coh_{X/Y}` over a
field `k` and `x` a deformation of `x₀` over `k[M]` whose test scheme maps to `Spec k` over `Y`
by the spectrum of `k ⟶ k[M]` (`AlgebraicGeometry.Space.CoherentSituation.HasTrivialBase`).
Then `X_x = X ×_Y Spec k[M]` is a split square-zero thickening of `X₀ = X ×_Y Spec k`, the
module `ℱ` of `x` is flat over `Spec k[M]`, and the arrow `x₀ ⟶ x` identifies `𝒢₀` with the
restriction of `ℱ` to `X₀`; so `r_*ℱ` is an extension of `𝒢₀` by `𝒢₀ ⊗ M`
(`AlgebraicGeometry.Space.retractionCopowerExtension`), whose class in `Ext¹(𝒢₀, 𝒢₀ ⊗ M)` is
the class of the deformation in Stacks 08W8.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.residueScalars`: the scalars `k ⟶ Γ(X₀, 𝒪)` of
  `X₀`, through `Spec k`.
* `AlgebraicGeometry.Space.CoherentSituation.kernelExtension`: the extension of a deformation
  with trivial base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

/-- `kᵐᵒᵖ` acts on a finite-dimensional `k`-vector space through `MulOpposite.unop`. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The actions of `k` and of `kᵐᵒᵖ` on a finite-dimensional `k`-vector space agree. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  (x₀ : CoherentObject D)
  (hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The identification of the global functions of `Spec k` with `k`. -/
def residueRingEquiv : k ≃+* D.testRing x₀.T :=
  RingEquiv.ofBijective (D.testRingOfSpec x₀.T (D.toScheme_basePoint (k := k) iΛ x₀ hx₀)).hom
    (D.bijective_testRingOfSpec x₀.T (D.toScheme_basePoint (k := k) iΛ x₀ hx₀))

/-- The scalars `k ⟶ Γ(X₀, 𝒪)` of `X₀ = X ×_Y Spec k`. -/
abbrev residueScalars : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (D.space x₀.T).1
      (D.space x₀.T).2).O) :=
  D.splitScalars₀ (D.residueRingEquiv iΛ x₀ hx₀).toRingHom

/-- The `k`-linear structure on the modules of `X₀`. -/
abbrev residueLinear : Linear k (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2) :=
  retractionLinear B S hS (X₀ := D.space x₀.T) (D.residueScalars iΛ x₀ hx₀)

variable (M : FGModuleCat.{u} k) (d : DeformationObject iΛ D.cohQ x₀ hx₀)
  (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)

include hd in
/-- The scheme of the test scheme of a deformation over `k[M]` is `Spec k[M]`. -/
theorem toScheme_defPoint :
    (BigFppfOver.toScheme B S hS).obj d.point.T.left =
      Spec (CommRingCat.of (TrivSqZeroExt k M)) :=
  (D.toScheme_deformationPoint iΛ x₀ hx₀ d).trans
    (congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (CommRingCat.of A)) hd)

/-- The identification of the global functions of the test scheme of `x` with `k[M]`. -/
def fiberRingEquiv : TrivSqZeroExt k M ≃+* D.testRing d.point.T :=
  RingEquiv.ofBijective (D.testRingOfSpec d.point.T (D.toScheme_defPoint iΛ x₀ hx₀ M d hd)).hom
    (D.bijective_testRingOfSpec d.point.T (D.toScheme_defPoint iΛ x₀ hx₀ M d hd))

/-- The square-zero functions `M ⟶ Γ(Spec k[M])`. -/
def fiberFunctions : ↥M →+ D.testRing d.point.T :=
  (D.fiberRingEquiv iΛ x₀ hx₀ M d hd).toAddMonoidHom.comp (TrivSqZeroExt.inrHom k M).toAddMonoidHom


/-- **Pullback of functions along the section is the residue map `k[M] ⟶ k`.** -/
theorem siteΓ_fiberSection (y : TrivSqZeroExt k M) :
    (siteΓ (D.homOf d.arrow).base.left).hom (D.fiberRingEquiv iΛ x₀ hx₀ M d hd y) =
      D.residueRingEquiv iΛ x₀ hx₀ y.fst := by
  obtain ⟨alg, pt, ar, bas, ab⟩ := d
  change alg = _ at hd
  subst hd
  have hσ := D.toScheme_map_arrow_base iΛ x₀ hx₀ ⟨_, pt, ar, bas, ab⟩
  have key := D.siteΓ_testRingOfSpec (T₁ := x₀.T) (T₀ := pt.T) (D.homOf ar).base.left
    (D.toScheme_defPoint iΛ x₀ hx₀ M ⟨_, pt, ar, bas, ab⟩ rfl)
    (D.toScheme_basePoint (k := k) iΛ x₀ hx₀)
    (CommRingCat.ofHom (residueMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)))
    hσ
  exact congrArg (fun f => f.hom y) key


/-- **The ring map of a trivial base is the inclusion `k ⟶ k[M]`.** -/
theorem siteΓ_trivialBase (π : d.point.T ⟶ x₀.T)
    (hπ : (BigFppfOver.toScheme B S hS).map π.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M d hd) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) (c : k) :
    (siteΓ π.left).hom (D.residueRingEquiv iΛ x₀ hx₀ c) =
      D.fiberRingEquiv iΛ x₀ hx₀ M d hd (algebraMap k (TrivSqZeroExt k M) c) := by
  have key := D.siteΓ_testRingOfSpec π.left (D.toScheme_basePoint (k := k) iΛ x₀ hx₀)
    (D.toScheme_defPoint iΛ x₀ hx₀ M d hd)
    (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) hπ
  exact congrArg (fun f => f.hom c) key

/-- A scheme equal to the spectrum of a ring is affine. -/
private theorem isAffine_of_eq_spec {X : Scheme.{u}} {R : CommRingCat.{u}} (h : X = Spec R) :
    IsAffine X := by
  rw [h]
  infer_instance

/-- The section followed by a trivial base is the identity. -/
theorem fiberSection_comp_trivialBase (π : d.point.T ⟶ x₀.T)
    (hπ : (BigFppfOver.toScheme B S hS).map π.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M d hd) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) :
    (D.homOf d.arrow).base ≫ π = 𝟙 x₀.T := by
  have hT₀ := isAffine_of_eq_spec (D.toScheme_basePoint (k := k) iΛ x₀ hx₀)
  refine CostructuredArrow.hom_ext _ _ ((BigFppfOver.toScheme B S hS).map_injective
    (ext_of_isAffine ?_))
  change siteΓ ((D.homOf d.arrow).base.left ≫ π.left) = siteΓ (𝟙 x₀.T.left)
  rw [siteΓ_comp, siteΓ_id]
  ext t
  obtain ⟨c, rfl⟩ := (D.residueRingEquiv iΛ x₀ hx₀).surjective t
  change (siteΓ (D.homOf d.arrow).base.left).hom ((siteΓ π.left).hom
    (D.residueRingEquiv iΛ x₀ hx₀ c)) = D.residueRingEquiv iΛ x₀ hx₀ c
  rw [D.siteΓ_trivialBase iΛ x₀ hx₀ M d hd π hπ, D.siteΓ_fiberSection iΛ x₀ hx₀ M d hd]
  rfl

include hx₀ in
/-- The scheme of the test scheme of `x₀` is affine. -/
theorem isAffine_basePoint :
    IsAffine ((BigFppfOver.toScheme B S hS).obj x₀.T.left) :=
  isAffine_of_eq_spec (D.toScheme_basePoint (k := k) iΛ x₀ hx₀)

include hd in
/-- The scheme of the test scheme of a deformation over `k[M]` is affine. -/
theorem isAffine_fiberPoint :
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.point.T.left) :=
  isAffine_of_eq_spec (D.toScheme_defPoint iΛ x₀ hx₀ M d hd)

/-- Pullback of functions along the section kills the square-zero functions. -/
theorem siteΓ_fiberSection_fiberFunctions (v : ↥M) :
    (siteΓ (D.homOf d.arrow).base.left).hom (D.fiberFunctions iΛ x₀ hx₀ M d hd v) = 0 := by
  change (siteΓ (D.homOf d.arrow).base.left).hom
    (D.fiberRingEquiv iΛ x₀ hx₀ M d hd (TrivSqZeroExt.inr v)) = 0
  rw [D.siteΓ_fiberSection iΛ x₀ hx₀ M d hd]
  simp

/-- The kernel of pullback of functions along the section is the ideal generated by the
square-zero functions. -/
theorem ker_siteΓ_fiberSection :
    RingHom.ker (siteΓ (D.homOf d.arrow).base.left).hom =
      Ideal.span (Set.range (D.fiberFunctions iΛ x₀ hx₀ M d hd)) := by
  apply le_antisymm
  · intro t ht
    obtain ⟨y, rfl⟩ := (D.fiberRingEquiv iΛ x₀ hx₀ M d hd).surjective t
    have h0 : D.residueRingEquiv iΛ x₀ hx₀ y.fst = 0 := by
      rw [← D.siteΓ_fiberSection iΛ x₀ hx₀ M d hd]
      exact ht
    have hfst : y.fst = 0 := by
      simpa using h0
    have hy : y = TrivSqZeroExt.inr y.snd := TrivSqZeroExt.ext (by simp [hfst]) (by simp)
    rw [hy]
    exact Ideal.subset_span ⟨y.snd, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨v, rfl⟩
    exact D.siteΓ_fiberSection_fiberFunctions iΛ x₀ hx₀ M d hd v

/-- The product of two square-zero functions is zero. -/
theorem fiberFunctions_mul (v w : ↥M) :
    D.fiberFunctions iΛ x₀ hx₀ M d hd v * D.fiberFunctions iΛ x₀ hx₀ M d hd w = 0 := by
  change D.fiberRingEquiv iΛ x₀ hx₀ M d hd (TrivSqZeroExt.inr v) *
    D.fiberRingEquiv iΛ x₀ hx₀ M d hd (TrivSqZeroExt.inr w) = 0
  rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]

/-- The square-zero functions `M ⟶ Γ(Spec k[M])` are injective. -/
theorem fiberFunctions_injective : Function.Injective (D.fiberFunctions iΛ x₀ hx₀ M d hd) :=
  (D.fiberRingEquiv iΛ x₀ hx₀ M d hd).injective.comp TrivSqZeroExt.inr_injective

/-- The residue `Γ(Spec k[M]) ⟶ k`. -/
def fiberResidue : D.testRing d.point.T →+* k :=
  (TrivSqZeroExt.fstHom k k M).toRingHom.comp (D.fiberRingEquiv iΛ x₀ hx₀ M d hd).symm.toRingHom

/-- The product of the square-zero function of `v` with a function `a` is the square-zero
function of `ā • v`, where `ā` is the residue of `a`. -/
theorem fiberFunctions_mul_eq (v : ↥M) (a : D.testRing d.point.T) :
    D.fiberFunctions iΛ x₀ hx₀ M d hd v * a =
      D.fiberFunctions iΛ x₀ hx₀ M d hd (D.fiberResidue iΛ x₀ hx₀ M d hd a • v) := by
  obtain ⟨y, rfl⟩ := (D.fiberRingEquiv iΛ x₀ hx₀ M d hd).surjective a
  change D.fiberRingEquiv iΛ x₀ hx₀ M d hd (TrivSqZeroExt.inr v) *
    D.fiberRingEquiv iΛ x₀ hx₀ M d hd y = D.fiberRingEquiv iΛ x₀ hx₀ M d hd (TrivSqZeroExt.inr
      ((TrivSqZeroExt.fstHom k k M) ((D.fiberRingEquiv iΛ x₀ hx₀ M d hd).symm
        (D.fiberRingEquiv iΛ x₀ hx₀ M d hd y)) • v))
  rw [← map_mul, RingEquiv.symm_apply_apply, TrivSqZeroExt.inr_mul_eq]
  rfl

/-- A function with residue zero pulls back to zero along the section. -/
theorem siteΓ_fiberSection_of_fiberResidue_eq_zero (a : D.testRing d.point.T)
    (ha : D.fiberResidue iΛ x₀ hx₀ M d hd a = 0) :
    (siteΓ (D.homOf d.arrow).base.left).hom a = 0 := by
  obtain ⟨y, rfl⟩ := (D.fiberRingEquiv iΛ x₀ hx₀ M d hd).surjective a
  rw [D.siteΓ_fiberSection iΛ x₀ hx₀ M d hd]
  have : y.fst = 0 := by
    have h := ha
    simp only [fiberResidue, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h
    exact h
  rw [this, map_zero]

/-- **The base change of `X` to a trivial base is a split square-zero thickening of `X₀`.** -/
theorem kernel_isSplitThickeningBy (π : d.point.T ⟶ x₀.T)
    (hπ : (BigFppfOver.toScheme B S hS).map π.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M d hd) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) :
    IsSplitThickeningBy B S hS (D.relativeMap π) (D.splitRep π)
      (D.relativeMap (D.homOf d.arrow).base)
      (D.relativeMap_comp_relativeMap_eq_id π _
        (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ))
      M (D.residueScalars iΛ x₀ hx₀) (D.splitScalars₁ π (D.residueRingEquiv iΛ x₀ hx₀).toRingHom)
      (D.splitFunctions M (D.fiberFunctions iΛ x₀ hx₀ M d hd)) :=
  D.isSplitThickeningBy π _ (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ) M
    (D.residueRingEquiv iΛ x₀ hx₀).toRingHom (D.fiberFunctions iΛ x₀ hx₀ M d hd)
    (D.isAffine_basePoint iΛ x₀ hx₀) (D.isAffine_fiberPoint iΛ x₀ hx₀ M d hd)
    (D.ker_siteΓ_fiberSection iΛ x₀ hx₀ M d hd) (D.fiberFunctions_mul iΛ x₀ hx₀ M d hd)
    (fun c v => by
      change D.fiberRingEquiv iΛ x₀ hx₀ M d hd (TrivSqZeroExt.inr (c • v)) =
        (siteΓ π.left).hom (D.residueRingEquiv iΛ x₀ hx₀ c) *
          D.fiberRingEquiv iΛ x₀ hx₀ M d hd (TrivSqZeroExt.inr v)
      rw [D.siteΓ_trivialBase iΛ x₀ hx₀ M d hd π hπ, ← map_mul]
      congr 1
      rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr])

/-- The identification `X_β^*ℱ ≅ 𝒢₀` carried by the arrow `x₀ ⟶ x`. -/
abbrev fiberIso : (modulePullback B S hS (D.relativeMap (D.homOf d.arrow).base)).obj
    d.point.F ≅ x₀.F :=
  asIso (D.homOf d.arrow).fibre

/-- The underlying map of `fiberIso` is the fibre map of the arrow `x₀ ⟶ x`. -/
theorem fiberIso_hom : (D.fiberIso iΛ x₀ hx₀ d).hom = (D.homOf d.arrow).fibre := rfl

/-- For a deformation with trivial base and sections `n j` of `ℱ` over an affine chart `U`
with `∑ j, e j • n j = 0`, where `e j` is the square-zero function of the `j`-th standard basis
vector of `M`, each `n j` lies in `I • ℱ(U)`, `I` being the kernel of restriction to `X₀`. -/
theorem kernel_flat (π : d.point.T ⟶ x₀.T)
    (hπ : (BigFppfOver.toScheme B S hS).map π.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M d hd) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)
    (U : SmallEtale B S hS (D.space x₀.T).1)
    (hU : IsAffine ((SmallEtale.toOver B S hS (D.space x₀.T).1 ⋙
      BigFppfOver.toScheme B S hS).obj U))
    (n : Fin (Module.finrank k M) → d.point.F.val.obj (op (retractionChartDiagram B S hS
      (D.relativeMap π) (D.splitRep π) (D.relativeMap (D.homOf d.arrow).base)
      (D.relativeMap_comp_relativeMap_eq_id π _
        (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ)) U).V))
    (hn : ∑ j, (D.splitFunctions M (D.fiberFunctions iΛ x₀ hx₀ M d hd)
        (ModuleDeformation.stdBasis M j)).1
        (op (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
          (D.relativeMap (D.homOf d.arrow).base)
          (D.relativeMap_comp_relativeMap_eq_id π _
            (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ)) U).V) • n j = 0)
    (j : Fin (Module.finrank k M)) :
    n j ∈ (RingHom.ker (chartDiagramRestrict B S hS
        (D.relativeMap (D.homOf d.arrow).base)
        (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
          (D.relativeMap (D.homOf d.arrow).base)
          (D.relativeMap_comp_relativeMap_eq_id π _
            (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ)) U))) •
      (⊤ : Submodule (chartRing B S hS (D.space d.point.T).1 (D.space d.point.T).2
          (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
            (D.relativeMap (D.homOf d.arrow).base)
            (D.relativeMap_comp_relativeMap_eq_id π _
              (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ)) U).V)
        (d.point.F.val.obj (op (retractionChartDiagram B S hS (D.relativeMap π) (D.splitRep π)
          (D.relativeMap (D.homOf d.arrow).base)
          (D.relativeMap_comp_relativeMap_eq_id π _
            (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ)) U).V))) :=
  D.splitFlat_of_isFlatOver π (D.homOf d.arrow).base
      (D.fiberSection_comp_trivialBase iΛ x₀ hx₀ M d hd π hπ) M (D.fiberFunctions iΛ x₀ hx₀ M d hd)
      (D.isAffine_basePoint iΛ x₀ hx₀) (D.isAffine_fiberPoint iΛ x₀ hx₀ M d hd)
      (D.fiberResidue iΛ x₀ hx₀ M d hd) (D.fiberFunctions_injective iΛ x₀ hx₀ M d hd)
      (D.fiberFunctions_mul_eq iΛ x₀ hx₀ M d hd)
      (D.siteΓ_fiberSection_of_fiberResidue_eq_zero iΛ x₀ hx₀ M d hd)
      d.point.F d.point.quasicoherent d.point.flat U hU n hn j

/-- **The extension `0 ⟶ 𝒢₀ ⊗ M ⟶ r_*ℱ ⟶ 𝒢₀ ⟶ 0` of a deformation with trivial base.** -/
def kernelExtension (π : d.point.T ⟶ x₀.T)
    (hπ : (BigFppfOver.toScheme B S hS).map π.left =
      eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M d hd) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
          eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm) :
    letI := D.residueLinear iΛ x₀ hx₀
    ModuleDeformation.CopowerExtension x₀.F M :=
  letI := D.residueLinear iΛ x₀ hx₀
  retractionCopowerExtension B S hS d.point.F x₀.F (D.fiberIso iΛ x₀ hx₀ d)
    d.point.quasicoherent (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M d hd π hπ)
    (D.kernel_flat iΛ x₀ hx₀ M d hd π hπ)

end CoherentSituation

end AlgebraicGeometry.Space

end
