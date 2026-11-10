module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTangentFinite
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackVerticalAut
public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionTransferExtension
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.DualNumbersUnderSquareZero
public import StacksFrontier.Deformation.Artin.FiniteDimensional.InfExtension

/-!
# The infinitesimal automorphisms of `Coh_{X/Y}` at a finite type point

Let `x` be an object of `𝓕 = 𝓕_{Coh_{X/Y}, k, x₀}` over `k` and `x'` its pushforward to the dual
numbers `k[ε]`. Then `x'` has a trivial base, so its module `ℱ'` gives the extension
`0 ⟶ 𝒢₀ ⊗ ε ⟶ r_*ℱ' ⟶ 𝒢₀ ⟶ 0` of `AlgebraicGeometry.Space.CoherentSituation.kernelExtension`.
An infinitesimal automorphism of `x` is an automorphism of `x'` over the identity of `k[ε]`; its
module automorphism `α` of `ℱ'` restricts to the identity of `𝒢₀`, so `r_*α` is an automorphism of
the extension inducing the identity on both outer terms, and `α` is determined by `r_*α`. The
transport along the scaling `ε ↦ c ε` is a morphism of `x'` over that scaling; its transfer
`r_*ℱ' ⟶ r_*ℱ'` induces `c` on `𝒢₀ ⊗ ε` and the identity on `𝒢₀`, and conjugates `r_*α` into
`r_*α'` for the transported automorphism `α'`, so `r_*α' - 𝟙 = c (r_*α - 𝟙)`. This is the input of
`Deformation.finiteDimensional_infinitesimalAutomorphismLinearLift_of_extension`, which bounds the
infinitesimal automorphisms by `Hom(𝒢₀, 𝒢₀ ⊗ ε)`, finite-dimensional by Stacks 0D0T.

Together with
`AlgebraicGeometry.Space.CoherentSituation.finiteDimensional_tangentModuleAt_cohDef_uLift` this is
Stacks 08W8.

## Main results

* `Deformation.ModuleDeformation.sub_id_eq_smul_of_comp_eq`: an endomorphism of an extension
  acting by `c` on the sub and trivially on the quotient scales `α - 𝟙` by `c`.
* `AlgebraicGeometry.Space.CoherentSituation.finiteDimensional_infinitesimalAutomorphism_cohDef`:
  the infinitesimal automorphisms of `x` form a finite-dimensional space.
* `CoherentSituation.finiteDimensional_tangentSpace_and_infinitesimalAutomorphisms_cohDef`: the
  tangent space and the infinitesimal automorphisms are both finite-dimensional.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] Abelian.hasFiniteBiproducts

universe u

/-- A finite-dimensional `k`-vector space is a module over `kᵐᵒᵖ` through `MulOpposite.unop`. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- The scalar actions of `k` and `kᵐᵒᵖ` on a finite-dimensional `k`-vector space agree. -/
local instance {k : Type u} [Field k] (V : FGModuleCat.{u} k) : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

namespace Deformation.ModuleDeformation

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- **An endomorphism `Φ` of an extension acting by `c` on the sub and trivially on the quotient
scales the differences from the identity of the automorphisms it intertwines**: if `α`, `β` fix
both outer terms and `Φ ≫ β = α ≫ Φ`, then `β - 𝟙 = c • (α - 𝟙)`. -/
theorem sub_id_eq_smul_of_comp_eq {R : Type*} [Semiring R] [Linear R 𝒜] {S : ShortComplex 𝒜}
    (hS : S.ShortExact) (α β Φ : S.X₂ ⟶ S.X₂) (c : R) (hαf : S.f ≫ α = S.f)
    (hαg : α ≫ S.g = S.g) (hβf : S.f ≫ β = S.f) (hβg : β ≫ S.g = S.g)
    (hΦf : S.f ≫ Φ = c • S.f) (hΦg : Φ ≫ S.g = S.g) (hcomm : Φ ≫ β = α ≫ Φ) :
    β - 𝟙 S.X₂ = c • (α - 𝟙 S.X₂) := by
  obtain ⟨t, ht, -⟩ := existsUnique_hom_of_extensionEndomorphism hS α hαf hαg
  obtain ⟨s, hs, -⟩ := existsUnique_hom_of_extensionEndomorphism hS β hβf hβg
  calc β - 𝟙 S.X₂ = Φ ≫ (β - 𝟙 S.X₂) := by rw [← hs, ← Category.assoc Φ S.g, hΦg]
    _ = (α - 𝟙 S.X₂) ≫ Φ := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, hcomm, Category.comp_id, Category.id_comp]
    _ = c • (α - 𝟙 S.X₂) := by
      rw [← ht, Category.assoc, Category.assoc, hΦf, Linear.comp_smul, Linear.comp_smul]

end Deformation.ModuleDeformation

namespace AlgebraicGeometry.Space

section TransferFactor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X₀ X₁ X₂ : AlgebraicSpaces B S hS}
  {r₁ : X₁ ⟶ X₀} {hrep₁ : yoneda.relativelyRepresentable r₁.hom} {i₁ : X₀ ⟶ X₁}
  {hi₁ : i₁ ≫ r₁ = 𝟙 X₀}
  {r₂ : X₂ ⟶ X₀} {hrep₂ : yoneda.relativelyRepresentable r₂.hom} {i₂ : X₀ ⟶ X₂}
  {hi₂ : i₂ ≫ r₂ = 𝟙 X₀}
  {k : Type u} [Field k] {M₁ M₂ : FGModuleCat.{u} k}
  {ψ₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O)}
  {ψ'₁ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₁.1 X₁.2).O)}
  {ψ'₂ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O)}
  {ι₁ : ↥M₁ →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₁.1 X₁.2).O)}
  {ι₂ : ↥M₂ →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O)}
  (hs₁ : IsSplitThickeningBy B S hS r₁ hrep₁ i₁ hi₁ M₁ ψ₀ ψ'₁ ι₁)
  (hs₂ : IsSplitThickeningBy B S hS r₂ hrep₂ i₂ hi₂ M₂ ψ₀ ψ'₂ ι₂)
  {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
  {G : Modules.{u, u} B S hS X₀.1 X₀.2}
  (ψ₁ : (modulePullback B S hS i₁).obj F₁ ≅ G) (ψ₂ : (modulePullback B S hS i₂).obj F₂ ≅ G)
  (hF₁ : F₁.IsQuasicoherentOnSite) (hF₂ : F₂.IsQuasicoherentOnSite)

/-- **The transfer carries the factored multiplication by `v` to the factored multiplication by
`f v`.** -/
theorem retractionMultiplicationFactor_comp_transferMap (f : M₁ ⟶ M₂) (h : X₂ ⟶ X₁)
    (hr : h ≫ r₁ = r₂) (hih : i₂ ≫ h = i₁) (θ : (modulePullback B S hS h).obj F₁ ⟶ F₂)
    (hψ : ψ₁.hom = (modulePullbackTriangle B S hS hih).hom.app F₁ ≫
      (modulePullback B S hS i₂).map θ ≫ ψ₂.hom)
    (hι : ∀ (U : SmallEtale B S hS X₀.1) (v : ↥M₁),
      chartDiagramRestrict B S hS h (transferChartDiagram B S hS r₁ hrep₁ r₂ hrep₂ h hr U)
        ((ι₁ v).1 (op ((smallBaseChange B S hS r₁ hrep₁).obj U))) =
          (ι₂ (f.hom.hom v)).1 (op ((smallBaseChange B S hS r₂ hrep₂).obj U))) (v : ↥M₁) :
    retractionMultiplicationFactor B S hS F₁ G ψ₁ hF₁ hs₁ v ≫
        transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ =
      retractionMultiplicationFactor B S hS F₂ G ψ₂ hF₂ hs₂ (f.hom.hom v) := by
  have := epi_retractionProjection B S hS F₁ G ψ₁ hF₁ hs₁
  let Φ := transferMap B S hS r₁ hrep₁ r₂ hrep₂ h hr θ
  let p₁ := retractionProjection B S hS r₁ hrep₁ i₁ hi₁ F₁ G ψ₁
  let p₂ := retractionProjection B S hS r₂ hrep₂ i₂ hi₂ F₂ G ψ₂
  have e1 : p₁ ≫ retractionMultiplicationFactor B S hS F₁ G ψ₁ hF₁ hs₁ v =
      retractionMultiplication B S hS r₁ hrep₁ M₁ ι₁ F₁ v :=
    retractionProjection_comp_factor B S hS F₁ G ψ₁ hF₁ hs₁ v
  have e2 : retractionMultiplication B S hS r₁ hrep₁ M₁ ι₁ F₁ v ≫ Φ =
      Φ ≫ retractionMultiplication B S hS r₂ hrep₂ M₂ ι₂ F₂ (f.hom.hom v) :=
    transferMap_comp_globalSmul B S hS r₁ hrep₁ r₂ hrep₂ h hr θ _ _ (fun U => hι U v)
  have e3 : Φ ≫ p₂ = p₁ :=
    transferMap_comp_retractionProjection B S hS ψ₁ ψ₂ h hr hih θ hψ
  have e4 : p₂ ≫ retractionMultiplicationFactor B S hS F₂ G ψ₂ hF₂ hs₂ (f.hom.hom v) =
      retractionMultiplication B S hS r₂ hrep₂ M₂ ι₂ F₂ (f.hom.hom v) :=
    retractionProjection_comp_factor B S hS F₂ G ψ₂ hF₂ hs₂ (f.hom.hom v)
  have key : p₁ ≫ (retractionMultiplicationFactor B S hS F₁ G ψ₁ hF₁ hs₁ v ≫ Φ) =
      p₁ ≫ retractionMultiplicationFactor B S hS F₂ G ψ₂ hF₂ hs₂ (f.hom.hom v) := by
    rw [← Category.assoc, e1, e2, ← e4, ← Category.assoc, e3]
  exact (cancel_epi p₁).1 key

end TransferFactor

section CopowerAut

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X₀ X' : AlgebraicSpaces B S hS} {r : X' ⟶ X₀}
  {hrep : yoneda.relativelyRepresentable r.hom} {i : X₀ ⟶ X'} {hi : i ≫ r = 𝟙 X₀}
  {k : Type u} [Field k] {M : FGModuleCat.{u} k}
  {ψ₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O)}
  {ψ' : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  {ι : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)}
  (hs : IsSplitThickeningBy B S hS r hrep i hi M ψ₀ ψ' ι)
  {F : Modules.{u, u} B S hS X'.1 X'.2} {G : Modules.{u, u} B S hS X₀.1 X₀.2}
  (ψ : (modulePullback B S hS i).obj F ≅ G) (hF : F.IsQuasicoherentOnSite)

/-- **The direct image of an endomorphism inducing the identity of `𝒢` fixes `𝒢 ⊗ M`.** -/
theorem copowerDesc_comp_retractionPushforward_map (a : F ⟶ F)
    (ha : (modulePullback B S hS i).map a ≫ ψ.hom = ψ.hom) :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    Deformation.ModuleDeformation.copowerDesc G
        (retractionMultiplicationFamily B S hS F G ψ hF hs) ≫
        (retractionPushforward B S hS r hrep).map a =
      Deformation.ModuleDeformation.copowerDesc G
        (retractionMultiplicationFamily B S hS F G ψ hF hs) := by
  let := retractionLinear B S hS (X₀ := X₀) ψ₀
  refine biproduct.hom_ext' _ _ fun j => ?_
  rw [Deformation.ModuleDeformation.ι_copowerDesc_assoc,
    Deformation.ModuleDeformation.ι_copowerDesc]
  exact retractionMultiplicationFactor_comp_map B S hS hs ψ hF a ha _

/-- **An endomorphism of the direct image scaling the factored multiplications by `c` scales
`𝒢 ⊗ M ⟶ r_*ℱ` by `c`.** -/
theorem copowerDesc_comp_eq_smul
    (Φ : (retractionPushforward B S hS r hrep).obj F ⟶ (retractionPushforward B S hS r hrep).obj F)
    (c : k) (hΦ : ∀ v, retractionMultiplicationFactor B S hS F G ψ hF hs v ≫ Φ =
      retractionMultiplicationFactor B S hS F G ψ hF hs (c • v)) :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    Deformation.ModuleDeformation.copowerDesc G
        (retractionMultiplicationFamily B S hS F G ψ hF hs) ≫ Φ =
      c • Deformation.ModuleDeformation.copowerDesc G
        (retractionMultiplicationFamily B S hS F G ψ hF hs) := by
  let := retractionLinear B S hS (X₀ := X₀) ψ₀
  refine biproduct.hom_ext' _ _ fun j => ?_
  rw [Deformation.ModuleDeformation.ι_copowerDesc_assoc, Linear.comp_smul,
    Deformation.ModuleDeformation.ι_copowerDesc]
  exact (hΦ _).trans ((retractionMultiplicationFamily B S hS F G ψ hF hs).map_smul c _)

end CopowerAut

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory predefCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {x₀ : CoherentObject D}
  {hx₀ : D.cohQ.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-! ### The transfer along a morphism of deformations with trivial bases -/

/-- `AlgebraicGeometry.Space.CoherentSituation.morphismBase_transfer_functions` with the trivial
base of the target given as a variable. -/
theorem morphismBase_transfer_functions_of_eq {M N : FGModuleCat.{u} k} {f : M ⟶ N}
    {a b : DeformationObject iΛ D.cohQ x₀ hx₀}
    (ha : a.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hb : b.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)
    (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ a b)
    (hm : m.ringHom = eqToHom ha ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f ≫
      eqToHom hb.symm)
    (πa : a.point.T ⟶ x₀.T) (πb : b.point.T ⟶ x₀.T) (hab : (D.homOf m.arrow).base ≫ πa = πb)
    (hr : D.relativeMap (D.homOf m.arrow).base ≫ D.relativeMap πa = D.relativeMap πb)
    (U : SmallEtale B S hS (D.space x₀.T).1) (v : ↥M) :
    chartDiagramRestrict B S hS (D.relativeMap ((D.homOf m.arrow).base))
        (transferChartDiagram B S hS (D.relativeMap πa) (D.splitRep πa)
          (D.relativeMap πb) (D.splitRep πb) (D.relativeMap ((D.homOf m.arrow).base)) hr U)
        (((D.splitFunctions M (D.fiberFunctions iΛ x₀ hx₀ M a ha)) v).1
          (op ((smallBaseChange B S hS (D.relativeMap πa) (D.splitRep πa)).obj U))) =
      ((D.splitFunctions N (D.fiberFunctions iΛ x₀ hx₀ N b hb)) (f.hom.hom v)).1
        (op ((smallBaseChange B S hS (D.relativeMap πb) (D.splitRep πb)).obj U)) := by
  subst hab
  exact D.morphismBase_transfer_functions ha hb m hm πa U v

variable {M : FGModuleCat.{u} k} {d : DeformationObject iΛ D.cohQ x₀ hx₀}
  (hd : d.algebra = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
  (π : d.point.T ⟶ x₀.T)
  (hπ : (BigFppfOver.toScheme B S hS).map π.left =
    eqToHom (D.toScheme_defPoint iΛ x₀ hx₀ M d hd) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))) ≫
        eqToHom (D.toScheme_basePoint (k := k) iΛ x₀ hx₀).symm)

/-- The section followed by the base of a reversed arrow `d ⟶ d` is the section. -/
theorem relativeMap_comp_arrowBase (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ d d) :
    D.relativeMap (D.homOf d.arrow).base ≫ D.relativeMap (D.homOf m.arrow).base =
      D.relativeMap (D.homOf d.arrow).base :=
  (D.relativeMap_comp_trivialBase (D.homOf m.arrow).base (D.homOf d.arrow).base).trans
    (congrArg (fun g => D.relativeMap g) (D.homOf_arrow_base_comp m))

section Transfer

variable {f : M ⟶ M} (m : DeformationMorphism iΛ D.cohQ x₀ hx₀ d d)
  (hm : m.ringHom = eqToHom hd ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map f ≫
    eqToHom hd.symm)

include hπ hm in
/-- The base of a reversed arrow `d ⟶ d` over `k[f]` followed by the trivial base is the trivial
base, on base changes. -/
theorem relativeMap_comp_trivialBase_self :
    D.relativeMap (D.homOf m.arrow).base ≫ D.relativeMap π = D.relativeMap π :=
  (D.relativeMap_comp_trivialBase π (D.homOf m.arrow).base).trans
    (congrArg (fun g => D.relativeMap g) (D.morphismBase_comp_trivialBase hd hd m hm π hπ π hπ))

/-- **The transfer `r_*ℱ ⟶ r_*ℱ` along a reversed arrow `d ⟶ d` over `k[f]`.** -/
def kernelTransfer :
    (retractionPushforward B S hS (D.relativeMap π) (D.splitRep π)).obj d.point.F ⟶
      (retractionPushforward B S hS (D.relativeMap π) (D.splitRep π)).obj d.point.F :=
  transferMap B S hS (D.relativeMap π) (D.splitRep π) (D.relativeMap π) (D.splitRep π)
    (D.relativeMap (D.homOf m.arrow).base) (D.relativeMap_comp_trivialBase_self hd π hπ m hm)
    (D.homOf m.arrow).fibre

/-- **The transfer induces the identity of `𝒢₀`.** -/
theorem kernelTransfer_comp_p :
    letI := D.residueLinear iΛ x₀ hx₀
    D.kernelTransfer hd π hπ m hm ≫ (D.kernelExtension iΛ x₀ hx₀ M d hd π hπ).p =
      (D.kernelExtension iΛ x₀ hx₀ M d hd π hπ).p :=
  transferMap_comp_retractionProjection B S hS (D.fiberIso iΛ x₀ hx₀ d)
    (D.fiberIso iΛ x₀ hx₀ d) (D.relativeMap (D.homOf m.arrow).base)
    (D.relativeMap_comp_trivialBase_self hd π hπ m hm) (D.relativeMap_comp_arrowBase m)
    (D.homOf m.arrow).fibre (D.homOf_arrow_fibre_eq m (D.relativeMap_comp_arrowBase m))

/-- **The transfer carries the multiplication by `v` to the multiplication by `f v`.** -/
theorem retractionMultiplicationFactor_comp_kernelTransfer (v : ↥M) :
    retractionMultiplicationFactor B S hS d.point.F x₀.F (D.fiberIso iΛ x₀ hx₀ d)
        d.point.quasicoherent (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M d hd π hπ) v ≫
        D.kernelTransfer hd π hπ m hm =
      retractionMultiplicationFactor B S hS d.point.F x₀.F (D.fiberIso iΛ x₀ hx₀ d)
        d.point.quasicoherent (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M d hd π hπ)
          (f.hom.hom v) := by
  have hι := fun U v => D.morphismBase_transfer_functions_of_eq hd hd m hm π π
    (D.morphismBase_comp_trivialBase hd hd m hm π hπ π hπ)
    (D.relativeMap_comp_trivialBase_self hd π hπ m hm) U v
  exact retractionMultiplicationFactor_comp_transferMap B S hS
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M d hd π hπ)
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M d hd π hπ) (D.fiberIso iΛ x₀ hx₀ d)
    (D.fiberIso iΛ x₀ hx₀ d) d.point.quasicoherent d.point.quasicoherent f
    (D.relativeMap (D.homOf m.arrow).base) (D.relativeMap_comp_trivialBase_self hd π hπ m hm)
    (D.relativeMap_comp_arrowBase m) (D.homOf m.arrow).fibre
    (D.homOf_arrow_fibre_eq m (D.relativeMap_comp_arrowBase m)) hι v

end Transfer

/-! ### Automorphisms over the identity of `k[M]` -/

section Automorphism

variable (n : DeformationMorphism iΛ D.cohQ x₀ hx₀ d d) (hn : n.ringHom = 𝟙 d.algebra)

include hn in
/-- **The base of a reversed arrow `d ⟶ d` over the identity is the identity.** -/
theorem arrowBase_eq_id : (D.homOf n.arrow).base = 𝟙 d.point.T := by
  have h := D.toScheme_map_morphism_base iΛ x₀ hx₀ n
  rw [hn] at h
  have h' : (BigFppfOver.toScheme B S hS).map (D.homOf n.arrow).base.left =
      (BigFppfOver.toScheme B S hS).map (𝟙 d.point.T.left) := by
    rw [h, CategoryTheory.Functor.map_id]
    change eqToHom _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ eqToHom _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
  exact CostructuredArrow.hom_ext _ _ ((BigFppfOver.toScheme B S hS).map_injective h')

/-- **The automorphism `r_*α` of the extension** induced by a reversed arrow `d ⟶ d` over the
identity, `α` its module automorphism. -/
def kernelAut :
    (retractionPushforward B S hS (D.relativeMap π) (D.splitRep π)).obj d.point.F ⟶
      (retractionPushforward B S hS (D.relativeMap π) (D.splitRep π)).obj d.point.F :=
  (retractionPushforward B S hS (D.relativeMap π) (D.splitRep π)).map
    (D.autOf (D.homOf n.arrow).base (D.arrowBase_eq_id n hn) d.point.F (D.homOf n.arrow).fibre)

/-- The morphism `r_*α` is an isomorphism. -/
instance isIso_kernelAut : IsIso (D.kernelAut π n hn) := by
  unfold kernelAut
  infer_instance

/-- The module automorphism restricts to the identity of `𝒢₀`. -/
theorem map_autOf_comp_fiberIso :
    (modulePullback B S hS (D.relativeMap (D.homOf d.arrow).base)).map
        (D.autOf (D.homOf n.arrow).base (D.arrowBase_eq_id n hn) d.point.F
          (D.homOf n.arrow).fibre) ≫ (D.fiberIso iΛ x₀ hx₀ d).hom =
      (D.fiberIso iΛ x₀ hx₀ d).hom :=
  D.map_autOf_comp_of_eq (D.homOf d.arrow).base (D.homOf n.arrow).base
    (D.arrowBase_eq_id n hn) d.point.F (D.homOf d.arrow).fibre (D.homOf n.arrow).fibre
    (D.relativeMap_comp_arrowBase n) (D.homOf_arrow_fibre_eq n (D.relativeMap_comp_arrowBase n))

/-- **`r_*α` induces the identity of `𝒢₀`.** -/
theorem kernelAut_comp_p :
    letI := D.residueLinear iΛ x₀ hx₀
    D.kernelAut π n hn ≫ (D.kernelExtension iΛ x₀ hx₀ M d hd π hπ).p =
      (D.kernelExtension iΛ x₀ hx₀ M d hd π hπ).p :=
  retractionPushforward_map_comp_projection B S hS (D.fiberIso iΛ x₀ hx₀ d) _
    (D.map_autOf_comp_fiberIso n hn)

/-- **`r_*α` induces the identity of `𝒢₀ ⊗ M`.** -/
theorem f_comp_kernelAut :
    letI := D.residueLinear iΛ x₀ hx₀
    (D.kernelExtension iΛ x₀ hx₀ M d hd π hπ).shortComplex.f ≫ D.kernelAut π n hn =
      (D.kernelExtension iΛ x₀ hx₀ M d hd π hπ).shortComplex.f := by
  let := D.residueLinear iΛ x₀ hx₀
  exact copowerDesc_comp_retractionPushforward_map B S hS
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ M d hd π hπ) (D.fiberIso iΛ x₀ hx₀ d)
    d.point.quasicoherent _ (D.map_autOf_comp_fiberIso n hn)

end Automorphism

/-- The base and fibre of the comparison of a composite of arrows in `Coh_{X/Y}`. -/
private theorem relativeMap_comp_fibre_of_eq_comp {A A' A'' : CoherentObject D}
    (a : A ⟶ A') (b : A' ⟶ A'') (c : A ⟶ A'') (h : c = a ≫ b) :
    ∃ hih : D.relativeMap (D.homOf a).base ≫ D.relativeMap (D.homOf b).base =
        D.relativeMap (D.homOf c).base,
      (D.homOf c).fibre = (modulePullbackTriangle B S hS hih).hom.app A''.F ≫
        (modulePullback B S hS (D.relativeMap (D.homOf a).base)).map (D.homOf b).fibre ≫
          (D.homOf a).fibre := by
  have hc : D.homOf c = (D.homOf a).comp (D.homOf b) :=
    (congrArg D.homOf h).trans (D.categoryData.composition _ _)
  have hih : D.relativeMap (D.homOf a).base ≫ D.relativeMap (D.homOf b).base =
      D.relativeMap (D.homOf c).base := by
    rw [hc]
    exact (baseChangeMap_comp D.f _ _).symm
  exact ⟨hih, CoherentHom.fibre_eq_of_eq_comp D (D.homOf a) (D.homOf b) (D.homOf c) hc hih⟩

/-- **`r_*α` is multiplicative**, for reversed arrows composing in the opposite order. -/
theorem kernelAut_comp (n₁ n₂ n₁₂ : DeformationMorphism iΛ D.cohQ x₀ hx₀ d d)
    (h₁ : n₁.ringHom = 𝟙 d.algebra) (h₂ : n₂.ringHom = 𝟙 d.algebra)
    (h₁₂ : n₁₂.ringHom = 𝟙 d.algebra) (harrow : n₁₂.arrow = n₂.arrow ≫ n₁.arrow) :
    D.kernelAut π n₁₂ h₁₂ = D.kernelAut π n₁ h₁ ≫ D.kernelAut π n₂ h₂ := by
  obtain ⟨hih, hf⟩ := D.relativeMap_comp_fibre_of_eq_comp n₂.arrow n₁.arrow n₁₂.arrow harrow
  unfold kernelAut
  rw [D.autOf_comp _ _ _ (D.arrowBase_eq_id n₂ h₂) (D.arrowBase_eq_id n₁ h₁)
    (D.arrowBase_eq_id n₁₂ h₁₂) d.point.F _ _ _ hih hf, Functor.map_comp]

include hd in
/-- **A reversed arrow over the identity is determined by `r_*α`.** -/
theorem eq_of_kernelAut_eq (n n' : DeformationMorphism iΛ D.cohQ x₀ hx₀ d d)
    (hn : n.ringHom = 𝟙 d.algebra) (hn' : n'.ringHom = 𝟙 d.algebra)
    (h : D.kernelAut π n hn = D.kernelAut π n' hn') : n = n' := by
  have := D.isAffine_basePoint iΛ x₀ hx₀
  have := D.isAffine_fiberPoint iΛ x₀ hx₀ M d hd
  have h' := retractionPushforward_map_injective B S hS (D.relativeMap π) (D.splitRep π)
    (D.isAffineHom_relativeMap π) d.point.quasicoherent h
  have hh := CoherentHom.eq_of_autOf_eq D (D.homOf n.arrow) (D.homOf n'.arrow)
    (D.arrowBase_eq_id n hn) (D.arrowBase_eq_id n' hn') h'
  exact DeformationMorphism.ext_of_components _ _ _ _ (hn.trans hn'.symm)
    ((Equiv.cast (D.categoryData.hom_type _ _)).injective hh)

/-! ### The infinitesimal automorphisms -/

section Final

variable (iΛ x₀ hx₀)

variable {x : (D.cohDef iΛ x₀ hx₀).carrier}
  (PF : ChosenPushforwardsAt (D.cohDef iΛ x₀ hx₀).projection x)

/-- The pushforward of `x` to the dual numbers. -/
abbrev dualPoint : (D.cohDef iΛ x₀ hx₀).carrier :=
  (PF.obj (dualNumbersUnder (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))).1

/-- The pushforward of `x` to the dual numbers lies over `k[ε]`. -/
theorem algebra_dualPoint :
    ((D.cohDef iΛ x₀ hx₀).objects (D.dualPoint iΛ x₀ hx₀ PF)).algebra =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).obj (FGModuleCat.of k (ULift.{u} k)) :=
  ((D.cohDef iΛ x₀ hx₀).object_projection _).symm.trans
    ((PF.obj (dualNumbersUnder (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))).2.trans
      (algebrasUnder_artinianDualNumbers_right_eq ((D.cohDef iΛ x₀ hx₀).projection.obj x)))

/-- **The pushforward of an object over `k` to the dual numbers has a trivial base.** -/
theorem hasTrivialBase'_dualPoint
    (hx : (D.cohDef iΛ x₀ hx₀).projection.obj x = Deformation.residueFieldObject.{u, u, u} Λ k) :
    D.HasTrivialBase' iΛ x₀ hx₀ (FGModuleCat.of k (ULift.{u} k))
      ((D.cohDef iΛ x₀ hx₀).objects (D.dualPoint iΛ x₀ hx₀ PF))
      (D.algebra_dualPoint iΛ x₀ hx₀ PF) := by
  let p := (D.cohDef iΛ x₀ hx₀).projection
  let 𝔇 := dualNumbersUnder (p := p) (x := x)
  have hb : ((D.cohDef iΛ x₀ hx₀).objects x).algebra =
      Deformation.residueFieldObject.{u, u, u} Λ k :=
    ((D.cohDef iΛ x₀ hx₀).object_projection x).symm.trans hx
  have : p.IsHomLift 𝔇.hom (PF.inclusion 𝔇) := (PF.inclusion_cocartesian 𝔇).toIsHomLift
  have hring : ((D.cohDef iΛ x₀ hx₀).morphisms x _ (PF.inclusion 𝔇)).ringHom =
      eqToHom hb ≫ (squareZeroCrossUnder.{u, u, u} (Deformation.residueFieldObject.{u, u, u} Λ k)
        (FGModuleCat.of k (ULift.{u} k))).hom ≫
          eqToHom (D.algebra_dualPoint iΛ x₀ hx₀ PF).symm := by
    rw [← (D.cohDef iΛ x₀ hx₀).morphism_projection (PF.inclusion 𝔇),
      IsHomLift.fac' p 𝔇.hom (PF.inclusion 𝔇)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    exact eqToHom_comp_dualNumbers_hom_comp_eqToHom (p.obj x) _ _ hx _ _ hb
      (D.algebra_dualPoint iΛ x₀ hx₀ PF)
  exact D.hasTrivialBase'_of_morphism iΛ x₀ hx₀ _ ((D.cohDef iΛ x₀ hx₀).objects x) _ hb
    (D.algebra_dualPoint iΛ x₀ hx₀ PF) _ hring

/-- A vertical endomorphism of the predeformation category has the identity as ring map. -/
theorem ringHom_eq_id_of_isHomLift {y : (D.cohDef iΛ x₀ hx₀).carrier}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (φ : y ⟶ y)
    [(D.cohDef iΛ x₀ hx₀).projection.IsHomLift (𝟙 A) φ] :
    ((D.cohDef iΛ x₀ hx₀).morphisms y y φ).ringHom = 𝟙 _ :=
  (ringHom_eq_eqToHom_of_isHomLift iΛ (A := A) φ).trans (eqToHom_refl _ _)

/-- **`Hom(𝒢₀, 𝒢₀ ⊗ M)` is finite-dimensional.** -/
theorem finiteDimensional_hom_copowerObj_basePoint (M : FGModuleCat.{u} k) :
    letI := D.residueLinear iΛ x₀ hx₀
    FiniteDimensional k (x₀.F ⟶ ModuleDeformation.copowerObj x₀.F M) := by
  let : HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2) :=
    HasExt.standard _
  let := D.residueLinear iΛ x₀ hx₀
  obtain ⟨-, h₀⟩ := D.finiteDimensional_ext_one_and_hom_basePoint iΛ x₀ hx₀
  have : FiniteDimensional k (Abelian.Ext x₀.F x₀.F 0) :=
    Module.Finite.equiv (Abelian.Ext.linearEquiv₀ (R := k)).symm
  have := ModuleDeformation.finiteDimensional_ext_copowerObj x₀.F x₀.F M 0
  exact Module.Finite.equiv (Abelian.Ext.linearEquiv₀ (R := k)
    (X := x₀.F) (Y := ModuleDeformation.copowerObj x₀.F M))

variable (hT : D.HasTrivialBase' iΛ x₀ hx₀ (FGModuleCat.of k (ULift.{u} k))
  ((D.cohDef iΛ x₀ hx₀).objects (D.dualPoint iΛ x₀ hx₀ PF)) (D.algebra_dualPoint iΛ x₀ hx₀ PF))

/-- The endomorphism of the pushforward to the dual numbers underlying an infinitesimal
automorphism. -/
abbrev infEndo (a : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    D.dualPoint iΛ x₀ hx₀ PF ⟶ D.dualPoint iΛ x₀ hx₀ PF :=
  a.val.asIso.hom.1

/-- The endomorphism underlying a product `a * b` is the composite of those of `b` and `a`. -/
theorem infEndo_mul (a b : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    D.infEndo iΛ x₀ hx₀ PF (a * b) = D.infEndo iΛ x₀ hx₀ PF b ≫ D.infEndo iΛ x₀ hx₀ PF a :=
  rfl

/-- The endomorphism underlying an infinitesimal automorphism lies over the identity of the dual
numbers. -/
theorem ringHom_infEndo (a : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a)).ringHom = 𝟙 _ :=
  haveI : (D.cohDef iΛ x₀ hx₀).projection.IsHomLift
      (𝟙 (dualNumbersUnder (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x)).right)
      (D.infEndo iΛ x₀ hx₀ PF a) := a.val.asIso.hom.2
  D.ringHom_eq_id_of_isHomLift iΛ x₀ hx₀
    (A := (dualNumbersUnder (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x)).right) _

/-- **`r_*α` is multiplicative on infinitesimal automorphisms.** -/
theorem kernelAut_infEndo_mul (a b : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF (a * b)))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF (a * b)) =
      D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF b))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF b) ≫
        D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF a) :=
  D.kernelAut_comp hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF b))
    ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
    ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF (a * b)))
    (D.ringHom_infEndo iΛ x₀ hx₀ PF b)
    (D.ringHom_infEndo iΛ x₀ hx₀ PF a) (D.ringHom_infEndo iΛ x₀ hx₀ PF (a * b))
    ((congrArg (fun φ => ((D.cohDef iΛ x₀ hx₀).morphisms _ _ φ).arrow)
      (D.infEndo_mul iΛ x₀ hx₀ PF a b)).trans
      ((D.cohDef iΛ x₀ hx₀).reversed_composition (D.infEndo iΛ x₀ hx₀ PF b)
        (D.infEndo iΛ x₀ hx₀ PF a)))

/-- The automorphism `r_*α` of an infinitesimal automorphism. -/
def infAut (a : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    Aut ((retractionPushforward B S hS (D.relativeMap hT.choose) (D.splitRep hT.choose)).obj
      ((D.cohDef iΛ x₀ hx₀).objects (D.dualPoint iΛ x₀ hx₀ PF)).point.F) :=
  Aut.of <| @asIso _ _ _ _
    (D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF a))
    (D.isIso_kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF a))

/-- The underlying morphism of `infAut c` is `r_*α` for the module automorphism `α` of `c`. -/
theorem infAut_hom (c : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    (D.infAut iΛ x₀ hx₀ PF hT c).asIso.hom =
      D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF c))
        (D.ringHom_infEndo iΛ x₀ hx₀ PF c) :=
  rfl

/-- The automorphism `r_*α` of a product is the product of the automorphisms. -/
theorem infAut_mul (a b : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    D.infAut iΛ x₀ hx₀ PF hT (a * b) = D.infAut iΛ x₀ hx₀ PF hT a * D.infAut iΛ x₀ hx₀ PF hT b := by
  refine Aut.ext (Iso.ext ?_)
  rw [Aut.mul_asIso]
  exact ((D.infAut_hom iΛ x₀ hx₀ PF hT (a * b)).trans
    ((D.kernelAut_infEndo_mul iΛ x₀ hx₀ PF hT a b).trans
      (congrArg₂ (· ≫ ·) (D.infAut_hom iΛ x₀ hx₀ PF hT b).symm
        (D.infAut_hom iΛ x₀ hx₀ PF hT a).symm)))

/-- **The action of the infinitesimal automorphisms on `r_*ℱ'`.** -/
def infAction :
    infinitesimalAutomorphismKernel PF
        (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x)) →*
      Aut ((retractionPushforward B S hS (D.relativeMap hT.choose) (D.splitRep hT.choose)).obj
        ((D.cohDef iΛ x₀ hx₀).objects (D.dualPoint iΛ x₀ hx₀ PF)).point.F) :=
  MonoidHom.mk' (D.infAut iΛ x₀ hx₀ PF hT) (D.infAut_mul iΛ x₀ hx₀ PF hT)

/-- The underlying morphism of the action of `a` is `r_*α` for the module automorphism `α` of `a`.
-/
theorem infAction_hom (a : infinitesimalAutomorphismKernel PF
    (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x))) :
    (D.infAction iΛ x₀ hx₀ PF hT a).asIso.hom =
      D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF a) :=
  rfl

/-- **The action of the infinitesimal automorphisms on `r_*ℱ'` is faithful.** -/
theorem infAction_injective : Function.Injective (D.infAction iΛ x₀ hx₀ PF hT) := by
  intro a b h
  have hn := D.eq_of_kernelAut_eq (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose _ _
    (D.ringHom_infEndo iΛ x₀ hx₀ PF a) (D.ringHom_infEndo iΛ x₀ hx₀ PF b)
    (congrArg (fun t => t.asIso.hom) h)
  have hφ : D.infEndo iΛ x₀ hx₀ PF a = D.infEndo iΛ x₀ hx₀ PF b :=
    ((D.cohDef iΛ x₀ hx₀).morphisms _ _).injective hn
  exact Subtype.ext (Aut.ext (Iso.ext (Functor.Fiber.hom_ext hφ)))

/-- The reversed arrow of the transport along the scaling `ε ↦ c ε`. -/
abbrev scalingMorphism (c : k) :=
  (D.cohDef iΛ x₀ hx₀).morphisms (D.dualPoint iΛ x₀ hx₀ PF) (D.dualPoint iΛ x₀ hx₀ PF)
    (PF.map (tangentScaling (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x) c))

/-- The ring map of the transport along the scaling is the scaling of `k[ε]`. -/
theorem ringHom_scalingMorphism (c : k) :
    (D.scalingMorphism iΛ x₀ hx₀ PF c).ringHom =
      eqToHom (D.algebra_dualPoint iΛ x₀ hx₀ PF) ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map
        (FGModuleCat.ofHom (c • LinearMap.id : ULift.{u} k →ₗ[k] ULift.{u} k)) ≫
          eqToHom (D.algebra_dualPoint iΛ x₀ hx₀ PF).symm := by
  let p := (D.cohDef iΛ x₀ hx₀).projection
  let f := tangentScaling (p := p) (x := x) c
  have : p.IsHomLift f.right (PF.map f) := PF.map_isHomLift f
  rw [← (D.cohDef iΛ x₀ hx₀).morphism_projection (PF.map f), IsHomLift.fac' p f.right (PF.map f)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  exact eqToHom_comp_algebrasUnder_map_comp_eqToHom (p.obj x) _ _ _ _ _

/-- **The transported infinitesimal automorphism is conjugate under the transfer along the
scaling.** -/
theorem kernelAut_comp_kernelTransfer_scaling (c : k)
    (a b : infinitesimalAutomorphismKernel PF
      (tangentReduction (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x)))
    (hab : b.val = PF.transportAutHom
      (tangentScaling (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x) c) a.val) :
    D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF a) ≫
        D.kernelTransfer (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose hT.choose_spec _
          (D.ringHom_scalingMorphism iΛ x₀ hx₀ PF c) =
      D.kernelTransfer (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose hT.choose_spec _
          (D.ringHom_scalingMorphism iΛ x₀ hx₀ PF c) ≫
        D.kernelAut hT.choose ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF b))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF b) := by
  let f := tangentScaling (p := (D.cohDef iΛ x₀ hx₀).projection) (x := x) c
  let na := (D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a)
  let nb := (D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF b)
  let mc := D.scalingMorphism iΛ x₀ hx₀ PF c
  have hb' : D.infEndo iΛ x₀ hx₀ PF b = PF.transportHom f a.val :=
    congrArg (fun t => t.asIso.hom.1) hab
  have he : PF.map f ≫ D.infEndo iΛ x₀ hx₀ PF b = D.infEndo iΛ x₀ hx₀ PF a ≫ PF.map f := by
    rw [hb']
    exact PF.map_transportHom f a.val
  have hcomp : nb.arrow ≫ mc.arrow = mc.arrow ≫ na.arrow := by
    rw [← (D.cohDef iΛ x₀ hx₀).reversed_composition, ←
      (D.cohDef iΛ x₀ hx₀).reversed_composition, he]
  obtain ⟨hih₁, hf₁⟩ := D.relativeMap_comp_fibre_of_eq_comp nb.arrow mc.arrow _ rfl
  obtain ⟨hih₂, hf₂⟩ := D.relativeMap_comp_fibre_of_eq_comp mc.arrow na.arrow _ hcomp
  have hfib := D.fibre_comp_autOf_of_eq (D.homOf mc.arrow).base (D.homOf (nb.arrow ≫ mc.arrow)).base
    (D.homOf na.arrow).base (D.homOf nb.arrow).base
    (D.arrowBase_eq_id na (D.ringHom_infEndo iΛ x₀ hx₀ PF a))
    (D.arrowBase_eq_id nb (D.ringHom_infEndo iΛ x₀ hx₀ PF b)) _ (D.homOf na.arrow).fibre
    (D.homOf nb.arrow).fibre (D.homOf mc.arrow).fibre hih₁ hih₂ (hf₁.symm.trans hf₂)
  exact transferMap_naturality B S hS _ _ _ _ _ _ _ _ _ _ hfib.symm

/-- **The transfer along the scaling acts by `c` on `𝒢₀ ⊗ ε`.** -/
theorem f_comp_kernelTransfer_scaling (c : k) :
    letI := D.residueLinear iΛ x₀ hx₀
    (D.kernelExtension iΛ x₀ hx₀ _ _ (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose
        hT.choose_spec).shortComplex.f ≫
        D.kernelTransfer (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose hT.choose_spec _
          (D.ringHom_scalingMorphism iΛ x₀ hx₀ PF c) =
      c • (D.kernelExtension iΛ x₀ hx₀ _ _ (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose
        hT.choose_spec).shortComplex.f := by
  let := D.residueLinear iΛ x₀ hx₀
  exact copowerDesc_comp_eq_smul B S hS
    (D.kernel_isSplitThickeningBy iΛ x₀ hx₀ _ _ (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose
      hT.choose_spec) (D.fiberIso iΛ x₀ hx₀ _) _ _ c fun v =>
    D.retractionMultiplicationFactor_comp_kernelTransfer _ hT.choose hT.choose_spec _ _ v

/-- **Stacks 08W8, the infinitesimal automorphisms.** The infinitesimal automorphisms of
`𝓕_{Coh_{X/Y}, k, x₀}` at an object over `k` are finite-dimensional. -/
theorem finiteDimensional_infinitesimalAutomorphism_cohDef
    (h𝓕 : IsDeformationCategory.{u, u, u} (D.cohDef iΛ x₀ hx₀).projection)
    (hx : (D.cohDef iΛ x₀ hx₀).projection.obj x = Deformation.residueFieldObject.{u, u, u} Λ k) :
    FiniteDimensional k ↥((infinitesimalAutomorphismLinearLift.{u, u, u} PF
      h𝓕.satisfiesRS).functor.obj (FGModuleCat.of k (ULift.{u} k))) := by
  have hT := D.hasTrivialBase'_dualPoint iΛ x₀ hx₀ PF hx
  let := D.residueLinear iΛ x₀ hx₀
  let E := D.kernelExtension iΛ x₀ hx₀ _ _ (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose
    hT.choose_spec
  have : FiniteDimensional k (E.shortComplex.X₃ ⟶ E.shortComplex.X₁) :=
    D.finiteDimensional_hom_copowerObj_basePoint iΛ x₀ hx₀ _
  have hi : ∀ a, E.shortComplex.f ≫ (D.infAction iΛ x₀ hx₀ PF hT a).asIso.hom =
      E.shortComplex.f := fun a =>
    D.f_comp_kernelAut (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose hT.choose_spec
      ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF a)
  have hq : ∀ a, (D.infAction iΛ x₀ hx₀ PF hT a).asIso.hom ≫ E.shortComplex.g =
      E.shortComplex.g := fun a =>
    D.kernelAut_comp_p (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose hT.choose_spec
      ((D.cohDef iΛ x₀ hx₀).morphisms _ _ (D.infEndo iΛ x₀ hx₀ PF a))
      (D.ringHom_infEndo iΛ x₀ hx₀ PF a)
  refine finiteDimensional_infinitesimalAutomorphismLinearLift_of_extension h𝓕.satisfiesRS PF
    E.shortExact (D.infAction iΛ x₀ hx₀ PF hT) (D.infAction_injective iΛ x₀ hx₀ PF hT) hi hq
    fun c a b hab => ?_
  exact ModuleDeformation.sub_id_eq_smul_of_comp_eq E.shortExact _ _
    (D.kernelTransfer (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose hT.choose_spec _
      (D.ringHom_scalingMorphism iΛ x₀ hx₀ PF c)) c (hi a) (hq a) (hi b) (hq b)
    (D.f_comp_kernelTransfer_scaling iΛ x₀ hx₀ PF hT c)
    (D.kernelTransfer_comp_p (D.algebra_dualPoint iΛ x₀ hx₀ PF) hT.choose hT.choose_spec _ _)
    (D.kernelAut_comp_kernelTransfer_scaling iΛ x₀ hx₀ PF hT c a b hab).symm

end Final

section Registration

variable (iΛ x₀ hx₀)

/-- **Stacks 08W8.** In Situation 08KB (`f : X ⟶ Y` of finite presentation) assume that `S` is
locally Noetherian and `Y ⟶ S` locally of finite presentation. Let `k` be a field of finite type
over `S`, with `Spec Λ ⊆ S` an affine open through which `Spec k ⟶ S` factors and `Λ → k` finite
as in Section 07T2, and let `x₀ = (Spec k, g₀, 𝒢₀)` be an object of `Coh_{X/Y}` over `Spec k`.
Then the tangent space `T𝓕` and the infinitesimal automorphisms `Inf(𝓕)` of
`𝓕 = 𝓕_{Coh_{X/Y}, k, x₀}` are finite-dimensional over `k`. The vector-space structures are those
of the deformation category `𝓕` (Stacks 07WU with Stacks 07WQ), which the conclusion records.

The conclusion spells out the two clauses of `Deformation.IsFiniteDimensionalDeformationCategory`:
that predicate asks the morphisms of `𝓕` to live in the universe of the rings of `𝒞_Λ`, while the
morphisms of `Coh_{X/Y}`, which carry morphisms of sheaves of modules, live one universe higher. -/
@[stacks 08W8]
theorem finiteDimensional_tangentSpace_and_infinitesimalAutomorphisms_cohDef
    [IsLocallyNoetherian S]
    (hlfp : IsLocallyOfFinitePresentation B S hS (terminal.from D.Y.1)) [Module.Finite Λ k]
    (hiΛ : AlgebraicGeometry.IsOpenImmersion iΛ)
    (hfinite : AlgebraicGeometry.LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      AlgebraicGeometry.QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    ∃ hp : IsDeformationCategory.{u, u, u} (D.cohDef iΛ x₀ hx₀).projection,
      (letI : Fact (IsPredeformationCategory.{u, u, u}
          (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection).p) := ⟨hp.predeformation⟩;
        letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
          (isomorphismClasses (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
            hp.predeformation.cofibered))) := ⟨tangentConditionS2.{u, u, u} hp⟩;
        FiniteDimensional k (tangentSpaceArtinian.{u, u, u} Λ k
          (isomorphismClasses (BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection)
            hp.predeformation.cofibered))) ∧
      ∀ (x : (D.cohDef iΛ x₀ hx₀).carrier),
        (D.cohDef iΛ x₀ hx₀).projection.obj x = Deformation.residueFieldObject.{u, u, u} Λ k →
        ∀ PF : ChosenPushforwardsAt (D.cohDef iΛ x₀ hx₀).projection x, FiniteDimensional k
          ↥((infinitesimalAutomorphismLinearLift.{u, u, u} PF hp.satisfiesRS).functor.obj
            (FGModuleCat.of k (ULift.{u} k))) := by
  have h𝓕 : IsDeformationCategory.{u, u, u} (D.cohDef iΛ x₀ hx₀).projection :=
    Deformation.Artin.isDeformationCategory_predeformationCategory B S hS
      (coherentSiteProjection D.categoryData)
      D.isFiberedInGroupoids_siteProjection D.satisfiesRS iΛ x₀ hx₀ hfinite.1 hfinite.2
  exact ⟨h𝓕, finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt
    (𝓕 := BasedCategory.ofFunctor (D.cohDef iΛ x₀ hx₀).projection) h𝓕
    (D.finiteDimensional_tangentModuleAt_cohDef_uLift iΛ x₀ hx₀ hlfp hiΛ hfinite h𝓕),
    fun x hx PF => D.finiteDimensional_infinitesimalAutomorphism_cohDef iΛ x₀ hx₀ PF h𝓕 hx⟩

end Registration

end CoherentSituation

end AlgebraicGeometry.Space

end
