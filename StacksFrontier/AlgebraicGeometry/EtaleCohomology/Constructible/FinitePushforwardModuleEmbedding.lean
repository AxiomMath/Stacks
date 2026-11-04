module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.PointwiseEmbeddingFamily
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.MainstreamTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.StagePointEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A constructible sheaf of modules embeds into a finite sum of finite direct images

**Stacks 09Z7, part (3).** Let `X` be a quasi-compact and quasi-separated scheme and `Λ` a
Noetherian ring. A constructible sheaf `ℱ` of `Λ`-modules on `X_étale` admits an injective map
`ℱ ⟶ ⨁_{i=1}^n f_{i,*} M̲_i` with `f_i : Y_i ⟶ X` finite and of finite presentation and `M_i`
finite `Λ`-modules.

The source reduces to the Noetherian case (Stacks 09Z6) by absolute Noetherian approximation and
Stacks 09YU. This file argues over the quasi-compact quasi-separated base directly instead, which
needs neither 09YU nor the Noetherian hypothesis anywhere:

* for each point `x` the construction of the proof of Stacks 09Z6, carried out on Mathlib's small
  étale site (`Stacks.EtaleCohomology.exists_stage_pointEmbedding`), produces a finite finitely
  presented `f : Y ⟶ X`, a finite `Λ`-module `M` and a map `ψ : f^{-1}ℱ ⟶ M̲` whose kernel
  vanishes at a geometric point of `Y` over `x`; the finite presentation of `ℱ` it needs is
  Stacks 095N, and the finiteness of the stalks Stacks 0GKC;
* those maps are transported to the small étale site of Stacks 021B, where constructibility lives,
  and finitely many of them suffice
  (`AlgebraicGeometry.exists_mono_biproduct_lift_of_forall_isZero_etaleStalk_kernel`, which uses
  compactness of the constructible topology in place of the ascending chain condition).

## Main results

* `AlgebraicGeometry.SmallEtale.sheafEquivPullbackModuleIso` — the passage between the two small
  étale sites commutes with inverse image of sheaves of modules.
* `AlgebraicGeometry.exists_pointEmbedding_of_isConstructibleModuleSheaf` — the pointwise
  embedding on the small étale site of Stacks 021B.
* `AlgebraicGeometry.exists_mono_biproduct_pushforward_constantSheaf_of_isConstructibleModuleSheaf`
  — **Stacks 09Z7 (3)**.

## References

* [Stacks Project, Tag 09Z7](https://stacks.math.columbia.edu/tag/09Z7)
* [Stacks Project, Tag 09Z6](https://stacks.math.columbia.edu/tag/09Z6)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance 3000] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- **The passage between the two small étale sites commutes with inverse image**, for sheaves of
`Λ`-modules. Both composites are left adjoint to the same functor, by
`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`. -/
public def sheafEquivPullbackModuleIso {S T : B.Scheme} (f : T ⟶ S) :
    (sheafEquiv B S.obj S.property (ModuleCat.{u + 1} Λ)).functor ⋙
        Stacks.EtaleCohomology.etaleModuleInverseImage.{u, u + 1} Λ (B.inclusion.map f) ≅
      (AlgebraicGeometry.smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
          (topology B S.obj S.property) (topology B T.obj T.property) ⋙
        (sheafEquiv B T.obj T.property (ModuleCat.{u + 1} Λ)).functor :=
  Adjunction.leftAdjointUniq
    (((sheafEquiv B S.obj S.property (ModuleCat.{u + 1} Λ)).toAdjunction.comp
      (Stacks.EtaleCohomology.etaleModuleInverseImageAdj.{u, u + 1} Λ
        (B.inclusion.map f))).ofNatIsoRight
      (toEtaleSitePushforwardBaseChangeIso B f (ModuleCat.{u + 1} Λ)))
    (((AlgebraicGeometry.smallEtaleBaseChange B f).sheafAdjunctionContinuous
      (ModuleCat.{u + 1} Λ) _ _).comp (sheafEquiv B T.obj T.property _).toAdjunction)

/-- **The passage between the two small étale sites carries constant sheaves to constant
sheaves**, for sheaves of `Λ`-modules. -/
public def sheafEquivConstantModuleIso (S : B.Scheme) (M : ModuleCat.{u + 1} Λ) :
    (sheafEquiv B S.obj S.property (ModuleCat.{u + 1} Λ)).functor.obj
        ((constantSheaf (topology B S.obj S.property) (ModuleCat.{u + 1} Λ)).obj M) ≅
      (constantSheaf S.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
  (sheafEquiv B S.obj S.property _).functor.mapIso
      (((Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
        (topology B S.obj S.property) S.obj.smallEtaleTopology (toEtaleSite B S.obj S.property)
        (ModuleCat.{u + 1} Λ)).app M).symm) ≪≫
    (sheafEquiv B S.obj S.property _).counitIso.app _

end SmallEtale

/-- The fibre at a point of a site of the constant sheaf with value `M` is `M` itself: the
neighbourhoods of a point are cofiltered, hence connected. -/
private def constantSheafPointFiberIso {C : Type*} [Category C] {J : GrothendieckTopology C}
    (p : J.Point.{u}) {A : Type*} [Category A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [HasWeakSheafify J A] (M : A) :
    p.sheafFiber.obj ((constantSheaf J A).obj M) ≅ M := by
  have : IsConnected p.fiber.Elementsᵒᵖ := IsFiltered.isConnected _
  exact (p.presheafToSheafCompSheafFiberIso A).app ((Functor.const _).obj M) ≪≫
    ((isColimitConstCocone p.fiber.Elementsᵒᵖ M).coconePointUniqueUpToIso
      (p.isColimitPresheafFiberCocone ((Functor.const _).obj M))).symm

section Presentation

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- The transport to Mathlib's small étale site of the extension by zero `j_{U!} Λ` of the
constant sheaf at an object `U` of the small étale site of Stacks 021B is the extension by zero of
`Λ` along the structure morphism of `U`
(`AlgebraicGeometry.SmallEtale.sheafEquivExtensionByZeroIso`). -/
def moduleShriekConstantTransportIso (X : B.Scheme) (U : SmallEtale B X.obj X.property) :
    Stacks.EtaleCohomology.extensionByZeroConstant Λ (B.inclusion.map U.obj.hom) ≅
      (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj
        (moduleShriekConstant.{u, u + 1, u + 1} B X Λ U) := by
  let A := ModuleCat.{u + 1} Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X Λ
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U.obj.left Λ
  let eW := SmallEtale.sheafEquiv B U.obj.left.1 U.obj.left.property A
  let T := SmallEtale.sheafEquivExtensionByZeroIso B X.obj X.property U A
    (Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj.{u, u + 1} Λ
      (B.inclusion.map U.obj.hom))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtalePostcompose B X.obj X.property U) A
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X.obj X.property))
  let r := (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    U.obj.left.1.smallEtaleTopology
    (SmallEtale.toEtaleSite B U.obj.left.1 U.obj.left.property) A).app
      (ModuleCat.of Λ Λ)
  let d : eW.functor.obj ((constantSheaf (SmallEtale.topology B U.obj.left.1
        U.obj.left.property) A).obj (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≅
      (constantSheaf U.obj.left.1.smallEtaleTopology A).obj (ModuleCat.of Λ Λ) :=
    eW.functor.mapIso ((constantSheaf _ A).mapIso
        (ULift.moduleEquiv : ULift.{u + 1} Λ ≃ₗ[Λ] Λ).toModuleIso ≪≫ r.symm) ≪≫
      eW.counitIso.app _
  exact (Stacks.EtaleCohomology.etaleModuleExtensionByZero.{u, u + 1} Λ _).mapIso d.symm ≪≫
    T.app _

/-- **Stacks 095N, read on Mathlib's site.** For a constructible sheaf `𝒢` of `Λ`-modules on the
small étale site of Stacks 021B of a quasi-compact quasi-separated `X`, the transport of `𝒢` to
Mathlib's small étale site is the cokernel of a map between finite direct sums of extensions by
zero of `Λ` along étale morphisms with affine source: there are an epimorphism `p` from such a sum
onto the transport of `𝒢` and an epimorphism `q` from such a sum onto `kernel p`. -/
theorem exists_presentation_sheafEquiv (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleModuleSheaf B X Λ G) :
    ∃ (n : ℕ) (W : Fin n → Scheme.{u}) (e : ∀ i, W i ⟶ X.obj) (_ : ∀ i, Etale (e i))
      (_ : ∀ i, IsAffine (W i))
      (p : (∐ fun i => Stacks.EtaleCohomology.extensionByZeroConstant Λ (e i)) ⟶
        (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj G)
      (_ : Epi p) (m : ℕ) (W' : Fin m → Scheme.{u}) (e' : ∀ l, W' l ⟶ X.obj)
      (_ : ∀ l, Etale (e' l)) (_ : ∀ l, IsAffine (W' l))
      (q : (∐ fun l => Stacks.EtaleCohomology.extensionByZeroConstant Λ (e' l)) ⟶ kernel p),
      Epi q := by
  let eX := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)
  have : eX.functor.IsLeftAdjoint := eX.toAdjunction.isLeftAdjoint
  have hE : ∀ {E F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
      (g : E ⟶ F), Epi g → Epi (eX.functor.map g) := fun g _ =>
    (Functor.preservesEpimorphisms_of_isLeftAdjoint eX.functor).preserves g
  obtain ⟨n, V, hV, f, hf⟩ :=
    exists_finite_epi_sigma_moduleShriekConstant_affine_of_isConstructibleModuleSheaf B X Λ G hG
  let P : ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{u + 1} Λ)) := fun H => IsConstructibleModuleSheaf B X Λ H
  let _ : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B _ Λ
  have hK : P (kernel f) :=
    P.prop_kernel f (isConstructibleModuleSheaf_sigma_moduleShriekConstant B X Λ V hV) hG
  obtain ⟨m, V', hV', g, hg⟩ :=
    exists_finite_epi_sigma_moduleShriekConstant_affine_of_isConstructibleModuleSheaf B X Λ _ hK
  let cs := Sigma.mapIso (fun i => moduleShriekConstantTransportIso B Λ X (V i)) ≪≫
    (PreservesCoproduct.iso eX.functor _).symm
  let cs' := Sigma.mapIso (fun i => moduleShriekConstantTransportIso B Λ X (V' i)) ≪≫
    (PreservesCoproduct.iso eX.functor _).symm
  let p := cs.hom ≫ eX.functor.map f
  let k : eX.functor.obj (kernel f) ≅ kernel p :=
    PreservesKernel.iso eX.functor f ≪≫ (kernelIsIsoComp cs.hom (eX.functor.map f)).symm
  exact ⟨n, fun i ↦ (V i).obj.left.1, fun i ↦ B.inclusion.map (V i).obj.hom,
    fun i ↦ (V i).property, fun i ↦ hV i, p, epi_comp' inferInstance (hE f hf),
    m, fun i ↦ (V' i).obj.left.1, fun i ↦ B.inclusion.map (V' i).obj.hom,
    fun i ↦ (V' i).property, fun i ↦ hV' i, cs'.hom ≫ eX.functor.map g ≫ k.hom,
    epi_comp' inferInstance (epi_comp' (hE g hg) inferInstance)⟩

end Presentation

section Embedding

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

/-- A monomorphism into a sheaf of `Λ`-modules on Mathlib's small étale site whose stalk at a
point vanishes has a source with vanishing stalk there: the fibre functor of a point is left
exact. -/
theorem isZero_sheafFiber_of_mono_module {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
    {K L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (m : K ⟶ L) [Mono m]
    (hL : IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj L)) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj K) := by
  have hfil : HasFilteredColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have hab : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have hm : Mono ((Scheme.pointSmallEtale s).sheafFiber.map m) := Functor.map_mono _ _
  exact (IsZero.iff_id_eq_zero _).2
    ((cancel_mono ((Scheme.pointSmallEtale s).sheafFiber.map m)).1 (hL.eq_of_tgt _ _))

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- **The inverse images of a constructible sheaf to spectra of separably closed fields have
finite global sections.** Over a separably closed field `Ω` such an inverse image is constant on
its global sections, which are therefore its stalk at an algebraic closure of `Ω`; that is the
stalk of the sheaf at a geometric point of `X`, finite by Stacks 0GKC
(`AlgebraicGeometry.isFG_etaleStalk_of_isConstructibleModuleSheaf`). -/
theorem module_finite_globalSections_inverseImage_sheafEquiv (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X.obj) :
    Module.Finite Λ ((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, u + 1} Λ
      (Spec (.of Ω))).obj ((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, u + 1} Λ s).obj
        ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F))) := by
  let G := (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, u + 1} Λ s).obj
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F)
  let M := (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj G
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have := Stacks.EtaleCohomology.isEquivalence_globalSections_of_isSepClosed Ω
    (ModuleCat.{u + 1} Λ)
  let α : (constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M ≅ G :=
    asIso ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)
  let Ωb := AlgebraicClosure Ω
  let a : Spec (.of Ωb) ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom (algebraMap Ω Ωb))
  let t : GeometricPoint X.obj := ⟨Ωb, a ≫ s⟩
  have : HasProducts.{u} (ModuleCat.{u + 1} Λ) := fun _ => ModuleCat.hasLimitsOfShape
  let e₁ : (Scheme.pointSmallEtale a).sheafFiber.obj G ≅ M :=
    (Scheme.pointSmallEtale a).sheafFiber.mapIso α.symm ≪≫ constantSheafPointFiberIso _ M
  let e₂ : (Scheme.pointSmallEtale a).sheafFiber.obj G ≅
      (etaleModuleStalkFunctor.{u, u + 1, u + 1} B X Λ t).obj F :=
    (Stacks.EtaleCohomology.etaleModuleStalkPullbackIso.{u, u + 1} Λ s a).app _ ≪≫
      (sheafEquivCompSheafFiberIso.{u, u + 1, u + 1} B X Λ t).app F
  have : Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, u + 1} B X Λ t).obj F) :=
    isFG_etaleStalk_of_isConstructibleModuleSheaf.{u, u + 1} B Λ X F hF t
  exact Module.Finite.equiv (e₂.symm ≪≫ e₁).toLinearEquiv

/-- **The pointwise embedding of a constructible sheaf of modules**, on the small étale site of
Stacks 021B. For a constructible sheaf `ℱ` of `Λ`-modules on a quasi-compact quasi-separated `X`
and a point `x ∈ X` there are a finite morphism of finite presentation `f : Y ⟶ X`, a finite
`Λ`-module `M`, a map `ψ : f^{-1}ℱ ⟶ M̲` and a geometric point of `Y` over `x` at which the
kernel of `ψ` has vanishing stalk. -/
theorem exists_pointEmbedding_of_isConstructibleModuleSheaf (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) (x : X.obj) :
    ∃ (Y : B.Scheme) (f : Y ⟶ X) (_ : IsFinite (B.inclusion.map f))
      (_ : FinitePresentation (B.inclusion.map f)) (M : ModuleCat.{u + 1} Λ)
      (_ : Module.Finite Λ M)
      (ψ : ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property)).obj F ⟶
        (constantSheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{u + 1} Λ)).obj M)
      (t : GeometricPoint Y.obj), (B.inclusion.map f) (t.hom default) = x ∧
        IsZero (etaleStalk B Y.obj Y.property t (kernel ψ).obj) := by
  let eX := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)
  obtain ⟨n, W, e, he, hW, p, hp, m, W', e', he', hW', q, hq⟩ :=
    exists_presentation_sheafEquiv B Λ X F hF
  obtain ⟨Y, f, hf, hfp, M, hM, ψ, Ω, _, _, t, ht, hz⟩ :=
    Stacks.EtaleCohomology.exists_stage_pointEmbedding Λ (eX.functor.obj F) e p e' q
      (module_finite_globalSections_inverseImage_sheafEquiv B Λ X F hF) x
  have : LocallyOfFinitePresentation f := hfp.1
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f X.property
  let YB : B.Scheme := B.obj Y hY
  let fB : YB ⟶ X := ObjectProperty.homMk f
  let eY := SmallEtale.sheafEquiv B Y hY (ModuleCat.{u + 1} Λ)
  let Pb := (SmallEtale.sheafEquivPullbackModuleIso B Λ fB).app F
  let γ := SmallEtale.sheafEquivConstantModuleIso B Λ YB M ≪≫
    smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, u + 1} Λ Y M
  let ψB := eY.fullyFaithfulFunctor.preimage (Pb.inv ≫ ψ ≫ γ.inv)
  have hψB : eY.functor.map ψB = Pb.inv ≫ ψ ≫ γ.inv := eY.fullyFaithfulFunctor.map_preimage _
  let Ωb := AlgebraicClosure Ω
  let a : Spec (.of Ωb) ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom (algebraMap Ω Ωb))
  let tb : GeometricPoint YB.obj := ⟨Ωb, a ≫ t⟩
  refine ⟨YB, fB, hf, hfp, M, hM, ψB, tb, ht _, ?_⟩
  have hcomp : (eY.functor.map (kernel.ι ψB) ≫ Pb.inv) ≫ ψ = 0 := by
    have : ψ = Pb.hom ≫ eY.functor.map ψB ≫ γ.hom := by simp [hψB]
    rw [this, Category.assoc, Pb.inv_hom_id_assoc, ← Category.assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, zero_comp]
  have : Mono (eY.functor.map (kernel.ι ψB)) := Functor.map_mono _ _
  have hmono : Mono (kernel.lift ψ _ hcomp) := mono_of_mono_fac (kernel.lift_ι _ _ _)
  have hzK : IsZero ((Scheme.pointSmallEtale tb.hom).sheafFiber.obj (kernel ψ)) :=
    IsZero.of_iso (Functor.map_isZero (Scheme.pointSmallEtale a).sheafFiber hz)
      ((Stacks.EtaleCohomology.etaleModuleStalkPullbackIso.{u, u + 1} Λ t a).app (kernel ψ)).symm
  exact IsZero.of_iso (isZero_sheafFiber_of_mono_module tb.hom Λ (kernel.lift ψ _ hcomp) hzK)
    ((sheafEquivCompSheafFiberIso.{u, u + 1, u + 1} B YB Λ tb).app (kernel ψB)).symm

/-- **Stacks 09Z7, part (3).** Let `X` be a quasi-compact and quasi-separated scheme and `Λ` a
Noetherian ring. For every constructible sheaf `ℱ` of `Λ`-modules on `X_étale` there are finitely
many finite morphisms of finite presentation `f_i : Y_i ⟶ X`, finite `Λ`-modules `M_i`, and an
injective map of sheaves of modules `ℱ ⟶ ⨁_i f_{i,*} M̲_i`.

Here `X` is a scheme of a big étale site `B` and the sheaves live on the small étale site of
Stacks 021B cut out of `B`, where the library's constructibility (Stacks 03RW) is defined. -/
@[sga "4 IX 2.14" "(ii), special case"]
theorem exists_mono_biproduct_pushforward_constantSheaf_of_isConstructibleModuleSheaf
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    ∃ (n : ℕ) (Y : Fin n → B.Scheme) (f : ∀ k, Y k ⟶ X)
      (_ : ∀ k, IsFinite (B.inclusion.map (f k)))
      (_ : ∀ k, FinitePresentation (B.inclusion.map (f k)))
      (M : Fin n → ModuleCat.{u + 1} Λ) (_ : ∀ k, Module.Finite Λ (M k))
      (φ : F ⟶ ⨁ fun k => ((smallEtaleBaseChange B (f k)).sheafPushforwardContinuous
        (ModuleCat.{u + 1} Λ) (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (Y k).obj (Y k).property)).obj
          ((constantSheaf (SmallEtale.topology B (Y k).obj (Y k).property)
            (ModuleCat.{u + 1} Λ)).obj (M k))), Mono φ := by
  choose Y f hf hfp M hM ψ t ht hz using
    exists_pointEmbedding_of_isConstructibleModuleSheaf B Λ X F hF
  have : ∀ x, LocallyOfFinitePresentation (B.inclusion.map (f x)) := fun x => (hfp x).1
  have hG : ∀ x, IsConstructibleModuleSheaf B (Y x) Λ
      ((constantSheaf (SmallEtale.topology B (Y x).obj (Y x).property)
        (ModuleCat.{u + 1} Λ)).obj (M x)) := fun x =>
    isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B (Y x) Λ _
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_constant.{u, u + 1, u + 1}
        _ Λ (hM x) (Iso.refl _))
  obtain ⟨n, p, hmono⟩ := exists_mono_biproduct_lift_of_forall_isZero_etaleStalk_kernel B Λ X
    F hF Y f _ hG ψ (fun x => ⟨t x, ht x, hz x⟩)
  exact ⟨n, fun k => Y (p k), fun k => f (p k), fun k => hf (p k), fun k => hfp (p k),
    fun k => M (p k), fun k => hM (p k), _, hmono⟩

end Embedding

end AlgebraicGeometry

end
