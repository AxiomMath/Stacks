module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.AffineLineNagata
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence

/-!
# Local constancy is étale local, and constructible sheaves on finite schemes over a field

Two facts on étale-locally constant sheaves of `Λ`-modules
(`Stacks.ConstantSheaf.IsLocallyConstantWith`):

* local constancy is étale local on the base: if `{oᵢ : Oᵢ ⟶ X}` is a jointly surjective family
  of étale morphisms and every `oᵢ⁻¹ F` is locally constant with values in `Q`, then so is `F`;
* a constructible sheaf on a reduced scheme `Z` finite over a field is locally constant of finite
  type: `Z` is a finite discrete space, so every point of `Z` is a generic point, near which a
  constructible sheaf is locally constant of finite type.

The second is used for the closed complement `Z` of the open where a punctual sheaf `P` on
`𝔸¹_k` vanishes: `P = i_* i⁻¹ P` with `i⁻¹ P` locally constant of finite type on `Z`, which makes
`H⁰(Φ(P[0]))` locally constant (the lisse half of the step (L5) of the single-level argument for
the irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.isLocallyConstantWith_of_etale_cover`.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule_of_isFinite`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **Local constancy is étale local**: if `{oᵢ : Oᵢ ⟶ X}` is a jointly surjective family of
étale morphisms and each `oᵢ⁻¹ F` is locally constant with values in `Q`, then `F` is locally
constant with values in `Q`. -/
theorem isLocallyConstantWith_of_etale_cover (Q : ModuleCat.{u + 1} Λ → Prop) {X : Scheme.{u}}
    {ι : Type u} {O : ι → Scheme.{u}} (o : ∀ i, O i ⟶ X) [∀ i, Etale (o i)]
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (o i).base) (F : EtaleModules.{u, 0} Λ X)
    (hF : ∀ i, Stacks.ConstantSheaf.IsLocallyConstantWith Λ (O i).smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ (o i)).obj F)) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q F := by
  intro V
  have : Etale V.hom := V.prop
  let U : ∀ i, (O i).Etale := fun i => Scheme.Etale.mk (pullback.snd V.hom (o i))
  choose I W g hcovW htriv using fun i => hF i (U i)
  have : ∀ i p, Etale (W i p).hom := fun i p => (W i p).prop
  let fst : ∀ i, (U i).left ⟶ V.left := fun i => pullback.fst V.hom (o i)
  have hfst : ∀ i, fst i ≫ V.hom = (U i).hom ≫ o i := fun i => pullback.condition
  have hw : ∀ i p, ((g i p).left ≫ fst i) ≫ V.hom = (W i p).hom ≫ o i := fun i p => by
    rw [Category.assoc, hfst, ← Category.assoc, MorphismProperty.Over.w (g i p)]
  refine ⟨Σ i, I i, fun p => Scheme.Etale.mk ((W p.1 p.2).hom ≫ o p.1),
    fun p => MorphismProperty.Over.homMk ((g p.1 p.2).left ≫ fst p.1) (hw p.1 p.2), ?_,
    fun p => ?_⟩
  · refine (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 (Set.eq_univ_of_forall fun v => ?_)
    obtain ⟨i, y, hy⟩ := hcov (V.hom v)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback v y hy.symm
    obtain ⟨p, w, hw'⟩ := Set.mem_iUnion.1
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff _).1 (hcovW i) ▸ Set.mem_univ z)
    refine Set.mem_iUnion.2 ⟨⟨i, p⟩, w, ?_⟩
    show ((g i p).left ≫ fst i) w = v
    rwa [Scheme.Hom.comp_apply, hw']
  · obtain ⟨i, p⟩ := p
    obtain ⟨E, hE, ⟨e⟩⟩ := htriv i p
    exact ⟨E, hE, ⟨overPullbackIsoConstantOfEtaleModuleInverseImage Λ _ F E
      ((etaleModuleInverseImageCompIso.{u, 0} Λ (W i p).hom (o i)).app F ≪≫
        etaleModuleInverseImageIsoConstantOfOverPullback (W i p) Λ _ E e)⟩⟩

variable [Finite Λ]

/-- **A constructible sheaf on a reduced scheme finite over a field is locally constant of finite
type**: the scheme is a finite discrete space, every point is a generic point, and near a generic
point a constructible sheaf is locally constant of finite type. -/
theorem isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule_of_isFinite {K : Type u}
    [Field K] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [IsFinite f] [IsReduced Z]
    {F : EtaleModules.{u, 0} Λ Z} (hF : IsConstructibleEtaleModule Λ F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Z.smallEtaleTopology F := by
  have : IsNoetherianRing Λ := inferInstance
  have : DiscreteTopology Z := (finite_discreteTopology_of_isFinite f).2
  let B := BigEtaleSite.containing Z
  have hZB : B.Contains Z := BigEtaleSite.contains_containing _
  have hc : IsBigSiteConstructibleEtaleModule B (B.obj _ hZB) Λ F :=
    (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hZB _).1 hF
  have : IsReduced (B.obj _ hZB).obj := inferInstanceAs (IsReduced Z)
  have hgen : ∀ z : Z, z ∈ genericPoints Z := fun z => by
    have h := genericPoints.closure (α := Z)
    rw [closure_discrete] at h
    exact h ▸ Set.mem_univ z
  choose O o ho hz hFO using fun z : Z =>
    exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule B
      (B.obj _ hZB) F hc (hgen z)
  have : ∀ z, IsOpenImmersion (B.inclusion.map (o z)) := ho
  exact isLocallyConstantWith_of_etale_cover Λ (ModuleCat.isFG Λ)
    (fun z => B.inclusion.map (o z)) (fun z => ⟨z, hz z⟩) F hFO

end Stacks.EtaleCohomology

end
