module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.DepthTwoReflexiveExtension.Restrict
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Vanishing
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureCoherence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.PointClosureComparisonMorphism
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictLocality
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSupport

/-!
# Coherence of a direct image from coherence at the closures of the associated points

Let `X` be a locally Noetherian scheme, `j : U ⟶ X` the inclusion of an open subscheme and `F` a
coherent `𝒪_U`-module. For `x ∈ U` write `i_x : W_x → U` for the integral closed subscheme with
generic point `x`. This file proves the implication (1) ⇒ (2) of [Stacks, Tag 0BJZ]: coherence of
`j_* i_{x,*} 𝒪_{W_x}` at every associated point of `F` gives coherence of `j_* F`.

The source's induction needs `U` Noetherian and quasi-affine, and the source's reduction to an
affine base supplies both. That reduction is carried out here, as
`isCoherent_pushforward_of_forall_affineOpens`: coherence of a direct image is local on the
target, because direct image commutes with restriction to an open of the target — the
natural isomorphism `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`.

## Main results

* `isCoherent_pushforward_of_forall_affineOpens` of the namespace below: coherence of a direct
  image is local on the target.
* `Stacks.AlgebraicGeometry.CoherenceFromPointClosures.exists_minimal_mem_supp`: a nonzero
  coherent module on a Noetherian scheme has a point of its support minimal under
  specialization, and its stalk there has finite length. This is the point the source's double
  induction is run at.
* `Stacks.AlgebraicGeometry.CoherenceFromPointClosures.exists_hom_surjective_stalkLinearMap`: the
  morphism `F ⟶ i_{x,*} 𝒪_{W_x}` of the source's first paragraph, surjective on the stalk at `x`.
* `isCoherent_pushforward_of_forall_isAssociatedPoint` of the namespace below:
  **[Stacks, Tag 0BJZ], the implication (1) ⇒ (2)**, for `U` Noetherian and quasi-affine.
* `isCoherent_pushforward_of_forall_isAssociatedPoint'` of the namespace below: the same
  implication for an arbitrary open subscheme of a locally Noetherian scheme.

## Implementation notes

The source runs a double induction, on the number of associated points of `F` and, at a chosen
generic point `x` of an irreducible component of `Supp(F)`, on the length of `F_x`. Both measures
appear in `isCoherent_pushforward_aux`, whose membership hypothesis is stated as the existence of
a point of `Supp(F)` minimal under specialization with a bound on the length of the stalk there
— the existential form is what survives the inductive step, since only the chosen point has its
length drop.

The induction is run over an abstract family `x ↦ G x` of `𝒪_U`-modules, constrained only by the
three properties of `i_{x,*} 𝒪_{W_x}` it uses: coherence, simplicity of the stalk at `x`, and
coherence of the direct image. On the affine pieces of the reduction the family is instantiated
at `(i_{x,*} 𝒪_{W_x})|_{j^{-1}V}` rather than at the point-closure sheaf of the open subscheme,
so the point-closure subschemes of `U` and of `j^{-1}V` never have to be identified; the two
facts that cross the restriction are instead simplicity of a stalk
(`isSimpleModule_stalk_restrict`) and membership in the associated points
(`Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff`).

The comparison morphism goes `F ⟶ i_{x,*} 𝒪_{W_x}`, the direction opposite to the one of
`Stacks.AlgebraicGeometry.PointClosureComparison.exists_mono_of_isAssociatedPoint`, and it is
asked only to be surjective on the stalk at `x` rather than injective. A nonzero stalk suffices:
`𝒪_{U,x} ⧸ 𝔪_x` is a simple module, so any nonzero map onto it is surjective, and Nakayama
produces one out of the nonzero finite module `F_x`. [Stacks, Tag 01YB] enters through
`Stacks.AlgebraicGeometry.PrincipalIdealExtension.exists_hom_app_eq_overApp_smul_pow_basicOpen`,
whose coherent argument is here `F` itself and whose quasi-coherent argument is
`i_{x,*} 𝒪_{W_x}`; the general form of 01YB, which is false, is not needed.

The length bookkeeping uses the canonical short exact sequence
`0 → ker φ → F → coimage φ → 0` and the exactness of the stalk functor through
`Stacks.SheafOfModules.FlatShortExact.stalkShortExact`, which is stated over `𝒪_{U,x}` rather
than over the stalk of the structure sheaf read in `RingCat`. The coimage has the same stalk at
`x` as `i_{x,*} 𝒪_{W_x}`, because the mono out of the coimage is surjective on that stalk.

## References

* [Stacks Project, Tag 0BJZ](https://stacks.math.columbia.edu/tag/0BJZ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01Y4](https://stacks.math.columbia.edu/tag/01Y4)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 05AE](https://stacks.math.columbia.edu/tag/05AE)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
* [Stacks Project, Tag 05AG](https://stacks.math.columbia.edu/tag/05AG)
* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherenceFromPointClosures

/-! ### The affine reduction -/

/-- Restriction of a direct image to an open of the target is coherent iff the direct image of the
restriction over that open is. -/
private theorem isCoherent_restrict_pushforward_iff {Y S : Scheme.{u}} (f : Y ⟶ S)
    (V : S.Opens) (M : Y.Modules) :
    (((Scheme.Modules.pushforward f).obj M).restrict V.ι).IsCoherent ↔
      ((Scheme.Modules.pushforward (f ∣_ V)).obj (M.restrict (f ⁻¹ᵁ V).ι)).IsCoherent :=
  have e : (((Scheme.Modules.pushforward f).obj M).restrict V.ι) ≅
      (Scheme.Modules.pushforward (f ∣_ V)).obj (M.restrict (f ⁻¹ᵁ V).ι) :=
    (AffinePushforward.restrictPushforwardIso f V).app M
  ⟨fun _ => CoherentDevissage.isCoherent_of_iso e.symm,
    fun _ => CoherentDevissage.isCoherent_of_iso e⟩

/-- **Coherence of a direct image is local on the target.** This is the source's "the statement
is local on `X`, hence we may assume `X` is affine" of [Stacks, Tag 0BJZ]. -/
theorem isCoherent_pushforward_of_forall_affineOpens {Y S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : Y ⟶ S) (M : Y.Modules)
    (h : ∀ V : S.affineOpens, ((Scheme.Modules.pushforward (f ∣_ (V : S.Opens))).obj
      (M.restrict (f ⁻¹ᵁ (V : S.Opens)).ι)).IsCoherent) :
    ((Scheme.Modules.pushforward f).obj M).IsCoherent := by
  have key : ∀ V : S.affineOpens,
      (((Scheme.Modules.pushforward f).obj M).restrict (V : S.Opens).ι).IsCoherent := fun V =>
    (isCoherent_restrict_pushforward_iff f (V : S.Opens) M).mpr (h V)
  have hqc : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    isQuasicoherent_of_iSup_eq_top _ (fun V : S.affineOpens => (V : S.Opens))
      (iSup_affineOpens_eq_top S)
      fun V => have := key V
        (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hft : ((Scheme.Modules.pushforward f).obj M).IsFiniteType :=
    isFiniteType_of_iSup_eq_top _ (fun V : S.affineOpens => (V : S.Opens))
      (iSup_affineOpens_eq_top S)
      fun V => have := key V
        (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).2
  exact CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### The comparison morphism -/

open PointClosureComparison in
/-- `G_x = κ(x)` is a simple module over the local ring, so it has length one. -/
theorem length_stalk_pointClosureStructureSheaf {U : Scheme.{u}} (x : U) :
    Module.length (U.presheaf.stalk x)
      ((pointClosureStructureSheaf x).presheaf.stalk x) = 1 :=
  have := isSimpleModule_stalk_pointClosureStructureSheaf x
  Module.length_eq_one _ _

/-- **Simplicity of a stalk passes to an open subscheme.** The stalk at `y` of the restriction
of `F` to an open `V` is the stalk of `F` at `y`, semilinearly over the identification of the two
local rings, so one is a simple module as soon as the other is. -/
theorem isSimpleModule_stalk_restrict {X : Scheme.{u}} (V : X.Opens) (F : X.Modules)
    (y : V.toScheme) (h : IsSimpleModule (X.presheaf.stalk y.1) (F.presheaf.stalk y.1)) :
    IsSimpleModule (V.toScheme.presheaf.stalk y) ((F.restrict V.ι).presheaf.stalk y) := by
  have := RingHomInvPair.of_ringEquiv (V.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv_symm (V.stalkIso y).commRingCatIsoToRingEquiv
  exact ((DepthTwoReflexiveExtension.restrictStalkSemilinearEquiv V F
      y).toLinearMap.isSimpleModule_iff_of_bijective
    (DepthTwoReflexiveExtension.restrictStalkSemilinearEquiv V F y).bijective).mpr h

/-- **At a point of its support the stalk of a coherent module surjects onto a simple stalk.** A
simple module over the local ring `𝒪_{U,x}` is its residue field, and Nakayama produces a
surjection onto the residue field out of the nonzero finite module `F_x`. -/
theorem exists_surjective_stalk_of_isSimpleModule {U : Scheme.{u}} (F : U.Modules)
    [F.IsCoherent] (G : U.Modules) (x : U)
    (hG : IsSimpleModule (U.presheaf.stalk x) (G.presheaf.stalk x))
    (hx : x ∈ _root_.SheafOfModules.supp F) :
    ∃ ψ : F.presheaf.stalk x →ₗ[U.presheaf.stalk x] G.presheaf.stalk x,
      Function.Surjective ψ := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hG
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  have hnt : Nontrivial (F.presheaf.stalk x) :=
    (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp hx
  have hft : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := F)
  have hfin : Module.Finite (U.presheaf.stalk x) (F.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk U.sheaf F x
  obtain ⟨χ, hχ⟩ := Stacks.Support.exists_surjective_toResidueField
    (R := U.presheaf.stalk x) (M := F.presheaf.stalk x)
  exact ⟨e.symm.toLinearMap ∘ₗ χ, e.symm.surjective.comp hχ⟩

open PointClosureComparison in
/-- At a point of the support of a coherent module `F` the stalk `F_x` surjects onto
`G_x = κ(x)`. -/
theorem exists_surjective_stalk_toPointClosure {U : Scheme.{u}} (F : U.Modules)
    [F.IsCoherent] (x : U) (hx : x ∈ _root_.SheafOfModules.supp F) :
    ∃ ψ : F.presheaf.stalk x →ₗ[U.presheaf.stalk x]
        (pointClosureStructureSheaf x).presheaf.stalk x, Function.Surjective ψ :=
  exists_surjective_stalk_of_isSimpleModule F _ x
    (isSimpleModule_stalk_pointClosureStructureSheaf x) hx

open PointClosureComparison
  PrincipalIdealExtension
  IdealPowerColimit Opposite in
/-- **The morphism of the first paragraph of [Stacks, Tag 0BJZ]**, for any quasi-coherent target
with simple stalk at `x`: there is a morphism `F ⟶ G` surjective on the stalk at `x`. -/
theorem exists_hom_surjective_stalkLinearMap_of_isSimpleModule {U : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian U] [U.IsQuasiAffine] (F : U.Modules) [F.IsCoherent]
    (G : U.Modules) [G.IsQuasicoherent] (x : U)
    (hG : IsSimpleModule (U.presheaf.stalk x) (G.presheaf.stalk x))
    (hx : x ∈ _root_.SheafOfModules.supp F) :
    ∃ φ : F ⟶ G, Function.Surjective (AlgebraicGeometry.stalkLinearMap F G φ x) := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_stalk_of_isSimpleModule F G x hG hx
  have hfp : F.IsFinitePresentation :=
    CoherentTFAE.isFinitePresentation_of_isCoherent' F
  obtain ⟨V, hxV, θ, hθ⟩ := Stacks.SheafOfModules.SheafHomStalk.exists_localHom_of_stalkLinearMap
    U.toTopCat U.sheaf F G x ψ
  obtain ⟨_, ⟨f, _, rfl⟩, hxf, hfV⟩ := Opens.isBasis_iff_nbhd.mp
    (Scheme.IsQuasiAffine.isBasis_basicOpen U) hxV
  obtain ⟨k, φ, hφ⟩ := exists_hom_app_eq_overApp_smul_pow_basicOpen f F G (overRestrict hfV θ)
  have hu : IsUnit (U.presheaf.germ ⊤ x trivial f) := (U.mem_basicOpen_top f x).mp hxf
  have key : ∀ m : F.presheaf.stalk x,
      AlgebraicGeometry.stalkLinearMap F G φ x m =
        ψ (U.presheaf.germ ⊤ x trivial f ^ k • m) := by
    intro m
    obtain ⟨W, hxW, g, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) F.val.presheaf m
    have hxW' : x ∈ W ⊓ U.basicOpen f := ⟨hxW, hxf⟩
    have hWB : W ⊓ U.basicOpen f ≤ U.basicOpen f := inf_le_right
    have step1 : TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf (W ⊓ U.basicOpen f) x hxW'
          (F.val.presheaf.map (homOfLE (inf_le_left : W ⊓ U.basicOpen f ≤ W)).op g)
        = TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf W x hxW g :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    have hgerm : U.presheaf.germ (W ⊓ U.basicOpen f) x hxW'
        (restrictTop f (W ⊓ U.basicOpen f)) = U.presheaf.germ ⊤ x trivial f := by
      rw [restrictTop, TopCat.Presheaf.germ_res_apply]
    rw [← step1]
    refine Eq.trans (AlgebraicGeometry.stalkLinearMap_germ F G φ
      (W ⊓ U.basicOpen f) x hxW' _) ?_
    refine Eq.trans (congrArg (fun s : Γ(G, W ⊓ U.basicOpen f) =>
      TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf
        (W ⊓ U.basicOpen f) x hxW' s)
      ((hφ hWB _).trans (overApp_overRestrict hfV θ hWB _))) ?_
    refine Eq.trans (hθ (W ⊓ U.basicOpen f) (hWB.trans hfV) hxW' _) ?_
    refine congrArg ψ (Eq.trans (Stacks.ModuleStalkSpecialization.germ_smul F hxW'
      (restrictTop f (W ⊓ U.basicOpen f) ^ k) _) ?_)
    rw [map_pow, hgerm]
    rfl
  refine ⟨φ, fun t => ?_⟩
  obtain ⟨s, hs⟩ := hψ t
  obtain ⟨v, hv⟩ := hu.pow k
  refine ⟨(↑v⁻¹ : U.presheaf.stalk x) • s, ?_⟩
  rw [key, smul_smul, ← hv, Units.mul_inv, one_smul, hs]

open PointClosureComparison in
/-- **The morphism of the first paragraph of [Stacks, Tag 0BJZ].** -/
theorem exists_hom_surjective_stalkLinearMap {U : Scheme.{u}} [AlgebraicGeometry.IsNoetherian U]
    [U.IsQuasiAffine] (F : U.Modules) [F.IsCoherent] (x : U)
    (hx : x ∈ _root_.SheafOfModules.supp F) :
    ∃ φ : F ⟶ pointClosureStructureSheaf x, Function.Surjective
      (AlgebraicGeometry.stalkLinearMap F (pointClosureStructureSheaf x) φ x) :=
  have := isQuasicoherent_pointClosureStructureSheaf x
  exists_hom_surjective_stalkLinearMap_of_isSimpleModule F _ x
    (isSimpleModule_stalk_pointClosureStructureSheaf x) hx

open CategoryTheory.Limits in
/-- **Length is additive along the canonical short exact sequence of stalks.** -/
theorem length_stalk_eq_add {U : Scheme.{u}} {F G : U.Modules} (φ : F ⟶ G) (x : U) :
    Module.length (U.presheaf.stalk x) (F.presheaf.stalk x) =
      Module.length (U.presheaf.stalk x) ((kernel φ).presheaf.stalk x)
        + Module.length (U.presheaf.stalk x) ((Abelian.coimage φ).presheaf.stalk x) := by
  let S : ShortComplex U.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι φ) }
  obtain ⟨f, g, hf, hfg, hg⟩ := Stacks.SheafOfModules.FlatShortExact.stalkShortExact S hS x
  exact Module.length_eq_add_of_exact f g hf hg hfg

open CategoryTheory.Limits in
/-- Where the stalk map of `φ` is surjective, the stalk of its coimage is its target stalk. -/
theorem length_stalk_coimage {U : Scheme.{u}} {F G : U.Modules} (φ : F ⟶ G) (x : U)
    (hφ : Function.Surjective (AlgebraicGeometry.stalkLinearMap F G φ x)) :
    Module.length (U.presheaf.stalk x) ((Abelian.coimage φ).presheaf.stalk x) =
      Module.length (U.presheaf.stalk x) (G.presheaf.stalk x) := by
  have hinj := Scheme.Modules.injective_stalkLinearMap_of_mono (Abelian.factorThruCoimage φ)
    inferInstance x
  have hsurj : Function.Surjective (AlgebraicGeometry.stalkLinearMap (Abelian.coimage φ) G
      (Abelian.factorThruCoimage φ) x) := by
    intro t
    obtain ⟨z, hz⟩ := hφ t
    refine ⟨AlgebraicGeometry.stalkLinearMap F (Abelian.coimage φ)
      (cokernel.π (kernel.ι φ)) x z, ?_⟩
    refine Eq.trans ?_ hz
    refine Eq.trans (Scheme.Modules.stalkLinearMap_comp (cokernel.π (kernel.ι φ))
      (Abelian.factorThruCoimage φ) x z).symm ?_
    exact congrArg (fun k : F ⟶ G => AlgebraicGeometry.stalkLinearMap F G k x z)
      (Abelian.coimage.fac φ)
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).length_eq

/-- **A nonzero coherent module on a Noetherian scheme has a minimal point of its support, and
its stalk there has finite length.** The minimal point is the generic point of an irreducible
component of the support, so [Stacks, Tag 02QW] applies. -/
theorem exists_minimal_mem_supp {U : Scheme.{u}} [AlgebraicGeometry.IsNoetherian U]
    (F : U.Modules) [F.IsCoherent] (hne : (_root_.SheafOfModules.supp F).Nonempty) :
    ∃ x : U, x ∈ _root_.SheafOfModules.supp F ∧
      (∀ y : U, y ∈ _root_.SheafOfModules.supp F → y ⤳ x → y = x) ∧
      Module.length (U.presheaf.stalk x) (F.presheaf.stalk x) ≠ ⊤ := by
  have hft : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := F)
  have hcl : IsClosed (_root_.SheafOfModules.supp F) := _root_.SheafOfModules.isClosed_supp F
  obtain ⟨z, hz⟩ := hne
  obtain ⟨C, hC, hzC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨z, hz⟩} : Set (_root_.SheafOfModules.supp F : Set U)) isIrreducible_singleton
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hirr : IsIrreducible (Subtype.val '' C) :=
    hC.1.image Subtype.val continuous_subtype_val.continuousOn
  have hclim : IsClosed (Subtype.val '' C) :=
    hcl.isClosedEmbedding_subtypeVal.isClosedMap C hCcl
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hirr hclim
  have hξim : ξ ∈ Subtype.val '' C := hξ ▸ subset_closure (Set.mem_singleton ξ)
  have hξsupp : ξ ∈ _root_.SheafOfModules.supp F := by
    obtain ⟨w, _, hw⟩ := hξim
    exact hw ▸ w.2
  refine ⟨ξ, hξsupp, fun y hy hyξ =>
    Stacks.Chow.eq_of_specializes_of_isGenericPoint_component hC hξ hy hyξ, ?_⟩
  exact Module.length_ne_top_iff.mpr
    (Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp F ⟨C, hC⟩ ξ hξ)

open CategoryTheory.Limits in
/-- **The exact-sequence step of [Stacks, Tag 0BJZ].** -/
theorem isCoherent_pushforward_of_isCoherent_pushforward_kernel {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] {F G : U.Modules}
    [F.IsQuasicoherent] (φ : F ⟶ G)
    (hker : ((Scheme.Modules.pushforward j).obj (kernel φ)).IsCoherent)
    (hG : ((Scheme.Modules.pushforward j).obj G).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent := by
  have hk : (kernel ((Scheme.Modules.pushforward j).map φ)).IsCoherent :=
    have := hker
    CoherentDevissage.isCoherent_of_iso
      (PreservesKernel.iso (Scheme.Modules.pushforward j) φ).symm
  have hkq : (kernel ((Scheme.Modules.pushforward j).map φ)).IsQuasicoherent :=
    have := hk
    (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hcoq : (Abelian.coimage ((Scheme.Modules.pushforward j).map φ)).IsQuasicoherent :=
    QuasicoherentColimits.isQuasicoherent_cokernel _
  have hco : (Abelian.coimage ((Scheme.Modules.pushforward j).map φ)).IsCoherent :=
    have := hG
    CoherentSubquotients.isCoherent_of_mono
      (Abelian.factorThruCoimage ((Scheme.Modules.pushforward j).map φ))
  exact AlgebraicGeometry.isCoherent_X₂_of_shortExact
    (S := ShortComplex.mk (kernel.ι ((Scheme.Modules.pushforward j).map φ))
      (cokernel.π (kernel.ι ((Scheme.Modules.pushforward j).map φ))) (cokernel.condition _))
    { exact := ShortComplex.exact_cokernel _ } hk hco

open CategoryTheory.Limits in
/-- The support of a kernel lies in the support of the source: the stalk sequence of the
canonical short exact sequence is exact, so the stalk of the kernel injects. -/
private theorem supp_kernel_subset {U : Scheme.{u}} {M N : U.Modules} (φ : M ⟶ N) :
    _root_.SheafOfModules.supp (kernel φ) ⊆ _root_.SheafOfModules.supp M := by
  intro y ⟨a, ha⟩
  exact ⟨AlgebraicGeometry.stalkLinearMap _ _ (kernel.ι φ) y a, fun h => ha
    (Scheme.Modules.injective_stalkLinearMap_of_mono (kernel.ι φ) inferInstance y
      (h.trans (map_zero _).symm))⟩

/-- A coherent module on a Noetherian scheme has finitely many associated points. -/
private theorem finite_associatedPoints {U : Scheme.{u}} [AlgebraicGeometry.IsNoetherian U]
    (M : U.Modules) [M.IsCoherent] : (Stacks.Divisors.associatedPoints M).Finite := by
  simpa using AlgebraicGeometry.associatedPoints_inter_finite M ⊤ (by simpa using isCompact_univ)

open CategoryTheory.Limits in
/-- A nonzero coherent module on a locally Noetherian scheme has nonempty support. -/
private theorem supp_nonempty_of_not_isZero {U : Scheme.{u}} [IsLocallyNoetherian U] (M : U.Modules)
    [M.IsCoherent] (hz : ¬IsZero M) : (_root_.SheafOfModules.supp M).Nonempty := by
  have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr fun h =>
    hz ((AlgebraicGeometry.isZero_iff_associatedPoints_eq_empty U M).mpr h)
  exact ⟨a, AlgebraicGeometry.associatedPoints_subset_support M ha⟩

open CategoryTheory.Limits in
/-- The direct image of a zero module is coherent. -/
private theorem isCoherent_pushforward_of_isZero {U X : Scheme.{u}} (j : U ⟶ X) {M : U.Modules}
    (h : IsZero M) : ((Scheme.Modules.pushforward j).obj M).IsCoherent :=
  CoherentDevissage.isCoherent_of_isZero (Functor.map_isZero (Scheme.Modules.pushforward j) h)

open CategoryTheory.Limits in
/-- Along a morphism to a module with simple stalk at `x` that is surjective on stalks at `x`,
the length of the stalk at `x` drops by one on passing to the kernel. -/
private theorem length_stalk_eq_length_stalk_kernel_add_one {U : Scheme.{u}} {F G : U.Modules}
    (φ : F ⟶ G) (x : U) [IsSimpleModule (U.presheaf.stalk x) (G.presheaf.stalk x)]
    (hφ : Function.Surjective (AlgebraicGeometry.stalkLinearMap F G φ x)) :
    Module.length (U.presheaf.stalk x) (F.presheaf.stalk x) =
      Module.length (U.presheaf.stalk x) ((kernel φ).presheaf.stalk x) + 1 := by
  rw [length_stalk_eq_add φ x, length_stalk_coimage φ x hφ,
    Module.length_eq_one (U.presheaf.stalk x) (G.presheaf.stalk x)]

open CategoryTheory.Limits in
/-- Under the hypotheses of `length_stalk_eq_length_stalk_kernel_add_one`, a bound `m + 1` on the
length of the stalk of `F` at `x` gives the bound `m` for the kernel. -/
private theorem length_stalk_kernel_le_of_le_succ {U : Scheme.{u}} {F G : U.Modules}
    (φ : F ⟶ G) (x : U) [IsSimpleModule (U.presheaf.stalk x) (G.presheaf.stalk x)]
    (hφ : Function.Surjective (AlgebraicGeometry.stalkLinearMap F G φ x)) {m : ℕ}
    (h : Module.length (U.presheaf.stalk x) (F.presheaf.stalk x) ≤ ((m + 1 : ℕ) : ℕ∞)) :
    Module.length (U.presheaf.stalk x) ((kernel φ).presheaf.stalk x) ≤ (m : ℕ∞) := by
  refine (ENat.add_le_add_iff_right (k := 1) (by simp)).mp ?_
  rw [← length_stalk_eq_length_stalk_kernel_add_one φ x hφ]
  exact_mod_cast h

open CategoryTheory.Limits in
/-- An associated point of `F` outside the support of `kernel φ` makes the kernel have strictly
fewer associated points. -/
private theorem ncard_associatedPoints_kernel_lt {U : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian U] {F G : U.Modules} [F.IsCoherent] (φ : F ⟶ G) {x : U}
    (hx : x ∈ Stacks.Divisors.associatedPoints F)
    (hxK : x ∉ _root_.SheafOfModules.supp (kernel φ)) :
    (Stacks.Divisors.associatedPoints (kernel φ)).ncard <
      (Stacks.Divisors.associatedPoints F).ncard :=
  Set.ncard_lt_ncard ⟨AlgebraicGeometry.associatedPoints_subset_of_mono (kernel.ι φ), fun h =>
    hxK (AlgebraicGeometry.associatedPoints_subset_support _ (h hx))⟩ (finite_associatedPoints F)

open CategoryTheory.Limits in
/-- **The induction of the first paragraph of [Stacks, Tag 0BJZ]**, over an abstract family
`x ↦ G x` of `𝒪_U`-modules: each `G x` is coherent, has simple stalk at `x`, and has coherent
direct image. -/
private theorem isCoherent_pushforward_aux {U X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j]
    [AlgebraicGeometry.IsNoetherian U] [U.IsQuasiAffine] (A : Set U) (G : U → U.Modules)
    (hGcoh : ∀ x ∈ A, (G x).IsCoherent)
    (hGsimple : ∀ x ∈ A, IsSimpleModule (U.presheaf.stalk x) ((G x).presheaf.stalk x))
    (hGpush : ∀ x ∈ A, ((Scheme.Modules.pushforward j).obj (G x)).IsCoherent) :
    ∀ (n m : ℕ) (F : U.Modules), F.IsCoherent →
      Stacks.Divisors.associatedPoints F ⊆ A →
      (Stacks.Divisors.associatedPoints F).ncard ≤ n →
      (IsZero F ∨ ∃ x : U, x ∈ _root_.SheafOfModules.supp F ∧
        (∀ y : U, y ∈ _root_.SheafOfModules.supp F → y ⤳ x → y = x) ∧
        Module.length (U.presheaf.stalk x) (F.presheaf.stalk x) ≤ (m : ℕ∞)) →
      ((Scheme.Modules.pushforward j).obj F).IsCoherent := by
  intro n
  induction n with
  | zero =>
      intro m F hF _ hcard _
      have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
      exact isCoherent_pushforward_of_isZero j
        ((AlgebraicGeometry.isZero_iff_associatedPoints_eq_empty U F).mpr
          ((Set.ncard_eq_zero (finite_associatedPoints F)).mp (Nat.le_zero.mp hcard)))
  | succ n ihn =>
      intro m
      induction m with
      | zero =>
          intro F _ _ _ hdisj
          rcases hdisj with h0 | ⟨x, hxs, _, hxl⟩
          · exact isCoherent_pushforward_of_isZero j h0
          have hnt : Nontrivial (F.presheaf.stalk x) :=
            (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp hxs
          rw [Nat.cast_zero] at hxl
          exact absurd hxl (not_le.mpr (Module.length_pos (R := U.presheaf.stalk x)
            (M := F.presheaf.stalk x)))
      | succ m ihm =>
          intro F hF hsub hcard hdisj
          have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
          rcases hdisj with h0 | ⟨x, hxs, hxmin, hxl⟩
          · exact isCoherent_pushforward_of_isZero j h0
          have hxass : x ∈ Stacks.Divisors.associatedPoints F :=
            AlgebraicGeometry.mem_associatedPoints_of_mem_supp_of_specialization U F x hxs hxmin
          have hGx := hGcoh x (hsub hxass)
          have := (CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent (G x)).1
          have hGs := hGsimple x (hsub hxass)
          obtain ⟨φ, hφ⟩ := exists_hom_surjective_stalkLinearMap_of_isSimpleModule F (G x) x hGs hxs
          have hKcoh : (kernel φ).IsCoherent := AlgebraicGeometry.isCoherent_kernel φ
          have hKsub : Stacks.Divisors.associatedPoints (kernel φ) ⊆
              Stacks.Divisors.associatedPoints F :=
            AlgebraicGeometry.associatedPoints_subset_of_mono (kernel.ι φ)
          refine isCoherent_pushforward_of_isCoherent_pushforward_kernel j φ ?_
            (hGpush x (hsub hxass))
          by_cases hxK : x ∈ _root_.SheafOfModules.supp (kernel φ)
          · exact ihm (kernel φ) hKcoh (hKsub.trans hsub)
              ((Set.ncard_le_ncard hKsub (finite_associatedPoints F)).trans hcard)
              (Or.inr ⟨x, hxK, fun y hy hyx => hxmin y (supp_kernel_subset φ hy) hyx,
                length_stalk_kernel_le_of_le_succ φ x hφ hxl⟩)
          by_cases hz : IsZero (kernel φ)
          · exact isCoherent_pushforward_of_isZero j hz
          obtain ⟨y, hy, hymin, hylen⟩ :=
            exists_minimal_mem_supp (kernel φ) (supp_nonempty_of_not_isZero _ hz)
          refine ihn (Module.length (U.presheaf.stalk y) ((kernel φ).presheaf.stalk y)).toNat
            (kernel φ) hKcoh (hKsub.trans hsub) ?_
            (Or.inr ⟨y, hy, hymin, le_of_eq (ENat.natCast_toNat hylen).symm⟩)
          exact Nat.lt_succ_iff.mp ((ncard_associatedPoints_kernel_lt φ hxass hxK).trans_le hcard)

open CategoryTheory.Limits in
/-- **The first paragraph of [Stacks, Tag 0BJZ] on a Noetherian quasi-affine open subscheme**,
run at an abstract family `x ↦ G x` indexed by the associated points of `F`: the double induction
of `isCoherent_pushforward_aux`, started at a minimal point of `Supp(F)`. -/
private theorem isCoherent_pushforward_of_family {U X : Scheme.{u}} [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] [AlgebraicGeometry.IsNoetherian U] [U.IsQuasiAffine]
    (F : U.Modules) [F.IsCoherent] (G : U → U.Modules)
    (hGcoh : ∀ x ∈ Stacks.Divisors.associatedPoints F, (G x).IsCoherent)
    (hGsimple : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      IsSimpleModule (U.presheaf.stalk x) ((G x).presheaf.stalk x))
    (hGpush : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      ((Scheme.Modules.pushforward j).obj (G x)).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent := by
  by_cases hz : IsZero F
  · exact isCoherent_pushforward_of_isZero j hz
  obtain ⟨x, hx, hxmin, hxlen⟩ := exists_minimal_mem_supp F (supp_nonempty_of_not_isZero F hz)
  exact isCoherent_pushforward_aux j (Stacks.Divisors.associatedPoints F) G hGcoh hGsimple
    hGpush (Stacks.Divisors.associatedPoints F).ncard
    (Module.length (U.presheaf.stalk x) (F.presheaf.stalk x)).toNat F
    ‹F.IsCoherent› subset_rfl le_rfl
    (Or.inr ⟨x, hx, hxmin, le_of_eq (ENat.natCast_toNat hxlen).symm⟩)

open CategoryTheory.Limits PointClosureComparison in
/-- **The implication (1) ⇒ (2) of [Stacks, Tag 0BJZ], for a Noetherian quasi-affine open
subscheme.** This is a special case, not registered under the tag. Let `X` be a locally
Noetherian scheme, let `j : U ⟶ X` be the inclusion of an open subscheme with `U` Noetherian and
quasi-affine, and let `F` be a coherent `𝒪_U`-module. If `j_* i_{x,*} 𝒪_{W_x}` is coherent for
every `x ∈ Ass(F)`, then `j_* F` is coherent.

The two conditions on `U` are what the source's reduction to an affine base supplies; they are
used only to produce the comparison morphism `F ⟶ i_{x,*} 𝒪_{W_x}`, through
[Stacks, Tag 01YB] for a principal ideal sheaf. The unconditional form is
`isCoherent_pushforward_of_forall_isAssociatedPoint'`, and the tag sits on the full equivalence
`isCoherent_pushforward_iff_forall_isAssociatedPoint`. -/
theorem isCoherent_pushforward_of_forall_isAssociatedPoint {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] [AlgebraicGeometry.IsNoetherian U]
    [U.IsQuasiAffine] (F : U.Modules) [F.IsCoherent]
    (h : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent :=
  isCoherent_pushforward_of_family j F pointClosureStructureSheaf
    (fun x _ => isCoherent_pointClosureStructureSheaf x)
    (fun x _ => isSimpleModule_stalk_pointClosureStructureSheaf x) h

open PointClosureComparison Stacks.AlgebraicGeometry.CodimensionOneObstruction in
/-- **The affine piece of [Stacks, Tag 0BJZ], the implication (1) ⇒ (2).** Over an affine open
`V` of `X` the restriction `j^{-1}V` of the open subscheme is Noetherian and quasi-affine, so the
induction applies there, to the family `y ↦ (i_{y,*} 𝒪_{W_y})|_{j^{-1}V}` restricted from `U`. -/
private theorem isCoherent_pushforward_restrict_of_forall_isAssociatedPoint {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (F : U.Modules) [F.IsCoherent]
    (V : X.Opens) [IsAffine V.toScheme]
    (h : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent) :
    ((Scheme.Modules.pushforward (j ∣_ V)).obj (F.restrict (j ⁻¹ᵁ V).ι)).IsCoherent := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have : AlgebraicGeometry.IsNoetherian V.toScheme := {}
  have : NoetherianSpace V.toScheme := AlgebraicGeometry.IsNoetherian.noetherianSpace
  have hNS : NoetherianSpace (j ⁻¹ᵁ V).toScheme :=
    (j ∣_ V).isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace (j ⁻¹ᵁ V).toScheme := hNS.compactSpace
  have : IsLocallyNoetherian (j ⁻¹ᵁ V).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (j ⁻¹ᵁ V).ι
  have : AlgebraicGeometry.IsNoetherian (j ⁻¹ᵁ V).toScheme := {}
  have : (j ⁻¹ᵁ V).toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion (j ∣_ V)
  have : (F.restrict (j ⁻¹ᵁ V).ι).IsCoherent :=
    AlgebraicGeometry.Modules.isCoherent_restrict F (j ⁻¹ᵁ V)
  refine isCoherent_pushforward_of_family (j ∣_ V) (F.restrict (j ⁻¹ᵁ V).ι)
    (fun y => (pointClosureStructureSheaf y.1).restrict (j ⁻¹ᵁ V).ι)
    (fun y _ => have := isCoherent_pointClosureStructureSheaf (y.1 : U)
      AlgebraicGeometry.Modules.isCoherent_restrict _ (j ⁻¹ᵁ V))
    (fun y _ => isSimpleModule_stalk_restrict (j ⁻¹ᵁ V) _ y
      (isSimpleModule_stalk_pointClosureStructureSheaf (y.1 : U)))
    fun y hy => ?_
  have := h (y.1 : U) ((isAssociatedPoint_restrict_iff (j ⁻¹ᵁ V).ι F y).mp hy)
  have : (((Scheme.Modules.pushforward j).obj
      (pointClosureStructureSheaf (y.1 : U))).restrict V.ι).IsCoherent :=
    AlgebraicGeometry.Modules.isCoherent_restrict _ V
  exact (isCoherent_restrict_pushforward_iff j V _).mp this

/-- **[Stacks, Tag 0BJZ], the implication (1) ⇒ (2).** Let `X` be a locally Noetherian scheme,
let `j : U ⟶ X` be the inclusion of an open subscheme and let `F` be a coherent `𝒪_U`-module. If
`j_* i_{x,*} 𝒪_{W_x}` is coherent for every `x ∈ Ass(F)`, then `j_* F` is coherent.

Coherence of a direct image is local on the target, and over an affine open of `X` the open
subscheme becomes Noetherian and quasi-affine, which is what the induction needs.

This is one direction of [Stacks, Tag 0BJZ]; the tag sits on the full equivalence
`isCoherent_pushforward_iff_forall_isAssociatedPoint`, in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.CoherenceEquivalence`.
-/
@[stacks 0BJZ "(1) implies (2)"]
theorem isCoherent_pushforward_of_forall_isAssociatedPoint' {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (F : U.Modules) [F.IsCoherent]
    (h : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      ((Scheme.Modules.pushforward j).obj (pointClosureStructureSheaf x)).IsCoherent) :
    ((Scheme.Modules.pushforward j).obj F).IsCoherent :=
  isCoherent_pushforward_of_forall_affineOpens j F fun V =>
    have : IsAffine (V : X.Opens).toScheme := V.2
    isCoherent_pushforward_restrict_of_forall_isAssociatedPoint j F (V : X.Opens) h

end Stacks.AlgebraicGeometry.CoherenceFromPointClosures

end
