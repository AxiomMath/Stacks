module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RankOneLocusHilbert
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChangeGeneral
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtensionGeneral
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.DerivedPushforwardToField
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# Field-valued points of `Pic_{X/k, σ}` translate into the rank-one locus

Let `k` be a separably closed field and `X` a smooth projective curve over `k` with a `k`-rational
point `σ`. For a field extension `K/k` and `ℒ ∈ Pic_{X/k, σ}(K)` there is `ℒ' ∈ Pic_{X/k, σ}(k)`
with `ℒ'_K + ℒ ∈ F(K)`, where `F` is the subfunctor of [Stacks, Tag 0B9V]: this is condition
(2)(c) of [Stacks, Tag 0B9Q], in the proof of [Stacks, Tag 0B9Z].

## Main results

* `AlgebraicGeometry.nonempty_iso_unit_of_finrank_moduleSpecΓFunctor_eq_one`: A sheaf of modules
  on `Spec K` whose global sections form a line is isomorphic to `𝒪_{Spec K}`.
* `AlgebraicGeometry.nonempty_derivedPushforwardModule_iso_single_unit`: For `q : Y ⟶ Spec K`
  quasi-compact and quasi-separated and a quasi-coherent `N` with `dim H⁰(Y, N) = 1` and
  `H^n(Y, N) = 0` for `n > 0`, `Rq_*(N[0]) ≅ 𝒪_{Spec K}[0]`.
* `AlgebraicGeometry.subsingleton_ofScheme_spec_field`: The Picard group of the spectrum of a
  field vanishes.
* `AlgebraicGeometry.RigidifiedPicard.exists_add_mem_rankOneLocus`: Condition (2)(c) of
  [Stacks, Tag 0B9Q] for `Pic_{X/k, σ}` and `F`, at a `k`-scheme of the form `Spec K`.

## References

* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

section SpecField

variable (K : Type u) [Field K]

/-- An open of `Spec K` other than the whole space is empty. -/
theorem eq_bot_of_ne_top_spec_field (V : (Spec (.of K)).Opens) (hV : V ≠ ⊤) : V = ⊥ := by
  refine eq_bot_iff.2 fun x hx => hV (top_le_iff.1 fun y _ => ?_)
  rwa [Subsingleton.elim y x]

/-- An open of `Spec K` other than the whole space has no points. -/
private theorem false_of_mem_of_ne_top_spec_field (V : (Spec (.of K)).Opens) (hV : V ≠ ⊤)
    {y : Spec (.of K)} (hy : y ∈ V) : False := by
  simp [eq_bot_of_ne_top_spec_field K V hV] at hy

/-- **Over the empty open, every sheaf of modules on `Spec K` has a single section.** -/
theorem subsingleton_sections_of_ne_top_spec_field (M : (Spec (.of K)).Modules)
    (V : (Spec (.of K)).Opens) (hV : V ≠ ⊤) : Subsingleton (M.val.obj (op V)) := by
  let F : TopCat.Sheaf AddCommGrpCat (Spec (.of K)).carrier :=
    ⟨M.val.presheaf, _root_.SheafOfModules.isSheaf M⟩
  exact ⟨fun s t => TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) F V s t fun _ hy =>
    (false_of_mem_of_ne_top_spec_field K V hV hy).elim⟩

/-- Over the empty open, the structure sheaf of `Spec K` is the zero ring. -/
theorem subsingleton_structureSheaf_of_ne_top_spec_field (V : (Spec (.of K)).Opens)
    (hV : V ≠ ⊤) : Subsingleton ((Spec (.of K)).presheaf.obj (op V)) := by
  exact ⟨fun s t => TopCat.Presheaf.section_ext (C := CommRingCat.{u}) (Spec (.of K)).sheaf V s t
    fun _ hy => (false_of_mem_of_ne_top_spec_field K V hV hy).elim⟩

/-- **A sheaf of modules on `Spec K` with no nonzero global section is zero.** -/
theorem isZero_of_subsingleton_sections_top_spec_field (M : (Spec (.of K)).Modules)
    (h : Subsingleton (M.val.obj (op ⊤))) : IsZero M := by
  refine Stacks.SheafOfModulesEvaluation.isZero_of_forall_isZero_evaluation _ fun U => ?_
  by_cases hU : U.unop = ⊤
  · rw [show U = op ⊤ from congrArg op hU]
    exact ModuleCat.isZero_iff_subsingleton.2 h
  · exact ModuleCat.isZero_iff_subsingleton.2
      (subsingleton_sections_of_ne_top_spec_field K M U.unop hU)

/-- **A sheaf of modules on `Spec K` whose global sections form a line is `𝒪_{Spec K}`.** -/
theorem nonempty_iso_unit_of_finrank_moduleSpecΓFunctor_eq_one (M : (Spec (.of K)).Modules)
    (h : Module.finrank K (moduleSpecΓFunctor.obj M) = 1) :
    Nonempty (M ≅ _root_.SheafOfModules.unit (Spec (.of K)).ringCatSheaf) := by
  have hpos : 0 < Module.finrank K (moduleSpecΓFunctor.obj M) := by lia
  have : Module.Free K (moduleSpecΓFunctor.obj M) := Module.Free.of_divisionRing K _
  have : Module.Finite K (moduleSpecΓFunctor.obj M) := Module.finite_of_finrank_pos hpos
  have : Nontrivial (moduleSpecΓFunctor.obj M) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : moduleSpecΓFunctor.obj M)
  have hspan := (finrank_eq_one_iff_of_nonzero' s₀ hs₀).1 h
  let s : M.val.sections := PresheafOfModules.sectionsMk
    (fun A => M.val.map (homOfLE (le_top (a := A.unop))).op (show M.val.obj (op ⊤) from s₀))
    (fun {A B} f => by
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) _)
  refine Stacks.SheafOfModules.nonempty_iso_unit_of_bijective_smul_on_cover
    (X := (Spec (.of K)).toRingedSpace) M s
    (fun _ : Unit => ⊤) (eq_top_iff.2 fun _ _ => Opens.mem_iSup.2 ⟨(), trivial⟩) fun _ V _ => ?_
  by_cases hV : V = ⊤
  · subst hV
    have hev : s.eval (op ⊤) = (show M.val.obj (op ⊤) from s₀) := by
      show M.val.map (homOfLE (le_top (a := (⊤ : (Spec (.of K)).Opens)))).op s₀ = s₀
      rw [show (homOfLE (le_top (a := (⊤ : (Spec (.of K)).Opens)))).op = 𝟙 _ from
        Subsingleton.elim _ _, M.val.map_id]
      rfl
    rw [hev]
    let φ := (Scheme.ΓSpecIso (.of K)).hom
    have hφ : Function.Bijective φ.hom := ConcreteCategory.bijective_of_isIso φ
    have hK : Function.Bijective (fun c : K => c • s₀) :=
      ⟨fun c₁ c₂ hc => smul_left_injective K hs₀ hc, fun m => hspan m⟩
    have hψ : Function.Bijective
        (fun c => (Scheme.ΓSpecIso (.of K)).inv.hom ((Scheme.ΓSpecIso (.of K)).hom.hom c)) :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).comp hφ
    exact (Function.Bijective.of_comp_iff _ hψ).1 (hK.comp hφ)
  · have := subsingleton_sections_of_ne_top_spec_field K M V hV
    have := subsingleton_structureSheaf_of_ne_top_spec_field K V hV
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun m => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **Cohomology over a point computes the derived pushforward.** Let `q : Y ⟶ Spec K` be
quasi-compact and quasi-separated and `N` a quasi-coherent `𝒪_Y`-module with `dim_K H⁰(Y, N) = 1`
and `H^n(Y, N) = 0` for every `n > 0`. Then `Rq_*(N[0]) ≅ 𝒪_{Spec K}[0]`. -/
theorem nonempty_derivedPushforwardModule_iso_single_unit {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of K)) [QuasiCompact q] [QuasiSeparated q] (N : Y.Modules)
    [N.IsQuasicoherent] (h0 : Module.finrank K (cohomologyOverField K q N 0) = 1)
    (hpos : ∀ n : ℕ, 0 < n → IsZero (cohomologyOverField K q N n)) :
    Nonempty (ProperFlatFibreEulerCharacteristic.derivedPushforwardModule q N ≅
      (DerivedCategory.singleFunctor (Spec (.of K)).Modules 0).obj
        (_root_.SheafOfModules.unit (Spec (.of K)).ringCatSheaf)) := by
  set E := ProperFlatFibreEulerCharacteristic.derivedPushforwardModule q N with hE
  have hGE : E.IsGE 0 := isGE_derivedPushforward_obj q _ 0 (by
    show ((DerivedCategory.singleFunctor Y.Modules 0).obj N).IsGE 0
    infer_instance)
  have hLE : E.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg hi.le⟩
    obtain ⟨e⟩ := nonempty_homology_derivedPushforward_linearEquiv_cohomologyOverField K q N n
    have hz : Subsingleton (cohomologyOverField K q N n) :=
      ModuleCat.subsingleton_of_isZero (hpos n (by exact_mod_cast hi))
    have hs : Subsingleton ((moduleSpecΓFunctor (R := .of K)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules n).obj E)) :=
      e.toEquiv.subsingleton
    exact isZero_of_subsingleton_sections_top_spec_field K _ hs
  obtain ⟨Y₀, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E 0
  have eH : (DerivedCategory.homologyFunctor (Spec (.of K)).Modules 0).obj E ≅ Y₀ :=
    (DerivedCategory.homologyFunctor _ 0).mapIso eY ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app Y₀
  obtain ⟨e₀⟩ := nonempty_homology_derivedPushforward_linearEquiv_cohomologyOverField K q N 0
  have hY₀ : Module.finrank K (moduleSpecΓFunctor.obj Y₀) = 1 := by
    rw [← ((moduleSpecΓFunctor (R := .of K)).mapIso eH).toLinearEquiv.finrank_eq, ← h0]
    exact e₀.finrank_eq
  obtain ⟨eU⟩ := nonempty_iso_unit_of_finrank_moduleSpecΓFunctor_eq_one K Y₀ hY₀
  exact ⟨eY ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eU⟩

/-- **The Picard group of the spectrum of a field vanishes.** -/
theorem subsingleton_ofScheme_spec_field :
    Subsingleton (Stacks.Picard.ofScheme (Spec (.of K))) := by
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : Stacks.Picard.ofScheme (Spec (.of K)), z = 0 := by
    intro z
    have := (Stacks.Picard.picardRepresentative (Spec (.of K)).toRingedSpace z).property
    obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology (Spec (.of K))
      (Stacks.Picard.picardRepresentative (Spec (.of K)).toRingedSpace z).obj
    exact (Stacks.Picard.eq_zero_iff_nonempty_iso_unit z).2 ⟨e⟩
  exact (hx x).trans (hx y).symm

end SpecField

namespace RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- Over the spectrum of a field, the normalisation along `σ` is the identity. -/
theorem coe_normalize_spec_field (K : Type u) [Field K] (α : Spec (.of K) ⟶ Spec (.of k))
    (a : Stacks.Picard.ofScheme (pullback f (Over.mk α).hom)) :
    (normalize f σ hσ (Over.mk α) a).1 = a := by
  have := subsingleton_ofScheme_spec_field K
  show a - Stacks.Picard.schemePullbackClassHom (pullback.snd f (Over.mk α).hom)
    (Stacks.Picard.schemePullbackClassHom (sectionAt f σ hσ (Over.mk α)) a) = a
  rw [show Stacks.Picard.schemePullbackClassHom (sectionAt f σ hσ (Over.mk α)) a = 0 from
    @Subsingleton.elim (Stacks.Picard.ofScheme (Spec (.of K))) this _ _, map_zero, sub_zero]

/-- **A class over `Spec K` whose representative has the cohomology of a point lies in `F(K)`.**
If an invertible `N` on `X_K` with `dim H⁰(X_K, N) = 1` and `H^n(X_K, N) = 0` for `n > 0`
represents `c ∈ Pic_{X/k, σ}(K)`, then `c ∈ F(K)`. -/
theorem mem_rankOneLocus_of_cohomology [IsProper f] (K : Type u) [Field K]
    (α : Spec (.of K) ⟶ Spec (.of k)) (c : (picardFunctor f σ hσ).obj (op (Over.mk α)))
    (N : (pullback f α).Modules)
    (hN : Stacks.SheafOfModules.IsInvertible (pullback f α).presheaf
      (pullback f α).ringCatSheaf.2 N)
    (hc : (c : kernelAt f σ hσ (Over.mk α)).1 =
      Stacks.SheafOfModules.picardClass _ (Stacks.RingedSpace.structureIsSheaf _) N hN)
    (h0 : Module.finrank K (cohomologyOverField K (pullback.snd f α) N 0) = 1)
    (hpos : ∀ n : ℕ, 0 < n → IsZero (cohomologyOverField K (pullback.snd f α) N n)) :
    c ∈ rankOneLocus f σ hσ (Over.mk α) := by
  set L := Stacks.Picard.picardRepresentative (pullback f α).toRingedSpace
    (c : kernelAt f σ hσ (Over.mk α)).1 with hL
  have hLcl := (Stacks.Picard.classOf_picardRepresentative (pullback f α).toRingedSpace
    (c : kernelAt f σ hσ (Over.mk α)).1).trans hc
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hLcl
  have e' : (L.obj : (pullback f α).Modules) ≅ N := e
  have : N.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible N hN
  have hq : IsProper (pullback.snd f α) := inferInstance
  obtain ⟨eE⟩ := nonempty_derivedPushforwardModule_iso_single_unit K (pullback.snd f α) N h0 hpos
  refine ⟨_root_.SheafOfModules.unit (Spec (.of K)).ringCatSheaf,
    SheafOfModules.isFiniteLocallyFreeOfRank_unit _, ⟨?_⟩⟩
  exact (derivedPushforward (pullback.snd f α).toLRSHom.toShHom).mapIso
    ((DerivedCategory.singleFunctor (pullback f α).Modules 0).mapIso e') ≪≫ eE

/-- **Condition (2)(c) of [Stacks, Tag 0B9Q] for `Pic_{X/k, σ}` and the subfunctor `F` of
[Stacks, Tag 0B9V]**, at a point `α : Spec K ⟶ Spec k`: for `ℒ ∈ Pic_{X/k, σ}(K)` there is
`ℒ' ∈ Pic_{X/k, σ}(k)` whose pullback to `K` added to `ℒ` lies in `F(K)`. -/
theorem exists_add_mem_rankOneLocus [IsSepClosed k] [IsCurve k f] [IsProjectiveVariety k f]
    [Smooth f] (K : Type u) [Field K] (α : Spec (.of K) ⟶ Spec (.of k))
    (c : (picardFunctor f σ hσ).obj (op (Over.mk α))) :
    ∃ r : (picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k))))),
      (picardFunctor f σ hσ).map
          (Over.homMk α (Category.comp_id α) : Over.mk α ⟶ Over.mk (𝟙 (Spec (.of k)))).op r + c ∈
        rankOneLocus f σ hσ (Over.mk α) := by
  have : IsProper f := inferInstance
  set φ : Over.mk α ⟶ Over.mk (𝟙 (Spec (.of k))) := Over.homMk α (Category.comp_id α)
  let : Algebra k K := (Spec.preimage α).hom.toAlgebra
  have hα : Spec.map (CommRingCat.ofHom (algebraMap k K)) = α := Spec.map_preimage α
  have hp : IsPullback (pullback.fst f α) (pullback.snd f α) f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    hα ▸ IsPullback.of_hasPullback f α
  set L := Stacks.Picard.picardRepresentative (pullback f α).toRingedSpace
    (c : kernelAt f σ hσ (Over.mk α)).1 with hL
  have hLinv : Stacks.Ample.IsInvertibleModule (pullback f α) L.obj :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ L.property
  have hproj : IsProjective f :=
    (IsProjectiveVariety.isProjective (k := k) (f := f)).isProjective
  obtain ⟨L₀, hL₀, h0, h1⟩ :=
    exists_invertible_baseChangeTwist_finrank_cohomologyOverField_eq_one' k K f
      (pullback.snd f α) (pullback.fst f α) hp hproj L.obj
  have hL₀' : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L₀ :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL₀
  set ℓ₀ : Stacks.Picard.ofScheme X :=
    Stacks.SheafOfModules.picardClass _ _ L₀ hL₀' with hℓ₀
  set r := normalize f σ hσ (Over.mk (𝟙 (Spec (.of k))))
    (Stacks.Picard.schemePullbackClass (pullback.fst f (𝟙 (Spec (.of k)))) ℓ₀) with hr
  refine ⟨r, ?_⟩
  have hfst : baseChangeMap f φ ≫
      pullback.fst f (𝟙 (Spec (.of k))) = pullback.fst f α := by
    simp only [baseChangeMap, pullback.map, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hrK : (picardFunctor f σ hσ).map φ.op r =
      normalize f σ hσ (Over.mk α) (Stacks.Picard.schemePullbackClass (pullback.fst f α) ℓ₀) := by
    show kernelMap f σ hσ φ r = _
    rw [hr, kernelMap_normalize, Stacks.Picard.schemePullbackClass_comp, hfst]
  set N := baseChangeTwist (pullback.fst f α) L.obj L₀ with hN
  have hpinv : Stacks.SheafOfModules.IsInvertible (pullback f α).presheaf
      (Stacks.RingedSpace.structureIsSheaf (pullback f α).toRingedSpace)
      ((Scheme.Modules.pullback (pullback.fst f α)).obj L₀) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of (pullback.fst f α).toLRSHom.toShHom L₀ hL₀'
  have hNinv : Stacks.SheafOfModules.IsInvertible (pullback f α).presheaf
      (Stacks.RingedSpace.structureIsSheaf (pullback f α).toRingedSpace) N :=
    have := L.property
    have := hpinv
    Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _
  have hpb : Stacks.Picard.schemePullbackClass (pullback.fst f α) ℓ₀ =
      Stacks.SheafOfModules.picardClass _ _ _ hpinv :=
    Stacks.Picard.pullbackClass_classOf (pullback.fst f α).toLRSHom.toShHom L₀ hL₀'
  have hcc : (c : kernelAt f σ hσ (Over.mk α)).1 =
      Stacks.SheafOfModules.picardClass _ _ L.obj L.property :=
    (Stacks.Picard.classOf_picardRepresentative _ _).symm
  have hcl : (Stacks.Picard.schemePullbackClass (pullback.fst f α) ℓ₀ :
        Stacks.Picard.ofScheme (pullback f (Over.mk α).hom)) +
      (c : kernelAt f σ hσ (Over.mk α)).1 =
      Stacks.SheafOfModules.picardClass _ _ N hNinv := by
    rw [hpb, add_comm, hcc]
    exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ L.property hpinv hNinv
  have hsum : ((picardFunctor f σ hσ).map φ.op r + c :
        kernelAt f σ hσ (Over.mk α)).1 =
      Stacks.SheafOfModules.picardClass _ _ N hNinv := by
    show ((picardFunctor f σ hσ).map φ.op r :
        kernelAt f σ hσ (Over.mk α)).1 + (c : kernelAt f σ hσ (Over.mk α)).1 = _
    rwa [hrK, coe_normalize_spec_field f σ hσ K α]
  have hdim : topologicalKrullDim (pullback f α : Scheme.{u}) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_baseChange k K (pullback.fst f α) (pullback.snd f α) f hp,
      IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)]
    rfl
  refine mem_rankOneLocus_of_cohomology f σ hσ K α _ N hNinv hsum h0 fun n hn => ?_
  rcases Nat.lt_or_ge 1 n with h | h
  · exact isZero_cohomologyOverField_of_topologicalKrullDim_le' K (pullback.snd f α) N hdim h
  · obtain rfl : n = 1 := le_antisymm h hn
    exact h1

end RigidifiedPicard

end AlgebraicGeometry

end
