module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.Epi.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoveringNumber.SeparatedCover
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.BaseVanishingCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict

/-!
# A uniform vanishing degree for the higher direct images of a quasi-compact morphism

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. [Stacks, Tag 01XJ] asserts that one integer `n`, depending on `f` alone, makes
`R ᵖ f_* F` vanish for every quasi-coherent `𝒪_X`-module `F` and every `p ≥ n`.

The bound is the one the source constructs. Choose a finite affine open cover `S = ⋃ Sⱼ` and, for
each `j`, a finite affine open cover `f⁻¹(Sⱼ) = ⋃ᵢ Uⱼᵢ`; the integer attached to `j` is the
maximum over subsets `I` of the fibre index set of `|I| + t(⋂_{i ∈ I} Uⱼᵢ)`, where `t` is the
affine covering number, and the bound is the maximum of those over `j`.

## Main results

* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerived_pushforward`:
  the uniform bound, with the higher direct images taken on the bounded below derived category.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedNat_pushforward`:
  the same bound for Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, which is
  built from injective resolutions and so mentions no model of the derived category at all.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerived_of_isAffine_target`:
  the bound over an affine base.
* `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward`:
  the bound for `CategoryTheory.Functor.rightDerivedPlus` at an arbitrary model of the bounded
  below derived category, the two `CategoryTheory.HasDerivedCategory` instances being free
  parameters rather than `CategoryTheory.HasDerivedCategory.standard`.

## Implementation notes

Higher direct images are the right derived functors of pushforward on sheaves of modules.
The degree is indexed by `ℤ`, as `Functor.rightDerivedPlus`; the two indexings are compared by
`Stacks.DerivedIndexing.rightDerivedIso` and `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`.

The two spellings of the category of modules on a scheme — `AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules (structureSheafRing X)` — are definitionally equal but not syntactically so, and
each comparison between them is made explicitly.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite RingedSpaceModuleAdjunction
open CategoryTheory.Abelian
open TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffineCoveringNumber
open Stacks.Cohomology.HigherDirectImage (moduleRestriction asRingSheafedSpace
  openSubspaceInclusion preimageOpen restrictedMorphism
  restrictedMorphism_comp_openSubspaceInclusion higherDirectImageRestrictIso)
open Stacks.Cohomology.LerayModules (nonempty_cohomology_iso_higherDirectImage_of_vanishing)

attribute [local instance] HasDerivedCategory.standard

universe u w w'

namespace Stacks.AlgebraicGeometry.HigherDirectImageQcoh

/-- Vanishing of Mathlib's cohomology presheaf at the top open is vanishing of the cohomology
group of the module sheaf, in positive degrees. -/
private lemma isZero_Hgroup_of_isZero_cohomologyPresheaf
    {X : Scheme.{u}} [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : X.Modules) (p : ℕ) (hp : 0 < p)
    (hF : IsZero
      ((((SheafOfModules.toSheaf X.ringCatSheaf).obj F).cohomologyPresheaf p).obj
        (op (⊤ : X.Opens)))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  cases p with
  | zero => omega
  | succ n =>
    let RT : RingedSpace.{u} := X.toLocallyRingedSpace.toRingedSpace
    let R := ringCatSheaf RT
    let J := Opens.grothendieckTopology RT.carrier
    let A := (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free)
    let G := (SheafOfModules.toSheaf R ⋙
      (sheafSections J AddCommGrpCat.{u}).obj (op (⊤ : X.Opens)))
    have hExt : IsZero ((CategoryTheory.Abelian.extFunctorObj A (n + 1)).obj
        ((SheafOfModules.toSheaf R).obj F)) := by
      simpa [A, Sheaf.cohomologyPresheaf, Sheaf.cohomologyPresheafFunctor] using hF
    let eEval := ModuleSheafCohomology.evaluationRepresentation J (⊤ : X.Opens)
    have hAb : IsZero ((G.rightDerived (n + 1)).obj F) := by
      let e₁ := ModuleSheafCohomology.rightDerivedIso eEval (n + 1)
      let e₂ := ModuleSheafCohomology.rightDerivedCoyonedaSuccIso.{u}
        (A := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) A n
      let e₃ := Functor.isoWhiskerLeft (SheafOfModules.toSheaf R) (e₁ ≪≫ e₂)
      have h : IsZero (((SheafOfModules.toSheaf R ⋙
          ((sheafSections J AddCommGrpCat.{u}).obj
            (op (⊤ : X.Opens))).rightDerived (n + 1))).obj F) :=
        IsZero.of_iso hExt (e₃.app F)
      obtain ⟨_, _, hsections⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying J R
      obtain ⟨eU, _⟩ := hsections (⊤ : X.Opens)
      exact IsZero.of_iso h ((eU (n + 1)).app F)
    simpa [Hgroup, Hfunctor, secF, R, RT, J] using hAb

/-- Chosen finite affine covers of the base and of the inverse images of its members, for a
quasi-compact and quasi-separated morphism over a quasi-compact base. -/
private theorem exists_finiteAffineCoversWithBound
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S] : ∃ C : FiniteAffineCoversWithBound.{u},
      C.X = X ∧ C.S = S ∧ HEq C.f f := by
  classical
  have htopcompact : IsCompact ((⊤ : S.Opens) : Set S) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set S))
  obtain ⟨Us, hUs, hUs_finite, hUs_sup⟩ :=
    S.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) htopcompact
  let Us' := insert (⊥ : S.Opens) Us
  have hUs' : ∀ U ∈ Us', IsAffineOpen U := by
    intro U hU
    rcases Set.mem_insert_iff.mp hU with rfl | hU
    · exact isAffineOpen_bot S
    · exact hUs hU
  have hUs'_finite : Us'.Finite := hUs_finite.insert _
  have hUs'_sup : sSup Us' = ⊤ := by
    refine le_antisymm le_top ?_
    rw [hUs_sup]
    exact sSup_le_sSup fun U hU ↦ Set.mem_insert_of_mem _ hU
  let _ : Fintype Us' := hUs'_finite.fintype
  let e := Fintype.equivFin Us'
  let m := Fintype.card Us'
  have hne : Nonempty Us' := ⟨⟨⊥, Set.mem_insert_iff.mpr (Or.inl rfl)⟩⟩
  have hm : 0 < m := Fintype.card_pos
  let B : Fin m → S.Opens := fun j ↦ (e.symm j).val
  have hB_aff : ∀ j, IsAffineOpen (B j) := fun j ↦ hUs' (B j) (e.symm j).property
  have hB_cover : iSup B = ⊤ := by
    apply le_antisymm
    · rw [← hUs'_sup, sSup_eq_iSup]
      refine iSup_le fun j ↦ ?_
      exact le_iSup_of_le (e.symm j).val (le_iSup_of_le (e.symm j).property le_rfl)
    · rw [← hUs'_sup, sSup_eq_iSup]
      refine iSup_le fun U' ↦ iSup_le fun hU' ↦ ?_
      let a : Us' := ⟨U', hU'⟩
      exact le_iSup_of_le (e a) (by simp [B, a])
  let M : Fin m → ℕ := fun j ↦
    Classical.choose (AlgebraicGeometry.exists_fin_affine_cover_of_isCompact
      (f ⁻¹ᵁ B j) (f.isCompact_preimage (hB_aff j).isCompact))
  let V : ∀ j, Fin (M j) → X.Opens := fun j ↦ Classical.choose
    (Classical.choose_spec (AlgebraicGeometry.exists_fin_affine_cover_of_isCompact
      (f ⁻¹ᵁ B j) (f.isCompact_preimage (hB_aff j).isCompact)))
  have hV_aff : ∀ j i, IsAffineOpen (V j i) := fun j i ↦
    (Classical.choose_spec (Classical.choose_spec
      (AlgebraicGeometry.exists_fin_affine_cover_of_isCompact
        (f ⁻¹ᵁ B j) (f.isCompact_preimage (hB_aff j).isCompact)))).1 i
  have hV_cover : ∀ j, iSup (V j) = f ⁻¹ᵁ B j := fun j ↦
    (Classical.choose_spec (Classical.choose_spec
      (AlgebraicGeometry.exists_fin_affine_cover_of_isCompact
        (f ⁻¹ᵁ B j) (f.isCompact_preimage (hB_aff j).isCompact)))).2
  exact ⟨{ X := X, S := S, f := f
           quasiCompact := inferInstance
           quasiSeparated := inferInstance
           compactSpace := inferInstance
           baseCard := m
           baseCard_pos := hm
           baseOpen := B
           baseOpen_isAffine := hB_aff
           iSup_baseOpen := hB_cover
           fiberCard := M
           fiberOpen := V
           fiberOpen_isAffine := hV_aff
           iSup_fiberOpen := hV_cover }, rfl, rfl, HEq.rfl⟩

/-- Taking inverse images commutes with a finite infimum of opens. -/
private lemma hom_preimage_finset_inf {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ}
    (V : Fin n → Y.Opens) (I : Finset (Fin n)) :
    f ⁻¹ᵁ (I.inf V) = I.inf (fun i => f ⁻¹ᵁ V i) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih => simp [Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

/-- A finite infimum of quasi-compact opens of a quasi-compact, quasi-separated scheme is
quasi-compact. -/
private lemma compact_finset_inf {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {n : ℕ} (V : Fin n → X.Opens) (hV : ∀ i, IsCompact (V i : Set X))
    (I : Finset (Fin n)) : IsCompact ((I.inf V : X.Opens) : Set X) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (CompactSpace.isCompact_univ : IsCompact (Set.univ : Set X))
  | @insert a I ha ih =>
    simpa [Finset.inf_insert] using
      (QuasiSeparatedSpace.inter_isCompact (V a : Set X) (I.inf V : X.Opens)
        (V a).2 (hV a) (I.inf V).2 ih)

/-- Above the chosen bound, the cohomology of the inverse image of a member of the chosen affine
cover of the base vanishes on every quasi-coherent module. -/
private lemma cohomologyPresheaf_isZero_on_restricted_source
    (C : FiniteAffineCoversWithBound.{u}) (j : Fin C.baseCard)
    (F : ((C.f ⁻¹ᵁ C.baseOpen j : C.X.Opens) : Scheme).Modules) [F.IsQuasicoherent]
    (p : ℕ) (hp : C.bound ≤ p) :
    IsZero (((((SheafOfModules.toSheaf
      ((C.f ⁻¹ᵁ C.baseOpen j : C.X.Opens) : Scheme).ringCatSheaf).obj F).cohomologyPresheaf
        p).obj (op (⊤ : ((C.f ⁻¹ᵁ C.baseOpen j : C.X.Opens) : Scheme).Opens)))) := by
  classical
  let Xj : Scheme := (C.f ⁻¹ᵁ C.baseOpen j : C.X.Opens)
  let e : Xj ⟶ C.X := Scheme.Opens.ι (C.f ⁻¹ᵁ C.baseOpen j)
  have : IsAffine (C.baseOpen j : Scheme) := C.baseOpen_isAffine j
  have : CompactSpace (C.baseOpen j : Scheme) :=
    isCompact_iff_compactSpace.mp (C.baseOpen_isAffine j).isCompact
  have : QuasiCompact C.f := C.quasiCompact
  have : QuasiSeparated C.f := C.quasiSeparated
  have : QuasiCompact (C.f ∣_ C.baseOpen j) := inferInstance
  have : QuasiSeparated (C.f ∣_ C.baseOpen j) := inferInstance
  have : CompactSpace Xj := QuasiCompact.compactSpace_of_compactSpace (C.f ∣_ C.baseOpen j)
  have : QuasiSeparatedSpace Xj := quasiSeparatedSpace_of_quasiSeparated (C.f ∣_ C.baseOpen j)
  let V : Fin (C.fiberCard j) → Xj.Opens := fun i ↦ e ⁻¹ᵁ C.fiberOpen j i
  have hV_le (i : Fin (C.fiberCard j)) : C.fiberOpen j i ≤ e.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    calc
      C.fiberOpen j i ≤ iSup (C.fiberOpen j) := le_iSup_of_le i le_rfl
      _ = C.f ⁻¹ᵁ C.baseOpen j := C.iSup_fiberOpen j
  have hV_affine (i : Fin (C.fiberCard j)) : IsAffineOpen (V i) := by
    dsimp [V]
    exact (C.fiberOpen_isAffine j i).preimage_of_isOpenImmersion e (hV_le i)
  have hV_cover : iSup V = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, C.iSup_fiberOpen j]
    exact Scheme.Opens.ι_preimage_self (C.f ⁻¹ᵁ C.baseOpen j)
  let d := Finset.univ.sup fun I : Finset (Fin (C.fiberCard j)) ↦
    I.card + AffineCoveringNumber.minimalAffineCoverCardinality (⨅ i ∈ I, V i) - 1
  have hbound : d ≤ C.bound := by
    apply Finset.sup_le
    intro I hI
    have hmin : AffineCoveringNumber.minimalAffineCoverCardinality (I.inf V) ≤
        AffineCoveringNumber.minimalAffineCoverCardinality
          ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ I.inf (C.fiberOpen j)) := by
      let VI : Xj.Opens := I.inf V
      let UI : C.X.Opens := I.inf (C.fiberOpen j)
      have hcompactVI : IsCompact (VI : Set Xj) := by
        simpa [VI] using compact_finset_inf V (fun i ↦ (hV_affine i).isCompact) I
      have hpreI : VI = e ⁻¹ᵁ UI := (hom_preimage_finset_inf e (C.fiberOpen j) I).symm
      have himage : e ''ᵁ VI = (C.f ⁻¹ᵁ C.baseOpen j) ⊓ UI := by
        rw [hpreI, e.image_preimage_eq_opensRange_inf]
        simp [e, Scheme.Opens.opensRange_ι]
      have hcompact : IsCompact
          (((C.f ⁻¹ᵁ C.baseOpen j) ⊓ UI : C.X.Opens) : Set C.X) := by
        rw [← himage]
        exact hcompactVI.image e.continuous
      obtain ⟨r, A₀, hA₀_affine, hA₀_cover⟩ :=
        AlgebraicGeometry.exists_fin_affine_cover_of_isCompact _ hcompact
      let m := AffineCoveringNumber.minimalAffineCoverCardinality ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ UI)
      have hm_nonempty : {q : ℕ | ∃ A : Fin q → C.X.Opens,
          (∀ k, IsAffineOpen (A k)) ∧ iSup A = (C.f ⁻¹ᵁ C.baseOpen j) ⊓ UI}.Nonempty :=
        ⟨r, ⟨A₀, hA₀_affine, hA₀_cover⟩⟩
      have hm_mem : ∃ A : Fin m → C.X.Opens,
          (∀ k, IsAffineOpen (A k)) ∧ iSup A = (C.f ⁻¹ᵁ C.baseOpen j) ⊓ UI := by
            simpa [m, AffineCoveringNumber.minimalAffineCoverCardinality] using
              (Nat.sInf_mem hm_nonempty)
      obtain ⟨A, hA_affine, hA_cover⟩ := hm_mem
      have hA_le (k : Fin m) : A k ≤ e.opensRange := by
        rw [Scheme.Opens.opensRange_ι]
        calc
          A k ≤ iSup A := le_iSup A k
          _ = (C.f ⁻¹ᵁ C.baseOpen j) ⊓ UI := hA_cover
          _ ≤ C.f ⁻¹ᵁ C.baseOpen j := inf_le_left
      let A' (k : Fin m) : Xj.Opens := e ⁻¹ᵁ A k
      have hA'_affine : ∀ k, IsAffineOpen (A' k) := by
        intro k
        dsimp [A']
        exact (hA_affine k).preimage_of_isOpenImmersion e (hA_le k)
      have hpre : e ⁻¹ᵁ ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ UI) = VI := by
        rw [← himage]
        exact e.preimage_image_eq _
      have hA'_cover : iSup A' = VI := by
        calc
          iSup A' = e ⁻¹ᵁ iSup A := (Scheme.Hom.preimage_iSup e A).symm
          _ = VI := by rw [hA_cover, hpre]
      have hminVI : AffineCoveringNumber.minimalAffineCoverCardinality VI ≤ m := by
        change sInf {q : ℕ | ∃ B : Fin q → Xj.Opens,
          (∀ k, IsAffineOpen (B k)) ∧ iSup B = VI} ≤ m
        exact Nat.sInf_le ⟨A', hA'_affine, hA'_cover⟩
      simpa [VI, UI, m] using hminVI
    have hIV : (⨅ i ∈ I, V i) = I.inf V := by rw [← Finset.inf_eq_iInf]
    have hterm : I.card + AffineCoveringNumber.minimalAffineCoverCardinality (⨅ i ∈ I, V i) - 1 ≤
        I.card + AffineCoveringNumber.minimalAffineCoverCardinality
          ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ I.inf (C.fiberOpen j)) := by
      rw [hIV]
      omega
    have hlocal : I.card + AffineCoveringNumber.minimalAffineCoverCardinality
        ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ I.inf (C.fiberOpen j)) ≤ C.localBound j := by
      unfold FiniteAffineCoversWithBound.localBound
      change I.card + AffineCoveringNumber.minimalAffineCoverCardinality
          ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ I.inf (C.fiberOpen j)) ≤
        Finset.univ.powerset.sup (fun K : Finset (Fin (C.fiberCard j)) ↦
          K.card + AffineCoveringNumber.minimalAffineCoverCardinality
            ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ K.inf (C.fiberOpen j)))
      exact Finset.le_sup (s := Finset.univ.powerset)
        (f := fun K : Finset (Fin (C.fiberCard j)) ↦
          K.card + AffineCoveringNumber.minimalAffineCoverCardinality
            ((C.f ⁻¹ᵁ C.baseOpen j) ⊓ K.inf (C.fiberOpen j)))
        (b := I) (Finset.mem_powerset.mpr (Finset.subset_univ I))
    have hlocal' : C.localBound j ≤ C.bound := by
      unfold FiniteAffineCoversWithBound.bound
      exact Finset.le_sup (Finset.mem_univ j)
    exact hterm.trans (hlocal.trans hlocal')
  exact cohomology_isZero_of_degree_ge_affineCoveringNumber V hV_cover
    (fun i ↦ (hV_affine i).isCompact)
    (fun i ↦ by
      have : IsAffine (V i : Scheme) := hV_affine i
      infer_instance) rfl F p (hbound.trans hp)

/-- A quasi-coherent module on an affine scheme with no global sections is zero. -/
private lemma isZero_quasicoherent_module_of_isZero_sections
    {T : Scheme.{u}} [IsAffine T] (M : T.Modules) [M.IsQuasicoherent]
    (hΓ : IsZero ((SheafOfModules.evaluation T.ringCatSheaf (op (⊤ : T.Opens))).obj M)) :
    IsZero M := by
  let e := T.isoSpec
  let M' := (Scheme.Modules.restrictFunctor e.inv).obj M
  have : M'.IsQuasicoherent := inferInstance
  have hΓcarrier : Subsingleton (M.val.obj (op (⊤ : T.Opens))) :=
    ModuleCat.isZero_iff_subsingleton.mp hΓ
  have hΓ'carrier : Subsingleton (M'.val.obj (op (⊤ : (Spec Γ(T, ⊤)).Opens))) := by
    dsimp [M', Scheme.Modules.restrictFunctor, SheafOfModules.pushforward,
      PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
      PresheafOfModules.pushforward₀Obj]
    change Subsingleton (M.val.obj (op (e.inv ''ᵁ (⊤ : (Spec Γ(T, ⊤)).Opens))))
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    exact hΓcarrier
  have hΓmodule : IsZero
      ((modulesSpecToSheaf.obj M').presheaf.obj (op (⊤ : (Spec Γ(T, ⊤)).Opens))) :=
    ModuleCat.isZero_iff_subsingleton.mpr hΓ'carrier
  have htilde : IsZero ((tilde.functor (CommRingCat.of Γ(T, ⊤))).obj
      ((modulesSpecToSheaf.obj M').presheaf.obj (op (⊤ : (Spec Γ(T, ⊤)).Opens)))) :=
    Functor.map_isZero _ hΓmodule
  have hM' : IsZero M' := IsZero.of_iso htilde (asIso M'.fromTildeΓ).symm
  have hM'' : IsZero ((Scheme.Modules.restrictFunctor e.inv ⋙
      Scheme.Modules.restrictFunctor e.hom).obj M) := by
    change IsZero ((Scheme.Modules.restrictFunctor e.hom).obj M')
    exact Functor.map_isZero _ hM'
  have hMcomp : IsZero ((Scheme.Modules.restrictFunctor (e.hom ≫ e.inv)).obj M) :=
    IsZero.of_iso hM'' ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app M)
  exact IsZero.of_iso hMcomp
    (((Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.restrictFunctorId).app M).symm)

/-- Above the chosen bound, the cohomology groups of the inverse image of a member of the chosen
affine cover of the base vanish on every quasi-coherent module. -/
private lemma isZero_Hgroup_on_restricted_source
    (C : FiniteAffineCoversWithBound.{u}) (j : Fin C.baseCard)
    (F : ((C.f ⁻¹ᵁ C.baseOpen j : C.X.Opens) : Scheme).Modules)
    [F.IsQuasicoherent] (q : ℕ) (hq : C.bound + 1 ≤ q) :
    IsZero (Hgroup (((C.f ⁻¹ᵁ C.baseOpen j : C.X.Opens) : Scheme).ringCatSheaf) ⊤ q F) := by
  exact isZero_Hgroup_of_isZero_cohomologyPresheaf F q (by omega)
    (cohomologyPresheaf_isZero_on_restricted_source C j F q (by omega))

/-- The `ℕ`-indexed higher direct images of a quasi-coherent module along a quasi-compact and
quasi-separated morphism are quasi-coherent. -/
private lemma isQuasicoherent_rightDerived_pushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsQuasicoherent :=
  have : (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F).IsQuasicoherent :=
    inferInstance
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n).app F).symm this

/-- Vanishing of the degree-zero cohomology group is vanishing of the global sections. -/
private lemma isZero_evaluation_of_isZero_Hgroup_zero
    {T : Scheme.{u}} (M : T.Modules) (h : IsZero (Hgroup T.ringCatSheaf ⊤ 0 M)) :
    IsZero ((SheafOfModules.evaluation T.ringCatSheaf (op (⊤ : T.Opens))).obj M) := by
  let RT : RingedSpace.{u} := T.toLocallyRingedSpace.toRingedSpace
  let E := SheafOfModules.evaluation (ringCatSheaf RT) (op (⊤ : T.Opens))
  let G := forget₂ (ModuleCat ((ringCatSheaf RT).obj.obj (op (⊤ : T.Opens)))) AddCommGrpCat
  have : PreservesFiniteLimits (secF T.ringCatSheaf ⊤) := by
    change PreservesFiniteLimits (E ⋙ G)
    infer_instance
  have h' : IsZero (((secF T.ringCatSheaf ⊤).rightDerived 0).obj M) := h
  have hΓ : IsZero ((secF T.ringCatSheaf ⊤).obj M) :=
    IsZero.of_iso h' ((secF T.ringCatSheaf ⊤).rightDerivedZeroIsoSelf.app M).symm
  have hΓ' : IsZero (G.obj (E.obj M)) := hΓ
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (G.obj (E.obj M))
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hΓ'

/-- A module sheaf whose restrictions to the members of an open cover vanish is zero. -/
private lemma isZero_module_of_isZero_ringedRestrictions
    {S : Scheme.{u}} {n : ℕ} (U : Fin n → S.Opens) (hU : iSup U = ⊤) (M : S.Modules)
    (hrest : ∀ i, IsZero ((moduleRestriction S.toLocallyRingedSpace.toRingedSpace (U i)).obj M)) :
    IsZero M := by
  classical
  have hstalk (x : S) : IsZero (M.presheaf.stalk x) := by
    have hxcover : x ∈ ⋃ i, (U i : Set S) := by
      have hx : x ∈ (iSup U : S.Opens) := by rw [hU]; simp
      simpa using hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcover
    let y : (TopologicalSpace.Opens.toTopCat (TopCat.of S)).obj (U i) := ⟨x, hxi⟩
    let T := Stacks.Cohomology.HigherDirectImage.restrictToOpen
      S.toLocallyRingedSpace.toRingedSpace (U i)
    let J := Opens.grothendieckTopology (TopCat.of T)
    let P := (sheafToPresheaf J Ab).obj
      ((SheafOfModules.toSheaf (ringCatSheaf T)).obj
        ((moduleRestriction S.toLocallyRingedSpace.toRingedSpace (U i)).obj M))
    have hz : IsZero (TopCat.Presheaf.stalk (X := TopCat.of T) P y) := by
      have hz₁ := Functor.map_isZero (SheafOfModules.toSheaf (ringCatSheaf T)) (hrest i)
      have hz₂ := Functor.map_isZero (sheafToPresheaf J Ab) hz₁
      have hz₃ := Functor.map_isZero (TopCat.Presheaf.stalkFunctor.{u} Ab y) hz₂
      change IsZero ((TopCat.Presheaf.stalkFunctor Ab y).obj P)
      simpa only [P] using hz₃
    have e := TopCat.Presheaf.stalkRestrictIso (U i) M.presheaf y
    have hm : (U i).inclusion' y = x := rfl
    rw [← hm]
    exact IsZero.of_iso hz e.symm
  let F : TopCat.Sheaf Ab (TopCat.of S) := ⟨M.presheaf, M.isSheaf⟩
  have hF : IsZero F := by
    rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
    exact hstalk
  have hM : IsZero ((Scheme.Modules.toPresheaf S).obj M) :=
    Functor.map_isZero (TopCat.Sheaf.forget Ab (TopCat.of S)) hF
  apply (IsZero.iff_id_eq_zero M).mpr
  apply Functor.map_injective (Scheme.Modules.toPresheaf S)
  change 𝟙 ((Scheme.Modules.toPresheaf S).obj M) = 0
  exact (IsZero.iff_id_eq_zero _).mp hM

/-- For a quasi-compact and quasi-separated morphism of schemes whose target is quasi-compact
there is an integer, depending on the morphism alone, above which every higher direct image of
every quasi-coherent module vanishes. -/
@[stacks 01XJ "uniform_vanishing"]
theorem exists_isZero_rightDerived_pushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ n : ℤ, ∀ p : ℤ, n ≤ p → ∀ (F : X.Modules) [F.IsQuasicoherent],
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  classical
  obtain ⟨C, hCX, hCS, hCf⟩ := exists_finiteAffineCoversWithBound f
  cases hCX
  cases hCS
  cases hCf
  refine ⟨(C.bound : ℤ) + 1, ?_⟩
  intro p hp F hF
  have : F.IsQuasicoherent := hF
  have hp_pos : 0 < p := by omega
  let q : ℕ := p.toNat
  have hpq : (q : ℤ) = p := Int.toNat_of_nonneg hp_pos.le
  have hbound : C.bound + 1 ≤ q := by omega
  let Uj : Fin C.baseCard → C.S.Opens := C.baseOpen
  let Xj : Fin C.baseCard → Scheme := fun j ↦ (C.f ⁻¹ᵁ Uj j : C.X.Opens)
  let Sj : Fin C.baseCard → Scheme := fun j ↦ (Uj j : Scheme)
  let ej : ∀ j, Xj j ⟶ C.X := fun j ↦ Scheme.Opens.ι (C.f ⁻¹ᵁ Uj j)
  let fj : ∀ j, Xj j ⟶ Sj j := fun j ↦ C.f ∣_ Uj j
  let Fj : ∀ j, (Xj j).Modules := fun j ↦ (Scheme.Modules.restrictFunctor (ej j)).obj F
  have hFjqc (j : Fin C.baseCard) : (Fj j).IsQuasicoherent := by
    have : IsOpenImmersion (ej j) := by dsimp [ej]; infer_instance
    exact Scheme.Modules.isQuasicoherent_restrictFunctor (ej j) F
  have hlocal : ∀ j : Fin C.baseCard,
      IsZero (Hgroup (Sj j).ringCatSheaf ⊤ 0
        (((Scheme.Modules.pushforward (fj j)).rightDerived q).obj (Fj j))) := by
    intro j
    let RXj : RingedSpace.{u} := (Xj j).toLocallyRingedSpace.toRingedSpace
    let RSj : RingedSpace.{u} := (Sj j).toLocallyRingedSpace.toRingedSpace
    let gj : RXj ⟶ RSj := (fj j).toLRSHom.toShHom
    have : IsAffine (Sj j) := C.baseOpen_isAffine j
    have : (Fj j).IsQuasicoherent := hFjqc j
    have hsource : IsZero (Hgroup (ringCatSheaf RXj) ⊤ q (Fj j)) :=
      isZero_Hgroup_on_restricted_source C j (Fj j) q hbound
    have hvan : ∀ a b : ℕ, 0 < a →
        IsZero (Hgroup (ringCatSheaf RSj) ⊤ a
          (((modulePushforward gj).rightDerived b).obj (Fj j))) := by
      intro a b ha
      let Q := ((Scheme.Modules.pushforward (fj j)).rightDerived b).obj (Fj j)
      have : Q.IsQuasicoherent := isQuasicoherent_rightDerived_pushforward (fj j) (Fj j) b
      change IsZero (Hgroup (ringCatSheaf RSj) ⊤ a Q)
      exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen (Sj j) Q ⊤
        (isAffineOpen_top (Sj j)) a ha
    obtain ⟨e⟩ :=
      nonempty_cohomology_iso_higherDirectImage_of_vanishing gj (Fj j) hvan q
    exact IsZero.of_iso hsource e.symm
  let RX : RingedSpace.{u} := C.X.toLocallyRingedSpace.toRingedSpace
  let RS : RingedSpace.{u} := C.S.toLocallyRingedSpace.toRingedSpace
  let g : RX ⟶ RS := C.f.toLRSHom.toShHom
  let Q : C.S.Modules := ((Scheme.Modules.pushforward C.f).rightDerived q).obj F
  have hlocalZero (j : Fin C.baseCard) :
      IsZero (((Scheme.Modules.pushforward (fj j)).rightDerived q).obj (Fj j)) := by
    have : IsAffine (Sj j) := C.baseOpen_isAffine j
    have : (Fj j).IsQuasicoherent := hFjqc j
    let Lj := ((Scheme.Modules.pushforward (fj j)).rightDerived q).obj (Fj j)
    have : Lj.IsQuasicoherent := isQuasicoherent_rightDerived_pushforward (fj j) (Fj j) q
    exact isZero_quasicoherent_module_of_isZero_sections Lj
      (isZero_evaluation_of_isZero_Hgroup_zero Lj (hlocal j))
  have hrest (j : Fin C.baseCard) : IsZero ((moduleRestriction RS (Uj j)).obj Q) := by
    have hRXj : openSubspace RX (preimageOpen g (Uj j)) =
        (Xj j).toLocallyRingedSpace.toRingedSpace := rfl
    have hRSj : openSubspace RS (Uj j) = (Sj j).toLocallyRingedSpace.toRingedSpace := rfl
    have hEjApp (W : (Xj j).Opens) : (ej j).appIso W = Iso.refl _ := by
      change (Scheme.Opens.ι (C.f ⁻¹ᵁ Uj j)).appIso W = Iso.refl _
      exact Scheme.Opens.ι_appIso (C.f ⁻¹ᵁ Uj j) W
    have hmap : (fj j).toLRSHom.toShHom = restrictedMorphism g (Uj j) := by
      cases hRXj
      cases hRSj
      have : SheafedSpace.IsOpenImmersion (openSubspaceInclusion RS (Uj j)) :=
        SheafedSpace.IsOpenImmersion.ofRestrict RS (Uj j).isOpenEmbedding
      have : Mono (openSubspaceInclusion RS (Uj j)) := by infer_instance
      have hfac : (fj j).toLRSHom.toShHom ≫ openSubspaceInclusion RS (Uj j) =
          openSubspaceInclusion RX (preimageOpen g (Uj j)) ≫ g := by
        have hs := congrArg (fun k : Xj j ⟶ C.S ↦ k.toLRSHom)
          (morphismRestrict_ι C.f (Uj j))
        rw [Scheme.Hom.comp_toLRSHom, Scheme.Hom.comp_toLRSHom] at hs
        have hs' := congrArg LocallyRingedSpace.Hom.toShHom hs
        rw [LocallyRingedSpace.comp_toShHom, LocallyRingedSpace.comp_toShHom] at hs'
        change (fj j).toLRSHom.toShHom ≫ (Uj j).ι.toLRSHom.toShHom =
          (C.f ⁻¹ᵁ Uj j).ι.toLRSHom.toShHom ≫ C.f.toLRSHom.toShHom
        exact hs'
      exact (cancel_mono (openSubspaceInclusion RS (Uj j))).1
        (hfac.trans (restrictedMorphism_comp_openSubspaceInclusion g (Uj j)))
    have hinput : ((moduleRestriction RX (preimageOpen g (Uj j))).obj F) ≅ Fj j := by
      cases hRXj
      let : (preimageOpen g (Uj j)).isOpenEmbedding.functor.IsContinuous
          (Opens.grothendieckTopology
            ((TopologicalSpace.Opens.toTopCat RX.carrier).obj (preimageOpen g (Uj j))))
          (Opens.grothendieckTopology RX.carrier) :=
        (preimageOpen g (Uj j)).isOpenEmbedding.functor_isContinuous
      dsimp [Fj, Scheme.Modules.restrictFunctor, moduleRestriction, asRingSheafedSpace,
        restMod, phiSh, OUSh, OXSh, jFun, openSubspace, LocallyRingedSpace.toRingedSpace,
        ringCatSheaf]
      exact (SheafOfModules.pushforwardCongr (by
        ext W
        have hApp := hEjApp (unop W)
        dsimp [CategoryTheory.Functor.whiskerRight]
        simp [hApp]
        rfl)).app F
    have hdom : IsZero (((modulePushforward (restrictedMorphism g (Uj j))).rightDerived q).obj
        ((moduleRestriction RX (preimageOpen g (Uj j))).obj F)) := by
      have hlocal' : IsZero (((modulePushforward ((fj j).toLRSHom.toShHom)).rightDerived q).obj
          (Fj j)) := hlocalZero j
      rw [hmap] at hlocal'
      exact IsZero.of_iso hlocal'
        (((modulePushforward (restrictedMorphism g (Uj j))).rightDerived q).mapIso hinput)
    exact IsZero.of_iso hdom ((higherDirectImageRestrictIso g (Uj j) q).app F).symm
  have hQ : IsZero Q := isZero_module_of_isZero_ringedRestrictions Uj C.iSup_baseOpen Q hrest
  rw [← hpq]
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward C.f) q F).1 hQ

/-! ### The other two indexings of the bound -/

/-- For a quasi-compact and quasi-separated morphism of schemes whose target is quasi-compact
there is a natural number, depending on the morphism alone, above which `(Rⁿ f_*) F` vanishes for
every quasi-coherent module `F`, where `Rⁿ f_*` is Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived (Scheme.Modules.pushforward f) n`. -/
@[stacks 01XJ "uniform_vanishing",
  ega "IV 1.7.21" "vanishing bound",
  ega "III 1.4.12" "existence of r"]
theorem exists_isZero_rightDerivedNat_pushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℕ, ∀ F : X.Modules, F.IsQuasicoherent → ∀ n : ℕ, N ≤ n →
      IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) := by
  obtain ⟨N, hN⟩ := exists_isZero_rightDerived_pushforward f
  refine ⟨N.toNat, fun F hF n hn ↦ ?_⟩
  have : F.IsQuasicoherent := hF
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward f) n F).2 (hN (n : ℤ) (by omega) F)

/-- For a quasi-compact and quasi-separated morphism of schemes with affine target there is a
natural number above which `(Rⁿ f_*) F` vanishes for every quasi-coherent module `F`, for Mathlib's
`ℕ`-indexed right derived functors. -/
theorem exists_isZero_rightDerived_of_isAffine_target {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [IsAffine S] :
    ∃ N : ℕ, ∀ F : X.Modules, F.IsQuasicoherent → ∀ n : ℕ, N ≤ n →
      IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) :=
  exists_isZero_rightDerivedNat_pushforward f

/-- For a quasi-compact and quasi-separated morphism of schemes whose target is quasi-compact
there is an integer, depending on the morphism alone, above which every higher direct image of
every quasi-coherent module vanishes, for the `ℤ`-indexed right derived functors at an arbitrary
model of the bounded below derived category. -/
@[stacks 01XJ "uniform_vanishing"]
theorem exists_isZero_rightDerivedPlus_pushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S]
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} S.Modules] :
    ∃ N : ℤ, ∀ p : ℤ, N ≤ p → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  obtain ⟨N, hN⟩ := exists_isZero_rightDerivedNat_pushforward f
  refine ⟨(N : ℤ) + 1, fun p hp F hF ↦ ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
    (Scheme.Modules.pushforward f) n F).1 (hN F hF n (by omega))

-- Stacks 071N compares the higher direct images of a quasi-coherent sheaf on the small étale or
-- Zariski site with those on the scheme; that comparison is a statement about quasi-coherent
-- modules because the higher direct images are themselves quasi-coherent.
add_to_stacks 071N "quasi-coherence of the higher direct images"
  isQuasicoherent_higherDirectImage

end Stacks.AlgebraicGeometry.HigherDirectImageQcoh

end
