module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Perfect.FibreCriterion.BaseChangeSurjective
import Mathlib
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# The three-term splitting from two adjacent surjective base-change maps

Finiteness and projectivity of the isolated cohomology module, the normalized three-term
decomposition and its uniqueness, and the splitting criterion [stacks 0A1V]
(`StacksDraft.Perfect.exists_localization_finite_free_homology_and_iso_biprod`).

Part of `StacksFrontier.Homology.Perfect.FibreCriterion`; see that module for the overview.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

-- The truncation and base-change identifications below read instances through iterated
-- `mapHomologicalComplex` and `opcycles` isomorphisms; this needs the pre-4.x defeq transparency.
set_option backward.isDefEq.respectTransparency false

namespace StacksDraft.Perfect

universe u v

/-! ### Finiteness and projectivity of the isolated cohomology module -/

/-- The degree-`i` cohomology of a complex concentrated in degrees `≥ i` is a retract of its
degree-`i` term, provided the complex maps to one concentrated in degrees `≤ i` by a map which is
an isomorphism on degree-`i` cohomology. -/
private lemma finite_projective_homology_of_split_at
    {R : Type u} [CommRing R]
    (P Q : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ)
    [P.IsStrictlyGE i] [Q.IsStrictlyLE i]
    [Module.Finite R (P.X i)] [Module.Projective R (P.X i)]
    (φ : P ⟶ Q) [IsIso (HomologicalComplex.homologyMap φ i)] :
    Module.Finite R (P.homology i) ∧ Module.Projective R (P.homology i) := by
  have hdP : P.d (i - 1) i = 0 :=
    (P.isZero_of_isStrictlyGE i (i - 1) (by omega)).eq_of_src _ _
  have hdQ : Q.d i (i + 1) = 0 :=
    (Q.isZero_of_isStrictlyLE i (i + 1) (by omega)).eq_of_tgt _ _
  have := P.isIso_homologyπ (i - 1) i (by simp) hdP
  have := Q.isIso_iCycles i (i + 1) (by simp) hdQ
  let inclusion : P.homology i ⟶ P.X i := inv (P.homologyπ i) ≫ P.iCycles i
  let retraction : P.X i ⟶ P.homology i := φ.f i ≫ inv (Q.iCycles i) ≫
    Q.homologyπ i ≫ inv (HomologicalComplex.homologyMap φ i)
  have h : inclusion ≫ retraction = 𝟙 _ := by
    simp only [inclusion, retraction, Category.assoc,
      ← HomologicalComplex.cyclesMap_i_assoc, IsIso.hom_inv_id_assoc,
      ← HomologicalComplex.homologyπ_naturality_assoc, IsIso.inv_hom_id_assoc,
      IsIso.hom_inv_id]
  have hr : Function.Surjective retraction.hom := by
    intro x
    exact ⟨inclusion.hom x, congrArg (fun f : P.homology i ⟶ P.homology i => f.hom x) h⟩
  exact ⟨Module.Finite.of_surjective retraction.hom hr,
    Module.Projective.of_split inclusion.hom retraction.hom (congrArg ModuleCat.Hom.hom h)⟩

section Homology

variable {C : Type*} [Category C] [Abelian C]

/-- The canonical truncation inclusion is an isomorphism on cohomology in degrees `≤ n`. -/
private lemma isIso_homology_truncLEι (K : DerivedCategory C) (n j : ℤ) (hj : j ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C j).map
      ((DerivedCategory.TStructure.t.truncLEι n).app K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGE n (n + 1) rfl).obj K
  have hT := t.triangleLEGE_distinguished n (n + 1) rfl K
  have : Epi ((DerivedCategory.homologyFunctor C j).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT j).mpr
      ((DerivedCategory.isZero_of_isGE ((t.truncGE (n + 1)).obj K) (n + 1) j
        (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor C j).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (j - 1) j
      (by omega)).mpr
      ((DerivedCategory.isZero_of_isGE ((t.truncGE (n + 1)).obj K) (n + 1) (j - 1)
        (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C j).map T.mor₁)

/-- The canonical truncation projection is an isomorphism on cohomology in degrees `≥ n`. -/
private lemma isIso_homology_truncGEπ (K : DerivedCategory C) (n j : ℤ) (hj : n ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor C j).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app K)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLEGE (n - 1) n (by omega)).obj K
  have hT := t.triangleLEGE_distinguished (n - 1) n (by omega) K
  have : Epi ((DerivedCategory.homologyFunctor C j).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT j (j + 1) rfl).mpr
      ((DerivedCategory.isZero_of_isLE ((t.truncLE (n - 1)).obj K) (n - 1) (j + 1)
        (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor C j).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT j).mpr
      ((DerivedCategory.isZero_of_isLE ((t.truncLE (n - 1)).obj K) (n - 1) j
        (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C j).map T.mor₂)

/-- An object concentrated in degree `i` is isomorphic to the single complex on its degree-`i`
cohomology, compatibly with a prescribed comparison. -/
private lemma exists_iso_single_normalized
    (K : DerivedCategory C) (i : ℤ) [K.IsLE i] [K.IsGE i]
    (H : C) (comparison : (DerivedCategory.homologyFunctor C i).obj K ≅ H) :
    ∃ e : K ≅ (DerivedCategory.singleFunctor C i).obj H,
      (DerivedCategory.homologyFunctor C i).map e.hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C i).hom.app H =
          comparison.hom := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K i
  let F := DerivedCategory.homologyFunctor C i
  let S := DerivedCategory.singleFunctor C i
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso C i
  let d : M ≅ H := (F.mapIso e ≪≫ ε.app M).symm ≪≫ comparison
  refine ⟨e ≪≫ S.mapIso d, ?_⟩
  show F.map (e.hom ≫ S.map d.hom) ≫ ε.hom.app H = comparison.hom
  have hn : F.map (S.map d.hom) ≫ ε.hom.app H = ε.hom.app M ≫ d.hom :=
    ε.hom.naturality d.hom
  rw [F.map_comp, Category.assoc, hn]
  simp [d, F, ε]

/-- A map between objects concentrated in degree `i` vanishes as soon as it vanishes on degree-`i`
cohomology. -/
private lemma hom_eq_zero_of_homology_eq_zero
    (X Y : DerivedCategory C) (i : ℤ)
    [X.IsLE i] [X.IsGE i] [Y.IsLE i] [Y.IsGE i]
    (f : X ⟶ Y) (hf : (DerivedCategory.homologyFunctor C i).map f = 0) : f = 0 := by
  obtain ⟨M, ⟨eM⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X i
  obtain ⟨N, ⟨eN⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y i
  let S := DerivedCategory.singleFunctor C i
  let F := DerivedCategory.homologyFunctor C i
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso C i
  obtain ⟨g, hg⟩ := S.map_surjective (eM.inv ≫ f ≫ eN.hom)
  have hm : F.map (S.map g) = 0 := by
    rw [hg, F.map_comp, F.map_comp, hf]
    simp
  have hn : F.map (S.map g) ≫ ε.hom.app N = ε.hom.app M ≫ g := ε.hom.naturality g
  have hg0 : g = 0 := by
    rw [hm, zero_comp] at hn
    apply (cancel_epi (ε.hom.app M)).mp
    simpa using hn.symm
  rw [hg0, S.map_zero] at hg
  apply (cancel_epi eM.inv).mp
  apply (cancel_mono eN.hom).mp
  simpa using hg.symm

end Homology

/-- Finiteness and projectivity transfer along an isomorphism of modules. -/
private lemma finite_projective_of_iso
    {R : Type u} [CommRing R] {M N : ModuleCat.{max u v} R} (e : M ≅ N)
    [Module.Finite R M] [Module.Projective R M] :
    Module.Finite R N ∧ Module.Projective R N :=
  ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv⟩

/-- Every morphism `Q(P) ⟶ Q(Q)` in the derived category out of a K-projective complex `P` is the
image of a chain map `P ⟶ Q`. -/
private lemma exists_chainMap_of_isKProjective
    {C : Type*} [Category C] [Abelian C]
    (P Q : CochainComplex C ℤ) [P.IsKProjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q) :
    ∃ φ : P ⟶ Q, DerivedCategory.Q.map φ = f := by
  let η := DerivedCategory.quotientCompQhIso C
  let qf := η.hom.app P ≫ f ≫ η.inv.app Q
  obtain ⟨q, hq⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient C (.up ℤ)).obj Q)).surjective qf
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective q
  refine ⟨φ, ?_⟩
  have hn : DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map φ) ≫
      η.hom.app Q = η.hom.app P ≫ DerivedCategory.Q.map φ := η.hom.naturality φ
  rw [hq] at hn
  have h := congrArg (fun z => η.inv.app P ≫ z) hn
  simpa [qf, Category.assoc] using h.symm

/-- If `τ_{≥ a'} K` has projective amplitude in `[a', b]`, where `a + 1 = a'`, then `K` splits as
`τ_{≤ a} K ⊕ τ_{≥ a'} K`, compatibly with the truncation maps. -/
private lemma exists_iso_biprod_truncLE_truncGE
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R)) (a a' b : ℤ)
    (h : a + 1 = a')
    (hU : HasProjectiveAmplitude.{u, v} ((DerivedCategory.TStructure.t.truncGE a').obj K) a' b) :
    ∃ e : K ≅ (DerivedCategory.TStructure.t.truncLE a).obj K ⊞
        (DerivedCategory.TStructure.t.truncGE a').obj K,
      (DerivedCategory.TStructure.t.truncLEι a).app K ≫ e.hom = biprod.inl ∧
      (DerivedCategory.TStructure.t.truncGEπ a').app K = e.hom ≫ biprod.snd := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  obtain ⟨e, he, -⟩ := (hom_eq_zero_and_existsUnique_iso_biprod
    ((t.truncLE a).obj K) ((t.truncGE a').obj K) a' b hU).2.2
    (fun j hj => DerivedCategory.isZero_of_isLE _ a j (by omega)) K
    ((t.truncLEι a).app K) ((t.truncGEπ a').app K) ((t.truncGEδLE a a' h).app K)
    (t.triangleLEGE_distinguished a a' h K)
  exact ⟨e, he⟩

/-- If both `K` in degrees `≥ n` and its upper truncation in degrees `≥ n + 1` have bounded finite
projective representatives, the degree-`n` cohomology of `K` is finite projective. -/
private lemma finite_projective_homology_of_upper_representative
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (n : ℤ)
    (hK : HasFiniteProjectiveRepresentative.{u, v} K n)
    (hUpper : HasFiniteProjectiveRepresentative.{u, v}
      ((DerivedCategory.TStructure.t.truncGE (n + 1)).obj K) (n + 1)) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K) ∧
      Module.Projective R
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).obj K) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n
  let L := (t.truncLE n).obj K
  let U := (t.truncGE (n + 1)).obj K
  obtain ⟨P, b, hPGE, hPLE, hFin, hProj, ⟨eP⟩⟩ := hK
  obtain ⟨V, c, hVGE, hVLE, _, hVProj, ⟨eV⟩⟩ := hUpper
  have hAmp : HasProjectiveAmplitude.{u, v} U (n + 1) c :=
    ⟨V, ⟨eV.symm⟩, hVProj, hVGE, hVLE⟩
  obtain ⟨e, he⟩ := exists_iso_biprod_truncLE_truncGE K n (n + 1) c rfl hAmp
  let r : K ⟶ L := e.hom ≫ biprod.fst
  have hr : (t.truncLEι n).app K ≫ r = 𝟙 _ := by
    show (t.truncLEι n).app K ≫ (e.hom ≫ biprod.fst) = 𝟙 L
    rw [← Category.assoc, he.1]
    exact biprod.inl_fst
  have : IsIso (H.map ((t.truncLEι n).app K)) := isIso_homology_truncLEι K n n le_rfl
  have : IsIso (H.map ((t.truncLEι n).app K) ≫ H.map r) := by
    rw [← H.map_comp, hr, H.map_id]
    infer_instance
  have : IsIso (H.map r) := IsIso.of_isIso_comp_left (H.map ((t.truncLEι n).app K)) _
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE L n
  let := hPGE
  let := hPLE
  let := hQ
  let (j : ℤ) := hProj j
  let (j : ℤ) := hFin j
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨φ, hφ⟩ := exists_chainMap_of_isKProjective P Q (eP.inv ≫ r ≫ eQ.hom)
  have hmap : IsIso (H.map (DerivedCategory.Q.map φ)) := by
    rw [hφ, H.map_comp, H.map_comp]
    infer_instance
  have : IsIso (HomologicalComplex.homologyMap φ n) :=
    (NatIso.isIso_map_iff
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n) φ).mp hmap
  obtain ⟨hfinite, hprojective⟩ := finite_projective_homology_of_split_at P Q n φ
  let := hfinite
  let := hprojective
  let eH : H.obj K ≅ P.homology n := H.mapIso eP ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) n).app P
  exact finite_projective_of_iso eH.symm

/-- From bounded finite projective representatives of the two adjacent upper truncations, the
degree-`i` cohomology of `K` is finite projective. -/
private lemma finite_projective_homology_of_adjacent_representatives
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ)
    (hPrev : HasFiniteProjectiveRepresentative.{u, v}
      ((DerivedCategory.TStructure.t.truncGE i).obj K) i)
    (hNext : HasFiniteProjectiveRepresentative.{u, v}
      ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj K) (i + 1)) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K) ∧
      Module.Projective R
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i
  have := t.isIso_truncGE_map_truncGEπ_app (i + 1) i (by omega) K
  let e := asIso ((t.truncGE (i + 1)).map ((t.truncGEπ i).app K))
  have hn := hasFiniteProjectiveRepresentative_of_iso e.symm hNext
  obtain ⟨hfinite, hprojective⟩ := finite_projective_homology_of_upper_representative
    ((t.truncGE i).obj K) i hPrev hn
  let := hfinite
  let := hprojective
  have := isIso_homology_truncGEπ K i i le_rfl
  let eH := asIso (H.map ((t.truncGEπ i).app K))
  exact finite_projective_of_iso eH.symm

/-! ### The three-term decomposition -/

/-- A projective module placed in degree `i` has projective amplitude in `[i, i]`. -/
private lemma hasProjectiveAmplitude_single
    {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R)
    [Module.Projective R M] (i : ℤ) :
    HasProjectiveAmplitude.{u, v}
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) i).obj M) i i := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{max u v} R) i).obj M
  refine ⟨P, ⟨((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max u v} R) i).app M).symm⟩,
    ?_, inferInstance, inferInstance⟩
  intro j
  by_cases hj : j = i
  · subst j
    exact Module.Projective.of_equiv'
      (HomologicalComplex.singleObjXSelf (.up ℤ) i M).toLinearEquiv.symm
  · have : Subsingleton (P.X j) := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) i M j hj)
    infer_instance

/-- Transport of projective amplitude along an isomorphism. -/
private lemma hasProjectiveAmplitude_of_iso
    {R : Type u} [CommRing R] {X Y : DerivedCategory (ModuleCat.{max u v} R)}
    (e : X ≅ Y) {a b : ℤ} (h : HasProjectiveAmplitude.{u, v} Y a b) :
    HasProjectiveAmplitude.{u, v} X a b := by
  obtain ⟨P, ⟨eP⟩, hProj, hGE, hLE⟩ := h
  exact ⟨P, ⟨eP ≪≫ e.symm⟩, hProj, hGE, hLE⟩

/-- A morphism from `K` to an object concentrated in degrees `≤ a` vanishes if it vanishes on
`τ_{≤ a} K`, provided `τ_{≥ a'} K` has projective amplitude in `[a', b]`, where `a + 1 = a'`. -/
private lemma eq_zero_of_truncLEι_comp_eq_zero
    {R : Type u} [CommRing R]
    (K M : DerivedCategory (ModuleCat.{max u v} R)) (a a' b : ℤ) (h : a + 1 = a') [M.IsLE a]
    (hU : HasProjectiveAmplitude.{u, v} ((DerivedCategory.TStructure.t.truncGE a').obj K) a' b)
    (f : K ⟶ M) (hf : (DerivedCategory.TStructure.t.truncLEι a).app K ≫ f = 0) : f = 0 := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  obtain ⟨r, hr⟩ := ((t.triangleLEGE a a' h).obj K).yoneda_exact₂
    (t.triangleLEGE_distinguished a a' h K) f hf
  have hr0 : r = 0 := (hom_eq_zero_and_existsUnique_iso_biprod
    M ((t.truncGE a').obj K) a' b hU).1
    (fun j hj => DerivedCategory.isZero_of_isLE M a j (by omega)) r
  exact hr.trans (by rw [hr0, comp_zero])

/-- A morphism from `K` to an object concentrated in degree `i` is determined by its effect on
degree-`i` cohomology, provided the upper truncation of `K` has projective amplitude in
`[i + 1, b]`. -/
private lemma homology_map_injective_of_upper_amplitude
    {R : Type u} [CommRing R]
    (K M : DerivedCategory (ModuleCat.{max u v} R)) (i b : ℤ)
    [M.IsLE i] [M.IsGE i]
    (hU : HasProjectiveAmplitude.{u, v}
      ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj K) (i + 1) b)
    (f : K ⟶ M) (hf : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map f = 0) :
    f = 0 := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i
  let Y := (t.truncLE i).obj K
  let J := (t.truncGE i).obj Y
  let T := (t.triangleLEGE (i - 1) i (by omega)).obj Y
  have hT := t.triangleLEGE_distinguished (i - 1) i (by omega) Y
  have hz : T.mor₁ ≫ ((t.truncLEι i).app K ≫ f) = 0 := by
    show (t.truncLEι (i - 1)).app Y ≫ ((t.truncLEι i).app K ≫ f) = 0
    exact t.zero _ (i - 1) i (by omega)
  obtain ⟨q, hq⟩ := T.yoneda_exact₂ hT ((t.truncLEι i).app K ≫ f) hz
  change J ⟶ M at q
  change (t.truncLEι i).app K ≫ f = (t.truncGEπ i).app Y ≫ q at hq
  have : IsIso (H.map ((t.truncGEπ i).app Y)) := isIso_homology_truncGEπ Y i i le_rfl
  have hq0 : H.map q = 0 := by
    apply (cancel_epi (H.map ((t.truncGEπ i).app Y))).mp
    rw [← H.map_comp, ← hq, H.map_comp, hf]
    simp
  have qzero : q = 0 := hom_eq_zero_of_homology_eq_zero J M i q hq0
  have hy : (t.truncLEι i).app K ≫ f = 0 := by rw [hq, qzero, comp_zero]
  exact eq_zero_of_truncLEι_comp_eq_zero K M i (i + 1) b rfl hU f hy

/-- An object concentrated in degrees `≤ i` with finite projective degree-`i` cohomology splits as
the biproduct of its truncation below `i` and the single complex on that cohomology. -/
private lemma exists_normalized_lower_decomposition
    {R : Type u} [CommRing R]
    (Y : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ) [Y.IsLE i]
    (M : ModuleCat.{max u v} R) [Module.Projective R M]
    (comparison : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj Y ≅ M) :
    ∃ e : Y ≅ (DerivedCategory.TStructure.t.truncLE (i - 1)).obj Y ⊞
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) i).obj M,
      (DerivedCategory.TStructure.t.truncLEι (i - 1)).app Y ≫ e.hom = biprod.inl ∧
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map e.hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map biprod.snd ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} R) i).hom.app M = comparison.hom := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i
  let L := (t.truncLE (i - 1)).obj Y
  let J := (t.truncGE i).obj Y
  have := isIso_homology_truncGEπ Y i i le_rfl
  let cJ : H.obj J ≅ M := (asIso (H.map ((t.truncGEπ i).app Y))).symm ≪≫ comparison
  obtain ⟨eJ, heJ⟩ := exists_iso_single_normalized J i M cJ
  have hAmp := hasProjectiveAmplitude_of_iso eJ (hasProjectiveAmplitude_single.{u, v} M i)
  obtain ⟨eY, heY⟩ := exists_iso_biprod_truncLE_truncGE Y (i - 1) i i (by omega) hAmp
  let e := eY ≪≫ biprod.mapIso (Iso.refl L) eJ
  have hπ : e.hom ≫ biprod.snd = (t.truncGEπ i).app Y ≫ eJ.hom := by
    simp only [e, Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.map_snd]
    rw [← Category.assoc, ← heY.2]
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e, Iso.trans_hom]
    rw [← Category.assoc, heY.1]
    simpa only [biprod.mapIso_hom, biprod.inl_map, Iso.refl_hom] using
      (Category.id_comp (biprod.inl : L ⟶ L ⊞ _))
  · show H.map e.hom ≫ H.map biprod.snd ≫ _ = _
    rw [← Category.assoc, ← H.map_comp, hπ, H.map_comp, Category.assoc, heJ]
    simp [cJ]

/-- If `τ_{≥ i+1} K` has projective amplitude in `[i + 1, b]` and `H^i(K) ≅ M` with `M`
projective, then `K ≅ (τ_{≤ i-1} K ⊕ M[-i]) ⊕ τ_{≥ i+1} K`, compatibly with the truncation maps
and with the given isomorphism on degree-`i` cohomology. -/
private lemma exists_normalized_three_term_decomposition
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (i b : ℤ)
    (hUpper : HasProjectiveAmplitude.{u, v}
      ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj K) (i + 1) b)
    (M : ModuleCat.{max u v} R) [Module.Projective R M]
    (comparison : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K ≅ M) :
    ∃ e : K ≅ ((DerivedCategory.TStructure.t.truncLE (i - 1)).obj K ⊞
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) i).obj M) ⊞
          (DerivedCategory.TStructure.t.truncGE (i + 1)).obj K,
      (DerivedCategory.TStructure.t.truncLEι (i - 1)).app K ≫ e.hom =
          biprod.inl ≫ biprod.inl ∧
      (DerivedCategory.TStructure.t.truncGEπ (i + 1)).app K = e.hom ≫ biprod.snd ∧
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map e.hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map biprod.fst ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map biprod.snd ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} R) i).hom.app M = comparison.hom := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i
  let Y := (t.truncLE i).obj K
  let L := (t.truncLE (i - 1)).obj K
  let U := (t.truncGE (i + 1)).obj K
  obtain ⟨eU, heU⟩ := exists_iso_biprod_truncLE_truncGE K i (i + 1) b rfl hUpper
  have := isIso_homology_truncLEι K i i le_rfl
  let cY : H.obj Y ≅ M := asIso (H.map ((t.truncLEι i).app K)) ≪≫ comparison
  obtain ⟨eY, heY⟩ := exists_normalized_lower_decomposition Y i M cY
  have := t.isIso_truncLE_map_truncLEι_app (i - 1) i (by omega) K
  let eL : (t.truncLE (i - 1)).obj Y ≅ L :=
    asIso ((t.truncLE (i - 1)).map ((t.truncLEι i).app K))
  let eLower := eY ≪≫ biprod.mapIso eL (Iso.refl _)
  let e := eU ≪≫ biprod.mapIso eLower (Iso.refl U)
  have hLnat : eL.hom ≫ (t.truncLEι (i - 1)).app K =
      (t.truncLEι (i - 1)).app Y ≫ (t.truncLEι i).app K :=
    (t.truncLEι (i - 1)).naturality ((t.truncLEι i).app K)
  have hL : (t.truncLEι (i - 1)).app Y ≫ eLower.hom = eL.hom ≫ biprod.inl := by
    dsimp only [eLower, Iso.trans_hom]
    rw [← Category.assoc, heY.1]
    simp
  have hY : (t.truncLEι i).app K ≫ e.hom = eLower.hom ≫ biprod.inl := by
    dsimp only [e, Iso.trans_hom]
    rw [← Category.assoc, heU.1]
    simp
  have hmid : e.hom ≫ biprod.fst ≫ biprod.snd =
      (eU.hom ≫ biprod.fst) ≫ (eY.hom ≫ biprod.snd) := by
    simp [e, eLower, Category.assoc]
  have hr : H.map (eU.hom ≫ biprod.fst) = inv (H.map ((t.truncLEι i).app K)) := by
    apply (cancel_epi (H.map ((t.truncLEι i).app K))).mp
    rw [← H.map_comp, ← Category.assoc, heU.1, biprod.inl_fst, H.map_id]
    simp
  refine ⟨e, ?_, ?_, ?_⟩
  · apply (cancel_epi eL.hom).mp
    rw [← Category.assoc, hLnat, Category.assoc, hY, ← Category.assoc, hL, Category.assoc]
  · show (t.truncGEπ (i + 1)).app K = e.hom ≫ (biprod.snd : _ ⊞ U ⟶ U)
    simp only [e, Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.map_snd,
      Iso.refl_hom]
    rw [Category.comp_id]
    exact heU.2
  · show H.map e.hom ≫ H.map biprod.fst ≫ H.map biprod.snd ≫ _ = _
    calc
      _ = H.map (e.hom ≫ biprod.fst ≫ biprod.snd) ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{max u v} R) i).hom.app M := by
            simp only [H.map_comp, Category.assoc]
      _ = H.map (eU.hom ≫ biprod.fst) ≫
          (H.map eY.hom ≫ H.map biprod.snd ≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{max u v} R) i).hom.app M) := by
              rw [hmid]
              simp only [H.map_comp, Category.assoc]
      _ = H.map (eU.hom ≫ biprod.fst) ≫ cY.hom := by rw [heY.2]
      _ = comparison.hom := by rw [hr]; simp [cY]

/-- Uniqueness of the normalized three-term decomposition. -/
private lemma normalized_three_term_decomposition_unique
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (i a b : ℤ)
    (hPrev : HasProjectiveAmplitude.{u, v}
      ((DerivedCategory.TStructure.t.truncGE i).obj K) i a)
    (hUpper : HasProjectiveAmplitude.{u, v}
      ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj K) (i + 1) b)
    (M : ModuleCat.{max u v} R)
    (comparison : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K ≅ M)
    (e₁ e₂ : K ≅ ((DerivedCategory.TStructure.t.truncLE (i - 1)).obj K ⊞
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) i).obj M) ⊞
          (DerivedCategory.TStructure.t.truncGE (i + 1)).obj K)
    (he₁ : (DerivedCategory.TStructure.t.truncLEι (i - 1)).app K ≫ e₁.hom =
        biprod.inl ≫ biprod.inl ∧
      (DerivedCategory.TStructure.t.truncGEπ (i + 1)).app K = e₁.hom ≫ biprod.snd ∧
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map e₁.hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map biprod.fst ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map biprod.snd ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} R) i).hom.app M = comparison.hom)
    (he₂ : (DerivedCategory.TStructure.t.truncLEι (i - 1)).app K ≫ e₂.hom =
        biprod.inl ≫ biprod.inl ∧
      (DerivedCategory.TStructure.t.truncGEπ (i + 1)).app K = e₂.hom ≫ biprod.snd ∧
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map e₂.hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map biprod.fst ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map biprod.snd ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{max u v} R) i).hom.app M = comparison.hom) : e₁ = e₂ := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i
  let L := (t.truncLE (i - 1)).obj K
  apply Iso.ext
  apply biprod.hom_ext
  · apply biprod.hom_ext
    · apply sub_eq_zero.mp
      refine eq_zero_of_truncLEι_comp_eq_zero K L (i - 1) i a (by omega) hPrev _ ?_
      simp only [t, Preadditive.comp_sub, ← Category.assoc, he₁.1, he₂.1, sub_self]
    · apply sub_eq_zero.mp
      let d : K ⟶ (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) i).obj M :=
        (e₁.hom ≫ biprod.fst) ≫ biprod.snd - (e₂.hom ≫ biprod.fst) ≫ biprod.snd
      let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} R) i).app M
      have hd : H.map d ≫ ε.hom = 0 := by
        simp only [d, H, ε, Iso.app_hom, Functor.map_sub, Functor.map_comp,
          Preadditive.sub_comp, Category.assoc, he₁.2.2, he₂.2.2, sub_self]
      have hd0 : H.map d = 0 := by
        have hh := congrArg (fun z : H.obj K ⟶ M => z ≫ ε.inv) hd
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] using hh
      exact homology_map_injective_of_upper_amplitude.{u, v} K
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) i).obj M) i b hUpper d hd0
  · exact he₁.2.1.symm.trans he₂.2.1

/-- A finite projective module is free after localizing away from some element outside any given
prime ideal. -/
private lemma exists_free_localizedModule_away_of_projective
    {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    (N : Type*) [AddCommGroup N] [Module S N] [Module.Finite S N] [Module.Projective S N] :
    ∃ s ∉ q, Module.Free (Localization.Away s) (LocalizedModule.Away s N) := by
  have : Module.FinitePresentation S N := Module.finitePresentation_of_projective S N
  have : Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl N) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl N) (Localization.AtPrime q)
  exact ⟨r, hr, hfree⟩

/-- A module which is finite projective after localizing away from `f` is finite *free* after
localizing away from a further element outside `p`, in which `f` is still invertible. -/
private lemma exists_finite_free_refinement
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (f : R) (hf : f ∉ p) (N : ModuleCat.{max u v} R)
    [Module.Finite (Localization.Away f)
      ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj N)]
    [Module.Projective (Localization.Away f)
      ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj N)] :
    ∃ g : R, g ∉ p ∧ IsUnit (algebraMap R (Localization.Away g) f) ∧
      Module.Finite (Localization.Away g)
        ((ModuleCat.extendScalars (algebraMap R (Localization.Away g))).obj N) ∧
      Module.Free (Localization.Away g)
        ((ModuleCat.extendScalars (algebraMap R (Localization.Away g))).obj N) := by
  let S := Localization.Away f
  let Nf := S ⊗[R] N
  have : Module.Finite S Nf :=
    Module.Finite.equiv (PseudoCoherence.extendScalarsTensorIso (S := S) N).toLinearEquiv
  have : Module.Projective S Nf :=
    Module.Projective.of_equiv (PseudoCoherence.extendScalarsTensorIso (S := S) N).toLinearEquiv
  let q := p.map (algebraMap R S)
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) S p
    inferInstance ((Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf)
  obtain ⟨s, hs, hfree⟩ := exists_free_localizedModule_away_of_projective q Nf
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f s
  have hap : a ∉ p := by
    intro hap
    have hmem : s * (algebraMap R S f) ^ n ∈ q := by
      rw [ha]
      exact Ideal.mem_map_of_mem (algebraMap R S) hap
    exact (Ideal.IsPrime.mem_or_mem (I := q) inferInstance hmem).elim hs
      (Ideal.notMem_of_isUnit q ((IsLocalization.Away.algebraMap_isUnit f).pow n))
  obtain ⟨hfa, huf, hua⟩ := common_principal_refinement p f a hf hap
  let A := Localization.Away (f * a)
  let φ : S →+* A := IsLocalization.Away.lift f huf
  let : Algebra S A := φ.toAlgebra
  have hcomp : (algebraMap S A).comp (algebraMap R S) = algebraMap R A :=
    IsLocalization.Away.lift_comp f huf
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq
    (fun r => (RingHom.congr_fun hcomp r).symm)
  have hsunit : IsUnit (algebraMap S A s) := by
    have hφ (r : R) : φ (algebraMap R S r) = algebraMap R A r :=
      IsLocalization.Away.lift_eq f huf r
    have h := congrArg φ ha
    simp only [map_mul, map_pow, hφ] at h
    have hh : IsUnit (φ s * (algebraMap R A f) ^ n) := h.symm ▸ hua
    exact (IsUnit.mul_iff.mp hh).1
  let B := Localization.Away s
  let ψ : B →+* A := IsLocalization.Away.lift s hsunit
  let : Algebra B A := ψ.toAlgebra
  have hcomp' : (algebraMap B A).comp (algebraMap S B) = algebraMap S A :=
    IsLocalization.Away.lift_comp s hsunit
  let : IsScalarTower S B A := IsScalarTower.of_algebraMap_eq (R := S) (S := B) (A := A)
    (fun r => (RingHom.congr_fun hcomp' r).symm)
  let := hfree
  have : Module.Free B (B ⊗[S] Nf) := Module.Free.of_equiv
    ((IsLocalizedModule.iso (Submonoid.powers s)
      ((TensorProduct.mk S B Nf) 1)).extendScalarsOfIsLocalization (Submonoid.powers s) B)
  let e₁ : A ⊗[B] (B ⊗[S] Nf) ≃ₗ[A] A ⊗[S] Nf :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S B A A Nf
  let e₂ : A ⊗[S] Nf ≃ₗ[A] A ⊗[R] N :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A N
  let e₃ := (PseudoCoherence.extendScalarsTensorIso (S := A) N).toLinearEquiv.symm
  exact ⟨f * a, hfa, huf, Module.Finite.equiv (e₂.trans e₃),
    Module.Free.of_equiv ((e₁.trans e₂).trans e₃)⟩

/-! ### The three-term splitting -/

/-- Let `R` be a ring, `p ⊂ R` a prime and `K` a pseudo-coherent object of
`D(R)`. If for some `i ∈ ℤ` both maps `H^i(K) ⊗_R κ(p) → H^i(K ⊗_R^L κ(p))` and
`H^{i-1}(K) ⊗_R κ(p) → H^{i-1}(K ⊗_R^L κ(p))` are surjective, then there is `f ∈ R`, `f ∉ p`,
such that

1. `τ_{≥ i+1}(K ⊗_R R_f)` is a perfect object of `D(R_f)` with Tor amplitude in `[i + 1, ∞]`,
2. `H^i(K)_f` is a finite free `R_f`-module, and
3. there is a canonical direct sum decomposition
   `K ⊗_R R_f ≅ τ_{≤ i-1}(K ⊗_R R_f) ⊕ H^i(K)_f[-i] ⊕ τ_{≥ i+1}(K ⊗_R R_f)` in `D(R_f)`. -/
@[stacks 0A1V]
theorem exists_localization_finite_free_homology_and_iso_biprod
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hbase_i : CohomologyBaseChangeSurjective.{u, v} p K i)
    (hbase_prev : CohomologyBaseChangeSurjective.{u, v} p K (i - 1)) :
    ∃ f : R, f ∉ p ∧
      let Rf := Localization.Away f
      let Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K
      let upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf
      let lower := (DerivedCategory.TStructure.t.truncLE (i - 1)).obj Kf
      let HiLocalized :=
        (ModuleCat.extendScalars (algebraMap R Rf)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)
      let middle :=
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} Rf) i).obj HiLocalized
      let comparison := (localizationAwayHomologyFunctorIso.{u, v} f i).app K
      IsPerfect upper ∧
        (∃ (P : CochainComplex (ModuleCat.{max u v} Rf) ℤ) (b : ℤ),
          P.IsStrictlyGE (i + 1) ∧ P.IsStrictlyLE b ∧
            (∀ j : ℤ, Module.Finite Rf (P.X j)) ∧
            (∀ j : ℤ, Module.Projective Rf (P.X j)) ∧
            Nonempty (upper ≅ DerivedCategory.Q.obj P) ∧
            ∀ (M : ModuleCat.{max u v} Rf) (j : ℤ), j < i + 1 →
              IsZero ((TorAmplitude.tensorComplex P M).homology j)) ∧
        Module.Finite Rf HiLocalized ∧ Module.Free Rf HiLocalized ∧
        ∃! e : Kf ≅ (lower ⊞ middle) ⊞ upper,
          (DerivedCategory.TStructure.t.truncLEι (i - 1)).app Kf ≫ e.hom =
              biprod.inl ≫ biprod.inl ∧
            (DerivedCategory.TStructure.t.truncGEπ (i + 1)).app Kf =
              e.hom ≫ biprod.snd ∧
            (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Rf) i).map e.hom ≫
                (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Rf) i).map biprod.fst ≫
                (DerivedCategory.homologyFunctor (ModuleCat.{max u v} Rf) i).map biprod.snd ≫
                (DerivedCategory.singleFunctorCompHomologyFunctorIso
                  (ModuleCat.{max u v} Rf) i).hom.app HiLocalized = comparison.hom := by
  obtain ⟨f, hf, hPrev, hNext⟩ :=
    exists_adjacent_upper_representatives p K hK i hbase_i hbase_prev
  let H₀ := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K
  let Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K
  let Hf := (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj H₀
  obtain ⟨hfinite, hprojective⟩ :=
    finite_projective_homology_of_adjacent_representatives Kf i hPrev hNext
  let := hfinite
  let := hprojective
  let cf : (DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (Localization.Away f)) i).obj Kf ≅ Hf :=
    (localizationAwayHomologyFunctorIso.{u, v} f i).app K
  obtain ⟨hHfin, hHproj⟩ := finite_projective_of_iso cf
  obtain ⟨g, hg, huf, hgfinite, hgfree⟩ := exists_finite_free_refinement p f hf H₀
  have hPrev' := upper_representative_after_localization f g huf K i hPrev
  have hNext' := upper_representative_after_localization f g huf K (i + 1) hNext
  obtain ⟨P₀, b₀, hGE₀, hLE₀, _, hProj₀, ⟨e₀⟩⟩ := hPrev'
  obtain ⟨P, b, hGE, hLE, hFin, hProj, ⟨eP⟩⟩ := hNext'
  let Kg := (PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K
  let M := (ModuleCat.extendScalars (algebraMap R (Localization.Away g))).obj H₀
  let := hgfinite
  let := hgfree
  have : Module.Projective (Localization.Away g) M := Module.Projective.of_free
  have hAmpPrev : HasProjectiveAmplitude.{u, v}
      ((DerivedCategory.TStructure.t.truncGE i).obj Kg) i b₀ :=
    ⟨P₀, ⟨e₀.symm⟩, hProj₀, hGE₀, hLE₀⟩
  have hAmp : HasProjectiveAmplitude.{u, v}
      ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kg) (i + 1) b :=
    ⟨P, ⟨eP.symm⟩, hProj, hGE, hLE⟩
  let cg : (DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (Localization.Away g)) i).obj Kg ≅ M :=
    (localizationAwayHomologyFunctorIso.{u, v} g i).app K
  obtain ⟨e, he⟩ := exists_normalized_three_term_decomposition Kg i b hAmp M cg
  refine ⟨g, hg, ⟨P, i + 1, b, hGE, hLE, hFin, hProj, ⟨eP⟩⟩,
    ⟨P, b, hGE, hLE, hFin, hProj, ⟨eP⟩, ?_⟩, hgfinite, hgfree, e, he, ?_⟩
  · exact fun N j hj => isZero_tensorComplex_homology_of_isStrictlyGE P (i + 1) hGE N j hj
  · intro e' he'
    exact normalized_three_term_decomposition_unique Kg i b₀ b hAmpPrev hAmp M cg e' e he' he

end StacksDraft.Perfect

end
