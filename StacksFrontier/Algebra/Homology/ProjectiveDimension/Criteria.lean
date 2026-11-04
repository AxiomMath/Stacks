module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.ProjectiveDimension.Amplitude
public import StacksFrontier.RingTheory.Module.Projective.Characterization
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Detecting projective amplitude by Ext vanishing

For an object of the derived category of modules, having projective amplitude in a fixed
integer interval is equivalent to several progressively smaller collections of cohomology and
Ext vanishing conditions: vanishing of `Ext^i(K, N)` for every module `N` and every `i` outside
`[-b, -a]`, or upper cohomology vanishing together with Ext vanishing above degree `-a`, or
cohomology vanishing outside `[a - 1, b]` together with vanishing of the single Ext degree
`-a + 1`.

## Main definitions

There are no new definitions.

## Main results

* `StacksDraft.ProjectiveDimension.hasProjectiveAmplitude_iff_ext_vanishing` characterizes
  projective amplitude in `[a, b]` by three equivalent cohomology and Ext vanishing criteria.

## Implementation notes

An `R`-module in an Ext group is regarded as the corresponding object of the derived category
concentrated in degree zero. Vanishing of an Ext group is expressed by its underlying type being
a subsingleton.

## References

* [Stacks Project, Tag 0A5P](https://stacks.math.columbia.edu/tag/0A5P)
-/

open CategoryTheory Limits

namespace StacksDraft.ProjectiveDimension

universe w v u

variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]

omit [HasDerivedCategory.{w} (ModuleCat.{v} R)] in
/-- A map of complexes with disjoint supports vanishes. -/
public lemma hom_eq_zero_of_strictly_disjoint
    {P L : CochainComplex (ModuleCat.{v} R) ℤ} {a b : ℤ}
    [P.IsStrictlyGE a] [L.IsStrictlyLE b] (h : b < a)
    (f : P ⟶ L) : f = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i < a
  · exact (P.isZero_of_isStrictlyGE a i hi).eq_of_src _ _
  · exact (L.isZero_of_isStrictlyLE b i (by omega)).eq_of_tgt _ _

/-- A projective complex supported in `[a, b]` is K-projective, so morphisms out of it in the
derived category to a complex supported in degrees `≤ a - 1` are computed by maps of complexes,
and those vanish. -/
public lemma subsingleton_hom_of_projective_strictly_disjoint
    {P L : CochainComplex (ModuleCat.{v} R) ℤ} {a b : ℤ}
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] [L.IsStrictlyLE (a - 1)]
    [∀ i, CategoryTheory.Projective (P.X i)] :
    Subsingleton (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) := by
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let Qh := DerivedCategory.Qh (C := ModuleCat.{v} R)
  let H := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)
  suffices ∀ f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L, f = 0 from
    subsingleton_of_forall_eq 0 this
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (H.obj L)).surjective
    ((e.app P).hom ≫ f ≫ (e.app L).inv)
  obtain ⟨g', rfl⟩ := H.map_surjective g
  have hg' : g' = 0 := hom_eq_zero_of_strictly_disjoint (a := a) (b := a - 1)
    (by omega) g'
  subst g'
  simp only [Functor.map_zero] at hg
  rw [← cancel_epi (e.app P).hom, ← cancel_mono (e.app L).inv]
  simpa only [Category.assoc, comp_zero, zero_comp] using hg.symm

/-- Ext vanishing into a module follows from vanishing of maps from a representative to the
shifted module. -/
private lemma subsingleton_ext_of_subsingleton_hom_shift
    {K : DerivedCategory (ModuleCat.{v} R)} {P : CochainComplex (ModuleCat.{v} R) ℤ}
    (e : DerivedCategory.Q.obj P ≅ K) (N : ModuleCat.{v} R) (i : ℤ)
    (hs : Subsingleton (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj
      (((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦i⟧))) :
    Subsingleton (DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i) := by
  let S := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N
  let eN : ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦i⟧ ≅
      DerivedCategory.Q.obj (S⟦i⟧) :=
    ((shiftFunctor (DerivedCategory (ModuleCat.{v} R)) i).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) 0).app N)) ≪≫
      ((DerivedCategory.Q (C := ModuleCat.{v} R)).commShiftIso i).symm.app S
  change Subsingleton (K ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦i⟧)
  exact Equiv.subsingleton (Iso.homCongr e.symm eN)

/-- **[stacks 0A5P], (1) implies (2).** Projective amplitude in `[a, b]` makes every Ext group
outside the degrees `[-b, -a]` vanish. -/
public lemma ext_vanishes_of_hasProjectiveAmplitude
    {K : DerivedCategory (ModuleCat.{v} R)} {a b : ℤ}
    (h : HasProjectiveAmplitude K a b)
    (N : ModuleCat.{v} R) (i : ℤ) (hi : i ∉ Set.Icc (-b) (-a)) :
    Subsingleton (DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i) := by
  obtain ⟨P, ⟨e⟩, hproj, hGE, hLE⟩ := h
  let S := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N
  let L := S⟦i⟧
  have : P.IsStrictlyGE a := hGE
  have : P.IsStrictlyLE b := hLE
  have : ∀ j, CategoryTheory.Projective (P.X j) := by
    intro j
    let : Module.Projective R (P.X j) := hproj j
    exact (P.X j).projective_of_categoryTheory_projective
  refine subsingleton_ext_of_subsingleton_hom_shift e N i ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · have : L.IsStrictlyGE (-i) :=
      CochainComplex.isStrictlyGE_shift S 0 i (-i) (by omega)
    exact DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE P L
      b (-i) (by omega)
  · have : L.IsStrictlyLE (a - 1) := by
      let : L.IsStrictlyLE (-i) :=
        CochainComplex.isStrictlyLE_shift S 0 i (-i) (by omega)
      exact CochainComplex.isStrictlyLE_of_le L (-i) (a - 1) (by omega)
    exact subsingleton_hom_of_projective_strictly_disjoint
      (P := P) (L := L) (a := a) (b := b)

/-- If every morphism in the derived category from a complex `P` to a module placed in degree `n`
vanishes, then `H^n(P) = 0`: embed `H^n(P)` into an injective module `I` and factor the resulting
map through `P^n`, producing a map of complexes whose degree-`n` homology map is the embedding. -/
public lemma isZero_homology_of_subsingleton_hom_single [Small.{v} R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    (h : ∀ I : ModuleCat.{v} R, Subsingleton
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) n).obj I))) :
    IsZero (P.homology n) := by
  let I := Injective.under (P.homology n)
  let ι : P.homology n ⟶ I := Injective.ι _
  let f : P.X n ⟶ I := Injective.factorThru (P.homologyπ n ≫ ι) (P.iCycles n)
  have hf : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i n → P.d i n ≫ f = 0 := by
    intro i hi
    rw [← P.toCycles_i i n, Category.assoc,
      show P.iCycles n ≫ f = P.homologyπ n ≫ ι from Injective.comp_factorThru _ _]
    rw [← Category.assoc, P.toCycles_comp_homologyπ, zero_comp]
  let φ := HomologicalComplex.mkHomToSingle f hf
  have hφ : DerivedCategory.Q.map φ = 0 := (h I).elim _ _
  have hHφ : HomologicalComplex.homologyMap φ n = 0 := by
    have hh := DerivedCategory.homologyFunctorFactors_hom_naturality φ n
    rw [hφ, Functor.map_zero, zero_comp] at hh
    have hcomp : ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).hom.app P) ≫
        HomologicalComplex.homologyMap φ n = 0 := hh.symm
    exact (cancel_epi ((DerivedCategory.homologyFunctorFactors _ n).hom.app P)).mp
      (hcomp.trans comp_zero.symm)
  let S := (HomologicalComplex.single (ModuleCat.{v} R) (ComplexShape.up ℤ) n).obj I
  have hs : S.homologyπ n ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n I).hom =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n I).hom :=
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom _ _ _
  have hmap : HomologicalComplex.homologyMap φ n ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n I).hom = ι := by
    rw [← cancel_epi (P.homologyπ n)]
    calc
      P.homologyπ n ≫ (HomologicalComplex.homologyMap φ n ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n I).hom) =
          P.cyclesMap φ n ≫ (S.homologyπ n ≫
            (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n I).hom) := by
              simpa only [Category.assoc] using
                congrArg (· ≫ (HomologicalComplex.singleObjHomologySelfIso
                  (ComplexShape.up ℤ) n I).hom) (HomologicalComplex.homologyπ_naturality φ n)
      _ = P.cyclesMap φ n ≫
          (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n I).hom := by rw [hs]
      _ = P.iCycles n ≫ f := by
          rw [HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
            HomologicalComplex.cyclesMap_i, Category.assoc, HomologicalComplex.mkHomToSingle_f]
          simp
      _ = P.homologyπ n ≫ ι := Injective.comp_factorThru _ _
  have hι : ι = 0 := by
    rw [← hmap, hHφ]
    simp
  rw [IsZero.iff_id_eq_zero, ← cancel_mono ι]
  simp [hι]

/-- Ext vanishing from `K` into a module in degree `i` gives vanishing of maps from a
representative of `K` to the module placed in degree `n`, when `i + n = 0`. -/
private lemma subsingleton_hom_single_of_subsingleton_ext
    {K : DerivedCategory (ModuleCat.{v} R)} {P : CochainComplex (ModuleCat.{v} R) ℤ}
    (e : DerivedCategory.Q.obj P ≅ K) (N : ModuleCat.{v} R) (n i : ℤ) (hni : i + n = 0)
    (h : Subsingleton (DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) :
    Subsingleton (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) n).obj N)) := by
  let eN : ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦i⟧ ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{v} R) n).obj N) :=
    ((DerivedCategory.singleFunctors (ModuleCat.{v} R)).shiftIso i n 0 hni).app N ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} R) n).app N)
  have : Subsingleton (K ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦i⟧) := h
  exact Equiv.subsingleton (Iso.homCongr e eN.symm)

/-- Vanishing of `Ext^{-n}(K, I)` for every module `I` forces `H^n(K) = 0`. -/
public lemma isZero_homology_of_ext_subsingleton [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (n : ℤ)
    (h : ∀ I : ModuleCat.{v} R,
      Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj I) (-n))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K) := by
  let P := (DerivedCategory.Q (C := ModuleCat.{v} R)).objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K :=
    (DerivedCategory.Q (C := ModuleCat.{v} R)).objObjPreimageIso K
  exact (isZero_homology_of_subsingleton_hom_single P n fun I =>
    subsingleton_hom_single_of_subsingleton_ext eK I n (-n) (by omega) (h I)).of_iso
    (((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso eK).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app P)

/-- **[stacks 0A5P], (2) implies (3).** -/
public lemma upperVanishing_of_extOutsideVanishes [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (h : ∀ (N : ModuleCat.{v} R) (i : ℤ),
      i ∉ Set.Icc (-b) (-a) →
        Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) :
    (∀ n : ℤ, b < n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
      ∀ (N : ModuleCat.{v} R) (i : ℤ), -a < i →
        Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i) := by
  constructor
  · intro n hn
    apply isZero_homology_of_ext_subsingleton K n
    intro I
    exact h I (-n) (by simp only [Set.mem_Icc, not_and_or, not_le]; left; omega)
  · intro N i hi
    exact h N i (by simp only [Set.mem_Icc, not_and_or, not_le]; right; omega)

/-- **[stacks 0A5P], (3) implies (4).** -/
public lemma endpointVanishing_of_upperVanishing [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (h : (∀ n : ℤ, b < n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
      ∀ (N : ModuleCat.{v} R) (i : ℤ), -a < i →
        Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i)) :
    (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
      ∀ N : ModuleCat.{v} R,
        Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) (-a + 1)) := by
  constructor
  · intro n hn
    simp only [Set.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · apply isZero_homology_of_ext_subsingleton K n
      intro I
      exact h.2 I (-n) (by omega)
    · exact h.1 n hn
  · intro N
    exact h.2 N (-a + 1) (by omega)

/-- The endpoint criterion gives cohomology vanishing outside `[a, b]`. -/
public lemma homologyVanishing_of_endpointVanishing [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (h : (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
      ∀ N : ModuleCat.{v} R,
        Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) (-a + 1))) :
    (∀ n : ℤ, n < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
      ∀ n : ℤ, b < n →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K) := by
  constructor
  · intro n hn
    by_cases heq : n = a - 1
    · subst n
      apply isZero_homology_of_ext_subsingleton K (a - 1)
      simpa only [show -(a - 1) = -a + 1 by omega] using h.2
    · exact h.1 n (by simp only [Set.mem_Icc, not_and_or, not_le]; left; omega)
  · intro n hn
    exact h.1 n (by simp only [Set.mem_Icc, not_and_or, not_le]; right; omega)

/-- A bounded above object of `D(R)` has a projective representative vanishing strictly above the
same degree. -/
public lemma exists_projective_representative_boundedAbove [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (b : ℤ) [K.IsLE b] :
    ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
        (∀ i : ℤ, Module.Projective R (P.X i)) ∧ P.IsStrictlyLE b := by
  let P₀ := (DerivedCategory.Q (C := ModuleCat.{v} R)).objPreimage K
  have : P₀.IsLE b := by
    let e : DerivedCategory.Q.obj P₀ ≅ K :=
      (DerivedCategory.Q (C := ModuleCat.{v} R)).objObjPreimageIso K
    exact (DerivedCategory.isLE_Q_obj_iff P₀ b).mp <| (DerivedCategory.isLE_iff _ _).2
      fun i hi => ((DerivedCategory.isLE_iff K b).mp ‹K.IsLE b› i hi).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)
  let : (CategoryTheory.isProjective (ModuleCat.{v} R)).ContainsZero :=
    ⟨⟨(ModuleCat.of R PUnit : ModuleCat.{v} R), ModuleCat.isZero_of_subsingleton _,
      Limits.IsZero.projective (ModuleCat.isZero_of_subsingleton _)⟩⟩
  let hpr (X : ModuleCat.{v} R) :
      ∃ (Y : ModuleCat.{v} R) (_ : CategoryTheory.Projective Y) (p : Y ⟶ X), Epi p := by
    let Y := CategoryTheory.Projective.over X
    exact ⟨Y, inferInstance, CategoryTheory.Projective.π X, inferInstance⟩
  obtain ⟨P, f, hq, hproj, hLE⟩ :=
    (CochainComplex.exists_quasiIso_prop
      (CategoryTheory.isProjective (ModuleCat.{v} R)) hpr b).2 P₀
  have : QuasiIso f := hq
  refine ⟨P, ⟨(asIso (DerivedCategory.Q.map f)) ≪≫
      (DerivedCategory.Q (C := ModuleCat.{v} R)).objObjPreimageIso K⟩, ?_, hLE⟩
  intro i
  exact (IsProjective.iff_projective (P.X i)).mpr (hproj i)

/-- Vanishing of every map in the derived category from a projective complex supported in degrees
`≤ b` to a module placed in degree `a - 1` makes the degree-`a` opcycles projective: a lift is
built from a null-homotopy of the map of complexes detecting the obstruction. -/
public lemma opcycles_projective_of_ext_endpoint [Small.{v} R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    [P.IsStrictlyLE b] [∀ i, CategoryTheory.Projective (P.X i)]
    (h : ∀ N : ModuleCat.{v} R, Subsingleton
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{v} R) (a - 1)).obj N))) :
    CategoryTheory.Projective (P.opcycles a) := by
  let : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  refine ⟨fun {E X} f e _ => ?_⟩
  obtain ⟨g, hg⟩ := CategoryTheory.Projective.factors (P.pOpcycles a ≫ f) e
  let N := kernel e
  have hdg : P.d (a - 1) a ≫ g ≫ e = 0 := by
    rw [hg, ← Category.assoc, P.d_pOpcycles]
    simp
  let φ₀ : P.X (a - 1) ⟶ N := kernel.lift e (P.d (a - 1) a ≫ g) hdg
  have hφ₀ : ∀ i, (ComplexShape.up ℤ).Rel i (a - 1) → P.d i (a - 1) ≫ φ₀ = 0 := by
    intro i hi
    apply (cancel_mono (kernel.ι e)).mp
    simp [φ₀, Category.assoc]
  let S := (CochainComplex.singleFunctor (ModuleCat.{v} R) (a - 1)).obj N
  let φ : P ⟶ S := HomologicalComplex.mkHomToSingle φ₀ hφ₀
  have hQφ : DerivedCategory.Q.map φ = 0 := (h N).elim _ _
  let H := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let η := DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)
  have hHφ : H.map φ = 0 := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective P (H.obj S)).injective
    apply (cancel_mono (η.hom.app S)).mp
    simpa only [Functor.comp_map, Functor.map_zero, zero_comp, comp_zero, hQφ] using
      (η.hom.naturality φ)
  obtain ⟨τ⟩ := (HomotopyCategory.quotient_map_eq_zero_iff φ).mp hHφ
  let t : P.X a ⟶ N := τ.hom a (a - 1) ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (a - 1) N).hom
  have ht : P.d (a - 1) a ≫ t = φ₀ := by
    have hprev : prevD (a - 1) τ.hom = 0 := by
      rw [prevD_eq τ.hom (show (ComplexShape.up ℤ).Rel (a - 2) (a - 1) by
        simp; omega)]
      simp [S]
    have hc := τ.comm (a - 1)
    simp only [hprev, HomologicalComplex.zero_f, add_zero] at hc
    rw [dNext_eq τ.hom (show (ComplexShape.up ℤ).Rel (a - 1) a by simp)] at hc
    calc
      P.d (a - 1) a ≫ t =
          (P.d (a - 1) a ≫ τ.hom a (a - 1)) ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (a - 1) N).hom := by
              simp [t, Category.assoc]
      _ = φ.f (a - 1) ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (a - 1) N).hom := by
              rw [hc]
      _ = φ₀ := by simp [φ, HomologicalComplex.mkHomToSingle_f]
  let g' : P.X a ⟶ E := g - t ≫ kernel.ι e
  have hg' : P.d (a - 1) a ≫ g' = 0 := by
    calc
      P.d (a - 1) a ≫ g' = P.d (a - 1) a ≫ g -
          (P.d (a - 1) a ≫ t) ≫ kernel.ι e := by simp [g', Category.assoc]
      _ = 0 := by rw [ht, kernel.lift_ι, sub_self]
  let lift : P.opcycles a ⟶ E := P.descOpcycles g' (a - 1) (by simp) hg'
  refine ⟨lift, ?_⟩
  apply (cancel_epi (P.pOpcycles a)).mp
  calc
    P.pOpcycles a ≫ lift ≫ e = g' ≫ e := by
      simp only [lift, ← Category.assoc, P.p_descOpcycles]
    _ = g ≫ e := by simp [g', Category.assoc]
    _ = P.pOpcycles a ≫ f := hg

/-- The Ext form of `opcycles_projective_of_ext_endpoint`. -/
public lemma opcycles_projective_of_ext_subsingleton [Small.{v} R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (K : DerivedCategory (ModuleCat.{v} R)) (e : DerivedCategory.Q.obj P ≅ K)
    (a b : ℤ) [P.IsStrictlyLE b] [∀ i, CategoryTheory.Projective (P.X i)]
    (h : ∀ N : ModuleCat.{v} R,
      Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) (-a + 1))) :
    CategoryTheory.Projective (P.opcycles a) := by
  apply opcycles_projective_of_ext_endpoint P a b
  intro N
  exact subsingleton_hom_single_of_subsingleton_ext e N (a - 1) (-a + 1) (by omega) (h N)

/-- **[stacks 0A5P], (4) implies (1).** -/
public lemma hasProjectiveAmplitude_of_endpointVanishing [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (hcoh : (∀ n : ℤ, n < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
      ∀ n : ℤ, b < n →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K))
    (hext : ∀ N : ModuleCat.{v} R,
      Subsingleton (DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) (-a + 1))) :
    HasProjectiveAmplitude K a b := by
  have : K.IsLE b := (DerivedCategory.isLE_iff K b).2 hcoh.2
  have : K.IsGE a := (DerivedCategory.isGE_iff K a).2 hcoh.1
  obtain ⟨P, ⟨e⟩, hproj, hLE⟩ := exists_projective_representative_boundedAbove K b
  have : P.IsStrictlyLE b := hLE
  have : ∀ i, CategoryTheory.Projective (P.X i) := by
    intro i
    let : Module.Projective R (P.X i) := hproj i
    exact (P.X i).projective_of_categoryTheory_projective
  have hQGE : (DerivedCategory.Q.obj P).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have hPGE : P.IsGE a := (DerivedCategory.isGE_Q_obj_iff P a).mp hQGE
  have : QuasiIso (P.πTruncGE a) := (P.quasiIso_πTruncGE_iff a).2 hPGE
  let T := P.truncGE a
  have : T.IsStrictlyGE a := inferInstance
  have : T.IsStrictlyLE b := inferInstance
  have hQproj : CategoryTheory.Projective (P.opcycles a) :=
    opcycles_projective_of_ext_subsingleton P K e a b hext
  refine ⟨T, ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ e⟩,
    fun i => ?_, inferInstance, inferInstance⟩
  have hcat : CategoryTheory.Projective (T.X i) := by
    rcases lt_trichotomy i a with hi | hi | hi
    · exact Limits.IsZero.projective (T.isZero_of_isStrictlyGE a i hi)
    · subst i
      exact CategoryTheory.Projective.of_iso (P.truncGEXIsoOpcycles a).symm hQproj
    · exact CategoryTheory.Projective.of_iso (P.truncGEXIso a i hi).symm
        (inferInstance : CategoryTheory.Projective (P.X i))
  exact (IsProjective.iff_projective (T.X i)).mpr hcat

/-- **[stacks 0A5P], (3) implies (2).** -/
public lemma extOutsideVanishes_of_upperVanishing [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ)
    (h : (∀ n : ℤ, b < n →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
      ∀ (N : ModuleCat.{v} R) (i : ℤ), -a < i →
        Subsingleton (DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i))
    (N : ModuleCat.{v} R) (i : ℤ) (hi : i ∉ Set.Icc (-b) (-a)) :
    Subsingleton (DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) i) := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hlo | hhi
  · have : K.IsLE b := (DerivedCategory.isLE_iff K b).2 h.1
    obtain ⟨P, ⟨e⟩, _, hLE⟩ := exists_projective_representative_boundedAbove K b
    let S := (CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N
    have : P.IsStrictlyLE b := hLE
    have : (S⟦i⟧).IsStrictlyGE (-i) :=
      CochainComplex.isStrictlyGE_shift S 0 i (-i) (by omega)
    exact subsingleton_ext_of_subsingleton_hom_shift e N i
      (DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE P (S⟦i⟧) b (-i)
        (by omega))
  · exact h.2 N i hhi

/-- **Stacks 0A5P.** Projective amplitude in `[a, b]` is equivalent to vanishing of all Ext
groups outside degrees `[-b, -a]`; equivalently, it can be detected using upper cohomology
vanishing and Ext groups above degree `-a`, or using cohomology outside `[a - 1, b]` and the
single Ext degree `-a + 1`. -/
@[stacks 0A5P]
public theorem hasProjectiveAmplitude_iff_ext_vanishing [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) :
    let moduleObject := fun N : ModuleCat.{v} R ↦
      (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N
    let projectiveAmplitude := HasProjectiveAmplitude K a b
    let extOutsideVanishes := ∀ (N : ModuleCat.{v} R) (i : ℤ),
      i ∉ Set.Icc (-b) (-a) → Subsingleton (DerivedCategory.Ext K (moduleObject N) i)
    let upperVanishing :=
      (∀ n : ℤ, b < n → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
        ∀ (N : ModuleCat.{v} R) (i : ℤ), -a < i →
          Subsingleton (DerivedCategory.Ext K (moduleObject N) i)
    let endpointVanishing :=
      (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).obj K)) ∧
        ∀ N : ModuleCat.{v} R,
          Subsingleton (DerivedCategory.Ext K (moduleObject N) (-a + 1))
    (projectiveAmplitude ↔ extOutsideVanishes) ∧
      (extOutsideVanishes ↔ upperVanishing) ∧
      (upperVanishing ↔ endpointVanishing) := by
  dsimp
  refine ⟨⟨fun h N i hi => ext_vanishes_of_hasProjectiveAmplitude h N i hi, fun h => ?_⟩,
    ⟨upperVanishing_of_extOutsideVanishes K a b, extOutsideVanishes_of_upperVanishing K a b⟩,
    ⟨endpointVanishing_of_upperVanishing K a b, fun hend => ?_⟩⟩
  · have hend :=
      endpointVanishing_of_upperVanishing K a b (upperVanishing_of_extOutsideVanishes K a b h)
    exact hasProjectiveAmplitude_of_endpointVanishing K a b
      (homologyVanishing_of_endpointVanishing K a b hend) hend.2
  · -- This follows after recovering projective amplitude from the endpoint criterion.
    have hproj := hasProjectiveAmplitude_of_endpointVanishing K a b
      (homologyVanishing_of_endpointVanishing K a b hend) hend.2
    exact upperVanishing_of_extOutsideVanishes K a b
      fun N i hi => ext_vanishes_of_hasProjectiveAmplitude hproj N i hi

end StacksDraft.ProjectiveDimension
