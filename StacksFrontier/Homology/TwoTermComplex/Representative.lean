module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TwoTermComplex.Ext

@[expose] public section

/-!
# Two-term representatives in the derived category

An object of the derived category of modules whose cohomology is concentrated in degrees `-1`
and `0` admits a two-term representative with free degree-zero term. Over a Noetherian ring,
finite cohomology in those degrees permits the representative to be chosen finite in degree
`-1` and finite free in degree `0`.

Having such a representative at hand turns ideal annihilation of the first Ext groups of the
object into a concrete factorization property of the degree-minus-one differential of the
representative.

## Main results

* `TwoTermComplex.exists_twoTerm_representative_free_zero_and_finite` (Stacks 0G9E).
* `TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization` (Stacks 0G9F).

## Implementation notes

A two-term representative is a cochain complex strictly supported between degrees `-1` and
`0`. Representation of a derived object is expressed by an isomorphism after applying the
localization functor to the complex. The smallness hypothesis places free representatives in
the universe of the given derived category; it is automatic when the ring and its modules are
taken in the same universe.

The free case truncates a degree-wise free resolution, produced by
`CochainComplex.exists_quasiIso_prop` (Stacks 05T7). The finite case goes through
pseudo-coherence: over a Noetherian ring bounded-above finite cohomology is exactly
pseudo-coherence (`StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology`,
Stacks 066E), and a pseudo-coherent object has a finite free representative with a prescribed
upper bound (`StacksDraft.PseudoCoherence.exists_finiteFree_representative_le`, Stacks 064U).

For the factorization criterion an `R`-module in the second argument of Ext is regarded as a
derived object concentrated in degree zero, and the criterion itself is the two-term
Hom-comparison of `TwoTermComplexExt.toHomD_bijective` and
`TwoTermComplexExt.forall_Q_map_comp_eq_zero_iff` (Stacks 0ALN, parts (1) and (2)) applied to
multiplication by a scalar on the representative. The word "ring" follows the Stacks Project
convention that rings are commutative.

## References

* [Stacks Project, Tag 0G9E](https://stacks.math.columbia.edu/tag/0G9E)
* [Stacks Project, Tag 0G9F](https://stacks.math.columbia.edu/tag/0G9F)
-/

open CategoryTheory CategoryTheory.Limits

namespace TwoTermComplex

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- Every module is covered by a free module in the same universe, provided the ring is small
enough to fit there. -/
private lemma exists_free_cover {R : Type u} [Ring R] [Small.{v} R]
    (X : ModuleCat.{v} R) :
    ∃ (Y : ModuleCat.{v} R) (_ : Module.Free R Y) (p : Y ⟶ X), Epi p := by
  let e : Module.Basis X R (X →₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
  refine ⟨ModuleCat.of R (X →₀ Shrink.{v} R), Module.Free.of_basis e,
    ModuleCat.ofHom (e.constr ℕ _root_.id), ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  intro x
  exact ⟨Finsupp.single x 1, by simp [e, Module.Basis.constr_apply]⟩

/-- A zero module is finite. -/
private lemma finite_of_isZero {R : Type u} [Ring R] (X : ModuleCat.{v} R)
    (hX : IsZero X) : Module.Finite R X := by
  have : Subsingleton X := ModuleCat.subsingleton_of_isZero hX
  infer_instance

/-- Truncating a representative `P` of `K` below degree `-1` gives a two-term representative. -/
private lemma truncGE_representative {R : Type u} [Ring R] [Small.{v} R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (K : DerivedCategory (ModuleCat.{v} R))
    [P.IsStrictlyLE 0] [K.IsGE (-1)] (e : DerivedCategory.Q.obj P ≅ K) :
    (P.truncGE (-1)).IsStrictlyGE (-1) ∧ (P.truncGE (-1)).IsStrictlyLE 0 ∧
      Nonempty (DerivedCategory.Q.obj (P.truncGE (-1)) ≅ K) := by
  have : P.IsGE (-1) := (DerivedCategory.isGE_Q_obj_iff P (-1)).1
    (DerivedCategory.TStructure.t.isGE_of_iso e.symm (-1))
  refine ⟨inferInstance, ?_, ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE (-1)))).symm ≪≫ e⟩⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (P.isZero_of_isStrictlyLE 0 i hi).of_iso (P.truncGEXIso (-1) i)

/-- **Stacks 0G9E.** A derived object with cohomology only in degrees `-1` and `0` has a
two-term representative whose degree-zero term is free. If the ring is Noetherian and both
cohomology modules are finite, it also has such a representative with finite degree-minus-one
term and finite free degree-zero term. -/
@[stacks 0G9E]
public theorem exists_twoTerm_representative_free_zero_and_finite
    {R : Type u} [Ring R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    (∃ L : CochainComplex (ModuleCat.{v} R) ℤ,
      L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧
        Module.Free R (L.X 0) ∧ Nonempty (DerivedCategory.Q.obj L ≅ K)) ∧
    (IsNoetherianRing R →
      Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) →
      Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K) →
      ∃ L : CochainComplex (ModuleCat.{v} R) ℤ,
        L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧
          Module.Finite R (L.X (-1)) ∧ Module.Finite R (L.X 0) ∧
            Module.Free R (L.X 0) ∧ Nonempty (DerivedCategory.Q.obj L ≅ K)) := by
  have hKLE : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun i hi ↦
    hK i (by omega) (by omega)
  have : K.IsLE 0 := hKLE
  have : K.IsGE (-1) := (DerivedCategory.isGE_iff K (-1)).2 fun i hi ↦
    hK i (by omega) (by omega)
  obtain ⟨M, hMLE, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE K 0
  have : M.IsStrictlyLE 0 := hMLE
  obtain ⟨P, f, _, hf, hPfree, hPLE⟩ :=
    have : ObjectProperty.ContainsZero (fun X : ModuleCat.{v} R ↦ Module.Free R X) :=
      ⟨⟨ModuleCat.of R (Fin 0 → Shrink.{v} R),
        ModuleCat.isZero_of_subsingleton _, inferInstance⟩⟩
    (CochainComplex.exists_quasiIso_prop
      (fun X : ModuleCat.{v} R ↦ Module.Free R X) exists_free_cover 0).1 M
  have : QuasiIso f := hf
  have : P.IsStrictlyLE 0 := hPLE
  obtain ⟨hPge, hPle, hPe⟩ :=
    truncGE_representative P K (asIso (DerivedCategory.Q.map f) ≪≫ eM.symm)
  refine ⟨⟨P.truncGE (-1), hPge, hPle,
    Module.Free.of_equiv (P.truncGEXIso (-1) 0).toLinearEquiv.symm, hPe⟩, ?_⟩
  · intro hnoeth hfinneg hfinzero
    have : IsNoetherianRing R := hnoeth
    have hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
      (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology K 0
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K)).2.1.mpr
        ⟨⟨0, fun i hi ↦ hK i (by omega) (by omega)⟩, fun i ↦ by
          by_cases hneg : i = -1
          · subst i
            exact hfinneg
          by_cases hzero : i = 0
          · subst i
            exact hfinzero
          exact finite_of_isZero _ (hK i hneg hzero)⟩
    obtain ⟨F, α, hF, hFLE, hα⟩ :=
      (StacksDraft.PseudoCoherence.exists_finiteFree_representative_le K 0)
        hpseudo (fun i hi ↦ hK i (by omega) (by omega))
    have : IsIso α := hα
    obtain ⟨hFge, hFle, hFe⟩ := truncGE_representative F K (asIso α)
    let N := F.truncGE (-1)
    have : Module.Finite R (F.X 0) := (hF 0).1
    have : Module.Free R (F.X 0) := (hF 0).2
    have : Module.Finite R (F.X (-1)) := (hF (-1)).1
    have hNzeroFinite : Module.Finite R (N.X 0) :=
      Module.Finite.equiv (F.truncGEXIso (-1) 0).toLinearEquiv.symm
    have hNzeroFree : Module.Free R (N.X 0) :=
      Module.Free.of_equiv (F.truncGEXIso (-1) 0).toLinearEquiv.symm
    have hNnegFinite : Module.Finite R (N.X (-1)) := by
      have hopcycles : Module.Finite R (F.opcycles (-1)) :=
        Module.Finite.of_surjective (ModuleCat.Hom.hom (F.pOpcycles (-1)))
          ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      exact Module.Finite.equiv (F.truncGEXIsoOpcycles (-1)).symm.toLinearEquiv
    exact ⟨N, hFge, hFle, hNnegFinite, hNzeroFinite, hNzeroFree, hFe⟩

section Factorization

open TwoTermComplexExt

/-- The forward half of `TwoTermComplexExt.forall_Q_map_comp_eq_zero_iff` only uses its
hypothesis for the module in degree `-1`. This is the precise form needed for the finite
case. -/
private lemma factorization_of_ext_to_neg_one_eq_zero
    {R : Type u} [CommRing R] [Small.{v} R]
    (M K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hMpos : ∀ i, 0 < i → IsZero (M.X i)) (hM0 : Projective (M.X 0))
    (hK : ∀ i, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) (a : M ⟶ K)
    (h : ∀ ξ : TwoTermComplexExt.ExtMod K (K.X (-1)) 1,
      DerivedCategory.Q.map a ≫ ξ = 0) :
    ∃ h0 : M.X 0 ⟶ K.X (-1), a.f (-1) + M.d (-1) 0 ≫ h0 = 0 := by
  let N := K.X (-1)
  have hTz : ∀ i, i ≠ (-1 : ℤ) → IsZero ((shiftSingle N 1).X i) := by
    intro i hi
    rw [shiftSingle, CochainComplex.shiftFunctor_obj_X']
    apply HomologicalComplex.isZero_single_obj_X
    omega
  have hTzero : ∀ i ≤ (-2 : ℤ), IsZero ((shiftSingle N 1).X i) :=
    fun i hi => hTz i (by omega)
  have eN : N ≅ (shiftSingle N 1).X (-1) := by
    refine (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).symm ≪≫ ?_
    refine eqToIso ?_
    rw [shiftSingle, CochainComplex.shiftFunctor_obj_X']
    norm_num
  have hTd : ∀ i j, (shiftSingle N 1).d i j = 0 := by
    intro i j
    by_cases hi : i = (-1 : ℤ)
    · by_cases hj : j = 0
      · subst hi hj
        exact (hTz 0 (by norm_num)).eq_zero_of_tgt _
      · apply (shiftSingle N 1).shape
        simp only [ComplexShape.up_Rel]
        omega
    · exact (hTz i hi).eq_zero_of_src _
  let kf : ∀ i, K.X i ⟶ (shiftSingle N 1).X i := fun i =>
    if hi : i = -1 then eqToHom (by rw [hi] : K.X i = N) ≫ eN.hom ≫
      eqToHom (by rw [hi] : (shiftSingle N 1).X (-1) = (shiftSingle N 1).X i)
    else 0
  let κcon : K ⟶ shiftSingle N 1 := HomologicalComplex.Hom.mk kf (by
    intro i j hij
    rw [hTd]
    simp only [comp_zero]
    by_cases hj : j = -1
    · have hi : i = -2 := by
        simp only [ComplexShape.up_Rel] at hij
        omega
      have hKi : IsZero (K.X i) := by
        rw [hi]
        exact hK (-2) (by norm_num) (by norm_num)
      rw [hKi.eq_zero_of_src (K.d i j)]
      simp
    · have hzj : kf j = 0 := by simp [kf, hj]
      rw [hzj]
      simp)
  let Qq := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
  let κ : ExtMod K N 1 := toHomD (Qq.map κcon)
  have hkill : DerivedCategory.Q.map a ≫ κ = 0 := h κ
  have hcomp : DerivedCategory.Q.map a ≫ κ = toHomD (Qq.map (a ≫ κcon)) := by
    have h1 : DerivedCategory.Q.map a ≫ κ = toHomD (Qq.map a ≫ Qq.map κcon) := by
      dsimp [κ]
      exact Q_map_comp_toHomD a (Qq.map κcon)
    rw [h1, ← Functor.map_comp]
  have hzero : toHomD (Qq.map (a ≫ κcon)) = 0 := hcomp.symm.trans hkill
  have hclzero : Qq.map (a ≫ κcon) = 0 := by
    apply (toHomD_bijective M (shiftSingle N 1) hMpos hM0 hTzero).1
    change toHomD (Qq.map (a ≫ κcon)) = toHomD (0 : HomK M (shiftSingle N 1))
    rw [hzero, toHomD_zero]
  obtain ⟨H⟩ : Nonempty (Homotopy (a ≫ κcon) 0) :=
    ⟨HomotopyCategory.homotopyOfEq _ _ (by rw [hclzero, Functor.map_zero])⟩
  refine ⟨-(H.hom 0 (-1) ≫ eN.inv), ?_⟩
  have hrel : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 := by simp [ComplexShape.up_Rel]
  have hrel2 : (ComplexShape.up ℤ).Rel (-2 : ℤ) (-1) := by simp [ComplexShape.up_Rel]
  have hcomm := H.comm (-1)
  rw [dNext_eq H.hom hrel, prevD_eq H.hom hrel2, hTd] at hcomm
  simp only [comp_zero, add_zero, HomologicalComplex.zero_f, HomologicalComplex.comp_f] at hcomm
  have hf1 : κcon.f (-1) ≫ eN.inv = 𝟙 (K.X (-1)) := by
    change kf (-1) ≫ eN.inv = _
    simp [kf]
  have key := congrArg (· ≫ eN.inv) hcomm
  simp only [Category.assoc] at key
  rw [hf1, Category.comp_id] at key
  rw [key, Preadditive.comp_neg, ← Category.assoc]
  abel

/-- A two-term complex has no terms outside degrees `-1` and `0`. -/
private lemma isZero_X_of_ne_neg_one_of_ne_zero {R : Type u} [Ring R]
    (L : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    (i : ℤ) (h1 : i ≠ -1) (h0 : i ≠ 0) : IsZero (L.X i) := by
  rcases lt_or_gt_of_ne h0 with hi | hi
  · exact CochainComplex.isZero_of_isStrictlyGE L (-1) i (by omega)
  · exact CochainComplex.isZero_of_isStrictlyLE L 0 i hi

/-- If `a` kills the Ext classes into the degree `-1` term of a two-term representative `L` of
`K`, then multiplication by `a` factors through the differential of `L`. -/
private lemma factorization_of_ext_annihilated {R : Type u} [CommRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (L : CochainComplex (ModuleCat.{v} R) ℤ)
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0] (hL0 : Module.Projective R (L.X 0))
    (e : DerivedCategory.Q.obj L ≅ K) (a : R)
    (h : ∀ ξ : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (L.X (-1))) 1, a • ξ = 0) :
    ∃ h0 : L.X 0 ⟶ L.X (-1), L.d (-1) 0 ≫ h0 = a • 𝟙 (L.X (-1)) := by
  have hProj : Projective (L.X 0) := (IsProjective.iff_projective (R := R) (L.X 0)).mp hL0
  let f : L ⟶ L := -(a • 𝟙 L)
  let tIso : DerivedCategory.Q.obj (shiftSingle (L.X (-1)) 1) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj (L.X (-1)))⟦(1 : ℤ)⟧ :=
    ((DerivedCategory.Q (C := ModuleCat.{v} R)).commShiftIso (1 : ℤ)).app
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj (L.X (-1)))
  have hfzero : ∀ ξ : ExtMod L (L.X (-1)) 1, DerivedCategory.Q.map f ≫ ξ = 0 := by
    intro ξ
    have hz' := congrArg (e.hom ≫ ·) (h (e.inv ≫ ξ ≫ tIso.hom))
    apply (cancel_mono tIso.hom).mp
    simpa [f, Category.assoc] using hz'
  obtain ⟨h0, hh⟩ := factorization_of_ext_to_neg_one_eq_zero L L
    (fun i hi => CochainComplex.isZero_of_isStrictlyLE L 0 i hi) hProj
    (isZero_X_of_ne_neg_one_of_ne_zero L) f hfzero
  refine ⟨h0, ?_⟩
  have hfm1 : f.f (-1) = -(a • 𝟙 (L.X (-1))) := by simp [f]
  rw [hfm1] at hh
  exact (neg_add_eq_zero.mp hh).symm

/-- Ideal annihilation of the first Ext groups of `K` is the factorization property for any one
two-term representative with projective degree-zero term. -/
private lemma criterion_for_representative
    {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{v} R))
    (L : CochainComplex (ModuleCat.{v} R) ℤ)
    (hLge : L.IsStrictlyGE (-1)) (hLle : L.IsStrictlyLE 0)
    (hL0 : Module.Projective R (L.X 0)) (e : DerivedCategory.Q.obj L ≅ K) :
    (∀ (N : ModuleCat.{v} R) (a : R), a ∈ I →
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0) ↔
      ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
        L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1)) := by
  have : L.IsStrictlyGE (-1) := hLge
  have : L.IsStrictlyLE 0 := hLle
  have hProj : Projective (L.X 0) :=
    (IsProjective.iff_projective (R := R) (L.X 0)).mp hL0
  have hLpos : ∀ i : ℤ, 0 < i → IsZero (L.X i) := fun i hi ↦
    CochainComplex.isZero_of_isStrictlyLE L 0 i hi
  have hLsupport := isZero_X_of_ne_neg_one_of_ne_zero L
  let targetIso (N : ModuleCat.{v} R) :
      DerivedCategory.Q.obj (TwoTermComplexExt.shiftSingle N 1) ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)⟦(1 : ℤ)⟧ :=
    ((DerivedCategory.Q (C := ModuleCat.{v} R)).commShiftIso (1 : ℤ)).app
      ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).obj N)
  let scalarMap (a : R) : L ⟶ L := -(a • 𝟙 L)
  have hscalar (a : R) : (scalarMap a).f (-1) = -(a • 𝟙 (L.X (-1))) := by
    simp [scalarMap]
  constructor
  · intro hAnn a ha
    exact factorization_of_ext_annihilated K L hL0 e a (hAnn _ a ha)
  · intro hfac N a ha ξ
    have hzero : ∀ (N : ModuleCat.{v} R) (ξ : TwoTermComplexExt.ExtMod L N 1),
        DerivedCategory.Q.map (scalarMap a) ≫ ξ = 0 := by
      apply (TwoTermComplexExt.forall_Q_map_comp_eq_zero_iff L L hLpos hProj hLsupport hProj
        (scalarMap a)).mpr
      obtain ⟨h, hh⟩ := hfac a ha
      refine ⟨h, ?_⟩
      rw [hscalar, neg_add_eq_zero]
      exact hh.symm
    have hz := hzero N (e.hom ≫ ξ ≫ (targetIso N).inv)
    have hz' := congrArg (e.inv ≫ ·) hz
    apply (cancel_mono (targetIso N).inv).mp
    simpa [scalarMap, Category.assoc] using hz'

/-- **Stacks 0G9F.** For a derived object with cohomology concentrated in degrees `-1` and `0`,
the first Ext groups are annihilated by an ideal exactly when multiplication by every element of
the ideal factors through the differential of a suitable free two-term representative, or of
every projective two-term representative. Under Noetherian and finiteness hypotheses these are
also equivalent to testing only finite modules and to the existence of a finite representative.
-/
@[stacks 0G9F]
public theorem ext_one_annihilated_iff_twoTerm_factorization
    {R : Type u} [CommRing R] [Small.{v} R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{v} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    let moduleObject := fun N : ModuleCat.{v} R ↦
      (DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N
    let extAnnihilated := ∀ (N : ModuleCat.{v} R) (a : R), a ∈ I →
      ∀ ξ : DerivedCategory.Ext K (moduleObject N) 1, a • ξ = 0
    let hasFreeRepresentative := ∃ L : CochainComplex (ModuleCat.{v} R) ℤ,
      L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧ Module.Free R (L.X 0) ∧
        Nonempty (DerivedCategory.Q.obj L ≅ K) ∧
        ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
          L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1))
    let everyProjectiveRepresentative := ∀ L : CochainComplex (ModuleCat.{v} R) ℤ,
      L.IsStrictlyGE (-1) → L.IsStrictlyLE 0 → Module.Projective R (L.X 0) →
        Nonempty (DerivedCategory.Q.obj L ≅ K) →
        ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
          L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1))
    let finiteExtAnnihilated := ∀ (N : ModuleCat.{v} R), Module.Finite R N →
      ∀ (a : R), a ∈ I → ∀ ξ : DerivedCategory.Ext K (moduleObject N) 1, a • ξ = 0
    let hasFiniteFreeRepresentative := ∃ L : CochainComplex (ModuleCat.{v} R) ℤ,
      L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧ Module.Finite R (L.X (-1)) ∧
        Module.Finite R (L.X 0) ∧ Module.Free R (L.X 0) ∧
        Nonempty (DerivedCategory.Q.obj L ≅ K) ∧
        ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
          L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1))
    (extAnnihilated ↔ hasFreeRepresentative) ∧
      (hasFreeRepresentative ↔ everyProjectiveRepresentative) ∧
      (IsNoetherianRing R →
        Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).obj K) →
        Module.Finite R
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj K) →
        (extAnnihilated ↔ finiteExtAnnihilated) ∧
          (finiteExtAnnihilated ↔ hasFiniteFreeRepresentative)) := by
  dsimp
  have reps := exists_twoTerm_representative_free_zero_and_finite K hK
  have free_projective (M : ModuleCat.{v} R) (h : Module.Free R M) :
      Module.Projective R M := by
    have : Module.Free R M := h
    infer_instance
  have A_to_C :
      (∀ (N : ModuleCat.{v} R) (a : R), a ∈ I →
        ∀ ξ : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0) →
      ∀ L : CochainComplex (ModuleCat.{v} R) ℤ,
        L.IsStrictlyGE (-1) → L.IsStrictlyLE 0 → Module.Projective R (L.X 0) →
          Nonempty (DerivedCategory.Q.obj L ≅ K) →
          ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
            L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1)) := by
    intro h L hge hle hp ⟨e⟩
    exact (criterion_for_representative I K L hge hle hp e).mp h
  have C_to_B :
      (∀ L : CochainComplex (ModuleCat.{v} R) ℤ,
        L.IsStrictlyGE (-1) → L.IsStrictlyLE 0 → Module.Projective R (L.X 0) →
          Nonempty (DerivedCategory.Q.obj L ≅ K) →
          ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
            L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1))) →
      ∃ L : CochainComplex (ModuleCat.{v} R) ℤ,
        L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧ Module.Free R (L.X 0) ∧
          Nonempty (DerivedCategory.Q.obj L ≅ K) ∧
          ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
            L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1)) := by
    intro h
    obtain ⟨L, hge, hle, hf, he⟩ := reps.1
    exact ⟨L, hge, hle, hf, he, h L hge hle (free_projective _ hf) he⟩
  have B_to_A :
      (∃ L : CochainComplex (ModuleCat.{v} R) ℤ,
        L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧ Module.Free R (L.X 0) ∧
          Nonempty (DerivedCategory.Q.obj L ≅ K) ∧
          ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
            L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1))) →
      ∀ (N : ModuleCat.{v} R) (a : R), a ∈ I →
        ∀ ξ : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0 := by
    rintro ⟨L, hge, hle, hf, ⟨e⟩, hfac⟩
    exact (criterion_for_representative I K L hge hle (free_projective _ hf) e).mpr hfac
  have A_to_B := fun h => C_to_B (A_to_C h)
  refine ⟨⟨A_to_B, B_to_A⟩, ⟨fun h => A_to_C (B_to_A h), C_to_B⟩, ?_⟩
  intro hnoeth hm1 hm0
  have finiteRep := reps.2 hnoeth hm1 hm0
  have finite_to_B :
      (∀ (N : ModuleCat.{v} R), Module.Finite R N → ∀ (a : R), a ∈ I →
        ∀ ξ : DerivedCategory.Ext K
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, a • ξ = 0) →
      ∃ L : CochainComplex (ModuleCat.{v} R) ℤ,
        L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧ Module.Free R (L.X 0) ∧
          Nonempty (DerivedCategory.Q.obj L ≅ K) ∧
          ∀ (a : R), a ∈ I → ∃ h : L.X 0 ⟶ L.X (-1),
            L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1)) := by
    intro hfinite
    obtain ⟨L, hge, hle, hfinm1, _, hfree, ⟨e⟩⟩ := finiteRep
    refine ⟨L, hge, hle, hfree, ⟨e⟩, ?_⟩
    intro a ha
    have : L.IsStrictlyGE (-1) := hge
    have : L.IsStrictlyLE 0 := hle
    exact factorization_of_ext_annihilated K L (free_projective _ hfree) e a
      (hfinite _ hfinm1 a ha)
  refine ⟨⟨fun h N _ a ha ξ ↦ h N a ha ξ, fun hfinite ↦ B_to_A (finite_to_B hfinite)⟩, ?_, ?_⟩
  · intro hfinite
    obtain ⟨L, hge, hle, hfinm1, hfin0, hfree, he⟩ := finiteRep
    exact ⟨L, hge, hle, hfinm1, hfin0, hfree, he,
      A_to_C (B_to_A (finite_to_B hfinite)) L hge hle (free_projective _ hfree) he⟩
  · rintro ⟨L, hge, hle, _, _, hf, he, hfac⟩ N _ a ha ξ
    exact B_to_A ⟨L, hge, hle, hf, he, hfac⟩ N a ha ξ

end Factorization

end TwoTermComplex
