module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.RingTheory.Cech.KoszulColimit
public import StacksFrontier.RingTheory.Koszul.Functoriality
public import StacksFrontier.RingTheory.Koszul.Regular

/-!
# The extended alternating Čech complex of a Koszul-regular sequence

Let `R` be a commutative ring and let `f_1, …, f_r ∈ R` be a Koszul-regular sequence. The
extended alternating Čech complex `C^•(f_1, …, f_r; R)` then has cohomology only in degree
`r`, the length of the sequence: it is a resolution of its own top cohomology. Equivalently,
after the shift built into `Cech.cechComplex`, the augmented complex
`R → C^•(f_1, …, f_r; R)` is acyclic away from the top.

## Main results

* `Cech.cechComplex_homology_isZero_of_isKoszulRegular`: the cohomology of the extended
  alternating Čech complex of a Koszul-regular sequence vanishes in every degree other than
  the length of the sequence.

## References

* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
-/

@[expose] public section

namespace Cech

open CategoryTheory CategoryTheory.Limits
open scoped ExteriorAlgebra

universe u

private theorem isKoszulRegular_of_iso {R : Type u} [CommRing R] {r : ℕ}
    {f g : Fin r → R} (hf : Koszul.IsKoszulRegular f)
    (e : Koszul.seqComplex f ≅ Koszul.seqComplex g) : Koszul.IsKoszulRegular g := by
  intro i hi
  exact (hf i hi).of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso e).symm

private theorem isKoszulRegular_perm {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) (σ : Equiv.Perm (Fin r)) :
    Koszul.IsKoszulRegular (f ∘ σ) := by
  obtain ⟨e⟩ := Koszul.seqComplex_mulVec_iso f (σ.permMatrix R)
    ((Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [Matrix.det_permutation]
      exact (Equiv.Perm.sign σ).isUnit.map (Int.castRingHom R)))
  rw [Matrix.permMatrix_mulVec] at e
  exact isKoszulRegular_of_iso hf e

private theorem snoc_init_comp_swap {α : Type*} {n : ℕ}
    (f : Fin (n + 1) → α) (i : Fin (n + 1)) (a : α) :
    Fin.snoc (Fin.init (f ∘ Equiv.swap i (Fin.last n))) a =
      Function.update f i a ∘ Equiv.swap i (Fin.last n) := by
  let σ := Equiv.swap i (Fin.last n)
  let q := Function.update f i a ∘ σ
  have hinit : Fin.init (f ∘ σ) = Fin.init q := by
    ext k
    have hne : σ k.castSucc ≠ i := by
      intro h
      have h' := congrArg σ h
      simp [σ] at h'
    simp [q, Fin.init, Function.update, hne]
  have hlast : q (Fin.last n) = a := by simp [q, σ]
  show Fin.snoc (Fin.init (f ∘ σ)) a = q
  rw [hinit, ← hlast, Fin.snoc_init_self]

private theorem isKoszulRegular_update_mul {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (i : Fin r) (a b : R)
    (ha : Koszul.IsKoszulRegular (Function.update f i a))
    (hb : Koszul.IsKoszulRegular (Function.update f i b)) :
    Koszul.IsKoszulRegular (Function.update f i (a * b)) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n =>
      let σ := Equiv.swap i (Fin.last n)
      let s := Fin.init (f ∘ σ)
      have hs : ∀ c, Koszul.IsKoszulRegularOn (Fin.snoc s c) R ↔
          Koszul.IsKoszulRegular (Function.update f i c) := fun c ↦ by
        rw [Koszul.isKoszulRegularOn_self_iff, snoc_init_comp_swap]
        exact ⟨fun h ↦ by simpa [σ, Function.comp_def] using isKoszulRegular_perm _ h σ,
          fun h ↦ isKoszulRegular_perm _ h σ⟩
      exact (hs _).1 ((Koszul.isH1RegularOn_and_isKoszulRegularOn_snoc_mul s a b).2
        ⟨(hs a).2 ha, (hs b).2 hb⟩)

private theorem isKoszulRegular_update_pow {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) (i : Fin r) (n : ℕ) :
    Koszul.IsKoszulRegular (Function.update f i (f i ^ (n + 1))) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [pow_succ]
      apply isKoszulRegular_update_mul f i (f i ^ (n + 1)) (f i) ih
      simpa using hf

private theorem isKoszulRegular_pow {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) (n : ℕ) :
    Koszul.IsKoszulRegular (fun i ↦ f i ^ (n + 1)) := by
  classical
  have step : ∀ (s : Finset (Fin r)), Koszul.IsKoszulRegular
      (fun i ↦ if i ∈ s then f i ^ (n + 1) else f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hf
    | @insert i s hi hs =>
        let q := fun k ↦ if k ∈ s then f k ^ (n + 1) else f k
        have hq := isKoszulRegular_update_pow q hs i n
        have heq : Function.update q i (q i ^ (n + 1)) =
            (fun k ↦ if k ∈ insert i s then f k ^ (n + 1) else f k) := by
          funext k
          by_cases hki : k = i <;> simp [q, hki, hi]
        simpa only [heq] using hq
  simpa using step Finset.univ

private lemma preservesColimits_shortComplexHomology {R : Type u} [CommRing R] :
    PreservesColimitsOfShape ℕ (ShortComplex.homologyFunctor (ModuleCat.{u} R)) := by
  let : HasFilteredColimitsOfSize.{0, 0} (ModuleCat.{u} R) :=
    hasFilteredColimitsOfSize_shrink
  let : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
    AB5OfSize_shrink.{0, 0, u, u} (ModuleCat.{u} R)
  let : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) := AB5OfSize.ofShape ℕ
  have hPFL : PreservesFiniteLimits (colim (J := ℕ) (C := ModuleCat.{u} R)) := inferInstance
  have hPC : PreservesColimitsOfSize.{u, u} (colim (J := ℕ) (C := ModuleCat.{u} R)) :=
    inferInstance
  let : (colim (J := ℕ) (C := ModuleCat.{u} R)).PreservesHomology :=
    { preservesKernels := fun {X Y} f ↦ inferInstance
      preservesCokernels := fun {X Y} f ↦ inferInstance }
  refine ⟨fun {E} ↦ preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone E) ?_⟩
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (Stacks.HomologyColimit.compHomologyFunctorIso E)
      (colimit.cocone
        ((ShortComplex.FunctorEquivalence.inverse ℕ (ModuleCat.{u} R)).obj E).homology)).symm
      (colimit.isColimit _))
    (Cocone.ext
      (((ShortComplex.FunctorEquivalence.inverse ℕ (ModuleCat.{u} R)).obj E).mapHomologyIso
      (colim : Functor (Functor ℕ (ModuleCat.{u} R)) (ModuleCat.{u} R))).symm (fun j ↦ ?_))
  set T := (ShortComplex.FunctorEquivalence.inverse ℕ (ModuleCat.{u} R)).obj E
  let ι : (evaluation ℕ (ModuleCat.{u} R)).obj j ⟶
      (colim : Functor (Functor ℕ (ModuleCat.{u} R)) (ModuleCat.{u} R)) :=
    { app := fun X ↦ colimit.ι X j
      naturality := fun X Y f ↦ by simp }
  have key : ι.app T.homology = (T.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} R)).obj j)).inv ≫
      ShortComplex.homologyMap (T.mapNatTrans ι) ≫ (T.mapHomologyIso colim).hom :=
    NatTrans.app_homology ι T
  show ((T.mapHomologyIso ((evaluation ℕ (ModuleCat.{u} R)).obj j)).hom ≫ ι.app T.homology) ≫
      (T.mapHomologyIso
        (colim : Functor (Functor ℕ (ModuleCat.{u} R)) (ModuleCat.{u} R))).inv =
    ShortComplex.homologyMap (T.mapNatTrans ι)
  rw [key]
  simp

private theorem homologyFunctor_preservesColimits (R : Type u) [CommRing R] (p : ℕ) :
    PreservesColimitsOfShape ℕ
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p) := by
  have : PreservesColimitsOfShape ℕ
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p) :=
    ⟨fun {_} ↦ ⟨fun hs ↦ ⟨ShortComplex.isColimitOfIsColimitπ _
      (isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs)
      (isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs)
      (isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs)⟩⟩⟩
  have := preservesColimits_shortComplexHomology (R := R)
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} R) (ComplexShape.up ℕ) p).symm

private theorem seqComplex_X_isZero_of_lt {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (q : ℕ) (hq : r < q) : IsZero ((Koszul.seqComplex f).X q) := by
  let b := Pi.basisFun R (Fin r)
  let : Subsingleton (⋀[R]^q (Fin r → R)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt b b.span_eq q (by simpa using hq)
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (⋀[R]^q (Fin r → R)))

private noncomputable def koszulPowerHomologyIso {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (n p : ℕ) (hpr : p ≤ r) :
    (koszulPowerCochainComplex f n).homology p ≅
      (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).homology (r - p) := by
  let K := Koszul.seqComplex (fun i ↦ f i ^ (n + 1))
  let E := K.extend ComplexShape.embeddingDownNat
  let S := (shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-(r : ℤ))).obj E
  change (S.restriction ComplexShape.embeddingUpNat).homology p ≅ K.homology (r - p)
  have e : (S.restriction ComplexShape.embeddingUpNat).homology p ≅ S.homology p := by
    by_cases hp : p = 0
    · subst p
      have hz : IsZero (S.X (-1)) :=
        (seqComplex_X_isZero_of_lt (fun i ↦ f i ^ (n + 1)) (r + 1) (by omega)).of_iso
          (CochainComplex.shiftFunctorObjXIso E (-(r : ℤ)) (-1)
              (-(↑(r + 1) : ℤ)) (by omega) ≪≫
            K.extendXIso ComplexShape.embeddingDownNat (by simp))
      exact (CochainComplex.isoHomologyπ₀ (S.restriction ComplexShape.embeddingUpNat)).symm ≪≫
        S.restrictionCyclesIso ComplexShape.embeddingUpNat 0 1 (by simp)
          (j' := (0 : ℤ)) (k' := (1 : ℤ)) (by simp) (by simp) (by simp) ≪≫
        S.isoHomologyπ (-1) 0 (by simp) (hz.eq_of_src _ _)
    · exact S.restrictionHomologyIso ComplexShape.embeddingUpNat (p - 1) p (p + 1)
        (by apply ComplexShape.prev_eq'; change p - 1 + 1 = p; omega) (by simp)
        (i' := ((p - 1 : ℕ) : ℤ)) (j' := (p : ℤ)) (k' := ((p + 1 : ℕ) : ℤ))
        (by simp) (by simp) (by simp) (by simp; omega) (by simp)
  exact e ≪≫
      (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).shiftIso
        (-(r : ℤ)) (p : ℤ) ((p : ℤ) - r) (by omega)).app E) ≪≫
      K.extendHomologyIso ComplexShape.embeddingDownNat (by simp; omega)

private theorem koszulPowerHomology_isZero {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (hf : Koszul.IsKoszulRegular f) (n p : ℕ)
    (hp : p ≠ r) :
    IsZero ((koszulPowerCochainComplex f n).homology p) := by
  by_cases hpr : p ≤ r
  · exact ((isKoszulRegular_pow f hf n (r - p) (by omega))).of_iso
      (koszulPowerHomologyIso f n p hpr)
  · apply HomologicalComplex.ExactAt.isZero_homology
    apply HomologicalComplex.ExactAt.of_isZero
    let K := Koszul.seqComplex (fun i ↦ f i ^ (n + 1))
    let E := K.extend ComplexShape.embeddingDownNat
    exact (K.isZero_extend_X ComplexShape.embeddingDownNat ((p : ℤ) - r)
      (by intro j; simp; omega)).of_iso
      (CochainComplex.shiftFunctorObjXIso E (-(r : ℤ)) (p : ℤ)
        ((p : ℤ) - r) (by omega))

/-- The extended alternating Čech complex of a Koszul-regular sequence has zero cohomology in
every degree other than the length of the sequence. -/
@[stacks 0G6L]
public theorem cechComplex_homology_isZero_of_isKoszulRegular
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (hf : Koszul.IsKoszulRegular f)
    (p : ℕ) (hp : p ≠ r) :
    CategoryTheory.Limits.IsZero ((Cech.cechComplex f R).homology p) := by
  obtain ⟨σ, _, ι, hι, _, ⟨hc⟩⟩ := cechComplex_isColimit_koszulPowerComplexes f
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) p
  let := homologyFunctor_preservesColimits R p
  exact (isColimitOfPreserves H hc).isZero_pt
    ((koszulPowerDiagram f σ ⋙ H).isZero
      (fun n ↦ koszulPowerHomology_isZero f hf n p hp))

end Cech

end
