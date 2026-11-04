module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology
public import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeShift

/-!
# Canonical truncations of bounded below complexes

For a bounded below cochain complex `K` in an abelian category and `n : ℤ`, the canonical
truncation `τ_{≥ n} K` is again bounded below, and so is the complex `τ_{≤ n} τ_{≥ n} K`, which is
concentrated in degree `n`, with `Hⁿ(K)` there. This file packages these truncations as functors
on `CochainComplex.Plus C`, together with:

* the short exact sequence `0 → τ_{≤ n} τ_{≥ n} K → τ_{≥ n} K → X₃ → 0` and the quasi-isomorphisms
  `X₃ ⟶ τ_{≥ n+1} τ_{≥ n} K ⟵ τ_{≥ n+1} K`, so that the graded pieces of the filtration
  `K → τ_{≥ 0} K → τ_{≥ 1} K → ⋯` are the `Hⁿ(K)[-n]`;
* the natural isomorphism `τ_{≤ n} τ_{≥ n} K ≅ Hⁿ(K)[-n]`.

## Main definitions

* `CochainComplex.Plus.truncGEFunctor`, `CochainComplex.Plus.gradedFunctor`.
* `CochainComplex.Plus.gradedIsoSingle`: `τ_{≤ n} τ_{≥ n} K ≅ Hⁿ(K)[-n]`, naturally.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- **The canonical truncation `τ_{≤ n}` of a complex `≥ a` is `≥ a`.** -/
theorem isStrictlyGE_truncLE (K : CochainComplex C ℤ) (a n : ℤ) [K.IsStrictlyGE a] :
    (K.truncLE n).IsStrictlyGE a := by
  rw [isStrictlyGE_iff]
  intro i hi
  rcases lt_trichotomy i n with h | rfl | h
  · exact (K.isZero_of_isStrictlyGE a i hi).of_iso (K.truncLEXIso n i h)
  · exact (IsZero.of_mono (K.iCycles i) (K.isZero_of_isStrictlyGE a i hi)).of_iso
      (K.truncLEXIsoCycles i)
  · exact (K.truncLE n).isZero_of_isStrictlyLE n i h

/-- A complex concentrated in degree `n` is the complex `(single n).obj` of its degree `n` term. -/
def isoSingleOfIsStrictly (M : CochainComplex C ℤ) (n : ℤ) [M.IsStrictlyGE n] [M.IsStrictlyLE n] :
    M ≅ (single C (ComplexShape.up ℤ) n).obj (M.X n) where
  hom := mkHomToSingle (𝟙 _) (fun i (hi : (ComplexShape.up ℤ).Rel i n) ↦
    (M.isZero_of_isStrictlyGE n i (by change i + 1 = n at hi; lia)).eq_of_src _ _)
  inv := mkHomFromSingle (𝟙 _) (fun i (hi : (ComplexShape.up ℤ).Rel n i) ↦
    (M.isZero_of_isStrictlyLE n i (by change n + 1 = i at hi; lia)).eq_of_tgt _ _)
  hom_inv_id := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i n
    · apply (M.isZero_of_isStrictlyGE n i (by lia)).eq_of_src
    · simp
    · apply (M.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt
  inv_hom_id := by
    apply from_single_hom_ext
    simp

/-- The isomorphism `isoSingleOfIsStrictly` is natural in the complex concentrated in degree
`n`. -/
theorem isoSingleOfIsStrictly_hom_naturality {M M' : CochainComplex C ℤ} (φ : M ⟶ M') (n : ℤ)
    [M.IsStrictlyGE n] [M.IsStrictlyLE n] [M'.IsStrictlyGE n] [M'.IsStrictlyLE n] :
    φ ≫ (isoSingleOfIsStrictly M' n).hom =
      (isoSingleOfIsStrictly M n).hom ≫ (single C (ComplexShape.up ℤ) n).map (φ.f n) := by
  apply to_single_hom_ext
  simp [isoSingleOfIsStrictly, single_map_f_self]

namespace Plus

/-- **The canonical truncation `τ_{≥ n}`** on bounded below complexes. -/
def truncGEFunctor (n : ℤ) : CochainComplex.Plus C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _
    (CochainComplex.Plus.ι C ⋙ (ComplexShape.embeddingUpIntGE n).truncGEFunctor C)
    (fun K => ⟨n, by
      change (K.obj.truncGE n).IsStrictlyGE n
      infer_instance⟩)

/-- **The graded piece `τ_{≤ n} τ_{≥ n}`** on bounded below complexes. -/
def gradedFunctor (n : ℤ) : CochainComplex.Plus C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι C ⋙
      (ComplexShape.embeddingUpIntGE n).truncGEFunctor C ⋙
      (ComplexShape.embeddingUpIntLE n).truncLEFunctor C)
    (fun K => ⟨n, isStrictlyGE_truncLE (K.obj.truncGE n) n n⟩)

/-- The graded piece `τ_{≤ n} τ_{≥ n} K` is strictly `≥ n`. -/
instance (n : ℤ) (K : CochainComplex.Plus C) : ((gradedFunctor n).obj K).obj.IsStrictlyGE n :=
  isStrictlyGE_truncLE (K.obj.truncGE n) n n

/-- The graded piece `τ_{≤ n} τ_{≥ n} K` is strictly `≤ n`. -/
instance (n : ℤ) (K : CochainComplex.Plus C) : ((gradedFunctor n).obj K).obj.IsStrictlyLE n := by
  change ((K.obj.truncGE n).truncLE n).IsStrictlyLE n
  infer_instance

/-- `K ⟶ τ_{≥ n} K`. -/
def πTruncGE (n : ℤ) : 𝟭 (CochainComplex.Plus C) ⟶ truncGEFunctor n where
  app K := ObjectProperty.homMk (K.obj.πTruncGE n)
  naturality _ _ φ := ObjectProperty.hom_ext _ (πTruncGE_naturality φ.hom n).symm

/-- `τ_{≤ n} τ_{≥ n} K ⟶ τ_{≥ n} K`. -/
def ιGraded (n : ℤ) : gradedFunctor n ⟶ truncGEFunctor (C := C) n where
  app K := ObjectProperty.homMk ((K.obj.truncGE n).ιTruncLE n)
  naturality _ _ φ := ObjectProperty.hom_ext _ (ιTruncLE_naturality (truncGEMap φ.hom n) n)

/-- `τ_{≥ n} K ⟶ τ_{≥ n'} τ_{≥ n} K`. -/
def πTruncGEComp (n n' : ℤ) : truncGEFunctor (C := C) n ⟶ truncGEFunctor n ⋙ truncGEFunctor n' :=
  Functor.whiskerLeft (truncGEFunctor n) (πTruncGE n')

/-- `τ_{≥ n'} K ⟶ τ_{≥ n'} τ_{≥ n} K`. -/
def truncGEπTruncGE (n n' : ℤ) :
    truncGEFunctor (C := C) n' ⟶ truncGEFunctor n ⋙ truncGEFunctor n' :=
  Functor.whiskerRight (πTruncGE n) (truncGEFunctor n')

/-- `τ_{≥ n'} K ⟶ τ_{≥ n'} τ_{≥ n} K` is a quasi-isomorphism for `n ≤ n'`. -/
theorem quasiIso_truncGEπTruncGE (n n' : ℤ) (h : n ≤ n') (K : CochainComplex.Plus C) :
    QuasiIso ((truncGEπTruncGE n n').app K).hom := by
  show QuasiIso (truncGEMap (K.obj.πTruncGE n) n')
  rw [quasiIso_truncGEMap_iff]
  intro i hi
  exact K.obj.quasiIsoAt_πTruncGE n i (by lia)

/-- **The graded piece `τ_{≤ n} τ_{≥ n} K` is its degree `n` term placed in degree `n`**,
naturally in `K`. -/
def gradedIsoSingle (n : ℤ) :
    gradedFunctor (C := C) n ≅ (gradedFunctor n ⋙ CochainComplex.Plus.ι C ⋙
      HomologicalComplex.eval C (ComplexShape.up ℤ) n) ⋙
        (Stacks.DerivedIndexing.cplusSingleFunctors C).functor n :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ (isoSingleOfIsStrictly ((gradedFunctor n).obj K).obj n))
    (fun {_ _} φ => ObjectProperty.hom_ext _
      (isoSingleOfIsStrictly_hom_naturality ((gradedFunctor n).map φ).hom n))

/-- `τ_{≤ n} τ_{≥ n} K` read through the inclusion, with its isomorphism to the complex of its
degree `n` term. -/
def gradedIsoSingle' (n : ℤ) :
    gradedFunctor (C := C) n ⋙ CochainComplex.Plus.ι C ≅
      (gradedFunctor n ⋙ CochainComplex.Plus.ι C ⋙
        HomologicalComplex.eval C (ComplexShape.up ℤ) n) ⋙
        HomologicalComplex.single C (ComplexShape.up ℤ) n :=
  NatIso.ofComponents (fun K => isoSingleOfIsStrictly ((gradedFunctor n).obj K).obj n)
    (fun {_ _} φ => isoSingleOfIsStrictly_hom_naturality ((gradedFunctor n).map φ).hom n)

/-- **The degree `n` term of `τ_{≤ n} τ_{≥ n} K` is `Hⁿ(K)`**, naturally in `K`: it is the
homology in degree `n` of a complex concentrated there, and the truncation maps
`τ_{≤ n} τ_{≥ n} K → τ_{≥ n} K ← K` are isomorphisms on `Hⁿ`. -/
def gradedXIsoHomology (n : ℤ) :
    gradedFunctor (C := C) n ⋙ CochainComplex.Plus.ι C ⋙
        HomologicalComplex.eval C (ComplexShape.up ℤ) n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n := by
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
  let e₁ : gradedFunctor (C := C) n ⋙ CochainComplex.Plus.ι C ⋙ H ≅
      gradedFunctor n ⋙ CochainComplex.Plus.ι C ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (gradedIsoSingle' n) H ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (HomologicalComplex.homologyFunctorSingleIso C (ComplexShape.up ℤ) n) ≪≫
      Functor.rightUnitor _
  haveI : ∀ K : CochainComplex.Plus C, IsIso ((Functor.whiskerRight (ιGraded (C := C) n)
      (CochainComplex.Plus.ι C ⋙ H)).app K) := fun K => by
    change IsIso (HomologicalComplex.homologyMap ((K.obj.truncGE n).ιTruncLE n) n)
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).1
      ((K.obj.truncGE n).quasiIsoAt_ιTruncLE n n le_rfl)
  haveI : ∀ K : CochainComplex.Plus C, IsIso ((Functor.whiskerRight (πTruncGE (C := C) n)
      (CochainComplex.Plus.ι C ⋙ H)).app K) := fun K => by
    change IsIso (HomologicalComplex.homologyMap (K.obj.πTruncGE n) n)
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 (K.obj.quasiIsoAt_πTruncGE n n le_rfl)
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight (ιGraded (C := C) n)
    (CochainComplex.Plus.ι C ⋙ H))
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight (πTruncGE (C := C) n)
    (CochainComplex.Plus.ι C ⋙ H))
  exact e₁.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    asIso (Functor.whiskerRight (ιGraded (C := C) n) (CochainComplex.Plus.ι C ⋙ H)) ≪≫
    (asIso (Functor.whiskerRight (πTruncGE (C := C) n) (CochainComplex.Plus.ι C ⋙ H))).symm ≪≫
    Functor.leftUnitor _

end Plus

end CochainComplex
