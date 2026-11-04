module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs

/-!
# The canonical truncation filtration of a cochain complex

Every cochain complex `K^•` of an abelian category carries the decreasing filtration by its
canonical truncations, `F^pK^• = τ_{≤ -p}K^•`. This file builds that filtered complex, identifies
its graded pieces, and records the resulting description in the derived category: the `p`-th
graded piece represents `H^{-p}(K^•)[p]`.

## Main definitions

* `CochainComplex.liftTruncLE`: the factorization of a morphism out of a complex strictly bounded
  above by `n` through the canonical truncation `τ_{≤ n}` of its target.
* `CochainComplex.truncLEιOfLE`: the inclusion `τ_{≤ m}K^• ⟶ τ_{≤ n}K^•` for `m ≤ n`.
* `CochainComplex.truncLETruncLEIso`: for `m ≤ n`, the identification of `τ_{≤ m}K^•` with
  `τ_{≤ m}τ_{≤ n}K^•`.
* `CochainComplex.canonicalTruncationFiltration`: the filtered complex `F^pK^• = τ_{≤ -p}K^•`.
* `CochainComplex.truncationFiltrationMap`: its functoriality in the complex.
* `CochainComplex.truncationGradedPieceToSingle`: the comparison of `gr^p` with the single complex
  on `H^{-p}(K^•)` in degree `-p`.
* `CochainComplex.canonicalGradedPieceIso`: the resulting identification
  `gr^pK^• ≅ H^{-p}(K^•)[p]` in the derived category.

## Main results

* `CochainComplex.quasiIso_truncationGradedPieceToSingle`: the comparison with the single complex
  is a quasi-isomorphism.
* `CochainComplex.truncationGradedMap_quasiIso`: a quasi-isomorphism of complexes induces a
  quasi-isomorphism on every graded piece of the canonical truncation filtration.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- A morphism out of a complex which is strictly bounded above by `n` factors through the
canonical truncation `τ_{≤ n}` of its target. -/
def liftTruncLE {C : Type*} [Category* C] [Abelian C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (n : ℤ) [X.IsStrictlyLE n] :
    X ⟶ Y.truncLE n := inv (X.ιTruncLE n) ≫ CochainComplex.truncLEMap f n

/-- The factorization `liftTruncLE` recovers the original morphism. -/
lemma liftTruncLE_ιTruncLE {C : Type*} [Category* C] [Abelian C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) (n : ℤ) [X.IsStrictlyLE n] :
    liftTruncLE f n ≫ Y.ιTruncLE n = f := by
  simp [liftTruncLE, CochainComplex.ιTruncLE_naturality]

/-- The inclusion `τ_{≤ m} X ⟶ τ_{≤ n} X` of canonical truncations, for `m ≤ n`. -/
def truncLEιOfLE {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) {m n : ℤ} (h : m ≤ n) :
    X.truncLE m ⟶ X.truncLE n := by
  letI := (X.truncLE m).isStrictlyLE_of_le m n h
  exact liftTruncLE (X.ιTruncLE m) n

/-- The inclusions of canonical truncations are compatible with the inclusions into `X`. -/
lemma truncLEιOfLE_ιTruncLE {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) {m n : ℤ} (h : m ≤ n) :
    truncLEιOfLE X h ≫ X.ιTruncLE n = X.ιTruncLE m := by
  have := (X.truncLE m).isStrictlyLE_of_le m n h
  exact liftTruncLE_ιTruncLE (X.ιTruncLE m) n

/-- The inclusions of canonical truncations are monomorphisms. -/
instance truncLEιOfLE_mono {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) {m n : ℤ} (h : m ≤ n) :
    Mono (truncLEιOfLE X h) := by
  have : Mono (X.ιTruncLE m) := by
    dsimp [CochainComplex.ιTruncLE]
    infer_instance
  exact mono_of_mono_fac (truncLEιOfLE_ιTruncLE X h)

/-- For `m ≤ n`, truncating `τ_{≤ n} X` at `m` gives back `τ_{≤ m} X`. -/
def truncLETruncLEIso {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) {m n : ℤ} (h : m ≤ n) :
    X.truncLE m ≅ (X.truncLE n).truncLE m := by
  letI (Y : CochainComplex C ℤ) (i : ℤ) : Mono (Y.ιTruncLE i) := by
    dsimp [CochainComplex.ιTruncLE]
    infer_instance
  refine
    { hom := liftTruncLE (truncLEιOfLE X h) m
      inv := liftTruncLE ((X.truncLE n).ιTruncLE m ≫ X.ιTruncLE n) m
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← cancel_mono (X.ιTruncLE m)]
    simp only [Category.assoc, liftTruncLE_ιTruncLE, Category.id_comp]
    rw [← Category.assoc, liftTruncLE_ιTruncLE, truncLEιOfLE_ιTruncLE]
  · rw [← cancel_mono ((X.truncLE n).ιTruncLE m ≫ X.ιTruncLE n)]
    simp only [Category.assoc, Category.id_comp]
    rw [← Category.assoc (liftTruncLE (truncLEιOfLE X h) m),
      liftTruncLE_ιTruncLE, truncLEιOfLE_ιTruncLE, liftTruncLE_ιTruncLE]

/-- The identification of `τ_{≤ m}X` with `τ_{≤ m}τ_{≤ n}X` is compatible with the inclusions of
truncations. -/
lemma truncLETruncLEIso_hom_ιTruncLE {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) {m n : ℤ} (h : m ≤ n) :
    (truncLETruncLEIso X h).hom ≫ (X.truncLE n).ιTruncLE m = truncLEιOfLE X h :=
  liftTruncLE_ιTruncLE _ _

/-- A complex filtered by its canonical truncations, `F^pX^• = τ_{≤ -p}X^•`. -/
def canonicalTruncationFiltration {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) : CochainComplex.Filtered C := by
  letI (n : ℤ) : Mono (X.ιTruncLE n) := by
    dsimp [CochainComplex.ιTruncLE]
    infer_instance
  exact
    { X := X
      filtration.toMonoOver :=
        { obj := fun i ↦ MonoOver.mk (X.ιTruncLE (-i.unop))
          map := fun f ↦ MonoOver.homMk (truncLEιOfLE X (neg_le_neg (leOfHom f.unop)))
            (truncLEιOfLE_ιTruncLE X _) } }

/-- Transport of the canonical truncation filtration along a morphism of complexes. -/
def truncationFiltrationMap {C : Type*} [Category* C] [Abelian C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    canonicalTruncationFiltration X ⟶ canonicalTruncationFiltration Y :=
  FilteredObject.homMk f (fun i ↦ CochainComplex.truncLEMap f (-i.unop)) (fun i ↦ by
    change CochainComplex.truncLEMap f (-i.unop) ≫ Y.ιTruncLE (-i.unop) =
      X.ιTruncLE (-i.unop) ≫ f
    exact CochainComplex.ιTruncLE_naturality f _)

/-- The `i`-th graded piece of the canonical truncation filtration is the cokernel of the
inclusion of truncations, computed inside `τ_{≤ -i}X^•`. -/
def truncationGradedPieceIsoCokernel {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) (i : ℤ) :
    (FilteredObject.gr i).obj (canonicalTruncationFiltration X) ≅
      ((X.truncLE (-i)).shortComplexTruncLE (-(i + 1))).X₃ := by
  change cokernel (truncLEιOfLE X (show -(i + 1) ≤ -i by omega)) ≅
    cokernel ((X.truncLE (-i)).ιTruncLE (-(i + 1)))
  exact cokernel.mapIso _ _ (truncLETruncLEIso X (by omega)) (Iso.refl _) (by
    simpa only [Iso.refl_hom, Category.comp_id] using
      (truncLETruncLEIso_hom_ιTruncLE X (show -(i + 1) ≤ -i by omega)).symm)

/-- The complex `τ_{≥ n} τ_{≤ n} X^•` is the single complex on `H^n(X^•)` in degree `n`. -/
def truncGETruncLEIsoSingle {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) (n : ℤ) :
    (X.truncLE n).truncGE n ≅
      (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj (X.homology n) := by
  let Y := (X.truncLE n).truncGE n
  letI : Y.IsStrictlyLE n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact IsZero.of_iso ((X.truncLE n).isZero_of_isStrictlyLE n i hi)
      ((X.truncLE n).truncGEXIso n i hi)
  let N := (Y.exists_iso_single n).choose
  let eY := (Y.exists_iso_single n).choose_spec.some
  let eH : N ≅ X.homology n :=
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n N).symm ≪≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).mapIso eY.symm ≪≫
      (asIso (HomologicalComplex.homologyMap ((X.truncLE n).πTruncGE n) n)).symm ≪≫
      asIso (HomologicalComplex.homologyMap (X.ιTruncLE n) n)
  exact eY ≪≫ (HomologicalComplex.single C (ComplexShape.up ℤ) n).mapIso eH

/-- The canonical map from the `i`-th graded piece of the canonical truncation filtration to the
single complex on `H^{-i}(X^•)` placed in degree `-i`. -/
def truncationGradedPieceToSingle {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) (i : ℤ) :
    (FilteredObject.gr i).obj (canonicalTruncationFiltration X) ⟶
      (HomologicalComplex.single C (ComplexShape.up ℤ) (-i)).obj (X.homology (-i)) :=
  (truncationGradedPieceIsoCokernel X i).hom ≫
    (X.truncLE (-i)).shortComplexTruncLEX₃ToTruncGE (-(i + 1)) (-i) (by omega) ≫
    (truncGETruncLEIsoSingle X (-i)).hom

/-- The comparison of a graded piece of the canonical truncation filtration with a single complex
is a quasi-isomorphism. -/
lemma quasiIso_truncationGradedPieceToSingle {C : Type*} [Category* C] [Abelian C]
    (X : CochainComplex C ℤ) (i : ℤ) :
    QuasiIso (truncationGradedPieceToSingle X i) := by
  dsimp [truncationGradedPieceToSingle]
  infer_instance

/-- The map induced on cokernels by a square of monomorphisms whose vertical maps are
quasi-isomorphisms is a quasi-isomorphism. -/
lemma quasiIso_cokernelMap {C : Type*} [Category* C] [Abelian C]
    {X Y X' Y' : CochainComplex C ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') [Mono f] [Mono g]
    (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ g)
    [QuasiIso a] [QuasiIso b] :
    QuasiIso (cokernel.map f g a b w) := by
  let φ : ShortComplex.mk f (cokernel.π f) (cokernel.condition f) ⟶
      ShortComplex.mk g (cokernel.π g) (cokernel.condition g) :=
    { τ₁ := a
      τ₂ := b
      τ₃ := cokernel.map f g a b w
      comm₁₂ := w.symm
      comm₂₃ := (cokernel.π_desc _ _ _).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ ⟨ShortComplex.exact_cokernel f⟩
    ⟨ShortComplex.exact_cokernel g⟩ inferInstance inferInstance

/-- A quasi-isomorphism induces a quasi-isomorphism on every graded piece of the canonical
truncation filtration. -/
lemma truncationGradedMap_quasiIso {C : Type*} [Category* C] [Abelian C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [QuasiIso f] (i : ℤ) :
    QuasiIso ((FilteredObject.gr i).map (truncationFiltrationMap f)) := by
  have h : truncLEιOfLE X (show -(i + 1) ≤ -i by lia) ≫ CochainComplex.truncLEMap f (-i) =
      CochainComplex.truncLEMap f (-(i + 1)) ≫ truncLEιOfLE Y (show -(i + 1) ≤ -i by lia) := by
    have : Mono (Y.ιTruncLE (-i)) := by
      dsimp [CochainComplex.ιTruncLE]
      infer_instance
    rw [← cancel_mono (Y.ιTruncLE (-i))]
    simp [reassoc_of% truncLEιOfLE_ιTruncLE, truncLEιOfLE_ιTruncLE]
  have hf (n : ℤ) : QuasiIso (CochainComplex.truncLEMap f n) := by
    rw [CochainComplex.quasiIso_truncLEMap_iff]
    exact fun j _ ↦ inferInstance
  exact quasiIso_cokernelMap _ _ _ _ h

/-- The `p`-th graded piece of the canonical truncation filtration of `K^•` represents
`H^n(K^•)[p]` in the derived category, where `n = -p`. -/
def canonicalGradedPieceIso {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : CochainComplex A ℤ) (p n : ℤ) (hn : n = -p) :
    DerivedCategory.Q.obj
        ((FilteredObject.gr (C := CochainComplex A ℤ) p).obj
          (canonicalTruncationFiltration K)) ≅
      ((DerivedCategory.singleFunctor A 0).obj
        ((DerivedCategory.homologyFunctor A n).obj (DerivedCategory.Q.obj K)))⟦p⟧ := by
  subst hn
  letI : QuasiIso (truncationGradedPieceToSingle K p) :=
    quasiIso_truncationGradedPieceToSingle K p
  letI : IsIso (DerivedCategory.Q.map (truncationGradedPieceToSingle K p)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let eQ : DerivedCategory.Q.obj
      ((FilteredObject.gr (C := CochainComplex A ℤ) p).obj
        (canonicalTruncationFiltration K)) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor A (-p)).obj (K.homology (-p))) := by
    simpa only [neg_neg, CochainComplex.singleFunctor, CochainComplex.singleFunctors] using
      asIso (DerivedCategory.Q.map (truncationGradedPieceToSingle K p))
  let eH : K.homology (-p) ≅
      (DerivedCategory.homologyFunctor A (-p)).obj (DerivedCategory.Q.obj K) :=
    ((DerivedCategory.homologyFunctorFactors A (-p)).app K).symm
  exact eQ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ A (-p)).app (K.homology (-p))).symm ≪≫
    (DerivedCategory.singleFunctor A (-p)).mapIso eH ≪≫
    ((DerivedCategory.singleFunctors A).shiftIso p (-p) 0 (by omega)).symm.app _

end CochainComplex
