module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualOfKoszulComplex
public import StacksFrontier.CategoryTheory.Monoidal.MateProductsOfUnit

/-!
# The differential and the transition maps of the dual Koszul complex, as matrices

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪`, and let
`K_n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})` be the Koszul complex of
`AlgebraicGeometry.RingedSite.koszulPowerComplex`, whose degree-`p` term is `∏_{|S| = p} 𝒪`. Its
dual `AlgebraicGeometry.RingedSite.koszulPowerDualComplex`, the Koszul complex in degrees
`-r, …, 0`, has the same terms read in the opposite degrees, and its differential and the
transition maps of its tower are mates. This file computes those mates as matrices: they are the
transposed matrices, with no mate left in them.

* The differential from degree `-(p+1)` to degree `-p` has, at a subset `T` of cardinality `p + 1`
  and a subset `S` of cardinality `p`, the entry `(-1)^p` times the `(S, T)` entry of the Koszul
  differential `d^p`, which is `± f_i^{n+1}` when `T = S ∪ {i}` and zero otherwise.
* The transition map from `n + 1` to `n` is diagonal, multiplication by `f_S` at `S`.

## Main results

* `AlgebraicGeometry.RingedSite.evaluation_exactPairingKoszulPowerComplexIn`: the self-duality of
  the terms of the Koszul complex is the standard pairing of a product of copies of `𝒪`.
* `AlgebraicGeometry.RingedSite.koszulPowerDualComplex_d_comp_π`: the matrix of the differential
  of the dual Koszul complex.
* `AlgebraicGeometry.RingedSite.koszulPowerDualComplexMap_f_comp_π`: the matrix of a map of dual
  Koszul complexes induced by a map of Koszul complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The index types of the degree-`i` term and of the degree-`(-j)` term of a Koszul complex
agree when `i + j = 0`. -/
def idxNegEquiv (i j : ℤ) (h : i + j = 0) :
    AlternatingCech.Idx r i ≃ AlternatingCech.Idx r (-j) :=
  Equiv.subtypeEquivRight fun S => by omega

/-- The equivalence `idxNegEquiv` does not change the underlying subset. -/
@[simp]
theorem idxNegEquiv_val (i j : ℤ) (h : i + j = 0) (S : AlternatingCech.Idx r i) :
    (idxNegEquiv i j h S).1 = S.1 :=
  rfl

/-- **The self-duality of the terms of the Koszul complex is the standard pairing**: its
evaluation is the sum over the subsets `S` of the products of the `S`-th projections. -/
theorem evaluation_exactPairingKoszulPowerComplexIn (n : ℕ) (i j : ℤ) (h : i + j = 0) :
    letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
    (exactPairingKoszulPowerComplexIn X f n i j h).evaluation' =
      ∑ S : AlternatingCech.Idx r i,
        (Pi.π (fun _ : AlternatingCech.Idx r (-j) =>
            𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (idxNegEquiv i j h S) ⊗ₘ
          Pi.π (fun _ : AlternatingCech.Idx r i =>
            𝟙_ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) S) ≫
        (λ_ _).hom := by
  let _ : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  obtain rfl : i = -j := by omega
  change (exactPairingKoszulPowerComplexX X f n (-j)).evaluation' = _
  let _ : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  let _ : HasFiniteBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact (ExactPairing.evaluation_exactPairingCongr_biproduct_unit
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (A := AlternatingCech.Idx r (-j))).trans rfl

/-- The `(S, T)` entry of the Koszul differential `d^m`, for `S` of cardinality `m` and `T` of
cardinality `m + 1`: `± f_i^{n+1}` when `T = S ∪ {i}`, the sign being that of the alternating
Čech complex, and zero otherwise. -/
def koszulEntry (n : ℕ) {m : ℤ} (S : AlternatingCech.Idx r m)
    (T : AlternatingCech.Idx r (m + 1)) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ∑ k ∈ T.1.attach, if T.erase k = S then
    Cech.cechSign T.1 k.1 • koszulScalar X f (koszulExp n S.1 T.1) else 0

/-- The inclusion of the factor indexed by `S` into the degree-`m` term of the Koszul complex. -/
def koszulUnitι (n : ℕ) {m : ℤ} (S : AlternatingCech.Idx r m) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      ∏ᶜ fun T : AlternatingCech.Idx r m => (koszulPowerFunctor X f n).obj T.1 :=
  Pi.lift fun T => if T = S then 𝟙 _ else 0

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The `T`-th projection of the inclusion of the factor indexed by `S` is the identity when
`T = S` and zero otherwise. -/
@[reassoc (attr := simp)]
theorem koszulUnitι_π (n : ℕ) {m : ℤ} (S T : AlternatingCech.Idx r m) :
    koszulUnitι X f n S ≫
        Pi.π (fun T : AlternatingCech.Idx r m => (koszulPowerFunctor X f n).obj T.1) T =
      if T = S then 𝟙 _ else 0 :=
  Pi.lift_π _ _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The entries of the Koszul differential are its matrix coefficients. -/
theorem koszulUnitι_comp_koszulPowerComplex_d_comp_π (n : ℕ) (m : ℤ)
    (S : AlternatingCech.Idx r m) (T : AlternatingCech.Idx r (m + 1)) :
    koszulUnitι X f n S ≫ (koszulPowerComplex X f n).d m (m + 1) ≫
        Pi.π (fun T : AlternatingCech.Idx r (m + 1) => (koszulPowerFunctor X f n).obj T.1) T =
      koszulEntry X f n S T := by
  have hd : (koszulPowerComplex X f n).d m (m + 1) =
      AlternatingCech.d (koszulPowerFunctor X f n) m :=
    AlternatingCech.complex_d _ m
  have h3 : (koszulPowerComplex X f n).d m (m + 1) ≫
      Pi.π (fun T : AlternatingCech.Idx r (m + 1) => (koszulPowerFunctor X f n).obj T.1) T =
        ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 •
          AlternatingCech.proj (koszulPowerFunctor X f n) (T.erase k) (T.erase_subset k) :=
    (congrArg (· ≫ Pi.π _ T) hd).trans (AlternatingCech.d_comp_pi _ m T)
  refine (congrArg (fun φ => koszulUnitι X f n S ≫ φ) h3).trans ?_
  rw [Preadditive.comp_sum, koszulEntry]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.comp_zsmul, AlternatingCech.proj, koszulUnitι_π_assoc]
  split_ifs with h
  · subst h
    exact congrArg (fun φ => Cech.cechSign T.1 k.1 • φ)
      (Category.id_comp ((koszulPowerFunctor X f n).map (homOfLE (T.erase_subset k))))
  · exact (congrArg (fun φ => Cech.cechSign T.1 k.1 • φ)
      (zero_comp (X := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (f := (koszulPowerFunctor X f n).map (homOfLE (T.erase_subset k))))).trans (smul_zero _)

/-- **The matrix of the differential of the dual Koszul complex.** From degree `-(p+1)` to degree
`-p`, the component at a subset `S` of cardinality `p` is `(-1)^p` times the sum over the
subsets `T` of cardinality `p + 1` of the `T`-th projection followed by the `(S, T)` entry of the
Koszul differential. -/
theorem koszulPowerDualComplex_d_comp_π (n : ℕ) (p : ℤ) (S : AlternatingCech.Idx r p) :
    (koszulPowerDualComplex X f n).d (-(p + 1)) (-p) ≫
        Pi.π (fun T : AlternatingCech.Idx r (-(-p)) => (koszulPowerFunctor X f n).obj T.1)
          (idxNegEquiv p (-p) (by omega) S) =
      ((p.negOnePow : ℤˣ) : ℤ) • ∑ T : AlternatingCech.Idx r (p + 1),
        Pi.π (fun T : AlternatingCech.Idx r (-(-(p + 1))) => (koszulPowerFunctor X f n).obj T.1)
          (idxNegEquiv (p + 1) (-(p + 1)) (by omega) T) ≫ koszulEntry X f n S T := by
  let _ : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  let _ : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  have hd := koszulPowerDualComplex_d X f n p
  have hm := ExactPairing.mate_comp_π_of_evaluation
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (idxNegEquiv p (-p) (by omega)) (idxNegEquiv (p + 1) (-(p + 1)) (by omega))
    (exactPairingKoszulPowerComplexIn X f n p (-p) (by omega))
    (evaluation_exactPairingKoszulPowerComplexIn X f n p (-p) (by omega))
    (exactPairingKoszulPowerComplexIn X f n (p + 1) (-(p + 1)) (by omega))
    (evaluation_exactPairingKoszulPowerComplexIn X f n (p + 1) (-(p + 1)) (by omega))
    ((koszulPowerComplex X f n).d p (p + 1)) S
  refine (congrArg (fun φ => φ ≫ Pi.π _ _) hd).trans ?_
  refine (Linear.units_smul_comp (p.negOnePow) (ExactPairing.mate
    (exactPairingKoszulPowerComplexIn X f n p (-p) (by omega))
    (exactPairingKoszulPowerComplexIn X f n (p + 1) (-(p + 1)) (by omega))
    ((koszulPowerComplex X f n).d p (p + 1))) (Pi.π _ _)).trans ?_
  refine (Units.smul_def _ _).trans (congrArg (fun φ => ((p.negOnePow : ℤˣ) : ℤ) • φ)
    (hm.trans (Finset.sum_congr rfl fun T _ => ?_)))
  exact congrArg (fun φ => Pi.π _ _ ≫ φ)
    (koszulUnitι_comp_koszulPowerComplex_d_comp_π X f n p S T)

/-- **The matrix of a map of dual Koszul complexes.** For a morphism `φ : K_m ⟶ K_{m'}` of Koszul
complexes, the degree-`j` component of the induced map of dual Koszul complexes has, at a subset
`S` of cardinality `-j`, the transposed row of the matrix of `φ` in degree `-j`. -/
theorem koszulPowerDualComplexMap_f_comp_π (m m' : ℕ)
    (φ : koszulPowerComplex X f m ⟶ koszulPowerComplex X f m') (j : ℤ)
    (S : AlternatingCech.Idx r (-j)) :
    letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
    letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
    (CochainComplex.dualComplexMap (koszulPowerComplex X f m)
        (fun j => (koszulPowerComplex X f m).X (-j)) (exactPairingKoszulPowerComplexIn X f m)
        (koszulPowerComplex X f m') (fun j => (koszulPowerComplex X f m').X (-j))
        (exactPairingKoszulPowerComplexIn X f m') φ).f j ≫
      Pi.π (fun T : AlternatingCech.Idx r (-j) => (koszulPowerFunctor X f m).obj T.1) S =
      ∑ T : AlternatingCech.Idx r (-j),
        Pi.π (fun T : AlternatingCech.Idx r (-j) => (koszulPowerFunctor X f m').obj T.1) T ≫
          (koszulUnitι X f m S ≫ φ.f (-j) ≫
            Pi.π (fun T : AlternatingCech.Idx r (-j) => (koszulPowerFunctor X f m').obj T.1)
              T) := by
  let _ : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  let _ : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  exact ExactPairing.mate_comp_π_of_evaluation
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (idxNegEquiv (-j) j (by omega)) (idxNegEquiv (-j) j (by omega))
    (exactPairingKoszulPowerComplexIn X f m (-j) j (by omega))
    (evaluation_exactPairingKoszulPowerComplexIn X f m (-j) j (by omega))
    (exactPairingKoszulPowerComplexIn X f m' (-j) j (by omega))
    (evaluation_exactPairingKoszulPowerComplexIn X f m' (-j) j (by omega))
    (φ.f (-j)) S

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The matrix of the map between successive Koszul powers is diagonal: multiplication by `f_S`
at `S`. -/
theorem koszulUnitι_comp_koszulPowerComplexMap_f_comp_π (n : ℕ) (p : ℤ)
    (S T : AlternatingCech.Idx r p) :
    koszulUnitι X f n S ≫ (koszulPowerComplexMap X f n).f p ≫
        Pi.π (fun T : AlternatingCech.Idx r p => (koszulPowerFunctor X f (n + 1)).obj T.1) T =
      if T = S then koszulScalar X f (fun i => if i ∈ S.1 then 1 else 0) else 0 := by
  have h : (koszulPowerComplexMap X f n).f p ≫
      Pi.π (fun T : AlternatingCech.Idx r p => (koszulPowerFunctor X f (n + 1)).obj T.1) T =
        Pi.π (fun T : AlternatingCech.Idx r p => (koszulPowerFunctor X f n).obj T.1) T ≫
          koszulScalar X f (fun i => if i ∈ T.1 then 1 else 0) :=
    AlternatingCech.mapX_comp_pi (koszulPowerTrans X f n) T
  refine (congrArg (fun φ => koszulUnitι X f n S ≫ φ) h).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun φ => φ ≫ koszulScalar X f (fun i => if i ∈ T.1 then 1 else 0))
    (koszulUnitι_π X f n S T)).trans ?_
  split_ifs with hTS
  · subst hTS
    exact Category.id_comp (koszulScalar X f (fun i => if i ∈ T.1 then 1 else 0))
  · exact zero_comp

end AlgebraicGeometry.RingedSite

end
