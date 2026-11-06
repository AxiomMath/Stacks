module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantCoefficients
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualOfKoszulComplexMatrix
public import StacksFrontier.Homology.DerivedComplete.NoetherianKoszulProIso
public import StacksFrontier.RingTheory.Koszul.ExteriorBasisMatrix

/-!
# The dual Koszul complex on a constant ringed site is the constant Koszul cochain complex

Let `(𝒞, Λ̲)` be the constant ringed site of a commutative ring `Λ` and let `f_1, …, f_r ∈ Λ`.
The Koszul complex `K(Λ̲, f̲_1^{n+1}, …, f̲_r^{n+1})` of
`AlgebraicGeometry.RingedSite.koszulPowerComplex`, in degrees `0, …, r`, has as its dual the
complex `AlgebraicGeometry.RingedSite.koszulPowerDualComplex` in degrees `-r, …, 0`. This file
identifies that dual, naturally in `n`, with the constant sheaf of modules applied termwise to
the Koszul complex `K(Λ, f_1^{n+1}, …, f_r^{n+1})` of `Λ`-modules — the exterior-algebra complex
`Koszul.seqComplex`, placed in degrees `-r, …, 0` — whose tower over `n` is the one of
[Stacks, Tag 0921].

The degree `-q` terms are matched by the exterior basis `e_S` of `⋀^q Λ^r`, indexed by the
subsets `S` of cardinality `q`, against the factors of `∏_{|S| = q} Λ̲`, with the sign
`(-1)^{q(q-1)/2}`: the differential of the dual complex carries the extra sign `(-1)^q` of the
signed transpose, and the transition maps are diagonal in both complexes.

## Main definitions

* `AlgebraicGeometry.RingedSite.ringKoszulComplex`: the Koszul complex of `Λ`-modules in degrees
  `-r, …, 0`, and `AlgebraicGeometry.RingedSite.ringKoszulCoord`, the `S`-th coordinate of its
  degree `j` term.
* `AlgebraicGeometry.RingedSite.constantKoszulDualX`: the degreewise comparison.
* `AlgebraicGeometry.RingedSite.constantKoszulDualIso`: the isomorphism of complexes.

## Main results

* `AlgebraicGeometry.RingedSite.ringKoszulComplex_d_comp_coord` and
  `AlgebraicGeometry.RingedSite.ringKoszulTransition_f_comp_coord`: the differential and the
  transition maps of the Koszul complexes of `Λ`-modules in coordinates.
* `AlgebraicGeometry.RingedSite.constantKoszulDualX_comm`: the comparison commutes with the
  differentials.
* `AlgebraicGeometry.RingedSite.constantKoszulDualIso_naturality`: it is natural in `n`.

## Implementation notes

The coordinate at a subset `S` of cardinality `-j` is defined through the identification
`HomologicalComplex.extendXIso` of the degree-`j` term with the exterior power whose degree is
the cardinality of `S`, so that no case distinction on `j` is needed to define it; the
coordinates at two presentations of that degree agree by `subst`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ExteriorAlgebra

universe u

namespace AlgebraicGeometry.RingedSite

section Ring

variable {Λ : Type u} [CommRing Λ] {r : ℕ}

/-- The product of `g` over the order embedding `Fin q ↪ Fin r` enumerating a finset `s` of
cardinality `q` is the product of `g` over `s`. -/
theorem prod_orderEmbOfFin {M : Type*} [CommMonoid M] (s : Finset (Fin r)) {q : ℕ}
    (h : s.card = q) (g : Fin r → M) :
    ∏ k, g (s.orderEmbOfFin h k) = ∏ i ∈ s, g i := by
  rw [← Finset.prod_coe_sort s]
  exact Fintype.prod_equiv (s.orderIsoOfFin h).toEquiv _ _ fun k => rfl

/-- The transition map sends a basis vector `e_S` to `f_S e_S`. -/
theorem koszulPowerTransition_exteriorBasis (f : Fin r → Λ) (n q : ℕ)
    (S : Set.powersetCard (Fin r) q) :
    ((NoetherianKoszulProIso.koszulPowerTransition f (n + 1) n (Nat.le_succ n)).f q).hom
        (Koszul.exteriorBasis Λ r q S) =
      (∏ i ∈ S.1, f i) • Koszul.exteriorBasis Λ r q S := by
  rw [Koszul.exteriorBasis_apply]
  refine (NoetherianKoszulProIso.koszulPowerTransition_apply_ιMulti f (n + 1) n
    (Nat.le_succ n) q _).trans (Subtype.ext ?_)
  have hv : (fun (k : Fin q) (i : Fin r) => f i ^ (n + 1 - n) *
      (Pi.single (S.1.orderEmbOfFin (Set.powersetCard.card_eq S) k) (1 : Λ) : Fin r → Λ) i) =
      fun k => f (S.1.orderEmbOfFin (Set.powersetCard.card_eq S) k) •
        (Pi.single (S.1.orderEmbOfFin (Set.powersetCard.card_eq S) k) (1 : Λ) : Fin r → Λ) := by
    funext k i
    by_cases hi : i = S.1.orderEmbOfFin (Set.powersetCard.card_eq S) k
    · subst hi
      simp
    · simp [hi]
  simp only [hv, SetLike.val_smul]
  refine ((ExteriorAlgebra.ιMulti Λ q).toMultilinearMap.map_smul_univ _ _).trans ?_
  rw [prod_orderEmbOfFin]
  rfl

variable (g : Fin r → Λ)

/-- The Koszul complex `K(Λ, g_1^{n+1}, …, g_r^{n+1})` of `Λ`-modules, placed in degrees
`-r, …, 0`: the complexes of the tower `NoetherianKoszulProIso.koszulPowerSystem`. -/
abbrev ringKoszulComplex (n : ℕ) : CochainComplex (ModuleCat.{u} Λ) ℤ :=
  (Koszul.seqComplex (fun i => g i ^ (n + 1))).extend ComplexShape.embeddingDownNat

/-- The coordinate at `S` of the degree-`a` term `⋀^a Λ^r` of the Koszul complex. -/
def seqKoszulCoord (n a : ℕ) (S : Set.powersetCard (Fin r) a) :
    (Koszul.seqComplex (fun i => g i ^ (n + 1))).X a ⟶ ModuleCat.of Λ Λ :=
  ModuleCat.ofHom ((Koszul.exteriorBasis Λ r a).coord S)

/-- The coordinate at `S` of the degree `-a` term of `ringKoszulComplex`, through the
identification of that term with `⋀^a Λ^r`. -/
def ringKoszulCoord' (n a : ℕ) {j : ℤ} (hj : -(a : ℤ) = j) (S : Set.powersetCard (Fin r) a) :
    (ringKoszulComplex g n).X j ⟶ ModuleCat.of Λ Λ :=
  ((Koszul.seqComplex (fun i => g i ^ (n + 1))).extendXIso ComplexShape.embeddingDownNat
    hj).hom ≫ seqKoszulCoord g n a S

/-- **The coordinate at a subset `S` of cardinality `-j` of the degree `j` term of the Koszul
cochain complex of `Λ`-modules.** -/
def ringKoszulCoord (n : ℕ) {j : ℤ} (S : AlternatingCech.Idx r (-j)) :
    (ringKoszulComplex g n).X j ⟶ ModuleCat.of Λ Λ :=
  ringKoszulCoord' g n S.1.card (by have := S.2; omega) (Set.powersetCard.ofCard rfl)

/-- For a subset `S` of cardinality `a`, `ringKoszulCoord` at `S` is `ringKoszulCoord'` at `S`
computed through the presentation `-a = j` of the degree. -/
theorem ringKoszulCoord_eq (n a : ℕ) {j : ℤ} (hj : -(a : ℤ) = j)
    (S : AlternatingCech.Idx r (-j)) (hS : S.1.card = a) :
    ringKoszulCoord g n S = ringKoszulCoord' g n a hj (Set.powersetCard.ofCard hS) := by
  subst hS; rfl

/-- The coordinates of the degree `j` term of the Koszul cochain complex present it as the
product of copies of `Λ` indexed by the subsets of cardinality `-j`. -/
instance isIso_piLift_ringKoszulCoord (n : ℕ) (j : ℤ) :
    IsIso (Pi.lift fun S : AlternatingCech.Idx r (-j) => ringKoszulCoord g n S) := by
  by_cases hj : 0 < j
  · have h₁ : IsZero ((ringKoszulComplex g n).X j) :=
      HomologicalComplex.isZero_extend_X _ _ _ fun a => by
        change -(a : ℤ) ≠ j; omega
    have h₂ : IsZero (∏ᶜ fun _ : AlternatingCech.Idx r (-j) => ModuleCat.of Λ Λ) := by
      rw [IsZero.iff_id_eq_zero]
      exact Pi.hom_ext _ _ fun S => ((AlternatingCech.isEmpty_idx_of_neg (by omega)).elim S)
    exact ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, j = -(a : ℤ) := ⟨(-j).toNat, by omega⟩
    let e : AlternatingCech.Idx r (-(-(a : ℤ))) ≃ Set.powersetCard (Fin r) a :=
      { toFun := fun S => Set.powersetCard.ofCard (s := S.1) (by have := S.2; omega)
        invFun := fun S => ⟨S.1, by rw [Set.powersetCard.card_eq S]; omega⟩
        left_inv := fun S => rfl
        right_inv := fun S => rfl }
    let L : (ringKoszulComplex g n).X (-(a : ℤ)) ≃ₗ[Λ]
        (AlternatingCech.Idx r (-(-(a : ℤ))) → Λ) :=
      ((Koszul.seqComplex (fun i => g i ^ (n + 1))).extendXIso ComplexShape.embeddingDownNat
        (rfl : -(a : ℤ) = -(a : ℤ))).toLinearEquiv ≪≫ₗ
        (Koszul.exteriorBasis Λ r a).equivFun ≪≫ₗ LinearEquiv.funCongrLeft Λ Λ e
    have hcomp : IsIso ((Pi.lift fun S : AlternatingCech.Idx r (-(-(a : ℤ))) =>
        ringKoszulCoord g n S) ≫
          (ModuleCat.piIsoPi (fun _ : AlternatingCech.Idx r (-(-(a : ℤ))) =>
            ModuleCat.of Λ Λ)).hom) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      convert L.bijective using 1
      funext x S
      refine (congrArg (fun φ => φ x) (congrArg ModuleCat.Hom.hom
        (show (Pi.lift fun S : AlternatingCech.Idx r (-(-(a : ℤ))) => ringKoszulCoord g n S) ≫
          (ModuleCat.piIsoPi _).hom ≫ ModuleCat.ofHom (LinearMap.proj S) =
            ringKoszulCoord g n S by
          rw [ModuleCat.piIsoPi_hom_ker_subtype, Pi.lift_comp_π]))).trans ?_
      rw [ringKoszulCoord_eq g n a rfl S (by have := S.2; omega)]
      rfl
    exact IsIso.of_isIso_comp_right _ (ModuleCat.piIsoPi _).hom

/-- The `(S, T)` coefficient of the Koszul differential of `Λ`-modules: `± g_i^{n+1}` when
`T = S ∪ {i}`, with the sign of the alternating Čech complex, and zero otherwise. -/
def ringKoszulEntry (n : ℕ) {m : ℤ} (S : AlternatingCech.Idx r m)
    (T : AlternatingCech.Idx r (m + 1)) : Λ :=
  ∑ k ∈ T.1.attach, if T.erase k = S then
    ((Cech.cechSign T.1 k.1 : ℤ) : Λ) * ∏ i, g i ^ koszulExp n S.1 T.1 i else 0

/-- For `k ∈ T`, the monomial `∏ i, g_i ^ koszulExp n (T \ {k}) T i` is `g_k^{n+1}`. -/
theorem prod_pow_koszulExp_erase (n : ℕ) (T : Finset (Fin r)) (k : Fin r) (hk : k ∈ T) :
    ∏ i, g i ^ koszulExp n (T.erase k) T i = g k ^ (n + 1) := by
  rw [Finset.prod_eq_single k]
  · simp [koszulExp, hk]
  · intro i _ hi
    simp [koszulExp, hi]
  · simp

/-- The `S`-th coordinate of the exterior-power Koszul differential is the sum over `T` of the
`T`-th coordinate scaled by `ringKoszulEntry g n S T`. -/
private theorem exteriorBasis_coord_comp_koszul_d (n p : ℕ) (S : AlternatingCech.Idx r (p : ℤ)) :
    (Koszul.exteriorBasis Λ r p).coord
        (Set.powersetCard.ofCard (s := S.1) (by have := S.2; omega)) ∘ₗ
        Koszul.d (Koszul.seqDual fun i => g i ^ (n + 1)) p =
      ∑ T : AlternatingCech.Idx r ((p : ℤ) + 1), (ringKoszulEntry g n S T • LinearMap.id) ∘ₗ
        (Koszul.exteriorBasis Λ r (p + 1)).coord
          (Set.powersetCard.ofCard (s := T.1) (by have := T.2; omega)) := by
  rw [Koszul.coord_comp_d]
  let eq : AlternatingCech.Idx r ((p : ℤ) + 1) ≃ Set.powersetCard (Fin r) (p + 1) :=
    { toFun := fun T => Set.powersetCard.ofCard (s := T.1) (by have := T.2; omega)
      invFun := fun T => ⟨T.1, by rw [Set.powersetCard.card_eq T]; push_cast; rfl⟩
      left_inv := fun T => rfl
      right_inv := fun T => rfl }
  refine (Fintype.sum_equiv eq.symm _ _ fun T => ?_)
  rw [LinearMap.smul_comp, LinearMap.id_comp]
  congr 1
  simp only [ringKoszulEntry, Koszul.seqDual_single, Set.powersetCard.val_ofCard]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hiff : ((eq.symm T).erase k = S) ↔ T.1.erase k.1 = S.1 := Subtype.ext_iff
  by_cases h : T.1.erase k.1 = S.1
  · rw [ite_eq_left h, ite_eq_left (hiff.2 h)]
    congr 1
    show g k.1 ^ (n + 1) = ∏ i, g i ^ koszulExp n S.1 T.1 i
    rw [← h, prod_pow_koszulExp_erase g n T.1 k.1 k.2]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.1 h'))]

/-- **The Koszul differential of `Λ`-modules in coordinates.** -/
theorem ringKoszulComplex_d_comp_coord (n p : ℕ) (S : AlternatingCech.Idx r (p : ℤ)) :
    (ringKoszulComplex g n).d (-((p : ℤ) + 1)) (-(p : ℤ)) ≫
        ringKoszulCoord g n (idxNegEquiv (p : ℤ) (-(p : ℤ)) (by omega) S) =
      ∑ T : AlternatingCech.Idx r ((p : ℤ) + 1),
        ringKoszulCoord g n (idxNegEquiv ((p : ℤ) + 1) (-((p : ℤ) + 1)) (by omega) T) ≫
          ModuleCat.ofHom (ringKoszulEntry g n S T • LinearMap.id) := by
  let K := Koszul.seqComplex (fun i => g i ^ (n + 1))
  let e := ComplexShape.embeddingDownNat
  have h1 : e.f (p + 1) = -((p : ℤ) + 1) := by simp [e]
  have h0 : e.f p = -(p : ℤ) := rfl
  have hd : (ringKoszulComplex g n).d (-((p : ℤ) + 1)) (-(p : ℤ)) =
      (K.extendXIso e h1).hom ≫ K.d (p + 1) p ≫ (K.extendXIso e h0).inv :=
    HomologicalComplex.extend_d_eq K e h1 h0
  rw [hd, ringKoszulCoord_eq g n p h0 _
    (by have h := (idxNegEquiv (p : ℤ) (-(p : ℤ)) (by omega) S).2; omega)]
  have hT : ∀ T : AlternatingCech.Idx r ((p : ℤ) + 1),
      ringKoszulCoord g n (idxNegEquiv ((p : ℤ) + 1) (-((p : ℤ) + 1)) (by omega) T) =
        (K.extendXIso e h1).hom ≫ seqKoszulCoord g n (p + 1)
          (Set.powersetCard.ofCard (s := T.1) (by have := T.2; omega)) :=
    fun T => ringKoszulCoord_eq g n (p + 1) h1 _ _
  simp only [hT, Category.assoc, ← Preadditive.comp_sum]
  show (K.extendXIso e h1).hom ≫ K.d (p + 1) p ≫ (K.extendXIso e h0).inv ≫
      (K.extendXIso e h0).hom ≫ _ = _
  simp only [Iso.inv_hom_id_assoc]
  refine (cancel_epi (K.extendXIso e h1).hom).2 ?_
  rw [Koszul.seqComplex_d]
  refine ModuleCat.hom_ext ?_
  simp only [seqKoszulCoord, ModuleCat.hom_sum]
  exact (exteriorBasis_coord_comp_koszul_d g n p S).trans (Finset.sum_congr rfl fun T _ => rfl)

/-- The transition map `K(Λ, g^{n+2}) ⟶ K(Λ, g^{n+1})` of the tower of [Stacks, Tag 0921], placed
in degrees `-r, …, 0`. -/
abbrev ringKoszulTransition (n : ℕ) : ringKoszulComplex g (n + 1) ⟶ ringKoszulComplex g n :=
  HomologicalComplex.extendMap
    (NoetherianKoszulProIso.koszulPowerTransition g (n + 1) n (Nat.le_succ n))
    ComplexShape.embeddingDownNat

/-- The transition map is diagonal in coordinates: multiplication by `g_S` at `S`. -/
theorem ringKoszulTransition_f_comp_coord (n : ℕ) (j : ℤ) (S : AlternatingCech.Idx r (-j)) :
    (ringKoszulTransition g n).f j ≫ ringKoszulCoord g n S =
      ringKoszulCoord g (n + 1) S ≫ ModuleCat.ofHom ((∏ i ∈ S.1, g i) • LinearMap.id) := by
  have hj : ComplexShape.embeddingDownNat.f S.1.card = j := by
    have := S.2
    simp only [ComplexShape.embeddingDownNat_f]
    omega
  rw [ringKoszulCoord_eq g n S.1.card hj S rfl, ringKoszulCoord_eq g (n + 1) S.1.card hj S rfl,
    ringKoszulTransition, HomologicalComplex.extendMap_f _ _ hj]
  simp only [ringKoszulCoord', Category.assoc, Iso.inv_hom_id_assoc]
  refine congrArg (fun φ => (HomologicalComplex.extendXIso
    (Koszul.seqComplex (fun i => g i ^ (n + 1 + 1))) ComplexShape.embeddingDownNat hj).hom ≫ φ) ?_
  refine ModuleCat.hom_ext ((Koszul.exteriorBasis Λ r S.1.card).ext fun T => ?_)
  show (Koszul.exteriorBasis Λ r S.1.card).coord _
      (((NoetherianKoszulProIso.koszulPowerTransition g (n + 1) n (Nat.le_succ n)).f
        S.1.card).hom (Koszul.exteriorBasis Λ r S.1.card T)) =
    (∏ i ∈ S.1, g i) • (Koszul.exteriorBasis Λ r S.1.card).coord _
      (Koszul.exteriorBasis Λ r S.1.card T)
  rw [koszulPowerTransition_exteriorBasis, map_smul]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, Finsupp.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

end Ring

/-- In a preadditive category, if `z * w = 1` then `z • ((w • (a ≫ b)) ≫ c) = a ≫ b ≫ c`. -/
theorem _root_.CategoryTheory.zsmul_zsmul_comp_comp {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {A B D E : 𝒞} (z w : ℤ) (h : z * w = 1) (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) :
    z • ((w • (a ≫ b)) ≫ c) = a ≫ b ≫ c := by
  rw [Preadditive.zsmul_comp, smul_smul, h, one_smul, Category.assoc]

section Sheaf

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]
  {r : ℕ} (g : Fin r → Λ)

/-- The sign `(-1)^{a(a-1)/2}` by which the degree `-a` terms of the two dual Koszul complexes are
matched. -/
def koszulDualSign : ℕ → ℤˣ
  | 0 => 1
  | a + 1 => (-1) ^ a * koszulDualSign a

/-- The recursion defining `koszulDualSign`. -/
theorem koszulDualSign_succ (a : ℕ) : koszulDualSign (a + 1) = (-1) ^ a * koszulDualSign a :=
  rfl

/-- `Λ̲` as the constant sheaf of modules on `Λ`, twisted by a sign. -/
def constantModuleFunctorUnitIsoSign (σ : ℤˣ) :
    (constantModuleFunctor J Λ).obj (ModuleCat.of Λ Λ) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) where
  hom := (σ : ℤ) • (constantModuleFunctorUnitIso J Λ).hom
  inv := (σ : ℤ) • (constantModuleFunctorUnitIso J Λ).inv
  hom_inv_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul, Iso.inv_hom_id]

/-- **The degreewise comparison** between the constant sheaf of modules applied to the Koszul
cochain complex of `Λ`-modules and the dual Koszul complex on the constant ringed site: at the
factor indexed by `S`, the `S`-th coordinate followed by `Λ̲ = Λ̲` with the sign of `|S|`. -/
def constantKoszulDualX (n : ℕ) (j : ℤ) :
    (constantModuleFunctor J Λ).obj ((ringKoszulComplex g n).X j) ⟶
      ∏ᶜ fun S : AlternatingCech.Idx r (-j) =>
        (koszulPowerFunctor (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n).obj S.1 :=
  Pi.lift fun S : AlternatingCech.Idx r (-j) =>
    (constantModuleFunctor J Λ).map (ringKoszulCoord g n S) ≫
      (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign S.1.card)).hom

/-- The component of `constantKoszulDualX` at `S` is the image of the `S`-th coordinate followed
by `Λ̲ = Λ̲` with the sign `koszulDualSign |S|`. -/
@[reassoc]
theorem constantKoszulDualX_π (n : ℕ) (j : ℤ) (S : AlternatingCech.Idx r (-j)) :
    constantKoszulDualX J Λ g n j ≫ Pi.π (fun T : AlternatingCech.Idx r (-j) =>
        (koszulPowerFunctor (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n).obj T.1)
        S =
      (constantModuleFunctor J Λ).map (ringKoszulCoord g n S) ≫
        (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign S.1.card)).hom :=
  Pi.lift_comp_π _ _

/-- The degreewise comparison `constantKoszulDualX` is an isomorphism. -/
instance isIso_constantKoszulDualX (n : ℕ) (j : ℤ) : IsIso (constantKoszulDualX J Λ g n j) := by
  let Φ := constantModuleFunctor J Λ
  have hF : IsLimit (Fan.mk ((ringKoszulComplex g n).X j)
      fun S : AlternatingCech.Idx r (-j) => ringKoszulCoord g n S) :=
    @Fan.isLimitOfIsIsoPiLift _ _ _ _ _ _ (isIso_piLift_ringKoszulCoord g n j)
  have hΦ := (isLimitMapConeFanMkEquiv Φ _ _) (isLimitOfPreserves Φ hF)
  have hiso : IsIso (Pi.lift fun S : AlternatingCech.Idx r (-j) =>
      Φ.map (ringKoszulCoord g n S)) := (Fan.nonempty_isLimit_iff_isIso_piLift _).1 ⟨hΦ⟩
  let p : ∀ S : AlternatingCech.Idx r (-j), Φ.obj (ModuleCat.of Λ Λ) ⟶
      (koszulPowerFunctor (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n).obj S.1 :=
    fun S => (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign S.1.card)).hom
  have hp : ∀ S, IsIso (p S) := fun S => Iso.isIso_hom _
  have h : constantKoszulDualX J Λ g n j =
      (Pi.lift fun S : AlternatingCech.Idx r (-j) => Φ.map (ringKoszulCoord g n S)) ≫
        Limits.Pi.map p := by
    refine Pi.hom_ext _ _ fun S => (constantKoszulDualX_π J Λ g n j S).trans ?_
    rw [Category.assoc, Limits.Pi.map_π, Pi.lift_π_assoc]
    rfl
  rw [h]
  infer_instance

/-- On the constant ringed site with the constant global sections `g̲_i`, the `(S, T)`
coefficient `koszulEntry` is the constant scalar of `ringKoszulEntry g n S T`. -/
theorem koszulEntry_constant (n : ℕ) {m : ℤ} (S : AlternatingCech.Idx r m)
    (T : AlternatingCech.Idx r (m + 1)) :
    koszulEntry (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n S T =
      constantScalar J Λ (ringKoszulEntry g n S T) := by
  rw [koszulEntry, ringKoszulEntry, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [koszulScalar_constantGlobalSection, ← zsmul_eq_mul, map_zsmul]
    rfl
  · rw [map_zero]

/-- The signed identification `constantModuleFunctorUnitIsoSign` intertwines multiplication by
`a` on `Λ` with the constant scalar `constantScalar J Λ a`. -/
theorem constantModuleFunctorUnitIsoSign_hom_comp_constantScalar (σ : ℤˣ) (a : Λ) :
    (constantModuleFunctor J Λ).map (ModuleCat.ofHom (a • LinearMap.id)) ≫
        (constantModuleFunctorUnitIsoSign J Λ σ).hom =
      (constantModuleFunctorUnitIsoSign J Λ σ).hom ≫ constantScalar J Λ a := by
  have h := constantModuleFunctor_map_smul_unitIso J Λ a
  show (constantModuleFunctor J Λ).map (a • 𝟙 (ModuleCat.of Λ Λ)) ≫
      ((σ : ℤ) • (constantModuleFunctorUnitIso J Λ).hom) =
    ((σ : ℤ) • (constantModuleFunctorUnitIso J Λ).hom) ≫ constantScalar J Λ a
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, h]
  rfl

/-- The identification twisted by `koszulDualSign (p + 1)` is `(-1)^p` times the one twisted by
`koszulDualSign p`. -/
theorem koszulDualSign_hom_succ (p : ℕ) :
    (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign (p + 1))).hom =
      (((-1 : ℤˣ) ^ p : ℤˣ) : ℤ) •
        (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign p)).hom := by
  show ((koszulDualSign (p + 1) : ℤˣ) : ℤ) • (constantModuleFunctorUnitIso J Λ).hom =
    (((-1 : ℤˣ) ^ p : ℤˣ) : ℤ) • (((koszulDualSign p : ℤˣ) : ℤ) •
      (constantModuleFunctorUnitIso J Λ).hom)
  rw [smul_smul, koszulDualSign_succ, Units.val_mul]

/-- The component at `S` of the degreewise comparison precomposed with the image of `x`, in terms
of the coordinate at `S`. -/
private theorem map_comp_constantKoszulDualX_comp_π {n : ℕ} {j : ℤ} {M : ModuleCat.{u} Λ}
    (x : M ⟶ (ringKoszulComplex g n).X j) (S : AlternatingCech.Idx r (-j)) :
    (constantModuleFunctor J Λ).map x ≫ constantKoszulDualX J Λ g n j ≫ Pi.π _ S =
      (constantModuleFunctor J Λ).map (x ≫ ringKoszulCoord g n S) ≫
        (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign S.1.card)).hom := by
  rw [constantKoszulDualX_π, Functor.map_comp, Category.assoc]
  rfl

/-- The component at `S` of the constant sheaf of modules applied to the Koszul differential,
followed by the degreewise comparison, in terms of the coordinates. -/
private theorem map_ringKoszulComplex_d_comp_constantKoszulDualX_comp_π (n p : ℕ)
    (S : AlternatingCech.Idx r (p : ℤ)) :
    ((constantModuleFunctor J Λ).map ((ringKoszulComplex g n).d (-((p : ℤ) + 1)) (-(p : ℤ))) ≫
      constantKoszulDualX J Λ g n (-(p : ℤ))) ≫
        Pi.π _ (idxNegEquiv (p : ℤ) (-(p : ℤ)) (by omega) S) =
      ∑ T : AlternatingCech.Idx r ((p : ℤ) + 1),
        (constantModuleFunctor J Λ).map
          (ringKoszulCoord g n (idxNegEquiv ((p : ℤ) + 1) (-((p : ℤ) + 1)) (by omega) T)) ≫
          (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign p)).hom ≫
            constantScalar J Λ (ringKoszulEntry g n S T) := by
  have hS : (idxNegEquiv (p : ℤ) (-(p : ℤ)) (by omega) S).1.card = p := by
    have h := S.2
    simp only [idxNegEquiv_val]
    omega
  rw [Category.assoc, map_comp_constantKoszulDualX_comp_π, hS]
  rw [ringKoszulComplex_d_comp_coord, Functor.map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Functor.map_comp, Category.assoc, constantModuleFunctorUnitIsoSign_hom_comp_constantScalar]

/-- The component at `S` of the degreewise comparison followed by the differential of the dual
Koszul complex, in terms of the coordinates. -/
private theorem constantKoszulDualX_comp_koszulPowerDualComplex_d_comp_π (n p : ℕ)
    (S : AlternatingCech.Idx r (p : ℤ)) :
    (constantKoszulDualX J Λ g n (-((p : ℤ) + 1)) ≫
      (koszulPowerDualComplex (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n).d
        (-((p : ℤ) + 1)) (-(p : ℤ))) ≫
        Pi.π _ (idxNegEquiv (p : ℤ) (-(p : ℤ)) (by omega) S) =
      ∑ T : AlternatingCech.Idx r ((p : ℤ) + 1),
        (constantModuleFunctor J Λ).map
          (ringKoszulCoord g n (idxNegEquiv ((p : ℤ) + 1) (-((p : ℤ) + 1)) (by omega) T)) ≫
          (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign p)).hom ≫
            constantScalar J Λ (ringKoszulEntry g n S T) := by
  have hT : ∀ T : AlternatingCech.Idx r ((p : ℤ) + 1),
      (idxNegEquiv ((p : ℤ) + 1) (-((p : ℤ) + 1)) (by omega) T).1.card = p + 1 := fun T => by
    have h := T.2
    simp only [idxNegEquiv_val]
    omega
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun φ => constantKoszulDualX J Λ g n (-((p : ℤ) + 1)) ≫ φ)
    (koszulPowerDualComplex_d_comp_π (constant J Λ) (fun i => constantGlobalSection J Λ (g i))
      n (p : ℤ) S)).trans ?_
  refine (Preadditive.comp_zsmul _ _ _).trans ?_
  refine (congrArg (fun φ => ((((p : ℤ)).negOnePow : ℤˣ) : ℤ) • φ)
    (Preadditive.comp_sum _ _ _)).trans ?_
  refine Finset.smul_sum.trans (Finset.sum_congr rfl fun T _ => ?_)
  have e2 := constantKoszulDualX_π_assoc J Λ g n (-((p : ℤ) + 1))
    (idxNegEquiv ((p : ℤ) + 1) (-((p : ℤ) + 1)) (by omega) T)
    (koszulEntry (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n S T)
  refine (congrArg (fun φ => ((((p : ℤ)).negOnePow : ℤˣ) : ℤ) • φ) e2).trans ?_
  rw [hT, koszulDualSign_hom_succ, koszulEntry_constant, Preadditive.comp_zsmul]
  have hsign : ((((p : ℤ)).negOnePow : ℤˣ) : ℤ) * (((-1 : ℤˣ) ^ p : ℤˣ) : ℤ) = 1 := by
    rw [Int.negOnePow_def, zpow_natCast, ← Units.val_mul, ← mul_pow, Int.units_mul_self,
      one_pow, Units.val_one]
  exact zsmul_zsmul_comp_comp _ _ hsign _ _ _

/-- **The degreewise comparison commutes with the differentials.** -/
theorem constantKoszulDualX_comm (n : ℕ) (i j : ℤ) (hij : i + 1 = j) :
    constantKoszulDualX J Λ g n i ≫
        (koszulPowerDualComplex (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n).d i j =
      (constantModuleFunctor J Λ).map ((ringKoszulComplex g n).d i j) ≫
        constantKoszulDualX J Λ g n j := by
  by_cases hj : 0 < j
  · exact (isZero_koszulPowerDualComplex_X_of_pos _ _ n hj).eq_of_tgt _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, j = -(p : ℤ) := ⟨(-j).toNat, by omega⟩
  obtain rfl : i = -((p : ℤ) + 1) := by omega
  refine Pi.hom_ext _ _ fun S' => ?_
  let S : AlternatingCech.Idx r (p : ℤ) := ⟨S'.1, by have := S'.2; omega⟩
  show _ ≫ Pi.π _ (idxNegEquiv (p : ℤ) (-(p : ℤ)) (by omega) S) =
    _ ≫ Pi.π _ (idxNegEquiv (p : ℤ) (-(p : ℤ)) (by omega) S)
  clear_value S
  exact (constantKoszulDualX_comp_koszulPowerDualComplex_d_comp_π J Λ g n p S).trans
    (map_ringKoszulComplex_d_comp_constantKoszulDualX_comp_π J Λ g n p S).symm

/-- **The dual Koszul complex on the constant ringed site is the constant sheaf of modules applied
to the Koszul cochain complex of `Λ`-modules.** -/
def constantKoszulDualIso (n : ℕ) :
    ((constantModuleFunctor J Λ).mapHomologicalComplex _).obj (ringKoszulComplex g n) ≅
      koszulPowerDualComplex (constant J Λ) (fun i => constantGlobalSection J Λ (g i)) n :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => @asIso _ _ _ _ (constantKoszulDualX J Λ g n j) (isIso_constantKoszulDualX J Λ g n j))
    (constantKoszulDualX_comm J Λ g n)

/-- `∏ i, g_i ^ [i ∈ S] = ∏_{i ∈ S} g_i`. -/
theorem prod_pow_indicator (S : Finset (Fin r)) :
    ∏ i, g i ^ (if i ∈ S then 1 else 0) = ∏ i ∈ S, g i := by
  rw [← Finset.prod_subset (Finset.subset_univ S) (fun i _ hi => by rw [ite_eq_right hi, pow_zero])]
  exact Finset.prod_congr rfl fun i hi => by rw [ite_eq_left hi, pow_one]

/-- The component at `S` of the identification at `n + 1` followed by the transition map of the
tower of dual Koszul complexes, in terms of the coordinates. -/
private theorem constantKoszulDualIso_hom_comp_koszulPowerDualComplexSystem_map_f_comp_π (n : ℕ)
    (j : ℤ) (S : AlternatingCech.Idx r (-j)) :
    ((constantKoszulDualIso J Λ g (n + 1)).hom ≫
      (koszulPowerDualComplexSystem (constant J Λ)
        (fun i => constantGlobalSection J Λ (g i))).map (homOfLE (Nat.le_succ n)).op).f j ≫
        Pi.π _ S =
      (constantModuleFunctor J Λ).map (ringKoszulCoord g (n + 1) S) ≫
        (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign S.1.card)).hom ≫
          constantScalar J Λ (∏ i ∈ S.1, g i) := by
  let f' := fun i => constantGlobalSection J Λ (g i)
  have hsys : (koszulPowerDualComplexSystem (constant J Λ) f').map (homOfLE (Nat.le_succ n)).op =
      let : MonoidalCategory (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)) :=
        Stacks.SheafOfModules.Strict.monoidalCategory (constant J Λ).O.obj
          (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf (constant J Λ).O)
      let : MonoidalPreadditive (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)) :=
        Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf (constant J Λ).O
      CochainComplex.dualComplexMap (koszulPowerComplex (constant J Λ) f' n)
        (fun j => (koszulPowerComplex (constant J Λ) f' n).X (-j))
        (exactPairingKoszulPowerComplexIn (constant J Λ) f' n)
        (koszulPowerComplex (constant J Λ) f' (n + 1))
        (fun j => (koszulPowerComplex (constant J Λ) f' (n + 1)).X (-j))
        (exactPairingKoszulPowerComplexIn (constant J Λ) f' (n + 1))
        (koszulPowerComplexMap (constant J Λ) f' n) := by
    rw [koszulPowerDualComplexSystem_map]
    congr 1
    exact Functor.ofSequence_map_homOfLE_succ _ n
  show ((constantKoszulDualIso J Λ g (n + 1)).hom ≫
      (koszulPowerDualComplexSystem (constant J Λ) f').map (homOfLE (Nat.le_succ n)).op).f j ≫
        Pi.π _ S = _
  refine (Category.assoc _ _ _).trans ?_
  rw [hsys]
  refine (congrArg (fun φ => constantKoszulDualX J Λ g (n + 1) j ≫ φ)
    (koszulPowerDualComplexMap_f_comp_π (constant J Λ) f' n (n + 1)
      (koszulPowerComplexMap (constant J Λ) f' n) j S)).trans ?_
  refine (Preadditive.comp_sum _ _ _).trans ?_
  rw [Finset.sum_eq_single S]
  · have e3 := koszulUnitι_comp_koszulPowerComplexMap_f_comp_π (constant J Λ) f' n (-j) S S
    rw [ite_eq_left rfl, koszulScalar_constantGlobalSection, prod_pow_indicator] at e3
    refine (congrArg (fun φ => constantKoszulDualX J Λ g (n + 1) j ≫ Pi.π _ S ≫ φ) e3).trans ?_
    exact (constantKoszulDualX_π_assoc J Λ g (n + 1) j S _).trans (Category.assoc _ _ _)
  · intro T _ hTS
    have e3 := koszulUnitι_comp_koszulPowerComplexMap_f_comp_π (constant J Λ) f' n (-j) S T
    rw [ite_eq_right hTS] at e3
    refine (congrArg (fun φ => constantKoszulDualX J Λ g (n + 1) j ≫ Pi.π _ T ≫ φ) e3).trans ?_
    exact (congrArg (fun φ => constantKoszulDualX J Λ g (n + 1) j ≫ φ) comp_zero).trans
      comp_zero
  · simp

/-- **The identification is natural in `n`**: it carries the transition maps of the tower of
[Stacks, Tag 0921] to those of the tower of dual Koszul complexes. -/
theorem constantKoszulDualIso_naturality (n : ℕ) :
    ((constantModuleFunctor J Λ).mapHomologicalComplex _).map (ringKoszulTransition g n) ≫
        (constantKoszulDualIso J Λ g n).hom =
      (constantKoszulDualIso J Λ g (n + 1)).hom ≫
        (koszulPowerDualComplexSystem (constant J Λ)
          (fun i => constantGlobalSection J Λ (g i))).map (homOfLE (Nat.le_succ n)).op := by
  let Φ := constantModuleFunctor J Λ
  let σ := fun a : ℕ => (constantModuleFunctorUnitIsoSign J Λ (koszulDualSign a)).hom
  refine HomologicalComplex.hom_ext _ _ fun j => Pi.hom_ext _ _ fun S => ?_
  have hL : ((Φ.mapHomologicalComplex _).map (ringKoszulTransition g n) ≫
      (constantKoszulDualIso J Λ g n).hom).f j ≫ Pi.π _ S =
        Φ.map (ringKoszulCoord g (n + 1) S) ≫ σ S.1.card ≫
          constantScalar J Λ (∏ i ∈ S.1, g i) := by
    change Φ.map ((ringKoszulTransition g n).f j) ≫ constantKoszulDualX J Λ g n j ≫ Pi.π _ S = _
    rw [map_comp_constantKoszulDualX_comp_π, ringKoszulTransition_f_comp_coord, Φ.map_comp,
      Category.assoc, constantModuleFunctorUnitIsoSign_hom_comp_constantScalar]
  exact hL.trans
    (constantKoszulDualIso_hom_comp_koszulPowerDualComplexSystem_map_f_comp_π J Λ g n j S).symm

end Sheaf

end AlgebraicGeometry.RingedSite

end
