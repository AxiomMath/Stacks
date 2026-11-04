module

public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Algebra.Homology.HomotopyCategory.HomComplexQuasiIso
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Flat base change of the Hom complex

Let `ρ : A ⟶ R` be a map of commutative rings, `P` a complex of `A`-modules and `I` a complex of
`A`-modules. Write `R ⊗_A I` for the complex `I` with scalars extended to `R` and then restricted
back to `A`. This file constructs the base-change map of Hom complexes

`θ : R ⊗_A Hom^•_A(P, I) ⟶ Hom^•_A(P, R ⊗_A I)`,  `b ⊗ c ↦ b · (c followed by 1 ⊗ -)`,

as a morphism of complexes of abelian groups, natural in `I`.

## Main definitions

* `Stacks.FlatBaseChangeHom.RE`: the functor `M ↦ R ⊗_A M`, read as an `A`-module.
* `Stacks.FlatBaseChangeHom.mulMap`: multiplication by an element of `R`, as a natural
  endomorphism of `RE`.
* `Stacks.FlatBaseChangeHom.theta`: the base-change map `θ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex TensorProduct

universe u

namespace Stacks.FlatBaseChangeHom

variable {A R : Type u} [CommRing A] [CommRing R] (ρ : A →+* R)

/-- Extension of scalars along `ρ`, read back as an `A`-module: `M ↦ R ⊗_A M`. -/
abbrev RE : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  ModuleCat.extendScalars ρ ⋙ ModuleCat.restrictScalars ρ

/-- The unit `M ⟶ R ⊗_A M`, `m ↦ 1 ⊗ m`. -/
abbrev unitRE : 𝟭 (ModuleCat.{u} A) ⟶ RE ρ := (ModuleCat.extendRestrictScalarsAdj ρ).unit

/-- Multiplication by `b ∈ R` on `R ⊗_A M`, as an `A`-linear map. -/
def mulApp (b : R) (M : ModuleCat.{u} A) : (RE ρ).obj M ⟶ (RE ρ).obj M :=
  (ModuleCat.restrictScalars ρ).map
    (ModuleCat.ofHom (X := (ModuleCat.extendScalars ρ).obj M)
      (Y := (ModuleCat.extendScalars ρ).obj M) (LinearMap.lsmul R _ b))

/-- Multiplication by `b ∈ R`, as a natural endomorphism of `M ↦ R ⊗_A M`. -/
def mulMap (b : R) : RE ρ ⟶ RE ρ where
  app := mulApp ρ b
  naturality {M N} f := by
    ext x
    exact (map_smul ((ModuleCat.extendScalars ρ).map f).hom b
      (show (ModuleCat.extendScalars ρ).obj M from x)).symm

/-- Multiplication on `R ⊗_A M` is additive in the scalar: `(b + b') · = b · + b' ·`. -/
lemma mulApp_add (b b' : R) (M : ModuleCat.{u} A) :
    mulApp ρ (b + b') M = mulApp ρ b M + mulApp ρ b' M := by
  ext x
  exact add_smul b b' (show (ModuleCat.extendScalars ρ).obj M from x)

/-- Multiplication by `b * b'` on `R ⊗_A M` is multiplication by `b'` followed by `b`. -/
lemma mulApp_mul (b b' : R) (M : ModuleCat.{u} A) :
    mulApp ρ (b * b') M = mulApp ρ b' M ≫ mulApp ρ b M := by
  ext x
  exact mul_smul b b' (show (ModuleCat.extendScalars ρ).obj M from x)

/-- Multiplication by `1` on `R ⊗_A M` is the identity. -/
lemma mulApp_one (M : ModuleCat.{u} A) : mulApp ρ 1 M = 𝟙 _ := by
  ext x
  exact one_smul R (show (ModuleCat.extendScalars ρ).obj M from x)

/-- Multiplication by `ρ a` on `R ⊗_A M` is the `A`-scalar action of `a`. -/
lemma mulApp_algebraMap (a : A) (M : ModuleCat.{u} A) : mulApp ρ (ρ a) M = a • 𝟙 _ := by
  ext x
  rfl

/-- The complex `R ⊗_A I`. -/
abbrev REc (I : CochainComplex (ModuleCat.{u} A) ℤ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  ((RE ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I

/-- The unit `I ⟶ R ⊗_A I`. -/
abbrev unitREc (I : CochainComplex (ModuleCat.{u} A) ℤ) : I ⟶ REc ρ I :=
  (NatTrans.mapHomologicalComplex (unitRE ρ) (ComplexShape.up ℤ)).app I

/-- Multiplication by `b ∈ R` on `R ⊗_A I`. -/
abbrev mulREc (b : R) (I : CochainComplex (ModuleCat.{u} A) ℤ) : REc ρ I ⟶ REc ρ I :=
  (NatTrans.mapHomologicalComplex (mulMap ρ b) (ComplexShape.up ℤ)).app I

variable (P I : CochainComplex (ModuleCat.{u} A) ℤ)

/-- The source of `θ`: the complex of abelian groups `R ⊗_A Hom^•_A(P, I)`. -/
abbrev S₀ : CochainComplex AddCommGrpCat.{u} ℤ :=
  ((ModuleCat.extendScalars ρ ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR A P I)

/-- The target of `θ`: the complex of abelian groups `Hom^•_A(P, R ⊗_A I)`. -/
abbrev T₀ : CochainComplex AddCommGrpCat.{u} ℤ := P.HomComplex (REc ρ I)

/-- The cochain `b · (c followed by 1 ⊗ -)`. -/
def thetaCochain {n : ℤ} (b : R) (c : Cochain P I n) : Cochain P (REc ρ I) n :=
  c.comp (Cochain.ofHom (unitREc ρ I ≫ mulREc ρ b I)) (add_zero n)

/-- The component of `thetaCochain ρ P I b c` from `P^p` to `R ⊗_A I^q` is `c^{p,q}`
followed by `m ↦ 1 ⊗ m` and multiplication by `b`. -/
lemma thetaCochain_v {n : ℤ} (b : R) (c : Cochain P I n) (p q : ℤ) (hpq : p + n = q) :
    (thetaCochain ρ P I b c).v p q hpq =
      c.v p q hpq ≫ (unitRE ρ).app (I.X q) ≫ mulApp ρ b (I.X q) := by
  simp [thetaCochain, Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q)]
  rfl

/-- `thetaCochain` is additive in the scalar `b`. -/
lemma thetaCochain_add_left {n : ℤ} (b b' : R) (c : Cochain P I n) :
    thetaCochain ρ P I (b + b') c = thetaCochain ρ P I b c + thetaCochain ρ P I b' c := by
  ext p q hpq
  simp only [Cochain.add_v, thetaCochain_v, mulApp_add, Preadditive.comp_add]

/-- `thetaCochain ρ P I (ρ a * b) c = a • thetaCochain ρ P I b c`. -/
lemma thetaCochain_smul_left {n : ℤ} (a : A) (b : R) (c : Cochain P I n) :
    thetaCochain ρ P I (ρ a * b) c = a • thetaCochain ρ P I b c := by
  ext p q hpq
  simp only [Cochain.smul_v, thetaCochain_v, mulApp_mul, mulApp_algebraMap, Linear.comp_smul,
    Category.comp_id]

/-- `thetaCochain` is additive in the cochain `c`. -/
lemma thetaCochain_add_right {n : ℤ} (b : R) (c c' : Cochain P I n) :
    thetaCochain ρ P I b (c + c') = thetaCochain ρ P I b c + thetaCochain ρ P I b c' :=
  Cochain.add_comp _ _ _ _

/-- `thetaCochain` is `A`-linear in the cochain `c`. -/
lemma thetaCochain_smul_right {n : ℤ} (a : A) (b : R) (c : Cochain P I n) :
    thetaCochain ρ P I b (a • c) = a • thetaCochain ρ P I b c :=
  Cochain.smul_comp _ _ _ _

/-- `thetaCochain` commutes with the differential `δ` of the Hom complexes. -/
lemma thetaCochain_δ {n m : ℤ} (b : R) (c : Cochain P I n) :
    thetaCochain ρ P I b (δ n m c) = δ n m (thetaCochain ρ P I b c) :=
  (δ_comp_ofHom c _ m).symm

/-- `R`, read as an `A`-module, in the spelling of `ModuleCat.extendScalars`. -/
abbrev RR : ModuleCat.{u} A := (ModuleCat.restrictScalars ρ).obj (ModuleCat.of R R)

/-- `θ` in degree `n`, as an `A`-linear map `R ⊗_A Hom^n_A(P, I) ⟶ Hom^n_A(P, R ⊗_A I)`. -/
def thetaLin (n : ℤ) :
    RR ρ ⊗[A] (CochainComplex.HomComplexR A P I).X n →ₗ[A] Cochain P (REc ρ I) n :=
  TensorProduct.lift
    { toFun := fun b =>
        { toFun := fun c => thetaCochain ρ P I b c
          map_add' := thetaCochain_add_right ρ P I b
          map_smul' := fun a c => thetaCochain_smul_right ρ P I a b c }
      map_add' := fun b b' => LinearMap.ext fun c => thetaCochain_add_left ρ P I b b' c
      map_smul' := fun a b => LinearMap.ext fun c => thetaCochain_smul_left ρ P I a b c }

/-- `thetaLin ρ P I n (b ⊗ c) = thetaCochain ρ P I b c`. -/
lemma thetaLin_tmul (n : ℤ) (b : RR ρ) (c : (CochainComplex.HomComplexR A P I).X n) :
    thetaLin ρ P I n (b ⊗ₜ c) = thetaCochain ρ P I b c := rfl

/-- `thetaLin` commutes with the differentials of `R ⊗_A Hom^•_A(P, I)` and
`Hom^•_A(P, R ⊗_A I)`. -/
lemma thetaLin_δ (n m : ℤ) (x : RR ρ ⊗[A] (CochainComplex.HomComplexR A P I).X n) :
    δ n m (thetaLin ρ P I n x) =
      thetaLin ρ P I m
        (LinearMap.lTensor (RR ρ) ((CochainComplex.HomComplexR A P I).d n m).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
    rw [LinearMap.lTensor_tmul, thetaLin_tmul, thetaLin_tmul]
    exact (thetaCochain_δ ρ P I b c).symm
  | add x y hx hy => rw [map_add, δ_add, hx, hy, map_add, map_add]

/-- **The base-change map of Hom complexes**
`θ : R ⊗_A Hom^•_A(P, I) ⟶ Hom^•_A(P, R ⊗_A I)`. -/
def theta : S₀ ρ P I ⟶ T₀ ρ P I where
  f n := AddCommGrpCat.ofHom (thetaLin ρ P I n).toAddMonoidHom
  comm' n m _ := by
    ext x
    exact thetaLin_δ ρ P I n m x

/-- In degree `n`, `theta ρ P I` sends `b ⊗ c` to `thetaCochain ρ P I b c`. -/
lemma theta_f_tmul (n : ℤ) (b : R) (c : Cochain P I n) :
    ((theta ρ P I).f n).hom ((b : RR ρ) ⊗ₜ[A] (c : (CochainComplex.HomComplexR A P I).X n)) =
      thetaCochain ρ P I b c := rfl

end Stacks.FlatBaseChangeHom

end
