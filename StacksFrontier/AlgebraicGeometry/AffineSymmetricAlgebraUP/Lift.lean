module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebraUP.Descent

/-!
# The descent of a degree-one generator out of the symmetric algebra on `Spec R`

Let `R` be a commutative ring, `M` an `R`-module, `B` a sheaf of graded `𝒪_{Spec R}`-algebras and
`κ : M̃ ⟶ B_1` a degree-one generator with pairwise commuting image. There is a degreewise
morphism

`Γ(U) ⊗_R Sym^n_R(M) ⟶ B_n(U)`

out of the base-change presheaf of the `n`-th symmetric power, multiplicative on homogeneous
local sections and carrying the unit to the unit. With `Stacks.GradedAlgebra.existsUnique_descCmp`
this is the existence half of the universal property of `Stacks.SymGraded.symAlgebra`.

The construction is the ungraded one. The ordered product of the images of `κ` generates a
ring homomorphism `Sym_R(M) →+* Total(B)(U)` out of the *whole* symmetric algebra, by
`Stacks.GradedAlgebra.liftTotal`; the degree-`n` component of the image of `Sym^n_R(M)` under
that homomorphism is the required morphism, and the fact that it lands in a single homogeneous
component — `Stacks.SymGraded.incl_proj_theta` — is what makes it multiplicative.

## Main definitions

* `Stacks.SymGraded.presheafOf`: a sheaf of graded algebras read as a graded algebra of
  presheaves of modules over the presheaf of *commutative* rings `(Spec R).presheaf`.
* `Stacks.SymGraded.genBC`: the degree-one generator read on the base-change presheaf of `M`.
* `Stacks.SymGraded.theta`: **the ring homomorphism `Sym_R(M) →+* Total(B)(U)`** determined by
  the generator.
* `Stacks.SymGraded.descHom`: **the degreewise morphism out of the base-change presheaf of the
  `n`-th symmetric power.**

## Main results

* `Stacks.SymGraded.theta_prod_ι`: `theta` carries a product of degree-one generators to the
  ordered product of their images.
* `Stacks.SymGraded.incl_proj_theta`: **`theta` is homogeneous**: it carries `Sym^n_R(M)` into
  the degree-`n` component of the ungraded realization.
* `Stacks.SymGraded.theta_naturality`: `theta` commutes with restriction.
* `Stacks.SymGraded.descHom_mul` and `Stacks.SymGraded.descHom_one`: `descHom` is multiplicative
  on homogeneous local sections and carries the unit to the unit.

## Implementation notes

**Why the base is re-spelled.** `Stacks.GradedAlgebra.liftTotal` and
`Stacks.GradedAlgebra.proj` are stated for a graded algebra of presheaves of modules over
`O ⋙ forget₂ CommRingCat RingCat` with `O` a presheaf of commutative rings, because the sections
of the base must carry a `CommRing` instance for `SymmetricAlgebra` to be formed over them, and
that instance (from `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`) is found only for
that spelling: `CommSemiring ↑((Spec R).ringCatSheaf.obj.obj U)` does not synthesise. The
abbreviations `Stacks.SymGraded.pieceVal` and `Stacks.SymGraded.bcPresheaf` therefore declare the
base as `(Spec R).presheaf ⋙ forget₂ CommRingCat RingCat`, so that the module structures on
their sections are the ones `liftTotal` asks for.

Two spellings of the ring of sections are unavoidable and both appear. `Γ(Spec R, U)` is the one
carrying `Algebra R Γ(Spec R, U)` and the base-change module structures of
`Stacks.AffineBaseChange`; `(Spec R).presheaf ⋙ forget₂ CommRingCat RingCat).obj U`, abbreviated
`Stacks.SymGraded.secRing`, is the one acting on the graded pieces and on the ungraded
realization. `Stacks.SymGraded.specStruct` is the structure map with its target in the second
spelling; the two are the same term, and the abbreviation is reducible, so a lemma stated with
one is applicable to a goal stated with the other.

**Why the sections are produced by `TensorProduct.liftAddHom`.** The degreewise morphism is
`a ⊗ z ↦ a • proj_n(theta z)`, which is `Γ(U)`-linear but *not* obtained from an `R`-linear map
by `LinearMap.liftBaseChange`: that would need `Module R (B_n(U))` and the scalar tower above it,
neither of which is an instance. `liftAddHom` asks only for an `R`-balanced biadditive map, which
is exactly what is available.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite PresheafOfModules
open scoped TensorProduct

universe u

namespace Stacks.SymGraded

/-! ### The base, re-spelled -/

variable (R : CommRingCat.{u})

/-- The structure sheaf of `Spec R` as a presheaf of *commutative* rings: the base in the
spelling for which the sections carry a `CommRing` instance. -/
abbrev specCommRing : ((Spec R).Opens)ᵒᵖ ⥤ CommRingCat.{u} := (Spec R).presheaf

/-- The sections of the structure sheaf of `Spec R`, spelled as the scalars of a presheaf of
modules over `specCommRing R ⋙ forget₂ CommRingCat RingCat`. -/
abbrev secRing (U : ((Spec R).Opens)ᵒᵖ) : Type u :=
  (specCommRing R ⋙ forget₂ CommRingCat RingCat).obj U

/-- The structure map `R ⟶ 𝒪(U)`, with its target in the `Stacks.SymGraded.secRing` spelling. -/
abbrev specStruct (U : ((Spec R).Opens)ᵒᵖ) : R →+* secRing R U :=
  algebraMap R Γ(Spec R, U.unop)

variable {R}

/-! ### The data -/

variable (M : ModuleCat.{u} R) (B : SheafOfModules.GradedAlgebra.{u, u} (Spec R).ringCatSheaf)

/-- The degree-`n` piece of `B`, as a presheaf of modules over
`specCommRing R ⋙ forget₂ CommRingCat RingCat`. -/
def pieceVal (n : ℤ) :
    PresheafOfModules.{u} (specCommRing R ⋙ forget₂ CommRingCat RingCat) := (B.piece n).val

/-- The base-change presheaf of `M`, over `specCommRing R ⋙ forget₂ CommRingCat RingCat`. -/
def bcPresheaf : PresheafOfModules.{u} (specCommRing R ⋙ forget₂ CommRingCat RingCat) :=
  AffineBaseChange.presheaf M

/-- **`B` as a graded algebra of presheaves of modules over `(Spec R).presheaf`.** -/
def presheafOf : Stacks.GradedAlgebra (pieceVal B) := B.toPresheafGradedAlgebra

/-- The multiplication of `presheafOf B` is that of `B`. -/
theorem presheafOf_mul (i j : ℤ) : (presheafOf B).mul i j = B.mul i j := rfl

/-- The unit of `presheafOf B` is the unit of `B`. -/
theorem presheafOf_one : (presheafOf B).one = B.one := rfl

variable (κ : (tilde M : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶ B.piece 1)

/-- The degree-one generator read on the base-change presheaf of `M`. -/
def genBC : bcPresheaf M ⟶ pieceVal B 1 := AffineBaseChange.toTilde M ≫ κ.val

/-- A pairwise commuting degree-one generator of `B` has pairwise commuting image on the
base-change presheaf. -/
theorem genCommutes_genBC (hκ : SheafOfModules.GradedAlgebra.PairwiseCommutes κ) :
    Stacks.GradedAlgebra.GenCommutes (presheafOf B) (genBC M B κ) := fun X _ _ => hκ X _ _

variable (hc : Stacks.GradedAlgebra.GenCommutes (presheafOf B) (genBC M B κ))

/-! ### The ring homomorphism out of the symmetric algebra -/

/-- `m ↦ 1 ⊗ m`, as a map semilinear along the structure map of the sections. -/
def oneTmul (U : ((Spec R).Opens)ᵒᵖ) :
    M →ₛₗ[algebraMap R Γ(Spec R, U.unop)] (Γ(Spec R, U.unop) ⊗[R] M) where
  toFun m := (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m
  map_add' a b := TensorProduct.tmul_add _ a b
  map_smul' r m := by
    change (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] (r • m) =
      algebraMap R Γ(Spec R, U.unop) r • ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m)
    rw [← TensorProduct.smul_tmul r (1 : Γ(Spec R, U.unop)) (m : M)]
    refine Eq.trans (congrArg (fun c : Γ(Spec R, U.unop) => c ⊗ₜ[R] (m : M)) ?_)
      (TensorProduct.smul_tmul' (algebraMap R Γ(Spec R, U.unop) r)
        (1 : Γ(Spec R, U.unop)) (m : M))
    rw [Algebra.smul_def, smul_eq_mul]

/-- `oneTmul M U` sends `m` to `1 ⊗ m`. -/
@[simp]
theorem oneTmul_apply (U : ((Spec R).Opens)ᵒᵖ) (m : M) :
    oneTmul M U m = (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m := rfl

/-- **The ring homomorphism out of the symmetric algebra of `M` into the ungraded realization of
`B` over `U`**, determined by the degree-one generator: the base change of `Sym_R(M)` to the
sections over `U`, followed by `Stacks.GradedAlgebra.liftTotal`. -/
def theta (U : ((Spec R).Opens)ᵒᵖ) : SymmetricAlgebra R M →+* (presheafOf B).Total U :=
  ((presheafOf B).liftTotal (genBC M B κ) hc U).comp
    (SymmetricAlgebra.mapₛₗ (algebraMap R Γ(Spec R, U.unop)) (oneTmul M U))

/-- `theta` is `liftTotal` after the base change of the symmetric algebra. -/
private theorem theta_eq_liftTotal (U : ((Spec R).Opens)ᵒᵖ) (z : SymmetricAlgebra R M) :
    theta M B κ hc U z = (presheafOf B).liftTotal (genBC M B κ) hc U
      (SymmetricAlgebra.mapₛₗ _ (oneTmul M U) z) := rfl

/-- `theta` sends the generator `ι m` to the degree-one image of `1 ⊗ m` under the generator. -/
theorem theta_ι (U : ((Spec R).Opens)ᵒᵖ) (m : M) :
    theta M B κ hc U (SymmetricAlgebra.ι R M m) =
      (presheafOf B).incl 1
        (PresheafOfModules.Hom.app (genBC M B κ) U ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m)) := by
  rw [theta_eq_liftTotal, SymmetricAlgebra.mapₛₗ_ι]
  exact SymmetricAlgebra.liftComm_ι _

/-- `theta` is semilinear along the structure map `R ⟶ 𝒪(U)`. -/
theorem theta_smul (U : ((Spec R).Opens)ᵒᵖ) (r : R) (z : SymmetricAlgebra R M) :
    theta M B κ hc U (r • z) = specStruct R U r • theta M B κ hc U z := by
  rw [theta_eq_liftTotal, SymmetricAlgebra.mapₛₗ_smul]
  exact SymmetricAlgebra.liftComm_smul (specStruct R U r) _

/-- `theta` sends the image of `r : R` to the image of `r` in the sections times the unit. -/
theorem theta_algebraMap (U : ((Spec R).Opens)ᵒᵖ) (r : R) :
    theta M B κ hc U (algebraMap R (SymmetricAlgebra R M) r) =
      specStruct R U r • (1 : (presheafOf B).Total U) := by
  rw [Algebra.algebraMap_eq_smul_one, theta_smul, map_one]

/-- **`theta` on a product of degree-one generators** is the ordered product of the images of
the generators in the ungraded realization. -/
theorem theta_prod_ι (U : ((Spec R).Opens)ᵒᵖ) {n : ℕ} (s : Fin n → M) :
    theta M B κ hc U (∏ i : Fin n, SymmetricAlgebra.ι R M (s i)) =
      (List.ofFn fun i => (presheafOf B).incl 1
        (PresheafOfModules.Hom.app (genBC M B κ) U
          ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] s i))).prod := by
  rw [theta_eq_liftTotal, map_prod]
  refine Eq.trans (congrArg ((presheafOf B).liftTotal (genBC M B κ) hc U)
    (Finset.prod_congr rfl fun i _ => SymmetricAlgebra.mapₛₗ_ι _ (oneTmul M U) (s i))) ?_
  exact SymmetricAlgebra.liftComm_prod_ι (T := (presheafOf B).Total U) _

/-! ### Homogeneity -/

/-- `theta`, as a map semilinear along the structure map, on the `n`-th symmetric power. -/
def thetaPow (U : ((Spec R).Opens)ᵒᵖ) (n : ℕ) :
    SymPow.symmetricPower n R M →ₛₗ[specStruct R U] (presheafOf B).Total U where
  toFun z := theta M B κ hc U (z : SymmetricAlgebra R M)
  map_add' _ _ := map_add (theta M B κ hc U) _ _
  map_smul' r _ := theta_smul M B κ hc U r _

/-- The degree-`n` component of `theta` on the `n`-th symmetric power, read back in the ungraded
realization. -/
def thetaPowHomog (U : ((Spec R).Opens)ᵒᵖ) (n : ℕ) :
    SymPow.symmetricPower n R M →ₛₗ[specStruct R U] (presheafOf B).Total U where
  toFun z := (presheafOf B).incl (n : ℤ)
    ((presheafOf B).proj U (n : ℤ) (theta M B κ hc U (z : SymmetricAlgebra R M)))
  map_add' z z' := by
    change (presheafOf B).incl (n : ℤ) ((presheafOf B).proj U (n : ℤ)
      (theta M B κ hc U ((z : SymmetricAlgebra R M) + (z' : SymmetricAlgebra R M)))) = _
    rw [map_add (theta M B κ hc U), map_add ((presheafOf B).proj U (n : ℤ))]
    exact (presheafOf B).incl_add (n : ℤ) _ _
  map_smul' r z := by
    change (presheafOf B).incl (n : ℤ) ((presheafOf B).proj U (n : ℤ)
      (theta M B κ hc U (r • (z : SymmetricAlgebra R M)))) = _
    rw [theta_smul, map_smul ((presheafOf B).proj U (n : ℤ))]
    exact (presheafOf B).incl_smul (n : ℤ) _ _

/-- **`theta` is homogeneous on the symmetric powers**: on `Sym^n_R(M)` it lands in the
degree-`n` component of the ungraded realization. -/
theorem incl_proj_theta_natCast (U : ((Spec R).Opens)ᵒᵖ) (n : ℕ)
    (z : SymPow.symmetricPower n R M) :
    (presheafOf B).incl (n : ℤ)
        ((presheafOf B).proj U (n : ℤ) (theta M B κ hc U (z : SymmetricAlgebra R M))) =
      theta M B κ hc U (z : SymmetricAlgebra R M) := by
  have key : thetaPowHomog M B κ hc U n = thetaPow M B κ hc U n := by
    refine SymPow.ext_of_prod_ι fun s => ?_
    change (presheafOf B).incl (n : ℤ) ((presheafOf B).proj U (n : ℤ)
      (theta M B κ hc U (∏ i : Fin n, SymmetricAlgebra.ι R M (s i)))) =
      theta M B κ hc U (∏ i : Fin n, SymmetricAlgebra.ι R M (s i))
    rw [theta_prod_ι, ← Stacks.GradedAlgebra.incl_homogeneousProd (presheafOf B) U n
      (fun i => PresheafOfModules.Hom.app (genBC M B κ) U ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] s i)),
      (presheafOf B).proj_incl U (n : ℤ)]
  exact DFunLike.congr_fun key z

/-- **`theta` is homogeneous**, in the `ℤ`-graded form: on the degree-`n` graded piece of
`Sym_R(M)` it lands in the degree-`n` component of the ungraded realization. -/
theorem incl_proj_theta (U : ((Spec R).Opens)ᵒᵖ) (n : ℤ) (z : gradedPiece (R := R) M n) :
    (presheafOf B).incl n
        ((presheafOf B).proj U n (theta M B κ hc U (z : SymmetricAlgebra R M))) =
      theta M B κ hc U (z : SymmetricAlgebra R M) := by
  match n with
  | .ofNat k => exact incl_proj_theta_natCast M B κ hc U k z
  | .negSucc k =>
      have hbot := gradedPiece_eq_bot_of_neg M (Int.negSucc_lt_zero k)
      have hz : (z : SymmetricAlgebra R M) = 0 :=
        Submodule.mem_bot R |>.mp (hbot ▸ z.2)
      rw [hz, map_zero (theta M B κ hc U),
        map_zero ((presheafOf B).proj U (Int.negSucc k)), (presheafOf B).incl_zero]

/-! ### Naturality -/

/-- `theta` commutes with restriction along `f : U ⟶ V`. -/
theorem theta_naturality {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V) (z : SymmetricAlgebra R M) :
    (presheafOf B).totalRestrict f (theta M B κ hc U z) = theta M B κ hc V z := by
  have key : ((presheafOf B).totalRestrictRingHom f).comp (theta M B κ hc U) =
      theta M B κ hc V := by
    refine SymmetricAlgebra.ringHom_ext (fun r => ?_) fun m => ?_
    · change (presheafOf B).totalRestrict f
        (theta M B κ hc U (algebraMap R (SymmetricAlgebra R M) r)) = _
      rw [theta_algebraMap, theta_algebraMap, (presheafOf B).totalRestrict_smul,
        (presheafOf B).totalRestrict_one]
      exact congrArg (fun c : secRing R V => c • (1 : (presheafOf B).Total V))
        (AffineBaseChange.algebraMap_restrict f.unop r)
    · change (presheafOf B).totalRestrict f (theta M B κ hc U (SymmetricAlgebra.ι R M m)) = _
      rw [theta_ι, theta_ι, (presheafOf B).totalRestrict_incl]
      refine congrArg ((presheafOf B).incl 1) ?_
      refine Eq.trans (naturality_apply (genBC M B κ) f
        ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] m)).symm ?_
      refine congrArg (PresheafOfModules.Hom.app (genBC M B κ) V) ?_
      refine Eq.trans (AffineBaseChange.presheaf_map M f (1 : Γ(Spec R, U.unop)) m) ?_
      exact congrArg (fun c : Γ(Spec R, V.unop) => c ⊗ₜ[R] (m : M))
        (AffineBaseChange.specRestrictₗ_one f.unop)
  exact congrArg (fun g : SymmetricAlgebra R M →+* (presheafOf B).Total V => g z) key

/-! ### The degreewise morphism out of the base-change presheaf -/

/-- The base-change presheaf of the degree-`n` symmetric power, over
`specCommRing R ⋙ forget₂ CommRingCat RingCat`. -/
def symPieceVal (n : ℤ) :
    PresheafOfModules.{u} (specCommRing R ⋙ forget₂ CommRingCat RingCat) := piecePresheaf M n

/-- The biadditive map `(a, z) ↦ a • proj_n(theta z)`. -/
def descAdd (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) :
    Γ(Spec R, U.unop) →+ (gradedPiece (R := R) M n) →+ (pieceVal B n).obj U :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun z => (a : secRing R U) •
        (presheafOf B).proj U n (theta M B κ hc U (z : SymmetricAlgebra R M)))
      fun z z' => by
        change (a : secRing R U) • (presheafOf B).proj U n
          (theta M B κ hc U ((z : SymmetricAlgebra R M) + (z' : SymmetricAlgebra R M))) = _
        rw [map_add (theta M B κ hc U), map_add ((presheafOf B).proj U n), smul_add])
    fun a a' => AddMonoidHom.ext fun z => add_smul (a : secRing R U) (a' : secRing R U) _

/-- `descAdd` sends `(a, z)` to `a • proj_n(theta z)`. -/
theorem descAdd_apply (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (a : Γ(Spec R, U.unop))
    (z : gradedPiece (R := R) M n) :
    descAdd M B κ hc n U a z =
      (a : secRing R U) •
        (presheafOf B).proj U n (theta M B κ hc U (z : SymmetricAlgebra R M)) := rfl

/-- `descAdd` is `R`-balanced: `descAdd (r • a) z = descAdd a (r • z)`. -/
theorem descAdd_balanced (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (r : R) (a : Γ(Spec R, U.unop))
    (z : gradedPiece (R := R) M n) :
    descAdd M B κ hc n U (r • a) z = descAdd M B κ hc n U a (r • z) := by
  rw [descAdd_apply, descAdd_apply,
    show ((r • z : gradedPiece (R := R) M n) : SymmetricAlgebra R M) =
      r • (z : SymmetricAlgebra R M) from rfl,
    theta_smul, map_smul ((presheafOf B).proj U n), smul_smul]
  exact congrArg (fun c : secRing R U =>
      c • (presheafOf B).proj U n (theta M B κ hc U (z : SymmetricAlgebra R M)))
    ((Algebra.smul_def r a).trans (mul_comm _ _))

/-- **The degreewise morphism on sections.** -/
def descSec (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) :
    (Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) →+ (pieceVal B n).obj U :=
  TensorProduct.liftAddHom (descAdd M B κ hc n U) (descAdd_balanced M B κ hc n U)

/-- `descSec` sends `a ⊗ z` to `a • proj_n(theta z)`. -/
@[simp]
theorem descSec_tmul (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (a : Γ(Spec R, U.unop))
    (z : gradedPiece (R := R) M n) :
    descSec M B κ hc n U (a ⊗ₜ[R] z) =
      (a : secRing R U) •
        (presheafOf B).proj U n (theta M B κ hc U (z : SymmetricAlgebra R M)) := rfl

/-- `descSec` is linear over the sections `Γ(Spec R, U)`. -/
theorem descSec_smul (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (c : Γ(Spec R, U.unop))
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) :
    descSec M B κ hc n U (c • x) = (c : secRing R U) • descSec M B κ hc n U x := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      rw [TensorProduct.smul_tmul' c a z, smul_eq_mul, descSec_tmul, descSec_tmul,
        show ((c * a : Γ(Spec R, U.unop)) : secRing R U) =
          (c : secRing R U) * (a : secRing R U) from rfl, ← smul_smul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- `descSec` commutes with restriction along `f : U ⟶ V`. -/
theorem descSec_naturality (n : ℤ) {U V : ((Spec R).Opens)ᵒᵖ} (f : U ⟶ V)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) :
    Stacks.sectionRestrict (pieceVal B n) f (descSec M B κ hc n U x) =
      descSec M B κ hc n V (pieceRestrict M f n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      have hp : Stacks.sectionRestrict (pieceVal B n) f
            ((presheafOf B).proj U n (theta M B κ hc U (z : SymmetricAlgebra R M))) =
          (presheafOf B).proj V n (theta M B κ hc V (z : SymmetricAlgebra R M)) := by
        rw [Stacks.GradedAlgebra.sectionRestrict_proj (presheafOf B) f n, theta_naturality]
      rw [descSec_tmul, pieceRestrict_tmul, descSec_tmul]
      refine Eq.trans ((pieceVal B n).map_smul f (a : secRing R U) _) ?_
      exact congrArg (fun y : (pieceVal B n).obj V =>
        ((specCommRing R ⋙ forget₂ CommRingCat RingCat).map f a) • y) hp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The degreewise morphism out of the base-change presheaf of the `n`-th symmetric power.** -/
def descHom (n : ℤ) : symPieceVal M n ⟶ pieceVal B n where
  app U := ModuleCat.ofHom (R := secRing R U)
    (X := (symPieceVal M n).obj U) (Y := (pieceVal B n).obj U)
    { toFun := descSec M B κ hc n U
      map_add' := map_add (descSec M B κ hc n U)
      map_smul' := fun c x => descSec_smul M B κ hc n U c x }
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (descSec_naturality M B κ hc n f x).symm)

/-- The component of `descHom` over `U` is `descSec`. -/
theorem descHom_app (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M n) :
    PresheafOfModules.Hom.app (descHom M B κ hc n) U x = descSec M B κ hc n U x := rfl

/-- The component of `descHom` over `U` sends `a ⊗ z` to `a • proj_n(theta z)`. -/
theorem descHom_tmul (n : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (a : Γ(Spec R, U.unop))
    (z : gradedPiece (R := R) M n) :
    PresheafOfModules.Hom.app (descHom M B κ hc n) U (a ⊗ₜ[R] z) =
      (a : secRing R U) •
        (presheafOf B).proj U n (theta M B κ hc U (z : SymmetricAlgebra R M)) := rfl

/-! ### Multiplicativity and the unit -/

/-- The degree-`(i+j)` component of `theta` on a product of homogeneous elements is the product
of the degree-`i` and degree-`j` components. -/
theorem proj_theta_mul (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ) (z : gradedPiece (R := R) M i)
    (w : gradedPiece (R := R) M j) :
    (presheafOf B).proj U (i + j)
        (theta M B κ hc U ((z : SymmetricAlgebra R M) * (w : SymmetricAlgebra R M))) =
      ((presheafOf B).mul i j).app U
          ((presheafOf B).proj U i (theta M B κ hc U (z : SymmetricAlgebra R M)))
        ((presheafOf B).proj U j (theta M B κ hc U (w : SymmetricAlgebra R M))) := by
  have key : (presheafOf B).incl (i + j) ((presheafOf B).proj U (i + j)
      (theta M B κ hc U ((z : SymmetricAlgebra R M) * (w : SymmetricAlgebra R M)))) =
      (presheafOf B).incl (i + j) (((presheafOf B).mul i j).app U
        ((presheafOf B).proj U i (theta M B κ hc U (z : SymmetricAlgebra R M)))
        ((presheafOf B).proj U j (theta M B κ hc U (w : SymmetricAlgebra R M)))) := by
    rw [incl_proj_theta M B κ hc U (i + j)
        (⟨(z : SymmetricAlgebra R M) * (w : SymmetricAlgebra R M),
          mul_mem_gradedPiece M i j z.2 w.2⟩ : gradedPiece (R := R) M (i + j)),
      ← (presheafOf B).incl_mul_incl i j, incl_proj_theta M B κ hc U i z,
      incl_proj_theta M B κ hc U j w]
    exact map_mul (theta M B κ hc U) _ _
  have hp := congrArg ((presheafOf B).proj U (i + j)) key
  rwa [(presheafOf B).proj_incl, (presheafOf B).proj_incl] at hp

/-- The multiplication of `presheafOf B` on sections vanishes when its left argument is zero. -/
theorem bilApp_zero_left (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (q : (pieceVal B j).obj U) :
    ((presheafOf B).mul i j).app U 0 q = 0 := by
  rw [map_zero]; rfl

/-- The multiplication of `presheafOf B` on sections vanishes when its right argument is
zero. -/
theorem bilApp_zero_right (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (p : (pieceVal B i).obj U) :
    ((presheafOf B).mul i j).app U p 0 = 0 := map_zero (((presheafOf B).mul i j).app U p)

/-- **The degreewise morphism is multiplicative on homogeneous local sections.** -/
theorem descSec_mul (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i)
    (y : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j) :
    descSec M B κ hc (i + j) U (mulSec M U i j x y) =
      ((presheafOf B).mul i j).app U (descSec M B κ hc i U x) (descSec M B κ hc j U y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      induction y using TensorProduct.inductionOn with
      | tmul b w =>
          rw [mulSec_tmul, descSec_tmul, descSec_tmul, descSec_tmul,
            ((presheafOf B).mul i j).map_smul_left U (a : secRing R U),
            ((presheafOf B).mul i j).map_smul_right U (b : secRing R U), smul_smul,
            show ((a * b : Γ(Spec R, U.unop)) : secRing R U) =
              (a : secRing R U) * (b : secRing R U) from rfl,
            show ((symMulₗ (R := R) M i j z w : gradedPiece (R := R) M (i + j)) :
              SymmetricAlgebra R M) = (z : SymmetricAlgebra R M) * (w : SymmetricAlgebra R M)
              from rfl, proj_theta_mul]
      | add y y' hy hy' =>
          rw [map_add (mulSec M U i j (a ⊗ₜ[R] z)), map_add, hy, hy', map_add,
            map_add (((presheafOf B).mul i j).app U (descSec M B κ hc i U (a ⊗ₜ[R] z)))]
  | add x x' hx hx' =>
      rw [map_add (mulSec M U i j), LinearMap.add_apply, map_add, hx, hx', map_add,
        ((presheafOf B).mul i j).map_add_left U (descSec M B κ hc i U x)
          (descSec M B κ hc i U x') (descSec M B κ hc j U y)]

/-- `descHom` carries the product of homogeneous local sections of the base-change presheaf of
the symmetric algebra to the product of their images in `presheafOf B`. -/
theorem descHom_mul (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (symPieceVal M i).obj U) (y : (symPieceVal M j).obj U) :
    PresheafOfModules.Hom.app (descHom M B κ hc (i + j)) U
        (((presheafAlgebra M).mul i j).app U x y) =
      ((presheafOf B).mul i j).app U (PresheafOfModules.Hom.app (descHom M B κ hc i) U x)
        (PresheafOfModules.Hom.app (descHom M B κ hc j) U y) :=
  descSec_mul M B κ hc i j U x y

/-- **`descHom` carries the unit to the unit.** -/
theorem descHom_one (U : ((Spec R).Opens)ᵒᵖ) :
    PresheafOfModules.Hom.app (descHom M B κ hc 0) U ((presheafAlgebra M).one.eval U) =
      (presheafOf B).one.eval U := by
  change descSec M B κ hc 0 U ((1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M) = _
  rw [descSec_tmul,
    show ((oneG (R := R) M : gradedPiece (R := R) M 0) : SymmetricAlgebra R M) = 1 from rfl,
    map_one (theta M B κ hc U), (presheafOf B).one_eq_incl U, (presheafOf B).proj_incl, one_smul]

end Stacks.SymGraded
