module

public import StacksFrontier.AlgebraicGeometry.AffineSymmetricAlgebraUP.Lift

/-!
# Functoriality of the symmetric algebra of an associated sheaf

Let `R` be a commutative ring and `f : M ⟶ N` a map of `R`-modules. The map `f` induces a unital
homomorphism of sheaves of graded algebras `Sym(M̃) ⟶ Sym(Ñ)`, whose degree-`n` component is
the associated sheaf of `Sym^n(f)`.

## Main definitions

* `Stacks.SymGraded.symMapGₗ`: the degree-`d` component of `Sym(f)` on graded pieces, for
  `d : ℤ` — the symmetric power map in a nonnegative degree and zero otherwise.
* `Stacks.SymGraded.symFunctorHom`: the induced unital homomorphism
  `symAlgebra M ⟶ symAlgebra N`.

## Main results

* `Stacks.SymGraded.symFunctorHom_app_natCast`: in degree `k : ℕ` the induced homomorphism is
  `tilde.map (Sym^k f)`.
* `Stacks.SymGraded.symGen_symFunctorHom`: it carries the degree-one generator of `symAlgebra M`
  to that of `symAlgebra N` along `tilde.map f`.

## Implementation notes

The homomorphism is obtained from `Stacks.GradedAlgebra.existsUnique_descCmp`, the universal
property of `Stacks.GradedAlgebra.ofComparison`: the degreewise morphism out of the base-change
presheaf is `Stacks.AffineBaseChange.presheafMap` of `Sym^d(f)` followed by the comparison for
`N`, and the two hypotheses of that universal property — multiplicativity on homogeneous local
sections and preservation of the unit — are computations on pure tensors.

Both are reduced to the single algebraic statement
`Stacks.SymGraded.symMapGₗ_coe`: the degree-`d` component of `Sym(f)` acts on the underlying
element of the symmetric algebra by `SymPow.symAlgMap f`, which is an algebra homomorphism. In a
negative degree the graded piece is `⊥` and the statement is the vanishing of both sides.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite PresheafOfModules
open scoped TensorProduct

universe u

namespace Stacks.SymGraded

variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N)

/-! ### The graded pieces of `Sym(f)` -/

/-- **The degree-`d` component of `Sym(f)` on `ℤ`-graded pieces**: the symmetric power map in a
nonnegative degree, and zero in a negative degree, where both pieces are `⊥`. -/
def symMapGₗ : (d : ℤ) → (gradedPiece (R := R) M d →ₗ[R] gradedPiece (R := R) N d)
  | .ofNat k => SymPow.symMap k f.hom
  | .negSucc _ => 0

/-- In a nonnegative degree `k`, `symMapGₗ f k` is the symmetric power map `Sym^k(f)`. -/
theorem symMapGₗ_natCast (k : ℕ) :
    symMapGₗ f (k : ℤ) = SymPow.symMap k f.hom := rfl

/-- **`Sym^d(f)` acts by the algebra map `SymPow.symAlgMap f` on underlying elements**, in every
degree. -/
theorem symMapGₗ_coe (d : ℤ) (z : gradedPiece (R := R) M d) :
    ((symMapGₗ f d z : gradedPiece (R := R) N d) : SymmetricAlgebra R N) =
      SymPow.symAlgMap f.hom (z : SymmetricAlgebra R M) := by
  match d with
  | .ofNat k => rfl
  | .negSucc k =>
      have hz : (z : SymmetricAlgebra R M) = 0 :=
        Submodule.mem_bot R |>.mp (gradedPiece_negSucc (R := R) M k ▸ z.2)
      rw [hz, map_zero]
      rfl

/-- The graded components of `Sym(f)` are compatible with the multiplication of graded pieces. -/
theorem symMapGₗ_symMulₗ (i j : ℤ) (z : gradedPiece (R := R) M i)
    (w : gradedPiece (R := R) M j) :
    symMapGₗ f (i + j) (symMulₗ (R := R) M i j z w) =
      symMulₗ (R := R) N i j (symMapGₗ f i z) (symMapGₗ f j w) :=
  Subtype.ext <| by
    rw [symMapGₗ_coe, symMulₗ_coe, symMulₗ_coe, symMapGₗ_coe, symMapGₗ_coe,
      map_mul (SymPow.symAlgMap f.hom)]

/-- The degree-zero component of `Sym(f)` sends the unit of `Sym(M)` to the unit of `Sym(N)`. -/
theorem symMapGₗ_oneG : symMapGₗ f 0 (oneG (R := R) M) = oneG (R := R) N :=
  Subtype.ext <| by rw [symMapGₗ_coe, oneG_coe, oneG_coe, map_one]

/-- The degree-one component of `Sym(f)` sends the generator `ιG M m` to `ιG N (f m)`. -/
theorem symMapGₗ_ιG (m : M) : symMapGₗ f 1 (ιG (R := R) M m) = ιG (R := R) N (f m) :=
  Subtype.ext <| by
    rw [symMapGₗ_coe, ιG_coe, ιG_coe, SymPow.symAlgMap_ι]

/-! ### The induced morphism of base-change presheaves -/

/-- `Sym^d(f)` as a map of `R`-modules. -/
def pieceModuleMap (d : ℤ) : pieceModule M d ⟶ pieceModule N d :=
  ModuleCat.ofHom (R := R) (X := pieceModule M d) (Y := pieceModule N d) (symMapGₗ f d)

/-- `pieceModuleMap f d` acts on elements by `symMapGₗ f d`. -/
theorem pieceModuleMap_apply (d : ℤ) (z : gradedPiece (R := R) M d) :
    (pieceModuleMap f d) z = symMapGₗ f d z := rfl

/-- `Sym^d(f)` on the base-change presheaves. -/
abbrev piecePresheafMap (d : ℤ) : piecePresheaf M d ⟶ piecePresheaf N d :=
  AffineBaseChange.presheafMap (pieceModuleMap f d)

/-- On a pure tensor `a ⊗ z`, the map `piecePresheafMap f d` is `a ⊗ symMapGₗ f d z`. -/
theorem piecePresheafMap_tmul (d : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (a : Γ(Spec R, U.unop))
    (z : gradedPiece (R := R) M d) :
    Hom.app (piecePresheafMap f d) U (a ⊗ₜ[R] z) = a ⊗ₜ[R] symMapGₗ f d z :=
  (AffineBaseChange.presheafMap_app (pieceModuleMap f d) U _).trans
    (AffineBaseChange.presheafMapₗ_tmul (pieceModuleMap f d) U.unop a z)

/-- **`Sym^d(f)` is multiplicative on sections of the base-change presheaves.** -/
theorem presheafMapₗ_mulSec (U : ((Spec R).Opens)ᵒᵖ) (i j : ℤ)
    (x : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M i)
    (y : Γ(Spec R, U.unop) ⊗[R] gradedPiece (R := R) M j) :
    AffineBaseChange.presheafMapₗ (pieceModuleMap f (i + j)) U.unop (mulSec M U i j x y) =
      mulSec N U i j (AffineBaseChange.presheafMapₗ (pieceModuleMap f i) U.unop x)
        (AffineBaseChange.presheafMapₗ (pieceModuleMap f j) U.unop y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      induction y using TensorProduct.inductionOn with
      | tmul b w =>
          rw [mulSec_tmul, AffineBaseChange.presheafMapₗ_tmul,
            AffineBaseChange.presheafMapₗ_tmul, AffineBaseChange.presheafMapₗ_tmul, mulSec_tmul,
            pieceModuleMap_apply, pieceModuleMap_apply, pieceModuleMap_apply,
            symMapGₗ_symMulₗ]
      | add y y' hy hy' => rw [map_add, map_add, map_add, map_add, hy, hy']
  | add x x' hx hx' =>
      rw [map_add (mulSec M U i j), LinearMap.add_apply,
        map_add (AffineBaseChange.presheafMapₗ (pieceModuleMap f (i + j)) U.unop), hx, hx',
        map_add (AffineBaseChange.presheafMapₗ (pieceModuleMap f i) U.unop),
        map_add (mulSec N U i j), LinearMap.add_apply]

/-- **`Sym^1(f)` on the base-change presheaves is the degree-one generator of `N` composed with
`f`.** -/
theorem presheafMapₗ_ιG (U : (Spec R).Opens) (x : Γ(Spec R, U) ⊗[R] M) :
    AffineBaseChange.presheafMapₗ (pieceModuleMap f 1) U
        (AffineBaseChange.presheafMapₗ (ModuleCat.ofHom (ιG (R := R) M)) U x) =
      AffineBaseChange.presheafMapₗ (ModuleCat.ofHom (ιG (R := R) N)) U
        (AffineBaseChange.presheafMapₗ f U x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      rw [AffineBaseChange.presheafMapₗ_tmul, AffineBaseChange.presheafMapₗ_tmul,
        AffineBaseChange.presheafMapₗ_tmul, AffineBaseChange.presheafMapₗ_tmul]
      exact congrArg (fun v : gradedPiece (R := R) N 1 => a ⊗ₜ[R] v) (symMapGₗ_ιG f m)
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-! ### The induced unital homomorphism -/

/-- The degreewise morphism out of the base-change presheaf of `M` into the symmetric algebra
sheaf of `N`. -/
abbrev descGen (d : ℤ) : piecePresheaf M d ⟶ ((symAlgebra N).piece d).val :=
  piecePresheafMap f d ≫ pieceCmp N d

/-- `descGen f d` on sections is `piecePresheafMap f d` followed by the comparison for `N`. -/
theorem descGen_app (d : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (x : (piecePresheaf M d).obj U) :
    Hom.app (descGen f d) U x =
      Hom.app (pieceCmp N d) U (Hom.app (piecePresheafMap f d) U x) :=
  rfl

/-- `descGen f` is multiplicative on homogeneous local sections. -/
theorem descGen_mul (i j : ℤ) (U : ((Spec R).Opens)ᵒᵖ) (x : (piecePresheaf M i).obj U)
    (y : (piecePresheaf M j).obj U) :
    Hom.app (descGen f (i + j)) U (((presheafAlgebra M).mul i j).app U x y) =
      ((symAlgebra N).mul i j).app U (Hom.app (descGen f i) U x)
        (Hom.app (descGen f j) U y) := by
  rw [descGen_app, descGen_app, descGen_app, symAlgebra_mul_toTilde]
  exact congrArg (Hom.app (pieceCmp N (i + j)) U) (presheafMapₗ_mulSec f U i j x y)

/-- `descGen f 0` sends the unit of the base-change presheaf of `M` to the unit of
`symAlgebra N`. -/
theorem descGen_one (U : ((Spec R).Opens)ᵒᵖ) :
    Hom.app (descGen f 0) U ((presheafAlgebra M).one.eval U) = (symAlgebra N).one.eval U := by
  rw [descGen_app, symAlgebra_one_eval]
  refine congrArg (Hom.app (pieceCmp N 0) U) ?_
  rw [show (presheafAlgebra M).one.eval U =
    (1 : Γ(Spec R, U.unop)) ⊗ₜ[R] oneG (R := R) M from rfl, piecePresheafMap_tmul,
    symMapGₗ_oneG]

/-- **The unital homomorphism of symmetric algebra sheaves induced by `f`.** -/
def symFunctorHom : SheafOfModules.GradedAlgebra.UnitalHom (symAlgebra M) (symAlgebra N) :=
  (Stacks.GradedAlgebra.existsUnique_descCmp (presheafAlgebra M) (pieceSheaf M) (pieceCmp M)
    (descGen f) (fun i j U x y => descGen_mul f i j U x y) (descGen_one f)).choose

/-- Composed with the comparison morphism for `M`, the degree-`d` component of
`symFunctorHom f` is `descGen f d`. -/
theorem symFunctorHom_comparison (d : ℤ) (U : ((Spec R).Opens)ᵒᵖ)
    (x : (piecePresheaf M d).obj U) :
    ((symFunctorHom f).app d).val.app U (Hom.app (pieceCmp M d) U x) =
      Hom.app (descGen f d) U x :=
  (Stacks.GradedAlgebra.existsUnique_descCmp (presheafAlgebra M) (pieceSheaf M) (pieceCmp M)
    (descGen f) (fun i j U x y => descGen_mul f i j U x y)
    (descGen_one f)).choose_spec.1 d U x

/-- **In degree `k : ℕ` the induced homomorphism is the associated sheaf of `Sym^k(f)`.** -/
theorem symFunctorHom_app_natCast (k : ℕ) :
    (symFunctorHom f).app (k : ℤ) =
      tilde.map (ModuleCat.ofHom (R := R) (X := pieceModule M (k : ℤ))
        (Y := pieceModule N (k : ℤ)) (SymPow.symMap k f.hom)) := by
  refine SheafOfModules.hom_ext (Stacks.hom_eq_of_app_eq
    (T := (pieceSheaf M (k : ℤ)).val) (pieceSheaf N (k : ℤ)).isSheaf.isSeparated
    (pieceCmp M (k : ℤ)) fun U x => ?_)
  exact (symFunctorHom_comparison f (k : ℤ) U x).trans
    (AffineBaseChange.toTilde_map_app (pieceModuleMap f (k : ℤ)) U x).symm

/-- **The induced homomorphism respects the degree-one generators.** -/
theorem symGen_symFunctorHom :
    symGen M ≫ (symFunctorHom f).app 1 = tilde.map f ≫ symGen N := by
  refine SheafOfModules.hom_ext (Stacks.hom_eq_of_app_eq (T := (tilde M).val)
    ((symAlgebra N).piece 1).isSheaf.isSeparated (AffineBaseChange.toTilde M) fun U x => ?_)
  change ((symFunctorHom f).app 1).val.app U
      ((symGen M).val.app U (Hom.app (AffineBaseChange.toTilde M) U x)) =
    (symGen N).val.app U ((tilde.map f).val.app U (Hom.app (AffineBaseChange.toTilde M) U x))
  rw [symGen_toTilde M U x, symFunctorHom_comparison, descGen_app,
    AffineBaseChange.toTilde_map_app f U x]
  refine Eq.trans ?_
    (symGen_toTilde N U (Hom.app (AffineBaseChange.presheafMap f) U x)).symm
  exact congrArg (Hom.app (pieceCmp N 1) U) (presheafMapₗ_ιG f U.unop x)

end Stacks.SymGraded
