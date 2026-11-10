module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraTotalSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# The ring of local sections of the Laurent algebra of an invertible module

Let `T` be a scheme and `L` an invertible `𝒪_T`-module. Over an open `V` of `T` the local
sections of the integral tensor powers `L^{⊗ n}`, `n ∈ ℤ`, form a `ℤ`-graded commutative ring, the
multiplication being the coherent multiplication of [Stacks, Tag 01CU]. This file records that
ring, `⨁_{n ∈ ℤ} Γ(V, L^{⊗ n})`, and the powers of a homogeneous unit of degree one in it.

The point is bookkeeping. The multiplication of the Laurent algebra lands in the piece of degree
`n + m`, and the integers `n + m`, `m + n`, `0 + n`, `n + 0` are only propositionally equal, so the
algebra laws are heterogeneous equalities. Inside the direct sum they are ordinary ring laws, and
the powers `w^n` of a homogeneous unit `w` of degree one are its integer powers in the unit group,
whose homogeneous components are what a trivialization of `L` over `V` needs in every degree.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections.gcommRing`: the graded
  commutative ring structure on the local sections of the Laurent algebra.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections.Ring`: the ring itself.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open SheafOfModules.GradedAlgebra Stacks.RingedSpace MonoidalCategory Stacks.PullbackTensorCoherence

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

variable {T : Scheme.{u}} (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The local sections of the Laurent algebra over an open form a graded commutative ring.** -/
@[instance_reducible]
def gcommRing (V : (Opens T.carrier)ᵒᵖ) : DirectSum.GCommRing ((laurent L).sectionsPiece V) :=
  { sectionsGRing (laurent L) V with
    mul_comm := fun ⟨i, x⟩ ⟨j, y⟩ => Sigma.ext (add_comm i j)
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra_mul_comm T.toRingedSpace.presheaf
        (isSheafStruct T) L i j V x y) }

attribute [local instance] gcommRing Stacks.PullbackGradedAlgebra.monoidalCategory

/-- **The ring of local sections of the Laurent algebra over `V`**, `⨁_{n ∈ ℤ} Γ(V, L^{⊗ n})`. -/
abbrev Ring (V : (Opens T.carrier)ᵒᵖ) : Type u :=
  DirectSum ℤ ((laurent L).sectionsPiece V)

variable {L}

/-- The product of two homogeneous elements is the summand of their product in the Laurent
algebra. -/
theorem of_mul_of (V : (Opens T.carrier)ᵒᵖ) (i j : ℤ) (x : (laurent L).sectionsPiece V i)
    (y : (laurent L).sectionsPiece V j) :
    DirectSum.of ((laurent L).sectionsPiece V) i x * DirectSum.of _ j y =
      DirectSum.of ((laurent L).sectionsPiece V) (i + j) (((laurent L).mul i j).app V x y) :=
  DirectSum.of_mul_of (A := (laurent L).sectionsPiece V) x y

/-- Two homogeneous elements whose degrees agree and which are heterogeneously equal are equal. -/
theorem of_eq_of_heq (V : (Opens T.carrier)ᵒᵖ) {i j : ℤ} (h : i = j)
    {x : (laurent L).sectionsPiece V i} {y : (laurent L).sectionsPiece V j} (hxy : HEq x y) :
    DirectSum.of ((laurent L).sectionsPiece V) i x = DirectSum.of _ j y := by
  subst h
  rw [eq_of_heq hxy]

/-- The unit of the ring is the unit section in degree zero. -/
theorem one_eq (V : (Opens T.carrier)ᵒᵖ) :
    (1 : Ring L V) = DirectSum.of ((laurent L).sectionsPiece V) 0 ((laurent L).one.eval V) :=
  rfl

/-- Scalar multiplication respects heterogeneous equality across an equality of degrees. -/
theorem heq_smul (V : (Opens T.carrier)ᵒᵖ) {i j : ℤ} (h : i = j)
    (r : (structureRingSheaf T.toRingedSpace).obj.obj V) {x : (laurent L).sectionsPiece V i}
    {y : (laurent L).sectionsPiece V j} (hxy : HEq x y) : HEq (r • x) (r • y) := by
  subst h
  rw [eq_of_heq hxy]

/-- A local section of the structure sheaf acts on a homogeneous element as the product with the
degree-zero element it is. -/
theorem smul_of (V : (Opens T.carrier)ᵒᵖ) (r : (structureRingSheaf T.toRingedSpace).obj.obj V)
    (i : ℤ) (x : (laurent L).sectionsPiece V i) :
    DirectSum.of ((laurent L).sectionsPiece V) i (r • x) =
      DirectSum.of ((laurent L).sectionsPiece V) 0 (r • (laurent L).one.eval V) *
        DirectSum.of _ i x := by
  rw [of_mul_of]
  refine of_eq_of_heq V (zero_add i).symm ?_
  rw [((laurent L).mul 0 i).map_smul_left]
  exact heq_smul V (zero_add i).symm r ((laurent L).one_mul i V x).symm

/-! ### Restriction -/

/-- **Restriction of local sections of the Laurent algebra, as a ring homomorphism.** -/
def res {V V' : (Opens T.carrier)ᵒᵖ} (e : V ⟶ V') : Ring L V →+* Ring L V' :=
  DirectSum.toSemiring (fun i => (DirectSum.of ((laurent L).sectionsPiece V') i).comp
      (((laurent L).piece i).val.restrictₛₗ e).toAddMonoidHom)
    (by
      change DirectSum.of ((laurent L).sectionsPiece V') 0
        (((laurent L).piece 0).val.restrictₛₗ e ((laurent L).one.eval V)) = 1
      rw [one_eq]
      exact congrArg _ ((laurent L).one.property e))
    (by
      intro i j x y
      change DirectSum.of ((laurent L).sectionsPiece V') (i + j)
          (((laurent L).piece (i + j)).val.restrictₛₗ e (((laurent L).mul i j).app V x y)) =
        DirectSum.of ((laurent L).sectionsPiece V') i
          (((laurent L).piece i).val.restrictₛₗ e x) *
          DirectSum.of ((laurent L).sectionsPiece V') j
            (((laurent L).piece j).val.restrictₛₗ e y)
      rw [of_mul_of]
      exact congrArg _ (((laurent L).mul i j).naturality e x y))

/-- Restriction of Laurent sections sends a homogeneous element `x` of degree `i` to the
restriction of `x`, again in degree `i`. -/
theorem res_of {V V' : (Opens T.carrier)ᵒᵖ} (e : V ⟶ V') (i : ℤ)
    (x : (laurent L).sectionsPiece V i) :
    res e (DirectSum.of _ i x) = DirectSum.of _ i (((laurent L).piece i).val.restrictₛₗ e x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-! ### Powers of a homogeneous unit of degree one -/

variable {V : (Opens T.carrier)ᵒᵖ} (w : (Ring L V)ˣ)

/-- A homogeneous element of degree `i` is the summand of its own degree-`i` component. -/
theorem of_apply_eq {i : ℤ} {z : Ring L V} (hz : ∃ y, z = DirectSum.of _ i y) :
    DirectSum.of ((laurent L).sectionsPiece V) i (z i) = z := by
  obtain ⟨y, rfl⟩ := hz
  rw [DirectSum.of_eq_same]

/-- **The integer powers of a homogeneous unit of degree one are homogeneous**, of degree the
exponent. -/
theorem zpow_homogeneous (hw : ∃ σ, (w : Ring L V) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring L V)ˣ) : Ring L V) = DirectSum.of _ (-1) τ) (k : ℤ) :
    ∃ y, ((w ^ k : (Ring L V)ˣ) : Ring L V) = DirectSum.of _ k y := by
  induction k using Int.induction_on with
  | zero => exact ⟨_, (one_eq V).trans rfl⟩
  | succ k ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨σ, hσ⟩ := hw
    exact ⟨_, by rw [zpow_add_one, Units.val_mul, hy, hσ, of_mul_of]⟩
  | pred k ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨τ, hτ⟩ := hw'
    have key : ∀ (a b : ℤ) (_ : a = b) (z : Ring L V), (∃ y, z = DirectSum.of _ a y) →
        ∃ y, z = DirectSum.of ((laurent L).sectionsPiece V) b y := by
      rintro a b rfl z hz
      exact hz
    refine key (-(k : ℤ) + -1) _ (by ring) _ ⟨((laurent L).mul _ _).app V y τ, ?_⟩
    rw [show -(k : ℤ) - 1 = -(k : ℤ) + -1 by ring, zpow_add, zpow_neg_one, Units.val_mul, hy, hτ,
      of_mul_of]

/-- The degree-`k` homogeneous component of `w^k`. -/
def pw (k : ℤ) : (laurent L).sectionsPiece V k := ((w ^ k : (Ring L V)ˣ) : Ring L V) k

/-- When `w` and `w⁻¹` are homogeneous of degrees `1` and `-1`, the degree-`k` component
`pw w k`, placed in degree `k`, is `w^k`. -/
theorem of_pw (hw : ∃ σ, (w : Ring L V) = DirectSum.of _ 1 σ)
    (hw' : ∃ τ, ((w⁻¹ : (Ring L V)ˣ) : Ring L V) = DirectSum.of _ (-1) τ) (k : ℤ) :
    DirectSum.of ((laurent L).sectionsPiece V) k (pw w k) = ((w ^ k : (Ring L V)ˣ) : Ring L V) :=
  of_apply_eq (zpow_homogeneous w hw hw' k)

/-! ### The morphism out of the structure sheaf named by a global section -/

variable (T) in
/-- Restriction from the whole of `T` to an open, as a morphism of `(Opens T)ᵒᵖ` with target `V`
on the nose. -/
def topRes (V : (Opens T.carrier)ᵒᵖ) : op (⊤ : Opens T.carrier) ⟶ V :=
  (homOfLE (show V.unop ≤ ⊤ from le_top)).op

/-- **The morphism `𝒪_T ⟶ F` named by a global section `x` of `F`**: `1 ↦ x`. -/
def secHom (F : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) (x : F.val.obj (op ⊤)) :
    𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) ⟶ F :=
  F.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun V => F.val.restrictₛₗ (topRes T V) x)
    (fun {V V'} e => by
      change F.val.map e (F.val.map (topRes T V) x) = F.val.map (topRes T V') x
      rw [← PresheafOfModules.map_comp_apply]
      rfl))

/-- On sections over `V`, `secHom F x` sends `r` to `r` times the restriction of `x` to `V`. -/
theorem secHom_app (F : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    (x : F.val.obj (op ⊤)) (V : (Opens T.carrier)ᵒᵖ)
    (r : (structureRingSheaf T.toRingedSpace).obj.obj V) :
    (secHom F x).val.app V r = r • F.val.restrictₛₗ (topRes T V) x := rfl

/-- On sections over `V`, `secHom F x` sends the unit section to the restriction of `x`. -/
private theorem secHom_app_oneSec (F : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    (x : F.val.obj (op ⊤)) (V : (Opens T.carrier)ᵒᵖ) :
    (secHom F x).val.app V (oneSec T.toRingedSpace V) = F.val.restrictₛₗ (topRes T V) x :=
  (secHom_app _ _ V 1).trans (one_smul _ _)

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

attribute [local instance] gcommRing Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T : Scheme.{u}} {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (w : (Ring L (op ⊤))ˣ)

/-- **The trivialization `𝒪_T ⟶ L^{⊗ (-m)}`, `1 ↦ w^{-m}`.** -/
def triv (m : ℤ) : 𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) ⟶
    (laurent L).piece (-m) :=
  secHom ((laurent L).piece (-m)) (pw w (-m))

/-- **The coordinate `L^{⊗ (-m)} ⟶ 𝒪_T`, `l ↦ w^m · l`.** -/
def coord (m : ℤ) : (laurent L).piece (-m) ⟶
    𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :=
  (λ_ _).inv ≫ (secHom ((laurent L).piece m) (pw w m) ▷ (laurent L).piece (-m)) ≫
    Stacks.PullbackTensorCoherence.mulHom (laurent L) m (-m) ≫
      eqToHom (congrArg (laurent L).piece (add_neg_cancel m))

/-- Transport along an equality of degrees does not change the summand. -/
theorem of_eqToHom {V : (Opens T.carrier)ᵒᵖ} {k k' : ℤ} (h : k = k')
    (x : (laurent L).sectionsPiece V k) :
    DirectSum.of ((laurent L).sectionsPiece V) k'
        ((eqToHom (congrArg (laurent L).piece h)).val.app V x) =
      DirectSum.of ((laurent L).sectionsPiece V) k x := by
  subst h
  rfl

/-- The left unitor's inverse on a local section: `x ↦ 1 ⊗ x`. -/
theorem leftUnitor_inv_app (X : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    (V : (Opens T.carrier)ᵒᵖ) (x : X.val.obj V) :
    (λ_ X).inv.val.app V x = tmul T.toRingedSpace (𝟙_ _) X V (oneSec T.toRingedSpace V) x := by
  have h := leftUnitor_hom_tmul (Z := T.toRingedSpace) (B := X) V
    (1 : (structureRingSheaf T.toRingedSpace).obj.obj V) x
  rw [one_smul] at h
  have h2 : ((λ_ X).hom ≫ (λ_ X).inv).val.app V
      (tmul T.toRingedSpace (𝟙_ _) X V (oneSec T.toRingedSpace V) x) =
      tmul T.toRingedSpace (𝟙_ _) X V (oneSec T.toRingedSpace V) x := by
    rw [Iso.hom_inv_id]
    rfl
  exact (congrArg (fun z => (λ_ X).inv.val.app V z) h.symm).trans h2

variable (hw : ∃ σ, (w : Ring L (op ⊤)) = DirectSum.of _ 1 σ)
  (hw' : ∃ τ, ((w⁻¹ : (Ring L (op ⊤))ˣ) : Ring L (op ⊤)) = DirectSum.of _ (-1) τ)

include hw hw' in
/-- The restriction of `w^m · w^{-m}` is `1`. -/
theorem res_pw_mul_pw (V : (Opens T.carrier)ᵒᵖ) (e : op (⊤ : Opens T.carrier) ⟶ V) (m : ℤ) :
    DirectSum.of ((laurent L).sectionsPiece V) m (((laurent L).piece m).val.restrictₛₗ e (pw w m)) *
        DirectSum.of _ (-m) (((laurent L).piece (-m)).val.restrictₛₗ e (pw w (-m))) = 1 := by
  rw [← res_of, ← res_of, of_pw w hw hw', of_pw w hw hw', ← map_mul, ← Units.val_mul,
    ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, map_one]

omit hw hw' in
/-- The coordinate on a local section: the product with `w^m`, read in degree zero. -/
theorem coord_app (m : ℤ) (V : (Opens T.carrier)ᵒᵖ) (y : ((laurent L).piece (-m)).val.obj V) :
    (coord w m).val.app V y =
      (eqToHom (congrArg (laurent L).piece (add_neg_cancel m))).val.app V
        (((laurent L).mul m (-m)).app V
          (((laurent L).piece m).val.restrictₛₗ (topRes T V) (pw w m)) y) := by
  have e1 := leftUnitor_inv_app ((laurent L).piece (-m)) V y
  have e2 := whiskerRight_tmul (secHom ((laurent L).piece m) (pw w m)) V
    (oneSec T.toRingedSpace V) y
  have e3 := secHom_app_oneSec ((laurent L).piece m) (pw w m) V
  have e4 := mulHom_tmul (laurent L) m (-m) V
    (((laurent L).piece m).val.restrictₛₗ (topRes T V) (pw w m)) y
  change (eqToHom (congrArg (laurent L).piece (add_neg_cancel m))).val.app V
    ((mulHom (laurent L) m (-m)).val.app V
      ((secHom ((laurent L).piece m) (pw w m) ▷ (laurent L).piece (-m)).val.app V
        ((λ_ ((laurent L).piece (-m))).inv.val.app V y))) = _
  rw [e1, e2, e3, e4]

omit hw hw' in
/-- The trivialization on a local section of the structure sheaf. -/
theorem triv_app (m : ℤ) (V : (Opens T.carrier)ᵒᵖ)
    (r : (structureRingSheaf T.toRingedSpace).obj.obj V) :
    (triv w m).val.app V r =
      r • ((laurent L).piece (-m)).val.restrictₛₗ (topRes T V) (pw w (-m)) :=
  secHom_app _ _ V r

include hw hw' in
/-- **The trivialization followed by the coordinate is the identity.** -/
theorem triv_coord (m : ℤ) : triv w m ≫ coord w m = 𝟙 _ := by
  apply (SheafOfModules.unitHomEquiv _).injective
  ext V
  change (coord w m).val.app V ((triv w m).val.app V (oneSec T.toRingedSpace V)) =
    oneSec T.toRingedSpace V
  have e1 := secHom_app_oneSec ((laurent L).piece (-m)) (pw w (-m)) V
  rw [show (triv w m).val.app V (oneSec T.toRingedSpace V) = _ from e1, coord_app]
  apply DirectSum.of_injective (β := (laurent L).sectionsPiece V) (0 : ℤ)
  rw [of_eqToHom (add_neg_cancel m), ← of_mul_of, res_pw_mul_pw w hw hw' V _ m, one_eq]
  rfl

omit hw hw' in
/-- The trivialization on a local section of the unit object. -/
theorem triv_app' (m : ℤ) (V : (Opens T.carrier)ᵒᵖ)
    (r : (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))).val.obj V) :
    (triv w m).val.app V r =
      (show (structureRingSheaf T.toRingedSpace).obj.obj V from r) •
        ((laurent L).piece (-m)).val.restrictₛₗ (topRes T V) (pw w (-m)) := rfl

omit hw hw' in
/-- A local section of the structure sheaf, read in degree zero, is its own product with the
unit. -/
theorem smul_one_eval (V : (Opens T.carrier)ᵒᵖ) (r : ((laurent L).piece 0).val.obj V) :
    (show (structureRingSheaf T.toRingedSpace).obj.obj V from r) • (laurent L).one.eval V = r :=
  _root_.mul_one (show (structureRingSheaf T.toRingedSpace).obj.obj V from r)

include hw hw' in
/-- **The coordinate followed by the trivialization is the identity.** -/
theorem coord_triv (m : ℤ) : coord w m ≫ triv w m = 𝟙 _ := by
  ext V y
  change (triv w m).val.app V ((coord w m).val.app V y) = y
  rw [triv_app', coord_app]
  apply DirectSum.of_injective (β := (laurent L).sectionsPiece V) (-m)
  rw [smul_of, smul_one_eval, of_eqToHom (add_neg_cancel m), ← of_mul_of]
  calc _ = DirectSum.of ((laurent L).sectionsPiece V) (-m) y *
        (DirectSum.of ((laurent L).sectionsPiece V) m
            (((laurent L).piece m).val.restrictₛₗ (topRes T V) (pw w m)) *
          DirectSum.of _ (-m) (((laurent L).piece (-m)).val.restrictₛₗ (topRes T V) (pw w (-m)))) :=
        by ring
    _ = _ := by rw [res_pw_mul_pw w hw hw' V (topRes T V) m, _root_.mul_one]

include hw hw' in
/-- The restriction of `w^m · w^i` is the restriction of `w^{m+i}`. -/
theorem res_pw_mul (V : (Opens T.carrier)ᵒᵖ) (e : op (⊤ : Opens T.carrier) ⟶ V) (m i : ℤ) :
    DirectSum.of ((laurent L).sectionsPiece V) m (((laurent L).piece m).val.restrictₛₗ e (pw w m)) *
        DirectSum.of _ i (((laurent L).piece i).val.restrictₛₗ e (pw w i)) =
      DirectSum.of _ (m + i) (((laurent L).piece (m + i)).val.restrictₛₗ e (pw w (m + i))) := by
  rw [← res_of, ← res_of, ← res_of, of_pw w hw hw', of_pw w hw hw', of_pw w hw hw', ← map_mul,
    ← Units.val_mul, ← zpow_add]

include hw hw' in
/-- **The contraction identity**: multiplying by `w^i` and then taking the degree-`(-m)`
coordinate is taking the degree-`(-(m+i))` coordinate. -/
theorem secHom_mul_coord (m i : ℤ) :
    (secHom ((laurent L).piece i) (pw w i) ▷ (laurent L).piece (-(m + i))) ≫
        mulHom (laurent L) i (-(m + i)) ≫
          eqToHom (congrArg (laurent L).piece (by ring : i + -(m + i) = -m)) ≫ coord w m =
      (λ_ _).hom ≫ coord w (m + i) := by
  refine tensor_hom_ext fun V (r : (structureRingSheaf T.toRingedSpace).obj.obj V) y => ?_
  have eL1 := whiskerRight_tmul (secHom ((laurent L).piece i) (pw w i)) V r y
  have eL2 : (secHom ((laurent L).piece i) (pw w i)).val.app V r =
      r • ((laurent L).piece i).val.restrictₛₗ (topRes T V) (pw w i) := secHom_app _ _ V r
  have eL3 := mulHom_tmul (laurent L) i (-(m + i)) V
    (r • ((laurent L).piece i).val.restrictₛₗ (topRes T V) (pw w i)) y
  have eR1 := leftUnitor_hom_tmul (Z := T.toRingedSpace) (B := (laurent L).piece (-(m + i))) V r y
  change (coord w m).val.app V ((eqToHom (congrArg (laurent L).piece
      (by ring : i + -(m + i) = -m))).val.app V ((mulHom (laurent L) i (-(m + i))).val.app V
        ((secHom ((laurent L).piece i) (pw w i) ▷ (laurent L).piece (-(m + i))).val.app V
          (tmul T.toRingedSpace (𝟙_ _) _ V r y)))) =
    (coord w (m + i)).val.app V ((λ_ ((laurent L).piece (-(m + i)))).hom.val.app V
      (tmul T.toRingedSpace (𝟙_ _) _ V r y))
  rw [eL1, eL2, eL3, eR1, coord_app, coord_app]
  apply DirectSum.of_injective (β := (laurent L).sectionsPiece V) (0 : ℤ)
  rw [of_eqToHom (add_neg_cancel m), of_eqToHom (add_neg_cancel (m + i)), ← of_mul_of,
    ← of_mul_of, of_eqToHom (by ring : i + -(m + i) = -m), ← of_mul_of,
    smul_of V r i (((laurent L).piece i).val.restrictₛₗ (topRes T V) (pw w i)),
    smul_of V r (-(m + i)) y, ← res_pw_mul w hw hw' V (topRes T V) m i]
  ring

include hw hw' in
/-- **The trivializations are compatible with multiplication by `w^i`**:
`w^i · w^{-(m+i)} = w^{-m}`, as morphisms out of the structure sheaf. -/
theorem secHom_tensor_triv (m i : ℤ) :
    (λ_ _).inv ≫ (secHom ((laurent L).piece i) (pw w i) ⊗ₘ triv w (m + i)) ≫
        mulHom (laurent L) i (-(m + i)) ≫
          eqToHom (congrArg (laurent L).piece (by ring : i + -(m + i) = -m)) = triv w m := by
  apply (SheafOfModules.unitHomEquiv _).injective
  ext V
  change (eqToHom (congrArg (laurent L).piece (by ring : i + -(m + i) = -m))).val.app V
      ((mulHom (laurent L) i (-(m + i))).val.app V
        ((secHom ((laurent L).piece i) (pw w i) ⊗ₘ triv w (m + i)).val.app V
          ((λ_ (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)))).inv.val.app V
            (oneSec T.toRingedSpace V)))) = (triv w m).val.app V (oneSec T.toRingedSpace V)
  rw [leftUnitor_inv_app, tensorHom_tmul, mulHom_tmul]
  rw [secHom_app_oneSec ((laurent L).piece i) (pw w i) V,
    show (triv w (m + i)).val.app V (oneSec T.toRingedSpace V) = _ from
      secHom_app_oneSec ((laurent L).piece (-(m + i))) (pw w (-(m + i))) V,
    show (triv w m).val.app V (oneSec T.toRingedSpace V) = _ from
      secHom_app_oneSec ((laurent L).piece (-m)) (pw w (-m)) V]
  apply DirectSum.of_injective (β := (laurent L).sectionsPiece V) (-m)
  rw [of_eqToHom (by ring : i + -(m + i) = -m), ← of_mul_of, res_pw_mul w hw hw' V _ i (-(m + i)),
    ← res_of, ← res_of, of_pw w hw hw', of_pw w hw hw', show i + -(m + i) = -m by ring]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentSections

end
