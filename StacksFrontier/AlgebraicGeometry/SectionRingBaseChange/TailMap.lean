module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.SectionAlgebra

/-!
# Ring homomorphisms between the section rings of two tail truncations

Let `P₁` be a sheaf of `ℤ`-graded algebras on a scheme `T` and `P₂` one on a scheme `S`, and let
`V ⊆ T`, `U ⊆ S` be opens.  Suppose given a ring map `ρ : Γ(T, V) → Γ(S, U)` and, in every
degree `n ≥ e`, an additive map `Φ_n : Γ(V, P₁_n) → Γ(U, P₂_n)` which is semilinear along `ρ` and
multiplicative in every bidegree `(n, m)` with `n, m ≥ e`.  For cuts `0 < d ≤ e`, this file
assembles these into a homomorphism of graded rings

`Γ(V, 𝒪_T ⊕ ⨁_{n ≥ e} P₁_n) ⟶ Γ(U, 𝒪_S ⊕ ⨁_{n ≥ d} P₂_n)`

between the graded rings of sections of the two tail truncations of
`Stacks.AlgebraicGeometry.SectionAlgebra.tailSheafGradedAlgebra`: `ρ` in degree zero, `Φ_n` in
each degree `n ≥ e`, and zero in between, where the source vanishes.

This is the shape of the comparison map of the proof of [Stacks, Tag 0D4F] (3) from the section
algebra of a Noetherian model to the section algebra of a deformation.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailMapApp`: the degreewise map.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailMapRingHom`: the ring homomorphism of the
  graded rings of sections.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailMapApp_mul`: the degreewise map carries
  products to products in every bidegree.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.tailMapRingHom_of`: the ring homomorphism on a
  homogeneous element.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open Stacks.AlgebraicGeometry.SectionAlgebra

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

variable {T S : Scheme.{u}}
  (P₁ : SheafOfModules.GradedAlgebra.{u, u} T.ringCatSheaf)
  (P₂ : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)
  (e d : ℕ) (he : 0 < e) (hd : 0 < d) (hde : d ≤ e) (V : T.Opens) (U : S.Opens)
  (ρ : T.ringCatSheaf.obj.obj (op V) →+* S.ringCatSheaf.obj.obj (op U))
  (Φ : ∀ n : ℤ, (P₁.piece n).val.obj (op V) →+ (P₂.piece n).val.obj (op U))

/-- **The degreewise map of the two tail truncations**: `ρ` in degree zero, `Φ_n` in each degree
`n ≥ e` (both truncations are the algebra there), and zero otherwise. -/
def tailMapApp (n : ℤ) :
    (tailPiece P₁ e n).val.obj (op V) →+ (tailPiece P₂ d n).val.obj (op U) :=
  if h0 : n = 0 then
    (ConcreteCategory.hom ((eqToHom (tailPiece_eq_unit P₂ d h0).symm).val.app
        (op U))).toAddMonoidHom.comp
      (((AddMonoidHom.mk' (ProjF1Dehomogenization.toUnit S.ringCatSheaf (W := op U))
          (fun _ _ => rfl)).comp ρ.toAddMonoidHom).comp
        ((ProjF1Dehomogenization.ofUnitHom T.ringCatSheaf (op V)).comp
          (ConcreteCategory.hom ((eqToHom (tailPiece_eq_unit P₁ e h0)).val.app
            (op V))).toAddMonoidHom))
  else if hn : (e : ℤ) ≤ n then
    (ConcreteCategory.hom ((eqToHom (tailPiece_eq_piece P₂ d hd
        (show (d : ℤ) ≤ n by omega)).symm).val.app (op U))).toAddMonoidHom.comp
      ((Φ n).comp (ConcreteCategory.hom ((eqToHom (tailPiece_eq_piece P₁ e he hn)).val.app
        (op V))).toAddMonoidHom)
  else 0

variable {P₁ P₂ e d he hd hde V U ρ Φ}

/-- In degree zero, the degreewise map is `ρ` transported along the identifications of both
degree-zero pieces with the structure sheaf. -/
theorem tailMapApp_zero {n : ℤ} (h0 : n = 0) (x : (tailPiece P₁ e n).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ n x =
      (eqToHom (tailPiece_eq_unit P₂ d h0).symm).val.app (op U)
        (ProjF1Dehomogenization.toUnit _ (ρ (ProjF1Dehomogenization.ofUnit _
          ((eqToHom (tailPiece_eq_unit P₁ e h0)).val.app (op V) x)))) := by
  unfold tailMapApp
  rw [dite_eq_left h0]
  rfl

/-- In a nonzero degree `n ≥ e`, the degreewise map is `Φ_n` transported along the identifications
of both pieces with the degree-`n` piece of the algebra. -/
theorem tailMapApp_tail {n : ℤ} (h0 : ¬ n = 0) (hn : (e : ℤ) ≤ n)
    (x : (tailPiece P₁ e n).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ n x =
      (eqToHom (tailPiece_eq_piece P₂ d hd (show (d : ℤ) ≤ n by omega)).symm).val.app (op U)
        (Φ n ((eqToHom (tailPiece_eq_piece P₁ e he hn)).val.app (op V) x)) := by
  unfold tailMapApp
  rw [dite_eq_right h0, dite_eq_left hn]
  rfl

/-- In a nonzero degree `n < e`, where the source piece vanishes, the degreewise map is zero. -/
theorem tailMapApp_null {n : ℤ} (h0 : ¬ n = 0) (hn : ¬ (e : ℤ) ≤ n)
    (x : (tailPiece P₁ e n).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ n x = 0 := by
  unfold tailMapApp
  rw [dite_eq_right h0, dite_eq_right hn]
  rfl

/-- The family `Φ` respects a reindexing of its degree, up to heterogeneous equality. -/
theorem heq_map_of_heq {n n' : ℤ} (h : n = n') (z : (P₁.piece n).val.obj (op V))
    (z' : (P₁.piece n').val.obj (op V)) (hz : HEq z' z) : HEq (Φ n' z') (Φ n z) := by
  subst h
  cases eq_of_heq hz
  rfl

/-- `(0, 0)`: the ring map `ρ` is multiplicative. -/
theorem tailMapApp_mul_zz {i j : ℤ} (hi : i = 0) (hj : j = 0)
    (x : (tailPiece P₁ e i).val.obj (op V)) (y : (tailPiece P₁ e j).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ (i + j) ((tailMul P₁ e he i j).app (op V) x y) =
      (tailMul P₂ d hd i j).app (op U) (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ i x)
        (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ j y) := by
  rw [tailMul_app_zz P₁ e he hi hj (by omega), tailMapApp_zero (show i + j = 0 by omega),
    eqToHom_app_eqToHom_app, tailMapApp_zero hi, tailMapApp_zero hj,
    tailMul_app_zz P₂ d hd hi hj (by omega), eqToHom_app_eqToHom_app, eqToHom_app_eqToHom_app]
  exact congrArg _ (congrArg _ (map_mul ρ _ _))

variable (hsmul : ∀ (n : ℤ) (r : T.ringCatSheaf.obj.obj (op V)) (x : (P₁.piece n).val.obj (op V)),
    Φ n (r • x) = ρ r • Φ n x)
  (hmul : ∀ n m : ℤ, (e : ℤ) ≤ n → (e : ℤ) ≤ m → ∀ (x : (P₁.piece n).val.obj (op V))
    (y : (P₁.piece m).val.obj (op V)),
    Φ (n + m) ((P₁.mul n m).app (op V) x y) = (P₂.mul n m).app (op U) (Φ n x) (Φ m y))

include hsmul in
/-- `(0, tail)`: semilinearity of `Φ`. -/
theorem tailMapApp_mul_zt {i j : ℤ} (hi : i = 0) (hj : ¬ j = 0) (hjt : (e : ℤ) ≤ j)
    (x : (tailPiece P₁ e i).val.obj (op V)) (y : (tailPiece P₁ e j).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ (i + j) ((tailMul P₁ e he i j).app (op V) x y) =
      (tailMul P₂ d hd i j).app (op U) (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ i x)
        (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ j y) := by
  rw [tailMul_app_zt P₁ e he hi hj hjt (show j = i + j by omega)
      (show (e : ℤ) ≤ i + j by omega),
    tailMapApp_tail (show ¬ i + j = 0 by omega) (show (e : ℤ) ≤ i + j by omega),
    tailMapApp_zero hi, tailMapApp_tail hj hjt,
    tailMul_app_zt P₂ d hd hi hj (show (d : ℤ) ≤ j by omega) (show j = i + j by omega)
      (show (d : ℤ) ≤ i + j by omega),
    eqToHom_app_eqToHom_app, eqToHom_app_eqToHom_app]
  refine eq_of_heq ((heq_eqToHom_app_of_eq _ _ _).trans (HEq.trans ?_
    (heq_eqToHom_app_of_eq _ _ _).symm))
  refine (heq_map_of_heq (show j = i + j by omega) _ _
    ((heq_eqToHom_app_of_eq _ _ _).trans (heq_eqToHom_app_of_eq _ _ _))).trans ?_
  rw [hsmul]
  rfl

include hsmul in
/-- `(tail, 0)`: semilinearity of `Φ`, on the other side. -/
theorem tailMapApp_mul_tz {i j : ℤ} (hi : ¬ i = 0) (hit : (e : ℤ) ≤ i) (hj : j = 0)
    (x : (tailPiece P₁ e i).val.obj (op V)) (y : (tailPiece P₁ e j).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ (i + j) ((tailMul P₁ e he i j).app (op V) x y) =
      (tailMul P₂ d hd i j).app (op U) (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ i x)
        (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ j y) := by
  rw [tailMul_app_tz P₁ e he hi hit hj (show i = i + j by omega)
      (show (e : ℤ) ≤ i + j by omega),
    tailMapApp_tail (show ¬ i + j = 0 by omega) (show (e : ℤ) ≤ i + j by omega),
    tailMapApp_zero hj, tailMapApp_tail hi hit,
    tailMul_app_tz P₂ d hd hi (show (d : ℤ) ≤ i by omega) hj (show i = i + j by omega)
      (show (d : ℤ) ≤ i + j by omega),
    eqToHom_app_eqToHom_app, eqToHom_app_eqToHom_app]
  refine eq_of_heq ((heq_eqToHom_app_of_eq _ _ _).trans (HEq.trans ?_
    (heq_eqToHom_app_of_eq _ _ _).symm))
  refine (heq_map_of_heq (show i = i + j by omega) _ _
    ((heq_eqToHom_app_of_eq _ _ _).trans (heq_eqToHom_app_of_eq _ _ _))).trans ?_
  rw [hsmul]
  rfl

include hmul in
/-- `(tail, tail)`: multiplicativity of `Φ`. -/
theorem tailMapApp_mul_tt {i j : ℤ} (hi : ¬ i = 0) (hit : (e : ℤ) ≤ i) (hj : ¬ j = 0)
    (hjt : (e : ℤ) ≤ j)
    (x : (tailPiece P₁ e i).val.obj (op V)) (y : (tailPiece P₁ e j).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ (i + j) ((tailMul P₁ e he i j).app (op V) x y) =
      (tailMul P₂ d hd i j).app (op U) (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ i x)
        (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ j y) := by
  rw [tailMul_app_tt P₁ e he hi hit hj hjt (show (e : ℤ) ≤ i + j by omega),
    tailMapApp_tail (show ¬ i + j = 0 by omega) (show (e : ℤ) ≤ i + j by omega),
    eqToHom_app_eqToHom_app, hmul i j hit hjt, tailMapApp_tail hi hit, tailMapApp_tail hj hjt,
    tailMul_app_tt P₂ d hd hi (show (d : ℤ) ≤ i by omega) hj (show (d : ℤ) ≤ j by omega)
      (show (d : ℤ) ≤ i + j by omega),
    eqToHom_app_eqToHom_app, eqToHom_app_eqToHom_app]

include hsmul hmul in
/-- **The degreewise map is multiplicative** in every bidegree. -/
theorem tailMapApp_mul (i j : ℤ)
    (x : (tailPiece P₁ e i).val.obj (op V)) (y : (tailPiece P₁ e j).val.obj (op V)) :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ (i + j) ((tailMul P₁ e he i j).app (op V) x y) =
      (tailMul P₂ d hd i j).app (op U) (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ i x)
        (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ j y) := by
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · exact tailMapApp_mul_zz hi hj x y
    · by_cases hjt : (e : ℤ) ≤ j
      · exact tailMapApp_mul_zt hsmul hi hj hjt x y
      · rw [tailMul_app_eq_zero P₁ e he (Or.inr ⟨hj, hjt⟩), map_zero,
          tailMapApp_null hj hjt, map_zero]
  · by_cases hit : (e : ℤ) ≤ i
    · by_cases hj : j = 0
      · exact tailMapApp_mul_tz hsmul hi hit hj x y
      · by_cases hjt : (e : ℤ) ≤ j
        · exact tailMapApp_mul_tt hmul hi hit hj hjt x y
        · rw [tailMul_app_eq_zero P₁ e he (Or.inr ⟨hj, hjt⟩), map_zero,
            tailMapApp_null hj hjt, map_zero]
    · rw [tailMul_app_eq_zero P₁ e he (Or.inl ⟨hi, hit⟩), map_zero,
        tailMapApp_null hi hit, map_zero, AddMonoidHom.zero_apply]

variable (hcomm₁ : IsCommutative P₁) (hqc₁ : ∀ n : ℤ, ((P₁.piece n : T.Modules)).IsQuasicoherent)
  (hcomm₂ : IsCommutative P₂) (hqc₂ : ∀ n : ℤ, ((P₂.piece n : S.Modules)).IsQuasicoherent)

/-- An isomorphism of sheaves of modules is bijective on sections. -/
theorem bijective_iso_hom_app' {Z : Scheme.{u}} {N N' : SheafOfModules.{u} Z.ringCatSheaf}
    (φ : N ≅ N') (W : (Z.Opens)ᵒᵖ) : Function.Bijective (φ.hom.val.app W) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨φ.inv.val.app W, fun x => ?_, fun y => ?_⟩
  · exact congrArg (fun ψ : N ⟶ N => ψ.val.app W x) φ.hom_inv_id
  · exact congrArg (fun ψ : N' ⟶ N' => ψ.val.app W y) φ.inv_hom_id

/-- Transport along an equality of sheaves of modules is linear. -/
theorem eqToHom_app_smul {Z : Scheme.{u}} {M N : SheafOfModules.{u} Z.ringCatSheaf} (h : M = N)
    (W : (Z.Opens)ᵒᵖ) (r : Z.ringCatSheaf.obj.obj W) (x : M.val.obj W) :
    (eqToHom h).val.app W (r • x) = r • (eqToHom h).val.app W x := by
  cases h
  rfl

/-- Transporting a multiple of a transported section back is the multiple of the section. -/
theorem eqToHom_app_smul_eqToHom_app {Z : Scheme.{u}} {M N : SheafOfModules.{u} Z.ringCatSheaf}
    (h : M = N) (W : (Z.Opens)ᵒᵖ) (r : Z.ringCatSheaf.obj.obj W) (x : M.val.obj W) :
    (eqToHom h.symm).val.app W (r • (eqToHom h).val.app W x) = r • x := by
  cases h
  rfl

/-- The degreewise map carries the unit to the unit. -/
theorem tailMapApp_one :
    tailMapApp P₁ P₂ e d he hd hde V U ρ Φ 0 ((tailOne P₁ e).eval (op V)) =
      (tailOne P₂ d).eval (op U) := by
  rw [tailMapApp_zero rfl, tailOne_eval, eqToHom_app_eqToHom_app, tailOne_eval]
  exact congrArg _ (congrArg _ (map_one ρ))

/-- The degreewise map, typed on the homogeneous sections of the two tail truncations. -/
def tailMapPiece (n : ℕ) :
    (tailSheafGradedAlgebra P₁ e he hcomm₁ hqc₁).sectionPieces V n →+
      (tailSheafGradedAlgebra P₂ d hd hcomm₂ hqc₂).sectionPieces U n :=
  tailMapApp P₁ P₂ e d he hd hde V U ρ Φ (n : ℤ)

include hsmul hmul in
/-- **The homomorphism of the graded rings of sections of the two tail truncations**: `ρ` in
degree zero, `Φ_n` in each degree `n ≥ e`, zero in between. -/
def tailMapRingHom :
    (tailSheafGradedAlgebra P₁ e he hcomm₁ hqc₁).sectionRing V →+*
      (tailSheafGradedAlgebra P₂ d hd hcomm₂ hqc₂).sectionRing U :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (fun n => (tailSheafGradedAlgebra P₂ d hd hcomm₂ hqc₂).sectionPieces
      U n) n).comp (tailMapPiece (ρ := ρ) (Φ := Φ) (hde := hde) hcomm₁ hqc₁ hcomm₂ hqc₂ n))
    ((congrArg (DirectSum.of _ 0) (tailMapApp_one (P₁ := P₁) (P₂ := P₂) (he := he) (hd := hd)
      (hde := hde) (ρ := ρ) (Φ := Φ))).trans (DirectSum.one_def _).symm)
    (fun {i j} a b =>
      (congrArg (DirectSum.of _ (i + j)) (tailMapApp_mul hsmul hmul (i : ℤ) (j : ℤ) a b)).trans
        (DirectSum.of_mul_of _ _).symm)

/-- The ring homomorphism sends a homogeneous element `a` of degree `n` to the homogeneous element
`tailMapPiece n a` of degree `n`. -/
theorem tailMapRingHom_of {n : ℕ}
    (a : (tailSheafGradedAlgebra P₁ e he hcomm₁ hqc₁).sectionPieces V n) :
    tailMapRingHom (hd := hd) (hde := hde) (hsmul := hsmul) (hmul := hmul) hcomm₁ hqc₁ hcomm₂ hqc₂
        (DirectSum.of _ n a) =
      DirectSum.of _ n (tailMapPiece (hd := hd) (ρ := ρ) (Φ := Φ) (hde := hde) hcomm₁ hqc₁ hcomm₂
        hqc₂ n a) :=
  DirectSum.toSemiring_of _ _ _ n a

include hsmul hmul in
/-- **The homomorphism of section rings lies over `ρ`.** -/
theorem tailMapRingHom_strHom (r : Γ(T, V)) :
    tailMapRingHom (hd := hd) (hde := hde) (hsmul := hsmul) (hmul := hmul) hcomm₁ hqc₁ hcomm₂ hqc₂
        ((tailSheafGradedAlgebra P₁ e he hcomm₁ hqc₁).strHom V r) =
      (tailSheafGradedAlgebra P₂ d hd hcomm₂ hqc₂).strHom U (ρ r) := by
  refine (congrArg _ (SheafGradedAlgebra.strHom_apply _ V r)).trans ?_
  refine (tailMapRingHom_of hsmul hmul hcomm₁ hqc₁ hcomm₂ hqc₂ _).trans ?_
  refine Eq.trans ?_ (SheafGradedAlgebra.strHom_apply _ U (ρ r)).symm
  refine congrArg (DirectSum.of _ 0) ?_
  refine (tailMapApp_zero rfl _).trans ?_
  have h1 : (tailSheafGradedAlgebra P₁ e he hcomm₁ hqc₁).one V = (tailOne P₁ e).eval (op V) := rfl
  have h2 : (tailSheafGradedAlgebra P₂ d hd hcomm₂ hqc₂).one U = (tailOne P₂ d).eval (op U) := rfl
  rw [h1, h2, tailOne_eval, tailOne_eval]
  have hV := eqToHom_app_smul_eqToHom_app (tailPiece_eq_unit P₁ e (rfl : (0 : ℤ) = 0)).symm
    (op V) (show T.ringCatSheaf.obj.obj (op V) from r)
    ((ProjF1Dehomogenization.unitSections T.ringCatSheaf).eval (op V))
  have hU := eqToHom_app_smul (tailPiece_eq_unit P₂ d (rfl : (0 : ℤ) = 0)).symm (op U) (ρ r)
    ((ProjF1Dehomogenization.unitSections S.ringCatSheaf).eval (op U))
  refine Eq.trans ?_ hU.symm
  refine congrArg _ ?_
  refine (congrArg (fun z => ProjF1Dehomogenization.toUnit _ (ρ (ProjF1Dehomogenization.ofUnit _
    z))) hV).trans ?_
  exact congrArg (fun z => ProjF1Dehomogenization.toUnit _ z)
    ((congrArg ρ (mul_one (show T.ringCatSheaf.obj.obj (op V) from r))).trans
      (mul_one (ρ r)).symm)

/-- With equal cuts, the degreewise map is bijective as soon as `ρ` and every `Φ_n`, `n ≥ e`, are:
outside `{0} ∪ [e, ∞)` both pieces vanish. -/
theorem bijective_tailMapApp (hed : e = d) (hρ : Function.Bijective ρ)
    (hΦ : ∀ n : ℤ, (e : ℤ) ≤ n → Function.Bijective (Φ n)) (n : ℤ) :
    Function.Bijective (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ n) := by
  by_cases h0 : n = 0
  · have hfun : (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ n : _ → _) =
        (eqToHom (tailPiece_eq_unit P₂ d h0).symm).val.app (op U) ∘
          (fun z => ProjF1Dehomogenization.toUnit _ (ρ (ProjF1Dehomogenization.ofUnit _ z))) ∘
            (eqToHom (tailPiece_eq_unit P₁ e h0)).val.app (op V) :=
      funext fun x => tailMapApp_zero h0 x
    rw [hfun]
    refine (bijective_iso_hom_app' (eqToIso (tailPiece_eq_unit P₂ d h0).symm) (op U)).comp
      ((hρ.comp Function.bijective_id).comp
        (bijective_iso_hom_app' (eqToIso (tailPiece_eq_unit P₁ e h0)) (op V)))
  · by_cases hn : (e : ℤ) ≤ n
    · have hfun : (tailMapApp P₁ P₂ e d he hd hde V U ρ Φ n : _ → _) =
          (eqToHom (tailPiece_eq_piece P₂ d hd (show (d : ℤ) ≤ n by omega)).symm).val.app (op U) ∘
            (Φ n) ∘ (eqToHom (tailPiece_eq_piece P₁ e he hn)).val.app (op V) :=
        funext fun x => tailMapApp_tail h0 hn x
      rw [hfun]
      exact (bijective_iso_hom_app' (eqToIso (tailPiece_eq_piece P₂ d hd
        (show (d : ℤ) ≤ n by omega)).symm) (op U)).comp ((hΦ n hn).comp
        (bijective_iso_hom_app' (eqToIso (tailPiece_eq_piece P₁ e he hn)) (op V)))
    · refine ⟨fun x y _ => (eq_zero_of_tailPiece P₁ e h0 hn _ x).trans
        (eq_zero_of_tailPiece P₁ e h0 hn _ y).symm, fun z => ⟨0, ?_⟩⟩
      rw [eq_zero_of_tailPiece P₂ d h0 (by omega) _ z, map_zero]

include hsmul hmul in
/-- With equal cuts, the homomorphism of section rings is bijective as soon as `ρ` and every
`Φ_n`, `n ≥ e`, are. -/
theorem bijective_tailMapRingHom (hed : e = d) (hρ : Function.Bijective ρ)
    (hΦ : ∀ n : ℤ, (e : ℤ) ≤ n → Function.Bijective (Φ n)) :
    Function.Bijective (tailMapRingHom (he := he) (hd := hd) (hde := hde) (hsmul := hsmul)
      (hmul := hmul) hcomm₁ hqc₁ hcomm₂ hqc₂) := by
  have hfun : (tailMapRingHom (he := he) (hd := hd) (hde := hde) (hsmul := hsmul) (hmul := hmul)
      hcomm₁ hqc₁ hcomm₂ hqc₂ : _ → _) =
      DirectSum.map (fun n => tailMapPiece (he := he) (hd := hd) (ρ := ρ) (Φ := Φ) (hde := hde)
        hcomm₁ hqc₁ hcomm₂ hqc₂ n) := by
    funext x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n a =>
      rw [tailMapRingHom_of, DirectSum.map_of]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hfun]
  exact ⟨(DirectSum.map_injective _).mpr fun n =>
      (bijective_tailMapApp hed hρ hΦ (n : ℤ)).1,
    (DirectSum.map_surjective _).mpr fun n => (bijective_tailMapApp hed hρ hΦ (n : ℤ)).2⟩

end Stacks.AlgebraicGeometry.SectionRingBaseChange

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

/-! ### The degree-zero part and the tail of a single tail truncation -/

section Single

variable {T : Scheme.{u}}

variable (P : SheafOfModules.GradedAlgebra.{u, u} T.ringCatSheaf) (e : ℕ) (he : 0 < e)
  (hcomm : IsCommutative P) (hqc : ∀ n : ℤ, ((P.piece n : T.Modules)).IsQuasicoherent)
  (V : T.Opens)

/-- **The degree-zero part of a tail truncation is the structure sheaf**: multiplying its unit by
the functions on an open is bijective onto the degree-zero sections. -/
theorem bijective_smul_one_tail :
    Function.Bijective fun r : Γ(T, V) => r • (tailSheafGradedAlgebra P e he hcomm hqc).one V := by
  have hfun : (fun r : Γ(T, V) => r • (tailSheafGradedAlgebra P e he hcomm hqc).one V) =
      (eqToHom (tailPiece_eq_unit P e (rfl : (0 : ℤ) = 0)).symm).val.app (op V) ∘
        fun r => ProjF1Dehomogenization.toUnit _ (show T.ringCatSheaf.obj.obj (op V) from r) := by
    funext r
    have h1 := eqToHom_app_smul (tailPiece_eq_unit P e (rfl : (0 : ℤ) = 0)).symm (op V)
      (show T.ringCatSheaf.obj.obj (op V) from r)
      ((ProjF1Dehomogenization.unitSections T.ringCatSheaf).eval (op V))
    exact h1.symm.trans (congrArg _ (congrArg (ProjF1Dehomogenization.toUnit _)
      (mul_one (show T.ringCatSheaf.obj.obj (op V) from r))))
  rw [hfun]
  exact (bijective_iso_hom_app' (eqToIso (tailPiece_eq_unit P e (rfl : (0 : ℤ) = 0)).symm)
    (op V)).comp ⟨fun _ _ h => h, fun z => ⟨ProjF1Dehomogenization.ofUnit _ z, rfl⟩⟩

/-- The inclusion of a section of `P_n`, `n ≥ e`, as a homogeneous element of the section ring
of the tail truncation. -/
def tailIncl (n : ℕ) (hn : e ≤ n) :
    (P.piece (n : ℤ)).val.obj (op V) →+ (tailSheafGradedAlgebra P e he hcomm hqc).sectionRing V :=
  (DirectSum.of (fun n => (tailSheafGradedAlgebra P e he hcomm hqc).sectionPieces V n) n).comp
    (ConcreteCategory.hom ((eqToHom (tailPiece_eq_piece P e he
      (show (e : ℤ) ≤ (n : ℤ) by omega)).symm).val.app (op V))).toAddMonoidHom

/-- Every homogeneous element of degree `n ≥ e` is the inclusion of a section of `P_n`. -/
theorem exists_tailIncl_eq (n : ℕ) (hn : e ≤ n)
    (y : (tailSheafGradedAlgebra P e he hcomm hqc).sectionPieces V n) :
    ∃ x, tailIncl P e he hcomm hqc V n hn x = DirectSum.of _ n y := by
  obtain ⟨x, hx⟩ := (bijective_iso_hom_app' (eqToIso (tailPiece_eq_piece P e he
    (show (e : ℤ) ≤ (n : ℤ) by omega)).symm) (op V)).2 y
  exact ⟨x, congrArg (DirectSum.of _ n) hx⟩

/-- **The inclusions of the tail are multiplicative.** -/
theorem tailIncl_mul (n m : ℕ) (hn : e ≤ n) (hm : e ≤ m)
    (x : (P.piece (n : ℤ)).val.obj (op V)) (y : (P.piece (m : ℤ)).val.obj (op V)) :
    tailIncl P e he hcomm hqc V n hn x * tailIncl P e he hcomm hqc V m hm y =
      tailIncl P e he hcomm hqc V (n + m) (by omega) ((P.mul (n : ℤ) (m : ℤ)).app (op V) x y) := by
  refine (DirectSum.of_mul_of _ _).trans (congrArg (DirectSum.of _ (n + m)) ?_)
  refine (tailMul_app_tt P e he (show ¬ (n : ℤ) = 0 by omega) (show (e : ℤ) ≤ n by omega)
    (show ¬ (m : ℤ) = 0 by omega) (show (e : ℤ) ≤ m by omega)
    (show (e : ℤ) ≤ (n : ℤ) + (m : ℤ) by omega) (op V) _ _).trans ?_
  exact congrArg _ (congrArg₂ (fun a b => ((P.mul (n : ℤ) (m : ℤ)).app (op V)) a b)
    (eqToHom_app_eqToHom_app _ _ (op V) x) (eqToHom_app_eqToHom_app _ _ (op V) y))

end Single

end Stacks.AlgebraicGeometry.SectionRingBaseChange
