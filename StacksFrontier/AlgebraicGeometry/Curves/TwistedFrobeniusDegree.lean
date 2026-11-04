module

public import StacksFrontier.AlgebraicGeometry.Curves.FrobeniusTwistCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Iterated
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# The degree of a twisted Frobenius of a curve

Let `C` be a smooth proper curve over a perfect field `k` of characteristic `p`. The absolute
Frobenius `F` of `C` is the relative Frobenius `C ⟶ C^{(p)}` followed by the projection
`C^{(p)} = C ×_{k, F} k ⟶ C`, which is an isomorphism because the Frobenius of `k` is; so `F` has
degree `p` ([Stacks, Tag 0CCF]), and by the tower law ([Stacks, Tag 02NZ]) its `f`-fold iterate
has degree `p ^ f`. A *twisted Frobenius* is an endomorphism `φ` of `C` over `k` with
`Ψ ≫ φ = F^f` for an automorphism `Ψ` of the scheme `C`; as `F^f` commutes with `Ψ⁻¹`,
`φ = F^f ≫ Ψ⁻¹`, and `φ` has degree `p ^ f`.

## Main results

* `AlgebraicGeometry.degreeOver_comp_of_pos`: the tower law for `AlgebraicGeometry.degreeOver`.
* `AlgebraicGeometry.degreeOver_absoluteFrobenius_curve`: `deg F = p`.
* `AlgebraicGeometry.degreeOver_absoluteFrobeniusPow_curve`: `deg F^n = p ^ n`.
* `AlgebraicGeometry.degreeOver_eq_pow_of_comp_eq_absoluteFrobeniusPow`: a twisted Frobenius
  `φ` with `Ψ ≫ φ = F^f` has degree `p ^ f`, with the instance arguments of `degreeOver` written
  as `AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul` writes them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- **The tower law for the degree** ([Stacks, Tag 02NZ]): for dominant morphisms of integral
schemes, locally of finite type, with finite extensions of function fields,
`deg(f ≫ g) = deg f · deg g`. -/
theorem degreeOver_comp_of_pos {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [LocallyOfFiniteType f] [IsDominant f] [LocallyOfFiniteType g] [IsDominant g]
    [LocallyOfFiniteType (f ≫ g)]
    (hf : 0 < degreeOver f) (hg : 0 < degreeOver g) :
    degreeOver (f ≫ g) = degreeOver f * degreeOver g := by
  let : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  let : Algebra Z.functionField Y.functionField := (dominantFunctionFieldMap g).toAlgebra
  let : Algebra Z.functionField X.functionField := (dominantFunctionFieldMap (f ≫ g)).toAlgebra
  have h1 : degreeOver f = Module.finrank Y.functionField X.functionField :=
    degreeOver_eq_finrank f rfl
  have h2 : degreeOver g = Module.finrank Z.functionField Y.functionField :=
    degreeOver_eq_finrank g rfl
  have h3 : degreeOver (f ≫ g) = Module.finrank Z.functionField X.functionField :=
    degreeOver_eq_finrank (f ≫ g) rfl
  have : FiniteDimensional Y.functionField X.functionField :=
    Module.finite_of_finrank_pos (h1 ▸ hf)
  have : FiniteDimensional Z.functionField Y.functionField :=
    Module.finite_of_finrank_pos (h2 ▸ hg)
  rw [h3, finrank_functionField_comp f g rfl rfl rfl, ← h1, ← h2]

/-- The degree only depends on the morphism, not on the proofs of its instance arguments. -/
theorem degreeOver_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') [IsIntegral X]
    [IsIntegral Y] [LocallyOfFiniteType f] [IsDominant f] [LocallyOfFiniteType f']
    [IsDominant f'] : degreeOver f = degreeOver f' := by
  subst h
  rfl

/-- Over a perfect field the absolute Frobenius of the spectrum is an isomorphism. -/
theorem isIso_absoluteFrobenius_spec_of_perfectRing (k : Type u) [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [PerfectRing k p] (hS : IsInCharacteristic (Spec (.of k)) p) :
    IsIso (absoluteFrobenius (Spec (.of k)) p hS) := by
  have h := specMap_eq_absoluteFrobeniusPow (frobeniusEquiv k p).toRingHom p 1 hS
    (fun a => by simp [frobenius_def])
  have h1 : absoluteFrobeniusPow (Spec (.of k)) p hS 1 = absoluteFrobenius (Spec (.of k)) p hS :=
    by simp
  rw [← h1, ← h]
  have : IsIso (CommRingCat.ofHom (frobeniusEquiv k p).toRingHom) :=
    (RingEquiv.toCommRingCatIso (frobeniusEquiv k p)).isIso_hom
  infer_instance

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
  {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsCurve k pX] [Smooth pX] [IsProper pX]
  (hX : IsInCharacteristic X p)

omit [Smooth pX] [IsProper pX] in
include pX in
/-- The `n`-fold absolute Frobenius of a curve over a perfect field is locally of finite type:
composed with the structure morphism it is the structure morphism followed by the `n`-fold
Frobenius of the spectrum of the field, an isomorphism. -/
theorem locallyOfFiniteType_absoluteFrobeniusPow_curve (n : ℕ) :
    LocallyOfFiniteType (absoluteFrobeniusPow X p hX n) := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  have := isIso_absoluteFrobenius_spec_of_perfectRing k p hS
  have hiso : IsIso (absoluteFrobeniusPow (Spec (.of k)) p hS n) := by
    induction n with
    | zero => rw [absoluteFrobeniusPow_zero]; infer_instance
    | succ m ih => rw [absoluteFrobeniusPow_succ_eq_comp]; infer_instance
  have hcomp : LocallyOfFiniteType (absoluteFrobeniusPow X p hX n ≫ pX) := by
    rw [absoluteFrobeniusPow_naturality pX p hX hS n]
    infer_instance
  exact locallyOfFiniteType_of_comp _ pX

omit [CharP k p] [PerfectRing k p] [IsCurve k pX] [Smooth pX] [IsProper pX] in
include pX in
/-- The absolute Frobenius of a curve over a perfect field is the relative Frobenius followed by
an isomorphism. -/
theorem relativeFrobenius_comp_fst_curve
    (hS : IsInCharacteristic (Spec (.of k)) p) :
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left ≫
        pullback.fst pX (absoluteFrobenius (Spec (.of k)) p hS) =
      absoluteFrobenius X p hX :=
  relativeFrobenius_fst (Spec (.of k)) p hS (Over.mk pX)

omit [IsProper pX] in
include pX in
/-- The absolute Frobenius of a curve over a perfect field is dominant. -/
theorem isDominant_absoluteFrobenius_curve : IsDominant (absoluteFrobenius X p hX) := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  have := isIso_absoluteFrobenius_spec_of_perfectRing k p hS
  have : IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    isCurve_frobeniusTwist_curve p hS pX
  have := isDominant_of_not_constant k pX
    ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (not_constant_relativeFrobenius_curve p hS pX)
  have : IsDominant (pullback.fst pX (absoluteFrobenius (Spec (.of k)) p hS)) :=
    (isDominant_iff _).mpr (Function.Surjective.denseRange
      (pullback.fst pX (absoluteFrobenius (Spec (.of k)) p hS)).homeomorph.surjective)
  rw [← relativeFrobenius_comp_fst_curve p pX hX hS]
  infer_instance

include pX in
/-- **The absolute Frobenius of a smooth proper curve over a perfect field of characteristic `p`
has degree `p`** ([Stacks, Tag 0CCF]). -/
theorem degreeOver_absoluteFrobenius_curve :
    haveI := isDominant_absoluteFrobenius_curve p pX hX
    haveI : LocallyOfFiniteType (absoluteFrobenius X p hX) := by
      simpa using locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX 1
    degreeOver (absoluteFrobenius X p hX) = p := by
  have hS : IsInCharacteristic (Spec (.of k)) p :=
    isInCharacteristic_spec k p (CharP.cast_eq_zero k p)
  have := isIso_absoluteFrobenius_spec_of_perfectRing k p hS
  have : IsCurve k ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom :=
    isCurve_frobeniusTwist_curve p hS pX
  have := locallyOfFiniteType_of_isCurve_comp k pX
    ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (relativeFrobenius_curve_comp p hS pX)
  have := isDominant_of_not_constant k pX
    ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk pX)).hom
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (not_constant_relativeFrobenius_curve p hS pX)
  have := isDominant_absoluteFrobenius_curve p pX hX
  have : LocallyOfFiniteType (absoluteFrobenius X p hX) := by
    simpa using locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX 1
  rw [degreeOver_eq_degreeOver_of_isIso (absoluteFrobenius X p hX)
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left
    (pullback.fst pX (absoluteFrobenius (Spec (.of k)) p hS))
    (relativeFrobenius_comp_fst_curve p pX hX hS)]
  exact degreeOver_relativeFrobenius_curve p hS pX

include pX in
/-- **The `(n + 1)`-fold absolute Frobenius of a smooth proper curve over a perfect field of
characteristic `p` is dominant and has degree `p ^ (n + 1)`.** -/
theorem degreeOver_absoluteFrobeniusPow_curve (n : ℕ) :
    ∃ (_ : IsDominant (absoluteFrobeniusPow X p hX (n + 1))),
      haveI := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX (n + 1)
      degreeOver (absoluteFrobeniusPow X p hX (n + 1)) = p ^ (n + 1) := by
  have := isDominant_absoluteFrobenius_curve p pX hX
  have : LocallyOfFiniteType (absoluteFrobenius X p hX) := by
    simpa using locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX 1
  have h1 := degreeOver_absoluteFrobenius_curve p pX hX
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  induction n with
  | zero =>
    have hF : absoluteFrobeniusPow X p hX (0 + 1) = absoluteFrobenius X p hX := by simp
    have : IsDominant (absoluteFrobeniusPow X p hX (0 + 1)) := by rw [hF]; infer_instance
    refine ⟨inferInstance, ?_⟩
    have := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX (0 + 1)
    rw [degreeOver_congr hF, h1, zero_add, pow_one]
  | succ m ih =>
    obtain ⟨hdom, hdeg⟩ := ih
    have := hdom
    have := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX (m + 1)
    have hsucc := absoluteFrobeniusPow_succ_eq_comp X p hX (m + 1)
    have : IsDominant (absoluteFrobeniusPow X p hX (m + 1 + 1)) := by
      rw [hsucc]; infer_instance
    refine ⟨inferInstance, ?_⟩
    have := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX (m + 1 + 1)
    have key : degreeOver (absoluteFrobenius X p hX ≫ absoluteFrobeniusPow X p hX (m + 1)) =
        degreeOver (absoluteFrobenius X p hX) *
          degreeOver (absoluteFrobeniusPow X p hX (m + 1)) :=
      degreeOver_comp_of_pos _ _ (by rw [h1]; exact hpos)
        (by rw [hdeg]; exact pow_pos hpos _)
    rw [degreeOver_congr hsucc, key, h1, hdeg, ← pow_succ']

omit [Smooth pX] [IsProper pX] in
/-- **A twisted Frobenius of a curve over an algebraically closed field has degree `p ^ f`**:
if `φ` is an endomorphism of `C` over `k` and `Ψ` an automorphism of the scheme `C` with
`Ψ ≫ φ = F^f`, then `deg φ = p ^ f`. Indeed `F^f` commutes with `Ψ⁻¹`, so `φ = F^f ≫ Ψ⁻¹`, and
composing with an isomorphism does not change the degree. -/
theorem degreeOver_eq_pow_of_comp_eq_absoluteFrobeniusPow [Smooth pX] [IsProper pX]
    (φ : X ⟶ X) (w : φ ≫ pX = pX) (hnc : ¬ ∃ y : X, ∀ x : X, φ.base x = y)
    (f : ℕ) (hf : 0 < f) (Ψ : X ≅ X) (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow X p hX f) :
    @degreeOver X X φ _ _ (locallyOfFiniteType_of_isCurve_comp k pX pX φ w)
      (isDominant_of_not_constant k pX pX φ hnc) = p ^ f := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  obtain ⟨hdom, hdeg⟩ := degreeOver_absoluteFrobeniusPow_curve p pX hX n
  have := hdom
  have := locallyOfFiniteType_absoluteFrobeniusPow_curve p pX hX (n + 1)
  have := locallyOfFiniteType_of_isCurve_comp k pX pX φ w
  have := isDominant_of_not_constant k pX pX φ hnc
  have hφ : absoluteFrobeniusPow X p hX (n + 1) ≫ Ψ.inv = φ := by
    rw [absoluteFrobeniusPow_naturality Ψ.inv p hX hX (n + 1), ← hΨ, Iso.inv_hom_id_assoc]
  rw [degreeOver_eq_degreeOver_of_isIso φ (absoluteFrobeniusPow X p hX (n + 1)) Ψ.inv hφ]
  exact hdeg

end AlgebraicGeometry
