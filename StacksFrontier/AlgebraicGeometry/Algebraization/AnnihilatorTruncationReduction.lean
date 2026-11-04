module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear

/-!
# Annihilating the cohomology of a derived Hom by truncation

Let `A` be a commutative ring and let `P`, `Q` be objects of `D(A)` with `P` concentrated in
degrees `≤ d` and `Q` concentrated in degrees `≥ a`. If for every `j ≤ s + d` some element of `A`
outside a prime `p` annihilates `H^j(Q)`, then the product of those finitely many elements — one
for each degree `a ≤ j ≤ s + d`, a product which is again outside `p` because `p` is prime —
annihilates `H^i(RHom_A(P, Q))` for every `i ≤ s`.

## Main results

* `Stacks.Algebraization.prod_smul_id_eq_zero_of_isGE_of_isLE` — a product of scalars, one per
  degree, annihilates the identity of an object with bounded cohomology.
* `Stacks.Algebraization.prod_smul_eq_zero_of_isLE_of_isGE` — the same product annihilates every
  morphism from an object concentrated in degrees `≤ b` to one concentrated in degrees `≥ a`.
* `Stacks.Algebraization.prod_smul_id_derivedHom_homology_eq_zero` — the product annihilates
  `H^i(RHom_A(P, Q))` for `i ≤ s`.
* `Stacks.Algebraization.exists_notMem_mem_annihilator_homology_derivedHom` — the existence
  statement away from a prime.

## Implementation notes

Derived Hom is `StacksDraft.DerivedHom.derivedHomAdjunction`, whose `hom` field is the derived Hom
bifunctor on `D(ModuleCat A)`; `RHom_A(P, Q)` is its value at `(Opposite.op P, Q)`. Cohomology is
`DerivedCategory.homologyFunctor`, truncation is the canonical t-structure
`DerivedCategory.TStructure.t` with its `truncLE`/`truncGE` and the distinguished triangle
`triangleLEGE`, and "concentrated in degrees `≤ d`" and "`≥ a`" are `DerivedCategory.IsLE` and
`DerivedCategory.IsGE`.

Annihilation is phrased as `r • 𝟙 X = 0`, which for a module is membership in
`Module.annihilator`. This form is what the truncation induction consumes: each step of the
canonical truncation of `Q` contributes its own scalar, and the scalars are multiplied, so the
conclusion carries a product rather than a single element. The elementary step — a scalar killing
a module kills every `Ext` out of it — is the `A`-linearity of the homology functor and of the
Hom functors of an `A`-linear category, not a computation with resolutions.

A lower bound on the cohomology of `Q` is *necessary*, not a convenience: without it infinitely
many degrees `j ≤ s + d` contribute and no finite product of elements outside `p` need annihilate.
The degrees that actually enter are `a ≤ j ≤ s + d`, and the product is taken over exactly those.

## References

* [Stacks Project, Tag 0EFH](https://stacks.math.columbia.edu/tag/0EFH)
* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-- Multiplication by `r` is zero on a module exactly when `r` annihilates it. -/
public theorem smul_id_eq_zero_iff_mem_annihilator {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) (r : A) :
    r • 𝟙 M = 0 ↔ r ∈ Module.annihilator A M := by
  rw [Module.mem_annihilator]
  refine ⟨fun h x => ConcreteCategory.congr_hom h x, fun h => ?_⟩
  ext x
  exact h x

/-- A scalar annihilating the identity of an object annihilates the identity of every isomorphic
object. -/
public theorem smul_id_eq_zero_of_iso {R : Type u} [Ring R] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear R C] (r : R) {X Y : C} (e : X ≅ Y) (h : r • 𝟙 Y = 0) :
    r • 𝟙 X = 0 := by
  apply (cancel_mono e.hom).mp
  simp only [Linear.smul_comp, Category.id_comp, zero_comp]
  simpa only [Linear.comp_smul, Category.comp_id, comp_zero] using
    congrArg (fun g => e.hom ≫ g) h


/-- **The elementary step.** For an object of `D(A)` concentrated in the single degree `n`, a
scalar annihilating `H^n` annihilates the identity of the object itself. -/
public theorem smul_id_eq_zero_of_isLE_of_isGE {A : Type u} [CommRing A] (r : A) (n : ℤ)
    (X : DerivedCategory (ModuleCat.{u} A)) [X.IsLE n] [X.IsGE n]
    (h : r • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X) = 0) :
    r • 𝟙 X = 0 := by
  apply hom_eq_zero_of_isLE_isGE X X n
  rwa [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- **The two-step composition.** If `a` annihilates the identity of the first term and `b` the
identity of the third term of a distinguished triangle, then `a * b` annihilates the identity of
the middle term. -/
public theorem mul_smul_id_eq_zero_of_distinguished {R : Type u} [CommRing R] {C : Type v}
    [Category.{w} C] [Preadditive C] [Linear R C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [HasZeroObject C] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distinguishedTriangles) (a b : R)
    (ha : a • 𝟙 T.obj₁ = 0) (hb : b • 𝟙 T.obj₃ = 0) :
    (a * b) • 𝟙 T.obj₂ = 0 := by
  have hz : (b • 𝟙 T.obj₂) ≫ T.mor₂ = 0 := by
    rw [Linear.smul_comp, Category.id_comp]
    simpa using congrArg (fun f => T.mor₂ ≫ f) hb
  obtain ⟨f, hf⟩ := T.coyoneda_exact₂ hT (b • 𝟙 T.obj₂) hz
  calc
    (a * b) • 𝟙 T.obj₂ = a • (b • 𝟙 T.obj₂) := mul_smul a b _
    _ = a • (f ≫ T.mor₁) := by rw [hf]
    _ = f ≫ (a • 𝟙 T.obj₁) ≫ T.mor₁ := by simp
    _ = 0 := by rw [ha, zero_comp, comp_zero]

/-- A scalar annihilating `H^i(X)` for `i ≤ b` annihilates `H^i` of the truncation `τ≤b X`. -/
private theorem smul_id_homology_truncLE_eq_zero {A : Type u} [CommRing A] (f : ℤ → A) (b : ℤ)
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ i : ℤ, i ≤ b →
      f i • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X) = 0) (i : ℤ) :
    f i • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X).obj₁) = 0 := by
  set T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) (by omega) X
  have h₃ge : T.obj₃.IsGE (b + 1) := by
    change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsGE (b + 1)
    infer_instance
  by_cases hi : i ≤ b
  · have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₁) :=
      isIso_homology_mor₁ T hT i
        (DerivedCategory.isZero_of_isGE T.obj₃ (b + 1) i (by omega))
        (DerivedCategory.isZero_of_isGE T.obj₃ (b + 1) (i - 1) (by omega))
    exact smul_id_eq_zero_of_iso (f i)
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₁)) (hX i hi)
  · have : T.obj₁.IsLE b := by
      change ((DerivedCategory.TStructure.t.truncLE b).obj X).IsLE b
      infer_instance
    exact (DerivedCategory.isZero_of_isLE T.obj₁ b i (by omega)).eq_of_src _ _

/-- **The truncation induction.** For an object of `D(A)` concentrated in degrees `a` through
`a + n`, the product of scalars annihilating `H^j` in those degrees annihilates the identity of
the object. -/
public theorem prod_smul_id_eq_zero_of_isGE_of_isLE {A : Type u} [CommRing A] (f : ℤ → A)
    (a : ℤ) (n : ℕ) (X : DerivedCategory (ModuleCat.{u} A)) [X.IsGE a] [X.IsLE (a + n)]
    (hX : ∀ i : ℤ,
      f i • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X) = 0) :
    (∏ j ∈ Finset.range (n + 1), f (a + j)) • 𝟙 X = 0 := by
  induction n generalizing X with
  | zero =>
    have : X.IsLE a := by simpa using (inferInstance : X.IsLE (a + (0 : ℕ)))
    simpa using smul_id_eq_zero_of_isLE_of_isGE (f a) a X (hX a)
  | succ n ih =>
    set b : ℤ := a + (n : ℤ) with hb
    set T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X
    have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) (by omega) X
    have hXle : X.IsLE (b + 1) := by
      have := (inferInstance : X.IsLE (a + ((n + 1 : ℕ) : ℤ)))
      refine DerivedCategory.TStructure.t.isLE_of_le X (a + ((n + 1 : ℕ) : ℤ)) (b + 1) ?_
      push_cast [hb]
      omega
    have h₁ge : T.obj₁.IsGE a := by
      show ((DerivedCategory.TStructure.t.truncLE b).obj X).IsGE a
      infer_instance
    have h₁le : T.obj₁.IsLE (a + n) := by
      show ((DerivedCategory.TStructure.t.truncLE b).obj X).IsLE b
      infer_instance
    have h₃ge : T.obj₃.IsGE (b + 1) := by
      show ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsGE (b + 1)
      infer_instance
    have h₃le : T.obj₃.IsLE (b + 1) := by
      show ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsLE (b + 1)
      infer_instance
    have hleft : (∏ j ∈ Finset.range (n + 1), f (a + j)) • 𝟙 T.obj₁ = 0 := by
      exact ih T.obj₁ (smul_id_homology_truncLE_eq_zero f b X fun i _ => hX i)
    have hright : f (b + 1) • 𝟙 T.obj₃ = 0 := by
      refine smul_id_eq_zero_of_isLE_of_isGE (f (b + 1)) (b + 1) T.obj₃ ?_
      have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (b + 1)).map T.mor₂) :=
        isIso_homology_mor₂ T hT (b + 1)
          (DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1) (by omega))
          (DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1 + 1) (by omega))
      exact smul_id_eq_zero_of_iso (f (b + 1))
        (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (b + 1)).map T.mor₂)).symm
        (hX (b + 1))
    have hprod : (∏ j ∈ Finset.range (n + 1 + 1), f (a + (j : ℤ))) =
        (∏ j ∈ Finset.range (n + 1), f (a + (j : ℤ))) * f (b + 1) := by
      rw [Finset.prod_range_succ]
      congr 2
      push_cast [hb]
      ring
    rw [hprod]
    exact mul_smul_id_eq_zero_of_distinguished T hT _ _ hleft hright

/-- **The single-truncation step.** For `Q` concentrated in degrees `≥ a` and `X` in degrees
`≤ b`, the product of scalars annihilating `H^j(Q)` for `a ≤ j ≤ b` annihilates every morphism
`X ⟶ Q`. -/
public theorem prod_smul_eq_zero_of_isLE_of_isGE {A : Type u} [CommRing A] (f : ℤ → A) (a b : ℤ)
    (Q : DerivedCategory (ModuleCat.{u} A)) [Q.IsGE a]
    (hQ : ∀ j : ℤ, j ≤ b →
      f j • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj Q) = 0)
    (X : DerivedCategory (ModuleCat.{u} A)) [X.IsLE b] (g : X ⟶ Q) :
    (∏ j ∈ Finset.range ((b - a).toNat + 1), f (a + j)) • g = 0 := by
  set T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj Q
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) (by omega) Q
  have h₁le : T.obj₁.IsLE b := by
    show ((DerivedCategory.TStructure.t.truncLE b).obj Q).IsLE b
    infer_instance
  have h₁ge : T.obj₁.IsGE a := by
    show ((DerivedCategory.TStructure.t.truncLE b).obj Q).IsGE a
    infer_instance
  have h₃ge : T.obj₃.IsGE (b + 1) := by
    show ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj Q).IsGE (b + 1)
    infer_instance
  obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ T hT g
    (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ b (b + 1) (by omega)
      inferInstance h₃ge)
  have hkill : (∏ j ∈ Finset.range ((b - a).toNat + 1), f (a + j)) • 𝟙 T.obj₁ = 0 := by
    by_cases hab : a ≤ b
    · have hle : T.obj₁.IsLE (a + ((b - a).toNat : ℤ)) := by
        refine DerivedCategory.TStructure.t.isLE_of_le T.obj₁ b (a + ((b - a).toNat : ℤ)) ?_
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      exact prod_smul_id_eq_zero_of_isGE_of_isLE f a (b - a).toNat T.obj₁
        (smul_id_homology_truncLE_eq_zero f b Q hQ)
    · exact (DerivedCategory.TStructure.t.isZero T.obj₁ b a (by omega)).eq_of_src _ _
  rw [hk]
  have hk0 : (∏ j ∈ Finset.range ((b - a).toNat + 1), f (a + j)) • k = 0 := by
    simpa only [Linear.comp_smul, Category.comp_id, comp_zero] using
      congrArg (fun q => k ≫ q) hkill
  calc
    (∏ j ∈ Finset.range ((b - a).toNat + 1), f (a + j)) • (k ≫ T.mor₁) =
        ((∏ j ∈ Finset.range ((b - a).toNat + 1), f (a + j)) • k) ≫ T.mor₁ := by
      rw [Linear.smul_comp]
    _ = 0 := by rw [hk0, zero_comp]

/-- **The shifted form of the single-truncation step.** For `P` concentrated in degrees `≤ d` and
`Q` in degrees `≥ a`, the product of scalars annihilating `H^j(Q)` for `a ≤ j ≤ s + d` annihilates
every morphism `P ⟶ Q⟦i⟧` with `i ≤ s`. -/
public theorem prod_smul_shiftedHom_eq_zero {A : Type u} [CommRing A] (f : ℤ → A) (a d s : ℤ)
    (P Q : DerivedCategory (ModuleCat.{u} A)) [P.IsLE d] [Q.IsGE a]
    (hQ : ∀ j : ℤ, j ≤ s + d →
      f j • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj Q) = 0)
    (i : ℤ) (hi : i ≤ s) (g : P ⟶ Q⟦i⟧) :
    (∏ j ∈ Finset.range ((s + d - a).toNat + 1), f (a + j)) • g = 0 := by
  set F := shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)
  have hPi : (F.obj P).IsLE (d + i) :=
    DerivedCategory.TStructure.t.isLE_shift P d (-i) (d + i) (by omega)
  have hPs : (F.obj P).IsLE (s + d) :=
    DerivedCategory.TStructure.t.isLE_of_le _ (d + i) (s + d) (by omega)
  have h := prod_smul_eq_zero_of_isLE_of_isGE f a (s + d) Q hQ (F.obj P)
    (F.map g ≫ (shiftShiftNeg Q i).hom)
  apply F.map_injective
  rw [Functor.map_smul, Functor.map_zero]
  apply (cancel_mono (shiftShiftNeg Q i).hom).mp
  simpa only [Linear.smul_comp, zero_comp] using h

/-- **The passage to the Hom complex.** If a scalar annihilates every morphism `K ⟶ L⟦i⟧` in the
derived category, it annihilates the degree-`i` homology of the Hom complex, for `L` K-injective.
-/
public theorem smul_id_homComplex_homology_eq_zero {A : Type u} [CommRing A] (r : A)
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) [L.IsKInjective] (i : ℤ)
    (h : ∀ g : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (L⟦i⟧), r • g = 0) :
    r • 𝟙 ((CochainComplex.HomComplexR A K L).homology i) = 0 := by
  set S := (CochainComplex.HomComplexR A K L).sc i
  apply smul_id_eq_zero_of_iso r S.moduleCatHomologyIso
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
    show r • (Submodule.Quotient.mk z :
      LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    set c : CochainComplex.HomComplex.Cocycle K L i :=
      CochainComplex.HomComplex.Cocycle.mk z.val (i + 1) rfl (by
        have hz := z.property
        change CochainComplex.HomComplex.δ i ((ComplexShape.up ℤ).next i) z.val = 0 at hz
        have hn : (ComplexShape.up ℤ).next i = i + 1 := by simp
        rwa [hn] at hz) with hc
    have hsmul : CochainComplex.HomComplex.Cocycle.equivHomShift.symm (r • c) =
        r • CochainComplex.HomComplex.Cocycle.equivHomShift.symm c := by
      ext n
      simp [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
        CochainComplex.HomComplex.Cocycle.homOf,
        CochainComplex.HomComplex.Cochain.rightShift_smul]
    have hQmap : DerivedCategory.Q.map
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (r • c)) = 0 := by
      rw [hsmul, Functor.map_smul]
      exact h _
    have hQh : DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{u} A)
        (.up ℤ)).map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (r • c))) = 0 := by
      have hn := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm (r • c))
      dsimp at hn
      rw [hQmap, comp_zero] at hn
      exact (cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app
        (L⟦i⟧))).mp (by simpa using hn)
    have hclass : CochainComplex.HomComplex.CohomologyClass.mk (r • c) = 0 := by
      apply CochainComplex.HomComplex.CohomologyClass.homAddEquiv.injective
      apply (CochainComplex.IsKInjective.Qh_map_bijective _ (L⟦i⟧)).1
      simpa only [map_zero,
        CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply,
        CochainComplex.HomComplex.CohomologyClass.toHom_mk, Functor.map_zero] using hQh
    have hclass' := (CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff _).mp hclass
    obtain ⟨y, hy⟩ := (CochainComplex.HomComplex.mem_coboundaries_iff
      (r • c) (i - 1) (by omega)).mp hclass'
    have hprev : (ComplexShape.up ℤ).prev i = i - 1 := by simp
    refine ⟨(CochainComplex.HomComplexR A K L).XIsoOfEq hprev.symm |>.hom <| y, ?_⟩
    apply Subtype.ext
    show (CochainComplex.HomComplexR A K L).d ((ComplexShape.up ℤ).prev i) i _ = _
    have hy' : (CochainComplex.HomComplexR A K L).d (i - 1) i y = r • z.val := hy
    show (((CochainComplex.HomComplexR A K L).XIsoOfEq hprev.symm).hom ≫
      (CochainComplex.HomComplexR A K L).d ((ComplexShape.up ℤ).prev i) i).hom y =
        r • z.val
    rw [HomologicalComplex.XIsoOfEq_hom_comp_d]
    exact hy'

/-- **The engine.** For `P` concentrated in degrees `≤ d` and `Q` in degrees `≥ a`, the product
of scalars annihilating `H^j(Q)` for `a ≤ j ≤ s + d` annihilates `H^i(RHom_A(P, Q))` for every
`i ≤ s`. -/
@[stacks 0EFH "the quantitative form of the truncation reduction, with the explicit product of \
per-degree annihilators"]
public theorem prod_smul_id_derivedHom_homology_eq_zero {A : Type u} [CommRing A] (f : ℤ → A)
    (a d s : ℤ) (P Q : DerivedCategory (ModuleCat.{u} A)) [P.IsLE d] [Q.IsGE a]
    (hQ : ∀ j : ℤ, j ≤ s + d →
      f j • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj Q) = 0)
    (i : ℤ) (hi : i ≤ s) :
    (∏ j ∈ Finset.range ((s + d - a).toNat + 1), f (a + j)) • 𝟙
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op P, Q))) = 0 := by
  set K := DerivedCategory.Q.objPreimage P
  set eK := DerivedCategory.Q.objObjPreimageIso P
  obtain ⟨L, q, hq, hL⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage Q)
  let := hq
  let := hL
  set eL : DerivedCategory.Q.obj L ≅ Q :=
    (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Q
  set D := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  set e := D.hom.mapIso (Iso.prod eK.op eL.symm) ≪≫ D.homIso K L
  refine smul_id_eq_zero_of_iso _
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app
        (CochainComplex.HomComplexR A K L)) ?_
  refine smul_id_homComplex_homology_eq_zero _ K L i fun g => ?_
  set ei : DerivedCategory.Q.obj (L⟦i⟧) ≅ Q⟦i⟧ :=
    (DerivedCategory.Q.commShiftIso i).app L ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) i).mapIso eL
  have h := prod_smul_shiftedHom_eq_zero f a d s P Q hQ i hi (eK.inv ≫ g ≫ ei.hom)
  apply (cancel_epi eK.inv).mp
  apply (cancel_mono ei.hom).mp
  simpa only [Linear.comp_smul, Linear.smul_comp, Category.assoc, comp_zero, zero_comp] using h

/-- **Stacks 0EFH, the homological reduction.** Let `P` have cohomology concentrated in degrees
`≤ d` and `Q` in degrees `≥ a`. If for each `j ≤ s + d` some element outside a prime `p`
annihilates `H^j(Q)`, then one element outside `p` annihilates `H^i(RHom_A(P, Q))` for all
`i ≤ s`. -/
@[stacks 0EFH "the homological-algebra reduction: after the two identifications of the first \
paragraph, the canonical-truncation argument producing an element outside `p` annihilating \
`H^i(RHom(P, Q))` for `i ≤ s`"]
public theorem exists_notMem_mem_annihilator_homology_derivedHom {A : Type u} [CommRing A]
    (p : PrimeSpectrum A) (a d s : ℤ) (P Q : DerivedCategory (ModuleCat.{u} A)) [Q.IsGE a]
    (hP : ∀ i : ℤ, d < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj P))
    (hQ : ∀ j : ℤ, j ≤ s + d → ∃ f : A, f ∉ p.asIdeal ∧
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj Q)) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      g ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
            (Opposite.op P, Q))) := by
  classical
  have hPle : P.IsLE d := (DerivedCategory.isLE_iff P d).mpr hP
  have hex : ∀ j : ℤ, ∃ f : A, f ∉ p.asIdeal ∧ (j ≤ s + d →
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj Q)) := by
    intro j
    by_cases hj : j ≤ s + d
    · obtain ⟨f, hfp, hfa⟩ := hQ j hj
      exact ⟨f, hfp, fun _ => hfa⟩
    · exact ⟨1, p.isPrime.one_notMem, fun h => absurd h hj⟩
  set f : ℤ → A := fun j => (hex j).choose
  have hfp : ∀ j : ℤ, f j ∉ p.asIdeal := fun j => (hex j).choose_spec.1
  have hfann : ∀ j : ℤ, j ≤ s + d →
      f j • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj Q) = 0 :=
    fun j hj => (smul_id_eq_zero_iff_mem_annihilator _ _).mpr ((hex j).choose_spec.2 hj)
  exact ⟨∏ j ∈ Finset.range ((s + d - a).toNat + 1), f (a + j),
    Submonoid.prod_mem p.asIdeal.primeCompl fun j _ => hfp (a + j),
    fun i hi => (smul_id_eq_zero_iff_mem_annihilator _ _).mp
      (prod_smul_id_derivedHom_homology_eq_zero f a d s P Q hfann i hi)⟩

end Stacks.Algebraization

end
