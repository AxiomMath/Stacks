module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of strictly perfect complexes

Let `C` be a preadditive monoidal category with finite biproducts and a zero object, whose tensor
product is additive in each variable. A finite free object of rank `n` is the biproduct of `n`
copies of the unit `𝟙_ C`, and a cochain complex `K` over `C` indexed by `ℤ` is strictly perfect
if `K.X i` is a zero object for all but finitely many `i` and every `K.X i` is a retract of a
finite free object. If `E` and `F` are strictly perfect, then so is the total complex
`HomologicalComplex.tensorObj E F`, whose degree `n` term is the coproduct of the
`E.X p ⊗ F.X q` over `p + q = n`.

## Main definitions

* `finFree`: the finite free object `⨁_{Fin n} 𝟙_ C` of rank `n`.
* `IsFiniteFreeSummand`: the property of being a retract of some `finFree C n`.
* `StrictlyPerfect`: a bounded cochain complex whose terms are retracts of finite free objects.
* `tensorObj_X_iso_biproduct`: for `E` vanishing outside `[aE, bE]`, the degree `j` term of
  `HomologicalComplex.tensorObj E F` is isomorphic to `⨁_{p ∈ [aE, bE]} E.X p ⊗ F.X (j - p)`.

## Main results

* `IsFiniteFreeSummand.biproduct`: a finite biproduct of retracts of finite free objects is a
  retract of a finite free object.
* `IsFiniteFreeSummand.tensor`: the tensor product of two retracts of finite free objects is a
  retract of a finite free object.
* `strictlyPerfect_tensorObj`: the total complex of the tensor product of two strictly perfect
  complexes is strictly perfect.

## Implementation notes

The source works with `𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, with tensor product `⊗_{𝒪_X}`
and unit `𝒪_X`. Strict perfectness and the statement only involve this monoidal structure and
finite direct sums, so they are formulated here over an abstract category `C` as above. Direct
summands of finite free modules are modelled as categorical `Retract`s, and the total complex
`Tot(E ⊗ F)` is `HomologicalComplex.tensorObj`. Cochain complexes are `CochainComplex C ℤ`, with
differentials raising degree by one.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 09J2](https://stacks.math.columbia.edu/tag/09J2)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [HasFiniteBiproducts C] [HasZeroObject C]

/-- The finite free object of rank `n`: the biproduct of `n` copies of the unit object `𝟙_ C`. -/
noncomputable def finFree (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    [HasFiniteBiproducts C] (n : ℕ) : C :=
  ⨁ fun _ : Fin n => (𝟙_ C)

/-- An object `M` is a *direct summand of a finite free object* if it is a retract of
`finFree C n` for some `n`, i.e. there are maps `i : M ⟶ finFree C n` and `r : finFree C n ⟶ M`
with `i ≫ r = 𝟙 M`. This is condition (2) of Stacks Definition 20.46.1 (Tag `08C4`). -/
def IsFiniteFreeSummand (M : C) : Prop :=
  ∃ n : ℕ, Nonempty (Retract M (finFree C n))

/-! ## Closure properties of finite free summands -/

-- The additive-functor instances needed by the helpers below live in a `section`, so that they
-- leave scope before `structure StrictlyPerfect`; the main theorem re-introduces them through its
-- own `variable` block, which avoids duplicate instance arguments on the theorem.
section Helpers
variable [(MonoidalCategory.curriedTensor C).Additive]
  [∀ X₁ : C, ((MonoidalCategory.curriedTensor C).obj X₁).Additive]

omit [HasZeroObject C] [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj
    X₁).Additive] in
/-- An object isomorphic to a finite free summand is a finite free summand. -/
theorem IsFiniteFreeSummand.ofIso {M N : C} (e : M ≅ N) (h : IsFiniteFreeSummand N) :
    IsFiniteFreeSummand M :=
  h.imp fun _ ⟨ret⟩ => ⟨(Retract.ofIso e).trans ret⟩

omit [HasZeroObject C] [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj
    X₁).Additive] in
/-- The finite free object of rank `0` is a zero object. -/
theorem isZero_finFree_zero : IsZero (finFree C 0) := by
  rw [finFree, IsZero.iff_id_eq_zero]
  ext (i : Fin 0)
  exact i.elim0

omit [HasZeroObject C] [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj
    X₁).Additive] in
/-- A zero object is a finite free summand. -/
theorem IsFiniteFreeSummand.of_isZero {M : C} (h : IsZero M) : IsFiniteFreeSummand M :=
  ⟨0, ⟨⟨h.to_ _, (isZero_finFree_zero (C := C)).to_ _, h.eq_of_src _ _⟩⟩⟩

/-- If each `M b` is a retract of `N b`, then `⨁ M` is a retract of `⨁ N`, via the biproduct
maps of the sections and retractions. -/
noncomputable def Retract.biproductRetract {β : Type} [Finite β] {M N : β → C}
    (r : ∀ b, Retract (M b) (N b)) : Retract (⨁ M) (⨁ N) where
  i := Limits.biproduct.map (fun b => (r b).i)
  r := Limits.biproduct.map (fun b => (r b).r)
  retract := by
    ext b
    simp [Retract.retract]

omit [HasZeroObject C] [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj
    X₁).Additive] in
/-- A finite biproduct of finite free objects is a finite free summand. -/
theorem isFiniteFreeSummand_biproduct_finFree {β : Type} [Finite β] (n : β → ℕ) :
    IsFiniteFreeSummand (⨁ fun b => finFree C (n b)) := by
  have := Fintype.ofFinite β
  exact ⟨_, ⟨Retract.ofIso (Limits.biproduct.mapIso (fun _ => Iso.refl _) ≪≫
    Limits.biproductBiproductIso (fun b => Fin (n b)) (fun _ _ => 𝟙_ C) ≪≫
    (Limits.biproduct.reindex (Fintype.equivFin _).symm (fun _ => 𝟙_ C)).symm)⟩⟩

omit [HasZeroObject C] [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj
    X₁).Additive] in
/-- A finite biproduct of finite free summands is a finite free summand. -/
theorem IsFiniteFreeSummand.biproduct {β : Type} [Finite β] {M : β → C}
    (h : ∀ b, IsFiniteFreeSummand (M b)) : IsFiniteFreeSummand (⨁ M) := by
  choose n ret using h
  obtain ⟨N, ⟨ret2⟩⟩ := isFiniteFreeSummand_biproduct_finFree (C := C) n
  exact ⟨N, ⟨(Retract.biproductRetract fun b => (ret b).some).trans ret2⟩⟩

/-- The isomorphism `M ⊗ finFree C m ≅ ⨁_{Fin m} M`, given by distributing `M ⊗ -` over the
biproduct and applying the right unitor in each summand. -/
noncomputable def tensorFinFreeIso (M : C) (m : ℕ) :
    (M ⊗ finFree C m) ≅ ⨁ fun _ : Fin m => M :=
  ((curriedTensor C).obj M).mapBiproduct (fun _ : Fin m => 𝟙_ C) ≪≫
    Limits.biproduct.mapIso fun _ => ρ_ M

omit [HasZeroObject C] [(curriedTensor C).Additive] in
/-- The tensor product of two finite free summands is a finite free summand. -/
theorem IsFiniteFreeSummand.tensor {M N : C}
    (hM : IsFiniteFreeSummand M) (hN : IsFiniteFreeSummand N) :
    IsFiniteFreeSummand (M ⊗ N) := by
  obtain ⟨m, ⟨retN⟩⟩ := hN
  obtain ⟨N', ⟨ret'⟩⟩ := IsFiniteFreeSummand.ofIso (tensorFinFreeIso M m)
    (IsFiniteFreeSummand.biproduct fun _ => hM)
  exact ⟨N', ⟨(retN.map ((curriedTensor C).obj M)).trans ret'⟩⟩

/-! ## Tensoring with a zero object -/

omit [HasFiniteBiproducts C] [HasZeroObject C] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive] in
/-- If `M` is a zero object, then `M ⊗ N` is a zero object. -/
theorem isZero_tensor_of_isZero_left {M N : C} (hM : IsZero M) : IsZero (M ⊗ N) :=
  Functor.map_isZero ((curriedTensor C).flip.obj N) hM

omit [HasFiniteBiproducts C] [HasZeroObject C] [(curriedTensor C).Additive] in
/-- If `N` is a zero object, then `M ⊗ N` is a zero object. -/
theorem isZero_tensor_of_isZero_right {M N : C} (hN : IsZero N) : IsZero (M ⊗ N) :=
  Functor.map_isZero ((curriedTensor C).obj M) hN

/-! ## The terms of the total complex as finite biproducts

The degree `j` term of `HomologicalComplex.tensorObj E F` is the coproduct of the
`E.X p ⊗ F.X q` over the infinite fibre `{(p, q) | p + q = j}`. When `E.X p` is a zero object for
`p ∉ [aE, bE]`, all summands with `p ∉ [aE, bE]` are zero objects, and this coproduct is
isomorphic to the finite biproduct `⨁_{p ∈ [aE, bE]} E.X p ⊗ F.X (j - p)`. -/

/-- The degree-`j` term of `Tot(E ⊗ F)` is isomorphic to the finite biproduct of the
summands `E^p ⊗ F^{j-p}` for `p` in the bounding range `[aE, bE]` of `E`.

Here `aE bE : ℤ` are bounds with `E.X p` a zero object for `p < aE ∨ bE < p`; the
biproduct is taken over the finite index `↑(Finset.Icc aE bE)`. -/
noncomputable def tensorObj_X_iso_biproduct
    (E F : CochainComplex C ℤ) [E.HasTensor F]
    (aE bE : ℤ) (hE0 : ∀ p : ℤ, p < aE ∨ bE < p → IsZero (E.X p)) (j : ℤ) :
    (HomologicalComplex.tensorObj E F).X j ≅
      ⨁ (fun p : (Finset.Icc aE bE) => E.X (p : ℤ) ⊗ F.X (j - (p : ℤ))) := by
  set X : GradedObject (ℤ × ℤ) C :=
    ((((MonoidalCategory.curriedTensor C).mapBifunctorHomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ)).obj E).obj F).toGradedObject
  set q' : ℤ × ℤ → ℤ := (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  set g : (Finset.Icc aE bE) → C := fun q => E.X (q : ℤ) ⊗ F.X (j - (q : ℤ))
  have hmemfib : ∀ q : ℤ, q' (q, j - q) = j := fun q => show q + (j - q) = j by omega
  let ι2 : ∀ i : ↑(q' ⁻¹' {j}), X i.1 ⟶ ⨁ g := fun i => by
    obtain ⟨⟨a, b⟩, hab⟩ := i
    by_cases hmem : a ∈ Finset.Icc aE bE
    · refine (eqToHom ?_) ≫ biproduct.ι g ⟨a, hmem⟩
      change E.X a ⊗ F.X b = E.X a ⊗ F.X (j - a)
      have : a + b = j := hab
      rw [show b = j - a by omega]
    · exact 0
  let s2 : X.CofanMapObjFun q' j := GradedObject.CofanMapObjFun.mk X q' j (⨁ g)
    (fun i hi => ι2 ⟨i, hi⟩)
  have hinj : ∀ i : ↑(q' ⁻¹' {j}), s2.inj i = ι2 i := fun i => rfl
  have hzero : ∀ (a b : ℤ), a ∉ Finset.Icc aE bE → IsZero (X (a, b)) := by
    intro a b hmem
    simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
    exact isZero_tensor_of_isZero_left (hE0 a (by omega))
  have hcol2 : IsColimit s2 := by
    refine Cofan.IsColimit.mk s2
      (fun t => biproduct.desc (fun q => t.inj ⟨(q.1, j - q.1), hmemfib q.1⟩)) ?_ ?_
    · rintro t ⟨⟨a, b⟩, hab⟩
      have hsum : a + b = j := hab
      change ι2 ⟨(a,b), hab⟩ ≫ _ = t.inj ⟨(a,b), hab⟩
      by_cases hmem : a ∈ Finset.Icc aE bE
      · obtain rfl : b = j - a := by omega
        simp only [ι2]
        rw [dite_eq_left hmem, Category.assoc, biproduct.ι_desc]
        simp
      · simp only [ι2]
        rw [dite_eq_right hmem, zero_comp]
        exact (hzero a b hmem).eq_of_src _ _
    · intro t m hm
      refine biproduct.hom_ext' _ _ fun q => ?_
      rw [biproduct.ι_desc]
      have hkey := hm ⟨(q.1, j - q.1), hmemfib q.1⟩
      rw [hinj] at hkey
      simp only [ι2] at hkey
      rw [dite_eq_left q.2] at hkey
      simpa using hkey
  exact (X.isColimitCofanMapObj q' j).coconePointUniqueUpToIso hcol2

end Helpers

/-- Stacks Definition 20.46.1 (Tag `08C4`): a cochain complex `K` is *strictly perfect* if

1. `K.X i` is a zero object for all but finitely many `i`, i.e. there are `a b : ℤ` such that
   `K.X i` is a zero object whenever `i < a` or `b < i`; and
2. each term `K.X i` is a direct summand of a finite free object. -/
@[sga "6 I 2.1" "special case"]
structure StrictlyPerfect (K : CochainComplex C ℤ) : Prop where
  /-- The complex is bounded: its terms vanish outside a finite range of degrees. -/
  bounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)
  /-- Each term is a direct summand of a finite free object. -/
  summand : ∀ i : ℤ, IsFiniteFreeSummand (K.X i)

variable [(MonoidalCategory.curriedTensor C).Additive]
  [∀ X₁ : C, ((MonoidalCategory.curriedTensor C).obj X₁).Additive]

omit [HasZeroObject C] in
/-- **Stacks Tag 09J2 (Lemma 20.46.3).** If `E` and `F` are strictly perfect complexes, then the
total complex `HomologicalComplex.tensorObj E F` of their tensor product, whose degree `n` term is
`⨁_{p+q=n} E^p ⊗ F^q` with the Koszul-sign differential, is strictly perfect.

The hypothesis `[E.HasTensor F]` asserts that the total complex exists; for bounded complexes
(such as strictly perfect ones) it is automatically satisfied since each total degree only
involves finitely many summands. -/
@[stacks 09J2]
theorem strictlyPerfect_tensorObj
    (E F : CochainComplex C ℤ) [E.HasTensor F]
    (hE : StrictlyPerfect E) (hF : StrictlyPerfect F) :
    StrictlyPerfect (HomologicalComplex.tensorObj E F) := by
  obtain ⟨aE, bE, hE0⟩ := hE.bounded
  obtain ⟨aF, bF, hF0⟩ := hF.bounded
  refine ⟨⟨aE + aF, bE + bF, fun j hj => ?_⟩, fun j => IsFiniteFreeSummand.ofIso
    (tensorObj_X_iso_biproduct E F aE bE hE0 j)
    (IsFiniteFreeSummand.biproduct fun _ => .tensor (hE.summand _) (hF.summand _))⟩
  refine IsZero.of_iso ?_ (tensorObj_X_iso_biproduct E F aE bE hE0 j)
  rw [IsZero.iff_id_eq_zero]
  refine biproduct.hom_ext' _ _ fun p => ?_
  have := Finset.mem_Icc.mp p.2
  exact (isZero_tensor_of_isZero_right (hF0 (j - p) (by omega))).eq_of_src _ _
