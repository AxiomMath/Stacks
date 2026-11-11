module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensor
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth formula over a field

Let `k` be a field and let `X` and `Y` be schemes over `k` carrying quasi-coherent modules `F`
and `G`. The cohomology of the external tensor product `pr₁^*F ⊗ pr₂^*G` on `X ×_k Y` is the
direct sum of the products `Hᵖ(X, F) ⊗_k Hᑫ(Y, G)` over the pairs with `p + q = n`.

## Main results

* `CochainComplex.Kunneth.kFlat_of_field`: every cochain complex of vector spaces over a field
  is K-flat.
* `CochainComplex.Kunneth.nonempty_derivedTensorHomologyIso`: the Künneth isomorphism for the
  derived tensor product of two complexes of vector spaces.
* `AlgebraicGeometry.nonempty_kunnethIso`: the Künneth isomorphism for sheaf cohomology, from a
  datum `AlgebraicGeometry.KunnethDerivedData`. The canonical Künneth isomorphism of
  [Stacks, Tag 0BEF] itself is `AlgebraicGeometry.KunnethQcqs.isIso_kunnethMap`.

## Implementation notes

Schemes over `k` are represented by explicit structure morphisms to `Spec k`, and the
cohomology of a module on such a scheme is the `k`-module `AlgebraicGeometry.cohomologyOverField`.
Because every complex of vector spaces is K-flat, the Künneth isomorphism for the derived tensor
product needs no boundedness hypothesis; the comparison of the cohomology of `X ×_k Y` with the
derived tensor product of the cohomologies of the factors is the content of Tag 0FLQ and enters
as `AlgebraicGeometry.KunnethDerivedData`.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped DirectSum TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CochainComplex.Kunneth

/-- **Every cochain complex of vector spaces over a field is K-flat.** Each truncation is a
bounded above complex of flat modules, and K-flatness passes to the filtered colimit. -/
theorem kFlat_of_field {k : Type u} [Field k] (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    C.KFlat := by
  have h : (colimit (CochainComplex.KFlat.truncLESequence C)).KFlat :=
    CochainComplex.KFlat.kFlat_colimit (CochainComplex.KFlat.truncLESequence C) (fun n ↦
      CochainComplex.KFlat.kFlat_of_flat (C.truncLE (n : ℤ)) n)
  let e := (colimit.isColimit (CochainComplex.KFlat.truncLESequence C)).coconePointUniqueUpToIso
    (CochainComplex.KFlat.truncLECocone_isColimit C)
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso
    ((MonoidalCategory.tensorLeft M).mapIso e) (h M hM)

/-- Over a field a complex receives a quasi-isomorphism from the complex of its own cohomology
modules, taken with zero differentials. -/
private lemma exists_zeroDifferential_quasiIso {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    ∃ (E : CochainComplex (ModuleCat.{u} k) ℤ) (f : E ⟶ C),
      (∀ i j, E.d i j = 0) ∧ QuasiIso f := by
  classical
  have hproj : ∀ i : ℤ, Projective (C.homology i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis k (C.homology i))
  let E : CochainComplex (ModuleCat.{u} k) ℤ :=
    { X := fun i => C.homology i
      d := fun _ _ => 0
      shape := by intros; rfl
      d_comp_d' := by intros; simp }
  let s (i : ℤ) := Projective.factorThru (𝟙 (C.homology i)) (C.homologyπ i)
  have hs (i : ℤ) : s i ≫ C.homologyπ i = 𝟙 _ := Projective.factorThru_comp _ _
  let f : E ⟶ C :=
    { f := fun i => s i ≫ C.iCycles i
      comm' := by intros; dsimp [E]; simp }
  refine ⟨E, f, fun _ _ => rfl, ?_⟩
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hi : IsIso (E.iCycles i) := E.isIso_iCycles _ _ rfl rfl
  have hp : IsIso (E.homologyπ i) := E.isIso_homologyπ _ _ rfl rfl
  have hc : HomologicalComplex.cyclesMap f i = E.iCycles i ≫ s i := by
    apply (cancel_mono (C.iCycles i)).1
    simp [HomologicalComplex.cyclesMap_i, f]
  have he : E.homologyπ i ≫ HomologicalComplex.homologyMap f i = E.iCycles i := by
    rw [HomologicalComplex.homologyπ_naturality, hc, Category.assoc, hs, Category.comp_id]
  have : IsIso (E.homologyπ i ≫ HomologicalComplex.homologyMap f i) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (E.homologyπ i) _

/-- Over a field every complex is isomorphic in the derived category to a complex with zero
differentials. -/
private lemma exists_zeroDifferential_derivedIso {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{u} k) ℤ) :
    ∃ E : CochainComplex (ModuleCat.{u} k) ℤ, (∀ i j, E.d i j = 0) ∧
      Nonempty (DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj C) := by
  obtain ⟨E, f, hzero, hf⟩ := exists_zeroDifferential_quasiIso C
  have _ : QuasiIso f := hf
  exact ⟨E, hzero, ⟨asIso (DerivedCategory.Q.map f)⟩⟩

/-- A complex isomorphic in the derived category to `K` has cohomology isomorphic to that of `K`
in each degree. -/
private lemma nonempty_homologyIso_of_derivedIso {k : Type u} [Field k]
    {C : CochainComplex (ModuleCat.{u} k) ℤ} {K : DerivedCategory (ModuleCat.{u} k)}
    (e : DerivedCategory.Q.obj C ≅ K) (i : ℤ) :
    Nonempty (C.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj K) :=
  ⟨((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) i).app C).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).mapIso e⟩

/-- A complex with zero differentials is its own cohomology in each degree. -/
private lemma zeroDifferential_homologyIso {C : Type*} [Category* C] [Abelian C]
    (E : CochainComplex C ℤ) (hzero : ∀ i j, E.d i j = 0) (i : ℤ) :
    Nonempty (E.X i ≅ E.homology i) := by
  have _ : IsIso (E.iCycles i) := E.isIso_iCycles i (i + 1) (by simp) (hzero i (i + 1))
  have _ : IsIso (E.homologyπ i) := E.isIso_homologyπ (i - 1) i (by simp) (hzero (i - 1) i)
  exact ⟨(asIso (E.iCycles i)).symm ≪≫ asIso (E.homologyπ i)⟩

/-- A family of isomorphisms induces an isomorphism of the direct sums of the termwise tensor
products. -/
lemma nonempty_directSumTensorIso_of_familyIso {k : Type u} [Field k]
    {ι : Type v} (A A' B B' : ι → ModuleCat.{u} k)
    (hA : ∀ i, Nonempty (A i ≅ A' i)) (hB : ∀ i, Nonempty (B i ≅ B' i)) :
    Nonempty (ModuleCat.of k (⨁ i, TensorProduct k (A i) (B i)) ≅
      ModuleCat.of k (⨁ i, TensorProduct k (A' i) (B' i))) := by
  classical
  let e : ∀ i, TensorProduct k (A i) (B i) ≃ₗ[k] TensorProduct k (A' i) (B' i) := fun i =>
    TensorProduct.congr (Classical.choice (hA i)).toLinearEquiv
      (Classical.choice (hB i)).toLinearEquiv
  exact ⟨(DirectSum.congrLinearEquiv e).toModuleIso⟩

/-- The tensor product of two complexes with zero differentials has zero differentials. -/
private lemma tensorComplex_zeroDifferentials {k : Type u} [Field k]
    (C D : CochainComplex (ModuleCat.{u} k) ℤ)
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) :
    ∀ i j, (HomologicalComplex.tensorObj C D).d i j = 0 := by
  intro i j
  change (HomologicalComplex.mapBifunctor C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).d i j = 0
  rw [HomologicalComplex.mapBifunctor.d_eq]
  have h₁ : HomologicalComplex.mapBifunctor.D₁ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i j = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b _
    rw [HomologicalComplex.mapBifunctor.ι_D₁]
    by_cases ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (a + 1, b) = j
    · rw [HomologicalComplex.mapBifunctor.d₁_eq C D _ _
        (ComplexShape.up_mk a (a + 1) (by simp)) b j ht]
      simp [hC]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero' C D _ _
        (ComplexShape.up_mk a (a + 1) (by simp)) b j ht]
      simp
  have h₂ : HomologicalComplex.mapBifunctor.D₂ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) i j = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b _
    rw [HomologicalComplex.mapBifunctor.ι_D₂]
    by_cases ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (a, b + 1) = j
    · rw [HomologicalComplex.mapBifunctor.d₂_eq C D _ _ a
        (ComplexShape.up_mk b (b + 1) (by simp)) j ht]
      simp [hD]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' C D _ _ a
        (ComplexShape.up_mk b (b + 1) (by simp)) j ht]
      simp
  rw [h₁, h₂, zero_add]

/-- The degree `n` term of a tensor product of complexes is the direct sum of the tensor
products of the terms in complementary degrees. -/
private def tensorComplexXIsoDirectSum {k : Type u} [Field k]
    (C D : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ) :
    (HomologicalComplex.tensorObj C D).X n ≅
      ModuleCat.of k
        (⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
          TensorProduct k (C.X pq.1.1) (D.X pq.1.2)) := by
  change (∐ fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} =>
    ModuleCat.of k (TensorProduct k (C.X pq.1.1) (D.X pq.1.2))) ≅ _
  exact ModuleCat.coprodIsoDirectSum _

/-- For complexes with zero differentials the cohomology of the tensor product is the direct sum
of the tensor products of the cohomologies in complementary degrees. -/
private lemma nonempty_tensorComplexHomologyDirectSumIso {k : Type u} [Field k]
    (C D : CochainComplex (ModuleCat.{u} k) ℤ)
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) (n : ℤ) :
    Nonempty
      ((HomologicalComplex.tensorObj C D).homology n ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
            TensorProduct k (C.homology pq.1.1) (D.homology pq.1.2))) := by
  obtain ⟨eH⟩ := zeroDifferential_homologyIso (HomologicalComplex.tensorObj C D)
    (tensorComplex_zeroDifferentials C D hC hD) n
  obtain ⟨eS⟩ := nonempty_directSumTensorIso_of_familyIso
    (ι := {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (fun pq => C.X pq.1.1) (fun pq => C.homology pq.1.1)
    (fun pq => D.X pq.1.2) (fun pq => D.homology pq.1.2)
    (fun pq => zeroDifferential_homologyIso C hC pq.1.1)
    (fun pq => zeroDifferential_homologyIso D hD pq.1.2)
  exact ⟨eH.symm ≪≫ tensorComplexXIsoDirectSum C D n ≪≫ eS⟩

/-- Restricting a direct sum along an injection whose complement indexes only zero summands is
an isomorphism. -/
private def directSumComapEquiv
    {R : Type*} [Semiring R] {ι κ : Type*} (e : ι → κ) (he : Function.Injective e)
    (M : κ → Type*) [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (hzero : ∀ j, j ∉ Set.range e → Subsingleton (M j)) :
    (⨁ j, M j) ≃ₗ[R] ⨁ i, M (e i) := by
  classical
  let f : (⨁ j, M j) →ₗ[R] ⨁ i, M (e i) :=
    { toFun := DFinsupp.comapDomain e he
      map_add' := DFinsupp.comapDomain_add e he
      map_smul' := DFinsupp.comapDomain_smul e he }
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    ext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun z => z i) h
    · exact (hzero j hj).elim _ _
  · intro y
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, f.map_zero⟩
    | of i x => exact ⟨DirectSum.lof R κ M (e i) x, DFinsupp.comapDomain_single e he i x⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', f.map_add x' y'⟩

/-- For families vanishing in negative degrees the sum over pairs of integers with a given
nonnegative sum is the sum over pairs of natural numbers with that sum. -/
private def directSumTensorIntIsoNat
    {k : Type u} [Field k] (A B : ℤ → ModuleCat.{u} k)
    (hA : ∀ i, i < 0 → IsZero (A i)) (hB : ∀ i, i < 0 → IsZero (B i)) (n : ℕ) :
    ModuleCat.of k (⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = (n : ℤ)},
      TensorProduct k (A pq.1.1) (B pq.1.2)) ≅
    ModuleCat.of k (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      TensorProduct k (A (pq.1.1 : ℤ)) (B (pq.1.2 : ℤ))) := by
  let e : {pq : ℕ × ℕ // pq.1 + pq.2 = n} → {pq : ℤ × ℤ // pq.1 + pq.2 = (n : ℤ)} :=
    fun pq => ⟨(pq.1.1, pq.1.2), by simp only [← Nat.cast_add, pq.2]⟩
  have he : Function.Injective e := by
    intro i j h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    dsimp [e] at h'
    exact Prod.ext (Int.ofNat_inj.mp (congrArg Prod.fst h'))
      (Int.ofNat_inj.mp (congrArg Prod.snd h'))
  apply LinearEquiv.toModuleIso (directSumComapEquiv e he
    (fun pq => TensorProduct k (A pq.1.1) (B pq.1.2)) ?_)
  intro pq hpq
  have hneg : pq.1.1 < 0 ∨ pq.1.2 < 0 := by
    by_contra! h
    apply hpq
    refine ⟨⟨(pq.1.1.toNat, pq.1.2.toNat), ?_⟩, ?_⟩
    · have := pq.2
      omega
    · apply Subtype.ext
      dsimp [e]
      exact Prod.ext (Int.toNat_of_nonneg h.1) (Int.toNat_of_nonneg h.2)
  rcases hneg with h | h
  · have : Subsingleton (A pq.1.1) := ModuleCat.isZero_iff_subsingleton.mp (hA _ h)
    infer_instance
  · have : Subsingleton (B pq.1.2) := ModuleCat.isZero_iff_subsingleton.mp (hB _ h)
    infer_instance

/-- **The Künneth formula over a field.** The cohomology of the derived tensor product of two
complexes of vector spaces is the direct sum of the tensor products of their cohomologies in
complementary degrees. -/
theorem nonempty_derivedTensorHomologyIso {k : Type u} [Field k]
    (K L : DerivedCategory (ModuleCat.{u} k)) (n : ℤ) :
    Nonempty
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor k).obj K).obj L) ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
            TensorProduct k
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) pq.1.1).obj K)
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) pq.1.2).obj L))) := by
  let C' := DerivedCategory.Q.objPreimage K
  let D' := DerivedCategory.Q.objPreimage L
  obtain ⟨C, hc, ⟨ec⟩⟩ := exists_zeroDifferential_derivedIso C'
  obtain ⟨D, hd, ⟨ed⟩⟩ := exists_zeroDifferential_derivedIso D'
  let ek := ec ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let el := ed ≪≫ DerivedCategory.Q.objObjPreimageIso L
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct k
  let e := (T.tensor.mapIso ek).app (DerivedCategory.Q.obj D) ≪≫
    (T.tensor.obj K).mapIso el
  obtain ⟨eH⟩ := nonempty_tensorComplexHomologyDirectSumIso C D hc hd n
  obtain ⟨eS⟩ := nonempty_directSumTensorIso_of_familyIso
    (fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} => C.homology pq.1.1)
    (fun pq => (DerivedCategory.homologyFunctor (ModuleCat.{u} k) pq.1.1).obj K)
    (fun pq => D.homology pq.1.2)
    (fun pq => (DerivedCategory.homologyFunctor (ModuleCat.{u} k) pq.1.2).obj L)
    (fun pq => nonempty_homologyIso_of_derivedIso ek pq.1.1)
    (fun pq => nonempty_homologyIso_of_derivedIso el pq.1.2)
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).mapIso
      (e.symm ≪≫ T.comparison C D (kFlat_of_field C) (kFlat_of_field D)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).app _ ≪≫ eH ≪≫ eS⟩

/-- **The Künneth formula over a field in nonnegative degrees.** For complexes with vanishing
cohomology in negative degrees the sum runs over pairs of natural numbers. -/
theorem nonempty_derivedTensorHomologyNatIso {k : Type u} [Field k]
    (K L : DerivedCategory (ModuleCat.{u} k))
    (hK : ∀ i, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hL : ∀ i, i < 0 → IsZero ((DerivedCategory.homologyFunctor _ i).obj L)) (n : ℕ) :
    Nonempty
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor k).obj K).obj L) ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct k
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (pq.1.1 : ℤ)).obj K)
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (pq.1.2 : ℤ)).obj L))) := by
  obtain ⟨e⟩ := nonempty_derivedTensorHomologyIso K L (n : ℤ)
  exact ⟨e ≪≫ directSumTensorIntIsoNat
    (fun i => (DerivedCategory.homologyFunctor _ i).obj K)
    (fun i => (DerivedCategory.homologyFunctor _ i).obj L) hK hL n⟩

end CochainComplex.Kunneth

namespace AlgebraicGeometry

open Opposite TopologicalSpace

/-- The external tensor product `pr₁^*F ⊗ pr₂^*G` of two modules on the factors of the fibre
product `X ×_k Y`. -/
@[ega "I 9.1.2" "special case", ega "II 4.3.1" "partial"]
def externalTensorSheaf {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (g : Y ⟶ Spec (.of k)) (F : X.Modules) (G : Y.Modules) : (pullback f g).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor ((pullback f g).sheaf)).obj ((Scheme.Modules.pullback
    (pullback.fst f g)).obj F)).obj ((Scheme.Modules.pullback (pullback.snd f g)).obj G)

/-- Complexes of `k`-vector spaces computing `RΓ(X, F)` and `RΓ(Y, G)` whose derived tensor
product computes `RΓ(X ×_k Y, pr₁^*F ⊗ pr₂^*G)`. -/
structure KunnethDerivedData (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (F : X.Modules) (G : Y.Modules) where
  /-- The object of the derived category of `k` computing the cohomology of `F` on `X`. -/
  left : DerivedCategory (ModuleCat.{u} k)
  /-- The object of the derived category of `k` computing the cohomology of `G` on `Y`. -/
  right : DerivedCategory (ModuleCat.{u} k)
  /-- The cohomology of `left` vanishes in negative degrees. -/
  isZero_left : ∀ i : ℤ, i < 0 →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj left)
  /-- The cohomology of `right` vanishes in negative degrees. -/
  isZero_right : ∀ i : ℤ, i < 0 →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj right)
  /-- In degree `p` the cohomology of `left` is `Hᵖ(X, F)`. -/
  homologyIso_left : ∀ p : ℕ,
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).obj left ≅
      cohomologyOverField k f F p)
  /-- In degree `q` the cohomology of `right` is `Hᑫ(Y, G)`. -/
  homologyIso_right : ∀ q : ℕ,
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (q : ℤ)).obj right ≅
      cohomologyOverField k g G q)
  /-- In degree `n` the cohomology of the derived tensor product is
  `Hⁿ(X ×_k Y, pr₁^*F ⊗ pr₂^*G)`. -/
  homologyIso_tensor : ∀ n : ℕ,
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor k).obj left).obj
          right) ≅
      cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorSheaf f g F G) n)

/-- **The Künneth formula.** For quasi-coherent modules on quasi-compact, quasi-separated
schemes over a field, the cohomology of the external tensor product on `X ×_k Y` is the direct
sum of the tensor products `Hᵖ(X, F) ⊗_k Hᑫ(Y, G)` over the pairs with `p + q = n`, given a
datum `AlgebraicGeometry.KunnethDerivedData` of derived global sections.

This is not the library's form of [Stacks, Tag 0BEF]: that is
`AlgebraicGeometry.KunnethQcqs.isIso_kunnethMap`, which proves the canonical Künneth map an
isomorphism under the tag's own assumptions, with no such datum. -/
theorem nonempty_kunnethIso (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (n : ℕ)
    (d : KunnethDerivedData k f g F G) :
    Nonempty
      (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorSheaf f g F G) n ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct k (cohomologyOverField k f F pq.1.1)
              (cohomologyOverField k g G pq.1.2))) := by
  obtain ⟨e⟩ := CochainComplex.Kunneth.nonempty_derivedTensorHomologyNatIso
    d.left d.right d.isZero_left d.isZero_right n
  obtain ⟨eT⟩ := d.homologyIso_tensor n
  obtain ⟨eS⟩ := CochainComplex.Kunneth.nonempty_directSumTensorIso_of_familyIso
    (ι := {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (fun pq => (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (pq.1.1 : ℤ)).obj d.left)
    (fun pq => cohomologyOverField k f F pq.1.1)
    (fun pq => (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (pq.1.2 : ℤ)).obj d.right)
    (fun pq => cohomologyOverField k g G pq.1.2)
    (fun pq => d.homologyIso_left pq.1.1) (fun pq => d.homologyIso_right pq.1.2)
  exact ⟨eT.symm ≪≫ e ≪≫ eS⟩

end AlgebraicGeometry

end
