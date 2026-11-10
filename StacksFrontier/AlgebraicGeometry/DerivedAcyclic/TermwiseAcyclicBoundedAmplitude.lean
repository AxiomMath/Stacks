module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# A complex of acyclic objects computes a right derived functor of bounded amplitude

Let `F : 𝒜 ⥤ 𝒯` be a left exact additive functor out of a Grothendieck abelian category, with right
derived functor `RF` on the unbounded derived category, and let `P` be a weak Serre class of
objects of `𝒜` ([Stacks, Tag 0754]); only its closure under kernels, cokernels and isomorphisms and
its containing zero are used. Assume `RF` has cohomological amplitude bounded above by `N` on
complexes with cohomology in `P`: it carries such a complex in `D^{≤ d}` into `D^{≤ d + N - 1}`.
Then a cochain complex `K` whose terms lie in `P` and are right acyclic for `F` computes `RF`: the
comparison `F(K) ⟶ RF(K)` is an isomorphism.

This is the argument of [Stacks, Tag 0G9N], stated for an arbitrary class `P` and an arbitrary
right derived functor. Fix a degree `q` and replace `K` by its stupid truncation `σ^{≥a}K` with
`a < q` and `a + N ≤ q`: the truncation is bounded below with right-acyclic terms, so the
comparison is invertible there by Leray's acyclicity criterion; `F` sees `σ^{≥a}K ⟶ K` as an
isomorphism on `H^q`, the map being a degreewise isomorphism above `a`; and so does `RF`, the
third vertex of the stupid truncation triangle lying in `D^{≤ a - 1}` with cohomology in `P`.

## Main results

* `Stacks.DerivedAcyclic.isIso_app_of_rightAcyclic_of_isLE`: the statement above.

## References

* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.DerivedAcyclic

variable {A : Type*} [Category* A] [Abelian A]

/-- The cohomology of a complex whose terms satisfy an object property closed under kernels and
cokernels satisfies it too: the cycles are a kernel of a map between two terms and the cohomology
is a cokernel of a map into the cycles. -/
lemma prop_homology_of_prop_X (P : ObjectProperty A) [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] (K : CochainComplex A ℤ) (hK : ∀ n : ℤ, P (K.X n)) (i : ℤ) :
    P (K.homology i) :=
  P.prop_of_isColimit_cokernelCofork
    (K.homologyIsCokernel ((ComplexShape.up ℤ).prev i) i rfl) (hK _)
    (P.prop_of_isLimit_kernelFork
      (K.cyclesIsKernel i ((ComplexShape.up ℤ).next i) rfl) (hK i) (hK _))

/-- The terms of a stupid truncation in degrees `≤ a` of a complex with terms in `P` are in `P`:
each is either a term of the complex or zero. -/
lemma prop_stupidTruncLE_X (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (K : CochainComplex A ℤ) (hK : ∀ n : ℤ, P (K.X n)) (a i : ℤ) :
    P ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X i) := by
  by_cases hi : i ≤ a
  · have heq : (ComplexShape.embeddingUpIntLE a).f (a - i).toNat = i := by
      change a - ((a - i).toNat : ℤ) = i
      omega
    exact P.prop_of_iso (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE a) heq).symm (hK i)
  · exact P.prop_of_isZero
      (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) i
        (by rw [ComplexShape.notMem_range_embeddingUpIntLE_iff]; omega))

variable {T : Type*} [Category* T] [Abelian T] [HasDerivedCategory A] [HasDerivedCategory T]

/-- Above the amplitude bound the derived functor sees `σ^{≥a}K ⟶ K` as an isomorphism on
`H^q`: the third term of the stupid truncation triangle lies in `D^{≤ a - 1}` with cohomology in
`P`, so its image lies in `D^{≤ a + N - 2}`, which `q` exceeds. -/
lemma isIso_homologyFunctor_map_rightDerived_stupidTrunc_of_prop
    (P : ObjectProperty A) [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (RF : DerivedCategory A ⥤ DerivedCategory T) [RF.CommShift ℤ] [RF.IsTriangulated] (N : ℤ)
    (hUpper : ∀ (E : DerivedCategory A) (d : ℤ),
      (∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E)) →
      E.IsLE d → (RF.obj E).IsLE (d + N - 1))
    (K : CochainComplex A ℤ) (hK : ∀ n, P (K.X n)) (a q : ℤ) (ha : a + N ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor T q).map
      (RF.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)))))) := by
  let tail := K.stupidTrunc (ComplexShape.embeddingUpIntLE (a - 1))
  have hTail : (RF.obj (DerivedCategory.Q.obj tail)).IsLE (a - 1 + N - 1) :=
    hUpper (DerivedCategory.Q.obj tail) (a - 1)
      (fun i ↦ P.prop_of_iso ((DerivedCategory.homologyFunctorFactors A i).app tail).symm
        (prop_homology_of_prop_X P tail (prop_stupidTruncLE_X P K hK (a - 1)) i))
      (Stacks.DerivedAcyclic.isLE_stupidTruncLE K (a - 1))
  let Tri := (DerivedCategory.Qh ⋙ RF).mapTriangle.obj
    (Stacks.DerivedAcyclic.stupidTruncTriangleh K (a - 1))
  have hTri : Tri ∈ distTriang (DerivedCategory T) :=
    (DerivedCategory.Qh ⋙ RF).map_distinguished _
      (Stacks.DerivedAcyclic.stupidTruncTriangleh_distinguished K (a - 1))
  have hTail' : Tri.obj₃.IsLE (a - 1 + N - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (RF.mapIso ((DerivedCategory.quotientCompQhIso A).symm.app tail)) (a - 1 + N - 1)
  have hepi : Epi ((DerivedCategory.homologyFunctor T q).map Tri.mor₁) :=
    ((DerivedCategory.homologyFunctor T 0).homologySequence_epi_shift_map_mor₁_iff
      Tri hTri q).2 ((Tri.obj₃.isZero_of_isLE (a - 1 + N - 1) q (by omega)).eq_of_tgt _ _)
  have hmono : Mono ((DerivedCategory.homologyFunctor T q).map Tri.mor₁) :=
    ((DerivedCategory.homologyFunctor T 0).homologySequence_mono_shift_map_mor₁_iff
      Tri hTri (q - 1) q (by omega)).2
      ((Tri.obj₃.isZero_of_isLE (a - 1 + N - 1) (q - 1) (by omega)).eq_of_src _ _)
  have hiso : IsIso ((DerivedCategory.homologyFunctor T q).map Tri.mor₁) :=
    isIso_of_mono_of_epi _
  change IsIso ((DerivedCategory.homologyFunctor T q).map
    ((DerivedCategory.Qh ⋙ RF).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (a - 1 + 1)))))) at hiso
  rw [show a - 1 + 1 = a by omega] at hiso
  simpa only [Functor.comp_map] using hiso

/-- **A complex of right-acyclic objects computes a right derived functor of bounded amplitude.**
Let `P` be a weak Serre class, and let `RF` carry complexes in `D^{≤ d}` with cohomology in `P`
into `D^{≤ d + N - 1}`. Then for a complex `K` with terms in `P` and right acyclic for `F`, the
comparison `F(K) ⟶ RF(K)` is an isomorphism. -/
theorem isIso_app_of_rightAcyclic_of_isLE [IsGrothendieckAbelian A] [EnoughInjectives A]
    (F : A ⥤ T) [F.Additive] [PreservesFiniteLimits F]
    (RF : DerivedCategory A ⥤ DerivedCategory T)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (P : ObjectProperty A) (hP : P.IsWeakSerreClass) (N : ℕ)
    (hUpper : ∀ (E : DerivedCategory A) (d : ℤ),
      (∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E)) →
      E.IsLE d → (RF.obj E).IsLE (d + N - 1))
    (K : CochainComplex A ℤ) (hK : ∀ n, P (K.X n))
    (hacyclic : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  have := hP
  let : RF.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated := Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor F RF α
  rw [DerivedCategory.isIso_iff]
  intro q
  let Φ := DerivedCategory.homologyFunctor T q
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a : ℤ, a < q ∧ a + (N : ℤ) ≤ q :=
    ⟨min (q - 1) (q - N), by omega, by omega⟩
  let v := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
    (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a))
  have hleft : IsIso (Φ.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v)) :=
    Stacks.DerivedAcyclic.isIso_homologyFunctor_map_termwise_stupidTrunc F K a q ha₁
  have hright : IsIso (Φ.map (RF.map (DerivedCategory.Qh.map v))) :=
    isIso_homologyFunctor_map_rightDerived_stupidTrunc_of_prop P RF (N : ℤ) hUpper K hK a q ha₂
  have htail : IsIso (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) :=
    Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic F RF α _
      (Stacks.DerivedAcyclic.plus_stupidTruncGE K a)
      (Stacks.DerivedAcyclic.rightAcyclic_stupidTruncGE F K hacyclic a)
  have hcomp : IsIso
      (Φ.map ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v) ≫
        Φ.map (α.app ((HomotopyCategory.quotient _ _).obj K))) := by
    rw [← Functor.map_comp, α.naturality v, Functor.map_comp]
    change IsIso (Φ.map (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) ≫
      Φ.map (RF.map (DerivedCategory.Qh.map v)))
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Φ.map ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v))
    (Φ.map (α.app ((HomotopyCategory.quotient _ _).obj K)))

end Stacks.DerivedAcyclic

end
