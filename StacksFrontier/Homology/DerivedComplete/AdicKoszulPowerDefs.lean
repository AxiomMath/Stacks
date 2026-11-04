module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulTower
public import StacksFrontier.Homology.DerivedComplete.CompleteKoszulPowers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical tensor--Koszul tower and Koszul derived completions

The canonical tensor--Koszul tower and its functorial derived-limit data are shared by the
characterisation of derived completeness through Koszul complexes (Stacks 091Z) and by the
auxiliary constructions used in its proof.

## Main definitions

* `AdicKoszul.canonicalKoszulPowerSystem` is the canonical inverse system of Koszul complexes on
  positive powers of a finite sequence.
* `AdicKoszul.derivedTensorKoszulPowerUnit` is the canonical map from a complex to its derived
  tensor product with one term of the Koszul power system.
* `AdicKoszul.tensorKoszulPowerSystem` handles complexes in an independent module universe.
* `AdicKoszul.KoszulPowerCompletion` records the functorial derived limit and its natural unit.

## Main results

* `AdicKoszul.KoszulPowerCompletion.isDerivedLimit` identifies each completion value with the
  specified derived limit after universe enlargement.

## Implementation notes

A functor, a natural unit, and natural projections are supplied together, for all complexes.
The projections exhibit the defining Milnor triangle. Ring and module universes are independent:
`ULift` is used only inside the tensor calculation, while the completion stays in the original
derived category. The ring-only Koszul system has the ring's universe; arbitrary coefficient
complexes enter through `AdicKoszul.tensorKoszulPowerSystem`. The chain-complex convention places
the Koszul complexes in nonnegative homological degrees; extending along `j ↦ -j` places them in
the source's nonpositive cohomological degrees.

## References

* [The Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace AdicKoszul

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The canonical transition map between Koszul complexes on two positive powers of a finite
sequence, selected from the inverse system of Stacks 0BKC. -/
@[ega "III 1.1.6"]
public noncomputable def koszulPowerTransition {r : ℕ} (f : Fin r → A) :
    ∀ (m n : ℕ), n ≤ m →
      (Koszul.seqComplex (fun i ↦ f i ^ (m + 1)) ⟶
        Koszul.seqComplex (fun i ↦ f i ^ (n + 1))) :=
  Classical.choose (_root_.koszulPowerComplexes_form_inverseSystem f)

/-- **The selected transition map is the explicit one**: scaling the `i`-th coordinate of `Aʳ` by
`f i ^ (m - n)` and taking the induced map of exterior powers.  The selection is a
`Classical.choose`, but the fifth clause of Stacks 0BKC pins it on the wedges of vectors, which
span each exterior power, so the choice is determined
(`choose_koszulPowerComplexes_form_inverseSystem_eq`).

Without this the transition maps of `AdicKoszul.canonicalKoszulPowerSystem` are opaque and no
equation relating that tower to another model of the Koszul complex can be stated. -/
@[ega "III 1.1.6"]
public theorem koszulPowerTransition_eq {r : ℕ} (f : Fin r → A) (m n : ℕ) (h : n ≤ m) :
    koszulPowerTransition f m n h = _root_.transition f m n h :=
  _root_.choose_koszulPowerComplexes_form_inverseSystem_eq f m n h

/-- The canonical map from the ring in degree zero to a Koszul complex on a positive power of a
finite sequence, selected compatibly with `AdicKoszul.koszulPowerTransition` from Stacks 0BKC. -/
public noncomputable def koszulPowerUnitChain {r : ℕ} (f : Fin r → A) : ∀ n : ℕ,
    (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A) ⟶
      Koszul.seqComplex (fun i ↦ f i ^ (n + 1)) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (_root_.koszulPowerComplexes_form_inverseSystem f))))

/-- The canonical map from `A[0]` to the cohomologically indexed Koszul complex on the
`(n + 1)`-st powers of `f`. -/
public noncomputable def koszulPowerUnit {r : ℕ} (f : Fin r → A) (n : ℕ) :
    ((CochainComplex.singleFunctors (ModuleCat.{u} A)).functor 0).obj (ModuleCat.of A A) ⟶
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))) :=
  HomologicalComplex.mkHomFromSingle
    ((koszulPowerUnitChain f n).f 0 ≫
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := 0) rfl).inv)
    (fun i hi ↦ by
      change 0 + 1 = i at hi
      simp only [zero_add] at hi
      subst i
      apply (HomologicalComplex.isZero_extend_X
        (Koszul.seqComplex (fun i ↦ f i ^ (n + 1)))
        ComplexShape.embeddingDownNat 1 ?_).eq_of_tgt
      intro j
      change -(j : ℤ) ≠ 1
      omega)

/-- The canonical inverse system in `D(A)` of Koszul complexes on the positive powers of `f`. -/
@[sga "2 II Lemma9"]
public noncomputable abbrev canonicalKoszulPowerSystem {r : ℕ} (f : Fin r → A) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  koszulPowerSystem f
    (fun n ↦ koszulPowerTransition f (n + 1) n (Nat.le_succ n))

/-- Put modules and the coefficient ring in a common universe. This changes neither the
module nor its scalars up to their canonical equivalences. -/
public noncomputable abbrev moduleUniverseLift (A : Type u) [CommRing A] :
    ModuleCat.{v} A ⥤ ModuleCat.{max u v} (ULift.{v} A) :=
  ModuleCat.uliftFunctor.{u, v} A ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom

/-- The exact universe enlargement on derived categories. The source module universe is
independent of the universe of the ring. -/
public noncomputable abbrev derivedUniverseLift (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{v} A) ⥤
      DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)) :=
  (moduleUniverseLift.{u, v} A).mapDerivedCategory

/-- The tensor--Koszul tower of an arbitrary complex. Only the tensor calculation takes
place in a common universe; the complex and its completion retain their original universe. -/
public noncomputable abbrev tensorKoszulPowerSystem {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A))
    (K : DerivedCategory (ModuleCat.{v} A)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)) :=
  canonicalKoszulPowerSystem (fun i ↦ (ULift.up (f i) : ULift.{v} A)) ⋙
    T.tensor.obj ((derivedUniverseLift A).obj K)

/-- The canonical map from the enlarged complex to a term of its tensor--Koszul tower. -/
public noncomputable def derivedTensorKoszulPowerUnit {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A))
    (K : DerivedCategory (ModuleCat.{v} A)) (n : ℕ) :
    (derivedUniverseLift A).obj K ⟶ (tensorKoszulPowerSystem f T K).obj ⟨n⟩ :=
  T.rightUnitor.inv.app ((derivedUniverseLift A).obj K) ≫
    (T.tensor.obj ((derivedUniverseLift A).obj K)).map
      (DerivedCategory.Q.map (koszulPowerUnit
        (fun i ↦ (ULift.up (f i) : ULift.{v} A)) n))

/-- The derived category of `R`-modules has countable products, in every module universe. -/
local instance derivedCountableProducts (R : Type u) [CommRing R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- A functorial realization of the Koszul derived limit and its canonical map, defined
for every complex, without a completeness assumption. The natural projections give the
specified Milnor triangle and recover the maps induced by `A → Kₙ`. -/
public structure KoszulPowerCompletion {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) where
  /-- The derived-limit object, in the original module universe. -/
  functor : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)
  /-- The canonical map exists naturally for every complex. -/
  unit : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ functor
  /-- The canonical projections are natural in the complex. -/
  projection (n : ℕ) : functor ⋙ derivedUniverseLift A ⟶
    derivedUniverseLift A ⋙ T.tensor.flip.obj
      ((canonicalKoszulPowerSystem (fun i ↦ (ULift.up (f i) : ULift.{v} A))).obj ⟨n⟩)
  /-- The projections exhibit the value as the derived limit of the specified tower. -/
  milnor (K : DerivedCategory (ModuleCat.{v} A)) :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (tensorKoszulPowerSystem f T K).obj ⟨n⟩) ⟶
        ((derivedUniverseLift A).obj (functor.obj K))⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift fun n ↦ (projection n).app K)
        (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ (tensorKoszulPowerSystem f T K).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ (tensorKoszulPowerSystem f T K).obj ⟨n⟩) (n + 1) ≫
              (tensorKoszulPowerSystem f T K).map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)))
  /-- The unit is the map induced by the compatible maps from the ring to the Koszul terms. -/
  unit_projection (K : DerivedCategory (ModuleCat.{v} A)) (n : ℕ) :
    (derivedUniverseLift A).map (unit.app K) ≫ (projection n).app K =
      derivedTensorKoszulPowerUnit f T K n

/-- Every value of a Koszul completion is the specified derived limit after the harmless
universe enlargement used to form tensor products. -/
public theorem KoszulPowerCompletion.isDerivedLimit {r : ℕ} {f : Fin r → A}
    {T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)}
    (C : KoszulPowerCompletion f T) (K : DerivedCategory (ModuleCat.{v} A)) :
    IsDerivedLimit (tensorKoszulPowerSystem f T K)
      ((derivedUniverseLift A).obj (C.functor.obj K)) := by
  obtain ⟨δ, hδ⟩ := C.milnor K
  exact ⟨Pi.lift fun n ↦ (C.projection n).app K, δ, hδ⟩

end AdicKoszul

end
