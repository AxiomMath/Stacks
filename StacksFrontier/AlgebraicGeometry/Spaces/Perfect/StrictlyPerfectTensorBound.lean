module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverDerivedTensorPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.CategoryTheory.Preadditive.RetractsOfFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.InterfaceShiftedUnit

/-!
# Lower bounds for `(E ⊗^L H) ⊗^L L` with `E` strictly perfect

Let `X` be an algebraic space and `E = P` a bounded complex of retracts of finite free
`𝒪_X`-modules vanishing below `c`. If `H ⊗^L L` has no cohomology below `a`, then neither has
`(P ⊗^L H) ⊗^L L` below `c + a`. Along the stupid filtration of `P` this reduces to a single term
`Pⁱ` in degree `i ≥ c`, a retract of `𝒪_X^{⊕ n}` placed in degree `i`, where it is the unit law.
No associativity of the derived tensor product is used.

## Main results

* `AlgebraicGeometry.Space.isGE_smallEtaleDerivedTensor_tensor_of_strictlyPerfect`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- An additive functor vanishing at `O` vanishes at every retract of a finite free object. -/
theorem isZero_obj_of_isRetractOfFiniteFree {C E : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] [Category E] [Preadditive E] (G : C ⥤ E) [G.Additive] {O M : C}
    (hO : IsZero (G.obj O)) (hM : IsRetractOfFiniteFree O M) : IsZero (G.obj M) := by
  obtain ⟨n, i, p, hip⟩ := hM
  have hB : IsZero (G.obj (⨁ fun _ : Fin n => O)) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← G.map_id, ← biproduct.total, G.map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [G.map_comp, hO.eq_of_tgt (G.map (biproduct.π (fun _ : Fin n => O) j)) 0, zero_comp]
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← G.map_id, ← hip, G.map_comp, hB.eq_of_tgt (G.map i) 0, zero_comp]

/-- **`(M[0] ⊗^L H) ⊗^L L ∈ D^{≥ a}` for `M` a retract of a finite free module and
`H ⊗^L L ∈ D^{≥ a}`**: for `M = 𝒪_X` this is the unit law, and the condition passes to finite
direct sums and to retracts. -/
theorem isGE_smallEtaleDerivedTensor_tensor_single_of_isRetractOfFiniteFree
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hM : IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) M)
    (H L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (hHL : (((smallEtaleDerivedTensor B S hS X).obj H).obj L).IsGE a) :
    (((smallEtaleDerivedTensor B S hS X).obj
      (((smallEtaleDerivedTensor B S hS X).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)).obj H)).obj L).IsGE a := by
  let T := smallEtaleDerivedTensorProduct B S hS X
  have hunit : (((smallEtaleDerivedTensor B S hS X).obj
      (((smallEtaleDerivedTensor B S hS X).obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))).obj H)).obj L).IsGE a := by
    let e₀ := (smallEtaleDerivedTensor B S hS X).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X))) ≪≫
      T.leftSingleUnitNatIso 0 ≪≫ shiftFunctorZero' _ (-0 : ℤ) (by simp)
    let e : ((smallEtaleDerivedTensor B S hS X).obj
        (((smallEtaleDerivedTensor B S hS X).obj ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)))).obj H)).obj L ≅
        ((smallEtaleDerivedTensor B S hS X).obj H).obj L :=
      ((smallEtaleDerivedTensor B S hS X).flip.obj L).mapIso (e₀.app H)
    rw [DerivedCategory.isGE_iff] at hHL ⊢
    intro k hk
    exact (hHL k hk).of_iso ((DerivedCategory.homologyFunctor _ k).mapIso e)
  rw [DerivedCategory.isGE_iff] at hunit ⊢
  intro k hk
  have : (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0 ⋙
      (smallEtaleDerivedTensor B S hS X).flip.obj H ⋙
      (smallEtaleDerivedTensor B S hS X).flip.obj L ⋙
      DerivedCategory.homologyFunctor _ k).Additive := by
    letI := T.commShift_left H
    letI := T.commShift_left L
    have : ((smallEtaleDerivedTensor B S hS X).flip.obj H).Additive := by
      have := T.exact_left H
      exact (inferInstance : (T.tensor.flip.obj H).Additive)
    have : ((smallEtaleDerivedTensor B S hS X).flip.obj L).Additive := by
      have := T.exact_left L
      exact (inferInstance : (T.tensor.flip.obj L).Additive)
    infer_instance
  exact isZero_obj_of_isRetractOfFiniteFree (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0 ⋙
      (smallEtaleDerivedTensor B S hS X).flip.obj H ⋙
      (smallEtaleDerivedTensor B S hS X).flip.obj L ⋙
      DerivedCategory.homologyFunctor _ k) (hunit k hk) hM

/-- **`(P ⊗^L H) ⊗^L L ∈ D^{≥ c + a}` for `P` strictly perfect vanishing below `c` and
`H ⊗^L L ∈ D^{≥ a}`.** -/
theorem isGE_smallEtaleDerivedTensor_tensor_of_strictlyPerfect
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS X)) (P.X j))
    (hPb : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (c : ℤ) (hPc : ∀ i, i < c → IsZero (P.X i))
    (H L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (a : ℤ) (hHL : (((smallEtaleDerivedTensor B S hS X).obj H).obj L).IsGE a) :
    (((smallEtaleDerivedTensor B S hS X).obj
      (((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj P)).obj H)).obj L).IsGE
        (c + a) := by
  let T := smallEtaleDerivedTensorProduct B S hS X
  let : ((smallEtaleDerivedTensor B S hS X).flip.obj H).CommShift ℤ := T.commShift_left H
  let : ((smallEtaleDerivedTensor B S hS X).flip.obj L).CommShift ℤ := T.commShift_left L
  have : ((smallEtaleDerivedTensor B S hS X).flip.obj H).IsTriangulated := T.exact_left H
  have : ((smallEtaleDerivedTensor B S hS X).flip.obj L).IsTriangulated := T.exact_left L
  refine StacksDraft.ExtremalDegrees.isGE_map_Q_of_terms
    ((smallEtaleDerivedTensor B S hS X).flip.obj H ⋙ (smallEtaleDerivedTensor B S hS X).flip.obj L)
    P hPb (c + a) fun i hi => ?_
  have hci : c ≤ i := not_lt.1 fun h => hi (hPc i h)
  have := isGE_smallEtaleDerivedTensor_tensor_single_of_isRetractOfFiniteFree (P.X i) (hP i)
    H L a hHL
  exact DerivedCategory.TStructure.t.isGE_of_ge (((smallEtaleDerivedTensor B S hS X).obj
      (((smallEtaleDerivedTensor B S hS X).obj
        ((DerivedCategory.singleFunctor _ 0).obj (P.X i))).obj H)).obj L) (c + a - i) a (by omega)

end AlgebraicGeometry.Space

end
