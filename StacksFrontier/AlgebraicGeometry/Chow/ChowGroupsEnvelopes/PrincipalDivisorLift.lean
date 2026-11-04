module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.SubschemeLift
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec

/-!
# Lifting a principal divisor along a completely decomposed morphism

Let `f : Y ⟶ X` be proper and completely decomposed, let `W ⊆ X` be an integral closed subscheme
of delta-dimension `n` over the base and let `g` be a nonzero rational function on `W`. The
lifted closed subscheme `V ⊆ Y` maps to `W` by a proper dominant morphism which is an isomorphism
on residue fields at the generic point, so the induced extension of function fields
`R(W) ⊆ R(V)` is an isomorphism. Thus `g` lifts to a rational function on `V`, and the
pushforward to `X` of the principal divisor of the lift is the principal divisor of `g`.

## Main definitions

* `Stacks.Chow.envelopeRationalFunctionLift` — the rational function on the lifted closed
  subscheme obtained from a rational function on the original one.

## Main results

* `Stacks.Chow.bijective_dominantFunctionFieldMap_envelopeSubschemeLiftMap` — the extension of
  function fields induced by the lift is an isomorphism.
* `Stacks.Chow.properPushforward_principalDivisorPushforward_envelopeSubschemeLift` — the
  pushforward along `f` of the principal divisor of the lifted rational function is the
  principal divisor of the original one.

## References

* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The function field of an integral scheme -/

/-- Transporting an isomorphism of stalks along an equality of base points gives a bijection. -/
theorem bijective_stalkMap_transport {V W : Scheme.{u}} (p : V ⟶ W) (x : V) {w : W}
    (h : p.base x = w) (hiso : IsIso (p.stalkMap x)) :
    Function.Bijective
      (h ▸ p.stalkMap x : W.presheaf.stalk w ⟶ V.presheaf.stalk x).hom := by
  subst h
  exact ConcreteCategory.bijective_of_isIso _

/-- A dominant morphism of integral schemes which is an isomorphism on residue fields at the
generic point induces an isomorphism of function fields. -/
theorem bijective_dominantFunctionFieldMap_of_residueFieldMap_isIso {V W : Scheme.{u}}
    (p : V ⟶ W) [IsIntegral V] [IsIntegral W] [IsDominant p]
    (hres : IsIso (p.residueFieldMap (genericPoint V))) :
    Function.Bijective (dominantFunctionFieldMap p) := by
  have hη : p.base (genericPoint V) = genericPoint W :=
    ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)
  have : IsIso (W.residue (p.base (genericPoint V))) := by
    rw [hη]
    exact AlgebraicGeometry.isIso_residue_genericPoint W
  have : IsIso (V.residue (genericPoint V)) := AlgebraicGeometry.isIso_residue_genericPoint V
  have : IsIso (p.stalkMap (genericPoint V) ≫ V.residue (genericPoint V)) := by
    rw [← Scheme.residue_residueFieldMap]
    infer_instance
  have : IsIso (p.stalkMap (genericPoint V)) :=
    IsIso.of_isIso_comp_right _ (V.residue (genericPoint V))
  exact bijective_stalkMap_transport p (genericPoint V) hη inferInstance

/-- The norm of an element of the base field along a trivial field extension is the element
itself. -/
theorem norm_algebraMap_eq_self_of_bijective {A B : Type u} [Field A] [Field B] [Algebra A B]
    (hbij : Function.Bijective (algebraMap A B)) (a : A) :
    Algebra.norm A (algebraMap A B a) = a := by
  simp [Algebra.norm_algebraMap, Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hbij]

/-- The norm along a bijective homomorphism of fields is the identity. -/
theorem norm_eq_self_of_bijective {A B : Type u} [Field A] [Field B] (φ : A →+* B)
    (hbij : Function.Bijective φ) (a : A) :
    letI := φ.toAlgebra
    Algebra.norm A (φ a) = a := by
  let := φ.toAlgebra
  exact norm_algebraMap_eq_self_of_bijective hbij a

/-! ### The lifted rational function -/

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f) (W : X.IdealSheafData)
  (hW : IsIntegral W.subscheme)

/-- The extension of function fields induced by the lift of an integral closed subscheme is an
isomorphism. -/
theorem bijective_dominantFunctionFieldMap_envelopeSubschemeLiftMap :
    have := hW
    have := isIntegral_envelopeSubschemeLift f hcd W hW
    have := isDominant_envelopeSubschemeLiftMap f hcd W hW
    Function.Bijective (dominantFunctionFieldMap (envelopeSubschemeLiftMap f hcd W hW)) := by
  intros
  exact bijective_dominantFunctionFieldMap_of_residueFieldMap_isIso _
    (envelopeSubschemeLiftMap_residueFieldMap_isIso f hcd W hW)

/-- The rational function on the lifted closed subscheme obtained by pulling a rational function
back along the lift. -/
def envelopeRationalFunctionLift (g : (rationalFunctions W.subscheme)ˣ) :
    (rationalFunctions (envelopeSubschemeLift f hcd W hW).subscheme)ˣ :=
  have := hW
  have := isIntegral_envelopeSubschemeLift f hcd W hW
  have := isDominant_envelopeSubschemeLiftMap f hcd W hW
  Units.map
    ((rationalFunctionsEquivFunctionField
            (envelopeSubschemeLift f hcd W hW).subscheme).1.symm.toRingHom.comp
        ((dominantFunctionFieldMap (envelopeSubschemeLiftMap f hcd W hW)).comp
          (rationalFunctionsEquivFunctionField W.subscheme).1.toRingHom)).toMonoidHom g

/-- The lifted rational function is, in the function field of the lift, the image of the
original one under the induced extension of function fields. -/
theorem rationalFunctionsEquivFunctionField_envelopeRationalFunctionLift
    (g : (rationalFunctions W.subscheme)ˣ) :
    have := hW
    have := isIntegral_envelopeSubschemeLift f hcd W hW
    have := isDominant_envelopeSubschemeLiftMap f hcd W hW
    (rationalFunctionsEquivFunctionField (envelopeSubschemeLift f hcd W hW).subscheme).1
        (envelopeRationalFunctionLift f hcd W hW g :
          rationalFunctions (envelopeSubschemeLift f hcd W hW).subscheme) =
      dominantFunctionFieldMap (envelopeSubschemeLiftMap f hcd W hW)
        ((rationalFunctionsEquivFunctionField W.subscheme).1
          (g : rationalFunctions W.subscheme)) := by
  intros
  exact (rationalFunctionsEquivFunctionField
    (envelopeSubschemeLift f hcd W hW).subscheme).1.apply_symm_apply _

/-! ### The pushforward of the lifted principal divisor -/

/-- The pushforward along `f` of the principal divisor of the lifted rational function on the
lifted closed subscheme is the principal divisor of the original rational function on the
original closed subscheme. -/
theorem properPushforward_principalDivisorPushforward_envelopeSubschemeLift
    (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsProper f] {n : ℤ}
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = (n : EInt))
    (g : (rationalFunctions W.subscheme)ˣ) :
    AlgebraicCycle.map f (relativeDimension C.dimensionFunction (f ≫ sX))
        (relativeDimension C.dimensionFunction sX)
        (principalDivisorPushforward C (f ≫ sX) (envelopeSubschemeLift f hcd W hW)
          (isIntegral_envelopeSubschemeLift f hcd W hW)
          (envelopeRationalFunctionLift f hcd W hW g)) =
      principalDivisorPushforward C sX W hW g := by
  have := hW
  have hV := isIntegral_envelopeSubschemeLift f hcd W hW
  have := isDominant_envelopeSubschemeLiftMap f hcd W hW
  have := isProper_envelopeSubschemeLiftMap f hcd W hW
  set V := envelopeSubschemeLift f hcd W hW
  set lift := envelopeSubschemeLiftMap f hcd W hW
  set sW : W.subscheme ⟶ C.S := W.subschemeι ≫ sX with hsW
  set sV : V.subscheme ⟶ C.S := V.subschemeι ≫ f ≫ sX with hsV
  have hnV : schemeDeltaDimension C sV = (n : EInt) :=
    (schemeDeltaDimension_envelopeSubschemeLift f hcd W hW C sX).trans hDim
  have hstruct : lift ≫ sW = sV := by
    rw [hsW, hsV, ← Category.assoc, envelopeSubschemeLiftMap_fac, Category.assoc]
  set fW : W.subscheme.functionField :=
    (rationalFunctionsEquivFunctionField W.subscheme).1 (g : rationalFunctions W.subscheme)
  set fV : V.subscheme.functionField :=
    (rationalFunctionsEquivFunctionField V.subscheme).1
      (envelopeRationalFunctionLift f hcd W hW g : rationalFunctions V.subscheme)
  have hfVeq : fV = dominantFunctionFieldMap lift fW :=
    rationalFunctionsEquivFunctionField_envelopeRationalFunctionLift f hcd W hW g
  have hfVne : fV ≠ 0 := fun h ↦ (envelopeRationalFunctionLift f hcd W hW g).ne_zero
    ((rationalFunctionsEquivFunctionField V.subscheme).1.injective
      (h.trans (map_zero _).symm))
  set DV : CycleGroup C sV (n - 1) := principalDivisorCycle C sV hnV fV with hDV
  set DW : CycleGroup C sW (n - 1) := principalDivisorCycle C sW hDim fW with hDW
  have hpushV : AlgebraicCycle.map V.subschemeι
      (relativeDimension C.dimensionFunction sV)
      (relativeDimension C.dimensionFunction (f ≫ sX)) DV.1 =
      principalDivisorPushforward C (f ≫ sX) V hV
        (envelopeRationalFunctionLift f hcd W hW g) := rfl
  have hpushW : AlgebraicCycle.map W.subschemeι
      (relativeDimension C.dimensionFunction sW)
      (relativeDimension C.dimensionFunction sX) DW.1 =
      principalDivisorPushforward C sX W hW g := rfl
  rw [← hpushV, ← hpushW]
  show (properPushforward C (f ≫ sX) sX f rfl (n - 1)
      (properPushforward C sV (f ≫ sX) V.subschemeι rfl (n - 1) DV)).1 =
    (properPushforward C sW sX W.subschemeι rfl (n - 1) DW).1
  rw [properPushforward_properPushforward C sV (f ≫ sX) sX V.subschemeι f rfl rfl (n - 1) DV]
  have hmor : V.subschemeι ≫ f = lift ≫ W.subschemeι :=
    (envelopeSubschemeLiftMap_fac f hcd W hW).symm
  rw [properPushforward_apply_congr C sV sX hmor (by rw [Category.assoc]) (by
      rw [Category.assoc, ← hsW, hstruct]) (n - 1) DV,
    ← properPushforward_properPushforward C sV sW sX lift W.subschemeι hstruct rfl (n - 1) DV]
  refine congrArg (fun c : CycleGroup C sW (n - 1) ↦
    (properPushforward C sW sX W.subschemeι rfl (n - 1) c).1) ?_
  rw [hDV, hDW, properPushforward_principalDivisorCycle C sV sW hnV hDim lift hstruct fV hfVne]
  refine congrArg (principalDivisorCycle C sW hDim) ?_
  rw [hfVeq]
  exact norm_eq_self_of_bijective (dominantFunctionFieldMap lift)
    (bijective_dominantFunctionFieldMap_envelopeSubschemeLiftMap f hcd W hW) fW

end Stacks.Chow

end
