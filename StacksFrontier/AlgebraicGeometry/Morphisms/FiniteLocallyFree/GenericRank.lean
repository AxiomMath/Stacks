module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Varieties.FunctionFieldEquivalence.Basic

/-!
# The rank of a finite locally free morphism of integral schemes is its degree

Let `f : X ⟶ Y` be a finite dominant morphism of integral schemes. The fibre of `f` over the
generic point of `Y` is the generic point of `X`, so the stalk of `f_*𝒪_X` at the generic point
of `Y` is the function field of `X`, and its dimension over the function field of `Y` is the
degree `deg(X/Y)` of [Stacks, Tag 02NY]. Hence if `f` is moreover finite locally free, it is
finite locally free of rank `deg(X/Y)`.

This is the identification of the rank of `[d]` with its degree used in the proof of
[Stacks, Tag 0BFG], where the degree is computed by [Stacks, Tag 0BEX].

## Main results

* `AlgebraicGeometry.preimage_genericPoint_of_isFinite_of_isDominant`: the generic fibre of a
  finite dominant morphism of integral schemes is the generic point.
* `fiberRank_pushforward_unit_genericPoint_eq_degreeOver_of_isFinite_of_isDominant`:
  (in `AlgebraicGeometry`) the rank of `f_*𝒪_X` at the generic point of `Y` is `deg(X/Y)`.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_degreeOver`: a finite locally free dominant morphism
  of integral schemes is finite locally free of rank `deg(X/Y)`.
* `Stacks.Morphisms.eq_degreeOver_of_isFiniteLocallyFreeOfRank`: its rank is `deg(X/Y)`.

## References

* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]

/-- **The generic fibre of a finite dominant morphism of integral schemes is the generic point**:
the fibre is discrete, as `f` is locally quasi-finite, and every point of it is a specialization of
the generic point of `X`, which lies in it. -/
theorem preimage_genericPoint_of_isFinite_of_isDominant [IsFinite f] [IsDominant f] :
    f.base ⁻¹' ({genericPoint Y} : Set Y) = {genericPoint X} := by
  have hgen := map_genericPoint_of_isDominant f
  refine Set.Subset.antisymm (fun x hx => ?_) (by simpa using hgen)
  have hdisc := f.isDiscrete_preimage_singleton (genericPoint Y)
  have hsub : ({genericPoint X, x} : Set X) ⊆ f.base ⁻¹' {genericPoint Y} := by
    rintro z (rfl | rfl)
    · exact hgen
    · exact hx
  have hirr : IsPreirreducible ({genericPoint X, x} : Set X) := by
    rw [← isPreirreducible_iff_closure]
    have : closure ({genericPoint X, x} : Set X) = closure {genericPoint X} := by
      refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono (by simp))
      rintro z (rfl | rfl)
      · exact subset_closure rfl
      · exact (genericPoint_specializes _).mem_closure
    rw [this]
    exact isPreirreducible_singleton.closure
  exact ((hdisc.mono hsub).subsingleton_of_isPreirreducible hirr (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ rfl)).symm

/-- **The rank of `f_*𝒪_X` at the generic point of `Y` is the degree `[R(X) : R(Y)]`**, for a
finite dominant morphism of integral schemes. The fibre over the generic point `ξ` of `Y` is the
generic point `η` of `X` (`AlgebraicGeometry.preimage_genericPoint_of_isFinite_of_isDominant`), so
the stalk of `f_*𝒪_X` at `ξ` is the stalk of `𝒪_X` at `η` ([Stacks, Tag 05B8]), whose dimension
over the function field of `Y` is the degree. This is
`AlgebraicGeometry.fiberRank_pushforward_unit_genericPoint_eq_degreeOver` without the curve
hypotheses. -/
theorem fiberRank_pushforward_unit_genericPoint_eq_degreeOver_of_isFinite_of_isDominant [IsFinite f]
    [IsDominant f] :
    Scheme.Modules.fiberRank
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
        (genericPoint (Y : Type u)) = degreeOver f := by
  have hgen : f.base (genericPoint (X : Type u)) = genericPoint (Y : Type u) :=
    map_genericPoint_of_isDominant f
  have hfiber : f.base ⁻¹' ({f.base (genericPoint (X : Type u))} : Set Y) =
      {genericPoint (X : Type u)} := by
    rw [hgen]
    exact preimage_genericPoint_of_isFinite_of_isDominant f
  let : Module (X.presheaf.stalk (genericPoint (X : Type u)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (SheafOfModules.unit X.ringCatSheaf).val (genericPoint (X : Type u))
  let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) :=
    Module.compHom _ (f.stalkMap (genericPoint (X : Type u))).hom
  let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
      (X.presheaf.stalk (genericPoint (X : Type u))) :=
    Module.compHom _ (f.stalkMap (genericPoint (X : Type u))).hom
  let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).val.presheaf
        (f.base (genericPoint (X : Type u)))) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
      (f.base (genericPoint (X : Type u)))
  have hfieldY : IsField (Y.presheaf.stalk (f.base (genericPoint (X : Type u)))) := by
    rw [hgen]
    exact isField_stalk_genericPoint Y
  obtain ⟨e05⟩ :=
    AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber f
      (genericPoint (X : Type u)) hfiber (SheafOfModules.unit X.ringCatSheaf)
  have h1 := fiberRank_eq_finrank_stalk_of_isField
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    (f.base (genericPoint (X : Type u))) hfieldY
  have h2 : Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) =
      Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf)).val.presheaf
          (f.base (genericPoint (X : Type u)))) :=
    LinearEquiv.finrank_eq e05.toLinearEquiv
  have h3 : Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) =
      Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (X.presheaf.stalk (genericPoint (X : Type u))) := by
    let : Module (X.presheaf.stalk (genericPoint (X : Type u)))
        ((Stacks.Divisors.structureModule X).presheaf.stalk (genericPoint (X : Type u))) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (Stacks.Divisors.structureModule X).val (genericPoint (X : Type u))
    let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        ((Stacks.Divisors.structureModule X).presheaf.stalk (genericPoint (X : Type u))) :=
      Module.compHom _ (f.stalkMap (genericPoint (X : Type u))).hom
    refine LinearEquiv.finrank_eq ?_
    let e := (Stacks.Divisors.unitStalkLinearEquiv (X := X) (genericPoint (X : Type u))).symm
    exact
      { toFun := e
        map_add' := e.map_add
        map_smul' := fun a m =>
          e.map_smul ((f.stalkMap (genericPoint (X : Type u))).hom a) m
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv }
  rw [← hgen]
  exact h1.trans (h2.symm.trans (h3.trans (finrank_stalk_genericPoint_eq_degreeOver f hgen)))

end AlgebraicGeometry

namespace Stacks.Morphisms

open _root_.AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]

/-- **A finite locally free dominant morphism of integral schemes is finite locally free of rank
`deg(X/Y)`.** The fibre rank of `f_*𝒪_X` is locally constant on the connected `Y`, and at the
generic point it is the degree. -/
theorem isFiniteLocallyFreeOfRank_degreeOver [h : IsFiniteLocallyFree f] [IsFinite f]
    [IsDominant f] : IsFiniteLocallyFreeOfRank f (degreeOver f) :=
  .mk (toIsAffineHom := h.toIsAffineHom)
    (toIsFiniteLocallyFreeOfRank := Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq _
      (degreeOver f) (genericPoint Y)
      (fiberRank_pushforward_unit_genericPoint_eq_degreeOver_of_isFinite_of_isDominant f))

/-- **The rank of a finite locally free dominant morphism of integral schemes is `deg(X/Y)`.** -/
theorem eq_degreeOver_of_isFiniteLocallyFreeOfRank [IsFinite f] [IsDominant f] (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] : r = degreeOver f :=
  (Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank _ r (genericPoint Y)).symm.trans
    (fiberRank_pushforward_unit_genericPoint_eq_degreeOver_of_isFinite_of_isDominant f)

end Stacks.Morphisms
