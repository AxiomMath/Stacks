module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IrreducibleGenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.AtPointCriteria
public import StacksCore.Tactic.StacksAttribute

/-!
# Rational functions and the order of vanishing along an étale morphism

Let `f : U ⟶ V` be an étale morphism of integral, locally Noetherian schemes. It is dominant, so
it induces a map `R(V) ⟶ R(U)` of function fields, and the order of vanishing is unchanged by it:
at every point `z` of `U` the pullback of a rational function on `V` vanishes to the same order as
the function does at `f z`.

## Main results

* `AlgebraicGeometry.coheight_eq_of_etale`: an étale morphism preserves codimension.
* `AlgebraicGeometry.isDominant_of_etale`: an étale morphism of integral schemes is dominant.
* `AlgebraicGeometry.length_quotient_span_stalkMap_of_etale`: the colength of a principal ideal
  is unchanged by the stalk map of an étale morphism.
* `Stacks.Chow.ord_dominantFunctionFieldMap_of_etale`: the order of vanishing is unchanged by an
  étale morphism.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD): the order of vanishing
  as a colength.
* [Stacks Project, Tag 04N8](https://stacks.math.columbia.edu/tag/04N8): an étale morphism
  preserves the dimension of local rings.
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1): the colength identity
  for a flat local homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme
open IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Codimension and dominance -/

/-- **An étale morphism preserves codimension.** -/
theorem coheight_eq_of_etale {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (z : U) :
    coheight (f.base z) = coheight z := by
  have h := ringKrullDim_stalk_eq_of_etale f z
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h.symm

/-- **An étale morphism of integral schemes is dominant.** -/
theorem isDominant_of_etale {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] [IsIntegral U]
    [IsIntegral V] : IsDominant f := by
  refine ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_univ_subset ?_)⟩
  rw [← genericPoint_spec (α := ↥V) |>.def]
  exact closure_mono (Set.singleton_subset_iff.mpr (genericPoint_mem_range_of_universallyOpen f))

/-! ### Colengths along the stalk map of an étale morphism -/

/-- **The colength of a principal ideal is unchanged by the stalk map of an étale morphism.** -/
theorem length_quotient_span_stalkMap_of_etale {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (z : U)
    (a : V.presheaf.stalk (f.base z)) :
    Module.length (U.presheaf.stalk z)
        (U.presheaf.stalk z ⧸ Ideal.span {(f.stalkMap z).hom a}) =
      Module.length (V.presheaf.stalk (f.base z))
        (V.presheaf.stalk (f.base z) ⧸ Ideal.span {a}) := by
  algebraize [(f.stalkMap z).hom]
  have hloc : IsLocalHom
      (algebraMap (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  have hflat : Module.Flat (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z) :=
    RingHom.flat_algebraMap_iff.mp (Flat.stalkMap f z)
  have hcrit := ((etaleAt_tfae f z).out 1 7).mp ((etale_iff_forall_etaleAt f).mp ‹Etale f› z)
  have hmax : extendedMaximalIdeal (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z) =
      maximalIdeal (U.presheaf.stalk z) := hcrit.2.1
  have hone : Module.length (U.presheaf.stalk z)
      (U.presheaf.stalk z ⧸
        extendedMaximalIdeal (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z)) = 1 := by
    rw [hmax]
    exact Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
      ⟨maximalIdeal (U.presheaf.stalk z), maximalIdeal.isMaximal (U.presheaf.stalk z),
        ⟨LinearEquiv.refl _ _⟩⟩)
  have hcoe : (f.stalkMap z).hom a =
      algebraMap (V.presheaf.stalk (f.base z)) (U.presheaf.stalk z) a := rfl
  rw [hcoe, length_quotient_span_algebraMap a, hone, mul_one]

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The order of vanishing along an étale morphism -/

/-- **The order of vanishing is unchanged by an étale morphism.** At every point `z` of `U` the
pullback along an étale `f : U ⟶ V` of integral locally Noetherian schemes of a rational function
on `V` vanishes to the same order at `z` as the function does at `f z`. -/
theorem ord_dominantFunctionFieldMap_of_etale {U V : Scheme.{u}} (f : U ⟶ V) [Etale f]
    [IsIntegral U] [IsIntegral V] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    [IsDominant f] (z : U) (g : V.functionField) :
    U.ord (dominantFunctionFieldMap f g) z = V.ord g (f.base z) := by
  by_cases hz : coheight z = 1
  · by_cases hg : g = 0
    · subst hg
      simp
    have hzV : coheight (f.base z) = 1 := (coheight_eq_of_etale f z).trans hz
    obtain ⟨a, b, ha, hb, hrep⟩ := exists_div_algebraMap_stalk_eq (f.base z) hg
    rw [← hrep, ord_dominantFunctionFieldMap_eq_length_sub f hz ha hb,
      ord_div_algebraMap_eq_length_sub hzV ha hb,
      length_quotient_span_stalkMap_of_etale f z a,
      length_quotient_span_stalkMap_of_etale f z b]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz,
      Scheme.ord_eq_zero_of_coheight_neq_one
        (fun h ↦ hz ((coheight_eq_of_etale f z).symm.trans h))]

end Stacks.Chow

end
