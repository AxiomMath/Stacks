module

public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# Fractions in the sheaf of total quotient rings

Let `O` be a sheaf of commutative rings on a topological space. Its sheaf of total quotient
rings `K` is the sheafification of the presheaf which localizes the sections over an open set
at those sections whose germs are everywhere nonzerodivisors. Three consequences of that
description are proved here, for an arbitrary space: such a section becomes a unit of `K`,
every section of `K` is locally a fraction of sections of `O` with such a denominator, and
`O` embeds in `K` on the sections over every open set.

## Main results

* `AlgebraicGeometry.isUnit_toTotalQuotientSheaf_app`: a section of `O` whose germ at every
  point of its domain is a nonzerodivisor has a unit image in `K`.
* `AlgebraicGeometry.exists_nhds_mul_toTotalQuotientSheaf_app_eq`: every section of `K` is,
  near each point, a fraction `a / b` of sections of `O` whose denominator becomes a unit.
* `Stacks.SheafifyMono.injective_toTotalQuotientSheaf_app`: the canonical map from the
  structure sheaf to the sheaf of total quotient rings is injective on sections over every open
  set.

## References

* [Stacks Project, Tag 01X2](https://stacks.math.columbia.edu/tag/01X2)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)

/-- Over each open `V`, the total quotient presheaf is the localization of the sections of `O`
at those whose germs are nonzerodivisors: such sections become units and every section is a
fraction. -/
private theorem units_and_fractions_toTotalQuotientPresheaf (V : Opens X) :
    (∀ b ∈ (O.presheaf.submonoidPresheafOfStalk
        fun y => nonZeroDivisors ↑(O.presheaf.stalk y)).obj (op V),
      IsUnit ((O.presheaf.toTotalQuotientPresheaf.app (op V)).hom b)) ∧
    ∀ t : O.presheaf.totalQuotientPresheaf.obj (op V),
      ∃ a b : O.presheaf.obj (op V),
        b ∈ (O.presheaf.submonoidPresheafOfStalk
          fun y => nonZeroDivisors ↑(O.presheaf.stalk y)).obj (op V) ∧
        t * (O.presheaf.toTotalQuotientPresheaf.app (op V)).hom b =
          (O.presheaf.toTotalQuotientPresheaf.app (op V)).hom a := by
  set S := O.presheaf.submonoidPresheafOfStalk
    fun y => nonZeroDivisors ↑(O.presheaf.stalk y) with hS
  let : Algebra ↑(O.presheaf.obj (op V)) ↑(O.presheaf.totalQuotientPresheaf.obj (op V)) := by
    change Algebra _ (Localization (S.obj (op V)))
    infer_instance
  let : IsLocalization (S.obj (op V)) ↑(O.presheaf.totalQuotientPresheaf.obj (op V)) := by
    change IsLocalization _ (Localization (S.obj (op V)))
    infer_instance
  refine ⟨fun b hb => IsLocalization.map_units (M := S.obj (op V))
    ↑(O.presheaf.totalQuotientPresheaf.obj (op V)) ⟨b, hb⟩, fun t => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (S.obj (op V)) t
  exact ⟨a, b.1, b.2, hab⟩

/-- A section of `O` over `V` whose germ at every point of `V` is a nonzerodivisor has a unit
image in the sheaf of total quotient rings over `V`. -/
theorem isUnit_toTotalQuotientSheaf_app (V : Opens X) (b : O.presheaf.obj (op V))
    (hb : ∀ (y : X) (hy : y ∈ V),
      O.presheaf.germ V y hy b ∈ nonZeroDivisors ↑(O.presheaf.stalk y)) :
    IsUnit ((toTotalQuotientSheaf O).hom.app (op V) b) := by
  refine ((units_and_fractions_toTotalQuotientPresheaf O V).1 b ?_).map
    ((toSheafify (Opens.grothendieckTopology X)
      O.presheaf.totalQuotientPresheaf).app (op V)).hom
  simp only [TopCat.Presheaf.submonoidPresheafOfStalk_obj, Submonoid.mem_iInf,
    Submonoid.mem_comap]
  exact fun y => hb y.1 y.2

/-- **Every section of the sheaf of total quotient rings is locally a fraction.** Given a
section `c` over `U` and a point of `U`, there is a neighbourhood `V ≤ U` of that point and
sections `a` and `b` of `O` over `V` with `c · b = a` there, the image of `b` being a unit. -/
theorem exists_nhds_mul_toTotalQuotientSheaf_app_eq (U : Opens X)
    (c : (totalQuotientSheaf O).presheaf.obj (op U)) {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧ ∃ a b : O.presheaf.obj (op V),
      IsUnit ((toTotalQuotientSheaf O).hom.app (op V) b) ∧
        (totalQuotientSheaf O).presheaf.map (homOfLE hVU).op c *
            (toTotalQuotientSheaf O).hom.app (op V) b =
          (toTotalQuotientSheaf O).hom.app (op V) a := by
  classical
  have hls := CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) O.presheaf.totalQuotientPresheaf) (U := op U) c
  rw [Opens.mem_grothendieckTopology] at hls
  obtain ⟨V, g, ⟨t, ht⟩, hxV⟩ := hls x hx
  obtain ⟨a, b, hbS, hab⟩ :=
    ((units_and_fractions_toTotalQuotientPresheaf O V).2 t)
  refine ⟨V, g.le, hxV, a, b, ?_, ?_⟩
  · exact ((units_and_fractions_toTotalQuotientPresheaf O V).1 b hbS).map
      ((toSheafify (Opens.grothendieckTopology X)
        O.presheaf.totalQuotientPresheaf).app (op V)).hom
  · have hcarrier : (totalQuotientSheaf O).presheaf.map (homOfLE g.le).op c =
        ((toSheafify (Opens.grothendieckTopology X)
          O.presheaf.totalQuotientPresheaf).app (op V)).hom t := ht.symm
    rw [hcarrier]
    exact (((toSheafify (Opens.grothendieckTopology X)
      O.presheaf.totalQuotientPresheaf).app (op V)).hom.map_mul _ _).symm.trans
      (congrArg _ hab)

end AlgebraicGeometry

namespace Stacks.SheafifyMono

open AlgebraicGeometry

variable {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)

/-- **A sheaf of rings embeds in its sheaf of total quotient rings, on sections.** The canonical
map from `O` to its sheaf of total quotient rings is injective on sections over every open set. -/
theorem injective_toTotalQuotientSheaf_app (U : Opens X) :
    Function.Injective (((toTotalQuotientSheaf O).hom.app (op U)).hom) := by
  have hstalk : ∀ x : X, Function.Injective (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (toTotalQuotientSheaf O).hom).hom) := by
    intro x
    have h₁ : Function.Injective (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        O.presheaf.toTotalQuotientPresheaf).hom) := by
      apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      intro V
      have hm : Mono ((O.presheaf.toTotalQuotientPresheaf).app (op V)) :=
        (NatTrans.mono_iff_mono_app O.presheaf.toTotalQuotientPresheaf).mp
          (inferInstance : Mono O.presheaf.toTotalQuotientPresheaf) (op V)
      exact ConcreteCategory.injective_of_mono_of_preservesPullback _
    have h₂ : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          O.presheaf.totalQuotientPresheaf)) :=
      TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat _
    have hfac : (TopCat.Presheaf.stalkFunctor CommRingCat x).map (toTotalQuotientSheaf O).hom =
        (TopCat.Presheaf.stalkFunctor CommRingCat x).map O.presheaf.toTotalQuotientPresheaf ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat x).map
            (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
              O.presheaf.totalQuotientPresheaf) := by
      rw [← Functor.map_comp]
      rfl
    have h₁m : Mono ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        O.presheaf.toTotalQuotientPresheaf) := ConcreteCategory.mono_of_injective _ h₁
    rw [hfac]
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp (mono_comp _ _)
  exact (TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective
    (toTotalQuotientSheaf O).hom).mp hstalk U

end Stacks.SheafifyMono
