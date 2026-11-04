module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullExtension

/-!
# Uniqueness of the extension of a generic map to the reflexive hull

Let `X` be an integral scheme with generic point `η`.  A section of a torsion-free
quasi-coherent `𝒪_X`-module is determined by its germ at `η`, and a module has no nonzero
sections over an open set avoiding `η`.  Consequently a morphism of `𝒪_X`-modules whose target
is torsion free is determined by the map it induces on the stalks at `η`.

On an integral locally Noetherian normal scheme the reflexive hull `ℱ^∨∨` of a coherent module
is reflexive, hence torsion free, so the extension of a linear map of generic stalks provided by
[Stacks, Tag 0AY7] is unique.

## Main results

* `AlgebraicGeometry.subsingleton_sections_of_notMem_genericPoint`: an open set missing the
  generic point carries no nonzero sections.
* `AlgebraicGeometry.injective_generic_germ_of_isTorsionFree`: a section of a torsion-free
  quasi-coherent module is determined by its germ at the generic point.
* `AlgebraicGeometry.hom_ext_of_generic_stalkFunctor_map_eq`: a morphism into a torsion-free
  quasi-coherent module is determined by the induced map of generic stalks.
* `AlgebraicGeometry.isTorsionFree_reflexiveHull`: the reflexive hull of a coherent module is
  torsion free.
* `AlgebraicGeometry.existsUnique_lift_toReflexiveHull_of_codimension_one`: the extension of a
  linear map of generic stalks to a map into the reflexive hull exists and is unique.

## References

* [Stacks Project, Tag 0AY7](https://stacks.math.columbia.edu/tag/0AY7)
* [Stacks Project, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveEquivalence
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- On an integral scheme a module has at most one section over an open set that misses the
generic point. -/
alias subsingleton_sections_of_notMem_genericPoint := subsingleton_sections_of_not_generic_mem

/-- A section of a torsion-free quasi-coherent module on an integral scheme is determined by
its germ at the generic point. -/
theorem injective_generic_germ_of_isTorsionFree [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent] (hF : IsTorsionFree F) {U : X.Opens}
    (hη : genericPoint X ∈ U) :
    Function.Injective (F.presheaf.germ U (genericPoint X) hη) := by
  have : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  intro a b hab
  apply sub_eq_zero.mp
  refine hF U _ ((torsion_section_tfae X F U (a - b)).out 3 2 |>.mp ?_)
  simpa only [map_sub, sub_eq_zero] using hab

/-- A morphism of `𝒪_X`-modules on an integral scheme whose target is torsion free and
quasi-coherent is determined by the map it induces on the stalks at the generic point. -/
theorem hom_ext_of_generic_stalkFunctor_map_eq [IsIntegral X] {F G : X.Modules}
    [F.IsQuasicoherent] (hF : IsTorsionFree F) (e₁ e₂ : G ⟶ F)
    (h : ∀ m : G.presheaf.stalk (genericPoint X),
      ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X) e₁)) m =
        ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X) e₂)) m) :
    e₁ = e₂ := by
  refine Scheme.Modules.hom_ext_iff.mpr fun U ↦ ?_
  by_cases hη : genericPoint X ∈ U
  · ext m
    apply injective_generic_germ_of_isTorsionFree F hF hη
    have key : ∀ e : G ⟶ F,
        F.presheaf.germ U (genericPoint X) hη (Scheme.Modules.Hom.app e U m) =
          ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
            (Scheme.Modules.Hom.mapPresheaf (X := X) e))
            (G.presheaf.germ U (genericPoint X) hη m) := fun e ↦ by
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, Scheme.Modules.mapPresheaf_app]
    rw [key e₁, key e₂, h]
  · have := subsingleton_sections_of_notMem_genericPoint F U hη
    ext m
    exact Subsingleton.elim _ _

/-- The reflexive hull of a coherent module on an integral locally Noetherian scheme is
torsion free. -/
theorem isTorsionFree_reflexiveHull (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] : IsTorsionFree (reflexiveHull F) :=
  isTorsionFree_of_isReflexive _ (isReflexive_reflexiveHull X F)

/-- On an integral locally Noetherian normal scheme, a linear map of generic stalks whose values
at every point of codimension one stay inside the image of the target stalk extends to a map into
the reflexive hull of its target in exactly one way. -/
theorem existsUnique_lift_toReflexiveHull_of_codimension_one (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G]
    (T : (G.presheaf.stalk (genericPoint X)) →ₗ[X.functionField]
      (F.presheaf.stalk (genericPoint X)))
    (hT : ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      let h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
      Set.MapsTo T (Set.range (G.presheaf.stalkSpecializes h))
        (Set.range (F.presheaf.stalkSpecializes h))) :
    ∃! e : G ⟶ reflexiveHull F,
      ∀ m : G.presheaf.stalk (genericPoint X),
        ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
          (Scheme.Modules.Hom.mapPresheaf (X := X) e)) m =
          ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
            (Scheme.Modules.Hom.mapPresheaf (X := X)
              (toReflexiveHull F).1)) (T m) := by
  have hcoh : _root_.SheafOfModules.IsCoherent (reflexiveHull F) := isCoherent_doubleDual F
  have : (reflexiveHull F).IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  obtain ⟨e, he⟩ :=
    (exists_lift_toReflexiveHull_iff_codimension_one X F G T).mpr hT
  exact ⟨e, he, fun e' he' ↦ hom_ext_of_generic_stalkFunctor_map_eq
    (isTorsionFree_reflexiveHull X F) e' e fun m ↦ (he' m).trans (he m).symm⟩

end AlgebraicGeometry

end
