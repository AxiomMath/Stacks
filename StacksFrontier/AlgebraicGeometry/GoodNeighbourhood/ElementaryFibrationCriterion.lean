module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.ElementaryFibration
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingDivisorOneStepReduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# A criterion for an elementary fibration

Let `T` be a normal integral scheme, smooth over a field `k`, with generic point `η`, and let
`π : X̄ ⟶ T` be projective and smooth of relative dimension `1` with geometrically irreducible
generic fibre. If `j : U ⟶ X̄` is an open immersion whose complement carries a reduced closed
subscheme `Z` étale over `T`, and `Z` is nonempty, then `j ≫ π : U ⟶ T` is an elementary
fibration (`AlgebraicGeometry.IsElementaryFibration`).

Two of the conditions of the definition are not assumed and are proved:

* *every* fibre of `π` is geometrically irreducible. By Zariski's connectedness theorem in the
  form of [Stacks, Tag 0AY8], a proper morphism from a reduced scheme to a normal integral scheme
  whose generic fibre has `H⁰ = κ(η)` has geometrically connected fibres. Here `X̄` is reduced,
  being smooth over `k`; its generic points lie over `η`, `π` being flat; and `H⁰ = κ(η)` on the
  generic fibre by [Stacks, Tag 0BUG] (8), the generic fibre being geometrically integral (smooth
  and geometrically irreducible). A smooth, geometrically connected morphism is geometrically
  irreducible.
* `Z ⟶ T` is finite and surjective. It is proper and étale, hence locally quasi-finite, hence
  finite ([Stacks, Tag 02OG]); its image is closed (finite) and open (flat of finite
  presentation), hence all of the connected `T`, as `Z` is nonempty.

This is the last step of the proof of SGA 4, Exposé XI, Proposition 3.3.

## Main results

* `AlgebraicGeometry.isElementaryFibration_of_smoothOfRelativeDimension_of_etale`.

## References

* SGA 4, Tome 3, Exposé XI, Définition 3.1 and Proposition 3.3.
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A criterion for an elementary fibration.** Let `T` be a normal integral scheme, smooth over
a field `k`, and let `π : X̄ ⟶ T` be projective and smooth of relative dimension `1` with
geometrically irreducible generic fibre. Let `j : U ⟶ X̄` be an open immersion and `i : Z ⟶ X̄`
a reduced closed subscheme with support the complement of the image of `j`, nonempty and étale
over `T`. Then `j ≫ π` is an elementary fibration. -/
theorem isElementaryFibration_of_smoothOfRelativeDimension_of_etale (k : Type u) [Field k]
    {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) [IsIntegral T] [IsNormal T] [Smooth τ]
    {Xt : Scheme.{u}} (π : Xt ⟶ T) (hπ : IsProjectiveMorphism π) [SmoothOfRelativeDimension 1 π]
    (hgi : GeometricallyIrreducible (π.fiberToSpecResidueField (genericPoint T)))
    {U : Scheme.{u}} (j : U ⟶ Xt) [IsOpenImmersion j]
    {Z : Scheme.{u}} (i : Z ⟶ Xt) [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i.base = (Set.range j.base)ᶜ) [Etale (i ≫ π)] [Nonempty Z] :
    IsElementaryFibration (j ≫ π) := by
  have : IsProper π := isProper_of_isProjectiveMorphism π hπ
  have : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  -- every fibre of `π` is geometrically irreducible, by Tag 0AY8
  have : IsReduced Xt :=
    Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field k (π ≫ τ)
  have hgen : ∀ x : Xt, x ∈ genericPoints Xt → π x = genericPoint T := fun x hx => by
    have h := mem_genericPoints_of_flat π hx
    rwa [genericPoints_eq_singleton] at h
  have hΓ : IsIso ((Scheme.ΓSpecIso (T.residueField (genericPoint T))).inv ≫
      (π.fiberToSpecResidueField (genericPoint T)).appTop) := by
    have hsm : Smooth (π.fiberToSpecResidueField (genericPoint T)) :=
      inferInstanceAs (Smooth (pullback.snd π (T.fromSpecResidueField (genericPoint T))))
    have hint : GeometricallyIntegral (π.fiberToSpecResidueField (genericPoint T)) :=
      @Stacks.AbelMap.geometricallyIntegral_of_smooth _ _ _ _ hgi hsm
    have hpr : IsProper (π.fiberToSpecResidueField (genericPoint T)) := inferInstance
    exact @isIso_globalSections_of_geometricallyIntegral _ _ _ _ hint hpr
  have hgc := Stacks.SteinFactorization.geometricallyConnected_of_isNormal π hgen hΓ
  have hgi' : GeometricallyIrreducible π :=
    geometricallyIrreducible_of_geometricallyConnected_of_smooth π hgc
  -- the boundary is finite, étale and surjective
  have : IsFinite (i ≫ π) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have hsurj : Surjective (i ≫ π) := by
    refine ⟨fun t => ?_⟩
    have hclopen : IsClopen (Set.range (i ≫ π).base) :=
      ⟨(i ≫ π).isClosedMap.isClosed_range, (i ≫ π).isOpenMap.isOpen_range⟩
    have h := hclopen.eq_univ (Set.range_nonempty _)
    have ht : t ∈ Set.range (i ≫ π).base := h ▸ Set.mem_univ t
    exact ht
  exact ⟨⟨Xt, Z, j, π, i, inferInstance, rfl, inferInstance, hπ, hgi', inferInstance,
    inferInstance, hZ, inferInstance, inferInstance, hsurj⟩⟩

end AlgebraicGeometry

end
