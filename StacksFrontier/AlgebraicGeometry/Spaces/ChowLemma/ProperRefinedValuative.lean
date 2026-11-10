module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RefinedValuativeCriterion

/-!
# Properness from the refined valuative criterion

A quasi-compact, quasi-separated morphism of algebraic spaces which is locally of finite type and
satisfies the refined valuative criterion relative to a quasi-compact morphism with dense image is
proper: the criterion gives universal closedness and separatedness, and the two hypotheses give
finite type.

## Main results

* `AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`: a morphism of algebraic
  spaces over `S` which is quasi-compact, quasi-separated and locally of finite type, and which
  satisfies the refined valuative criterion relative to a quasi-compact morphism with dense image,
  is proper.

## References

* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 089G](https://stacks.math.columbia.edu/tag/089G)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Properness from the refined valuative criterion.** Let `f : X ⟶ Y` be a quasi-compact,
quasi-separated morphism of algebraic spaces over `S` which is locally of finite type, and let
`h : U ⟶ X` be quasi-compact with dense image on points. If every valuative square for `f` whose
generic point factors through `h` admits at most one lift, and admits one after a dominating
extension of the valuation ring, then `f` is proper. -/
theorem isProper_of_refinedValuativeCriterion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U)
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (h : U ⟶ X) (f : X ⟶ Y)
    (hf : IsQuasiCompact B S hS f)
    (hh : IsQuasiCompact B S hS h)
    (hqs : IsQuasiSeparated B S hS f)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hdense : letI : TopologicalSpace (AlgebraicGeometry.Space.points B S hS X) :=
        pointTopology B S hS X
      DenseRange (pointsMap B S hS U h))
    (hunique : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Subsingleton q.Lift)
    (hexists : ∀ (q : ValuativeSquare f)
      (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic →
        ∃ e : q.DominatingExtension, Nonempty e.square.Lift) :
    IsProper B S hS f :=
  ⟨isSeparated_of_refinedValuativeCriterion B S hS hU hX hY h f hh hqs hdense hunique hexists,
    ⟨hlft, hf⟩,
    universallyClosed_of_refinedValuativeCriterion B S hS hU hX hY h f hf hh hdense hunique
      hexists⟩

end AlgebraicGeometry.Space

end
