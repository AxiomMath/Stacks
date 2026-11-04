module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType

/-!
# A morphism with one-point image to a rational point of the target

The contraction step of [Stacks, Tag 0AEM] is applied to a closed subvariety `C` of `(ℙ¹_k)^n`
which the given morphism "maps to a point". The library's statements of that step —
`AlgebraicGeometry.Space.exists_isOpenSubspace_forall_isFinite_comp_eq_orbitMap`,
`AlgebraicGeometry.Space.exists_isOpenSubspace_forall_comp_matrixAut_comp_eq_of_factors` and
`AlgebraicGeometry.Space.comp_matrixAut_eq_of_contractedPiece` — read "maps to a point" as the
hypothesis

`hconst : C.ι ≫ f = toBaseFunctor k B hk C.toFunctor ≫ ζ`

for a *rational* point `ζ` of the target, while the extraction
`AlgebraicGeometry.Space.exists_reducedClosedSubspace_pair_ne_of_infinite_fibre` produces only
that the image of `|C|` is contained in one closed point `y` of `|Z|`. This file closes that
gap.

The passage is the theory of residual spaces of
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/ReducedSingleton.lean`. Write `W` for the reduced
closed subspace of `Z` on `{y}`, which is a residual space of `Z` at `y` (Stacks 06R0): it is
reduced, locally Noetherian and has exactly one point. By Stacks 03JJ the morphism factors
through `W`, so a rational point of `C` gives a rational point `a` of `W`. That `a` is a
monomorphism, being split by the structure morphism of `W` to the base, and `W` carries a flat,
surjective, locally finitely presented cover by the spectrum of a field (Stacks 06QX), so
Stacks 06QY makes `a` an *isomorphism*. Hence the structure morphism of `W` is an isomorphism
too, and every morphism into `W` is its own structure morphism followed by `a`.

No algebraic closedness is needed: the field spectrum covering `W` is the one Stacks 06QX
produces, not the base. Local Noetherianity of `Z` is read off local finite type over the
field.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_baseFunctor`: the base,
  read as an algebraic space over itself, is locally Noetherian.
* `AlgebraicGeometry.Space.isIso_rationalPoint_reducedClosedSubspace_singleton`:
  **a rational point of the reduced closed subspace on a closed point is an isomorphism.**
* `AlgebraicGeometry.Space.exists_rationalPoint_comp_eq_of_range_pointsMap_subset_singleton`:
  **a morphism carrying its whole image on points into one closed point of the target, out of a
  reduced algebraic space with a rational point, is that rational point's value** — it is the
  structure morphism to the base followed by a rational point of the target.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 06QX](https://stacks.math.columbia.edu/tag/06QX)
* [Stacks Project, Tag 06QY](https://stacks.math.columbia.edu/tag/06QY)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-- **The base, read as an algebraic space over itself, is locally Noetherian**: it is
represented by the identity of `Spec k` in the site, and the spectrum of a field is locally
Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_baseFunctor :
    HasEtaleLocalProperty B (Spec (CommRingCat.of k)) hk (baseFunctor k B hk)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  hasEtaleLocalProperty_of_representable B (Spec (CommRingCat.of k)) hk _ _
    (Over.mk (𝟙 (B.obj hk))) (Iso.refl _)
    ((AlgebraicGeometry.isLocallyNoetherian_Spec (R := CommRingCat.of k)).2 inferInstance)

variable {Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}

/-- An algebraic space locally of finite type over the base is locally Noetherian, the base
being the spectrum of a field. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z) (z : Z ⟶ baseFunctor k B hk)
    (hz : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk z) :
    HasEtaleLocalProperty B (Spec (CommRingCat.of k)) hk Z
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk hZ
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) z hz
    (hasEtaleLocalProperty_isLocallyNoetherian_baseFunctor k B hk)

/-- **A rational point of the reduced closed subspace on a closed point of a locally Noetherian
algebraic space is an isomorphism.**

The subspace is a residual space at that point (Stacks 06R0), hence reduced, locally Noetherian
and with exactly one point, so Stacks 06QX gives it a flat, surjective, locally finitely
presented cover by the spectrum of a field. A rational point of it is split by its structure
morphism to the base, hence a monomorphism, and Stacks 06QY makes a monomorphism into such a
space either empty or an isomorphism; the point set of the base is nonempty because the point
set of the subspace is. -/
theorem isIso_rationalPoint_reducedClosedSubspace_singleton
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (hN : HasEtaleLocalProperty B (Spec (CommRingCat.of k)) hk Z
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (y : points B (Spec (CommRingCat.of k)) hk Z)
    (hy : IsClosed ({y} : Set (points B (Spec (CommRingCat.of k)) hk Z)))
    (a : baseFunctor k B hk ⟶
      (reducedClosedSubspace B (Spec (CommRingCat.of k)) hk Z hZ {y} hy).toFunctor) :
    IsIso a := by
  obtain ⟨halg, -, hred, hnoeth, hne, hsub, -⟩ :=
    isResidualSpaceAt_ι_reducedClosedSubspace B (Spec (CommRingCat.of k)) hk hZ hN y hy
  have hcover : HasLocallyOfFinitePresentationFlatFieldCover B (Spec (CommRingCat.of k)) hk
      (reducedClosedSubspace B (Spec (CommRingCat.of k)) hk Z hZ {y} hy).toFunctor :=
    (isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover B
      (Spec (CommRingCat.of k)) hk _ halg).1 ⟨hred, hnoeth, hne, hsub⟩
  have : IsSplitMono a :=
    IsSplitMono.mk' ⟨toBaseFunctor k B hk _, (base_isTerminal k B hk).hom_ext _ _⟩
  rcases isEmpty_points_or_isIso_of_mono_of_hasFinitePresentationCover B
    (Spec (CommRingCat.of k)) hk
    (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _) halg a hcover with hempty | hiso
  · exact absurd (Function.isEmpty (pointsMap B (Spec (CommRingCat.of k)) hk _
      (toBaseFunctor k B hk
        (reducedClosedSubspace B (Spec (CommRingCat.of k)) hk Z hZ {y} hy).toFunctor)))
      (not_isEmpty_of_nonempty _)
  · exact hiso

/-- **A morphism out of a reduced algebraic space whose image on points is a single closed
point of the target is constant**, as soon as its source has a rational point: it is the
structure morphism of the source followed by a rational point of the target.

This is the hypothesis `hconst` of the contraction step of [Stacks, Tag 0AEM], obtained from
what the extraction of a contracted piece delivers. By Stacks 03JJ the morphism factors through
the reduced closed subspace `W` on that point; the rational point of the source gives a
rational point `a` of `W`, which is an isomorphism by
`AlgebraicGeometry.Space.isIso_rationalPoint_reducedClosedSubspace_singleton`; so the structure
morphism of `W` is the inverse of `a` and the factoring morphism is the structure morphism of
the source followed by `a`. -/
theorem exists_rationalPoint_comp_eq_of_range_pointsMap_subset_singleton
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ baseFunctor k B hk)
    (hz : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk z)
    {R : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u}
    (hR : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk R)
    (hRred : HasEtaleLocalProperty B (Spec (CommRingCat.of k)) hk R
      (fun T : Scheme.{u} => IsReduced T))
    (h₀ : R ⟶ Z) (y : points B (Spec (CommRingCat.of k)) hk Z)
    (hy : IsClosed ({y} : Set (points B (Spec (CommRingCat.of k)) hk Z)))
    (hrange : Set.range (pointsMap B (Spec (CommRingCat.of k)) hk R h₀) ⊆ {y})
    (l : baseFunctor k B hk ⟶ R) :
    ∃ ζ : baseFunctor k B hk ⟶ Z, h₀ = toBaseFunctor k B hk R ≫ ζ := by
  set W := reducedClosedSubspace B (Spec (CommRingCat.of k)) hk Z hZ {y} hy
  obtain ⟨h, hh⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B
    (Spec (CommRingCat.of k)) hk Z hZ {y} hy hR hRred h₀).2 hrange
  have hiso : IsIso (l ≫ h) :=
    isIso_rationalPoint_reducedClosedSubspace_singleton k B hk hZ
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType_toBase k B hk hZ z hz)
      y hy (l ≫ h)
  refine ⟨(l ≫ h) ≫ W.ι, ?_⟩
  rw [← hh, (base_isTerminal k B hk).hom_ext (toBaseFunctor k B hk R) (h ≫ inv (l ≫ h)),
    Category.assoc h, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
