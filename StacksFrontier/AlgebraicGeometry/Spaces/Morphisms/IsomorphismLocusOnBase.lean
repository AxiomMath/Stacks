module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenFiltrationSeparatedNeighbourhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The open locus on the base over which a base change is an isomorphism

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`.  If `p` is locally
of finite presentation, flat and universally closed and `q` is locally of finite type, closed
and separated, then there is an open subspace `W` of `Z` through which a morphism `Z' ⟶ Z`
factors exactly when the base change of `f` along it is an isomorphism.  This is
**Stacks 05XD**.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isClosedImmersion_of_isFlat_of_isSurjective`: a surjective
  flat closed immersion of algebraic spaces is an isomorphism.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isIso_baseChange` is **Stacks 05XD**.

## Implementation notes

The open subspace is the intersection of the one of Stacks 05XC, over which the base change is
surjective and flat, with the one of Stacks 05XA, over which it is a closed immersion; the
intersection is formed on point sets through the correspondence of Stacks 03BZ.  What remains
is that a surjective flat closed immersion is an isomorphism and conversely, which is checked
on represented base changes: a closed immersion of schemes is a quasi-compact monomorphism, and
a flat surjective quasi-compact monomorphism of schemes is an isomorphism by Stacks 06NC.

Nothing here is conditional: Stacks 05XC draws on Stacks 05X3,
`AlgebraicGeometry.Space.flatLocusOpenAndStableUnderBaseChange`, which the library proves.

## References

* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
* [Stacks Project, Tag 05XC](https://stacks.math.columbia.edu/tag/05XC)
* [Stacks Project, Tag 05XA](https://stacks.math.columbia.edu/tag/05XA)
* [Stacks Project, Tag 06NC](https://stacks.math.columbia.edu/tag/06NC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullback_presheaf_IsomorphismLocusOnBase
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Isomorphisms among surjective flat closed immersions -/

/-- An isomorphism of algebraic spaces over `S` is surjective on points: the map on points of
its inverse is a section of its map on points. -/
theorem isSurjective_of_isIso (f : X ⟶ Y) [IsIso f] : IsSurjective B S hS f := fun y =>
  ⟨pointsMap B S hS Y (inv f) y, by
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]⟩

/-- **A surjective flat closed immersion of algebraic spaces over `S` is an isomorphism.**

A closed immersion is representable and a monomorphism, so it is injective on sections, and a
section of the target over a site object pulls back to a morphism of schemes which is a closed
immersion — hence a quasi-compact monomorphism — and is flat and surjective.  Such a morphism of
schemes is an isomorphism by Stacks 06NC, and its inverse factors the section. -/
theorem isIso_of_isClosedImmersion_of_isFlat_of_isSurjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hci : IsClosedImmersion B S hS f) (hflat : IsFlat B S hS f)
    (hsurj : IsSurjective B S hS f) :
    IsIso f := by
  have htfae := (closedImmersion_conditions_tfae B S hS hX hY f).out 1 4
  have hmono : Mono f := (htfae.mp hci).2.2
  have hsurj' := (presheafSurjective_iff_isSurjective B S hS hX hY f hci.rep).2 hsurj
  have hflat' := (isFlat_iff_presheaf B S hS hX hY hci.rep).mp hflat
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).mp hmono T), fun x ↦ ?_⟩
  set t : yoneda.obj T.unop ⟶ Y := yonedaEquiv.symm x with ht
  have hpb := hci.rep.isPullback t
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hci.rep.snd t)) := hci.property_snd t
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map (hci.rep.snd t)) :=
    hsurj'.property_snd t
  have _ : _root_.AlgebraicGeometry.Flat
      ((BigFppfOver.toScheme B S hS).map (hci.rep.snd t)) := hflat'.property_snd t
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map (hci.rep.snd t)) :=
    _root_.AlgebraicGeometry.Flat.isIso_of_surjective_of_mono _
  have _ : IsIso (hci.rep.snd t) := isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  refine ⟨yonedaEquiv (inv (yoneda.map (hci.rep.snd t)) ≫ hci.rep.fst t), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, hpb.w, IsIso.inv_hom_id_assoc, ht,
    Equiv.apply_symm_apply]

/-! ### The isomorphism locus on the base, Stacks 05XD -/

/-- **Stacks 05XD.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` whose source and target are given over a third algebraic space `Z` by morphisms
`p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`.  If `p` is locally of finite presentation, flat
and universally closed and `q` is locally of finite type, closed and separated, then there is an
open subspace `W` of `Z` through which a morphism `Z' ⟶ Z` from an algebraic space factors
exactly when the base change of `f` along it is an isomorphism.

The open subspace is the intersection, formed on point sets through the correspondence of
Stacks 03BZ, of the open subspace of Stacks 05XC over which the base change is surjective and
flat with that of Stacks 05XA over which it is a closed immersion.  A surjective flat closed
immersion is an isomorphism, and an isomorphism is surjective, flat and a closed immersion. -/
@[stacks 05XD "the open subspace of the base over which the morphism becomes an isomorphism"]
theorem exists_isOpenSubspace_iff_isIso_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFinitePresentation B S hS p) (hpflat : IsFlat B S hS p)
    (hpuc : UniversallyClosed B S hS p) (hq : IsLocallyOfFiniteType B S hS q)
    (hqc : IsClosedMorphism B S hS q) (hqsep : IsSeparated B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsIso (baseChangeOverBase B S hS f p q hfq g) := by
  obtain ⟨W₁, hW₁, hW₁prop⟩ := exists_isOpenSubspace_iff_isSurjective_isFlat_baseChange
    B S hS hX hY hZ f p q hfq hp hpflat
    (isClosed_of_universallyClosed B S hS hZ p hpuc) hq hqc
  obtain ⟨W₂, hW₂, hW₂prop⟩ := exists_isOpenSubspace_iff_isClosedImmersion_baseChange
    B S hS hX hY hZ f p q hfq
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hp) hpuc hqsep
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hZ
    (Set.range (pointsMap B S hS W₁.toFunctor W₁.ι) ∩
      Set.range (pointsMap B S hS W₂.toFunctor W₂.ι))
    ((isOpen_range_pointsMap_of_isOpenImmersion B S hS W₁.ι hW₁.2).inter
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS W₂.ι hW₂.2))
  refine ⟨W, hWopen, fun Z' hZ' g => ?_⟩
  have hX' : IsAlgebraicSpace B S hS (pullback p g) :=
    isAlgebraicSpace_pullback B S hS p g hX hZ' hZ
  have hY' : IsAlgebraicSpace B S hS (pullback q g) :=
    isAlgebraicSpace_pullback B S hS q g hY hZ' hZ
  have hfactor : (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
      ((∃ r : Z' ⟶ W₁.toFunctor, r ≫ W₁.ι = g) ∧
        ∃ r : Z' ⟶ W₂.toFunctor, r ≫ W₂.ι = g) := by
    rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' W hWopen g,
      factorsThrough_openSubspace_iff_points B S hS hZ hZ' W₁ hW₁ g,
      factorsThrough_openSubspace_iff_points B S hS hZ hZ' W₂ hW₂ g, hWrange,
      Set.subset_inter_iff]
  rw [hfactor, hW₁prop Z' hZ' g, hW₂prop Z' hZ' g]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact isIso_of_isClosedImmersion_of_isFlat_of_isSurjective B S hS hX' hY' _ h.2
      h.1.2 h.1.1
  · have _ : IsIso (baseChangeOverBase B S hS f p q hfq g) := h
    exact ⟨⟨isSurjective_of_isIso B S hS _,
      isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS _)⟩,
      isClosedImmersion_of_isIso B S hS _⟩

end AlgebraicGeometry.Space

end
