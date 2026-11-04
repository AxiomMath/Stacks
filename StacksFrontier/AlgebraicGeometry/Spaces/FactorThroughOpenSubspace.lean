module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# Factoring a morphism through an open subspace (Stacks 03IE)

A morphism of algebraic spaces over `S` factors through an open subspace of its target exactly
when every point of its source maps into the set of points of that open subspace.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points`: **Stacks 03IE**.

## Implementation notes

The set of points of an open subspace is the range of the map on points induced by its
inclusion, so the right-hand side is the containment of images of point sets; the left-hand
side records the factorization as a morphism of presheaves on the big fppf site of `S`.

The forward implication is functoriality of the point map. For the converse, let `P` be the
fibre product of `f : Y ⟶ X` with the inclusion of the open subspace `U`. Its projection
`p : P ⟶ Y` is an open immersion by Tag 02YW, hence a monomorphism, and the hypothesis plus
Tag 03H4 make it surjective on points; so the range of `p` and the whole of `Y` are two open
subspaces of `Y` with the same point set, and the order isomorphism of Tag 03BZ identifies
them. Therefore `p` is epi as well as mono, hence an isomorphism, and the factorization is
`p⁻¹` followed by the second projection.

## References

* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A morphism of algebraic spaces factors through an open subspace if and only
if its map on points has image in the point set of that subspace. -/
@[stacks 03IE]
theorem factorsThrough_openSubspace_iff_points
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (f : Y ⟶ X) :
    (∃ g : Y ⟶ U.toFunctor, g ≫ U.ι = f) ↔
      (Set.range (pointsMap B S hS Y f) ⊆
        Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
  constructor
  · rintro ⟨g, rfl⟩ z ⟨y, rfl⟩
    exact ⟨pointsMap B S hS Y g y, (congrFun (pointsMap_comp B S hS _ g U.ι) y).symm⟩
  · intro hpoints
    let Xₒ : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Yₒ : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Uₒ : AlgebraicSpaces B S hS := ⟨U.toFunctor, hU.1⟩
    let fₒ : Yₒ ⟶ Xₒ := ObjectProperty.homMk f
    let iₒ : Uₒ ⟶ Xₒ := ObjectProperty.homMk U.ι
    let P : AlgebraicSpaces B S hS :=
      AlgebraicSpaces.fiberProduct B S hS fₒ iₒ
    let p : P ⟶ Yₒ := ObjectProperty.homMk (pullback.fst f U.ι)
    let q : P ⟶ Uₒ := ObjectProperty.homMk (pullback.snd f U.ι)
    have sq : IsPullback p q fₒ iₒ :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS fₒ iₒ
    have hpOpen : IsOpenImmersion B S hS p.hom :=
      isOpenImmersion_of_isPullback B S hS sq.flip hU.2
    have hpMono : Mono p.hom := mono_of_isOpenImmersion B S hS p.hom hpOpen
    let V : Subfunctor Y := Subfunctor.range p.hom
    have hV : IsOpenSubspace B S hS V := by
      refine ⟨AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
        (asIso (Subfunctor.toRange p.hom)).symm P.property, ?_⟩
      have h : IsOpenImmersion B S hS ((asIso (Subfunctor.toRange p.hom)).inv ≫ p.hom) :=
        MorphismProperty.RespectsIso.precomp _ _ p.hom hpOpen
      rwa [(Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι p.hom).symm] at h
    have hrange : Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      obtain ⟨x, hx⟩ := hpoints (Set.mem_range.mpr ⟨y, rfl⟩)
      obtain ⟨w, hw₁, -⟩ := exists_point_of_isPullback B S hS sq y x hx.symm
      refine ⟨pointsMap B S hS P.1 (Subfunctor.toRange p.hom) w,
        (congrFun (pointsMap_comp B S hS _ (Subfunctor.toRange p.hom) V.ι) w).symm.trans ?_⟩
      rwa [Subfunctor.toRange_ι]
    have hVtop : V = ⊤ := by
      let : TopologicalSpace (points B S hS Y) := pointTopology B S hS Y
      have h : (⟨V, hV⟩ : {G : Subfunctor Y // IsOpenSubspace B S hS G}) =
          ⟨⊤, isOpenSubspace_top hY⟩ := by
        apply (openSubspacesOrderIso B S hS Y hY).injective
        apply SetLike.coe_injective
        show Set.range (pointsMap B S hS V.toFunctor V.ι) =
          Set.range (pointsMap B S hS (⊤ : Subfunctor Y).toFunctor (⊤ : Subfunctor Y).ι)
        rw [hrange, (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor Y).ι).range_eq]
      exact congrArg Subtype.val h
    have hpEpi : Epi p.hom := (Subfunctor.epi_iff_range_eq_top p.hom).2 hVtop
    have : IsIso p := (ObjectProperty.isIso_hom_iff p).1 (isIso_of_mono_of_epi p.hom)
    have hgₒ : (inv p ≫ q) ≫ iₒ = fₒ := by
      rw [Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc]
    exact ⟨(inv p ≫ q).hom, congrArg (·.hom) hgₒ⟩

end AlgebraicGeometry.Space

end
