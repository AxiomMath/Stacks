module

public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite local freeness of a sheaf of modules is local on the base

The pointwise formulation of finite local freeness, which asks that every point of the base
have an open neighbourhood over which the sheaf becomes free on a finite index type, restricts
along open immersions and glues along open covers. Both halves are proved by transporting a
free presentation across a restriction functor, which preserves coproducts and sends the
structure sheaf to the structure sheaf, so it sends a free sheaf to a free sheaf on the same
index type.

The direct image along an isomorphism of schemes is identified with a restriction, so it is
covered by the same two results.

## Main results

* `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.of_iso`: finite local freeness depends
  only on the isomorphism class of a sheaf of modules.
* `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.restrict`: finite local freeness is
  inherited by the restriction along an open immersion.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top`: a sheaf of modules
  whose restriction to each member of an open cover of the base is finite locally free is
  itself finite locally free.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isOpenImmersion_cover`: the same for
  a family of open immersions whose ranges cover the base, the sources being arbitrary schemes
  rather than open subschemes.
* `AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrict`: the direct image along an
  isomorphism of schemes is the restriction along its inverse.
* `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.pushforward_of_iso`: finite local
  freeness is preserved by the direct image along an isomorphism of schemes.

## Implementation notes

The index type of a free presentation is carried through unchanged, which is what makes the
restriction statement a statement about the same index types and hence usable for the
fixed-rank variant as well. Transporting the freeness uses
`AlgebraicGeometry.SheafOfModules.mapFreeIso`; its hypothesis that the functor preserve
`I`-indexed coproducts has to be supplied as an explicit argument, because the category
structure on `AlgebraicGeometry.Scheme.Modules` is a separate instance from the one on
`SheafOfModules` and instance search does not identify the two.

Gluing produces, for a point `x` of the base lying in the member `U` of the cover and an open
`V` of `U` witnessing freeness at `x`, the open `U.ι ''ᵁ V` of the base. Its inclusion and the
composite inclusion of `V` have the same range, so they differ by an isomorphism of schemes,
along which the free presentation is transported.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction along an open immersion of a free sheaf of modules on a finite index type
is free on the same index type. -/
noncomputable def restrictFreeIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (I : Type u) :
    SheafOfModules.free.{u} I ≅ (restrictFunctor g).obj (SheafOfModules.free.{u} I) :=
  haveI hdisc : PreservesColimitsOfShape (Discrete I) (restrictFunctor g) := inferInstance
  @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ (restrictFunctor g) I hdisc
    (restrictUnitIso g).symm

/-- Finite local freeness depends only on the isomorphism class of a sheaf of modules. -/
theorem IsFiniteLocallyFree.of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : IsFiniteLocallyFree M) : IsFiniteLocallyFree N := by
  intro x
  obtain ⟨U, hU, I, hIfin, ⟨ε⟩⟩ := h x
  exact ⟨U, hU, I, hIfin, ⟨((restrictFunctor U.ι).mapIso e).symm ≪≫ ε⟩⟩

/-- Finite local freeness is inherited by the restriction along an open immersion: a free
presentation over an open `U` of the target restricts to one over the preimage of `U`. -/
theorem IsFiniteLocallyFree.restrict {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    {M : Y.Modules} (h : IsFiniteLocallyFree M) : IsFiniteLocallyFree (M.restrict g) := by
  intro x
  obtain ⟨U, hU, I, hIfin, ⟨ε⟩⟩ := h (g.base x)
  refine ⟨g ⁻¹ᵁ U, hU, I, hIfin, ⟨?_⟩⟩
  exact ((restrictFunctorComp (g ⁻¹ᵁ U).ι g).app M).symm ≪≫
    ((restrictFunctorCongr (morphismRestrict_ι g U)).app M).symm ≪≫
    (restrictFunctorComp (g ∣_ U) U.ι).app M ≪≫
    (restrictFunctor (g ∣_ U)).mapIso ε ≪≫ (restrictFreeIso (g ∣_ U) I).symm

/-- If two open immersions into `X` have the same range, the restriction of `M` along the first is
the restriction along the comparison isomorphism of the restriction along the second. -/
private noncomputable def restrictIsoRestrictOfRangeEq {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] (h : Set.range f.base = Set.range g.base)
    (M : X.Modules) :
    M.restrict f ≅ (M.restrict g).restrict (IsOpenImmersion.isoOfRangeEq f g h).hom :=
  (restrictFunctorCongr (IsOpenImmersion.isoOfRangeEq_hom_fac f g h).symm).app M ≪≫
    (restrictFunctorComp (IsOpenImmersion.isoOfRangeEq f g h).hom g).app M

/-- A sheaf of modules whose restriction to each member of an open cover of the base is finite
locally free is itself finite locally free. -/
theorem isFiniteLocallyFree_of_iSup_eq_top {X : Scheme.{u}} {M : X.Modules} {ι : Type*}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, IsFiniteLocallyFree (M.restrict (U i).ι)) : IsFiniteLocallyFree M := by
  intro x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU ▸ trivial : x ∈ (⨆ i, U i : X.Opens))
  obtain ⟨V, hV, I, hIfin, ⟨ε⟩⟩ := h i ⟨x, hi⟩
  refine ⟨(U i).ι ''ᵁ V, ⟨⟨x, hi⟩, hV, rfl⟩, I, hIfin, ⟨?_⟩⟩
  have hrange : Set.range ((U i).ι ''ᵁ V).ι = Set.range (V.ι ≫ (U i).ι) := by
    simp [Set.range_comp]
  exact restrictIsoRestrictOfRangeEq ((U i).ι ''ᵁ V).ι (V.ι ≫ (U i).ι) hrange M ≪≫
    (restrictFunctor
      (IsOpenImmersion.isoOfRangeEq ((U i).ι ''ᵁ V).ι (V.ι ≫ (U i).ι) hrange).hom).mapIso
      ((restrictFunctorComp V.ι (U i).ι).app M ≪≫ ε) ≪≫
    (restrictFreeIso _ I).symm

/-- **A sheaf of modules whose restriction along each member of a family of open immersions
covering the base is finite locally free is itself finite locally free.** Each member has the
same range as the inclusion of that range as an open subscheme, so the two sources are
isomorphic over the base and the two restrictions are carried to one another; the previous
result then applies to the family of ranges. -/
theorem isFiniteLocallyFree_of_isOpenImmersion_cover {X : Scheme.{u}} {M : X.Modules}
    {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hg : ⨆ i, (g i).opensRange = ⊤)
    (h : ∀ i, IsFiniteLocallyFree (M.restrict (g i))) : IsFiniteLocallyFree M := by
  refine isFiniteLocallyFree_of_iSup_eq_top (fun i => (g i).opensRange) hg fun i => ?_
  have hrange : Set.range ((g i).opensRange).ι.base = Set.range (g i).base :=
    Scheme.Opens.range_ι _
  exact IsFiniteLocallyFree.of_iso
    (restrictIsoRestrictOfRangeEq ((g i).opensRange).ι (g i) hrange M).symm
    ((h i).restrict _)

/-- The direct image of a sheaf of modules along an isomorphism of schemes is the restriction
along the inverse isomorphism. -/
noncomputable def pushforwardIsoRestrict {S S' : Scheme.{u}} (e : S ≅ S') (N : S.Modules) :
    (pushforward e.hom).obj N ≅ N.restrict e.inv :=
  ((restrictFunctorAdjCounitIso e.inv).app ((pushforward e.hom).obj N)).symm ≪≫
    (restrictFunctor e.inv).mapIso ((pushforwardComp e.hom e.inv).app N ≪≫
      (pushforwardCongr e.hom_inv_id).app N ≪≫ (pushforwardId S).app N)

/-- Finite local freeness is preserved by the direct image along an isomorphism of schemes. -/
theorem IsFiniteLocallyFree.pushforward_of_iso {S S' : Scheme.{u}} (e : S ≅ S')
    {N : S.Modules} (h : IsFiniteLocallyFree N) :
    IsFiniteLocallyFree ((pushforward e.hom).obj N) :=
  .of_iso (pushforwardIsoRestrict e N).symm (h.restrict e.inv)

end AlgebraicGeometry.Scheme.Modules

end
