module

public import Mathlib.RingTheory.Artinian.Ring
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubobject
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhood

/-!
# Morphisms into the infinitesimal neighbourhoods of a closed subspace

Let `X` be an algebraic space over a scheme `S`, let `Z ⊆ X` be a closed subspace, and let
`Zₙ ⊆ X` be its `n`th order infinitesimal neighbourhood, built on a surjective étale chart
`φ : U ⟶ X` from a sheaf of ideals `J ⊆ 𝒪_U` invariant under the relation `U ×_X U` and
cutting out `Z`, as in `AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood`.

Two things are proved. First, every closed subspace of `X` is presented in this way on every
surjective étale chart, so the infinitesimal neighbourhoods of the library are those of an
arbitrary closed subspace. Second, a morphism `β : T ⟶ X` from a scheme factors through `Zₙ`
as soon as the `(n + 1)`st power of the ideal sheaf of the base change `Z ×_X T ⊆ T` vanishes;
in particular a morphism from the spectrum of an Artinian local ring whose closed point maps
into `Z` factors through some `Zₙ`. That is the step "the maximal ideal of `B'` is nilpotent
(as `B'` is Artinian) and hence the morphism `β` factors through `Zₙ`" of Stacks 0APQ.

## Main results

* `AlgebraicGeometry.Space.exists_isInvariantIdealSheaf_invariantSubspace_eq`: **every closed
  subspace is cut out on a surjective étale chart by an invariant sheaf of ideals**, namely the
  ideal sheaf of its base change to the chart.
* `AlgebraicGeometry.Space.ker_rep_snd_eq_of_invariantSubspace_eq`: that sheaf of ideals is
  the only one cutting out the closed subspace.
* `AlgebraicGeometry.Space.mem_nthOrderInfinitesimalNeighbourhood_of_ker_pow_eq_bot`: a
  morphism from a scheme along which the ideal sheaf of `Z` has vanishing `(n + 1)`st power
  lands in `Zₙ`.
* `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_succ_eq_bot_of_isArtinianRing`: a proper
  sheaf of ideals on the spectrum of an Artinian local ring is nilpotent.
* `AlgebraicGeometry.Space.exists_mem_nthOrderInfinitesimalNeighbourhood_of_isArtinianRing`:
  a morphism from the spectrum of an Artinian local ring whose closed point lies over a point
  of `Z` lands in some `Zₙ`.

## Implementation notes

The vanishing of the power is tested on every lift `k : T' ⟶ U` of a restriction of `β`, which
is what membership in `AlgebraicGeometry.Space.invariantSubspace` asks for. The inverse image of
`J` along `k` is the ideal sheaf of the base change of `Z` along `k ≫ φ`, by
`AlgebraicGeometry.Space.schemeKer_snd_comp`, and since `k ≫ φ` is a restriction of `β` it is
the inverse image of the ideal sheaf of `Z ×_X T` along `T' ⟶ T`; inverse images of ideal
sheaves commute with powers, `Stacks.IdealSheaf.comap_pow`.

## References

* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
* [Stacks Project, Tag 0APQ](https://stacks.math.columbia.edu/tag/0APQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A proper sheaf of ideals on the spectrum of an Artinian local ring is nilpotent.** Its
ideal of global sections lies in the maximal ideal, which is nilpotent. -/
theorem Scheme.IdealSheafData.exists_pow_succ_eq_bot_of_isArtinianRing {T : Scheme.{u}}
    {R : CommRingCat.{u}} [IsLocalRing R] [IsArtinianRing R] (e : T ≅ Spec R)
    (I : T.IdealSheafData) (hI : I ≠ ⊤) : ∃ n : ℕ, I ^ (n + 1) = ⊥ := by
  have : IsAffine T := IsAffine.of_isIso e.hom
  let ρ : Γ(T, ⊤) ≃+* R :=
    (Scheme.Γ.mapIso e.op).symm.commRingCatIsoToRingEquiv.trans
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  set I₀ := I.ideal ⟨⊤, isAffineOpen_top T⟩ with hI₀
  have hI₀top : I₀ ≠ ⊤ := fun h =>
    hI (Scheme.IdealSheafData.ext_of_isAffine (by rw [← hI₀, h]; rfl))
  have hmap : I₀.map ρ ≠ ⊤ := by
    intro h
    apply hI₀top
    have := congrArg (Ideal.comap ρ) h
    rwa [Ideal.comap_map_of_bijective ρ ρ.bijective, Ideal.comap_top] at this
  refine ⟨N, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  show I₀ ^ (N + 1) = ⊥
  refine (Ideal.map_eq_bot_iff_of_injective ρ.injective).mp ?_
  rw [Ideal.map_pow, eq_bot_iff]
  calc I₀.map ρ ^ (N + 1) ≤ IsLocalRing.maximalIdeal R ^ (N + 1) :=
        Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hmap) _
    _ ≤ IsLocalRing.maximalIdeal R ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
    _ = ⊥ := by rw [hN, Ideal.zero_eq_bot]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

/-- The subobject cut out by an ideal sheaf of a scheme of the site is an immersion. -/
private theorem isImmersion_arrow_mk_subschemeι {U : BigFppfOver B S hS}
    (K : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) :
    AlgebraicGeometry.IsImmersion (Subobject.mk K.subschemeι).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

include hs in
/-- **The invariant sheaf of ideals cutting out a closed subspace on a chart is unique**: it is
the ideal sheaf of the base change of the closed subspace to the chart. -/
theorem ker_rep_snd_eq_of_invariantSubspace_eq (Z : ClosedSubspaces B S hS X.1)
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J)
    (hZJ : invariantSubspace B S hS φ (Subobject.mk J.subschemeι) = Z.1) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)).ker = J := by
  refine Scheme.IdealSheafData.subobject_mk_subschemeι_inj.1
    (subschemePoints_injective B S hS (isImmersion_arrow_mk_subschemeι B S hS _)
      (isImmersion_arrow_mk_subschemeι B S hS _) ?_)
  rw [subschemePoints_mk_ker_rep_snd B S hS Z.1 Z.2.2 φ, ← hZJ,
    preimage_invariantSubspace B S hS hs _
      (isInvariantSubscheme_of_isInvariantIdealSheaf B S hS hs hJ)]

include hs he in
/-- **Every closed subspace is cut out on a surjective étale chart by an invariant sheaf of
ideals.** For a closed subspace `Z ⊆ X` and a surjective étale chart `φ : U ⟶ X`, the ideal sheaf
of the base change `Z ×_X U ⊆ U` is invariant under the relation `U ×_X U` and cuts out `Z`, so
the infinitesimal neighbourhoods `AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood` of
Stacks 05ZV are available for every closed subspace. -/
theorem exists_isInvariantIdealSheaf_invariantSubspace_eq (Z : ClosedSubspaces B S hS X.1) :
    ∃ J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData,
      IsInvariantIdealSheaf B S hS hs J ∧
        invariantSubspace B S hS φ (Subobject.mk J.subschemeι) = Z.1 := by
  obtain ⟨W, ⟨hWim, hWinv⟩, hWZ⟩ := exists_invariantSubspace_eq B S hS hs he X.2 Z.1
    (isLocallyClosedSubspace_of_isClosedSubspace Z.1 Z.2)
  have hW : W = Subobject.mk
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd φ)).ker.subschemeι := by
    refine subschemePoints_injective B S hS hWim (isImmersion_arrow_mk_subschemeι B S hS _) ?_
    rw [subschemePoints_mk_ker_rep_snd B S hS Z.1 Z.2.2 φ, ← hWZ,
      preimage_invariantSubspace B S hS hs W hWinv]
  subst hW
  refine ⟨_, ?_, hWZ⟩
  rw [IsInvariantSubscheme, Scheme.IdealSheafData.pullback_subobject_mk_subschemeι,
    Scheme.IdealSheafData.pullback_subobject_mk_subschemeι] at hWinv
  exact Scheme.IdealSheafData.subobject_mk_subschemeι_inj.1 hWinv

include hs in
/-- **A morphism along which the ideal of a closed subspace has vanishing `(n + 1)`st power
lands in the `n`th infinitesimal neighbourhood.** Let `Z ⊆ X` be cut out on the chart `φ` by
the invariant sheaf of ideals `J`, and let `β : T ⟶ X` be a morphism from an object of the site.
If the `(n + 1)`st power of the ideal sheaf of the base change `Z ×_X T ⊆ T` vanishes, then `β`
is a section of the `n`th order infinitesimal neighbourhood of `Z`. -/
theorem mem_nthOrderInfinitesimalNeighbourhood_of_ker_pow_eq_bot
    (Z : ClosedSubspaces B S hS X.1)
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J)
    (hZJ : invariantSubspace B S hS φ (Subobject.mk J.subschemeι) = Z.1)
    {T : BigFppfOver B S hS} (β : yoneda.obj T ⟶ X.1) {n : ℕ}
    (hker : ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd β)).ker ^ (n + 1) = ⊥) :
    yonedaEquiv β ∈ (nthOrderInfinitesimalNeighbourhood B S hS φ J n).obj (op T) := by
  have hJker := ker_rep_snd_eq_of_invariantSubspace_eq B S hS hs Z hJ hZJ
  intro T' g k hk
  have hw : yoneda.map k ≫ φ = yoneda.map g ≫ β := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, hk, yonedaEquiv_naturality, yonedaEquiv_comp,
      yonedaEquiv_yoneda_map]
  rw [mem_subschemePoints_iff, Scheme.IdealSheafData.factors_mk_subschemeι_iff,
    ← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le,
    Stacks.IdealSheaf.comap_pow, ← hJker, ← schemeKer_snd_comp B S hS Z φ k, hw,
    schemeKer_snd_comp B S hS Z β g, ← Stacks.IdealSheaf.comap_pow, hker,
    Scheme.IdealSheafData.comap_bot]

include hs in
/-- **A morphism from the spectrum of an Artinian local ring centred in a closed subspace lands
in one of its infinitesimal neighbourhoods.** Let `Z ⊆ X` be cut out on the chart `φ` by the
invariant sheaf of ideals `J`, let `T` be an object of the site whose underlying scheme is the
spectrum of an Artinian local ring, and let `β : T ⟶ X` send some point of `T` into `Z`. Then
`β` is a section of the `n`th order infinitesimal neighbourhood of `Z` for some `n`.

The base change `Z ×_X T ⊆ T` is a nonempty closed subscheme, because a point of `T` lies over a
point of `Z`; its ideal sheaf is therefore proper, hence nilpotent. -/
theorem exists_mem_nthOrderInfinitesimalNeighbourhood_of_isArtinianRing
    (Z : ClosedSubspaces B S hS X.1)
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J)
    (hZJ : invariantSubspace B S hS φ (Subobject.mk J.subschemeι) = Z.1)
    {R : CommRingCat.{u}} [IsLocalRing R] [IsArtinianRing R] {T : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec R) (β : yoneda.obj T ⟶ X.1)
    (w : points B S hS (yoneda.obj T))
    (hw : pointsMap B S hS (yoneda.obj T) β w ∈
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι)) :
    ∃ n : ℕ, yonedaEquiv β ∈ (nthOrderInfinitesimalNeighbourhood B S hS φ J n).obj (op T) := by
  obtain ⟨z, hz⟩ := hw
  obtain ⟨w', -, -⟩ := exists_points_of_isPullback B S hS (Z.2.2.rep.isPullback β) z w hz
  obtain ⟨p, -⟩ := Quot.exists_rep w'
  have hne : ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd β)).ker ≠ ⊤ := fun h =>
    ((Scheme.Hom.ker_eq_top_iff_isEmpty _).mp h).false (schemePoint B S hS _ p)
  obtain ⟨n, hn⟩ := Scheme.IdealSheafData.exists_pow_succ_eq_bot_of_isArtinianRing e _ hne
  exact ⟨n, mem_nthOrderInfinitesimalNeighbourhood_of_ker_pow_eq_bot B S hS hs Z hJ hZJ β hn⟩

end Space

end AlgebraicGeometry

end
