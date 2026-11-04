module

public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison

/-!
# A coherent module on a regular scheme is perfect on the site of opens

[Stacks, Tag 08CM] defines perfectness of a complex of `O_X`-modules on a ringed space by
testing on an open neighbourhood of each *point*: a strictly perfect complex over `X|_U` with a
quasi-isomorphism to the restriction of the complex. [Stacks, Tag 08G5] defines it on a ringed
site by testing on a *covering sieve* of each object, with the strictly perfect complex taken
over the slice sheaf of rings. This file proves that the first implies the second at the ringed
site of opens of the space, `Stacks.SheafOfModules.ringedSite X.sheaf`, and deduces the
site-level form of the degree-zero case of [Stacks, Tag 0FDC]: a coherent module on a regular
scheme is perfect.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/PerfectInternalHomPushforward.lean` and of
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHomEvaluation/PerfectEvaluation.lean` record
that no comparison between the two notions of perfectness exists anywhere in this library; it
does now, and those two consumers can stop duplicating the local data.

## Main definitions

* `AlgebraicGeometry.RingedSpace.PerfectComplexes.HasSitePerfectModel`: the local datum of
  [Stacks, Tag 08G5] over a single open of a ringed space — a strictly perfect complex over the
  slice sheaf of rings, with a quasi-isomorphism to the restriction of the complex.

## Main results

* `AlgebraicGeometry.RingedSpace.PerfectComplexes.isPerfectComplex_ringedSite` and
  `isPerfect_ringedSite`: the comparison, [Stacks, Tag 08CM] parts (1) and (2) into
  [Stacks, Tag 08G5] parts (1) and (2).
* `AlgebraicGeometry.isPerfect_singleFunctor_of_isCoherent_of_isRegular`: a coherent module on a
  regular scheme, placed in degree zero, is a perfect object of the derived category of modules
  on the ringed site of opens of the scheme. This is the site-level form of the degree-zero case
  of the forward half of [Stacks, Tag 0FDC].

## The three steps

*The change of model in the local data.* The ringed-space predicate produces a strictly perfect
complex over `X.restrict U`, and the site predicate wants one over the slice
`(structureSheafOfRings X).over U`. The transport is
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictBackward`, already built for
pseudo-coherence: it is exact and carries the unit sheaf to the unit sheaf, so
`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex` applies to it, the two notions
of strict perfection agree by
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_iff`, and
`restrictComplexBackwardIso` identifies its value on the restriction to `U` with the restriction
to the slice over `U`. Being exact it is also invertible on cohomology degreewise, which is what
turns the local quasi-isomorphism into a site-level one.

*Shrinking.* The covering sieve of an object `U₀` of the site must consist of opens *contained
in* `U₀`, while the point-local data lives on an open `Uₓ` which need not be. Restriction along
an arrow of the site is again exact and unit-preserving, so a site model over `U` restricts to
one over any smaller open; `hasSitePerfectModel_mono`.

*The covering.* With shrinking in hand the covering presieve of `U₀` is "every open admitting a
site model", which covers because for `x ∈ U₀` the open `U₀ ⊓ Uₓ` is one such open containing
`x`. The sieve it generates therefore contains an arrow through a member at every point, which is
membership in `Opens.grothendieckTopology`.

## Implementation notes

The whole argument is the one of
`StacksFrontier/Topology/Sheaves/Cohomology/PseudoCoherence/RingedSiteComparison.lean` with the
approximation data of [Stacks, Tag 08FT] replaced by a quasi-isomorphism, and it reuses that
file's transport functors and their exactness verbatim; only `HasSitePerfectModel` and the three
steps above are new. The quasi-isomorphism is handled degreewise through
`quasiIsoAt_iff_isIso_homologyMap` and `AlgebraicGeometry.RingedSite.isIso_homologyMap_map` and
`isIso_homologyMap_comp_iso`, rather than through Mathlib's instances for
`QuasiIso ((F.mapHomologicalComplex c).map φ)`, because at the use site the source complex of
the transported map has two spellings which agree only at default transparency, where instance
search does not look.

The module universe is the universe of the structure rings throughout, as it already must be for
[Stacks, Tag 08CM]: `SheafOfModules.free`, which the site notion of strict perfection is phrased
with, lands at the ring universe and at no other. This is also why the locality results pinned
at module universe `0` are of no use for `Scheme.{u}`.

The derived category of `O_X`-modules has to be read at the site spelling of the sheaf of rings
as well: the two spellings are `rfl`-equal but instance search does not cross them, and
`HasDerivedCategory` carries the localized category as data, so the instance must be transported
rather than re-synthesized — a second instance would give a second derived category and
`isPerfect_ringedSite` would be about a different one. The transport is
`AlgebraicGeometry.RingedSpace.PseudoCoherence.hasDerivedCategoryRingedSite` of
`StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison`, activated here
by `attribute [local instance]`.

## References

* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

universe u d

namespace AlgebraicGeometry.RingedSpace.PerfectComplexes

open AlgebraicGeometry.RingedSpace.PseudoCoherence

variable (X : RingedSpace.{u, u})

/-- **A site-level strictly perfect model of `E` over the open `W`.** The local datum asked for
by [Stacks, Tag 08G5] at one object of the site of opens: a strictly perfect complex of modules
over the slice sheaf of rings `O_X|_W`, in the sense of [Stacks, Tag 08FL], together with a
quasi-isomorphism from it to the restriction of `E` to the site over `W`. -/
def HasSitePerfectModel (E : CochainComplex (OXMod.{u} X) ℤ) (W : Opens X.carrier) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} ((structureSheafOfRings X).over W)) ℤ,
    _root_.IsStrictlyPerfect ((structureSheafOfRings X).over W) P ∧
    ∃ q : P ⟶ (Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E W, QuasiIso q

/-- An exact functor of sheaves of modules carrying the unit sheaf to the unit sheaf transports a
strictly perfect model along a quasi-isomorphism, up to an isomorphism of complexes. -/
private theorem exists_strictlyPerfect_quasiIso_of_exact
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R))
    {P : CochainComplex (SheafOfModules.{u} R) ℤ} (hP : _root_.IsStrictlyPerfect R P)
    {E' : CochainComplex (SheafOfModules.{u} R) ℤ} {E : CochainComplex (SheafOfModules.{u} S) ℤ}
    (q : P ⟶ E') [QuasiIso q]
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E' ≅ E) :
    ∃ P' : CochainComplex (SheafOfModules.{u} S) ℤ, _root_.IsStrictlyPerfect S P' ∧
      ∃ q' : P' ⟶ E, QuasiIso q' := by
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  exact ⟨_, Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex F η hP,
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ e.hom, ⟨fun j =>
      (quasiIsoAt_iff_isIso_homologyMap _ j).2 (RingedSite.isIso_homologyMap_comp_iso _ _ j
        (RingedSite.isIso_homologyMap_map F q j
          ((quasiIsoAt_iff_isIso_homologyMap q j).1 inferInstance)))⟩⟩

/-- **A ringed-space strictly perfect model over `U` is a site model over `U`.** The strictly
perfect complex over the open subspace `X|_U` of [Stacks, Tag 08CM] is carried to one over the
slice sheaf of rings over `U` by `restrictBackward`, which is exact and carries the unit sheaf to
the unit sheaf, hence preserves strict perfection and invertibility on cohomology; composing with
`restrictComplexBackwardIso` lands the transported map in the site-level restriction of `E`. -/
theorem hasSitePerfectModel_of_space (U : Opens X.carrier)
    (E : CochainComplex (OXMod.{u} X) ℤ)
    {P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ}
    (hP : StrictlyPerfect.IsStrictlyPerfect P)
    (q : P ⟶ restrictComplex E U) (hq : QuasiIso q) :
    HasSitePerfectModel X E U := by
  have hlim : PreservesFiniteLimits (restrictBackward X U) := inferInstance
  have hcol : PreservesFiniteColimits (restrictBackward X U) := inferInstance
  have := hq
  exact exists_strictlyPerfect_quasiIso_of_exact (restrictBackward X U)
    (restrictBackwardUnitIso X U) ((isStrictlyPerfect_iff _ P).1 hP) q
    (restrictComplexBackwardIso X U E)

/-- **A site model shrinks to a smaller open.** Restriction along the arrow `W ⟶ U` of the site
is exact and carries the unit sheaf to the unit sheaf, so it preserves both strict perfection and
invertibility on cohomology; the identification of the two ways of restricting `E` to `W` is
again a composition with an isomorphism of complexes. -/
theorem hasSitePerfectModel_mono (E : CochainComplex (OXMod.{u} X) ℤ)
    {U W : Opens X.carrier} (hWU : W ≤ U) (h : HasSitePerfectModel X E U) :
    HasSitePerfectModel X E W := by
  obtain ⟨P, hP, q, hq⟩ := h
  set F := SheafOfModules.overMap.{u} (structureSheafOfRings X) (homOfLE hWU)
  have hadd : F.Additive := ⟨by intros; ext V; rfl⟩
  have hlim : PreservesFiniteLimits F :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits (homOfLE hWU)
  have hcol : PreservesFiniteColimits F :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits (homOfLE hWU)
  exact exists_strictlyPerfect_quasiIso_of_exact F
    (SheafOfModules.overMapUnitIso.{u} (R := structureSheafOfRings X) (homOfLE hWU)).symm hP q
    ((Functor.mapHomologicalComplexCompIso
      (SheafOfModules.overFunctorMap.{u} (structureSheafOfRings X) (homOfLE hWU))
      (ComplexShape.up ℤ)).app E)

/-- **Ringed-space perfectness of a complex is perfectness on the site of opens.** Given an open
covering of `X` carrying strictly perfect models of `E`, the covering presieve of an object `U₀`
of the site of opens is "every open admitting a site-level strictly perfect model of `E`". It
generates a covering sieve because a point `x` of `U₀` lies in some member `U i` of the covering,
and `U₀ ⊓ U i` is then an open containing `x` which admits a site model, by transporting the
model over `U i` and shrinking it. -/
theorem isPerfectComplex_ringedSite (E : CochainComplex (OXMod.{u} X) ℤ)
    (h : IsPerfectComplex E) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfectComplex E := by
  obtain ⟨I, U, hsup, hmod⟩ := h
  intro U₀
  refine ⟨fun {W} _ => HasSitePerfectModel X E W, ?_, fun {W} f hf => hf⟩
  intro x hx
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := Opens.mem_iSup.mp (by rw [hsup]; trivial)
  obtain ⟨P, hP, q, hq⟩ := hmod i
  refine ⟨U₀ ⊓ U i, homOfLE inf_le_left, ?_, hx, hxi⟩
  exact ⟨U₀ ⊓ U i, 𝟙 _, homOfLE inf_le_left,
    hasSitePerfectModel_mono X E inf_le_right
      (hasSitePerfectModel_of_space X (U i) E hP q hq), Category.id_comp _⟩

variable [HasDerivedCategory.{d} (OXMod.{u} X)]

-- The derived category of `O_X`-modules read at the site spelling of the sheaf of rings. It is
-- the same instance, found at the other spelling of the sheaf of rings, which instance search
-- does not cross; `AlgebraicGeometry.RingedSpace.PseudoCoherence.hasDerivedCategoryRingedSite`
-- of `StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison` already
-- transports it, so it is activated here rather than declared again.
attribute [local instance]
  AlgebraicGeometry.RingedSpace.PseudoCoherence.hasDerivedCategoryRingedSite

/-- **Stacks 08CM implies Stacks 08G5 on derived categories.** A perfect complex representing
`K` on the ringed space is, by `isPerfectComplex_ringedSite`, a perfect complex on the site of
opens, and it represents the same object of the derived category. -/
theorem isPerfect_ringedSite (K : DerivedCategory (OXMod.{u} X)) (h : IsPerfect K) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect K := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  exact ⟨E, isPerfectComplex_ringedSite X E hE, ⟨e⟩⟩

end AlgebraicGeometry.RingedSpace.PerfectComplexes

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **A coherent module on a regular scheme is perfect on the site of opens.** Let `X` be a
regular scheme and `ℱ` a coherent `𝒪_X`-module. Then `ℱ`, placed in degree zero, is a perfect
object of the derived category of modules on the ringed site of opens of `X`, in the sense of
[Stacks, Tag 08G5].

This is the site-level form of the degree-zero case of the forward half of [Stacks, Tag 0FDC].
It is `AlgebraicGeometry.isPerfect_single_of_isCoherent_of_isRegular`, the same statement for the
underlying ringed space, carried across `isPerfect_ringedSite`; no quasi-compactness is needed,
for the same reason as there. -/
theorem isPerfect_singleFunctor_of_isCoherent_of_isRegular {X : Scheme.{u}} (hX : IsRegular X)
    (F : X.Modules) [F.IsCoherent] :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (Stacks.SheafOfModules.ringedSite X.sheaf).O)) 0).obj F) :=
  RingedSpace.PerfectComplexes.isPerfect_ringedSite X.toRingedSpace _
    (isPerfect_single_of_isCoherent_of_isRegular hX F)

end AlgebraicGeometry

end
