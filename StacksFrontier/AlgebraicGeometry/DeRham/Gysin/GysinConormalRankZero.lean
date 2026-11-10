module

public import StacksFrontier.AlgebraicGeometry.ConormalEquations.RankGenerators
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartLocal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.KerCover
public import StacksFrontier.AlgebraicGeometry.Modules.ClopenCoverSplitting
public import StacksFrontier.AlgebraicGeometry.Modules.PushforwardAlongIso
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsUniv

/-!
# A closed immersion whose conormal sheaf has rank zero is an open immersion

[Stacks, Tag 0G86] produces the Gysin map of a closed immersion of finite presentation whose
conormal sheaf is locally free of rank `c`, for an unqualified natural number `c`.  The chart
route to that tag needs `c ≠ 0`, because away from the closed subscheme the chart equations must
generate the unit ideal and an empty family cannot.  This file supplies the geometry of the
remaining case `c = 0`, which is not vacuous: rank `0` says exactly that the conormal sheaf
vanishes, and that forces `i` to be an isomorphism onto an *open* subscheme — whose range, being
also closed, is clopen — but it does **not** force the range to be all of `X`.  The inclusion of
a proper clopen piece `Z ⊊ X` satisfies it, for instance one component of `Spec k ⊔ Spec k`,
where the ideal `I` of the component is nonzero and yet `I = I ²`, so `I/I ² = 0`.

## Main results

* `Stacks.Gysin.exists_affineOpen_subset_range_ker_eq_bot`: at rank `0` every point of `Z` has an
  affine neighbourhood in `X` which is contained in the image of `i` and on which the ideal of
  `Z` vanishes.
* `Stacks.Gysin.isOpen_range_base_of_conormalRank_zero`: the image of `i` is open.
* `Stacks.Gysin.isClopen_range_base_of_conormalRank_zero`: the image of `i` is clopen.
* `Stacks.Gysin.isOpenImmersion_of_conormalRank_zero`: `i` is an open immersion, hence an
  isomorphism onto a clopen subscheme.
* `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnZeroIsoId`: **degree-zero local
  cohomology with supports in the whole scheme is the identity**, `ℋ ⁰_X ≅ 𝟭`.
* `Stacks.Gysin.pushforwardLocalCohomologyZeroIso`: **the target of the local Gysin map of
  [Stacks, Tag 0G83] for an *empty* family of equations is the coefficient module itself**, which
  is that degeneration in the spelling [Stacks, Tag 0G83] states its target at.

## Implementation notes

The neighbourhood is produced by `exists_affineOpen_equations_of_conormalRank`, which carries no
hypothesis on `c` and so applies verbatim at `c = 0`, where it returns an affine `W` and an
*empty* family of equations generating the ideal of `Z` on `W`; the ideal is therefore `⊥` there.

That `W` lies inside the image is read off the same empty family.  The common zero locus
`Stacks.Gysin.equationsClosedSet` of a family is the complement of the union of the basic opens
of its members, so for an empty family it is everything; and
`Stacks.Gysin.equationsClosedSet_restrictEquations` identifies that zero locus with the part of
the image lying over `W`.  Hence all of `W` lies over the image.

This local use of the equations is sound exactly because it is local.  The *global* statement
`Stacks.Gysin.equationsClosedSet_eq_range` applied to an empty family of global sections would
force the image to be all of `X`, so the empty family can never cut out a proper `Z` on the
whole of `X`; here it only ever cuts out `Z` on a chart `W` already inside the image, and what
is concluded is `W ⊆ Set.range i.base`, not surjectivity.

From there `Stacks.ClosedCoverKer.isOpenImmersion_of_isClosedImmersion_of_ker_ideal_eq_bot`
finishes, and it is the lemma to use rather than a reducedness-based one: it asks only that the
range be open and that the kernel ideal vanish on the affine opens inside the range.  The latter
is upgraded from the chart neighbourhoods to *every* affine open inside the range by
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_bot_of_cover_eq_bot`, vanishing of an ideal
sheaf being a local condition.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.DifferentialsRestrict
open Stacks.Perfect.CechDerivedSupport
open Stacks.AlgebraicGeometry.ConormalEquations

universe u

namespace Stacks.Gysin

variable {Z X : Scheme.{u}}

/-- **An empty family of equations cuts out the whole scheme.**  The common zero locus of a
family is the complement of the union of the basic opens of its members, and a union over no
members is empty. -/
theorem equationsClosedSet_empty {Y : Scheme.{u}} (g : Fin 0 → Γ(Y, ⊤)) :
    equationsClosedSet g = Set.univ := by
  simp [equationsClosedSet]

/-- **At conormal rank `0` the ideal of `Z` vanishes on an affine neighbourhood of every point
of the image, and that neighbourhood lies inside the image.**

`exists_affineOpen_equations_of_conormalRank` has no hypothesis on the rank, so at `c = 0` it
returns an affine `W` around `i.base z` together with an empty family of equations generating the
ideal of `Z` over `W`; the ideal is then the span of the empty set, that is `⊥`.  That `W` lies
over the image is the identification
`Stacks.Gysin.equationsClosedSet_restrictEquations` of the common zero locus of those equations
with the part of the image over `W`: an empty family has everything as its zero locus. -/
theorem exists_affineOpen_subset_range_ker_eq_bot (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hE : ConormalRank i 0) (z : Z) :
    ∃ W : X.Opens, IsAffineOpen W ∧ i.base z ∈ W ∧ (W : Set X) ⊆ Set.range i.base ∧
      RingHom.ker (i.app W).hom = ⊥ := by
  obtain ⟨W, hWaff, hzW, f, -, hgen, hker⟩ :=
    exists_affineOpen_equations_of_conormalRank i 0 hE z
  refine ⟨W, hWaff, hzW, ?_, by rw [hker, Set.range_eq_empty, Ideal.span_empty]⟩
  have hcut := isCutOutByEquationsOn_of_isGeneratedByOn i hgen fun V hV j => j.elim0
  simpa only [Scheme.Opens.range_ι] using Set.preimage_eq_univ_iff.mp
    ((equationsClosedSet_restrictEquations i W hcut).symm.trans (equationsClosedSet_empty _))

/-- **The image of a closed immersion of conormal rank `0` is open.**  Every point of the image
is `i.base z` for some `z`, and `exists_affineOpen_subset_range_ker_eq_bot` puts an open
neighbourhood of it inside the image. -/
theorem isOpen_range_base_of_conormalRank_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hE : ConormalRank i 0) :
    IsOpen (Set.range i.base) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨z, rfl⟩
  obtain ⟨W, -, hzW, hsub, -⟩ := exists_affineOpen_subset_range_ker_eq_bot i hE z
  exact ⟨(W : Set X), hsub, W.2, hzW⟩

/-- **The image of a closed immersion of conormal rank `0` is clopen.**  It is closed because `i`
is a closed immersion and open by `isOpen_range_base_of_conormalRank_zero`. -/
theorem isClopen_range_base_of_conormalRank_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hE : ConormalRank i 0) :
    IsClopen (Set.range i.base) :=
  ⟨isClosed_range_base i, isOpen_range_base_of_conormalRank_zero i hE⟩

/-- **The kernel ideal of a closed immersion of conormal rank `0` vanishes on every affine open
inside the image.**  The chart neighbourhoods of
`exists_affineOpen_subset_range_ker_eq_bot` cover any such affine open, since each point of it
lies in the image, and vanishing of an ideal sheaf is a local condition. -/
theorem ker_ideal_eq_bot_of_conormalRank_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hE : ConormalRank i 0) (A : X.affineOpens)
    (hA : (A : Set X) ⊆ Set.range i.base) :
    (Scheme.Hom.ker i).ideal A = ⊥ := by
  classical
  choose W hWaff hzW hsub hker using
    fun z : Z => exists_affineOpen_subset_range_ker_eq_bot i hE z
  refine Scheme.IdealSheafData.ideal_eq_bot_of_cover_eq_bot _
    (fun z : Z => (⟨W z, hWaff z⟩ : X.affineOpens)) A (fun x => ?_) fun z => ?_
  · obtain ⟨z, hz⟩ := hA x.2
    exact ⟨z, hz ▸ hzW z⟩
  · rw [Scheme.Hom.ker_apply]
    exact hker z

/-- **A closed immersion of finite presentation whose conormal sheaf has rank `0` is an open
immersion**, hence an isomorphism onto a clopen subscheme of the ambient scheme.

This is the geometry of the case `c = 0` of [Stacks, Tag 0G86].  It does not make `i`
surjective: the identity satisfies the hypotheses, and so does the inclusion of a proper clopen
piece. -/
theorem isOpenImmersion_of_conormalRank_zero (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hE : ConormalRank i 0) :
    IsOpenImmersion i :=
  Stacks.ClosedCoverKer.isOpenImmersion_of_isClosedImmersion_of_ker_ideal_eq_bot i
    (isOpen_range_base_of_conormalRank_zero i hE)
    (ker_ideal_eq_bot_of_conormalRank_zero i hE)

/-! ### The image as a clopen subscheme, and the source over it -/

/-- **The image of a closed immersion of conormal rank `0`, as an open of the ambient scheme.**
Its underlying set is `Set.range i.base`, which
`isClopen_range_base_of_conormalRank_zero` shows is clopen. -/
def rangeOpens (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (hE : ConormalRank i 0) : X.Opens :=
  ⟨Set.range i.base, isOpen_range_base_of_conormalRank_zero i hE⟩

/-- **Over its own image, a closed immersion of conormal rank `0` is an isomorphism.**  It is an
open immersion by `isOpenImmersion_of_conormalRank_zero`, so its restriction over any open is
one too; and over the image that restriction is surjective, because the image of the restriction
is the part of the image lying over the open, which here is everything. -/
theorem isIso_morphismRestrict_rangeOpens (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hE : ConormalRank i 0) :
    IsIso (i ∣_ rangeOpens i hE) := by
  have := isOpenImmersion_of_conormalRank_zero i hE
  refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨fun y => ?_⟩⟩
  change y ∈ Set.range (i ∣_ rangeOpens i hE).base
  rw [range_morphismRestrict_base i (rangeOpens i hE)]
  exact y.2

/-- **Over the image, the source of the Gysin map is the relative forms of the image.**  That is,
`(i_*Ω^p_{Z/S})|_U ≅ Ω^p_{U/S}` for `U` the image of `i`.

`Stacks.Gysin.srcIso` presents the left side as the pushforward, along `i ∣_ U`, of the relative
forms of a composite through it; over the image `i ∣_ U` is an isomorphism, by
`isIso_morphismRestrict_rangeOpens`, and
`AlgebraicGeometry.Scheme.Modules.pushforwardRelativeFormsIsoOfIso` then reads that pushforward
away. -/
def restrictSourceRangeIso (i : Z ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    {S : Scheme.{u}} (π : X ⟶ S) (p : ℕ) (hE : ConormalRank i 0) :
    Scheme.Modules.restrict (pushforwardRelativeForms i π (p : ℤ)) (rangeOpens i hE).ι ≅
      relativeDifferentialForms ((rangeOpens i hE).ι ≫ π) (p : ℤ) :=
  haveI := isIso_morphismRestrict_rangeOpens i hE
  srcIso i π (rangeOpens i hE) p ≪≫
    Scheme.Modules.pushforwardRelativeFormsIsoOfIso (asIso (i ∣_ rangeOpens i hE))
      ((rangeOpens i hE).ι ≫ π) (p : ℤ)

/-- **Over the image, the source and the ambient relative forms agree**: `(i_*Ω^p_{Z/S})|_U` is
`(Ω^p_{X/S})|_U`.

This is `restrictSourceRangeIso` followed by the inverse of the étale comparison
`Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIso` for the
open `U`.  It is the isomorphism that the `c = 0` Gysin map is over the image; off the image both
sheaves vanish, and the clopen splitting
`AlgebraicGeometry.exists_hom_of_clopenHoms` turns the pair into a morphism on `X`. -/
def restrictSourceAmbientIso (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] {S : Scheme.{u}} (π : X ⟶ S) (p : ℕ)
    (hE : ConormalRank i 0) :
    Scheme.Modules.restrict (pushforwardRelativeForms i π (p : ℤ)) (rangeOpens i hE).ι ≅
      Scheme.Modules.restrict (relativeDifferentialForms π (p : ℤ)) (rangeOpens i hE).ι :=
  restrictSourceRangeIso i π p hE ≪≫
    (relativeDifferentialFormsRestrictIso π (rangeOpens i hE) (p : ℤ)).symm

/-- The complement of the image is open, the image being closed. -/
theorem isOpen_compl_rangeOpens (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (hE : ConormalRank i 0) :
    IsOpen (((rangeOpens i hE : X.Opens) : Set X)ᶜ) :=
  (isClosed_range_base i).isOpen_compl

/-- `restrictSourceAmbientIso` read at the `pullback` spelling, which is the one the clopen
splitting `AlgebraicGeometry.exists_hom_of_clopenHoms` consumes. -/
def pullbackSourceAmbientIso (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] {S : Scheme.{u}} (π : X ⟶ S) (p : ℕ)
    (hE : ConormalRank i 0) :
    (Scheme.Modules.pullback (rangeOpens i hE).ι).obj
        (pushforwardRelativeForms i π (p : ℤ)) ≅
      (Scheme.Modules.pullback (rangeOpens i hE).ι).obj
        (relativeDifferentialForms π (p : ℤ)) :=
  ((Scheme.Modules.restrictFunctorIsoPullback (rangeOpens i hE).ι).app _).symm ≪≫
    restrictSourceAmbientIso i π p hE ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback (rangeOpens i hE).ι).app _

/-- **The extension-by-zero map `i_*Ω^p_{Z/S} ⟶ Ω^p_{X/S}` of a closed immersion of conormal
rank `0`**, characterised by what it is over the image.

For a general closed immersion there is no such map — the canonical map runs the other way, by
restriction.  It exists here because the image is clopen: over the image the two sheaves agree,
by `restrictSourceAmbientIso`, and over the complement the source vanishes, so *any* morphism
will do there and `0` is taken.  That those two pieces need satisfy no compatibility is
`AlgebraicGeometry.exists_hom_of_clopenHoms`, the two pieces being disjoint.

Only the component over the image is recorded, that being the one with content; the component
over the complement is `0` by construction. -/
theorem exists_extendByZeroHom (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] {S : Scheme.{u}} (π : X ⟶ S) (p : ℕ)
    (hE : ConormalRank i 0) :
    ∃ ψ : pushforwardRelativeForms i π (p : ℤ) ⟶ relativeDifferentialForms π (p : ℤ),
      (Scheme.Modules.pullback (rangeOpens i hE).ι).map ψ =
        (pullbackSourceAmbientIso i π p hE).hom := by
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.exists_hom_of_clopenHoms (rangeOpens i hE)
    (isOpen_compl_rangeOpens i hE) (pushforwardRelativeForms i π (p : ℤ))
    (relativeDifferentialForms π (p : ℤ))
    (fun b => match b with
      | true => (pullbackSourceAmbientIso i π p hE).hom
      | false => 0)
  exact ⟨ψ, hψ true⟩

end Stacks.Gysin

/-! ### The degree-zero target is a subsheaf, not a cokernel -/

section DegreeZero

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedFraction

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Perfect.LocalCohomologyExcision

/-- **Degree-zero local cohomology with supports in a closed subset is the subsheaf of sections
supported there**: `ℋ ⁰_T = H_T`, as endofunctors of `X.Modules`.

The right derived functors of `H_T` taken on `X` are, by
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso`, the direct images of the local
cohomology sheaves `ℋ ⁿ_T` taken on `T`; and in degree zero the latter, pushed forward, are
`H_T` again, by
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorZeroCompPushforwardIso`, whose
content is that `H_T` is left exact, being a right adjoint.

This is what replaces, in degree zero, the cokernel presentation of the higher local cohomology
sheaves: `ℋ ⁰_T(ℱ)` is a *subsheaf* of `ℱ`, so no quotient by a top-degree differential of an
extended alternating Čech complex is involved, and none is available — such a complex has no
differential into degree `0`. -/
def localCohomologyOnZeroIso (X : Scheme.{u}) (T : Set X) (hT : IsClosed T) :
    localCohomologyOn X T 0 ≅ supportedSectionsOn X T :=
  (localCohomologyOnIso X T hT 0).symm ≪≫
    localCohomologySheafFunctorZeroCompPushforwardIso X.toRingedSpace T hT

/-- **Sections supported on the whole scheme are all the sections**: `H_X ≅ 𝟭`.

This is `Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctorIsoId` of the underlying
ringed space, read at the `X.Modules` spelling of the category of `𝒪_X`-modules, which is the
spelling `supportedSectionsOn` is stated at. -/
def supportedSectionsOnIsoId (X : Scheme.{u}) (T : Set X) (hT : T = Set.univ) :
    supportedSectionsOn X T ≅ Functor.id X.Modules :=
  Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctorIsoId X.toRingedSpace T hT

/-- **Degree-zero local cohomology with supports in the whole scheme is the identity**:
`ℋ ⁰_X ≅ 𝟭`.

In degree zero local cohomology with supports in `T` is the subsheaf of sections supported on
`T`, by `localCohomologyOnZeroIso`; when `T` is everything that subsheaf is the whole sheaf, by
`supportedSectionsOnIsoId`.

This is the degeneration the Gysin map of [Stacks, Tag 0G86] meets at conormal rank `c = 0`: a
chart then carries an empty family of equations, whose common zero locus is the whole chart by
`Stacks.Gysin.equationsClosedSet_empty`, so the local cohomology in the target of
[Stacks, Tag 0G83] is taken with supports in everything and in degree zero. -/
def localCohomologyOnZeroIsoId (X : Scheme.{u}) (T : Set X) (hT : T = Set.univ) :
    localCohomologyOn X T 0 ≅ Functor.id X.Modules :=
  localCohomologyOnZeroIso X T (hT ▸ isClosed_univ) ≪≫ supportedSectionsOnIsoId X T hT

end Stacks.Perfect.LocalCohomologyExcision

namespace Stacks.Gysin

open AlgebraicGeometry.Scheme.Hom Stacks.Perfect.LocalCohomologyExcision

/-- **The target of the Gysin map of [Stacks, Tag 0G86] at `c = 0` is the subsheaf of sections
supported on `Z`.**  That is, `ℋ ⁰_Z(Ω^p_{X/S})` is `H_Z(Ω^p_{X/S}) ⊆ Ω^p_{X/S}`.

`Stacks.Gysin.gysinTarget` is the degree-`c` cohomology sheaf of `i_* R𝓗_Z(ℱ[0])`; at `c = 0`
`Stacks.Gysin.supportCohomologyOnIso` turns it into the degree-zero right derived functor of
`H_Z`, which `localCohomologyOnZeroIso` identifies with `H_Z` itself.

This is the degree-zero replacement for the class-map presentation used when `c = d + 1`.  There
the target is a *cokernel* — `Stacks.Perfect.SupportedFraction.supportedFractionClass` descends
along `cokernel.π (lastDif f F)`, the quotient by the last differential of the extended
alternating Čech complex, from degree `d` to the top degree `d + 1`.  At `c = 0` that complex has
only degree `0`, so there is no such differential and no cokernel; the identification above says
what the target is instead. -/
def gysinTargetZeroIso {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S)
    (p : ℕ) :
    gysinTarget i π 0 p ≅
      (supportedSectionsOn X (Set.range i.base)).obj
        (relativeDifferentialForms π ((p : ℤ) + ((0 : ℕ) : ℤ))) :=
  (supportCohomologyOnIso X (Set.range i.base) (isClosed_range_base i) 0).app _ ≪≫
    (localCohomologyOnZeroIso X (Set.range i.base) (isClosed_range_base i)).app _

/-- **The target of the local Gysin map of [Stacks, Tag 0G83] for an empty family of equations is
the coefficient module itself**: `i_*ℋ ⁰_{V(∅)}(𝒢) ≅ 𝒢`.

This is the degeneration of the whole supported-cohomology tower at `c = 0`, in the spelling the
Gysin map of [Stacks, Tag 0G83] uses for its target.  Three steps:

* `Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` moves from that spelling —
  the direct image of the degree-`c` local cohomology sheaf — to the spelling
  `Stacks.Perfect.SupportedFraction.supportCohomologySheaf` in which the degree-`c` cohomology is
  taken after the pushforward.  It is stated for an arbitrary number of equations, zero included,
  the direct image from a closed subset being exact;
* `Stacks.Gysin.supportCohomologyOnIso` identifies that with the degree-zero right derived
  functor of the sections supported on the zero locus;
* and `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnZeroIsoId` collapses it, the zero
  locus of an empty family being everything by `equationsClosedSet_empty`.

No cokernel of a top Čech differential appears, and none is available: the extended alternating
Čech complex of an empty family has only degree `0`. -/
def pushforwardLocalCohomologyZeroIso {Y : Scheme.{u}} (g : Fin 0 → Γ(Y, ⊤)) (G : Y.Modules) :
    pushforwardLocalCohomology g G ≅ G :=
  (Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward g G).symm ≪≫
    (supportCohomologyOnIso Y (equationsClosedSet g) (isClosed_equationsClosedSet g) 0).app G ≪≫
      (localCohomologyOnZeroIsoId Y (equationsClosedSet g) (equationsClosedSet_empty g)).app G

end Stacks.Gysin

end DegreeZero

end
