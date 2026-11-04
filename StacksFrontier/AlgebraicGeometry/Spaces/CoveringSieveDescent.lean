module

public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transferring effective descent along a covering sieve between properties

`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve B S hS P` is effective descent
for `P`-morphisms along the covering sieves of the big fppf site of `S`; it is the hypothesis
on which the three conclusions of Stacks 0265 are made to depend in
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic`, and it is taken there at *two*
different properties, neither of which is the property of Stacks 02W8.

This file shows that, exactly as for the single-morphism predicate
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`, the *property* half of the
covering-sieve predicate is free: effective descent along the covering sieves at one property
`P` implies it at every smaller property which satisfies fppf descent. Both properties at which
Stacks 0265 takes the hypothesis are smaller than the property of Stacks 02W8 and satisfy fppf
descent, so both instances are consequences of the single instance at the property of Stacks
02W8, and the three conclusions of Stacks 0265 are restated here conditional on that one
hypothesis.

The reduction needs one piece of geometry which the single-morphism predicate did not: a
property of morphisms of schemes which is Zariski local on the target and descends along the
surjective flat morphisms of finite presentation is local on the target for a *family* of flat
morphisms of finite presentation which is jointly surjective, and a covering sieve of the big
fppf site contains such a family. The first half is
`AlgebraicGeometry.of_jointlySurjective_flat_locallyOfFinitePresentation`, the second is
`AlgebraicGeometry.BigFppfSite.exists_mem_of_mem_topology`.

## Main results

* `AlgebraicGeometry.of_jointlySurjective_flat_locallyOfFinitePresentation`: a property of
  morphisms of schemes which is Zariski local on the target and descends along the surjective
  flat morphisms of finite presentation may be checked after base change along a jointly
  surjective family of flat morphisms of finite presentation.
* `AlgebraicGeometry.BigFppfSite.exists_mem_of_mem_topology` and
  `AlgebraicGeometry.BigFppfOver.exists_mem_of_mem_topology`: through every point of the base
  of a covering sieve of the big fppf site there passes an arrow of the sieve which is flat and
  locally of finite presentation.
* `AlgebraicGeometry.monomorphisms_descendsAlong_fppf`: monomorphisms of schemes satisfy fppf
  descent.
* `AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong` is the unconditional
  property-descent statement: if the base change of a morphism of presheaves along a morphism
  from a representable presheaf is *already* representable, then every property which is
  Zariski local on the target and satisfies fppf descent transfers to it from the base changes
  along the arrows of any covering sieve of the base.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_le`: effective descent along
  the covering sieves at `P` implies it at every `Q ≤ P` which is Zariski local on the target
  and satisfies fppf descent.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_of_zariskiCover` is the glueing
  step, Tag 0AP4, for the covering sieves: effective descent follows from a Zariski covering of
  the descended sheaf by representable open subfunctors, with no further hypothesis — in
  particular with no `AlgebraicGeometry.HasZariskiGluing` hypothesis, that being now proved
  outright.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_quotientChart` and its
  companion for the monomorphisms locally of finite type: the two instances of the hypothesis
  which Stacks 0265 consumes, each from the single instance at the property of Stacks 02W8.
* `AlgebraicGeometry.Space.surjective_toQuotientSheaf_of_coveringSieveDescent`,
  `AlgebraicGeometry.Space.etale_toQuotientSheaf_of_coveringSieveDescent` and
  `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_coveringSieveDescent`: the three
  conclusions of Stacks 0265, each conditional on effective descent along the covering sieves
  of the site at the property of Stacks 02W8 and on nothing else.

## Implementation notes

**Why the hypothesis is taken at the property of Stacks 02W8 and not at
`AlgebraicGeometry.IsSeparated ⊓ AlgebraicGeometry.LocallyQuasiFinite`.** Mathlib's
`AlgebraicGeometry.LocallyQuasiFinite` omits the finite-type condition of Stacks 00PL, so the
latter property is strictly larger than the property of Stacks 02W8 and effective descent at it
does not follow from that tag; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent`. Everything here is
therefore stated at
`AlgebraicGeometry.IsSeparated ⊓ AlgebraicGeometry.LocallyQuasiFinite ⊓
AlgebraicGeometry.LocallyOfFiniteType`.

**The family, not a coproduct.** The covering along which a point of a quotient sheaf lifts is a
covering sieve whose members are neither individually surjective nor étale, and the site's size
cutoff is only known to have uncountable cofinality, so the members cannot be replaced by a
coproduct *inside the site*. They can be replaced by a coproduct of *schemes*, which is all the
descent of a property needs, since no object has to be descended a second time: the coproduct is
formed over the points of the base, reindexing the family so that its index type lies in the
working universe, and the resulting morphism is surjective, flat and locally of finite
presentation because each of those properties is Zariski local at the source or is joint
surjectivity.

**Where the covering family comes from.** `AlgebraicGeometry.BigFppfSite.topology` is the
Grothendieck topology *generated* by the site's chosen fppf covering families, so a covering
sieve need not contain one of those families; it is only built from them by the pullback and
local-character axioms. That it is nevertheless refined by one is
`AlgebraicGeometry.Space.exists_covering_refining_sieve`, which is where the induction over
`CategoryTheory.Precoverage.Saturate` is performed once and for all. The statement that a
covering sieve has a flat, locally of finite presentation arrow through every point of its base
is then immediate from the geometry of a chosen covering family, with no induction of its own.

## References

* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02L4](https://stacks.math.columbia.edu/tag/02L4)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### fppf locality on the target for a jointly surjective family -/

/-- A property respecting isomorphisms holds for the second projection of one pullback square
as soon as it holds for that of another pullback square on the same cospan. -/
private theorem snd_of_isPullback_of_isPullback {C : Type*} [Category C] {P : MorphismProperty C}
    [P.RespectsIso] {X Y Z A A' : C} {f : X ⟶ Z} {g : Y ⟶ Z} {fst : A ⟶ X} {snd : A ⟶ Y}
    {fst' : A' ⟶ X} {snd' : A' ⟶ Y} (h : IsPullback fst snd f g) (h' : IsPullback fst' snd' f g)
    (hP : P snd) : P snd' := by
  rw [← h'.isoIsPullback_hom_snd _ _ h]
  exact MorphismProperty.RespectsIso.precomp P _ _ hP

/-- **A property which is Zariski local on the target and satisfies fppf descent may be checked
after base change along a jointly surjective family of flat morphisms of finite
presentation.** Precisely: let `w : Z ⟶ a` be a morphism of schemes and assume that through
every point of `a` there passes a flat morphism `q : b ⟶ a` of finite presentation along which
some base change of `w` has `Q`. Then `w` has `Q`.

The family is replaced by the single morphism `∐ b ⟶ a` indexed by the points of `a`: that
morphism is surjective because the family is jointly surjective, and flat and locally of finite
presentation because both properties are Zariski local at the source, so it is a one-element
fppf covering and `Q.DescendsAlong` applies to it. The base change of `w` along it has `Q`
because `Q` is Zariski local on the target and the coproduct is covered by its summands, over
each of which the base change is the given one. -/
theorem of_jointlySurjective_flat_locallyOfFinitePresentation
    {Q : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget Q]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {a Z : Scheme.{u}} (w : Z ⟶ a)
    (H : ∀ x : a, ∃ (b : Scheme.{u}) (q : b ⟶ a) (c : Scheme.{u}) (p₁ : c ⟶ Z) (p₂ : c ⟶ b),
      IsPullback p₁ p₂ w q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧
        x ∈ Set.range q.base ∧ Q p₂) :
    Q w := by
  have _hfls : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have _hfps : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  choose b q c p₁ p₂ hsq hflat hlofp hmem hQ using H
  -- the given base changes, transported to the chosen fibre products
  have hQ' : ∀ x : a, Q (pullback.fst (q x) w) := fun x ↦
    snd_of_isPullback_of_isPullback (hsq x) (IsPullback.of_hasPullback (q x) w).flip (hQ x)
  have hsurj : Surjective (Sigma.desc q) :=
    Surjective.sigmaDesc_of_union_range_eq_univ
      (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, hmem x⟩)
  have hfl : Flat (Sigma.desc q) := IsZariskiLocalAtSource.sigmaDesc hflat
  have hfp : LocallyOfFinitePresentation (Sigma.desc q) :=
    IsZariskiLocalAtSource.sigmaDesc hlofp
  have hpieces : ∀ x : a,
      Q (pullback.snd (pullback.fst (Sigma.desc q) w) (Sigma.ι b x)) := by
    intro x
    have hpaste := (IsPullback.of_hasPullback (pullback.fst (Sigma.desc q) w)
      (Sigma.ι b x)).paste_horiz (IsPullback.of_hasPullback (Sigma.desc q) w).flip
    rw [Sigma.ι_desc] at hpaste
    exact snd_of_isPullback_of_isPullback (IsPullback.of_hasPullback (q x) w).flip hpaste (hQ' x)
  refine MorphismProperty.of_pullback_fst_of_descendsAlong
    (Q := (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
    ⟨⟨hsurj, hfl⟩, hfp⟩ ?_
  exact IsZariskiLocalAtTarget.of_openCover (𝒰 := sigmaOpenCover b) fun i ↦ hpieces i

/-! ### Covering sieves of the big fppf site are jointly surjective -/

namespace BigFppfSite

/-- **Through every point of the base of a covering sieve of a big fppf site there passes an
arrow of the sieve which is flat and locally of finite presentation.**

The topology of a big fppf site is the one *generated* by the chosen fppf covering families, so
a covering sieve need not contain such a family. That it is nevertheless *refined* by one is
`AlgebraicGeometry.Space.exists_covering_refining_sieve`, and it is all that is needed here: a
chosen covering family is jointly surjective with flat members of finite presentation by
definition, so an arrow of the family through the given point is an arrow of the sieve through
the given point. -/
theorem exists_mem_of_mem_topology (B : BigFppfSite.{u}) {X : B.Schemes} {T : Sieve X}
    (hT : T ∈ B.topology X) (x : B.inclusion.obj X) :
    ∃ (Y : B.Schemes) (q : Y ⟶ X), T q ∧ Flat (B.inclusion.map q) ∧
      LocallyOfFinitePresentation (B.inclusion.map q) ∧
      x ∈ Set.range (B.inclusion.map q).base := by
  obtain ⟨E, hE, hET⟩ := Space.exists_covering_refining_sieve B hT
  have h := hE.1
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    ← PreZeroHypercover.presieve₀_map, Scheme.fppfPrecoverage,
    PreZeroHypercover.presieve₀, Scheme.ofArrows_mem_precoverage_iff] at h
  obtain ⟨i, y, hy⟩ := h.1 x
  exact ⟨E.X i, E.f i, hET _ _ ⟨i⟩, (h.2 i).1, (h.2 i).2, y, hy⟩

end BigFppfSite

namespace BigFppfOver

/-- `AlgebraicGeometry.BigFppfSite.exists_mem_of_mem_topology` in the big fppf category over
`S`: through every point of the base of a covering sieve there passes an arrow of the sieve
whose underlying morphism of schemes is flat and locally of finite presentation.

A sieve of an object of the slice is covering exactly when the corresponding sieve of its
underlying object is, by `CategoryTheory.GrothendieckTopology.mem_over_iff`, and an arrow of the
latter is the underlying morphism of an arrow of the former by
`CategoryTheory.Sieve.overEquiv_iff`. -/
theorem exists_mem_of_mem_topology (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {a : BigFppfOver B S hS} {T : Sieve a} (hT : T ∈ BigFppfOver.topology B S hS a)
    (x : (BigFppfOver.toScheme B S hS).obj a) :
    ∃ (c : BigFppfOver B S hS) (q : c ⟶ a), T q ∧
      Flat ((BigFppfOver.toScheme B S hS).map q) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q) ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map q).base := by
  rw [GrothendieckTopology.mem_over_iff] at hT
  obtain ⟨Y, q, hq, hqf, hqp, hx⟩ := B.exists_mem_of_mem_topology hT x
  exact ⟨Over.mk (q ≫ a.hom), Over.homMk q, (Sieve.overEquiv_iff T q).1 hq, hqf, hqp, hx⟩

end BigFppfOver

/-! ### fppf descent of the two properties of Stacks 0265 -/

/-- **Monomorphisms of schemes satisfy fppf descent**: if the base change of `g` along a
surjective flat morphism of finite presentation is a monomorphism, then so is `g`.

A monomorphism is a morphism whose diagonal is an isomorphism, and isomorphisms satisfy fpqc
descent by Stacks 02L4; fpqc descent for the diagonal of a property is Mathlib's
`CategoryTheory.MorphismProperty.DescendsAlong` instance for `MorphismProperty.diagonal`, and
the upgrade from the fpqc to the fppf coverings is
`AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc`. -/
@[ega "IV 2.7.1" "(ix), special case", sga "3 IV 2.4" "(a)"]
theorem monomorphisms_descendsAlong_fppf :
    (MorphismProperty.monomorphisms Scheme.{u}).DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _h1 : MorphismProperty.IsStableUnderBaseChange
      (@Surjective.{u} ⊓ @Flat : MorphismProperty Scheme.{u}) := .inf
  have _h2 : MorphismProperty.IsStableUnderBaseChange
      (@Surjective.{u} ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := .inf
  have _hm : (MorphismProperty.monomorphisms Scheme.{u}).DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    MorphismProperty.diagonal_isomorphisms (C := Scheme.{u}).symm ▸ inferInstance
  descendsAlong_fppf_of_descendsAlong_fpqc _

/-- Monomorphisms which are locally of finite type satisfy fppf descent. This is the property
carried by the base changes of the diagonal of the quotient sheaf of an étale equivalence
relation. -/
theorem monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType)
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _hm := monomorphisms_descendsAlong_fppf.{u}
  have _hl : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
  have _hd : MorphismProperty.DescendsAlong (@LocallyOfFiniteType.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of_descendsAlong_fpqc _
  MorphismProperty.DescendsAlong.inf

/-- Monomorphisms which are locally of finite type are Zariski local on the target. -/
theorem monomorphisms_inf_locallyOfFiniteType_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  have _hl : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- A monomorphism of schemes which is locally of finite type is separated, locally quasi-finite
and locally of finite type: it lies in the property of Stacks 02W8. This is the theorem
`monomorphisms_inf_locallyOfFiniteType_le_isSeparated_inf_locallyQuasiFinite` of
`StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent` with the finite-type conjunct
retained. -/
theorem monomorphisms_inf_locallyOfFiniteType_le_stacks02W8 :
    (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) ≤
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) := by
  intro _ _ f hf
  have h₁ : Mono f := hf.1
  have h₂ : LocallyOfFiniteType f := hf.2
  exact ⟨⟨inferInstance, inferInstance⟩, h₂⟩

/-- The property of Stacks 02W8 together with surjectivity and étaleness — the property at which
Stacks 0265 needs effective descent for the chart of a quotient sheaf — satisfies fppf
descent. -/
theorem stacks02W8_inf_surjective_inf_etale_descendsAlong_fppf :
    MorphismProperty.DescendsAlong
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @Surjective ⊓ @Etale :
        MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  have _h1 := isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  have _h2 := Space.surjective_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
  have _h3 := Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.{u}
  have _h4 : MorphismProperty.DescendsAlong
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @Surjective :
        MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := MorphismProperty.DescendsAlong.inf
  MorphismProperty.DescendsAlong.inf

/-- The property of Stacks 02W8 together with surjectivity and étaleness is Zariski local on the
target. -/
theorem stacks02W8_inf_surjective_inf_etale_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @Surjective ⊓ @Etale :
        MorphismProperty Scheme.{u}) :=
  have _h1 := isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _he : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
  have _h2 : IsZariskiLocalAtTarget
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @Surjective :
        MorphismProperty Scheme.{u}) := MorphismProperty.IsLocalAtTarget.inf _ _
  MorphismProperty.IsLocalAtTarget.inf _ _

/-- The property of Stacks 02W8 together with surjectivity and étaleness is contained in the
property of Stacks 02W8. -/
theorem stacks02W8_inf_surjective_inf_etale_le_stacks02W8 :
    (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @Surjective ⊓ @Etale :
        MorphismProperty Scheme.{u}) ≤
      (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
  fun _ _ _ hf ↦ hf.1.1

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The property half of descent along a covering sieve, unconditionally -/

/-- **The property half of effective descent along a covering sieve, with no descent
hypothesis.** Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let
`h : yoneda.obj a ⟶ Y` be a morphism from a representable presheaf whose base change of `f` is
*already known to be representable*, and let `T` be a covering sieve of `a`. If the base change
of `f` along `yoneda.map q ≫ h` is representable with a property `Q` which is Zariski local on
the target and descends along the surjective flat morphisms of finite presentation, for every
arrow `q` of `T`, then the base change of `f` along `h` is representable with `Q`.

This is the covering-sieve analogue of
`AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart_of_descendsAlong`, and the one place
where the two predicates genuinely differ. For a single surjective étale covering morphism `q`
the property descends along `q` itself, which is a one-element fppf covering of the site. Along
a covering sieve there is no such morphism inside the site, so the descent is performed over the
*schemes* underlying the arrows of the sieve, by
`AlgebraicGeometry.of_jointlySurjective_flat_locallyOfFinitePresentation` applied to the family
of arrows supplied by `AlgebraicGeometry.BigFppfOver.exists_mem_of_mem_topology`: the base
change of the descended morphism along an arrow `r` of the pulled-back sieve is the fibre
product in the site of the two representables, which the hypothesis at `r ≫ k` describes. -/
theorem presheaf_of_coveringSieve_of_descendsAlong {Q : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget Q]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {a : BigFppfOver B S hS}
    (h : yoneda.obj a ⟶ Y) (hrep : yoneda.relativelyRepresentable (pullback.snd f h))
    {T : Sieve a} (hTmem : T ∈ BigFppfOver.topology B S hS a)
    (hall : ∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd f (yoneda.map q ≫ h))) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _hri : MorphismProperty.RespectsIso (Q.inverseImage (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hrep fun a' k ↦ ?_
  obtain ⟨k', rfl⟩ := yoneda.map_surjective k
  show Q ((BigFppfOver.toScheme B S hS).map (hrep.snd (yoneda.map k')))
  set v : hrep.pullback (yoneda.map k') ⟶ a' := hrep.snd (yoneda.map k') with hv
  refine of_jointlySurjective_flat_locallyOfFinitePresentation _ fun x ↦ ?_
  obtain ⟨c, r, hr, hrf, hrp, hx⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS
    ((BigFppfOver.topology B S hS).pullback_stable k' hTmem) x
  have sq1 : IsPullback (hrep.fst (yoneda.map k') ≫ pullback.fst f h) (yoneda.map v) f
      (yoneda.map k' ≫ h) :=
    (hrep.isPullback (yoneda.map k')).paste_horiz (IsPullback.of_hasPullback f h)
  have sq2 : IsPullback (yoneda.map (pullback.fst v r) ≫
        hrep.fst (yoneda.map k') ≫ pullback.fst f h)
      (yoneda.map (pullback.snd v r)) f (yoneda.map (r ≫ k') ≫ h) := by
    rw [Functor.map_comp, Category.assoc]
    exact ((IsPullback.of_hasPullback v r).map yoneda).paste_horiz sq1
  have hq2 := snd_of_isPullback_of_isPullback (IsPullback.of_hasPullback f _) sq2
    (hall (r ≫ k') hr)
  refine ⟨_, (BigFppfOver.toScheme B S hS).map r, _,
    (BigFppfOver.toScheme B S hS).map (pullback.fst v r),
    (BigFppfOver.toScheme B S hS).map (pullback.snd v r),
    (IsPullback.of_hasPullback v r).map (BigFppfOver.toScheme B S hS), hrf, hrp, hx, ?_⟩
  exact MorphismProperty.of_relative_map
    (P := Q.inverseImage (BigFppfOver.toScheme B S hS)) (F := yoneda) hq2

/-! ### Descent along a covering sieve, for a morphism to a representable presheaf -/

/-- **Descent along a covering sieve of representability by morphisms with `Q`.** A morphism to
a representable presheaf out of a sheaf is represented by morphisms with `Q` as soon as its base
change along every arrow of some covering sieve of the base is, provided morphisms with `Q`
descend effectively along covering sieves. -/
theorem presheaf_of_coveringSieve {Q : MorphismProperty Scheme.{u}}
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS Q)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U : BigFppfOver B S hS} (a : F ⟶ yoneda.obj U)
    {T : Sieve U} (hT : T ∈ BigFppfOver.topology B S hS U)
    (hall : ∀ ⦃V : BigFppfOver B S hS⦄ (q : V ⟶ U), T q →
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd a (yoneda.map q))) :
    (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf a := by
  have hall' : ∀ ⦃V : BigFppfOver B S hS⦄ (q : V ⟶ U), T q →
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd a (yoneda.map q ≫ 𝟙 (yoneda.obj U))) := by
    have hcongr : ∀ {V : BigFppfOver B S hS} {g g' : yoneda.obj V ⟶ yoneda.obj U}, g = g' →
        (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd a g) →
        (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd a g') := by
      rintro V g g' rfl h
      exact h
    exact fun V q hq => hcongr (Category.comp_id _).symm (hall q hq)
  have h0 := hdesc a hF (BigFppfOver.isSheaf_yoneda_obj B S hS U) (𝟙 (yoneda.obj U)) T hT hall'
  have hid : IsPullback (𝟙 F) a a (𝟙 (yoneda.obj U)) := IsPullback.of_id_fst
  exact snd_of_isPullback_of_isPullback (IsPullback.of_hasPullback a _) hid h0

/-! ### Transferring the hypothesis between properties -/

/-- **Effective descent along the covering sieves of the big fppf site of `S` at a property `P`
implies it at every property `Q ≤ P` which is Zariski local on the target and descends along the
surjective flat morphisms of finite presentation.** This is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le` for the covering-sieve
predicate: the smaller property still supplies the representability of the descended morphism
through `P`, and is then recovered on it by
`AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`. -/
theorem isEffectiveDescentAlongCoveringSieve_of_le {P Q : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget Q]
    [Q.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS P) (hQP : Q ≤ P) :
    IsEffectiveDescentAlongCoveringSieve B S hS Q := by
  intro X Y f hX hY a h T hTmem hall
  have hP := hdesc f hX hY h T hTmem fun _ q hq ↦
    MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hQP) _ (hall q hq)
  exact presheaf_of_coveringSieve_of_descendsAlong h hP.rep hTmem hall

/-! ### Glueing the descended pieces -/

/-- **Descent, Lemma 35.35.13 in the shape of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`**, which is Tag 0AP4: the
glueing step of Stacks 02W8, for the covering sieves of the site. Effective descent along the
covering sieves follows from producing, for each descent datum along a covering sieve, a Zariski
covering of the descended sheaf by representable open subfunctors, indexed by a type smaller
than the cofinality of the site's cutoff.

This is `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover` for the
covering-sieve predicate, and it carries no `HasZariskiGluing` hypothesis: that is now proved
outright, as `AlgebraicGeometry.hasZariskiGluing`. Nothing beyond the covering is needed: the
fibre product `X ×[Y] yoneda.obj a` whose representability is at stake is a sheaf, by
`AlgebraicGeometry.BigFppfOver.isSheaf_pullback_yoneda_obj`, so the covering makes it
representable by `AlgebraicGeometry.isRepresentable_of_zariskiCover_of_lt_cof`; and the property
`P` of the descended morphism is then recovered from the datum by
`AlgebraicGeometry.Space.presheaf_of_coveringSieve_of_descendsAlong`. In particular the pieces of
the covering are *not* required to carry `P`, which matters because the covering of Stacks 02W8
is a covering of the *source*, and separatedness is not Zariski local there. -/
theorem isEffectiveDescentAlongCoveringSieve_of_zariskiCover {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
            (pullback.snd f (yoneda.map q ≫ h))) →
        ∃ (ι : Type u) (_ : Nonempty ι), Cardinal.mk ι < B.cutoff.ord.cof ∧
          ∃ (W : ι → BigFppfOver B S hS) (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h),
            (∀ i, IsOpenImmersion B S hS (k i)) ∧
              Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    IsEffectiveDescentAlongCoveringSieve B S hS P := by
  intro X Y f hX hY a h T hTmem hall
  obtain ⟨ι, hne, hι, W, k, hk, hksurj⟩ := H f hX hY h T hTmem hall
  have hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hrep : (pullback f h).IsRepresentable :=
    isRepresentable_of_zariskiCover_of_lt_cof B S hS hF hι W k hk hksurj
  set e := (pullback f h).reprW with he
  set p := yoneda.preimage (e.hom ≫ pullback.snd f h) with hp
  have hmap : yoneda.map p = e.hom ≫ pullback.snd f h := by rw [hp, Functor.map_preimage]
  have hfac : pullback.snd f h = e.inv ≫ yoneda.map p := by
    rw [hmap, Iso.inv_hom_id_assoc]
  have hrep' : yoneda.relativelyRepresentable (pullback.snd f h) := by
    rw [hfac]
    exact MorphismProperty.comp_mem _ _ _ (Functor.relativelyRepresentable.of_isIso _ _)
      (Functor.relativelyRepresentable.map yoneda p)
  exact presheaf_of_coveringSieve_of_descendsAlong h hrep' hTmem hall

/-- **The descent hypothesis which the diagonal of a quotient sheaf needs, from the single
instance at the property of Stacks 02W8.** Effective descent along the covering sieves of the
big fppf site of `S` for the separated, locally quasi-finite morphisms which are locally of
finite type implies it for the monomorphisms locally of finite type, which is the hypothesis of
`AlgebraicGeometry.Space.relativelyRepresentable_diag_quotientSheaf`. -/
theorem isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  have _h1 := monomorphisms_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  isEffectiveDescentAlongCoveringSieve_of_le hdesc
    monomorphisms_inf_locallyOfFiniteType_le_stacks02W8

/-- **The descent hypothesis which the chart of a quotient sheaf needs, from the single instance
at the property of Stacks 02W8.** Effective descent along the covering sieves of the big fppf
site of `S` for the separated, locally quasi-finite morphisms which are locally of finite type
implies it for that property together with surjectivity and étaleness, which is the hypothesis
of `AlgebraicGeometry.Space.presheaf_surjective_quotientChart` and of
`AlgebraicGeometry.Space.presheaf_etale_quotientChart`. -/
theorem isEffectiveDescentAlongCoveringSieve_quotientChart
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})) :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
  have _h1 := stacks02W8_inf_surjective_inf_etale_isZariskiLocalAtTarget.{u}
  have _h2 := stacks02W8_inf_surjective_inf_etale_descendsAlong_fppf.{u}
  isEffectiveDescentAlongCoveringSieve_of_le hdesc
    stacks02W8_inf_surjective_inf_etale_le_stacks02W8

/-! ### The three conclusions of Stacks 0265 from one hypothesis -/

section Quotient

variable (B) (S) (hS) (U : BigFppfOver B S hS)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {R : Over S}
  (j : Stacks.Groupoids.PreRelation R ((Over.post B.inclusion).obj U))
  [Stacks.Groupoids.IsEtaleEquivalenceRelation j]

/-- **Stacks 0265, surjectivity of the quotient map**, conditional on effective descent along
the covering sieves of the big fppf site of `S` at the property of Stacks 02W8 and on nothing
else.

This is `AlgebraicGeometry.Space.surjective_toQuotientSheaf` with its hypothesis, descent at the
property of Stacks 02W8 together with surjectivity and étaleness, replaced by descent at the
property of Stacks 02W8 itself, by
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_quotientChart`. It does
**not** carry `@[stacks 0265]`: the descent hypothesis is undischarged. -/
theorem surjective_toQuotientSheaf_of_coveringSieveDescent
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  surjective_toQuotientSheaf B S hS U j
    (isEffectiveDescentAlongCoveringSieve_quotientChart hdesc)

/-- **Stacks 0265, étaleness of the quotient map**, conditional on effective descent along the
covering sieves of the big fppf site of `S` at the property of Stacks 02W8 and on nothing else.
It does **not** carry `@[stacks 0265]`: the descent hypothesis is undischarged. -/
theorem etale_toQuotientSheaf_of_coveringSieveDescent
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  etale_toQuotientSheaf B S hS U j
    (isEffectiveDescentAlongCoveringSieve_quotientChart hdesc)

/-- **Stacks 0265, the algebraic-space property**, conditional on effective descent along the
covering sieves of the big fppf site of `S` at the property of Stacks 02W8 and on nothing else.

`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` takes two instances of the descent
hypothesis, at two different properties neither of which implies the other: the monomorphisms
locally of finite type for the diagonal, and the property of Stacks 02W8 together with
surjectivity and étaleness for the chart. Both are contained in the property of Stacks 02W8 and
satisfy fppf descent, so both follow from the single instance at that property. It does **not**
carry `@[stacks 0265]`: the descent hypothesis is undischarged. -/
theorem isAlgebraicSpace_quotientSheaf_of_coveringSieveDescent
    (hdesc : IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})) :
    IsAlgebraicSpace B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType hdesc)
    (isEffectiveDescentAlongCoveringSieve_quotientChart hdesc)

end Quotient

end Space

end AlgebraicGeometry

end
