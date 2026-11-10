module

public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleArbitraryBaseFpqc

/-!
# The covering hypothesis of Tag 0GN7 at the affine objects is independent of Tag 03OJ

`Stacks.Sites.bijective_associatedModuleMap_of_mem_fpqcPrecoverage` proves Descent, Lemma 0GN7
over an arbitrary base on a site of schemes over `S` presented by a precoverage `K` and a functor
`toOver : C ⥤ Over S` whose covering families become fpqc covering families of schemes.  It
carries exactly one hypothesis beyond the data of the site, namely

```
hcover : ∀ X : C, Sieve.coverByImage
  (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ K.toGrothendieck X
```

— the arrows factoring through an object whose **underlying scheme is affine** cover every
object.  This file settles whether that hypothesis follows from the four conditions of Tag 03OJ.

## The verdict: it does not

The four conditions of Tag 03OJ constrain the *coverings* of the site and the *shape* of the
functor to the schemes over `S`; not one of them asserts that any object of the site has affine
underlying scheme.  Two theorems make that precise, one here and one in
`StacksFrontier.AlgebraicGeometry.Topologies.NonaffineZariskiRefinement`.

`Stacks.Sites.not_coverByImage_isAffine_mem_toGrothendieck` is the mechanism: on **any** site
whose covering families become fpqc covering families of schemes — which is condition (4) —
`hcover` *fails* at every object with a point, as soon as every object of the site whose
underlying scheme is affine has empty underlying scheme.  An fpqc covering family is jointly
surjective, so a covering sieve must contain an arrow in whose image a given point of the base
lies; if every arrow of the sieve factors through an affine object, that point lies in the image
of an empty scheme.

`AlgebraicGeometry.exists_nonaffine_flat_quasiCompact_cover` is the other half: inside every open
neighbourhood of every point of a quasi-separated scheme there is the image of a flat,
quasi-compact morphism whose source is quasi-compact, quasi-separated and **not** affine — the
punctured plane over the ring of functions of an affine open.  So condition (2) is satisfiable by
refining families consisting entirely of non-affine objects: refine a Zariski covering `R` of an
object by one such morphism through each point, each of which factors through the member of `R`
inside which its image lies.  Condition (4) holds of those morphisms, being flat and
quasi-compact; condition (3) is had by taking the base `S` itself non-affine and quasi-separated,
for instance the punctured plane over a field or
`AlgebraicGeometry.not_isAffine_projectiveLine`; and the full-subcategory half of condition (1)
by taking `C` to be a full subcategory of `Over S`.

**What is not formalized**, and is the only thing between these two theorems and a single
existential statement, is the assembly: packaging the refining families into one
`CategoryTheory.Precoverage` on one category and checking condition (2) against it.  That asks
for the quasi-compactness factor of `AlgebraicGeometry.Scheme.qcPrecoverage` —
`AlgebraicGeometry.QuasiCompactCover`, a condition on a *family*, available in this tree only at
a presieve presented as a `CategoryTheory.Presieve.ofArrows` — and for the essential smallness of
condition (1), which on the full subcategory of the non-affine objects of `Over S` needs the
closure of `S` under "affine open, then punctured plane over its ring of functions" cut down to a
small set of objects.  Neither step can produce an object with affine underlying scheme, which is
the only thing `hcover` asks for.

What condition (2) does supply is the covering at `Stacks.Sites.OverAffineOpen`, the objects whose
structure morphism has image inside an affine open of `S`
(`Stacks.Sites.coverByImage_overAffineOpen_mem`), and the implementation notes of
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineOpenCovering` record why the
regress from that class to the affine objects does not terminate: refinement in the sense of
Sites, Definition 00VV is *factorization* through a member of the Zariski covering, and a
factorization through an open immersion with affine source does not identify that source with the
underlying scheme of an object of `C`.

## The fifth condition

`Stacks.Sites.HasAffineObjectCover` is the hypothesis that repairs the gap, and it is what holds
on each of the five sites of Tag 03DU: the affine opens of the underlying scheme of an object are
themselves objects of the site.  Stated as the existence, through every point of every object, of
an arrow from an object with affine underlying scheme whose image is an open immersion, it
combines with condition (2) — and with the fullness and faithfulness of `toOver`, which is
condition (1) — to give `hcover` as a theorem:
`Stacks.Sites.coverByImage_isAffine_mem_of_hasAffineObjectCover`.  The three clauses of Tag 0GN7
are then restated on it below, so that the lemma is consumable from conditions (1)–(5) with no
covering hypothesis carried.

The two facts together are the precise statement of the gap: `hcover` is **equivalent**, over
conditions (1), (2) and (4), to a condition on the objects of the site which Tag 03OJ does not
state, and which its own examples in Tag 03DU all satisfy.

## Main definitions

* `Stacks.Sites.HasAffineObjectCover`: **the fifth condition** — through every point of every
  object there is an arrow from an object with affine underlying scheme whose image downstairs is
  an open immersion.
* `Stacks.Sites.affineObjectPresieve`: the Zariski covering of the underlying scheme of an object
  which that condition supplies.

## Main results

* `AlgebraicGeometry.Scheme.fpqcTopology_le_jointlySurjectiveTopology` and
  `AlgebraicGeometry.Scheme.exists_mem_arrows_of_mem_fpqcTopology`: **an fpqc covering sieve of
  schemes is jointly surjective.**
* `Stacks.Sites.not_coverByImage_isAffine_mem_toGrothendieck`: **the covering hypothesis of Tag
  0GN7 at the affine objects fails on a site with no nonempty affine objects**, granted only
  condition (4).  With `Stacks.Sites.not_coverByImage_isAffine_of_forall_not_isAffine` as the
  form in which no affine object exists at all.
* `Stacks.Sites.coverByImage_isAffine_mem_of_hasAffineObjectCover`: **conditions (1), (2) and (5)
  give the covering hypothesis.**
* `Stacks.Sites.bijective_associatedModuleMap_of_hasAffineObjectCover`,
  `Stacks.Sites.full_associatedModuleFunctor_of_hasAffineObjectCover` and
  `Stacks.Sites.faithful_associatedModuleFunctor_of_hasAffineObjectCover`: **Descent, Lemma 0GN7
  over an arbitrary base on a site satisfying conditions (1)–(5)**, with the covering hypothesis
  discharged.

## Implementation notes

No `@[stacks]` attribute is claimed.  The negative result is a statement about the formalization
and not an assertion of the source; the fifth condition is a hypothesis that the source leaves
implicit; and the three clauses of Tag 0GN7 restated at the end are the registrations already
carried by `StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleArbitraryBaseFpqc`, read at
a different hypothesis.

`Stacks.Sites.not_coverByImage_isAffine_mem_toGrothendieck` is proved through the *topology* and
not through the precoverage.  `CategoryTheory.Precoverage.toGrothendieck` is an inductive
saturation — `CategoryTheory.Precoverage.Saturate`, with constructors for the generating families,
the maximal sieve, pullback and transitivity — so a covering sieve of `K.toGrothendieck` need not
be refined by a single member of `K`, and condition (4) cannot be read off it directly.  What
does transport is cover preservation:
`Stacks.Sites.coverPreserving_toScheme_of_mem_fpqcPrecoverage` already pushes every covering sieve
of the site forward to an fpqc covering sieve of schemes, and joint surjectivity is available
there because `AlgebraicGeometry.Scheme.fpqcPrecoverage` is
`AlgebraicGeometry.Scheme.propQCPrecoverage @AlgebraicGeometry.Flat`, whose flat factor is an
intersection with the jointly surjective precoverage.

The hypothesis of the negative result is that every affine object is *empty*, rather than that
none is affine.  The weaker form is what the proof gives and is strictly more general: a site may
contain the empty scheme — which is affine, being `Spec 0` — without the arrows out of it
covering anything, since their images are empty.  So adjoining empty objects to a site does not
repair `hcover`, and a witness to the independence is free to contain them.

`Stacks.Sites.affineObjectPresieve` records the factorization through the arrow of the site
explicitly, with an arbitrary morphism `k` to the affine object rather than an isomorphism.  That
is what survives the factoring form of refinement: condition (2) hands back a factorization of
`toOver.map q` through a member of the presieve, and composing the two legs gives a morphism to
the affine object which fullness lifts to an arrow of `C` and faithfulness identifies with `q`.
This is exactly the step that `Stacks.Sites.OverAffineOpen` cannot perform, and it is available
here only because the presieve carries the arrow of the site inside it.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- **The fpqc topology on schemes is contained in the jointly surjective topology.**  The fpqc
precoverage is `AlgebraicGeometry.Scheme.propQCPrecoverage @AlgebraicGeometry.Flat`, whose second
factor is an intersection with the jointly surjective precoverage; generating a topology is
monotone. -/
public theorem fpqcTopology_le_jointlySurjectiveTopology :
    Scheme.fpqcTopology.{u} ≤ Scheme.jointlySurjectiveTopology.{u} := by
  rw [Scheme.jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology]
  change Scheme.fpqcTopology ≤
    Scheme.jointlySurjectivePrecoverage.toPretopology.toGrothendieck
  rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  exact Precoverage.toGrothendieck_mono
    ((Scheme.propQCPrecoverage_le_precoverage (P := @Flat)).trans inf_le_left)

/-- **An fpqc covering sieve of schemes is jointly surjective**: every point of the base is in the
image of one of its arrows. -/
public theorem exists_mem_arrows_of_mem_fpqcTopology {X : Scheme.{u}} {R : Sieve X}
    (hR : R ∈ Scheme.fpqcTopology.{u} X) (x : X) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ X), R.arrows g ∧ x ∈ Set.range g.base := by
  have hcov := fpqcTopology_le_jointlySurjectiveTopology _ hR
  rw [Scheme.mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology] at hcov
  change R.arrows ∈ Scheme.jointlySurjectivePrecoverage X at hcov
  rw [Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hcov
  exact hcov x

end AlgebraicGeometry.Scheme

namespace Stacks.Sites

open _root_.AlgebraicGeometry

section Negative

variable {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C] {S : Scheme.{u}}
  (K : Precoverage C) (toOver : C ⥤ Over S)
  [PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S)]

/-- **The covering hypothesis of Descent, Lemma 0GN7 at the objects with affine underlying scheme
is not a consequence of the conditions of Tag 03OJ.**  On a site of schemes over `S` whose
covering families become fpqc covering families of schemes — condition (4) of that tag — the sieve
of arrows factoring through an object with affine underlying scheme is *not* a covering sieve of
any object with a point, as soon as every object whose underlying scheme is affine has empty
underlying scheme.

Covering sieves of the site push forward to fpqc covering sieves of schemes
(`Stacks.Sites.coverPreserving_toScheme_of_mem_fpqcPrecoverage`), and an fpqc covering sieve is
jointly surjective, so the point `x` would lie in the image of an arrow of the pushforward.  Such
an arrow factors through `toOver.map q` for an arrow `q` of the sieve, and `q` in turn factors
through an object `Y` with affine underlying scheme; so the underlying scheme of `Y` receives a
point, and is not empty. -/
public theorem not_coverByImage_isAffine_mem_toGrothendieck
    (hfpqc : ∀ ⦃T : C⦄ (R : Presieve T), R ∈ K T →
      Presieve.map (toOver ⋙ Over.forget S) R ∈
        Scheme.fpqcPrecoverage.{u} ((toOver ⋙ Over.forget S).obj T))
    (hempty : ∀ Y : C, IsAffine (toOver.obj Y).left → IsEmpty (toOver.obj Y).left)
    (X : C) (x : (toOver.obj X).left) :
    Sieve.coverByImage (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X
      ∉ K.toGrothendieck X := by
  intro hmem
  have hpush :=
    (coverPreserving_toScheme_of_mem_fpqcPrecoverage K toOver hfpqc).cover_preserve hmem
  obtain ⟨Z, g, hg, hx⟩ := Scheme.exists_mem_arrows_of_mem_fpqcTopology hpush x
  obtain ⟨W, q, k, hq, rfl⟩ := hg
  obtain ⟨⟨⟨Y, hY⟩, l, h, -⟩⟩ := hq
  obtain ⟨z, -⟩ := hx
  exact (hempty Y hY).false (((toOver ⋙ Over.forget S).map l).base (k.base z))

/-- **The covering hypothesis of Descent, Lemma 0GN7 fails on a site of schemes over `S` whose
coverings are fpqc coverings and which has no object with affine underlying scheme.**  This is
`Stacks.Sites.not_coverByImage_isAffine_mem_toGrothendieck` in the form in which no affine object
exists at all. -/
public theorem not_coverByImage_isAffine_of_forall_not_isAffine
    (hfpqc : ∀ ⦃T : C⦄ (R : Presieve T), R ∈ K T →
      Presieve.map (toOver ⋙ Over.forget S) R ∈
        Scheme.fpqcPrecoverage.{u} ((toOver ⋙ Over.forget S).obj T))
    (hno : ∀ Y : C, ¬ IsAffine (toOver.obj Y).left)
    (X : C) (x : (toOver.obj X).left) :
    Sieve.coverByImage (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X
      ∉ K.toGrothendieck X :=
  not_coverByImage_isAffine_mem_toGrothendieck K toOver hfpqc
    (fun Y hY => absurd hY (hno Y)) X x

end Negative

section Positive

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-- **The fifth condition that Tag 03OJ leaves implicit: the affine opens of an object are objects
of the site.**  Through every point of the underlying scheme of every object there is an arrow of
the site from an object with affine underlying scheme, whose image downstairs is an open
immersion.

On each of the five sites of Tag 03DU this holds because the affine opens of the underlying scheme
of an object are themselves objects of the site, with the open immersions between them as arrows.
It is not a consequence of conditions (1)–(4): see
`Stacks.Sites.not_coverByImage_isAffine_mem_toGrothendieck`. -/
public def HasAffineObjectCover : Prop :=
  ∀ (X : C) (x : (toOver.obj X).left), ∃ (Y : C) (h : Y ⟶ X),
    IsAffine (toOver.obj Y).left ∧ IsOpenImmersion ((toOver ⋙ Over.forget S).map h) ∧
      x ∈ Set.range ((toOver ⋙ Over.forget S).map h).base

/-- The presieve on the underlying scheme of `X` of open immersions which factor through the image
of an arrow of the site whose source has affine underlying scheme.

The arrow of the site is recorded inside the presieve, which is what makes the factoring form of
refinement usable at the affine objects: a factorization through a member of this presieve is a
factorization through `toOver.map h` for an arrow `h` of `C`. -/
public def affineObjectPresieve (X : C) : Presieve ((toOver.obj X).left) :=
  fun ⦃Z⦄ j => IsOpenImmersion j ∧ ∃ (Y : C) (h : Y ⟶ X), IsAffine (toOver.obj Y).left ∧
    ∃ k : Z ⟶ (toOver.obj Y).left, j = k ≫ ((toOver ⋙ Over.forget S).map h)

/-- **`Stacks.Sites.affineObjectPresieve` is a Zariski covering**, granted the fifth condition.
Its members are open immersions by construction, and joint surjectivity is the content of the
condition, read at the arrow itself with `k = 𝟙`. -/
public theorem affineObjectPresieve_mem_zariskiPrecoverage
    (haff : HasAffineObjectCover S toOver) (X : C) :
    affineObjectPresieve S toOver X ∈
      Scheme.zariskiPrecoverage.{u} ((toOver.obj X).left) := by
  refine ⟨fun x => ?_, fun {Z} j hj => hj.1⟩
  obtain ⟨Y, h, hY, hoi, hx⟩ := haff X x
  exact ⟨Scheme.forget.obj (toOver.obj Y).left,
    Scheme.forget.map ((toOver ⋙ Over.forget S).map h),
    Presieve.map_map (F := Scheme.forget)
      (show affineObjectPresieve S toOver X ((toOver ⋙ Over.forget S).map h) from
        ⟨hoi, Y, h, hY, 𝟙 _, (Category.id_comp _).symm⟩),
    hx⟩

variable (K : Precoverage C)

/-- **Conditions (1), (2) and (5) of Tag 03OJ give the covering hypothesis of Descent, Lemma
0GN7 at the objects with affine underlying scheme.**

Refine `Stacks.Sites.affineObjectPresieve` by a covering family `Q` of the site, which condition
(2) permits.  Each member `q` of `Q` has `toOver.map q` factoring as `k ≫ m ≫ toOver.map h` with
`h` an arrow of the site whose source `Y` has affine underlying scheme.  The composite `k ≫ m` is
a morphism over `S`, because `toOver.map h` and `toOver.map q` are; fullness of `toOver` lifts it
to an arrow `n : W ⟶ Y` of the site, and faithfulness identifies `n ≫ h` with `q`.  So `q`, and
with it every arrow of the sieve generated by `Q`, factors through `Y`. -/
public theorem coverByImage_isAffine_mem_of_hasAffineObjectCover [toOver.Full] [toOver.Faithful]
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (haff : HasAffineObjectCover S toOver) (X : C) :
    Sieve.coverByImage (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X
      ∈ K.toGrothendieck X := by
  obtain ⟨Q, hQ, hQle⟩ := hZariski X (affineObjectPresieve S toOver X)
    (affineObjectPresieve_mem_zariskiPrecoverage S toOver haff X)
  refine K.toGrothendieck.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck hQ)
  rintro Z f ⟨W, l, q, hq, rfl⟩
  obtain ⟨Z', k, j, ⟨-, Y, h, hY, m, rfl⟩, hfac⟩ :=
    hQle _ _ (Presieve.map_map (F := toOver ⋙ Over.forget S) hq)
  have h1 : (toOver ⋙ Over.forget S).map h ≫ (toOver.obj X).hom = (toOver.obj Y).hom :=
    Over.w (toOver.map h)
  have h2 : (toOver ⋙ Over.forget S).map q ≫ (toOver.obj X).hom = (toOver.obj W).hom :=
    Over.w (toOver.map q)
  have hw : (k ≫ m) ≫ (toOver.obj Y).hom = (toOver.obj W).hom := by
    rw [← h1, ← h2, ← hfac]
    simp
  obtain ⟨n, hn⟩ := toOver.map_surjective (Over.homMk (k ≫ m) hw)
  have hnh : n ≫ h = q := by
    refine toOver.map_injective (Over.OverMorphism.ext ?_)
    rw [toOver.map_comp, hn]
    change (k ≫ m) ≫ (toOver ⋙ Over.forget S).map h = (toOver ⋙ Over.forget S).map q
    rw [Category.assoc, hfac]
  exact ⟨⟨⟨Y, hY⟩, l ≫ n, h, by rw [Category.assoc, hnh]⟩⟩

end Positive

section Fpqc

variable {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C] {S : Scheme.{u}}
  (K : Precoverage C) (toOver : C ⥤ Over S)
  [PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S)]
  [K.HasPullbacks] [K.IsStableUnderBaseChange] [toOver.Full] [toOver.Faithful]

variable (hfpqc : ∀ ⦃T : C⦄ (R : Presieve T), R ∈ K T →
  Presieve.map (toOver ⋙ Over.forget S) R ∈
    Scheme.fpqcPrecoverage.{u} ((toOver ⋙ Over.forget S).obj T))

variable (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
  R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
    ∃ Q : Presieve T, Q ∈ K T ∧
      Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)

variable (haff : HasAffineObjectCover S toOver)

include hfpqc hZariski haff

/-- **Descent, Lemma 0GN7 over an arbitrary base, on a site of schemes over `S` satisfying the
four conditions of Tag 03OJ together with the fifth condition
`Stacks.Sites.HasAffineObjectCover`.**  The covering hypothesis that
`Stacks.Sites.bijective_associatedModuleMap_of_mem_fpqcPrecoverage` carries is discharged by
`Stacks.Sites.coverByImage_isAffine_mem_of_hasAffineObjectCover`. -/
public theorem bijective_associatedModuleMap_of_hasAffineObjectCover
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀))
    (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  bijective_associatedModuleMap_of_mem_fpqcPrecoverage K toOver hfpqc
    (coverByImage_isAffine_mem_of_hasAffineObjectCover S toOver K hZariski haff) X₀ hterm M N

/-- **Descent, Lemma 0GN7 over an arbitrary base, faithfulness clause, on a site satisfying the
four conditions of Tag 03OJ together with `Stacks.Sites.HasAffineObjectCover`.** -/
public theorem faithful_associatedModuleFunctor_of_hasAffineObjectCover
    (X₀ : C) [IsIso (toOver.obj X₀).hom] :
    (associatedModuleFunctor S toOver).Faithful :=
  faithful_associatedModuleFunctor_of_mem_fpqcPrecoverage K toOver hfpqc
    (coverByImage_isAffine_mem_of_hasAffineObjectCover S toOver K hZariski haff) X₀

/-- **Descent, Lemma 0GN7 over an arbitrary base, fullness clause, on a site satisfying the four
conditions of Tag 03OJ together with `Stacks.Sites.HasAffineObjectCover`.** -/
public theorem full_associatedModuleFunctor_of_hasAffineObjectCover
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    (associatedModuleFunctor S toOver).Full :=
  full_associatedModuleFunctor_of_mem_fpqcPrecoverage K toOver hfpqc
    (coverByImage_isAffine_mem_of_hasAffineObjectCover S toOver K hZariski haff) X₀ hterm

end Fpqc

end Stacks.Sites

end
