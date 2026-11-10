module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence

/-!
# The affine schemes of a site of algebraic spaces generate

An algebraic space is covered étale-locally by *affine schemes*, never by affine algebraic
spaces: affineness is not a property an object of a site of algebraic spaces has, but the
property of being representable by a scheme with affine total space. This file states the
resulting density for the three sites of algebraic spaces — the big fppf site and the big étale
site of an algebraic space, and its spaces-étale site — in the form a cohomological covering
criterion consumes: the arrows out of the objects representable by an affine scheme generate a
covering sieve of every object.

The covering family is indexed by the points of the object: through each point of an algebraic
space there is an affine scheme of the chosen big fppf site of schemes, étale over the space and
hitting that point. For the spaces-étale site that family is a covering family on the nose, the
covering condition there being joint surjectivity on points. On the two big sites, whose chosen
families carry a cardinality bound, the family is an étale covering, hence also an fppf covering
by Stacks 0DFC, and a chosen combinatorially equivalent representative of it generates the same
presieve.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceOver.IsAffineSchemeOver`,
  `AlgebraicGeometry.BigEtaleSpaceSite.IsAffineSchemeOver` and
  `AlgebraicGeometry.Space.SpacesEtale.IsAffineScheme`: the objects of the big fppf site, of the
  big étale site of an algebraic space, resp. of its spaces-étale site that are representable by
  a scheme of the big fppf site of schemes with affine total space.
* `AlgebraicGeometry.BigFppfSpaceOver.affineSchemePresieve`,
  `AlgebraicGeometry.BigEtaleSpaceSite.affineSchemePresieve` and
  `AlgebraicGeometry.Space.SpacesEtale.affineSchemePresieve`: the arrows out of those objects.

## Main results

* `AlgebraicGeometry.Space.exists_isEtaleCovering_affine`: every algebraic space over `S` admits
  an étale covering, indexed by its points, whose members are affine schemes of the big fppf
  site of `S`.
* `AlgebraicGeometry.BigFppfSpaceOver.generate_affineSchemePresieve_mem`: **the objects
  representable by an affine scheme generate a covering sieve of the big fppf topology of an
  algebraic space.**
* `AlgebraicGeometry.BigEtaleSpaceSite.generate_affineSchemePresieve_mem` and
  `AlgebraicGeometry.Space.SpacesEtale.generate_affineSchemePresieve_mem`: **the same for the
  big étale site and for the spaces-étale site of an algebraic space.**

## Implementation notes

The witnessing predicates are stated with an isomorphism to the algebraic space represented by
an affine scheme, not with an equality of objects: the generated sieve is unchanged, and a
consumer of the density statement transports a cohomological vanishing along the isomorphism.
Both proofs produce the identity isomorphism, the members of the covering family being
representable objects by construction.

The index type of the covering family is the point set of the object, which lies in
`Type (u + 1)`. That is exactly the index universe of the covering families of the spaces-étale
site; the families of a big site of algebraic spaces are indexed in `Type (u + 2)`, so there
the point set is raised by `ULift` before the family is formed.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 0DBW](https://stacks.math.columbia.edu/tag/0DBW)
* [Stacks Project, Tag 0DBY](https://stacks.math.columbia.edu/tag/0DBY)
* [Stacks Project, Tag 0DFC](https://stacks.math.columbia.edu/tag/0DFC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Every algebraic space over `S` is covered by affine schemes in the étale topology.**
Through each point of the space there is a scheme of the big fppf site of `S` with affine total
space, étale over the space and hitting that point, so the family of those charts, indexed by
the point set, is an étale covering. -/
theorem exists_isEtaleCovering_affine (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ (W : points B S hS F → BigFppfOver B S hS) (b : ∀ x, yoneda.obj (W x) ⟶ F),
      (∀ x, IsAffine ((BigFppfOver.toScheme B S hS).obj (W x))) ∧
      (∀ x, IsEtale B S hS (b x)) ∧
      (∀ x, x ∈ Set.range (pointsMap B S hS (yoneda.obj (W x)) (b x))) ∧
      IsEtaleCovering B S hS (fun x => yoneda.obj (W x)) b := by
  choose W b hWaff hbEt hbpt using
    fun x => exists_affine_etale_chart_at_point B S hS F hF x
  have hbEt' := fun x => isEtale_of_presheaf_etale B S hS (hbEt x)
  exact ⟨W, b, hWaff, hbEt', hbpt,
    { target_isAlgebraicSpace := hF
      source_isAlgebraicSpace := fun x => isAlgebraicSpace_yoneda B S hS (W x)
      etale := hbEt'
      jointly_surjective := Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hbpt x⟩ }⟩

namespace SpacesEtale

variable (X : AlgebraicSpaces B S hS)

/-- The property of an object of the spaces-étale site of `X` that the algebraic space it is
given by is isomorphic to the one represented by a scheme of the big fppf site of `S` with
affine total space. -/
def IsAffineScheme : ObjectProperty (SpacesEtale B S hS X) :=
  fun U ↦ ∃ W : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
    Nonempty ((schemeSpaceFunctor B S hS).obj W ≅ (toSpaces B S hS X).obj U)

/-- The presieve of all arrows into an object of the spaces-étale site of `X` whose source is
representable by a scheme with affine total space. -/
def affineSchemePresieve (U : SpacesEtale B S hS X) : Presieve U :=
  fun {V} _ ↦ IsAffineScheme B S hS X V

/-- **Every object of the spaces-étale site of `X` is covered by its objects representable by
an affine scheme.**  The affine étale charts through the points of the object, composed with
its structure morphism to `X`, are objects of the site, and the resulting family is covering
because the covering families of the spaces-étale site are the jointly point-surjective
ones. -/
theorem generate_affineSchemePresieve_mem (U : SpacesEtale B S hS X) :
    Sieve.generate (affineSchemePresieve B S hS X U) ∈ topology B S hS X U := by
  obtain ⟨W, b, hWaff, hbEt, hbpt, -⟩ := exists_isEtaleCovering_affine B S hS
    ((toSpaces B S hS X).obj U).1 ((toSpaces B S hS X).obj U).2
  have hcEt : ∀ x, IsEtaleOver B S hS X
      (Over.mk ((ObjectProperty.homMk (b x) :
        (schemeSpaceFunctor B S hS).obj (W x) ⟶ (toSpaces B S hS X).obj U) ≫ U.obj.hom)) := by
    intro x
    change IsEtale B S hS (b x ≫ U.obj.hom.hom)
    exact isEtale_of_presheaf_etale B S hS
      (U.property (W x) (b x) (presheaf_etale_of_isEtale B S hS (hbEt x)))
  let E : PreZeroHypercover.{u + 1} U :=
    { I₀ := points B S hS ((toSpaces B S hS X).obj U).1
      X := fun x ↦ ⟨Over.mk ((ObjectProperty.homMk (b x) :
        (schemeSpaceFunctor B S hS).obj (W x) ⟶ (toSpaces B S hS X).obj U) ≫ U.obj.hom), hcEt x⟩
      f := fun x ↦ ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (b x)) rfl) }
  have hcovE : IsCovering B S hS X ⟨U, E⟩ := fun x ↦ by
    obtain ⟨w, hw⟩ := hbpt x
    exact ⟨x, w, hw⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (Precoverage.generate_mem_toGrothendieck (R := E.presieve₀) ⟨E, rfl, hcovE⟩)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨x⟩
  exact Sieve.le_generate _ _ _ ⟨W x, hWaff x, ⟨Iso.refl _⟩⟩

end SpacesEtale

end Space

/-- A presieve of the slice at `X` is covering for the localization of a topology generated by
chosen covering families, once a covering family `E` of `Y.left` (covering in the sense of `Q`,
which has a chosen representative) has all its arrows into `Y` generating arrows of the presieve. -/
private theorem generate_mem_over_of_covering_representative
    {C : Type*} [Category C] {K : Precoverage C} {IsC Q : Covering.{_, _, u + 2} C → Prop}
    (hK : ∀ {X : C} {R : Presieve X},
      R ∈ K X ↔ ∃ E : PreZeroHypercover.{u + 2} X, R = E.presieve₀ ∧ IsC ⟨X, E⟩)
    (hrep : ∀ E, Q E → ∃ E', IsC E' ∧ Covering.CombEquiv E E') {X : C} {Y : Over X}
    (R : Presieve Y) (E : PreZeroHypercover.{u + 2} Y.left) (hE : Q ⟨Y.left, E⟩)
    (hR : ∀ x : E.I₀, Sieve.generate R (Over.homMk (E.f x) rfl : Over.mk (E.f x ≫ Y.hom) ⟶ Y)) :
    Sieve.generate R ∈ K.toGrothendieck.over X Y := by
  have hgen : Sieve.generate E.presieve₀ ∈ K.toGrothendieck Y.left := by
    obtain ⟨⟨V, F⟩, hF, hleft, hcomb⟩ := hrep ⟨Y.left, E⟩ hE
    cases hleft
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb, hK]
    exact ⟨F, rfl, hF⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine GrothendieckTopology.superset_covering _ ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨x⟩
  rw [Sieve.overEquiv_iff]
  exact hR x

namespace BigFppfSpaceOver

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The property of an object of the big fppf site of an algebraic space `X` of `T` that its
source is isomorphic to the algebraic space represented by a scheme of the chosen big fppf site
of schemes with affine total space. -/
def IsAffineSchemeOver (X : T.Spaces) : ObjectProperty (BigFppfSpaceOver T X) :=
  fun Y ↦ ∃ W : T.Schemes,
    IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj W) ∧
      Nonempty ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj W ≅ Y.left)

/-- The presieve of all arrows into an object of the big fppf site of `X` whose source is
representable by a scheme with affine total space. -/
def affineSchemePresieve {X : T.Spaces} (Y : BigFppfSpaceOver T X) : Presieve Y :=
  fun {Z} _ ↦ IsAffineSchemeOver T X Z

/-- **Every object of the big fppf site of an algebraic space `X` is covered by its objects
representable by an affine scheme.**  The affine étale charts through the points of the source
of the object form an étale, hence fppf, covering family of that source (Stacks 0DFC); a chosen
covering family of the site combinatorially equivalent to it generates the same presieve, and
the lift of that presieve to the slice at `X` is refined by the arrows out of the representable
affine objects. -/
theorem generate_affineSchemePresieve_mem {X : T.Spaces} (Y : BigFppfSpaceOver T X) :
    Sieve.generate (affineSchemePresieve T Y) ∈ BigFppfSpaceOver.topology T X Y := by
  obtain ⟨W, b, hWaff, -, -, hcov⟩ := Space.exists_isEtaleCovering_affine
    T.schemeSite S T.scheme_mem Y.left.1 Y.left.2
  let E : PreZeroHypercover.{u + 2} Y.left :=
    { I₀ := ULift.{u + 2} (Space.points T.schemeSite S T.scheme_mem Y.left.1)
      X := fun x ↦ (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj (W x.down)
      f := fun x ↦ ObjectProperty.homMk (b x.down) }
  have hE : Space.IsFppfCoveringFamily T.schemeSite S T.scheme_mem ⟨Y.left, E⟩ :=
    Space.isFppfCovering_of_isEtaleCovering T.schemeSite S T.scheme_mem
      (Space.IsEtaleCovering.reindex T.schemeSite S T.scheme_mem hcov
        (σ := ULift.down) fun x ↦ ⟨ULift.up x, rfl⟩)
  exact generate_mem_over_of_covering_representative (Y := Y)
    (Q := Space.IsFppfCoveringFamily T.schemeSite S T.scheme_mem) T.mem_precoverage_iff
    T.covering_representative _ E hE fun x ↦
      Sieve.le_generate _ _ _ ⟨W x.down, hWaff x.down, ⟨Iso.refl _⟩⟩

end BigFppfSpaceOver

namespace BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- The property of an object of the big étale site of an algebraic space `X` of `T` that its
source is isomorphic to the algebraic space represented by a scheme of the auxiliary big fppf
site of schemes with affine total space. -/
def IsAffineSchemeOver (X : T.Spaces) : ObjectProperty (Over X) :=
  fun Y ↦ ∃ W : BigFppfOver T.fppfSite S T.fppf_mem,
    IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj W) ∧
      Nonempty ((schemeSpaceFunctor T.fppfSite S T.fppf_mem).obj W ≅ Y.left)

/-- The presieve of all arrows into an object of the big étale site of `X` whose source is
representable by a scheme with affine total space. -/
def affineSchemePresieve {X : T.Spaces} (Y : Over X) : Presieve Y :=
  fun {Z} _ ↦ IsAffineSchemeOver T X Z

/-- **Every object of the big étale site of an algebraic space `X` is covered by its objects
representable by an affine scheme.**  The affine étale charts through the points of the source
of the object form an étale covering family of that source; a chosen covering family of the site
combinatorially equivalent to it generates the same presieve, and the lift of that presieve to
the slice at `X` is refined by the arrows out of the representable affine objects. -/
theorem generate_affineSchemePresieve_mem {X : T.Spaces} (Y : Over X) :
    Sieve.generate (affineSchemePresieve T Y) ∈ T.bigEtaleTopology X Y := by
  obtain ⟨W, b, hWaff, -, -, hcov⟩ := Space.exists_isEtaleCovering_affine
    T.fppfSite S T.fppf_mem Y.left.1 Y.left.2
  let E : PreZeroHypercover.{u + 2} Y.left :=
    { I₀ := ULift.{u + 2} (Space.points T.fppfSite S T.fppf_mem Y.left.1)
      X := fun x ↦ (schemeSpaceFunctor T.fppfSite S T.fppf_mem).obj (W x.down)
      f := fun x ↦ ObjectProperty.homMk (b x.down) }
  have hE : Space.IsEtaleCoveringFamily T.fppfSite S T.fppf_mem ⟨Y.left, E⟩ :=
    Space.IsEtaleCovering.reindex T.fppfSite S T.fppf_mem hcov
      (σ := ULift.down) fun x ↦ ⟨ULift.up x, rfl⟩
  exact generate_mem_over_of_covering_representative (Y := Y)
    (Q := Space.IsEtaleCoveringFamily T.fppfSite S T.fppf_mem) T.mem_precoverage_iff
    T.covering_representative _ E hE fun x ↦
      Sieve.le_generate _ _ _ ⟨W x.down, hWaff x.down, ⟨Iso.refl _⟩⟩

end BigEtaleSpaceSite

end AlgebraicGeometry

end
