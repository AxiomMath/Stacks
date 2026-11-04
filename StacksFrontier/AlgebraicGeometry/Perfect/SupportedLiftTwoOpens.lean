module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules
public import StacksFrontier.AlgebraicGeometry.RestrictionAlongNestedOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.TwoOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessOnACover

/-!
# Glueing a supported perfect object with a map, over a scheme covered by two opens

Let `X` be a scheme covered by two opens `U` and `V`, let `T ⊆ X` be a subset and let `E` be an
object of `D(𝒪_X)`. Given a perfect object over `U` and one over `V`, each with cohomology
supported on the part of `T` it sees and each with a map to the restriction of `E`, and given an
isomorphism of the two over the intersection through which the two maps agree, there is a perfect
object of `D(𝒪_X)` supported on `T` with a map to `E` restricting to the given data.

This is the glueing half of the two-open step of [Stacks, Tag 09IM], with no affine hypothesis
and no lifting data: the two objects over `U` and over `V` are given. Both halves of
[Stacks, Tag 08DG] are used — the existence of the glued object, which needs no cover, and the
production of the map out of it, which does — and the two clauses of the conclusion are the
locality of perfectness and of cohomological support on a cover by two opens.

The *compatibility* clause is stated as the two equalities
`ρ|_U = f.hom ≫ a` and `ρ|_V = g.hom ≫ b`, with `f` and `g` the two identifications; that is
what [Stacks, Tag 08DG] produces, and it is the form the strengthened compatibility of
[Stacks, Tag 09IM]'s step is read off from. Over `U` the given map `a` will be
`biprod.fst ≫ ρ₁`, so that the glued map is, in the coordinates of the splitting, the projection
followed by the map of the previous stage — which is exactly the hypothesis `oracle` of
`DerivedCategory.exists_approximatesFrom_of_splitLiftOracle` wants.

## Main results

* `Stacks.Perfect.SupportedLiftTwoOpens.exists_isPerfect_supported_hom_of_overlap_iso`: the
  statement above.

## Implementation notes

Everything is in the one restriction model [Stacks, Tag 08DG] is stated in,
`Stacks.Cohomology.GlueingComplexes.derivedRestrict`, which is an abbreviation for the derived
pullback along a morphism of ringed spaces. The covering hypothesis of that lemma at two opens of
a scheme is `Stacks.RestrictionSpellings.range_union_ofRestrict_eq_univ`, and the two locality
statements — `Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_derivedPullback_sup_eq_top`
and `Stacks.DerivedQCoh.cohomologySupportedOn_of_derivedPullback_sup_eq_top` — are stated for that
same functor, so no comparison of restriction spellings appears in the proof.

**The overlap is left abstract, and why it has to be.** The intersection of the two opens enters
only as the apex of a Cartesian square, exactly as in [Stacks, Tag 08DG] itself, so `W`, `iU`,
`iV` and the square are hypotheses rather than `U ⊓ V` and the two `X.homOfLE`s. That is not
generality for its own sake. Writing the square out with
`Stacks.RestrictionSpellings.isPullback_ofRestrict_inf` makes the *kernel* time out on the
default heartbeat budget: `exists_hom_of_compatible` applied at
`(X.homOfLE _).toLRSHom.toShHom` costs more than the budget allows, while with `iU` and `iV`
variables — everything else unchanged — the same term checks in a fraction of a second. The
elaborator unfolds the `X.homOfLE` spelling of the overlap inclusion eagerly, and the resulting
definitional unfolding is what the kernel then has to repeat. A consumer that wants `U ⊓ V`
passes `Stacks.RestrictionSpellings.isPullback_ofRestrict_inf X U V` and pays for that
instantiation once, where it can be isolated.

For the same reason the two halves of [Stacks, Tag 08DG] are applied in
`Stacks.Perfect.SupportedLiftTwoOpens.exists_hom_of_overlap_iso_abstract`, which mentions no
scheme at all, and the two locality clauses are proved in two separate private lemmas: a single
declaration carrying all four steps does not pass the kernel either.

**`HasDerivedCategory.standard`** is a local instance at priority `10000`, as in the modules this
one consumes: without the priority a different derived-category model is selected and the
locality statements are then about a different category, with no error naming the cause.

The registration of [Stacks, Tag 09IM] is on another declaration, and that
of [Stacks, Tag 08DG] is on the two halves consumed here, so no tag attribute is placed in this
module.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.GlueingComplexes

universe u

namespace Stacks.Perfect.SupportedLiftTwoOpens

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The two halves of [Stacks, Tag 08DG] in one statement, at abstract open immersions.** For
a cover of a ringed space by two open immersions, an object over each, an isomorphism of the two
over the intersection, and maps to the restrictions of an ambient `E` agreeing over the
intersection, there is an object of `D(𝒪_X)` with a map to `E` restricting to the given data.

Both halves of [Stacks, Tag 08DG] are applied here, with nothing concrete in sight: the whole
statement is about abstract ringed spaces and abstract open immersions. That is deliberate — the
assembled term at the two inclusions of opens of a scheme does not pass the kernel inside the
default heartbeat budget, while this one does and is applied once, in term mode. -/
private theorem exists_hom_of_overlap_iso_abstract {X U V W : RingedSpace.{u, u}}
    (jU : U ⟶ X) (jV : V ⟶ X) (iU : W ⟶ U) (iV : W ⟶ V)
    [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (h : IsPullback iU iV jU jV)
    (hcover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    (A : DerivedModules U) (B : DerivedModules V) (E : DerivedModules X)
    (a : A ⟶ (derivedRestrict jU).obj E) (b : B ⟶ (derivedRestrict jV).obj E)
    (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (hab : (derivedRestrict iU).map a ≫ (overlapIso jU jV iU iV h.w).hom.app E =
      c.hom ≫ (derivedRestrict iV).map b) :
    ∃ (R : DerivedModules X) (ρ : R ⟶ E) (f : (derivedRestrict jU).obj R ≅ A)
      (g : (derivedRestrict jV).obj R ≅ B),
      (derivedRestrict jU).map ρ = f.hom ≫ a ∧ (derivedRestrict jV).map ρ = g.hom ≫ b := by
  obtain ⟨G⟩ := exists_glueing jU jV iU iV h A B c
  obtain ⟨ρ, hρU, hρV⟩ := exists_hom_of_compatible jU jV iU iV h hcover G E a b hab
  exact ⟨G.F, ρ, G.f, G.g, hρU, hρV⟩

variable (X : Scheme.{u}) (U V : X.Opens)

/-- The inclusion of the open subspace `U` of `X`, as a morphism of ringed spaces: the morphism
[Stacks, Tag 08DG]'s restriction functor is taken along. -/
abbrev openInclusion : (X.toRingedSpace.restrict U.isOpenEmbedding) ⟶ X.toRingedSpace :=
  X.toRingedSpace.ofRestrict U.isOpenEmbedding

/-- The perfectness clause of the glueing, isolated: an object of `D(𝒪_X)` whose restrictions to
two opens covering `X` are isomorphic to perfect objects is perfect.

This is `Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_derivedPullback_sup_eq_top`
after `Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso`, split off so that the kernel
checks it against the small statement rather than as one part of the assembled conclusion below;
the two universe annotations are needed because the restriction functor of [Stacks, Tag 08DG] is
stated at the `Stacks.Cohomology.GlueingComplexes.DerivedModules` spelling of the category and
these two lemmas at the `Stacks.StrictlyPerfect.OXMod` one. -/
private theorem isPerfect_of_restrict_iso (hUV : U ⊔ V = ⊤) (R : DerivedModules X.toRingedSpace)
    {A : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)}
    {B : DerivedModules (X.toRingedSpace.restrict V.isOpenEmbedding)}
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := X.toRingedSpace.restrict U.isOpenEmbedding) A)
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := X.toRingedSpace.restrict V.isOpenEmbedding) B)
    (f : (derivedRestrict (openInclusion X U)).obj R ≅ A)
    (g : (derivedRestrict (openInclusion X V)).obj R ≅ B) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) R :=
  Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_derivedPullback_sup_eq_top.{u}
    R U V hUV
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} f.symm hA)
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} g.symm hB)

/-- The support clause of the glueing, isolated: an object of `D(𝒪_X)` whose restrictions to two
opens covering `X` are isomorphic to objects supported on the preimages of `T` is supported on
`T`.

This is `Stacks.DerivedQCoh.cohomologySupportedOn_of_derivedPullback_sup_eq_top` after
`Stacks.DerivedQCoh.cohomologySupportedOn_of_iso`, split off for the same reason as
`Stacks.Perfect.SupportedLiftTwoOpens.isPerfect_of_restrict_iso`. -/
private theorem cohomologySupportedOn_of_restrict_iso (hUV : U ⊔ V = ⊤) (T : Set X)
    (R : DerivedModules X.toRingedSpace)
    {A : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding)}
    {B : DerivedModules (X.toRingedSpace.restrict V.isOpenEmbedding)}
    (hAT : AlgebraicGeometry.CohomologySupportedOn (U : X.Opens).toScheme.ringCatSheaf
      (Subtype.val ⁻¹' T) A)
    (hBT : AlgebraicGeometry.CohomologySupportedOn (V : X.Opens).toScheme.ringCatSheaf
      (Subtype.val ⁻¹' T) B)
    (f : (derivedRestrict (openInclusion X U)).obj R ≅ A)
    (g : (derivedRestrict (openInclusion X V)).obj R ≅ B) :
    AlgebraicGeometry.CohomologySupportedOn X.ringCatSheaf T R :=
  Stacks.DerivedQCoh.cohomologySupportedOn_of_derivedPullback_sup_eq_top U V hUV T R
    (Stacks.DerivedQCoh.cohomologySupportedOn_of_iso _ f.symm hAT)
    (Stacks.DerivedQCoh.cohomologySupportedOn_of_iso _ g.symm hBT)

/-- **Glueing a supported perfect object with a map, over a scheme covered by two opens.** Let
`U ⊔ V = ⊤` in a scheme `X`, let `T ⊆ X`, and let `E` be an object of `D(𝒪_X)`. Let `W` be the
intersection of `U` and `V`, presented as the apex of a Cartesian square of the four inclusions.
Let `A` over `U` and `B` over `V` be perfect with cohomology supported on the preimages of `T`,
let `a : A ⟶ E|_U` and `b : B ⟶ E|_V`, and let `c : A|_W ≅ B|_W` carry `a|_W` to `b|_W`. Then
there is a perfect object `R` of `D(𝒪_X)` with cohomology supported on `T`, a map `ρ : R ⟶ E`,
and identifications `R|_U ≅ A` and `R|_V ≅ B` through which `ρ` restricts to `a` and to `b`.

This is the glueing half of the two-open step of [Stacks, Tag 09IM]. The object and the
identifications are `Stacks.Cohomology.GlueingComplexes.exists_glueing`, the map is
`Stacks.Cohomology.GlueingComplexes.exists_hom_of_compatible` — the half that needs the cover —
and the two remaining clauses are the locality of perfectness and of cohomological support.

`Stacks.RestrictionSpellings.isPullback_ofRestrict_inf X U V` is the square at `W = U ⊓ V`; see
the implementation notes for why it is not written out here.

The registration of [Stacks, Tag 09IM] is on another declaration, so no
tag attribute is placed here. -/
theorem exists_isPerfect_supported_hom_of_overlap_iso (hUV : U ⊔ V = ⊤) (T : Set X)
    {W : RingedSpace.{u, u}} (iU : W ⟶ X.toRingedSpace.restrict U.isOpenEmbedding)
    (iV : W ⟶ X.toRingedSpace.restrict V.isOpenEmbedding)
    (hpb : IsPullback iU iV (openInclusion X U) (openInclusion X V))
    (E : DerivedModules X.toRingedSpace)
    (A : DerivedModules (X.toRingedSpace.restrict U.isOpenEmbedding))
    (B : DerivedModules (X.toRingedSpace.restrict V.isOpenEmbedding))
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := X.toRingedSpace.restrict U.isOpenEmbedding) A)
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1}
      (X := X.toRingedSpace.restrict V.isOpenEmbedding) B)
    (hAT : AlgebraicGeometry.CohomologySupportedOn (U : X.Opens).toScheme.ringCatSheaf
      (Subtype.val ⁻¹' T) A)
    (hBT : AlgebraicGeometry.CohomologySupportedOn (V : X.Opens).toScheme.ringCatSheaf
      (Subtype.val ⁻¹' T) B)
    (a : A ⟶ (derivedRestrict (openInclusion X U)).obj E)
    (b : B ⟶ (derivedRestrict (openInclusion X V)).obj E)
    (c : (derivedRestrict iU).obj A ≅ (derivedRestrict iV).obj B)
    (hab : (derivedRestrict iU).map a ≫
        (overlapIso (openInclusion X U) (openInclusion X V) iU iV hpb.w).hom.app E =
      c.hom ≫ (derivedRestrict iV).map b) :
    ∃ (R : DerivedModules X.toRingedSpace) (ρ : R ⟶ E),
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn X.ringCatSheaf T R ∧
          ∃ (f : (derivedRestrict (openInclusion X U)).obj R ≅ A)
            (g : (derivedRestrict (openInclusion X V)).obj R ≅ B),
            (derivedRestrict (openInclusion X U)).map ρ = f.hom ≫ a ∧
              (derivedRestrict (openInclusion X V)).map ρ = g.hom ≫ b := by
  obtain ⟨R, ρ, f, g, hρU, hρV⟩ := exists_hom_of_overlap_iso_abstract (openInclusion X U)
    (openInclusion X V) iU iV hpb
    (Stacks.RestrictionSpellings.range_union_ofRestrict_eq_univ X U V hUV) A B E a b c hab
  exact ⟨R, ρ, isPerfect_of_restrict_iso X U V hUV R hA hB f g,
    cohomologySupportedOn_of_restrict_iso X U V hUV T R hAT hBT f g, f, g, hρU, hρV⟩

end Stacks.Perfect.SupportedLiftTwoOpens

end
