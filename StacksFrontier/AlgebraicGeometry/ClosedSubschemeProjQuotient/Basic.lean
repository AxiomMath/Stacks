module

public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.ProjImmersion
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0801 over an absolute `Proj`: all but the isomorphism, which is the tag

Stacks Tag 0801 says that a closed subscheme `Z` of a quasi-compact relative `Proj_S(A)` is the
relative `Proj` of the quotient of `A` by the graded ideal of homogeneous sections vanishing on
`Z`. Its formal statement bundles that into Tag 0801's `ClosedSubschemeProjPresentation`, a structure with
seven fields: the graded quotient, a projection-formula twist comparison, degreewise
surjectivity of the quotient maps, the identification of their kernel with the vanishing
sections, everywhere-definedness of the induced map on `Proj`, the isomorphism `Z ≅ Proj` of the
quotient, and the compatibility of that isomorphism with the ambient `Proj`.

**The statement of Tag 0801 cannot be axiom-clean in the current library, for a reason outside
Tag 0801.** Every object in it is built from Tag 01NQ's `relativeProj`, which is unproved, as are
Tag 01NR's `relativeProjTwists` and Tag 07ZG's `relativeProjMap`. An open goal reached through
the vocabulary of a statement is reported by `#print axioms` exactly as one in a proof is, so no
declaration whose type mentions those can be clean, however it is proved. What is *not* an
obstruction is Tag 01NN's `sectionRingStructure_exists`: it is proved in full, with no open goal
anywhere in its proof. (Its form here is
`Stacks.RelativeProj.Situation.sectionRingStructure_exists`.)

This file therefore states Tag 0801's content over the **absolute** `Proj` of a graded ring,
where every object does exist, and records how much of it the library proves.

## What is proved here, and what each clause costs

Over `AlgebraicGeometry.Proj 𝒮` for a nonnegatively graded `R`-algebra `S`, and a closed
immersion `i : Z ⟶ Proj 𝒮`:

* the graded ideal is `Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme`
  (Stacks Tag 0BXK), homogeneous by `idealOfClosedSubscheme_isHomogeneous`, so it is a
  `HomogeneousIdeal 𝒮` — that packaging is
  `Stacks.ClosedSubschemeProjQuotient.homogeneousIdealOfClosedSubscheme`;
* the graded quotient is `Stacks.RingTheory.HomogeneousQuotient.quotientGrading`, and
  the quotient map `Stacks.RingTheory.HomogeneousQuotient.quotientMk`;
* **degreewise surjectivity** is `surjective_gradedAddHom_quotientMk`, in every degree,
  which is the presentation's `quotient_epi`;
* **everywhere-definedness**, the presentation's `domain_eq_top`, follows from that surjectivity by
  `Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective`
  so the induced morphism can be taken on the whole of `Proj` of the quotient. It is
  baked into `Stacks.ClosedSubschemeProjQuotient.ambientHom` rather than carried as a field;
* **the kernel clause** is proved here. It is the composite of
  `Stacks.RingTheory.HomogeneousQuotient.quotientMk_apply` and
  `Ideal.Quotient.eq_zero_iff_mem` with
  `Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.mem_idealOfClosedSubscheme_iff`, and it comes
  out in exactly the shape Tag 0801's `quotient_kernel` has: a homogeneous element of degree `n`
  dies in the quotient precisely when the global section of `𝒪(n)` it determines pulls back to
  zero on `Z`;
* **the closed immersion into the ambient `Proj`** is
  `Stacks.AlgebraicGeometry.SegreClosedImmersion.isClosedImmersion_mapHomOfTop` — Stacks
  Tag 01N1 part (2) on the whole of `Proj` rather than on the domain of definition.

The presentation's `twist_comparison` has **no absolute analogue**: it compares the twist of `i_* 𝒪_Z`
with the pushforward of the restricted twist, and over an absolute `Proj` the kernel clause is
stated directly against the pullback of global sections, with no projection formula in the way.

**What is left is exactly the isomorphism, and it is the whole mathematical content of the tag.**
`Stacks.ClosedSubschemeProjQuotient.SaturationIdentification` names it. It is the half of Stacks
Tag 0BXK — the correspondence between closed subschemes of `Proj 𝒮` and *saturated* homogeneous
ideals — that Mathlib does not have (see
`StacksFrontier/AlgebraicGeometry/CodimensionOneEquation/Basic.lean`): Mathlib has only the
topological Galois connection `ProjectiveSpectrum.gc_homogeneousIdeal` between homogeneous ideals
and closed *subsets*, which says nothing about closed subschemes. The two facts proved here —
that `Proj` of the quotient is a closed subscheme of `Proj 𝒮`, and that the ideal of `Z` is
homogeneous — are the two halves of that correspondence that do *not* need it.

It is not proved in **this** file, but it is proved in this repository, twice:
`Stacks.ClosedSubschemeProjQuotient.saturationIdentification` (`./Saturation.lean`) for a
Noetherian graded ring generated in degree one, and
`Stacks.ProjQuotientFiniteCover.saturationIdentification_of_cover`
(`../ProjQuotientFiniteCover/Basic.lean`) with the Noetherian hypothesis traded for a finite
family of degree-one elements whose standard opens cover `Proj 𝒮` — which, instantiated at the
variables of a polynomial ring, gives Stacks Tag 03GL over an arbitrary coefficient ring.

So, of the presentation's seven fields at the absolute `Proj`, four are discharged here
(three directly from existing results, the kernel clause assembled here), one has no absolute
analogue, and **two — the isomorphism and its compatibility, which are the tag — are discharged
downstream, in the two files just named.**

## Main definitions

* `Stacks.ClosedSubschemeProjQuotient.homogeneousIdealOfClosedSubscheme`: the ideal of a closed
  subscheme of `Proj 𝒮` as a `HomogeneousIdeal 𝒮`.
* `Stacks.ClosedSubschemeProjQuotient.projQuotient`: `Proj` of the quotient by that ideal — the
  absolute analogue of `relativeProj quotient.targetSituation` as Tag 0801 writes it.
* `Stacks.ClosedSubschemeProjQuotient.ambientHom`: the canonical morphism from it to `Proj 𝒮`,
  defined on all of `Proj` of the quotient.
* `Stacks.ClosedSubschemeProjQuotient.ProjQuotientPresentation`: the absolute analogue of
  Tag 0801's `ClosedSubschemeProjPresentation`.
* `Stacks.ClosedSubschemeProjQuotient.SaturationIdentification`: the one clause this file does
  not prove, named as a condition so that consumers can state it; its witnesses are built in
  `./Saturation.lean` and `../ProjQuotientFiniteCover/Basic.lean`.

## Main results

* `Stacks.ClosedSubschemeProjQuotient.quotientMk_eq_zero_iff`: an arbitrary element of `S` dies in
  the quotient exactly when every one of its homogeneous components vanishes on `Z`.
* `Stacks.ClosedSubschemeProjQuotient.quotientMk_coe_eq_zero_iff`: **Tag 0801's kernel clause**,
  for a homogeneous element of degree `n`.
* `Stacks.ClosedSubschemeProjQuotient.surjective_quotientMk`: Tag 0801's `quotient_epi` clause, in
  every degree.
* `Stacks.ClosedSubschemeProjQuotient.mapDomain_eq_top`: Tag 0801's `domain_eq_top` clause.
* `Stacks.ClosedSubschemeProjQuotient.isClosedImmersion_ambientHom`: `Proj` of the quotient is a
  closed subscheme of `Proj 𝒮`.
* `Stacks.ClosedSubschemeProjQuotient.projQuotientPresentation_of_saturationIdentification`: the
  whole presentation, from the one open clause.

## What is not done, and no tag is attached

**No Stacks tag attribute is attached anywhere in this file.** Nothing here is Tag 0801: the tag
is about a *relative* `Proj` over an arbitrary base with a quasi-compactness hypothesis, and
everything below is about the absolute `Proj` of a graded ring — the case `S = Spec R` of the
tag, and then only after the relative-`Proj` vocabulary of Tags 01NQ, 01NR and 07ZG exists.
`Stacks.ClosedSubschemeProjQuotient.ProjQuotientPresentation` is an analogue, not a restriction,
and the clause that is open here is open in the relative case too.

No Tag 0BXK attribute is attached either: the clause of that tag this file would support is its
first assertion, that a closed subscheme of a quasi-compact `Proj 𝒮` is `V₊` of its ideal of
equations, and that assertion is completed — and registered — in `./Saturation.lean`, which this
file only prepares.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealOfClosedSubscheme
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.RingTheory.HomogeneousQuotient

universe u

namespace Stacks.ClosedSubschemeProjQuotient

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝒮 : ℕ → Submodule R S)
  [GradedAlgebra 𝒮]

/-! ### The graded ideal, the quotient, and the morphism to the ambient `Proj` -/

/-- **The homogeneous ideal of a closed subscheme of `Proj 𝒮`.** This is
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme` packaged with its own
homogeneity proof, which is the form `Stacks.RingTheory.HomogeneousQuotient.quotientGrading`
consumes. It is the absolute analogue of the graded ideal of Stacks Tag 0801. -/
@[ega "II 2.9.2", ega "II 3.6.2" "(ii), special case"]
def homogeneousIdealOfClosedSubscheme {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    HomogeneousIdeal 𝒮 :=
  ⟨idealOfClosedSubscheme 𝒮 i, idealOfClosedSubscheme_isHomogeneous 𝒮 i⟩

/-- **`Proj` of the quotient by the ideal of `Z`.** The absolute analogue of the target of Tag
0801's isomorphism. -/
abbrev projQuotient {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] : Scheme.{u} :=
  Proj (quotientGrading 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i))

/-! ### The clauses that come from existing results -/

/-- **Tag 0801's `quotient_epi` clause, in every degree.** The degree-`n` piece of the quotient is
by construction the image of `𝒮 n`. -/
theorem surjective_quotientMk {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] (n : ℕ) :
    Function.Surjective
      (GradedRingHom.gradedAddHom (quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i)) n) :=
  surjective_gradedAddHom_quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i) n

/-- Degreewise surjectivity in the eventual form the `Proj` machinery consumes. -/
theorem eventually_surjective_quotientMk {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] :
    ∀ᶠ d : ℕ in Filter.atTop,
      Function.Surjective
        (GradedRingHom.gradedAddHom (quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i)) d) :=
  Filter.Eventually.of_forall (surjective_quotientMk 𝒮 i)

/-- **Tag 0801's `domain_eq_top` clause.** The induced morphism on `Proj` is everywhere defined,
because the quotient map is surjective in every degree. This is
`Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective`. -/
theorem mapDomain_eq_top {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    Stacks.AlgebraicGeometry.ProjShared.mapDomain 𝒮
      (quotientGrading 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i))
      (quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i)) = ⊤ :=
  Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective _ _ _
    (eventually_surjective_quotientMk 𝒮 i)

/-- **The canonical morphism `Proj (𝒮 / I) ⟶ Proj 𝒮`**, for `I` the ideal of `Z`, defined on the
whole of `Proj (𝒮 / I)` by `Stacks.ClosedSubschemeProjQuotient.mapDomain_eq_top`. The absolute
analogue of Tag 07ZG's `relativeProjMap`, as Tag 0801 reads it through its `domain_eq_top`
clause. -/
abbrev ambientHom {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    projQuotient 𝒮 i ⟶ Proj 𝒮 :=
  Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop 𝒮
    (quotientGrading 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i))
    (quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i)) (mapDomain_eq_top 𝒮 i)

/-- **`Proj` of the quotient is a closed subscheme of `Proj 𝒮`.** This is
`Stacks.AlgebraicGeometry.SegreClosedImmersion.isClosedImmersion_mapHomOfTop` — Stacks Tag 01N1
part (2) on the whole of `Proj` — at the graded quotient map, whose degreewise
surjectivity is `Stacks.ClosedSubschemeProjQuotient.surjective_quotientMk`. -/
@[ega "II 2.9.2" "(i), special case"]
theorem isClosedImmersion_ambientHom {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    IsClosedImmersion (ambientHom 𝒮 i) :=
  Stacks.AlgebraicGeometry.SegreClosedImmersion.isClosedImmersion_mapHomOfTop _ _ _ _
    (eventually_surjective_quotientMk 𝒮 i)

/-! ### The kernel clause -/

/-- The equation map in degree `n`, as an additive homomorphism: a homogeneous element of degree
`n` goes to the pullback to `Z` of the global section of `𝒪(n)` it determines.

`StacksFrontier/AlgebraicGeometry/IdealOfClosedSubscheme/Basic.lean` has this map, and records at
its lines 136-144 why it has to be bundled — the target is reached through a semireducible
`Scheme.Modules.presheaf`, so `map_zero` cannot be instantiated against the unbundled
application. It is `private` there, so it is rebuilt here rather than reused. -/
private def equationHom {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) (n : ℕ) :
    𝒮 n →+ Γ((Scheme.Modules.pullback i).obj
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n : ℤ)), ⊤) :=
  AddMonoidHom.comp
    (AddMonoidHom.mk'
      (fun s => pullbackGlobalSections i
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n : ℤ)) s)
      (fun s t => map_add (ConcreteCategory.hom (pullbackGlobalSections i
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n : ℤ)))) s t))
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSectionHom 𝒮 n)

/-- **The kernel of the quotient map, on an arbitrary element.** An element of `S` dies in the
quotient by the ideal of `Z` exactly when the section attached to each of its homogeneous
components pulls back to zero on `Z`.

This is `Stacks.RingTheory.HomogeneousQuotient.ker_quotientMk` followed by
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.mem_idealOfClosedSubscheme_iff`. -/
theorem quotientMk_eq_zero_iff {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] (a : S) :
    quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i) a = 0 ↔
      ∀ n : ℕ, pullbackGlobalSections i
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 n
          ((DirectSum.decompose 𝒮 a) n)) = 0 := by
  rw [quotientMk_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact mem_idealOfClosedSubscheme_iff 𝒮 i a

/-- **Stacks Tag 0801's kernel clause, at the absolute `Proj`.** A homogeneous element of degree
`n` dies in the quotient by the ideal of `Z` exactly when the global section of `𝒪(n)` it
determines pulls back to zero on `Z`.

This is the shape Tag 0801's `ClosedSubschemeProjPresentation.quotient_kernel` has: the quotient
is specified by its kernel against the restriction of the canonical homogeneous section to the
closed subscheme, degree by degree. The reduction from
`Stacks.ClosedSubschemeProjQuotient.quotientMk_eq_zero_iff` is that a homogeneous element has one
nonzero component. -/
theorem quotientMk_coe_eq_zero_iff {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i]
    (n : ℕ) (a : 𝒮 n) :
    quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i) (a : S) = 0 ↔
      pullbackGlobalSections i
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 n a) = 0 := by
  classical
  have hsame : (DirectSum.decompose 𝒮 (a : S)) n = a :=
    Subtype.ext (DirectSum.decompose_of_mem_same 𝒮 a.2)
  rw [quotientMk_eq_zero_iff]
  refine ⟨fun h => ?_, fun h k => ?_⟩
  · have := h n
    rwa [hsame] at this
  · by_cases hk : k = n
    · subst k
      rwa [hsame]
    · have hzero : (DirectSum.decompose 𝒮 (a : S)) k = 0 :=
        Subtype.ext (DirectSum.decompose_of_mem_ne 𝒮 a.2 (Ne.symm hk))
      show equationHom 𝒮 i k ((DirectSum.decompose 𝒮 (a : S)) k) = 0
      rw [hzero]
      exact map_zero _

/-! ### The presentation, and the one clause that is open -/

/-- **The absolute analogue of Tag 0801's `ClosedSubschemeProjPresentation`**: the graded quotient
by the ideal of `Z`, its degreewise surjectivity and kernel, the closed immersion into the
ambient `Proj`, and the identification of `Z` with `Proj` of the quotient over that ambient
`Proj`.

Tag 0801's `domain_eq_top` is not a field here: it is proved outright by
`Stacks.ClosedSubschemeProjQuotient.mapDomain_eq_top` and is already inside `ambientHom`. Tag
0801's `twist_comparison` has no absolute analogue; see the module documentation. -/
structure ProjQuotientPresentation {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮)
    [IsClosedImmersion i] where
  /-- The quotient maps are surjective in every degree. -/
  quotient_epi (n : ℕ) :
    Function.Surjective
      (GradedRingHom.gradedAddHom (quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i)) n)
  /-- The quotient ideal is exactly the degreewise set of equations for `Z`. -/
  quotient_kernel (n : ℕ) (a : 𝒮 n) :
    quotientMk 𝒮 (homogeneousIdealOfClosedSubscheme 𝒮 i) (a : S) = 0 ↔
      pullbackGlobalSections i
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮 (n : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒮 n a) = 0
  /-- `Proj` of the quotient is a closed subscheme of the ambient `Proj`. -/
  isClosedImmersion_ambient : IsClosedImmersion (ambientHom 𝒮 i)
  /-- The closed subscheme is isomorphic to `Proj` of the quotient. -/
  iso : Z ≅ projQuotient 𝒮 i
  /-- The identification is canonical over the ambient `Proj`. -/
  iso_over_ambient : iso.hom ≫ ambientHom 𝒮 i = i

/-- **The one clause of Stacks Tag 0801 this file does not prove, named as a condition.** Every
closed subscheme of an absolute `Proj` is isomorphic, over that `Proj`, to `Proj` of the quotient
by its own graded ideal of equations.

This is the half of Stacks Tag 0BXK that Mathlib does not have: the correspondence between closed
subschemes of `Proj 𝒮` and saturated homogeneous ideals of `𝒮`. Its absence from Mathlib is
recorded at
`StacksFrontier/AlgebraicGeometry/CodimensionOneEquation/Basic.lean`; Mathlib's
`ProjectiveSpectrum.gc_homogeneousIdeal` is the topological statement about closed *subsets* and
does not give this.

The two directions that are *not* missing are both proved above:
`Stacks.ClosedSubschemeProjQuotient.isClosedImmersion_ambientHom` gives the closed subscheme
attached to a homogeneous ideal, and
`Stacks.ClosedSubschemeProjQuotient.quotientMk_coe_eq_zero_iff` identifies the ideal attached to a
closed subscheme degreewise. What neither gives is that the two assignments are mutually inverse,
which is this condition.

**It is stated at a single situation, deliberately, and no witness is constructed here.** A
universally quantified form over every nonnegatively graded algebra would be an over-claim:
Stacks Tag 0801 carries a quasi-compactness hypothesis on the structure morphism of the relative
`Proj`, and nothing establishes that the correspondence survives its removal. So this is a
condition a consumer supplies where it holds, in the shape
`Stacks.AmpleImmersionReduction.ChartImmersion` is stated, and not an assertion about all graded
rings.

Witnesses are constructed downstream, where the hypotheses that buy them are available:
`Stacks.ClosedSubschemeProjQuotient.saturationIdentification` (`./Saturation.lean`) for a
Noetherian graded ring generated in degree one, and
`Stacks.ProjQuotientFiniteCover.saturationIdentification_of_cover`
(`../ProjQuotientFiniteCover/Basic.lean`) for a graded ring generated in degree one carrying a
finite family of degree-one elements whose standard opens cover `Proj 𝒮`. -/
def SaturationIdentification {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] : Prop :=
  ∃ e : Z ≅ projQuotient 𝒮 i, e.hom ≫ ambientHom 𝒮 i = i

/-- **Stacks Tag 0801's presentation at the absolute `Proj`, from the one clause named above.**
Four of
the seven fields of Tag 0801's presentation are discharged from existing results, one has no absolute analogue, and
`SaturationIdentification` supplies only the isomorphism and its compatibility. -/
theorem projQuotientPresentation_of_saturationIdentification
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] (h : SaturationIdentification 𝒮 i) :
    Nonempty (ProjQuotientPresentation 𝒮 i) := by
  obtain ⟨e, he⟩ := h
  exact ⟨{ quotient_epi := surjective_quotientMk 𝒮 i
           quotient_kernel := quotientMk_coe_eq_zero_iff 𝒮 i
           isClosedImmersion_ambient := isClosedImmersion_ambientHom 𝒮 i
           iso := e
           iso_over_ambient := he }⟩

end Stacks.ClosedSubschemeProjQuotient

end
