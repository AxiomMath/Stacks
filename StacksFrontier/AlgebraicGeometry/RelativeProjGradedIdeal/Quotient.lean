module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.GeneratedInDegreeOne
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient of a sheaf-level graded algebra by a graded ideal

Work in Situation 01NN: a scheme `S` and a quasi-coherent graded `𝒪_S`-algebra `𝒜` in the
sheaf-level form `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`. Let `ℐ ⊆ 𝒜`
be a graded ideal with quasi-coherent homogeneous pieces. This file constructs the quotient
`𝒜/ℐ`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.QcohGradedIdeal`: a graded ideal whose
  homogeneous pieces are quasi-coherent, which is the shape Tag 0801 produces.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotPiece`: the degree-`n` piece of the
  quotient, the cokernel of `ℐ_n ⟶ 𝒜_n`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mulQuot`: the multiplication of the quotient.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotAlgebra`: **the quotient `𝒜/ℐ`**, as a
  `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotHom`: the quotient homomorphism
  `𝒜 ⟶ 𝒜/ℐ`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.projQuotientHom`: the induced morphism
  `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.gradedQuotientPresentationOfIso`: Tag 0801's
  conclusion-as-data, from a graded ideal together with the identification of the closed
  subscheme with `Proj_S(𝒜/ℐ)`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotProj_app_eq_zero_iff`: **the kernel of
  `𝒜_n ⟶ (𝒜/ℐ)_n` on the sections over an arbitrary open is exactly `ℐ_n`** — no sheafification
  intervenes, because the ideal is a subsheaf and evaluation at an open is left exact.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.mulQuot_app_quotProj`: the multiplication of
  the quotient is the multiplication of `𝒜`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.surjectiveOnAffineSections_quotHom`: the
  quotient homomorphism is surjective on homogeneous sections over the affine opens of the base,
  in every degree. This is the hypothesis of
  `Stacks.AlgebraicGeometry.ProjBundleSurjection.map`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.sectionHom_quotHom_eq_zero_iff`: **the kernel
  of `Γ(U, 𝒜) ⟶ Γ(U, 𝒜/ℐ)` on the graded rings of sections over an arbitrary open of the base is
  exactly the graded ideal of local sections of `ℐ`**, degree by degree.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isClosedImmersion_projQuotientHom`:
  `Proj_S(𝒜/ℐ)` is a closed subscheme of `Proj_S(𝒜)`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_iff_ker_eq`: **for a
  graded ideal already in hand, the identification `Z ≅ Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)` is exactly
  the equality of the two ideal sheaves on `Proj_S(𝒜)`** — in particular it is a local statement,
  and `gradedQuotientPresentationOfKerAppEq` reads it off a comparison of kernels on sections over
  the members of any affine open cover.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isFiniteType_quotPiece` and
  `isGeneratedInDegreeOneAt_quotAlgebra`: the two properties clause (8) of Tag 0B45 asks of a
  graded algebra — finiteness of type of the degree-one piece, and generation in degree one —
  are inherited by a graded quotient.

## Implementation notes

**Where the multiplication comes from.** The sections of a cokernel of sheaves of modules are
not the quotient of the sections, so the multiplication cannot be written down degreewise on the
quotient. What makes it exist anyway is that a bilinear map *into a sheaf* does not see a local
bijection in either variable, `Stacks.BilinearMap.extend`. The route is therefore: form the
sectionwise quotient presheaf `prePiece`, where the multiplication *is* sectionwise
(`mulQuotBoth`, two applications of `Stacks.BilinearMap.quotDescBil`, one per variable, the
second of which needs the ideal to absorb multiplication on the right — `mul_mem_right`, the
`mul_mem` field read through the commutativity of `𝒜`); exhibit the comparison map
`theta : prePiece ⟶ (𝒜/ℐ)_n` into the cokernel; and extend along it in each variable.

`theta` is *injective* on the sections over every open, not merely locally injective: a section
of the sectionwise quotient dying in the cokernel comes from a section of `ℐ_n`, by
`AlgebraicGeometry.cokernel_π_val_app_eq_zero_iff` for the monomorphism `ℐ_n ⟶ 𝒜_n`. It is
locally surjective because over an affine open the projection `𝒜_n ⟶ (𝒜/ℐ)_n` is an epimorphism
of quasi-coherent modules, hence surjective on sections
(`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`), and the affine opens form a basis.
That is where quasi-coherence of `ℐ` is used for the construction itself; it is used again for
quasi-coherence of the quotient, which is a field of `SheafGradedAlgebra`.

The construction needs neither a monoidal structure on `SheafOfModules` nor an internal hom of
sheaves of modules, and the pinned Mathlib has neither.

**The laws.** Associativity, commutativity and the two unit laws are proved by lifting the
sections of the quotient locally to sections of `𝒜` and invoking the corresponding law of `𝒜`.
The lifting is `eq_of_forall_lift_three`, the three-section form of
`Stacks.eq_of_forall_lift₂` with the three sources allowed to differ — the three arguments of
associativity live in three different degrees. Degrees are transported with `Stacks.degCast`, as
in `SheafOfModules.PreGradedModule.transfer`, and each step is a term-level `congrArg` or
`Eq.trans` rather than a rewrite: `rw` cannot always build its motive through
`AlgebraicGeometry.Scheme.Modules` and `TopCat.Sheaf`, both of which are plain `def`s whose
projections are not type-correct at the transparency `rw` uses.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)

## Not done here

No Stacks tag is claimed. The Stacks project introduces the quotient `𝒜/ℐ` inline, inside the
statements of Tags 0801 and 0802; it has no tag of its own.

**Tag 0801 is not proved in this file.** It is proved, under the source's own hypotheses and
nothing else, in `StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/Identification.lean`:
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.exists_iso_projQuotient_twistKer` carries the
`@[stacks 0801]` attribute. Everything below is an input to it. The rest of this section is the
record of what was open while it was being assembled.

The graded ideal `ℐ` cut out by a closed subscheme
`i : Z ⟶ Proj_S(𝒜)` is in the tree — `twistKerGradedIdeal` of the sibling file
`TwistRestriction.lean`, see the last paragraph of this section — and everything that is done with
such an ideal once it exists is here; what is missing is the chart comparison that identifies the
ideal of local sections of `ℐ` with the absolute ideal of equations.
`exists_iso_projQuotient_iff_ker_eq` disposes of what used to be described as the missing
isomorphism: for an ideal in hand, `Z ≅ Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)` is **equivalent** to the
equality of the two kernels `i.ker = (projQuotientHom 𝒜 ℐ).ker`, by Mathlib's
`AlgebraicGeometry.IsClosedImmersion.lift` and `isIso_lift` — two closed subschemes with the same
ideal sheaf are isomorphic over the ambient scheme. So no glueing of chart isomorphisms, and no
mapping-in statement for a relative `Proj`, is needed for a closed subscheme: the obstruction
recorded in `Stacks.FiniteMorphismProjective.PushforwardIsRelativeProj` — that a morphism *into*
`Proj_S(ℬ)` cannot be assembled from its charts — does not arise.

Three claims one might expect to hold here are false.

* *That the relative twisted pushforward exists only at the level of algebraic spaces, as*
  `Stacks.AlgebraicGeometry.Spaces.closedSubspaceSectionMap`, *and there conditionally on Tag
  03M9.* The scheme-level homogeneous-section map `𝒜_n ⟶ p_*(𝒪_{Proj_S(𝒜)}(n))` is the `ψ` field
  of `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`
  (`StacksFrontier/AlgebraicGeometry/RelativeProjTwists/Statement.lean:238`), and
  `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`
  (`StacksFrontier/AlgebraicGeometry/GluedTwistAlgebra/Assemble.lean:521`) produces a `TwistData`
  for
  **every** quasi-coherent graded algebra on **every** scheme, with no hypothesis — it is the
  existence assertion of Tag 01NR.
* *That Tag 03M9 is needed for the quasi-coherence of the kernel.* At the level of schemes it is
  not. With `ℐ_d` taken to be the kernel of `𝒜_d ⟶ p_*(i_*(i^*𝒪(d)))`, the unit of
  `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` supplying `𝒪(d) ⟶ i_*i^*𝒪(d)`,
  quasi-coherence is assembled from three results of the library: `isQuasicoherent_pullback`,
  Tag 01BG (`StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean:162`),
  `pushforward_isQuasicoherent`,
  Tag 01LC (`StacksFrontier/AlgebraicGeometry/Scheme/FunctorialityQuasiCoherent/Basic.lean:3274`),
  applied to `i` — affine, hence quasi-compact and quasi-separated — and to `p`, quasi-compact by
  Tag 0801's own hypothesis and separated by
  `Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase`
  (`StacksFrontier/AlgebraicGeometry/RelativeProjSeparated/Basic.lean:117`), and
  `Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`
  (`StacksFrontier/AlgebraicGeometry/QcohLimits/Basic.lean:53`).
* *That the absolute chart comparison is available only for a Noetherian graded ring.*
  `Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover`
  (`StacksFrontier/AlgebraicGeometry/ProjQuotientFiniteCover/Basic.lean:139`) proves it, in both
  directions, for a graded ring generated in degree one with a finite family of degree-one
  elements whose standard opens cover `Proj`, and **no** Noetherian hypothesis. Over an affine open
  `U` of the base the chart of `Proj_S(𝒜)` is `Proj Γ(U, 𝒜)` and quasi-compactness of `p` supplies
  the finite family, `exists_finite_cover_chart` of the sibling file `ClosedSubscheme.lean`.

A fourth such claim is false as well: *that the `mul_mem`
field of `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedIdeal` for that kernel is open,
because the degreewise maps `𝒜_d ⟶ p_*(i_*(i^*𝒪(d)))` can only be shown multiplicative through
multiplication by a local section as a morphism of restricted modules.* The reduction this
describes is right — multiplicativity of the degreewise maps is what is needed, and it asks for a
graded-algebra structure on `i^*` of the twists together with the compatibility of the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` with it — but no restricted-module
multiplication is involved and both inputs are in the tree. The pullback of a sheaf of graded
algebras along a morphism of schemes is `Stacks.Conormal.gradedPullback`
(`StacksFrontier/AlgebraicGeometry/ConormalAlgebra/GradedPullback.lean`), which is
`Stacks.RingedSpace.pullbackGradedAlgebra` read in the vocabulary of schemes, and the
compatibility of the unit with it is that file's `gradedPullback_mul_pullbackSection` together with
`pullbackSection_self`. So **the graded ideal is constructed**, in
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistRestriction.lean`:
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal` is Tag 0801's ideal `ℐ`
with quasi-coherent pieces, over the source's own hypotheses — `i` a closed immersion and `p`
quasi-compact — and nothing else, with
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistRestrictMap_mul` the multiplicativity and
`mem_twistKerGradedIdeal_iff` the membership criterion.

The reduction it is fed through is
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/KernelIdeal.lean`:
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.kerQcohGradedIdeal` turns a degreewise family of
morphisms out of the homogeneous pieces of `𝒜` into quasi-coherent targets carrying a
multiplication the family respects — a `MulCompatibleMaps`, which asks for strictly less than a
`SheafGradedAlgebraHom`, since the target of Tag 0801's map does not vanish in negative degrees —
into a graded ideal with quasi-coherent pieces, `mul_mem` included.

The remaining input of Tag 0801 is the chart comparison, not the ideal — it is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal`
`.sectionIdeal_eq_idealOfClosedSubscheme` of the sibling `ChartComparison.lean`: that
over an affine open `U` of the base the homogeneous ideal
`sectionIdeal 𝒜 (twistKerGradedIdeal 𝒜 D i) U` of the sibling file `ChartQuotient.lean` agrees
with the absolute ideal of equations
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme (𝒜.grading U)` of the
closed subscheme that `i` cuts out of the chart `Proj Γ(U, 𝒜)`. Both sides are described by the
vanishing of a twisted section pulled back along a closed immersion —
`mem_twistKerGradedIdeal_iff` on one side and
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.mem_idealOfClosedSubscheme_iff` on the other — so
what is needed is the identification of the two vanishing conditions: the closed immersion into
the chart obtained from `i` by base change along the chart open immersion, and the fact that the
section of `𝒪(n)` over `p⁻¹(U)` named by `ψ` is carried to the absolute twisted global section
`degreeSection (𝒜.grading U) n` by the chart identification, which is
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.ψ_chart`. With that identification
`Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover` feeds
`ker_eq_ker_projQuotientHom_of_ker_app_eq` below and Tag 0801 follows.

The graded identification, over an
affine open `U` of the base, of `Γ(U, 𝒜/ℐ)` with `Γ(U, 𝒜)/ℐ(U)` is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotGradedHom` and `quotGradedInv` of
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/ChartQuotient.lean`, a pair of mutually
inverse graded ring homomorphisms onto `Stacks.HomogeneousIdeal.quotientGrading` of the
homogeneous ideal `sectionIdeal` of local sections of `ℐ`; and `chartMap_eq_comp_mapHomOfTop_`
`quotientMk` of that file puts the chart map of `projQuotientHom` into the shape
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` of a quotient by a homogeneous ideal, which is
the shape `Stacks.ClosedSubschemeProjQuotient.ambientHom` has. It is assembled
from two halves: `sectionHom_quotHom_eq_zero_iff` for the kernel, over an
arbitrary open, and `Stacks.AlgebraicGeometry.ProjBundleSurjection.surjective_sectionHom` applied
to `surjectiveOnAffineSections_quotHom` for the surjectivity over an affine open. What that does
**not** do is identify `ℐ(U)` with the absolute ideal of equations
`Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.idealOfClosedSubscheme` of the closed subscheme
of the chart; that identification is the chart comparison above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

universe u

variable {S : Scheme.{u}} (𝒜 : SheafGradedAlgebra S)

/-- A graded ideal of a sheaf-level graded algebra whose homogeneous pieces are quasi-coherent.

This is the shape in which Stacks Tag 0801 produces its ideal: the kernel of
`𝒜 ⟶ ⨁_d p_*((i_*𝒪_Z)(d))` is quasi-coherent because the pushforward along a quasi-compact
separated morphism is. Quasi-coherence is what makes the quotient a graded algebra of the same
kind, so it is carried in the datum rather than in every statement. -/
structure QcohGradedIdeal (𝒜 : SheafGradedAlgebra S) extends GradedIdeal 𝒜 where
  /-- Every homogeneous piece of the ideal is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (piece n).toSheafOfModules.IsQuasicoherent

attribute [instance] QcohGradedIdeal.isQuasicoherent

variable (ℐ : QcohGradedIdeal 𝒜)

/-! ### The degreewise quotient sheaf -/

/-- The inclusion of the degree-`n` piece of the graded ideal into the algebra. -/
def pieceι (n : ℤ) : (ℐ.piece n).toSheafOfModules ⟶ 𝒜.piece n := (ℐ.piece n).ι

/-- The inclusion of the degree-`n` piece of the graded ideal is a monomorphism. -/
instance mono_pieceι (n : ℤ) : Mono (pieceι 𝒜 ℐ n) :=
  inferInstanceAs (Mono (ℐ.piece n).ι)

/-- A section of `𝒜_n` is in the image of the sections of `ℐ_n` exactly when it lies in `ℐ_n`. -/
theorem mem_imgSub_pieceι_iff (n : ℤ) (U : S.Opens) (s : Γ(𝒜.piece n, U)) :
    s ∈ Stacks.imgSub (pieceι 𝒜 ℐ n).val (op U) ↔
      s ∈ (ℐ.piece n).toSubmodule.obj (op U) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩

/-- **The degree-`n` piece of the quotient `𝒜/ℐ`**: the cokernel of `ℐ_n ⟶ 𝒜_n`. -/
def quotPiece (n : ℤ) : S.Modules := cokernel (pieceι 𝒜 ℐ n)

/-- The projection of the degree-`n` piece of `𝒜` onto that of the quotient. -/
def quotProj (n : ℤ) : 𝒜.piece n ⟶ quotPiece 𝒜 ℐ n := cokernel.π _

/-- The projection onto the degree-`n` piece of the quotient is an epimorphism. -/
instance epi_quotProj (n : ℤ) : Epi (quotProj 𝒜 ℐ n) :=
  inferInstanceAs (Epi (cokernel.π (pieceι 𝒜 ℐ n)))

/-- **The kernel of the projection, on sections over an arbitrary open.** A homogeneous local
section of `𝒜` dies in the quotient exactly when it is a local section of `ℐ`. -/
theorem quotProj_app_eq_zero_iff (n : ℤ) (U : S.Opens) (s : Γ(𝒜.piece n, U)) :
    (quotProj 𝒜 ℐ n).val.app (op U) s = 0 ↔ s ∈ (ℐ.piece n).toSubmodule.obj (op U) := by
  exact (AlgebraicGeometry.cokernel_π_val_app_eq_zero_iff (pieceι 𝒜 ℐ n)
    (mono_pieceι 𝒜 ℐ n) U s).trans (mem_imgSub_pieceι_iff 𝒜 ℐ n U s)

/-- The quotient of a quasi-coherent module by a quasi-coherent submodule is quasi-coherent. -/
instance isQuasicoherent_quotPiece (n : ℤ) : (quotPiece 𝒜 ℐ n).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel (pieceι 𝒜 ℐ n)

/-! ### The sectionwise quotient presheaf, and its comparison with the quotient sheaf -/

/-- The sectionwise quotient of `𝒜_n` by `ℐ_n`, as a presheaf of modules. -/
def prePiece (n : ℤ) : PresheafOfModules.{u} S.ringCatSheaf.obj :=
  Stacks.quotPresheaf (pieceι 𝒜 ℐ n).val

/-- The inclusion of `ℐ_n` followed by the projection onto `𝒜_n/ℐ_n` is zero, on the underlying
presheaves. -/
theorem pieceι_comp_quotProj_val (n : ℤ) :
    (pieceι 𝒜 ℐ n).val ≫ (quotProj 𝒜 ℐ n).val = 0 :=
  congrArg SheafOfModules.Hom.val (cokernel.condition (pieceι 𝒜 ℐ n))

/-- **The comparison map.** The sectionwise quotient presheaf maps to the quotient sheaf. It is
injective on the sections over every open and locally surjective, which is what lets the
multiplication be transported across it. -/
def theta (n : ℤ) : prePiece 𝒜 ℐ n ⟶ (quotPiece 𝒜 ℐ n).val :=
  Stacks.quotDesc (pieceι 𝒜 ℐ n).val (quotProj 𝒜 ℐ n).val (pieceι_comp_quotProj_val 𝒜 ℐ n)

/-- The comparison map sends the class of a section of `𝒜_n` to its image under the projection. -/
@[simp]
theorem theta_app_quotπ (n : ℤ) (U : (Opens ↥S)ᵒᵖ) (s : (𝒜.piece n).val.obj U) :
    (theta 𝒜 ℐ n).app U ((Stacks.quotπ (pieceι 𝒜 ℐ n).val).app U s) =
      (quotProj 𝒜 ℐ n).val.app U s := rfl

/-- **The comparison map is injective on sections.** A section of the sectionwise quotient dying
in the quotient sheaf comes from a section of `ℐ_n`, hence is already zero: the kernel of
`𝒜_n ⟶ 𝒜_n/ℐ_n` on the sections over an open is exactly `ℐ_n`, with no sheafification. -/
theorem theta_app_injective (n : ℤ) (U : (Opens ↥S)ᵒᵖ) :
    Function.Injective ((theta 𝒜 ℐ n).app U) := by
  intro q q' h
  obtain ⟨s, rfl⟩ := Stacks.quotπ_surjective (pieceι 𝒜 ℐ n).val U q
  obtain ⟨s', rfl⟩ := Stacks.quotπ_surjective (pieceι 𝒜 ℐ n).val U q'
  rw [theta_app_quotπ, theta_app_quotπ, ← sub_eq_zero, ← map_sub] at h
  refine eq_of_sub_eq_zero ((map_sub (ConcreteCategory.hom
    ((Stacks.quotπ (pieceι 𝒜 ℐ n).val).app U)) s s').symm.trans ?_)
  exact (Stacks.quotπ_eq_zero_iff _ _).2
    ((mem_imgSub_pieceι_iff 𝒜 ℐ n U.unop _).2 ((quotProj_app_eq_zero_iff 𝒜 ℐ n U.unop _).1 h))

/-- The comparison map is locally injective, being injective on the sections over every open. -/
instance isLocallyInjective_theta (n : ℤ) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology ↥S) (theta 𝒜 ℐ n) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun U => theta_app_injective 𝒜 ℐ n U

/-- **The comparison map is locally surjective.** Over an affine open of the base the projection
`𝒜_n ⟶ 𝒜_n/ℐ_n` is surjective on sections, because it is an epimorphism of quasi-coherent
modules; and the affine opens form a basis. -/
instance isLocallySurjective_theta (n : ℤ) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥S) (theta 𝒜 ℐ n) := by
  constructor
  intro U s p hp
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hp U.2
  refine ⟨V, homOfLE hVU, ?_, hpV⟩
  obtain ⟨a, ha⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen S
    (quotProj 𝒜 ℐ n) V hV ((quotPiece 𝒜 ℐ n).val.map (homOfLE hVU).op s)
  exact ⟨(Stacks.quotπ (pieceι 𝒜 ℐ n).val).app (op V) a, ha⟩

/-! ### The multiplication of the quotient -/

/-- Transport of membership in the graded ideal along an equality of degrees. -/
theorem mem_piece_of_heq {k l : ℤ} (h : k = l) (U : S.Opens) {x : Γ(𝒜.piece k, U)}
    {y : Γ(𝒜.piece l, U)} (hxy : HEq x y)
    (hx : x ∈ (ℐ.piece k).toSubmodule.obj (op U)) :
    y ∈ (ℐ.piece l).toSubmodule.obj (op U) := by
  subst h
  rw [← eq_of_heq hxy]
  exact hx

/-- **A graded ideal absorbs multiplication on the right too.** The product of an arbitrary
homogeneous local section with a local section of the ideal lies in the ideal; this is the
`mul_mem` field read through the commutativity of `𝒜`, whose two sides live in the pieces of the
degrees `j + i` and `i + j`. -/
theorem mul_mem_right (i j : ℤ) (U : S.Opens) (a : Γ(𝒜.piece i, U)) {b : Γ(𝒜.piece j, U)}
    (hb : b ∈ (ℐ.piece j).toSubmodule.obj (op U)) :
    (𝒜.mul i j).app U a b ∈ (ℐ.piece (i + j)).toSubmodule.obj (op U) :=
  mem_piece_of_heq 𝒜 ℐ (add_comm j i) U (𝒜.mul_comm j i U b a) (ℐ.mul_mem j i U hb a)

/-- The multiplication of `𝒜`, read as a bilinear map of presheaves of modules. -/
def mulPre (i j : ℤ) :
    Stacks.BilinearMap (𝒜.piece i).val (𝒜.piece j).val (𝒜.piece (i + j)).val where
  app U := (𝒜.mul i j).app U.unop
  map_smul_left U r x y := (𝒜.mul i j).map_smul_left U.unop r x y
  map_smul_right U r x y := (𝒜.mul i j).map_smul_right U.unop r x y
  naturality f x y := (𝒜.mul i j).naturality (leOfHom f.unop) x y

/-- Multiplication followed by the projection to the quotient. -/
def mulToQuot (i j : ℤ) :
    Stacks.BilinearMap (𝒜.piece i).val (𝒜.piece j).val (quotPiece 𝒜 ℐ (i + j)).val :=
  (mulPre 𝒜 i j).postcomp (quotProj 𝒜 ℐ (i + j)).val

/-- Multiplication descends to the sectionwise quotient in the first variable, because the ideal
absorbs multiplication on the left. -/
def mulQuotLeft (i j : ℤ) :
    Stacks.BilinearMap (prePiece 𝒜 ℐ i) (𝒜.piece j).val (quotPiece 𝒜 ℐ (i + j)).val :=
  Stacks.BilinearMap.quotDescBil (pieceι 𝒜 ℐ i).val (mulToQuot 𝒜 ℐ i j) (fun U x y =>
    (quotProj_app_eq_zero_iff 𝒜 ℐ (i + j) U.unop _).2 (ℐ.mul_mem i j U.unop x.2 y))

/-- Multiplication descends to the sectionwise quotient in both variables. -/
def mulQuotBoth (i j : ℤ) :
    Stacks.BilinearMap (prePiece 𝒜 ℐ i) (prePiece 𝒜 ℐ j) (quotPiece 𝒜 ℐ (i + j)).val :=
  (Stacks.BilinearMap.quotDescBil (pieceι 𝒜 ℐ j).val (mulQuotLeft 𝒜 ℐ i j).flip (by
    intro U y q
    obtain ⟨s, rfl⟩ := Stacks.quotπ_surjective (pieceι 𝒜 ℐ i).val U q
    exact (quotProj_app_eq_zero_iff 𝒜 ℐ (i + j) U.unop _).2
      (mul_mem_right 𝒜 ℐ i j U.unop s y.2))).flip

/-- **The multiplication of the quotient `𝒜/ℐ`.** The sectionwise multiplication of the
sectionwise quotient, extended across the comparison map in each variable in turn: a bilinear map
into a sheaf does not see a local bijection. -/
def mulQuot (i j : ℤ) :
    Stacks.BilinearMap (quotPiece 𝒜 ℐ i).val (quotPiece 𝒜 ℐ j).val
      (quotPiece 𝒜 ℐ (i + j)).val :=
  (Stacks.BilinearMap.extend (quotPiece 𝒜 ℐ (i + j)).isSheaf (theta 𝒜 ℐ j)
    (Stacks.BilinearMap.extend (quotPiece 𝒜 ℐ (i + j)).isSheaf (theta 𝒜 ℐ i)
      (mulQuotBoth 𝒜 ℐ i j)).flip).flip

/-- The extended multiplication agrees with the sectionwise one on the sections that come from
the sectionwise quotient. -/
theorem mulQuot_app_theta (i j : ℤ) (U : (Opens ↥S)ᵒᵖ) (q : (prePiece 𝒜 ℐ i).obj U)
    (q' : (prePiece 𝒜 ℐ j).obj U) :
    (mulQuot 𝒜 ℐ i j).app U ((theta 𝒜 ℐ i).app U q) ((theta 𝒜 ℐ j).app U q') =
      (mulQuotBoth 𝒜 ℐ i j).app U q q' :=
  (Stacks.BilinearMap.extendVal_app (quotPiece 𝒜 ℐ (i + j)).isSheaf (theta 𝒜 ℐ j)
      (Stacks.BilinearMap.extend (quotPiece 𝒜 ℐ (i + j)).isSheaf (theta 𝒜 ℐ i)
        (mulQuotBoth 𝒜 ℐ i j)).flip q' ((theta 𝒜 ℐ i).app U q)).trans
    (Stacks.BilinearMap.extendVal_app (quotPiece 𝒜 ℐ (i + j)).isSheaf (theta 𝒜 ℐ i)
      (mulQuotBoth 𝒜 ℐ i j) q q')

/-- **The multiplication of the quotient is the multiplication of `𝒜`.** -/
theorem mulQuot_app_quotProj (i j : ℤ) (U : (Opens ↥S)ᵒᵖ) (s : (𝒜.piece i).val.obj U)
    (t : (𝒜.piece j).val.obj U) :
    (mulQuot 𝒜 ℐ i j).app U ((quotProj 𝒜 ℐ i).val.app U s)
        ((quotProj 𝒜 ℐ j).val.app U t) =
      (quotProj 𝒜 ℐ (i + j)).val.app U ((𝒜.mul i j).app U.unop s t) :=
  mulQuot_app_theta 𝒜 ℐ i j U ((Stacks.quotπ (pieceι 𝒜 ℐ i).val).app U s)
    ((Stacks.quotπ (pieceι 𝒜 ℐ j).val).app U t)

/-! ### The laws -/

/-- Transport along an equality of degrees commutes with the restriction maps of the quotient. -/
private theorem degCast_restr {i j : ℤ} (h : i = j) {U V : (Opens ↥S)ᵒᵖ} (f : U ⟶ V)
    (x : (quotPiece 𝒜 ℐ i).val.obj U) :
    Stacks.restr (quotPiece 𝒜 ℐ j).val f
        (Stacks.degCast (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj U) h x)
      = Stacks.degCast (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj V) h
          (Stacks.restr (quotPiece 𝒜 ℐ i).val f x) := by
  subst h; rfl

/-- Transport along an equality of degrees commutes with the projections to the quotient. -/
private theorem degCast_quotProj {i j : ℤ} (h : i = j) (U : (Opens ↥S)ᵒᵖ)
    (x : (𝒜.piece i).val.obj U) :
    (quotProj 𝒜 ℐ j).val.app U (Stacks.degCast (F := fun n ↦ (𝒜.piece n).val.obj U) h x)
      = Stacks.degCast (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj U) h
          ((quotProj 𝒜 ℐ i).val.app U x) := by
  subst h; rfl

/-- Transport along an equality of degrees preserves the relation between the restriction of a
section of the quotient and the projection of a section of `𝒜`. -/
private theorem restr_degCast_eq_quotProj {i j : ℤ} (h : i = j) {U V : (Opens ↥S)ᵒᵖ} (f : U ⟶ V)
    {p : (quotPiece 𝒜 ℐ i).val.obj U} {q : (𝒜.piece i).val.obj V}
    (hpq : Stacks.restr (quotPiece 𝒜 ℐ i).val f p = (quotProj 𝒜 ℐ i).val.app V q) :
    Stacks.restr (quotPiece 𝒜 ℐ j).val f
        (Stacks.degCast (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj U) h p) =
      (quotProj 𝒜 ℐ j).val.app V
        (Stacks.degCast (F := fun n ↦ (𝒜.piece n).val.obj V) h q) :=
  (degCast_restr 𝒜 ℐ h f p).trans <|
    (congrArg (Stacks.degCast (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj V) h) hpq).trans
      (degCast_quotProj 𝒜 ℐ h V q).symm

/-- Two sections of a separated presheaf of modules agree as soon as they agree after restriction
along the local lifts of three given sections, each along its own locally surjective morphism.

This is `Stacks.eq_of_forall_lift₂` with the sources allowed to differ, which is what the laws of
the quotient need: the three arguments of associativity live in three different degrees. -/
private theorem eq_of_forall_lift_three
    {M₁ M₂ M₃ N₁ N₂ N₃ P : PresheafOfModules.{u} S.ringCatSheaf.obj}
    (hP : Presheaf.IsSeparated (Opens.grothendieckTopology ↥S) P.presheaf)
    (α₁ : M₁ ⟶ N₁) (α₂ : M₂ ⟶ N₂) (α₃ : M₃ ⟶ N₃)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥S) α₁]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥S) α₂]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥S) α₃]
    {X : (Opens ↥S)ᵒᵖ} (a₁ : N₁.obj X) (a₂ : N₂.obj X) (a₃ : N₃.obj X) (x y : P.obj X)
    (h : ∀ {Y : (Opens ↥S)ᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj Y) (m₂ : M₂.obj Y) (m₃ : M₃.obj Y),
      α₁.app Y m₁ = N₁.map f a₁ → α₂.app Y m₂ = N₂.map f a₂ → α₃.app Y m₃ = N₃.map f a₃ →
      P.map f x = P.map f y) :
    x = y := by
  refine hP _ _ ((Opens.grothendieckTopology ↥S).intersection_covering
    ((Opens.grothendieckTopology ↥S).intersection_covering
      (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf _).map α₁) a₁)
      (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf _).map α₂) a₂))
    (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf _).map α₃) a₃)) _ _ ?_
  rintro Y f ⟨⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩⟩, ⟨m₃, hm₃⟩⟩
  exact h f.op m₁ m₂ m₃ hm₁ hm₂ hm₃

/-- The projections to the quotient are locally surjective: over an affine open of the base they
are surjective on sections, and the affine opens form a basis. -/
instance isLocallySurjective_quotProj (n : ℤ) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥S)
      (quotProj 𝒜 ℐ n).val := by
  constructor
  intro U s p hp
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hp U.2
  exact ⟨V, homOfLE hVU, Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen S
    (quotProj 𝒜 ℐ n) V hV _, hpV⟩

/-- The restriction of a product of two sections of the quotient, computed on local lifts: it is
the image of the product of the lifts. This is the one computation the laws are assembled from,
stated so that no rewriting takes place underneath a transport of degrees. -/
private theorem restr_mulQuot_lift (i j : ℤ) {U V : (Opens ↥S)ᵒᵖ} (f : U ⟶ V)
    (a : (quotPiece 𝒜 ℐ i).val.obj U) (b : (quotPiece 𝒜 ℐ j).val.obj U)
    (x : (𝒜.piece i).val.obj V) (y : (𝒜.piece j).val.obj V)
    (hx : (quotProj 𝒜 ℐ i).val.app V x = Stacks.restr (quotPiece 𝒜 ℐ i).val f a)
    (hy : (quotProj 𝒜 ℐ j).val.app V y = Stacks.restr (quotPiece 𝒜 ℐ j).val f b) :
    Stacks.restr (quotPiece 𝒜 ℐ (i + j)).val f ((mulQuot 𝒜 ℐ i j).app U a b)
      = (quotProj 𝒜 ℐ (i + j)).val.app V ((𝒜.mul i j).app V.unop x y) :=
  ((mulQuot 𝒜 ℐ i j).restr_bil f a b).trans (by
    rw [← hx, ← hy]
    exact mulQuot_app_quotProj 𝒜 ℐ i j V x y)

/-- **Associativity of the quotient multiplication.** -/
theorem mulQuot_assoc (i j k : ℤ) (U : S.Opens) (a : Γ(quotPiece 𝒜 ℐ i, U))
    (b : Γ(quotPiece 𝒜 ℐ j, U)) (c : Γ(quotPiece 𝒜 ℐ k, U)) :
    HEq ((mulQuot 𝒜 ℐ (i + j) k).app (op U) ((mulQuot 𝒜 ℐ i j).app (op U) a b) c)
      ((mulQuot 𝒜 ℐ i (j + k)).app (op U) a ((mulQuot 𝒜 ℐ j k).app (op U) b c)) := by
  refine Stacks.heq_of_degCast_eq
    (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj (op U)) (add_assoc i j k) ?_
  refine eq_of_forall_lift_three (quotPiece 𝒜 ℐ (i + (j + k))).isSheaf.isSeparated
    (quotProj 𝒜 ℐ i).val (quotProj 𝒜 ℐ j).val (quotProj 𝒜 ℐ k).val a b c _ _ ?_
  intro Y f x y z hx hy hz
  have hL := restr_mulQuot_lift 𝒜 ℐ (i + j) k f ((mulQuot 𝒜 ℐ i j).app (op U) a b) c
    ((𝒜.mul i j).app Y.unop x y) z (restr_mulQuot_lift 𝒜 ℐ i j f a b x y hx hy).symm hz
  have hR := restr_mulQuot_lift 𝒜 ℐ i (j + k) f a ((mulQuot 𝒜 ℐ j k).app (op U) b c) x
    ((𝒜.mul j k).app Y.unop y z) hx (restr_mulQuot_lift 𝒜 ℐ j k f b c y z hy hz).symm
  change Stacks.restr (quotPiece 𝒜 ℐ (i + (j + k))).val f _
    = Stacks.restr (quotPiece 𝒜 ℐ (i + (j + k))).val f _
  refine (restr_degCast_eq_quotProj 𝒜 ℐ (add_assoc i j k) f hL).trans ?_
  exact (congrArg _ (Stacks.degCast_eq_of_heq _ (𝒜.mul_assoc i j k Y.unop x y z))).trans hR.symm

/-- **Commutativity of the quotient multiplication.** -/
theorem mulQuot_comm (i j : ℤ) (U : S.Opens) (a : Γ(quotPiece 𝒜 ℐ i, U))
    (b : Γ(quotPiece 𝒜 ℐ j, U)) :
    HEq ((mulQuot 𝒜 ℐ i j).app (op U) a b) ((mulQuot 𝒜 ℐ j i).app (op U) b a) := by
  refine Stacks.heq_of_degCast_eq
    (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj (op U)) (add_comm i j) ?_
  refine eq_of_forall_lift_three (quotPiece 𝒜 ℐ (j + i)).isSheaf.isSeparated
    (quotProj 𝒜 ℐ i).val (quotProj 𝒜 ℐ j).val (quotProj 𝒜 ℐ i).val a b a _ _ ?_
  intro Y f x y _ hx hy _
  have hL := restr_mulQuot_lift 𝒜 ℐ i j f a b x y hx hy
  have hR := restr_mulQuot_lift 𝒜 ℐ j i f b a y x hy hx
  change Stacks.restr (quotPiece 𝒜 ℐ (j + i)).val f _
    = Stacks.restr (quotPiece 𝒜 ℐ (j + i)).val f _
  refine (restr_degCast_eq_quotProj 𝒜 ℐ (add_comm i j) f hL).trans ?_
  exact (congrArg _ (Stacks.degCast_eq_of_heq _ (𝒜.mul_comm i j Y.unop x y))).trans hR.symm

/-! ### The unit -/

/-- The unit of the quotient: the image of the unit of `𝒜`. -/
def quotOne (U : S.Opens) : Γ(quotPiece 𝒜 ℐ 0, U) :=
  (quotProj 𝒜 ℐ 0).val.app (op U) (𝒜.one U)

private theorem restr_quotOne {U V : (Opens ↥S)ᵒᵖ} (f : U ⟶ V) :
    Stacks.restr (quotPiece 𝒜 ℐ 0).val f (quotOne 𝒜 ℐ U.unop)
      = (quotProj 𝒜 ℐ 0).val.app V (𝒜.one V.unop) :=
  have h : Stacks.restr (𝒜.piece 0).val f (𝒜.one U.unop) = 𝒜.one V.unop :=
    𝒜.one_res (leOfHom f.unop)
  (Stacks.restr_app (quotProj 𝒜 ℐ 0).val f (𝒜.one U.unop)).symm.trans (congrArg _ h)

/-- The unit of the quotient is compatible with restriction. -/
theorem quotOne_res {U V : S.Opens} (h : U ≤ V) :
    (quotPiece 𝒜 ℐ 0).presheaf.map (homOfLE h).op (quotOne 𝒜 ℐ V) = quotOne 𝒜 ℐ U :=
  restr_quotOne 𝒜 ℐ (homOfLE h).op

/-- **The unit of the quotient is a left identity.** -/
theorem mulQuot_one_mul (i : ℤ) (U : S.Opens) (a : Γ(quotPiece 𝒜 ℐ i, U)) :
    HEq ((mulQuot 𝒜 ℐ 0 i).app (op U) (quotOne 𝒜 ℐ U) a) a := by
  refine Stacks.heq_of_degCast_eq
    (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj (op U)) (zero_add i) ?_
  refine Stacks.eq_of_forall_lift (quotPiece 𝒜 ℐ i).isSheaf.isSeparated
    (quotProj 𝒜 ℐ i).val a _ _ ?_
  intro Y f x hx
  have hL := restr_mulQuot_lift 𝒜 ℐ 0 i f (quotOne 𝒜 ℐ U) a (𝒜.one Y.unop) x
    (restr_quotOne 𝒜 ℐ f).symm hx
  change Stacks.restr (quotPiece 𝒜 ℐ i).val f _ = Stacks.restr (quotPiece 𝒜 ℐ i).val f _
  refine (restr_degCast_eq_quotProj 𝒜 ℐ (zero_add i) f hL).trans ?_
  exact (congrArg _ (Stacks.degCast_eq_of_heq _ (𝒜.one_mul i Y.unop x))).trans hx

/-- **The unit of the quotient is a right identity.** -/
theorem mulQuot_mul_one (i : ℤ) (U : S.Opens) (a : Γ(quotPiece 𝒜 ℐ i, U)) :
    HEq ((mulQuot 𝒜 ℐ i 0).app (op U) a (quotOne 𝒜 ℐ U)) a := by
  refine Stacks.heq_of_degCast_eq
    (F := fun n ↦ (quotPiece 𝒜 ℐ n).val.obj (op U)) (add_zero i) ?_
  refine Stacks.eq_of_forall_lift (quotPiece 𝒜 ℐ i).isSheaf.isSeparated
    (quotProj 𝒜 ℐ i).val a _ _ ?_
  intro Y f x hx
  have hL := restr_mulQuot_lift 𝒜 ℐ i 0 f a (quotOne 𝒜 ℐ U) x (𝒜.one Y.unop) hx
    (restr_quotOne 𝒜 ℐ f).symm
  change Stacks.restr (quotPiece 𝒜 ℐ i).val f _ = Stacks.restr (quotPiece 𝒜 ℐ i).val f _
  refine (restr_degCast_eq_quotProj 𝒜 ℐ (add_zero i) f hL).trans ?_
  exact (congrArg _ (Stacks.degCast_eq_of_heq _ (𝒜.mul_one i Y.unop x))).trans hx

/-! ### The quotient as a sheaf-level graded algebra -/

/-- The negative homogeneous pieces of the quotient vanish, because those of `𝒜` do. -/
theorem isZero_quotPiece (n : ℤ) (hn : n < 0) : IsZero (quotPiece 𝒜 ℐ n) := by
  have : Epi (pieceι 𝒜 ℐ n) := ⟨fun g h _ => (𝒜.negative_isZero n hn).eq_of_src g h⟩
  exact isZero_cokernel_of_epi (pieceι 𝒜 ℐ n)

/-- The quotient multiplication, as an `𝒪_S`-bilinear map of the homogeneous pieces. -/
def mulSheaf (i j : ℤ) :
    SheafBilinearMap (quotPiece 𝒜 ℐ i) (quotPiece 𝒜 ℐ j) (quotPiece 𝒜 ℐ (i + j)) where
  app U := (mulQuot 𝒜 ℐ i j).app (op U)
  map_smul_left U r x y := (mulQuot 𝒜 ℐ i j).map_smul_left (op U) r x y
  map_smul_right U r x y := (mulQuot 𝒜 ℐ i j).map_smul_right (op U) r x y
  naturality h x y := (mulQuot 𝒜 ℐ i j).naturality (homOfLE h).op x y

/-- **The quotient `𝒜/ℐ` of a sheaf-level graded `𝒪_S`-algebra by a graded ideal with
quasi-coherent pieces.** Its degree-`n` piece is the cokernel of `ℐ_n ⟶ 𝒜_n` and its
multiplication is the multiplication of `𝒜`, descended degreewise. -/
def quotAlgebra : SheafGradedAlgebra S where
  piece n := quotPiece 𝒜 ℐ n
  mul i j := mulSheaf 𝒜 ℐ i j
  one U := quotOne 𝒜 ℐ U
  one_res h := quotOne_res 𝒜 ℐ h
  mul_assoc i j k U a b c := mulQuot_assoc 𝒜 ℐ i j k U a b c
  one_mul i U a := mulQuot_one_mul 𝒜 ℐ i U a
  mul_one i U a := mulQuot_mul_one 𝒜 ℐ i U a
  mul_comm i j U a b := mulQuot_comm 𝒜 ℐ i j U a b
  negative_isZero n hn := isZero_quotPiece 𝒜 ℐ n hn
  isQuasicoherent n := isQuasicoherent_quotPiece 𝒜 ℐ n

/-- The degree-`n` piece of `quotAlgebra` is `quotPiece`. -/
@[simp]
theorem quotAlgebra_piece (n : ℤ) : (quotAlgebra 𝒜 ℐ).piece n = quotPiece 𝒜 ℐ n := rfl

/-- The multiplication of `quotAlgebra` over an open is the descended multiplication `mulQuot`. -/
@[simp]
theorem quotAlgebra_mul_app (i j : ℤ) (U : S.Opens) :
    ((quotAlgebra 𝒜 ℐ).mul i j).app U = (mulQuot 𝒜 ℐ i j).app (op U) := rfl

/-- **The quotient homomorphism `𝒜 ⟶ 𝒜/ℐ`.** -/
def quotHom : SheafGradedAlgebraHom 𝒜 (quotAlgebra 𝒜 ℐ) where
  app n := quotProj 𝒜 ℐ n
  app_mul i j U a b := (mulQuot_app_quotProj 𝒜 ℐ i j (op U) a b).symm
  app_one _ := rfl

/-- The degree-`n` component of `quotHom` is the projection `quotProj`. -/
@[simp]
theorem quotHom_app (n : ℤ) : (quotHom 𝒜 ℐ).app n = quotProj 𝒜 ℐ n := rfl

/-- **The quotient homomorphism is surjective on homogeneous sections over the affine opens of
the base**, in every degree: it is an epimorphism of quasi-coherent modules in each degree, and
the global sections functor is exact on quasi-coherent modules over an affine open.

This is the hypothesis of `Stacks.AlgebraicGeometry.ProjBundleSurjection.map`, so the quotient
produces the closed immersion `Proj_S(𝒜/ℐ) ⟶ Proj_S(𝒜)`. -/
theorem surjectiveOnAffineSections_quotHom :
    ProjBundleSurjection.SurjectiveOnAffineSections (quotHom 𝒜 ℐ) := fun U hU n b =>
  Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen S (quotProj 𝒜 ℐ (n : ℤ)) U hU b

/-- **The homogeneous pieces of a graded quotient inherit finiteness of type.** -/
theorem isFiniteType_quotPiece (n : ℤ) (h : (𝒜.piece n).IsFiniteType) :
    (quotPiece 𝒜 ℐ n).IsFiniteType := by
  have : @Epi (SheafOfModules.{u} S.ringCatSheaf) _ (𝒜.piece n) (quotPiece 𝒜 ℐ n)
      (quotProj 𝒜 ℐ n) := epi_quotProj 𝒜 ℐ n
  exact Stacks.SheafOfModules.isFiniteType_of_epi (M := 𝒜.piece n) (N := quotPiece 𝒜 ℐ n)
    (quotProj 𝒜 ℐ n) h

/-- **Generation in degree one passes to a graded quotient**, over an open of the base over which
the quotient homomorphism is surjective on sections.

The degree-`1 + n` sections of the quotient over an affine open are images of those of `𝒜`, and
the preimage of an additive subgroup containing all products of a degree-one by a degree-`n`
section of the quotient contains all such products in `𝒜`. -/
theorem isGeneratedInDegreeOneAt_quotAlgebra (U : S.Opens) (hU : IsAffineOpen U)
    (hgen : 𝒜.IsGeneratedInDegreeOneAt U) :
    (quotAlgebra 𝒜 ℐ).IsGeneratedInDegreeOneAt U := by
  intro n P hP
  let φ : Γ(𝒜.piece (1 + (n : ℤ)), U) →+ Γ(quotPiece 𝒜 ℐ (1 + (n : ℤ)), U) :=
    { toFun := (quotProj 𝒜 ℐ (1 + (n : ℤ))).val.app (op U)
      map_zero' := map_zero _
      map_add' := map_add _ }
  have hcomap : P.comap φ = ⊤ := by
    refine hgen n (P.comap φ) fun x y => ?_
    have h2 := hP ((quotProj 𝒜 ℐ 1).val.app (op U) x)
      ((quotProj 𝒜 ℐ (n : ℤ)).val.app (op U) y)
    exact Eq.mp (congrArg (· ∈ P) (mulQuot_app_quotProj 𝒜 ℐ 1 (n : ℤ) (op U) x y)) h2
  refine (AddSubgroup.eq_top_iff' P).2 fun z => ?_
  obtain ⟨w, rfl⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen S
    (quotProj 𝒜 ℐ (1 + (n : ℤ))) U hU z
  exact (hcomap ▸ AddSubgroup.mem_top w : w ∈ P.comap φ)

/-! ### The kernel on the graded ring of sections -/

/-- The degree-`n` component of the image of a section of the graded ring of sections is the
image of its degree-`n` component. -/
private theorem sectionRingHom_apply {A B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (U : S.Opens) (x : A.sectionRing U) (n : ℕ) :
    ψ.sectionRingHom U x n = ψ.sectionPieceHom U n (x n) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, DFinsupp.zero_apply, DFinsupp.zero_apply, map_zero]
  | of m y =>
    rw [ψ.sectionRingHom_of]
    by_cases h : m = n
    · subst h
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),
        map_zero]
  | add x y hx hy =>
    rw [map_add, DFinsupp.add_apply, DFinsupp.add_apply, hx, hy, map_add]

/-- **The kernel of the quotient homomorphism on the graded ring of sections over an arbitrary
open of the base**: a section of `⨁_{n ≥ 0} Γ(𝒜_n, U)` dies in `⨁_{n ≥ 0} Γ((𝒜/ℐ)_n, U)` exactly
when every one of its homogeneous components is a local section of `ℐ`.

No affineness and no sheafification intervene, because `quotProj_app_eq_zero_iff` holds over every
open. This is the kernel half of the graded identification of `Γ(U, 𝒜/ℐ)` with `Γ(U, 𝒜)/ℐ(U)`
that the chart comparison of Tag 0801 is stated at; the other half, surjectivity over an affine
open, is `Stacks.AlgebraicGeometry.ProjBundleSurjection.surjective_sectionHom` applied to
`surjectiveOnAffineSections_quotHom`. -/
theorem sectionHom_quotHom_eq_zero_iff (U : S.Opens) (x : 𝒜.sectionRing U) :
    (quotHom 𝒜 ℐ).sectionHom U x = 0 ↔
      ∀ n : ℕ, x n ∈ (ℐ.piece (n : ℤ)).toSubmodule.obj (op U) := by
  have hcoe : (quotHom 𝒜 ℐ).sectionHom U x = (quotHom 𝒜 ℐ).sectionRingHom U x := rfl
  have key : ∀ n : ℕ, (quotHom 𝒜 ℐ).sectionRingHom U x n = 0 ↔
      x n ∈ (ℐ.piece (n : ℤ)).toSubmodule.obj (op U) := by
    intro n
    rw [sectionRingHom_apply]
    exact quotProj_app_eq_zero_iff 𝒜 ℐ (n : ℤ) U (x n)
  rw [hcoe]
  refine ⟨fun h n => (key n).1 ?_, fun h => DFinsupp.ext fun n => ?_⟩
  · rw [h]
    exact DFinsupp.zero_apply n
  · exact ((key n).2 (h n)).trans (DFinsupp.zero_apply n).symm

/-! ### The closed subscheme the quotient cuts out -/

/-- **The relative Proj of a graded quotient, mapped into the relative Proj of `𝒜`.** -/
def projQuotientHom :
    (relativeProj (quotAlgebra 𝒜 ℐ)).scheme ⟶ (relativeProj 𝒜).scheme :=
  ProjBundleSurjection.map (surjectiveOnAffineSections_quotHom 𝒜 ℐ)

/-- **`Proj_S(𝒜/ℐ)` is a closed subscheme of `Proj_S(𝒜)`.** -/
@[ega "II 3.6.2" "(i), special case"]
theorem isClosedImmersion_projQuotientHom : IsClosedImmersion (projQuotientHom 𝒜 ℐ) :=
  ProjBundleSurjection.isClosedImmersion_map (surjectiveOnAffineSections_quotHom 𝒜 ℐ)

/-- The closed immersion is one over the base. -/
theorem projQuotientHom_comp_toBase :
    projQuotientHom 𝒜 ℐ ≫ (relativeProj 𝒜).toBase =
      (relativeProj (quotAlgebra 𝒜 ℐ)).toBase :=
  ProjBundleSurjection.map_comp_toBase (surjectiveOnAffineSections_quotHom 𝒜 ℐ)

/-- **Tag 0801's conclusion-as-data, from a graded ideal and the identification.** A graded ideal
with quasi-coherent pieces supplies every field of
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.GradedQuotientPresentation` except the
isomorphism `Z ≅ Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)`: the quotient algebra, the quotient homomorphism,
and its surjectivity on the sections over the affine opens of the base. -/
def gradedQuotientPresentationOfIso {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    (e : Z ≅ (relativeProj (quotAlgebra 𝒜 ℐ)).scheme)
    (he : e.hom ≫ projQuotientHom 𝒜 ℐ = i) : GradedQuotientPresentation 𝒜 i where
  target := quotAlgebra 𝒜 ℐ
  hom := quotHom 𝒜 ℐ
  surjective := surjectiveOnAffineSections_quotHom 𝒜 ℐ
  iso := e
  iso_comp := he

/-! ### The identification, as an equality of ideal sheaves -/

/-- **An identification forces the two ideal sheaves to agree.** If `Z` is identified with
`Proj_S(𝒜/ℐ)` over `Proj_S(𝒜)`, the two morphisms into `Proj_S(𝒜)` have the same kernel, because
`AlgebraicGeometry.Scheme.Hom.ker` is unchanged by precomposition with an isomorphism. -/
theorem ker_eq_ker_projQuotientHom_of_iso {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    (e : Z ≅ (relativeProj (quotAlgebra 𝒜 ℐ)).scheme)
    (he : e.hom ≫ projQuotientHom 𝒜 ℐ = i) :
    i.ker = (projQuotientHom 𝒜 ℐ).ker := by
  conv_lhs => rw [← he]
  exact Scheme.Hom.ker_comp_of_isIso e.hom (projQuotientHom 𝒜 ℐ)

/-- **An equality of ideal sheaves produces the identification.** Both morphisms into `Proj_S(𝒜)`
are closed immersions — `i` by hypothesis and the projection of the quotient by
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isClosedImmersion_projQuotientHom` — so when
their kernels agree the universal property of a closed immersion,
`AlgebraicGeometry.IsClosedImmersion.lift`, produces a morphism `Z ⟶ Proj_S(𝒜/ℐ)` over
`Proj_S(𝒜)`, and `AlgebraicGeometry.IsClosedImmersion.isIso_lift` says it is invertible. -/
theorem exists_iso_projQuotient_of_ker_eq {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    [IsClosedImmersion i] (h : i.ker = (projQuotientHom 𝒜 ℐ).ker) :
    ∃ e : Z ≅ (relativeProj (quotAlgebra 𝒜 ℐ)).scheme, e.hom ≫ projQuotientHom 𝒜 ℐ = i := by
  have : IsClosedImmersion (projQuotientHom 𝒜 ℐ) := isClosedImmersion_projQuotientHom 𝒜 ℐ
  have : IsIso (IsClosedImmersion.lift (projQuotientHom 𝒜 ℐ) i h.symm.le) :=
    IsClosedImmersion.isIso_lift (projQuotientHom 𝒜 ℐ) i h.symm
  exact ⟨asIso (IsClosedImmersion.lift (projQuotientHom 𝒜 ℐ) i h.symm.le),
    IsClosedImmersion.lift_fac (projQuotientHom 𝒜 ℐ) i h.symm.le⟩

/-- **Tag 0801's remaining clause, for a graded ideal already in hand, is exactly an equality of
ideal sheaves on `Proj_S(𝒜)`.** This is the relative analogue of
`Stacks.ProjQuotientSaturationKer.saturationIdentification_iff_ker_eq`, and it is what reduces the
identification `Z ≅ Proj_S(𝒜/ℐ)` to a local computation: `Scheme.Hom.ker` is determined by its
ideals on the affine opens, so no glueing of isomorphisms has to be done by hand. -/
theorem exists_iso_projQuotient_iff_ker_eq {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    [IsClosedImmersion i] :
    (∃ e : Z ≅ (relativeProj (quotAlgebra 𝒜 ℐ)).scheme, e.hom ≫ projQuotientHom 𝒜 ℐ = i) ↔
      i.ker = (projQuotientHom 𝒜 ℐ).ker :=
  ⟨fun ⟨e, he⟩ => ker_eq_ker_projQuotientHom_of_iso 𝒜 ℐ i e he,
    exists_iso_projQuotient_of_ker_eq 𝒜 ℐ i⟩

/-- **Tag 0801's conclusion-as-data, from a graded ideal and an equality of ideal sheaves.** This
is `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.gradedQuotientPresentationOfIso` with its
isomorphism replaced by the hypothesis that `Z` and `Proj_S(𝒜/ℐ)` cut out the same ideal sheaf on
`Proj_S(𝒜)`. -/
def gradedQuotientPresentationOfKerEq {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    [IsClosedImmersion i] (h : i.ker = (projQuotientHom 𝒜 ℐ).ker) :
    GradedQuotientPresentation 𝒜 i :=
  haveI : IsClosedImmersion (projQuotientHom 𝒜 ℐ) := isClosedImmersion_projQuotientHom 𝒜 ℐ
  haveI : IsIso (IsClosedImmersion.lift (projQuotientHom 𝒜 ℐ) i h.symm.le) :=
    IsClosedImmersion.isIso_lift (projQuotientHom 𝒜 ℐ) i h.symm
  gradedQuotientPresentationOfIso 𝒜 ℐ i
    (asIso (IsClosedImmersion.lift (projQuotientHom 𝒜 ℐ) i h.symm.le))
    (IsClosedImmersion.lift_fac (projQuotientHom 𝒜 ℐ) i h.symm.le)

/-- **The cover form of Tag 0801's remaining clause.** It is enough to compare, over each member
of a family of affine opens of `Proj_S(𝒜)` whose supremum is `⊤`, the kernels of the two maps on
sections: the one induced by the closed subscheme and the one induced by the projection of the
quotient.

Both morphisms are closed immersions, hence quasi-compact, so
`AlgebraicGeometry.Scheme.Hom.ker_apply` computes each ideal sheaf on an affine open as the kernel
of the map on sections, and `AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top` glues.
The affine opens to use are the standard opens of the charts of `Proj_S(𝒜)`, on which the
comparison is the absolute statement of
`Stacks.ProjQuotientFiniteCover.app_awayMk_eq_zero_iff_of_cover`. -/
theorem ker_eq_ker_projQuotientHom_of_ker_app_eq {Z : Scheme.{u}}
    (i : Z ⟶ (relativeProj 𝒜).scheme) [IsClosedImmersion i] {ι : Type*}
    (W : ι → (relativeProj 𝒜).scheme.affineOpens) (hW : ⨆ k, (W k).1 = ⊤)
    (H : ∀ k, RingHom.ker (i.app (W k)).hom =
      RingHom.ker ((projQuotientHom 𝒜 ℐ).app (W k)).hom) :
    i.ker = (projQuotientHom 𝒜 ℐ).ker := by
  have : IsClosedImmersion (projQuotientHom 𝒜 ℐ) := isClosedImmersion_projQuotientHom 𝒜 ℐ
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W hW fun k => ?_
  rw [Scheme.Hom.ker_apply i (W k), Scheme.Hom.ker_apply (projQuotientHom 𝒜 ℐ) (W k)]
  exact H k

/-- **Tag 0801's conclusion-as-data, from a graded ideal and a chartwise comparison of kernels.**
The composite of
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.ker_eq_ker_projQuotientHom_of_ker_app_eq` with
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.gradedQuotientPresentationOfKerEq`. -/
def gradedQuotientPresentationOfKerAppEq {Z : Scheme.{u}} (i : Z ⟶ (relativeProj 𝒜).scheme)
    [IsClosedImmersion i] {ι : Type*} (W : ι → (relativeProj 𝒜).scheme.affineOpens)
    (hW : ⨆ k, (W k).1 = ⊤)
    (H : ∀ k, RingHom.ker (i.app (W k)).hom =
      RingHom.ker ((projQuotientHom 𝒜 ℐ).app (W k)).hom) :
    GradedQuotientPresentation 𝒜 i :=
  gradedQuotientPresentationOfKerEq 𝒜 ℐ i
    (ker_eq_ker_projQuotientHom_of_ker_app_eq 𝒜 ℐ i W hW H)

/-! ### What the quotient does not yet give -/

/-- **The quotient homomorphism is surjective, and its kernel is `ℐ`.** Together with
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.quotProj_app_eq_zero_iff` this is the
degreewise exactness of `ℐ ⟶ 𝒜 ⟶ 𝒜/ℐ` on the sections over an affine open of the base. -/
theorem exact_quotHom_app (n : ℤ) (U : S.Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((quotProj 𝒜 ℐ n).val.app (op U)) ∧
      ∀ s : Γ(𝒜.piece n, U), (quotProj 𝒜 ℐ n).val.app (op U) s = 0 ↔
        s ∈ (ℐ.piece n).toSubmodule.obj (op U) :=
  ⟨Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen S (quotProj 𝒜 ℐ n) U hU,
    quotProj_app_eq_zero_iff 𝒜 ℐ n U⟩

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
