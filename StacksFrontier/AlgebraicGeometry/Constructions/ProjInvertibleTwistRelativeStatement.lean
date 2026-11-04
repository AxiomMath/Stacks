module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeCanonical
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeGluing

/-!
# Tag 02NC over a base scheme: intermediate results in one statement

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible `𝒪_S`-module
and `ℬ_d = 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}` the twist of `𝒜` by it
(`Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist`, Tag 02NB). Tag 02NC asserts a **canonical
isomorphism** `g : P = Proj_S(𝒜) → Proj_S(ℬ) = P'` over `S`, with

1. isomorphisms `θ_n : g^*𝒪_{P'}(n) → 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` fitting together into an isomorphism
   of `ℤ`-graded algebras, and
2. for every open `V ⊆ S`, a commuting diagram on homogeneous sections.

Clause (3) of the source is the placeholder `Add more here as necessary.` and has no counterpart.

`Stacks.ProjInvertibleTwistRelativeStatement.relativeTag02NC` collects, as one theorem over an
**arbitrary base scheme**, everything the development proves of that assertion.

## Why this carries no `stacks` attribute

The whole tag — `g`, clause (1) with its graded assembly and clause (2) for every open of the
base — is stated as one theorem in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistRelativeTag.lean`, which carries
the registration. This file collects intermediate results along the way and is not a statement of
the tag.

## The conjuncts, against the source

The parenthesised numbers are line numbers in the source text of the lemma, `constructions.tex`
`:4695–4743`:

1. **clause (2)'s multiplication is an isomorphism** (`:4725–4740`) — over an affine open `V` of
   the base the map labelled *multiply* in the source's diagram, from
   `𝒜_n(V) ⊗_{Γ(S,V)} ℒ^{⊗ n}(V)` to `ℬ_n(V)`, is bijective; and the pure tensors span, so the
   top row of the diagram is onto. This is unconditional: no trivialization and no global
   section.
2. **the comparison is the source's *multiply*** (`:4727`) — the degree-`d` comparison attached
   to a section `x` of `ℒ` over an arbitrary open is the canonical image of `a ⊗ x^d`, which is
   what identifies the morphism below with the one the tag describes.
3. **the tag over one open of the base, with no global section of `ℒ`** (`:4700–4714`) — for
   every open `V` and section `x` of `ℒ` over `V` whose powers trivialize the powers of `ℒ`
   there: the comparison is defined on all of `Proj ℬ(V)`, it is an **isomorphism**
   `Proj ℬ(V) ≅ Proj 𝒜(V)`, and every comparison map on the twisting sheaves attached to it is an
   isomorphism. For `V` affine these two spectra are the preimages of `V` in `P'` and `P` by
   `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.chartIsoPreimage`, so this is `g` over that
   chart.
4. **the degreewise canonicity** — rescaling the section by a function on the open rescales the
   comparison by its `d`-th power, i.e. composes it with a degree scaling. Two sections
   trivializing `ℒ` over one open differ by a unit, so this is the compatibility the glueing
   would consume on overlaps; the absolute input that turns it into an equality of morphisms of
   homogeneous spectra is `Stacks.GradedRing.Proj_map_eq_of_target_degreeScale`.
5. **the morphism over an arbitrary base scheme when `ℒ` is trivialized globally**
   (`:4700–4724`) — for a global section `ℓ` of `ℒ` whose induced map `𝒪_S ⟶ ℒ` is an
   isomorphism: `U(ψ) = Proj_S(𝒜)`, the morphism `Proj_S(𝒜) ⟶ Proj_S(ℬ)` is an isomorphism, it
   is a morphism **over `S`** — the triangle of the source's diagram — every comparison map on
   the twisting sheaves attached to it is an isomorphism, and these fit together into an
   isomorphism of `ℤ`-graded algebras. This is the source's first step, *"this is the identity
   map when `ℒ ≅ 𝒪_S`"*, over a base scheme rather than over `Spec R`.
6. **the glueing** (`:4700–4710` and the source's proof) — over an arbitrary base scheme, the
   canonical isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)` over `S`
   (`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistIso`, whose inverse is the tag's
   `g`) is the unique isomorphism over `S` restricting to the comparison of 3 over every member of
   the basis of affine opens of `S` trivializing `ℒ`
   (`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.existsUnique_relativeTwistIsoOver`).

The maps on twisting sheaves in 3 and 5 are the comparisons attached to a morphism of homogeneous
spectra by Tag 07ZG, in the direction of that morphism; they are not the source's `θ_n`, whose
target carries the factor `π^*ℒ^{⊗ n}`. The source's `θ_n` and `θ` are
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistThetaIso` and
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistTheta`.

## The glueing

**The glueing is done.** `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistIso` is
the tag's `g`, over an arbitrary base scheme, and
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.existsUnique_relativeTwistIsoOver` is its
uniqueness over `S`. Its ingredients are the following:

* the extraction of the unit from two trivializations of `ℒ` over one open is
  `Stacks.SheafOfModules.TensorGenerator.exists_unit_smul_generator`, the relative form of
  `Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton`;
* the passage from the partial `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` of 3 to
  `AlgebraicGeometry.Proj.map` is
  `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map`.
  What that needs supplied is Mathlib's hypothesis `ℬ₊ ≤ 𝒜₊.map ψ`, which is
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.irrelevant_le_map_psiSectionAt`;
* compatibility of 3 with the chart transitions is
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projInclusionMap_comp_projMap_psiSectionAt`;
* that the comparison of 3 is a morphism **over** the open of the base — not implied by the
  other entries of this list, since the comparison is `Proj.map` of
  a graded homomorphism whose degree-zero part is the canonical `𝒜_0(V) → 𝒜_0(V) ⊗ 𝒪(V)` and not
  an identity — is
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_comp_projInclusionToOpen`.
  Its route is `Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_comp_toOpen`'s, with the
  degree-zero compatibility of the comparison in place of that of a surjection;
* that the powers of a section trivializing `ℒ` over `V` trivialize the powers of `ℒ` there is
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.trivializesPower_of_one`, so 3 is conditional
  on ONE trivialization rather than on a family;
* a **basis** of opens of `S` over which `ℒ` is trivialized is
  `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isBasis_trivializingOpens`. A
  trivialization restricts by `Stacks.SheafOfModules.overIsoRestrict`, with the generator law
  `Stacks.SheafOfModules.overIsoSection_restrict`, and the same basis argument is already carried
  out for a finite locally free module of rank `r` in
  `Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.isBasis_trivializing`.

`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.existsUnique_isoOver` is **not** the glueing
tool: that theorem is stated for a
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`, whose `chart` field demands a chart over
**every** affine open of `S`; an invertible `ℒ` is trivialized only locally, so over an affine
open carrying no trivializing section there is no comparison to put there, and the datum cannot be
built. The theorem that applies, and that is used, is the one it is itself proved from,
`AlgebraicGeometry.Scheme.BasisGluingData.existsUnique_isoOver` of
`StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis` (Tag 01LH, uniqueness), which
takes an **arbitrary** basis `B` of the topology of `S`.

Clause (1) in the general case, a single `θ` over an arbitrary base scheme, is built on top of
conjunct 6 in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistRelativeThetaData.lean` and the
files depending on it, and the tag is stated in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistRelativeTag.lean`.


## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
-/

@[expose] public noncomputable section

open CategoryTheory Filter Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.RelativeInvertibleTwist
open Stacks.AlgebraicGeometry.AffineOpenTensorSections
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.ProjInvertibleTwistRelativeStatement

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- **What the development proves of Stacks Tag 02NC over an arbitrary base scheme**, in one
statement. `𝒜` is a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible `𝒪_S`-module and
`ℬ = ⨁_d 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}` its twist.

The six conjuncts are enumerated in the module documentation, with the source line each
discharges. In order: clause (2)'s *multiply* map is an isomorphism over every affine open of the
base and the pure tensors span; the comparison attached to a local section of `ℒ` **is** that
*multiply* map; over every open of the base carrying a section whose powers trivialize the powers
of `ℒ`, the comparison is everywhere defined, is an **isomorphism of homogeneous spectra**, and has
every comparison map on the twisting sheaves an isomorphism; rescaling the section composes the
comparison with a degree scaling, which is the canonicity the glueing consumes on overlaps; for `ℒ`
trivialized by a **global** section, over an arbitrary base scheme: the morphism of relative
homogeneous spectra, its invertibility, its being a morphism over `S`, and its comparison maps on
the twisting sheaves both componentwise and as a graded assembly; and **the glueing**, which
produces the tag's `g : Proj_S(𝒜) ⟶ Proj_S(ℬ)` over an arbitrary base scheme as the unique
isomorphism over `S` restricting to the comparison over every member of the trivializing basis.

This collects intermediate results and carries no `stacks` attribute; the whole tag is stated in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistRelativeTag.lean`. -/
theorem relativeTag02NC :
    -- 1. clause (2)'s `multiply`: over an affine open of the base the map
    --    `𝒜_n(V) ⊗_{Γ(S,V)} ℒ^{⊗ n}(V) ⟶ ℬ_n(V)` is bijective, and the pure tensors span
    (∀ (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ),
        Function.Bijective (twistPieceSectionsEquiv L 𝒜 hV n)) ∧
      (∀ (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ),
        Submodule.span Γ(S, V)
            (Set.range fun p : Γ(𝒜.piece n, V) × Γ(tpMod L n, V) =>
              gammaTmul (𝒜.piece n) (tpMod L n) V p.1 p.2) = ⊤) ∧
      -- 2. the comparison attached to a local section is the source's `multiply` map
      (∀ (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ) (a : 𝒜.sectionPieces V d),
        psiPieceAt L 𝒜 V x d a =
          gammaTmul (𝒜.piece (d : ℤ)) (tpMod L d) V a (powSecAtMod L V x d)) ∧
      -- 3. the tag over one open of the base, with no global section of `ℒ`
      (∀ (V : S.Opens) (x : (tp L 1).val.obj (op V)),
        (∀ᶠ d : ℕ in atTop, TrivializesPower L V x d) →
          mapDomain (𝒜.grading V) ((twist 𝒜 L).grading V) (psiSectionAt L 𝒜 V x) = ⊤ ∧
            IsIso (mapHom (𝒜.grading V) ((twist 𝒜 L).grading V) (psiSectionAt L 𝒜 V x)) ∧
            ∀ n : ℤ, IsIso ((projMapData (𝒜.grading V) ((twist 𝒜 L).grading V)
              (psiSectionAt L 𝒜 V x)).twistMap n)) ∧
      -- 4. the degreewise canonicity: rescaling the section is a degree scaling
      (∀ (V : S.Opens) (u : funsAt V) (x : (tp L 1).val.obj (op V)),
        psiSectionAt L 𝒜 V (u • x) =
          (Stacks.GradedRing.degreeScale ((twist 𝒜 L).grading V)
            ((twist 𝒜 L).strHom_mem V u)).comp (psiSectionAt L 𝒜 V x)) ∧
      -- 5. the morphism over an arbitrary base scheme, for `ℒ` trivialized by a global section
      (∀ (ℓ : (tp L 1).sections), IsIso (powHom L ℓ 1) →
        (psi L 𝒜 ℓ).relativeMapDomain = ⊤ ∧
          IsIso (Tag07ZGMorphism.relativeMapHom (psi L 𝒜 ℓ)) ∧
          Tag07ZGMorphism.relativeMapHom (psi L 𝒜 ℓ) ≫ (RelativeProj.relativeProj 𝒜).toBase =
            (psi L 𝒜 ℓ).relativeMapDomain.ι ≫
              (RelativeProj.relativeProj (twist 𝒜 L)).toBase ∧
          (∀ n : ℤ, IsIso (Tag07ZGTwist.relativeTwistMap (psi L 𝒜 ℓ) n)) ∧
          Nonempty (Stacks.RingedSpace.pullbackGradedAlgebra
              (Tag07ZGMorphism.relativeMapHom (psi L 𝒜 ℓ)).toLRSHom.toShHom
              (Tag07ZGTwist.twistAlgebra 𝒜) ≅
            Stacks.RingedSpace.pullbackGradedAlgebra
              (psi L 𝒜 ℓ).relativeMapDomain.ι.toLRSHom.toShHom
              (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)))) ∧
      -- 6. the glueing: the tag's `g`, over an arbitrary base scheme, as the unique isomorphism
      --    of relative homogeneous spectra over `S` which is the comparison over every member of
      --    the basis of affine opens of `S` trivializing `ℒ`
      (∃! e : (RelativeProj.relativeProj (twist 𝒜 L)).scheme ≅ (RelativeProj.relativeProj 𝒜).scheme,
        (∀ V : trivializingOpens L,
            (RelativeProj.relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ≫ e.hom =
              basisComparison L 𝒜 V ≫
                (RelativeProj.relativeProj 𝒜).chart (V : S.Opens) V.2.1) ∧
          e.hom ≫ (RelativeProj.relativeProj 𝒜).toBase =
            (RelativeProj.relativeProj (twist 𝒜 L)).toBase) :=
  ⟨fun _ hV n => (twistPieceSectionsEquiv L 𝒜 hV n).bijective,
    fun _ hV n => span_twistPieceSections_eq_top L 𝒜 hV n,
    fun V x d a => psiPieceAt_eq_gammaTmul L 𝒜 V x d a,
    fun _ _ hx => ⟨mapDomain_psiSectionAt_eq_top L 𝒜 hx, isIso_mapHom_psiSectionAt L 𝒜 hx,
      fun n => isIso_twistMap_psiSectionAt L 𝒜 hx n⟩,
    fun _ u x => psiSectionAt_eq_degreeScale_comp L 𝒜 u x,
    fun ℓ h1 =>
      ⟨(relativeComparison_of_trivialized L 𝒜 ℓ h1).1,
        (relativeComparison_of_trivialized L 𝒜 ℓ h1).2.1,
        (relativeComparison_of_trivialized L 𝒜 ℓ h1).2.2.1,
        (relativeComparison_of_trivialized L 𝒜 ℓ h1).2.2.2,
        ⟨relativeThetaGradedIsoOfTrivialized L 𝒜 ℓ h1⟩⟩,
    existsUnique_relativeTwistIsoOver L 𝒜⟩

end Stacks.ProjInvertibleTwistRelativeStatement

end
