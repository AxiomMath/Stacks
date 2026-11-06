module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartAssembly
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift

/-!
# The conormal generator of an immersion is determined locally, and the `k/s` normalization

A computation of a section of the conormal sheaf `𝒞_i` of an immersion `i : Z ⟶ Y` is produced
in one of two spellings. The *self* spelling names it through
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, by the pullback along `i` of a section of
the ideal sheaf `ℐ_i` over an open `V'` of `Y`; this is the spelling the source half of
[Stacks, Tag 0B3V] clause 3 produces
(`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt`), and it is
forced to shrink `V'` to a chart of `𝐏(ℰ)`, because the section of `𝒪(-1)` that pins the
base-change comparison exists on no larger open. The *factorization* spelling names it through
`Stacks.Conormal.conormalQuotientMap`, by a section of the ideal sheaf of a chosen closed
factorization `i = i' ≫ ι_O` over an open of `O`; this is the spelling
[Stacks, Tag 01R3] states its generators in, and a consumer may present the factorization however
it likes.

**This file identifies the two spellings whenever one ambient section of `𝒪_Y` names both ideal
sections, and then makes the identification local on `Z`.** Neither open is constrained beyond
the inclusions that make the sections restrict: no affineness, no trivialisation, no relation
between the factorization's open and the open the self spelling uses.

**That locality is then spent**: the last section of this file closes the
`"local k/s normalization of the conormal isomorphism"` clause of [Stacks, Tag 0B3V], computing
the value of the canonical conormal map of a section of a projective bundle on `k ⊗ s̄^{⊗ -1}` as
the ideal class of the ratio `k/s`, at the clause's own generality — arbitrary base open where
`s` generates, arbitrary closed factorization, arbitrary open of `𝐏(ℰ)` carrying the ratio.

## Main results

* `Stacks.AlgebraicGeometry.ModuleSections.section_eq_of_forall_exists_restrict_eq`: **sections of
  a sheaf of modules on a scheme are determined locally.** Two sections over `U` that agree on
  some neighbourhood of each point of `U` are equal.
* `Stacks.Conormal.conormalSheafIsoPullbackSelf_inv_pullbackSection_eq_conormalQuotientMap`:
  **the two spellings of a conormal generator agree.** If `f : Γ(Y, V)` names a section `x` of
  the ideal sheaf of the factorization `i = i' ≫ ι_O` over `W ≤ ι_O⁻¹V`, and also names a section
  `y` of `ℐ_i` over an open `V' ≤ V`, then the self-spelling generator at `y` and the
  factorization generator at `x` agree on every open of `Z` lying over both.
* `Stacks.Conormal.val_app_eq_conormalQuotientMap_of_forall_exists_local`: **the local form.** A
  value of an arbitrary morphism into `𝒞_i` is the factorization generator at `x` as soon as it is
  the self-spelling generator locally, with the upstairs open and the ideal section allowed to
  vary from point to point.
* `Stacks.ProjectiveBundleConormal`
  `.conormalCanonicalMap_val_app_tensorSectionsAt_eq_conormalQuotientMap`: **the
  `"local k/s normalization of the conormal isomorphism"` clause of [Stacks, Tag 0B3V]**, and the
  one declaration in the development carrying that label. On any base open where `s` generates
  the quotient line, the canonical conormal map carries `k ⊗ s̄^{⊗ -1}` to the ideal class of the
  homogeneous ratio `k/s`, computed in an arbitrary closed factorization and on an arbitrary open
  of `𝐏(ℰ)` carrying the ratio. No open is affine and no trivialisation is chosen.

## Implementation notes

The ambient open of `Stacks.Immersion.conormalQuotientMap_apply_eq_canonical_of_appLE` is shared
by the ideal section of the factorization and the ideal section of `i`, so the comparison above
cannot be applied at `V` directly: `y` lives over the smaller `V'`. The factorization's open is
therefore cut down to `W ⊓ ι_O⁻¹V'` first, and
`Stacks.Conormal.Locality.conormalQuotientMap_restrict` moves the generator back up to `W`
afterwards. The ideal `I` that lemma carries is instantiated at `⊤`, since it uses only the
underlying ambient section.

The ambient section of the cut-down factorization open is computed by
`AlgebraicGeometry.Scheme.Hom.map_appLE` and `appLE_map` — shrinking the target open and the
source open of an `appLE` in turn. This is inlined rather than named: the target-open half alone
is `Stacks.AlgebraicGeometry.PushforwardRegularity.appLE_res`.

Locality is `TopCat.Presheaf.IsSheaf.section_ext` at `M.isSheaf`, whose hypothesis is already in
the pointwise-shrinking form a local argument produces, so no indexed cover is constructed — the
same discipline as
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_forall_exists_isIso_restrict` for morphisms.

Nothing here is rewritten on a section of a `Scheme.Modules`: every step is `Eq.trans` of a
naturality or a `PresheafOfModules.map_comp_apply`, and the two `rw`s occur on pure `appLE` and
`Opens` goals.

## How the clause is closed

**No `@[stacks 0B3V]` attribute is attached in this file.** The local formula
`Stacks.ProjectiveBundleConormal`
`.conormalCanonicalMap_val_app_tensorSectionsAt_eq_conormalQuotientMap`
describes the tag's isomorphism on local sections; it is not a clause of the tag. The tag is
registered once, on `Stacks.RelativeProj.projectiveBundle_sections_classification` in
`StacksFrontier/AlgebraicGeometry/ProjectiveBundleConormal/SectionsClause.lean`, stated on
`Stacks.RelativeProj.projectiveBundle`.

Beyond the chart formula
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio`
the clause needs exactly two statements, both proved at the end of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTwistProduct`.

1. **The chart formula does not have to be restated at a smaller upstairs open.** The formula
   pins the upstairs open to
   `Stacks.ProjectiveBundleConormal.tautologicalChart E W s`, the clause's ratio lives on an
   unrelated `V`, and the two meet only on `V ⊓ tautologicalChart E W s`. But the local form
   above lets the upstairs open and the ideal section vary pointwise, so only the formula's
   *output* has to move down to the intersection, which is one application of
   `Stacks.Conormal.pullbackSection_restrict_source` together with naturality of the ideal-sheaf
   inclusion. Restating the formula — and with it the compatibility with restriction of
   `Stacks.SheafOfModules.Invertible.sectionMulNegOne` — is **not** needed. What *is* needed is the compatibility with restriction of
   `Stacks.ProjectiveBundleConormal.tautologicalSectionOver`, for a different reason: the clause's
   ratio hypothesis is about the given `s` over the given `U`, and the chart lives over a smaller
   affine open, so the hypothesis has to be reindexed there. That is
   `Stacks.ProjectiveBundleConormal.tautologicalSectionOver_res`, consumed by
   `res_eq_res_of_tautologicalSectionOver_eq_smul`, which identifies the given ratio with the
   chart's on the intersection.
2. **The frame of the clause's own section.** The clause assumes only that `s` generates the
   quotient line, in the form that the image `q s` pairs to `1` against a section of
   `𝓛^{⊗ -1}`; the chart formula assumes an affine open carrying a frame
   `eL : Γ(𝓛, W) ≃ₗ Γ(𝒪_X, W)` with `Stacks.ProjectiveBundleConormal.chartLinearForm` of `s`
   equal to `1`. Going from the first to the second means shrinking to an affine open on which
   `𝓛` is trivial — `Stacks.Modules.exists_affineOpen_restrict_iso_unit_of_isInvertible`, as
   `Stacks.ProjectiveBundleConormal.exists_affine_open_splitting` does — and then showing that
   the coordinate of `q s` in the frame found there is a *unit*, which the pairing gives by
   exhibiting the retraction of `a ↦ a • q s`. The cover
   `Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` does **not** serve: it returns
   a section of its own choosing, and the clause's ratio hypothesis is about the given `s`. This
   is `Stacks.ProjectiveBundleConormal.exists_isAffineOpen_chartLinearForm_eq_one`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.ModuleSections

/-- **Sections of a sheaf of modules on a scheme are determined locally.** If every point of `U`
has an open neighbourhood inside `U` on which two sections of `M` agree, the two sections agree
on `U`.

This is `TopCat.Presheaf.IsSheaf.section_ext` at the sheaf condition of `M`, whose hypothesis is
already in the pointwise-shrinking form a local argument produces: no indexed open cover has to
be built. It is the section-level companion of
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_forall_exists_isIso_restrict`. -/
theorem section_eq_of_forall_exists_restrict_eq {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (a b : M.val.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      M.val.map (homOfLE hV).op a = M.val.map (homOfLE hV).op b) :
    a = b :=
  TopCat.Presheaf.IsSheaf.section_ext M.isSheaf (U := op U) h

end Stacks.AlgebraicGeometry.ModuleSections

namespace Stacks.Conormal

open Stacks.ClosedImmersion Stacks.Immersion

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsImmersion i]

/-- Restricting a section of a sheaf of modules along `A ≤ B` after `B ≤ C` is restricting along
`A ≤ C`. -/
private theorem map_map_homOfLE {Z : Scheme.{u}} (M : Z.Modules) {A B C : Z.Opens}
    (hAB : A ≤ B) (hBC : B ≤ C) (hAC : A ≤ C) (m : M.val.obj (op C)) :
    M.val.map (homOfLE hAB).op (M.val.map (homOfLE hBC).op m) = M.val.map (homOfLE hAC).op m :=
  (M.val.map_comp_apply (homOfLE hBC).op (homOfLE hAB).op m).symm.trans
    (M.val.congr_map_apply (Subsingleton.elim _ _) m)

/-- **The two spellings of a conormal generator agree.**

The ambient section `f : Γ(Y, V)` names a section `x` of the ideal sheaf of the closed
factorization `i = i' ≫ ι_O` over an open `W ≤ ι_O⁻¹V`, and also names a section `y` of the ideal
sheaf of `i` itself over an open `V' ≤ V`. Then the conormal generator
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` names by the pullback of `y`, and the
conormal generator `Stacks.Conormal.conormalQuotientMap` of the factorization computes from `x`,
agree on every open `T` of `Z` lying over both.

Nothing is assumed affine, and the two opens `W` and `V'` are unrelated.

`Stacks.Conormal.conormalSheafIsoPullbackSelf_inv_pullbackSection` reads the first generator as
`Stacks.Immersion.canonicalConormalQuotientMap`, which mentions no factorization, and
`Stacks.Immersion.conormalQuotientMap_apply_eq_canonical_of_appLE` reads the second as the same
thing — but at an ambient open shared with the ideal section of `i`, so the factorization's open
is cut down to `W ⊓ ι_O⁻¹V'` first and
`Stacks.Conormal.Locality.conormalQuotientMap_restrict` moves the result back up to `W`. -/
theorem conormalSheafIsoPullbackSelf_inv_pullbackSection_eq_conormalQuotientMap
    (V : Y.Opens) (f : Γ(Y, V))
    (O : Y.Opens) (i' : Z ⟶ O.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ O.ι = i)
    (W : O.toScheme.Opens) (hW : W ≤ O.ι ⁻¹ᵁ V)
    (x : (idealSheaf i'.toLRSHom.toShHom).val.obj (op W))
    (hx : (idealSheafι i'.toLRSHom.toShHom).val.app (op W) x = (O.ι.appLE V W hW).hom f)
    (V' : Y.Opens) (hV' : V' ≤ V)
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op V'))
    (hy : (idealSheafι i.toLRSHom.toShHom).val.app (op V') y =
      (Y.presheaf.map (homOfLE hV').op).hom f)
    (T : Z.Opens) (hTW : T ≤ i' ⁻¹ᵁ W) (hTV' : T ≤ i ⁻¹ᵁ V') :
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv.val.app (op T)
        (Scheme.Modules.pullbackSection i (idealSheaf i.toLRSHom.toShHom) V' T hTV' y) =
      (Stacks.Conormal.conormalSheaf i).val.map (homOfLE hTW).op
        ((Stacks.Conormal.conormalQuotientMap i O i' hfac).val.app (op W) x) := by
  set W' : O.toScheme.Opens := W ⊓ O.ι ⁻¹ᵁ V' with hW'def
  have hW'W : W' ≤ W := inf_le_left
  have hW'V' : W' ≤ O.ι ⁻¹ᵁ V' := inf_le_right
  set x' := (idealSheaf i'.toLRSHom.toShHom).val.map (homOfLE hW'W).op x with hx'def
  -- shrinking the target open and then the source open of an `appLE`
  have happ : (O.ι.appLE V' W' hW'V').hom ((Y.presheaf.map (homOfLE hV').op).hom f) =
      (O.toScheme.presheaf.map (homOfLE hW'W).op).hom ((O.ι.appLE V W hW).hom f) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_map]
  -- the restricted ideal section is named by the restricted ambient section
  have hx' : (O.ι.appLE V' W' hW'V').hom
        ((Y.presheaf.map (homOfLE hV').op).hom f) =
      (idealSheafι i'.toLRSHom.toShHom).val.app (op W') x' := by
    refine Eq.trans ?_ (PresheafOfModules.naturality_apply
      (idealSheafι i'.toLRSHom.toShHom).val (homOfLE hW'W).op x).symm
    refine Eq.trans happ ?_
    exact congrArg
      (fun z : Γ(O.toScheme, W) => (O.toScheme.presheaf.map (homOfLE hW'W).op).hom z) hx.symm
  have hTW' : T ≤ i' ⁻¹ᵁ W' := by
    have h2 : T ≤ i' ⁻¹ᵁ (O.ι ⁻¹ᵁ V') := by
      rw [← Scheme.Hom.comp_preimage, hfac]
      exact hTV'
    exact fun z hz => ⟨hTW hz, h2 hz⟩
  -- the self spelling is the canonical generator
  have hcan := Stacks.Conormal.conormalSheafIsoPullbackSelf_inv_pullbackSection i V' T hTV'
    (homOfLE hTV') y
  -- the factorization generator is the canonical generator, at the ambient open `V'`
  have hfacgen := Stacks.Immersion.conormalQuotientMap_apply_eq_canonical_of_appLE i V' ⊤
    ⟨(Y.presheaf.map (homOfLE hV').op).hom f, trivial⟩ O i' hfac W' hW'V' x' y hy hx' T hTW' hTV'
  have hres := Stacks.Conormal.Locality.conormalQuotientMap_restrict i O i' hfac hW'W x
  refine hcan.trans (Eq.trans hfacgen.symm ?_)
  refine Eq.trans (congrArg
    (fun z => (Stacks.Conormal.conormalSheaf i).val.map (homOfLE hTW').op z) hres.symm) ?_
  exact map_map_homOfLE _ _ _ _ _

/-- **A value of a morphism into the conormal sheaf is the conormal generator of an arbitrary
open factorization as soon as it is so locally in the self spelling.**

Let `φ : S ⟶ 𝒞_i` be any morphism of modules on `Z`, let the ambient section `f : Γ(Y, V)` name a
section `x` of the ideal sheaf of a closed factorization `i = i' ≫ ι_O` over `W ≤ ι_O⁻¹V`, and let
`a` be a section of `S` over an open `U ≤ (i')⁻¹W`. Suppose that around every point of `U` there
is an open `U'` on which the value of `φ` is the section of `𝒞_i` that
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf` names by a section of `ℐ_i` over *some* open
`V' ≤ V` whose image in `𝒪_Y` is the restriction of `f`. Then the value of `φ` at `a` is the
conormal generator of the given factorization at `x`, restricted to `U`.

The upstairs open `V'` and the ideal section `y` vary from point to point, and `V'` is
unconstrained apart from `V' ≤ V`. That is what a chart computation needs: the source half of
[Stacks, Tag 0B3V] clause 3 produces its value only on
`Stacks.ProjectiveBundleConormal.tautologicalChart`, while the clause's ambient ratio lives on an
unrelated open of `𝐏(ℰ)`.

`Stacks.AlgebraicGeometry.ModuleSections.section_eq_of_forall_exists_restrict_eq` is the locality,
and `conormalSheafIsoPullbackSelf_inv_pullbackSection_eq_conormalQuotientMap` the identification
of the two spellings at each point. -/
theorem val_app_eq_conormalQuotientMap_of_forall_exists_local
    {S : Z.Modules} (φ : S ⟶ Stacks.Conormal.conormalSheaf i)
    (V : Y.Opens) (f : Γ(Y, V))
    (O : Y.Opens) (i' : Z ⟶ O.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ O.ι = i)
    (W : O.toScheme.Opens) (hW : W ≤ O.ι ⁻¹ᵁ V)
    (x : (idealSheaf i'.toLRSHom.toShHom).val.obj (op W))
    (hx : (idealSheafι i'.toLRSHom.toShHom).val.app (op W) x = (O.ι.appLE V W hW).hom f)
    (U : Z.Opens) (hU : U ≤ i' ⁻¹ᵁ W) (a : S.val.obj (op U))
    (hloc : ∀ z ∈ U, ∃ (U' : Z.Opens) (hU' : U' ≤ U), z ∈ U' ∧
      ∃ (V' : Y.Opens) (hV' : V' ≤ V) (hU'V' : U' ≤ i ⁻¹ᵁ V')
        (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op V')),
        (idealSheafι i.toLRSHom.toShHom).val.app (op V') y =
            (Y.presheaf.map (homOfLE hV').op).hom f ∧
          φ.val.app (op U') (S.val.map (homOfLE hU').op a) =
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv.val.app (op U')
              (Scheme.Modules.pullbackSection i (idealSheaf i.toLRSHom.toShHom) V' U'
                hU'V' y)) :
    φ.val.app (op U) a =
      (Stacks.Conormal.conormalSheaf i).val.map (homOfLE hU).op
        ((Stacks.Conormal.conormalQuotientMap i O i' hfac).val.app (op W) x) := by
  refine Stacks.AlgebraicGeometry.ModuleSections.section_eq_of_forall_exists_restrict_eq
    (Stacks.Conormal.conormalSheaf i) U _ _ fun z hz => ?_
  obtain ⟨U', hU', hzU', V', hV', hU'V', y, hy, heq⟩ := hloc z hz
  refine ⟨U', hU', hzU', ?_⟩
  refine Eq.trans (PresheafOfModules.naturality_apply φ.val (homOfLE hU').op a).symm ?_
  refine Eq.trans heq ?_
  refine Eq.trans (conormalSheafIsoPullbackSelf_inv_pullbackSection_eq_conormalQuotientMap
    i V f O i' hfac W hW x hx V' hV' y hy U' (hU'.trans hU) hU'V') ?_
  exact (map_map_homOfLE _ hU' hU _ _).symm

end Stacks.Conormal

namespace Stacks.ProjectiveBundleConormal

open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

include hσ e hqe in
/-- **The local `k/s` normalization of the conormal isomorphism of [Stacks, Tag 0B3V].**

On any base open `U` where `s : Γ(ℰ, U)` generates the quotient line — in the form that its image
`q s` pairs to the unit section against a section `t` of `𝓛^{⊗ -1}` over `U` — the canonical
conormal map `ker(q) ⊗ 𝓛^{⊗ -1} ⟶ 𝒞_σ` carries `k ⊗ t` to the ideal class of the homogeneous
ratio `k/s`.

The ratio is the hypothesis `hratio`: a function `f` on an open `V` of `𝐏(ℰ)` lying over `U` with
`v(ι k) = f · v(s)`, the equation `f · s = k` in the tautological line. The ideal class is the
hypothesis `hx`: a section `x` of the ideal sheaf of a *closed factorization* `σ = i' ≫ ι_O` whose
image in `𝒪_O` is `f`, carried into the conormal sheaf by
`Stacks.Conormal.conormalQuotientMap` and restricted to `U`.

**Nothing is constrained beyond what makes the data restrict.** The factorization `(O, i')` is
arbitrary; `V` is an arbitrary open over `U`; no open is assumed affine and no trivialisation of
`𝓛` is chosen. The section `s` is given, and the frame the chart computation needs is produced
from the pairing by
`Stacks.ProjectiveBundleConormal.exists_isAffineOpen_chartLinearForm_eq_one`.

**The route is forced to be local on `X`.** The chart formula
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio`
produces the value only over `Stacks.ProjectiveBundleConormal.tautologicalChart`, because the
section of `𝒪(-1)` pinning the base-change comparison exists on no open containing `π⁻¹U` once
`ℰ` has rank at least two. So the value is computed around each point of `U`, on an affine open
carrying a frame, with the upstairs open `V ⊓ tautologicalChart E W (s|_W)` varying from point to
point, and `Stacks.Conormal.val_app_eq_conormalQuotientMap_of_forall_exists_local` glues. The two
ratios met there — the given `f` and the one the chart produces — are identified by
`Stacks.ProjectiveBundleConormal.res_eq_res_of_tautologicalSectionOver_eq_smul`, and the chart's
section of `ℐ(σ)` is moved down to the intersection by
`Stacks.Conormal.pullbackSection_restrict_source`.

The hypothesis `ht` is the pairing of `q s` with `t` read against
`Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'`, which is the development's normal form
for the evaluation `𝓛 ⊗ 𝓛^{⊗ -1} ≅ 𝒪_X` of [Stacks, Tag 01CU] at the exponents `(1, -1)` and the
spelling every pairing hypothesis on this layer is stated in. The data `(e, hqe)` presenting `σ`
as the section classified by `q` is the one the clause-(b) registration
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap` uses. -/
theorem conormalCanonicalMap_val_app_tensorSectionsAt_eq_conormalQuotientMap
    (U : X.Opens) (s : Γ(E, U)) (k : Γ(kernel Q.q, U))
    (t : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1), U))
    (ht : Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) Q.L) U (Q.q.app U s) t =
      Stacks.SheafOfModules.unitSection X.toRingedSpace U)
    (V : (bundle E).scheme.Opens) (hV : V ≤ (bundle E).toBase ⁻¹ᵁ U)
    (f : Γ((bundle E).scheme, V))
    (hratio : (tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
          (tautologicalSectionOver E U ((kernel.ι Q.q).val.app (op U) k)) =
        ((tautologicalTwist E (symPieces E)).smul f).asHom.hom
          ((tautologicalTwist E (symPieces E)).presheaf.map (homOfLE hV).op
            (tautologicalSectionOver E U s)))
    (O : (bundle E).scheme.Opens) (i' : X ⟶ O.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ O.ι = σ)
    (W : O.toScheme.Opens) (hW : W ≤ O.ι ⁻¹ᵁ V) (hU : U ≤ i' ⁻¹ᵁ W)
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (op W))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom i'.toLRSHom.toShHom))).val.app (op W) x =
      (O.ι.appLE V W hW).hom f) :
    (conormalCanonicalMap E Q hσ e hqe).val.app (op U)
        (Stacks.SheafOfModules.tensorSectionsAt X.presheaf X.ringCatSheaf.2 (op U)
          (kernel Q.q)
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
          k t) =
      (Stacks.Conormal.conormalSheaf σ).val.map (homOfLE hU).op
        ((Stacks.Conormal.conormalQuotientMap σ O i' hfac).val.app (op W) x) := by
  have hUV : U ≤ σ ⁻¹ᵁ V := by
    refine hU.trans ?_
    refine (i'.preimage_mono hW).trans ?_
    exact le_of_eq (by rw [← Scheme.Hom.comp_preimage, hfac])
  refine Stacks.Conormal.val_app_eq_conormalQuotientMap_of_forall_exists_local σ
    (conormalCanonicalMap E Q hσ e hqe) V f O i' hfac W hW x hx U hU _ ?_
  intro z hz
  obtain ⟨W₀, hW₀U, hzW₀, hW₀aff, eL, hs1⟩ :=
    exists_isAffineOpen_chartLinearForm_eq_one Q U s _
      (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso' (X := X.toRingedSpace) Q.L) t ht
      z hz
  -- the pairing hypothesis, restricted to the affine open the frame lives on
  have hnat : Q.q.app W₀ (E.val.map (homOfLE hW₀U).op s) =
      Q.L.val.map (homOfLE hW₀U).op (Q.q.app U s) :=
    NatTrans.naturality_apply Q.q.mapPresheaf (homOfLE hW₀U).op s
  have hpair : Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) Q.L) W₀
        (Q.q.app W₀ (E.val.map (homOfLE hW₀U).op s))
        ((Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
          Q.L (-1)).val.map (homOfLE hW₀U).op t) =
      Stacks.SheafOfModules.unitSection X.toRingedSpace W₀ := by
    refine Eq.trans (congrArg (fun y : Γ(Q.L, W₀) =>
      Stacks.SheafOfModules.tensorPairing
        (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
          (X := X.toRingedSpace) Q.L) W₀ y
        ((Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
          Q.L (-1)).val.map (homOfLE hW₀U).op t)) hnat) ?_
    refine Eq.trans (Stacks.SheafOfModules.tensorPairing_res
      (Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'
        (X := X.toRingedSpace) Q.L) (homOfLE hW₀U) (Q.q.app U s) t).symm ?_
    refine Eq.trans (congrArg
      (fun y : Γ(X, U) =>
        (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val.map
          (homOfLE hW₀U).op y) ht) ?_
    exact map_one ((structureSheafRing X.toRingedSpace).obj.map (homOfLE hW₀U).op).hom
  -- the ratio the chart produces, and the kernel section read over the smaller open
  have hκ : (kernel.ι Q.q).val.app (op W₀)
        ((kernel Q.q).val.map (homOfLE hW₀U).op k) =
      E.val.map (homOfLE hW₀U).op ((kernel.ι Q.q).val.app (op U) k) :=
    PresheafOfModules.naturality_apply (kernel.ι Q.q).val (homOfLE hW₀U).op k
  obtain ⟨g, hg⟩ := exists_tautologicalSectionOver_res_eq_smul E W₀
    (E.val.map (homOfLE hW₀U).op s)
    (E.val.map (homOfLE hW₀U).op ((kernel.ι Q.q).val.app (op U) k))
  obtain ⟨y, hy, hmap⟩ := exists_conormalCanonicalMap_val_app_tensorSectionsAt_ratio E Q hσ e hqe
    hW₀aff eL (E.val.map (homOfLE hW₀U).op s) hs1
    ((kernel Q.q).val.map (homOfLE hW₀U).op k)
    ((Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
      Q.L (-1)).val.map (homOfLE hW₀U).op t) hpair g
    (Eq.trans (congrArg
      (fun w : Γ(E, W₀) =>
        (tautologicalTwist E (symPieces E)).presheaf.map
          (homOfLE (tautologicalChart_le E W₀ (E.val.map (homOfLE hW₀U).op s))).op
          (tautologicalSectionOver E W₀ w)) hκ) hg)
  -- the given ratio and the chart's agree where they meet
  have hfg := res_eq_res_of_tautologicalSectionOver_eq_smul E U s
    ((kernel.ι Q.q).val.app (op U) k) W₀ hW₀U V hV f hratio g hg
  have hPC : V ⊓ tautologicalChart E W₀ (E.val.map (homOfLE hW₀U).op s) ≤
      tautologicalChart E W₀ (E.val.map (homOfLE hW₀U).op s) := inf_le_right
  refine ⟨W₀, hW₀U, hzW₀, V ⊓ tautologicalChart E W₀ (E.val.map (homOfLE hW₀U).op s),
    inf_le_left, fun a ha => ⟨hUV (hW₀U ha),
      le_preimage_tautologicalChart E Q hσ e hqe W₀ (E.val.map (homOfLE hW₀U).op s)
        hW₀aff eL hs1 ha⟩,
    (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.map (homOfLE hPC).op y, ?_, ?_⟩
  · refine Eq.trans (PresheafOfModules.naturality_apply
      (Stacks.ClosedImmersion.idealSheafι σ.toLRSHom.toShHom).val (homOfLE hPC).op y) ?_
    refine Eq.trans (congrArg
      (fun w : Γ((bundle E).scheme,
          tautologicalChart E W₀ (E.val.map (homOfLE hW₀U).op s)) =>
        (bundle E).scheme.presheaf.map (homOfLE hPC).op w) hy) ?_
    exact hfg.symm
  · refine Eq.trans (congrArg
      (fun w => (conormalCanonicalMap E Q hσ e hqe).val.app (op W₀) w)
      (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality
        X.presheaf X.ringCatSheaf.2 (kernel Q.q)
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1))
        (homOfLE hW₀U).op k t)) ?_
    refine Eq.trans hmap ?_
    exact congrArg
      (fun w : Γ((Scheme.Modules.pullback σ).obj
          (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom), W₀) =>
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv.val.app (op W₀) w)
      (Stacks.Conormal.pullbackSection_restrict_source σ
        (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom)
        (tautologicalChart E W₀ (E.val.map (homOfLE hW₀U).op s))
        (V ⊓ tautologicalChart E W₀ (E.val.map (homOfLE hW₀U).op s)) hPC W₀ _ y)

end Stacks.ProjectiveBundleConormal

end
