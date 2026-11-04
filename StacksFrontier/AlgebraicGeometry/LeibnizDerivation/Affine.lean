module

public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Universal
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective

/-!
# The affine comparison for `Ω_{X/S} ⟶ C_Δ`, and the locality of its invertibility

`StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Universal` constructed the canonical
morphism `Stacks.LeibnizDerivation.toConormal f : Ω_{X/S} ⟶ C_Δ` of
[Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2) and proved the tag's generator
formula for it. What the tag still asserts is that this morphism is an *isomorphism*. This
file reduces that assertion to a single explicitly named statement about one explicitly given
map on one affine open, and proves everything else.

**The reduction.** For an affine open `V` of `S` and an affine open `U ≤ f ⁻¹ᵁ V` of `X`, the
conormal class `Stacks.LeibnizDerivation.cls f U` is a derivation of `Γ(X, U)` relative to
`f.appLE V U hUV : Γ(S, V) ⟶ Γ(X, U)` — that is exactly the content of `cls_add`, `cls_mul`
and `cls_appLE_eq_zero`, with no sheafy data needed. So the universal property of the Kähler
differentials of a morphism of `CommRingCat` gives a map

  `kaehlerToConormal f V U hUV : Ω[Γ(X, U)⁄Γ(S, V)] ⟶ Γ(C_Δ, U)`,

normalized by `kaehlerToConormal_d : d b ↦ cls f U b`. Three things are then proved about it,
none of them needing `U` or `V` affine:

* it is the *unique* candidate for the affine comparison of [Stacks, Tag 08S2] — the
  isomorphism `Γ(C_Δ, U) ≅ Ω[Γ(X, U)⁄Γ(S, V)]` carrying `cls f U b` to `d b` is unique if it
  exists (`affineConormalIsoKaehler_unique`), and exists exactly when `kaehlerToConormal` is
  invertible (`existsUnique_affineConormalIsoKaehler_iff_isIso`);
* it factors the canonical morphism:
  `kaehlerToSections ≫ (toConormal f).val.app (.op U) = kaehlerToConormal`
  (`kaehlerToSections_comp_toConormal_app`), the left factor being the comparison map of
  [Stacks, Tag 01UT];
* hence, `U` and `V` being affine, `(toConormal f).val.app (.op U)` is invertible if and only
  if `kaehlerToConormal f V U hUV` is (`isIso_toConormal_app_iff`), because the left factor is
  invertible by tag 01UT.

**The locality.** The affine opens `U` admitting an affine `V` with `U ≤ f ⁻¹ᵁ V` form a basis
of `X` (`isBasis_affineOpens_le_preimage`), and a morphism of sheaves of modules on a scheme
whose component is invertible on every member of a basis is invertible
(`isIso_of_isIso_app_basis`). So invertibility of `toConormal f` follows from the affine
comparison alone: `isIso_toConormal_of_forall_affineConormalIsoKaehler`.

Granting invertibility, both clauses of [Stacks, Tag 08S2] are then in hand:
`diagonalConormalIso` is the comparison isomorphism and
`diagonalConormalIso_hom_d_eq_quotientMap` is the tag's quotient formula for its hom,
discharged by `toConormal_d_eq_quotientMap` with no further argument.

## Main definitions

* `Stacks.LeibnizDerivation.conormalDerivation`: `cls f U` read as a ring-theoretic derivation
  of `Γ(X, U)` relative to `f.appLE V U hUV`.
* `Stacks.LeibnizDerivation.kaehlerToConormal`: the canonical map
  `Ω[Γ(X, U)⁄Γ(S, V)] ⟶ Γ(C_Δ, U)`.
* `Stacks.LeibnizDerivation.diagonalConormalIso`: the comparison isomorphism
  `Ω_{X/S} ≅ C_Δ`, under the hypothesis that `toConormal f` is invertible.

## Main results

* `Stacks.LeibnizDerivation.kaehlerToConormal_d`: the generator formula for the affine
  comparison map.
* `Stacks.LeibnizDerivation.kaehlerToSections_comp_toConormal_app`: the factorization of
  `toConormal` on an open through the comparison map of [Stacks, Tag 01UT].
* `Stacks.LeibnizDerivation.existsUnique_affineConormalIsoKaehler_iff_isIso`: the affine
  comparison isomorphism of [Stacks, Tag 08S2] exists, and is then unique, precisely when
  `kaehlerToConormal` is invertible.
* `Stacks.LeibnizDerivation.isIso_toConormal_app_iff`: for `U` and `V` affine, the component
  of `toConormal f` on `U` is invertible iff `kaehlerToConormal f V U hUV` is.
* `Stacks.LeibnizDerivation.isIso_of_isIso_app_basis`: a morphism of sheaves of modules on a
  scheme invertible on a basis of opens is invertible.
* `Stacks.LeibnizDerivation.isIso_toConormal_of_forall_affineConormalIsoKaehler` and
  `Stacks.LeibnizDerivation.isIso_toConormal_of_forall_isIso_kaehlerToConormal`: **the
  reduction of [Stacks, Tag 08S2] to the affine comparison.**

## Route

The derivation is `ModuleCat.Derivation.mk` applied to `cls_add`, `cls_mul` and
`cls_appLE_eq_zero`, and the comparison map is `ModuleCat.Derivation.desc`; this is the same
route `Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections` takes for the sheaf of
relative differentials, and the two uniqueness arguments are the same argument — `d b`
generates the Kähler differentials, so a map *out of* them is determined on generators, and an
isomorphism *into* them satisfying the generator formula is determined through its inverse
(`CommRingCat.KaehlerDifferential.ext`).

`Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections` (tag 01UT) supplies
the invertible left factor. The locality is `TopCat.Sheaf.isIso_iff_isIso_basis` for the
underlying sheaf of abelian groups, together with `AlgebraicGeometry.Scheme.Modules.toPresheaf`
reflecting isomorphisms — the same two steps as
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`, with the basis criterion in
place of the stalk criterion. The basis itself is `AlgebraicGeometry.Scheme.isBasis_affineOpens`
used twice: once on `S` to find an affine `V` around the image of a point, once on `X` inside
`U ⊓ f ⁻¹ᵁ V`.

`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict` is *not* used: it asks for
invertibility of the restriction of the morphism to each member of a cover, which on an affine
member is strictly more than invertibility of its component there, and the basis criterion
delivers the conclusion from the component data directly.

## What is not done

**`kaehlerToConormal f V U hUV` is not shown to be invertible for `U` and `V` affine.** That
single statement is all that separates this file from [Stacks, Tag 08S2], and no label of the
tag is attached here because of it. It is the affine computation
`Γ(C_Δ, U) ≅ Ω[Γ(X, U)⁄Γ(S, V)]`, and the obstruction is the one
described in the "What is not done" section of
`StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Universal`: the sheaf-level passage
`Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel` is a five-fold composite of
isomorphisms — `conormalSheafRestrictIsoOfLe`, the pullback of
`idealSheafIsoAffineModelOfMorphismRestrict`, `modulePullbackCompIso` twice and
`pullbackObjCongr` — and *not one of the five has an elementwise formula*, so a section cannot
be carried across it; and the comparison of the two scalar actions, over
`Γ((Δ ⁻¹ᵁ W).toScheme, ⊤)` on one side and `Γ(X, W)` on the other, which
`Stacks.Conormal.AffineShape.conormalRestrictTopSectionsIso`'s own docstring records as not
supplied, is exactly what carrying `cls` across it needs.

Two inputs to that computation are available:
`AlgebraicGeometry.isAffineOpen_inf_preimage`
(`StacksFrontier/AlgebraicGeometry/Size/Pullback.lean`) makes
`pullback.fst f f ⁻¹ᵁ U ⊓ pullback.snd f f ⁻¹ᵁ U` an affine open of `X ×_S X` for `U`, `V`
affine — and `Stacks.LeibnizDerivation.chart f U` is the restriction of that open to the
coborder neighbourhood, with `chart_preimage` giving its preimage as `U`; and Mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen` identifies its ring of sections with
the pushout `Γ(X, U) ⊗_{Γ(S, V)} Γ(X, U)`, which is where
`Stacks.DiagonalConormal.ker_lmulHom` and
`Stacks.DiagonalConormal.toCotangent_one_tmul_sub_tmul_one` apply.

## Vocabulary

The conormal sheaf of Stacks Tag 01R2 is `Stacks.Conormal.conormalSheaf` and the quotient map of
Stacks Tag 01R3 is `Stacks.Conormal.conormalQuotientMap`
(`StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison`); the ideal sheaf of
Stacks Tag 01C2 is `Stacks.ClosedImmersion.idealSheaf`; the module of relative differentials and
the universal relative derivation of Stacks Tag 01US are
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and
`AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`.

No `stacks` attribute is attached. Both labels of [Stacks, Tag 08S2] — the bare one on the
comparison isomorphism and `"canonical quotient formula"` on a statement about that
isomorphism's hom — are carried here only under the hypothesis `IsIso (toConormal f)`, which
is not discharged; a labelled assertion may not carry a hypothesis the tag does not have.

## Transparency gotchas

The three gaps recorded in `StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Basic` do not
bite in this file, and the reason is worth recording: every statement here is about a *single*
open, so no restriction map and no pushforward is involved, and the `ModuleCat B` spelling
that `ModuleCat.Derivation` and `CommRingCat.KaehlerDifferential` are stated at is reached by
unification against a *declared* result type at each use — the construction of
`conormalDerivation` is checked against its own stated type, so `cls_mul`'s `toXRing b • _`
and `ModuleCat.Derivation.mk`'s `b • _` are unified at default transparency with nothing to
help them along. In particular no `toXRing`-style abbreviation is needed here.

One real gap remains, in `isIso_of_isIso_app_basis`: a local hypothesis of type `IsIso ψ` for
`ψ` a `let`-bound morphism of `TopCat.Sheaf Ab` is *not* found by instance search at the use
site, so `CategoryTheory.Functor.map_isIso` is applied as an explicit term with the hypothesis
passed by hand rather than as an instance.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.LeibnizDerivation

/-! ### The conormal class on one open, as a ring-theoretic derivation -/

section Affine

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

/-- **The conormal class of [Stacks, Tag 08S2] on a single open, as a derivation of the
sections.** For `U ≤ f ⁻¹ᵁ V`, the map `b ↦ cls f U b` is a derivation of `Γ(X, U)` relative
to the ring map `f.appLE V U hUV : Γ(S, V) ⟶ Γ(X, U)`. The three axioms are `cls_add`,
`cls_mul` and `cls_appLE_eq_zero`; no restriction-compatibility is needed, a single open being
involved. -/
noncomputable def conormalDerivation :
    ((Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U)).Derivation
      (f.appLE V U hUV) :=
  ModuleCat.Derivation.mk (fun b => cls f U b) (cls_add f U) (cls_mul f U)
    (fun a => cls_appLE_eq_zero f V U hUV a)

/-- **The affine comparison map of [Stacks, Tag 08S2].** The canonical map from the Kähler
differentials of `Γ(S, V) ⟶ Γ(X, U)` to the sections on `U` of the conormal sheaf of the
diagonal, given by the universal property of the Kähler differentials applied to
`conormalDerivation`. Neither `U` nor `V` needs to be affine for it to exist; the tag's
assertion is that it is invertible when they are. -/
noncomputable def kaehlerToConormal :
    CommRingCat.KaehlerDifferential (f.appLE V U hUV) ⟶
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) :=
  (conormalDerivation f V U hUV).desc

/-- **The generator formula for the affine comparison map:** it carries the universal
differential of a section to the conormal class of that section. -/
theorem kaehlerToConormal_d (b : Γ(X, U)) :
    (kaehlerToConormal f V U hUV).hom (CommRingCat.KaehlerDifferential.d b) = cls f U b :=
  (conormalDerivation f V U hUV).desc_d b

/-- **The canonical morphism of [Stacks, Tag 08S2] factors the affine comparison map through
the comparison map of [Stacks, Tag 01UT].** Both sides are maps out of the Kähler
differentials, so they agree as soon as they agree on the universal differentials, and there
they are `toConormal_d`. -/
theorem kaehlerToSections_comp_toConormal_app :
    Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections f V U hUV ≫
        (toConormal f).val.app (.op U) =
      kaehlerToConormal f V U hUV := by
  refine CommRingCat.KaehlerDifferential.ext fun b => ?_
  refine Eq.trans (congrArg ((toConormal f).val.app (.op U)).hom
    (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections_d f V U hUV b)) ?_
  exact (toConormal_d f U b).trans (kaehlerToConormal_d f V U hUV b).symm

/-! ### Uniqueness of the affine comparison isomorphism -/

/-- An isomorphism from the conormal sections on `U` to the Kähler differentials of the
sections, carrying the conormal class to the universal differential, has an inverse that
carries universal differentials to conormal classes. -/
theorem inv_hom_apply_d
    (e : (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) ≅
      CommRingCat.KaehlerDifferential (f.appLE V U hUV))
    (he : ∀ b : Γ(X, U), e.hom.hom (cls f U b) = CommRingCat.KaehlerDifferential.d b)
    (b : Γ(X, U)) :
    e.inv.hom (CommRingCat.KaehlerDifferential.d b) = cls f U b :=
  by rw [← he b]; exact e.hom_inv_id_apply _

/-- Such an isomorphism has the affine comparison map as its inverse. -/
theorem kaehlerToConormal_eq_inv
    (e : (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) ≅
      CommRingCat.KaehlerDifferential (f.appLE V U hUV))
    (he : ∀ b : Γ(X, U), e.hom.hom (cls f U b) = CommRingCat.KaehlerDifferential.d b) :
    kaehlerToConormal f V U hUV = e.inv := by
  refine CommRingCat.KaehlerDifferential.ext fun b => ?_
  exact (kaehlerToConormal_d f V U hUV b).trans (inv_hom_apply_d f V U hUV e he b).symm

/-- **The affine comparison isomorphism of [Stacks, Tag 08S2] is unique.** There is at most
one isomorphism from the sections on `U` of the conormal sheaf of the diagonal to the Kähler
differentials of `Γ(S, V) ⟶ Γ(X, U)` carrying the conormal class of a section to its
universal differential. Neither `U` nor `V` needs to be affine for this: the universal
differentials generate, so the inverse is determined, and hence so is the isomorphism. -/
theorem affineConormalIsoKaehler_unique
    (e e' : (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) ≅
      CommRingCat.KaehlerDifferential (f.appLE V U hUV))
    (he : ∀ b : Γ(X, U), e.hom.hom (cls f U b) = CommRingCat.KaehlerDifferential.d b)
    (he' : ∀ b : Γ(X, U), e'.hom.hom (cls f U b) = CommRingCat.KaehlerDifferential.d b) :
    e = e' :=
  Iso.ext ((Iso.inv_eq_inv e e').1
    ((kaehlerToConormal_eq_inv f V U hUV e he).symm.trans
      (kaehlerToConormal_eq_inv f V U hUV e' he')))

/-- **The affine clause of [Stacks, Tag 08S2], reduced to a single map.** The sections on `U`
of the conormal sheaf of the diagonal are uniquely isomorphic to the Kähler differentials of
`Γ(S, V) ⟶ Γ(X, U)`, compatibly with the conormal class and the universal differential,
precisely when the affine comparison map `kaehlerToConormal` is invertible. The uniqueness is
unconditional; it is the existence that is at issue for `U` and `V` affine. -/
theorem existsUnique_affineConormalIsoKaehler_iff_isIso :
    (∃! e : (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) ≅
        CommRingCat.KaehlerDifferential (f.appLE V U hUV),
      ∀ b : Γ(X, U), e.hom.hom (cls f U b) = CommRingCat.KaehlerDifferential.d b) ↔
      IsIso (kaehlerToConormal f V U hUV) := by
  constructor
  · rintro ⟨e, he, -⟩
    rw [kaehlerToConormal_eq_inv f V U hUV e he]
    infer_instance
  · intro h
    have key : ∀ b : Γ(X, U),
        (inv (kaehlerToConormal f V U hUV)).hom (cls f U b) =
          CommRingCat.KaehlerDifferential.d b := fun b => by
      rw [← kaehlerToConormal_d f V U hUV b]
      exact (asIso (kaehlerToConormal f V U hUV)).hom_inv_id_apply _
    exact ⟨(asIso (kaehlerToConormal f V U hUV)).symm, key,
      fun e' he' => affineConormalIsoKaehler_unique f V U hUV e' _ he' key⟩

/-- **On an affine open over an affine open, the canonical morphism of [Stacks, Tag 08S2] is
invertible exactly when the affine comparison map is.** The factorization
`kaehlerToSections_comp_toConormal_app` has invertible left factor by
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections`, which is
[Stacks, Tag 01UT]. -/
theorem isIso_toConormal_app_iff (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsIso ((toConormal f).val.app (.op U)) ↔ IsIso (kaehlerToConormal f V U hUV) := by
  have hk : IsIso (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections f V U hUV) :=
    Stacks.AlgebraicGeometry.AffineDifferentialsIso.isIso_kaehlerToSections f hU hUV hV
  rw [← kaehlerToSections_comp_toConormal_app f V U hUV]
  exact ⟨fun h => @IsIso.comp_isIso _ _ _ _ _ _ _ hk h, fun _ => IsIso.of_isIso_comp_left
    (Stacks.AlgebraicGeometry.AffineDifferentials.kaehlerToSections f V U hUV) _⟩

end Affine

/-! ### Invertibility of a morphism of sheaves of modules is detected on a basis -/

/-- **A morphism of sheaves of modules on a scheme whose component is invertible on every
member of a basis of opens is invertible.** This is `TopCat.Sheaf.isIso_iff_isIso_basis` for
the underlying sheaf of abelian groups, together with
`AlgebraicGeometry.Scheme.Modules.toPresheaf` reflecting isomorphisms — the same two steps as
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk`, with the basis criterion in
place of the stalk criterion. Nothing about the scheme or the modules is used beyond the sheaf
condition; this is general infrastructure stated here for want of a home. -/
theorem isIso_of_isIso_app_basis {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    {ι : Type*} {B : ι → Y.Opens} (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (h : ∀ i, IsIso (φ.val.app (.op (B i)))) : IsIso φ := by
  rw [← isIso_iff_of_reflects_iso _ (Scheme.Modules.toPresheaf Y)]
  let ψ : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab.{u} Y.toTopCat) ⟶
      ⟨N.presheaf, N.isSheaf⟩ := ⟨φ.mapPresheaf⟩
  have hψ : IsIso ψ := by
    refine TopCat.Sheaf.isIso_iff_isIso_basis (B := B) hB fun i => ?_
    refine (ConcreteCategory.isIso_iff_bijective (ψ.hom.app (.op (B i)))).2 ?_
    exact ConcreteCategory.bijective_of_isIso (f := φ.val.app (.op (B i)))
  exact @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget Ab.{u} Y.toTopCat) ψ hψ

section Reduction

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The affine opens of `X` lying over an affine open of `S` form a basis of `X`.** Given a
point of an open `U`, choose an affine open `V` of `S` around its image and then an affine
open of `X` inside `U ⊓ f ⁻¹ᵁ V` around the point; both choices are
`AlgebraicGeometry.Scheme.isBasis_affineOpens`. -/
theorem isBasis_affineOpens_le_preimage :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun p : {p : S.Opens × X.Opens //
          IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.2 ≤ f ⁻¹ᵁ p.1} => p.1.2)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  have htop : f.base x ∈ (⊤ : S.Opens) := trivial
  obtain ⟨V, hV, hfx, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens htop
  have hx' : x ∈ U ⊓ f ⁻¹ᵁ V := ⟨hx, hfx⟩
  obtain ⟨U', hU', hxU', hU'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx'
  exact ⟨U', ⟨⟨⟨V, U'⟩, hV, hU', hU'le.trans inf_le_right⟩, rfl⟩,
    hxU', hU'le.trans inf_le_left⟩

/-- **[Stacks, Tag 08S2] reduced to the affine comparison map.** If the affine comparison map
`kaehlerToConormal` is invertible for every affine open `U` of `X` lying inside the preimage
of an affine open `V` of `S`, then the canonical morphism `Ω_{X/S} ⟶ C_Δ` is an isomorphism.

Those opens form a basis by `isBasis_affineOpens_le_preimage`, on each of them
`isIso_toConormal_app_iff` turns the hypothesis into invertibility of the component of
`toConormal f`, and `isIso_of_isIso_app_basis` globalizes. -/
theorem isIso_toConormal_of_forall_isIso_kaehlerToConormal
    (h : ∀ (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V), IsAffineOpen V → IsAffineOpen U →
      IsIso (kaehlerToConormal f V U hUV)) :
    IsIso (toConormal f) := by
  refine isIso_of_isIso_app_basis (toConormal f) (isBasis_affineOpens_le_preimage f) ?_
  rintro ⟨⟨V, U⟩, hV, hU, hUV⟩
  exact (isIso_toConormal_app_iff f V U hUV hU hV).2 (h V U hUV hV hU)

/-- **[Stacks, Tag 08S2] reduced to the affine comparison isomorphism**, in the shape the tag
states it: if for every affine open `V` of `S` and every affine open `U ≤ f ⁻¹ᵁ V` of `X`
there is an isomorphism from the conormal sections on `U` to the Kähler differentials of
`Γ(S, V) ⟶ Γ(X, U)` carrying the conormal class of a section to its universal differential,
then the canonical morphism `Ω_{X/S} ⟶ C_Δ` is an isomorphism.

This is `isIso_toConormal_of_forall_isIso_kaehlerToConormal` with the hypothesis traded for
its unique-isomorphism form by `existsUnique_affineConormalIsoKaehler_iff_isIso`; the
uniqueness that form carries is free, so the two hypotheses are the same assertion. -/
theorem isIso_toConormal_of_forall_affineConormalIsoKaehler
    (h : ∀ (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V), IsAffineOpen V → IsAffineOpen U →
      ∃ e : (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.obj (.op U) ≅
          CommRingCat.KaehlerDifferential (f.appLE V U hUV),
        ∀ b : Γ(X, U), e.hom.hom (cls f U b) = CommRingCat.KaehlerDifferential.d b) :
    IsIso (toConormal f) := by
  refine isIso_toConormal_of_forall_isIso_kaehlerToConormal f fun V U hUV hV hU => ?_
  obtain ⟨e, he⟩ := h V U hUV hV hU
  rw [kaehlerToConormal_eq_inv f V U hUV e he]
  infer_instance

/-! ### The two clauses of [Stacks, Tag 08S2], granting invertibility -/

variable [IsIso (toConormal f)]

/-- **The comparison isomorphism `Ω_{X/S} ≅ C_Δ` of [Stacks, Tag 08S2]**, granting that the
canonical morphism is invertible. This is the tag's first labelled assertion with the single
hypothesis `IsIso (toConormal f)` added, which is why no label is attached. -/
noncomputable def diagonalConormalIso :
    Scheme.Hom.relativeDifferentials f ≅
      Stacks.Conormal.conormalSheaf (pullback.diagonal f) :=
  asIso (toConormal f)

/-- **The canonical quotient formula of [Stacks, Tag 08S2] for the comparison
isomorphism.** Granting that the canonical morphism is invertible, the hom of
`diagonalConormalIso` sends `d b` to the image of `p₂^♯ b - p₁^♯ b` under the canonical
quotient map from the ideal sheaf of the diagonal to its conormal sheaf, on any open `V` of
the coborder neighbourhood admitting the tag's two containments.

The hom of `diagonalConormalIso` is `toConormal f` definitionally, so this is
`toConormal_d_eq_quotientMap` with nothing added. That is the tag's second labelled
assertion, with the same single hypothesis. -/
theorem diagonalConormalIso_hom_d_eq_quotientMap
    (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V) x =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b) :
    ((diagonalConormalIso f).hom.val.app
          (.op ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) =
      (Stacks.Conormal.conormalQuotientMap (pullback.diagonal f)
        (pullback.diagonal f).coborderRange (pullback.diagonal f).liftCoborder
        (pullback.diagonal f).liftCoborder_ι).val.app (.op V) x :=
  toConormal_d_eq_quotientMap f V h₁ h₂ b x hx

end Reduction

end Stacks.LeibnizDerivation

end
