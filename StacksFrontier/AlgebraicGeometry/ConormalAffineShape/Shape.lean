module

public import StacksFrontier.AlgebraicGeometry.ConormalAffineShape.PullbackIso
public import StacksFrontier.AlgebraicGeometry.ConormalSourceTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Coborder

/-!
# Matching the shapes: the conormal sheaf over an affine open of the ambient scheme

`Stacks.Conormal.Locality.conormalSheafRestrictIso` computes the conormal sheaf of an immersion
`i : Z ⟶ X` restricted to `i' ⁻¹ᵁ V'`, where `(U, i')` is a closed-immersion factorization of `i`
and `V'` is an open of `U.toScheme`. The part (2) assertions of
[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) are about an open `V` of **`X`**, and
the affine model `Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` is about
`Spec (Γ(X, V) ⧸ I) ⟶ Spec Γ(X, V)`. Three shapes, no stated relation between them: that is the
gap this file closes at the level of sheaves.

The pivot is `AlgebraicGeometry.morphismRestrict`. If `i' ≫ U.ι = i` and `V ≤ U` then

`i' ∣_ (U.ι ⁻¹ᵁ V) ≫ (Scheme.Opens.isoOfLE hVU).hom = i ∣_ V`,

so the factorization's restriction and the ambient restriction differ by an *isomorphism of the
target* — which is exactly the slot
`Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget` transports along. With
that, the locality comparison can be restated at an open of `X` and in terms of `i ∣_ V`, which is
the morphism the source-slot junction
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict` is
stated for. Composing the two with the pseudofunctoriality isomorphism twice identifies the
restricted conormal sheaf with the affine model's pulled-back ideal sheaf, from the
hypotheses of Tag 01R3 part (2) verbatim.

## Main results

* `Stacks.Conormal.AffineShape.morphismRestrict_opens_ι`: the restriction of `U.ι` to a smaller
  open `V` is `AlgebraicGeometry.Scheme.Opens.isoOfLE`.
* `Stacks.Conormal.AffineShape.morphismRestrict_comp_isoOfLE`: consequently
  `i' ∣_ (U.ι ⁻¹ᵁ V) ≫ (isoOfLE hVU).hom = (i' ≫ U.ι) ∣_ V`.
* `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe`: **the shape match.** For a
  closed-immersion factorization `(U, i')` of `i` and an open `V ≤ U` of `X`, the restriction of
  `Stacks.Conormal.conormalSheaf i` to `i ⁻¹ᵁ V` is the module pullback along `i ∣_ V` of the
  ideal sheaf of `i ∣_ V`. The factorization has disappeared from the statement.
* `Stacks.Conormal.AffineShape.morphismRestrict_isoSpec_eq`: the presentation square of part (2)
  with
  the fibre product replaced by `i ⁻¹ᵁ V`.
* `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel`: **the junction.** From the
  data `hV, I, e, he` of part (2) and nothing else, the restriction of the conormal sheaf to
  `i ⁻¹ᵁ V` is the module pullback, along the isomorphism `ε` identifying `i ⁻¹ᵁ V` with
  `Spec (Γ(X, V) ⧸ I)`, of the module pullback along `k = Spec (Γ(X,V) ⧸ I) ⟶ Spec Γ(X,V)` of the
  ideal sheaf of `k`.
* `Stacks.Conormal.AffineShape.appLE_eq_ΓSpecIso_inv`: **the ring map of the part (2) generator
  hypothesis, routed through `Spec`.** For `V ≤ U` with `V` affine and `W ≤ U.ι ⁻¹ᵁ V` an open of
  `U.toScheme`, the map `U.ι.appLE V W hW` that the generator formula of part (2) uses to name an
  element of `Γ(X, V)` on `W` is `(AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V)).inv` followed by the
  global-sections map of `(isoOfLE hVU).hom ≫ hV.isoSpec.hom`, a `topIso` and a restriction map.
  `(Scheme.ΓSpecIso Γ(X, V)).inv` is the ring map the affine model's answer is stated through
  (`Stacks.Conormal.CotangentAppIso.moduleSpecΓFunctor_obj_eq`), so this is the form in which the
  hypothesis of the generator formula can meet the affine computation.
* `Stacks.Conormal.AffineShape.unit_comp_map_pullbackObjCongr`: `pullbackObjCongr` commutes with
  the units of the two pullback-pushforward adjunctions.
* `Stacks.Conormal.AffineShape.conormalRestrictTopSectionsIso`: the same at the level of global
  sections, with the pullback along `ε` traded for the pushforward along `ε.inv` by
  `Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv` — the form in which the right-hand side
  is the module the affine model computes.

## Route

For the shape match: `AlgebraicGeometry.morphismRestrict_comp` splits `(i' ≫ U.ι) ∣_ V` as
`i' ∣_ (U.ι ⁻¹ᵁ V) ≫ U.ι ∣_ V`, and `U.ι ∣_ V` is `Scheme.Opens.isoOfLE hVU` because both become
`(U.ι ⁻¹ᵁ V).ι ≫ U.ι` after composing with the monomorphism `V.ι`
(`AlgebraicGeometry.morphismRestrict_ι` and `AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_ι`). The
factorization hypothesis is then discharged by `subst`, which is what makes
`i' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) = i ⁻¹ᵁ V` hold by `rfl`.

For the junction, the containment `V ≤ i.coborderRange` needed to apply the shape match at the
*defining* factorization is `Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient`,
which derives it from the presentation hypothesis of part (2). Then
`idealSheafIsoAffineModelOfMorphismRestrict` replaces the ideal sheaf of `i ∣_ V`, and
`Stacks.PullbackPseudofunctor.modulePullbackCompIso` is applied twice — once to collapse
`(i ∣_ V)^* (isoSpec)^*` into `((i ∣_ V) ≫ isoSpec)^*`, once to expand `(ε ≫ k)^*` — with
`morphismRestrict_isoSpec_eq` between them.

## Vocabulary

Tag 01R2's `conormalSheaf` is `Stacks.Conormal.conormalSheaf`.

Tag 01C2's `idealSheaf` is `Stacks.ClosedImmersion.idealSheaf`.

**No clause of [Stacks, Tag 01R3] is stated here
and no `stacks` attribute is attached.** Every statement is an input to its part (2).

The hypotheses of the junction are copied verbatim from the part (2) clauses of Tag 01R3: `hV`, `I`,
`e` and `he` are the data of the statement with no reshaping. Nothing is Noetherian, finite or
quasi-compact, and the only closed-immersion hypothesis used is the one carried by
`i.liftCoborder`.

## Universe situation

A single universe `u`, as in the statements of Tag 01R3: `Scheme.{u}` and `SheafOfModules.{u}`,
forced by
`RingedSpaceModuleAdjunction`.

## Transparency gotchas

The two spellings `AlgebraicGeometry.Scheme.Modules.pullback f` and
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom` are mixed deliberately, because
the two inputs are stated in different ones: `Stacks.Conormal.Locality.conormalSheafRestrictIso`
in the former, `Transport.idealSheafPullbackIsoOfIsoTarget` in the latter. `Iso.trans` unifies
them here without a `change`; it is the one place in this
chain where the two spellings compose directly.

`pullbackObjCongr` transports along an equality of *morphisms* by `subst` rather than by `rw`,
because the morphism sits inside the type of the functor being applied and `rw` elaborates
congruence motives at implicit transparency.

`V.ι ''ᵁ ⊤ = V` and `V.ι ⁻¹ᵁ V = ⊤` are **not** `rfl`, while `f ⁻¹ᵁ ⊤ = ⊤` and
`i' ⁻¹ᵁ (U.ι ⁻¹ᵁ V) = (i' ≫ U.ι) ⁻¹ᵁ V` are. That asymmetry is why the global-sections statement
below is phrased at `⊤` of `i ⁻¹ᵁ V` rather than at `V` of `X`; see the next section.

## What is not done

* **No clause of [Stacks, Tag 01R3] is discharged and no tag is attached.**
* **The sections statement of part (2) of Tag 01R3 is not reached here**, though it needs
  nothing that does not exist. Part (2) asks for an isomorphism
  `((modulePushforward i).obj (conormalSheaf i)).val.obj (.op V) ≅`
  `ModuleCat.of Γ(X, V) I.Cotangent`, whose two ends are modules over `Γ(X, V)`. Every
  statement here is an isomorphism over `Γ((i ⁻¹ᵁ V).toScheme, ⊤)` instead, and the two
  rings are identified only by `AlgebraicGeometry.Scheme.Opens.topIso`, not definitionally. The
  two restriction-of-scalars comparisons that close that gap are **in the library**, in
  `StacksFrontier.AlgebraicGeometry.CotangentAppIso.Basic`:
  * for `M : X.Modules` and an open `V`, the isomorphism
    `M.val.obj (.op V) ≅ (ModuleCat.restrictScalars V.topIso.inv.hom).obj`
    `(((Scheme.Modules.restrictFunctor V.ι).obj M).val.obj (.op ⊤))`,
    the module-level analogue of `AlgebraicGeometry.Scheme.Opens.topIso`, is
    `Stacks.Conormal.CotangentAppIso.sectionsRestrictTopIso`, with its underlying map given by
    `sectionsRestrictTopIso_hom_apply`. (Its linearity is *not* routed through
    `V.ι.appLE V ⊤ _ = V.topIso.inv`, which is `Stacks.Smooth.opens_ι_appLE_top` — note the
    spelling: `ι`, and no `LiftTorsor` namespace component — and is not needed: the linearity is
    the semilinearity built into `PresheafOfModules.map`.)
  * and the same for a pushforward along `AlgebraicGeometry.IsAffineOpen.isoSpec`, comparing
    `V.topIso.inv` with `(Scheme.ΓSpecIso Γ(X, V)).inv`, is
    `Stacks.Conormal.CotangentAppIso.isoSpecPushforwardTopSectionsIso`, whose content is
    `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop`.

  With those, `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` inhabits the
  type of part (2); what the statement of part (2) adds beyond it is the generator formula,
  the next item.
* **No generator formula.** Nothing here says where a named *section of a module* goes, so the
  generator lemma `pushforwardConormalIsoCotangent_apply` and the `WithQuotient` subtype are
  untouched.
  What `appLE_eq_ΓSpecIso_inv` supplies is only the ring-map half: the hypothesis of part (2)'s
  generator formula, re-expressed so that the element of `Γ(X, V)` naming the generator reaches
  `W` through the same `(Scheme.ΓSpecIso Γ(X, V)).inv` the affine model uses. The formula itself
  is an equation between sections of `Stacks.Conormal.conormalSheaf i`, and
  `conormalSheafRestrictIsoAffineModel` is still not described on sections.

  The transfer of the open `W`
  from `U.toScheme` to `(U.ι ⁻¹ᵁ V).toScheme` does **not** need
  `AlgebraicGeometry.Scheme.Hom.appIso`, whose `inv` field is sealed at this pin. Stating the map
  at the level of global sections of `(U.ι ⁻¹ᵁ V).toScheme` and coming back with
  `AlgebraicGeometry.Scheme.Opens.topIso` and one restriction map avoids `appIso` entirely —
  `AlgebraicGeometry.Scheme.Hom.resLE_app_top` is the lemma that does it, and the proof is four
  rewrites with no compiler option.
* **No reduction of the factorization quantifier.** `conormalSheafRestrictIsoOfLe` is stated for
  one factorization at a time; it does *not* say that two factorizations give the same comparison.
* **Nothing about `Ideal.Cotangent`, the square of the ideal, or epimorphy of the quotient map.**

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.AffineShape

/-- **The restriction of an open inclusion to a smaller open is the canonical isomorphism.** Both
sides become `(U.ι ⁻¹ᵁ V).ι ≫ U.ι` after composition with the monomorphism `V.ι`, by
`AlgebraicGeometry.morphismRestrict_ι` and
`AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_ι` respectively. -/
theorem morphismRestrict_opens_ι {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    U.ι ∣_ V = (Scheme.Opens.isoOfLE hVU).hom := by
  rw [← cancel_mono V.ι, morphismRestrict_ι, Scheme.Opens.isoOfLE_hom_ι]

/-- **The restriction of a factored morphism to an open contained in the factoring open.** If
`i' ≫ U.ι = i` and `V ≤ U` then `i ∣_ V` is `i' ∣_ (U.ι ⁻¹ᵁ V)` followed by the canonical
isomorphism `(U.ι ⁻¹ᵁ V).toScheme ≅ V.toScheme`. -/
theorem morphismRestrict_comp_isoOfLE {Z X : Scheme.{u}} (U : X.Opens) (i' : Z ⟶ U.toScheme)
    (V : X.Opens) (hVU : V ≤ U) :
    i' ∣_ (U.ι ⁻¹ᵁ V) ≫ (Scheme.Opens.isoOfLE hVU).hom = (i' ≫ U.ι) ∣_ V := by
  rw [morphismRestrict_comp, morphismRestrict_opens_ι]

/-- **Locality of the conormal sheaf at an open of the ambient scheme.** For a closed-immersion
factorization `i' : Z ⟶ U` of an immersion `i : Z ⟶ X` and an open `V ≤ U` of `X`, the restriction
of `Stacks.Conormal.conormalSheaf i` to `i ⁻¹ᵁ V` is the module pullback along `i ∣_ V` of the
ideal sheaf of `i ∣_ V`.

This is the shape the affine computation needs, and the shape
`Stacks.Conormal.Locality.conormalSheafRestrictIso` does not have: there the open ranges over
opens of the factorization's target and the restricted morphism is `i' ∣_ V'`, so the statement
mentions the chosen factorization twice. Here neither `U` nor `i'` occurs in the conclusion.

`morphismRestrict_comp_isoOfLE` says `i' ∣_ (U.ι ⁻¹ᵁ V)` and `i ∣_ V` differ by an isomorphism of
the target, and `Transport.idealSheafPullbackIsoOfIsoTarget` transports the pulled-back ideal
sheaf along such an isomorphism. The factorization hypothesis is discharged by `subst`, after
which `i' ⁻¹ᵁ (U.ι ⁻¹ᵁ V)` and `i ⁻¹ᵁ V` are the same open by `rfl`. -/
noncomputable def conormalSheafRestrictIsoOfLe {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V : X.Opens) (hVU : V ≤ U) :
    (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj (Stacks.Conormal.conormalSheaf i) ≅
      (modulePullback (i ∣_ V).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (i ∣_ V).toLRSHom.toShHom) := by
  subst hfac
  exact Locality.conormalSheafRestrictIso (i' ≫ U.ι) U i' rfl (U.ι ⁻¹ᵁ V) ≪≫
    (AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget (i' ∣_ (U.ι ⁻¹ᵁ V))
      (Scheme.Opens.isoOfLE hVU) ((i' ≫ U.ι) ∣_ V)
      (morphismRestrict_comp_isoOfLE U i' V hVU)).symm

/-- Transporting the module pullback along an equality of morphisms. Stated with `subst` rather
than `rw` because the morphism occurs in the type of the functor being applied. -/
noncomputable def pullbackObjCongr {A D : Scheme.{u}} {g g' : A ⟶ D} (h : g = g') (M : D.Modules) :
    (Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g').obj M := by
  subst h; exact Iso.refl _

/-- **`pullbackObjCongr` commutes with the units.** Transporting along an equality of morphisms
carries the unit of `g^* ⊣ g_*` to the unit of `g'^* ⊣ g'_*`, the two targets being matched by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`.

This is the compatibility with the units that
`StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic` names as absent for this factor of
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso`. Like the definition it is discharged by
`subst`, after which both transports are the identity on sections. -/
theorem unit_comp_map_pullbackObjCongr {A D : Scheme.{u}} {g g' : A ⟶ D} (h : g = g')
    (M : D.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map (pullbackObjCongr h M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction g').unit.app M ≫
        (Scheme.Modules.pushforwardCongr h.symm).hom.app
          ((Scheme.Modules.pullback g').obj M) := by
  subst h
  have hid : (Scheme.Modules.pushforwardCongr (rfl : g = g)).hom.app
      ((Scheme.Modules.pullback g).obj M) = 𝟙 _ := by
    ext U : 3
    simp
  rw [hid]
  simp [pullbackObjCongr]

/-- **The presentation square of Tag 01R3 part (2), with the fibre product replaced by the open
subscheme.**
The hypothesis `he` of [Stacks, Tag 01R3]'s part (2) is a square over the fibre product
`Z ×_X V`; `AlgebraicGeometry.pullbackRestrictIsoRestrict` identifies that with `i ⁻¹ᵁ V`, and
cancelling it off turns `he` into the same square for `i ∣_ V`. This is the hypothesis shape that
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare` consumes, and the
isomorphism appearing in it, `ε = (pullbackRestrictIsoRestrict i V).symm ≪≫ e`, is the one the
junction below pulls back along. -/
theorem morphismRestrict_isoSpec_eq {Z X : Scheme.{u}} (i : Z ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    (i ∣_ V) ≫ hV.isoSpec.hom =
      ((pullbackRestrictIsoRestrict i V).symm ≪≫ e).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict i V).hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict_assoc]
  exact he

/-- **The restricted conormal sheaf is the affine model's pulled-back ideal sheaf.** For an
immersion `i : Z ⟶ X` and the part (2) data of [Stacks, Tag 01R3] — an affine open `V`, an ideal
`I` of `Γ(X, V)`, a presentation `e` of the fibre as `Spec (Γ(X, V) ⧸ I)` and the compatibility
`he` — the restriction of `Stacks.Conormal.conormalSheaf i` to `i ⁻¹ᵁ V` is the module pullback,
along `ε = (pullbackRestrictIsoRestrict i V).symm ≪≫ e`, of the module pullback along
`k = Spec.map (Ideal.Quotient.mk I)` of the ideal sheaf of `k`.

The right-hand side is precisely the sheaf whose global sections
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` computes to be `I.Cotangent`, pulled
back along an isomorphism of schemes; `Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv`
turns that pullback into a pushforward, where sections are computable. So this is the whole of the
sheaf-level passage from the construction of the conormal sheaf to the affine model.

Four steps: the containment `V ≤ i.coborderRange` forced by the presentation
(`le_coborderRange_of_isoSpecQuotient`), the shape match `conormalSheafRestrictIsoOfLe` at the
defining factorization, the source-slot junction
`idealSheafIsoAffineModelOfMorphismRestrict`, and `modulePullbackCompIso` twice around
`morphismRestrict_isoSpec_eq`. -/
noncomputable def conormalSheafRestrictIsoAffineModel {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj (Stacks.Conormal.conormalSheaf i) ≅
      (modulePullback ((pullbackRestrictIsoRestrict i V).symm ≪≫ e).hom.toLRSHom.toShHom).obj
        ((modulePullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom)) :=
  conormalSheafRestrictIsoOfLe i i.coborderRange i.liftCoborder i.liftCoborder_ι V
      (AffineCotangent.le_coborderRange_of_isoSpecQuotient i V hV I e he) ≪≫
    (Scheme.Modules.pullback (i ∣_ V)).mapIso
      (AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict
        i V hV I e he) ≪≫
    ((Stacks.PullbackPseudofunctor.modulePullbackCompIso hV.isoSpec.hom.toLRSHom.toShHom
      (i ∣_ V).toLRSHom.toShHom).app _).symm ≪≫
    pullbackObjCongr (morphismRestrict_isoSpec_eq i V hV I e he) _ ≪≫
    (Stacks.PullbackPseudofunctor.modulePullbackCompIso
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom
      ((pullbackRestrictIsoRestrict i V).symm ≪≫ e).hom.toLRSHom.toShHom).app _

/-- **The global sections of the restricted conormal sheaf are those of the affine model.** The
same identification as `conormalSheafRestrictIsoAffineModel`, evaluated at `⊤` and with the
pullback along `ε` traded for the pushforward along `ε.inv`, which is where sections are
computable: the sections over `⊤` of `(ε.inv)_* N` are the sections of `N` over `ε.inv ⁻¹ᵁ ⊤`, and
`ε.inv ⁻¹ᵁ ⊤ = ⊤` by `rfl`.

The right-hand side is therefore the global sections of `k^* I(k)` with the structure sheaf of
`i ⁻¹ᵁ V` acting through `ε.inv`, and
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` identifies that module with
`I.Cotangent`. What is *not* supplied is the comparison of the two scalar actions, over
`Γ((i ⁻¹ᵁ V).toScheme, ⊤)` here and over `Γ(X, V)` in Tag 01R3; see the module docstring. -/
noncomputable def conormalRestrictTopSectionsIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj
        (Stacks.Conormal.conormalSheaf i)).val.obj (.op ⊤) ≅
      ((Scheme.Modules.pushforward ((pullbackRestrictIsoRestrict i V).symm ≪≫ e).inv).obj
          ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
              (Stacks.ClosedImmersion.idealSheaf
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom))).val.obj
        (.op ⊤) :=
  (SheafOfModules.evaluation (i ⁻¹ᵁ V).toScheme.ringCatSheaf (.op ⊤)).mapIso
    (conormalSheafRestrictIsoAffineModel i V hV I e he ≪≫
      (pullbackIsoPushforwardInv ((pullbackRestrictIsoRestrict i V).symm ≪≫ e)).app _)

/-- **The ambient restriction map over an affine open, routed through `Spec Γ(X, V)`.** For opens
`V ≤ U` of `X` with `V` affine and an open `W` of `U.toScheme` contained in `U.ι ⁻¹ᵁ V`, the
structure-sheaf map `U.ι.appLE V W hW` — the map that names a section of `Γ(X, V)` on `W`, and the
map appearing in the hypothesis of the part (2) generator formula of [Stacks, Tag 01R3] — is
`(AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V)).inv` followed by the global-sections map of
`(isoOfLE hVU).hom ≫ hV.isoSpec.hom`, the identification of `Γ((U.ι ⁻¹ᵁ V).toScheme, ⊤)` with
`Γ(U.toScheme, U.ι ⁻¹ᵁ V)`, and the restriction map of `U.toScheme` down to `W`.

`(Scheme.ΓSpecIso Γ(X, V)).inv` is the ring map through which the affine model's answer is stated
(`Stacks.Conormal.CotangentAppIso.moduleSpecΓFunctor_obj_eq`), so this is the form in which a
section named by an element of `Γ(X, V)` can be followed through the chain of
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso`.

There is no morphism `U.toScheme ⟶ Spec Γ(X, V)`, so no `appLE` of the composite produces the
map directly; `(isoOfLE hVU).hom ≫ hV.isoSpec.hom` is defined on `(U.ι ⁻¹ᵁ V).toScheme` instead,
and the passage back to an open `W` of `U.toScheme` is carried by
`AlgebraicGeometry.Scheme.Opens.topIso` together with a restriction map, not by
`AlgebraicGeometry.Scheme.Hom.appIso` — so the sealed `inv` field of `appIso` is not involved at
all.

The route is `morphismRestrict_opens_ι` read backwards: `(isoOfLE hVU).hom` is `U.ι ∣_ V`, hence
`AlgebraicGeometry.Scheme.Hom.resLE` of `U.ι`, whose global-sections map is `appLE` conjugated by
the two `topIso`s (`AlgebraicGeometry.Scheme.Hom.resLE_app_top`). All four `topIso`/`ΓSpecIso`
factors then cancel in pairs and `AlgebraicGeometry.Scheme.Hom.appLE_map` absorbs the restriction
to `W`. -/
theorem appLE_eq_ΓSpecIso_inv {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U)
    (hV : IsAffineOpen V) (W : U.toScheme.Opens) (hW : W ≤ U.ι ⁻¹ᵁ V) :
    U.ι.appLE V W hW =
      (Scheme.ΓSpecIso Γ(X, V)).inv ≫
        ((Scheme.Opens.isoOfLE hVU).hom ≫ hV.isoSpec.hom).appTop ≫
          (U.ι ⁻¹ᵁ V).topIso.hom ≫ U.toScheme.presheaf.map (homOfLE hW).op := by
  rw [Scheme.Hom.comp_appTop, hV.isoSpec_hom_appTop, ← morphismRestrict_opens_ι hVU,
    ← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Scheme.Hom.appLE_map]

end Stacks.Conormal.AffineShape

end
