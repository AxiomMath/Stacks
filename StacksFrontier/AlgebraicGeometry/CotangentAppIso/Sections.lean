module

public import StacksFrontier.AlgebraicGeometry.CotangentAppIso.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.AffineModel
public import StacksFrontier.AlgebraicGeometry.ConormalAffineShape.Shape
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sections over an affine open are `I / I²`

`StacksFrontier.AlgebraicGeometry.ConormalAffineShape.Shape` carries the sheaf-level passage from
the construction of the conormal sheaf to the affine model
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent`, and records that what separates it
from the part (2) assertions of [Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) is
one kind of step: two restriction-of-scalars comparisons.
`StacksFrontier.AlgebraicGeometry.CotangentAppIso.Basic` supplies those. This file closes the
chain and produces the `Γ(X, V)`-module isomorphism.

The engine is stated once, for an arbitrary morphism of schemes and an arbitrary module, taking
the locality comparison as an input; the two shapes [Stacks, Tag 01R3] asks for — at the
immersion itself and at a closed-immersion factorization — are then instances, differing only in
which locality comparison is fed in.

## Main definitions

* `Stacks.Conormal.CotangentAppIso.restrictAffineModelIso`: **the sheaf-level engine.** For a
  morphism `j : A ⟶ B`, a module `M` on `A`, an affine open `V` of `B` with the
  presentation data of the tag `I, e, he`, and a locality comparison identifying `M ∣_ (j ⁻¹ᵁ V)` with the
  inverse image along `j ∣_ V` of the ideal sheaf of `j ∣_ V`, the restriction of `j _* M` to `V`
  is the pushforward along `hV.isoSpec.inv` of the affine model's sheaf
  `k _* k ^* I(k)`, where `k = Spec.map (Ideal.Quotient.mk I)`.
* `Stacks.Conormal.CotangentAppIso.affineSectionsIsoCotangent`: **the engine's conclusion.** With
  the same data, the `Γ(B, V)`-module of sections of `j _* M` over `V` is `I.Cotangent`.
* `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`: the instance at the
  immersion itself, which inhabits the type of
  [Stacks, Tag 01R3]'s `affineConormalIsoCotangent` (part (2)).
* `Stacks.Conormal.CotangentAppIso.pushforwardConormalSectionsIsoCotangent`: the instance at a
  closed-immersion factorization, which inhabits the type of [Stacks, Tag 01R3]'s
  `pushforwardConormalIsoCotangent` (part (1)).

## Route

Six factors, all of them already in the library or in `Basic`:

1. `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`: restricting a direct
   image to `V` is the direct image along `j ∣_ V` of the restriction to `j ⁻¹ᵁ V`. This is what
   makes the locality comparison applicable at all.
2. the locality comparison `c`, under `Scheme.Modules.pushforward (j ∣_ V)`.
3. `Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict`
   together with `Stacks.PullbackPseudofunctor.modulePullbackCompIso` twice around
   `Stacks.Conormal.AffineShape.morphismRestrict_isoSpec_eq` — exactly the tail of
   `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel`, which this generalizes by
   taking `c` as a hypothesis instead of deriving it at the defining factorization.
4. `Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv`, which turns the inverse image along
   the isomorphism `ε` identifying `j ⁻¹ᵁ V` with `Spec (Γ(B, V) ⧸ I)` into the direct image
   along `ε.inv`, so that the two remaining factors are both direct images.
5. `AlgebraicGeometry.Scheme.Modules.pushforwardComp` and `pushforwardCongr` at
   `ε.inv ≫ (j ∣_ V) = k ≫ hV.isoSpec.inv`, which is the statement's square with `ε` cancelled off.
6. the two comparisons of `CotangentAppIso.Basic`, and the affine model.

## Universe situation

A single universe `u`, as in the tagged statements.

## Transparency notes

`Stacks.ClosedImmersion.idealSheaf` is stated for the underlying morphism of ringed spaces and
the locality comparisons for `RingedSpaceModuleAdjunction.modulePullback`; the two spellings are
mixed with `AlgebraicGeometry.Scheme.Modules.pullback` deliberately, because the inputs come in
different ones, and `Iso.trans` unifies them without a `change`. This works here as it does
in `ConormalAffineShape.Shape`.

## What is not done, and why no tag is attached

**No `stacks` attribute is attached, and the reason is specific rather than cautionary.**

The tagged statement gives `affineConormalIsoCotangent` as
`(affineConormalIsoCotangentWithQuotient …).val` — the projection of a *subtype*, whose second
component is the formula on ideal generators for every closed-immersion factorization and every
open of it: the affine identification is constructed together with its formula on ideal
generators from every closed factorization. Four further labels of the statement are derived from
that second component. `conormalAffineSectionsIsoCotangent` below inhabits the *type* of
`affineConormalIsoCotangent`, canonically and from the statement's hypotheses verbatim, but it is
not the subtype's projection and carries no generator formula, so the assertion that label names
is only partly discharged. The same holds for `pushforwardConormalSectionsIsoCotangent` against
the statement's `pushforwardConormalIsoCotangent`, whose companion label
`pushforwardConormalIsoCotangent_apply` is the generator formula for it.

The missing declaration is an elementwise formula for `Stacks.Conormal.AffineShape.conormalSheafRestrictIsoAffineModel` — the
only factor of the chain above that is not the identity on sections or a restriction map — saying
where the adjunction unit of the ideal sheaf goes. Everything else in this file is identity on
sections (`pushforwardComp`, the `restrictScalars` comparisons, `pushforward_sections_eq`) or a
presheaf restriction map (`sectionsCongr`, `pushforwardCongr`,
`AffinePushforward.restrictPushforwardIso` via
`Stacks.Conormal.Restriction.restrictPushforwardIso_hom_app`), and the affine model already
carries its generator formula.

The ring-map half of that formula's *hypothesis* is now available:
`Stacks.Conormal.AffineShape.appLE_eq_ΓSpecIso_inv` re-expresses `U.ι.appLE V W hW`, the map the
statement uses to name a generator on `W`, through the same `(Scheme.ΓSpecIso Γ(B, V)).inv` that
`moduleSpecΓFunctor_obj_eq` makes the affine model's scalars act by. The module-level half is
still absent.

Also not done:

* **No unit statement for the engine.** Every ideal-sheaf factor of `restrictAffineModelIso` now
  has one, and so do the two that
  `StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic` listed as missing:
  `Stacks.Conormal.AffineShape.unit_comp_map_pullbackIsoPushforwardInv` and
  `Stacks.Conormal.AffineShape.unit_comp_map_pullbackObjCongr`. The two
  `AlgebraicGeometry.Scheme.Modules.pushforwardComp`/`pushforwardCongr` steps need nothing new —
  Mathlib's `pushforwardComp_hom_app_app` is `𝟙` by `rfl` and `pushforwardCongr_hom_app_app` is a
  presheaf restriction map, also by `rfl`. What blocks the assembly is a property of the engine
  itself rather than a missing factor: **the locality comparison `c` enters as a bare hypothesis,
  with no characterization at all**, so a unit statement for `restrictAffineModelIso` cannot be
  stated without also assuming one for `c` — and the two instances below feed in different
  comparisons (`Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe` and
  `Stacks.Conormal.Locality.conormalSheafRestrictIso`), whose own unit statements are
  `Stacks.Conormal.Locality.unit_comp_map_conormalRestrictIso` and nothing, respectively. The
  engine therefore needs one more argument before it can carry a generator formula.
* **No reduction of the factorization quantifier.** The engine is applied at one locality
  comparison at a time, and nothing says that two factorizations give the same answer.
* **Nothing about the square of the ideal or epimorphy of the quotient map**, so the part (1)
  labels "sheaf quotient map is epimorphic" and "quotient by the ideal square" are untouched.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Conormal.CotangentAppIso

variable {A B : Scheme.{u}} (j : A ⟶ B) (M : A.Modules) (V : B.Opens) (hV : IsAffineOpen V)
  (I : Ideal Γ(B, V)) (e : Limits.pullback j V.ι ≅ Spec (.of (Γ(B, V) ⧸ I)))

/-- The square of the statement with the identification of the fibre product cancelled off and the
isomorphism `ε` moved to the other side: `ε.inv ≫ (j ∣_ V) = k ≫ hV.isoSpec.inv`.

This is the form in which `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` can use it, both
sides being composites of *two* morphisms with the two direct images taken in the opposite
order. -/
theorem isoSpec_inv_comp_eq
    (he : Limits.pullback.snd j V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ((pullbackRestrictIsoRestrict j V).symm ≪≫ e).inv ≫ (j ∣_ V) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ hV.isoSpec.inv := by
  rw [Iso.eq_comp_inv, Category.assoc,
    Stacks.Conormal.AffineShape.morphismRestrict_isoSpec_eq j V hV I e he,
    Iso.inv_hom_id_assoc]

/-- **The sheaf-level engine.** Let `j : A ⟶ B` be a morphism of schemes, `M` a module on `A`,
`V` an affine open of `B`, and `I, e, he` the presentation data of [Stacks, Tag 01R3]'s part (2):
an ideal of `Γ(B, V)` with an identification of the fibre `A ×_B V` with `Spec (Γ(B, V) ⧸ I)`
over `V`. Let `c` identify the restriction of `M` to `j ⁻¹ᵁ V` with the inverse image along
`j ∣_ V` of the ideal sheaf of `j ∣_ V` — the conclusion of the locality comparisons for the
conormal sheaf.

Then the restriction to `V` of the direct image `j _* M` is the direct image along
`hV.isoSpec.inv` of the affine model's sheaf `k _* k ^* I(k)`, for
`k = Spec.map (Ideal.Quotient.mk I)`.

Both remaining functors are direct images, which is what makes the right-hand side computable on
sections; see `affineSectionsIsoCotangent`. -/
noncomputable def restrictAffineModelIso
    (he : Limits.pullback.snd j V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (c : (Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι).obj M ≅
      (modulePullback (j ∣_ V).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom)) :
    (Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.pushforward j).obj M) ≅
      (Scheme.Modules.pushforward hV.isoSpec.inv).obj
        ((Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
          ((Scheme.Modules.pullback
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
            (Stacks.ClosedImmersion.idealSheaf
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom))) :=
  (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso j V).app M ≪≫
    (Scheme.Modules.pushforward (j ∣_ V)).mapIso
      (c ≪≫
        (Scheme.Modules.pullback (j ∣_ V)).mapIso
          (AffineCotangent.SourceTransport.idealSheafIsoAffineModelOfMorphismRestrict
            j V hV I e he) ≪≫
        ((Stacks.PullbackPseudofunctor.modulePullbackCompIso hV.isoSpec.hom.toLRSHom.toShHom
          (j ∣_ V).toLRSHom.toShHom).app _).symm ≪≫
        AffineShape.pullbackObjCongr
          (AffineShape.morphismRestrict_isoSpec_eq j V hV I e he) _ ≪≫
        (Stacks.PullbackPseudofunctor.modulePullbackCompIso
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom.toShHom
          ((pullbackRestrictIsoRestrict j V).symm ≪≫ e).hom.toLRSHom.toShHom).app _ ≪≫
        (AffineShape.pullbackIsoPushforwardInv
          ((pullbackRestrictIsoRestrict j V).symm ≪≫ e)).app _) ≪≫
    (Scheme.Modules.pushforwardComp
      ((pullbackRestrictIsoRestrict j V).symm ≪≫ e).inv (j ∣_ V)).app _ ≪≫
    (Scheme.Modules.pushforwardCongr (isoSpec_inv_comp_eq j V hV I e he)).app _ ≪≫
    (Scheme.Modules.pushforwardComp
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hV.isoSpec.inv).symm.app _

/-- **The engine's conclusion: the sections are `I / I²`.** With the data of
`restrictAffineModelIso`, the `Γ(B, V)`-module of sections of `j _* M` over `V` is
`Ideal.Cotangent` of `I`.

Three steps on top of the sheaf-level engine: `sectionsRestrictTopIso` turns sections over `V`
into global sections of the restriction to `V`, `isoSpecPushforwardTopSectionsIso` turns the
global sections of the direct image along `hV.isoSpec.inv` into
`AlgebraicGeometry.moduleSpecΓFunctor` of the affine model's sheaf, and
`Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` computes that to be
`I.Cotangent`. -/
noncomputable def affineSectionsIsoCotangent
    (he : Limits.pullback.snd j V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (c : (Scheme.Modules.restrictFunctor (j ⁻¹ᵁ V).ι).obj M ≅
      (modulePullback (j ∣_ V).toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf (j ∣_ V).toLRSHom.toShHom)) :
    ((Scheme.Modules.pushforward j).obj M).val.obj (.op V) ≅
      ModuleCat.of Γ(B, V) I.Cotangent :=
  sectionsRestrictTopIso _ V ≪≫
    (ModuleCat.restrictScalars V.topIso.inv.hom).mapIso
      ((SheafOfModules.evaluation V.toScheme.ringCatSheaf (.op ⊤)).mapIso
        (restrictAffineModelIso j M V hV I e he c)) ≪≫
    isoSpecPushforwardTopSectionsIso V hV _ ≪≫
    (Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent Γ(B, V) I).choose

/-! ### The two shapes of [Stacks, Tag 01R3] -/

/-- **The conormal sections over an affine open of the ambient scheme.** For an immersion
`i : Z ⟶ X` and the part (2) data of [Stacks, Tag 01R3] — an affine open `V` of `X`, an ideal `I`
of `Γ(X, V)`, an identification `e` of the fibre with `Spec (Γ(X, V) ⧸ I)` and the compatibility
`he` — the sections over `V` of the direct image of `Stacks.Conormal.conormalSheaf i` are
`I.Cotangent`, as `Γ(X, V)`-modules.

This inhabits the type of the statement's `affineConormalIsoCotangent`, from its hypotheses
verbatim: nothing is Noetherian, finite or quasi-compact, and the only closed-immersion
hypothesis used is the one carried by `AlgebraicGeometry.Scheme.Hom.liftCoborder`. It is **not**
the tagged declaration, which is the projection of a generator-carrying subtype; see the "What is
not done" section of the module docstring.

The locality comparison fed into the engine is
`Stacks.Conormal.AffineShape.conormalSheafRestrictIsoOfLe` at the defining factorization, whose
containment hypothesis `V ≤ i.coborderRange` is forced by the presentation
(`Stacks.Conormal.AffineCotangent.le_coborderRange_of_isoSpecQuotient`). -/
@[ega "IV 16.1.2" "special case",
  sga "5 III 6.8" "partial",
  sga "6 0 2.1" "partial",
  sga "6 VII 1.6",
  sga "7 VI 4.7" "special case"]
noncomputable def conormalAffineSectionsIsoCotangent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (V : X.Opens) (hV : IsAffineOpen V) (I : Ideal Γ(X, V))
    (e : Limits.pullback i V.ι ≅ Spec (.of (Γ(X, V) ⧸ I)))
    (he : Limits.pullback.snd i V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ((modulePushforward i.toLRSHom.toShHom).obj
      (Stacks.Conormal.conormalSheaf i)).val.obj (.op V) ≅
        ModuleCat.of Γ(X, V) I.Cotangent :=
  affineSectionsIsoCotangent i (Stacks.Conormal.conormalSheaf i) V hV I e he
    (AffineShape.conormalSheafRestrictIsoOfLe i i.coborderRange i.liftCoborder
      i.liftCoborder_ι V (AffineCotangent.le_coborderRange_of_isoSpecQuotient i V hV I e he))

/-- **The conormal sections over an affine open of a closed-immersion factorization.** For an
immersion `i : Z ⟶ X`, a closed-immersion factorization `i' : Z ⟶ U.toScheme` of it, and the
part (1) data of [Stacks, Tag 01R3] at an affine open `V` of `U.toScheme`, the sections over `V`
of the direct image along `i'` of `Stacks.Conormal.conormalSheaf i` are `I.Cotangent`, as
`Γ(U.toScheme, V)`-modules.

This inhabits the type of the statement's `pushforwardConormalIsoCotangent`, and is the same engine
with `Stacks.Conormal.Locality.conormalSheafRestrictIso` — which is stated for an open of the
factorization's target — fed in as the locality comparison, in place of
`conormalSheafRestrictIsoOfLe`. As above, it carries no generator formula and is not the tagged
declaration. -/
noncomputable def pushforwardConormalSectionsIsoCotangent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(U.toScheme, V))
    (e : Limits.pullback i' V.ι ≅ Spec (.of (Γ(U.toScheme, V) ⧸ I)))
    (he : Limits.pullback.snd i' V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ((modulePushforward i'.toLRSHom.toShHom).obj
      (Stacks.Conormal.conormalSheaf i)).val.obj (.op V) ≅
        ModuleCat.of Γ(U.toScheme, V) I.Cotangent :=
  affineSectionsIsoCotangent i' (Stacks.Conormal.conormalSheaf i) V hV I e he
    (Locality.conormalSheafRestrictIso i U i' hfac V)

end Stacks.Conormal.CotangentAppIso

end
