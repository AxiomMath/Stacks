module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDerivationSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningRestrict
public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareIso
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentRestrictNatural
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two conormal tracks of an infinitesimal deformation agree

The unrestricted form of [Stacks Project, Tag 04FG] produces, from two lifts of one morphism
inducing the same map of conormal sheaves, a derivation datum
```
θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}
```
spelled `(Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
Stacks.Conormal.conormalSheaf i` — see `Stacks.Thickenings.exists_isDerivationAction`. The
deformation-sheaf development of [Stacks Project, Tag 04FH] and [Stacks Project, Tag 04FI]
spells the same object `Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶
Stacks.Thickenings.conormalModules i`, and it needs the datum over an **open** `V` of `X'`, that
is for the restricted thickening `i ∣_ V` rather than for `i`.

This file is the bridge between the two spellings, in both respects.

## Main definitions

* `Stacks.Modules.ofRingedSpaceHom` and `Stacks.Modules.ofRingedSpaceIso`: a morphism, resp. an
  isomorphism, of sheaves of modules on the ringed space underlying a scheme, read in
  `AlgebraicGeometry.Scheme.Modules`. The two are the same type, but they carry different
  `CategoryTheory.Category` instances, so an isomorphism built in one of them is not accepted in
  the other without this step.
* `Stacks.Immersion.conormalSheafPullbackRestrictIso`: `ι_{i⁻¹V}^* 𝒞_{X/X'} ≅ 𝒞_{i ∣_ V}`, the
  isomorphism whose underlying morphism is the map of [Stacks Project, Tag 01R4] of the
  restriction square, and `Stacks.Thickenings.pullbackConormalModulesIso`,
  `Stacks.Thickenings.restrictConormalModulesIso`: the same in the scheme-module vocabulary,
  for the pullback and for `AlgebraicGeometry.Scheme.Modules.restrict`. These are the conormal
  counterpart of `Stacks.Smooth.restrictPullbackCotangentSheafIso`.
* `Stacks.Thickenings.derivationDatumOfCotangent` and
  `Stacks.Thickenings.cotangentDatumOfDerivationDatum`, packaged as
  `Stacks.Thickenings.derivationDatumEquiv`: the translation of a derivation datum between the
  two spellings of the sheaf of relative differentials, along
  `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`.
* `Stacks.Thickenings.restrictDerivationDatumEquiv`: a datum for the restricted thickening
  `i ∣_ V` is a morphism between the restrictions to `i⁻¹V` of `a^*Ω_{Y/S}` and of `𝒞_{X/X'}`.
* `Stacks.Modules.overHomEquivRestrictHom`: morphisms of the restrictions of two sheaves of
  modules to the site of opens contained in `U` are morphisms of their restrictions to the open
  subscheme `U`; by `Stacks.Modules.overHomEquivRestrictHom_val_app` the bijection does nothing
  to sections.

## Main results

* `Stacks.Thickenings.derivationSectionι_derivationDatumOfCotangent`: the derivation
  `D = θ ∘ d_{Y/S}` of Equation [Stacks Project, Tag 04BV] attached to a translated datum is
  `Stacks.Smooth.pullbackD` followed by `θ` on sections and the inclusion of the conormal sheaf.
  This is the sectionwise half of the bridge, and the form the deformation sheaf consumes.
* `Stacks.Thickenings.exists_isDerivationAction_pullbackCotangentSheaf`: the unrestricted
  [Stacks Project, Tag 04FG] read on the `Stacks.Smooth.pullbackCotangentSheaf` track.
* `Stacks.Thickenings.exists_isDerivationAction_morphismRestrict` and
  `Stacks.Thickenings.exists_isDerivationAction_over`: the same for two lifts of `a` over an open
  `V` of `X'`, with the datum a morphism of the restrictions to `i⁻¹V`, respectively a section
  over `i⁻¹V` of the sheaf of homomorphisms. These are the shapes the simple-transitivity half of
  [Stacks Project, Tag 04FJ] needs.

## Implementation notes

Nothing here is a new mathematical input. The morphism-level identity
`Stacks.Immersion.modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso` already says that
the composite of the three comparison isomorphisms identifying `𝒞_{X/X'}|_{i⁻¹V}` with
`𝒞_{i ∣_ V}` *is* the canonical map of [Stacks Project, Tag 01R4] of the restriction square, and
`Stacks.Immersion.isIso_immersionConormalSheafMap_ι` already records that that map is
invertible; on the differentials side `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`,
`Stacks.Smooth.restrictPullbackCotangentSheafIso` and `Stacks.Smooth.pullbackD_self` are all
available. What is new is the assembly, and the sectionwise identity that makes it usable.

The only real obstacle is that `AlgebraicGeometry.Scheme.Modules` is a structure copy of
`SheafOfModules`: the two hom types are the same type, but the `CategoryTheory.Category`
instances are distinct terms, so `CategoryTheory.asIso` elaborated in one spelling does not see
the `CategoryTheory.IsIso` hypothesis supplied in the other, and `rw` motives do not typecheck
across the two. Two devices handle this. Isomorphisms are built in the `SheafOfModules`
spelling and moved across by `Stacks.Modules.ofRingedSpaceIso`, which is the identity.
Equalities of morphisms are proved by `Eq.trans`/`congrArg` chains and by the generic
`CategoryTheory.Iso.map_hom_inv_id_assoc`, never by rewriting inside a goal that mentions both
spellings.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace
open Stacks.Immersion Stacks.Thickenings

universe u

/-! ### The two spellings of a sheaf of modules on a scheme -/

namespace Stacks.Modules

variable {Z : Scheme.{u}} {M N : Z.Modules}

/-- **A morphism of sheaves of modules on the ringed space underlying a scheme, read in
`AlgebraicGeometry.Scheme.Modules`.** The two hom types are the same type, by
`Stacks.SchemeCohomology.ringSheaf_ringedSpace` and the definition of
`AlgebraicGeometry.Scheme.Modules.Hom`, so this is the identity. -/
def ofRingedSpaceHom
    (f : (M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) ⟶ N) :
    M ⟶ N := f

/-- **An isomorphism of sheaves of modules on the ringed space underlying a scheme, read in
`AlgebraicGeometry.Scheme.Modules`.** Both components are
`Stacks.Modules.ofRingedSpaceHom`, and the two identities are the identities of the given
isomorphism: the composition of the two spellings agrees on the nose, only the instances
differ. -/
def ofRingedSpaceIso
    (e : (M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) ≅ N) :
    M ≅ N where
  hom := ofRingedSpaceHom e.hom
  inv := ofRingedSpaceHom e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The forward morphism of `Stacks.Modules.ofRingedSpaceIso e` is
`Stacks.Modules.ofRingedSpaceHom e.hom`. -/
@[simp]
theorem ofRingedSpaceIso_hom
    (e : (M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) ≅ N) :
    (ofRingedSpaceIso e).hom = ofRingedSpaceHom e.hom := rfl

/-- The inverse morphism of `Stacks.Modules.ofRingedSpaceIso e` is
`Stacks.Modules.ofRingedSpaceHom e.inv`. -/
@[simp]
theorem ofRingedSpaceIso_inv
    (e : (M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)) ≅ N) :
    (ofRingedSpaceIso e).inv = ofRingedSpaceHom e.inv := rfl

/-- **The sections of a sheaf of homomorphisms of [Stacks Project, Tag 01CO] over an open, read
through the open subscheme.** A morphism of the restrictions of `M` and `N` to the site of opens
contained in `U` is a morphism of their restrictions to the open subscheme `U`, by the
equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` of the two categories of modules on
`U`, which carries `SheafOfModules.over` to `AlgebraicGeometry.Scheme.Modules.restrict` by
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`. -/
def overHomEquivRestrictHom (M N : Z.Modules) (U : Z.Opens) :
    (M.over U ⟶ N.over U) ≃ (M.restrict U.ι ⟶ N.restrict U.ι) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app M)
      ((Scheme.Modules.overFunctorEquiv U).app N))

/-- **`Stacks.Modules.overHomEquivRestrictHom` does nothing to sections.** Over an open `W` of
the open subscheme `U` the two sides act by the same map: the sections of `M.restrict U.ι` over
`W` are the sections of `M` over `U.ι ''ᵁ W`, which are the sections of `M.over U` over that open
viewed in `Over U`, and the equivalence is the identity on them. -/
theorem overHomEquivRestrictHom_val_app (M N : Z.Modules) (U : Z.Opens)
    (θ : M.over U ⟶ N.over U) (W : U.toScheme.Opens)
    (x : (M.restrict U.ι).val.obj (op W)) :
    (overHomEquivRestrictHom M N U θ).val.app (op W) x =
      θ.val.app (op (Over.mk (homOfLE (U.ι_image_le W)))) x := rfl

end Stacks.Modules

/-! ### The conormal sheaf of a restricted immersion -/

namespace Stacks.Immersion

variable {X X' : Scheme.{u}}

/-- **`ι_{i⁻¹V}^* 𝒞_{X/X'} ≅ 𝒞_{i ∣_ V}`.** For an immersion `i : X ⟶ X'` of schemes and an open
`V` of `X'`, the pullback of the conormal sheaf of `i` to `i⁻¹V` is the conormal sheaf of the
restricted immersion `i ∣_ V`.

It is the composite of `AlgebraicGeometry.RingedSpace.modulePullbackRestrictIso`, which
identifies a pullback along an open immersion with a restriction, with
`Stacks.Immersion.conormalSheafSelfRestrictIso` and `Stacks.Immersion.conormalSheafSelfIso`. By
`Stacks.Immersion.conormalSheafPullbackRestrictIso_hom` the composite is the map of
[Stacks Project, Tag 01R4] attached to the restriction square, so the isomorphism is
canonical. -/
def conormalSheafPullbackRestrictIso (i : X ⟶ X') [IsImmersion i] (V : X'.Opens) :
    (modulePullback (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj (immersionConormalSheaf i) ≅
      immersionConormalSheaf (i ∣_ V) :=
  (modulePullbackRestrictIso X.toSheafedSpace (i ⁻¹ᵁ V)).app (immersionConormalSheaf i) ≪≫
    conormalSheafSelfRestrictIso i V ≪≫ conormalSheafSelfIso (i ∣_ V)

/-- **`Stacks.Immersion.conormalSheafPullbackRestrictIso` is the canonical map of the restriction
square.** This is `Stacks.Immersion.modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso`,
read as a statement about the isomorphism assembled from its three factors. -/
theorem conormalSheafPullbackRestrictIso_hom (i : X ⟶ X') [IsImmersion i] (V : X'.Opens) :
    (conormalSheafPullbackRestrictIso i V).hom =
      immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
        (toShHom_square (morphismRestrict_ι i V)) :=
  modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso i V

end Stacks.Immersion

/-! ### The universal differential through the comparison of the two sheaves of differentials -/

namespace AlgebraicGeometry.Scheme.Hom

/-- **`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso` carries the universal relative derivation
to the universal differential on sections.** This is
`AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_postcomp_toCotangentSheaf` read at an
open `W` on a section. -/
theorem cotangentSheafIso_hom_val_app_d {Y S : Scheme.{u}} (p : Y ⟶ S) (W : Y.Opens)
    (y : Γ(Y, W)) :
    (cotangentSheafIso p).hom.val.app (op W) ((universalRelativeDerivation p).d y) =
      Stacks.Smooth.universalD p W y :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (universalRelativeDerivation_postcomp_toCotangentSheaf p) y

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Thickenings

/-! ### The conormal sheaf of a restricted thickening, in the scheme-module vocabulary -/

section Conormal

variable {X X' : Scheme.{u}}

/-- **`ι_{i⁻¹V}^* 𝒞_{X/X'} ≅ 𝒞_{i ∣_ V}` in the scheme-module vocabulary**, the conormal
counterpart of `Stacks.Smooth.restrictPullbackCotangentSheafIso`. -/
def pullbackConormalModulesIso (i : X ⟶ X') [IsImmersion i] (V : X'.Opens) :
    (Scheme.Modules.pullback (i ⁻¹ᵁ V).ι).obj (conormalModules i) ≅ conormalModules (i ∣_ V) :=
  Stacks.Modules.ofRingedSpaceIso (conormalSheafPullbackRestrictIso i V)

/-- `Stacks.Thickenings.pullbackConormalModulesIso` is the map of [Stacks Project, Tag 01R4] of
the restriction square. -/
theorem pullbackConormalModulesIso_hom (i : X ⟶ X') [IsImmersion i] (V : X'.Opens) :
    (pullbackConormalModulesIso i V).hom =
      Stacks.Modules.ofRingedSpaceHom (immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
        (toShHom_square (morphismRestrict_ι i V))) :=
  congrArg Stacks.Modules.ofRingedSpaceHom (conormalSheafPullbackRestrictIso_hom i V)

/-- **`𝒞_{X/X'}|_{i⁻¹V} ≅ 𝒞_{i ∣_ V}`.** The restriction of the conormal sheaf of `i` to the open
subscheme `i⁻¹V` is the conormal sheaf of the restricted thickening, by
`Stacks.Thickenings.pullbackConormalModulesIso` and the identification
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` of restriction along an open
immersion with pullback. -/
def restrictConormalModulesIso (i : X ⟶ X') [IsImmersion i] (V : X'.Opens) :
    (conormalModules i).restrict (i ⁻¹ᵁ V).ι ≅ conormalModules (i ∣_ V) :=
  (Scheme.Modules.restrictFunctorIsoPullback (i ⁻¹ᵁ V).ι).app (conormalModules i) ≪≫
    pullbackConormalModulesIso i V

end Conormal

/-! ### The derivation datum in the two spellings of the sheaf of differentials -/

section Datum

variable {X Y S : Scheme.{u}}

/-- A composite of morphisms of sheaves of modules, read on sections. -/
theorem comp_val_app_apply {Z : Scheme.{u}} {M N P : Z.Modules} (f : M ⟶ N)
    (g : N ⟶ P) (U : Z.Opens) (x : M.val.obj (op U)) :
    (f ≫ g).val.app (op U) x = g.val.app (op U) (f.val.app (op U) x) := rfl

/-- **A derivation datum on the `Stacks.Smooth.pullbackCotangentSheaf` track, read on the
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` track.** It is precomposition with the
pullback along `a` of `AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`. -/
def derivationDatumOfCotangent {a : X ⟶ Y} {p : Y ⟶ S} {N : X.Modules}
    (θ : Stacks.Smooth.pullbackCotangentSheaf p a ⟶ N) :
    (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials p) ⟶ N :=
  (Scheme.Modules.pullback a).map (Scheme.Hom.cotangentSheafIso p).hom ≫ θ

/-- **A derivation datum on the `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` track, read
on the `Stacks.Smooth.pullbackCotangentSheaf` track.** -/
def cotangentDatumOfDerivationDatum {a : X ⟶ Y} {p : Y ⟶ S} {N : X.Modules}
    (φ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials p) ⟶ N) :
    Stacks.Smooth.pullbackCotangentSheaf p a ⟶ N :=
  show (Scheme.Modules.pullback a).obj (Stacks.Smooth.cotangentSheaf p) ⟶ N from
    (Scheme.Modules.pullback a).map (Scheme.Hom.cotangentSheafIso p).inv ≫ φ

/-- `Stacks.Thickenings.derivationDatumOfCotangent` is a left inverse of
`Stacks.Thickenings.cotangentDatumOfDerivationDatum`. -/
theorem derivationDatumOfCotangent_cotangentDatum {a : X ⟶ Y} {p : Y ⟶ S} {N : X.Modules}
    (φ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials p) ⟶ N) :
    derivationDatumOfCotangent (cotangentDatumOfDerivationDatum φ) = φ :=
  Iso.hom_inv_id_map_assoc (Scheme.Hom.cotangentSheafIso p) (Scheme.Modules.pullback a) φ

/-- `Stacks.Thickenings.cotangentDatumOfDerivationDatum` is a left inverse of
`Stacks.Thickenings.derivationDatumOfCotangent`. -/
theorem cotangentDatum_derivationDatumOfCotangent {a : X ⟶ Y} {p : Y ⟶ S} {N : X.Modules}
    (θ : Stacks.Smooth.pullbackCotangentSheaf p a ⟶ N) :
    cotangentDatumOfDerivationDatum (derivationDatumOfCotangent θ) = θ :=
  Iso.inv_hom_id_map_assoc (Scheme.Hom.cotangentSheafIso p) (Scheme.Modules.pullback a) θ

/-- **The derivation data of the two tracks are the same data.** The two sheaves of relative
differentials of `p : Y ⟶ S` are canonically isomorphic by
`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`, so precomposition with its pullback along `a`
is a bijection on morphisms into any sheaf of modules on the source. -/
def derivationDatumEquiv (a : X ⟶ Y) (p : Y ⟶ S) (N : X.Modules) :
    (Stacks.Smooth.pullbackCotangentSheaf p a ⟶ N) ≃
      ((Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials p) ⟶ N) where
  toFun := derivationDatumOfCotangent
  invFun := cotangentDatumOfDerivationDatum
  left_inv := cotangentDatum_derivationDatumOfCotangent
  right_inv := derivationDatumOfCotangent_cotangentDatum

/-- **The transpose of a translated datum, on a universal differential.** The transpose along
`a^* ⊣ a_*` of `Stacks.Thickenings.derivationDatumOfCotangent θ`, applied to the universal
relative differential of a section of `𝒪_Y` over `W`, is `θ` applied on sections over `a⁻¹W` to
`Stacks.Smooth.pullbackD`.

This is the one computation of the file: the naturality of the adjunction in the source turns the
precomposition into the comparison of the two universal derivations, which is
`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso_hom_val_app_d`, and the transpose written through
the unit is `Stacks.Smooth.pullbackD_self`. -/
theorem homEquiv_derivationDatumOfCotangent_d {a : X ⟶ Y} {p : Y ⟶ S} {N : X.Modules}
    (θ : Stacks.Smooth.pullbackCotangentSheaf p a ⟶ N) (W : Y.Opens) (y : Γ(Y, W)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Scheme.Hom.relativeDifferentials p) N (derivationDatumOfCotangent θ)).val.app (op W))
        ((Scheme.Hom.universalRelativeDerivation p).d y)
      = θ.val.app (op (a ⁻¹ᵁ W)) (Stacks.Smooth.pullbackD p a W le_rfl y) := by
  have key : (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
        (Scheme.Hom.relativeDifferentials p) N (derivationDatumOfCotangent θ) =
      (Scheme.Hom.cotangentSheafIso p).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Stacks.Smooth.cotangentSheaf p) N θ :=
    Adjunction.homEquiv_naturality_left _ _ _
  have key2 : (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
        (Stacks.Smooth.cotangentSheaf p) N θ =
      (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          (Stacks.Smooth.cotangentSheaf p) ≫ (Scheme.Modules.pushforward a).map θ :=
    Adjunction.homEquiv_unit _ _ _ _
  refine Eq.trans (congrArg (fun φ : Scheme.Hom.relativeDifferentials p ⟶
      (Scheme.Modules.pushforward a).obj N =>
        φ.val.app (op W) ((Scheme.Hom.universalRelativeDerivation p).d y)) key) ?_
  refine Eq.trans (comp_val_app_apply (Scheme.Hom.cotangentSheafIso p).hom
      ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
        (Stacks.Smooth.cotangentSheaf p) N θ) W _) ?_
  refine Eq.trans (congrArg (fun z : Γ(Stacks.Smooth.cotangentSheaf p, W) =>
      ((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv
          (Stacks.Smooth.cotangentSheaf p) N θ).val.app (op W) z)
      (Scheme.Hom.cotangentSheafIso_hom_val_app_d p W y)) ?_
  refine Eq.trans (congrArg (fun φ : Stacks.Smooth.cotangentSheaf p ⟶
      (Scheme.Modules.pushforward a).obj N =>
        φ.val.app (op W) (Stacks.Smooth.universalD p W y)) key2) ?_
  refine Eq.trans (comp_val_app_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        (Stacks.Smooth.cotangentSheaf p)) ((Scheme.Modules.pushforward a).map θ) W _) ?_
  exact congrArg (fun z : Γ(Stacks.Smooth.pullbackCotangentSheaf p a, a ⁻¹ᵁ W) =>
    θ.val.app (op (a ⁻¹ᵁ W)) z) (Stacks.Smooth.pullbackD_self p a W y).symm

end Datum

/-! ### The bridge -/

section Bridge

variable {S T T' Y Y' : Scheme.{u}} {i : T ⟶ T'} {j : Y ⟶ Y'} {a : T ⟶ Y} {a' b' : T' ⟶ Y'}
  [IsClosedImmersion i] [IsImmersion j]

omit [IsImmersion j] in
/-- **The derivation of Equation [Stacks Project, Tag 04BV] attached to a translated datum, on
sections.** For `θ : a^*Ω_{Y/S} ⟶ 𝒞_{T/T'}` on the `Stacks.Smooth.pullbackCotangentSheaf` track,
the value of `D = θ ∘ d_{Y/S}` on a section `y` of `𝒪_Y` over `j⁻¹V` is `θ` applied to
`Stacks.Smooth.pullbackD`, read inside `𝒪_{T'}` by `Stacks.Thickenings.conormalSectionι`.

This is `Stacks.Thickenings.derivationSectionι_eq` composed with
`Stacks.Thickenings.homEquiv_derivationDatumOfCotangent_d`; it is what lets the
deformation-sheaf development recognise `Stacks.Thickenings.derivationSectionι` of a translated
datum as its own derivation on sections. -/
theorem derivationSectionι_derivationDatumOfCotangent (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (ca : i ≫ a' = a ≫ j)
    (θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
    (V : Y'.Opens) (y : Γ(Y, j ⁻¹ᵁ V)) :
    derivationSectionι hi q ca (derivationDatumOfCotangent θ) V y =
      conormalSectionι hi ca V
        (θ.val.app (op (a ⁻¹ᵁ (j ⁻¹ᵁ V)))
          (Stacks.Smooth.pullbackD (j ≫ q) a (j ⁻¹ᵁ V) le_rfl y)) :=
  (derivationSectionι_eq hi q ca (derivationDatumOfCotangent θ) V y).trans
    (congrArg (conormalSectionι hi ca V)
      (homEquiv_derivationDatumOfCotangent_d θ (j ⁻¹ᵁ V) y))

/-- **The unrestricted [Stacks Project, Tag 04FG] on the deformation-sheaf conormal track.** Two
lifts `a'`, `b'` of the same `a` inducing the same map of conormal sheaves differ by a derivation
datum `θ : a^*Ω_{Y/S} ⟶ 𝒞_{T/T'}` spelled with `Stacks.Smooth.pullbackCotangentSheaf` and
`Stacks.Thickenings.conormalModules`.

It is `Stacks.Thickenings.exists_isDerivationAction` read through
`Stacks.Thickenings.derivationDatumEquiv`. -/
@[ega "IV 16.5.14" "Transitivity"]
theorem exists_isDerivationAction_pullbackCotangentSheaf (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (hq : b' ≫ q = a' ≫ q) (ca : i ≫ a' = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC : immersionConormalSheafMap i j a a' (toShHom_square ca) =
      immersionConormalSheafMap i j a b' (toShHom_square cb)) :
    ∃ θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i,
      IsDerivationAction hi q ca cb (derivationDatumOfCotangent θ) := by
  exact (derivationDatumEquiv a (j ≫ q) _).symm.exists_congr_left.mp
    (exists_isDerivationAction q hi hq ca cb hC)

/-- **A derivation datum for the restricted thickening `i ∣_ V` is a morphism of the restrictions
to `i⁻¹V`.** Both sides of a datum for `i ∣_ V` are restrictions: `(ι ≫ a)^*Ω_{Y/S}` is the
restriction of `a^*Ω_{Y/S}` by `Stacks.Smooth.restrictPullbackCotangentSheafIso`, and
`𝒞_{i ∣_ V}` is the restriction of `𝒞_{T/T'}` by
`Stacks.Thickenings.restrictConormalModulesIso`. -/
def restrictDerivationDatumEquiv (i : T ⟶ T') [IsImmersion i] (a : T ⟶ Y) (p : Y ⟶ S)
    (V : T'.Opens) :
    ((Stacks.Smooth.pullbackCotangentSheaf p a).restrict (i ⁻¹ᵁ V).ι ⟶
        (conormalModules i).restrict (i ⁻¹ᵁ V).ι) ≃
      (Stacks.Smooth.pullbackCotangentSheaf p ((i ⁻¹ᵁ V).ι ≫ a) ⟶ conormalModules (i ∣_ V)) :=
  Iso.homCongr (Stacks.Smooth.restrictPullbackCotangentSheafIso p a (i ⁻¹ᵁ V))
    (restrictConormalModulesIso i V)

/-- **[Stacks Project, Tag 04FG] for two lifts over an open of `T'`.** Let `i : T ⟶ T'` be a
first-order thickening, `V` an open of `T'`, and `b₁`, `b₂ : V ⟶ Y'` two lifts of
`ι_{i⁻¹V} ≫ a` along `j` over `S` inducing the same map of conormal sheaves. Then `b₂` is
`θ ⬝ b₁` for a derivation datum `θ` over `i⁻¹V`, a morphism from the restriction of
`a^*Ω_{Y/S}` to the restriction of `𝒞_{T/T'}`.

This is the shape the simple-transitivity half of [Stacks Project, Tag 04FJ] needs: the group of
that tag acts on the lifts over `V`, so the datum it produces has to live over `V` and be
written with the sheaves on `T` rather than with the sheaves on `i⁻¹V`. It is
`Stacks.Thickenings.exists_isDerivationAction_pullbackCotangentSheaf` for the restricted
thickening `i ∣_ V`, whose defining ideal still squares to zero by
`Stacks.Thickenings.ker_pow_morphismRestrict_eq_bot`, read through
`Stacks.Thickenings.restrictDerivationDatumEquiv`. -/
theorem exists_isDerivationAction_morphismRestrict (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (V : T'.Opens) {b₁ b₂ : V.toScheme ⟶ Y'} (hq : b₂ ≫ q = b₁ ≫ q)
    (cb₁ : i ∣_ V ≫ b₁ = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (cb₂ : i ∣_ V ≫ b₂ = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (hC : immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b₁ (toShHom_square cb₁) =
      immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b₂ (toShHom_square cb₂)) :
    ∃ θ : (Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a).restrict (i ⁻¹ᵁ V).ι ⟶
        (conormalModules i).restrict (i ⁻¹ᵁ V).ι,
      IsDerivationAction (ker_pow_morphismRestrict_eq_bot i hi V) q cb₁ cb₂
        (derivationDatumOfCotangent
          (restrictDerivationDatumEquiv i a (j ≫ q) V θ)) := by
  exact (restrictDerivationDatumEquiv i a (j ≫ q) V).symm.exists_congr_left.mp
    (exists_isDerivationAction_pullbackCotangentSheaf
      (ker_pow_morphismRestrict_eq_bot i hi V) q hq cb₁ cb₂ hC)

/-- **[Stacks Project, Tag 04FG] for two lifts over an open of `T'`, with the datum a section of
the sheaf of homomorphisms.** `Stacks.Thickenings.exists_isDerivationAction_morphismRestrict`
read through `Stacks.Modules.overHomEquivRestrictHom`, so that the datum produced is a section
over `i⁻¹V` of `SheafHom_{𝒪_T}(a^*Ω_{Y/S}, 𝒞_{T/T'})` — the group of
[Stacks Project, Tag 04FJ] itself. -/
theorem exists_isDerivationAction_over (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (V : T'.Opens) {b₁ b₂ : V.toScheme ⟶ Y'} (hq : b₂ ≫ q = b₁ ≫ q)
    (cb₁ : i ∣_ V ≫ b₁ = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (cb₂ : i ∣_ V ≫ b₂ = ((i ⁻¹ᵁ V).ι ≫ a) ≫ j)
    (hC : immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b₁ (toShHom_square cb₁) =
      immersionConormalSheafMap (i ∣_ V) j ((i ⁻¹ᵁ V).ι ≫ a) b₂ (toShHom_square cb₂)) :
    ∃ θ : (Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a).over (i ⁻¹ᵁ V) ⟶
        (conormalModules i).over (i ⁻¹ᵁ V),
      IsDerivationAction (ker_pow_morphismRestrict_eq_bot i hi V) q cb₁ cb₂
        (derivationDatumOfCotangent (restrictDerivationDatumEquiv i a (j ≫ q) V
          (Stacks.Modules.overHomEquivRestrictHom _ _ _ θ))) := by
  exact (Stacks.Modules.overHomEquivRestrictHom _ _ _).symm.exists_congr_left.mp
    (exists_isDerivationAction_morphismRestrict hi q V hq cb₁ cb₂ hC)

end Bridge

end Stacks.Thickenings

end
