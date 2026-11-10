module

public import StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalAffineCotangent.Sections

/-!
# The conormal quotient map of one factorization determines that of any other

[Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) attaches to every factorization of
an immersion `i : Z ⟶ X` as a closed immersion `k : Z ⟶ U` into an open subscheme, followed by
the inclusion `U.ι`, a quotient map `Stacks.Conormal.conormalQuotientMap` from the ideal sheaf of
`k` to the direct image along `k` of the conormal sheaf. The tag's part (1) label
"compatibility of open factorizations" and the factorization quantifier inside its part (2)
subtype both ask that these maps agree. Nothing in the tree related two factorizations; this file
does.

The pivot is the coborder neighbourhood. `Stacks.Conormal.le_coborderRange_of_comp_eq` puts every
factorizing open below `i.coborderRange`, and `Stacks.Conormal.comp_homOfLE_eq_liftCoborder`
makes the factorizing morphism followed by that inclusion equal to `i.liftCoborder`. At the
coborder factorization the comparison isomorphism is `Iso.refl` — the tag's normalization clause,
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf_liftCoborder` — so the quotient map there is
the bare adjunction unit, and the whole comparison reduces to a statement about units.

## Main results

* `Stacks.Conormal.OpenFactorizations.unit_comp_map_compIso_comp_map`: the unit of
  `(f' ≫ f)^* ⊣ (f' ≫ f)_*` against the pseudofunctoriality isomorphism followed by the inverse
  image of an arbitrary morphism out of `f^* M`. This generalizes
  `Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_comp_map`, which covers only
  a morphism that is itself an inverse image, and the generalization is what lets the
  ideal-sheaf restriction isomorphism — not an inverse image of anything — travel through.
* `Stacks.Conormal.OpenFactorizations.idealRestrictHom`: the comparison `I(k ≫ j) ⟶ j_* I(k)`
  for an open immersion `j`, with
  `Stacks.Conormal.OpenFactorizations.idealRestrictHom_comp_ι` describing it through the
  inclusions of the two ideal sheaves into the two structure sheaves. Since those inclusions are
  monomorphisms and `Stacks.Conormal.Locality.idealSheaf_section_injective` makes them injective
  on sections, that description pins the comparison down on sections.
* `Stacks.Conormal.OpenFactorizations.unit_eq_idealRestrictHom_comp`: **the sheaf-level
  identity.** The unit at the ideal sheaf of `k ≫ j` is `idealRestrictHom` followed by the direct
  image along `j` of the quotient map of the factorization `k`.
* `Stacks.Conormal.OpenFactorizations.generator_eq_of_compEq`: **the same identity on sections**,
  with the composite `k ≫ j` presented as a separately named morphism together with an equation,
  which is the form a factorization statement supplies.
* `Stacks.Conormal.OpenFactorizations.conormalQuotientMap_liftCoborder`: at the defining
  factorization the quotient map of Tag 01R3 is the adjunction unit itself.
* `Stacks.Conormal.OpenFactorizations.conormalQuotientMap_eq_of_factorization`: **the tagged
  statement.** For any closed-immersion factorization `(U, k)` of `i` and any open `O` of
  `i.coborderRange`, the quotient generator computed at the coborder factorization and the one
  computed at `(U, k)` agree after restriction to a common open of `Z`, provided the two sections
  of the two ideal sheaves correspond under `idealRestrictHom`.
* `Stacks.Conormal.OpenFactorizations.pullbackIdealSheafCompIso_hom_unit` and
  `pullbackIdealSheafIsoOfCompEq_hom_unit`: **the comparison read forwards on a unit generator**,
  for the literal composite and for the composite presented by an equation. The identity above is
  stated with the comparison's *inverse* applied to the generator of the factorization; these are
  the same identity in the direction in which the comparison is consumed, the chart layer reading
  it out of the conormal sheaf rather than into it.
* `Stacks.Conormal.OpenFactorizations.pullbackIdealSheafIsoOfCompEq_trans_isoOfIsoSource_hom_unit`:
  the previous one composed with
  `Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource`. These
  are the two factors of `Stacks.Conormal.restrictConormalIsoOfOpenFactor` — the target half of
  the conormal comparison of [Stacks, Tag 0B3V] clause 3 over a chart — that had no description on
  sections; the other two have `Stacks.Conormal.Locality.conormalRestrictIso_unit_app` and, via
  `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, `pullbackIdealSheafIsoOfCompEq_hom_unit`
  itself.

## Why the sheaf-level identity cannot be stated with a named composite

`unit_eq_idealRestrictHom_comp` is stated for the literal composite `k ≫ j`, and
`generator_eq_of_compEq` — which takes `L` with `hL : k ≫ j = L` — is stated **on sections**
rather than as an equality of morphisms of sheaves. That is forced, not a preference. The
right-hand side of the sheaf-level identity has target `j_* (k_* N)` and the left-hand side has
target `L_* N`; these agree by `Stacks.PullbackPseudofunctor.modulePushforward_comp` only once
`L` is `k ≫ j`, so with `L` a variable the two sides have propositionally — not definitionally —
equal types and the statement does not elaborate. On sections the mismatch becomes an equality of
*opens*, `L ⁻¹ᵁ O` against `k ⁻¹ᵁ (j ⁻¹ᵁ O)`, and once both sides are restricted to a common open
`T` of `Z` the types coincide outright. So `generator_eq_of_compEq` takes two containments, one
for each spelling, and `subst` collapses them in the proof.

## Transparency and heartbeat notes

Two measurements, both costing a rewrite each:

* The collapse `(k ≫ j)_* = j_* ∘ k_*` holds by `rfl`, but a `rw` whose motive leaves the
  pushed-forward morphism as a metavariable, and an `exact` that has to check the collapse while
  also unifying a functor, each exhaust the default heartbeat budget. The working form is a
  `rfl` lemma stated at the *one specific morphism* it is used on
  (`pushforward_comp_map_compIso_inv`) together with the reassociation done by
  `comp_map_reassoc`, which is stated for a variable functor so that there is nothing to unfold.
  No heartbeat limit is raised anywhere in this file; the restructuring is the whole remedy.
* `(SheafOfModules.unit _)`-valued statements must stay in a single spelling. Mixing
  `AlgebraicGeometry.Scheme.Modules.pushforward` with
  `RingedSpaceModuleAdjunction.modulePushforward` makes `rw` fail with `V.Modules` against
  `SheafOfModules (structureSheafRing V.toSheafedSpace)`; the two are definitionally equal but
  not at the elaborator's `implicit` transparency. `unit_comp_map_pullbackUnitIso` is the
  one-line term-mode bridge, and term mode is where the two spellings may meet.

## Universe situation

A single universe `u`, as in the tagged statements, except for `comp_map_reassoc`, which is a
statement about
arbitrary categories.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.PullbackPseudofunctor

universe v₁ u₁ v₂ u₂ u

namespace Stacks.Conormal.OpenFactorizations

/-! ### A reassociation helper -/

/-- Reassociation across a functor: moving one factor from inside `F.map` to the other side.

Stated for a variable functor on purpose. At the concrete functors of this file — direct images
of sheaves of modules along composites of morphisms of ringed spaces — unifying the two spellings
of a composite pushforward inside `exact` exhausts the default heartbeat budget; with `F` a
variable there is nothing to unfold. -/
theorem comp_map_reassoc {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {W : D} {A B B' E : C} (a : W ⟶ F.obj A) (x : A ⟶ B) (y : B ⟶ B')
    (z : B' ⟶ E) :
    (a ≫ F.map (x ≫ y)) ≫ F.map z = (a ≫ F.map x) ≫ F.map (y ≫ z) := by
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Category.assoc]

/-! ### The unit through the pseudofunctoriality isomorphism -/

/-- **The unit of `(f' ≫ f)^* ⊣ (f' ≫ f)_*` against the pseudofunctoriality isomorphism**,
followed by the inverse image along `f'` of an arbitrary `φ : f^* M ⟶ P`.

`Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_comp_map` is the case where
`φ` is itself an inverse image; the ideal-sheaf restriction isomorphism of an open immersion is
not, which is why the general form is needed here. Both sides are read as the unit of
`Stacks.PullbackPseudofunctor.compAdjunction`, whose *type* performs the collapse of the
composite pushforward, after which the claim is naturality of the inner unit. -/
theorem unit_comp_map_compIso_comp_map {X X' X'' : RingedSpace.{u, u}}
    (f : X' ⟶ X) (f' : X'' ⟶ X')
    (M : SheafOfModules.{u} (structureSheafRing X)) (P : SheafOfModules.{u} (structureSheafRing X'))
    (φ : (modulePullback f).obj M ⟶ P) :
    (modulePullbackPushforwardAdjunction (f' ≫ f)).unit.app M ≫
        (modulePushforward (f' ≫ f)).map
          ((modulePullbackCompIso f f').hom.app M ≫ (modulePullback f').map φ) =
      (modulePullbackPushforwardAdjunction f).unit.app M ≫
        (modulePushforward f).map
          (φ ≫ (modulePullbackPushforwardAdjunction f').unit.app P) := by
  have nat : φ ≫ (modulePullbackPushforwardAdjunction f').unit.app P =
      (modulePullbackPushforwardAdjunction f').unit.app ((modulePullback f).obj M) ≫
        (modulePushforward f').map ((modulePullback f').map φ) :=
    (modulePullbackPushforwardAdjunction f').unit.naturality φ
  have h1 : (modulePullbackPushforwardAdjunction (f' ≫ f)).unit.app M ≫
      (modulePushforward (f' ≫ f)).map
        ((modulePullbackCompIso f f').hom.app M ≫ (modulePullback f').map φ) =
      (compAdjunction f f').unit.app M ≫
        (modulePushforward (f' ≫ f)).map ((modulePullback f').map φ) := by
    rw [Functor.map_comp, ← Category.assoc, unit_comp_map_modulePullbackCompIso_hom_app,
      ← compAdjunction_unit_app]
  have h2 : (modulePullbackPushforwardAdjunction f).unit.app M ≫
      (modulePushforward f).map
        (φ ≫ (modulePullbackPushforwardAdjunction f').unit.app P) =
      (compAdjunction f f').unit.app M ≫
        (modulePushforward (f' ≫ f)).map ((modulePullback f').map φ) := by
    rw [nat, Functor.map_comp, ← Category.assoc, ← compAdjunction_unit_app]
    rfl
  exact h1.trans h2.symm

/-! ### Restriction of the ideal sheaf along an open immersion, as a morphism -/

variable {Z U V : Scheme.{u}} (k : Z ⟶ U) (j : U ⟶ V) [IsOpenImmersion j]

/-- The comparison `I(k ≫ j) ⟶ j_* I(k)`: the unit of `j^* ⊣ j_*` followed by the direct image
along `j` of `Stacks.IdealSheafRestrict.pullbackIdealSheafIso`. -/
noncomputable def idealRestrictHom :
    Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom ⟶
      (modulePushforward j.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) :=
  (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).unit.app
      (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom) ≫
    (modulePushforward j.toLRSHom.toShHom).map
      (Stacks.IdealSheafRestrict.pullbackIdealSheafIso j k).hom

/-- `Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso` in the vocabulary of the tagged
statements. The two
spellings of the category of modules on a scheme are definitionally equal but not at the
elaborator's `implicit` transparency, so the bridge is a term-mode declaration of its own. -/
theorem unit_comp_map_pullbackUnitIso :
    (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).unit.app
        (SheafOfModules.unit (structureSheafRing V.toSheafedSpace)) ≫
      (modulePushforward j.toLRSHom.toShHom).map
        (Stacks.IdealSheafRestrict.pullbackUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom) :=
  Stacks.Conormal.unit_comp_map_pullbackUnitModuleIso j

/-- **`idealRestrictHom` through the inclusions of the ideal sheaves into the structure
sheaves**, the right-hand vertical map being the structure-sheaf map of `j`.

The inclusions are `CategoryTheory.Limits.kernel.ι`, hence monomorphisms, hence injective on
sections over every open by `Stacks.Conormal.Locality.idealSheaf_section_injective`. So this
determines `idealRestrictHom` on sections: it sends a section of `I(k ≫ j)` over `O` to the
unique section of `I(k)` over `j ⁻¹ᵁ O` with the restricted image in the structure sheaf. -/
theorem idealRestrictHom_comp_ι :
    idealRestrictHom k j ≫
        (modulePushforward j.toLRSHom.toShHom).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom k.toLRSHom.toShHom))) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom (k ≫ j).toLRSHom.toShHom)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom) := by
  have nat : kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (k ≫ j).toLRSHom.toShHom)) ≫
      (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).unit.app
        (SheafOfModules.unit (structureSheafRing V.toSheafedSpace)) =
      (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom) ≫
        (modulePushforward j.toLRSHom.toShHom).map
          ((modulePullback j.toLRSHom.toShHom).map
            (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom (k ≫ j).toLRSHom.toShHom)))) :=
    (modulePullbackPushforwardAdjunction j.toLRSHom.toShHom).unit.naturality _
  rw [idealRestrictHom, Category.assoc, ← Functor.map_comp,
    Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι, Functor.map_comp,
    ← Category.assoc, ← nat, Category.assoc, unit_comp_map_pullbackUnitIso]
  rfl

/-! ### The sheaf-level factorization identity -/

/-- The two factors of `Stacks.Conormal.pullbackIdealSheafCompIso`, named so that the composite
appearing in `unit_comp_map_compIso_comp_map` can be rewritten into it. -/
theorem pullbackIdealSheafCompIso_hom :
    (Stacks.Conormal.pullbackIdealSheafCompIso k j).hom =
      (modulePullbackCompIso j.toLRSHom.toShHom k.toLRSHom.toShHom).hom.app
          (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom) ≫
        (modulePullback k.toLRSHom.toShHom).map
          (Stacks.IdealSheafRestrict.pullbackIdealSheafIso j k).hom :=
  rfl

/-- The collapse `(k ≫ j)_* = j_* ∘ k_*`, stated at the one morphism it is applied to. Left as a
metavariable the same `rfl` exhausts the default heartbeat budget; see the module docstring. -/
theorem pushforward_comp_map_compIso_inv :
    (modulePushforward (k.toLRSHom.toShHom ≫ j.toLRSHom.toShHom)).map
        (Stacks.Conormal.pullbackIdealSheafCompIso k j).inv =
      (modulePushforward j.toLRSHom.toShHom).map
        ((modulePushforward k.toLRSHom.toShHom).map
          (Stacks.Conormal.pullbackIdealSheafCompIso k j).inv) :=
  rfl

/-- **The sheaf-level factorization identity.** For a closed-immersion-free `k : Z ⟶ U` and an
open immersion `j : U ⟶ V`, the unit of `(k ≫ j)^* ⊣ (k ≫ j)_*` at the ideal sheaf of `k ≫ j`
is `idealRestrictHom` followed by the direct image along `j` of the quotient map of the
factorization `k` — that is, of the unit at `I(k)` read through
`Stacks.Conormal.pullbackIdealSheafCompIso`.

No hypothesis on `k` is used: not that it is a closed immersion, not that `k ≫ j` is an
immersion. Only `j` is assumed an open immersion, and only because the ideal-sheaf restriction
isomorphism needs it. -/
theorem unit_eq_idealRestrictHom_comp :
    (modulePullbackPushforwardAdjunction (k ≫ j).toLRSHom.toShHom).unit.app
        (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom) =
      idealRestrictHom k j ≫
        (modulePushforward j.toLRSHom.toShHom).map
          ((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).unit.app
              (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) ≫
            (modulePushforward k.toLRSHom.toShHom).map
              (Stacks.Conormal.pullbackIdealSheafCompIso k j).inv) := by
  have hU := unit_comp_map_compIso_comp_map j.toLRSHom.toShHom k.toLRSHom.toShHom
    (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom)
    (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom)
    (Stacks.IdealSheafRestrict.pullbackIdealSheafIso j k).hom
  rw [← pullbackIdealSheafCompIso_hom] at hU
  have h := (Iso.eq_comp_inv ((modulePushforward
      (k.toLRSHom.toShHom ≫ j.toLRSHom.toShHom)).mapIso
      (Stacks.Conormal.pullbackIdealSheafCompIso k j))).mpr hU
  rw [Functor.mapIso_inv] at h
  refine h.trans ?_
  rw [pushforward_comp_map_compIso_inv, idealRestrictHom]
  exact comp_map_reassoc (modulePushforward j.toLRSHom.toShHom) _ _ _ _

/-! ### The factorization presented by an equation -/

/-- `idealRestrictHom` with the composite `k ≫ j` presented as a separately named morphism `L`
together with the equation `k ≫ j = L`. This is the form a factorization statement supplies:
the canonical closed immersion into the coborder neighbourhood is given as `i.liftCoborder` and
the equation is a theorem about it. -/
noncomputable def idealRestrictHomOfCompEq (L : Z ⟶ V) (hL : k ≫ j = L) :
    Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom ⟶
      (modulePushforward j.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) := by
  subst hL
  exact idealRestrictHom k j

/-- `idealRestrictHom_comp_ι` for `idealRestrictHomOfCompEq`. -/
theorem idealRestrictHomOfCompEq_comp_ι (L : Z ⟶ V) (hL : k ≫ j = L) :
    idealRestrictHomOfCompEq k j L hL ≫
        (modulePushforward j.toLRSHom.toShHom).map
          (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom k.toLRSHom.toShHom))) =
      kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom L.toLRSHom.toShHom)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom) := by
  subst hL
  exact idealRestrictHom_comp_ι k j

/-! ### The section-level factorization identity -/

/-- A direct image of a morphism acts on sections over `O` as the morphism itself on sections
over the preimage of `O`. -/
theorem modulePushforward_map_val_app {A B : Scheme.{u}} (g : A ⟶ B)
    {M N : SheafOfModules.{u} (structureSheafRing A.toLocallyRingedSpace.toRingedSpace)} (ψ : M ⟶ N)
    (O : B.Opens) (t : ((modulePushforward g.toLRSHom.toShHom).obj M).val.obj (.op O)) :
    ((modulePushforward g.toLRSHom.toShHom).map ψ).val.app (.op O) t =
      ψ.val.app (.op (g ⁻¹ᵁ O)) t :=
  rfl

/-- **The factorization identity on sections, with the composite presented by an equation.**
Let `k ≫ j = L`, let `O` be an open of `V`, and let `y` over `O` and `x` over `j ⁻¹ᵁ O` be
sections of the two ideal sheaves corresponding under `idealRestrictHomOfCompEq`. Then the image
of `y` under the unit at `I(L)` and the image of `x` under the quotient map of the factorization
`k` agree after restriction to any open `T` of `Z` below both preimages.

The two containments `hT` and `hT'` are the same inequality in two spellings — `L ⁻¹ᵁ O` and
`k ⁻¹ᵁ (j ⁻¹ᵁ O)` — and both are needed because with `L` a variable only one of them types each
side; see the module docstring. -/
theorem generator_eq_of_compEq (L : Z ⟶ V) (hL : k ≫ j = L)
    (O : V.Opens) (T : Z.Opens) (hT : T ≤ L ⁻¹ᵁ O) (hT' : T ≤ k ⁻¹ᵁ (j ⁻¹ᵁ O))
    (y : (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom).val.obj (.op O))
    (x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op (j ⁻¹ᵁ O)))
    (hxy : (idealRestrictHomOfCompEq k j L hL).val.app (.op O) y = x) :
    ((modulePullback L.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom)).val.map (homOfLE hT).op
        (((modulePullbackPushforwardAdjunction L.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom)).val.app (.op O) y) =
      ((modulePullback L.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom)).val.map (homOfLE hT').op
        (((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).unit.app
              (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) ≫
            (modulePushforward k.toLRSHom.toShHom).map
              (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq k j L hL).inv).val.app
          (.op (j ⁻¹ᵁ O)) x) := by
  subst hL
  subst hxy
  rw [unit_eq_idealRestrictHom_comp k j]
  rfl

/-! ### The comparison isomorphism itself, on a unit generator -/

/-- **The generator formula for `Stacks.Conormal.pullbackIdealSheafCompIso`.** The comparison
carries the unit generator of `(k ≫ j)^* I(k ≫ j)` named by a section `y` of `I(k ≫ j)` over an
open `O` of `V` to the unit generator of `k^* I(k)` named by the corresponding section of `I(k)`
over `j ⁻¹ᵁ O`, which is `idealRestrictHom` of `y` and which `idealRestrictHom_comp_ι` pins down.

`generator_eq_of_compEq` states the same identity with the comparison on the other side, as the
inverse applied to the right-hand generator; this is the direction in which the comparison is
*consumed*, the chart layer reading it forwards out of the conormal sheaf. No transport appears:
the composite is literal, so `(k ≫ j) ⁻¹ᵁ O` and `k ⁻¹ᵁ (j ⁻¹ᵁ O)` are the same open.

The route is `unit_eq_idealRestrictHom_comp` read on sections over `O` — where the two collapses
it needs, a composite of morphisms of sheaves on sections and a direct image of a morphism on
sections, both hold by `rfl` — followed by cancelling the comparison against its inverse. -/
theorem pullbackIdealSheafCompIso_hom_unit (O : V.Opens)
    (y : (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom).val.obj (.op O)) :
    (Stacks.Conormal.pullbackIdealSheafCompIso k j).hom.val.app (.op (k ⁻¹ᵁ (j ⁻¹ᵁ O)))
        (((modulePullbackPushforwardAdjunction (k ≫ j).toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf (k ≫ j).toLRSHom.toShHom)).val.app (.op O) y) =
      ((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom)).val.app (.op (j ⁻¹ᵁ O))
        ((idealRestrictHom k j).val.app (.op O) y) := by
  refine Eq.trans (congrArg ((Stacks.Conormal.pullbackIdealSheafCompIso k j).hom.val.app
    (.op (k ⁻¹ᵁ (j ⁻¹ᵁ O))))
    (congrArg (fun ψ => ModuleCat.Hom.hom ψ y)
      (congr($(unit_eq_idealRestrictHom_comp k j).val.app (.op O))))) ?_
  exact congrArg (fun ψ => ModuleCat.Hom.hom ψ _)
    (congr($((Stacks.Conormal.pullbackIdealSheafCompIso k j).inv_hom_id).val.app
      (.op (k ⁻¹ᵁ (j ⁻¹ᵁ O)))))

/-- **The generator formula for `Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`**, that is, with
the composite `k ≫ j` presented as a separately named morphism `L` together with the equation
`k ≫ j = L`. This is the form a factorization statement supplies, and the form in which the
comparison is consumed: `Stacks.Conormal.restrictConormalIsoOfOpenFactor` cancels the open
immersion `j` off the target with exactly this isomorphism.

The inclusion of opens `ρ` is a **variable**: `L ⁻¹ᵁ O` and `k ⁻¹ᵁ (j ⁻¹ᵁ O)` are equal by the
equation `hL`, but with `L` a variable they are not the same open, so the two sides of the
identity live over the two spellings and one restriction map is unavoidable. Morphisms between
opens are unique, so taking it as a variable costs the consumer nothing and spares it exhibiting
the transport; the device is that of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.tailIso_hom_val_app_of`.

`subst` on `hL` reduces the statement to `pullbackIdealSheafCompIso_hom_unit`, the restriction map
then being the identity. -/
theorem pullbackIdealSheafIsoOfCompEq_hom_unit (L : Z ⟶ V) (hL : k ≫ j = L) (O : V.Opens)
    (ρ : L ⁻¹ᵁ O ⟶ k ⁻¹ᵁ (j ⁻¹ᵁ O))
    (y : (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom).val.obj (.op O))
    (x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj (.op (j ⁻¹ᵁ O)))
    (hxy : (idealRestrictHomOfCompEq k j L hL).val.app (.op O) y = x) :
    (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq k j L hL).hom.val.app (.op (L ⁻¹ᵁ O))
        (((modulePullbackPushforwardAdjunction L.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom)).val.app (.op O) y) =
      ((modulePullback k.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom)).val.map ρ.op
        (((modulePullbackPushforwardAdjunction k.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom)).val.app (.op (j ⁻¹ᵁ O))
          x) := by
  subst hL
  subst hxy
  obtain rfl : ρ = 𝟙 ((k ≫ j) ⁻¹ᵁ O) := Subsingleton.elim _ _
  refine Eq.trans (pullbackIdealSheafCompIso_hom_unit k j O y) ?_
  exact (congrArg (fun ψ => ModuleCat.Hom.hom ψ _)
    (((modulePullback k.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom)).val.map_id
      (.op ((k ≫ j) ⁻¹ᵁ O)))).symm

/-! ### The comparison of open factorizations of Tag 01R3 -/

variable {X : Scheme.{u}} (i : Z ⟶ X)

/-- **At the defining factorization the quotient map is the adjunction unit.** The
comparison isomorphism there is `Iso.refl` by the tag's normalization clause,
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf_liftCoborder`, so the second factor of
`Stacks.Conormal.conormalQuotientMap` is the identity. -/
theorem conormalQuotientMap_liftCoborder [IsImmersion i] :
    Stacks.Conormal.conormalQuotientMap i i.coborderRange i.liftCoborder i.liftCoborder_ι =
      (modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
        (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom) := by
  rw [Stacks.Conormal.conormalQuotientMap,
    Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf_liftCoborder, Iso.refl_inv,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- **The quotient generator of an arbitrary factorization is the one computed at the coborder
neighbourhood.** For an immersion `i : Z ⟶ X`, a closed-immersion factorization
`k : Z ⟶ W.toScheme` of it, an open `O` of `i.coborderRange` and corresponding sections `y` of
the ideal sheaf of `i.liftCoborder` over `O` and `x` of the ideal sheaf of `k` over the preimage
of `O`, the two quotient generators agree after restriction to any open `T` of `Z` below both
preimages.

This is `generator_eq_of_compEq` at `L = i.liftCoborder`, with
`Stacks.Conormal.le_coborderRange_of_comp_eq` supplying the open immersion and
`Stacks.Conormal.comp_homOfLE_eq_liftCoborder` the equation, and
`conormalQuotientMap_liftCoborder` identifying the left-hand side. Nothing beyond the tag's
hypotheses is used. -/
theorem conormalQuotientMap_eq_of_factorization [IsImmersion i]
    (W : X.Opens) (k : Z ⟶ W.toScheme) [IsClosedImmersion k] (hfac : k ≫ W.ι = i)
    (O : i.coborderRange.toScheme.Opens) (T : Z.Opens)
    (hT : T ≤ i.liftCoborder ⁻¹ᵁ O)
    (hT' : T ≤ k ⁻¹ᵁ (X.homOfLE (Stacks.Conormal.le_coborderRange_of_comp_eq i W k hfac) ⁻¹ᵁ O))
    (y : (Stacks.ClosedImmersion.idealSheaf i.liftCoborder.toLRSHom.toShHom).val.obj (.op O))
    (x : (Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom).val.obj
      (.op (X.homOfLE (Stacks.Conormal.le_coborderRange_of_comp_eq i W k hfac) ⁻¹ᵁ O)))
    (hxy : (idealRestrictHomOfCompEq k
        (X.homOfLE (Stacks.Conormal.le_coborderRange_of_comp_eq i W k hfac)) i.liftCoborder
        (Stacks.Conormal.comp_homOfLE_eq_liftCoborder i W k hfac)).val.app (.op O) y = x) :
    (Stacks.Conormal.conormalSheaf i).val.map (homOfLE hT).op
        ((Stacks.Conormal.conormalQuotientMap i i.coborderRange i.liftCoborder
          i.liftCoborder_ι).val.app (.op O) y) =
      (Stacks.Conormal.conormalSheaf i).val.map (homOfLE hT').op
        ((Stacks.Conormal.conormalQuotientMap i W k hfac).val.app
          (.op (X.homOfLE (Stacks.Conormal.le_coborderRange_of_comp_eq i W k hfac) ⁻¹ᵁ O)) x) := by
  rw [conormalQuotientMap_liftCoborder, Stacks.Conormal.conormalQuotientMap,
    Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf]
  exact generator_eq_of_compEq k _ _ _ O T hT hT' y x hxy

/-! ### The two transports of `restrictConormalIsoOfOpenFactor`, composed -/

section Composite

open Stacks.Conormal.AffineCotangent.SourceTransport

variable {A' A B C : Scheme.{u}} (α : A' ≅ A) (g : A ⟶ B) (m : B ⟶ C) [IsOpenImmersion m]

/-- **The generator formula for the two transports of
`Stacks.Conormal.restrictConormalIsoOfOpenFactor`, composed.** For a factorization
`(α.hom ≫ g) ≫ m = L` with `α` an isomorphism and `m` an open immersion, the composite
`L^* I(L) ≅ α.hom^* g^* I(g)` of
`Stacks.Conormal.pullbackIdealSheafIsoOfCompEq`, which cancels the open immersion off the target,
with
`Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSource`, which
splits the isomorphism off the source, carries the unit generator of `L^* I(L)` named by a section
`y` of `I(L)` over an open `O` of `C` to the iterated unit generator of `α.hom^* g^* I(g)` named
by the image under `idealSheafIsoOfIsoSource` of the corresponding section `x` of
`I(α.hom ≫ g)` over `m ⁻¹ᵁ O`.

These are exactly the two factors of `Stacks.Conormal.restrictConormalIsoOfOpenFactor` that had no
description on sections; the other two are
`Stacks.Conormal.Locality.conormalRestrictIso_unit_app` and — through
`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, which is
`pullbackIdealSheafIsoOfCompEq` at the coborder factorization — `generator_eq_of_compEq`.

Three steps: `pullbackIdealSheafIsoOfCompEq_hom_unit` for the first factor, naturality of the
second in the open to move it past the restriction map the first leaves behind, and
`modulePullbackIdealSheafIsoOfIsoSource_unit_app` for the second factor. The inclusion of opens
`ρ` is a variable for the reason recorded at `pullbackIdealSheafIsoOfCompEq_hom_unit`. -/
theorem pullbackIdealSheafIsoOfCompEq_trans_isoOfIsoSource_hom_unit (L : A' ⟶ C)
    (hL : (α.hom ≫ g) ≫ m = L) (O : C.Opens)
    (ρ : L ⁻¹ᵁ O ⟶ (α.hom ≫ g) ⁻¹ᵁ (m ⁻¹ᵁ O))
    (y : (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom).val.obj (.op O))
    (x : (Stacks.ClosedImmersion.idealSheaf (α.hom ≫ g).toLRSHom.toShHom).val.obj
      (.op (m ⁻¹ᵁ O)))
    (hxy : (idealRestrictHomOfCompEq (α.hom ≫ g) m L hL).val.app (.op O) y = x) :
    (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq (α.hom ≫ g) m L hL ≪≫
          modulePullbackIdealSheafIsoOfIsoSource α g).hom.val.app (.op (L ⁻¹ᵁ O))
        (((modulePullbackPushforwardAdjunction L.toLRSHom.toShHom).unit.app
            (Stacks.ClosedImmersion.idealSheaf L.toLRSHom.toShHom)).val.app (.op O) y) =
      ((modulePullback α.hom.toLRSHom.toShHom).obj
          ((modulePullback g.toLRSHom.toShHom).obj
            (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val.map ρ.op
        (((modulePullbackPushforwardAdjunction α.hom.toLRSHom.toShHom).unit.app
              ((modulePullback g.toLRSHom.toShHom).obj
                (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val.app
            (.op (g ⁻¹ᵁ (m ⁻¹ᵁ O)))
          (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
                (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom)).val.app (.op (m ⁻¹ᵁ O))
            ((idealSheafIsoOfIsoSource α g).hom.val.app (.op (m ⁻¹ᵁ O)) x))) := by
  refine Eq.trans (congrArg
    ((modulePullbackIdealSheafIsoOfIsoSource α g).hom.val.app (.op (L ⁻¹ᵁ O)))
    (pullbackIdealSheafIsoOfCompEq_hom_unit (α.hom ≫ g) m L hL O ρ y x hxy)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (modulePullbackIdealSheafIsoOfIsoSource α g).hom.val ρ.op _) ?_
  exact congrArg (fun z => ((modulePullback α.hom.toLRSHom.toShHom).obj
      ((modulePullback g.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))).val.map ρ.op z)
    (modulePullbackIdealSheafIsoOfIsoSource_unit_app α g (m ⁻¹ᵁ O) x)

end Composite

end Stacks.Conormal.OpenFactorizations

end
