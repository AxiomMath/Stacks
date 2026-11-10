module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison

/-!
# The comparison isomorphism is the identity at the defining factorization

`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf` attaches, to every factorization of an
immersion `i : Z ⟶ X` as a closed immersion `i' : Z ⟶ U` followed by the inclusion of an open
`U ≤ X`, an isomorphism from the conormal sheaf of `i` to the module pullback along `i'` of the
ideal sheaf of `i'`. At the *defining* factorization — `U = i.coborderRange`,
`i' = i.liftCoborder` — the conormal sheaf is by definition the right-hand side, and this file
proves that the isomorphism is then `Iso.refl`, with no transport.

## Main results

* `Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf_liftCoborder`: the normalization itself.
* `Stacks.Conormal.modulePullbackCompIso_hom_app_id`: **unitality of the pseudofunctoriality
  isomorphism** of `StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic`, whose module
  docstring records it as missing. For a morphism of ringed spaces `f' : X' ⟶ X`, the component
  of `modulePullbackCompIso (𝟙 X) f'` at `M` is `f'^*` applied to the unit of the identity
  adjunction at `M`.
* `Stacks.Conormal.pullbackIdealSheafCompIso_id` and
  `Stacks.Conormal.idUnit_comp_pullbackIdealSheafIso`: **unitality of the restriction
  isomorphism of ideal sheaves**, also recorded as missing there.

## Route

`AlgebraicGeometry.Scheme.homOfLE le_rfl` is the identity morphism (`Scheme.homOfLE_rfl`), not
definitionally but by a proof; and `IsOpenImmersion` and `≤` are both `Prop`s, so substituting
that proof carries the open-immersion instance with it. After the substitution the statement is
about the literal identity, where three further facts hold **definitionally** and so cost
nothing: `k ≫ 𝟙 U = k`, `modulePushforward (𝟙 X) = 𝟭` and
`structureSheafHom (k ≫ 𝟙 U) = structureSheafHom k`. In particular both sides of the
normalization clause already have the same type and `Iso.refl` needs no `eqToIso`.

What is left is to collapse the two factors of `Stacks.Conormal.pullbackIdealSheafCompIso`.

* The first factor is the pseudofunctoriality isomorphism. Both it and the candidate
  `f'^* (unit)` transpose, under the adjunction for `f' ≫ 𝟙 X`, to the same composite of units:
  for the isomorphism by `unit_comp_map_modulePullbackCompIso_hom_app`, and for the candidate by
  naturality of the unit. A morphism out of a pullback is determined by its transpose.
* The second factor is the restriction isomorphism of ideal sheaves. Its target is a kernel and
  `Stacks.IdealSheafRestrict.pullbackIdealSheafIso_hom_comp_ι` describes it through the
  monomorphism `kernel.ι`, so cancelling that monomorphism reduces the claim to the same
  statement for the structure sheaf, and naturality of the unit moves the unit past `kernel.ι`.
* For the structure sheaf the statement is checked on sections. Mathlib's
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` transposes the unit of the
  pullback adjunction into the unit of `Scheme.Modules.restrictAdjunction`, whose components are
  plain restriction maps, and `Scheme.Modules.restrictUnitIso` is `Scheme.Hom.appIso`. The
  resulting identity is `Scheme.Hom.appIso_hom'` followed by `Scheme.Hom.map_appLE`.

## Vocabulary

Tag 01R3's `conormalSheafIsoPullbackIdealSheaf_liftCoborder` is
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf_liftCoborder`.

Tag 01R3's `conormalSheafIsoPullbackIdealSheaf` is
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf`.

Tag 01R2's `conormalSheaf` is `Stacks.Conormal.conormalSheaf`.

Tag 01C2's `idealSheaf` is `Stacks.ClosedImmersion.idealSheaf`.

No hypothesis beyond those of the statement is used: `IsImmersion i` is what makes `i.liftCoborder`
available and nothing else is assumed. Nothing here is affine, Noetherian, finite or
quasi-compact, and the auxiliary statements about a general morphism `k` of schemes use no
property of `k` at all.

## Transparency gotchas

Two spellings of the same category are in play, as in
`StacksFrontier.AlgebraicGeometry.IdealSheafRestrict.Basic`: `AlgebraicGeometry.Scheme.Modules U`
and `SheafOfModules (structureSheafRing U.toSheafedSpace)`. They agree definitionally but not at the
elaborator's implicit transparency, so a `rw` whose motive straddles them fails. Every statement
below that a later `rw` has to match is therefore written in the second spelling, including the
type of `Stacks.Conormal.idUnit`, whose body is the first; and the final assembly is a chain of
`Eq.trans` and `congrArg` rather than a `rw`, because the identity
`modulePullback (k ≫ 𝟙 U) = modulePullback k` is definitional but not syntactic and `rw` cannot
abstract across it.

The collapse `modulePushforward (𝟙 X) = 𝟭` for a morphism of **ringed spaces** is expensive:
two of them in one declaration exceed the default heartbeat budget. The small `rfl` lemmas
`modulePushforward_id_map_unit_app` and `unit_comp_unit_app_id` exist to carry one collapse
each. At the `AlgebraicGeometry.Scheme.Modules` spelling the same collapse is cheap.

## Universe situation

A single universe `u`, as in the statement: `Scheme.{u}` and `SheafOfModules.{u}`, forced by
`RingedSpaceModuleAdjunction`, whose module pullback exists only for `RingedSpace.{u, u}`.

## What is not done

* **Only one of the twelve labelled assertions of [Stacks, Tag 01R3] is addressed**, namely
  part (1)'s canonical normalization. No tag attribute is attached.
* **The quotient map is still not shown to be an epimorphism.**
  `Stacks.Conormal.epi_conormalQuotientMap_iff` reduces that to the unit of
  `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` being an epimorphism at the
  ideal sheaf of a closed immersion, and nothing here proves it. At the structure sheaf itself
  that reduction is available: Mathlib's `SheafOfModules.pullbackObjUnitToUnit` is invertible
  for a final site functor and
  `SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit` identifies its
  transpose with `SheafOfModules.unitToPushforwardObjUnit`, which a closed immersion makes an
  epimorphism by definition. Passing from the structure sheaf to the ideal sheaf is what is
  missing, and it is not formal: the pullback of a free sheaf of modules is free over an index
  *type*, so a local presentation of the ideal sheaf is needed, together with preservation of
  epimorphisms by the pushforward.
* **Nothing about `Ideal.Cotangent`.** The affine assertions of part (2) are untouched.
* **No unitality in the other slot.** `modulePullbackCompIso f' (𝟙 X')` — the identity in the
  second argument rather than the first — is not treated, and neither is the associativity
  coherence.
* **No elementwise description.** `Stacks.Conormal.idUnit` is characterized only through the
  adjunction and through `kernel.ι`; no formula for its sections is given, the module pullback
  being a sheafification.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.PullbackPseudofunctor Stacks.IdealSheafRestrict

universe u

namespace Stacks.Conormal

/-- A morphism out of `F.obj M` is determined by its adjoint transpose. -/
theorem eq_of_unit_comp_map {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {M : C} {N : D} {c c' : F.obj M ⟶ N}
    (h : adj.unit.app M ≫ G.map c = adj.unit.app M ≫ G.map c') : c = c' :=
  (adj.homEquiv M N).injective <| by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]; exact h

section RingedSpace

variable {X X' : RingedSpace.{u, u}}

/-- Pushforward along an identity does nothing to a unit component. -/
theorem modulePushforward_id_map_unit_app (f' : X' ⟶ X)
    (P : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePushforward (𝟙 X)).map ((modulePullbackPushforwardAdjunction f').unit.app P) =
      (modulePullbackPushforwardAdjunction (f' ≫ 𝟙 X)).unit.app P :=
  rfl

/-- Naturality of the unit for `f' ≫ 𝟙 X`, with the pullback written for `f'`. -/
theorem unit_naturality_comp_id (f' : X' ⟶ X)
    {M N : SheafOfModules.{u} (structureSheafRing X)} (g : M ⟶ N) :
    g ≫ (modulePullbackPushforwardAdjunction (f' ≫ 𝟙 X)).unit.app N =
      (modulePullbackPushforwardAdjunction (f' ≫ 𝟙 X)).unit.app M ≫
        (modulePushforward (f' ≫ 𝟙 X)).map ((modulePullback f').map g) :=
  (modulePullbackPushforwardAdjunction (f' ≫ 𝟙 X)).unit.naturality g

/-- The instance of `unit_naturality_comp_id` at the unit of the identity adjunction. -/
theorem unit_comp_unit_app_id (f' : X' ⟶ X) (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction (𝟙 X)).unit.app M ≫
        (modulePullbackPushforwardAdjunction (f' ≫ 𝟙 X)).unit.app
          ((modulePullback (𝟙 X)).obj M) =
      (modulePullbackPushforwardAdjunction (f' ≫ 𝟙 X)).unit.app M ≫
        (modulePushforward (f' ≫ 𝟙 X)).map ((modulePullback f').map
          ((modulePullbackPushforwardAdjunction (𝟙 X)).unit.app M)) :=
  unit_naturality_comp_id f' _

/-- **Unitality of the pseudofunctoriality isomorphism.** -/
theorem modulePullbackCompIso_hom_app_id (f' : X' ⟶ X)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackCompIso (𝟙 X) f').hom.app M =
      (modulePullback f').map ((modulePullbackPushforwardAdjunction (𝟙 X)).unit.app M) := by
  refine eq_of_unit_comp_map (modulePullbackPushforwardAdjunction (f' ≫ 𝟙 X)) ?_
  rw [unit_comp_map_modulePullbackCompIso_hom_app, modulePushforward_id_map_unit_app]
  exact unit_comp_unit_app_id f' M

end RingedSpace

section Schemes

variable {U V Z : Scheme.{u}}

/-- On sections, `appIso` undoes the restriction to the image of the preimage. -/
theorem map_comp_appIso_hom (j : U ⟶ V) [IsOpenImmersion j] (O : V.Opens) :
    V.presheaf.map (homOfLE (j.image_preimage_le O)).op ≫ (j.appIso (j ⁻¹ᵁ O)).hom =
      j.app O := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_app]

/-- The restriction adjunction's unit, followed by the structure-sheaf identification, is
the structure-sheaf map. -/
theorem restrictAdjunction_unit_comp_restrictUnitIso (j : U ⟶ V) [IsOpenImmersion j] :
    (Scheme.Modules.restrictAdjunction j).unit.app (unitModule V) ≫
        (Scheme.Modules.pushforward j).map (restrictUnitModuleIso j).hom =
      structureMap j := by
  ext O x
  exact congr($(map_comp_appIso_hom j O) x)

/-- The two structure-sheaf identifications agree across `restrictFunctorIsoPullback`. -/
theorem restrictFunctorIsoPullback_hom_comp_pullbackUnitModuleIso (j : U ⟶ V)
    [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.app (unitModule V) ≫
        (pullbackUnitModuleIso j).hom = (restrictUnitModuleIso j).hom := by
  simp [pullbackUnitModuleIso]

/-- The structure-sheaf map of an identity is the identity. -/
theorem structureMap_id (U : Scheme.{u}) : structureMap (𝟙 U) = 𝟙 (unitModule U) :=
  rfl

/-- The unit of the pullback-pushforward adjunction along an identity morphism of schemes,
with the (identity) pushforward collapsed in the type. -/
noncomputable def idUnit (U : Scheme.{u})
    (M : SheafOfModules.{u} (structureSheafRing U.toSheafedSpace)) :
    M ⟶ (modulePullback (𝟙 U : U ⟶ U).toLRSHom.toShHom).obj M :=
  (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 U)).unit.app M

/-- Naturality of `idUnit`. -/
theorem idUnit_naturality (U : Scheme.{u})
    {M N : SheafOfModules.{u} (structureSheafRing U.toSheafedSpace)} (g : M ⟶ N) :
    idUnit U M ≫ (modulePullback (𝟙 U : U ⟶ U).toLRSHom.toShHom).map g =
      g ≫ idUnit U N :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 U)).unit.naturality g).symm

/-- `idUnit` is inverse to the identification of the pullback of the structure sheaf. -/
theorem idUnit_comp_pullbackUnitIso (U : Scheme.{u}) :
    idUnit U (SheafOfModules.unit (structureSheafRing U.toSheafedSpace)) ≫
        (pullbackUnitIso (𝟙 U)).hom =
      𝟙 (SheafOfModules.unit (structureSheafRing U.toSheafedSpace)) :=
  (unit_comp_map_pullbackUnitModuleIso (𝟙 U)).trans (structureMap_id U)

/-- `idUnit` is inverse to the restriction isomorphism of ideal sheaves at the identity. -/
theorem idUnit_comp_pullbackIdealSheafIso (k : Z ⟶ U) :
    idUnit U (Stacks.ClosedImmersion.idealSheaf (k ≫ (𝟙 U : U ⟶ U)).toLRSHom.toShHom) ≫
      (pullbackIdealSheafIso (𝟙 U) k).hom = 𝟙 _ := by
  refine (cancel_mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom k.toLRSHom.toShHom)))).mp ?_
  rw [Category.assoc, pullbackIdealSheafIso_hom_comp_ι, ← Category.assoc, idUnit_naturality,
    Category.assoc, idUnit_comp_pullbackUnitIso]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- `modulePullbackCompIso_hom_app_id` for the identity morphism of a scheme. -/
theorem modulePullbackCompIso_hom_app_scheme_id (k : Z ⟶ U)
    (M : SheafOfModules.{u} (structureSheafRing U.toSheafedSpace)) :
    (modulePullbackCompIso (𝟙 U : U ⟶ U).toLRSHom.toShHom k.toLRSHom.toShHom).hom.app M =
      (modulePullback k.toLRSHom.toShHom).map (idUnit U M) :=
  modulePullbackCompIso_hom_app_id _ _

/-- The two factors of `pullbackIdealSheafCompIso` at the identity cancel. -/
theorem compIso_comp_map_pullbackIdealSheafIso_id (k : Z ⟶ U) :
    (modulePullbackCompIso (𝟙 U : U ⟶ U).toLRSHom.toShHom k.toLRSHom.toShHom).hom.app
        (Stacks.ClosedImmersion.idealSheaf (k ≫ (𝟙 U : U ⟶ U)).toLRSHom.toShHom) ≫
      (modulePullback k.toLRSHom.toShHom).map (pullbackIdealSheafIso (𝟙 U) k).hom = 𝟙 _ := by
  refine Eq.trans (modulePullbackCompIso_hom_app_scheme_id k _ =≫ _) ?_
  refine Eq.trans ((modulePullback k.toLRSHom.toShHom).map_comp _ _).symm ?_
  refine Eq.trans (congrArg (modulePullback k.toLRSHom.toShHom).map
    (idUnit_comp_pullbackIdealSheafIso k)) ?_
  exact (modulePullback k.toLRSHom.toShHom).map_id _

/-- **`pullbackIdealSheafCompIso` along an identity is the identity.** -/
theorem pullbackIdealSheafCompIso_id (k : Z ⟶ U) :
    pullbackIdealSheafCompIso k (𝟙 U) = Iso.refl _ :=
  Iso.ext (compIso_comp_map_pullbackIdealSheafIso_id k)

/-- `pullbackIdealSheafIsoOfCompEq` is the identity whenever the open immersion is the
identity morphism. -/
theorem pullbackIdealSheafIsoOfCompEq_eq_refl (k : Z ⟶ U) (j : U ⟶ U) [IsOpenImmersion j]
    (hj : j = 𝟙 U) (hL : k ≫ j = k) :
    pullbackIdealSheafIsoOfCompEq k j k hL = Iso.refl _ := by
  subst hj
  exact pullbackIdealSheafCompIso_id k

/-- **[Stacks, Tag 01R3], part (1): canonical normalization.** -/
@[stacks 01R3 "part (1): canonical normalization"]
theorem conormalSheafIsoPullbackIdealSheaf_liftCoborder {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] :
    conormalSheafIsoPullbackIdealSheaf i i.coborderRange i.liftCoborder i.liftCoborder_ι =
      Iso.refl (conormalSheaf i) :=
  pullbackIdealSheafIsoOfCompEq_eq_refl _ _ (X.homOfLE_rfl _) _

end Schemes

end Stacks.Conormal

end
