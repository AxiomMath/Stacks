module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.RestrictionMaps

/-!
# Sections and stalks on an affine spectrum

For a commutative ring `R` and an `R`-module `M`, the structure sheaf of `Spec R` and the sheaf
`M̃` associated to `M` are determined by localization: their global sections recover `R` and `M`,
their sections over a standard open `D(f)` are the localizations away from `f`, and their stalks
at a point are the localizations at the corresponding prime.

Mathlib records each of these identifications in the choice-independent form — an
`IsLocalization.Away`, `IsLocalization.AtPrime` or `IsLocalizedModule` statement, or an explicit
isomorphism — rather than as an equality with a chosen localization, and those are the
statements tagged here. This file adds the compatibility of these identifications with
restriction: on an inclusion `D(g) ≤ D(f)` of standard opens, restriction of sections is the
canonical localization map of Tag 01HS.

## Main results

* `AlgebraicGeometry.StructureSheaf.map_basicOpen`: restriction of functions from `D(f)` to
  `D(g)` is `PrimeSpectrum.ringRestrictionMap`.
* `AlgebraicGeometry.tilde.map_basicOpen`: restriction of sections of `M̃` from `D(f)` to `D(g)`
  is `PrimeSpectrum.moduleRestrictionMap`.

## Implementation notes

The structure-sheaf identification on a standard open is `IsLocalization.algEquiv`. For modules,
`AlgebraicGeometry.tilde.toOpen` is the canonical localization map on each standard open and
`IsLocalizedModule.iso` is the resulting identification; for a chosen model of the localization,
`IsLocalizedModule.iso_mk_one` characterizes the identification on the image of `M`, and
`LinearEquiv.extendScalarsOfIsLocalization` upgrades it to a map linear over the localized ring.
Mathlib's `tilde` places the ring and the module in the same universe.

## References

* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

add_to_stacks 01HV "global_structure_sections" AlgebraicGeometry.StructureSheaf.globalSectionsIso
add_to_ega "I 1.3.7" "Case M = A" AlgebraicGeometry.StructureSheaf.globalSectionsIso
add_to_ega "I 10.1.3" "special case" AlgebraicGeometry.StructureSheaf.globalSectionsIso
add_to_stacks 01HV "global_module_sections" AlgebraicGeometry.tilde.isoTop
add_to_ega "I 1.3.7" AlgebraicGeometry.tilde.isoTop
add_to_ega "I 10.10.2" "(i), special case" AlgebraicGeometry.tilde.isoTop
add_to_stacks 01HV "basic_open_structure_sections"
  AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
add_to_ega "I 9.3.2" "special case" AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
add_to_ega "I 9.3.3" "special case" AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
add_to_ega "III 1.2.2" "special case" AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen
add_to_stacks 01HV "basic_open_module_sections"
  AlgebraicGeometry.tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen -- https://stacks.math.columbia.edu/tag/01HV
-- The auto-generated instance name is longer than a line, so its identifier is assembled
-- from two pieces before being handed to `add_to_ega`.
run_cmd do
  let decl := Lean.mkIdent <| .str `AlgebraicGeometry.tilde <|
    "instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCat" ++
      "PresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen"
  Lean.Elab.Command.elabCommand (← `(command| add_to_ega "I 1.3.7" $decl:ident))
add_to_stacks 01HV "structure_stalk" AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk
add_to_stacks 01HV "module_stalk"
  AlgebraicGeometry.tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk -- https://stacks.math.columbia.edu/tag/01HV

universe u

namespace AlgebraicGeometry.StructureSheaf

/-- Under the canonical identifications of sections on standard opens with localizations,
restriction in the structure sheaf is the canonical map `R_f → R_g`. -/
@[stacks 01HV "restriction_maps"]
theorem map_basicOpen {R : CommRingCat.{u}} (f g : R)
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ((AlgebraicGeometry.Spec.structureSheaf R).obj.map (homOfLE hfg).op).hom.comp
        (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
          ((AlgebraicGeometry.Spec.structureSheaf R).obj.obj
            (.op (PrimeSpectrum.basicOpen f)))).toRingHom =
      (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
        ((AlgebraicGeometry.Spec.structureSheaf R).obj.obj
          (.op (PrimeSpectrum.basicOpen g)))).toRingHom.comp
        (PrimeSpectrum.ringRestrictionMap f g hfg).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext r
  simp only [homOfLE_leOfHom, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
    RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.commutes,
    AlgHom.toRingHom_eq_coe, AlgHom.commutes]
  change
    ((CommRingCat.ofHom (algebraMap R
        ((AlgebraicGeometry.structureSheafInType R R).obj.obj
          (.op (PrimeSpectrum.basicOpen f)))) ≫
      (AlgebraicGeometry.Spec.structureSheaf R).1.map (homOfLE hfg).op).hom r) =
    (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap R
      ((AlgebraicGeometry.structureSheafInType R R).obj.obj
        (.op (PrimeSpectrum.basicOpen g))))) r)
  exact congrArg (fun φ : CommRingCat.of R ⟶ CommRingCat.of
      ((AlgebraicGeometry.structureSheafInType R R).obj.obj
        (.op (PrimeSpectrum.basicOpen g))) => CommRingCat.Hom.hom φ r)
    (AlgebraicGeometry.StructureSheaf.algebraMap_self_map R
      (.op (PrimeSpectrum.basicOpen g)) (.op (PrimeSpectrum.basicOpen f))
      (homOfLE hfg).op)

end AlgebraicGeometry.StructureSheaf

namespace AlgebraicGeometry.tilde

/-- Sections of the associated sheaf on `D(f)` and `D(g)` are canonically isomorphic to `M_f`
and `M_g`. The isomorphisms identify sheaf restriction with the canonical map `M_f → M_g`. -/
@[stacks 01HV "restriction_maps"]
theorem map_basicOpen {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f g : R)
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∀ x : LocalizedModule.Away (R := R) f M,
      (modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hfg).op
          ((IsLocalizedModule.iso (Submonoid.powers f)
            (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom) x) =
        (IsLocalizedModule.iso (Submonoid.powers g)
          (tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom)
            (PrimeSpectrum.moduleRestrictionMap f g hfg x) := by
  let φ := PrimeSpectrum.ringRestrictionMap f g hfg
  let := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
    (LocalizedModule.Away (R := R) g M) φ.toRingHom
  let : IsScalarTower R (Localization.Away f)
      (LocalizedModule.Away (R := R) g M) :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change φ (algebraMap R (Localization.Away f) r) • m = r • m
      rw [φ.commutes]
      exact IsScalarTower.algebraMap_smul (Localization.Away g) r m
  let ρ := ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (homOfLE hfg).op).hom
  let ef := IsLocalizedModule.iso (Submonoid.powers f)
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
  let eg := IsLocalizedModule.iso (Submonoid.powers g)
    (tilde.toOpen M (PrimeSpectrum.basicOpen g)).hom
  let F := ρ.comp ef.toLinearMap
  let G := eg.toLinearMap.comp (LinearMap.restrictScalars (↑R)
      (PrimeSpectrum.moduleRestrictionMap f g hfg))
  have hFG : F = G := by
    refine IsLocalizedModule.ext (S := Submonoid.powers f)
      (f := LocalizedModule.mkLinearMap (Submonoid.powers f) M) (by
        intro s
        obtain ⟨n, hn⟩ := s.property
        rw [← hn, map_pow]
        exact (AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen
          (M := tilde M) (U := PrimeSpectrum.basicOpen g) f hfg).pow n) ?_
    ext m
    change ρ (ef (LocalizedModule.mk m 1)) =
      eg (PrimeSpectrum.moduleRestrictionMap f g hfg
        ((LocalizedModule.mkLinearMap (Submonoid.powers f) M) m))
    rw [IsLocalizedModule.iso_mk_one,
      PrimeSpectrum.moduleRestrictionMap_mk,
      LocalizedModule.mkLinearMap_apply]
    dsimp [eg]
    rw [IsLocalizedModule.iso_mk_one]
    rfl
  intro x
  exact DFunLike.congr_fun hFG x

end AlgebraicGeometry.tilde

end
