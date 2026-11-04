module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedScalarRestriction
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.AlgebraicGeometry.SheafifyStalk.StalkMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatOpenRestriction

/-!
# A module flat over the base is flat over the inverse image of the base's structure sheaf

Let `f : X ⟶ S` be a morphism of schemes and `ℱ` an `𝒪_X`-module which is flat over `S`, that
is, whose stalk `ℱ_y` is flat over `𝒪_{S, f(y)}` through the stalk map of `f` at every point `y`
(`AlgebraicGeometry.IsFlatOver`, [Stacks, Tag 08KT]). Then `ℱ`, read as a module over
`f⁻¹𝒪_S` by restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`, is a flat sheaf of
`f⁻¹𝒪_S`-modules.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver`: the statement above,
  with flatness of a sheaf of modules on the inverse-image ringed space
  `AlgebraicGeometry.RingedSpace.inverseImage S.toRingedSpace f.base` read as exactness of the
  tensor product, which is the notion the Tor-amplitude development consumes.

## Implementation notes

Flatness of a sheaf of modules on a ringed space is detected on stalks
(`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`, [Stacks, Tag 05NE]). At a point `y`
the stalk of the restriction of scalars is the stalk `ℱ_y`, with `(f⁻¹𝒪_S)_y` acting through the
stalk of the structural map `f⁻¹𝒪_S ⟶ 𝒪_X`; this is checked on germs in
`restrictScalars_commStalk_smul`. The comparison `(f⁻¹𝒪_S)_y ≅ 𝒪_{S, f(y)}` of
`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso` carries that stalk map to the stalk
map of `f` (`Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap`), so
flatness over `𝒪_{S, f(y)}` transports along the ring isomorphism
(`AlgebraicGeometry.SheafOfModules.isFlat_of_ringEquiv`).

## References

* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 05NE](https://stacks.math.columbia.edu/tag/05NE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

omit f in
/-- Flatness over `B`, acting through `φ : B →+* C`, transports to flatness over `A` along a
ring isomorphism `e : A ≃+* B` compatible with the two actions. -/
private theorem flat_of_ringEquiv_compHom {A B C M : Type u} [CommRing A] [CommRing B]
    [CommRing C] [AddCommGroup M] (instA : Module A M) (instC : Module C M) (φ : B →+* C)
    (e : A ≃+* B) (h : @Module.Flat B M _ _ (Module.compHom M φ))
    (hsmul : ∀ (a : A) (m : M), a • m = φ (e a) • m) : Module.Flat A M := by
  let := Module.compHom M φ
  exact AlgebraicGeometry.SheafOfModules.isFlat_of_ringEquiv e hsmul

omit f in
/-- **The stalk action on a restriction of scalars.** For `α : R ⟶ R'` a morphism of presheaves
of commutative rings and `N` a presheaf of modules over `R'`, the action of `R_y` on the stalk
of the restriction of scalars of `N` is the action of `R'_y` through the stalk of `α`. -/
private theorem restrictScalars_commStalk_smul {T : TopCat.{u}}
    {R R' : TopCat.Presheaf CommRingCat.{u} T} (α : R ⟶ R')
    (N : _root_.PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (y : T)
    (a : R.stalk y) (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf y)
    (b : R'.stalk y) (hb : ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map α).hom a = b) :
    letI : Module (R.stalk y) (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf y) :=
      inferInstanceAs (Module (R.stalk y) (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((_root_.PresheafOfModules.restrictScalars
          (Functor.whiskerRight α (forget₂ CommRingCat.{u} RingCat.{u}))).obj N).presheaf y))
    a • m = b • m := by
  subst hb
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u}) R a
  obtain ⟨V, hyV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) N.presheaf m
  have hyW : y ∈ U ⊓ V := ⟨hyU, hyV⟩
  rw [← TopCat.Presheaf.germ_res_apply R (homOfLE inf_le_left : U ⊓ V ⟶ U) y hyW s,
    ← TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) y hyW t,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact (_root_.PresheafOfModules.germ_smul ((_root_.PresheafOfModules.restrictScalars
    (Functor.whiskerRight α (forget₂ CommRingCat.{u} RingCat.{u}))).obj N) y (U ⊓ V)
      hyW _ _).symm.trans (_root_.PresheafOfModules.germ_smul N y (U ⊓ V) hyW _ _)

/-- **A module flat over the base is flat over `f⁻¹𝒪_S`.** If an `𝒪_X`-module `ℱ` is flat over
`S` in the stalkwise sense of [Stacks, Tag 08KT], then `ℱ`, read as an `f⁻¹𝒪_S`-module by
restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`, is a flat sheaf of modules on the inverse-image
ringed space `(X, f⁻¹𝒪_S)`. -/
theorem isFlat_scalarRestriction_of_isFlatOver (F : OXMod.{u, u} X.toRingedSpace)
    (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (RingedSpace.inverseImage S.toRingedSpace f.base).sheaf)
      ((Scheme.Hom.scalarRestriction f).obj F) := by
  refine (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat
    (X := (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (RingedSpace.inverseImage S.toRingedSpace f.base).sheaf _).2 ?_
  intro y
  let Z := RingedSpace.inverseImage S.toRingedSpace f.base
  let M : _root_.PresheafOfModules.{u} (Z.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
    ((Scheme.Hom.scalarRestriction f).obj F).val
  let N : _root_.PresheafOfModules.{u}
      (X.toRingedSpace.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let instA : Module (TopCat.Presheaf.stalk (C := CommRingCat.{u}) Z.sheaf.obj y)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf y) := inferInstance
  exact flat_of_ringEquiv_compHom instA _ _
    (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f y).commRingCatIsoToRingEquiv
    (hF y) fun a m => restrictScalars_commStalk_smul
      (AlgebraicGeometry.inverseImageStructureMap f).hom N y a m _
      (congrArg (fun φ => φ.hom a)
        (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap f y)).symm

end AlgebraicGeometry.Scheme.Hom
