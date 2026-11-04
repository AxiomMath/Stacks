module

public import StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionFlatOver
import all StacksFrontier.AlgebraicGeometry.Perfect.ScalarRestrictionFlatOver

/-!
# A module flat over the inverse image of the base's structure sheaf is flat over the base

Let `f : X ⟶ S` be a morphism of schemes and `ℱ` an `𝒪_X`-module. If `ℱ`, read as a module over
`f⁻¹𝒪_S` by restriction of scalars along `f⁻¹𝒪_S ⟶ 𝒪_X`, is a flat sheaf of `f⁻¹𝒪_S`-modules,
then `ℱ` is flat over `S` in the stalkwise sense of [Stacks, Tag 08KT]. This is the converse of
`AlgebraicGeometry.Scheme.Hom.isFlat_scalarRestriction_of_isFlatOver`, so the two notions of
flatness over the base agree.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFlatOver_of_isFlat_scalarRestriction`: the statement above.

## Implementation notes

The proof is the one of `isFlat_scalarRestriction_of_isFlatOver` read backwards. Flatness of a
sheaf of modules is detected on stalks ([Stacks, Tag 05NE]); at a point `y` the stalk of the
restriction of scalars is `ℱ_y` with `(f⁻¹𝒪_S)_y` acting through the stalk of the structural map,
and the comparison `(f⁻¹𝒪_S)_y ≅ 𝒪_{S, f(y)}` carries that action to the action through the
stalk map of `f`, so flatness transports along the inverse ring isomorphism. The germ computation
is the private `restrictScalars_commStalk_smul` of the forward file, reached by `import all`.

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
/-- Flatness over `A` transports to flatness over `B`, acting through `φ : B →+* C`, along a
ring isomorphism `e : A ≃+* B` compatible with the two actions. This is the converse of the
private `flat_of_ringEquiv_compHom` of the forward file. -/
theorem flat_compHom_of_ringEquiv {A B C M : Type u} [CommRing A] [CommRing B]
    [CommRing C] [AddCommGroup M] (instA : Module A M) (instC : Module C M) (φ : B →+* C)
    (e : A ≃+* B) (h : @Module.Flat A M _ _ instA)
    (hsmul : ∀ (a : A) (m : M), a • m = φ (e a) • m) :
    @Module.Flat B M _ _ (Module.compHom M φ) := by
  let := Module.compHom M φ
  refine AlgebraicGeometry.SheafOfModules.isFlat_of_ringEquiv e.symm fun b m => ?_
  rw [hsmul (e.symm b) m, RingEquiv.apply_symm_apply]
  rfl

/-- **A module flat over `f⁻¹𝒪_S` is flat over the base.** If the restriction of scalars of an
`𝒪_X`-module `ℱ` along `f⁻¹𝒪_S ⟶ 𝒪_X` is a flat sheaf of modules on `(X, f⁻¹𝒪_S)`, then every
stalk `ℱ_y` is flat over `𝒪_{S, f(y)}` through the stalk map of `f`. -/
theorem isFlatOver_of_isFlat_scalarRestriction (F : OXMod.{u, u} X.toRingedSpace)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (RingedSpace.inverseImage S.toRingedSpace f.base).sheaf)
      ((Scheme.Hom.scalarRestriction f).obj F)) :
    AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F := by
  intro y
  have hy := (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat
    (X := (RingedSpace.inverseImage S.toRingedSpace f.base).carrier)
    (RingedSpace.inverseImage S.toRingedSpace f.base).sheaf _).1 hF y
  let N : _root_.PresheafOfModules.{u}
      (X.toRingedSpace.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  dsimp only [AlgebraicGeometry.IsFlatOverAt]
  let e := (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso f y).commRingCatIsoToRingEquiv
  have key : ∀ a, (f.toLRSHom.toShHom.hom.stalkMap y).hom (e a) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map
        (AlgebraicGeometry.inverseImageStructureMap f).hom).hom a := fun a =>
    congrArg (fun φ => φ.hom a)
      (Stacks.SheafifyStalk.stalkInverseImageStructureSheafIso_hom_comp_stalkMap f y)
  exact flat_compHom_of_ringEquiv _ _ _ e hy fun a m =>
    restrictScalars_commStalk_smul (AlgebraicGeometry.inverseImageStructureMap f).hom
      N y a m _ (key a).symm

end AlgebraicGeometry.Scheme.Hom

end
