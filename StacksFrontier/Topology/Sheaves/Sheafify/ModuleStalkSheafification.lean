module

public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor

/-!
# Sheafification does not change the stalks of a presheaf of modules

Let `X` be a topological space, `O` a sheaf of commutative rings on `X` and `P` a presheaf of
`O`-modules.  Sheafifying `P` in the category of `O`-modules (Stacks 0089, in the form of
`PresheafOfModules.sheafification` along the identity of `O`, which is legitimate because `O` is
already a sheaf) does not change its stalks: the unit of the sheafification adjunction induces an
`O_x`-linear isomorphism `P_x ≅ (P^#)_x` at every point.

This is the general form of the second ingredient of Stacks 008B.  That ingredient is already
proved in `StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor`, but only for the particular
presheaf of modules appearing there (the sectionwise change-of-rings tensor product), with the
tensor product baked into the statement.  Nothing in the argument uses what `P` is, so it is
recorded here for an arbitrary `P`.

## Main results

* `Stacks.Sheafify.stalkSheafifyIso` is the `O_x`-linear isomorphism `P_x ≅ (P^#)_x`.
* `Stacks.Sheafify.stalkIsoOfSheafifyIso` transports it along an isomorphism identifying some
  other sheaf of `O`-modules with `P^#`.

## Relation to `OXModule.sheafifyStalkLinearEquiv`

`OXModule.sheafifyStalkLinearEquiv` (Stacks Tag 08BQ) already proves
`stalkSheafifyIso` for a sheaf of commutative rings presented as the structure sheaf of an
`AlgebraicGeometry.RingedSpace`, by the same argument.  The version here takes the sheaf of
commutative rings on a `TopCat` directly.  `stalkLinearEquivOfIso` and `stalkIsoOfSheafifyIso`
have no counterpart there.

## Implementation notes

The comparison map is `O_x`-linear because the sheafification is performed in the category of
`O`-modules, so its unit is a morphism of presheaves of modules; on underlying abelian groups it
is `(stalkFunctor Ab x).map (toSheafify …)`, which is an isomorphism by
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`.

`Stacks.Sheafify.moduleStalkOfRingSheaf` records, once and for all, the `O_x`-module structure on
the stalk of a presheaf of modules over `(structureSheafRing O).obj`.  Mathlib supplies this
structure for a presheaf of modules over a presheaf of rings spelled
`R ⋙ forget₂ CommRingCat RingCat`, and `(structureSheafRing O).obj` *is*
`O.presheaf ⋙ forget₂ CommRingCat RingCat` — but only after unfolding
`CategoryTheory.sheafCompose` and projecting out of the structure it builds, which typeclass
resolution does not do at reducible transparency.  `inferInstanceAs` through a `show` retyping
checks the identification at default transparency instead.  `ModuleStalkTensor` records the same
instance for the one presheaf of modules it is about; this is the general version.

## References

* [Stacks Project, Tag 0089](https://stacks.math.columbia.edu/tag/0089)
* [Stacks Project, Tag 008B](https://stacks.math.columbia.edu/tag/008B)
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

namespace Stacks.Sheafify

variable {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)
  (P : PresheafOfModules.{u} (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O).obj) (x : X)

/-- The canonical `O_x`-module structure on the stalk at `x` of a presheaf of modules over the
`RingCat`-valued sheaf of rings underlying `O`. -/
noncomputable instance (priority := 100) moduleStalkOfRingSheaf :
    Module (O.presheaf.stalk x)
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x)) :=
  inferInstanceAs (Module (O.presheaf.stalk x)
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u})
      (show PresheafOfModules.{u} (Stacks.Sheafify.ModuleStalkTensor.ringPresheaf O.presheaf) from
        P).presheaf x)))

/-- A morphism of presheaves of `O`-modules is bijective on the stalks at `x` as soon as its
stalk map on underlying abelian groups is an isomorphism. -/
private theorem stalkLinearMapOfHom_bijective_of_isIso {M N : PresheafOfModules.{u}
  (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O).obj}
    (φ : M ⟶ N) (_ : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((PresheafOfModules.toPresheaf _).map φ))) :
    Function.Bijective (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom O.presheaf x φ) := by
  change Function.Bijective ⇑(ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((PresheafOfModules.toPresheaf _).map φ)))
  exact CategoryTheory.ConcreteCategory.bijective_of_isIso _

/-- An isomorphism of presheaves of `O`-modules induces a bijection on the stalks at `x`. -/
theorem stalkLinearMapOfHom_bijective {M N : PresheafOfModules.{u}
  (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O).obj}
    (φ : M ⟶ N) [IsIso φ] :
    Function.Bijective (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom O.presheaf x φ) := by
  exact stalkLinearMapOfHom_bijective_of_isIso O x φ inferInstance

/-- An isomorphism of presheaves of `O`-modules induces an `O_x`-linear isomorphism on the
stalks at `x`. -/
noncomputable def stalkLinearEquivOfIso
    {M N : PresheafOfModules.{u} (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O).obj} (e : M ≅ N) :
    (TopCat.Presheaf.stalk (C := Ab.{u}) M.presheaf x)
      ≃ₗ[O.presheaf.stalk x] (TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x) :=
  LinearEquiv.ofBijective (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom O.presheaf x e.hom)
    (stalkLinearMapOfHom_bijective O x e.hom)

/-- The sheafification `P^#` of a presheaf of `O`-modules, as a sheaf of `O`-modules.  Since `O`
is already a sheaf of rings, this is `PresheafOfModules.sheafification` along the identity of
`O`. -/
noncomputable abbrev sheafify : SheafOfModules.{u} (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O)
  :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O).obj)).obj P

/-- The comparison map `P_x → (P^#)_x`: the stalk at `x` of the unit of the sheafification
adjunction for presheaves of `O`-modules, evaluated at `P`.  It is `O_x`-linear because that
unit is a morphism of presheaves of `O`-modules. -/
noncomputable def stalkSheafifyMap :
    (TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x)
      →ₗ[O.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (sheafify O P).val.presheaf x) :=
  Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom O.presheaf x
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.Sheafify.ModuleStalkTensor.ringSheaf
      O).obj)).unit.app P)

/-- The comparison map `P_x → (P^#)_x` is bijective.

On underlying abelian groups it is `(stalkFunctor Ab x).map η₀` with
`η₀ = (toPresheaf _).map (η.app P) = toSheafify _ P.presheaf`, by
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`, and the stalk functor
sends `toSheafify` to an isomorphism. -/
theorem stalkSheafifyMap_bijective : Function.Bijective (stalkSheafifyMap O P x) := by
  have hiso : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((PresheafOfModules.toPresheaf _).map ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O).obj)).unit.app P))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab _
  exact stalkLinearMapOfHom_bijective_of_isIso O x _ hiso

/-- **Sheafification does not change stalks.**  For a sheaf of commutative rings `O` on `X` and a
presheaf of `O`-modules `P`, the unit of the sheafification adjunction induces an `O_x`-linear
isomorphism from the stalk of `P` at `x` to the stalk of its sheafification `P^#`. -/
noncomputable def stalkSheafifyIso :
    (TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x)
      ≃ₗ[O.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (sheafify O P).val.presheaf x) :=
  LinearEquiv.ofBijective (stalkSheafifyMap O P x) (stalkSheafifyMap_bijective O P x)

/-- **The stalks of a sheaf of modules presented as a sheafification.**  If a sheaf of
`O`-modules `F` is isomorphic to the sheafification of a presheaf of `O`-modules `P`, then the
stalk of `F` at `x` is `O_x`-linearly isomorphic to the stalk of `P` at `x`.

This is the composite of `stalkSheafifyIso` with the stalk isomorphism induced by `e`; it is
assembled here so that the composition happens where only one spelling of `O`'s underlying sheaf
of rings is in scope. -/
noncomputable def stalkIsoOfSheafifyIso
    {F : SheafOfModules.{u} (Stacks.Sheafify.ModuleStalkTensor.ringSheaf O)} (e : sheafify O P ≅ F)
      :
    (TopCat.Presheaf.stalk (C := Ab.{u}) P.presheaf x)
      ≃ₗ[O.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  (stalkSheafifyIso O P x).trans
    (stalkLinearEquivOfIso O x ((SheafOfModules.forget (Stacks.Sheafify.ModuleStalkTensor.ringSheaf
      O)).mapIso e))

end Stacks.Sheafify

end
