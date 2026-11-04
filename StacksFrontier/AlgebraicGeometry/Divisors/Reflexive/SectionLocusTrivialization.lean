module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# A section trivializes its module on its isomorphism locus

Let `ℱ` be a coherent module on a scheme `X`, let `s` be a global section of `ℱ`, and let

`U = {x ∈ X | s : 𝒪_{X, x} → ℱ_x is an isomorphism}`

be the open subscheme of [Stacks, Tag 0EBN] produced by
`AlgebraicGeometry.sectionIsomorphismOpen`.  Membership of `U` is, by definition, invertibility
of the stalk at that point of the morphism `σ : 𝒪_X ⟶ ℱ` attached to `s`.  A morphism of sheaves
of modules which is invertible on the stalks at the points of an open is invertible after
restriction to that open, so `σ` restricts to an isomorphism

`𝒪_U ≅ ℱ|_U`

on `U` itself, and `ℱ|_U` is in particular invertible.

This is the step of the colimit assertion of [Stacks, Tag 0EBN] that makes `U` a trivializing
open for `ℱ`: it is what identifies `U` with a nonvanishing open, and it is the source of the
comparison `ℱ^{[n]}|_U ≅ 𝒪_U` that the cocone `ℱ^{[n]} ⟶ j_*𝒪_U` is assembled from.

## Main results

* `AlgebraicGeometry.isIso_restrictFunctor_map_of_forall_mem_isIso`: **a morphism of
  `𝒪_X`-modules invertible on the stalks at the points of an open restricts to an isomorphism on
  that open.**
* `AlgebraicGeometry.isIso_restrict_unitHom_sectionIsomorphismOpen`: the section's morphism
  `𝒪_X ⟶ ℱ` is an isomorphism after restriction to its isomorphism locus.
* `AlgebraicGeometry.sectionIsomorphismOpenTrivialization`: **the trivialization `𝒪_U ≅ ℱ|_U`.**
* `AlgebraicGeometry.isInvertible_restrict_sectionIsomorphismOpen`: `ℱ|_U` is invertible.

## Implementation notes

**Why the general lemma is about restriction and not about each open separately.**  The
hypothesis is pointwise — invertibility of a stalk map at each point of `U` — and the conclusion
is about the single morphism `(restrictFunctor U.ι).map σ` of `𝒪_U`-modules.  The two are joined
by `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, which says restriction along an open
immersion commutes with taking stalks: naturality of that isomorphism writes the stalk of the
restricted morphism at `y ∈ U` as a conjugate of the stalk of `σ` at `U.ι y`, so it is invertible
there, and `ExtensionByZeroModules.isIso_of_stalk_isIso` turns stalkwise invertibility into
invertibility.  No reflexivity, rank or normality hypothesis enters, and none is assumed.

**Neither `IsIntegral U.toScheme` nor nonemptiness of `U` is needed.**  `U` is empty exactly when
`s` generates no stalk — for instance when `s = 0` — and the statements below are then the
(correct) statements about the empty scheme.  This is worth recording because
`AlgebraicGeometry.CoherentReflexive.reflexivePowerRestrictIso`, which compares the reflexive
powers of [Stacks, Tag 0EBN] with ordinary tensor powers, *does* require its open to be integral,
so it cannot be applied with `V := U` without first excluding the empty case; the trivialization
here is free of that restriction.

**Why the invertibility statement is at the `.sheaf.obj` spelling.**  `ℱ|_U` invertible is
transported from `𝒪_U` invertible along the trivialization by
`Stacks.UFDExtensionGlobal.isInvertible_of_iso`, which takes its hypothesis explicitly rather
than as an instance; instance search does not see through
`AlgebraicGeometry.Scheme.ringCatSheaf` to find the invertibility of the structure sheaf, so
`AlgebraicGeometry.SheafOfModules.isInvertible_unit` is supplied with both arguments explicit.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (unitModule)

universe u

namespace AlgebraicGeometry

/-! ### Restriction to an open of a stalkwise isomorphism -/

/-- **A morphism of `𝒪_X`-modules which is an isomorphism on the stalks at the points of an open
`U` restricts to an isomorphism on `U`.**  Restriction along an open immersion commutes with
taking stalks, so naturality of `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` writes the
stalk of the restricted morphism at `y` as a conjugate of the stalk of the original at `U.ι y`;
a morphism of sheaves of modules invertible on every stalk is invertible. -/
theorem isIso_restrictFunctor_map_of_forall_mem_isIso {X : Scheme.{u}} (U : X.Opens)
    {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, x ∈ U → IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map φ))) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso U.toScheme.ringCatSheaf _ fun y => ?_
  have : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι.base y)).map φ) :=
    h _ (U.range_ι.le (Set.mem_range_self y))
  have : IsIso ((Scheme.Modules.restrictStalkNatIso U.ι y).hom.app M) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso ((Scheme.Modules.restrictStalkNatIso U.ι y).inv.app N) :=
    NatIso.isIso_app_of_isIso _ _
  have key : (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ =
      (Scheme.Modules.restrictStalkNatIso U.ι y).hom.app M ≫
        (Scheme.Modules.toPresheaf X ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι.base y)).map φ ≫
          (Scheme.Modules.restrictStalkNatIso U.ι y).inv.app N := by
    rw [← Category.assoc, ← (Scheme.Modules.restrictStalkNatIso U.ι y).hom.naturality φ,
      Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, Category.comp_id]
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map φ) := key ▸ inferInstance
  exact this

/-! ### The trivialization on the isomorphism locus of a section -/

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **On its isomorphism locus a section is an isomorphism.**  Membership of
`AlgebraicGeometry.sectionIsomorphismLocus` is by definition invertibility at that point of the
stalk of the morphism `𝒪_X ⟶ ℱ` attached to the section, which is exactly the hypothesis of
`AlgebraicGeometry.isIso_restrictFunctor_map_of_forall_mem_isIso`. -/
theorem isIso_restrict_unitHom_sectionIsomorphismOpen (F : X.Modules) [F.IsCoherent]
    (s : F.sections) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F s).ι).map
      (F.unitHomEquiv.symm s)) :=
  isIso_restrictFunctor_map_of_forall_mem_isIso _ _ fun _ hx => hx

/-- **The trivialization of `ℱ` on the isomorphism locus of a section**: on the open `U` of
[Stacks, Tag 0EBN] the section `s` is an isomorphism `𝒪_U ≅ ℱ|_U`.  It is the restriction to `U`
of the morphism `𝒪_X ⟶ ℱ` attached to `s`, read through
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`. -/
def sectionIsomorphismOpenTrivialization (F : X.Modules) [F.IsCoherent] (s : F.sections) :
    unitModule (sectionIsomorphismOpen X F s).toScheme ≅
      Scheme.Modules.restrict F (sectionIsomorphismOpen X F s).ι :=
  (Scheme.Modules.restrictUnitIso (sectionIsomorphismOpen X F s).ι).symm ≪≫
    @asIso _ _ _ _ _ (isIso_restrict_unitHom_sectionIsomorphismOpen F s)

/-- **`ℱ` is invertible on the isomorphism locus of a section**, being isomorphic there to the
structure sheaf. -/
theorem isInvertible_restrict_sectionIsomorphismOpen (F : X.Modules) [F.IsCoherent]
    (s : F.sections) :
    SheafOfModules.IsInvertible (sectionIsomorphismOpen X F s).toScheme.sheaf.obj
      (sectionIsomorphismOpen X F s).toScheme.ringCatSheaf.property
      (Scheme.Modules.restrict F (sectionIsomorphismOpen X F s).ι) :=
  Stacks.UFDExtensionGlobal.isInvertible_of_iso (sectionIsomorphismOpenTrivialization F s)
    (SheafOfModules.isInvertible_unit _ _)

end AlgebraicGeometry

end
