module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf

/-!
# Invertibility of the conormal module map of a fibre product square

Let `Z'` be a closed subspace of an algebraic space `X'`, let `g : X ⟶ X'` be a morphism of
algebraic spaces, and let `Z = g⁻¹(Z')` be the inverse image closed subspace of
[Stacks Project, Tag 083Q], so that the square of `Z, X, Z', X'` is a fibre product square.
The canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is then an
isomorphism as soon as the inverse image along `g` of the inclusion `𝓘' ⊆ 𝒪_{X'}` of the
defining ideal sheaf of `Z'`, read in `𝒪_X` through the canonical comparison
`g^*𝒪_{X'} ⟶ 𝒪_X`, is injective.

Surjectivity of the map of defining ideal sheaves is
`AlgebraicGeometry.Space.epi_idealSheafMap`, so the cartesianness half of the hypotheses of
[Stacks Project, Tag 04CQ] and of [Stacks Project, Tag 06BH] is discharged; what remains is the
injectivity, which those tags obtain from flatness of `g`.

## Main results

* `AlgebraicGeometry.Space.isIso_idealSheafMap_preimage_of_mono`: the map `g^*𝓘' ⟶ 𝓘` of
  defining ideal sheaves of the fibre product square is an isomorphism.
* `AlgebraicGeometry.Space.isIso_conormalMap_preimage_of_mono` and
  `AlgebraicGeometry.Space.isIso_conormalMap_preimage_of_mono_comp`: **the conormal-module
  condition of [Stacks Project, Tag 06BH] at the fibre product square**, in the two shapes of
  the injectivity hypothesis.
* `AlgebraicGeometry.Space.isIso_structureModulePullbackMap_of_unitSection`: the comparison
  `g^*𝒪_{X'} ⟶ 𝒪_X` is invertible as soon as its transpose carries the unit section to the
  unit section.

## Coverage limits

No `@[stacks 06BH]` or `@[stacks 04CQ]` attribute is placed.  Both tags assume that `g` is flat
and derive from that the injectivity of `g^*𝓘' ⟶ 𝓘` which is assumed here: for a flat morphism
the inverse image of modules is exact, hence carries the inclusion `𝓘' ⊆ 𝒪_{X'}` to a
monomorphism.  That exactness is not available in this development, so the hypothesis of each
result below is strictly stronger than the tag's and no attribute claims either tag.

`AlgebraicGeometry.Space.isIso_structureModulePullbackMap_of_unitSection` reduces invertibility
of the comparison `g^*𝒪_{X'} ⟶ 𝒪_X` — the second half of the injectivity hypothesis, which is
true, the comparison being the isomorphism of
`AlgebraicGeometry.Space.modulePullbackUnitIso` read through corepresentability — to a single
identity of global sections of the direct image.  That identity is not proved: establishing it
means comparing the transpose of
`AlgebraicGeometry.Space.structureModulePullbackMap`, which is pinned on diagrams of étale
scheme charts, with the global-sections description of the corepresentation, which is pinned
through the terminal sheaf; the two live over the two spellings of the direct image of modules
compared by `AlgebraicGeometry.Space.modulePushforwardIso`, and identifying them is the
unfolding of the whole chain of direct images and restrictions of scalars that the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyBaseChange.lean` record as impracticable.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory

/-- A morphism to `Y` from an object corepresenting `coyoneda.obj (op Y)` which that
corepresentation carries to the identity of `Y` is an isomorphism. -/
theorem isIso_of_coyoneda_corepresentableBy {C : Type*} [Category C] {Y Z : C}
    (e : (coyoneda.obj (op Y)).CorepresentableBy Z) (φ : Z ⟶ Y)
    (h : e.homEquiv φ = 𝟙 Y) : IsIso φ := by
  have h1 : e.homEquiv (𝟙 Z) ≫ φ = 𝟙 Y :=
    ((e.homEquiv_comp φ (𝟙 Z)).symm.trans
      (congrArg e.homEquiv (Category.id_comp φ))).trans h
  have h2 : φ ≫ e.homEquiv (𝟙 Z) = 𝟙 Z := by
    refine e.homEquiv.injective (Eq.trans (e.homEquiv_comp (e.homEquiv (𝟙 Z)) φ) ?_)
    show e.homEquiv φ ≫ e.homEquiv (𝟙 Z) = e.homEquiv (𝟙 Z)
    rw [h, Category.id_comp]
  exact ⟨e.homEquiv (𝟙 Z), h2, h1⟩

end CategoryTheory

namespace MorphismOfTopoi

/-- The global section of a direct image obtained from a global section of the sheaf, by the
direct image of that section and the unique global section of the direct image of the terminal
sheaf, is carried back to it by `MorphismOfTopoi.pushforwardTerminalHomEquiv`. -/
theorem pushforwardTerminalHomEquiv_terminal_comp {C : Type*} [Category C]
    {J : GrothendieckTopology C} {D : Type*} [Category D] {K : GrothendieckTopology D}
    (gt : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) (E : Sheaf J (Type u))
    (s : ⊤_ (Sheaf J (Type u)) ⟶ E) :
    gt.pushforwardTerminalHomEquiv E
        ((gt.pushforwardTerminalHomEquiv (⊤_ (Sheaf J (Type u)))).symm (𝟙 _) ≫
          gt.pushforward.map s) = s :=
  (pushforwardTerminalHomEquiv_comp gt s _).trans
    ((congrArg (fun m => m ≫ s) (Equiv.apply_symm_apply _ _)).trans (Category.id_comp s))

end MorphismOfTopoi

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The unit section of the structure sheaf -/

/-- The unit section of the structure sheaf of an algebraic space, read as a morphism from the
terminal sheaf of sets on its small étale site. -/
noncomputable def structureUnitSection (X : AlgebraicSpaces B S hS) :
    ⊤_ (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) ⟶
      moduleSetSheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  unitTerminalHomEquiv (structureRingSheaf B S hS X)
    (SheafOfModules.unit (structureRingSheaf B S hS X)) (𝟙 _)

/-- The unit section takes the value `1` over every étale scheme chart. -/
theorem sectionsFunctor_map_structureUnitSection (X : AlgebraicSpaces B S hS)
    (Z : (SmallEtale B S hS X.1)ᵒᵖ)
    (p : (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1) Z).obj
      (⊤_ (Sheaf (SmallEtale.topology B S hS X.1) (Type u)))) :
    (sectionsFunctor.{u} (SmallEtale.topology B S hS X.1) Z).map
        (structureUnitSection B S hS X) p =
      (1 : (structureRingSheaf B S hS X).obj.obj Z) :=
  rfl

variable {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')

/-! ### The comparison of structure sheaves -/

/-- **The comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is invertible once its transpose carries the unit
section to the unit section.**  Morphisms out of `g^*𝒪_{X'}` are, by the adjunction of
[Stacks Project, Tag 03D7], the global sections of the target, and under that corepresentation
the comparison corresponds to the global section which the hypothesis names as the unit one. -/
theorem isIso_structureModulePullbackMap_of_unitSection
    (h : pushforwardModulesUnitHomEquiv (smallEtaleRingedToposModulesHom B S hS g)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        ((pullbackAdjPushforwardModules
            (smallEtaleRingedToposModulesHom B S hS g)).homEquiv _ _
          (structureModulePullbackMap B S hS g)) =
      structureUnitSection B S hS X) :
    IsIso (structureModulePullbackMap B S hS g) :=
  isIso_of_coyoneda_corepresentableBy
    (pullbackModulesObjUnitCorepresentableBy (smallEtaleRingedToposModulesHom B S hS g))
    (structureModulePullbackMap B S hS g)
    ((congrArg (unitTerminalHomEquiv (structureRingSheaf B S hS X)
        (SheafOfModules.unit (structureRingSheaf B S hS X))).symm h).trans
      ((unitTerminalHomEquiv (structureRingSheaf B S hS X)
        (SheafOfModules.unit (structureRingSheaf B S hS X))).symm_apply_apply (𝟙 _)))

/-! ### The fibre product square -/

variable (Z' : ClosedSubspaces B S hS X'.1)

/-- **The map of defining ideal sheaves of a fibre product square is an isomorphism once the
inverse image of the inclusion `𝓘' ⊆ 𝒪_{X'}` is injective.**  Surjectivity is
`AlgebraicGeometry.Space.epi_idealSheafMap`, and modules on the small étale site of an algebraic
space form a balanced category. -/
theorem isIso_idealSheafMap_preimage_of_mono
    (hm : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
      structureModulePullbackMap B S hS g)) :
    IsIso (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) :=
  isIso_idealSheafMap_of_epi_of_mono B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z')
    (epi_idealSheafMap B S hS g Z') hm

/-- **The conormal-module condition of [Stacks Project, Tag 06BH] at a fibre product square.**
For the inverse image closed subspace `g⁻¹(Z') ⊆ X` of [Stacks Project, Tag 083Q] the canonical
map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}` of [Stacks Project, Tag 04CP] is an isomorphism, provided
the inverse image along `g` of the inclusion `𝓘' ⊆ 𝒪_{X'}`, read in `𝒪_X` through the
comparison `g^*𝒪_{X'} ⟶ 𝒪_X`, is injective.

The hypothesis is what [Stacks Project, Tag 06BH] obtains from flatness of `g`; the coverage
limits of this file record that the derivation is not carried here. -/
theorem isIso_conormalMap_preimage_of_mono_comp
    (hm : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
      structureModulePullbackMap B S hS g)) :
    IsIso (conormalMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) :=
  isIso_conormalMap_of_epi_idealSheafMap_of_mono B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z')
    (epi_idealSheafMap B S hS g Z') hm

/-- **The conormal-module condition of [Stacks Project, Tag 06BH] at a fibre product square**,
with the injectivity hypothesis split into its two factors: injectivity of the inverse image of
the inclusion `𝓘' ⊆ 𝒪_{X'}`, which holds for a flat `g`, and injectivity of the comparison
`g^*𝒪_{X'} ⟶ 𝒪_X`, which holds always. -/
theorem isIso_conormalMap_preimage_of_mono
    (hι : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι))
    (hθ : Mono (structureModulePullbackMap B S hS g)) :
    IsIso (conormalMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) :=
  have := hι
  have := hθ
  isIso_conormalMap_preimage_of_mono_comp B S hS g Z' (mono_comp _ _)

end AlgebraicGeometry.Space

end
