module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor
public import StacksFrontier.CategoryTheory.Sites.CharacterTwist

/-!
# The twist of the integers by a character of a group acting on an étale space

Let `X` be an algebraic space over a scheme `S`, let `W` be an algebraic space étale over `X`
and let a group `G` act on `W` by automorphisms over `X`. A character `χ : G → ℤˣ` twists the
extension by zero `j_{W!} ℤ` of the constant sheaf `ℤ`: the quotient `ℤ(χ)` of `j_{W!} ℤ`
which identifies the universal section at a morphism `φ : V ⟶ W` of the spaces-étale site of
`X` with `χ g` times the universal section at `g ∘ φ`. Its defining property, and the reason
Stacks 0727 introduces it, is that a map `ℤ(χ) ⟶ F` of abelian sheaves on `X_étale` is the
same thing as a section of `F` over `W` transforming according to `χ`, that is an element of
`H⁰(W, F|_W)^χ`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantCharacterTwistProjection`
  exhibits `ℤ(χ)` as a quotient of `j_{W!} ℤ`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantCharacterTwistProjection_generator`:
  the quotient map from `j_{W!} ℤ` carries the universal section at `φ : V ⟶ W` to the class
  of `φ`.

The identification of maps `ℤ(χ) ⟶ F` with the elements of `H⁰(W, F|_W)^χ`, naturally in
`F`, is `CategoryTheory.characterTwistHomEquiv` and
`CategoryTheory.characterTwistHomEquiv_comp`, read at the topology
`AlgebraicGeometry.Space.SpacesEtale.topology`.

## Implementation notes

The twist, the group `H⁰(W, F|_W)^χ` of sections transforming according to `χ` and the
identification between maps out of the twist and such sections are the general construction
of `StacksFrontier.CategoryTheory.Sites.CharacterTwist`, which needs nothing of the geometry:
the quotient of the free abelian sheaf on `W` by the relations imposed by `χ` makes sense on
any site. What is particular to the spaces-étale site is the comparison with extension by
zero, which goes through
`AlgebraicGeometry.Space.SpacesEtale.extensionByZeroConstantFreeRepresentableIso`: `j_{W!} ℤ`
is the free abelian sheaf on the representable presheaf of `W`, and `ℤ(χ)` is its quotient by
the relations imposed by `χ`.

Stacks 0727 asks for `W` with a free action of a finite group `G` and for `X` the quotient
`W/G`, and then concludes further that `ℤ(χ)` is locally free of rank one and that
`H⁰(W, F|_W)^χ` is `H⁰(X, F ⊗_ℤ ℤ(χ))`. Both of those rest on the triviality of `W ×_X W`
over `W` as a `G`-set, which is where the freeness and the finiteness of `G` enter and which
needs `X` to be the quotient of `W` by `G`; that quotient is not available as an algebraic
space in this library, since
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf` still carries two undischarged
effective-descent hypotheses. The construction and the identification of sections below are
independent of all of that: they hold for any action of any group on any object of the site.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space.SpacesEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : AlgebraicSpaces B S hS} (W : SpacesEtale B S hS X)
    {G : Type v} [Group G] (act : G →* Aut W) (χ : G →* ℤˣ)

/-- The composite of the identification of `j_{W!} ℤ` with the free abelian sheaf on the
representable presheaf of `W` and the quotient map onto the twist. -/
def extensionByZeroConstantCharacterTwistProjection :
    extensionByZeroConstant B S hS X W ⟶ characterTwist W act χ (topology B S hS X) :=
  (extensionByZeroConstantFreeRepresentableIso B S hS X W).hom ≫
    freeYonedaCharacterTwistProjection W act χ (topology B S hS X)

/-- Transported along the identification of the free abelian sheaf on `W` with `j_{W!} ℤ`,
the quotient map onto the twist is the sheafification of the quotient map of presheaves. -/
lemma freeRepresentableToExtensionByZeroConstant_comp_characterTwistProjection :
    freeRepresentableToExtensionByZeroConstant B S hS X W ≫
        extensionByZeroConstantCharacterTwistProjection W act χ =
      (presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
        (freeYonedaCharacterTwistProjectionPresheaf W act χ) :=
  Iso.inv_hom_id_assoc (extensionByZeroConstantFreeRepresentableIso B S hS X W) _

/-- The universal section of `j_{W!} ℤ` at `φ : V ⟶ W`, followed by the quotient map onto the
twist, is the class of `φ`. -/
lemma extensionByZeroConstantCharacterTwistProjection_generator
    {V : SpacesEtale B S hS X} (φ : V ⟶ W) :
    ((extensionByZeroConstantCharacterTwistProjection W act χ).hom.app (op V))
        (extensionByZeroConstantGenerator B S hS X W V φ) =
      (toSheafify (topology B S hS X) (characterTwistPresheaf W act χ)).app (op V)
        (twistedGenerator W act χ φ) := by
  have hgen : (((freeAbelianRepresentableSheaf B S hS X).obj W).obj.map φ.op)
      (freeAbelianRepresentableGenerator B S hS X W) =
    (toSheafify (topology B S hS X) (yoneda.obj W ⋙ AddCommGrpCat.free)).app (op V)
      (FreeAbelianGroup.of φ) := by
    rw [freeAbelianRepresentableGenerator_eq]
    have hnat := NatTrans.naturality_apply
      (toSheafify (topology B S hS X) (yoneda.obj W ⋙ AddCommGrpCat.free)) φ.op
      (FreeAbelianGroup.of (𝟙 W))
    exact hnat.symm.trans (congrArg
      (fun x => ((toSheafify (topology B S hS X)
        (yoneda.obj W ⋙ AddCommGrpCat.free)).app (op V)) x)
      (congrArg FreeAbelianGroup.of (Category.comp_id φ)))
  have key : ∀ y : (((freeAbelianRepresentableSheaf B S hS X).obj W).obj.obj (op V)),
      ((extensionByZeroConstantCharacterTwistProjection W act χ).hom.app (op V))
          (((freeRepresentableToExtensionByZeroConstant B S hS X W).hom.app (op V)) y) =
        ((((presheafToSheaf (topology B S hS X) AddCommGrpCat.{u + 1}).map
          (freeYonedaCharacterTwistProjectionPresheaf W act χ)).hom).app (op V)) y :=
    fun y => congrArg (fun k => (k.hom.app (op V)) y)
      (freeRepresentableToExtensionByZeroConstant_comp_characterTwistProjection W act χ)
  rw [← freeRepresentableToExtensionByZeroConstant_generatorAt B S hS X W V φ, key, hgen]
  exact (congrArg (fun k => (k.app (op V)) (FreeAbelianGroup.of φ))
    (toSheafify_naturality (topology B S hS X)
      (freeYonedaCharacterTwistProjectionPresheaf W act χ))).symm

end AlgebraicGeometry.Space.SpacesEtale

end
