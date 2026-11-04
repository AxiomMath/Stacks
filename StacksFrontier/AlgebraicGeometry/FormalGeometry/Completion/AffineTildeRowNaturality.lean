module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality

/-!
# The termwise affine tensor comparison is natural in the module variable

`AlgebraicGeometry.tildeTensorRowIso P N` identifies the associated sheaf of the termwise tensor
product `P ⊗_R N` of a complex of `R`-modules with a module,

`(P ⊗_R N)^\sim ≅ rowComplex (⊗_{𝒪_{Spec R}}) P^\sim N^\sim`,

for a *fixed* `N`. The affine projection formula

`RΓ(V, K ⊗^𝐋_{𝒪_X} 𝒪_X/ℐⁿ) ≅ RΓ(V, K) ⊗^𝐋_A A/Iⁿ`

that part (2) of [Stacks, Tag 0A0K] consumes is required **naturally in `n`**, and the adic
quotient tower is a diagram in the module variable; so an objectwise comparison transports
nothing. This file proves the square.

## The content is the naturality of Tag 01I8 in one variable

`AlgebraicGeometry.tildeTensorIso_natural` is the naturality of the affine tensor comparison of
[Stacks, Tag 01I8] in *both* module variables, phrased with
`AlgebraicGeometry.tildeTensorSheafMap`. Setting the first argument to an identity leaves the
square this file needs, and `Stacks.Algebraization.tildeTensorSheafMap_id_left` identifies the
resulting map with the action of `⊗_{𝒪_{Spec R}}` in its second variable — the mirror of the
first-variable identification that `AlgebraicGeometry.DerivedTildeTorAmplitude` already makes
for the opposite square. The differentials need no attention: they act on the *first* factor, so
the two squares of the chain-map condition are disjoint.

## Main results

* `Stacks.Algebraization.tildeTensorSheafMap_id_left` — `AlgebraicGeometry.tildeTensorSheafMap`
  with an identity in its first argument is `⊗_{𝒪_{Spec R}}` applied to `N^\sim ⟶ N'^\sim` in its
  second variable.
* `Stacks.Algebraization.tildeTensorComplexMap` — the termwise tensor product of a fixed complex
  `P` of `R`-modules is functorial in the module variable, by whiskering.
* `Stacks.Algebraization.tildeRowIso_hom_naturality` — **the naturality square**: the comparison
  commutes with `Stacks.Algebraization.tildeTensorComplexMap` on the left and
  `CochainComplex.KFlatBifunctor.rowComplexMapRight` on the right.

The square is left as an equation rather than packaged as an isomorphism of functors
`ModuleCat R ⥤ CochainComplex (𝒪_{Spec R}\text{-Mod}) ℤ`. Writing that functor out names the
row complex with no expression of the sheaf category to anchor it, and the additivity instances
of `⊗_{𝒪_{Spec R}}` are then searched for before unification has determined which spelling of
that category is meant. At a use site the `AlgebraicGeometry.tildeTensorRowIso` of the diagram
being compared supplies the anchor, so `CategoryTheory.NatIso.ofComponents` applied to this
equation there costs nothing.

## What is not done

No `@[stacks]` attribute is attached. [Stacks, Tag 01I8] is already carried by
`AlgebraicGeometry.tildeTensorIso` and `AlgebraicGeometry.tildeTensorIso_natural`, which is what
is applied here; promoting an objectwise comparison of this library's packaging to a natural one
is not a statement of the source.

This is naturality in the module variable only. The derived-category links of the projection
formula — `Stacks.Algebraization.derivedTensorSingleIsoRowComplex` and
`AlgebraicGeometry.derivedTensorTildeIso` — are still objectwise, and so is the
`Γ`-computes-`RΓ` comparison `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde`;
those remain to be made natural before the tower-level formula can be assembled.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace Stacks.Algebraization

variable (R : CommRingCat.{u})

/-- **`AlgebraicGeometry.tildeTensorSheafMap` with an identity first argument acts in the second
variable of `⊗_{𝒪_{Spec R}}`.** This is the mirror of the first-variable identification
`tildeTensorSheafMap_id` of `StacksFrontier/AlgebraicGeometry/DerivedTildeTorAmplitude.lean`, and is
proved the same way: both sides are the sheafification of the monoidal tensor of two morphisms of
presheaves of modules, one of which is an identity, and `AlgebraicGeometry.tilde.map_id` turns
that identity into the identity of the sheaf before the two unfold to the same term. -/
public theorem tildeTensorSheafMap_id_left (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') :
    tildeTensorSheafMap R (𝟙 M) g =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u}
        (AlgebraicGeometry.specCommRingSheaf R)).obj (tilde M)).map (tilde.map g) := by
  unfold tildeTensorSheafMap Stacks.SheafOfModules.Tensor.sheafTensor
  rw [tilde.map_id]
  rfl

variable (P : CochainComplex (ModuleCat.{u} R) ℤ)

/-- **The termwise tensor product of a fixed complex is functorial in the module variable.** For
`g : N ⟶ N'` the degreewise maps `Pᵖ ◁ g` commute with the differentials `d_P ▷ N`, by
`CategoryTheory.MonoidalCategory.whisker_exchange`: the differentials act on the first factor and
`g` on the second. -/
public def tildeTensorComplexMap {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    StacksDraft.TorAmplitude.Termwise.tensorComplex P N ⟶
      StacksDraft.TorAmplitude.Termwise.tensorComplex P N' where
  f p := P.X p ◁ g
  comm' p p' _ := whisker_exchange (P.d p p') g

/-- The degreewise formula for `Stacks.Algebraization.tildeTensorComplexMap`. -/
@[simp]
public lemma tildeTensorComplexMap_f {N N' : ModuleCat.{u} R} (g : N ⟶ N') (p : ℤ) :
    (tildeTensorComplexMap R P g).f p = P.X p ◁ g := rfl

/-- `Stacks.Algebraization.tildeTensorComplexMap` at an identity is the identity. -/
@[simp]
public lemma tildeTensorComplexMap_id (N : ModuleCat.{u} R) :
    tildeTensorComplexMap R P (𝟙 N) =
      𝟙 (StacksDraft.TorAmplitude.Termwise.tensorComplex P N) :=
  HomologicalComplex.hom_ext _ _ fun p => MonoidalCategory.whiskerLeft_id (P.X p) N

/-- `Stacks.Algebraization.tildeTensorComplexMap` of a composite is the composite. -/
@[simp]
public lemma tildeTensorComplexMap_comp {N N' N'' : ModuleCat.{u} R} (g : N ⟶ N')
    (g' : N' ⟶ N'') :
    tildeTensorComplexMap R P (g ≫ g') =
      tildeTensorComplexMap R P g ≫ tildeTensorComplexMap R P g' :=
  HomologicalComplex.hom_ext _ _ fun p => MonoidalCategory.whiskerLeft_comp (P.X p) g g'

/-- **The termwise tensor product of a fixed complex, as a functor of the module variable.** -/
public def tildeTensorComplexFunctor :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj N := StacksDraft.TorAmplitude.Termwise.tensorComplex P N
  map g := tildeTensorComplexMap R P g
  map_id N := tildeTensorComplexMap_id R P N
  map_comp g g' := tildeTensorComplexMap_comp R P g g'

/-- **The termwise affine tensor comparison is natural in the module variable.** For
`g : N ⟶ N'` the square

`(P ⊗_R N)^\sim ⟶ (P ⊗_R N')^\sim`, `rowComplex P^\sim N^\sim ⟶ rowComplex P^\sim N'^\sim`

commutes. In each degree `p` this is `AlgebraicGeometry.tildeTensorIso_natural` with the first
argument the identity of `Pᵖ`, read through
`CategoryTheory.MonoidalCategory.id_tensorHom` on the left and
`Stacks.Algebraization.tildeTensorSheafMap_id_left` on the right. -/
public theorem tildeRowIso_hom_naturality {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (tildeTensorComplexMap R P g) ≫ (AlgebraicGeometry.tildeTensorRowIso P N').hom =
      (AlgebraicGeometry.tildeTensorRowIso P N).hom ≫
        CochainComplex.KFlatBifunctor.rowComplexMapRight
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u}
            (AlgebraicGeometry.specCommRingSheaf R))
          (AlgebraicGeometry.tildeComplexMod P) (tilde.map g) := by
  apply HomologicalComplex.hom_ext
  intro p
  refine Eq.trans (congrArg (fun z => tilde.map z ≫ (tildeTensorIso R (P.X p) N').hom)
    (MonoidalCategory.id_tensorHom (P.X p) g).symm) ?_
  refine Eq.trans (tildeTensorIso_natural R (𝟙 (P.X p)) g) ?_
  exact congrArg (fun z => (tildeTensorIso R (P.X p) N).hom ≫ z)
    (tildeTensorSheafMap_id_left R (P.X p) g)

end Stacks.Algebraization

end
