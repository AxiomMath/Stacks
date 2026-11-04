module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalEtaleRestrictionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedIdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComp

/-!
# The ideal-sheaf level of part (2) of Stacks 04G2, in the closed case

Let
```
R --j--> V
|        |
b        a
↓        ↓
R' -j'-> V'
```
be a commutative square of the big fppf category over a scheme `S` contained in a big fppf site
`B`, with the two underlying morphisms of schemes `j` and `j'` closed immersions.  Two maps of
sheaves of ideals are attached to it.

* The **spaces** one.  `AlgebraicGeometry.Space.kernelIdealSquareMap` in degree one is the map
  `g^*Ker((i')^♯) ⟶ Ker(i^♯)` of the represented square of algebraic spaces, which is the step
  `g^♯(𝓘') ⊆ 𝓘` of the proof of [Stacks Project, Tag 04CP].
* The **schemes** one.  `Stacks.ClosedImmersion.idealSheafMap` is the map `a^*ℐ_{j'} ⟶ ℐ_j` of
  Morphisms, Lemma [Stacks Project, Tag 01R4], induced by `a^♯`.

This file proves that they agree, across the identification of the two sheaves of ideals of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiDefiningIdeal.lean` and the transport of
the inverse image of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`.  That is the
**ideal-sheaf level** of part (2) of [Stacks Project, Tag 04G2]: both canonical maps of conormal
modules factor as a square comparison followed by the inverse image along the upper morphism of
exactly these maps of ideal sheaves, and the two square comparisons are already compared at the
structure sheaf.

## Main results

* `AlgebraicGeometry.Space.representedSpaceMap_square_of_comp_eq` and
  `AlgebraicGeometry.Space.toShHom_square_of_comp_eq`: the commutative square of the big fppf
  category gives the commutative square of represented algebraic spaces and the commutative
  square of the underlying morphisms of ringed spaces.  The first rests on the composition law
  `AlgebraicGeometry.Space.representedSpaceMap_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRepresentableBaseChangeComp.lean`.  Both
  hypotheses of the main statement are therefore satisfied by any commutative square of the site,
  so nothing below is empty.
* `AlgebraicGeometry.Space.kernelIdealSheafZPow_one_representedSpaceMap`: for a represented
  closed immersion the degree-one piece of the kernel ideal sheaf is the defining ideal sheaf of
  Stacks 03MB of the closed subspace it cuts out.
* `AlgebraicGeometry.Space.representedAssociatedModuleKernelIdealZPowIso`: consequently
  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` reads as an identification of
  the degree-one piece of the kernel ideal sheaf with the associated module of
  `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes, and
  `AlgebraicGeometry.Space.representedAssociatedModuleKernelIdealZPowIso_hom_comp_ι` is its
  compatibility with the inclusions into the two structure sheaves.
* `AlgebraicGeometry.Space.kernelIdealSquareMap_representedAssociatedModuleKernelIdealZPowIso`:
  **the two maps of ideal sheaves agree.**
* `CategoryTheory.comp_eq_map_comp_of_mono_comparison`: the formal content of that agreement,
  stated for six functors and the six equations in an arbitrary pair of squares of categories.

## Route

Both maps of ideal sheaves are determined by their composite with the inclusion of the target
sheaf of ideals into the structure sheaf, which is a monomorphism: schemes-side that composite is
`Stacks.ClosedImmersion.idealSheafMap_comp_ι`, spaces-side it is
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`, and both say "the inverse image of the
inclusion followed by pullback of regular functions".  So the agreement follows from

* the compatibility of the ideal-sheaf identification with the two inclusions, which is
  `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso_hom_comp_ι_comp` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedIdealSheafInclusion.lean`, carried
  across the equality of sheaves of ideals above;
* the **naturality in the module** of
  `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso`, which moves the transport of
  the inverse image past the inclusion; and
* its **unit-module compatibility**
  `AlgebraicGeometry.Space.structureModulePullbackMap_representedAssociatedModulePullbackIso`,
  which says that the transport carries pullback of regular functions along the represented
  morphism to the associated module of pullback of regular functions along the morphism of
  schemes.

## Implementation notes

Three measurements decide the shape of this file; all three are instances of the same rule, that
at this scale the cost is dominated by whether the elaborator is handed a term or has to find it.

**The generic lemma takes every morphism as an implicit argument determined by one of its six
hypotheses.**  With the two transposes passed explicitly instead — that is, with the right-hand
side of a hypothesis restated at the geometric instance — the cognate step of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedIdealSheafInclusion.lean` is an
`isDefEq` timeout; here the same change is a `whnf` timeout.

**Four objects must nevertheless be pinned at the instantiation**: the two structure sheaves of
the representing schemes, in the `AlgebraicGeometry.Scheme.ringCatSheaf` spelling, and the two
structure sheaves of their small étale sites.  Left to unification the elaborator meets
`F.obj ?O =?= CategoryTheory.SheafOfModules.unit (AlgebraicGeometry.Space.structureRingSheaf …)`
with `?O` a metavariable under a functor's `obj`, which is not a pattern, and weak-head
normalising the transport of the inverse image to decide it exhausts the budget.  With the four
objects given, the file checks in about twelve seconds.  The same applies to
`Stacks.ClosedImmersion.idealSheafMap`, whose four implicit morphisms are written out: left to
unification against the expected type the statement alone is a `whnf` timeout, and with them
written out it is free.

**The monomorphism is an explicit argument.**  `Mono` of the inclusion of the degree-one piece of
the kernel ideal sheaf is an instance, but instance search for it inside the application of the
generic lemma fails; supplied as a term through an explicit argument it is immediate.  This is the
same shape as the invertibility hypotheses of a transport lemma having to be explicit.

**Not** needed here, contrary to the practice of the neighbouring files:
`attribute [local irreducible] modulePullback modulePullbackCompIso`.  With the four objects
pinned nothing asks for the inverse image to be unfolded, and the attribute changes neither the
outcome nor the time.

No declaration here carries a `stacks` tag.  What is proved is the ideal-sheaf level of part (2)
of Stacks 04G2 and not part (2) itself: the passage from the ideal sheaves to the conormal modules
is the inverse image along the upper morphism of the square together with the comparison of the
two square comparisons, and that is not asserted here.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), part (2).
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the spaces-side
  canonical map whose ideal-sheaf factor this is.
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4), the schemes-side one.
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), the defining ideal sheaf
  of a closed subspace.
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC), part (1), the base change
  of the associated module which the transport is built from.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

/-- **Two maps into a subobject agree when their composites with its inclusion do.**

The situation is two squares of categories, `Q` over `P` through `A`, `A'` and `F`, `F'`, with:
subobjects `Iₛ ⊆ Oₛ` and `Iₛ' ⊆ Oₛ'` downstairs, given by `ιₛ` and `ιₛ'`; comparisons `Ψ`, `Ψ'`
of their images under `F ∘ A` and `F' ∘ A'` with objects `NP`, `NP'` carrying monomorphisms `ιP`,
`ιP'` into the images of `O`, `O'`; a map `mₛ : Q.obj Iₛ' ⟶ Iₛ` and a map `mP : P.obj NP' ⟶ NP`,
each described by its composite with the inclusion; and a comparison `Ξ` of the two routes round
the square, natural in the object and compatible with the maps `ν`, `ν'`, `νₐ`, `θ` out of the
`O`'s.  Then `mₛ` and `mP` agree through `Ψ`, `Ψ'` and `Ξ`.

Every morphism is an **implicit** argument, determined by the hypothesis naming it; a consumer
therefore supplies six existing lemmas and restates nothing.  That is what makes this usable at a
geometric instance — see the implementation notes of this file. -/
theorem comp_eq_map_comp_of_mono_comparison
    {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
    {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']
    {E : Type u₅} [Category.{v₅} E] {E' : Type u₆} [Category.{v₆} E']
    (F : E ⥤ C) (F' : E' ⥤ C') (A : D ⥤ E) (A' : D' ⥤ E') (P : C' ⥤ C) (Q : D' ⥤ D)
    {Iₛ Oₛ : D} {Iₛ' Oₛ' : D'} {O : E} {O' : E'} {NP : C} {NP' : C'}
    {ιₛ : Iₛ ⟶ Oₛ} {ιₛ' : Iₛ' ⟶ Oₛ'} {ν : A.obj Oₛ ⟶ O} {ν' : A'.obj Oₛ' ⟶ O'}
    {mₛ : Q.obj Iₛ' ⟶ Iₛ} {νₐ : Q.obj Oₛ' ⟶ Oₛ}
    {Ψ : F.obj (A.obj Iₛ) ≅ NP} {Ψ' : F'.obj (A'.obj Iₛ') ≅ NP'}
    {ιP : NP ⟶ F.obj O} {ιP' : NP' ⟶ F'.obj O'}
    {ΞI : P.obj (F'.obj (A'.obj Iₛ')) ≅ F.obj (A.obj (Q.obj Iₛ'))}
    {ΞO : P.obj (F'.obj (A'.obj Oₛ')) ≅ F.obj (A.obj (Q.obj Oₛ'))}
    {θ : P.obj (F'.obj O') ⟶ F.obj O} {mP : P.obj NP' ⟶ NP}
    (hunit : P.map (F'.map ν') ≫ θ = ΞO.hom ≫ F.map (A.map νₐ ≫ ν))
    (hΨ : Ψ.hom ≫ ιP = F.map (A.map ιₛ ≫ ν))
    (hΨ' : Ψ'.hom ≫ ιP' = F'.map (A'.map ιₛ' ≫ ν'))
    (hmₛ : mₛ ≫ ιₛ = Q.map ιₛ' ≫ νₐ)
    (hnat : P.map (F'.map (A'.map ιₛ')) ≫ ΞO.hom = ΞI.hom ≫ F.map (A.map (Q.map ιₛ')))
    (hmP : mP ≫ ιP = P.map ιP' ≫ θ) (hmono : Mono ιP) :
    ΞI.hom ≫ F.map (A.map mₛ) ≫ Ψ.hom = P.map Ψ'.hom ≫ mP := by
  have := hmono
  refine (cancel_mono (f := ιP)).1 ?_
  rw [Category.assoc, Category.assoc, hΨ, ← F.map_comp, ← Category.assoc (A.map mₛ),
    ← A.map_comp, hmₛ, A.map_comp, Category.assoc, F.map_comp, ← Category.assoc, ← hnat,
    Category.assoc, ← hunit, ← Category.assoc, ← P.map_comp, ← F'.map_comp]
  rw [Category.assoc (P.map Ψ'.hom), hmP, ← Category.assoc, ← P.map_comp, hΨ']

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two squares a commutative square of the site induces -/

/-- **Passing to represented algebraic spaces carries the identity to the identity.**  It is
`CategoryTheory.Functor.map_id` for `yoneda`, read in the full subcategory of algebraic spaces.
Unlike `AlgebraicGeometry.Space.representedSpaceMap_comp` this is *not* `rfl`: the Yoneda image of
an identity is the natural transformation `g ↦ g ≫ 𝟙`, which is the identity only after the unit
law of the site. -/
theorem representedSpaceMap_id (T : BigFppfOver B S hS) :
    representedSpaceMap B S hS (𝟙 T) =
      𝟙 (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.hom_ext _ (yoneda.map_id T)

variable {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')

/-- **A commutative square of the big fppf category gives a commutative square of represented
algebraic spaces.** -/
theorem representedSpaceMap_square_of_comp_eq (hsq : j ≫ a = b ≫ j') :
    representedSpaceMap B S hS j ≫ representedSpaceMap B S hS a =
      representedSpaceMap B S hS b ≫ representedSpaceMap B S hS j' :=
  (representedSpaceMap_comp B S hS j a).trans
    ((congrArg (fun m : R ⟶ V' => representedSpaceMap B S hS m) hsq).trans
      (representedSpaceMap_comp B S hS b j').symm)

/-- **A commutative square of the big fppf category gives a commutative square of the underlying
morphisms of ringed spaces.** -/
theorem toShHom_square_of_comp_eq (hsq : j ≫ a = b ≫ j') :
    ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom ≫
        ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom =
      ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom ≫
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom :=
  congrArg (fun m : R ⟶ V' => ((BigFppfOver.toScheme B S hS).map m).toLRSHom.toShHom) hsq

/-! ### The ideal-sheaf identification at the degree-one piece of the kernel ideal sheaf -/

variable (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- **For a represented closed immersion the degree-one piece of the kernel ideal sheaf is the
defining ideal sheaf of the closed subspace it cuts out.**  This is
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one` followed by
`AlgebraicGeometry.Space.kernelIdealSheaf_representedSpaceMap`. -/
theorem kernelIdealSheafZPow_one_representedSpaceMap :
    kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j) 1 =
      definingIdealSheaf B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
        (closedSubspaceRange B S hS j hj) :=
  (kernelIdealSheafZPow_one B S hS (representedSpaceMap B S hS j)).trans
    (kernelIdealSheaf_representedSpaceMap B S hS j hj)

/-- **The degree-one piece of the kernel ideal sheaf of a represented closed immersion is the
associated module of `Stacks.ClosedImmersion.idealSheaf` of the underlying morphism of schemes.**

This is `AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso` read across
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one_representedSpaceMap`, which is the spelling the
canonical map of [Stacks Project, Tag 04CP] is stated at. -/
def representedAssociatedModuleKernelIdealZPowIso :
    (representedSmallEtaleModuleEquivalence B S hS V).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj
          (Stacks.ClosedImmersion.idealSheaf
            ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)) ≅
      (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j) 1).toSheafOfModules :=
  representedAssociatedModuleIdealSheafIso B S hS V j hj ≪≫
    eqToIso (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
          ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule => N.toSheafOfModules)
      (kernelIdealSheafZPow_one_representedSpaceMap B S hS j hj).symm)

/-- **The identification respects the inclusions into the two structure sheaves.**  This is
`AlgebraicGeometry.Space.representedAssociatedModuleIdealSheafIso_hom_comp_ι_comp` carried across
the equality of sheaves of ideals, an equality being compatible with the inclusions by
`Stacks.SheafOfModules.Submodule.eqToHom_comp_ι`. -/
theorem representedAssociatedModuleKernelIdealZPowIso_hom_comp_ι :
    (representedAssociatedModuleKernelIdealZPowIso B S hS j hj).hom ≫
        (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j) 1).ι =
      (representedSmallEtaleModuleEquivalence B S hS V).functor.map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              (Stacks.ClosedImmersion.idealSheafι
                ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom) ≫
          SheafOfModules.pullbackObjUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => (representedAssociatedModuleIdealSheafIso B S hS V j hj).hom ≫ t)
        (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι
          (kernelIdealSheafZPow_one_representedSpaceMap B S hS j hj).symm
          (congrArg
            (fun N : (SheafOfModules.unit (structureRingSheaf B S hS
                ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)).Submodule =>
              N.toSheafOfModules)
            (kernelIdealSheafZPow_one_representedSpaceMap B S hS j hj).symm))).trans
      (representedAssociatedModuleIdealSheafIso_hom_comp_ι_comp B S hS V j hj))

/-! ### The two maps of ideal sheaves agree -/

variable (hj' : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j'))

/-- **The ideal-sheaf level of part (2) of [Stacks Project, Tag 04G2], in the closed case.**

For a commutative square of the big fppf category over `S` whose horizontal morphisms are closed
immersions of schemes, the map of sheaves of ideals `g^*Ker((i')^♯) ⟶ Ker(i^♯)` of
`AlgebraicGeometry.Space.kernelIdealSquareMap` in degree one is the associated module of the map
`a^*ℐ_{j'} ⟶ ℐ_j` of Morphisms, Lemma [Stacks Project, Tag 01R4], read across the transport of
the inverse image `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` and the two
identifications `AlgebraicGeometry.Space.representedAssociatedModuleKernelIdealZPowIso`.

Both maps are determined by their composite with the inclusion of the target sheaf of ideals into
the structure sheaf, which is a monomorphism; those two composites are
`Stacks.ClosedImmersion.idealSheafMap_comp_ι` and
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`, and the identification is compatible with
the inclusions.  The two commutativity hypotheses are supplied, for any commutative square of the
site, by `AlgebraicGeometry.Space.representedSpaceMap_square_of_comp_eq` and
`AlgebraicGeometry.Space.toShHom_square_of_comp_eq`. -/
theorem kernelIdealSquareMap_representedAssociatedModuleKernelIdealZPowIso
    (hsq : representedSpaceMap B S hS j ≫ representedSpaceMap B S hS a =
      representedSpaceMap B S hS b ≫ representedSpaceMap B S hS j')
    (comm : ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom ≫
          ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom =
        ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom ≫
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) :
    (representedAssociatedModulePullbackIso B S hS a
            (relativelyRepresentable_yoneda_map B S hS a)
            (Stacks.ClosedImmersion.idealSheaf
              ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS V).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj V) V.left.property).map
              (Stacks.ClosedImmersion.idealSheafMap
                (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
                (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
                (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
                (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom) comm)) ≫
          (representedAssociatedModuleKernelIdealZPowIso B S hS j hj).hom =
      (modulePullback B S hS (representedSpaceMap B S hS a)).map
          (representedAssociatedModuleKernelIdealZPowIso B S hS j' hj').hom ≫
        kernelIdealSquareMap B S hS (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
          (representedSpaceMap B S hS a) hsq 1 := by
  have hunit := structureModulePullbackMap_representedAssociatedModulePullbackIso B S hS a
    (relativelyRepresentable_yoneda_map B S hS a)
  have hΨ := representedAssociatedModuleKernelIdealZPowIso_hom_comp_ι B S hS j hj
  have hΨ' := representedAssociatedModuleKernelIdealZPowIso_hom_comp_ι B S hS j' hj'
  have hmₛ := Stacks.ClosedImmersion.idealSheafMap_comp_ι
    (i := ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)
    (j := ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
    (f := ((BigFppfOver.toScheme B S hS).map b).toLRSHom.toShHom)
    (k := ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom) comm
  have hnat := representedAssociatedModulePullbackIso_naturality B S hS a
    (relativelyRepresentable_yoneda_map B S hS a)
    (𝓖 := SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj V').ringCatSheaf)
    (Stacks.ClosedImmersion.idealSheafι
      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom)
  have hmP := kernelIdealSquareMap_comp_ι B S hS (representedSpaceMap B S hS j)
    (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
    (representedSpaceMap B S hS a) hsq 1
  have hmono : Mono (kernelIdealSheafZPow B S hS (representedSpaceMap B S hS j) 1).ι :=
    inferInstance
  exact CategoryTheory.comp_eq_map_comp_of_mono_comparison
    (Oₛ := SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf)
    (Oₛ' := SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj V').ringCatSheaf)
    (O := SheafOfModules.unit (representedSchemeStructureSheaf B S hS V))
    (O' := SheafOfModules.unit (representedSchemeStructureSheaf B S hS V'))
    (representedSmallEtaleModuleEquivalence B S hS V).functor
    (representedSmallEtaleModuleEquivalence B S hS V').functor
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V') V'.left.property)
    (modulePullback B S hS (representedSpaceMap B S hS a))
    (Scheme.Modules.pullback (B.inclusion.map a.left))
    hunit hΨ hΨ' hmₛ hnat hmP hmono

end AlgebraicGeometry.Space

end
