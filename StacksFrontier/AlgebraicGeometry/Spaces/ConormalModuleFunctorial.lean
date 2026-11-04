module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso

/-!
# Functoriality of the conormal module of a closed subspace of an algebraic space

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
in which `Z` is a closed subspace of `X` and `Z'` is a closed subspace of `X'`, with `i` and `i'`
the inclusions.  This file constructs the canonical map of `𝒪_Z`-modules
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of Stacks 04CP between the conormal modules of
`AlgebraicGeometry.Space.conormalModule`.

The construction is the one of the source.  Since `g ∘ i` factors through `Z'`, the composite
`g^{-1}𝓘' ⟶ g^{-1}𝒪_{X'} ⟶ 𝒪_X ⟶ i_*𝒪_Z` vanishes, so the defining ideal sheaf `𝓘'` of `Z'`
is carried into the defining ideal sheaf `𝓘` of `Z` by pullback of regular functions along `g`;
that is the map `g^*𝓘' ⟶ 𝓘` of `AlgebraicGeometry.Space.idealSheafMap`.  Pulling it back along
`i` and reading `i^*g^* = (i ≫ g)^* = (f ≫ i')^* = f^*(i')^*` through the Stacks 03LU
composition comparison gives
`f^*𝒞_{Z'/X'} = f^*(i')^*𝓘' ⟶ i^*g^*𝓘' ⟶ i^*𝓘 = 𝒞_{Z/X}`.

## Main definitions

* `AlgebraicGeometry.Space.idealSheafFMap`: the chartwise linear map of sections along `g` from
  the defining ideal sheaf of `Z` to that of `Z'`, given by pullback of regular functions along
  the vertical morphism of a chart diagram.
* `AlgebraicGeometry.Space.idealSheafMap`: the morphism `g^*𝓘' ⟶ 𝓘` of `𝒪_X`-modules obtained
  from it by transposing twice.
* `AlgebraicGeometry.Space.conormalPullbackCompIso`: the identification
  `f^*(i')^* ≅ i^*g^*` of inverse-image functors furnished by the commutative square.
* `AlgebraicGeometry.Space.conormalPullbackComparison`: its component at the defining ideal
  sheaf of `Z'`, read as a morphism `f^*𝒞_{Z'/X'} ⟶ i^*g^*𝓘'`.
* `AlgebraicGeometry.Space.conormalMap`: **Stacks 04CP for closed immersions**, the canonical
  map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of conormal modules.

## Main results

* `AlgebraicGeometry.Space.mem_definingIdealAt_chartDiagramPullback`: the arithmetic heart of
  the construction.  Pullback of regular functions along the vertical morphism of a chart
  diagram over `g` carries the defining ideal of `Z'` into the defining ideal of `Z`.  This is
  the step `g^♯(𝓘') ⊆ 𝓘` of the proof of Stacks 04CP.
* `AlgebraicGeometry.Space.idealSheafFMap_app_coe`: the chartwise formula for
  `AlgebraicGeometry.Space.idealSheafFMap`.
* `AlgebraicGeometry.Space.idealSheafMap_transpose`: the characterising property of
  `AlgebraicGeometry.Space.idealSheafMap`.  Its double transpose under the Stacks 03LU
  adjunction and the chartwise universal property of the direct image is the chartwise map, so
  the morphism is pinned down by the formula on sections.
* `AlgebraicGeometry.Space.isIso_conormalPullbackComparison`: the comparison factor of the
  canonical map is an isomorphism, being a component of a natural isomorphism.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_isIso_idealSheafMap`: a square whose map of
  defining ideal sheaves is invertible has an invertible map of conormal modules.

## Implementation notes

**Why closed subspaces and not immersions.**  Stacks 04CP is stated for a square in which `i`
and `i'` are immersions, and its proof reduces at once to the closed case: open subspaces
`U ⊆ X` and `U' ⊆ X'` with `g(U) ⊆ U'` are chosen so that `i(Z) ⊆ U` and `i'(Z') ⊆ U'` are
closed, and `X`, `X'` are replaced by them.  The statement below is that closed case, stated for
`AlgebraicGeometry.Space.conormalModule`, which is defined for a
`AlgebraicGeometry.Space.ClosedSubspaces`.  The tag at its own generality — arbitrary
immersions — is `AlgebraicGeometry.Space.conormalMapOfImmersions` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean`, built on the
conormal module of an immersion `AlgebraicGeometry.Space.immersionConormalModule`; the module
documentation there records how the source's choice of `U` and `U'` is discharged by the
canonical ambient `X ∖ ∂Z` of `AlgebraicGeometry.Space.immersionAmbient` and the Stacks 04CE
factorisation through it, and that the two maps are not identified with one another here.  The
subspaces are taken as objects of `AlgebraicGeometry.Space.ClosedSubspaces` rather than as
morphisms with a closed-immersion hypothesis because that is the shape in which every
statement about the defining ideal sheaf of Stacks 03MB is available.

**Why the map of ideal sheaves is built by transposing and not as a kernel lift.**  One category
down, in `StacksFrontier/AlgebraicGeometry/Thickenings/ConormalSheaf.lean`, the ideal sheaf of a
closed immersion of ringed spaces *is* a categorical kernel, and the corresponding map is
`CategoryTheory.Limits.kernel.lift` of the vanishing composite.  Here the defining ideal sheaf
is `AlgebraicGeometry.Space.definingIdealSheaf`, a
`CategoryTheory.SheafOfModules.Submodule` of the unit module given chartwise by the ideals
`AlgebraicGeometry.Space.definingIdealAt`, and no presentation of it as a kernel of a morphism
of `𝒪_X`-modules is available on the small étale site.  So the vanishing of the composite is
used in its chartwise form — `AlgebraicGeometry.Space.definingIdealAt_le_ker_of_comp_eq`, the
factorization half of Stacks 03MB — and the morphism of modules is obtained from the chartwise
map by transposing along the chartwise universal property of the direct image
(`AlgebraicGeometry.Space.modulePushforwardHomEquiv`, Stacks 03LU) and then along the
adjunction `g^* ⊣ g_*` (`AlgebraicGeometry.Space.modulePullbackAdjunction`, Stacks 03D7).

**The composition comparison used is the primed one.**
`AlgebraicGeometry.Space.modulePullbackCompIso` is the adjunction mate of the comparison of
direct images, so it is determined by the direct-image side and makes no second choice; it is
the comparison that `AlgebraicGeometry.Space.modulePullbackSquareIso` also uses, and
`AlgebraicGeometry.Space.conormalPullbackCompIso` below has the same three-step body with the
commutativity of the square in place of the cartesian hypothesis — none of which that
construction consumes either.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

/-! ### The map of defining ideal sheaves induced by a commutative square -/

/-- **A commutative square carries the defining ideal into the defining ideal.**  Let the square
of `AlgebraicGeometry.Space.subspaceInclusion`s commute, and let `d` be a commutative diagram of
étale scheme charts over `g`.  Then pullback of regular functions along the vertical morphism of
`d` carries the defining ideal of `Z'` at the chart of `X'` into the defining ideal of `Z` at the
chart of `X`.

This is the step `g^♯(𝓘') ⊆ 𝓘` of the proof of [Stacks Project, Tag 04CP]: the composite
`g^{-1}𝓘' ⟶ 𝒪_X ⟶ i_*𝒪_Z` vanishes because `g ∘ i` factors through `Z'`.  The vanishing is read
chartwise through `AlgebraicGeometry.Space.definingIdealAt_le_ker_of_comp_eq`, applied to the
point of `Z` given by the base change of the chart of `X` along the inclusion of `Z`. -/
theorem mem_definingIdealAt_chartDiagramPullback
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : ToType ((structureRingSheaf B S hS X').obj.obj (op d.V)))
    (hs : s ∈ definingIdealAt B S hS X' Z' (op d.V)) :
    chartDiagramPullback B S hS g d s ∈ definingIdealAt B S hS X Z (op d.U) := by
  have hy : yoneda.map (Z.2.2.rep.snd d.U.1.hom ≫ d.g) ≫ d.V.1.hom =
      Z.2.2.rep.fst d.U.1.hom ≫ (subspaceInclusion B S hS X Z ≫ g).hom := by
    rw [Functor.map_comp, Category.assoc, ← d.comm, ← Category.assoc, ← Z.2.2.rep.w,
      Category.assoc, ObjectProperty.FullSubcategory.comp_hom]
    rfl
  have key := definingIdealAt_le_ker_of_comp_eq B S hS X'
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) Z'
    (subspaceInclusion B S hS X Z ≫ g) f hsq.symm d.V
    (Z.2.2.rep.snd d.U.1.hom ≫ d.g) (Z.2.2.rep.fst d.U.1.hom) hy hs
  have hsplit : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (Z.2.2.rep.snd d.U.1.hom ≫ d.g)).op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd d.U.1.hom)).op := by
    rw [Functor.map_comp, op_comp, Functor.map_comp]
  have hker := RingHom.mem_ker.mp key
  rw [hsplit] at hker
  rw [definingIdealAt_eq_ker]
  exact RingHom.mem_ker.mpr hker

/-- **The chartwise map of defining ideal sheaves of a commutative square.**  The linear map of
sections along `g` which, on a commutative diagram of étale scheme charts, is pullback of regular
functions along the vertical morphism, corestricted to the defining ideals.

It is well defined by
`AlgebraicGeometry.Space.mem_definingIdealAt_chartDiagramPullback`; additivity and
semilinearity hold because it is a restriction of a homomorphism of rings whose coefficient map
is the same pullback of regular functions. -/
noncomputable def idealSheafFMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    ModuleFMap B S hS g (definingIdealSheaf B S hS X Z).toSheafOfModules
      (definingIdealSheaf B S hS X' Z').toSheafOfModules where
  app d s := ⟨chartDiagramPullback B S hS g d s.1,
    mem_definingIdealAt_chartDiagramPullback B S hS Z Z' g f hsq d s.1 s.2⟩
  naturality d d' i j hij s := by
    have hcomm : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X'.1).map j)).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d'.g).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map i)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← Functor.map_comp,
        ← Functor.map_comp, hij]
    exact Subtype.ext (ConcreteCategory.congr_hom hcomm s.1)
  map_add d s t := Subtype.ext (map_add (chartDiagramPullback B S hS g d).hom s.1 t.1)
  map_smul d r s := Subtype.ext (map_mul (chartDiagramPullback B S hS g d).hom r s.1)

/-- **The map of defining ideal sheaves induced by a commutative square**, `g^*𝓘' ⟶ 𝓘`: the
transpose along the Stacks 03D7 adjunction `g^* ⊣ g_*` of the transpose along the chartwise
universal property of the direct image of `AlgebraicGeometry.Space.idealSheafFMap`.

This realizes the map `g^{-1}𝓘' ⟶ 𝓘` of the proof of [Stacks Project, Tag 04CP] as a morphism of
`𝒪_X`-modules out of the inverse image. -/
noncomputable def idealSheafMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    (modulePullback B S hS g).obj (definingIdealSheaf B S hS X' Z').toSheafOfModules ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  ((modulePullbackAdjunction B S hS g).homEquiv _ _).symm
    ((modulePushforwardHomEquiv B S hS g (definingIdealSheaf B S hS X Z).toSheafOfModules
      (definingIdealSheaf B S hS X' Z').toSheafOfModules).symm
        (idealSheafFMap B S hS Z Z' g f hsq))

/-- The chartwise formula for `AlgebraicGeometry.Space.idealSheafFMap`: on a commutative diagram
of étale scheme charts it is pullback of regular functions along the vertical morphism. -/
theorem idealSheafFMap_app_coe
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (definingIdealSheaf B S hS X' Z').toSheafOfModules.val.obj (op d.V)) :
    ((idealSheafFMap B S hS Z Z' g f hsq).app d s).1 =
      chartDiagramPullback B S hS g d s.1 :=
  rfl

/-- **The characterising property of `AlgebraicGeometry.Space.idealSheafMap`.**  Transposing it
back along the Stacks 03D7 adjunction and then along the chartwise universal property of the
direct image returns the chartwise map `AlgebraicGeometry.Space.idealSheafFMap`.

Both transposes are bijections, so this determines the morphism: together with
`AlgebraicGeometry.Space.idealSheafFMap_app_coe` it says that `idealSheafMap` is the map induced
by `g^♯` on sections, which is the description [Stacks Project, Tag 04CP] gives. -/
theorem idealSheafMap_transpose
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    modulePushforwardHomEquiv B S hS g (definingIdealSheaf B S hS X Z).toSheafOfModules
        (definingIdealSheaf B S hS X' Z').toSheafOfModules
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (idealSheafMap B S hS Z Z' g f hsq)) =
      idealSheafFMap B S hS Z Z' g f hsq := by
  rw [idealSheafMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ### The conormal module map of a commutative square -/

/-- **The identification `f^*(i')^* ≅ i^*g^*` furnished by a commutative square.**  The two
sides are the inverse images along the two ways around the square, compared by the Stacks 03LU
composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` on each side and the
commutativity of the square in the middle.

This is the identification `i^{-1}g^{-1} = f^{-1}(i')^{-1}` of the last step of the proof of
[Stacks Project, Tag 04CP].  It is `AlgebraicGeometry.Space.modulePullbackSquareIso` with the
cartesian hypothesis weakened to commutativity, which is all that construction uses. -/
noncomputable def conormalPullbackCompIso
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    modulePullback B S hS (subspaceInclusion B S hS X' Z') ⋙ modulePullback B S hS f ≅
      modulePullback B S hS g ⋙ modulePullback B S hS (subspaceInclusion B S hS X Z) :=
  modulePullbackCompIso B S hS f (subspaceInclusion B S hS X' Z') ≪≫
    eqToIso (congrArg
      (fun h : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X' =>
        modulePullback B S hS h) hsq.symm) ≪≫
    (modulePullbackCompIso B S hS (subspaceInclusion B S hS X Z) g).symm

/-- The identification of `AlgebraicGeometry.Space.conormalPullbackCompIso` evaluated at the
defining ideal sheaf of `Z'` and read as a morphism `f^*𝒞_{Z'/X'} ⟶ i^*g^*𝓘'` out of the conormal
module of `Z'` in `X'`.

Both spellings of the source are the same object — the conormal module is by definition the
inverse image of the defining ideal sheaf along the inclusion — and naming the comparison here
fixes that identification once, so that `AlgebraicGeometry.Space.conormalMap` is a composite of
two morphisms formed at the same objects. -/
noncomputable def conormalPullbackComparison
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    (modulePullback B S hS f).obj (conormalModule B S hS X' Z') ⟶
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        ((modulePullback B S hS g).obj (definingIdealSheaf B S hS X' Z').toSheafOfModules) :=
  (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
    (definingIdealSheaf B S hS X' Z').toSheafOfModules

/-- **Stacks 04CP for closed immersions.**  The canonical map of `𝒪_Z`-modules
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` attached to a commutative square of algebraic spaces in which `Z` is a
closed subspace of `X` and `Z'` a closed subspace of `X'`: the inverse image along the inclusion
of `Z` of `AlgebraicGeometry.Space.idealSheafMap`, read through the identification
`f^*(i')^* ≅ i^*g^*` of `AlgebraicGeometry.Space.conormalPullbackCompIso`.

The source states the lemma for immersions and reduces it to closed immersions at the start of
its proof; the lemma for arbitrary immersions is
`AlgebraicGeometry.Space.conormalMapOfImmersions`, and the implementation notes of this file say
why the closed case is the one carried here. -/
@[stacks 04CP "the canonical map, for closed immersions"]
noncomputable def conormalMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    (modulePullback B S hS f).obj (conormalModule B S hS X' Z') ⟶
      conormalModule B S hS X Z :=
  conormalPullbackComparison B S hS Z Z' g f hsq ≫
    (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
      (idealSheafMap B S hS Z Z' g f hsq)

/-! ### Invertibility of the conormal module map -/

/-- **The comparison factor of the conormal module map is an isomorphism.**  It is the component
at the defining ideal sheaf of `Z'` of the natural isomorphism
`AlgebraicGeometry.Space.conormalPullbackCompIso`. -/
theorem isIso_conormalPullbackComparison
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    IsIso (conormalPullbackComparison B S hS Z Z' g f hsq) :=
  inferInstanceAs (IsIso ((conormalPullbackCompIso B S hS Z Z' g f hsq).app
    (definingIdealSheaf B S hS X' Z').toSheafOfModules).hom)

/-- **A square whose map of defining ideal sheaves is invertible has an invertible map of
conormal modules.**  `AlgebraicGeometry.Space.conormalMap` is the comparison
`AlgebraicGeometry.Space.conormalPullbackComparison`, which is an isomorphism, followed by the
inverse image along `i` of `AlgebraicGeometry.Space.idealSheafMap`, and a functor carries an
isomorphism to an isomorphism.

This is how the conormal-module condition of [Stacks Project, Tag 06BH] is reached: for a
morphism of first-order thickenings whose square of ambient spaces is cartesian with flat lower
edge, the map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves is an isomorphism, and the condition on
conormal modules follows.  That hypothesis on `AlgebraicGeometry.Space.idealSheafMap` is the
content of [Stacks Project, Tag 04CQ], which this development does not carry. -/
theorem isIso_conormalMap_of_isIso_idealSheafMap
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (h : IsIso (idealSheafMap B S hS Z Z' g f hsq)) :
    IsIso (conormalMap B S hS Z Z' g f hsq) := by
  rw [conormalMap]
  refine IsIso.comp_isIso' (isIso_conormalPullbackComparison B S hS Z Z' g f hsq) ?_
  exact @Functor.map_isIso _ _ _ _ _ _ _ _ h

end AlgebraicGeometry.Space

end
