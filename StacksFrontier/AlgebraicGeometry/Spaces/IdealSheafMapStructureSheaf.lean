module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The map of defining ideal sheaves is the inverse image of an inclusion into the structure sheaf

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `Z` a closed subspace of `X` and `Z'` a closed subspace of `X'`.  The map
`g^*𝓘' ⟶ 𝓘` of defining ideal sheaves of [Stacks Project, Tag 04CP], followed by the inclusion
`𝓘 ⊆ 𝒪_X`, is the inverse image along `g` of the inclusion `𝓘' ⊆ 𝒪_{X'}`, read in `𝒪_X` through
the canonical comparison `g^*𝒪_{X'} ⟶ 𝒪_X`.

Both sides are morphisms out of `g^*𝓘'`, so each is determined by its transpose along the
adjunction of [Stacks Project, Tag 03D7], and each transpose is determined by its linear map of
sections along `g` of [Stacks Project, Tag 03LU].  The two linear maps of sections are both
pullback of regular functions along the vertical morphism of a diagram of étale scheme charts,
so the two morphisms agree.

The consequence is that *injectivity* of `g^*𝓘' ⟶ 𝓘` follows from injectivity of the inverse
image of a single inclusion of `𝒪_{X'}`-modules.  That is the shape in which flatness of `g` is
consumed by the proof of the conormal-module condition of [Stacks Project, Tag 06BH]: for a flat
morphism the inverse image of modules is exact, so it carries the inclusion `𝓘' ⊆ 𝒪_{X'}` to a
monomorphism.

## Main definitions

* `AlgebraicGeometry.Space.structureModuleFMap`: pullback of regular functions along the
  vertical morphism of a diagram of étale scheme charts, read as a linear map of sections along
  `g` from `𝒪_X` to `𝒪_{X'}`.
* `AlgebraicGeometry.Space.structureModulePullbackMap`: the canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` of
  `𝒪_X`-modules obtained from it by transposing twice.
* `AlgebraicGeometry.Space.structureUnitModule`: the structure sheaf of an algebraic space read
  as a module over itself, with its type written in the `AlgebraicGeometry.Space.Modules`
  spelling of that category of modules.
* `AlgebraicGeometry.Space.structureUnitPullbackMap`: the same canonical map `g^*𝒪_{X'} ⟶ 𝒪_X`,
  with both its source and its target written in that spelling.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardHomEquiv_app_comp_left` and
  `AlgebraicGeometry.Space.modulePushforwardHomEquiv_app_comp_right`: the chartwise universal
  property of the direct image is natural in both modules.
* `AlgebraicGeometry.Space.structureModulePullbackMap_transpose`: the characterising property of
  `AlgebraicGeometry.Space.structureModulePullbackMap`.
* `AlgebraicGeometry.Space.structureUnitPullbackMap_eq`: the two spellings of that map are the
  same morphism.
* `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`: **the map of defining ideal
  sheaves, followed by the inclusion of `𝓘` into `𝒪_X`, is the inverse image of the inclusion of
  `𝓘'` into `𝒪_{X'}`.**
* `AlgebraicGeometry.Space.mono_idealSheafMap_of_mono_comp`: consequently `g^*𝓘' ⟶ 𝓘` is
  injective as soon as that inverse image is.
* `AlgebraicGeometry.Space.isIso_idealSheafMap_of_epi_of_mono` and
  `AlgebraicGeometry.Space.isIso_conormalMap_of_epi_idealSheafMap_of_mono`: the invertibility of
  `g^*𝓘' ⟶ 𝓘`, and with it the conormal-module condition of [Stacks Project, Tag 06BH], from
  surjectivity of `g^*𝓘' ⟶ 𝓘` together with that injectivity.

## Implementation notes

**No tag is placed, and what the coverage limits are.**  The conclusion of
`AlgebraicGeometry.Space.isIso_conormalMap_of_epi_idealSheafMap_of_mono` is the
conormal-module condition of [Stacks Project, Tag 06BH], but its hypotheses are stronger than
that tag's: the tag assumes that the square of ambient spaces is cartesian and that `g` is flat,
and derives surjectivity of `g^*𝓘' ⟶ 𝓘` from the first — which is the content of
[Stacks Project, Tag 04CQ], assumed here as in
`AlgebraicGeometry.Space.epi_conormalMap_of_epi_idealSheafMap` — and the injectivity below from
the second.  So what is proved is a further reduction and not the tag, and no attribute claims
it.

**Why the comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is built here rather than taken from
`AlgebraicGeometry.Space.modulePullbackUnitIso`.**  That isomorphism is obtained by
corepresentability: morphisms out of `g^*𝒪_{X'}` are, by the adjunction of
[Stacks Project, Tag 03D7], morphisms out of `𝒪_{X'}` into the direct image, which are its
global sections, and global sections are preserved by a direct image.  Its linear map of sections
of [Stacks Project, Tag 03LU] is therefore pinned only through the terminal sheaf, and no
description of it on the charts of a diagram is available.  The map used below is instead
*defined* by its linear map of sections, which is what makes the comparison with
`AlgebraicGeometry.Space.idealSheafMap` — itself defined that way — a matter of comparing two
linear maps of sections.  The two maps `g^*𝒪_{X'} ⟶ 𝒪_X` agree, both being the map that carries
the unit section to the unit section; that identification is not made here but it **is** made, as
`AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackUnitIso_hom` of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSheafPullbackComparisonUnit.lean`, by
semilinearity of a linear map of sections out of the unit module together with the one available
value of the corepresentability comparison.  So the hypothesis of
`AlgebraicGeometry.Space.mono_idealSheafMap_of_mono` below is dischargeable — it is discharged
there, as `AlgebraicGeometry.Space.mono_structureModulePullbackMap` — and is kept as a
hypothesis here only because the discharge lives downstream of this file.

What *is* identified, for a **representable** `g`, is the other canonical comparison:
`AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackChartIso_comp` of
`StacksFrontier/AlgebraicGeometry/Spaces/StructureModulePullbackChart.lean` carries the map built
here onto `SheafOfModules.pullbackObjUnitToUnit` of
`AlgebraicGeometry.Space.smallBaseChangeSharp` across
`AlgebraicGeometry.Space.modulePullbackChartIso`.  That is a comparison with the pullback along
base change of étale scheme charts, not with
`AlgebraicGeometry.Space.modulePullbackUnitIso`, so it does not discharge the hypothesis above —
`SheafOfModules.pullbackObjUnitToUnit` is invertible when the index functor is final, which base
change of charts need not be.

**Why the map is given a second spelling.**  The category of `𝒪_X`-modules has two names here:
`AlgebraicGeometry.Space.Modules`, whose Grothendieck topology is the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite …).J` of a semireducible definition, and
`CategoryTheory.SheafOfModules` of `AlgebraicGeometry.Space.structureRingSheaf`, whose topology
is `AlgebraicGeometry.Space.SmallEtale.topology` because that is what the latter abbreviation
ascribes.  The two are the same category, but only after
`AlgebraicGeometry.Space.smallEtaleRingedSite` is unfolded, and the inverse image of
`AlgebraicGeometry.Space.modulePullback` is stated in the first spelling while
`CategoryTheory.SheafOfModules.unit` of the structure ring sheaf carries the second.  A morphism
written with one spelling on its source and the other on its target therefore hands that
unfolding to every consumer that composes it.
`AlgebraicGeometry.Space.structureUnitModule` names the unit module with its type written in the
first spelling, and `AlgebraicGeometry.Space.structureUnitPullbackMap` is the canonical map
written over it, so that a consumer meets one spelling throughout.  The two maps are the same
morphism, by `AlgebraicGeometry.Space.structureUnitPullbackMap_eq`.

**What that buys, and what it does not.**  The definition and the identification
are each free — the identification holds by `rfl`.  What is *not* free is bridging the two
spellings inside a composite that also mixes the two spellings
`(F ⋙ G).obj M` and `F.obj (G.obj M)` of one object — the composition law
`AlgebraicGeometry.Space.structureModulePullbackMap_comp`, restated over
`AlgebraicGeometry.Space.structureUnitPullbackMap` and proved by that law, exhausts the
elaborator's 200,000-heartbeat `whnf` budget.  So a consumer should pick one of the two spellings
and keep it for the whole statement rather than bridge between them in the middle; that is what
this map is for.

It is *not* what blocks the comparison of the two square comparisons of
[Stacks Project, Tag 04G2] part (2): the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonUnit.lean` record the bisection
that located that cost elsewhere, and the hypothesis that this spelling clash was responsible is
refuted there.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
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

/-! ### Naturality of the chartwise universal property of the direct image -/

variable {F F' : Modules.{u, u} B S hS X.1 X.2} {G G' : Modules.{u, u} B S hS X'.1 X'.2}

/-- The chartwise universal property of the direct image of [Stacks Project, Tag 03LU] is
natural in the module on the target: the linear map of sections of a composite `a ≫ b` is the
one of `b` precomposed with the sections of `a`. -/
theorem modulePushforwardHomEquiv_app_comp_left (a : G' ⟶ G)
    (b : G ⟶ (modulePushforward B S hS g).obj F)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (s : G'.val.obj (op d.V)) :
    (modulePushforwardHomEquiv B S hS g F G' (a ≫ b)).app d s =
      (modulePushforwardHomEquiv B S hS g F G b).app d (a.val.app (op d.V) s) :=
  rfl

/-- The chartwise universal property of the direct image of [Stacks Project, Tag 03LU] is
natural in the module on the source: the linear map of sections of `a` followed by the direct
image of `c` is the one of `a` postcomposed with the sections of `c`. -/
theorem modulePushforwardHomEquiv_app_comp_right (a : G ⟶ (modulePushforward B S hS g).obj F)
    (c : F ⟶ F') (d : ChartDiagram B S hS X.1 X'.1 g.hom) (s : G.val.obj (op d.V)) :
    (modulePushforwardHomEquiv B S hS g F' G
          (a ≫ (modulePushforward B S hS g).map c)).app d s =
      c.val.app (op d.U) ((modulePushforwardHomEquiv B S hS g F G a).app d s) :=
  modulePushforwardCounitApp_map B S hS g c d (a.val.app (op d.V) s)

/-! ### The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` -/

/-- **The structure map of a morphism of algebraic spaces as a linear map of sections.**  On a
commutative diagram of étale scheme charts over `g` it is pullback of regular functions along
the vertical morphism of the diagram.

This is `AlgebraicGeometry.Space.idealSheafFMap` with the two defining ideal sheaves replaced by
the two structure sheaves; additivity and semilinearity hold because the map is a homomorphism
of rings whose coefficient map is itself. -/
noncomputable def structureModuleFMap :
    ModuleFMap B S hS g (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS X')) where
  app d s := chartDiagramPullback B S hS g d s
  naturality d d' i j hij s := by
    have hcomm : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X'.1).map j)).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d'.g).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map i)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← Functor.map_comp,
        ← Functor.map_comp, hij]
    exact ConcreteCategory.congr_hom hcomm s
  map_add d s t := map_add (chartDiagramPullback B S hS g d).hom s t
  map_smul d r s := map_mul (chartDiagramPullback B S hS g d).hom r s

/-- **The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X`**: the transpose along the adjunction of
[Stacks Project, Tag 03D7] of the transpose along the chartwise universal property of the direct
image of `AlgebraicGeometry.Space.structureModuleFMap`.

It is the map that pullback of regular functions along `g` induces on the inverse image, built
in the same way as `AlgebraicGeometry.Space.idealSheafMap`. -/
noncomputable def structureModulePullbackMap :
    (modulePullback B S hS g).obj (SheafOfModules.unit (structureRingSheaf B S hS X')) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  ((modulePullbackAdjunction B S hS g).homEquiv _ _).symm
    ((modulePushforwardHomEquiv B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS X'))).symm
        (structureModuleFMap B S hS g))

/-- **The characterising property of `AlgebraicGeometry.Space.structureModulePullbackMap`.**
Transposing it back along the adjunction of [Stacks Project, Tag 03D7] gives the transpose of
`AlgebraicGeometry.Space.structureModuleFMap`, so the morphism is pinned down by pullback of
regular functions on sections. -/
theorem structureModulePullbackMap_transpose :
    (modulePullbackAdjunction B S hS g).homEquiv _ _ (structureModulePullbackMap B S hS g) =
      (modulePushforwardHomEquiv B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS X'))).symm
          (structureModuleFMap B S hS g) :=
  Equiv.apply_symm_apply _ _

/-! ### The same map, written in the `Modules` spelling -/

/-- **The structure sheaf of an algebraic space read as a module over itself**, as an object of
the category of `𝒪_X`-modules on its small étale site.

The two spellings `AlgebraicGeometry.Space.Modules` and `CategoryTheory.SheafOfModules` of that
category agree only after `AlgebraicGeometry.Space.smallEtaleRingedSite` — a semireducible
definition — has been unfolded, so a statement that hands
`CategoryTheory.SheafOfModules.unit` of the structure ring sheaf directly to an inverse-image
functor is not type-correct at `implicit` transparency and every step touching it pays that
unfolding.  Naming the object with its type written in the first spelling pays it once. -/
noncomputable abbrev structureUnitModule (T : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS T.1 T.2 :=
  SheafOfModules.unit (structureRingSheaf B S hS T)

/-- **The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X`, with source and target in the `Modules` spelling.**

This is `AlgebraicGeometry.Space.structureModulePullbackMap`, whose target is written as
`CategoryTheory.SheafOfModules.unit` of the structure ring sheaf while its source — being a
value of `AlgebraicGeometry.Space.modulePullback` — is written in the
`AlgebraicGeometry.Space.Modules` spelling.  The implementation notes of this file record what
mixing the two costs a consumer; here both ends are
`AlgebraicGeometry.Space.structureUnitModule`. -/
noncomputable def structureUnitPullbackMap :
    (modulePullback B S hS g).obj (structureUnitModule B S hS X') ⟶
      structureUnitModule B S hS X :=
  structureModulePullbackMap B S hS g

/-- **The two spellings of the canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` are the same morphism.**  This is
the one place where the reconciliation of the two spellings of the category of `𝒪_X`-modules is
paid for; see the implementation notes of this file. -/
theorem structureUnitPullbackMap_eq :
    structureUnitPullbackMap B S hS g = structureModulePullbackMap B S hS g :=
  rfl

/-! ### The map of defining ideal sheaves inside the structure sheaf -/

/-- **The map of defining ideal sheaves, read inside the structure sheaf.**  The map
`g^*𝓘' ⟶ 𝓘` of [Stacks Project, Tag 04CP], followed by the inclusion `𝓘 ⊆ 𝒪_X`, is the inverse
image along `g` of the inclusion `𝓘' ⊆ 𝒪_{X'}`, read in `𝒪_X` through
`AlgebraicGeometry.Space.structureModulePullbackMap`.

Both sides are morphisms out of `g^*𝓘'`, hence determined by their transposes along the
adjunction of [Stacks Project, Tag 03D7], and those by their linear maps of sections along `g`.
Both linear maps of sections are pullback of regular functions along the vertical morphism of a
chart diagram: on the left by `AlgebraicGeometry.Space.idealSheafMap_transpose` and
`AlgebraicGeometry.Space.idealSheafFMap_app_coe`, on the right by
`AlgebraicGeometry.Space.structureModulePullbackMap_transpose`. -/
theorem idealSheafMap_comp_definingIdealSheaf_ι
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    idealSheafMap B S hS Z Z' g f hsq ≫ (definingIdealSheaf B S hS X Z).ι =
      (modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
        structureModulePullbackMap B S hS g := by
  refine ((modulePullbackAdjunction B S hS g).homEquiv _ _).injective ?_
  refine Eq.trans ((modulePullbackAdjunction B S hS g).homEquiv_naturality_right
      (idealSheafMap B S hS Z Z' g f hsq) (definingIdealSheaf B S hS X Z).ι)
    (Eq.trans ?_ ((modulePullbackAdjunction B S hS g).homEquiv_naturality_left
      (definingIdealSheaf B S hS X' Z').ι (structureModulePullbackMap B S hS g)).symm)
  refine Eq.trans ?_ (congrArg (fun t ↦ (definingIdealSheaf B S hS X' Z').ι ≫ t)
    (structureModulePullbackMap_transpose B S hS g).symm)
  refine (modulePushforwardHomEquiv B S hS g _ _).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  refine Eq.trans (modulePushforwardHomEquiv_app_comp_right B S hS g
    ((modulePullbackAdjunction B S hS g).homEquiv _ _ (idealSheafMap B S hS Z Z' g f hsq))
    (definingIdealSheaf B S hS X Z).ι d s) ?_
  refine Eq.trans (congrArg ((definingIdealSheaf B S hS X Z).ι.val.app (op d.U))
    (congrFun (congrFun (congrArg ModuleFMap.app
      (idealSheafMap_transpose B S hS Z Z' g f hsq)) d) s)) ?_
  refine Eq.trans ?_ (modulePushforwardHomEquiv_app_comp_left B S hS g
    (definingIdealSheaf B S hS X' Z').ι
    ((modulePushforwardHomEquiv B S hS g _ _).symm (structureModuleFMap B S hS g)) d s).symm
  refine Eq.trans ?_ (congrFun (congrFun (congrArg ModuleFMap.app
      (Equiv.apply_symm_apply (modulePushforwardHomEquiv B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS X')))
        (structureModuleFMap B S hS g)).symm) d)
      ((definingIdealSheaf B S hS X' Z').ι.val.app (op d.V) s))
  rfl

/-! ### Injectivity and invertibility of the map of defining ideal sheaves -/

/-- **Injectivity of the inverse image of the inclusion `𝓘' ⊆ 𝒪_{X'}` gives injectivity of the
map of defining ideal sheaves.**  By
`AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι` the hypothesis says that
`g^*𝓘' ⟶ 𝓘` followed by the inclusion `𝓘 ⊆ 𝒪_X` is a monomorphism, and a morphism whose
composite with another is a monomorphism is one. -/
theorem mono_idealSheafMap_of_mono_comp
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (h : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
      structureModulePullbackMap B S hS g)) :
    Mono (idealSheafMap B S hS Z Z' g f hsq) := by
  have : Mono (idealSheafMap B S hS Z Z' g f hsq ≫
      (definingIdealSheaf B S hS X Z).ι) := by
    rw [idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Z' g f hsq]
    exact h
  exact mono_of_mono _ (definingIdealSheaf B S hS X Z).ι

/-- **The map of defining ideal sheaves is injective once the inverse image of the inclusion
`𝓘' ⊆ 𝒪_{X'}` is, and the comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is.**

For a flat `g` the inverse image of modules is exact and so carries the inclusion
`𝓘' ⊆ 𝒪_{X'}` to a monomorphism; that is the shape in which the proof of
[Stacks Project, Tag 06BH] uses flatness.  The second hypothesis holds because
`AlgebraicGeometry.Space.structureModulePullbackMap` is the canonical comparison
`g^*𝒪_{X'} ⟶ 𝒪_X`, which is invertible; it is proved as
`AlgebraicGeometry.Space.mono_structureModulePullbackMap` in
`StacksFrontier/AlgebraicGeometry/Spaces/StructureSheafPullbackComparisonUnit.lean`, downstream of
this file, so the hypothesis is kept here. -/
theorem mono_idealSheafMap_of_mono
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hι : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι))
    (hθ : Mono (structureModulePullbackMap B S hS g)) :
    Mono (idealSheafMap B S hS Z Z' g f hsq) := by
  have := hι
  have := hθ
  exact mono_idealSheafMap_of_mono_comp B S hS Z Z' g f hsq (mono_comp _ _)

/-- **The map of defining ideal sheaves is invertible once it is surjective and the inverse image
of the inclusion `𝓘' ⊆ 𝒪_{X'}` is injective.**  Modules on the small étale site of an algebraic
space form a balanced category, so an epimorphism that is a monomorphism is invertible. -/
theorem isIso_idealSheafMap_of_epi_of_mono
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (h : Epi (idealSheafMap B S hS Z Z' g f hsq))
    (hm : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
      structureModulePullbackMap B S hS g)) :
    IsIso (idealSheafMap B S hS Z Z' g f hsq) :=
  have := mono_idealSheafMap_of_mono_comp B S hS Z Z' g f hsq hm
  isIso_of_mono_of_epi _

/-- **The conormal-module condition of [Stacks Project, Tag 06BH], from surjectivity of the map
of defining ideal sheaves and injectivity of the inverse image of the inclusion
`𝓘' ⊆ 𝒪_{X'}`.**  The canonical map `f^*𝒞_{Z'/X'} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 04CP] is
an isomorphism.

The two hypotheses are the two halves that [Stacks Project, Tag 06BH] obtains from its own: the
first from cartesianness of the square of ambient spaces, by [Stacks Project, Tag 04CQ], and the
second from flatness of `g`, for which the inverse image of modules is exact.  Neither
derivation is carried in this development, and the implementation notes of this file record why
no attribute claims the tag.

Given the two, the map of defining ideal sheaves is invertible by
`AlgebraicGeometry.Space.isIso_idealSheafMap_of_epi_of_mono`, and the conormal-module condition
follows by `AlgebraicGeometry.Space.isIso_conormalMap_of_isIso_idealSheafMap`. -/
theorem isIso_conormalMap_of_epi_idealSheafMap_of_mono
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (h : Epi (idealSheafMap B S hS Z Z' g f hsq))
    (hm : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
      structureModulePullbackMap B S hS g)) :
    IsIso (conormalMap B S hS Z Z' g f hsq) :=
  isIso_conormalMap_of_isIso_idealSheafMap B S hS Z Z' g f hsq
    (isIso_idealSheafMap_of_epi_of_mono B S hS Z Z' g f hsq h hm)

end AlgebraicGeometry.Space

end
