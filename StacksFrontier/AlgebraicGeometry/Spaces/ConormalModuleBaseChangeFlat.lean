module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapChartHom
import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapSections
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSingleRelation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact

/-!
# The flat clause of Stacks 04CQ

Let `Z' ⊆ X'` be a closed subspace of an algebraic space over a scheme `S` contained in a big
fppf site `B`, let `g : X ⟶ X'` be a morphism of algebraic spaces, and form the fibre product
square whose upper closed subspace is the inverse image `g⁻¹(Z') ⊆ X` of Stacks 083Q and whose
vertical morphism is the projection.  Stacks 04CQ asserts that the canonical map
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}` of conormal modules of Stacks 04CP is surjective, and that it is
an **isomorphism when `g` is flat**.  The surjectivity clause is
`AlgebraicGeometry.Space.epi_conormalMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`.  This file proves the
flat clause.

The argument is the one of the source.  The map of conormal modules is the inverse image along
the inclusion of `g⁻¹(Z')` of the map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves, precomposed with an
isomorphism (`AlgebraicGeometry.Space.conormalMap_eq`), so it suffices that the map of ideal
sheaves is an isomorphism.  It is an epimorphism unconditionally
(`AlgebraicGeometry.Space.epi_idealSheafMap`), and the flatness of `g` is what makes it a
monomorphism: composed with the inclusion `𝓘 ⟶ 𝒪_X` it is the inverse image of the inclusion
`𝓘' ⟶ 𝒪_{X'}` followed by the map `g^*𝒪_{X'} ⟶ 𝒪_X` of structure sheaves
(`AlgebraicGeometry.Space.idealSheafMap_comp_ι`); the first factor is a monomorphism because the
inverse image of modules along a flat morphism is exact, and the second is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.structureUnitFMap`: the chartwise map of structure sheaves along `g`,
  namely pullback of regular functions along the vertical morphism of a chart diagram.
* `AlgebraicGeometry.Space.structureSheafMap`: the map `g^*𝒪_{X'} ⟶ 𝒪_X` of `𝒪_X`-modules it
  transposes to, built exactly as `AlgebraicGeometry.Space.idealSheafMap` is but with the full
  structure sheaves in place of the defining ideals.

## Main results

* `AlgebraicGeometry.Space.exactFunctor_modulePullback_of_isFlat`: the inverse image of
  modules along a morphism of algebraic spaces whose morphism of small étale ringed topoi is flat
  is exact, hence preserves monomorphisms.  This is Stacks 04JC
  (`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`) read at the morphism
  of small étale ringed topoi of Stacks 03G8; no tag is claimed, the tag being registered there.
* `AlgebraicGeometry.Space.epi_structureSheafMap`: the map of structure sheaves is an
  epimorphism, with no hypothesis on `g`.
* `AlgebraicGeometry.Space.isIso_structureSheafMap`: it is an isomorphism, again with no
  hypothesis on `g`.
* `AlgebraicGeometry.Space.idealSheafMap_comp_ι`: the map of defining ideal sheaves, followed by
  the inclusion of the ideal sheaf, is the inverse image of the inclusion downstairs followed by
  the map of structure sheaves.
* `AlgebraicGeometry.Space.mono_idealSheafMap_of_isFlat` and
  `AlgebraicGeometry.Space.isIso_idealSheafMap_of_isFlat`.
* `AlgebraicGeometry.Space.isIso_conormalMap_of_isFlat`: **the flat clause of
  [Stacks Project, Tag 04CQ]**.
* `AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom_of_eq`: for an
  étale `g`, the canonical map of [Stacks Project, Tag 04CP] at the étale restriction square is
  the forward map of the comparison isomorphism of [Stacks Project, Tag 04CO], **granted one
  equation of maps of defining ideal sheaves on `X`**.
* `AlgebraicGeometry.Space.idealSheafMap_eq_modulePullbackIsoEtaleModulePullback_hom_comp`: **that
  equation**, proved.  The map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves at an étale restriction
  square is the identification of [Stacks Project, Tag 03LW] followed by the comparison of
  [Stacks Project, Tag 04CO].
* `AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom`: **the
  identification of the canonical map of [Stacks Project, Tag 04CP] with the comparison
  isomorphism of [Stacks Project, Tag 04CO], with no hypothesis.**  The two preceding results
  composed.

## Implementation notes

**What "flat" means here.**  The hypothesis is that the morphism of small étale ringed topoi
induced by `g` is flat in the sense of [Stacks Project, Tag 04JB],
`AlgebraicGeometry.RingedToposHom.IsFlat` — that is, that `𝒪_X` is flat over `g⁻¹𝒪_{X'}`.  That
is the condition the source's proof uses, and it is the condition under which the development has
exactness of the inverse image of modules (Stacks 04JC).  It is *not* literally
`AlgebraicGeometry.Space.IsFlat`, the chartwise flatness of Stacks 03ML part (1): the two agree,
but no statement in this development relates them, so the clause string on the tag below names
the hypothesis actually carried.

**Why `structureSheafMap` is built by hand rather than taken from the unit comparison.**
`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso` already gives an isomorphism
`𝒪_X ≅ g^*𝒪_{X'}`, but it is constructed by corepresentability and no description of it on
sections is available; identifying it with the chartwise pullback of regular functions would
mean computing its transpose through `unitTerminalHomEquiv`, the terminal-sections comparison of
a direct image, and the comparison of the two direct images of modules.  So the map used here is
the one with the chartwise description, defined by the same double transpose as
`AlgebraicGeometry.Space.idealSheafMap` — which is what makes
`AlgebraicGeometry.Space.idealSheafMap_comp_ι` a chartwise computation — and the unit comparison
is used only for its *existence*: composing it with `structureSheafMap` gives an epimorphism of
`𝒪_X` onto itself, and such a map is right multiplication by a global regular function which
local surjectivity makes locally invertible, so it is a monomorphism and hence, the modules on
the small étale site being a balanced category, an isomorphism.

**The abelian structure of the modules is written out once, and must stay an explicit term.**
`AlgebraicGeometry.Space.isIso_structureSheafMap` and
`AlgebraicGeometry.Space.isIso_idealSheafMap_of_isFlat` both need
`Balanced (Modules.{u, u} B S hS X.1 X.2)`, and both obtain it from the private lemma
`balanced_modules`, which uses `Stacks.SheafOfModules.ImageSubsheaf.balanced_of_abelian`.  The
abelian structure is supplied as
an explicit term — `SheafOfModules.instAbelian` fed the two sheafification instances of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian` — and **not** by `inferInstance`.  The
reason is the one recorded at
`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityFlatInjection.lean`: those two sheafification
instances have a universe parameter occurring only inside a `max`, so with a wide enough instance
set in scope the search for `Abelian (Modules.{u, u} …)` meets a candidate at module universe
`max (u + 1) u ?u`, reports

`stuck at solving universe constraint u + 1 =?= max (u + 1) ?u`

and *aborts* instead of backtracking.  That abort is what the three imports
`EtaleSourceModuleFMapChartHom`, `IdealSheafMapSections` and `ModulePullbackChartGeneration` —
needed for the identification of Stacks 04CP with Stacks 04CO below — would otherwise cause.  For
the same reason `AlgebraicGeometry.Space.isIso_structureSheafMap` also names the balancedness a
second time at the ringed-topos spelling of the category: the composite it feeds to
`CategoryTheory.isIso_of_mono_of_epi` is elaborated at
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos …).O)`,
which is the same category but not the same term as `Modules …`, so the hypothesis stated at the
site spelling does not stop that search on its own.

**The three imports for the identification of Stacks 04CP with Stacks 04CO are private, and must
stay private.**  `EtaleSourceModuleFMapChartHom`, `IdealSheafMapSections` and
`ModulePullbackChartGeneration` are imported without `public`, so they do not enter the closure of
this file's consumers.  Making any of them public re-exports the aborting candidate and breaks
three files that import this one — `ConormalAlgebraSquareMapFlatClause`,
`ConormalModuleFirstOrderThickening` and `Groupoids/More/SectionsConormalAction` — each at its own
`inferInstance` for `Abelian (Modules.{u, u} …)`, exactly as above.  Taking the imports one at a
time, the offending candidate is reachable from `EtaleSourceModulePullbackComparison` (hence from
`EtaleSourceModuleFMapChartHom`) *and* from `ModulePullbackChartGeneration`, while
`IdealSheafMapSections` alone does not expose it.  A private import still exposes it to *this*
file, which is why the two proofs above pin the instance as well; neither precaution substitutes for
the other.  The helper lemmas whose statements mention the privately imported names are therefore
`private`, and the two public results state nothing that was not already in this file's public
closure.

**The chartwise identity is crossed once.**  Both sides of
`AlgebraicGeometry.Space.idealSheafMap_comp_ι` are morphisms out of `g^*𝓘'`; the proof transposes
along the Stacks 03D7 adjunction and then along the chartwise universal property of the direct
image of Stacks 03LU, and compares the two resulting linear maps of sections on a chart diagram,
where both are pullback of regular functions.  The two transposes are moved past the two
compositions by the naturality of the adjunction bijection and by the naturality of the counit of
the chartwise universal property, exactly as in
`AlgebraicGeometry.Space.mem_range_idealSheafMap`.

## What is not proved

* **The clause is stated for flatness of the induced morphism of small étale ringed topoi**, not
  for `AlgebraicGeometry.Space.IsFlat`, the chartwise flatness of Stacks 03ML part (1).  The
  passage between the two,
  `AlgebraicGeometry.Space.IsFlat g → (smallEtaleRingedToposHom B S hS g).IsFlat`, is a
  consequence of Stacks 073C,
  `AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleFlatTopos.lean`, an equivalence, so the clause
  below is available for chartwise flatness by rewriting its hypothesis with it.  Its use for an
  étale morphism is `AlgebraicGeometry.Space.isFlat_smallEtaleRingedToposHom_of_isEtale` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestrictionCanonical.lean`.
* **The exactness in the middle of Stacks 06BD is not proved**, and nothing here bears on it; see
  the "What is not proved" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`.
* **The immersion case is not covered.**  As everywhere in this part of the development the
  clause is proved for closed subspaces; the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` record why.
* **No tag is claimed for the identification of Stacks 04CP with Stacks 04CO.**  The
  identification is proved here with no hypothesis
  (`AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom`), but this
  development records it as the content of Stacks 04G2 and 04CQ rather than of 04CO — see the
  "What is not proved" section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` — and no clause of
  either tag is stated by it on its own, so the bare tags stay where they are.

## References

* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS}

/-! ### The inverse image of modules along a flat morphism -/

/-- The inverse image of modules along a flat morphism of algebraic spaces is exact. -/
theorem exactFunctor_modulePullback_of_isFlat (g : X ⟶ X')
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    exactFunctor (Modules.{u, u} B S hS X'.1 X'.2) (Modules.{u, u} B S hS X.1 X.2)
      (modulePullback B S hS g) :=
  Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
    (smallEtaleRingedToposHom B S hS g) hg

/-- The inverse image of modules along a flat morphism preserves monomorphisms. -/
private theorem preservesMonomorphisms_modulePullback_of_isFlat (g : X ⟶ X')
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    (modulePullback B S hS g).PreservesMonomorphisms :=
  have := ((exactFunctor_iff (modulePullback B S hS g)).mp
    (exactFunctor_modulePullback_of_isFlat B S hS g hg)).1
  inferInstance

/-! ### The map of structure sheaves -/

/-- The chartwise map of structure sheaves along `g`. -/
noncomputable def structureUnitFMap (g : X ⟶ X') :
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

/-- The map `g^*𝒪_{X'} ⟶ 𝒪_X` of structure sheaves. -/
noncomputable def structureSheafMap (g : X ⟶ X') :
    (modulePullback B S hS g).obj (SheafOfModules.unit (structureRingSheaf B S hS X')) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
  ((modulePullbackAdjunction B S hS g).homEquiv _ _).symm
    ((modulePushforwardHomEquiv B S hS g (SheafOfModules.unit (structureRingSheaf B S hS X))
      (SheafOfModules.unit (structureRingSheaf B S hS X'))).symm (structureUnitFMap B S hS g))

/-- The characterising property of `structureSheafMap`. -/
theorem structureSheafMap_transpose (g : X ⟶ X') :
    modulePushforwardHomEquiv B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS X'))
        ((modulePullbackAdjunction B S hS g).homEquiv _ _ (structureSheafMap B S hS g)) =
      structureUnitFMap B S hS g := by
  rw [structureSheafMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The chartwise formula for the transpose of a morphism into the direct image. -/
private theorem homEquiv_app (g : X ⟶ X') (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS X'.1 X'.2) (a : G ⟶ (modulePushforward B S hS g).obj F)
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (s : G.val.obj (op d.V)) :
    (modulePushforwardHomEquiv B S hS g F G a).app d s =
      ((modulePushforwardPresentation B S hS g).counit F).app d (a.val.app (op d.V) s) :=
  (modulePushforwardPresentation B S hS g).homEquiv_apply F G a d s

/-! ### The map of structure sheaves is an epimorphism -/

/-- A linear map onto a ring, as a module over itself, whose image contains `1` is surjective:
its image is a submodule, so it contains `y • 1 = y` for every `y`. -/
private theorem mem_range_of_one_mem_range {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)
    (h : (1 : R) ∈ LinearMap.range φ) (y : R) : y ∈ LinearMap.range φ := by
  have hy := (LinearMap.range φ).smul_mem y h
  rwa [smul_eq_mul, mul_one] at hy

/-- The map of structure sheaves hits the pullbacks of regular functions. -/
theorem mem_range_structureSheafMap (g : X ⟶ X')
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (SheafOfModules.unit (structureRingSheaf B S hS X')).val.obj (op d.V)) :
    (structureUnitFMap B S hS g).app d s ∈
      LinearMap.range ((structureSheafMap B S hS g).val.app (op d.U)).hom := by
  refine LinearMap.mem_range.mpr ⟨((modulePushforwardPresentation B S hS g).counit
    ((modulePullback B S hS g).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X')))).app d
      (((modulePullbackAdjunction B S hS g).unit.app
        (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.app (op d.V) s), ?_⟩
  have hnat := (modulePushforwardPresentation B S hS g).naturality
    (structureSheafMap B S hS g) d
    (((modulePullbackAdjunction B S hS g).unit.app
      (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.app (op d.V) s)
  have h2 := (modulePushforwardPresentation B S hS g).homEquiv_apply
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (SheafOfModules.unit (structureRingSheaf B S hS X'))
    ((modulePullbackAdjunction B S hS g).homEquiv _ _ (structureSheafMap B S hS g)) d s
  have h1 : ((modulePullbackAdjunction B S hS g).homEquiv _ _
        (structureSheafMap B S hS g)).val.app (op d.V) s =
      ((modulePushforward B S hS g).map
        (structureSheafMap B S hS g)).val.app (op d.V)
        (((modulePullbackAdjunction B S hS g).unit.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'))).val.app (op d.V) s) :=
    congrArg
      (fun m : SheafOfModules.unit (structureRingSheaf B S hS X') ⟶
          (modulePushforward B S hS g).obj
            (SheafOfModules.unit (structureRingSheaf B S hS X)) ↦ m.val.app (op d.V) s)
      ((modulePullbackAdjunction B S hS g).homEquiv_unit _ _ (structureSheafMap B S hS g))
  refine Eq.symm (Eq.trans ?_ hnat)
  refine Eq.trans ?_ (congrArg (fun t ↦ ((modulePushforwardPresentation B S hS g).counit
    (SheafOfModules.unit (structureRingSheaf B S hS X))).app d t) h1)
  refine Eq.trans ?_ h2
  exact congrArg (fun ξ ↦ ξ.app d s) (structureSheafMap_transpose B S hS g).symm

/-- The map of structure sheaves is surjective on the sections over a chart diagram: the image
is a submodule of the regular functions containing `1`. -/
theorem surjective_structureSheafMap_val_app (g : X ⟶ X')
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) :
    Function.Surjective ((structureSheafMap B S hS g).val.app (op d.U)).hom := by
  obtain ⟨x, hx⟩ := mem_range_structureSheafMap B S hS g d
    (1 : ToType ((structureRingSheaf B S hS X').obj.obj (op d.V)))
  have hx1 : ((structureSheafMap B S hS g).val.app (op d.U)).hom x =
      (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op d.U))) :=
    hx.trans (map_one (chartDiagramPullback B S hS g d).hom)
  intro y
  have h1 : (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op d.U))) ∈
      LinearMap.range ((structureSheafMap B S hS g).val.app (op d.U)).hom := ⟨x, hx1⟩
  exact LinearMap.mem_range.mp (mem_range_of_one_mem_range
    ((structureSheafMap B S hS g).val.app (op d.U)).hom h1 y)

/-- The map of structure sheaves is locally surjective on the small étale site of `X`. -/
theorem isLocallySurjective_structureSheafMap (g : X ⟶ X') :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).map
        (structureSheafMap B S hS g).val) := by
  constructor
  intro U s
  refine mem_topology_of_hasAffineChartDiagram B S hS g U _ ?_
  intro W a hW
  obtain ⟨-, V, q, hcomm, -⟩ := hW
  have hd : Function.Surjective ((structureSheafMap B S hS g).val.app (op W)).hom :=
    surjective_structureSheafMap_val_app B S hS g
      { U := W, V := V, g := q, comm := hcomm.symm }
  exact hd (((PresheafOfModules.toPresheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)).val).map a.op s)

/-- The map of structure sheaves is an epimorphism of `𝒪_X`-modules. -/
theorem epi_structureSheafMap (g : X ⟶ X') : Epi (structureSheafMap B S hS g) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_structureSheafMap B S hS g)

/-! ### An epimorphism of the structure sheaf onto itself is an isomorphism -/

/-- A linear endomorphism of a ring, as a module over itself, is right multiplication by the
image of `1`. -/
private theorem apply_eq_mul_apply_one {R : Type*} [Ring R] (φ : R →ₗ[R] R) (z : R) :
    φ z = z * φ 1 := by
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- Right multiplication by an element with a left inverse is injective in a commutative ring. -/
private theorem eq_of_mul_right_eq {R : Type*} [Ring R] (c t x y : R)
    (hcomm : ∀ a b : R, a * b = b * a) (htc : t * c = 1) (h : x * c = y * c) : x = y := by
  have hct : c * t = 1 := (hcomm c t).trans htc
  simpa [mul_assoc, hct] using congrArg (· * t) h

/-- The regular functions over an étale chart commute: the structure sheaf of rings in which the
modules are indexed is the sheaf of commutative rings with commutativity forgotten. -/
private theorem mul_comm_structureRingSheaf (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (a b : ToType ((structureRingSheaf B S hS X).obj.obj W)) : a * b = b * a :=
  mul_comm (G := ToType ((structureSheaf B S hS X.1 X.2).obj.obj W)) a b

/-- **An epimorphism of the structure sheaf onto itself is a monomorphism.**  Such a morphism is
right multiplication by the global regular function `c` it sends `1` to; it is locally surjective
because it is an epimorphism, so `c` is locally invertible, and right multiplication by a unit is
injective. -/
private theorem mono_of_epi_unitEndo
    (v : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      SheafOfModules.unit (structureRingSheaf B S hS X)) (hv : Epi v) : Mono v := by
  have hinst := hv
  have hloc := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi v
  refine Stacks.SheafOfModules.mono_of_isLocallyInjective_val v ⟨fun {U} x y hxy ↦ ?_⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (hloc.imageSieve_mem (1 : ToType ((structureRingSheaf B S hS X).obj.obj U)))
  intro W a ha
  obtain ⟨t, ht⟩ := ha
  refine eq_of_mul_right_eq (R := ToType ((structureRingSheaf B S hS X).obj.obj (op W)))
    ((v.val.app (op W)).hom
      (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op W)))) t _ _
    (mul_comm_structureRingSheaf B S hS (op W)) ?_ ?_
  · exact (apply_eq_mul_apply_one (v.val.app (op W)).hom t).symm.trans
      (ht.trans (PresheafOfModules.unit_map_one _ a.op))
  · have h1 := ConcreteCategory.congr_hom
      (((PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).map v.val).naturality
          a.op)
    have key : ∀ z, (v.val.app (op W)).hom (((PresheafOfModules.toPresheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X)).val).map a.op z) =
        ((PresheafOfModules.toPresheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X)).val).map a.op
          ((v.val.app U).hom z) := fun z ↦ h1 z
    refine Eq.trans (apply_eq_mul_apply_one
        (R := ToType ((structureRingSheaf B S hS X).obj.obj (op W)))
        (v.val.app (op W)).hom _).symm ?_
    refine Eq.trans (key x) (Eq.trans (congrArg _ hxy) (Eq.trans (key y).symm ?_))
    exact apply_eq_mul_apply_one
      (R := ToType ((structureRingSheaf B S hS X).obj.obj (op W)))
      (v.val.app (op W)).hom _

/-- The modules on the small étale site of `X` form a balanced category.  The abelian structure is
supplied as an explicit term, not by `inferInstance`. -/
private theorem balanced_modules (X : AlgebraicSpaces B S hS) :
    Balanced (Modules.{u, u} B S hS X.1 X.2) := by
  let habelian : Abelian (Modules.{u, u} B S hS X.1 X.2) :=
    @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS X.1 X.2)
      (smallEtaleRingedSite_wEqualsLocallyBijective B S hS X.1 X.2)
  exact Stacks.SheafOfModules.ImageSubsheaf.balanced_of_abelian

/-- **The map of structure sheaves is an isomorphism.**  It is an epimorphism, and the inverse
image of the structure sheaf is the structure sheaf, so it becomes an epimorphism of the
structure sheaf onto itself; such a map is a monomorphism, and the modules on the small étale
site are a balanced category. -/
theorem isIso_structureSheafMap (g : X ⟶ X') : IsIso (structureSheafMap B S hS g) := by
  have hbal := balanced_modules B S hS X
  let hbalTopos : Balanced (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS X).O)) := hbal
  set e := Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
    (smallEtaleRingedToposModulesHom B S hS g) with he
  have hepiHom : Epi e.hom := ⟨fun g₁ g₂ h => by
    rw [← Iso.inv_hom_id_assoc e g₁, h, Iso.inv_hom_id_assoc]⟩
  have hepiSsm : Epi (structureSheafMap B S hS g) := epi_structureSheafMap B S hS g
  have hepi : Epi (e.hom ≫ structureSheafMap B S hS g) :=
    @epi_comp _ _ _ _ _ e.hom hepiHom (structureSheafMap B S hS g) hepiSsm
  have hmono : Mono (e.hom ≫ structureSheafMap B S hS g) :=
    mono_of_epi_unitEndo B S hS _ hepi
  have hiso : IsIso (e.hom ≫ structureSheafMap B S hS g) := isIso_of_mono_of_epi _
  have hisoHom : IsIso e.hom := Iso.isIso_hom e
  exact IsIso.of_isIso_comp_left e.hom (structureSheafMap B S hS g)

/-! ### The square -/

section Square

variable (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))

private theorem transpose_left
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (definingIdealSheaf B S hS X' Z').toSheafOfModules.val.obj (op d.V)) :
    (modulePushforwardHomEquiv B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (definingIdealSheaf B S hS X' Z').toSheafOfModules
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (idealSheafMap B S hS Z Z' g f hsq ≫
            (definingIdealSheaf B S hS X Z).ι))).app d s =
      chartDiagramPullback B S hS g d s.1 := by
  have hnat := (modulePullbackAdjunction B S hS g).homEquiv_naturality_right
    (idealSheafMap B S hS Z Z' g f hsq) (definingIdealSheaf B S hS X Z).ι
  rw [hnat]
  refine Eq.trans (homEquiv_app B S hS g _ _ _ d s) ?_
  refine Eq.trans ((modulePushforwardPresentation B S hS g).naturality
    (definingIdealSheaf B S hS X Z).ι d _) ?_
  refine Eq.trans (congrArg (fun t ↦ (definingIdealSheaf B S hS X Z).ι.val.app (op d.U) t)
    (Eq.trans (homEquiv_app B S hS g (definingIdealSheaf B S hS X Z).toSheafOfModules
        (definingIdealSheaf B S hS X' Z').toSheafOfModules
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (idealSheafMap B S hS Z Z' g f hsq)) d s).symm
      (congrArg (fun ξ : ModuleFMap B S hS g
            (definingIdealSheaf B S hS X Z).toSheafOfModules
            (definingIdealSheaf B S hS X' Z').toSheafOfModules ↦ ξ.app d s)
        (idealSheafMap_transpose B S hS Z Z' g f hsq)))) ?_
  exact idealSheafFMap_app_coe B S hS Z Z' g f hsq d s

private theorem transpose_right
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (definingIdealSheaf B S hS X' Z').toSheafOfModules.val.obj (op d.V)) :
    (modulePushforwardHomEquiv B S hS g
      (SheafOfModules.unit (structureRingSheaf B S hS X))
      (definingIdealSheaf B S hS X' Z').toSheafOfModules
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
            structureSheafMap B S hS g))).app d s =
      chartDiagramPullback B S hS g d s.1 := by
  have hnat := (modulePullbackAdjunction B S hS g).homEquiv_naturality_left
    (definingIdealSheaf B S hS X' Z').ι (structureSheafMap B S hS g)
  rw [hnat]
  refine Eq.trans (homEquiv_app B S hS g _ _ _ d s) ?_
  refine Eq.trans (homEquiv_app B S hS g
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (SheafOfModules.unit (structureRingSheaf B S hS X'))
    ((modulePullbackAdjunction B S hS g).homEquiv _ _ (structureSheafMap B S hS g)) d
    ((definingIdealSheaf B S hS X' Z').ι.val.app (op d.V) s)).symm ?_
  refine Eq.trans (congrArg (fun ξ : ModuleFMap B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS X')) ↦
      ξ.app d ((definingIdealSheaf B S hS X' Z').ι.val.app (op d.V) s))
    (structureSheafMap_transpose B S hS g)) ?_
  rfl

/-- **The map of defining ideal sheaves is the restriction of the map of structure sheaves.** -/
theorem idealSheafMap_comp_ι
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    idealSheafMap B S hS Z Z' g f hsq ≫ (definingIdealSheaf B S hS X Z).ι =
      (modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
        structureSheafMap B S hS g := by
  refine ((modulePullbackAdjunction B S hS g).homEquiv _ _).injective ?_
  refine (modulePushforwardHomEquiv B S hS g
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (definingIdealSheaf B S hS X' Z').toSheafOfModules).injective ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  rw [transpose_left B S hS Z Z' g f hsq d s, transpose_right B S hS Z' g d s]

/-- **The map of defining ideal sheaves along a flat morphism is a monomorphism.** -/
theorem mono_idealSheafMap_of_isFlat
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat)
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z') :
    Mono (idealSheafMap B S hS Z Z' g f hsq) := by
  have hpm := preservesMonomorphisms_modulePullback_of_isFlat B S hS g hg
  have hmi : Mono (definingIdealSheaf B S hS X' Z').ι :=
    (definingIdealShortComplex_shortExact B S hS X' Z').mono_f
  have h1 : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι) :=
    @Functor.map_mono _ _ _ _ (modulePullback B S hS g) hpm _ _
      (definingIdealSheaf B S hS X' Z').ι hmi
  have h2m : Mono (structureSheafMap B S hS g) :=
    @IsIso.mono_of_iso _ _ _ _ (structureSheafMap B S hS g) (isIso_structureSheafMap B S hS g)
  have h3 : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι ≫
      structureSheafMap B S hS g) :=
    @mono_comp _ _ _ _ _ _ h1 _ h2m
  have h4 : Mono (idealSheafMap B S hS Z Z' g f hsq ≫ (definingIdealSheaf B S hS X Z).ι) := by
    rw [idealSheafMap_comp_ι]
    exact h3
  exact mono_of_mono _ (definingIdealSheaf B S hS X Z).ι

end Square

/-! ### The flat clause of Stacks 04CQ -/

/-- **The map of defining ideal sheaves of a fibre product square along a flat morphism is an
isomorphism.** -/
theorem isIso_idealSheafMap_of_isFlat (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    IsIso (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z')) := by
  have hbal := balanced_modules B S hS X
  have hm := mono_idealSheafMap_of_isFlat B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z') hg (conormalEtaleRestrictionSquare B S hS g Z')
  have he := epi_idealSheafMap B S hS g Z'
  exact isIso_of_mono_of_epi _

/-! ### The canonical map at an étale restriction square -/

/-- Pure morphism algebra in a bare category: a two-factor composite rewritten one factor at a
time.  Stated with every object and morphism a variable, so that the concrete composites of
`AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom_of_eq` are matched
against it first-order. -/
private theorem comp_eq_of_both_factors {C : Type*} [Category C] {a b c : C} {u u' : a ⟶ b}
    {v v' : b ⟶ c} {w : a ⟶ c} (hu : u = u') (hv : v = v') (hw : u' ≫ v' = w) : u ≫ v = w :=
  (congrArg (fun t ↦ t ≫ v) hu).trans ((congrArg (fun t ↦ u' ≫ t) hv).trans hw)

/-- **The canonical map of [Stacks Project, Tag 04CP] at an étale restriction square is the
comparison isomorphism of [Stacks Project, Tag 04CO], granted the identity of the two maps of
ideal sheaves.**  For an étale `g : X ⟶ X'` and a closed subspace `Z' ⊆ X'`, both
`AlgebraicGeometry.Space.conormalMap` at the square of
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` and the forward map of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` are morphisms
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}`, and they agree as soon as their fibres over `X` do: that is, as
soon as the map `g^*𝓘' ⟶ 𝓘` of defining ideal sheaves of
`AlgebraicGeometry.Space.idealSheafMap` is the identification of [Stacks Project, Tag 03LW]
followed by the identification `𝓘'|_X = 𝓘` of
`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`.

This is the whole of the reduction: the two maps share their comparison factor on the nose, so
the hypothesis is the only thing that distinguishes them.  The hypothesis is an equation between
morphisms of `𝒪_X`-modules in which no closed subspace appears, and it is what the "What is not
proved" section of this file records as missing; see also the second bullet of the same section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean`, which this
declaration reduces to that one equation.

No `@[stacks]` attribute is claimed: a hypothesis-carrying form of a tag's clause must not carry
the bare tag. -/
theorem conormalMap_eq_conormalModuleEtaleRestrictionIso_hom_of_eq (g : X ⟶ X')
    (hg : IsEtale B S hS g.hom) (Z' : ClosedSubspaces B S hS X'.1)
    (h : idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
          (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z') =
        (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app
            (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫
          (etaleIdealSheafRestrictionIso B S hS g hg Z').hom) :
    conormalMap B S hS (preimageSubspace B S hS g Z') Z' g (preimageProjection B S hS g Z')
        (conormalEtaleRestrictionSquare B S hS g Z') =
      (conormalModuleEtaleRestrictionIso B S hS g hg Z').hom :=
  have e1 : conormalPullbackComparison B S hS
        (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
          ClosedSubspaces B S hS X.1) Z' g (ObjectProperty.homMk (Z'.1.fromPreimage g.hom))
        (conormalEtaleRestrictionSquare B S hS g Z') =
      (conormalPullbackCompIso B S hS
          (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
            ClosedSubspaces B S hS X.1) Z' g
          (ObjectProperty.homMk (Z'.1.fromPreimage g.hom))
          (conormalEtaleRestrictionSquare B S hS g Z')).hom.app
        (definingIdealSheaf B S hS X' Z').toSheafOfModules :=
    rfl
  have e2 : (modulePullback B S hS (subspaceInclusion B S hS X
          (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
            ClosedSubspaces B S hS X.1))).map
        (idealSheafMap B S hS
          (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
            ClosedSubspaces B S hS X.1) Z' g (ObjectProperty.homMk (Z'.1.fromPreimage g.hom))
          (conormalEtaleRestrictionSquare B S hS g Z')) =
      (modulePullback B S hS (subspaceInclusion B S hS X
            (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
              ClosedSubspaces B S hS X.1))).map
          ((modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app
            (definingIdealSheaf B S hS X' Z').toSheafOfModules) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X
            (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
              ClosedSubspaces B S hS X.1))).map
          (etaleIdealSheafRestrictionIso B S hS g hg Z').hom :=
    (congrArg (fun m ↦ (modulePullback B S hS (subspaceInclusion B S hS X
        (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
          ClosedSubspaces B S hS X.1))).map m) h).trans (Functor.map_comp _ _ _)
  (conormalMap_eq B S hS
      (⟨Z'.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z'.1 X'.2 X.2 Z'.2⟩ :
        ClosedSubspaces B S hS X.1) Z' g (ObjectProperty.homMk (Z'.1.fromPreimage g.hom))
      (conormalEtaleRestrictionSquare B S hS g Z')).trans
    (comp_eq_of_both_factors e1 e2 (conormalModuleEtaleRestrictionIso_hom B S hS g hg Z').symm)

/-- **The backward map of the comparison of [Stacks Project, Tag 03LW] at an identity-vertical
chart diagram.**  The inverse of the Stacks 03LW identification carries a section `t` of `M` over
the composite chart of `X'` to the chart section of `g^*M` attached to the identity-vertical chart
diagram of the chart of `X`.

This is the `restrict` coherence
`modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit` of the module
`EtaleSourceModulePullbackComparison` read backwards along the comparison, the backward reading
being what a morphism *out of* the étale restriction needs. -/
private theorem modulePullbackIsoEtaleModulePullback_inv_app_etaleUnit (g : X ⟶ X')
    (hg : IsEtale B S hS g.hom) (M : Modules.{u, u} B S hS X'.1 X'.2)
    (W : SmallEtale B S hS X.1)
    (t : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj W))) :
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M).val.app (op W) t =
      modulePullbackChartSection B S hS g M (ChartDiagram.etaleUnit B S hS g hg W) t :=
  have h465 := modulePullbackIsoEtaleModulePullback_hom_modulePullbackChartSection_etaleUnit
    B S hS g hg M W t
  have hid := (modulePullbackIsoEtaleModulePullback B S hS g hg).hom_inv_id_app M
  (congrArg
      (fun x ↦ ((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app M).val.app (op W) x)
      h465.symm).trans
    (congrArg (fun m ↦ m.val.app (op W)
      (modulePullbackChartSection B S hS g M (ChartDiagram.etaleUnit B S hS g hg W) t)) hid)

/-- The two morphisms `g^*𝓘'|_{X_étale} ⟶ 𝓘` agree on each section over each chart of `X`: both
are the identity on the underlying regular function.  On the left the backward comparison produces
a unit section, on which the map of defining ideal sheaves is pullback of regular functions along
the identity (`AlgebraicGeometry.Space.chartDiagramPullback_etaleUnit_apply`); on the right the
comparison of [Stacks Project, Tag 04CO] is the identity on regular functions outright. -/
private theorem idealSheafMap_etaleRestriction_app_eq (g : X ⟶ X')
    (hg : IsEtale B S hS g.hom) (Z' : ClosedSubspaces B S hS X'.1)
    (W : SmallEtale B S hS X.1)
    (x : ((etaleModulePullback.{u, u} B S hS g hg).obj
      (definingIdealSheaf B S hS X' Z').toSheafOfModules).val.obj (op W)) :
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app
          (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫
        idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
          (preimageProjection B S hS g Z')
          (conormalEtaleRestrictionSquare B S hS g Z')).val.app (op W) x =
      (etaleIdealSheafRestrictionIso B S hS g hg Z').hom.val.app (op W) x := by
  have h1 : ((modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app
        (definingIdealSheaf B S hS X' Z').toSheafOfModules).val.app (op W) x =
      modulePullbackUnitSection B S hS g
        (definingIdealSheaf B S hS X' Z').toSheafOfModules
        (ChartDiagram.etaleUnit B S hS g hg W) x :=
    Eq.trans
      (modulePullbackIsoEtaleModulePullback_inv_app_etaleUnit B S hS g hg
        (definingIdealSheaf B S hS X' Z').toSheafOfModules W x)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g
        (definingIdealSheaf B S hS X' Z').toSheafOfModules
        (ChartDiagram.etaleUnit B S hS g hg W) x).symm
  have h2 := idealSheafMap_unitSection_coe B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z')
    (ChartDiagram.etaleUnit B S hS g hg W) x
  have h3 := chartDiagramPullback_etaleUnit_apply B S hS g hg W (x : ToType _).1
  have h4 := etaleIdealSheafRestrictionIso_hom_apply_coe B S hS g hg Z' W x
  have h5 := congrArg (fun y ↦ (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z')
    (conormalEtaleRestrictionSquare B S hS g Z')).val.app (op W) y) h1
  exact h5.trans (Subtype.ext (h2.trans (h3.trans h4.symm)))

/-- The map of defining ideal sheaves, read through the backward comparison of
[Stacks Project, Tag 03LW], is the comparison isomorphism of [Stacks Project, Tag 04CO].  Both
sides are morphisms out of the étale restriction `𝓘'|_{X_étale}`, so both are determined by their
values at the identity-vertical chart diagrams
(`AlgebraicGeometry.Space.etaleRestrictHomOfModuleFMap`, a left inverse of the passage to the
linear map of sections), and there they agree by
`AlgebraicGeometry.Space.idealSheafMap_etaleRestriction_app_eq`. -/
private theorem modulePullbackIsoEtaleModulePullback_inv_comp_idealSheafMap_eq (g : X ⟶ X')
    (hg : IsEtale B S hS g.hom) (Z' : ClosedSubspaces B S hS X'.1) :
    (modulePullbackIsoEtaleModulePullback B S hS g hg).inv.app
          (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫
        idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
          (preimageProjection B S hS g Z')
          (conormalEtaleRestrictionSquare B S hS g Z') =
      (etaleIdealSheafRestrictionIso B S hS g hg Z').hom := by
  refine Function.LeftInverse.injective
    (etaleRestrictHom_moduleFMapOfEtaleRestrictHom B S hS g hg
      (definingIdealSheaf B S hS X (preimageSubspace B S hS g Z')).toSheafOfModules
      (definingIdealSheaf B S hS X' Z').toSheafOfModules) ?_
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun t ↦ ?_)
  exact idealSheafMap_etaleRestriction_app_eq B S hS g hg Z' d.U _

/-- **The map of defining ideal sheaves at an étale restriction square is the identification of
[Stacks Project, Tag 03LW] followed by the comparison of [Stacks Project, Tag 04CO].**  For an
étale `g : X ⟶ X'` and a closed subspace `Z' ⊆ X'`, the map `g^*𝓘' ⟶ 𝓘` of
`AlgebraicGeometry.Space.idealSheafMap` attached to the fibre product square is the Stacks 03LW
identification `g^*𝓘' ≅ 𝓘'|_{X_étale}` followed by the identification `𝓘'|_{X_étale} = 𝓘` of
`AlgebraicGeometry.Space.etaleIdealSheafRestrictionIso`.

This is the equation the "What is not proved" section of this file recorded as missing, and it is
the one hypothesis of
`AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom_of_eq`.

No `@[stacks]` attribute is claimed.  The identification of the canonical map of Stacks 04CP with
the comparison of Stacks 04CO is, as the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` records, the content of
Stacks 04G2 and 04CQ rather than of 04CO, and no clause of either is stated by this equation on
its own. -/
theorem idealSheafMap_eq_modulePullbackIsoEtaleModulePullback_hom_comp (g : X ⟶ X')
    (hg : IsEtale B S hS g.hom) (Z' : ClosedSubspaces B S hS X'.1) :
    idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
          (preimageProjection B S hS g Z')
          (conormalEtaleRestrictionSquare B S hS g Z') =
      (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app
          (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫
        (etaleIdealSheafRestrictionIso B S hS g hg Z').hom := by
  refine Eq.trans ?_ (congrArg
    (fun k ↦ (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app
      (definingIdealSheaf B S hS X' Z').toSheafOfModules ≫ k)
    (modulePullbackIsoEtaleModulePullback_inv_comp_idealSheafMap_eq B S hS g hg Z'))
  refine Eq.trans (Category.id_comp _).symm ?_
  refine Eq.trans (congrArg (fun m ↦ m ≫ idealSheafMap B S hS
    (preimageSubspace B S hS g Z') Z' g (preimageProjection B S hS g Z')
    (conormalEtaleRestrictionSquare B S hS g Z'))
    ((modulePullbackIsoEtaleModulePullback B S hS g hg).hom_inv_id_app
      (definingIdealSheaf B S hS X' Z').toSheafOfModules).symm) ?_
  exact Category.assoc _ _ _

/-- **The canonical map of [Stacks Project, Tag 04CP] at an étale restriction square is the
comparison isomorphism of [Stacks Project, Tag 04CO]**, with no hypothesis.  For an étale
`g : X ⟶ X'` and a closed subspace `Z' ⊆ X'`, the canonical map
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}` of conormal modules attached by
`AlgebraicGeometry.Space.conormalMap` to the square of
`AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` *is* the forward map of
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`; in particular it is an isomorphism.

This discharges the hypothesis of
`AlgebraicGeometry.Space.conormalMap_eq_conormalModuleEtaleRestrictionIso_hom_of_eq` with
`AlgebraicGeometry.Space.idealSheafMap_eq_modulePullbackIsoEtaleModulePullback_hom_comp`, whose
only missing ingredient was the `restrict` coherence of
`AlgebraicGeometry.Space.ModulePullbackEtaleSourceCoherence`.

No `@[stacks]` attribute is claimed, for the reason given on the equation it uses. -/
theorem conormalMap_eq_conormalModuleEtaleRestrictionIso_hom (g : X ⟶ X')
    (hg : IsEtale B S hS g.hom) (Z' : ClosedSubspaces B S hS X'.1) :
    conormalMap B S hS (preimageSubspace B S hS g Z') Z' g (preimageProjection B S hS g Z')
        (conormalEtaleRestrictionSquare B S hS g Z') =
      (conormalModuleEtaleRestrictionIso B S hS g hg Z').hom :=
  conormalMap_eq_conormalModuleEtaleRestrictionIso_hom_of_eq B S hS g hg Z'
    (idealSheafMap_eq_modulePullbackIsoEtaleModulePullback_hom_comp B S hS g hg Z')

/-- **The flat clause of [Stacks Project, Tag 04CQ], for closed immersions.**  If `g` is flat —
that is, if the morphism of small étale ringed topoi it induces is flat in the sense of
[Stacks Project, Tag 04JB] — then the canonical map of conormal modules
`f^*𝒞_{Z'/X'} ⟶ 𝒞_{g⁻¹(Z')/X}` of [Stacks Project, Tag 04CP] attached to the fibre product
square is an isomorphism. -/
@[stacks 04CQ "isomorphism when the morphism of small etale ringed topoi is flat"]
theorem isIso_conormalMap_of_isFlat (g : X ⟶ X') (Z' : ClosedSubspaces B S hS X'.1)
    (hg : (smallEtaleRingedToposHom B S hS g).IsFlat) :
    IsIso (conormalMap B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z')
      (conormalEtaleRestrictionSquare B S hS g Z')) := by
  have hc : IsIso (conormalPullbackComparison B S hS (preimageSubspace B S hS g Z') Z' g
      (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z')) :=
    NatIso.isIso_app_of_isIso _ _
  have hp : @IsIso _ _
      ((modulePullback B S hS
          (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'))).obj
        ((modulePullback B S hS g).obj
          (definingIdealSheaf B S hS X' Z').toSheafOfModules))
      (conormalModule B S hS X (preimageSubspace B S hS g Z'))
      ((modulePullback B S hS
          (subspaceInclusion B S hS X (preimageSubspace B S hS g Z'))).map
        (idealSheafMap B S hS (preimageSubspace B S hS g Z') Z' g
          (preimageProjection B S hS g Z')
          (conormalEtaleRestrictionSquare B S hS g Z'))) :=
    have := isIso_idealSheafMap_of_isFlat B S hS g Z' hg
    Functor.map_isIso _ _
  rw [conormalMap_eq B S hS (preimageSubspace B S hS g Z') Z' g
    (preimageProjection B S hS g Z') (conormalEtaleRestrictionSquare B S hS g Z')]
  exact IsIso.comp_isIso

end AlgebraicGeometry.Space

end
