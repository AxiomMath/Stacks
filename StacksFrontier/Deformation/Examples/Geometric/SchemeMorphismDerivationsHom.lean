module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafScheme
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSequenceTerms
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The third term of the deformation sequence as a group of maps into the conormal sheaf

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, with `Y` carrying the structure
morphism `pY`. The third term of the exact sequence of [Stacks Project, Tag 0E3V] is
`Der_k(𝒪_Y, f_*𝒪_X)`, built in
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismSequenceTerms.lean`. The arrows of that
sequence into and out of the third term come from the torsor structure of
[Stacks Project, Tag 04FJ], whose acting group is the sections of
`SheafHom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})` for a first-order thickening `i : X ⟶ X'`.

This file is the purely homological bridge between those two groups: it identifies
`Der_k(𝒪_Y, f_*𝒪_X)` with `Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})` whenever the conormal sheaf of `i`
is isomorphic to the structure sheaf of `X`, which is the case the sequence of
[Stacks Project, Tag 0E3V] is read in. No geometry of thickenings, deformations or torsors
enters: the two geometric inputs — the thickening `i` and the trivialisation of its conormal
sheaf — are hypotheses.

## Main definitions

* `Deformation.Examples.pullbackCotangentSheafHomAddEquiv`: the adjunction bijection
  `Stacks.Smooth.pullbackCotangentSheafHomEquiv` of
  `StacksFrontier/AlgebraicGeometry/Smooth/CotangentSheafScheme.lean`, upgraded to an additive
  equivalence `(a^*Ω_{X/S} ⟶ N) ≃+ (Ω_{X/S} ⟶ a_*N)`.
* `Deformation.Examples.schemeMorphismDerivationsEquivHom`: the third term
  `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of [Stacks Project, Tag 0E3V] as the group
  `Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})` of `𝒪_X`-module maps from the pulled-back sheaf of
  differentials to the conormal sheaf of a first-order thickening with trivialised conormal
  sheaf.
* `Deformation.Examples.adjunctionHomLinearEquiv`: the hom-set bijection of an adjunction between
  `R`-linear categories, as an `R`-linear equivalence. Mathlib has the additive upgrade but not
  this one.
* `Deformation.Examples.schemeMorphismDerivationsLinearEquivHom`: the same identification of the
  third term, `k`-linearly rather than merely additively.

## Main results

* `Deformation.Examples.pullbackCotangentSheafHomAddEquiv_toEquiv`: the additive upgrade is the
  bijection `Stacks.Smooth.pullbackCotangentSheafHomEquiv` and nothing else, so the two
  may be used interchangeably.
* `Deformation.Examples.schemeMorphismDerivationsEquivHom_apply`: the chain's underlying map,
  unfolded, for use by the arrows of the sequence.
* `Deformation.Examples.pushforward_linear`: pushforward along a morphism of schemes over the
  residue field is `k`-linear. This is what makes the identification of the third term `k`-linear
  and not merely additive.

## Implementation notes

Additivity of the adjunction bijection is Mathlib's
`CategoryTheory.Adjunction.homAddEquiv`, which applies because
`AlgebraicGeometry.Scheme.Modules` is preadditive and `AlgebraicGeometry.Scheme.Modules.pullback`
is an additive functor; no transport is needed and the resulting `AddEquiv` has the existing
`Equiv` as its underlying bijection on the nose. Postcomposition with an isomorphism of the
target is `Stacks.Injectives.homCongrAddEquiv` of
`StacksFrontier/Homology/Injectives/FilteredComplex/HomComplex.lean`, which is stated for an
arbitrary preadditive category and so applies here unchanged; it is reused rather than restated.

The three steps of the chain that are not equivalences are identifications of spellings, all of
which hold by `rfl`:

* `Stacks.Smooth.cotangentSheaf pY` is `moduleOfDifferentials pY.toLRSHom.toShHom`, because
  `Stacks.Smooth.ringedSpaceHom pY` is `pY.toLRSHom.toShHom`
  (`Stacks.Smooth.cotangentSheaf_eq`);
* `AlgebraicGeometry.Scheme.Modules.pushforward f` is
  `RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom`
  (`Stacks.ProjectionFormula.modulePushforward_eq_schemePushforward`), so
  `Deformation.Examples.schemeMorphismPushforwardStructureSheaf f` is the scheme-level
  pushforward of the structure sheaf of `X`;
* `SheafOfModules.unit (structureSheafRing X.toRingedSpace)` is
  `SheafOfModules.unit X.ringCatSheaf`, because `structureSheafRing X.toRingedSpace` is
  `X.ringCatSheaf` (`Stacks.RingedSpaceModules.schemeRingCatSheaf_eq_ringSheaf`); it is
  therefore also `AlgebraicGeometry.Scheme.unitModule X`. The
  `structureSheafRing` spelling is the one used here, because it is the one
  `Deformation.Examples.schemeMorphismPushforwardStructureSheaf` and
  `Stacks.Thickenings.conormalι` are already stated at.

These identifications are made by `AddEquiv.refl` and `LinearEquiv.refl` at a declared type
(`Deformation.Examples.derivationsHomAddEquivAux`,
`Deformation.Examples.derivationsHomLinearEquivAux`) rather than by `rw` or `simp`: the two
spellings of a category of sheaves of modules on a scheme are equal by `rfl` but not with
reducible transparency, so a rewrite refuses the motive while a term-mode ascription goes
through. This is the escape hatch documented in
`StacksFrontier/AlgebraicGeometry/RingedSpaceModuleSpellings.lean`.

The structure sheaf of `X` is spelled two ways here, deliberately. The hypothesis trivialising
the conormal sheaf is stated at `SheafOfModules.unit (structureSheafRing X.toRingedSpace)`,
which is the spelling the conormal sheaf itself
(`Stacks.Thickenings.immersionConormalSheaf`) and the inclusion
`Stacks.Thickenings.conormalι` are stated at, so a caller needs no bridge. The chain is then run
at `AlgebraicGeometry.Scheme.unitModule X`, to which that hypothesis is converted by a
declared-type `let`. The conversion is needed because the two are equal only by `rfl`: the
former's type is a `SheafOfModules`, and instance search — which runs at reducible transparency,
where neither `AlgebraicGeometry.Scheme.Modules` nor `AlgebraicGeometry.structureSheafRing`
unfolds — then fails to find the additive structure on a group of morphisms into it, so the
middle term of the chain has no `Add`. `AlgebraicGeometry.Scheme.unitModule` has `X.Modules` as
its declared type and the search succeeds. The third spelling,
`SheafOfModules.unit X.ringCatSheaf`, is what `AlgebraicGeometry.Scheme.unitModule` unfolds to;
all three are interchangeable in term position and none of them in instance position.

The `k`-linear refinement needs two things beyond the additive one. Mathlib has no linear
counterpart of `CategoryTheory.Adjunction.homAddEquiv`, so
`Deformation.Examples.adjunctionHomLinearEquiv` supplies it, for an adjunction between `R`-linear
categories with additive left adjoint and `R`-linear right adjoint. The hypothesis it needs here
is that `AlgebraicGeometry.Scheme.Modules.pushforward f` is `k`-linear for the two actions
`AlgebraicGeometry.modulesLinear k (Over.mk pY)` on `Y.Modules` and
`AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))` on `X.Modules`. That is not a formal
consequence of the adjunction but a compatibility of `AlgebraicGeometry.baseRingToCenter` with
pushforward, and it is already proved: `AlgebraicGeometry.over_pushforward_linear`, applied to `f`
read as a morphism of schemes over the residue field by `CategoryTheory.Over.homMk`, which is
`Deformation.Examples.pushforward_linear`. The `k`-actions are supplied by `letI` throughout and
never left to instance search, `AlgebraicGeometry.modulesLinear` being a definition rather than an
instance; each `letI` carries its declared type, because the action's own spelling mentions
`(Over.mk (f ≫ pY)).left` rather than `X`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (moduleOfDifferentials)

universe u

namespace Deformation.Examples

/-! ### The adjunction bijection as an additive equivalence -/

/-- **The adjunction bijection out of a pulled-back sheaf of differentials is additive.** For
`f : X ⟶ S` and `a : T ⟶ X`, morphisms `a^*Ω_{X/S} ⟶ N` form a group isomorphic to the group of
morphisms `Ω_{X/S} ⟶ a_*N`. This is `Stacks.Smooth.pullbackCotangentSheafHomEquiv` with its
additivity recorded: the adjunction is between preadditive categories and its left adjoint
`AlgebraicGeometry.Scheme.Modules.pullback a` is additive, so Mathlib's
`CategoryTheory.Adjunction.homAddEquiv` applies. -/
@[ega "IV 16.5.14" "more general"]
def pullbackCotangentSheafHomAddEquiv {X S T : Scheme.{u}} (g : X ⟶ S) (a : T ⟶ X)
    (N : T.Modules) :
    (Stacks.Smooth.pullbackCotangentSheaf g a ⟶ N) ≃+
      (Stacks.Smooth.cotangentSheaf g ⟶ (Scheme.Modules.pushforward a).obj N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction a).homAddEquiv _ _

/-- `Deformation.Examples.pullbackCotangentSheafHomAddEquiv` is the adjunction bijection
`Stacks.Smooth.pullbackCotangentSheafHomEquiv`, with no change to the underlying map. -/
theorem pullbackCotangentSheafHomAddEquiv_toEquiv {X S T : Scheme.{u}} (g : X ⟶ S) (a : T ⟶ X)
    (N : T.Modules) :
    (pullbackCotangentSheafHomAddEquiv g a N).toEquiv =
      Stacks.Smooth.pullbackCotangentSheafHomEquiv g a N :=
  rfl

/-- `Deformation.Examples.pullbackCotangentSheafHomAddEquiv` sends a morphism to the unit of the
adjunction followed by the pushforward of that morphism. -/
theorem pullbackCotangentSheafHomAddEquiv_apply {X S T : Scheme.{u}} (g : X ⟶ S) (a : T ⟶ X)
    (N : T.Modules) (φ : Stacks.Smooth.pullbackCotangentSheaf g a ⟶ N) :
    pullbackCotangentSheafHomAddEquiv g a N φ =
      (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          (Stacks.Smooth.cotangentSheaf g) ≫ (Scheme.Modules.pushforward a).map φ :=
  rfl

/-! ### The third term as a group of maps into the conormal sheaf -/

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}}

/-- **The two spellings of the coefficient module of the third term agree.** The group of
`𝒪_Y`-module maps `Ω_{Y/k} ⟶ f_*𝒪_X` that
`Deformation.Examples.schemeMorphismDerivationsAddEquiv` is stated at, in the ringed-space
vocabulary, is the group of maps out of `Stacks.Smooth.cotangentSheaf pY` into the scheme-level
pushforward of the structure sheaf of `X`. Both spellings denote the same group, so the
identification is the identity; it is made at a declared type because the equality of the two
categories of sheaves of modules holds by `rfl` but not with reducible transparency. -/
def derivationsHomAddEquivAux (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) :
    (moduleOfDifferentials pY.toLRSHom.toShHom ⟶ schemeMorphismPushforwardStructureSheaf f) ≃+
      (Stacks.Smooth.cotangentSheaf pY ⟶
        (Scheme.Modules.pushforward f).obj (Scheme.unitModule X)) :=
  AddEquiv.refl _

/-- **Stacks 0E3V, the third term as a group of maps into the conormal sheaf.** Let `f : X ⟶ Y`
be a morphism of schemes with `Y` over the residue field through `pY`, let `i : X ⟶ X'` be a
closed immersion, and suppose its conormal sheaf `𝒞_{X/X'}` is trivialised, that is isomorphic
to the structure sheaf of `X`. Then the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's exact
sequence is the group `Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})` of `𝒪_X`-module maps from the sheaf of
differentials of `Y` pulled back along `f` into that conormal sheaf — the group that acts on the
lifts of `f` along `i` in [Stacks Project, Tag 04FJ].

The chain is: a derivation is a map out of the module of differentials
(`Deformation.Examples.schemeMorphismDerivationsAddEquiv`, by the corepresentability of
derivations of [Stacks Project, Tag 04BL]); such a map is a map out of the pullback
(`Deformation.Examples.pullbackCotangentSheafHomAddEquiv`, by the adjunction between pullback
and pushforward); and the target may be moved along the trivialisation
(`Stacks.Injectives.homCongrAddEquiv`). -/
def schemeMorphismDerivationsEquivHom (f : X ⟶ Y)
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) {X' : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i]
    (e : Stacks.Thickenings.conormalModules i ≅
      SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :
    schemeMorphismDerivations f pY ≃+
      (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules i) :=
  let e' : Stacks.Thickenings.conormalModules i ≅ Scheme.unitModule X := e
  (((schemeMorphismDerivationsAddEquiv f pY
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).symm.trans
        (derivationsHomAddEquivAux f pY)).trans
      (pullbackCotangentSheafHomAddEquiv pY f (Scheme.unitModule X)).symm).trans
    (Stacks.Injectives.homCongrAddEquiv (Iso.refl _) e'.symm)

/-- `Deformation.Examples.schemeMorphismDerivationsEquivHom` on an element: undo the
corepresentability of derivations, cross the adjunction, then compose with the inverse of the
trivialisation of the conormal sheaf. -/
theorem schemeMorphismDerivationsEquivHom_apply (f : X ⟶ Y)
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) {X' : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i]
    (e : Stacks.Thickenings.conormalModules i ≅
      SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (D : schemeMorphismDerivations f pY) :
    schemeMorphismDerivationsEquivHom f pY i e D =
      (Stacks.Smooth.pullbackCotangentSheafHomEquiv pY f (Scheme.unitModule X)).symm
          ((schemeMorphismDerivationsAddEquiv f pY
            (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).symm D) ≫ e.inv := by
  simp only [schemeMorphismDerivationsEquivHom, AddEquiv.trans_apply,
    Stacks.Injectives.homCongrAddEquiv_apply, Iso.refl_inv, Category.id_comp]
  rfl

/-! ### The `k`-linear refinement -/

/-- **The adjunction bijection is linear over the base ring.** For an adjunction between
`R`-linear categories whose left adjoint is additive and whose right adjoint is `R`-linear, the
hom-set bijection `CategoryTheory.Adjunction.homEquiv` is an `R`-linear equivalence: it is
`φ ↦ unit ≫ G.map φ`, and `G.map` is `R`-linear while composition is `R`-linear on the right.
Mathlib records the additive upgrade (`CategoryTheory.Adjunction.homAddEquiv`) but not the
linear one. -/
def adjunctionHomLinearEquiv {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (R : Type*) [CommRing R] [Linear R C] [Linear R D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [F.Additive] [G.Linear R] (A : C) (B : D) :
    (F.obj A ⟶ B) ≃ₗ[R] (A ⟶ G.obj B) :=
  (adj.homAddEquiv A B).toLinearEquiv fun r φ => by
    simp only [Adjunction.homAddEquiv_apply, Adjunction.homEquiv_unit, Functor.map_smul,
      Linear.comp_smul]

/-- **Pushforward along a morphism of schemes over `k` is `k`-linear.** `X` is a scheme over the
residue field through `f ≫ pY` and `Y` is one through `pY`, so `f` is a morphism of schemes over
the residue field and `AlgebraicGeometry.over_pushforward_linear` applies: the scalar is pulled
back from the base in both spellings. -/
theorem pushforward_linear (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
    letI : Linear k Y.Modules := modulesLinear k (Over.mk pY)
    (Scheme.Modules.pushforward f).Linear k :=
  let : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
  let : Linear k Y.Modules := modulesLinear k (Over.mk pY)
  over_pushforward_linear k (Over.homMk f rfl : Over.mk (f ≫ pY) ⟶ Over.mk pY)

/-- The `k`-linear form of `Deformation.Examples.derivationsHomAddEquivAux`: the two spellings of
the group of `𝒪_Y`-module maps `Ω_{Y/k} ⟶ f_*𝒪_X` carry the same `k`-action, that of
`AlgebraicGeometry.modulesLinear k (Over.mk pY)`, so the identification is the identity. -/
def derivationsHomLinearEquivAux (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) :
    letI : Linear k Y.Modules := modulesLinear k (Over.mk pY)
    letI : Module k (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
        schemeMorphismPushforwardStructureSheaf f) :=
      (modulesLinear k (Over.mk pY)).homModule _ _
    (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
        schemeMorphismPushforwardStructureSheaf f) ≃ₗ[k]
      (Stacks.Smooth.cotangentSheaf pY ⟶
        (Scheme.Modules.pushforward f).obj (Scheme.unitModule X)) :=
  letI : Linear k Y.Modules := modulesLinear k (Over.mk pY)
  letI : Module k (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
      schemeMorphismPushforwardStructureSheaf f) :=
    (modulesLinear k (Over.mk pY)).homModule _ _
  LinearEquiv.refl k _

/-- **Stacks 0E3V, the third term as a `k`-vector space of maps into the conormal sheaf.** The
`k`-linear refinement of `Deformation.Examples.schemeMorphismDerivationsEquivHom`: the
identification of the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's exact sequence with
`Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒞_{X/X'})` is linear for the `k`-vector space structure
`Deformation.Examples.schemeMorphismDerivationsModule` on the former and the `k`-action of
`AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))` on the latter.

Each of the three steps is linear: the corepresentability of derivations transports the action by
construction (`Deformation.Examples.schemeMorphismDerivationsLinearEquiv`), the adjunction
bijection is linear because pushforward is (`Deformation.Examples.pushforward_linear` feeding
`Deformation.Examples.adjunctionHomLinearEquiv`), and postcomposition with an isomorphism is
linear (`CategoryTheory.Linear.homCongr`). -/
def schemeMorphismDerivationsLinearEquivHom (f : X ⟶ Y)
    (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) {X' : Scheme.{u}} (i : X ⟶ X')
    [IsClosedImmersion i]
    (e : Stacks.Thickenings.conormalModules i ≅
      SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
    letI := schemeMorphismDerivationsModule f pY
      (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    schemeMorphismDerivations f pY ≃ₗ[k]
      (Stacks.Smooth.pullbackCotangentSheaf pY f ⟶ Stacks.Thickenings.conormalModules i) :=
  let e' : Stacks.Thickenings.conormalModules i ≅ Scheme.unitModule X := e
  letI : Linear k X.Modules := modulesLinear k (Over.mk (f ≫ pY))
  letI : Linear k Y.Modules := modulesLinear k (Over.mk pY)
  letI : (Scheme.Modules.pushforward f).Linear k := pushforward_linear f pY
  letI : Module k (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
      schemeMorphismPushforwardStructureSheaf f) :=
    (modulesLinear k (Over.mk pY)).homModule _ _
  letI := schemeMorphismDerivationsModule f pY
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
  ((schemeMorphismDerivationsLinearEquiv f pY
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace))).trans
        (derivationsHomLinearEquivAux f pY)).trans
    ((adjunctionHomLinearEquiv k (Scheme.Modules.pullbackPushforwardAdjunction f)
          (Stacks.Smooth.cotangentSheaf pY) (Scheme.unitModule X)).symm.trans
      (Linear.homCongr k (Iso.refl _) e'.symm))

end Deformation.Examples

end
