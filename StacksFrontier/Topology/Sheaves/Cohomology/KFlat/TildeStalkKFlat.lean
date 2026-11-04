module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.PullbackFromTheStalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The stalk of an associated sheaf, and K-flatness of `M̃^•`

Let `R` be a commutative ring and `x` a point of `Spec R`. This file identifies the stalk at `x`
of the associated sheaf `M̃` of an `R`-module `M` with the base change of `M` along the germ map
`R ⟶ 𝒪_{Spec R, x}`,

`(M̃)_x ≅ 𝒪_{Spec R,x} ⊗_R M`,

**naturally in `M`** and over the stalk ring, and deduces that degreewise sheafification carries
a K-flat complex of `R`-modules to a K-flat complex of `𝒪_{Spec R}`-modules.

## The proof compares right adjoints

Nothing is computed about `tilde`. Both sides of the asserted isomorphism are left adjoints:

* `~ ⋙ (-)_x` is left adjoint to `i_{x,*} ⋙ Γ`, by `AlgebraicGeometry.tilde.adjunction` composed
  with `AlgebraicGeometry.SheafOfModules.stalkSkyscraperAdjunction`;
* `𝒪_{Spec R,x} ⊗_R -` is left adjoint to restriction of scalars, by
  `ModuleCat.extendRestrictScalarsAdj`.

So an isomorphism of the right adjoints transports to one of the left adjoints, and the right
adjoints are concrete: the global sections of the skyscraper sheaf at `x` with value an
`𝒪_{Spec R,x}`-module `N` are the constant functions on `PLift (x ∈ ⊤)` with values in `N`, with
`r : R` acting through its germ at `x`. That is `specSkyscraperSectionsIso`, and it is the only
computation in the file — its two linearity obligations and both triangle identities hold by
`rfl`, because the action on the sections of a skyscraper is *defined* by composing with the germ
map, which is exactly how `specStalkRingHom` is built.

This is the same architecture as `Stacks.RingedSpace.stalkModulePullbackFunctorIso` (Stacks 0098
for `RingedSpaceModuleAdjunction.modulePullback`), and the same architecture as
`AlgebraicGeometry.pullbackTildeIso` (Stacks 01I9), which obtains the pullback–tilde comparison
from `tilde.adjunction` by `CategoryTheory.Adjunction.leftAdjointUniq` in the same way.

## Main definitions

* `Stacks.TildeStalk.specStalkFunctor` — the stalk functor at `x`, spelled with source
  `(Spec R).Modules`.
* `Stacks.TildeStalk.specStalkRingHom` — the germ map `R ⟶ 𝒪_{Spec R, x}`, namely the global
  sections isomorphism of Stacks 01HR followed by the germ at `x`.
* `Stacks.TildeStalk.tildeStalkBaseChange` — the base-change functor
  `M ↦ 𝒪_{Spec R,x} ⊗_R M` on stalk modules.
* `Stacks.TildeStalk.specSkyscraperSectionsIso` — the global sections of a skyscraper at `x` are
  restriction of scalars along `specStalkRingHom`.

## Main results

* `Stacks.TildeStalk.tildeStalkFunctorIso` — **the stalk of an associated sheaf, naturally in the
  module**: `~ ⋙ (-)_x ≅ 𝒪_{Spec R,x} ⊗_R -`.
* `Stacks.TildeStalk.tildeStalkComplexIso` — the same identification degreewise on complexes,
  which is the form the stalk criterion for K-flatness consumes.
* `Stacks.TildeStalk.kFlatStalkwise_tilde` and `Stacks.TildeStalk.kFlatComplex_tilde` —
  **degreewise sheafification preserves K-flatness**, stalkwise and then absolutely.
* `Stacks.TildeStalk.kFlatTilde` — the same conclusion in the shape
  `AlgebraicGeometry.KFlatTilde`, which is the one remaining input of Stacks 08DW part (2).
  No tag attribute is placed anywhere in this file: which declarations form the covering set of
  08DW is that tag's own call, and the stalk identification itself belongs to Stacks 01HV.

## Implementation notes

*Three spellings of one category, and which one lets `Additive` fire.* `specStalkFunctor` is
`AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing (Spec R).toRingedSpace) x` with
its source written as `(Spec R).Modules`, and it exists for exactly one reason: `tilde.functor R`
lands in `(Spec R).Modules`, so in the composite `tilde.functor R ⋙ stalkFunctor _ x` the middle
category is presented that way, and then `CategoryTheory.Functor.instAdditiveComp` does **not**
find `Additive` for the stalk functor, whose instance `stalkFunctor_additive` is keyed at the
`SheafOfModules (structureSheafRing _)` spelling — a hard synthesis failure, together
with a `PreservesZeroMorphisms` failure for the composite. Restating the functor at
`(Spec R).Modules` and re-seating the instance there removes both, and nothing else changes: the
two functors are equal by `rfl`. This is the mirror image of the note in
`StacksDraft.AlgebraicGeometry.Duality.DerivedTildeFold.AffinePullbackComparison`, where the
degreewise pullback had to be written `Scheme.Modules.pullback` for the same reason.

*Commutativity of the stalk ring is seated by hand.* `ModuleCat.extendScalars` and
`ModuleCat.extendRestrictScalarsAdj` need both rings commutative, and the `RingCat`-valued stalk
carries only a `Ring` instance. `Stacks.RingedSpace.structureStalkCommRing` is seated with `letI`
inside the two declarations that need it, so that the *statements* keep the `RingCat` instances
and the elaborator checks one definitional equality instead of searching for it in every
consumer; the reason a `CommRing` instance must not be in scope here is recorded in
`StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback`.

A second commutativity route reaches the same ring,
`StacksDraft.StalkTensor.commRing_stalk_ringSheaf`, which is the instance baked into
`AlgebraicGeometry.SheafOfModules.KFlatStalkwise` and into
`Stacks.SheafOfModules.KFlatPullback.kFlat_of_stalkIso`. The two agree — each is the `RingCat`
  `Ring` instance extended
by a proof of `mul_comm` — so the crossing between them is proof irrelevance, and the final proof
is in term mode where it is discharged by unification.

*Why the stalkwise statement is proved by `intro` and not stated.* `CochainComplex.KFlat` applied
to `stalkComplex (Spec R).sheaf x K` cannot be *written down* at `Spec R`: the `CommRing` instance
has to be found for a stalk of `(Spec R).sheaf`, whose type is `TopCat.Sheaf CommRingCat`, and
synthesis is stuck on `max ?u ?v =?= u` there rather than failing. Inside
`KFlatStalkwise (Spec R).sheaf _` the instance is already fixed, having been resolved once at the
site spelling in the generic declaration, so the goal after `intro` is writable even though the
statement is not.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.SheafOfModules
open Stacks.RingedSpace

universe u

noncomputable section

namespace Stacks.TildeStalk

variable (R : CommRingCat.{u}) (x : (Spec R).carrier)

/-! ### The stalk functor at the spelling the composite with `tilde` needs -/

/-- **Taking stalks at `x` of a sheaf of modules on `Spec R`**, as a functor out of
`(Spec R).Modules`.

This is
`AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing (Spec R).toRingedSpace) x`,
restated with its source spelled the way `AlgebraicGeometry.tilde.functor` presents its target.
The restatement is forced: see the implementation note at the head of this file. -/
def specStalkFunctor :
    (Spec R).Modules ⥤ ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec R).toRingedSpace).obj x) :=
  stalkFunctor (structureSheafRing (Spec R).toRingedSpace) x

/-- `specStalkFunctor` is additive, being `stalkFunctor` and nothing else. Re-seating the
instance at this spelling is what lets `Additive` be found for the composite with
`AlgebraicGeometry.tilde.functor`. -/
instance specStalkFunctor_additive : (specStalkFunctor R x).Additive :=
  stalkFunctor_additive (structureSheafRing (Spec R).toRingedSpace) x

/-! ### Base change along the germ map -/

/-- **The germ map `R ⟶ 𝒪_{Spec R, x}`**: the inverse of the global sections isomorphism of
Stacks 01HR followed by the germ at `x` of the structure sheaf, read for the `RingCat`-valued
structure sheaf that `SheafOfModules` is stated for. -/
def specStalkRingHom :
    R →+* ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec R).toRingedSpace).obj x) :=
  (TopCat.Presheaf.germ (C := RingCat.{u}) (structureSheafRing (Spec R).toRingedSpace).obj
      ⊤ x trivial).hom.comp (Scheme.ΓSpecIso R).inv.hom

/-- **Base change along the germ map**, `M ↦ 𝒪_{Spec R,x} ⊗_R M`. This is
`ModuleCat.extendScalars` of `specStalkRingHom`, stated at the `Ring` instance the
`RingCat`-valued stalk carries; its carrier is `ModuleCat.ExtendScalars.obj'`. -/
def tildeStalkBaseChange :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec R).toRingedSpace).obj x) :=
  letI := structureStalkCommRing (Spec R).toRingedSpace x
  ModuleCat.extendScalars.{u, u, u} (specStalkRingHom R x)

/-- Base change along the germ map is left adjoint to restriction of scalars along it: this is
`ModuleCat.extendRestrictScalarsAdj`, with the commutativity of the stalk ring seated by hand. -/
def tildeStalkBaseChangeAdjunction :
    tildeStalkBaseChange R x ⊣ ModuleCat.restrictScalars.{u, u, u} (specStalkRingHom R x) :=
  letI := structureStalkCommRing (Spec R).toRingedSpace x
  ModuleCat.extendRestrictScalarsAdj.{u, u, u} (specStalkRingHom R x)

/-- Base change of stalk modules is additive, so it can be applied to a complex degreewise. It is
a left adjoint, hence preserves colimits, hence preserves binary biproducts, hence is additive.

The shorter route through `CategoryTheory.Adjunction.left_adjoint_additive` is not available: the
`Additive` instance for `ModuleCat.restrictScalars` does not fire at the `Ring` instance that
`CommRing.toRing (structureStalkCommRing ..)` puts on the stalk. -/
instance tildeStalkBaseChange_additive : (tildeStalkBaseChange R x).Additive :=
  haveI : PreservesColimits (tildeStalkBaseChange R x) :=
    (tildeStalkBaseChangeAdjunction R x).leftAdjoint_preservesColimits
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tildeStalkBaseChange R x)
  Functor.additive_of_preservesBinaryBiproducts _

/-! ### The content: global sections of a skyscraper on `Spec R` -/

section Skyscraper

attribute [local instance] AlgebraicGeometry.SheafOfModules.skyscraperModule

/-- **The global sections of a skyscraper sheaf at `x`**, as an `R`-module, are the value of the
skyscraper with scalars restricted along the germ map.

A section over `⊤` is a function on `PLift (x ∈ ⊤)`, a subsingleton, so evaluating at the unique
proof is bijective; and `r : R` acts on such a section by scaling its value by the germ at `x` of
`r`, which is `specStalkRingHom` applied to `r`. Both linearity obligations and both triangle
identities therefore hold by `rfl`, up to the proof irrelevance that identifies the two
membership proofs. -/
def specSkyscraperSectionsObjIso
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing (Spec R).toRingedSpace).obj x)) :
    moduleSpecΓFunctor.obj (skyscraperObj (structureSheafRing (Spec R).toRingedSpace) x N) ≅
      (ModuleCat.restrictScalars.{u, u, u} (specStalkRingHom R x)).obj N where
  hom := ModuleCat.ofHom
    (X := moduleSpecΓFunctor.obj (skyscraperObj (structureSheafRing (Spec R).toRingedSpace) x N))
    (Y := (ModuleCat.restrictScalars.{u, u, u} (specStalkRingHom R x)).obj N)
    { toFun := fun s => s ⟨trivial⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  inv := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars.{u, u, u} (specStalkRingHom R x)).obj N)
    (Y := moduleSpecΓFunctor.obj (skyscraperObj (structureSheafRing (Spec R).toRingedSpace) x N))
    { toFun := fun n => fun _ => n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  hom_inv_id := by ext s; funext h; rfl
  inv_hom_id := by ext n; rfl

/-- **The right adjoint of `~ ⋙ (-)_x` is restriction of scalars along the germ map.** This is
`specSkyscraperSectionsObjIso` as an isomorphism of functors; naturality is `rfl`, both sides
applying the given linear map to the value of a section. -/
def specSkyscraperSectionsIso :
    skyscraperFunctor (structureSheafRing (Spec R).toRingedSpace) x ⋙ moduleSpecΓFunctor ≅
      ModuleCat.restrictScalars.{u, u, u} (specStalkRingHom R x) :=
  NatIso.ofComponents (fun N => specSkyscraperSectionsObjIso R x N) (fun _ => by ext; rfl)

end Skyscraper

/-! ### The stalk of an associated sheaf -/

/-- Sheafification followed by the stalk at `x` is left adjoint to the skyscraper at `x` followed
by global sections: a composite of `AlgebraicGeometry.tilde.adjunction` with the
stalk–skyscraper adjunction. -/
def tildeStalkAdjunction :
    tilde.functor R ⋙ specStalkFunctor R x ⊣
      skyscraperFunctor (structureSheafRing (Spec R).toRingedSpace) x ⋙ moduleSpecΓFunctor :=
  (tilde.adjunction (R := R)).comp
    (stalkSkyscraperAdjunction (structureSheafRing (Spec R).toRingedSpace) x)

/-- **Stacks 01HV, functorially and over the stalk ring.** The stalk at `x` of the sheaf
associated to an `R`-module is the base change of that module along the germ map
`R ⟶ 𝒪_{Spec R,x}`, naturally in the module:

`~ ⋙ (-)_x ≅ 𝒪_{Spec R,x} ⊗_R -`.

Both sides are left adjoints and their right adjoints are isomorphic by
`specSkyscraperSectionsIso`, so this is the uniqueness of a left adjoint. Nothing about the
sections of `tilde` is used; in particular the `IsLocalizedModule` instance of
`AlgebraicGeometry.tilde.toStalk` and the element equation
`AlgebraicGeometry.tilde.toStalk_map` are not needed. -/
def tildeStalkFunctorIso :
    tilde.functor R ⋙ specStalkFunctor R x ≅ tildeStalkBaseChange R x :=
  ((tildeStalkAdjunction R x).ofNatIsoRight (specSkyscraperSectionsIso R x)).leftAdjointUniq
    (tildeStalkBaseChangeAdjunction R x)

/-- **The complex-level form of Stacks 01HV.** Sheafifying a complex of `R`-modules degreewise and
then taking stalks at `x` degreewise is base changing degreewise along the germ map.

This is the form the stalk criterion for K-flatness consumes, and it is
`tildeStalkFunctorIso` transported by `CategoryTheory.NatIso.mapHomologicalComplex`: the stalk
complex of `M̃^•` is the value at `M^•` of `(~ ⋙ (-)_x)` applied degreewise, the two readings of
that composite being equal by `rfl`. -/
def tildeStalkComplexIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    AlgebraicGeometry.SheafOfModules.stalkComplex (Spec R).sheaf x
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((tildeStalkBaseChange R x).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (NatIso.mapHomologicalComplex (tildeStalkFunctorIso R x) (ComplexShape.up ℤ)).app K

/-! ### K-flatness -/

/-- **Degreewise sheafification preserves K-flatness, stalkwise.** For a K-flat complex `M^•` of
`R`-modules, the stalk complex of `M̃^•` at every point of `Spec R` is K-flat over the stalk ring.

The stalk complex is a base change of `M^•` along the germ map by `tildeStalkComplexIso`, and
extension of scalars along an arbitrary ring homomorphism preserves K-flatness, which is
Stacks 06Y1 (`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`). -/
theorem kFlatStalkwise_tilde (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) :
    AlgebraicGeometry.SheafOfModules.KFlatStalkwise (Spec R).sheaf
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  intro y
  let _ := structureStalkCommRing (Spec R).toRingedSpace y
  exact Stacks.SheafOfModules.KFlatPullback.kFlat_of_stalkIso (Spec R).sheaf y (tildeStalkComplexIso
    R y K).symm
    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u}
      (specStalkRingHom R y) K hK)

/-- **Degreewise sheafification carries a K-flat complex of `R`-modules to a K-flat complex of
`𝒪_{Spec R}`-modules.** This is `kFlatStalkwise_tilde` followed by the half of the stalk criterion
for K-flatness (Stacks 06YB) that reads K-flatness off the stalks, which is available
unconditionally as `Stacks.SheafOfModules.KFlatPullback.stalkCriterion`. -/
theorem kFlatComplex_tilde (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex (Spec R).toRingedSpace
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Stacks.SheafOfModules.KFlatPullback.stalkCriterion.kFlat_of_kFlatStalkwise (Spec R).toRingedSpace
    _
    (kFlatStalkwise_tilde R K hK)

/-- `kFlatComplex_tilde` packaged as the hypothesis it discharges: the single remaining input of
Stacks 08DW part (2), carried as
`AlgebraicGeometry.KFlatTilde` by
`StacksDraft.AlgebraicGeometry.Duality.DerivedTildeFold.AffinePullbackComparison`. That
hypothesis is an `abbrev`, so this term also discharges it at every consumer by `exact`. -/
theorem kFlatTilde (R : CommRingCat.{u}) :
    ∀ K : CochainComplex (ModuleCat.{u} R) ℤ, CochainComplex.KFlat.{u, u} K →
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex (Spec R).toRingedSpace
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  fun K hK => kFlatComplex_tilde R K hK

end Stacks.TildeStalk

end

end
