module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# A projection formula for Ext

Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type, `E` a perfect
object of `D(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with
support proper over `S` — the situation of [Stacks, Tag 0DJQ], where
`K = Rf_*(E ⊗^L_{𝒪_X} 𝒢)` is shown to be perfect.  [Stacks, Tag 0A1F] asserts functorial
isomorphisms

`H^i(S, K ⊗^L_{𝒪_S} ℱ) ≅ H^i(X, E ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ))`

for `ℱ` an `𝒪_S`-module, compatible with boundary maps.

## Main definitions

* `Stacks.Cohomology.ExtProjectionFormula.tensorModuleComplex` is `M ↦ 𝒢 ⊗_{𝒪_X} M`, the
  degreewise tensor product of a complex with a module, as a functor of the module.
* `Stacks.Cohomology.ExtProjectionFormula.pullbackTensorFunctor` is
  `ℱ ↦ E ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ)` and
  `Stacks.Cohomology.ExtProjectionFormula.baseTensorFunctor` is `ℱ ↦ K ⊗^L_{𝒪_S} ℱ`: the two
  sides of the tag, before taking cohomology.
* `Stacks.Cohomology.ExtProjectionFormula.ExtProjectionInput` bundles the hypotheses on
  `E` and `𝒢` of [Stacks, Tag 0DJQ] with the two inputs of the source's proof that this
  library does not supply; each field says which it is.

## Main results

* `Stacks.Cohomology.ExtProjectionFormula.derivedTensorPushforwardIso` is the isomorphism in
  `D(𝒪_S)` underlying the tag: `K ⊗^L_{𝒪_S} ℱ ≅ Rf_*(E ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ))`, natural
  in `ℱ`.
* `Stacks.Cohomology.ExtProjectionFormula.extCohomologyIso` is **[Stacks, Tag 0A1F]**, the
  isomorphism on `i`-th cohomology, as a natural isomorphism in `ℱ`.

## Implementation notes

**The quasi-coherence hypothesis is dropped.**  The source states the tag for `ℱ`
quasi-coherent, because that is what its appeal to [Stacks, Tag 08EU] needs.  Since that appeal
is carried as a hypothesis, nothing below uses quasi-coherence and `ℱ` ranges over all
`𝒪_S`-modules; the statement is therefore more general than the source's in that respect.

**Boundary maps.**  The compatibility with boundary maps is *not* delivered.  It asks that for a
short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` the isomorphisms commute with the two connecting
maps: on the left the one of the distinguished triangle obtained by applying `K ⊗^L_{𝒪_S} -` to
the triangle of the sequence, on the right the one of the triangle of the short exact sequence
of complexes `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`, which is exact because the `𝒢^n`
are flat over `S`.  Naturality in `ℱ` gives the two squares of the triangle morphism built from
the maps of the sequence, but not the third: in a triangulated category a square on the first
two legs of two distinguished triangles always admits *some* fill-in, and that the fill-in is
the isomorphism below is exactly the verification the source omits.  The clause string of the
tag records this.

## References

* [Stacks Project, Tag 0A1F](https://stacks.math.columbia.edu/tag/0A1F)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedProjectionFormula (projectionFormulaMap)
open Stacks.Cohomology.DerivedSectionsLeray
  (derivedSectionsOverOpen derivedPreimageSections derivedSectionsPushforwardIso)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct derivedTensorProductFunctor)

namespace Stacks.Cohomology.ExtProjectionFormula

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### The ordinary tensor product of a complex with a module -/

/-- **The complex `𝒢 ⊗_{𝒪_X} M`**, with terms `𝒢^p ⊗_{𝒪_X} M` and differentials `d ⊗ 1`, as a
functor of the `𝒪_X`-module `M`.  On objects it is
`CochainComplex.KFlatBifunctor.rowComplex` of the tensor product of sheaves of modules.

It is written at `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules`, which is
`StrictlyPerfect.OXMod` by `rfl`, for the reason that declaration's docstring gives: the
instance arguments of the tensor product of sheaves of modules fix the sheaf of rings as
`Stacks.SheafOfModules.Tensor.ringSheaf`, and at the other spelling they are synthesized before
the two are unified. -/
def tensorModuleComplex (Z : Scheme.{u})
    (G : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace) ℤ) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace ⥤
      CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace) ℤ where
  obj M := CochainComplex.KFlatBifunctor.rowComplex
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.toRingedSpace.sheaf) G M
  map {_ _} φ :=
    { f := fun p =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.toRingedSpace.sheaf).obj
          (G.X p)).map φ
      comm' := fun p q _ =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.toRingedSpace.sheaf).map
          (G.d p q)).naturality φ }
  map_id M := HomologicalComplex.hom_f_injective (funext fun p =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.toRingedSpace.sheaf).obj
      (G.X p)).map_id M)
  map_comp φ ψ := HomologicalComplex.hom_f_injective (funext fun p =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.toRingedSpace.sheaf).obj
      (G.X p)).map_comp φ ψ)

/-! ### The two sides of the tag

Everything is written at the derived tensor product of [Stacks, Tag 06YU],
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, which is the one the
projection-formula map of [Stacks, Tag 0B53] is stated at. -/

variable (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)

/-- The object `E ⊗^L_{𝒪_X} 𝒢` of `D(𝒪_X)`. -/
abbrev derivedTensorG : DerivedCategory (OXMod.{u, u} X.toRingedSpace) :=
  ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E).obj (DerivedCategory.Q.obj G)

/-- The object `K = Rf_*(E ⊗^L_{𝒪_X} 𝒢)` of `D(𝒪_S)` of [Stacks, Tag 0DJQ]. -/
abbrev pushforwardK : DerivedCategory (OXMod.{u, u} S.toRingedSpace) :=
  (ProperSupportPerfection.derivedPushforwardOX f).obj (derivedTensorG E G)

/-- **The left-hand side of [Stacks, Tag 0A1F] before cohomology**: `ℱ ↦ K ⊗^L_{𝒪_S} ℱ`, with
`ℱ` placed in degree zero. -/
abbrev baseTensorFunctor :
    OXMod.{u, u} S.toRingedSpace ⥤ DerivedCategory (OXMod.{u, u} S.toRingedSpace) :=
  DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0 ⋙
    (derivedTensorProductFunctor S.toRingedSpace.sheaf).obj (pushforwardK f E G)

/-- **The right-hand side of [Stacks, Tag 0A1F] before cohomology**:
`ℱ ↦ E ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ)`, with `f^*` the ordinary pullback of [Stacks, Tag 0096]
and `𝒢 ⊗_{𝒪_X} f^*ℱ` the degreewise tensor product. -/
abbrev pullbackTensorFunctor :
    OXMod.{u, u} S.toRingedSpace ⥤ DerivedCategory (OXMod.{u, u} X.toRingedSpace) :=
  modulePullback f.toLRSHom.toShHom ⋙ tensorModuleComplex X G ⋙ DerivedCategory.Q ⋙
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E

/-- The functor `ℱ ↦ 𝒢 ⊗^L_{𝒪_X} Lf^*ℱ` on `𝒪_S`-modules, the source of the flat
identification of [Stacks, Tag 08DE]. -/
abbrev derivedPullbackTensorFunctor :
    OXMod.{u, u} S.toRingedSpace ⥤ DerivedCategory (OXMod.{u, u} X.toRingedSpace) :=
  DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0 ⋙
    derivedPullback f.toLRSHom.toShHom ⋙
    (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (DerivedCategory.Q.obj G)

/-! ### The hypotheses -/

/-- **The input of [Stacks, Tag 0A1F]**: the assumptions of [Stacks, Tag 0DJQ] on `E` and `𝒢`,
together with the two steps of the source's proof that this library does not supply.

The first two fields are the source's assumptions, in the shape
`Stacks.Cohomology.PerfectPushforward` states them. The last two are **carried, not derived**. -/
structure ExtProjectionInput [LocallyOfFiniteType f] where
  /-- `E` is a perfect object of `D(𝒪_X)`, as in [Stacks, Tag 0DJQ]. -/
  isPerfect : RingedSpace.IsPerfect (X := X.toRingedSpace) E
  /-- `𝒢` is a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with support proper
  over `S`, as in [Stacks, Tag 0DJQ]. -/
  flatProperSupport : PerfectPushforward.FlatProperSupportComplex f G
  /-- **[Stacks, Tag 08EU] at `ℱ`**: the projection-formula map of [Stacks, Tag 0B53] is
  invertible at the source complex `E ⊗^L_{𝒪_X} 𝒢` and the target complex `ℱ`.  Carried, not
  derived: the library proves that tag only at `ℱ = 𝒪_S`. -/
  projectionFormula : ∀ F : OXMod.{u, u} S.toRingedSpace,
    IsIso (projectionFormulaMap f.toLRSHom.toShHom (derivedTensorG E G)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0).obj F))
  /-- **[Stacks, Tag 08DE] together with flatness of the terms of `𝒢` over `S`**:
  `𝒢 ⊗^L_{𝒪_X} Lf^*ℱ ≅ 𝒢 ⊗_{𝒪_X} f^*ℱ` in `D(𝒪_X)`, naturally in `ℱ`.  Carried, not derived:
  the library has [Stacks, Tag 08DE] in `D(𝒪_X)`, but not the comparison of the derived tensor
  product over `f⁻¹𝒪_S` with the underived one for terms flat over `S`. -/
  mixedFlatTensor : derivedPullbackTensorFunctor f G ≅
    modulePullback f.toLRSHom.toShHom ⋙ tensorModuleComplex X G ⋙ DerivedCategory.Q

/-! ### The isomorphism in the derived category -/

variable [LocallyOfFiniteType f]

/-- **The projection formula as a natural isomorphism in `ℱ`**:
`K ⊗^L_{𝒪_S} ℱ ≅ Rf_*((E ⊗^L_{𝒪_X} 𝒢) ⊗^L_{𝒪_X} Lf^*ℱ)`.  Invertibility at each `ℱ` is the
`projectionFormula` field; naturality is
`Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right`. -/
def projectionFormulaNatIso (h : ExtProjectionInput f E G) :
    baseTensorFunctor f E G ≅
      DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0 ⋙
        derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (derivedTensorG E G) ⋙
        derivedPushforward f.toLRSHom.toShHom :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ _ (h.projectionFormula F))
    (fun φ => Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
      f.toLRSHom.toShHom (derivedTensorG E G)
      ((DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0).map φ))

/-- **Associativity as a natural isomorphism in `ℱ`**:
`(E ⊗^L_{𝒪_X} 𝒢) ⊗^L_{𝒪_X} Lf^*ℱ ≅ E ⊗^L_{𝒪_X} (𝒢 ⊗^L_{𝒪_X} Lf^*ℱ)`.  Nothing is carried:
the associator and its naturality in the third variable are
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator` and
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_right`. -/
def associatorNatIso :
    DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0 ⋙
        derivedPullback f.toLRSHom.toShHom ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj (derivedTensorG E G) ≅
      derivedPullbackTensorFunctor f G ⋙
        (derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E :=
  NatIso.ofComponents
    (fun F => Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator
      X.toRingedSpace.sheaf (canonicalDerivedTensorProduct X.toRingedSpace.sheaf) E
      (DerivedCategory.Q.obj G)
      ((derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0).obj F)))
    (fun φ => Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_right
      X.toRingedSpace.sheaf (canonicalDerivedTensorProduct X.toRingedSpace.sheaf) E
      (DerivedCategory.Q.obj G)
      ((derivedPullback f.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctor (OXMod.{u, u} S.toRingedSpace) 0).map φ)))

/-- **The isomorphism of [Stacks, Tag 0A1F] in the derived category**:
`K ⊗^L_{𝒪_S} ℱ ≅ Rf_*(E ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ))`, natural in the `𝒪_S`-module `ℱ`.  It is
the projection formula, then associativity, then the flat identification, each pushed forward
along `f` where needed. -/
def derivedTensorPushforwardIso (h : ExtProjectionInput f E G) :
    baseTensorFunctor f E G ≅
      pullbackTensorFunctor f E G ⋙ derivedPushforward f.toLRSHom.toShHom :=
  projectionFormulaNatIso f E G h ≪≫
    Functor.isoWhiskerRight (associatorNatIso f E G ≪≫
        Functor.isoWhiskerRight h.mixedFlatTensor
          ((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj E))
      (derivedPushforward f.toLRSHom.toShHom)

/-! ### Cohomology

Cohomology on `S` of an object of `D(𝒪_S)` is the `i`-th homology of its unbounded derived
global sections, and cohomology on `X` is read as a `Γ(S, 𝒪_S)`-module by restriction of
scalars along `f^♯`, which is the target in which [Stacks, Tag 0D5W] compares the two. -/

/-- `H^i(Z, -)` on `D(𝒪_Z)`, valued in `Γ(Z, 𝒪_Z)`-modules. -/
abbrev cohomologyOnBase (Z : Scheme.{u}) (i : ℤ) :
    DerivedCategory (OXMod.{u, u} Z.toRingedSpace) ⥤
      ModuleCat.{u} ((structureSheafRing Z.toRingedSpace).obj.obj (op ⊤)) :=
  derivedSectionsOverOpen Z.toRingedSpace ⊤ ⋙ DerivedCategory.homologyFunctor _ i

/-- `H^i(X, -)` on `D(𝒪_X)`, valued in `Γ(S, 𝒪_S)`-modules by restriction of scalars along
`f^♯`. -/
abbrev cohomologyOnSource (i : ℤ) :
    DerivedCategory (OXMod.{u, u} X.toRingedSpace) ⥤
      ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op ⊤)) :=
  derivedPreimageSections f.toLRSHom.toShHom ⊤ ⋙ DerivedCategory.homologyFunctor _ i

/-- In the situation of [Stacks, Tag 0DJQ] there are isomorphisms

`H^i(S, K ⊗^L_{𝒪_S} ℱ) ≅ H^i(X, E ⊗^L_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ))`,

functorial in the `𝒪_S`-module `ℱ` — the statement is a natural isomorphism of functors on
`𝒪_S`-modules, so functoriality is part of its type — and `Γ(S, 𝒪_S)`-linear.  Quasi-coherence
of `ℱ` is not assumed.

Two steps of the source's proof are carried, as the `projectionFormula` and `mixedFlatTensor`
fields of `h`: [Stacks, Tag 08EU] at `ℱ`, which this library proves only at `ℱ = 𝒪_S`, and the
identification `𝒢 ⊗^L_{𝒪_X} Lf^*ℱ ≅ 𝒢 ⊗_{𝒪_X} f^*ℱ`, which is [Stacks, Tag 08DE] together
with flatness of the `𝒢^n` over `S`.  The other two steps are proved: associativity of the
derived tensor product, and Leray in the unbounded form [Stacks, Tag 0D5W], which holds with no
hypothesis on `f` and which the bounded-below [Stacks, Tag 01EZ] that the source cites does not
cover here.

The compatibility with boundary maps is **not** part of this statement; see the module
docstring for what it asks and why naturality does not give it. -/
@[stacks 0A1F "the functorial isomorphisms for every i, as a natural isomorphism in ℱ ranging \
over all 𝒪_S-modules rather than only the quasi-coherent ones, and Γ(S, 𝒪_S)-linear; two steps \
of the source's proof are carried as explicit named hypotheses, the fields projectionFormula \
and mixedFlatTensor of ExtProjectionInput — invertibility of the projection-formula map of Tag \
0B53 at ℱ, which is Tag 08EU and which this library proves only at ℱ = 𝒪_S, and the \
identification of 𝒢 ⊗ᴸ Lf^*ℱ with 𝒢 ⊗ f^*ℱ, which is Tag 08DE together with flatness of \
the terms of 𝒢 over S; the remaining two steps, associativity of the derived \
tensor product and Leray, are proved, the latter in the unbounded form of Tag 0D5W; the \
compatibility with boundary maps is NOT carried"]
def extCohomologyIso (h : ExtProjectionInput f E G) (i : ℤ) :
    baseTensorFunctor f E G ⋙ cohomologyOnBase S i ≅
      pullbackTensorFunctor f E G ⋙ cohomologyOnSource f i :=
  Functor.isoWhiskerRight (derivedTensorPushforwardIso f E G h) (cohomologyOnBase S i) ≪≫
    Functor.isoWhiskerLeft (pullbackTensorFunctor f E G)
      (Functor.isoWhiskerRight (derivedSectionsPushforwardIso f.toLRSHom.toShHom ⊤)
        (DerivedCategory.homologyFunctor _ i))

end Stacks.Cohomology.ExtProjectionFormula

end
