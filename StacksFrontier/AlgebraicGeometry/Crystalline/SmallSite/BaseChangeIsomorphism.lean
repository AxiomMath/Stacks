module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedTensorBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Modules.GlobalSectionsOverGamma
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat modules on `Cris(X/S)`, the general pullback, and the statement of [Stacks, Tag 07MU]

[Stacks, Tag 07MU] asserts that the base change map (07MT) of [Stacks, Tag 07MS],

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`,

is an isomorphism provided **seven** conditions hold.  This file supplies a rendering of the
flatness of `F'` as an `𝒪_{X'/S'}`-module, which is condition (5), and a pullback of a sheaf of
modules along change of divided power base for an arbitrary morphism `g : X ⟶ X'` and not only
for an open immersion, and then writes the statement down, with all seven conditions.

## Condition (5): flatness of `F'` as an `𝒪_{X'/S'}`-module

This condition needs a tensor product of sheaves of modules over a general site, and nothing new
needs to be invented for it: the library already carries the source's own definition, as

`Stacks.SheafOfModules.IsFlat`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactness.lean`, [Stacks, Tag 03ER]
part (3)),

namely **exactness of the endofunctor `G ↦ G ⊗_𝒪 F` of sheaves of `𝒪`-modules**, where the tensor
product `G ⊗_𝒪 F` is the sheafification of the objectwise tensor product of presheaves of modules
(`Stacks.sheafTensorRight`).  Exactness there is `CategoryTheory.exactFunctor`, i.e. preservation
of finite limits *and* of finite colimits, which is the condition the source states, and not the
weaker preservation of monomorphisms that right exactness makes equivalent to it.
`AlgebraicGeometry.SheafOfModules.IsFlat` (`StacksFrontier/CategoryTheory/Sites/Modules/Flat.lean`)
is the same definition under a second spelling of the underlying sheaf of rings.

Two things make it applicable here.

* The ring universe and the module universe of `Stacks.sheafTensorRight` are **independent**: its
  objectwise tensor product of presheaves of modules is built by hand in
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactness.lean` rather than taken from
  Mathlib's monoidal structure on `PresheafOfModules`, precisely because the monoidal instance
  pins the module universe to the ring universe.  So `𝒪_{X/S}` may stay at `RingCat.{u}` while
  the modules sit at the universe `u + 1` that this chapter's cohomology uses.
* Commutativity of `𝒪_{X/S}` is available as
  `Crystalline.GlobalCrystallineSituation.SmallSite.commStructureSheaf`, the `CommRingCat`-valued
  twin of the structure sheaf; `commRingSheafToRingSheaf_commStructureSheaf` below says that
  forgetting commutativity returns the structure sheaf used everywhere else *on the nose*.

Objectwise flatness is **not** used: it is a strictly stronger condition in general (it implies
the source's, by [Stacks, Tag 03ES] and [Stacks, Tag 03ET], and is not implied by it), so taking
it as the definition would have made the statement below weaker than [Stacks, Tag 07MU].

The one universe choice that remains is which category of modules is tensored against.  The
crystal and quasi-coherence predicates of this chapter are stated for
`SheafOfModules.{u} (structureSheaf S)`, while the sheaf tensor product needs sheafification of
`AddCommGrpCat`-valued presheaves on `Cris(X/S)`, which exists only from `u + 1` upwards (see
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleCohomology.lean`).  So
flatness is read on the universe lift `moduleULift`, exactly as cohomology is: `IsFlatModule`
below is `IsFlatModuleSheaf` of `(moduleULift S).obj F`.  This is the chapter's standard passage
and is the same category of coefficients that `RΓ(Cris(X/S), -)` is taken in; no comparison
between flatness at the two module universes is claimed or proved.

## The pullback of a module, for an arbitrary `g : X ⟶ X'`

`Crystalline.GlobalCrystallineSituation.SmallSite.smallChangeBaseModulePullback` needs
`[IsOpenImmersion g]`, which [Stacks, Tag 07MU](4) — `X = X' ×_{S'₀} S₀` — does not provide.  The
reason is structural and is not removable by weakening a hypothesis: that pullback is restriction
along `Crystalline.GlobalCrystallineSituation.smallChangeBase`, a functor
`Cris(X/S) ⥤ Cris(X'/S')`, and an object `(U, T, δ)` of `Cris(X/S)` has `U ⟶ X` an open immersion
while `U ⟶ X ⟶ X'` need not be one.  The source does not use such a functor either: its
`f_cris` is `π_{X'} ∘ f_CRIS ∘ i_X` through the **big** crystalline site
([Stacks, Tag 07IK]), which is `Crystalline.GlobalCrystallineSituation.crisMorphism`, and
`Crystalline.GlobalCrystallineSituation.changeBase` — the big-site change of base — is
continuous and cocontinuous with no hypothesis on `g` at all.

So the general construction is added alongside the open-immersion one, as restriction along the
composite `Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`, which exists for every `g`:

`crisModulePullback : SheafOfModules.{v} (crystallineStructureSheaf S') ⥤
  SheafOfModules.{v} (structureSheaf S)`.

`crisModulePullback_obj_eq_smallChangeBaseModulePullback` says that where the open-immersion
construction applies the two agree, so this is a generalisation and not a second notion.

## Main results

* `commRingSheafToRingSheaf_commStructureSheaf` — forgetting commutativity carries the
  `CommRingCat`-valued structure sheaf of `Cris(X/S)` to `structureSheaf S` on the nose, which is
  what makes the library's flatness predicate applicable to this chapter's modules;
* `isFlatModuleSheaf_iff` — flatness unfolded into the two half-exactness statements;
* `crisModulePullback` is a functor in the generality of [Stacks, Tag 07MJ] (arbitrary `g`), with
  its sections computed by `crisModulePullback_obj_val_obj`, and it agrees with
  `smallChangeBaseModulePullback` on the nose wherever the latter is defined
  (`crisModulePullback_obj_eq_smallChangeBaseModulePullback`);
* `crisRestrictModules` — the restriction of modules from `CRIS(X/S)` to `Cris(X/S)` as a
  functor;
* `isBaseChangeIso07MU_iff_degreewise` — **[Stacks, Tag 07MU] is equivalent to its degreewise
  form** `DegreewiseBaseChangeIso07MU`, the same seven conditions with "`φ` is an isomorphism"
  replaced by "`φ` is an isomorphism on the cohomology of `D(A)` in every degree".  Nothing is
  assumed: the two directions are
  `isBaseChangeIso07MU_of_degreewiseBaseChangeIso07MU` and
  `degreewiseBaseChangeIso07MU_of_isBaseChangeIso07MU`, both running through
  `isIso_iff_forall_isIso_homologyMap_baseChangeMap07MT`, which is
  `CategoryTheory.DerivedCategory.isIso_iff` at the two objects of [Stacks, Tag 07MS].  So all
  of the tag's content is degreewise, and the degreewise statement is the one the source's
  argument produces;
* `baseChangeCohomologyIso` — the graded form of the conclusion, an isomorphism of `A`-modules
  `H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ≅ H^j(Cris(X/S), F)` for every `j : ℕ`, the target being
  the chapter's own `moduleULiftCohomology` that [Stacks, Tag 07MR] and [Stacks, Tag 07MX] are
  stated about;
* `isZero_homologyFunctor_obj_derivedBaseChangeTensorGlobalSections_of_neg` — a *necessary*
  condition the tag carries with it: an isomorphism (07MT) forces
  `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` to have no cohomology in negative degrees, because the target
  has none (`isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg`, the
  negative-degree vanishing of a right derived functor).  That vanishing is what conditions (4),
  (5) and (7) of the remark have to buy.

## The source's proof

The proof of [Stacks, Tag 07MU] is the reduction given in the source's Hints, in four steps.
Mayer–Vietoris [Stacks, Tag 07ML] reduces to `X'` affine, and condition (6) supplies a
Koszul-regular presentation `C' = A'/I'[x_1, …, x_n]/(f̄'_1, …, f̄'_c)`; the divided power envelope
`D' = A'[x_1, …, x_n]⟨ξ_1, …, ξ_c⟩/(ξ_i - f'_i)` is computed by [Stacks, Tag 07HC], and
conditions (4) and (7) give `D' ⊗^L_{A'} A = D`; the equivalence [Stacks, Tag 07JH] of crystals
in quasi-coherent modules with modules with connection turns `F'` into a pair `(M', ∇)`,
condition (5) giving `M = M' ⊗^L_{A'} A`; and the de Rham computation [Stacks, Tag 07LG]
concludes.

The reduction needs [Stacks, Tag 07JH] and [Stacks, Tag 07LG] compatible with change of divided
power base.  The degree-`j` clause of `DegreewiseBaseChangeIso07MU` is about the given base change
map, so the de Rham side needs a form of [Stacks, Tag 07LG] that names its comparison map: the
existence of an isomorphism between two groups in each degree says nothing about whether a given
map between them is one.  The de Rham computation identifies the abelian-valued cohomology
`(cohomologyFunctor S j).obj (abelianSheaf F)`, whereas `RΓ(Cris(X/S), F)` has the `A`-modules
`moduleULiftCohomology` as its cohomology objects (`homologyModuleULiftDerivedGlobalSectionsIso`);
crossing between the two is [Stacks, Tag 03FD].

## Implementation notes

The base change map (07MT) is constructed for `g : X ⟶ X'` an open immersion, as
`Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeMap07MT` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapConstruction.lean`; but
condition (4) makes the `g` of [Stacks, Tag 07MU] a base change `X = X' ×_{S'₀} S₀`, which is not
an open immersion (see the "Generality" section of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMap.lean`).  So
`IsBaseChangeIso07MU` is a *predicate on a map*: it says of a given
`BaseChangeMap07MT f F' F` that the seven conditions force it to be an isomorphism.
[Stacks, Tag 07MU] is exactly this predicate applied to the canonical map (07MT), and nothing
here asserts it of any other map — in particular `IsBaseChangeIso07MU` is deliberately *not*
quantified over all `φ`, which would be a different and false assertion, and it does not
assert instead that source and target are merely isomorphic, which would be strictly weaker
than the tag.  Each of the seven conditions is named in the docstring of `IsBaseChangeIso07MU`
against the clause it renders.

`crisModulePullback` takes its coefficients on the big site `CRIS(X'/S')`.  The pullback from the
small site `Cris(X'/S')` in the generality of [Stacks, Tag 07MJ] goes through the module-level
`i_!` of [Stacks, Tag 07IJ], the left adjoint of `crisRestrictModules`, which is
`...SmallSite.moduleLowerShriek` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LowerShriekModules.lean`, with
`...SmallSite.crisModuleInverseImage` the composite.  `F` is carried as a parameter of
`IsBaseChangeIso07MU`, as it is in `BaseChangeMap07MT`; `IsBaseChangeIso07MUOfCrisModule` is the
variant with it computed, for coefficients given on the big site.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07HC](https://stacks.math.columbia.edu/tag/07HC)
* [Stacks Project, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe v u wS wS' wA wA'

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Flatness of a sheaf of `𝒪_{X/S}`-modules -/

section Flat

/-- **Forgetting commutativity preserves the sheaf condition on `Cris(X/S)`**, for sections at
any universe.  This is `Stacks.hasSheafCompose_forget₂_commRingCat`, which holds on every site
with no size hypothesis, specialised to the small crystalline topology; it is what lets the
`CommRingCat`-valued `commStructureSheaf` be used as the ring sheaf of a ringed site.

It is a theorem rather than an instance for the reason given in the file
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforwardModules/`
`HasSheafComposeForget.lean`: registering a second globally applicable witness of this class
puts two distinct terms of it in scope wherever a structure already carries its own. -/
theorem hasSheafCompose_forget₂_smallTopology (S : GlobalCrystallineSituation.{u}) :
    (smallTopology S).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  Stacks.hasSheafCompose_forget₂_commRingCat _

attribute [local instance] hasSheafCompose_forget₂_smallTopology

variable (S : GlobalCrystallineSituation.{u})

/-- **The sheaf of rings underlying `commStructureSheaf S` is `structureSheaf S` on the nose.**

`commStructureSheaf S` is the structure sheaf of `Cris(X/S)` read in `CommRingCat.{u}` and
`structureSheaf S` the same sheaf read in `RingCat.{u}`; composing the first with
`forget₂ CommRingCat RingCat` returns the second definitionally, because
`Crystalline.GlobalCrystallineSituation.SmallSite.crisRing` *is*
`structurePresheaf S ⋙ forget₂ CommRingCat RingCat` up to the associativity of functor
composition.

This is what makes the library's flatness predicate for sheaves of modules on a ringed site —
which is stated over a sheaf of *commutative* rings — a predicate about the very modules this
chapter uses, with no transport. -/
theorem commRingSheafToRingSheaf_commStructureSheaf :
    Stacks.commRingSheafToRingSheaf (commStructureSheaf S) = structureSheaf S := rfl

/-- **Flatness of a sheaf of `𝒪_{X/S}`-modules**, condition (5) of [Stacks, Tag 07MU]: the
endofunctor `G ↦ G ⊗_{𝒪_{X/S}} F` of sheaves of `𝒪_{X/S}`-modules is exact.

This is the library's `Stacks.SheafOfModules.IsFlat`, which is [Stacks, Tag 03ER] part (3) — the
source's own definition of a flat module over a sheaf of rings on a site — for the ringed site
`(Cris(X/S), 𝒪_{X/S})`, with `𝒪_{X/S}` supplied as the `CommRingCat`-valued
`commStructureSheaf S`.  Unwinding it: the tensor product is the sheafification of the objectwise
tensor product of the underlying presheaves of modules, and exactness is
`CategoryTheory.exactFunctor`, the conjunction of preservation of finite limits and of finite
colimits.  See `isFlatModuleSheaf_iff`.

The modules are at the universe `u + 1` of `ModuleSheaf`, which is where sheafification of
`AddCommGrpCat`-valued presheaves on `Cris(X/S)` is available and where this chapter's
cohomology is taken; the rings stay at `u`.  Nothing weaker, and nothing stronger, is asked
than the source asks: in particular objectwise flatness of the sections is not used, being
strictly stronger. -/
@[sga "4½ Etat_0 6.2" "special case"]
def IsFlatModuleSheaf (F : ModuleSheaf S) : Prop :=
  Stacks.SheafOfModules.IsFlat (O := commStructureSheaf S) F

/-- **The endofunctor `G ↦ G ⊗_{𝒪_{X/S}} F` of sheaves of `𝒪_{X/S}`-modules**, whose exactness
is `IsFlatModuleSheaf`.  It is `Stacks.sheafTensorRight` of the `CommRingCat`-valued structure
sheaf: the objectwise tensor product of the underlying presheaves of modules, sheafified.

Its declared result type pins the spelling of the ring sheaf to `structureSheaf S`, which
`commRingSheafToRingSheaf_commStructureSheaf` says is the same sheaf of rings; without that the
category of modules comes back in the other spelling and instance search fails to connect the
two. -/
def moduleSheafTensorRight (F : ModuleSheaf S) : ModuleSheaf S ⥤ ModuleSheaf S :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u + 1, u + 1}
    (commStructureSheaf S)).flip.obj F)

/-- **Flatness unfolded**: a sheaf of `𝒪_{X/S}`-modules is flat exactly when tensoring with it
preserves finite limits and finite colimits.  Both halves are asked for, as the source asks; the
right exact half is automatic for a tensor functor but is not proved in this library, so it is
not silently dropped. -/
theorem isFlatModuleSheaf_iff (F : ModuleSheaf S) :
    IsFlatModuleSheaf S F ↔
      PreservesFiniteLimits (moduleSheafTensorRight S F) ∧
        PreservesFiniteColimits (moduleSheafTensorRight S F) :=
  Iff.rfl

/-- Tensoring with a flat sheaf of `𝒪_{X/S}`-modules preserves finite limits. -/
theorem IsFlatModuleSheaf.preservesFiniteLimits {F : ModuleSheaf S} (hF : IsFlatModuleSheaf S F) :
    PreservesFiniteLimits (moduleSheafTensorRight S F) :=
  hF.1

/-- Tensoring with a flat sheaf of `𝒪_{X/S}`-modules preserves finite colimits. -/
theorem IsFlatModuleSheaf.preservesFiniteColimits {F : ModuleSheaf S}
    (hF : IsFlatModuleSheaf S F) :
    PreservesFiniteColimits (moduleSheafTensorRight S F) :=
  hF.2

/-- **Flatness of a sheaf of `𝒪_{X/S}`-modules at the universe of this chapter's crystal and
quasi-coherence predicates**, which is the form condition (5) of [Stacks, Tag 07MU] is used in:
flatness of the universe lift `moduleULift`.

`Crystalline.GlobalCrystallineSituation.IsSheafCrystal` and
`SheafOfModules.IsQuasicoherentOnSite` are stated for
`SheafOfModules.{u} (structureSheaf S)`, while the sheaf tensor product needs the modules one
universe up; `moduleULift` is the passage between them that this chapter already uses for
cohomology, so `RΓ(Cris(X/S), F)` and the flatness of `F` are read on the same object. -/
def IsFlatModule (F : SheafOfModules.{u} (structureSheaf S)) : Prop :=
  IsFlatModuleSheaf S ((moduleULift S).obj F)

end Flat

/-! ### The pullback of a module along an arbitrary change of base -/

section Pullback

variable {S S' : GlobalCrystallineSituation.{u}}

/-- **The comparison of structure sheaves for the inclusion `Cris(X/S) ⥤ CRIS(X/S)`.**  It is the
identity: the structure sheaf of either crystalline site sends an object to the global sections of
its ambient divided power scheme, and the inclusion leaves the object untouched. -/
def crisInclusionStructureHom (S : GlobalCrystallineSituation.{u}) :
    structureSheaf S ⟶
      ((CrystallineThickening.ι S).sheafPushforwardContinuous RingCat.{u}
        (smallTopology S) (topology S)).obj (crystallineStructureSheaf S) :=
  ⟨𝟙 _⟩

/-- **The restriction of a sheaf of modules from `CRIS(X/S)` to `Cris(X/S)`, as a functor.**

`Crystalline.GlobalCrystallineSituation.SmallSite.restrictSheafOfModules` performs this on
objects; the functor is what a composite such as `crisModulePullback` needs.  It is the direct
image of sheaves of modules along the continuous inclusion
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.ι`, whose comparison of structure
sheaves is the identity `crisInclusionStructureHom`. -/
def crisRestrictModules (S : GlobalCrystallineSituation.{u}) :
    SheafOfModules.{v} (crystallineStructureSheaf S) ⥤
      SheafOfModules.{v} (structureSheaf S) :=
  SheafOfModules.pushforward.{v} (crisInclusionStructureHom S)

/-- The sections of the restriction of a module from `CRIS(X/S)` to `Cris(X/S)` over an object of
the small site are its sections over the underlying object of the big site. -/
theorem crisRestrictModules_obj_val_obj (S : GlobalCrystallineSituation.{u})
    (N : SheafOfModules.{v} (crystallineStructureSheaf S))
    (A : (CrystallineThickening S)ᵒᵖ) :
    (((crisRestrictModules.{v} S).obj N).val.obj A : Type v) =
      (N.val.obj (op ((CrystallineThickening.ι S).obj A.unop)) : Type v) :=
  rfl

/-- **`Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')` is continuous**, for *every* `g : X ⟶ X'`: the
inclusion of the small crystalline site into the big one is continuous ([Stacks, Tag 07IJ]) and
so is change of divided power base on the big sites ([Stacks, Tag 07IC]), neither with any
hypothesis on `g`.  This is what makes the general pullback below exist. -/
instance isContinuous_ι_comp_changeBase (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (CrystallineThickening.ι S ⋙ changeBase S S' f g h).IsContinuous
      (smallTopology S) (topology S') :=
  Functor.isContinuous_comp (CrystallineThickening.ι S) (changeBase S S' f g h)
    (smallTopology S) (topology S) (topology S')

/-- **The comparison of structure sheaves for `Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`**, the
composite along which a module on the big crystalline site of `X'/S'` is pulled back to the small
crystalline site of `X/S` for an *arbitrary* `g : X ⟶ X'`.

It is the identity, for the two reasons the two legs are: change of divided power base replaces
the structure morphism `T ⟶ S` of an object by `T ⟶ S ⟶ S'` and leaves `T` itself alone, and the
inclusion of the small site into the big one leaves an object alone outright; so both legs carry
`(U, T, δ)` to an object with the same ambient scheme `T`, and the structure sheaf of each site is
`Γ(T, 𝒪_T)`. -/
def crisChangeBaseStructureHom (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    structureSheaf S ⟶
      (((CrystallineThickening.ι S ⋙ changeBase S S' f g h)).sheafPushforwardContinuous
        RingCat.{u} (smallTopology S) (topology S')).obj (crystallineStructureSheaf S') :=
  ⟨𝟙 _⟩

/-- **The pullback of a sheaf of modules along change of divided power base, in the generality of
[Stacks, Tag 07MJ]**: no hypothesis whatever on `g : X ⟶ X'`, in particular not that it is an
open immersion, so this covers the hypothesis `X = X' ×_{S'₀} S₀` of [Stacks, Tag 07MU](4).

Its coefficients are taken on the **big** crystalline site `CRIS(X'/S')`, which is what buys the
generality: the source's `f_cris` of [Stacks, Tag 07IK] is `π_{X'} ∘ f_CRIS ∘ i_X`, and the two
legs `i_X` and `f_CRIS` are exactly the composite
`Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')` restricted along here.  The remaining leg `π_{X'}` is the
module-level `i_!` of [Stacks, Tag 07IJ], and it is built in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LowerShriekModules.lean` as
`...SmallSite.moduleLowerShriek`; the composite with this pullback is
`...SmallSite.crisModuleInverseImage`, the module-valued `f_cris^{-1}` for an arbitrary `g`.

Where `Crystalline.GlobalCrystallineSituation.SmallSite.smallChangeBaseModulePullback` applies —
that is, for `g` an open immersion, the generality of [Stacks, Tag 07KL] — the two constructions
agree, by `crisModulePullback_obj_eq_smallChangeBaseModulePullback`. -/
def crisModulePullback (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    SheafOfModules.{v} (crystallineStructureSheaf S') ⥤
      SheafOfModules.{v} (structureSheaf S) :=
  SheafOfModules.pushforward.{v} (crisChangeBaseStructureHom f g h)

/-- **The sections of the general pullback.**  Over an object `(U, T, δ)` of `Cris(X/S)` they are
the sections of the given module on `CRIS(X'/S')` over the image of `(U, T, δ)` under change of
divided power base — the same ambient scheme `T`, with `U ⟶ X ⟶ X'` and `T ⟶ S ⟶ S'` as its
structure maps.  So the construction is pinned down pointwise and is not vacuous. -/
theorem crisModulePullback_obj_val_obj (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (N : SheafOfModules.{v} (crystallineStructureSheaf S'))
    (A : (CrystallineThickening S)ᵒᵖ) :
    (((crisModulePullback.{v} f g h).obj N).val.obj A : Type v) =
      (N.val.obj (op ((changeBase S S' f g h).obj A.unop.obj)) : Type v) :=
  rfl

/-- **The general pullback extends the open-immersion one.**  For `g` an open immersion the
pullback of a module on `CRIS(X'/S')` constructed here is
`Crystalline.GlobalCrystallineSituation.SmallSite.smallChangeBaseModulePullback` applied to the
restriction of that module to `Cris(X'/S')`.

The two are literally the same restriction: `smallChangeBase` is cut out of `changeBase` by
`ObjectProperty.lift`, so `smallChangeBase ⋙ ι` and `ι ⋙ changeBase` are the same functor
`Cris(X/S) ⥤ CRIS(X'/S')`.  This is what makes `crisModulePullback` a generalisation rather than
a second notion of pullback. -/
theorem crisModulePullback_obj_eq_smallChangeBaseModulePullback (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] (N : SheafOfModules.{v} (crystallineStructureSheaf S')) :
    (crisModulePullback.{v} f g h).obj N =
      (SheafOfModules.pushforward.{v} (smallChangeBaseStructureHom S S' f g h)).obj
        ((crisRestrictModules.{v} S').obj N) :=
  rfl

end Pullback

/-! ### The statement of [Stacks, Tag 07MU] -/

section BaseChange

variable {S S' : GlobalCrystallineSituation.{u}} [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The statement of [Stacks, Tag 07MU], as a predicate on the base change map.**

Given a morphism `f : S ⟶ S'` of divided power bases, a compatible `g : X ⟶ X'`, a sheaf `F'` of
`𝒪_{X'/S'}`-modules, a sheaf `F` of `𝒪_{X/S}`-modules and a map

`φ : RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`

of `D(A)` — that is, a `Crystalline.GlobalCrystallineSituation.SmallSite.BaseChangeMap07MT` — this
is the assertion that `φ` is an isomorphism as soon as all seven conditions of the remark hold.
Clause by clause, with `A' = Γ(S', 𝒪_{S'})` and `A = Γ(S, 𝒪_S)`:

1. `p` is nilpotent in `A'`: `IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤))`.
2. `F'` is a crystal in quasi-coherent `𝒪_{X'/S'}`-modules:
   `SheafOfModules.IsQuasicoherentOnSite` together with
   `Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal`, which is
   [Stacks, Tag 07IS] part (3) read on `Cris(X'/S')` — the small-site predicate, this being
   where `F'` lives.
3. `X' ⟶ S'₀` is quasi-compact and quasi-separated: `AlgebraicGeometry.QuasiCompact` and
   `AlgebraicGeometry.QuasiSeparated` of `S'.toClosedFiber`.
4. `X = X' ×_{S'₀} S₀`: `CategoryTheory.IsPullback` of the square with sides `g`,
   `S.toClosedFiber`, `S'.toClosedFiber` and
   `Crystalline.DividedPowerScheme.closedFiberMap f`.  Being a pullback square carries the
   commutativity with it, so the compatibility `h` of `f` and `g` is *not* taken as a separate
   hypothesis here; a redundant conjunct would make this strictly weaker than the tag.
5. `F'` is a flat `𝒪_{X'/S'}`-module: `IsFlatModule`, which is
   `Stacks.SheafOfModules.IsFlat` ([Stacks, Tag 03ER] part (3)) of the universe lift of `F'` —
   exactness of `- ⊗_{𝒪_{X'/S'}} F'`, the source's own definition.  See the module docstring.
6. `X' ⟶ S'₀` is a local complete intersection morphism:
   `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism` ([Stacks, Tag 069F] part (2)).
7. `X'` and `S₀` are Tor independent over `S'₀`: `AlgebraicGeometry.TorIndependent`
   ([Stacks, Tag 08IA]) of `S'.toClosedFiber` and `closedFiberMap f`.

**This is a predicate, not a claim.**  It is not quantified over `φ`: the content of
[Stacks, Tag 07MU] is this predicate applied to the *canonical* base change map (07MT), which is
constructed for `g` an open immersion, as `...SmallSite.baseChangeMap07MT` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapConstruction.lean`, while
condition (4) above makes the `g` of the tag a base change (see the module docstring and the
"Generality" section of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMap.lean`).  Asserting it
for every `φ` of this type would be a strictly different and false statement, and asserting
instead that source and target are merely isomorphic would be strictly weaker than the tag; so
the map is carried, as it is in `BaseChangeMap07MT` itself. -/
def IsBaseChangeIso07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) : Prop :=
  IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)) →
    F'.IsQuasicoherentOnSite → IsSheafCrystal F' →
      QuasiCompact S'.toClosedFiber → QuasiSeparated S'.toClosedFiber →
        IsPullback g S.toClosedFiber S'.toClosedFiber
            (DividedPowerScheme.closedFiberMap f) →
          IsFlatModule S' F' →
            AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber →
              AlgebraicGeometry.TorIndependent S'.toClosedFiber
                  (DividedPowerScheme.closedFiberMap f) →
                IsIso φ

/-! #### What the tag amounts to degreewise -/

/-- **A map of `D(A)` of the type of the base change map (07MT) is an isomorphism exactly when it
is one on cohomology in every degree.**  This is `CategoryTheory.DerivedCategory.isIso_iff` at the
two objects of [Stacks, Tag 07MS]; no hypothesis of [Stacks, Tag 07MU] is used, and the degrees
run over all of `ℤ` because the source `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` is not known to be
bounded below — the derived tensor product is only right t-exact
(`isLE_derivedBaseChangeTensor_obj`), so no finite range of degrees suffices here.

This is what makes `DegreewiseBaseChangeIso07MU` below an equivalent form of the tag rather than a
weaker one. -/
theorem isIso_iff_forall_isIso_homologyMap_baseChangeMap07MT (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) :
    IsIso φ ↔ ∀ n : ℤ,
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).map φ) :=
  DerivedCategory.isIso_iff _ φ

/-- **The degreewise form of [Stacks, Tag 07MU]**: under the seven conditions of the remark, the
base change map (07MT) induces an isomorphism of `A`-modules on the cohomology of `D(A)` in every
degree.

The hypothesis block is that of `IsBaseChangeIso07MU`, condition for condition and in the same
order, and only the conclusion differs; `isBaseChangeIso07MU_iff_degreewise` is the machine check
that the two blocks really do agree, so this is not a second and silently different set of
conditions.  See the docstring of `IsBaseChangeIso07MU` for what each condition renders.

This is the form in which the source's argument delivers the tag: the de Rham computation
[Stacks, Tag 07LG] identifies
cohomology one degree at a time, and it does so for the *abelian*-valued cohomology of the sheaf
underlying `F`, so reaching the `A`-modules `moduleULiftCohomology` that `RΓ` has as its
cohomology objects needs [Stacks, Tag 03FD] on top of it. -/
def DegreewiseBaseChangeIso07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) : Prop :=
  IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)) →
    F'.IsQuasicoherentOnSite → IsSheafCrystal F' →
      QuasiCompact S'.toClosedFiber → QuasiSeparated S'.toClosedFiber →
        IsPullback g S.toClosedFiber S'.toClosedFiber
            (DividedPowerScheme.closedFiberMap f) →
          IsFlatModule S' F' →
            AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber →
              AlgebraicGeometry.TorIndependent S'.toClosedFiber
                  (DividedPowerScheme.closedFiberMap f) →
                ∀ n : ℤ,
                  IsIso ((DerivedCategory.homologyFunctor
                    (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).map φ)

/-- **[Stacks, Tag 07MU] follows from its degreewise form, and from nothing else.**  The seven
conditions are passed through unchanged and the conclusion is read off degree by degree with
`isIso_iff_forall_isIso_homologyMap_baseChangeMap07MT`. -/
theorem isBaseChangeIso07MU_of_degreewiseBaseChangeIso07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) (h : DegreewiseBaseChangeIso07MU f g F' F φ) :
    IsBaseChangeIso07MU f g F' F φ := fun hp hqc hcr hqcpt hqsep hpb hflat hlci htor =>
  (isIso_iff_forall_isIso_homologyMap_baseChangeMap07MT f φ).2
    (h hp hqc hcr hqcpt hqsep hpb hflat hlci htor)

/-- The converse: [Stacks, Tag 07MU] gives its degreewise form. -/
theorem degreewiseBaseChangeIso07MU_of_isBaseChangeIso07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) (h : IsBaseChangeIso07MU f g F' F φ) :
    DegreewiseBaseChangeIso07MU f g F' F φ := fun hp hqc hcr hqcpt hqsep hpb hflat hlci htor =>
  (isIso_iff_forall_isIso_homologyMap_baseChangeMap07MT f φ).1
    (h hp hqc hcr hqcpt hqsep hpb hflat hlci htor)

/-- **[Stacks, Tag 07MU] and its degreewise form are the same statement.**  Nothing is lost or
gained by asking for the isomorphism one degree at a time, so the whole content of the tag is
degreewise, and the hypothesis blocks of `IsBaseChangeIso07MU` and
`DegreewiseBaseChangeIso07MU` are checked here to agree. -/
theorem isBaseChangeIso07MU_iff_degreewise (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) :
    IsBaseChangeIso07MU f g F' F φ ↔ DegreewiseBaseChangeIso07MU f g F' F φ :=
  ⟨degreewiseBaseChangeIso07MU_of_isBaseChangeIso07MU f g F' F φ,
    isBaseChangeIso07MU_of_degreewiseBaseChangeIso07MU f g F' F φ⟩

/-- **The graded form of the conclusion of [Stacks, Tag 07MU]**: an isomorphism of `A`-modules

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ≅ H^j(Cris(X/S), F)`

for every `j : ℕ`, from a base change map (07MT) that is an isomorphism in `D(A)`.  The target is
the chapter's own cohomology module `moduleULiftCohomology`, which is what [Stacks, Tag 07MR] and
[Stacks, Tag 07MX] are stated about; the identification of it with the cohomology of `RΓ` is
`homologyModuleULiftDerivedGlobalSectionsIso`.

Only `IsIso φ` is asked for, not the seven conditions: this is the shape in which the conclusion
of the tag is consumed, and keeping the conditions out of it is what lets a caller supply them
once. -/
def baseChangeCohomologyIso (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) [IsIso φ] (j : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
        (derivedBaseChangeTensorGlobalSections f F') ≅
      moduleULiftCohomology S F j :=
  asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).map φ) ≪≫
    homologyModuleULiftDerivedGlobalSectionsIso S F j

/-- **`RΓ(Cris(X/S), F)` has no cohomology in negative degrees.**  It is the right derived
functor of `baseModuleGlobalSections` applied to a module placed in degree zero, and the right
derived functors of an additive functor vanish below degree zero
(`CategoryTheory.Functor.isZero_rightDerivedPlus_of_neg`).  Read in the unbounded derived
category, which is where the base change map (07MT) lives. -/
theorem isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg
    (F : SheafOfModules.{u} (structureSheaf S)) (n : ℤ) (hn : n < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).obj
      (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections S F))) :=
  (baseModuleGlobalSections S).isZero_rightDerivedPlus_of_neg ((moduleULift S).obj F) n hn

/-- **What [Stacks, Tag 07MU] forces on the derived tensor product**: if a base change map (07MT)
is an isomorphism then `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no cohomology in negative degrees.

So the tag carries a vanishing assertion with it, about the negative terms the derived tensor
product contributes — the target has none, by
`isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg`, and an isomorphism transports
that.  This is a necessary condition for the tag and not a step towards it: it is what conditions
(4), (5) and (7) of the remark have to buy. -/
theorem isZero_homologyFunctor_obj_derivedBaseChangeTensorGlobalSections_of_neg
    (f : S.S ⟶ S'.S) {F' : SheafOfModules.{u} (structureSheaf S')}
    {F : SheafOfModules.{u} (structureSheaf S)} (φ : BaseChangeMap07MT f F' F) [IsIso φ]
    (n : ℤ) (hn : n < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).obj
      (derivedBaseChangeTensorGlobalSections f F')) :=
  IsZero.of_iso (isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg F n hn)
    (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).map φ))

/-- **The statement of [Stacks, Tag 07MU] with `F` computed rather than carried**, for
coefficients given on the big crystalline site `CRIS(X'/S')`.

Here `F'` is the restriction of `N` to `Cris(X'/S')` and `F` is its pullback
`crisModulePullback` — the general pullback of this file, available for *every* `g : X ⟶ X'` and
so in particular under condition (4) — so the only datum left free is the base change map
itself. -/
def IsBaseChangeIso07MUOfCrisModule (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (φ : BaseChangeMap07MT f ((crisRestrictModules.{u} S').obj N)
      ((crisModulePullback.{u} f g h).obj N)) : Prop :=
  IsBaseChangeIso07MU f g ((crisRestrictModules.{u} S').obj N)
    ((crisModulePullback.{u} f g h).obj N) φ

end BaseChange

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
