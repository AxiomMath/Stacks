module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraStructureProof
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.TwistMultTransport.Structural

/-!
# Towards the repaired transport: the descent of a morphism, and the assembly of the algebra

`AlgebraicGeometry.AdicAlgebraStructureSystemTransport`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraStructureProof.lean`)
is the repaired step 5 of the reduction of the `halg` hypotheses of Stacks 09ZT, 0A42 and 0899 to
Grothendieck existence for modules: given a cartesian system `(B n)` of quasi-coherent algebra
sheaves on the adic thickenings and a coherent module with proper support whose completion is
isomorphic, **as a system**, to the system of the underlying modules of the `B n`, it asks for an
algebra sheaf on `X` realizing the system. This file carries the steps a proof of it needs that
do not depend on Grothendieck existence.

## What is proved here

The source's recipe is: transport the multiplications `ℳₙ ⊗ ℳₙ ⟶ ℳₙ` and the units
`𝒪_{Xₙ} ⟶ ℳₙ` of the `B n` across the Stacks 088F equivalence to a multiplication and a unit on
`𝒩`, check the three algebra laws, and assemble the algebra sheaf.

**The multiplicativity of a morphism of algebra sheaves**,
`Stacks.RelativeSpec.AlgebraSheaf.multiplication_comp_underlyingModuleMap`, is the input the
family of multiplications needs in order to be compatible with the transitions at all: a
morphism of the `B n` reads on underlying modules as a morphism intertwining the two
multiplications. Only the special case of it was available before, inside the proof of
`Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective`, where it is *derived from*
joint injectivity rather than from the morphism; the general statement is the one a transport of
multiplications along the transitions `hBtrans` has to use, and it is proved here directly from
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap_mulSection`.

**The transitions of the module system carry the algebra structure**, which is the step that used
to be non-derivable. The transitions of `AlgebraicGeometry.adicAlgebraModuleSystem` are
`(hpullback iₙ (B (n+1)))⁻¹ ≫ underlyingModuleMap (hBtrans n)`. The second factor is an
isomorphism of *algebra* sheaves, so it intertwines the multiplications and the units by the
statement above; the first factor is the identification `hpullback` of the module underlying an
algebra pullback with the module pullback, and
`AlgebraicGeometry.AlgebraPullbackModuleIso` now requires of it exactly that it be a morphism of
algebra sheaves underlying-module-wise. Composing the two,
`AlgebraicGeometry.AlgebraPullbackModuleIso.multiplication_comp_transition` and
`AlgebraicGeometry.AlgebraPullbackModuleIso.unitModuleMap_comp_transition` say that the
transition of the system intertwines the pullback of the multiplication (resp. of the unit) of
`B (n+1)`, compared by [Stacks, Tag 01CD], with the multiplication (resp. the unit) of `B n`;
`AlgebraicGeometry.multiplication_comp_adicAlgebraModuleSystem_transitionIso` and
`AlgebraicGeometry.unitModuleMap_comp_adicAlgebraModuleSystem_transitionIso` are the same two
statements read at the system itself.

**The descent**, `AlgebraicGeometry.existsUnique_hom_of_adicThickeningCompletion`, is the
Stacks 088F equivalence in the form the recipe consumes: a family of morphisms of the restrictions
to the thickenings, compatible with the canonical transitions of the two completions, comes from a
unique morphism on `X`. It is stated for arbitrary objects of
`Stacks.Algebraization.CoherentModulesProperOver f`, so it applies to the multiplication through
`AlgebraicGeometry.tensorSquareProperOver` and to the associativity through
`AlgebraicGeometry.tensorCubeProperOver` — the two objects
`AlgebraicGeometry.bijective_adicThickeningCompletionFunctor_map_tensorSquare` and
`AlgebraicGeometry.injective_adicThickeningCompletionFunctor_map_tensorCube` put in that category.
Against those two it is the hom-set bijection read as a descent statement: what the recipe needs
is not that the map on hom-sets is bijective but that a prescribed compatible family has a unique
preimage, and the compatibility it must be handed is a commuting square in
`AlgebraicGeometry.AdicCoherentModuleSystem`, not a morphism of systems already assembled.

**The assembly**, `AlgebraicGeometry.adicAlgebraStructureSystemTransport_of_moduleAlgebraData`,
closes the recipe at the other end: once the multiplication, the unit and the three laws are in
hand as a `Stacks.FundamentalGroup.ModuleAlgebraData` on the algebraization, and the algebra
sheaf it builds is known to restrict to the `B n`, the repaired binder follows. The module
isomorphism the conclusion also asks for is supplied here, by
`Stacks.FundamentalGroup.algebraSheafOfModuleIso`; no hypothesis about it is needed.

So the repaired binder rests on one named input, `hdata` below, and that input is about building
a multiplication and a unit on one module — no longer about algebra structures on a system.

## What remains between `hdata` and the library

The binder on `hpullback` that used to be missing is now present, so the compatibility of the
transported multiplications with the transitions is a theorem (above) rather than a gap. Two
things still stand between `hdata` and the library, and both are about *changing the picture*,
not about algebra.

1. **The monoidal comparison against the transitions of the two completions.** The components of
   the multiplication family are
   `cₙ⁻¹ ≫ (eₙ ⊗ eₙ) ≫ multiplication (B n) ≫ eₙ⁻¹`, where `cₙ` is the comparison of
   [Stacks, Tag 01CD] at the projection `vₙ : Xₙ ⟶ X`
   (`Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso`, unconditional) and `eₙ` is the `n`-th
   component of the given isomorphism of systems. Its compatibility with the canonical
   transitions `AlgebraicGeometry.adicThickeningCompletionTransition` — the hypothesis `hm` of
   `AlgebraicGeometry.existsUnique_hom_of_adicThickeningCompletion` at
   `AlgebraicGeometry.tensorSquareProperOver` — reduces, by the two theorems of this file and the
   `comm` field of the isomorphism of systems, to the compatibility of the comparison `cₙ` with
   the two isomorphisms `AlgebraicGeometry.adicThickeningCompletionNatIso` is built from,
   `AlgebraicGeometry.Scheme.Modules.pullbackComp` and `pullbackCongr`. That is a coherence
   property of Tag 01CD alone, with no algebra in it, and the first half of it is proved:
   `Stacks.PullbackCompMonoidal.comparison_tensor` is exactly the compatibility of the comparison
   of Tag 01CD with the contraction of an iterated pullback. What is missing is that statement
   read at the scheme-level spellings `AlgebraicGeometry.Scheme.Modules.pullback` and
   `Stacks.SheafOfModules.Tensor.sheafTensor` used here — it is stated for
   `Stacks.RingedSpace.pullbackFunctor` and the monoidal `⊗` of Tag 01CA, which are the same
   functor and the same object but not the same spellings — together with the corresponding
   statement for `pullbackCongr`, which is naturality of the comparison in the *morphism* rather
   than in the module and is not in the library at all.

2. **The unit, and only the change of picture.** Moving a morphism out of `𝒪_X` is
   `Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete`
   (`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/SheafHomQuotient.lean`), and
   it is **unconditional**: the degree-zero theorem on formal functions for a coherent sheaf of
   proper support — Stacks 087U, i.e. Stacks 02OC in degree zero — is a theorem over a Noetherian
   `I`-adically complete base,
   `Stacks.Algebraization.isIso_globalSectionsToLimit_of_hasProperSupport`, so no 087U binder is
   carried. The general-`I` form at
   `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AsymmetricFormalFunctions.lean`
   still has its `hFF`; the `_complete` forms are the ones to use, and
   `AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport`, the one consumer of
   the repaired binder, has the `[IsAdicComplete I A]` they need.

   What is left on the unit side is therefore only the change of picture. Those statements are
   about `Stacks.Algebraization.completionFunctor X ℐ`, whose objects are inverse systems of
   quotients of `𝒪_X`-modules, while the systems of
   `AlgebraicGeometry.adicThickeningCompletionFunctor` are modules on the thickenings; the bridge
   is `AlgebraicGeometry.adicThickeningCompletionPushforwardIso`, with its normalization and its
   naturality, and the recovery direction
   `AlgebraicGeometry.adicThickeningCompletion_iso_of_pushforward_iso`. Those are object-level;
   the identification of the two hom-sets out of `𝒪_X`, which is what carries a compatible family
   of units `𝒪_{Xₙ} ⟶ ℳₙ` from one picture to the other, is not in the library.

A third thing is a change of spelling rather than a gap:
`Stacks.FundamentalGroup.ModuleAlgebraData` asks for its multiplication as a morphism
`E.val ⊗ E.val ⟶ E.val` of *presheaves* of modules, while the descent of this file produces a
morphism out of `Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of that; the
sheafification unit mediates, and the three laws of the structure are stated on local sections,
where `Stacks.RelativeSpec.AlgebraSheaf.multiplication_tmul` computes.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.multiplication_comp_underlyingModuleMap` — a morphism of
  algebra sheaves intertwines the multiplications of the tensor squares of the underlying
  modules.
* `AlgebraicGeometry.AlgebraPullbackModuleIso.multiplication_comp_transition` and
  `AlgebraicGeometry.AlgebraPullbackModuleIso.unitModuleMap_comp_transition` — **the transition
  of the module system underlying a cartesian system of algebra sheaves intertwines the pullback
  of the multiplication, and of the unit, with the multiplication and the unit downstairs.** This
  is what the strengthened `hpullback` buys, and it is what no form of the old binder gave.
* `AlgebraicGeometry.multiplication_comp_adicAlgebraModuleSystem_transitionIso` and
  `AlgebraicGeometry.unitModuleMap_comp_adicAlgebraModuleSystem_transitionIso` — the same two
  statements read at `AlgebraicGeometry.adicAlgebraModuleSystem` itself.
* `AlgebraicGeometry.existsUnique_hom_of_adicThickeningCompletion` — granted the Stacks 088F
  equivalence, a family of morphisms of the restrictions to the adic thickenings compatible with
  the transitions descends to a unique morphism on `X`.
* `AlgebraicGeometry.adicAlgebraStructureSystemTransport_of_moduleAlgebraData` — the repaired
  binder `AlgebraicGeometry.AdicAlgebraStructureSystemTransport` follows from the construction of
  a `Stacks.FundamentalGroup.ModuleAlgebraData` on the algebraization whose algebra sheaf
  restricts to the given system.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

/-! ### A morphism of algebra sheaves intertwines the multiplications -/

namespace Stacks.RelativeSpec.AlgebraSheaf

/-- **A morphism of algebra sheaves intertwines the multiplications.** For `ψ : A ⟶ B` a morphism
of sheaves of commutative `𝒪_X`-algebras, the square

  `A ⊗ A ⟶ A`,  `A ⊗ A ⟶ B ⊗ B ⟶ B`

built from `Stacks.RelativeSpec.AlgebraSheaf.multiplication` and the tensor square of the
underlying morphism of modules commutes. On pure tensors of local sections this is
multiplicativity of `ψ` on sections,
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap_mulSection`, and two morphisms out of a
tensor product agreeing on pure tensors are equal.

This is the input the transport of the multiplications of a cartesian system of algebra sheaves
along its transition isomorphisms runs on: the transitions are isomorphisms of *algebra* sheaves,
and what the descent of the multiplication needs of them is exactly this square. Only the special
case of it was available, inside the proof of
`Stacks.RelativeSpec.AlgebraSheaf.exists_hom_of_jointlyInjective`, where it is derived from joint
injectivity instead. -/
public theorem multiplication_comp_underlyingModuleMap {X : Scheme.{u}} {A B : AlgebraSheaf X}
    (ψ : A ⟶ B) :
    multiplication A ≫ underlyingModuleMap ψ =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.presheaf, X.IsSheaf⟩)).map
          ((underlyingModuleMap ψ, underlyingModuleMap ψ) : (_, _) ⟶ (_, _))) ≫
        multiplication B := by
  refine hom_ext_toTensorSheafSection X.toRingedSpace _ _ fun U x y => ?_
  refine (multiplication_comp_tmul (underlyingModuleMap ψ) U x y).trans ?_
  refine Eq.trans ?_
    (tensorSheafMap_comp_tmul (underlyingModuleMap ψ) (multiplication B) U x y).symm
  exact (underlyingModuleMap_mulSection ψ U x y).trans (multiplication_tmul B U _ _).symm

end Stacks.RelativeSpec.AlgebraSheaf

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport)
open Stacks.RelativeSpec.AlgebraSheaf (multiplication unitModuleMap underlyingModuleMap
  underlyingModuleFunctor unitModuleMap_comp)

/-! ### The transitions of the module system carry the algebra structure -/

namespace AlgebraPullbackModuleIso

/-- Reading a multiplicativity square backwards along an isomorphism, as pure category algebra:
if the forward direction `fwd` of the identification carries `mul` to `tfwd ≫ cpm`, then its
backward direction carries `cpm` to `tbwd ≫ mul`.

Stated in an abstract category for the reason recorded at
`Stacks.AlgebraicGeometry.TwistMultTransport`: `CategoryTheory.Category.assoc` cannot be matched
by `rw` at `AlgebraicGeometry.Scheme.Modules`, whose category instance is a structure copy over a
`def`, and writing out the tensor square of the identification a second time — inside a
`congrArg` motive — exhausts the deterministic budget on its own. Here the tensor squares enter
only as the abstract morphisms `tfwd` and `tbwd`, so nothing is elaborated twice. -/
private theorem tensorInvChain {D : Type*} [Category D] {TA TB PA PB : D}
    {mul : TA ⟶ PA} {fwd : PA ⟶ PB} {bwd : PB ⟶ PA}
    {tfwd : TA ⟶ TB} {tbwd : TB ⟶ TA} {cpm : TB ⟶ PB}
    (h : mul ≫ fwd = tfwd ≫ cpm)
    (ht : tbwd ≫ tfwd = 𝟙 TB)
    (hi : fwd ≫ bwd = 𝟙 PA) :
    tbwd ≫ mul = cpm ≫ bwd := by
  calc tbwd ≫ mul
      = tbwd ≫ (mul ≫ fwd) ≫ bwd := by
        rw [Category.assoc mul fwd bwd, hi, Category.comp_id]
    _ = tbwd ≫ (tfwd ≫ cpm) ≫ bwd := by rw [h]
    _ = (tbwd ≫ tfwd) ≫ cpm ≫ bwd := by simp only [Category.assoc]
    _ = cpm ≫ bwd := by rw [ht, Category.id_comp]

/-- Composing a multiplicativity square with a second one along a factored transition, as pure
category algebra; the companion of `AlgebraicGeometry.AlgebraPullbackModuleIso.tensorInvChain`
for the second factor of the transition. Abstract for the same reason. -/
private theorem transitionChain {D : Type*} [Category D] {TA TB TC PA PB PF K : D}
    {ttau : TA ⟶ TC} {tbwd : TA ⟶ TB} {tpsi : TB ⟶ TC}
    {mul : TB ⟶ PB} {mulF : TC ⟶ PF} {u : PB ⟶ PF}
    {ci : TA ⟶ K} {pm : K ⟶ PA} {bwd : PA ⟶ PB}
    (hsplit : ttau = tbwd ≫ tpsi)
    (hmul : mul ≫ u = tpsi ≫ mulF)
    (hkey : tbwd ≫ mul = (ci ≫ pm) ≫ bwd) :
    ttau ≫ mulF = ci ≫ pm ≫ bwd ≫ u := by
  rw [hsplit, Category.assoc, ← hmul, ← Category.assoc, hkey]
  simp only [Category.assoc]

/-- **A bifunctor carries a pair of retractions to a retraction.** Read through
`CategoryTheory.Functor.uncurry`, which is the spelling in which
`AlgebraicGeometry.AlgebraPullbackModuleIso` asks for the tensor square of its identification,
this says that the tensor square of an isomorphism and the tensor square of its inverse compose
to the identity.

Stated for an arbitrary bifunctor rather than for
`Stacks.SheafOfModules.Tensor.sheafTensor` itself: the pair `(z, z)` cannot be elaborated inside
a `congrArg` motive at `AlgebraicGeometry.Scheme.Modules`, whose morphisms are a `def` over
those of `CategoryTheory.SheafOfModules` and whose coefficient ring sheaf is reached through
`Stacks.SheafOfModules.Tensor.ringSheaf`, also a `def`; the symptom is a `whnf`
timeout. Here the pair is elaborated once, against a known expected type. -/
private theorem uncurry_map_comp_id {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
    (F : C₁ ⥤ C₂ ⥤ D) {A A' : C₁} {B B' : C₂}
    {aFwd : A ⟶ A'} {aBwd : A' ⟶ A} {bFwd : B ⟶ B'} {bBwd : B' ⟶ B}
    (ha : aBwd ≫ aFwd = 𝟙 A') (hb : bBwd ≫ bFwd = 𝟙 B') :
    ((Functor.uncurry.obj F).map ((aBwd, bBwd) : (A', B') ⟶ (A, B))) ≫
        ((Functor.uncurry.obj F).map ((aFwd, bFwd) : (A, B) ⟶ (A', B'))) =
      𝟙 ((Functor.uncurry.obj F).obj (A', B')) := by
  rw [← Functor.map_comp]
  exact (congrArg ((Functor.uncurry.obj F).map (X := (A', B')) (Y := (A', B')))
      (Prod.ext ha hb)).trans ((Functor.uncurry.obj F).map_id (A', B'))

/-- **The transition of the underlying module system intertwines the multiplications.** Let
`g : T ⟶ S`, let `E` be an algebra sheaf on `S` with a strengthened identification `θ` of
`AlgebraicGeometry.AlgebraPullbackModuleIso g E`, and let `ψ : (algebraPullback g).obj E ≅ F`
be an isomorphism of algebra sheaves on `T` — the data of one transition of a cartesian system.
Then the composite `τ = θ.iso⁻¹ ≫ underlyingModuleMap ψ`, which is the transition of
`AlgebraicGeometry.adicAlgebraModuleSystem`, carries the pullback of the multiplication of `E`
— read through the comparison of [Stacks, Tag 01CD] — to the multiplication of `F`:

  `(τ ⊗ τ) ≫ mul F = c⁻¹ ≫ g^*(mul E) ≫ τ`.

**This is the statement whose non-derivability from the old hypothesis list was the defect.** The
second factor of `τ` contributes by
`Stacks.RelativeSpec.AlgebraSheaf.multiplication_comp_underlyingModuleMap`, which needs only that
`ψ` is a morphism of algebra sheaves. The first factor contributes by the field
`multiplication_comp_iso_hom`, and nothing else can supply it: an arbitrary isomorphism of
modules between the module underlying an algebra pullback and the module pullback relates the
multiplication of a pullback to nothing at all, so with the old binder the left-hand side was
unconstrained. The repair is therefore in the hypothesis, where the intended carrier — induced by
a map of sheaves of rings — already satisfies it. -/
public theorem multiplication_comp_transition {T S : Scheme.{u}} {g : T ⟶ S}
    {E : AlgebraSheaf S} (θ : AlgebraPullbackModuleIso g E) {F : AlgebraSheaf T}
    (ψ : (algebraPullback g).obj E ≅ F) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨T.presheaf, T.IsSheaf⟩)).map
          ((θ.iso.inv ≫ underlyingModuleMap ψ.hom, θ.iso.inv ≫ underlyingModuleMap ψ.hom) :
            (_, _) ⟶ (_, _))) ≫ multiplication F =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso g
          (AlgebraSheaf.underlyingModule E) (AlgebraSheaf.underlyingModule E)).inv ≫
        (Scheme.Modules.pullback g).map (multiplication E) ≫
          θ.iso.inv ≫ underlyingModuleMap ψ.hom :=
  transitionChain
    (Stacks.AlgebraicGeometry.TwistMultTransport.tensorSheafMap_comp T.toRingedSpace
      θ.iso.inv (underlyingModuleMap ψ.hom) θ.iso.inv (underlyingModuleMap ψ.hom))
    (Stacks.RelativeSpec.AlgebraSheaf.multiplication_comp_underlyingModuleMap ψ.hom)
    (tensorInvChain θ.multiplication_comp_iso_hom
      (uncurry_map_comp_id
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨T.presheaf, T.IsSheaf⟩)
        θ.iso.inv_hom_id θ.iso.inv_hom_id)
      θ.iso.hom_inv_id)

/-- **The transition of the underlying module system intertwines the structure morphisms.** The
companion of `AlgebraicGeometry.AlgebraPullbackModuleIso.multiplication_comp_transition` for the
unit: the pullback of the structure morphism `𝒪_S ⟶ E`, read through the identification
`Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso` of `g^* 𝒪_S` with `𝒪_T`, followed by
the transition, is the structure morphism `𝒪_T ⟶ F`.

The second factor of the transition contributes by
`Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap_comp`, the first by the field
`unitModuleMap_comp_iso_hom`. Together with the multiplication statement this is the whole of
"the transitions of the system are morphisms of algebra sheaves": what the descent of an algebra
structure has to know about them. -/
public theorem unitModuleMap_comp_transition {T S : Scheme.{u}} {g : T ⟶ S}
    {E : AlgebraSheaf S} (θ : AlgebraPullbackModuleIso g E) {F : AlgebraSheaf T}
    (ψ : (algebraPullback g).obj E ≅ F) :
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).inv ≫
          (Scheme.Modules.pullback g).map (unitModuleMap E) ≫
        θ.iso.inv ≫ underlyingModuleMap ψ.hom =
      unitModuleMap F := by
  have key : (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map (unitModuleMap E) ≫ θ.iso.inv =
      unitModuleMap ((algebraPullback g).obj E) := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫ θ.iso.inv)
      θ.unitModuleMap_comp_iso_hom.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun z => unitModuleMap ((algebraPullback g).obj E) ≫ z)
      θ.iso.hom_inv_id) ?_
    exact Category.comp_id _
  refine Eq.trans (congrArg
    (fun z => (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).inv ≫ z)
    (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ underlyingModuleMap ψ.hom) key) ?_
  exact unitModuleMap_comp ψ.hom

end AlgebraPullbackModuleIso

/-- **The transitions of `AlgebraicGeometry.adicAlgebraModuleSystem` intertwine the
multiplications.** This is
`AlgebraicGeometry.AlgebraPullbackModuleIso.multiplication_comp_transition` read at the system
itself: the transition `φₙ : iₙ^* ℳₙ₊₁ ≅ ℳₙ` of the system of Stacks 088F underlying a cartesian
system `(B n)` of quasi-coherent algebra sheaves carries the pullback of the multiplication of
`B (n + 1)`, compared by [Stacks, Tag 01CD], to the multiplication of `B n`.

This is the compatibility that a transport of the multiplications of the `B n` to a
multiplication on the algebraization has to check against the transitions, and it was not
derivable before `hpullback` was required to be multiplicative. -/
public theorem multiplication_comp_adicAlgebraModuleSystem_transitionIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
    (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
    (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
    (hBtrans : ∀ n, Nonempty
      ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
    (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
    (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
      (AlgebraSheaf.underlyingModule (B 0)))
    (n : ℕ) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(adicBaseChange A I f n).toRingedSpace.presheaf,
              (adicBaseChange A I f n).toRingedSpace.IsSheaf⟩)).map
          ((((adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh
                hM0).transitionIso n).hom,
              ((adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh
                hM0).transitionIso n).hom) : (_, _) ⟶ (_, _))) ≫
        multiplication (B n) =
      (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso (adicBaseChangeSucc A I f n)
          (AlgebraSheaf.underlyingModule (B (n + 1)))
          (AlgebraSheaf.underlyingModule (B (n + 1)))).inv ≫
        (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map
            (multiplication (B (n + 1))) ≫
          ((adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh
            hM0).transitionIso n).hom :=
  AlgebraPullbackModuleIso.multiplication_comp_transition
    (hpullback (adicBaseChangeSucc A I f n) (B (n + 1)) (hqc (n + 1))) (hBtrans n).some

/-- **The transitions of `AlgebraicGeometry.adicAlgebraModuleSystem` intertwine the structure
morphisms.** `AlgebraicGeometry.AlgebraPullbackModuleIso.unitModuleMap_comp_transition` read at
the system itself: the pullback of the structure morphism of `B (n + 1)`, read through
`Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso`, followed by the transition of the
system, is the structure morphism of `B n`. -/
public theorem unitModuleMap_comp_adicAlgebraModuleSystem_transitionIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
      AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
    (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
    (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
    (hBtrans : ∀ n, Nonempty
      ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
    (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
    (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
      (AlgebraSheaf.underlyingModule (B 0)))
    (n : ℕ) :
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso
            (adicBaseChangeSucc A I f n)).inv ≫
          (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map
            (unitModuleMap (B (n + 1))) ≫
        ((adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0).transitionIso n).hom =
      unitModuleMap (B n) :=
  AlgebraPullbackModuleIso.unitModuleMap_comp_transition
    (hpullback (adicBaseChangeSucc A I f n) (B (n + 1)) (hqc (n + 1))) (hBtrans n).some

/-! ### The Stacks 088F equivalence as a descent statement -/

/-- **Granted Grothendieck existence, a compatible family of morphisms on the adic thickenings
descends uniquely.** Let `P` and `Q` be coherent `𝒪_X`-modules with support proper over the base
and suppose given, for every `n`, a morphism `mₙ : P|_{Xₙ} ⟶ Q|_{Xₙ}` commuting with the canonical
transitions `AlgebraicGeometry.adicThickeningCompletionTransition` of the two completions. Then
there is exactly one `μ : P ⟶ Q` with `μ|_{Xₙ} = mₙ` for every `n`.

This is the form in which the Stacks 088F equivalence is used to build the structure maps of an
algebra: full faithfulness read as existence and uniqueness of a preimage of a prescribed
compatible family, rather than as bijectivity of a map of hom-sets. The compatibility is the
`comm` field of `AlgebraicGeometry.AdicCoherentModuleSystem.Hom` at the two completions, which is
why it is stated as a commuting square and not as a morphism of systems: a consumer building the
family out of the multiplications of a system of algebra sheaves has the square to check, not the
morphism to hand over.

Both of the objects the descent of an algebra structure is applied to are in the category this is
stated for: the tensor square and the tensor cube of a coherent module with proper support, by
`AlgebraicGeometry.tensorSquareProperOver` and `AlgebraicGeometry.tensorCubeProperOver`. -/
public theorem existsUnique_hom_of_adicThickeningCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (P Q : Stacks.Algebraization.CoherentModulesProperOver f)
    (m : ∀ n : ℕ, adicThickeningCompletion A I f P.obj.obj n ⟶
      adicThickeningCompletion A I f Q.obj.obj n)
    (hm : ∀ n : ℕ,
      (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (m (n + 1)) ≫
          (adicThickeningCompletionTransition A I f Q.obj.obj n).hom =
        (adicThickeningCompletionTransition A I f P.obj.obj n).hom ≫ m n) :
    ∃! μ : P.obj.obj ⟶ Q.obj.obj,
      ∀ n : ℕ,
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ = m n := by
  have := h088F
  let α : (adicThickeningCompletionFunctor A I f).obj P ⟶
      (adicThickeningCompletionFunctor A I f).obj Q := { app := m, comm := hm }
  obtain ⟨φ, hφ⟩ := Functor.map_surjective (adicThickeningCompletionFunctor A I f) α
  refine ⟨φ.hom.hom, fun n => congrArg (fun t => t.app n) hφ, fun μ hμ => ?_⟩
  have hmap : (adicThickeningCompletionFunctor A I f).map
      (⟨⟨μ⟩⟩ : P ⟶ Q) = (adicThickeningCompletionFunctor A I f).map φ :=
    (AdicCoherentModuleSystem.Hom.ext (funext hμ)).trans hφ.symm
  exact congrArg (fun t : P ⟶ Q => t.hom.hom)
    (Functor.map_injective (adicThickeningCompletionFunctor A I f) hmap)

/-! ### The assembly of the algebra sheaf -/

/-- **The repaired transport follows from the construction of a module algebra structure on the
algebraization.** `AlgebraicGeometry.AdicAlgebraStructureSystemTransport A I f` asks for an
algebra sheaf `C` on `X` whose underlying module is the algebraization `P` and whose restriction
to every adic thickening is `B n`. Granted `hdata` — a multiplication, a unit and the three
algebra laws on `P`, as a `Stacks.FundamentalGroup.ModuleAlgebraData`, whose algebra sheaf
restricts to the given system — the transport holds: `C` is
`Stacks.FundamentalGroup.algebraSheafOfModule`, and the identification of its underlying module
with `P` is
`Stacks.FundamentalGroup.algebraSheafOfModuleIso`, which needs no hypothesis.

So the whole of the repaired binder is reduced to constructing the multiplication and the unit:
the step from them to a sheaf of commutative rings — which is what makes this step of Stacks 09ZT
not module theory — is discharged. The multiplication is descended by
`AlgebraicGeometry.existsUnique_hom_of_adicThickeningCompletion` at
`AlgebraicGeometry.tensorSquareProperOver`, and its laws are decided on the thickenings by the
same statement at `AlgebraicGeometry.tensorCubeProperOver`; the compatibility of the descended
family with the transitions of the module system is
`AlgebraicGeometry.multiplication_comp_adicAlgebraModuleSystem_transitionIso` above, and see the
module docstring for the two changes of picture that remain.

Neither coherence nor proper support of the algebraization is weakened: both are components of
the `Stacks.Algebraization.CoherentModulesProperOver f` that `hdata` and the transport are stated
over, and the counterexamples in the module docstring of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraAlgebraization.lean` show the
statement is false without them. -/
public theorem adicAlgebraStructureSystemTransport_of_moduleAlgebraData
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (hdata : ∀ (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
        AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
      (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
      (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
      (hBtrans : ∀ n, Nonempty
        ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
      (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
      (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
        (AlgebraSheaf.underlyingModule (B 0)))
      (P : Stacks.Algebraization.CoherentModulesProperOver f),
      ((adicThickeningCompletionFunctor A I f).obj P ≅
          adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0) →
        ∃ d : Stacks.FundamentalGroup.ModuleAlgebraData P.obj.obj, ∀ n, Nonempty
          ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj
            (Stacks.FundamentalGroup.algebraSheafOfModule P.obj.obj d) ≅ B n)) :
    AdicAlgebraStructureSystemTransport A I f := by
  intro _h088F hpullback B hqc hBtrans hMcoh hM0 P e
  obtain ⟨d, hd⟩ := hdata hpullback B hqc hBtrans hMcoh hM0 P e
  exact ⟨Stacks.FundamentalGroup.algebraSheafOfModule P.obj.obj d,
    ⟨Stacks.FundamentalGroup.algebraSheafOfModuleIso P.obj.obj d⟩, hd⟩

end AlgebraicGeometry

end
