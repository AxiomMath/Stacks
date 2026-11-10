module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningCoherentSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningUnwinding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.SheafHomQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.TwistMultTransport.Structural
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two changes of picture behind the transport of an algebra structure

The module docstring of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraStructureSystemProof`
leaves two things between its named input `hdata` and the library, and records that neither
contains any algebra: the compatibility of [Stacks, Tag 01CD] with the transitions of
`AlgebraicGeometry.adicThickeningCompletionNatIso`, and the identification of the hom-sets out of
`𝒪_X` between the two pictures of a completion. This file settles both.

## The first: Tag 01CD against the completion's transitions

### Both halves are already in the library

The `pullbackCongr` half — naturality of the Tag 01CD comparison in the *morphism* rather than in
the module — and the `pullbackComp` half, which is proved at the
`Stacks.RingedSpace.pullbackFunctor` and monoidal-`⊗` spellings by
`Stacks.PullbackCompMonoidal.comparison_tensor`, are both proved at the
`AlgebraicGeometry.Scheme.Modules.pullback` and
`Stacks.SheafOfModules.Tensor.sheafTensor` spellings this development uses, in
`StacksFrontier/AlgebraicGeometry/TwistMultTransport/Structural.lean`:
`Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp_hom` and
`comparison_pullbackCongr_hom`, together with `comparison_pullbackId` for the third structural
factor. They are proved there for the transport of Tag 01MY's multiplication identity along Tag
01NO's six-factor comparison; the `pullbackCongr` half is two lines, by `subst`, after which
`pullbackCongr` is `CategoryTheory.eqToIso` of a reflexivity proof and every component is the
identity.

So nothing of Tag 01CD is reproved here. What this file does is name the two halves at the
spellings of the adic files, paste them, and identify the completion's transition with the
composite they are pasted along.

* `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_pullbackComp_hom` and
  `schemePullbackTensorIso_pullbackCongr_hom` — the two halves, renamed at the spellings
  `AlgebraicGeometry.AlgebraPullbackModuleIso` and `AlgebraicGeometry.adicAlgebraModuleSystem` are
  stated in. Each is the existing statement itself: the comparisons and the tensor product objects
  of the two spellings are identified by `rfl`.
* `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_pullbackCompCongr` — **the first change of
  picture.** For `i ≫ v = w`, the two-factor identification of `i ^* (v ^* M)` with `w ^* M`
  carries the two-stage splitting of a tensor product to the one-stage splitting along `w`: the
  two halves pasted along the comparison for `i ≫ v`, which is the edge they share.
* `AlgebraicGeometry.adicThickeningCompletionTransition_hom`, and the same equation in the other
  direction as `pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition` — **the
  canonical transition of a completion is exactly that two-factor identification**, at
  `AlgebraicGeometry.adicBaseChangeSucc_fst`. So the coherence above, applied at `i = iₙ`,
  `v = vₙ₊₁`, `w = vₙ`, *is* the compatibility of Tag 01CD with
  `AlgebraicGeometry.adicThickeningCompletionTransition` — the hypothesis `hm` of
  `AlgebraicGeometry.existsUnique_hom_of_adicThickeningCompletion` read at
  `AlgebraicGeometry.tensorSquareProperOver`.

### Why the adic instance is not written out

The coherence is stated once, for an arbitrary `i ≫ v = w`, and a consumer applies it at the adic
morphisms. Writing the resulting statement out — with
`AlgebraicGeometry.adicThickeningCompletionTransition` in place of the composite, or
`AlgebraicGeometry.adicThickeningCompletion A I f P (n + 1)` in place of `vₙ₊₁ ^* P` — does not
compile. Four routes to it all die the same way:

* the statement proved in one step from the generic coherence: `isDefEq` timeout;
* the three substitutions split off into their own declarations: `isDefEq` timeout in the first;
* the transition ascribed to the generic type, which *does* typecheck
  (`adicThickeningCompletionTransition_hom` is exactly that ascription), and then carried through
  `congrArg₂` into the arguments of
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`: `whnf` timeout;
* the same with the implicit module arguments of `tensorSheafMap` given explicitly: `isDefEq`
  timeout.

The common factor is the ringed space `(AlgebraicGeometry.adicBaseChange A I f n).toRingedSpace`
in `tensorSheafMap`'s first argument. `tensorSheafMap` is defined through sheafification, its
module arguments are typed over `structureSheafRing _` while `Scheme.Modules` is typed over
`ringCatSheaf`, and reconciling those two over a *variable* scheme is cheap — the generic
coherence does it — while over `adicBaseChange A I f n`, which is a fibre product, it is not.
Abstracting the scheme is what stating the coherence generically does, so the generic statement is
the one to use and the adic one is the one not to write.
`AlgebraicGeometry.adicThickeningCompletionNatIso_eq` and
`adicThickeningCompletionTransition_hom_eq` are both `rfl` and are named for the same reason: they
are the two steps whose unification, left implicit, is what overruns.

## The second: the hom-sets of the two pictures

`Stacks.Algebraization.completionFunctor X ℐ` sends a coherent module to the inverse system of its
quotients by the powers of `ℐ`, which live on `X`; and
`AlgebraicGeometry.adicThickeningCompletionFunctor`
sends it to the system of its restrictions to the adic thickenings, which live on the `Xₙ`. The
object-level bridge `AlgebraicGeometry.adicThickeningCompletionPushforwardIso` is available, with
its normalization and its naturality; the identification of the hom-sets is what carries a
compatible family of units from one picture to the other.

* `AlgebraicGeometry.adicThickeningCompletionHomEquiv` — **the identification, degreewise.** Two
  inputs: the object-level bridge, and [Stacks, Tag 08KS] in the form
  `Stacks.ClosedImmersion.fullyFaithfulPushforward`, the direct image along the closed immersion
  `Xₙ ⟶ X` being fully faithful. It identifies the hom-sets for *every* pair of coherent modules,
  not only out of `𝒪_X`.
* `AlgebraicGeometry.adicThickeningCompletionHomEquiv_completionFunctor_map` — **the
  identification takes the completion of a morphism to its restriction**, which is what makes it
  the right bijection rather than some bijection. It is the naturality of the object-level
  bridge with that bridge cancelled on the left.
* `AlgebraicGeometry.adicThickeningCompletionUnitHomEquiv` and
  `adicThickeningCompletionUnitHomEquiv_completionFunctor_map` — the same out of the structure
  sheaf, composed with `Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso`, so that the
  target is `𝒪_{Xₙ} ⟶ G|_{Xₙ}` — the type of
  `Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap (B n)`.
* `AlgebraicGeometry.exists_unit_of_adicThickeningFamily` — **the unit descends.** A family
  `u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` realized, under that identification, by a morphism of the first
  picture's systems comes from a morphism `𝒪_X ⟶ G` on `X`. Unconditional:
  `Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete` carries
  no hypothesis on the theorem on formal functions over a Noetherian `I`-adically complete base,
  which is what the one consumer of the repaired binder has.

### What is left on the unit side

Exactly the binder `α` of `exists_unit_of_adicThickeningFamily`: the family `u` has to be
assembled into a morphism of the *first* picture's systems, whose compatibility condition is with
the quotient projections of `Stacks.Algebraization.completionFunctor` rather than with
`AlgebraicGeometry.adicThickeningCompletionTransition`. The degreewise half of that assembly is
`adicThickeningCompletionUnitHomEquiv`; translating the compatibility is what
`AlgebraicGeometry.adicThickeningCompletionPushforwardIso_projection` is for, and it is not done
here. It is a statement about one morphism of systems, with no algebra in it.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 0A42](https://stacks.math.columbia.edu/tag/0A42)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.TwistMultTransport (tensorSheafMap_comp)

universe u

namespace Stacks.Tag01VSPullbackTensor

/-! ### Pasting -/

/-- Two commuting squares sharing an edge paste. Stated generically, at the level of variables:
neither `rw` nor `simp` can match `CategoryTheory.Category.assoc` at the concrete instances below,
the category instance on sheaves of modules on a scheme being reached through a `def`. -/
private theorem paste {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    {x : O₁ ⟶ O₂} {k₁ : O₂ ⟶ O₃} {k₂ : O₃ ⟶ O₄} {a : O₁ ⟶ O₅} {m : O₅ ⟶ O₃}
    {b : O₅ ⟶ O₆} {n : O₆ ⟶ O₄}
    (h₁ : x ≫ k₁ = a ≫ m) (h₂ : m ≫ k₂ = b ≫ n) :
    x ≫ k₁ ≫ k₂ = (a ≫ b) ≫ n := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

/-! ### Tag 01CD against the two pseudofunctoriality isomorphisms -/

/-- **The comparison of [Stacks, Tag 01CD] against the composition law of the inverse image**, at
the `AlgebraicGeometry.Scheme.Modules.pullback` and
`Stacks.SheafOfModules.Tensor.sheafTensor` spellings: contracting an iterated
inverse image of a tensor product and then splitting it is splitting it in two stages and then
contracting each factor.

This is `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp_hom`, whose
comparison is written as a component of `Stacks.PullbackTensorIso.pullbackTensorIso` and whose
tensor product object is written as a value of the bifunctor `Stacks.RingedSpace.tensorSheaf`.
Those are the same morphism and the same object as the spellings here — the identification is by
`rfl` in each case — and the spellings here are the ones
`AlgebraicGeometry.AlgebraPullbackModuleIso` and `AlgebraicGeometry.adicAlgebraModuleSystem` are
stated in. -/
public theorem schemePullbackTensorIso_pullbackComp_hom {W W' W'' : Scheme.{u}} (i : W ⟶ W')
    (v : W' ⟶ W'') (P Q : W''.Modules) :
    ((Scheme.Modules.pullback i).map (schemePullbackTensorIso v P Q).hom ≫
          (schemePullbackTensorIso i ((Scheme.Modules.pullback v).obj P)
            ((Scheme.Modules.pullback v).obj Q)).hom) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj P),
              (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj Q)))
            (Y := ((Scheme.Modules.pullback (i ≫ v)).obj P,
              (Scheme.Modules.pullback (i ≫ v)).obj Q))
            (((Scheme.Modules.pullbackComp i v).hom.app P,
              (Scheme.Modules.pullbackComp i v).hom.app Q) : (_, _) ⟶ (_, _))) =
      (Scheme.Modules.pullbackComp i v).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj P).obj Q) ≫
        (schemePullbackTensorIso (i ≫ v) P Q).hom :=
  Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp_hom i v P Q

/-- **The comparison of [Stacks, Tag 01CD] against the congruence isomorphism of the inverse
image** — naturality of the comparison in the *morphism* rather than in the module: the comparison
along `i` and the comparison along an equal `w`, compared by
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, agree.

This is `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackCongr_hom` read at the
spellings used here. It is proved there by `subst`, after which `pullbackCongr` is
`CategoryTheory.eqToIso` of a reflexivity proof and every component is the identity, together with
the `pullbackComp` half above — both for the transport of Tag 01MY's multiplication identity along
Tag 01NO's six-factor comparison, which is five structural factors away from anything adic.
Nothing is reproved here. -/
public theorem schemePullbackTensorIso_pullbackCongr_hom {W W' : Scheme.{u}} {i w : W ⟶ W'}
    (hw : i = w) (P Q : W'.Modules) :
    (schemePullbackTensorIso i P Q).hom ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj P, (Scheme.Modules.pullback i).obj Q))
            (Y := ((Scheme.Modules.pullback w).obj P, (Scheme.Modules.pullback w).obj Q))
            (((Scheme.Modules.pullbackCongr hw).hom.app P,
              (Scheme.Modules.pullbackCongr hw).hom.app Q) : (_, _) ⟶ (_, _))) =
      (Scheme.Modules.pullbackCongr hw).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩).obj P).obj Q) ≫
        (schemePullbackTensorIso w P Q).hom :=
  Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackCongr_hom hw P Q

/-- **The comparison of [Stacks, Tag 01CD] against pseudofunctoriality with the composite named by
an equation.** For `i ≫ v = w` the two-factor identification of `i ^* (v ^* M)` with `w ^* M` —
the composition law followed by the congruence isomorphism, which is
`Stacks.Tag01VSPullbackTensor.pullbackCompCongrIso` written on components — carries the two-stage
splitting of a tensor product to the one-stage splitting along `w`.

This is the whole of the first change of picture: the two halves above pasted along the comparison
for `i ≫ v`, which is the edge they share, with the functoriality of the tensor product sheaf used
once to split the tensor of the two composites. No algebra enters, and no hypothesis beyond the
equation.

Stated on components rather than at `pullbackCompCongrIso` itself: that isomorphism is typed with
`i ^* (v ^* M)` where the composition law is typed with `(v ⋙ i) ^* M`, and converting an `Iso`
between sheaves of modules on a scheme across that spelling of its index exhausts the
deterministic budget, as an `isDefEq` timeout. -/
public theorem schemePullbackTensorIso_pullbackCompCongr {W W' W'' : Scheme.{u}} (i : W ⟶ W')
    (v : W' ⟶ W'') {w : W ⟶ W''} (hw : i ≫ v = w) (P Q : W''.Modules) :
    ((Scheme.Modules.pullback i).map (schemePullbackTensorIso v P Q).hom ≫
          (schemePullbackTensorIso i ((Scheme.Modules.pullback v).obj P)
            ((Scheme.Modules.pullback v).obj Q)).hom) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj P),
              (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj Q)))
            (Y := ((Scheme.Modules.pullback w).obj P, (Scheme.Modules.pullback w).obj Q))
            (((Scheme.Modules.pullbackComp i v).hom.app P ≫
                (Scheme.Modules.pullbackCongr hw).hom.app P,
              (Scheme.Modules.pullbackComp i v).hom.app Q ≫
                (Scheme.Modules.pullbackCongr hw).hom.app Q) : (_, _) ⟶ (_, _))) =
      ((Scheme.Modules.pullbackComp i v).hom.app
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj P).obj Q) ≫
          (Scheme.Modules.pullbackCongr hw).hom.app
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj P).obj Q)) ≫
        (schemePullbackTensorIso w P Q).hom := by
  refine Eq.trans (whisker_eq _
    (tensorSheafMap_comp W.toRingedSpace
      ((Scheme.Modules.pullbackComp i v).hom.app P)
      ((Scheme.Modules.pullbackCongr hw).hom.app P)
      ((Scheme.Modules.pullbackComp i v).hom.app Q)
      ((Scheme.Modules.pullbackCongr hw).hom.app Q))) ?_
  exact paste (schemePullbackTensorIso_pullbackComp_hom i v P Q)
    (schemePullbackTensorIso_pullbackCongr_hom hw P Q)

end Stacks.Tag01VSPullbackTensor

namespace AlgebraicGeometry

open Stacks.Tag01VSPullbackTensor (schemePullbackTensorIso
  schemePullbackTensorIso_pullbackCompCongr)

/-! ### The transitions of the completion -/

section Transitions

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [LocallyOfFiniteType f]

omit [LocallyOfFiniteType f] in
/-- `AlgebraicGeometry.adicThickeningCompletionNatIso` written out, as an equality of
isomorphisms of functors. Taken at this level deliberately: no component is evaluated, so no
transport of the inverse image functor is converted. -/
public theorem adicThickeningCompletionNatIso_eq (n : ℕ) :
    adicThickeningCompletionNatIso A I f n =
      Scheme.Modules.pullbackComp (adicBaseChangeSucc A I f n)
          (pullback.fst f (adicThickeningι A I (n + 1))) ≪≫
        Scheme.Modules.pullbackCongr (adicBaseChangeSucc_fst A I f n) := rfl

omit [LocallyOfFiniteType f] in
/-- The canonical transition of a completion is the component at `G` of the natural isomorphism
above. This is the definition; it is named so that the splitting below can be composed with it
without any conversion. -/
public theorem adicThickeningCompletionTransition_hom_eq (n : ℕ) (G : X.Modules) :
    (adicThickeningCompletionTransition A I f G n).hom =
      (adicThickeningCompletionNatIso A I f n).hom.app G := rfl

omit [LocallyOfFiniteType f] in
/-- **`AlgebraicGeometry.adicThickeningCompletionNatIso` on components is the composition law
followed by the congruence isomorphism at `iₙ ≫ vₙ₊₁ = vₙ`.**

Proved by transporting the equality of natural isomorphisms and then naming
`CategoryTheory.Iso.trans_hom` and `CategoryTheory.NatTrans.comp_app`, rather than by `rfl`: both
of those are reflexivity, but reaching them by unification goes through the category instance on
sheaves of modules on a scheme, which is a `def`, and exhausts the deterministic budget, as
a `whnf` timeout. -/
public theorem adicThickeningCompletionNatIso_hom_app (n : ℕ) (G : X.Modules) :
    (adicThickeningCompletionNatIso A I f n).hom.app G =
      (Scheme.Modules.pullbackComp (adicBaseChangeSucc A I f n)
            (pullback.fst f (adicThickeningι A I (n + 1)))).hom.app G ≫
        (Scheme.Modules.pullbackCongr (adicBaseChangeSucc_fst A I f n)).hom.app G := by
  refine Eq.trans (congrArg (fun e : Scheme.Modules.pullback
        (pullback.fst f (adicThickeningι A I (n + 1))) ⋙
        Scheme.Modules.pullback (adicBaseChangeSucc A I f n) ≅
        Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n)) =>
      e.hom.app G) (adicThickeningCompletionNatIso_eq A I f n)) ?_
  refine Eq.trans (NatTrans.congr_app (Iso.trans_hom
    (Scheme.Modules.pullbackComp (adicBaseChangeSucc A I f n)
      (pullback.fst f (adicThickeningι A I (n + 1))))
    (Scheme.Modules.pullbackCongr (adicBaseChangeSucc_fst A I f n))) G) ?_
  exact NatTrans.comp_app _ _ G

omit [LocallyOfFiniteType f] in
/-- **The two pseudofunctoriality factors at `iₙ ≫ vₙ₊₁ = vₙ` are the canonical transition of a
completion.** Stated in this direction, with the composite on the left, so that the type of the
equation is the one the generic coherence is stated at: the `Eq` takes its type from its left-hand
side, and `AlgebraicGeometry.adicThickeningCompletion` on the right would put a delta inside the
arguments of `Stacks.SheafOfModules.Tensor.sheafTensor` that converting
exhausts the deterministic budget. `adicThickeningCompletionTransition_hom` is the same equation
read the other way. -/
public theorem pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition (n : ℕ)
    (G : X.Modules) :
    (Scheme.Modules.pullbackComp (adicBaseChangeSucc A I f n)
            (pullback.fst f (adicThickeningι A I (n + 1)))).hom.app G ≫
          (Scheme.Modules.pullbackCongr (adicBaseChangeSucc_fst A I f n)).hom.app G =
      (adicThickeningCompletionTransition A I f G n).hom :=
  ((adicThickeningCompletionTransition_hom_eq A I f n G).trans
    (adicThickeningCompletionNatIso_hom_app A I f n G)).symm

omit [LocallyOfFiniteType f] in
/-- The canonical transition of a completion, on components, as the two pseudofunctoriality
factors. -/
public theorem adicThickeningCompletionTransition_hom (n : ℕ) (G : X.Modules) :
    (adicThickeningCompletionTransition A I f G n).hom =
      (Scheme.Modules.pullbackComp (adicBaseChangeSucc A I f n)
            (pullback.fst f (adicThickeningι A I (n + 1)))).hom.app G ≫
        (Scheme.Modules.pullbackCongr (adicBaseChangeSucc_fst A I f n)).hom.app G :=
  (pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition A I f n G).symm

end Transitions

/-! ### The hom-sets of the two pictures of a completion -/

section Unit

open Stacks.Algebraization (completionFunctor unitCoherentModule)
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open Stacks.AlgebraicGeometry.AffineBaseChange (unitObj pullbackUnitIso)
open Stacks.Algebraization (HasProperSupport)

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [IsLocallyNoetherian X]

/-- **The hom-sets of the two pictures of a completion agree, degreewise.** A morphism between
the `n`-th terms of the completions of `Stacks.Algebraization.completionFunctor` — quotients of
`𝒪_X`-modules on `X` — is the same thing as a morphism between the restrictions to the `n`-th adic
thickening.

Two inputs: the object-level bridge
`AlgebraicGeometry.adicThickeningCompletionPushforwardIso`, which identifies the `n`-th term of
the first picture with the direct image of the `n`-th term of the second; and [Stacks, Tag 08KS],
`Stacks.ClosedImmersion.fullyFaithfulPushforward`, which says that direct image along the closed
immersion `Xₙ ⟶ X` is fully faithful, so the direct images of the second picture's terms have the
same hom-set as the terms themselves.

**This is the identification of the two hom-sets**, built on the object-level bridge, its
normalization and its naturality; it is what carries a compatible family of units from one
picture to the other. It carries *every* compatible family, not only the units; the unit case is
`adicThickeningCompletionUnitHomEquiv` below. -/
public def adicThickeningCompletionHomEquiv (n : ℕ)
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (((completionFunctor X (baseIdealSheaf A I f)).obj F).obj.obj (op n) ⟶
        ((completionFunctor X (baseIdealSheaf A I f)).obj G).obj.obj (op n)) ≃
      (adicThickeningCompletion A I f F.obj n ⟶
        adicThickeningCompletion A I f G.obj n) :=
  ((adicThickeningCompletionPushforwardIso A I f F n).homCongr
      (adicThickeningCompletionPushforwardIso A I f G n)).trans
    (Stacks.ClosedImmersion.fullyFaithfulPushforward
      (pullback.fst f (adicThickeningι A I n))).homEquiv.symm

/-- **The identification of hom-sets takes the completion of a morphism to its restriction.** This
is what makes `adicThickeningCompletionHomEquiv` the right identification rather than some
bijection: on the image of `Stacks.Algebraization.completionFunctor` it is the image of
`AlgebraicGeometry.adicThickeningCompletionFunctor`, so a family in one picture that comes from a
morphism on `X` is carried to the family in the other picture that comes from the same morphism.

It is `AlgebraicGeometry.adicThickeningCompletionPushforwardIso_naturality` with the object-level
bridge cancelled on the left and full faithfulness of the direct image used to drop it. -/
public theorem adicThickeningCompletionHomEquiv_completionFunctor_map (n : ℕ)
    {F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf} (φ : F ⟶ G) :
    adicThickeningCompletionHomEquiv A I f n F G
        (((completionFunctor X (baseIdealSheaf A I f)).map φ).hom.app (op n)) =
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map φ.hom := by
  change (Stacks.ClosedImmersion.fullyFaithfulPushforward
      (pullback.fst f (adicThickeningι A I n))).homEquiv.symm
      ((adicThickeningCompletionPushforwardIso A I f F n).homCongr
        (adicThickeningCompletionPushforwardIso A I f G n)
        (((completionFunctor X (baseIdealSheaf A I f)).map φ).hom.app (op n))) = _
  refine (Equiv.symm_apply_eq _).mpr ?_
  exact (whisker_eq _ (adicThickeningCompletionPushforwardIso_naturality A I f φ n)).trans
    ((adicThickeningCompletionPushforwardIso A I f F n).inv_hom_id_assoc _)

/-- **The identification of the hom-sets out of the structure sheaf.** The `n`-th term of the
completion of `𝒪_X` in the picture of `Stacks.Algebraization.completionFunctor` has the same
hom-sets into the `n`-th term of the completion of `G` as `𝒪_{Xₙ}` has into `G|_{Xₙ}`.

This is `adicThickeningCompletionHomEquiv` at the unit object, composed with the identification
`Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso` of `vₙ^* 𝒪_X` with `𝒪_{Xₙ}`. It is the
change of picture the unit side of `hdata` needs:
`Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete` is
stated in the first picture and is unconditional there, while the units
`Stacks.RelativeSpec.AlgebraSheaf.unitModuleMap (B n)` of a system of algebra sheaves live in the
second. -/
public def adicThickeningCompletionUnitHomEquiv (n : ℕ)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (((completionFunctor X (baseIdealSheaf A I f)).obj (unitCoherentModule X)).obj.obj (op n) ⟶
        ((completionFunctor X (baseIdealSheaf A I f)).obj G).obj.obj (op n)) ≃
      (unitObj (adicBaseChange A I f n) ⟶ adicThickeningCompletion A I f G.obj n) :=
  (adicThickeningCompletionHomEquiv A I f n (unitCoherentModule X) G).trans
    ((pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).homCongr
      (Iso.refl (adicThickeningCompletion A I f G.obj n)))

/-- **The unit identification takes the completion of a morphism out of `𝒪_X` to its restriction,
read through `Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso`.** -/
public theorem adicThickeningCompletionUnitHomEquiv_completionFunctor_map (n : ℕ)
    {G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (μ : unitCoherentModule X ⟶ G) :
    adicThickeningCompletionUnitHomEquiv A I f n G
        (((completionFunctor X (baseIdealSheaf A I f)).map μ).hom.app (op n)) =
      (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).inv ≫
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ.hom :=
  (congrArg ((pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).homCongr
      (Iso.refl (adicThickeningCompletion A I f G.obj n)))
    (adicThickeningCompletionHomEquiv_completionFunctor_map A I f n μ)).trans
    (congrArg (fun z => (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).inv ≫ z)
      (Category.comp_id
        ((Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ.hom)))

/-- **The unit side of `hdata`, with only the change of picture left to the caller.** Let `G` be a
coherent `𝒪_X`-module whose support is proper over an `I`-adically complete Noetherian base, let
`u n : 𝒪_{Xₙ} ⟶ G|_{Xₙ}` be a family of morphisms on the adic thickenings, and suppose the family
is realized, under the identification of hom-sets above, by a morphism `α` of the completions of
`𝒪_X` and `G` in the picture of `Stacks.Algebraization.completionFunctor`. Then there is a
morphism `μ : 𝒪_X ⟶ G` on `X` restricting to `u n` for every `n`.

No hypothesis on the theorem on formal functions is carried:
`Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete` is
unconditional, its `hFF` being discharged by
`Stacks.Algebraization.isIso_globalSectionsToLimit_of_hasProperSupport` over a Noetherian
`I`-adically complete base.

So on the unit side what is left between `hdata` and the library is exactly the hypothesis `α`:
the family `u` has to be assembled into a morphism of the *first* picture's systems, whose
compatibility condition is with the quotient projections of
`Stacks.Algebraization.completionFunctor`
rather than with `AlgebraicGeometry.adicThickeningCompletionTransition`. The degreewise half of
that assembly is `adicThickeningCompletionUnitHomEquiv`; the compatibility is what
`AlgebraicGeometry.adicThickeningCompletionPushforwardIso_projection` is for, and it is not done
here. Taking `α` as a binder is what makes this a theorem rather than a conjecture, and it is a
binder about one morphism of systems, with no algebra in it. -/
@[ega "III 4.1.10" "partial"]
public theorem exists_unit_of_adicThickeningFamily [IsNoetherianRing A] [IsAdicComplete I A]
    [LocallyOfFiniteType f]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : HasProperSupport f G.obj)
    (u : ∀ n : ℕ, unitObj (adicBaseChange A I f n) ⟶ adicThickeningCompletion A I f G.obj n)
    (α : (completionFunctor X (baseIdealSheaf A I f)).obj (unitCoherentModule X) ⟶
      (completionFunctor X (baseIdealSheaf A I f)).obj G)
    (hα : ∀ n : ℕ,
      adicThickeningCompletionUnitHomEquiv A I f n G (α.hom.app (op n)) = u n) :
    ∃ μ : SheafOfModules.unit X.ringCatSheaf ⟶ G.obj, ∀ n : ℕ,
      (pullbackUnitIso (pullback.fst f (adicThickeningι A I n))).inv ≫
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ = u n := by
  obtain ⟨μ, hμ⟩ :=
    (Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete
      A I f G hG).2 α
  refine ⟨μ.hom, fun n => ?_⟩
  subst hμ
  exact (adicThickeningCompletionUnitHomEquiv_completionFunctor_map A I f n μ).symm.trans (hα n)

end Unit

end AlgebraicGeometry

end
