module

public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Pushout along a change of the ideal module is faithful

Fix a square-zero extension problem `S : RingedToposExtensionProblem X B` of ringed topoi — the
problem (91.13.0.1) of [Stacks Project, Tag 08UF] — and a map `φ : 𝒢 ⟶ 𝒢'` of `𝒪`-modules out
of its prescribed ideal module. Composing the prescribed map `c : f⁻¹𝒥 ⟶ 𝒢` with `φ` gives a
second problem over the same bottom row, `changeKernel S φ`, and *pushout along `φ`* is a
functor

`F : {solutions of S} ⥤ {solutions of changeKernel S φ}`

from the solutions of the first to the solutions of the second. When `S.baseReduction` is
invertible the solutions of `S` are exactly the square-zero extensions
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `f⁻¹𝒪_ℬ`-algebras — this is the reading of the problem that the
library's [Stacks Project, Tag 0GQ5] uses, see
`StacksFrontier/Deformation/ToposThickening/SquareZeroExtensionClasses.lean`, and
`Deformation.ToposThickening.RingedToposExtensionProblem.squareZeroProblem` together with
`.isIso_squareZeroProblem_baseReduction` is a problem of exactly that shape — so `F` is then
the functor of the situation preceding [Stacks Project, Tag 0D3P].

The source writes the two modules `ℱ ⟶ 𝒢` and the problem's own ideal `𝒥`; here the problem's
prescribed module is `S.G` and the second one is `N`, so `φ : 𝒢 ⟶ 𝒢'` below is the source's
`ℱ ⟶ 𝒢`.

This file proves that `F` is **faithful**, which is one half of the "fully faithful" half of
that tag, and that `F` is **full** under one hypothesis the source does not have and this
library cannot derive — see *What is not covered*, and
`...RingedToposExtensionProblem.ReflectsIsomorphicSolutions`.

The faithfulness proof is the source's own: two morphisms of solutions `P ⟶ Q` differ by a unique
derivation of `P` with values in `𝒢`, by clause (2) of [Stacks Project, Tag 08UG] in the form
proved at
`...RingedToposExtensionProblem.CompatibleFirstOrderThickening.translate_existsUnique`;
the pushout comparison `j_Q : Q ⟶ F(Q)` carries that derivation to `φ ∘ δ`, because `j_Q`
induces `φ` on the identified ideals; so two morphisms with the same image under `F` differ by
a derivation killed by `φ`, and the source's hypothesis that `φ` induces an *injection* on
`Ext⁰` makes that derivation zero.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.changeKernel`: the problem with the
  same bottom row and the ideal module `𝒢` replaced by `𝒢'` along `φ`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.KernelChangeHom`: a morphism of
  solutions over the change of ideal — a map of thickened structure sheaves over `𝒪`, under
  `f⁻¹𝒪_{ℬ'}`, inducing `φ` on the identified ideals. This is the comparison `j_P : P ⟶ F(P)`
  of a pushout.
* `Deformation.ToposThickening.RingedToposExtensionProblem.IsKernelPushoutFunctor`: the
  universal property that makes a functor between the two solution groupoids *the* pushout
  along `φ` — a comparison `j_P` for every solution, natural in `P`, through which every
  `KernelChangeHom` out of `P` factors uniquely.
* `...RingedToposExtensionProblem.CompatibleFirstOrderThickening.DerivationTo`:
  a derivation of a solution of `S` with values in an arbitrary `𝒪`-module rather than in the
  problem's own ideal module. This is the source's `Ext⁰_X(NL_{X/B}, −)`, read in the library's
  concrete model, as a functor of the module.
* `Deformation.ToposThickening.RingedToposExtensionProblem.IsInjectiveOnDerivations` and
  `...IsSurjectiveOnDerivations`: post-composition with `φ` is injective, respectively
  surjective, on the derivations of the solutions of `S`. These are the source's
  `Ext⁰_X(NL_{X/B}, 𝒢) ⟶ Ext⁰_X(NL_{X/B}, 𝒢')` being injective, respectively surjective, read in
  the library's concrete model of those groups; see *What is carried, and why*.
* `Deformation.ToposThickening.RingedToposExtensionProblem.ReflectsIsomorphicSolutions`: `F`
  reflects isomorphy of solutions. This is **not** a reading of a hypothesis of the source but a
  stand-in for an input of its proof that this library cannot state; it is implied by the
  conclusion of the tag, so nothing assuming it carries the tag. See *What is not covered*.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.faithful_of_isKernelPushoutFunctor`:
  **the faithfulness clause of [Stacks Project, Tag 0D3P]** — pushout along `φ` is a faithful
  functor on solution groupoids.
* `Deformation.ToposThickening.RingedToposExtensionProblem.surjective_map_of_nonempty_hom`:
  the degree-zero half of the fullness clause — between two solutions that admit *some*
  morphism, pushout along `φ` is surjective on morphisms. Untagged: `Nonempty (P ⟶ Q)` is an
  added hypothesis.
* `Deformation.ToposThickening.RingedToposExtensionProblem.full_of_isKernelPushoutFunctor` and
  `...fullyFaithful_of_isKernelPushoutFunctor`: pushout along `φ` is full, respectively fully
  faithful, given `IsSurjectiveOnDerivations` and `ReflectsIsomorphicSolutions`. Untagged, for
  the latter hypothesis.
* `Deformation.ToposThickening.RingedToposExtensionProblem.isInjectiveOnDerivations_of_injective`:
  a `φ` that is injective on sections satisfies the hypothesis.

## What is carried, and why

Three things are hypotheses rather than constructions, and the clause string of the tag names
all three.

**The functor.** The source introduces `F` by the words "given by pushout" and proves nothing
about its existence. Here it is carried together with the universal property that pins it down,
`IsKernelPushoutFunctor`, so the theorem is a statement about the pushout functor and not about
an arbitrary functor with a natural comparison. The object-level construction exists in the
library — `Stacks.Sites.SqZeroPushout.pushoutSheaf` of
`StacksFrontier/CategoryTheory/Sites/Modules/SquareZeroPushout.lean` builds `(𝒪' ⋉ 𝒢')/J` for a
locally surjective `𝒪' ⟶ 𝒪` and a map out of its kernel, which is exactly `F` on objects — but
assembling it into a functor on solution groupoids, with the `baseMap`, the kernel
identification and the universal property, is not done here.

**The `Ext⁰` injectivity.** The source's hypotheses are that `X` is quasi-compact and
quasi-separated and that `DQ_X(𝒢) ⟶ DQ_X(𝒢')` is an isomorphism, from which its proof deduces
that `Ext^i_X(NL_{X/B}, 𝒢) ⟶ Ext^i_X(NL_{X/B}, 𝒢')` is an isomorphism for every `i`, using that
`NL_{X/B}` lies in `D_{QCoh}(𝒪_X)` ([Stacks Project, Tag 0D0Y]). That deduction is now
formalized: the quasi-coherence of the cohomology sheaves of `NL_{X/B}` is
[Stacks Project, Tag 0D0Y] at `AlgebraicGeometry.Space.naiveCotangentComplex_homology`, and
[Stacks Project, Tag 0D3P] itself is
`AlgebraicGeometry.Space.isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map_of_qcqs`, for
a morphism of algebraic spaces. The statements of this file are the ringed-topos forms, which
carry the conclusion instead; so what is carried here is the conclusion the source's proof
actually uses, in degree `0` and in the injective direction only, which is all faithfulness needs.

Moreover it is carried for the *concrete* acting group. The library's clause (2) of
[Stacks Project, Tag 08UG] acts by
`...RingedToposExtensionProblem.CompatibleFirstOrderThickening.Derivation`,
section-wise derivations of the thickened structure sheaf vanishing on the ideal and on the
image of `f⁻¹𝒪_{ℬ'}`, and its identification with `Ext⁰_X(NL_{X/B}, 𝒢)` is explicitly not
claimed there, nor in the 08V5 of
`StacksFrontier/Deformation/ToposThickening/SolutionAutomorphisms.lean`, which records the three
missing steps. So `IsInjectiveOnDerivations` is the source's `Ext⁰` injectivity read through
that model, and the tag says so.

**The generality.** The statement is for an arbitrary morphism of ringed topoi and an arbitrary
square-zero extension problem, where the source has a morphism `f : X ⟶ B` of algebraic spaces
and the bottom row `0 ⟶ 0 ⟶ f⁻¹𝒪_ℬ ⟶ f⁻¹𝒪_ℬ ⟶ 0`. The source's own proof is entirely through
the ringed-topos lemmas [Stacks Project, Tag 08UG] and [Stacks Project, Tag 08UK], applied to
the small étale ringed topoi, so this is the generality at which its argument runs; `𝒪_X`-module
maps on `X_étale` and solutions on the small étale ringed topos of `X` are the instance
obtained by taking `f` to be `AlgebraicGeometry.Space.smallEtaleRingedToposHom`. Allowing the
bottom row a genuine base thickening — that is, dropping `IsIso S.baseReduction`, which this
statement never uses — makes the functor the `FT` of [Stacks Project, Tag 0D3Q]; that tag is
not claimed.

## What is not covered

Neither the fullness clause nor essential surjectivity is proved *as the source states them*,
so 0D3P's conclusion that `F` is an equivalence is not available.

*Fullness* splits into two halves, and only the first is reachable here. The morphisms `P ⟶ Q`
are a principal homogeneous space under the derivations of `P` **only when there is at least one
of them**, so the degree-zero argument proves exactly `surjective_map_of_nonempty_hom`: given
one morphism `P ⟶ Q`, the `Ext⁰` surjectivity produces the preimage of any `F(P) ⟶ F(Q)`. The
remaining half is the non-emptiness itself, and it is not derivable from
`IsKernelPushoutFunctor` and a degree-zero hypothesis — the universal property pins down only
the morphisms *out of* `F(P)`, and pushout along `φ` genuinely need not reflect isomorphy: for
`φ = 0` with no non-zero derivations, `IsInjectiveOnDerivations` and
`IsSurjectiveOnDerivations` both hold while every `F(P)` is the trivial extension, so all of
them are isomorphic however many isomorphism classes of solutions `S` has.

What the source uses there is injectivity of `Ext¹_X(NL_{X/B}, 𝒢) ⟶ Ext¹_X(NL_{X/B}, 𝒢')`
together with the *torsor* half of [Stacks Project, Tag 08UK], which attaches to a pair of
solutions a class in `Ext¹` vanishing exactly when they are isomorphic. Of that, the
pair-to-`Ext¹` assignment is *carried* as an assumption by the three statements that use it —
`...SquareZeroExtensionClasses.setoid_iff_isomorphic`, `...classesEquivExt` and
`...SolutionClassesFibre.classesEquivFibre` — and its naturality under the pushout, which is
what the fullness argument would need, is not expressible against an assumed assignment.

So the non-emptiness is carried here as the hypothesis `ReflectsIsomorphicSolutions`. The
declarations that assume it do **not** carry the tag, because that hypothesis is
implied by 0D3P's own conclusion — a fully faithful functor reflects isomorphy — so assuming it
would assume what is claimed. The implication to it from the source's stated hypotheses needs
the quasi-coherence of `NL_{X/B}`
([Stacks Project, Tag 0D0Y]), which is proved at
`AlgebraicGeometry.Space.naiveCotangentComplex_homology`; the tag is registered on the
algebraic-space form
`AlgebraicGeometry.Space.isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map_of_qcqs`.

The two extra instance assumptions of the fullness statements — that the topology admits the
forgetful sheaf composition for commutative rings and that the forgetful functor reflects
isomorphisms — are the ones under which the library's [Stacks Project, Tag 08UK]
(`CompatibleFirstOrderThickening.Hom.isIso`) and [Stacks Project, Tag 08V5] are stated, and are
needed for the same reason: the translate of a morphism of solutions by a derivation is produced
as a morphism, and the groupoid of solutions has the *isomorphisms* for its morphisms.

*Essential surjectivity* is "by [Stacks Project, Tag 08UK]" in the source, and uses the half of
that tag which this library does not have: that the isomorphism classes of solutions are a
*torsor* under `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)`. Only the separation half is proved, at
`Deformation.ToposThickening.RingedToposExtensionProblem.isomorphic_iff_nonempty_hom`; the
implementation notes of
`StacksFrontier/Deformation/ToposThickening/SolutionIsomorphism.lean` record what the torsor half
is missing, and on a general site it needs [Stacks Project, Tag 08UB], which the library has
only on the site of open sets of a topological space
(`StacksFrontier/Topology/Sheaves/Modules/NaiveCotangentExtClassRepresentation.lean`).

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open CompatibleFirstOrderThickening

variable {X : RingedTopos.{v, u, w}}
  {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-! ### Changing the ideal module of a problem -/

/-- The square-zero extension problem with the same bottom row as `S` and the prescribed ideal
module `𝒢` replaced by `𝒢'` along `φ : 𝒢 ⟶ 𝒢'`: the prescribed map `c : f⁻¹𝒥 ⟶ 𝒢` from the base
ideal is composed with `φ`. Its solutions are the target of the pushout functor of the
situation preceding [Stacks Project, Tag 0D3P]. -/
public noncomputable abbrev changeKernel (S : RingedToposExtensionProblem X B)
    {N : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (φ : S.G ⟶ N) : RingedToposExtensionProblem X B :=
  { S with
    G := N
    c := S.c ≫ (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        S.f.fSharpInverseImage)).map φ }

variable {S : RingedToposExtensionProblem X B}
  {N : SheafOfModules.{w}
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}

/-- A morphism of solutions over a change of the ideal module: a morphism of the thickened
structure sheaves which is over the reduced structure sheaf, under the inverse image of the
thickened base, and induces `φ` — rather than the identity — on the identified ideals. This is
the comparison `j_P : P ⟶ F(P)` a pushout along `φ` comes with; for `φ` the identity it is
`CompatibleFirstOrderThickening.Hom`. -/
public structure KernelChangeHom (φ : S.G ⟶ N)
    (P : S.CompatibleFirstOrderThickening)
    (R : (changeKernel S φ).CompatibleFirstOrderThickening) where
  /-- The morphism of the thickened structure sheaves. -/
  hom : P.extension ⟶ R.extension
  /-- It is over the reduced structure sheaf. -/
  reduction_comm : hom ≫ R.reduction = P.reduction
  /-- It respects the map from the inverse image of the thickened base. -/
  baseMap_comm :
    P.baseMap ≫ hom =
      (show (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ R.extension from
        R.baseMap)
  /-- It induces `φ` on the identified ideals. -/
  kernel_comm : ∀ (U : X.Cᵒᵖ) (g : S.G.val.obj U),
    hom.hom.app U (P.incl g) = R.incl (show N.val.obj U from φ.val.app U g)

/-- **The universal property of pushout along `φ`.** A functor from the solutions of `S` to the
solutions of `changeKernel S φ` is pushout along `φ` when it comes with a comparison
`j_P : P ⟶ F(P)` for every solution `P`, natural in `P`, through which every morphism out of `P`
over the change of ideal factors uniquely. This is the source's "given by pushout". -/
public def IsKernelPushoutFunctor (φ : S.G ⟶ N)
    (F : S.CompatibleFirstOrderThickening ⥤
      (changeKernel S φ).CompatibleFirstOrderThickening) : Prop :=
  ∃ j : ∀ P : S.CompatibleFirstOrderThickening, KernelChangeHom φ P (F.obj P),
    (∀ {P Q : S.CompatibleFirstOrderThickening} (k : P ⟶ Q),
      (j P).hom ≫ (F.map k).hom.hom = k.hom.hom ≫ (j Q).hom) ∧
    (∀ (P : S.CompatibleFirstOrderThickening)
      (R : (changeKernel S φ).CompatibleFirstOrderThickening)
      (h : KernelChangeHom φ P R),
      ∃! k : F.obj P ⟶ R, (j P).hom ≫ k.hom.hom = h.hom)

/-! ### The hypothesis on `φ` -/

/-- **Post-composition with `φ` is injective on derivations.** This is the source's injectivity
of `Ext⁰_X(NL_{X/B}, 𝒢) ⟶ Ext⁰_X(NL_{X/B}, 𝒢')`, read in the concrete model of that group used
by the library's clause (2) of [Stacks Project, Tag 08UG]: the derivations of a solution, which are
section-wise additive maps out of its thickened structure sheaf obeying the Leibniz rule and
vanishing on the ideal and on the image of `f⁻¹𝒪_{ℬ'}`. Since those derivations form an additive
group and post-composition with `φ` is additive, injectivity is the vanishing of its kernel,
which is the form stated. -/
public abbrev IsInjectiveOnDerivations (φ : S.G ⟶ N) : Prop :=
  ∀ (P : S.CompatibleFirstOrderThickening)
    (δ : CompatibleFirstOrderThickening.Derivation P),
    (∀ (U : X.Cᵒᵖ) (x : P.extension.obj.obj U), φ.val.app U (δ.toFun U x) = 0) → δ = 0

/-- A map of modules that is injective on sections is injective on derivations. -/
public theorem isInjectiveOnDerivations_of_injective (φ : S.G ⟶ N)
    (hφ : ∀ U : X.Cᵒᵖ, Function.Injective (φ.val.app U)) :
    IsInjectiveOnDerivations φ := fun _ δ h =>
  Derivation.ext_apply fun U x => by
    change δ.toFun U x = 0
    refine hφ U ?_
    rw [h U x]
    exact (map_zero (φ.val.app U).hom).symm

namespace CompatibleFirstOrderThickening

/-- The derivation situation of a solution `P` of `S` with the values taken in an arbitrary
`𝒪`-module `M` rather than in the problem's own prescribed ideal module: the same thickened
structure sheaf, reduction, structure map from `f⁻¹𝒪_{ℬ'}` and identified ideal `S.G`, only the
module a derivation lands in is changed. For `M = S.G` it is
`CompatibleFirstOrderThickening.toSituation`. -/
public noncomputable abbrev situationTo (P : S.CompatibleFirstOrderThickening)
    (M : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)) :
    DerivationSituation X.J :=
  { P.toSituation with G := M }

/-- A derivation of a solution `P` of `S` **with values in `M`**: a section-wise additive map
from the thickened structure sheaf of `P` to `M`, natural in the object of the site, satisfying
the Leibniz rule with scalars acting through the reduction of `P`, and vanishing both on the
ideal `S.G` of `P` and on the image of `f⁻¹𝒪_{ℬ'}`. For `M = S.G` it is
`CompatibleFirstOrderThickening.Derivation`.

This is the group the source writes `Ext⁰_X(NL_{X/B}, M)`, read in the concrete model of the
library's clause (2) of [Stacks Project, Tag 08UG]; post-composition with a map `φ : S.G ⟶ M` of
modules sends `Derivation P` into it, and `IsInjectiveOnDerivations` and
`IsSurjectiveOnDerivations` are the injectivity and surjectivity of that map. -/
public abbrev DerivationTo (P : S.CompatibleFirstOrderThickening)
    (M : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)) :=
  _root_.Deformation.ToposThickening.Derivation (P.situationTo M)

end CompatibleFirstOrderThickening

/-- **Post-composition with `φ` is surjective on derivations.** This is the source's
surjectivity of `Ext⁰_X(NL_{X/B}, 𝒢) ⟶ Ext⁰_X(NL_{X/B}, 𝒢')`, read in the same concrete model
of those groups as `IsInjectiveOnDerivations`: every derivation of a solution of `S` with values
in `𝒢'` is `φ ∘ δ` for a derivation `δ` with values in `𝒢`. -/
public abbrev IsSurjectiveOnDerivations (φ : S.G ⟶ N) : Prop :=
  ∀ (P : S.CompatibleFirstOrderThickening) (ε : P.DerivationTo N),
    ∃ δ : CompatibleFirstOrderThickening.Derivation P,
      ∀ (U : X.Cᵒᵖ) (x : P.extension.obj.obj U),
        φ.val.app U (δ.toFun U x) = ε.toFun U x

/-! ### Faithfulness -/

omit [X.J.HasSheafCompose (forget RingCat)] [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Composition of morphisms of sheaves of commutative rings, on sections. -/
private theorem sheafComp_apply {A A' A'' : Sheaf X.J CommRingCat.{w}} (a : A ⟶ A')
    (b : A' ⟶ A'') (U : X.Cᵒᵖ) (x : A.obj.obj U) :
    (a ≫ b).hom.app U x = b.hom.app U (a.hom.app U x) := rfl

/-- An equality of composites of morphisms of sheaves of commutative rings, on sections. -/
private theorem sheafComp_eq_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A A' A'' B : Sheaf J CommRingCat.{w}} {a : A ⟶ A'} {b : A' ⟶ A''} {c : A ⟶ B}
    {d : B ⟶ A''} (h : a ≫ b = c ≫ d) (U : Cᵒᵖ) (x : A.obj.obj U) :
    b.hom.app U (a.hom.app U x) = d.hom.app U (c.hom.app U x) :=
  congrArg (fun m : A ⟶ A'' => m.hom.app U x) h

/-- **[Stacks Project, Tag 0D3P], the faithfulness clause.** Let `S` be a square-zero extension
problem of ringed topoi, let `φ : 𝒢 ⟶ 𝒢'` be a map out of its prescribed ideal module, and let
`F` be pushout along `φ`, from the solutions of `S` to the solutions of `changeKernel S φ`. If
post-composition with `φ` is injective on the derivations of the solutions of `S` — the source's
injectivity of `Ext⁰_X(NL_{X/B}, 𝒢) ⟶ Ext⁰_X(NL_{X/B}, 𝒢')` — then `F` is faithful.

The proof is the source's. Let `u, v : P ⟶ Q` be isomorphisms of solutions with `F u = F v`.
Naturality of the pushout comparison turns that into `u ≫ j_Q = v ≫ j_Q` on thickened structure
sheaves. The difference of `u` and `v` on a section is the inclusion of a section of `𝒢`, and
that assignment is a derivation `δ` of `P`
(`CompatibleFirstOrderThickening.derivationOfHoms`, the construction underlying clause (2) of
[Stacks Project, Tag 08UG]). Applying `j_Q`, which induces `φ` on ideals, the inclusion of
`φ ∘ δ` in `F(Q)` is the difference of `u ≫ j_Q` and `v ≫ j_Q`, hence zero; the inclusion is
injective on sections, so `φ ∘ δ = 0`, so `δ = 0` by hypothesis. Finally translating `u` by the
zero derivation gives `u` and translating it by `δ` gives `v`
(`CompatibleFirstOrderThickening.translate_existsUnique`, clause (2) of Tag 08UG), so `u = v`. -/
public theorem faithful_of_isKernelPushoutFunctor (φ : S.G ⟶ N)
    (F : S.CompatibleFirstOrderThickening ⥤
      (changeKernel S φ).CompatibleFirstOrderThickening)
    (hF : IsKernelPushoutFunctor φ F) (hφ : IsInjectiveOnDerivations φ) :
    F.Faithful := by
  obtain ⟨j, hnat, -⟩ := hF
  refine ⟨fun {P Q} {u v} huv => ?_⟩
  have hcomp : u.hom.hom ≫ (j Q).hom = v.hom.hom ≫ (j Q).hom := by
    rw [← hnat u, ← hnat v, huv]
  have hδ : derivationOfHoms (Iso.toHom u) (Iso.toHom v) = 0 := by
    refine hφ P _ fun U x => ?_
    refine (F.obj Q).incl_injective ?_
    rw [(F.obj Q).incl_zero, derivationOfHoms_toFun,
      ← (j Q).kernel_comm U (diff (Iso.toHom u) (Iso.toHom v) U x),
      incl_diff, map_sub, sub_eq_zero]
    exact (sheafComp_eq_apply hcomp U x).symm
  have htr : translate (Iso.toHom u) (derivationOfHoms (Iso.toHom u) (Iso.toHom v)) =
      Iso.toHom v := translate_derivationOfHoms _ _
  rw [hδ, translate_zero] at htr
  exact Iso.ext (CategoryTheory.Iso.ext (congrArg (fun h : Hom P Q => h.hom) htr))

/-! ### Fullness -/

namespace KernelChangeHom

variable {φ : S.G ⟶ N} {P Q : S.CompatibleFirstOrderThickening}
  {R : (changeKernel S φ).CompatibleFirstOrderThickening}

/-- A morphism over the change of ideal is over the reduced structure sheaf, on sections. -/
public theorem reduction_apply (a : KernelChangeHom φ P R) {U : X.Cᵒᵖ}
    (x : P.extension.obj.obj U) :
    R.reduction.hom.app U (a.hom.hom.app U x) = P.reduction.hom.app U x :=
  congrArg (fun k : P.extension ⟶ X.O => k.hom.app U x) a.reduction_comm

/-- A morphism over the change of ideal respects the map from the inverse image of the thickened
base, on sections. -/
public theorem baseMap_apply (a : KernelChangeHom φ P R) {U : X.Cᵒᵖ}
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    a.hom.hom.app U (P.baseMap.hom.app U b) =
      (show (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ R.extension from
        R.baseMap).hom.app U b :=
  congrArg
    (fun k : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ R.extension =>
      k.hom.app U b) a.baseMap_comm

/-- Precomposing a morphism over the change of ideal with a morphism of solutions of `S`. -/
public def precomp (u : Hom P Q) (a : KernelChangeHom φ Q R) : KernelChangeHom φ P R where
  hom := u.hom ≫ a.hom
  reduction_comm := by rw [Category.assoc, a.reduction_comm, u.reduction_comm]
  baseMap_comm := by rw [← Category.assoc, u.baseMap_comm]; exact a.baseMap_comm
  kernel_comm U g := by rw [sheafComp_apply, u.kernel_comm, a.kernel_comm]

/-- The underlying homomorphism of a precomposite. -/
@[simp]
public theorem precomp_hom (u : Hom P Q) (a : KernelChangeHom φ Q R) :
    (precomp u a).hom = u.hom ≫ a.hom := rfl

/-- **A derivation pulls back along a morphism over the change of ideal.** If `a : P ⟶ R` induces
`φ` on the identified ideals, a derivation `ε` of `R` — which takes its values in `𝒢'` — composes
with `a` to a derivation of `P` with values in `𝒢'`. Applied to the pushout comparison
`j_P : P ⟶ F(P)` this is how a derivation of `F(P)` is read as a derivation of `P` with values in
`𝒢'`, which is where `IsSurjectiveOnDerivations` applies. -/
public def compDerivation (a : KernelChangeHom φ P R)
    (ε : CompatibleFirstOrderThickening.Derivation R) : P.DerivationTo N where
  toFun := fun U x => ε.toFun U (a.hom.hom.app U x)
  map_add' U x y := by
    change ε.toFun U (a.hom.hom.app U (x + y)) =
      ε.toFun U (a.hom.hom.app U x) + ε.toFun U (a.hom.hom.app U y)
    rw [show a.hom.hom.app U (x + y) = a.hom.hom.app U x + a.hom.hom.app U y from by simp]
    exact ε.map_add' U _ _
  naturality := fun {U V} h x => by
    change ε.toFun V (a.hom.hom.app V (P.extension.obj.map h x)) =
      (show N.val.obj V from N.val.map h (ε.toFun U (a.hom.hom.app U x)))
    rw [sheafHom_naturality_apply]
    exact ε.naturality h _
  leibniz U x y := by
    change ε.toFun U (a.hom.hom.app U (x * y)) =
      toRingSection X.J (P.reduction.hom.app U x) • ε.toFun U (a.hom.hom.app U y) +
        toRingSection X.J (P.reduction.hom.app U y) • ε.toFun U (a.hom.hom.app U x)
    rw [show a.hom.hom.app U (x * y) = a.hom.hom.app U x * a.hom.hom.app U y from by simp,
      ε.leibniz U _ _]
    change toRingSection X.J (R.reduction.hom.app U (a.hom.hom.app U x)) • _ +
        toRingSection X.J (R.reduction.hom.app U (a.hom.hom.app U y)) • _ = _
    rw [a.reduction_apply, a.reduction_apply]
  map_kernel U g := by
    change ε.toFun U (a.hom.hom.app U (P.incl g)) = 0
    rw [a.kernel_comm]
    exact ε.map_kernel U _
  map_base U b := by
    change ε.toFun U (a.hom.hom.app U (P.baseMap.hom.app U b)) = 0
    rw [a.baseMap_apply]
    exact ε.map_base U b

/-- The pullback of a derivation along a morphism over the change of ideal, on sections. -/
@[simp]
public theorem compDerivation_toFun (a : KernelChangeHom φ P R)
    (ε : CompatibleFirstOrderThickening.Derivation R) (U : X.Cᵒᵖ)
    (x : P.extension.obj.obj U) :
    (a.compDerivation ε).toFun U x = ε.toFun U (a.hom.hom.app U x) := rfl

end KernelChangeHom

/-- **The pushout functor reflects isomorphy of solutions.** For any two solutions `P`, `Q` of
`S`, if `F(P)` and `F(Q)` are isomorphic then so are `P` and `Q`.

This is **not** a consequence of the source's hypotheses that this library can derive, and it is
not derivable from `IsKernelPushoutFunctor` either: it is the one input the fullness clause of
[Stacks Project, Tag 0D3P] needs beyond degree zero. In the source it comes from injectivity of
`Ext¹_X(NL_{X/B}, 𝒢) ⟶ Ext¹_X(NL_{X/B}, 𝒢')` together with the *torsor* half of
[Stacks Project, Tag 08UK] — which attaches to a pair of solutions a class in `Ext¹` vanishing
exactly when they are isomorphic.

It is stated in this weakest form on purpose: the declarations below state fullness without
committing to a presentation, a family of generators or a two-term complex.

Because it is implied by the conclusion of 0D3P — a fully faithful functor reflects isomorphy —
the declarations below that assume it do **not** carry the tag. -/
public def ReflectsIsomorphicSolutions (φ : S.G ⟶ N)
    (F : S.CompatibleFirstOrderThickening ⥤
      (changeKernel S φ).CompatibleFirstOrderThickening) : Prop :=
  ∀ P Q : S.CompatibleFirstOrderThickening,
    CompatibleFirstOrderThickening.Isomorphic (F.obj P) (F.obj Q) →
      CompatibleFirstOrderThickening.Isomorphic P Q

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms]

/-- **Pushout along `φ` is full between any two solutions that are already isomorphic.** Let `F`
be pushout along `φ : 𝒢 ⟶ 𝒢'`, let `P`, `Q` be solutions of `S` and assume there is *some*
morphism `P ⟶ Q`. If post-composition with `φ` is surjective on derivations — the source's
surjectivity of `Ext⁰_X(NL_{X/B}, 𝒢) ⟶ Ext⁰_X(NL_{X/B}, 𝒢')` — then every morphism
`F(P) ⟶ F(Q)` is `F` of a morphism `P ⟶ Q`.

This is the degree-zero half of the fullness clause of [Stacks Project, Tag 0D3P], and it is
all of that clause except for the existence of one morphism `P ⟶ Q`; the hypothesis
`Nonempty (P ⟶ Q)` is an added hypothesis that the source does not have, so this does not carry
the tag. See `ReflectsIsomorphicSolutions` for what the source uses instead and why this library
cannot state it.

The proof is the source's. Fix a morphism `u₀ : P ⟶ Q`. A morphism `k : F(P) ⟶ F(Q)` and
`F(u₀)` differ by a unique derivation `ε` of `F(P)` with values in `𝒢'` (clause (2) of
[Stacks Project, Tag 08UG]); pulling `ε` back along the pushout comparison `j_P : P ⟶ F(P)`
makes it a derivation of `P` with values in `𝒢'`, so by hypothesis it is `φ ∘ δ` for a derivation
`δ` of `P`. Translating `u₀` by `δ` gives `u : P ⟶ Q` with `j_P ≫ k = u ≫ j_Q`, because `j_Q`
induces `φ` on the identified ideals; and `F(u)` is, by the uniqueness in the universal property
of the pushout, the only morphism `F(P) ⟶ F(Q)` factoring `u ≫ j_Q` through `j_P`, so
`F(u) = k`. -/
public theorem surjective_map_of_nonempty_hom (φ : S.G ⟶ N)
    (F : S.CompatibleFirstOrderThickening ⥤
      (changeKernel S φ).CompatibleFirstOrderThickening)
    (hF : IsKernelPushoutFunctor φ F) (hφ : IsSurjectiveOnDerivations φ)
    {P Q : S.CompatibleFirstOrderThickening} (hPQ : Nonempty (P ⟶ Q)) :
    Function.Surjective (F.map : (P ⟶ Q) → (F.obj P ⟶ F.obj Q)) := by
  obtain ⟨j, hnat, huniq⟩ := hF
  obtain ⟨u₀⟩ := hPQ
  intro k
  obtain ⟨δ, hδ⟩ := hφ P ((j P).compDerivation
    (derivationOfHoms (Iso.toHom (F.map u₀)) (Iso.toHom k)))
  refine ⟨(translate (Iso.toHom u₀) δ).toIso, ?_⟩
  refine (huniq P (F.obj Q)
    (KernelChangeHom.precomp (translate (Iso.toHom u₀) δ) (j Q))).unique (hnat _) ?_
  refine sheafHom_ext X.J fun U x => ?_
  have hu₀ : (Iso.toHom (F.map u₀)).hom.hom.app U ((j P).hom.hom.app U x) =
      (j Q).hom.hom.app U ((Iso.toHom u₀).hom.hom.app U x) := sheafComp_eq_apply (hnat u₀) U x
  rw [KernelChangeHom.precomp_hom, sheafComp_apply, sheafComp_apply, translate_apply, map_add,
    (j Q).kernel_comm, hδ U x, KernelChangeHom.compDerivation_toFun, derivationOfHoms_toFun,
    incl_diff, ← hu₀]
  change k.hom.hom.hom.app U ((j P).hom.hom.app U x) =
    (Iso.toHom (F.map u₀)).hom.hom.app U ((j P).hom.hom.app U x) +
      (k.hom.hom.hom.app U ((j P).hom.hom.app U x) -
        (Iso.toHom (F.map u₀)).hom.hom.app U ((j P).hom.hom.app U x))
  abel

/-- **Pushout along `φ` is full**, given the degree-zero surjectivity and the reflection of
isomorphy. Let `F` be pushout along `φ : 𝒢 ⟶ 𝒢'`. If post-composition with `φ` is surjective on
derivations and `F` reflects isomorphy of solutions, then `F` is full.

This is **not** the fullness clause of [Stacks Project, Tag 0D3P] and does not carry its tag:
`ReflectsIsomorphicSolutions` is an added hypothesis, implied by the tag's own conclusion, which
stands in for an input — injectivity of the `Ext¹` map together with the torsor half of
[Stacks Project, Tag 08UK] — that this library cannot state. Its docstring says exactly what is
missing. -/
public theorem full_of_isKernelPushoutFunctor (φ : S.G ⟶ N)
    (F : S.CompatibleFirstOrderThickening ⥤
      (changeKernel S φ).CompatibleFirstOrderThickening)
    (hF : IsKernelPushoutFunctor φ F) (hφ : IsSurjectiveOnDerivations φ)
    (hiso : ReflectsIsomorphicSolutions φ F) : F.Full := by
  refine ⟨fun {P Q} k => ?_⟩
  exact surjective_map_of_nonempty_hom φ F hF hφ (hiso P Q ⟨k⟩) k

/-- **Pushout along `φ` is fully faithful**, given the two degree-zero hypotheses and the
reflection of isomorphy: `F` is faithful by `faithful_of_isKernelPushoutFunctor` and full by
`full_of_isKernelPushoutFunctor`.

This is **not** the fully faithful half of [Stacks Project, Tag 0D3P] and does not carry its
tag, for the same reason `full_of_isKernelPushoutFunctor` does not: the hypothesis
`ReflectsIsomorphicSolutions` is implied by the tag's conclusion and stands in for an `Ext¹`
input this library cannot state. The faithfulness clause alone, which needs no such hypothesis,
is `faithful_of_isKernelPushoutFunctor`, and that is where the tag sits. -/
public noncomputable def fullyFaithful_of_isKernelPushoutFunctor (φ : S.G ⟶ N)
    (F : S.CompatibleFirstOrderThickening ⥤
      (changeKernel S φ).CompatibleFirstOrderThickening)
    (hF : IsKernelPushoutFunctor φ F) (hinj : IsInjectiveOnDerivations φ)
    (hsurj : IsSurjectiveOnDerivations φ) (hiso : ReflectsIsomorphicSolutions φ F) :
    F.FullyFaithful :=
  haveI := full_of_isKernelPushoutFunctor φ F hF hsurj hiso
  haveI := faithful_of_isKernelPushoutFunctor φ F hF hinj
  Functor.FullyFaithful.ofFullyFaithful F

end Deformation.ToposThickening.RingedToposExtensionProblem

end
