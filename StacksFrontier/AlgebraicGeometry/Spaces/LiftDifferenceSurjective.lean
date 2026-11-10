module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent

/-!
# Every linear map on the differentials is the descended difference of a pair of lifts

Let `a : X ⟶ Y` and `b : Y ⟶ T` be morphisms of algebraic spaces over a scheme `S`, let `C` be
a sheaf of `𝒪_X`-modules and let `q : A ⟶ 𝒪_Y` be a locally surjective morphism of sheaves of
rings on the small étale site of `Y` — the quotient map of a thickening of `Y`.  A *lift* is a
morphism of sheaves of rings `f : A ⟶ 𝒜` into an ambient sheaf of rings carrying a square-zero
ideal identified with `a_*C`, and
`AlgebraicGeometry.Space.liftDifferenceDifferentialsHom` descends the difference of two lifts to
an `𝒪_X`-linear map

`θ : a^*Ω_{Y/T} ⟶ C`.

`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceInjective.lean` proves that the
correspondence is *injective* on the pairs of lifts sharing their first member.  This file
proves that it is *surjective*: for every `θ` the map

`g = f − ι ∘ D ∘ q`, where `D = d_{Y/T} ∘ θ` is the `𝒪_T`-derivation attached to `θ` by
Equation [Stacks Project, Tag 0619],

is again a morphism of sheaves of rings, the pair `(f, g)` is a pair of lifts, and its descended
difference is `θ` again.

So, at the level of comorphisms, the correspondence of [Stacks Project, Tag 0618] is a
bijection between the `𝒪_X`-linear maps `a^*Ω_{Y/T} ⟶ C` and the lifts with first member `f`.

## Main definitions

* `Stacks.Sites.derivationActionRingHom`: the modified lift `g = f − ι ∘ D ∘ q` on the sections
  over one object, and `Stacks.Sites.derivationActionHom`: the same as a morphism of sheaves of
  rings.
* `Stacks.Sites.derivationActionData`: the pair `(f, g)`, as a
  `Stacks.Sites.LiftDifferenceData`.
* `AlgebraicGeometry.Space.liftDifferenceDataOfHom`: that pair in the geometric situation, with
  `D` the derivation attached to a given `θ` by Equation [Stacks Project, Tag 0619].

## Main results

* `Stacks.Sites.derivationActionData_diff`: the sectionwise difference of the pair is `D ∘ q`.
* `Stacks.Sites.derivationActionData_descend`: its descent along `q` is `D` itself.
* `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_liftDifferenceDataOfHom`: the
  descended difference of the pair is the given `θ`.
* `AlgebraicGeometry.Space.exists_liftDifferenceData_liftDifferenceDifferentialsHom_eq`: every
  `θ` is the descended difference of a pair of lifts whose first member is the given one.

## Implementation notes

**Why the sum can be formed here.**  Forming the sum `(a')^♯ + D` of
[Stacks Project, Tag 04D0] on the small étale site of `X'` asks for the ambient sheaves of its
two summands to be identified, which is the structure-sheaf half of
[Stacks Project, Tag 05ZM].  That identification is available: it is
`AlgebraicGeometry.Space.conormalAmbientSquareZeroValues` of
`Thickenings/ConormalAmbientSquareZeroValues.lean`, and the sum there is
`AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom`.  The point
is that the obstruction is absent *in the present setting* without any such transport: a
`Stacks.Sites.LiftDifferenceData` reads both of its maps in *one* ambient sheaf of rings
`E.ambient` to begin with, and the module of values is included in that same sheaf by the field
`ι` of `Stacks.Sites.SquareZeroValues`.  So the sum is an honest sectionwise operation, and what
has to be checked is only that it is multiplicative.

**Where the square-zero hypothesis is spent.**  In exactly one place, the cross term of
`map_mul'`: the product `ι (D (q x)) * ι (D (q y))` of two sections of the ideal of values
vanishes by `Stacks.Sites.SquareZeroValues.mul_ι_eq_zero`.  The two surviving correction terms
are the two halves of the Leibniz rule for `D`, after the `𝒪_Y`-action on the module is
rewritten as multiplication by `f` through the field `ι_smul`; the commutativity of the sections
of the ambient sheaf is used to put the second of them on the correct side.

**The sign.**  The modified map is `f − ι ∘ D ∘ q` rather than `f + ι ∘ D ∘ q` so that the
difference of the pair `(f, g)` is `D ∘ q` on the nose rather than its negative, matching the
field `ι_diff` of `Stacks.Sites.LiftDifferenceData`, which is `ι (diff x) = f x − g x`.

**Hypothesis (2) of [Stacks Project, Tag 0618] is free here.**  The two maps agree on every
section killed by `q`, because the correction term is read off `q x` and an additive map kills
the zero section.  No generating family is needed, so
`Stacks.Sites.app_eq_of_app_eq_zero_of_mem_span` is not used.

**Every section-indexed family here is quantified over an explicit argument.**  `D` is
`∀ V, 𝒪_Y(V) →+ M(V)`, and the hypothesis `ι_smul` likewise names its object; neither index is
implicit.  With implicit indices the terms are eta-expanded when they are passed to a
definition, and the geometric instance of that definition is then a deterministic `whnf`
timeout at the sections of the small étale structure sheaf.  The bundled
`PresheafOfModules.Derivation'` of Equation (0619) has its index implicit, so the geometric
layer repackages it once, as `AlgebraicGeometry.Space.derivationFamilyOfHom`, and restates its
three laws there; the field `ι_smul` of `Stacks.Sites.LiftDifferenceData`, whose index is
implicit, is filled in from the explicit form.

**The descent is the given derivation.**  The descended family is only known to compute the
difference on the sections in the image of `q`; that it is `D` everywhere is a local statement,
settled on the image sieve of a section by separatedness of the module, exactly as the Leibniz
rule `Stacks.Sites.QuotientDerivation.descend_mul` is.

## What this does not give

The conclusion is about the *comorphism* `g`, not about a morphism of algebraic spaces inducing
it.  Recovering a morphism of algebraic spaces from its comorphism is the full faithfulness of
Properties of Spaces, Theorem [Stacks Project, Tag 04KL], which this development has as
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` — a theorem for a base scheme whose
canonical morphism `S ⟶ Spec Γ(S, ⊤)` is a monomorphism, so for an affine or quasi-affine base,
and open for a general one; nothing here uses, proves or weakens it.  Over an *affine* chart
no such input is needed, a morphism into an affine scheme being
determined by its map of global sections (`Stacks.Thickenings.homOfAppTop`); turning the
comorphism produced here into a morphism that way is not done here either, and needs the
comparison of the sections of the sheaves above with the global sections of the charts.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v₁ u₁

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A O : Sheaf J RingCat.{u}} {q : A ⟶ O} {M : SheafOfModules.{u} O}
  (E : SquareZeroValues M) (f : A ⟶ E.ambient)
  (D : ∀ V : Cᵒᵖ, O.obj.obj V →+ M.val.obj V)
  (hmul : ∀ (V : Cᵒᵖ) (s t : O.obj.obj V), D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : Cᵒᵖ) (h : V ⟶ W) (s : O.obj.obj V),
    D W (O.obj.map h s) = M.val.map h (D V s))
  (ι_smul : ∀ (V : Cᵒᵖ) (x : A.obj.obj V) (m : M.val.obj V),
    E.ι (q.hom.app V x • m) = f.hom.app V x * E.ι m)

/-- A derivation kills the unit section: the Leibniz rule at `1 * 1`. -/
theorem derivationFamily_one_eq_zero
    (hmul : ∀ (V : Cᵒᵖ) (s t : O.obj.obj V), D V (s * t) = s • D V t + t • D V s)
    (V : Cᵒᵖ) : D V 1 = 0 := by
  simpa using hmul V 1 1

/-- **The lift modified by a derivation, on the sections over one object.**  For a lift
`f : A ⟶ 𝒜` and a derivation `D` of `𝒪_Y` with values in the square-zero ideal of values, the
sectionwise difference `x ↦ f x − ι (D (q x))` is a ring homomorphism.  The square-zero
hypothesis is spent on the cross term of `map_mul'`. -/
noncomputable def derivationActionRingHom (V : Cᵒᵖ) :
    A.obj.obj V →+* E.ambient.obj.obj V where
  toFun x := f.hom.app V x - E.ι (D V (q.hom.app V x))
  map_zero' := by simp only [map_zero, sub_zero]
  map_add' x y := by
    simp only [map_add]
    abel
  map_one' := by
    simp only [map_one, derivationFamily_one_eq_zero D hmul V, map_zero, sub_zero]
  map_mul' x y := by
    have hzz : E.ι (D V (q.hom.app V x)) * E.ι (D V (q.hom.app V y)) = 0 :=
      E.mul_ι_eq_zero _ _
    simp only [map_mul, hmul, map_add, ι_smul V,
      E.ambient_mul_comm (f.hom.app V y) (E.ι (D V (q.hom.app V x)))]
    rw [sub_mul, mul_sub, mul_sub, hzz]
    abel

/-- The value of `Stacks.Sites.derivationActionRingHom`. -/
theorem derivationActionRingHom_apply (V : Cᵒᵖ) (x : A.obj.obj V) :
    derivationActionRingHom E f D hmul ι_smul V x =
      f.hom.app V x - E.ι (D V (q.hom.app V x)) := rfl

/-- **The lift modified by a derivation.**  This is the map `(a')^♯ + D` of the proof of
[Stacks Project, Tag 02H5], formed in the one ambient sheaf of rings in which both maps of a
`Stacks.Sites.LiftDifferenceData` are read. -/
noncomputable def derivationActionHom : A ⟶ E.ambient :=
  ⟨{ app := fun V => RingCat.ofHom (derivationActionRingHom E f D hmul ι_smul V)
     naturality := fun V W h => RingCat.hom_ext (RingHom.ext fun x => by
       change f.hom.app W (A.obj.map h x) - E.ι (D W (q.hom.app W (A.obj.map h x))) =
         E.ambient.obj.map h (f.hom.app V x - E.ι (D V (q.hom.app V x)))
       rw [map_sub, NatTrans.naturality_apply f.hom h x,
         NatTrans.naturality_apply q.hom h x, hmap, E.ι_map]) }⟩

/-- The value of `Stacks.Sites.derivationActionHom` on sections. -/
@[simp]
theorem derivationActionHom_app_apply (V : Cᵒᵖ) (x : A.obj.obj V) :
    (derivationActionHom E f D hmul hmap ι_smul).hom.app V x =
      f.hom.app V x - E.ι (D V (q.hom.app V x)) := rfl

/-- **The pair of lifts whose difference is a prescribed derivation.**  The given lift and the
lift it is moved to by `D`, as a `Stacks.Sites.LiftDifferenceData` for `q`.

Hypothesis (2) of [Stacks Project, Tag 0618] — that the two maps agree on the sections killed by
`q` — holds here with no generating family: the correction term is read off `q x`, and an
additive map kills the zero section. -/
noncomputable def derivationActionData : LiftDifferenceData q E where
  f := f
  g := derivationActionHom E f D hmul hmap ι_smul
  ι_smul {V} x m := ι_smul V x m
  diff {V} x := D V (q.hom.app V x)
  ι_diff {V} x := by
    rw [derivationActionHom_app_apply, sub_sub_cancel]
  app_eq_of_app_eq_zero {V} x hx := by
    rw [derivationActionHom_app_apply, hx, map_zero, map_zero, sub_zero]

/-- The sectionwise difference of the pair `(f, f − ι ∘ D ∘ q)` is `D ∘ q`. -/
@[simp]
theorem derivationActionData_diff (V : Cᵒᵖ) (x : A.obj.obj V) :
    (derivationActionData E f D hmul hmap ι_smul).diff x = D V (q.hom.app V x) := rfl

/-- The first map of the pair is the given lift. -/
theorem derivationActionData_f :
    (derivationActionData E f D hmul hmap ι_smul).f = f := rfl

/-- **The descent of the difference of the pair is the given derivation.**  The descended family
computes the difference on the sections in the image of `q`, which is `D` there; both sides are
sections of a sheaf, so they agree on the image sieve of a section and hence everywhere. -/
theorem derivationActionData_descend [HasSheafify J AddCommGrpCat.{u}]
    [Sheaf.IsLocallySurjective q] (V : Cᵒᵖ) (t : O.obj.obj V) :
    (derivationActionData E f D hmul hmap ι_smul).toQuotientDerivation.descend t = D V t := by
  have hsep : Presheaf.IsSeparated J M.val.presheaf := M.isSheaf.isSeparated
  refine hsep V.unop (Presheaf.imageSieve q.hom t)
    (Presheaf.imageSieve_mem J q.hom t) _ _ ?_
  rintro Y p ⟨x, hx⟩
  change M.val.map p.op
      ((derivationActionData E f D hmul hmap ι_smul).toQuotientDerivation.descend t) =
    M.val.map p.op (D V t)
  rw [← QuotientDerivation.descend_map, ← hmap, ← hx, QuotientDerivation.descend_app]
  rfl

end Stacks.Sites

namespace AlgebraicGeometry.Space

open Stacks.Sites

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y T : AlgebraicSpaces B S hS} (b : Y ⟶ T)
  {A : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
  {q : A ⟶ structureRingSheaf B S hS Y} [Sheaf.IsLocallySurjective q]
  {X : AlgebraicSpaces B S hS} (a : X ⟶ Y) (C : Modules B S hS X.1 X.2)
  {E : SquareZeroValues ((modulePushforward B S hS a).obj C)}
  (f : A ⟶ E.ambient)
  (ι_smul : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ) (x : A.obj.obj V)
    (m : ((modulePushforward B S hS a).obj C).val.obj V),
    E.ι (@HSMul.hSMul
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj V)
      _ _ _ (q.hom.app V x) m) = f.hom.app V x * E.ι m)
  (θ : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ C)

/-- **The derivation attached to `θ` by Equation [Stacks Project, Tag 0619]**, as a family
indexed by an *explicit* argument.  The bundled `PresheafOfModules.Derivation'` has its index
implicit, and leaving it to unification against the sections of the structure sheaf of the small
étale site is a `whnf` timeout; pinning it here spends that defeq once. -/
noncomputable def derivationFamilyOfHom (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    (structureRingSheaf B S hS Y).obj.obj V →+
      ((modulePushforward B S hS a).obj C).val.obj V :=
  (derivationDirectImageEquiv B S hS a b C θ).d (X := V)

/-- The Leibniz rule for `AlgebraicGeometry.Space.derivationFamilyOfHom`. -/
theorem derivationFamilyOfHom_mul (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s t : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
      V) :
    derivationFamilyOfHom B S hS b a C θ V (s * t) =
      s • derivationFamilyOfHom B S hS b a C θ V t +
        t • derivationFamilyOfHom B S hS b a C θ V s :=
  (derivationDirectImageEquiv B S hS a b C θ).d_mul s t

/-- `AlgebraicGeometry.Space.derivationFamilyOfHom` commutes with restriction. -/
theorem derivationFamilyOfHom_map (V W : (SmallEtale B S hS Y.1)ᵒᵖ) (h : V ⟶ W)
    (s : (structureRingSheaf B S hS Y).obj.obj V) :
    derivationFamilyOfHom B S hS b a C θ W ((structureRingSheaf B S hS Y).obj.map h s) =
      ((modulePushforward B S hS a).obj C).val.map h
        (derivationFamilyOfHom B S hS b a C θ V s) :=
  (derivationDirectImageEquiv B S hS a b C θ).d_map h s

/-- `AlgebraicGeometry.Space.derivationFamilyOfHom` kills the sections read from the base. -/
theorem derivationFamilyOfHom_app (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj V) :
    derivationFamilyOfHom B S hS b a C θ V
      ((structureSharpInverseImage B S hS b).hom.app V s) = 0 :=
  (derivationDirectImageEquiv B S hS a b C θ).d_app s

/-- The pair of lifts attached to an `𝒪_X`-linear map `θ : a^*Ω_{Y/T} ⟶ C` and a lift `f`: the
second member is `f − ι ∘ D ∘ q` for `D = d_{Y/T} ∘ θ` the `𝒪_T`-derivation of `𝒪_Y` attached to
`θ` by Equation [Stacks Project, Tag 0619]. -/
noncomputable def liftDifferenceDataOfHom : LiftDifferenceData q E :=
  derivationActionData (J := SmallEtale.topology B S hS Y.1) (A := A)
    (O := structureRingSheaf B S hS Y) (q := q)
    (M := (modulePushforward B S hS a).obj C) E f
    (derivationFamilyOfHom B S hS b a C θ)
    (derivationFamilyOfHom_mul B S hS b a C θ)
    (derivationFamilyOfHom_map B S hS b a C θ) ι_smul

omit [Sheaf.IsLocallySurjective q] in
/-- The first map of `AlgebraicGeometry.Space.liftDifferenceDataOfHom` is the given lift. -/
theorem liftDifferenceDataOfHom_f :
    (liftDifferenceDataOfHom B S hS b a C f ι_smul θ).f = f := rfl

/-- The descent of the difference of `AlgebraicGeometry.Space.liftDifferenceDataOfHom` is the
derivation attached to `θ`. -/
private theorem liftDifferenceDataOfHom_descend_apply
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) (t : (structureRingSheaf B S hS Y).obj.obj V) :
    (liftDifferenceDataOfHom B S hS b a C f ι_smul θ).toQuotientDerivation.descend t =
      derivationFamilyOfHom B S hS b a C θ V t :=
  derivationActionData_descend (J := SmallEtale.topology B S hS Y.1) (A := A)
    (O := structureRingSheaf B S hS Y) (q := q)
    (M := (modulePushforward B S hS a).obj C) E f
    (derivationFamilyOfHom B S hS b a C θ)
    (derivationFamilyOfHom_mul B S hS b a C θ)
    (derivationFamilyOfHom_map B S hS b a C θ) ι_smul V t

/-- The descended difference of `AlgebraicGeometry.Space.liftDifferenceDataOfHom` kills the
sections read from the base: the derivation attached to `θ` does, which is the field `d_app` of
Equation [Stacks Project, Tag 0619]. -/
theorem liftDifferenceDataOfHom_descend_eq_zero
    (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj V) :
    (liftDifferenceDataOfHom B S hS b a C f ι_smul θ).toQuotientDerivation.descend
      ((structureSharpInverseImage B S hS b).hom.app V s) = 0 :=
  (liftDifferenceDataOfHom_descend_apply B S hS b a C f ι_smul θ V _).trans
    (derivationFamilyOfHom_app B S hS b a C θ V s)

/-- **The descended difference of the modified pair is the given linear map.**  For every
`𝒪_X`-linear map `θ : a^*Ω_{Y/T} ⟶ C` the pair of lifts
`AlgebraicGeometry.Space.liftDifferenceDataOfHom` has descended difference `θ`.

With `AlgebraicGeometry.Space.liftDifferenceDifferentialsHom_eq_zero_iff` — which says that two
lifts with the same descended difference have the same comorphism — this is the bijectivity of
the correspondence of [Stacks Project, Tag 0618] at the level of comorphisms, for the pairs of
lifts with a fixed first member. -/
theorem liftDifferenceDifferentialsHom_liftDifferenceDataOfHom :
    liftDifferenceDifferentialsHom B S hS b a C
        (liftDifferenceDataOfHom B S hS b a C f ι_smul θ)
        (liftDifferenceDataOfHom_descend_eq_zero B S hS b a C f ι_smul θ) = θ := by
  refine (eq_descendedDifferentialsHom B S hS b a C
    (liftDifferenceDataOfHom B S hS b a C f ι_smul θ).toQuotientDerivation
    (liftDifferenceDataOfHom_descend_eq_zero B S hS b a C f ι_smul θ) θ ?_).symm
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext V t
  exact (liftDifferenceDataOfHom_descend_apply B S hS b a C f ι_smul θ V t).symm

include ι_smul in
/-- **Every `𝒪_X`-linear map `a^*Ω_{Y/T} ⟶ C` is the descended difference of a pair of lifts
whose first member is the given one.**  This is the existence half of
[Stacks Project, Tag 0618] at the level of comorphisms: the correspondence `g ↦ θ` is onto. -/
theorem exists_liftDifferenceData_liftDifferenceDifferentialsHom_eq :
    ∃ (L : LiftDifferenceData q E) (hz : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ)
        (s : (inverseImageStructureSheaf B S hS b).obj.obj V),
        L.toQuotientDerivation.descend
          ((structureSharpInverseImage B S hS b).hom.app V s) = 0),
      L.f = f ∧ liftDifferenceDifferentialsHom B S hS b a C L hz = θ :=
  ⟨liftDifferenceDataOfHom B S hS b a C f ι_smul θ,
    liftDifferenceDataOfHom_descend_eq_zero B S hS b a C f ι_smul θ, rfl,
    liftDifferenceDifferentialsHom_liftDifferenceDataOfHom B S hS b a C f ι_smul θ⟩

end AlgebraicGeometry.Space

end
