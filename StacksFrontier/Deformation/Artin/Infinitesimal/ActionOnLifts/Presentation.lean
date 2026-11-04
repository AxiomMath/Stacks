module

public import StacksFrontier.Deformation.Artin.Infinitesimal.Functoriality

/-!
# The difference construction at a deformation situation

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` satisfying
the Rim–Schlessinger condition (RS*), let `A` be an `S`-algebra whose spectrum lies in the
site, and let `x` be an object of `𝒳` over `Spec A`. Let `A' → A` be a surjection of
`S`-algebras with square-zero kernel `I`, again with `Spec A'` in the site: a *deformation
situation* for `x`.

Two lifts of `x` over `Spec A'` differ by an element of `A[I]`: the self-fibre product
`A' ×_A A'` is canonically isomorphic to `A' ×_A A[I]`, and (RS*) turns both fibre products
into two-fold products of lifts. That is the *difference construction*, and this file draws
from it the two assertions of Stacks 07Y9 that concern a general deformation situation.

Part (2)(b): the tangent module `T_x(I)` acts on the set `Lift(x, A')` of isomorphism
classes of lifts of `x` over `Spec A'`, simply transitively as soon as there is a lift.

Part (1): the module `Inf_x(I)` of infinitesimal automorphisms of the trivial deformation
of `x` over `A[I]` is isomorphic, as a group, to the group `Inf(x'/x)` of infinitesimal
automorphisms of a chosen lift `x'` of `x` over `Spec A'`.

## Main definitions

* `Deformation.Artin.liftClassesOver` — the isomorphism classes of lifts of `x` along an
  arrow out of `Spec A`.
* `Deformation.Artin.IsGeometricDifference` — the difference of two lift classes: glue the
  two lifts over `A' ×_A A'`, transport across the canonical ring isomorphism
  `A' ×_A A' ≅ A' ×_A A[I]`, and read off the component over `A[I]`.
* `Deformation.Artin.ActionOnLiftsData` — the action of `T_x(I)` on `Lift(x, A')`, together
  with the difference map that pins it and the bijectivity of its orbit maps.
* `Deformation.Artin.IsGeometricInfDifference` — the same difference construction for
  infinitesimal automorphisms: an automorphism of the glueing of a lift with itself which is
  the identity on the first factor matches an automorphism of the lift with one of the
  trivial deformation over `A[I]`.
* `Deformation.Artin.InfComparisonData` — the comparison of `Inf_x(I)` with the
  infinitesimal automorphisms of a lift, the two laws making it an isomorphism of groups,
  and the geometric difference that pins it.

## Main results

* `Deformation.Artin.isSiteModule_kernel` — the kernel of a square-zero surjection whose
  source lies in the site is a module whose trivial square-zero extension lies in the site,
  so `T_x(I)` and `Inf_x(I)` are defined with no further size hypothesis.
* `Deformation.Artin.exists_actionOnLifts` — **Stacks 07Y9 part (2)(b)**, the action exists.
  Every orbit map is bijective, so the action is simply transitive whenever `Lift(x, A')` is
  nonempty.
* `Deformation.Artin.exists_infComparison` — **Stacks 07Y9 part (1)** at a general
  deformation situation: `Inf_x(I)` is the group of infinitesimal automorphisms of a lift.

## Implementation notes

The action of part (2)(b) is produced as data rather than merely asserted to exist: a bare
assertion that some simply transitive action exists says only that the set of lifts is empty
or in bijection with the module, and would be satisfied by an arbitrary torsor structure (for
instance the reversed one). The field `ActionOnLiftsData.difference_geometric` pins the
difference map geometrically, and `ActionOnLiftsData.action_difference` then determines the
action from the difference.

Deformation situations are presented by `Deformation.Artin.AffineDeformation`: an affine
object of the site over `S` whose global sections are a given ring, together with the arrow
from `Spec A` realizing the augmentation. Fibre products over `A` and trivial square-zero
extensions of such presentations are assembled by `Deformation.Artin.BasedRing`, the
`A'`-algebras augmented to `A`; condition (RS*) says exactly that lifts over a fibre product
are pairs of lifts, which is `Deformation.Artin.BasedRing.pair_bijective` on isomorphism
classes and `Deformation.Artin.end_pair_bijective` on infinitesimal automorphisms.

Additivity of the difference of lift classes — the cocycle rule making the action an action —
comes from the triple fibre product `A' ×_A A' ×_A A'`: the two outer differences and the
total difference are the three components of one map to `A[I × I] → A[I]`, and the tangent
functor is additive.

For part (1) no triple product is needed: the comparison is multiplicative because the two
(RS*) product decompositions of the automorphisms of the glueing are, and the glueing used
is the restriction of `x'` along the *diagonal* of `A' ×_A A'`, whose difference component is
the structural map `A' → A → A[I]` — so the `A[I]`-factor of the glueing is the trivial
deformation on the nose (`Deformation.Artin.BasedRing.delta_comp_diag`). That the module
structure of Stacks 06I6 on `Inf_x(M)` is composition of automorphisms is an Eckmann–Hilton
argument, `Deformation.Artin.map_add_of_interchange`.

## File layout

This is the first of three files, re-exported together by
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts`. It contains the torsor presented by its
difference map, deformation situations in the site, the lift classes, and the presentations
`Deformation.Artin.AffineDeformation` and `Deformation.Artin.BasedRing` up to
`Deformation.Artin.BasedRing.pair_bijective`. The square-zero extensions, the difference map
and the action of `T_x(I)` follow in
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.LiftAction`, and the comparison of
`Inf_x(I)` with `Inf(x'/x)` in
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts.InfComparison`.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] Deformation.Artin.squareZeroRing
  CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Under.post

universe u v w

namespace Deformation.Artin

/-! ### A torsor presented by its difference map -/

private structure LiftDifference (V Y : Type*) [AddGroup V] where
  difference : Y → Y → V
  difference_self : ∀ y, difference y y = 0
  difference_trans : ∀ y₁ y₂ y₃,
    difference y₁ y₂ + difference y₂ y₃ = difference y₁ y₃
  difference_existsUnique : ∀ y a, ∃! y', difference y' y = a

private noncomputable def LiftDifference.action {V Y : Type*} [AddGroup V]
    (D : LiftDifference V Y) : V → Y → Y :=
  fun a y => Classical.choose (D.difference_existsUnique y a)

private theorem LiftDifference.action_difference {V Y : Type*} [AddGroup V]
    (D : LiftDifference V Y) (a : V) (y : Y) :
    D.difference (D.action a y) y = a :=
  (Classical.choose_spec (D.difference_existsUnique y a)).1

/-- An element `y'` with `difference y' y = a` is the translate of `y` by `a`. -/
private theorem LiftDifference.action_eq_of_difference {V Y : Type*} [AddGroup V]
    (D : LiftDifference V Y) {a : V} {y y' : Y} (h : D.difference y' y = a) :
    D.action a y = y' :=
  ((Classical.choose_spec (D.difference_existsUnique y a)).2 y' h).symm

private theorem LiftDifference.action_zero {V Y : Type*} [AddGroup V]
    (D : LiftDifference V Y) (y : Y) : D.action 0 y = y :=
  D.action_eq_of_difference (D.difference_self y)

private theorem LiftDifference.action_add {V Y : Type*} [AddGroup V]
    (D : LiftDifference V Y) (a b : V) (y : Y) :
    D.action (a + b) y = D.action a (D.action b y) :=
  D.action_eq_of_difference <| by
    rw [← D.difference_trans _ (D.action b y), D.action_difference, D.action_difference]

private theorem LiftDifference.action_bijective {V Y : Type*} [AddGroup V]
    (D : LiftDifference V Y) (y : Y) :
    Function.Bijective (fun a : V => D.action a y) := by
  refine ⟨fun a b hab => ?_, fun y' => ⟨D.difference y' y, D.action_eq_of_difference rfl⟩⟩
  simpa only [D.action_difference] using congrArg (fun y' => D.difference y' y) hab

private def equivFromPairCoordinates {Y V Z : Type*}
    (e : Z ≃ Y × Y) (f : Z ≃ Y × V)
    (hfst : ∀ z, (e z).1 = (f z).1) (y₀ : Y) : Y ≃ V := by
  let P := e.symm.trans f
  have hP : ∀ z, (P z).1 = z.1 := by
    intro z
    calc
      (P z).1 = (f (e.symm z)).1 := rfl
      _ = (e (e.symm z)).1 := (hfst (e.symm z)).symm
      _ = z.1 := congrArg Prod.fst (e.apply_symm_apply z)
  refine
    { toFun := fun y => (P (y₀, y)).2
      invFun := fun v => (P.symm (y₀, v)).2
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    have hpair : P (y₀, y) = (y₀, (P (y₀, y)).2) :=
      Prod.ext (hP (y₀, y)) rfl
    change (P.symm (y₀, (P (y₀, y)).2)).2 = y
    rw [← hpair]
    exact congrArg Prod.snd (P.symm_apply_apply (y₀, y))
  · intro v
    have hpair : P.symm (y₀, v) = (y₀, (P.symm (y₀, v)).2) := by
      apply Prod.ext
      · have hp := hP (P.symm (y₀, v))
        have hq := congrArg Prod.fst (P.apply_symm_apply (y₀, v))
        exact hp.symm.trans hq
      · rfl
    change (P (y₀, (P.symm (y₀, v)).2)).2 = v
    rw [← hpair]
    exact congrArg Prod.snd (P.apply_symm_apply (y₀, v))

/-! ### Deformation situations in the site -/

section Deformations

variable (A : Type u) [CommRing A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-- The kernel of a square-zero surjection `q : A' → A` whose source lies in the chosen big
site is a module whose trivial square-zero extension again lies in the site: `A[I]` is
`A × I` with `#A ≤ #A'` and `#I ≤ #A'`, so `#A[I] ≤ max ℵ₀ #A'`, and the cutoff is a strong
prelimit above `ℵ₀`. Consequently the tangent module at the kernel of a deformation
situation is defined with no further size hypothesis. -/
public theorem isSiteModule_kernel {A' : Type u} [CommRing A']
    (hA' : B.Contains (Spec (.of A'))) (q : A' →+* A) (hq : Function.Surjective q)
    [Module A (RingHom.ker q)] : IsSiteModule A B (ModuleCat.of A (RingHom.ker q)) := by
  let : Module Aᵐᵒᵖ (RingHom.ker q) := oppositeModule A (ModuleCat.of A (RingHom.ker q))
  let : IsCentralScalar A (RingHom.ker q) := centralScalar A (ModuleCat.of A (RingHom.ker q))
  show (Spec (.of (TrivSqZeroExt A (RingHom.ker q)))).size < B.cutoff
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hA' ?_
  have hmk : Cardinal.mk (TrivSqZeroExt A (RingHom.ker q)) =
      Cardinal.mk (A × (RingHom.ker q)) := rfl
  rw [hmk, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc Cardinal.mk A * Cardinal.mk (RingHom.ker q)
      ≤ max Cardinal.aleph0 (Cardinal.mk A') * max Cardinal.aleph0 (Cardinal.mk A') :=
        mul_le_mul' ((Cardinal.mk_le_of_surjective hq).trans (le_max_right _ _))
          ((Cardinal.mk_le_of_injective Subtype.val_injective).trans (le_max_right _ _))
    _ = max Cardinal.aleph0 (Cardinal.mk A') := Cardinal.mul_eq_self (le_max_left _ _)

/-- **The Rim–Schlessinger comparison for affine objects over `S`.** The four corners are
arbitrary objects of the big fppf category over `S` whose underlying schemes are affine, so
the statement applies directly to the presentations of a deformation situation. -/
public theorem exists_squareZeroLiftEquivalenceOnBigFppfOver
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
    (U V W Z : BigFppfOver B S hS)
    [hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    [hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    (hpb : IsPullback ((BigFppfOver.toScheme B S hS).map i).appTop
      ((BigFppfOver.toScheme B S hS).map j).appTop
      ((BigFppfOver.toScheme B S hS).map f).appTop
      ((BigFppfOver.toScheme B S hS).map g).appTop)
    (hsurj : Function.Surjective (((BigFppfOver.toScheme B S hS).map g).appTop.hom))
    (hsq : RingHom.ker (((BigFppfOver.toScheme B S hS).map g).appTop.hom) ^ 2 = ⊥) :
    letI : p.IsFibered := hp.isFibered
    let c := Functor.chosenPullbacks p
    ∀ y : p.Fiber U,
      ∃ E : Functor.IsoFiber (c.pullbackFunctor (f ≫ i)) y ≌
          (Functor.IsoFiber (c.pullbackFunctor f) y ×
            Functor.IsoFiber (c.pullbackFunctor g) y),
        (∀ t,
          ((E.functor.obj t).1).1.left = (c.pullbackFunctor i).obj t.1.left ∧
          ((E.functor.obj t).2).1.left = (c.pullbackFunctor j).obj t.1.left) ∧
        (∀ t t' (m : t ⟶ t'),
          HEq ((E.functor.map m).1.1.left) ((c.pullbackFunctor i).map m.1.left) ∧
          HEq ((E.functor.map m).2.1.left) ((c.pullbackFunctor j).map m.1.left)) ∧
        (∀ t,
          HEq ((E.functor.obj t).1).1.hom
            (((c.pullbackFunctorCompIso f i).symm.app t.1.left).hom ≫ t.1.hom) ∧
          HEq ((E.functor.obj t).2).1.hom
            (((c.pullbackFunctorCompIso g j).symm.app t.1.left).hom ≫
              eqToHom (congrArg (fun k => (c.pullbackFunctor k).obj t.1.left)
                (show g ≫ j = f ≫ i from h.symm)) ≫
              t.1.hom)) :=
  exists_squareZeroLiftEquivalence hp hRS ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ ⟨Z, hZ⟩
    (ObjectProperty.homMk f) (ObjectProperty.homMk g) (ObjectProperty.homMk i)
    (ObjectProperty.homMk j) (ObjectProperty.hom_ext _ h) hpb hsurj hsq

private theorem specContainsOfCardinalBound
    (R Q : Type u) [CommRing R] [CommRing Q]
    (hQ : B.Contains (Spec (.of Q)))
    (hbound : Cardinal.mk R ≤ max Cardinal.aleph0 (Cardinal.mk Q)) :
    B.Contains (Spec (.of R)) := by
  show (Spec (.of R)).size < B.cutoff
  exact Scheme.size_Spec_lt_of_mk_le_max (R := Q) B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hQ hbound


private theorem ringPullbackIsPullback
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* T) (g : S →+* T) :
    IsPullback
      (CommRingCat.ofHom (RingHom.pullbackFst f g))
      (CommRingCat.ofHom (RingHom.pullbackSnd f g))
      (CommRingCat.ofHom f) (CommRingCat.ofHom g) := by
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  apply (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact congrArg (fun h : f.pullback g →+* T => h x)
      (RingHom.pullback_comm_sq f g)
  · intro x y hxy
    have hfst' := hxy.1
    have hsnd' := hxy.2
    have hfst : x.1.1 = y.1.1 := by
      change x.1.1 = y.1.1 at hfst'
      exact hfst'
    have hsnd : x.1.2 = y.1.2 := by
      change x.1.2 = y.1.2 at hsnd'
      exact hsnd'
    apply Subtype.ext
    apply Prod.ext
    · exact hfst
    · exact hsnd
  · intro x y hxy
    refine ⟨⟨(x, y), hxy⟩, ?_, ?_⟩ <;> rfl

/-- Isomorphism classes of lifts of `x` along an arrow out of `Spec A`. -/
public abbrev liftClassesOver {U : BigFppfOver B S hS}
    (g : algebraOver A B S hS toS hA ⟶ U) : Type _ :=
  Quotient (isIsomorphicSetoid
    ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ g))))

/-- The difference of two lifts is the square-zero lift obtained by first
gluing them over `A' ×ₐ A'`, then transporting across the canonical ring
isomorphism `A' ×ₐ A' ≃ A' ×ₐ A[I]`, and finally restricting to `A[I]`.
The first projection gives `z₂` and the second gives `z₁`, so the difference
of `z₁` from `z₂` has the source's second-minus-first sign. -/
public def IsGeometricDifference
    (T : TangentFunctorData A B S hS toS hA p x hx)
    (A' : Type u) [CommRing A']
    (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS)
    (q : A' →+* A) (hq : Function.Surjective q)
    (hsq : (RingHom.ker q) ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶
      (Over.mk toS' : BigFppfOver B S hS))
    (hI : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      IsSiteModule A B
        (ModuleCat.of A (RingHom.ker q)))
    (z₁ z₂ : liftClassesOver A B S hS toS hA p x hx g)
    (a : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (T.functor.obj ⟨ModuleCat.of A (RingHom.ker q), hI⟩ : Type _)) : Prop :=
  letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let M : SiteModule A B :=
    ⟨ModuleCat.of A (RingHom.ker q), hI⟩
  letI : Module Aᵐᵒᵖ (RingHom.ker q) :=
    oppositeModule A (ModuleCat.of A (RingHom.ker q))
  letI : IsCentralScalar A (RingHom.ker q) :=
    centralScalar A (ModuleCat.of A (RingHom.ker q))
  let Q := q.pullback ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom)
  ∃ (hP : B.Contains (Spec (.of (q.pullback q))))
    (hQ : B.Contains (Spec (.of Q)))
    (toSP : B.obj hP ⟶ B.obj hS)
    (toSQ : B.obj hQ ⟶ B.obj hS)
    (r₁ r₂ : (Over.mk toS' : BigFppfOver B S hS) ⟶ Over.mk toSP)
    (s : squareZeroOver A B S hS toS M ⟶ Over.mk toSQ)
    (e : (Over.mk toSQ : BigFppfOver B S hS) ≅ Over.mk toSP)
    (er : (q.pullback q) ≃+* Q),
      B.inclusion.map r₁.left = Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ∧
      B.inclusion.map r₂.left = Spec.map (CommRingCat.ofHom (q.pullbackSnd q)) ∧
      B.inclusion.map s.left =
        Spec.map (CommRingCat.ofHom
          (q.pullbackSnd ((TrivSqZeroExt.fstHom A A (RingHom.ker q)).toRingHom))) ∧
      B.inclusion.map e.hom.left =
        Spec.map (CommRingCat.ofHom er.toRingHom) ∧
      (∀ y : q.pullback q,
        (er y).1.1 = y.1.1 ∧
        (er y).1.2 =
          ((q y.1.1, kerDifference q y) :
            TrivSqZeroExt A (RingHom.ker q))) ∧
      ∃ (t₁ t₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ g)))
        (t : (Under.post p).Fiber
          (Under.mk (eqToHom hx ≫
            squareZeroArrow A B S hS toS hA M)))
        (v : X) (w : X)
        (φ₁ : t₁.1.right ⟶ v) (φ₂ : t₂.1.right ⟶ v)
        (ψ : t.1.right ⟶ w) (ε : w ⟶ v),
        Quotient.mk _ t₁ = z₁ ∧ Quotient.mk _ t₂ = z₂ ∧
        Quotient.mk _ t = T.liftEquiv M a ∧
        p.IsStronglyCartesian r₂ φ₁ ∧ p.IsStronglyCartesian r₁ φ₂ ∧
        p.IsStronglyCartesian s ψ ∧ p.IsStronglyCartesian e.hom ε ∧
        t₁.1.hom ≫ φ₁ = t₂.1.hom ≫ φ₂ ∧
        t.1.hom ≫ ψ ≫ ε = t₁.1.hom ≫ φ₁

/-- A tangent action on the classes of lifts to a square-zero thickening.
The orbit map at each lift is a bijection. -/
public structure ActionOnLiftsData
    (T : TangentFunctorData A B S hS toS hA p x hx)
    (A' : Type u) [CommRing A']
    (hA' : B.Contains (Spec (.of A')))
    (toS' : B.obj hA' ⟶ B.obj hS)
    (q : A' →+* A)
    (hq : Function.Surjective q)
    (hsq : (RingHom.ker q) ^ 2 = ⊥)
    (g : algebraOver A B S hS toS hA ⟶
      (Over.mk toS' : BigFppfOver B S hS)) where
  /-- The kernel of the deformation situation is a module of the site, so the tangent
  module at it is defined. -/
  kernelIsSiteModule :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    IsSiteModule A B
      (ModuleCat.of A (RingHom.ker q))
  action :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    (T.functor.obj ⟨ModuleCat.of A (RingHom.ker q), kernelIsSiteModule⟩ : Type _) →
      liftClassesOver A B S hS toS hA p x hx g →
        liftClassesOver A B S hS toS hA p x hx g
  difference :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    liftClassesOver A B S hS toS hA p x hx g →
      liftClassesOver A B S hS toS hA p x hx g →
        (T.functor.obj ⟨ModuleCat.of A (RingHom.ker q), kernelIsSiteModule⟩ : Type _)
  difference_geometric :
    ∀ z₁ z₂, IsGeometricDifference A B S hS toS hA p x hx T A' hA' toS'
      q hq hsq g kernelIsSiteModule z₁ z₂ (difference z₁ z₂)
  action_difference :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    ∀ a : (T.functor.obj
        ⟨ModuleCat.of A (RingHom.ker q), kernelIsSiteModule⟩ : Type _),
      ∀ z : liftClassesOver A B S hS toS hA p x hx g,
        difference (action a z) z = a
  zero_action :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    ∀ z : liftClassesOver A B S hS toS hA p x hx g, action 0 z = z
  add_action :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    ∀ a b : (T.functor.obj
        ⟨ModuleCat.of A (RingHom.ker q), kernelIsSiteModule⟩ : Type _),
      ∀ z : liftClassesOver A B S hS toS hA p x hx g,
        action (a + b) z = action a (action b z)
  orbit_bijective :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    ∀ z : liftClassesOver A B S hS toS hA p x hx g,
      Function.Bijective (fun a : (T.functor.obj
        ⟨ModuleCat.of A (RingHom.ker q), kernelIsSiteModule⟩ : Type _) => action a z)


private structure AffineDeformation where
  ring : CommRingCat.{u}
  contains : B.Contains (Spec ring)
  structureMap : B.obj contains ⟶ B.obj hS
  aug : ring →+* A
  arrow : algebraOver A B S hS toS hA ⟶
    Over.mk structureMap
  arrow_eq : B.inclusion.map arrow.left = Spec.map (CommRingCat.ofHom aug)

namespace AffineDeformation

variable {A B S hS toS hA}

private abbrev siteOver (D : AffineDeformation A B S hS toS hA) :=
  (Over.mk D.structureMap : BigFppfOver B S hS)

private abbrev under (D : AffineDeformation A B S hS toS hA) := Under.mk D.arrow

private abbrev Hom (D E : AffineDeformation A B S hS toS hA) := E.under ⟶ D.under

private def homMk {D E : AffineDeformation A B S hS toS hA}
    (f : D.ring →+* E.ring) (hf : E.aug.comp f = D.aug)
    (hs : Spec.map (CommRingCat.ofHom f) ≫ B.inclusion.map D.structureMap =
      B.inclusion.map E.structureMap) : Hom D E := by
  refine Under.homMk (Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom f))) (ObjectProperty.hom_ext _ hs)) ?_
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change B.inclusion.map E.arrow.left ≫ Spec.map (CommRingCat.ofHom f) =
    B.inclusion.map D.arrow.left
  rw [E.arrow_eq, D.arrow_eq]
  exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom E.aug)).symm.trans
    (congrArg Spec.map (CommRingCat.hom_ext hf))

private lemma hom_ext {D E : AffineDeformation A B S hS toS hA}
    {f g : Hom D E}
    (h : B.inclusion.map f.right.left = B.inclusion.map g.right.left) : f = g :=
  Under.UnderMorphism.ext (Over.OverMorphism.ext (ObjectProperty.hom_ext _ h))

private abbrev classes (D : AffineDeformation A B S hS toS hA) :=
  liftClassesOver A B S hS toS hA p x hx D.arrow

private def underMap {D E : AffineDeformation A B S hS toS hA} (f : Hom D E) :
    Under.mk (eqToHom hx ≫ E.arrow) ⟶ Under.mk (eqToHom hx ≫ D.arrow) :=
  Under.homMk f.right (by
    change (eqToHom hx ≫ E.arrow) ≫ f.right = eqToHom hx ≫ D.arrow
    rw [Category.assoc]
    exact congrArg (fun k => eqToHom hx ≫ k) (Under.w f))

variable (hp : p.IsFiberedInGroupoids)

private def map {D E : AffineDeformation A B S hS toS hA} (f : Hom D E) :
    classes p x hx D → classes p x hx E :=
  letI := underPost_isFibered p hp x
  (Under.post p).isoClassPresheaf.map (underMap p x hx f).op

private lemma map_comp {D E F : AffineDeformation A B S hS toS hA}
    (f : Hom D E) (g : Hom E F) (z : classes p x hx D) :
    map p x hx hp (g ≫ f) z = map p x hx hp g (map p x hx hp f z) := by
  let := underPost_isFibered p hp x
  show (Under.post p).isoClassPresheaf.map ((underMap p x hx g) ≫
    (underMap p x hx f)).op z = _
  exact ConcreteCategory.congr_hom
    ((Under.post p).isoClassPresheaf.map_comp (underMap p x hx f).op
      (underMap p x hx g).op) z

private lemma map_id (D : AffineDeformation A B S hS toS hA)
    (z : classes p x hx D) : map p x hx hp (𝟙 D.under) z = z := by
  let := underPost_isFibered p hp x
  show (Under.post p).isoClassPresheaf.map (𝟙 _) z = z
  simp

private def mapEquiv {D E : AffineDeformation A B S hS toS hA}
    (f : Hom D E) (g : Hom E D) (hf : g ≫ f = 𝟙 _) (hg : f ≫ g = 𝟙 _) :
    classes p x hx D ≃ classes p x hx E where
  toFun := map p x hx hp f
  invFun := map p x hx hp g
  left_inv z := by rw [← map_comp, hf, map_id]
  right_inv z := by rw [← map_comp, hg, map_id]

private lemma map_eq_of_lift {D E : AffineDeformation A B S hS toS hA}
    (f : Hom D E)
    (d : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow)))
    (e : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ E.arrow)))
    (φ : e.1.right ⟶ d.1.right) (hφ : p.IsStronglyCartesian f.right φ)
    (hw : e.1.hom ≫ φ = d.1.hom) :
    map p x hx hp f (Quotient.mk _ d) = Quotient.mk _ e := by
  let := underPost_isFibered p hp x
  let ψ : e.1 ⟶ d.1 := Under.homMk φ hw
  have hψ : (Under.post p).IsHomLift (underMap p x hx f) ψ := by
    refine IsHomLift.of_fac' _ _ _ e.2 d.2 ?_
    apply Under.UnderMorphism.ext
    have := hφ.toIsHomLift
    simpa [ψ, underMap, Under.post, Under.eqToHom_right] using
      IsHomLift.fac' p f.right φ
  let := hψ
  have hc := (underPost_isFiberedInGroupoids p hp x).isStronglyCartesian_homLift
    (underMap p x hx f) ψ
  exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian _ d e ψ hψ
    hc.isCartesian_of_isStronglyCartesian).symm

private lemma representative_map {D E : AffineDeformation A B S hS toS hA}
    (f : Hom D E)
    (d : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) :
    ∃ (e : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ E.arrow)))
      (φ : e.1.right ⟶ d.1.right),
      p.IsStronglyCartesian f.right φ ∧ e.1.hom ≫ φ = d.1.hom ∧
      map p x hx hp f (Quotient.mk _ d) = Quotient.mk _ e := by
  let := underPost_isFibered p hp x
  let c := Functor.chosenPullbacks (Under.post p : Under x ⥤ Under (p.obj x))
  let e := c.obj (underMap p x hx f) d
  let φ := c.map (underMap p x hx f) d
  have hφ : p.IsHomLift f.right φ.right :=
    underPost_isHomLift_right p (underMap p x hx f) φ
      (c.isStronglyCartesian (underMap p x hx f) d).toIsHomLift
  have hstrong := hp.isStronglyCartesian_homLift f.right φ.right
  exact ⟨e, φ.right, hstrong, Under.w φ,
    map_eq_of_lift p x hx hp f d e φ.right hstrong (Under.w φ)⟩

end AffineDeformation

namespace AffineDeformation

variable {A B S hS toS hA}

private lemma pair_bijective (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    (D E P : AffineDeformation A B S hS toS hA)
    (i : Hom P D) (j : Hom P E)
    (hpb : IsPullback
      ((BigFppfOver.toScheme B S hS).map i.right).appTop
      ((BigFppfOver.toScheme B S hS).map j.right).appTop
      (Spec.map (CommRingCat.ofHom D.aug)).appTop
      (Spec.map (CommRingCat.ofHom E.aug)).appTop)
    (hsurj : Function.Surjective E.aug) (hsq : (RingHom.ker E.aug) ^ 2 = ⊥) :
    Function.Bijective (fun z : classes p x hx P =>
      (map p x hx hp i z, map p x hx hp j z)) := by
  let : p.IsFibered := hp.isFibered
  let c := Functor.chosenPullbacks p
  let U : BigFppfOver B S hS :=
    algebraOver A B S hS toS hA
  let V : BigFppfOver B S hS := D.siteOver
  let W : BigFppfOver B S hS := E.siteOver
  let Z : BigFppfOver B S hS := P.siteOver
  let f : U ⟶ V := D.arrow
  let g : U ⟶ W := E.arrow
  let ii : V ⟶ Z := i.right
  let jj : W ⟶ Z := j.right
  have h : f ≫ ii = g ≫ jj := (Under.w i).trans (Under.w j).symm
  have hf : (BigFppfOver.toScheme B S hS).map f =
      Spec.map (CommRingCat.ofHom D.aug) := D.arrow_eq
  have hg : (BigFppfOver.toScheme B S hS).map g =
      Spec.map (CommRingCat.ofHom E.aug) := E.arrow_eq
  obtain ⟨e, he₁, _, he₃⟩ :=
    exists_squareZeroLiftEquivalenceOnBigFppfOver
      B S hS p hp hRS U V W Z
      (hU := show IsAffine (Spec (.of A)) from inferInstance)
      (hV := show IsAffine (Spec D.ring) from inferInstance)
      (hW := show IsAffine (Spec E.ring) from inferInstance)
      (hZ := show IsAffine (Spec P.ring) from inferInstance)
      f g ii jj h
      (by
        rw [hf, hg]
        exact hpb)
      (by rw [hg]; exact specMap_appTop_surjective _ hsurj)
      (by rw [hg]; exact specMap_appTop_ker_sq _ hsq) ⟨x, hx⟩
  have he : ∀ t,
      (e.functor.obj t).1 = isoFiberRestrict p c D.arrow ⟨x, hx⟩
        i.right (D.arrow ≫ i.right) rfl t ∧
      (e.functor.obj t).2 = isoFiberRestrict p c E.arrow ⟨x, hx⟩
        j.right (D.arrow ≫ i.right) ((Under.w j).trans (Under.w i).symm) t := by
    intro t
    refine ⟨Functor.IsoFiber.ext (he₁ t).1 ?_, Functor.IsoFiber.ext (he₁ t).2 (he₃ t).2⟩
    refine (he₃ t).1.trans (heq_of_eq ?_)
    show ((c.pullbackFunctorCompIso D.arrow i.right).symm.app t.obj.left).hom ≫
        t.obj.hom =
      ((c.pullbackFunctorCompIso D.arrow i.right).symm.app t.obj.left).hom ≫
        𝟙 _ ≫ t.obj.hom
    rw [Category.id_comp]
  exact underClassPair_bijective p hp c D.arrow ⟨x, hx⟩ E.arrow i.right j.right
    ((Under.w i).trans (Under.w j).symm) P.arrow (Under.w i) e he

end AffineDeformation

private lemma contains_pullback {R T : CommRingCat.{u}}
    (hR : B.Contains (Spec R)) (hT : B.Contains (Spec T))
    (f : R →+* A) (g : T →+* A) :
    B.Contains (Spec (.of (f.pullback g))) := by
  have hbound : Cardinal.mk (f.pullback g) ≤
      max Cardinal.aleph0 (max (Cardinal.mk R) (Cardinal.mk T)) := by
    calc
      _ ≤ Cardinal.mk (R × T) := Cardinal.mk_subtype_le _
      _ = Cardinal.mk R * Cardinal.mk T := by simp only [Cardinal.mk_prod, Cardinal.lift_id]
      _ ≤ max Cardinal.aleph0 (max (Cardinal.mk R) (Cardinal.mk T)) *
          max Cardinal.aleph0 (max (Cardinal.mk R) (Cardinal.mk T)) :=
        mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
          ((le_max_right _ _).trans (le_max_right _ _)) zero_le zero_le
      _ = _ := Cardinal.mul_eq_self (le_max_left _ _)
  rcases le_total (Cardinal.mk R) (Cardinal.mk T) with h | h
  · apply specContainsOfCardinalBound B _ T hT
    simpa [max_eq_right h] using hbound
  · apply specContainsOfCardinalBound B _ R hR
    simpa [max_eq_left h] using hbound

namespace AffineDeformation

variable {A B S hS toS hA}

private def ofRing (R : AffineDeformation A B S hS toS hA)
    (ring : CommRingCat.{u}) (contains : B.Contains (Spec ring))
    (aug : ring →+* A) (base : R.ring →+* ring) (fac : aug.comp base = R.aug) :
    AffineDeformation A B S hS toS hA where
  ring := ring
  contains := contains
  structureMap := ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom base) ≫ B.inclusion.map R.structureMap)
  aug := aug
  arrow := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom aug))) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom aug) ≫
      (Spec.map (CommRingCat.ofHom base) ≫ B.inclusion.map R.structureMap) = toS
    rw [← Category.assoc, ← Spec.map_comp]
    have hf : CommRingCat.ofHom base ≫ CommRingCat.ofHom aug =
        CommRingCat.ofHom R.aug := CommRingCat.hom_ext fac
    rw [hf, ← R.arrow_eq]
    exact congrArg B.inclusion.map (Over.w R.arrow))
  arrow_eq := rfl

end AffineDeformation

private structure BasedRing (R : AffineDeformation A B S hS toS hA)
    extends AffineDeformation A B S hS toS hA where
  base : R.ring →+* ring
  fac : aug.comp base = R.aug
  structure_fac : Spec.map (CommRingCat.ofHom base) ≫ B.inclusion.map R.structureMap =
    B.inclusion.map structureMap

namespace BasedRing

variable {A B S hS toS hA}

private abbrev toAffine {R : AffineDeformation A B S hS toS hA} (D : BasedRing A B S hS toS hA R) :
    AffineDeformation A B S hS toS hA := D.toAffineDeformation

private structure RingMap {R : AffineDeformation A B S hS toS hA}
    (D E : BasedRing A B S hS toS hA R) where
  hom : D.ring →+* E.ring
  aug_fac : E.aug.comp hom = D.aug
  base_fac : hom.comp D.base = E.base

private def RingMap.toHom {R : AffineDeformation A B S hS toS hA}
    {D E : BasedRing A B S hS toS hA R} (f : RingMap D E) :
    AffineDeformation.Hom D.toAffine E.toAffine :=
  AffineDeformation.homMk f.hom f.aug_fac (by
    rw [← D.structure_fac, ← E.structure_fac, ← Category.assoc, ← Spec.map_comp]
    exact congrArg (fun k => Spec.map k ≫ B.inclusion.map R.structureMap)
      (CommRingCat.hom_ext f.base_fac))

private def RingMap.comp {R : AffineDeformation A B S hS toS hA}
    {D E F : BasedRing A B S hS toS hA R}
    (g : RingMap E F) (f : RingMap D E) : RingMap D F where
  hom := g.hom.comp f.hom
  aug_fac := by rw [← RingHom.comp_assoc, g.aug_fac, f.aug_fac]
  base_fac := by rw [RingHom.comp_assoc, f.base_fac, g.base_fac]

private lemma RingMap.ext {R : AffineDeformation A B S hS toS hA}
    {D E : BasedRing A B S hS toS hA R}
    {f g : RingMap D E} (h : f.hom = g.hom) : f = g := by
  cases f; cases g; cases h; rfl

private lemma RingMap.toHom_comp {R : AffineDeformation A B S hS toS hA}
    {D E F : BasedRing A B S hS toS hA R}
    (g : RingMap E F) (f : RingMap D E) :
    (g.comp f).toHom = g.toHom ≫ f.toHom :=
  AffineDeformation.hom_ext
    (Spec.map_comp (CommRingCat.ofHom f.hom) (CommRingCat.ofHom g.hom))

private abbrev classes {R : AffineDeformation A B S hS toS hA} (D : BasedRing A B S hS toS hA R) :=
  AffineDeformation.classes p x hx D.toAffine

private abbrev map {R : AffineDeformation A B S hS toS hA} (hp : p.IsFiberedInGroupoids)
    {D E : BasedRing A B S hS toS hA R} (f : RingMap D E) :
    classes p x hx D → classes p x hx E :=
  AffineDeformation.map p x hx hp f.toHom

private lemma map_comp {R : AffineDeformation A B S hS toS hA} (hp : p.IsFiberedInGroupoids)
    {D E F : BasedRing A B S hS toS hA R}
    (g : RingMap E F) (f : RingMap D E) (z : classes p x hx D) :
    map p x hx hp (g.comp f) z = map p x hx hp g (map p x hx hp f z) := by
  show AffineDeformation.map p x hx hp _ z = _
  rw [RingMap.toHom_comp, AffineDeformation.map_comp]

private def original (R : AffineDeformation A B S hS toS hA) :
    BasedRing A B S hS toS hA R where
  toAffineDeformation := R
  base := RingHom.id _
  fac := rfl
  structure_fac := by simp

private def prod {R : AffineDeformation A B S hS toS hA} (D E : BasedRing A B S hS toS hA R) :
    BasedRing A B S hS toS hA R := by
  let base := (D.base.prod E.base).codRestrict (D.aug.pullback E.aug) (by
    intro r
    exact (RingHom.congr_fun D.fac r).trans (RingHom.congr_fun E.fac r).symm)
  exact {
    toAffineDeformation := AffineDeformation.ofRing R (.of (D.aug.pullback E.aug))
      (contains_pullback A B D.contains E.contains D.aug E.aug)
      (D.aug.comp (D.aug.pullbackFst E.aug)) base D.fac
    base := base
    fac := D.fac
    structure_fac := rfl }

private def fst {R : AffineDeformation A B S hS toS hA} (D E : BasedRing A B S hS toS hA R) :
    RingMap (prod D E) D where
  hom := D.aug.pullbackFst E.aug
  aug_fac := rfl
  base_fac := rfl

private def snd {R : AffineDeformation A B S hS toS hA} (D E : BasedRing A B S hS toS hA R) :
    RingMap (prod D E) E where
  hom := D.aug.pullbackSnd E.aug
  aug_fac := (RingHom.pullback_comm_sq D.aug E.aug).symm
  base_fac := rfl

private def lift {R : AffineDeformation A B S hS toS hA} {D E F : BasedRing A B S hS toS hA R}
    (f : RingMap D E) (g : RingMap D F) : RingMap D (prod E F) where
  hom := (f.hom.prod g.hom).codRestrict _ (by
    intro r
    exact (RingHom.congr_fun f.aug_fac r).trans (RingHom.congr_fun g.aug_fac r).symm)
  aug_fac := f.aug_fac
  base_fac := RingHom.ext fun r => Subtype.ext <|
    Prod.ext (RingHom.congr_fun f.base_fac r) (RingHom.congr_fun g.base_fac r)

private lemma pair_bijective {R : AffineDeformation A B S hS toS hA} (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    (D E : BasedRing A B S hS toS hA R)
    (hsurj : Function.Surjective E.aug) (hsq : (RingHom.ker E.aug) ^ 2 = ⊥) :
    Function.Bijective (fun z : classes p x hx (prod D E) =>
      (map p x hx hp (fst D E) z, map p x hx hp (snd D E) z)) := by
  apply AffineDeformation.pair_bijective p x hx hp hRS
    D.toAffine E.toAffine (prod D E).toAffine (fst D E).toHom (snd D E).toHom
    _ hsurj hsq
  apply (ringPullbackIsPullback D.aug E.aug).of_iso'
    (Scheme.ΓSpecIso (prod D E).ring) (Scheme.ΓSpecIso D.ring)
    (Scheme.ΓSpecIso E.ring) (Scheme.ΓSpecIso (.of A)) <;>
    exact (Scheme.ΓSpecIso_naturality _).symm

end BasedRing

end Deformations

end Deformation.Artin

end
