module

public import StacksFrontier.Deformation.SquareZero.AlgebraExtensionMaps
public import Mathlib.Algebra.Module.TransferInstance
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pushout and pullback of square-zero algebra extensions (Stacks 0GPW)

Let `A → B → C` be ring maps, let `M` be a `B`-module, let `N` be a `C`-module and let
`c : M → N` be `B`-linear.  Let `0 → M → B' → B → 0` be a square-zero extension of
`A`-algebras with class `ξ ∈ Ext¹_B(NL_{B/A}, M)` under **Stacks 0GPT**, and let
`0 → N → C' → C → 0` be one with class `ζ ∈ Ext¹_C(NL_{C/A}, N)`, as in **Stacks 0GPV**.

This file carries out the two constructions of the remark **Stacks 0GPW** and proves the three
assertions the remark records.

* Pushing `B'` out along `c` gives a square-zero extension `0 → N → B'₁ → B → 0` of
  `A`-algebras, with `B'₁ = (N × B')/M` for `M` antidiagonally embedded.
* Pulling `C'` back along `B → C` gives a square-zero extension `0 → N → B'₂ → B → 0` of
  `A`-algebras, with `B'₂ = C' ×_C B` the fibre product of rings.
* `B'₁` corresponds, under **Stacks 0GPT**, to the image of `ξ` by the map
  `Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)` induced by `c`.
* `B'₂` corresponds to the image of `ζ` by the map
  `Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N)`.
* Consequently there is an `A`-algebra map `B' → C'` compatible with `B → C` and with `c` if
  and only if `B'₁` is isomorphic to `B'₂` as an `A`-algebra extension of `B` by `N`.

## Main definitions

* `Stacks.Deformation.pushoutRing`: the ring `B'₁ = (N × B')/M`.
* `Stacks.Deformation.pushoutExtension`: `B'₁` as a square-zero extension of the `A`-algebra
  `B` by `N`, and `Stacks.Deformation.pushoutMap` the map `B' → B'₁`.
* `Stacks.Deformation.pullbackSubalgebra`: the fibre product `B'₂ = C' ×_C B`.
* `Stacks.Deformation.pullbackExtension`: `B'₂` as a square-zero extension of the `A`-algebra
  `B` by `N`, and `Stacks.Deformation.pullbackMap` the map `B'₂ → C'`.
* `Stacks.Deformation.extClass`: the class of a square-zero extension under **Stacks 0GPT**.

## Main results

* `Stacks.Deformation.extClass_pushoutExtension`: the class of `B'₁` is the image of `ξ`.
* `Stacks.Deformation.extClass_pullbackExtension`: the class of `B'₂` is the image of `ζ`.
* `Stacks.Deformation.isomorphic_pushoutExtension_pullbackExtension_iff`: the diagram chase of
  the remark.
* `Stacks.Deformation.naiveCotangentExtOneMap_id` and
  `Stacks.Deformation.naiveCotangentExtOneTowerMap_self`: the two maps on first Ext which the
  identifications above need to be the identity.

## Implementation notes

**Stacks 0GPT** confines the middle ring of a square-zero extension of `B` by `N` to the
universe `max uB uN`.  Neither `(N × B')/M` nor `C' ×_C B` lies in that universe when the
universes of `M`, `C` are unrelated to those of `B` and `N`, so the two constructions could
not then be compared with each other or read through the classification.  All five of `A`,
`B`, `C`, `M`, `N` are therefore taken in a single universe `u`.  This is a restriction
relative to the source, and it is recorded in the clause string of the tag on each of the two
constructions.

Both constructions have real bodies: `B'₁` is an honest quotient of the trivial square-zero
extension `N × B'` of `B'` by `N` by the antidiagonal ideal, and `B'₂` is an honest
`A`-subalgebra of `C' × B`.  In each case the identification of the kernel of the reduction
with `N` is obtained by exhibiting the map `N → kernel` and proving it bijective, and the
`B`-module structure on the kernel is transported from `N` along the resulting additive
equivalence.

The declarations `Stacks.Deformation.reduction` and `Stacks.Deformation.extClass` are a
spelling layer: the surjection of an extension lands in the module field
`(algebraExtensionProblem A B N).B` of the extension problem, which is definitionally but not
syntactically `B`, and almost every rewrite in this file needs the honest spelling.

The two class identifications are not proved by hand.  Each is **Stacks 0GPV** applied to a
map the construction already supplies: `B' → B'₁` for the trivial tower `A → B → B`, and
`B'₂ → C'` with the identity of `N`.  That leaves the two maps on first Ext which must be
shown to be the identity, which is `naiveCotangentExtOneTowerMap_self` and
`naiveCotangentExtOneMap_id`.  The diagram chase of the remark then follows from these two
identifications and the injectivity of the classification of **Stacks 0GPT**, rather than from
a chase in the two displayed diagrams.

## References

* [Stacks Project, Tag 0GPW](https://stacks.math.columbia.edu/tag/0GPW)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace Stacks.Deformation

section Spelling

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type u} [AddCommGroup N] [Module B N]
  (X : (algebraExtensionProblem A B N).CompatibleExtension.{u})

/-- The reduction `B' → B` of a square-zero extension of the `A`-algebra `B` by `N`, with its
target spelled `B` rather than the module field of the extension problem. -/
public def reduction : X.B' →ₐ[A] B := X.toB

/-- The reduction is the structural surjection of the extension. -/
public lemma reduction_apply (z : X.B') : reduction X z = X.toB z := rfl

/-- The reduction of an extension is surjective. -/
public lemma reduction_surjective : Function.Surjective (reduction X) := X.surjective

/-- The reduction kills the included copy of `N`. -/
public lemma reduction_kernelInclusion (n : N) : reduction X (kernelInclusion X n) = 0 :=
  toB_kernelInclusion X n

/-- Multiplying an element of the included copy of `N` by a ring element acts through `B`. -/
public lemma mul_kernelInclusion' (z : X.B') (n : N) :
    z * kernelInclusion X n = kernelInclusion X (reduction X z • n) :=
  mul_kernelInclusion X z n

/-- The class in `Ext¹_B(NL_{B/A}, N)` of a square-zero extension of the `A`-algebra `B` by `N`,
under the classification of **Stacks 0GPT**. -/
public def extClass : naiveCotangentExtOne A B N :=
  squareZeroAlgebraExtensionClassesEquivExtOne A B N
    (Quotient.mk (SquareZeroExtensionProblem.CompatibleExtension.isomorphicSetoid
      (algebraExtensionProblem A B N)) X)

/-- The inclusion of `N` into the kernel sends `0` to `0`. -/
public lemma kernelInclusion_zero' : kernelInclusion X (0 : N) = 0 := map_zero _

/-- The inclusion of `N` into the kernel is additive on negatives. -/
public lemma kernelInclusion_neg' (n : N) :
    kernelInclusion X (-n) = -kernelInclusion X n := map_neg _ n

/-- An element of the middle ring killed by the reduction comes from `N`. -/
public lemma exists_eq_kernelInclusion' {z : X.B'} (hz : reduction X z = 0) :
    ∃ n : N, kernelInclusion X n = z :=
  exists_eq_kernelInclusion X hz

end Spelling

section Identities

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  (N : Type u) [AddCommGroup N] [Module B N]

/-- The comparison of canonical presentations `A[B] → A[B]` along the identity of `B` is the
identity. -/
public lemma towerPolyHom_self (p : MvPolynomial B A) : towerPolyHom A B B p = p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [towerPolyHom_C]
  | add p q hp hq => rw [map_add, hp, hq]
  | mul_X p b hp => rw [map_mul, hp, towerPolyHom_X]; simp

omit [AddCommGroup N] [Module B N] in
/-- Degree `1` of the canonical map `NL_{B/A} → NL_{B/A}` along the identity of `B` is the
identity. -/
public lemma towerConormal_self (t : (Algebra.Generators.self A B).toExtension.Cotangent) :
    towerConormal A B B t = t := by
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective t
  refine (Algebra.Extension.Cotangent.map_mk
    (towerPresentationHom A B B).toExtensionHom x).trans ?_
  refine congrArg (Algebra.Extension.Cotangent.mk
    (P := (Algebra.Generators.self A B).toExtension)) (Subtype.ext ?_)
  exact towerPolyHom_self A B x.1

/-- For the trivial tower `A → B → B`, restriction of conormal functionals is the identity. -/
public lemma towerConormalPullback_self
    (e : (Algebra.Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    towerConormalPullback A B B e = e := by
  ext t
  rw [towerConormalPullback_apply, towerConormal_self]

/-- The map on conormal cokernels induced by the identity of `N` is the identity. -/
public lemma conormalCokernelPush_id (y : extOneCokernel A B N) :
    conormalCokernelPush A B (LinearMap.id : N →ₗ[B] N) y = y := by
  induction y using Quotient.inductionOn' with
  | h δ => rfl

/-- For the trivial tower `A → B → B`, the map on conormal cokernels is the identity. -/
public lemma conormalCokernelPullback_self (y : extOneCokernel A B N) :
    conormalCokernelPullback A B B y = y := by
  induction y using Quotient.inductionOn' with
  | h e =>
    change Submodule.Quotient.mk (towerConormalPullback A B B e) = Submodule.Quotient.mk e
    rw [towerConormalPullback_self]

/-- The map `Ext¹_B(NL_{B/A}, N) → Ext¹_B(NL_{B/A}, N)` induced by the identity of `N` is the
identity. -/
public lemma naiveCotangentExtOneMap_id (x : naiveCotangentExtOne A B N) :
    naiveCotangentExtOneMap A B (LinearMap.id : N →ₗ[B] N) x = x := by
  change (extCokernelIso A B N).symm
    (conormalCokernelPush A B (LinearMap.id : N →ₗ[B] N) (extCokernelIso A B N x)) = x
  rw [conormalCokernelPush_id]
  exact (extCokernelIso A B N).symm_apply_apply x

/-- For the trivial tower `A → B → B`, the restriction map on `Ext¹_B(NL_{B/A}, N)` is the
identity. -/
public lemma naiveCotangentExtOneTowerMap_self (x : naiveCotangentExtOne A B N) :
    naiveCotangentExtOneTowerMap A B B x = x := by
  change (extCokernelIso A B N).symm
    (conormalCokernelPullback A B B (extCokernelIso A B N x)) = x
  rw [conormalCokernelPullback_self]
  exact (extCokernelIso A B N).symm_apply_apply x

end Identities

section Pullback

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {N : Type u} [AddCommGroup N] [Module B N] [Module C N] [IsScalarTower B C N]
  (Y : (algebraExtensionProblem A C N).CompatibleExtension.{u})

/-- The fibre product of rings `C' ×_C B`, as an `A`-subalgebra of `C' × B`.  This is the middle
ring `B'₂` of the remark's second displayed diagram. -/
public def pullbackSubalgebra : Subalgebra A (Y.B' × B) where
  carrier := {p | reduction Y p.1 = algebraMap B C p.2}
  mul_mem' := by
    intro p q hp hq
    change reduction Y (p.1 * q.1) = algebraMap B C (p.2 * q.2)
    rw [map_mul, map_mul, hp, hq]
  one_mem' := by
    change reduction Y 1 = algebraMap B C 1
    rw [map_one, map_one]
  add_mem' := by
    intro p q hp hq
    change reduction Y (p.1 + q.1) = algebraMap B C (p.2 + q.2)
    rw [map_add, map_add, hp, hq]
  zero_mem' := by
    change reduction Y 0 = algebraMap B C 0
    rw [map_zero, map_zero]
  algebraMap_mem' := by
    intro a
    change reduction Y (algebraMap A Y.B' a) = algebraMap B C (algebraMap A B a)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply A B C]

omit [Module B N] [IsScalarTower B C N] in
/-- A pair lies in the fibre product exactly when its two images in `C` agree. -/
public lemma pullback_mem_iff (p : Y.B' × B) :
    p ∈ pullbackSubalgebra A B C Y ↔ reduction Y p.1 = algebraMap B C p.2 := Iff.rfl

/-- The reduction `B'₂ = C' ×_C B → B`, the second projection. -/
public def pullbackToB : ↥(pullbackSubalgebra A B C Y) →ₐ[A] B :=
  (AlgHom.snd A Y.B' B).comp (pullbackSubalgebra A B C Y).val

omit [Module B N] [IsScalarTower B C N] in
/-- The reduction of the fibre product is the second projection. -/
public lemma pullbackToB_apply (z : ↥(pullbackSubalgebra A B C Y)) :
    pullbackToB A B C Y z = (z : Y.B' × B).2 := rfl

/-- `N`, included into the kernel of `B'₂ → B` by `n ↦ (n, 0)`, reading `n` inside `C'`. -/
public def pullbackKernelHom : N →+ RingHom.ker (pullbackToB A B C Y).toRingHom where
  toFun n := ⟨⟨(kernelInclusion Y n, 0), by
      change reduction Y (kernelInclusion Y n) = algebraMap B C 0
      rw [reduction_kernelInclusion, map_zero]⟩, rfl⟩
  map_zero' := Subtype.ext <| Subtype.ext <| Prod.ext (map_zero (kernelInclusion Y)) rfl
  map_add' n m := Subtype.ext <| Subtype.ext <|
    Prod.ext (map_add (kernelInclusion Y) n m) (add_zero 0).symm

omit [Module B N] [IsScalarTower B C N] in
/-- The inclusion of `N` into the kernel of `B'₂ → B`, read in `C' × B`. -/
public lemma pullbackKernelHom_val (n : N) :
    ((pullbackKernelHom A B C Y n : ↥(pullbackSubalgebra A B C Y)) : Y.B' × B)
      = (kernelInclusion Y n, 0) := rfl

omit [Module B N] [IsScalarTower B C N] in
/-- The inclusion of `N` is a bijection onto the kernel of `B'₂ → B`: an element of that kernel
has second coordinate `0`, hence first coordinate in the kernel of `C' → C`. -/
public lemma pullbackKernelHom_bijective :
    Function.Bijective (pullbackKernelHom A B C Y) := by
  refine ⟨fun n m h ↦ kernelInclusion_injective Y
    (congrArg (fun p : Y.B' × B ↦ p.1) (congrArg Subtype.val (congrArg Subtype.val h))), ?_⟩
  rintro ⟨⟨⟨y, b⟩, hmem⟩, hker⟩
  have hb : b = 0 := hker
  have hy : reduction Y y = 0 := by
    rw [(pullback_mem_iff A B C Y (y, b)).1 hmem, hb, map_zero]
  obtain ⟨n, hn⟩ := exists_eq_kernelInclusion' Y hy
  exact ⟨n, Subtype.ext <| Subtype.ext <| Prod.ext hn hb.symm⟩

/-- The kernel of `B'₂ → B` is additively `N`. -/
public def pullbackKernelAddEquiv : N ≃+ RingHom.ker (pullbackToB A B C Y).toRingHom :=
  AddEquiv.ofBijective (pullbackKernelHom A B C Y) (pullbackKernelHom_bijective A B C Y)

omit [Module B N] [IsScalarTower B C N] in
/-- The identification of `N` with the kernel, read in `C' × B`. -/
public lemma pullbackKernelAddEquiv_val (n : N) :
    (((pullbackKernelAddEquiv A B C Y n : RingHom.ker (pullbackToB A B C Y).toRingHom) :
      ↥(pullbackSubalgebra A B C Y)) : Y.B' × B) = (kernelInclusion Y n, 0) := rfl

/-- Multiplication of an element of the fibre product by the included copy of `N` acts through
the second coordinate, because the two coordinates agree over `C`. -/
public lemma pullback_val_mul_kernelInclusion
    (b' : ↥(pullbackSubalgebra A B C Y)) (n : N) :
    (b' : Y.B' × B) * (kernelInclusion Y n, (0 : B))
      = (kernelInclusion Y (pullbackToB A B C Y b' • n), (0 : B)) := by
  refine Prod.ext ?_ (mul_zero _)
  change (b' : Y.B' × B).1 * kernelInclusion Y n = _
  rw [mul_kernelInclusion' Y]
  refine congrArg (kernelInclusion Y) ?_
  have hb : reduction Y (b' : Y.B' × B).1 = algebraMap B C (b' : Y.B' × B).2 := b'.2
  rw [hb, pullbackToB_apply]
  exact IsScalarTower.algebraMap_smul C (b' : Y.B' × B).2 n

/-- **The pullback extension `B'₂ = C' ×_C B`.**  Pulling the square-zero extension
`0 → N → C' → C → 0` of `A`-algebras back along `B → C` gives a square-zero extension
`0 → N → B'₂ → B → 0` of the `A`-algebra `B` by `N`. -/
@[stacks 0GPW "the pullback extension B'₂ = C' ×_C B; all five rings and modules in one universe"]
public def pullbackExtension :
    (algebraExtensionProblem A B N).CompatibleExtension.{u} := by
  letI : Module B (RingHom.ker (pullbackToB A B C Y).toRingHom) :=
    (pullbackKernelAddEquiv A B C Y).symm.module B
  dsimp only [algebraExtensionProblem]
  exact
    { B' := ↥(pullbackSubalgebra A B C Y)
      toB := pullbackToB A B C Y
      surjective := by
        intro b
        obtain ⟨y, hy⟩ := reduction_surjective Y (algebraMap B C b)
        exact ⟨⟨(y, b), (pullback_mem_iff A B C Y (y, b)).2 hy⟩, rfl⟩
      sq_zero := by
        rw [pow_two]
        refine le_antisymm (Ideal.mul_le.2 ?_) bot_le
        intro r hr s hs
        obtain ⟨n, hn⟩ := (pullbackKernelAddEquiv A B C Y).surjective ⟨r, hr⟩
        obtain ⟨m, hm⟩ := (pullbackKernelAddEquiv A B C Y).surjective ⟨s, hs⟩
        have hr' : (r : Y.B' × B) = (kernelInclusion Y n, 0) :=
          (congrArg (fun t : RingHom.ker (pullbackToB A B C Y).toRingHom ↦
            ((t : ↥(pullbackSubalgebra A B C Y)) : Y.B' × B)) hn).symm
        have hs' : (s : Y.B' × B) = (kernelInclusion Y m, 0) :=
          (congrArg (fun t : RingHom.ker (pullbackToB A B C Y).toRingHom ↦
            ((t : ↥(pullbackSubalgebra A B C Y)) : Y.B' × B)) hm).symm
        rw [Ideal.mem_bot]
        apply Subtype.ext
        change (r : Y.B' × B) * (s : Y.B' × B) = 0
        rw [hr', hs']
        exact Prod.ext (kernelInclusion_mul_kernelInclusion Y n m) (mul_zero 0)
      toB_smul_kernel := by
        intro b' x
        obtain ⟨n, rfl⟩ := (pullbackKernelAddEquiv A B C Y).surjective x
        have hL : (pullbackKernelAddEquiv A B C Y).symm
            (pullbackToB A B C Y b' • pullbackKernelAddEquiv A B C Y n)
            = pullbackToB A B C Y b' • (pullbackKernelAddEquiv A B C Y).symm
              (pullbackKernelAddEquiv A B C Y n) :=
          ((pullbackKernelAddEquiv A B C Y).symm.linearEquiv B).map_smul _ _
        rw [AddEquiv.symm_apply_apply] at hL
        have hsmul := congrArg (pullbackKernelAddEquiv A B C Y) hL
        rw [AddEquiv.apply_symm_apply] at hsmul
        rw [hsmul]
        exact Subtype.ext (Subtype.ext (pullback_val_mul_kernelInclusion A B C Y b' n).symm)
      kernelEquiv := ((pullbackKernelAddEquiv A B C Y).symm.linearEquiv B).symm
      map_I := by
        intro i
        obtain rfl : i = 0 := Subtype.ext i.2
        simp only [map_zero, Submodule.coe_zero] }

/-- The middle ring of the pullback extension is the fibre product. -/
public lemma pullbackExtension_B' :
    (pullbackExtension A B C Y).B' = ↥(pullbackSubalgebra A B C Y) := rfl

/-- **The map `B'₂ → C'`** of the remark's second displayed diagram: the first projection of the
fibre product. -/
@[stacks 0GPW "the map B'₂ → C' of the second displayed diagram"]
public def pullbackMap : ↥(pullbackSubalgebra A B C Y) →ₐ[A] Y.B' :=
  (AlgHom.fst A Y.B' B).comp (pullbackSubalgebra A B C Y).val

omit [Module B N] [IsScalarTower B C N] in
/-- The map `B'₂ → C'` is the first projection. -/
public lemma pullbackMap_apply (z : ↥(pullbackSubalgebra A B C Y)) :
    pullbackMap A B C Y z = (z : Y.B' × B).1 := rfl

omit [Module B N] [IsScalarTower B C N] in
/-- The map `B'₂ → C'` is compatible with `B → C` on the quotients. -/
public lemma pullbackMap_spec (z : ↥(pullbackSubalgebra A B C Y)) :
    Y.toB (pullbackMap A B C Y z) = algebraMap B C (pullbackToB A B C Y z) := z.2

/-- The map `B'₂ → C'` is the identity on the identified kernels `N`. -/
public lemma pullbackMap_kernelInclusion (n : N) :
    pullbackMap A B C Y (kernelInclusion (pullbackExtension A B C Y) n)
      = kernelInclusion Y n := rfl

end Pullback

section PushoutInstances

variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {M' : Type u} [AddCommGroup M'] [Module B M']
  {N : Type u} [AddCommGroup N] [Module B N]

/-- The reduction `B' → B` read on the opposite ring; the rings are commutative, so this is the
reduction composed with `unop`. -/
public def opReduction (X : (algebraExtensionProblem A B M').CompatibleExtension.{u}) :
    (X.B')ᵐᵒᵖ →+* B where
  toFun w := reduction X w.unop
  map_one' := map_one (reduction X)
  map_mul' w v := by
    change reduction X (v.unop * w.unop) = reduction X w.unop * reduction X v.unop
    rw [map_mul, mul_comm]
  map_zero' := map_zero (reduction X)
  map_add' w v := map_add (reduction X) w.unop v.unop

/-- `N`, viewed as a module over the middle ring `B'` of a square-zero extension of `B`, through
the reduction `B' → B`. -/
@[instance_reducible]
public def moduleExtensionRing
    {X : (algebraExtensionProblem A B M').CompatibleExtension.{u}} : Module X.B' N :=
  Module.compHom N (reduction X).toRingHom

/-- The same module structure read on the opposite ring of `B'`. -/
@[instance_reducible]
public def moduleOpExtensionRing
    {X : (algebraExtensionProblem A B M').CompatibleExtension.{u}} : Module (X.B')ᵐᵒᵖ N :=
  Module.compHom N (opReduction X)

end PushoutInstances

attribute [local instance] moduleExtensionRing moduleOpExtensionRing

section PushoutInstances2

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {M' : Type u} [AddCommGroup M'] [Module B M']
  {N : Type u} [AddCommGroup N] [Module B N]

/-- The two actions of `B'` on `N` agree, both being induced by the reduction `B' → B`. -/
public theorem isCentralScalarExtensionRing
    {X : (algebraExtensionProblem A B M').CompatibleExtension.{u}} :
    IsCentralScalar X.B' N := ⟨fun _ _ ↦ rfl⟩

end PushoutInstances2

attribute [local instance] isCentralScalarExtensionRing

section PushoutFst

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type u} [AddCommGroup M] [Module B M]
  (X : (algebraExtensionProblem A B M).CompatibleExtension.{u})
  (N : Type u) [AddCommGroup N] [Module B N]

/-- The composite `N × B' → B' → B` of the projection of the trivial square-zero extension of
`B'` by `N` with the reduction of the extension. -/
public def pushoutFstHom : TrivSqZeroExt X.B' N →+* B where
  toFun w := reduction X w.fst
  map_one' := by
    change reduction X (1 : TrivSqZeroExt X.B' N).fst = 1
    rw [TrivSqZeroExt.fst_one, map_one]
  map_mul' w v := by
    change reduction X (w * v).fst = reduction X w.fst * reduction X v.fst
    rw [TrivSqZeroExt.fst_mul, map_mul]
  map_zero' := by
    change reduction X (0 : TrivSqZeroExt X.B' N).fst = 0
    rw [TrivSqZeroExt.fst_zero, map_zero]
  map_add' w v := by
    change reduction X (w + v).fst = reduction X w.fst + reduction X v.fst
    rw [TrivSqZeroExt.fst_add, map_add]

/-- The map `N × B' → B` is the reduction of the first coordinate. -/
public lemma pushoutFstHom_apply (w : TrivSqZeroExt X.B' N) :
    pushoutFstHom X N w = reduction X w.fst := rfl

end PushoutFst

section Pushout

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type u} [AddCommGroup M] [Module B M]
  {N : Type u} [AddCommGroup N] [Module B N]
  (c : M →ₗ[B] N) (X : (algebraExtensionProblem A B M).CompatibleExtension.{u})

/-- The antidiagonal embedding `m ↦ (ι m, -c m)` of `M` into `N × B'`, where `ι : M → B'` is the
identification of `M` with the kernel of `B' → B`. -/
public def pushoutAntidiag (m : M) : TrivSqZeroExt X.B' N := (kernelInclusion X m, -c m)

/-- First coordinate of the antidiagonal embedding. -/
public lemma pushoutAntidiag_fst (m : M) :
    (pushoutAntidiag c X m).fst = kernelInclusion X m := rfl

/-- Second coordinate of the antidiagonal embedding. -/
public lemma pushoutAntidiag_snd (m : M) : (pushoutAntidiag c X m).snd = -c m := rfl

/-- The antidiagonal copy of `M` is an ideal of `N × B'`: multiplying `(ι m, -c m)` by `w` gives
the antidiagonal element of `w̄ · m`, since `ι m` kills `N` and `B'` acts on `N` through `B`. -/
public def pushoutIdeal : Ideal (TrivSqZeroExt X.B' N) where
  carrier := Set.range (pushoutAntidiag c X)
  add_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨m', rfl⟩
    refine ⟨m + m', TrivSqZeroExt.ext ?_ ?_⟩
    · change kernelInclusion X (m + m') = kernelInclusion X m + kernelInclusion X m'
      exact map_add (kernelInclusion X) m m'
    · change -c (m + m') = -c m + -c m'
      rw [map_add, neg_add]
  zero_mem' := by
    refine ⟨0, TrivSqZeroExt.ext (map_zero (kernelInclusion X)) ?_⟩
    change -c 0 = (0 : TrivSqZeroExt X.B' N).snd
    rw [map_zero, neg_zero, TrivSqZeroExt.snd_zero]
  smul_mem' := by
    rintro w _ ⟨m, rfl⟩
    refine ⟨reduction X w.fst • m, TrivSqZeroExt.ext ?_ ?_⟩
    · change kernelInclusion X (reduction X w.fst • m)
        = (w * pushoutAntidiag c X m).fst
      rw [TrivSqZeroExt.fst_mul, pushoutAntidiag_fst, mul_kernelInclusion' X]
    · change -c (reduction X w.fst • m) = (w * pushoutAntidiag c X m).snd
      rw [TrivSqZeroExt.snd_mul, pushoutAntidiag_fst, pushoutAntidiag_snd]
      have h0 : (MulOpposite.op (kernelInclusion X m) : (X.B')ᵐᵒᵖ) • w.snd = (0 : N) := by
        change reduction X (kernelInclusion X m) • w.snd = (0 : N)
        rw [reduction_kernelInclusion, zero_smul]
      have h1 : (w.fst • (-c m) : N) = -(c (reduction X w.fst • m)) := by
        change (reduction X w.fst • (-c m) : N) = -(c (reduction X w.fst • m))
        rw [map_smul, smul_neg]
      rw [h0, h1, add_zero, map_smul]

/-- Membership in the antidiagonal ideal. -/
public lemma mem_pushoutIdeal_iff (w : TrivSqZeroExt X.B' N) :
    w ∈ pushoutIdeal c X ↔ ∃ m : M, pushoutAntidiag c X m = w := Iff.rfl

/-- The middle ring `B'₁ = (N × B')/M` of the pushout, with `M` antidiagonally embedded. -/
public abbrev pushoutRing := (TrivSqZeroExt X.B' N) ⧸ pushoutIdeal c X

/-- The quotient map `N × B' → B'₁`. -/
public def pushoutMk : TrivSqZeroExt X.B' N →+* pushoutRing c X :=
  Ideal.Quotient.mk (pushoutIdeal c X)

/-- The quotient map onto `B'₁` is surjective. -/
public lemma pushoutMk_surjective : Function.Surjective (pushoutMk c X) :=
  Ideal.Quotient.mk_surjective

/-- An element of `N × B'` dies in `B'₁` exactly when it is antidiagonal. -/
public lemma pushoutMk_eq_zero_iff (w : TrivSqZeroExt X.B' N) :
    pushoutMk c X w = 0 ↔ ∃ m : M, pushoutAntidiag c X m = w :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The reduction `B'₁ → B`, induced by `N × B' → B`. -/
public def pushoutToBRingHom : pushoutRing c X →+* B :=
  Ideal.Quotient.lift (pushoutIdeal c X) (pushoutFstHom X N) (by
    rintro w ⟨m, rfl⟩
    change reduction X (kernelInclusion X m) = 0
    exact reduction_kernelInclusion X m)

/-- The reduction `B'₁ → B` on a representative. -/
public lemma pushoutToBRingHom_mk (w : TrivSqZeroExt X.B' N) :
    pushoutToBRingHom c X (pushoutMk c X w) = reduction X w.fst := rfl

/-- The `A`-algebra structure on `B'₁`, through `A → B' → N × B' → B'₁`. -/
@[instance_reducible]
public def pushoutAlgebra : Algebra A (pushoutRing c X) :=
  RingHom.toAlgebra ((pushoutMk c X).comp
    ((TrivSqZeroExt.inlHom X.B' N).comp (algebraMap A X.B')))

/-- Multiplying an element of `N × B'` by a pure `N`-element acts through the reduction to `B`. -/
public lemma pushout_mul_inr (w : TrivSqZeroExt X.B' N) (n : N) :
    w * TrivSqZeroExt.inr n = TrivSqZeroExt.inr (reduction X w.fst • n) := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inr, mul_zero]
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inr]
    have h0 : (MulOpposite.op (0 : X.B') : (X.B')ᵐᵒᵖ) • w.snd = (0 : N) := by
      change reduction X 0 • w.snd = (0 : N)
      rw [map_zero, zero_smul]
    rw [h0, add_zero]
    rfl

/-- Two pure `N`-elements of `N × B'` multiply to zero. -/
public lemma pushout_inr_mul_inr (n m : N) :
    (TrivSqZeroExt.inr n : TrivSqZeroExt X.B' N) * TrivSqZeroExt.inr m = 0 := by
  rw [pushout_mul_inr, TrivSqZeroExt.fst_inr, map_zero, zero_smul, TrivSqZeroExt.inr_zero]

/-- `N`, included into the kernel of `B'₁ → B` by `n ↦ [(n, 0)]`. -/
public def pushoutKernelHom : N →+ RingHom.ker (pushoutToBRingHom c X) where
  toFun n := ⟨pushoutMk c X (TrivSqZeroExt.inr n), by
    change pushoutToBRingHom c X (pushoutMk c X (TrivSqZeroExt.inr n)) = 0
    rw [pushoutToBRingHom_mk, TrivSqZeroExt.fst_inr, map_zero]⟩
  map_zero' := by
    apply Subtype.ext
    change pushoutMk c X (TrivSqZeroExt.inr (0 : N)) = 0
    rw [TrivSqZeroExt.inr_zero, map_zero]
  map_add' n m := by
    apply Subtype.ext
    change pushoutMk c X (TrivSqZeroExt.inr (n + m)) = _
    rw [TrivSqZeroExt.inr_add, map_add]
    rfl

/-- The inclusion of `N` into the kernel of `B'₁ → B`, on representatives. -/
public lemma pushoutKernelHom_val (n : N) :
    ((pushoutKernelHom c X n : RingHom.ker (pushoutToBRingHom c X)) : pushoutRing c X)
      = pushoutMk c X (TrivSqZeroExt.inr n) := rfl

/-- The inclusion of `N` is a bijection onto the kernel of `B'₁ → B`: it is injective because
`ι` is, and an element `[w]` of the kernel has `w.fst = ι m`, so `[w] = [(w.snd + c m, 0)]`. -/
public lemma pushoutKernelHom_bijective : Function.Bijective (pushoutKernelHom c X) := by
  constructor
  · refine (injective_iff_map_eq_zero (pushoutKernelHom c X)).2 ?_
    intro n hn
    have h0 : pushoutMk c X (TrivSqZeroExt.inr n) = 0 :=
      congrArg (fun t : RingHom.ker (pushoutToBRingHom c X) ↦ (t : pushoutRing c X)) hn
    obtain ⟨m, hm⟩ := (pushoutMk_eq_zero_iff c X _).1 h0
    have hfst : kernelInclusion X m = 0 := by
      have := congrArg TrivSqZeroExt.fst hm
      rwa [pushoutAntidiag_fst, TrivSqZeroExt.fst_inr] at this
    have hm0 : m = 0 :=
      kernelInclusion_injective X (hfst.trans (kernelInclusion_zero' X).symm)
    have hsnd : -c m = n := by
      have := congrArg TrivSqZeroExt.snd hm
      rwa [pushoutAntidiag_snd, TrivSqZeroExt.snd_inr] at this
    rw [← hsnd, hm0, map_zero, neg_zero]
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := pushoutMk_surjective c X z
    have hw : reduction X w.fst = 0 := hz
    obtain ⟨m, hm⟩ := exists_eq_kernelInclusion' X hw
    refine ⟨w.snd + c m, ?_⟩
    apply Subtype.ext
    change pushoutMk c X (TrivSqZeroExt.inr (w.snd + c m)) = pushoutMk c X w
    rw [← sub_eq_zero, ← map_sub, pushoutMk_eq_zero_iff]
    refine ⟨-m, TrivSqZeroExt.ext ?_ ?_⟩
    · change kernelInclusion X (-m) = _
      rw [kernelInclusion_neg', hm, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inr, zero_sub]
    · change -c (-m) = _
      rw [map_neg, neg_neg, TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inr]
      abel

/-- The kernel of `B'₁ → B` is additively `N`. -/
public def pushoutKernelAddEquiv : N ≃+ RingHom.ker (pushoutToBRingHom c X) :=
  AddEquiv.ofBijective (pushoutKernelHom c X) (pushoutKernelHom_bijective c X)

/-- The identification of `N` with the kernel, on representatives. -/
public lemma pushoutKernelAddEquiv_val (n : N) :
    ((pushoutKernelAddEquiv c X n : RingHom.ker (pushoutToBRingHom c X)) : pushoutRing c X)
      = pushoutMk c X (TrivSqZeroExt.inr n) := rfl

/-- **The pushout extension `B'₁ = (N × B')/M`.**  Pushing the square-zero extension
`0 → M → B' → B → 0` of `A`-algebras out along `c : M → N` gives a square-zero extension
`0 → N → B'₁ → B → 0` of the `A`-algebra `B` by `N`. -/
@[stacks 0GPW "the pushout extension B'₁ = (N × B')/M; all five rings and modules in one universe",
  ega "0 19.5.6.1" "partial"]
public def pushoutExtension : (algebraExtensionProblem A B N).CompatibleExtension.{u} := by
  letI : Algebra A (pushoutRing c X) := pushoutAlgebra c X
  letI : Module B (RingHom.ker (pushoutToBRingHom c X)) :=
    (pushoutKernelAddEquiv c X).symm.module B
  dsimp only [algebraExtensionProblem]
  exact
    { B' := pushoutRing c X
      algebraA'B' := pushoutAlgebra c X
      toB := AlgHom.mk (pushoutToBRingHom c X) (fun a ↦ (reduction X).commutes a)
      surjective := by
        intro b
        obtain ⟨x, hx⟩ := reduction_surjective X b
        refine ⟨pushoutMk c X (TrivSqZeroExt.inl x), ?_⟩
        change pushoutToBRingHom c X (pushoutMk c X (TrivSqZeroExt.inl x)) = b
        rw [pushoutToBRingHom_mk, TrivSqZeroExt.fst_inl, hx]
      sq_zero := by
        rw [pow_two]
        refine le_antisymm (Ideal.mul_le.2 ?_) bot_le
        intro r hr s hs
        obtain ⟨n, hn⟩ := (pushoutKernelAddEquiv c X).surjective ⟨r, hr⟩
        obtain ⟨m, hm⟩ := (pushoutKernelAddEquiv c X).surjective ⟨s, hs⟩
        have hr' : r = pushoutMk c X (TrivSqZeroExt.inr n) :=
          (congrArg (fun t : RingHom.ker (pushoutToBRingHom c X) ↦
            (t : pushoutRing c X)) hn).symm
        have hs' : s = pushoutMk c X (TrivSqZeroExt.inr m) :=
          (congrArg (fun t : RingHom.ker (pushoutToBRingHom c X) ↦
            (t : pushoutRing c X)) hm).symm
        rw [Ideal.mem_bot, hr', hs', ← map_mul, pushout_inr_mul_inr, map_zero]
      toB_smul_kernel := by
        intro z x
        change pushoutToBRingHom c X z • x = z • x
        obtain ⟨n, rfl⟩ := (pushoutKernelAddEquiv c X).surjective x
        have hL : (pushoutKernelAddEquiv c X).symm
            (pushoutToBRingHom c X z • pushoutKernelAddEquiv c X n)
            = pushoutToBRingHom c X z • (pushoutKernelAddEquiv c X).symm
              (pushoutKernelAddEquiv c X n) :=
          ((pushoutKernelAddEquiv c X).symm.linearEquiv B).map_smul _ _
        rw [AddEquiv.symm_apply_apply] at hL
        have hsmul := congrArg (pushoutKernelAddEquiv c X) hL
        rw [AddEquiv.apply_symm_apply] at hsmul
        rw [show (pushoutToBRingHom c X z • pushoutKernelAddEquiv c X n :
            RingHom.ker (pushoutToBRingHom c X))
          = pushoutKernelAddEquiv c X (pushoutToBRingHom c X z • n) from hsmul]
        apply Subtype.ext
        obtain ⟨w, rfl⟩ := pushoutMk_surjective c X z
        change pushoutMk c X (TrivSqZeroExt.inr
            (pushoutToBRingHom c X (pushoutMk c X w) • n))
          = pushoutMk c X w * pushoutMk c X (TrivSqZeroExt.inr n)
        rw [← map_mul, pushout_mul_inr, pushoutToBRingHom_mk]
      kernelEquiv := ((pushoutKernelAddEquiv c X).symm.linearEquiv B).symm
      map_I := by
        intro i
        obtain rfl : i = 0 := Subtype.ext i.2
        simp only [map_zero, Submodule.coe_zero] }

/-- The reduction of the pushout extension on a representative. -/
public lemma pushoutExtension_toB_mk (w : TrivSqZeroExt X.B' N) :
    (pushoutExtension c X).toB (pushoutMk c X w) = reduction X w.fst := rfl

/-- The identified kernel of the pushout extension, on representatives. -/
public lemma kernelInclusion_pushoutExtension (n : N) :
    kernelInclusion (pushoutExtension c X) n = pushoutMk c X (TrivSqZeroExt.inr n) := rfl

/-- **The map `B' → B'₁`** of the remark's first displayed diagram: `x ↦ [(0, x)]`. -/
@[stacks 0GPW "the map B' → B'₁ of the first displayed diagram"]
public def pushoutMap : X.B' →ₐ[A] (pushoutExtension c X).B' where
  toRingHom := (pushoutMk c X).comp (TrivSqZeroExt.inlHom X.B' N)
  commutes' := fun _ ↦ rfl

/-- The map `B' → B'₁` on elements. -/
public lemma pushoutMap_apply (x : X.B') :
    pushoutMap c X x = pushoutMk c X (TrivSqZeroExt.inl x) := rfl

/-- The map `B' → B'₁` is compatible with the reductions to `B`. -/
public lemma pushoutExtension_toB_pushoutMap (x : X.B') :
    (pushoutExtension c X).toB (pushoutMap c X x) = reduction X x := rfl

/-- The map `B' → B'₁` carries the identified kernel `M` to `N` by `c`: this is exactly the
relation imposed by the antidiagonal ideal. -/
public lemma pushoutMap_kernelInclusion (m : M) :
    pushoutMap c X (kernelInclusion X m)
      = kernelInclusion (pushoutExtension c X) (c m) := by
  change (pushoutMk c X (TrivSqZeroExt.inl (kernelInclusion X m)) : pushoutRing c X)
    = pushoutMk c X (TrivSqZeroExt.inr (c m))
  rw [← sub_eq_zero, ← map_sub, pushoutMk_eq_zero_iff]
  refine ⟨m, TrivSqZeroExt.ext ?_ ?_⟩
  · change kernelInclusion X m = _
    rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, sub_zero]
  · change -c m = _
    rw [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_sub]

end Pushout

section Claims

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {M : Type u} [AddCommGroup M] [Module B M]
  {N : Type u} [AddCommGroup N] [Module B N] [Module C N] [IsScalarTower B C N]

/-- **Stacks 0GPW.**  The pushout extension `B'₁` corresponds, under the classification of
**Stacks 0GPT**, to the image of the class of `B'` by the map
`Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)` induced by `c : M → N`.

This is **Stacks 0GPV** for the trivial tower `A → B → B`, applied to the map `B' → B'₁`
produced by the construction, together with the fact that the restriction map for that tower
is the identity. -/
@[stacks 0GPW "B'₁ corresponds to the image of ξ under Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)"]
public theorem extClass_pushoutExtension (c : M →ₗ[B] N)
    (X : (algebraExtensionProblem A B M).CompatibleExtension.{u}) :
    extClass (pushoutExtension c X) = naiveCotangentExtOneMap A B c (extClass X) := by
  have h := (exists_compatible_algebraMap_iff A B B c X (pushoutExtension c X)).1
    ⟨pushoutMap c X, fun _ ↦ rfl, pushoutMap_kernelInclusion c X⟩
  rw [naiveCotangentExtOneTowerMap_self] at h
  exact h.symm

/-- **Stacks 0GPW.**  The pullback extension `B'₂` corresponds, under the classification of
**Stacks 0GPT**, to the image of the class of `C'` by the map
`Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N)`.

This is **Stacks 0GPV** applied to the projection `B'₂ → C'`, which is compatible with
`B → C` and with the identity of `N`, together with the fact that the map on first Ext
induced by the identity of `N` is the identity. -/
@[stacks 0GPW "B'₂ corresponds to the image of ζ under Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N)"]
public theorem extClass_pullbackExtension
    (Y : (algebraExtensionProblem A C N).CompatibleExtension.{u}) :
    extClass (pullbackExtension A B C Y) = naiveCotangentExtOneTowerMap A B C (extClass Y) := by
  have h := (exists_compatible_algebraMap_iff A B C (LinearMap.id : N →ₗ[B] N)
    (pullbackExtension A B C Y) Y).1
    ⟨pullbackMap A B C Y, pullbackMap_spec A B C Y, pullbackMap_kernelInclusion A B C Y⟩
  rwa [naiveCotangentExtOneMap_id] at h

/-- **Stacks 0GPW**, the diagram chase.  There is an `A`-algebra map `B' → C'` compatible with
`B → C` and with `c : M → N` if and only if the pushout `B'₁` is isomorphic to the pullback
`B'₂` as `A`-algebra extensions of `B` by `N`.

The two directions are obtained from **Stacks 0GPV** together with the two class
identifications above and the injectivity of the classification of **Stacks 0GPT**. -/
@[stacks 0GPW "a compatible A-algebra map B' → C' exists iff B'₁ and B'₂ are isomorphic"]
public theorem isomorphic_pushoutExtension_pullbackExtension_iff (c : M →ₗ[B] N)
    (X : (algebraExtensionProblem A B M).CompatibleExtension.{u})
    (Y : (algebraExtensionProblem A C N).CompatibleExtension.{u}) :
    SquareZeroExtensionProblem.CompatibleExtension.Isomorphic
        (pushoutExtension c X) (pullbackExtension A B C Y) ↔
      ∃ h : X.B' →ₐ[A] Y.B',
        (∀ z : X.B', Y.toB (h z) = algebraMap B C (X.toB z)) ∧
          ∀ m : M, h (kernelInclusion X m) = kernelInclusion Y (c m) := by
  rw [exists_compatible_algebraMap_iff A B C c X Y]
  change _ ↔ naiveCotangentExtOneMap A B c (extClass X)
    = naiveCotangentExtOneTowerMap A B C (extClass Y)
  rw [← extClass_pushoutExtension, ← extClass_pullbackExtension]
  exact ⟨fun h ↦ congrArg (squareZeroAlgebraExtensionClassesEquivExtOne A B N) (Quotient.sound h),
    fun h ↦ Quotient.exact ((squareZeroAlgebraExtensionClassesEquivExtOne A B N).injective h)⟩

end Claims

end Stacks.Deformation

end
