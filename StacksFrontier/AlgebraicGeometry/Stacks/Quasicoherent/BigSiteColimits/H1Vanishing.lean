module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CoproductSections

/-!
# Surjectivity on sections over an affine object

The one hypothesis of the cokernel step of a global presentation which is not formal is that
the presenting morphism is surjective on sections over the base, and over an affine object of
a big site of schemes that is the vanishing of the first cohomology of a quasi-coherent module
on an affine, Stacks 03DW.  This file reduces that surjectivity to ring-level descent along a
single faithfully flat morphism, in two steps, both of which are elementary once the
identifications they take as data are in hand.

The first step is the passage from a covering family to a single morphism.  A covering sieve of
an affine object does not contain the morphism out of the disjoint union of a covering family —
a sieve is closed under precomposition, not under coproducts — so the descent property
`SheafOfModules.JointlyDetectsRange` has to be stated over a family.  But if the family itself
covers one object `W` of the site, in such a way that restriction to the members is surjective
on the source and injective on the target, then a lift over each member assembles into a lift
over `W`; for `W` the disjoint union of a finite subfamily and the family its own pieces, both
conditions are the sheaf condition for that decomposition.  This is
`SheafOfModules.jointlyDetectsRange_of_detectsRange`, and it needs nothing else.

The second step is descent along the single morphism, and that is where the content is: an
element of the sections over the base whose restriction is a value of the presenting morphism is
already a value of it, because membership in the image of a map of modules descends along a
faithfully flat base change.  The ring-level statement is
`Module.Descent.mem_range_of_mem_range_of_baseChangeEquiv`, whose data is a pair of
isomorphisms identifying the sections over the covering object with the base change of the
sections over the base, compatible with the morphism.  Those identifications are what a
quasi-coherent module over an affine base supplies, and they are the hypotheses left open here.

No first cohomology of a Čech or Amitsur complex is computed on the way: the descent of
membership in an image along a faithfully flat base change is a degree-zero statement, and the
first cohomology of the kernel is already accounted for by the base-change identification of
the sections of the source, because flat base change commutes with kernels
(`Module.Descent.isBaseChange_ker`).

## Main definitions

* `SheafOfModules.DetectsRange`: a single morphism along which membership in the image of a
  morphism of sheaves of modules descends.

## Main results

* `SheafOfModules.jointlyDetectsRange_of_detectsRange`: a family whose members cover an object
  along which images are detected, and over which the sections of the source and the target are
  determined by their restrictions, jointly detects images.
* `SheafOfModules.detectsRange_of_baseChangeEquiv`: **a faithfully flat morphism whose sections
  are a base change detects images.**  This is the descent half of Stacks 03DW.
* `SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange`: the shape the cokernel step
  of a global presentation consumes — surjectivity of an epimorphism on sections over a terminal
  object, given that every covering sieve of that object contains a family which jointly detects
  images.
* `SheafOfModules.surjective_val_app_of_epi_of_detectsRange`: the two steps combined, with the
  per-sieve data supplied as a single morphism.

## Implementation notes

The ring structures are passed as data rather than read off the structure sheaf.  A
`SheafOfModules.{m} R` has `R : Sheaf J RingCat`, so its sections carry a ring and nothing
more, while a base change needs a commutative ring and an algebra; on a big site of schemes
both are present, but only through `CategoryTheory.forget₂ CommRingCat RingCat`, which
instance search does not unfold.  The statements below therefore take the commutative rings,
the module structures over them, and the morphism of modules they make of the presenting
morphism, as explicit arguments, together with the equations identifying them with the
structure already on the sections.  Those equations are all that the proofs use, so the
identification is made once, where the structure sheaf is in hand.

Membership in `LinearMap.range` of a map of sections does not depend on which ring the map is
linear over, so no compatibility between the two scalar actions on a single module of sections
is required: `SheafOfModules.detectsRange_of_baseChangeEquiv` relates the given `A`-linear and
`B`-linear maps to the morphism of sheaves only through their values.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- A morphism `h : W ⟶ T` *detects images* of `b` when a section of the target over `T` whose
restriction along `h` is a value of `b` is itself a value of `b`.  This is the one-morphism form
of `SheafOfModules.JointlyDetectsRange`. -/
def DetectsRange {P N : SheafOfModules.{m} R} (b : P ⟶ N) {T W : C} (h : W ⟶ T) : Prop :=
  ∀ n : N.val.obj (op T),
    N.val.restrictₛₗ h.op n ∈ LinearMap.range (b.val.app (op W)).hom →
      n ∈ LinearMap.range (b.val.app (op T)).hom

/-- **A family which covers an object detecting images jointly detects images.**  Let the
members `V i` of a family over `T` all factor through a single `W ⟶ T` which detects images of
`b`, and let restriction to the members be surjective on the sections of the source over `W` and
injective on the sections of the target over `W`.  Then a section over `T` which is a value of
`b` on each member is a value of `b`: the lifts over the members assemble into a lift over `W`,
which is carried to the restriction of the section because its restrictions to the members are.

For `W` a disjoint union of the members and the family its own pieces, the two hypotheses on
restriction are the sheaf condition for that decomposition.  This is why
`SheafOfModules.JointlyDetectsRange` is stated over a family: an fppf covering sieve of an
affine object contains no single morphism out of a disjoint union of the covering. -/
theorem jointlyDetectsRange_of_detectsRange {P N : SheafOfModules.{m} R} (b : P ⟶ N)
    {T W : C} {I : Type w} {V : I → C} (g : ∀ i, V i ⟶ T) (h : W ⟶ T) (a : ∀ i, V i ⟶ W)
    (hcomm : ∀ i, a i ≫ h = g i)
    (hsurj : Function.Surjective
      fun p : P.val.obj (op W) ↦ fun i ↦ P.val.restrictₛₗ (a i).op p)
    (hinj : Function.Injective
      fun n : N.val.obj (op W) ↦ fun i ↦ N.val.restrictₛₗ (a i).op n)
    (hdet : DetectsRange b h) : JointlyDetectsRange.{w} b g := by
  intro n hn
  refine hdet n ?_
  choose p hp using hn
  obtain ⟨q, hq⟩ := hsurj p
  refine ⟨q, hinj (funext fun i ↦ ?_)⟩
  calc N.val.restrictₛₗ (a i).op (b.val.app (op W) q)
      = b.val.app (op (V i)) (P.val.restrictₛₗ (a i).op q) :=
        (PresheafOfModules.naturality_apply b.val (a i).op q).symm
    _ = b.val.app (op (V i)) (p i) :=
        congrArg (fun z ↦ b.val.app (op (V i)) z) (congrFun hq i)
    _ = N.val.restrictₛₗ (g i).op n := hp i
    _ = N.val.restrictₛₗ (a i).op (N.val.restrictₛₗ h.op n) :=
        (N.val.congr_map_apply (congrArg Quiver.Hom.op (hcomm i)) n).symm.trans
          (N.val.map_comp_apply h.op (a i).op n)

/-- **A faithfully flat morphism whose sections are a base change detects images.**  Let `A` and
`B` be commutative rings with `B` faithfully flat over `A`, acting on the sections of `P` and `N`
over `T` and over `W` respectively; let `bT` and `bW` be the morphism `b` read as a map of those
modules; and let `eP` and `eN` identify the sections over `W` with the base change along `A → B`
of the sections over `T`, compatibly with `b` and, for `N`, with restriction along `h`.  Then `h`
detects images of `b`.

This is the descent half of Stacks 03DW: the vanishing of the first cohomology of a
quasi-coherent module on an affine, in the only form in which the cokernel step of a global
presentation uses it.  The content is
`Module.Descent.mem_range_of_mem_range_of_baseChangeEquiv`, that membership in the image of a
map of modules descends along a faithfully flat base change. -/
theorem detectsRange_of_baseChangeEquiv {P N : SheafOfModules.{m} R} (b : P ⟶ N) {T W : C}
    (h : W ⟶ T) (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B]
    [Module A (P.val.obj (op T))] [Module A (N.val.obj (op T))]
    [Module B (P.val.obj (op W))] [Module B (N.val.obj (op W))]
    (bT : P.val.obj (op T) →ₗ[A] N.val.obj (op T))
    (hbT : ∀ p, bT p = b.val.app (op T) p)
    (bW : P.val.obj (op W) →ₗ[B] N.val.obj (op W))
    (hbW : ∀ p, bW p = b.val.app (op W) p)
    (eP : B ⊗[A] P.val.obj (op T) ≃ₗ[B] P.val.obj (op W))
    (eN : B ⊗[A] N.val.obj (op T) ≃ₗ[B] N.val.obj (op W))
    (hsq : ∀ x, bW (eP x) = eN (LinearMap.lTensor B bT x))
    (hres : ∀ n, eN ((1 : B) ⊗ₜ[A] n) = N.val.restrictₛₗ h.op n) :
    DetectsRange b h := by
  intro n hn
  obtain ⟨p, hp⟩ := hn
  obtain ⟨q, hq⟩ := Module.Descent.mem_range_of_mem_range_of_baseChangeEquiv A B bT bW eP eN hsq
    (m' := n) ⟨p, by rw [hbW, hres]; exact hp⟩
  exact ⟨q, (hbT q).symm.trans hq⟩

/-- **An epimorphism of sheaves of modules is surjective on sections over a terminal object**
as soon as every covering sieve of that object contains a family which jointly detects images.
This is `SheafOfModules.surjective_val_app_of_jointlyDetectsRange` with local surjectivity
replaced by the epimorphism property it is equivalent to. -/
theorem surjective_val_app_of_epi_of_jointlyDetectsRange {T : C} {P N : SheafOfModules.{m} R}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (b : P ⟶ N) [Epi b]
    (hdet : ∀ S : Sieve T, S ∈ J T → ∃ (I : Type w) (V : I → C) (g : ∀ i, V i ⟶ T),
      (∀ i, S (g i)) ∧ JointlyDetectsRange.{w} b g) :
    Function.Surjective (b.val.app (op T)) :=
  surjective_val_app_of_jointlyDetectsRange.{w} b
    (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi b) hdet

/-- **Surjectivity on sections over a terminal object from descent along one morphism per
covering sieve.**  The two steps of the file combined: every covering sieve of the terminal
object is required to contain a family which covers a single object detecting images of `b` and
over which the sections of the source and the target are determined by their restrictions to the
family. -/
theorem surjective_val_app_of_epi_of_detectsRange {T : C} {P N : SheafOfModules.{m} R}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (b : P ⟶ N) [Epi b]
    (hdet : ∀ S : Sieve T, S ∈ J T → ∃ (I : Type w) (V : I → C) (g : ∀ i, V i ⟶ T) (W : C)
      (h : W ⟶ T) (a : ∀ i, V i ⟶ W), (∀ i, S (g i)) ∧ (∀ i, a i ≫ h = g i) ∧
        Function.Surjective
          (fun p : P.val.obj (op W) ↦ fun i ↦ P.val.restrictₛₗ (a i).op p) ∧
        Function.Injective
          (fun n : N.val.obj (op W) ↦ fun i ↦ N.val.restrictₛₗ (a i).op n) ∧
        DetectsRange b h) :
    Function.Surjective (b.val.app (op T)) :=
  surjective_val_app_of_epi_of_jointlyDetectsRange.{w} b fun S hS ↦ by
    obtain ⟨I, V, g, W, h, a, hgS, hcomm, hsurj, hinj, hb⟩ := hdet S hS
    exact ⟨I, V, g, hgS,
      jointlyDetectsRange_of_detectsRange.{w} b g h a hcomm hsurj hinj hb⟩

end SheafOfModules

end
