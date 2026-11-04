module

public import StacksFrontier.Algebra.MittagLeffler.Basic
public import StacksFrontier.Algebra.MittagLeffler.Colimit
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.RingTheory.Flat.MittagLeffler

/-!
# Colimits of free modules over a local ring are Mittag-Leffler

Let `(A, 𝔪)` be a local ring and let `(F i, u_{i i'})` be a directed system of free `A`-modules
whose transition maps `u_{i i'}` induce injective maps `F i / 𝔪 F i → F i' / 𝔪 F i'`. Then the
colimit of the system is a Mittag-Leffler `A`-module.

This is the second half of the proof of Stacks 05U7. That lemma says that a finite module `N` over
a local ring `B`, essentially of finite type over a henselian local ring `A` and flat over `A`, is
a filtered colimit of free `A`-modules with injective reductions modulo `𝔪_A`, *and* that `N` is
then a Mittag-Leffler `A`-module. The source deduces the second assertion from the first by two
steps, both of which are available: the transition maps are `A`-universally injective by Stacks
05FQ, because a free module is projective and flat; and a colimit of a directed system of
Mittag-Leffler modules along universally injective transition maps is Mittag-Leffler by Stacks
0AS7, free modules being Mittag-Leffler by Stacks 059R (2). This file carries out that deduction.

## Main definitions

There are no new definitions.

## Main results

* `Module.rTensor_injective_of_free_of_injective_mapQ_maximalIdeal`: a map of free modules over a
  local ring whose reduction modulo the maximal ideal is injective is universally injective. This
  is Stacks 05FQ specialized to the case the source's proof of Stacks 05U7 uses.
* `Module.mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal`: the colimit of a directed
  system of free modules over a local ring with injective reductions modulo the maximal ideal is
  Mittag-Leffler, in the spelled-out form of Stacks 059E (1) that Stacks 0AS7 produces.
* `Module.isMittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal`: the same conclusion written
  with the predicate `IsMittagLeffler` of Stacks 059F.
* `IsMittagLeffler.of_linearEquiv`: being Mittag-Leffler transports along a linear equivalence,
  including one which changes the universe of the module.

## Implementation notes

The reduction of a transition map modulo the maximal ideal is the canonical `Submodule.mapQ`
between the quotients by `𝔪 • ⊤`, exactly as in the library's form of Stacks 05FQ
(`Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal`) and as in Stacks
0AS5 and 046Y. The hypothesis is therefore stated in that form, which is also the form in which
the first half of Stacks 05U7 states it, so that the two halves compose with no transport.

The index category is a nonempty directed preorder, which is what Stacks means by a filtered
colimit of modules, what the system of affine open neighbourhoods of a point supplies in the
geometric proof of Stacks 05U7, and what the library's Stacks 0AS7
(`ModuleCat.mittagLeffler_pt_of_forall_mittagLeffler_of_forall_rTensor_injective`) takes. A
directed preorder is filtered, by `CategoryTheory.isFiltered_of_directed_le_nonempty`, so a
conclusion drawn here also supplies the filtered form.

The modules of the system and the test data live in a single universe `v` with `Small.{v} A`,
which is inherited from every result used: Stacks 05FQ, Stacks 059R and Stacks 0AS7 are all stated
that way, Stacks 0AS5 — through which Stacks 05FQ passes — being what fixes it. `Small.{v} A` is
no restriction when `v = max u v`, in particular when the ring and the modules share a universe.
The index type `w` is independent.

`IsMittagLeffler.of_linearEquiv` is what identifies the colimit with a module given in advance,
and it is the one statement here whose universes are free: the two modules may live in different
universes, which is what makes it usable against a colimit formed in the joint universe of the
ring and the module.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 05FQ](https://stacks.math.columbia.edu/tag/05FQ)
* [Stacks Project, Tag 0AS7](https://stacks.math.columbia.edu/tag/0AS7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe uR uP uM uM' uQ uN u v w

/-- Being a Mittag-Leffler module transports along a linear equivalence. The two modules may live
in different universes; the universes of the finitely presented source, of the finitely presented
witness and of the test module are untouched. -/
theorem IsMittagLeffler.of_linearEquiv {R : Type uR} [CommRing R] {M : Type uM} {M' : Type uM'}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (h : IsMittagLeffler.{uR, uP, uM, uQ, uN} R M) (e : M ≃ₗ[R] M') :
    IsMittagLeffler.{uR, uP, uM', uQ, uN} R M' := by
  intro P _ _ _ f
  obtain ⟨Q, hQa, hQm, hQfp, g, h₁, h₂⟩ := h P (e.symm.toLinearMap ∘ₗ f)
  have key : ∀ (N : Type uN) [AddCommGroup N] [Module R N],
      LinearMap.ker (TensorProduct.map (e.symm.toLinearMap ∘ₗ f) (LinearMap.id : N →ₗ[R] N)) =
        LinearMap.ker (TensorProduct.map f (LinearMap.id : N →ₗ[R] N)) := by
    intro N _ _
    have hcomp : TensorProduct.map (e.symm.toLinearMap ∘ₗ f) (LinearMap.id : N →ₗ[R] N) =
        TensorProduct.map e.symm.toLinearMap LinearMap.id ∘ₗ
          TensorProduct.map f (LinearMap.id : N →ₗ[R] N) := by
      rw [← TensorProduct.map_comp]; simp
    have hmono : Function.Injective
        (TensorProduct.map e.symm.toLinearMap (LinearMap.id : N →ₗ[R] N)) :=
      (e.symm.rTensor N).injective
    rw [hcomp, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hmono, Submodule.comap_bot]
  exact ⟨Q, hQa, hQm, hQfp, g, fun N _ _ ↦ (key N).ge.trans (h₁ N),
    fun N _ _ ↦ (h₂ N).trans (key N).le⟩

namespace Module

/-- **Stacks 05FQ for free modules.** Let `(A, 𝔪)` be a local ring and let `u : M →ₗ[A] N` be a
map of free `A`-modules. If the induced map `M / 𝔪 M → N / 𝔪 N` is injective, then `u` is
universally injective, that is `u ⊗ id_Q` is injective for every `A`-module `Q`.

This is the case of Stacks 05FQ used in the proof of Stacks 05U7, where both modules are free: a
free module is projective, which is the hypothesis on the source, and flat, which is the
hypothesis on the target. -/
theorem rTensor_injective_of_free_of_injective_mapQ_maximalIdeal {A : Type u} [CommRing A]
    [IsLocalRing A] [Small.{v} A] {M N : Type v} [AddCommGroup M] [Module A M] [Module.Free A M]
    [AddCommGroup N] [Module A N] [Module.Free A N] (u : M →ₗ[A] N)
    (hu : Function.Injective ((maximalIdeal A • (⊤ : Submodule A M)).mapQ
      (maximalIdeal A • (⊤ : Submodule A N)) u
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) u))) :
    ∀ (Q : Type v) [AddCommGroup Q] [Module A Q], Function.Injective (u.rTensor Q) :=
  Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal u hu

variable {A : Type u} [CommRing A] [IsLocalRing A] [Small.{v} A] {J : Type w} [Preorder J]
  [IsDirectedOrder J] [Nonempty J] {F : J ⥤ ModuleCat.{v} A} {c : Cocone F}

/-- **The second half of the proof of Stacks 05U7.** Let `(A, 𝔪)` be a local ring and let
`(F i, u_{i i'})` be a directed system of free `A`-modules indexed by a nonempty directed
preorder, such that every transition map induces an injective map
`F i / 𝔪 F i → F i' / 𝔪 F i'`. Then the colimit of the system is a Mittag-Leffler `A`-module.

Being Mittag-Leffler is spelled out in the intrinsic form of Stacks 059E (1), as in the library's
Stacks 0AS7: every map `f : P → c.pt` from a finitely presented module dominates and is dominated
by a map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `A`-module `N`.

The transition maps are universally injective by Stacks 05FQ and every `F i` is Mittag-Leffler by
Stacks 059R (2), so Stacks 0AS7 applies. -/
theorem mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal
    (hfree : ∀ i, Module.Free A (F.obj i))
    (hinj : ∀ {i j : J} (u : i ⟶ j), Function.Injective
      (Submodule.mapQ
        (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
        (F.map u).hom
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map u).hom)))
    (hc : IsColimit c) :
    ∀ (P : Type v) [AddCommGroup P] [Module A P] [Module.FinitePresentation A P]
        (f : P →ₗ[A] c.pt),
      ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module A Q) (_ : Module.FinitePresentation A Q)
        (g : P →ₗ[A] Q), ∀ (N : Type v) [AddCommGroup N] [Module A N],
          LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
  ModuleCat.mittagLeffler_pt_of_forall_mittagLeffler_of_forall_rTensor_injective
    (fun {i j} u T _ _ ↦ by
      have := hfree i
      have := hfree j
      exact rTensor_injective_of_free_of_injective_mapQ_maximalIdeal (F.map u).hom (hinj u) T)
    (fun i ↦ by
      have := hfree i
      exact Module.mittagLeffler_of_projective A (F.obj i))
    hc

/-- **The second half of the proof of Stacks 05U7**, with the conclusion written using the
predicate `IsMittagLeffler` of Stacks 059F. Let `(A, 𝔪)` be a local ring and let
`(F i, u_{i i'})` be a directed system of free `A`-modules indexed by a nonempty directed
preorder, such that every transition map induces an injective map
`F i / 𝔪 F i → F i' / 𝔪 F i'`. Then the colimit of the system is a Mittag-Leffler
`A`-module. -/
theorem isMittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal
    (hfree : ∀ i, Module.Free A (F.obj i))
    (hinj : ∀ {i j : J} (u : i ⟶ j), Function.Injective
      (Submodule.mapQ
        (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (F.obj j)))
        (F.map u).hom
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map u).hom)))
    (hc : IsColimit c) :
    IsMittagLeffler.{u, v, v, v, v} A c.pt :=
  (isMittagLeffler_def_iff A (c.pt : Type v)).mpr
    (mittagLeffler_pt_of_free_of_injective_mapQ_maximalIdeal hfree hinj hc)

end Module

end
