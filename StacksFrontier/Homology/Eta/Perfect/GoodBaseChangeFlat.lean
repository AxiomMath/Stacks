module

public import StacksFrontier.Homology.Eta.Perfect.GoodBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat base change of the décalage, as an isomorphism of complexes

Let `A → B` be a flat map of commutative rings, let `f ∈ A` with image `g = algebraMap A B f`,
and let `K` be a cochain complex of `A`-modules.  More on Algebra, Tag 0GSR says that the
décalage commutes with flat base change.  `Stacks.Eta.BaseChange.etaBaseChangeTerm_eq_fetaTerm`
states that as an equality of two `B`-submodules of one ambient localization; this file turns it
into the statement that the canonical comparison chain map

`B ⊗_A (η_f K) ⟶ η_g (B ⊗_A K)`

of `Stacks.Eta.GoodBaseChange.etaBaseChangeMap` is an isomorphism of complexes of `B`-modules.

## Main results

* `Stacks.Eta.GoodBaseChange.fetaTerm_baseChange_eq_span_image`: the degree-`i` décalage term of
  the base-changed differential is the `B`-span of the image of the degree-`i` décalage term —
  the bare-differential form of `Stacks.Eta.BaseChange.fetaTerm_baseChange_eq`.
* `Stacks.Eta.GoodBaseChange.bijective_psiTermMap_of_flat`: the degreewise comparison is
  bijective.
* `Stacks.Eta.GoodBaseChange.isIso_etaBaseChangeMap_of_flat`: **Tag 0GSR as an isomorphism of
  complexes.**

## Implementation notes

Both halves of the bijectivity come from one identity.  The underlying map of the degreewise
comparison `Stacks.Eta.GoodBaseChange.psiTermMap` is the localization–base-change isomorphism
`Stacks.Eta.BaseChange.psiEquiv` precomposed with the base change of the inclusion of the
décalage term, so its range is the image under `psiEquiv` of
`Submodule.baseChange B (η_f d)^i`, which `Stacks.Eta.BaseChange.span_image_etaBCPsi` identifies
with the `B`-span of the image — and that span is the whole target by Tag 0GSR.  Injectivity is
flatness again: `Submodule.toBaseChange_injective`.

Unlike `Stacks.Eta.GoodBaseChange.isIso_etaBaseChangeMap_toCochainComplex`, which is Tag 0F7X
and asks for a bounded complex of finite free modules with principal determinantal ideals over
an arbitrary ring map, the hypothesis here is flatness of the ring map and the complex is
arbitrary.  Neither statement implies the other.

## References

* [Stacks Project, Tag 0GSR](https://stacks.math.columbia.edu/tag/0GSR)
-/

@[expose] public noncomputable section

open CategoryTheory EtaPow Stacks.Eta.BaseChange

open scoped TensorProduct

universe u

namespace Stacks.Eta.GoodBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Tag 0GSR for a bare differential.**  For `A → B` flat, the degree-`i` décalage term of
the base change of an `A`-linear map `d` with respect to the image of `f` is the `B`-span of the
image of the degree-`i` décalage term of `d` under the comparison
`Stacks.Eta.BaseChange.etaBCPsi`.

This is `Stacks.Eta.BaseChange.fetaTerm_baseChange_eq` with the two consecutive differentials of
a complex replaced by a single linear map; the proof is the same composition of the three
flat-base-change steps for `f^i M`, for the preimage of `f^{i+1} N`, and for the
intersection. -/
theorem fetaTerm_baseChange_eq_span_image (f : A) [Module.Flat A B] {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) (i : ℤ) :
    fetaTerm (algebraMap A B f) (LinearMap.baseChange B d) i =
      Submodule.span B ((etaBCPsi (B := B) f M) '' (fetaTerm f d i : Set (Loc f M))) := by
  rw [fetaTerm_eq_inf (f := algebraMap A B f) (LinearMap.baseChange B d) i,
    fpowSub_baseChange_eq f M i, comap_fLoc_baseChange_eq f d (i + 1),
    ← span_image_etaBCPsi_inf f (fpowSub f M i) ((fpowSub f N (i + 1)).comap (fLoc f d)),
    fetaTerm_eq_inf d i]

/-- **The degreewise flat-base-change comparison of the décalage is bijective.**  For `A → B`
flat the comparison `B ⊗_A (η_f d)^i ⟶ (η_g (B ⊗_A d))^i` of
`Stacks.Eta.GoodBaseChange.psiTermMap` is a bijection: it is surjective because its range is the
`B`-span of the image of the décalage term, which is the whole target by Tag 0GSR, and injective
because base change along a flat ring map keeps the inclusion of a submodule injective. -/
theorem bijective_psiTermMap_of_flat (f : A) [Module.Flat A B] {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) (i : ℤ) :
    Function.Bijective (psiTermMap (B := B) f d i) := by
  have hsub : Function.Injective
      (LinearMap.baseChange B (fetaTerm f d i).subtype) := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := B)
      (fetaTerm f d i).subtype (Submodule.injective_subtype _)
    rwa [← LinearMap.baseChange_eq_lTensor] at h
  refine ⟨fun x y hxy => hsub ((psiEquiv (B := B) f M).injective (congrArg Subtype.val hxy)), ?_⟩
  intro y
  have hy : (y : Loc (algebraMap A B f) (B ⊗[A] M)) ∈
      Submodule.map (psiEquiv (B := B) f M : _ →ₗ[B] _)
        (Submodule.baseChange B (fetaTerm f d i)) := by
    rw [← span_image_etaBCPsi f M (fetaTerm f d i),
      ← fetaTerm_baseChange_eq_span_image f d i]
    exact y.2
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨x, hx⟩ := Submodule.toBaseChange_surjective' B (fetaTerm f d i) hz
  have hx' : LinearMap.baseChange B (fetaTerm f d i).subtype x = z := hx
  refine ⟨x, Subtype.ext ?_⟩
  change (psiEquiv (B := B) f M) (LinearMap.baseChange B (fetaTerm f d i).subtype x) = _
  rw [hx']
  exact hzy

/-- **More on Algebra, Tag 0GSR as an isomorphism of complexes.**  Let `A → B` be a flat map of
commutative rings, let `f ∈ A` with image `g = algebraMap A B f`, and let `K` be a cochain
complex of `A`-modules.  Then the canonical comparison

`B ⊗_A (η_f K) ⟶ η_g (B ⊗_A K)`

is an isomorphism of complexes of `B`-modules: the décalage commutes with flat base change.

The tag itself, `Stacks.Eta.BaseChange.etaBaseChangeTerm_eq_fetaTerm`, states this as an
equality of `B`-submodules of one ambient localization in each degree; what is added here is
that the comparison realizing that equality is a degreewise bijection, which is
`Stacks.Eta.GoodBaseChange.bijective_psiTermMap_of_flat`. -/
@[stacks 0GSR "the comparison `B ⊗_A (η_f K) ⟶ η_g (B ⊗_A K)` is an isomorphism of complexes, \
for a flat ring map and an arbitrary cochain complex"]
theorem isIso_etaBaseChangeMap_of_flat (f : A) [Module.Flat A B]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsIso (etaBaseChangeMap (B := B) f K) := by
  have h : ∀ n : ℤ, IsIso ((etaBaseChangeMap (B := B) f K).f n) := by
    intro i
    rw [etaBaseChangeMap_f]
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_psiTermMap_of_flat f (K.d i (i + 1)).hom i)
  exact HomologicalComplex.Hom.isIso_of_components _

end Stacks.Eta.GoodBaseChange

end
