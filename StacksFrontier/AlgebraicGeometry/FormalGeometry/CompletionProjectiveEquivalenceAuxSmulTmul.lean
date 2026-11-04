module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Moving a scalar across the sectionwise tensor product of two sheaves of modules

The homogeneous pieces of the free graded module `F ⊗ 𝓟(-d)` are sheafifications of the
*sectionwise* tensor product, whose sections over an object `U` of the site are
`Γ(F, U) ⊗_{𝒪(U)} Γ(𝓟_{n-d}, U)`. Rewriting inside that tensor product is where the two
spellings of the structure ring collide.

A sheaf of modules on a scheme is indexed by `AlgebraicGeometry.Scheme.ringCatSheaf`, while the
sectionwise tensor product is formed over
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` applied to the structure
presheaf. The two are the same sheaf of rings — definitionally, by
`Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf` — but not syntactically, and the module
structure on the sections of an `𝒪_X`-module is registered at the first spelling only (Mathlib's
`AlgebraicGeometry.Scheme.Modules.instModule`, which is what the `Γ(-, -)` notation sees). So the
`TensorProduct.CompatibleSMul` instance that `TensorProduct.smul_tmul` needs is *not* found at a
use site phrased with `Γ(-, -)`: the scalar is typed at one spelling and the tensor product is
formed at the other, and the two do not even share a `CommSemiring` instance, `ringCatSheaf`
being a sheaf of `RingCat`.

This file is the single fix. Both statements below are proved on an arbitrary ringed site, where
the structure ring has only one spelling and the instances are therefore found; a scheme-level
consumer obtains them by application, the two spellings being definitionally equal. Nothing here
is specific to a scheme or to the grading, and nothing downstream needs to mention
`TensorProduct.CompatibleSMul` again.

## Main results

* `Stacks.Coherent.smul_tmul_section` — **a scalar moves across a pure tensor of local
  sections**, `(r · g) ⊗ a = g ⊗ (r · a)`.
* `Stacks.Coherent.map_tmul_mem_of_sum_smul` — **the form the generation argument consumes.**
  If a section `g` of `F` is a finite combination `∑ᵢ cᵢ · gᵢ` of sections drawn from a finite
  set, then for any additive map `φ` out of the sectionwise tensor product and any additive
  subgroup `S` of its target, `φ(g ⊗ a)` lies in `S` as soon as every `φ(gᵢ ⊗ (cᵢ · a))` does.
  Stating the conclusion as a membership rather than as an identity of tensors is what keeps the
  rewriting on this side of the spelling boundary: the consumer only ever applies `φ` to pure
  tensors.

## References

* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.SheafOfModules.TensorSheafification

open scoped TensorProduct

universe w v u

namespace Stacks.Coherent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  (F G : SheafOfModules.{w} (⟨structureRingPresheaf 𝒪, h𝒪⟩ : Sheaf J RingCat.{w}))
  (U : Cᵒᵖ)

/-- **A scalar moves across a pure tensor of local sections**, `(r · g) ⊗ a = g ⊗ (r · a)`.

This is `TensorProduct.smul_tmul` for the action of the structure ring on itself, whose
`TensorProduct.CompatibleSMul` instance comes from `IsScalarTower.left`. The content of the
statement is that it is phrased at the only spelling of the structure ring at which that
instance is found; see the module documentation. -/
public theorem smul_tmul_section (r : (structureRingPresheaf 𝒪).obj U) (g : F.val.obj U)
    (a : G.val.obj U) :
    (r • g) ⊗ₜ[(structureRingPresheaf 𝒪).obj U] a = g ⊗ₜ (r • a) :=
  TensorProduct.smul_tmul r g a

/-- **Reducing a pure tensor to a finite family of generators of the left factor.** Let `s` be a
finite set of sections of `F` over `U` and `c` a family of scalars with `∑_{i ∈ s} cᵢ · i = g`.
Then for an additive map `φ` out of the sectionwise tensor product and an additive subgroup `S`
of its target, `φ(g ⊗ a)` lies in `S` as soon as `φ(i ⊗ (cᵢ · a))` does for every `i ∈ s`.

The scalar is moved to the right factor by `Stacks.Coherent.smul_tmul_section`, which is the
whole point: the hypothesis speaks only of pure tensors whose left factor is one of the chosen
generators, and that is what a generating family for the free graded module supplies. -/
public theorem map_tmul_mem_of_sum_smul {T : Type*} [AddCommGroup T]
    (φ : (F.val.obj U ⊗[(structureRingPresheaf 𝒪).obj U] G.val.obj U) →+ T) (S : AddSubgroup T)
    (s : Finset (F.val.obj U)) (c : F.val.obj U → (structureRingPresheaf 𝒪).obj U)
    (g : F.val.obj U) (hg : ∑ i ∈ s, c i • i = g) (a : G.val.obj U)
    (h : ∀ i ∈ s, φ (i ⊗ₜ (c i • a)) ∈ S) :
    φ (g ⊗ₜ a) ∈ S := by
  subst hg
  rw [TensorProduct.sum_tmul, map_sum]
  refine AddSubgroup.sum_mem _ fun i hi => ?_
  rw [smul_tmul_section 𝒪 h𝒪 F G U (c i) i a]
  exact h i hi

end Stacks.Coherent

end
