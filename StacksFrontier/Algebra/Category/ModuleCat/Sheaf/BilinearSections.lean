module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear

/-!
# Bilinear maps of sheaves of modules, sectionwise

Let `O` be a sheaf of commutative rings on a site and let `A`, `B`, `N` be sheaves of `O`-modules.
A map `q : A × B → N` of the underlying sheaves of sets is a bilinear map of sheaves of
`O`-modules when, for every object `U`, the induced map `A(U) × B(U) → N(U)` is an
`O(U)`-bilinear map of modules. This is the definition of the section [Stacks, Tag 0GIG].

`Stacks.SheafOfModules.IsBilinearPairing` spells this condition out as the four identities of a
bilinear map, which makes sense over a not necessarily commutative sheaf of rings. Over a sheaf of
commutative rings, the theorem of this file identifies it with the existence, over every object,
of an `O(U)`-bilinear map `A(U) →ₗ B(U) →ₗ N(U)` in the sense of Mathlib whose values are those of
`q`.

## Main results

* `Stacks.SheafOfModules.isBilinearPairing_iff_forall_exists_linearMap`: a map of sheaves of sets
  is a bilinear map of sheaves of modules if and only if it is given over every object by an
  `O(U)`-bilinear map.

## References

* [Stacks Project, Tag 0GIG](https://stacks.math.columbia.edu/tag/0GIG)
-/

@[expose] public noncomputable section

open CategoryTheory Limits CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O : Sheaf J CommRingCat.{w}} {A B N : _root_.SheafOfModules.{w} (Tensor.ringSheaf O)}

/-- **Bilinearity is bilinearity on sections.** A map `q : A × B → N` of the underlying sheaves of
sets of three sheaves of modules over a sheaf of commutative rings `O` is a bilinear map of sheaves
of `O`-modules if and only if, for every object `U`, the induced map `A(U) × B(U) → N(U)` is an
`O(U)`-bilinear map of modules. -/
@[stacks 0GIG "the definition of the section: a bilinear map `F x G -> H` of sheaves of
`O_X`-modules is a map of sheaves of sets such that for every open `U` the induced map
`F(U) x G(U) -> H(U)` is an `O_X(U)`-bilinear map of modules; here `IsBilinearPairing`, the
condition the rest of the section is phrased in, is shown to be exactly that, with `O_X(U)`-bilinear
meaning given by an `O_X(U)`-linear map `F(U) -> Hom(G(U), H(U))`. Over an arbitrary site rather
than only the opens of a ringed space"]
theorem isBilinearPairing_iff_forall_exists_linearMap
    (q : moduleSheaf (Tensor.ringSheaf O) A ⨯ moduleSheaf (Tensor.ringSheaf O) B ⟶
      moduleSheaf (Tensor.ringSheaf O) N) :
    IsBilinearPairing (Tensor.ringSheaf O) q ↔
      ∀ U : Cᵒᵖ, ∃ φ : A.val.obj U →ₗ[(Tensor.ringSheaf O).obj.obj U]
          B.val.obj U →ₗ[(Tensor.ringSheaf O).obj.obj U] N.val.obj U,
        ∀ (a : A.val.obj U) (b : B.val.obj U), φ a b = pairingApp (Tensor.ringSheaf O) q U a b := by
  refine ⟨fun h U ↦ ⟨LinearMap.mk₂ _ (fun a b ↦ pairingApp (Tensor.ringSheaf O) q U a b)
    (h.add_left U) (h.smul_left U) (h.add_right U) (h.smul_right U), fun _ _ ↦ rfl⟩,
    fun h ↦ ?_⟩
  choose φ hφ using h
  refine ⟨fun U a a' b ↦ ?_, fun U a b b' ↦ ?_, fun U r a b ↦ ?_, fun U r a b ↦ ?_⟩
  · change A.val.obj U at a a'
    change B.val.obj U at b
    exact (hφ U (a + a') b).symm.trans (by rw [map_add, LinearMap.add_apply, hφ, hφ]; rfl)
  · change A.val.obj U at a
    change B.val.obj U at b b'
    exact (hφ U a (b + b')).symm.trans (by rw [map_add, hφ, hφ]; rfl)
  · change (Tensor.ringSheaf O).obj.obj U at r
    change A.val.obj U at a
    change B.val.obj U at b
    exact (hφ U (r • a) b).symm.trans (by rw [map_smul, LinearMap.smul_apply, hφ]; rfl)
  · change (Tensor.ringSheaf O).obj.obj U at r
    change A.val.obj U at a
    change B.val.obj U at b
    exact (hφ U a (r • b)).symm.trans (by rw [map_smul, hφ]; rfl)

end Stacks.SheafOfModules
