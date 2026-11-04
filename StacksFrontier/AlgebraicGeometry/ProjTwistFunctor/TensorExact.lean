module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPower
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Preadditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits

/-!
# Exactness of tensoring a sheaf of modules with a fixed sheaf of modules

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)` and let `L` be a sheaf of
`𝒪`-modules. Tensoring with `L` is the endofunctor

`(Stacks.SheafOfModules.Tensor.sheafTensor 𝒪).flip.obj L : ℱ ↦ (ℱ ⊗_p L)^#`

of sheaves of `𝒪`-modules, the canonical sheaf tensor bifunctor evaluated at `L` in its second
variable. This file records its exactness properties.

Unconditionally the functor is *right* exact: it is additive, hence preserves zero morphisms,
and it preserves all colimits, hence every finite colimit. It need not preserve monomorphisms,
so the short-exactness statement is given in three forms of decreasing generality: from
`PreservesMonomorphisms` (flatness of `L`, [Stacks, Tag 05ND]), from the tensor functor being
an equivalence, and from `L` being invertible ([Stacks, Tag 01CS]).

## Main results

* `Stacks.ProjTwistFunctor.additive_tensorRightFunctor`: tensoring with `L` is additive. This
  is an instance, so `CategoryTheory.Functor.PreservesZeroMorphisms`, and therefore
  `CategoryTheory.ShortComplex.map` applied to the functor, is available with no hypothesis
  on `L`.
* `Stacks.ProjTwistFunctor.preservesFiniteColimits_tensorRightFunctor`: tensoring with `L` is
  right exact, with no hypothesis on `L`. This is [Stacks, Tag 05NB] moved across the
  braiding.
* `Stacks.ProjTwistFunctor.exact_map_and_epi_of_shortExact`: tensoring a short exact sequence
  with `L` gives an exact short complex whose second map is an epimorphism, with no hypothesis
  on `L`.
* `Stacks.ProjTwistFunctor.shortExact_map_tensorRightFunctor_of_preservesMonomorphisms`:
  **tensoring with a flat sheaf of modules is exact.**
* `Stacks.ProjTwistFunctor.shortExact_map_tensorRightFunctor`: the same from the tensor
  functor being an equivalence.
* `Stacks.ProjTwistFunctor.isEquivalence_tensorRightFunctor_of_isInvertible`: an invertible
  sheaf of modules has an equivalence for its tensor functor, so **tensoring with an
  invertible sheaf of modules is exact**.

## Implementation notes

The tensor functor is, after unfolding, the composite of the forgetful functor to presheaves of
modules, `MonoidalCategory.tensorRight` on presheaves of modules, and sheafification. Mathlib's
additivity instance for the middle factor is stated over a
`CategoryTheory.MonoidalPreadditive` category, which for `PresheafOfModules` is
`Stacks.ProjTwistFunctor.monoidalPreadditive`.

The sheaf `L` tensored with is typed over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`, while the canonical
bifunctor is typed over `Stacks.SheafOfModules.Tensor.ringSheaf ⟨𝒪, _⟩`; the two are equal by
unfolding but not syntactically, and instance search does not unfold the ordinary definition
`Stacks.SheafOfModules.Tensor.ringSheaf`. `CategoryTheory.ShortComplex.map` takes its source
category from the short complex, so the additivity instance and every short complex below are
stated over `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf ⟨𝒪, _⟩)`, the category the
canonical bifunctor acts on, and the zero-morphism instance `ShortComplex.map` asks for is then
found directly.

Right exactness is `Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits`
([Stacks, Tag 05NB]) transported along the braiding
`Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight`. That statement is for
`R : Sheaf J CommRingCat`, so the right-exactness section takes a sheaf of commutative rings,
while the additivity section needs only the presheaf `𝒪` and the sheaf condition on its
composite with `forget₂ CommRingCat RingCat`.

No tag attribute is attached: Tag 05NB and Tag 05ND are stated elsewhere, and the exactness
statements here are a consequence rather than the statement of any tag.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 05ND](https://stacks.math.columbia.edu/tag/05ND)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u w

namespace Stacks.ProjTwistFunctor

section Additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Tensoring with a fixed sheaf of modules is additive.** -/
instance additive_tensorRightFunctor
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Functor.Additive
      (C := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩))
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          L) := by
  let : MonoidalCategory
      (PresheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) := by
    change MonoidalCategory
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    infer_instance
  have : Functor.Additive (Stacks.SheafOfModules.TensorSheafification.sheafify O hO) :=
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).left_adjoint_additive
  have : MonoidalPreadditive
      (PresheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj) :=
    inferInstanceAs (MonoidalPreadditive
      (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
  change Functor.Additive
    (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
      MonoidalCategory.tensorRight L.val ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO)
  infer_instance

/-- **Tensoring with an invertible sheaf of modules is an equivalence**, tensoring on the
right. -/
theorem isEquivalence_tensorRightFunctor_of_isInvertible
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [Stacks.SheafOfModules.IsInvertible O hO L] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L)).IsEquivalence := by
  rw [Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor_iff]
  exact inferInstanceAs (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj
        L)).IsEquivalence

/-- If tensoring with `L` is an equivalence, it carries short exact sequences to short exact
sequences. By `Stacks.ProjTwistFunctor.isEquivalence_tensorRightFunctor_of_isInvertible` this
holds for an invertible `L`. -/
theorem shortExact_map_tensorRightFunctor
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L)).IsEquivalence]
    {S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩))}
    (hS : S.ShortExact) :
    (S.map (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L))).ShortExact :=
  hS.map_of_exact _

end Additive

section RightExact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
  (hR : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf R.obj))

/-- **Tensoring with a fixed sheaf of modules is right exact**, with no hypothesis on the
sheaf tensored with: it preserves every finite colimit. This is [Stacks, Tag 05NB] moved across
the braiding of the tensor product. -/
theorem preservesFiniteColimits_tensorRightFunctor
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj hR)) :
    PreservesFiniteColimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).flip.obj
        L)) := by
  have : PreservesColimitsOfSize.{w, w}
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).obj L)) :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits.{u, v, w, w, w} J
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩ L
  have : PreservesFiniteColimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).obj L)) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact preservesFiniteColimits_of_natIso
    (Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight R.obj hR L)

/-- Tensoring a short exact sequence with any sheaf of modules gives an exact short complex
whose second map is an epimorphism. -/
theorem exact_map_and_epi_of_shortExact
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj hR))
    {S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩))}
    (hS : S.ShortExact) :
    (S.map (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).flip.obj
        L))).Exact ∧
      Epi ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).flip.obj
        L)).map S.g) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).1
    (preservesFiniteColimits_tensorRightFunctor R hR L) S hS

/-- **Tensoring with a flat sheaf of modules is exact**: if tensoring with `L` preserves
monomorphisms (flatness of `L`, [Stacks, Tag 05ND]), it carries short exact sequences to short
exact sequences. -/
theorem shortExact_map_tensorRightFunctor_of_preservesMonomorphisms
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj hR))
    [(((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).flip.obj
        L)).PreservesMonomorphisms]
    {S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩))}
    (hS : S.ShortExact) :
    (S.map (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).flip.obj
        L))).ShortExact := by
  let T := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨R.obj, Presheaf.isSheaf_of_isSheaf_comp _ R.obj (forget₂ CommRingCat RingCat) hR⟩).flip.obj
        L)
  have : PreservesFiniteColimits T := preservesFiniteColimits_tensorRightFunctor R hR L
  have : T.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels T
  have : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesHomology T
  exact hS.map_of_exact T

end RightExact

end Stacks.ProjTwistFunctor

end
