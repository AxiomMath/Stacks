module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Localization
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.MorphismProperty.NatIsoTransport

/-!
# Tensoring with a K-flat complex preserves quasi-isomorphisms

Let `(C, 𝒪)` be a ringed site and `K^•` a K-flat cochain complex of `𝒪`-modules. Then
`F^• ↦ Tot(F^• ⊗_𝒪 K^•)` carries quasi-isomorphisms to quasi-isomorphisms on the homotopy
category `K(Mod(𝒪))`. This is [Stacks, Tag 06YA], stated there for a ringed space.

## Main results

* `Stacks.SheafOfModules.IsKFlat.quasiIso_le_inverseImage`: [Stacks, Tag 06YA] on the homotopy
  category, as a containment of morphism properties.
* `Stacks.SheafOfModules.IsKFlat.quasiIso_rightTensorComplex_map`: the same statement at the
  level of cochain complexes, which is the form a consumer applies.

## Implementation notes

The proof is the Stacks proof. Quasi-isomorphisms of `K(Mod(𝒪))` are the morphisms attached by
`ObjectProperty.trW` to the triangulated subcategory of acyclic objects
(`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`), so it suffices to know that the functor
sends acyclic objects to acyclic objects — which is exactly K-flatness of `K` — and that it is an
exact functor of triangulated categories, which is [Stacks, Tag 06YM]
(`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated` at the bifunctor `⊗_𝒪`). The
  passage from
objects to morphisms is `ObjectProperty.trW_monotone` with `ObjectProperty.inverseImage_trW_iff`.

The hypotheses are those of `Stacks.SheafOfModules.IsKFlat` with `HasWeakSheafify` strengthened
to `HasSheafify`, which is what makes `Mod(𝒪)` abelian (the `Abelian (SheafOfModules R)`
instance of `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`); `HasSheafify` is a class implying
`HasWeakSheafify`, so nothing else changes. Abelianness is not a choice here: the acyclic
subcategory, the quasi-isomorphisms and their identification as a `trW` class are all stated for
an abelian category, and the Stacks source works in `Mod(𝒪)`, abelian by its standing convention.

The cochain-level corollary needs no transport along
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors`: `Φ` is a
  `CategoryTheory.Quotient.lift`, so
`Φ.map (quotient.map f)` and `quotient.map (Tot(f ⊗_𝒪 K))` are the same term, and
`HomotopyCategory.quotient_map_mem_quasiIso_iff` closes the gap between a quasi-isomorphism of
`K(Mod(𝒪))` and one of complexes. The two `change`s inside the proof of the first statement are
the same definitional identity read on objects.

## References

* [Stacks Project, Tag 06YA](https://stacks.math.columbia.edu/tag/06YA)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)]

/-- A triangulated functor on `K(A)` carrying acyclic complexes to acyclic complexes
preserves quasi-isomorphisms. -/
private theorem quasiIso_le_inverseImage_of_acyclic {A : Type*} [Category A] [Abelian A]
    (Φ : HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory A (ComplexShape.up ℤ))
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (G : CochainComplex A ℤ → CochainComplex A ℤ)
    (hΦ : ∀ L, Φ.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (G L))
    (hG : ∀ L, L.Acyclic → (G L).Acyclic) :
    HomotopyCategory.quasiIso A (ComplexShape.up ℤ) ≤
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage Φ := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  have hobj : HomotopyCategory.subcategoryAcyclic A ≤
      (HomotopyCategory.subcategoryAcyclic A).inverseImage Φ := by
    intro X hX
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    rw [ObjectProperty.prop_inverseImage_iff, hΦ]
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hX ⊢
    exact hG L hX
  intro X Y f hf
  rw [MorphismProperty.inverseImage_iff,
    ← ObjectProperty.inverseImage_trW_iff (P := HomotopyCategory.subcategoryAcyclic A) (F := Φ)]
  exact ObjectProperty.trW_monotone hobj _ hf

/-- **[Stacks, Tag 06YA].** For a K-flat complex `K` of `𝒪`-modules, the exact functor
`F ↦ Tot(F ⊗_𝒪 K)` of `K(Mod(𝒪))` carries quasi-isomorphisms to quasi-isomorphisms. -/
@[stacks 06YA "on the homotopy category, as the tag states it"]
theorem IsKFlat.quasiIso_le_inverseImage
    (K : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K) :
    HomotopyCategory.quasiIso
        (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ) ≤
      (HomotopyCategory.quasiIso
          (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R))
          (ComplexShape.up ℤ)).inverseImage
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor R) K) := by
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
    (Stacks.SheafOfModules.Tensor.sheafTensor R) K
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor R) K
  exact quasiIso_le_inverseImage_of_acyclic _ _ (fun _ => rfl) hK

/-- **[Stacks, Tag 06YA] at the level of complexes.** For a K-flat complex `K` of `𝒪`-modules
and a quasi-isomorphism `f : F₁ ⟶ F₂` of complexes of `𝒪`-modules, the induced morphism
`Tot(F₁ ⊗_𝒪 K) ⟶ Tot(F₂ ⊗_𝒪 K)` is a quasi-isomorphism.

The hypothesis is explicit rather than an instance: with the tensor-total functor applied to a
consumer's own factorization, an instance argument is synthesized at a different spelling of the
same type. -/
@[stacks 06YA "at the level of complexes rather than of the homotopy category"]
theorem IsKFlat.quasiIso_rightTensorComplex_map
    (K : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K)
    {F₁ F₂ : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : F₁ ⟶ F₂) (hf : QuasiIso f) :
    QuasiIso ((Stacks.SheafOfModules.Tensor.rightTensorComplex R K).map f) :=
  (HomotopyCategory.quotient_map_mem_quasiIso_iff
    ((Stacks.SheafOfModules.Tensor.rightTensorComplex R K).map f)).1
    (IsKFlat.quasiIso_le_inverseImage R K hK _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf))

end Stacks.SheafOfModules

-- ===== merged from StacksDraft.Ch21.Sec17.KFlatTensorQuasiIso =====

/-!
# Tensoring with a K-flat complex preserves quasi-isomorphisms

Let `(C, O)` be a ringed site and `K` a K-flat complex of `O`-modules. Then the functor
`F ↦ Tot(F ⊗_O K)` on the homotopy category `K(Mod(O))` carries quasi-isomorphisms to
quasi-isomorphisms, and so does `F ↦ Tot(K ⊗_O F)`. This is Stacks 06YP.

The argument is the one in the source. A morphism of `K(Mod(O))` is a quasi-isomorphism
exactly when its cone is acyclic, which Mathlib expresses as
`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`: the quasi-isomorphisms are the class
generated by the acyclic objects. Tensoring with `K` and totalising is an exact functor of
triangulated categories — that is Stacks 06YM, proved as
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated` — so it carries that
  generated class
into the class generated by the images of the acyclic objects; and those images are acyclic,
which is precisely K-flatness of `K`.

## Main results

* `Stacks.SheafOfModules.IsKFlat.tensorRight_preserves_quasiIso`: `F ↦ Tot(F ⊗_O K)`
  preserves quasi-isomorphisms, for `K` K-flat.
* `Stacks.SheafOfModules.IsKFlat.tensorLeft_preserves_quasiIso`: `F ↦ Tot(K ⊗_O F)`
  preserves quasi-isomorphisms, for `K` K-flat.

## Implementation notes

The two functors on the homotopy category are the ones Stacks 06YM provides,
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR` for the K-flat complex in the right tensor
  slot — the
slot in which `Stacks.SheafOfModules.IsKFlat` is stated — and
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi` for the left. The left-hand statement needs
  that
K-flatness is two-sided, which is `Stacks.SheafOfModules.IsKFlat.acyclic_tensor_left`.

Preservation of quasi-isomorphisms is stated as containment of the quasi-isomorphisms in
their inverse image, which is the form the localisation API consumes.

## References

* [Stacks Project, Tag 06YP](https://stacks.math.columbia.edu/tag/06YP)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- Tensoring with a K-flat complex on the right and totalising preserves
quasi-isomorphisms of the homotopy category. -/
@[stacks 06YP "the K-flat complex as right tensor factor"]
theorem IsKFlat.tensorRight_preserves_quasiIso
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K) :
    HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ) ≤
      MorphismProperty.inverseImage
        (HomotopyCategory.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ))
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
          (Stacks.SheafOfModules.Tensor.sheafTensor R) K) :=
  IsKFlat.quasiIso_le_inverseImage R K hK

/-- Tensoring with a K-flat complex on the left and totalising preserves
quasi-isomorphisms of the homotopy category. -/
@[stacks 06YP "the K-flat complex as left tensor factor"]
theorem IsKFlat.tensorLeft_preserves_quasiIso
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K) :
    HomotopyCategory.quasiIso
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ) ≤
      MorphismProperty.inverseImage
        (HomotopyCategory.quasiIso
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ))
        (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
          (Stacks.SheafOfModules.Tensor.sheafTensor R) K) := by
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
    (Stacks.SheafOfModules.Tensor.sheafTensor R) K
  let _ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
    (Stacks.SheafOfModules.Tensor.sheafTensor R) K
  exact quasiIso_le_inverseImage_of_acyclic _ _ (fun _ => rfl) (IsKFlat.acyclic_tensor_left R hK)

end Stacks.SheafOfModules

end

-- ===== merged from StacksDraft.Ch21.Sec17.KFlatTensorQuasiIsoComplexes =====

/-!
# Stacks 06YP at the level of complexes

Stacks 06YP says that tensoring with a K-flat complex carries quasi-isomorphisms to
quasi-isomorphisms; `Stacks.SheafOfModules.IsKFlat.tensorRight_preserves_quasiIso` states it
for the functor on the homotopy category that Stacks 06YM provides. This file restates it for
the total tensor complex of two complexes, which is the form a construction working with
actual complexes consumes.

## Main results

* `Stacks.SheafOfModules.IsKFlat.quasiIso_tensorComplex_map_app`: for `K` K-flat and `f` a
  quasi-isomorphism, `Tot(f ⊗ 1_K)` is a quasi-isomorphism.
* `Stacks.SheafOfModules.IsKFlat.quasiIso_tensorComplex_obj_map`: for `K` K-flat and `g` a
  quasi-isomorphism, `Tot(1_K ⊗ g)` is a quasi-isomorphism.
* `Stacks.SheafOfModules.IsKFlat.quasiIso_mapBifunctorMap_id_right` and
  `quasiIso_mapBifunctorMap_id_left`: the same two statements in the
  `HomologicalComplex.mapBifunctorMap` spelling.

## Implementation notes

Both statements are given in two spellings of the same morphism. The one through
`Stacks.SheafOfModules.Tensor.tensorComplex`, the induced bifunctor on complexes, is primary: it is
  the one
the descent to the derived category consumes, and it is what the 06YM factorisation
isomorphism produces directly. The `HomologicalComplex.mapBifunctorMap` spelling is derived
from it by `CategoryTheory.Functor.map₂HomologicalComplex_map_app`; it is the one that
composes in both variables at once.

The passage between the homotopy category and complexes is Mathlib's
`HomotopyCategory.quotient_map_mem_quasiIso_iff`, and the identification of the descended
functor of 06YM with the total tensor complex is its factorisation isomorphism
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors`, transported with
`CategoryTheory.MorphismProperty.of_natIso_map`. The morphism
`Tot(f ⊗ 1_K) = HomologicalComplex.mapBifunctorMap f (𝟙 K) _ _` is definitionally the value of
that functor on `f`.

## References

* [Stacks Project, Tag 06YP](https://stacks.math.columbia.edu/tag/06YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- For `K` K-flat and `f` a quasi-isomorphism, the total tensor product `Tot(f ⊗ 1_K)` is a
quasi-isomorphism. -/
@[stacks 06YP "for complexes, the K-flat complex as right tensor factor"]
theorem IsKFlat.quasiIso_tensorComplex_map_app
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K)
    {A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : A ⟶ B) (hf : QuasiIso f) :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex R).map f).app K) := by
  have h0 : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
    (MorphismProperty.of_natIso_map
      (e := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
        (Stacks.SheafOfModules.Tensor.sheafTensor R) K)
      (IsKFlat.tensorRight_preserves_quasiIso R K hK _ h0))

/-- For `K` K-flat and `g` a quasi-isomorphism, the total tensor product `Tot(1_K ⊗ g)` is a
quasi-isomorphism. -/
@[stacks 06YP "for complexes, the K-flat complex as left tensor factor"]
theorem IsKFlat.quasiIso_tensorComplex_obj_map
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K)
    {A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (g : A ⟶ B) (hg : QuasiIso g) :
    QuasiIso (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K).map g) := by
  have h0 : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map g) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 hg
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
    (MorphismProperty.of_natIso_map
      (e := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
        (Stacks.SheafOfModules.Tensor.sheafTensor R) K)
      (IsKFlat.tensorLeft_preserves_quasiIso R K hK _ h0))

/-- The `HomologicalComplex.mapBifunctorMap` spelling of
`Stacks.SheafOfModules.IsKFlat.quasiIso_tensorComplex_map_app`. -/
@[stacks 06YP "for complexes, right tensor factor, mapBifunctorMap spelling"]
theorem IsKFlat.quasiIso_mapBifunctorMap_id_right
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K)
    {A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (f : A ⟶ B) (hf : QuasiIso f) :
    QuasiIso (HomologicalComplex.mapBifunctorMap f (𝟙 K)
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)) := by
  rw [← Functor.map₂HomologicalComplex_map_app]
  exact IsKFlat.quasiIso_tensorComplex_map_app R K hK f hf

/-- The `HomologicalComplex.mapBifunctorMap` spelling of
`Stacks.SheafOfModules.IsKFlat.quasiIso_tensorComplex_obj_map`. -/
@[stacks 06YP "for complexes, left tensor factor, mapBifunctorMap spelling"]
theorem IsKFlat.quasiIso_mapBifunctorMap_id_left
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (hK : IsKFlat R K)
    {A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (g : A ⟶ B) (hg : QuasiIso g) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) g
      (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)) := by
  rw [← Functor.map₂HomologicalComplex_obj_map]
  exact IsKFlat.quasiIso_tensorComplex_obj_map R K hK g hg

end Stacks.SheafOfModules

end
