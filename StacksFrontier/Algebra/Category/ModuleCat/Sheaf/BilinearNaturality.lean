module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor
public import StacksCore.Tactic.StacksAttribute

/-! # Naturality in the target of the bilinear-pairing bijections

The three bijections that make up the chain of Stacks 03EL —
`Stacks.SheafOfModules.bilinearEquivTensorHom` (the universal property of the tensor product
sheaf, used twice) and `Stacks.SheafOfModules.inverseImageBilinearEquiv` (the inverse image of a
bilinear pairing) — are stated at a fixed sheaf of modules `N` of values. The Yoneda step which
turns the composite chain into an isomorphism of sheaves of modules needs them to be natural in
`N`, and that is what this file supplies.

In each case naturality is with respect to post-composition with a morphism `k : N ⟶ N'` of
sheaves of modules, read on the underlying sheaves of sets as
`(Sheaf.moduleSheafFunctor R).map k`; on the inverse-image side the matching operation
downstairs is the direct image `(directImageModules f O).map k` of `k`.

## Main results

* `Stacks.SheafOfModules.IsBilinearPairing.comp`: a bilinear pairing composed with a morphism
  of sheaves of modules is bilinear. This is what makes post-composition an operation on
  `Bilin_O(A × B, -)` at all.
* `Stacks.SheafOfModules.bilinearEquivPresheafTensorHom_naturality` and
  `Stacks.SheafOfModules.bilinearEquivTensorHom_naturality`: the universal properties of the
  objectwise tensor product presheaf and of the tensor product sheaf are natural in the sheaf
  of values. These are steps 2 and 5 of the chain of Tag 03EL.
* `Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom_naturality` and its `symm` form:
  naturality of the sheafification bijection, which is the right-hand naturality of the
  sheafification adjunction.
* `Stacks.SheafOfModules.inverseImagePairingEquiv_naturality` and
  `Stacks.SheafOfModules.inverseImageBilinearEquiv_naturality`: the bijection between pairings
  of the inverse images and pairings into the direct image is natural in the sheaf of values.
  This is step 3 of the chain of Tag 03EL.

## Implementation notes

Every one of these is ultimately `Adjunction.homEquiv_naturality_right`, for the sheafification
adjunction in the tensor-product case and for `f⁻¹ ⊣ f_*` in the inverse-image case; the only
genuine work is `IsBilinearPairing.comp`, which is four applications of the fact that a morphism
of sheaves of modules is additive and linear on sections
(`Stacks.Sheaves.ToposPullback.sectionsFunctor_map_moduleSheafFunctor_map_add` and `_smul`).

Two of the proofs are written in term mode rather than with `rw`, deliberately. The sheaf of
rings of the tensor-product bijections is spelled `Stacks.SheafOfModules.Tensor.ringSheaf O` for a
sheaf of commutative rings `O` in `Stacks.SheafOfModules.bilinearEquivTensorHom`, and
`Stacks.Sheaves.RingedToposModules.commRingSheaf J O.obj _` in the presheaf-level
`Stacks.SheafOfModules.tensorHomOfPairing` which it is built from; likewise the source of
`Stacks.SheafOfModules.inverseImagePairingEquiv` is spelled `f.inverseImage.obj (moduleSheaf O F)`
while its `@[simp]` characterisation is spelled
`moduleSheaf _ ((inverseImageModules f O).obj F)`. The two spellings in each pair are
definitionally equal but not at the `reducible` transparency at which `rw` and `simp` unify, so
`rw` reports "did not find an occurrence" on a pattern that is visibly present. Term mode type-
checks at default transparency and therefore needs no transparency option: `congrArg` and
`Eq.trans` replace the rewrites, and the declared statement absorbs the change of spelling.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v u

namespace Stacks.SheafOfModules

/-! ## Post-composition of a pairing with a morphism of sheaves of modules -/

section Comp

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {A B N N' : SheafOfModules.{w} R}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The value on a pair of local sections of a pairing composed with a morphism of sheaves of
modules: apply the morphism to the value of the original pairing. -/
lemma pairingApp_comp (q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N) (k : N ⟶ N')
    (U : Cᵒᵖ) (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)) :
    pairingApp R (q ≫ (moduleSheafFunctor R).map k) U a b =
      (sectionsFunctor J U).map ((moduleSheafFunctor R).map k) (pairingApp R q U a b) :=
  (sectionsFunctor J U).map_comp_apply q ((moduleSheafFunctor R).map k) _

/-- A bilinear pairing composed with a morphism of sheaves of modules is bilinear, because a
morphism of sheaves of modules is additive and linear on sections. This is the action of
`Bilin_O(A × B, -)` on morphisms. -/
lemma IsBilinearPairing.comp {q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N}
    (hq : IsBilinearPairing R q) (k : N ⟶ N') :
    IsBilinearPairing R (q ≫ (moduleSheafFunctor R).map k) where
  add_left U a a' b := by
    simp only [pairingApp_comp, hq.add_left, sectionsFunctor_map_moduleSheafFunctor_map_add]
  add_right U a b b' := by
    simp only [pairingApp_comp, hq.add_right, sectionsFunctor_map_moduleSheafFunctor_map_add]
  smul_left U r a b := by
    simp only [pairingApp_comp, hq.smul_left, sectionsFunctor_map_moduleSheafFunctor_map_smul]
  smul_right U r a b := by
    simp only [pairingApp_comp, hq.smul_right, sectionsFunctor_map_moduleSheafFunctor_map_smul]

end Comp

/-! ## Naturality of the presheaf-level universal property -/

section PresheafTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O)}
  {A B N N' : SheafOfModules.{w} (commRingSheaf J O hO)}

/-- The morphism out of the objectwise tensor product determined by a bilinear pairing is
natural in the sheaf of values. -/
lemma tensorHomOfPairing_comp
    {q : moduleSheaf (commRingSheaf J O hO) A ⨯ moduleSheaf (commRingSheaf J O hO) B ⟶
      moduleSheaf (commRingSheaf J O hO) N}
    (hq : IsBilinearPairing (commRingSheaf J O hO) q) (k : N ⟶ N') :
    tensorHomOfPairing (hq.comp k) = tensorHomOfPairing hq ≫ k.val := by
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  exact pairingApp_comp q k U a b

/-- **The universal property of the objectwise tensor product is natural in the sheaf of
values.** -/
lemma bilinearEquivPresheafTensorHom_naturality
    (q : { q : moduleSheaf (commRingSheaf J O hO) A ⨯
        moduleSheaf (commRingSheaf J O hO) B ⟶ moduleSheaf (commRingSheaf J O hO) N //
      IsBilinearPairing (commRingSheaf J O hO) q }) (k : N ⟶ N') :
    bilinearEquivPresheafTensorHom
        ⟨q.1 ≫ (moduleSheafFunctor (commRingSheaf J O hO)).map k, q.2.comp k⟩ =
      bilinearEquivPresheafTensorHom q ≫ k.val :=
  tensorHomOfPairing_comp q.2 k

end PresheafTensor

/-! ## Naturality of the universal property of the tensor product sheaf -/

section SheafTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}
  {A B N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The bijection between morphisms out of the tensor product sheaf and morphisms out of the
objectwise tensor product presheaf is natural in the sheaf of values: this is the right-hand
naturality of the sheafification adjunction. -/
lemma tensorHomEquivPresheafTensorHom_naturality
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj A).obj B ⟶ N) (k : N ⟶ N') :
    tensorHomEquivPresheafTensorHom (t ≫ k) =
      tensorHomEquivPresheafTensorHom t ≫ k.val :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).homEquiv_naturality_right t k

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The inverse of `Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom` is natural in the
sheaf of values. -/
lemma tensorHomEquivPresheafTensorHom_symm_naturality (t : A.val ⊗ B.val ⟶ N.val) (k : N ⟶ N') :
    tensorHomEquivPresheafTensorHom.symm (t ≫ k.val) =
      (tensorHomEquivPresheafTensorHom (A := A) (B := B)).symm t ≫ k :=
  tensorHomEquivPresheafTensorHom.injective (by
    rw [Equiv.apply_symm_apply, tensorHomEquivPresheafTensorHom_naturality,
      Equiv.apply_symm_apply])

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The universal property of the tensor product sheaf is natural in the sheaf of values.**
This is the naturality in `N` of steps 2 and 5 of the chain of bijections of Tag 03EL. -/
lemma bilinearEquivTensorHom_naturality
    (q : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) A ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) B ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O) N //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf O) q }) (k : N ⟶ N') :
    bilinearEquivTensorHom
        ⟨q.1 ≫ (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf O)).map k, q.2.comp k⟩ =
      bilinearEquivTensorHom q ≫ k :=
  (congrArg (fun t ↦ (tensorHomEquivPresheafTensorHom (A := A) (B := B) (N := N')).symm t)
      (tensorHomOfPairing_comp (hO := (Stacks.SheafOfModules.Tensor.ringSheaf O).property)
        q.2 k)).trans
    (tensorHomEquivPresheafTensorHom_symm_naturality _ k)

end SheafTensor

/-! ## Naturality of the inverse-image bijection -/

section InverseImage

universe w' v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'}) (F G : SheafOfModules.{w'} O)
  {N N' : SheafOfModules.{w} (inverseImageRingSheaf f O)}

/-- The bijection between pairings of the inverse images of two sheaves of modules and pairings
into the direct image is natural in the sheaf of values, the morphism downstairs being the
direct image of the morphism upstairs. -/
lemma inverseImagePairingEquiv_naturality
    (q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) (k : N ⟶ N') :
    inverseImagePairingEquiv f O F G N'
        (q ≫ (moduleSheafFunctor (inverseImageRingSheaf f O)).map k) =
      inverseImagePairingEquiv f O F G N q ≫
        (moduleSheafFunctor O).map ((directImageModules f O).map k) :=
  (congrArg (fun t ↦ f.adj.homEquiv (moduleSheaf O F ⨯ moduleSheaf O G)
        (moduleSheaf (inverseImageRingSheaf f O) N') t)
      (Category.assoc (prodComparison f.inverseImage (moduleSheaf O F) (moduleSheaf O G)) q
        ((moduleSheafFunctor (inverseImageRingSheaf f O)).map k)).symm).trans
    (f.adj.homEquiv_naturality_right
      (prodComparison f.inverseImage (moduleSheaf O F) (moduleSheaf O G) ≫ q)
      ((moduleSheafFunctor (inverseImageRingSheaf f O)).map k))

/-- **The bilinear pairings of the inverse images are the bilinear pairings into the direct
image, naturally in the sheaf of values.** This is the naturality in `N` of step 3 of the chain
of bijections of Tag 03EL. -/
lemma inverseImageBilinearEquiv_naturality
    (q : { q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
          moduleSheaf (inverseImageRingSheaf f O) N //
      IsBilinearPairing (inverseImageRingSheaf f O) q }) (k : N ⟶ N') :
    (inverseImageBilinearEquiv f O F G N'
          ⟨q.1 ≫ (moduleSheafFunctor (inverseImageRingSheaf f O)).map k, q.2.comp k⟩).1 =
      (inverseImageBilinearEquiv f O F G N q).1 ≫
        (moduleSheafFunctor O).map ((directImageModules f O).map k) :=
  inverseImagePairingEquiv_naturality f O F G q.1 k

end InverseImage

end Stacks.SheafOfModules

end
