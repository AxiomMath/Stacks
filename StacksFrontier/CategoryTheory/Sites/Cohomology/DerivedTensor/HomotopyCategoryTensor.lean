module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product on the homotopy category of sheaves of modules

Let `(C, O)` be a ringed site. The total tensor product `Tot(K ⊗_O L)` of cochain complexes of
`O`-modules descends to the homotopy category `K(Mod(O))` as a bifunctor in both variables at
once.

Stacks 06YM, which is in the library, descends `Tot(G ⊗_O -)` and `Tot(- ⊗_O G)` separately for a
*fixed* complex `G` in the other slot, as `Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi` and
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR`. What is added here is the descent of both
  variables
simultaneously, as a single bifunctor on `K(Mod(O))`; that is what a bifunctor on the derived
category is in turn obtained from.

## Main definitions

* `Stacks.SheafOfModules.Tensor.complexHomotopyEquivalences`: the homotopy equivalences of
  complexes of
  sheaves of modules.
* `Stacks.SheafOfModules.Tensor.homotopyCategoryTensor`: the tensor bifunctor on `K(Mod(O))`.
* `Stacks.SheafOfModules.Tensor.homotopyCategoryTensorComparison`: its value on the classes of two
  complexes
  is the class of their total tensor complex.
* `Stacks.SheafOfModules.Tensor.homotopyCategoryTensorRightIso` and
  `Stacks.SheafOfModules.Tensor.homotopyCategoryTensorLeftIso`: fixing one variable at the class of
    a complex
  recovers the one-variable descent of Stacks 06YM.

## Main results

* `Stacks.SheafOfModules.Tensor.tensorComplex_inverts_homotopyEquivalences₂`: the total tensor
  product
  followed by the homotopy quotient inverts homotopy equivalences in both variables
  simultaneously, which is what makes the descent possible.

## Implementation notes

The descent is Mathlib's `CategoryTheory.Localization.lift₂`, whose hypotheses are that the
two functors being localized along are localization functors — which
`HomotopyCategory.quotient` is, for the homotopy equivalences — and that the bifunctor inverts
the two classes jointly. Because `Functor.uncurry` sends a pair of morphisms to the composite
of the two one-variable images, inverting the two classes jointly reduces to inverting each
separately, which is `isIso_quotient_map_tensorComplex_map_app` and
`isIso_quotient_map_tensorComplex_obj_map`.

Those two are read off the 06YM descent rather than reproved from homotopies: the
factorisation isomorphism `Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors` identifies
`Tot(- ⊗_O G)` followed by the homotopy quotient with the homotopy quotient followed by the
descended functor, and a functor carries the image of a homotopy equivalence — which the
quotient inverts — to an isomorphism. Transferring along the factorisation isomorphism is
`CategoryTheory.NatIso.isIso_map_iff`.

`homotopyCategoryTensorLifting` records the lifting datum as an `instance_reducible`
definition so that the comparison isomorphism can be obtained from the localization API
rather than re-derived.

The comparison with the one-variable descent of 06YM is the uniqueness of a lift along a
localization functor, `CategoryTheory.Localization.liftNatIso`: both
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR` and the flip of the bifunctor built here
  lift the same
functor `Tot(- ⊗_O K)` followed by the homotopy quotient, the first by
`Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors` and the second by
`CategoryTheory.Localization.Lifting₂.snd`. These comparisons are what transport the exactness
and the quasi-isomorphism-preservation of 06YM and 06YP to the bifunctor.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(sheafTensor.{u, v, w} R).Additive]
  [∀ M, ((sheafTensor.{u, v, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor R) (ComplexShape.up ℤ)]

/-- The homotopy equivalences of cochain complexes of sheaves of modules. The homotopy
category is the localization at this class. -/
abbrev complexHomotopyEquivalences :
    MorphismProperty
      (CochainComplex (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) ℤ) :=
  HomologicalComplex.homotopyEquivalences
    (SheafOfModules.{w} (ringSheaf.{u, v, w} R)) (ComplexShape.up ℤ)

/-- If `Q ⋙ Φ ≅ G` and `Q` sends `f` to an isomorphism, then so does `G`. -/
private theorem isIso_map_of_comp_iso {X D E : Type*} [Category X] [Category D] [Category E]
    (Q : X ⥤ D) (Φ : D ⥤ E) (G : X ⥤ E) (e : Q ⋙ Φ ≅ G) {A B : X} (f : A ⟶ B)
    [IsIso (Q.map f)] : IsIso (G.map f) :=
  (NatIso.isIso_map_iff e f).1 (by rw [Functor.comp_map]; infer_instance)

/-- Tensoring a homotopy equivalence with a fixed complex on the right gives a map which the
homotopy quotient inverts. -/
theorem isIso_quotient_map_tensorComplex_map_app
    (K₂ : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ)
    {A B : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ} (f : A ⟶ B)
    (hf : complexHomotopyEquivalences R f) :
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (((tensorComplex R).map f).app K₂)) := by
  have hQf : IsIso ((HomotopyCategory.quotient
      (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)).map f) :=
    Localization.inverts _ (complexHomotopyEquivalences R) f hf
  exact isIso_map_of_comp_iso _ _ _ (Reduction.bifunctorPhiRFactors (sheafTensor R) K₂) f

/-- Tensoring a homotopy equivalence with a fixed complex on the left gives a map which the
homotopy quotient inverts. -/
theorem isIso_quotient_map_tensorComplex_obj_map
    (L₁ : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ)
    {A B : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ} (g : A ⟶ B)
    (hg : complexHomotopyEquivalences R g) :
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (((tensorComplex R).obj L₁).map g)) := by
  have hQg : IsIso ((HomotopyCategory.quotient
      (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)).map g) :=
    Localization.inverts _ (complexHomotopyEquivalences R) g hg
  exact isIso_map_of_comp_iso _ _ _ (Reduction.bifunctorPhiFactors (sheafTensor R) L₁) g

/-- The total tensor product followed by the homotopy quotient inverts homotopy equivalences
in both variables simultaneously. -/
theorem tensorComplex_inverts_homotopyEquivalences₂ :
    MorphismProperty.IsInvertedBy₂ (complexHomotopyEquivalences.{u, v, w} R)
      (complexHomotopyEquivalences.{u, v, w} R)
      (tensorComplex.{u, v, w} R ⋙
        (Functor.whiskeringRight _ _ _).obj
          (HomotopyCategory.quotient
            (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ))) := by
  rintro ⟨K₁, K₂⟩ ⟨L₁, L₂⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have h₁ := isIso_quotient_map_tensorComplex_map_app R K₂ f hf
  have h₂ := isIso_quotient_map_tensorComplex_obj_map R L₁ g hg
  simp only [Functor.uncurry_obj_map, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app]
  infer_instance

/-- The tensor bifunctor on the homotopy category of sheaves of modules, obtained by
descending the total tensor product of complexes in both variables. -/
def homotopyCategoryTensor :
    HomotopyCategory (SheafOfModules.{w} (ringSheaf.{u, v, w} R))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{w} (ringSheaf.{u, v, w} R))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{w} (ringSheaf.{u, v, w} R))
        (ComplexShape.up ℤ) :=
  Localization.lift₂
    (tensorComplex.{u, v, w} R ⋙
      (Functor.whiskeringRight _ _ _).obj
        (HomotopyCategory.quotient
          (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)))
    (tensorComplex_inverts_homotopyEquivalences₂ R)
    (HomotopyCategory.quotient (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ))
    (HomotopyCategory.quotient (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ))

/-- `Stacks.SheafOfModules.Tensor.homotopyCategoryTensor` lifts the total tensor product of
  complexes through
the homotopy quotient in both variables. -/
@[instance_reducible]
def homotopyCategoryTensorLifting :
    Localization.Lifting₂
      (HomotopyCategory.quotient
        (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ))
      (HomotopyCategory.quotient
        (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ))
      (complexHomotopyEquivalences.{u, v, w} R) (complexHomotopyEquivalences.{u, v, w} R)
      (tensorComplex.{u, v, w} R ⋙
        (Functor.whiskeringRight _ _ _).obj
          (HomotopyCategory.quotient
            (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)))
      (homotopyCategoryTensor.{u, v, w} R) := by
  unfold homotopyCategoryTensor
  infer_instance

attribute [local instance] homotopyCategoryTensorLifting

/-- On the classes of two complexes, the homotopy-category tensor product is the class of
their total tensor complex. -/
def homotopyCategoryTensorComparison
    (K L : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ) :
    ((homotopyCategoryTensor R).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) ≅
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((tensorComplex R).obj K).obj L) :=
  ((Localization.Lifting₂.iso
    (HomotopyCategory.quotient
      (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ))
    (HomotopyCategory.quotient
      (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ))
    (complexHomotopyEquivalences R) (complexHomotopyEquivalences R)
    (tensorComplex R ⋙
      (Functor.whiskeringRight _ _ _).obj
        (HomotopyCategory.quotient
          (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)))
    (homotopyCategoryTensor R)).app K).app L

/-- Fixing the second variable at the class of a complex `K` recovers the one-variable
descent `Tot(- ⊗_O K)` of Stacks 06YM. Both functors lift `Tot(- ⊗_O K)` followed by the
homotopy quotient, so they agree by uniqueness of lifts along a localization. -/
def homotopyCategoryTensorRightIso
    (K : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ) :
    (homotopyCategoryTensor R).flip.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≅
      Reduction.bifunctorPhiR (sheafTensor R) K := by
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)
  let F := (tensorComplex R).flip.obj K ⋙ Q
  letI : Localization.Lifting Q (complexHomotopyEquivalences R) F
      (Reduction.bifunctorPhiR (sheafTensor R) K) :=
    ⟨Reduction.bifunctorPhiRFactors (sheafTensor R) K⟩
  letI : Localization.Lifting Q (complexHomotopyEquivalences R) F
      ((homotopyCategoryTensor R).flip.obj (Q.obj K)) :=
    Localization.Lifting₂.snd Q Q (complexHomotopyEquivalences R)
      (complexHomotopyEquivalences R)
      (tensorComplex R ⋙ (Functor.whiskeringRight _ _ _).obj Q)
      (homotopyCategoryTensor R) K
  exact Localization.liftNatIso Q (complexHomotopyEquivalences R) F F _ _ (Iso.refl _)

/-- Fixing the first variable at the class of a complex `K` recovers the one-variable descent
`Tot(K ⊗_O -)` of Stacks 06YM. -/
def homotopyCategoryTensorLeftIso
    (K : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ) :
    (homotopyCategoryTensor R).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≅
      Reduction.bifunctorPhi (sheafTensor R) K := by
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)
  let F := (tensorComplex R).obj K ⋙ Q
  letI : Localization.Lifting Q (complexHomotopyEquivalences R) F
      (Reduction.bifunctorPhi (sheafTensor R) K) :=
    ⟨Reduction.bifunctorPhiFactors (sheafTensor R) K⟩
  letI : Localization.Lifting Q (complexHomotopyEquivalences R) F
      ((homotopyCategoryTensor R).obj (Q.obj K)) :=
    Localization.Lifting₂.fst Q Q (complexHomotopyEquivalences R)
      (complexHomotopyEquivalences R)
      (tensorComplex R ⋙ (Functor.whiskeringRight _ _ _).obj Q)
      (homotopyCategoryTensor R) K
  exact Localization.liftNatIso Q (complexHomotopyEquivalences R) F F _ _ (Iso.refl _)

end Stacks.SheafOfModules.Tensor

end
