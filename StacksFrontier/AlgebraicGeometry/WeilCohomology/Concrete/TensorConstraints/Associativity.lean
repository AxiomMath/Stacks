module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorTransport
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorClopen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorConstraints.ProductPushforward

/-!
# The associativity constraint of the tensor product of correspondences

Transporting `(c₁ ⊗ c₂) ⊗ c₃` along the associativity isomorphisms gives `c₁ ⊗ (c₂ ⊗ c₃)`
(Stacks 0FG7).

## Main results

* `Stacks.WeilCohomology.corrEquivOfIso_tensor_tensor`: associativity.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

local notation "pf[" sA ", " sB ", " v ", " hv ", " n "]" =>
  properChowPushforward (fieldChowSituation k) sA sB v hv n
    (properPushforwardDescends _ _ _ _ _ _)

section Assoc

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Scheme.{u}}
  (sA₁ : A₁ ⟶ (fieldChowSituation k).S) (sA₂ : A₂ ⟶ (fieldChowSituation k).S)
  (sA₃ : A₃ ⟶ (fieldChowSituation k).S) (sB₁ : B₁ ⟶ (fieldChowSituation k).S)
  (sB₂ : B₂ ⟶ (fieldChowSituation k).S) (sB₃ : B₃ ⟶ (fieldChowSituation k).S)
  [Smooth sA₁] [IsSeparated sA₁] [IsProper sA₁] [Smooth sA₂] [IsSeparated sA₂] [IsProper sA₂]
  [Smooth sA₃] [IsSeparated sA₃] [IsProper sA₃] [Smooth sB₁] [IsSeparated sB₁] [IsProper sB₁]
  [Smooth sB₂] [IsSeparated sB₂] [IsProper sB₂] [Smooth sB₃] [IsSeparated sB₃] [IsProper sB₃]
  (φA : Limits.pullback (prodBase sA₁ sA₂) sA₃ ⟶ Limits.pullback sA₁ (prodBase sA₂ sA₃))
  [IsIso φA]
  (hφA₁ : φA ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
  (hφA₂ : φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
    Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _)
  (hφA₃ : φA ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)
  (φB : Limits.pullback (prodBase sB₁ sB₂) sB₃ ⟶ Limits.pullback sB₁ (prodBase sB₂ sB₃))
  [IsIso φB]
  (hφB₁ : φB ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
  (hφB₂ : φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.fst _ _ =
    Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _)
  (hφB₃ : φB ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _)

include hφA₂ hφA₃ hφB₂ hφB₃ in
omit [IsSeparated sA₁] [IsProper sA₁] [IsSeparated sA₂] [IsProper sA₂] [IsSeparated sA₃]
  [IsProper sA₃] [IsSeparated sB₁] [IsProper sB₁] [IsSeparated sB₂] [IsProper sB₂] [IsSeparated sB₃]
  [IsProper sB₃] in
/-- The associativity isomorphisms on a block of the sixfold product, read in the sixfold
product. -/
theorem tensorBlockHom_assoc (d₁ d₂ d₃ e₁ e₂ e₃ : ℕ) :
    ((prodHom (prodBase (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃)) (prodBase
        (partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃))
          (prodBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃)) (prodBase
              (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃))
          (prodHom (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃) (prodBase
              (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (partProdHom k sA₁ sA₂ d₁ d₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sA₁ sA₂ d₁ d₂) (Category.id_comp _))
          (prodHom (partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃) (prodBase
              (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃) (partProdHom k sB₁ sB₂ e₁ e₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sB₁ sB₂ e₁ e₂) (Category.id_comp _))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (d₁ + d₂) d₃
                  (e₁ + e₂) e₃) ≫
        (prodHom (partBase (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase
            (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (partBase (prodBase
                (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃)
                    (e₁ + e₂ + e₃))
          (partMap (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃) φA
              (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (d₁ + d₂ + d₃))
          (partMap (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φB
              (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (e₁ + e₂ + e₃))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))) ≫
      (prodHom (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃)) (partBase
          (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase (prodBase sB₁
              (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (dimPart (prodBase sA₁ (prodBase sA₂ sA₃))
                  (d₁ + d₂ + d₃)).ι
          (dimPart (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)).ι rfl rfl) =
    ((tensorAssocHom k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sA₃ d₃) (partBase sB₁ e₁)
        (partBase sB₂ e₂) (partBase sB₃ e₃) (prodAssocHom (partBase sA₁ d₁) (partBase sA₂ d₂)
            (partBase sA₃ d₃))
          (prodAssocHom (partBase sB₁ e₁) (partBase sB₂ e₂) (partBase sB₃ e₃))
              (prodAssocHom_fst _ _ _) (prodAssocHom_fst _ _ _)) ≫ (prodHom (prodBase
                  (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃))) (prodBase
                      (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)))
          (prodBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))) (prodBase
              (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)))
          (prodHom (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sA₁ d₁)
              (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃)) (𝟙 _) (partProdHom k sA₂ sA₃ d₂ d₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃))
          (prodHom (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (partBase sB₁ e₁)
              (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)) (𝟙 _) (partProdHom k sB₂ sB₃ e₂ e₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁ (d₂ + d₃) e₁
                  (e₂ + e₃))) ≫
      (prodHom (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃)) (partBase
          (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + (d₂ + d₃))) (partBase (prodBase sB₁
              (prodBase sB₂ sB₃)) (e₁ + (e₂ + e₃))) (dimPart (prodBase sA₁ (prodBase sA₂ sA₃))
                  (d₁ + (d₂ + d₃))).ι
          (dimPart (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + (e₂ + e₃))).ι rfl rfl) := by
  refine Limits.pullback.hom_ext (Limits.pullback.hom_ext ?_ (Limits.pullback.hom_ext ?_ ?_))
    (Limits.pullback.hom_ext ?_ (Limits.pullback.hom_ext ?_ ?_)) <;>
    simp [tensorBlockHom, tensorAssocHom, hφA₁, hφA₂, hφA₃, hφB₁, hφB₂, hφB₃]

/-- The left side of associativity on a block, as one pushforward. -/
theorem assoc_left_int (r₁ r₂ r₃ : ℤ) (d₁ e₁ d₂ e₂ d₃ e₃ : ℕ)
    (α₁ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₁ d₁) (partBase sB₁ e₁))
        (((e₁ : ℕ) : ℤ) - r₁)) (α₂ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₂ d₂)
            (partBase sB₂ e₂)) (((e₂ : ℕ) : ℤ) - r₂))
    (α₃ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₃ d₃) (partBase sB₃ e₃))
        (((e₃ : ℕ) : ℤ) - r₃)) :
    chowPushforwardOfIso (fieldChowSituation k) (prodBase (partBase (prodBase
        (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃)
            (e₁ + e₂ + e₃))) (prodBase (partBase (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃))
                (partBase (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃))) (prodHom (partBase
                    (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase (prodBase sB₁
                        (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (partBase (prodBase
                            (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase
                                (prodBase sB₁ sB₂) sB₃) (e₁ + e₂ + e₃))
          (partMap (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃) φA
              (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (d₁ + d₂ + d₃))
          (partMap (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φB
              (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (e₁ + e₂ + e₃))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))
        (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (((e₁ + e₂ + e₃ : ℕ) : ℤ) - (r₁ + r₂ + r₃))
        (pf[tensorBase (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃) (partBase
            (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃), (prodBase (partBase (prodBase
                (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃)
                    (e₁ + e₂ + e₃))), (tensorBlockHom k (prodBase sA₁ sA₂) sA₃
                        (prodBase sB₁ sB₂) sB₃ (d₁ + d₂) d₃ (e₁ + e₂) e₃),
          tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _, (((e₁ + e₂ + e₃ : ℕ) : ℤ) -
              (r₁ + r₂ + r₃))] (tensorInt k (partBase (prodBase sA₁ sA₂) (d₁ + d₂))
                  (partBase sA₃ d₃) (partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃)
                      (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase (prodBase sA₁ sA₂) (d₁ + d₂))
                (relativeDimension_partBase sA₃ d₃)
            (relativeDimension_partBase (prodBase sB₁ sB₂) (e₁ + e₂))
                (relativeDimension_partBase sB₃ e₃)
            (r₁ + r₂) r₃ (pf[tensorBase (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁)
                (partBase sB₂ e₂), prodBase (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase
                    (prodBase sB₁ sB₂) (e₁ + e₂)),
              tensorBlockHom k sA₁ sA₂ sB₁ sB₂ d₁ d₂ e₁ e₂,
              tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _, (((e₁ + e₂ : ℕ) : ℤ) - (r₁ + r₂))]
                  (tensorInt k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁)
                      (partBase sB₂ e₂) (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sB₁ e₁)
                (relativeDimension_partBase sB₂ e₂) r₁ r₂ α₁ α₂)) α₃)) =
      pf[(tensorBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase
          (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃)), (prodBase (partBase
              (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase (prodBase sB₁
                  (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃))), ((prodHom (prodBase (partBase
                      (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃)) (prodBase (partBase
                          (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃))
          (prodBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃)) (prodBase
              (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃))
          (prodHom (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃) (prodBase
              (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (partProdHom k sA₁ sA₂ d₁ d₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sA₁ sA₂ d₁ d₂) (Category.id_comp _))
          (prodHom (partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃) (prodBase
              (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃) (partProdHom k sB₁ sB₂ e₁ e₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sB₁ sB₂ e₁ e₂) (Category.id_comp _))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (d₁ + d₂) d₃
                  (e₁ + e₂) e₃) ≫
        (prodHom (partBase (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase
            (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (partBase (prodBase
                (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃)
                    (e₁ + e₂ + e₃))
          (partMap (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃) φA
              (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (d₁ + d₂ + d₃))
          (partMap (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φB
              (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (e₁ + e₂ + e₃))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))),
      by simp only [Category.assoc, prodHom_comp_prodBase],
      (((e₁ + e₂ + e₃ : ℕ) : ℤ) - (r₁ + r₂ + r₃))] (tensorInt k (prodBase (partBase sA₁ d₁)
          (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂))
              (partBase sB₃ e₃)
          (canonicalDiagonalClassFamily k)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₁ d₁)
            (relativeDimension_partBase sA₂ d₂)) (relativeDimension_partBase sA₃ d₃)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₁ e₁)
            (relativeDimension_partBase sB₂ e₂)) (relativeDimension_partBase sB₃ e₃) (r₁ + r₂) r₃
          (tensorInt k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁) (partBase sB₂ e₂)
              (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sB₁ e₁)
                (relativeDimension_partBase sB₂ e₂) r₁ r₂ α₁ α₂) α₃) := by
  have h6 := tensorInt_properChowPushforward_prodHom_left k (partProdHom k sA₁ sA₂ d₁ d₂)
    (partProdHom k sB₁ sB₂ e₁ e₂) (partProdHom_comp_partBase k sA₁ sA₂ d₁ d₂)
    (partProdHom_comp_partBase k sB₁ sB₂ e₁ e₂)
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₁ d₁)
      (relativeDimension_partBase sA₂ d₂)) (relativeDimension_partBase sA₃ d₃)
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₁ e₁)
      (relativeDimension_partBase sB₂ e₂)) (relativeDimension_partBase sB₃ e₃)
    (relativeDimension_partBase (prodBase sA₁ sA₂) (d₁ + d₂))
    (relativeDimension_partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (r₁ + r₂) r₃ (tensorInt k
        (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁) (partBase sB₂ e₂)
            (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sB₁ e₁) (relativeDimension_partBase sB₂ e₂) r₁ r₂ α₁ α₂) α₃
  have c₁ := properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ (prodHom (prodBase
      (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃)) (prodBase (partBase
          (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃))
          (prodBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃)) (prodBase
              (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃))
          (prodHom (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃) (prodBase
              (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (partProdHom k sA₁ sA₂ d₁ d₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sA₁ sA₂ d₁ d₂) (Category.id_comp _))
          (prodHom (partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃) (prodBase
              (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃) (partProdHom k sB₁ sB₂ e₁ e₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sB₁ sB₂ e₁ e₂) (Category.id_comp _))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _))
    ((tensorBlockHom k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (d₁ + d₂) d₃ (e₁ + e₂) e₃) ≫
        (prodHom (partBase (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase
            (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (partBase (prodBase
                (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃)
                    (e₁ + e₂ + e₃))
          (partMap (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃) φA
              (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (d₁ + d₂ + d₃))
          (partMap (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φB
              (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (e₁ + e₂ + e₃))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))) _ rfl
              (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (by rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase])
    (by simp only [Category.assoc, prodHom_comp_prodBase])
    (((e₁ + e₂ + e₃ : ℕ) : ℤ) - (r₁ + r₂ + r₃)) (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
            (tensorInt k (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase
                (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃)
          (canonicalDiagonalClassFamily k)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₁ d₁)
            (relativeDimension_partBase sA₂ d₂)) (relativeDimension_partBase sA₃ d₃)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₁ e₁)
            (relativeDimension_partBase sB₂ e₂)) (relativeDimension_partBase sB₃ e₃) (r₁ + r₂) r₃
          (tensorInt k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁) (partBase sB₂ e₂)
              (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sB₁ e₁) (relativeDimension_partBase sB₂ e₂) r₁ r₂ α₁ α₂) α₃)
  have c₂ := properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ (tensorBlockHom k
      (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (d₁ + d₂) d₃ (e₁ + e₂) e₃) (prodHom (partBase
          (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase (prodBase sB₁
              (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (partBase (prodBase (prodBase sA₁ sA₂) sA₃)
                  (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃) (e₁ + e₂ + e₃))
          (partMap (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃) φA
              (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (d₁ + d₂ + d₃))
          (partMap (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φB
              (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (e₁ + e₂ + e₃))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _)) _ rfl
    (tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (by rw [Category.assoc, prodHom_comp_prodBase, tensorBlockHom_comp_prodBase])
    (((e₁ + e₂ + e₃ : ℕ) : ℤ) - (r₁ + r₂ + r₃)) (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
  rw [h6]
  exact (c₂ _).symm.trans c₁.symm

/-- The right side of associativity on a block, as one pushforward. -/
theorem assoc_right_int (r₁ r₂ r₃ : ℤ) (d₁ e₁ d₂ e₂ d₃ e₃ : ℕ)
    (α₁ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₁ d₁) (partBase sB₁ e₁))
        (((e₁ : ℕ) : ℤ) - r₁)) (α₂ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₂ d₂)
            (partBase sB₂ e₂)) (((e₂ : ℕ) : ℤ) - r₂))
    (α₃ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₃ d₃) (partBase sB₃ e₃))
        (((e₃ : ℕ) : ℤ) - r₃)) :
    pf[tensorBase (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sB₁ e₁)
        (partBase (prodBase sB₂ sB₃) (e₂ + e₃)), (prodBase (partBase (prodBase sA₁
            (prodBase sA₂ sA₃)) (d₁ + (d₂ + d₃))) (partBase (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ +
                (e₂ + e₃)))), (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁
                    (d₂ + d₃) e₁ (e₂ + e₃)),
          tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _, (((e₁ + (e₂ + e₃) : ℕ) : ℤ) - (r₁ +
              (r₂ + r₃)))] (tensorInt k (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃))
                  (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃))
                      (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase (prodBase sA₂ sA₃)
                (d₂ + d₃))
            (relativeDimension_partBase sB₁ e₁) (relativeDimension_partBase (prodBase sB₂ sB₃)
                (e₂ + e₃))
            r₁ (r₂ + r₃) α₁ (pf[tensorBase (partBase sA₂ d₂) (partBase sA₃ d₃) (partBase sB₂ e₂)
                (partBase sB₃ e₃), prodBase (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase
                    (prodBase sB₂ sB₃) (e₂ + e₃)),
              tensorBlockHom k sA₂ sA₃ sB₂ sB₃ d₂ d₃ e₂ e₃,
              tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _, (((e₂ + e₃ : ℕ) : ℤ) - (r₂ + r₃))]
                  (tensorInt k (partBase sA₂ d₂) (partBase sA₃ d₃) (partBase sB₂ e₂)
                      (partBase sB₃ e₃) (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₂ d₂) (relativeDimension_partBase sA₃ d₃)
            (relativeDimension_partBase sB₂ e₂) (relativeDimension_partBase sB₃ e₃) r₂ r₃ α₂ α₃))) =
      pf[(tensorBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))
          (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃))), (prodBase (partBase
              (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + (d₂ + d₃))) (partBase (prodBase sB₁
                  (prodBase sB₂ sB₃)) (e₁ + (e₂ + e₃)))), ((prodHom (prodBase (partBase sA₁ d₁)
                      (partBase (prodBase sA₂ sA₃) (d₂ + d₃))) (prodBase (partBase sB₁ e₁)
                          (partBase (prodBase sB₂ sB₃) (e₂ + e₃)))
          (prodBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))) (prodBase
              (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)))
          (prodHom (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sA₁ d₁)
              (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃)) (𝟙 _) (partProdHom k sA₂ sA₃ d₂ d₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃))
          (prodHom (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (partBase sB₁ e₁)
              (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)) (𝟙 _) (partProdHom k sB₂ sB₃ e₂ e₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁ (d₂ + d₃) e₁
                  (e₂ + e₃))),
      by rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase],
      (((e₁ + (e₂ + e₃) : ℕ) : ℤ) - (r₁ + (r₂ + r₃)))] (tensorInt k (partBase sA₁ d₁) (prodBase
          (partBase sA₂ d₂) (partBase sA₃ d₃)) (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂)
              (partBase sB₃ e₃))
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sA₁ d₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sA₃ d₃)) (relativeDimension_partBase sB₁ e₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₂ e₂)
            (relativeDimension_partBase sB₃ e₃)) r₁ (r₂ + r₃) α₁ (tensorInt k (partBase sA₂ d₂)
                (partBase sA₃ d₃) (partBase sB₂ e₂) (partBase sB₃ e₃)
                    (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₂ d₂) (relativeDimension_partBase sA₃ d₃)
            (relativeDimension_partBase sB₂ e₂)
                (relativeDimension_partBase sB₃ e₃) r₂ r₃ α₂ α₃)) := by
  have h6 := tensorInt_properChowPushforward_prodHom_right k (partProdHom k sA₂ sA₃ d₂ d₃)
    (partProdHom k sB₂ sB₃ e₂ e₃) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃)
    (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃) (relativeDimension_partBase sA₁ d₁)
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₂ d₂)
      (relativeDimension_partBase sA₃ d₃)) (relativeDimension_partBase sB₁ e₁)
    (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₂ e₂)
      (relativeDimension_partBase sB₃ e₃))
    (relativeDimension_partBase (prodBase sA₂ sA₃) (d₂ + d₃))
    (relativeDimension_partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (r₂ + r₃) r₁ α₁ (tensorInt k
        (partBase sA₂ d₂) (partBase sA₃ d₃) (partBase sB₂ e₂) (partBase sB₃ e₃)
            (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₂ d₂) (relativeDimension_partBase sA₃ d₃)
            (relativeDimension_partBase sB₂ e₂) (relativeDimension_partBase sB₃ e₃) r₂ r₃ α₂ α₃)
  have c₃ := properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ (prodHom (prodBase
      (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃))) (prodBase (partBase sB₁ e₁)
          (partBase (prodBase sB₂ sB₃) (e₂ + e₃)))
          (prodBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))) (prodBase
              (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)))
          (prodHom (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sA₁ d₁)
              (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃)) (𝟙 _) (partProdHom k sA₂ sA₃ d₂ d₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃))
          (prodHom (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (partBase sB₁ e₁)
              (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)) (𝟙 _) (partProdHom k sB₂ sB₃ e₂ e₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _))
              (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁ (d₂ + d₃) e₁
                  (e₂ + e₃)) _ rfl
    (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (tensorBlockHom_comp_prodBase _ _ _ _ _ _ _ _ _)
    (by rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase])
    (((e₁ + (e₂ + e₃) : ℕ) : ℤ) - (r₁ + (r₂ + r₃))) (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
            (tensorInt k (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))
                (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃))
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sA₁ d₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sA₃ d₃)) (relativeDimension_partBase sB₁ e₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₂ e₂)
            (relativeDimension_partBase sB₃ e₃)) r₁ (r₂ + r₃) α₁ (tensorInt k (partBase sA₂ d₂)
                (partBase sA₃ d₃) (partBase sB₂ e₂) (partBase sB₃ e₃)
                    (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₂ d₂) (relativeDimension_partBase sA₃ d₃)
            (relativeDimension_partBase sB₂ e₂) (relativeDimension_partBase sB₃ e₃) r₂ r₃ α₂ α₃))
  rw [h6]
  exact c₃.symm

include hφA₂ hφA₃ hφB₂ hφB₃ in
/-- Associativity on a block, on integral Chow groups. -/
theorem assoc_parts_heq (r₁ r₂ r₃ : ℤ) (d₁ e₁ d₂ e₂ d₃ e₃ : ℕ)
    (α₁ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₁ d₁) (partBase sB₁ e₁))
        (((e₁ : ℕ) : ℤ) - r₁)) (α₂ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₂ d₂)
            (partBase sB₂ e₂)) (((e₂ : ℕ) : ℤ) - r₂))
    (α₃ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₃ d₃) (partBase sB₃ e₃))
        (((e₃ : ℕ) : ℤ) - r₃)) :
    pf[(tensorBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase
        (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃)), (prodBase (partBase (prodBase sA₁
            (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase (prodBase sB₁ (prodBase sB₂ sB₃))
                (e₁ + e₂ + e₃))), ((prodHom (prodBase (partBase (prodBase sA₁ sA₂) (d₁ + d₂))
                    (partBase sA₃ d₃)) (prodBase (partBase (prodBase sB₁ sB₂) (e₁ + e₂))
                        (partBase sB₃ e₃))
          (prodBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃)) (prodBase
              (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃))
          (prodHom (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃) (prodBase
              (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (partProdHom k sA₁ sA₂ d₁ d₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sA₁ sA₂ d₁ d₂) (Category.id_comp _))
          (prodHom (partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃) (prodBase
              (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃) (partProdHom k sB₁ sB₂ e₁ e₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sB₁ sB₂ e₁ e₂) (Category.id_comp _))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (d₁ + d₂) d₃
                  (e₁ + e₂) e₃) ≫
        (prodHom (partBase (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase
            (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (partBase (prodBase
                (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃)
                    (e₁ + e₂ + e₃))
          (partMap (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃) φA
              (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (d₁ + d₂ + d₃))
          (partMap (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φB
              (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (e₁ + e₂ + e₃))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))),
      by simp only [Category.assoc, prodHom_comp_prodBase],
      (((e₁ + e₂ + e₃ : ℕ) : ℤ) - (r₁ + r₂ + r₃))] (tensorInt k (prodBase (partBase sA₁ d₁)
          (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂))
              (partBase sB₃ e₃)
          (canonicalDiagonalClassFamily k)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₁ d₁)
            (relativeDimension_partBase sA₂ d₂)) (relativeDimension_partBase sA₃ d₃)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₁ e₁)
            (relativeDimension_partBase sB₂ e₂)) (relativeDimension_partBase sB₃ e₃) (r₁ + r₂) r₃
          (tensorInt k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁) (partBase sB₂ e₂)
              (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sB₁ e₁)
                (relativeDimension_partBase sB₂ e₂) r₁ r₂ α₁ α₂) α₃) ≍
      pf[(tensorBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))
          (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃))), (prodBase (partBase
              (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + (d₂ + d₃))) (partBase (prodBase sB₁
                  (prodBase sB₂ sB₃)) (e₁ + (e₂ + e₃)))), ((prodHom (prodBase (partBase sA₁ d₁)
                      (partBase (prodBase sA₂ sA₃) (d₂ + d₃))) (prodBase (partBase sB₁ e₁)
                          (partBase (prodBase sB₂ sB₃) (e₂ + e₃)))
          (prodBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))) (prodBase
              (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)))
          (prodHom (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sA₁ d₁)
              (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃)) (𝟙 _) (partProdHom k sA₂ sA₃ d₂ d₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃))
          (prodHom (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (partBase sB₁ e₁)
              (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)) (𝟙 _) (partProdHom k sB₂ sB₃ e₂ e₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁ (d₂ + d₃) e₁
                  (e₂ + e₃))),
      by rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase],
      (((e₁ + (e₂ + e₃) : ℕ) : ℤ) - (r₁ + (r₂ + r₃)))] (tensorInt k (partBase sA₁ d₁) (prodBase
          (partBase sA₂ d₂) (partBase sA₃ d₃)) (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂)
              (partBase sB₃ e₃))
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sA₁ d₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sA₃ d₃)) (relativeDimension_partBase sB₁ e₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₂ e₂)
            (relativeDimension_partBase sB₃ e₃)) r₁ (r₂ + r₃) α₁ (tensorInt k (partBase sA₂ d₂)
                (partBase sA₃ d₃) (partBase sB₂ e₂) (partBase sB₃ e₃)
                    (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₂ d₂) (relativeDimension_partBase sA₃ d₃)
            (relativeDimension_partBase sB₂ e₂)
                (relativeDimension_partBase sB₃ e₃) r₂ r₃ α₂ α₃)) := by
  have hassoc := tensorInt_assoc k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sA₃ d₃)
      (partBase sB₁ e₁) (partBase sB₂ e₂) (partBase sB₃ e₃)
    (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
    (relativeDimension_partBase sA₃ d₃) (relativeDimension_partBase sB₁ e₁)
    (relativeDimension_partBase sB₂ e₂) (relativeDimension_partBase sB₃ e₃)
    (prodAssocHom (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sA₃ d₃)) (prodAssocHom_fst _ _ _)
        (prodAssocHom_snd_fst _ _ _)
    (prodAssocHom_snd_snd _ _ _) (prodAssocHom (partBase sB₁ e₁) (partBase sB₂ e₂)
        (partBase sB₃ e₃)) (prodAssocHom_fst _ _ _)
    (prodAssocHom_snd_fst _ _ _) (prodAssocHom_snd_snd _ _ _) r₁ r₂ r₃ α₁ α₂ α₃
  have hcomp := properChowPushforward_comp_apply (fieldChowSituation k) _ _ _
    (tensorAssocHom k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sA₃ d₃) (partBase sB₁ e₁)
        (partBase sB₂ e₂) (partBase sB₃ e₃) (prodAssocHom (partBase sA₁ d₁) (partBase sA₂ d₂)
            (partBase sA₃ d₃))
          (prodAssocHom (partBase sB₁ e₁) (partBase sB₂ e₂) (partBase sB₃ e₃))
              (prodAssocHom_fst _ _ _) (prodAssocHom_fst _ _ _)) ((prodHom (prodBase
                  (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃))) (prodBase
                      (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)))
          (prodBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))) (prodBase
              (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)))
          (prodHom (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sA₁ d₁)
              (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃)) (𝟙 _) (partProdHom k sA₂ sA₃ d₂ d₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃))
          (prodHom (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (partBase sB₁ e₁)
              (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)) (𝟙 _) (partProdHom k sB₂ sB₃ e₂ e₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁ (d₂ + d₃) e₁
                  (e₂ + e₃))) _ rfl (prodHom_comp_prodBase _ _ _ _ _ _ _ _)
    (by rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase])
    (by rw [Category.assoc, Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase,
      prodHom_comp_prodBase])
    (((e₁ + e₂ + e₃ : ℕ) : ℤ) - (r₁ + r₂ + r₃)) (properPushforwardDescends _ _ _ _ _ _)
        (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
            (tensorInt k (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase
                (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃)
          (canonicalDiagonalClassFamily k)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₁ d₁)
            (relativeDimension_partBase sA₂ d₂)) (relativeDimension_partBase sA₃ d₃)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₁ e₁)
            (relativeDimension_partBase sB₂ e₂)) (relativeDimension_partBase sB₃ e₃) (r₁ + r₂) r₃
          (tensorInt k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁) (partBase sB₂ e₂)
              (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sB₁ e₁) (relativeDimension_partBase sB₂ e₂) r₁ r₂ α₁ α₂) α₃)
  refine (properChowPushforward_parts_heq k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁
      (prodBase sB₂ sB₃)) _ (Nat.add_assoc d₁ d₂ d₃)
    (Nat.add_assoc e₁ e₂ e₃) _ _ ((tensorAssocHom k (partBase sA₁ d₁) (partBase sA₂ d₂)
        (partBase sA₃ d₃) (partBase sB₁ e₁) (partBase sB₂ e₂) (partBase sB₃ e₃) (prodAssocHom
            (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sA₃ d₃))
          (prodAssocHom (partBase sB₁ e₁) (partBase sB₂ e₂) (partBase sB₃ e₃))
              (prodAssocHom_fst _ _ _) (prodAssocHom_fst _ _ _)) ≫ ((prodHom (prodBase
                  (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃))) (prodBase
                      (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)))
          (prodBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))) (prodBase
              (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)))
          (prodHom (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sA₁ d₁)
              (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃)) (𝟙 _) (partProdHom k sA₂ sA₃ d₂ d₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃))
          (prodHom (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (partBase sB₁ e₁)
              (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)) (𝟙 _) (partProdHom k sB₂ sB₃ e₂ e₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁ (d₂ + d₃) e₁
                  (e₂ + e₃))))
    (by rw [Category.assoc, Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase,
      prodHom_comp_prodBase])
    (tensorBlockHom_assoc k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA hφA₁ hφA₂ hφA₃ φB hφB₁ hφB₂ hφB₃
      d₁ d₂ d₃ e₁ e₂ e₃) rfl _ _ HEq.rfl).trans ?_
  rw [hcomp]
  exact properChowPushforward_heq_congr (fieldChowSituation k) _ _ _ _ (by push_cast; ring)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) _ _ hassoc

/-- The left side of associativity on pure blocks. -/
theorem assoc_lhs_tmul (r₁ r₂ r₃ : ℤ) (d₁ e₁ d₂ e₂ d₃ e₃ : ℕ) (q₁ q₂ q₃ : ℚ)
    (α₁ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₁ d₁) (partBase sB₁ e₁))
        (((e₁ : ℕ) : ℤ) - r₁)) (α₂ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₂ d₂)
            (partBase sB₂ e₂)) (((e₂ : ℕ) : ℤ) - r₂))
    (α₃ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₃ d₃) (partBase sB₃ e₃))
        (((e₃ : ℕ) : ℤ) - r₃)) :
    corrEquivOfIso k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃)
        (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φA φB
            (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁)
        (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (r₁ + r₂ + r₃)
        (tensor k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (canonicalDiagonalClassFamily k)
          (r₁ + r₂) r₃ (tensor k sA₁ sA₂ sB₁ sB₂ (canonicalDiagonalClassFamily k) r₁ r₂
            (DirectSum.lof ℚ ℕ _ d₁ (DirectSum.lof ℚ ℕ _ e₁ (q₁ ⊗ₜ[ℤ] α₁))) (DirectSum.lof ℚ ℕ _ d₂
                (DirectSum.lof ℚ ℕ _ e₂ (q₂ ⊗ₜ[ℤ] α₂)))) (DirectSum.lof ℚ ℕ _ d₃
                    (DirectSum.lof ℚ ℕ _ e₃ (q₃ ⊗ₜ[ℤ] α₃)))) =
      DirectSum.lof ℚ ℕ _ (d₁ + d₂ + d₃) (DirectSum.lof ℚ ℕ _ (e₁ + e₂ + e₃) ((q₁ * q₂ * q₃) ⊗ₜ[ℤ]
        pf[(tensorBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase
            (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃)), (prodBase (partBase
                (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase (prodBase sB₁
                    (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃))), ((prodHom (prodBase (partBase
                        (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃)) (prodBase (partBase
                            (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃))
          (prodBase (prodBase (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃)) (prodBase
              (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃))
          (prodHom (partBase (prodBase sA₁ sA₂) (d₁ + d₂)) (partBase sA₃ d₃) (prodBase
              (partBase sA₁ d₁) (partBase sA₂ d₂)) (partBase sA₃ d₃) (partProdHom k sA₁ sA₂ d₁ d₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sA₁ sA₂ d₁ d₂) (Category.id_comp _))
          (prodHom (partBase (prodBase sB₁ sB₂) (e₁ + e₂)) (partBase sB₃ e₃) (prodBase
              (partBase sB₁ e₁) (partBase sB₂ e₂)) (partBase sB₃ e₃) (partProdHom k sB₁ sB₂ e₁ e₂)
                  (𝟙 _)
            (partProdHom_comp_partBase k sB₁ sB₂ e₁ e₂) (Category.id_comp _))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (d₁ + d₂) d₃
                  (e₁ + e₂) e₃) ≫
        (prodHom (partBase (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + d₂ + d₃)) (partBase
            (prodBase sB₁ (prodBase sB₂ sB₃)) (e₁ + e₂ + e₃)) (partBase (prodBase
                (prodBase sA₁ sA₂) sA₃) (d₁ + d₂ + d₃)) (partBase (prodBase (prodBase sB₁ sB₂) sB₃)
                    (e₁ + e₂ + e₃))
          (partMap (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃) φA
              (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (d₁ + d₂ + d₃))
          (partMap (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φB
              (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (e₁ + e₂ + e₃))
          (partMap_comp_partBase _ _ _ _ _) (partMap_comp_partBase _ _ _ _ _))),
      by simp only [Category.assoc, prodHom_comp_prodBase],
      (((e₁ + e₂ + e₃ : ℕ) : ℤ) - (r₁ + r₂ + r₃))] (tensorInt k (prodBase (partBase sA₁ d₁)
          (partBase sA₂ d₂)) (partBase sA₃ d₃) (prodBase (partBase sB₁ e₁) (partBase sB₂ e₂))
              (partBase sB₃ e₃)
          (canonicalDiagonalClassFamily k)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₁ d₁)
            (relativeDimension_partBase sA₂ d₂)) (relativeDimension_partBase sA₃ d₃)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₁ e₁)
            (relativeDimension_partBase sB₂ e₂)) (relativeDimension_partBase sB₃ e₃) (r₁ + r₂) r₃
          (tensorInt k (partBase sA₁ d₁) (partBase sA₂ d₂) (partBase sB₁ e₁) (partBase sB₂ e₂)
              (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₁ d₁) (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sB₁ e₁)
                (relativeDimension_partBase sB₂ e₂) r₁ r₂ α₁ α₂) α₃))) := by
  have h₄ := assoc_left_int k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA hφA₁ φB hφB₁ r₁ r₂ r₃ d₁ e₁ d₂ e₂ d₃ e₃
    α₁ α₂ α₃
  simp only [tensor_lof_lof_tmul, corrEquivOfIso_lof_lof]
  refine lof_lof_congr k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃)) ?_
  rw [correspondenceEquivOfIso_tmul, h₄]

/-- The right side of associativity on pure blocks. -/
theorem assoc_rhs_tmul (r₁ r₂ r₃ : ℤ) (d₁ e₁ d₂ e₂ d₃ e₃ : ℕ) (q₁ q₂ q₃ : ℚ)
    (α₁ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₁ d₁) (partBase sB₁ e₁))
        (((e₁ : ℕ) : ℤ) - r₁)) (α₂ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₂ d₂)
            (partBase sB₂ e₂)) (((e₂ : ℕ) : ℤ) - r₂))
    (α₃ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₃ d₃) (partBase sB₃ e₃))
        (((e₃ : ℕ) : ℤ) - r₃)) :
    tensor k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) (canonicalDiagonalClassFamily k)
        r₁ (r₂ + r₃) (DirectSum.lof ℚ ℕ _ d₁ (DirectSum.lof ℚ ℕ _ e₁ (q₁ ⊗ₜ[ℤ] α₁)))
        (tensor k sA₂ sA₃ sB₂ sB₃ (canonicalDiagonalClassFamily k) r₂ r₃
          (DirectSum.lof ℚ ℕ _ d₂ (DirectSum.lof ℚ ℕ _ e₂ (q₂ ⊗ₜ[ℤ] α₂))) (DirectSum.lof ℚ ℕ _ d₃
              (DirectSum.lof ℚ ℕ _ e₃ (q₃ ⊗ₜ[ℤ] α₃)))) =
      DirectSum.lof ℚ ℕ _ (d₁ + (d₂ + d₃)) (DirectSum.lof ℚ ℕ _ (e₁ + (e₂ + e₃))
          ((q₁ * q₂ * q₃) ⊗ₜ[ℤ]
        pf[(tensorBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))
            (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃))), (prodBase (partBase
                (prodBase sA₁ (prodBase sA₂ sA₃)) (d₁ + (d₂ + d₃))) (partBase (prodBase sB₁
                    (prodBase sB₂ sB₃)) (e₁ + (e₂ + e₃)))), ((prodHom (prodBase (partBase sA₁ d₁)
                        (partBase (prodBase sA₂ sA₃) (d₂ + d₃))) (prodBase (partBase sB₁ e₁)
                            (partBase (prodBase sB₂ sB₃) (e₂ + e₃)))
          (prodBase (partBase sA₁ d₁) (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃))) (prodBase
              (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)))
          (prodHom (partBase sA₁ d₁) (partBase (prodBase sA₂ sA₃) (d₂ + d₃)) (partBase sA₁ d₁)
              (prodBase (partBase sA₂ d₂) (partBase sA₃ d₃)) (𝟙 _) (partProdHom k sA₂ sA₃ d₂ d₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sA₂ sA₃ d₂ d₃))
          (prodHom (partBase sB₁ e₁) (partBase (prodBase sB₂ sB₃) (e₂ + e₃)) (partBase sB₁ e₁)
              (prodBase (partBase sB₂ e₂) (partBase sB₃ e₃)) (𝟙 _) (partProdHom k sB₂ sB₃ e₂ e₃)
            (Category.id_comp _) (partProdHom_comp_partBase k sB₂ sB₃ e₂ e₃))
          (prodHom_comp_prodBase _ _ _ _ _ _ _ _) (prodHom_comp_prodBase _ _ _ _ _ _ _ _)) ≫
              (tensorBlockHom k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) d₁ (d₂ + d₃) e₁
                  (e₂ + e₃))),
      by rw [Category.assoc, tensorBlockHom_comp_prodBase, prodHom_comp_prodBase],
      (((e₁ + (e₂ + e₃) : ℕ) : ℤ) - (r₁ + (r₂ + r₃)))] (tensorInt k (partBase sA₁ d₁) (prodBase
          (partBase sA₂ d₂) (partBase sA₃ d₃)) (partBase sB₁ e₁) (prodBase (partBase sB₂ e₂)
              (partBase sB₃ e₃))
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sA₁ d₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sA₂ d₂)
            (relativeDimension_partBase sA₃ d₃)) (relativeDimension_partBase sB₁ e₁)
          (relativeDimension_prodBase_add k _ _ (relativeDimension_partBase sB₂ e₂)
            (relativeDimension_partBase sB₃ e₃)) r₁ (r₂ + r₃) α₁ (tensorInt k (partBase sA₂ d₂)
                (partBase sA₃ d₃) (partBase sB₂ e₂) (partBase sB₃ e₃)
                    (canonicalDiagonalClassFamily k)
            (relativeDimension_partBase sA₂ d₂) (relativeDimension_partBase sA₃ d₃)
            (relativeDimension_partBase sB₂ e₂)
                (relativeDimension_partBase sB₃ e₃) r₂ r₃ α₂ α₃)))) := by
  have h₄ := assoc_right_int k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ r₁ r₂ r₃ d₁ e₁ d₂ e₂ d₃ e₃ α₁ α₂ α₃
  simp only [tensor_lof_lof_tmul]
  refine lof_lof_congr k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃)) ?_
  rw [h₄, mul_assoc]

include hφA₂ hφA₃ hφB₂ hφB₃ in
/-- **Associativity of the tensor product of correspondences** on pure blocks. -/
theorem corrEquivOfIso_tensor_tensor_tmul (r₁ r₂ r₃ : ℤ) (d₁ e₁ d₂ e₂ d₃ e₃ : ℕ) (q₁ q₂ q₃ : ℚ)
    (α₁ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₁ d₁) (partBase sB₁ e₁))
        (((e₁ : ℕ) : ℤ) - r₁)) (α₂ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₂ d₂)
            (partBase sB₂ e₂)) (((e₂ : ℕ) : ℤ) - r₂))
    (α₃ : chowGroup (fieldChowSituation k) (prodBase (partBase sA₃ d₃) (partBase sB₃ e₃))
        (((e₃ : ℕ) : ℤ) - r₃)) :
    corrEquivOfIso k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃)
        (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φA φB
            (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁)
        (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁) (r₁ + r₂ + r₃)
        (tensor k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (canonicalDiagonalClassFamily k)
          (r₁ + r₂) r₃ (tensor k sA₁ sA₂ sB₁ sB₂ (canonicalDiagonalClassFamily k) r₁ r₂
            (DirectSum.lof ℚ ℕ _ d₁ (DirectSum.lof ℚ ℕ _ e₁ (q₁ ⊗ₜ[ℤ] α₁))) (DirectSum.lof ℚ ℕ _ d₂
                (DirectSum.lof ℚ ℕ _ e₂ (q₂ ⊗ₜ[ℤ] α₂)))) (DirectSum.lof ℚ ℕ _ d₃
                    (DirectSum.lof ℚ ℕ _ e₃ (q₃ ⊗ₜ[ℤ] α₃)))) =
      corrCongr k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃))
          (add_assoc r₁ r₂ r₃).symm
        (tensor k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) (canonicalDiagonalClassFamily k)
          r₁ (r₂ + r₃) (DirectSum.lof ℚ ℕ _ d₁ (DirectSum.lof ℚ ℕ _ e₁ (q₁ ⊗ₜ[ℤ] α₁)))
          (tensor k sA₂ sA₃ sB₂ sB₃ (canonicalDiagonalClassFamily k) r₂ r₃
            (DirectSum.lof ℚ ℕ _ d₂ (DirectSum.lof ℚ ℕ _ e₂ (q₂ ⊗ₜ[ℤ] α₂))) (DirectSum.lof ℚ ℕ _ d₃
                (DirectSum.lof ℚ ℕ _ e₃ (q₃ ⊗ₜ[ℤ] α₃))))) :=
  (assoc_lhs_tmul k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA hφA₁ φB hφB₁ r₁ r₂ r₃ d₁ e₁ d₂ e₂ d₃ e₃
    q₁ q₂ q₃ α₁ α₂ α₃).trans ((lof_lof_eq_corrCongr k (prodBase sA₁ (prodBase sA₂ sA₃))
        (prodBase sB₁ (prodBase sB₂ sB₃)) (add_assoc r₁ r₂ r₃).symm
      (Nat.add_assoc d₁ d₂ d₃) (Nat.add_assoc e₁ e₂ e₃) (q₁ * q₂ * q₃) _ _ _ _ rfl rfl
      (assoc_parts_heq k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA hφA₁ hφA₂ hφA₃ φB hφB₁ hφB₂ hφB₃ r₁ r₂ r₃
        d₁ e₁ d₂ e₂ d₃ e₃ α₁ α₂ α₃)).trans
      (congrArg (corrCongr k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃))
          (add_assoc r₁ r₂ r₃).symm)
        (assoc_rhs_tmul k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ r₁ r₂ r₃ d₁ e₁ d₂ e₂ d₃ e₃ q₁ q₂ q₃ α₁ α₂
          α₃).symm))

include hφA₂ hφA₃ hφB₂ hφB₃ in
/-- **Associativity of the tensor product of correspondences** (Stacks 0FG7): for isomorphisms
`φA : (A₁ × A₂) × A₃ ≅ A₁ × (A₂ × A₃)` and `φB : (B₁ × B₂) × B₃ ≅ B₁ ×
    (B₂ × B₃)` compatible with the
three projections, transporting `(c₁ ⊗ c₂) ⊗ c₃` along `φA × φB` gives `c₁ ⊗ (c₂ ⊗ c₃)`, for the
canonical diagonal classes. -/
theorem corrEquivOfIso_tensor_tensor (r₁ r₂ r₃ : ℤ) (a₁ : Corr k sA₁ sB₁ r₁)
    (a₂ : Corr k sA₂ sB₂ r₂) (a₃ : Corr k sA₃ sB₃ r₃) :
    corrEquivOfIso k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃)
        (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φA φB
        (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁)
        (r₁ + r₂ + r₃)
        (tensor k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (canonicalDiagonalClassFamily k)
          (r₁ + r₂) r₃ (tensor k sA₁ sA₂ sB₁ sB₂ (canonicalDiagonalClassFamily k) r₁ r₂ a₁ a₂)
          a₃) =
      corrCongr k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃))
        (add_assoc r₁ r₂ r₃).symm
        (tensor k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) (canonicalDiagonalClassFamily k)
          r₁ (r₂ + r₃) a₁
          (tensor k sA₂ sA₃ sB₂ sB₃ (canonicalDiagonalClassFamily k) r₂ r₃ a₂ a₃)) :=
  corr_trilinear_ext k sA₁ sB₁ sA₂ sB₂ sA₃ sB₃
    (tensor k sA₁ sA₂ sB₁ sB₂ (canonicalDiagonalClassFamily k) r₁ r₂)
    (tensor k (prodBase sA₁ sA₂) sA₃ (prodBase sB₁ sB₂) sB₃ (canonicalDiagonalClassFamily k)
      (r₁ + r₂) r₃)
    (corrEquivOfIso k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase (prodBase sA₁ sA₂) sA₃)
      (prodBase sB₁ (prodBase sB₂ sB₃)) (prodBase (prodBase sB₁ sB₂) sB₃) φA φB
      (assocHom_comp_prodBase sA₁ sA₂ sA₃ φA hφA₁) (assocHom_comp_prodBase sB₁ sB₂ sB₃ φB hφB₁)
      (r₁ + r₂ + r₃))
    (tensor k sA₂ sA₃ sB₂ sB₃ (canonicalDiagonalClassFamily k) r₂ r₃)
    (tensor k sA₁ (prodBase sA₂ sA₃) sB₁ (prodBase sB₂ sB₃) (canonicalDiagonalClassFamily k)
      r₁ (r₂ + r₃))
    (corrCongr k (prodBase sA₁ (prodBase sA₂ sA₃)) (prodBase sB₁ (prodBase sB₂ sB₃))
      (add_assoc r₁ r₂ r₃).symm)
    (corrEquivOfIso_tensor_tensor_tmul k sA₁ sA₂ sA₃ sB₁ sB₂ sB₃ φA hφA₁ hφA₂ hφA₃ φB hφB₁ hφB₂
      hφB₃ r₁ r₂ r₃) a₁ a₂ a₃

end Assoc

end Stacks.WeilCohomology

end
