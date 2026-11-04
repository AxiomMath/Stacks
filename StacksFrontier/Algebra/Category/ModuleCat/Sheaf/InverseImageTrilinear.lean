module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrilinearPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor
public import StacksCore.Tactic.StacksAttribute

/-! # The inverse image of a triple pairing of sheaves of modules

Let `f : Sh(C) → Sh(D)` be a morphism of topoi and let `O` be a sheaf of rings on `D`.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor` proves that the inverse image
of sheaves of modules along `f` carries bilinear pairings to bilinear pairings, bijectively:
`Bilin_{f⁻¹O}(f⁻¹F × f⁻¹G, N) = Bilin_O(F × G, f_*N)`, the "interesting equality" of the proof
of Stacks 03EL.

This file is the **three-variable form**,
`Stacks.SheafOfModules.inverseImageTrilinearEquiv`:

`Trilin_{f⁻¹O}(f⁻¹F × f⁻¹G × f⁻¹H, N) = Trilin_O(F × G × H, f_*N)`,

for the trilinear pairings of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrilinearPairing`. Like the binary one it cannot
be done on sections — a morphism of topoi has no description of `f⁻¹` or `f_*` on sections — so
each of the six trilinearity squares is transported in the form of a commuting square of
morphisms of sheaves of sets.

## Main definitions

* `Stacks.SheafOfModules.prodComparison₄`, `prodComparison₄'`, `prodComparison₄''`: the iterated
  product comparisons of a functor at a quadruple product, in the three shapes
  `((X ⨯ Y) ⨯ Z) ⨯ T`, `(X ⨯ (Y ⨯ Z)) ⨯ T` and `(X ⨯ Y) ⨯ (Z ⨯ T)` which the six trilinearity
  squares live over. Each is an isomorphism when the functor preserves finite products.
* `Stacks.SheafOfModules.inverseImagePairingEquiv₃`: the bijection between triple pairings of
  the inverse images and triple pairings into the direct image, with no trilinearity required.

## Main results

* `Stacks.SheafOfModules.inverseImage_addLeftSquare₃_iff` and its five companions: each of the
  six trilinearity squares for a triple pairing of the inverse images holds if and only if the
  corresponding square for the transposed pairing does.
* `Stacks.SheafOfModules.inverseImageTrilinearEquiv`: **the trilinear pairings of the inverse
  images are the trilinear pairings into the direct image.**

## Implementation notes

**The transport used here is the binary `Stacks.SheafOfModules.square_transport_iff`.** The
arity of the pairing and the arity of the operation on the *target* of a linearity square are
independent: additivity in one argument of a pairing of any arity says that the pairing composed
with an operation on one factor equals a *binary* operation — addition, or the scalar action —
applied to *two* legs. So all six squares here have two legs and a binary target operation,
exactly as the four binary ones do, and the only thing that grows with the arity is the *source*,
which is a quadruple rather than a triple product. That is why the three `prodComparison₄`
variants are what this file needs.

Otherwise each transport has the same two-step shape as its binary original. First the square,
whose source is a quadruple product of inverse images, is moved to one whose source is the
inverse image of a quadruple product by precomposition with the iterated product comparison;
this is an isomorphism because `f⁻¹` is left exact. Then `square_transport_iff` moves it across
the adjunction. `Stacks.Sheaves.ToposPullback.moduleAdd_map_aux'` and `moduleSMul_map_aux'` enter
the first step unchanged, and on the direct-image side the scalar squares pick up the unit
`O ⟶ f_*f⁻¹O` through `Stacks.SheafOfModules.moduleSMulHom_directImage`, again unchanged.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

/-! ## Quadruple product comparisons -/

section Iterated

universe v u v' u'

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  [HasFiniteProducts E] [HasFiniteProducts F] (Φ : F ⥤ E)

/-- The iterated product comparison `Φ(((X ⨯ Y) ⨯ Z) ⨯ T) ⟶ ((ΦX ⨯ ΦY) ⨯ ΦZ) ⨯ ΦT`. -/
def prodComparison₄ (X Y Z T : F) :
    Φ.obj (((X ⨯ Y) ⨯ Z) ⨯ T) ⟶ ((Φ.obj X ⨯ Φ.obj Y) ⨯ Φ.obj Z) ⨯ Φ.obj T :=
  prodComparison Φ ((X ⨯ Y) ⨯ Z) T ≫ prod.map (prodComparison₃ Φ X Y Z) (𝟙 (Φ.obj T))

/-- The iterated product comparison `Φ((X ⨯ (Y ⨯ Z)) ⨯ T) ⟶ (ΦX ⨯ (ΦY ⨯ ΦZ)) ⨯ ΦT`. -/
def prodComparison₄' (X Y Z T : F) :
    Φ.obj ((X ⨯ (Y ⨯ Z)) ⨯ T) ⟶ (Φ.obj X ⨯ (Φ.obj Y ⨯ Φ.obj Z)) ⨯ Φ.obj T :=
  prodComparison Φ (X ⨯ (Y ⨯ Z)) T ≫ prod.map (prodComparison₃' Φ X Y Z) (𝟙 (Φ.obj T))

/-- The iterated product comparison `Φ((X ⨯ Y) ⨯ (Z ⨯ T)) ⟶ (ΦX ⨯ ΦY) ⨯ (ΦZ ⨯ ΦT)`. -/
def prodComparison₄'' (X Y Z T : F) :
    Φ.obj ((X ⨯ Y) ⨯ (Z ⨯ T)) ⟶ (Φ.obj X ⨯ Φ.obj Y) ⨯ (Φ.obj Z ⨯ Φ.obj T) :=
  prodComparison Φ (X ⨯ Y) (Z ⨯ T) ≫
    prod.map (prodComparison Φ X Y) (prodComparison Φ Z T)

variable [PreservesFiniteProducts Φ]

/-- The iterated product comparison `Stacks.SheafOfModules.prodComparison₄` is an isomorphism
when the functor preserves finite products. -/
instance isIso_prodComparison₄ (X Y Z T : F) : IsIso (prodComparison₄ Φ X Y Z T) := by
  have h₁ : IsIso (prodComparison Φ ((X ⨯ Y) ⨯ Z) T) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  rw [prodComparison₄]
  infer_instance

/-- The iterated product comparison `Stacks.SheafOfModules.prodComparison₄'` is an isomorphism
when the functor preserves finite products. -/
instance isIso_prodComparison₄' (X Y Z T : F) : IsIso (prodComparison₄' Φ X Y Z T) := by
  have h₁ : IsIso (prodComparison Φ (X ⨯ (Y ⨯ Z)) T) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  rw [prodComparison₄']
  infer_instance

/-- The iterated product comparison `Stacks.SheafOfModules.prodComparison₄''` is an isomorphism
when the functor preserves finite products. -/
instance isIso_prodComparison₄'' (X Y Z T : F) : IsIso (prodComparison₄'' Φ X Y Z T) := by
  have h₁ : IsIso (prodComparison Φ (X ⨯ Y) (Z ⨯ T)) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  have h₂ : IsIso (prodComparison Φ X Y) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  have h₃ : IsIso (prodComparison Φ Z T) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  rw [prodComparison₄'']
  infer_instance

variable {Φ}

/-- A binary operation on the first two of four factors, read through the iterated product
comparison. -/
lemma prodComparison₄_comp_prodMap {X Y X' Z T : F} (opO : X ⨯ Y ⟶ X')
    (opΦ : Φ.obj X ⨯ Φ.obj Y ⟶ Φ.obj X')
    (hop : prodComparison Φ X Y ≫ opΦ = Φ.map opO) :
    prodComparison₄ Φ X Y Z T ≫ prod.map (prod.map opΦ (𝟙 (Φ.obj Z))) (𝟙 (Φ.obj T)) =
      Φ.map (prod.map (prod.map opO (𝟙 Z)) (𝟙 T)) ≫ prodComparison₃ Φ X' Z T := by
  rw [prodComparison₄, Category.assoc, prod.map_map, Category.comp_id,
    prodComparison₃_comp_prodMap opO opΦ hop]
  refine prod.hom_ext ?_ ?_ <;> simp [prodComparison₃, ← Functor.map_comp, ← Functor.map_comp_assoc]

/-- A binary operation on the second and third of four factors, read through the iterated
product comparison. -/
lemma prodComparison₄'_comp_prodMap {X Y Z Z' T : F} (opO : Y ⨯ Z ⟶ Z')
    (opΦ : Φ.obj Y ⨯ Φ.obj Z ⟶ Φ.obj Z')
    (hop : prodComparison Φ Y Z ≫ opΦ = Φ.map opO) :
    prodComparison₄' Φ X Y Z T ≫ prod.map (prod.map (𝟙 (Φ.obj X)) opΦ) (𝟙 (Φ.obj T)) =
      Φ.map (prod.map (prod.map (𝟙 X) opO) (𝟙 T)) ≫ prodComparison₃ Φ X Z' T := by
  rw [prodComparison₄', Category.assoc, prod.map_map, Category.comp_id,
    prodComparison₃'_comp_prodMap opO opΦ hop]
  refine prod.hom_ext ?_ ?_ <;> simp [prodComparison₃, ← Functor.map_comp, ← Functor.map_comp_assoc]

/-- A binary operation on the last two of four factors, read through the iterated product
comparison. -/
lemma prodComparison₄''_comp_prodMap {X Y Z T T' : F} (opO : Z ⨯ T ⟶ T')
    (opΦ : Φ.obj Z ⨯ Φ.obj T ⟶ Φ.obj T')
    (hop : prodComparison Φ Z T ≫ opΦ = Φ.map opO) :
    prodComparison₄'' Φ X Y Z T ≫ prod.map (𝟙 (Φ.obj X ⨯ Φ.obj Y)) opΦ =
      Φ.map (prod.map (𝟙 (X ⨯ Y)) opO) ≫ prodComparison₃ Φ X Y T' := by
  rw [prodComparison₄'', Category.assoc, prod.map_map, Category.comp_id, hop]
  refine prod.hom_ext ?_ ?_ <;> simp [prodComparison₃, ← Functor.map_comp, ← Functor.map_comp_assoc]

/-- Keeping the first, third and fourth of four factors, read through the iterated product
comparison. -/
lemma prodComparison₄_comp_liftFstFstFst {X Y Z T : F} :
    prodComparison₄ Φ X Y Z T ≫
        prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          prod.snd =
      Φ.map (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          prod.snd) ≫
        prodComparison₃ Φ X Z T := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;>
    simp [prodComparison₄, prodComparison₃, ← Functor.map_comp, ← Functor.map_comp_assoc]

/-- Keeping the second, third and fourth of four factors, read through the iterated product
comparison. -/
lemma prodComparison₄_comp_liftFstFstSnd {X Y Z T : F} :
    prodComparison₄ Φ X Y Z T ≫
        prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.snd) (prod.fst ≫ prod.snd))
          prod.snd =
      Φ.map (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.snd) (prod.fst ≫ prod.snd))
          prod.snd) ≫
        prodComparison₃ Φ Y Z T := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;>
    simp [prodComparison₄, prodComparison₃, ← Functor.map_comp, ← Functor.map_comp_assoc]

omit [PreservesFiniteProducts Φ] in
/-- Keeping only the first of four factors, read through the iterated product comparison. -/
lemma prodComparison₄_comp_fstFstFst {X Y Z T : F} :
    prodComparison₄ Φ X Y Z T ≫ (prod.fst ≫ prod.fst ≫ prod.fst) =
      Φ.map (prod.fst ≫ prod.fst ≫ prod.fst) ≫ 𝟙 (Φ.obj X) := by
  simp [prodComparison₄, prodComparison₃, ← Functor.map_comp]

/-- Keeping the first, second and fourth factors, read through the iterated product comparison
of the middle association. -/
lemma prodComparison₄'_comp_liftSndFst {X Y Z T : F} :
    prodComparison₄' Φ X Y Z T ≫
        prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.fst))
          prod.snd =
      Φ.map (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.fst))
          prod.snd) ≫
        prodComparison₃ Φ X Y T := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;>
    simp [prodComparison₄', prodComparison₃, prodComparison₃', ← Functor.map_comp,
      ← Functor.map_comp_assoc]

/-- Keeping the first, third and fourth factors, read through the iterated product comparison
of the middle association. -/
lemma prodComparison₄'_comp_liftSndSnd {X Y Z T : F} :
    prodComparison₄' Φ X Y Z T ≫
        prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.snd))
          prod.snd =
      Φ.map (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.snd))
          prod.snd) ≫
        prodComparison₃ Φ X Z T := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;>
    simp [prodComparison₄', prodComparison₃, prodComparison₃', ← Functor.map_comp,
      ← Functor.map_comp_assoc]

omit [PreservesFiniteProducts Φ] in
/-- Keeping only the second of four factors, read through the iterated product comparison of
the middle association. -/
lemma prodComparison₄'_comp_fstSndFst {X Y Z T : F} :
    prodComparison₄' Φ X Y Z T ≫ (prod.fst ≫ prod.snd ≫ prod.fst) =
      Φ.map (prod.fst ≫ prod.snd ≫ prod.fst) ≫ 𝟙 (Φ.obj Y) := by
  simp [prodComparison₄', prodComparison₃', ← Functor.map_comp]

/-- Keeping the first, second and third factors, read through the iterated product comparison
of the right association. -/
lemma prodComparison₄''_comp_liftSndFst {X Y Z T : F} :
    prodComparison₄'' Φ X Y Z T ≫
        prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          (prod.snd ≫ prod.fst) =
      Φ.map (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          (prod.snd ≫ prod.fst)) ≫
        prodComparison₃ Φ X Y Z := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;>
    simp [prodComparison₄'', prodComparison₃, ← Functor.map_comp, ← Functor.map_comp_assoc]

/-- Keeping the first, second and fourth factors, read through the iterated product comparison
of the right association. -/
lemma prodComparison₄''_comp_liftSndSnd {X Y Z T : F} :
    prodComparison₄'' Φ X Y Z T ≫
        prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          (prod.snd ≫ prod.snd) =
      Φ.map (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
          (prod.snd ≫ prod.snd)) ≫
        prodComparison₃ Φ X Y T := by
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;>
    simp [prodComparison₄'', prodComparison₃, ← Functor.map_comp, ← Functor.map_comp_assoc]

omit [PreservesFiniteProducts Φ] in
/-- Keeping only the third of four factors, read through the iterated product comparison of the
right association. -/
lemma prodComparison₄''_comp_sndFst {X Y Z T : F} :
    prodComparison₄'' Φ X Y Z T ≫ (prod.snd ≫ prod.fst) =
      Φ.map (prod.snd ≫ prod.fst) ≫ 𝟙 (Φ.obj Z) := by
  simp [prodComparison₄'', ← Functor.map_comp]

end Iterated

/-! ## The six trilinearity squares along a morphism of topoi -/

section InverseImage

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

variable (O : Sheaf K RingCat.{w'})
  (F G H : SheafOfModules.{w'} O) (N : SheafOfModules.{w} (inverseImageRingSheaf f O))

/-- The bijection between triple pairings of the inverse images of three sheaves of modules and
triple pairings of the three sheaves themselves with values in the direct image: compose with
the iterated product comparison of `f⁻¹`, which is an isomorphism because `f⁻¹` is left exact,
and transpose across the adjunction `f⁻¹ ⊣ f_*`. The three-variable form of
`Stacks.SheafOfModules.inverseImagePairingEquiv`. -/
def inverseImagePairingEquiv₃ :
    ((f.inverseImage.obj (moduleSheaf O F) ⨯ f.inverseImage.obj (moduleSheaf O G)) ⨯
        f.inverseImage.obj (moduleSheaf O H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) ≃
      ((moduleSheaf O F ⨯ moduleSheaf O G) ⨯ moduleSheaf O H ⟶
        moduleSheaf O ((directImageModules f O).obj N)) where
  toFun q := f.adj.homEquiv _ _
    (prodComparison₃ f.inverseImage (moduleSheaf O F) (moduleSheaf O G)
      (moduleSheaf O H) ≫ q)
  invFun p := inv (prodComparison₃ f.inverseImage (moduleSheaf O F) (moduleSheaf O G)
      (moduleSheaf O H)) ≫ (f.adj.homEquiv _ _).symm p
  left_inv _ := by
    simp only [Equiv.symm_apply_apply]
    exact IsIso.inv_hom_id_assoc _ _
  right_inv _ := by
    simp only [IsIso.hom_inv_id_assoc]
    exact Equiv.apply_symm_apply _ _

/-- `Stacks.SheafOfModules.inverseImagePairingEquiv₃` sends a triple pairing of the inverse
images to the transpose across `f⁻¹ ⊣ f_*` of its composite with the iterated product
comparison of `f⁻¹`. -/
@[simp]
lemma inverseImagePairingEquiv₃_apply
    (q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    inverseImagePairingEquiv₃ f O F G H N q =
      f.adj.homEquiv _ _
        (prodComparison₃ f.inverseImage (moduleSheaf O F) (moduleSheaf O G)
          (moduleSheaf O H) ≫ q) := rfl

/-- Transport of an additivity square with values in `N` across the adjunction `f⁻¹ ⊣ f_*`. -/
private lemma add_square_transport_iff {Y A A₁ A₂ : Sheaf K (Type w')} {P : Sheaf J (Type w)}
    (γ : f.inverseImage.obj Y ⟶ P) [IsIso γ]
    (L D₁ D₂ : P ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (a : f.inverseImage.obj A ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (a₁ : f.inverseImage.obj A₁ ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (a₂ : f.inverseImage.obj A₂ ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (m : Y ⟶ A) (d₁ : Y ⟶ A₁) (d₂ : Y ⟶ A₂)
    (hL : γ ≫ L = f.inverseImage.map m ≫ a) (h₁ : γ ≫ D₁ = f.inverseImage.map d₁ ≫ a₁)
    (h₂ : γ ≫ D₂ = f.inverseImage.map d₂ ≫ a₂) :
    L = prod.lift D₁ D₂ ≫ moduleAddHom (inverseImageRingSheaf f O) N ↔
      m ≫ f.adj.homEquiv A _ a =
        prod.lift (d₁ ≫ f.adj.homEquiv A₁ _ a₁) (d₂ ≫ f.adj.homEquiv A₂ _ a₂) ≫
          moduleAddHom O ((directImageModules f O).obj N) :=
  square_transport_iff f.adj γ L D₁ D₂ a a₁ a₂ m d₁ d₂ _ _
    (moduleAdd_map_aux' K f.pushforward (inverseImageRingSheaf f O) N).symm hL h₁ h₂

/-- Transport of a scalar-compatibility square with values in `N` across the adjunction
`f⁻¹ ⊣ f_*`, the scalars on the direct-image side acting through the unit `O ⟶ f_*f⁻¹O`. -/
private lemma smul_square_transport_iff {Y A A₂ : Sheaf K (Type w')} {P : Sheaf J (Type w)}
    (γ : f.inverseImage.obj Y ⟶ P) [IsIso γ]
    (L : P ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (D₁ : P ⟶ Sheaf.ringSheaf (inverseImageRingSheaf f O))
    (D₂ : P ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (a : f.inverseImage.obj A ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (a₂ : f.inverseImage.obj A₂ ⟶ moduleSheaf (inverseImageRingSheaf f O) N)
    (m : Y ⟶ A) (d₁ : Y ⟶ Sheaf.ringSheaf O) (d₂ : Y ⟶ A₂)
    (hL : γ ≫ L = f.inverseImage.map m ≫ a)
    (h₁ : γ ≫ D₁ = f.inverseImage.map d₁ ≫
      (𝟙 (Sheaf.ringSheaf (inverseImageRingSheaf f O)) :
        f.inverseImage.obj (Sheaf.ringSheaf O) ⟶ _))
    (h₂ : γ ≫ D₂ = f.inverseImage.map d₂ ≫ a₂) :
    L = prod.lift D₁ D₂ ≫ moduleSMulHom (inverseImageRingSheaf f O) N ↔
      m ≫ f.adj.homEquiv A _ a =
        prod.lift d₁ (d₂ ≫ f.adj.homEquiv A₂ _ a₂) ≫
          moduleSMulHom O ((directImageModules f O).obj N) := by
  refine (square_transport_iff f.adj γ L D₁ D₂ a _ a₂ m d₁ d₂ _ _
    (moduleSMul_map_aux' K f.pushforward (inverseImageRingSheaf f O) N).symm hL h₁ h₂).trans
    (Eq.congr rfl ?_)
  exact lift_comp_prodMap_eq _ _ d₁ _ _ (moduleSMulHom_directImage f O N)

/-- Additivity in the first argument of a triple pairing transports across the adjunction
`f⁻¹ ⊣ f_*`. -/
lemma inverseImage_addLeftSquare₃_iff
    (q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    addLeftSquare₃ (inverseImageRingSheaf f O) q ↔
      addLeftSquare₃ O (inverseImagePairingEquiv₃ f O F G H N q) := by
  rw [addLeftSquare₃, addLeftSquare₃, inverseImagePairingEquiv₃_apply]
  exact add_square_transport_iff f O N
    (prodComparison₄ f.inverseImage (moduleSheaf O F) (moduleSheaf O F) (moduleSheaf O G)
      (moduleSheaf O H))
    _ _ _ _ _ _
    (prod.map (prod.map (moduleAddHom O F) (𝟙 (moduleSheaf O G))) (𝟙 (moduleSheaf O H)))
    (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd)) prod.snd)
    (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.snd) (prod.fst ≫ prod.snd)) prod.snd)
    (comp_assoc_eq q (prodComparison₄_comp_prodMap _ _
      (moduleAdd_map_aux' J f.inverseImage O F).symm))
    (comp_assoc_eq q prodComparison₄_comp_liftFstFstFst)
    (comp_assoc_eq q prodComparison₄_comp_liftFstFstSnd)

/-- Additivity in the second argument of a triple pairing transports across the adjunction
`f⁻¹ ⊣ f_*`. -/
lemma inverseImage_addMidSquare₃_iff
    (q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    addMidSquare₃ (inverseImageRingSheaf f O) q ↔
      addMidSquare₃ O (inverseImagePairingEquiv₃ f O F G H N q) := by
  rw [addMidSquare₃, addMidSquare₃, inverseImagePairingEquiv₃_apply]
  exact add_square_transport_iff f O N
    (prodComparison₄' f.inverseImage (moduleSheaf O F) (moduleSheaf O G) (moduleSheaf O G)
      (moduleSheaf O H))
    _ _ _ _ _ _
    (prod.map (prod.map (𝟙 (moduleSheaf O F)) (moduleAddHom O G)) (𝟙 (moduleSheaf O H)))
    (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.fst)) prod.snd)
    (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.snd)) prod.snd)
    (comp_assoc_eq q (prodComparison₄'_comp_prodMap _ _
      (moduleAdd_map_aux' J f.inverseImage O G).symm))
    (comp_assoc_eq q prodComparison₄'_comp_liftSndFst)
    (comp_assoc_eq q prodComparison₄'_comp_liftSndSnd)

/-- Additivity in the third argument of a triple pairing transports across the adjunction
`f⁻¹ ⊣ f_*`. -/
lemma inverseImage_addRightSquare₃_iff
    (q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    addRightSquare₃ (inverseImageRingSheaf f O) q ↔
      addRightSquare₃ O (inverseImagePairingEquiv₃ f O F G H N q) := by
  rw [addRightSquare₃, addRightSquare₃, inverseImagePairingEquiv₃_apply]
  exact add_square_transport_iff f O N
    (prodComparison₄'' f.inverseImage (moduleSheaf O F) (moduleSheaf O G) (moduleSheaf O H)
      (moduleSheaf O H))
    _ _ _ _ _ _
    (prod.map (𝟙 (moduleSheaf O F ⨯ moduleSheaf O G)) (moduleAddHom O H))
    (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd)) (prod.snd ≫ prod.fst))
    (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd)) (prod.snd ≫ prod.snd))
    (comp_assoc_eq q (prodComparison₄''_comp_prodMap _ _
      (moduleAdd_map_aux' J f.inverseImage O H).symm))
    (comp_assoc_eq q prodComparison₄''_comp_liftSndFst)
    (comp_assoc_eq q prodComparison₄''_comp_liftSndSnd)

/-- Compatibility with scalars in the first argument of a triple pairing transports across the
adjunction `f⁻¹ ⊣ f_*`, the scalars on the direct-image side acting through the unit
`O ⟶ f_*f⁻¹O`. -/
lemma inverseImage_smulLeftSquare₃_iff
    (q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    smulLeftSquare₃ (inverseImageRingSheaf f O) q ↔
      smulLeftSquare₃ O (inverseImagePairingEquiv₃ f O F G H N q) := by
  rw [smulLeftSquare₃, smulLeftSquare₃, inverseImagePairingEquiv₃_apply]
  exact smul_square_transport_iff f O N
    (prodComparison₄ f.inverseImage (Sheaf.ringSheaf O) (moduleSheaf O F) (moduleSheaf O G)
      (moduleSheaf O H))
    _ _ _ _ _
    (prod.map (prod.map (moduleSMulHom O F) (𝟙 (moduleSheaf O G))) (𝟙 (moduleSheaf O H)))
    (prod.fst ≫ prod.fst ≫ prod.fst)
    (prod.lift (prod.lift (prod.fst ≫ prod.fst ≫ prod.snd) (prod.fst ≫ prod.snd)) prod.snd)
    (comp_assoc_eq q (prodComparison₄_comp_prodMap _ _
      (moduleSMul_map_aux' J f.inverseImage O F).symm))
    prodComparison₄_comp_fstFstFst
    (comp_assoc_eq q prodComparison₄_comp_liftFstFstSnd)

/-- Compatibility with scalars in the second argument of a triple pairing transports across the
adjunction `f⁻¹ ⊣ f_*`, the scalars on the direct-image side acting through the unit
`O ⟶ f_*f⁻¹O`. -/
lemma inverseImage_smulMidSquare₃_iff
    (q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    smulMidSquare₃ (inverseImageRingSheaf f O) q ↔
      smulMidSquare₃ O (inverseImagePairingEquiv₃ f O F G H N q) := by
  rw [smulMidSquare₃, smulMidSquare₃, inverseImagePairingEquiv₃_apply]
  exact smul_square_transport_iff f O N
    (prodComparison₄' f.inverseImage (moduleSheaf O F) (Sheaf.ringSheaf O) (moduleSheaf O G)
      (moduleSheaf O H))
    _ _ _ _ _
    (prod.map (prod.map (𝟙 (moduleSheaf O F)) (moduleSMulHom O G)) (𝟙 (moduleSheaf O H)))
    (prod.fst ≫ prod.snd ≫ prod.fst)
    (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd ≫ prod.snd)) prod.snd)
    (comp_assoc_eq q (prodComparison₄'_comp_prodMap _ _
      (moduleSMul_map_aux' J f.inverseImage O G).symm))
    prodComparison₄'_comp_fstSndFst
    (comp_assoc_eq q prodComparison₄'_comp_liftSndSnd)

/-- Compatibility with scalars in the third argument of a triple pairing transports across the
adjunction `f⁻¹ ⊣ f_*`, the scalars on the direct-image side acting through the unit
`O ⟶ f_*f⁻¹O`. -/
lemma inverseImage_smulRightSquare₃_iff
    (q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    smulRightSquare₃ (inverseImageRingSheaf f O) q ↔
      smulRightSquare₃ O (inverseImagePairingEquiv₃ f O F G H N q) := by
  rw [smulRightSquare₃, smulRightSquare₃, inverseImagePairingEquiv₃_apply]
  exact smul_square_transport_iff f O N
    (prodComparison₄'' f.inverseImage (moduleSheaf O F) (moduleSheaf O G) (Sheaf.ringSheaf O)
      (moduleSheaf O H))
    _ _ _ _ _
    (prod.map (𝟙 (moduleSheaf O F ⨯ moduleSheaf O G)) (moduleSMulHom O H))
    (prod.snd ≫ prod.fst)
    (prod.lift (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd)) (prod.snd ≫ prod.snd))
    (comp_assoc_eq q (prodComparison₄''_comp_prodMap _ _
      (moduleSMul_map_aux' J f.inverseImage O H).symm))
    prodComparison₄''_comp_sndFst
    (comp_assoc_eq q prodComparison₄''_comp_liftSndSnd)

/-- **The trilinear pairings of the inverse images are the trilinear pairings into the direct
image**: `Trilin_{f⁻¹O}(f⁻¹F × f⁻¹G × f⁻¹H, N) = Trilin_O(F × G × H, f_*N)`. The three-variable
form of `Stacks.SheafOfModules.inverseImageBilinearEquiv`. -/
def inverseImageTrilinearEquiv :
    { q : (moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G)) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj H) ⟶
          moduleSheaf (inverseImageRingSheaf f O) N //
      IsTrilinearPairing (inverseImageRingSheaf f O) q } ≃
      { p : (moduleSheaf O F ⨯ moduleSheaf O G) ⨯ moduleSheaf O H ⟶
          moduleSheaf O ((directImageModules f O).obj N) // IsTrilinearPairing O p } :=
  Equiv.subtypeEquiv (inverseImagePairingEquiv₃ f O F G H N) fun q ↦ by
    rw [isTrilinearPairing_iff_squares, isTrilinearPairing_iff_squares,
      inverseImage_addLeftSquare₃_iff, inverseImage_addMidSquare₃_iff,
      inverseImage_addRightSquare₃_iff, inverseImage_smulLeftSquare₃_iff,
      inverseImage_smulMidSquare₃_iff, inverseImage_smulRightSquare₃_iff]
    exact Iff.rfl

end InverseImage

end Stacks.SheafOfModules

end
