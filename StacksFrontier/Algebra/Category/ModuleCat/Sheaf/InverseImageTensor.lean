module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-! # The inverse image of a tensor product of sheaves of modules

Let `f : Sh(C) → Sh(D)` be a morphism of topoi and let `O` be a sheaf of rings on `D`. The
inverse image of sheaves of modules along `f` (Stacks 03D2) is left adjoint to the direct
image (Stacks 03D3), and the content of this file is that it carries bilinear pairings to
bilinear pairings, bijectively:

`Bilin_{f⁻¹O}(f⁻¹F × f⁻¹G, N) = Bilin_O(F × G, f_*N)`.

This is the "interesting equality" of the proof of Stacks 03EL. The source calls it
straightforward, and it is, but it cannot be done on sections: a morphism of topoi has no
description of `f⁻¹` or of `f_*` on sections, so bilinearity has to be moved across the
adjunction in the form of commuting squares of morphisms of sheaves of sets. That is what
`Stacks.SheafOfModules.addLeftSquare` and its companions are for.

## Main definitions

* `Stacks.SheafOfModules.inverseImagePairingEquiv`: the bijection between pairings of the
  inverse images and pairings into the direct image, with no bilinearity required.
* `Stacks.SheafOfModules.inverseImageBilinearEquiv`: the same bijection, restricted to the
  bilinear pairings on both sides.

## Main results

* `Stacks.SheafOfModules.homEquiv_pairSquare_iff`: the general transport of a square across an
  adjunction whose left adjoint preserves finite products. Both sides of such a square are a
  composite of the image of a morphism downstairs with a pairing, and this is the statement
  that such an equation holds if and only if the corresponding equation for the adjuncts does.
* `Stacks.SheafOfModules.inverseImage_addLeftSquare_iff` and its three companions: each of the
  four bilinearity squares for a pairing of the inverse images holds if and only if the
  corresponding square for the transposed pairing does.

## Implementation notes

The four square transports all have the same two-step shape. First the square, whose source is
a triple product `(f⁻¹F ⨯ f⁻¹F) ⨯ f⁻¹G` of inverse images, is moved to one whose source is the
inverse image `f⁻¹((F ⨯ F) ⨯ G)` of a triple product, by precomposition with the iterated
product comparison; this is an isomorphism because `f⁻¹` is left exact, so the move is an
equivalence. Then `homEquiv_pairSquare_iff` moves it across the adjunction. The first step is
where `Stacks.Sheaves.ToposPullback.moduleAdd_map_aux'` and `moduleSMul_map_aux'` enter: they
say that the operations of an inverse-image module are the inverse images of the original
operations, read through the product comparison.

On the direct-image side the module structure is the one of
`Stacks.Sheaves.RingedToposModules.directImageModules`, i.e. restricted along the unit
`O ⟶ f_*f⁻¹O`. Restriction of scalars leaves the addition map of the underlying sheaf of sets
alone, so the additivity squares need no adjustment; for the scalar squares the unit appears,
exactly as it does in `homEquiv_moduleSMulHom_iff`, and
`Stacks.Sheaves.RingedToposModules.moduleSMulHom_restrictScalars` together with
`homEquiv_id_eq_ringUnit` put it there.

### The chain of Tag 03EL, and where each link is

Tag 03EL is `f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G` for a morphism of ringed topoi, naturally in
`F` and `G`. The pullback of Stacks 03D6 part (2) factors as

```
Stacks.Sheaves.RingedToposModules.pullbackModules f =
  inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
    extendScalarsFSharp f
```

that is, inverse image followed by extension of scalars along `f⁻¹O_D ⟶ O_C`, so the source's
chain of equalities becomes, for a sheaf of `O_C`-modules `N`:

1. `Hom_{O_C}(f^*(F ⊗ G), N) = Hom_{O_D}(F ⊗ G, f_*N)` — Stacks 03D7,
   `pullbackAdjPushforwardModules`;
2. `Hom_{O_D}(F ⊗ G, f_*N) = Bilin_{O_D}(F × G, f_*N)` — `bilinearEquivTensorHom`;
3. `Bilin_{O_D}(F × G, f_*N) = Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|_{f⁻¹O_D})` —
   `inverseImageBilinearEquiv`, this file;
4. `Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|_{f⁻¹O_D}) = Bilin_{O_C}(f^*F × f^*G, N)` —
   `Stacks.SheafOfModules.extendScalarsBilinearEquiv`, in
   `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsBilinearPairing`;
5. `Bilin_{O_C}(f^*F × f^*G, N) = Hom_{O_C}(f^*F ⊗ f^*G, N)` — `bilinearEquivTensorHom`.

Step 4 is base change: a bilinear pairing of `O_C ⊗_{f⁻¹O_D} f⁻¹F` and `O_C ⊗_{f⁻¹O_D} f⁻¹G`
is the same thing as an `f⁻¹O_D`-bilinear pairing of `f⁻¹F` and `f⁻¹G`. It is proved by
composing the universal property of the tensor product sheaf on each side with the adjunction of
Tag 03CZ and the monoidality
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` of extension of scalars, which is
itself the presheaf-level base change of Tag 03CU transported along sheafification by Tag 05NA.
It needs no transport of linearity squares, because both of its sides live over the same site
and the comparison between them is an isomorphism of sheaves of modules rather than merely an
adjunction; that is the one respect in which it is easier than step 3. The three-variable form,
which the associativity constraint of the pullback consumes, is
`Stacks.SheafOfModules.extendScalarsTrilinearEquiv`.

All five steps are therefore available, and each is natural in `N`: steps 1, 2, 3 and 5 in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality`, step 4 as
`Stacks.SheafOfModules.extendScalarsBilinearEquiv_naturality`. So Yoneda turns the composite
into the isomorphism of Tag 03EL, whose naturality in `F` and `G` is then a hom-extensionality
check on pure tensors (`tensorSectionPairing`).

The three-variable chain is complete at the level of statements but not of naturality: the
trilinear analogues of `Stacks.SheafOfModules.IsBilinearPairing.comp` and of
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom_naturality` are not available, so
`Stacks.SheafOfModules.extendScalarsTrilinearEquiv` has no naturality lemma yet.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

/-! ## Transport of a pairing square across an adjunction -/

section Transport

universe v u v' u'

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  [HasFiniteProducts E] [HasFiniteProducts F]
  {Φ : F ⥤ E} {Ψ : E ⥤ F} (adj : Φ ⊣ Ψ)

/-- The adjunct of a product comparison followed by a product of two morphisms and a binary
operation is the product of the adjuncts followed by the transported operation. -/
lemma homEquiv_prodComparison_prodMap_comp {A₁ A₂ : F} {B₁ B₂ B : E}
    (a₁ : Φ.obj A₁ ⟶ B₁) (a₂ : Φ.obj A₂ ⟶ B₂) (n : B₁ ⨯ B₂ ⟶ B)
    (n' : Ψ.obj B₁ ⨯ Ψ.obj B₂ ⟶ Ψ.obj B) (hn : prodComparison Ψ B₁ B₂ ≫ n' = Ψ.map n) :
    adj.homEquiv (A₁ ⨯ A₂) B (prodComparison Φ A₁ A₂ ≫ prod.map a₁ a₂ ≫ n) =
      prod.map (adj.homEquiv A₁ B₁ a₁) (adj.homEquiv A₂ B₂ a₂) ≫ n' := by
  rw [← Category.assoc, adj.homEquiv_naturality_right, ← hn, ← Category.assoc,
    homEquiv_prodComparison_prodMap adj]

/-- **Transport of a pairing square across an adjunction.** Both sides of a bilinearity square
are the image under `Φ` of a morphism of the base category followed by a pairing; such an
equation holds if and only if the corresponding equation for the adjuncts holds. -/
lemma homEquiv_pairSquare_iff {X A A₁ A₂ : F} {B B₁ B₂ : E} (a : Φ.obj A ⟶ B)
    (a₁ : Φ.obj A₁ ⟶ B₁) (a₂ : Φ.obj A₂ ⟶ B₂) (m : X ⟶ A) (d₁ : X ⟶ A₁) (d₂ : X ⟶ A₂)
    (n : B₁ ⨯ B₂ ⟶ B) (n' : Ψ.obj B₁ ⨯ Ψ.obj B₂ ⟶ Ψ.obj B)
    (hn : prodComparison Ψ B₁ B₂ ≫ n' = Ψ.map n) :
    Φ.map m ≫ a = prod.lift (Φ.map d₁ ≫ a₁) (Φ.map d₂ ≫ a₂) ≫ n ↔
      m ≫ adj.homEquiv A B a =
        prod.lift (d₁ ≫ adj.homEquiv A₁ B₁ a₁) (d₂ ≫ adj.homEquiv A₂ B₂ a₂) ≫ n' := by
  have key : prod.lift (Φ.map d₁ ≫ a₁) (Φ.map d₂ ≫ a₂) =
      Φ.map (prod.lift d₁ d₂) ≫ prodComparison Φ A₁ A₂ ≫ prod.map a₁ a₂ :=
    prod.hom_ext (by simp [← Functor.map_comp_assoc])
      (by simp [← Functor.map_comp_assoc])
  have key' : prod.lift (d₁ ≫ adj.homEquiv A₁ B₁ a₁) (d₂ ≫ adj.homEquiv A₂ B₂ a₂) =
      prod.lift d₁ d₂ ≫
        prod.map (adj.homEquiv A₁ B₁ a₁) (adj.homEquiv A₂ B₂ a₂) :=
    prod.hom_ext (by simp) (by simp)
  rw [key, key']
  simp only [Category.assoc]
  rw [← Equiv.apply_eq_iff_eq (adj.homEquiv X B), adj.homEquiv_naturality_left,
    adj.homEquiv_naturality_left, homEquiv_prodComparison_prodMap_comp adj a₁ a₂ n n' hn]

omit [HasFiniteProducts F] in
/-- A right-hand side of a pairing square in which the first argument is carried along a
morphism `u` of the scalar object, rewritten as the same square for the pairing composed with
`u` on the first factor. -/
lemma lift_comp_prodMap_eq {Y W W' B B' : E} (u : W ⟶ W') (y : Y ⟶ B') (d : Y ⟶ W)
    (n : W' ⨯ B' ⟶ B) (n' : W ⨯ B' ⟶ B) (hn : n' = prod.map u (𝟙 B') ≫ n) :
    prod.lift (d ≫ u) y ≫ n = prod.lift d y ≫ n' := by
  rw [hn, ← Category.assoc, prod.lift_map, Category.comp_id]

omit [HasFiniteProducts E] [HasFiniteProducts F] in
/-- Appending a morphism to a compatibility between two comparisons. -/
lemma comp_assoc_eq {X P W B Y : E} {γ : X ⟶ P} {D : P ⟶ W} {u : X ⟶ Y} {c : Y ⟶ W}
    (q : W ⟶ B) (h : γ ≫ D = u ≫ c) : γ ≫ D ≫ q = u ≫ c ≫ q := by
  rw [← Category.assoc, h, Category.assoc]

/-- **The two-step transport of a bilinearity square.** A square whose source is a product of
images of `Φ` is first moved, along an isomorphism `γ` out of the image of a product, to one
whose source is an image, and then across the adjunction. -/
lemma square_transport_iff {Y A A₁ A₂ : F} {P B B₁ B₂ : E}
    (γ : Φ.obj Y ⟶ P) [IsIso γ]
    (L : P ⟶ B) (D₁ : P ⟶ B₁) (D₂ : P ⟶ B₂)
    (a : Φ.obj A ⟶ B) (a₁ : Φ.obj A₁ ⟶ B₁) (a₂ : Φ.obj A₂ ⟶ B₂)
    (m : Y ⟶ A) (d₁ : Y ⟶ A₁) (d₂ : Y ⟶ A₂)
    (n : B₁ ⨯ B₂ ⟶ B) (n' : Ψ.obj B₁ ⨯ Ψ.obj B₂ ⟶ Ψ.obj B)
    (hn : prodComparison Ψ B₁ B₂ ≫ n' = Ψ.map n)
    (hL : γ ≫ L = Φ.map m ≫ a) (h₁ : γ ≫ D₁ = Φ.map d₁ ≫ a₁)
    (h₂ : γ ≫ D₂ = Φ.map d₂ ≫ a₂) :
    L = prod.lift D₁ D₂ ≫ n ↔
      m ≫ adj.homEquiv A B a =
        prod.lift (d₁ ≫ adj.homEquiv A₁ B₁ a₁) (d₂ ≫ adj.homEquiv A₂ B₂ a₂) ≫ n' := by
  have eR : γ ≫ prod.lift D₁ D₂ ≫ n = prod.lift (Φ.map d₁ ≫ a₁) (Φ.map d₂ ≫ a₂) ≫ n := by
    rw [← Category.assoc, prod.comp_lift, h₁, h₂]
  rw [← cancel_epi γ, hL, eR]
  exact homEquiv_pairSquare_iff adj a a₁ a₂ m d₁ d₂ n n' hn

/-- `square_transport_iff` for a pairing whose first argument is a scalar: the adjunct of `a₁`
is moved onto the first factor of the transported operation. -/
private lemma square_transport_iff_of_comp {Y A A₁ A₂ : F} {P B B₁ B₂ : E}
    (γ : Φ.obj Y ⟶ P) [IsIso γ]
    (L : P ⟶ B) (D₁ : P ⟶ B₁) (D₂ : P ⟶ B₂)
    (a : Φ.obj A ⟶ B) (a₁ : Φ.obj A₁ ⟶ B₁) (a₂ : Φ.obj A₂ ⟶ B₂)
    (m : Y ⟶ A) (d₁ : Y ⟶ A₁) (d₂ : Y ⟶ A₂)
    (n : B₁ ⨯ B₂ ⟶ B) (n' : Ψ.obj B₁ ⨯ Ψ.obj B₂ ⟶ Ψ.obj B)
    (n₀ : A₁ ⨯ Ψ.obj B₂ ⟶ Ψ.obj B)
    (hn : prodComparison Ψ B₁ B₂ ≫ n' = Ψ.map n)
    (hn₀ : n₀ = prod.map (adj.homEquiv A₁ B₁ a₁) (𝟙 (Ψ.obj B₂)) ≫ n')
    (hL : γ ≫ L = Φ.map m ≫ a) (h₁ : γ ≫ D₁ = Φ.map d₁ ≫ a₁)
    (h₂ : γ ≫ D₂ = Φ.map d₂ ≫ a₂) :
    L = prod.lift D₁ D₂ ≫ n ↔
      m ≫ adj.homEquiv A B a = prod.lift d₁ (d₂ ≫ adj.homEquiv A₂ B₂ a₂) ≫ n₀ :=
  (square_transport_iff adj γ _ _ _ _ _ _ _ _ _ _ _ hn hL h₁ h₂).trans
    (Eq.congr rfl (lift_comp_prodMap_eq _ _ _ _ _ hn₀))

end Transport

/-! ## Iterated product comparisons -/

section Iterated

universe v u v' u'

variable {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
  [HasFiniteProducts E] [HasFiniteProducts F] (Φ : F ⥤ E)

/-- The iterated product comparison `Φ((X ⨯ Y) ⨯ Z) ⟶ (ΦX ⨯ ΦY) ⨯ ΦZ`. -/
def prodComparison₃ (X Y Z : F) :
    Φ.obj ((X ⨯ Y) ⨯ Z) ⟶ (Φ.obj X ⨯ Φ.obj Y) ⨯ Φ.obj Z :=
  prodComparison Φ (X ⨯ Y) Z ≫ prod.map (prodComparison Φ X Y) (𝟙 (Φ.obj Z))

/-- The iterated product comparison `Φ(X ⨯ (Y ⨯ Z)) ⟶ ΦX ⨯ (ΦY ⨯ ΦZ)`. -/
def prodComparison₃' (X Y Z : F) :
    Φ.obj (X ⨯ (Y ⨯ Z)) ⟶ Φ.obj X ⨯ (Φ.obj Y ⨯ Φ.obj Z) :=
  prodComparison Φ X (Y ⨯ Z) ≫ prod.map (𝟙 (Φ.obj X)) (prodComparison Φ Y Z)

variable [PreservesFiniteProducts Φ]

/-- The iterated product comparison `Φ((X ⨯ Y) ⨯ Z) ⟶ (ΦX ⨯ ΦY) ⨯ ΦZ` is an isomorphism
when `Φ` preserves finite products. -/
instance isIso_prodComparison₃ (X Y Z : F) : IsIso (prodComparison₃ Φ X Y Z) := by
  have h₁ : IsIso (prodComparison Φ (X ⨯ Y) Z) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  have h₂ : IsIso (prodComparison Φ X Y) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  rw [prodComparison₃]
  infer_instance

/-- The iterated product comparison `Φ(X ⨯ (Y ⨯ Z)) ⟶ ΦX ⨯ (ΦY ⨯ ΦZ)` is an isomorphism
when `Φ` preserves finite products. -/
instance isIso_prodComparison₃' (X Y Z : F) : IsIso (prodComparison₃' Φ X Y Z) := by
  have h₁ : IsIso (prodComparison Φ X (Y ⨯ Z)) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  have h₂ : IsIso (prodComparison Φ Y Z) := by
    rw [← PreservesLimitPair.iso_hom]; infer_instance
  rw [prodComparison₃']
  infer_instance

variable {Φ}

/-- A binary operation on the first two factors, read through the iterated product
comparison. -/
lemma prodComparison₃_comp_prodMap {X Y X' Z : F} (opO : X ⨯ Y ⟶ X')
    (opΦ : Φ.obj X ⨯ Φ.obj Y ⟶ Φ.obj X')
    (hop : prodComparison Φ X Y ≫ opΦ = Φ.map opO) :
    prodComparison₃ Φ X Y Z ≫ prod.map opΦ (𝟙 (Φ.obj Z)) =
      Φ.map (prod.map opO (𝟙 Z)) ≫ prodComparison Φ X' Z := by
  rw [prodComparison₃, Category.assoc, prod.map_map, hop, Category.comp_id,
    ← CategoryTheory.Functor.map_id Φ Z, ← prodComparison_natural]

/-- A binary operation on the last two factors, read through the iterated product
comparison. -/
lemma prodComparison₃'_comp_prodMap {X Y Z Z' : F} (opO : Y ⨯ Z ⟶ Z')
    (opΦ : Φ.obj Y ⨯ Φ.obj Z ⟶ Φ.obj Z')
    (hop : prodComparison Φ Y Z ≫ opΦ = Φ.map opO) :
    prodComparison₃' Φ X Y Z ≫ prod.map (𝟙 (Φ.obj X)) opΦ =
      Φ.map (prod.map (𝟙 X) opO) ≫ prodComparison Φ X Z' := by
  rw [prodComparison₃', Category.assoc, prod.map_map, hop, Category.comp_id,
    ← CategoryTheory.Functor.map_id Φ X, ← prodComparison_natural]

/-- Keeping the first and third factors, read through the iterated product comparison. -/
lemma prodComparison₃_comp_liftFstFst {X Y Z : F} :
    prodComparison₃ Φ X Y Z ≫ prod.lift (prod.fst ≫ prod.fst) prod.snd =
      Φ.map (prod.lift (prod.fst ≫ prod.fst) prod.snd) ≫ prodComparison Φ X Z := by
  refine prod.hom_ext ?_ ?_ <;> simp [prodComparison₃, ← Functor.map_comp]

/-- Keeping the second and third factors, read through the iterated product comparison. -/
lemma prodComparison₃_comp_liftFstSnd {X Y Z : F} :
    prodComparison₃ Φ X Y Z ≫ prod.lift (prod.fst ≫ prod.snd) prod.snd =
      Φ.map (prod.lift (prod.fst ≫ prod.snd) prod.snd) ≫ prodComparison Φ Y Z := by
  refine prod.hom_ext ?_ ?_ <;> simp [prodComparison₃, ← Functor.map_comp]

omit [PreservesFiniteProducts Φ] in
/-- Keeping only the first factor, read through the iterated product comparison. -/
lemma prodComparison₃_comp_fstFst {X Y Z : F} :
    prodComparison₃ Φ X Y Z ≫ (prod.fst ≫ prod.fst) =
      Φ.map (prod.fst ≫ prod.fst) ≫ 𝟙 (Φ.obj X) := by
  simp [prodComparison₃, ← Functor.map_comp]

/-- Keeping the first and second factors, read through the iterated product comparison. -/
lemma prodComparison₃'_comp_liftFstFst {X Y Z : F} :
    prodComparison₃' Φ X Y Z ≫ prod.lift prod.fst (prod.snd ≫ prod.fst) =
      Φ.map (prod.lift prod.fst (prod.snd ≫ prod.fst)) ≫ prodComparison Φ X Y := by
  refine prod.hom_ext ?_ ?_ <;> simp [prodComparison₃', ← Functor.map_comp]

/-- Keeping the first and third factors, read through the iterated product comparison of the
other association. -/
lemma prodComparison₃'_comp_liftFstSnd {X Y Z : F} :
    prodComparison₃' Φ X Y Z ≫ prod.lift prod.fst (prod.snd ≫ prod.snd) =
      Φ.map (prod.lift prod.fst (prod.snd ≫ prod.snd)) ≫ prodComparison Φ X Z := by
  refine prod.hom_ext ?_ ?_ <;> simp [prodComparison₃', ← Functor.map_comp]

omit [PreservesFiniteProducts Φ] in
/-- Keeping only the second factor, read through the iterated product comparison of the other
association. -/
lemma prodComparison₃'_comp_sndFst {X Y Z : F} :
    prodComparison₃' Φ X Y Z ≫ (prod.snd ≫ prod.fst) =
      Φ.map (prod.snd ≫ prod.fst) ≫ 𝟙 (Φ.obj Y) := by
  simp [prodComparison₃', ← Functor.map_comp]

end Iterated

/-! ## The four bilinearity squares along a morphism of topoi -/

section InverseImage

universe w w' v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

variable (O : Sheaf K RingCat.{w'})
  (F G : SheafOfModules.{w'} O) (N : SheafOfModules.{w} (inverseImageRingSheaf f O))

/-- The bijection between pairings of the inverse images of two sheaves of modules and
pairings of the two sheaves themselves with values in the direct image: compose with the
product comparison of `f⁻¹`, which is an isomorphism because `f⁻¹` is left exact, and transpose
across the adjunction `f⁻¹ ⊣ f_*`. -/
def inverseImagePairingEquiv :
    (f.inverseImage.obj (moduleSheaf O F) ⨯ f.inverseImage.obj (moduleSheaf O G) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) ≃
      (moduleSheaf O F ⨯ moduleSheaf O G ⟶
        moduleSheaf O ((directImageModules f O).obj N)) where
  toFun q := f.adj.homEquiv _ _
    ((PreservesLimitPair.iso f.inverseImage (moduleSheaf O F) (moduleSheaf O G)).hom ≫ q)
  invFun p := (PreservesLimitPair.iso f.inverseImage (moduleSheaf O F)
    (moduleSheaf O G)).inv ≫ (f.adj.homEquiv _ _).symm p
  left_inv _ := by
    simp only [Equiv.symm_apply_apply]
    exact Iso.inv_hom_id_assoc _ _
  right_inv _ := by
    simp only [Iso.hom_inv_id_assoc]
    exact Equiv.apply_symm_apply _ _

/-- `inverseImagePairingEquiv` sends a pairing `q` of the inverse images to the adjunct of its
precomposition with the product comparison of `f⁻¹`. -/
@[simp]
lemma inverseImagePairingEquiv_apply
    (q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    inverseImagePairingEquiv f O F G N q =
      f.adj.homEquiv _ _
        (prodComparison f.inverseImage (moduleSheaf O F) (moduleSheaf O G) ≫ q) := rfl

/-- Additivity in the first argument transports across the adjunction `f⁻¹ ⊣ f_*`. -/
lemma inverseImage_addLeftSquare_iff
    (q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    addLeftSquare (inverseImageRingSheaf f O) q ↔
      addLeftSquare O (inverseImagePairingEquiv f O F G N q) := by
  rw [addLeftSquare, addLeftSquare, inverseImagePairingEquiv_apply]
  exact square_transport_iff f.adj
    (prodComparison₃ f.inverseImage (moduleSheaf O F) (moduleSheaf O F) (moduleSheaf O G))
    _ _ _ _ _ _ (prod.map (moduleAddHom O F) (𝟙 (moduleSheaf O G)))
    (prod.lift (prod.fst ≫ prod.fst) prod.snd) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
    (moduleAddHom (inverseImageRingSheaf f O) N)
    (moduleAddHom O ((directImageModules f O).obj N))
    (moduleAdd_map_aux' K f.pushforward (inverseImageRingSheaf f O) N).symm
    (comp_assoc_eq q (prodComparison₃_comp_prodMap _ _
      (moduleAdd_map_aux' J f.inverseImage O F).symm))
    (comp_assoc_eq q prodComparison₃_comp_liftFstFst)
    (comp_assoc_eq q prodComparison₃_comp_liftFstSnd)

/-- Additivity in the second argument transports across the adjunction `f⁻¹ ⊣ f_*`. -/
lemma inverseImage_addRightSquare_iff
    (q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    addRightSquare (inverseImageRingSheaf f O) q ↔
      addRightSquare O (inverseImagePairingEquiv f O F G N q) := by
  rw [addRightSquare, addRightSquare, inverseImagePairingEquiv_apply]
  exact square_transport_iff f.adj
    (prodComparison₃' f.inverseImage (moduleSheaf O F) (moduleSheaf O G) (moduleSheaf O G))
    _ _ _ _ _ _ (prod.map (𝟙 (moduleSheaf O F)) (moduleAddHom O G))
    (prod.lift prod.fst (prod.snd ≫ prod.fst)) (prod.lift prod.fst (prod.snd ≫ prod.snd))
    (moduleAddHom (inverseImageRingSheaf f O) N)
    (moduleAddHom O ((directImageModules f O).obj N))
    (moduleAdd_map_aux' K f.pushforward (inverseImageRingSheaf f O) N).symm
    (comp_assoc_eq q (prodComparison₃'_comp_prodMap _ _
      (moduleAdd_map_aux' J f.inverseImage O G).symm))
    (comp_assoc_eq q prodComparison₃'_comp_liftFstFst)
    (comp_assoc_eq q prodComparison₃'_comp_liftFstSnd)

/-- The scalar action on the direct image is the scalar action over the direct-image ring,
precomposed with the unit `O ⟶ f_*f⁻¹O` on the scalar factor. The unit is written as the
adjunct of the identity, which is the form in which it appears on the right-hand side of a
transported scalar square. -/
lemma moduleSMulHom_directImage :
    moduleSMulHom O ((directImageModules f O).obj N) =
      prod.map (f.adj.homEquiv (Sheaf.ringSheaf O)
            (Sheaf.ringSheaf (inverseImageRingSheaf f O))
            (𝟙 (Sheaf.ringSheaf (inverseImageRingSheaf f O))))
          (𝟙 (moduleSheaf O ((directImageModules f O).obj N))) ≫
        moduleSMulHom (pushforwardRingSheaf f (inverseImageRingSheaf f O))
          ((pushforwardModuleFunctor f (inverseImageRingSheaf f O)).obj N) := by
  rw [homEquiv_id_eq_ringUnit]
  exact moduleSMulHom_restrictScalars (ringUnit f O) _

/-- Compatibility with scalars in the first argument transports across the adjunction
`f⁻¹ ⊣ f_*`, the scalars on the direct-image side acting through the unit `O ⟶ f_*f⁻¹O`. -/
lemma inverseImage_smulLeftSquare_iff
    (q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    smulLeftSquare (inverseImageRingSheaf f O) q ↔
      smulLeftSquare O (inverseImagePairingEquiv f O F G N q) := by
  rw [smulLeftSquare, smulLeftSquare, inverseImagePairingEquiv_apply]
  exact square_transport_iff_of_comp f.adj
    (prodComparison₃ f.inverseImage (Sheaf.ringSheaf O) (moduleSheaf O F) (moduleSheaf O G))
    _ _ _ _ _ _ (prod.map (moduleSMulHom O F) (𝟙 (moduleSheaf O G)))
    (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd)
    (moduleSMulHom (inverseImageRingSheaf f O) N)
    (moduleSMulHom (pushforwardRingSheaf f (inverseImageRingSheaf f O))
      ((pushforwardModuleFunctor f (inverseImageRingSheaf f O)).obj N))
    (moduleSMulHom O ((directImageModules f O).obj N))
    (moduleSMul_map_aux' K f.pushforward (inverseImageRingSheaf f O) N).symm
    (moduleSMulHom_directImage f O N)
    (comp_assoc_eq q (prodComparison₃_comp_prodMap _ _
      (moduleSMul_map_aux' J f.inverseImage O F).symm))
    prodComparison₃_comp_fstFst
    (comp_assoc_eq q prodComparison₃_comp_liftFstSnd)

/-- Compatibility with scalars in the second argument transports across the adjunction
`f⁻¹ ⊣ f_*`, the scalars on the direct-image side acting through the unit `O ⟶ f_*f⁻¹O`. -/
lemma inverseImage_smulRightSquare_iff
    (q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    smulRightSquare (inverseImageRingSheaf f O) q ↔
      smulRightSquare O (inverseImagePairingEquiv f O F G N q) := by
  rw [smulRightSquare, smulRightSquare, inverseImagePairingEquiv_apply]
  exact square_transport_iff_of_comp f.adj
    (prodComparison₃' f.inverseImage (moduleSheaf O F) (Sheaf.ringSheaf O) (moduleSheaf O G))
    _ _ _ _ _ _ (prod.map (𝟙 (moduleSheaf O F)) (moduleSMulHom O G))
    (prod.snd ≫ prod.fst) (prod.lift prod.fst (prod.snd ≫ prod.snd))
    (moduleSMulHom (inverseImageRingSheaf f O) N)
    (moduleSMulHom (pushforwardRingSheaf f (inverseImageRingSheaf f O))
      ((pushforwardModuleFunctor f (inverseImageRingSheaf f O)).obj N))
    (moduleSMulHom O ((directImageModules f O).obj N))
    (moduleSMul_map_aux' K f.pushforward (inverseImageRingSheaf f O) N).symm
    (moduleSMulHom_directImage f O N)
    (comp_assoc_eq q (prodComparison₃'_comp_prodMap _ _
      (moduleSMul_map_aux' J f.inverseImage O G).symm))
    prodComparison₃'_comp_sndFst
    (comp_assoc_eq q prodComparison₃'_comp_liftFstSnd)

/-- **The bilinear pairings of the inverse images are the bilinear pairings into the direct
image.** This is the equality
`Bilin_{f⁻¹O}(f⁻¹F × f⁻¹G, N) = Bilin_O(F × G, f_*N)`, the step the proof of Stacks 03EL
calls the interesting one. -/
def inverseImageBilinearEquiv :
    { q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G) ⟶
          moduleSheaf (inverseImageRingSheaf f O) N //
      IsBilinearPairing (inverseImageRingSheaf f O) q } ≃
      { p : moduleSheaf O F ⨯ moduleSheaf O G ⟶
          moduleSheaf O ((directImageModules f O).obj N) // IsBilinearPairing O p } :=
  Equiv.subtypeEquiv (inverseImagePairingEquiv f O F G N) fun q ↦ by
    rw [isBilinearPairing_iff_squares, isBilinearPairing_iff_squares,
      inverseImage_addLeftSquare_iff, inverseImage_addRightSquare_iff,
      inverseImage_smulLeftSquare_iff, inverseImage_smulRightSquare_iff]
    exact Iff.rfl

end InverseImage

end Stacks.SheafOfModules

end
