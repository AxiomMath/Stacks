module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LongExactSequence

/-!
# Naturality of the Mayer--Vietoris sequence in the square

`StacksFrontier/Topology/Sheaves/Cohomology/MayerVietoris/LongExactSequence.lean` records that the
Mayer--Vietoris sequence of a Mayer--Vietoris square `S` of a site, with coefficients in an
abelian sheaf `F`, is exact and natural in `F`. This file records the other naturality: the
sequence is **contravariantly functorial in the square**.

A morphism of squares `φ : S ⟶ S'` has four components `τ₁, …, τ₄`, and cohomology over an
object is contravariant, so each term of the sequence of `S'` maps to the corresponding term of
the sequence of `S`. The two restriction maps `toBiprod` and `fromBiprod` are built from the
action of `CategoryTheory.Sheaf.cohomologyPresheaf`, so the squares containing them commute by
functoriality. The connecting map is precomposition with the extension class of the short exact
sequence of free abelian sheaves attached to the square, and `φ` induces a morphism of those
short exact sequences; the square containing the connecting map therefore commutes by
`CategoryTheory.ShortComplex.ShortExact.extClass_naturality` together with the associativity of
the Yoneda product.

This is what makes the Mayer--Vietoris sequences of a *system* of squares into a diagram of long
exact sequences.

## Main definitions

* `Stacks.Cohomology.MayerVietoris.freeSheaf`: the free abelian sheaf on an object, as a functor.
* `Stacks.Cohomology.MayerVietoris.shortComplexMap`: the morphism
  `S.shortComplex ⟶ S'.shortComplex` induced by a morphism of squares.
* `Stacks.Cohomology.MayerVietoris.sequenceMap`: **the induced morphism of Mayer--Vietoris
  sequences** `S'.sequence F n₀ n₁ h ⟶ S.sequence F n₀ n₁ h`.

## Main results

* `Stacks.Cohomology.MayerVietoris.delta_naturality_square`: the connecting morphisms commute
  with the restriction maps along a morphism of squares.
* `Stacks.Cohomology.MayerVietoris.sequenceMap_app_zero` and its companions: the components of
  the induced morphism, which is what the five lemma consumes.

## Implementation notes

The objects of `CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex` and of the
sequence are biproducts only up to definitional unfolding: the type appearing in a goal is
`S.shortComplex.X₂`, not a syntactic `_ ⊞ _`, so `simp` lemmas about `biprod` do not fire on it.
The two naturality squares for the biproduct terms are therefore proved once and for all as
`biprod_lift_map_comm` and `biprod_map_desc_comm`, where the types *are* syntactic biproducts,
and are then applied by `exact`, which closes the definitional gap.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w v u

namespace Stacks.Cohomology.MayerVietoris

/-! ### Two naturality squares for biproducts -/

section Biprod

variable {D : Type*} [Category* D] [Preadditive D] {A B A' B' X X' : D}
  [HasBinaryBiproduct A B] [HasBinaryBiproduct A' B']

/-- A square of morphisms into a biproduct commutes as soon as its two components do. -/
theorem biprod_lift_map_comm (t : X ⟶ X') (a : X ⟶ A) (b : X ⟶ B) (a' : X' ⟶ A')
    (b' : X' ⟶ B') (u : A ⟶ A') (v : B ⟶ B') (ha : t ≫ a' = a ≫ u) (hb : t ≫ b' = b ≫ v) :
    t ≫ biprod.lift a' b' = biprod.lift a b ≫ biprod.map u v := by
  refine biprod.hom_ext _ _ ?_ ?_
  · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc, ha]
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc, hb]

/-- A square of morphisms out of a biproduct commutes as soon as its two components do. -/
theorem biprod_map_desc_comm (t : X ⟶ X') (a : A ⟶ X) (b : B ⟶ X) (a' : A' ⟶ X')
    (b' : B' ⟶ X') (u : A ⟶ A') (v : B ⟶ B') (ha : u ≫ a' = a ≫ t) (hb : v ≫ b' = b ≫ t) :
    biprod.map u v ≫ biprod.desc a' b' = biprod.desc a b ≫ t := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc, ha]
  · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, hb]

end Biprod

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- The free abelian sheaf on an object of a site, as a functor. The terms of the short exact
sequence attached to a Mayer--Vietoris square are its values, and the cohomology of an abelian
sheaf over an object is the `Ext`-group out of it. -/
abbrev freeSheaf (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}] :
    C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf J _

omit [HasWeakSheafify J (Type v)] in
/-- Restriction of a cohomology class along a morphism of objects is precomposition with the
induced morphism of free abelian sheaves. -/
theorem cohomologyPresheaf_map_apply (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {X Y : C}
    (f : X ⟶ Y) (y : Sheaf.H'.{w} F n Y) :
    (F.cohomologyPresheaf.{w} n).map f.op y =
      (Ext.mk₀ ((freeSheaf J).map f)).comp y (zero_add n) := rfl

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The left-hand term of the short exact sequence of a Mayer--Vietoris square is the free
abelian sheaf on the top-left object. -/
theorem shortComplex_X₁_eq (S : J.MayerVietorisSquare) :
    S.shortComplex.X₁ = (freeSheaf J).obj S.X₁ := rfl

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The right-hand term of the short exact sequence of a Mayer--Vietoris square is the free
abelian sheaf on the bottom-right object. -/
theorem shortComplex_X₃_eq (S : J.MayerVietorisSquare) :
    S.shortComplex.X₃ = (freeSheaf J).obj S.X₄ := rfl

/-- **The morphism of short exact sequences induced by a morphism of squares.** A morphism of
squares induces a morphism of the free abelian sheaves on each of the four objects, and the
outer maps of the short exact sequence — the difference and the sum of the two restrictions —
are compatible with them. -/
def shortComplexMap {S S' : J.MayerVietorisSquare} (φ : S.toSquare ⟶ S'.toSquare) :
    S.shortComplex ⟶ S'.shortComplex where
  τ₁ := (freeSheaf J).map φ.τ₁
  τ₂ := biprod.map ((freeSheaf J).map φ.τ₂) ((freeSheaf J).map φ.τ₃)
  τ₃ := (freeSheaf J).map φ.τ₄
  comm₁₂ :=
    biprod_lift_map_comm ((freeSheaf J).map φ.τ₁) ((freeSheaf J).map S.f₁₂)
      (-(freeSheaf J).map S.f₁₃) ((freeSheaf J).map S'.f₁₂) (-(freeSheaf J).map S'.f₁₃)
      ((freeSheaf J).map φ.τ₂) ((freeSheaf J).map φ.τ₃)
      (by rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂])
      (by rw [Preadditive.comp_neg, Preadditive.neg_comp, ← Functor.map_comp,
        ← Functor.map_comp, φ.comm₁₃])
  comm₂₃ :=
    biprod_map_desc_comm ((freeSheaf J).map φ.τ₄) ((freeSheaf J).map S.f₂₄)
      ((freeSheaf J).map S.f₃₄) ((freeSheaf J).map S'.f₂₄) ((freeSheaf J).map S'.f₃₄)
      ((freeSheaf J).map φ.τ₂) ((freeSheaf J).map φ.τ₃)
      (by rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₄])
      (by rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₃₄])

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The left-hand component of `shortComplexMap φ` is the morphism of free abelian sheaves
induced by the top-left component of `φ`. -/
@[simp] theorem shortComplexMap_τ₁ {S S' : J.MayerVietorisSquare}
    (φ : S.toSquare ⟶ S'.toSquare) :
    (shortComplexMap φ).τ₁ = (freeSheaf J).map φ.τ₁ := rfl

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] in
/-- The right-hand component of `shortComplexMap φ` is the morphism of free abelian sheaves
induced by the bottom-right component of `φ`. -/
@[simp] theorem shortComplexMap_τ₃ {S S' : J.MayerVietorisSquare}
    (φ : S.toSquare ⟶ S'.toSquare) :
    (shortComplexMap φ).τ₃ = (freeSheaf J).map φ.τ₄ := rfl

section Sequence

variable (F : Sheaf J AddCommGrpCat.{v}) {S S' : J.MayerVietorisSquare}
  (φ : S.toSquare ⟶ S'.toSquare) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- **The connecting morphisms of the Mayer--Vietoris sequence are natural in the square.** The
connecting morphism is precomposition with the extension class of the short exact sequence of
free abelian sheaves, so the assertion is the naturality of that class in the short exact
sequence, read through the associativity of the Yoneda product. -/
theorem delta_naturality_square :
    S'.δ F n₀ n₁ h ≫ (F.cohomologyPresheaf.{w} n₁).map φ.τ₄.op =
      (F.cohomologyPresheaf.{w} n₀).map φ.τ₁.op ≫ S.δ F n₀ n₁ h := by
  have hh : 1 + n₀ = n₁ := by omega
  have key : (S.shortComplex_shortExact.extClass.comp
        (Ext.mk₀ ((freeSheaf J).map φ.τ₁)) (add_zero 1) :
      Ext.{w} ((freeSheaf J).obj S.X₄) ((freeSheaf J).obj S'.X₁) 1) =
      (Ext.mk₀ ((freeSheaf J).map φ.τ₄)).comp
        S'.shortComplex_shortExact.extClass (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality S.shortComplex_shortExact
      S'.shortComplex_shortExact (shortComplexMap φ)
  ext x
  change (Ext.mk₀ ((freeSheaf J).map φ.τ₄)).comp
      (S'.shortComplex_shortExact.extClass.comp x hh) (zero_add n₁) =
    S.shortComplex_shortExact.extClass.comp
      ((Ext.mk₀ ((freeSheaf J).map φ.τ₁)).comp x (zero_add n₀)) hh
  have step₁ : (Ext.mk₀ ((freeSheaf J).map φ.τ₄)).comp
        (S'.shortComplex_shortExact.extClass.comp x hh) (zero_add n₁) =
      Ext.comp (((Ext.mk₀ ((freeSheaf J).map φ.τ₄)).comp
            S'.shortComplex_shortExact.extClass (zero_add 1) :
          Ext.{w} ((freeSheaf J).obj S.X₄) ((freeSheaf J).obj S'.X₁) 1)) x hh :=
    (Ext.comp_assoc (Ext.mk₀ ((freeSheaf J).map φ.τ₄))
      S'.shortComplex_shortExact.extClass x (zero_add 1) hh
      (show 0 + 1 + n₀ = n₁ by omega)).symm
  have step₃ : Ext.comp ((S.shortComplex_shortExact.extClass.comp
          (Ext.mk₀ ((freeSheaf J).map φ.τ₁)) (add_zero 1) :
        Ext.{w} ((freeSheaf J).obj S.X₄) ((freeSheaf J).obj S'.X₁) 1)) x hh =
      S.shortComplex_shortExact.extClass.comp
        ((Ext.mk₀ ((freeSheaf J).map φ.τ₁)).comp x (zero_add n₀)) hh :=
    Ext.comp_assoc S.shortComplex_shortExact.extClass
      (Ext.mk₀ ((freeSheaf J).map φ.τ₁)) x (add_zero 1) (zero_add n₀)
      (show 1 + 0 + n₀ = n₁ by omega)
  exact step₁.trans ((congrArg (fun z => Ext.comp z x hh) key.symm).trans step₃)

/-- The sum of the two restrictions is natural in the square. -/
theorem toBiprod_naturality_square :
    S'.toBiprod F n₀ ≫
        biprod.map ((F.cohomologyPresheaf.{w} n₀).map φ.τ₂.op)
          ((F.cohomologyPresheaf.{w} n₀).map φ.τ₃.op) =
      (F.cohomologyPresheaf.{w} n₀).map φ.τ₄.op ≫ S.toBiprod F n₀ :=
  (biprod_lift_map_comm ((F.cohomologyPresheaf.{w} n₀).map φ.τ₄.op)
    ((F.cohomologyPresheaf.{w} n₀).map S'.f₂₄.op) ((F.cohomologyPresheaf.{w} n₀).map S'.f₃₄.op)
    ((F.cohomologyPresheaf.{w} n₀).map S.f₂₄.op) ((F.cohomologyPresheaf.{w} n₀).map S.f₃₄.op)
    ((F.cohomologyPresheaf.{w} n₀).map φ.τ₂.op) ((F.cohomologyPresheaf.{w} n₀).map φ.τ₃.op)
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, φ.comm₂₄])
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, φ.comm₃₄])).symm

/-- The difference of the two restrictions is natural in the square. -/
theorem fromBiprod_naturality_square :
    S'.fromBiprod F n₀ ≫ (F.cohomologyPresheaf.{w} n₀).map φ.τ₁.op =
      biprod.map ((F.cohomologyPresheaf.{w} n₀).map φ.τ₂.op)
          ((F.cohomologyPresheaf.{w} n₀).map φ.τ₃.op) ≫
        S.fromBiprod F n₀ :=
  (biprod_map_desc_comm ((F.cohomologyPresheaf.{w} n₀).map φ.τ₁.op)
    ((F.cohomologyPresheaf.{w} n₀).map S'.f₁₂.op) (-(F.cohomologyPresheaf.{w} n₀).map S'.f₁₃.op)
    ((F.cohomologyPresheaf.{w} n₀).map S.f₁₂.op) (-(F.cohomologyPresheaf.{w} n₀).map S.f₁₃.op)
    ((F.cohomologyPresheaf.{w} n₀).map φ.τ₂.op) ((F.cohomologyPresheaf.{w} n₀).map φ.τ₃.op)
    (by rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, φ.comm₁₂])
    (by rw [Preadditive.comp_neg, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, φ.comm₁₃])).symm

/-- **The morphism of Mayer--Vietoris sequences induced by a morphism of squares.** Cohomology
over an object is contravariant, so a morphism `φ : S ⟶ S'` of squares carries the sequence of
`S'` to the sequence of `S`. -/
def sequenceMap : S'.sequence F n₀ n₁ h ⟶ S.sequence F n₀ n₁ h :=
  ComposableArrows.homMk₅ ((F.cohomologyPresheaf.{w} n₀).map φ.τ₄.op)
    (biprod.map ((F.cohomologyPresheaf.{w} n₀).map φ.τ₂.op)
      ((F.cohomologyPresheaf.{w} n₀).map φ.τ₃.op))
    ((F.cohomologyPresheaf.{w} n₀).map φ.τ₁.op)
    ((F.cohomologyPresheaf.{w} n₁).map φ.τ₄.op)
    (biprod.map ((F.cohomologyPresheaf.{w} n₁).map φ.τ₂.op)
      ((F.cohomologyPresheaf.{w} n₁).map φ.τ₃.op))
    ((F.cohomologyPresheaf.{w} n₁).map φ.τ₁.op)
    (toBiprod_naturality_square F φ n₀) (fromBiprod_naturality_square F φ n₀)
    (delta_naturality_square F φ n₀ n₁ h) (toBiprod_naturality_square F φ n₁)
    (fromBiprod_naturality_square F φ n₁)

/-- At position `0`, `sequenceMap` is restriction of `n₀`-th cohomology along the bottom-right
component of `φ`. -/
@[simp] theorem sequenceMap_app_zero :
    (sequenceMap F φ n₀ n₁ h).app 0 = (F.cohomologyPresheaf.{w} n₀).map φ.τ₄.op := rfl

/-- At position `2`, `sequenceMap` is restriction of `n₀`-th cohomology along the top-left
component of `φ`. -/
@[simp] theorem sequenceMap_app_two :
    (sequenceMap F φ n₀ n₁ h).app ⟨2, by valid⟩ =
      (F.cohomologyPresheaf.{w} n₀).map φ.τ₁.op := rfl

/-- At position `3`, `sequenceMap` is restriction of `n₁`-th cohomology along the bottom-right
component of `φ`. -/
@[simp] theorem sequenceMap_app_three :
    (sequenceMap F φ n₀ n₁ h).app ⟨3, by valid⟩ =
      (F.cohomologyPresheaf.{w} n₁).map φ.τ₄.op := rfl

/-- At position `5`, `sequenceMap` is restriction of `n₁`-th cohomology along the top-left
component of `φ`. -/
@[simp] theorem sequenceMap_app_five :
    (sequenceMap F φ n₀ n₁ h).app ⟨5, by valid⟩ =
      (F.cohomologyPresheaf.{w} n₁).map φ.τ₁.op := rfl

end Sequence

end Stacks.Cohomology.MayerVietoris

end
