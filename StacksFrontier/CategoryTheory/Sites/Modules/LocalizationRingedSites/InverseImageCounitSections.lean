module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image along a localization, and the counit of its adjunction, on local sections

This file describes on local sections the composite

`(f⁻¹F ⨯ f⁻¹G ⟶ f⁻¹(F ⨯ G)) ≫ f⁻¹(b) ≫ (ε : f⁻¹f_*N ⟶ N)`

of the inverse product comparison of `f⁻¹`, the inverse image of a bilinear pairing `b` of
Tag 03EL, and the counit of `f⁻¹ ⊣ f_*`. Once the pairing is exhibited as the transpose
`η ≫ f_*(g)` of a morphism `g` out of the inverse image, the composite is `g` on the pair of
sections read through the composite functor; for a localization, `f⁻¹` is restriction along
`Over.forget U`, and the composite reads a pair of sections over `V ⟶ U` as a pair of sections
over `V` and applies `g`.

## Main results

* `Stacks.Sheaves.ToposPullback.map_preservesLimitPair_iso_inv_prodObjMk`: the inverse product
  comparison of a finite-product-preserving functor, on a pair of sections.
* `Stacks.Sheaves.ToposPullback.map_comp_counit_of_eq`: the inverse image of a transpose followed
  by the counit is the morphism it transposes.
* `Stacks.Sheaves.ToposPullback.map_prodComparisonInv_map_comp_counit_prodObjMk`: the
  sections-level description of `(f⁻¹F ⨯ f⁻¹G ⟶ f⁻¹(F ⨯ G)) ≫ f⁻¹(b) ≫ ε`.
* `Stacks.Sheaves.ToposPullback.sheafPushforwardContinuous_comp_sectionsFunctor`: for a continuous
  functor of sites, restriction followed by sections over `W` is sections over `G W`.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

/-! ## The inverse product comparison and the counit, on a pair of sections -/

section Abstract

universe t

variable {A B : Type*} [Category* A] [Category* B] [HasFiniteProducts A] [HasFiniteProducts B]

/-- **The inverse product comparison of a finite-product-preserving functor, on a pair of
sections.** A pair of sections of `L P₁` and `L P₂` over a finite-product-preserving functor `S`
is carried by the inverse of the product comparison of `L` to the pair of the same two sections
taken over the composite functor `L ⋙ S`. -/
theorem map_preservesLimitPair_iso_inv_prodObjMk (L : A ⥤ B) [PreservesFiniteProducts L]
    (S : B ⥤ Type t) [PreservesFiniteProducts S] [PreservesFiniteProducts (L ⋙ S)]
    (P₁ P₂ : A) (a : S.obj (L.obj P₁)) (b : S.obj (L.obj P₂)) :
    S.map (PreservesLimitPair.iso L P₁ P₂).inv (Functor.prodObjMk a b) =
      Functor.prodObjMk (P := L ⋙ S) a b :=
  Functor.prodObjMk_ext (P := L ⋙ S)
    (((S.map_comp_apply (PreservesLimitPair.iso L P₁ P₂).inv (L.map prod.fst)
              (Functor.prodObjMk a b)).symm.trans
          ((congrArg (fun m ↦ S.map m (Functor.prodObjMk a b))
                (PreservesLimitPair.iso_inv_fst L P₁ P₂)).trans
            (Functor.map_fst_prodObjMk (P := S) a b))).trans
      (Functor.map_fst_prodObjMk (P := L ⋙ S) a b).symm)
    (((S.map_comp_apply (PreservesLimitPair.iso L P₁ P₂).inv (L.map prod.snd)
              (Functor.prodObjMk a b)).symm.trans
          ((congrArg (fun m ↦ S.map m (Functor.prodObjMk a b))
                (PreservesLimitPair.iso_inv_snd L P₁ P₂)).trans
            (Functor.map_snd_prodObjMk (P := S) a b))).trans
      (Functor.map_snd_prodObjMk (P := L ⋙ S) a b).symm)

variable {L : A ⥤ B} {R : B ⥤ A}

omit [HasFiniteProducts A] [HasFiniteProducts B] in
/-- **The inverse image of a transpose, followed by the counit, is the morphism it transposes.**
If a morphism `q : P ⟶ R N` is the transpose `η ≫ R g` of `g : L P ⟶ N` then
`L q ≫ ε_N = g`. -/
@[ega "0 3.5.4" "more general"]
theorem map_comp_counit_of_eq (adj : L ⊣ R) {P : A} {N : B} (q : P ⟶ R.obj N) (g : L.obj P ⟶ N)
    (hq : q = adj.unit.app P ≫ R.map g) : L.map q ≫ adj.counit.app N = g :=
  (congrArg (adj.homEquiv P N).symm (hq : q = adj.homEquiv P N g)).trans
    ((adj.homEquiv P N).symm_apply_apply g)

/-- **The sections-level description of the inverse product comparison, the inverse image of a
pairing and the counit.** Once the pairing `q` is exhibited as the transpose of `g`, the
composite carries a pair `(a, b)` of local sections to `g` applied to that pair read over
`L ⋙ S`. -/
theorem map_prodComparisonInv_map_comp_counit_prodObjMk (adj : L ⊣ R)
    [PreservesFiniteProducts L] (S : B ⥤ Type t) [PreservesFiniteProducts S]
    [PreservesFiniteProducts (L ⋙ S)] (P₁ P₂ : A) (N : B) (q : P₁ ⨯ P₂ ⟶ R.obj N)
    (g : L.obj (P₁ ⨯ P₂) ⟶ N) (hq : q = adj.unit.app (P₁ ⨯ P₂) ≫ R.map g)
    (a : S.obj (L.obj P₁)) (b : S.obj (L.obj P₂)) :
    S.map ((PreservesLimitPair.iso L P₁ P₂).inv ≫ L.map q ≫ adj.counit.app N)
        (Functor.prodObjMk a b) =
      S.map g (Functor.prodObjMk (P := L ⋙ S) a b) :=
  (S.map_comp_apply (PreservesLimitPair.iso L P₁ P₂).inv (L.map q ≫ adj.counit.app N)
        (Functor.prodObjMk a b)).trans
    ((congrArg
          (fun m ↦ S.map m
            (S.map (PreservesLimitPair.iso L P₁ P₂).inv (Functor.prodObjMk a b)))
          (map_comp_counit_of_eq adj q g hq)).trans
      (congrArg (S.map g) (map_preservesLimitPair_iso_inv_prodObjMk L S P₁ P₂ a b)))

end Abstract

/-! ## The inverse image along a localization is restriction, on sections -/

section Sites

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K]

/-- **The inverse image along a localization, on sections.** For a continuous functor of sites
`G`, restriction of sheaves of types along `G` followed by sections over an object `W` of the
source site is sections over `G W` — on the nose, both being evaluation of the underlying
presheaf at `G W`. -/
theorem sheafPushforwardContinuous_comp_sectionsFunctor (W : Cᵒᵖ) :
    G.sheafPushforwardContinuous (Type w) J K ⋙ Sheaf.sectionsFunctor.{w} J W =
      Sheaf.sectionsFunctor.{w} K (G.op.obj W) :=
  rfl

end Sites

end Stacks.Sheaves.ToposPullback

end
