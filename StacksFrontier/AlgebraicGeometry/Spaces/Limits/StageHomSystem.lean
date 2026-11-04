module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesColimitFiveLemma

/-!
# Systems of homomorphism groups along the stages of a limit

In the proof of Stacks 09RI the groups `Hom(Lf_{ki}^*E, Lf_{ki}^*K)`, `k ≥ i`, of the stages of a
limit, with the transition maps given by pulling back to later stages and the maps to
`Hom(Lfᵢ^*E, Lfᵢ^*K)` at the limit, are compared with the group at the limit. This file isolates
the formal part of that comparison: a family of functors `F k : 𝒞₀ ⥤ 𝒞 k` out of the stage `i`,
a functor `F' : 𝒞₀ ⥤ 𝒟` to the limit, and transition and limit maps on the groups of morphisms
`F k X ⟶ F k K`, additive, transitive, compatible with each other and with precomposition by the
images of morphisms of `𝒞₀`.

The property that `Hom(F' X, F' K)` is the filtered colimit of the `Hom(F k X, F k K)` is then
invariant under isomorphism in `X`, stable under binary biproducts in `X`, and, for exact
functors, passes to the third vertex of a distinguished triangle from the other two and their
shifts (the five lemma on directed colimits, `Stacks.IsStagesColimit.of_distTriang`, applied to
the images of one triangle of `𝒞₀`).

## Main definitions

* `Stacks.StageHomSystem`: the data and the laws.
* `Stacks.StageHomSystem.IsColimitAt`: `Hom(F' X, F' K)` is the filtered colimit of the stages.

## Main results

* `Stacks.IsStagesColimit.prod`: products of filtered colimit systems.
* `Stacks.StageHomSystem.IsColimitAt.of_iso`, `Stacks.StageHomSystem.IsColimitAt.biprod`,
  `Stacks.StageHomSystem.IsColimitAt.of_distTriang`.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
-/

@[expose] public noncomputable section

universe v w₁ w₂ w₃ w₄ u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks

/-- **Filtered colimits of two systems of stages give the filtered colimit of their product**,
for a directed index and transitive transition maps. -/
theorem IsStagesColimit.prod {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    {G₁ : I → Type w₁} {T₁ : Type w₂} {G₂ : I → Type w₃} {T₂ : Type w₄}
    {tr₁ : ∀ i j : I, i ≤ j → G₁ i → G₁ j} {ι₁ : ∀ i : I, G₁ i → T₁}
    {tr₂ : ∀ i j : I, i ≤ j → G₂ i → G₂ j} {ι₂ : ∀ i : I, G₂ i → T₂}
    (htr₁ : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (s : G₁ i),
      tr₁ j k hjk (tr₁ i j hij s) = tr₁ i k (hij.trans hjk) s)
    (htr₂ : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (s : G₂ i),
      tr₂ j k hjk (tr₂ i j hij s) = tr₂ i k (hij.trans hjk) s)
    (h₁ : IsStagesColimit tr₁ ι₁) (h₂ : IsStagesColimit tr₂ ι₂) :
    IsStagesColimit (G := fun i => G₁ i × G₂ i)
      (fun i j h s => (tr₁ i j h s.1, tr₂ i j h s.2)) (fun i s => (ι₁ i s.1, ι₂ i s.2)) where
  ι_trans i j h s := Prod.ext (h₁.ι_trans i j h s.1) (h₂.ι_trans i j h s.2)
  exists_stage t := by
    obtain ⟨i₁, s₁, hs₁⟩ := h₁.exists_stage t.1
    obtain ⟨i₂, s₂, hs₂⟩ := h₂.exists_stage t.2
    obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) i₁ i₂
    exact ⟨k, (tr₁ i₁ k hk₁ s₁, tr₂ i₂ k hk₂ s₂),
      Prod.ext ((h₁.ι_trans _ _ _ _).trans hs₁) ((h₂.ι_trans _ _ _ _).trans hs₂)⟩
  exists_trans_eq i s s' hss := by
    obtain ⟨j₁, hj₁, e₁⟩ := h₁.exists_trans_eq i s.1 s'.1 (congrArg Prod.fst hss)
    obtain ⟨j₂, hj₂, e₂⟩ := h₂.exists_trans_eq i s.2 s'.2 (congrArg Prod.snd hss)
    obtain ⟨k, hk₁, hk₂⟩ := directed_of (· ≤ ·) j₁ j₂
    refine ⟨k, hj₁.trans hk₁, Prod.ext ?_ ?_⟩
    · change tr₁ i k _ s.1 = tr₁ i k _ s'.1
      rw [← htr₁ i j₁ k hj₁ hk₁, ← htr₁ i j₁ k hj₁ hk₁, e₁]
    · change tr₂ i k _ s.2 = tr₂ i k _ s'.2
      rw [← htr₂ i j₂ k hj₂ hk₂, ← htr₂ i j₂ k hj₂ hk₂, e₂]

/-- **A system of homomorphism groups along the stages of a limit.** Functors `F k : 𝒞₀ ⥤ 𝒞 k`
from a fixed stage to the later stages and `F' : 𝒞₀ ⥤ 𝒟` to the limit, with, for all objects
`X`, `K` of `𝒞₀`, transition maps `Hom(F k X, F k K) ⟶ Hom(F m X, F m K)` for `k ≤ m` and maps
`Hom(F k X, F k K) ⟶ Hom(F' X, F' K)` to the limit. They are additive, transitive, compatible
with each other, and commute with precomposition by the images of morphisms of `𝒞₀`. -/
structure StageHomSystem (J : Type v) [Preorder J] (𝒞₀ : Type u') [Category.{v'} 𝒞₀]
    (𝒞 : J → Type u') [∀ k, Category.{v'} (𝒞 k)] [∀ k, Preadditive (𝒞 k)]
    (𝒟 : Type u') [Category.{v'} 𝒟] [Preadditive 𝒟] where
  /-- The functors to the later stages. -/
  F : ∀ k, 𝒞₀ ⥤ 𝒞 k
  /-- The functor to the limit. -/
  F' : 𝒞₀ ⥤ 𝒟
  /-- The transition maps. -/
  raise : ∀ (X K : 𝒞₀) (k m : J), k ≤ m → ((F k).obj X ⟶ (F k).obj K) →
    ((F m).obj X ⟶ (F m).obj K)
  /-- The maps to the limit. -/
  lim : ∀ (X K : 𝒞₀) (k : J), ((F k).obj X ⟶ (F k).obj K) → (F'.obj X ⟶ F'.obj K)
  raise_add : ∀ (X K : 𝒞₀) (k m : J) (h : k ≤ m) (a b : (F k).obj X ⟶ (F k).obj K),
    raise X K k m h (a + b) = raise X K k m h a + raise X K k m h b
  raise_map_comp : ∀ (X' X K : 𝒞₀) (k m : J) (h : k ≤ m) (φ : X' ⟶ X)
    (a : (F k).obj X ⟶ (F k).obj K),
    raise X' K k m h ((F k).map φ ≫ a) = (F m).map φ ≫ raise X K k m h a
  raise_raise : ∀ (X K : 𝒞₀) (k m n : J) (hkm : k ≤ m) (hmn : m ≤ n)
    (a : (F k).obj X ⟶ (F k).obj K),
    raise X K m n hmn (raise X K k m hkm a) = raise X K k n (hkm.trans hmn) a
  lim_add : ∀ (X K : 𝒞₀) (k : J) (a b : (F k).obj X ⟶ (F k).obj K),
    lim X K k (a + b) = lim X K k a + lim X K k b
  lim_map_comp : ∀ (X' X K : 𝒞₀) (k : J) (φ : X' ⟶ X) (a : (F k).obj X ⟶ (F k).obj K),
    lim X' K k ((F k).map φ ≫ a) = F'.map φ ≫ lim X K k a
  lim_raise : ∀ (X K : 𝒞₀) (k m : J) (h : k ≤ m) (a : (F k).obj X ⟶ (F k).obj K),
    lim X K m (raise X K k m h a) = lim X K k a

namespace StageHomSystem

variable {J : Type v} [Preorder J] {𝒞₀ : Type u'} [Category.{v'} 𝒞₀]
  {𝒞 : J → Type u'} [∀ k, Category.{v'} (𝒞 k)] [∀ k, Preadditive (𝒞 k)]
  {𝒟 : Type u'} [Category.{v'} 𝒟] [Preadditive 𝒟] (Ξ : StageHomSystem J 𝒞₀ 𝒞 𝒟)

/-- **`Hom(F' X, F' K)` is the filtered colimit of the groups `Hom(F k X, F k K)`.** -/
def IsColimitAt (X K : 𝒞₀) : Prop :=
  IsStagesColimit (fun k m h => Ξ.raise X K k m h) (fun k => Ξ.lim X K k)

/-- The transition maps as additive maps. -/
def raiseHom (X K : 𝒞₀) (k m : J) (h : k ≤ m) :
    ((Ξ.F k).obj X ⟶ (Ξ.F k).obj K) →+ ((Ξ.F m).obj X ⟶ (Ξ.F m).obj K) :=
  AddMonoidHom.mk' (Ξ.raise X K k m h) (Ξ.raise_add X K k m h)

/-- The maps to the limit as additive maps. -/
def limHom (X K : 𝒞₀) (k : J) :
    ((Ξ.F k).obj X ⟶ (Ξ.F k).obj K) →+ (Ξ.F'.obj X ⟶ Ξ.F'.obj K) :=
  AddMonoidHom.mk' (Ξ.lim X K k) (Ξ.lim_add X K k)

/-- `raiseHom` applied to a morphism is the transition map `raise` applied to it. -/
theorem raiseHom_apply (X K : 𝒞₀) (k m : J) (h : k ≤ m) (a : (Ξ.F k).obj X ⟶ (Ξ.F k).obj K) :
    Ξ.raiseHom X K k m h a = Ξ.raise X K k m h a := rfl

/-- `limHom` applied to a morphism is the map `lim` to the limit applied to it. -/
theorem limHom_apply (X K : 𝒞₀) (k : J) (a : (Ξ.F k).obj X ⟶ (Ξ.F k).obj K) :
    Ξ.limHom X K k a = Ξ.lim X K k a := rfl

/-- **The colimit property only depends on the isomorphism class of the source.** -/
theorem IsColimitAt.of_iso {X X' K : 𝒞₀} (e : X ≅ X') (h : Ξ.IsColimitAt X K) :
    Ξ.IsColimitAt X' K :=
  IsStagesColimit.ofEquiv (G := fun k => (Ξ.F k).obj X ⟶ (Ξ.F k).obj K)
    (G' := fun k => (Ξ.F k).obj X' ⟶ (Ξ.F k).obj K) _ _
    (fun k => { toFun := fun a => (Ξ.F k).map e.hom ≫ a
                invFun := fun b => (Ξ.F k).map e.inv ≫ b
                left_inv := fun a => by simp [← Functor.map_comp_assoc]
                right_inv := fun b => by simp [← Functor.map_comp_assoc] })
    { toFun := fun a => Ξ.F'.map e.hom ≫ a
      invFun := fun b => Ξ.F'.map e.inv ≫ b
      left_inv := fun a => by simp [← Functor.map_comp_assoc]
      right_inv := fun b => by simp [← Functor.map_comp_assoc] }
    (fun k m hkm a => (Ξ.raise_map_comp X X' K k m hkm e.hom a).symm)
    (fun k a => (Ξ.lim_map_comp X X' K k e.hom a).symm) h

/-- Morphisms out of the image of a binary biproduct under an additive functor are pairs of
morphisms. -/
def homBiprodEquiv {C : Type*} {D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] (G : C ⥤ D) [G.Additive] (X Y : C) (Z : D) :
    (G.obj (X ⊞ Y) ⟶ Z) ≃ (G.obj X ⟶ Z) × (G.obj Y ⟶ Z) where
  toFun a := (G.map biprod.inl ≫ a, G.map biprod.inr ≫ a)
  invFun b := G.map biprod.fst ≫ b.1 + G.map biprod.snd ≫ b.2
  left_inv a := by
    simp only [← Category.assoc, ← Functor.map_comp, ← Preadditive.add_comp, ← G.map_add,
      biprod.total, CategoryTheory.Functor.map_id, Category.id_comp]
  right_inv b := by
    simp only [Preadditive.comp_add, ← Category.assoc, ← Functor.map_comp, biprod.inl_fst,
      biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, CategoryTheory.Functor.map_id,
      Functor.map_zero, Category.id_comp, zero_comp, add_zero, zero_add, Prod.mk.eta]

/-- **The colimit property is stable under binary biproducts of the source**, for additive
functors. -/
theorem IsColimitAt.biprod [IsDirected J (· ≤ ·)] [Preadditive 𝒞₀] [HasBinaryBiproducts 𝒞₀]
    [∀ k, (Ξ.F k).Additive] [Ξ.F'.Additive] {X Y K : 𝒞₀} (hX : Ξ.IsColimitAt X K)
    (hY : Ξ.IsColimitAt Y K) : Ξ.IsColimitAt (X ⊞ Y) K := by
  refine IsStagesColimit.ofEquiv _ _ (fun k => homBiprodEquiv (Ξ.F k) X Y ((Ξ.F k).obj K))
    (homBiprodEquiv Ξ.F' X Y (Ξ.F'.obj K)) ?_ ?_
    (IsStagesColimit.prod (Ξ.raise_raise X K) (Ξ.raise_raise Y K) hX hY)
  · intro k m hkm a
    exact Prod.ext (Ξ.raise_map_comp _ _ K k m hkm _ a).symm
      (Ξ.raise_map_comp _ _ K k m hkm _ a).symm
  · intro k a
    exact Prod.ext (Ξ.lim_map_comp _ _ K k _ a).symm (Ξ.lim_map_comp _ _ K k _ a).symm

section Triangulated

variable [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [HasShift 𝒞₀ ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive] [Pretriangulated 𝒞₀]
  [∀ k, HasZeroObject (𝒞 k)] [∀ k, HasShift (𝒞 k) ℤ]
  [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive] [∀ k, Pretriangulated (𝒞 k)]
  [HasZeroObject 𝒟] [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  [∀ k, (Ξ.F k).CommShift ℤ] [Ξ.F'.CommShift ℤ]

/-- The transition maps on morphisms out of `(F k X)⟦1⟧`, read through
`F k (X⟦1⟧) ≅ (F k X)⟦1⟧`. -/
def raiseShift (X K : 𝒞₀) (k m : J) (h : k ≤ m) :
    (((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) →+ (((Ξ.F m).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F m).obj K) :=
  AddMonoidHom.mk' (fun a => ((Ξ.F m).commShiftIso (1 : ℤ)).inv.app X ≫
      Ξ.raise (X⟦(1 : ℤ)⟧) K k m h (((Ξ.F k).commShiftIso (1 : ℤ)).hom.app X ≫ a))
    (fun a b => by simp only [Preadditive.comp_add, Ξ.raise_add])

/-- The maps to the limit on morphisms out of `(F k X)⟦1⟧`. -/
def limShift (X K : 𝒞₀) (k : J) :
    (((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) →+ ((Ξ.F'.obj X)⟦(1 : ℤ)⟧ ⟶ Ξ.F'.obj K) :=
  AddMonoidHom.mk' (fun a => (Ξ.F'.commShiftIso (1 : ℤ)).inv.app X ≫
      Ξ.lim (X⟦(1 : ℤ)⟧) K k (((Ξ.F k).commShiftIso (1 : ℤ)).hom.app X ≫ a))
    (fun a b => by simp only [Preadditive.comp_add, Ξ.lim_add])

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] [HasShift 𝒟 ℤ] [Ξ.F'.CommShift ℤ] in
/-- `raiseShift X K k m h a` is the transition map `raise` applied to `a` precomposed with
`F k (X⟦1⟧) ≅ (F k X)⟦1⟧`, then precomposed with the inverse of `F m (X⟦1⟧) ≅ (F m X)⟦1⟧`. -/
theorem raiseShift_apply (X K : 𝒞₀) (k m : J) (h : k ≤ m)
    (a : ((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) :
    Ξ.raiseShift X K k m h a = ((Ξ.F m).commShiftIso (1 : ℤ)).inv.app X ≫
      Ξ.raise (X⟦(1 : ℤ)⟧) K k m h (((Ξ.F k).commShiftIso (1 : ℤ)).hom.app X ≫ a) := rfl

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] in
/-- `limShift X K k a` is the map `lim` applied to `a` precomposed with `F k (X⟦1⟧) ≅ (F k X)⟦1⟧`,
then precomposed with the inverse of `F' (X⟦1⟧) ≅ (F' X)⟦1⟧`. -/
theorem limShift_apply (X K : 𝒞₀) (k : J) (a : ((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) :
    Ξ.limShift X K k a = (Ξ.F'.commShiftIso (1 : ℤ)).inv.app X ≫
      Ξ.lim (X⟦(1 : ℤ)⟧) K k (((Ξ.F k).commShiftIso (1 : ℤ)).hom.app X ≫ a) := rfl

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] [HasShift 𝒟 ℤ] [Ξ.F'.CommShift ℤ] in
/-- For `f : Z ⟶ X⟦1⟧`, precomposing `raiseShift X K k m h a` with `F m f` followed by
`F m (X⟦1⟧) ≅ (F m X)⟦1⟧` gives the transition map applied to the corresponding composite at
stage `k`. -/
theorem raiseShift_comp_of_map (Z X K : 𝒞₀) (k m : J) (h : k ≤ m) (f : Z ⟶ X⟦(1 : ℤ)⟧)
    (a : ((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) :
    ((Ξ.F m).map f ≫ ((Ξ.F m).commShiftIso (1 : ℤ)).hom.app X) ≫ Ξ.raiseShift X K k m h a =
      Ξ.raiseHom Z K k m h (((Ξ.F k).map f ≫ ((Ξ.F k).commShiftIso (1 : ℤ)).hom.app X) ≫ a) := by
  simp only [raiseShift_apply, raiseHom_apply, Category.assoc, Iso.hom_inv_id_app_assoc,
    Ξ.raise_map_comp]

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] in
/-- For `f : Z ⟶ X⟦1⟧`, precomposing `limShift X K k a` with `F' f` followed by
`F' (X⟦1⟧) ≅ (F' X)⟦1⟧` gives the map to the limit applied to the corresponding composite at
stage `k`. -/
theorem limShift_comp_of_map (Z X K : 𝒞₀) (k : J) (f : Z ⟶ X⟦(1 : ℤ)⟧)
    (a : ((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) :
    (Ξ.F'.map f ≫ (Ξ.F'.commShiftIso (1 : ℤ)).hom.app X) ≫ Ξ.limShift X K k a =
      Ξ.limHom Z K k (((Ξ.F k).map f ≫ ((Ξ.F k).commShiftIso (1 : ℤ)).hom.app X) ≫ a) := by
  simp only [limShift_apply, limHom_apply, Category.assoc, Iso.hom_inv_id_app_assoc,
    Ξ.lim_map_comp]

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] [HasShift 𝒟 ℤ] [Ξ.F'.CommShift ℤ] in
/-- The shifted transition maps are transitive. -/
theorem raiseShift_raiseShift (X K : 𝒞₀) (k m n : J) (hkm : k ≤ m) (hmn : m ≤ n)
    (a : ((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) :
    Ξ.raiseShift X K m n hmn (Ξ.raiseShift X K k m hkm a) =
      Ξ.raiseShift X K k n (hkm.trans hmn) a := by
  simp only [raiseShift, AddMonoidHom.mk'_apply, Iso.hom_inv_id_app_assoc, Ξ.raise_raise]

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] [HasShift 𝒟 ℤ] [Ξ.F'.CommShift ℤ] in
/-- The shifted transition maps commute with precomposition by `(F k φ)⟦1⟧` and `(F m φ)⟦1⟧` for
a morphism `φ` of `𝒞₀`. -/
theorem raiseShift_map_comp (X' X K : 𝒞₀) (k m : J) (h : k ≤ m) (φ : X' ⟶ X)
    (a : ((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) :
    Ξ.raiseShift X' K k m h ((shiftFunctor _ (1 : ℤ)).map ((Ξ.F k).map φ) ≫ a) =
      (shiftFunctor _ (1 : ℤ)).map ((Ξ.F m).map φ) ≫ Ξ.raiseShift X K k m h a := by
  simp only [raiseShift, AddMonoidHom.mk'_apply]
  rw [← Functor.commShiftIso_hom_naturality_assoc, Ξ.raise_map_comp,
    Functor.commShiftIso_inv_naturality_assoc]

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] in
/-- The shifted maps to the limit commute with precomposition by `(F k φ)⟦1⟧` and `(F' φ)⟦1⟧` for
a morphism `φ` of `𝒞₀`. -/
theorem limShift_map_comp (X' X K : 𝒞₀) (k : J) (φ : X' ⟶ X)
    (a : ((Ξ.F k).obj X)⟦(1 : ℤ)⟧ ⟶ (Ξ.F k).obj K) :
    Ξ.limShift X' K k ((shiftFunctor _ (1 : ℤ)).map ((Ξ.F k).map φ) ≫ a) =
      (shiftFunctor _ (1 : ℤ)).map (Ξ.F'.map φ) ≫ Ξ.limShift X K k a := by
  simp only [limShift, AddMonoidHom.mk'_apply]
  rw [← Functor.commShiftIso_hom_naturality_assoc, Ξ.lim_map_comp,
    Functor.commShiftIso_inv_naturality_assoc]

omit [Preadditive 𝒞₀] [HasZeroObject 𝒞₀] [∀ n : ℤ, (shiftFunctor 𝒞₀ n).Additive]
  [Pretriangulated 𝒞₀] [∀ k, HasZeroObject (𝒞 k)] [∀ k (n : ℤ), (shiftFunctor (𝒞 k) n).Additive]
  [∀ k, Pretriangulated (𝒞 k)] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
  [Pretriangulated 𝒟] in
/-- The colimit property for `X⟦1⟧` is the colimit property for the morphisms out of the
shifts `(F k X)⟦1⟧`. -/
theorem isStagesColimit_shift {X K : 𝒞₀} (h : Ξ.IsColimitAt (X⟦(1 : ℤ)⟧) K) :
    IsStagesColimit (fun k m hkm => Ξ.raiseShift X K k m hkm) (fun k => Ξ.limShift X K k) :=
  IsStagesColimit.ofEquiv (G := fun k => (Ξ.F k).obj (X⟦(1 : ℤ)⟧) ⟶ (Ξ.F k).obj K) _ _
    (fun k => { toFun := fun a => ((Ξ.F k).commShiftIso (1 : ℤ)).hom.app X ≫ a
                invFun := fun b => ((Ξ.F k).commShiftIso (1 : ℤ)).inv.app X ≫ b
                left_inv := fun a => by simp
                right_inv := fun b => by simp })
    { toFun := fun a => (Ξ.F'.commShiftIso (1 : ℤ)).hom.app X ≫ a
      invFun := fun b => (Ξ.F'.commShiftIso (1 : ℤ)).inv.app X ≫ b
      left_inv := fun a => by simp
      right_inv := fun b => by simp }
    (fun k m hkm a => by simp [raiseShift])
    (fun k a => by simp [limShift]) h

/-- **The colimit property passes to the third vertex of a distinguished triangle**: for exact
functors `F k`, `F'` and a distinguished triangle `X ⟶ Y ⟶ E ⟶ X⟦1⟧` of `𝒞₀`, if the colimit
property holds for `Y`, `X⟦1⟧`, `Y⟦1⟧` and `X` (against `K`), it holds for `E`. This is the five
lemma on directed colimits applied to the images of the triangle. -/
theorem IsColimitAt.of_distTriang [IsDirected J (· ≤ ·)] [∀ k, (Ξ.F k).IsTriangulated]
    [Ξ.F'.IsTriangulated] (T : Triangle 𝒞₀) (hT : T ∈ distTriang 𝒞₀) (K : 𝒞₀)
    (hY : Ξ.IsColimitAt T.obj₂ K) (hX₁ : Ξ.IsColimitAt (T.obj₁⟦(1 : ℤ)⟧) K)
    (hY₁ : Ξ.IsColimitAt (T.obj₂⟦(1 : ℤ)⟧) K) (hX : Ξ.IsColimitAt T.obj₁ K) :
    Ξ.IsColimitAt T.obj₃ K := by
  have h₁ := Ξ.isStagesColimit_shift hY₁
  have h₂ := Ξ.isStagesColimit_shift hX₁
  exact IsStagesColimit.of_distTriang (fun k => (Ξ.F k).mapTriangle.obj T)
    (fun k => (Ξ.F k).map_distinguished T hT) (fun k => (Ξ.F k).obj K)
    (Ξ.F'.mapTriangle.obj T) (Ξ.F'.map_distinguished T hT) (Ξ.F'.obj K)
    (fun k m hkm => Ξ.raiseShift T.obj₂ K k m hkm) (fun k m hkm => Ξ.raiseShift T.obj₁ K k m hkm)
    (fun k m hkm => Ξ.raiseHom T.obj₃ K k m hkm) (fun k m hkm => Ξ.raiseHom T.obj₂ K k m hkm)
    (fun k m hkm => Ξ.raiseHom T.obj₁ K k m hkm)
    (fun k => Ξ.limShift T.obj₂ K k) (fun k => Ξ.limShift T.obj₁ K k)
    (fun k => Ξ.limHom T.obj₃ K k) (fun k => Ξ.limHom T.obj₂ K k)
    (fun k => Ξ.limHom T.obj₁ K k)
    (fun k m hkm a => (Ξ.raiseShift_map_comp _ _ K k m hkm T.mor₁ a).symm)
    (fun k m hkm a => Ξ.raiseShift_comp_of_map _ _ K k m hkm T.mor₃ a)
    (fun k m hkm a => (Ξ.raise_map_comp _ _ K k m hkm T.mor₂ a).symm)
    (fun k m hkm a => (Ξ.raise_map_comp _ _ K k m hkm T.mor₁ a).symm)
    (fun k a => Ξ.limShift_map_comp _ _ K k T.mor₁ a)
    (fun k a => (Ξ.limShift_comp_of_map _ _ K k T.mor₃ a).symm)
    (fun k a => Ξ.lim_map_comp _ _ K k T.mor₂ a)
    (fun k a => Ξ.lim_map_comp _ _ K k T.mor₁ a)
    (fun k m n hkm hmn a => Ξ.raiseShift_raiseShift _ K k m n hkm hmn a)
    (fun k m n hkm hmn a => Ξ.raise_raise _ K k m n hkm hmn a)
    h₁.exists_stage h₂ (fun k m hkm a => Ξ.lim_raise _ K k m hkm a) hY hX.exists_trans_eq

end Triangulated

end StageHomSystem

end Stacks
