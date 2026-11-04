module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent

/-!
# The five lemma for elementwise filtered colimits of abelian groups

`Stacks.IsStagesColimit` records, elementwise, that a type is the filtered colimit of a system of
stages. For a directed index, filtered colimits of abelian groups are exact, so the five lemma
passes to them: given a five-term complex of directed systems of abelian groups, exact in the
middle three places, mapping to a five-term complex at the limit, also exact in the middle three
places, the comparison out of the colimit is a bijection in the middle as soon as it is a
bijection in the second and fourth places, surjective in the first and injective in the fifth.

This is the step of the induction of Stacks 08GP in the proof of Stacks 09RI that passes from
the two pieces and the intersection of an elementary distinguished square to the whole space,
through the long exact Mayer–Vietoris sequence of homomorphisms in the derived category
(Stacks 08H9).

## Main results

* `Stacks.IsStagesColimit.of_fiveTerm`: the five lemma, elementwise.
* `Stacks.IsStagesColimit.of_distTriang`: the same for the long exact sequences of homomorphisms
  out of distinguished triangles `X ⟶ Y ⟶ E ⟶ X⟦1⟧` into objects `K`, at each stage of a
  directed system of pretriangulated categories and at the limit: the homomorphism groups out of
  the third vertices form a filtered colimit once those out of `X⟦1⟧` and `Y` do, those out of
  `Y⟦1⟧` are jointly surjective and those out of `X` are eventually injective. The transition
  maps are arbitrary additive maps; their compatibility with the maps of the triangles is the
  naturality hypothesis.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
-/

@[expose] public section

universe v w v' u'

namespace Stacks

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {A₁ A₂ A₃ A₄ A₅ : I → Type w} [∀ i, AddCommGroup (A₁ i)] [∀ i, AddCommGroup (A₂ i)]
  [∀ i, AddCommGroup (A₃ i)] [∀ i, AddCommGroup (A₄ i)] [∀ i, AddCommGroup (A₅ i)]
  {B₁ B₂ B₃ B₄ B₅ : Type w} [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
  [AddCommGroup B₄] [AddCommGroup B₅]

/-- **The five lemma for elementwise filtered colimits of abelian groups.** Let
`A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄ ⟶ A₅` be a sequence of directed systems of abelian groups (maps `f`,
transition maps `t`), exact at `A₂`, `A₃` and `A₄` in the sense used below, mapping by `ι`
compatibly to a sequence `B₁ ⟶ B₂ ⟶ B₃ ⟶ B₄ ⟶ B₅` (maps `g`) exact at `B₂`, `B₃`, `B₄`. If
`B₂` and `B₄` are the filtered colimits of `A₂` and `A₄`, every element of `B₁` comes from a
stage, two elements of a stage of `A₅` with the same image in `B₅` agree at a later stage, and
the maps `A₃ ⟶ B₃` form a cocone, then `B₃` is the filtered colimit of `A₃`. -/
theorem IsStagesColimit.of_fiveTerm
    {t₁ : ∀ i j : I, i ≤ j → A₁ i →+ A₁ j} {t₂ : ∀ i j : I, i ≤ j → A₂ i →+ A₂ j}
    {t₃ : ∀ i j : I, i ≤ j → A₃ i →+ A₃ j} {t₄ : ∀ i j : I, i ≤ j → A₄ i →+ A₄ j}
    {t₅ : ∀ i j : I, i ≤ j → A₅ i →+ A₅ j}
    {ι₁ : ∀ i, A₁ i →+ B₁} {ι₂ : ∀ i, A₂ i →+ B₂} {ι₃ : ∀ i, A₃ i →+ B₃}
    {ι₄ : ∀ i, A₄ i →+ B₄} {ι₅ : ∀ i, A₅ i →+ B₅}
    {f₁ : ∀ i, A₁ i →+ A₂ i} {f₂ : ∀ i, A₂ i →+ A₃ i} {f₃ : ∀ i, A₃ i →+ A₄ i}
    {f₄ : ∀ i, A₄ i →+ A₅ i}
    {g₁ : B₁ →+ B₂} {g₂ : B₂ →+ B₃} {g₃ : B₃ →+ B₄} {g₄ : B₄ →+ B₅}
    (ht₁ : ∀ i j h a, f₁ j (t₁ i j h a) = t₂ i j h (f₁ i a))
    (ht₂ : ∀ i j h a, f₂ j (t₂ i j h a) = t₃ i j h (f₂ i a))
    (ht₃ : ∀ i j h a, f₃ j (t₃ i j h a) = t₄ i j h (f₃ i a))
    (ht₄ : ∀ i j h a, f₄ j (t₄ i j h a) = t₅ i j h (f₄ i a))
    (hι₁ : ∀ i a, ι₂ i (f₁ i a) = g₁ (ι₁ i a)) (hι₂ : ∀ i a, ι₃ i (f₂ i a) = g₂ (ι₂ i a))
    (hι₃ : ∀ i a, ι₄ i (f₃ i a) = g₃ (ι₃ i a)) (hι₄ : ∀ i a, ι₅ i (f₄ i a) = g₄ (ι₄ i a))
    (htt₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) a,
      t₂ j k hjk (t₂ i j hij a) = t₂ i k (hij.trans hjk) a)
    (htt₃ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) a,
      t₃ j k hjk (t₃ i j hij a) = t₃ i k (hij.trans hjk) a)
    (hf₂₁ : ∀ i a, f₂ i (f₁ i a) = 0)
    (hf₃ : ∀ i a, f₃ i a = 0 → ∃ b, f₂ i b = a) (hf₄ : ∀ i a, f₄ i a = 0 → ∃ b, f₃ i b = a)
    (hg₄₃ : ∀ x, g₄ (g₃ x) = 0)
    (hg₂ : ∀ x, g₂ x = 0 → ∃ y, g₁ y = x) (hg₃ : ∀ x, g₃ x = 0 → ∃ y, g₂ y = x)
    (h₁ : ∀ x, ∃ (i : I) (a : A₁ i), ι₁ i a = x)
    (h₂ : IsStagesColimit (fun i j h => t₂ i j h) (fun i => ι₂ i))
    (h₃ : ∀ i j h a, ι₃ j (t₃ i j h a) = ι₃ i a)
    (h₄ : IsStagesColimit (fun i j h => t₄ i j h) (fun i => ι₄ i))
    (h₅ : ∀ (i : I) (a a' : A₅ i), ι₅ i a = ι₅ i a' → ∃ (j : I) (h : i ≤ j),
      t₅ i j h a = t₅ i j h a') :
    IsStagesColimit (fun i j h => t₃ i j h) (fun i => ι₃ i) where
  ι_trans := h₃
  exists_stage x := by
    obtain ⟨i, y, hy⟩ := h₄.exists_stage (g₃ x)
    obtain ⟨j, hij, hj⟩ := h₅ i (f₄ i y) 0 (by
      rw [hι₄, hy, hg₄₃, map_zero])
    obtain ⟨z, hz⟩ := hf₄ j (t₄ i j hij y) (by rw [ht₄, hj, map_zero])
    obtain ⟨w, hw⟩ := hg₃ (x - ι₃ j z) (by
      rw [map_sub, ← hι₃, hz]
      rw [h₄.ι_trans, hy, sub_self])
    obtain ⟨k, v, hv⟩ := h₂.exists_stage w
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j k
    refine ⟨m, t₃ j m hjm z + t₃ k m hkm (f₂ k v), ?_⟩
    simp only [map_add, h₃, hι₂, hv, hw]
    abel
  exists_trans_eq i s s' hss' := by
    have hd : ι₃ i (s - s') = 0 := by rw [map_sub, hss', sub_self]
    obtain ⟨j, hij, hj⟩ := h₄.exists_trans_eq i (f₃ i (s - s')) 0 (by
      rw [hι₃, hd, map_zero, map_zero])
    simp only [map_zero] at hj
    obtain ⟨e, he⟩ := hf₃ j (t₃ i j hij (s - s')) (by rw [ht₃, hj])
    obtain ⟨c, hc⟩ := hg₂ (ι₂ j e) (by rw [← hι₂, he, h₃, hd])
    obtain ⟨k, a, ha⟩ := h₁ c
    obtain ⟨m, hjm, hkm⟩ := directed_of (· ≤ ·) j k
    obtain ⟨n, hmn, hn⟩ := h₂.exists_trans_eq m (t₂ j m hjm e) (f₁ m (t₁ k m hkm a)) (by
      rw [h₂.ι_trans, ht₁, h₂.ι_trans, hι₁, ha, hc])
    have key : t₃ i n (hij.trans (hjm.trans hmn)) (s - s') = 0 := by
      rw [← htt₃ i j n hij (hjm.trans hmn), ← he, ← ht₂, ← htt₂ j m n hjm hmn, hn, ht₂, hf₂₁,
        map_zero]
    refine ⟨n, hij.trans (hjm.trans hmn), ?_⟩
    rw [← sub_eq_zero, ← map_sub, key]

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated

/-- Exactness of `Hom(-, K)` at the middle term of a distinguished triangle, with the
factorization written as `T.mor₂ ≫ b = a`. -/
private theorem exists_comp_eq_of_comp_eq_zero {𝒞 : Type u'} [Category.{v'} 𝒞] [Preadditive 𝒞]
    [HasZeroObject 𝒞] [HasShift 𝒞 ℤ] [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]
    {T : Triangle 𝒞} (hT : T ∈ distTriang 𝒞) {K : 𝒞} (a : T.obj₂ ⟶ K) (ha : T.mor₁ ≫ a = 0) :
    ∃ b, T.mor₂ ≫ b = a :=
  (Triangle.yoneda_exact₂ _ hT a ha).imp fun _ => Eq.symm

/-- **The five lemma on directed colimits, for homomorphisms out of distinguished triangles.**
Let `𝒞 i` be a directed system of pretriangulated categories (no functors between them are
needed), `𝒟` a pretriangulated category, `T i : X i ⟶ Y i ⟶ E i ⟶ X i⟦1⟧` and
`T' : X' ⟶ Y' ⟶ E' ⟶ X'⟦1⟧` distinguished triangles and `K i`, `K'` objects. Suppose given
additive transition maps `t₁, …, t₅` on the groups of morphisms into `K` out of `Y⟦1⟧`, `X⟦1⟧`,
`E`, `Y`, `X`, and additive maps `ι₁, …, ι₅` to the corresponding groups at the limit, commuting
with precomposition by the morphisms of the triangles (`ht₁`–`ht₄`, `hι₁`–`hι₄`), with `t₂`,
`t₃` functorial. If the groups out of `X⟦1⟧` and out of `Y` are the filtered colimits of their
stages, the maps out of `Y⟦1⟧` are jointly surjective, two morphisms out of `X i` with the same
image agree at a later stage, and the maps out of `E` form a cocone, then
`Hom(E', K')` is the filtered colimit of the `Hom(E i, K i)`.

This is the Mayer–Vietoris step of the proof of Stacks 09RI, for the triangle of Stacks 08GV. -/
theorem IsStagesColimit.of_distTriang
    {𝒞 : I → Type u'} [∀ i, Category.{v'} (𝒞 i)] [∀ i, Preadditive (𝒞 i)]
    [∀ i, HasZeroObject (𝒞 i)] [∀ i, HasShift (𝒞 i) ℤ]
    [∀ i (n : ℤ), (shiftFunctor (𝒞 i) n).Additive] [∀ i, Pretriangulated (𝒞 i)]
    {𝒟 : Type u'} [Category.{v'} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
    [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
    (T : ∀ i, Triangle (𝒞 i)) (hT : ∀ i, T i ∈ distTriang (𝒞 i)) (K : ∀ i, 𝒞 i)
    (T' : Triangle 𝒟) (hT' : T' ∈ distTriang 𝒟) (K' : 𝒟)
    (t₁ : ∀ i j : I, i ≤ j → ((T i).obj₂⟦(1 : ℤ)⟧ ⟶ K i) →+ ((T j).obj₂⟦(1 : ℤ)⟧ ⟶ K j))
    (t₂ : ∀ i j : I, i ≤ j → ((T i).obj₁⟦(1 : ℤ)⟧ ⟶ K i) →+ ((T j).obj₁⟦(1 : ℤ)⟧ ⟶ K j))
    (t₃ : ∀ i j : I, i ≤ j → ((T i).obj₃ ⟶ K i) →+ ((T j).obj₃ ⟶ K j))
    (t₄ : ∀ i j : I, i ≤ j → ((T i).obj₂ ⟶ K i) →+ ((T j).obj₂ ⟶ K j))
    (t₅ : ∀ i j : I, i ≤ j → ((T i).obj₁ ⟶ K i) →+ ((T j).obj₁ ⟶ K j))
    (ι₁ : ∀ i, ((T i).obj₂⟦(1 : ℤ)⟧ ⟶ K i) →+ (T'.obj₂⟦(1 : ℤ)⟧ ⟶ K'))
    (ι₂ : ∀ i, ((T i).obj₁⟦(1 : ℤ)⟧ ⟶ K i) →+ (T'.obj₁⟦(1 : ℤ)⟧ ⟶ K'))
    (ι₃ : ∀ i, ((T i).obj₃ ⟶ K i) →+ (T'.obj₃ ⟶ K'))
    (ι₄ : ∀ i, ((T i).obj₂ ⟶ K i) →+ (T'.obj₂ ⟶ K'))
    (ι₅ : ∀ i, ((T i).obj₁ ⟶ K i) →+ (T'.obj₁ ⟶ K'))
    (ht₁ : ∀ i j h a, (shiftFunctor _ (1 : ℤ)).map (T j).mor₁ ≫ t₁ i j h a =
      t₂ i j h ((shiftFunctor _ (1 : ℤ)).map (T i).mor₁ ≫ a))
    (ht₂ : ∀ i j h a, (T j).mor₃ ≫ t₂ i j h a = t₃ i j h ((T i).mor₃ ≫ a))
    (ht₃ : ∀ i j h a, (T j).mor₂ ≫ t₃ i j h a = t₄ i j h ((T i).mor₂ ≫ a))
    (ht₄ : ∀ i j h a, (T j).mor₁ ≫ t₄ i j h a = t₅ i j h ((T i).mor₁ ≫ a))
    (hι₁ : ∀ i a, ι₂ i ((shiftFunctor _ (1 : ℤ)).map (T i).mor₁ ≫ a) =
      (shiftFunctor _ (1 : ℤ)).map T'.mor₁ ≫ ι₁ i a)
    (hι₂ : ∀ i a, ι₃ i ((T i).mor₃ ≫ a) = T'.mor₃ ≫ ι₂ i a)
    (hι₃ : ∀ i a, ι₄ i ((T i).mor₂ ≫ a) = T'.mor₂ ≫ ι₃ i a)
    (hι₄ : ∀ i a, ι₅ i ((T i).mor₁ ≫ a) = T'.mor₁ ≫ ι₄ i a)
    (htt₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) a,
      t₂ j k hjk (t₂ i j hij a) = t₂ i k (hij.trans hjk) a)
    (htt₃ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) a,
      t₃ j k hjk (t₃ i j hij a) = t₃ i k (hij.trans hjk) a)
    (h₁ : ∀ x, ∃ (i : I) (a : (T i).obj₂⟦(1 : ℤ)⟧ ⟶ K i), ι₁ i a = x)
    (h₂ : IsStagesColimit (fun i j h => t₂ i j h) (fun i => ι₂ i))
    (h₃ : ∀ i j h a, ι₃ j (t₃ i j h a) = ι₃ i a)
    (h₄ : IsStagesColimit (fun i j h => t₄ i j h) (fun i => ι₄ i))
    (h₅ : ∀ (i : I) (a a' : (T i).obj₁ ⟶ K i), ι₅ i a = ι₅ i a' → ∃ (j : I) (h : i ≤ j),
      t₅ i j h a = t₅ i j h a') :
    IsStagesColimit (fun i j h => t₃ i j h) (fun i => ι₃ i) := by
  refine IsStagesColimit.of_fiveTerm
    (f₁ := fun i => Preadditive.leftComp _ ((shiftFunctor _ (1 : ℤ)).map (T i).mor₁))
    (f₂ := fun i => Preadditive.leftComp _ (T i).mor₃)
    (f₃ := fun i => Preadditive.leftComp _ (T i).mor₂)
    (f₄ := fun i => Preadditive.leftComp _ (T i).mor₁)
    (g₁ := Preadditive.leftComp _ ((shiftFunctor 𝒟 (1 : ℤ)).map T'.mor₁))
    (g₂ := Preadditive.leftComp _ T'.mor₃)
    (g₃ := Preadditive.leftComp _ T'.mor₂) (g₄ := Preadditive.leftComp _ T'.mor₁)
    ht₁ ht₂ ht₃ ht₄ hι₁ hι₂ hι₃ hι₄ htt₂ htt₃ ?_ ?_ ?_ ?_ ?_ ?_ h₁ h₂ h₃ h₄ h₅
  · intro i a
    show (T i).mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (T i).mor₁ ≫ a = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₃₁ _ (hT i), zero_comp]
  · exact fun i a ha => exists_comp_eq_of_comp_eq_zero (rot_of_distTriang _ (hT i)) a ha
  · exact fun i a ha => exists_comp_eq_of_comp_eq_zero (hT i) a ha
  · intro x
    show T'.mor₁ ≫ T'.mor₂ ≫ x = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ _ hT', zero_comp]
  · intro x hx
    obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ _ (rot_of_distTriang _ (rot_of_distTriang _ hT'))
      x hx
    refine ⟨-b, ?_⟩
    show (shiftFunctor 𝒟 (1 : ℤ)).map T'.mor₁ ≫ (-b) = x
    rw [hb]
    exact (Preadditive.comp_neg _ _).trans (Preadditive.neg_comp _ _).symm
  · exact fun x hx => exists_comp_eq_of_comp_eq_zero (rot_of_distTriang _ hT') x hx

end Stacks
