module

public import StacksFrontier.CategoryTheory.Abelian.ExtTransport
public import StacksFrontier.Algebra.Homology.DirectedTowerDevissage

/-!
# Directed systems of `Ext` groups along exact functors

Let `𝒜` be an abelian category, `G` an object of `𝒜`, and `(P_i : 𝒜 ⥤ 𝒞_i)` a directed family of
exact functors together with an exact functor `P_∞ : 𝒜 ⥤ 𝒞_∞`. Suppose given transition maps
`τ : Ext^m(P_i M, P_i G) → Ext^m(P_{i'} M, P_{i'} G)` and maps to the limit
`λ : Ext^m(P_i M, P_i G) → Ext^m(P_∞ M, P_∞ G)`, functorial and compatible with precomposition by
`P(v)` and with the connecting maps of short exact sequences of `𝒜`. Then the class of objects `M`
for which `colim_i Ext^m(P_i M, P_i G) → Ext^m(P_∞ M, P_∞ G)` is an isomorphism in every degree
is closed under isomorphisms, finite direct sums, and passes from the first two terms of a short
exact sequence to the third. These are the three closure properties used by the Mayer–Vietoris
argument for Stacks 09YQ, where `P_i` is inverse image of étale sheaves along a directed system of
schemes.

## Main definitions

* `Stacks.ExtDirectedSystem.Good`: the comparison is an isomorphism in every degree, expressed
  elementwise.

## Main results

* `Stacks.ExtDirectedSystem.good_of_shortExact`: the five lemma.
* `Stacks.ExtDirectedSystem.good_of_iso`, `Stacks.ExtDirectedSystem.good_biprod`.
-/

@[expose] public noncomputable section

universe w v v' v'' u u' u'' t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Homology.DirectedTower

namespace Stacks.ExtDirectedSystem

variable {J : Type t} [Preorder J] [IsDirected J (· ≤ ·)]
  {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  {𝒞 : J → Type u'} [∀ i, Category.{v'} (𝒞 i)] [∀ i, Abelian (𝒞 i)] [∀ i, HasExt.{w} (𝒞 i)]
  {𝒞L : Type u''} [Category.{v''} 𝒞L] [Abelian 𝒞L] [HasExt.{w} 𝒞L]
  (P : ∀ i, 𝒜 ⥤ 𝒞 i) [∀ i, (P i).Additive] [∀ i, PreservesFiniteLimits (P i)]
  [∀ i, PreservesFiniteColimits (P i)]
  (PL : 𝒜 ⥤ 𝒞L) [PL.Additive] [PreservesFiniteLimits PL] [PreservesFiniteColimits PL]
  (G : 𝒜)
  (τ : ∀ {i i' : J}, i ≤ i' → ∀ (M : 𝒜) (m : ℕ),
    Ext.{w} ((P i).obj M) ((P i).obj G) m →+ Ext.{w} ((P i').obj M) ((P i').obj G) m)
  (lm : ∀ (i : J) (M : 𝒜) (m : ℕ),
    Ext.{w} ((P i).obj M) ((P i).obj G) m →+ Ext.{w} (PL.obj M) (PL.obj G) m)

/-- The comparison of the colimit of the stages with the limit is an isomorphism on `M` in every
degree, expressed elementwise. -/
def Good (M : 𝒜) : Prop :=
  ∀ m, DirectedSurj (A := fun i => Ext.{w} ((P i).obj M) ((P i).obj G) m)
      (L := Ext.{w} (PL.obj M) (PL.obj G) m) (fun i x => lm i M m x) ∧
    DirectedEvInj (A := fun i => Ext.{w} ((P i).obj M) ((P i).obj G) m)
      (L := Ext.{w} (PL.obj M) (PL.obj G) m) (fun i x => lm i M m x) (fun h x => τ h M m x)

variable {P PL G τ lm}
  (hττ : ∀ {i i' i'' : J} (h : i ≤ i') (h' : i' ≤ i'') M m x,
    τ h' M m (τ h M m x) = τ (h.trans h') M m x)
  (hlτ : ∀ {i i' : J} (h : i ≤ i') M m x, lm i' M m (τ h M m x) = lm i M m x)
  (hτmk : ∀ {i i' : J} (h : i ≤ i') {B C : 𝒜} (v : B ⟶ C) m x,
    τ h B m ((Ext.mk₀ ((P i).map v)).comp x (zero_add m)) =
      (Ext.mk₀ ((P i').map v)).comp (τ h C m x) (zero_add m))
  (hlmk : ∀ (i : J) {B C : 𝒜} (v : B ⟶ C) m x,
    lm i B m ((Ext.mk₀ ((P i).map v)).comp x (zero_add m)) =
      (Ext.mk₀ (PL.map v)).comp (lm i C m x) (zero_add m))
  (hτδ : ∀ {i i' : J} (h : i ≤ i') {T : ShortComplex 𝒜} (hT : T.ShortExact) m x,
    τ h T.X₃ (m + 1) ((hT.map_of_exact (P i)).extClass.comp x (add_comm 1 m)) =
      (hT.map_of_exact (P i')).extClass.comp (τ h T.X₁ m x) (add_comm 1 m))
  (hlδ : ∀ (i : J) {T : ShortComplex 𝒜} (hT : T.ShortExact) m x,
    lm i T.X₃ (m + 1) ((hT.map_of_exact (P i)).extClass.comp x (add_comm 1 m)) =
      (hT.map_of_exact PL).extClass.comp (lm i T.X₁ m x) (add_comm 1 m))

include hττ hlτ hτmk hlmk hτδ hlδ in
/-- **The five lemma.** For a short exact sequence `0 → A → B → C → 0` of `𝒜`, if the comparison
is an isomorphism on `A` and on `B` in every degree, it is one on `C` in every degree. -/
theorem good_of_shortExact {T : ShortComplex 𝒜} (hT : T.ShortExact)
    (h₁ : Good P PL G τ lm T.X₁) (h₂ : Good P PL G τ lm T.X₂) : Good P PL G τ lm T.X₃ := by
  have hTi := fun i => hT.map_of_exact (P i)
  have hTl := hT.map_of_exact PL
  intro m
  refine surj_and_evInj_of_shortExact
    (EC := fun i m => Ext.{w} ((P i).obj T.X₃) ((P i).obj G) m)
    (EB := fun i m => Ext.{w} ((P i).obj T.X₂) ((P i).obj G) m)
    (EA := fun i m => Ext.{w} ((P i).obj T.X₁) ((P i).obj G) m)
    (eC := fun m => Ext.{w} (PL.obj T.X₃) (PL.obj G) m)
    (eB := fun m => Ext.{w} (PL.obj T.X₂) (PL.obj G) m)
    (eA := fun m => Ext.{w} (PL.obj T.X₁) (PL.obj G) m)
    (tC := fun h m => τ h T.X₃ m) (tB := fun h m => τ h T.X₂ m) (tA := fun h m => τ h T.X₁ m)
    (lC := fun i m => lm i T.X₃ m) (lB := fun i m => lm i T.X₂ m) (lA := fun i m => lm i T.X₁ m)
    (a := fun i m => (Ext.mk₀ ((P i).map T.g)).precomp ((P i).obj G) (zero_add m))
    (b := fun i m => (Ext.mk₀ ((P i).map T.f)).precomp ((P i).obj G) (zero_add m))
    (d := fun i m => (hTi i).extClass.precomp ((P i).obj G) (add_comm 1 m))
    (a' := fun m => (Ext.mk₀ (PL.map T.g)).precomp (PL.obj G) (zero_add m))
    (b' := fun m => (Ext.mk₀ (PL.map T.f)).precomp (PL.obj G) (zero_add m))
    (d' := fun m => hTl.extClass.precomp (PL.obj G) (add_comm 1 m))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun m => (h₂ m).1)
    (fun m => (h₂ m).2) (fun m => (h₁ m).1) (fun m => (h₁ m).2) m
  · intro i i' i'' h h' m x; exact hττ h h' _ m x
  · intro i i' i'' h h' m x; exact hττ h h' _ m x
  · intro i i' h m x; exact hlτ h _ m x
  · intro i i' h m x; exact hlτ h _ m x
  · intro i i' h m x; exact hlτ h _ m x
  · intro i i' h m x; exact (hτmk h T.g m x).symm
  · intro i i' h m x; exact (hτmk h T.f m x).symm
  · intro i i' h m x; exact (hτδ h hT m x).symm
  · intro i m x; exact hlmk i T.g m x
  · intro i m x; exact hlmk i T.f m x
  · intro i m x; exact hlδ i hT m x
  · intro i x hx
    exact Ext.precomp_mk₀_injective_of_epi _ _ (hg := (hTi i).epi_g) (hx.trans (by simp))
  · intro i m y hy; exact Ext.contravariant_sequence_exact₂ (hTi i) _ y hy
  · intro i m x hx; exact Ext.contravariant_sequence_exact₃ (hTi i) _ x hx (add_comm 1 m)
  · intro i m y
    simp only [Ext.bilinearComp_apply_apply]
    exact (hTi i).extClass_comp_assoc y
  · intro x hx
    exact Ext.precomp_mk₀_injective_of_epi _ _ (hg := hTl.epi_g) (hx.trans (by simp))
  · intro m y
    simp only [Ext.bilinearComp_apply_apply]
    exact Stacks.ExtTransport.mk₀_f_comp_mk₀_g_comp hTl y
  · intro m x hx; exact Ext.contravariant_sequence_exact₁ hTl _ x (add_comm 1 m) hx
  · intro m x hx; exact Ext.contravariant_sequence_exact₃ hTl _ x hx (add_comm 1 m)

/-- Precomposition by `Ext.mk₀ e` is bijective for an isomorphism `e`. -/
private theorem precomp_mk₀_bijective_of_isIso {𝒟 : Type u'} [Category.{v'} 𝒟] [Abelian 𝒟]
    [HasExt.{w} 𝒟] {A A' : 𝒟} (e : A ⟶ A') [IsIso e] (B : 𝒟) (m : ℕ) :
    Function.Bijective ((Ext.mk₀ e).precomp B (zero_add m) : Ext.{w} A' B m → _) := by
  have e₁ : (⇑((Ext.mk₀ e).precomp B (zero_add m)) : Ext.{w} A' B m → _) =
      Stacks.ExtTransport.sandwich e (𝟙 B) m := by
    funext x
    simp [Stacks.ExtTransport.sandwich_apply]
  rw [e₁]
  exact Stacks.ExtTransport.sandwich_bijective _ _ m

omit [IsDirected J (· ≤ ·)] [Abelian 𝒜] [∀ i, (P i).Additive] [∀ i, PreservesFiniteLimits (P i)]
  [∀ i, PreservesFiniteColimits (P i)] [PL.Additive] [PreservesFiniteLimits PL]
  [PreservesFiniteColimits PL] in
include hτmk hlmk in
/-- The comparison being an isomorphism is invariant under isomorphism of the object. -/
theorem good_of_iso {M M' : 𝒜} (e : M ≅ M') (hM : Good P PL G τ lm M) :
    Good P PL G τ lm M' := by
  intro m
  have key := surj_evInj_of_bijective (J := J)
    (A := fun i => Ext.{w} ((P i).obj M) ((P i).obj G) m)
    (B := fun i => Ext.{w} ((P i).obj M') ((P i).obj G) m)
    (tA := fun h => τ h M m) (tB := fun h => τ h M' m) (lA := fun i => lm i M m)
    (lB := fun i => lm i M' m)
    (ψ := fun i => (Ext.mk₀ ((P i).map e.hom)).precomp ((P i).obj G) (zero_add m))
    (ψ' := (Ext.mk₀ (PL.map e.hom)).precomp (PL.obj G) (zero_add m))
    (fun i => ?_) ?_ (fun h x => ?_) (fun i x => ?_)
  · exact ⟨key.1 (hM m).1, key.2 (hM m).2⟩
  · exact precomp_mk₀_bijective_of_isIso _ _ m
  · exact (precomp_mk₀_bijective_of_isIso _ _ m).1
  · simp only [Ext.bilinearComp_apply_apply]
    exact (hτmk h e.hom m x).symm
  · simp only [Ext.bilinearComp_apply_apply]
    exact (hlmk i e.hom m x).symm

omit [IsDirected J (· ≤ ·)] in
/-- For an additive functor `F`, every class `x` in `Ext (F (M₁ ⊞ M₂)) N m` is the sum of its
restrictions along `F.map biprod.inl` and `F.map biprod.inr`, pulled back along `F.map biprod.fst`
and `F.map biprod.snd` respectively. -/
theorem biprod_decomp {𝒟 : Type u'} [Category.{v'} 𝒟] [Abelian 𝒟] [HasExt.{w} 𝒟] (F : 𝒜 ⥤ 𝒟)
    [F.Additive] (M₁ M₂ : 𝒜) {N : 𝒟} {m : ℕ} (x : Ext.{w} (F.obj (M₁ ⊞ M₂)) N m) :
    (Ext.mk₀ (F.map biprod.fst)).comp ((Ext.mk₀ (F.map biprod.inl)).comp x (zero_add m))
        (zero_add m) +
      (Ext.mk₀ (F.map biprod.snd)).comp ((Ext.mk₀ (F.map biprod.inr)).comp x (zero_add m))
        (zero_add m) = x := by
  rw [Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, ← Ext.add_comp, ← Ext.mk₀_add,
    ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id, Ext.mk₀_id_comp]

omit [∀ i, PreservesFiniteLimits (P i)] [∀ i, PreservesFiniteColimits (P i)]
  [PreservesFiniteLimits PL] [PreservesFiniteColimits PL] in
include hττ hlτ hτmk hlmk in
/-- The comparison being an isomorphism passes to a direct sum of two objects. -/
theorem good_biprod {M₁ M₂ : 𝒜} (h₁ : Good P PL G τ lm M₁) (h₂ : Good P PL G τ lm M₂) :
    Good P PL G τ lm (M₁ ⊞ M₂) := by
  intro m
  exact surj_evInj_of_sum (J := J)
    (B := fun i => Ext.{w} ((P i).obj (M₁ ⊞ M₂)) ((P i).obj G) m)
    (B₁ := fun i => Ext.{w} ((P i).obj M₁) ((P i).obj G) m)
    (B₂ := fun i => Ext.{w} ((P i).obj M₂) ((P i).obj G) m)
    (t := fun h => τ h _ m) (t₁ := fun h => τ h _ m) (t₂ := fun h => τ h _ m)
    (fun h h' x => hττ h h' _ m x) (fun h h' x => hττ h h' _ m x)
    (l := fun i => lm i _ m) (l₁ := fun i => lm i _ m) (l₂ := fun i => lm i _ m)
    (fun h x => hlτ h _ m x) (fun h x => hlτ h _ m x)
    (p₁ := fun i => (Ext.mk₀ ((P i).map biprod.inl)).precomp ((P i).obj G) (zero_add m))
    (p₂ := fun i => (Ext.mk₀ ((P i).map biprod.inr)).precomp ((P i).obj G) (zero_add m))
    (s₁ := fun i => (Ext.mk₀ ((P i).map biprod.fst)).precomp ((P i).obj G) (zero_add m))
    (s₂ := fun i => (Ext.mk₀ ((P i).map biprod.snd)).precomp ((P i).obj G) (zero_add m))
    (fun i x => by simp only [Ext.bilinearComp_apply_apply]; exact biprod_decomp (P i) M₁ M₂ x)
    (p₁' := (Ext.mk₀ (PL.map biprod.inl)).precomp (PL.obj G) (zero_add m))
    (p₂' := (Ext.mk₀ (PL.map biprod.inr)).precomp (PL.obj G) (zero_add m))
    (s₁' := (Ext.mk₀ (PL.map biprod.fst)).precomp (PL.obj G) (zero_add m))
    (s₂' := (Ext.mk₀ (PL.map biprod.snd)).precomp (PL.obj G) (zero_add m))
    (fun x => by simp only [Ext.bilinearComp_apply_apply]; exact biprod_decomp PL M₁ M₂ x)
    (fun h x => by simp only [Ext.bilinearComp_apply_apply]; exact (hτmk h _ m x).symm)
    (fun h x => by simp only [Ext.bilinearComp_apply_apply]; exact (hτmk h _ m x).symm)
    (fun h x => by simp only [Ext.bilinearComp_apply_apply]; exact (hτmk h _ m x).symm)
    (fun h x => by simp only [Ext.bilinearComp_apply_apply]; exact (hτmk h _ m x).symm)
    (fun i x => by simp only [Ext.bilinearComp_apply_apply]; exact hlmk i _ m x)
    (fun i x => by simp only [Ext.bilinearComp_apply_apply]; exact hlmk i _ m x)
    (fun i x => by simp only [Ext.bilinearComp_apply_apply]; exact hlmk i _ m x)
    (fun i x => by simp only [Ext.bilinearComp_apply_apply]; exact hlmk i _ m x)
    (h₁ m).1 (h₂ m).1 (h₁ m).2 (h₂ m).2

omit [IsDirected J (· ≤ ·)] [Abelian 𝒜] [∀ i, (P i).Additive] [∀ i, PreservesFiniteLimits (P i)]
  [∀ i, PreservesFiniteColimits (P i)] [PL.Additive] [PreservesFiniteLimits PL]
  [PreservesFiniteColimits PL] in
/-- **Transfer along compatible bijections between two systems.** -/
theorem good_of_bijective
    {𝒜' : Type u} [Category.{v} 𝒜'] [Abelian 𝒜']
    {𝒞' : J → Type u'} [∀ i, Category.{v'} (𝒞' i)] [∀ i, Abelian (𝒞' i)]
    [∀ i, HasExt.{w} (𝒞' i)]
    {𝒞L' : Type u''} [Category.{v''} 𝒞L'] [Abelian 𝒞L'] [HasExt.{w} 𝒞L']
    {P' : ∀ i, 𝒜' ⥤ 𝒞' i} [∀ i, (P' i).Additive] [∀ i, PreservesFiniteLimits (P' i)]
    [∀ i, PreservesFiniteColimits (P' i)]
    {PL' : 𝒜' ⥤ 𝒞L'} [PL'.Additive] [PreservesFiniteLimits PL'] [PreservesFiniteColimits PL']
    {G' : 𝒜'}
    {τ' : ∀ {i i' : J}, i ≤ i' → ∀ (M : 𝒜') (m : ℕ),
      Ext.{w} ((P' i).obj M) ((P' i).obj G') m →+ Ext.{w} ((P' i').obj M) ((P' i').obj G') m}
    {lm' : ∀ (i : J) (M : 𝒜') (m : ℕ),
      Ext.{w} ((P' i).obj M) ((P' i).obj G') m →+ Ext.{w} (PL'.obj M) (PL'.obj G') m}
    {M : 𝒜} {M' : 𝒜'}
    (ψ : ∀ i m, Ext.{w} ((P i).obj M) ((P i).obj G) m →+ Ext.{w} ((P' i).obj M') ((P' i).obj G') m)
    (ψ' : ∀ m, Ext.{w} (PL.obj M) (PL.obj G) m →+ Ext.{w} (PL'.obj M') (PL'.obj G') m)
    (hψ : ∀ i m, Function.Bijective (ψ i m)) (hψ' : ∀ m, Function.Injective (ψ' m))
    (ht : ∀ {i i' : J} (h : i ≤ i') m x, ψ i' m (τ h M m x) = τ' h M' m (ψ i m x))
    (hl : ∀ i m x, ψ' m (lm i M m x) = lm' i M' m (ψ i m x))
    (h : Good P' PL' G' τ' lm' M') : Good P PL G τ lm M := by
  intro m
  have key := surj_evInj_of_bijective (J := J)
    (A := fun i => Ext.{w} ((P' i).obj M') ((P' i).obj G') m)
    (B := fun i => Ext.{w} ((P i).obj M) ((P i).obj G) m)
    (tA := fun h => τ' h M' m) (tB := fun h => τ h M m) (lA := fun i => lm' i M' m)
    (lB := fun i => lm i M m) (ψ := fun i => ψ i m) (ψ' := ψ' m) (fun i => hψ i m) (hψ' m)
    (fun h x => ht h m x) (fun i x => hl i m x)
  exact ⟨key.1 (h m).1, key.2 (h m).2⟩

end Stacks.ExtDirectedSystem
