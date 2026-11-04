module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsOverBase
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Formal functions for a principal ideal along the quotient tower

Let `(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative
ring `A`, let `f ∈ A` and let `ℱ` be a sheaf of `𝒪_X`-modules whose `f`-power torsion stabilizes,
that is `ℱ[f^c] = ℱ[fⁿ]` for all `n ≥ c` and some `c`. The middle column of the nine-term
diagram of formal functions is the Milnor short exact sequence of the `f`-power Koszul tower
`E_n = ℱ ⊗_{𝒪_X} (𝒪_X --fⁿ--> 𝒪_X)`. Under the stabilization hypothesis that tower is
pro-isomorphic to the tower of honest quotients `ℱ/fⁿℱ`, so the column may be read off the
quotient tower instead:

`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, ℱ^) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0`,

where `ℱ^` is a derived limit of the quotient tower. This file carries out that substitution: the
short exact sequence is the Milnor sequence of the quotient tower, and the pro-isomorphism
identifies its three terms with the three terms of the Koszul column.

## Main results

* `Stacks.Cohomology.QuotientTowerFormalFunctions.nonempty_proIso_koszulTower_quotientTower` — the
  `f`-power Koszul tower of a sheaf whose `f`-power torsion stabilizes is pro-isomorphic to the
  tower of quotients `ℱ/fⁿℱ`.
* `Stacks.Cohomology.QuotientTowerFormalFunctions`
  `.nonempty_iso_isDerivedLimit_koszulTower_quotientTower` — their derived limits agree.
* `Stacks.Cohomology.QuotientTowerFormalFunctions`
  `.exists_shortExact_homology_derivedSections_quotientTower` — the middle column of the
  nine-term diagram, for the quotient tower, together with the identifications of its three terms
  with the corresponding terms for the Koszul tower.

## Implementation notes

The `f`-power Koszul tower is taken here in the form in which the pro-isomorphism is available:
the inverse system `Ksys` of the cones of the powers `f^(n+1)` of multiplication by `f` on `ℱ`
placed in degree zero, that is the two-term complexes `ℱ --f^(n+1)--> ℱ`. These are the terms
`E_n = ℱ ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` of the source: the two-term complex
`𝒪_X --f^(n+1)--> 𝒪_X` consists of free modules of rank one, so no K-flat resolution intervenes
and the derived tensor product is that cone.

The pro-isomorphism has a special shape: its forward family is a morphism of inverse systems (the
projection of the two-term complex onto its degree-zero cohomology) and its backward family is a
morphism of inverse systems after shifting the index by the stabilization constant. For such
pro-isomorphisms the comparison of first derived inverse limits is elementary: dropping finitely
many levels on the product of the terms of an inverse system differs from the identity by an
explicit telescoping nullhomotopy of the two-term complex whose cokernel is `R¹lim`, so the two
induced maps on `R¹lim` are mutually inverse.

## References

* [Stacks Project, Tag 0H3E](https://stacks.math.columbia.edu/tag/0H3E)
* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
* [Stacks Project, Tag 0H3D](https://stacks.math.columbia.edu/tag/0H3D)
* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase (baseSmul derivedSectionsOver)

universe u

namespace Stacks.Cohomology.QuotientTowerFormalFunctions

/-! ### Shifted pro-isomorphisms of inverse systems -/

/-- Transition maps of an inverse system are computed after two functors by applying them. -/
private lemma tr_comp₂ {D : Type*} [Category D] {E : Type*} [Category E] {E' : Type*}
    [Category E'] (K : ℕᵒᵖ ⥤ D) (W : D ⥤ E) (H : E ⥤ E') {n m : ℕ} (h : n ≤ m) :
    InverseSequence.tr ((K ⋙ W) ⋙ H) h = H.map (W.map (InverseSequence.tr K h)) := rfl

/-- A square of morphisms against transition maps still commutes after applying two functors. -/
private lemma tr_comp₂_comp_map_map {D : Type*} [Category D] {E : Type*} [Category E]
    {E' : Type*} [Category E'] {K₁ K₂ : ℕᵒᵖ ⥤ D} (W : D ⥤ E) (H : E ⥤ E') {n m n' m' : ℕ}
    {h : n ≤ m} {h' : n' ≤ m'} {p : K₁.obj (op n) ⟶ K₂.obj (op n')}
    {q : K₁.obj (op m) ⟶ K₂.obj (op m')}
    (hpq : InverseSequence.tr K₁ h ≫ p = q ≫ InverseSequence.tr K₂ h') :
    InverseSequence.tr ((K₁ ⋙ W) ⋙ H) h ≫ H.map (W.map p) =
      H.map (W.map q) ≫ InverseSequence.tr ((K₂ ⋙ W) ⋙ H) h' := by
  rw [tr_comp₂, tr_comp₂, ← H.map_comp, ← H.map_comp, ← W.map_comp, ← W.map_comp, hpq]

/-- A composite equal to a transition map stays one after applying two functors. -/
private lemma map_map_comp_map_map_eq_tr₂ {D : Type*} [Category D] {E : Type*} [Category E]
    {E' : Type*} [Category E'] {K₁ K₂ : ℕᵒᵖ ⥤ D} (W : D ⥤ E) (H : E ⥤ E') {n m k : ℕ}
    {h : n ≤ m} {p : K₁.obj (op m) ⟶ K₂.obj (op k)} {q : K₂.obj (op k) ⟶ K₁.obj (op n)}
    (hpq : p ≫ q = InverseSequence.tr K₁ h) :
    H.map (W.map p) ≫ H.map (W.map q) = InverseSequence.tr ((K₁ ⋙ W) ⋙ H) h := by
  rw [tr_comp₂, ← H.map_comp, ← W.map_comp, hpq]

/-! ### Inverse limits and first derived inverse limits along a shifted pro-isomorphism -/

section Systems

variable {A : Type u} [CommRing A]

/-- **Dropping levels on the product of the terms of an inverse system of modules.** On the
factor indexed by `m` it is the projection to the factor indexed by `m + c`, followed by the
transition map of the system. -/
private def levelShiftMap (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c : ℕ) :
    (∏ᶜ fun n : ℕ ↦ E.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ E.obj (op n) :=
  Pi.lift fun m : ℕ ↦
    Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + c) ≫ InverseSequence.tr E (Nat.le_add_right m c)

/-- **The telescoping map of an inverse system of modules.** On the factor indexed by `m` it is
the sum, over `k < c`, of the projection to the factor indexed by `m + k` followed by the
transition map; it is a nullhomotopy of the difference between the identity and `levelShiftMap`
for the two-term complex whose cokernel computes `R¹lim`. -/
private def telescopeMap (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c : ℕ) :
    (∏ᶜ fun n : ℕ ↦ E.obj (op n)) ⟶ ∏ᶜ fun n : ℕ ↦ E.obj (op n) :=
  Pi.lift fun m : ℕ ↦ ∑ k ∈ Finset.range c,
    Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + k) ≫ InverseSequence.tr E (Nat.le_add_right m k)

/-- A projection followed by a transition map depends on the index only through its value. -/
private lemma pi_tr_congr (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) {i j k : ℕ} (hij : i = j)
    (hi : k ≤ i) (hj : k ≤ j) :
    Pi.π (fun n : ℕ ↦ E.obj (op n)) i ≫ InverseSequence.tr E hi =
      Pi.π (fun n : ℕ ↦ E.obj (op n)) j ≫ InverseSequence.tr E hj := by
  subst hij; rfl

/-- The components of `1 - shift` on the product of the terms of an inverse system. -/
private lemma moduleDifference_π (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (m : ℕ) :
    CompletionSequences.moduleDifference A E ≫ Pi.π (fun n : ℕ ↦ E.obj (op n)) m =
      Pi.π (fun n : ℕ ↦ E.obj (op n)) m -
        Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + 1) ≫ InverseSequence.tr E (Nat.le_succ m) :=
  Pi.lift_π _ m

/-- The components of the level-dropping map. -/
private lemma levelShiftMap_π (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c m : ℕ) :
    levelShiftMap E c ≫ Pi.π (fun n : ℕ ↦ E.obj (op n)) m =
      Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + c) ≫ InverseSequence.tr E (Nat.le_add_right m c) :=
  Pi.lift_π _ m

/-- The components of the telescoping map. -/
private lemma telescopeMap_π (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c m : ℕ) :
    telescopeMap E c ≫ Pi.π (fun n : ℕ ↦ E.obj (op n)) m =
      ∑ k ∈ Finset.range c,
        Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + k) ≫ InverseSequence.tr E (Nat.le_add_right m k) :=
  Pi.lift_π _ m

/-- **The telescoping identity.** Composing the telescoping map with `1 - shift` is the
difference between the identity and dropping `c` levels. -/
private lemma telescopeMap_comp_moduleDifference (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c : ℕ) :
    telescopeMap E c ≫ CompletionSequences.moduleDifference A E = 𝟙 _ - levelShiftMap E c := by
  refine Pi.hom_ext _ _ fun m ↦ ?_
  have hstep (k : ℕ) :
      (Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + 1 + k) ≫
          InverseSequence.tr E (Nat.le_add_right (m + 1) k)) ≫
          InverseSequence.tr E (Nat.le_succ m) =
        Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + (k + 1)) ≫
          InverseSequence.tr E (Nat.le_add_right m (k + 1)) := by
    rw [Category.assoc, InverseSequence.ProIso.tr_trans]
    exact pi_tr_congr E (by omega) _ _
  have hzero : Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + 0) ≫
      InverseSequence.tr E (Nat.le_add_right m 0) = Pi.π (fun n : ℕ ↦ E.obj (op n)) m := by
    rw [InverseSequence.ProIso.tr_refl]
    exact Category.comp_id _
  rw [Category.assoc, moduleDifference_π, Preadditive.comp_sub, telescopeMap_π,
    ← Category.assoc, telescopeMap_π, Preadditive.sub_comp, Category.id_comp, levelShiftMap_π,
    Preadditive.sum_comp, Finset.sum_congr rfl (fun k _ ↦ hstep k), ← Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun k ↦ Pi.π (fun n : ℕ ↦ E.obj (op n)) (m + k) ≫
      InverseSequence.tr E (Nat.le_add_right m k)) c, hzero]

/-- **Dropping finitely many levels does not change the first derived inverse limit.** -/
private lemma levelShiftMap_comp_cokernel_π (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (c : ℕ) :
    levelShiftMap E c ≫ cokernel.π (CompletionSequences.moduleDifference A E) =
      cokernel.π (CompletionSequences.moduleDifference A E) := by
  have key : levelShiftMap E c =
      𝟙 _ - telescopeMap E c ≫ CompletionSequences.moduleDifference A E := by
    rw [telescopeMap_comp_moduleDifference]; abel
  rw [key, Preadditive.sub_comp, Category.id_comp, Category.assoc, cokernel.condition,
    comp_zero, sub_zero]

/-- **Comparison of inverse limits along a shifted pro-isomorphism.** If two inverse systems are
related by a morphism of systems in one direction and by a morphism of systems shifted by `c`
levels in the other, whose two composites are the transition maps dropping `c` levels, then after
applying two functors ending in a category of modules the two systems have isomorphic inverse
limits. -/
private theorem nonempty_limit_iso_of_shifted
    {D : Type*} [Category D] {E : Type*} [Category E] (K₁ K₂ : ℕᵒᵖ ⥤ D) (c : ℕ)
    (fwd : ∀ m : ℕ, K₁.obj (op m) ⟶ K₂.obj (op m))
    (bwd : ∀ m : ℕ, K₂.obj (op (m + c)) ⟶ K₁.obj (op m))
    (hfwd : ∀ (m m' : ℕ) (h : m ≤ m'),
      InverseSequence.tr K₁ h ≫ fwd m = fwd m' ≫ InverseSequence.tr K₂ h)
    (hbwd : ∀ (m m' : ℕ) (h : m ≤ m'),
      InverseSequence.tr K₂ (Nat.add_le_add_right h c) ≫ bwd m = bwd m' ≫ InverseSequence.tr K₁ h)
    (hbf : ∀ m : ℕ, fwd (m + c) ≫ bwd m = InverseSequence.tr K₁ (Nat.le_add_right m c))
    (hfb : ∀ m : ℕ, bwd m ≫ fwd m = InverseSequence.tr K₂ (Nat.le_add_right m c))
    (W : D ⥤ E) (H : E ⥤ ModuleCat.{u} A) :
    Nonempty (limit ((K₁ ⋙ W) ⋙ H) ≅ limit ((K₂ ⋙ W) ⋙ H)) := by
  have hfwd' (m m' : ℕ) (h : m ≤ m') := tr_comp₂_comp_map_map W H (hfwd m m' h)
  have hbwd' (m m' : ℕ) (h : m ≤ m') := tr_comp₂_comp_map_map W H (hbwd m m' h)
  have hbf' (m : ℕ) := map_map_comp_map_map_eq_tr₂ W H (hbf m)
  have hfb' (m : ℕ) := map_map_comp_map_map_eq_tr₂ W H (hfb m)
  have lift (L₁ L₂ : ℕᵒᵖ ⥤ ModuleCat.{u} A) (s : ℕ)
      (g : ∀ m : ℕ, L₁.obj (op (m + s)) ⟶ L₂.obj (op m))
      (hg : ∀ (m m' : ℕ) (h : m ≤ m'),
        InverseSequence.tr L₁ (Nat.add_le_add_right h s) ≫ g m = g m' ≫ InverseSequence.tr L₂ h) :
      ∃ φ : limit L₁ ⟶ limit L₂,
        ∀ j, φ ≫ limit.π L₂ j = limit.π L₁ (op (j.unop + s)) ≫ g j.unop := by
    refine ⟨limit.lift L₂
      { pt := limit L₁
        π :=
          { app := fun j ↦ limit.π L₁ (op (j.unop + s)) ≫ g j.unop
            naturality := by
              intro j k g'
              have hjk : k.unop ≤ j.unop := leOfHom g'.unop
              have hg' : g' = (homOfLE hjk).op := Subsingleton.elim _ _
              subst hg'
              have key := hg _ _ hjk
              simp only [InverseSequence.tr] at key
              simp only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp]
              rw [Category.assoc, ← key, ← Category.assoc, limit.w] } },
      fun j ↦ limit.lift_π _ j⟩
  obtain ⟨u, hu⟩ := lift ((K₁ ⋙ W) ⋙ H) ((K₂ ⋙ W) ⋙ H) 0 (fun m ↦ H.map (W.map (fwd m))) hfwd'
  obtain ⟨v, hv⟩ := lift ((K₂ ⋙ W) ⋙ H) ((K₁ ⋙ W) ⋙ H) c (fun m ↦ H.map (W.map (bwd m))) hbwd'
  simp only [Nat.add_zero, op_unop] at hu
  refine ⟨u, v, ?_, ?_⟩
  · refine limit.hom_ext fun j ↦ ?_
    rw [Category.assoc, hv, ← Category.assoc, hu, Category.assoc, hbf', Category.id_comp]
    exact limit.w ((K₁ ⋙ W) ⋙ H) (homOfLE (Nat.le_add_right j.unop c)).op
  · refine limit.hom_ext fun j ↦ ?_
    rw [Category.assoc, hu, ← Category.assoc, hv, Category.assoc, hfb', Category.id_comp]
    exact limit.w ((K₂ ⋙ W) ⋙ H) (homOfLE (Nat.le_add_right j.unop c)).op

/-- **Comparison of first derived inverse limits along a shifted pro-isomorphism.** In the
situation of `nonempty_limit_iso_of_shifted` the cokernels of `1 - shift` on the products of the
terms are also isomorphic: the two induced maps on these cokernels are mutually inverse, because
their composites are the maps dropping `c` levels, which act as the identity. -/
private theorem nonempty_firstDerivedLimit_iso_of_shifted
    {D : Type*} [Category D] {E : Type*} [Category E] (K₁ K₂ : ℕᵒᵖ ⥤ D) (c : ℕ)
    (fwd : ∀ m : ℕ, K₁.obj (op m) ⟶ K₂.obj (op m))
    (bwd : ∀ m : ℕ, K₂.obj (op (m + c)) ⟶ K₁.obj (op m))
    (hfwd : ∀ (m m' : ℕ) (h : m ≤ m'),
      InverseSequence.tr K₁ h ≫ fwd m = fwd m' ≫ InverseSequence.tr K₂ h)
    (hbwd : ∀ (m m' : ℕ) (h : m ≤ m'),
      InverseSequence.tr K₂ (Nat.add_le_add_right h c) ≫ bwd m = bwd m' ≫ InverseSequence.tr K₁ h)
    (hbf : ∀ m : ℕ, fwd (m + c) ≫ bwd m = InverseSequence.tr K₁ (Nat.le_add_right m c))
    (hfb : ∀ m : ℕ, bwd m ≫ fwd m = InverseSequence.tr K₂ (Nat.le_add_right m c))
    (W : D ⥤ E) (H : E ⥤ ModuleCat.{u} A) :
    Nonempty (cokernel (CompletionSequences.moduleDifference A ((K₁ ⋙ W) ⋙ H)) ≅
      cokernel (CompletionSequences.moduleDifference A ((K₂ ⋙ W) ⋙ H))) := by
  have hfwd' (m m' : ℕ) (h : m ≤ m') := tr_comp₂_comp_map_map W H (hfwd m m' h)
  have hbwd' (m m' : ℕ) (h : m ≤ m') := tr_comp₂_comp_map_map W H (hbwd m m' h)
  have hbf' (m : ℕ) := map_map_comp_map_map_eq_tr₂ W H (hbf m)
  have hfb' (m : ℕ) := map_map_comp_map_map_eq_tr₂ W H (hfb m)
  let P : (∏ᶜ fun n : ℕ ↦ ((K₁ ⋙ W) ⋙ H).obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ ((K₂ ⋙ W) ⋙ H).obj (op n) :=
    Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ ((K₁ ⋙ W) ⋙ H).obj (op n)) n ≫ H.map (W.map (fwd n))
  let V : (∏ᶜ fun n : ℕ ↦ ((K₂ ⋙ W) ⋙ H).obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ ((K₁ ⋙ W) ⋙ H).obj (op n) :=
    Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ ((K₂ ⋙ W) ⋙ H).obj (op n)) (n + c) ≫ H.map (W.map (bwd n))
  have hPπ : ∀ n : ℕ, P ≫ Pi.π (fun n : ℕ ↦ ((K₂ ⋙ W) ⋙ H).obj (op n)) n =
      Pi.π (fun n : ℕ ↦ ((K₁ ⋙ W) ⋙ H).obj (op n)) n ≫ H.map (W.map (fwd n)) :=
    fun n ↦ Pi.lift_π _ n
  have hVπ : ∀ n : ℕ, V ≫ Pi.π (fun n : ℕ ↦ ((K₁ ⋙ W) ⋙ H).obj (op n)) n =
      Pi.π (fun n : ℕ ↦ ((K₂ ⋙ W) ⋙ H).obj (op n)) (n + c) ≫ H.map (W.map (bwd n)) :=
    fun n ↦ Pi.lift_π _ n
  have hP : CompletionSequences.moduleDifference A ((K₁ ⋙ W) ⋙ H) ≫ P =
      P ≫ CompletionSequences.moduleDifference A ((K₂ ⋙ W) ⋙ H) := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, hPπ, ← Category.assoc, moduleDifference_π, Preadditive.sub_comp,
      Category.assoc, hfwd' n (n + 1) (Nat.le_succ n), Category.assoc, moduleDifference_π,
      Preadditive.comp_sub, hPπ, ← Category.assoc, ← Category.assoc, hPπ]
  have hV : CompletionSequences.moduleDifference A ((K₂ ⋙ W) ⋙ H) ≫ V =
      V ≫ CompletionSequences.moduleDifference A ((K₁ ⋙ W) ⋙ H) := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, hVπ, ← Category.assoc, moduleDifference_π,
      pi_tr_congr ((K₂ ⋙ W) ⋙ H) (show n + c + 1 = n + 1 + c by omega) (Nat.le_succ (n + c))
        (Nat.add_le_add_right (Nat.le_succ n) c),
      Preadditive.sub_comp, Category.assoc, hbwd' n (n + 1) (Nat.le_succ n), Category.assoc,
      moduleDifference_π, Preadditive.comp_sub, hVπ, ← Category.assoc, ← Category.assoc, hVπ]
  have hPV : P ≫ V = levelShiftMap ((K₁ ⋙ W) ⋙ H) c := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, hVπ, ← Category.assoc, hPπ, Category.assoc, hbf', levelShiftMap_π]
  have hVP : V ≫ P = levelShiftMap ((K₂ ⋙ W) ⋙ H) c := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, hPπ, ← Category.assoc, hVπ, Category.assoc, hfb', levelShiftMap_π]
  refine ⟨cokernel.desc _
      (P ≫ cokernel.π (CompletionSequences.moduleDifference A ((K₂ ⋙ W) ⋙ H)))
      (by rw [← Category.assoc, hP, Category.assoc, cokernel.condition, comp_zero]),
    cokernel.desc _
      (V ≫ cokernel.π (CompletionSequences.moduleDifference A ((K₁ ⋙ W) ⋙ H)))
      (by rw [← Category.assoc, hV, Category.assoc, cokernel.condition, comp_zero]), ?_, ?_⟩
  · refine (cancel_epi (cokernel.π
      (CompletionSequences.moduleDifference A ((K₁ ⋙ W) ⋙ H)))).1 ?_
    rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc, ← Category.assoc,
      hPV, levelShiftMap_comp_cokernel_π, Category.comp_id]
  · refine (cancel_epi (cokernel.π
      (CompletionSequences.moduleDifference A ((K₂ ⋙ W) ⋙ H)))).1 ?_
    rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc, ← Category.assoc,
      hVP, levelShiftMap_comp_cokernel_π, Category.comp_id]

end Systems

/-! ### The Koszul tower and the quotient tower on a ringed space -/

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))

attribute [local instance] HasDerivedCategory.standard

/-- **The Koszul tower and the quotient tower are pro-isomorphic.** If the `f`-power torsion of
`ℱ` stabilizes, that is `ℱ[f^c] = ℱ[f^n]` for all `n ≥ c`, then the `f`-power Koszul tower
`ℱ ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)`, realized as the tower of two-term complexes
`ℱ --f^(n+1)--> ℱ`, is pro-isomorphic to the tower of honest quotients `ℱ/f^(n+1)ℱ`. -/
theorem nonempty_proIso_koszulTower_quotientTower (f : A)
    (ℱ : SheafOfModules.{u} (structureSheafRing X)) (hstab : Stabilizes ((baseSmul X ρ f).app ℱ)) :
    Nonempty
      (InverseSequence.ProIso (Ksys ((baseSmul X ρ f).app ℱ)) (Csys ((baseSmul X ρ f).app ℱ))) :=
  proIso_Ksys_Csys ((baseSmul X ρ f).app ℱ) hstab

/-- **The derived limits of the Koszul tower and of the quotient tower agree.** If the `f`-power
torsion of `ℱ` stabilizes then any derived limit of the `f`-power Koszul tower is isomorphic to
any derived limit of the tower of quotients `ℱ/f^(n+1)ℱ`. -/
theorem nonempty_iso_isDerivedLimit_koszulTower_quotientTower (f : A)
    (ℱ : SheafOfModules.{u} (structureSheafRing X)) (hstab : Stabilizes ((baseSmul X ρ f).app ℱ))
    (Ehat Fhat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hEhat : IsDerivedLimit (Ksys ((baseSmul X ρ f).app ℱ)) Ehat)
    (hFhat : IsDerivedLimit (Csys ((baseSmul X ρ f).app ℱ)) Fhat) :
    Nonempty (Ehat ≅ Fhat) := by
  obtain ⟨a⟩ := nonempty_proIso_koszulTower_quotientTower X ρ f ℱ hstab
  exact Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism _ _ _ _ hEhat hFhat a

/-- **Formal functions for a principal ideal along the quotient tower: the middle column.**
Let `(X, 𝒪_X)` be a ringed space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative
ring `A`, let `f ∈ A` and let `ℱ` be a sheaf of `𝒪_X`-modules whose `f`-power torsion stabilizes.
Let `ℱ^` be a derived limit of the tower of quotients `ℱ/f^(n+1)ℱ` and let `E^` be a derived limit
of the `f`-power Koszul tower. Then `E^ ≅ ℱ^`, and for every `p` the cohomology of `RΓ(X, ℱ^)`
over `A` sits in a short exact sequence

`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/f^(n+1)ℱ) ⟶ Hᵖ(X, ℱ^) ⟶ lim Hᵖ(X, ℱ/f^(n+1)ℱ) ⟶ 0`,

whose inclusion descends the connecting morphism of the Milnor triangle and whose projection is
characterized by the limit projections, and whose outer terms are isomorphic to the outer terms of
the corresponding sequence for the Koszul tower. -/
@[stacks 0H3E "the middle column of the diagram, transported to the quotient tower ℱ/fⁿℱ by
the pro-isomorphism of Tag 0H3D; its two maps normalized by the Milnor triangle of the quotient
tower itself"]
theorem exists_shortExact_homology_derivedSections_quotientTower (f : A)
    (ℱ : SheafOfModules.{u} (structureSheafRing X)) (hstab : Stabilizes ((baseSmul X ρ f).app ℱ))
    (Fhat Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hFhat : IsDerivedLimit (Csys ((baseSmul X ρ f).app ℱ)) Fhat)
    (hEhat : IsDerivedLimit (Ksys ((baseSmul X ρ f).app ℱ)) Ehat) :
    let F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      Csys ((baseSmul X ρ f).app ℱ) ⋙ derivedSectionsOver X ρ
    let G : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      Ksys ((baseSmul X ρ f).app ℱ) ⋙ derivedSectionsOver X ρ
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ F.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    Nonempty (Ehat ≅ Fhat) ∧
      ∃ (a : (derivedSectionsOver X ρ).obj Fhat ⟶ ∏ᶜ Y)
        (b : (∏ᶜ Y) ⟶ ((derivedSectionsOver X ρ).obj Fhat)⟦(1 : ℤ)⟧),
        let T := Triangle.mk a d b
        T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
          ∀ p : ℤ,
            let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) p
            let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p - 1)
            let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H
            let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H₁
            let P : ModuleCat.{u} A :=
              ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (op n)
            let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) n -
                Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) (n + 1) ≫
                  shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
            ∃ (e : H₁.obj (∏ᶜ Y) ≅ P)
              (i : cokernel δ ⟶ H.obj ((derivedSectionsOver X ρ).obj Fhat))
              (q : H.obj ((derivedSectionsOver X ρ).obj Fhat) ⟶ limit homologySystem)
              (w : i ≫ q = 0),
              e.hom = piComparison H₁ Y ∧
                cokernel.π δ ≫ i = e.inv ≫
                  DerivedCategory.HomologySequence.δ T (p - 1) p ∧
                (∀ n : ℕ, q ≫ limit.π homologySystem (op n) =
                  H.map a ≫ H.map (Pi.π Y n)) ∧
                (ShortComplex.mk i q w).ShortExact ∧
                Nonempty (limit homologySystem ≅ limit (G ⋙ H)) ∧
                Nonempty (cokernel δ ≅
                  CompletionSequences.firstDerivedLimit A (G ⋙ H₁)) := by
  obtain ⟨c, hc, hstab'⟩ := hstab
  obtain ⟨a, b, hT, hp⟩ := DerivedSectionsOverBase.exists_shortExact_homology_derivedSectionsOver
    X ρ (Csys ((baseSmul X ρ f).app ℱ)) Fhat hFhat
  refine ⟨nonempty_iso_isDerivedLimit_koszulTower_quotientTower X ρ f ℱ ⟨c, hc, hstab'⟩
      Ehat Fhat hEhat hFhat, a, b, hT, fun p ↦ ?_⟩
  obtain ⟨e, i, q, w, he, hi, hq, hse⟩ := hp p
  refine ⟨e, i, q, w, he, hi, hq, hse, ?_, ?_⟩
  · exact (nonempty_limit_iso_of_shifted (Ksys ((baseSmul X ρ f).app ℱ))
      (Csys ((baseSmul X ρ f).app ℱ)) c (Kproj ((baseSmul X ρ f).app ℱ))
      (Cinv ((baseSmul X ρ f).app ℱ) c hstab')
      (fun _ _ h ↦ Kproj_naturality ((baseSmul X ρ f).app ℱ) h)
      (fun _ _ h ↦ Cinv_naturality ((baseSmul X ρ f).app ℱ) c hstab' h)
      (Cinv_Kproj ((baseSmul X ρ f).app ℱ) c hstab')
      (Kproj_Cinv ((baseSmul X ρ f).app ℱ) c hstab')
      (derivedSectionsOver X ρ)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p)).map Iso.symm
  · exact (nonempty_firstDerivedLimit_iso_of_shifted (Ksys ((baseSmul X ρ f).app ℱ))
      (Csys ((baseSmul X ρ f).app ℱ)) c (Kproj ((baseSmul X ρ f).app ℱ))
      (Cinv ((baseSmul X ρ f).app ℱ) c hstab')
      (fun _ _ h ↦ Kproj_naturality ((baseSmul X ρ f).app ℱ) h)
      (fun _ _ h ↦ Cinv_naturality ((baseSmul X ρ f).app ℱ) c hstab' h)
      (Cinv_Kproj ((baseSmul X ρ f).app ℱ) c hstab')
      (Kproj_Cinv ((baseSmul X ρ f).app ℱ) c hstab')
      (derivedSectionsOver X ρ)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p - 1))).map Iso.symm

end Stacks.Cohomology.QuotientTowerFormalFunctions

end
