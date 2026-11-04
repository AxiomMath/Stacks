module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionInduction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IteratedChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme

/-!
# Powers of the first Chern class of a module pulled back from a low-dimensional scheme

Stacks 0FDX says that for `P` of finite type over the base, carrying an ample invertible module
and of dimension at most `g`, the product of `g + 1` first Chern classes of invertible modules on
`P` vanishes in `A^{g+1}(P)`; on every test scheme `u : H ⟶ P` this is the vanishing of
`c₁(u^*ℳ₀) ∩ ⋯ ∩ c₁(u^*ℳ_g) ∩ −`
(`Stacks.Chow.iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le`).

This file reads that at a single invertible module `𝒩` on `H` whose Picard class is pulled back
from `P`: if `[𝒩] = u^*[ℳ]` in `Pic(H)` then `c₁(𝒩)ⁿ ∩ α = 0` for every `n > g` and every class
`α` of `H`. This is the last step of Stacks 0FH9, where `𝒩 = f^*ℳ` with `f : Sⁿ(X) ⟶ Pic^n_{X/k}`
and `n > g = dim Pic^n_{X/k}`.

## Main results

* `Stacks.Chow.iteratedChernCapOnChow_replicate_eq_zero_of_pullbackPicardClass` — for `P`
  Noetherian with an ample module, on every class of `H`.
* `Stacks.Chow.iteratedChernCapOnChow_replicate_fundamental_eq_zero_of_flat` — for `u` flat of
  relative dimension `n - g`, on the fundamental class, with no hypothesis on `P` beyond
  `dim P ≤ g`.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-- Replacing an invertible module by an isomorphic one does not change its iterated cap. -/
private theorem iteratedChernCapOnChow_replicate_eq_pullback_of_pullbackPicardClass
    {H P : Scheme.{u}} (sH : H ⟶ C.S) [LocallyOfFiniteType sH] (u : H ⟶ P) (M : P.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (N : H.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible H.sheaf.obj H.ringCatSheaf.property N]
    (hNM : Stacks.SheafOfModules.pullbackPicardClass u M hM = H.picardClass N hN) (n : ℕ)
    (k : ℤ) (α : chowGroup C sH (k + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ)))
    (hc : k + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ) =
      k + ((List.ofFn fun _ : Fin n =>
        invCap C sH ((Scheme.Modules.pullback u).obj M)).length : ℤ)) :
    iteratedChernCapOnChow C sH (List.ofFn fun _ : Fin n => invCap C sH N) k α =
      iteratedChernCapOnChow C sH (List.ofFn fun _ : Fin n =>
        invCap C sH ((Scheme.Modules.pullback u).obj M)) k (chowGroupCast C sH hc α) := by
  obtain ⟨e⟩ := (H.picardClass_eq_iff _ _ _ _).1 hNM
  have e' : N ≅ (Scheme.Modules.pullback u).obj M := e.symm
  exact iteratedChernCapOnChow_congr_forall₂ C sH
    (forall₂_ofFn fun _ m z => invCap_capOnChow_congr C sH N _ e' m z) k _ _
    (chowGroupCast_heq C sH hc α).symm

/-- **`c₁(𝒩)ⁿ = 0` for `𝒩` pulled back from a scheme of dimension less than `n`.** Let `P` be
locally of finite type over the base, Noetherian, of topological dimension at most `g` and
carrying an ample invertible module, let `u : H ⟶ P` be a morphism over the base and `𝒩` an
invertible module on `H` with `[𝒩] = u^*[ℳ]` in `Pic(H)` for an invertible `ℳ` on `P`. Then for
every `n > g` and every `α ∈ A_{k+n}(H)`,

  `c₁(𝒩)ⁿ ∩ α = 0`   in `A_k(H)`. -/
theorem iteratedChernCapOnChow_replicate_eq_zero_of_pullbackPicardClass {H P : Scheme.{u}}
    (sH : H ⟶ C.S) [LocallyOfFiniteType sH] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    [IsNoetherian P] (A : P.Modules) [Stacks.Ample.IsInvertibleModule P A]
    (hA : Stacks.Ample.IsAmple P A) (g : ℕ) (hdim : topologicalKrullDim P ≤ (g : WithBot ℕ∞))
    (u : H ⟶ P) [LocallyOfFiniteType u] (hu : u ≫ sP = sH) (M : P.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (N : H.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible H.sheaf.obj H.ringCatSheaf.property N]
    (hNM : Stacks.SheafOfModules.pullbackPicardClass u M hM = H.picardClass N hN) {n : ℕ}
    (hn : g < n) (k : ℤ)
    (α : chowGroup C sH (k + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ))) :
    iteratedChernCapOnChow C sH (List.ofFn fun _ : Fin n => invCap C sH N) k α = 0 := by
  have hc : k + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ) =
      k + ((List.ofFn fun _ : Fin n =>
        invCap C sH ((Scheme.Modules.pullback u).obj M)).length : ℤ) := by
    simp only [List.length_ofFn]
  rw [iteratedChernCapOnChow_replicate_eq_pullback_of_pullbackPicardClass C sH u M N hNM n k α hc]
  set O := invCap C sH ((Scheme.Modules.pullback u).obj M)
  have hsplit : (List.ofFn fun _ : Fin n => O) =
      List.replicate (n - (g + 1)) O ++ List.ofFn fun _ : Fin (g + 1) => O := by
    rw [List.ofFn_const, List.ofFn_const, ← List.replicate_add, Nat.sub_add_cancel hn]
  set β := chowGroupCast C sH hc α
  have e3 : k + ((List.ofFn fun _ : Fin n => O).length : ℤ) =
      k + ((List.replicate (n - (g + 1)) O ++ List.ofFn fun _ : Fin (g + 1) => O).length : ℤ) := by
    simp only [List.length_append, List.length_replicate, List.length_ofFn]; omega
  have e4 : k + ((List.replicate (n - (g + 1)) O ++
        List.ofFn fun _ : Fin (g + 1) => O).length : ℤ) =
      k + ((List.replicate (n - (g + 1)) O).length : ℤ) +
        ((List.ofFn fun _ : Fin (g + 1) => O).length : ℤ) := by
    simp only [List.length_append, Nat.cast_add]; ring
  rw [chowGroup_eq_of_heq C sH (iteratedChernCapOnChow_heq_of_eq C sH hsplit k
      (chowGroupCast_heq C sH e3 β).symm),
    iteratedChernCapOnChow_append C sH _ _ k _ (chowGroupCast C sH e4 _)
      (chowGroupCast_heq C sH e4 _).symm,
    iteratedChernCapOnChow_ofFn_eq_zero_of_topologicalKrullDim_le C g sP A hA hdim
      (fun _ => M) u sH hu _ _, map_zero]

/-- **`c₁(𝒩)ⁿ ∩ [H] = 0` for `𝒩` pulled back along a flat morphism to a scheme of
delta-dimension less than `n`.** The form of
`Stacks.Chow.iteratedChernCapOnChow_replicate_fundamental_eq_zero_of_flat` with the bound on `P`
given on its delta-dimension. Let the base be Jacobson with dimension function vanishing at
closed points (for instance the spectrum of a field), let `P` be locally of finite type over it
of delta-dimension at most `g`, and let `u : H ⟶ P` be flat of relative dimension `r` over
the base, with `g + r = n` and `g < n`. If `𝒩` on `H` has `[𝒩] = u^*[ℳ]` in `Pic(H)`, then

  `c₁(𝒩)ⁿ ∩ [H]_n = 0`   in `A_0(H)`.

Indeed `[H]_n = u^*[P]_g`, so `c₁(𝒩)ⁿ ∩ [H] = u^*(c₁(ℳ)ⁿ ∩ [P]_g)` by Stacks 02SS, and
`c₁(ℳ)ⁿ ∩ [P]_g` lies in `A_{-r}(P) = 0`. No ampleness and no Noetherian hypothesis on `P` is
needed. -/
theorem iteratedChernCapOnChow_replicate_fundamental_eq_zero_of_flat_of_schemeDeltaDimension_le
    [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) {H P : Scheme.{u}}
    (sH : H ⟶ C.S) [LocallyOfFiniteType sH] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (g r n : ℕ) (hP' : schemeDeltaDimension C sP ≤ ((g : ℤ) : EInt)) (hgr : g + r = n)
    (hn : g < n) (u : H ⟶ P) [LocallyOfFiniteType u] [Flat u] (hu : u ≫ sP = sH)
    (hrel : AlgebraicGeometry.RelativeDimension u r) (M : P.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (N : H.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible H.sheaf.obj H.ringCatSheaf.property N]
    (hNM : Stacks.SheafOfModules.pullbackPicardClass u M hM = H.picardClass N hN) :
    iteratedChernCapOnChow C sH (List.ofFn fun _ : Fin n => invCap C sH N) 0
      (fundamentalChowClass C sH (0 + ((List.ofFn fun _ : Fin n =>
        invCap C sH N).length : ℤ))) = 0 := by
  have hc : (0 : ℤ) + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ) =
      0 + ((List.ofFn fun _ : Fin n =>
        invCap C sH ((Scheme.Modules.pullback u).obj M)).length : ℤ) := by
    simp only [List.length_ofFn]
  rw [iteratedChernCapOnChow_replicate_eq_pullback_of_pullbackPicardClass C sH u M N hNM n 0 _ hc]
  -- `u^*` of the iterated cap of `ℳ` on `[P]`
  have hxlen : (-(r : ℤ)) + ((List.ofFn fun _ : Fin n => invCap C sP M).length : ℤ) = g := by
    simp only [List.length_ofFn]; omega
  have key := flatPullbackChowOfRelativeDimension_iteratedChernCapOnChow C sH sP u hu r hrel
    (fun _ : Fin n => M) (-(r : ℤ)) (chowGroupCast C sP hxlen.symm (fundamentalChowClass C sP g))
    (chowGroupCast C sH (by simp only [List.length_ofFn]; omega)
      (fundamentalChowClass C sH (0 + ((List.ofFn fun _ : Fin n =>
        invCap C sH ((Scheme.Modules.pullback u).obj M)).length : ℤ))))
    (by
      refine HEq.trans ?_ (chowGroupCast_heq C sH _ _).symm
      refine (flatPullbackChowOfRelativeDimension_heq C sH sP u hu r hrel hxlen
        (chowGroupCast_heq C sP hxlen.symm _)).trans ?_
      rw [flatPullbackChowOfRelativeDimension_fundamentalChowClass C sH sP u hu r hrel g hP']
      rw [show (g : ℤ) + r = 0 + ((List.ofFn fun _ : Fin n =>
        invCap C sH ((Scheme.Modules.pullback u).obj M)).length : ℤ) by
          simp only [List.length_ofFn]; omega])
  rw [chowGroup_eq_zero_of_neg C hδ sP (k := -(r : ℤ)) (by omega)
    (iteratedChernCapOnChow C sP _ _ _), map_zero] at key
  refine chowGroup_eq_of_heq C sH (HEq.trans ?_ (heq_of_eq key.symm |>.trans ?_))
  · refine iteratedChernCapOnChow_heq C sH _ (by omega) ?_
    refine (chowGroupCast_heq C sH hc _).trans ?_
    refine HEq.trans ?_ (chowGroupCast_heq C sH _ _).symm
    rw [show (0 : ℤ) + ((List.ofFn fun _ : Fin n => invCap C sH N).length : ℤ) =
      0 + ((List.ofFn fun _ : Fin n =>
        invCap C sH ((Scheme.Modules.pullback u).obj M)).length : ℤ) from hc]
  · have : (-(r : ℤ)) + r = 0 := by omega
    rw [this]

/-- **`c₁(𝒩)ⁿ ∩ [H] = 0` for `𝒩` pulled back along a flat morphism to a scheme of dimension
less than `n`.** Let the base be Jacobson with dimension function vanishing at closed points
(for instance the spectrum of a field), let `P` be locally of finite type over it of
topological dimension at most `g`, and let `u : H ⟶ P` be flat of relative dimension `r` over
the base, with `g + r = n` and `g < n`. If `𝒩` on `H` has `[𝒩] = u^*[ℳ]` in `Pic(H)`, then

  `c₁(𝒩)ⁿ ∩ [H]_n = 0`   in `A_0(H)`.

Indeed `[H]_n = u^*[P]_g`, so `c₁(𝒩)ⁿ ∩ [H] = u^*(c₁(ℳ)ⁿ ∩ [P]_g)` by Stacks 02SS, and
`c₁(ℳ)ⁿ ∩ [P]_g` lies in `A_{-r}(P) = 0`. No ampleness and no Noetherian hypothesis on `P` is
needed. -/
theorem iteratedChernCapOnChow_replicate_fundamental_eq_zero_of_flat [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) {H P : Scheme.{u}}
    (sH : H ⟶ C.S) [LocallyOfFiniteType sH] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (g r n : ℕ) (hdim : topologicalKrullDim P ≤ (g : WithBot ℕ∞)) (hgr : g + r = n)
    (hn : g < n) (u : H ⟶ P) [LocallyOfFiniteType u] [Flat u] (hu : u ≫ sP = sH)
    (hrel : AlgebraicGeometry.RelativeDimension u r) (M : P.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (N : H.Modules)
    [hN : AlgebraicGeometry.SheafOfModules.IsInvertible H.sheaf.obj H.ringCatSheaf.property N]
    (hNM : Stacks.SheafOfModules.pullbackPicardClass u M hM = H.picardClass N hN) :
    iteratedChernCapOnChow C sH (List.ofFn fun _ : Fin n => invCap C sH N) 0
      (fundamentalChowClass C sH (0 + ((List.ofFn fun _ : Fin n =>
        invCap C sH N).length : ℤ))) = 0 := by
  -- `δ`-dimension of `P`
  have hP : schemeDeltaDimension C (𝟙 P ≫ sP) ≤ ((g : ℤ) : EInt) :=
    schemeDeltaDimension_le_of_forall_relativeDimension_le C sP (𝟙 P) fun p =>
      relativeDimension_le_of_topologicalKrullDim_le C hδ sP (T := Set.univ) isClosed_univ
        (by rwa [topologicalKrullDim_univ]) (Set.mem_univ _)
  have hP' : schemeDeltaDimension C sP ≤ ((g : ℤ) : EInt) := by
    have : ∀ (a b : P ⟶ C.S) [LocallyOfFiniteType a] [LocallyOfFiniteType b], a = b →
        schemeDeltaDimension C a = schemeDeltaDimension C b := by
      rintro a b _ _ rfl; rfl
    exact (this _ _ (Category.id_comp sP)).symm.trans_le hP
  exact iteratedChernCapOnChow_replicate_fundamental_eq_zero_of_flat_of_schemeDeltaDimension_le C
    hδ sH sP g r n hP' hgr hn u hu hrel M N hNM

end Stacks.Chow

end
