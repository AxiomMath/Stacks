module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodModules

/-!
# Reading the neighbourhood comparison through a change of the inverse system

This file studies the comparison `colim_W Γ(W, E) ⟶ lim_n Γ(Y_n, E|_{Y_n})` of
`Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete` with its inverse-limit side replaced
by an arbitrary inverse system `(B n, τ)` together with termwise maps `β n` out of the sections on
the `n`-th term. If every `β n` is bijective and the `β n` commute with the transition maps, the
two comparisons are equivalent. The comparison also transports along a change of the tower whose
opens containing the support are cofinal.

## Main definitions

* `Stacks.Algebraization.InfinitesimalTower.IsSectionsCompleteVia`: the comparison read through
  termwise maps into another inverse system.

## Main results

* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.via`: a bijective,
  transition-compatible change of the inverse system carries `IsSectionsComplete` to
  `IsSectionsCompleteVia`.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsCompleteVia.isSectionsComplete`: conversely,
  `IsSectionsCompleteVia` implies `IsSectionsComplete` for such a change.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.ofTowerMap`: the comparison
  transports along a change of the tower, through a cofinal order embedding of the opens containing
  the support.

## Implementation notes

The maps `β n` are not asked to be additive, and `(B n, τ)` is not asked to be a functor: only the
compatibility `β n ∘ (transition) = τ ∘ β m` for `n ≤ m` is assumed.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization.InfinitesimalTower

variable {Z : Scheme.{u}} (T : InfinitesimalTower Z) (E : Z.Modules)

/-- The comparison `colim_W Γ(W, E) ⟶ lim_n B n`, where `(B n, τ)` is an inverse system receiving
termwise maps `β n` from the sections of `E` on the terms of the tower. -/
public structure IsSectionsCompleteVia (B : ℕ → Type u)
    (β : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤) → B n)
    (τ : ∀ (n m : ℕ), n ≤ m → B m → B n) : Prop where
  /-- Every compatible family in the inverse system comes from a section over some open
  containing the support. -/
  exists_section : ∀ b : ∀ n : ℕ, B n, (∀ (n m : ℕ) (h : n ≤ m), τ n m h (b m) = b n) →
      ∃ (W : Z.Opens) (hW : T.support ⊆ W) (t : Γ(E, W)),
        ∀ n : ℕ, β n (T.sectionsAt E hW n t) = b n
  /-- Two sections inducing the same family in the inverse system agree on a smaller open. -/
  eq_of_eq : ∀ (W W' : Z.Opens) (hW : T.support ⊆ W) (hW' : T.support ⊆ W')
      (t : Γ(E, W)) (u : Γ(E, W')),
      (∀ n : ℕ, β n (T.sectionsAt E hW n t) = β n (T.sectionsAt E hW' n u)) →
      ∃ (W'' : Z.Opens) (_ : T.support ⊆ W'') (h₁ : W'' ≤ W) (h₂ : W'' ≤ W'),
        E.presheaf.map (homOfLE h₁).op t = E.presheaf.map (homOfLE h₂).op u

variable {B : ℕ → Type u}
  {β : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤) → B n}
  {τ : ∀ (n m : ℕ), n ≤ m → B m → B n}

/-- A bijective, transition-compatible change of the inverse system carries the comparison to the
comparison read through it. -/
public theorem IsSectionsComplete.via (hβ : ∀ n : ℕ, Function.Bijective (β n))
    (hcompat : ∀ (n m : ℕ) (h : n ≤ m) (x : Γ((Scheme.Modules.pullback (T.obj m).hom).obj E, ⊤)),
      β n (pullbackSectionsMap E (T.trans n m h) x) = τ n m h (β m x))
    (hE : T.IsSectionsComplete E) : T.IsSectionsCompleteVia E B β τ where
  exists_section := by
    intro b hb
    obtain ⟨W, hW, t, ht⟩ := hE.exists_section (fun n => Function.surjInv (hβ n).2 (b n))
      (fun n m h => (hβ n).1 (by
        rw [hcompat n m h, Function.surjInv_eq (hβ m).2, Function.surjInv_eq (hβ n).2, hb n m h]))
    exact ⟨W, hW, t, fun n => by rw [ht n, Function.surjInv_eq (hβ n).2]⟩
  eq_of_eq := fun W W' hW hW' t u htu =>
    hE.eq_of_sectionsAt_eq W W' hW hW' t u fun n => (hβ n).1 (htu n)

/-- The comparison read through a bijective, transition-compatible change of the inverse system is
the comparison itself. -/
public theorem IsSectionsCompleteVia.isSectionsComplete (hβ : ∀ n : ℕ, Function.Bijective (β n))
    (hcompat : ∀ (n m : ℕ) (h : n ≤ m) (x : Γ((Scheme.Modules.pullback (T.obj m).hom).obj E, ⊤)),
      β n (pullbackSectionsMap E (T.trans n m h) x) = τ n m h (β m x))
    (hE : T.IsSectionsCompleteVia E B β τ) : T.IsSectionsComplete E where
  exists_section := fun s hs => by
    obtain ⟨W, hW, t, ht⟩ := hE.exists_section (fun n => β n (s n)) (fun n m h =>
      (hcompat n m h (s m)).symm.trans (congrArg (β n) (hs n m h)))
    exact ⟨W, hW, t, fun n => (hβ n).1 (ht n)⟩
  eq_of_sectionsAt_eq := fun W W' hW hW' t u htu =>
    hE.eq_of_eq W W' hW hW' t u fun n => congrArg (β n) (htu n)

/-! ### Changing the tower -/

/-- Restriction along a chain of two inclusions of opens. -/
public theorem presheaf_map_homOfLE_trans {Z : Scheme.{u}} (M : Z.Modules) {A B C : Z.Opens}
    (hAB : A ≤ B) (hBC : B ≤ C) (x : Γ(M, C)) :
    M.presheaf.map (homOfLE hAB).op (M.presheaf.map (homOfLE hBC).op x) =
      M.presheaf.map (homOfLE (hAB.trans hBC)).op x :=
  (ConcreteCategory.comp_apply _ _ x).symm.trans
    (ConcreteCategory.congr_hom
      ((M.presheaf.map_comp (homOfLE hBC).op (homOfLE hAB).op).symm.trans
        (congrArg M.presheaf.map (Subsingleton.elim _ _))) x)

/-- Let `S` be a tower over `Z` and `T`
a tower over `Z'`, let `E` and `E'` be modules on `Z` and `Z'`, and suppose the opens of `Z'`
containing the support of `T` are carried to opens of `Z` containing the support of `S` by an
order embedding `im` whose image is cofinal. If the sections of `E'` over `W` are identified with
those of `E` over `im W`, compatibly with shrinking the open, and the sections of `E'` on the
terms of `T` with those of `E` on the terms of `S`, compatibly with the transition maps, and if
the two identifications intertwine the two comparisons, then the comparison for `E` carries over
to the comparison for `E'`. -/
public theorem IsSectionsComplete.ofTowerMap {Z Z' : Scheme.{u}} (S : InfinitesimalTower Z)
    (T : InfinitesimalTower Z') (E : Z.Modules) (E' : Z'.Modules)
    (im : Z'.Opens → Z.Opens)
    (himono : ∀ {W W' : Z'.Opens}, W' ≤ W → im W' ≤ im W)
    (hirefl : ∀ {W W' : Z'.Opens}, im W' ≤ im W → W' ≤ W)
    (hisupp : ∀ (W : Z'.Opens), T.support ⊆ W → S.support ⊆ im W)
    (hcofinal : ∀ U : Z.Opens, S.support ⊆ U →
      ∃ (W : Z'.Opens) (_ : T.support ⊆ W), im W ≤ U)
    (γ : ∀ (W : Z'.Opens), T.support ⊆ W → Γ(E', W) → Γ(E, im W))
    (hγ : ∀ (W : Z'.Opens) (hW : T.support ⊆ W), Function.Bijective (γ W hW))
    (hγres : ∀ (W W' : Z'.Opens) (hW : T.support ⊆ W) (hW' : T.support ⊆ W') (h : W' ≤ W)
      (t : Γ(E', W)),
      γ W' hW' (E'.presheaf.map (homOfLE h).op t) =
        E.presheaf.map (homOfLE (himono h)).op (γ W hW t))
    (δ : ∀ n : ℕ, Γ((Scheme.Modules.pullback (T.obj n).hom).obj E', ⊤) →
      Γ((Scheme.Modules.pullback (S.obj n).hom).obj E, ⊤))
    (hδ : ∀ n : ℕ, Function.Bijective (δ n))
    (hδtrans : ∀ (n m : ℕ) (h : n ≤ m)
      (x : Γ((Scheme.Modules.pullback (T.obj m).hom).obj E', ⊤)),
      δ n (pullbackSectionsMap E' (T.trans n m h) x) =
        pullbackSectionsMap E (S.trans n m h) (δ m x))
    (hcompat : ∀ (W : Z'.Opens) (hW : T.support ⊆ W) (n : ℕ) (t : Γ(E', W)),
      δ n (T.sectionsAt E' hW n t) = S.sectionsAt E (hisupp W hW) n (γ W hW t))
    (hS : S.IsSectionsComplete E) : T.IsSectionsComplete E' where
  exists_section := by
    intro s hs
    obtain ⟨U, hU, t, ht⟩ := hS.exists_section (fun n => δ n (s n))
      (fun n m h => (hδtrans n m h (s m)).symm.trans (congrArg (δ n) (hs n m h)))
    obtain ⟨W, hW, hle⟩ := hcofinal U hU
    refine ⟨W, hW, Function.surjInv (hγ W hW).2
      (E.presheaf.map (homOfLE hle).op t), fun n => ?_⟩
    refine (hδ n).1 ?_
    rw [hcompat W hW n _, Function.surjInv_eq (hγ W hW).2 _,
      S.sectionsAt_restrict E hle hU (hisupp W hW) n t, ht n]
  eq_of_sectionsAt_eq := by
    intro W W' hW hW' t u htu
    obtain ⟨U'', hU'', h₁, h₂, hres⟩ := hS.eq_of_sectionsAt_eq (im W) (im W')
      (hisupp W hW) (hisupp W' hW') (γ W hW t) (γ W' hW' u)
      (fun n => (hcompat W hW n t).symm.trans ((congrArg (δ n) (htu n)).trans
        (hcompat W' hW' n u)))
    obtain ⟨W'', hW'', hle⟩ := hcofinal U'' hU''
    refine ⟨W'', hW'', hirefl (hle.trans h₁), hirefl (hle.trans h₂), (hγ W'' hW'').1 ?_⟩
    rw [hγres W W'' hW hW'' (hirefl (hle.trans h₁)) t,
      hγres W' W'' hW' hW'' (hirefl (hle.trans h₂)) u,
      ← presheaf_map_homOfLE_trans E hle h₁ (γ W hW t),
      ← presheaf_map_homOfLE_trans E hle h₂ (γ W' hW' u), hres]

end Stacks.Algebraization.InfinitesimalTower

end
