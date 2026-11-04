module

public import StacksFrontier.RingTheory.Koszul.Relations

/-!
# `IsH1Regular` transported along a ring isomorphism

`Koszul.IsH1Regular` depends only on the sequence up to isomorphism of the ambient ring: an
isomorphism `e : R ≃+* S` carries an `H₁`-regular sequence `f` to the `H₁`-regular sequence
`e ∘ f`. Four modules proved this privately; it lives here once.

## Main results

* `isH1Regular_map_ringEquiv`
-/

@[expose] public section

/-- An `H₁`-regular sequence stays `H₁`-regular after transport along a ring isomorphism. -/
public theorem isH1Regular_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {m : ℕ} (f : Fin m → R) (hf : Koszul.IsH1Regular f) :
    Koszul.IsH1Regular (fun i => e (f i)) := by
  rw [Koszul.isH1Regular_iff_forall] at hf ⊢
  intro a ha
  let b : Fin m → R := fun i => e.symm (a i)
  have hb : ∑ i, b i * f i = 0 := by
    apply e.injective
    simpa [b, map_sum, map_mul] using ha
  have hmem := hf b hb
  rw [Koszul.relSpan] at hmem ⊢
  have hmapped : (fun i => e (b i)) ∈
      Submodule.span S (Set.range fun (p : Fin m × Fin m) =>
        Koszul.trivRel (fun i => e (f i)) p.1 p.2) := by
    refine Submodule.span_induction (p := fun x _ => (fun i => e (x i)) ∈
      Submodule.span S (Set.range fun (p : Fin m × Fin m) =>
        Koszul.trivRel (fun i => e (f i)) p.1 p.2)) ?_ ?_ ?_ ?_ hmem
    · intro x hx
      obtain ⟨p, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨p, funext fun k => ?_⟩
      simp only [Koszul.trivRel_apply]
      split_ifs <;> simp
    · rw [show (fun i => e ((0 : Fin m → R) i)) = 0 by
        funext i
        simp]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [show (fun i => e ((x + y) i)) = (fun i => e (x i)) + (fun i => e (y i)) by
        funext i
        simp]
      exact add_mem hx hy
    · intro r x _ hx
      rw [show (fun i => e ((r • x) i)) = e r • (fun i => e (x i)) by
        funext i
        simp [smul_eq_mul]]
      exact Submodule.smul_mem _ (e r) hx
  simpa [b] using hmapped
end
