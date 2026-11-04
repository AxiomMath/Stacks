module

public import StacksFrontier.CategoryTheory.Abelian.InverseSystemProDominated
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# The Mittag-Leffler condition is a pro-invariant

The Mittag-Leffler condition of Stacks Tag 02N0 for an inverse system of modules depends only on
the pro-object the system represents: if `F` and `G` are pro-isomorphic inverse systems of
`A`-modules indexed by `ℕᵒᵖ` and `G` is Mittag-Leffler, then so is `F`.

This is what makes the condition usable through a comparison that is an isomorphism only up to a
shift of the index, which is the only form in which the comparisons of this repository come: the
Artin--Rees comparison of a tower of reductions with an adic quotient tower is a pro-isomorphism
and nothing better. `IsMittagLefflerCategorical.of_natIso` covers the degenerate case of a
genuine isomorphism of systems; the statements here are its pro version.

The refinement data of `InverseSequence.ProIso` is a pair of monotone reindexings `α, β` with
`m ≤ α m` and `m ≤ β m`, not a uniform shift `m ↦ m + c`, which is why
`isMittagLefflerCategorical_of_proDominated_of_monotone` is stated for monotone shifts.

## Main results

* `isMittagLefflerCategorical_of_proIso_of_surjective`: a system pro-isomorphic to one whose
  one-step transition maps are surjective is Mittag-Leffler. This is the form the Artin--Rees
  comparison with an adic quotient tower `n ↦ N/IⁿN` feeds.
* `IsMittagLefflerCategorical.of_proIso`: the pro-invariance itself, with no hypothesis on the
  transition maps of the comparison system beyond its own Mittag-Leffler condition.

## References

* [Stacks Project, Tag 02N0](https://stacks.math.columbia.edu/tag/02N0)
* [Stacks Project, Tag 0H3D](https://stacks.math.columbia.edu/tag/0H3D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite InverseSequence

universe u v

/-- **Mittag-Leffler through a pro-isomorphism with a system of surjective transitions.** If an
inverse system `F` of `A`-modules is pro-isomorphic to a system `G` whose one-step transition
maps are surjective, then `F` satisfies the Mittag-Leffler condition of Stacks Tag 02N0.

The refinement data of the pro-isomorphism is exactly the pro-domination data of
`isMittagLefflerCategorical_of_proDominated_of_monotone`: the backward maps `ψ` dominate `F` by
`G`, and the forward maps `φ` provide the factorisation of the transition map
`F_{α (β n)} ⟶ F_n`. -/
theorem isMittagLefflerCategorical_of_proIso_of_surjective {A : Type u} [Ring A]
    {F G : ℕᵒᵖ ⥤ ModuleCat.{v} A} (e : ProIso F G)
    (hG : ∀ n : ℕ, Function.Surjective (G.map (homOfLE (Nat.le_succ n)).op).hom) :
    IsMittagLefflerCategorical F :=
  isMittagLefflerCategorical_of_proDominated_of_monotone F G e.α e.β e.βmono
    (fun n => (e.βle n).trans (e.αle (e.β n))) hG e.ψ (fun _ _ h => e.ψnat h) e.φ e.ψφ

/-- **The Mittag-Leffler condition is a pro-invariant.** If the inverse systems `F` and `G` of
`A`-modules are pro-isomorphic and `G` satisfies the Mittag-Leffler condition of Stacks Tag
02N0, then so does `F`.

Fix a level `i` and let `N ≥ β i` be a level beyond which the transition images in `G_{β i}` are
all one submodule `S`. The claim is that the transition images in `F_i` are all `ψ_i(S)` from
level `α N` on. One inclusion is the factorisation
`F_k ⟶ F_{α N} ⟶ G_N ⟶ G_{β i} ⟶ F_i` of the transition map, assembled from the naturality of
`φ` and the identity `φ_{β i} ≫ ψ_i = tr F`; the other holds because an element of `S` is, `β k`
being at least `N`, the image of an element of `G_{β k}`, which the naturality of `ψ` carries to
an element of the transition image of `F_k` in `F_i`. -/
theorem IsMittagLefflerCategorical.of_proIso {A : Type u} [Ring A]
    {F G : ℕᵒᵖ ⥤ ModuleCat.{v} A} (e : ProIso F G) (hG : IsMittagLefflerCategorical G) :
    IsMittagLefflerCategorical F := by
  -- The refinement data, with the transition maps spelled as `F.map (homOfLE _).op`.
  have hφnat : ∀ {m m' : ℕ} (h : m ≤ m'),
      F.map (homOfLE (e.αmono h)).op ≫ e.φ m = e.φ m' ≫ G.map (homOfLE h).op :=
    fun h => e.φnat h
  have hψnat : ∀ {m m' : ℕ} (h : m ≤ m'),
      G.map (homOfLE (e.βmono h)).op ≫ e.ψ m = e.ψ m' ≫ F.map (homOfLE h).op :=
    fun h => e.ψnat h
  have hψφ : ∀ m : ℕ, e.φ (e.β m) ≫ e.ψ m =
      F.map (homOfLE ((e.βle m).trans (e.αle (e.β m)))).op :=
    fun m => e.ψφ m
  refine isMittagLefflerCategorical_of_forall_exists_range_eq F fun i => ?_
  obtain ⟨N, hβiN, hstab⟩ := hG.exists_range_eq (e.β i)
  have hiK : i ≤ e.α N := ((e.βle i).trans hβiN).trans (e.αle N)
  -- The transition map `F_{α N} ⟶ F_i` runs through `G_N ⟶ G_{β i}`.
  have hfac : e.φ N ≫ G.map (homOfLE hβiN).op ≫ e.ψ i = F.map (homOfLE hiK).op :=
    calc e.φ N ≫ G.map (homOfLE hβiN).op ≫ e.ψ i
        = (e.φ N ≫ G.map (homOfLE hβiN).op) ≫ e.ψ i := (Category.assoc _ _ _).symm
      _ = (F.map (homOfLE (e.αmono hβiN)).op ≫ e.φ (e.β i)) ≫ e.ψ i := by rw [hφnat hβiN]
      _ = F.map (homOfLE (e.αmono hβiN)).op ≫ e.φ (e.β i) ≫ e.ψ i := Category.assoc _ _ _
      _ = F.map (homOfLE (e.αmono hβiN)).op ≫
            F.map (homOfLE ((e.βle i).trans (e.αle (e.β i)))).op := by rw [hψφ i]
      _ = F.map (homOfLE hiK).op :=
          (inverseSystem_transition_comp F ((e.βle i).trans (e.αle (e.β i)))
            (e.αmono hβiN)).symm
  -- From level `α N` on, every transition image in `F_i` is the image of `S` under `ψ_i`.
  have key : ∀ (k : ℕ) (hk : e.α N ≤ k),
      LinearMap.range (F.map (homOfLE (hiK.trans hk)).op).hom =
        LinearMap.range (G.map (homOfLE hβiN).op ≫ e.ψ i).hom := by
    intro k hk
    have hchain : F.map (homOfLE (hiK.trans hk)).op =
        (F.map (homOfLE hk).op ≫ e.φ N) ≫ G.map (homOfLE hβiN).op ≫ e.ψ i :=
      (inverseSystem_transition_comp F hiK hk).trans
        ((congrArg (F.map (homOfLE hk).op ≫ ·) hfac).symm.trans
          (Category.assoc _ _ _).symm)
    refine le_antisymm ?_ ?_
    · rw [hchain, ModuleCat.hom_comp]
      exact LinearMap.range_comp_le_range _ _
    · rintro _ ⟨t, rfl⟩
      have hNβk : N ≤ e.β k := ((e.αle N).trans hk).trans (e.βle k)
      have hstab' : LinearMap.range (G.map (homOfLE (e.βmono (hiK.trans hk))).op).hom =
          LinearMap.range (G.map (homOfLE hβiN).op).hom := hstab (e.β k) hNβk
      obtain ⟨t', ht'⟩ : (G.map (homOfLE hβiN).op).hom t ∈
          LinearMap.range (G.map (homOfLE (e.βmono (hiK.trans hk))).op).hom := by
        rw [hstab']
        exact ⟨t, rfl⟩
      have hnat := congrArg (fun φ : G.obj (op (e.β k)) ⟶ F.obj (op i) => φ.hom t')
        (hψnat (hiK.trans hk))
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hnat ⊢
      rw [ht'] at hnat
      exact ⟨(e.ψ k).hom t', hnat.symm⟩
  exact ⟨e.α N, hiK, fun k hk => (key k hk).trans (key (e.α N) le_rfl).symm⟩

end
