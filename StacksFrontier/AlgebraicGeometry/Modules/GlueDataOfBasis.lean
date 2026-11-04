module

public import StacksFrontier.AlgebraicGeometry.Modules.BasisSectionExtension
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Glueing data for sheaves of modules from comparisons on a basis

A glueing datum of sheaves of modules (Stacks 00AM, in the form
`Stacks.SheafOfModules.OModuleGlueData.ofModules`) asks for the comparison of two members over an
*arbitrary* open of their overlap, together with naturality and the cocycle identity. A comparison
of quasi-coherent sheaves is in practice only available on *adapted* opens — in the case of the
relative dualizing module, opens which are simultaneously a principal open of either affine chart
and lie over a common principal open of the base.

This file converts the second kind of datum into the first. The adapted opens are presented as a
family `W : κ → S.Opens` together with a predicate `good : κ → ι → Prop` recording which members of
the cover an index is adapted to; the hypotheses are that the adapted opens form a basis of each
pairwise *and* each triple overlap, and that the given comparisons are compatible with restriction
and satisfy the cocycle identity on adapted opens only.

## Main results

* `Stacks.Modules.exists_transData_of_basis`: the comparison data in the shape
  `OModuleGlueData.ofModules` consumes, agreeing with the given comparisons on adapted opens.

## Implementation notes

`good` is a `Prop`, so a comparison may use `Classical.choice` to recover whatever presentation of
an adapted open it needs: proof irrelevance makes the result a function of the index alone, which
is exactly what is required for the comparisons at a single adapted open to share a target and so
to satisfy the cocycle identity there for free.

Both the pairwise and the triple basis hypotheses are needed, and they are genuinely different
requirements: naturality of the extended comparison is a statement about one pair, so a basis of
the pairwise overlap suffices for it, whereas the cocycle identity involves three members at once
and is proved by the separation lemma `Stacks.Modules.sectionsMap_eq_of_basis` on a basis of the
*triple* overlap — on which all three comparisons are simultaneously given by the data.

Opens are indexed as opens of `S`, so nothing here transports along an identification of opens.
The two spellings of a comparison of sections — `Γ(N i, V) ≃ₗ[Γ(S, V)] Γ(N j, V)` and the
`ModuleCat`-valued one that `ofModules` is stated with — are the same type by `rfl`, so no
conversion appears below.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u v

namespace Stacks.Modules

/-- **Glueing data from comparisons on a basis of adapted opens.** Given sheaves of modules
`N i` on a scheme `S`, a family of opens `U i`, and comparisons of the sections of `N i` and
`N j` over the opens `W k` adapted to both `i` and `j` which are compatible with restriction and
satisfy the cocycle identity, there is comparison data over every open of every overlap — i.e.
the `trans`, `trans_map` and `trans_trans` fields of
`Stacks.SheafOfModules.OModuleGlueData.ofModules` — agreeing with the given comparisons on the
adapted opens. -/
public theorem exists_transData_of_basis {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens)
    (N : ι → S.Modules) {κ : Type v} (W : κ → S.Opens) (good : κ → ι → Prop)
    (hWU : ∀ (k : κ) (i : ι), good k i → W k ≤ U i)
    (hpair : ∀ (i j : ι) (V : S.Opens), V ≤ U i ⊓ U j → ∀ x ∈ V,
      ∃ k, good k i ∧ good k j ∧ x ∈ W k ∧ W k ≤ V)
    (htriple : ∀ (i j m : ι) (V : S.Opens), V ≤ U i ⊓ U j ⊓ U m → ∀ x ∈ V,
      ∃ k, good k i ∧ good k j ∧ good k m ∧ x ∈ W k ∧ W k ≤ V)
    (e : ∀ (k : κ) (i j : ι), good k i → good k j → Γ(N i, W k) ≃ₗ[Γ(S, W k)] Γ(N j, W k))
    (hres : ∀ (k l : κ) (i j : ι) (hki : good k i) (hkj : good k j) (hli : good l i)
      (hlj : good l j) (h : W l ≤ W k) (s : Γ(N i, W k)),
      e l i j hli hlj ((N i).presheaf.map (homOfLE h).op s) =
        (N j).presheaf.map (homOfLE h).op (e k i j hki hkj s))
    (hcoc : ∀ (k : κ) (i j m : ι) (hi : good k i) (hj : good k j) (hm : good k m)
      (s : Γ(N i, W k)), e k j m hj hm (e k i j hi hj s) = e k i m hi hm s) :
    ∃ (t : ∀ (i j : ι) {V : S.Opens} (_hi : V ≤ U i) (_hj : V ≤ U j),
        (N i).val.obj (op V) ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))] (N j).val.obj (op V))
      (_tm : ∀ (i j : ι) {V V' : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (h : V' ≤ V)
        (s : ToType ((N i).val.obj (op V))),
        t i j (h.trans hi) (h.trans hj) ((N i).val.map (homOfLE h).op s)
          = (N j).val.map (homOfLE h).op (t i j hi hj s))
      (_tt : ∀ (i j m : ι) {V : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hm : V ≤ U m)
        (s : ToType ((N i).val.obj (op V))),
        t j m hj hm (t i j hi hj s) = t i m hi hm s),
      ∀ (k : κ) (i j : ι) (hki : good k i) (hkj : good k j) (s : Γ(N i, W k)),
        t i j (hWU k i hki) (hWU k j hkj) s = e k i j hki hkj s := by
  classical
  have key : ∀ i j : ι,
      ∃ E : ∀ V : S.Opens, V ≤ U i ⊓ U j → (Γ(N i, V) ≃ₗ[Γ(S, V)] Γ(N j, V)),
        (∀ (V V' : S.Opens) (hV : V ≤ U i ⊓ U j) (hV' : V' ≤ U i ⊓ U j) (h : V' ≤ V)
          (s : Γ(N i, V)),
          E V' hV' ((N i).presheaf.map (homOfLE h).op s) =
            (N j).presheaf.map (homOfLE h).op (E V hV s)) ∧
        (∀ (p : {k : κ // good k i ∧ good k j}) (hp : W p.1 ≤ U i ⊓ U j)
          (s : Γ(N i, W p.1)), E (W p.1) hp s = e p.1 i j p.2.1 p.2.2 s) := by
    intro i j
    refine Stacks.Modules.exists_sectionEquiv_of_basis (κ := {k : κ // good k i ∧ good k j})
      (N i) (N j) (U i ⊓ U j) (fun p => W p.1) (fun V hV x hx => ?_)
      (fun p => e p.1 i j p.2.1 p.2.2)
      (fun p q h s => hres p.1 q.1 i j p.2.1 p.2.2 q.2.1 q.2.2 h s)
    obtain ⟨k, hki, hkj, hxk, hkV⟩ := hpair i j V hV x hx
    exact ⟨⟨k, hki, hkj⟩, hxk, hkV⟩
  choose E hEnat hEbasis using key
  refine ⟨fun i j _ hi hj => E i j _ (le_inf hi hj), fun i j _ _ hi hj h s => ?_,
    fun i j m V hi hj hm s => ?_, fun k i j hki hkj s => hEbasis i j ⟨k, hki, hkj⟩ _ s⟩
  · exact hEnat i j _ _ (le_inf hi hj) (le_inf (h.trans hi) (h.trans hj)) h s
  · refine Stacks.Modules.sectionsMap_eq_of_basis (κ := {k : κ // good k i ∧ good k j ∧ good k m})
      (W := fun p => W p.1) (N i) (N m) (fun V' hV' x hx => ?_)
      (fun V' hV' s' => E j m V'
          (le_inf (hV'.trans (inf_le_left.trans inf_le_right)) (hV'.trans inf_le_right))
          (E i j V' (hV'.trans inf_le_left) s'))
      (fun V' hV' s' => E i m V'
          (le_inf (hV'.trans (inf_le_left.trans inf_le_left)) (hV'.trans inf_le_right)) s')
      (fun V' V'' hV' hV'' h s' => ?_) (fun V' V'' hV' hV'' h s' => ?_)
      (fun p hp s' => ?_) (le_inf (le_inf hi hj) hm) s
    · obtain ⟨k, h1, h2, h3, hxk, hkV⟩ := htriple i j m V' hV' x hx
      exact ⟨⟨k, h1, h2, h3⟩, hxk, hkV⟩
    · rw [hEnat i j _ _ (hV'.trans inf_le_left) (hV''.trans inf_le_left) h s',
        hEnat j m _ _ _ _ h (E i j V' (hV'.trans inf_le_left) s')]
    · rw [hEnat i m _ _ _ _ h s']
    · rw [hEbasis i j ⟨p.1, p.2.1, p.2.2.1⟩, hEbasis j m ⟨p.1, p.2.2.1, p.2.2.2⟩,
        hEbasis i m ⟨p.1, p.2.1, p.2.2.2⟩, hcoc]

end Stacks.Modules

end
