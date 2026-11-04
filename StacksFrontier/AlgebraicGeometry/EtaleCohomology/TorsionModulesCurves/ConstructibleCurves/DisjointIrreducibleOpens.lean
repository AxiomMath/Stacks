module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.LocallyConstantOpens

/-!
# A dense disjoint union of irreducible opens on which a constructible sheaf is locally constant

Let `X` be a scheme whose underlying space is Noetherian and let `ℱ` be a constructible sheaf of
`Λ`-modules on `X_étale`. Then there are finitely many pairwise disjoint irreducible opens
`W₁, …, Wₙ` of `X`, with dense union, such that `ℱ|_{Wₐ}` is a finite type, locally constant
sheaf of `Λ`-modules for every `a`.

This is the second step of the proof of [Stacks, Tag 0GJI]: "there is a dense open `U ⊂ X` such
that `ℱ|_U` is a finite type, locally constant sheaf of `Λ`-modules … we may assume, after
shrinking `U`, that `U = U₁ ⨿ … ⨿ Uₙ` is a disjoint union of irreducible schemes."

## Main results

* `Stacks.EtaleCohomology.exists_disjoint_isIrreducible_opens_isFiniteTypeLocallyConstant` — the
  statement above.

## Implementation notes

The opens are cut out one irreducible component at a time. For a component `C` with generic point
`η`, `exists_isOpen_isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction` gives an open
`O ∋ η` such that `ℱ` is locally constant of finite type on every open of `O` inside `C`; the open
`W_C = O \ ⋃_{C' ≠ C} C'` is such an open. It contains `η`, which lies on no other component by
maximality of `C`, so the `W_C` have dense union, and two of them are disjoint because every point
of `W_C` lies on `C` and on no other component.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

/-- **A constructible sheaf is locally constant of finite type on a dense disjoint union of
irreducible opens.** Let `X` be a scheme with Noetherian underlying space and `ℱ` a constructible
sheaf of `Λ`-modules on `X_étale`. There are finitely many pairwise disjoint irreducible opens
`Wₐ` of `X` whose union is dense, such that each restriction `ℱ|_{Wₐ}` is a finite type, locally
constant sheaf of `Λ`-modules. -/
theorem exists_disjoint_isIrreducible_opens_isFiniteTypeLocallyConstant {X : Scheme.{u}}
    [NoetherianSpace X] (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (n : ℕ) (W : Fin n → X.Opens),
      Pairwise (fun a b => Disjoint (W a : Set X) (W b)) ∧ Dense (⋃ a, (W a : Set X)) ∧
      ∀ a, IsIrreducible (W a : Set X) ∧
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
          (W a).toScheme.smallEtaleTopology Λ
            ((etaleModuleRestriction.{u, r} Λ (W a).ι).obj F) := by
  have : Finite (irreducibleComponents X) := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let e : Fin (Nat.card (irreducibleComponents X)) ≃ irreducibleComponents X :=
    (Finite.equivFin _).symm
  set n := Nat.card (irreducibleComponents X)
  let C : Fin n → Set X := fun a => (e a : Set X)
  have hCirr : ∀ a, IsIrreducible (C a) := fun a => (e a).2.1
  have hCcl : ∀ a, IsClosed (C a) := fun a => isClosed_of_mem_irreducibleComponents _ (e a).2
  have hCmax : ∀ a b, C a ⊆ C b → a = b := fun a b h =>
    e.injective (Subtype.ext (h.antisymm ((e a).2.2 (hCirr b) h)))
  have hCcov : ∀ x : X, ∃ a, x ∈ C a := fun x => by
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.1
      ((sUnion_irreducibleComponents (X := X)).symm ▸ Set.mem_univ x)
    exact ⟨e.symm ⟨Z, hZ⟩, by simpa [C] using hxZ⟩
  let η : Fin n → X := fun a => (hCirr a).genericPoint
  have hη : ∀ a, closure {η a} = C a := fun a =>
    ((hCirr a).isGenericPoint_genericPoint (hCcl a)).def
  have hηC : ∀ a b, η a ∈ C b → a = b := fun a b h => hCmax a b <| by
    rw [← hη a]
    exact (hCcl b).closure_subset_iff.2 (Set.singleton_subset_iff.2 h)
  choose O hηO hO using fun a =>
    exists_isOpen_isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction Λ F hF (η a)
  let Oth : Fin n → Set X := fun a => ⋃ b ∈ ({a}ᶜ : Set (Fin n)), C b
  have hOth : ∀ a, IsClosed (Oth a) := fun a =>
    (Set.toFinite _).isClosed_biUnion fun b _ => hCcl b
  let W : Fin n → X.Opens := fun a => O a ⊓ ⟨(Oth a)ᶜ, (hOth a).isOpen_compl⟩
  have hWeq : ∀ a b x, x ∈ (W a : Set X) → x ∈ C b → b = a := fun a b x hx hb =>
    by_contra fun hab => hx.2 (Set.mem_biUnion hab hb)
  have hWC : ∀ a, (W a : Set X) ⊆ C a := fun a x hx =>
    (hCcov x).elim fun b hb => hWeq a b x hx hb ▸ hb
  have hηW : ∀ a, η a ∈ (W a : Set X) := fun a => by
    refine ⟨hηO a, fun h => ?_⟩
    obtain ⟨b, hb, hηb⟩ := Set.mem_iUnion₂.1 h
    exact hb (hηC a b hηb).symm
  refine ⟨n, W, fun a b hab => ?_, ?_, fun a => ⟨?_, ?_⟩⟩
  · exact Set.disjoint_left.2 fun x hxa hxb => hab (hWeq a b x hxa (hWC b hxb)).symm
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun x => ?_)
    obtain ⟨a, ha⟩ := hCcov x
    rw [← hη a] at ha
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_iUnion.2 ⟨a, hηW a⟩)) ha
  · exact ⟨⟨η a, hηW a⟩, (hCirr a).isPreirreducible.open_subset (W a).isOpen (hWC a)⟩
  · exact hO a (W a) inf_le_left ((hη a).symm ▸ hWC a)

end Stacks.EtaleCohomology

end
