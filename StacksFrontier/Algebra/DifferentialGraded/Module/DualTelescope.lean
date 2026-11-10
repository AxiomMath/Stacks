module

public import StacksFrontier.Algebra.DifferentialGraded.Module.ProductHomotopy
public import StacksCore.Tactic.StacksAttribute

/-! # The telescope of a complete filtration of a differential graded module

Let `(A, d)` be a differential graded algebra and let `I` be a right differential graded
`A`-module presented as the limit of a tower of quotients `⋯ → Q 1 → Q 0` whose transition maps
are admissible epimorphisms — which is what conditions (1) and (2) of property (I) provide, with
`Q i = I / Fᵢ I`. This file proves that

`0 → I → ∏ᵢ Q i → ∏ᵢ Q i → 0`

is an admissible short exact sequence of differential graded `A`-modules, the first map being the
family of quotient maps and the second the identity minus the map induced by the transitions.
This is Stacks Tag 09KR, the dual of the telescope of Tag 09KL.

## Main results

* `DifferentialGradedModule.exists_isAdmissibleShortExact_telescope`: Stacks Tag 09KR.

## Implementation notes

*Everything is presented as data.* The quotients `Q i` and the product `P` of them are taken as
data together with the properties that characterize them — for the tower, compatibility with the
quotient maps, separatedness and completeness; for the product, joint injectivity and degreewise
joint surjectivity of the projections — rather than being constructed. This keeps the statement
reusable: any consumer holding a product of the tower can apply it, whether that product came
from `DifferentialGradedModule.product` or from elsewhere. For the tower it is a convenience,
its canonical construction as a family of cokernels carrying no information this statement uses.

The named product it is instantiated at is `DifferentialGradedModule.uliftProduct`
(`Module/Product.lean`), which is what gives the 09KR specialization in
`Module/DualTelescopeProduct.lean`. The two maps of the sequence are likewise produced rather than
named, each with the equation that pins it down, since both are the lifts into the product
supplied by `DifferentialGradedModule.exists_homLift`.

*Why the sequence is exact on the right.* Surjectivity of the second map is not a formal
consequence of anything about the tower; it is produced by the same recursion that produces the
graded splitting, and it is where the transitions being *admissible* epimorphisms is used. Given
`r` in the product one solves `qᵢ - tᵢ(q_{i+1}) = rᵢ` by setting `q₀ = 0` and lifting
`qᵢ - rᵢ` through the chosen graded section of `tᵢ`; the resulting `q` depends `A`-linearly on
`r` and preserves degrees, because each section does, so it is a graded section of the second
map and in particular a right inverse.

*Why the sequence is exact on the left and in the middle.* Injectivity of the first map is
separatedness. An element of the product killed by the second map is a compatible family, and
completeness — used degreewise, the limit being formed in differential graded modules and hence
degreewise — presents it as the image of an element of `I`. The graded retraction of the first
map is then `α⁻¹ ∘ (id - s ∘ β)`, which lands in the image of `α` because `β` kills it, and is
graded because an injective homomorphism reflects homogeneity.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following the Stacks Tag 09JJ formalization.

## References

* [Stacks Project, Tag 09KR](https://stacks.math.columbia.edu/tag/09KR), and
  [Tag 09KL](https://stacks.math.columbia.edu/tag/09KL), of which it is the dual.
-/

@[expose] public section

open CategoryTheory MulOpposite

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-- **Stacks 09KR.** Let `I` be the limit of a tower of quotients `p i : I ⟶ Q i` with
transition maps `t i : Q (i + 1) ⟶ Q i` that are admissible epimorphisms, and let `P` with its
projections `π i` be the product of the `Q i`. Then the family of quotient maps and the identity
minus the map induced by the transitions form an admissible short exact sequence
`0 → I → P → P → 0`.

This deliberately carries **no** `@[stacks 09KR]` attribute: it takes the product `P` and its
projections as data, together with the properties characterising them, whereas Stacks 09KR
asserts that the sequence `0 → I → ∏ I/F_iI → ∏ I/F_iI → 0` *exists*. The tag therefore belongs
on the specialization at a named product, which is
`DifferentialGradedModule.exists_isAdmissibleShortExact_uliftProduct`
(`Module/DualTelescopeProduct.lean`), obtained from this theorem by instantiating the data at
`DifferentialGradedModule.uliftProduct` (`Module/Product.lean`).

This general form is kept because it is the reusable one: a consumer that already has a product
in hand — 09KU's totalization, for instance — can apply it directly without routing through the
`ULift` layer. -/
theorem exists_isAdmissibleShortExact_telescope {I P : DifferentialGradedModule A}
    (Q : ℕ → DifferentialGradedModule A) (p : ∀ i, I ⟶ Q i) (t : ∀ i, Q (i + 1) ⟶ Q i)
    (π : ∀ i, P ⟶ Q i)
    (hp : ∀ (i : ℕ) (x : I.M), (t i).toFun ((p (i + 1)).toFun x) = (p i).toFun x)
    (hadm : ∀ i, IsAdmissibleEpi (t i))
    (hsep : ∀ x : I.M, (∀ i, (p i).toFun x = 0) → x = 0)
    (hcomplete : ∀ (n : ℤ) (q : ∀ i, (Q i).M), (∀ i, q i ∈ (Q i).grading n) →
      (∀ i, (t i).toFun (q (i + 1)) = q i) → ∃ y ∈ I.grading n, ∀ i, (p i).toFun y = q i)
    (hPsep : ∀ y : P.M, (∀ i, (π i).toFun y = 0) → y = 0)
    (hPlift : ∀ (n : ℤ) (q : ∀ i, (Q i).M), (∀ i, q i ∈ (Q i).grading n) →
      ∃ y ∈ P.grading n, ∀ i, (π i).toFun y = q i) :
    ∃ (α : I ⟶ P) (β : P ⟶ P),
      (∀ (i : ℕ) (x : I.M), (π i).toFun (α.toFun x) = (p i).toFun x) ∧
      (∀ (i : ℕ) (y : P.M), (π i).toFun (β.toFun y)
        = (π i).toFun y - (t i).toFun ((π (i + 1)).toFun y)) ∧
      IsAdmissibleShortExact α β := by
  classical
  -- the two maps of the sequence
  obtain ⟨α, hα⟩ := exists_homLift π hPsep hPlift p
  obtain ⟨τ, hτ⟩ := exists_homLift π hPsep hPlift fun i => π (i + 1) ≫ t i
  have hτ' : ∀ (i : ℕ) (y : P.M),
      (π i).toFun (τ.toFun y) = (t i).toFun ((π (i + 1)).toFun y) := by
    intro i y
    have := hτ i y
    rwa [Hom.comp_toFun_apply] at this
  have hβ : ∀ y : P.M, (𝟙 P - τ).toFun y = y - τ.toFun y := by
    intro y
    rw [Hom.hom_sub_toFun]
    simp only [LinearMap.sub_apply]
    rfl
  refine ⟨α, 𝟙 P - τ, hα, fun i y => by rw [hβ, map_sub, hτ' i y], ?_⟩
  -- the first map is injective, by separatedness
  have hαinj : Function.Injective α.toFun := by
    intro x x' hxx
    have h := hsep (x - x') fun i => by rw [map_sub, ← hα i x, ← hα i x', hxx, sub_self]
    rwa [sub_eq_zero] at h
  -- the composite of the two maps vanishes
  have hcomp : ∀ x : I.M, (𝟙 P - τ).toFun (α.toFun x) = 0 := by
    intro x
    rw [hβ, sub_eq_zero]
    refine (eq_of_proj_eq π hPsep fun i => ?_).symm
    rw [hτ' i (α.toFun x), hα (i + 1) x, hp i x, hα i x]
  -- an element killed by the second map comes from `I`
  have hker : ∀ y : P.M, (𝟙 P - τ).toFun y = 0 → ∃ x : I.M, α.toFun x = y := by
    intro y hy
    rw [hβ, sub_eq_zero] at hy
    -- the graded components of `y` are themselves fixed by `τ`
    have hcompfix : ∀ n : ℤ,
        τ.toFun ((DirectSum.decompose P.grading y n : P.M))
          = (DirectSum.decompose P.grading y n : P.M) := by
      intro n
      have h := DirectSum.coe_decompose_apply_map P.grading P.grading τ.toFun
        (fun i z hz => τ.map_grading i z hz) y n
      rw [← hy] at h
      exact h.symm
    -- each component is the image of a homogeneous element of `I`
    have hpiece : ∀ n : ℤ, ∃ x : I.M, α.toFun x = (DirectSum.decompose P.grading y n : P.M) := by
      intro n
      obtain ⟨x, _, hx⟩ := hcomplete n (fun i => (π i).toFun
          ((DirectSum.decompose P.grading y n : P.M)))
        (fun i => (π i).map_grading n _ (DirectSum.decompose P.grading y n).2)
        (fun i => by
          rw [← hτ' i, hcompfix n])
      exact ⟨x, eq_of_proj_eq π hPsep fun i => by rw [hα i x, hx i]⟩
    refine ⟨∑ n ∈ DFinsupp.support (DirectSum.decompose P.grading y),
      (hpiece n).choose, ?_⟩
    rw [map_sum]
    calc ∑ n ∈ DFinsupp.support (DirectSum.decompose P.grading y),
          α.toFun ((hpiece n).choose)
        = ∑ n ∈ DFinsupp.support (DirectSum.decompose P.grading y),
            ((DirectSum.decompose P.grading y) n : P.M) :=
          Finset.sum_congr rfl fun n _ => (hpiece n).choose_spec
      _ = y := DirectSum.sum_support_decompose P.grading y
  -- the graded section of the second map, by the recursion through the chosen sections
  choose σ hσ using hadm
  let Sq : ∀ i : ℕ, P.M → (Q i).M := fun i =>
    Nat.rec (motive := fun i => P.M → (Q i).M) (fun _ => 0)
      (fun j prev r => (σ j).toFun (prev r - (π j).toFun r)) i
  have hSq0 : ∀ r : P.M, Sq 0 r = 0 := fun _ => rfl
  have hSqs : ∀ (j : ℕ) (r : P.M),
      Sq (j + 1) r = (σ j).toFun (Sq j r - (π j).toFun r) := fun _ _ => rfl
  have hSqadd : ∀ (i : ℕ) (r r' : P.M), Sq i (r + r') = Sq i r + Sq i r' := by
    intro i
    induction i with
    | zero => intro r r'; rw [hSq0, hSq0, hSq0, add_zero]
    | succ j ih =>
        intro r r'
        rw [hSqs, hSqs, hSqs, ih, map_add, show Sq j r + Sq j r'
            - ((π j).toFun r + (π j).toFun r')
          = (Sq j r - (π j).toFun r) + (Sq j r' - (π j).toFun r') from by abel, map_add]
  have hSqR : ∀ (i : ℕ) (c : R) (r : P.M), Sq i (c • r) = c • Sq i r := by
    intro i
    induction i with
    | zero => intro c r; rw [hSq0, hSq0, smul_zero]
    | succ j ih =>
        intro c r
        rw [hSqs, hSqs, ih, map_smul, ← smul_sub, map_smul]
  have hSqA : ∀ (i : ℕ) (a : A.A) (r : P.M), Sq i (op a • r) = op a • Sq i r := by
    intro i
    induction i with
    | zero => intro a r; rw [hSq0, hSq0, smul_zero]
    | succ j ih =>
        intro a r
        rw [hSqs, hSqs, ih, (π j).map_smul, ← smul_sub, (σ j).map_smul]
  have hSqgr : ∀ (i : ℕ) (n : ℤ) (r : P.M), r ∈ P.grading n → Sq i r ∈ (Q i).grading n := by
    intro i
    induction i with
    | zero => intro n r _; rw [hSq0]; exact Submodule.zero_mem _
    | succ j ih =>
        intro n r hr
        rw [hSqs]
        exact (σ j).map_grading n _ ((Submodule.sub_mem _ (ih n r hr) ((π j).map_grading n r hr)))
  obtain ⟨s, hsadd, hsR, hsA, hsgr, hsπ⟩ :=
    exists_productLift π hPsep hPlift 0 Sq hSqadd hSqR hSqA
      fun i n r hr => by rw [add_zero]; exact hSqgr i n r hr
  have hsgr' : ∀ (n : ℤ) (r : P.M), r ∈ P.grading n → s r ∈ P.grading n := fun n r hr => by
    simpa using hsgr n r hr
  have hβs : ∀ r : P.M, (𝟙 P - τ).toFun (s r) = r := by
    intro r
    refine eq_of_proj_eq π hPsep fun i => ?_
    rw [hβ, map_sub, hτ' i (s r), hsπ i r, hsπ (i + 1) r, hSqs i r, hσ i]
    abel
  have hs0 : s 0 = 0 := by
    have h := hsadd 0 0
    rw [add_zero] at h
    have h' : s 0 + 0 = s 0 + s 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  -- the graded retraction of the first map
  have hexρ : ∀ r : P.M, ∃ x : I.M, α.toFun x = r - s ((𝟙 P - τ).toFun r) := by
    intro r
    refine hker _ ?_
    rw [map_sub, hβs ((𝟙 P - τ).toFun r), sub_self]
  have hρ : ∀ r : P.M, α.toFun ((hexρ r).choose) = r - s ((𝟙 P - τ).toFun r) :=
    fun r => (hexρ r).choose_spec
  refine ⟨hαinj, fun r => ⟨s r, hβs r⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- the image of the first map is the kernel of the second
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      exact hcomp x
    · intro y hy
      obtain ⟨x, hx⟩ := hker y (LinearMap.mem_ker.mp hy)
      exact ⟨x, hx⟩
  · -- the graded retraction
    exact {
      toFun :=
        { toFun := fun r => (hexρ r).choose
          map_add' := fun r r' => hαinj (by
            calc α.toFun ((hexρ (r + r')).choose)
                = r + r' - s ((𝟙 P - τ).toFun (r + r')) := hρ (r + r')
              _ = (r - s ((𝟙 P - τ).toFun r)) + (r' - s ((𝟙 P - τ).toFun r')) := by
                  rw [map_add, hsadd]
                  abel
              _ = α.toFun ((hexρ r).choose) + α.toFun ((hexρ r').choose) := by rw [hρ, hρ]
              _ = α.toFun ((hexρ r).choose + (hexρ r').choose) := (map_add _ _ _).symm)
          map_smul' := fun c r => hαinj (by
            calc α.toFun ((hexρ (c • r)).choose)
                = c • r - s ((𝟙 P - τ).toFun (c • r)) := hρ (c • r)
              _ = c • (r - s ((𝟙 P - τ).toFun r)) := by rw [map_smul, hsR, smul_sub]
              _ = c • α.toFun ((hexρ r).choose) := by rw [hρ]
              _ = α.toFun (c • (hexρ r).choose) := (map_smul _ _ _).symm) }
      map_smul := fun r a => hαinj (by
        calc α.toFun ((hexρ (op a • r)).choose)
            = op a • r - s ((𝟙 P - τ).toFun (op a • r)) := hρ _
          _ = op a • (r - s ((𝟙 P - τ).toFun r)) := by
              rw [(𝟙 P - τ).map_smul, hsA, smul_sub]
          _ = op a • α.toFun ((hexρ r).choose) := by rw [hρ]
          _ = α.toFun (op a • (hexρ r).choose) := (α.map_smul _ a).symm)
      map_grading := fun n r hr => Hom.mem_grading_of_injective hαinj (by
        change α.toFun ((hexρ r).choose) ∈ P.grading n
        rw [hρ]
        exact Submodule.sub_mem _ hr (hsgr' n _ ((𝟙 P - τ).map_grading n r hr))) }
  · intro x
    refine hαinj ?_
    change α.toFun ((hexρ (α.toFun x)).choose) = α.toFun x
    rw [hρ, hcomp x, hs0, sub_zero]
  · exact ⟨{
      toFun := { toFun := s, map_add' := hsadd, map_smul' := hsR }
      map_smul := fun r a => hsA a r
      map_grading := hsgr' }, hβs⟩

end DifferentialGradedModule

end
