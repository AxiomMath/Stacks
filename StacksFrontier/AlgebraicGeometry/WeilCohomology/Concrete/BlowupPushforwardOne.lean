module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupPoints
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinTransversal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PushforwardUnitOfTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceUniqueness
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PoincareDualityWeilThree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension

/-!
# Stacks 0FIS: `b_*(1) = 1` for the blowing up in a nowhere dense smooth centre

Let data (D0), (D1), (D2') satisfy axioms (A1)–(A8) of Section 45.14, and let `b : X' ⟶ X` be the
blowing up of a nonempty smooth projective scheme `X` over `k`, equidimensional of dimension `d`,
in a nowhere dense smooth centre `Z`. Then `∫_{X'} ∘ b^* = ∫_X` on `H^{2d}(X)(d)`, and
`b_*(1) = 1`.

The proof is the source's, with the points chosen in every component of `X'` at once.

* Choose closed points `x'ⱼ ∈ X'` off the exceptional divisor with separable residue fields,
  detecting `Γ(X', 𝒪_{X'})` (Tag 056U); restriction to them is injective on `H^0(X')` by (A8)
  and Tag 0FVS (`Stacks.WeilCohomology.FirstChernClassData.pull_points_injective`).
* Along `(b ∘ x'ⱼ) × b : x'ⱼ × X' ⟶ X × X` and `x'ⱼ × 1 : x'ⱼ × X' ⟶ X' × X'` the diagonals pull
  back to the same cycle, the graph of `x'ⱼ`, because `b` is an isomorphism near `x'ⱼ`
  (`Stacks.WeilCohomology.codimensionGysin_prodHom_diagonal_of_isIso` and
  `Stacks.WeilCohomology.codimensionGysin_prodHom_id_diagonal`); compatibility of `γ` with
  pullbacks transports this to cohomology.
* `Stacks.WeilCohomology.FirstChernClassData.traceContract_comp_pullTw_eq_one` then shows that
  `∫_{X'} ∘ b^*` satisfies the normalization (A6) of `∫_X`, and uniqueness of the trace map
  (Remark 0FIK) gives `∫_{X'} ∘ b^* = ∫_X`; `b_*(1) = 1` follows by Poincaré duality.

## Main results

* `Stacks.WeilCohomology.FirstChernClassData.pushforward_unitTw_blowupHom`: **Stacks 0FIS**,
  `b_*(1) = 1`.
* `Stacks.WeilCohomology.FirstChernClassData.trace_comp_pullGradeTw_blowupHom`: **Stacks 0FIS**,
  in the form the proof establishes, `∫_{X'} ∘ b^* = ∫_X`.
* `Stacks.WeilCohomology.FirstChernClassData.pullTw_diagonal_points_eq`: the comparison of the
  pulled back diagonal classes at the points, for any family `γ` compatible with pullbacks.
* `Stacks.WeilCohomology.FirstChernClassData.trace_comp_pull_blowup_of_cycleClass`: the trace
  identity, for any such family `γ` whose diagonal classes are normalized by traces, unique on `X`.

## References

* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 0FVS](https://stacks.math.columbia.edu/tag/0FVS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology.FirstChernClassData

open SmoothProjectiveScheme Stacks.Chow

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

section Diagonal

variable (γ : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ),
    codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i)
  (hγ : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i : ℕ)
    (β : codimensionChowGroup k Y.obj.hom i),
    γ X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) = 𝔇.pullTw f i (γ Y i β))

include hγ in
/-- **The two diagonal classes agree at a point off the centre.** For `p : P ⟶ X'` with `P` of
dimension zero and `b : X' ⟶ X` such that `P ×_X X' = P` along `b ∘ p` and `b`, with `X`, `X'` of
dimension `d`, `((b p) × b)^* γ([Δ_X]) = (p × 1)^* γ([Δ_{X'}])` in `H^{2d}(P × X')(d)`. -/
theorem pullTw_diagonal_points_eq {P X' X : (SmoothProjectiveScheme k).FullSubcategory} (p : P ⟶ X')
    (b : X' ⟶ X) {d : ℕ} (hP : RelativeDimension P.obj.hom 0)
    (hX' : RelativeDimension X'.obj.hom d) (hX : RelativeDimension X.obj.hom d)
    [IsIso (pullback.fst (p.hom.left ≫ b.hom.left) b.hom.left)] :
    𝔇.pullTw (prodMap (p ≫ b) b) d (γ (prod X X) d (diagonalClass X d)) =
      𝔇.pullTw (prodMap p (𝟙 X')) d (γ (prod X' X') d (diagonalClass X' d)) := by
  rw [← hγ, ← hγ]
  congr 1
  have h1 := codimensionGysin_prodHom_diagonal_of_isIso X.obj.hom P.obj.hom X'.obj.hom p.hom.left
    b.hom.left (Over.w p.hom) (Over.w b.hom) hP hX' hX
  have h2 := codimensionGysin_prodHom_id_diagonal P.obj.hom X'.obj.hom p.hom.left (Over.w p.hom)
    hP hX'
  exact h1.trans h2.symm

/-- **The trace identity of Stacks 0FIS, for a family `γ`.** Let `γ` be compatible with pullbacks
and take values in the even graded pieces, let `b : X' ⟶ X` be the blowing up of a nonempty
smooth projective `X`, equidimensional of dimension `d`, in a nowhere dense smooth centre, with
`X'` nonempty equidimensional of dimension `d`, and let `λ'` satisfy the normalization (A6) for
`X'`. If the trace of `X` is the unique `λ` satisfying (A6) for `X`, then `λ' ∘ b^* = λ`. -/
theorem trace_comp_pull_blowup_of_cycleClass [CharZero F] (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom)
    (hA7 : 𝔇.BlowupAxiom) (hA8 : 𝔇.GlobalSectionsAxiom)
    (γ : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ),
      codimensionChowGroup k X.obj.hom i →+ tateTwist F 𝔇.tate (𝔇.H X) i)
    (hγ : ∀ {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (i : ℕ)
      (β : codimensionChowGroup k Y.obj.hom i),
      γ X i (codimensionGysin X.obj.hom Y.obj.hom (Over.w f.hom) i β) = 𝔇.pullTw f i (γ Y i β))
    (hγmem : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℕ)
        (β : codimensionChowGroup k X.obj.hom i),
      𝔇.κ X i (γ X i β) ∈ 𝔇.grade X (2 * (i : ℤ)))
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (hZ : IsNowhereDense (Set.range i.hom.left.base)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hX' : IsNonemptyEquidimensional (blowupObj i) d)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (lam' : tateTwist F 𝔇.tate (𝔇.grade (blowupObj i) (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam' : 𝔇.traceContract hA5 (blowupObj i) d lam'
      (γ (prod (blowupObj i) (blowupObj i)) d (diagonalClass (blowupObj i) d)) = 1)
    (huniq : ∀ μ, 𝔇.traceContract hA5 X d μ (γ (prod X X) d (diagonalClass X d)) = 1 → μ = lam) :
    lam' ∘ₗ 𝔇.pullGradeTw (blowupHom i) (2 * (d : ℤ)) d = lam := by
  obtain ⟨ι, hι, x, hx, hinj⟩ := exists_separablePoints_blowup i
  have hfin : ∀ j, let := residueAlgebra (blowupObj i) (x j)
      Module.Finite k ((blowupObj i).obj.left.residueField (x j)) := fun j => (hx j).2.1
  have hsep : ∀ j, let := residueAlgebra (blowupObj i) (x j)
      Algebra.IsSeparable k ((blowupObj i).obj.left.residueField (x j)) := fun j => (hx j).2.2
  have : Nonempty ι := by
    by_contra hι0
    rw [not_nonempty_iff] at hι0
    obtain ⟨x0⟩ := hX'.nonempty
    have h01 : (1 : Γ((blowupObj i).obj.left, ⊤)) = 0 := hinj (funext fun j => hι0.elim j)
    have := congrArg ((blowupObj i).obj.left.Γevaluation x0).hom h01
    rw [map_one, map_zero] at this
    exact one_ne_zero this
  have hpts : ∀ j, 𝔇.pullTw (prodMap (pointHom (x j) ≫ blowupHom i) (blowupHom i)) d
      (γ (prod X X) d (diagonalClass X d)) =
        𝔇.pullTw (prodMap (pointHom (x j)) (𝟙 (blowupObj i))) d
          (γ (prod (blowupObj i) (blowupObj i)) d (diagonalClass (blowupObj i) d)) := by
    intro j
    let := residueAlgebra (blowupObj i) (x j)
    have : IsIso (pullback.fst ((pointHom (x j)).hom.left ≫ (blowupHom i).hom.left)
        (blowupHom i).hom.left) := by
      refine @isIso_pullback_fst_comp_of_isIso_restrict _ _ _ _ (blowupHom i).hom.left
        (⟨(i.hom.left.ker.support : Set X.obj.left)ᶜ,
            i.hom.left.ker.support.isClosed.isOpen_compl⟩ :
          X.obj.left.Opens) (isIso_blowupHom_restrict i) fun pt => ?_
      have hpt : (pointHom (x j)).hom.left pt = x j := by
        have := Scheme.range_fromSpecResidueField (X := (blowupObj i).obj.left) (x j)
        have hmem : (blowupObj i).obj.left.fromSpecResidueField (x j) pt ∈
            Set.range ((blowupObj i).obj.left.fromSpecResidueField (x j)) := ⟨pt, rfl⟩
        rw [this] at hmem
        exact hmem
      change (blowupHom i).hom.left ((pointHom (x j)).hom.left pt) ∉
        (i.hom.left.ker.support : Set X.obj.left)
      rw [hpt, mem_support_ker_iff]
      exact (hx j).1
    exact 𝔇.pullTw_diagonal_points_eq γ hγ (pointHom (x j)) (blowupHom i)
      (relativeDimension_zero_of_dimension_zero topologicalKrullDim_spec_field)
      hX'.relativeDimension hX.relativeDimension
  have hinj' := 𝔇.pull_points_injective hA1 hA3 hA4 hA5 hA8 (blowupObj i) x hinj
  refine huniq _ (𝔇.traceContract_comp_pullTw_eq_one hA5 (blowupHom i) (hA7 Z X i hZ) d _ _
    (hγmem _ d _) (hγmem _ d _) lam' hlam' (fun j => pointHom (x j)) hinj' hpts)

end Diagonal

/-! ### The cycle class map of Tag 0FIF -/

section CycleClass

variable [CharZero F] {ch : ∀ X : (SmoothProjectiveScheme k).FullSubcategory,
    VectorBundleKZero ((SmoothProjectiveScheme.toScheme k).obj X) → ∀ n : ℕ,
      tateTwist F 𝔇.tate (𝔇.H X) n}

/-- **The trace identity of Stacks 0FIS for the cycle class map `γ` of Tag 0FIF**: for the
blowing up `b : X' ⟶ X` in a nowhere dense smooth centre and traces `λ`, `λ'` normalized by (A6)
for `X` and `X'`, `λ'` composed with `b^*` is `λ`, as soon as `λ` is the only trace normalized
for `X`. -/
theorem trace_comp_pull_blowup (h : 𝔇.IsCohomologicalChernCharacter ch) (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom)
    (hA7 : 𝔇.BlowupAxiom) (hA8 : 𝔇.GlobalSectionsAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (hZ : IsNowhereDense (Set.range i.hom.left.base)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (lam' : tateTwist F 𝔇.tate (𝔇.grade (blowupObj i) (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam' : 𝔇.traceContract hA5 (blowupObj i) d lam'
      (h.codimensionCycleClass (prod (blowupObj i) (blowupObj i)) d
        (diagonalClass (blowupObj i) d)) = 1)
    (huniq : ∀ μ, 𝔇.traceContract hA5 X d μ
      (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) = 1 → μ = lam) :
    lam' ∘ₗ 𝔇.pullGradeTw (blowupHom i) (2 * (d : ℤ)) d = lam :=
  𝔇.trace_comp_pull_blowup_of_cycleClass hA1 hA3 hA4 hA5 hA7 hA8 h.codimensionCycleClass
    (fun f i b => h.codimensionCycleClass_codimensionGysin f i b)
    (fun Y i β => (𝔇.mem_range_tateTwistMap_iff _ _ _).mp
      (h.codimensionCycleClass_mem hA1 hA3 Y i β))
    i hZ hX (isNonemptyEquidimensional_blowupObj i hX hZ) lam lam' hlam' huniq

/-- **Stacks Project, Tag 0FIS.** Let data (D0), (D1), (D2') satisfy axioms (A1)–(A8) of
Section 45.14 (of which (A1), (A3), (A4), (A5), (A7), (A8) are used), with `γ` the cycle class map
of Tag 0FIF. Let `b : X' ⟶ X` be the blowing up of a smooth projective scheme `X` over `k`,
nonempty and equidimensional of dimension `d`, in a nowhere dense smooth centre `Z ⊆ X`. Then the
trace map `∫_{X'}` of `X'` composed with `b^* : H^{2d}(X)(d) ⟶ H^{2d}(X')(d)` is the trace map
`∫_X` of `X`: for the linear maps `λ`, `λ'` of axiom (A6) for `X` and `X'` (unique by Remark 0FIK),
`λ' ∘ b^* = λ`. This is the identity the source's proof establishes ("`∫_X` is equal to `∫_{X'}`
composed with the pullback map"), equivalent to `b_*(1) = 1` for the pushforward of Section 45.9
built from these trace maps. -/
@[stacks 0FIS "∫_{X'} ∘ b^* = ∫_X on H^{2d}(X)(d) for the blowing up in a nowhere dense smooth \
centre, the trace maps being the λ of (A6) and γ the cycle class map of 0FIF, under (A1)-(A8); the \
form b_*(1) = 1 of the statement is this identity read through Poincaré duality"]
theorem trace_comp_pullGradeTw_blowupHom (h : 𝔇.IsCohomologicalChernCharacter ch)
    (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom)
    (hA5 : 𝔇.KunnethAxiom) (hA7 : 𝔇.BlowupAxiom) (hA8 : 𝔇.GlobalSectionsAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (hZ : IsNowhereDense (Set.range i.hom.left.base)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (lam' : tateTwist F 𝔇.tate (𝔇.grade (blowupObj i) (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 X d lam
      (h.codimensionCycleClass (prod X X) d (diagonalClass X d)) = 1)
    (hlam' : 𝔇.traceContract hA5 (blowupObj i) d lam'
      (h.codimensionCycleClass (prod (blowupObj i) (blowupObj i)) d
        (diagonalClass (blowupObj i) d)) = 1) :
    lam' ∘ₗ 𝔇.pullGradeTw (blowupHom i) (2 * (d : ℤ)) d = lam :=
  𝔇.trace_comp_pull_blowup h hA1 hA3 hA4 hA5 hA7 hA8 i hZ hX lam lam' hlam'
    fun μ hμ => h.trace_unique hA1 hA3 hA4 hA5 hA7 X d hX μ lam hμ hlam

/-- **Stacks Project, Tag 0FIS: `b_*(1) = 1`.** Let data (D0), (D1), (D2') satisfy axioms
(A1)–(A8) of Section 45.14 (of which (A1), (A3)–(A8) are used), `γ` the cycle class map of
Tag 0FIF, and let `W` be the data (D0)–(D3) of Section 45.9 they define, with trace maps the `λ`
of (A6) (`IsCohomologicalChernCharacter.toWeilData`), which satisfy axiom (A) by Lemma 0FIJ. Let
`b : X' ⟶ X` be the blowing up of a smooth projective scheme `X` over `k`, nonempty and
equidimensional of dimension `d`, in a nowhere dense smooth centre. Then the pushforward
`b_* : H^0(X') ⟶ H^0(X)` of Section 45.9 sends `1` to `1`. -/
@[stacks 0FIS "b_*(1) = 1 for the blowing up in a nowhere dense smooth centre, for the pushforward \
of Section 45.9 attached to the data of (A1)-(A8) with the trace maps of (A6) and γ of 0FIF"]
theorem pushforward_unitTw_blowupHom (h : 𝔇.IsCohomologicalChernCharacter ch)
    (hA1 : 𝔇.CoproductAxiom) (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom)
    (hA5 : 𝔇.KunnethAxiom) (hA6 : 𝔇.TraceAxiomFor hA5 h.codimensionCycleClass)
    (hA7 : 𝔇.BlowupAxiom) (hA8 : 𝔇.GlobalSectionsAxiom)
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    (hZ : IsNowhereDense (Set.range i.hom.left.base)) {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) :
    (h.toWeilData hA1 hA3 hA5 hA6).pushforward
        (h.poincareDuality_toWeilData hA1 hA3 hA5 hA6 hA4 hA7).perfectPairing (blowupHom i)
        (isNonemptyEquidimensional_blowupObj i hX hZ) hX 0 0 0 0 rfl rfl
        ((h.toWeilData hA1 hA3 hA5 hA6).unitTw (blowupObj i) 0 0 rfl) =
      (h.toWeilData hA1 hA3 hA5 hA6).unitTw X 0 0 rfl := by
  set W := h.toWeilData hA1 hA3 hA5 hA6
  have hX' := isNonemptyEquidimensional_blowupObj i hX hZ
  rw [W.pushforward_unitTw_eq_unitTw_iff]
  intro a
  have key := 𝔇.trace_comp_pullGradeTw_blowupHom h hA1 hA3 hA4 hA5 hA7 hA8 i hZ hX
    (W.trace X d hX) (W.trace (blowupObj i) d hX')
    (h.traceContract_toWeilData_trace hA1 hA3 hA5 hA6 X d hX)
    (h.traceContract_toWeilData_trace hA1 hA3 hA5 hA6 (blowupObj i) d hX')
  exact LinearMap.congr_fun key a

end CycleClass

end Stacks.WeilCohomology.FirstChernClassData

end
