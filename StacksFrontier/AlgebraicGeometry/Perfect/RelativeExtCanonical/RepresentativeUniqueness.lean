module

public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleOfTower

/-!
# An object with quasi-coherent cohomology is determined by maps to bounded below objects

Let `X` be a scheme and let `L`, `L'` be objects of `D(𝒪_X)` with quasi-coherent cohomology
sheaves. Suppose given, for every `N` in a class `P` of bounded below objects containing the
truncations `τ_{≥ -n}L` and `τ_{≥ -n}L'`, a bijection

`α_N : Hom(L, N) ≃ Hom(L', N)`

natural in `N`. Then there is an isomorphism `φ : L' ≅ L` inducing `α`: `α_N(x) = φ ∘ x` for
every `N` in `P` and every `x : L ⟶ N`.

This is the uniqueness half of the statement that a representing object of a functor on
bounded below objects is canonical. It is the mechanism behind the canonicity asserted in
[Stacks, Tag 0DJS]: the complex `L` of [Stacks, Tag 08IF] (B) represents
`N ↦ Hom(E, 𝒢 ⊗ f^*N)` on the bounded below objects with quasi-coherent cohomology, and so it
is determined up to an isomorphism compatible with that identification.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.exists_hom_comp_truncGEπ`: maps out of an object into
  the truncation tower of `L` that are compatible with the tower lift to a map into `L`, for `L`
  with quasi-coherent cohomology (the Milnor triangle of [Stacks, Tag 08D3]).
* `Stacks.Cohomology.RelativeExtCanonical.exists_iso_of_natural_homEquiv`: the uniqueness
  statement above.

## Implementation notes

The isomorphism is not unique in general: two choices differ by a map vanishing on every
truncation `τ_{≥ -n}`, which is a `lim¹`-phenomenon of the Milnor sequence. What is unique is
its composite with each truncation map, and that is what the conclusion pins: the equation
`α_N(x) = φ ∘ x` for all `N` in `P`.

The proof: the maps `α(L ⟶ τ_{≥ -n}L)` form a compatible family into the tower of `L`, which
lifts to `φ₀ : L' ⟶ L` through the Milnor triangle; symmetrically for `α⁻¹`. Every map from `L`
to a bounded below object factors through a truncation, so `φ₀` induces `α` on all of `P`, and
the composites `φ₀ ∘ ψ₀` and `ψ₀ ∘ φ₀` are the identity after every truncation. They are then
isomorphisms on every cohomology sheaf, hence isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry

namespace Stacks.Cohomology.RelativeExtCanonical

variable {X : Scheme.{u}}

/-- The truncation `τ_{≥ -n}L`, as the `n`-th term of the truncation tower. -/
abbrev towerObj (L : DerivedCategory X.Modules) (n : ℕ) : DerivedCategory X.Modules :=
  (Stacks.DerivedLimit.truncGETower X.Modules L).obj ⟨n⟩

/-- The truncation map `L ⟶ τ_{≥ -n}L`. -/
abbrev truncMap (L : DerivedCategory X.Modules) (n : ℕ) : L ⟶ towerObj L n :=
  (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app L

/-- **Lifting a compatible family into the truncation tower.** Let `L` have quasi-coherent
cohomology sheaves. A family of maps `xₙ : A ⟶ τ_{≥ -n}L` compatible with the transition maps of
the tower lifts to a map `A ⟶ L` whose composite with every truncation map is `xₙ`. -/
theorem exists_hom_comp_truncGEπ (L : DerivedCategory X.Modules)
    (hL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L).IsQuasicoherent)
    {A : DerivedCategory X.Modules}
    (x : ∀ n : ℕ, A ⟶ towerObj L n)
    (hx : ∀ n : ℕ, x (n + 1) ≫ (Stacks.DerivedLimit.truncGETower X.Modules L).map
      (homOfLE (Nat.le_succ n)).op = x n) :
    ∃ φ : A ⟶ L, ∀ n : ℕ, φ ≫ truncMap L n = x n := by
  have hprod := Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower X.ringCatSheaf L
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower X.Modules L)
    (fun n : ℕ ↦ truncMap L n)
    (fun n ↦ Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map L
      (homOfLE (Nat.le_succ n)).op)
    fun L₀ f p δ' hT hcn ↦ isIso_of_isDerivedLimit_truncGETower X L hL L₀ f p δ' hT hcn
  have hw : (Pi.lift x) ≫ (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules L).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules L).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower X.Modules L).map (homOfLE (Nat.le_succ n)).op) =
        0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, Pi.lift_comp_π, ← Category.assoc,
      Pi.lift_comp_π, hx n, sub_self, zero_comp]
  obtain ⟨φ, hφ⟩ := Triangle.coyoneda_exact₂ _ hδ (Pi.lift x) hw
  refine ⟨φ, fun n ↦ ?_⟩
  have h := congrArg (fun g ↦ g ≫ Pi.π (fun n : ℕ ↦ towerObj L n) n) hφ
  have h1 : Pi.lift x ≫ Pi.π (fun n : ℕ ↦ towerObj L n) n = x n := Pi.lift_comp_π _ _
  have h2 : (Pi.lift fun n ↦ truncMap L n) ≫ Pi.π (fun n : ℕ ↦ towerObj L n) n =
      truncMap L n := Pi.lift_comp_π _ _
  dsimp only [Triangle.mk_mor₁] at h
  rw [h1, Category.assoc, h2] at h
  exact h.symm

/-- A map from `L` to an object in degrees `≥ -n` factors through the truncation map
`L ⟶ τ_{≥ -n}L`. -/
theorem exists_eq_truncMap_comp (L N : DerivedCategory X.Modules) (n : ℕ)
    [N.IsGE (-(n : ℤ))] (y : L ⟶ N) :
    ∃ z : towerObj L n ⟶ N, y = truncMap L n ≫ z :=
  ⟨DerivedCategory.TStructure.t.descTruncGE y (-(n : ℤ)),
    (DerivedCategory.TStructure.t.π_descTruncGE y (-(n : ℤ))).symm⟩

/-- A map inducing the identity after every truncation `τ_{≥ -n}` is an isomorphism. -/
theorem isIso_of_comp_truncMap_eq (L : DerivedCategory X.Modules) (e : L ⟶ L)
    (he : ∀ n : ℕ, e ≫ truncMap L n = truncMap L n) : IsIso e := by
  rw [DerivedCategory.isIso_iff]
  intro i
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ i := ⟨i.natAbs, by omega⟩
  have hiso : IsIso ((DerivedCategory.homologyFunctor X.Modules i).map (truncMap L n)) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ (C := X.Modules) (-(n : ℤ)) i hn L
  have h := congrArg (DerivedCategory.homologyFunctor X.Modules i).map (he n)
  rw [Functor.map_comp] at h
  have : (DerivedCategory.homologyFunctor X.Modules i).map e = 𝟙 _ := by
    rw [← cancel_mono ((DerivedCategory.homologyFunctor X.Modules i).map (truncMap L n)), h,
      Category.id_comp]
  rw [this]
  infer_instance

/-- A family of bijections `Hom(M, N) ≃ Hom(M', N)` on `P`, natural in `N`, is given by
precomposition with a map `M' ⟶ M`, for `M` with quasi-coherent cohomology. -/
private theorem exists_hom_eq_equiv_comp (P : ObjectProperty (DerivedCategory X.Modules))
    (hPge : ∀ N : DerivedCategory X.Modules, P N → ∃ m : ℤ, N.IsGE m)
    {M M' : DerivedCategory X.Modules}
    (hM : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj M).IsQuasicoherent)
    (hPM : ∀ n : ℕ, P (towerObj M n))
    (β : ∀ N : DerivedCategory X.Modules, P N → ((M ⟶ N) ≃ (M' ⟶ N)))
    (hβ : ∀ {N N' : DerivedCategory X.Modules} (hN : P N) (hN' : P N') (g : N ⟶ N')
      (x : M ⟶ N), β N' hN' (x ≫ g) = β N hN x ≫ g) :
    ∃ φ : M' ⟶ M, ∀ (N : DerivedCategory X.Modules) (hN : P N) (x : M ⟶ N),
      β N hN x = φ ≫ x := by
  obtain ⟨φ, hφ⟩ := exists_hom_comp_truncGEπ M hM
    (fun n ↦ β (towerObj M n) (hPM n) (truncMap M n))
    (fun n ↦ by
      rw [← hβ (hPM (n + 1)) (hPM n)]
      exact congrArg _ (Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map M
        (homOfLE (Nat.le_succ n)).op))
  refine ⟨φ, fun N hN x ↦ ?_⟩
  obtain ⟨m, hm⟩ := hPge N hN
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ m := ⟨m.natAbs, by omega⟩
  have : N.IsGE (-(n : ℤ)) := DerivedCategory.TStructure.t.isGE_of_ge N _ _ hn
  obtain ⟨z, rfl⟩ := exists_eq_truncMap_comp M N n x
  rw [hβ (hPM n) hN, ← hφ n, Category.assoc]

/-- **An object with quasi-coherent cohomology is determined by its maps to bounded below
objects.** Let `P` be a class of objects of `D(𝒪_X)`, each bounded below, which contains every
truncation `τ_{≥ -n}L` and `τ_{≥ -n}L'` of two objects `L`, `L'` with quasi-coherent cohomology
sheaves. A family of bijections `α_N : Hom(L, N) ≃ Hom(L', N)`, `N ∈ P`, natural in `N`, is
induced by an isomorphism `φ : L' ≅ L`, in the sense that `α_N(x) = φ ∘ x` for all `N ∈ P` and
`x : L ⟶ N`. -/
theorem exists_iso_of_natural_homEquiv (P : ObjectProperty (DerivedCategory X.Modules))
    (hPge : ∀ N : DerivedCategory X.Modules, P N → ∃ m : ℤ, N.IsGE m)
    (L L' : DerivedCategory X.Modules)
    (hL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L).IsQuasicoherent)
    (hL' : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L').IsQuasicoherent)
    (hPL : ∀ n : ℕ, P ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L))
    (hPL' : ∀ n : ℕ, P ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L'))
    (α : ∀ N : DerivedCategory X.Modules, P N → ((L ⟶ N) ≃ (L' ⟶ N)))
    (hα : ∀ {N N' : DerivedCategory X.Modules} (hN : P N) (hN' : P N') (g : N ⟶ N')
      (x : L ⟶ N), α N' hN' (x ≫ g) = α N hN x ≫ g) :
    ∃ φ : L' ≅ L, ∀ (N : DerivedCategory X.Modules) (hN : P N) (x : L ⟶ N),
      α N hN x = φ.hom ≫ x := by
  have hαsymm : ∀ {N N' : DerivedCategory X.Modules} (hN : P N) (hN' : P N') (g : N ⟶ N')
      (y : L' ⟶ N), (α N' hN').symm (y ≫ g) = (α N hN).symm y ≫ g := by
    intro N N' hN hN' g y
    rw [Equiv.symm_apply_eq, hα hN hN', Equiv.apply_symm_apply]
  have hPL₀ : ∀ n : ℕ, P (towerObj L n) := hPL
  have hPL₀' : ∀ n : ℕ, P (towerObj L' n) := hPL'
  obtain ⟨φ₀, hφα⟩ := exists_hom_eq_equiv_comp P hPge hL hPL₀ α hα
  obtain ⟨ψ₀, hψα⟩ := exists_hom_eq_equiv_comp P hPge hL' hPL₀' (fun N hN ↦ (α N hN).symm)
    hαsymm
  have h1 : IsIso (ψ₀ ≫ φ₀) := isIso_of_comp_truncMap_eq L _ fun n ↦ by
    rw [Category.assoc, ← hφα _ (hPL₀ n), ← hψα _ (hPL₀ n), Equiv.symm_apply_apply]
  have h2 : IsIso (φ₀ ≫ ψ₀) := isIso_of_comp_truncMap_eq L' _ fun n ↦ by
    rw [Category.assoc, ← hψα _ (hPL₀' n), ← hφα _ (hPL₀' n), Equiv.apply_symm_apply]
  have : Mono φ₀ := by
    have : Mono (φ₀ ≫ ψ₀) := inferInstance
    exact mono_of_mono φ₀ ψ₀
  have : IsSplitEpi φ₀ := IsSplitEpi.mk' ⟨inv (ψ₀ ≫ φ₀) ≫ ψ₀, by simp⟩
  have : IsIso φ₀ := isIso_of_mono_of_isSplitEpi φ₀
  exact ⟨asIso φ₀, hφα⟩


/-- The class of bounded below objects of `D(𝒪_X)` with quasi-coherent cohomology sheaves,
`D^+_{QCoh}(𝒪_X)`. -/
def boundedBelowQuasicoherent (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) :=
  fun N ↦ (∃ c : ℤ, N.IsGE c) ∧
    ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj N).IsQuasicoherent

/-- The truncations `τ_{≥ -n}L` of an object with quasi-coherent cohomology lie in
`D^+_{QCoh}(𝒪_X)`. -/
theorem boundedBelowQuasicoherent_truncGE (L : DerivedCategory X.Modules)
    (hL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L).IsQuasicoherent)
    (n : ℤ) : boundedBelowQuasicoherent X ((DerivedCategory.TStructure.t.truncGE n).obj L) :=
  ⟨⟨n, inferInstance⟩, fun i ↦ isQuasicoherent_homology_truncGE X L hL n i⟩

/-- **A representing object on `D^+_{QCoh}` is unique up to an isomorphism inducing the
identification.** Let `Φ : D(𝒪_X) ⥤ 𝒟` be a functor and `E` an object of `𝒟`. Let `L`, `L'` be
objects of `D(𝒪_X)` with quasi-coherent cohomology, and let `P` be a class of bounded below
objects containing `D^+_{QCoh}(𝒪_X)`'s truncations of `L` and `L'` (for instance
`boundedBelowQuasicoherent X` itself). If both represent `N ↦ Hom(E, Φ N)` on `P` — bijections
`θ_N : Hom(L, N) ≃ Hom(E, Φ N)` and `θ'_N : Hom(L', N) ≃ Hom(E, Φ N)`, natural in `N ∈ P` —
then there is an isomorphism `φ : L' ≅ L` with `θ'_N(φ ∘ x) = θ_N(x)` for all `N ∈ P` and all
`x : L ⟶ N`. -/
theorem exists_iso_of_representing {𝒟 : Type*} [Category 𝒟]
    (Φ : DerivedCategory X.Modules ⥤ 𝒟) (E : 𝒟)
    (P : ObjectProperty (DerivedCategory X.Modules))
    (hPge : ∀ N : DerivedCategory X.Modules, P N → ∃ m : ℤ, N.IsGE m)
    (L L' : DerivedCategory X.Modules)
    (hL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L).IsQuasicoherent)
    (hL' : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj L').IsQuasicoherent)
    (hPL : ∀ n : ℕ, P ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L))
    (hPL' : ∀ n : ℕ, P ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj L'))
    (θ : ∀ N : DerivedCategory X.Modules, P N → ((L ⟶ N) ≃ (E ⟶ Φ.obj N)))
    (hθ : ∀ {N N' : DerivedCategory X.Modules} (hN : P N) (hN' : P N') (g : N ⟶ N')
      (x : L ⟶ N), θ N' hN' (x ≫ g) = θ N hN x ≫ Φ.map g)
    (θ' : ∀ N : DerivedCategory X.Modules, P N → ((L' ⟶ N) ≃ (E ⟶ Φ.obj N)))
    (hθ' : ∀ {N N' : DerivedCategory X.Modules} (hN : P N) (hN' : P N') (g : N ⟶ N')
      (x : L' ⟶ N), θ' N' hN' (x ≫ g) = θ' N hN x ≫ Φ.map g) :
    ∃ φ : L' ≅ L, ∀ (N : DerivedCategory X.Modules) (hN : P N) (x : L ⟶ N),
      θ' N hN (φ.hom ≫ x) = θ N hN x := by
  obtain ⟨φ, hφ⟩ := exists_iso_of_natural_homEquiv P hPge L L' hL hL' hPL hPL'
    (fun N hN ↦ (θ N hN).trans (θ' N hN).symm)
    (fun hN hN' g x ↦ by
      simp only [Equiv.trans_apply]
      rw [hθ hN hN', Equiv.symm_apply_eq, hθ' hN hN', Equiv.apply_symm_apply])
  refine ⟨φ, fun N hN x ↦ ?_⟩
  rw [← hφ N hN x]
  simp

end Stacks.Cohomology.RelativeExtCanonical

end
