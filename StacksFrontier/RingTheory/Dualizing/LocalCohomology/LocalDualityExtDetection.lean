module

public import StacksFrontier.Homology.DerivedComplete.CompletionUnitDenseModIdeal
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExtVanishing
public import StacksFrontier.RingTheory.LocalCohomology.UniformVanishingSpread

/-!
# Reading a vanishing of Ext modules back as a vanishing of local cohomology

Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a normalized dualizing complex, let
`ι : κ ⟶ E` be an injective hull of the residue field and let `Z = V(𝔪)`. For a morphism
`g : K' ⟶ K` of `D(A)`, the lemma
`Dualizing.LocalDuality.comp_eq_zero_of_homologyMap_localCohomology_eq_zero` carries the
vanishing of `H^i_Z(g)` over to the vanishing of the Ext map
`Ext^{-i}_A(K, ω) ⟶ Ext^{-i}_A(K', ω)`. This module proves the **converse**, which is the step
the uniformity paragraph of [Stacks, Tag 0EFX] needs on the way back: once a bound has been made
uniform on the finite Ext modules it has to be returned to local cohomology.

The converse is not formal. Local duality identifies the Matlis dual `Hom_A(H^i_Z(K), E)` with
the `𝔪`-adic *completion* of `Ext^{-i}_A(K, ω)`, so the functionals on `H^i_Z(K)` coming from
morphisms `K ⟶ ω⟦-i⟧` do not exhaust the dual — they only generate it modulo `𝔪`. Two inputs
close that gap.

* `Stacks.Algebraization.range_homologyMap_derivedCompletionUnit_sup_smul_eq_top`: the derived
  completion unit is surjective modulo the ideal on degree-zero cohomology, so the image of the
  local duality map together with `𝔪 · Hom_A(H^i_Z(K), E)` is the whole dual.
* `Stacks.LocalCohomology.eq_zero_of_forall_mem_comp_eq_zero_of_sup_eq_top`: a map into an
  `𝔪`-power-torsion module is already zero when the functionals killing it generate the dual
  modulo `𝔪`, the socle of the injective hull providing the one nonzero element killed by `𝔪`
  that the detection needs.

The `𝔪`-power torsion of `H^i_Z(K)` is not a hypothesis: it is the defining property of the
objects in the image of `Dualizing.localCohomologyFunctor`.

## Main results

* `Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero` — the
  converse transport: if `g ≫ u = 0` for every `u : K ⟶ ω⟦-i⟧` then `H^i_Z(g) = 0`.
* `Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero_of_bounded` —
  the same with the finiteness side condition on `RHom_A(K, ω⟦-i⟧)` discharged from boundedness
  and finiteness of the cohomology of `K` and of `ω⟦-i⟧`.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Dualizing.LocalDuality

variable (A : Type u) [CommRing A]

/-- **The socle element of an injective hull of the residue field.** The image of `1` under an
injective hull `ι : κ ⟶ E` is a nonzero element of `E` annihilated by the maximal ideal. -/
theorem exists_ne_zero_maximalIdeal_smul_eq_zero_of_isInjectiveHull
    [IsLocalRing A] {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E) [Mono ι] :
    ∃ e : (E : Type u), e ≠ 0 ∧ ∀ a ∈ IsLocalRing.maximalIdeal A, a • e = 0 := by
  have hinj : Function.Injective ι.hom := (ModuleCat.mono_iff_injective ι).1 inferInstance
  set x₀ : ((ModuleCat.uliftFunctor.{u} A).obj
    (ModuleCat.of A (IsLocalRing.ResidueField A)) : Type u) :=
    ULift.up (1 : IsLocalRing.ResidueField A) with hx₀
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg ULift.down h)
  have hsm : ∀ a ∈ IsLocalRing.maximalIdeal A, a • x₀ = 0 := by
    intro a ha
    refine ULift.ext _ _ ?_
    show a • (1 : IsLocalRing.ResidueField A) = 0
    rw [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  refine ⟨ι.hom x₀, fun h => hx₀ne (hinj (h.trans (map_zero ι.hom).symm)), fun a ha => ?_⟩
  rw [← map_smul ι.hom a x₀, hsm a ha, map_zero]

/-- **The vanishing of the Ext maps transported back to local cohomology.** Let `(A, 𝔪, κ)` be a
Noetherian local ring, let `f` generate `𝔪`, let `ω` be a normalized dualizing complex, let
`ι : κ ⟶ E` be an injective hull of the residue field and let `Z = V(𝔪)`. Let `g : K' ⟶ K` be a
morphism of `D(A)` such that `g ≫ u = 0` for every `u : K ⟶ ω⟦-i⟧` — that is, the Ext map
`Ext^{-i}_A(K, ω) ⟶ Ext^{-i}_A(K', ω)` is zero — and suppose the cohomology modules of
`RHom_A(K, ω⟦-i⟧)` are finite. Then `H^i_Z(g) = 0`.

*Argument.* Let `θ` be the family of local duality isomorphisms
`H⁰(RHom_A(-, ω⟦-i⟧)^∧) ≅ Hom_A(H^i_Z(-), E)` of
`Dualizing.LocalDuality.exists_localDualityExtNatEquiv`, and let `W` be the image under `θ K` of
the image of the derived completion unit on `H⁰(RHom_A(K, ω⟦-i⟧))`. Each member of `W` kills
`H^i_Z(g)`: by the naturality square of `θ`, the composite of `θ K` of the unit's value at a
class is `θ K'` of the completed precomposition by `g` applied to that class, and the unit is
natural, so this is `θ K'` of the unit's value at the image of the class under the Ext map, which
vanishes by hypothesis — every class of `H⁰(RHom_A(K, ω⟦-i⟧))` being `Ext^{-i}` of a morphism
`u : K ⟶ ω⟦-i⟧` through `Dualizing.extHomologyZeroLinearEquiv`. And `W` generates the dual modulo
`𝔪`, because the derived completion unit is surjective modulo `𝔪` on degree-zero cohomology and
`θ K` is an isomorphism. The detection lemma then forces `H^i_Z(g)` to vanish. -/
theorem homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero
    [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (hfin : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (op K, (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω))))
    (hExt : ∀ u : K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω,
      g ≫ u = 0) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
        (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g) = 0 := by
  classical
  have : Module.Injective A (E : Type u) :=
    (Module.injective_iff_injective_object A (E : Type u)).mpr hι.1
  obtain ⟨e, he, hme⟩ := exists_ne_zero_maximalIdeal_smul_eq_zero_of_isInjectiveHull A ι
  set Wsh := (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω
    with hWsh
  set RH : DerivedCategory (ModuleCat.{u} A) → DerivedCategory (ModuleCat.{u} A) :=
    fun L => (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj (op L, Wsh) with hRH
  set pre : RH K ⟶ RH K' :=
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
      (show (op K, Wsh) ⟶ (op K', Wsh) from (g.op, 𝟙 Wsh)) with hpre
  -- the submodule of the dual cut out by the local duality map
  set V := LinearMap.range (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    ((DerivedCompletion.derivedCompletionUnit A f).app (RH K))).hom) with hV
  obtain ⟨θ, hθ⟩ := exists_localDualityExtNatEquiv A f hf ω hω ι hι i
  -- it generates the dual modulo the maximal ideal
  have hWtop : Submodule.map (θ K).toLinearMap V ⊔ IsLocalRing.maximalIdeal A •
      (⊤ : Submodule A (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
          (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).obj K) : Type u) →ₗ[A]
          (E : Type u))) = ⊤ := by
    have hbase := Stacks.Algebraization.range_homologyMap_derivedCompletionUnit_sup_smul_eq_top
      A f (RH K) hfin
    rw [hf] at hbase
    have hθtop : Submodule.map (θ K).toLinearMap ⊤ = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.2 (θ K).surjective
    calc Submodule.map (θ K).toLinearMap V ⊔ IsLocalRing.maximalIdeal A • ⊤
        = Submodule.map (θ K).toLinearMap V ⊔
            IsLocalRing.maximalIdeal A • Submodule.map (θ K).toLinearMap ⊤ := by rw [hθtop]
      _ = Submodule.map (θ K).toLinearMap
            (V ⊔ IsLocalRing.maximalIdeal A • (⊤ : Submodule A _)) := by
          rw [← Submodule.map_smul'', ← Submodule.map_sup]
      _ = ⊤ := by rw [hV, hbase, hθtop]
  -- every member of it kills the map on local cohomology
  have hkill : ∀ ψ ∈ Submodule.map (θ K).toLinearMap V, ψ ∘ₗ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
          (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g)).hom = 0 := by
    intro ψ hψ
    obtain ⟨y, hy, rfl⟩ := hψ
    obtain ⟨z, rfl⟩ := hy
    -- `z` is the Ext class of a morphism `u`, and the Ext map kills it
    obtain ⟨u, hu⟩ : ∃ u : K ⟶ Wsh, extHomologyZeroLinearEquiv A K Wsh u = z :=
      ⟨(extHomologyZeroLinearEquiv A K Wsh).symm z, by
        rw [LinearEquiv.apply_symm_apply]⟩
    have hpz : (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map pre)).hom z = 0 := by
      rw [← hu, ← extHomologyZeroLinearEquiv_naturality A g u, hExt u, map_zero]
    -- naturality of the completion unit
    have hnatc : (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((DerivedCompletion.derivedCompletionFunctor A f).map pre))).hom
        ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((DerivedCompletion.derivedCompletionUnit A f).app (RH K)))).hom z) = 0 := by
      have h := (DerivedCompletion.derivedCompletionUnit A f).naturality pre
      simp only [Functor.id_map] at h
      have h4 := congrArg
        (fun t => ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map t).hom z) h
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h4
      rw [← h4, hpz, map_zero]
    -- the naturality square of local duality
    have hsq := hθ K K' g ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((DerivedCompletion.derivedCompletionUnit A f).app (RH K)))).hom z)
    rw [hnatc, map_zero] at hsq
    exact hsq.symm
  -- the detection lemma
  refine ModuleCat.hom_ext ?_
  refine Stacks.LocalCohomology.eq_zero_of_forall_mem_comp_eq_zero_of_sup_eq_top
    e he hme (fun z => ?_) _ (Submodule.map (θ K).toLinearMap V) hWtop hkill
  obtain ⟨n, -, hn⟩ :=
    ((Dualizing.localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _)).obj K).property i z
  exact ⟨n, hn⟩

/-- **The converse transport, with the finiteness side condition discharged.** The hypothesis on
the cohomology of `RHom_A(K, ω⟦-i⟧)` in
`Dualizing.LocalDuality.homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero` holds
whenever `K` is bounded above and `ω⟦-i⟧` bounded below, both with finite cohomology modules, by
`StacksDraft.DerivedHom.finite_homology_derivedHom`. That is the shape in which the hypothesis is
met in the proof of [Stacks, Tag 0EFX], where `K` is a finite module in degree zero and `ω` is a
dualizing complex. -/
theorem homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero_of_bounded
    [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K) (d b : ℤ)
    (hKle : K.IsLE d)
    (hωge : ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω).IsGE b)
    (hKfin : ∀ k : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj K))
    (hωfin : ∀ k : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω)))
    (hExt : ∀ u : K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω,
      g ≫ u = 0) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
        (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).map g) = 0 :=
  homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero A f hf ω hω ι hι i g
    (fun n => StacksDraft.DerivedHom.finite_homology_derivedHom
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)) K
      ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) d b
      hKle hωge hKfin hωfin n) hExt

end Dualizing.LocalDuality

end
