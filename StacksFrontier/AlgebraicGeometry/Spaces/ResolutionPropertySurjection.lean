module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardFiniteTypeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyLocalSplitting

/-!
# The surjection `⨁ π_*(ℐ^{n_i}) ⟶ ℱ` of Stacks 0GUZ

In the situation of [Stacks, Tag 0GUY] with `X` Noetherian, every coherent `𝒪_X`-module `ℱ` is a
quotient of a finite direct sum `⨁_i π_*(ℐ^{n_i})`.

## The proof

The source's `π^*ℱ ⊗ ω_{Y/X}` and its trace are replaced by the right adjoint `𝒢 = π^!ℱ` of `π_*`
(`AlgebraicGeometry.Space.affinePushforwardRightAdjoint`), with `π_*𝒢 ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` and
the trace the counit `π_*𝒢 ⟶ ℱ` (evaluation at `1`).

1. `𝒢` is coherent (`AlgebraicGeometry.Space.isCoherent_affinePushforwardRightAdjoint_obj`).
2. Finitely many `s'_i : ℐ^{n_i} ⟶ 𝒢` restrict to generators of `𝒢` over `V = Y ∖ V(ℐ)` (Stacks
   07UM), so their cokernel `𝒬` is killed by some `ℐ^m` (Stacks 07UK)
   (`AlgebraicGeometry.Space.exists_idealPowModule_homs_cokernel_smul_eq_zero`).
3. `σ = Tr ∘ ⨁ π_*(s'_i)`.  Near each point of `V` there is an étale `g : U ⟶ X` with a split
   section of `(π_*𝒪_Y)|_U` through `(π_*ℐ^m)|_U`
   (`AlgebraicGeometry.Space.exists_etale_split_section_factorsThrough_idealSheafPow`), and then
   `σ|_U` is surjective
   (`AlgebraicGeometry.Space.epi_etaleModulePullback_map_comp_counit_of_killed`).
4. These `U` cover `X` since `V ⟶ X` is surjective, and surjectivity descends along a jointly
   surjective family of flat morphisms.

## Main results

* `AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward`: **Stacks 0GUZ**.
* `AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward_of_le`: the same with all
  the integers `n_i` at least a prescribed `N`, which the converse of Stacks 0GV0 consumes with
  `N = 1`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModules_resolutionPropertySurjection
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-- **An additive functor keeps a map out of a finite direct sum zero once it is zero on each
summand.**  The comparison `⨁ F(fⱼ) ⟶ F(⨁ fⱼ)` has the section `F(⨁ fⱼ) ⟶ ⨁ F(fⱼ)` given by the
projections, so it can be cancelled. -/
theorem map_biproduct_desc_comp_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {J : Type} [Finite J] {f : J → C} [HasBiproduct f]
    [HasBiproduct fun j => F.obj (f j)] {Z : C} (Ψ : ∀ j, f j ⟶ Z) {T : D} (d : F.obj Z ⟶ T)
    (h : ∀ j, F.map (Ψ j) ≫ d = 0) : F.map (biproduct.desc Ψ) ≫ d = 0 := by
  cases nonempty_fintype J
  have hsc : biproduct.lift (fun j => F.map (biproduct.π f j)) ≫
      biproduct.desc (fun j => F.map (biproduct.ι f j)) = 𝟙 _ := by
    rw [biproduct.lift_desc]
    simp_rw [← F.map_comp]
    rw [← F.map_sum, biproduct.total, F.map_id]
  have hc : biproduct.desc (fun j => F.map (biproduct.ι f j)) ≫ F.map (biproduct.desc Ψ) ≫ d =
      0 := by
    refine biproduct.hom_ext' _ _ fun j => ?_
    rw [biproduct.ι_desc_assoc, ← F.map_comp_assoc, biproduct.ι_desc, h j, comp_zero]
  rw [← Category.id_comp (F.map _ ≫ d), ← hsc, Category.assoc, hc, comp_zero]

/-- **A cokernel property survives étale restriction**: if every map out of `𝒩` killing `ψ`
factors through `q`, the same holds after the étale restriction `g^*`, which is a left adjoint. -/
theorem exists_factor_etaleModulePullback_map {X U : AlgebraicSpaces B S hS} (g : U ⟶ X)
    (hg : IsEtale B S hS g.hom) {M N Q : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ N) (q : N ⟶ Q)
    (h : ∀ ⦃T : Modules.{u, u} B S hS X.1 X.2⦄ (d : N ⟶ T), ψ ≫ d = 0 → ∃ d₀ : Q ⟶ T, d = q ≫ d₀)
    ⦃Z : Modules.{u, u} B S hS U.1 U.2⦄ (d : (etaleModulePullback B S hS g hg).obj N ⟶ Z)
    (hd : (etaleModulePullback B S hS g hg).map ψ ≫ d = 0) :
    ∃ d'' : (etaleModulePullback B S hS g hg).obj Q ⟶ Z,
      d = (etaleModulePullback B S hS g hg).map q ≫ d'' := by
  let adj := etaleModulePullbackAdjunction B S hS g hg
  have h0 : ψ ≫ adj.homEquiv _ _ d = 0 := by
    rw [← adj.homEquiv_naturality_left, hd, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  obtain ⟨d₀, hd₀⟩ := h _ h0
  refine ⟨(adj.homEquiv _ _).symm d₀, ?_⟩
  rw [← adj.homEquiv_naturality_left_symm, ← hd₀, Equiv.symm_apply_apply]

variable (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **Stacks 0GUZ, with a lower bound on the exponents.**  In the situation of Stacks 0GUY — a
quasi-compact and quasi-separated algebraic space `X`, a surjective étale `φ : V ⟶ X` from an
affine scheme factored as an open immersion `j : V ⟶ Y` followed by a finite `π : Y ⟶ X`, and a
finite type quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_Y` with `V(ℐ) = Y ∖ j(V)` — assume `X`
Noetherian.  Then every coherent `𝒪_X`-module `ℱ` admits, for some `r ≥ 0` and integers
`n_1, …, n_r ≥ 0`, a surjection

`⨁_{i = 1}^{r} π_*(ℐ^{n_i}) ⟶ ℱ`

of `𝒪_X`-modules, and the integers can be taken `≥ N` for any prescribed `N`.  See the module
documentation for the proof; the lower bound comes from
`AlgebraicGeometry.Space.exists_idealPowModule_homs_eq_zero_of_restrict_of_le`. -/
theorem exists_epi_biproduct_idealSheafPowPushforward_of_le (hX : IsNoetherian B S hS hZ X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (N : ℕ) :
    ∃ (r : ℕ) (n : Fin r → ℕ) (_ : ∀ i, N ≤ n i)
      (_ : HasBiproduct fun i =>
        idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i))
      (σ : (⨁ fun i => idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i)) ⟶
        F), Epi σ := by
  let π := D.piHom B S hS hZ X hqc hqs
  have hπA : IsAffineHom B S hS π.hom := D.isFinite_π.isAffineHom
  have hNo := isNoetherian_Y_of_resolutionSituation B S hS hZ X hqc hqs D hX
  have : Fact (HasEtaleLocalProperty B S hS D.Y.1
    (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hNo.2.2⟩
  have hA : IsCoherent B S hS X.1 X.2 (pushforwardStructureModule B S hS π) :=
    isCoherent_modulePushforward_of_isFinite' B S hS π D.isFinite_π hX.2.2 _
      (isCoherent_structureSheaf B S hS D.Y.1 D.Y.2)
  have hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite :=
    SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite _ hA.toIsCoherentOnSite
  -- the module `𝒢 = π^!ℱ`
  have hG := isCoherent_affinePushforwardRightAdjoint_obj B S hS π D.isFinite_π hX.2.2 hNo.2.2 F hF
  obtain ⟨r, n, hB, Ψ, m, hN, hsum, hQ, hK⟩ :=
    exists_idealPowModule_homs_cokernel_smul_eq_zero_of_le B S hS hZ X hqc hqs D hX _ hG N
  have hA' : ∀ i, @Eq (Modules.{u, u} B S hS D.Y.1 D.Y.2)
      (SheafOfModules.idealSheafPow D.I (n i)).toSheafOfModules
      (idealPowModule D.I (n i) (SheafOfModules.unit (structureRingSheaf B S hS D.Y))) := fun i =>
    congrArg SheafOfModules.Submodule.toSheafOfModules
      (idealSheafPow_eq_idealPowSubmodule B S hS D.Y D.I (n i))
  have hB' : HasBiproduct fun i =>
      idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i) :=
    HasBiproduct.of_hasProduct _
  let ψ₀ : (⨁ fun i => idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i)) ⟶
      (modulePushforward B S hS π).obj ((affinePushforwardRightAdjoint B S hS π).obj F) :=
    biproduct.desc fun i => (modulePushforward B S hS π).map (eqToHom (hA' i)) ≫
      (modulePushforward B S hS π).map (Ψ i)
  -- `π_*` keeps the cokernel of `⨁ s'_i`
  have hcokX : ∀ ⦃T : Modules.{u, u} B S hS X.1 X.2⦄
      (d : (modulePushforward B S hS π).obj ((affinePushforwardRightAdjoint B S hS π).obj F) ⟶ T),
      ψ₀ ≫ d = 0 → ∃ d₀ : (modulePushforward B S hS π).obj (cokernel (biproduct.desc Ψ)) ⟶ T,
        d = (modulePushforward B S hS π).map (cokernel.π (biproduct.desc Ψ)) ≫ d₀ := by
    intro T d hd
    have hcan : ∀ {A₁ A₂ : Modules.{u, u} B S hS D.Y.1 D.Y.2} (h : A₁ = A₂)
        {Gm : Modules.{u, u} B S hS D.Y.1 D.Y.2} (f : A₂ ⟶ Gm) {T : Modules.{u, u} B S hS X.1 X.2}
        (d : (modulePushforward B S hS π).obj Gm ⟶ T),
        (modulePushforward B S hS π).map (eqToHom h) ≫ (modulePushforward B S hS π).map f ≫ d =
          0 → (modulePushforward B S hS π).map f ≫ d = 0 := by
      intro A₁ A₂ h Gm f T d hd
      subst h
      simpa only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp] using hd
    have h1 : ∀ i, (modulePushforward B S hS π).map (Ψ i) ≫ d = 0 := fun i => by
      have h := congrArg (fun k => biproduct.ι _ i ≫ k) hd
      simp only [ψ₀, biproduct.ι_desc_assoc, comp_zero, Category.assoc] at h
      exact hcan (hA' i) (Ψ i) d h
    have h2 : (modulePushforward B S hS π).map (biproduct.desc Ψ) ≫ d = 0 := by
      have : (modulePushforward B S hS π).Additive := inferInstance
      have : HasBiproduct fun i => (modulePushforward B S hS π).obj
          (idealPowModule D.I (n i) (SheafOfModules.unit (structureRingSheaf B S hS D.Y))) :=
        HasBiproduct.of_hasProduct _
      exact map_biproduct_desc_comp_eq_zero (modulePushforward B S hS π) Ψ d h1
    exact exists_factor_modulePushforward_map_cokernelπ B S hS π hπA (biproduct.desc Ψ)
      hsum.toIsQuasicoherentOnSite hG.toIsQuasicoherentOnSite
      (isCoherent_kernel B S hS D.Y.1 D.Y.2 hG hQ _).toIsQuasicoherentOnSite
      hQ.toIsQuasicoherentOnSite d h2
  let e := moduleDirectImage_affinePushforwardRightAdjointIso B S hS π hπA hfp F
    hF.toIsQuasicoherentOnSite
  let σ := ((ψ₀ : _ ⟶ (directImageAlgebraRestrictScalars B S hS π).obj
      ((moduleDirectImage B S hS π).obj ((affinePushforwardRightAdjoint B S hS π).obj F))) ≫
      (directImageAlgebraRestrictScalars B S hS π).map e.inv) ≫
      (directImageAlgebraRestrictCoextendAdjunction B S hS π).counit.app F
  refine ⟨r, n, hN, hB', σ, ?_⟩
  -- surjectivity near every point of `V`
  have hloc : ∀ v : points B S hS (yoneda.obj D.V), ∃ (U : AlgebraicSpaces B S hS) (g : U ⟶ X)
      (hg : IsEtale B S hS g.hom) (u : points B S hS U.1),
      pointsMap B S hS U.1 g.hom u = pointsMap B S hS (yoneda.obj D.V) D.φ v ∧
      Epi ((etaleModulePullback B S hS g hg).map σ) := by
    intro v
    obtain ⟨U, g, hg, u, hu, εK, ε, pr, hfac, hε⟩ :=
      exists_etale_split_section_factorsThrough_idealSheafPow B S hS hZ X hqc hqs D m v
    exact ⟨U, g, hg, u, hu, epi_etaleModulePullback_map_comp_counit_of_killed B S hS π g hg F e
      ψ₀ (cokernel.π (biproduct.desc Ψ))
      (exists_factor_etaleModulePullback_map B S hS g hg ψ₀ _ hcokX)
      (SheafOfModules.idealSheafPow D.I m) hK εK ε hfac pr hε⟩
  choose U g hg u hu hepi using hloc
  refine epi_of_forall_epi_modulePullback_map_of_isFlat B S hS g
    (fun v => isFlat_of_isEtale B S hS (hg v)) ?_ _ fun v => ?_
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨v, hv⟩ := D.isSurjective_φ x
    exact Set.mem_iUnion.2 ⟨v, u v, (hu v).trans hv⟩
  · have := hepi v
    rw [← NatIso.naturality_2 (modulePullbackIsoEtaleModulePullback B S hS (g v) (hg v))]
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom
      ((modulePullbackIsoEtaleModulePullback B S hS (g v) (hg v)).app _))) _
      (@epi_comp _ _ _ _ _ _ (hepi v) _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv
        ((modulePullbackIsoEtaleModulePullback B S hS (g v) (hg v)).app _))))

/-- **Stacks 0GUZ.**  In the situation of Stacks 0GUY — a quasi-compact and quasi-separated
algebraic space `X`, a surjective étale `φ : V ⟶ X` from an affine scheme factored as an open
immersion `j : V ⟶ Y` followed by a finite `π : Y ⟶ X`, and a finite type quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_Y` with `V(ℐ) = Y ∖ j(V)` — assume `X` Noetherian.  Then every coherent
`𝒪_X`-module `ℱ` admits, for some `r ≥ 0` and integers `n_1, …, n_r ≥ 0`, a surjection

`⨁_{i = 1}^{r} π_*(ℐ^{n_i}) ⟶ ℱ`

of `𝒪_X`-modules.  This is
`AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward_of_le` at `N = 0`. -/
@[stacks 0GUZ]
theorem exists_epi_biproduct_idealSheafPowPushforward (hX : IsNoetherian B S hS hZ X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    ∃ (r : ℕ) (n : Fin r → ℕ)
      (_ : HasBiproduct fun i =>
        idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i))
      (σ : (⨁ fun i => idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I (n i)) ⟶
        F), Epi σ := by
  obtain ⟨r, n, -, hB, σ, hσ⟩ :=
    exists_epi_biproduct_idealSheafPowPushforward_of_le B S hS hZ X hqc hqs D hX F hF 0
  exact ⟨r, n, hB, σ, hσ⟩

end AlgebraicGeometry.Space

end
