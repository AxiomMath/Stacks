module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineTopCompactSupportCard
public import StacksFrontier.RingTheory.FiniteRingRankOneModule

/-!
# `H²_c(𝔸¹_k̄, Λ)` is free of rank one over `Λ`

Let `k` be a finite field, `Λ` a finite commutative ring in which `#k` is invertible and `k̄` an
algebraically closed extension of `k`. Then `H²_c(𝔸¹_k̄, Λ) ≅ Λ` as `Λ`-modules, for every
compactification of `𝔸¹_k`.

`E = H²_c(𝔸¹_k̄, Λ)` has `#Λ` elements
(`Stacks.EtaleCohomology.natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine`).
For a maximal ideal `𝔪`, `H²_c` is right exact on finite modules (`H³_c = 0`), so
`E / Im H²_c(𝔪) ≅ H²_c(Λ/𝔪)` has `#(Λ/𝔪)` elements; and `Im H²_c(𝔪) ⊆ 𝔪E`, because `𝔪` is the
image of `⊕_{a ∈ 𝔪} Λ ⟶ Λ, (x_a) ↦ ∑ a x_a`, on which `H²_c` is `∑ a · H²_c(pr_a)` by
`Λ`-linearity (`Stacks.EtaleCohomology.compactSupportSheafCohomology_linear`). Hence
`#(E/𝔪E) ≤ #(Λ/𝔪)`, and `E ≅ Λ` by `Stacks.FiniteRingRankOne.nonempty_linearEquiv_self_of_natCard`.
This is the computation `R Γ_c(𝔸¹_k̄, Λ) = Λ(-1)[-2]` (up to the twist) in degree two, as used for
the invertibility of `H²(R f_! Λ)` in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exact_compactSupportSheafCohomology_map_of_shortExact`.
* `Stacks.EtaleCohomology.surjective_compactSupportSheafCohomology_map_of_shortExact`.
* `nonempty_linearEquiv_compactSupportSheafCohomology_two_constantSheaf_affineLine`, in namespace
  `Stacks.EtaleCohomology`.

## Implementation notes

`Stacks.EtaleCohomology.compactSupportSheafCohomology` lives in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section ShortExact

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- A sheaf placed in degree zero is a bounded below complex. -/
private theorem plus_single_obj (M : EtaleModules.{u, 0} Λ X) :
    CochainComplex.plus _ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) :=
  ⟨0, inferInstance⟩

/-- **`Hⁱ_c(X_k̄, -)` is exact in the middle** on a short exact sequence of sheaves. -/
theorem exact_compactSupportSheafCohomology_map_of_shortExact
    {T : ShortComplex (EtaleModules.{u, 0} Λ X)} (hT : T.ShortExact) (i : ℤ) :
    Function.Exact ((compactSupportSheafCohomology Λ f j kbar i).map T.f).hom
      ((compactSupportSheafCohomology Λ f j kbar i).map T.g).hom := by
  have := Fintype.ofFinite k
  exact exact_homology_compactSupportFrobeniusFunctor_map Λ f j kbar
    (hT.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0))
    (plus_single_obj Λ _) (plus_single_obj Λ _) (plus_single_obj Λ _) i

/-- **`Hⁱ_c(X_k̄, G₂) → Hⁱ_c(X_k̄, G₃)` is onto when `Hⁱ⁺¹_c(X_k̄, G₁) = 0`**, for a short exact
sequence `0 → G₁ → G₂ → G₃ → 0` of sheaves. -/
theorem surjective_compactSupportSheafCohomology_map_of_shortExact
    {T : ShortComplex (EtaleModules.{u, 0} Λ X)} (hT : T.ShortExact) (i i₁ : ℤ) (hi : i + 1 = i₁)
    (h : Subsingleton ((compactSupportSheafCohomology Λ f j kbar i₁).obj T.X₁)) :
    Function.Surjective ((compactSupportSheafCohomology Λ f j kbar i).map T.g).hom := by
  have := Fintype.ofFinite k
  exact (ModuleCat.epi_iff_surjective _).1 (epi_homology_compactSupportFrobeniusFunctor_map_g Λ f j
    kbar (hT.map_of_exact
      (HomologicalComplex.single (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0))
    (plus_single_obj Λ _) (plus_single_obj Λ _) (plus_single_obj Λ _) i i₁ hi
    (@ModuleCat.isZero_of_subsingleton _ _ _ h))

end ShortExact

/-- The constant sheaf functor on `𝔸¹_k` preserves finite colimits. -/
private theorem preservesFiniteColimits_affineLineConstantSheaf (k : Type u) [Field k]
    (Λ : Type) [CommRing Λ] :
    PreservesFiniteColimits (affineLineConstantSheaf k Λ) :=
  have := (constantSheafAdj (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtaleMkId (Spec (.of k[X])))).leftAdjoint_preservesColimits
  inferInstance

section RankOne

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar]

include kbar in
/-- **`H²_c(𝔸¹_k̄, -)` carries a surjection of finite modules to a surjection**, `#k` invertible
in `Λ`: the kernel has `H³_c = 0`. -/
theorem surjective_compactSupportSheafCohomology_two_map_constantSheaf_of_surjective
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    {M N : ModuleCat.{u + 1} Λ} [Finite M] (g : M ⟶ N) (hg : Function.Surjective g.hom) :
    Function.Surjective ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2).map
      ((affineLineConstantSheaf k Λ).map g)).hom := by
  let F := affineLineConstantSheaf k Λ
  have := preservesFiniteColimits_affineLineConstantSheaf k Λ
  let K := LinearMap.ker g.hom
  let T := ModuleCat.shortComplexOfCompEqZero K.subtype g.hom (by ext x; exact x.2)
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T
    (LinearMap.exact_subtype_ker_map g.hom) K.injective_subtype hg
  have : Finite T.X₁ := inferInstanceAs (Finite K)
  exact surjective_compactSupportSheafCohomology_map_of_shortExact Λ (affineLineStructureMap k) j
    kbar (hT.map_of_exact F) 2 3 (by norm_num)
    (subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine k Λ kbar hq j 3
      (by norm_num) T.X₁)

include kbar in
/-- **`H²_c(𝔸¹_k̄, Λ) ≅ Λ` as `Λ`-modules**, for a finite ring `Λ` in which `#k` is invertible
and any compactification of `𝔸¹_k`. -/
theorem nonempty_linearEquiv_compactSupportSheafCohomology_two_constantSheaf_affineLine
    (hq : IsUnit (Fintype.card k : Λ))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k))) :
    Nonempty ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k Λ).obj (ModuleCat.of Λ (ULift.{u + 1} Λ))) ≃ₗ[Λ] Λ) := by
  let H := compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2
  let F := affineLineConstantSheaf k Λ
  let A := ModuleCat.of Λ (ULift.{u + 1} Λ)
  have : Finite A := inferInstanceAs (Finite (ULift.{u + 1} Λ))
  have := preservesFiniteColimits_affineLineConstantSheaf k Λ
  have hFl : Functor.Linear Λ F :=
    inferInstanceAs (Functor.Linear Λ (Functor.const (Spec (.of k[X])).Etaleᵒᵖ ⋙
      presheafToSheaf (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  have hHa := compactSupportSheafCohomology_additive Λ (affineLineStructureMap k) j kbar 2
  have hHl := compactSupportSheafCohomology_linear Λ (affineLineStructureMap k) j kbar 2
  have hE : Nat.card (H.obj (F.obj A)) = Nat.card Λ :=
    (natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine k Λ kbar hq j A).trans
      (Nat.card_ulift Λ)
  have : Finite (H.obj (F.obj A)) :=
    Nat.finite_of_card_ne_zero (by rw [hE]; exact Nat.card_pos.ne')
  refine Stacks.FiniteRingRankOne.nonempty_linearEquiv_self_of_natCard hE fun 𝔪 h𝔪 => ?_
  classical
  let : Fintype 𝔪 := Fintype.ofFinite 𝔪
  -- `𝔪` inside `A = Λ`, and the surjection `⊕_{a ∈ 𝔪} Λ ⟶ 𝔪`
  let e : ULift.{u + 1} Λ ≃ₗ[Λ] Λ := ULift.moduleEquiv
  let N : Submodule Λ (ULift.{u + 1} Λ) := Submodule.map e.symm.toLinearMap 𝔪
  let P := ModuleCat.of Λ (𝔪 → ULift.{u + 1} Λ)
  have : Finite P := inferInstanceAs (Finite (𝔪 → ULift.{u + 1} Λ))
  let pM : P ⟶ A := ∑ a : 𝔪, ModuleCat.ofHom (LinearMap.proj a) ≫ ((a : Λ) • 𝟙 A)
  have hpM : ∀ w : 𝔪 → ULift.{u + 1} Λ, pM.hom w = ∑ a : 𝔪, (a : Λ) • w a := fun w => by
    rw [ModuleCat.hom_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => rfl
  have hpN : ∀ w, pM.hom w ∈ N := fun w => by
    rw [hpM]
    exact Submodule.sum_mem _ fun a _ => ⟨(a : Λ) * (w a).down, 𝔪.mul_mem_right _ a.2, rfl⟩
  let p' : (𝔪 → ULift.{u + 1} Λ) →ₗ[Λ] N := LinearMap.codRestrict N pM.hom hpN
  have hp' : Function.Surjective p' := by
    rintro ⟨y, b, hb, rfl⟩
    refine ⟨Pi.single ⟨b, hb⟩ (ULift.up 1), Subtype.ext ?_⟩
    change pM.hom (Pi.single ⟨b, hb⟩ (ULift.up 1)) = e.symm b
    rw [hpM, Finset.sum_eq_single (⟨b, hb⟩ : 𝔪) (fun a _ ha => by rw [Pi.single_eq_of_ne ha,
      smul_zero]) (by simp), Pi.single_eq_same]
    change ULift.up (b * 1) = ULift.up b
    rw [mul_one]
  let NM := ModuleCat.of Λ N
  have : Finite NM := inferInstanceAs (Finite N)
  let ι : NM ⟶ A := ModuleCat.ofHom N.subtype
  have hfac : ModuleCat.ofHom p' ≫ ι = pM := by
    ext w
    rfl
  -- `Im H²_c(ι) ⊆ 𝔪 E`
  have hsurj' := surjective_compactSupportSheafCohomology_two_map_constantSheaf_of_surjective k Λ
    kbar hq j (ModuleCat.ofHom p' : P ⟶ NM) hp'
  have hrange :
      LinearMap.range (H.map (F.map ι)).hom ≤ 𝔪 • (⊤ : Submodule Λ (H.obj (F.obj A))) := by
    rintro y ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hsurj' z
    have hcomp : (H.map (F.map ι)).hom ((H.map (F.map (ModuleCat.ofHom p'))).hom w) =
        ((F ⋙ H).map pM).hom w := by
      rw [← hfac, Functor.map_comp]
      rfl
    rw [hcomp]
    have hmap : (F ⋙ H).map pM =
        ∑ a : 𝔪, (F ⋙ H).map (ModuleCat.ofHom (LinearMap.proj a)) ≫
          ((a : Λ) • (F ⋙ H).map (𝟙 A)) := by
      simp only [pM, Functor.map_sum, Functor.map_comp, Functor.map_smul]
    rw [hmap, ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem_smul a.2 Submodule.mem_top
  -- `E / Im H²_c(ι) ≅ H²_c(Λ/𝔪)`
  let T := ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext; simp)
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T (LinearMap.exact_subtype_mkQ N)
    N.injective_subtype N.mkQ_surjective
  have : Finite T.X₁ := inferInstanceAs (Finite N)
  have : Finite T.X₃ := Finite.of_surjective _ N.mkQ_surjective
  have hex := exact_compactSupportSheafCohomology_map_of_shortExact Λ (affineLineStructureMap k) j
    kbar (hT.map_of_exact F) 2
  have hsurj := surjective_compactSupportSheafCohomology_two_map_constantSheaf_of_surjective k Λ
    kbar hq j (ModuleCat.ofHom N.mkQ : A ⟶ ModuleCat.of Λ (ULift.{u + 1} Λ ⧸ N)) N.mkQ_surjective
  have hQ : Nat.card (H.obj (F.obj A) ⧸ LinearMap.range (H.map (F.map ι)).hom) =
      Nat.card (Λ ⧸ 𝔪) := by
    have h1 : Nat.card (H.obj (F.obj A) ⧸ LinearMap.range (H.map (F.map ι)).hom) =
        Nat.card (H.obj (F.obj T.X₃)) := by
      have hk := hex.linearMap_ker_eq
      change LinearMap.ker (H.map (F.map T.g)).hom = LinearMap.range (H.map (F.map ι)).hom at hk
      rw [← hk]
      exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hsurj).toEquiv
    rw [h1, natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine k Λ kbar hq j T.X₃]
    exact (Nat.card_congr (Submodule.Quotient.equiv 𝔪 N e.symm rfl).toEquiv).symm
  rw [← hQ]
  have : Finite (H.obj (F.obj A) ⧸ LinearMap.range (H.map (F.map ι)).hom) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact Nat.card_le_card_of_surjective _ (Submodule.factor_surjective hrange)

end RankOne

end Stacks.EtaleCohomology

end
