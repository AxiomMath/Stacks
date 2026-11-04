module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleQuasicoherentClosure
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Abelian.CommutingFamilyMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Restriction to the scheme of a chart preserves joint epimorphisms of quasi-coherent modules

Restriction of an `𝒪_F`-module to the scheme underlying an étale chart `A` of an algebraic space
`F` (`AlgebraicGeometry.Space.restrictToChartSchemeFunctor`) is only left exact in general.  On
quasi-coherent modules it does carry a jointly epimorphic family `φᵢ : Mᵢ ⟶ N` to a jointly
epimorphic family: on an affine Zariski open `V` of the chart's scheme the sections are those over
the affine étale chart `V` cuts out, where an epimorphism of quasi-coherent modules is surjective
(`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`), and the affine
opens cover.

Consequently the restriction of a commuting family of quasi-coherent modules generated in bounded
degree is generated in the same degrees.  This is how the graded pieces `𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ` of the proof
of Stacks 0D39 are read on the scheme `X_y`.

## Main results

* `AlgebraicGeometry.Space.exists_eq_sum_of_jointlyEpi`: joint surjectivity on affine charts.
* `AlgebraicGeometry.Space.eq_zero_of_restrictToChartScheme_comp_eq_zero`: the restriction
  preserves joint epimorphy.
* `AlgebraicGeometry.Space.generatedFrom_map_restrictToChartScheme`: and generation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- A finite sum of morphisms of sheaves of modules acts on sections as the sum. -/
theorem sheafOfModules_sum_val_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (W : Cᵒᵖ) (x : M.val.obj W) :
    (∑ i ∈ s, f i).val.app W x = ∑ i ∈ s, (f i).val.app W x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- **A jointly epimorphic finite family of morphisms of quasi-coherent `𝒪_F`-modules is jointly
surjective on the sections over every affine étale chart.** -/
theorem exists_eq_sum_of_jointlyEpi {r : ℕ} {M : Fin r → Modules.{u, u} B S hS F hF}
    {N : Modules.{u, u} B S hS F hF} (φ : ∀ i, M i ⟶ N)
    (hM : ∀ i, (M i).IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hφ : ∀ ⦃Q : Modules.{u, u} B S hS F hF⦄ (g : N ⟶ Q), (∀ i, φ i ≫ g = 0) → g = 0)
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (s : N.val.obj (op W)) :
    ∃ t : ∀ i, (M i).val.obj (op W), s = ∑ i, (φ i).val.app (op W) (t i) := by
  have hd : Epi (biproduct.desc φ) := Preadditive.epi_of_cancel_zero _ fun {Q} g hg =>
    hφ g fun i => by rw [← biproduct.ι_desc_assoc φ i, hg, comp_zero]
  have hqc : (⨁ M).IsQuasicoherentOnSite := by
    have h := SheafOfModules.isQuasicoherentOnSite_coproduct _ M hM
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso (biproduct.isoCoproduct M).symm h
  obtain ⟨t₀, ht⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite _ hd hqc hN W hW s
  refine ⟨fun i => (biproduct.π M i).val.app (op W) t₀, ?_⟩
  rw [← ht, biproduct.desc_eq, sheafOfModules_sum_val_app_apply]
  rfl

/-- **Restriction to the scheme of a chart preserves joint epimorphy of quasi-coherent
modules.**  If `φᵢ : Mᵢ ⟶ N` are jointly epimorphic morphisms of quasi-coherent `𝒪_F`-modules, a
morphism out of the restriction of `N` to the scheme of an étale chart `A` which vanishes on the
restrictions of all `φᵢ` is zero.

The restriction is the Zariski sheafification of a presheaf whose sections over an open `V` are
those of `N` over the étale chart `V` cuts out.  The morphism transposes to that presheaf; over an
affine `V` the chart is affine and every section of `N` there is a sum of images of the `φᵢ`
(`AlgebraicGeometry.Space.exists_eq_sum_of_jointlyEpi`), and the affine opens cover. -/
theorem eq_zero_of_restrictToChartScheme_comp_eq_zero (A : SmallEtale B S hS F) {r : ℕ}
    {M : Fin r → Modules.{u, u} B S hS F hF} {N : Modules.{u, u} B S hS F hF} (φ : ∀ i, M i ⟶ N)
    (hM : ∀ i, (M i).IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hφ : ∀ ⦃Q : Modules.{u, u} B S hS F hF⦄ (g : N ⟶ Q), (∀ i, φ i ≫ g = 0) → g = 0)
    {Q : SheafOfModules.{u} (chartScheme A).ringCatSheaf}
    (g : (restrictToChartSchemeFunctor B S hS F hF A).obj N ⟶ Q)
    (hg : ∀ i, (restrictToChartSchemeFunctor B S hS F hF A).map (φ i) ≫ g = 0) : g = 0 := by
  let : HasSheafify (Opens.grothendieckTopology (chartScheme A)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (chartScheme A)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let P : Modules.{u, u} B S hS F hF ⥤ PresheafOfModules.{u} (chartScheme A).ringCatSheaf.obj :=
    SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u} ⋙
      SheafOfModules.forget _ ⋙
      PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F A)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (chartScheme A).ringCatSheaf.obj)
  change (PresheafOfModules.sheafification (𝟙 _)).obj (P.obj N) ⟶ Q at g
  have hg' : ∀ i, (PresheafOfModules.sheafification (𝟙 _)).map (P.map (φ i)) ≫ g = 0 := hg
  have h0 : adj.homEquiv _ _ (0 : (PresheafOfModules.sheafification (𝟙 _)).obj (P.obj N) ⟶ Q) =
      0 := by
    rw [adj.homEquiv_unit, Functor.map_zero, comp_zero]
  refine (adj.homEquiv _ _).injective (Eq.trans ?_ h0.symm)
  have hz : ∀ i, P.map (φ i) ≫ adj.homEquiv _ _ g = 0 := fun i => by
    rw [← adj.homEquiv_naturality_left, hg' i, adj.homEquiv_unit, Functor.map_zero, comp_zero]
  have haff : ∀ (V : (chartScheme A).Opens), IsAffineOpen V →
      ∀ x, (adj.homEquiv _ _ g).app (op V) x = 0 := by
    intro V hV x
    have hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
        ((openChartFunctor B S hS F A).obj V)) := hV
    obtain ⟨t, ht⟩ := exists_eq_sum_of_jointlyEpi φ hM hN hφ _ hW x.down
    have hx : x = ∑ i, (P.map (φ i)).app (op V) (ULift.up (t i)) := by
      refine ULift.ext _ _ ?_
      classical
      have hdown : ∀ s : Finset (Fin r),
          (∑ i ∈ s, (P.map (φ i)).app (op V) (ULift.up (t i))).down =
            ∑ i ∈ s, (φ i).val.app (op ((openChartFunctor B S hS F A).obj V)) (t i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => rfl
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl
      exact ht.trans (hdown _).symm
    rw [hx, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact congrArg (fun k => k.app (op V) (ULift.up (t i))) (hz i)
  refine PresheafOfModules.hom_ext fun V => ?_
  ext x
  obtain ⟨V⟩ := V
  show (adj.homEquiv _ _ g).app (op V) x = (0 : Q.val.obj (op V))
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (M := Q)
    (S := Sieve.generate (fun (V' : (chartScheme A).Opens) (_ : V' ⟶ V) => IsAffineOpen V'))
    _ ?_ fun V' f hf => ?_
  · intro y hy
    obtain ⟨V', hV', hyV', hle⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (x := y) (U := V) hy
    exact ⟨V', homOfLE hle, ⟨V', 𝟙 _, homOfLE hle, hV', Category.id_comp _⟩, hyV'⟩
  · obtain ⟨V'', f₁, f₂, hf₂, rfl⟩ := hf
    have e1 := PresheafOfModules.naturality_apply (adj.homEquiv _ _ g) f₂.op x
    have e2 : Q.val.map f₂.op ((adj.homEquiv _ _ g).app (op V) x) = 0 :=
      e1.symm.trans (haff V'' hf₂ _)
    exact (PresheafOfModules.map_comp_apply Q.val f₂.op f₁.op _).trans
      ((congrArg _ e2).trans (map_zero _))

/-- **The restriction of a commuting family of quasi-coherent modules to the scheme of a chart
is generated in the same degrees.** -/
theorem generatedFrom_map_restrictToChartScheme (A : SmallEtale B S hS F) {r : ℕ}
    (G : Stacks.CommutingFamily (Modules.{u, u} B S hS F hF) r)
    (hqc : ∀ n, (G.obj n).IsQuasicoherentOnSite) {N : ℕ} (hG : G.GeneratedFrom N) :
    (G.map (restrictToChartSchemeFunctor B S hS F hF A)).GeneratedFrom N :=
  fun n hn _ g hg => eq_zero_of_restrictToChartScheme_comp_eq_zero A (fun i => G.act i n)
    (fun _ => hqc n) (hqc (n + 1)) (fun _ g' hg' => hG n hn g' hg') g hg

end AlgebraicGeometry.Space

end
