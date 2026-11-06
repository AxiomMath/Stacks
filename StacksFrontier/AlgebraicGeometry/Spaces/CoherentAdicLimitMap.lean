module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartTower
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# Morphisms of coherent adic systems out of morphisms of their limits

Let `F` be an algebraic space over a scheme `S` whose étale charts are locally Noetherian and let
`𝓘 ⊆ 𝒪_F` be a quasi-coherent sheaf of ideals.  For a coherent adic system `(E_n)` in
`Coh(F, 𝓘)` the inverse limit `lim E_n`, formed in the category of `𝒪_F`-modules, maps onto every
`E_n`, and the kernel of that projection is, over every Noetherian affine chart, `𝓘 ⁿ⁺¹` times the
limit.  So a morphism `lim E ⟶ lim H` of limits of two coherent adic systems descends to a
morphism `E ⟶ H` of coherent adic systems, and the descended morphism is determined by its limit.

This is the space-level counterpart of `Stacks.Coherent.coherentAdicSystemMapOfLimitMap` of the
scheme-level development, and it is what produces the map `α` of Stacks 08BD from the theorem on
formal functions.

## Main definitions

* `AlgebraicGeometry.Space.coherentAdicSystemMapOfLimitMap` — the morphism of coherent adic
  systems induced by a morphism of their limits.
* `AlgebraicGeometry.Space.systemMapOfComparisonIso` — for `c : H ⟶ D` with `lim c` invertible
  and `γ : E ⟶ D`, the morphism `E ⟶ H` whose limit is `lim γ ≫ (lim c)⁻¹`.

## Main results

* `AlgebraicGeometry.Space.surjective_limit_π_app` and
  `AlgebraicGeometry.Space.epi_limit_π_of_isCoherentAdicSystem` — the projections of the limit
  of a coherent adic system are surjective on the sections over affine charts, hence
  epimorphisms.
* `AlgebraicGeometry.Space.ker_limit_π_app` — their kernels over a Noetherian affine chart.
* `AlgebraicGeometry.Space.eq_zero_of_app_eq_zero_of_isAffineChart` — a morphism of
  `𝒪_F`-modules vanishing on the sections over the affine charts vanishes.
* `AlgebraicGeometry.Space.systemMapOfComparisonIso_comp` — the factorization.

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Morphisms vanishing on the affine charts -/

include hF in
/-- **A morphism of `𝒪_F`-modules which vanishes on the sections over every affine chart
vanishes.**  Its kernel is bijective on the sections over the affine charts, hence invertible. -/
theorem eq_zero_of_app_eq_zero_of_isAffineChart {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    (h : ∀ (Z : SmallEtale B S hS F), IsAffine (chartScheme Z) →
      ∀ x : M.val.obj (op Z), φ.val.app (op Z) x = 0) :
    φ = 0 := by
  have hiso : IsIso (SheafOfModules.Submodule.ker φ).ι :=
    SmallEtale.isIso_of_bijective_app_of_isAffineChart B S hS F hF _ fun Z hZ =>
      ⟨fun a b hab => Subtype.ext hab, fun x => ⟨⟨x, (SheafOfModules.Submodule.mem_ker φ (op Z) x).2
        (h Z hZ x)⟩, rfl⟩⟩
  have hepi : Epi (SheafOfModules.Submodule.ker φ).ι := IsIso.epi_of_iso _
  exact (cancel_epi (SheafOfModules.Submodule.ker φ).ι).1
    ((SheafOfModules.Submodule.ker_ι_comp φ).trans comp_zero.symm)

/-! ### The sections of a limit -/

/-- **The sections over a chart of the limit of an inverse system of `𝒪_F`-modules are the limit
of the sections**: evaluation at a chart preserves limits. -/
def limitSectionsIso (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F) :
    (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) (op V)).obj
          (limit E) ≅ chartSectionsLimit B S hS F hF E V :=
  preservesLimitIso (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) (op V)) E

/-- The identification of the sections of the limit is compatible with the projections. -/
theorem limitSectionsIso_hom_chartSectionsLevel (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (n : ℕ) :
    (limitSectionsIso B S hS F hF E V).hom ≫ chartSectionsLevel B S hS F hF E V n =
      (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) (op V)).map
          (limit.π E (op n)) :=
  preservesLimitIso_hom_π _ _ _

variable (𝓘 : (SheafOfModules.unit.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- The projection of the limit onto level `n`, on the sections over a chart, is the identification
of the sections of the limit followed by the projection of the limit of the sections. -/
private theorem limit_π_app_hom_eq (E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (n : ℕ) : ((limit.π E (op n)).val.app (op V)).hom =
      (chartSectionsLevel B S hS F hF E V n).hom ∘ₗ
        (limitSectionsIso B S hS F hF E V).toLinearEquiv.toLinearMap :=
  congrArg (fun φ => φ.hom) (limitSectionsIso_hom_chartSectionsLevel B S hS F hF E V n).symm

/-- **The projections of the limit of a coherent adic system are surjective on the sections over
an affine chart.** -/
theorem surjective_limit_π_app {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) {V : SmallEtale B S hS F}
    (hV : IsAffine (chartScheme V)) (n : ℕ) :
    Function.Surjective ((limit.π E (op n)).val.app (op V)) := by
  change Function.Surjective ((limit.π E (op n)).val.app (op V)).hom
  rw [limit_π_app_hom_eq]
  exact (surjective_chartSectionsLevel B S hS F hF 𝓘 hE hV n).comp
    (limitSectionsIso B S hS F hF E V).toLinearEquiv.surjective

/-- **The projections of the limit of a coherent adic system are epimorphisms.** -/
theorem epi_limit_π_of_isCoherentAdicSystem {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E) (n : ℕ) :
    Epi (limit.π E (op n)) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (SmallEtale.isLocallySurjective_of_surjective_app_of_isAffineChart B S hS F hF _ fun _ hZ =>
      surjective_limit_π_app B S hS F hF 𝓘 hE hZ n)

/-- **The kernel of the projection of the limit of a coherent adic system onto level `n`, over a
Noetherian affine chart, is `𝓘 ⁿ⁺¹` times the sections of the limit.** -/
theorem ker_limit_π_app {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) (n : ℕ) :
    LinearMap.ker ((limit.π E (op n)).val.app (op V)).hom =
      chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF V) ((limit E).val.obj (op V))) := by
  let e := (limitSectionsIso B S hS F hF E V).toLinearEquiv
  have hmap : ∀ (L : Submodule (chartRing B S hS F hF V) (chartSectionsLimit B S hS F hF E V)),
      L.comap e.toLinearMap = L.map e.symm.toLinearMap := fun L =>
    (Submodule.map_equiv_eq_comap_symm e.symm L).symm
  ext x
  have h1 : ((limit.π E (op n)).val.app (op V)).hom x =
      (chartSectionsLevel B S hS F hF E V n).hom (e x) :=
    congrArg (fun φ => φ.hom x) (limitSectionsIso_hom_chartSectionsLevel B S hS F hF E V n).symm
  rw [LinearMap.mem_ker, h1]
  refine (LinearMap.mem_ker (f := (chartSectionsLevel B S hS F hF E V n).hom) (y := e
      x)).symm.trans ?_
  refine (Iff.of_eq (congrArg (e x ∈ ·)
    (ker_chartSectionsLevel B S hS F hF 𝓘 hE hIcart hV n))).trans ?_
  have h2 := congrArg (fun L => x ∈ L)
    (hmap (chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) • (⊤ : Submodule _ _)))
  simp only [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at h2
  exact Iff.of_eq h2

/-- A section of the limit of a coherent adic system over a Noetherian affine chart which dies in
level `n` lies in `𝓘 ⁿ⁺¹` times the sections of the limit. -/
theorem mem_pow_smul_top_of_limit_π_app_eq_zero {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF}
    (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V) (n : ℕ)
    (y : (limit E).val.obj (op V)) (hy : (limit.π E (op n)).val.app (op V) y = 0) :
    y ∈ chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF V) ((limit E).val.obj (op V))) := by
  rw [← ker_limit_π_app B S hS F hF 𝓘 hE hIcart hV n]
  exact hy

/-! ### Morphisms of coherent adic systems out of morphisms of limits -/

section SystemMap

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (hN : ∀ Z : SmallEtale B S hS F, IsAffine (chartScheme Z) → IsNoetherianAffineChart B S hS F Z)

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
include hIcart hN in
/-- A morphism `a : lim E ⟶ lim H` of the limits of two coherent adic systems, followed by the
projection of `lim H` onto level `n`, kills every morphism into `lim E` killed by the projection
of `lim E` onto level `n`: over a Noetherian affine chart such a morphism lands in `𝓘 ⁿ⁺¹` times
the limit, and `H_n` is annihilated by `𝓘 ⁿ⁺¹`. -/
theorem comp_limit_π_eq_zero_of_comp_limit_π_eq_zero {E H : CoherentAdicSystems B S hS F hF 𝓘}
    {P : Modules.{u, u} B S hS F hF} (φ : P ⟶ limit E.obj) (n : ℕ)
    (hφ : φ ≫ limit.π E.obj (op n) = 0) (a : limit E.obj ⟶ limit H.obj) :
    φ ≫ a ≫ limit.π H.obj (op n) = 0 := by
  refine eq_zero_of_app_eq_zero_of_isAffineChart B S hS F hF _ fun Z hZ x => ?_
  have hy := mem_pow_smul_top_of_limit_π_app_eq_zero B S hS F hF 𝓘 E.property hIcart
    (hN Z hZ) n (φ.val.app (op Z) x)
    (congrArg (fun ψ : P ⟶ E.obj.obj (op n) => ψ.val.app (op Z) x) hφ)
  have hann := (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 (n + 1) (H.obj.obj (op n))).mp
    (H.property.2.1 n) Z
  refine Submodule.smul_induction_on (p := fun y =>
    ((a ≫ limit.π H.obj (op n)).val.app (op Z)) y = 0) hy (fun r hr m _ => ?_)
    (fun m m' hm hm' => ?_)
  · rw [map_smul]
    exact hann r hr _
  · rw [map_add, hm, hm', add_zero]

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
include hIcart hN in
/-- For a morphism `a : lim E ⟶ lim H` of the limits of two coherent adic systems, the kernel of
the projection `lim E ⟶ E_n` is killed by `a` followed by the projection `lim H ⟶ H_n`. -/
theorem kernel_ι_limit_π_comp_eq_zero {E H : CoherentAdicSystems B S hS F hF 𝓘}
    (a : limit E.obj ⟶ limit H.obj) (n : ℕ) :
    kernel.ι (limit.π E.obj (op n)) ≫ a ≫ limit.π H.obj (op n) = 0 :=
  comp_limit_π_eq_zero_of_comp_limit_π_eq_zero B S hS F hF 𝓘 hIcart hN _ n
    (kernel.condition _) a

/-- The component at level `n` of the morphism of coherent adic systems induced by a morphism of
their limits: the descent of `a ≫ π_n` along the epimorphism `π_n : lim E ⟶ E_n`. -/
def limitMapComponent {E H : CoherentAdicSystems B S hS F hF 𝓘}
    (a : limit E.obj ⟶ limit H.obj) (n : ℕ) : E.obj.obj (op n) ⟶ H.obj.obj (op n) :=
  haveI := epi_limit_π_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property n
  Abelian.epiDesc (limit.π E.obj (op n)) (a ≫ limit.π H.obj (op n))
    (kernel_ι_limit_π_comp_eq_zero B S hS F hF 𝓘 hIcart hN a n)

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
/-- The components of the induced morphism are compatible with the limit projections. -/
theorem limit_π_comp_limitMapComponent {E H : CoherentAdicSystems B S hS F hF 𝓘}
    (a : limit E.obj ⟶ limit H.obj) (n : ℕ) :
    limit.π E.obj (op n) ≫ limitMapComponent B S hS F hF 𝓘 hIcart hN a n =
      a ≫ limit.π H.obj (op n) :=
  have := epi_limit_π_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property n
  Abelian.comp_epiDesc _ _ _

/-- **The morphism of coherent adic systems induced by a morphism of their limits.** -/
def coherentAdicSystemMapOfLimitMap {E H : CoherentAdicSystems B S hS F hF 𝓘}
    (a : limit E.obj ⟶ limit H.obj) : E ⟶ H :=
  ObjectProperty.homMk
    { app n := limitMapComponent B S hS F hF 𝓘 hIcart hN a n.unop
      naturality i j g := by
        have := epi_limit_π_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property i.unop
        refine (cancel_epi (limit.π E.obj i)).mp ?_
        rw [← Category.assoc, limit.w, limit_π_comp_limitMapComponent, ← Category.assoc,
          limit_π_comp_limitMapComponent, Category.assoc, limit.w] }

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
/-- The levelwise components of the induced morphism. -/
theorem coherentAdicSystemMapOfLimitMap_hom_app {E H : CoherentAdicSystems B S hS F hF 𝓘}
    (a : limit E.obj ⟶ limit H.obj) (n : ℕ) :
    (coherentAdicSystemMapOfLimitMap B S hS F hF 𝓘 hIcart hN a).hom.app (op n) =
      limitMapComponent B S hS F hF 𝓘 hIcart hN a n :=
  rfl

/-- **Factorization through a comparison morphism that is an isomorphism on limits.**  Given
`c : H ⟶ D` with `lim c` invertible and `γ : E ⟶ D`, this is the morphism `E ⟶ H` of coherent
adic systems whose limit is `lim γ ≫ (lim c)⁻¹`. -/
def systemMapOfComparisonIso {E H : CoherentAdicSystems B S hS F hF 𝓘}
    {D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (c : H.obj ⟶ D) [IsIso (limMap c)]
    (γ : E.obj ⟶ D) : E ⟶ H :=
  coherentAdicSystemMapOfLimitMap B S hS F hF 𝓘 hIcart hN (limMap γ ≫ inv (limMap c))

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
/-- **The factorization through a comparison morphism does factor the given morphism.** -/
theorem systemMapOfComparisonIso_comp {E H : CoherentAdicSystems B S hS F hF 𝓘}
    {D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (c : H.obj ⟶ D) [IsIso (limMap c)]
    (γ : E.obj ⟶ D) :
    (systemMapOfComparisonIso B S hS F hF 𝓘 hIcart hN c γ).hom ≫ c = γ := by
  refine NatTrans.ext (funext fun n => ?_)
  have := epi_limit_π_of_isCoherentAdicSystem B S hS F hF 𝓘 E.property n.unop
  refine (cancel_epi (limit.π E.obj n)).mp ?_
  rw [NatTrans.comp_app, ← Category.assoc]
  change (limit.π E.obj (op n.unop) ≫ limitMapComponent B S hS F hF 𝓘 hIcart hN _ n.unop) ≫ _ = _
  rw [limit_π_comp_limitMapComponent, Category.assoc]
  change _ ≫ limit.π H.obj n ≫ c.app n = _
  rw [← limMap_π c n, ← Category.assoc, Category.assoc (limMap γ), IsIso.inv_hom_id,
    Category.comp_id, limMap_π]

end SystemMap


end AlgebraicGeometry.Space

end
