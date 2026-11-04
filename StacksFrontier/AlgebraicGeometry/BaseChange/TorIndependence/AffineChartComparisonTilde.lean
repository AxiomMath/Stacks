module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonMap
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DerivedPullbackCompCoherence

/-!
# The chart comparison of Stacks 0DJ8 on derived sheafifications

Let `ch` be a Cartesian affine-open chart of a cartesian square of schemes, with the comparison
map `AlgebraicGeometry.BaseChangeChart.comparison` of Stacks 0DJ8 (2). This module proves that
the comparison is natural in its data, so that its invertibility depends only on the data up to
isomorphism. It also computes the comparison on a chart whose opens are the whole schemes, at
derived sheafifications: there it is the ring-level comparison of Stacks 065Z followed by the
given morphism, up to isomorphisms on both sides.

## Main results

* `AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeMap_naturality` and
  `AlgebraicGeometry.BaseChangeChart.comparison_naturality`: naturality in `K`, and in the triple
  `(K, K', φ)`.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_of_iso`: invariance of condition (2)
  under isomorphism of the data.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_tilde_iff`: on a chart with
  `X ≅ Spec A` and `X' ≅ Spec A'`, for `K = L(j)^*(Ñ)` and `K' = L(j')^*(Ñ')`, the chart comparison
  is an isomorphism exactly when the comparison of Stacks 065Z at `N`, followed by `ψ`, is.

## Implementation notes

Every computation is carried out first for abstract functors and natural transformations
(the `_aux` lemmas) and then instantiated once. Run directly on the derived functors, the
elaboration of the intermediate naturality squares alone exceeds the heartbeat budget. The
pseudofunctor coherence of derived pullback that `isIso_comparison_tilde_iff` needs is
`Stacks.Duality.derivedPullbackCompIso_retraction_square`.

Everything is at the locally small model of the derived categories of sheaves of modules.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- The naturality of a composite of the shape of `sectionsBaseChangeMap`, for abstract functors
and natural transformations: every factor is a component of a natural transformation, the unit of
an adjunction, or a transport along an equality of functors. -/
theorem sectionsBaseChangeMap_naturality_aux {𝒦 𝒦' 𝒜 𝒜₀ 𝒜₀' 𝒜' : Type*} [Category* 𝒦]
    [Category* 𝒦'] [Category* 𝒜] [Category* 𝒜₀] [Category* 𝒜₀'] [Category* 𝒜']
    {Lu : 𝒦 ⥤ 𝒜} {Γ : 𝒜 ⥤ 𝒜₀} {E : 𝒜₀ ⥤ 𝒜₀'} {F' Z' : 𝒜₀' ⥤ 𝒜'} {G' : 𝒜' ⥤ 𝒜₀'}
    {Z F : 𝒜₀ ⥤ 𝒜} {Lc : 𝒜 ⥤ 𝒜'} {P P' : 𝒦 ⥤ 𝒜'} {Lg : 𝒦 ⥤ 𝒦'} {Lu' : 𝒦' ⥤ 𝒜'}
    (adj : F' ⊣ G') (ι' : F' ⟶ Z') (b : E ⋙ Z' ⟶ Z ⋙ Lc) (ι : Z ⟶ F) (ε : Γ ⋙ F ⟶ 𝟭 𝒜)
    (c₁ : Lu ⋙ Lc ⟶ P) (hP : P = P') (c₂ : P' ⟶ Lg ⋙ Lu') {K K₂ : 𝒦} (e : K ⟶ K₂) :
    E.map (Γ.map (Lu.map e)) ≫ adj.unit.app (E.obj (Γ.obj (Lu.obj K₂))) ≫
        G'.map (ι'.app (E.obj (Γ.obj (Lu.obj K₂)))) ≫ G'.map (b.app (Γ.obj (Lu.obj K₂))) ≫
        G'.map (Lc.map (ι.app (Γ.obj (Lu.obj K₂)))) ≫ G'.map (Lc.map (ε.app (Lu.obj K₂))) ≫
        G'.map (c₁.app K₂) ≫ G'.map (eqToHom (Functor.congr_obj hP K₂)) ≫ G'.map (c₂.app K₂) =
      (adj.unit.app (E.obj (Γ.obj (Lu.obj K))) ≫
        G'.map (ι'.app (E.obj (Γ.obj (Lu.obj K)))) ≫ G'.map (b.app (Γ.obj (Lu.obj K))) ≫
        G'.map (Lc.map (ι.app (Γ.obj (Lu.obj K)))) ≫ G'.map (Lc.map (ε.app (Lu.obj K))) ≫
        G'.map (c₁.app K) ≫ G'.map (eqToHom (Functor.congr_obj hP K)) ≫ G'.map (c₂.app K)) ≫
        G'.map (Lu'.map (Lg.map e)) := by
  subst hP
  simp only [eqToHom_refl, Category.assoc]
  rw [← adj.unit_naturality_assoc]
  simp only [← Functor.map_comp]
  congr 2
  have h₁ := ι'.naturality (E.map (Γ.map (Lu.map e)))
  have h₂ := b.naturality (Γ.map (Lu.map e))
  have h₃ := ι.naturality (Γ.map (Lu.map e))
  have h₄ := ε.naturality (Lu.map e)
  have h₅ := c₁.naturality e
  have h₆ := c₂.naturality e
  simp only [Functor.comp_map, Functor.id_map] at h₂ h₄ h₅ h₆
  simp only [Category.id_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Lc.map_comp_assoc, h₃, Lc.map_comp_assoc,
    ← Lc.map_comp_assoc (F.map _), h₄, Lc.map_comp_assoc, reassoc_of% h₅, h₆]

/-- **The identification of Stacks 0DJ8 (2) is natural in `K`.** -/
theorem sectionsBaseChangeMap_naturality (ch : BaseChangeChart f g f' g')
    {K K₂ : DerivedCategory X.Modules} (e : K ⟶ K₂) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).functor.map ((affineDerivedSections ch.incU).map e) ≫
        ch.sectionsBaseChangeMap K₂ =
      ch.sectionsBaseChangeMap K ≫
        (affineDerivedSections ch.incU').map ((Stacks.Duality.derivedPullback g').map e) :=
  sectionsBaseChangeMap_naturality_aux (derivedTildeGlobalSectionsAdjunction ch.A').val
    (derivedTildeCompι ch.A').hom (affinePullbackComparison ch.A ch.A' ch.c).inv
    (derivedTildeCompι ch.A).inv (derivedTildeGlobalSectionsAdjunction ch.A).val.counit
    (Stacks.Duality.derivedPullbackCompIso (Spec.map ch.c) ch.incU).hom
    (congrArg Stacks.Duality.derivedPullback ch.wU'U.symm)
    (Stacks.Duality.derivedPullbackCompIso ch.incU' g').inv e

/-- The naturality of a composite of the shape of `comparison`, for abstract functors: a component
of a natural transformation, then the image of a natural family, then the image of a morphism. -/
theorem comparison_naturality_aux {𝒦 𝒦' 𝒜₀ 𝒜₀' ℛ ℛ' : Type*} [Category* 𝒦] [Category* 𝒦']
    [Category* 𝒜₀] [Category* 𝒜₀'] [Category* ℛ] [Category* ℛ']
    {Ra : 𝒜₀ ⥤ ℛ} {Lb : ℛ ⥤ ℛ'} {Lc : 𝒜₀ ⥤ 𝒜₀'} {Rd : 𝒜₀' ⥤ ℛ'} {RΓ : 𝒦 ⥤ 𝒜₀}
    {RΓ' : 𝒦' ⥤ 𝒜₀'} {Lg : 𝒦 ⥤ 𝒦'} (τ : Ra ⋙ Lb ⟶ Lc ⋙ Rd)
    (σ : ∀ K, Lc.obj (RΓ.obj K) ⟶ RΓ'.obj (Lg.obj K))
    (hσ : ∀ {K K₂ : 𝒦} (e : K ⟶ K₂), Lc.map (RΓ.map e) ≫ σ K₂ = σ K ≫ RΓ'.map (Lg.map e))
    {K K₂ : 𝒦} {K' K₂' : 𝒦'} (e : K ⟶ K₂) (e' : K' ⟶ K₂') (φ : Lg.obj K ⟶ K')
    (φ₂ : Lg.obj K₂ ⟶ K₂') (h : Lg.map e ≫ φ₂ = φ ≫ e') :
    ((τ.app (RΓ.obj K) ≫ Rd.map (σ K)) ≫ Rd.map (RΓ'.map φ)) ≫ Rd.map (RΓ'.map e') =
      Lb.map (Ra.map (RΓ.map e)) ≫ (τ.app (RΓ.obj K₂) ≫ Rd.map (σ K₂)) ≫
        Rd.map (RΓ'.map φ₂) := by
  have hτ := τ.naturality (RΓ.map e)
  simp only [Functor.comp_map] at hτ
  simp only [Category.assoc]
  rw [reassoc_of% hτ]
  simp only [← Rd.map_comp]
  rw [reassoc_of% hσ, ← RΓ'.map_comp (Lg.map e), h, RΓ'.map_comp]

/-- **The chart comparison of Stacks 0DJ8 is natural** in the pair `(K, K')` and the morphism
`L(g')^*K ⟶ K'`. -/
theorem comparison_naturality (ch : BaseChangeChart f g f' g')
    {K K₂ : DerivedCategory X.Modules} {K' K₂' : DerivedCategory X'.Modules} (e : K ⟶ K₂)
    (e' : K' ⟶ K₂') (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (φ₂ : (Stacks.Duality.derivedPullback g').obj K₂ ⟶ K₂')
    (h : (Stacks.Duality.derivedPullback g').map e ≫ φ₂ = φ ≫ e') :
    ch.comparison K K' φ ≫ (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.map
        ((affineDerivedSections ch.incU').map e') =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).functor.map ((ModuleCat.restrictScalars ch.a.hom).mapDerivedCategory.map
          ((affineDerivedSections ch.incU).map e)) ≫ ch.comparison K₂ K₂' φ₂ :=
  comparison_naturality_aux
    (@RingTheory.TorIndependence.derivedBaseChangeComparison _ _ _ _ _ _ _ _ _ _ _ _
      ch.a.hom ch.b.hom ch.c.hom ch.d.hom ch.isPushout_hom
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).functor
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).functor
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).comparison
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).comparison
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.b.hom).isLeftDerived
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ch.c.hom).isLeftDerived).2.1
    ch.sectionsBaseChangeMap (fun e => ch.sectionsBaseChangeMap_naturality e) e e' φ φ₂ h

/-- **Condition (2) of Stacks 0DJ8 is invariant under isomorphism of the data.** Given
isomorphisms `K ≅ K₂` and `K' ≅ K₂'` carrying `φ : L(g')^*K ⟶ K'` to `φ₂ : L(g')^*K₂ ⟶ K₂'`, the
chart comparison for `φ` is invertible if and only if the one for `φ₂` is. -/
theorem isIso_comparison_iff_of_iso (ch : BaseChangeChart f g f' g')
    {K K₂ : DerivedCategory X.Modules} {K' K₂' : DerivedCategory X'.Modules} (e : K ≅ K₂)
    (e' : K' ≅ K₂') (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (φ₂ : (Stacks.Duality.derivedPullback g').obj K₂ ⟶ K₂')
    (h : (Stacks.Duality.derivedPullback g').map e.hom ≫ φ₂ = φ ≫ e'.hom) :
    IsIso (ch.comparison K K' φ) ↔ IsIso (ch.comparison K₂ K₂' φ₂) := by
  rw [← isIso_comp_right_iff (ch.comparison K K' φ)
      ((ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.map
        ((affineDerivedSections ch.incU').map e'.hom)),
    ch.comparison_naturality e.hom e'.hom φ φ₂ h, isIso_comp_left_iff]

/-- The identification of Stacks 0DJ8 (2) on derived sheafifications, for abstract functors:
the composite of the shape of `sectionsBaseChangeMap ≫ RΓ(U', φ)` is, up to isomorphisms on both
sides, the given morphism `ψ : E(N) ⟶ N'`. The input is the pseudofunctor coherence `hP`. -/
theorem sectionsBaseChangeMap_tilde_aux {𝒜₀ 𝒜 𝒜₀' 𝒜' 𝒳 𝒳' : Type*} [Category* 𝒜₀]
    [Category* 𝒜] [Category* 𝒜₀'] [Category* 𝒜'] [Category* 𝒳] [Category* 𝒳']
    {F Z : 𝒜₀ ⥤ 𝒜} {Γ : 𝒜 ⥤ 𝒜₀} {F' Z' : 𝒜₀' ⥤ 𝒜'} {Γ' : 𝒜' ⥤ 𝒜₀'} {E : 𝒜₀ ⥤ 𝒜₀'}
    {Lc : 𝒜 ⥤ 𝒜'} {Lu : 𝒳 ⥤ 𝒜} {Lj : 𝒜 ⥤ 𝒳} {Lu' : 𝒳' ⥤ 𝒜'} {Lj' : 𝒜' ⥤ 𝒳'} {Lg : 𝒳 ⥤ 𝒳'}
    (adj : F ⊣ Γ) (adj' : F' ⊣ Γ') (κ : F ≅ Z) (κ' : F' ≅ Z') (apc : Z ⋙ Lc ≅ E ⋙ Z')
    (N : 𝒜₀) (N' : 𝒜₀') (ψ : E.obj N ⟶ N')
    (ρ : Z.obj N ⟶ Lu.obj (Lj.obj (Z.obj N)))
    (ρ' : ∀ Y : 𝒜', Y ⟶ Lu'.obj (Lj'.obj Y))
    (hρ' : ∀ {Y Y' : 𝒜'} (q : Y ⟶ Y'), q ≫ ρ' Y' = ρ' Y ≫ Lu'.map (Lj'.map q))
    {P₁ P₂ : 𝒜'} (c₁ : Lc.obj (Lu.obj (Lj.obj (Z.obj N))) ⟶ P₁) (e₁ : P₁ ⟶ P₂)
    (c₂ : P₂ ⟶ Lu'.obj (Lg.obj (Lj.obj (Z.obj N)))) {Q₁ Q₂ : 𝒳'}
    (d₁ : Lg.obj (Lj.obj (Z.obj N)) ⟶ Q₁) (e₂ : Q₁ ⟶ Q₂) (d₂ : Q₂ ⟶ Lj'.obj (Lc.obj (Z.obj N)))
    (hP : Lc.map ρ ≫ c₁ ≫ e₁ ≫ c₂ ≫ Lu'.map (d₁ ≫ e₂ ≫ d₂) = ρ' (Lc.obj (Z.obj N)))
    [IsIso (adj.unit.app N)] [IsIso ρ] :
    (adj'.unit.app (E.obj (Γ.obj (Lu.obj (Lj.obj (Z.obj N))))) ≫
        Γ'.map (κ'.hom.app (E.obj (Γ.obj (Lu.obj (Lj.obj (Z.obj N)))))) ≫
        Γ'.map (apc.inv.app (Γ.obj (Lu.obj (Lj.obj (Z.obj N))))) ≫
        Γ'.map (Lc.map (κ.inv.app (Γ.obj (Lu.obj (Lj.obj (Z.obj N)))))) ≫
        Γ'.map (Lc.map (adj.counit.app (Lu.obj (Lj.obj (Z.obj N))))) ≫
        Γ'.map c₁ ≫ Γ'.map e₁ ≫ Γ'.map c₂) ≫
        Γ'.map (Lu'.map (d₁ ≫ e₂ ≫ d₂ ≫ Lj'.map (apc.hom.app N ≫ Z'.map ψ))) =
      E.map (inv (adj.unit.app N ≫ Γ.map (κ.hom.app N ≫ ρ))) ≫ ψ ≫
        adj'.unit.app N' ≫ Γ'.map (κ'.hom.app N' ≫ ρ' (Z'.obj N')) := by
  have key : κ.inv.app (Γ.obj (Lu.obj (Lj.obj (Z.obj N)))) ≫
      adj.counit.app (Lu.obj (Lj.obj (Z.obj N))) =
      Z.map (inv (adj.unit.app N ≫ Γ.map (κ.hom.app N ≫ ρ))) ≫ ρ := by
    rw [← cancel_epi (Z.map (adj.unit.app N ≫ Γ.map (κ.hom.app N ≫ ρ))), ← Z.map_comp_assoc,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      κ.inv.naturality_assoc, F.map_comp_assoc]
    rw [adj.counit_naturality (κ.hom.app N ≫ ρ)]
    simp only [Functor.id_obj, Adjunction.left_triangle_components_assoc, Iso.inv_hom_id_app_assoc]
  have hapc := apc.inv.naturality (inv (adj.unit.app N ≫ Γ.map (κ.hom.app N ≫ ρ)))
  have hψ := hρ' (Z'.map ψ)
  have hh := hρ' (apc.hom.app N)
  simp only [Functor.comp_map] at hapc
  rw [← adj'.unit_naturality_assoc, ← adj'.unit_naturality_assoc, Category.assoc]
  simp only [← Functor.map_comp]
  congr 2
  have hh' : ρ' (Z'.obj (E.obj N)) =
      apc.inv.app N ≫ ρ' (Lc.obj (Z.obj N)) ≫ Lu'.map (Lj'.map (apc.hom.app N)) := by
    simp only [Functor.comp_obj] at hh
    rw [← hh, Iso.inv_hom_id_app_assoc]
  rw [κ'.hom.naturality_assoc, κ'.hom.naturality_assoc, hψ, hh']
  simp only [Category.assoc]
  rw [reassoc_of% hapc, ← hP]
  have key' := congrArg Lc.map key
  simp only [Functor.map_comp] at key'
  simp only [Functor.map_comp, Category.assoc, reassoc_of% key']


/-- A composite `τ_M ≫ R(s) ≫ R(t)` whose last two factors compose to `E(a) ≫ ψ ≫ b` with `a`
and `b` invertible is invertible exactly when `τ_N ≫ R(ψ)` is, by naturality of `τ`. -/
theorem isIso_comp_map_iff_of_fac {𝒜₀ ℛ ℛ' 𝒜₀' : Type*} [Category* 𝒜₀] [Category* ℛ]
    [Category* ℛ'] [Category* 𝒜₀'] {Ra : 𝒜₀ ⥤ ℛ} {Lb : ℛ ⥤ ℛ'} {E : 𝒜₀ ⥤ 𝒜₀'}
    {Rd : 𝒜₀' ⥤ ℛ'} (τ : Ra ⋙ Lb ⟶ E ⋙ Rd) {M N : 𝒜₀} {N' Y Y' : 𝒜₀'} (s : E.obj M ⟶ Y)
    (t : Y ⟶ Y') (a : M ⟶ N) (ψ : E.obj N ⟶ N') (b : N' ⟶ Y') [IsIso a] [IsIso b]
    (h : s ≫ t = E.map a ≫ ψ ≫ b) :
    IsIso ((τ.app M ≫ Rd.map s) ≫ Rd.map t) ↔ IsIso (τ.app N ≫ Rd.map ψ) := by
  have hτ := τ.naturality a
  simp only [Functor.comp_map] at hτ
  rw [Category.assoc, ← Rd.map_comp, h, Rd.map_comp, Rd.map_comp, ← reassoc_of% hτ,
    isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff]

/-- On a chart whose opens `U` and `U'` are the whole schemes, the morphism `g'` reads, under the
identifications `X ≅ Spec A` and `X' ≅ Spec A'`, as `Spec c`. -/
theorem comp_inv_incU (ch : BaseChangeChart f g f' g') [IsIso ch.incU] [IsIso ch.incU'] :
    g' ≫ inv ch.incU = inv ch.incU' ≫ Spec.map ch.c := by
  rw [← cancel_epi ch.incU', IsIso.hom_inv_id_assoc, ← Category.assoc, ch.wU'U, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- **Condition (2) of Stacks 0DJ8 on derived sheafifications.** On a chart whose opens `U` and
`U'` are the whole schemes `X ≅ Spec A` and `X' ≅ Spec A'`, take `K = L(j)^*(Ñ)` and
`K' = L(j')^*(Ñ')` for `j`, `j'` the inverses of the chart's open immersions, and the morphism
`L(g')^*K ⟶ K'` induced by `ψ : A' ⊗ᴸ_A N ⟶ N'` through Stacks 0D5S and the affine comparison
square of Stacks 08DW. Then the chart comparison is an isomorphism if and only if the ring-level
comparison of Stacks 065Z at `N` followed by `ψ` is. -/
theorem isIso_comparison_tilde_iff (ch : BaseChangeChart f g f' g') [IsIso ch.incU]
    [IsIso ch.incU'] (N : DerivedCategory (ModuleCat.{u} ch.A))
    (N' : DerivedCategory (ModuleCat.{u} ch.A'))
    (ψ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      ch.c.hom).functor.obj N ⟶ N') :
    IsIso (ch.comparison
        ((Stacks.Duality.derivedPullback (inv ch.incU)).obj
          ((tilde.functor ch.A).mapDerivedCategory.obj N))
        ((Stacks.Duality.derivedPullback (inv ch.incU')).obj
          ((tilde.functor ch.A').mapDerivedCategory.obj N'))
        ((Stacks.Duality.derivedPullbackCompIso g' (inv ch.incU)).hom.app
            ((tilde.functor ch.A).mapDerivedCategory.obj N) ≫
          eqToHom (congrArg (fun t : X' ⟶ Spec ch.A => (Stacks.Duality.derivedPullback t).obj
            ((tilde.functor ch.A).mapDerivedCategory.obj N)) ch.comp_inv_incU) ≫
          (Stacks.Duality.derivedPullbackCompIso (inv ch.incU') (Spec.map ch.c)).inv.app
            ((tilde.functor ch.A).mapDerivedCategory.obj N) ≫
          (Stacks.Duality.derivedPullback (inv ch.incU')).map
            ((affinePullbackComparison ch.A ch.A' ch.c).hom.app N ≫
              (tilde.functor ch.A').mapDerivedCategory.map ψ))) ↔
      IsIso ((@RingTheory.TorIndependence.derivedBaseChangeComparison _ _ _ _ _ _ _ _ _ _ _ _
          ch.a.hom ch.b.hom ch.c.hom ch.d.hom ch.isPushout_hom
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.b.hom).functor
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.c.hom).functor
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.b.hom).comparison
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.c.hom).comparison
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.b.hom).isLeftDerived
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ch.c.hom).isLeftDerived).2.1.app N ≫
        (ModuleCat.restrictScalars ch.d.hom).mapDerivedCategory.map ψ) := by
  obtain ⟨ι, hιr, -⟩ := Stacks.Duality.exists_derivedPullbackIdIso_unit_laws (Spec ch.A)
  obtain ⟨ι', -, hι'l⟩ := Stacks.Duality.exists_derivedPullbackIdIso_unit_laws (Spec ch.A')
  have hη := isIso_derivedTildeGlobalSectionsAdjunction_unit ch.A
  have hη' := isIso_derivedTildeGlobalSectionsAdjunction_unit ch.A'
  have hP := Stacks.Duality.derivedPullbackCompIso_retraction_square (Spec.map ch.c) ch.incU
    (inv ch.incU) ch.incU' g' (inv ch.incU') (IsIso.hom_inv_id ch.incU)
    (IsIso.hom_inv_id ch.incU') ch.wU'U.symm ch.comp_inv_incU ι ι'
    (fun M => hιr (Spec.map ch.c) M) (fun M => hι'l (Spec.map ch.c) M)
    ((tilde.functor ch.A).mapDerivedCategory.obj N)
  have : IsIso ((derivedTildeGlobalSectionsAdjunction ch.A).val.unit.app N) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso ((derivedTildeGlobalSectionsAdjunction ch.A').val.unit.app N') :=
    NatIso.isIso_app_of_isIso _ _
  exact isIso_comp_map_iff_of_fac _ _ _ _ ψ _
    (sectionsBaseChangeMap_tilde_aux (derivedTildeGlobalSectionsAdjunction ch.A).val
      (derivedTildeGlobalSectionsAdjunction ch.A').val (derivedTildeCompι ch.A)
      (derivedTildeCompι ch.A') (affinePullbackComparison ch.A ch.A' ch.c) N N' ψ _
      (fun Y => ι'.inv.app Y ≫ eqToHom (congrArg (fun t : Spec ch.A' ⟶ Spec ch.A' =>
          (Stacks.Duality.derivedPullback t).obj Y) (IsIso.hom_inv_id ch.incU').symm) ≫
        (Stacks.Duality.derivedPullbackCompIso ch.incU' (inv ch.incU')).inv.app Y)
      (fun q => Stacks.Duality.derivedPullbackCompIso_retraction_naturality ch.incU' (inv ch.incU')
        (IsIso.hom_inv_id ch.incU') ι' q)
      _ _ _ _ _ _ hP)

end AlgebraicGeometry.BaseChangeChart
