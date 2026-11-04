module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroFibrationReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# The top-degree trace of the class of a `k`-point on a family of curves is split

Let `g : U → S` be separated of finite type with a compactification whose fibres have dimension at
most one, `Λ = ℤ/ℓ`, `ν : R²g_! g⁻¹ ≅ 𝟭`, and let `p : Spec k → U` be a `k`-point over the
`k`-point `i' = g ∘ p` of `S`, `k` separably closed, `X = i'_* Λ`. For a class
`δ ∈ Ext²_U(p_* Λ, g⁻¹ X)` whose image `H⁰(Rg_!(δ)) : H⁰(Rg_!(p_* Λ)) ⟶ R²g_!(g⁻¹ X)` is nonzero,
the composite `τ = t_X ∘ Rg_!(δ) : Rg_!(p_* Λ) ⟶ X` with the top-degree trace is split
(`Stacks.EtaleCohomology.exists_section_of_homology_map_ne_zero`): `Rg_!(p_* Λ) ≅ R(g ∘ p)_! Λ ≅ X`
(Tag 0F7J for the finite morphism `p`), `τ` is nonzero, and every nonzero endomorphism of
`X = i'_* Λ` is a unit multiple of the identity, `End(i'_* Λ) = End(Λ_k) = ℤ/ℓ` being a field.

This is the input on the fibre of the step of the class of a point through an elementary
fibration (`Stacks.EtaleCohomology.pointClassNonzeroAt_of_fibration_of_section`), in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekIsoOfEq`.
* `Stacks.EtaleCohomology.exists_nsmul_eq_id_of_ne_zero`.
* `Stacks.EtaleCohomology.exists_section_of_homology_map_ne_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

-- `Stacks.EtaleCohomology.PointClassNonzeroAt` reads `ZMod ℓ` as a ring through `ZMod.commRing`.
attribute [-instance] ZMod.instField

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe, on which instance
-- problems below get stuck.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- `Rf₁_! ≅ Rf₂_!` for equal morphisms, through the transported compactification. -/
def derivedLowerShriekIsoOfEq {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂)
    (j₂ : CompactificationOf (Over.mk f₂)) (Λ : Type) [Ring Λ] :
    derivedLowerShriek.{u, 0} f₁ (h.symm ▸ j₂) Λ ≅ derivedLowerShriek.{u, 0} f₂ j₂ Λ := by
  subst h
  exact Iso.refl _

variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] {k : Type u} [Field k]

/-- **A nonzero endomorphism of `i_* Λ` for a `k`-point `i` is a unit multiple of the identity**:
`End(i_* Λ) = End(Λ_k) = ℤ/ℓ`, `i_*` being fully faithful. -/
theorem exists_nsmul_eq_id_of_ne_zero {S : Scheme.{u}} (i : Spec (.of k) ⟶ S)
    [IsClosedImmersion i]
    (a : (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Spec (.of k)) ℓ) ⟶
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := Spec (.of k)) ℓ))
    (ha : a ≠ 0) : ∃ m : ℕ, m • a = 𝟙 _ := by
  let FF := etaleModuleDirectImageFullyFaithful (ZMod ℓ) i
  have := FF.full
  have := FF.faithful
  obtain ⟨b, rfl⟩ := (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).map_surjective a
  have : ConnectedSpace (Spec (.of k)) :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ _).isConnected
  let E : (unitSheaf (X := Spec (.of k)) ℓ ⟶ unitSheaf (X := Spec (.of k)) ℓ) ≃+ ZMod ℓ :=
    Ext.addEquiv₀.symm.trans (extZeroUnitSheafAddEquivOfConnectedSpace ℓ (Spec (.of k)))
  have hb : b ≠ 0 := by
    rintro rfl
    exact ha (Functor.map_zero _ _ _)
  have hEb : E b ≠ 0 := fun h => hb (E.injective (h.trans (map_zero E).symm))
  let : Field (ZMod ℓ) := ZMod.instField ℓ
  refine ⟨(E (𝟙 _) / E b).val, ?_⟩
  have hm : (E (𝟙 _) / E b).val • b = 𝟙 _ := by
    apply E.injective
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact div_mul_cancel₀ _ hEb
  rw [← Functor.map_nsmul, hm, CategoryTheory.Functor.map_id]

variable {U S : Scheme.{u}} (g : U ⟶ S) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  [CompactSpace S] [QuasiSeparatedSpace S]
  (jg : CompactificationOf (Over.mk g))
  (hf : ∀ y : S, topologicalKrullDim (jg.toBase.fiber y) ≤ 1)
  (ν : etaleModuleInverseImage.{u, 0} (ZMod ℓ) g ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedLowerShriek.{u, 0} g jg (ZMod ℓ) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod ℓ) S))

/-- **`Rg_!(p_* Λ) ≅ i'_* Λ`** for a `k`-point `p` over the closed `k`-point `i' = g ∘ p`: Tag 0F7J
for the finite morphism `p`, and `Ri'_! = i'_*` for the closed immersion `i'`. -/
def derivedLowerShriekDirectImageSingleIso (i' : Spec (.of k) ⟶ S) [IsClosedImmersion i']
    (p : Spec (.of k) ⟶ U) [IsClosedImmersion p] (hp : p ≫ g = i') :
    (derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := Spec (.of k)) ℓ))) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := Spec (.of k)) ℓ)) :=
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  let L₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)
  have hL₀ : isTorsionPlus.{u, 0} (ZMod ℓ) (Spec (.of k)) L₀ := fun _ =>
    isTorsionEtaleModule_of_natCast_eq_zero (ZMod ℓ) ℓ hℓ (ZMod.natCast_self ℓ) _
  (derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).mapIso
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleDirectImage.{u, 0} (ZMod ℓ) p) 0).app _) ≪≫
    ((derivedLowerShriekCompDirectImageIsoOfIsFinite (ZMod ℓ) p g jg
      (hp.symm ▸ CompactificationOf.ofProper i')).app ⟨L₀, hL₀⟩).symm ≪≫
    (derivedLowerShriekIsoOfEq hp (CompactificationOf.ofProper i') (ZMod ℓ)).app L₀ ≪≫
    (derivedLowerShriekOfProperIso (ZMod ℓ) i').app L₀ ≪≫
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i') 0).app _).symm

variable [IsSepClosed k]

omit [IsSepClosed k] in
/-- **The top-degree trace of a class with nonzero top image is split.** For a `k`-point `p` over
the closed `k`-point `i' = g ∘ p` and `δ ∈ Ext²_U(p_* Λ, g⁻¹ i'_* Λ)` with
`H⁰(Rg_!(δ)) ≠ 0`, some `σ : i'_* Λ ⟶ Rg_!(p_* Λ)` has `t ∘ Rg_!(δ) ∘ σ = 𝟙`. -/
theorem exists_section_of_homology_map_ne_zero (i' : Spec (.of k) ⟶ S) [IsClosedImmersion i']
    (p : Spec (.of k) ⟶ U) [IsClosedImmersion p] (hp : p ≫ g = i')
    (δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := Spec (.of k)) ℓ))
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := Spec (.of k)) ℓ))) 2)
    (hδ : (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).map (Stacks.TopTruncationExt.extPlus δ)) ≠ 0) :
    ∃ σ : (DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := Spec (.of k)) ℓ)) ⟶
      DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := Spec (.of k)) ℓ)))),
      σ ≫ ((Stacks.TopTruncationExt.extPlus δ).map
        (derivedLowerShriek.{u, 0} g jg (ZMod ℓ) ⋙ DerivedCategory.Plus.ι)).comp
          (lowerShriekTopTrace g jg ℓ hf ν _) (show (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 by norm_num) =
        ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 _) := by
  let X : EtaleModules.{u, 0} (ZMod ℓ) S :=
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := Spec (.of k)) ℓ)
  let Φ := derivedLowerShriek.{u, 0} g jg (ZMod ℓ) ⋙ DerivedCategory.Plus.ι
  let H₀ := DerivedCategory.homologyFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) 0
  let t := lowerShriekTopTrace g jg ℓ hf ν X
  let ψ := DerivedCategory.Plus.ι.mapIso (derivedLowerShriekDirectImageSingleIso ℓ g jg i' p hp)
  let τ := ((Stacks.TopTruncationExt.extPlus δ).map Φ).comp t
    (show (-2 : ℤ) + ((2 : ℕ) : ℤ) = 0 by norm_num)
  -- `H⁰` of the trace, shifted, is invertible
  have hH2 : IsIso ((DerivedCategory.homologyFunctor _ 2).map t) := by
    have h := Stacks.TopTruncationExt.homologyFunctor_map_topProj _ 2
      (isLE_derivedLowerShriek_inverseImage_single g jg ℓ hf X)
    have hA : IsIso ((DerivedCategory.homologyFunctor _ 2).map (Stacks.TopTruncationExt.topProj
        _ 2 (isLE_derivedLowerShriek_inverseImage_single g jg ℓ hf X))) := by
      have : IsIso ((DerivedCategory.homologyFunctor _ 2).map (Stacks.TopTruncationExt.topProj
          _ 2 (isLE_derivedLowerShriek_inverseImage_single g jg ℓ hf X)) ≫
          (Stacks.TopTruncationExt.singleShiftHomologyIso 2).hom.app _) := by
        rw [h]; infer_instance
      exact IsIso.of_isIso_comp_right _
        ((Stacks.TopTruncationExt.singleShiftHomologyIso 2).hom.app _)
    have hB : IsIso ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) 2).map
        (((DerivedCategory.singleFunctor _ 0).map (ν.hom.app X))⟦(-2 : ℤ)⟧')) := inferInstance
    simp only [t, lowerShriekTopTrace, Stacks.TopTruncationExt.topTrace, Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hA hB
  have hH0 : IsIso (H₀.map (t⟦((2 : ℕ) : ℤ)⟧')) :=
    (NatIso.isIso_map_iff ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} (ZMod ℓ) S)
      0).shiftIso ((2 : ℕ) : ℤ) 0 (2 : ℤ) (by norm_num)) t).2 hH2
  -- `τ` is nonzero
  let r := H₀.map ((Φ.commShiftIso ((2 : ℕ) : ℤ)).hom.app _) ≫ H₀.map (t⟦((2 : ℕ) : ℤ)⟧') ≫
    H₀.map ((shiftFunctorAdd' (DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) S)) (-2)
      ((2 : ℕ) : ℤ) 0 (by norm_num)).inv.app _)
  have : IsIso r := by dsimp only [r]; infer_instance
  have hτ : H₀.map τ = H₀.map (Φ.map (Stacks.TopTruncationExt.extPlus δ)) ≫ r := by
    simp only [τ, r, ShiftedHom.comp, ShiftedHom.map, Functor.map_comp, Category.assoc]
    rfl
  let φ := ψ.inv ≫ τ
  have hφ : φ ≠ 0 := by
    intro h0
    apply hδ
    have hτφ : τ = ψ.hom ≫ φ := (Iso.hom_inv_id_assoc ψ τ).symm
    have h1 : H₀.map τ = 0 := by
      rw [hτφ, h0, comp_zero, Functor.map_zero]
    rw [hτ] at h1
    exact (@cancel_mono _ _ _ _ _ r (IsIso.mono_of_iso r) _ _).1
      (h1.trans (zero_comp (f := r)).symm)
  -- `φ` is a unit multiple of the identity
  let z₀ := (shiftFunctorZero' (DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) S)) (0 : ℤ) rfl)
  obtain ⟨a, ha⟩ :=
    (DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) 0).map_surjective
      (φ ≫ z₀.hom.app _)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hφ
    have h := ha.symm
    rw [Functor.map_zero] at h
    exact (cancel_mono (z₀.hom.app _)).1 (h.trans (zero_comp (f := z₀.hom.app _)).symm)
  obtain ⟨m, hm⟩ := exists_nsmul_eq_id_of_ne_zero ℓ i' a ha0
  refine ⟨m • ψ.inv, ?_⟩
  have hφm : (m • ψ.inv) ≫ τ = m • φ := Preadditive.nsmul_comp _ _ _
  have gen : ∀ {A B C : DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) S)} (f : A ⟶ B) (e : B ≅ C)
      (g : A ⟶ C), g = f ≫ e.hom → f = g ≫ e.inv := by
    intro A B C f e g h
    rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e1 := gen φ (z₀.app _) _ ha
  have e2 : m • (DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) 0).map a = 𝟙 _ := by
    rw [← Functor.map_nsmul, hm, CategoryTheory.Functor.map_id]
  have h2 : m • φ = ShiftedHom.mk₀ (0 : ℤ) rfl
      (𝟙 ((DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) 0).obj X)) :=
    (congrArg (fun x => m • x) e1).trans ((Preadditive.nsmul_comp _ _ _).symm.trans
      (congrArg (· ≫ (z₀.app _).inv) e2))
  exact hφm.trans h2

end Stacks.EtaleCohomology

end
