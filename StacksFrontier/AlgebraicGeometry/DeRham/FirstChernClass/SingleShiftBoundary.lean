module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct

/-!
# A morphism into a translate, read through the single functors

Let `Φ : D⁺(𝒜) ⥤ D⁺(ℬ)` commute with the shift and put `Ψ = Φ ∘ Q`. A morphism
`τ : Z[0] ⟶ K[1]` of bounded below complexes from an object placed in degree zero to a translate
induces `H¹(Ψ(Z[0])) ⟶ H¹(Ψ(K[1])) = H²(Ψ K)`. Translating `τ` back by one gives a morphism
`ι : Z[-1] ⟶ K` from the object placed in degree one, which induces
`H²(Ψ(Z[-1])) ⟶ H²(Ψ K)`. This file proves that the two agree through the identification
`H²(Ψ(Z[-1])) ≅ H¹(Ψ(Z[0]))` of `DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`,
which is the identification `H¹(X, F) ≅ H²(X, F[-1])` the de Rham first Chern class of
[Stacks, Tag 0FLE] is taken through.

## Main results

* `AlgebraicGeometry.SheafOfModules.homology_map_comp_shiftHomologyIso_eq`: the comparison.
* `AlgebraicGeometry.SheafOfModules.shiftHomologyIso_add`,
  `AlgebraicGeometry.SheafOfModules.shiftHomologyIso_zero`: the identifications
  `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)` of `D⁺` compose, and are the identity at `s = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SheafOfModules

open Stacks.Cohomology.RealizationShift (shiftHomologyIso shiftHomologyIsoU)

section Generic

variable {V W : Type*} [Category* V] [Category* W] [Abelian V] [Abelian W] [HasDerivedCategory V]
  [HasDerivedCategory W] (Φ : DerivedCategory.Plus V ⥤ DerivedCategory.Plus W) [Φ.CommShift ℤ]

/-- `shiftHomologyIso` at the shift by zero is the map induced by the identification of the shift
by zero with the identity. -/
theorem shiftHomologyIso_zero {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C ⥤ DerivedCategory.Plus W) [F.CommShift ℤ] (X : C) (n : ℤ) :
    (shiftHomologyIso F X 0 n n (zero_add n)).hom =
      (DerivedCategory.Plus.homologyFunctor W n).map
        (F.map ((shiftFunctorZero C ℤ).hom.app X)) := by
  change (DerivedCategory.Plus.homologyFunctor W n).map ((F.commShiftIso (0 : ℤ)).hom.app X) ≫
    ((DerivedCategory.Plus.homologyFunctor W 0).shiftIso 0 n n (zero_add n)).hom.app (F.obj X) = _
  rw [Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
    Functor.shiftIso_zero_hom_app, Functor.map_comp]
  change ((DerivedCategory.Plus.homologyFunctor W n).map _ ≫
    (DerivedCategory.Plus.homologyFunctor W n).map _) ≫
      (DerivedCategory.Plus.homologyFunctor W n).map _ = _
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (congrArg (_ ≫ ·) ((DerivedCategory.Plus.homologyFunctor W n).map_id _)).trans
    (Category.comp_id _)

/-- **The identifications `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)` compose**, in `D⁺`. -/
theorem shiftHomologyIso_add {C : Type*} [Category* C] [HasShift C ℤ]
    (F : C ⥤ DerivedCategory.Plus W) [F.CommShift ℤ] (X : C)
    (t₁ t₂ t : ℤ) (ht : t₂ + t₁ = t) (a a' a'' : ℤ) (h₁ : t₁ + a = a') (h₂ : t₂ + a' = a'') :
    (shiftHomologyIso F (X⟦t₂⟧) t₁ a a' h₁).hom ≫ (shiftHomologyIso F X t₂ a' a'' h₂).hom =
      (DerivedCategory.Plus.homologyFunctor W a).map
          (F.map ((shiftFunctorAdd' C t₂ t₁ t ht).inv.app X)) ≫
        (shiftHomologyIso F X t a a'' (by omega)).hom := by
  rw [Stacks.Cohomology.RealizationShift.shiftHomologyIso_eq_U,
    Stacks.Cohomology.RealizationShift.shiftHomologyIso_eq_U,
    Stacks.Cohomology.RealizationShift.shiftHomologyIso_eq_U]
  exact Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_add _ X t₁ t₂ t ht a a' a'' h₁ h₂

/-- The algebra of `homology_map_comp_shiftHomologyIso_eq`, with every object and morphism a
variable. -/
private theorem shift_paste {C : Type*} [Category* C] {P R Q T U V Vz : C} (σ : P ≅ Q)
    (Hj : P ⟶ R) (s₀ : R ⟶ Q) (Hτ : Q ⟶ U) (sK : U ⟶ V) (Hτ' : R ⟶ T) (s₁ : T ⟶ U)
    (Ha : T ⟶ Vz) (sz : Vz ⟶ V) (Hι : P ⟶ V) (he : σ.hom = Hj ≫ s₀)
    (hn : Hτ' ≫ s₁ = s₀ ≫ Hτ) (hadd : s₁ ≫ sK = Ha ≫ sz) (hι : Hj ≫ Hτ' ≫ Ha ≫ sz = Hι) :
    Hτ ≫ sK = σ.inv ≫ Hι := by
  rw [Iso.eq_inv_comp, he, ← hι, Category.assoc, ← reassoc_of% hn, hadd]

/-- A functor applied to a three-fold composite, with every object and morphism a variable. -/
private theorem map_three {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {p q r s : C}
    (a : p ⟶ q) (b : q ⟶ r) (c : r ⟶ s) (w : p ⟶ s) (h : a ≫ b ≫ c = w) :
    H.map a ≫ H.map b ≫ H.map c = H.map w := by
  rw [← h, H.map_comp, H.map_comp]

/-- A functor applied to a four-fold composite, with every object and morphism a variable. -/
private theorem map_four {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {p q r s t : C}
    (a : p ⟶ q) (b : q ⟶ r) (c : r ⟶ s) (d : s ⟶ t) (cd : r ⟶ t) (w : p ⟶ t)
    (hcd : c ≫ d = cd) (hw : a ≫ b ≫ cd = w) :
    H.map a ≫ H.map b ≫ H.map c ≫ H.map d = H.map w := by
  rw [← hw, ← hcd, H.map_comp, H.map_comp, H.map_comp]

/-- **A morphism `Z[0] ⟶ K[1]` and its translate `Z[-1] ⟶ K` induce the same map on cohomology**:
the map `H¹(Ψ(Z[0])) ⟶ H¹(Ψ(K[1])) = H²(Ψ K)` induced by `τ : Z[0] ⟶ K[1]` is the identification
`H¹(Ψ(Z[0])) ≅ H²(Ψ(Z[-1]))` followed by the map induced by the translate `ι : Z[-1] ⟶ K` of `τ`,
for `Ψ = Φ ∘ Q`. -/
theorem homology_map_comp_shiftHomologyIso_eq (Z : V) (K : CochainComplex.Plus V)
    (τ : (Stacks.DerivedIndexing.singlePlusFunctor V 0).obj Z ⟶ K⟦(1 : ℤ)⟧)
    (ι : (Stacks.DerivedIndexing.singlePlusFunctor V 1).obj Z ⟶ K)
    (hι : ((Stacks.DerivedIndexing.cplusSingleFunctors V).shiftIso (-1) 1 0 (by omega)).inv.app Z ≫
      τ⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (CochainComplex.Plus V) (1 : ℤ) (-1) (by omega)).hom.app K = ι) :
    (DerivedCategory.Plus.homologyFunctor W 1).map ((DerivedCategory.Plus.Q ⋙ Φ).map τ) ≫
        (shiftHomologyIso (DerivedCategory.Plus.Q ⋙ Φ) K 1 1 2 (by omega)).hom =
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso Φ 1 1).app Z).inv ≫
        (DerivedCategory.Plus.homologyFunctor W (1 + 1)).map
          ((DerivedCategory.Plus.Q ⋙ Φ).map ι) := by
  let Ψ := DerivedCategory.Plus.Q ⋙ Φ
  have hadd := shiftHomologyIso_add Ψ K (-1) 1 0 (by omega) 2 1 2 (by omega) (by omega)
  rw [shiftHomologyIso_zero Ψ K 2] at hadd
  exact shift_paste _ _ _ _ _ _ _ _ _ _ (singleFunctorCompHomologyFunctorShiftIso_app_hom Φ 1 1 Z)
    (Stacks.Cohomology.RealizationShift.shiftHomologyIso_naturality Ψ τ (-1) 2 1 (by omega)) hadd
    (map_four (DerivedCategory.Plus.homologyFunctor W 2) (Ψ.map _) (Ψ.map _) (Ψ.map _) (Ψ.map _)
      (Ψ.map ((shiftFunctorCompIsoId (CochainComplex.Plus V) (1 : ℤ) (-1) (by omega)).hom.app K)) _
      ((Ψ.map_comp _ _).symm.trans rfl) (map_three Ψ _ _ _ _ hι))

/-- The algebra of `homology_map_comp_shiftHomologyIso_eq_of_cochain`, with every object and
morphism a variable. -/
private theorem cc_paste {C : Type*} [Category* C] (G : C ⥤ C) {p q r s t m m' : C}
    (a : p ⟶ q) (x : q ⟶ r) (cB : r ⟶ G.obj m') (cs : m' ⟶ s) (w : G.obj s ⟶ t)
    (cA : q ⟶ G.obj m) (Ai : p ⟶ G.obj m) (mt : m ⟶ m') (Tm : m ⟶ s) (csi : s ⟶ m')
    (ι' : p ⟶ t) (h₁ : a ≫ cA = Ai) (h₃ : x ≫ cB = cA ≫ G.map mt)
    (hτ : mt = Tm ≫ csi) (hcs : csi ≫ cs = 𝟙 _) (hι : Ai ≫ G.map Tm ≫ w = ι') :
    a ≫ x ≫ (cB ≫ G.map cs ≫ w) = ι' := by
  rw [← Category.assoc x, h₃, Category.assoc, ← Category.assoc a, h₁, hτ, ← G.map_comp_assoc,
    Category.assoc, hcs, Category.comp_id, hι]

/-- **A morphism `Z[0] ⟶ K[1]` and its translate `Z[-1] ⟶ K` induce the same map on cohomology**,
for a morphism `T : Z[0] ⟶ K[1]` of complexes, read in bounded below complexes through the
commutation of the inclusion with the shift: it suffices that the translate of `T`, through the
comparison of the single functors with the shift, is `ι`. -/
theorem homology_map_comp_shiftHomologyIso_eq_of_cochain (Z : V) (K : CochainComplex.Plus V)
    (T : (CochainComplex.Plus.ι V).obj ((Stacks.DerivedIndexing.singlePlusFunctor V 0).obj Z) ⟶
      (CochainComplex.Plus.ι V ⋙ shiftFunctor _ (1 : ℤ)).obj K)
    (ι : (CochainComplex.singleFunctor V 1).obj Z ⟶ K.obj)
    (hι : ((CochainComplex.singleFunctors V).shiftIso (-1) 1 0 (by omega)).inv.app Z ≫
      T⟦(-1 : ℤ)⟧' ≫ (shiftFunctorCompIsoId (CochainComplex V ℤ) (1 : ℤ) (-1) (by omega)).hom.app
        K.obj = ι) :
    (DerivedCategory.Plus.homologyFunctor W 1).map ((DerivedCategory.Plus.Q ⋙ Φ).map
        ((CochainComplex.Plus.ι V).preimage
          (T ≫ ((CochainComplex.Plus.ι V).commShiftIso (1 : ℤ)).inv.app K))) ≫
        (shiftHomologyIso (DerivedCategory.Plus.Q ⋙ Φ) K 1 1 2 (by omega)).hom =
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso Φ 1 1).app Z).inv ≫
        (DerivedCategory.Plus.homologyFunctor W (1 + 1)).map
          ((DerivedCategory.Plus.Q ⋙ Φ).map (ObjectProperty.homMk ι :
            (Stacks.DerivedIndexing.singlePlusFunctor V 1).obj Z ⟶ K)) := by
  refine homology_map_comp_shiftHomologyIso_eq Φ Z K _ _ ?_
  apply (CochainComplex.Plus.ι V).map_injective
  have h₁ := ι_map_cplusSingleFunctors_shiftIso_inv_app (-1) 1 0 (by omega) Z
  have h₃ := (CochainComplex.Plus.ι V).commShiftIso_hom_naturality
    ((CochainComplex.Plus.ι V).preimage
      (T ≫ ((CochainComplex.Plus.ι V).commShiftIso (1 : ℤ)).inv.app K)) (-1 : ℤ)
  rw [Functor.map_comp, Functor.map_comp,
    (CochainComplex.Plus.ι V).map_shiftFunctorCompIsoId_hom_app K (1 : ℤ) (-1) (by omega)]
  exact cc_paste (shiftFunctor (CochainComplex V ℤ) (-1 : ℤ)) _ _ _ _ _ _ _ _ _ _ _ h₁
    h₃ ((CochainComplex.Plus.ι V).map_preimage _) (Iso.inv_hom_id_app _ _) hι

end Generic

end AlgebraicGeometry.SheafOfModules

end
