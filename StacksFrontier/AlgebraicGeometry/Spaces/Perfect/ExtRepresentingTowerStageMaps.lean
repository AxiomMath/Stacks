module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtRepresentingTower

/-!
# The pseudo-coherent object representing `Ext` out of a tower, with its stage maps

`AlgebraicGeometry.Space.exists_isPseudoCoherent_extAddEquiv_of_tower` produces, from a tower
`L₀ ⟶ L₁ ⟶ ⋯` of perfect objects of `D(𝒪_Y)` representing `Ext` out of a tower of perfect
approximations `Eₙ ⟶ E`, a pseudo-coherent `L ∈ D(𝒪_Y)` representing `Ext` out of `E`.  The form
here also returns the maps `ιₙ : Lₙ ⟶ L` (compatible with the tower, and isomorphisms on
cohomology in degrees `> -(n + a)`), and the identification of `Ext^i(L, F) ≅ Ext^i(E, M(F))` with
`Ψₙ` at every stage `n`, not only for `n` large compared to `i`.

## Main results

* `AlgebraicGeometry.Space.exists_isPseudoCoherent_extAddEquiv_stageMaps_of_tower`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated


universe w w' v' u' u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] pointTopology smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

variable (Y : AlgebraicSpaces B S hS) [HasDerivedCategory.{w} (Modules.{u, u} B S hS Y.1 Y.2)]
  {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜]

/-- **`Ext` out of a pseudo-coherent object representing a tower of perfect approximations, with
the maps from the stages of the tower.**  As
`AlgebraicGeometry.Space.exists_isPseudoCoherent_extAddEquiv_of_tower`, also returning the maps
`ιₙ : Lₙ ⟶ L` and the compatibility of the identification with `Ψₙ` at every stage `n`. -/
theorem exists_isPseudoCoherent_extAddEquiv_stageMaps_of_tower (hY : IsQuasiCompactSpace B S hS Y.1)
    (E : DerivedCategory 𝒜) (tE : ℕ ⥤ DerivedCategory 𝒜) (cE : ∀ n, tE.obj n ⟶ E)
    (hcEcomp : ∀ n, tE.map (homOfLE (Nat.le_succ n)) ≫ cE (n + 1) = cE n)
    (hcE : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + 2) < j →
      IsIso ((DerivedCategory.homologyFunctor 𝒜 j).map (cE n)))
    (M : Modules.{u, u} B S hS Y.1 Y.2 ⥤ DerivedCategory 𝒜) (a : ℤ)
    (hM : ∀ F : Modules.{u, u} B S hS Y.1 Y.2, F.IsQuasicoherentOnSite → (M.obj F).IsGE a)
    (L : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hL : ∀ n, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect (L.obj n))
    (Ψ : ∀ (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
      (L.obj n ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) ≃+ (tE.obj n ⟶ (M.obj F)⟦i⟧))
    (hΨnat : ∀ (n : ℕ) {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
      (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
      (e : L.obj n ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧),
      Ψ n F' hF' i (e ≫ ((DerivedCategory.singleFunctor _ 0).map q)⟦i⟧') =
        Ψ n F hF i e ≫ (M.map q)⟦i⟧')
    (hΨtrans : ∀ (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite)
      (i : ℤ) (e : L.obj (n + 1) ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧),
      Ψ n F hF i (L.map (homOfLE (Nat.le_succ n)) ≫ e) =
        tE.map (homOfLE (Nat.le_succ n)) ≫ Ψ (n + 1) F hF i e)
    (δX : ∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)), T.ShortExact →
      T.X₁.IsQuasicoherentOnSite → T.X₂.IsQuasicoherentOnSite → T.X₃.IsQuasicoherentOnSite →
        (M.obj T.X₃ ⟶ (M.obj T.X₁)⟦(1 : ℤ)⟧))
    (hΨδ : ∀ (n : ℕ) (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
      (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
      (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
      (e : ShiftedHom (L.obj n) ((DerivedCategory.singleFunctor _ 0).obj T.X₃) i),
      Ψ n T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
        (show ShiftedHom (tE.obj n) (M.obj T.X₃) i from Ψ n T.X₃ h₃ i e).comp
          (δX T hT h₁ h₂ h₃) (add_comm 1 i)) :
    ∃ (Linf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (ι : ∀ n, L.obj n ⟶ Linf)
      (_ : ∀ n, L.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n)
      (_ : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + a) < j →
        IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) j).map (ι n)))
      (_ : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent Linf)
      (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        (Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) ≃+ (E ⟶ (M.obj F)⟦i⟧)),
      (∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) (i : ℤ)
        (e : Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) (n : ℕ),
        cE n ≫ Φ F hF i e = Ψ n F hF i (ι n ≫ e)) ∧
      (∀ {F F' : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
        (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ)
        (e : Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧),
        Φ F' hF' i (e ≫ ((DerivedCategory.singleFunctor _ 0).map q)⟦i⟧') =
          Φ F hF i e ≫ (M.map q)⟦i⟧') ∧
      (∀ (T : ShortComplex (Modules.{u, u} B S hS Y.1 Y.2)) (hT : T.ShortExact)
        (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite)
        (h₃ : T.X₃.IsQuasicoherentOnSite) (i : ℤ)
        (e : ShiftedHom Linf ((DerivedCategory.singleFunctor _ 0).obj T.X₃) i),
        Φ T.X₁ h₁ (i + 1) (e.comp hT.singleδ (add_comm 1 i)) =
          (show ShiftedHom E (M.obj T.X₃) i from Φ T.X₃ h₃ i e).comp
            (δX T hT h₁ h₂ h₃) (add_comm 1 i)) := by
  have := hasColimitsOfShape_discrete_nat_derivedCategory_modules B S hS Y.1 Y.2
  -- Step 1: precomposition with `cE n` and with the transition maps of `E`.
  have hbE : ∀ (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite)
      (i : ℤ), i ≤ n + a → Function.Bijective (fun e : E ⟶ (M.obj F)⟦i⟧ => cE n ≫ e) :=
    fun n F hF i hi => by
      have := hM F hF
      exact DerivedCategory.bijective_comp_shiftedHom_of_isIso_homologyFunctor_map (cE n)
        (-((n : ℤ) + 2)) (hcE n) (M.obj F) a i (by omega)
  have hbtE : ∀ (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite)
      (i : ℤ), i ≤ n + a → Function.Bijective
        (fun e : tE.obj (n + 1) ⟶ (M.obj F)⟦i⟧ => tE.map (homOfLE (Nat.le_succ n)) ≫ e) := by
    intro n F hF i hi
    have h1 := hbE (n + 1) F hF i (by push_cast; omega)
    have h0 := hbE n F hF i hi
    have hcomp : (fun e : E ⟶ (M.obj F)⟦i⟧ => cE n ≫ e) =
        (fun e : tE.obj (n + 1) ⟶ (M.obj F)⟦i⟧ => tE.map (homOfLE (Nat.le_succ n)) ≫ e) ∘
          (fun e : E ⟶ (M.obj F)⟦i⟧ => cE (n + 1) ≫ e) := by
      funext e
      simp only [Function.comp_apply, ← Category.assoc, hcEcomp]
    rw [hcomp] at h0
    exact (Function.Bijective.of_comp_iff _ h1).1 h0
  -- Step 2: the transition maps of `L` are bijective on `Ext^i(-, F)` for `i ≤ n + a`.
  have hbL : ∀ (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite)
      (i : ℤ), i ≤ n + a → Function.Bijective
        (fun e : L.obj (n + 1) ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧ =>
          L.map (homOfLE (Nat.le_succ n)) ≫ e) := by
    intro n F hF i hi
    have hcomp : (fun e : L.obj (n + 1) ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧ =>
          L.map (homOfLE (Nat.le_succ n)) ≫ e) =
        (Ψ n F hF i).symm ∘
          (fun e : tE.obj (n + 1) ⟶ (M.obj F)⟦i⟧ => tE.map (homOfLE (Nat.le_succ n)) ≫ e) ∘
            (Ψ (n + 1) F hF i) := by
      funext e
      simp only [Function.comp_apply, ← hΨtrans, AddEquiv.symm_apply_apply]
    rw [hcomp]
    exact (Ψ n F hF i).symm.bijective.comp ((hbtE n F hF i hi).comp (Ψ (n + 1) F hF i).bijective)
  -- Step 3: hence they are isomorphisms on cohomology in degrees `> -(n + a)`.
  have hLiso : ∀ (n : ℕ) (j : ℤ), -((n : ℤ) + a) < j →
      IsIso ((DerivedCategory.homologyFunctor _ j).map (L.map (homOfLE (Nat.le_succ n)))) := by
    intro n j hj
    obtain ⟨D, g, h, hT⟩ := distinguished_cocone_triangle (L.map (homOfLE (Nat.le_succ n)))
    have hD : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect D :=
      RingedSite.isPerfect_obj₃_of_distinguished_general _ _ hT (hL n) (hL (n + 1))
    obtain ⟨t₀, ht₀⟩ := exists_isZero_homology_of_lt_of_isPerfect Y hY D hD
    have : D.IsLE t₀ := by rwa [DerivedCategory.isLE_iff]
    exact DerivedCategory.isIso_homologyFunctor_map_of_bijective_comp_shiftedHom _ g h hT t₀
      ((n : ℤ) + a) (fun F => F.IsQuasicoherentOnSite)
      (derivedCategoryB_isQuasicoherentOnSite_of_isPerfect Y D hD)
      (hbL n) j (by omega)
  -- Step 4: the homotopy colimit.
  obtain ⟨Linf, ι, hcolim, hι⟩ := exists_isHomotopyColimitWith_isIso_homology_of_tower B S hS Y.1
    Y.2 L (fun n => -((n : ℤ) + a)) (fun n => by push_cast; omega) hLiso
  have hpc : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent Linf :=
    isPseudoCoherent_of_isIso_homology_of_isPerfect B S hS Y.1 Y.2 L.obj ι _ hL hι
      (fun m => ⟨(-a - m + 1).toNat, by omega⟩)
  have hιcomp : ∀ n, L.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n := by
    obtain ⟨p, q, hT, hp⟩ := hcolim
    intro n
    have h1 := Sigma.ι L.obj n ≫= comp_distTriang_mor_zero₁₂ _ hT
    simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, comp_zero, ← Category.assoc, Sigma.ι_comp_desc,
      Preadditive.sub_comp] at h1
    rw [← hp, ← hp]
    simp only [Category.assoc] at h1
    exact (sub_eq_zero.1 h1).symm
  -- Step 5: `Ext^i(Linf, F) = Ext^i(Lₙ, F)` for `i ≤ n + a - 2`.
  have hbι : ∀ (n : ℕ) (F : Modules.{u, u} B S hS Y.1 Y.2) (i : ℤ), i ≤ n + a - 2 →
      Function.Bijective
        (fun e : Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧ => ι n ≫ e) :=
    fun n F i hi => DerivedCategory.bijective_comp_shiftedHom_of_isIso_homologyFunctor_map (ι n)
      (-((n : ℤ) + a)) (hι n) _ 0 i (by omega)
  -- Step 6: the isomorphisms, read through the stage `n(i)`.
  let N : ℤ → ℕ := fun i => (i - a + 2).toNat
  have hN : ∀ i : ℤ, i ≤ (N i : ℤ) + a - 2 := fun i => by
    change i ≤ ((i - a + 2).toNat : ℤ) + a - 2
    omega
  let Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
      (Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) ≃+ (E ⟶ (M.obj F)⟦i⟧) :=
    fun F hF i =>
      (AddEquiv.ofBijective (Preadditive.leftComp _ (ι (N i))) (hbι (N i) F i (hN i))).trans
        ((Ψ (N i) F hF i).trans
          (AddEquiv.ofBijective (Preadditive.leftComp _ (cE (N i)))
            (hbE (N i) F hF i (by have := hN i; omega))).symm)
  -- the characterisation of `Φ` at every stage `n ≥ n(i)`
  have hchar : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) (i : ℤ)
      (e : Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) (k : ℕ),
      cE (N i + k) ≫ Φ F hF i e = Ψ (N i + k) F hF i (ι (N i + k) ≫ e) := by
    intro F hF i e k
    induction k with
    | zero =>
      exact (AddEquiv.ofBijective (Preadditive.leftComp _ (cE (N i)))
        (hbE (N i) F hF i (by have := hN i; omega))).apply_symm_apply _
    | succ k ih =>
      apply (hbtE (N i + k) F hF i (by have := hN i; omega)).1
      change tE.map _ ≫ cE (N i + k + 1) ≫ Φ F hF i e =
        tE.map _ ≫ Ψ (N i + k + 1) F hF i (ι (N i + k + 1) ≫ e)
      rw [← Category.assoc, hcEcomp, ih, ← hΨtrans, ← Category.assoc, hιcomp]
  have hchar' : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) (i : ℤ)
      (e : Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) (n : ℕ), N i ≤ n →
      cE n ≫ Φ F hF i e = Ψ n F hF i (ι n ≫ e) := by
    intro F hF i e n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact hchar F hF i e k
  -- the characterisation at every stage, also below `n(i)`
  have hcharAll : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (hF : F.IsQuasicoherentOnSite) (i : ℤ)
      (e : Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) (n : ℕ),
      cE n ≫ Φ F hF i e = Ψ n F hF i (ι n ≫ e) := by
    intro F hF i e n
    by_cases hn : N i ≤ n
    · exact hchar' F hF i e n hn
    · obtain ⟨k, hk⟩ : ∃ k, n + k = N i := ⟨N i - n, by omega⟩
      induction k generalizing n with
      | zero => exact absurd (by omega : N i ≤ n) hn
      | succ k ih =>
        have h1 : cE (n + 1) ≫ Φ F hF i e = Ψ (n + 1) F hF i (ι (n + 1) ≫ e) := by
          by_cases hn' : N i ≤ n + 1
          · exact hchar' F hF i e (n + 1) hn'
          · exact ih (n + 1) hn' (by omega)
        rw [← hcEcomp, Category.assoc, h1, ← hΨtrans, ← Category.assoc, hιcomp]
  refine ⟨Linf, ι, hιcomp, hι, hpc, Φ, hcharAll, ?_, ?_⟩
  · intro F F' hF hF' q i e
    apply (hbE (N i) F' hF' i (by have := hN i; omega)).1
    change cE (N i) ≫ Φ F' hF' i _ = cE (N i) ≫ Φ F hF i e ≫ _
    rw [hchar' F' hF' i _ (N i) le_rfl, ← Category.assoc (cE (N i)),
      hchar' F hF i e (N i) le_rfl, ← hΨnat, Category.assoc]
  · intro T hT h₁ h₂ h₃ i e
    let n := max (N i) (N (i + 1))
    apply (hbE n T.X₁ h₁ (i + 1) (by have := hN (i + 1); omega)).1
    change cE n ≫ Φ T.X₁ h₁ (i + 1) _ = cE n ≫ _
    rw [hchar' T.X₁ h₁ (i + 1) _ n (le_max_right _ _)]
    have h1 : ι n ≫ (e.comp hT.singleδ (add_comm 1 i)) =
        (show ShiftedHom (L.obj n) _ i from ι n ≫ e).comp hT.singleδ (add_comm 1 i) := by
      simp only [ShiftedHom.comp, Category.assoc]
    have h2 : cE n ≫ (show ShiftedHom E (M.obj T.X₃) i from Φ T.X₃ h₃ i e).comp
          (δX T hT h₁ h₂ h₃) (add_comm 1 i) =
        (show ShiftedHom (tE.obj n) (M.obj T.X₃) i from cE n ≫ Φ T.X₃ h₃ i e).comp
          (δX T hT h₁ h₂ h₃) (add_comm 1 i) := by
      simp only [ShiftedHom.comp, Category.assoc]
    rw [h1, hΨδ, h2, hchar' T.X₃ h₃ i e n (le_max_left _ _)]


end AlgebraicGeometry.Space

end
