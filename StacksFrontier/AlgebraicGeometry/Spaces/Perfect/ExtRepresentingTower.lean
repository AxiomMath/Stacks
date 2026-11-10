module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTowerHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectSupportedExtensionCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral

/-!
# A pseudo-coherent object representing `Ext` out of a tower of perfect approximations

This is the formal part of the proof of Stacks 08JR, part (B).  Let `Y` be a quasi-compact
algebraic space and `𝒜` an abelian category.  Suppose given

* an object `E` of `D(𝒜)` with a tower `E₀ ⟶ E₁ ⟶ ⋯ ⟶ E` whose `n`-th map is an isomorphism on
  cohomology in degrees `> -(n + 2)` (the approximations of Stacks 0DKB),
* a functor `F ↦ M(F)` from `𝒪_Y`-modules to `D(𝒜)` whose values on quasi-coherent `F` live in
  degrees `≥ a` (the coefficient complexes `𝒢^• ⊗ f^*F`),
* a tower `L₀ ⟶ L₁ ⟶ ⋯` of perfect objects of `D(𝒪_Y)` and isomorphisms
  `Ψₙ : Ext^i(Lₙ, F) ≅ Ext^i(Eₙ, M(F))`, natural in `F`, compatible with the boundary maps and
  with the two towers.

Then there is a pseudo-coherent `L ∈ D(𝒪_Y)` with isomorphisms
`Ext^i(L, F) ≅ Ext^i(E, M(F))`, natural in `F` and compatible with the boundary maps.

The proof is the source's.  Precomposition with `Eₙ ⟶ E` is bijective on `Ext^i(-, M(F))` for
`i ≤ n + a` (Stacks 06XS), hence so is `Ext^i(Lₙ₊₁, F) ⟶ Ext^i(Lₙ, F)`; looking at the top
cohomology sheaf of the cone, `Lₙ ⟶ Lₙ₊₁` is an isomorphism on cohomology in degrees `> -(n + a)`.
So `L = hocolim Lₙ` is pseudo-coherent and `Ext^i(L, F) = Ext^i(Lₙ, F)` for `i ≤ n + a - 2`.

## Main results

* `AlgebraicGeometry.Space.exists_isPseudoCoherent_extAddEquiv_of_tower`.
* `AlgebraicGeometry.Space.exists_isPerfect_bijective_comp_shiftedHom`: the comparison of the
  proof of part (A), `Ext^i(E, M) = Ext^i(P, M)` for `i ≤ m` and a perfect approximation `P ⟶ E`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
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

/-- Precomposition commutes with composition of shifted morphisms. -/
private theorem comp_shiftedHom_comp {C : Type*} [Category C] [HasShift C ℤ] {X X' Y Z : C}
    (f : X ⟶ X') {i j k : ℤ} (x : ShiftedHom X' Y i) (y : ShiftedHom Y Z j) (h : j + i = k) :
    f ≫ x.comp y h = (show ShiftedHom X Y i from f ≫ x).comp y h := by
  simp only [ShiftedHom.comp, Category.assoc]

/-- **`Ext` out of a pseudo-coherent object representing a tower of perfect approximations.**
See the module documentation. The quasi-coherent `𝒪_Y`-modules are the class
`IsQuasicoherentOnSite`; `δX` is the boundary map in `D(𝒜)` attached to a short exact sequence of
quasi-coherent modules, and `Ψ` is compatible with it and with the boundary map
`ShortComplex.ShortExact.singleδ` of `D(𝒪_Y)`. -/
theorem exists_isPseudoCoherent_extAddEquiv_of_tower (hY : IsQuasiCompactSpace B S hS Y.1)
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
    ∃ (Linf : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (_ : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent Linf)
      (Φ : ∀ (F : Modules.{u, u} B S hS Y.1 Y.2) (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        (Linf ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧) ≃+ (E ⟶ (M.obj F)⟦i⟧)),
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
    have h0 := hbE n F hF i hi
    have hcomp : (fun e : E ⟶ (M.obj F)⟦i⟧ => cE n ≫ e) =
        (fun e : tE.obj (n + 1) ⟶ (M.obj F)⟦i⟧ => tE.map (homOfLE (Nat.le_succ n)) ≫ e) ∘
          (fun e : E ⟶ (M.obj F)⟦i⟧ => cE (n + 1) ≫ e) := by
      funext e
      simp only [Function.comp_apply, ← Category.assoc, hcEcomp]
    rw [hcomp] at h0
    exact (Function.Bijective.of_comp_iff _ (hbE (n + 1) F hF i (by push_cast; omega))).1 h0
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
    have h1 := congrArg (fun φ => Sigma.ι L.obj n ≫ φ) (comp_distTriang_mor_zero₁₂ _ hT)
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
  refine ⟨Linf, hpc, Φ, ?_, ?_⟩
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
    rw [comp_shiftedHom_comp, hΨδ, comp_shiftedHom_comp, hchar' T.X₃ h₃ i e n (le_max_left _ _)]

/-- **`Ext` out of a pseudo-coherent object is `Ext` out of a perfect approximation in a range of
degrees** (the first paragraph of the proof of Stacks 08JR). On a quasi-compact and
quasi-separated algebraic space, for a pseudo-coherent `K` and integers `m`, `a` there are a
perfect `P` and a map `α : P ⟶ K` such that `Ext^i(K, M) ⟶ Ext^i(P, M)` is bijective for every
`M ≥ a` and every `i ≤ m`: take an approximation of `(|X|, K, a - m - 1)` (Stacks 08HP); its cone
lives in degrees `≤ a - m - 2` (Stacks 06XS). -/
theorem exists_isPerfect_bijective_comp_shiftedHom (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (K : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hK : (smallEtaleRingedSite B S hS X hX).IsPseudoCoherent K) (m a : ℤ) :
    ∃ (P : DerivedCategory (Modules.{u, u} B S hS X hX))
      (_ : (smallEtaleRingedSite B S hS X hX).IsPerfect P) (α : P ⟶ K),
      ∀ (M : DerivedCategory (Modules.{u, u} B S hS X hX)) [M.IsGE a] (i : ℤ), i ≤ m →
        Function.Bijective (fun e : K ⟶ M⟦i⟧ => α ≫ e) := by
  obtain ⟨P, hP, α, hiso, hepi⟩ :=
    exists_isPerfect_approximation_of_isPseudoCoherent B S hS hZ X hX hqc hqs K hK (a - m - 1)
  obtain ⟨Q, β, γ, hT⟩ := distinguished_cocone_triangle α
  have : Q.IsLE (a - m - 2) := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    exact CategoryTheory.isZero_homology_obj₃_of_distinguished (a - m - 1) _ hT hiso hepi j
      (by omega)
  exact ⟨P, hP, α, fun M _ i hi =>
    DerivedCategory.bijective_comp_shiftedHom_of_isLE_of_isGE α β γ hT (a - m - 2) M a i
      (by omega)⟩

end AlgebraicGeometry.Space

end
