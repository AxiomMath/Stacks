module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UniformProInverse
public import StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.UniformVanishingConditions
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityI.VanishingEquivalences
public import StacksFrontier.Homology.KFlat.ProjectiveResolution
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived and the naive reductions of a complex are strictly pro-isomorphic

Let `I` be an ideal of a Noetherian ring `A` and let `M` be a bounded complex of finite
`A`-modules, with a bounded above resolution `p : P ⟶ M` by finite flat modules.  The comparison
`P/IⁿP ⟶ M/IⁿM` from the derived reductions of `M` (the system `M ⊗ᴸ A/Iⁿ`) to its degreewise
reductions is a pro-isomorphism by [Stacks, Tag 0G9M].  This file proves that it is a *strict*
pro-isomorphism, as asserted in [Stacks, Tag 0GA5]: there is a single shift `c` such that for
every level `n` the comparison has an inverse from the level `n + c`.

## Main definitions

* `Stacks.AdicSystem.DerivedReductionProIso.reductionComplexSystem`: the inverse system of
  cochain complexes `n ↦ K/I^(n+1)K`.
* `Stacks.AdicSystem.DerivedReductionProIso.reductionComplexSystemMap`: the map of such systems
  induced by a map of complexes.

## Main results

* `Stacks.AdicSystem.DerivedReductionProIso.homologyMap_reductionTransition_eq_zero`: for an
  acyclic complex of finite modules, in every degree the transitions of the reductions over a
  fixed number of steps vanish on cohomology (Artin–Rees).
* `Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_hasUniformInverses`: **the
  comparison of the derived and the naive reductions has uniform inverses.**

## How the statement is proved

We apply `DerivedCategory.hasUniformInverses_whiskerRight_Q`.  Its two substantive inputs are
the two inputs of the source's sketch.  The first is [Stacks, Tag 0GA3]: for `n` large the
transition `A/Iⁿ ⟶ A/I^(n-c)` lifts to projective resolutions by a map vanishing in homological
degrees above the number `t` of generators of `I`; tensoring it with `M`, the transitions of
`M ⊗ᴸ A/Iⁿ` vanish on everything with cohomology below `a - t`, where `M` lives in degrees
`≥ a`.  The second is the Artin–Rees lemma, in the form of [Stacks, Tag 0911]: the cone of
`P/IⁿP ⟶ M/IⁿM` is the reduction of the acyclic complex `cone(p)` of finite modules, and the
transitions of the reductions of an acyclic complex of finite modules vanish on cohomology over a
fixed number of steps.  The remaining work — that finitely many degrees of vanishing on
cohomology together with the vanishing in low degrees give a vanishing composite of transitions
of the cones, and hence uniform inverses — is [Stacks, Tag 08Q2] and is done in
`StacksFrontier.Algebra.Homology.DerivedCategory.UniformProInverse`.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 0G9M](https://stacks.math.columbia.edu/tag/0G9M)
* [Stacks Project, Tag 0GA3](https://stacks.math.columbia.edu/tag/0GA3)
* [Stacks Project, Tag 0911](https://stacks.math.columbia.edu/tag/0911)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite LiftAcyclic CategoryTheory.InverseSequence

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.AdicSystem.DerivedReductionProIso

universe u

variable {A : Type u} [CommRing A]

/-! ### The inverse systems of reductions -/

/-- The inverse system of cochain complexes `n ↦ K/I^(n+1)K`, with the canonical surjections as
transition maps. -/
noncomputable def reductionComplexSystem (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj n := (reduceComplex (I ^ (n.unop + 1))).obj K
  map f := (NatTrans.mapHomologicalComplex (reductionNatTrans
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))) (ComplexShape.up ℤ)).app K
  map_id n := by
    have h : ∀ (J : Ideal A) (hJ : J ≤ J), reductionNatTrans hJ = 𝟙 (redFunctor J) := by
      intro J hJ
      ext M x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule A M)) x
      rfl
    rw [h, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp {a b c} f g := by
    change _ = (NatTrans.mapHomologicalComplex (reductionNatTrans
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))) (ComplexShape.up ℤ) ≫
        NatTrans.mapHomologicalComplex (reductionNatTrans
          (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1)))
            (ComplexShape.up ℤ)).app K
    have h : ∀ {J K L : Ideal A} (hJK : J ≤ K) (hKL : K ≤ L),
        reductionNatTrans hJK ≫ reductionNatTrans hKL = reductionNatTrans (hJK.trans hKL) := by
      intro J K L hJK hKL
      ext M x
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule A M)) x
      rfl
    rw [← NatTrans.mapHomologicalComplex_comp, h]

/-- The map of systems of reductions induced by a map of complexes. -/
noncomputable def reductionComplexSystemMap (I : Ideal A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) :
    reductionComplexSystem I K ⟶ reductionComplexSystem I L where
  app n := (reduceComplex (I ^ (n.unop + 1))).map p
  naturality _ _ f := ((NatTrans.mapHomologicalComplex (reductionNatTrans
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1)))
      (ComplexShape.up ℤ)).naturality p).symm

/-- The localization functor `DerivedCategory.Q` sends the transition map of
`reductionComplexSystem I K` for `n ≤ m` to `adicReductionTransition I K h`. -/
theorem Q_map_reductionComplexSystem_map (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    {n m : ℕ} (h : n ≤ m) :
    DerivedCategory.Q.map (tr (reductionComplexSystem I K) h) = adicReductionTransition I K h :=
  rfl

/-- The localization functor `DerivedCategory.Q` sends the component at `n` of
`reductionComplexSystemMap I p` to `adicReductionComparison I p n`. -/
theorem Q_map_reductionComplexSystemMap_app (I : Ideal A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) (n : ℕ) :
    DerivedCategory.Q.map ((reductionComplexSystemMap I p).app (op n)) =
      adicReductionComparison I p n :=
  rfl

/-! ### Artin–Rees for an acyclic complex -/

/-- A map of short complexes of modules sending every cycle into the boundaries vanishes on
homology. -/
theorem _root_.CategoryTheory.ShortComplex.homologyMap_eq_zero_of_mem_range
    {S T : ShortComplex (ModuleCat.{u} A)} (φ : S ⟶ T)
    (h : ∀ x : S.X₂, S.g x = 0 → φ.τ₂ x ∈ LinearMap.range T.f.hom) :
    ShortComplex.homologyMap φ = 0 := by
  apply (cancel_mono T.homologyι).1
  apply (cancel_epi S.homologyπ).1
  rw [← Category.assoc, S.homologyπ_naturality φ, Category.assoc, T.homology_π_ι]
  apply ModuleCat.hom_ext
  ext x
  have hS : S.g (S.iCycles x) = 0 := by
    have h' := congrArg (fun q : S.cycles ⟶ S.X₃ => q x) S.iCycles_g
    simpa only [ConcreteCategory.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using h'
  have hmem := h (S.iCycles x) hS
  simpa [ModuleCat.hom_comp, ModuleCat.hom_zero] using
    (T.moduleCat_pOpcycles_eq_zero_iff (φ.τ₂ (S.iCycles x))).2 hmem

variable [IsNoetherianRing A]

/-- **Artin–Rees for an acyclic complex.**  Let `C` be a complex of finite modules over a
Noetherian ring which is exact in degree `d`.  There is a `c` such that for every `n` the
transition `C/I^(n+c)C ⟶ C/IⁿC` vanishes on `H^d`. -/
theorem homologyMap_reductionTransition_eq_zero (I : Ideal A)
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (hC : ∀ i, Module.Finite A (C.X i)) (d : ℤ)
    (hd : C.ExactAt d) :
    ∃ c : ℕ, ∀ n m : ℕ, (h : n ≤ m) → n + c ≤ m → HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (reductionNatTrans
        (Ideal.pow_le_pow_right h : I ^ m ≤ I ^ n))
          (ComplexShape.up ℤ)).app C) d = 0 := by
  let d' := (ComplexShape.up ℤ).next d
  let B : Submodule A (C.X d') := LinearMap.range (C.d d d').hom
  have : Module.Finite A (C.X d') := hC d'
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I B
  have hex : LinearMap.ker (C.sc d).g.hom ≤ LinearMap.range (C.sc d).f.hom :=
    (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 ((HomologicalComplex.exactAt_iff C d).1 hd)
  refine ⟨k, fun n m h hm => ?_⟩
  apply ShortComplex.homologyMap_eq_zero_of_mem_range
  intro x hx
  obtain ⟨x₀, rfl⟩ := Submodule.mkQ_surjective _ x
  -- `d x₀ ∈ I^(n+k) C^{d'}`
  have hdx : (C.d d d').hom x₀ ∈ I ^ (n + k) • (⊤ : Submodule A (C.X d')) := by
    have : Submodule.Quotient.mk (p := I ^ m • (⊤ : Submodule A (C.X d')))
        ((C.d d d').hom x₀) = 0 := hx
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hm)
      ((Submodule.Quotient.mk_eq_zero _).1 this)
  have hmem : (C.d d d').hom x₀ ∈ I ^ n • B := by
    have h₁ : (C.d d d').hom x₀ ∈ I ^ (n + k) • (⊤ : Submodule A (C.X d')) ⊓ B :=
      ⟨hdx, ⟨x₀, rfl⟩⟩
    rw [hk (n + k) (by omega), show n + k - k = n by omega] at h₁
    exact Submodule.smul_mono le_rfl inf_le_right h₁
  have hmap : I ^ n • B = (I ^ n • (⊤ : Submodule A (C.X d))).map (C.d d d').hom := by
    rw [Submodule.map_smul'', Submodule.map_top]
  rw [hmap] at hmem
  obtain ⟨y, hy, hxy⟩ := hmem
  have hker : x₀ - y ∈ LinearMap.ker (C.sc d).g.hom := by
    change (C.d d d').hom (x₀ - y) = 0
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := hex hker
  refine ⟨Submodule.Quotient.mk z, ?_⟩
  change Submodule.Quotient.mk (p := I ^ n • (⊤ : Submodule A (C.X d)))
    ((C.sc d).f.hom z) = Submodule.Quotient.mk x₀
  rw [hz]
  refine (Submodule.Quotient.eq (I ^ n • (⊤ : Submodule A (C.X d)))).2 ?_
  simpa using Submodule.neg_mem _ hy

/-! ### Reduction commutes with mapping cones, naturally -/

section ConeNaturality

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] [Preadditive 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  [Preadditive 𝒟]
  [HasBinaryBiproducts 𝒞] [HasBinaryBiproducts 𝒟]

/-- The comparison `H(cone φ) ≅ cone(Hφ)` is natural in the additive functor `H`. -/
theorem mapHomologicalComplexIso_naturality {H H' : 𝒞 ⥤ 𝒟} [H.Additive] [H'.Additive]
    (τ : H ⟶ H') {K L : CochainComplex 𝒞 ℤ} (φ : K ⟶ L) :
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ H).hom ≫
        CochainComplex.mappingCone.map ((H.mapHomologicalComplex _).map φ)
          ((H'.mapHomologicalComplex _).map φ)
          ((NatTrans.mapHomologicalComplex τ _).app K)
          ((NatTrans.mapHomologicalComplex τ _).app L)
          ((NatTrans.mapHomologicalComplex τ _).naturality φ) =
      (NatTrans.mapHomologicalComplex τ _).app (CochainComplex.mappingCone φ) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso φ H').hom := by
  ext n
  dsimp [CochainComplex.mappingCone.mapHomologicalComplexIso]
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq φ H n (n + 1) rfl,
    CochainComplex.mappingCone.mapHomologicalComplexXIso_eq φ H' n (n + 1) rfl,
    CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    CochainComplex.mappingCone.map, Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_desc_f, CochainComplex.mappingCone.inr_f_desc_f,
    Preadditive.comp_add]
  simp only [← Category.assoc]
  simp

end ConeNaturality

/-! ### The cones of the comparison -/

omit [IsNoetherianRing A] in
/-- The mapping cone of a quasi-isomorphism is acyclic. -/
theorem mappingCone_exactAt_of_isIso {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L)
    (hp : IsIso (DerivedCategory.Q.map p)) (d : ℤ) :
    (CochainComplex.mappingCone p).ExactAt d := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished p
  have hz : IsZero (DerivedCategory.Q.obj (CochainComplex.mappingCone p)) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).2 hp
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((DerivedCategory.homologyFunctor _ d).map_isZero hz).of_iso
    ((DerivedCategory.homologyFunctorFactors _ d).app _).symm

omit [IsNoetherianRing A] in
/-- The mapping cone of a map of complexes of finite modules has finite terms. -/
theorem mappingCone_X_finite {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L)
    (hK : ∀ i, Module.Finite A (K.X i)) (hL : ∀ i, Module.Finite A (L.X i)) (i : ℤ) :
    Module.Finite A ((CochainComplex.mappingCone p).X i) := by
  let e := HomologicalComplex.homotopyCofiber.XIsoBiprod p i (i + 1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _
  have : Module.Finite A (K.X (i + 1)) := hK _
  have : Module.Finite A (L.X i) := hL _
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- **Artin–Rees for the cones of the comparison.**  For a quasi-isomorphism `p` between
complexes of finite modules over a Noetherian ring, in every degree `d` the transitions of the
cones of the comparison of reductions vanish on `H^d` over a fixed number of steps. -/
theorem coneTriangleSystem_homology_eq_zero (I : Ideal A)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M)
    (hP : ∀ i, Module.Finite A (P.X i)) (hM : ∀ i, Module.Finite A (M.X i))
    (hp : IsIso (DerivedCategory.Q.map p)) (d : ℤ) :
    ∃ c : ℕ, ∀ n : ℕ, (DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).map
      (tr (DerivedCategory.coneTriangleSystem (𝒜 := ModuleCat.{u} A)
        (reductionComplexSystemMap I p)) (Nat.le_add_right n c)).hom₃ = 0 := by
  have h₁ := mappingCone_X_finite p hP hM
  have h₂ := mappingCone_exactAt_of_isIso p hp d
  obtain ⟨c, hc⟩ := homologyMap_reductionTransition_eq_zero I _ h₁ d h₂
  refine ⟨c, fun n => ?_⟩
  have hle : n + 1 ≤ n + c + 1 := by omega
  let τ := reductionNatTrans (Ideal.pow_le_pow_right hle : I ^ (n + c + 1) ≤ I ^ (n + 1))
  have hnat := mapHomologicalComplexIso_naturality (𝒞 := ModuleCat.{u} A) (𝒟 := ModuleCat.{u} A) τ p
  have hmap : (tr (DerivedCategory.coneTriangleSystem (𝒜 := ModuleCat.{u} A)
      (reductionComplexSystemMap I p)) (Nat.le_add_right n c)).hom₃ =
      DerivedCategory.Q.map ((CochainComplex.mappingCone.mapHomologicalComplexIso p
        (redFunctor (I ^ (n + c + 1)))).inv ≫
          (NatTrans.mapHomologicalComplex τ _).app (CochainComplex.mappingCone p) ≫
          (CochainComplex.mappingCone.mapHomologicalComplexIso p
            (redFunctor (I ^ (n + 1)))).hom) := by
    rw [← hnat, Iso.inv_hom_id_assoc]
    rfl
  rw [hmap]
  apply DerivedCategory.homologyFunctor_map_Q_map_eq_zero
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    hc (n + 1) (n + c + 1) hle (by omega), zero_comp, comp_zero]

/-! ### Bounds -/

omit [IsNoetherianRing A] in
/-- The reduction modulo `J` of a complex strictly concentrated in degrees `≥ a` is strictly
concentrated in degrees `≥ a`. -/
theorem reduceComplex_isStrictlyGE (J : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ)
    [K.IsStrictlyGE a] : ((reduceComplex J).obj K).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (redFunctor J).map_isZero (K.isZero_of_isStrictlyGE a i hi)

omit [IsNoetherianRing A] in
/-- The reduction modulo `J` of a complex strictly concentrated in degrees `≤ b` is strictly
concentrated in degrees `≤ b`. -/
theorem reduceComplex_isStrictlyLE (J : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : ((reduceComplex J).obj K).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (redFunctor J).map_isZero (K.isZero_of_isStrictlyLE b i hi)

/-! ### The low degrees: transitions of the derived reductions factor through a truncation -/

omit [IsNoetherianRing A] in
/-- A map of resolutions vanishing in homological degrees above `t`, tensored with a complex
without terms below `a`, vanishes in the degrees `≤ a - t - 1`. -/
theorem trightCochain_map_f_eq_zero {F F' : CochainComplex (ModuleCat.{u} A) ℤ} (l : F ⟶ F')
    (t : ℕ) (hl : ∀ i : ℕ, t < i → l.f (-(i : ℤ)) = 0) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ℤ) [M.IsStrictlyGE a] (i : ℤ) (hi : i ≤ a - t - 1) :
    ((TrightCochain M).map l).f i = 0 := by
  change (HomologicalComplex.mapBifunctorMap l (𝟙 M) (MonoidalCategory.curriedTensor _)
    (ComplexShape.up ℤ)).f i = 0
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = i at hpq
  rw [HomologicalComplex.ι_mapBifunctorMap, comp_zero]
  by_cases hq : q < a
  · have hz : IsZero (MonoidalCategory.tensorObj (F.X p) (M.X q)) :=
      (MonoidalCategory.tensorLeft (F.X p)).map_isZero (M.isZero_of_isStrictlyGE a q hq)
    exact hz.eq_of_src _ _
  · have hp : l.f p = 0 := by
      have h := hl (-p).toNat (by omega)
      rwa [show (-(((-p).toNat : ℕ) : ℤ)) = p by omega] at h
    simp [hp]

omit [IsNoetherianRing A] in
/-- The lift of a transition `A/J ⟶ A/J'` provided by [Stacks, Tag 0GA3] is a property of the
ideals only, so it can be transported along an equality of exponents. -/
theorem hasLiftVanishingAbove_congr (I : Ideal A) (m k₁ k₂ t : ℕ) (e : k₁ = k₂)
    (h₁ : I ^ m ≤ I ^ k₁) (h₂ : I ^ m ≤ I ^ k₂)
    (h : HasLiftVanishingAbove (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ m))).π'
      (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ k₁))).π'
      (ModuleCat.ofHom (Submodule.factor h₁)) t) :
    HasLiftVanishingAbove (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ m))).π'
      (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ k₂))).π'
      (ModuleCat.ofHom (Submodule.factor h₂)) t := by
  subst e
  exact h

omit [IsNoetherianRing A] in
/-- **The transitions of the derived reductions kill the low degrees.**  If the transition
`A/I^k ⟶ A/I^k'` lifts to the projective resolutions by a map vanishing in homological degrees
above `t`, then the transition `P/I^kP ⟶ P/I^k'P` of the derived reductions of `M` kills every
map out of an object of `D(A)` without cohomology above `a - t - 1`, where `M` has no terms below
`a`. -/
theorem comp_Q_map_reductionTransition_eq_zero (I : Ideal A)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (hP : P.KFlat)
    (hp : IsIso (DerivedCategory.Q.map p)) (a : ℤ) [M.IsStrictlyGE a] (t : ℕ) {k k' : ℕ}
    (hk : k' ≤ k)
    (hlift : HasLiftVanishingAbove (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ k))).π'
      (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ k'))).π'
      (ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right hk : I ^ k ≤ I ^ k'))) t)
    (W : DerivedCategory (ModuleCat.{u} A)) (hW : W.IsLE (a - t - 1))
    (g : W ⟶ DerivedCategory.Q.obj ((reduceComplex (I ^ k)).obj P)) :
    g ≫ DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (reductionNatTrans (Ideal.pow_le_pow_right hk)) (ComplexShape.up ℤ)).app P) = 0 := by
  let R := ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ k))
  let R' := ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ k'))
  obtain ⟨l, hl, hz⟩ := hlift
  have : QuasiIso p := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).1 hp
  have : CochainComplex.IsProjectiveResolution R.π' := isProjectiveResolution_π' R
  have : CochainComplex.IsProjectiveResolution R'.π' := isProjectiveResolution_π' R'
  have hF : R.cochainComplex.KFlat := CochainComplex.KFlat.kFlat_projectiveResolution R
  have hF' : R'.cochainComplex.KFlat := CochainComplex.KFlat.kFlat_projectiveResolution R'
  let u := (TrightCochain P).map R.π'
  let u' := (TrightCochain P).map R'.π'
  let v : (TrightCochain P).obj R.cochainComplex ⟶ (TrightCochain M).obj R.cochainComplex :=
    (TleftCochain R.cochainComplex).map p
  let v' : (TrightCochain P).obj R'.cochainComplex ⟶ (TrightCochain M).obj R'.cochainComplex :=
    (TleftCochain R'.cochainComplex).map p
  have : QuasiIso u := CochainComplex.DerivedTensor.quasiIso_tright_map P hP R.π'
  have : QuasiIso v' :=
    CochainComplex.DerivedTensor.quasiIso_tleft_map_of_kFlat R'.cochainComplex hF' p
  have hu : IsIso (DerivedCategory.Q.map u) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ u).2 ‹_›
  have hv' : IsIso (DerivedCategory.Q.map v') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ v').2 ‹QuasiIso v'›
  -- the three commutative squares
  have S1 : u ≫ (TrightCochain P).map ((CochainComplex.singleFunctor _ 0).map
      (quotientModuleMap (Ideal.pow_le_pow_right hk : I ^ k ≤ I ^ k'))) =
      (TrightCochain P).map l ≫ u' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ hl.symm
  have S3 : (TrightCochain P).map l ≫ v' = v ≫ (TrightCochain M).map l :=
    (((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.map l).naturality
      p).symm
  let iso : (TrightCochain P).obj ((CochainComplex.singleFunctor _ 0).obj
      (ModuleCat.of A (A ⧸ I ^ k))) ≅ (reduceComplex (I ^ k)).obj P :=
    singleQuotientTensorIsoReduction (I ^ k) P
  let iso' : (TrightCochain P).obj ((CochainComplex.singleFunctor _ 0).obj
      (ModuleCat.of A (A ⧸ I ^ k'))) ≅ (reduceComplex (I ^ k')).obj P :=
    singleQuotientTensorIsoReduction (I ^ k') P
  let τ : (reduceComplex (I ^ k)).obj P ⟶ (reduceComplex (I ^ k')).obj P :=
    (NatTrans.mapHomologicalComplex (reductionNatTrans
      (Ideal.pow_le_pow_right hk : I ^ k ≤ I ^ k')) (ComplexShape.up ℤ)).app P
  have S2 : (TrightCochain P).map ((CochainComplex.singleFunctor _ 0).map
      (quotientModuleMap (Ideal.pow_le_pow_right hk : I ^ k ≤ I ^ k'))) ≫ iso'.hom =
      iso.hom ≫ τ :=
    singleQuotientTensorIsoReduction_naturality (Ideal.pow_le_pow_right hk : I ^ k ≤ I ^ k') P
  have E₀ : (u ≫ iso.hom) ≫ τ = (TrightCochain P).map l ≫ (u' ≫ iso'.hom) := by
    rw [Category.assoc, ← S2, ← Category.assoc, S1, Category.assoc]
  have : IsIso (DerivedCategory.Q.map (u ≫ iso.hom)) := by
    rw [Functor.map_comp]
    infer_instance
  let g₂ := g ≫ inv (DerivedCategory.Q.map (u ≫ iso.hom))
  have hg : g = g₂ ≫ DerivedCategory.Q.map (u ≫ iso.hom) := by simp [g₂]
  have h₁ : g₂ ≫ DerivedCategory.Q.map ((TrightCochain P).map l) = 0 := by
    refine (cancel_mono (DerivedCategory.Q.map v')).1 ?_
    rw [zero_comp, Category.assoc, ← Functor.map_comp, S3, Functor.map_comp, ← Category.assoc]
    exact DerivedCategory.comp_Q_map_eq_zero_of_f_eq_zero _ (a - t - 1)
      (fun i hi => trightCochain_map_f_eq_zero l t hz M a i hi) W hW _
  change g ≫ DerivedCategory.Q.map τ = 0
  rw [hg, Category.assoc, ← Functor.map_comp, E₀, Functor.map_comp, ← Category.assoc, h₁,
    zero_comp]

omit [IsNoetherianRing A] in
/-- **The transitions of the derived reductions kill the low degrees, uniformly.**  For a
Noetherian ring there are `t` and `c₀` such that every transition of the derived reductions of
`M` over at least `c₀` steps kills every map out of an object without cohomology above
`a - t - 1`. -/
theorem exists_tail_reductionComplexSystem [IsNoetherianRing A] (I : Ideal A)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (hP : P.KFlat)
    (hp : IsIso (DerivedCategory.Q.map p)) (a : ℤ) [M.IsStrictlyGE a] :
    ∃ t c₀ : ℕ, ∀ n m : ℕ, (h : n ≤ m) → n + c₀ ≤ m → ∀ (W : DerivedCategory (ModuleCat.{u} A)),
      W.IsLE (a - t - 1) → ∀ g : W ⟶ DerivedCategory.Q.obj ((reductionComplexSystem I P).obj
        (op m)), g ≫ DerivedCategory.Q.map (tr (reductionComplexSystem I P) h) = 0 := by
  obtain ⟨t, gens, hgens⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨N, c, hNc⟩ :=
    Stacks.LocalCohomology.UniformityII.exists_uniform_hasLiftVanishingAbove_quotientFactor
      gens hgens.symm
  refine ⟨t, N + c, fun n m h hm W hW g => ?_⟩
  have hlm : m - c ≤ m := Nat.sub_le m c
  have hl : n ≤ m - c := by omega
  have hsplit : tr (reductionComplexSystem I P) h =
      tr (reductionComplexSystem I P) hlm ≫ tr (reductionComplexSystem I P) hl :=
    (tr_comp _ _ _).symm
  have := isProjectiveResolution_π' (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ (m + 1))))
  have := isProjectiveResolution_π'
    (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ (m + 1 - c))))
  have hlift := hasLiftVanishingAbove_congr I (m + 1) (m + 1 - c) (m - c + 1) t (by omega) _
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hlm 1))
    (hNc (m + 1) (by omega) (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ (m + 1)))).π'
      (ProjectiveResolution.of (ModuleCat.of A (A ⧸ I ^ (m + 1 - c)))).π')
  have hkey := comp_Q_map_reductionTransition_eq_zero I p hP hp a t
    (Nat.add_le_add_right hlm 1) hlift W hW g
  rw [hsplit, Functor.map_comp, ← Category.assoc]
  change g ≫ _ = 0 at hkey
  rw [show g ≫ DerivedCategory.Q.map (tr (reductionComplexSystem I P) hlm) = 0 from hkey,
    zero_comp]

/-! ### The main theorem -/

omit [IsNoetherianRing A] in
/-- **[Stacks, Tag 0GA5]: the derived reductions of a bounded complex of finite modules are
strictly pro-isomorphic to its naive reductions.**  Let `I` be an ideal of a Noetherian ring
`A`, let `M` be a bounded complex of finite `A`-modules and let `p : P ⟶ M` be a
quasi-isomorphism from a bounded above complex of finite flat modules.  Then the comparison
`P/I^(n+1)P ⟶ M/I^(n+1)M` from the system `M ⊗ᴸ A/Iⁿ` to the system `M/IⁿM` has uniform inverses
in `D(A)`: there is a single shift `c` with inverses `M/I^mM ⟶ P/IⁿP` for all `m ≥ n + c`. -/
theorem derivedReduction_hasUniformInverses [IsNoetherianRing A] (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i))
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (hPbounded : ∃ b : ℤ, P.IsStrictlyLE b)
    (hPfinite : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Flat A (P.X i))
    (hp : IsIso (DerivedCategory.Q.map p)) :
    HasUniformInverses
      (Functor.whiskerRight (reductionComplexSystemMap I p) DerivedCategory.Q) := by
  obtain ⟨a, b, hMa, hMb⟩ := hMbounded
  obtain ⟨b', hPb⟩ := hPbounded
  have : ∀ i, Module.Flat A (P.X i) := fun i => (hPfinite i).2
  have hP : P.KFlat := CochainComplex.KFlat.kFlat_of_flat P b'
  obtain ⟨t, c₀, htail⟩ := exists_tail_reductionComplexSystem I p hP hp a
  have hMb' : M.IsStrictlyLE (max b b') := M.isStrictlyLE_of_le b (max b b') (le_max_left _ _)
  have hPb' : P.IsStrictlyLE (max b b') := P.isStrictlyLE_of_le b' (max b b') (le_max_right _ _)
  have hLE : ∀ (K : CochainComplex (ModuleCat.{u} A) ℤ), K.IsStrictlyLE (max b b') →
      ∀ n : ℕ, (DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj K)).IsLE (max b b') :=
    fun K _ n => by
      have := reduceComplex_isStrictlyLE (I ^ (n + 1)) K (max b b')
      infer_instance
  refine DerivedCategory.hasUniformInverses_whiskerRight_Q (reductionComplexSystemMap I p)
    a (max b b') (a - t - 1) (by omega) (fun n => ?_) (fun n => hLE M hMb' n.unop)
    (fun n => hLE P hPb' n.unop)
    ⟨c₀, htail⟩ (coneTriangleSystem_homology_eq_zero I p (fun i => (hPfinite i).1) hMfinite hp)
  have := reduceComplex_isStrictlyGE (I ^ (n.unop + 1)) M a
  change (DerivedCategory.Q.obj ((reduceComplex (I ^ (n.unop + 1))).obj M)).IsGE a
  infer_instance

omit [IsNoetherianRing A] in
/-- **[Stacks, Tag 0GA5], explicitly.**  In the situation of
`derivedReduction_hasUniformInverses`, there is a shift `c` such that for all `n + c ≤ m` the
comparison maps `adicReductionComparison` acquire an inverse from level `m` to level `n` whose
two round trips are the transition maps. -/
@[stacks 0GA5 "the natural map from (2) to (1) is a strict pro-isomorphism: inverses over a \
uniform shift"]
theorem derivedReduction_exists_uniform_inverse [IsNoetherianRing A] (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i))
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (hPbounded : ∃ b : ℤ, P.IsStrictlyLE b)
    (hPfinite : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Flat A (P.X i))
    (hp : IsIso (DerivedCategory.Q.map p)) :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      ∃ (h : n ≤ m) (s : DerivedCategory.Q.obj ((reduceComplex (I ^ (m + 1))).obj M) ⟶
          DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj P)),
        adicReductionComparison I p m ≫ s = adicReductionTransition I P h ∧
          s ≫ adicReductionComparison I p n = adicReductionTransition I M h := by
  obtain ⟨c, hc⟩ :=
    derivedReduction_hasUniformInverses I M hMbounded hMfinite p hPbounded hPfinite hp
  refine ⟨c, fun n m hm => ?_⟩
  obtain ⟨s, h, hs₁, hs₂⟩ := hc n m hm
  exact ⟨h, s, hs₁, hs₂⟩

end Stacks.AdicSystem.DerivedReductionProIso

end
