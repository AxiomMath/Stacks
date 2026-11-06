module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArtinSchreierScaledLineCharacter
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFirstProjectionFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportGeometricVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineConstantCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalkLinear
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevels

/-!
# Vanishing of `H¹_c` on the geometric fibres of the first projection of Laumon's plane

Let `k'` be a finite field with `q` elements, `Ω` a field over `k'`, `p` a prime with `p ∤ q`, and
`𝔸¹_Ω = Spec Ω[t] → Spec Ω` the structure morphism `f'`. For a finite `ℤ/p`-module `M` with a
continuous action of `π₁(𝔸¹_Ω, ȳ)` and its lisse sheaf `ℱ_M`:

* if `π₁` acts through the character of the Artin–Schreier cover of `a t`, `a ≠ 0`, by an action
  `ρ` of `k'` without invariants (`∑_c ρ(c) = 0`), then all `Hⁱ(Rf'_! ℱ_M)` vanish
  (`isZero_homology_derivedLowerShriek_lisseEtaleSheaf_scaledLine`): the coordinate `t ↦ a t`
  presents `𝔸¹_Ω` as the base change of `𝔸¹_{k'}` to `Ω`, `ℱ_M` is the inverse image of the lisse
  sheaf on `𝔸¹_{k'}` of `M` with `π₁(𝔸¹_{k'})` acting through the Artin–Schreier character of `t`
  (Tag 0DV6 and the base change of Artin–Schreier characters), whose `Rf_!` vanishes by the
  counting argument over `ℤ/p`
  (`Stacks.ArtinSchreier.subsingleton_compactSupportSheafCohomology_affineLine_torsor_character`),
  and proper base change (Tag 0F7L);
* if `π₁` acts trivially, `Hⁱ(Rf'_! ℱ_M) = 0` for `i ≠ 2`
  (`isZero_homology_derivedLowerShriek_lisseEtaleSheaf_affineLine_of_trivial`).

For a continuous `τ : π₁(𝔸¹_Ω, ȳ) → GL_r(ℤ_ℓ)` whose rational matrices are `N(χ)` for the
character `χ` of the Artin–Schreier cover of `a t` and a multiplicative `N : k' → M_r(ℚ_ℓ)` with
`∑_c N(c) = 0`, this gives `H¹(Rf'_! ℱ_{τ mod ℓ}) = 0`
(`isZero_homology_one_derivedLowerShriek_levelModule_scaledLine`): for `a = 0` the action is
trivial; for `a ≠ 0` the character is surjective, so every `N(c)` is the integral matrix of some
`τ(γ)`, and `∑_c N(c) = 0` says that `k'` acts on `(ℤ/ℓ)^r` without invariants. This is the
vanishing of `R¹pr₁!` of the bottom level of the flat model of Laumon's family sheaf on the
geometric fibre over `x̄`, `a = h(x̄)` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `characterFactorContinuousModule`: a finite `R`-module on which `G` acts through a character
  `χ : G → K` and an action of `K`, as a finite continuous `R`-module.

## Main results

* `isZero_homology_derivedLowerShriek_inverseImage_of_isPullback_affineLine`: the vanishing of
  `Hⁱ(Rf_! G₀)` on `𝔸¹_k` implies that of `Hⁱ(R pr_!(T⁻¹ G₀))` on a base change of `𝔸¹_k`.
* `isZero_homology_derivedLowerShriek_lisseEtaleSheaf_scaledLine`: `Rf'_! ℱ_M = 0` when `π₁` acts
  through the Artin–Schreier character of `a t`, `a ≠ 0`, by an action without invariants.
* `isZero_homology_derivedLowerShriek_lisseEtaleSheaf_affineLine_of_trivial`: `Hⁱ(Rf'_! ℱ_M) = 0`
  for `i ≠ 2` when `π₁` acts trivially on `M`.
* `isZero_homology_one_derivedLowerShriek_levelModule_scaledLine`: `H¹(Rf'_! ℱ_{τ mod ℓ}) = 0`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.ArtinSchreier
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u v w

attribute [local instance] discreteForget₂AddCommGrpCat
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

namespace Stacks.EtaleCohomology

/-! ### Modules on which a group acts through a character -/

section Modules

open scoped Stacks.DiscreteModuleTopology

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Type*}
  [AddCommGroup K] (R : Type) [CommRing R] (W : Type (u + 1)) [AddCommGroup W] [Module R W]
  [Module.Finite R W] (χ : G →* Multiplicative K)
  (hχ : ∀ S : Set (Multiplicative K), IsOpen (χ ⁻¹' S))
  (ρK : Multiplicative K →* Module.End R W)

/-- **A finite `R`-module `W` on which `G` acts through a character `χ : G → K`** and an action
`ρ` of `K`, as a finite continuous `R`-module, `χ` having open fibres. -/
def characterFactorContinuousModule : FiniteTypeContinuousModule.{0, u + 1, u + 1} R G :=
  ⟨ofRepresentation (R := R) (M := W) (ρK.comp χ)
      ((isContinuous_actionOfRepresentation_iff _).2 fun v => hχ {c | ρK c v = v}),
    (ModuleCat.isFG_iff _).2 (show Module.Finite R W from inferInstance)⟩

/-- The action of `g : G` on `characterFactorContinuousModule R W χ hχ ρK` is `ρK (χ g)`. -/
theorem characterFactorContinuousModule_ρ_hom (g : G) (v : W) :
    ((characterFactorContinuousModule R W χ hχ ρK).obj.obj.obj.ρ g).asHom.hom v = ρK (χ g) v :=
  rfl

end Modules

/-! ### The lifted level representations -/

section LevelRepresentation

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (τ : G →* GL (Fin r) ℤ_[ℓ])

omit [IsTopologicalGroup G] in
/-- The lifted level representation of `g` depends only on `τ g`. -/
theorem levelULiftRepresentation_eq_of_eq (k : ℕ) {g g' : G} (h : τ g = τ g') :
    levelULiftRepresentation.{v, w} τ k g = levelULiftRepresentation.{v, w} τ k g' := by
  refine LinearMap.ext fun x => ULift.ext ?_
  change levelRepresentation τ k g x.down = levelRepresentation τ k g' x.down
  rw [levelRepresentation_apply, levelRepresentation_apply, h]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If the matrices `τ (g c)` sum to zero, so do the vectors
`levelULiftRepresentation τ k (g c) x`. -/
theorem sum_levelULiftRepresentation_apply_eq_zero {ι : Type*} (s : Finset ι) (g : ι → G)
    (h : ∑ c ∈ s, (τ (g c)).val = 0) (k : ℕ) (x : ULift.{w} (Fin r → ZMod (ℓ ^ k))) :
    ∑ c ∈ s, levelULiftRepresentation.{v, w} τ k (g c) x = 0 := by
  let Φ : Matrix (Fin r) (Fin r) ℤ_[ℓ] →+ (Fin r → ZMod (ℓ ^ k)) :=
    (Matrix.mulVec.addMonoidHomLeft x.down).comp
      (PadicInt.toZModPow (p := ℓ) k).mapMatrix.toAddMonoidHom
  have hΦ := congrArg Φ h
  rw [map_sum, map_zero] at hΦ
  apply (AddEquiv.ulift : ULift.{w} (Fin r → ZMod (ℓ ^ k)) ≃+ _).injective
  rwa [map_sum, map_zero]

end LevelRepresentation

/-! ### Proper base change from the affine line over the finite field -/

section BaseChange

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]

omit [Fintype k] in
/-- **`Hⁱ(R pr_!(T⁻¹ G₀)) = 0` on a base change `P = 𝔸¹_k ×_k W` as soon as
`Hⁱ(Rf_! G₀) = 0` on `𝔸¹_k`**, with any compactifications: proper base change (Tag 0F7L) and the
exactness of inverse image. -/
theorem isZero_homology_derivedLowerShriek_inverseImage_of_isPullback_affineLine
    (j₀ : CompactificationOf (Over.mk (affineLineStructureMap k))) {W P : Scheme.{u}}
    [CompactSpace W] [QuasiSeparatedSpace W] (πW : W ⟶ Spec (.of k))
    {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr (affineLineStructureMap k) πW) (j : CompactificationOf (Over.mk pr))
    (G₀ : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (i : ℤ)
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} (affineLineStructureMap k) j₀ Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G₀)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} pr j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ T).obj G₀)))) := by
  have : LocallyOfFiniteType (affineLineStructureMap k) := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFiniteType pr :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : IsSeparated pr := MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact pr := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let K₀ := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ
    (Spec (.of (Polynomial k)))) 0).obj G₀
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j₀ K₀ (isTorsionPlus_of_finite Λ _ K₀)
  let eK : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ T).obj K₀ ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((etaleModuleInverseImage.{u, 0} Λ T).obj G₀) :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (etaleModuleInverseImage.{u, 0} Λ T)
      0).app G₀
  let c := (derivedLowerShriekCompactificationIso pr (j₀.baseChange sq) j Λ).app
    ⟨_, isTorsionPlus_of_finite Λ P
      ((DerivedCategory.Plus.singleFunctor _ 0).obj ((etaleModuleInverseImage.{u, 0} Λ T).obj G₀))⟩
  let E : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ πW).obj
        ((derivedLowerShriek.{u, 0} (affineLineStructureMap k) j₀ Λ).obj K₀) ≅
      (derivedLowerShriek.{u, 0} pr j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} Λ T).obj G₀)) :=
    asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j₀).app K₀) ≪≫
      (derivedLowerShriek.{u, 0} pr (j₀.baseChange sq) Λ).mapIso eK ≪≫ c
  have := (etaleModuleInverseImageAdj.{u, 0} Λ πW).isLeftAdjoint
  have : (etaleModuleInverseImage.{u, 0} Λ πW).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact (Functor.map_isZero (etaleModuleInverseImage.{u, 0} Λ πW) h).of_iso
    ((DerivedCategory.Plus.homologyFunctor _ i).mapIso E.symm ≪≫
      (etaleModuleInverseImageHomologyIso Λ πW _ i).symm)

/-- Vanishing of `Hⁱ(R pr_! G)` for a sheaf `G ≅ T⁻¹ G₀` on a base change of `𝔸¹_k`, from that of
`Hⁱ(Rf_! G₀)`. -/
private theorem isZero_homology_derivedLowerShriek_of_iso_inverseImage_affineLine
    (k : Type u) [Field k] (Λ : Type) [CommRing Λ] [Finite Λ]
    (j₀ : CompactificationOf (Over.mk (affineLineStructureMap k))) {W P : Scheme.{u}}
    [CompactSpace W] [QuasiSeparatedSpace W] (πW : W ⟶ Spec (.of k))
    {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr (affineLineStructureMap k) πW) (j : CompactificationOf (Over.mk pr))
    (G₀ : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (G : EtaleModules.{u, 0} Λ P)
    (e : G ≅ (etaleModuleInverseImage.{u, 0} Λ T).obj G₀) (i : ℤ)
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} (affineLineStructureMap k) j₀ Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G₀)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} pr j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
  (isZero_homology_derivedLowerShriek_inverseImage_of_isPullback_affineLine k Λ j₀ πW sq j G₀ i
    h).of_iso ((DerivedCategory.Plus.homologyFunctor _ i).mapIso
      ((derivedLowerShriek.{u, 0} _ j Λ).mapIso
        ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e)))

end BaseChange

/-! ### The geometric fibres -/

section Fibre

attribute [local instance] HasDerivedCategory.standard

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u}) {Ω : Type u} [Field Ω]
  [Algebra k' Ω] (hP : schemeSizeBelow B.cutoff (Spec (.of (Polynomial Ω))))

/-- **`Rf'_! ℱ_M = 0` on `𝔸¹_Ω` when `π₁` acts through the Artin–Schreier character of `a t`,
`a ≠ 0`, by an action of `k'` without invariants**, `p ∤ q`, for any compactification of
`f' : 𝔸¹_Ω → Spec Ω`. -/
theorem isZero_homology_derivedLowerShriek_lisseEtaleSheaf_scaledLine (p : ℕ) [Fact p.Prime]
    (hp : IsUnit (Fintype.card k' : ZMod p)) (a : Ω) (ha : a ≠ 0)
    (y : GeometricPoint (Spec (.of (Polynomial Ω))))
    (q : (finiteEtaleFiberFunctor y).obj (cover k' (Polynomial Ω) (C a * Polynomial.X)))
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod p)
      (EtaleFundamentalGroup (Spec (.of (Polynomial Ω))) y))
    (ρK : Multiplicative k' →* Module.End (ZMod p) M.obj.obj.obj.V)
    (hM : ∀ σ v, (M.obj.obj.obj.ρ σ).asHom.hom v =
      ρK ((torsorCover k' (Polynomial Ω) (C a * Polynomial.X)).character y q σ) v)
    (hfix : ∀ v, ∑ c : k', ρK (Multiplicative.ofAdd c) v = 0)
    (j : CompactificationOf (Over.mk (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω)))))
    (i : ℤ) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω))) j
        (ZMod p)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((lisseEtaleSheaf B (specObject (Polynomial Ω) B hP) y (ZMod p)).obj M)))) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Module.Finite (ZMod p) M.obj.obj.obj.V := M.property
  have : LocallyOfFiniteType (affineLineStructureMap k') := locallyOfFiniteType_specPolynomial k'
  let ι := algebraMap k' Ω
  let φT : Polynomial k' →ₐ[k'] Polynomial Ω := Polynomial.aeval (C a * Polynomial.X)
  generalize hg : (C a * Polynomial.X : Polynomial Ω) = g' at q hM
  obtain rfl : φT Polynomial.X = g' := (aeval_X _).trans hg
  let T : Spec (.of (Polynomial Ω)) ⟶ Spec (.of (Polynomial k')) :=
    Spec.map (CommRingCat.ofHom φT.toRingHom)
  have hT : T = Spec.map (CommRingCat.ofHom (eval₂RingHom ((C : Ω →+* Polynomial Ω).comp ι)
      (C a * Polynomial.X))) := by
    change Spec.map _ = Spec.map _
    congr 2
  have sq : IsPullback T (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω)))
      (affineLineStructureMap k') (Spec.map (CommRingCat.ofHom ι)) := by
    rw [hT]
    exact isPullback_specMap_scaledCoordinate k' ι a ha
  let 𝔸 := specObject (Polynomial k') B (schemeSizeBelow_spec_polynomial k' B)
  let Tb : specObject (Polynomial Ω) B hP ⟶ 𝔸 := ObjectProperty.homMk T
  let q₀ : (finiteEtaleFiberFunctor (y.map T)).obj (cover k' (Polynomial k') Polynomial.X) :=
    finiteEtaleFiberProjection T y (cover k' (Polynomial k') Polynomial.X)
      ((finiteEtaleFiberFunctor y).map (coverBaseChangeHom k' Polynomial.X φT) q)
  let χ₀ := (torsorCover k' (Polynomial k') Polynomial.X).character (y.map T) q₀
  have hχ₀ : ∀ S : Set (Multiplicative k'), IsOpen (χ₀ ⁻¹' S) := by
    let : TopologicalSpace (Multiplicative k') := ⊥
    have : DiscreteTopology (Multiplicative k') := ⟨rfl⟩
    exact fun S => (isOpen_discrete S).preimage
      ((torsorCover k' (Polynomial k') Polynomial.X).continuous_character _ q₀)
  let M₀ := characterFactorContinuousModule (ZMod p) M.obj.obj.obj.V χ₀ hχ₀ ρK
  let eM : M ≅
      (finiteTypeContinuousModuleRes (ZMod p) (etaleFundamentalGroupMap Tb.hom y)).obj M₀ :=
    finiteTypeContinuousModuleIsoOfLinearEquiv (ZMod p) (LinearEquiv.refl _ _) fun σ v => by
      change (M.obj.obj.obj.ρ σ).asHom.hom v = ρK (χ₀ (etaleFundamentalGroupMap T y σ)) v
      rw [hM]
      exact congrArg (fun c => ρK c v) (torsorCover_character_map k' Polynomial.X φT y q σ)
  obtain ⟨e₂⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso B Tb y (ZMod p) M₀
  let G₀ := (lisseEtaleSheaf B 𝔸 (y.map T) (ZMod p)).obj M₀
  obtain ⟨j₀, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace
    (affineLineStructureMap k')
  have h0 : IsZero ((derivedLowerShriek.{u, 0} (affineLineStructureMap k') j₀ (ZMod p)).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G₀)) :=
    isZero_derivedLowerShriek_single_of_forall_subsingleton (ZMod p) (affineLineStructureMap k') j₀
      G₀ (fun i => subsingleton_compactSupportSheafCohomology_affineLine_torsor_character k' B p hp
        j₀ (y.map T) q₀ M₀ ρK (fun σ v => rfl) hfix i)
  exact isZero_homology_derivedLowerShriek_of_iso_inverseImage_affineLine k' (ZMod p) j₀
    (Spec.map (CommRingCat.ofHom ι)) sq j G₀ _
    ((lisseEtaleSheaf B (specObject (Polynomial Ω) B hP) y (ZMod p)).mapIso eM ≪≫ e₂.symm) i
    (Functor.map_isZero _ h0)

/-- **`Hⁱ(Rf'_! ℱ_M) = 0` for `i ≠ 2` on `𝔸¹_Ω` when `π₁` acts trivially on `M`**, `p ∤ q`:
`ℱ_M` is constant, the inverse image of a constant sheaf on `𝔸¹_{k'}` along the base change
`𝔸¹_Ω → 𝔸¹_{k'}`. -/
theorem isZero_homology_derivedLowerShriek_lisseEtaleSheaf_affineLine_of_trivial (p : ℕ)
    [Fact p.Prime] (hp : IsUnit (Fintype.card k' : ZMod p))
    (y : GeometricPoint (Spec (.of (Polynomial Ω))))
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod p)
      (EtaleFundamentalGroup (Spec (.of (Polynomial Ω))) y))
    (hM : ∀ σ, M.obj.obj.obj.ρ σ = 1)
    (j : CompactificationOf (Over.mk (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω)))))
    (i : ℤ) (hi : i ≠ 2) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω))) j
        (ZMod p)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((lisseEtaleSheaf B (specObject (Polynomial Ω) B hP) y (ZMod p)).obj M)))) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have : Module.Finite (ZMod p) M.obj.obj.obj.V := M.property
  have : Finite M.obj.obj.obj.V := Module.finite_of_finite (ZMod p)
  let ι := algebraMap k' Ω
  have sq := isPullback_specMap_scaledCoordinate k' ι (1 : Ω) one_ne_zero
  obtain ⟨j₀, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace
    (affineLineStructureMap k')
  have h0 := isZero_homology_derivedLowerShriek_constantSheaf_affineLine k' (ZMod p) hp j₀
    M.obj.obj.obj.V i hi
  obtain ⟨e⟩ := nonempty_lisseEtaleSheaf_iso_constantSheaf_of_trivial B
    (specObject (Polynomial Ω) B hP) y (ZMod p) M hM
  exact isZero_homology_derivedLowerShriek_of_iso_inverseImage_affineLine k' (ZMod p) j₀
    (Spec.map (CommRingCat.ofHom ι)) sq j _ _
    (e ≪≫ ((etaleModuleInverseImageConstantIso (ZMod p) _).app M.obj.obj.obj.V).symm) i h0

/-- **`H¹(Rf'_! ℱ_{τ mod ℓ}) = 0` on `𝔸¹_Ω`** for a continuous `τ : π₁(𝔸¹_Ω, ȳ) → GL_r(ℤ_ℓ)` whose
rational matrices are `N(χ)`, `χ` the character of the Artin–Schreier cover of `a t` and
`N : k' → M_r(ℚ_ℓ)` with `N(0) = 1` and `∑_c N(c) = 0`, `ℓ ∤ q`: for `a = 0` the character is
trivial, so `π₁` acts trivially on `(ℤ/ℓ)^r`; for `a ≠ 0` the character is surjective, so
`π₁` acts through an action of `k'` by the reductions of the integral matrices `N(c)`, without
invariants since `∑_c N(c) = 0`. -/
theorem isZero_homology_one_derivedLowerShriek_levelModule_scaledLine {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (Fintype.card k' : ZMod (ℓ ^ (0 + 1)))) {r : ℕ}
    (y : GeometricPoint (Spec (.of (Polynomial Ω)))) (a : Ω)
    (q : (finiteEtaleFiberFunctor y).obj (cover k' (Polynomial Ω) (C a * Polynomial.X)))
    (τ : EtaleFundamentalGroup (Spec (.of (Polynomial Ω))) y →* GL (Fin r) ℤ_[ℓ])
    (hτ : Continuous τ) (N : k' → Matrix (Fin r) (Fin r) ℚ_[ℓ])
    (hτN : ∀ γ, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (τ γ).val =
      N (Multiplicative.toAdd
        ((torsorCover k' (Polynomial Ω) (C a * Polynomial.X)).character y q γ)))
    (hN0 : N 0 = 1) (hN : ∑ c : k', N c = 0)
    (j : CompactificationOf (Over.mk (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω))))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((derivedLowerShriek.{u, 0} (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω))) j
        (ZMod (ℓ ^ (0 + 1)))).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((lisseEtaleSheaf B (specObject (Polynomial Ω) B hP) y (ZMod (ℓ ^ (0 + 1)))).obj
            (levelModule.{u + 1, u + 1} τ hτ (0 + 1)))))) := by
  have : Fact (ℓ ^ (0 + 1)).Prime := ⟨by simpa using (Fact.out : ℓ.Prime)⟩
  let χ := (torsorCover k' (Polynomial Ω) (C a * Polynomial.X)).character y q
  have hτ1 : ∀ γ, χ γ = 1 → τ γ = 1 := by
    intro γ hγ
    apply Units.ext
    apply mapMatrix_padicInt_injective
    rw [hτN, show (torsorCover k' (Polynomial Ω) (C a * Polynomial.X)).character y q γ = 1 from hγ,
      toAdd_one, hN0, Units.val_one, map_one]
  let L : EtaleFundamentalGroup (Spec (.of (Polynomial Ω))) y →*
      Module.End (ZMod (ℓ ^ (0 + 1))) (ULift.{u + 1} (Fin r → ZMod (ℓ ^ (0 + 1)))) :=
    levelULiftRepresentation.{u + 1, u + 1} τ (0 + 1)
  have hL1 : ∀ γ, τ γ = 1 → L γ = 1 := fun γ hγ =>
    (levelULiftRepresentation_eq_of_eq τ _ (hγ.trans (map_one τ).symm)).trans (map_one _)
  rcases eq_or_ne a 0 with rfl | ha
  · refine isZero_homology_derivedLowerShriek_lisseEtaleSheaf_affineLine_of_trivial k' B hP
      (ℓ ^ (0 + 1)) hℓ y _ (fun σ => ?_) j 1 (by norm_num)
    refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun v => ?_))
    change L σ v = v
    rw [hL1 σ (hτ1 σ (DFunLike.congr_fun (torsorCover_character_scaledLine_zero k' y q) σ))]
    rfl
  · have hsurj := surjective_torsorCover_character_scaledLine k' a ha y q
    have hLeq : ∀ γ γ', χ γ = χ γ' → L γ = L γ' := by
      intro γ γ' hγ
      have h := hτ1 (γ * γ'⁻¹) (by rw [map_mul, map_inv, hγ, mul_inv_cancel])
      rw [map_mul, map_inv, mul_inv_eq_one] at h
      exact levelULiftRepresentation_eq_of_eq τ _ h
    let s := Function.surjInv hsurj
    have hs : ∀ c, χ (s c) = c := Function.surjInv_eq hsurj
    let ρK : Multiplicative k' →* Module.End (ZMod (ℓ ^ (0 + 1)))
        (ULift.{u + 1} (Fin r → ZMod (ℓ ^ (0 + 1)))) :=
      { toFun := fun c => L (s c)
        map_one' := (hLeq _ _ ((hs 1).trans (map_one χ).symm)).trans L.map_one
        map_mul' := fun c c' =>
          (hLeq _ _ ((hs _).trans (by rw [map_mul, hs, hs]))).trans (L.map_mul _ _) }
    have hρK : ∀ γ, ρK (χ γ) = L γ := fun γ => hLeq _ _ (hs _)
    refine isZero_homology_derivedLowerShriek_lisseEtaleSheaf_scaledLine k' B hP (ℓ ^ (0 + 1)) hℓ
      a ha y q _ ρK (fun σ v => ?_) (fun v => ?_) j 1
    · change L σ v = ρK (χ σ) v
      rw [hρK]
    · have hsum : ∑ c : k', (τ (s (Multiplicative.ofAdd c))).val = 0 := by
        apply mapMatrix_padicInt_injective
        rw [map_sum, map_zero]
        refine (Finset.sum_congr rfl fun c _ => ?_).trans hN
        rw [hτN]
        exact congrArg N (congrArg Multiplicative.toAdd (hs _))
      exact sum_levelULiftRepresentation_apply_eq_zero τ Finset.univ _ hsum _ v

end Fibre

end Stacks.EtaleCohomology

end
