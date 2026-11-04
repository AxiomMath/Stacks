module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedSectionsFinrank
public import StacksFrontier.Algebra.Homology.FibreEulerCharacteristicFiniteProjective
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerDegreeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange

/-!
# Local constancy of the twisted Euler characteristics from a finite projective model

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation, `L` an invertible
`𝒪_X`-module and `(T, 𝓕)` an object of `Coh_{X/B}` over an affine test scheme `T = Spec R`.
Suppose that the derived sections of the twisted module `𝓖 = 𝓕 ⊗ L_T^{⊗ n}` have a finite
projective model in the sense of Stacks 0A1Q: a bounded complex `M^•` of finite projective
`R`-modules with `RΓ(X_{T'}, 𝓖_{T'}) ≅ M^• ⊗^L_R R'` for every affine `T' = Spec R'` over `T`.
Then for every `t ∈ T`

`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = ∑ᵢ (-1)ⁱ rank_t M^i`,

and the right hand side is locally constant on `T`.  Since the twisted Euler characteristics are
unchanged by restriction to affine opens, `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is then locally constant
on every test scheme, and `Coh^{P, L}_{X/B} ⊆ Coh_{X/B}` is cut out by an open and closed
condition.

The identity is read over the residue field point `Spec κ(t) ⟶ T`: the cohomology of the fibre
`X_t` has the dimensions of the cohomology of the derived sections of `𝓖_t` over `Spec κ(t)`,
which by the model are those of `M^• ⊗^L_R κ(t)`, whose Euler characteristic is the alternating
sum of the ranks.

## Main definitions

All names are in the namespace `AlgebraicGeometry.Space`.

* `CoherentObject.HasFiniteProjectiveDerivedSectionsModel`: the existence of the model, the
  conclusion of Stacks 0A1Q without its compatibility with composition.

## Main results

* `CoherentObject.twistedEuler_eq_finsum_rankAtStalk_of_model`: the identity above.
* `CoherentObject.isLocallyConstant_twistedEuler_of_model`: local constancy on every test
  scheme, given models over affine test schemes.
* `CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial_of_model`:
  `Coh^{P, L}_{X/B}` is cut out by an open and closed condition, given those models.

## Implementation notes

The derived categories of the model are those of the standard model
(`HasDerivedCategory.standard`), in which Stacks 0A1Q is stated; the instances are named
explicitly.

## References

* [Stacks Project, Tag 0A1Q](https://stacks.math.columbia.edu/tag/0A1Q)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Space.CoherentObject

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- The twisted module `𝓕 ⊗ L_T^{⊗ n}` on `X_T` of an object `(T, 𝓕)` of `Coh_{X/B}`. -/
abbrev familyTwistedModule (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (n : ℤ) : Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS (D.space A.T).1 (D.space A.T).2).O).obj A.F).obj
    ((modulePullback B S hS (baseChangeProjection D.f A.T)).obj
      (invertibleTensorPower B S hS D.X.1 D.X.2 L n))

/-- **A finite projective model of the derived sections of a module on `X_T`** (the content of
Stacks 0A1Q).  For an object `(T, 𝓕)` of `Coh_{X/B}` over an affine test scheme `T = Spec R` and a
module `𝓖` on `X_T`: a bounded complex `M^•` of finite projective `R`-modules together with, for
every affine `T' = Spec R'` over `T` and every cartesian square `X' ⟶ X_T` over `T' ⟶ T`, an
isomorphism `RΓ(T', Rf'_*(g')^*𝓖) ≅ M^• ⊗^L_R R'`. -/
def HasFiniteProjectiveDerivedSectionsModel (A : CoherentObject D) [IsAffine A.testScheme]
    (G : Modules.{u, u} B S hS (D.space A.T).1 (D.space A.T).2) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(A.testScheme, ⊤))
  ∃ (M : CochainComplex (ModuleCat.{u} Γ(A.testScheme, ⊤)) ℤ) (a b : ℤ),
    M.IsStrictlyGE a ∧ M.IsStrictlyLE b ∧ (∀ i, Module.Finite Γ(A.testScheme, ⊤) (M.X i)) ∧
    (∀ i, Module.Projective Γ(A.testScheme, ⊤) (M.X i)) ∧
    ∀ {U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (g : U' ⟶ A.T.left) {X' : AlgebraicSpaces B S hS}
      (f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩) (g' : X' ⟶ D.space A.T),
      IsPullback g' f' (D.projection A.T) (representedSpaceMap B S hS g) →
      letI :=
        HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U', ⊤))
      letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
      Nonempty ((representedAffineDerivedSections B S hS U').obj
        ((derivedModulePushforward B S hS f').obj
          (DerivedCategory.Q.obj
            (((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
              (X := smallEtaleRingedTopos B S hS X')
              (Y := smallEtaleRingedTopos B S hS (D.space A.T))
              (smallEtaleRingedToposHom B S hS g').toModulesHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)))) ≅
        (representedAffineDerivedExtension B S hS g).functor.obj
          (DerivedCategory.Q.obj M))

/-- The point of `Spec Γ(T)` under a point `t` of the test scheme is the kernel of the map
`Γ(T) ⟶ Γ(Spec κ(t))` to the functions of the residue field point. -/
theorem comap_bot_representedAffineCommRingCatHom_pointSchemeHom (A : CoherentObject D)
    (t : A.testScheme) :
    letI : Field Γ(Spec (.of (A.testScheme.residueField t)), ⊤) :=
      (MulEquiv.isField (Field.toIsField (A.testScheme.residueField t))
        (Scheme.ΓSpecIso (CommRingCat.of (A.testScheme.residueField t))
          |>.commRingCatIsoToRingEquiv.toMulEquiv)).toField
    (⊥ : PrimeSpectrum Γ(Spec (.of (A.testScheme.residueField t)), ⊤)).comap
        (representedAffineCommRingCatHom B S hS (A.pointSchemeHom t)).hom =
      A.testScheme.toSpecΓ t := by
  let : Field Γ(Spec (.of (A.testScheme.residueField t)), ⊤) :=
    (MulEquiv.isField (Field.toIsField (A.testScheme.residueField t))
      (Scheme.ΓSpecIso (CommRingCat.of (A.testScheme.residueField t))
        |>.commRingCatIsoToRingEquiv.toMulEquiv)).toField
  let h := A.testScheme.fromSpecResidueField t
  let s : Spec (.of (A.testScheme.residueField t)) := IsLocalRing.closedPoint _
  have hs : h s = t := A.testScheme.fromSpecResidueField_apply t s
  have hnat := congrArg (fun k => k s) (Scheme.toSpecΓ_naturality h)
  simp only [Scheme.Hom.comp_apply, hs] at hnat
  rw [hnat]
  show PrimeSpectrum.comap h.appTop.hom ⊥ = PrimeSpectrum.comap h.appTop.hom _
  congr 1
  ext x
  constructor
  · intro hx
    exact (show x = 0 from hx) ▸ Ideal.zero_mem _
  · intro hx
    by_contra hne
    exact ((Spec (.of (A.testScheme.residueField t))).toSpecΓ s).isPrime.ne_top
      ((Ideal.eq_top_of_isUnit_mem _ hx (Ne.isUnit hne)))

/-- The twisted module on the fibre `X_t`, `𝓕_t ⊗ (L^{⊗ n})_t`, the module whose cohomology
`AlgebraicGeometry.Space.CoherentObject.twistedEuler` takes. -/
abbrev fibreTwistedModule (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    (A : CoherentObject D) (t : A.testScheme) (n : ℤ)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L] :
    Modules.{u, u} B S hS (A.fibreSpace t).1 (A.fibreSpace t).2 :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
        (A.fibreModule t)).obj
      ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj
        (invertibleTensorPower B S hS D.X.1 D.X.2 L n))

/-- The pullback of the twisted module `𝓕 ⊗ L_T^{⊗ n}` to the fibre `X_t` is the twisted module
`𝓕_t ⊗ (L^{⊗ n})_t` of the fibre. -/
def modulePullbackTwistedModuleIso (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (n : ℤ) :
    (modulePullback B S hS (D.relativeMap (A.pointTestHom t))).obj (familyTwistedModule L A n) ≅
      fibreTwistedModule L A t n :=
  modulePullbackSheafTensorIso B S hS (D.relativeMap (A.pointTestHom t)) _ _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj _).mapIso
      ((modulePullbackTriangle B S hS
        (baseChangeMap_comp_projection D.f (A.pointTestHom t))).app _).symm

/-- **The twisted Euler characteristics are the alternating sums of the ranks of a model.**  Let
`(T, 𝓕)` be an object of `Coh_{X/B}` over an affine test scheme `T = Spec R` and suppose the
derived sections of `𝓕 ⊗ L_T^{⊗ n}` have a finite projective model `M^•` (Stacks 0A1Q).  Then
`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = ∑ᵢ (-1)ⁱ rank_t M^i` for every `t ∈ T`. -/
theorem exists_twistedEuler_eq_finsum_rankAtStalk_of_model (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) [IsAffine A.testScheme] (n : ℤ)
    (h : HasFiniteProjectiveDerivedSectionsModel A (familyTwistedModule L A n)) :
    ∃ M : CochainComplex (ModuleCat.{u} Γ(A.testScheme, ⊤)) ℤ,
      (∀ i, Module.Finite Γ(A.testScheme, ⊤) (M.X i)) ∧
      (∀ i, Module.Projective Γ(A.testScheme, ⊤) (M.X i)) ∧
      {i | ¬ IsZero (M.X i)}.Finite ∧
      ∀ t : A.testScheme, twistedEuler L A t n =
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) *
          (Module.rankAtStalk (M.X i) (A.testScheme.toSpecΓ t) : ℤ) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(A.testScheme, ⊤))
  obtain ⟨M, a, b, ha, hb, hfin, hproj, hφ⟩ := h
  have hsupp : {i | ¬ IsZero (M.X i)}.Finite := by
    refine (Set.finite_Icc a b).subset fun i hi => ?_
    simp only [Set.mem_setOf_eq] at hi
    refine ⟨?_, ?_⟩
    · by_contra hlt
      exact hi (M.isZero_of_isStrictlyGE a i (by omega))
    · by_contra hlt
      exact hi (M.isZero_of_isStrictlyLE b i (by omega))
  refine ⟨M, hfin, hproj, hsupp, fun t => ?_⟩
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (A.pointScheme t)) :=
    inferInstanceAs (IsAffine (Spec (.of (A.testScheme.residueField t))))
  let e := (Scheme.ΓSpecIso (CommRingCat.of (A.testScheme.residueField t)))
    |>.commRingCatIsoToRingEquiv
  have hK : IsField Γ((BigFppfOver.toScheme B S hS).obj (A.pointScheme t), ⊤) :=
    MulEquiv.isField (Field.toIsField (A.testScheme.residueField t)) e.toMulEquiv
  let : Field Γ((BigFppfOver.toScheme B S hS).obj (A.pointScheme t), ⊤) := hK.toField
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj
    (A.pointScheme t), ⊤))
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS (A.fibreSpace t).1 (A.fibreSpace t).2)
  have := hasInjectiveResolutions_modules B S hS (A.fibreSpace t).1 (A.fibreSpace t).2
  obtain ⟨φ⟩ := hφ (A.pointSchemeHom t) (D.projection (A.pointTest t))
    (D.relativeMap (A.pointTestHom t)) (isPullback_baseChangeMap D.f (A.pointTestHom t))
  let K := Γ((BigFppfOver.toScheme B S hS).obj (A.pointScheme t), ⊤)
  let Dx := representedAffineDerivedExtension B S hS (A.pointSchemeHom t)
  have := isInvertible_invertibleTensorPower B S hS D.X.1 D.X.2 L n
  have : (fibreTwistedModule L A t n).IsQuasicoherentOnSite :=
    A.isQuasicoherentOnSite_fibreTwistedModule t (invertibleTensorPower B S hS D.X.1 D.X.2 L n)
  let Fp := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS (A.fibreSpace t))
    (Y := smallEtaleRingedTopos B S hS (D.space A.T))
    (smallEtaleRingedToposHom B S hS (D.relativeMap (A.pointTestHom t))).toModulesHom
  let eC : (Fp.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (familyTwistedModule L A n)) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (fibreTwistedModule L A t n) :=
    (HomologicalComplex.singleMapHomologicalComplex Fp (ComplexShape.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        ((pullbackModulesIsoModulePullback B S hS (D.relativeMap (A.pointTestHom t))).app _ ≪≫
          modulePullbackTwistedModuleIso L A t n)
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS (A.fibreSpace t)).O))
  let Ψ := (representedAffineDerivedSections B S hS (A.pointScheme t)).mapIso
      ((derivedModulePushforward B S hS (D.projection (A.pointTest t))).mapIso
        (DerivedCategory.Q.mapIso eC).symm) ≪≫ φ
  let d : ℤ → ℕ := fun i => Module.finrank K
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj (Dx.functor.obj
      (DerivedCategory.Q.obj M)))
  have hfinH : ∀ i : ℤ, Module.Finite K
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj (Dx.functor.obj
        (DerivedCategory.Q.obj M))) := fun i =>
    open CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars in
    moduleFinite_homology_functor_obj_Q _ Dx M (b := b) hfin hproj i
  have hE1 : ∀ k : ℕ, (Module.finrank (A.testScheme.residueField t)
      ((ModuleCat.restrictScalars (A.fibreFieldHom t)).obj
        (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (A.fibreSpace t).1 (A.fibreSpace t).2).O)).rightDerived k).obj
          (fibreTwistedModule L A t n))) : ℤ) = d k := by
    intro k
    have eH := (DerivedCategory.homologyFunctor (ModuleCat.{u} K) (k : ℤ)).mapIso Ψ
    have hbr := finrank_homology_representedAffineDerivedSections_derivedModulePushforward B S hS
      (U := A.pointScheme t) hK (D.projection (A.pointTest t))
      (D.isQuasiCompact_projection _) (D.isQuasiSeparated_projection _)
      (fibreTwistedModule L A t n) k (Module.Finite.equiv eH.toLinearEquiv.symm)
    exact_mod_cast (finrank_restrictScalars_globalSectionsRingHom (A.fibreSpace t)
      (A.pointScheme t) (D.projection (A.pointTest t)) e.symm _).trans
      (hbr.symm.trans eH.toLinearEquiv.finrank_eq)
  have hE2 : ∀ i : ℤ, i < 0 → d i = 0 := fun i hi => by
    have := ModuleCat.isZero_iff_subsingleton.mp
      (IsZero.of_iso
        (isZero_homology_representedAffineDerivedSections_derivedModulePushforward_of_neg B S hS
          (U := A.pointScheme t) (D.projection (A.pointTest t)) (D.isQuasiCompact_projection _)
          (D.isQuasiSeparated_projection _) (fibreTwistedModule L A t n) hi)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).mapIso Ψ).symm)
    exact Module.finrank_zero_of_subsingleton
  have hsum : ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (d i : ℤ) =
      ∑ᶠ k : ℕ, (-1 : ℤ) ^ k * (d k : ℤ) := by
    have hsub : Function.support (fun i : ℤ => (i.negOnePow : ℤ) * (d i : ℤ)) ⊆
        Set.range (Nat.cast : ℕ → ℤ) := by
      intro i hi
      by_contra hn
      apply hi
      have : i < 0 := by
        by_contra h
        exact hn ⟨i.toNat, Int.toNat_of_nonneg (by omega)⟩
      simp [hE2 i this]
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range (Nat.cast : ℕ → ℤ))
      (fun x hx => ⟨fun _ => hsub hx, fun _ => trivial⟩), finsum_mem_range Nat.cast_injective]
    exact finsum_congr fun k => by rw [Int.coe_negOnePow_natCast]
  have h2 :=
    open CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars in
    finsum_finrank_homology_functor_obj_Q_eq _ Dx M (a := a) (b := b) hfin hproj
  have hc := comap_bot_representedAffineCommRingCatHom_pointSchemeHom A t
  have h3 : twistedEuler L A t n = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (d i : ℤ) := by
    rw [hsum, twistedEuler, eulerCharacteristicAlong_eq_finsum_rightDerived]
    exact finsum_congr fun k => by rw [hE1 k]
  exact h3.trans (h2.trans (finsum_congr fun i =>
    congrArg (fun p => (i.negOnePow : ℤ) * (Module.rankAtStalk (M.X i) p : ℤ)) hc))

/-- Over an affine test scheme `T`, if the derived sections of `𝓕 ⊗ L_T^{⊗ n}` have a finite
projective model, then `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant on `T`. -/
theorem isLocallyConstant_twistedEuler_of_model_of_isAffine
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) [IsAffine A.testScheme] (n : ℤ)
    (h : HasFiniteProjectiveDerivedSectionsModel A (familyTwistedModule L A n)) :
    IsLocallyConstant fun t : A.testScheme => twistedEuler L A t n := by
  obtain ⟨M, hfin, hproj, hsupp, he⟩ := exists_twistedEuler_eq_finsum_rankAtStalk_of_model L A n h
  have hf : (fun t : A.testScheme => twistedEuler L A t n) =
      (fun p : PrimeSpectrum Γ(A.testScheme, ⊤) =>
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (M.X i) p : ℤ)) ∘
        A.testScheme.toSpecΓ := funext he
  rw [hf]
  exact (CochainComplex.isLocallyConstant_finsum_rankAtStalk M hfin hproj hsupp).comp_continuous
    A.testScheme.toSpecΓ.continuous

/-- **The twisted Euler characteristics are locally constant, given finite projective models
over affine test schemes** (Stacks 0A1Q, 0D1Z).  If for every object `(T, 𝓕)` of `Coh_{X/B}`
over an affine test scheme the derived sections of `𝓕 ⊗ L_T^{⊗ n}` have a finite projective
model, then `t ↦ χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is locally constant on every test scheme: it is
unchanged by restriction to an affine open
(`AlgebraicGeometry.Space.CoherentHom.twistedEuler_eq`). -/
theorem isLocallyConstant_twistedEuler_of_model (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L] (n : ℤ)
    (h : ∀ (A : CoherentObject D) [IsAffine A.testScheme],
      HasFiniteProjectiveDerivedSectionsModel A (familyTwistedModule L A n))
    (A : CoherentObject D) :
    IsLocallyConstant fun t : A.testScheme => twistedEuler L A t n := by
  rw [IsLocallyConstant.iff_exists_open]
  intro t₀
  obtain ⟨W, hW, ht₀W, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top t₀)
  let W' : ((BigFppfOver.toScheme B S hS).obj A.T.left).affineOpens := ⟨W, hW⟩
  let j := affineOpenSpecSiteHom B S hS A.T.left W'
  let T' : SchemesOver D.Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map j ≫ A.T.hom)
  let hj : T' ⟶ A.T := CostructuredArrow.homMk j rfl
  let A' := CoherentSituation.pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS)
    A hj
  let m := CoherentSituation.pullbackHom' (modulePullbackStabilityOfFinitePresentation B S hS) A hj
  have hm : ∀ s : A'.testScheme, m.baseScheme s = hW.fromSpec s := fun s => by
    show (BigFppfOver.toScheme B S hS).map j s = hW.fromSpec s
    rw [map_affineOpenSpecSiteHom]
  have hA' : IsAffine A'.testScheme :=
    inferInstanceAs (IsAffine (Spec Γ((BigFppfOver.toScheme B S hS).obj A.T.left, W)))
  obtain ⟨s₀, hs₀⟩ : t₀ ∈ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  obtain ⟨V, hV, hs₀V, hconst⟩ := (IsLocallyConstant.iff_exists_open _).1
    (isLocallyConstant_twistedEuler_of_model_of_isAffine L A' n (h A')) s₀
  have he : ∀ s : A'.testScheme, twistedEuler L A (hW.fromSpec s) n = twistedEuler L A' s n :=
    fun s => by rw [← hm s]; exact (CoherentHom.twistedEuler_eq L m s n).symm
  refine ⟨hW.fromSpec '' V, hW.fromSpec.isOpenEmbedding.isOpenMap V hV, ⟨s₀, hs₀V, hs₀⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  rw [← hs₀]
  exact (he s).trans ((hconst s hs).trans (he s₀).symm)

end AlgebraicGeometry.Space.CoherentObject

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **`Coh^{P, L}_{X/B}` is cut out by an open and closed condition, given finite projective
models of the derived sections over affine test schemes** (Stacks 0A1Q).  With the locally
bounded degrees of the Hilbert polynomials
(`AlgebraicGeometry.Space.CoherentObject.exists_mem_nhds_isPolynomialOfDegreeLE_twistedEuler`),
the local constancy of the twisted Euler characteristics given by the models is all that the
condition `P(n) = χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` for all `n` needs to be open and closed. -/
theorem isOpenAndClosedCondition_hasHilbertPolynomial_of_model
    (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (h : ∀ (A : CoherentObject D) [IsAffine A.testScheme] (n : ℤ),
      CoherentObject.HasFiniteProjectiveDerivedSectionsModel A
        (CoherentObject.familyTwistedModule L A n))
    (P : ℤ → ℤ) :
    IsOpenAndClosedCondition D (CoherentObject.HasHilbertPolynomial L P) :=
  isOpenAndClosedCondition_hasHilbertPolynomial_of_forall_isLocallyConstant L
    (fun A n => CoherentObject.isLocallyConstant_twistedEuler_of_model L n (fun A' _ => h A' n) A) P

end AlgebraicGeometry.Space.CoherentSituation

end
