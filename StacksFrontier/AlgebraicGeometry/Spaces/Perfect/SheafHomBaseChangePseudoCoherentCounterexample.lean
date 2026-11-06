module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePseudoCoherentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedSheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.Examples.BaseChange.ZModFourTor
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Part (2) of Stacks 08JQ fails for an arbitrary base change

Part (2) of [Stacks, Tag 08JQ] asserts that for a quasi-compact and quasi-separated morphism
`f : X ⟶ Y` of algebraic spaces, a pseudo-coherent `E ∈ D(𝒪_X)` and a bounded complex `𝒢^•` of
quasi-coherent `𝒪_X`-modules flat over `Y`, the base change map

`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)`

(`AlgebraicGeometry.Space.smallEtaleDerivedSheafHomBaseChangeMap`) is an isomorphism for every
cartesian square. This file proves that this fails for

* `Y = X = Spec ℤ/4` (the algebraic space it represents), `f = id`,
* `E = (ℤ/4 ⧸ 2)^~`, pseudo-coherent (resolved by `⋯ ⟶ ℤ/4 ⟶ ℤ/4 ⟶ ℤ/4`, multiplication by `2`),
* `𝒢^• = 𝒪_X` in degree zero (bounded, quasi-coherent, flat over `Y`),
* `g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`, `X' = Y' = Spec ℤ/2`, `f' = id`.

The source of the base change map lies in `D^{≤ 0}`: `R𝓗om(E, 𝒪_X)` has no cohomology in
positive degrees, because its `q`-th cohomology module is `Ext^q_{ℤ/4}(ℤ/2, ℤ/4)`, which vanishes
for `q ≥ 1` as `ℤ/4` is self-injective, and `Lg^*` is right t-exact. The target has nonzero
cohomology in degree `1`: that cohomology is detected by morphisms `L(g')^*E ⟶ 𝒪_{X'}[1]`, and
`L(g')^*E` is the associated complex of `ℤ/2 ⊗_{ℤ/4} (⋯ ⟶ ℤ/4 ⟶ ℤ/4)`, which has zero
differentials, so it has `𝒪_{X'}[1]` as a direct summand. In the source's proof the gap is in
Stacks 0DKI (3), which needs `g` of finite Tor dimension, and `Spec ℤ/2 ⟶ Spec ℤ/4` has not.

## Main results

* `not_isIso_baseChangeMap`: the base change map is not an isomorphism for the data above.
* `not_forall_isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent`: part (2) of
  Stacks 08JQ, negated, at the source's hypotheses.

## References

* [Stacks Project, Tag 08JQ](https://stacks.math.columbia.edu/tag/08JQ)
* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Space.SheafHomBaseChangeCounterexample

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The ring: a periodic free resolution and self-injectivity -/

section Ring

variable {R : Type u} [CommRing R] (x : R)

/-- The periodic complex `⋯ ⟶ R ⟶ R ⟶ R`, every differential multiplication by `x`, for
`x² = 0`. -/
def periodic (hx : x * x = 0) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of R R) (fun _ => x • 𝟙 (ModuleCat.of R R)) (fun _ => by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, hx, zero_smul])

/-- Every differential of `periodic x hx` is multiplication by `x`. -/
theorem periodic_d (hx : x * x = 0) (n : ℕ) :
    (periodic x hx).d (n + 1) n = x • 𝟙 (ModuleCat.of R R) := by
  simp [periodic]

/-- The quotient `R ⧸ x`, as an `R`-module. -/
abbrev quot : ModuleCat.{u} R := ModuleCat.of R (R ⧸ Ideal.span {x})

/-- The quotient map `R ⟶ R ⧸ x`. -/
def reduce : ModuleCat.of R R ⟶ quot x := ModuleCat.ofHom (Submodule.mkQ (Ideal.span {x}))

/-- The first differential of `periodic x hx` composed with `reduce x` vanishes. -/
theorem periodic_d_comp_reduce (hx : x * x = 0) :
    (periodic x hx).d 1 0 ≫ reduce x = 0 := by
  rw [periodic_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  change (Submodule.Quotient.mk (x * (show R from r)) : R ⧸ Ideal.span {x}) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2
    (Ideal.mul_mem_right (show R from r) _ (Ideal.mem_span_singleton_self x))

/-- The augmentation of the periodic complex. -/
def augmentation (hx : x * x = 0) :
    periodic x hx ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj (quot x) :=
  (ChainComplex.toSingle₀Equiv (periodic x hx) (quot x)).symm
    ⟨reduce x, periodic_d_comp_reduce x hx⟩

/-- The degree-zero component of `augmentation x hx` is `reduce x`. -/
theorem augmentation_f_zero (hx : x * x = 0) : (augmentation x hx).f 0 = reduce x :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable {x} in
/-- If the annihilator of `x` is contained in `x R`, then `periodic x hx` is exact in every
positive degree. -/
theorem periodic_exactAt_succ (hx : x * x = 0)
    (hker : ∀ r : R, x * r = 0 → ∃ s : R, x * s = r) (m : ℕ) :
    (periodic x hx).ExactAt (m + 1) := by
  rw [HomologicalComplex.exactAt_iff' (periodic x hx) (m + 2) (m + 1) m (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro r hr
  change ((periodic x hx).d (m + 1) m).hom r = 0 at hr
  rw [periodic_d] at hr
  change x • r = 0 at hr
  obtain ⟨s, hs⟩ := hker r hr
  refine ⟨s, ?_⟩
  change ((periodic x hx).d (m + 2) (m + 1)).hom s = r
  rw [periodic_d]
  exact hs

variable {x} in
/-- If the annihilator of `x` is contained in `x R`, then `augmentation x hx` is a
quasi-isomorphism, so `periodic x hx` is a free resolution of `R ⧸ x`. -/
theorem quasiIso_augmentation (hx : x * x = 0)
    (hker : ∀ r : R, x * r = 0 → ∃ s : R, x * s = r) : QuasiIso (augmentation x hx) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff]
        intro r hr
        change ((augmentation x hx).f 0).hom r = 0 at hr
        rw [augmentation_f_zero] at hr
        change (Submodule.Quotient.mk r : R ⧸ Ideal.span {x}) = 0 at hr
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 ((Submodule.Quotient.mk_eq_zero _).1 hr)
        refine ⟨s, ?_⟩
        change ((periodic x hx).d 1 0).hom s = r
        rw [periodic_d]
        change x * s = r
        rw [mul_comm, hs]
      · change Epi ((augmentation x hx).f 0)
        rw [augmentation_f_zero]
        exact (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
    all_goals rfl
  | succ m =>
    rw [quasiIsoAt_iff_exactAt']
    · exact periodic_exactAt_succ hx hker m
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The periodic projective resolution of `R ⧸ x`. -/
def resolution (hx : x * x = 0) (hker : ∀ r : R, x * r = 0 → ∃ s : R, x * s = r) :
    ProjectiveResolution (quot x) where
  complex := periodic x hx
  projective := fun _ => ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{u + 1} R)
  π := augmentation x hx
  quasiIso := quasiIso_augmentation hx hker

/-- **Baer's criterion transports along ring isomorphisms.** -/
theorem baer_of_ringEquiv {A : Type u} [CommRing A] (e : A ≃+* R) (h : Module.Baer A A) :
    Module.Baer R R := by
  intro I g
  let I' : Ideal A := I.comap e.toRingHom
  let g' : I' →ₗ[A] A :=
    { toFun := fun y => e.symm (g ⟨e y, y.2⟩)
      map_add' := fun y z => by
        rw [← map_add]
        congr 1
        rw [← map_add g]
        congr 1
        exact Subtype.ext (map_add e _ _)
      map_smul' := fun a y => by
        change e.symm (g ⟨e (a * y), _⟩) = a * e.symm (g ⟨e y, y.2⟩)
        have hy : (⟨e (a * y), (a • y).2⟩ : I) = e a • (⟨e y, y.2⟩ : I) :=
          Subtype.ext (map_mul e a y)
        rw [hy, map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply] }
  obtain ⟨f', hf'⟩ := h I' g'
  refine ⟨{ toFun := fun r => e (f' (e.symm r))
            map_add' := fun r s => by rw [map_add, map_add, map_add]
            map_smul' := fun r s => by
              change e (f' (e.symm (r * s))) = r * e (f' (e.symm s))
              rw [map_mul, ← smul_eq_mul (e.symm r), map_smul, smul_eq_mul, map_mul,
                RingEquiv.apply_symm_apply] }, fun r hr => ?_⟩
  change e (f' (e.symm r)) = g ⟨r, hr⟩
  have hr' : e.symm r ∈ I' := by
    change e (e.symm r) ∈ I
    rwa [RingEquiv.apply_symm_apply]
  rw [hf' (e.symm r) hr']
  change e (e.symm (g ⟨e (e.symm r), _⟩)) = g ⟨r, hr⟩
  rw [RingEquiv.apply_symm_apply]
  congr 1
  exact Subtype.ext (RingEquiv.apply_symm_apply e r)

/-- Extension of scalars along a map to a ring of characteristic `2` kills multiplication by
`2 = 1 + 1`. -/
theorem extendScalars_map_two_smul_id_eq_zero {R' : Type u} [CommRing R'] (ψ : R →+* R')
    (h2 : (1 + 1 : R') = 0) :
    (ModuleCat.extendScalars.{u, u, u} ψ).map ((1 + 1 : R) • 𝟙 (ModuleCat.of R R)) = 0 := by
  rw [add_smul, one_smul, Functor.map_add, CategoryTheory.Functor.map_id, ← one_smul R' (𝟙 _),
    ← add_smul, h2, zero_smul]

end Ring


/-! ### Cohomology of `R𝓗om(F, 𝒪)` on an affine representable algebraic space -/

section Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The algebraic space represented by `U`. -/
abbrev space : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩

/-- `𝒪` in degree zero, as a complex. -/
abbrev structureComplex :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (space U))) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS (space U)))

/-- Every term of `structureComplex U` is quasi-coherent. -/
theorem isQuasicoherentOnSite_structureComplex_X (n : ℤ) :
    ((structureComplex U).X n).IsQuasicoherentOnSite := by
  by_cases hn : n = 0
  · subst hn
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm ≪≫
        (representedAffineAssociatedObjUnitIso B S hS U).symm).symm
      (isQuasicoherentOnSite_representedAffineAssociated_obj B S hS U _)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn)

/-- `𝒪` in degree zero lies in `D^+_QCoh`. -/
theorem derivedCategoryBPlus_structureDerived :
    DerivedCategoryB.derivedCategoryBPlus
      (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (space U)))
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (space U).1 (space U).2).O)))
      (structureDerived (space U)) :=
  ⟨⟨0, fun i hi => (DerivedCategory.Q.obj (structureComplex U)).isZero_of_isGE 0 i hi⟩,
    qcohDerived_Q_obj_of_isQuasicoherentOnSite (structureComplex U)
      (isQuasicoherentOnSite_structureComplex_X U)⟩

/-- An `R`-module is zero exactly when every map out of `R` to it is. -/
theorem isZero_iff_subsingleton_hom_of_self {R : Type u} [CommRing R] (H : ModuleCat.{u} R) :
    IsZero H ↔ Subsingleton (ModuleCat.of R R ⟶ H) := by
  refine ⟨fun h => ⟨fun a b => h.eq_of_tgt a b⟩, fun h => ?_⟩
  have key (a : H) : a = (ModuleCat.ofHom (LinearMap.toSpanSingleton R H a)).hom 1 := by simp
  have : Subsingleton H := ⟨fun a b => by
    rw [key a, key b, Subsingleton.elim (ModuleCat.ofHom (LinearMap.toSpanSingleton R H a))
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R H b))]⟩
  exact ModuleCat.isZero_of_subsingleton H

/-- **The cohomology of `R𝓗om(F, 𝒪)` on an affine representable algebraic space.** For `F`
pseudo-coherent, `H^q(R𝓗om(F, 𝒪))` vanishes exactly when every morphism `F ⟶ 𝒪[q]` does: the
object `R𝓗om(F, 𝒪)` lies in `D_QCoh` (Stacks 0A8A), so it is `Φ(N)` with `N = RΓ(R𝓗om(F, 𝒪))`,
whose `q`-th cohomology is corepresented by `R[-q]`, and morphisms `R[-q] ⟶ N` are morphisms
`𝒪[-q] ⊗^L F ⟶ 𝒪` by Stacks 08J8. -/
theorem isZero_homology_sheafHom_iff
    (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (space U))))
    (hF : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS (space U).1 (space U).2) F)
    (q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      (((smallEtaleDerivedSheafHom B S hS (space U)).obj (op F)).obj
        (structureDerived (space U)))) ↔
      Subsingleton (F ⟶ (structureDerived (space U))⟦q⟧) := by
  set K := ((smallEtaleDerivedSheafHom B S hS (space U)).obj (op F)).obj
    (structureDerived (space U))
  have hK : QcohDerived B S hS (space U) K :=
    qcohDerived_smallEtaleDerivedSheafHom_of_isPseudoCoherent (space U) F _ hF
      (derivedCategoryBPlus_structureDerived U)
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS U K hK
  let adj := representedAffineDerivedAdjunction B S hS U
  let N := (representedAffineDerivedSections B S hS U).obj K
  let R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  have : Projective R₀ := ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{u + 1} _)
  let e₁ : (DerivedCategory.homologyFunctor _ q).obj K ≅
      (representedAffineAssociated B S hS U).obj ((DerivedCategory.homologyFunctor _ q).obj N) :=
    (DerivedCategory.homologyFunctor _ q).mapIso (asIso (adj.counit.app K)).symm ≪≫
      ((representedAffineAssociated B S hS U).mapDerivedCategoryHomologyIso q).app N
  have h₁ : IsZero ((DerivedCategory.homologyFunctor _ q).obj K) ↔
      IsZero ((DerivedCategory.homologyFunctor _ q).obj N) := by
    have := (representedAffineAssociatedFullyFaithful B S hS U).faithful
    exact ⟨fun h => isZero_of_faithful (representedAffineAssociated B S hS U) (h.of_iso e₁.symm),
      fun h => ((representedAffineAssociated B S hS U).map_isZero h).of_iso e₁⟩
  rw [h₁, isZero_iff_subsingleton_hom_of_self,
    ← (DerivedCategory.homologyFromSingleAddEquiv R₀ N q).toEquiv.subsingleton_congr]
  let T := (smallEtaleDerivedTensor B S hS (space U)).flip.obj F
  let : T.CommShift ℤ :=
    (smallEtaleDerivedTensorProduct B S hS (space U)).commShift₂.commShiftFlipObj F
  let O := structureDerived (space U)
  let eO : (DerivedCategory.singleFunctor _ q).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS (space U))) ≅ O⟦-q⟧ :=
    (((DerivedCategory.singleFunctors _).shiftIso (-q) q 0 (by omega)).app _).symm
  let eT : T.obj (O⟦-q⟧) ≅ F⟦-q⟧ :=
    (T.commShiftIso (-q)).app O ≪≫
      (shiftFunctor _ (-q)).mapIso
        ((smallEtaleDerivedTensorProduct B S hS (space U)).leftUnitor.app F)
  let E : ((DerivedCategory.singleFunctor _ q).obj R₀ ⟶ N) ≃ (F ⟶ O⟦q⟧) :=
    (adj.homEquiv _ _).symm.trans <|
      ((representedAffineDerivedAssociatedSingleUnitIso B S hS U q).homCongr (Iso.refl K)).trans <|
      (eO.homCongr (Iso.refl K)).trans <|
      ((smallEtaleDerivedTensorSheafHomAdjunction B S hS (space U) F).homEquiv _ _).symm.trans <|
      (eT.homCongr (Iso.refl O)).trans <|
      (shiftEquiv' _ (-q) q (by omega)).toAdjunction.homEquiv F O
  exact E.subsingleton_congr

/-! ### The object `E = (R ⧸ 2)^~` and its derived dual -/

/-- The object `E = (R ⧸ 2)^~` of `D(𝒪)`, for `R` the ring of functions of `U`. -/
abbrev quotDerived :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (space U))) :=
  (representedAffineDerivedAssociated B S hS U).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (quot (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))

/-- `E = (R ⧸ 2)^~` is pseudo-coherent: `R ⧸ 2` has the periodic free resolution. -/
theorem isPseudoCoherent_quotDerived
    (h2 : (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) * (1 + 1) = 0)
    (hker : ∀ r : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
      (1 + 1) * r = 0 → ∃ s, (1 + 1) * s = r) :
    RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS (space U).1 (space U).2)
      (quotDerived U) := by
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m => ?_
  refine (isPseudoCoherentFrom_iff_representedAffineDerivedSections B S hS U _
    (qcohDerived_representedAffineDerivedAssociated_obj B S hS U _) m).2 ?_
  let res := resolution (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) h2 hker
  have hPC : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor _ 0).obj
        (quot (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))) := by
    refine ⟨res.cochainComplex, ⟨⟨0, inferInstance⟩, fun i => ?_⟩,
      ⟨RingTheory.TorIndependence.projectiveResolutionIsoSingle res⟩⟩
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
      have e : res.cochainComplex.X (-k) ≅ ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := res.cochainComplexXIso (-k) k
      exact ⟨Module.Finite.equiv e.toLinearEquiv.symm, Module.Free.of_equiv e.toLinearEquiv.symm⟩
    · have : Subsingleton (res.cochainComplex.X i) := ModuleCat.isZero_iff_subsingleton.mp
        (CochainComplex.isZero_of_isStrictlyLE _ 0 _ (by omega))
      exact ⟨inferInstance, inferInstance⟩
  exact ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1 hPC m).ofIso
    (asIso ((representedAffineDerivedAdjunction B S hS U).unit.app _))

variable {U} in
/-- **`Ext^q(E, 𝒪) = 0` for `q ≥ 1`**, from the self-injectivity of `R`: maps `E ⟶ 𝒪[q]` are maps
`(R ⧸ 2)[0] ⟶ R[q]` in `D(R)`, that is elements of `Ext^q_R(R ⧸ 2, R)`. -/
theorem subsingleton_hom_quotDerived_shift
    (hbaer : Module.Baer Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) (n : ℕ) :
    Subsingleton (quotDerived U ⟶ (structureDerived (space U))⟦((n + 1 : ℕ) : ℤ)⟧) := by
  let Φ := representedAffineDerivedAssociated B S hS U
  let R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let e : (structureDerived (space U))⟦((n + 1 : ℕ) : ℤ)⟧ ≅
      Φ.obj (((DerivedCategory.singleFunctor _ 0).obj R₀)⟦((n + 1 : ℕ) : ℤ)⟧) :=
    (shiftFunctor _ _).mapIso (representedAffineDerivedAssociatedSingleUnitIso B S hS U 0).symm ≪≫
      ((Φ.commShiftIso ((n + 1 : ℕ) : ℤ)).app _).symm
  refine (((Iso.refl _).homCongr e).trans
    (representedAffineDerivedAssociatedFullyFaithful B S hS U).homEquiv.symm).subsingleton_congr.2
      ?_
  have := HasExt.standard (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  have : Module.Injective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := hbaer.injective
  have : Injective R₀ := Module.injective_object_of_injective_module _ _
  refine (Abelian.Ext.homEquiv (X := quot (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (Y := R₀) (n := n + 1)).subsingleton_congr.1 ⟨fun a b => ?_⟩
  rw [Abelian.Ext.eq_zero_of_injective a, Abelian.Ext.eq_zero_of_injective b]

variable {U} in
/-- **`R𝓗om(E, 𝒪)` lies in `D^{≤ 0}`.** -/
theorem isLE_sheafHom_quotDerived
    (h2 : (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) * (1 + 1) = 0)
    (hker : ∀ r : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
      (1 + 1) * r = 0 → ∃ s, (1 + 1) * s = r)
    (hbaer : Module.Baer Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (((smallEtaleDerivedSheafHom B S hS (space U)).obj (op (quotDerived U))).obj
      (structureDerived (space U))).IsLE 0 := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = ((n + 1 : ℕ) : ℤ) := ⟨i.toNat - 1, by omega⟩
  exact (isZero_homology_sheafHom_iff U _ (isPseudoCoherent_quotDerived U h2 hker) _).2
    (subsingleton_hom_quotDerived_shift hbaer n)

end Affine

/-! ### The derived pullback of `E` along a map to a ring of characteristic `2` -/

section Pullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {U U' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g₀ : U' ⟶ U)
  (h2 : (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) * (1 + 1) = 0)
  (hker : ∀ r : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
    (1 + 1) * r = 0 → ∃ s, (1 + 1) * s = r)

/-- The complex `(R' ⊗_R P)^~` on `U'`, for `P` the periodic resolution of `R ⧸ 2`. -/
abbrev reducedComplex :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (space U'))) ℤ :=
  ((representedAffineAssociated B S hS U').mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (resolution (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) h2 hker).cochainComplex)

/-- **`L(g')^*E ≅ (R' ⊗_R P)^~`**: `E ≅ P^~` with `P^~` a bounded above complex of flat modules,
on which `Lg^*` is the degreewise pullback, and `g^*(M^~) ≅ (R' ⊗_R M)^~`. -/
def pullbackQuotDerivedIso :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀)).obj (quotDerived U) ≅
      DerivedCategory.Q.obj (reducedComplex g₀ h2 hker) := by
  let res := resolution (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) h2 hker
  let A := representedAffineAssociated B S hS U
  let K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (space U))) ℤ :=
    (A.mapHomologicalComplex (ComplexShape.up ℤ)).obj res.cochainComplex
  have : CochainComplex.IsStrictlyLE K 0 := (CochainComplex.isStrictlyLE_iff K 0).2 fun i hi =>
    A.map_isZero (CochainComplex.isZero_of_isStrictlyLE _ 0 i hi)
  have hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS (space U)).O) (K.X i) := by
    intro i
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
      exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
        (A.mapIso (res.cochainComplexXIso (-k) k) ≪≫
          representedAffineAssociatedObjUnitIso B S hS U).symm
        (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
          (Y := smallEtaleRingedSite B S hS _ (isAlgebraicSpace_yoneda B S hS U)))
    · exact isFlat_of_isZero B S hS
        (A.map_isZero (CochainComplex.isZero_of_isStrictlyLE _ 0 i (by omega)))
  exact (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀)).mapIso
      ((representedAffineDerivedAssociated B S hS U).mapIso
          (RingTheory.TorIndependence.projectiveResolutionIsoSingle res).symm ≪≫
        A.mapDerivedCategoryFactors.app res.cochainComplex) ≪≫
    smallEtaleDerivedModulePullbackObjQIso (representedSpaceMap B S hS g₀) K 0 hflat ≪≫
    DerivedCategory.Q.mapIso
      ((representedAffineComplexPullbackIso B S hS g₀).app res.cochainComplex)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
variable {g₀ h2 hker} in
/-- The differentials of `(R' ⊗_R P)^~` vanish when `2 = 0` in `R'`. -/
theorem reducedComplex_d_eq_zero
    (h2' : (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) = 0)
    (n₁ n₂ : ℤ) (k : ℕ) (h₁ : -((k + 1 : ℕ) : ℤ) = n₁) (h₂ : -(k : ℤ) = n₂) :
    (reducedComplex g₀ h2 hker).d n₁ n₂ = 0 := by
  let res := resolution (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) h2 hker
  change (representedAffineAssociated B S hS U').map
    ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map
      (res.cochainComplex.d n₁ n₂)) = 0
  have hd : (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map
      (res.complex.d (k + 1) k) = 0 := by
    change (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g₀).hom).map
      ((periodic (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) h2).d (k + 1) k) = 0
    rw [periodic_d]
    exact extendScalars_map_two_smul_id_eq_zero _ h2'
  rw [ProjectiveResolution.cochainComplex_d res n₁ n₂ (k + 1) k h₁ h₂]
  simp only [Functor.map_comp, hd, zero_comp, comp_zero, Functor.map_zero]

variable {g₀} in
include h2 hker in
/-- **`L(g')^*E` has `𝒪_{U'}[1]` as a direct summand** when `2 = 0` on `U'`, so there is a nonzero
morphism `L(g')^*E ⟶ 𝒪_{U'}[1]`: the complex `(R' ⊗_R P)^~` has zero differentials and its
term in degree `-1` is `𝒪_{U'}`. -/
theorem not_subsingleton_hom_pullbackQuotDerived_shift_one
    (h2' : (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) = 0)
    [Nontrivial Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)] :
    ¬ Subsingleton ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀)).obj
        (quotDerived U) ⟶ (structureDerived (space U'))⟦(1 : ℤ)⟧) := by
  let res := resolution (1 + 1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) h2 hker
  let C := reducedComplex g₀ h2 hker
  let A' := representedAffineAssociated B S hS U'
  let O' := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS (space U'))
  let c : C.X (-1) ≅ O' :=
    A'.mapIso ((ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g₀).hom).mapIso
        (res.cochainComplexXIso (-1) 1) ≪≫ ModuleCat.ExtendScalars.objSelfIso _) ≪≫
      representedAffineAssociatedObjUnitIso B S hS U'
  let t : C ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).obj O' :=
    HomologicalComplex.mkHomToSingle c.hom (fun i hi => by
      obtain rfl : i = -2 := by simp at hi; omega
      rw [reducedComplex_d_eq_zero h2' (-2) (-1) 1 (by norm_num) (by norm_num), zero_comp])
  let s : (HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).obj O' ⟶ C :=
    HomologicalComplex.mkHomFromSingle c.inv (fun k hk => by
      obtain rfl : k = 0 := by simp at hk; omega
      rw [reducedComplex_d_eq_zero h2' (-1) 0 0 (by norm_num) (by norm_num), comp_zero])
  have hst : s ≫ t = 𝟙 _ := by
    ext
    simp [s, t]
  let ι : DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).obj O') ≅
      (structureDerived (space U'))⟦(1 : ℤ)⟧ :=
    (((DerivedCategory.singleFunctors _).shiftIso 1 (-1) 0 (by omega)).app O').symm
  have key : (pullbackQuotDerivedIso g₀ h2 hker).hom ≫ DerivedCategory.Q.map t ≫ ι.hom ≠ 0 := by
    intro h
    have ht : DerivedCategory.Q.map t = 0 := by
      have e₁ : DerivedCategory.Q.map t = (pullbackQuotDerivedIso g₀ h2 hker).inv ≫
          ((pullbackQuotDerivedIso g₀ h2 hker).hom ≫ DerivedCategory.Q.map t ≫ ι.hom) ≫ ι.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
      rw [e₁, h, zero_comp, comp_zero]
    have hz : IsZero (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) (-1)).obj O')) := by
      rw [IsZero.iff_id_eq_zero, ← DerivedCategory.Q.map_id, ← hst, Functor.map_comp, ht,
        comp_zero]
    have hO : IsZero O' := isZero_of_faithful (DerivedCategory.singleFunctor _ (-1)) hz
    have := (representedAffineAssociatedFullyFaithful B S hS U').faithful
    have hR := isZero_of_faithful A' (hO.of_iso (representedAffineAssociatedObjUnitIso B S hS U'))
    exact not_subsingleton _ (ModuleCat.isZero_iff_subsingleton.1 hR)
  exact fun hsub => key (@Subsingleton.elim _ hsub _ _)

end Pullback

/-! ### The counterexample: `Spec ℤ/2 ⟶ Spec ℤ/4` -/

section Example

/-- `ℤ/4`. -/
abbrev R₄ : CommRingCat.{0} := CommRingCat.of (ZMod 4)

/-- `ℤ/2`. -/
abbrev R₂ : CommRingCat.{0} := CommRingCat.of (ZMod 2)

/-- The reduction `ℤ/4 → ℤ/2`. -/
abbrev reduction : R₄ ⟶ R₂ := CommRingCat.ofHom Stacks.Examples.ZModFour.toTwo

/-- A big fppf site containing `Spec ℤ/4` and `Spec ℤ/2`. -/
abbrev site : BigFppfSite.{0} :=
  (BigFppfSite.exists_containing ({Spec R₄, Spec R₂} : Set Scheme.{0})).choose

/-- `site` contains `Spec ℤ/4`. -/
theorem site_contains_four : site.Contains (Spec R₄) :=
  (BigFppfSite.exists_containing ({Spec R₄, Spec R₂} : Set Scheme.{0})).choose_spec _ (by simp)

/-- `site` contains `Spec ℤ/2`. -/
theorem site_contains_two : site.Contains (Spec R₂) :=
  (BigFppfSite.exists_containing ({Spec R₄, Spec R₂} : Set Scheme.{0})).choose_spec _ (by simp)

/-- The base scheme `Spec ℤ/4`. -/
abbrev base : Scheme.{0} := Spec R₄

/-- `Spec ℤ/4` over itself. -/
abbrev U₄ : BigFppfOver site base site_contains_four :=
  BigFppfOver.mk site base site_contains_four site_contains_four (𝟙 base)

/-- `Spec ℤ/2` over `Spec ℤ/4`. -/
abbrev U₂ : BigFppfOver site base site_contains_four :=
  BigFppfOver.mk site base site_contains_four site_contains_two (Spec.map reduction)

/-- The scheme underlying `U₄` is affine. -/
instance : IsAffine ((BigFppfOver.toScheme site base site_contains_four).obj U₄) :=
  inferInstanceAs (IsAffine (Spec R₄))

/-- The scheme underlying `U₂` is affine. -/
instance : IsAffine ((BigFppfOver.toScheme site base site_contains_four).obj U₂) :=
  inferInstanceAs (IsAffine (Spec R₂))

/-- The closed immersion `Spec ℤ/2 ⟶ Spec ℤ/4`, over `Spec ℤ/4`. -/
abbrev closedPoint : U₂ ⟶ U₄ :=
  BigFppfOver.homMk site base site_contains_four site_contains_four (𝟙 base)
    (Spec.map reduction) (Category.comp_id _)

/-- `g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`, as a morphism of algebraic spaces. -/
abbrev g : space U₂ ⟶ space U₄ := representedSpaceMap site base site_contains_four closedPoint

/-- The ring of functions of `Spec ℤ/4` is `ℤ/4`. -/
def ringEquivFour : ZMod 4 ≃+* Γ((BigFppfOver.toScheme site base site_contains_four).obj U₄, ⊤) :=
  (Scheme.ΓSpecIso R₄).symm.commRingCatIsoToRingEquiv

/-- The ring of functions of `Spec ℤ/2` is `ℤ/2`. -/
def ringEquivTwo : ZMod 2 ≃+* Γ((BigFppfOver.toScheme site base site_contains_four).obj U₂, ⊤) :=
  (Scheme.ΓSpecIso R₂).symm.commRingCatIsoToRingEquiv

/-- `2 * 2 = 0` in the ring of functions of `Spec ℤ/4`. -/
theorem two_mul_two_four :
    (1 + 1 : Γ((BigFppfOver.toScheme site base site_contains_four).obj U₄, ⊤)) * (1 + 1) = 0 := by
  have h : ((1 + 1) * (1 + 1) : ZMod 4) = 0 := by decide
  simpa using congrArg ringEquivFour h

/-- In the ring of functions of `Spec ℤ/4`, every element annihilated by `2` is a multiple
of `2`. -/
theorem exists_two_mul_four (r : Γ((BigFppfOver.toScheme site base site_contains_four).obj U₄, ⊤))
    (hr : (1 + 1) * r = 0) : ∃ s, (1 + 1) * s = r := by
  obtain ⟨a, rfl⟩ := ringEquivFour.surjective r
  have ha : (1 + 1) * a = 0 := ringEquivFour.injective (by simpa using hr)
  have key : ∀ a : ZMod 4, (1 + 1) * a = 0 → ∃ b : ZMod 4, (1 + 1) * b = a := by decide
  obtain ⟨b, hb⟩ := key a ha
  exact ⟨ringEquivFour b, by rw [← hb]; simp⟩

/-- The ring of functions of `Spec ℤ/4` satisfies Baer's criterion as a module over itself,
so it is self-injective. -/
theorem baer_four : Module.Baer Γ((BigFppfOver.toScheme site base site_contains_four).obj U₄, ⊤)
    Γ((BigFppfOver.toScheme site base site_contains_four).obj U₄, ⊤) :=
  baer_of_ringEquiv ringEquivFour Stacks.Examples.ZModFour.baer_zmodFour

/-- `2 = 0` in the ring of functions of `Spec ℤ/2`. -/
theorem two_eq_zero_two :
    (1 + 1 : Γ((BigFppfOver.toScheme site base site_contains_four).obj U₂, ⊤)) = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  simpa using congrArg ringEquivTwo h

/-- The ring of functions of `Spec ℤ/2` is nontrivial. -/
instance : Nontrivial Γ((BigFppfOver.toScheme site base site_contains_four).obj U₂, ⊤) :=
  ringEquivTwo.symm.toEquiv.nontrivial

/-- `E = (ℤ/4 ⧸ 2)^~` on `Spec ℤ/4`. -/
abbrev E := quotDerived U₄

/-- `𝒢^• = 𝒪` in degree zero on `Spec ℤ/4`. -/
abbrev G := structureComplex U₄

/-- The cartesian square with `f = id`, `f' = id` and `g = g'`. -/
theorem isPullback_g : IsPullback g (𝟙 (space U₂)) (𝟙 (space U₄)) g := IsPullback.id_vert g

/-- `Q(g^*𝒢^•) ≅ 𝒪` on `Spec ℤ/2`. -/
def pullbackStructureComplexIso :
    DerivedCategory.Q.obj
        (((modulePullback site base site_contains_four g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G) ≅ structureDerived (space U₂) :=
  haveI := modulePullback_additive (B := site) (S := base) (hS := site_contains_four) g
  DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
        (modulePullback site base site_contains_four g) (ComplexShape.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
        (modulePullbackUnitIso site base site_contains_four g))

/-- **The base change map of part (2) of Stacks 08JQ is not an isomorphism** for
`Y = X = Spec ℤ/4`, `f = id`, `E = (ℤ/4 ⧸ 2)^~`, `𝒢^• = 𝒪_X` and `g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`:
its source lies in `D^{≤ 0}`, its target has nonzero cohomology in degree `1`. -/
theorem not_isIso_baseChangeMap :
    ¬ IsIso (smallEtaleDerivedSheafHomBaseChangeMap (𝟙 (space U₄)) g (𝟙 (space U₂)) g
      isPullback_g.w E G) := by
  intro hiso
  have hK := isLE_sheafHom_quotDerived two_mul_two_four exists_two_mul_four baer_four
  have hK' : ((derivedModulePushforward site base site_contains_four (𝟙 (space U₄))).obj
      (((smallEtaleDerivedSheafHom site base site_contains_four (space U₄)).obj (op E)).obj
        (DerivedCategory.Q.obj G))).IsLE 0 :=
    @Triangulated.TStructure.isLE_of_iso _ _ _ _ _ _ _ DerivedCategory.TStructure.t _ _
      (((derivedModulePushforwardIdIso site base site_contains_four (space U₄)).app _).symm) 0 hK
  have hsrc := isLE_smallEtaleDerivedModulePullback_obj g _ 0 hK'
  have hL := isPseudoCoherent_smallEtaleDerivedModulePullback g E
    (isPseudoCoherent_quotDerived U₄ two_mul_two_four exists_two_mul_four)
  have htgt := (isZero_homology_sheafHom_iff U₂ _ hL 1).not.2
    (not_subsingleton_hom_pullbackQuotDerived_shift_one two_mul_two_four exists_two_mul_four
      (g₀ := closedPoint) two_eq_zero_two)
  apply htgt
  refine (DerivedCategory.isZero_of_isLE _ 0 1 (by norm_num) (hX := hsrc)).of_iso
    ((DerivedCategory.homologyFunctor _ 1).mapIso ?_)
  exact ((smallEtaleDerivedSheafHom site base site_contains_four (space U₂)).obj _).mapIso
      pullbackStructureComplexIso.symm ≪≫
    ((derivedModulePushforwardIdIso site base site_contains_four (space U₂)).app _).symm ≪≫
    (@asIso _ _ _ _ _ hiso).symm

/-- The terms of `𝒢^• = 𝒪[0]` are flat over `Y` along `f = id`. -/
theorem isFlatOver_G (n : ℤ) :
    IsFlatOver site base site_contains_four (space U₄).2
      (𝟙 (space U₄) : space U₄ ⟶ space U₄).hom (G.X n) := by
  by_cases hn : n = 0
  · subst hn
    exact (isFlatOver_iff_of_iso site base site_contains_four (space U₄).2
      (𝟙 (space U₄) : space U₄ ⟶ space U₄).hom
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm).2
      (isFlatOver_structureSheafModule site base site_contains_four (𝟙 (space U₄))
        (isFlat_id site base site_contains_four (space U₄).2))
  · exact isFlatOver_of_isZero site base site_contains_four _
      (HomologicalComplex.isZero_single_obj_X _ 0 _ n hn)

/-- **Part (2) of Stacks 08JQ is false as stated.** It is not true that for every quasi-compact
and quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, every pseudo-coherent
`E ∈ D(𝒪_X)`, every bounded complex `𝒢^•` of quasi-coherent `𝒪_X`-modules flat over `Y` and
every cartesian square, the base change map
`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` of
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHomBaseChangeMap` is an isomorphism: it fails for
`Y = X = Spec ℤ/4`, `f = id`, `E = (ℤ/4 ⧸ 2)^~`, `𝒢^• = 𝒪_X` and `g = g' : Spec ℤ/2 ⟶ Spec ℤ/4`. -/
theorem not_forall_isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent :
    ¬ ∀ {B : BigFppfSite.{0}} {S : Scheme.{0}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
      (f : X ⟶ Y), IsQuasiCompact B S hS f.hom → IsQuasiSeparated B S hS f.hom →
      ∀ (E : DerivedCategory (SheafOfModules.{0} (ringedToposStructureRingSheaf B S hS X))),
        RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E →
      ∀ (G : CochainComplex (SheafOfModules.{0} (ringedToposStructureRingSheaf B S hS X)) ℤ),
        (∀ n, (G.X n).IsQuasicoherentOnSite) → (∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) →
        (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (G.X i)) →
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G) := fun h =>
  not_isIso_baseChangeMap (h (𝟙 (space U₄))
    (isQuasiCompact_of_isIso site base site_contains_four (𝟙 (space U₄) : space U₄ ⟶ space U₄).hom)
    (isQuasiSeparated_of_mono site base site_contains_four
      (𝟙 (space U₄) : space U₄ ⟶ space U₄).hom (inferInstanceAs (Mono (𝟙 _))))
    E (isPseudoCoherent_quotDerived U₄ two_mul_two_four exists_two_mul_four)
    G (isQuasicoherentOnSite_structureComplex_X U₄) isFlatOver_G
    ⟨0, 0, fun i hi => HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩
    g (𝟙 (space U₂)) g isPullback_g)

end Example

end AlgebraicGeometry.Space.SheafHomBaseChangeCounterexample

end
