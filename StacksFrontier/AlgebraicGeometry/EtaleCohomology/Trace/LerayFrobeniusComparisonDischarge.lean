module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LerayFrobeniusComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLeray
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionProperDirectImageUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactificationIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.CategoryTheory.Preadditive.Injective.GrothendieckFunctorial
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# The Leray comparison `RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, Rg_! K)` with Frobenius

Let `g : U ⟶ W` be separated of finite type between noetherian schemes, with a compactification
`j_g`, and `f_W : W ⟶ Spec k` separated of finite type over a finite field, with a
compactification `j_W : W ⟶ W̄`. Following the proof of [Stacks, Tag 0F7J], choose a
compactification `U ⟶ X̄` of `U` over `W̄` (Nagata's theorem, [Stacks, Tag 0F41]), with proper
`π : X̄ ⟶ W̄`, and compute `RΓ_c(U_k̄, -)` through `j_U : U ⟶ X̄ ⟶ W̄ ⟶ Spec k`. For an
ℓ-power torsion sheaf `K` on `U` let `M(K)` be a functorial injective resolution of `j_{U!} K` on
`X̄` ([Stacks, Tags 0139, 0141]) and `C(K) = j_W^{-1} π_* M(K)`, a bounded below complex on `W`.

* `C(K)` computes `Rg_! K`: `j_W^{-1} Rπ_* Rb_! = Rg'_*` on torsion objects, `b : X̄ ×_W̄ W ⟶ X̄`
  and `g'` the base change of `π` (proper base change, [Stacks, Tag 0DDE]), and `Rg_!` does not
  depend on the compactification ([Stacks, Tag 0F7I]).
* `RΓ_c(U_k̄, K) = RΓ(X̄_k̄, (j_{U!} K)|) ≅ RΓ(X̄_k̄, M(K)|) ≅ RΓ(W̄_k̄, (π_* M(K))|)`, the last
  step `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIsoOfIsIso`, and
  `RΓ(W̄_k̄, (π_* M(K))|) ≅ RΓ(W̄_k̄, (j_{W!} C(K))|) = RΓ_c(W_k̄, C(K))` along the counit
  `j_{W!} j_W^{-1} π_* M(K) ⟶ π_* M(K)`, a quasi-isomorphism because `Rπ_* M(K)` is an extension
  by zero from `W` ([Stacks, Tag 0F7B]). Every step is a natural isomorphism commuting with the
  canonical geometric Frobenius.

This proves `Stacks.EtaleCohomology.LAdicSheaf.LerayFrobeniusComparison`, the Leray input of the
reduction of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH))
to curves.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.lerayFrobeniusComparison`.
* `LAdicSheaf.lerayWeightInput_higherDirectImageShriekFamily_of_constructibility`:
  the Leray weight implication for `Rʳ g_! G` with the comparison discharged.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` and `compactSupportFrobeniusFunctor` live in the
standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Generalities -/

section Generalities

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

/-- The degreewise counit `L(R(N)) ⟶ N` of an adjunction of additive functors, on bounded below
complexes. -/
def mapCochainComplexPlusCounitApp {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    (adj : L ⊣ R) (N : CochainComplex.Plus B) :
    L.mapCochainComplexPlus.obj (R.mapCochainComplexPlus.obj N) ⟶ N :=
  ObjectProperty.homMk ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app N.obj)

/-- The degreewise counit `mapCochainComplexPlusCounitApp` is natural in the complex. -/
theorem mapCochainComplexPlusCounitApp_naturality {L : A ⥤ B} {R : B ⥤ A} [L.Additive]
    [R.Additive] (adj : L ⊣ R) {N N' : CochainComplex.Plus B} (f : N ⟶ N') :
    L.mapCochainComplexPlus.map (R.mapCochainComplexPlus.map f) ≫
        mapCochainComplexPlusCounitApp adj N' =
      mapCochainComplexPlusCounitApp adj N ≫ f := by
  ext n : 2
  exact adj.counit.naturality (f.hom.f n)

/-- An additive functor carries an object annihilated by `m` to one annihilated by `m`. -/
theorem nsmul_id_obj_eq_zero {A' B' : Type*} [Category* A'] [Category* B'] [Preadditive A']
    [Preadditive B'] (F : A' ⥤ B') [F.Additive] {X : A'} {m : ℕ} (h : m • 𝟙 X = 0) :
    m • 𝟙 (F.obj X) = 0 := by
  rw [← F.map_id, ← F.map_nsmul, h, F.map_zero]

/-- A bounded below complex annihilated by a positive integer has torsion cohomology sheaves. -/
theorem isTorsionPlus_Q_obj_of_nsmul {X : Scheme.{u}} {Λ : Type} [Ring Λ]
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (m : ℕ) (hm : 0 < m)
    (h : m • 𝟙 M.obj = 0) : isTorsionPlus.{u, 0} Λ X (DerivedCategory.Plus.Q.obj M) := fun i =>
  IsTorsionEtaleModule.of_iso Λ X ((DerivedCategory.homologyFunctorFactors _ i).app M.obj).symm
    (isTorsionEtaleModule_of_nsmul_id_eq_zero_typeZero _ m hm
      (nsmul_id_obj_eq_zero (HomologicalComplex.homologyFunctor _ _ i) h))

/-- Torsion cohomology sheaves are invariant under isomorphism in `D⁺`. -/
theorem isTorsionPlus_of_iso {X : Scheme.{u}} {Λ : Type} [Ring Λ]
    {K K' : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)} (e : K ≅ K')
    (hK : isTorsionPlus.{u, 0} Λ X K) : isTorsionPlus.{u, 0} Λ X K' := fun i =>
  IsTorsionEtaleModule.of_iso Λ X ((DerivedCategory.Plus.homologyFunctor _ i).mapIso e) (hK i)

/-- Conjugating endomorphisms along `a ≫ b ≫ c⁻¹`. -/
theorem comp_comp_inv_conj {C₀ : Type*} [Category* C₀] {X₁ X₂ X₃ X₄ : C₀} (f₁ : X₁ ⟶ X₁)
    (f₂ : X₂ ⟶ X₂) (f₃ : X₃ ⟶ X₃) (f₄ : X₄ ⟶ X₄) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (c : X₄ ⟶ X₃)
    (hci : IsIso c) (ha : f₁ ≫ a = a ≫ f₂) (hb : f₂ ≫ b = b ≫ f₃) (hc : c ≫ f₃ = f₄ ≫ c) :
    f₁ ≫ a ≫ b ≫ inv c = (a ≫ b ≫ inv c) ≫ f₄ := by
  rw [← cancel_mono c]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hc, IsIso.inv_hom_id_assoc, reassoc_of% ha, hb]

/-- The unit `Q(F K) ⟶ RF(Q K)` is invertible for a functor preserving homology. -/
theorem isIso_mapCochainComplexPlusDerivedUnit_app_of_preservesHomology [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology] (K : CochainComplex.Plus A) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit F).app K) := by
  have hu : IsIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj K)) :=
    have := F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    NatIso.isIso_app_of_isIso _ _
  rw [Functor.mapCochainComplexPlusDerivedUnit_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (@IsIso.comp_isIso _ _ _ _ _ _ _ hu
    inferInstance)

/-- An isomorphism between zero objects. -/
theorem isIso_of_isZero_of_isZero {C₀ : Type*} [Category* C₀] {X Y : C₀} (f : X ⟶ Y)
    (hX : IsZero X) (hY : IsZero Y) : IsIso f := by
  rw [hX.eq_of_src f (hX.iso hY).hom]
  infer_instance

end Generalities

/-! ### `RΓ(Y_k̄, -|_{Y_k̄})` as a functor of complexes -/

section Restriction

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- `C ↦ RΓ(Y_k̄, C|_{Y_k̄})`, of which `compactSupportFrobeniusFunctor` is the value at
`j_! K`. -/
abbrev frobeniusRestrictionCohomologyFunctor :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Λ) :=
  fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar ⋙
    etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) ⋙
    etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))

omit [Fintype k] in
/-- `C ↦ RΓ(Y_k̄, C|_{Y_k̄})` inverts quasi-isomorphisms, inverse image being exact. -/
theorem isIso_frobeniusRestrictionCohomologyFunctor_map_of_quasiIso
    {K L : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : K ⟶ L) (hφ : QuasiIso φ.hom) :
    IsIso ((frobeniusRestrictionCohomologyFunctor Λ Y kbar).map φ) := by
  have : PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) :=
    etaleModuleInverseImage_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)) :=
    etaleModuleInverseImage_preservesFiniteColimits _ _
  have h₁ : QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map φ).hom) := by
    change QuasiIso (((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar)).mapHomologicalComplex _).map φ.hom)
    infer_instance
  have := isIso_plusQ_map_of_quasiIso_of_abelian _ h₁
  dsimp only [frobeniusRestrictionCohomologyFunctor, fieldBaseChangeRestrictionFunctor,
    Functor.comp_map]
  infer_instance

end Restriction

/-! ### The construction -/

section Leray

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {U W : B.Scheme} (g : U ⟶ W)
  {k : Type u} [Field k] [Fintype k] (fW : W.1 ⟶ Spec (.of k))
  (jW : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  (jX : CompactificationOf (Over.mk (B.inclusion.map g ≫ jW.immersion)))
  (R : CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] jX.space) ⥤
    CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] jX.space)) (α : 𝟭 _ ⟶ R)

/-- The proper morphism `π : X̄ ⟶ W̄`, over `k`. -/
abbrev lerayAmbientHom :
    Over.mk (CompactificationOf.compOver jW jX).toBase ⟶ Over.mk jW.toBase :=
  Over.homMk jX.toBase rfl

/-- `K ↦ M(K)`: the resolution `R` of `j_{U!} K` on `X̄`. -/
abbrev lerayResolution :
    (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] jX.space) :=
  (IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _ ⋙
    (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ]
      (CompactificationOf.compOver jW jX).immersion).mapCochainComplexPlus ⋙ R

/-- `K ↦ C(K) = j_W^{-1} π_* M(K)`, a bounded below complex on `W`. -/
abbrev lerayComplex :
    (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤ CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] W.1) :=
  lerayResolution B ℓ g fW jW jX R ⋙
    (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapCochainComplexPlus ⋙
    (etaleModuleRestriction.{u, 0} ℤ_[ℓ] jW.immersion).mapCochainComplexPlus

/-- The counit `j_{W!} C(K) ⟶ π_* M(K)`. -/
abbrev lerayCounit (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :=
  mapCochainComplexPlusCounitApp (etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] jW.immersion)
    ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapCochainComplexPlus.obj
      ((lerayResolution B ℓ g fW jW jX R).obj K))

omit [Fintype k] in
/-- `j_{U!} K` is killed by a power of `ℓ`, hence has torsion cohomology. -/
theorem isTorsionPlus_lerayExtension (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :
    isTorsionPlus.{u, 0} ℤ_[ℓ] jX.space (DerivedCategory.Plus.Q.obj
      ((etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ]
        (CompactificationOf.compOver jW jX).immersion).mapCochainComplexPlus.obj
          ((singlePlus _).obj K.obj))) := by
  obtain ⟨N, hN⟩ := K.property
  exact isTorsionPlus_Q_obj_of_nsmul _ (ℓ ^ N) (pow_pos (Fact.out : ℓ.Prime).pos N)
    (nsmul_id_obj_eq_zero ((etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ]
      (CompactificationOf.compOver jW jX).immersion).mapHomologicalComplex (ComplexShape.up ℤ))
      (nsmul_id_obj_eq_zero (HomologicalComplex.single _ (ComplexShape.up ℤ) 0) hN))

omit [Fintype k] in
/-- `M(K)` has torsion cohomology. -/
theorem isTorsionPlus_lerayResolution (hα : ∀ K, QuasiIso (α.app K).hom)
    (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :
    isTorsionPlus.{u, 0} ℤ_[ℓ] jX.space (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.quotient _).obj ((lerayResolution B ℓ g fW jW jX R).obj K))) :=
  isTorsionPlus_of_iso ((@asIso _ _ _ _ (DerivedCategory.Plus.Q.map (α.app _))
      (isIso_plusQ_map_of_quasiIso_of_abelian _ (hα _))) ≪≫
      ((DerivedCategory.Plus.quotientCompQhIso _).app _).symm)
    (isTorsionPlus_lerayExtension B ℓ g fW jW jX K)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

section Frobenius

variable (hα : ∀ K, QuasiIso (α.app K).hom) (hR : ∀ K n, Injective ((R.obj K).obj.X n))
  (hc : ∀ K, QuasiIso (lerayCounit B ℓ g fW jW jX R K).hom)

omit [Fintype k] in
include hα hR in
/-- For the base change `π_{k̄}` of `π` to `k̄`, the comparison
`Q(π_{k̄*}(M(K)|_{X̄_k̄})) ⟶ Rπ_{k̄*} Q(M(K)|_{X̄_k̄})` is an isomorphism. -/
theorem isIso_lerayUnit [Finite k] (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, 0} ℤ_[ℓ]
        (fieldBaseChangeMap (lerayAmbientHom B g fW jW jX) kbar))).app
        ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (fieldBaseChangeProj
          (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar)).mapCochainComplexPlus.obj
            ((lerayResolution B ℓ g fW jW jX R).obj K))) :=
  have : IsProper (lerayAmbientHom B g fW jW jX).left := (inferInstance : IsProper jX.toBase)
  isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap_of_injective ℤ_[ℓ]
    (lerayAmbientHom B g fW jW jX) kbar _ (hR _)
    (isTorsionPlus_lerayResolution B ℓ g fW jW jX R α hα K)

include hα hR in
/-- `RΓ(X̄_k̄, M(K)|_{X̄_k̄}) ≅ RΓ(W̄_k̄, (π_* M(K))|_{W̄_k̄})`. -/
def lerayProperIso (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :
    (frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
        (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar).obj
        ((lerayResolution B ℓ g fW jW jX R).obj K) ≅
      (frobeniusRestrictionCohomologyFunctor ℤ_[ℓ] (Over.mk jW.toBase) kbar).obj
        ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapCochainComplexPlus.obj
          ((lerayResolution B ℓ g fW jW jX R).obj K)) :=
  haveI := isIso_lerayUnit B ℓ g fW jW kbar jX R α hα hR K
  haveI : IsProper (lerayAmbientHom B g fW jW jX).left := (inferInstance : IsProper jX.toBase)
  frobeniusRestrictionProperDirectImageIsoOfIsIso ℤ_[ℓ] (lerayAmbientHom B g fW jW jX) kbar _

/-- `K ↦ j_{U!} K` on `X̄`. -/
abbrev lerayExtension :
    (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] jX.space) :=
  (IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _ ⋙ (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ]
    (CompactificationOf.compOver jW jX).immersion).mapCochainComplexPlus

include hα in
/-- `RΓ(X̄_k̄, -|)` of the resolution `j_{U!} K ⟶ M(K)`. -/
def lerayResolutionIso :
    lerayExtension B ℓ g fW jW jX ⋙ frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
        (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar ≅
      lerayResolution B ℓ g fW jW jX R ⋙ frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
        (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar :=
  haveI : ∀ X, IsIso ((frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
      (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar).map (α.app X)) := fun X =>
    isIso_frobeniusRestrictionCohomologyFunctor_map_of_quasiIso ℤ_[ℓ]
      (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar (α.app X) (hα X)
  NatIso.ofComponents (fun K => asIso ((frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
      (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar).map
        (α.app ((lerayExtension B ℓ g fW jW jX).obj K))))
    fun {K K'} f =>
      let P := lerayExtension B ℓ g fW jW jX
      let Γ := frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
        (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar
      (Γ.map_comp (P.map f) (α.app (P.obj K'))).symm.trans
        ((congrArg Γ.map (α.naturality (P.map f))).trans
          (Γ.map_comp (α.app (P.obj K)) (R.map (P.map f))))

include hα hR in
/-- The proper Leray step, naturally in `K`. -/
def lerayProperNatIso :
    lerayResolution B ℓ g fW jW jX R ⋙ frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
        (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar ≅
      lerayResolution B ℓ g fW jW jX R ⋙
        (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapCochainComplexPlus ⋙
          frobeniusRestrictionCohomologyFunctor ℤ_[ℓ] (Over.mk jW.toBase) kbar :=
  NatIso.ofComponents (lerayProperIso B ℓ g fW jW kbar jX R α hα hR) fun {K K'} f => by
    have := isIso_lerayUnit B ℓ g fW jW kbar jX R α hα hR K
    have := isIso_lerayUnit B ℓ g fW jW kbar jX R α hα hR K'
    have : IsProper (lerayAmbientHom B g fW jW jX).left := (inferInstance : IsProper jX.toBase)
    exact frobeniusRestrictionProperDirectImageIsoOfIsIso_hom_naturality ℤ_[ℓ]
      (lerayAmbientHom B g fW jW jX) kbar ((lerayResolution B ℓ g fW jW jX R).map f)

include hc in
/-- `RΓ(W̄_k̄, -|)` of the counit `j_{W!} C(K) ⟶ π_* M(K)`, naturally in `K`. -/
def lerayCounitNatIso :
    lerayComplex B ℓ g fW jW jX R ⋙
        (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] jW.immersion).mapCochainComplexPlus ⋙
          frobeniusRestrictionCohomologyFunctor ℤ_[ℓ] (Over.mk jW.toBase) kbar ≅
      lerayResolution B ℓ g fW jW jX R ⋙
        (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapCochainComplexPlus ⋙
          frobeniusRestrictionCohomologyFunctor ℤ_[ℓ] (Over.mk jW.toBase) kbar :=
  haveI : ∀ K, IsIso ((frobeniusRestrictionCohomologyFunctor ℤ_[ℓ] (Over.mk jW.toBase) kbar).map
      (lerayCounit B ℓ g fW jW jX R K)) := fun K =>
    isIso_frobeniusRestrictionCohomologyFunctor_map_of_quasiIso ℤ_[ℓ] (Over.mk jW.toBase) kbar
      (lerayCounit B ℓ g fW jW jX R K) (hc K)
  NatIso.ofComponents (fun K => asIso ((frobeniusRestrictionCohomologyFunctor ℤ_[ℓ]
      (Over.mk jW.toBase) kbar).map (lerayCounit B ℓ g fW jW jX R K))) fun {K K'} f =>
    let Γ := frobeniusRestrictionCohomologyFunctor ℤ_[ℓ] (Over.mk jW.toBase) kbar
    let π := (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapCochainComplexPlus
    let E := (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] jW.immersion).mapCochainComplexPlus
    let ρ := (etaleModuleRestriction.{u, 0} ℤ_[ℓ] jW.immersion).mapCochainComplexPlus
    let h := π.map ((lerayResolution B ℓ g fW jW jX R).map f)
    (Γ.map_comp (E.map (ρ.map h)) (lerayCounit B ℓ g fW jW jX R K')).symm.trans
      ((congrArg Γ.map (mapCochainComplexPlusCounitApp_naturality
          (etaleModuleExtensionByZeroAdj.{u, 0} ℤ_[ℓ] jW.immersion) h)).trans
        (Γ.map_comp (lerayCounit B ℓ g fW jW jX R K) h))

include hα hR hc in
/-- **`RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, C(K))`**, naturally in `K`: `RΓ(X̄_k̄, -|)` of the resolution
`j_{U!} K ⟶ M(K)`, the proper Leray step along `π`, and the inverse of `RΓ(W̄_k̄, -|)` of the
counit `j_{W!} C(K) ⟶ π_* M(K)`. -/
def lerayFrobeniusIso :
    LAdicSheaf.torsionCompactSupport B ℓ g fW kbar (CompactificationOf.compOver jW jX) ≅
      lerayComplex B ℓ g fW jW jX R ⋙ compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] fW jW kbar :=
  NatIso.ofComponents (fun K => (lerayResolutionIso B ℓ g fW jW kbar jX R α hα).app K ≪≫
      (lerayProperNatIso B ℓ g fW jW kbar jX R α hα hR).app K ≪≫
        (lerayCounitNatIso B ℓ g fW jW kbar jX R hc).symm.app K)
    fun f => (lerayResolutionIso B ℓ g fW jW kbar jX R α hα ≪≫
      lerayProperNatIso B ℓ g fW jW kbar jX R α hα hR ≪≫
        (lerayCounitNatIso B ℓ g fW jW kbar jX R hc).symm).hom.naturality f

include hα hR hc in
/-- **The isomorphism `RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, C(K))` commutes with the canonical geometric
Frobenius.** -/
theorem lerayFrobeniusIso_hom_frobenius :
    Functor.whiskerLeft ((IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _)
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] (B.inclusion.map g ≫ fW)
          (CompactificationOf.compOver jW jX) kbar p q hcard) ≫
        (lerayFrobeniusIso B ℓ g fW jW kbar jX R α hα hR hc).hom =
      (lerayFrobeniusIso B ℓ g fW jW kbar jX R α hα hR hc).hom ≫
        Functor.whiskerLeft (lerayComplex B ℓ g fW jW jX R)
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fW jW kbar p q hcard) := by
  refine NatTrans.ext (funext fun K => ?_)
  have := isIso_lerayUnit B ℓ g fW jW kbar jX R α hα hR K
  have : IsProper (lerayAmbientHom B g fW jW jX).left := (inferInstance : IsProper jX.toBase)
  exact comp_comp_inv_conj _ _ _ _ _ _ _
    (isIso_frobeniusRestrictionCohomologyFunctor_map_of_quasiIso ℤ_[ℓ] (Over.mk jW.toBase)
      kbar (lerayCounit B ℓ g fW jW jX R K) (hc K))
    (frobeniusRestrictionCohomologyEndo_naturality
      (Over.mk (CompactificationOf.compOver jW jX).toBase) kbar p q hcard (α.app _)).symm
    (frobeniusRestrictionProperDirectImageIsoOfIsIso_hom_frobenius ℤ_[ℓ]
      (lerayAmbientHom B g fW jW jX) kbar p q hcard ((lerayResolution B ℓ g fW jW jX R).obj K))
    (frobeniusRestrictionCohomologyEndo_naturality (Over.mk jW.toBase) kbar p q hcard
      (lerayCounit B ℓ g fW jW jX R K))

end Frobenius

section Derived

variable (hα : ∀ K, QuasiIso (α.app K).hom) (hR : ∀ K n, Injective ((R.obj K).obj.X n))

/-- Extension by zero along `a ≫ b` is extension by zero along `a` then along `b`, on bounded
below complexes. -/
def extensionByZeroCompPlusNatIso {T₁ T₂ T₃ : Scheme.{u}} (a : T₁ ⟶ T₂) (b : T₂ ⟶ T₃) [Etale a]
    [Etale b] :
    (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] (a ≫ b)).mapCochainComplexPlus ≅
      (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] a).mapCochainComplexPlus ⋙
        (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] b).mapCochainComplexPlus :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _
      ((NatIso.mapHomologicalComplex (etaleModuleExtensionByZeroCompIso.{u, 0} ℤ_[ℓ] a b)
        (ComplexShape.up ℤ)).app K.obj))
    fun f => by
      ext n : 2
      exact (etaleModuleExtensionByZeroCompIso.{u, 0} ℤ_[ℓ] a b).hom.naturality (f.hom.f n)

/-- `K ↦ R(rbImm)_! K` on `X̄ ×_W̄ W`, for the open immersion `rbImm : U ⟶ X̄ ×_W̄ W`. -/
abbrev lerayRestrictedExtension :
    (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤ DerivedCategory.Plus (EtaleModules.{u, 0} ℤ_[ℓ]
      (CompactificationOf.restrictBase jW jX).space) :=
  (IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _ ⋙ DerivedCategory.Plus.Q ⋙
    etaleModuleDerivedExtensionByZero.{u, 0} ℤ_[ℓ] (CompactificationOf.restrictBase jW jX).immersion

/-- An ℓ-power torsion sheaf `K` on `U`, as a complex concentrated in degree `0`, has torsion
cohomology. -/
theorem isTorsionPlus_singlePlus (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :
    isTorsionPlus.{u, 0} ℤ_[ℓ] U.1 (DerivedCategory.Plus.Q.obj ((singlePlus _).obj K.obj)) := by
  obtain ⟨N, hN⟩ := K.property
  exact isTorsionPlus_Q_obj_of_nsmul _ (ℓ ^ N) (pow_pos (Fact.out : ℓ.Prime).pos N)
    (nsmul_id_obj_eq_zero (HomologicalComplex.single _ (ComplexShape.up ℤ) 0) hN)

omit [Fintype k] in
/-- `R(rbImm)_! K` has torsion cohomology. -/
theorem isTorsionPlus_lerayRestrictedExtension (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :
    isTorsionPlus.{u, 0} ℤ_[ℓ] (CompactificationOf.restrictBase jW jX).space
      ((lerayRestrictedExtension B ℓ g fW jW jX).obj K) :=
  isTorsionPlus_etaleModuleDerivedExtensionByZero_obj ℤ_[ℓ] _ _ (isTorsionPlus_singlePlus B ℓ K)

include hα in
/-- **`Q(M(K)) ≅ Rb_! R(rbImm)_! K`** in `D⁺(X̄)`, naturally in `K`: the resolution, the
composition of extensions by zero, and the units of the exact extensions by zero. -/
def lerayResolutionQIso :
    lerayResolution B ℓ g fW jW jX R ⋙ DerivedCategory.Plus.Q ≅
      lerayRestrictedExtension B ℓ g fW jW jX ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} ℤ_[ℓ] (CompactificationOf.restrictBaseι jW jX) :=
  let P := lerayExtension B ℓ g fW jW jX
  let Q := (DerivedCategory.Plus.Q : CochainComplex.Plus (EtaleModules.{u, 0} ℤ_[ℓ] jX.space) ⥤ _)
  let a := (CompactificationOf.restrictBase jW jX).immersion
  let b := CompactificationOf.restrictBaseι jW jX
  let Ea := (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] a)
  let Eb := (etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] b)
  let S := (IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus (EtaleModules.{u, 0} ℤ_[ℓ] U.1)
  haveI : ∀ X, IsIso (Q.map (α.app X)) := fun X => isIso_plusQ_map_of_quasiIso_of_abelian _ (hα X)
  haveI := fun X => isIso_mapCochainComplexPlusDerivedUnit_app_of_preservesHomology Ea X
  haveI := fun X => isIso_mapCochainComplexPlusDerivedUnit_app_of_preservesHomology Eb X
  let S₃ : P ⋙ Q ≅ lerayResolution B ℓ g fW jW jX R ⋙ Q :=
    NatIso.ofComponents (fun K => asIso (Q.map (α.app (P.obj K)))) fun {K K'} f =>
      (Q.map_comp (P.map f) (α.app (P.obj K'))).symm.trans
        ((congrArg Q.map (α.naturality (P.map f))).trans
          (Q.map_comp (α.app (P.obj K)) (R.map (P.map f))))
  let S₄ : P ⋙ Q ≅ S ⋙ Ea.mapCochainComplexPlus ⋙ Eb.mapCochainComplexPlus ⋙ Q :=
    NatIso.ofComponents (fun K => Q.mapIso ((extensionByZeroCompPlusNatIso ℓ a b).app (S.obj K)))
      fun f => (Q.map_comp _ _).symm.trans ((congrArg Q.map
        ((extensionByZeroCompPlusNatIso ℓ a b).hom.naturality (S.map f))).trans (Q.map_comp _ _))
  let S₅ : S ⋙ Ea.mapCochainComplexPlus ⋙ Eb.mapCochainComplexPlus ⋙ Q ≅
      S ⋙ Ea.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ Eb.rightDerivedFunctorPlus :=
    NatIso.ofComponents (fun K => asIso ((Functor.mapCochainComplexPlusDerivedUnit Eb).app
        (Ea.mapCochainComplexPlus.obj (S.obj K))))
      fun f => (Functor.mapCochainComplexPlusDerivedUnit Eb).naturality
        (Ea.mapCochainComplexPlus.map (S.map f))
  let S₆ : S ⋙ Ea.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙ Eb.rightDerivedFunctorPlus ≅
      lerayRestrictedExtension B ℓ g fW jW jX ⋙ Eb.rightDerivedFunctorPlus :=
    NatIso.ofComponents (fun K => Eb.rightDerivedFunctorPlus.mapIso
        (asIso ((Functor.mapCochainComplexPlusDerivedUnit Ea).app (S.obj K))))
      fun f => (Eb.rightDerivedFunctorPlus.map_comp _ _).symm.trans ((congrArg
        Eb.rightDerivedFunctorPlus.map ((Functor.mapCochainComplexPlusDerivedUnit Ea).naturality
          (S.map f))).trans (Eb.rightDerivedFunctorPlus.map_comp _ _))
  NatIso.ofComponents (fun K => S₃.symm.app K ≪≫ S₄.app K ≪≫ S₅.app K ≪≫ S₆.app K)
    fun f => (S₃.symm ≪≫ S₄ ≪≫ S₅ ≪≫ S₆).hom.naturality f

/-- The closed complement of `W` in `W̄`, with its reduced structure. -/
abbrev lerayBoundary : (Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range jW.immersion.base)ᶜ, jW.immersion.isOpenEmbedding.isOpen_range.isClosed_compl⟩ :
      TopologicalSpace.Closeds jW.space)).subscheme ⟶ jW.space :=
  Scheme.IdealSheafData.subschemeι _

omit [Fintype k] in
/-- The image of `j_W` is the complement of the image of `lerayBoundary`. -/
theorem range_immersion_eq_compl_range_lerayBoundary :
    Set.range jW.immersion.base = (Set.range (lerayBoundary B fW jW).base)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact (compl_compl _).symm

omit [Fintype k] in
include hα hR in
/-- **The counit `j_{W!} j_W^{-1} π_* M(K) ⟶ π_* M(K)` is a quasi-isomorphism**: over `W` it is
invertible since the unit of `j_{W!} ⊣ j_W^{-1}` is; over the closed complement both sides vanish,
`Rπ_* M(K) = Rπ_* Rb_! (-)` being an extension by zero from `W` ([Stacks, Tag 0F7B]). -/
theorem quasiIso_lerayCounit (K : (IsLPowerTorsion ℓ U.1).FullSubcategory) :
    QuasiIso (lerayCounit B ℓ g fW jW jX R K).hom := by
  let j := jW.immersion
  let c := lerayBoundary B fW jW
  let N := (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapCochainComplexPlus.obj
    ((lerayResolution B ℓ g fW jW jX R).obj K)
  let ε := lerayCounit B ℓ g fW jW jX R K
  let res := etaleModuleRestriction.{u, 0} ℤ_[ℓ] j
  let Ej := etaleModuleExtensionByZero.{u, 0} ℤ_[ℓ] j
  let ci := etaleModuleInverseImage.{u, 0} ℤ_[ℓ] c
  have : PreservesFiniteLimits ci := etaleModuleInverseImage_preservesFiniteLimits _ _
  have : PreservesFiniteColimits ci := etaleModuleInverseImage_preservesFiniteColimits _ _
  have : res.PreservesHomology := Functor.preservesHomologyOfExact _
  have : ci.PreservesHomology := Functor.preservesHomologyOfExact _
  have hcj : Disjoint (Set.range c.base) (Set.range j.base) :=
    disjoint_compl_right.mono_right (range_immersion_eq_compl_range_lerayBoundary B fW jW).le
  have hπ := isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic
    (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase) ((lerayResolution B ℓ g fW jW jX R).obj K)
    fun n => by
      have : Injective (((lerayResolution B ℓ g fW jW jX R).obj K).obj.X n) := hR _ n
      exact Functor.rightAcyclic_of_injective _ _
  let A : (isTorsionPlus.{u, 0} ℤ_[ℓ]
      (CompactificationOf.restrictBase jW jX).space).FullSubcategory :=
    ⟨_, isTorsionPlus_lerayRestrictedExtension B ℓ g fW jW jX K⟩
  let eN : DerivedCategory.Plus.Q.obj N ≅ (etaleModuleDerivedExtensionByZero.{u, 0} ℤ_[ℓ] j).obj
      ((etaleModuleDerivedDirectImage.{u, 0} ℤ_[ℓ]
        (CompactificationOf.restrictBase jW jX).toBase).obj A.obj) :=
    asIso ((Functor.mapCochainComplexPlusDerivedUnit
        (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase)).app
          ((lerayResolution B ℓ g fW jW jX R).obj K)) ≪≫
      (etaleModuleDerivedDirectImage.{u, 0} ℤ_[ℓ] jX.toBase).mapIso
        ((lerayResolutionQIso B ℓ g fW jW jX R α hα).app K) ≪≫
      (etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper ℤ_[ℓ] jX.toBase j
        (CompactificationOf.restrictBaseι jW jX) (CompactificationOf.restrictBase jW jX).toBase
        (IsPullback.of_hasPullback jX.toBase j)).app A
  suffices h : IsIso (DerivedCategory.Plus.Q.map ε) by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ε)) := inferInstance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 this
  refine isIso_of_isIso_etaleModuleDerivedInverseImagePlus ℤ_[ℓ] c j
    (range_immersion_eq_compl_range_lerayBoundary B fW jW) _ ?_ ?_
  · have hz : ∀ {Z Y}, (Z ≅ (etaleModuleDerivedExtensionByZero.{u, 0} ℤ_[ℓ] j).obj Y) →
        IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} ℤ_[ℓ] c).obj Z) := fun e =>
      (isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint ℤ_[ℓ] c j hcj
        _).of_iso ((etaleModuleDerivedInverseImagePlus.{u, 0} ℤ_[ℓ] c).mapIso e)
    have := isIso_mapCochainComplexPlusDerivedUnit_app_of_preservesHomology Ej
      (res.mapCochainComplexPlus.obj N)
    exact isIso_of_isZero_of_isZero _
      (hz (asIso ((Functor.mapCochainComplexPlusDerivedUnit Ej).app
        (res.mapCochainComplexPlus.obj N)))) (hz eN)
  · rw [← NatIso.isIso_map_iff (etaleModuleDerivedRestrictionIsoInverseImagePlus ℤ_[ℓ] j)]
    have := isIso_mapCochainComplexPlusDerivedUnit_app_of_preservesHomology res
      (Ej.mapCochainComplexPlus.obj (res.mapCochainComplexPlus.obj N))
    have := isIso_mapCochainComplexPlusDerivedUnit_app_of_preservesHomology res N
    have : ∀ n, IsIso ((res.mapCochainComplexPlus.map ε).hom.f n) := fun n =>
      isIso_etaleModuleRestriction_map_counit ℤ_[ℓ] j (N.obj.X n)
    have : IsIso (res.mapCochainComplexPlus.map ε).hom :=
      HomologicalComplex.Hom.isIso_of_components _
    have := isIso_plusQ_map_of_quasiIso_of_abelian (res.mapCochainComplexPlus.map ε)
      (quasiIso_of_isIso _)
    have hn := (Functor.mapCochainComplexPlusDerivedUnit res).naturality ε
    dsimp only [Functor.comp_map] at hn
    exact IsIso.of_isIso_fac_left hn.symm

variable (jg : CompactificationOf (Over.mk (B.inclusion.map g))) [CompactSpace (B.inclusion.obj W)]
  [QuasiSeparatedSpace (B.inclusion.obj W)] [IsSeparated (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)]

include hα hR in
/-- **`C(K)` computes `Rg_! K`**: `Q(j_W^{-1} π_* M(K)) ≅ j_W^{-1} Rπ_* Rb_! R(rbImm)_! K ≅
Rg'_* R(rbImm)_! K` (proper base change along `j_W`, [Stacks, Tag 0DDE]), which is `Rg_! K`
computed through the compactification `X̄ ×_W̄ W`, hence through `j_g` ([Stacks, Tag 0F7I]). -/
def lerayComplexQIso :
    lerayComplex B ℓ g fW jW jX R ⋙ DerivedCategory.Plus.Q ≅
      LAdicSheaf.torsionLowerShriek B ℓ g jg :=
  let j := jW.immersion
  let M := lerayResolution B ℓ g fW jW jX R
  let πc := (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jX.toBase)
  let res := etaleModuleRestriction.{u, 0} ℤ_[ℓ] j
  haveI : res.PreservesHomology := Functor.preservesHomologyOfExact _
  haveI := fun X => isIso_mapCochainComplexPlusDerivedUnit_app_of_preservesHomology res X
  haveI : IsIso (Functor.mapCochainComplexPlusDerivedUnit res) := NatIso.isIso_of_isIso_app _
  haveI hπ : ∀ K, IsIso ((Functor.mapCochainComplexPlusDerivedUnit πc).app (M.obj K)) := fun K =>
    isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic πc (M.obj K)
      fun n => by
        have : Injective ((M.obj K).obj.X n) := hR _ n
        exact Functor.rightAcyclic_of_injective _ _
  haveI : IsIso (Functor.whiskerLeft M (Functor.mapCochainComplexPlusDerivedUnit πc)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hπ
  let LP : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤ (isTorsionPlus.{u, 0} ℤ_[ℓ]
      (CompactificationOf.restrictBase jW jX).space).FullSubcategory :=
    ObjectProperty.lift _ (lerayRestrictedExtension B ℓ g fW jW jX)
      (isTorsionPlus_lerayRestrictedExtension B ℓ g fW jW jX)
  let LU : (IsLPowerTorsion ℓ U.1).FullSubcategory ⥤
      (isTorsionPlus.{u, 0} ℤ_[ℓ] U.1).FullSubcategory :=
    ObjectProperty.lift _ ((IsLPowerTorsion ℓ U.1).ι ⋙ singlePlus _ ⋙ DerivedCategory.Plus.Q)
      (isTorsionPlus_singlePlus B ℓ)
  let T₁ := Functor.isoWhiskerLeft (M ⋙ πc.mapCochainComplexPlus)
    (asIso (Functor.mapCochainComplexPlusDerivedUnit res))
  let T₂ := Functor.isoWhiskerRight (asIso (Functor.whiskerLeft M
    (Functor.mapCochainComplexPlusDerivedUnit πc))) res.rightDerivedFunctorPlus
  let T₃ := Functor.isoWhiskerRight (lerayResolutionQIso B ℓ g fW jW jX R α hα)
    (πc.rightDerivedFunctorPlus ⋙ res.rightDerivedFunctorPlus)
  let T₇ := Functor.isoWhiskerLeft LP (etaleModuleDerivedDirectImageIsoRestrictionOfIsProper ℤ_[ℓ]
    jX.toBase j (CompactificationOf.restrictBaseι jW jX)
      (CompactificationOf.restrictBase jW jX).toBase
      (IsPullback.of_hasPullback jX.toBase j)).symm
  let T₈ := Functor.isoWhiskerLeft LU (derivedLowerShriekCompactificationIso (B.inclusion.map g)
    (CompactificationOf.restrictBase jW jX) jg ℤ_[ℓ])
  NatIso.ofComponents (fun K => T₁.app K ≪≫ T₂.app K ≪≫ T₃.app K ≪≫ T₇.app K ≪≫ T₈.app K)
    fun f => (T₁ ≪≫ T₂ ≪≫ T₃ ≪≫ T₇ ≪≫ T₈).hom.naturality f

end Derived

end Leray

section Discharge

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime] {U W : B.Scheme} [IsNoetherian U.1]
  [IsNoetherian W.1] (g : U ⟶ W) [LocallyOfFiniteType (B.inclusion.map g)]
  [QuasiCompact (B.inclusion.map g)] [IsSeparated (B.inclusion.map g)]
  (jg : CompactificationOf (Over.mk (B.inclusion.map g))) {k : Type u} [Field k] [Fintype k]
  (fW : W.1 ⟶ Spec (.of k)) (jW : CompactificationOf (Over.mk fW))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **The Leray comparison with Frobenius** ([Stacks, Tags 0F7J, 0F7L]): for `g : U ⟶ W`
separated of finite type between noetherian schemes, any compactification `j_W` of `W` over a
finite field `k` and any extension `k̄` of `k`, there are a compactification `j_U` of `U` over
`k`, a functorial complex `C(K)` computing `Rg_! K` for ℓ-power torsion sheaves `K` on `U`, and a
natural isomorphism `RΓ_c(U_k̄, K) ≅ RΓ_c(W_k̄, C(K))` commuting with the canonical geometric
Frobenius. `j_U` comes from Nagata's theorem ([Stacks, Tag 0F41]) and `C` from functorial injective
resolutions ([Stacks, Tags 0139, 0141]). -/
theorem LAdicSheaf.lerayFrobeniusComparison :
    LAdicSheaf.LerayFrobeniusComparison B ℓ g jg fW jW kbar p q hcard := by
  have : CompactSpace (B.inclusion.obj U) := (inferInstance : CompactSpace U.1)
  have : CompactSpace (B.inclusion.obj W) := (inferInstance : CompactSpace W.1)
  have : QuasiSeparatedSpace (B.inclusion.obj W) :=
    @IsLocallyNoetherian.quasiSeparatedSpace W.1 IsNoetherian.toIsLocallyNoetherian
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion (B.inclusion.map g) fW jW
  obtain ⟨J, η, hη⟩ := StacksDraft.DerivedSectionsComparison.exists_injectiveEmbeddingData _
    (Stacks.Injectives.FunctorialEmbedding.hasFunctorialInjectiveEmbeddings
      (EtaleModules.{u, 0} ℤ_[ℓ] jX.space))
  obtain ⟨F, α, hα⟩ :=
    (CochainComplex.Plus.exists_functorial_injective_resolution_and_exists_resolutionFunctor _).1
      J η hη
  have hα' : ∀ K, QuasiIso (α.app K).hom := fun K => hα K
  have hR : ∀ K n, Injective (((F ⋙ (InjectiveObject.ι _).mapCochainComplexPlus).obj K).obj.X n) :=
    fun K n => ((F.obj K).obj.X n).property
  exact ⟨CompactificationOf.compOver jW jX, lerayComplex B ℓ g fW jW jX _,
    lerayComplexQIso B ℓ g fW jW jX _ α hα' hR jg,
    lerayFrobeniusIso B ℓ g fW jW kbar jX _ α hα' hR
      (quasiIso_lerayCounit B ℓ g fW jW jX _ α hα' hR),
    lerayFrobeniusIso_hom_frobenius B ℓ g fW jW kbar jX _ α p q hcard hα' hR
      (quasiIso_lerayCounit B ℓ g fW jW jX _ α hα' hR)⟩

end Discharge

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Leray weight implication for `Rʳ g_! G`** (Weil II 3.3; the Leray step of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), with the Leray comparison with Frobenius
discharged (`Stacks.EtaleCohomology.LAdicSheaf.lerayFrobeniusComparison`): it rests only on the
constructibility of `Rᵠ g_!` (Tag 0GL0) and the finiteness of compactly supported cohomology
(Tag 03V3). -/
theorem LAdicSheaf.lerayWeightInput_higherDirectImageShriekFamily_of_constructibility
    (hT : LowerShriekConstructibilityInput B)
    (hfin : LAdicSheaf.FiniteCompactSupportCohomologyInput B ℓ)
    (hfinT : LAdicSheaf.TorsionCompactSupportFinitenessInput B ℓ) :
    LAdicSheaf.LerayWeightInput (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
  LAdicSheaf.lerayWeightInput_higherDirectImageShriekFamily B ℓ
    (fun _ _ _ kbar _ _ _ p q _ _ hcard _ _ _ _ _ g _ _ _ jg fW _ _ _ jW =>
      LAdicSheaf.lerayFrobeniusComparison B ℓ g jg fW jW kbar p q hcard) hT hfin hfinT

end Stacks.EtaleCohomology

end
