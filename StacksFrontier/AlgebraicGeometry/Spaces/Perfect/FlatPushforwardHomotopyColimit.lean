module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.General
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NoetherianMorphismModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionPostnikov
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DistinguishedTrianglesGeneral

/-!
# The direct image of the structure sheaf along a flat morphism is a homotopy colimit of perfects

Let `A` be a ring and `f : U ⟶ X` a flat morphism of algebraic spaces of finite presentation
over `A`. Then `Rf_*𝒪_U = hocolim Eₙ` for a system of perfect objects `Eₙ` of `D(𝒪_X)`. This is
the step of the proof of Stacks 0CRW which writes `Rf_*𝒪_U` as a homotopy colimit.

Write `A` as a filtered colimit of rings `A₀` of finite type over `ℤ`; then `f` is the base
change of a flat morphism `f₀ : U₀ ⟶ X₀` of algebraic spaces of finite presentation over some
`A₀` (`AlgebraicGeometry.Space.exists_finiteType_model_hom`). As `A₀` is countable, the
structure sheaves of `X₀` and `U₀` have countable sections over affine étale charts, and for
every perfect `E` on `X₀` the groups `Hom(E[m], Rf₀_*𝒪_{U₀}) = Hom(Lf₀^*E[m], 𝒪_{U₀})` are
countable by Stacks 0CRU; by the cell tower of Stacks 0CRV, `Rf₀_*𝒪_{U₀}` is a homotopy colimit
of perfect objects. Its derived pullback to `X` is `Rf_*𝒪_U` by Tor independent base change
(Stacks 08IR), and derived pullback preserves perfect objects and homotopy colimits.

## Main results

* `AlgebraicGeometry.Space.exists_isHomotopyColimit_isPerfect_derivedPushforward_of_isFlat`.

## References

* [Stacks Project, Tag 0CRW](https://stacks.math.columbia.edu/tag/0CRW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-! ### Countability over a ring of finite type over `ℤ` -/

/-- An algebra of finite type over a countable ring is countable. -/
theorem countable_of_finiteType (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Countable R] : Countable S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹_›
  have : Countable (MvPolynomial (Fin n) R) :=
    Function.Injective.countable (f := AddMonoidAlgebra.coeff)
      fun a b h => by cases a; cases b; simp_all
  exact hf.countable

variable {B : BigFppfSite.{u}}

/-- **The structure sheaf of an algebraic space locally of finite type over a countable ring has
countable sections over the affine étale charts**: such a chart is the spectrum of an algebra of
finite type over the ring. -/
theorem countable_ringSheaf_obj_of_countable {A₀ : Type u} [CommRing A₀] [Countable A₀]
    {hA₀ : B.Contains (Spec (.of A₀))} (Y : AlgebraicSpaces B (Spec (.of A₀)) hA₀)
    (p : Y.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA₀))))
    (hp : IsLocallyOfFinitePresentation B (Spec (.of A₀)) hA₀ p)
    (V : SmallEtale B (Spec (.of A₀)) hA₀ Y.1) (hV : IsAffineChart B (Spec (.of A₀)) hA₀ Y.1 V) :
    Countable (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A₀)) hA₀ Y.1 Y.2).O)).obj.obj
      (op V)) := by
  let W := (SmallEtale.toOver B (Spec (.of A₀)) hA₀ Y.1).obj V
  have hlfp : LocallyOfFinitePresentation (B.inclusion.map W.hom) :=
    holdsOnEveryEtaleChart_structure_chart B _ p hp _
      (presheaf_etale_of_isEtale B (Spec (.of A₀)) hA₀
        (isEtale_chartToSpace B (Spec (.of A₀)) hA₀ Y V))
  have : IsAffine (B.inclusion.obj W.left) := hV
  have : IsAffine (B.inclusion.obj (B.obj hA₀)) := inferInstanceAs (IsAffine (Spec (.of A₀)))
  have : Countable Γ(B.inclusion.obj (B.obj hA₀), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A₀)).commRingCatIsoToRingEquiv.toEquiv.injective.countable
  let := (B.inclusion.map W.hom).appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(B.inclusion.obj (B.obj hA₀), ⊤) Γ(B.inclusion.obj W.left, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).1 inferInstance
  exact countable_of_finiteType Γ(B.inclusion.obj (B.obj hA₀), ⊤) Γ(B.inclusion.obj W.left, ⊤)

variable {S : Scheme.{u}} {hS : B.Contains S}

/-- **The cohomology sheaves of `𝒪_X[0]` have countable sections over the affine étale charts**
when `𝒪_X` does. -/
theorem countable_homology_structureModule_sections (X : AlgebraicSpaces B S hS)
    (hO : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      Countable (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op V)))
    (V : SmallEtale B S hS X.1) (hV : IsAffineChart B S hS X.1 V) (i : ℤ) :
    Countable (((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))).val.obj (op V)) := by
  by_cases hi : i = 0
  · subst hi
    have h : Countable ((structureModule X).val.obj (op V)) := hO V hV
    exact @Function.Injective.countable _ _ h _
      ((PresheafOfModules.evaluation _ (op V)).mapIso ((SheafOfModules.forget _).mapIso
        (homologyUnitIso (X := X.1) (hX := X.2)))).toLinearEquiv.injective
  · have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.singleFunctor _ 0).obj (structureModule X))) := by
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    exact @Subsingleton.to_countable _ (ModuleCat.subsingleton_of_isZero
      (((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op V)).map_isZero hz)))

/-- **Stacks 0CRU for `Rf_*𝒪_U`.** If `U` is quasi-compact and quasi-separated with structure
sheaf countable over affine étale charts, then for every morphism `f : U ⟶ X` and every perfect
`E` on `X` the groups `Hom(E[m], Rf_*𝒪_U) = Hom(Lf^*(E[m]), 𝒪_U)` are countable. -/
theorem countable_hom_derivedPushforward_structureDerived {X U : AlgebraicSpaces B S hS}
    (f : U ⟶ X) (hUqc : IsQuasiCompactSpace B S hS U.obj)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.obj)
    (hO : ∀ V : SmallEtale B S hS U.1, IsAffineChart B S hS U.1 V →
      Countable (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O)).obj.obj (op V)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.obj X.property))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.obj X.property) E) (m : ℤ) :
    Countable (E⟦m⟧ ⟶ (derivedModulePushforward B S hS f).obj (structureDerived U)) := by
  have hP := isPerfect_smallEtaleDerivedModulePullback f _
    (RingedSite.isPerfect_shift_general (smallEtaleRingedSite B S hS X.obj X.property) hE m)
  have hc := countable_hom_shift_of_countable_sections U hUqc hUqs (unitQuasicoherent U.2)
    (countable_homology_structureModule_sections U hO) _ hP 0
  have hc' : Countable ((smallEtaleDerivedModulePullback B S hS f).obj (E⟦m⟧) ⟶
      structureDerived U) :=
    @Function.Injective.countable _ _ hc
      (fun k => ((shiftFunctorZero _ ℤ).app _).hom ≫ k) fun k k' hk =>
        (((shiftFunctorZero _ ℤ).app _).cancel_iso_hom_left _ _).1 hk
  exact @Function.Injective.countable _ _ hc' _
    ((smallEtaleDerivedModuleAdjunction B S hS f).homEquiv _ _).symm.injective

/-- **`Rf_*𝒪_U` is a homotopy colimit of perfect objects over a countable base.** Let
`f : U ⟶ X` be a quasi-compact quasi-separated morphism of quasi-compact quasi-separated algebraic
spaces whose structure sheaves have countable sections over the affine étale charts. Then
`Rf_*𝒪_U` is a homotopy colimit of perfect objects of `D(𝒪_X)` (Stacks 0CRV and 0CRU). -/
theorem exists_isHomotopyColimit_isPerfect_derivedPushforward_of_countable
    {X U : AlgebraicSpaces B S hS} (f : U ⟶ X) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hXqc : IsQuasiCompactSpace B S hS X.obj)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.obj)
    (hUqc : IsQuasiCompactSpace B S hS U.obj)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.obj)
    (hOX : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      Countable (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op V)))
    (hOU : ∀ V : SmallEtale B S hS U.1, IsAffineChart B S hS U.1 V →
      Countable (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS U.1 U.2).O)).obj.obj (op V))) :
    ∃ F : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (F.obj n)) ∧
        IsHomotopyColimit F ((derivedModulePushforward B S hS f).obj (structureDerived U)) :=
  exists_isHomotopyColimit_isPerfect_of_countable_hom X hXqc hXqs hOX
    ⟨_, qcohDerived_derivedModulePushforward_obj B S hS f hfqc hfqs _
      (qcohDerived_singleFunctor_structureModule (X := U.1) (hX := U.2))⟩
    fun E hE m => countable_hom_derivedPushforward_structureDerived f hUqc hUqs hOU E hE m

/-! ### Transport along a restriction to a smaller base -/

section Transport

variable {T : Scheme.{u}} {hT : B.Contains T} (g : B.obj hT ⟶ B.obj hS)

open DerivedChow

/-- **Homotopy colimits of perfect objects along a restriction.** Let `f₀ : U₀ ⟶ X₀` be a flat,
quasi-compact and quasi-separated morphism of algebraic spaces over `S`, and `f : U ⟶ X` a
morphism of algebraic spaces over `T` identified with the restriction `R f₀` along
`g : T ⟶ S`. If `Rf₀_*𝒪_{U₀}` is a homotopy colimit of perfect objects, so is `Rf_*𝒪_U`: its
image under `L κ^*` for `κ : Λ R X₀ ⟶ X₀` is `R(Λ R f₀)_*𝒪` by Tor independent base change
(Stacks 08IR), the relocalization carries this to `R(R f₀)_*𝒪`, and the identification of `f`
with `R f₀` is an étale base change. Each step preserves perfect objects and homotopy
colimits. -/
theorem exists_isHomotopyColimit_isPerfect_derivedPushforward_of_restrict
    {X₀ U₀ : AlgebraicSpaces B S hS} (f₀ : U₀ ⟶ X₀) (hf₀ : IsFlat B S hS f₀.hom)
    (hqc : IsQuasiCompact B S hS f₀.hom) (hqs : IsQuasiSeparated B S hS f₀.hom)
    {X U : AlgebraicSpaces B T hT} (f : U ⟶ X) (θX : X ⟶ relocalizeRestrictSpace g X₀)
    (θU : U ⟶ relocalizeRestrictSpace g U₀) [IsIso θX] [IsIso θU]
    (hθ : θU ≫ restrictHom g f₀ = f ≫ θX)
    (F₀ : ℕ ⥤ DerivedCategory (Modules.{u, u} B S hS X₀.1 X₀.2))
    (hF₀ : ∀ n, (smallEtaleRingedSite B S hS X₀.1 X₀.2).IsPerfect (F₀.obj n))
    (h : IsHomotopyColimit F₀ ((derivedModulePushforward B S hS f₀).obj (structureDerived U₀))) :
    ∃ F : ℕ ⥤ DerivedCategory (Modules.{u, u} B T hT X.1 X.2),
      (∀ n, (smallEtaleRingedSite B T hT X.1 X.2).IsPerfect (F.obj n)) ∧
        IsHomotopyColimit F ((derivedModulePushforward B T hT f).obj (structureDerived U)) := by
  let κX : relocalizeSpace B hT hS g (relocalizeRestrictSpace g X₀) ⟶ X₀ :=
    ObjectProperty.homMk (OverShriek.relocalizeRestrictCounit g _)
  let κU : relocalizeSpace B hT hS g (relocalizeRestrictSpace g U₀) ⟶ U₀ :=
    ObjectProperty.homMk (OverShriek.relocalizeRestrictCounit g _)
  let Φ₁ : DerivedCategory (Modules.{u, u} B S hS X₀.1 X₀.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS
        (relocalizeSpace B hT hS g (relocalizeRestrictSpace g X₀)).1
        (relocalizeSpace B hT hS g (relocalizeRestrictSpace g X₀)).2) :=
    smallEtaleDerivedModulePullback B S hS κX
  let Φ₂ : DerivedCategory (Modules.{u, u} B S hS
        (relocalizeSpace B hT hS g (relocalizeRestrictSpace g X₀)).1
        (relocalizeSpace B hT hS g (relocalizeRestrictSpace g X₀)).2) ⥤
      DerivedCategory (Modules.{u, u} B T hT (relocalizeRestrictSpace g X₀).1
        (relocalizeRestrictSpace g X₀).2) :=
    relocalizeInverse B hT hS g _ (relocalizeRestrictSpace g X₀).2
  let Φ₃ : DerivedCategory (Modules.{u, u} B T hT (relocalizeRestrictSpace g X₀).1
        (relocalizeRestrictSpace g X₀).2) ⥤
      DerivedCategory (Modules.{u, u} B T hT X.1 X.2) :=
    smallEtaleDerivedModulePullback B T hT θX
  let : Φ₁.CommShift ℤ := commShift_smallEtaleDerivedModulePullback B S hS κX
  have : Φ₁.IsTriangulated := isTriangulated_smallEtaleDerivedModulePullback B S hS κX
  let : Φ₃.CommShift ℤ := commShift_smallEtaleDerivedModulePullback B T hT θX
  have : Φ₃.IsTriangulated := isTriangulated_smallEtaleDerivedModulePullback B T hT θX
  let : Φ₂.CommShift ℤ :=
    inferInstanceAs ((relocalizeInverse B hT hS g _ (relocalizeRestrictSpace g X₀).2).CommShift ℤ)
  have : Φ₂.IsTriangulated :=
    inferInstanceAs (relocalizeInverse B hT hS g _ (relocalizeRestrictSpace g X₀).2).IsTriangulated
  have sqκ : IsPullback κU (relocalizeHom B hT hS g (restrictHom g f₀)) f₀ κX :=
    IsPullback.of_map (ObjectProperty.ι _)
      (ObjectProperty.hom_ext _ (isPullback_relocalize_relocalizeRestrict_map B S hS
        f₀.hom hT g).w)
      (isPullback_relocalize_relocalizeRestrict_map B S hS f₀.hom hT g)
  have sqθ : IsPullback θU f (restrictHom g f₀) θX := IsPullback.of_horiz_isIso ⟨hθ⟩
  -- `L κ^* Rf₀_*𝒪 ≅ R(Λ R f₀)_*𝒪`
  let e₁ : Φ₁.obj ((derivedModulePushforward B S hS f₀).obj (structureDerived U₀)) ≅
      (derivedModulePushforward B S hS (relocalizeHom B hT hS g (restrictHom g f₀))).obj
        (structureDerived _) :=
    @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS _ _ _ _ sqκ.w _)
      (isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS _ _ _ _ sqκ hqc hqs
        (torIndependent_of_isFlat_left f₀ κX hf₀) _
        (qcohDerived_singleFunctor_structureModule (X := U₀.1) (hX := U₀.2))) ≪≫
      (derivedModulePushforward B S hS _).mapIso (smallEtaleDerivedModulePullbackUnitIso κU)
  -- `G R(Λ R f₀)_*𝒪 ≅ R(R f₀)_*𝒪`
  let e₂ : Φ₂.obj ((derivedModulePushforward B S hS
        (relocalizeHom B hT hS g (restrictHom g f₀))).obj (structureDerived _)) ≅
      (derivedModulePushforward B T hT (restrictHom g f₀)).obj (structureDerived _) :=
    ((relocalizeInversePushforwardIso B hT hS g (restrictHom g f₀)).app _).symm ≪≫
      (derivedModulePushforward B T hT _).mapIso (relocalizeInverseUnitIso B hT hS g _ _)
  -- `L θ^* R(R f₀)_*𝒪 ≅ Rf_*𝒪`
  let e₃ : Φ₃.obj ((derivedModulePushforward B T hT (restrictHom g f₀)).obj
        (structureDerived _)) ≅ (derivedModulePushforward B T hT f).obj (structureDerived U) :=
    @asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B T hT _ _ _ _ sqθ.w _)
      (isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B T hT _ _ _ _ sqθ
        (isEtale_of_isIso B T hT _) (Functor.relativelyRepresentable.of_isIso yoneda _) _) ≪≫
      (derivedModulePushforward B T hT _).mapIso (smallEtaleDerivedModulePullbackUnitIso θU)
  have : Φ₁.IsLeftAdjoint := (smallEtaleDerivedModuleAdjunction B S hS κX).isLeftAdjoint
  have : Φ₂.IsLeftAdjoint :=
    (relocalizeInverseEquivalence B hT hS g _
      (relocalizeRestrictSpace g X₀).2).symm.toAdjunction.isLeftAdjoint
  have : Φ₃.IsLeftAdjoint := (smallEtaleDerivedModuleAdjunction B T hT θX).isLeftAdjoint
  refine ⟨((F₀ ⋙ Φ₁) ⋙ Φ₂) ⋙ Φ₃, fun n => ?_, ?_⟩
  · exact isPerfect_smallEtaleDerivedModulePullback θX _
      (isPerfect_relocalizeModulesEquivalence_inverse_mapDerivedCategory_obj B hT hS g _ _ _
        (isPerfect_smallEtaleDerivedModulePullback κX _ (hF₀ n)))
  · exact StacksDraft.BrutalPostnikov.isHomotopyColimit_of_iso
      ((StacksDraft.BrutalPostnikov.isHomotopyColimit_of_iso
        ((StacksDraft.BrutalPostnikov.isHomotopyColimit_of_iso (h.map Φ₁) e₁).map Φ₂) e₂).map Φ₃) e₃

end Transport

/-! ### The direct image of the structure sheaf along a flat morphism -/

open DerivedChow in
/-- **Stacks 0CRW, the homotopy colimit of perfect objects.** Let `A` be a ring and
`f : U ⟶ X` a flat morphism of algebraic spaces of finite presentation over `A`. Then
`Rf_*𝒪_U = hocolim Eₙ` for a system `(Eₙ)` of perfect objects of `D(𝒪_X)`.

By Noetherian approximation `f` is the base change of a flat morphism `f₀ : U₀ ⟶ X₀` of
algebraic spaces of finite presentation over a ring `A₀ ⊆ A` of finite type over `ℤ`
(Stacks 07SK, 08K0); `Rf₀_*𝒪_{U₀}` is a homotopy colimit of perfect objects as `A₀` is
countable (Stacks 0CRV, 0CRU), and its derived pullback to `X` is `Rf_*𝒪_U` (Stacks 08IR). -/
theorem exists_isHomotopyColimit_isPerfect_derivedPushforward_of_isFlat
    (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))
    {U X : AlgebraicSpaces B (Spec (.of A)) hA} (f : U ⟶ X)
    (hX : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA X).hom)
    (hU : IsFinitePresentation B (Spec (.of A)) hA (toBase B (Spec (.of A)) hA U).hom)
    (hf : IsFlat B (Spec (.of A)) hA f.hom) :
    ∃ E : ℕ ⥤ DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X.1 X.2),
      (∀ n, (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).IsPerfect (E.obj n)) ∧
        IsHomotopyColimit E
          ((derivedModulePushforward B (Spec (.of A)) hA f).obj (structureDerived U)) := by
  obtain ⟨A₀, _, _, _, hA₀, X₀', U₀', hX₀, hU₀, pX₀, pU₀, f₀', hpX₀, hpU₀, hfl, hiso⟩ :=
    exists_finiteType_model_hom B X.2 U.2 (toBase B (Spec (.of A)) hA X).hom
      (toBase B (Spec (.of A)) hA U).hom hX hU f.hom
  have : Countable A₀ := countable_of_finiteType ℤ A₀
  let g : B.obj hA ⟶ B.obj hA₀ :=
    B.inclusion.preimage (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))
  obtain ⟨eU, eX, he⟩ := hiso g (B.inclusion.map_preimage _)
  let X₀ : AlgebraicSpaces B (Spec (.of A₀)) hA₀ := ⟨X₀', hX₀⟩
  let U₀ : AlgebraicSpaces B (Spec (.of A₀)) hA₀ := ⟨U₀', hU₀⟩
  let f₀ : U₀ ⟶ X₀ := ObjectProperty.homMk f₀'
  have hZ := BigFppfSite.contains_terminal B
  have hT : IsAbsolutelyQuasiSeparated B (Spec (.of A₀)) hA₀ hZ
      (yoneda.obj (Over.mk (𝟙 (B.obj hA₀)))) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B (Spec (.of A₀)) hA₀ _ hZ
      ⟨_, inferInstanceAs (QuasiSeparatedSpace (Spec (.of A₀))),
        ⟨Functor.RepresentableBy.yoneda _⟩⟩
  have hX₀qc := isQuasiCompactSpace_of_isQuasiCompact_toBase B (Spec (.of A₀)) hA₀ pX₀ hpX₀.2.1
  have hU₀qc := isQuasiCompactSpace_of_isQuasiCompact_toBase B (Spec (.of A₀)) hA₀ pU₀ hpU₀.2.1
  have hX₀qs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A₀)) hA₀ hZ hX₀ hT
    hpX₀.2.2
  have hU₀qs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated B (Spec (.of A₀)) hA₀ hZ hU₀ hT
    hpU₀.2.2
  have hqc : IsQuasiCompact B (Spec (.of A₀)) hA₀ f₀.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B (Spec (.of A₀)) hA₀ hZ hX₀ hX₀qs hU₀qc f₀'
  have hqs : IsQuasiSeparated B (Spec (.of A₀)) hA₀ f₀.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B (Spec (.of A₀)) hA₀ hZ hU₀ hU₀qs f₀'
  obtain ⟨F₀, hF₀, hh⟩ := exists_isHomotopyColimit_isPerfect_derivedPushforward_of_countable f₀
    hqc hqs hX₀qc hX₀qs hU₀qc hU₀qs (countable_ringSheaf_obj_of_countable X₀ pX₀ hpX₀.1)
    (countable_ringSheaf_obj_of_countable U₀ pU₀ hpU₀.1)
  let θX : X ⟶ relocalizeRestrictSpace g X₀ := ObjectProperty.homMk eX.hom
  let θU : U ⟶ relocalizeRestrictSpace g U₀ := ObjectProperty.homMk eU.hom
  exact exists_isHomotopyColimit_isPerfect_derivedPushforward_of_restrict g f₀ (hfl hf) hqc hqs f
    θX θU (ObjectProperty.hom_ext _ he) F₀ hF₀ hh

end AlgebraicGeometry.Space
