module

public import StacksFrontier.Algebra.Category.Grp.CountableCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Homology.DerivedCategory.CountablePerfectHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableSectionsEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Countable `Ext` groups over the quasi-compact quasi-separated étale objects of a space

The clause of Stacks 0CRU on the groups `Ext^i(E|_U, K|_U)`, with nothing assumed beyond the
source's hypotheses: `K ∈ D_QCoh(𝒪_X)` has countable sections of its cohomology sheaves over the
affine charts and `E` is perfect. The conditional form, which carries the reduction of `Ext` to
cohomology, the affine case and the Mayer–Vietoris triangles as hypotheses, is
`AlgebraicGeometry.Space.countable_ext_of_qcqs_etale`.

The induction of Stacks 08GP is run directly on the groups `Ext^n(E|_Y, K|_Y)`:

* `countable_hom_shift_etaleRestrict_of_isAffineSpace` is the affine case. On an affine `Y`,
  `Ext^n(E|_Y, K|_Y) = Hom_{D(R)}(RΓ(Y, E), RΓ(Y, K)[n])` with `RΓ(Y, E)` perfect and
  `H^j(RΓ(Y, K)) = Γ(Y, H^j(K))` countable (`Stacks.Homology.countable_hom_of_isPerfect`).
* `countable_hom_shift_of_eds` is the Mayer–Vietoris step, from the exact sequence of Stacks 08H9.
* `countable_ext_of_qcqs_etale_of_countable_sections` is the clause itself.

## References

* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AddCommGrpCat (HasCountableCohomology)
open Opposite

universe w u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasDerivedCategory.{w} AddCommGrpCat.{u}]

section Clauses

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- **The middle term of an exact sequence of abelian groups with countable ends is
countable.** -/
theorem countable_of_function_exact {A M N : Type*} [AddCommGroup A] [AddCommGroup M]
    [AddCommGroup N] (f : A →+ M) (g : M →+ N) (h : Function.Exact f g) [Countable A]
    [Countable N] : Countable M := by
  classical
  let s : N → M := fun c => if hc : ∃ m, g m = c then hc.choose else 0
  have hex : ∀ m : M, ∃ a : A, m = s (g m) + f a := by
    intro m
    have hc : ∃ m', g m' = g m := ⟨m, rfl⟩
    have hs : s (g m) = hc.choose := dite_eq_left hc
    obtain ⟨a, ha⟩ := (h (m - hc.choose)).1 (by rw [map_sub, hc.choose_spec, sub_self])
    exact ⟨a, by rw [hs, ha]; abel⟩
  refine Function.Injective.countable (f := fun m : M => (g m, (hex m).choose)) ?_
  intro m m' hmm'
  simp only [Prod.mk.injEq] at hmm'
  calc m = s (g m) + f (hex m).choose := (hex m).choose_spec
    _ = s (g m') + f (hex m').choose := by rw [hmm'.2, hmm'.1]
    _ = m' := (hex m').choose_spec.symm

omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- Countability of `Hom(A, B⟦n⟧)` depends on `A` and `B` only up to isomorphism. -/
theorem countable_hom_shift_of_iso {C : Type*} [Category C] [HasShift C ℤ] {A A' B B' : C}
    (eA : A ≅ A') (eB : B ≅ B') (n : ℤ) (h : Countable (A ⟶ B⟦n⟧)) :
    Countable (A' ⟶ B'⟦n⟧) :=
  Function.Injective.countable (f := fun g => eA.hom ≫ g ≫ (shiftFunctor C n).map eB.inv)
    fun g g' hg => by
      have := congrArg (fun k => eA.inv ≫ k ≫ (shiftFunctor C n).map eB.hom) hg
      simpa [← Functor.map_comp] using this

omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- **Étale restriction of derived categories is functorial**: restricting along `g` and then
along `j` is restricting along `j ≫ g`. -/
def etaleRestrictDerivedCompIso {Z Y X : AlgebraicSpaces B S hS} (j : Z ⟶ Y) (g : Y ⟶ X)
    (hj : IsEtale B S hS j.hom) (hg : IsEtale B S hS g.hom) (hjg : IsEtale B S hS (j ≫ g).hom)
    (A : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj A) ≅
      (etaleModulePullback.{u, u} B S hS (j ≫ g) hjg).mapDerivedCategory.obj A :=
  ((Functor.mapDerivedCategoryComp _ _).app A).symm ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModulePullbackCompIso B S hS j g hj hg hjg)).app A

omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- A module `N` over a ring `R` is the set of morphisms `R ⟶ N`. -/
def moduleCatHomFromRingEquiv {R : Type*} [Ring R] (N : ModuleCat R) :
    (ModuleCat.of R R ⟶ N) ≃ N where
  toFun k := k.hom 1
  invFun x := ModuleCat.ofHom (LinearMap.toSpanSingleton R N x)
  left_inv k := by ext; simp
  right_inv x := by simp

/-- **The sections of a module on an affine represented algebraic space are its sections over
the final chart**: `Γ(M) ≃ Hom_R(R, Γ(M)) ≃ Hom(𝒪, M) ≃ M(h_T)`. -/
def representedAffineSectionsEquiv (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (representedAffineSections B S hS T).obj M ≃ M.val.obj (op (idEtaleChart B S hS T)) :=
  (moduleCatHomFromRingEquiv _).symm.trans
    ((((representedAffineAssociatedAdjunction B S hS T).homEquiv _ _).symm.trans
      (representedAffineAssociatedObjUnitIso B S hS T).homFromEquiv).trans
      (M.unitHomEquiv.trans (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
        (isTerminalIdEtaleChart B S hS T))))

omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- **The sections of a module on an affine represented algebraic space** are countable when its
sections over the final chart are. -/
theorem countable_representedAffineSections_obj (T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (h : Countable (M.val.obj (op (idEtaleChart B S hS T)))) :
    Countable ((representedAffineSections B S hS T).obj M) :=
  (representedAffineSectionsEquiv T M).injective.countable

omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- **The affine case of Stacks 0CRU on a represented affine space.** For an étale
`g : h_T ⟶ X` with `T` affine, `E` perfect and `K ∈ D_QCoh(𝒪_X)` with countable sections of its
cohomology sheaves over the affine étale charts of `X`, the groups `Ext^n(E|_T, K|_T)` are
countable. -/
theorem countable_hom_shift_etaleRestrict_yoneda (X Y : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hY : Y = schemeSpace T) (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (E K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) (hKq : QcohDerived B S hS X K)
    (hK : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V → ∀ j : ℤ,
      Countable (((DerivedCategory.homologyFunctor _ j).obj K).val.obj (op V))) (n : ℤ) :
    Countable ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E ⟶
      ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj K)⟦n⟧) := by
  subst hY
  have := etaleModulePullback_additive B S hS g hg
  have := preservesFiniteLimits_etaleModulePullback B S hS g hg
  have := preservesFiniteColimits_etaleModulePullback B S hS g hg
  let E' := (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E
  let K' := (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj K
  have hE' := isPerfect_etaleRestrict B S hS g hg E hE
  have hE'q := qcohDerived_of_isPerfect _ _ _ _ E' hE'
  have hK'q := derivedQuasicoherent_etaleModulePullback B S hS g hg K hKq
  have hLq : QcohDerived B S hS _ (K'⟦n⟧) := qcohDerived_shift K' n hK'q
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS T E' hE'q
  let adj := representedAffineDerivedAdjunction B S hS T
  let RΓ := representedAffineDerivedSections B S hS T
  let e : (E' ⟶ K'⟦n⟧) ≃ (RΓ.obj E' ⟶ RΓ.obj (K'⟦n⟧)) :=
    (asIso (adj.counit.app E')).homFromEquiv.symm.trans (adj.homEquiv _ _)
  have hN : Stacks.Homology.HasCountableHomology (RΓ.obj (K'⟦n⟧)) := fun j => by
    let eH := representedAffineDerivedSectionsHomologyIso B S hS T (K'⟦n⟧) hLq j
    let M := (DerivedCategory.homologyFunctor _ j).obj (K'⟦n⟧)
    have hM : Countable (M.val.obj (op (idEtaleChart B S hS T))) := by
      let e₁ := ((DerivedCategory.homologyFunctor _ 0).shiftIso n j (n + j) rfl).app K' ≪≫
        ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryHomologyIso (n + j)).app K
      have := hK ((smallEtalePostcomp B S hS g hg).obj (idEtaleChart B S hS T))
        (show IsAffine ((BigFppfOver.toScheme B S hS).obj T) from inferInstance) (n + j)
      exact @Function.Injective.countable _ _ this _
        ((PresheafOfModules.evaluation _ (op (idEtaleChart B S hS T))).mapIso
          ((SheafOfModules.forget _).mapIso e₁)).toLinearEquiv.injective
    exact @Function.Injective.countable _ _ (countable_representedAffineSections_obj T M hM) _
      eH.toLinearEquiv.injective
  have := Stacks.Homology.countable_hom_of_isPerfect
    (isPerfect_representedAffineDerivedSections_obj B S hS T E' hE') hN
  exact e.injective.countable

end Clauses

section Unconditional

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback



omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- **The affine case of Stacks 0CRU.** For an étale `g : Y ⟶ X` from an affine algebraic space,
`E` perfect and `K ∈ D_QCoh(𝒪_X)` with countable sections of its cohomology sheaves over the
affine étale charts of `X`, the groups `Ext^n(E|_Y, K|_Y)` are countable. -/
theorem countable_hom_shift_etaleRestrict_of_isAffineSpace (X Y : AlgebraicSpaces B S hS)
    (hYa : IsAffineSpace B S hS Y.1) (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (E K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) (hKq : QcohDerived B S hS X K)
    (hK : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V → ∀ j : ℤ,
      Countable (((DerivedCategory.homologyFunctor _ j).obj K).val.obj (op V))) (n : ℤ) :
    Countable ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E ⟶
      ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj K)⟦n⟧) := by
  obtain ⟨T, hT, ⟨i₀⟩⟩ := hYa
  obtain ⟨Y', hY'⟩ : ∃ Y' : AlgebraicSpaces B S hS,
      Y' = ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ := ⟨_, rfl⟩
  let i : Y.obj ≅ Y'.obj := i₀ ≪≫ eqToIso (by rw [hY'])
  let e : Y ≅ Y' := ObjectProperty.isoMk _ i
  have he₁ : IsEtale B S hS e.hom.hom := isEtale_of_isIso B S hS i.hom
  have he₂ : IsEtale B S hS e.inv.hom := isEtale_of_isIso B S hS i.inv
  have hg' : IsEtale B S hS (e.inv ≫ g).hom := isEtale_comp B S hS he₂ hg
  have hid : IsEtale B S hS (𝟙 Y : Y ⟶ Y).hom := isEtale_of_isIso B S hS (𝟙 Y.1)
  have he : IsEtale B S hS (e.hom ≫ e.inv).hom := isEtale_comp B S hS he₁ he₂
  let G := (etaleModulePullback.{u, u} B S hS e.inv he₂).mapDerivedCategory
  let F := (etaleModulePullback.{u, u} B S hS e.hom he₁).mapDerivedCategory
  let hGF : G ⋙ F ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryComp _ _).symm ≪≫
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
        (etaleModulePullbackCompIso B S hS e.hom e.inv he₁ he₂ he ≪≫
          etaleModulePullbackCongr B S hS he hid e.hom_inv_id ≪≫
          etaleModulePullbackIdIso B S hS hid) ≪≫
      Functor.mapDerivedCategoryIdIso _
  have : G.Faithful := Functor.Faithful.of_comp_iso hGF
  have hc := countable_hom_shift_etaleRestrict_yoneda X Y' T hY' (e.inv ≫ g) hg' E K hE hKq hK n
  have hc' := countable_hom_shift_of_iso
    (etaleRestrictDerivedCompIso e.inv g he₂ hg hg' E).symm
    (etaleRestrictDerivedCompIso e.inv g he₂ hg hg' K).symm n hc
  have hc'' : Countable (G.obj ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E) ⟶
      G.obj (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj K)⟦n⟧)) :=
    @Function.Injective.countable _ _ hc' (fun k => k ≫ (G.commShiftIso n).hom.app _)
      fun k k' hk => by simpa using congrArg (· ≫ (G.commShiftIso n).inv.app _) hk
  exact Function.Injective.countable (f := fun k => G.map k) G.map_injective

omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- **The Mayer–Vietoris step of Stacks 0CRU.** For an elementary distinguished square
`(U ⊆ W, V ⟶ W)` with intersection `P`, if `Ext^n(E|_Y, F|_Y)` is countable for every `n` at
`Y = U`, `V` and `P`, then `Ext^n(E, F)` is countable for every `n`: this is the exactness of the
Mayer–Vietoris sequence of Stacks 08H9 at its first term. -/
theorem countable_hom_shift_of_eds {W : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor W.1} {f : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 U f)
    (E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : ∀ n : ℤ, Countable ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
      ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧))
    (hV : ∀ n : ℤ, Countable ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
      ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧))
    (hP : ∀ n : ℤ, Countable ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
      ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)) (n : ℤ) :
    Countable (E ⟶ F⟦n⟧) := by
  obtain ⟨restriction, difference, boundary, hex⟩ :=
    exists_mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek B S hS hsq E F
  have key : ∀ m : ℤ, Countable (E ⟶ F⟦m + 1⟧) := fun m => by
    have := hP m
    have := hU (m + 1)
    have := hV (m + 1)
    exact countable_of_function_exact (boundary m) (restriction (m + 1)) (hex m).2.2
  simpa using key (n - 1)

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
omit [HasDerivedCategory.{w} AddCommGrpCat.{u}] in
/-- **Stacks 0CRU, the clause on `Ext^i(E|_U, K|_U)`.** Let `X` be a quasi-compact
quasi-separated algebraic space over `S` and let `K` be an object of `D_QCoh(𝒪_X)` whose
cohomology sheaves `H^i(K)` have countable sets of sections over the affine schemes étale over
`X`. Then for every quasi-compact quasi-separated étale `U ⟶ X` and every perfect object `E` of
`D(𝒪_X)` the sets `Ext^i(E|_U, K|_U)` are countable.

The proof is the source's: by the induction principle of Stacks 08GP it suffices to treat an
affine `U`, where `Ext^i(E|_U, K|_U) = Hom_{D(R)}(RΓ(U, E), RΓ(U, K)[i])` with `RΓ(U, E)` a
perfect complex of `R`-modules and `H^j(RΓ(U, K)) = Γ(U, H^j(K))` countable, and the
Mayer–Vietoris step, which is the long exact sequence of Stacks 08H9. -/
theorem countable_ext_of_qcqs_etale_of_countable_sections (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.obj)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.obj)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X.obj X.property)
    (hK : ∀ V : SmallEtale B S hS X.obj, IsAffineChart B S hS X.obj V → ∀ i : ℤ,
      Countable (((DerivedCategory.homologyFunctor _ i).obj K.obj).val.obj (op V)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.obj X.property))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.obj X.property) E)
    (U : SpacesEtale B S hS X)
    (hUqc : IsQuasiCompactSpace B S hS U.obj.left.obj)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.obj.left.obj) (i : ℤ) :
    Countable (DerivedCategory.Ext
      ((etaleModulePullback.{u, u} B S hS (Y := X) U.obj.hom U.property).mapDerivedCategory.obj E)
      ((etaleModulePullback.{u, u} B S hS (Y := X) U.obj.hom U.property).mapDerivedCategory.obj
        K.obj) i) := by
  let Pred : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X.obj) → Prop := fun Y g =>
    ∀ (hY : IsAlgebraicSpace B S hS Y) (hg : IsEtale B S hS g) (n : ℤ),
      let := etaleModulePullback_additive.{u, u} B S hS
        (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) hg
      let := preservesFiniteLimits_etaleModulePullback B S hS
        (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) hg
      let := preservesFiniteColimits_etaleModulePullback B S hS
        (ObjectProperty.homMk g : (⟨Y, hY⟩ : AlgebraicSpaces B S hS) ⟶ X) hg
      Countable ((etaleModulePullback.{u, u} B S hS (X := ⟨Y, hY⟩) (Y := X)
          (ObjectProperty.homMk g) hg).mapDerivedCategory.obj E ⟶
        ((etaleModulePullback.{u, u} B S hS (X := ⟨Y, hY⟩) (Y := X)
          (ObjectProperty.homMk g) hg).mapDerivedCategory.obj K.obj)⟦n⟧)
  have tr : ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g g' : Y ⟶ X.obj}, g = g' →
      Pred Y g → Pred Y g' := by
    rintro _ _ _ rfl h
    exact h
  refine qcqs_induction_on B S hS B.contains_terminal X hXqc hXqs Pred
    (fun V hV hY hg n => countable_hom_shift_etaleRestrict_of_isAffineSpace X ⟨_, hY⟩ hV _ hg
      E K.obj hE K.property hK n) ?_ U hUqc hUqs U.obj.left.property U.property i
  intro W V Uo f hcomm hsq _ _ _ _ hU hV hP hY hg n
  let W' : AlgebraicSpaces B S hS := ⟨W.obj.left.obj, hY⟩
  let gW : W' ⟶ X := ObjectProperty.homMk W.obj.hom.hom
  have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 Uo f := hsq
  have hUW : IsEtale B S hS (edsOpenHom B S hS hsq' ≫ gW).hom :=
    isEtale_comp B S hS (isEtale_edsOpenHom B S hS hsq') hg
  have hVW : IsEtale B S hS (edsEtaleHom B S hS hsq' ≫ gW).hom :=
    isEtale_comp B S hS (isEtale_edsEtaleHom B S hS hsq') hg
  have hPW : IsEtale B S hS (edsInterHom B S hS hsq' ≫ gW).hom :=
    isEtale_comp B S hS (isEtale_edsInterHom B S hS hsq') hg
  refine countable_hom_shift_of_eds hsq' _ _ (fun m => ?_) (fun m => ?_) (fun m => ?_) n
  · exact countable_hom_shift_of_iso
      (etaleRestrictDerivedCompIso (edsOpenHom B S hS hsq') gW _ hg hUW E).symm
      (etaleRestrictDerivedCompIso (edsOpenHom B S hS hsq') gW _ hg hUW K.obj).symm m
      (hU (edsOpen B S hS hsq').2 hUW m)
  · exact countable_hom_shift_of_iso
      (etaleRestrictDerivedCompIso (edsEtaleHom B S hS hsq') gW _ hg hVW E).symm
      (etaleRestrictDerivedCompIso (edsEtaleHom B S hS hsq') gW _ hg hVW K.obj).symm m
      (tr hcomm.symm hV (edsEtale B S hS hsq').2 hVW m)
  · exact countable_hom_shift_of_iso
      (etaleRestrictDerivedCompIso (edsInterHom B S hS hsq') gW _ hg hPW E).symm
      (etaleRestrictDerivedCompIso (edsInterHom B S hS hsq') gW _ hg hPW K.obj).symm m
      (tr (Category.assoc _ _ _).symm hP (edsInter B S hS hsq').2 hPW m)

end Unconditional

end AlgebraicGeometry.Space

end
