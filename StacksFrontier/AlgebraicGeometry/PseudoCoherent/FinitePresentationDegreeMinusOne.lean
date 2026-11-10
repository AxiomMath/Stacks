module

public import Mathlib.Algebra.Homology.Double
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationNextCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finitely presented modules are exactly the `(-1)`-pseudo-coherent ones

Let `X` be a ringed space and let `ℱ` be a sheaf of `𝒪_X`-modules. Stacks 09V9(2) says that `ℱ`,
viewed as an object of the derived category of `𝒪_X`-modules through the degree-zero single
functor, is `(-1)`-pseudo-coherent if and only if `ℱ` is an `𝒪_X`-module of finite presentation.

## Main results

* `HomologicalComplex.isIso_homologyMap_mkHomFromDouble_zero`: a two-term complex `A ⟶ B` in
  degrees `-1` and `0` has the same degree-zero cohomology as the cokernel of `A ⟶ B` placed in
  degree zero.
* `StrictlyPerfect.isDirectSummandOfFiniteFree_free`: a free module on a finite index type is a
  direct summand of a finite free module.
* `StrictlyPerfect.isStrictlyPerfect_double`: a morphism between direct summands of finite free
  modules, placed in degrees `-1` and `0`, is a strictly perfect complex.
* `SheafOfModules.IsFinitePresentation.of_iso`: finite presentation is invariant under
  isomorphism.

In the namespace `AlgebraicGeometry.RingedSpace`:

* `isPseudoCoherentFrom_singleFunctor_zero_neg_one_of_exists_cokernel`: a sheaf of modules which
  is locally the cokernel of a morphism between direct summands of finite free modules is
  `(-1)`-pseudo-coherent in degree zero.
* `isFinitePresentation_of_isPseudoCoherentFrom_singleFunctor_zero_neg_one`: a sheaf of modules
  which is `(-1)`-pseudo-coherent in degree zero is of finite presentation.
* `isPseudoCoherentFrom_singleFunctor_zero_neg_one_of_isFinitePresentation`: a sheaf of modules
  of finite presentation is `(-1)`-pseudo-coherent in degree zero.
* `isPseudoCoherentFrom_singleFunctor_zero_neg_one_iff_isFinitePresentation`: a sheaf of modules
  is `(-1)`-pseudo-coherent in degree zero if and only if it is of finite presentation.

## References

* [The Stacks Project, Lemma 36.60.11 (09V9)](https://stacks.math.columbia.edu/tag/09V9)
* [The Stacks Project, Lemma 20.47.4 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect AlgebraicGeometry

namespace HomologicalComplex

universe v u

/-- **A two-term complex computes the cokernel of its differential in the upper degree.** Let
`f : A ⟶ B` and `g : B ⟶ M` satisfy `f ≫ g = 0` and exhibit `g` as a cokernel of `f`. Place `f` in
degrees `prev 0` and `0`, place `M` in degree zero, and let `α` be the morphism of complexes given
by `g` in degree zero. Then `α` is an isomorphism on cohomology in degree zero. -/
public theorem isIso_homologyMap_mkHomFromDouble_zero {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [CategoryWithHomology C] {A B M : C} (f : A ⟶ B)
    (g : B ⟶ M) (hfg : f ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g hfg)) :
    IsIso (homologyMap
      (mkHomFromDouble (C := C) (c := ComplexShape.up ℤ) (i₀ := (ComplexShape.up ℤ).prev 0)
        (i₁ := 0) (f := f) (by rw [CochainComplex.prev]; simp [ComplexShape.up])
        (by rw [CochainComplex.prev]; omega)
        (K := (single C (ComplexShape.up ℤ) 0).obj M) 0
        (g ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 M).inv)
        (by simp only [zero_comp]; rw [← Category.assoc, hfg, zero_comp])
        (by intro k _hk; simp)) 0) := by
  let c := ComplexShape.up ℤ
  have hrel : c.Rel (c.prev 0) 0 := by
    dsimp [c]
    rw [CochainComplex.prev]
    simp [ComplexShape.up]
  have hne : c.prev 0 ≠ 0 := by
    change (ComplexShape.up ℤ).prev 0 ≠ 0
    rw [CochainComplex.prev]
    omega
  have hnxt : c.next 0 ≠ 0 := by
    change (ComplexShape.up ℤ).next 0 ≠ 0
    rw [CochainComplex.next]
    omega
  let K := double (c := c) (i₀ := c.prev 0) (i₁ := 0) f hrel
  let L := (single C (ComplexShape.up ℤ) 0).obj M
  let α := mkHomFromDouble (c := c) (i₀ := c.prev 0) (i₁ := 0) (f := f) hrel hne (K := L) 0
    (g ≫ (singleObjXSelf c 0 M).inv)
    (by simp only [zero_comp]; rw [← Category.assoc, hfg, zero_comp])
    (by
      intro k _hk
      change (g ≫ (singleObjXSelf c 0 M).inv) ≫ L.d 0 k = 0
      simp [L])
  let e₀ := doubleXIso₀ (c := c) (i₀ := c.prev 0) (i₁ := 0) f hrel
  let e₁ := doubleXIso₁ (c := c) (i₀ := c.prev 0) (i₁ := 0) f hrel hne
  let s₀ := singleObjXSelf c 0 M
  have hdK : K.d (c.prev 0) 0 = e₀.hom ≫ f ≫ e₁.inv := double_d f hrel hne
  have hdiff : K.d (c.prev 0) 0 ≫ e₁.hom = e₀.hom ≫ f := by
    rw [hdK, Category.assoc, Category.assoc, e₁.inv_hom_id, Category.comp_id]
  have hiff : ∀ ⦃W : C⦄ (φ : B ⟶ W),
      f ≫ φ = 0 ↔ K.d (c.prev 0) 0 ≫ e₁.hom ≫ φ = 0 := by
    intro W φ
    have key : K.d (c.prev 0) 0 ≫ e₁.hom ≫ φ = e₀.hom ≫ f ≫ φ :=
      (Category.assoc (K.d (c.prev 0) 0) e₁.hom φ).symm.trans
        (by rw [hdiff]; exact Category.assoc e₀.hom f φ)
    rw [key]
    exact (comp_eq_zero_iff_of_epi e₀.hom).symm
  have hgS : K.d 0 (c.next 0) = 0 := double_d_eq_zero₁ f hrel 0 (c.next 0) hnxt
  have hdL : L.d (c.prev 0) 0 = 0 := by simp [L]
  have hgT : L.d 0 (c.next 0) = 0 := by simp [L]
  have hfgs : f ≫ (g ≫ s₀.inv) = 0 := by rw [← Category.assoc, hfg, zero_comp]
  have hc₀ : IsColimit (CokernelCofork.ofπ (g ≫ s₀.inv) hfgs) :=
    IsCokernel.cokernelIso f (g ≫ s₀.inv) hc s₀.symm (by simp)
  have hc₁ := CokernelCofork.isColimitOfIsColimitOfIff hc₀ (K.d (c.prev 0) 0) e₁ hiff
  have hc₂ := CokernelCofork.IsColimit.ofId (L.d (c.prev 0) 0) hdL
  have hcomm : ((shortComplexFunctor C c 0).map α).τ₂ ≫ 𝟙 (L.X 0) =
      (e₁.hom ≫ g ≫ s₀.inv) ≫ 𝟙 (L.X 0) := by
    change α.f 0 ≫ 𝟙 (L.X 0) = (e₁.hom ≫ g ≫ s₀.inv) ≫ 𝟙 (L.X 0)
    rw [mkHomFromDouble_f₁]
  let γ := ShortComplex.HomologyMapData.ofIsColimitCokernelCofork
    ((shortComplexFunctor C c 0).map α) hgS _ hc₁ hgT _ hc₂ (𝟙 (L.X 0)) hcomm
  change IsIso (ShortComplex.homologyMap ((shortComplexFunctor C c 0).map α))
  rw [γ.left.homologyMap_eq]
  have : IsIso γ.left.φH := inferInstanceAs (IsIso (𝟙 (L.X 0)))
  infer_instance

end HomologicalComplex

namespace CochainComplex

/-- The predecessor of degree `0` in the cochain complex shape on `ℤ` is `-1`. -/
public theorem prev_zero : (ComplexShape.up ℤ).prev 0 = -1 := by
  rw [CochainComplex.prev]; omega

/-- In the cochain complex shape on `ℤ`, the predecessor of degree `0` is related to `0`. -/
public theorem rel_prev_zero : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev 0) 0 := by
  rw [CochainComplex.prev]; simp [ComplexShape.up]

/-- The predecessor of degree `0` in the cochain complex shape on `ℤ` is not `0`. -/
public theorem prev_zero_ne : (ComplexShape.up ℤ).prev 0 ≠ 0 := by
  rw [CochainComplex.prev]; omega

end CochainComplex

namespace StrictlyPerfect

universe u

/-- The free `𝒪_Y`-module on a finite index type is a direct summand of a finite free module. -/
public theorem isDirectSummandOfFiniteFree_free {Y : AlgebraicGeometry.RingedSpace.{u, u}}
    (I : Type u) [Finite I] :
    IsDirectSummandOfFiniteFree (SheafOfModules.free (R := structureSheafOfRings Y) I) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  refine isDirectSummandOfFiniteFree_of_iso
    (((SheafOfModules.freeFunctor (R := structureSheafOfRings Y)).mapIso
        (Equiv.toIso (Equiv.ulift.trans (Fintype.equivFin I).symm))).symm ≪≫
      (finiteFreeIsoFree Y (Fintype.card I)).symm)
    ⟨Fintype.card I, ⟨Retract.refl _⟩⟩

/-- A morphism between direct summands of finite free `𝒪_Y`-modules, placed in degrees
`(ComplexShape.up ℤ).prev 0` and `0`, is a strictly perfect complex. -/
public theorem isStrictlyPerfect_double {Y : AlgebraicGeometry.RingedSpace.{u, u}}
    {A₀ A₁ : OXMod.{u, u} Y} (hA₀ : IsDirectSummandOfFiniteFree A₀)
    (hA₁ : IsDirectSummandOfFiniteFree A₁) (f : A₀ ⟶ A₁)
    (hrel : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev 0) 0)
    (hne : (ComplexShape.up ℤ).prev 0 ≠ 0) :
    IsStrictlyPerfect (HomologicalComplex.double f hrel) where
  bounded := by
    refine Set.Finite.subset ((Set.finite_singleton ((ComplexShape.up ℤ).prev 0)).union
      (Set.finite_singleton (0 : ℤ))) ?_
    intro j hj
    by_cases hj₀ : j = (ComplexShape.up ℤ).prev 0
    · simp [hj₀]
    · by_cases hj₁ : j = 0
      · simp [hj₁]
      · exact absurd (HomologicalComplex.isZero_double_X f hrel j hj₀ hj₁) hj
  directSummand j := by
    by_cases hj₀ : j = (ComplexShape.up ℤ).prev 0
    · subst hj₀
      exact isDirectSummandOfFiniteFree_of_iso (HomologicalComplex.doubleXIso₀ f hrel) hA₀
    · by_cases hj₁ : j = 0
      · subst hj₁
        exact isDirectSummandOfFiniteFree_of_iso (HomologicalComplex.doubleXIso₁ f hrel hne) hA₁
      · exact isDirectSummandOfFiniteFree_of_isZero
          (HomologicalComplex.isZero_double_X f hrel j hj₀ hj₁)

end StrictlyPerfect

namespace SheafOfModules

universe u v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ Y, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules isomorphic to one of finite presentation is of finite presentation. -/
public theorem IsFinitePresentation.of_iso {M N : SheafOfModules.{u} R}
    (h : M.IsFinitePresentation) (e : M ≅ N) : N.IsFinitePresentation := by
  obtain ⟨σ, hσ⟩ := h.exists_quasicoherentData
  exact ⟨σ.ofIsIso e.hom, inferInstance⟩

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- If, near every point of `X`, the restriction of `B` to an open subspace is the cokernel of a
morphism between direct summands of finite free modules, then the complex `B` placed in degree
zero is `(-1)`-pseudo-coherent. -/
public theorem isPseudoCoherentComplexFrom_single_zero_neg_one_of_exists_cokernel
    (B : OXMod.{u, u} X)
    (h : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ A₀ A₁ : OXMod.{u, u} (X.restrict W.isOpenEmbedding),
        IsDirectSummandOfFiniteFree A₀ ∧ IsDirectSummandOfFiniteFree A₁ ∧
          ∃ (f : A₀ ⟶ A₁) (g : A₁ ⟶ (restrictModules X W).obj B) (hfg : f ≫ g = 0),
            Nonempty (IsColimit (CokernelCofork.ofπ g hfg))) :
    IsPseudoCoherentComplexFrom
      ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj B) (-1) := by
  intro x
  obtain ⟨W, hxW, A₀, A₁, hA₀, hA₁, f, g, hfg, ⟨hc⟩⟩ := h x
  let α₀ := HomologicalComplex.mkHomFromDouble (c := ComplexShape.up ℤ)
    (i₀ := (ComplexShape.up ℤ).prev 0) (i₁ := 0) (f := f) CochainComplex.rel_prev_zero
    CochainComplex.prev_zero_ne
    (K := (HomologicalComplex.single (OXMod.{u, u} (X.restrict W.isOpenEmbedding))
      (ComplexShape.up ℤ) 0).obj ((restrictModules X W).obj B)) 0
    (g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      ((restrictModules X W).obj B)).inv)
    (by simp only [zero_comp]; rw [← Category.assoc, hfg, zero_comp])
    (by intro k _hk; simp)
  let eL : restrictComplex
        ((HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj B) W ≅
      (HomologicalComplex.single (OXMod.{u, u} (X.restrict W.isOpenEmbedding))
        (ComplexShape.up ℤ) 0).obj ((restrictModules X W).obj B) :=
    (HomologicalComplex.singleMapHomologicalComplex (restrictModules X W)
      (ComplexShape.up ℤ) 0).app B
  have hLzero : ∀ j : ℤ, j ≠ 0 →
      IsZero ((restrictComplex ((HomologicalComplex.single (OXMod.{u, u} X)
        (ComplexShape.up ℤ) 0).obj B) W).homology j) := fun j hj =>
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
      ((restrictModules X W).obj B) j hj).of_iso (HomologicalComplex.homologyMapIso eL j)
  refine ⟨W, hxW, HomologicalComplex.double f CochainComplex.rel_prev_zero,
    StrictlyPerfect.isStrictlyPerfect_double hA₀ hA₁ f CochainComplex.rel_prev_zero
      CochainComplex.prev_zero_ne,
    α₀ ≫ eL.inv, ?_, ?_⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [HomologicalComplex.homologyMap_comp]
      have h0 : IsIso (HomologicalComplex.homologyMap α₀ 0) :=
        HomologicalComplex.isIso_homologyMap_mkHomFromDouble_zero f g hfg hc
      have h1 : IsIso (HomologicalComplex.homologyMap eL.inv 0) :=
        inferInstanceAs (IsIso (HomologicalComplex.homologyMapIso eL.symm 0).hom)
      infer_instance
    · exact IsZero.isIso (HomologicalComplex.isZero_homology_of_isZero_X _ _
        (HomologicalComplex.isZero_double_X f CochainComplex.rel_prev_zero j
          (by rw [CochainComplex.prev_zero]; omega) hj0)) (hLzero j hj0) _
  · exact (hLzero (-1) (by decide)).epi _

/-- If, near every point of `X`, the restriction of `B` to an open subspace is the cokernel of a
morphism between direct summands of finite free modules, then `B`, viewed in degree zero as an
object of the derived category, is `(-1)`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_singleFunctor_zero_neg_one_of_exists_cokernel
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (B : OXMod.{u, u} X)
    (h : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ A₀ A₁ : OXMod.{u, u} (X.restrict W.isOpenEmbedding),
        IsDirectSummandOfFiniteFree A₀ ∧ IsDirectSummandOfFiniteFree A₁ ∧
          ∃ (f : A₀ ⟶ A₁) (g : A₁ ⟶ (restrictModules X W).obj B) (hfg : f ≫ g = 0),
            Nonempty (IsColimit (CokernelCofork.ofπ g hfg))) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj B) (-1) :=
  ⟨(HomologicalComplex.single (OXMod.{u, u} X) (ComplexShape.up ℤ) 0).obj B,
    isPseudoCoherentComplexFrom_single_zero_neg_one_of_exists_cokernel B h,
    ⟨eqToIso (DerivedCategory.Q_obj_single_obj (OXMod.{u, u} X) 0 B)⟩⟩

/-- A finite presentation of the restriction of an `𝒪_X`-module to the slice `Over W` is a finite
presentation of its restriction to the open subspace `W`. -/
public theorem exists_isFinite_presentation_restrictModules_of_over (M : OXMod.{u, u} X)
    (W : Opens X.carrier) (h : ∃ p : (M.over W).Presentation, p.IsFinite) :
    ∃ p : ((restrictModules X W).obj M).Presentation, p.IsFinite :=
  SheafOfModules.exists_isFinite_presentation_of_iso
    ((restrictModulesIsoOverComp X W).symm.app M).symm
    (SheafOfModules.exists_isFinite_presentation_map
      (W.sheafOfModulesEquivOver (structureSheafOfRings X)).functor (equivOverUnitIso X W) h)

/-- The cohomology of an `𝒪_X`-module viewed in degree zero in the derived category vanishes in
every nonzero degree. -/
public theorem isZero_homology_singleFunctor_zero_of_ne_zero
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (F : OXMod.{u, u} X) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)) := by
  exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 F i hi).of_iso
    (derivedHomologyIso _ i)

/-- An `𝒪_X`-module which is `(-1)`-pseudo-coherent when viewed in degree zero as an object of the
derived category of `𝒪_X`-modules is of finite presentation. -/
@[sga "6 I 2.9" "(ii)⇒(i)"]
public theorem isFinitePresentation_of_isPseudoCoherentFrom_singleFunctor_zero_neg_one
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (F : OXMod.{u, u} X)
    (hF : IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) (-1)) :
    SheafOfModules.IsFinitePresentation (R := structureSheafOfRings X) F := by
  have hH : SheafOfModules.IsFinitePresentation (R := structureSheafOfRings X)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) 0).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)) :=
    isFinitePresentation_homology_of_isPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) (-1) hF
      fun i hi => isZero_homology_singleFunctor_zero_of_ne_zero F i (by omega)
  exact hH.of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso (OXMod.{u, u} X) 0).app F)

/-- An `𝒪_X`-module of finite presentation is `(-1)`-pseudo-coherent when viewed in degree zero as
an object of the derived category of `𝒪_X`-modules. -/
public theorem isPseudoCoherentFrom_singleFunctor_zero_neg_one_of_isFinitePresentation
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (F : OXMod.{u, u} X)
    (hF : SheafOfModules.IsFinitePresentation (R := structureSheafOfRings X) F) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) (-1) := by
  refine isPseudoCoherentFrom_singleFunctor_zero_neg_one_of_exists_cokernel F fun x => ?_
  obtain ⟨σ, hσ⟩ := hF.exists_quasicoherentData
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff X.carrier σ.X).mp σ.coversTop).exists_mem x
  obtain ⟨P, hP⟩ := exists_isFinite_presentation_restrictModules_of_over F (σ.X i)
    ⟨σ.presentation i, hσ.isFinite_presentation i⟩
  have hgen : Finite P.generators.I := hP.isFiniteType_generators.finite
  have hrel : Finite P.relations.I := hP.isFiniteType_relations.finite
  exact ⟨σ.X i, hxi,
    SheafOfModules.free (R := structureSheafOfRings (X.restrict (σ.X i).isOpenEmbedding))
      P.relations.I,
    SheafOfModules.free (R := structureSheafOfRings (X.restrict (σ.X i).isOpenEmbedding))
      P.generators.I,
    StrictlyPerfect.isDirectSummandOfFiniteFree_free _,
    StrictlyPerfect.isDirectSummandOfFiniteFree_free _,
    (SheafOfModules.freeHomEquiv (kernel P.generators.π)).symm P.relations.s ≫
      kernel.ι P.generators.π,
    P.generators.π, by simp, ⟨P.isColimit⟩⟩

/-- Let `X` be a ringed space and let `ℱ` be a sheaf of `𝒪_X`-modules.
Then `ℱ`, viewed in degree zero as an object of the derived category of `𝒪_X`-modules, is
`(-1)`-pseudo-coherent if and only if `ℱ` is an `𝒪_X`-module of finite presentation. -/
@[stacks 09V9 "finite_presentation_iff_minus_one_pseudo_coherent"]
public theorem isPseudoCoherentFrom_singleFunctor_zero_neg_one_iff_isFinitePresentation
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (F : OXMod.{u, u} X) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) (-1) ↔
      SheafOfModules.IsFinitePresentation (R := structureSheafOfRings X) F :=
  ⟨isFinitePresentation_of_isPseudoCoherentFrom_singleFunctor_zero_neg_one F,
    isPseudoCoherentFrom_singleFunctor_zero_neg_one_of_isFinitePresentation F⟩

end AlgebraicGeometry.RingedSpace

end
