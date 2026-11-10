module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Derived
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusPastingHorizontal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedBaseChangePasting

/-!
# The base change map for `Rf_!` attached to a cube of compactifications

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be morphisms with compactifications `j : X ⟶ X̄` and
`j' : X' ⟶ X̄'`, and let `g : Y' ⟶ Y`, `g' : X' ⟶ X` and `φ : X̄' ⟶ X̄` form a commutative cube
whose face through the two open immersions is cartesian. The base change map
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of [Stacks, Tag 0F7L] is defined for such a cube by the recipe of
the source: the base change map `g⁻¹ Rf̄_* ⟶ Rf̄'_* φ⁻¹` followed by the inverse of
`(g')⁻¹ ∘ j'_! ≅ φ⁻¹ ∘ j_!`. For the cube of the base change of `j`
(`AlgebraicGeometry.CompactificationOf.baseChange`) it is
`Stacks.EtaleCohomology.derivedLowerShriekBaseChange`; allowing an arbitrary cube makes the
compatibilities with composition statements about cubes, without comparisons of iterated fibre
products.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCubeIso`:
  `(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹` on `D⁺` for a cartesian square.
* `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube`: the base change map of a cube.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekBaseChange_eq_cube`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedBaseChangePlus

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

section Cube

/-- **Extension by zero commutes with inverse image on `D⁺`**, for an arbitrary cartesian square
`g' ≫ j = j' ≫ φ` with `j` and `j'` étale ([Stacks, Tag 03S6]): `(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹`. -/
def etaleModuleDerivedExtensionByZeroCubeIso {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X}
    {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb} [Etale j] [Etale j']
    (hc : IsPullback g' j' j φ) :
    (etaleModuleInverseImage.{u, 0} Λ g').mapDerivedCategoryPlus ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ j' ≅
      etaleModuleDerivedExtensionByZero.{u, 0} Λ j ⋙
        (etaleModuleInverseImage.{u, 0} Λ φ).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (etaleModuleInverseImage.{u, 0} Λ g') (etaleModuleInverseImage.{u, 0} Λ φ)
    (etaleModuleExtensionByZero.{u, 0} Λ j) (etaleModuleExtensionByZero.{u, 0} Λ j')
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc)
    (fun _ _ => Functor.rightAcyclic_of_exact _ _)

/-- The inverse of `etaleModuleDerivedExtensionByZeroCubeIso` is the base change map of the
inverse of the underived isomorphism. -/
theorem etaleModuleDerivedExtensionByZeroCubeIso_inv {X X' Xb Xb' : Scheme.{u}} {g' : X' ⟶ X}
    {j : X ⟶ Xb} {j' : X' ⟶ Xb'} {φ : Xb' ⟶ Xb} [Etale j] [Etale j']
    (hc : IsPullback g' j' j φ) :
    (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv =
      derivedBaseChangePlus (etaleModuleExtensionByZero.{u, 0} Λ j)
        (etaleModuleExtensionByZero.{u, 0} Λ j') (etaleModuleInverseImage.{u, 0} Λ φ)
        (etaleModuleInverseImage.{u, 0} Λ g')
        (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc).inv :=
  derivedBaseChangePlusIso_inv _ _ _ _ _ _

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- **The base change map `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of a cube of compactifications**
([Stacks, Tag 0F7L]): for compactifications `j` of `f` and `j'` of `f'` and `φ : X̄' ⟶ X̄`
with `j' ≫ φ = g' ≫ j` cartesian and `f̄' ≫ g = φ ≫ f̄`, the base change map
`g⁻¹ Rf̄_* j_! ⟶ Rf̄'_* φ⁻¹ j_!` followed by `Rf̄'_*` of the inverse of
`(g')⁻¹ ∘ j'_! ≅ φ⁻¹ ∘ j_!`. -/
def derivedLowerShriekBaseChangeCube (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (φ : j'.space ⟶ j.space)
    (hc : IsPullback g' j'.immersion j.immersion φ) (w : j'.toBase ≫ g = φ ≫ j.toBase) :
    derivedLowerShriek.{u, 0} f j Λ ⋙ etaleModuleDerivedInverseImagePlus.{u, 0} Λ g ⟶
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ g' ⋙ derivedLowerShriek.{u, 0} f' j' Λ :=
  Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion)
      (etaleModuleDerivedBaseChange.{u, 0} Λ j.toBase j'.toBase g φ w) ≫
    Functor.whiskerRight (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv
      (etaleModuleDerivedDirectImage.{u, 0} Λ j'.toBase)

/-- The base change map of `Stacks.EtaleCohomology.derivedLowerShriekBaseChange` is that of the
cube of the base change of the compactification. -/
theorem derivedLowerShriekBaseChange_eq_cube (sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekBaseChange.{u, 0} Λ sq j =
      derivedLowerShriekBaseChangeCube Λ j (j.baseChange sq) (pullback.fst j.toBase g)
        (j.isPullback_baseChange sq) pullback.condition.symm :=
  rfl

end Cube

/-! ### Vertical composition of base change maps of direct images -/

section VerticalDirectImage

/-- The transport of right derived functors along `F ⋙ G ≅ H` is the invariance comparison of
the isomorphism. -/
theorem rightDerivedFunctorPlusIsoOfCompIso_eq {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E] [EnoughInjectives C] [EnoughInjectives D]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    (e : F ⋙ G ≅ H) :
    rightDerivedFunctorPlusIsoOfCompIso F G H e = Functor.rightDerivedFunctorPlusNatIso e := by
  have : mapHomotopyCategoryPlusIsoOfCompIso F G H e = Functor.mapHomotopyCategoryPlusNatIso e := by
    refine Iso.ext (NatTrans.ext (funext fun K => ?_))
    apply (HomotopyCategory.Plus.ι E).map_injective
    change 𝟙 _ ≫ (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K.obj =
        (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K.obj
    rw [Category.id_comp, Functor.mapHomotopyCategoryCompIso_hom_app_eq]
  rw [rightDerivedFunctorPlusIsoOfCompIso, this]
  rfl

variable {A B C A' B' C' : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (pq : A ⟶ C) (hpq : pq = p ≫ q)
  (p' : A' ⟶ B') (q' : B' ⟶ C') (pq' : A' ⟶ C') (hpq' : pq' = p' ≫ q')
  (φA : A' ⟶ A) (φB : B' ⟶ B) (φC : C' ⟶ C) (wp : p' ≫ φB = φA ≫ p) (wq : q' ≫ φC = φB ≫ q)
  (wpq : pq' ≫ φC = φA ≫ pq)

/-- The pasting of base change maps of `D⁺` direct images, with the composition comparison
`R(p ≫ q)_* ⟶ Rp_* ∘ Rq_*` expanded as the invariance comparison followed by
`Functor.rightDerivedFunctorPlusComp`. -/
private theorem etaleModuleDerivedBaseChange_comp_aux :
    etaleModuleDerivedBaseChange.{u, 0} Λ pq pq' φC φA wpq ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ φA)
          ((Functor.rightDerivedFunctorPlusNatIso
            (etaleModuleDirectImageComp.{u, 0} Λ p' q' pq' hpq')).inv ≫
            Functor.rightDerivedFunctorPlusComp _ _) =
      Functor.whiskerRight ((Functor.rightDerivedFunctorPlusNatIso
            (etaleModuleDirectImageComp.{u, 0} Λ p q pq hpq)).inv ≫
            Functor.rightDerivedFunctorPlusComp _ _)
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ φC) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ p)
          (etaleModuleDerivedBaseChange.{u, 0} Λ q q' φC φB wq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChange.{u, 0} Λ p p' φB φA wp)
          (etaleModuleDerivedDirectImage.{u, 0} Λ q') ≫
        (Functor.associator _ _ _).hom := by
  have d1 := derivedBaseChangePlus_pasteV (etaleModuleBaseChange Λ p p' φB φA wp)
    (etaleModuleBaseChange Λ q q' φC φB wq)
  have d3 := derivedBaseChangePlus_natIso (etaleModuleInverseImage.{u, 0} Λ φC)
    (etaleModuleInverseImage.{u, 0} Λ φA) _ _ _ _
    (etaleModuleBaseChange_pasteV Λ p q pq hpq p' q' pq' hpq' φA φB φC wp wq wpq)
  have d3' := congrArg (fun t => Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatIso
      (etaleModuleDirectImageComp.{u, 0} Λ p q pq hpq)).inv
      (etaleModuleInverseImage.{u, 0} Λ φC).mapDerivedCategoryPlus ≫ t ≫
      Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} Λ φA).mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusNatIso (etaleModuleDirectImageComp.{u, 0} Λ
          p' q' pq' hpq')).inv) d3
  simp only [← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
    Functor.whiskerRight_id', Category.id_comp] at d3'
  simp only [Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id,
    Functor.whiskerLeft_id', Category.comp_id] at d3'
  refine (whisker_eq _ (Functor.whiskerLeft_comp _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker d3' _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ d1).trans ?_
  exact (Category.assoc _ _ _).symm.trans (eq_whisker (Functor.whiskerRight_comp _ _ _).symm _)


/-- **The base change maps of derived direct images compose vertically**, read through the
composition isomorphisms `R(p ≫ q)_* ≅ Rp_* ∘ Rq_*`. -/
theorem etaleModuleDerivedBaseChange_comp :
    etaleModuleDerivedBaseChange.{u, 0} Λ pq pq' φC φA wpq ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ φA)
          (etaleModuleDerivedDirectImageComp.{u, 0} Λ p' q' pq' hpq').hom =
      Functor.whiskerRight (etaleModuleDerivedDirectImageComp.{u, 0} Λ p q pq hpq).hom
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ φC) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ p)
          (etaleModuleDerivedBaseChange.{u, 0} Λ q q' φC φB wq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChange.{u, 0} Λ p p' φB φA wp)
          (etaleModuleDerivedDirectImage.{u, 0} Λ q') ≫
        (Functor.associator _ _ _).hom := by
  dsimp only [etaleModuleDerivedDirectImageComp, rightDerivedFunctorPlusCompIsoOfIso]
  simp only [rightDerivedFunctorPlusIsoOfCompIso_eq, Iso.trans_hom, Iso.symm_hom,
    Functor.rightDerivedFunctorPlusCompIso_hom]
  exact etaleModuleDerivedBaseChange_comp_aux Λ p q pq hpq p' q' pq' hpq' φA φB φC wp wq wpq

end VerticalDirectImage

/-! ### Naturality in morphisms of compactifications -/

section Chain

variable {C : Type*} [Category* C]

/-- The cancellation pattern of `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_hom`,
over plain objects. -/
lemma cube_hom_chain {X₀ X₁ X₂ X₃ X₄ W₁ W₂ Z₁ Z₂ Z₃ : C} (A : X₀ ⟶ X₁) (B : X₁ ⟶ X₂)
    (c : X₂ ⟶ X₃) (D : X₃ ⟶ X₄) (E : X₀ ⟶ W₁) (F : W₁ ⟶ W₂) (G : W₂ ⟶ Z₃) (H : Z₃ ⟶ X₄)
    (x : X₁ ⟶ Z₁) (y : Z₁ ⟶ Z₂) (gd : X₂ ⟶ X₁) (e' : X₃ ⟶ Z₂) (ie' : Z₂ ⟶ X₃)
    (p : W₁ ⟶ Z₁) (q : Z₂ ⟶ Z₃)
    (a1 : A ≫ x = E ≫ p) (a2 : c ≫ e' = gd ≫ x ≫ y) (a3 : q ≫ H = ie' ≫ D)
    (a4 : p ≫ y ≫ q = F ≫ G) (hB : B ≫ gd = 𝟙 _) (he : e' ≫ ie' = 𝟙 _) :
    A ≫ B ≫ c ≫ D = E ≫ F ≫ G ≫ H := by
  have h1 : B ≫ c ≫ D = x ≫ y ≫ ie' ≫ D := by
    calc B ≫ c ≫ D = B ≫ (c ≫ e') ≫ ie' ≫ D := by
          rw [Category.assoc, reassoc_of% he]
      _ = x ≫ y ≫ ie' ≫ D := by rw [a2]; simp only [Category.assoc, reassoc_of% hB]
  rw [h1, reassoc_of% a1, ← a3, reassoc_of% a4]

/-- The cancellation pattern of `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_comp`,
over plain objects. -/
lemma cube_comp_chain {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ B₃ : C} (c : A₀ ⟶ A₁) (gB : A₁ ⟶ A₂)
    (B2' : A₂ ⟶ A₃) (Dh : A₃ ⟶ A₄) (X : A₀ ⟶ A₄) (DY : A₄ ⟶ A₇) (Di : A₄ ⟶ A₃)
    (Dp : A₃ ⟶ A₅) (DZ : A₅ ⟶ A₆) (Dc : A₆ ⟶ A₇) (gD3 : A₂ ⟶ B₃) (B2 : B₃ ⟶ A₅)
    (hk1 : X = c ≫ gB ≫ B2' ≫ Dh) (hk2 : DY = Di ≫ Dp ≫ DZ ≫ Dc) (hn : gD3 ≫ B2 = B2' ≫ Dp)
    (hhi : Dh ≫ Di = 𝟙 _) :
    X ≫ DY = c ≫ gB ≫ gD3 ≫ B2 ≫ DZ ≫ Dc := by
  rw [hk1, hk2]
  simp only [Category.assoc, reassoc_of% hhi, reassoc_of% hn]

end Chain

section Naturality

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {j₁ j₂ : CompactificationOf (Over.mk f)} {j₁' j₂' : CompactificationOf (Over.mk f')}
  (ψ : j₁ ⟶ j₂) (ψ' : j₁' ⟶ j₂') (φ₁ : j₁'.space ⟶ j₁.space) (φ₂ : j₂'.space ⟶ j₂.space)
  (hc₁ : IsPullback g' j₁'.immersion j₁.immersion φ₁)
  (hc₂ : IsPullback g' j₂'.immersion j₂.immersion φ₂)
  (wp : CompactificationOf.Hom.map ψ' ≫ φ₂ = φ₁ ≫ CompactificationOf.Hom.map ψ)

/-- **The map of [Stacks, Tag 0F7G] commutes with base change**, on `D⁺`: for a cube of
compactifications through two morphisms of compactifications, the base change of the map
`Rj₂_! ⟶ Rp_* ∘ Rj₁_!` is the map of the base-changed morphism, read through the
isomorphisms `(g')⁻¹ ∘ Rj'_! ≅ Rj_! ∘ φ⁻¹` and the base change map of `p`. The input is the
underived compatibility `hθ`. -/
theorem derivedRefinementComparison_baseChange
    (hθ : Functor.whiskerRight (refinementIso Λ ψ).hom (etaleModuleInverseImage.{u, 0} Λ φ₂) ≫
        pasteV (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₁).inv
          (etaleModuleBaseChange Λ (CompactificationOf.Hom.map ψ)
            (CompactificationOf.Hom.map ψ') φ₂ φ₁ wp) =
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₂).inv ≫
        Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} Λ g') (refinementIso Λ ψ').hom) :
    Functor.whiskerRight (derivedRefinementComparison Λ ψ)
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ φ₂) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, 0} Λ j₁.immersion)
        (etaleModuleDerivedBaseChange.{u, 0} Λ (CompactificationOf.Hom.map ψ)
          (CompactificationOf.Hom.map ψ') φ₂ φ₁ wp) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etaleModuleDerivedExtensionByZeroCubeIso Λ hc₁).inv
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map ψ')) ≫
      (Functor.associator _ _ _).hom =
    (etaleModuleDerivedExtensionByZeroCubeIso Λ hc₂).inv ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g')
        (derivedRefinementComparison Λ ψ') := by
  have d1 := derivedBaseChangePlus_pasteV
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₁).inv
    (etaleModuleBaseChange Λ (CompactificationOf.Hom.map ψ) (CompactificationOf.Hom.map ψ')
      φ₂ φ₁ wp)
  have d3 := derivedBaseChangePlus_natIso (etaleModuleInverseImage.{u, 0} Λ φ₂)
    (etaleModuleInverseImage.{u, 0} Λ g') (refinementIso Λ ψ) (refinementIso Λ ψ') _ _ hθ
  rw [etaleModuleDerivedExtensionByZeroCubeIso_inv, etaleModuleDerivedExtensionByZeroCubeIso_inv]
  dsimp only [etaleModuleDerivedInverseImagePlus, etaleModuleDerivedBaseChange,
    etaleModuleDerivedExtensionByZero, etaleModuleDerivedDirectImage]
  simp only [derivedRefinementComparison, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Category.assoc]
  refine (whisker_eq _ d1.symm).trans ?_
  exact ((Category.assoc _ _ _).symm.trans (eq_whisker d3 _)).trans (Category.assoc _ _ _)

/-- **Base change maps of direct images compose along a morphism of compactifications**: the
base change map of `f̄₁ = p ≫ f̄₂`, read through the composition comparisons
`Rf̄₁_* ≅ Rp_* ∘ Rf̄₂_*`, is the vertical pasting of the base change maps of `p` and of `f̄₂`.
The input is the underived pasting `Stacks.EtaleCohomology.etaleModuleBaseChange_pasteV`. -/
theorem derivedBaseComparison_baseChange (w₁ : j₁'.toBase ≫ g = φ₁ ≫ j₁.toBase)
    (w₂ : j₂'.toBase ≫ g = φ₂ ≫ j₂.toBase) :
    etaleModuleDerivedBaseChange.{u, 0} Λ j₁.toBase j₁'.toBase g φ₁ w₁ ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ φ₁)
          (derivedBaseComparison Λ ψ') =
      Functor.whiskerRight (derivedBaseComparison Λ ψ)
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.Hom.map ψ))
          (etaleModuleDerivedBaseChange.{u, 0} Λ j₂.toBase j₂'.toBase g φ₂ w₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedBaseChange.{u, 0} Λ (CompactificationOf.Hom.map ψ)
            (CompactificationOf.Hom.map ψ') φ₂ φ₁ wp)
          (etaleModuleDerivedDirectImage.{u, 0} Λ j₂'.toBase) ≫
        (Functor.associator _ _ _).hom := by
  dsimp only [derivedBaseComparison]
  exact etaleModuleDerivedBaseChange_comp_aux Λ _ _ _ (CompactificationOf.map_comp_toBase ψ).symm
    _ _ _ (CompactificationOf.map_comp_toBase ψ').symm φ₁ φ₂ g wp w₂ w₁

/-- **The base change map of a cube is natural in morphisms of compactifications**
([Stacks, Tag 0F7L], independence of the compactification): along morphisms `ψ : j₁ ⟶ j₂` and
`ψ' : j₁' ⟶ j₂'` compatible with the two cubes, the base change maps of the cubes correspond
under the comparisons `Rf_!^{j₂} ⟶ Rf_!^{j₁}` of [Stacks, Tag 0F7I]. The inputs are the
underived identity `hθ`. -/
theorem derivedLowerShriekBaseChangeCube_hom (w₁ : j₁'.toBase ≫ g = φ₁ ≫ j₁.toBase)
    (w₂ : j₂'.toBase ≫ g = φ₂ ≫ j₂.toBase)
    (hθ : Functor.whiskerRight (refinementIso Λ ψ).hom (etaleModuleInverseImage.{u, 0} Λ φ₂) ≫
        pasteV (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₁).inv
          (etaleModuleBaseChange Λ (CompactificationOf.Hom.map ψ)
            (CompactificationOf.Hom.map ψ') φ₂ φ₁ wp) =
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₂).inv ≫
        Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} Λ g') (refinementIso Λ ψ').hom) :
    Functor.whiskerRight (derivedLowerShriekHom Λ ψ)
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g) ≫
      derivedLowerShriekBaseChangeCube Λ j₁ j₁' φ₁ hc₁ w₁ =
    derivedLowerShriekBaseChangeCube Λ j₂ j₂' φ₂ hc₂ w₂ ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g')
        (derivedLowerShriekHom Λ ψ') := by
  have A1 := derivedBaseComparison_baseChange Λ ψ ψ' φ₁ φ₂ wp w₁ w₂
  have A2 := derivedRefinementComparison_baseChange Λ ψ ψ' φ₁ φ₂ hc₁ hc₂ wp hθ
  refine NatTrans.ext (funext fun K => ?_)
  have a1 := (etaleModuleDerivedBaseChange.{u, 0} Λ j₂.toBase j₂'.toBase g φ₂ w₂).naturality
    ((derivedRefinementComparison Λ ψ).app K)
  have a2 := NatTrans.congr_app A1
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j₁.immersion).obj K)
  have a3 := (inv (derivedBaseComparison Λ ψ')).naturality
    ((etaleModuleDerivedExtensionByZeroCubeIso Λ hc₁).inv.app K)
  have a4 := NatTrans.congr_app A2 K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.comp_map] at a1 a2 a3 a4 ⊢
  simp only [derivedLowerShriekBaseChangeCube, derivedLowerShriekHom_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    Functor.comp_obj]
  refine cube_hom_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1 a2 a3 ?_ ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp, a4, Functor.map_comp]
  · rw [← Functor.map_comp, ← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app]
    exact CategoryTheory.Functor.map_id _ _
  · exact (NatTrans.comp_app _ _ _).symm.trans ((congrArg (fun t => NatTrans.app t _)
      (IsIso.hom_inv_id (derivedBaseComparison Λ ψ'))).trans (NatTrans.id_app _ _))

end Naturality

/-! ### Horizontal composition of cubes -/

section Horizontal

variable {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
  {g₁ : Y' ⟶ Y} {g₁' : X' ⟶ X} {g₂ : Y'' ⟶ Y'} {g₂' : X'' ⟶ X'}
  (j : CompactificationOf (Over.mk f)) (j' : CompactificationOf (Over.mk f'))
  (j'' : CompactificationOf (Over.mk f'')) (φ₁ : j'.space ⟶ j.space) (φ₂ : j''.space ⟶ j'.space)
  (hc₁ : IsPullback g₁' j'.immersion j.immersion φ₁)
  (hc₂ : IsPullback g₂' j''.immersion j'.immersion φ₂)
  (w₁ : j'.toBase ≫ g₁ = φ₁ ≫ j.toBase) (w₂ : j''.toBase ≫ g₂ = φ₂ ≫ j'.toBase)
  (w₁₂ : j''.toBase ≫ (g₂ ≫ g₁) = (φ₂ ≫ φ₁) ≫ j.toBase)

/-- **The base change maps of cubes compose horizontally** ([Stacks, Tag 0F7L]): the base change
map of the composite of two cubes side by side is the composite of their base change maps, read
through the composition isomorphisms of inverse images. The inputs are the underived pasting
identities `hU` (base change maps) and `hU₀` (extension by zero). -/
theorem derivedLowerShriekBaseChangeCube_comp
    (hU : pasteH (etaleModuleBaseChange Λ j.toBase j'.toBase g₁ φ₁ w₁)
        (etaleModuleBaseChange Λ j'.toBase j''.toBase g₂ φ₂ w₂)
        (etaleModuleInverseImageCompIso.{u, 0} Λ g₂ g₁).symm
        (etaleModuleInverseImageCompIso.{u, 0} Λ φ₂ φ₁).symm =
      etaleModuleBaseChange Λ j.toBase j''.toBase (g₂ ≫ g₁) (φ₂ ≫ φ₁) w₁₂)
    (hU₀ : pasteH (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₁).inv
        (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₂).inv
        (etaleModuleInverseImageCompIso.{u, 0} Λ φ₂ φ₁).symm
        (etaleModuleInverseImageCompIso.{u, 0} Λ g₂' g₁').symm =
      (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ (hc₂.paste_horiz hc₁)).inv) :
    derivedLowerShriekBaseChangeCube Λ j j'' (φ₂ ≫ φ₁) (hc₂.paste_horiz hc₁) w₁₂ =
      Functor.whiskerLeft (derivedLowerShriek.{u, 0} f j Λ)
          (Functor.mapDerivedCategoryPlusCompIsoh
            (etaleModuleInverseImageCompIso.{u, 0} Λ g₂ g₁).symm).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedLowerShriekBaseChangeCube Λ j j' φ₁ hc₁ w₁)
          (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g₂) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g₁')
          (derivedLowerShriekBaseChangeCube Λ j' j'' φ₂ hc₂ w₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryPlusCompIsoh
            (etaleModuleInverseImageCompIso.{u, 0} Λ g₂' g₁').symm).hom
          (derivedLowerShriek.{u, 0} f'' j'' Λ) := by
  have e1 := derivedBaseChangePlus_pasteH
    (etaleModuleBaseChange Λ j.toBase j'.toBase g₁ φ₁ w₁)
    (etaleModuleBaseChange Λ j'.toBase j''.toBase g₂ φ₂ w₂)
    (etaleModuleInverseImageCompIso.{u, 0} Λ g₂ g₁).symm
    (etaleModuleInverseImageCompIso.{u, 0} Λ φ₂ φ₁).symm
  have e2 := derivedBaseChangePlus_pasteH
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₁).inv
    (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ hc₂).inv
    (etaleModuleInverseImageCompIso.{u, 0} Λ φ₂ φ₁).symm
    (etaleModuleInverseImageCompIso.{u, 0} Λ g₂' g₁').symm
  rw [hU] at e1
  rw [hU₀] at e2
  refine NatTrans.ext (funext fun K => ?_)
  have k1 := NatTrans.congr_app e1 ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj K)
  have k2 := NatTrans.congr_app e2 K
  have n := (etaleModuleDerivedBaseChange.{u, 0} Λ j'.toBase j''.toBase g₂ φ₂ w₂).naturality
    ((etaleModuleDerivedExtensionByZeroCubeIso Λ hc₁).inv.app K)
  rw [etaleModuleDerivedExtensionByZeroCubeIso_inv] at n
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Functor.comp_obj,
    Functor.comp_map] at k1 k2 n ⊢
  simp only [derivedLowerShriekBaseChangeCube, etaleModuleDerivedExtensionByZeroCubeIso_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc, Functor.comp_obj]
  refine cube_comp_chain _ _ _ _ _ _ ((etaleModuleDerivedDirectImage.{u, 0} Λ j''.toBase).map
    ((Functor.mapDerivedCategoryPlusCompIsoh
      (etaleModuleInverseImageCompIso.{u, 0} Λ φ₂ φ₁).symm).inv.app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj K))) _ _ _ _ _ k1 ?_ n ?_
  · rw [k2, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    rfl
  · rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact CategoryTheory.Functor.map_id _ _

end Horizontal

end Stacks.EtaleCohomology
