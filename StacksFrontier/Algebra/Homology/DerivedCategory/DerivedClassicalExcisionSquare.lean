module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompIsoSpellings
public import StacksFrontier.Homology.DerivedIndexing.PostCompositionCoherence
public import StacksFrontier.Homology.DerivedIndexing.PreCompositionCoherence

/-!
# The derived excision and the classical excision agree, abstractly

Let `𝒜`, `ℬ`, `𝒜'`, `ℬ'` be abelian categories with unbounded derived categories, `𝒜` and `𝒜'`
with enough injectives. Let

* `w : 𝒜 ⥤ ℬ` and `w' : 𝒜' ⥤ ℬ'` be additive,
* `G : ℬ ⥤ ℬ'` be additive and exact,
* `F : 𝒜 ⥤ 𝒜'` be additive, exact and preserving injective objects,
* `δ : w ⋙ G ≅ F ⋙ w'` a degreewise comparison,

and let `Rw : D(𝒜) ⥤ D(ℬ)` with unit `α` and `Rw' : D(𝒜') ⥤ D(ℬ')` with unit `α'` be right
derived functors on the unbounded derived categories. There are then **two** comparisons
`Rⁿw(-) ∘ G ≅ F ∘ Rⁿw'(-)`, built from the single datum `δ`:

* the **derived** one: the isomorphism `Rw ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ Rw'`
  that the uniqueness of right derived functors on `D(𝒜)` produces from `δ`, read on the
  degree-`n` cohomology of the value at an object placed in degree `0`; and
* the **classical** one: `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` followed by
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` ([Stacks, Tag 015Z]), built
  from `δ` through Mathlib's `CategoryTheory.Functor.rightDerived`.

**They agree** under the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` between `Hⁿ(Rw(X[0]))` and
`Rⁿw(X)` taken at `w` and at `w'`. That is
`Stacks.DerivedIndexing.derivedExcisionSquare`, the only result of this file.

## Main definitions

* `Stacks.DerivedFunctor.excisionSourceIso`: the comparison of the two sources on the homotopy
  category that the derived excision feeds to the universal property —
  `CategoryTheory.Functor.mapDerivedCategoryFactorsh` for `G` followed by `δ` applied termwise.
  This is the shape in which
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso` presents
  it.

## Main results

* `Stacks.DerivedIndexing.derivedExcisionSquare`: **the square commutes.**

## Implementation notes

**The proof is the three coherences of the bridge and one cancellation.** Writing `b₁` for the
bridge at `w ⋙ G` taken at `Rw ⋙ G.mapDerivedCategory` and `b₂` for the bridge at `F ⋙ w'`
taken at `F.mapDerivedCategory ⋙ Rw'`:

* `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app` computes
  `b₁` as the left vertical followed by `CategoryTheory.Functor.rightDerivedCompIso` inverted;
* `Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_preComp_app` computes the
  right vertical as `b₂` followed by `compRightDerivedNatIso`;
* `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality_app` is the
  middle square, relating the induced morphism of derived functors to
  `CategoryTheory.NatTrans.rightDerived δ.hom n`;
* `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso` splits the classical comparison
  into `CategoryTheory.Functor.rightDerivedCompIso` inverted and
  `CategoryTheory.NatTrans.rightDerived δ.hom n`, so the two copies of `rightDerivedCompIso`
  cancel.

**The units of the derived excision are not the units the bridge is defined for.** The excision
presents the unit of `Rw ⋙ G.mapDerivedCategory` as `α` whiskered by `G.mapDerivedCategory`, at
the source `w(-) ∘ Qh ∘ G.mapDerivedCategory`, whereas the bridge needs it at
`(w ⋙ G)(-) ∘ Qh`; likewise on the other side.
`Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso` transports between the two, the
transporting isomorphisms being exactly the
`Stacks.DerivedFunctor.postcomposeSourceIso` and `Stacks.DerivedFunctor.precomposeSourceIso` the
canonical units are built from; that is what `hβ₁` and `hβ₂` say, and
`Stacks.DerivedFunctor.postcomposeUnit_whiskerRight` and
`Stacks.DerivedFunctor.precomposeUnit_whisker` discharge them at the canonical presentations.

**Every chase is a helper at a variable category applied with `exact`**, the objects implicit and
the morphisms explicit: at the concrete derived category the spellings
`(w ⋙ G).mapHomotopyCategory c` and `w.mapHomotopyCategory c ⋙ G.mapHomotopyCategory c` of one
object are definitionally but not syntactically equal, and a rewrite whose motive crosses them is
not type-correct.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂ w₃ w₄

namespace Stacks.DerivedFunctor

/-! ### The two presentations of the units -/

section Units

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

/-- **The unit of `Rw ⋙ G.mapDerivedCategory` in the shape a whiskering produces it.** The
canonical unit `Stacks.DerivedFunctor.postcomposeUnit` is written at the source
`(w ⋙ G)(-) ∘ Qh`, which is what the bridge needs; a composite right derived functor is more
naturally presented with the unit `α` of `Rw` whiskered by `G.mapDerivedCategory`, at the source
`w(-) ∘ Qh ∘ G.mapDerivedCategory`. The two differ by
`Stacks.DerivedFunctor.postcomposeSourceIso` exactly. -/
theorem postcomposeUnit_whiskerRight (w : A ⥤ B) [w.Additive] (G : B ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rw) :
    Functor.whiskerRight α G.mapDerivedCategory =
      (postcomposeSourceIso w G).inv ≫ postcomposeUnit w G Rw α := by
  have hdef : postcomposeUnit w G Rw α =
      (postcomposeSourceIso w G).hom ≫
        (Functor.whiskerRight α G.mapDerivedCategory ≫
          (Functor.associator DerivedCategory.Qh Rw G.mapDerivedCategory).hom) := rfl
  have hassoc : Functor.whiskerRight α G.mapDerivedCategory ≫
      (Functor.associator DerivedCategory.Qh Rw G.mapDerivedCategory).hom =
        Functor.whiskerRight α G.mapDerivedCategory :=
    NatTrans.ext (funext fun K => Category.comp_id _)
  rw [hdef, hassoc, Iso.inv_hom_id_assoc]

/-- **The unit of `F.mapDerivedCategory ⋙ Rw` in the shape a whiskering produces it.** The
counterpart of `postcomposeUnit_whiskerRight` for pre-composition: the canonical
`Stacks.DerivedFunctor.precomposeUnit` is the two-factor whiskering below, read across
`Stacks.DerivedFunctor.precomposeSourceIso`. -/
theorem precomposeUnit_whisker (F : E ⥤ A) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (w : A ⥤ B) [w.Additive]
    (Rw : DerivedCategory A ⥤ DerivedCategory B)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Rw) :
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
        Functor.whiskerRight F.mapDerivedCategoryFactorsh.inv Rw =
      (precomposeSourceIso F w).inv ≫ precomposeUnit F w Rw α := by
  have hdef : precomposeUnit F w Rw α =
      (precomposeSourceIso F w).hom ≫
        (Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
          (precomposeTargetIso F Rw).hom) := rfl
  have hc : Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
        (precomposeTargetIso F Rw).hom =
      Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) α ≫
        Functor.whiskerRight F.mapDerivedCategoryFactorsh.inv Rw := by
    refine NatTrans.ext (funext fun K => ?_)
    change α.app _ ≫ (precomposeTargetIso F Rw).hom.app K =
      α.app _ ≫ Rw.map (F.mapDerivedCategoryFactorsh.inv.app K)
    have h : (precomposeTargetIso F Rw).hom.app K =
        CategoryStruct.id _ ≫ Rw.map (F.mapDerivedCategoryFactorsh.inv.app K) ≫
          CategoryStruct.id _ := rfl
    rw [h, Category.id_comp, Category.comp_id]
  rw [hdef, hc, Iso.inv_hom_id_assoc]

end Units

/-! ### The comparison of the two sources the derived excision uses -/

section Source

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {A' : Type u₃} [Category.{v₃} A'] [Abelian A'] [HasDerivedCategory.{w₃} A']
  {B' : Type u₄} [Category.{v₄} B'] [Abelian B'] [HasDerivedCategory.{w₄} B']
  (w : A ⥤ B) [w.Additive]
  (G : B ⥤ B') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (F : A ⥤ A') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (w' : A' ⥤ B') [w'.Additive]
  (δ : w ⋙ G ≅ F ⋙ w')

/-- **The comparison of the two sources on the homotopy category that the derived excision feeds
to the universal property of right derivation**: the factorization of `G.mapDerivedCategory`
through the homotopy category, followed by `δ` applied termwise.

This is the shape in which
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso` presents
it, the final factor being the identification of `(F ⋙ w')(-)` on complexes with `F(-)` then
`w'(-)`, which has identity components. -/
def excisionSourceIso :
    w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙ G.mapDerivedCategory ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
  Functor.isoWhiskerLeft (w.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso δ (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ w'))
          (ComplexShape.up ℤ)).symm) DerivedCategory.Qh

/-- A composite whose second factor is an identity. Stated at an arbitrary category with the
objects implicit, so that the identity may be given at either of two spellings of its object. -/
private theorem comp_id_eq {D : Type*} [Category* D] {x y : D} (f : x ⟶ y) (g : y ⟶ y)
    (hg : g = CategoryStruct.id y) : f ≫ g = f := by rw [hg, Category.comp_id]

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory A'] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] in
/-- **The components of `excisionSourceIso`**: the factorization of `G.mapDerivedCategory`
through the homotopy category, then `δ` applied termwise. -/
theorem excisionSourceIso_hom_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (excisionSourceIso w G F w' δ).hom.app K =
      G.mapDerivedCategoryFactorsh.hom.app
          ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory δ.hom (ComplexShape.up ℤ)).app K) := by
  have h3 : (Functor.mapHomotopyCategoryCompIso δ (ComplexShape.up ℤ)).hom.app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ w'))
          (ComplexShape.up ℤ)).inv.app K =
      (NatTrans.mapHomotopyCategory δ.hom (ComplexShape.up ℤ)).app K :=
    comp_id_eq _ _ rfl
  have h2 : (excisionSourceIso w G F w' δ).hom.app K =
      G.mapDerivedCategoryFactorsh.hom.app
          ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso δ (ComplexShape.up ℤ)).hom.app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ w'))
              (ComplexShape.up ℤ)).inv.app K) := rfl
  exact h2.trans (congrArg (fun z => G.mapDerivedCategoryFactorsh.hom.app
    ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ DerivedCategory.Qh.map z) h3)

omit [EnoughInjectives A] [HasDerivedCategory A] in
/-- **The components of `postcomposeSourceIso` inverted**: the factorization of
`G.mapDerivedCategory` through the homotopy category and nothing else, the comparison of the two
spellings of `(w ⋙ G)(-)` on complexes having identity components. -/
theorem postcomposeSourceIso_inv_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (postcomposeSourceIso w G).inv.app K =
      G.mapDerivedCategoryFactorsh.hom.app
        ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  have h2 : (postcomposeSourceIso w G).inv.app K =
      ((CategoryStruct.id _ ≫ G.mapDerivedCategoryFactorsh.hom.app
            ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
          CategoryStruct.id _) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (w ⋙ G)) (ComplexShape.up ℤ)).hom.app K) := rfl
  exact h2.trans ((comp_id_eq _ _ (DerivedCategory.Qh.map_id _)).trans
    ((comp_id_eq _ _ rfl).trans (Category.id_comp _)))

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory A'] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] in
/-- **`precomposeSourceIso` has identity components**: it is the comparison of the two spellings
of `(F ⋙ w')(-)` on complexes, reassociated. -/
theorem precomposeSourceIso_hom_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (precomposeSourceIso F w').hom.app K =
      CategoryStruct.id (DerivedCategory.Qh.obj
        ((w'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K))) := by
  have h2 : (precomposeSourceIso F w').hom.app K =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (F ⋙ w')) (ComplexShape.up ℤ)).inv.app K) ≫
        CategoryStruct.id _ := rfl
  exact h2.trans ((comp_id_eq _ _ rfl).trans (DerivedCategory.Qh.map_id _))

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory A'] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] in
/-- **The source comparison of the derived excision is the canonical datum, transported.** The
isomorphism `excisionSourceIso` is `δ` read on the homotopy category and composed with `Qh`,
conjugated by the two source identifications that the canonical units of
`Rw ⋙ G.mapDerivedCategory` and `F.mapDerivedCategory ⋙ Rw'` are built from. This is the
hypothesis `hσ` of `Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso`. -/
theorem excisionSourceIso_hom_eq :
    (excisionSourceIso w G F w' δ).hom =
      (postcomposeSourceIso w G).inv ≫
        mapHomotopyCategoryCompQhNatTrans (w ⋙ G) (F ⋙ w') δ.hom ≫
          (precomposeSourceIso F w').hom := by
  refine NatTrans.ext (funext fun K => ?_)
  change (excisionSourceIso w G F w' δ).hom.app K =
    (postcomposeSourceIso w G).inv.app K ≫
      (mapHomotopyCategoryCompQhNatTrans (w ⋙ G) (F ⋙ w') δ.hom).app K ≫
        (precomposeSourceIso F w').hom.app K
  rw [excisionSourceIso_hom_app, postcomposeSourceIso_inv_app,
    mapHomotopyCategoryCompQhNatTrans_app, precomposeSourceIso_hom_app]
  exact (congrArg (fun z => G.mapDerivedCategoryFactorsh.hom.app
    ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ z)
      (comp_id_eq (DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory δ.hom (ComplexShape.up ℤ)).app K)) _ rfl).symm)

end Source

end Stacks.DerivedFunctor

namespace Stacks.DerivedIndexing

/-! ### The square -/

section Square

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {A' : Type u₃} [Category.{v₃} A'] [Abelian A'] [EnoughInjectives A']
    [HasDerivedCategory.{w₃} A']
  {B' : Type u₄} [Category.{v₄} B'] [Abelian B'] [HasDerivedCategory.{w₄} B']
  (w : A ⥤ B) [w.Additive]
  (G : B ⥤ B') [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (F : A ⥤ A') [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesInjectiveObjects]
  (w' : A' ⥤ B') [w'.Additive]
  (δ : w ⋙ G ≅ F ⋙ w')
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (Rw' : DerivedCategory A' ⥤ DerivedCategory B')
  (α' : w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw')
  [Rw'.IsRightDerivedFunctor α' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  [(Rw ⋙ G.mapDerivedCategory).IsRightDerivedFunctor
    (Stacks.DerivedFunctor.postcomposeUnit w G Rw α)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(F.mapDerivedCategory ⋙ Rw').IsRightDerivedFunctor
    (Stacks.DerivedFunctor.precomposeUnit F w' Rw' α')
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (β₁ : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⋙ G.mapDerivedCategory ⟶
    DerivedCategory.Qh ⋙ Rw ⋙ G.mapDerivedCategory)
  (β₂ : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (w'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
    DerivedCategory.Qh ⋙ F.mapDerivedCategory ⋙ Rw')
  [(Rw ⋙ G.mapDerivedCategory).IsRightDerivedFunctor β₁
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(F.mapDerivedCategory ⋙ Rw').IsRightDerivedFunctor β₂
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hβ₁ : β₁ = (Stacks.DerivedFunctor.postcomposeSourceIso w G).inv ≫
    Stacks.DerivedFunctor.postcomposeUnit w G Rw α)
  (hβ₂ : β₂ = (Stacks.DerivedFunctor.precomposeSourceIso F w').inv ≫
    Stacks.DerivedFunctor.precomposeUnit F w' Rw' α')
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hres' : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- The square whose four sides are computed by the three coherences and the spelling
identification. Stated at an arbitrary category with the objects implicit and the morphisms
explicit. -/
private theorem chase {D : Type*} [Category* D] {x₀ x₁ x₂ y₀ y₁ y₂ : D}
    (ρ : x₀ ⟶ y₀) (b₁ : x₀ ⟶ x₁) (lv : x₀ ⟶ x₂) (q : x₂ ⟶ x₁)
    (b₂ : y₀ ⟶ y₁) (cm : y₁ ⟶ y₂) (rv : y₀ ⟶ y₂) (d : x₁ ⟶ y₁) (cl : x₂ ⟶ y₂)
    (hb₁ : b₁ = lv ≫ q) (hrv : rv = b₂ ≫ cm) (hnat : ρ ≫ b₂ = b₁ ≫ d)
    (hcl : cl = q ≫ d ≫ cm) :
    ρ ≫ rv = lv ≫ cl := by
  rw [hrv, hcl, ← Category.assoc, hnat, hb₁]
  simp only [Category.assoc]

include hβ₁ hβ₂

/-- **The derived excision and the classical excision agree.** For `δ : w ⋙ G ≅ F ⋙ w'` with `G`
exact and `F` exact and preserving injectives, the morphism
`Rw ⋙ G.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ Rw'` that the universal property of right
derivation on `D(𝒜)` produces from `δ`, read on the degree-`n` cohomology of the value at
`M` placed in degree `0`, corresponds under the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` to the classical comparison
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` followed by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`.

The left vertical is `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for `G` followed by
`G` applied to the bridge at `w`; the right vertical is `Rw'` applied to
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` for `F` followed by the bridge at `w'`
read at `F M`. -/
theorem derivedExcisionSquare (n : ℕ) (M : A) :
    (DerivedCategory.homologyFunctor B' (n : ℤ)).map
          ((Functor.rightDerivedNatIso (Rw ⋙ G.mapDerivedCategory)
            (F.mapDerivedCategory ⋙ Rw') β₁ β₂
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
            (Stacks.DerivedFunctor.excisionSourceIso w G F w' δ)).hom.app
              ((DerivedCategory.singleFunctor A 0).obj M)) ≫
        ((DerivedCategory.homologyFunctor B' (n : ℤ)).map
              (Rw'.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
            (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w' Rw' α'
              hres' n).hom.app (F.obj M)) =
      ((G.mapDerivedCategoryHomologyIso (n : ℤ)).hom.app
            (Rw.obj ((DerivedCategory.singleFunctor A 0).obj M)) ≫
          G.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α
            hres n).hom.app M)) ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso w G (F ⋙ w') δ n ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w' n).hom.app M := by
  -- the derived excision's induced morphism is the canonical one
  have hρ : (Functor.rightDerivedNatIso (Rw ⋙ G.mapDerivedCategory)
        (F.mapDerivedCategory ⋙ Rw') β₁ β₂
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
        (Stacks.DerivedFunctor.excisionSourceIso w G F w' δ)).hom =
      Stacks.DerivedFunctor.derivedNatTrans (w ⋙ G) (F ⋙ w')
        (Rw ⋙ G.mapDerivedCategory) (F.mapDerivedCategory ⋙ Rw')
        (Stacks.DerivedFunctor.postcomposeUnit w G Rw α)
        (Stacks.DerivedFunctor.precomposeUnit F w' Rw' α') δ.hom :=
    Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (Rw ⋙ G.mapDerivedCategory) (F.mapDerivedCategory ⋙ Rw')
      (Stacks.DerivedFunctor.postcomposeUnit w G Rw α)
      (Stacks.DerivedFunctor.precomposeUnit F w' Rw' α') β₁ β₂
      (Stacks.DerivedFunctor.postcomposeSourceIso w G).symm
      (Stacks.DerivedFunctor.precomposeSourceIso F w').symm
      (Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans (w ⋙ G) (F ⋙ w') δ.hom)
      (Stacks.DerivedFunctor.excisionSourceIso w G F w' δ).hom
      inferInstance inferInstance hβ₁ hβ₂
      (Stacks.DerivedFunctor.excisionSourceIso_hom_eq w G F w' δ)
  -- the middle square
  have hnat := Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality_app
    (w ⋙ G) (F ⋙ w') (Rw ⋙ G.mapDerivedCategory) (F.mapDerivedCategory ⋙ Rw')
    (Stacks.DerivedFunctor.postcomposeUnit w G Rw α)
    (Stacks.DerivedFunctor.precomposeUnit F w' Rw' α') hres δ.hom n M
  rw [Stacks.DerivedFunctor.singleCompDerivedCompHomologyNatTrans_app] at hnat
  -- the left vertical
  have hb₁ := singleCompDerivedCompHomologyIsoRightDerived_postComp_app w G Rw α hres n M
  -- the right vertical
  have hrv := singleCompDerivedCompHomologyIsoRightDerived_preComp_app F w' Rw' α'
    (Stacks.DerivedFunctor.precomposeUnit F w' Rw' α')
    (Stacks.DerivedFunctor.precomposeUnit_app F w' Rw' α') hres hres' n M
  -- the classical comparison, split
  have hcl : (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso w G (F ⋙ w') δ n ≪≫
        Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w' n).hom.app M =
      (w.rightDerivedCompIso G n).inv.app M ≫
        (NatTrans.rightDerived δ.hom n).app M ≫
          (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w' n).hom.app M := by
    have h : (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso w G (F ⋙ w') δ n ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w' n).hom.app M =
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso w G (F ⋙ w') δ n).hom.app M ≫
          (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso F w' n).hom.app M :=
      rfl
    rw [h, moduleComparison_rightDerivedCompIso_app w G (F ⋙ w') δ n M, Category.assoc]
    rfl
  rw [hρ, hcl]
  exact chase _ _ _ _ _ _ _ _ _ (hb₁.trans (Category.assoc _ _ _).symm) hrv.symm hnat rfl

end Square

end Stacks.DerivedIndexing

end
