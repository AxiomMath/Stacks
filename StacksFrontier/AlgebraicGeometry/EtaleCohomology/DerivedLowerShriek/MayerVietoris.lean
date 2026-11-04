module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTriangleTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.StacksAttribute

/-!
# The Mayer--Vietoris triangle for `Rf_!`

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄`, `f = f̄ ∘ j` with
`f̄` proper, and let `X = U ∪ V` be a cover by two opens. The restrictions `a`, `b`, `c` of `f` to
`U`, `V` and `U ∩ V` have the compactifications `X̄` induced by `j`, and for `K` on `X_étale`
there is a distinguished triangle
`Rc_!(K|_{U ∩ V}) ⟶ Ra_!(K|_U) ⊕ Rb_!(K|_V) ⟶ Rf_! K ⟶ Rc_!(K|_{U ∩ V})[1]`,
both on bounded below derived categories and on unbounded ones. This is [Stacks, Tag 0GKN].

## Main results

* `Stacks.EtaleCohomology.exists_distTriang_plus_cover`: the Mayer--Vietoris triangle of Tag 0GKK
  on `D⁺(X_étale, Λ)`, with terms `Rj_{W!}(K|_W)`.
* `Stacks.EtaleCohomology.exists_distTriang_derivedLowerShriek_cover` and
  `Stacks.EtaleCohomology.exists_distTriang_derivedLowerShriekUnbounded_cover`: the triangle for
  `Rf_!` on `D⁺` and on `D`.
* `Stacks.EtaleCohomology.exists_distTriang_derivedLowerShriek_mayerVietoris`:
  **[Stacks, Tag 0GKN]**, both cases together.
* `CategoryTheory.Functor.pointwiseBiprodMapDerivedCategoryObjIso`: the functor induced on derived
  categories by a pointwise biproduct of exact endofunctors computes biproducts.

## Implementation notes

The maps of the triangle are not named: the statements assert that the three objects are the
vertices of a distinguished triangle.

## References

* [Stacks Project, Tag 0GKN](https://stacks.math.columbia.edu/tag/0GKN)
* [Stacks Project, Tag 0GKK](https://stacks.math.columbia.edu/tag/0GKK)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u r

namespace CategoryTheory.Functor

section PointwiseBiprod

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] (A B : C ⥤ C)
  [A.Additive] [B.Additive]

/-- The inclusion of the first summand of a pointwise biproduct of endofunctors. -/
@[simps]
def pointwiseBiprod.inl : A ⟶ pointwiseBiprod A B where
  app _ := biprod.inl
  naturality _ _ f := (biprod.inl_map (A.map f) (B.map f)).symm

/-- The inclusion of the second summand of a pointwise biproduct of endofunctors. -/
@[simps]
def pointwiseBiprod.inr : B ⟶ pointwiseBiprod A B where
  app _ := biprod.inr
  naturality _ _ f := (biprod.inr_map (A.map f) (B.map f)).symm

/-- The projection to the first summand of a pointwise biproduct of endofunctors. -/
@[simps]
def pointwiseBiprod.fst : pointwiseBiprod A B ⟶ A where
  app _ := biprod.fst
  naturality _ _ f := biprod.map_fst (A.map f) (B.map f)

/-- The projection to the second summand of a pointwise biproduct of endofunctors. -/
@[simps]
def pointwiseBiprod.snd : pointwiseBiprod A B ⟶ B where
  app _ := biprod.snd
  naturality _ _ f := biprod.map_snd (A.map f) (B.map f)

/-- The image in the derived category of the degreewise pointwise biproduct of a complex is the
biproduct of the images of the two degreewise summands. -/
def pointwiseBiprodMapHomologicalComplexQIso (L : CochainComplex C ℤ) :
    DerivedCategory.Q.obj
        (((pointwiseBiprod A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅
      DerivedCategory.Q.obj ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ⊞
        DerivedCategory.Q.obj ((B.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
  let c : ComplexShape ℤ := ComplexShape.up ℤ
  let i₁ := (NatTrans.mapHomologicalComplex (pointwiseBiprod.inl A B) c).app L
  let i₂ := (NatTrans.mapHomologicalComplex (pointwiseBiprod.inr A B) c).app L
  let p₁ := (NatTrans.mapHomologicalComplex (pointwiseBiprod.fst A B) c).app L
  let p₂ := (NatTrans.mapHomologicalComplex (pointwiseBiprod.snd A B) c).app L
  let b : BinaryBicone (DerivedCategory.Q.obj ((A.mapHomologicalComplex c).obj L))
      (DerivedCategory.Q.obj ((B.mapHomologicalComplex c).obj L)) :=
    { pt := DerivedCategory.Q.obj (((pointwiseBiprod A B).mapHomologicalComplex c).obj L)
      fst := DerivedCategory.Q.map p₁
      snd := DerivedCategory.Q.map p₂
      inl := DerivedCategory.Q.map i₁
      inr := DerivedCategory.Q.map i₂
      inl_fst := by
        rw [← Functor.map_comp, ← Functor.map_id]
        congr 1
        ext n
        exact biprod.inl_fst
      inl_snd := by
        rw [← Functor.map_comp, ← Functor.map_zero DerivedCategory.Q]
        congr 1
        ext n
        exact biprod.inl_snd
      inr_fst := by
        rw [← Functor.map_comp, ← Functor.map_zero DerivedCategory.Q]
        congr 1
        ext n
        exact biprod.inr_fst
      inr_snd := by
        rw [← Functor.map_comp, ← Functor.map_id]
        congr 1
        ext n
        exact biprod.inr_snd }
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal b (by
    change DerivedCategory.Q.map p₁ ≫ DerivedCategory.Q.map i₁ +
      DerivedCategory.Q.map p₂ ≫ DerivedCategory.Q.map i₂ = 𝟙 _
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, ← Functor.map_id]
    congr 1
    ext n
    exact biprod.total))

variable [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]

/-- The functor induced on derived categories by a pointwise biproduct of exact endofunctors
takes an object to the biproduct of the images under the two summands. -/
def pointwiseBiprodMapDerivedCategoryObjIso (K : DerivedCategory C) :
    (pointwiseBiprod A B).mapDerivedCategory.obj K ≅
      A.mapDerivedCategory.obj K ⊞ B.mapDerivedCategory.obj K :=
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  (pointwiseBiprod A B).mapDerivedCategory.mapIso e.symm ≪≫
    (pointwiseBiprod A B).mapDerivedCategoryFactors.app L ≪≫
    pointwiseBiprodMapHomologicalComplexQIso A B L ≪≫
    biprod.mapIso ((A.mapDerivedCategoryFactors.app L).symm ≪≫ A.mapDerivedCategory.mapIso e)
      ((B.mapDerivedCategoryFactors.app L).symm ≪≫ B.mapDerivedCategory.mapIso e)

end PointwiseBiprod

end CategoryTheory.Functor

namespace Stacks.EtaleCohomology

open AlgebraicGeometry DerivedCategoryComparisons

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

variable (Λ : Type r) [Ring Λ]

section Plus

variable {X : Scheme.{u}}

/-- On `D⁺(X_étale, Λ)`, the derived extension by zero of the derived restriction to an open `W`
is, after forgetting boundedness, the functor `j_{W!} j_W^{-1}` applied degreewise. -/
def plusExtensionByZeroRestrictionιIso (W : X.Opens)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    DerivedCategory.Plus.ι.obj ((etaleModuleDerivedExtensionByZero.{u, r} Λ W.ι).obj
        ((etaleModuleDerivedRestriction.{u, r} Λ W.ι).obj K)) ≅
      (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W.ι).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj K) :=
  DerivedCategory.Plus.ι.mapIso
      ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
          (etaleModuleExtensionByZero.{u, r} Λ W.ι)).app _ ≪≫
        (etaleModuleExtensionByZero.{u, r} Λ W.ι).mapDerivedCategoryPlus.mapIso
          ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
            (etaleModuleRestriction.{u, r} Λ W.ι)).app K)) ≪≫
    (Iso.refl _ : DerivedCategory.Plus.ι.obj
        ((etaleModuleExtensionByZero.{u, r} Λ W.ι).mapDerivedCategoryPlus.obj
          ((etaleModuleRestriction.{u, r} Λ W.ι).mapDerivedCategoryPlus.obj K)) ≅
      ((etaleModuleRestriction.{u, r} Λ W.ι).mapDerivedCategory ⋙
        (etaleModuleExtensionByZero.{u, r} Λ W.ι).mapDerivedCategory).obj
          (DerivedCategory.Plus.ι.obj K)) ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (etaleModuleRestriction.{u, r} Λ W.ι) (etaleModuleExtensionByZero.{u, r} Λ W.ι)).symm.app
        (DerivedCategory.Plus.ι.obj K)

variable (U V : X.Opens) (hUV : U ⊔ V = ⊤)

include hUV in
/-- The Mayer--Vietoris triangle of Stacks Tag 0GKK on `D⁺(X_étale, Λ)`, with the terms written
through the derived functors `Rj_!` and `Rj^{-1}` of the bounded below derived category. -/
theorem exists_distTriang_plus_cover (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    ∃ (α : (etaleModuleDerivedExtensionByZero.{u, r} Λ (U ⊓ V).ι).obj
          ((etaleModuleDerivedRestriction.{u, r} Λ (U ⊓ V).ι).obj K) ⟶
        (etaleModuleDerivedExtensionByZero.{u, r} Λ U.ι).obj
            ((etaleModuleDerivedRestriction.{u, r} Λ U.ι).obj K) ⊞
          (etaleModuleDerivedExtensionByZero.{u, r} Λ V.ι).obj
            ((etaleModuleDerivedRestriction.{u, r} Λ V.ι).obj K))
      (β : _ ⟶ K) (γ : K ⟶ _⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_etaleModuleCover Λ U V hUV (DerivedCategory.Plus.ι.obj K)
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (DerivedCategory.Plus.ι (C := EtaleModules.{u, r} Λ X))
  exact DerivedCategory.Plus.exists_distinguished_of_ι_objIso _ hT _ _ _
    (plusExtensionByZeroRestrictionιIso Λ (U ⊓ V) K)
    (DerivedCategory.Plus.ι.mapBiprod _ _ ≪≫
      biprod.mapIso (plusExtensionByZeroRestrictionιIso Λ U K)
        (plusExtensionByZeroRestrictionιIso Λ V K) ≪≫
      (Functor.pointwiseBiprodMapDerivedCategoryObjIso _ _ _).symm)
    (Iso.refl _)

end Plus

section Main

/-- A triangulated additive functor carries a distinguished triangle with biproduct middle term to
one with any objects isomorphic to the images of its vertices. -/
private theorem exists_distTriang_of_map_biprod {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    [G.Additive] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    {A B₁ B₂ K : C} {α : A ⟶ B₁ ⊞ B₂} {β : B₁ ⊞ B₂ ⟶ K} {γ : K ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang C) {A' B₁' B₂' K' : D} (a : A' ≅ G.obj A)
    (b₁ : B₁' ≅ G.obj B₁) (b₂ : B₂' ≅ G.obj B₂) (k : K' ≅ G.obj K) :
    ∃ (α' : A' ⟶ B₁' ⊞ B₂') (β' : B₁' ⊞ B₂' ⟶ K') (γ' : K' ⟶ A'⟦(1 : ℤ)⟧),
      Triangle.mk α' β' γ' ∈ distTriang D := by
  have hG := G.map_distinguished _ hT
  have := preservesBinaryBiproducts_of_preservesBiproducts G
  exact exists_distinguished_of_objIso _ hG _ _ _ a
    (biprod.mapIso b₁ b₂ ≪≫ (G.mapBiprod _ _).symm) k

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j : CompactificationOf (Over.mk f)) (U V : X.Opens)
  (hUV : U ⊔ V = ⊤)

include hUV in
/-- The Mayer--Vietoris triangle for `Rf_!` on `D⁺(X_étale, Λ)`. -/
theorem exists_distTriang_derivedLowerShriek_cover
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    ∃ (α : (derivedLowerShriek.{u, r} ((U ⊓ V).ι ≫ f) (j.restrictOpen (U ⊓ V).ι) Λ).obj
          ((etaleModuleDerivedRestriction.{u, r} Λ (U ⊓ V).ι).obj K) ⟶
        (derivedLowerShriek.{u, r} (U.ι ≫ f) (j.restrictOpen U.ι) Λ).obj
            ((etaleModuleDerivedRestriction.{u, r} Λ U.ι).obj K) ⊞
          (derivedLowerShriek.{u, r} (V.ι ≫ f) (j.restrictOpen V.ι) Λ).obj
            ((etaleModuleDerivedRestriction.{u, r} Λ V.ι).obj K))
      (β : _ ⟶ (derivedLowerShriek.{u, r} f j Λ).obj K) (γ : _ ⟶ _⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) := by
  obtain ⟨α, β, γ, hT⟩ := exists_distTriang_plus_cover Λ U V hUV K
  exact exists_distTriang_of_map_biprod (derivedLowerShriek.{u, r} f j Λ) hT
    ((derivedLowerShriekRestrictOpenIso Λ j (U ⊓ V).ι).app _)
    ((derivedLowerShriekRestrictOpenIso Λ j U.ι).app _)
    ((derivedLowerShriekRestrictOpenIso Λ j V.ι).app _) (Iso.refl _)

include hUV in
/-- The Mayer--Vietoris triangle for `Rf_!` on `D(X_étale, Λ)`. -/
theorem exists_distTriang_derivedLowerShriekUnbounded_cover
    (K : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ∃ (α : (derivedLowerShriekUnbounded.{u, r} ((U ⊓ V).ι ≫ f)
            (j.restrictOpen (U ⊓ V).ι) Λ).obj
          ((etaleModuleRestriction.{u, r} Λ (U ⊓ V).ι).mapDerivedCategory.obj K) ⟶
        (derivedLowerShriekUnbounded.{u, r} (U.ι ≫ f) (j.restrictOpen U.ι) Λ).obj
            ((etaleModuleRestriction.{u, r} Λ U.ι).mapDerivedCategory.obj K) ⊞
          (derivedLowerShriekUnbounded.{u, r} (V.ι ≫ f) (j.restrictOpen V.ι) Λ).obj
            ((etaleModuleRestriction.{u, r} Λ V.ι).mapDerivedCategory.obj K))
      (β : _ ⟶ (derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) (γ : _ ⟶ _⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (DerivedCategory (EtaleModules.{u, r} Λ Y)) := by
  let A : ∀ W : X.Opens, DerivedCategory (EtaleModules.{u, r} Λ X) := fun W ↦
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ W.ι).obj
      ((etaleModuleRestriction.{u, r} Λ W.ι).mapDerivedCategory.obj K)
  let eA : ∀ W : X.Opens, A W ≅
      (etaleModuleExtensionByZeroOfRestriction.{u, r} Λ W.ι).mapDerivedCategory.obj K := fun W ↦
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ W.ι).app _ ≪≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (etaleModuleRestriction.{u, r} Λ W.ι) (etaleModuleExtensionByZero.{u, r} Λ W.ι)).symm.app K
  obtain ⟨δ, hT⟩ := exists_distTriang_etaleModuleCover Λ U V hUV K
  obtain ⟨α, β, γ, hT'⟩ := exists_distinguished_of_objIso _ hT (A (U ⊓ V)) (A U ⊞ A V) K
    (eA (U ⊓ V))
    (biprod.mapIso (eA U) (eA V) ≪≫ (Functor.pointwiseBiprodMapDerivedCategoryObjIso _ _ _).symm)
    (Iso.refl _)
  let G := (etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapDerivedCategory ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase
  let e : derivedLowerShriekUnbounded.{u, r} f j Λ ≅ G :=
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j.immersion) _
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  exact exists_distTriang_of_map_biprod G hT'
    ((derivedLowerShriekUnboundedRestrictOpenIso Λ j (U ⊓ V).ι).app _ ≪≫ e.app _)
    ((derivedLowerShriekUnboundedRestrictOpenIso Λ j U.ι).app _ ≪≫ e.app _)
    ((derivedLowerShriekUnboundedRestrictOpenIso Λ j V.ι).app _ ≪≫ e.app _) (e.app K)

include hUV in
/-- Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄`, so that
`Rf_! = R(f̄)_* ∘ Rj_!` is defined (`Stacks.EtaleCohomology.derivedLowerShriek` on `D⁺`,
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` on `D`), and let `U` and `V` be opens of `X`
with `X = U ∪ V`. Denote `a : U ⟶ Y`, `b : V ⟶ Y` and `c : U ∩ V ⟶ Y` the restrictions of `f`,
with the compactifications induced by `j`. Let `Λ` be a ring. For `K` in `D⁺(X_étale, Λ)`, and
also for `K` in `D(X_étale, Λ)`, there is a distinguished triangle
`Rc_!(K|_{U ∩ V}) ⟶ Ra_!(K|_U) ⊕ Rb_!(K|_V) ⟶ Rf_! K ⟶ Rc_!(K|_{U ∩ V})[1]`
in `D⁺(Y_étale, Λ)`, respectively `D(Y_étale, Λ)`. -/
@[stacks 0GKN]
theorem exists_distTriang_derivedLowerShriek_mayerVietoris :
    (∀ K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X),
      ∃ (α : (derivedLowerShriek.{u, r} ((U ⊓ V).ι ≫ f) (j.restrictOpen (U ⊓ V).ι) Λ).obj
            ((etaleModuleDerivedRestriction.{u, r} Λ (U ⊓ V).ι).obj K) ⟶
          (derivedLowerShriek.{u, r} (U.ι ≫ f) (j.restrictOpen U.ι) Λ).obj
              ((etaleModuleDerivedRestriction.{u, r} Λ U.ι).obj K) ⊞
            (derivedLowerShriek.{u, r} (V.ι ≫ f) (j.restrictOpen V.ι) Λ).obj
              ((etaleModuleDerivedRestriction.{u, r} Λ V.ι).obj K))
        (β : _ ⟶ (derivedLowerShriek.{u, r} f j Λ).obj K) (γ : _ ⟶ _⟦(1 : ℤ)⟧),
        Triangle.mk α β γ ∈ distTriang (DerivedCategory.Plus (EtaleModules.{u, r} Λ Y))) ∧
    (∀ K : DerivedCategory (EtaleModules.{u, r} Λ X),
      ∃ (α : (derivedLowerShriekUnbounded.{u, r} ((U ⊓ V).ι ≫ f)
              (j.restrictOpen (U ⊓ V).ι) Λ).obj
            ((etaleModuleRestriction.{u, r} Λ (U ⊓ V).ι).mapDerivedCategory.obj K) ⟶
          (derivedLowerShriekUnbounded.{u, r} (U.ι ≫ f) (j.restrictOpen U.ι) Λ).obj
              ((etaleModuleRestriction.{u, r} Λ U.ι).mapDerivedCategory.obj K) ⊞
            (derivedLowerShriekUnbounded.{u, r} (V.ι ≫ f) (j.restrictOpen V.ι) Λ).obj
              ((etaleModuleRestriction.{u, r} Λ V.ι).mapDerivedCategory.obj K))
        (β : _ ⟶ (derivedLowerShriekUnbounded.{u, r} f j Λ).obj K) (γ : _ ⟶ _⟦(1 : ℤ)⟧),
        Triangle.mk α β γ ∈ distTriang (DerivedCategory (EtaleModules.{u, r} Λ Y))) :=
  ⟨exists_distTriang_derivedLowerShriek_cover Λ j U V hUV,
    exists_distTriang_derivedLowerShriekUnbounded_cover Λ j U V hUV⟩

end Main

end Stacks.EtaleCohomology
