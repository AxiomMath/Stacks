module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeClassifyingCoverReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeInertiaBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids

/-!
# The relative inertia over a target with thin fibres is the absolute inertia

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` with `𝒴` representable by an
algebraic space. Then the relative inertia `ℐ_{𝒳/𝒴}` and the absolute inertia `ℐ_𝒳` are *the
same* object over `𝒳`: an automorphism `α` of an object `x` of `𝒳` lying over an identity of the
site automatically has `f α = 𝟙`, because `f α` is then a vertical endomorphism of an object of
`𝒴` and the fibres of `𝒴` are thin.

## Main definitions

* `CategoryTheory.RelativeInertia.toAbsolute` and
  `CategoryTheory.RelativeInertia.ofAbsolute`: the two comparison functors
  `I_{S/S'} ⥤ I_S` and `I_S ⥤ I_{S/S'}`, each the identity on the underlying object and
  automorphism. The second needs the fibres of `p'` to be thin.
* `CategoryTheory.RelativeInertia.absoluteEquivalence`: they are mutually inverse, so the two
  inertias are isomorphic categories over the base.
* `AlgebraicGeometry.Stack.toAbsoluteInertia` and `AlgebraicGeometry.Stack.ofAbsoluteInertia`:
  the same two comparisons as 1-morphisms of algebraic stacks over `S`, each strictly over the
  site and each strictly compatible with the two forgetful 1-morphisms.

## Main results

* `CategoryTheory.RelativeInertia.toAbsolute_comp_ofAbsolute` and
  `…ofAbsolute_comp_toAbsolute`: the two comparisons are mutually inverse.
* `AlgebraicGeometry.Stack.isFlat_relativeInertiaProjection_iff` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_relativeInertiaProjection_iff`: for a
  target with thin fibres — in particular one representable by an algebraic space — the
  forgetful 1-morphism of the relative inertia is flat, resp. locally of finite presentation,
  exactly when that of the absolute inertia is.
* `AlgebraicGeometry.Stack.isFlat_relativeInertiaProjection_iff_of_representableTarget`
  and its local-finite-presentation companion: the same for a target representable by an
  algebraic space (Stacks 04SV).
* `AlgebraicGeometry.Stack.isFlat_inertiaProjection_of_baseChange` and
  `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_inertiaProjection_of_baseChange`: for
  `π : 𝒵 ⟶ Y` and a surjective flat `v : Y' ⟶ Y` with both `Y` and `Y'` representable by
  algebraic spaces, flatness of the forgetful 1-morphism of the inertia of `𝒵 ×_Y Y'` gives
  flatness of that of `𝒵`, and likewise for local finite presentation.
* `AlgebraicGeometry.Stack.exists_schemeBase_gerbe_inertia_reduction_of_isGerbe`: for a gerbe `𝒳`
  over `S`, flatness, resp. local finite presentation, of the forgetful 1-morphism of the inertia
  of `𝒳` follows from the same for a gerbe over the algebraic stack of an object of the site.

## References

* [Stacks Project, Tag 034I](https://stacks.math.columbia.edu/tag/034I)
* [Stacks Project, Tag 04SA](https://stacks.math.columbia.edu/tag/04SA)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 06PQ](https://stacks.math.columbia.edu/tag/06PQ)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

namespace CategoryTheory.RelativeInertia

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
  {S' : Type u₃} [Category.{v₃} S']

/-- The comparison `I_{S/S'} ⥤ I_S` from the relative inertia of a functor `F : S ⥤ S'` over
`C` to the absolute inertia of `S` over `C`: the identity on the pair `(x, α)`. -/
def toAbsolute (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p) :
    RelativeInertia F ⥤ RelativeInertia p where
  obj A :=
    { obj := A.obj
      auto := A.auto
      cond := by
        subst hw
        simpa using congrArg p'.map A.cond }
  map φ := { hom := φ.hom, comm := φ.comm }

/-- The comparison `I_S ⥤ I_{S/S'}` in the other direction, again the identity on the pair
`(x, α)`, for `p'` fibred with thin fibres. -/
def ofAbsolute (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (hfib : p'.IsFibered) (ht : ∀ R : C, Quiver.IsThin (p'.Fiber R)) :
    RelativeInertia p ⥤ RelativeInertia F where
  obj A :=
    { obj := A.obj
      auto := A.auto
      cond := by
        subst hw
        have := hfib
        have hA : p'.map (F.map A.auto.hom) = 𝟙 (p'.obj (F.obj A.obj)) := A.cond
        have h₁ : p'.IsHomLift (𝟙 (p'.obj (F.obj A.obj))) (F.map A.auto.hom) :=
          IsHomLift.of_fac' p' _ (F.map A.auto.hom) rfl rfl (by simpa using hA)
        have h₂ : p'.IsHomLift (𝟙 (p'.obj (F.obj A.obj))) (𝟙 (F.obj A.obj)) :=
          IsHomLift.id rfl
        exact Functor.hom_unique_of_fiber_isThin p' (𝟙 (p'.obj (F.obj A.obj))) (ht _)
          (F.map A.auto.hom) (𝟙 (F.obj A.obj)) h₁ h₂ }
  map φ := { hom := φ.hom, comm := φ.comm }

/-- The comparison `I_{S/S'} ⥤ I_S` is the identity on underlying objects. -/
@[simp] lemma toAbsolute_obj_obj (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (A : RelativeInertia F) : ((toAbsolute F p p' hw).obj A).obj = A.obj := rfl

/-- The comparison `I_{S/S'} ⥤ I_S` is the identity on underlying morphisms. -/
@[simp] lemma toAbsolute_map_hom (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    {A D : RelativeInertia F} (φ : A ⟶ D) : ((toAbsolute F p p' hw).map φ).hom = φ.hom := rfl

/-- The comparison `I_{S/S'} ⥤ I_S` followed by the forgetful functor of `I_S` is the
forgetful functor of `I_{S/S'}`. -/
lemma toAbsolute_comp_π (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p) :
    toAbsolute F p p' hw ⋙ RelativeInertia.π p = RelativeInertia.π F := rfl

/-- The comparison `I_S ⥤ I_{S/S'}` followed by the forgetful functor of `I_{S/S'}` is the
forgetful functor of `I_S`. -/
lemma ofAbsolute_comp_π (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (hfib : p'.IsFibered) (ht : ∀ R : C, Quiver.IsThin (p'.Fiber R)) :
    ofAbsolute F p p' hw hfib ht ⋙ RelativeInertia.π F = RelativeInertia.π p := rfl

/-- The two comparisons compose to the identity of `I_{S/S'}`. -/
lemma toAbsolute_comp_ofAbsolute (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (hfib : p'.IsFibered) (ht : ∀ R : C, Quiver.IsThin (p'.Fiber R)) :
    toAbsolute F p p' hw ⋙ ofAbsolute F p p' hw hfib ht = 𝟭 (RelativeInertia F) := rfl

/-- The two comparisons compose to the identity of `I_S`. -/
lemma ofAbsolute_comp_toAbsolute (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (hfib : p'.IsFibered) (ht : ∀ R : C, Quiver.IsThin (p'.Fiber R)) :
    ofAbsolute F p p' hw hfib ht ⋙ toAbsolute F p p' hw = 𝟭 (RelativeInertia p) := rfl

/-- The relative inertia of a functor whose target has thin fibres is its absolute inertia: the two
comparisons are mutually inverse, so `I_{S/S'}` and `I_S` are isomorphic categories, by an
isomorphism which is the identity on the underlying pairs `(x, α)` and therefore commutes with the
two forgetful functors and with the two structure functors to `C`. -/
def absoluteEquivalence (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (hfib : p'.IsFibered) (ht : ∀ R : C, Quiver.IsThin (p'.Fiber R)) :
    RelativeInertia F ≌ RelativeInertia p :=
  CategoryTheory.Equivalence.mk (toAbsolute F p p' hw) (ofAbsolute F p p' hw hfib ht)
    (Iso.refl _) (Iso.refl _)

/-- When the fibres of `p'` are thin, the comparison `I_{S/S'} ⥤ I_S` is an equivalence. -/
lemma isEquivalence_toAbsolute (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (hfib : p'.IsFibered) (ht : ∀ R : C, Quiver.IsThin (p'.Fiber R)) :
    Functor.IsEquivalence (toAbsolute F p p' hw) :=
  (absoluteEquivalence F p p' hw hfib ht).isEquivalence_functor

/-- When the fibres of `p'` are thin, the comparison `I_S ⥤ I_{S/S'}` is an equivalence. -/
lemma isEquivalence_ofAbsolute (F : S ⥤ S') (p : S ⥤ C) (p' : S' ⥤ C) (hw : F ⋙ p' = p)
    (hfib : p'.IsFibered) (ht : ∀ R : C, Quiver.IsThin (p'.Fiber R)) :
    Functor.IsEquivalence (ofAbsolute F p p' hw hfib ht) :=
  (absoluteEquivalence F p p' hw hfib ht).isEquivalence_inverse

end CategoryTheory.RelativeInertia

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The comparison 1-morphism `ℐ_{𝒳/𝒴} ⟶ ℐ_𝒳` of algebraic stacks over `S`, the identity on the
pair `(x, α)`. -/
def toAbsoluteInertia :
    relativeInertiaStack B S hS f ⟶ inertiaAlgebraicStack B S hS 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      { toFunctor := RelativeInertia.toAbsolute f.hom.hom.toFunctor 𝒳.val.val.p 𝒴.val.val.p
          f.hom.hom.w
        w := rfl })

/-- The comparison 1-morphism `ℐ_𝒳 ⟶ ℐ_{𝒳/𝒴}` of algebraic stacks over `S`, the identity on the
pair `(x, α)`, for `𝒴` fibred in setoids. -/
def ofAbsoluteInertia (hset : 𝒴.val.val.p.IsFiberedInSetoids) :
    inertiaAlgebraicStack B S hS 𝒳 ⟶ relativeInertiaStack B S hS f :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      { toFunctor := RelativeInertia.ofAbsolute f.hom.hom.toFunctor 𝒳.val.val.p 𝒴.val.val.p
          f.hom.hom.w hset.isFiberedInGroupoids.isFibered hset.fiber_isThin
        w := rfl })

/-- The comparison `ℐ_{𝒳/𝒴} ⟶ ℐ_𝒳` followed by the forgetful 1-morphism of the absolute inertia
is the forgetful 1-morphism of the relative inertia, on the nose. -/
lemma toAbsoluteInertia_comp_inertiaProjection :
    toAbsoluteInertia B S hS f ≫ inertiaProjectionAlgebraicStacks B S hS 𝒳 =
      relativeInertiaProjection B S hS f := rfl

/-- The comparison `ℐ_𝒳 ⟶ ℐ_{𝒳/𝒴}` followed by the forgetful 1-morphism of the relative inertia
is the forgetful 1-morphism of the absolute inertia, on the nose. -/
lemma ofAbsoluteInertia_comp_relativeInertiaProjection
    (hset : 𝒴.val.val.p.IsFiberedInSetoids) :
    ofAbsoluteInertia B S hS f hset ≫ relativeInertiaProjection B S hS f =
      inertiaProjectionAlgebraicStacks B S hS 𝒳 := rfl

/-- When the fibres of `𝒴` are thin, the comparison `ℐ_{𝒳/𝒴} ⟶ ℐ_𝒳` is an equivalence of the
underlying categories. -/
lemma isEquivalence_toAbsoluteInertia (hset : 𝒴.val.val.p.IsFiberedInSetoids) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (toAbsoluteInertia B S hS f).hom) :=
  RelativeInertia.isEquivalence_toAbsolute f.hom.hom.toFunctor 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.w hset.isFiberedInGroupoids.isFibered hset.fiber_isThin

/-- When the fibres of `𝒴` are thin, the comparison `ℐ_𝒳 ⟶ ℐ_{𝒳/𝒴}` is an equivalence of the
underlying categories. -/
lemma isEquivalence_ofAbsoluteInertia (hset : 𝒴.val.val.p.IsFiberedInSetoids) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (ofAbsoluteInertia B S hS f hset).hom) :=
  RelativeInertia.isEquivalence_ofAbsolute f.hom.hom.toFunctor 𝒳.val.val.p 𝒴.val.val.p
    f.hom.hom.w hset.isFiberedInGroupoids.isFibered hset.fiber_isThin

/-- Condition (2) of Stacks 06FM is the same for the two inertia projections when the fibres of
the target are thin. -/
theorem hasPropertyOnSomeSmoothDiagram_relativeInertiaProjection_iff
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hset : 𝒴.val.val.p.IsFiberedInSetoids) :
    HasPropertyOnSomeSmoothDiagram B S hS P (relativeInertiaProjection B S hS f).hom ↔
      HasPropertyOnSomeSmoothDiagram B S hS P
        (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom :=
  ⟨hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS P
      (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom
      (relativeInertiaProjection B S hS f).hom (toAbsoluteInertia B S hS f).hom
      (isEquivalence_toAbsoluteInertia B S hS f hset) (Iso.refl _),
    hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS P
      (relativeInertiaProjection B S hS f).hom
      (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom
      (ofAbsoluteInertia B S hS f hset).hom
      (isEquivalence_ofAbsoluteInertia B S hS f hset) (Iso.refl _)⟩

/-- The forgetful 1-morphism of the relative inertia is flat exactly when that of the absolute
inertia is, for a target whose fibres are thin. -/
theorem isFlat_relativeInertiaProjection_iff (hset : 𝒴.val.val.p.IsFiberedInSetoids) :
    AlgebraicStacks.IsFlat B S hS (relativeInertiaProjection B S hS f) ↔
      AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) :=
  hasPropertyOnSomeSmoothDiagram_relativeInertiaProjection_iff B S hS f _ hset

/-- Local finite presentation of a 1-morphism of algebraic stacks is equivalent to the existential
condition (2) of Stacks 06FM at local finite presentation of morphisms of algebraic spaces. -/
private theorem isLocallyOfFinitePresentation_iff_hasPropertyOnSomeSmoothDiagram
    {𝒲 𝒵 : AlgebraicStacks.{u, w} B S hS} (g : 𝒲 ⟶ 𝒵) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g ↔
      HasPropertyOnSomeSmoothDiagram B S hS
        (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k) g.hom :=
  hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    𝒲.property 𝒵.property g.hom

/-- The forgetful 1-morphism of the relative inertia is locally of finite presentation exactly
when that of the absolute inertia is, for a target whose fibres are thin. -/
theorem isLocallyOfFinitePresentation_relativeInertiaProjection_iff
    (hset : 𝒴.val.val.p.IsFiberedInSetoids) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (relativeInertiaProjection B S hS f) ↔
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒳) := by
  refine (isLocallyOfFinitePresentation_iff_hasPropertyOnSomeSmoothDiagram B S hS _).trans ?_
  exact (hasPropertyOnSomeSmoothDiagram_relativeInertiaProjection_iff B S hS f _ hset).trans
    (isLocallyOfFinitePresentation_iff_hasPropertyOnSomeSmoothDiagram B S hS _).symm

/-- A category fibred in groupoids over the big fppf site which is representable by an algebraic
space (Stacks 04SV) is fibred in setoids (Stacks 02ZX). -/
theorem isFiberedInSetoids_of_isRepresentableByAlgebraicSpace
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵) :
    𝒵.val.p.IsFiberedInSetoids :=
  ((isRepresentableByAlgebraicSpace_iff B S hS 𝒵).1 h𝒵).1

/-- The forgetful 1-morphism of the relative inertia of a 1-morphism to an algebraic space is
flat exactly when that of the absolute inertia is. -/
theorem isFlat_relativeInertiaProjection_iff_of_representableTarget
    (h𝒴 : IsRepresentableByAlgebraicSpace B S hS 𝒴.val) :
    AlgebraicStacks.IsFlat B S hS (relativeInertiaProjection B S hS f) ↔
      AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) :=
  isFlat_relativeInertiaProjection_iff B S hS f
    (isFiberedInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒴.val h𝒴)

/-- The forgetful 1-morphism of the relative inertia of a 1-morphism to an algebraic space is
locally of finite presentation exactly when that of the absolute inertia is. -/
theorem isLocallyOfFinitePresentation_relativeInertiaProjection_iff_of_representableTarget
    (h𝒴 : IsRepresentableByAlgebraicSpace B S hS 𝒴.val) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (relativeInertiaProjection B S hS f) ↔
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
        (inertiaProjectionAlgebraicStacks B S hS 𝒳) :=
  isLocallyOfFinitePresentation_relativeInertiaProjection_iff B S hS f
    (isFiberedInSetoids_of_isRepresentableByAlgebraicSpace B S hS 𝒴.val h𝒴)

/-! ### Base change of the base of a 1-morphism to an algebraic space -/

section BaseChange

variable {𝒵 Y Y' : AlgebraicStacks.{u, w} B S hS} (π : 𝒵 ⟶ Y) (v : Y' ⟶ Y)

/-- The first projection of the base change of `π : 𝒵 ⟶ Y` along `v : Y' ⟶ Y` is surjective
when `v` is. -/
theorem isSurjective_twoFibreProductSquare_fst (hvsurj : IsSurjective B S hS v) :
    IsSurjective B S hS (twoFibreProductSquareAlgebraicStacks B S hS π v).fst :=
  isSurjective_of_isTwoFibreProduct B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS π v).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS π v)) hvsurj

/-- The flatness of the inertia projection descends along a base change of the base. Let
`π : 𝒵 ⟶ Y` and `v : Y' ⟶ Y` be 1-morphisms of algebraic stacks over `S` with `Y` and `Y'` both
representable by algebraic spaces and `v` surjective and flat, and let `𝒵' = 𝒵 ×_Y Y'`. If the
forgetful 1-morphism of the inertia of `𝒵'` is flat, then so is that of the inertia of `𝒵`. -/
theorem isFlat_inertiaProjection_of_baseChange
    (hY : IsRepresentableByAlgebraicSpace B S hS Y.val)
    (hY' : IsRepresentableByAlgebraicSpace B S hS Y'.val)
    (hvsurj : IsSurjective B S hS v) (hvflat : AlgebraicStacks.IsFlat B S hS v)
    (h : AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS π v).pt)) :
    AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒵) := by
  refine (isFlat_relativeInertiaProjection_iff_of_representableTarget
    B S hS π hY).1 ?_
  refine AlgebraicStacks.isFlat_twoFibreProduct_fst_descent B S hS
    (relativeInertiaProjection B S hS π)
    (twoFibreProductSquareAlgebraicStacks B S hS π v).fst _
    (cartesianRelativeInertiaSquare B S hS π v).cartesian
    (isSurjective_twoFibreProductSquare_fst B S hS π v hvsurj)
    (AlgebraicStacks.isFlat_baseChange B S hS v π _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS π v) hvflat) ?_
  exact (isFlat_relativeInertiaProjection_iff_of_representableTarget B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS π v).snd hY').2 h

/-- The local finite presentation of the inertia projection descends along a base change of the
base. Let `π : 𝒵 ⟶ Y` and `v : Y' ⟶ Y` be 1-morphisms of algebraic stacks over `S` with `Y` and
`Y'` both representable by algebraic spaces and `v` surjective, flat and locally of finite
presentation, and let `𝒵' = 𝒵 ×_Y Y'`. If the forgetful 1-morphism of the inertia of `𝒵'` is
locally of finite presentation, then so is that of the inertia of `𝒵`. -/
theorem isLocallyOfFinitePresentation_inertiaProjection_of_baseChange
    (hY : IsRepresentableByAlgebraicSpace B S hS Y.val)
    (hY' : IsRepresentableByAlgebraicSpace B S hS Y'.val)
    (hvsurj : IsSurjective B S hS v) (hvflat : AlgebraicStacks.IsFlat B S hS v)
    (hvlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS v)
    (h : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (inertiaProjectionAlgebraicStacks B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS π v).pt)) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (inertiaProjectionAlgebraicStacks B S hS 𝒵) := by
  have h1 : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
      (relativeInertiaProjection B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS π v).snd) :=
    (isLocallyOfFinitePresentation_relativeInertiaProjection_iff_of_representableTarget
      B S hS (twoFibreProductSquareAlgebraicStacks B S hS π v).snd hY').2 h
  have h2 := (isLocallyOfFinitePresentation_iff_hasPropertyOnSomeSmoothDiagram B S hS _).1 h1
  have h3 : HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ k => Space.IsLocallyOfFinitePresentation B S hS k)
      (twoFibreProductSquareAlgebraicStacks B S hS (relativeInertiaProjection B S hS π)
        (twoFibreProductSquareAlgebraicStacks B S hS π v).fst).snd.hom :=
    hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS _
      (((inertiaBaseChangeModel B S hS π v).precompose
        (inertiaBaseChangeComparison B S hS π v)).swap)
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (relativeInertiaProjection B S hS π).hom
        (twoFibreProductSquareAlgebraicStacks B S hS π v).fst.hom).swap)
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_inertiaBaseChangePrecompose B S hS π v))
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (relativeInertiaProjection B S hS π).hom
          (twoFibreProductSquareAlgebraicStacks B S hS π v).fst.hom))
      h2
  refine (isLocallyOfFinitePresentation_relativeInertiaProjection_iff_of_representableTarget
    B S hS π hY).1 ?_
  refine AlgebraicStacks.isLocallyOfFinitePresentation_of_baseChange B S hS
    (relativeInertiaProjection B S hS π)
    (twoFibreProductSquareAlgebraicStacks B S hS π v).fst
    (isSurjective_twoFibreProductSquare_fst B S hS π v hvsurj)
    (AlgebraicStacks.isFlat_baseChange B S hS v π _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS π v) hvflat)
    (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS v π _
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS π v) hvlfp) ?_
  exact (isLocallyOfFinitePresentation_iff_hasPropertyOnSomeSmoothDiagram B S hS _).2 h3

/-- If `𝒳` is a gerbe over `S` then there are an object `V` of the big fppf site, an algebraic
stack `𝒴` over `S` and a 1-morphism `q : 𝒴 ⟶ 𝒮_V` making `𝒴` a gerbe over the algebraic stack of
`V`, such that flatness, resp. local finite presentation, of the forgetful 1-morphism of the
inertia of `𝒴` gives the same for `𝒳`. -/
theorem exists_schemeBase_gerbe_inertia_reduction_of_isGerbe
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : AlgebraicStacks.IsGerbe B S hS 𝒳) :
    ∃ (V : BigFppfOver B S hS) (𝒴 : AlgebraicStacks.{u, w} B S hS)
      (q : 𝒴 ⟶ schemeStack.{u, w} B S hS V),
      AlgebraicStacks.IsGerbeOver B S hS q ∧
      (AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒴) →
        AlgebraicStacks.IsFlat B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳)) ∧
      (AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
          (inertiaProjectionAlgebraicStacks B S hS 𝒴) →
        AlgebraicStacks.IsLocallyOfFinitePresentation B S hS
          (inertiaProjectionAlgebraicStacks B S hS 𝒳)) := by
  obtain ⟨X, hX, π, hπ⟩ := h𝒳
  obtain ⟨V, v, hvsurj, hvflat, hvlfp⟩ :=
    AlgebraicStacks.exists_isSurjective_isFlat_isLocallyOfFinitePresentation_schemeStack.{u, w}
      B S hS X
  refine ⟨V, (twoFibreProductSquareAlgebraicStacks B S hS π v).pt,
    (twoFibreProductSquareAlgebraicStacks B S hS π v).snd,
    AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS π v)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS π v) hπ,
    fun h => isFlat_inertiaProjection_of_baseChange B S hS π v hX
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) hvsurj hvflat h,
    fun h => isLocallyOfFinitePresentation_inertiaProjection_of_baseChange B S hS π v hX
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V) hvsurj hvflat hvlfp h⟩

end BaseChange

end AlgebraicGeometry.Stack

end
