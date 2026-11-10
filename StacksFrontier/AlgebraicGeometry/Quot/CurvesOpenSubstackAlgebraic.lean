module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal

/-!
# Open substacks of an algebraic stack of curves cut out by condition (o)

Let `𝒳` be an algebraic stack over the big fppf site of `Spec(ℤ)` together with an equivalence
`E` over the site between the category of families of curves and `𝒳`. A property `P` of families
of curves satisfying condition (o) of Section 0E0E (`AlgebraicGeometry.IsOpenCurvesLocus`) cuts
out an open substack of `𝒳` in the sense of Tag 04YM: the strictly full subcategory of objects
whose family has `P`, an algebraic stack whose inclusion is an open immersion of algebraic
stacks. This is how the intrinsic open substacks `Curves^P` of Tag 0E0E become open substacks of
an algebraic model of the stack of curves, on which smoothness over `Spec(ℤ)` can be stated.

## Main definitions

* `AlgebraicGeometry.curvesOpenSubstackOfIsOpenCurvesLocus`: the open substack of `𝒳` cut out
  by `P`, together with the characterization of its objects.

## Main results

* `AlgebraicGeometry.curvesOpenSubstackOfIsOpenCurvesLocus_property_iff`: an object of `𝒳`
  identified with a family of curves lies in the open substack exactly when the family has `P`.
* `AlgebraicGeometry.curvesOpenSubstackOfIsOpenCurvesLocus_mono`: if `P` implies `Q`, the open
  substack of `P` lies in that of `Q`.

## Implementation notes

The construction is that of `AlgebraicGeometry.nodalCurvesOpenSubstack` with the at-worst-nodal
condition replaced by `P`, and it uses the same private helpers, reached by `import all`: over a
scheme-valued point of `𝒳` the open of the base given by condition (o) represents the presheaf of
proofs of `P`, so the inclusion of the full subcategory is representable by open immersions. The
algebraic-stack clause of Tag 05UN is applied to that inclusion.

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Over a scheme-valued point `y` of `𝒳` the open of the base of condition (o) is represented
by an object of the site over the base: an object of the site maps to it exactly when the family
of curves attached to `y` there has `P`. -/
private theorem exists_isOpenCurvesLocus_open_over {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      IsOpenImmersion (B.inclusion.map V.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        P (E.inverse.obj (y.obj T)) ↔ Nonempty (T ⟶ V) := by
  classical
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let G := E.inverse.obj (y.obj T₀)
  obtain ⟨W, hW, hWchar⟩ := hP G
  obtain ⟨V, j, hj, e, he⟩ := openSubspace_yoneda_representation B
    integerBase hZ G.base W hW
  let β := curveFamilyBaseIsoAt B hZ 𝒳 E hE U y hy
  let j' : V ⟶ U := j ≫ β.hom
  let V' : BigFppfOver B U.left.1 U.left.2 := Over.mk j'.left
  have hj' : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j') := by
    change IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map (j ≫ β.hom))
    rw [Functor.map_comp]
    have : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) := hj
    infer_instance
  refine ⟨V', hj', fun T => ?_⟩
  let t : T ⟶ T₀ := Over.homMk T.hom rfl
  let F := E.inverse.obj (y.obj T)
  let a : F ⟶ G := E.inverse.map (y.map t)
  have hT : 𝒳.val.val.p.obj (y.obj T) = (Over.map U.hom).obj T :=
    congrArg (fun H => H.obj T) hy
  let α : F.base ≅ (Over.map U.hom).obj T :=
    curveFamilyBaseIso B hZ 𝒳 E hE (y.obj T) ≪≫ eqToIso hT
  have hcomm : a.baseMap ≫ β.hom =
      α.hom ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    simpa only [α, Iso.trans_hom, eqToIso.hom, Category.assoc] using
      curveFamilyBaseMap_toTerminal B hZ 𝒳 E hE U y hy T
  exact (hWchar F a).trans <|
    (factor_openSubspace_iff W j e he a.baseMap).trans <|
    (factorization_iff_of_iso a.baseMap
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) j α β hcomm).trans <|
    factor_to_over_iff B integerBase hZ U V (j ≫ β.hom) T

/-- **The open substack of an algebraic stack of curves cut out by condition (o).** Let `𝒳` be
an algebraic stack over the big fppf site of `Spec(ℤ)` identified with the category of families of
curves by an equivalence `E` over the site. A property `P` of families of curves satisfying
condition (o) of Section 0E0E cuts out an open substack of `𝒳`, whose objects are those whose
family has `P`. -/
@[no_expose]
def curvesOpenSubstackOfIsOpenCurvesLocus {P : ObjectProperty (CurveFamily B hZ)}
    (hP : IsOpenCurvesLocus B hZ P)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) :
    {U : Stack.OpenSubstack 𝒳 // ∀ F : CurveFamily B hZ, U.property (E.functor.obj F) ↔ P F} := by
  classical
  let Q : ObjectProperty 𝒳.val.val.obj := fun x => P (E.inverse.obj x)
  have hpre : ∀ {x y : 𝒳.val.val.obj}, (x ⟶ y) → Q y → Q x := by
    intro x y f hy
    exact hP.prop_of_hom (E.inverse.map f) hy
  have hstrict : Q.IsClosedUnderIsomorphisms := ⟨fun e hx => hpre e.inv hx⟩
  have hOpen :
      ∃ hQ : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
          (Stack.fullSubcategoryBased 𝒳 Q),
        Stack.AlgebraicStacks.IsOpenImmersion B integerBase hZ
          (Stack.fullSubcategoryInclusion 𝒳 Q hQ) := by
    have hlocal : ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
        (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
        IsAlgebraicSpace B U.left.1 U.left.2
          (propertyPresheaf.{u} (fun T => Q (y.obj T)) (fun f => hpre (y.map f))) := by
      intro U y hy
      obtain ⟨V, hV, hchar⟩ := exists_isOpenCurvesLocus_open_over B hZ hP 𝒳 E hE U y hy
      let e := propertyPresheafIsoYoneda.{u} (fun T => Q (y.obj T))
        (fun f => hpre (y.map f)) V hchar
        (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV)
      exact isAlgebraicSpace_of_iso B U.left.1 U.left.2 e
        (isAlgebraicSpace_yoneda B U.left.1 U.left.2 V)
    let hQ := fullSubcategory_isAlgebraicStack_of_local_representability
      B integerBase hZ 𝒳 Q hpre hlocal
    refine ⟨hQ, ?_⟩
    constructor
    · intro U
      dsimp only
      intro y hy
      exact ⟨propertyPresheaf.{u} (fun T => Q (y.obj T)) (fun f => hpre (y.map f)),
        hlocal U y hy,
        ⟨fullSubcategoryBaseChangePresheafEquivalence
          𝒳.val.val.p (Over.map U.hom) y hy Q hpre⟩⟩
    · intro U y hy F hF heF
      obtain ⟨V, hV, hchar⟩ := exists_isOpenCurvesLocus_open_over B hZ hP 𝒳 E hE U y hy
      let R := propertyPresheaf.{u} (fun T => Q (y.obj T)) (fun f => hpre (y.map f))
      let eQ := fullSubcategoryBaseChangePresheafEquivalence
        𝒳.val.val.p (Over.map U.hom) y hy Q hpre
      have hp : (TwoFibreProductOver.fst (Over.map U.hom)
          (Q.ι ⋙ 𝒳.val.val.p) 𝒳.val.val.p y Q.ι).IsFiberedInGroupoids :=
        StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver eQ
          (elementsProjection_isFiberedInSetoids R).isFiberedInGroupoids
      let e : F ≅ R := presheafIsoOfEquivalenceOver hp F R (Classical.choice heF) eQ
      let eV := propertyPresheafIsoYoneda.{u} (fun T => Q (y.obj T))
        (fun f => hpre (y.map f)) V hchar
        (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV)
      exact algebraicSpaceMap_open_of_yonedaIso B hZ U F hF V hV (e ≪≫ eV)
  let hQ := Classical.choose hOpen
  have hopen := Classical.choose_spec hOpen
  refine ⟨⟨Q, hstrict, hQ, hopen⟩, fun F => ?_⟩
  exact ⟨fun h => hP.prop_of_hom (E.unitIso.hom.app F) h,
    fun h => hP.prop_of_hom (E.unitIso.inv.app F) h⟩

/-- An object of `𝒳` identified with a family of curves lies in the open substack cut out by
`P` exactly when the family has `P`. -/
theorem curvesOpenSubstackOfIsOpenCurvesLocus_property_iff
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) (F : CurveFamily B hZ) :
    (curvesOpenSubstackOfIsOpenCurvesLocus B hZ hP 𝒳 E hE).1.property (E.functor.obj F) ↔ P F :=
  (curvesOpenSubstackOfIsOpenCurvesLocus B hZ hP 𝒳 E hE).2 F

/-- The membership in the open substack cut out by `P` of an arbitrary object of `𝒳`: the
family of curves attached to it by the inverse equivalence has `P`. -/
theorem curvesOpenSubstackOfIsOpenCurvesLocus_property_iff_inverse
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) (x : 𝒳.val.val.obj) :
    (curvesOpenSubstackOfIsOpenCurvesLocus B hZ hP 𝒳 E hE).1.property x ↔
      P (E.inverse.obj x) := by
  have := (curvesOpenSubstackOfIsOpenCurvesLocus B hZ hP 𝒳 E hE).1.strictlyFull
  rw [← curvesOpenSubstackOfIsOpenCurvesLocus_property_iff B hZ hP 𝒳 E hE]
  exact ⟨ObjectProperty.prop_of_iso _ (E.counitIso.app x).symm,
    ObjectProperty.prop_of_iso _ (E.counitIso.app x)⟩

/-- **Inclusions of open substacks of curves.** If `P` implies `Q`, the open substack of `𝒳` cut
out by `P` is contained in that cut out by `Q`. -/
theorem curvesOpenSubstackOfIsOpenCurvesLocus_mono
    {P Q : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (hQ : IsOpenCurvesLocus B hZ Q) (hPQ : ∀ F, P F → Q F)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) :
    (curvesOpenSubstackOfIsOpenCurvesLocus B hZ hP 𝒳 E hE).1.property ≤
      (curvesOpenSubstackOfIsOpenCurvesLocus B hZ hQ 𝒳 E hE).1.property := by
  intro x hx
  rw [curvesOpenSubstackOfIsOpenCurvesLocus_property_iff_inverse] at hx ⊢
  exact hPQ _ hx

end AlgebraicGeometry

end
