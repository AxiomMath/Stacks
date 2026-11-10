module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Limits.Final

/-!
# Limit preservation on objects implies local finite presentation

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` which is limit preserving
on objects. Then `f` is locally of finite presentation.

## Main results

* `AlgebraicStacks.isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects`, in the namespace
  `AlgebraicGeometry.Stack`: a 1-morphism of algebraic stacks which is limit preserving on objects
  is locally of finite presentation.
* `AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_of_iso`: limit preservation on objects
  only depends on the 2-isomorphism class of the 1-morphism.
* `AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_reindex`: the condition at index
  categories in large universes implies the condition at index categories in the universe of
  the schemes.
* `AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_twoFibreProductSquareFst`: the first
  projection of the canonical 2-fibre product square is limit preserving on objects as soon as
  the opposite leg of the cospan is.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_isRelativelySmooth`: a smooth
  1-morphism is limit preserving on objects.
* `AlgebraicGeometry.Stack.isLocallyOfFinitePresentation_of_associatedMap`: a morphism of
  algebraic spaces whose associated 1-morphism of categories fibred in groupoids is limit
  preserving on objects is locally of finite presentation.

## References

* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CV](https://stacks.math.columbia.edu/tag/06CV)
* [Stacks Project, Tag 06CW](https://stacks.math.columbia.edu/tag/06CW)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigFppfOver

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] uliftCategory

/-- Precomposing a strongly cartesian morphism with an isomorphism lying over an identity gives a
strongly cartesian morphism over the same base map. -/
private theorem isStronglyCartesian_comp_of_isHomLift_id
    {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮] {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a a' b : 𝒳}
    {f : R ⟶ S} {ψ : a' ⟶ a} {φ : a ⟶ b} [IsIso ψ] (hψ : p.IsHomLift (𝟙 R) ψ)
    (hφ : p.IsStronglyCartesian f φ) : p.IsStronglyCartesian f (ψ ≫ φ) := by
  simpa using (inferInstance : p.IsStronglyCartesian (𝟙 R ≫ f) (ψ ≫ φ))

/-- If `f` and `g` are 2-isomorphic 1-morphisms of categories fibred in groupoids and `f` is limit
preserving on objects, so is `g`. -/
theorem isLimitPreservingOnObjects_of_iso
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g)
    (hf : IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳 𝒴 f) :
    IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳 𝒴 g := by
  intro I _ _ D c hc i y x γ hγ
  let inc := BigAffineFppf.inclusion B S hS
  let α := CatFiberedInGroupoids.underlyingIso e
  have hα : 𝒴.val.p.IsHomLift (𝟙 (inc.obj c.pt)) (α.hom.app x.1) :=
    e.hom.hom.isHomLift x.2
  have hαγ := isStronglyCartesian_comp_of_isHomLift_id hα hγ
  obtain ⟨j, a, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ :=
    hf I D c hc i y x (α.hom.app x.1 ≫ γ) hαγ
  have hα' : 𝒴.val.p.IsHomLift (𝟙 (inc.obj (D.obj j))) (α.inv.app x'.1) :=
    e.inv.hom.isHomLift x'.2
  refine ⟨j, a, x', xU, δ, β, α.inv.app x'.1 ≫ γ', hδ, hβ, hβiso,
    isStronglyCartesian_comp_of_isHomLift_id hα' hγ', ?_⟩
  change g.hom.toFunctor.map δ ≫ α.inv.app x'.1 ≫ γ' = g.hom.toFunctor.map β ≫ γ
  rw [← Category.assoc, α.inv.naturality δ, Category.assoc, hcomm,
    ← Category.assoc (f.hom.toFunctor.map β), α.hom.naturality β]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Limit preservation on objects at index categories in a large universe implies the condition at
index categories in the universe `u` of the schemes. -/
theorem isLimitPreservingOnObjects_reindex
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsLimitPreservingOnObjects.{u, max u v w, max u w} B S hS 𝒳 𝒴 f) :
    IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f := by
  intro I _ _ D c hc i y x γ hγ
  let e := ULiftHomULiftCategory.equiv.{max u w, max u v w} I
  let J := ULiftHom.{max u w} (ULift.{max u v w} I)
  let q : J ⥤ I := e.inverse
  have : IsCofiltered J := IsCofiltered.of_equivalence e
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone (c.whisker q)) :=
    (Functor.Initial.isLimitWhiskerEquiv q
      ((BigAffineFppf.toScheme B S hS).mapCone c)).symm hc
  obtain ⟨j, a, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ :=
    hf J (q ⋙ D) (c.whisker q) hc' (e.functor.obj i) y x γ hγ
  exact ⟨q.obj j, q.map a, x', xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩

/-- If `f : 𝒳 ⟶ 𝒴` is limit preserving on objects, then the first projection of the canonical
2-commutative square over the cospan `(g, f)` — the base change of `f` along `g : 𝒵 ⟶ 𝒴`, seen as
a 1-morphism to `𝒵` — is limit preserving on objects. -/
theorem isLimitPreservingOnObjects_twoFibreProductSquareFst
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hf : IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f) :
    IsLimitPreservingOnObjects.{u, u, u} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt 𝒵
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).fst := by
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f
  let Q' := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g
  let r : Q'.pt.val ⥤ᵇ Q.pt.val :=
    { toFunctor := TwoFibreProductOver.swap _ _ _ _ _
      w := rfl }
  have hp : IsLimitPreservingOnObjects.{u, u, u} B S hS Q'.pt 𝒵 Q'.snd :=
    isLimitPreservingOnObjects_baseChange B S hS 𝒳 𝒴 𝒵 f g hf
  intro I _ _ D c hc i y x γ hγ
  let x' : Q'.pt.val.p.Fiber c.pt.obj := ⟨TwoFibreProductOver.swap _ _ _ _ _ |>.obj x.1, x.2⟩
  obtain ⟨j, a, z, zU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ := hp I D c hc i y x' γ hγ
  have hδ' : Q.pt.val.p.IsStronglyCartesian
      ((BigAffineFppf.inclusion B S hS).map (c.π.app j)) (r.toFunctor.map δ) := by
    have : Q'.pt.val.p.IsHomLift
        ((BigAffineFppf.inclusion B S hS).map (c.π.app j)) δ := hδ.toIsHomLift
    have : Q.pt.val.p.IsHomLift
        ((BigAffineFppf.inclusion B S hS).map (c.π.app j))
        (r.toFunctor.map δ) := BasedFunctor.preserves_isHomLift r _ _
    exact Q.pt.2.isStronglyCartesian_homLift _ _
  have hβ' : Q.pt.val.p.IsHomLift (𝟙 c.pt.obj) (r.toFunctor.map β) := by
    have : Q'.pt.val.p.IsHomLift (𝟙 c.pt.obj) β := hβ
    exact BasedFunctor.preserves_isHomLift r _ _
  have hβiso' : IsIso (r.toFunctor.map β) := inferInstance
  exact ⟨j, a, ⟨r.toFunctor.obj z.1, z.2⟩, ⟨r.toFunctor.obj zU.1, zU.2⟩,
    r.toFunctor.map δ, r.toFunctor.map β, γ', hδ', hβ', hβiso', hγ', hcomm⟩

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A smooth 1-morphism of categories fibred in groupoids is limit preserving on objects. -/
theorem isLimitPreservingOnObjects_of_isRelativelySmooth
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRelativelySmooth B S hS f) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS 𝒳 𝒴 f :=
  (isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS 𝒳 𝒴 f hf.1).mpr
    fun U y hy F hF e ↦ Space.isLocallyOfFinitePresentation_of_isSmooth B S hS (hf.2 U y hy F hF e)

section Presheaf

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The element of `F` over `U` named by an object of the fibre over `U` of the category fibred
in groupoids attached to the set-valued presheaf `F`. An object of that category is a pair
`(V, x)` with `x : F(V)`, and lying in the fibre over `U` means `V = U`. -/
def presheafFiberElement (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {U : BigFppfOver B S hS} (x : (fibredCategory B S hS F).val.p.Fiber U) :
    F.obj (Opposite.op U) :=
  x.2 ▸ Discrete.as (show Discrete (F.obj (Opposite.op x.1.base)) from x.1.fiber)

/-- A morphism of the category fibred in groupoids attached to `F` lying over `a : U ⟶ V`
restricts the element named by its target to the element named by its source. -/
theorem presheafFiberElement_map (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {U V : BigFppfOver B S hS} (a : U ⟶ V)
    (x : (fibredCategory B S hS F).val.p.Fiber U)
    (y : (fibredCategory B S hS F).val.p.Fiber V) (δ : x.1 ⟶ y.1)
    (hδ : (fibredCategory B S hS F).val.p.IsHomLift a δ) :
    F.map a.op (presheafFiberElement B S hS F y) = presheafFiberElement B S hS F x := by
  rcases x with ⟨⟨U', x⟩, hx⟩
  rcases y with ⟨⟨V', y⟩, hy⟩
  change U' = U at hx
  change V' = V at hy
  subst U' V'
  have hbase : δ.base = a :=
    (IsHomLift.fac' (fibredCategory B S hS F).val.p a δ).trans
      (by change (eqToHom (rfl : U = U)) ≫ a ≫ eqToHom (rfl : V = V) = a; simp)
  have hd := @Discrete.eq_of_hom _
    (show Discrete (F.obj (Opposite.op U)) from x)
    (Discrete.mk (F.map δ.base.op y.as)) δ.fiber
  change x.as = F.map δ.base.op y.as at hd
  simpa only [presheafFiberElement, hbase] using hd.symm

/-- The element named by an object of the fibre is read off its second component. -/
theorem presheafFiberElement_eq_of_heq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {U : BigFppfOver B S hS} (x : (fibredCategory B S hS F).val.p.Fiber U)
    (v : F.obj (Opposite.op U)) (h : HEq x.1.fiber (Discrete.mk v)) :
    presheafFiberElement B S hS F x = v := by
  rcases x with ⟨⟨U', x⟩, hx⟩
  change U' = U at hx
  subst U'
  exact congrArg Discrete.as (eq_of_heq h)

/-- The 1-morphism associated with a map `a : F ⟶ G` of set-valued presheaves acts on the
elements named by objects of the fibres as `a` itself. -/
theorem presheafFiberElement_associatedMap (a : F ⟶ G)
    {U : BigFppfOver B S hS} (x : (fibredCategory B S hS F).val.p.Fiber U) :
    presheafFiberElement B S hS G
        ((Functor.fiberFunctorOfCompEq (associatedMap B S hS a).1.hom.w U).obj x) =
      a.app (Opposite.op U) (presheafFiberElement B S hS F x) := by
  apply presheafFiberElement_eq_of_heq
  rcases x with ⟨⟨U', x⟩, hx⟩
  change U' = U at hx
  subst U'
  exact (associatedMap B S hS a).2 ⟨U, x⟩

/-- The morphism of the category fibred in groupoids attached to `F` lying over `a : U ⟶ V`
witnessing that the element named by `y` restricts to the element named by `x`. -/
def presheafFiberHom (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {U V : BigFppfOver B S hS} (a : U ⟶ V)
    (x : (fibredCategory B S hS F).val.p.Fiber U)
    (y : (fibredCategory B S hS F).val.p.Fiber V)
    (h : F.map a.op (presheafFiberElement B S hS F y) = presheafFiberElement B S hS F x) :
    {δ : x.1 ⟶ y.1 // (fibredCategory B S hS F).val.p.IsHomLift a δ} := by
  rcases x with ⟨⟨U', x⟩, hx⟩
  rcases y with ⟨⟨V', y⟩, hy⟩
  change U' = U at hx
  change V' = V at hy
  subst U' V'
  refine ⟨{ base := a, fiber := Discrete.eqToHom h.symm }, ?_⟩
  exact IsHomLift.of_fac _ _ _ rfl rfl
    (by change a = (eqToHom (rfl : U = U)) ≫ a ≫ eqToHom (rfl : V = V); simp)

/-- A morphism of algebraic spaces whose associated 1-morphism of categories fibred in groupoids
is limit preserving on objects is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_of_associatedMap
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (a : F ⟶ G)
    (ha : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (fibredCategory B S hS F) (fibredCategory B S hS G) (associatedMap B S hS a).1) :
    Space.IsLocallyOfFinitePresentation B S hS a := by
  apply Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B S hS hF hG a
  intro I _ _ D c hc hD hpt x y hxy
  obtain ⟨i, yi, rfl⟩ := Types.jointly_surjective' y
  rw [colimit.ι_desc_apply] at hxy
  let D' : I ⥤ BigAffineFppf B S hS :=
    { obj := fun i ↦ ⟨D.obj i, hD i⟩
      map := fun a ↦ ObjectProperty.homMk (D.map a) }
  let c' : Cone D' :=
    { pt := ⟨c.pt, hpt⟩
      π := { app := fun i ↦ ObjectProperty.homMk (c.π.app i)
             naturality := fun i j a ↦ by
               apply ObjectProperty.hom_ext
               change c.π.app j = c.π.app i ≫ D.map a
               exact (c.w a).symm } }
  let X := fibredCategory B S hS F
  let Y := fibredCategory B S hS G
  let q := (associatedMap B S hS a).1
  let xF : X.val.p.Fiber c.pt := ⟨⟨c.pt, Discrete.mk x⟩, rfl⟩
  let yG : Y.val.p.Fiber (D.obj i.unop) := ⟨⟨D.obj i.unop, Discrete.mk yi⟩, rfl⟩
  let qx : Y.val.p.Fiber c.pt := (Functor.fiberFunctorOfCompEq q.hom.w c.pt).obj xF
  have hqx : G.map (c.π.app i.unop).op (presheafFiberElement B S hS G yG) =
      presheafFiberElement B S hS G qx := by
    rw [presheafFiberElement_associatedMap]
    exact hxy.symm
  let γ := presheafFiberHom B S hS G (c.π.app i.unop) qx yG hqx
  have hγ : Y.val.p.IsStronglyCartesian (c.π.app i.unop) γ.1 := by
    have := γ.2
    exact Y.2.isStronglyCartesian_homLift _ _
  obtain ⟨j, b, xj, xU, δ, β, γ', hδ, hβ, hβiso, hγ', hcomm⟩ :=
    ha I D' c' hc i.unop yG xF γ.1 hγ
  refine ⟨colimit.ι (D.op ⋙ F) (Opposite.op j) (presheafFiberElement B S hS F xj), ?_, ?_⟩
  · rw [colimit.ι_desc_apply]
    have hδ' := presheafFiberElement_map B S hS F (c.π.app j) xU xj δ hδ.toIsHomLift
    have hβ' := presheafFiberElement_map B S hS F (𝟙 c.pt) xU xF β hβ
    change F.map (c.π.app j).op (presheafFiberElement B S hS F xj) = x
    have hβ'' : presheafFiberElement B S hS F xF = presheafFiberElement B S hS F xU := by
      simpa using hβ'
    exact hδ'.trans hβ''.symm
  · rw [← CategoryTheory.comp_apply, ι_colimMap, CategoryTheory.comp_apply]
    have hγ'' := presheafFiberElement_map B S hS G (D.map b)
      ((Functor.fiberFunctorOfCompEq q.hom.w (D.obj j)).obj xj) yG γ' hγ'.toIsHomLift
    rw [presheafFiberElement_associatedMap] at hγ''
    change colimit.ι (D.op ⋙ G) (Opposite.op j)
      (a.app (Opposite.op (D.obj j)) (presheafFiberElement B S hS F xj)) = _
    rw [← hγ'', ← CategoryTheory.comp_apply]
    exact ConcreteCategory.congr_hom (colimit.w (D.op ⋙ G) b.op) yi

end Presheaf

/-- A 1-morphism of algebraic stacks over `S` which is limit preserving on objects, at index
categories in the universe `u` of the schemes, is locally of finite presentation. -/
@[stacks 0CMY "the implication (2) => (3) only"]
theorem AlgebraicStacks.isLocallyOfFinitePresentation_of_isLimitPreservingOnObjects
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1}
      B S hS 𝒳.val 𝒴.val f.hom) :
    Stack.AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f := by
  intro U V hU hV a b h η ha hb hcomparison
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} b f.hom
  let hQ :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} b f.hom
  let k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f.hom a b h η) Q :=
    CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} b f.hom _
  have hk := isLimitPreservingOnObjects_of_isRelativelySmooth B S hS k.hom
    (hcomparison Q hQ k)
  have hp := BigFppfOver.isLimitPreservingOnObjects_twoFibreProductSquareFst B S hS f.hom b hf
  have hcomp := BigFppfOver.isLimitPreservingOnObjects_comp B S hS _ _ _ k.hom Q.fst hk hp
  exact isLocallyOfFinitePresentation_of_associatedMap B S hS hU hV h
    (BigFppfOver.isLimitPreservingOnObjects_of_iso B S hS k.isoFst.symm hcomp)

end AlgebraicGeometry.Stack

end
