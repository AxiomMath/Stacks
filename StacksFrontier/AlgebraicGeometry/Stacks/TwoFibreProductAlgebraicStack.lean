module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorSheafIndependentBase
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# A 2-fibre product over a stack with representable diagonal is algebraic (Stacks 04TF)

Let `B` be a big fppf site, `S` a scheme contained in it, and let `𝒵` be a stack in groupoids
over the big fppf site of `S` whose diagonal is representable by algebraic spaces. If `𝒳` and
`𝒴` are algebraic stacks over `S` and `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` are 1-morphisms of stacks in
groupoids, then the 2-fibre product `𝒳 ×_{f, 𝒵, g} 𝒴` is an algebraic stack over `S`.

The three clauses of `AlgebraicGeometry.Stack.IsAlgebraicStack` are checked in turn, following
the source.

* The stack condition is Stacks 02ZL. The library's `@[stacks 02ZL]`
  `CategoryTheory.TwoFibreProductOver.isStack_isFiberedInGroupoids_structureFunctor` proves it
  in the sieve-indexed rendering `CategoryTheory.Functor.IsStack` of Stacks 026F, while
  `AlgebraicGeometry.Stack.IsAlgebraicStack` asks for the family-indexed
  `CategoryTheory.Functor.IsStackInGroupoids` of Stacks 02ZI, and the bridge from the one to the
  other runs the wrong way. So the two conditions of the family-indexed form are proved here
  directly from those of the factors: the isomorphism-sheaf condition from the morphism-presheaf
  sheaf condition of the 2-fibre product, and effective descent by descending the two components
  of a descent datum separately and gluing their comparison isomorphisms.
* The diagonal condition is condition (2) of Stacks 045G for the 2-fibre product: the source's
  cartesian square of `Isom`-sheaves is the pullback description of the morphism presheaf of the
  2-fibre product, and the three corners are algebraic spaces by condition (2) for `𝒳`, `𝒴` and
  `𝒵`, so the pullback is one by Stacks 02X2.
* The presentation is the composite of base changes of presentations of `𝒳` and of `𝒴`, as in
  the source. The resulting 1-morphism has an algebraic space as source rather than a scheme,
  and the final step of the source — "choosing a scheme `W` and a surjective étale morphism
  `W → F`" — is
  `AlgebraicGeometry.Stack.exists_schemePresentation_of_isRepresentableByAlgebraicSpace`.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_of_forall_nonempty_equivalenceOver_fst`: the
  relative property of Stacks 03YK transports along a family of equivalences of the first
  projections of the 2-fibre products it quantifies over.
* `AlgebraicGeometry.Stack.exists_schemePresentation_of_isRepresentableByAlgebraicSpace`: a
  1-morphism to `𝒳` which is representable by algebraic spaces, surjective and smooth, and whose
  source is representable by an algebraic space, yields a presentation of `𝒳` by a scheme.
* `CategoryTheory.TwoFibreProductOver.isStackInGroupoids_structureFunctor`: the 2-fibre product
  of stacks in groupoids is a stack in groupoids, in the family-indexed sense of Stacks 02ZI and
  at every index universe `t` for the covering families.
* `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`: **Stacks 04TF**.

## Implementation notes

The source's last step is isolated as
`exists_schemePresentation_of_isRepresentableByAlgebraicSpace` because it is the only place a
presentation by an algebraic space has to be replaced by a presentation by a scheme. Its proof
composes a scheme atlas of the representing algebraic space — which exists because the stack of
an algebraic space is an algebraic stack, `AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`
— with the given 1-morphism, by Stacks 0301 for representability and Stacks 045B for the
surjectivity and smoothness. Transporting the given 1-morphism from its source to the category of
elements of the representing algebraic space is the cheap half of Stacks 0457, i.e.
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_fst_of_equivalence_source`, for which
`relativeProperty_of_forall_nonempty_equivalenceOver_fst` is the relative-property companion of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst`.

This is deliberately *not* Stacks 05UL, whose conclusion is the same presentation clause from the
same hypotheses: 05UL also proves the diagonal clause, and that is the part which needs
Bootstrap 04S6. Here the diagonal clause is already available for the 2-fibre product, so only
the presentation clause is needed and no bootstrap is involved.

The canonical 2-fibre product square and its universal property are
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` and
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare`, so the base changes
of the two presentations are instances of Stacks 0302 and Stacks 045C. The fppf
`CategoryTheory.MorphismProperty.IsLocalAtTarget` instances that Stacks 045B and Stacks 045C ask
for are the existing `@[stacks 0429 "the fppf precoverage"]` and
`@[stacks 041Q "the fppf precoverage"]`, so no comparison of the fppf and fpqc precoverages is
made here.

## References

* [Stacks Project, Tag 02ZL](https://stacks.math.columbia.edu/tag/02ZL)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

-- The objects and morphisms of `CategoryTheory.TwoFibreProductOver` are spelled through
-- `CategoryTheory.Functor.pullbackFiber`, `CategoryTheory.Functor.Fiber.fiberInclusion` and
-- `CategoryTheory.Functor.fiberFunctorOfCompEq`, so the instance arguments of
-- `CategoryTheory.Functor.IsHomLift` and `CategoryTheory.Functor.IsCartesian` are only found
-- after unfolding those. Each section therefore makes exactly the constructions its own
-- declarations are phrased in locally `implicit_reducible`, as
-- `StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheafVertHom` does for the same reason.

universe u w v₁ w₁

section MapDescent
universe vC vD vE uC uD uE t
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E]
variable {p : D ⥤ C} {q : E ⥤ C} (F : D ⥤ E) (hF : F ⋙ q = p)
  (hq : q.IsFiberedInGroupoids)
private lemma map_homLift {V U : C} (f : V ⟶ U) {x y : D}
    (hx : p.obj x = V) (hy : p.obj y = U) (φ : x ⟶ y)
    (hφ : p.IsHomLift (eqToHom hx ≫ f ≫ eqToHom hy.symm) φ) :
    q.IsHomLift (eqToHom ((Functor.congr_obj hF x).trans hx) ≫ f ≫
      eqToHom ((Functor.congr_obj hF y).trans hy).symm) (F.map φ) := by
  subst p
  have := hφ
  exact Functor.isHomLift_map_of_comp_eq rfl _ φ

private def mapRestriction {V U : C} {f : V ⟶ U} {x : D} {hx : p.obj x = U}
    (r : p.Restriction f x hx) :
    q.Restriction f (F.obj x) ((Functor.congr_obj hF x).trans hx) where
  pt := F.obj r.pt
  hpt := (Functor.congr_obj hF r.pt).trans r.hpt
  hom := F.map r.hom
  isHomLift := map_homLift F hF f r.hpt hx r.hom r.isHomLift
  isCart := by
    have := map_homLift F hF f r.hpt hx r.hom r.isHomLift
    exact hq.isStronglyCartesian_homLift _ _

attribute [local implicit_reducible] mapRestriction

private lemma compTo_homLift {W V U : C} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f) {x : D} {hx : p.obj x = U}
    (r : p.Restriction f x hx) (s : p.Restriction h x hx) :
    p.IsHomLift (eqToHom s.hpt ≫ g ≫ eqToHom r.hpt.symm)
      (Functor.Restriction.compTo p g f hh r s) := by
  unfold Functor.Restriction.compTo
  infer_instance

private lemma map_compTo {W V U : C} (g : W ⟶ V) (f : V ⟶ U)
    {h : W ⟶ U} (hh : h = g ≫ f) {x : D} {hx : p.obj x = U}
    (r : p.Restriction f x hx) (s : p.Restriction h x hx) :
    F.map (Functor.Restriction.compTo p g f hh r s) =
      Functor.Restriction.compTo q g f hh (mapRestriction F hF hq r)
        (mapRestriction F hF hq s) := by
  have := map_homLift F hF g s.hpt r.hpt _ (compTo_homLift g f hh r s)
  have := compTo_homLift g f hh (mapRestriction F hF hq r) (mapRestriction F hF hq s)
  have := (mapRestriction F hF hq r).isCart
  apply Functor.IsStronglyCartesian.ext q
    (eqToHom (mapRestriction F hF hq r).hpt ≫ f ≫
      eqToHom ((Functor.congr_obj hF x).trans hx).symm)
    (mapRestriction F hF hq r).hom
    (eqToHom (mapRestriction F hF hq s).hpt ≫ g ≫
      eqToHom (mapRestriction F hF hq r).hpt.symm)
  rw [Functor.Restriction.compTo_hom]
  exact (F.map_comp _ _).symm.trans
    (congrArg F.map (Functor.Restriction.compTo_hom p g f hh r s))

private lemma map_isRestrictionOf
    {W V Ux Uy : C} (g : W ⟶ V) {fx : V ⟶ Ux} {fy : V ⟶ Uy}
    {hx' : W ⟶ Ux} {hy' : W ⟶ Uy} (hfx : hx' = g ≫ fx) (hfy : hy' = g ≫ fy)
    {x y : D} {hx : p.obj x = Ux} {hy : p.obj y = Uy}
    (xr : p.Restriction fx x hx) (yr : p.Restriction fy y hy)
    (xs : p.Restriction hx' x hx) (ys : p.Restriction hy' y hy)
    (α : xr.pt ⟶ yr.pt) (β : xs.pt ⟶ ys.pt)
    (h : Functor.IsRestrictionOf p g hfx hfy xr yr xs ys α β) :
    Functor.IsRestrictionOf q g hfx hfy (mapRestriction F hF hq xr)
      (mapRestriction F hF hq yr) (mapRestriction F hF hq xs)
      (mapRestriction F hF hq ys) (F.map α) (F.map β) := by
  unfold Functor.IsRestrictionOf
  rw [← map_compTo, ← map_compTo, ← F.map_comp, ← F.map_comp]
  exact congrArg F.map h

private lemma map_fibreHom {U : C} {x y : D} (hx : p.obj x = U) (hy : p.obj y = U)
    (φ : x ⟶ y) (hφ : Functor.FibreHom p x y hx hy φ) :
    Functor.FibreHom q (F.obj x) (F.obj y) ((Functor.congr_obj hF x).trans hx)
      ((Functor.congr_obj hF y).trans hy) (F.map φ) := by
  have h : p.IsHomLift (eqToHom hx ≫ 𝟙 U ≫ eqToHom hy.symm) φ := by
    simpa only [Category.id_comp] using hφ
  simpa only [Category.id_comp] using map_homLift F hF (𝟙 U) hx hy φ h

private def mapDescent
    {U : C} {I : Type t} {V : I → C} {f : ∀ i, V i ⟶ U}
    {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
    {Vijk : I → I → I → C}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
    {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
    (d : p.DescentDatum V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    q.DescentDatum V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ where
  x i := F.obj (d.x i)
  hx i := (Functor.congr_obj hF (d.x i)).trans (d.hx i)
  xrij i j := mapRestriction F hF hq (d.xrij i j)
  xrji i j := mapRestriction F hF hq (d.xrji i j)
  φ i j := F.map (d.φ i j)
  φ_fibreHom i j := map_fibreHom F hF _ _ _ (d.φ_fibreHom i j)
  φ_iso i j := by have := d.φ_iso i j; infer_instance
  wi i j k := mapRestriction F hF hq (d.wi i j k)
  wj i j k := mapRestriction F hF hq (d.wj i j k)
  wk i j k := mapRestriction F hF hq (d.wk i j k)
  αij i j k := F.map (d.αij i j k)
  αjk i j k := F.map (d.αjk i j k)
  αik i j k := F.map (d.αik i j k)
  αij_restr i j k := by
    apply map_isRestrictionOf F hF hq
    exact d.αij_restr i j k
  αjk_restr i j k := by
    apply map_isRestrictionOf F hF hq
    exact d.αjk_restr i j k
  s₁₃ := d.s₁₃
  hs₁₃₁ := d.hs₁₃₁
  hs₁₃₂ := d.hs₁₃₂
  αik_restr i j k := by
    apply map_isRestrictionOf F hF hq
    exact d.αik_restr i j k
  cocycle i j k := (congrArg F.map (d.cocycle i j k)).trans (F.map_comp _ _)

end MapDescent

section DescentCocone
universe vC vD uC uD t
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {p : D ⥤ C}
private def restrictionOfHomLift (hp : p.IsFiberedInGroupoids)
    {V U : C} {f : V ⟶ U} {x y : D} (hx : p.obj x = V) (hy : p.obj y = U)
    (φ : x ⟶ y) (hφ : p.IsHomLift f φ) : p.Restriction f y hy where
  pt := x
  hpt := hx
  hom := φ
  isHomLift := by
    have := hφ
    apply IsHomLift.of_fac' p _ φ rfl rfl
    simpa using IsHomLift.fac' p f φ
  isCart := by
    have := hφ
    have hm : p.map φ = eqToHom hx ≫ f ≫ eqToHom hy.symm := IsHomLift.fac' p f φ
    rw [← hm]
    exact hp.isStronglyCartesian φ

attribute [local implicit_reducible] restrictionOfHomLift

private lemma compTo_id {V U : C} (g : V ⟶ U) {h : V ⟶ U}
    (hh : h = g ≫ 𝟙 U) {x : D} {hx : p.obj x = U} (r : p.Restriction h x hx) :
    Functor.Restriction.compTo p g (𝟙 U) hh (Functor.Restriction.id p x hx) r = r.hom := by
  simpa only [Functor.Restriction.id, Category.comp_id] using
    Functor.Restriction.compTo_hom p g (𝟙 U) hh (Functor.Restriction.id p x hx) r

variable {U : C} {I : Type t} {V : I → C} {f : ∀ i, V i ⟶ U}
    {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
    {Vijk : I → I → I → C}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
    {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
variable (d : p.DescentDatum V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

private lemma exists_descentCocone_of_isEffective (hd : d.IsEffective) :
    ∃ (x : D) (_hx : p.obj x = U) (a : ∀ i, d.x i ⟶ x),
      (∀ i, p.IsHomLift (f i) (a i)) ∧
      ∀ i j, d.φ i j ≫ (d.xrji i j).hom ≫ a j = (d.xrij i j).hom ≫ a i := by
  obtain ⟨x, hx, xr, ψ, hψ, hi, hc⟩ := hd
  have hψl (i : I) : p.IsHomLift (𝟙 (V i)) (ψ i) := (Functor.fibreHomMk (hψ i)).2
  let (i : I) := hi i
  let a (i : I) := inv (ψ i) ≫ (xr i).hom
  have ha (i : I) : p.IsHomLift (f i) (a i) := by
    have : p.IsHomLift (𝟙 (V i)) (asIso (ψ i)).hom := hψl i
    have := IsHomLift.lift_id_inv p (V i) (asIso (ψ i))
    have := (xr i).isHomLift_hom
    exact Functor.isHomLift_of_eq (inferInstance : p.IsHomLift (𝟙 (V i) ≫ f i) (a i))
      (Category.id_comp _)
  refine ⟨x, hx, a, ha, ?_⟩
  intro i j
  obtain ⟨r, ψi, ψj, hψi, hψj, hii, hij, hri, hrj, heq⟩ := hc i j
  have := hii
  have hri' : ψi ≫ (d.xrij i j).hom =
      Functor.Restriction.compTo p (pr₁ i j) (f i) rfl (xr i) r ≫ ψ i := by
    simpa only [Functor.IsRestrictionOf, compTo_id] using hri
  have hrj' : ψj ≫ (d.xrji i j).hom =
      Functor.Restriction.compTo p (pr₂ i j) (f j) (hVij i j).w (xr j) r ≫ ψ j := by
    simpa only [Functor.IsRestrictionOf, compTo_id] using hrj
  have hi' : ψi ≫ (d.xrij i j).hom ≫ a i = r.hom := by
    dsimp [a]
    rw [← Category.assoc, hri']
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact Functor.Restriction.compTo_hom p _ _ _ _ _
  have hj' : ψj ≫ (d.xrji i j).hom ≫ a j = r.hom := by
    dsimp [a]
    rw [← Category.assoc, hrj']
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact Functor.Restriction.compTo_hom p _ _ _ _ _
  apply (cancel_epi ψi).mp
  simpa only [← Category.assoc, heq] using hj'.trans hi'.symm

private lemma compTo_eq (hp : p.IsFiberedInGroupoids)
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f)
    {x : D} {hx : p.obj x = U} (r : p.Restriction f x hx) (s : p.Restriction h x hx)
    (m : s.pt ⟶ r.pt) (hm : p.IsHomLift g m) (hfac : m ≫ r.hom = s.hom) :
    Functor.Restriction.compTo p g f hh r s = m := by
  let := hp.isFibered
  have := r.isStronglyCartesian_hom
  have := Functor.Restriction.isHomLift_compTo g f hh r s
  have := hm
  apply Functor.IsStronglyCartesian.ext p f r.hom g
  exact (Functor.Restriction.compTo_hom p g f hh r s).trans hfac.symm

private lemma compTo_restrictionOfHomLift_eq (hp : p.IsFiberedInGroupoids) {x : D}
    {hx : p.obj x = U} {a : ∀ i, d.x i ⟶ x} (ha : ∀ i, p.IsHomLift (f i) (a i))
    (hc : ∀ i j, d.φ i j ≫ (d.xrji i j).hom ≫ a j = (d.xrij i j).hom ≫ a i) (i j : I)
    (hal : p.IsHomLift (pr₁ i j ≫ f i) ((d.xrij i j).hom ≫ a i)) :
    Functor.Restriction.compTo p (pr₁ i j) (f i) rfl
        (restrictionOfHomLift hp (d.hx i) hx (a i) (ha i))
        (restrictionOfHomLift hp (d.xrij i j).hpt hx _ hal) = (d.xrij i j).hom ∧
      Functor.Restriction.compTo p (pr₂ i j) (f j) (hVij i j).w
        (restrictionOfHomLift hp (d.hx j) hx (a j) (ha j))
        (restrictionOfHomLift hp (d.xrij i j).hpt hx _ hal) =
        d.φ i j ≫ (d.xrji i j).hom := by
  have hφ : p.IsHomLift (𝟙 (Vij i j)) (d.φ i j) := (Functor.fibreHomMk (d.φ_fibreHom i j)).2
  have := (d.xrji i j).isHomLift_hom
  exact ⟨compTo_eq hp _ _ _ _ _ _ (d.xrij i j).isHomLift_hom rfl,
    compTo_eq hp _ _ _ _ _ _
      (Functor.isHomLift_of_eq (inferInstance : p.IsHomLift (𝟙 _ ≫ pr₂ i j) _) (by simp))
      ((Category.assoc _ _ _).trans (hc i j))⟩

private lemma isEffective_of_descentCocone (hp : p.IsFiberedInGroupoids)
    (x : D) (hx : p.obj x = U) (a : ∀ i, d.x i ⟶ x)
    (ha : ∀ i, p.IsHomLift (f i) (a i))
    (hc : ∀ i j, d.φ i j ≫ (d.xrji i j).hom ≫ a j = (d.xrij i j).hom ≫ a i) :
    d.IsEffective := by
  let := hp.isFibered
  let r (i : I) := restrictionOfHomLift hp (d.hx i) hx (a i) (ha i)
  refine ⟨x, hx, r, fun i => 𝟙 (d.x i), ?_, ?_, ?_⟩
  · intro i
    exact Functor.fibreHom_of_isHomLift_id (d.hx i) (d.hx i) (IsHomLift.id (d.hx i))
  · intro i
    show IsIso (𝟙 (d.x i))
    infer_instance
  · intro i j
    have := (d.xrij i j).isHomLift_hom
    have := ha i
    have hal : p.IsHomLift (pr₁ i j ≫ f i) ((d.xrij i j).hom ≫ a i) := inferInstance
    obtain ⟨hs₁, hs₂⟩ := compTo_restrictionOfHomLift_eq d hp ha hc i j hal
    let s := restrictionOfHomLift hp (d.xrij i j).hpt hx _ hal
    refine ⟨s, 𝟙 _, d.φ i j, ?_, d.φ_fibreHom i j, inferInstance, d.φ_iso i j, ?_, ?_, ?_⟩
    · exact Functor.fibreHom_of_isHomLift_id _ _ (IsHomLift.id (d.xrij i j).hpt)
    · show _ ≫ _ = _ ≫ 𝟙 _
      simpa only [Category.id_comp, Category.comp_id] using
        (compTo_id (pr₁ i j) (by simp) (d.xrij i j)).trans hs₁.symm
    · show _ ≫ _ = _ ≫ 𝟙 _
      simpa only [Category.comp_id] using
        (congrArg (fun k => d.φ i j ≫ k)
          (compTo_id (pr₂ i j) (by simp) (d.xrji i j))).trans hs₂.symm
    · simp

end DescentCocone

/-- The comparison isomorphism of an object of a 2-fibre product lies over the identity of its
base. -/
private lemma isHomLift_id_iso_hom {C X Y Z : Type*} [Category C] [Category X] [Category Y]
    [Category Z] {pX : X ⥤ C} {pY : Y ⥤ C} {pZ : Z ⥤ C} {F : X ⥤ Z} {G : Y ⥤ Z} {W : C}
    (P : TwoFibreProductOver pX pY pZ F G)
    (hP : (TwoFibreProductOver.structureFunctor pX pY pZ F G).obj P = W) :
    pZ.IsHomLift (𝟙 W) P.iso.hom := by
  have := P.vertical
  subst hP
  exact this

section ProductDescent
universe uC uX uY uZ vC vX vY vZ t
variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
variable (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
  (F : X ⥤ Z) (G : Y ⥤ Z) (hF : F ⋙ pZ = pX) (hG : G ⋙ pZ = pY)
  (J : GrothendieckTopology C)
  (hX : pX.IsStackInGroupoids.{t} J) (hY : pY.IsStackInGroupoids.{t} J)
  (hZ : pZ.IsStackInGroupoids.{t} J)
local notation "pP" => TwoFibreProductOver.structureFunctor pX pY pZ F G
local notation "πX" => TwoFibreProductOver.fst pX pY pZ F G
local notation "πY" => TwoFibreProductOver.snd pX pY pZ F G
variable {U : C} {I : Type t} {V : I → C} {f : ∀ i, V i ⟶ U}
    {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
    {Vijk : I → I → I → C}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
    {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

attribute [local implicit_reducible] mapRestriction restrictionOfHomLift mapDescent
  TwoFibreProductOver.fst TwoFibreProductOver.snd

include hF hG hX hY hZ in
private lemma productDescent_isEffective
    (hf : Sieve.ofArrows V f ∈ J U)
    (d : (pP).DescentDatum V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    d.IsEffective := by
  let hPX := hX.isFiberedInGroupoids
  let hPY := hY.isFiberedInGroupoids
  let hPZ := hZ.isFiberedInGroupoids
  let hp := TwoFibreProductOver.isFiberedInGroupoids pX pY pZ F G hPX hPY hPZ hF hG
  let dX := mapDescent πX TwoFibreProductOver.fst_comp_eq hPX d
  let dY := mapDescent πY TwoFibreProductOver.snd_comp_eq hPY d
  obtain ⟨x, hx, a, ha, hac⟩ := exists_descentCocone_of_isEffective dX
    (hX.effective_descent V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃ dX)
  obtain ⟨y, hy, b, hb, hbc⟩ := exists_descentCocone_of_isEffective dY
    (hY.effective_descent V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃ dY)
  let rx i := restrictionOfHomLift hPX (dX.hx i) hx (a i) (ha i)
  let ry i := restrictionOfHomLift hPY (dY.hx i) hy (b i) (hb i)
  have hal i j : pX.IsHomLift (pr₁ i j ≫ f i) ((dX.xrij i j).hom ≫ a i) := by
    have := (dX.xrij i j).isHomLift_hom
    have := ha i
    infer_instance
  have hbl i j : pY.IsHomLift (pr₁ i j ≫ f i) ((dY.xrij i j).hom ≫ b i) := by
    have := (dY.xrij i j).isHomLift_hom
    have := hb i
    infer_instance
  let rxx i j := restrictionOfHomLift hPX (dX.xrij i j).hpt hx _ (hal i j)
  let ryy i j := restrictionOfHomLift hPY (dY.xrij i j).hpt hy _ (hbl i j)
  choose cx₁ cx₂ using fun i j => compTo_restrictionOfHomLift_eq dX hPX ha hac i j (hal i j)
  choose cy₁ cy₂ using fun i j => compTo_restrictionOfHomLift_eq dY hPY hb hbc i j (hbl i j)
  obtain ⟨θ, hθ, -⟩ := hZ.isom_isSheaf (F.obj x) (G.obj y)
    ((Functor.congr_obj hF x).trans hx) ((Functor.congr_obj hG y).trans hy)
    V f hf Vij pr₁ pr₂ hVij
    (fun i => mapRestriction F hF hPZ (rx i))
    (fun i => mapRestriction G hG hPZ (ry i))
    (fun i j => mapRestriction F hF hPZ (rxx i j))
    (fun i j => mapRestriction G hG hPZ (ryy i j))
    (fun i => (d.x i).iso.hom)
    (fun i => Functor.fibreHom_of_isHomLift_id _ _ (isHomLift_id_iso_hom _ (d.hx i)))
    (by intro i; infer_instance) (by
      intro i j
      refine ⟨(d.xrij i j).pt.iso.hom, ?_, ?_, ?_⟩
      · exact Functor.fibreHom_of_isHomLift_id _ _
          (isHomLift_id_iso_hom _ (d.xrij i j).hpt)
      · unfold Functor.IsRestrictionOf
        rw [← map_compTo, ← map_compTo, cx₁, cy₁]
        exact (d.xrij i j).hom.w.symm
      · unfold Functor.IsRestrictionOf
        rw [← map_compTo, ← map_compTo, cx₂, cy₂]
        simp only [Functor.map_comp]
        have hh := (d.φ i j ≫ (d.xrji i j).hom).w.symm
        change (d.xrij i j).pt.iso.hom ≫ G.map ((d.φ i j).b ≫ (d.xrji i j).hom.b) =
          F.map ((d.φ i j).a ≫ (d.xrji i j).hom.a) ≫ (d.x j).iso.hom at hh
        show (d.xrij i j).pt.iso.hom ≫ G.map (d.φ i j).b ≫ G.map (d.xrji i j).hom.b =
          (F.map (d.φ i j).a ≫ F.map (d.xrji i j).hom.a) ≫ (d.x j).iso.hom
        simpa only [Functor.map_comp, Category.assoc] using hh)
  have ht : IsIso θ := hθ.2.1
  let z : TwoFibreProductOver pX pY pZ F G :=
    { base := U
      x := x
      y := y
      hx := hx
      hy := hy
      iso := asIso θ
      vertical := (Functor.fibreHomMk hθ.1).2 }
  let c (i : I) : d.x i ⟶ z := TwoFibreProductOver.Hom.mk' (a i) (b i) (by
    have := ha i
    have := hb i
    rw [IsHomLift.fac' pX (f i) (a i), IsHomLift.fac' pY (f i) (b i)]
    simp [z]) (hθ.2.2 i)
  apply isEffective_of_descentCocone d hp z rfl c
  · intro i
    have := ha i
    apply IsHomLift.of_fac' pP (f i) (c i) (d.hx i) rfl
    show eqToHom (d.x i).hx.symm ≫ pX.map (a i) ≫ eqToHom hx = _
    rw [IsHomLift.fac' pX (f i) (a i)]
    -- `pP.obj z` and `U` are definitionally equal but not syntactically, so the last
    -- `eqToHom` is collapsed at default transparency rather than by `simp`.
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      eqToHom_trans_assoc]
    show eqToHom _ ≫ f i = eqToHom _ ≫ f i ≫ 𝟙 _
    simp
  · intro i j
    exact TwoFibreProductOver.Hom.ext' (hac i j) (hbc i j)
end ProductDescent

section ProductIsom
universe uC uX uY uZ vC vX vY vZ t
variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {Z : Type uZ} [Category.{vZ} Z]
variable (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
  (F : X ⥤ Z) (G : Y ⥤ Z) (hF : F ⋙ pZ = pX) (hG : G ⋙ pZ = pY)
  (J : GrothendieckTopology C)
  (hX : pX.IsStackInGroupoids.{t} J) (hY : pY.IsStackInGroupoids.{t} J)
  (hZ : pZ.IsStackInGroupoids.{t} J)
local notation "pP" => TwoFibreProductOver.structureFunctor pX pY pZ F G
local notation "πX" => TwoFibreProductOver.fst pX pY pZ F G
local notation "πY" => TwoFibreProductOver.snd pX pY pZ F G

attribute [local implicit_reducible] mapRestriction TwoFibreProductOver.fst
  TwoFibreProductOver.snd

include hF hG hX hY hZ in
/-- **The `Isom` presheaves of the 2-fibre product of stacks in groupoids are sheaves.** The
gluing problem projects to gluing problems in `𝒳` and in `𝒴`, whose solutions are the two
components of the glued morphism; they form a morphism of the 2-fibre product because the two
composites around its comparison square solve one and the same gluing problem in `𝒵`. -/
private lemma productIsom_isSheafFor {U : C} (x y : TwoFibreProductOver pX pY pZ F G)
    (hx : (pP).obj x = U) (hy : (pP).obj y = U)
    {I : Type t} (V : I → C) (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U)
    (Vij : I → I → C) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, (pP).Restriction (f i) x hx) (yr : ∀ i, (pP).Restriction (f i) y hy)
    (xrij : ∀ i j, (pP).Restriction (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, (pP).Restriction (pr₁ i j ≫ f i) y hy) :
    Functor.IsomIsSheafFor (pP) x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij := by
  intro φ hφ hφiso hcompat
  let hPX := hX.isFiberedInGroupoids
  let hPY := hY.isFiberedInGroupoids
  let hPZ := hZ.isFiberedInGroupoids
  -- the projected gluing problems in `𝒳` and `𝒴`
  have hfstX := TwoFibreProductOver.fst_comp_eq (p𝒳 := pX) (p𝒴 := pY) (p𝒮 := pZ) (F := F)
    (G := G)
  have hsndY := TwoFibreProductOver.snd_comp_eq (p𝒳 := pX) (p𝒴 := pY) (p𝒮 := pZ) (F := F)
    (G := G)
  obtain ⟨gX, ⟨hgXfib, hgXiso, hgX⟩, hgXuniq⟩ := hX.isom_isSheaf ((πX).obj x) ((πX).obj y)
    ((Functor.congr_obj hfstX x).trans hx) ((Functor.congr_obj hfstX y).trans hy)
    V f hf Vij pr₁ pr₂ hVij
    (fun i => mapRestriction πX hfstX hPX (xr i)) (fun i => mapRestriction πX hfstX hPX (yr i))
    (fun i j => mapRestriction πX hfstX hPX (xrij i j))
    (fun i j => mapRestriction πX hfstX hPX (yrij i j))
    (fun i => (πX).map (φ i)) (fun i => map_fibreHom πX hfstX _ _ _ (hφ i))
    (fun i => by have := hφiso i; infer_instance) (by
      intro i j
      obtain ⟨γ, hγfib, hγ₁, hγ₂⟩ := hcompat i j
      exact ⟨(πX).map γ, map_fibreHom πX hfstX _ _ _ hγfib,
        map_isRestrictionOf πX hfstX hPX _ rfl rfl _ _ _ _ _ _ hγ₁,
        map_isRestrictionOf πX hfstX hPX _ _ _ _ _ _ _ _ _ hγ₂⟩)
  obtain ⟨gY, ⟨hgYfib, hgYiso, hgY⟩, hgYuniq⟩ := hY.isom_isSheaf ((πY).obj x) ((πY).obj y)
    ((Functor.congr_obj hsndY x).trans hx) ((Functor.congr_obj hsndY y).trans hy)
    V f hf Vij pr₁ pr₂ hVij
    (fun i => mapRestriction πY hsndY hPY (xr i)) (fun i => mapRestriction πY hsndY hPY (yr i))
    (fun i j => mapRestriction πY hsndY hPY (xrij i j))
    (fun i j => mapRestriction πY hsndY hPY (yrij i j))
    (fun i => (πY).map (φ i)) (fun i => map_fibreHom πY hsndY _ _ _ (hφ i))
    (fun i => by have := hφiso i; infer_instance) (by
      intro i j
      obtain ⟨γ, hγfib, hγ₁, hγ₂⟩ := hcompat i j
      exact ⟨(πY).map γ, map_fibreHom πY hsndY _ _ _ hγfib,
        map_isRestrictionOf πY hsndY hPY _ rfl rfl _ _ _ _ _ _ hγ₁,
        map_isRestrictionOf πY hsndY hPY _ _ _ _ _ _ _ _ _ hγ₂⟩)
  -- the two composites around the comparison square solve one gluing problem in `𝒵`
  let xZ i := mapRestriction F hF hPZ (mapRestriction πX hfstX hPX (xr i))
  let yZ i := mapRestriction G hG hPZ (mapRestriction πY hsndY hPY (yr i))
  let xZij i j := mapRestriction F hF hPZ (mapRestriction πX hfstX hPX (xrij i j))
  let yZij i j := mapRestriction G hG hPZ (mapRestriction πY hsndY hPY (yrij i j))
  have hvert : ∀ {W : C} (P Q : TwoFibreProductOver pX pY pZ F G) (hP : (pP).obj P = W)
      (hQ : (pP).obj Q = W) (h : P ⟶ Q), Functor.FibreHom (pP) P Q hP hQ h →
      pZ.IsHomLift (𝟙 W) (P.iso.hom ≫ G.map h.b) := by
    intro W P Q hP hQ h hh
    have h₁ := isHomLift_id_iso_hom P hP
    have h₂ : pZ.IsHomLift (𝟙 W) (G.map h.b) :=
      (Functor.fibreHomMk (map_fibreHom G hG _ _ _
        (map_fibreHom πY hsndY hP hQ h hh))).2
    infer_instance
  let ψ i : (xZ i).pt ⟶ (yZ i).pt := (xr i).pt.iso.hom ≫ G.map (φ i).b
  have hψ : ∀ i, Functor.FibreHom pZ (xZ i).pt (yZ i).pt (xZ i).hpt (yZ i).hpt (ψ i) :=
    fun i => Functor.fibreHom_of_isHomLift_id _ _ (hvert _ _ (xr i).hpt (yr i).hpt _ (hφ i))
  have hψiso : ∀ i, IsIso (ψ i) := fun i => by
    have := hφiso i
    have : IsIso (φ i).b := inferInstanceAs (IsIso ((πY).map (φ i)))
    infer_instance
  have hcx : ∀ {W V₀ : C} (g : W ⟶ V₀) (f₀ : V₀ ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f₀)
      (r : (pP).Restriction f₀ x hx) (s : (pP).Restriction h x hx),
      Functor.Restriction.compTo pZ g f₀ hh
          (mapRestriction F hF hPZ (mapRestriction πX hfstX hPX r))
          (mapRestriction F hF hPZ (mapRestriction πX hfstX hPX s)) =
        F.map (Functor.Restriction.compTo (pP) g f₀ hh r s).a := by
    intro W V₀ g f₀ h hh r s
    rw [← map_compTo F hF hPZ, ← map_compTo πX hfstX hPX]
    rfl
  have hcy : ∀ {W V₀ : C} (g : W ⟶ V₀) (f₀ : V₀ ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f₀)
      (r : (pP).Restriction f₀ y hy) (s : (pP).Restriction h y hy),
      Functor.Restriction.compTo pZ g f₀ hh
          (mapRestriction G hG hPZ (mapRestriction πY hsndY hPY r))
          (mapRestriction G hG hPZ (mapRestriction πY hsndY hPY s)) =
        G.map (Functor.Restriction.compTo (pP) g f₀ hh r s).b := by
    intro W V₀ g f₀ h hh r s
    rw [← map_compTo G hG hPZ, ← map_compTo πY hsndY hPY]
    rfl
  obtain ⟨_, -, hθuniq⟩ := hZ.isom_isSheaf (F.obj ((πX).obj x)) (G.obj ((πY).obj y))
    ((Functor.congr_obj hF ((πX).obj x)).trans ((Functor.congr_obj hfstX x).trans hx))
    ((Functor.congr_obj hG ((πY).obj y)).trans ((Functor.congr_obj hsndY y).trans hy))
    V f hf Vij pr₁ pr₂ hVij xZ yZ xZij yZij ψ hψ hψiso (by
      intro i j
      obtain ⟨γ, hγfib, hγ₁, hγ₂⟩ := hcompat i j
      refine ⟨(xrij i j).pt.iso.hom ≫ G.map γ.b,
        Functor.fibreHom_of_isHomLift_id _ _ (hvert _ _ (xrij i j).hpt (yrij i j).hpt _ hγfib),
        ?_, ?_⟩
      · unfold Functor.IsRestrictionOf at hγ₁ ⊢
        rw [hcx, hcy]
        have hb := congrArg TwoFibreProductOver.Hom.b hγ₁
        have hw := (Functor.Restriction.compTo (pP) (pr₁ i j) (f i) rfl (xr i) (xrij i j)).w
        change γ.b ≫ _ = _ ≫ (φ i).b at hb
        show _ = F.map _ ≫ ((xr i).pt.iso.hom ≫ G.map (φ i).b)
        rw [← Category.assoc (F.map _), hw]
        simp only [Category.assoc, ← G.map_comp, hb]
      · unfold Functor.IsRestrictionOf at hγ₂ ⊢
        rw [hcx, hcy]
        have hb := congrArg TwoFibreProductOver.Hom.b hγ₂
        have hw := (Functor.Restriction.compTo (pP) (pr₂ i j) (f j) (hVij i j).w (xr j)
          (xrij i j)).w
        change γ.b ≫ _ = _ ≫ (φ j).b at hb
        show _ = F.map _ ≫ ((xr j).pt.iso.hom ≫ G.map (φ j).b)
        rw [← Category.assoc (F.map _), hw]
        simp only [Category.assoc, ← G.map_comp, hb])
  have hgXiso' : IsIso gX := hgXiso
  have hgYiso' : IsIso gY := hgYiso
  have hfibX : pZ.IsHomLift (𝟙 U) (F.map gX) :=
    (Functor.fibreHomMk (map_fibreHom F hF _ _ gX hgXfib)).2
  have hfibY : pZ.IsHomLift (𝟙 U) (G.map gY) :=
    (Functor.fibreHomMk (map_fibreHom G hG _ _ gY hgYfib)).2
  have hxv := isHomLift_id_iso_hom x hx
  have hyv := isHomLift_id_iso_hom y hy
  have hcand₁ : pZ.IsHomLift (𝟙 U) (F.map gX ≫ y.iso.hom) := by infer_instance
  have hcand₂ : pZ.IsHomLift (𝟙 U) (x.iso.hom ≫ G.map gY) := by infer_instance
  have hcomm : F.map gX ≫ y.iso.hom = x.iso.hom ≫ G.map gY := by
    refine (hθuniq _ ⟨Functor.fibreHom_of_isHomLift_id _ _ hcand₁, inferInstance, ?_⟩).trans
      (hθuniq _ ⟨Functor.fibreHom_of_isHomLift_id _ _ hcand₂, inferInstance, ?_⟩).symm
    · intro i
      have h₁ := congrArg F.map (hgX i)
      have h₂ := (yr i).hom.w
      have h₃ := (φ i).w
      show F.map (xr i).hom.a ≫ F.map gX ≫ y.iso.hom =
        ((xr i).pt.iso.hom ≫ G.map (φ i).b) ≫ G.map (yr i).hom.b
      change F.map ((xr i).hom.a ≫ gX) = F.map ((φ i).a ≫ (yr i).hom.a) at h₁
      rw [← Category.assoc, ← F.map_comp, h₁, F.map_comp, Category.assoc, h₂, ← Category.assoc,
        h₃, Category.assoc]
    · intro i
      have h₁ := congrArg G.map (hgY i)
      have h₂ := (xr i).hom.w
      show F.map (xr i).hom.a ≫ x.iso.hom ≫ G.map gY =
        ((xr i).pt.iso.hom ≫ G.map (φ i).b) ≫ G.map (yr i).hom.b
      change G.map ((xr i).hom.b ≫ gY) = G.map ((φ i).b ≫ (yr i).hom.b) at h₁
      rw [← Category.assoc, h₂, Category.assoc, ← G.map_comp, h₁, G.map_comp, Category.assoc]
  -- the glued morphism
  have h₁ : pX.IsHomLift (𝟙 U) gX := (Functor.fibreHomMk hgXfib).2
  have h₂ : pY.IsHomLift (𝟙 U) gY := (Functor.fibreHomMk hgYfib).2
  have hbase : eqToHom x.hy.symm ≫ pY.map gY ≫ eqToHom y.hy =
      eqToHom x.hx.symm ≫ pX.map gX ≫ eqToHom y.hx := by
    rw [IsHomLift.fac' pX (𝟙 U) gX, IsHomLift.fac' pY (𝟙 U) gY]
    simp only [Category.id_comp, eqToHom_trans]
  let g : x ⟶ y := TwoFibreProductOver.Hom.mk' gX gY hbase hcomm
  refine ⟨g, ⟨?_, ?_, fun i => TwoFibreProductOver.Hom.ext' (hgX i) (hgY i)⟩, ?_⟩
  · refine Functor.fibreHom_of_isHomLift_id hx hy (IsHomLift.of_fac' (pP) _ g hx hy ?_)
    show eqToHom x.hx.symm ≫ pX.map gX ≫ eqToHom y.hx = _
    rw [IsHomLift.fac' pX (𝟙 U) gX]
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  · have : IsIso g.hbase := by
      show IsIso (eqToHom x.hx.symm ≫ pX.map gX ≫ eqToHom y.hx)
      infer_instance
    have : IsIso g.a := hgXiso'
    have : IsIso g.b := hgYiso'
    exact TwoFibreProductOver.isIso_of_components g
  · rintro g' ⟨hg'fib, hg'iso, hg'⟩
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · refine hgXuniq g'.a ⟨map_fibreHom πX hfstX hx hy g' hg'fib, ?_, fun i =>
        congrArg TwoFibreProductOver.Hom.a (hg' i)⟩
      exact inferInstanceAs (IsIso ((πX).map g'))
    · refine hgYuniq g'.b ⟨map_fibreHom πY hsndY hx hy g' hg'fib, ?_, fun i =>
        congrArg TwoFibreProductOver.Hom.b (hg' i)⟩
      exact inferInstanceAs (IsIso ((πY).map g'))

include hF hG hX hY hZ in
/-- **The 2-fibre product of stacks in groupoids is a stack in groupoids**, in the
family-indexed sense of Stacks 02ZI and at any one index universe for the covering families.
It is fibred in groupoids by Stacks 02ZL's first clause; its `Isom` presheaves are sheaves and its
descent data are effective because those of the three factors are. -/
theorem _root_.CategoryTheory.TwoFibreProductOver.isStackInGroupoids_structureFunctor :
    (pP).IsStackInGroupoids.{t} J where
  isFiberedInGroupoids := TwoFibreProductOver.isFiberedInGroupoids pX pY pZ F G
    hX.isFiberedInGroupoids hY.isFiberedInGroupoids hZ.isFiberedInGroupoids hF hG
  isom_isSheaf x y hx hy _ V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij :=
    productIsom_isSheafFor pX pY pZ F G hF hG J hX hY hZ x y hx hy V f hf Vij pr₁ pr₂ hVij
      xr yr xrij yrij
  effective_descent _ _ hf _ _ _ _ _ _ _ _ _ _ _ _ _ _ d :=
    productDescent_isEffective pX pY pZ F G hF hG J hX hY hZ hf d

end ProductIsom

section IsomSheaf
open CategoryTheory.Functor
universe uC uD vC vD t
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {p : D ⥤ C} [p.IsFibered] {J : GrothendieckTopology C}
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.Fiber.mk
private theorem isomIsSheafFor_of_isMorSheaf
    (hMor : ∀ (U : C) (x y : p.Fiber U), Functor.IsMorSheaf p J U x y)
    {U : C} (x y : D) (hx : p.obj x = U) (hy : p.obj y = U)
    {I : Type t} (V : I → C) (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U)
    (Vij : I → I → C) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Restriction p (f i) x hx) (yr : ∀ i, Restriction p (f i) y hy)
    (xrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Restriction p (pr₁ i j ≫ f i) y hy) :
    IsomIsSheafFor p x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij yrij := by
  intro φ hfib hiso hcompat
  -- the given fibre isomorphisms, read between the chosen pullbacks
  set Θ : ∀ i, pullbackFiber p (Fiber.mk hx) (f i) ≅ pullbackFiber p (Fiber.mk hy) (f i) :=
    fun i => (xr i).fiberIsoOf (yr i) (hfib i) (hiso i) with hΘdef
  have hΘ : ∀ i, (Θ i).hom = (xr i).fiberMor (yr i) (hfib i) := fun i => rfl
  -- the base change of `Θ i` to an arrow of the covering sieve does not depend on the
  -- factorization of that arrow through the family
  have hindep : ∀ {W : C} (b : W ⟶ U) (i j : I) (a : W ⟶ V i) (c : W ⟶ V j)
      (ha : a ≫ f i = b) (hc : c ≫ f j = b),
      baseChangeFiberMor (Θ i).hom a b ha b ha
        = baseChangeFiberMor (Θ j).hom c b hc b hc := by
    intro W b i j a c ha hc
    obtain ⟨γ, hγfib, hγ1, hγ2⟩ := hcompat i j
    have hac : a ≫ f i = c ≫ f j := by rw [ha, hc]
    have hd1 : (hVij i j).lift a c hac ≫ pr₁ i j = a := (hVij i j).lift_fst a c hac
    have hd2 : (hVij i j).lift a c hac ≫ pr₂ i j = c := (hVij i j).lift_snd a c hac
    have hb1 : (hVij i j).lift a c hac ≫ (pr₁ i j ≫ f i) = b := by
      rw [← Category.assoc, hd1, ha]
    have h1 : (xrij i j).fiberMor (yrij i j) hγfib
        = baseChangeFiberMor (Θ i).hom (pr₁ i j) (pr₁ i j ≫ f i) rfl (pr₁ i j ≫ f i) rfl := by
      rw [hΘ i]
      exact fiberMor_eq_baseChangeFiberMor rfl rfl (xr i) (yr i) (xrij i j) (yrij i j)
        (hfib i) hγfib hγ1
    have h2 : (xrij i j).fiberMor (yrij i j) hγfib
        = baseChangeFiberMor (Θ j).hom (pr₂ i j) (pr₁ i j ≫ f i) (hVij i j).w.symm
          (pr₁ i j ≫ f i) (hVij i j).w.symm := by
      rw [hΘ j]
      exact fiberMor_eq_baseChangeFiberMor (hVij i j).w (hVij i j).w (xr j) (yr j) (xrij i j)
        (yrij i j) (hfib j) hγfib hγ2
    have key1 : baseChangeFiberMor (Θ i).hom a b ha b ha
        = baseChangeFiberMor ((xrij i j).fiberMor (yrij i j) hγfib)
          ((hVij i j).lift a c hac) b hb1 b hb1 := by
      rw [h1, baseChangeFiberMor_baseChangeFiberMor]
      exact baseChangeFiberMor_congr _ hd1.symm _ _ _ _
    have key2 : baseChangeFiberMor (Θ j).hom c b hc b hc
        = baseChangeFiberMor ((xrij i j).fiberMor (yrij i j) hγfib)
          ((hVij i j).lift a c hac) b hb1 b hb1 := by
      rw [h2, baseChangeFiberMor_baseChangeFiberMor]
      exact baseChangeFiberMor_congr _ hd2.symm _ _ _ _
    rw [key1, key2]
  -- a choice of factorization for every arrow of the covering sieve
  have hex : ∀ (W : C) (h : W ⟶ U), (Sieve.ofArrows V f).arrows h →
      ∃ (i : I) (a : W ⟶ V i), a ≫ f i = h := fun _ _ hh => exists_factorization_of_ofArrows hh
  choose idx arr harr using hex
  set θ : ∀ ⦃W : C⦄ (h : W ⟶ U), (Sieve.ofArrows V f).arrows h →
      (pullbackFiber p (Fiber.mk hx) h ≅ pullbackFiber p (Fiber.mk hy) h) :=
    fun _ h hh => baseChangeFiberIso (Θ (idx _ h hh)) (arr _ h hh) h (harr _ h hh) h
      (harr _ h hh) with hθdef
  have hθ : ∀ ⦃W W' : C⦄ (h : W ⟶ U) (hh : (Sieve.ofArrows V f).arrows h) (γ : W' ⟶ W)
      (b : W' ⟶ U) (hb : γ ≫ h = b) (hb' : (Sieve.ofArrows V f).arrows b),
      (θ b hb').hom = (pullbackFiberCompIso' (Fiber.mk hx) h γ b hb).inv ≫
        pullbackFiberHom (θ h hh).hom γ ≫
          (pullbackFiberCompIso' (Fiber.mk hy) h γ b hb).hom := by
    intro W W' h hh γ b hb hb'
    rw [← baseChangeFiberMor.eq_1]
    rw [hθdef]
    simp only [baseChangeFiberIso_hom]
    rw [baseChangeFiberMor_baseChangeFiberMor]
    exact hindep b _ _ _ _ (harr _ b hb') (by rw [Category.assoc, harr _ h hh, hb])
  obtain ⟨e, he⟩ := exists_fiberIso_of_locally p (hMor U) hf θ hθ
  -- the base change of the glued isomorphism to a member of the family is the given `φ i`
  have hE : ∀ i, pullbackFiberHom e.hom (f i) = (xr i).fiberMor (yr i) (hfib i) := by
    intro i
    rw [he (f i) (Sieve.ofArrows_mk V f i), hθdef]
    simp only [baseChangeFiberIso_hom]
    rw [hindep (f i) _ i _ (𝟙 (V i)) (harr _ (f i) (Sieve.ofArrows_mk V f i)) (Category.id_comp _),
      baseChangeFiberMor_id, hΘ i]
  refine ⟨Fiber.fiberInclusion.map e.hom,
    ⟨fibreHom_of_fiberHom e.hom, inferInstance, fun i =>
      (pullbackFiberHom_eq_fiberMor_iff (xr i) (yr i) (hfib i) e.hom).1 (hE i)⟩, ?_⟩
  rintro g' ⟨hg'fib, hg'iso, hg'restr⟩
  have hg' : ∀ i, pullbackFiberHom (fibreHomMk hg'fib) (f i)
      = (xr i).fiberMor (yr i) (hfib i) := fun i =>
    (pullbackFiberHom_eq_fiberMor_iff (xr i) (yr i) (hfib i) (fibreHomMk hg'fib)).2 (hg'restr i)
  have : fibreHomMk hg'fib = e.hom := by
    refine eq_of_pullbackFiberHom_locally_eq p (hMor U _ _) hf ?_
    intro W h hh
    rw [pullbackFiberHom_eq_baseChangeFiberMor _ (f (idx W h hh)) (arr W h hh) h (harr W h hh),
      pullbackFiberHom_eq_baseChangeFiberMor _ (f (idx W h hh)) (arr W h hh) h (harr W h hh),
      hg' (idx W h hh), hE (idx W h hh)]
  exact congrArg Fiber.fiberInclusion.map this

end IsomSheaf

attribute [local implicit_reducible] Functor.isomSubpresheaf Functor.isomPresheaf

private noncomputable def eqPullbackIsoPullback
    {C : Type*} [Category C] {A B D : Cᵒᵖ ⥤ Type u}
    (f : A ⟶ D) (g : B ⟶ D) : Presheaf.eqPullback f g ≅ pullback f g := by
  let a : Presheaf.eqPullback f g ⟶ A :=
    { app := fun _ => ↾fun t => t.1.1 }
  let b : Presheaf.eqPullback f g ⟶ B :=
    { app := fun _ => ↾fun t => t.1.2 }
  have h : a ≫ f = b ≫ g := by
    ext X t
    exact t.2
  let L : ∀ s : PullbackCone f g, s.pt ⟶ Presheaf.eqPullback f g := fun s =>
    { app := fun X => ↾fun t => ⟨(s.fst.app X t, s.snd.app X t),
        congrArg (fun k => k.app X t) s.condition⟩
      naturality := by
        intro X Y k
        ext t
        apply Subtype.ext
        apply Prod.ext <;> simp [Presheaf.eqPullback] }
  let hL := PullbackCone.IsLimit.mk h L (fun _ => rfl) (fun _ => rfl) (by
    intro s m hm hn
    ext X t
    apply Subtype.ext
    exact Prod.ext (congrArg (fun k => k.app X t) hm)
      (congrArg (fun k => k.app X t) hn))
  exact hL.conePointUniqueUpToIso (pullback.isLimit f g)

private def uliftPresheafIso {C : Type*} [Category C] (F : C ⥤ Type u) :
    F ≅ F ⋙ uliftFunctor.{u, u} :=
  NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift.symm) (fun _ => rfl)

private lemma isSheaf_of_iteratedSlice
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (Q : (Over U)ᵒᵖ ⥤ Type u)
    (h : Presheaf.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
      ((Over.iteratedSliceBackward U).op ⋙ Q)) :
    Presheaf.IsSheaf ((BigFppfOver.topology B S hS).over U)
      Q := by
  let F := Over.iteratedSliceForward U
  let G := Over.iteratedSliceBackward U
  have h' : Presheaf.IsSheaf ((B.topology.over (B.obj hS)).over U)
      (F.op ⋙ (G.op ⋙ Q)) :=
    F.op_comp_isSheaf_of_isSheaf ((B.topology.over (B.obj hS)).over U)
      (B.topology.over U.left) (G.op ⋙ Q) h
  have hunit : (F ⋙ G).op ≅ (𝟭 (Over U)).op := by
    simpa [F, G] using NatIso.op (Over.iteratedSliceEquiv U).unitIso
  let e₀ : F.op ⋙ G.op ≅ 𝟭 _ :=
    (Functor.opComp F G).symm ≪≫ hunit ≪≫ (Functor.opId _)
  have e : F.op ⋙ G.op ⋙ Q ≅ Q := by
    refine NatIso.ofComponents (fun X => Q.mapIso (e₀.app X)) ?_
    intro X Y f
    calc
      _ = Q.map (G.op.map (F.op.map f) ≫ e₀.hom.app Y) := by simp
      _ = Q.map (e₀.hom.app X ≫ (𝟭 (Over U)ᵒᵖ).map f) := by
        simpa using congrArg Q.map (e₀.hom.naturality f)
      _ = _ := by simp
  exact (Presheaf.isSheaf_of_iso_iff e).mp (by simpa [F, G] using h')

private lemma isAlgebraicSpace_morPresheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (hX : HasRepresentableDiagonal B S hS X)
    (U : BigFppfOver B S hS) (x y : X.val.p.Fiber U) :
    letI := X.isFiberedInGroupoids.isFibered
    IsAlgebraicSpace B U.left.1 U.left.2
      ((Over.iteratedSliceBackward U).op ⋙ X.val.p.morPresheaf x y) := by
  let := X.isFiberedInGroupoids.isFibered
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf
      B S hS X).mp hX U x y
  let e' := uliftPresheafIso F ≪≫ e ≪≫
    (uliftPresheafIso ((Over.iteratedSliceBackward U).op ⋙ X.val.p.isomPresheaf x y)).symm
  exact Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (e' ≪≫ Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
      (AlgebraicGeometry.Stack.isomPresheafIsoMorPresheaf X.val.p X.isFiberedInGroupoids x y)) hF

private lemma hasRepresentableDiagonal_twoFibreProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y Z : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS))
    (f : X.val ⥤ᵇ Z.val) (g : Y.val ⥤ᵇ Z.val)
    (hX : HasRepresentableDiagonal B S hS X)
    (hY : HasRepresentableDiagonal B S hS Y)
    (hZ : HasRepresentableDiagonal B S hS Z) :
    HasRepresentableDiagonal B S hS
      (twoFibreProduct B S hS Z X Y f g) := by
  let P := twoFibreProduct B S hS Z X Y f g
  let := X.isFiberedInGroupoids.isFibered
  let := Y.isFiberedInGroupoids.isFibered
  let := Z.isFiberedInGroupoids.isFibered
  let : (TwoFibreProductOver.structureFunctor X.val.p Y.val.p Z.val.p
      f.toFunctor g.toFunctor).IsFibered := P.isFiberedInGroupoids.isFibered
  let := P.isFiberedInGroupoids.isFibered
  let hf := Z.isFiberedInGroupoids.isFibredOneMorphism f.w
  let hg := Z.isFiberedInGroupoids.isFibredOneMorphism g.w
  apply (hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf
    B S hS P).mpr
  intro U x y
  let H := (Over.iteratedSliceBackward U).op
  let a := Functor.whiskerLeft H (hf.morPresheafMap
    (TwoFibreProductOver.fibFst x) (TwoFibreProductOver.fibFst y))
  let b := Functor.whiskerLeft H (TwoFibreProductOver.morSnd hf hg x y)
  have hA := isAlgebraicSpace_morPresheaf B S hS X hX U
    (TwoFibreProductOver.fibFst x) (TwoFibreProductOver.fibFst y)
  have hB := isAlgebraicSpace_morPresheaf B S hS Y hY U
    (TwoFibreProductOver.fibSnd x) (TwoFibreProductOver.fibSnd y)
  have hC := isAlgebraicSpace_morPresheaf B S hS Z hZ U
    ((Functor.fiberFunctorOfCompEq f.w U).obj (TwoFibreProductOver.fibFst x))
    ((Functor.fiberFunctorOfCompEq f.w U).obj (TwoFibreProductOver.fibFst y))
  have hPB := AlgebraicGeometry.isAlgebraicSpace_pullback B U.left.1 U.left.2 a b hA hB hC
  have hEq := Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (eqPullbackIsoPullback a b).symm hPB
  have hMor := Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (Functor.isoWhiskerLeft H (TwoFibreProductOver.morPresheafEqPullbackIso hf hg x y)).symm hEq
  have hIso := Space.isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (Functor.isoWhiskerLeft H
      (AlgebraicGeometry.Stack.isomPresheafIsoMorPresheaf P.val.p P.isFiberedInGroupoids x
        y)).symm hMor
  exact ⟨_, hIso, ⟨Iso.refl _⟩⟩

attribute [local implicit_reducible] Bicategory.InducedBicategory
  BasedFunctor.comp Bicategory.InducedBicategory.categoryStruct
  Bicategory.InducedBicategory.bicategory BasedCategory.bicategory
attribute [local simp] Bicategory.InducedBicategory.bicategory_comp_hom

attribute [local implicit_reducible] TwoFibreProductOver.fst TwoFibreProductOver.snd
  TwoFibreProductOver.structureFunctor
private lemma homLift_eqToHom_of_vertical
    {C : Type*} [Category C] {D : Type*} [Category D] (p : D ⥤ C)
    {x y : D} {A B T : C} (hx : p.obj x = A) (hy : p.obj y = B)
    (hAB : A = B) (e : x ⟶ y) (he : p.IsHomLift (𝟙 T) e) :
    p.IsHomLift (eqToHom hAB) e := by
  have := he
  apply IsHomLift.of_fac' p _ _ hx hy
  rw [IsHomLift.fac' p (𝟙 T) e]
  simp

section AtlasComparison
universe uC vC uX vX uY vY uZ vZ uU vU uV vV
variable {C : Type uC} [Category.{vC} C]
  {X : Type uX} [Category.{vX} X] {Y : Type uY} [Category.{vY} Y]
  {Z : Type uZ} [Category.{vZ} Z] {U : Type uU} [Category.{vU} U]
  {V : Type uV} [Category.{vV} V]
  (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C) (pU : U ⥤ C) (pV : V ⥤ C)
  (f : X ⥤ Z) (g : Y ⥤ Z) (a : U ⥤ X) (b : V ⥤ Y)
  (hf : f ⋙ pZ = pX) (hg : g ⋙ pZ = pY)
  (ha : a ⋙ pX = pU) (hb : b ⋙ pY = pV)
local notation "pP" => TwoFibreProductOver.structureFunctor pX pY pZ f g
local notation "πX" => TwoFibreProductOver.fst pX pY pZ f g
local notation "πY" => TwoFibreProductOver.snd pX pY pZ f g
local notation "pA" => TwoFibreProductOver.structureFunctor pP pU pX πX a
local notation "πP" => TwoFibreProductOver.fst pP pU pX πX a
local notation "R" => TwoFibreProductOver pA pV pY (πP ⋙ πY) b
local notation "Q" => TwoFibreProductOver pU pV pZ (a ⋙ f) (b ⋙ g)

private def atlasComparison : R ⥤ Q where
  obj r :=
    { base := r.base
      x := r.x.y
      y := r.y
      hx := r.x.hy.trans r.hx
      hy := r.hy
      iso := (f.mapIso r.x.iso.symm) ≪≫ r.x.x.iso ≪≫ g.mapIso r.iso
      vertical := by
        have hi := isHomLift_id_iso_hom r.x r.hx
        have hi' : pX.IsHomLift (𝟙 r.base) r.x.iso.inv :=
          IsHomLift.lift_id_inv pX r.base r.x.iso
        have hf' := Functor.isHomLift_map_of_comp_eq hf (𝟙 r.base) r.x.iso.inv
        have hj := isHomLift_id_iso_hom r.x.x (r.x.hx.trans r.hx)
        have hk := r.vertical
        have hg' := Functor.isHomLift_map_of_comp_eq hg (𝟙 r.base) r.iso.hom
        change pZ.IsHomLift (𝟙 r.base) (f.map r.x.iso.inv ≫ r.x.x.iso.hom ≫ g.map r.iso.hom)
        exact Functor.isHomLift_of_eq
          (inferInstance : pZ.IsHomLift (𝟙 r.base ≫ 𝟙 r.base ≫ 𝟙 r.base)
            (f.map r.x.iso.inv ≫ r.x.x.iso.hom ≫ g.map r.iso.hom))
          (by simp) }
  map {r s} k :=
    { hbase := k.hbase
      a := k.a.b
      b := k.b
      ha := by
        have := k.a.hb
        have := k.ha
        apply IsHomLift.of_fac' pU k.hbase k.a.b (r.x.hy.trans r.hx) (s.x.hy.trans s.hx)
        have hmap : pU.map k.a.b = eqToHom r.x.hy ≫ k.a.hbase ≫ eqToHom s.x.hy.symm :=
          IsHomLift.fac' pU k.a.hbase k.a.b
        rw [hmap]
        have hh : k.a.hbase = eqToHom r.hx ≫ k.hbase ≫ eqToHom s.hx.symm :=
          IsHomLift.fac' pA k.hbase k.a
        rw [hh]
        simp
      hb := k.hb
      w := by
        have h₁ : a.map k.a.b ≫ s.x.iso.inv = r.x.iso.inv ≫ k.a.a.a := by
          rw [Iso.comp_inv_eq, Category.assoc]
          apply (cancel_epi r.x.iso.hom).mp
          have hh : k.a.a.a ≫ s.x.iso.hom = r.x.iso.hom ≫ a.map k.a.b := k.a.w
          simpa only [Iso.hom_inv_id_assoc] using hh.symm
        have h₂ := k.a.a.w
        have h₃ : k.a.a.b ≫ s.iso.hom = r.iso.hom ≫ b.map k.b := k.w
        dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
        calc
          _ = f.map (a.map k.a.b ≫ s.x.iso.inv) ≫ s.x.x.iso.hom ≫ g.map s.iso.hom := by
            simp only [Functor.map_comp, Category.assoc]
          _ = f.map (r.x.iso.inv ≫ k.a.a.a) ≫ s.x.x.iso.hom ≫ g.map s.iso.hom := by rw [h₁]
          _ = f.map r.x.iso.inv ≫ r.x.x.iso.hom ≫ g.map (k.a.a.b ≫ s.iso.hom) := by
            simp only [Functor.map_comp, Category.assoc]
            rw [reassoc_of% h₂]
          _ = _ := by
            rw [h₃]
            simp only [Functor.map_comp, Category.assoc] }
  map_id _ := by apply TwoFibreProductOver.Hom.ext' <;> rfl
  map_comp _ _ := by apply TwoFibreProductOver.Hom.ext' <;> rfl

private def atlasInsertion : Q ⥤ R where
  obj q :=
    { base := q.base
      x :=
        { base := q.base
          x :=
            { base := q.base
              x := a.obj q.x
              y := b.obj q.y
              hx := (Functor.congr_obj ha q.x).trans q.hx
              hy := (Functor.congr_obj hb q.y).trans q.hy
              iso := q.iso
              vertical := q.vertical }
          y := q.x
          hx := rfl
          hy := q.hx
          iso := Iso.refl _
          vertical := IsHomLift.id ((Functor.congr_obj ha q.x).trans q.hx) }
      y := q.y
      hx := rfl
      hy := q.hy
      iso := Iso.refl _
      vertical := IsHomLift.id ((Functor.congr_obj hb q.y).trans q.hy) }
  map {q s} k :=
    { hbase := k.hbase
      a :=
        { hbase := k.hbase
          a :=
            { hbase := k.hbase
              a := a.map k.a
              b := b.map k.b
              ha := by have := k.ha; exact Functor.isHomLift_map_of_comp_eq ha k.hbase k.a
              hb := by have := k.hb; exact Functor.isHomLift_map_of_comp_eq hb k.hbase k.b
              w := k.w }
          b := k.a
          ha := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
          hb := k.ha
          w := by simp }
      b := k.b
      ha := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      hb := k.hb
      w := by simp }
  map_id _ := by
    apply TwoFibreProductOver.Hom.ext'
    · apply TwoFibreProductOver.Hom.ext'
      · apply TwoFibreProductOver.Hom.ext' <;> simp
      · rfl
    · rfl
  map_comp _ _ := by
    apply TwoFibreProductOver.Hom.ext'
    · apply TwoFibreProductOver.Hom.ext'
      · apply TwoFibreProductOver.Hom.ext' <;> simp
      · rfl
    · rfl

attribute [local implicit_reducible] atlasComparison atlasInsertion

private noncomputable def atlasUnitComponent (r : R) :
    r ≅ (atlasInsertion pX pY pZ pU pV f g a b ha hb).obj
      ((atlasComparison pX pY pZ pU pV f g a b hf hg).obj r) := by
  let s := (atlasInsertion pX pY pZ pU pV f g a b ha hb).obj
    ((atlasComparison pX pY pZ pU pV f g a b hf hg).obj r)
  let m : r.x.x ⟶ s.x.x :=
    { hbase := eqToHom (r.x.hx.trans r.hx)
      a := r.x.iso.hom
      b := r.iso.hom
      ha := homLift_eqToHom_of_vertical pX r.x.x.hx s.x.x.hx
        (r.x.hx.trans r.hx) _ r.x.vertical
      hb := homLift_eqToHom_of_vertical pY r.x.x.hy s.x.x.hy
        (r.x.hx.trans r.hx) _ r.vertical
      w := by
        dsimp [s, atlasInsertion, atlasComparison]
        simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
        rw [f.map_id]
        exact Category.id_comp _ }
  have hm : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m
    (by dsimp [m]; infer_instance) (by dsimp [m]; infer_instance)
  let n : r.x ⟶ s.x :=
    { hbase := eqToHom r.hx
      a := m
      b := 𝟙 _
      ha := IsHomLift.of_fac' pP _ m r.x.hx rfl (by dsimp [m]; simp)
      hb := homLift_eqToHom_of_vertical pU r.x.hy s.x.hy r.hx (𝟙 _) (IsHomLift.id r.x.hy)
      w := by dsimp [m, s, atlasInsertion]; simp }
  have hn : IsIso n := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ n
    hm (by dsimp [n]; infer_instance)
  let l : r ⟶ s :=
    { hbase := 𝟙 _
      a := n
      b := 𝟙 _
      ha := IsHomLift.of_fac' pA _ n r.hx rfl (by dsimp [n]; simp)
      hb := IsHomLift.id r.hy
      w := by dsimp [n, m, s, atlasInsertion]; simp }
  have hl : IsIso l := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ l
    hn (by dsimp [l]; infer_instance)
  exact asIso l

private noncomputable def atlasComparisonEquivalence :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor pA pV pY (πP ⋙ πY) b)
      (TwoFibreProductOver.structureFunctor pU pV pZ (a ⋙ f) (b ⋙ g)) where
  hom := ⟨atlasComparison pX pY pZ pU pV f g a b hf hg, rfl⟩
  inv := ⟨atlasInsertion pX pY pZ pU pV f g a b ha hb, rfl⟩
  unitIso := NatIso.ofComponents
    (atlasUnitComponent pX pY pZ pU pV f g a b hf hg ha hb) (by
      intro r s k
      apply TwoFibreProductOver.Hom.ext'
      · apply TwoFibreProductOver.Hom.ext'
        · apply TwoFibreProductOver.Hom.ext'
          · exact k.a.w
          · exact k.w
        · change k.a.b ≫ 𝟙 _ = 𝟙 _ ≫ k.a.b
          simp
      · change k.b ≫ 𝟙 _ = 𝟙 _ ≫ k.b
        simp)
  counitIso := NatIso.ofComponents (fun q => by
    let m : (atlasComparison pX pY pZ pU pV f g a b hf hg).obj
        ((atlasInsertion pX pY pZ pU pV f g a b ha hb).obj q) ⟶ q :=
      { hbase := 𝟙 _
        a := 𝟙 _
        b := 𝟙 _
        ha := IsHomLift.id q.hx
        hb := IsHomLift.id q.hy
        w := by
          dsimp [atlasComparison, atlasInsertion]
          simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
          change q.iso.hom = f.map (𝟙 _) ≫ q.iso.hom ≫ g.map (𝟙 _)
          rw [f.map_id, g.map_id]
          simp }
    have : IsIso m := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ m
      (by dsimp [m]; infer_instance) (by dsimp [m]; infer_instance)
    exact asIso m) (by
      intro r s k
      apply TwoFibreProductOver.Hom.ext'
      · change k.a ≫ 𝟙 _ = 𝟙 _ ≫ k.a
        simp
      · change k.b ≫ 𝟙 _ = 𝟙 _ ≫ k.b
        simp)
  unit_over := by
    ext r
    change 𝟙 _ = _
    simp
    rfl
  counit_over := by
    ext q
    change 𝟙 _ = _
    simp
    rfl

end AtlasComparison

/-- **Transport of the relative property of Stacks 03YK along a family of equivalences of the
first projections.** If, for every scheme `V` over `S` and every scheme-valued point `y` of `𝒴`
over `V`, the first projection of `(Sch/V)_{fppf} ×_{y, 𝒴, f'} 𝒳'` is equivalent over the big
fppf site of `V` to that of `(Sch/V)_{fppf} ×_{y, 𝒴, f} 𝒳`, then `f'` has the relative property
`P` as soon as `f` does.

This is the relative-property companion of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst`:
the target `𝒴` and the point `y` do not move, so the two quantifications match up and the
algebraic space whose structural morphism is tested is literally the same one. The relative
property is written out as the quantifier of `AlgebraicGeometry.Stack.HasRelativeProperty`
rather than through that abbreviation, so that no hypothesis on `P` is needed. -/
theorem relativeProperty_of_forall_nonempty_equivalenceOver_fst
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒳' 𝒴 : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (f' : 𝒳' ⟶ 𝒴)
    (e : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj), y ⋙ 𝒴.val.p = Over.map V.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳'.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f'))
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))))
    (hP : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩))) :
    ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒳'.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f'))
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)) := by
  intro V y hy G hG hE
  obtain ⟨E⟩ := e V y hy
  exact hP V y hy G hG (hE.map fun k => E.symm.trans k)

/-- **A presentation by an algebraic space yields a presentation by a scheme.** Let
`p : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which is representable by algebraic spaces, surjective and smooth in the sense of Stacks 03YK,
and assume `𝒰` is representable by an algebraic space over `S`. Then `𝒳` admits a presentation
by a scheme: the third clause of `AlgebraicGeometry.Stack.IsAlgebraicStack`.

This is the final step of the source's proof of Stacks 04TF — "choosing a scheme `W` and a
surjective étale morphism `W → F`" — and it is only that step. In particular it is not
Stacks 05UL, which draws the same conclusion from the same hypotheses but also proves the
diagonal clause and therefore needs Bootstrap 04S6.

A scheme atlas of the representing algebraic space `F` presents the stack of `F`
(`AlgebraicGeometry.Stack.isAlgebraicStack_fibredCategory`); the given 1-morphism is transported
from `𝒰` to the category of elements of `F` along the representing equivalence, which changes
neither the target nor the family of scheme-valued points the relative property is tested on;
and the two are composed by Stacks 0301 and Stacks 045B. -/
theorem exists_schemePresentation_of_isRepresentableByAlgebraicSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (p : 𝒰 ⟶ 𝒳)
    (h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰)
    (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom)
    (hprops : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hy : y ⋙ 𝒳.val.p = Over.map V.hom)
      (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒰.val.p 𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor p))
        (presheafOfCategories (G ⋙ typeToCat)).p) →
      (let g := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom
       Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g)) :
    ∃ (W : BigFppfOver B S hS) (k : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒳.val),
      IsRepresentableByAlgebraicSpaces B S hS k ∧
        ∀ (V : BigFppfOver B S hS)
          (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
          (_hy : y ⋙ 𝒳.val.p = Over.map V.hom)
          (G : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
          (hG : IsAlgebraicSpace B V.left.1 V.left.2 G),
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map V.hom)
              (schemeFibredCategory B S hS W).val.p 𝒳.val.p y k.toFunctor)
            (presheafOfCategories (G ⋙ typeToCat)).p) →
          (let g := (algebraicSpaceMap B S hS V
            ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨G, hG⟩)).hom
           Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g) := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := h𝒰
  obtain ⟨hFfib, hFstack, hFdiag, hFatlas⟩ :=
    isAlgebraicStack_fibredCategory.{u, u} B S hS F hF
  obtain ⟨W, atl, hatl, hatlProp⟩ := hFatlas
  -- the representing equivalence, read as a 1-morphism out of the category of elements of `F`
  let d : fibredCategory B S hS F ⟶ 𝒰 :=
    Bicategory.InducedBicategory.mkHom ⟨eF.inv.functor, eF.inv.w⟩
  have hd : Functor.IsEquivalence d.hom.toFunctor := eF.isEquivalence_inv_functor
  let q : fibredCategory B S hS F ⟶ 𝒳 := d ≫ p
  have he : ∀ (V : BigFppfOver B S hS)
      (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj), y ⋙ 𝒳.val.p = Over.map V.hom →
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (fibredCategory B S hS F).val.p 𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor q))
        (TwoFibreProductOver.fst (Over.map V.hom) 𝒰.val.p 𝒳.val.p y
          (CatFiberedInGroupoids.homFunctor p))) :=
    fun V y hy => nonempty_equivalenceOver_fst_of_equivalence_source B S hS d.hom p.hom V y hy
  have hq : IsRepresentableByAlgebraicSpaces B S hS q.hom :=
    isRepresentableByAlgebraicSpaces_of_forall_nonempty_equivalenceOver_fst
      (f := p.hom) (f' := q.hom) he hp
  have hqsurj := relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
    (Space.surjectiveMorphismProperty B S hS) p q he
    (fun V y hy G hG h => (hprops V y hy G hG h).1)
  have hqsmooth := relativeProperty_of_forall_nonempty_equivalenceOver_fst B S hS
    (Space.smoothMorphismProperty B S hS) p q he
    (fun V y hy G hG h => (hprops V y hy G hG h).2)
  -- the scheme atlas of `F`, read as a 1-morphism of the 2-category
  let k₀ : schemeFibredCategory B S hS W ⟶ fibredCategory B S hS F :=
    Bicategory.InducedBicategory.mkHom atl
  have hk := AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp B S hS k₀ q hatl hq
  refine ⟨W, (k₀ ≫ q).hom, hk, fun V y hy G hG hEq => ⟨?_, ?_⟩⟩
  · exact hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) k₀ q hatl hq
      (fun V y hy G hG h => (hatlProp V y hy G hG h).1) hqsurj V y hy G hG hEq
  · exact hasRelativeProperty_comp.{u, u, u + 1, u + 1} B S hS
      (Space.smoothMorphismProperty B S hS) k₀ q hatl hq
      (fun V y hy G hG h => (hatlProp V y hy G hG h).2) hqsmooth V y hy G hG hEq

/-- **Stacks 04TF.** Let `𝒵` be a stack in groupoids over the big fppf site of `S` whose
diagonal is representable by algebraic spaces, let `𝒳` and `𝒴` be algebraic stacks over `S` and
let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` be 1-morphisms of stacks in groupoids. Then the 2-fibre product
`𝒳 ×_{f, 𝒵, g} 𝒴` is an algebraic stack over `S`.

The hypothesis on `𝒵` is the stack clause of `AlgebraicGeometry.Stack.IsAlgebraicStack`, i.e.
"stack in groupoids" in both renderings of Stacks 02ZJ; the sieve-indexed conjunct is what Stacks
04TF asks for, and it is what Stacks 026G
(`CategoryTheory.TwoFibreProductOver.isStack_structureFunctor`) consumes. -/
@[stacks 04TF]
theorem isAlgebraicStack_twoFibreProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⥤ᵇ 𝒵) (g : 𝒴 ⥤ᵇ 𝒵)
    (h𝒵 : 𝒵.p.IsStack (BigFppfOver.topology B S hS) ∧
      𝒵.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk 𝒵 h𝒵.2.isFiberedInGroupoids))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴) :
    IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor)) := by
  obtain ⟨hXfib, hXstack, hXdiag, hXatlas⟩ := h𝒳
  obtain ⟨hYfib, hYstack, hYdiag, hYatlas⟩ := h𝒴
  let X := CatFiberedInGroupoids.mk 𝒳 hXfib
  let Y := CatFiberedInGroupoids.mk 𝒴 hYfib
  let Z := CatFiberedInGroupoids.mk 𝒵 h𝒵.2.isFiberedInGroupoids
  let f' : X ⟶ Z := Bicategory.InducedBicategory.mkHom f
  let g' : Y ⟶ Z := Bicategory.InducedBicategory.mkHom g
  let PSq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f' g'
  let P := PSq.pt
  let hp := P.isFiberedInGroupoids
  let J := BigFppfOver.topology B S hS
  have hPdiag : HasRepresentableDiagonal B S hS P :=
    hasRepresentableDiagonal_twoFibreProduct B S hS X Y Z f g hXdiag hYdiag hdiag
  let : (TwoFibreProductOver.structureFunctor 𝒳.p 𝒴.p 𝒵.p
    f.toFunctor g.toFunctor).IsFibered := hp.isFibered
  let := P.isFiberedInGroupoids.isFibered
  have hMor (U : BigFppfOver B S hS) (x y : P.val.p.Fiber U) :
      Functor.IsMorSheaf P.val.p J U x y :=
    isSheaf_of_iteratedSlice B S hS U (P.val.p.morPresheaf x y)
      (isAlgebraicSpace_morPresheaf B S hS P hPdiag U x y).isSheaf
  have hPstack : P.val.p.IsStackInGroupoids.{w} J :=
    { isFiberedInGroupoids := hp
      isom_isSheaf := by
        intro U x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
        exact isomIsSheafFor_of_isMorSheaf hMor x y hx hy V f hf
          Vij pr₁ pr₂ hVij xr yr xrij yrij
      effective_descent := by
        intro U I V a ha Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ d
        exact productDescent_isEffective 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor f.w g.w
          J hXstack.2 hYstack.2 h𝒵.2 ha d }
  have hPisStack : P.val.p.IsStack J :=
    TwoFibreProductOver.isStack_structureFunctor 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor J
      hXstack.1 hYstack.1 h𝒵.1
      (Functor.IsFiberedInGroupoids.isFibredOneMorphism h𝒵.2.isFiberedInGroupoids f.w)
      (Functor.IsFiberedInGroupoids.isFibredOneMorphism h𝒵.2.isFiberedInGroupoids g.w)
  refine ⟨hp, ⟨hPisStack, hPstack⟩, hPdiag, ?_⟩
  obtain ⟨U, a₀, ha₀, haProp⟩ := hXatlas
  obtain ⟨V, b₀, hb₀, hbProp⟩ := hYatlas
  let a : schemeFibredCategory B S hS U ⟶ X := Bicategory.InducedBicategory.mkHom a₀
  let b : schemeFibredCategory B S hS V ⟶ Y := Bicategory.InducedBicategory.mkHom b₀
  -- base change the presentation of `𝒳` along the first projection of `P`, then that of `𝒴`
  -- along the result
  let s₁ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} PSq.fst a
  let s₂ := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (s₁.fst ≫ PSq.snd) b
  have hs₁ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    PSq.fst a
  have hs₂ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (s₁.fst ≫ PSq.snd) b
  have ha' := isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ a
    PSq.fst s₁ hs₁ ha₀
  have hb' := isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ b
    (s₁.fst ≫ PSq.snd) s₂ hs₂ hb₀
  have hc := AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp B S hS
    s₂.fst s₁.fst hb' ha'
  -- the source is the 2-fibre product of the two presentations over `𝒵`, hence representable by
  -- an algebraic space by condition (4) of Stacks 045G for `𝒵`
  have hQ := (isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS Z).mp
    ((isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS Z).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS Z).mp hdiag))
    U V (a₀.comp f) (b₀.comp g)
  obtain ⟨F, hF, ⟨eF⟩⟩ := hQ
  have hR : IsRepresentableByAlgebraicSpace B S hS s₂.pt :=
    ⟨F, hF, ⟨(atlasComparisonEquivalence 𝒳.p 𝒴.p 𝒵.p
      (schemeFibredCategory B S hS U).val.p (schemeFibredCategory B S hS V).val.p
      f.toFunctor g.toFunctor a₀.toFunctor b₀.toFunctor f.w g.w a₀.w b₀.w).trans eF⟩⟩
  -- the composite is surjective and smooth, by Stacks 045C and Stacks 045B
  have hprop (T : MorphismProperty (AlgebraicSpaces B S hS))
      [T.IsStableUnderBaseChange]
      [T.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)]
      [T.IsStableUnderComposition]
      (haT : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS T a ha₀)
      (hbT : HasRelativeProperty.{u, u, u + 1, u + 1} B S hS T b hb₀) :
      HasRelativeProperty.{u, u, u + 1, u + 1} B S hS T (s₂.fst ≫ s₁.fst) hc :=
    hasRelativeProperty_comp B S hS T _ _ hb' ha'
      (hasRelativeProperty_baseChange.{u, u, u + 1} B S hS T _ _ _ b (s₁.fst ≫ PSq.snd) s₂ hs₂
        hb₀ hbT)
      (hasRelativeProperty_baseChange.{u, u, u + 1} B S hS T _ _ _ a PSq.fst s₁ hs₁ ha₀ haT)
  have hsur := hprop (Space.surjectiveMorphismProperty B S hS)
    (fun T y hy F hF he => (haProp T y hy F hF he).1)
    (fun T y hy F hF he => (hbProp T y hy F hF he).1)
  have hsm := hprop (Space.smoothMorphismProperty B S hS)
    (fun T y hy F hF he => (haProp T y hy F hF he).2)
    (fun T y hy F hF he => (hbProp T y hy F hF he).2)
  -- replace the presentation by an algebraic space with one by a scheme
  exact exists_schemePresentation_of_isRepresentableByAlgebraicSpace B S hS s₂.pt P
    (s₂.fst ≫ s₁.fst) hR hc
    (fun T y hy G hG he => ⟨hsur T y hy G hG he, hsm T y hy G hG he⟩)

end AlgebraicGeometry.Stack

end
