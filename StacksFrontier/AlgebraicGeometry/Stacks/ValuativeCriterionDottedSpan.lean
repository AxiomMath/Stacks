module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionSchemePoint
public import StacksFrontier.CategoryTheory.DottedArrows.TwoYoneda

/-!
# Dotted arrows of a dominating extension, and spans in the source

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site, let `q`
be a valuative square for `f` (Stacks 0CLK) and let `e` be a dominating extension of `q`. This
file identifies the dotted arrows of the outer rectangle cut out by `e` with elementary data in
`𝒳` and `𝒴`:

```text
  Z_{K'} --m--> Z_{R'}
    |
    n
    v
  x(1_K)                    b : f(Z_{R'}) ⟶ y(1_R)
```

a span in `𝒳` whose legs lie over the two edges `Spec K' ⟶ Spec K` and `Spec K' ⟶ Spec R'` of the
extension, together with a morphism `b` of `𝒴` over the edge `Spec R' ⟶ Spec R`, such that the
images under `f` of the two legs are compatible with the link of `q`
(`AlgebraicGeometry.Stack.pointLink`).

Both directions are the 2-Yoneda lemma together with the unique-fill-in property of a category
fibred in groupoids: a dotted arrow is determined by its value at the unit object, and conversely
data at the unit object extends to a dotted arrow
(`CategoryTheory.CatFiberedInGroupoids.nonempty_dottedArrow_of_fiberObj`). The span is the shape
in which a base change of `q` to an algebraic space sees a dotted arrow, which is what Stacks
0CLN needs.

## Main results

* `AlgebraicGeometry.Stack.nonempty_dottedArrow_of_span`: a compatible span produces a dotted
  arrow for the outer rectangle.
* `AlgebraicGeometry.Stack.exists_span_of_dottedArrow`: a dotted arrow for the outer rectangle
  produces a compatible span.

## Implementation notes

In both directions the morphisms involved are replaced by morphisms over an identity through the
unique-fill-in property, using `CategoryTheory.Functor.IsStronglyCartesian.map`, and those are
isomorphisms because the fibres are groupoids. The compatibility is then checked after composing
with a strongly cartesian arrow, by `CategoryTheory.Functor.IsStronglyCartesian.ext`, so that no
component of the filling 2-morphism has to be computed.

## References

* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLN](https://stacks.math.columbia.edu/tag/0CLN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.Bicategory.InducedBicategory
  AlgebraicGeometry.Stack.outerSquare

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}

/-- A morphism over an identity of `𝒞` is invertible, with inverse over the same identity, when
the fibre is a groupoid. -/
private theorem isIso_and_isHomLift_inv_of_fiber_isGroupoid {𝒮 𝒞 : Type*} [Category 𝒮]
    [Category 𝒞] {p : 𝒮 ⥤ 𝒞} {U : 𝒞} (hg : IsGroupoid (p.Fiber U)) {a b : 𝒮} (φ : a ⟶ b)
    (h : p.IsHomLift (𝟙 U) φ) : ∃ _ : IsIso φ, p.IsHomLift (𝟙 U) (inv φ) := by
  have := Functor.isIso_of_fiber_isGroupoid hg φ h
  exact ⟨this, IsHomLift.lift_id_inv_isIso p U φ⟩

/-- The canonical arrow of `q.x` at the unit object of the generic point of `e` lies over the
generic edge. -/
private theorem isHomLift_map_x_canonical (q : ValuativeSquare B S hS f)
    (e : q.DominatingExtension) :
    𝒳.val.val.p.IsHomLift e.genericOver (q.x.hom.map (Over.mkIdTerminal.from
      (e.k.hom.obj (Over.mk (𝟙 (dominatingGenericObject B e)))))) :=
  Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_of_eq 𝒳.val.val.p e.genericOver
    (H := q.x.hom) _ (Functor.congr_obj e.k_canonical _)

/-- The canonical arrow of `q.y` at the unit object of the special point of `e` lies over the
special edge. -/
private theorem isHomLift_map_y_canonical (q : ValuativeSquare B S hS f)
    (e : q.DominatingExtension) :
    𝒴.val.val.p.IsHomLift e.specialOver (q.y.hom.map (Over.mkIdTerminal.from
      (e.a.hom.obj (Over.mk (𝟙 (dominatingSpecialObject B e)))))) :=
  Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_of_eq 𝒴.val.val.p e.specialOver
    (H := q.y.hom) _ (Functor.congr_obj e.a_canonical _)

/-- **A compatible span produces a dotted arrow.** Let `e` be a dominating extension of a
valuative square `q` for `f`. Given a span `n : Z_{K'} ⟶ x(1_K)`, `m : Z_{K'} ⟶ Z_{R'}` in `𝒳`
whose legs lie over the two upper edges of the extension, and a morphism
`b : f(Z_{R'}) ⟶ y(1_R)` of `𝒴` over its lower edge, such that the images under `f` of the two
legs are compatible with the link of `q`, the outer rectangle cut out by `e` has a dotted
arrow. -/
theorem nonempty_dottedArrow_of_span (q : ValuativeSquare B S hS f)
    (e : q.DominatingExtension) {ZK ZR : 𝒳.val.val.obj}
    (n : ZK ⟶ q.x.hom.obj (Over.mk (𝟙 _))) (hn : 𝒳.val.val.p.IsHomLift e.genericOver n)
    (m : ZK ⟶ ZR) (hm : 𝒳.val.val.p.IsHomLift e.genericMap m)
    (b : f.hom.hom.obj ZR ⟶ q.y.hom.obj (Over.mk (𝟙 _)))
    (hb : 𝒴.val.val.p.IsHomLift e.specialOver b)
    (h : f.hom.hom.map n ≫ pointLink B q = f.hom.hom.map m ≫ b) :
    Nonempty (DottedArrow (e.k ≫ q.x) e.j f.hom (e.a ≫ q.y) e.inducedGamma) := by
  let zK : Over (dominatingGenericObject B e) := Over.mk (𝟙 (dominatingGenericObject B e))
  let zR : Over (dominatingSpecialObject B e) := Over.mk (𝟙 (dominatingSpecialObject B e))
  let cK := q.x.hom.map (Over.mkIdTerminal.from (e.k.hom.obj zK))
  let cR := q.y.hom.map (Over.mkIdTerminal.from (e.a.hom.obj zR))
  have hcK := isHomLift_map_x_canonical B q e
  have hcR := isHomLift_map_y_canonical B q e
  have hcartK := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift e.genericOver cK
  have hcartR := 𝒴.val.isFiberedInGroupoids.isStronglyCartesian_homLift e.specialOver b
  let v := Functor.IsStronglyCartesian.map 𝒳.val.val.p e.genericOver cK
    (Category.id_comp _).symm n
  have hv : 𝒳.val.val.p.IsHomLift (𝟙 (dominatingGenericObject B e)) v := inferInstance
  obtain ⟨hviso, hvinv⟩ := isIso_and_isHomLift_inv_of_fiber_isGroupoid
    (𝒳.val.isFiberedInGroupoids.fiber_isGroupoid (dominatingGenericObject B e)) v hv
  have hvfac : v ≫ cK = n := Functor.IsStronglyCartesian.fac _ _ _ _ _
  have hvfac' : inv v ≫ n = cK := by rw [← hvfac, IsIso.inv_hom_id_assoc]
  let β := Functor.IsStronglyCartesian.map 𝒴.val.val.p e.specialOver b
    (Category.id_comp _).symm cR
  have hβ : 𝒴.val.val.p.IsHomLift (𝟙 (dominatingSpecialObject B e)) β := inferInstance
  have hβfac : β ≫ b = cR := Functor.IsStronglyCartesian.fac _ _ _ _ _
  let m₀ := inv v ≫ m
  have hm₀ : 𝒳.val.val.p.IsHomLift e.genericMap m₀ :=
    IsHomLift.comp_lift_id_left _ e.genericMap m (inv v)
  have hfm₀ : 𝒴.val.val.p.IsHomLift e.genericMap (f.hom.hom.map m₀) :=
    f.hom.hom.preserves_isHomLift _ _
  have hγ : 𝒴.val.val.p.IsHomLift (𝟙 (dominatingGenericObject B e))
      ((outerSquare B q e).γ.hom.app zK) := (outerSquare B q e).γ.hom.isHomLift' zK
  have ht : 𝒴.val.val.p.IsHomLift e.genericMap
      ((outerSquare B q e).y.hom.map (Over.mkIdTerminal.from (e.j.hom.obj zK))) :=
    Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_of_eq 𝒴.val.val.p e.genericMap
      (H := (outerSquare B q e).y.hom) _ (Functor.congr_obj e.j_canonical zK)
  have := hγ
  have := hβ
  have hl : 𝒴.val.val.p.IsHomLift e.genericMap
      ((outerSquare B q e).γ.hom.app zK ≫ f.hom.hom.map m₀) :=
    IsHomLift.comp_lift_id_left _ e.genericMap _ _
  have hr : 𝒴.val.val.p.IsHomLift e.genericMap
      ((outerSquare B q e).y.hom.map (Over.mkIdTerminal.from (e.j.hom.obj zK)) ≫ β) :=
    IsHomLift.comp_lift_id_right _ e.genericMap _ _
  refine CatFiberedInGroupoids.nonempty_dottedArrow_of_fiberObj e.genericMap
    e.j_canonical ZR (IsHomLift.codomain_eq _ e.genericMap m) m₀ hm₀ β hβ ?_
  show (outerSquare B q e).γ.hom.app zK ≫ f.hom.hom.map m₀ =
    (outerSquare B q e).y.hom.map (Over.mkIdTerminal.from (e.j.hom.obj zK)) ≫ β
  refine Functor.IsStronglyCartesian.ext 𝒴.val.val.p e.specialOver b e.genericMap ?_
  calc
    _ = (outerSquare B q e).γ.hom.app zK ≫
        f.hom.hom.map (inv v) ≫ f.hom.hom.map m ≫ b := by
      simp only [m₀, f.hom.hom.toFunctor.map_comp, Category.assoc]
    _ = (outerSquare B q e).γ.hom.app zK ≫
        f.hom.hom.map (inv v) ≫ f.hom.hom.map n ≫ pointLink B q := by rw [h]
    _ = (outerSquare B q e).γ.hom.app zK ≫ f.hom.hom.map cK ≫ pointLink B q := by
      rw [← f.hom.hom.toFunctor.map_comp_assoc, hvfac']
    _ = (outerSquare B q e).y.hom.map (Over.mkIdTerminal.from (e.j.hom.obj zK)) ≫ cR :=
      outerSquare_pointLink B q e
    _ = _ := by rw [← hβfac, Category.assoc]

/-- **A dotted arrow produces a compatible span.** The converse of
`AlgebraicGeometry.Stack.nonempty_dottedArrow_of_span`: a dotted arrow for the outer rectangle cut
out by a dominating extension `e` of a valuative square `q` gives a span in `𝒳` over the two upper
edges of the extension and a morphism of `𝒴` over its lower edge, compatible with the link of
`q`. -/
theorem exists_span_of_dottedArrow (q : ValuativeSquare B S hS f)
    (e : q.DominatingExtension)
    (d : DottedArrow (e.k ≫ q.x) e.j f.hom (e.a ≫ q.y) e.inducedGamma) :
    ∃ (ZK ZR : 𝒳.val.val.obj) (n : ZK ⟶ q.x.hom.obj (Over.mk (𝟙 _)))
      (m : ZK ⟶ ZR) (b : f.hom.hom.obj ZR ⟶ q.y.hom.obj (Over.mk (𝟙 _))),
      𝒳.val.val.p.IsHomLift e.genericOver n ∧
      𝒳.val.val.p.IsHomLift e.genericMap m ∧
      𝒴.val.val.p.IsHomLift e.specialOver b ∧
      f.hom.hom.map n ≫ pointLink B q = f.hom.hom.map m ≫ b := by
  let zK : Over (dominatingGenericObject B e) := Over.mk (𝟙 (dominatingGenericObject B e))
  let zR : Over (dominatingSpecialObject B e) := Over.mk (𝟙 (dominatingSpecialObject B e))
  let cK := q.x.hom.map (Over.mkIdTerminal.from (e.k.hom.obj zK))
  let cR := q.y.hom.map (Over.mkIdTerminal.from (e.a.hom.obj zR))
  have hcK := isHomLift_map_x_canonical B q e
  have hcR := isHomLift_map_y_canonical B q e
  have hα : 𝒳.val.val.p.IsHomLift (𝟙 (dominatingGenericObject B e)) (d.α.hom.app zK) :=
    d.α.hom.isHomLift' zK
  have hβ : 𝒴.val.val.p.IsHomLift (𝟙 (dominatingSpecialObject B e)) (d.β.hom.app zR) :=
    d.β.hom.isHomLift' zR
  obtain ⟨hαiso, hαinv⟩ := isIso_and_isHomLift_inv_of_fiber_isGroupoid
    (𝒳.val.isFiberedInGroupoids.fiber_isGroupoid (dominatingGenericObject B e)) _ hα
  obtain ⟨hβiso, hβinv⟩ := isIso_and_isHomLift_inv_of_fiber_isGroupoid
    (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid (dominatingSpecialObject B e)) _ hβ
  have ht : 𝒳.val.val.p.IsHomLift e.genericMap
      (d.a.hom.map (Over.mkIdTerminal.from (e.j.hom.obj zK))) :=
    Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_of_eq 𝒳.val.val.p e.genericMap
      (H := d.a.hom) _ (Functor.congr_obj e.j_canonical zK)
  have := hαinv
  have := hβinv
  let t := d.a.hom.map (Over.mkIdTerminal.from (e.j.hom.obj zK))
  let m := inv (d.α.hom.app zK) ≫ t
  let b := inv (d.β.hom.app zR) ≫ cR
  refine ⟨_, _, cK, m, b, hcK,
    IsHomLift.comp_lift_id_left _ _ _ _, IsHomLift.comp_lift_id_left _ _ _ _, ?_⟩
  have hγ : 𝒴.val.val.p.IsHomLift (𝟙 (dominatingGenericObject B e))
      ((outerSquare B q e).γ.hom.app zK) := (outerSquare B q e).γ.hom.isHomLift' zK
  obtain ⟨hγiso, -⟩ := isIso_and_isHomLift_inv_of_fiber_isGroupoid
    (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid (dominatingGenericObject B e)) _ hγ
  refine (cancel_epi ((outerSquare B q e).γ.hom.app zK)).mp ?_
  refine Eq.trans (outerSquare_pointLink B q e) ?_
  have hcompat := congrArg (fun η => η.hom.app zK) d.compat
  change (outerSquare B q e).γ.hom.app zK = d.β.hom.app (e.j.hom.obj zK) ≫
    𝟙 _ ≫ f.hom.hom.map (d.α.hom.app zK) at hcompat
  rw [hcompat]
  simp only [m, b, f.hom.hom.toFunctor.map_comp, Category.id_comp, Category.assoc]
  rw [← f.hom.hom.toFunctor.map_comp_assoc, IsIso.hom_inv_id,
    f.hom.hom.toFunctor.map_id, Category.id_comp]
  have hnat := d.β.hom.toNatTrans.naturality (Over.mkIdTerminal.from (e.j.hom.obj zK))
  change (outerSquare B q e).y.hom.map (Over.mkIdTerminal.from (e.j.hom.obj zK)) ≫
      d.β.hom.app zR =
    d.β.hom.app (e.j.hom.obj zK) ≫ f.hom.hom.map t at hnat
  rw [← Category.assoc (d.β.hom.app _) _, ← hnat]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rfl

end AlgebraicGeometry.Stack

end
