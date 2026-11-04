module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiQuasicoherentDescent
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic
public import StacksFrontier.CategoryTheory.Sites.Descent.OfRefinement
public import StacksFrontier.CategoryTheory.Sites.Descent.SingletonCoalgebraObj

/-!
# The chart comparison for descent of modules along an open covering

This file supplies the dictionary between a descent datum for the pullback pseudofunctor of
sheaves of modules along a covering by open subschemes and the glueing data of sheaves of
`O`-modules of Stacks 00AM.  It is the input of the effectivity half of Stacks 023E, which is
reduced in `StacksFrontier/AlgebraicGeometry/Descent/ZariskiQuasicoherentDescent.lean` to the single
statement `AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens`.

The transition morphisms of a descent datum are indexed by an *arbitrary* object mapping to two
members of the family, while a glueing datum compares sections over the *opens* contained in two
members.  Translating between the two needs, for an open `V` contained in a member `W`, a
comparison of the pullback to `V` of the pushforward of a module on `W` with the pullback along
the inclusion `V ⟶ W`: this is `AlgebraicGeometry.openChartIso`.  Its compatibility with further
pullback, `AlgebraicGeometry.pullHom_openChartIso_hom`, is what makes the transitions of the
glueing datum compatible with restriction.

## Main definitions

* `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.mapCompIso`: the comparison of the inverse
  image along a composite with the iterated inverse image, as an isomorphism of objects.
* `AlgebraicGeometry.openChartIso`: for `b : X ⟶ W` over `S` with `W` an open of `S`, the
  comparison of the pullback along `b ≫ W.ι` of a pushforward from `W` with the pullback along
  `b` of the original module.
* `AlgebraicGeometry.descentTransPullback` and `AlgebraicGeometry.descentTransRestrict`: the
  transition of a descent datum over an open `V` contained in two members, read on the pullbacks
  respectively the restrictions to `V` of the pushed-forward components.
* `AlgebraicGeometry.opensChosenPullback`: the intersection of two opens of a scheme, as a chosen
  fibre product of their inclusions.

## Main results

* `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_hom_app`: the comparison
  isomorphism of a composite is compatible with further pullback.  This is the associativity
  coherence of a pseudofunctor in the form `Pseudofunctor.LocallyDiscreteOpToCat.pullHom` needs.
* `AlgebraicGeometry.pullHom_openChartIso_hom`: the same for `openChartIso`.
* `AlgebraicGeometry.localApp_comp`, `AlgebraicGeometry.localApp_id`: the sections map of a
  morphism of restrictions is functorial.
* `AlgebraicGeometry.descentTransPullback_comp`, `AlgebraicGeometry.descentTransPullback_self`:
  the cocycle condition and the unit condition for the transitions.
* `AlgebraicGeometry.restrictLocal_descentTransRestrict`: the transitions are compatible with
  restriction to a smaller open, which is the `trans_map` field of a glueing datum.
* `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.comm_of_mapCompIso`: the compatibility
  condition that `CategoryTheory.Pseudofunctor.DescentData.isoMk` asks of a family of morphisms
  out of `CategoryTheory.Pseudofunctor.DescentData.ofObj M`, from one compatibility over `M`.
* `AlgebraicGeometry.app_comp_localApp`, `AlgebraicGeometry.restrictFunctor_map_comp_eq` and
  `AlgebraicGeometry.pullback_map_comp_eq`: the three steps that promote an identity of sections
  maps to an identity of morphisms of pullbacks along an open immersion.
* `AlgebraicGeometry.openChartIso_hom_comp_hom`: the chart comparisons carry a descent datum's
  transition to `AlgebraicGeometry.descentTransPullback`.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Limits
open scoped AlgebraicGeometry

universe v u

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

/-- **The associativity coherence of a pseudofunctor, in the form `pullHom` needs.**  Pulling
the comparison isomorphism of a composite `b ≫ a = q` back along `g` gives the comparison
isomorphism of the composite `gb ≫ a = gq`. -/
lemma pullHom_mapComp'_hom_app {X S : C} (a : X ⟶ S) (M : F.obj (.mk (op S)))
    ⦃Y Y' : C⦄ (b : Y ⟶ X) (q : Y ⟶ S) (hq : b ≫ a = q)
    (g : Y' ⟶ Y) (gb : Y' ⟶ X) (gq : Y' ⟶ S) (hgb : g ≫ b = gb) (hgq : g ≫ q = gq) :
    pullHom (F := F)
        ((F.mapComp' a.op.toLoc b.op.toLoc q.op.toLoc (by
          rw [← Quiver.Hom.comp_toLoc, ← op_comp, hq])).hom.toNatTrans.app M)
        g gq gb hgq hgb =
      (F.mapComp' a.op.toLoc gb.op.toLoc gq.op.toLoc (by
        rw [← Quiver.Hom.comp_toLoc, ← op_comp, ← hgq, ← hq, ← hgb, Category.assoc])
        ).hom.toNatTrans.app M := by
  dsimp only [pullHom]
  rw [← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app a.op.toLoc b.op.toLoc g.op.toLoc
    q.op.toLoc gb.op.toLoc gq.op.toLoc (by grind) (by grind) (by grind)]
  simp

/-- The comparison of the inverse image along a composite `b ≫ a = c` with the iterated inverse
image, as an isomorphism of objects. -/
noncomputable def mapCompIso {X Y Z : C} {a : Y ⟶ Z} {b : X ⟶ Y} {c : X ⟶ Z} (h : b ≫ a = c)
    (A : F.obj (.mk (op Z))) :
    (F.map c.op.toLoc).toFunctor.obj A ≅
      (F.map b.op.toLoc).toFunctor.obj ((F.map a.op.toLoc).toFunctor.obj A) where
  hom := (F.mapComp' a.op.toLoc b.op.toLoc c.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.app A
  inv := (F.mapComp' a.op.toLoc b.op.toLoc c.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans.app A
  hom_inv_id := Cat.Hom.hom_inv_id_toNatTrans_app _ _
  inv_hom_id := Cat.Hom.inv_hom_id_toNatTrans_app _ _

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.mapCompIso` is compatible with further
pullback. -/
lemma pullHom_mapCompIso_hom {X X' Y Z : C} {a : Y ⟶ Z} {b : X ⟶ Y} {c : X ⟶ Z}
    (h : b ≫ a = c) (A : F.obj (.mk (op Z))) (g : X' ⟶ X) {gb : X' ⟶ Y} {gc : X' ⟶ Z}
    (hgb : g ≫ b = gb) (hgc : g ≫ c = gc) :
    pullHom (F := F) (mapCompIso h A).hom g gc gb hgc hgb =
      (mapCompIso (show gb ≫ a = gc by rw [← hgb, Category.assoc, h, hgc]) A).hom :=
  pullHom_mapComp'_hom_app a A b c h g gb gc hgb hgc

/-- A comparison isomorphism of a composite, followed by the inverse image of a fixed morphism,
is compatible with further pullback. -/
lemma pullHom_mapCompIso_hom_comp_map {X X' Y Z : C} {a : Y ⟶ Z} {b : X ⟶ Y} {c : X ⟶ Z}
    (h : b ≫ a = c) (A : F.obj (.mk (op Z))) {N : F.obj (.mk (op Y))}
    (e : (F.map a.op.toLoc).toFunctor.obj A ⟶ N)
    (g : X' ⟶ X) {gb : X' ⟶ Y} {gc : X' ⟶ Z} (hgb : g ≫ b = gb) (hgc : g ≫ c = gc) :
    pullHom (F := F) ((mapCompIso h A).hom ≫ (F.map b.op.toLoc).toFunctor.map e) g gc gb
        hgc hgb =
      (mapCompIso (show gb ≫ a = gc by rw [← hgb, Category.assoc, h, hgc]) A).hom ≫
        (F.map gb.op.toLoc).toFunctor.map e := by
  rw [Pseudofunctor.pullHom_comp (F := F) _ _ g gc gb gb hgc hgb hgb,
    Pseudofunctor.pullHom_map, pullHom_mapCompIso_hom]

/-- Pulling back the identity is the identity. -/
lemma pullHom_id' {X X' Y : C} {f : X ⟶ Y} (M : F.obj (.mk (op Y))) (g : X' ⟶ X)
    {gf : X' ⟶ Y} (hgf : g ≫ f = gf) :
    pullHom (F := F) (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) g gf gf hgf hgf = 𝟙 _ := by
  simpa using Pseudofunctor.pullHom_map (F := F) (f₁ := f) (𝟙 M) g gf hgf

/-- If pulling back the forward direction of an isomorphism gives the forward direction of
another, pulling back the inverse gives its inverse. -/
lemma pullHom_inv_eq {X₁ X₂ Y Y' : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) {gf₁ : Y' ⟶ X₁} {gf₂ : Y' ⟶ X₂} (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂)
    {e' : (F.map gf₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map gf₂.op.toLoc).toFunctor.obj M₂}
    (he : pullHom (F := F) e.hom g gf₁ gf₂ h₁ h₂ = e'.hom) :
    pullHom (F := F) e.inv g gf₂ gf₁ h₂ h₁ = e'.inv := by
  rw [← cancel_epi e'.hom, Iso.hom_inv_id, ← he,
    ← Pseudofunctor.pullHom_comp (F := F) e.hom e.inv g gf₁ gf₂ gf₁ h₁ h₂ h₁,
    e.hom_inv_id, pullHom_id']

/-- A threefold composite is pulled back factor by factor.  The three factors are given by
equations rather than computed, so that the proof term stays small at a concrete pseudofunctor. -/
lemma pullHom_comp₃_eq {X₁ X₂ X₃ X₄ Y Y' : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))} {M₄ : F.obj (.mk (op X₄))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃} {f₄ : Y ⟶ X₄}
    (α : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (β : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (γ : (F.map f₃.op.toLoc).toFunctor.obj M₃ ⟶ (F.map f₄.op.toLoc).toFunctor.obj M₄)
    (g : Y' ⟶ Y) {gf₁ : Y' ⟶ X₁} {gf₂ : Y' ⟶ X₂} {gf₃ : Y' ⟶ X₃} {gf₄ : Y' ⟶ X₄}
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) (h₄ : g ≫ f₄ = gf₄)
    {α' : (F.map gf₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map gf₂.op.toLoc).toFunctor.obj M₂}
    {β' : (F.map gf₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map gf₃.op.toLoc).toFunctor.obj M₃}
    {γ' : (F.map gf₃.op.toLoc).toFunctor.obj M₃ ⟶ (F.map gf₄.op.toLoc).toFunctor.obj M₄}
    (hα : pullHom (F := F) α g gf₁ gf₂ h₁ h₂ = α')
    (hβ : pullHom (F := F) β g gf₂ gf₃ h₂ h₃ = β')
    (hγ : pullHom (F := F) γ g gf₃ gf₄ h₃ h₄ = γ') :
    pullHom (F := F) (α ≫ β ≫ γ) g gf₁ gf₄ h₁ h₄ = α' ≫ β' ≫ γ' := by
  rw [Pseudofunctor.pullHom_comp (F := F) α (β ≫ γ) g gf₁ gf₂ gf₄ h₁ h₂ h₄,
    Pseudofunctor.pullHom_comp (F := F) β γ g gf₂ gf₃ gf₄ h₂ h₃ h₄, hα, hβ, hγ]

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.mapCompIso` is natural in the object.
This is `CategoryTheory.Pseudofunctor.mapComp'_hom_naturality` with the composite given by an
equation between morphisms of the base. -/
@[reassoc]
lemma mapCompIso_hom_naturality {X Y Z : C} {a : Y ⟶ Z} {b : X ⟶ Y} {c : X ⟶ Z}
    (h : b ≫ a = c) {A A' : F.obj (.mk (op Z))} (u : A ⟶ A') :
    (F.map c.op.toLoc).toFunctor.map u ≫ (mapCompIso h A').hom =
      (mapCompIso h A).hom ≫
        (F.map b.op.toLoc).toFunctor.map ((F.map a.op.toLoc).toFunctor.map u) :=
  F.mapComp'_hom_naturality a.op.toLoc b.op.toLoc c.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h]) u

/-- **The compatibility condition of a morphism of descent data, from one over an object.**  Let
`M` be an object over `S` equipped with morphisms `χ₁ : M ⟶ P₁` and `χ₂ : M ⟶ P₂`, and let the
inverse images of `P₁` and `P₂` to `Y` along `a₁ ≫ f₁ = q = a₂ ≫ f₂` be compared with objects
`A₁` over `X₁` and `A₂` over `X₂` by `c₁` and `c₂`.  If the comparison `t` of the inverse images
of `P₁` and `P₂` to `Y` is carried to `d` by those comparisons, and if `t` is compatible with
`χ₁` and `χ₂`, then the morphisms `(F.map fₖ).map χₖ ≫ cₖ` satisfy the compatibility condition
that `CategoryTheory.Pseudofunctor.DescentData.isoMk` asks of a family of morphisms out of
`CategoryTheory.Pseudofunctor.DescentData.ofObj M`.

The three comparisons `O₁`, `O₂` and the inverse-image morphism `d` are given by equations rather
than computed, so that the proof term stays small at a concrete pseudofunctor. -/
lemma comm_of_mapCompIso {X₁ X₂ Y S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    {a₁ : Y ⟶ X₁} {a₂ : Y ⟶ X₂} {q : Y ⟶ S} (h₁ : a₁ ≫ f₁ = q) (h₂ : a₂ ≫ f₂ = q)
    {M P₁ P₂ : F.obj (.mk (op S))} {A₁ : F.obj (.mk (op X₁))} {A₂ : F.obj (.mk (op X₂))}
    (χ₁ : M ⟶ P₁) (χ₂ : M ⟶ P₂)
    {c₁ : (F.map f₁.op.toLoc).toFunctor.obj P₁ ⟶ A₁}
    {c₂ : (F.map f₂.op.toLoc).toFunctor.obj P₂ ⟶ A₂}
    {d : (F.map a₁.op.toLoc).toFunctor.obj A₁ ⟶ (F.map a₂.op.toLoc).toFunctor.obj A₂}
    {t : (F.map q.op.toLoc).toFunctor.obj P₁ ⟶ (F.map q.op.toLoc).toFunctor.obj P₂}
    {O₁ : (F.map q.op.toLoc).toFunctor.obj P₁ ⟶ (F.map a₁.op.toLoc).toFunctor.obj A₁}
    {O₂ : (F.map q.op.toLoc).toFunctor.obj P₂ ⟶ (F.map a₂.op.toLoc).toFunctor.obj A₂}
    (hO₁ : (mapCompIso h₁ P₁).hom ≫ (F.map a₁.op.toLoc).toFunctor.map c₁ = O₁)
    (hO₂ : (mapCompIso h₂ P₂).hom ≫ (F.map a₂.op.toLoc).toFunctor.map c₂ = O₂)
    (ht : O₁ ≫ d = t ≫ O₂)
    (hχ : (F.map q.op.toLoc).toFunctor.map χ₁ ≫ t = (F.map q.op.toLoc).toFunctor.map χ₂) :
    (F.map a₁.op.toLoc).toFunctor.map ((F.map f₁.op.toLoc).toFunctor.map χ₁ ≫ c₁) ≫ d =
      ((mapCompIso h₁ M).inv ≫ (mapCompIso h₂ M).hom) ≫
        (F.map a₂.op.toLoc).toFunctor.map ((F.map f₂.op.toLoc).toFunctor.map χ₂ ≫ c₂) := by
  rw [← cancel_epi (mapCompIso h₁ M).hom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← mapCompIso_hom_naturality_assoc h₁ χ₁, ← mapCompIso_hom_naturality_assoc h₂ χ₂,
    reassoc_of% hO₁, hO₂, ht, reassoc_of% hχ]

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Stacks.SheafOfModules Pseudofunctor.LocallyDiscreteOpToCat

/-- The pullback along the inclusion of an open subscheme of the pushforward of a sheaf of
modules on it is that sheaf.  This is the counit of the restriction adjunction, read through the
comparison of restriction with pullback. -/
noncomputable def pushforwardCounitIso {S : Scheme.{u}} (W : S.Opens)
    (N : (W : Scheme.{u}).Modules) :
    (modulePullbackPseudofunctor.map W.ι.op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward W.ι).obj N) ≅ N :=
  ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app N

/-- **The chart comparison.**  For `b : X ⟶ W` with `b ≫ W.ι = c`, the pullback along `c` of
the pushforward from the open subscheme `W` of a sheaf of modules `N` is the pullback of `N`
along `b`. -/
noncomputable def openChartIso {S X : Scheme.{u}} {W : S.Opens}
    {b : X ⟶ (W : Scheme.{u})} {c : X ⟶ S} (h : b ≫ W.ι = c) (N : (W : Scheme.{u}).Modules) :
    (modulePullbackPseudofunctor.map c.op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward W.ι).obj N) ≅
      (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.obj N :=
  mapCompIso h _ ≪≫ (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.mapIso
    (pushforwardCounitIso W N)

/-- **The chart comparison is compatible with further pullback.**  This is what makes the
transitions of the associated glueing datum compatible with restriction. -/
lemma pullHom_openChartIso_hom {S X X' : Scheme.{u}} {W : S.Opens}
    {b : X ⟶ (W : Scheme.{u})} {c : X ⟶ S} (h : b ≫ W.ι = c) (N : (W : Scheme.{u}).Modules)
    (g : X' ⟶ X) {gb : X' ⟶ (W : Scheme.{u})} {gc : X' ⟶ S} (hgb : g ≫ b = gb)
    (hgc : g ≫ c = gc) :
    pullHom (F := modulePullbackPseudofunctor) (openChartIso h N).hom g gc gb hgc hgb =
      (openChartIso (show gb ≫ W.ι = gc by rw [← hgb, Category.assoc, h, hgc]) N).hom :=
  pullHom_mapCompIso_hom_comp_map h _ (pushforwardCounitIso W N).hom g hgb hgc

/-- The inverse of the chart comparison is compatible with further pullback. -/
lemma pullHom_openChartIso_inv {S X X' : Scheme.{u}} {W : S.Opens}
    {b : X ⟶ (W : Scheme.{u})} {c : X ⟶ S} (h : b ≫ W.ι = c) (N : (W : Scheme.{u}).Modules)
    (g : X' ⟶ X) {gb : X' ⟶ (W : Scheme.{u})} {gc : X' ⟶ S} (hgb : g ≫ b = gb)
    (hgc : g ≫ c = gc) :
    pullHom (F := modulePullbackPseudofunctor) (openChartIso h N).inv g gb gc hgb hgc =
      (openChartIso (show gb ≫ W.ι = gc by rw [← hgb, Category.assoc, h, hgc]) N).inv :=
  pullHom_inv_eq _ g hgc hgb (pullHom_openChartIso_hom h N g hgb hgc)

/-- The chart comparison, factored as the comparison of the inverse image along a composite
followed by the inverse image of the counit.  This is the shape in which
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.comm_of_mapCompIso` consumes it. -/
lemma openChartIso_hom_eq {S X : Scheme.{u}} {W : S.Opens} {b : X ⟶ (W : Scheme.{u})}
    {c : X ⟶ S} (h : b ≫ W.ι = c) (N : (W : Scheme.{u}).Modules) :
    (mapCompIso h ((Scheme.Modules.pushforward W.ι).obj N)).hom ≫
        (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.map
          (pushforwardCounitIso W N).hom =
      (openChartIso h N).hom := rfl

/-- **An isomorphism of a restriction, read on the pullback.**  If a morphism
`χ : M ⟶ (pushforward W.ι).obj N` restricts to an isomorphism `e` of `M.restrict W.ι` with `N`,
then `e`, transported to the pullback along `W.ι`, is the pullback of `χ` followed by the counit
comparison `AlgebraicGeometry.pushforwardCounitIso` (whose right-hand side is spelled out here so
that the statement mentions only honest sheaves of modules). -/
lemma restrictFunctorIsoPullback_symm_trans_hom {S : Scheme.{u}} (W : S.Opens)
    {M : S.Modules} {N : (W : Scheme.{u}).Modules}
    (χ : M ⟶ (Scheme.Modules.pushforward W.ι).obj N)
    (e : Scheme.Modules.restrict M W.ι ≅ N)
    (he : (Scheme.Modules.restrictFunctor W.ι).map χ ≫
      ((Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app N).hom = e.hom) :
    ((((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm ≪≫ e)).hom =
      (Scheme.Modules.pullback W.ι).map χ ≫
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app
            ((Scheme.Modules.pushforward W.ι).obj N)).inv ≫
          ((Scheme.Modules.restrictFunctorAdjCounitIso W.ι).app N).hom := by
  rw [Iso.trans_hom, Iso.symm_hom, ← he, Iso.app_inv, Iso.app_inv, ← Category.assoc,
    ← (Scheme.Modules.restrictFunctorIsoPullback W.ι).inv.naturality χ, Category.assoc]

/-- **Two open subschemes meet in their intersection.**  The intersection of two opens of a
scheme, as a chosen fibre product of their inclusions. -/
noncomputable def opensChosenPullback {S : Scheme.{u}} (U V : S.Opens) :
    ChosenPullback U.ι V.ι where
  pullback := (U ⊓ V : S.Opens)
  p₁ := S.homOfLE inf_le_left
  p₂ := S.homOfLE inf_le_right
  condition := (isPullback_opens_inf U V).w
  isLimit := (isPullback_opens_inf U V).isLimit
  p := (U ⊓ V : S.Opens).ι
  hp₁ := Scheme.homOfLE_ι S inf_le_left

section LocalApp

variable {X : Scheme.{u}} {W : X.Opens}

/-- A round trip of restriction maps of a module inside a longer composite is the identity. -/
lemma presheaf_map_round_assoc (M : X.Modules) {P Q : (X.Opens)ᵒᵖ} (h₁ : P ⟶ Q) (h₂ : Q ⟶ P)
    {Z : Ab} (k : M.presheaf.obj P ⟶ Z) :
    M.presheaf.map h₁ ≫ M.presheaf.map h₂ ≫ k = k := by
  rw [presheaf_map_comp₂_assoc M h₁ h₂ (𝟙 _), CategoryTheory.Functor.map_id, Category.id_comp]

/-- `AlgebraicGeometry.localApp` is multiplicative. -/
lemma localApp_comp {A B C : X.Modules}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (ψ : Scheme.Modules.restrict B W.ι ⟶ Scheme.Modules.restrict C W.ι)
    (V : X.Opens) (hV : V ≤ W) :
    localApp (φ ≫ ψ) V hV = localApp φ V hV ≫ localApp ψ V hV := by
  simp only [localApp, Scheme.Modules.Hom.comp_app, Category.assoc]
  rw [presheaf_map_round_assoc B _ _, Iso.hom_inv_id_assoc]

/-- `AlgebraicGeometry.localApp` is unital. -/
lemma localApp_id (A : X.Modules) (V : X.Opens) (hV : V ≤ W) :
    localApp (𝟙 (Scheme.Modules.restrict A W.ι)) V hV = 𝟙 _ := by
  simp only [localApp, Scheme.Modules.Hom.id_app, Category.id_comp, Iso.inv_hom_id_assoc]
  rw [presheaf_map_comp₂ A _ _ (𝟙 _), CategoryTheory.Functor.map_id]

/-- The sections map of the restriction of a global morphism, at an open of the form
`W.ι ''ᵁ U`, is the component of that morphism. -/
lemma localApp_restrictFunctor_map_image {A B : X.Modules} (ψ : A ⟶ B) (U : W.toScheme.Opens) :
    localApp ((Scheme.Modules.restrictFunctor W.ι).map ψ) (W.ι ''ᵁ U)
        (Scheme.Opens.ι_image_le W U) = ψ.app (W.ι ''ᵁ U) := by
  rw [localApp_image, restrictFunctor_map_app]
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_inv, Iso.refl_hom]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The sections map over `V ≤ W` of a morphism of the restrictions to `W`, as a function on the
underlying types of the modules of sections. -/
noncomputable def localAppFun {A B : X.Modules}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (V : X.Opens)
    (hV : V ≤ W) : ToType (A.val.obj (op V)) → ToType (B.val.obj (op V)) :=
  fun s ↦ ConcreteCategory.hom (localApp φ V hV) s

/-- `AlgebraicGeometry.localAppFun` is multiplicative. -/
lemma localAppFun_comp {A B C : X.Modules}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (ψ : Scheme.Modules.restrict B W.ι ⟶ Scheme.Modules.restrict C W.ι)
    (V : X.Opens) (hV : V ≤ W) (s : ToType (A.val.obj (op V))) :
    localAppFun (φ ≫ ψ) V hV s = localAppFun ψ V hV (localAppFun φ V hV s) :=
  ConcreteCategory.congr_hom (localApp_comp φ ψ V hV) s

/-- `AlgebraicGeometry.localAppFun` is unital. -/
lemma localAppFun_id (A : X.Modules) (V : X.Opens) (hV : V ≤ W)
    (s : ToType (A.val.obj (op V))) :
    localAppFun (𝟙 (Scheme.Modules.restrict A W.ι)) V hV s = s :=
  ConcreteCategory.congr_hom (localApp_id A V hV) s

/-- `AlgebraicGeometry.localAppFun` commutes with restriction of sections. -/
lemma localAppFun_naturality {A B : X.Modules}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) {V V' : X.Opens}
    (hV : V ≤ W) (hV' : V' ≤ W) (i : V' ⟶ V) (s : ToType (A.val.obj (op V))) :
    B.val.map i.op (localAppFun φ V hV s) = localAppFun φ V' hV' (A.val.map i.op s) :=
  ConcreteCategory.congr_hom (localApp_naturality φ hV hV' i) s

/-- `AlgebraicGeometry.localAppFun` is linear over the functions on the open. -/
lemma localAppFun_smul {A B : X.Modules}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (V : X.Opens)
    (hV : V ≤ W) (r : ToType (X.ringCatSheaf.obj.obj (op V)))
    (s : ToType (A.val.obj (op V))) :
    localAppFun φ V hV (r • s) = r • localAppFun φ V hV s :=
  localApp_smul φ V hV r s

/-- **The sections equivalence of an isomorphism of restrictions.**  An isomorphism of the
restrictions to an open `W` of two sheaves of modules induces, over every open `V ≤ W`, a
linear equivalence of the modules of sections. -/
noncomputable def localAppEquiv {A B : X.Modules}
    (φ : Scheme.Modules.restrict A W.ι ≅ Scheme.Modules.restrict B W.ι) (V : X.Opens)
    (hV : V ≤ W) :
    ToType (A.val.obj (op V)) ≃ₗ[ToType (X.ringCatSheaf.obj.obj (op V))]
      ToType (B.val.obj (op V)) where
  toFun := localAppFun φ.hom V hV
  invFun := localAppFun φ.inv V hV
  map_add' s t :=
    map_add (ConcreteCategory.hom (localApp φ.hom V hV)) s t
  map_smul' r s := by simpa using localAppFun_smul φ.hom V hV r s
  left_inv s := by
    rw [← localAppFun_comp, φ.hom_inv_id, localAppFun_id]
  right_inv s := by
    rw [← localAppFun_comp, φ.inv_hom_id, localAppFun_id]

/-- `AlgebraicGeometry.localAppEquiv` is `AlgebraicGeometry.localAppFun`. -/
lemma localAppEquiv_apply {A B : X.Modules}
    (φ : Scheme.Modules.restrict A W.ι ≅ Scheme.Modules.restrict B W.ι) (V : X.Opens)
    (hV : V ≤ W) (s : ToType (A.val.obj (op V))) :
    localAppEquiv φ V hV s = localAppFun φ.hom V hV s := rfl

/-- **A morphism of restrictions is determined by its sections maps.**  Two morphisms of the
restrictions to `W` of two sheaves of modules agree as soon as their sections maps over the opens
of the form `W.ι ''ᵁ U` agree. -/
lemma hom_ext_of_localApp_image {A B : X.Modules}
    (φ ψ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (h : ∀ U : W.toScheme.Opens, localApp φ (W.ι ''ᵁ U) (Scheme.Opens.ι_image_le W U) =
      localApp ψ (W.ι ''ᵁ U) (Scheme.Opens.ι_image_le W U)) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  have h' := ((localApp_image φ U).symm.trans (h U)).trans (localApp_image ψ U)
  exact (cancel_mono (B.restrictAppIso W.ι U).hom).mp
    ((cancel_epi (A.restrictAppIso W.ι U).inv).mp h')

/-- **From sections to the sections map.**  A triangle of sections maps over a single open `V`
commutes as soon as it commutes on every section.

The sections map is spelled with `CategoryTheory.ConcreteCategory.hom`, which is the spelling
`AlgebraicGeometry.localAppFun` uses, so no further translation is needed.  The `ext` tactic
would instead produce `AddCommGrpCat.Hom.hom`, in which none of the `localAppFun` lemmas apply. -/
lemma app_comp_localApp {G A B : X.Modules} {V : X.Opens} (hV : V ≤ W) (φ : G ⟶ A) (ψ : G ⟶ B)
    (θ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (h : ∀ s : ToType (G.val.obj (op V)), localAppFun θ V hV (φ.app V s) = ψ.app V s) :
    φ.app V ≫ localApp θ V hV = ψ.app V :=
  ConcreteCategory.ext_apply fun s ↦ (CategoryTheory.comp_apply _ _ s).trans (h s)

/-- **From the sections maps to the morphism.**  A triangle whose slanted side is a morphism of
restrictions commutes as soon as the triangles of sections maps over the opens contained in `W`
commute. -/
lemma restrictFunctor_map_comp_eq {G A B : X.Modules} (φ : G ⟶ A) (ψ : G ⟶ B)
    (θ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (h : ∀ (V : X.Opens) (hV : V ≤ W), φ.app V ≫ localApp θ V hV = ψ.app V) :
    (Scheme.Modules.restrictFunctor W.ι).map φ ≫ θ =
      (Scheme.Modules.restrictFunctor W.ι).map ψ :=
  hom_ext_of_localApp_image _ _ fun U ↦
    (localApp_comp _ _ _ _).trans
      ((congrArg (· ≫ localApp θ (W.ι ''ᵁ U) (Scheme.Opens.ι_image_le W U))
          (localApp_restrictFunctor_map_image φ U)).trans
        ((h (W.ι ''ᵁ U) (Scheme.Opens.ι_image_le W U)).trans
          (localApp_restrictFunctor_map_image ψ U).symm))

end LocalApp

section RestrictHom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- `AlgebraicGeometry.restrictHomOfPullbackHom` is multiplicative. -/
lemma restrictHomOfPullbackHom_comp {A B C : Y.Modules}
    (θ : (Scheme.Modules.pullback f).obj A ⟶ (Scheme.Modules.pullback f).obj B)
    (θ' : (Scheme.Modules.pullback f).obj B ⟶ (Scheme.Modules.pullback f).obj C) :
    restrictHomOfPullbackHom f (θ ≫ θ') =
      restrictHomOfPullbackHom f θ ≫ restrictHomOfPullbackHom f θ' := by
  simp [restrictHomOfPullbackHom]

/-- `AlgebraicGeometry.restrictHomOfPullbackHom` is unital. -/
lemma restrictHomOfPullbackHom_id (A : Y.Modules) :
    restrictHomOfPullbackHom f (𝟙 ((Scheme.Modules.pullback f).obj A)) = 𝟙 _ := by
  simp [restrictHomOfPullbackHom]

/-- **From the restrictions to the pullbacks.**  A triangle whose slanted side is a morphism of
pullbacks along an open immersion commutes as soon as the corresponding triangle of restrictions
commutes, because `AlgebraicGeometry.restrictHomOfPullbackHom` is injective. -/
lemma pullback_map_comp_eq {G A B : Y.Modules} (φ : G ⟶ A) (ψ : G ⟶ B)
    (η : (Scheme.Modules.pullback f).obj A ⟶ (Scheme.Modules.pullback f).obj B)
    (h : (Scheme.Modules.restrictFunctor f).map φ ≫ restrictHomOfPullbackHom f η =
      (Scheme.Modules.restrictFunctor f).map ψ) :
    (Scheme.Modules.pullback f).map φ ≫ η = (Scheme.Modules.pullback f).map ψ :=
  restrictHomOfPullbackHom_injective f
    ((restrictHomOfPullbackHom_comp f _ _).trans
      ((congrArg (· ≫ restrictHomOfPullbackHom f η) (restrictHomOfPullbackHom_map f φ)).trans
        (h.trans (restrictHomOfPullbackHom_map f ψ).symm)))

end RestrictHom

section Glue

variable {S : Scheme.{u}} {ιt : Type u} {W : ιt → S.Opens}
  (D : modulePullbackPseudofunctor.DescentData (fun i ↦ (W i).ι))

/-- The transition of a descent datum over an open `V` contained in both `W i` and `W j`, read
as a morphism of the pullbacks to `V` of the pushed-forward components. -/
noncomputable def descentTransPullback (i j : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j) :
    (modulePullbackPseudofunctor.map V.ι.op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)) ⟶
      (modulePullbackPseudofunctor.map V.ι.op.toLoc).toFunctor.obj
        ((Scheme.Modules.pushforward (W j).ι).obj (D.obj j)) :=
  (openChartIso (Scheme.homOfLE_ι S hi) (D.obj i)).hom ≫
    D.hom V.ι (S.homOfLE hi) (S.homOfLE hj) (Scheme.homOfLE_ι S hi) (Scheme.homOfLE_ι S hj) ≫
    (openChartIso (Scheme.homOfLE_ι S hj) (D.obj j)).inv

/-- The transitions compose. -/
lemma descentTransPullback_comp (i j k : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j)
    (hk : V ≤ W k) :
    descentTransPullback D i j hi hj ≫ descentTransPullback D j k hj hk =
      descentTransPullback D i k hi hk := by
  simp only [descentTransPullback, Category.assoc, Iso.inv_hom_id_assoc,
    Pseudofunctor.DescentData.hom_comp_assoc]

/-- The transition from a member to itself is the identity. -/
lemma descentTransPullback_self (i : ιt) {V : S.Opens} (hi hi' : V ≤ W i) :
    descentTransPullback D i i hi hi' = 𝟙 _ := by
  simp only [descentTransPullback]
  rw [D.hom_self V.ι (S.homOfLE hi) (Scheme.homOfLE_ι S hi)]
  simp

/-- **The chart comparisons carry the datum's transition to the transition over `V`.**  This is
the equation that `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.comm_of_mapCompIso` takes
as its hypothesis `ht`. -/
lemma openChartIso_hom_comp_hom (i j : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j) :
    (openChartIso (Scheme.homOfLE_ι S hi) (D.obj i)).hom ≫
        D.hom V.ι (S.homOfLE hi) (S.homOfLE hj)
          (Scheme.homOfLE_ι S hi) (Scheme.homOfLE_ι S hj) =
      descentTransPullback D i j hi hj ≫
        (openChartIso (Scheme.homOfLE_ι S hj) (D.obj j)).hom := by
  simp only [descentTransPullback, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Pulling the transition back to a smaller open gives the transition over that open. -/
lemma pullHom_descentTransPullback (i j : ιt) {V V' : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j)
    (hV' : V' ≤ V) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
        (descentTransPullback D i j hi hj) (S.homOfLE hV') V'.ι V'.ι
        (Scheme.homOfLE_ι S hV') (Scheme.homOfLE_ι S hV') =
      descentTransPullback D i j (hV'.trans hi) (hV'.trans hj) :=
  pullHom_comp₃_eq _ _ _ (S.homOfLE hV') (Scheme.homOfLE_ι S hV')
    (Scheme.homOfLE_homOfLE S hV' hi) (Scheme.homOfLE_homOfLE S hV' hj)
    (Scheme.homOfLE_ι S hV')
    (pullHom_openChartIso_hom (Scheme.homOfLE_ι S hi) (D.obj i) (S.homOfLE hV')
      (Scheme.homOfLE_homOfLE S hV' hi) (Scheme.homOfLE_ι S hV'))
    (D.pullHom_hom (S.homOfLE hV') V.ι V'.ι (Scheme.homOfLE_ι S hV') (S.homOfLE hi)
      (S.homOfLE hj) (Scheme.homOfLE_ι S hi) (Scheme.homOfLE_ι S hj)
      (S.homOfLE (hV'.trans hi)) (S.homOfLE (hV'.trans hj))
      (Scheme.homOfLE_homOfLE S hV' hi) (Scheme.homOfLE_homOfLE S hV' hj))
    (pullHom_openChartIso_inv (Scheme.homOfLE_ι S hj) (D.obj j) (S.homOfLE hV')
      (Scheme.homOfLE_homOfLE S hV' hj) (Scheme.homOfLE_ι S hV'))

/-- The transition of a descent datum over `V`, read as a morphism of the restrictions to `V` of
the pushed-forward components. -/
noncomputable def descentTransRestrict (i j : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)) V.ι ⟶
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (W j).ι).obj (D.obj j)) V.ι :=
  restrictHomOfPullbackHom V.ι (descentTransPullback D i j hi hj)

/-- The transitions, read on restrictions, compose. -/
lemma descentTransRestrict_comp (i j k : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j)
    (hk : V ≤ W k) :
    descentTransRestrict D i j hi hj ≫ descentTransRestrict D j k hj hk =
      descentTransRestrict D i k hi hk :=
  (restrictHomOfPullbackHom_comp V.ι _ _).symm.trans
    (congrArg (restrictHomOfPullbackHom V.ι) (descentTransPullback_comp D i j k hi hj hk))

/-- The transition from a member to itself, read on restrictions, is the identity. -/
lemma descentTransRestrict_self (i : ιt) {V : S.Opens} (hi hi' : V ≤ W i) :
    descentTransRestrict D i i hi hi' = 𝟙 _ :=
  (congrArg (restrictHomOfPullbackHom V.ι) (descentTransPullback_self D i hi hi')).trans
    (restrictHomOfPullbackHom_id V.ι _)

/-- Restricting the transition to a smaller open gives the transition over that open. -/
lemma restrictLocal_descentTransRestrict (i j : ιt) {V V' : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) (hV' : V' ≤ V) :
    restrictLocal (descentTransRestrict D i j hi hj) hV' =
      descentTransRestrict D i j (hV'.trans hi) (hV'.trans hj) :=
  (restrictLocal_restrictHomOfPullbackHom hV' _).trans
    (congrArg (restrictHomOfPullbackHom V'.ι)
      (pullHom_descentTransPullback D i j hi hj hV'))

end Glue

end AlgebraicGeometry

end
