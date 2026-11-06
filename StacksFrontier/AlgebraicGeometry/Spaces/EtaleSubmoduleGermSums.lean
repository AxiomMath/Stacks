module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGerms
public import StacksFrontier.CategoryTheory.Sites.Modules.SubmoduleSupLocal

/-!
# Germ sets of submodules on the small étale site: transport, locality and sums

Let `X` be an algebraic space, `M` an `𝒪_X`-module, `g : Y ⟶ X` étale and `N ⊆ M|_Y` a
submodule.  The germ set `AlgebraicGeometry.Space.etaleGermSet` of `N` at a lift `t` of a geometric
point `x̄` of `X` is a subset of the fibre of `M` at `x̄`.  This file proves four facts about it.

* It is the image of the germ set of `N` at the lifted geometric point of `Y` under the
  identification of fibres of Stacks' Equation 08GT.
* A section of `M` whose germ lies in the germ set of a submodule lies in that submodule over a
  neighbourhood of the point.
* It is closed under sums of germs of sections over a common chart.
* The germ set of `N₁ ⊔ N₂` is contained in every germ set containing those of `N₁` and `N₂`
  which is closed under sums.

## Main results

* `AlgebraicGeometry.Space.etaleGermSet_eq_image_submoduleGermSet`: the transport.
* `AlgebraicGeometry.Space.exists_map_mem_of_toPresheafFiber_mem_submoduleGermSet`: locality.
* `AlgebraicGeometry.Space.toPresheafFiber_add_mem_etaleGermSet`: closure under sums.
* `AlgebraicGeometry.Space.etaleGermSet_sup_subset`: germ sets of a supremum.

## Implementation notes

The fibre of a module at a geometric point is taken here, as in
`AlgebraicGeometry.Space.etaleGermSet`, of the presheaf of *sets* underlying the module, which
carries no addition.  Sums of germs are compared through the fibre of the underlying presheaf of
abelian groups, to which the fibre of sets is identified by
`CategoryTheory.GrothendieckTopology.Point.presheafFiberCompIso`, the forgetful functor of abelian
groups preserving filtered colimits:
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_add`.

## References

* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) {R : Cᵒᵖ ⥤ RingCat.{w}} (M : PresheafOfModules.{w} R)

/-- **Germs of sums are sums of germs.**  If two sections of a presheaf of modules over `Y` have
the same germs at a point of the site as two sections over `Z`, then so do their sums.  The fibre
is that of the presheaf of sets underlying `M`. -/
theorem toPresheafFiber_add {Y Z : C} (y : Φ.fiber.obj Y) (z : Φ.fiber.obj Z)
    (a₁ a₂ : M.obj (op Y)) (b₁ b₂ : M.obj (op Z))
    (h₁ : Φ.toPresheafFiber Y y (M.presheaf ⋙ forget AddCommGrpCat) a₁ =
      Φ.toPresheafFiber Z z (M.presheaf ⋙ forget AddCommGrpCat) b₁)
    (h₂ : Φ.toPresheafFiber Y y (M.presheaf ⋙ forget AddCommGrpCat) a₂ =
      Φ.toPresheafFiber Z z (M.presheaf ⋙ forget AddCommGrpCat) b₂) :
    Φ.toPresheafFiber Y y (M.presheaf ⋙ forget AddCommGrpCat) (a₁ + a₂) =
      Φ.toPresheafFiber Z z (M.presheaf ⋙ forget AddCommGrpCat) (b₁ + b₂) := by
  let e := (Φ.presheafFiberCompIso (forget AddCommGrpCat.{w})).app M.presheaf
  have key : ∀ {X : C} (x : Φ.fiber.obj X) (a : M.obj (op X)),
      e.hom (Φ.toPresheafFiber X x (M.presheaf ⋙ forget AddCommGrpCat) a) =
        Φ.toPresheafFiber X x M.presheaf a := fun {X} x a =>
    ConcreteCategory.congr_hom
      (Φ.toPresheafFiber_presheafFiberCompIso_hom_app (forget AddCommGrpCat) X x M.presheaf) a
  have hadd : ∀ {X : C} (x : Φ.fiber.obj X) (a a' : M.obj (op X)),
      Φ.toPresheafFiber X x M.presheaf (a + a') =
        Φ.toPresheafFiber X x M.presheaf a + Φ.toPresheafFiber X x M.presheaf a' :=
    fun {X} x a a' => map_add (Φ.toPresheafFiber X x M.presheaf).hom a a'
  have hinj : Function.Injective e.hom := fun p q h => by
    simpa using congr_arg e.inv h
  apply hinj
  rw [key, key, hadd, hadd, ← key, ← key, h₁, h₂, key, key]

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transport

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- **The germ set of `N ⊆ M|_Y` at a lift is the transported germ set at the lifted point.**
The germ set of `N` at a lift `t` of a geometric point of `X` is the image, under the
identification of fibres of Stacks' Equation 08GT, of the germ set of `N` at the geometric point
of `Y` which `t` determines. -/
theorem etaleGermSet_eq_image_submoduleGermSet
    (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x) :
    etaleGermSet B S hS g hg N t =
      ((restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app
        (etaleModuleSectionsPresheaf B S hS M)).hom ''
        submoduleGermSet B S hS N (liftGeometricPoint B S hS g t) := by
  have hι : ∀ (V : SmallEtale B S hS Y.1) (w : (liftSitePoint B S hS g t).fiber.obj V)
      (n : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V))),
      ((restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app
        (etaleModuleSectionsPresheaf B S hS M)).hom
          ((liftSitePoint B S hS g t).toPresheafFiber V w
            ((smallEtalePostcomp B S hS g hg).op ⋙ etaleModuleSectionsPresheaf B S hS M) n) =
        (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber
          ((smallEtalePostcomp B S hS g hg).obj V) (pushLift B S hS g hg V t w)
          (etaleModuleSectionsPresheaf B S hS M) n := fun V w n => by
    have := ConcreteCategory.congr_hom
      (restrictionPresheafFiberIso_toPresheafFiber (A := Type u) B S hS g hg t
        (etaleModuleSectionsPresheaf B S hS M) V w) n
    exact this
  ext e
  constructor
  · rintro ⟨V, w, n, hn, rfl⟩
    exact ⟨_, ⟨V, w, n, hn, rfl⟩, hι V w n⟩
  · rintro ⟨_, ⟨V, w, n, hn, rfl⟩, rfl⟩
    exact ⟨V, w, n, hn, (hι V w n).symm⟩

end Transport

section Locality

variable {X : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS X.1 X.2}

/-- **A section whose germ lies in the germ set of a submodule lies in it near the point.**  If
the germ of a section `s` over a chart `V` at a lift `p` of a geometric point lies in the germ
set of a submodule `N`, then over some chart `V' ⟶ V` through which `p` lifts the restriction of
`s` is a section of `N`. -/
theorem exists_map_mem_of_toPresheafFiber_mem_submoduleGermSet (N : M.Submodule)
    {x : GeometricPoint B S hS X.1} {V : SmallEtale B S hS X.1}
    (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V) (s : M.val.obj (op V))
    (h : (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber V p
      (etaleModuleSectionsPresheaf B S hS M) s ∈ submoduleGermSet B S hS N x) :
    ∃ (V' : SmallEtale B S hS X.1) (ψ : V' ⟶ V)
      (p' : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V'),
      (etaleSitePoint B S hS X.1 x X.2).fiber.map ψ p' = p ∧ M.val.map ψ.op s ∈ N.obj (op V') := by
  obtain ⟨V', w', n, hn, he⟩ := h
  let Φ := etaleSitePoint B S hS X.1 x X.2
  let P := etaleModuleSectionsPresheaf B S hS M
  obtain ⟨@⟨V₀, w₀⟩, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs
    (C := Φ.fiber.Elements) (Φ.fiber.elementsMk V p) (Φ.fiber.elementsMk V' w')
  have ha := Φ.toPresheafFiber_w_apply a.hom w₀ P s
  have hb := Φ.toPresheafFiber_w_apply b.hom w₀ P n
  rw [a.map_val] at ha
  rw [b.map_val] at hb
  have heq := he.symm
  rw [← ha, ← hb] at heq
  obtain ⟨V₁, c, w₁, hc, hcs⟩ := (Φ.toPresheafFiber_eq_iff' V₀ w₀ _ _).1 heq
  refine ⟨V₁, c ≫ a.hom, w₁, ?_, ?_⟩
  · change Φ.fiber.map (c ≫ a.hom) w₁ = p
    rw [Functor.map_comp, types_comp_apply, hc, a.map_val]
  · have hn' := N.map_mem (c ≫ b.hom).op hn
    have e : M.val.map (c ≫ a.hom).op s = M.val.map (c ≫ b.hom).op n := by
      have e1 := PresheafOfModules.map_comp_apply M.val a.hom.op c.op s
      have e2 := PresheafOfModules.map_comp_apply M.val b.hom.op c.op n
      exact e1.trans (hcs.trans e2.symm)
    rw [e]
    exact hn'

end Locality

section Sums

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- The germ at a pushed lift of the restriction of a section of `M|_Y` along a morphism of the
fibre category of the point of `Y` is the germ of the section itself. -/
theorem toPresheafFiber_pushLift_map {x : GeometricPoint B S hS X.1}
    (t : GeometricPointLift B S hS g.hom x)
    {V₀ V₁ : SmallEtale B S hS Y.1} {w₀ : (liftSitePoint B S hS g t).fiber.obj V₀}
    {w₁ : (liftSitePoint B S hS g t).fiber.obj V₁} (a : V₀ ⟶ V₁)
    (ha : (liftSitePoint B S hS g t).fiber.map a w₀ = w₁)
    (n : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (op V₁)) :
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber _ (pushLift B S hS g hg V₀ t w₀)
        (etaleModuleSectionsPresheaf B S hS M)
        (((etaleModulePullback.{u, u} B S hS g hg).obj M).val.map a.op n) =
      (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber _ (pushLift B S hS g hg V₁ t w₁)
        (etaleModuleSectionsPresheaf B S hS M) n := by
  refine ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_w_apply
    ((smallEtalePostcomp B S hS g hg).map a) (pushLift B S hS g hg V₀ t w₀)
    (etaleModuleSectionsPresheaf B S hS M) n).trans ?_
  rw [pushLift_map, ha]

/-- The sum of two sections of a submodule of `M|_Y`, as a section of `M`. -/
theorem add_mem_etaleSubmodule_obj
    (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule) {V : SmallEtale B S hS Y.1}
    (n₁ n₂ : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (op V))
    (h₁ : n₁ ∈ N.obj (op V)) (h₂ : n₂ ∈ N.obj (op V)) :
    ((n₁ : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V))) + n₂) ∈ N.obj (op V) :=
  (N.obj (op V)).add_mem h₁ h₂

/-- **Germ sets are closed under sums.**  If the germs at a point of two sections of `M` over a
common chart lie in the germ set of `N ⊆ M|_Y` at a lift, so does the germ of their sum. -/
theorem toPresheafFiber_add_mem_etaleGermSet
    (N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    {Z : SmallEtale B S hS X.1} (z : (etaleSitePoint B S hS X.1 x X.2).fiber.obj Z)
    (s₁ s₂ : M.val.obj (op Z))
    (h₁ : (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber Z z
      (etaleModuleSectionsPresheaf B S hS M) s₁ ∈ etaleGermSet B S hS g hg N t)
    (h₂ : (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber Z z
      (etaleModuleSectionsPresheaf B S hS M) s₂ ∈ etaleGermSet B S hS g hg N t) :
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber Z z
      (etaleModuleSectionsPresheaf B S hS M) (s₁ + s₂) ∈ etaleGermSet B S hS g hg N t := by
  obtain ⟨V₁, w₁, n₁, hn₁, he₁⟩ := h₁
  obtain ⟨V₂, w₂, n₂, hn₂, he₂⟩ := h₂
  obtain ⟨@⟨V₀, w₀⟩, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs
    (C := (liftSitePoint B S hS g t).fiber.Elements)
      ((liftSitePoint B S hS g t).fiber.elementsMk V₁ w₁)
      ((liftSitePoint B S hS g t).fiber.elementsMk V₂ w₂)
  exact ⟨V₀, w₀, _, add_mem_etaleSubmodule_obj B S hS g hg N _ _
      (N.map_mem a.hom.op hn₁) (N.map_mem b.hom.op hn₂),
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber_add M.val _ z _ _ s₁ s₂
      ((toPresheafFiber_pushLift_map B S hS g hg t a.hom a.map_val n₁).trans he₁)
      ((toPresheafFiber_pushLift_map B S hS g hg t b.hom b.map_val n₂).trans he₂)⟩

/-- The sum of two sections of the étale pullback `M|_Y` is their sum as sections of `M`. -/
theorem etaleModulePullback_add_eq {V : SmallEtale B S hS Y.1}
    (a b : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (op V)) :
    (a + b : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (op V)) =
      ((a : M.val.obj (op ((smallEtalePostcomp B S hS g hg).obj V))) + b) := rfl

/-- `AlgebraicGeometry.Space.toPresheafFiber_add_mem_etaleGermSet` for two sections of `M|_Y`
over a chart of `Y`, summed in `M|_Y`. -/
theorem toPresheafFiber_add_mem_etaleGermSet_of_pullback {Y' : AlgebraicSpaces B S hS}
    (g' : Y' ⟶ X) (hg' : IsEtale B S hS g'.hom)
    (Q : ((etaleModulePullback.{u, u} B S hS g' hg').obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (t' : GeometricPointLift B S hS g'.hom x) {V : SmallEtale B S hS Y.1}
    (w : (liftSitePoint B S hS g t).fiber.obj V)
    (a b : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (op V))
    (ha : (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber _ (pushLift B S hS g hg V t w)
      (etaleModuleSectionsPresheaf B S hS M) a ∈ etaleGermSet B S hS g' hg' Q t')
    (hb : (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber _ (pushLift B S hS g hg V t w)
      (etaleModuleSectionsPresheaf B S hS M) b ∈ etaleGermSet B S hS g' hg' Q t') :
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber _ (pushLift B S hS g hg V t w)
      (etaleModuleSectionsPresheaf B S hS M) (a + b) ∈ etaleGermSet B S hS g' hg' Q t' := by
  rw [etaleModulePullback_add_eq]
  exact toPresheafFiber_add_mem_etaleGermSet B S hS g' hg' Q t' (pushLift B S hS g hg V t w)
    a b ha hb

/-- **The germ set of a supremum.**  If the germ sets of `N₁` and `N₂` at a lift `t` are
contained in the germ set of a submodule `Q ⊆ M|_{Y'}` at a lift `t'`, then so is the germ set of
`N₁ ⊔ N₂`: its sections are locally sums of sections of `N₁` and `N₂`, and germ sets are closed
under sums. -/
theorem etaleGermSet_sup_subset {Y' : AlgebraicSpaces B S hS} (g' : Y' ⟶ X)
    (hg' : IsEtale B S hS g'.hom)
    (N₁ N₂ : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule)
    (Q : ((etaleModulePullback.{u, u} B S hS g' hg').obj M).Submodule)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (t' : GeometricPointLift B S hS g'.hom x)
    (h₁ : etaleGermSet B S hS g hg N₁ t ⊆ etaleGermSet B S hS g' hg' Q t')
    (h₂ : etaleGermSet B S hS g hg N₂ t ⊆ etaleGermSet B S hS g' hg' Q t') :
    etaleGermSet B S hS g hg (N₁ ⊔ N₂) t ⊆ etaleGermSet B S hS g' hg' Q t' := by
  rintro _ ⟨V, w, n, hn, rfl⟩
  obtain ⟨T, hT, hsum⟩ := Stacks.SheafOfModules.mem_sup_iff.1 hn
  obtain ⟨V₁, f, hf, w₁, rfl⟩ := (liftSitePoint B S hS g t).jointly_surjective T hT w
  obtain ⟨a, ha, b, hb, hab⟩ := hsum f hf
  have h := toPresheafFiber_add_mem_etaleGermSet_of_pullback B S hS g hg g' hg' Q t t' w₁ a b
    (h₁ (germ_mem_etaleGermSet B S hS g hg N₁ t V₁ w₁ a ha))
    (h₂ (germ_mem_etaleGermSet B S hS g hg N₂ t V₁ w₁ b hb))
  rw [← toPresheafFiber_pushLift_map B S hS g hg t f rfl n]
  exact hab ▸ h

end Sums

end AlgebraicGeometry.Space

end
