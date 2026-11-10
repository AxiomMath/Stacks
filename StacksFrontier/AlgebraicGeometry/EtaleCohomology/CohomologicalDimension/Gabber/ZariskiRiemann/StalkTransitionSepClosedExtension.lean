module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenterLimitGermDeathOfInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift

/-!
# Germ death along a refinement survives extension of the geometric point

Let `s : Spec Ω ⟶ S` be a geometric point of a scheme with `Ω` separably closed, and let
`t : Spec Ω' ⟶ Spec Ω` with `Ω'` separably closed. An étale scheme over `Spec Ω` is a disjoint
union of copies of `Spec Ω`, so composing with `t` is a bijection from the lifts of `s` to an
étale `S`-scheme `U` onto the lifts of `t ≫ s` to `U`. Hence `t` induces an isomorphism of the
points of the small étale site of `S` at `t ≫ s` and at `s`, and the stalk of an étale sheaf at
`s` maps isomorphically onto its stalk at `t ≫ s`, by sending the germ over `(U, w)` to the germ
over `(U, t ≫ w)`. This map commutes with the identification of the stalks of an inverse image
(Stacks 03Q1) and with every map of sheaves, so it intertwines the transition maps of stalks
along a refinement of proper models. That proves
`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionSepClosedExtension`, the third input of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centerLimitGermDeath_of_inputs`.

## Main definitions

* `AlgebraicGeometry.pointSmallEtaleExtension`: the morphism of points of the small étale site
  from `t ≫ s` to `s` given by precomposition with `t`.

## Main results

* `AlgebraicGeometry.etale_field_map_factors_of_isSepClosed`: a field-valued point of a scheme
  étale over the spectrum of a separably closed field factors through a section.
* `AlgebraicGeometry.geometric_lift_bijective_of_isSepClosed`: composing with `t` is a bijection
  on lifts through an étale morphism.
* `AlgebraicGeometry.pointSmallEtaleExtension_sheafFiber_injective`: the induced map of stalks is
  injective.
* `AlgebraicGeometry.smallEtaleStalkPullbackAbIso_inv_map_germ_extension`: the map of stalks
  commutes with the stalks of an inverse image followed by a map of sheaves, on germs.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.stalkTransitionSepClosedExtension`:
  `StalkTransitionSepClosedExtension` holds.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04HU](https://stacks.math.columbia.edu/tag/04HU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-- An étale scheme over the spectrum of a separably closed field `k` admits, through any
field-valued point of it, a section of its structure morphism over `Spec k` through which that
point factors: it is a disjoint union of spectra of finite separable extensions of `k`, each of
which is `k` itself. -/
theorem etale_field_map_factors_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of k)) (hf : Etale f)
    (L : Type u) [Field L] (q : Spec (.of L) ⟶ V) :
    ∃ l : Spec (.of k) ⟶ V,
      l ≫ f = 𝟙 _ ∧ q = (q ≫ f) ≫ l := by
  let : Etale f := hf
  obtain ⟨ι, K, hField, hAlgebra, hFinite, hSeparable, e, he⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k f).mp hf
  let Y : ι → Scheme.{u} := fun i => Spec (.of (K i))
  have hsplit : e.hom ≫ Sigma.desc (fun i =>
      Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
    simpa [Y] using he
  obtain ⟨i, t, ht⟩ := factor_through_coproduct_of_field Y L
    (q ≫ e.hom)
  let : Field (K i) := hField i
  let : Algebra k (K i) := hAlgebra i
  let : Module.Finite k (K i) := hFinite i
  let : Algebra.IsSeparable k (K i) := hSeparable i
  let b : Spec (.of (K i)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (K i)))
  let eK : k ≃+* K i :=
    RingEquiv.ofBijective (algebraMap k (K i)) (IsSepClosed.algebraMap_bijective k (K i))
  let eSpec : Spec (.of (K i)) ≅ Spec (.of k) :=
    Scheme.Spec.mapIso eK.toCommRingCatIso.op
  have hbIso : eSpec.hom = b := rfl
  have hsplitAt : q ≫ f = t ≫ b := by
    calc
      q ≫ f = q ≫ e.hom ≫ Sigma.desc
          (fun j => Spec.map (CommRingCat.ofHom (algebraMap k (K j)))) := by
            rw [hsplit]
      _ = t ≫ Sigma.ι Y i ≫ Sigma.desc
          (fun j => Spec.map (CommRingCat.ofHom (algebraMap k (K j)))) := by
            rw [← Category.assoc, ← ht, Category.assoc]
      _ = t ≫ b := by
        rw [Sigma.ι_comp_desc]
  let l : Spec (.of k) ⟶ V := eSpec.inv ≫ Sigma.ι Y i ≫ e.inv
  have hinv : e.inv ≫ f = Sigma.desc (fun j =>
      Spec.map (CommRingCat.ofHom (algebraMap k (K j)))) := by
    calc
      e.inv ≫ f = e.inv ≫ (e.hom ≫ Sigma.desc (fun j =>
          Spec.map (CommRingCat.ofHom (algebraMap k (K j))))) := by rw [hsplit]
      _ = _ := by simp
  have hl : l ≫ f = 𝟙 _ := by
    calc
      l ≫ f = eSpec.inv ≫ (Sigma.ι Y i ≫
          Sigma.desc (fun j => Spec.map (CommRingCat.ofHom
            (algebraMap k (K j))))) := by
              dsimp [l]
              rw [Category.assoc, Category.assoc, hinv]
      _ = eSpec.inv ≫ b := by
        rw [Sigma.ι_comp_desc]
      _ = 𝟙 _ := by rw [← hbIso, eSpec.inv_hom_id]
  have hle : l ≫ e.hom = eSpec.inv ≫ Sigma.ι Y i := by
    simp only [l, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hq : q = (q ≫ f) ≫ l := by
    apply (cancel_mono e.hom).1
    calc
      q ≫ e.hom = t ≫ Sigma.ι Y i := ht.symm
      _ = t ≫ (eSpec.hom ≫ eSpec.inv) ≫ Sigma.ι Y i := by
        rw [eSpec.hom_inv_id, Category.id_comp]
      _ = (t ≫ b) ≫ eSpec.inv ≫ Sigma.ι Y i := by
        rw [← hbIso]
        simp only [Category.assoc]
      _ = (q ≫ f) ≫ l ≫ e.hom := by rw [hle, hsplitAt]
  exact ⟨l, hl, hq⟩

/-- Composing with a morphism `f : Spec L ⟶ Spec k`, `k` separably closed, is a bijection from
the lifts of a geometric point `s : Spec k ⟶ X` through an étale morphism `v : V ⟶ X` to the lifts
of `f ≫ s`: the base change of `v` to `Spec k` is a disjoint union of copies of `Spec k`. -/
theorem geometric_lift_bijective_of_isSepClosed {k L : Type u} [Field k] [IsSepClosed k]
    [Field L] {X V : Scheme.{u}} (v : V ⟶ X) [Etale v] (s : Spec (.of k) ⟶ X)
    (f : Spec (.of L) ⟶ Spec (.of k)) :
    Function.Bijective (fun p : {p : Spec (.of k) ⟶ V // p ≫ v = s} =>
      (⟨f ≫ p.1, by rw [Category.assoc, p.2]⟩ :
        {q : Spec (.of L) ⟶ V // q ≫ v = f ≫ s})) := by
  let : Flat f := inferInstance
  let : Surjective f := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  let : Epi f := Flat.epi_of_flat_of_surjective f
  constructor
  · exact fun p q h => Subtype.ext ((cancel_epi f).mp (congrArg Subtype.val h))
  · intro q
    let g : pullback v s ⟶ Spec (.of k) := pullback.snd v s
    let q' : Spec (.of L) ⟶ pullback v s := pullback.lift q.1 f q.2
    obtain ⟨l, hl, hq⟩ := etale_field_map_factors_of_isSepClosed k g inferInstance L q'
    refine ⟨⟨l ≫ pullback.fst v s, ?_⟩, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hl, Category.id_comp]
    · apply Subtype.ext
      change f ≫ (l ≫ pullback.fst v s) = q.1
      calc
        _ = ((q' ≫ g) ≫ l) ≫ pullback.fst v s := by
          rw [show q' ≫ g = f from pullback.lift_snd _ _ _]
          exact (Category.assoc _ _ _).symm
        _ = q' ≫ pullback.fst v s := congrArg (· ≫ pullback.fst v s) hq.symm
        _ = q.1 := pullback.lift_fst _ _ _

section Extension

variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ Spec (.of Ω))

/-- **The morphism of points of the small étale site given by extending a geometric point**:
precomposition with `t : Spec Ω' ⟶ Spec Ω` maps the lifts of `s` to an étale `S`-scheme to the
lifts of `t ≫ s`. -/
def pointSmallEtaleExtension : pointSmallEtale (t ≫ s) ⟶ pointSmallEtale s :=
  ⟨Functor.whiskerLeft (Scheme.Etale.forget S)
    (coyoneda.map (Over.homMk t rfl : Over.mk (t ≫ s) ⟶ Over.mk s).op)⟩

/-- On a lift `w` of `s`, the morphism of points is precomposition with `t`. -/
theorem pointSmallEtaleExtension_hom_app_left (U : S.Etale)
    (w : (pointSmallEtale s).fiber.obj U) :
    ((pointSmallEtaleExtension s t).hom.app U w).left = t ≫ w.left :=
  rfl

/-- Precomposition with `t` is a bijection on lifts through each étale `S`-scheme. -/
theorem pointSmallEtaleExtension_hom_app_bijective (U : S.Etale) :
    Function.Bijective ((pointSmallEtaleExtension s t).hom.app U) := by
  have : Etale U.hom := U.prop
  have hb := geometric_lift_bijective_of_isSepClosed U.hom s t
  constructor
  · intro a b hab
    have h1 : t ≫ a.left = t ≫ b.left := congrArg CommaMorphism.left hab
    have h2 := hb.1 (a₁ := ⟨a.left, Over.w a⟩) (a₂ := ⟨b.left, Over.w b⟩) (Subtype.ext h1)
    exact Over.OverMorphism.ext (congrArg Subtype.val h2)
  · intro c
    obtain ⟨p, hp⟩ := hb.2 ⟨c.left, Over.w c⟩
    exact ⟨Over.homMk p.1 p.2, Over.OverMorphism.ext (congrArg Subtype.val hp)⟩

/-- The natural transformation of fiber functors underlying `pointSmallEtaleExtension s t` is an
isomorphism. -/
instance isIso_pointSmallEtaleExtension_hom : IsIso (pointSmallEtaleExtension s t).hom := by
  have : ∀ U, IsIso ((pointSmallEtaleExtension s t).hom.app U) := fun U =>
    (isIso_iff_bijective _).2 (pointSmallEtaleExtension_hom_app_bijective s t U)
  exact NatIso.isIso_of_isIso_app _

/-- **Extending a geometric point along a map of separably closed fields is an isomorphism of
points of the small étale site.** -/
instance isIso_pointSmallEtaleExtension : IsIso (pointSmallEtaleExtension s t) :=
  ⟨⟨⟨inv (pointSmallEtaleExtension s t).hom⟩, Point.hom_ext (by simp), Point.hom_ext (by simp)⟩⟩

/-- **The map of stalks induced by extending a geometric point is injective** (it is an
isomorphism, the points being isomorphic). -/
theorem pointSmallEtaleExtension_sheafFiber_injective
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) :
    Function.Injective ((pointSmallEtaleExtension s t).sheafFiber.app G) := by
  have e : (pointSmallEtaleExtension s t).sheafFiber.app G ≫
      (inv (pointSmallEtaleExtension s t)).sheafFiber.app G = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Point.Hom.sheafFiber_comp, IsIso.inv_hom_id,
      Point.Hom.sheafFiber_id, NatTrans.id_app]
  intro a b hab
  have h := congrArg ((inv (pointSmallEtaleExtension s t)).sheafFiber.app G) hab
  rwa [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, e, CategoryTheory.id_apply,
    CategoryTheory.id_apply] at h

/-- **The action of extending a geometric point on germs of presheaves**: the germ at `(U, w)`
goes to the germ at `(U, t ≫ w)`. -/
theorem toPresheafFiber_pointSmallEtaleExtension_presheafFiber
    (P : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) (U : S.Etale) (w : (pointSmallEtale s).fiber.obj U) :
    (pointSmallEtale s).toPresheafFiber U w P ≫
        (pointSmallEtaleExtension s t).presheafFiber.app P =
      (pointSmallEtale (t ≫ s)).toPresheafFiber U
        ((pointSmallEtaleExtension s t).hom.app U w) P := by
  simp only [Point.Hom.presheafFiber_app, Point.toPresheafFiber_presheafFiberDesc]

/-- **The action of extending a geometric point on germs**: the germ at `(U, w)` goes to the germ
at `(U, t ≫ w)`. -/
theorem toPresheafFiber_pointSmallEtaleExtension_sheafFiber
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (U : S.Etale)
    (w : (pointSmallEtale s).fiber.obj U) :
    (pointSmallEtale s).toPresheafFiber U w G.obj ≫
        (pointSmallEtaleExtension s t).sheafFiber.app G =
      (pointSmallEtale (t ≫ s)).toPresheafFiber U
        ((pointSmallEtaleExtension s t).hom.app U w) G.obj :=
  toPresheafFiber_pointSmallEtaleExtension_presheafFiber s t G.obj U w

/-- On a lift `w` of `s`, the morphism of points is precomposition with `t`, as a morphism of
`S`-schemes. -/
theorem pointSmallEtaleExtension_hom_app_apply (U : S.Etale)
    (w : (pointSmallEtale s).fiber.obj U) :
    (pointSmallEtaleExtension s t).hom.app U w =
      (Over.homMk t rfl : Over.mk (t ≫ s) ⟶ Over.mk s) ≫ w :=
  rfl

/-- The bijection between lifts of `s` to a base change and lifts of `s ≫ π` is the adjunction
`Over.map π ⊣ Over.pullback π`. -/
theorem pointSmallEtaleBaseChangeFiberIso_hom_app_apply {Y : Scheme.{u}} (π : S ⟶ Y)
    (U : Y.Etale) (w : (pointSmallEtale (s ≫ π)).fiber.obj U) :
    (pointSmallEtaleBaseChangeFiberIso π s).hom.app U w =
      ((Over.mapPullbackAdj π).homEquiv (Over.mk s) ((Etale.forget Y).obj U) w :
        Over.mk s ⟶ (Etale.forget S).obj ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj U)) :=
  rfl

/-- A lift `wb` of `(t ≫ s) ≫ π` with `wb = t ≫ w` is the image of `w` under `Over.map π` of the
morphism `t : Over.mk (t ≫ s) ⟶ Over.mk s`. -/
theorem eq_map_homMk_comp_of_left_eq {Y : Scheme.{u}} (π : S ⟶ Y)
    (U : Y.Etale) (w : (pointSmallEtale (s ≫ π)).fiber.obj U)
    (wb : (pointSmallEtale ((t ≫ s) ≫ π)).fiber.obj U) (hw : wb.left = t ≫ w.left) :
    wb = ((Over.map π).map (Over.homMk t rfl : Over.mk (t ≫ s) ⟶ Over.mk s) ≫ w :
      Over.mk ((t ≫ s) ≫ π) ⟶ (Etale.forget Y).obj U) :=
  Over.OverMorphism.ext hw

/-- **Lifts to a base change are compatible with extending the geometric point**: if `wb` is the
lift `t ≫ w` of `(t ≫ s) ≫ π` to an étale `Y`-scheme `U`, the corresponding lift of `t ≫ s` to
`U ×_Y S` is `t` followed by the lift of `s` corresponding to `w`. -/
theorem pointSmallEtaleBaseChangeFiberIso_hom_app_extension {Y : Scheme.{u}} (π : S ⟶ Y)
    (U : Y.Etale) (w : (pointSmallEtale (s ≫ π)).fiber.obj U)
    (wb : (pointSmallEtale ((t ≫ s) ≫ π)).fiber.obj U) (hw : wb.left = t ≫ w.left) :
    (pointSmallEtaleBaseChangeFiberIso π (t ≫ s)).hom.app U wb =
      (pointSmallEtaleExtension s t).hom.app ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj U)
        ((pointSmallEtaleBaseChangeFiberIso π s).hom.app U w) := by
  rw [pointSmallEtaleExtension_hom_app_apply, pointSmallEtaleBaseChangeFiberIso_hom_app_apply,
    pointSmallEtaleBaseChangeFiberIso_hom_app_apply, eq_map_homMk_comp_of_left_eq s t π U w wb hw]
  exact (Over.mapPullbackAdj π).homEquiv_naturality_left
    (Over.homMk t rfl : Over.mk (t ≫ s) ⟶ Over.mk s) w

/-- On germs, the stalk comparison for an inverse image is the unit of the adjunction followed by
the germ at the corresponding lift to the base change. -/
private theorem smallEtaleStalkPullbackAbIso_inv_app_germ {S Y : Scheme.{u}} {Ω₁ : Type u}
    [Field Ω₁] [IsSepClosed Ω₁] (π : S ⟶ Y) (s₁ : Spec (.of Ω₁) ⟶ S)
    (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (U : Y.Etale)
    (w : (pointSmallEtale (s₁ ≫ π)).fiber.obj U) (x : G.obj.obj (op U)) :
    (smallEtaleStalkPullbackAbIso π s₁).inv.app G
        ((pointSmallEtale (s₁ ≫ π)).toPresheafFiber U w G.obj x) =
      (pointSmallEtale s₁).toPresheafFiber ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj U)
        ((pointSmallEtaleComapFiberIso π s₁).hom.app U w) ((smallEtalePullbackAb π).obj G).obj
        (((smallEtaleAdjunctionAb π).unit.app G).hom.app (op U) x) :=
  ConcreteCategory.congr_hom (toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv π s₁ G U w) x

/-- **The stalks of an inverse image followed by a map of sheaves commute with extending the
geometric point, on germs.** For `π : S ⟶ Y`, a map `β : π⁻¹ G ⟶ G'`, and the germ of a section
`x` of `G` over an étale neighbourhood `(U, w)` of `s ≫ π`: sending the image of the germ in
`G'_s` to `G'_{t ≫ s}` gives the image of the germ of `x` at `(U, t ≫ w)`. -/
theorem smallEtaleStalkPullbackAbIso_inv_map_germ_extension {Y : Scheme.{u}} (π : S ⟶ Y)
    {G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {G' : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (β : (smallEtalePullbackAb π).obj G ⟶ G') (U : Y.Etale)
    (w : (pointSmallEtale (s ≫ π)).fiber.obj U)
    (wb : (pointSmallEtale ((t ≫ s) ≫ π)).fiber.obj U) (hw : wb.left = t ≫ w.left)
    (x : G.obj.obj (op U)) :
    (pointSmallEtaleExtension s t).sheafFiber.app G'
        (((smallEtaleStalkPullbackAbIso π s).inv.app G ≫
            (smallEtaleStalkAb s).map β)
          ((pointSmallEtale (s ≫ π)).toPresheafFiber U w G.obj x)) =
      ((smallEtaleStalkPullbackAbIso π (t ≫ s)).inv.app G ≫
          (smallEtaleStalkAb (t ≫ s)).map β)
        ((pointSmallEtale ((t ≫ s) ≫ π)).toPresheafFiber U wb G.obj x) := by
  have hfib : (pointSmallEtaleComapFiberIso π (t ≫ s)).hom.app U wb =
      (pointSmallEtaleExtension s t).hom.app ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj U)
        ((pointSmallEtaleComapFiberIso π s).hom.app U w) :=
    pointSmallEtaleBaseChangeFiberIso_hom_app_extension s t π U w wb hw
  have hb : ∀ y, (pointSmallEtaleExtension s t).sheafFiber.app G' ((smallEtaleStalkAb s).map β y) =
      (smallEtaleStalkAb (t ≫ s)).map β
        ((pointSmallEtaleExtension s t).sheafFiber.app ((smallEtalePullbackAb π).obj G) y) :=
    fun y => ConcreteCategory.congr_hom ((pointSmallEtaleExtension s t).sheafFiber.naturality β) y
  have hc := ConcreteCategory.congr_hom (toPresheafFiber_pointSmallEtaleExtension_sheafFiber s t
    ((smallEtalePullbackAb π).obj G) ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj U)
    ((pointSmallEtaleComapFiberIso π s).hom.app U w))
    (((smallEtaleAdjunctionAb π).unit.app G).hom.app (op U) x)
  change (pointSmallEtaleExtension s t).sheafFiber.app G' ((smallEtaleStalkAb s).map β
      ((smallEtaleStalkPullbackAbIso π s).inv.app G
        ((pointSmallEtale (s ≫ π)).toPresheafFiber U w G.obj x))) =
    (smallEtaleStalkAb (t ≫ s)).map β ((smallEtaleStalkPullbackAbIso π (t ≫ s)).inv.app G
      ((pointSmallEtale ((t ≫ s) ≫ π)).toPresheafFiber U wb G.obj x))
  rw [smallEtaleStalkPullbackAbIso_inv_app_germ π s G U w x,
    smallEtaleStalkPullbackAbIso_inv_app_germ π (t ≫ s) G U wb x]
  refine (hb _).trans ?_
  rw [hfib]
  exact congrArg (fun y => (smallEtaleStalkAb (t ≫ s)).map β y) hc

end Extension

namespace Scheme.ZariskiRiemann

/-- **Germ death along a refinement survives extension of the geometric point**
(`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionSepClosedExtension`). After identifying
`s₀ = s ≫ π`, `sb = t ≫ s` and `sb₀ = sb ≫ π`, the map of stalks
`G'_s ⟶ G'_{t ≫ s}` induced by `t` is injective
(`AlgebraicGeometry.pointSmallEtaleExtension_sheafFiber_injective`) and sends the image of the
germ of `x` at `(U, w)` under the transition map at `s` to its image at `(U, t ≫ w)` under the
transition map at `t ≫ s`
(`AlgebraicGeometry.smallEtaleStalkPullbackAbIso_inv_map_germ_extension`). -/
theorem stalkTransitionSepClosedExtension : StalkTransitionSepClosedExtension.{u} := by
  intro B _ _ F q M' M φ Ω _ _ s₀ s h Ω' _ _ t sb₀ sb hb₀ _ h₂ U w wb hw x hx
  subst h hb₀ h₂
  simp only [eqToHom_refl, Category.id_comp] at hx ⊢
  apply pointSmallEtaleExtension_sheafFiber_injective s t
  rw [map_zero]
  exact (smallEtaleStalkPullbackAbIso_inv_map_germ_extension s t φ.π _ U w wb hw x).trans hx

end Scheme.ZariskiRiemann

end AlgebraicGeometry

end
