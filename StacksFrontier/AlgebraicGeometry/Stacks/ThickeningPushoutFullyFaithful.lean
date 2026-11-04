module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineSections

/-!
# Restriction to a thickening-and-affine pushout is fully faithful on an algebraic stack

Let `X ⟶ X'` be a thickening and `X ⟶ Y` an affine morphism of schemes over `S`, with pushout
`Y' = Y ⨿_X X'` in schemes over `S` (Stacks 07RT). For a category fibred in groupoids `𝒳` over the
big fppf site of `S` whose isomorphism presheaves are algebraic spaces — in particular for every
algebraic stack — the comparison functor

`𝒳_{Y'} ⥤ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}`

of `Deformation.Artin.fiberSquareComparison` is full and faithful. This is the first paragraph of
the proof of Stacks 07WN: a morphism `y₁ ⟶ y₂` of the fibre over `Y'` is a section over `Y'` of
the algebraic space `Isom(y₁, y₂)` (Stacks 045G), and `Y'` is a pushout in algebraic spaces as well
as in schemes (Stacks 07SY), so a compatible pair of sections over `Y` and `X'` glues uniquely.

## Main results

* `existsUnique_section_over`: sections glue uniquely along the pushout square, the
  functor-of-points reading of Stacks 07SY
  (`AlgebraicGeometry.Space.existsUnique_section_of_isThickening_of_isAffineHom`), for a presheaf
  on `Over U` which is an algebraic space over `U` through the iterated-slice equivalence, the
  shape in which condition (2) of Stacks 045G presents `Isom(y₁, y₂)`.
* `fiberSquareComparison_full_and_faithful`: the comparison functor is full and faithful when the
  isomorphism presheaves are algebraic spaces.
* `fiberSquareComparison_full_and_faithful_of_isAlgebraicStack`: the same for an algebraic stack,
  at the hypotheses of Stacks 07WN.

## Implementation notes

The essential surjectivity half of Stacks 07WN is not proved here, so no declaration in this file
carries `@[stacks 07WN]`. The source obtains it by gluing the two smooth algebraic spaces
`Y ×_𝒵 W` and `X' ×_𝒵 W` along a pushout of algebraic spaces (Stacks 07VX and 07W3), which in turn
needs that an étale lift of an affine scheme across a thickening of algebraic spaces is a scheme
(Stacks 05ZR, through Stacks 07VT).

A morphism `φ : y₁ ⟶ y₂` of the fibre over `Y'` is read as the section
`AlgebraicGeometry.Stack.ThickeningPushout.idSection` of `Mor(y₁, y₂)` over the identity of `Y'`,
and its restriction along a morphism `k` into `Y'` is the base change of `φ` along `k` for the
canonical choice of pullbacks (`morRestrict_idSection`). The compatibility condition of a morphism
of the two-fibre product is read, through the structure isomorphism of the comparison functor, as
the equality of the two restrictions to the corner `X` (`morRestrict_snd_eq_morRestrict_fst`);
every equation between morphisms of a fibre is checked after composing with a cartesian morphism.

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 07SY](https://stacks.math.columbia.edu/tag/07SY)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack.ThickeningPushout

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Over an object `U` of the big fppf site of `S`, a presheaf `H` on `Over U` which, read
through the iterated-slice equivalence, is an algebraic space over `U` (up to universe lifts),
has the same gluing property along thickening-and-affine pushout squares of `Over U`. -/
theorem existsUnique_section_over {U : BigFppfOver B S hS} (H : (Over U)ᵒᵖ ⥤ Type v)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (e : F ⋙ uliftFunctor.{v, u} ≅ ((Over.iteratedSliceBackward U).op ⋙ H) ⋙ uliftFunctor.{u, v})
    {X X' Y Y' : Over U} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i.left))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f.left)]
    (hPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i.left)
      ((BigFppfOver.toScheme B S hS).map f.left)
      ((BigFppfOver.toScheme B S hS).map a.left)
      ((BigFppfOver.toScheme B S hS).map b.left))
    (sX' : H.obj (op X')) (sY : H.obj (op Y))
    (hcompat : H.map i.op sX' = H.map f.op sY) :
    ∃! s : H.obj (op Y'), H.map a.op s = sX' ∧ H.map b.op s = sY := by
  let Φ := Over.iteratedSliceForward U
  let unit : ∀ Z : Over U, Z ≅ (Over.iteratedSliceBackward U).obj (Φ.obj Z) := fun Z =>
    (Over.iteratedSliceEquiv U).unitIso.app Z
  let θ : ∀ Z : Over U, F.obj (op (Φ.obj Z)) ≃ H.obj (op Z) := fun Z =>
    Equiv.ulift.symm.trans ((e.app (op (Φ.obj Z))).toEquiv.trans
      (Equiv.ulift.trans (H.mapIso (unit Z).op).toEquiv))
  have hθ : ∀ {Z₁ Z₂ : Over U} (g : Z₁ ⟶ Z₂) (s : F.obj (op (Φ.obj Z₂))),
      θ Z₁ (F.map (Φ.map g).op s) = H.map g.op (θ Z₂ s) := by
    intro Z₁ Z₂ g s
    have hn := NatTrans.naturality_apply e.hom (Φ.map g).op
      (show (F ⋙ uliftFunctor.{v, u}).obj (op (Φ.obj Z₂)) from ULift.up s)
    have hu : g ≫ (unit Z₂).hom = (unit Z₁).hom ≫
        (Over.iteratedSliceBackward U).map (Φ.map g) :=
      ((Over.iteratedSliceEquiv U).unitIso.hom.naturality g).symm
    show H.map (unit Z₁).hom.op (e.hom.app (op (Φ.obj Z₁))
        ((F ⋙ uliftFunctor.{v, u}).map (Φ.map g).op (ULift.up s))).down
      = H.map g.op (H.map (unit Z₂).hom.op (e.hom.app (op (Φ.obj Z₂)) (ULift.up s)).down)
    refine (congrArg (fun t => H.map (unit Z₁).hom.op (ULift.down t)) hn).trans ?_
    show H.map (unit Z₁).hom.op (H.map ((Over.iteratedSliceBackward U).map (Φ.map g)).op
        (e.hom.app (op (Φ.obj Z₂)) (ULift.up s)).down)
      = H.map g.op (H.map (unit Z₂).hom.op (e.hom.app (op (Φ.obj Z₂)) (ULift.up s)).down)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hu]
  have : IsAffineHom ((BigFppfOver.toScheme B U.left.1 U.left.2).map (Φ.map f)) :=
    ‹IsAffineHom ((BigFppfOver.toScheme B S hS).map f.left)›
  have hcompat' : F.map (Φ.map i).op ((θ X').symm sX') = F.map (Φ.map f).op ((θ Y).symm sY) := by
    apply (θ X).injective
    rw [hθ, hθ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hcompat]
  obtain ⟨s₀, ⟨hs₁, hs₂⟩, huniq⟩ :=
    Space.existsUnique_section_of_isThickening_of_isAffineHom B U.left.1 U.left.2
      (Φ.map i) (Φ.map f) (Φ.map a) (Φ.map b) hi hPushout F hF _ _ hcompat'
  refine ⟨θ Y' s₀, ⟨?_, ?_⟩, ?_⟩
  · rw [← hθ, hs₁, Equiv.apply_symm_apply]
  · rw [← hθ, hs₂, Equiv.apply_symm_apply]
  · rintro t ⟨ht₁, ht₂⟩
    have := huniq ((θ Y').symm t) ⟨(θ X').injective (by rw [hθ, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, ht₁]), (θ Y).injective (by rw [hθ, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, ht₂])⟩
    rw [← this, Equiv.apply_symm_apply]

section FiberComputations

open Functor

variable {𝒮 : Type*} [Category 𝒮] {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ 𝒮) [p.IsFibered]

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

/-- The value of the restriction map of `Isom(x, y)`. -/
lemma isomPresheaf_map_val {U : 𝒮} (x y : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (s : (p.isomPresheaf x y).obj (op g₂)) :
    ((p.isomPresheaf x y).map h.op s).1 = morRestrict p x y h s.1 :=
  rfl

/-- A morphism `φ : x ⟶ y` of the fibre over `U`, read as a section of `Mor(x, y)` over the
identity of `U`. -/
noncomputable def idSection {U : 𝒮} {x y : p.Fiber U} (φ : x ⟶ y) :
    pullbackFiber p x (𝟙 U) ⟶ pullbackFiber p y (𝟙 U) :=
  (pullbackFiberIdIso x).hom ≫ φ ≫ (pullbackFiberIdIso y).inv

/-- The image in `𝒳` of the canonical isomorphism from the pullback of `x` along the identity of
`U` to `x` is the chosen lift of the identity. -/
lemma fiberInclusion_map_pullbackFiberIdIso_hom {U : 𝒮} (x : p.Fiber U) :
    Fiber.fiberInclusion.map (pullbackFiberIdIso x).hom = IsPreFibered.pullbackMap x.2 (𝟙 U) := by
  rw [← chosenPullbacks_objIdIso]
  exact (chosenPullbacks p).fiberInclusion_map_objIdIso_hom x

/-- The section of `Mor(x, y)` over the identity attached to `φ`, followed by the chosen
lift of the identity, is the chosen lift of the identity followed by `φ`. -/
lemma idSection_fac {U : 𝒮} {x y : p.Fiber U} (φ : x ⟶ y) :
    Fiber.fiberInclusion.map (idSection p φ) ≫ IsPreFibered.pullbackMap y.2 (𝟙 U) =
      IsPreFibered.pullbackMap x.2 (𝟙 U) ≫ Fiber.fiberInclusion.map φ := by
  have h2 : Fiber.fiberInclusion.map (pullbackFiberIdIso y).inv ≫
      IsPreFibered.pullbackMap y.2 (𝟙 U) = 𝟙 _ := by
    rw [← fiberInclusion_map_pullbackFiberIdIso_hom, ← CategoryTheory.Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  dsimp only [idSection]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, h2, Category.comp_id, fiberInclusion_map_pullbackFiberIdIso_hom]

/-- Restricting the section of `Mor(x, y)` over the identity attached to `φ` along `k : V ⟶ U`
gives the base change of `φ` along `k`. -/
lemma morRestrict_idSection {U V : 𝒮} {x y : p.Fiber U} (φ : x ⟶ y) (k : V ⟶ U) :
    morRestrict p x y (Over.homMk k (Category.comp_id k) : Over.mk k ⟶ Over.mk (𝟙 U))
      (idSection p φ) = (chosenPullbacks p).homMap k φ := by
  refine (morRestrict_uniq p x y _ _ _ ?_).symm
  have h1 : Fiber.fiberInclusion.map ((chosenPullbacks p).homMap k φ) ≫
      IsPreFibered.pullbackMap y.2 k = IsPreFibered.pullbackMap x.2 k ≫
        Fiber.fiberInclusion.map φ := (chosenPullbacks p).homMap_fac k φ
  have h3 : pullbackFiberMap p x
      (Over.homMk k (Category.comp_id k) : Over.mk k ⟶ Over.mk (𝟙 U)) ≫
        IsPreFibered.pullbackMap x.2 (𝟙 U) = IsPreFibered.pullbackMap x.2 k :=
    pullbackFiberMap_fac p x _
  refine h1.trans ?_
  rw [← h3, Category.assoc, ← idSection_fac]
  rfl

/-- A morphism of the fibre is determined by its section of `Mor(x, y)` over the identity. -/
lemma idSection_injective {U : 𝒮} {x y : p.Fiber U} {φ ψ : x ⟶ y}
    (h : idSection p φ = idSection p ψ) : φ = ψ := by
  simpa [idSection] using
    congrArg (fun t => (pullbackFiberIdIso x).inv ≫ t ≫ (pullbackFiberIdIso y).hom) h

/-- Every section of `Mor(x, y)` over the identity comes from a morphism of the fibre. -/
lemma idSection_surjective {U : 𝒮} {x y : p.Fiber U}
    (m : pullbackFiber p x (𝟙 U) ⟶ pullbackFiber p y (𝟙 U)) :
    idSection p ((pullbackFiberIdIso x).inv ≫ m ≫ (pullbackFiberIdIso y).hom) = m := by
  simp [idSection]

/-- The transport of the chosen pullback along an equality of base morphisms. -/
lemma fiberInclusion_map_eqToHom_app_comp {U V : 𝒮} {k₁ k₂ : V ⟶ U} (h : k₁ = k₂)
    (y : p.Fiber U) :
    Fiber.fiberInclusion.map
        ((eqToHom (congrArg (chosenPullbacks p).pullbackFunctor h)).app y) ≫
      (chosenPullbacks p).map k₂ y = (chosenPullbacks p).map k₁ y := by
  subst h
  simp only [eqToHom_refl, NatTrans.id_app]
  exact Category.id_comp _

/-- The restriction map of the chosen pullbacks along `homMk g` is any `θ` into the pullback
along `g` which is compatible with the chosen lifts, followed by the chosen lift of `g`. -/
private lemma pullbackFiberMap_homMk_eq {U V W : 𝒮} (x : p.Fiber U) {g : W ⟶ V} {k : V ⟶ U}
    {m : W ⟶ U} (hm : g ≫ k = m)
    (θ : (chosenPullbacks p).obj m x ⟶ (chosenPullbacks p).obj g ((chosenPullbacks p).obj k x))
    (hθ : Fiber.fiberInclusion.map θ ≫ (chosenPullbacks p).map g ((chosenPullbacks p).obj k x) ≫
      (chosenPullbacks p).map k x = (chosenPullbacks p).map m x) :
    pullbackFiberMap p x (Over.homMk g hm : Over.mk m ⟶ Over.mk k) =
      Fiber.fiberInclusion.map θ ≫ (chosenPullbacks p).map g ((chosenPullbacks p).obj k x) := by
  have h0 : p.IsHomLift (𝟙 W ≫ g) (Fiber.fiberInclusion.map θ ≫
      (chosenPullbacks p).map g ((chosenPullbacks p).obj k x)) := by
    have : p.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map θ) := θ.2
    infer_instance
  rw [Category.id_comp] at h0
  have h1 : p.IsHomLift g (pullbackFiberMap p x (Over.homMk g hm : Over.mk m ⟶ Over.mk k)) :=
    pullbackFiberMap_isHomLift p x (Over.homMk g hm : Over.mk m ⟶ Over.mk k)
  have h2 : p.IsStronglyCartesian k (IsPreFibered.pullbackMap x.2 k) := inferInstance
  refine @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _ k (IsPreFibered.pullbackMap x.2 k) h2 _ _ g
    _ _ h1 h0 ?_
  exact (pullbackFiberMap_fac p x _).trans (hθ.symm.trans (Category.assoc _ _ _).symm)

/-- The restriction map of the chosen pullbacks along `homMk g`, for a composite `g ≫ k`. -/
lemma pullbackFiberMap_homMk_comp {U V W : 𝒮} (x : p.Fiber U) (g : W ⟶ V) (k : V ⟶ U) :
    pullbackFiberMap p x (Over.homMk g rfl : Over.mk (g ≫ k) ⟶ Over.mk k) =
      Fiber.fiberInclusion.map ((chosenPullbacks p).objCompIso g k x).hom ≫
        (chosenPullbacks p).map g ((chosenPullbacks p).obj k x) :=
  pullbackFiberMap_homMk_eq p x rfl _ ((chosenPullbacks p).objCompIso_hom_fac g k x)

variable {X X' Y Y' : 𝒮} (f : X ⟶ Y) (i : X ⟶ X') (b : Y ⟶ Y') (a : X' ⟶ Y')
  (w : f ≫ b = i ≫ a)

/-- The structure isomorphism of the comparison functor, followed by the chosen lifts along
`i` and `a`, is the composite of the chosen lifts along `f` and `b`. -/
lemma fiberSquareComparison_iso_fac (y : p.Fiber Y') :
    Fiber.fiberInclusion.map
        ((Deformation.Artin.fiberSquareComparison p (chosenPullbacks p) f i b a w).obj y).iso.hom ≫
      (chosenPullbacks p).map i ((chosenPullbacks p).obj a y) ≫ (chosenPullbacks p).map a y =
    (chosenPullbacks p).map f ((chosenPullbacks p).obj b y) ≫ (chosenPullbacks p).map b y := by
  let c := chosenPullbacks p
  let A := (c.objCompIso f b y).inv
  let E : c.obj (f ≫ b) y ⟶ c.obj (i ≫ a) y := (eqToHom (congrArg c.pullbackFunctor w)).app y
  let C := (c.objCompIso i a y).hom
  have e1 : Fiber.fiberInclusion.map C ≫ c.map i (c.obj a y) ≫ c.map a y = c.map (i ≫ a) y :=
    c.objCompIso_hom_fac i a y
  have e2 : Fiber.fiberInclusion.map (c.objCompIso f b y).hom ≫ c.map f (c.obj b y) ≫
      c.map b y = c.map (f ≫ b) y := c.objCompIso_hom_fac f b y
  have e3 : Fiber.fiberInclusion.map E ≫ c.map (i ≫ a) y = c.map (f ≫ b) y :=
    fiberInclusion_map_eqToHom_app_comp p w y
  have hmc : Fiber.fiberInclusion.map (A ≫ E ≫ C) = Fiber.fiberInclusion.map A ≫
      Fiber.fiberInclusion.map E ≫ Fiber.fiberInclusion.map C :=
    (Fiber.fiberInclusion.map_comp A (E ≫ C)).trans
      (congrArg (Fiber.fiberInclusion.map A ≫ ·) (Fiber.fiberInclusion.map_comp E C))
  show Fiber.fiberInclusion.map (A ≫ E ≫ C) ≫ c.map i (c.obj a y) ≫ c.map a y =
    c.map f (c.obj b y) ≫ c.map b y
  calc Fiber.fiberInclusion.map (A ≫ E ≫ C) ≫ c.map i (c.obj a y) ≫ c.map a y
      = Fiber.fiberInclusion.map A ≫ Fiber.fiberInclusion.map E ≫
          (Fiber.fiberInclusion.map C ≫ c.map i (c.obj a y) ≫ c.map a y) := by
        rw [hmc, Category.assoc, Category.assoc]
    _ = Fiber.fiberInclusion.map A ≫ (Fiber.fiberInclusion.map E ≫ c.map (i ≫ a) y) := by
        rw [e1]
    _ = Fiber.fiberInclusion.map A ≫ (Fiber.fiberInclusion.map (c.objCompIso f b y).hom ≫
          c.map f (c.obj b y) ≫ c.map b y) := by rw [e3, e2]
    _ = c.map f (c.obj b y) ≫ c.map b y := by
        rw [← Category.assoc, ← Fiber.fiberInclusion.map_comp, Iso.inv_hom_id,
          CategoryTheory.Functor.map_id, Category.id_comp]

/-- The two components of a morphism of the two-fibre product of fibres have the same
restriction to the corner `X`, read as sections of `Mor`. -/
lemma morRestrict_snd_eq_morRestrict_fst {y₁ y₂ : p.Fiber Y'}
    (α : (chosenPullbacks p).obj b y₁ ⟶ (chosenPullbacks p).obj b y₂)
    (β : (chosenPullbacks p).obj a y₁ ⟶ (chosenPullbacks p).obj a y₂)
    (hαβ : (chosenPullbacks p).homMap f α ≫
        ((Deformation.Artin.fiberSquareComparison p (chosenPullbacks p) f i b a w).obj y₂).iso.hom =
      ((Deformation.Artin.fiberSquareComparison p (chosenPullbacks p) f i b a w).obj y₁).iso.hom ≫
        (chosenPullbacks p).homMap i β) :
    morRestrict p y₁ y₂ (Over.homMk i rfl : Over.mk (i ≫ a) ⟶ Over.mk a) β =
      morRestrict p y₁ y₂ (Over.homMk f w : Over.mk (i ≫ a) ⟶ Over.mk b) α := by
  let c := chosenPullbacks p
  let F := Deformation.Artin.fiberSquareComparison p c f i b a w
  let ι : ∀ {T : 𝒮}, p.Fiber T ⥤ 𝒳 := fun {T} => Fiber.fiberInclusion
  have hcart : p.IsCartesian (i ≫ a) (IsPreFibered.pullbackMap y₂.2 (i ≫ a)) := inferInstance
  refine fiber_hom_ext_of_cartesian (i ≫ a) (IsPreFibered.pullbackMap y₂.2 (i ≫ a)) hcart _ _ ?_
  refine (morRestrict_fac p y₁ y₂ (Over.homMk i rfl : Over.mk (i ≫ a) ⟶ Over.mk a) β).trans
    (Eq.trans ?_ (morRestrict_fac p y₁ y₂ (Over.homMk f w : Over.mk (i ≫ a) ⟶ Over.mk b) α).symm)
  have hA : pullbackFiberMap p y₁ (Over.homMk i rfl : Over.mk (i ≫ a) ⟶ Over.mk a) =
      ι.map (c.objCompIso i a y₁).hom ≫ c.map i (c.obj a y₁) :=
    pullbackFiberMap_homMk_comp p y₁ i a
  let Q : ∀ y : p.Fiber Y', c.obj f (c.obj b y) ≅ c.obj i (c.obj a y) := fun y => (F.obj y).iso
  have eQ : ∀ y : p.Fiber Y', ι.map (Q y).hom ≫ c.map i (c.obj a y) ≫ c.map a y =
      c.map f (c.obj b y) ≫ c.map b y := fun y => fiberSquareComparison_iso_fac p f i b a w y
  have eQ' : ∀ y : p.Fiber Y', ι.map (Q y).inv ≫ c.map f (c.obj b y) ≫ c.map b y =
      c.map i (c.obj a y) ≫ c.map a y := fun y => by
    rw [← eQ y, ← Category.assoc, ← ι.map_comp, Iso.inv_hom_id, ι.map_id, Category.id_comp]
  let θ : c.obj (i ≫ a) y₁ ⟶ c.obj f (c.obj b y₁) := (c.objCompIso i a y₁).hom ≫ (Q y₁).inv
  have hB : pullbackFiberMap p y₁ (Over.homMk f w : Over.mk (i ≫ a) ⟶ Over.mk b) =
      ι.map θ ≫ c.map f (c.obj b y₁) := by
    refine pullbackFiberMap_homMk_eq p y₁ w θ ?_
    rw [ι.map_comp, Category.assoc, eQ' y₁]
    exact c.objCompIso_hom_fac i a y₁
  rw [hA, hB]
  have hw : ι.map (c.homMap f α) ≫ ι.map (Q y₂).hom =
      ι.map (Q y₁).hom ≫ ι.map (c.homMap i β) := by
    rw [← ι.map_comp, ← ι.map_comp]
    exact congrArg ι.map hαβ
  have hfac₁ : ι.map (c.homMap f α) ≫ c.map f (c.obj b y₂) =
      c.map f (c.obj b y₁) ≫ ι.map α := c.homMap_fac f α
  have hfac₂ : ι.map (c.homMap i β) ≫ c.map i (c.obj a y₂) =
      c.map i (c.obj a y₁) ≫ ι.map β := c.homMap_fac i β
  show (ι.map (c.objCompIso i a y₁).hom ≫ c.map i (c.obj a y₁)) ≫ ι.map β ≫
      IsPreFibered.pullbackMap y₂.2 a =
    (ι.map θ ≫ c.map f (c.obj b y₁)) ≫ ι.map α ≫ IsPreFibered.pullbackMap y₂.2 b
  calc (ι.map (c.objCompIso i a y₁).hom ≫ c.map i (c.obj a y₁)) ≫ ι.map β ≫
        IsPreFibered.pullbackMap y₂.2 a
      = ι.map (c.objCompIso i a y₁).hom ≫ ι.map (c.homMap i β) ≫ c.map i (c.obj a y₂) ≫
          c.map a y₂ := by
        rw [← Category.assoc (ι.map (c.homMap i β)), hfac₂]
        simp only [Category.assoc]
        rfl
    _ = ι.map θ ≫ ι.map (Q y₁).hom ≫ ι.map (c.homMap i β) ≫ c.map i (c.obj a y₂) ≫
          c.map a y₂ := by
        rw [← Category.assoc (ι.map θ), ← ι.map_comp]
        simp only [θ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = ι.map θ ≫ ι.map (c.homMap f α) ≫ (ι.map (Q y₂).hom ≫ c.map i (c.obj a y₂) ≫
          c.map a y₂) := by
        rw [← Category.assoc (ι.map (Q y₁).hom), ← hw]
        simp only [Category.assoc]
    _ = (ι.map θ ≫ c.map f (c.obj b y₁)) ≫ ι.map α ≫ IsPreFibered.pullbackMap y₂.2 b := by
        rw [eQ y₂, ← Category.assoc (ι.map (c.homMap f α)), hfac₁]
        simp only [Category.assoc]
        rfl

end FiberComputations

open Functor in
/-- **Restriction to a thickening-and-affine pushout is fully faithful.** Let `X ⟶ X'` be a
thickening and `X ⟶ Y` an affine morphism of schemes over `S` with pushout `Y'`, and let `𝒳` be
a category fibred in groupoids over the big fppf site of `S` whose isomorphism presheaves are
algebraic spaces (condition (2) of Stacks 045G, which holds for every algebraic stack). Then the
comparison functor from the fibre over `Y'` to the two-fibre product of the fibres over `Y` and
`X'` over the fibre over `X` is full and faithful.

This is the first half of the proof of Stacks 07WN: a morphism over `Y'` is a section of the
algebraic space `Isom` over `Y'`, and sections of an algebraic space glue along the pushout by
Stacks 07SY. -/
theorem fiberSquareComparison_full_and_faithful
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒳)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    (Deformation.Artin.fiberSquareComparison 𝒳.val.p (𝒳.val.p.chosenPullbacks)
      f i b a w.symm).Full ∧
    (Deformation.Artin.fiberSquareComparison 𝒳.val.p (𝒳.val.p.chosenPullbacks)
      f i b a w.symm).Faithful := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  set p := 𝒳.val.p
  set c := p.chosenPullbacks
  have hgrp := 𝒳.isFiberedInGroupoids.fiber_isGroupoid
  let iX : Over.mk (i ≫ a) ⟶ Over.mk a := Over.homMk i rfl
  let fX : Over.mk (i ≫ a) ⟶ Over.mk b := Over.homMk f w.symm
  let aX : Over.mk a ⟶ Over.mk (𝟙 Y') := Over.homMk a (Category.comp_id a)
  let bX : Over.mk b ⟶ Over.mk (𝟙 Y') := Over.homMk b (Category.comp_id b)
  have hsqX : iX ≫ aX = fX ≫ bX := Over.OverMorphism.ext w
  have : IsAffineHom ((BigFppfOver.toScheme B S hS).map fX.left) :=
    ‹IsAffineHom ((BigFppfOver.toScheme B S hS).map f)›
  have glue : ∀ (y₁ y₂ : p.Fiber Y') (sX' : (p.isomPresheaf y₁ y₂).obj (op (Over.mk a)))
      (sY : (p.isomPresheaf y₁ y₂).obj (op (Over.mk b))),
      (p.isomPresheaf y₁ y₂).map iX.op sX' = (p.isomPresheaf y₁ y₂).map fX.op sY →
      ∃! s : (p.isomPresheaf y₁ y₂).obj (op (Over.mk (𝟙 Y'))),
        (p.isomPresheaf y₁ y₂).map aX.op s = sX' ∧ (p.isomPresheaf y₁ y₂).map bX.op s = sY := by
    intro y₁ y₂ sX' sY hc
    obtain ⟨F, hF, ⟨e⟩⟩ := h𝒳 Y' y₁ y₂
    exact existsUnique_section_over B S hS (p.isomPresheaf y₁ y₂) F hF e iX fX aX bX hi hsq
      sX' sY hc
  let toSec : ∀ {y₁ y₂ : p.Fiber Y'} (φ : y₁ ⟶ y₂),
      (p.isomPresheaf y₁ y₂).obj (op (Over.mk (𝟙 Y'))) := fun {y₁ y₂} φ =>
    ⟨idSection p φ, (hgrp Y').all_isIso _⟩
  have resA : ∀ {y₁ y₂ : p.Fiber Y'} (φ : y₁ ⟶ y₂),
      ((p.isomPresheaf y₁ y₂).map aX.op (toSec φ)).1 = c.homMap a φ := fun φ =>
    morRestrict_idSection p φ a
  have resB : ∀ {y₁ y₂ : p.Fiber Y'} (φ : y₁ ⟶ y₂),
      ((p.isomPresheaf y₁ y₂).map bX.op (toSec φ)).1 = c.homMap b φ := fun φ =>
    morRestrict_idSection p φ b
  refine ⟨⟨fun {y₁ y₂} ψ => ?_⟩, ⟨fun {y₁ y₂} φ₁ φ₂ hφ => ?_⟩⟩
  · let sX' : (p.isomPresheaf y₁ y₂).obj (op (Over.mk a)) := ⟨ψ.snd, (hgrp _).all_isIso _⟩
    let sY : (p.isomPresheaf y₁ y₂).obj (op (Over.mk b)) := ⟨ψ.fst, (hgrp _).all_isIso _⟩
    have hc : (p.isomPresheaf y₁ y₂).map iX.op sX' = (p.isomPresheaf y₁ y₂).map fX.op sY :=
      Subtype.ext (morRestrict_snd_eq_morRestrict_fst p f i b a w.symm ψ.fst ψ.snd ψ.w)
    obtain ⟨s, ⟨hs₁, hs₂⟩, -⟩ := glue y₁ y₂ sX' sY hc
    let φ : y₁ ⟶ y₂ := (pullbackFiberIdIso y₁).inv ≫ s.1 ≫ (pullbackFiberIdIso y₂).hom
    have hφ : toSec φ = s := Subtype.ext (idSection_surjective p s.1)
    refine ⟨φ, ?_⟩
    apply CategoricalPullback.hom_ext
    · show c.homMap b φ = ψ.fst
      rw [← resB, hφ, hs₂]
    · show c.homMap a φ = ψ.snd
      rw [← resA, hφ, hs₁]
  · have h₁ : c.homMap b φ₁ = c.homMap b φ₂ := congrArg CategoricalPullback.Hom.fst hφ
    have h₂ : c.homMap a φ₁ = c.homMap a φ₂ := congrArg CategoricalPullback.Hom.snd hφ
    have hc : (p.isomPresheaf y₁ y₂).map iX.op ((p.isomPresheaf y₁ y₂).map aX.op (toSec φ₁)) =
        (p.isomPresheaf y₁ y₂).map fX.op ((p.isomPresheaf y₁ y₂).map bX.op (toSec φ₁)) := by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hsqX]
    obtain ⟨s, -, huniq⟩ := glue y₁ y₂ _ _ hc
    have e₂ := huniq (toSec φ₂) ⟨Subtype.ext (by rw [resA, resA, h₂]),
      Subtype.ext (by rw [resB, resB, h₁])⟩
    exact idSection_injective p (congrArg Subtype.val ((huniq (toSec φ₁) ⟨rfl, rfl⟩).trans e₂.symm))

/-- **Restriction to a thickening-and-affine pushout is fully faithful on an algebraic stack.**
The full-faithfulness half of Stacks 07WN, at the hypotheses of that tag: `X ⟶ X'` a
thickening, `X ⟶ Y` affine, `Y'` the pushout in schemes over `S`, and `𝒵` an algebraic stack
over `S`. The diagonal of an algebraic stack is representable by algebraic spaces, so its
isomorphism presheaves are algebraic spaces by Stacks 045G, and
`AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_full_and_faithful` applies. -/
theorem fiberSquareComparison_full_and_faithful_of_isAlgebraicStack.{w'}
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    (h𝒵 : IsAlgebraicStack.{u, w'} B S hS 𝒵)
    {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y') (w : i ≫ a = f ≫ b)
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffineHom ((BigFppfOver.toScheme B S hS).map f)]
    (hsq : IsPushout ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)) :
    letI : 𝒵.p.IsFibered := (Classical.choose h𝒵).isFibered
    (Deformation.Artin.fiberSquareComparison 𝒵.p (𝒵.p.chosenPullbacks) f i b a w.symm).Full ∧
    (Deformation.Artin.fiberSquareComparison 𝒵.p (𝒵.p.chosenPullbacks) f i b a
      w.symm).Faithful := by
  let 𝒳 := CatFiberedInGroupoids.mk 𝒵 (Classical.choose h𝒵)
  exact fiberSquareComparison_full_and_faithful B S hS 𝒳
    ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳).mp
      (Classical.choose_spec h𝒵).2.1)
    i f a b w hi hsq

end AlgebraicGeometry.Stack.ThickeningPushout
