module

public import StacksFrontier.CategoryTheory.FibredOneMorphism
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.SieveDescentDatum

/-!
# Chosen pullbacks along a 1-morphism of fibred categories

Let `F : 𝒮 ⥤ 𝒯` be a 1-morphism of fibred categories `p : 𝒮 ⥤ 𝒞` and `q : 𝒯 ⥤ 𝒞` over `𝒞`.
Since `F` preserves strongly cartesian morphisms, the image under `F` of the chosen pullback of an
object `a` of the fibre of `p` over `U` along `f : V ⟶ U` is again a pullback of `F a` along `f`,
hence canonically isomorphic to the chosen pullback of `F a` along `f`. That comparison
isomorphism is natural in the morphisms of the fibre and in the object of `𝒞/U`, and compatible
with iterated chosen pullbacks; conjugating the gluing isomorphisms of a descent datum for `p` by
it carries the datum to a descent datum for `q`.

## Main definitions

* `CategoryTheory.Functor.mapPbIso`: the comparison isomorphism between the chosen pullback of
  `F a` along `f` and the image under `F` of the chosen pullback of `a` along `f`.
* `CategoryTheory.Functor.SieveDescentDatum.mapF`: the image under `F` of a descent datum for `p`
  relative to a sieve.

## Main results

* `CategoryTheory.Functor.pullbackFiberMap_mapPbIso_hom`: `mapPbIso` is natural in the object of
  `𝒞/U`.
* `CategoryTheory.Functor.mapPbIso_naturality`: `mapPbIso` is natural in the morphism of the fibre.
* `CategoryTheory.Functor.mapPbIso_comp`: `mapPbIso` is compatible with iterated chosen pullbacks.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒯 : Type u₃} [Category.{v₃} 𝒯]

variable {p : 𝒮 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒞} {F : 𝒮 ⥤ 𝒯} [p.IsFibered] [q.IsFibered]

/-! ### The lifting API with the lifting facts as explicit hypotheses

Implementation note: an endpoint of the composites below is spelled `Fiber.fiberInclusion.obj x`
on one side of a `≫` and `F.obj x.1` on the other, and the two spellings agree only after `Fiber`,
`Fiber.fiberInclusion` and `Fiber.mapOfComp` unfold, which instance search does not do. The lemmas
below therefore take the lifting arguments of `IsHomLift.comp_lift_id_*`, `IsFibered.comp` and
`IsStronglyCartesian.ext` explicitly; without them the proofs here would need a transparency
option override. -/

omit [p.IsFibered] [q.IsFibered] in
/-- `IsHomLift.comp_lift_id_right` with its two lifting hypotheses explicit. -/
private lemma isHomLift_comp_of_right_lift_id {R S T : 𝒞} {x y z : 𝒯} (φ : x ⟶ y) (ψ : y ⟶ z)
    (f : R ⟶ S) (hφ : q.IsHomLift f φ) (hψ : q.IsHomLift (𝟙 T) ψ) : q.IsHomLift f (φ ≫ ψ) :=
  have := hφ
  have := hψ
  IsHomLift.comp_lift_id_right' q f φ T ψ

omit [p.IsFibered] [q.IsFibered] in
/-- `IsHomLift.comp_lift_id_left` with its two lifting hypotheses explicit. -/
private lemma isHomLift_comp_of_left_lift_id {R S T : 𝒞} {x y z : 𝒯} (φ : x ⟶ y) (ψ : y ⟶ z)
    (f : S ⟶ T) (hφ : q.IsHomLift (𝟙 R) φ) (hψ : q.IsHomLift f ψ) : q.IsHomLift f (φ ≫ ψ) :=
  have := hφ
  have := hψ
  IsHomLift.comp_lift_id_left' q R φ f ψ

omit [p.IsFibered] in
/-- The composite of two cartesian morphisms is cartesian, with the two hypotheses explicit. -/
private lemma isCartesian_comp {R S T : 𝒞} {x y z : 𝒯} (f : R ⟶ S) (g : S ⟶ T) (φ : x ⟶ y)
    (ψ : y ⟶ z) (hφ : q.IsCartesian f φ) (hψ : q.IsCartesian g ψ) :
    q.IsCartesian (f ≫ g) (φ ≫ ψ) :=
  have := hφ
  have := hψ
  IsFibered.comp f g φ ψ

omit [p.IsFibered] [q.IsFibered] in
/-- `IsStronglyCartesian.ext` with its three lifting hypotheses explicit. -/
private lemma isStronglyCartesian_ext {R S R' : 𝒞} {x y z : 𝒯} {f : R ⟶ S} (φ : x ⟶ y)
    (hφ : q.IsStronglyCartesian f φ) (g : R' ⟶ R) {ψ ψ' : z ⟶ x} (hψ : q.IsHomLift g ψ)
    (hψ' : q.IsHomLift g ψ') (hcomp : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' :=
  have := hφ
  have := hψ
  have := hψ'
  IsStronglyCartesian.ext q f φ g hcomp

/-- If `G ψ ≫ c = d` and `G φ ≫ d = e`, then `G (φ ≫ ψ) ≫ c = e`. -/
private lemma map_comp_comp_eq {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {x y z : C}
    (φ : x ⟶ y) (ψ : y ⟶ z) {W : D} (c : G.obj z ⟶ W) {d : G.obj y ⟶ W} {e : G.obj x ⟶ W}
    (h₁ : G.map ψ ≫ c = d) (h₂ : G.map φ ≫ d = e) : G.map (φ ≫ ψ) ≫ c = e := by
  rw [G.map_comp, Category.assoc, h₁, h₂]

omit [q.IsFibered] in
/-- The image under `F` of the chosen cartesian lift of `f` at `a` is a cartesian lift of `f` at
`F a`, since `F` preserves strongly cartesian morphisms. -/
lemma isCartesian_map_pullbackMap_of_one (hF1 : IsFibredOneMorphism p q F) {U : 𝒞}
    (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    q.IsCartesian f (F.map (IsPreFibered.pullbackMap a.2 f)) :=
  have := hF1.map_isStronglyCartesian f (IsPreFibered.pullbackMap a.2 f) inferInstance
  inferInstance

/-- The comparison isomorphism, in the fibre of `q` over `V`, between the chosen pullback of `F a`
along `f` and the image under `F` of the chosen pullback of `a` along `f`: both carry a cartesian
morphism over `f` to `F a`. -/
noncomputable def mapPbIso (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    pullbackFiber q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f ≅
      (Fiber.mapOfComp p q F hF1.comp_eq V).obj (pullbackFiber p a f) :=
  fiberIsoOfCartesian f
    (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 f)
    (F.map (IsPreFibered.pullbackMap a.2 f)) inferInstance
    (isCartesian_map_pullbackMap_of_one hF1 a f)

/-- `mapPbIso` followed by the image under `F` of the chosen cartesian lift of `f` at `a` is the
chosen cartesian lift of `f` at `F a`. -/
lemma mapPbIso_hom_fac (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    Fiber.fiberInclusion.map (mapPbIso hF1 a f).hom ≫ F.map (IsPreFibered.pullbackMap a.2 f) =
      IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-! Implementation note: the reassociated forms of `mapPbIso_hom_fac`, `mapPbIso_inv_fac` and
`pullbackFiberMap_mapPbIso_hom` are written by hand. Their two sides end at `F.obj a.1` and at
`((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).1`, which agree only after `Fiber`,
`Fiber.fiberInclusion` and `Fiber.mapOfComp` unfold; `@[reassoc]` does not unfold them and emits
`(a ≫ b) ≫ h = c ≫ h`, which cannot be rewritten with. -/

/-- `mapPbIso_hom_fac` reassociated. -/
lemma mapPbIso_hom_fac_assoc (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U)
    {V : 𝒞} (f : V ⟶ U) {Z : 𝒯} (k : F.obj a.1 ⟶ Z) :
    Fiber.fiberInclusion.map (mapPbIso hF1 a f).hom ≫
        F.map (IsPreFibered.pullbackMap a.2 f) ≫ k =
      IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 f ≫ k :=
  (Category.assoc _ _ _).symm.trans (mapPbIso_hom_fac hF1 a f =≫ k)

/-- The inverse of `mapPbIso` followed by the chosen cartesian lift of `f` at `F a` is the image
under `F` of the chosen cartesian lift of `f` at `a`. -/
lemma mapPbIso_inv_fac (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    Fiber.fiberInclusion.map (mapPbIso hF1 a f).inv ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 f =
      F.map (IsPreFibered.pullbackMap a.2 f) :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- `mapPbIso_inv_fac` reassociated. -/
lemma mapPbIso_inv_fac_assoc (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U)
    {V : 𝒞} (f : V ⟶ U) {Z : 𝒯}
    (k : ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).1 ⟶ Z) :
    Fiber.fiberInclusion.map (mapPbIso hF1 a f).inv ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 f ≫ k =
      F.map (IsPreFibered.pullbackMap a.2 f) ≫ k :=
  (Category.assoc _ _ _).symm.trans (mapPbIso_inv_fac hF1 a f =≫ k)

/-- `mapPbIso` is natural in the object of `𝒞/U`: it turns the restriction map of the chosen
pullbacks of `F a` into the image under `F` of the restriction map of the chosen pullbacks
of `a`. -/
lemma pullbackFiberMap_mapPbIso_hom (hF1 : IsFibredOneMorphism p q F) {U : 𝒞}
    (a : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) :
    pullbackFiberMap q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) h ≫
        Fiber.fiberInclusion.map (mapPbIso hF1 a g₂.hom).hom =
      Fiber.fiberInclusion.map (mapPbIso hF1 a g₁.hom).hom ≫ F.map (pullbackFiberMap p a h) := by
  have hscart : q.IsStronglyCartesian g₂.hom (F.map (IsPreFibered.pullbackMap a.2 g₂.hom)) :=
    hF1.map_isStronglyCartesian g₂.hom _ inferInstance
  have hl : q.IsHomLift h.left
      (pullbackFiberMap q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) h ≫
        Fiber.fiberInclusion.map (mapPbIso hF1 a g₂.hom).hom) :=
    isHomLift_comp_of_right_lift_id
      (pullbackFiberMap q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) h)
      (Fiber.fiberInclusion.map (mapPbIso hF1 a g₂.hom).hom) h.left
      (pullbackFiberMap_isHomLift q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) h)
      (mapPbIso hF1 a g₂.hom).hom.2
  have hr : q.IsHomLift h.left
      (Fiber.fiberInclusion.map (mapPbIso hF1 a g₁.hom).hom ≫ F.map (pullbackFiberMap p a h)) :=
    isHomLift_comp_of_left_lift_id
      (Fiber.fiberInclusion.map (mapPbIso hF1 a g₁.hom).hom)
      (F.map (pullbackFiberMap p a h)) h.left (mapPbIso hF1 a g₁.hom).hom.2
      (hF1.map_isHomLift h.left (pullbackFiberMap p a h))
  have hL : (pullbackFiberMap q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) h ≫
        Fiber.fiberInclusion.map (mapPbIso hF1 a g₂.hom).hom) ≫
        F.map (IsPreFibered.pullbackMap a.2 g₂.hom) =
      IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 g₁.hom :=
    (Category.assoc _ _ _).trans
      ((_ ≫= mapPbIso_hom_fac hF1 a g₂.hom).trans
        (pullbackFiberMap_fac q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) h))
  have hR : (Fiber.fiberInclusion.map (mapPbIso hF1 a g₁.hom).hom ≫
        F.map (pullbackFiberMap p a h)) ≫ F.map (IsPreFibered.pullbackMap a.2 g₂.hom) =
      IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 g₁.hom :=
    (Category.assoc _ _ _).trans
      ((_ ≫= ((F.map_comp _ _).symm.trans
            (congrArg F.map (pullbackFiberMap_fac p a h)))).trans
        (mapPbIso_hom_fac hF1 a g₁.hom))
  exact isStronglyCartesian_ext (F.map (IsPreFibered.pullbackMap a.2 g₂.hom)) hscart h.left
    hl hr (hL.trans hR.symm)

/-- `pullbackFiberMap_mapPbIso_hom` reassociated. -/
lemma pullbackFiberMap_mapPbIso_hom_assoc (hF1 : IsFibredOneMorphism p q F) {U : 𝒞}
    (a : p.Fiber U) {g₁ g₂ : Over U} (h : g₁ ⟶ g₂) {Z : 𝒯}
    (k : Fiber.fiberInclusion.obj ((Fiber.mapOfComp p q F hF1.comp_eq g₂.left).obj
      (pullbackFiber p a g₂.hom)) ⟶ Z) :
    pullbackFiberMap q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) h ≫
        Fiber.fiberInclusion.map (mapPbIso hF1 a g₂.hom).hom ≫ k =
      Fiber.fiberInclusion.map (mapPbIso hF1 a g₁.hom).hom ≫
        F.map (pullbackFiberMap p a h) ≫ k :=
  (Category.assoc _ _ _).symm.trans
    ((pullbackFiberMap_mapPbIso_hom hF1 a h =≫ k).trans (Category.assoc _ _ _))

/-- `mapPbIso` is natural in the morphism of the fibre. -/
@[reassoc]
lemma mapPbIso_naturality (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} {a b : p.Fiber U}
    (φ : a ⟶ b) {V : 𝒞} (f : V ⟶ U) :
    (Fiber.mapOfComp p q F hF1.comp_eq V).map (pullbackFiberHom φ f) ≫ (mapPbIso hF1 b f).inv =
      (mapPbIso hF1 a f).inv ≫
        pullbackFiberHom ((Fiber.mapOfComp p q F hF1.comp_eq U).map φ) f := by
  have hL : Fiber.fiberInclusion.map
        ((Fiber.mapOfComp p q F hF1.comp_eq V).map (pullbackFiberHom φ f) ≫
          (mapPbIso hF1 b f).inv) ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj b).2 f =
      F.map (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map φ) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _ (mapPbIso_inv_fac hF1 b f)
      ((Fiber.fiberInclusion_map_mapOfComp_map p q F hF1.comp_eq V
          (pullbackFiberHom φ f) =≫ _).trans <|
        (F.map_comp _ _).symm.trans (congrArg F.map (pullbackFiberHom_fac φ f)))
  have hR : Fiber.fiberInclusion.map
        ((mapPbIso hF1 a f).inv ≫
          pullbackFiberHom ((Fiber.mapOfComp p q F hF1.comp_eq U).map φ) f) ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj b).2 f =
      F.map (IsPreFibered.pullbackMap a.2 f ≫ Fiber.fiberInclusion.map φ) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _
      (pullbackFiberHom_fac ((Fiber.mapOfComp p q F hF1.comp_eq U).map φ) f)
      ((Category.assoc _ _ _).symm.trans <|
        (mapPbIso_inv_fac hF1 a f =≫ _).trans <|
          (_ ≫= Fiber.fiberInclusion_map_mapOfComp_map p q F hF1.comp_eq U φ).trans
            (F.map_comp _ _).symm)
  exact fiber_hom_ext_of_cartesian f
    (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj b).2 f)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ (hL.trans hR.symm)

/-- `mapPbIso` is compatible with iterated chosen pullbacks. -/
@[reassoc]
lemma mapPbIso_comp (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U) {V Z : 𝒞}
    (f : V ⟶ U) (γ : Z ⟶ V) :
    (Fiber.mapOfComp p q F hF1.comp_eq Z).map (pullbackFiberCompIso a f γ).hom ≫
        (mapPbIso hF1 a (γ ≫ f)).inv =
      (mapPbIso hF1 (pullbackFiber p a f) γ).inv ≫
        pullbackFiberHom (mapPbIso hF1 a f).inv γ ≫
        (pullbackFiberCompIso ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f γ).hom := by
  have hL : Fiber.fiberInclusion.map
        ((Fiber.mapOfComp p q F hF1.comp_eq Z).map (pullbackFiberCompIso a f γ).hom ≫
          (mapPbIso hF1 a (γ ≫ f)).inv) ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 (γ ≫ f) =
      F.map (IsPreFibered.pullbackMap (pullbackFiber p a f).2 γ ≫
        IsPreFibered.pullbackMap a.2 f) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _ (mapPbIso_inv_fac hF1 a (γ ≫ f))
      ((Fiber.fiberInclusion_map_mapOfComp_map p q F hF1.comp_eq Z
          (pullbackFiberCompIso a f γ).hom =≫ _).trans <|
        (F.map_comp _ _).symm.trans (congrArg F.map (pullbackFiberCompIso_hom_fac a f γ)))
  have hinner : Fiber.fiberInclusion.map
        (pullbackFiberHom (mapPbIso hF1 a f).inv γ ≫
          (pullbackFiberCompIso ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f γ).hom) ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 (γ ≫ f) =
      IsPreFibered.pullbackMap
          ((Fiber.mapOfComp p q F hF1.comp_eq V).obj (pullbackFiber p a f)).2 γ ≫
        F.map (IsPreFibered.pullbackMap a.2 f) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _
      (pullbackFiberCompIso_hom_fac ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f γ)
      ((Category.assoc _ _ _).symm.trans <|
        (pullbackFiberHom_fac (mapPbIso hF1 a f).inv γ =≫ _).trans <|
          (Category.assoc _ _ _).trans (_ ≫= mapPbIso_inv_fac hF1 a f))
  have hR : Fiber.fiberInclusion.map
        ((mapPbIso hF1 (pullbackFiber p a f) γ).inv ≫
          pullbackFiberHom (mapPbIso hF1 a f).inv γ ≫
          (pullbackFiberCompIso ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f γ).hom) ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 (γ ≫ f) =
      F.map (IsPreFibered.pullbackMap (pullbackFiber p a f).2 γ ≫
        IsPreFibered.pullbackMap a.2 f) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _ hinner
      ((Category.assoc _ _ _).symm.trans <|
        (mapPbIso_inv_fac hF1 (pullbackFiber p a f) γ =≫ _).trans (F.map_comp _ _).symm)
  exact fiber_hom_ext_of_cartesian (γ ≫ f)
    (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 (γ ≫ f))
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ (hL.trans hR.symm)

/-- `mapPbIso_comp` with the two contractions inverted. -/
@[reassoc]
lemma mapPbIso_comp_inv (hF1 : IsFibredOneMorphism p q F) {U : 𝒞} (a : p.Fiber U)
    {V Z : 𝒞} (f : V ⟶ U) (γ : Z ⟶ V) :
    (mapPbIso hF1 a (γ ≫ f)).hom ≫
        (Fiber.mapOfComp p q F hF1.comp_eq Z).map (pullbackFiberCompIso a f γ).inv ≫
        (mapPbIso hF1 (pullbackFiber p a f) γ).inv =
      (pullbackFiberCompIso ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f γ).inv ≫
        pullbackFiberHom (mapPbIso hF1 a f).hom γ := by
  have hγ : q.IsCartesian γ (IsPreFibered.pullbackMap
      ((Fiber.mapOfComp p q F hF1.comp_eq V).obj (pullbackFiber p a f)).2 γ) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have hf : q.IsCartesian f (F.map (IsPreFibered.pullbackMap a.2 f)) :=
    isCartesian_map_pullbackMap_of_one hF1 a f
  have hCγ : Fiber.fiberInclusion.map (mapPbIso hF1 (pullbackFiber p a f) γ).inv ≫
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq V).obj
            (pullbackFiber p a f)).2 γ ≫ F.map (IsPreFibered.pullbackMap a.2 f)) =
      F.map (IsPreFibered.pullbackMap (pullbackFiber p a f).2 γ ≫
        IsPreFibered.pullbackMap a.2 f) :=
    (Category.assoc _ _ _).symm.trans <|
      (mapPbIso_inv_fac hF1 (pullbackFiber p a f) γ =≫ _).trans (F.map_comp _ _).symm
  have hBC : Fiber.fiberInclusion.map
        ((Fiber.mapOfComp p q F hF1.comp_eq Z).map (pullbackFiberCompIso a f γ).inv ≫
          (mapPbIso hF1 (pullbackFiber p a f) γ).inv) ≫
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq V).obj
            (pullbackFiber p a f)).2 γ ≫ F.map (IsPreFibered.pullbackMap a.2 f)) =
      F.map (IsPreFibered.pullbackMap a.2 (γ ≫ f)) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _ hCγ
      ((Fiber.fiberInclusion_map_mapOfComp_map p q F hF1.comp_eq Z
          (pullbackFiberCompIso a f γ).inv =≫ _).trans <|
        (F.map_comp _ _).symm.trans (congrArg F.map (pullbackFiberCompIso_inv_fac a f γ)))
  have hL : Fiber.fiberInclusion.map
        ((mapPbIso hF1 a (γ ≫ f)).hom ≫
          (Fiber.mapOfComp p q F hF1.comp_eq Z).map (pullbackFiberCompIso a f γ).inv ≫
          (mapPbIso hF1 (pullbackFiber p a f) γ).inv) ≫
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq V).obj
            (pullbackFiber p a f)).2 γ ≫ F.map (IsPreFibered.pullbackMap a.2 f)) =
      IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 (γ ≫ f) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _ hBC (mapPbIso_hom_fac hF1 a (γ ≫ f))
  have hEγ : Fiber.fiberInclusion.map (pullbackFiberHom (mapPbIso hF1 a f).hom γ) ≫
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq V).obj
            (pullbackFiber p a f)).2 γ ≫ F.map (IsPreFibered.pullbackMap a.2 f)) =
      IsPreFibered.pullbackMap
          (pullbackFiber q ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f).2 γ ≫
        IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 f :=
    (Category.assoc _ _ _).symm.trans <|
      (pullbackFiberHom_fac (mapPbIso hF1 a f).hom γ =≫ _).trans <|
        (Category.assoc _ _ _).trans (_ ≫= mapPbIso_hom_fac hF1 a f)
  have hR : Fiber.fiberInclusion.map
        ((pullbackFiberCompIso ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f γ).inv ≫
          pullbackFiberHom (mapPbIso hF1 a f).hom γ) ≫
        (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq V).obj
            (pullbackFiber p a f)).2 γ ≫ F.map (IsPreFibered.pullbackMap a.2 f)) =
      IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a).2 (γ ≫ f) :=
    map_comp_comp_eq Fiber.fiberInclusion _ _ _ hEγ
      (pullbackFiberCompIso_inv_fac ((Fiber.mapOfComp p q F hF1.comp_eq U).obj a) f γ)
  exact fiber_hom_ext_of_cartesian (γ ≫ f)
    (IsPreFibered.pullbackMap ((Fiber.mapOfComp p q F hF1.comp_eq V).obj
      (pullbackFiber p a f)).2 γ ≫ F.map (IsPreFibered.pullbackMap a.2 f))
    (isCartesian_comp γ f _ _ hγ hf) _ _ (hL.trans hR.symm)

/-- The image under `F` of a descent datum for `p`: its objects are transported by the functors
induced on fibres and its gluing isomorphisms are conjugated by `mapPbIso`. -/
noncomputable def SieveDescentDatum.mapF (hF1 : IsFibredOneMorphism p q F) {U : 𝒞}
    {R : Sieve U} (D : SieveDescentDatum p R) : SieveDescentDatum q R where
  obj {V} f hf := (Fiber.mapOfComp p q F hF1.comp_eq V).obj (D.obj f hf)
  iso {V W Z} {f} hf {g} hg ε ε' heq :=
    mapPbIso hF1 (D.obj f hf) ε ≪≫
      (Fiber.mapOfComp p q F hF1.comp_eq Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
      (mapPbIso hF1 (D.obj g hg) ε').symm
  cocycle {V W X Z} {f} hf {g} hg {h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc, D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]
  iso_pullback {V W Z Z'} {f} hf {g} hg ε ε' heq γ := by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      pullbackFiberIso_hom, pullbackFiberHom_comp]
    rw [← D.iso_pullback hf hg ε ε' heq γ]
    simp only [pullbackFiberIso_hom, Functor.map_comp, Category.assoc,
      ← mapPbIso_comp_inv_assoc hF1 (D.obj f hf) ε γ]
    rw [← mapPbIso_naturality_assoc hF1 (D.iso hf hg ε ε' heq).hom γ,
      ← mapPbIso_comp hF1 (D.obj g hg) ε' γ]

end CategoryTheory.Functor

end
