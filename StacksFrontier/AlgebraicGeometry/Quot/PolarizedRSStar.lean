module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPushout
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPushoutEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# Condition (RS*) for the stack of polarized schemes

Stacks 0D44 says that for a pushout `S' = S ⨿_T T'` of schemes along a thickening `T ⟶ T'` and an
affine `T ⟶ S`, the comparison `𝒫olarized_{S'} ⟶ 𝒫olarized_S ×_{𝒫olarized_T} 𝒫olarized_{T'}` is an
equivalence. Condition (RS*) of Stacks 07Y8, the input of Stacks 07Y9, asks for this equivalence
for the category `𝒫olarized` read over the big fppf site of the base `S` (the slice of the site at
a terminal object), with its chosen pullbacks, at squares with affine corners along a first-order
thickening. This file compares the two comparison functors, for any category fibred in groupoids
and its slice at a terminal object, and deduces (RS*) for `𝒫olarized`, as in the first paragraph of
the proof of [Stacks, Tag 0D4S].

## Main results

* `CategoryTheory.Functor.sliceFiberFunctor`: the fibre of the slice over `V` is the fibre over
  `V.left`.
* `CategoryTheory.Functor.isEquivalence_fiberSquareComparison_sliceAtTerminal`: the comparison
  functor of a square of the slice is an equivalence if that of the underlying square is.
* `AlgebraicGeometry.satisfiesRSStar_polarizedSliceProjection`: `𝒫olarized` satisfies (RS*).

## References

* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0D4S](https://stacks.math.columbia.edu/tag/0D4S)
-/

open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂ u

variable {C : Type u₁} [Category.{v₁} C] {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ C) {T : C}
  (hT : IsTerminal T)

/-- A morphism lying over a morphism of the slice lies over its underlying morphism. -/
theorem isHomLift_left_of_sliceAtTerminal {V W : Over T} (g : V ⟶ W) {a b : 𝒳} (φ : a ⟶ b)
    (h : (p.sliceAtTerminal hT).IsHomLift g φ) : p.IsHomLift g.left φ := by
  have hf := IsHomLift.fac' (p.sliceAtTerminal hT) g φ
  have hl := congrArg CommaMorphism.left hf
  simp only [Over.comp_left, Over.eqToHom_left, sliceAtTerminal_map_left] at hl
  exact IsHomLift.of_fac' p g.left φ
    (congrArg Comma.left (IsHomLift.domain_eq (p.sliceAtTerminal hT) g φ))
    (congrArg Comma.left (IsHomLift.codomain_eq (p.sliceAtTerminal hT) g φ)) hl

/-- A morphism lying over the underlying morphism of a morphism of the slice lies over it. -/
theorem isHomLift_sliceAtTerminal_of_left {V W : Over T} (g : V ⟶ W) {a b : 𝒳} (φ : a ⟶ b)
    (ha : (p.sliceAtTerminal hT).obj a = V) (hb : (p.sliceAtTerminal hT).obj b = W)
    (h : p.IsHomLift g.left φ) : (p.sliceAtTerminal hT).IsHomLift g φ := by
  refine IsHomLift.of_fac' _ g φ ha hb ?_
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left, sliceAtTerminal_map_left]
  exact IsHomLift.fac' p g.left φ

/-- The fibre of the slice over `V` is the fibre over the underlying object. -/
def sliceFiberFunctor (V : Over T) : (p.sliceAtTerminal hT).Fiber V ⥤ p.Fiber V.left where
  obj x := ⟨x.1, congrArg Comma.left x.2⟩
  map φ := ⟨φ.1, isHomLift_left_of_sliceAtTerminal p hT (𝟙 V) φ.1 φ.2⟩

/-- `sliceFiberFunctor` does not change the underlying objects. -/
@[simp]
theorem fiberInclusion_obj_sliceFiberFunctor_obj (V : Over T)
    (x : (p.sliceAtTerminal hT).Fiber V) :
    Fiber.fiberInclusion.obj ((sliceFiberFunctor p hT V).obj x) = Fiber.fiberInclusion.obj x :=
  rfl

/-- `sliceFiberFunctor` does not change the underlying morphisms. -/
@[simp]
theorem fiberInclusion_map_sliceFiberFunctor_map (V : Over T)
    {x y : (p.sliceAtTerminal hT).Fiber V} (u : x ⟶ y) :
    Fiber.fiberInclusion.map ((sliceFiberFunctor p hT V).map u) = Fiber.fiberInclusion.map u :=
  rfl

/-- `sliceFiberFunctor` is faithful. -/
instance (V : Over T) : (sliceFiberFunctor p hT V).Faithful where
  map_injective {X Y} _ _ h := Subtype.ext <| congrArg
    (fun φ : (sliceFiberFunctor p hT V).obj X ⟶ (sliceFiberFunctor p hT V).obj Y => φ.1) h

/-- `sliceFiberFunctor` is full. -/
instance (V : Over T) : (sliceFiberFunctor p hT V).Full where
  map_surjective {x y} ψ :=
    ⟨⟨ψ.1, isHomLift_sliceAtTerminal_of_left p hT (𝟙 V) ψ.1 x.2 y.2 ψ.2⟩, rfl⟩

/-- `sliceFiberFunctor` is essentially surjective. -/
instance (V : Over T) : (sliceFiberFunctor p hT V).EssSurj where
  mem_essImage z := ⟨⟨z.1, p.sliceAtTerminal_obj_eq hT z.2⟩, ⟨eqToIso rfl⟩⟩

/-- `sliceFiberFunctor` is an equivalence. -/
instance (V : Over T) : (sliceFiberFunctor p hT V).IsEquivalence where


variable (hp : p.IsFiberedInGroupoids)

include hp in
/-- The chosen pullbacks of the slice are cartesian over the underlying morphisms. -/
theorem isCartesian_left_chosenPullbacks_map {A A' : Over T} (g : A ⟶ A')
    (y : (p.sliceAtTerminal hT).Fiber A') :
    letI : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
    p.IsCartesian g.left ((chosenPullbacks (p.sliceAtTerminal hT)).map g y) := by
  let : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
  have : p.IsHomLift g.left ((chosenPullbacks (p.sliceAtTerminal hT)).map g y) :=
    isHomLift_left_of_sliceAtTerminal p hT g _ inferInstance
  exact (hp.isStronglyCartesian_homLift g.left _).isCartesian_of_isStronglyCartesian

/-- The chosen pullback in the slice, read in the fibres of `p`, is the chosen pullback of `p`. -/
def slicePullbackIso {A A' : Over T} (g : A ⟶ A') :
    letI : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
    letI : p.IsFibered := hp.isFibered
    (chosenPullbacks (p.sliceAtTerminal hT)).pullbackFunctor g ⋙ sliceFiberFunctor p hT A ≅
      sliceFiberFunctor p hT A' ⋙ fiberPullback p g.left :=
  letI : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
  letI : p.IsFibered := hp.isFibered
  NatIso.ofComponents
    (fun y => fiberIsoOfCartesian g.left ((chosenPullbacks (p.sliceAtTerminal hT)).map g y)
      (fiberPullbackHom p g.left ((sliceFiberFunctor p hT A').obj y))
      (isCartesian_left_chosenPullbacks_map p hT hp g y)
      (isCartesian_fiberPullbackHom p g.left _))
    (fun {y y'} α => by
      refine fiber_hom_ext_of_cartesian g.left
        (fiberPullbackHom p g.left ((sliceFiberFunctor p hT A').obj y'))
        (isCartesian_fiberPullbackHom p g.left _) _ _ ?_
      have h1 := fiberIsoOfCartesian_hom_fac g.left
        (z := (sliceFiberFunctor p hT A).obj
          ((chosenPullbacks (p.sliceAtTerminal hT)).obj g y'))
        (z' := (fiberPullback p g.left).obj ((sliceFiberFunctor p hT A').obj y'))
        ((chosenPullbacks (p.sliceAtTerminal hT)).map g y')
        (fiberPullbackHom p g.left ((sliceFiberFunctor p hT A').obj y'))
        (isCartesian_left_chosenPullbacks_map p hT hp g y')
        (isCartesian_fiberPullbackHom p g.left _)
      have h2 := fiberIsoOfCartesian_hom_fac g.left
        (z := (sliceFiberFunctor p hT A).obj
          ((chosenPullbacks (p.sliceAtTerminal hT)).obj g y))
        (z' := (fiberPullback p g.left).obj ((sliceFiberFunctor p hT A').obj y))
        ((chosenPullbacks (p.sliceAtTerminal hT)).map g y)
        (fiberPullbackHom p g.left ((sliceFiberFunctor p hT A').obj y))
        (isCartesian_left_chosenPullbacks_map p hT hp g y)
        (isCartesian_fiberPullbackHom p g.left _)
      have h3 := fiberPullback_map_fac p g.left ((sliceFiberFunctor p hT A').map α)
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
      rw [h3]
      refine (congrArg (Fiber.fiberInclusion.map ((sliceFiberFunctor p hT A).map
        (((chosenPullbacks (p.sliceAtTerminal hT)).pullbackFunctor g).map α)) ≫ ·) h1).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_
        (congrArg (· ≫ Fiber.fiberInclusion.map ((sliceFiberFunctor p hT A').map α)) h2.symm)
      exact (chosenPullbacks (p.sliceAtTerminal hT)).homMap_fac g α)

/-- The comparison of chosen pullbacks commutes with the cartesian morphisms to the base. -/
@[reassoc (attr := simp)]
theorem slicePullbackIso_hom_app_fac {A A' : Over T} (g : A ⟶ A')
    (y : (p.sliceAtTerminal hT).Fiber A') :
    letI : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
    letI : p.IsFibered := hp.isFibered
    Fiber.fiberInclusion.map ((slicePullbackIso p hT hp g).hom.app y) ≫
        fiberPullbackHom p g.left ((sliceFiberFunctor p hT A').obj y) =
      (chosenPullbacks (p.sliceAtTerminal hT)).map g y := by
  let : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
  let : p.IsFibered := hp.isFibered
  exact fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse comparison of chosen pullbacks commutes with the cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem slicePullbackIso_inv_app_fac {A A' : Over T} (g : A ⟶ A')
    (y : (p.sliceAtTerminal hT).Fiber A') :
    letI : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
    letI : p.IsFibered := hp.isFibered
    Fiber.fiberInclusion.map ((slicePullbackIso p hT hp g).inv.app y) ≫
        (chosenPullbacks (p.sliceAtTerminal hT)).map g y =
      fiberPullbackHom p g.left ((sliceFiberFunctor p hT A').obj y) := by
  let : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
  let : p.IsFibered := hp.isFibered
  exact fiberIsoOfCartesian_inv_fac _ _ _ _ _

omit [Category.{v₁} C] in
/-- Transport along an equality of morphisms of the base of a chosen pullback. -/
@[reassoc (attr := simp)]
theorem eqToHom_app_choiceOfPullbacks_map {𝒮 : Type*} [Category 𝒮] {q : 𝒳 ⥤ 𝒮}
    (c : q.ChoiceOfPullbacks) {U V : 𝒮} {g g' : U ⟶ V} (h : g = g') (x : q.Fiber V) :
    Fiber.fiberInclusion.map ((eqToIso (congrArg c.pullbackFunctor h)).hom.app x) ≫ c.map g' x =
      c.map g x := by
  subst h
  exact Category.id_comp _

/-- The inverse of the comparison of iterated chosen pullbacks commutes with the cartesian
morphisms. -/
@[reassoc (attr := simp)]
theorem choiceOfPullbacks_pullbackFunctorCompIso_inv_app_fac {𝒮 : Type*} [Category 𝒮]
    {q : 𝒳 ⥤ 𝒮} (c : q.ChoiceOfPullbacks) {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : q.Fiber U) :
    Fiber.fiberInclusion.map ((c.pullbackFunctorCompIso g f).inv.app x) ≫ c.map (g ≫ f) x =
      c.map g (c.obj f x) ≫ c.map f x := by
  have e : (c.pullbackFunctorCompIso g f).inv.app x = (c.objCompIso g f x).inv := rfl
  rw [e, ← c.objCompIso_hom_fac g f x]
  have h0 : Fiber.fiberInclusion.map (c.objCompIso g f x).inv ≫
      Fiber.fiberInclusion.map (c.objCompIso g f x).hom = 𝟙 _ :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg _ (Iso.inv_hom_id _)).trans (Functor.map_id _ _))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (c.map g (c.obj f x) ≫ c.map f x)) h0).trans (Category.id_comp _))

/-- The comparison of iterated chosen pullbacks commutes with the cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem choiceOfPullbacks_pullbackFunctorCompIso_hom_app_fac {𝒮 : Type*} [Category 𝒮]
    {q : 𝒳 ⥤ 𝒮} (c : q.ChoiceOfPullbacks) {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : q.Fiber U) :
    Fiber.fiberInclusion.map ((c.pullbackFunctorCompIso g f).hom.app x) ≫ c.map g (c.obj f x) ≫
        c.map f x = c.map (g ≫ f) x :=
  c.objCompIso_hom_fac g f x


omit [Category.{v₁} C] in
/-- Transport of the chosen cartesian morphism of `p` along an equality of morphisms of the
base. -/
@[reassoc (attr := simp)]
theorem eqToHom_app_fiberPullbackHom {𝒮 : Type*} [Category 𝒮] (q : 𝒳 ⥤ 𝒮) [q.IsFibered]
    {U V : 𝒮} {g g' : U ⟶ V} (h : g = g') (x : q.Fiber V) :
    Fiber.fiberInclusion.map
          ((eqToIso (congrArg (fun k : U ⟶ V ↦ fiberPullback q k) h)).hom.app x) ≫
        fiberPullbackHom q g' x = fiberPullbackHom q g x := by
  subst h
  exact Category.id_comp _

omit [Category.{v₁} C] in
/-- The comparison of iterated base changes commutes with the cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem fiberPullbackCompIso_hom_app_fac {𝒮 : Type*} [Category 𝒮] (q : 𝒳 ⥤ 𝒮) [q.IsFibered]
    {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : q.Fiber U) :
    Fiber.fiberInclusion.map ((fiberPullbackCompIso q g f).hom.app x) ≫
        fiberPullbackHom q (g ≫ f) x =
      fiberPullbackHom q g ((fiberPullback q f).obj x) ≫ fiberPullbackHom q f x :=
  fiberInclusion_map_fiberPullbackCompIsoApp_hom q g f x

omit [Category.{v₁} C] in
/-- The inverse comparison of iterated base changes commutes with the cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem fiberPullbackCompIso_inv_app_fac {𝒮 : Type*} [Category 𝒮] (q : 𝒳 ⥤ 𝒮) [q.IsFibered]
    {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (x : q.Fiber U) :
    Fiber.fiberInclusion.map ((fiberPullbackCompIso q g f).inv.app x) ≫
        fiberPullbackHom q g ((fiberPullback q f).obj x) ≫ fiberPullbackHom q f x =
      fiberPullbackHom q (g ≫ f) x := by
  rw [← fiberPullbackCompIso_hom_app_fac q g f x]
  have h0 : Fiber.fiberInclusion.map ((fiberPullbackCompIso q g f).inv.app x) ≫
      Fiber.fiberInclusion.map ((fiberPullbackCompIso q g f).hom.app x) = 𝟙 _ :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg _ (Iso.inv_hom_id_app _ _)).trans (Functor.map_id _ _))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ fiberPullbackHom q (g ≫ f) x) h0).trans (Category.id_comp _))

section Square

variable {X X' Y Y' : Over T} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
  (w : i ≫ a = f ≫ b)

omit [Category.{v₂} 𝒳] in
include w in
/-- The underlying square of a commutative square of the slice commutes. -/
theorem left_comm_of_comm : f.left ≫ b.left = i.left ≫ a.left := by
  rw [← Over.comp_left, ← Over.comp_left, w]

attribute [local implicit_reducible] CategoryTheory.Functor.fiberSquareRestriction
  CategoryTheory.Limits.CategoricalPullback.map
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Functor.sliceFiberFunctor CategoryTheory.Functor.fiberPullback
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

/-- The coherence of the comparison of the two fibre squares, in explicit form. -/
theorem sliceSquare_coherence (z : (p.sliceAtTerminal hT).Fiber Y') :
    letI : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
    letI : p.IsFibered := hp.isFibered
    (fiberPullback p f.left).map ((slicePullbackIso p hT hp b).hom.app z) ≫
        (fiberPullbackSquareIso p i.left f.left a.left b.left
          (left_comm_of_comm i f a b w)).hom.app ((sliceFiberFunctor p hT Y').obj z) =
      ((slicePullbackIso p hT hp f).inv.app
          ((chosenPullbacks (p.sliceAtTerminal hT)).obj b z) ≫
        (sliceFiberFunctor p hT X).map
          ((((chosenPullbacks (p.sliceAtTerminal hT)).pullbackFunctorCompIso f b).symm ≪≫
            eqToIso (congrArg (chosenPullbacks (p.sliceAtTerminal hT)).pullbackFunctor w.symm) ≪≫
            (chosenPullbacks (p.sliceAtTerminal hT)).pullbackFunctorCompIso i a).hom.app z) ≫
        (slicePullbackIso p hT hp i).hom.app ((chosenPullbacks (p.sliceAtTerminal hT)).obj a z)) ≫
        (fiberPullback p i.left).map ((slicePullbackIso p hT hp a).hom.app z) := by
  let : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
  let : p.IsFibered := hp.isFibered
  refine fiber_hom_ext_of_cartesian (i.left ≫ a.left)
    (fiberPullbackHom p i.left ((fiberPullback p a.left).obj ((sliceFiberFunctor p hT Y').obj z)) ≫
      fiberPullbackHom p a.left ((sliceFiberFunctor p hT Y').obj z))
    (isCartesian_fiberPullbackHom_comp p i.left a.left _) _ _ ?_
  simp only [fiberPullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj, fiberPullbackCompIso_inv_app_fac,
    fiberPullback_map_fac_assoc, slicePullbackIso_hom_app_fac, slicePullbackIso_hom_app_fac_assoc,
    fiberInclusion_map_sliceFiberFunctor_map, choiceOfPullbacks_pullbackFunctorCompIso_hom_app_fac]
  rw [eqToHom_app_choiceOfPullbacks_map _ w.symm,
    eqToHom_app_fiberPullbackHom p (left_comm_of_comm i f a b w)]
  simp only [fiberPullbackCompIso_hom_app_fac, fiberPullback_map_fac_assoc,
    slicePullbackIso_hom_app_fac, choiceOfPullbacks_pullbackFunctorCompIso_inv_app_fac]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (chosenPullbacks (p.sliceAtTerminal hT)).map b z)
      (slicePullbackIso_inv_app_fac p hT hp f _))).symm

include hp in
/-- **Condition (RS) is insensitive to slicing at a terminal object.** For a category fibred in
groupoids `p` over `C` and a terminal object `T`, the comparison functor of a commutative square of
the slice `C/T`, for `p` read over the slice and its chosen pullbacks, is an equivalence as soon as
the comparison functor of the underlying square of `C` is. -/
theorem isEquivalence_fiberSquareComparison_sliceAtTerminal
    (h : letI : p.IsFibered := hp.isFibered
      (fiberSquareRestriction p i.left f.left a.left b.left
        (left_comm_of_comm i f a b w)).IsEquivalence) :
    letI : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
    (Deformation.Artin.fiberSquareComparison (p.sliceAtTerminal hT)
      (chosenPullbacks (p.sliceAtTerminal hT)) f i b a w.symm).IsEquivalence := by
  let : (p.sliceAtTerminal hT).IsFibered := (hp.sliceAtTerminal hT).isFibered
  let : p.IsFibered := hp.isFibered
  let Φ := CategoricalPullback.map ((chosenPullbacks (p.sliceAtTerminal hT)).pullbackFunctor f)
    ((chosenPullbacks (p.sliceAtTerminal hT)).pullbackFunctor i) (sliceFiberFunctor p hT Y)
    (sliceFiberFunctor p hT X') (sliceFiberFunctor p hT X) (fiberPullback p f.left)
    (fiberPullback p i.left) (slicePullbackIso p hT hp i).symm (slicePullbackIso p hT hp f)
  have : Φ.IsEquivalence :=
    induced_isEquivalence_of_isEquivalence (sliceFiberFunctor p hT Y) (sliceFiberFunctor p hT X')
      (sliceFiberFunctor p hT X) _ _
  let θ : Deformation.Artin.fiberSquareComparison (p.sliceAtTerminal hT)
      (chosenPullbacks (p.sliceAtTerminal hT)) f i b a w.symm ⋙ Φ ≅
      sliceFiberFunctor p hT Y' ⋙ fiberSquareRestriction p i.left f.left a.left b.left
        (left_comm_of_comm i f a b w) :=
    NatIso.ofComponents
      (fun z => CategoricalPullback.mkIso ((slicePullbackIso p hT hp b).app z)
        ((slicePullbackIso p hT hp a).app z) (sliceSquare_coherence p hT hp i f a b w z))
      (fun {z z'} φ => by
        apply CategoricalPullback.hom_ext
        · exact (slicePullbackIso p hT hp b).hom.naturality φ
        · exact (slicePullbackIso p hT hp a).hom.naturality φ)
  have : (sliceFiberFunctor p hT Y' ⋙ fiberSquareRestriction p i.left f.left a.left b.left
      (left_comm_of_comm i f a b w)).IsEquivalence := inferInstance
  have := Functor.isEquivalence_of_iso θ.symm
  exact Functor.isEquivalence_of_comp_right _ Φ

end Square

end CategoryTheory.Functor

namespace AlgebraicGeometry

open CategoryTheory.Functor

universe u

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **`𝒫olarized` satisfies condition (RS*)** (Stacks 07Y8), by Stacks 0D44: at a pushout square
of affine schemes along a first-order thickening, the comparison functor of fibre categories is an
equivalence. This is the first step of the proof of Stacks 0D4S. -/
theorem satisfiesRSStar_polarizedSliceProjection :
    Deformation.Artin.SatisfiesRSStar B S hS (polarizedSliceProjection B hS hT)
      ((polarizedProjection_isFiberedInGroupoids_unconditional).sliceAtTerminal hT) := by
  refine Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine B S hS
    _ _ fun {X X' Y Y'} i f a b w hX hX' hY hY' hfirst hpush => ?_
  have : IsAffine (B.inclusion.obj X.left) := hX
  have : IsAffine (B.inclusion.obj Y.left) := hY
  exact isEquivalence_fiberSquareComparison_sliceAtTerminal (polarizedProjection B) hT
    polarizedProjection_isFiberedInGroupoids_unconditional i f a b w
    (isEquivalence_polarizedPushoutRestriction B i.left f.left a.left b.left
      (left_comm_of_comm i f a b w) hpush.flip hfirst.isThickening)

end AlgebraicGeometry

end
