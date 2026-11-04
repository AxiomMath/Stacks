module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.Deformation.Artin.SquareZeroDifference
public import StacksFrontier.Deformation.TangentSpace.LinearFunctor

/-!
# The tangent functor of an object of a category satisfying (RS*)

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `A` be
an `S`-algebra whose spectrum lies in the site, and let `x` be an object of `𝒳` over
`Spec A`. For an `A`-module `M` write `A[M]` for the trivial square-zero extension of `A` by
`M`. The *tangent functor* `T_x` sends `M` to the set of isomorphism classes of lifts of `x`
to `Spec A[M]`.

If `𝒳` satisfies the Rim–Schlessinger condition (RS*), this set-valued functor preserves
finite products — the product of two modules has `A[M × N] = A[M] ×_A A[N]`, which is a
fibre-product square to which (RS*) applies — and takes the zero module to a singleton. By
Stacks 06I6 it therefore carries a unique `A`-linear module structure, functorially in `M`.
That linear functor is the tangent functor.

## Main definitions

* `Deformation.Artin.squareZeroRing` — the trivial square-zero extension `A[M]`, as a
  commutative ring in the site's universe.
* `Deformation.Artin.IsSiteModule`, `Deformation.Artin.SiteModule` — the `A`-modules whose
  trivial square-zero extension occurs in the chosen big fppf site, and the resulting full
  subcategory of `Mod_A`.
* `Deformation.Artin.algebraOver`, `Deformation.Artin.squareZeroOver` — `Spec A` and
  `Spec A[M]` as objects over `S` in the site, `Deformation.Artin.squareZeroArrow` the
  square-zero closed immersion between them, and
  `Deformation.Artin.squareZeroOverMap` its functoriality in `M`.
* `Deformation.Artin.squareZeroLiftClasses` — the isomorphism classes of lifts of `x` to
  `Spec A[M]`.
* `Deformation.Artin.IsCanonicalLiftTransition`,
  `Deformation.Artin.IsPullbackOfSquareZeroLift` — the two descriptions of the transition
  between lift classes along a module map, by a cartesian arrow over the induced map of
  square-zero extensions.
* `Deformation.Artin.TangentFunctorData` — an `A`-linear functor on `SiteModule A B`
  together with bijections of its values with the lift classes, natural for those
  transitions.
* `Deformation.Artin.tangentFunctor` — the chosen tangent functor.

## Main results

* `Deformation.Artin.exists_tangentFunctor` — **Stacks 07Y9**, the tangent functor exists.
* `Deformation.Artin.nonempty_tangentFunctorData_of_bijective` — the tangent functor exists as
  soon as restriction of lift classes to the two factors of `A[M × N]` is bijective.

## Implementation notes

The base category is the chosen big fppf site over `S`. A module is admitted only when its
trivial square-zero extension lies in that site; this is the module category implicit in the
source's standing site convention, and it is closed under finite products and contains the
zero module because the site's cutoff is an uncountable strong prelimit.

The source's *set* of lifts is the quotient of its category of lifts by isomorphism. Lifts
are taken in the fibre of `Under.post p` over the square-zero arrow, which records the
identification with `x` after restriction; that fibre is compared with the iso-fibre of a
chosen pullback functor, `CategoryTheory.Functor.IsoFiber`, which is the form in which (RS*)
is available. The comparison is a fully faithful functor which is surjective on objects, so
it is a bijection on isomorphism classes.

Finite-product preservation is proved on the two generating shapes. For a binary product,
the square `A[M × N] = A[M] ×_A A[N]` of trivial square-zero extensions is a pullback of
rings whose right-hand map is the surjection `A[N] → A` with square-zero kernel, so (RS*)
applies and `Deformation.Artin.exists_squareZeroLiftEquivalence` identifies the lifts over
`A[M × N]` with pairs of lifts. For the terminal shape, the square-zero arrow of the zero
module is an isomorphism, so lifts along it are unique up to isomorphism and there is exactly
one class.

The linear structure is then supplied by `Deformation.LinearFunctorLift.linearFunctorLift`
for the general preadditive linear source category, and the resulting module is transported
into the universe `max (u+1) v w` of the lift classes by `Shrink`, which is legitimate
because the lift classes are small in that universe.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/- The goals below are stated in terms of fibres of structure functors, their inclusions and
their induced functors, and of chosen pullback functors; those spellings are built from
definitions that the `implicit` transparency level does not unfold, so the ordinary tactics
decline to act on them. Naming the unfolding chain here is what makes the goals type-correct
at that level. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Under.post

universe u v w

namespace Deformation.Artin

/-! ### Transporting a module-valued functor into a smaller universe -/

section Shrink

variable {R : Type*} [CommRing R] {C : Type*} [Category C]

/-- A module-valued functor all of whose values are small in a universe is isomorphic to one
with values in that universe. -/
private def shrinkModuleFunctor (F : C ⥤ ModuleCat.{v} R) [∀ X, Small.{w} (F.obj X)] :
    C ⥤ ModuleCat.{w} R where
  obj X := ModuleCat.of R (Shrink.{w} (F.obj X))
  map {X Y} f := ModuleCat.ofHom
    (((Shrink.linearEquiv R (F.obj Y)).symm.toLinearMap.comp (F.map f).hom).comp
      (Shrink.linearEquiv R (F.obj X)).toLinearMap)
  map_id X := by ext x; simp
  map_comp f g := by ext x; simp

private theorem shrinkModuleFunctor_additive [Preadditive C] (F : C ⥤ ModuleCat.{v} R)
    [∀ X, Small.{w} (F.obj X)] [F.Additive] : (shrinkModuleFunctor F).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    simp only [shrinkModuleFunctor, Functor.map_add, ModuleCat.hom_add, ModuleCat.hom_ofHom,
      LinearMap.comp_add, LinearMap.add_comp]
    rfl

private theorem shrinkModuleFunctor_linear [Preadditive C] [Linear R C]
    (F : C ⥤ ModuleCat.{v} R) [∀ X, Small.{w} (F.obj X)] [F.Linear R] :
    (shrinkModuleFunctor F).Linear R where
  map_smul := by
    intro X Y f r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp only [shrinkModuleFunctor, Functor.map_smul]
    change (Shrink.linearEquiv R (F.obj Y)).symm
        (r • (F.map f).hom ((Shrink.linearEquiv R (F.obj X)) z)) =
      r • (Shrink.linearEquiv R (F.obj Y)).symm
        ((F.map f).hom ((Shrink.linearEquiv R (F.obj X)) z))
    exact (Shrink.linearEquiv R (F.obj Y)).symm.map_smul r _

end Shrink

/-! ### Lifts under an object as a fibred category -/

section UnderPost

open Functor

variable {C : Type u} [Category C] {X : Type v} [Category X]

/-- Slices under an object, over slices under its image: the lifts of `x` along the arrows of
the base out of `p x` form a fibred category over those arrows. -/
public theorem underPost_isFibered (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) (x : X) :
    (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := by
  let q : Under x ⥤ Under (p.obj x) := Under.post p
  let : p.IsFibered := hp.isFibered
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  dsimp [Under.post] at f
  obtain ⟨y, ψ, hψ⟩ := hp.exists_lift f.right a.right rfl
  have hy := IsHomLift.domain_eq p f.right ψ
  have hψ' : eqToHom hy.symm ≫ p.map ψ = f.right := by
    rw [IsHomLift.fac' p f.right ψ]
    simp
  have hcomp : (R.hom ≫ eqToHom hy.symm) ≫ p.map ψ = p.map a.hom := by
    rw [Category.assoc, hψ']
    exact Under.w f
  obtain ⟨χ, ⟨hχ, hχcomp⟩, hχuniq⟩ := hp.unique_lift ψ a.hom (R.hom ≫ eqToHom hy.symm) hcomp
  let b : Under x := Under.mk χ
  let φ : b ⟶ a := Under.homMk ψ hχcomp
  have hb : q.obj b = R := StructuredArrow.obj_ext _ _ hy (by
    change p.map χ ≫ eqToHom hy = R.hom
    rw [hχ]
    simp [Category.assoc])
  have hbr : p.obj y = R.right := hy
  have hbase : p.map ψ = eqToHom hbr ≫ f.right := by
    simpa [Category.assoc] using congrArg (fun k => eqToHom hbr ≫ k) hψ'
  have hφ : q.IsHomLift f φ := by
    refine IsHomLift.of_fac' q f φ hb rfl ?_
    apply Under.UnderMorphism.ext
    simp only [Under.comp_right, Under.eqToHom_right]
    have hbr' : (by rw [hb] : (q.obj b).right = R.right) = hbr := Subsingleton.elim _ _
    simpa [q, b, φ, Under.post, hbr'] using hbase
  refine ⟨b, φ, { toIsHomLift := hφ, universal_property' := ?_ }⟩
  intro R' b' g hφ'
  have hgbase : p.map g.right = b'.right ≫ f.right := by
    let : q.IsHomLift (b' ≫ f) g := hφ'
    have heq' := congrArg Under.Hom.right (IsHomLift.eq_of_isHomLift q (b' ≫ f) g)
    simp only [Under.comp_right] at heq'
    simpa [q, Under.post] using heq'.symm
  have hfac : (b'.right ≫ eqToHom hy.symm) ≫ p.map ψ = p.map g.right := by
    rw [Category.assoc, hψ', hgbase]
  obtain ⟨χ', ⟨hχ'map, hχ'comp⟩, hχ'unique⟩ :=
    hp.unique_lift ψ g.right (b'.right ≫ eqToHom hy.symm) hfac
  have hunder : R'.hom ≫ χ' = χ := by
    refine hχuniq _ ⟨?_, ?_⟩
    · calc
        p.map (R'.hom ≫ χ') = p.map R'.hom ≫ p.map χ' := Functor.map_comp p _ _
        _ = p.map R'.hom ≫ b'.right ≫ eqToHom hy.symm := by rw [hχ'map]
        _ = (p.map R'.hom ≫ b'.right) ≫ eqToHom hy.symm := (Category.assoc _ _ _).symm
        _ = R.hom ≫ eqToHom hy.symm := by
          rw [show p.map R'.hom ≫ b'.right = R.hom by simpa [q, Under.post] using Under.w b']
    · calc
        (R'.hom ≫ χ') ≫ ψ = R'.hom ≫ g.right := by rw [Category.assoc, hχ'comp]
        _ = a.hom := Under.w g
  let χ₀ : R' ⟶ b := Under.homMk χ' hunder
  have hχlift : q.IsHomLift b' χ₀ := by
    refine IsHomLift.of_fac' q b' χ₀ rfl hb ?_
    apply Under.UnderMorphism.ext
    simp only [Under.comp_right, Under.eqToHom_right, eqToHom_refl, Category.id_comp]
    exact hχ'map
  refine ⟨χ₀, ⟨hχlift, Under.UnderMorphism.ext hχ'comp⟩, ?_⟩
  intro χ'' hχ''
  apply Under.UnderMorphism.ext
  refine hχ'unique χ''.right ⟨?_, ?_⟩
  · obtain ⟨hχ''lift, -⟩ := hχ''
    let : q.IsHomLift b' χ'' := hχ''lift
    have hh := congrArg Under.Hom.right (IsHomLift.fac' q b' χ'')
    simp only [Under.comp_right, Under.eqToHom_right, eqToHom_refl, Category.id_comp] at hh
    exact hh
  · obtain ⟨-, hχ''comp⟩ := hχ''
    simpa [φ] using congrArg Under.Hom.right hχ''comp

/-- A morphism of slices lying over a morphism of base slices lies, on the right-hand
components, over its right-hand component. -/
public theorem underPost_isHomLift_right (p : X ⥤ C) {x : X} {a b : Under x}
    {U V : Under (p.obj x)} (f : U ⟶ V) (φ : a ⟶ b)
    (h : (Under.post p).IsHomLift f φ) : p.IsHomLift f.right φ.right := by
  cases h
  exact IsHomLift.map p φ.right

/-- A morphism of slices lies over a morphism of base slices as soon as its right-hand component
lies over the right-hand component. -/
private theorem underPost_isHomLift_of_right (p : X ⥤ C) {x : X} {a b : Under x}
    {U V : Under (p.obj x)} (f : U ⟶ V) (φ : a ⟶ b) (ha : (Under.post p).obj a = U)
    (hb : (Under.post p).obj b = V) (h : p.IsHomLift f.right φ.right) :
    (Under.post p).IsHomLift f φ := by
  refine IsHomLift.of_fac' _ _ _ ha hb (Under.UnderMorphism.ext ?_)
  simp only [Under.comp_right, Under.eqToHom_right]
  exact IsHomLift.fac' p f.right φ.right

/-- A morphism of slices is invertible as soon as its right-hand component is. -/
private theorem isIso_of_isIso_right {Y : Type*} [Category Y] {y : Y} {a b : Under y} (m : a ⟶ b)
    [IsIso m.right] : IsIso m :=
  have : IsIso ((Under.forget y).map m) := ‹IsIso m.right›
  isIso_of_reflects_iso m (Under.forget y)

/-- The lifts of `x` along the arrows of the base out of `p x` form a category fibred in
groupoids over those arrows. -/
public theorem underPost_isFiberedInGroupoids (p : X ⥤ C) (hp : p.IsFiberedInGroupoids)
    (x : X) : (Under.post p : Under x ⥤ Under (p.obj x)).IsFiberedInGroupoids := by
  have : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  apply Functor.IsFiberedInGroupoids.mk'
  intro U
  refine ⟨?_⟩
  intro a b m
  have : p.IsHomLift (𝟙 U.right) m.1.right := underPost_isHomLift_right p _ _ m.2
  have : p.IsStronglyCartesian (𝟙 U.right) m.1.right := hp.isStronglyCartesian_homLift _ _
  have : IsIso m.1.right := Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 U.right) _
  have : IsIso m.1 := isIso_of_isIso_right m.1
  have he : (Functor.Fiber.isoMk (asIso m.1) m.2).hom = m := rfl
  rw [← he]
  infer_instance

private theorem isCartesian_over_image (p : X ⥤ C) {a b : X} {U V : C} (f : U ⟶ V)
    (φ : a ⟶ b) (h : p.IsCartesian f φ) : p.IsCartesian (p.map φ) φ := by
  have := h
  subst_hom_lift p f φ
  exact h

end UnderPost

/-! ### The iso-fibre of a pullback functor and the fibre of lifts -/

section LiftComparison

open Functor

variable {C : Type u} [Category C] {D : Type v} [Category D]
  (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
  {U V : C} (f : U ⟶ V) (x : p.Fiber U)

/-- The arrow of `D` over `f` attached to an object of the iso-fibre of `f^*` over `x`. -/
public def isoFiberArrow (t : Functor.IsoFiber (c.pullbackFunctor f) x) : x.1 ⟶ t.obj.left.1 :=
  have : IsIso t.obj.hom := t.property
  Fiber.fiberInclusion.map (inv t.obj.hom) ≫ c.map f t.obj.left

/-- The arrow attached to an object of the iso-fibre lies over `f`. -/
public theorem isoFiberArrow_isHomLift (t : Functor.IsoFiber (c.pullbackFunctor f) x) :
    p.IsHomLift f (isoFiberArrow p c f x t) := by
  have : IsIso t.obj.hom := t.property
  have h : p.IsHomLift (𝟙 U ≫ f)
      (Fiber.fiberInclusion.map (inv t.obj.hom) ≫ c.map f t.obj.left) := inferInstance
  simpa only [Category.id_comp, isoFiberArrow] using h

/-- The lift of `x` along `f` attached to an object of the iso-fibre of `f^*` at `x`. -/
public def isoFiberToUnderObj (t : Functor.IsoFiber (c.pullbackFunctor f) x) :
    (Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ f)) := by
  have : p.IsHomLift f (isoFiberArrow p c f x t) := isoFiberArrow_isHomLift p c f x t
  refine ⟨Under.mk (isoFiberArrow p c f x t), ?_⟩
  apply StructuredArrow.obj_ext _ _ t.obj.left.2
  change p.map (isoFiberArrow p c f x t) ≫ eqToHom t.obj.left.2 = eqToHom x.2 ≫ f
  rw [IsHomLift.fac' p f (isoFiberArrow p c f x t)]
  simp

/-- The arrows attached to the objects of the iso-fibre are compatible with its morphisms. -/
public theorem isoFiberArrow_naturality
    {s t : Functor.IsoFiber (c.pullbackFunctor f) x} (m : s ⟶ t) :
    isoFiberArrow p c f x s ≫ m.hom.left.1 = isoFiberArrow p c f x t := by
  have : IsIso s.obj.hom := s.property
  have : IsIso t.obj.hom := t.property
  have hm : inv s.obj.hom ≫ c.homMap f m.hom.left = inv t.obj.hom := by
    apply (cancel_mono t.obj.hom).1
    simp only [Category.assoc, IsIso.inv_hom_id]
    change inv s.obj.hom ≫ (c.pullbackFunctor f).map m.hom.left ≫ t.obj.hom = _
    rw [CostructuredArrow.w m.hom, IsIso.inv_hom_id]
  change (Fiber.fiberInclusion.map (inv s.obj.hom) ≫ c.map f s.obj.left) ≫
    Fiber.fiberInclusion.map m.hom.left = _
  rw [Category.assoc, ← c.homMap_fac, ← Category.assoc, ← Functor.map_comp, hm]
  rfl

/-- The morphism of lifts attached to a morphism of the iso-fibre. -/
public def isoFiberToUnderMap {s t : Functor.IsoFiber (c.pullbackFunctor f) x} (m : s ⟶ t) :
    isoFiberToUnderObj p c f x s ⟶ isoFiberToUnderObj p c f x t := by
  refine ⟨Under.homMk m.hom.left.1 (isoFiberArrow_naturality p c f x m),
    IsHomLift.of_fac' _ _ _ (isoFiberToUnderObj p c f x s).2
      (isoFiberToUnderObj p c f x t).2 ?_⟩
  apply Under.UnderMorphism.ext
  change p.map m.hom.left.1 = _
  have : p.IsHomLift (𝟙 V) m.hom.left.1 := m.hom.left.2
  simp only [Under.comp_right, Under.eqToHom_right, Under.id_right]
  exact IsHomLift.fac' p (𝟙 V) m.hom.left.1

/-- The comparison from the iso-fibre of the pullback functor along `f` at `x` to the fibre
of lifts of `x` along `f`. -/
public def isoFiberToUnder : Functor.IsoFiber (c.pullbackFunctor f) x ⥤
    (Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ f)) where
  obj := isoFiberToUnderObj p c f x
  map := isoFiberToUnderMap p c f x
  map_id _ := by apply Fiber.hom_ext; apply Under.UnderMorphism.ext; rfl
  map_comp _ _ := by apply Fiber.hom_ext; apply Under.UnderMorphism.ext; rfl

/-- The comparison to the fibre of lifts is faithful. -/
public theorem isoFiberToUnder_faithful : (isoFiberToUnder p c f x).Faithful where
  map_injective {s t} m n h := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Fiber.hom_ext
    exact congrArg (fun k => k.1.right) h

/-- The comparison to the fibre of lifts is full. -/
public theorem isoFiberToUnder_full : (isoFiberToUnder p c f x).Full where
  map_surjective {s t} φ := by
    have : IsIso s.obj.hom := s.property
    have : IsIso t.obj.hom := t.property
    let m : s.obj.left ⟶ t.obj.left := ⟨φ.1.right, underPost_isHomLift_right p _ _ φ.2⟩
    have he : inv s.obj.hom ≫ c.homMap f m = inv t.obj.hom := by
      apply fiber_hom_ext_of_cartesian f (c.map f t.obj.left) inferInstance
      rw [Functor.map_comp, Category.assoc, c.homMap_fac, ← Category.assoc]
      exact Under.w φ.1
    have hm : (c.pullbackFunctor f).map m ≫ t.obj.hom = s.obj.hom := by
      calc
        (c.pullbackFunctor f).map m ≫ t.obj.hom =
            s.obj.hom ≫ (inv s.obj.hom ≫ c.homMap f m) ≫ t.obj.hom := by simp
        _ = s.obj.hom := by rw [he]; simp
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk m hm), ?_⟩
    apply Fiber.hom_ext
    apply Under.UnderMorphism.ext
    rfl

private theorem underFiber_isHomLift (a : (Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ f))) :
    p.IsHomLift f a.1.hom := by
  have hy : p.obj a.1.right = V := congrArg Under.right a.2
  apply IsHomLift.of_fac p f a.1.hom x.2 hy
  have hw := Under.w (eqToHom a.2)
  simp only [Under.eqToHom_right] at hw
  change p.map a.1.hom ≫ eqToHom hy = eqToHom x.2 ≫ f at hw
  rw [hw]
  simp

include hp in
/-- The comparison to the fibre of lifts is surjective on objects. -/
public theorem isoFiberToUnder_surjective :
    Function.Surjective (isoFiberToUnder p c f x).obj := by
  intro a
  let y : p.Fiber V := ⟨a.1.right, congrArg Under.right a.2⟩
  have ha : p.IsHomLift f a.1.hom := underFiber_isHomLift p f x a
  have hc : p.IsCartesian f a.1.hom :=
    (hp.isStronglyCartesian_homLift f a.1.hom).isCartesian_of_isStronglyCartesian
  let e : c.obj f y ≅ x := fiberIsoOfCartesian f (c.map f y) a.1.hom inferInstance hc
  let t₀ : Functor.IsoFiber (c.pullbackFunctor f) x :=
    ⟨CostructuredArrow.mk e.hom, show IsIso e.hom from inferInstance⟩
  refine ⟨t₀, ?_⟩
  apply Subtype.ext
  refine (StructuredArrow.obj_ext _ a.1 rfl ?_)
  change isoFiberArrow p c f x t₀ ≫ 𝟙 _ = a.1.hom
  dsimp [t₀, isoFiberArrow]
  simp only [Category.comp_id]
  rw [show inv e.hom = e.inv from IsIso.inv_eq_of_hom_inv_id e.hom_inv_id]
  exact fiberIsoOfCartesian_inv_fac f (c.map f y) a.1.hom inferInstance hc

/-- The map on isomorphism classes induced by a functor. -/
public def isoClassMap {E : Type*} [Category E] {F : Type*} [Category F] (G : E ⥤ F) :
    Quotient (isIsomorphicSetoid E) → Quotient (isIsomorphicSetoid F) :=
  Quotient.map G.obj (fun _ _ ⟨e⟩ => ⟨G.mapIso e⟩)

/-- A fully faithful functor which is surjective on objects induces a bijection on
isomorphism classes. -/
public theorem isoClassMap_bijective {E : Type*} [Category E] {F : Type*} [Category F]
    (G : E ⥤ F) [G.Full] [G.Faithful] (hG : Function.Surjective G.obj) :
    Function.Bijective (isoClassMap G) := by
  constructor
  · intro a b
    induction a using Quotient.ind with
    | _ a =>
      induction b using Quotient.ind with
      | _ b =>
        intro h
        obtain ⟨e⟩ := Quotient.exact h
        exact Quotient.sound ⟨G.preimageIso e⟩
  · intro a
    induction a using Quotient.ind with
    | _ a =>
      obtain ⟨b, rfl⟩ := hG a
      exact ⟨Quotient.mk _ b, rfl⟩

include hp in
/-- Isomorphism classes of lifts of `x` along `f` are the isomorphism classes of the
iso-fibre of the pullback functor along `f`. -/
public def isoFiberUnderClassesEquiv :
    Quotient (isIsomorphicSetoid (Functor.IsoFiber (c.pullbackFunctor f) x)) ≃
      Quotient (isIsomorphicSetoid
        ((Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ f)))) := by
  have := isoFiberToUnder_full p c f x
  have := isoFiberToUnder_faithful p c f x
  exact Equiv.ofBijective (isoClassMap (isoFiberToUnder p c f x))
    (isoClassMap_bijective _ (isoFiberToUnder_surjective p hp c f x))

/-- Restriction of an object of the iso-fibre along a factorization of the base arrow. -/
public def isoFiberRestrict {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k)
    (t : Functor.IsoFiber (c.pullbackFunctor k) x) :
    Functor.IsoFiber (c.pullbackFunctor f) x :=
  have : IsIso t.obj.hom := t.property
  ⟨CostructuredArrow.mk ((c.objCompIso f i t.obj.left).inv ≫
      eqToHom (congrArg (fun l => c.obj l t.obj.left) h) ≫ t.obj.hom),
    show IsIso ((c.objCompIso f i t.obj.left).inv ≫
      eqToHom (congrArg (fun l => c.obj l t.obj.left) h) ≫ t.obj.hom) from inferInstance⟩

/-- The base arrow of the restriction map on lifts. -/
public def underBaseMap {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k) :
    Under.mk (eqToHom x.2 ≫ f) ⟶ Under.mk (eqToHom x.2 ≫ k) :=
  Under.homMk i (by simp [Category.assoc, h])

/-- Restriction is compatible with the arrows out of `x`: the arrow of the restricted lift,
followed by the chosen pullback of `i`, is the arrow of the original lift. -/
public theorem isoFiberRestrict_fac {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k)
    (t : Functor.IsoFiber (c.pullbackFunctor k) x) :
    isoFiberArrow p c f x (isoFiberRestrict p c f x i k h t) ≫ c.map i t.obj.left =
      isoFiberArrow p c k x t := by
  subst k
  have : IsIso t.obj.hom := t.property
  change (Fiber.fiberInclusion.map
    (inv ((c.objCompIso f i t.obj.left).inv ≫ 𝟙 _ ≫ t.obj.hom)) ≫
      c.map f (c.obj i t.obj.left)) ≫ c.map i t.obj.left =
    Fiber.fiberInclusion.map (inv t.obj.hom) ≫ c.map (f ≫ i) t.obj.left
  have hi : inv (c.objCompIso f i t.obj.left).inv = (c.objCompIso f i t.obj.left).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    simp
  simp only [Category.id_comp, IsIso.inv_comp, hi, Functor.map_comp, Category.assoc,
    c.objCompIso_hom_fac]

include hp in
/-- On isomorphism classes of lifts, restriction along `i` is the map induced by the base
arrow `underBaseMap`. -/
public theorem isoFiberRestrict_class {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k)
    (t : Functor.IsoFiber (c.pullbackFunctor k) x) :
    letI : (Under.post p : Under x.1 ⥤ Under (p.obj x.1)).IsFibered :=
      underPost_isFibered p hp x.1
    (Under.post p).isoClassPresheaf.map (underBaseMap p f x i k h).op
      (Quotient.mk _ (isoFiberToUnderObj p c k x t)) =
        Quotient.mk _ (isoFiberToUnderObj p c f x (isoFiberRestrict p c f x i k h t)) := by
  let : (Under.post p : Under x.1 ⥤ Under (p.obj x.1)).IsFibered := underPost_isFibered p hp x.1
  let φ : (isoFiberToUnderObj p c f x (isoFiberRestrict p c f x i k h t)).1 ⟶
      (isoFiberToUnderObj p c k x t).1 :=
    Under.homMk (c.map i t.obj.left) (isoFiberRestrict_fac p c f x i k h t)
  have hφ : (Under.post p).IsHomLift (underBaseMap p f x i k h) φ :=
    underPost_isHomLift_of_right p _ _ (isoFiberToUnderObj p c f x _).2
      (isoFiberToUnderObj p c k x t).2
        (by change p.IsHomLift i (c.map i t.obj.left); infer_instance)
  have hc := (underPost_isFiberedInGroupoids p hp x.1).isStronglyCartesian_homLift
    (underBaseMap p f x i k h) φ
  exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian _ _ _ φ hφ
    hc.isCartesian_of_isStronglyCartesian).symm

private def isoClassesEquiv {E F : Type*} [Category E] [Category F] (e : E ≌ F) :
    Quotient (isIsomorphicSetoid E) ≃ Quotient (isIsomorphicSetoid F) where
  toFun := isoClassMap e.functor
  invFun := isoClassMap e.inverse
  left_inv a := by
    induction a using Quotient.ind with
    | _ a => exact Quotient.sound ⟨(e.unitIso.app a).symm⟩
  right_inv a := by
    induction a using Quotient.ind with
    | _ a => exact Quotient.sound ⟨e.counitIso.app a⟩

private def isoClassesProdEquiv (E F : Type*) [Category E] [Category F] :
    Quotient (isIsomorphicSetoid (E × F)) ≃
      Quotient (isIsomorphicSetoid E) × Quotient (isIsomorphicSetoid F) where
  toFun := Quotient.lift (fun a => (Quotient.mk _ a.1, Quotient.mk _ a.2)) (by
    intro a b ⟨e⟩
    exact Prod.ext (Quotient.sound ⟨(CategoryTheory.Prod.fst E F).mapIso e⟩)
      (Quotient.sound ⟨(CategoryTheory.Prod.snd E F).mapIso e⟩))
  invFun a := Quotient.liftOn₂ a.1 a.2 (fun b c => Quotient.mk _ (b, c)) (by
    intro a b c d ⟨e⟩ ⟨e'⟩
    exact Quotient.sound ⟨{
      hom := (e.hom, e'.hom)
      inv := (e.inv, e'.inv)
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }⟩)
  left_inv a := by induction a using Quotient.ind; rfl
  right_inv a := by
    obtain ⟨a, b⟩ := a
    induction a using Quotient.ind
    induction b using Quotient.ind
    rfl

include hp in
/-- Given the (RS*) equivalence of iso-fibres, restriction along the two legs of the square
is a bijection from the lift classes over the fourth corner to pairs of lift classes. -/
public theorem underClassPair_bijective {W Z : C}
    (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (k : U ⟶ Z) (hk : f ≫ i = k)
    (e : Functor.IsoFiber (c.pullbackFunctor (f ≫ i)) x ≌
      (Functor.IsoFiber (c.pullbackFunctor f) x ×
        Functor.IsoFiber (c.pullbackFunctor g) x))
    (he : ∀ t,
      (e.functor.obj t).1 = isoFiberRestrict p c f x i (f ≫ i) rfl t ∧
      (e.functor.obj t).2 = isoFiberRestrict p c g x j (f ≫ i) h.symm t) :
    letI : (Under.post p : Under x.1 ⥤ Under (p.obj x.1)).IsFibered :=
      underPost_isFibered p hp x.1
    Function.Bijective (fun a =>
      ((Under.post p).isoClassPresheaf.map (underBaseMap p f x i k hk).op a,
       (Under.post p).isoClassPresheaf.map
         (underBaseMap p g x j k (h.symm.trans hk)).op a)) := by
  subst k
  let : (Under.post p : Under x.1 ⥤ Under (p.obj x.1)).IsFibered := underPost_isFibered p hp x.1
  let e₀ := isoFiberUnderClassesEquiv p hp c (f ≫ i) x
  let e₁ := isoFiberUnderClassesEquiv p hp c f x
  let e₂ := isoFiberUnderClassesEquiv p hp c g x
  let e' := (isoClassesEquiv e).trans
    ((isoClassesProdEquiv _ _).trans (Equiv.prodCongr e₁ e₂))
  have hh : (fun a =>
      ((Under.post p).isoClassPresheaf.map (underBaseMap p f x i (f ≫ i) rfl).op a,
       (Under.post p).isoClassPresheaf.map
         (underBaseMap p g x j (f ≫ i) h.symm).op a)) ∘ e₀ = e' := by
    funext a
    induction a using Quotient.ind with
    | _ a =>
      change (_, _) = (Quotient.mk _ (isoFiberToUnderObj p c f x (e.functor.obj a).1),
        Quotient.mk _ (isoFiberToUnderObj p c g x (e.functor.obj a).2))
      rw [(he a).1, (he a).2]
      exact Prod.ext (isoFiberRestrict_class p hp c f x i _ rfl a)
        (isoFiberRestrict_class p hp c g x j _ h.symm a)
  exact (Function.Bijective.of_comp_iff _ e₀.bijective).mp (hh.symm ▸ e'.bijective)

include c in
private theorem underClasses_nonempty [IsIso f] :
    Nonempty (Quotient (isIsomorphicSetoid
      ((Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ f))))) := by
  let y := c.obj (inv f) x
  let ψ := c.map (inv f) x
  have : IsIso ψ := IsStronglyCartesian.isIso_of_base_isIso p (inv f) ψ
  have hi : p.IsHomLift f (inv ψ) := by
    simpa using (IsHomLift.inv (p := p) (f := inv f) (φ := ψ))
  have hy : (Under.post p).obj (Under.mk (inv ψ)) = Under.mk (eqToHom x.2 ≫ f) := by
    apply StructuredArrow.obj_ext _ _ y.2
    change p.map (inv ψ) ≫ eqToHom y.2 = eqToHom x.2 ≫ f
    rw [IsHomLift.fac' p f (inv ψ)]
    simp
  exact ⟨Quotient.mk _ ⟨Under.mk (inv ψ), hy⟩⟩

include hp in
private theorem underClasses_subsingleton [IsIso f] :
    Subsingleton (Quotient (isIsomorphicSetoid
      ((Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ f))))) := by
  constructor
  intro a b
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      have : p.IsHomLift f a.1.hom := underFiber_isHomLift p f x a
      have : p.IsHomLift f b.1.hom := underFiber_isHomLift p f x b
      have : p.IsStronglyCartesian f a.1.hom := hp.isStronglyCartesian_homLift _ _
      have : p.IsStronglyCartesian f b.1.hom := hp.isStronglyCartesian_homLift _ _
      have : IsIso a.1.hom := IsStronglyCartesian.isIso_of_base_isIso p f _
      have : IsIso b.1.hom := IsStronglyCartesian.isIso_of_base_isIso p f _
      let φ : a.1 ⟶ b.1 := Under.homMk (inv a.1.hom ≫ b.1.hom) (by simp)
      have hφ : (Under.post p).IsHomLift (𝟙 (Under.mk (eqToHom x.2 ≫ f))) φ := by
        have hi : p.IsHomLift (𝟙 V) φ.right := by
          have hh : p.IsHomLift (inv f ≫ f) (inv a.1.hom ≫ b.1.hom) := inferInstance
          simpa only [IsIso.inv_hom_id, φ, Under.homMk_right] using hh
        exact underPost_isHomLift_of_right p _ _ a.2 b.2 hi
      have : IsIso φ.right := by
        change IsIso (inv a.1.hom ≫ b.1.hom)
        infer_instance
      have : IsIso φ := isIso_of_isIso_right φ
      exact Quotient.sound ⟨Fiber.isoMk (asIso φ) hφ⟩

end LiftComparison

/-! ### Modules in the site and their trivial square-zero extensions -/

section SiteModules

variable (A : Type u) [CommRing A]

/-- The induced right action of a commutative ring on one of its modules: the shared
`Module.oppositeOfCommSemiring`, so that it agrees at instance transparency with local
instances written using that same construction. -/
@[instance_reducible] public instance oppositeModule (M : ModuleCat.{u} A) : Module Aᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring A M

/-- Over a commutative ring the left and right actions on a module agree. -/
public instance centralScalar (M : ModuleCat.{u} A) : IsCentralScalar A M :=
  Module.isCentralScalar_oppositeOfCommSemiring A M

/-- The commutative ring `A[M]` of the trivial square-zero extension of `A` by `M`. -/
public def squareZeroRing (M : ModuleCat.{u} A) : CommRingCat.{u} :=
  .of (TrivSqZeroExt A M)

private theorem mk_le_squareZeroRing (M : ModuleCat.{u} A) :
    Cardinal.mk (M : Type u) ≤ Cardinal.mk (squareZeroRing A M) := by
  change Cardinal.mk (M : Type u) ≤ Cardinal.mk (A × (M : Type u))
  exact Cardinal.mk_le_of_injective (f := fun m : M => (0, m))
    (fun m n h => (Prod.mk.inj h).2)

omit [CommRing A] in
private theorem mk_squareZeroProduct_le (M N : Type u) :
    Cardinal.mk (A × (M × N)) ≤
      max Cardinal.aleph0 (max (Cardinal.mk A)
        (max (Cardinal.mk M) (Cardinal.mk N))) := by
  simp only [Cardinal.mk_prod, Cardinal.lift_id]
  calc
    Cardinal.mk A * (Cardinal.mk M * Cardinal.mk N) ≤
        max (max (Cardinal.mk A) (Cardinal.mk M * Cardinal.mk N)) Cardinal.aleph0 :=
      Cardinal.mul_le_max (Cardinal.mk A) (Cardinal.mk M * Cardinal.mk N)
    _ ≤ max (max (Cardinal.mk A)
        (max (max (Cardinal.mk M) (Cardinal.mk N)) Cardinal.aleph0)) Cardinal.aleph0 := by
      gcongr
      exact Cardinal.mul_le_max (Cardinal.mk M) (Cardinal.mk N)
    _ = max Cardinal.aleph0 (max (Cardinal.mk A)
        (max (Cardinal.mk M) (Cardinal.mk N))) := by ac_rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S)
  (hA : B.Contains (Spec (.of A)))

/-- The `A`-modules whose trivial square-zero extension occurs in the chosen big site. -/
public abbrev IsSiteModule : ObjectProperty (ModuleCat.{u} A) :=
  fun M => B.Contains (Spec (squareZeroRing A M))

/-- The module category implicit in the chosen big fppf site. -/
public abbrev SiteModule := (IsSiteModule A B).FullSubcategory

private theorem module_card_lt_cutoff (M : SiteModule A B) :
    Cardinal.mk (M.obj : Type u) < B.cutoff := by
  have hM : (Spec (squareZeroRing A M.obj)).size < B.cutoff := M.property
  rw [Scheme.size_Spec] at hM
  exact lt_of_le_of_lt (mk_le_squareZeroRing A M.obj)
    (lt_of_le_of_lt (le_max_right Cardinal.aleph0
      (Cardinal.mk (squareZeroRing A M.obj))) hM)

include hA in
private theorem card_lt_cutoff_of_contains : Cardinal.mk A < B.cutoff := by
  have h : (Spec (.of A)).size < B.cutoff := hA
  rw [Scheme.size_Spec] at h
  exact lt_of_le_of_lt (le_max_right Cardinal.aleph0 (Cardinal.mk A)) h

include hA in
/-- The product of two site modules is a site module. -/
public theorem product_isSiteModule (M N : SiteModule A B) :
    IsSiteModule A B (ModuleCat.of A (M.obj × N.obj)) := by
  have hbound : max Cardinal.aleph0 (max (Cardinal.mk A)
      (max (Cardinal.mk (M.obj : Type u)) (Cardinal.mk (N.obj : Type u)))) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (max_lt (card_lt_cutoff_of_contains A B hA)
      (max_lt (module_card_lt_cutoff A B M) (module_card_lt_cutoff A B N)))
  have hring : Cardinal.mk (squareZeroRing A (ModuleCat.of A (M.obj × N.obj))) < B.cutoff :=
    lt_of_le_of_lt (mk_squareZeroProduct_le A (M.obj : Type u) (N.obj : Type u)) hbound
  simpa [IsSiteModule, Scheme.size_Spec] using ⟨B.aleph0_lt_cutoff, hring⟩

include hA in
/-- The zero module is a site module. -/
public theorem zero_isSiteModule : IsSiteModule A B (ModuleCat.of A PUnit.{u + 1}) := by
  have hring : Cardinal.mk (squareZeroRing A (ModuleCat.of A PUnit.{u + 1})) < B.cutoff := by
    change Cardinal.mk (A × PUnit) < B.cutoff
    rw [Cardinal.mk_congr (Equiv.prodPUnit A)]
    exact card_lt_cutoff_of_contains A B hA
  simpa [IsSiteModule, Scheme.size_Spec] using ⟨B.aleph0_lt_cutoff, hring⟩

/-- `Spec A`, as an object over `S` in the site. -/
public def algebraOver : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk toS : B.obj hA ⟶ B.obj hS)

/-- `Spec A[M]`, as an object over `S` in the site. -/
public def squareZeroOver (M : SiteModule A B) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS) :
      B.obj M.property ⟶ B.obj hS)

/-- The square-zero closed immersion `Spec A ⟶ Spec A[M]`. -/
public def squareZeroArrow (M : SiteModule A B) :
    algebraOver A B S hS toS hA ⟶ squareZeroOver A B S hS toS M := by
  refine Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom)) :
      B.obj hA ⟶ B.obj M.property) ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS = toS
  have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom =
        𝟙 (CommRingCat.of A) := by
    apply CommRingCat.hom_ext
    ext a
    simp
  rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_id, Category.id_comp]

/-- A module map induces the contravariant morphism of trivial square-zero extensions. -/
public def squareZeroOverMap {M N : SiteModule A B} (f : M ⟶ N) :
    squareZeroOver A B S hS toS N ⟶ squareZeroOver A B S hS toS M := by
  refine Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom)) :
      B.obj N.property ⟶ B.obj M.property) ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A N.obj)) ≫ toS
  have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) ≫
      CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.inlHom A N.obj) := by
    apply CommRingCat.hom_ext
    ext a
    · simp
    · change (TrivSqZeroExt.map f.hom.hom (TrivSqZeroExt.inl a)).snd =
        (TrivSqZeroExt.inl a).snd
      rw [TrivSqZeroExt.map_inl]
  rw [← Category.assoc, ← Spec.map_comp, h]

/-- The map of square-zero extension rings induced by a module homomorphism. -/
public def squareZeroRingMap {M N : SiteModule A B} (f : M ⟶ N) :
    squareZeroRing A M.obj ⟶ squareZeroRing A N.obj :=
  CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom

/-- The pair of components of `squareZeroRingMap` applied to an element of the trivial
square-zero extension. Stated with `M N` kept as the abstract site modules of this section (so
that `M.obj`, `N.obj` carry a single, consistently resolved `Module Aᵒᵖ` instance throughout):
instantiating `M` or `N` at a concrete module afterwards substitutes into this already-elaborated
statement, rather than triggering a fresh instance search at a module expression that a
discrimination tree may fail to see through. -/
public theorem squareZeroRingMap_hom_apply {M N : SiteModule A B} (f : M ⟶ N)
    (z : TrivSqZeroExt A M.obj) :
    (squareZeroRingMap A B f).hom z = (z.fst, f.hom.hom z.snd) :=
  TrivSqZeroExt.ext (TrivSqZeroExt.fst_map f.hom.hom z) (TrivSqZeroExt.snd_map f.hom.hom z)

/-- The morphism of trivial square-zero extensions attached to an identity is the identity. -/
public theorem squareZeroOverMap_id (M : SiteModule A B) :
    squareZeroOverMap A B S hS toS (𝟙 M) = 𝟙 (squareZeroOver A B S hS toS M) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (LinearMap.id : M.obj →ₗ[A] M.obj)).toRingHom) = 𝟙 _
  rw [TrivSqZeroExt.map_id]
  exact Spec.map_id _

/-- The morphisms of trivial square-zero extensions compose contravariantly. -/
public theorem squareZeroOverMap_comp {M N P : SiteModule A B} (f : M ⟶ N) (g : N ⟶ P) :
    squareZeroOverMap A B S hS toS (f ≫ g) =
      squareZeroOverMap A B S hS toS g ≫ squareZeroOverMap A B S hS toS f := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.map (g.hom.hom.comp f.hom.hom)).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map g.hom.hom).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z <;> simp

/-- The square-zero immersions are compatible with the maps of trivial square-zero
extensions induced by a module map. -/
public theorem squareZeroArrow_naturality {M N : SiteModule A B} (f : M ⟶ N) :
    squareZeroArrow A B S hS toS hA N ≫ squareZeroOverMap A B S hS toS f =
      squareZeroArrow A B S hS toS hA M := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A N.obj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  simp

end SiteModules

/-! ### The square `A[M × N] = A[M] ×_A A[N]` -/

section ProductSquare

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})

/-- The projection `A[M] ⟶ A` of a trivial square-zero extension onto its base ring. -/
@[ega "0 18.2.3" "special case"]
public abbrev squareZeroProjection (M : ModuleCat.{u} A) : squareZeroRing A M ⟶ .of A :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M).toRingHom

variable (hA : B.Contains (Spec (.of A)))

include hA in
/-- The product of two site modules, as a site module. -/
public abbrev siteModuleProd (M N : SiteModule A B) : SiteModule A B :=
  ⟨ModuleCat.of A (M.obj × N.obj), product_isSiteModule A B hA M N⟩

/-- The first projection of a product of site modules. -/
public def siteModuleFst (M N : SiteModule A B) : siteModuleProd A B hA M N ⟶ M :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.fst A M.obj N.obj))

/-- The second projection of a product of site modules. -/
public def siteModuleSnd (M N : SiteModule A B) : siteModuleProd A B hA M N ⟶ N :=
  ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.snd A M.obj N.obj))

include hA in
/-- The zero site module. -/
public abbrev siteModuleZero : SiteModule A B :=
  ⟨ModuleCat.of A PUnit.{u + 1}, zero_isSiteModule A B hA⟩

private theorem squareZeroRingProduct_isPullback (M N : SiteModule A B) :
    IsPullback (squareZeroRingMap A B (siteModuleFst A B hA M N))
      (squareZeroRingMap A B (siteModuleSnd A B hA M N))
      (squareZeroProjection A M.obj) (squareZeroProjection A N.obj) := by
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext z
    change (TrivSqZeroExt.map (LinearMap.fst A M.obj N.obj) z).fst =
      (TrivSqZeroExt.map (LinearMap.snd A M.obj N.obj) z).fst
    exact (TrivSqZeroExt.fst_map _ z).trans (TrivSqZeroExt.fst_map _ z).symm
  · intro a b hab
    change TrivSqZeroExt.map (LinearMap.fst A M.obj N.obj) a =
        TrivSqZeroExt.map (LinearMap.fst A M.obj N.obj) b ∧
      TrivSqZeroExt.map (LinearMap.snd A M.obj N.obj) a =
        TrivSqZeroExt.map (LinearMap.snd A M.obj N.obj) b at hab
    have hfst : TrivSqZeroExt.fst a = TrivSqZeroExt.fst b :=
      ((TrivSqZeroExt.fst_map _ a).symm.trans
        (congrArg TrivSqZeroExt.fst hab.1)).trans (TrivSqZeroExt.fst_map _ b)
    have h₁ : (TrivSqZeroExt.snd a).1 = (TrivSqZeroExt.snd b).1 :=
      ((TrivSqZeroExt.snd_map _ a).symm.trans
        (congrArg TrivSqZeroExt.snd hab.1)).trans (TrivSqZeroExt.snd_map _ b)
    have h₂ : (TrivSqZeroExt.snd a).2 = (TrivSqZeroExt.snd b).2 :=
      ((TrivSqZeroExt.snd_map _ a).symm.trans
        (congrArg TrivSqZeroExt.snd hab.2)).trans (TrivSqZeroExt.snd_map _ b)
    exact TrivSqZeroExt.ext hfst (Prod.ext h₁ h₂)
  · intro a b hab
    change a.fst = b.fst at hab
    refine ⟨⟨a.fst, (a.snd, b.snd)⟩, ?_, ?_⟩
    · change TrivSqZeroExt.map (LinearMap.fst A M.obj N.obj) _ = a
      exact TrivSqZeroExt.ext (TrivSqZeroExt.fst_map _ _) (TrivSqZeroExt.snd_map _ _)
    · change TrivSqZeroExt.map (LinearMap.snd A M.obj N.obj) _ = b
      exact TrivSqZeroExt.ext ((TrivSqZeroExt.fst_map _ _).trans hab)
        (TrivSqZeroExt.snd_map _ _)

/-- The kernel of the projection `A[M] ⟶ A` is square zero. -/
public theorem squareZeroProjection_ker_sq (M : ModuleCat.{u} A) :
    RingHom.ker (squareZeroProjection A M).hom ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two, Ideal.mul_le]
  intro a ha b hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  change (a * b : TrivSqZeroExt A M) = 0
  refine TrivSqZeroExt.ext ?_ ?_
  · change a.fst * b.fst = 0
    rw [ha, zero_mul]
  · change a.fst • b.snd + MulOpposite.op b.fst • a.snd = 0
    rw [ha, hb]
    simp

/-- The map on global sections induced by the spectrum of a ring map with square-zero
kernel again has square-zero kernel. -/
public theorem specMap_appTop_ker_sq {R T : CommRingCat.{u}} (f : R ⟶ T)
    (hf : RingHom.ker f.hom ^ 2 = ⊥) : RingHom.ker (Spec.map f).appTop.hom ^ 2 = ⊥ := by
  have hR := (ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso R).hom).mp inferInstance
  rw [Stacks.Smooth.ker_specMap_appTop]
  apply le_antisymm _ bot_le
  calc
    _ ≤ Ideal.comap (Scheme.ΓSpecIso R).hom.hom (RingHom.ker f.hom ^ 2) :=
      Ideal.le_comap_pow _ _
    _ = ⊥ := by
      rw [hf]
      exact (RingHom.injective_iff_ker_eq_bot _).mp hR.1

end ProductSquare

/-! ### Isomorphism classes of lifts over a trivial square-zero extension -/

section LiftClasses

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-- Isomorphism classes of lifts of `x` to `Spec A[M]`, together with their identification
with `x` after restriction to `Spec A`. -/
@[stacks 07WZ "lift classes at the dual numbers"]
public abbrev squareZeroLiftClasses (M : SiteModule A B) : Type _ :=
  Quotient (isIsomorphicSetoid ((Under.post p).Fiber
    (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))))

/-- A pair of lift classes related by the canonical pullback along the ring map induced by a
module homomorphism. -/
public def IsCanonicalLiftTransition {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M)
    (b : squareZeroLiftClasses A B S hS toS hA p x hx N) : Prop :=
  ∃ (yM : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
    (yN : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N))),
    Quotient.mk _ yM = a ∧ Quotient.mk _ yN = b ∧
    ∃ φ : yN.1 ⟶ yM.1,
      (Under.post p).IsCartesian ((Under.post p).map φ) φ ∧
      (BigFppfOver.toScheme B S hS).map
        (eqToHom (congrArg (fun t : Under (p.obj x) => t.right) yN.2).symm ≫
          ((Under.post p).map φ).right ≫
          eqToHom (congrArg (fun t : Under (p.obj x) => t.right) yM.2)) =
        Spec.map (squareZeroRingMap A B f)

/-- A lift over `A[N]` is the pullback of a lift over `A[M]` along a module map `M ⟶ N`,
with its identification over `A` preserved. -/
public def IsPullbackOfSquareZeroLift {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M)
    (b : squareZeroLiftClasses A B S hS toS hA p x hx N) : Prop :=
  ∃ (a' : (Under.post p).Fiber
        (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
    (b' : (Under.post p).Fiber
        (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N))),
    Quotient.mk _ a' = a ∧ Quotient.mk _ b' = b ∧
      ∃ φ : b'.1.right ⟶ a'.1.right,
        p.IsStronglyCartesian (squareZeroOverMap A B S hS toS f) φ ∧
          b'.1.hom ≫ φ = a'.1.hom

private abbrev liftBase {M : SiteModule A B} : Under (p.obj x) :=
  Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)

private def liftBaseMap {M N : SiteModule A B} (f : M ⟶ N) :
    liftBase A B S hS toS hA p x hx (M := N) ⟶ liftBase A B S hS toS hA p x hx (M := M) :=
  Under.homMk (squareZeroOverMap A B S hS toS f) (by
    change (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) ≫
      squareZeroOverMap A B S hS toS f = eqToHom hx ≫ squareZeroArrow A B S hS toS hA M
    rw [Category.assoc, squareZeroArrow_naturality])

private def liftBaseFunctor : SiteModule A B ⥤ (Under (p.obj x))ᵒᵖ where
  obj M := Opposite.op (liftBase A B S hS toS hA p x hx (M := M))
  map f := (liftBaseMap A B S hS toS hA p x hx f).op
  map_id M := by
    apply Quiver.Hom.unop_inj
    apply Under.UnderMorphism.ext
    exact squareZeroOverMap_id A B S hS toS M
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Under.UnderMorphism.ext
    exact squareZeroOverMap_comp A B S hS toS f g

/-- The set-valued functor sending a site module to the isomorphism classes of lifts of `x`
to its trivial square-zero extension. -/
private def liftClassFunctor (hp : p.IsFiberedInGroupoids) : SiteModule A B ⥤ Type _ := by
  letI : (Under.post p).IsFibered := underPost_isFibered p hp x
  exact liftBaseFunctor A B S hS toS hA p x hx ⋙ (Under.post p).isoClassPresheaf

private theorem liftClassFunctor_naturality (hp : p.IsFiberedInGroupoids)
    {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    IsCanonicalLiftTransition A B S hS toS hA p x hx f a
      ((liftClassFunctor A B S hS toS hA p x hx hp).map f a) ∧
    IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f a
      ((liftClassFunctor A B S hS toS hA p x hx hp).map f a) := by
  let q : Under x ⥤ Under (p.obj x) := Under.post p
  let : q.IsFibered := underPost_isFibered p hp x
  induction a using Quotient.ind with
  | _ a =>
    let g := liftBaseMap A B S hS toS hA p x hx f
    let b := Functor.pullbackFiber q a g
    let φ : b.1 ⟶ a.1 := Functor.IsPreFibered.pullbackMap a.2 g
    have hc : q.IsCartesian g φ := Functor.IsPreFibered.pullbackMap.IsCartesian a.2 g
    have hφ : q.IsHomLift g φ := hc.toIsHomLift
    change IsCanonicalLiftTransition A B S hS toS hA p x hx f (Quotient.mk _ a)
        (Quotient.mk _ b) ∧
      IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f (Quotient.mk _ a) (Quotient.mk _ b)
    refine ⟨⟨a, b, rfl, rfl, φ, isCartesian_over_image q g φ hc, ?_⟩,
      ⟨a, b, rfl, rfl, φ.right, ?_, Under.w φ⟩⟩
    · have hh := congrArg Under.Hom.right (IsHomLift.fac q g φ)
      simp only [Under.comp_right, Under.eqToHom_right] at hh
      change (BigFppfOver.toScheme B S hS).map _ = _
      have hmap : (BigFppfOver.toScheme B S hS).map (Under.Hom.right g) =
          Spec.map (squareZeroRingMap A B f) := rfl
      exact (congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) hh).symm.trans hmap
    · have : p.IsHomLift (squareZeroOverMap A B S hS toS f) φ.right :=
        underPost_isHomLift_right p g φ hφ
      exact hp.isStronglyCartesian_homLift _ _

/-- **Lift classes can be transported along every module map.** Every class of lifts of `x`
over `A[M]` has, along each map of site modules `f : M ⟶ N`, a class over `A[N]` which is at once
its canonical transition and its pullback along `Spec A[N] ⟶ Spec A[M]`. -/
public theorem exists_isCanonicalLiftTransition_isPullbackOfSquareZeroLift
    (hp : p.IsFiberedInGroupoids) {M N : SiteModule A B} (f : M ⟶ N)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    ∃ b, IsCanonicalLiftTransition A B S hS toS hA p x hx f a b ∧
      IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f a b :=
  ⟨_, liftClassFunctor_naturality A B S hS toS hA p x hx hp f a⟩

end LiftClasses

/-! ### The tangent functor -/

section Tangent

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

private abbrev algebraAffine : BigAffineFppf B S hS :=
  ⟨algebraOver A B S hS toS hA, show IsAffine (Spec (.of A)) from inferInstance⟩

private abbrev squareZeroAffine (M : SiteModule A B) : BigAffineFppf B S hS :=
  ⟨squareZeroOver A B S hS toS M,
    show IsAffine (Spec (squareZeroRing A M.obj)) from inferInstance⟩

private theorem squareZeroArrow_prod_comm (M N : SiteModule A B) :
    (ObjectProperty.homMk (squareZeroArrow A B S hS toS hA M) :
        algebraAffine A B S hS toS hA ⟶ squareZeroAffine A B S hS toS M) ≫
      (ObjectProperty.homMk
        (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N)) :
          squareZeroAffine A B S hS toS M ⟶
            squareZeroAffine A B S hS toS (siteModuleProd A B hA M N)) =
    (ObjectProperty.homMk (squareZeroArrow A B S hS toS hA N) :
        algebraAffine A B S hS toS hA ⟶ squareZeroAffine A B S hS toS N) ≫
      (ObjectProperty.homMk
        (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N)) :
          squareZeroAffine A B S hS toS N ⟶
            squareZeroAffine A B S hS toS (siteModuleProd A B hA M N)) := by
  apply ObjectProperty.hom_ext
  exact (squareZeroArrow_naturality A B S hS toS hA _).trans
    (squareZeroArrow_naturality A B S hS toS hA _).symm

/-- The commutativity, pullback, surjectivity and square-zero hypotheses of (RS*) at the square
`A[M × N] = A[M] ×_A A[N]`. -/
private theorem squareZeroProd_rsStar_hyps (M N : SiteModule A B) :
    let U := algebraAffine A B S hS toS hA
    let V := squareZeroAffine A B S hS toS M
    let W := squareZeroAffine A B S hS toS N
    let Z := squareZeroAffine A B S hS toS (siteModuleProd A B hA M N)
    let f : U ⟶ V := ObjectProperty.homMk (squareZeroArrow A B S hS toS hA M)
    let g : U ⟶ W := ObjectProperty.homMk (squareZeroArrow A B S hS toS hA N)
    let i : V ⟶ Z :=
      ObjectProperty.homMk (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N))
    let j : W ⟶ Z :=
      ObjectProperty.homMk (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N))
    f ≫ i = g ≫ j ∧
    IsPullback ((BigAffineFppf.toScheme B S hS).map i).appTop
      ((BigAffineFppf.toScheme B S hS).map j).appTop
      ((BigAffineFppf.toScheme B S hS).map f).appTop
      ((BigAffineFppf.toScheme B S hS).map g).appTop ∧
    Function.Surjective ((BigAffineFppf.toScheme B S hS).map g).appTop.hom ∧
    RingHom.ker ((BigAffineFppf.toScheme B S hS).map g).appTop.hom ^ 2 = ⊥ := by
  intro U V W Z f g i j
  refine ⟨squareZeroArrow_prod_comm A B S hS toS hA M N, ?_,
    specMap_appTop_surjective (squareZeroProjection A N.obj) (fun a => ⟨⟨a, 0⟩, rfl⟩),
    specMap_appTop_ker_sq _ (squareZeroProjection_ker_sq A N.obj)⟩
  apply (squareZeroRingProduct_isPullback A B hA M N).of_iso'
    (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _)
  all_goals exact (Scheme.ΓSpecIso_naturality _).symm

/-- **(RS*) at the square `A[M × N] = A[M] ×_A A[N]`.** Restriction along the two
projections is an equivalence from the fibre over `Spec A[M × N]` to the two-fibre product
of the fibres over `Spec A[M]`, `Spec A[N]` and `Spec A`. -/
public theorem squareZeroProd_isEquivalence (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) (M N : SiteModule A B) :
    letI : p.IsFibered := hp.isFibered
    (fiberSquareComparison p (Functor.chosenPullbacks p)
      (squareZeroArrow A B S hS toS hA M) (squareZeroArrow A B S hS toS hA N)
      (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N))
      (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N))
      ((squareZeroArrow_naturality A B S hS toS hA _).trans
        (squareZeroArrow_naturality A B S hS toS hA _).symm)).IsEquivalence := by
  let : p.IsFibered := hp.isFibered
  let U := algebraAffine A B S hS toS hA
  let V := squareZeroAffine A B S hS toS M
  let W := squareZeroAffine A B S hS toS N
  let Z := squareZeroAffine A B S hS toS (siteModuleProd A B hA M N)
  let f : U ⟶ V := ObjectProperty.homMk (squareZeroArrow A B S hS toS hA M)
  let g : U ⟶ W := ObjectProperty.homMk (squareZeroArrow A B S hS toS hA N)
  let i : V ⟶ Z :=
    ObjectProperty.homMk (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N))
  let j : W ⟶ Z :=
    ObjectProperty.homMk (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N))
  obtain ⟨h, hpb, hsurj, hsq⟩ := squareZeroProd_rsStar_hyps A B S hS toS hA M N
  exact hRS U V W Z f g i j h hpb hsurj hsq

/-- Restriction to the two factors is a bijection from the lift classes over the product
module to pairs of lift classes. This is where (RS*) enters. -/
private theorem liftClassFunctor_product_bijective (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) (M N : SiteModule A B) :
    Function.Bijective (fun a : (liftClassFunctor A B S hS toS hA p x hx hp).obj
        (siteModuleProd A B hA M N) =>
      ((liftClassFunctor A B S hS toS hA p x hx hp).map (siteModuleFst A B hA M N) a,
       (liftClassFunctor A B S hS toS hA p x hx hp).map (siteModuleSnd A B hA M N) a)) := by
  let : p.IsFibered := hp.isFibered
  let c := Functor.chosenPullbacks p
  let ι := BigAffineFppf.inclusion B S hS
  let U := algebraAffine A B S hS toS hA
  let V := squareZeroAffine A B S hS toS M
  let W := squareZeroAffine A B S hS toS N
  let Z := squareZeroAffine A B S hS toS (siteModuleProd A B hA M N)
  let f : U ⟶ V := ObjectProperty.homMk (squareZeroArrow A B S hS toS hA M)
  let g : U ⟶ W := ObjectProperty.homMk (squareZeroArrow A B S hS toS hA N)
  let i : V ⟶ Z :=
    ObjectProperty.homMk (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N))
  let j : W ⟶ Z :=
    ObjectProperty.homMk (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N))
  obtain ⟨h, hpb, hsurj, hsq⟩ := squareZeroProd_rsStar_hyps A B S hS toS hA M N
  let x₀ : p.Fiber (ι.obj U) := ⟨x, hx⟩
  obtain ⟨e, he₁, he₂, he₃⟩ :=
    exists_squareZeroLiftEquivalence hp hRS U V W Z f g i j h hpb hsurj hsq x₀
  have h' : ι.map f ≫ ι.map i = ι.map g ≫ ι.map j := congrArg ι.map h
  have he : ∀ t,
      (e.functor.obj t).1 = isoFiberRestrict p c (ι.map f) x₀ (ι.map i)
        (ι.map f ≫ ι.map i) rfl t ∧
      (e.functor.obj t).2 = isoFiberRestrict p c (ι.map g) x₀ (ι.map j)
        (ι.map f ≫ ι.map i) h'.symm t := by
    intro t
    refine ⟨Functor.IsoFiber.ext (he₁ t).1 ?_, Functor.IsoFiber.ext (he₁ t).2 ?_⟩
    · refine (he₃ t).1.trans (heq_of_eq ?_)
      change ((c.pullbackFunctorCompIso (ι.map f) (ι.map i)).symm.app t.obj.left).hom ≫
          t.obj.hom =
        ((c.pullbackFunctorCompIso (ι.map f) (ι.map i)).symm.app t.obj.left).hom ≫
          𝟙 _ ≫ t.obj.hom
      rw [Category.id_comp]
    · exact (he₃ t).2
  have hk : ι.map f ≫ ι.map i =
      squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N) :=
    squareZeroArrow_naturality A B S hS toS hA _
  exact underClassPair_bijective p hp c (ι.map f) x₀ (ι.map g) (ι.map i) (ι.map j) h' _ hk e he

/-- The square-zero immersion attached to the zero module is an isomorphism: `A[0]` is `A`. -/
public theorem squareZeroArrow_zero_isIso :
    IsIso (squareZeroArrow A B S hS toS hA (siteModuleZero A B hA)) := by
  let z := siteModuleZero A B hA
  have hi : IsIso (squareZeroProjection A z.obj) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    refine ⟨fun a b hab => TrivSqZeroExt.ext hab
      (Subsingleton.elim (α := PUnit.{u + 1}) _ _), fun a => ⟨⟨a, PUnit.unit⟩, rfl⟩⟩
  have : IsIso (Spec.map (squareZeroProjection A z.obj)) := inferInstance
  have : IsIso (B.inclusion.map (squareZeroArrow A B S hS toS hA z).left) := by
    change IsIso (Spec.map (squareZeroProjection A z.obj))
    infer_instance
  have : IsIso ((Over.forget (B.obj hS)).map (squareZeroArrow A B S hS toS hA z)) := by
    change IsIso (squareZeroArrow A B S hS toS hA z).left
    exact isIso_of_reflects_iso _ B.inclusion
  exact isIso_of_reflects_iso _ (Over.forget (B.obj hS))

/-- The two projections of a product of site modules exhibit it as a binary product. -/
public def siteModuleProd_isLimit (M N : SiteModule A B) :
    IsLimit (BinaryFan.mk (siteModuleFst A B hA M N) (siteModuleSnd A B hA M N)) := by
  apply isLimitOfReflectsOfMapIsLimit (IsSiteModule A B).ι
  exact IsLimit.ofIsoLimit (ModuleCat.binaryProductLimitCone M.obj N.obj).isLimit
    (BinaryFan.ext (Iso.refl _) rfl rfl)

/-- The zero site module is a terminal object. -/
public def siteModuleZero_isTerminal : IsTerminal (siteModuleZero A B hA) :=
  IsTerminal.ofUniqueHom (fun _ => 0) (by
    intro M f
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact Subsingleton.elim (α := PUnit.{u + 1}) _ _)

include hA in
/-- Two site modules have a binary product. -/
public theorem siteModuleHasLimitPair {M N : SiteModule A B} : HasLimit (pair M N) := by
  let P := IsSiteModule A B
  let c₀ := ModuleCat.binaryProductLimitCone M.obj N.obj
  let α : pair M.obj N.obj ≅ pair M N ⋙ P.ι :=
    NatIso.ofComponents (fun j => eqToIso (by cases j with | mk j => cases j <;> rfl))
      (by
        intro i j f
        obtain ⟨i⟩ := i
        obtain ⟨j⟩ := j
        cases f.eq
        simp)
  let c : LimitCone (pair M N ⋙ P.ι) :=
    { cone := (Cone.postcompose α.hom).obj c₀.cone
      isLimit := (IsLimit.postcomposeHomEquiv α c₀.cone).symm c₀.isLimit }
  let : HasLimit (pair M N ⋙ P.ι) := ⟨⟨c⟩⟩
  let : CreatesLimit (pair M N) P.ι :=
    Limits.createsLimitFullSubcategoryInclusion' (pair M N) c.isLimit
      (product_isSiteModule A B hA M N)
  exact hasLimit_of_created (pair M N) P.ι

include hA in
/-- The site modules have a terminal object. -/
public theorem siteModuleHasTerminal : HasTerminal (SiteModule A B) :=
  (siteModuleZero_isTerminal A B hA).hasTerminal

/-- A set-valued functor on the site modules preserves finite products as soon as its value at
the zero module is a one-element set and restriction to the two factors is a bijection on every
product module. -/
public theorem preservesFiniteProducts_of_product_bijective (F : SiteModule A B ⥤ Type*)
    (hzero : Unique (F.obj (siteModuleZero A B hA)))
    (hprod : ∀ M N : SiteModule A B,
      Function.Bijective (fun a : F.obj (siteModuleProd A B hA M N) =>
        (F.map (siteModuleFst A B hA M N) a, F.map (siteModuleSnd A B hA M N) a))) :
    PreservesFiniteProducts F := by
  have : HasTerminal (SiteModule A B) := siteModuleHasTerminal A B hA
  have : ∀ M N : SiteModule A B, HasLimit (pair M N) :=
    fun M N => siteModuleHasLimitPair A B hA
  have : HasBinaryProducts (SiteModule A B) := hasBinaryProducts_of_hasLimit_pair _
  have : HasFiniteProducts (SiteModule A B) := hasFiniteProducts_of_has_binary_and_terminal
  have : PreservesLimit (Functor.empty.{0} (SiteModule A B)) F := by
    apply preservesLimit_of_preserves_limit_cone (siteModuleZero_isTerminal A B hA)
    refine (isLimitMapConeEmptyConeEquiv F _).symm ?_
    exact (Types.isTerminalEquivUnique _).symm hzero
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) F :=
    preservesLimitsOfShape_pempty_of_preservesTerminal F
  have hpair (M N : SiteModule A B) : PreservesLimit (pair M N) F := by
    apply preservesLimit_of_preserves_limit_cone (siteModuleProd_isLimit A B hA M N)
    refine (isLimitMapConeBinaryFanEquiv F _ _).symm ?_
    have : IsIso ((Types.binaryProductLimit (F.obj M) (F.obj N)).lift
        (BinaryFan.mk (F.map (siteModuleFst A B hA M N))
          (F.map (siteModuleSnd A B hA M N)))) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (hprod M N)
    exact IsLimit.ofPointIso (Types.binaryProductLimit (F.obj M) (F.obj N))
  have : PreservesLimitsOfShape (Discrete WalkingPair) F := ⟨fun {K} => by
    have := hpair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)
    exact preservesLimit_of_iso_diagram F (diagramIsoPair K).symm⟩
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal F

@[instance_reducible]
private def liftClassFunctorZeroUnique (hp : p.IsFiberedInGroupoids) :
    Unique ((liftClassFunctor A B S hS toS hA p x hx hp).obj (siteModuleZero A B hA)) := by
  haveI : p.IsFibered := hp.isFibered
  haveI := squareZeroArrow_zero_isIso A B S hS toS hA
  let x₀ : p.Fiber (algebraOver A B S hS toS hA) := ⟨x, hx⟩
  have hn := underClasses_nonempty p (Functor.chosenPullbacks p)
    (squareZeroArrow A B S hS toS hA (siteModuleZero A B hA)) x₀
  have hs := underClasses_subsingleton p hp
    (squareZeroArrow A B S hS toS hA (siteModuleZero A B hA)) x₀
  exact { default := Classical.choice hn, uniq := fun a => hs.elim _ _ }

private theorem liftClassFunctor_preservesFiniteProducts (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) :
    PreservesFiniteProducts (liftClassFunctor A B S hS toS hA p x hx hp) :=
  preservesFiniteProducts_of_product_bijective A B hA _
    (liftClassFunctorZeroUnique A B S hS toS hA p x hx hp)
    (liftClassFunctor_product_bijective A B S hS toS hA p x hx hp hRS)

/-- An `A`-linear functor on the site modules together with its pointwise identification
with the isomorphism classes of square-zero lifts. -/
public structure TangentFunctorData where
  /-- The tangent functor, linear over the base algebra. -/
  functor : SiteModule A B ⥤ ModuleCat.{max (u + 1) v w} A
  [additive : functor.Additive]
  [linear : functor.Linear A]
  /-- Its underlying sets are the sets of isomorphism classes of lifts. -/
  liftEquiv : ∀ M : SiteModule A B,
    (functor.obj M : Type max (u + 1) v w) ≃
      squareZeroLiftClasses A B S hS toS hA p x hx M
  /-- The identifications commute with the canonical pullback maps on lifts. -/
  naturality : ∀ {M N : SiteModule A B} (f : M ⟶ N) (a : functor.obj M),
    IsCanonicalLiftTransition A B S hS toS hA p x hx f
      (liftEquiv M a) (liftEquiv N (functor.map f a))
  /-- The identifications respect pullback along every module map. -/
  liftEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N) (z : functor.obj M),
    IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f
      (liftEquiv M z) (liftEquiv N (functor.map f z))

attribute [instance] TangentFunctorData.additive TangentFunctorData.linear

/-- A tangent functor exists as soon as the lift classes are small and the set-valued functor
of lift classes preserves finite products. -/
private theorem nonempty_tangentFunctorData_of_preservesFiniteProducts
    (hp : p.IsFiberedInGroupoids)
    (hF : PreservesFiniteProducts (liftClassFunctor A B S hS toS hA p x hx hp))
    (hsmall : ∀ M, Small.{max (u + 1) v w} (squareZeroLiftClasses A B S hS toS hA p x hx M)) :
    Nonempty (TangentFunctorData A B S hS toS hA p x hx) := by
  let F := liftClassFunctor A B S hS toS hA p x hx hp
  have : PreservesFiniteProducts F := hF
  have : HasTerminal (SiteModule A B) := siteModuleHasTerminal A B hA
  have : HasZeroObject (SiteModule A B) := Limits.hasZeroObject_of_hasTerminal_object
  have : ∀ M N : SiteModule A B, HasLimit (pair M N) :=
    fun M N => siteModuleHasLimitPair A B hA
  have : HasBinaryProducts (SiteModule A B) := hasBinaryProducts_of_hasLimit_pair _
  let L := Deformation.linearFunctorLift A F
  let e : L.functor ⋙ forget (ModuleCat A) ≅ F := eqToIso L.forget_comp
  have : ∀ M, Small.{max (u + 1) v w} (L.functor.obj M) := fun M => by
    have : Small.{max (u + 1) v w} (F.obj M) := hsmall M
    exact small_of_injective (e.app M).toEquiv.injective
  let K := shrinkModuleFunctor L.functor
  have : K.Additive := shrinkModuleFunctor_additive L.functor
  have : K.Linear A := shrinkModuleFunctor_linear L.functor
  let e' (M : SiteModule A B) : K.obj M ≃ F.obj M :=
    (Shrink.linearEquiv A (L.functor.obj M)).toEquiv.trans (e.app M).toEquiv
  have he' {M N : SiteModule A B} (f : M ⟶ N) (a : K.obj M) :
      e' N (K.map f a) = F.map f (e' M a) := by
    have he := ConcreteCategory.congr_hom (e.hom.naturality f)
      ((Shrink.linearEquiv A (L.functor.obj M)) a)
    change (e.app N).hom (L.functor.map f _) = F.map f ((e.app M).hom _) at he
    change (e.app N).hom ((Shrink.linearEquiv A (L.functor.obj N))
      ((Shrink.linearEquiv A (L.functor.obj N)).symm
        (L.functor.map f ((Shrink.linearEquiv A (L.functor.obj M)) a)))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact he
  refine ⟨{ functor := K, liftEquiv := e', naturality := ?_, liftEquiv_natural := ?_ }⟩
  · intro M N f a
    change IsCanonicalLiftTransition A B S hS toS hA p x hx f (e' M a) (e' N (K.map f a))
    rw [he']
    exact (liftClassFunctor_naturality A B S hS toS hA p x hx hp f _).1
  · intro M N f a
    change IsPullbackOfSquareZeroLift A B S hS toS hA p x hx f (e' M a) (e' N (K.map f a))
    rw [he']
    exact (liftClassFunctor_naturality A B S hS toS hA p x hx hp f _).2

private theorem nonempty_tangentFunctorData_iff_small (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) :
    Nonempty (TangentFunctorData A B S hS toS hA p x hx) ↔
      ∀ M, Small.{max (u + 1) v w} (squareZeroLiftClasses A B S hS toS hA p x hx M) := by
  constructor
  · rintro ⟨T⟩ M
    exact small_of_injective (T.liftEquiv M).symm.injective
  · intro hsmall
    exact nonempty_tangentFunctorData_of_preservesFiniteProducts A B S hS toS hA p x hx hp
      (liftClassFunctor_preservesFiniteProducts A B S hS toS hA p x hx hp hRS) hsmall

/-- **Stacks 07Y9 part (2)(a), the tangent functor.** For `𝒳` satisfying (RS*), the
isomorphism classes of lifts of `x` over the trivial square-zero extensions `A[M]` are the
underlying sets of an `A`-linear functor of `M`. -/
@[stacks 07Y9 "part (2)(a), the A-linear tangent functor T_x"]
public theorem exists_tangentFunctor (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) :
    Nonempty (TangentFunctorData A B S hS toS hA p x hx) := by
  apply (nonempty_tangentFunctorData_iff_small A B S hS toS hA p x hx hp hRS).mpr
  intro M
  infer_instance

/-- The chosen tangent functor `T_x`, for use in further deformation constructions. -/
public def tangentFunctor (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) : TangentFunctorData A B S hS toS hA p x hx :=
  Classical.choice (exists_tangentFunctor A B S hS toS hA p x hx hp hRS)

/-- **The tangent functor from the product condition alone.** Suppose that, for all site
modules `M` and `N`, restriction along the two projections `A[M × N] ⟶ A[M]` and
`A[M × N] ⟶ A[N]` is a bijection from the isomorphism classes of lifts of `x` over `A[M × N]`
to pairs of isomorphism classes of lifts over `A[M]` and `A[N]`. Then these classes are the
underlying sets of an `A`-linear functor of `M`. This is the part of (RS*) that the
construction of `T_x` uses: the value at the zero module is a single class in any case. -/
public theorem nonempty_tangentFunctorData_of_bijective (hp : p.IsFiberedInGroupoids)
    (hprod : ∀ M N : SiteModule A B,
      letI := underPost_isFibered p hp x
      Function.Bijective (fun a : squareZeroLiftClasses A B S hS toS hA p x hx
          (siteModuleProd A B hA M N) =>
        ((Under.post p).isoClassPresheaf.map
            (Under.homMk (U := Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M))
              (V := Under.mk (eqToHom hx ≫
                squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N)))
              (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N))
              (by simp [squareZeroArrow_naturality])).op a,
          (Under.post p).isoClassPresheaf.map
            (Under.homMk (U := Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N))
              (V := Under.mk (eqToHom hx ≫
                squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N)))
              (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N))
              (by simp [squareZeroArrow_naturality])).op a))) :
    Nonempty (TangentFunctorData A B S hS toS hA p x hx) :=
  nonempty_tangentFunctorData_of_preservesFiniteProducts A B S hS toS hA p x hx hp
    (preservesFiniteProducts_of_product_bijective A B hA _
      (liftClassFunctorZeroUnique A B S hS toS hA p x hx hp) hprod)
    (fun _ => inferInstance)

end Tangent

end Deformation.Artin
