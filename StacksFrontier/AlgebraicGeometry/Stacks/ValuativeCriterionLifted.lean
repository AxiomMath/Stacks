module

public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion
public import StacksFrontier.CategoryTheory.DottedArrows.TwoYoneda
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomStack

/-!
# The existence part of the valuative criterion at a larger morphism universe (Stacks 0CLK)

`AlgebraicGeometry.Stack.ValuativeCriterion.Existence` states Stacks 0CLK for a 1-morphism of
`AlgebraicGeometry.Stack.AlgebraicStacks`, the 2-category of algebraic stacks whose total
categories have their morphisms in the universe `u` of the schemes of the site. Stacks of
sheaves — the Picard stack of Section 0372, the stack of coherent sheaves of Stacks 08KB — have
their morphisms one universe higher, because a morphism carries a morphism of sheaves of modules
on a site. This file states the same criterion for a 1-morphism of categories fibred in groupoids
over the big fppf site whose morphisms live in the universe `max u v`, with the categories
represented by the spectra of the valuation ring and of its fraction field raised to that
universe by `CategoryTheory.ULiftHom`, which changes neither their objects nor, up to the
canonical equivalence, the category over the site.

Algebraicity of the source and target is not needed to state the criterion and is not assumed.

## Main definitions

* `AlgebraicGeometry.Stack.liftedRepresentable` and
  `AlgebraicGeometry.Stack.liftedRepresentableMap`: the category represented by an object of the
  big fppf site, with its morphisms raised to the universe `max u v`, and the 1-morphism a map of
  site objects induces.
* `AlgebraicGeometry.Stack.LiftedValuativeSquare` and
  `AlgebraicGeometry.Stack.LiftedValuativeSquare.DominatingExtension`: **Stacks 0CLK**, the
  valuative square and a dominating extension of it, field for field those of
  `AlgebraicGeometry.Stack.ValuativeSquare`.
* `AlgebraicGeometry.Stack.LiftedValuativeCriterion.Existence`: **Stacks 0CLK**, the criterion.
* `AlgebraicGeometry.Stack.LiftedValuativeSquare.trivialExtension`: the dominating extension
  given by the valuation ring itself.

## Main results

* `AlgebraicGeometry.Stack.nonempty_dottedArrow_liftedRepresentable_of_fiberObj`: a dotted arrow
  out of a lifted represented category, from an object of the fibre over the special point and
  a factorisation of the filling 2-morphism at the unit object. This is the 2-Yoneda lemma
  (`CategoryTheory.Functor.TwoYoneda.exists_factorisation_of_unitHom`) read through the lift.
* `AlgebraicGeometry.Stack.nonempty_dottedArrow_liftedRepresentable_of_faithful`: the same when
  the structure functor of the target is faithful, where the factorisation is automatic.

## References

* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace AlgebraicGeometry.Stack

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Represented categories at a larger morphism universe -/

/-- The category fibred in groupoids over the big fppf site of `S` represented by an object `T`
of the site, with its morphisms raised to the universe `max u v` by `CategoryTheory.ULiftHom`:
the slice over `T` with its forgetful functor. -/
abbrev liftedRepresentable (T : BigFppfOver B S hS) :
    CatFiberedInGroupoids.{u, max u v, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (Functor.uliftHomProj.{u, u + 1, u, u + 1, v} (Over.forget T)))
    (Functor.isFiberedInGroupoids_uliftHomProj _ (Functor.IsFiberedInGroupoids.over_forget T))

/-- The functor between lifted represented categories induced by a map of site objects: the lift
of `CategoryTheory.Over.map`. -/
abbrev liftedOverMap {T T' : BigFppfOver B S hS} (h : T ⟶ T') :
    ULiftHom.{v} (Over T) ⥤ ULiftHom.{v} (Over T') :=
  ULiftHom.down ⋙ Over.map h ⋙ ULiftHom.up

/-- The canonical 1-morphism of lifted represented categories induced by a map of site
objects. -/
abbrev liftedRepresentableMap {T T' : BigFppfOver B S hS} (h : T ⟶ T') :
    liftedRepresentable.{u, v} B S hS T ⟶ liftedRepresentable.{u, v} B S hS T' :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := liftedOverMap.{u, v} B S hS h
      w := rfl }

/-- The comparison `𝒞/T ⥤ ULiftHom (𝒞/T)` of the represented category with its lift, as a
1-morphism over the site. -/
abbrev liftedRepresentableUp (T : BigFppfOver B S hS) :
    BasedCategory.slice T ⥤ᵇ (liftedRepresentable.{u, v} B S hS T).val where
  toFunctor := (ULiftHom.up : Over T ⥤ ULiftHom.{v} (Over T))
  w := rfl

/-- The comparison `ULiftHom (𝒞/T) ⥤ 𝒞/T` of the lift with the represented category, as a
1-morphism over the site. -/
abbrev liftedRepresentableDown (T : BigFppfOver B S hS) :
    (liftedRepresentable.{u, v} B S hS T).val ⥤ᵇ BasedCategory.slice T where
  toFunctor := (ULiftHom.down : ULiftHom.{v} (Over T) ⥤ Over T)
  w := rfl

/-! ### The valuative square -/

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Stacks 0CLK.** The solid part of a 2-commutative valuative square for a 1-morphism `f` of
categories fibred in groupoids over the big fppf site of `S` whose morphisms live in the universe
`max u v`: a valuation ring with its fraction field, both of whose spectra lie in the chosen big
fppf site, a structure morphism to `S`, the canonical map between the two spectra and its
realisation `j` between the lifted represented categories, a generic point `x` of `𝒳`, a special
point `y` of `𝒴`, and a 2-morphism `γ` making the square 2-commute.

This is `AlgebraicGeometry.Stack.ValuativeSquare` field for field, with the represented
categories lifted to the morphism universe of `𝒳` and `𝒴`. -/
structure LiftedValuativeSquare (f : 𝒳 ⟶ 𝒴) where
  /-- The valuation ring. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The fraction field of the valuation ring. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The spectrum of the valuation ring lies in the big fppf site. -/
  ring_mem : B.Contains (Spec (.of R))
  /-- The spectrum of the fraction field lies in the big fppf site. -/
  field_mem : B.Contains (Spec (.of K))
  /-- The structure morphism of the spectrum of the valuation ring. -/
  base : Spec (.of R) ⟶ S
  /-- The canonical map from the generic point to the spectrum of the valuation ring, read in the
  big fppf category over `S`. -/
  genericMap : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
    siteObject B S hS ring_mem base
  /-- The canonical map is the one induced by the inclusion of the valuation ring in its fraction
  field. -/
  genericMap_left : (B.inclusion).map genericMap.left =
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  /-- The left edge of the square: the canonical map, read as a 1-morphism of categories fibred
  in groupoids. -/
  j : liftedRepresentable.{u, v} B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)) ⟶
    liftedRepresentable.{u, v} B S hS (siteObject B S hS ring_mem base)
  /-- The left edge is the canonical map. -/
  j_canonical : j.hom.toFunctor = liftedOverMap.{u, v} B S hS genericMap
  /-- The generic point of `𝒳`. -/
  x : liftedRepresentable.{u, v} B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base)) ⟶ 𝒳
  /-- The special point of `𝒴`. -/
  y : liftedRepresentable.{u, v} B S hS (siteObject B S hS ring_mem base) ⟶ 𝒴
  /-- The 2-morphism making the square 2-commute. -/
  γ : (j ≫ y) ⟶ (x ≫ f)

namespace LiftedValuativeSquare

attribute [instance] commRing domain valuationRing field algebra isFractionRing

variable {f : 𝒳 ⟶ 𝒴}

/-- **Stacks 0CLK.** An extension `K'/K` of fields together with a valuation ring `R' ⊂ K'`
dominating `R`, and the diagram of lifted represented spectra it induces: the maps
`specialOver`, `genericOver` and `genericMap` of site objects, their realisations `a`, `k` and `j`
as 1-morphisms of categories fibred in groupoids, and the 2-morphism `commute` filling the square
of spectra. This is `AlgebraicGeometry.Stack.ValuativeSquare.DominatingExtension` field for
field. -/
structure DominatingExtension (q : LiftedValuativeSquare B S hS f) where
  /-- The dominating valuation ring. -/
  R' : Type u
  [commRing : CommRing R']
  [domain : IsDomain R']
  [valuationRing : ValuationRing R']
  /-- The extension of the fraction field. -/
  K' : Type u
  [field : Field K']
  [algebra : Algebra R' K']
  [isFractionRing : IsFractionRing R' K']
  /-- The map of valuation rings. -/
  ringMap : q.R →+* R'
  /-- The map of fraction fields. -/
  fieldMap : q.K →+* K'
  /-- The map of valuation rings is local: this is the domination condition. -/
  isLocalHom : IsLocalHom ringMap
  /-- The two maps are compatible with the inclusions of the valuation rings in their fraction
  fields. -/
  fraction_comm :
    (algebraMap R' K').comp ringMap = fieldMap.comp (algebraMap q.R q.K)
  /-- The spectrum of the dominating valuation ring lies in the big fppf site. -/
  ring_mem : B.Contains (Spec (.of R'))
  /-- The spectrum of the extended fraction field lies in the big fppf site. -/
  field_mem : B.Contains (Spec (.of K'))
  /-- The map of spectra of valuation rings, as a map of site objects. -/
  specialOver : siteObject B S hS ring_mem
      (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base
  /-- `specialOver` is the map induced by `ringMap`. -/
  specialOver_left : (B.inclusion).map specialOver.left =
    Spec.map (CommRingCat.ofHom ringMap)
  /-- The map of spectra of fraction fields, as a map of site objects. -/
  genericOver : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  /-- `genericOver` is the map induced by `fieldMap`. -/
  genericOver_left : (B.inclusion).map genericOver.left =
    Spec.map (CommRingCat.ofHom fieldMap)
  /-- The canonical map of the extended square, as a map of site objects. -/
  genericMap : siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom ringMap) ≫ q.base) ⟶
    siteObject B S hS ring_mem
      (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)
  /-- The canonical map of the extended square is the one induced by the inclusion of the
  dominating valuation ring in its fraction field. -/
  genericMap_left : (B.inclusion).map genericMap.left =
    Spec.map (CommRingCat.ofHom (algebraMap R' K'))
  /-- The left edge of the extended square. -/
  j : liftedRepresentable.{u, v} B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)) ⟶
    liftedRepresentable.{u, v} B S hS
      (siteObject B S hS ring_mem
        (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base))
  /-- The left edge of the extended square is the canonical map. -/
  j_canonical : j.hom.toFunctor = liftedOverMap.{u, v} B S hS genericMap
  /-- The map from the extended special point to the original one. -/
  a : liftedRepresentable.{u, v} B S hS
      (siteObject B S hS ring_mem
        (Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)) ⟶
    liftedRepresentable.{u, v} B S hS (siteObject B S hS q.ring_mem q.base)
  /-- `a` is the map induced by `specialOver`. -/
  a_canonical : a.hom.toFunctor = liftedOverMap.{u, v} B S hS specialOver
  /-- The map from the extended generic point to the original one. -/
  k : liftedRepresentable.{u, v} B S hS
      (siteObject B S hS field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom ringMap) ≫ q.base)) ⟶
    liftedRepresentable.{u, v} B S hS
      (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))
  /-- `k` is the map induced by `genericOver`. -/
  k_canonical : k.hom.toFunctor = liftedOverMap.{u, v} B S hS genericOver
  /-- The 2-morphism filling the square of represented spectra. -/
  commute : (j ≫ a) ⟶ (k ≫ q.j)

attribute [instance] DominatingExtension.commRing DominatingExtension.domain
  DominatingExtension.valuationRing DominatingExtension.field
  DominatingExtension.algebra DominatingExtension.isFractionRing

/-- The 2-morphism filling the outer rectangle of a dominating extension, obtained by pasting the
square of represented spectra with the original square. -/
noncomputable def DominatingExtension.inducedGamma
    {q : LiftedValuativeSquare B S hS f} (e : q.DominatingExtension) :
    (e.j ≫ (e.a ≫ q.y)) ⟶ ((e.k ≫ q.x) ≫ f) :=
  (α_ e.j e.a q.y).inv ≫ (e.commute ▷ q.y) ≫
    (α_ e.k q.j q.y).hom ≫ (e.k ◁ q.γ) ≫
      (α_ e.k q.x f).inv

end LiftedValuativeSquare

namespace LiftedValuativeCriterion

/-- **Stacks 0CLK**, at the morphism universe `max u v`. A 1-morphism of categories fibred in
groupoids over the big fppf site *satisfies the existence part of the valuative criterion* when
every valuative square for it admits a dotted arrow after an extension of the fraction field and
passage to a dominating valuation ring. -/
abbrev Existence (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ q : LiftedValuativeSquare B S hS f,
    ∃ e : q.DominatingExtension,
      Nonempty (DottedArrow (e.k ≫ q.x) e.j f (e.a ≫ q.y) e.inducedGamma)

end LiftedValuativeCriterion

/-! ### Dotted arrows out of a lifted represented category -/

/-- Over a faithful functor, two morphisms with the same source and target lying over the same
morphism are equal. -/
theorem eq_of_isHomLift_of_faithful {𝒞 : Type*} [Category* 𝒞] {𝒮 : Type*} [Category* 𝒮]
    (p : 𝒮 ⥤ 𝒞) [p.Faithful] {R R' : 𝒞} (g : R ⟶ R') {a b : 𝒮} (φ ψ : a ⟶ b)
    (hφ : p.IsHomLift g φ) (hψ : p.IsHomLift g ψ) : φ = ψ :=
  p.map_injective (by rw [IsHomLift.fac' p g φ, IsHomLift.fac' p g ψ])

section DottedArrow

variable {U V : BigFppfOver B S hS} (r : U ⟶ V)
  {x : liftedRepresentable.{u, v} B S hS U ⟶ 𝒳}
  {j : liftedRepresentable.{u, v} B S hS U ⟶ liftedRepresentable.{u, v} B S hS V}
  {f : 𝒳 ⟶ 𝒴} {y : liftedRepresentable.{u, v} B S hS V ⟶ 𝒴} {γ : (j ≫ y) ⟶ (x ≫ f)}

/-- A 1-morphism of categories fibred in groupoids over the site preserves lifts of morphisms. -/
private theorem isHomLift_hom_map {a b : 𝒳.val.obj} {R R' : BigFppfOver B S hS} {g : R ⟶ R'}
    {φ : a ⟶ b} (f : 𝒳 ⟶ 𝒴) (hφ : 𝒳.val.p.IsHomLift g φ) : 𝒴.val.p.IsHomLift g (f.hom.map φ) :=
  have : (BasedCategory.ofFunctor 𝒳.val.p).p.IsHomLift g φ := hφ
  f.hom.preserves_isHomLift _ _

/-- **A dotted arrow out of a lifted represented category, from an object of a fibre.** Let the
left edge `j` of the square be the lift of the restriction along `r : U ⟶ V`. Given an object
`Z` of `𝒳` over `V`, a morphism `m : x(1_U) ⟶ Z` over `r` and a morphism `b : y(1_V) ⟶ f(Z)` over
`𝟙 V` through which `γ` factors at the unit object, the square has a dotted arrow.

This is the 2-Yoneda lemma `CategoryTheory.Functor.TwoYoneda.exists_factorisation_of_unitHom`,
applied to the functors over the site obtained by precomposing `x` and `y` with
`CategoryTheory.ULiftHom.up`; the dotted arrow and its two 2-morphisms are read back through
`CategoryTheory.ULiftHom.down`, which is the identity on objects. -/
theorem nonempty_dottedArrow_liftedRepresentable_of_fiberObj
    (hj : j.hom.toFunctor = liftedOverMap.{u, v} B S hS r)
    (Z : 𝒳.val.obj) (hZ : 𝒳.val.p.obj Z = V)
    (m : x.hom.obj (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))) ⟶ Z) (hm : 𝒳.val.p.IsHomLift r m)
    (b : y.hom.obj (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 V))) ⟶ f.hom.obj Z)
    (hb : 𝒴.val.p.IsHomLift (𝟙 V) b)
    (h : γ.hom.app (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))) ≫ f.hom.map m =
      y.hom.map (show j.hom.obj (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))) ⟶
          ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 V)) from
        ULift.up (Over.mkIdTerminal.from
          (ULiftHom.objDown.{u + 1, v} (j.hom.obj (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))))))) ≫
        b) :
    Nonempty (DottedArrow x j f y γ) := by
  obtain rfl : j = liftedRepresentableMap.{u, v} B S hS r :=
    Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' hj)
  let G : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor 𝒳.val.p :=
    BasedFunctor.comp (liftedRepresentableUp.{u, v} B S hS U) x.hom
  let H : BasedCategory.slice V ⥤ᵇ BasedCategory.ofFunctor 𝒴.val.p :=
    BasedFunctor.comp (liftedRepresentableUp.{u, v} B S hS V) y.hom
  let γ' : BasedFunctor.comp (BasedFunctor.overMap r) H ⟶ BasedFunctor.comp G f.hom :=
    { toNatTrans :=
        { app := fun z => γ.hom.app (ULiftHom.objUp.{u + 1, v} z)
          naturality := fun {z z'} φ => γ.hom.naturality (X := ULiftHom.objUp.{u + 1, v} z)
            (Y := ULiftHom.objUp.{u + 1, v} z') (ULift.up φ) }
      isHomLift' := fun z => γ.hom.isHomLift' (ULiftHom.objUp.{u + 1, v} z) }
  obtain ⟨A, c, hc⟩ := Functor.TwoYoneda.exists_basedFunctor_unitHom
    𝒳.val.p 𝒳.isFiberedInGroupoids Z hZ
  have hciso : IsIso c :=
    Functor.isIso_of_fiber_isGroupoid (𝒳.isFiberedInGroupoids.fiber_isGroupoid V) c hc
  have hcinv : 𝒳.val.p.IsHomLift (𝟙 V) (inv c) :=
    have := hc
    IsHomLift.lift_id_inv_isIso 𝒳.val.p V c
  have hmc : 𝒳.val.p.IsHomLift r (m ≫ inv c) :=
    have := hm
    IsHomLift.comp_lift_id_right 𝒳.val.p r m (inv c)
  have hbc : 𝒴.val.p.IsHomLift (𝟙 V) (b ≫ f.hom.map (inv c)) :=
    have := hb
    have := isHomLift_hom_map B S hS f hcinv
    IsHomLift.comp_lift_id_right 𝒴.val.p (𝟙 V) b (f.hom.map (inv c))
  obtain ⟨α, β, he⟩ := Functor.TwoYoneda.exists_factorisation_of_unitHom
    𝒳.val.p 𝒴.val.p 𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids r f.hom γ' A
    (m ≫ inv c) hmc (b ≫ f.hom.map (inv c)) hbc (by
      refine Eq.trans (congrArg (fun t => γ.hom.app (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))) ≫ t)
        (f.hom.toFunctor.map_comp m (inv c))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact Eq.trans (congrArg (fun t => t ≫ f.hom.map (inv c)) h) (Category.assoc _ _ _))
  let a : liftedRepresentable.{u, v} B S hS V ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp (liftedRepresentableDown.{u, v} B S hS V) A)
  let αd : (liftedRepresentableMap.{u, v} B S hS r ≫ a) ⟶ x :=
    ⟨{ toNatTrans :=
        { app := fun w => α.app (ULiftHom.objDown.{u + 1, v} w)
          naturality := fun {w w'} φ => α.naturality φ.down }
       isHomLift' := fun w => α.isHomLift' (ULiftHom.objDown.{u + 1, v} w) }⟩
  let βd : y ⟶ (a ≫ f) :=
    ⟨{ toNatTrans :=
        { app := fun w => β.app (ULiftHom.objDown.{u + 1, v} w)
          naturality := fun {w w'} φ => β.naturality φ.down }
       isHomLift' := fun w => β.isHomLift' (ULiftHom.objDown.{u + 1, v} w) }⟩
  refine ⟨{ a := a, α := αd, β := βd, compat := ?_ }⟩
  refine CatFiberedInGroupoids.hom₂_ext_app fun w => ?_
  show γ.hom.app w = β.app ((Over.map r).obj (ULiftHom.objDown.{u + 1, v} w)) ≫ 𝟙 _ ≫
    f.hom.map (α.app (ULiftHom.objDown.{u + 1, v} w))
  exact (he (ULiftHom.objDown.{u + 1, v} w)).trans
    (congrArg (fun t => β.app ((Over.map r).obj (ULiftHom.objDown.{u + 1, v} w)) ≫ t)
      (Category.id_comp _).symm)

/-- **A dotted arrow out of a lifted represented category, when the target is fibred in sets.**
If the structure functor of `𝒴` is faithful, the factorisation of `γ` at the unit object asked
for by `AlgebraicGeometry.Stack.nonempty_dottedArrow_liftedRepresentable_of_fiberObj` holds
automatically: both sides are morphisms of `𝒴` lying over `r`. -/
theorem nonempty_dottedArrow_liftedRepresentable_of_faithful
    (hj : j.hom.toFunctor = liftedOverMap.{u, v} B S hS r) [𝒴.val.p.Faithful]
    (Z : 𝒳.val.obj) (hZ : 𝒳.val.p.obj Z = V)
    (m : x.hom.obj (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))) ⟶ Z) (hm : 𝒳.val.p.IsHomLift r m)
    (b : y.hom.obj (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 V))) ⟶ f.hom.obj Z)
    (hb : 𝒴.val.p.IsHomLift (𝟙 V) b) :
    Nonempty (DottedArrow x j f y γ) := by
  refine nonempty_dottedArrow_liftedRepresentable_of_fiberObj B S hS r hj Z hZ m hm b hb ?_
  obtain rfl : j = liftedRepresentableMap.{u, v} B S hS r :=
    Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' hj)
  have hfm := isHomLift_hom_map B S hS f hm
  have hl : 𝒴.val.p.IsHomLift r
      (γ.hom.app (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))) ≫ f.hom.map m) :=
    @IsHomLift.comp_lift_id_left _ _ _ _ 𝒴.val.p _ _ _ _ _ r (f.hom.map m) hfm
      (γ.hom.app (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))))
      (γ.hom.isHomLift' (ULiftHom.objUp.{u + 1, v} (Over.mk (𝟙 U))))
  let H : BasedCategory.slice V ⥤ᵇ BasedCategory.ofFunctor 𝒴.val.p :=
    BasedFunctor.comp (liftedRepresentableUp.{u, v} B S hS V) y.hom
  have hr : 𝒴.val.p.IsHomLift r
      (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver r)) ≫ b) :=
    @IsHomLift.comp_lift_id_right _ _ _ _ 𝒴.val.p _ _ _ _ _ r
      (H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver r)))
      (Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_unitOver 𝒴.val.p r) b hb
  exact eq_of_isHomLift_of_faithful 𝒴.val.p r _ _ hl hr

end DottedArrow

/-! ### The trivial dominating extension -/

section Trivial

variable {f : 𝒳 ⟶ 𝒴} (q : LiftedValuativeSquare B S hS f)

/-- The ring map of the trivial dominating extension: the identity of the valuation ring.

It is irreducible on purpose. The site objects of the trivial extension carry the base morphism
`Spec(ringMap) ≫ q.base`, and with the identity visible the unifier, comparing two such objects,
unfolds `Spec.map` and the composition of schemes trying to match `Spec(𝟙) ≫ q.base`
against `q.base`; with the map opaque the comparison fails at once. The value is recovered by
`AlgebraicGeometry.Stack.LiftedValuativeSquare.trivialRingMap_eq`. -/
@[irreducible]
noncomputable def LiftedValuativeSquare.trivialRingMap : q.R →+* q.R :=
  RingHom.id q.R

/-- The ring map of the trivial extension is the identity. -/
theorem LiftedValuativeSquare.trivialRingMap_eq : q.trivialRingMap = RingHom.id q.R := by
  unfold LiftedValuativeSquare.trivialRingMap
  rfl

/-- `Spec` of the ring map of the trivial extension, followed by the base morphism, is the base
morphism. -/
theorem LiftedValuativeSquare.spec_trivialRingMap_comp_base :
    Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base = q.base := by
  rw [q.trivialRingMap_eq, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- The compatibility making `trivialSpecialOver` a morphism over `S`. -/
theorem LiftedValuativeSquare.trivialSpecialOver_w :
    𝟙 (B.obj q.ring_mem) ≫ (siteObject B S hS q.ring_mem q.base).hom =
      (siteObject B S hS q.ring_mem
        (Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base)).hom := by
  rw [q.spec_trivialRingMap_comp_base, Category.id_comp]

/-- The identity of the spectrum of the valuation ring, from the site object of the base
morphism of the trivial extension. -/
noncomputable def LiftedValuativeSquare.trivialSpecialOver :
    siteObject B S hS q.ring_mem (Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base :=
  Over.homMk (𝟙 (B.obj q.ring_mem)) (q.trivialSpecialOver_w B S hS)

/-- The compatibility making `trivialGenericOver` a morphism over `S`. -/
theorem LiftedValuativeSquare.trivialGenericOver_w :
    𝟙 (B.obj q.field_mem) ≫
        (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)).hom =
      (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
          Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base)).hom := by
  rw [q.spec_trivialRingMap_comp_base, Category.id_comp]

/-- The identity of the spectrum of the fraction field, between the two site objects the trivial
extension produces. -/
noncomputable def LiftedValuativeSquare.trivialGenericOver :
    siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
          Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base) ⟶
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
  Over.homMk (𝟙 (B.obj q.field_mem)) (q.trivialGenericOver_w B S hS)

/-- The underlying morphism of schemes of the canonical map of `q`, typed by the two objects of
the site it connects. -/
noncomputable abbrev LiftedValuativeSquare.genericMapLeft : B.obj q.field_mem ⟶ B.obj q.ring_mem :=
  q.genericMap.left

/-- The compatibility making `trivialGenericMap` a morphism over `S`. -/
theorem LiftedValuativeSquare.trivialGenericMap_w :
    q.genericMapLeft B S hS ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base) :
          B.obj q.ring_mem ⟶ B.obj hS) =
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
          Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base) :
        B.obj q.field_mem ⟶ B.obj hS) := by
  rw [q.spec_trivialRingMap_comp_base]
  exact Over.w q.genericMap

/-- The canonical map of the trivial extension: the canonical map of `q`, between the site
objects the trivial extension produces. -/
noncomputable def LiftedValuativeSquare.trivialGenericMap :
    siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
          Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem
        (Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base) :=
  Over.homMk (q.genericMapLeft B S hS) (q.trivialGenericMap_w B S hS)

/-- The two composites around the square of spectra of the trivial extension agree. -/
theorem LiftedValuativeSquare.trivialGenericMap_comp :
    q.trivialGenericMap B S hS ≫ q.trivialSpecialOver B S hS =
      q.trivialGenericOver B S hS ≫ q.genericMap :=
  Over.OverMorphism.ext (show q.genericMapLeft B S hS ≫ 𝟙 (B.obj q.ring_mem) =
      𝟙 (B.obj q.field_mem) ≫ q.genericMapLeft B S hS from
    (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The 1-morphisms around the square of lifted represented spectra of the trivial extension
agree. -/
theorem LiftedValuativeSquare.trivial_commute :
    liftedRepresentableMap.{u, v} B S hS (q.trivialGenericMap B S hS) ≫
        liftedRepresentableMap.{u, v} B S hS (q.trivialSpecialOver B S hS) =
      liftedRepresentableMap.{u, v} B S hS (q.trivialGenericOver B S hS) ≫ q.j := by
  refine Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' ?_)
  show liftedOverMap.{u, v} B S hS (q.trivialGenericMap B S hS) ⋙
      liftedOverMap.{u, v} B S hS (q.trivialSpecialOver B S hS) =
    liftedOverMap.{u, v} B S hS (q.trivialGenericOver B S hS) ⋙ q.j.hom.toFunctor
  rw [q.j_canonical]
  show ULiftHom.down ⋙ (Over.map (q.trivialGenericMap B S hS) ⋙
      Over.map (q.trivialSpecialOver B S hS)) ⋙ ULiftHom.up =
    ULiftHom.down ⋙ (Over.map (q.trivialGenericOver B S hS) ⋙ Over.map q.genericMap) ⋙
      ULiftHom.up
  rw [← Over.mapComp_eq, ← Over.mapComp_eq, q.trivialGenericMap_comp]

/-- The ring map of the trivial extension is local. -/
theorem LiftedValuativeSquare.isLocalHom_trivialRingMap : IsLocalHom q.trivialRingMap := by
  rw [q.trivialRingMap_eq]
  infer_instance

/-- `trivialSpecialOver` is the map induced by the ring map of the trivial extension. -/
theorem LiftedValuativeSquare.trivialSpecialOver_left :
    (B.inclusion).map (q.trivialSpecialOver B S hS).left =
      Spec.map (CommRingCat.ofHom q.trivialRingMap) := by
  show B.inclusion.map (𝟙 (B.obj q.ring_mem)) = _
  rw [CategoryTheory.Functor.map_id, q.trivialRingMap_eq, CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- `trivialGenericMap` is the map induced by `R ⟶ K`. -/
theorem LiftedValuativeSquare.trivialGenericMap_left :
    (B.inclusion).map (q.trivialGenericMap B S hS).left =
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := by
  have h : B.inclusion.map (q.genericMapLeft B S hS) =
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) := q.genericMap_left
  exact h

/-- `trivialGenericOver` is the map induced by the identity of `K`. -/
theorem LiftedValuativeSquare.trivialGenericOver_left :
    (B.inclusion).map (q.trivialGenericOver B S hS).left =
      Spec.map (CommRingCat.ofHom (RingHom.id q.K)) := by
  show B.inclusion.map (𝟙 (B.obj q.field_mem)) = _
  rw [CategoryTheory.Functor.map_id, CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- The square of rings of the trivial extension commutes. -/
theorem LiftedValuativeSquare.trivial_fraction_comm :
    (algebraMap q.R q.K).comp q.trivialRingMap = (RingHom.id q.K).comp (algebraMap q.R q.K) := by
  rw [q.trivialRingMap_eq]
  rfl

/-- **The trivial dominating extension** of a valuative square: the valuation ring itself and its
fraction field, with the identity maps. -/
noncomputable def LiftedValuativeSquare.trivialExtension : q.DominatingExtension B S hS where
  R' := q.R
  K' := q.K
  ringMap := q.trivialRingMap
  fieldMap := RingHom.id q.K
  isLocalHom := q.isLocalHom_trivialRingMap
  fraction_comm := q.trivial_fraction_comm
  ring_mem := q.ring_mem
  field_mem := q.field_mem
  specialOver := q.trivialSpecialOver B S hS
  specialOver_left := q.trivialSpecialOver_left B S hS
  genericOver := q.trivialGenericOver B S hS
  genericOver_left := q.trivialGenericOver_left B S hS
  genericMap := q.trivialGenericMap B S hS
  genericMap_left := q.trivialGenericMap_left B S hS
  j := liftedRepresentableMap.{u, v} B S hS (q.trivialGenericMap B S hS)
  j_canonical := rfl
  a := liftedRepresentableMap.{u, v} B S hS (q.trivialSpecialOver B S hS)
  a_canonical := rfl
  k := liftedRepresentableMap.{u, v} B S hS (q.trivialGenericOver B S hS)
  k_canonical := rfl
  commute := eqToHom (q.trivial_commute B S hS)

end Trivial

end AlgebraicGeometry.Stack

end
