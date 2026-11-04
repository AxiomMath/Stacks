module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.Amelioration

/-!
# Fibredness is invariant under equivalence over the base (Stacks 042G)

Let `𝒮` be a category.  A *category over `𝒮`* is a pair `(𝒳, p)` with `p : 𝒳 ⥤ 𝒮`, which is
Mathlib's `CategoryTheory.BasedCategory`, and a *functor over `𝒮`* is a `BasedFunctor`
`𝒳 ⥤ᵇ 𝒴`, i.e. a functor carrying the strict equality `F ⋙ q = p`.  Two categories over `𝒮`
are *equivalent as categories over `𝒮`* when there are functors over `𝒮` in both directions
together with isomorphisms identifying both composites with the identity functors over `𝒮`.
Those isomorphisms are taken in the categories of based functors, so all their components
automatically lie over identity morphisms of `𝒮`; this is exactly being equivalent as
objects of the 2-category of categories over `𝒮`.  Mathlib has no equivalence notion for
based functors, so it is recorded here as `BasedCategory.Equivalence`.

The result is that such an equivalence transports fibredness: `𝒳.p` is a fibred category,
in the sense of `CategoryTheory.Functor.IsFibered`, if and only if `𝒴.p` is.  The crux is
that the forward functor of the equivalence carries strongly cartesian morphisms to
strongly cartesian morphisms, proved by transporting the universal property across the
equivalence of underlying categories, along which the forward functor is fully faithful.
Fibredness of `𝒴.p` then follows by composing the image of a strongly cartesian lift with
the counit component, which is an isomorphism over an identity and hence itself strongly
cartesian.

Composition of based functors is *diagrammatic*: `(F.comp G).obj x = G.obj (F.obj x)`.
Thus for `F : 𝒳 ⥤ᵇ 𝒴` and `G : 𝒴 ⥤ᵇ 𝒳` the endofunctor `F.comp G` of `𝒳` is the composite
written `G ∘ F` in the source, and `G.comp F` on `𝒴` is the one written `F ∘ G`.

The two categories over `𝒮` live in independent object and morphism universes.  Nothing forces
them together: Mathlib's `BasedFunctor`, `BasedNatTrans` and the category `𝒳 ⥤ᵇ 𝒴` in which the
unit and counit are isomorphisms all take the two universe pairs separately, and so does
`CategoryTheory.Equivalence` of the underlying categories.  That is what makes an equivalence
over `𝒮` able to compare a category over `𝒮` with a universe lift of it, which is the use
`StacksFrontier/CategoryTheory/Sites/Stack/Transport/UliftStack.lean` makes of it.
-/

@[expose] public section

-- Needed for the reducibility of `BasedFunctor.comp` in the strongly-cartesian transports below.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Two categories `𝒳` and `𝒴` over `𝒮` are *equivalent as categories over `𝒮`* if there
exist functors over `𝒮` `functor : 𝒳 ⥤ᵇ 𝒴` and `inverse : 𝒴 ⥤ᵇ 𝒳`, together with
isomorphisms of functors over `𝒮` `unitIso : functor ∘ inverse ≅ id` and
`counitIso : inverse ∘ functor ≅ id` (recall that `BasedFunctor.comp` is diagrammatic, so
these are the composites written `G ∘ F` and `F ∘ G` in the Stacks project).  The `≅` is
taken in the category of based functors, so the components of the two isomorphisms
automatically lie over identity morphisms of `𝒮`.

This is precisely being equivalent as objects of the 2-category of categories over `𝒮`. -/
structure BasedCategory.Equivalence (𝒳 : BasedCategory.{v₂, u₂} 𝒮)
    (𝒴 : BasedCategory.{v₃, u₃} 𝒮) where
  /-- The functor over `𝒮` in the forward direction. -/
  functor : 𝒳 ⥤ᵇ 𝒴
  /-- The functor over `𝒮` in the backward direction. -/
  inverse : 𝒴 ⥤ᵇ 𝒳
  /-- Isomorphism of functors over `𝒮` identifying the composite `𝒳 ⥤ 𝒴 ⥤ 𝒳` with the
  identity of `𝒳`. -/
  unitIso : functor.comp inverse ≅ BasedFunctor.id 𝒳
  /-- Isomorphism of functors over `𝒮` identifying the composite `𝒴 ⥤ 𝒳 ⥤ 𝒴` with the
  identity of `𝒴`. -/
  counitIso : inverse.comp functor ≅ BasedFunctor.id 𝒴

/-- An equivalence over `𝒮` read in the other direction: swap `functor` with `inverse` and
`unitIso` with `counitIso`. -/
def BasedCategory.Equivalence.symm {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (e : BasedCategory.Equivalence 𝒳 𝒴) : BasedCategory.Equivalence 𝒴 𝒳 where
  functor := e.inverse
  inverse := e.functor
  unitIso := e.counitIso
  counitIso := e.unitIso

/-- The image of an isomorphism of based functors `F.comp G ≅ id` under the forgetful map to
ordinary functors: an isomorphism `F.toFunctor ⋙ G.toFunctor ≅ 𝟭` obtained by taking
`.toNatTrans` componentwise.  Since `.toNatTrans` preserves composition and identities
definitionally, the result is again an isomorphism. -/
noncomputable def BasedFunctor.toFunctorIso {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒳)
    (unitIso : F.comp G ≅ BasedFunctor.id 𝒳) :
    (F.toFunctor ⋙ G.toFunctor) ≅ 𝟭 𝒳.obj where
  hom := unitIso.hom.toNatTrans
  inv := unitIso.inv.toNatTrans
  hom_inv_id := by
    change (unitIso.hom ≫ unitIso.inv).toNatTrans = _
    rw [unitIso.hom_inv_id]; rfl
  inv_hom_id := by
    change (unitIso.inv ≫ unitIso.hom).toNatTrans = _
    rw [unitIso.inv_hom_id]; rfl

/-- The underlying equivalence of categories `𝒳.obj ≌ 𝒴.obj` of an equivalence over `𝒮`.
It is built with `Equivalence.mk`, which adjointifies the data; in particular the forward
functor of the result is fully faithful. -/
noncomputable def BasedCategory.Equivalence.equiv {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (e : BasedCategory.Equivalence 𝒳 𝒴) : 𝒳.obj ≌ 𝒴.obj :=
  CategoryTheory.Equivalence.mk e.functor.toFunctor e.inverse.toFunctor
    (BasedFunctor.toFunctorIso e.functor e.inverse e.unitIso).symm
    (BasedFunctor.toFunctorIso e.inverse e.functor e.counitIso)

/-- The forward functor `F` of an equivalence over `𝒮` carries `𝒳.p`-strongly cartesian
morphisms to `𝒴.p`-strongly cartesian morphisms.

This is `CategoryTheory.Equivalence.isStronglyCartesian_map_functor` for the underlying
equivalence of categories `e.equiv`, whose forward functor is `F` and along which `𝒴.p`
restricts to `𝒳.p` by `BasedFunctor.w`: a test morphism into `F(x)` is carried back to `𝒳`
by the counit isomorphism and the full faithfulness of `F`, factored uniquely there through
the strongly cartesian `φ`, and the factorisation carried forward again. -/
theorem BasedCategory.Equivalence.isStronglyCartesian_map
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (e : BasedCategory.Equivalence 𝒳 𝒴)
    {U V : 𝒮} {x y : 𝒳.obj} (f : V ⟶ U) (φ : y ⟶ x) [𝒳.p.IsStronglyCartesian f φ] :
    𝒴.p.IsStronglyCartesian f (e.functor.map φ) :=
  e.equiv.isStronglyCartesian_map_functor 𝒴.p e.functor.w f φ inferInstance

/-- Fibredness transports along an equivalence over `𝒮`: if `𝒳.p` is a fibred category and
`𝒳` is equivalent to `𝒴` over `𝒮`, then `𝒴.p` is a fibred category.

Given `x₂` in `𝒴` over `U := p₂(x₂)` and `f : V ⟶ U`, put `G := e.inverse` and note
`p₁(G x₂) = U`.  Fibredness of `𝒳.p` supplies a strongly cartesian `φ : y ⟶ G x₂` over `f`
(a cartesian lift is automatically strongly cartesian in a fibred category), and by
`BasedCategory.Equivalence.isStronglyCartesian_map` its image `F(φ)` is strongly cartesian
over `f` in `𝒴`.  The counit component `i : F (G x₂) ⟶ x₂` is an isomorphism lying over an
identity, hence strongly cartesian, so the composite `F(φ) ≫ i` is a strongly cartesian
morphism into `x₂` over `f`. -/
theorem BasedCategory.Equivalence.isFibered {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
    {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (e : BasedCategory.Equivalence 𝒳 𝒴) (h : 𝒳.p.IsFibered) : 𝒴.p.IsFibered := by
  have := h
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro x₂ V f
  have hw : 𝒳.p.obj (e.inverse.obj x₂) = 𝒴.p.obj x₂ := e.inverse.w_obj x₂
  set f' : V ⟶ 𝒳.p.obj (e.inverse.obj x₂) := f ≫ eqToHom hw.symm with hf'_def
  obtain ⟨y, φ, hφ⟩ := Functor.IsPreFibered.exists_isCartesian' (p := 𝒳.p) f'
  have hφI : 𝒳.p.IsCartesian f' φ := hφ
  have hφS : 𝒳.p.IsStronglyCartesian f' φ := inferInstance
  have hFφ : 𝒴.p.IsStronglyCartesian f' (e.functor.map φ) := e.isStronglyCartesian_map f' φ
  -- The counit component `i : F (G x₂) ⟶ x₂`; it is an isomorphism because it is a component
  -- of the natural isomorphism `BasedFunctor.toFunctorIso _ _ e.counitIso`.
  set i := e.counitIso.hom.toNatTrans.app x₂ with hi_def
  have hi_iso : IsIso i := inferInstanceAs
    (IsIso ((BasedFunctor.toFunctorIso e.inverse e.functor e.counitIso).hom.app x₂))
  have hi_lift : 𝒴.p.IsHomLift (𝟙 (𝒴.p.obj x₂)) i := e.counitIso.hom.app_isHomLift x₂
  -- `i` also lies over `eqToHom hw : 𝒳.p.obj (G x₂) ⟶ 𝒴.p.obj x₂` (= `eqToHom hw ≫ 𝟙`), hence
  -- is strongly cartesian over it.
  have hi_lift' : 𝒴.p.IsHomLift (eqToHom hw) i := by
    rw [← Category.comp_id (eqToHom hw)]
    exact IsHomLift.lift_eqToHom_comp 𝒴.p (𝟙 (𝒴.p.obj x₂)) i hw
  have hi_sc : 𝒴.p.IsStronglyCartesian (eqToHom hw) i :=
    Functor.IsStronglyCartesian.of_isIso 𝒴.p (eqToHom hw) i
  -- Compose: `F.map φ ≫ i` is strongly cartesian over `f' ≫ eqToHom hw = f`.
  have hcomp : 𝒴.p.IsStronglyCartesian (f' ≫ eqToHom hw) (e.functor.map φ ≫ i) :=
    Functor.IsStronglyCartesian.comp 𝒴.p
  rw [hf'_def, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at hcomp
  exact ⟨e.functor.obj y, e.functor.map φ ≫ i, hcomp⟩

/-- **Stacks 042G (Lemma 4.33.8).** Let `𝒮` be a category and let `𝒳` and `𝒴` be categories
over `𝒮`.  If `𝒳` and `𝒴` are equivalent as categories over `𝒮`, then `𝒳` is a fibred
category over `𝒮` if and only if `𝒴` is. -/
@[stacks 042G]
theorem BasedCategory.isFibered_iff_of_equivalence
    {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
    (e : BasedCategory.Equivalence 𝒳 𝒴) :
    𝒳.p.IsFibered ↔ 𝒴.p.IsFibered :=
  ⟨e.isFibered, e.symm.isFibered⟩

end CategoryTheory
