module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Topology.Sheaves.Modules.FreeAlgebraSheafStalk

/-!
# Free algebra sheaves and local isomorphisms of the variable presheaf

Let `A` be a sheaf of commutative rings on a site. A morphism `e : E₁ ⟶ E₂` of presheaves of
sets induces a morphism `A[E₁] ⟶ A[E₂]` of `A`-algebras sending the variable `[t]` to the
variable `[e t]`. On a topological space this morphism is an isomorphism as soon as `e` is a
local isomorphism, that is, locally injective and locally surjective: the stalk at `x` of `A[E]`
is the polynomial algebra `Aₓ[Eₓ]`, the induced morphism is renaming of variables along the map
`(E₁)ₓ → (E₂)ₓ`, and that map is bijective.

## Main definitions

* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafMap`: the morphism `A[E₁] ⟶ A[E₂]` induced by a
  morphism `e : E₁ ⟶ E₂` of presheaves of sets.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafMapIso`: the induced isomorphism
  `A[E₁] ≅ A[E₂]` for a local isomorphism `e`.

## Main results

* `TopCat.Presheaf.injective_stalkFunctor_map_of_isLocallyInjective` and
  `TopCat.Presheaf.bijective_stalkFunctor_map_of_isLocallyBijective`: a locally injective
  morphism of presheaves with values in a concrete category on a space is injective on stalks,
  and a local isomorphism is bijective on stalks.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafStalkRingEquiv_comp_map`: on stalks, and in the
  description of the stalk of `A[E]` as a polynomial algebra, the induced morphism is renaming
  of variables along the map induced by `e` on the stalks of `E₁` and `E₂`.
* `Stacks.Sites.FreeAlgebra.isIso_freeAlgebraSheafMap`: a local isomorphism of presheaves of
  sets induces an isomorphism of free algebra sheaves.

## Implementation notes

The proof below is stalkwise, so it is written for a topological space.

On a general site, `freeAlgebraSheafMap` is constructed together with its two characterising
identities, and it is an isomorphism on an arbitrary site, with no hypothesis
on it — in particular without enough points. This is proved in
`StacksFrontier/CategoryTheory/Sites/Modules/FreeAlgebraSheafSiteLocalIso.lean` as
`Stacks.Sites.FreeAlgebra.isIso_freeAlgebraSheafMap_of_isLocallyBijective`, with
`isIso_freeAlgebraSheafMap_of_W` the form taken by its usual consumer. The use of stalks here is
inessential: `CategoryTheory.GrothendieckTopology.W` is by definition the property that
precomposition with the morphism is bijective on morphisms into a sheaf, which together with the
universal property of `A[E]` transports the variables across `e` and back. What *is* specific to
a topological space is the route taken below, through a description of the stalk of `A[E]` as a
polynomial algebra.

The two spellings `stalk F x` and `(stalkFunctor C x).obj F` of one object are definitionally
but not syntactically equal, so `rw` and `simp` reject rewrites in the stalk identities below as
not type-correct at the `implicit` transparency level. Those identities are therefore assembled
from terms with `congrArg` and `Eq.trans`, and the shape of a goal produced by
`MvPolynomial.ringHom_ext` is fixed with `change` before any such term is applied.

## References

* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf

universe v u w

noncomputable section

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [PreservesFilteredColimits (CategoryTheory.forget C)]
variable {X : TopCat.{v}} {F G : X.Presheaf C}

/-- A locally injective morphism of presheaves with values in a concrete category on a
topological space is injective on every stalk. -/
theorem injective_stalkFunctor_map_of_isLocallyInjective (φ : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ] (x : X) :
    Function.Injective ((stalkFunctor C x).map φ) := by
  intro ξ₁ ξ₂ h
  obtain ⟨U₁, h₁, s₁, rfl⟩ := F.exists_germ_eq ξ₁
  obtain ⟨U₂, h₂, s₂, rfl⟩ := F.exists_germ_eq ξ₂
  rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at h
  obtain ⟨W, hxW, iU, iV, heq⟩ := G.germ_eq x h₁ h₂ _ _ h
  have hnat : ConcreteCategory.hom (φ.app (op W)) ((ConcreteCategory.hom (F.map iU.op)) s₁) =
      ConcreteCategory.hom (φ.app (op W)) ((ConcreteCategory.hom (F.map iV.op)) s₂) := by
    rwa [NatTrans.naturality_apply, NatTrans.naturality_apply]
  obtain ⟨V, g, hg, hxV⟩ :=
    CategoryTheory.Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) φ _ _ hnat x hxW
  have hgg : ConcreteCategory.hom (F.map (g ≫ iU).op) s₁ =
      ConcreteCategory.hom (F.map (g ≫ iV).op) s₂ := by
    simpa [op_comp, F.map_comp] using hg
  calc ConcreteCategory.hom (F.germ U₁ x h₁) s₁
      = ConcreteCategory.hom (F.germ V x hxV) (ConcreteCategory.hom (F.map (g ≫ iU).op) s₁) := by
        rw [germ_res_apply]
    _ = ConcreteCategory.hom (F.germ V x hxV)
          (ConcreteCategory.hom (F.map (g ≫ iV).op) s₂) := by rw [hgg]
    _ = ConcreteCategory.hom (F.germ U₂ x h₂) s₂ := by rw [germ_res_apply]

/-- A local isomorphism of presheaves with values in a concrete category on a topological space,
that is, a morphism which is both locally injective and locally surjective, is bijective on
every stalk. -/
theorem bijective_stalkFunctor_map_of_isLocallyBijective (φ : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ]
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ] (x : X) :
    Function.Bijective ((stalkFunctor C x).map φ) :=
  ⟨injective_stalkFunctor_map_of_isLocallyInjective φ x,
    (locally_surjective_iff_surjective_on_stalks φ).mp
      (inferInstanceAs (CategoryTheory.Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology X) φ)) x⟩

end TopCat.Presheaf

namespace Stacks.Sites.FreeAlgebra

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] (A : Sheaf J CommRingCat.{w})
  {E₁ E₂ : Functor Cᵒᵖ (Type w)}

/-- The morphism of `A`-algebras `A[E₁] ⟶ A[E₂]` induced by a morphism `e : E₁ ⟶ E₂` of
presheaves of sets, sending the variable `[t]` to the variable `[e t]`. -/
def freeAlgebraSheafMap (e : E₁ ⟶ E₂) :
    freeAlgebraSheaf J A E₁ ⟶ freeAlgebraSheaf J A E₂ :=
  freeAlgebraSheafDesc J A _ E₁ (freeAlgebraSheafCoefficientMap J A E₂)
    (e ≫ freeAlgebraSheafVariable J A E₂)

/-- The induced morphism `A[E₁] ⟶ A[E₂]` respects the structural morphisms from `A`. -/
theorem freeAlgebraSheafCoefficientMap_comp_map (e : E₁ ⟶ E₂) :
    freeAlgebraSheafCoefficientMap J A E₁ ≫ freeAlgebraSheafMap J A e =
      freeAlgebraSheafCoefficientMap J A E₂ :=
  freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _

/-- The induced morphism `A[E₁] ⟶ A[E₂]` carries the variable `[t]` to the variable `[e t]`. -/
theorem freeAlgebraSheafVariable_comp_map (e : E₁ ⟶ E₂) :
    freeAlgebraSheafVariable J A E₁ ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map (freeAlgebraSheafMap J A e))
        (forget CommRingCat.{w}) = e ≫ freeAlgebraSheafVariable J A E₂ :=
  freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _

end Site

section Space

variable {X : TopCat.{u}} (A : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  {E₁ E₂ : X.Presheaf (Type u)} (e : E₁ ⟶ E₂) (x : X)

/-- **On stalks the induced morphism is renaming of variables.** Under the identification of the
stalk of `A[E]` with the polynomial algebra `Aₓ[Eₓ]`, the morphism `A[E₁] ⟶ A[E₂]` induced by
`e : E₁ ⟶ E₂` is renaming of variables along the map `(E₁)ₓ → (E₂)ₓ` induced by `e`. -/
theorem freeAlgebraSheafStalkRingEquiv_comp_map :
    ((freeAlgebraSheafStalkRingEquiv A E₂ x).toRingHom.comp
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom)).comp
        (freeAlgebraSheafStalkRingEquiv A E₁ x).symm.toRingHom =
      (MvPolynomial.rename ((stalkFunctor (Type u) x).map e).hom :
        MvPolynomial (E₁.stalk x) (ToType (stalk A.obj x)) →ₐ[ToType (stalk A.obj x)]
          MvPolynomial (E₂.stalk x) (ToType (stalk A.obj x))).toRingHom := by
  have hcomp : (stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E₁).hom ≫
      (stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom =
      (stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E₂).hom :=
    ((stalkFunctor CommRingCat.{u} x).map_comp _ _).symm.trans
      (congrArg ((stalkFunctor CommRingCat.{u} x).map)
        (congrArg (fun g => (sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map g)
          (freeAlgebraSheafCoefficientMap_comp_map (Opens.grothendieckTopology X) A e)))
  apply MvPolynomial.ringHom_ext
  · intro a
    change (freeAlgebraSheafStalkRingEquiv A E₂ x)
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom
          ((freeAlgebraSheafStalkRingEquiv A E₁ x).symm (MvPolynomial.C a))) =
      MvPolynomial.rename ((stalkFunctor (Type u) x).map e).hom (MvPolynomial.C a)
    have hs : (freeAlgebraSheafStalkRingEquiv A E₁ x).symm (MvPolynomial.C a) =
        ((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E₁).hom).hom a :=
      ((freeAlgebraSheafStalkRingEquiv A E₁ x).symm_apply_eq.2
        (freeAlgebraSheafStalkRingEquiv_coefficientMap A E₁ x a).symm)
    have hmid : (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom)
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E₁).hom).hom a) =
        ((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A E₂).hom).hom a :=
      (CommRingCat.comp_apply _ _ a).symm.trans
        (congrArg (fun q : stalk A.obj x ⟶
            stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A E₂).obj x => q.hom a) hcomp)
    exact ((congrArg (fun y => (freeAlgebraSheafStalkRingEquiv A E₂ x)
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom y)) hs).trans
      ((congrArg (freeAlgebraSheafStalkRingEquiv A E₂ x) hmid).trans
        (freeAlgebraSheafStalkRingEquiv_coefficientMap A E₂ x a))).trans
      (MvPolynomial.rename_C _ _).symm
  · intro ε
    obtain ⟨U, hx, t, rfl⟩ := E₁.exists_germ_eq ε
    change (freeAlgebraSheafStalkRingEquiv A E₂ x)
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom
          ((freeAlgebraSheafStalkRingEquiv A E₁ x).symm
            (MvPolynomial.X ((E₁.germ U x hx).hom t)))) =
      MvPolynomial.rename ((stalkFunctor (Type u) x).map e).hom
        (MvPolynomial.X ((E₁.germ U x hx).hom t))
    have hs : (freeAlgebraSheafStalkRingEquiv A E₁ x).symm
          (MvPolynomial.X ((E₁.germ U x hx).hom t)) =
        (germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A E₁).obj U x hx).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E₁).app (op U) t) :=
      ((freeAlgebraSheafStalkRingEquiv A E₁ x).symm_apply_eq.2
        (freeAlgebraSheafStalkRingEquiv_variable A E₁ x U hx t).symm)
    have hv : ((freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom.app (op U)).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E₁).app (op U) t) =
        (freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E₂).app (op U)
          (e.app (op U) t) :=
      congrArg (fun n : E₁ ⟶ underlyingPresheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A E₂) => n.app (op U) t)
        (freeAlgebraSheafVariable_comp_map (Opens.grothendieckTopology X) A e)
    refine ((congrArg (fun y => (freeAlgebraSheafStalkRingEquiv A E₂ x)
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom y)) hs).trans
      ((congrArg (freeAlgebraSheafStalkRingEquiv A E₂ x)
        ((stalkFunctor_map_germ_apply U x hx
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom
          ((freeAlgebraSheafVariable (Opens.grothendieckTopology X) A E₁).app (op U) t)).trans
        (congrArg (fun z => (germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A E₂).obj
          U x hx).hom z) hv))).trans ?_)).trans (MvPolynomial.rename_X _ _).symm
    exact (freeAlgebraSheafStalkRingEquiv_variable A E₂ x U hx (e.app (op U) t)).trans
      (congrArg MvPolynomial.X (stalkFunctor_map_germ_apply U x hx e t).symm)

/-- Under the identification of the stalk of `A[E]` with a polynomial algebra, the stalk of the
induced morphism is renaming of variables, read on elements. -/
theorem freeAlgebraSheafStalkRingEquiv_map
    (ξ : ToType (stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A E₁).obj x)) :
    freeAlgebraSheafStalkRingEquiv A E₂ x
        (((stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom ξ) =
      MvPolynomial.rename ((stalkFunctor (Type u) x).map e).hom
        (freeAlgebraSheafStalkRingEquiv A E₁ x ξ) :=
  (congrArg (fun y => (freeAlgebraSheafStalkRingEquiv A E₂ x)
      (((stalkFunctor CommRingCat.{u} x).map
        (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom).hom y))
    (RingEquiv.symm_apply_apply _ ξ)).symm.trans
    (DFunLike.congr_fun (freeAlgebraSheafStalkRingEquiv_comp_map A e x)
      (freeAlgebraSheafStalkRingEquiv A E₁ x ξ))

/-- If `e` is bijective on the stalks at `x`, so is the induced morphism `A[E₁] ⟶ A[E₂]`: both
stalks are polynomial algebras over `Aₓ` and the morphism renames the variables. -/
theorem bijective_stalkFunctor_map_freeAlgebraSheafMap
    (h : Function.Bijective ((stalkFunctor (Type u) x).map e).hom) :
    Function.Bijective (ConcreteCategory.hom ((stalkFunctor CommRingCat.{u} x).map
      (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e).hom)) := by
  constructor
  · intro ξ₁ ξ₂ hξ
    refine (freeAlgebraSheafStalkRingEquiv A E₁ x).injective
      (MvPolynomial.rename_injective _ h.1 ?_)
    exact (freeAlgebraSheafStalkRingEquiv_map A e x ξ₁).symm.trans
      ((congrArg (freeAlgebraSheafStalkRingEquiv A E₂ x) hξ).trans
        (freeAlgebraSheafStalkRingEquiv_map A e x ξ₂))
  · intro η
    obtain ⟨p, hp⟩ := MvPolynomial.rename_surjective ((stalkFunctor (Type u) x).map e).hom h.2
      (freeAlgebraSheafStalkRingEquiv A E₂ x η)
    refine ⟨(freeAlgebraSheafStalkRingEquiv A E₁ x).symm p,
      (freeAlgebraSheafStalkRingEquiv A E₂ x).injective ?_⟩
    exact (freeAlgebraSheafStalkRingEquiv_map A e x _).trans
      ((congrArg (MvPolynomial.rename ((stalkFunctor (Type u) x).map e).hom)
        (RingEquiv.apply_symm_apply _ p)).trans hp)

/-- **A local isomorphism of the variable presheaf induces an isomorphism of free algebra
sheaves.** If `e : E₁ ⟶ E₂` is locally injective and locally surjective then
`A[E₁] ⟶ A[E₂]` is an isomorphism, because on stalks it is renaming of variables along a
bijection. -/
instance isIso_freeAlgebraSheafMap
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) e]
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e] :
    IsIso (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e) :=
  (isIso_iff_stalkFunctor_map_iso _).mpr fun x =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_stalkFunctor_map_freeAlgebraSheafMap A e x
        (bijective_stalkFunctor_map_of_isLocallyBijective e x))

/-- The isomorphism `A[E₁] ≅ A[E₂]` induced by a local isomorphism `e : E₁ ⟶ E₂` of presheaves
of sets. -/
def freeAlgebraSheafMapIso
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) e]
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e] :
    freeAlgebraSheaf (Opens.grothendieckTopology X) A E₁ ≅
      freeAlgebraSheaf (Opens.grothendieckTopology X) A E₂ :=
  asIso (freeAlgebraSheafMap (Opens.grothendieckTopology X) A e)

/-- The forward map of `freeAlgebraSheafMapIso A e` is `freeAlgebraSheafMap _ A e`. -/
@[simp]
theorem freeAlgebraSheafMapIso_hom
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) e]
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e] :
    (freeAlgebraSheafMapIso A e).hom = freeAlgebraSheafMap (Opens.grothendieckTopology X) A e :=
  rfl

end Space

end Stacks.Sites.FreeAlgebra

end

end
