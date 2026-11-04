module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardTopologies

/-!
# The restricted sheaf condition for the extension

Two steps towards the restricted sheaf condition
`AlgebraicGeometry.ExtendingFunctors.IsStandardAffineSheaf` for the extension of a functor from a
full subcategory of `Sch/S`, which Stacks 0GDW deduces from its condition (c).

The first is the passage from a limit cone in `Sch/S` to the underlying limit cone of schemes,
which is what the descent of a standard covering along an inverse limit is stated over. The
second is the passage from the sheaf condition for a covering of a subcategory object by
subcategory objects, tested on the subcategory, to the sheaf condition for the same covering read
in `Sch/S` and tested on all of `Sch/S`.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.isConnected_op_of_isDirectedOrder`,
  `AlgebraicGeometry.ExtendingFunctors.isLimitMapConeForget`: the underlying cone of schemes of a
  limit cone in `Sch/S` indexed by the opposite of a nonempty directed poset is a limit cone.
* `AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isSheafFor`: the sheaf condition
  for the extension and a covering by objects of the subcategory, from the sheaf condition for
  the original functor and the same covering read in the subcategory.

## Implementation notes

The forgetful functor `Sch/S ⟶ Sch` preserves limits of connected shape, and the opposite of a
nonempty directed poset is cofiltered, hence connected; no affineness or finiteness enters.

The two sheaf conditions of
`AlgebraicGeometry.ExtendingFunctors.isSheafFor_extension_of_isSheafFor` differ in what the
compatibility of a family of sections is tested on: an arbitrary object of `Sch/S` mapping to two
members of the covering, against an object of the subcategory doing so. The ambient condition is
therefore the stronger hypothesis and the weaker conclusion, and both halves of
`CategoryTheory.Presieve.IsSheafFor` transfer in the same direction: a family compatible in
`Sch/S` is compatible in the subcategory, so the subcategory condition amalgamates it, and the
amalgamation is unique in `Sch/S` because it is unique in the subcategory. The identification of
the restriction of the extension with the original functor is
`AlgebraicGeometry.ExtendingFunctors.nonempty_restrictionIso`, and it is natural, which is what
makes both transfers go through.

Morphisms of a full subcategory are the ambient morphisms wrapped by
`CategoryTheory.ObjectProperty.homMk`, so the two presieves have literally the same index type
and the same underlying morphisms; only the categories the arrows live in differ.

## References

* [Stacks Project, Tag 0GDW](https://stacks.math.columbia.edu/tag/0GDW)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe v w u

variable {S : Scheme.{u}}

/-! ### The underlying cone of schemes of a limit cone in `Sch/S` -/

/-- The underlying cone of schemes of a limit cone in `Sch/S` of connected shape is a limit
cone. -/
noncomputable def isLimitMapConeForget {J : Type*} [Category J] [IsConnected J]
    {D : J ⥤ Over S} {c : Cone D} (hc : IsLimit c) :
    IsLimit ((Over.forget S).mapCone c) :=
  isLimitOfPreserves (Over.forget S) hc

/-- The underlying cone of schemes of a limit cone in `Sch/S` indexed by the opposite of a
nonempty directed poset is a limit cone. This is the shape of the presentations produced by
`AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation`. -/
noncomputable def isLimitMapConeForgetOfDirected {Λ : Type*} [PartialOrder Λ] [Nonempty Λ]
    [IsDirectedOrder Λ] {D : Λᵒᵖ ⥤ Over S} {c : Cone D} (hc : IsLimit c) :
    IsLimit ((Over.forget S).mapCone c) :=
  have := IsCofiltered.isConnected Λᵒᵖ
  isLimitMapConeForget hc

/-! ### From the subcategory sheaf condition to the ambient one -/

variable {P : ObjectProperty (Over S)} (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))

/-- A family of sections of the extension over the members of a covering by objects of the
subcategory, read as a family of sections of the original functor along the identification of its
restriction with the extension. -/
private lemma map_hom_restrictionIso
    (e : P.ι.op ⋙ extension P F ≅ F) {X Y : P.FullSubcategory} (g : X ⟶ Y)
    (z : (extension P F).obj (op Y.obj)) :
    F.map g.op (e.hom.app (op Y) z)
      = e.hom.app (op X) ((extension P F).map g.hom.op z) :=
  (congrFun (congrArg (fun k => (ConcreteCategory.hom k : _ → F.obj (op X)))
    (e.hom.naturality g.op)) z).symm

/-- Two sections of the extension with equal restrictions along `g` and `g'` have equal
restrictions of their images in the original functor. -/
private lemma map_restrictionIso_eq
    (e : P.ι.op ⋙ extension P F ≅ F) {X Y Y' : P.FullSubcategory} (g : X ⟶ Y) (g' : X ⟶ Y')
    {z : (extension P F).obj (op Y.obj)} {z' : (extension P F).obj (op Y'.obj)}
    (hz : (extension P F).map g.hom.op z = (extension P F).map g'.hom.op z') :
    F.map g.op (e.hom.app (op Y) z) = F.map g'.op (e.hom.app (op Y') z') := by
  rw [map_hom_restrictionIso F e, map_hom_restrictionIso F e, hz]

/-- **The ambient sheaf condition from the subcategory one.** Let `V` be an object of the full
subcategory and `{W i ⟶ V}` a family of morphisms from objects of the full subcategory. If the
original functor satisfies the sheaf condition for that family read in the subcategory, then the
extension satisfies the sheaf condition for the same family read in `Sch/S`.

Compatibility of a family of sections is a stronger demand in `Sch/S`, where it is tested on
every object mapping to two members of the covering, than in the subcategory; so the subcategory
condition amalgamates every `Sch/S`-compatible family, and the amalgamation is unique because it
is already unique in the subcategory. -/
theorem isSheafFor_extension_of_isSheafFor (hP1 : HasAffineOpens P)
    (hP2 : HasFinitePresentationAffines P) (haF : IsZariskiSheafOnSubcategory P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F)
    {ι : Type v} (V : P.FullSubcategory) (W : ι → P.FullSubcategory) (f : ∀ i, W i ⟶ V)
    (hsh : (Presieve.ofArrows W f).IsSheafFor F) :
    (Presieve.ofArrows (fun i => (W i).obj) (fun i => (f i).hom)).IsSheafFor
      (extension P F) := by
  classical
  obtain ⟨e⟩ := nonempty_restrictionIso F hP1 hP2 haF hbF
  have hinj : ∀ (X : P.FullSubcategory), Function.Injective (e.hom.app (op X)) := fun X =>
    (ConcreteCategory.bijective_of_isIso (e.hom.app (op X))).1
  -- the factorization of a general member of each presieve through the arrow of its index
  have hfac : ∀ (A : Over S) (h : A ⟶ V.obj)
      (hh : Presieve.ofArrows (fun i => (W i).obj) (fun i => (f i).hom) h),
      eqToHom hh.obj_idx.symm ≫ (f hh.idx).hom = h :=
    fun _ _ hh => hh.eq_eqToHom_comp_hom_idx.symm
  -- the underlying morphism of a member of the subcategory presieve
  have hhom : ∀ (A : P.FullSubcategory) (h : A ⟶ V) (hh : Presieve.ofArrows W f h),
      h.hom = (eqToHom hh.obj_idx.symm : A ⟶ W hh.idx).hom ≫ (f hh.idx).hom :=
    fun A h hh => by
      rw [← ObjectProperty.FullSubcategory.comp_hom, ← hh.eq_eqToHom_comp_hom_idx]
  -- separatedness
  have hsep : (Presieve.ofArrows (fun i => (W i).obj)
      (fun i => (f i).hom)).IsSeparatedFor (extension P F) := by
    intro x t₁ t₂ ht₁ ht₂
    have key : ∀ i, (extension P F).map (f i).hom.op t₁
        = (extension P F).map (f i).hom.op t₂ := fun i => by
      rw [ht₁ (f i).hom (Presieve.ofArrows.mk i), ht₂ (f i).hom (Presieve.ofArrows.mk i)]
    refine hinj V ?_
    refine hsh.isSeparatedFor.ext fun A h hh => ?_
    refine map_restrictionIso_eq F e h h ?_
    rw [hhom A h hh, ← map_map_apply, ← map_map_apply, key hh.idx]
  refine hsep.isSheafFor fun x hx => ?_
  -- the family of sections of `F` attached to the indices is coherent
  have hcoh : ∀ (i i' : ι) (A : P.FullSubcategory) (a : A ⟶ W i) (b : A ⟶ W i'),
      a ≫ f i = b ≫ f i' →
      F.map a.op (e.hom.app (op (W i)) (x (f i).hom (Presieve.ofArrows.mk i)))
        = F.map b.op (e.hom.app (op (W i')) (x (f i').hom (Presieve.ofArrows.mk i'))) := by
    intro i i' A a b hab
    refine map_restrictionIso_eq F e a b (hx a.hom b.hom (Presieve.ofArrows.mk i)
      (Presieve.ofArrows.mk i') ?_)
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      hab]
  obtain ⟨t, ht⟩ := exists_section_of_isSheafFor_ofArrows W f hsh _ hcoh
  -- the section of the extension matching `t` amalgamates the given family
  obtain ⟨t', ht'⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app (op V))).2 t
  have hval : ∀ i, (extension P F).map (f i).hom.op t'
      = x (f i).hom (Presieve.ofArrows.mk i) := by
    intro i
    refine hinj (W i) ?_
    rw [← map_hom_restrictionIso F e, ht', ht i]
  refine ⟨t', fun A h hh => ?_⟩
  have h1 : (extension P F).map h.op t'
      = (extension P F).map (eqToHom hh.obj_idx.symm).op
        (x (f hh.idx).hom (Presieve.ofArrows.mk hh.idx)) := by
    rw [← hval hh.idx, map_map_apply, hfac A h hh]
  have h2 : x h hh = (extension P F).map (eqToHom hh.obj_idx.symm).op
      (x (f hh.idx).hom (Presieve.ofArrows.mk hh.idx)) := by
    have hcomp := hx (𝟙 A) (eqToHom hh.obj_idx.symm) hh (Presieve.ofArrows.mk hh.idx)
      (by rw [Category.id_comp]; exact (hfac A h hh).symm)
    rw [op_id, Functor.map_id_apply] at hcomp
    exact hcomp
  exact h1.trans h2.symm

end AlgebraicGeometry.ExtendingFunctors

end
