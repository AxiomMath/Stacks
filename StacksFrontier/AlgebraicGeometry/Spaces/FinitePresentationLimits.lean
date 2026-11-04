module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving

/-!
# Limit preservation for representable presheaves of finite presentation

A presheaf on the big fppf site of `S` is *limit preserving* when it turns a cofiltered
inverse limit of affine schemes into a filtered colimit of sets. For a presheaf represented
by an object `A` of the slice over a site object `Z`, this is the assertion that every
`Z`-morphism from the limit factors, essentially uniquely, through a member of the inverse
system; it holds as soon as the underlying scheme morphism of `A` is locally of finite
presentation.

## Main results

* `AlgebraicGeometry.limitPreserving_yoneda_of_locallyOfFinitePresentation`: a representable
  presheaf on the slice of the big fppf site over `Z`, represented by an object whose
  underlying scheme morphism to `Z` is locally of finite presentation, is limit preserving
  for index categories in the universe of the schemes.

## Implementation notes

This is the representable case of Stacks 04AK, which characterizes locally-of-finite-presentation
morphisms of algebraic spaces by relative limit preservation. The biconditional of Stacks 04AK
itself is not proved in this file; it is proved as
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_iff_relativelyLimitPreserving`, at index
universes equal to the universe of the schemes, which is the restriction discussed below.

The content of the result is Mathlib's `AlgebraicGeometry.Scheme.preservesColimit_yoneda`,
transported along the fully faithful comparison functor from the slice of the big fppf site
over `Z` to the slice of all schemes over the underlying scheme of `Z`. The comparison is the
composite of `CategoryTheory.Over.iteratedSliceEquiv` with `CategoryTheory.Over.post` of the
site's inclusion into schemes, which is fully faithful because that inclusion is. The limit
hypothesis of `AlgebraicGeometry.LimitPreserving` is a limit of underlying schemes, so it is
first reflected into the slice over the underlying scheme of `Z`; the shape of the diagram is
cofiltered, hence nonempty, which is all that reflection along `CategoryTheory.Over.forget`
needs.

The index universes are those of the schemes. Mathlib's inverse-limit API for schemes with
affine transition maps is stated for an index category `I : Type u` with `Category.{u} I`
where `u` is the universe of the schemes, while
`AlgebraicGeometry.LimitPreserving.{u, v, w, w'}` quantifies over `I : Type (max w w')` with
`Category.{w'} I`. The two agree exactly when `w = w' = u`, which is the form proved here, and
this is why Stacks 04AK is formalized at that index size rather than at free index universes: its
relative-limit-preservation side read at the larger index universes `max u w` and `max u w'`
does not follow from this result.

## References

* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A cone in a slice category is limiting as soon as its image under the forgetful functor
is, provided the shape of the diagram is nonempty. -/
private def isLimitOfIsLimitForget {C : Type*} [Category* C] {J : Type*} [Category* J]
    [Nonempty J] {W : C} {D : J ⥤ Over W} (c : Cone D)
    (hc : IsLimit ((Over.forget W).mapCone c)) : IsLimit c where
  lift t := Over.homMk (hc.lift ((Over.forget W).mapCone t)) (by
    obtain ⟨j⟩ := ‹Nonempty J›
    have h1 : hc.lift ((Over.forget W).mapCone t) ≫ (c.π.app j).left = (t.π.app j).left :=
      hc.fac ((Over.forget W).mapCone t) j
    have h2 : (c.π.app j).left ≫ (D.obj j).hom = c.pt.hom := Over.w (c.π.app j)
    have h3 : (t.π.app j).left ≫ (D.obj j).hom = t.pt.hom := Over.w (t.π.app j)
    rw [← h2, ← Category.assoc, h1, h3])
  fac t j := by ext; exact hc.fac ((Over.forget W).mapCone t) j
  uniq t m hm := by
    ext
    exact hc.uniq ((Over.forget W).mapCone t) m.left fun j ↦ congrArg (·.left) (hm j)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison functor from the slice of the big fppf site over `Z` to the slice of all
schemes over the underlying scheme of `Z`. -/
private noncomputable def sliceToSchemeOver (Z : BigFppfOver B S hS) :
    Over Z ⥤ Over ((BigFppfOver.toScheme B S hS).obj Z) :=
  (Over.iteratedSliceEquiv Z).functor ⋙ Over.post B.inclusion

private instance (Z : BigFppfOver B S hS) : (sliceToSchemeOver B S hS Z).Full := by
  dsimp only [sliceToSchemeOver]
  exact Functor.Full.comp _ _

private instance (Z : BigFppfOver B S hS) : (sliceToSchemeOver B S hS Z).Faithful := by
  dsimp only [sliceToSchemeOver]
  exact Functor.Faithful.comp _ _

/-- The comparison functor of `AlgebraicGeometry.sliceToSchemeOver`, as full faithfulness
data. -/
private noncomputable def sliceToSchemeOverFullyFaithful (Z : BigFppfOver B S hS) :
    (sliceToSchemeOver B S hS Z).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- Full faithfulness of the comparison functor, as an identification of the presheaf
represented by `A` with the restriction of the presheaf represented by its image. -/
private noncomputable def yonedaCompIso (Z : BigFppfOver B S hS) (A : Over Z) :
    (sliceToSchemeOver B S hS Z).op ⋙ yoneda.obj ((sliceToSchemeOver B S hS Z).obj A) ≅
      yoneda.obj A :=
  NatIso.ofComponents
    (fun W ↦ Equiv.toIso
      ((sliceToSchemeOverFullyFaithful B S hS Z).homEquiv (X := W.unop) (Y := A)).symm)
    (by
      intro W W' g
      ext (x : (sliceToSchemeOver B S hS Z).obj W.unop ⟶ (sliceToSchemeOver B S hS Z).obj A)
      apply (sliceToSchemeOver B S hS Z).map_injective
      simp [sliceToSchemeOverFullyFaithful, Functor.FullyFaithful.homEquiv])

/-- The identification of `AlgebraicGeometry.yonedaCompIso` undoes the comparison functor. -/
private lemma map_yonedaCompIso_hom_app (Z : BigFppfOver B S hS) (A : Over Z) (W : (Over Z)ᵒᵖ)
    (x : (sliceToSchemeOver B S hS Z).obj W.unop ⟶ (sliceToSchemeOver B S hS Z).obj A) :
    (sliceToSchemeOver B S hS Z).map ((yonedaCompIso B S hS Z A).hom.app W x) = x :=
  (sliceToSchemeOverFullyFaithful B S hS Z).map_preimage x

/-- The presheaf on the slice of the big fppf site over `Z` represented by an object `A`
whose underlying scheme morphism to `Z` is locally of finite presentation is limit
preserving, for index categories in the universe of the schemes. -/
theorem limitPreserving_yoneda_of_locallyOfFinitePresentation (Z : BigFppfOver B S hS)
    (A : Over Z)
    (hA : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map A.hom)) :
    LimitPreserving.{u, u, u, u, u + 1, u}
      (Over.forget Z ⋙ BigFppfOver.toScheme B S hS) (yoneda.obj A) := by
  intro I _ _ D c hc hDaff hcaff
  have : Nonempty I := IsCofiltered.nonempty
  have : ∀ i, IsAffine ((D ⋙ sliceToSchemeOver B S hS Z).obj i).left := hDaff
  have : IsAffine ((sliceToSchemeOver B S hS Z).mapCone c).pt.left := hcaff
  have : ∀ i, CompactSpace ((D ⋙ sliceToSchemeOver B S hS Z).obj i).left := fun _ ↦ inferInstance
  have : ∀ i, QuasiSeparatedSpace ((D ⋙ sliceToSchemeOver B S hS Z).obj i).left :=
    fun _ ↦ inferInstance
  have : ∀ {i j : I} (g : i ⟶ j),
      IsAffineHom ((D ⋙ sliceToSchemeOver B S hS Z).map g).left := fun _ ↦ inferInstance
  have : LocallyOfFinitePresentation ((sliceToSchemeOver B S hS Z).obj A).hom := hA
  have hc' : IsLimit ((Over.forget ((BigFppfOver.toScheme B S hS).obj Z)).mapCone
      ((sliceToSchemeOver B S hS Z).mapCone c)) := hc
  obtain ⟨key⟩ := (Scheme.preservesColimit_yoneda (D ⋙ sliceToSchemeOver B S hS Z)
    ((sliceToSchemeOver B S hS Z).obj A)).preserves (isLimitOfIsLimitForget _ hc').op
  refine ⟨(IsColimit.precomposeHomEquiv
      (Functor.isoWhiskerLeft D.op (yonedaCompIso B S hS Z A)) _)
    (IsColimit.ofIsoColimit key (Cocone.ext
      ((yonedaCompIso B S hS Z A).app (Opposite.op c.pt)) ?_))⟩
  intro j
  ext (x : (sliceToSchemeOver B S hS Z).obj (D.obj j.unop) ⟶
    (sliceToSchemeOver B S hS Z).obj A)
  apply (sliceToSchemeOver B S hS Z).map_injective
  simp only [Functor.comp_obj, Over.forget_obj, ObjectProperty.ι_obj, Cone.op_pt, Functor.op_obj,
    yoneda_obj_obj, Functor.isoWhiskerLeft_hom, Cocone.precompose_obj_pt, Functor.mapCocone_pt,
    Functor.mapCone_pt, Functor.mapCocone_ι_app, Cone.op_ι, NatTrans.op_app, Functor.const_obj_obj,
    Functor.mapCone_π_app, yoneda_obj_map, Quiver.Hom.unop_op, Iso.app_hom,
    TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp]
  rw [map_yonedaCompIso_hom_app, map_yonedaCompIso_hom_app]

end AlgebraicGeometry

end
