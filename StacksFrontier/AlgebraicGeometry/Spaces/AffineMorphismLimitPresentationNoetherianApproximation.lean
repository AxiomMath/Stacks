module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeAlgebraSectionsCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasicoherentAlgebraFinitePresentationOfApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecLimit

/-!
# Stacks 0870 from absolute Noetherian approximation

Stacks 0870: an affine morphism `f : X ⟶ Y` of algebraic spaces with `Y` quasi-compact and
quasi-separated presents `X` as a directed limit `X = lim X_i` of algebraic spaces affine and of
finite presentation over `Y`.  The source's proof: write `f_* 𝒪_X = colim 𝒜_i` with `𝒜_i` of
finite presentation (Stacks 082A) and set `X_i = \underline{Spec}_Y(𝒜_i)` (Stacks 081W); "by
construction" these are affine and of finite presentation over `Y`, and `X = lim X_i`.

## Main results

* `AlgebraicGeometry.Space.exists_directed_limit_of_isAffineHom_of_noetherianApproximation`:
  Stacks 0870, with one argument beyond the tag's hypotheses, absolute Noetherian approximation
  over `Spec ℤ` (`h07SU`, Stacks 07SU), from which Stacks 082A is, in the namespace
  `AlgebraicGeometry.Space`,
  `exists_directed_isColimit_isFinitePresentation_quasicoherentAlgebra_of_noetherianApproximation`.

## Implementation notes

Stacks 081V is used in the corrected form of this library: the direct image is an
anti-equivalence onto the quasi-coherent algebras with fewer sections than the cutoff of the site
over every étale chart (`AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor`).
The algebras `𝒜_i` lie in that target because they are of finite type
(`AlgebraicGeometry.Space.AlgebraSheaf.sectionsBelowCutoff_of_isFinitePresentation`), and so does
`f_* 𝒪_X`, as a direct image.

The two "by construction" steps are proved, not carried: that the relative spectrum of an
algebra of finite presentation is of finite presentation is
`AlgebraicGeometry.Space.isFinitePresentation_of_pushforwardAlgebraIso`, and that the relative
spectrum turns the colimit of Stacks 082A into a limit of presheaves over `Y` is
`AlgebraicGeometry.Space.isLimitAffineOverToOverMapCone`.  The latter needs the colimit of
Stacks 082A as a colimit of algebra sheaves, which is what the source asserts and the form in
which Stacks 082A is proved here.

No `@[stacks]` attribute is attached: the argument `h07SU` is the statement of a tag not yet
proved here, and the registration is one application of this theorem once that tag is proved.

## References

* [Stacks Project, Tag 0870](https://stacks.math.columbia.edu/tag/0870)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A colimit cocone `L` stays a colimit after a functor `G` followed by a functor `P` with
`G ⋙ P ≅ 𝟭`, read through the same functors `ι₁ ⋙ ι₂`. -/
def isColimitMapCoconeOfCompIsoId {J C D E E' : Type*} [Category J] [Category C] [Category D]
    [Category E] [Category E'] {F : J ⥤ C} (L : Cocone F) (G : C ⥤ D) (P : D ⥤ C) (ι₁ : C ⥤ E)
    (ι₂ : E ⥤ E') (ε : G ⋙ P ≅ 𝟭 C) (h : IsColimit ((ι₁ ⋙ ι₂).mapCocone L)) :
    IsColimit (ι₂.mapCocone ((P ⋙ ι₁).mapCocone (G.mapCocone L))) :=
  IsColimit.mapCoconeEquiv
    ((Functor.leftUnitor _).symm ≪≫ (Functor.isoWhiskerRight ε _).symm ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G (Functor.associator _ _ _).symm) h

/-- **Stacks 0870**, granted Stacks 07SU over `Spec ℤ` (`h07SU`).  An affine morphism
`f : X ⟶ Y` of algebraic spaces over `S` with `Y` quasi-compact and quasi-separated presents `X`
as a directed limit `X = lim X_i` of algebraic spaces `X_i` which are affine and of finite
presentation over `Y`: `t` is the family of structure morphisms `X_i ⟶ Y`, `p` the family of
projections `X ⟶ X_i`, each composing with `t` to `f`, and `X` is the limit of the underlying
presheaves. -/
theorem exists_directed_limit_of_isAffineHom_of_noetherianApproximation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsAffineHom B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (t : D ⟶ (Functor.const Iᵒᵖ).obj Y) (p : (Functor.const Iᵒᵖ).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) ∧
        (∀ i, IsAffineHom B S hS (t.app i)) ∧
          (∀ i, IsFinitePresentation B S hS (t.app i)) ∧
            ∀ i, p.app i ≫ t.app i = f := by
  classical
  set Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩ with hY'
  set X' : AlgebraicSpaces B S hS := ⟨X, hX⟩ with hX'
  set Z : AffineOver B S hS Y' :=
    ⟨Over.mk (ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := X') (Y := Y') f),
      hf⟩ with hZ
  set A : QuasicoherentAlgebra B S hS Y' :=
    (quasicoherentPushforwardAlgebraFunctor B S hS Y').obj (op Z) with hA
  obtain ⟨I, hIpre, hIne, hIdir, D, φ, ⟨hcolim⟩, hDfp⟩ :=
    exists_directed_isColimit_isFinitePresentation_quasicoherentAlgebra_of_noetherianApproximation
      B S hS B.contains_terminal h07SU Y' A hYqc hYqs
  let _ : Preorder I := hIpre
  let _ : Nonempty I := hIne
  let _ : IsDirected I (· ≤ ·) := hIdir
  -- the corrected anti-equivalence of Stacks 081V, and the algebras lifted to its target
  have := isEquivalence_boundedPushforwardAlgebraFunctor B S hS Y'
  set EQ := (boundedPushforwardAlgebraFunctor B S hS Y').asEquivalence with hEQ
  let Db : I ⥤ BoundedQuasicoherentAlgebra B S hS Y' :=
    ObjectProperty.lift _ D fun i =>
      AlgebraSheaf.sectionsBelowCutoff_of_isFinitePresentation B S hS _ (hDfp i)
  let Lb : Cocone Db :=
    { pt := (boundedPushforwardAlgebraFunctor B S hS Y').obj (op Z)
      ι :=
        { app := fun i => ObjectProperty.homMk (φ.app i)
          naturality := fun i j g => ObjectProperty.hom_ext _ (φ.naturality g) } }
  set DA : Iᵒᵖ ⥤ AffineOver B S hS Y' := (Db ⋙ EQ.inverse).leftOp with hDA
  set K := EQ.inverse.mapCocone Lb with hK
  set c0 : Cone DA := coneLeftOpOfCocone K with hc0
  have hcolimB : IsColimit ((boundedQuasicoherentAlgebraInclusion B S hS Y' ⋙
      quasicoherentAlgebraInclusion B S hS Y').mapCocone Lb) := hcolim
  have hKE : IsColimit ((quasicoherentAlgebraInclusion B S hS Y').mapCocone
      ((quasicoherentPushforwardAlgebraFunctor B S hS Y').mapCocone K)) := by
    rw [← boundedPushforwardAlgebraFunctor_comp_ι]
    exact isColimitMapCoconeOfCompIsoId Lb EQ.inverse _ _ _
      (Functor.isoWhiskerLeft _ (eqToIso (Functor.asEquivalence_functor _)).symm ≪≫
        EQ.counitIso) hcolimB
  have hpre0 : IsLimit ((affineOverToOver B S hS Y').mapCone c0) :=
    isLimitAffineOverToOverMapCone K hKE
  set eZ : Z ≅ c0.pt := (EQ.unitIso.app (op Z)).unop.symm with heZ
  set cu : Cone DA := c0.extend eZ.hom with hcu
  have hpre : IsLimit ((affineOverToOver B S hS Y').mapCone cu) :=
    IsLimit.ofIsoLimit hpre0 (Cone.ext ((affineOverToOver B S hS Y').mapIso eZ).symm
      (fun j => by
        change (affineOverToOver B S hS Y').map (c0.π.app j) =
          (affineOverToOver B S hS Y').map eZ.inv ≫
            (affineOverToOver B S hS Y').map (eZ.hom ≫ c0.π.app j)
        rw [← Functor.map_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]))
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  have hw : ∀ {U V : AffineOver B S hS Y'} (g : U ⟶ V),
      g.hom.left.hom ≫ V.obj.hom.hom = U.obj.hom.hom := fun g => by
    have h := congrArg (fun k => k.hom) (Over.w g.hom)
    rwa [ObjectProperty.FullSubcategory.comp_hom] at h
  set Dp : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    DA ⋙ affineOverToOver B S hS Y' ⋙ Over.forget Y'.obj with hDp
  set t : Dp ⟶ (Functor.const Iᵒᵖ).obj Y :=
    { app := fun i => (DA.obj i).obj.hom.hom
      naturality := fun i j g => by
        exact (hw (DA.map g)).trans (Category.comp_id _).symm } with ht
  set p : (Functor.const Iᵒᵖ).obj X ⟶ Dp :=
    { app := fun i => (cu.π.app i).hom.left.hom
      naturality := fun i j g => by
        have h := congrArg (fun k : Z ⟶ DA.obj j => k.hom.left.hom) (cu.w g)
        simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left] at h
        change 𝟙 X ≫ (cu.π.app j).hom.left.hom =
          (cu.π.app i).hom.left.hom ≫ (DA.map g).hom.left.hom
        rw [Category.id_comp]
        exact h.symm } with hp
  refine ⟨I, hIpre, hIne, hIdir, Dp, t, p,
    isLimitOfPreserves (Over.forget Y'.obj) hpre, fun i => (DA.obj i).obj.left.property,
    fun i => (DA.obj i).property, fun i => ?_, fun i => ?_⟩
  · obtain ⟨i⟩ := i
    exact isFinitePresentation_of_pushforwardAlgebraIso (D.obj i) (DA.obj (op i))
      ((boundedQuasicoherentAlgebraInclusion B S hS Y' ⋙
        quasicoherentAlgebraInclusion B S hS Y').mapIso (EQ.counitIso.app (Db.obj i)))
      hYqc (hDfp i)
  · exact hw (cu.π.app i)

end AlgebraicGeometry.Space
