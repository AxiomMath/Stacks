module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Reasonable
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaRefinement

/-!
# Very reasonableness passes to the source of a representable morphism

Stacks 03KF says that each of the properties `(β)`, `(γ)`, `(δ)`, `(ε)` and `(θ)` of
Stacks 03JX passes from the target of a representable morphism of algebraic spaces to its
source. This file treats the case `(ε)`, very reasonableness: a presheaf admitting a
representable morphism to a very reasonable one is itself very reasonable.

Property `(ε)` asks for a jointly surjective family of étale charts by schemes whose two
self-intersection projections are quasi-compact, which is how
`AlgebraicGeometry.Space.IsVeryReasonableSpace` spells it. Neither presheaf is assumed to be an
algebraic space.

## Main results

* `CategoryTheory.IsPullback.pullbackFst` and `CategoryTheory.IsPullback.pullbackSnd`: in a
  cartesian square, each self-intersection projection of the base change is itself a base
  change of the corresponding self-intersection projection of the original morphism.
* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_isPullback`: a jointly surjective
  family of charts of the target of a morphism pulls back to a jointly surjective family of
  charts of its source.
* `AlgebraicGeometry.Space.isVeryReasonableSpace_of_relativelyRepresentable`: the case `(ε)`
  of Stacks 03KF.

## References

* [Stacks Project, Tag 03IH](https://stacks.math.columbia.edu/tag/03IH)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KF](https://stacks.math.columbia.edu/tag/03KF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category C] [HasPullbacks C] {T V X Y : C} {inc : T ⟶ V} {p : T ⟶ X}
    {ψ : V ⟶ Y} {f : X ⟶ Y}

/-- In a cartesian square with vertical maps `p : T ⟶ X` and `ψ : V ⟶ Y`, the first
projection of the self-intersection `T ×_X T` is a base change of the first projection of the
self-intersection `V ×_Y V` along `inc : T ⟶ V`. -/
theorem pullbackFst (h : IsPullback inc p ψ f) :
    IsPullback (pullback.map p p ψ ψ inc inc f h.w.symm h.w.symm) (pullback.fst p p)
      (pullback.fst ψ ψ) inc := by
  have hsnd : pullback.map p p ψ ψ inc inc f h.w.symm h.w.symm ≫ pullback.snd ψ ψ =
    pullback.snd p p ≫ inc := pullback.lift_snd _ _ _
  have hs := ((of_hasPullback p p).flip).paste_horiz h
  rw [← h.w, ← hsnd] at hs
  exact of_right hs (pullback.lift_fst _ _ _) (of_hasPullback ψ ψ).flip

/-- In a cartesian square with vertical maps `p : T ⟶ X` and `ψ : V ⟶ Y`, the second
projection of the self-intersection `T ×_X T` is a base change of the second projection of
the self-intersection `V ×_Y V` along `inc : T ⟶ V`. -/
theorem pullbackSnd (h : IsPullback inc p ψ f) :
    IsPullback (pullback.map p p ψ ψ inc inc f h.w.symm h.w.symm) (pullback.snd p p)
      (pullback.snd ψ ψ) inc := by
  have hfst : pullback.map p p ψ ψ inc inc f h.w.symm h.w.symm ≫ pullback.fst ψ ψ =
    pullback.fst p p ≫ inc := pullback.lift_fst _ _ _
  have hs := (of_hasPullback p p).paste_horiz h
  rw [← h.w, ← hfst] at hs
  exact of_right hs (pullback.lift_snd _ _ _) (of_hasPullback ψ ψ)

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A jointly surjective family of charts of the target of a morphism of presheaves on the
big fppf site of `S` pulls back to a jointly surjective family of charts of its source. -/
theorem isLocallySurjective_sigmaDesc_of_isPullback {I : Type u}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {U V : I → BigFppfOver B S hS}
    {ψ : ∀ i, yoneda.obj (V i) ⟶ Y} {inc : ∀ i, yoneda.obj (U i) ⟶ yoneda.obj (V i)}
    {p : ∀ i, yoneda.obj (U i) ⟶ X} (hp : ∀ i, IsPullback (inc i) (p i) (ψ i) f)
    (hcover : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc ψ)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc p) := by
  refine ⟨?_⟩
  intro T x
  apply (BigFppfOver.topology B S hS).superset_covering ?_
    (hcover.imageSieve_mem (f.app (op T) x))
  rintro T' g ⟨s, hs⟩
  obtain ⟨i, u, hsigma⟩ := Presheaf.exists_sigmaι_app_eq (fun i => yoneda.obj (V i)) (op T') s
  have hsection : (ψ i).app (op T') u = Y.map g.op (f.app (op T) x) := by
    rw [← hsigma] at hs
    change ((Sigma.ι (fun i => yoneda.obj (V i)) i ≫ Sigma.desc ψ).app (op T')) u = _ at hs
    simpa only [Sigma.ι_comp_desc, NatTrans.comp_app] using hs
  have hcomm : yonedaEquiv.symm u ≫ ψ i = yonedaEquiv.symm (X.map g.op x) ≫ f := by
    apply yonedaEquiv.injective
    simpa [yonedaEquiv_comp] using hsection
  refine ⟨(Sigma.ι (fun i => yoneda.obj (U i)) i).app (op T')
    (yonedaEquiv ((hp i).lift (yonedaEquiv.symm u) (yonedaEquiv.symm (X.map g.op x)) hcomm)), ?_⟩
  change ((Sigma.ι (fun i => yoneda.obj (U i)) i ≫ Sigma.desc p).app (op T')) _ = _
  rw [Sigma.ι_comp_desc, ← yonedaEquiv_comp, (hp i).lift_snd _ _ hcomm]
  simp

/-- Property `(ε)` of Stacks 03JX, very reasonableness, passes from the target of a representable
morphism of presheaves on the big fppf site of `S` to its source. -/
@[stacks 03KF "property_epsilon"]
theorem isVeryReasonableSpace_of_relativelyRepresentable
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f) (hY : IsVeryReasonableSpace B S hS Y) :
    IsVeryReasonableSpace B S hS X := by
  obtain ⟨I, V, ψ, hcover, hψ⟩ := hY
  set U : I → BigFppfOver B S hS := fun i => hf.pullback (ψ i)
  set inc : ∀ i, yoneda.obj (U i) ⟶ yoneda.obj (V i) :=
    fun i => yoneda.map (hf.snd (ψ i))
  set p : ∀ i, yoneda.obj (U i) ⟶ X := fun i => hf.fst (ψ i)
  have hp : ∀ i, IsPullback (inc i) (p i) (ψ i) f := fun i => (hf.isPullback (ψ i)).flip
  have hEtale : ∀ i, IsEtale B S hS (p i) := fun i =>
    (isEtale_iff_presheaf_of_yoneda B S hS (p i)).2
      ((MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))).of_isPullback (hp i)
        ((isEtale_iff_presheaf_of_yoneda B S hS (ψ i)).1 (hψ i).1))
  exact ⟨I, U, p, isLocallySurjective_sigmaDesc_of_isPullback B S hS hp hcover,
    fun i => ⟨hEtale i, isQuasiCompact_of_isPullback B S hS (hp i).pullbackFst (hψ i).2.1,
      isQuasiCompact_of_isPullback B S hS (hp i).pullbackSnd (hψ i).2.2⟩⟩

end AlgebraicGeometry.Space

end
