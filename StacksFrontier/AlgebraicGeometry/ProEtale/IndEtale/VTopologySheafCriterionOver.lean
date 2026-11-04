module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.VTopologySheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.SheavesOver
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves for the V topology on the schemes over a base

A functor on the category `Sch/S` of all schemes over a base scheme `S` which satisfies the sheaf
condition for every covering family of `Sch/S` that is locally of finite presentation and a V
covering, and which turns cofiltered inverse limits of affine schemes over `S` into filtered
colimits of sets, satisfies the sheaf condition for every V covering of `Sch/S`.

This is the relative form of Stacks 0EVQ.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.exists_affineSystem_over_of_isStandardVCovering_singleton`
  presents a morphism of `Sch/S` between objects with affine underlying scheme which is a standard
  V covering as a cofiltered inverse limit, over its target, of objects of `Sch/S` with affine
  underlying scheme whose structure morphisms are locally of finite presentation and are V
  coverings. This is the relative form of Stacks 0EVP.
* `AlgebraicGeometry.ExtendingFunctors.isVSheafOver_of_isSheafFor_vCovering_of_isLimitPreserving`
  is the sheaf criterion itself.

## References

* [Stacks Project, Tag 0EVQ](https://stacks.math.columbia.edu/tag/0EVQ)
* [Stacks Project, Tag 0EVP](https://stacks.math.columbia.edu/tag/0EVP)
* [Stacks Project, Tag 0ETM](https://stacks.math.columbia.edu/tag/0ETM)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u v

namespace AlgebraicGeometry.ExtendingFunctors

variable {S : Scheme.{u}}

/-! ### Limits of `Sch/S` -/

/-- The underlying scheme of a fibre product of `Sch/S` is affine as soon as the fibre product of
the underlying schemes is. -/
theorem isAffine_left_pullback {A B C : Over S} (g : A ⟶ C) (h : B ⟶ C)
    [IsAffine (Limits.pullback g.left h.left)] :
    IsAffine (Limits.pullback g h).left := by
  have hpb : IsPullback (Limits.pullback.fst g h).left (Limits.pullback.snd g h).left
      g.left h.left := (IsPullback.of_hasPullback g h).map (Over.forget S)
  exact IsAffine.of_isIso hpb.isoPullback.hom

/-! ### The relative form of Stacks 0EVP -/

/-- **The relative form of Stacks 0EVP.** A morphism of `Sch/S` between objects with affine
underlying scheme whose underlying morphism of schemes is a standard V covering is a cofiltered
inverse limit, over its target, of objects of `Sch/S` with affine underlying scheme whose
structure morphisms are locally of finite presentation and are themselves V coverings. -/
theorem exists_affineSystem_over_of_isStandardVCovering_singleton {Y X : Over S}
    (hY : IsAffine Y.left) (hX : IsAffine X.left) (f : X ⟶ Y)
    (hStd : IsStandardVCovering (fun _ : Unit ↦ X.left) (fun _ ↦ f.left)) :
    ∃ (J : Type u) (_ : Category.{u} J) (_ : IsCofiltered J) (D : J ⥤ Over S)
      (t : D ⟶ (Functor.const J).obj Y) (p : (Functor.const J).obj X ⟶ D)
      (_ : IsLimit (Cone.mk X p)),
      (∀ i, IsAffine (D.obj i).left) ∧ p ≫ t = (Functor.const J).map f ∧
        (∀ i, LocallyOfFinitePresentation (t.app i).left) ∧
        ∀ i, IsVCoveringOver (fun _ : Unit ↦ t.app i) := by
  let _ : IsAffine X.left := hX
  let _ : IsAffine Y.left := hY
  obtain ⟨J, hJ, hJcof, D₀, t₀, p₀, hlim, haff, hcompat, hlfp, hV⟩ :=
    exists_affineSystem_of_isStandardVCovering_singleton f.left hStd
  let _ : Category.{u} J := hJ
  let _ : IsCofiltered J := hJcof
  let _ : IsConnected J := IsCofiltered.isConnected J
  have hnat : ∀ {i j : J} (α : i ⟶ j), D₀.map α ≫ t₀.app j = t₀.app i := by simp
  have hpt : ∀ i, p₀.app i ≫ t₀.app i = f.left := fun i ↦ by
    simpa using NatTrans.congr_app hcompat i
  have hfw : f.left ≫ Y.hom = X.hom := Over.w f
  let D : J ⥤ Over S :=
    { obj := fun i ↦ Over.mk (t₀.app i ≫ Y.hom)
      map := fun {i j} α ↦ Over.homMk (D₀.map α) (by
        show D₀.map α ≫ t₀.app j ≫ Y.hom = t₀.app i ≫ Y.hom
        rw [← Category.assoc, hnat α])
      map_id := fun i ↦ by apply Over.OverMorphism.ext; simp
      map_comp := fun α β ↦ by apply Over.OverMorphism.ext; simp }
  let t : D ⟶ (Functor.const J).obj Y :=
    { app := fun i ↦ Over.homMk (t₀.app i)
      naturality := fun i j α ↦ by
        apply Over.OverMorphism.ext
        show D₀.map α ≫ t₀.app j = t₀.app i ≫ 𝟙 Y.left
        exact (hnat α).trans (Category.comp_id (t₀.app i)).symm }
  let p : (Functor.const J).obj X ⟶ D :=
    { app := fun i ↦ Over.homMk (p₀.app i) (by
        show p₀.app i ≫ t₀.app i ≫ Y.hom = X.hom
        rw [← Category.assoc, hpt i, hfw])
      naturality := fun i j α ↦ by
        apply Over.OverMorphism.ext
        show 𝟙 X.left ≫ p₀.app j = p₀.app i ≫ D₀.map α
        exact p₀.naturality α }
  refine ⟨J, hJ, hJcof, D, t, p, isLimitOfReflects (Over.forget S) hlim,
    fun i ↦ haff i, ?_, fun i ↦ hlfp i, fun i ↦ hV i⟩
  ext i
  exact hpt i

/-! ### The relative form of Stacks 0EVQ -/

/-- A functor on the schemes over `S` which satisfies the sheaf condition for every h covering
of `Sch/S` and which is limit preserving in the sense of Stacks 05LX satisfies the sheaf condition
for every V covering of `Sch/S`.

The h coverings are taken in the form of the second of the two equivalent conditions of
Stacks 0ETR: the hypothesis `hH` is the sheaf condition for the families of morphisms which are
locally of finite presentation and are V coverings. -/
@[stacks 0EVQ "the relative form, for a contravariant functor on the category of all schemes over \
`S`, which is how the source states it. The sheaf property for the h topology is read, as in the \
absolute case, through the second of the two equivalent conditions of Stacks 0ETR: the hypothesis \
is the sheaf condition for the families which are locally of finite presentation and are V \
coverings. Stacks 0ETR, `AlgebraicGeometry.isPHCovering_iff_isVCovering`, is what identifies \
that hypothesis with the ph reading fixed by `AlgebraicGeometry.IsHCovering`; it is proved in \
this library, further down the import graph than this file"]
theorem isVSheafOver_of_isSheafFor_vCovering_of_isLimitPreserving (F : (Over S)ᵒᵖ ⥤ Type w)
    (hH : ∀ (T : Over S) (I : Type (max u v)) (X : I → Over S) (g : ∀ i, X i ⟶ T),
      (∀ i, LocallyOfFinitePresentation (g i).left) → IsVCoveringOver g →
        (Presieve.ofArrows X g).IsSheafFor F)
    (hLP : Scheme.IsLimitPreserving S F) :
    IsVSheafOver.{w, u, max u v} F := by
  have hZar : IsZariskiCoverSheafOver.{w, u, max u v} F := by
    intro T 𝒰
    refine hH T 𝒰.I₀ _ _ (fun i ↦ ?_) (isVCoveringOver_openCover 𝒰)
    have := 𝒰.map_prop i
    show LocallyOfFinitePresentation (𝒰.f i)
    infer_instance
  rw [isVSheafOver_iff_zariski_and_standard.{w, u, v} F]
  refine ⟨hZar, (isStandardVSheafOver_iff_singleton.{w, u, v} F hZar).mpr ?_⟩
  intro Y X hY hX f hstd
  let _ : IsAffine Y.left := hY
  let _ : IsAffine X.left := hX
  obtain ⟨J, hJ, hJcof, D, t, p, hlim, haff, hcompat, hlfp, hV⟩ :=
    exists_affineSystem_over_of_isStandardVCovering_singleton hY hX f hstd
  let _ : Category.{u} J := hJ
  let _ : IsCofiltered J := hJcof
  have hne : Nonempty J := IsCofiltered.nonempty
  let _ : ∀ i, IsAffine (D.obj i).left := haff
  have hfi : ∀ i, (Cone.mk X p).π.app i ≫ t.app i = f := fun i ↦ by
    simpa using NatTrans.congr_app hcompat i
  have hstage : ∀ i, (Presieve.singleton (t.app i)).IsSheafFor F := by
    intro i
    have h := hH Y (ULift.{max u v} Unit) (fun _ ↦ D.obj i) (fun _ ↦ t.app i)
      (fun _ ↦ hlfp i) (isVCovering_const_of_isVCovering (t.app i).left (hV i) _)
    rwa [ofArrows_const_eq_singleton] at h
  have hsqaff : ∀ i, IsAffine ((RelativeSquares.squareDiagram t).obj i).left := fun i ↦ by
    have : IsAffine (((Functor.const J).obj Y).obj i).left := hY
    exact isAffine_left_pullback (t.app i) (t.app i)
  have hcol : IsColimit (F.mapCocone (Cone.mk X p).op) :=
    Classical.choice ((hLP J D haff).preserves hlim.op)
  have hsq : IsColimit (F.mapCocone (RelativeSquares.squareCone t (Cone.mk X p) f hfi).op) :=
    Classical.choice ((hLP J (RelativeSquares.squareDiagram t) hsqaff).preserves
      (RelativeSquares.isLimitSquareCone t (Cone.mk X p) f hfi hlim).op)
  rw [ofArrows_const_eq_singleton f Unit]
  exact RelativeSquares.isSheafFor_singleton_of_isColimit t (Cone.mk X p) f hfi F hcol hsq hstage

end AlgebraicGeometry.ExtendingFunctors
