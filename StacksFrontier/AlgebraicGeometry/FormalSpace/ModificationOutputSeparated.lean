module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSeparated
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputProper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperAffineCriterion
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism

/-!
# Separated finite-type modifications and their completions (Stacks 0ARW)

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be a closed subset and `U ⊆ X` its open complement. **Stacks 0ARW**
says that a finite-type modification `f : X' ⟶ X` of `X` outside `U`, corresponding under the
completion functor of Stacks 0AR5 (Theorem 0ARB) to a rig-étale `g : W ⟶ X_{/T}` with `W` a
locally Noetherian formal algebraic space, is separated exactly when `g` is separated and its
relative diagonal `Δ_g : W ⟶ W ×_{X_{/T}} W` is rig-surjective.

## Main results

All names below live in the namespace `AlgebraicGeometry.FormalSpace`.

* `isSeparated_iff_isSeparatedMorphism_and_isRigSurjective_diagonal_of_iso`: **Stacks 0ARW**.
* `isSeparated_of_isSeparatedMorphism_completionSheafMap`: the converse implication, for the
  completion `f_{/T}` itself.
* `isSeparated_pullback_snd_of_isSeparatedMorphism_completionSheafMap`: if `f_{/T}` is
  separated, the base change of `f` along a scheme all of whose points lie over `T` is separated
  (the use of Formal Spaces, Lemma 0ARS in Case II of the source).

## Implementation notes

The correspondence `f ↔ g` is rendered exactly as for Stacks 0ARX in
`StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputProper`: as an isomorphism over
`X_{/T}` between `f_{/T}`, the image of `f` under the completion functor of Stacks 0AR5, and an
object `g` of the right-hand category of Stacks 0AR5. Separatedness of `g` is part (1) of
Stacks 0ARN, the separatedness axiom: the relative diagonal is a closed immersion of formal
algebraic spaces (Stacks 0ANP).

The direct implication is Stacks 0GDG and Stacks 0GDI. For the converse the source first
reduces to an affine `X` and invokes Stacks 0ARV for quasi-separatedness of `f`. Here no
reduction is needed: over every affine scheme `V ⟶ X` with image in `T` the base change of `f`
is separated, being by Stacks 0APV a base change of `g` read through the agreement of the two
notions of closed immersion, and quasi-separatedness of `f` then follows as in
`AlgebraicGeometry.FormalSpace.isQuasiSeparated_of_isSeparated_pullback_snd`. Separatedness of
`f` is reduced by Stacks 0ARJ and Remark 0ARL to uniqueness of dotted arrows over complete
discrete valuation rings `R`, and the three cases of the source are
`AlgebraicGeometry.FormalSpace.unique_lift_of_range_subset_compl` (Case I),
`AlgebraicGeometry.FormalSpace.subsingleton_lift_of_isSeparated_pullback_snd` (Case II) and
`AlgebraicGeometry.FormalSpace.subsingleton_lift_of_iff_closedPoint` (Case III, through
Stacks 0GBA (2), 0APV, 0AR0 and 0AQH).

## References

* [Stacks Project, Tag 0ARW](https://stacks.math.columbia.edu/tag/0ARW)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 0GDG](https://stacks.math.columbia.edu/tag/0GDG)
* [Stacks Project, Tag 0GDI](https://stacks.math.columbia.edu/tag/0GDI)
* [Stacks Project, Tag 0ARJ](https://stacks.math.columbia.edu/tag/0ARJ)
* [Stacks Project, Tag 0ARL](https://stacks.math.columbia.edu/tag/0ARL)
* [Stacks Project, Tag 0ARS](https://stacks.math.columbia.edu/tag/0ARS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- A separated morphism of fppf sheaves on the big fppf site of `S`, in the sense of
Stacks 0ARN, has separated underlying morphism of presheaves in the universe-lifted sense: the
underlying morphism of the relative diagonal is a closed immersion along the universe-lifted
Yoneda embedding, and it is the relative diagonal of the underlying morphism up to the
comparison isomorphism of fibre products. -/
theorem isSeparatedULift_hom_of_isSeparatedMorphism {W Y : FppfSheaf B S hS} (g : W ⟶ Y)
    (hg : IsSeparatedMorphism B S hS g) : Space.IsSeparatedULift.{u + 1} B S hS g.hom := by
  let L := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let R := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have h1 : R.relative uliftYoneda.{u + 1} (L.map (pullback.diagonal g)) :=
    (relative_fppfYoneda_iff_uliftYoneda B S hS R _).mp
      ((isClosedImmersion_iff_relative B S hS _).mp hg)
  have hdiag : pullback.diagonal (L.map g) =
      L.map (pullback.diagonal g) ≫ (PreservesPullback.iso L g g).hom := by
    apply pullback.hom_ext <;> simp [← L.map_comp]
  show R.relative uliftYoneda.{u + 1} (pullback.diagonal (L.map g))
  rw [hdiag]
  exact ((R.relative uliftYoneda.{u + 1}).cancel_right_of_respectsIso _ _).mpr h1

/-- **Separatedness over the closed set, read off a separated completion.** Let `f : X' ⟶ X` be
a morphism of algebraic spaces whose completion `f_{/T} : X'_{/T'} ⟶ X_{/T}` along a set `T` of
points of `X` is separated. Then the base change of `f` along every morphism `v : V ⟶ X` from a
scheme of the site whose points all lie in `T` is a separated morphism of algebraic spaces.

By the completion square of Stacks 0APV the base change of `f_{/T}` along the point of `X_{/T}`
defined by `v` is the universe lift of `X' ×_X V ⟶ V`; separatedness of `f_{/T}` is read on
underlying presheaves by
`AlgebraicGeometry.FormalSpace.isSeparatedULift_hom_of_isSeparatedMorphism`, is stable under
base change, and descends from the universe lift by
`AlgebraicGeometry.Space.isSeparatedULift_whiskerRight_iff`. -/
theorem isSeparated_pullback_snd_of_isSeparatedMorphism_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hg : IsSeparatedMorphism B S hS (Space.completionSheafMap B S hS f T))
    (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ X)
    (hv : Space.HasImageIn B S hS X T V (yonedaEquiv v)) :
    Space.IsSeparated B S hS (pullback.snd f v) := by
  obtain ⟨ξ, e, he⟩ := exists_iso_pullback_completionSheafMap hX' hX f T V v hv
  have h1 : Space.IsSeparatedULift.{u + 1} B S hS
      (pullback.fst ξ (Space.completionSheafMap B S hS f T).hom) :=
    Space.isSeparatedULift_of_isPullback.{u + 1} B S hS (IsPullback.of_hasPullback ξ _).flip
      (isSeparatedULift_hom_of_isSeparatedMorphism _ hg)
  have heq : Functor.whiskerRight (pullback.snd f v) uliftFunctor.{u + 1} =
      e.inv ≫ pullback.fst ξ (Space.completionSheafMap B S hS f T).hom :=
    (e.inv_hom_id_assoc _).symm.trans (congrArg (e.inv ≫ ·) he)
  have h2 : Space.IsSeparatedULift.{u + 1} B S hS
      (Functor.whiskerRight (pullback.snd f v) uliftFunctor.{u + 1}) :=
    Space.isSeparatedULift_of_isPullback.{u + 1} B S hS
      (IsPullback.of_horiz_isIso (fst := e.inv) (g := 𝟙 ((uliftYoneda.{u + 1}).obj V))
        ⟨heq.symm.trans (Category.comp_id _).symm⟩) h1
  exact (Space.isSeparatedULift_whiskerRight_iff.{u + 1} B S hS _).mp h2

/-- **Case II of the uniqueness argument of Stacks 0ARW.** A valuative square for a morphism
`f` whose base change along the bottom edge is separated has at most one dotted arrow: two
dotted arrows give two dotted arrows of the induced square for the base change, which agree by
the uniqueness part of the valuative criterion for separated morphisms. -/
theorem subsingleton_lift_of_isSeparated_pullback_snd {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X' ⟶ X} (q : Space.ValuativeSquare f)
    (hsep : Space.IsSeparated B S hS (pullback.snd f q.special)) :
    Subsingleton q.Lift := by
  let jK := yoneda.map (Over.homMk
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem) :
    siteObject B S hS q.field_mem (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base)
  let q' : Space.ValuativeSquare (pullback.snd f q.special) :=
    { R := q.R, K := q.K, ring_mem := q.ring_mem, field_mem := q.field_mem, base := q.base
      generic := pullback.lift q.generic jK q.comm
      special := 𝟙 _
      comm := by rw [pullback.lift_snd, Category.comp_id] }
  let toLift (l : q.Lift) : q'.Lift :=
    { map := pullback.lift l.map (𝟙 _) (by rw [l.special_comm, Category.id_comp])
      generic_comm := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, l.generic_comm]
          exact (pullback.lift_fst _ _ _).symm
        · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
          exact (pullback.lift_snd _ _ _).symm
      special_comm := pullback.lift_snd _ _ _ }
  refine ⟨fun l₁ l₂ => ?_⟩
  have h := congrArg (fun l : q'.Lift => l.map ≫ pullback.fst f q.special)
    ((Space.valuativeCriterion_uniqueness_of_isSeparated _ hsep q').elim (toLift l₁) (toLift l₂))
  change pullback.lift l₁.map _ _ ≫ _ = pullback.lift l₂.map _ _ ≫ _ at h
  rw [pullback.lift_fst, pullback.lift_fst] at h
  cases l₁
  cases l₂
  cases h
  rfl

/-- **The converse implication of Stacks 0ARW**, for the completion itself: a morphism
`f : X' ⟶ X` of algebraic spaces, locally of finite type, with `X` locally Noetherian, which is
an isomorphism over the complement of a closed set `T` and whose completion `f_{/T}` is
separated with rig-surjective relative diagonal, is separated. -/
theorem isSeparated_of_isSeparatedMorphism_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hN : Space.HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T))
    (f : X' ⟶ X) (hf : Space.IsLocallyOfFiniteType B S hS f)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (hfU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hg : IsSeparatedMorphism B S hS (Space.completionSheafMap B S hS f T))
    (hΔ : IsRigSurjective B S hS (pullback.diagonal (Space.completionSheafMap B S hS f T))) :
    Space.IsSeparated B S hS f := by
  have hsepT : ∀ (V : BigFppfOver B S hS) (w : yoneda.obj V ⟶ X),
      Set.range (Space.pointsMap B S hS (yoneda.obj V) w) ⊆ T →
      Space.IsSeparated B S hS (pullback.snd f w) := fun V w hwT ↦
    isSeparated_pullback_snd_of_isSeparatedMorphism_completionSheafMap hX' hX f T hg V w (by
      rwa [Space.hasImageIn_iff_range_subset, Equiv.symm_apply_apply])
  have hqs := isQuasiSeparated_of_isSeparated_pullback_snd hX' hX hN f hf T hT hfU
    fun V w _ hwT ↦ hsepT V w hwT
  refine (Space.isSeparated_iff_completeDiscreteValuativeUniqueness B S hS hX' hX f hN hf
    hqs).2 fun q hd hc => ?_
  rcases range_subset_or_range_subset_compl_or_iff_closedPoint T hT q.ring_mem q.base
    q.special with h | h | hpre
  · exact subsingleton_lift_of_isSeparated_pullback_snd q (hsepT _ q.special h)
  · exact (unique_lift_of_range_subset_compl hfU q h).2
  · exact subsingleton_lift_of_iff_closedPoint hX' hX hΔ q hd hc hpre

/-- Separatedness of a morphism of fppf sheaves, in the sense of Stacks 0ARN, is unchanged by
precomposing with an isomorphism: the composite is a base change of the morphism along the
identity. -/
theorem isSeparatedMorphism_isIso_comp {W' W Y : FppfSheaf B S hS} (i : W' ⟶ W) [IsIso i]
    (h : W ⟶ Y) (hh : IsSeparatedMorphism B S hS h) : IsSeparatedMorphism B S hS (i ≫ h) :=
  isSeparatedMorphism_of_isPullback B S hS
    (IsPullback.of_horiz_isIso (fst := i) (snd := i ≫ h) (f := h) (g := 𝟙 Y) ⟨by simp⟩) hh

/-- Pullbacks of fppf sheaves (in `Type (u + 1)`, where completions live), found once: instance
search for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_ModificationOutputSeparated :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) := by
  set_option synthInstance.maxHeartbeats 400000 in infer_instance

/-- The pullback of two morphisms of fppf sheaves in `Type (u + 1)`. -/
local instance (priority := high) hasLimit_cospan_sheaf_ModificationOutputSeparated
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ModificationOutputSeparated :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_ModificationOutputSeparated
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 0ARW.** Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
closed with open complement `U`, and let `f : X' ⟶ X` be a finite-type modification of `X`
outside `U` (Stacks 0AS2), corresponding to an object `g : W ⟶ X_{/T}` of the right-hand
category of Stacks 0AR5 — a rig-étale morphism with `W` a locally Noetherian formal algebraic
space — through an isomorphism over `X_{/T}` between `f_{/T}` and `g`. Then `f` is separated if
and only if `g` is separated (Stacks 0ARN) and its relative diagonal
`Δ_g : W ⟶ W ×_{X_{/T}} W` is rig-surjective. -/
@[stacks 0ARW "the correspondence `f ↔ g` of Theorem 0ARB is rendered as an isomorphism over \
`X_{/T}` between the image `f_{/T}` of `f` under the completion functor of Stacks 0AR5 and an \
object `g` of the right-hand category of Stacks 0AR5; the equivalence of Theorem 0ARB itself is \
not used. Separatedness of `g` is the separatedness axiom of Stacks 0ARN, part (1)"]
theorem isSeparated_iff_isSeparatedMorphism_and_isRigSurjective_diagonal_of_iso
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    (P : RigEtaleOverCompletion B S hS X T)
    (e : (Space.completionOverFunctor B S hS T).obj M.obj ≅ P.obj) :
    Space.IsSeparated B S hS M.obj.hom ↔
      IsSeparatedMorphism B S hS P.obj.hom ∧
        IsRigSurjective B S hS (pullback.diagonal P.obj.hom) := by
  have hX' : IsAlgebraicSpace B S hS M.obj.left := M.property.1.1
  have hfU : IsIso (pullback.snd M.obj.hom (Space.openSubspaceOfPoints B S hS X Tᶜ).ι) :=
    M.property.1.2
  constructor
  · intro hf
    have hfrom : IsIso ((Space.openSubspaceOfPoints B S hS X Tᶜ).fromPreimage M.obj.hom) := by
      rw [← (Subfunctor.isPullback_fromPreimage (Space.openSubspaceOfPoints B S hS X Tᶜ)
        M.obj.hom).flip.isoPullback_hom_snd]
      infer_instance
    have : IsIso e.inv.left := ((Over.forget _).mapIso e).isIso_inv
    have key : ∀ {φ : P.obj.left ⟶ Space.completionSheaf B S hS X T},
        φ = e.inv.left ≫ Space.completionSheafMap B S hS M.obj.hom T →
          IsSeparatedMorphism B S hS φ ∧ IsRigSurjective B S hS (pullback.diagonal φ) := by
      rintro φ rfl
      exact ⟨isSeparatedMorphism_isIso_comp e.inv.left _
          (isSeparatedMorphism_completionSheafMap B S hS hX' hX _ T hf),
        isRigSurjective_diagonal_isIso_comp e.inv.left _
          (isRigSurjective_diagonal_completionSheafMap hX' hX _ T hT hf (IsIso.mono_of_iso _))⟩
    exact key (Over.w e.inv).symm
  · rintro ⟨hsep, hΔ⟩
    have hN : Space.HasEtaleLocalProperty B S hS X
        (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T) :=
      (Space.exists_atlas_iff_forall_etale B S hS X _ hX).mpr fun W q hq ↦
        hXN W q ((Space.isEtale_iff_presheaf_of_yoneda B S hS q).2 hq)
    have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
    have hg : Space.completionSheafMap B S hS M.obj.hom T = e.hom.left ≫ P.obj.hom :=
      (Over.w e.hom).symm
    refine isSeparated_of_isSeparatedMorphism_completionSheafMap hX' hX hN M.obj.hom
      M.property.2 T hT hfU ?_ ?_ <;> rw [hg]
    · exact isSeparatedMorphism_isIso_comp e.hom.left P.obj.hom hsep
    · exact isRigSurjective_diagonal_isIso_comp e.hom.left P.obj.hom hΔ

end AlgebraicGeometry.FormalSpace

end
