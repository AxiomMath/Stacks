module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.CompleteLocalAlgebra
public import StacksFrontier.Deformation.Smooth.Pushforward
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Unobstructed predeformation categories and smooth versal rings (Stacks 0DZK)

Let `𝓕` be a predeformation category over `𝒞_Λ` with a versal formal object `ξ` lying over
`R`. This file proves that `𝓕` is unobstructed — that is, that its structure functor is
smooth — if and only if `Λ → R` is formally smooth in the `m_R`-adic topology, and, when the
base is classical, if and only if `R` is a formal power series algebra over `Λ`.

## Main definitions

* `Deformation.baseProjection` is the structure functor of a category over `𝒞_Λ`, regarded
  as a morphism of categories over that base.

## Main results

* `Deformation.isSmooth_baseProjection_iff_formallySmoothNAdic`: **Stacks 0DZK**, conditions
  (1) and (2).
* `Deformation.isSmooth_baseProjection_iff_powerSeries`: **Stacks 0DZK**, condition (3) in the
  classical case.

## Implementation notes

Unobstructedness of `𝓕` is smoothness of `baseProjection p`, which is how the source defines
it: the structure functor is read as a morphism from `𝓕` to the base category regarded as a
based category over itself, so the condition is `Deformation.IsSmooth`.

The proof factors the projection through the morphism `associatedMorphism` attached to the
versal object, whose target is the restricted representable category of `R`. Versality says
that morphism is smooth, and it is essentially surjective because every object of the
restricted representable category over an Artinian local algebra `A` is a map `R → A`, which
the formal object pushes forward to an object of `𝓕` over `A`; the comparison is an
isomorphism because `𝓕` is cofibered in groupoids. Composing with `baseProjection p` gives
the projection of the restricted representable category, so one direction is stability of
smoothness under composition and the other is Stacks 06HM for a morphism that is essentially
surjective, both in `StacksFrontier.Deformation.Smooth.Basic`. Conditions (2) and (3) are then
read off Stacks 0DYL for `R`.

Essential surjectivity needs a choice of pushforwards along every morphism of `𝒞_Λ`; these
are produced from cofiberedness of the structure functor by `Classical.choice`, which is why
this file is `noncomputable` in that step.

## References

* [Stacks Project, Tag 0DZK](https://stacks.math.columbia.edu/tag/0DZK)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

private noncomputable def algebraMapToResidue (A : Type*) [CommRing A] [Algebra Λ A]
    [IsLocalRing A] : A →ₐ[Λ] ResidueField A :=
  IsScalarTower.toAlgHom Λ A (ResidueField A)

private noncomputable def liftResidueMap {A : Type*} [CommRing A] [Algebra Λ A]
    [IsLocalRing A] (e : ResidueField A ≃ₐ[Λ] k) : A →ₐ[Λ] ULift.{v, w} k :=
  (ULift.algEquiv (R := Λ) (A := k)).symm.toAlgHom.comp
    (e.toAlgHom.comp (algebraMapToResidue A))

private theorem liftResidueMap_surjective {A : Type*} [CommRing A] [Algebra Λ A]
    [IsLocalRing A] (e : ResidueField A ≃ₐ[Λ] k) :
    Function.Surjective (liftResidueMap (Λ := Λ) e) := by
  intro x
  obtain ⟨y, hy⟩ := e.surjective x.down
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) y
  refine ⟨a, ?_⟩
  apply ULift.ext
  simpa [liftResidueMap, algebraMapToResidue, ha] using hy

private theorem liftResidueMap_residue_comm (A : Type*) [CommRing A] [Algebra Λ A]
    [IsLocalRing A] (e : ResidueField A ≃ₐ[Λ] k) (x : A) :
    (residueFieldObject Λ k).residueEquiv
      (residue (residueFieldObject Λ k)
      ((liftResidueMap (Λ := Λ) e : A →ₐ[Λ] ULift.{v, w} k) x)) = e (residue A x) := by
  show ((Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{v, w} k))).trans
    ((AlgEquiv.quotientBot Λ (ULift.{v, w} k)).trans
      (ULift.algEquiv (R := Λ) (A := k))))
    (Ideal.Quotient.mk (maximalIdeal (ULift.{v, w} k))
      ((ULift.algEquiv (R := Λ) (A := k)).symm (e (residue A x)))) = _
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    AlgEquiv.quotientBot_mk]
  exact AlgEquiv.apply_symm_apply _ _

private theorem liftResidueMap_isLocalHom {A : Type*} [CommRing A] [Algebra Λ A]
    [IsLocalRing A] (e : ResidueField A ≃ₐ[Λ] k) :
    IsLocalHom (liftResidueMap (Λ := Λ) e : A →ₐ[Λ] ULift.{v, w} k).toRingHom :=
  IsLocalHom.of_surjective _ (liftResidueMap_surjective (Λ := Λ) e)

private noncomputable def completeResiduePoint (R : CompleteLocalAlgCat.{u, max v w, w} Λ k) :
    R ⟶ artinianToComplete.obj
      (residueFieldObject Λ k : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :=
  ⟨liftResidueMap (Λ := Λ) R.residueEquiv, liftResidueMap_isLocalHom R.residueEquiv,
    fun x => liftResidueMap_residue_comm R R.residueEquiv x⟩

private noncomputable def artinianResiduePoint
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    A ⟶ residueFieldObject Λ k :=
  ⟨liftResidueMap (Λ := Λ) A.residueEquiv, liftResidueMap_isLocalHom A.residueEquiv,
    fun x => liftResidueMap_residue_comm A A.residueEquiv x⟩

private theorem specialFiber_objects_iso
    (hp : IsPredeformationCategory p)
    {x y : F}
    (hx : p.obj x = residueFieldObject Λ k)
    (hy : p.obj y = residueFieldObject Λ k) :
    Nonempty ((show p.Fiber (residueFieldObject Λ k) from ⟨x, hx⟩) ≅
      (show p.Fiber (residueFieldObject Λ k) from ⟨y, hy⟩)) := by
  classical
  let A : ArtinianLocalAlgCat.{u, max v w, w} Λ k := residueFieldObject Λ k
  let E := Classical.choice hp.specialFiber
  have hUnique : ∀ X Y : p.Fiber A, Nonempty (Unique (X ⟶ Y)) :=
    (CategoryTheory.equiv_punit_iff_unique (p.Fiber A)).mp ⟨E⟩ |>.2
  let X : p.Fiber A := ⟨x, hx⟩
  let Y : p.Fiber A := ⟨y, hy⟩
  obtain ⟨_⟩ := hUnique X Y
  obtain ⟨_⟩ := hUnique Y X
  obtain ⟨_⟩ := hUnique X X
  obtain ⟨_⟩ := hUnique Y Y
  exact ⟨⟨default, default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

private theorem associatedMorphism_essentiallySurjective
    (hp : IsPredeformationCategory p) (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p)
    (hξ : IsVersal hp.cofibered ξ) :
    ((associatedMorphism hp.cofibered ξ pushforwards).toBasedFunctor).toFunctor.EssSurj := by
  classical
  let M := (associatedMorphism hp.cofibered ξ pushforwards).toBasedFunctor
  have hM : IsSmooth M := hξ pushforwards
  refine ⟨fun y => ?_⟩
  let yF : F := y
  let K : ArtinianLocalAlgCat.{u, max v w, w} Λ k := residueFieldObject Λ k
  let α : (restrictedCoyoneda ξ.base).obj K := completeResiduePoint ξ.base
  let z₀ : (restrictedCoyoneda ξ.base).Elements := (restrictedCoyoneda ξ.base).elementsMk K α
  have hz₀ : p.obj (M.obj z₀) = K := by
    exact (BasedFunctor.w_obj M z₀).trans rfl
  let A := p.obj yF
  let f := artinianResiduePoint A
  obtain ⟨zop, gop, hgop⟩ := hp.cofibered.exists_lift f.op (Opposite.op yF) rfl
  let z := Opposite.unop zop
  let g : yF ⟶ z := Opposite.unop gop
  have hz : p.obj z = K := congrArg Opposite.unop (IsHomLift.domain_eq p.op f.op gop)
  have hg : p.IsHomLift f g := by
    apply IsHomLift.of_fac p f g rfl hz
    let _ : p.op.IsHomLift f.op gop := hgop
    have hfac := IsHomLift.fac p.op f.op gop
    convert congrArg Quiver.Hom.unop hfac using 1 <;> simp [g, eqToHom_unop]
    congr 1
  let zK : p.Fiber K := ⟨z, hz⟩
  let xK : p.Fiber K := ⟨M.obj z₀, hz₀⟩
  let e : zK ≅ xK := Classical.choice (specialFiber_objects_iso hp hz hz₀)
  let u : z ⟶ M.obj z₀ := e.hom.val
  have hu : p.IsHomLift (𝟙 K) u := e.hom.property
  have hgu : p.IsHomLift f (g ≫ u) := IsHomLift.comp_lift_id_right p f g u
  have hsurj : Function.Surjective f.hom := liftResidueMap_surjective (Λ := Λ) A.residueEquiv
  obtain ⟨x', h, a, hh, ha, hcomm⟩ := hM f hsurj yF z₀ (g ≫ u) hgu
  have : IsIso a := isIso_of_isHomLift_id hp.cofibered a ha
  show ∃ x' : (restrictedCoyoneda ξ.base).Elements,
    Nonempty (M.obj x' ≅ yF)
  exact ⟨x', ⟨asIso a⟩⟩

/-- The structure functor of a category over `𝒞_Λ`, viewed as a morphism of categories over
that base, the base itself being regarded as a based category over itself. Smoothness of
this morphism is unobstructedness of the category. -/
public def baseProjection
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    BasedFunctor (BasedCategory.ofFunctor p)
      (BasedCategory.ofFunctor (𝟭 (ArtinianLocalAlgCat.{u, max v w, w} Λ k))) where
  toFunctor := p
  w := rfl

/-- **Stacks 0DZK.** A predeformation category with a versal formal object over `R` is
unobstructed if and only if `Λ → R` is formally smooth in the `m_R`-adic topology. -/
@[stacks 0DZK "conditions (1) and (2)", sga "7 VI 2.4" "P smooth <=> R f.smooth"]
public theorem isSmooth_baseProjection_iff_formallySmoothNAdic
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ) :
    IsSmooth (baseProjection p) ↔
      RingHom.FormallySmoothNAdic.{max u (max v w)}
        (algebraMap Λ ξ.base) (maximalIdeal ξ.base) := by
  classical
  let P := chosenPushforwardsOfCofibered p hp.cofibered
  let M := (associatedMorphism hp.cofibered ξ P).toBasedFunctor
  have : M.toFunctor.EssSurj := associatedMorphism_essentiallySurjective hp ξ P hξ
  have hcomp : BasedFunctor.comp M (baseProjection p) =
      restrictedCoyonedaProjection ξ.base :=
    BasedCategory.BasedFunctor.ext' M.w
  have hcriterion := (smooth_formallySmooth_flat_specialFibre_tfae ξ.base).out 1 2
  rw [← hcomp] at hcriterion
  exact ⟨fun h => hcriterion.mp (isSmooth_comp M (baseProjection p) (hξ P) h),
    fun h => isSmooth_of_essSurj_comp
      (categoryOfElements_projection_isCofibered (restrictedCoyoneda ξ.base)) M
      (baseProjection p) (hcriterion.mpr h)⟩

/-- **Stacks 0DZK.** In the classical case, a predeformation category with a versal formal
object over `R` is unobstructed if and only if `R` is a formal power series algebra in
finitely many variables over `Λ`. -/
@[stacks 0DZK "condition (3), classical case",
  sga "7 VI 2.4" "P smooth <=> R=Λ[[x]]",
  sga "7 VI 1.14" "more general"]
public theorem isSmooth_baseProjection_iff_powerSeries
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsPredeformationCategory p)
    (ξ : FormalObject p) (hξ : IsVersal hp.cofibered ξ)
    (hΛ : IsClassical Λ k) :
    IsSmooth (baseProjection p) ↔
      ∃ n : ℕ, Nonempty (ξ.base ≃ₐ[Λ] MvPowerSeries (Fin n) Λ) := by
  rw [isSmooth_baseProjection_iff_formallySmoothNAdic hp ξ hξ]
  exact (smooth_formallySmooth_flat_specialFibre_powerSeries_tfae ξ.base hΛ).out 2 5
end Deformation

end
