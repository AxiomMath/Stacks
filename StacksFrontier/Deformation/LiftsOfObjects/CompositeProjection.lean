module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Lift
public import StacksFrontier.Deformation.LiftsOfObjects.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Projections of lifts over a composite of two fibre squares

For two successive fibre squares, isomorphism classes of lifts over the outer pullback
correspond to pairs consisting of a lift over the inner factor and a lift of the original
object over the other outer factor, by a bijection whose two coordinates are characterized by
the two projections of the diagram.

## Main definitions

* `Deformation.LiftProjectionEquiv`: a bijection of lift classes over a composite of two
  fibre squares whose two coordinates are pinned down by the two projections of the diagram.

## Main results

* `Deformation.liftClassesEquivProdOfResiduePullback`: such a bijection exists for a
  deformation category, provided the inner map and the first outer map are surjective.

## Implementation notes

The statement is made for a general pair of fibre squares; the residue-field square is the case
where the right square is `A ×_k k[I]` and the left square is its pullback along `A' → A`.

## References

* [Stacks Project, Tag 06TC](https://stacks.math.columbia.edu/tag/06TC)
-/

@[expose] public section

namespace Deformation

/-! ### Lifts over a composite of fibre squares, via the two projections -/

section
open CategoryTheory CategoryTheory.Limits

universe u v w uF vF

private lemma exists_projection_data
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (x : p.Fiber A)
    (E : LiftProductEquiv p c x)
    (z : Lift p (c.fst ≫ f₁) x) :
    ∃ (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
      (h₁ : z.obj ⟶ a₁.obj) (h₂ : z.obj ⟶ a₂.obj),
      E.equiv.symm (ThinSkeleton.mk z) = (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) ∧
      p.IsHomLift c.fst h₁ ∧ p.IsHomLift c.snd h₂ ∧
      h₁ ≫ a₁.hom = z.hom ∧ h₂ ≫ a₂.hom = z.hom := by
  classical
  let pair := E.equiv.symm (ThinSkeleton.mk z)
  let a₁ := Quotient.out pair.1
  let a₂ := Quotient.out pair.2
  have ha₁ : ThinSkeleton.mk a₁ = pair.1 := Quotient.out_eq pair.1
  have ha₂ : ThinSkeleton.mk a₂ = pair.2 := Quotient.out_eq pair.2
  have heq : E.equiv (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) = ThinSkeleton.mk z := by
    calc
      E.equiv (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) = E.equiv pair :=
        congrArg E.equiv (Prod.ext ha₁ ha₂)
      _ = ThinSkeleton.mk z := Equiv.apply_symm_apply _ _
  obtain ⟨w, hw, hew⟩ := E.maps_pair_to_fiberProduct a₁ a₂
  have hwz : ThinSkeleton.mk w = ThinSkeleton.mk z := hew.symm.trans heq
  obtain ⟨i⟩ : Nonempty (w ≅ z) := Quotient.exact hwz
  rcases hw with ⟨g₁, g₂, _, hg₁, hg₂, hfac₁, hfac₂, _⟩
  let h₁ := i.inv.hom ≫ g₁
  let h₂ := i.inv.hom ≫ g₂
  refine ⟨a₁, a₂, h₁, h₂, by simpa [pair] using (Prod.ext ha₁ ha₂).symm, ?_, ?_, ?_, ?_⟩
  · dsimp [h₁]
    infer_instance
  · dsimp [h₂]
    infer_instance
  · simpa only [h₁, Category.assoc, hfac₁] using i.inv.fac
  · simpa only [h₂, Category.assoc, hfac₂] using i.inv.fac

private lemma first_coordinate_iff
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {A₁' A₂' A₁ : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {g : A₁' ⟶ A₁} {r : A₂' ⟶ A₁}
    (c : PullbackCone g r) (x : p.Fiber A₁)
    (E : LiftProductEquiv p c x)
    (z : Lift p (c.fst ≫ g) x)
    (b : Lift p g x) :
    (E.equiv.symm (ThinSkeleton.mk z)).1 = ThinSkeleton.mk b ↔
      ∃ h : z.obj ⟶ b.obj, p.IsHomLift c.fst h ∧ h ≫ b.hom = z.hom := by
  obtain ⟨a₁, a₂, h₁, h₂, hpair, hh₁, hh₂, hfac₁, hfac₂⟩ := exists_projection_data c x E z
  constructor
  · intro h
    have hab : ThinSkeleton.mk a₁ = ThinSkeleton.mk b := by
      simpa [hpair] using h
    obtain ⟨i⟩ : Nonempty (a₁ ≅ b) := Quotient.exact hab
    refine ⟨h₁ ≫ i.hom.hom, ?_, ?_⟩
    · infer_instance
    · simpa only [Category.assoc, i.hom.fac] using hfac₁
  · rintro ⟨h, hh, hfac⟩
    obtain ⟨i⟩ := nonempty_iso_of_liftFactorizations hp c.fst g x z a₁ b h₁ h hh₁ hh hfac₁ hfac
    rw [hpair]
    change ThinSkeleton.mk a₁ = ThinSkeleton.mk b
    exact Quotient.sound ⟨i⟩

private noncomputable def isLimit_mapped_pullback_of_lift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c) (x : p.Fiber A)
    (z : Lift p (c.fst ≫ f₁) x)
    (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (g₁ : z.obj ⟶ a₁.obj) (g₂ : z.obj ⟶ a₂.obj)
    (comm : g₁ ≫ a₁.hom = g₂ ≫ a₂.hom)
    (hg₁ : p.IsHomLift c.fst g₁) (hg₂ : p.IsHomLift c.snd g₂) :
    IsLimit ((PullbackCone.mk g₁ g₂ comm).map p) := by
  let h₀ := CategoryTheory.IsHomLift.domain_eq p c.fst g₁
  let h₁ := CategoryTheory.IsHomLift.codomain_eq p c.fst g₁
  let h₂ := CategoryTheory.IsHomLift.codomain_eq p c.snd g₂
  have hb : IsPullback (p.map g₁) (p.map g₂)
      (p.map a₁.hom) (p.map a₂.hom) := by
    apply (IsPullback.of_isLimit hc).of_iso'
      (eqToIso h₀) (eqToIso h₁) (eqToIso h₂) (eqToIso x.2)
    · rw [CategoryTheory.IsHomLift.fac' p c.fst g₁]
      simp [Category.assoc]
    · rw [CategoryTheory.IsHomLift.fac' p c.snd g₂]
      simp [Category.assoc]
    · rw [CategoryTheory.IsHomLift.fac' p f₁ a₁.hom]
      simp [Category.assoc]
    · rw [CategoryTheory.IsHomLift.fac' p f₂ a₂.hom]
      simp [Category.assoc]
  change IsLimit (PullbackCone.mk (p.map g₁) (p.map g₂) (by
    simpa only [p.map_comp] using congrArg p.map comm))
  exact hb.isLimit

/-- A bijection of lift classes over a composite of two fibre squares whose two coordinates
are induced by the two projections of the diagram. -/
public structure LiftProjectionEquiv
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {A₁' A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {g : A₁' ⟶ A₁}
    (right : PullbackCone f₁ f₂) (left : PullbackCone g right.fst)
    (x₀ : p.Fiber A) (a₁ : Lift p f₁ x₀) where
  /-- The bijection on isomorphism classes of lifts. -/
  equiv : LiftClasses p (left.fst ≫ g) (liftSourceFiber a₁) ≃
    LiftClasses p g (liftSourceFiber a₁) × LiftClasses p f₂ x₀
  /-- The first coordinate is pushforward along the first projection. -/
  fst_eq_iff : ∀ (z : Lift p (left.fst ≫ g) (liftSourceFiber a₁))
      (b : Lift p g (liftSourceFiber a₁)),
    (equiv (ThinSkeleton.mk z)).1 = ThinSkeleton.mk b ↔
      ∃ h : z.obj ⟶ b.obj,
        p.IsHomLift left.fst h ∧ h ≫ b.hom = z.hom
  /-- The second coordinate is pushforward along the composite second projection. -/
  snd_eq_iff : ∀ (z : Lift p (left.fst ≫ g) (liftSourceFiber a₁))
      (b : Lift p f₂ x₀),
    (equiv (ThinSkeleton.mk z)).2 = ThinSkeleton.mk b ↔
      ∃ h : z.obj ⟶ b.obj,
        p.IsHomLift (left.snd ≫ right.snd) h ∧
          h ≫ b.hom = z.hom ≫ a₁.hom

/-- For a composite of two fibre squares, lifts over the outer pullback are identified with a
lift over the inner factor and a lift over the other outer factor, via the two projections. -/
@[stacks 06TC]
public theorem liftClassesEquivProdOfResiduePullback
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hp : IsDeformationCategory p)
    {A₁' A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {g : A₁' ⟶ A₁}
    (right : PullbackCone f₁ f₂) (hright : IsLimit right)
    (left : PullbackCone g right.fst) (hleft : IsLimit left)
    (hg : Function.Surjective g.hom)
    (hf₁ : Function.Surjective f₁.hom)
    (x₀ : p.Fiber A) (a₁ : Lift p f₁ x₀) :
    Nonempty (LiftProjectionEquiv p right left x₀ a₁) :=
  by
    classical
    obtain ⟨E₁⟩ := liftClassesProdEquivPullback p hp.satisfiesRS left hleft
      (Or.inl hg) (liftSourceFiber a₁)
    obtain ⟨E₂⟩ := liftClassesEquivOfFixedLift p hp.satisfiesRS right hright
      (Or.inl hf₁) x₀ a₁
    refine ⟨{
      equiv := E₁.equiv.symm.trans (Equiv.prodCongr (Equiv.refl _) E₂.equiv)
      fst_eq_iff := ?_
      snd_eq_iff := ?_ }⟩
    · intro z b
      change (E₁.equiv.symm (ThinSkeleton.mk z)).1 = ThinSkeleton.mk b ↔ _
      exact first_coordinate_iff hp.satisfiesRS.1 left (liftSourceFiber a₁) E₁ z b
    · intro z b
      obtain ⟨b₁, b₂, h₁, h₂, hpair, hh₁, hh₂, hfac₁, hfac₂⟩ :=
        exists_projection_data left (liftSourceFiber a₁) E₁ z
      change E₂.equiv ((E₁.equiv.symm (ThinSkeleton.mk z)).2) =
        ThinSkeleton.mk b ↔
          ∃ h : z.obj ⟶ b.obj,
            p.IsHomLift (left.snd ≫ right.snd) h ∧
              h ≫ b.hom = z.hom ≫ a₁.hom
      constructor
      · intro heq
        rcases (E₂.maps_to_pushforward b₂ b).1
            ((congrArg (fun q => E₂.equiv q.2) hpair).symm.trans heq) with
          ⟨h₂', hcomm, hh₂', _⟩
        refine ⟨h₂ ≫ h₂', inferInstance, ?_⟩
        calc
          (h₂ ≫ h₂') ≫ b.hom = h₂ ≫ (h₂' ≫ b.hom) := Category.assoc _ _ _
          _ = h₂ ≫ (b₂.hom ≫ a₁.hom) := by rw [hcomm]
          _ = (h₂ ≫ b₂.hom) ≫ a₁.hom := (Category.assoc _ _ _).symm
          _ = z.hom ≫ a₁.hom := by rw [hfac₂]
      · rintro ⟨h, hh, hfac⟩
        let hmid := CategoryTheory.IsHomLift.codomain_eq p left.snd h₂
        let hcod := CategoryTheory.IsHomLift.codomain_eq p (left.snd ≫ right.snd) h
        let fbase : p.obj b₂.obj ⟶ p.obj b.obj :=
          eqToHom hmid ≫ right.snd ≫ eqToHom hcod.symm
        have hbase : p.map h₂ ≫ fbase = p.map h := by
          rw [CategoryTheory.IsHomLift.fac' p left.snd h₂,
            CategoryTheory.IsHomLift.fac' p (left.snd ≫ right.snd) h]
          simp [fbase, Category.assoc]
        obtain ⟨h₂', ⟨h₂map, h₂fac⟩, _⟩ :=
          existsUnique_factor_of_isHomLift hp.satisfiesRS.1 h₂ h fbase hbase
        have hh₂' : p.IsHomLift right.snd h₂' := by
          apply CategoryTheory.IsHomLift.of_fac' p right.snd h₂'
            hmid hcod
          simpa using h₂map
        let : p.IsHomLift right.snd h₂' := hh₂'
        let : p.IsHomLift (right.snd ≫ f₂) (h₂' ≫ b.hom) := inferInstance
        have hbase' : right.fst ≫ f₁ = right.snd ≫ f₂ := right.condition
        let : p.IsHomLift (right.snd ≫ f₂) (b₂.hom ≫ a₁.hom) := by
          rw [← hbase']
          exact @CategoryTheory.IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
            right.fst f₁ b₂.hom a₁.hom b₂.isHomLift a₁.isHomLift
        let : p.IsStronglyCocartesian left.snd h₂ :=
          isStronglyCocartesian_of_isCofiberedInGroupoids
            hp.satisfiesRS.1 left.snd h₂ hh₂
        have hcomm : b₂.hom ≫ a₁.hom = h₂' ≫ b.hom := by
          apply Functor.IsStronglyCocartesian.ext p left.snd h₂ (right.snd ≫ f₂)
          calc
            h₂ ≫ (b₂.hom ≫ a₁.hom) = (h₂ ≫ b₂.hom) ≫ a₁.hom :=
              (Category.assoc _ _ _).symm
            _ = z.hom ≫ a₁.hom := by rw [hfac₂]
            _ = h ≫ b.hom := hfac.symm
            _ = (h₂ ≫ h₂') ≫ b.hom := by rw [h₂fac]
            _ = h₂ ≫ (h₂' ≫ b.hom) := Category.assoc _ _ _
        let d : PullbackCone a₁.hom b.hom := PullbackCone.mk b₂.hom h₂' hcomm
        have hdmap : IsLimit (d.map p) :=
          isLimit_mapped_pullback_of_lift right hright x₀ (liftToComposite a₁ b₂)
            a₁ b b₂.hom h₂' hcomm b₂.isHomLift hh₂'
        have hsurj := surjective_map_of_lift p f₁ a₁.hom hf₁
        have hdflip : Nonempty (IsLimit d.flip) :=
          isLimit_of_map_isLimit hp.satisfiesRS b.hom a₁.hom d.flip hsurj (by
            change Nonempty (IsLimit (d.map p).flip)
            exact ⟨PullbackCone.flipIsLimit hdmap⟩)
        have hlim : Nonempty (IsLimit d) :=
          ⟨PullbackCone.isLimitOfFlip hdflip.some⟩
        rw [hpair]
        exact (E₂.maps_to_pushforward b₂ b).2 ⟨h₂', hcomm, hh₂', hlim⟩

end

end Deformation
