module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Quot.PointsOverBaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions

/-!
# Limits of algebraic spaces affine over a base, read on the test schemes

A functor on the test schemes over an algebraic space `Y` which is a limit of functors each of
which is an algebraic space affine over `Y` is again one, as soon as the limit of the
representing algebraic spaces is an algebraic space affine over `Y`.  For an equalizer this
always holds: the equalizer of two morphisms `a, b : P ⟶ Q` over `Y` is the base change of the
relative diagonal of `Q ⟶ Y` along `(a, b) : P ⟶ Q ×_Y Q`, which is affine because an affine
morphism is separated (Stacks 03HL, 01S7).

## Main results

* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isLimit_predicateSystem`: the limit of
  a connected system of functors each an algebraic space affine over `Y`, granted that the limit
  of the chosen representing algebraic spaces is one.
* `CategoryTheory.Limits.isPullback_equalizer_pullbackDiagonal`: the equalizer of two morphisms
  over `T` is the pullback of the relative diagonal over `T`.
* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isLimit_fork`: **an equalizer of two
  morphisms of functors which are algebraic spaces affine over `Y` is one.**

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 01S7](https://stacks.math.columbia.edu/tag/01S7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] {X Y T : C} (f g : X ⟶ Y) (t : Y ⟶ T)

/-- **The equalizer of two morphisms over `T` is the pullback of the relative diagonal of
`Y ⟶ T` along `(f, g) : X ⟶ Y ×_T Y`.** -/
theorem isPullback_equalizer_pullbackDiagonal [HasEqualizer f g] [HasPullback t t]
    (h : f ≫ t = g ≫ t) :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f) (pullback.lift f g h)
      (pullback.diagonal t) := by
  have hl₁ : pullback.lift f g h ≫ pullback.fst t t = f := pullback.lift_fst _ _ _
  have hl₂ : pullback.lift f g h ≫ pullback.snd t t = g := pullback.lift_snd _ _ _
  have hd₁ : pullback.diagonal t ≫ pullback.fst t t = 𝟙 _ := pullback.diagonal_fst t
  have hd₂ : pullback.diagonal t ≫ pullback.snd t t = 𝟙 _ := pullback.diagonal_snd t
  have H (s : PullbackCone (pullback.lift f g h) (pullback.diagonal t)) :
      s.fst ≫ f = s.snd ∧ s.fst ≫ g = s.snd := by
    exact ⟨by simpa [hl₁, hd₁] using congr($s.condition ≫ pullback.fst t t),
      by simpa [hl₂, hd₂] using congr($s.condition ≫ pullback.snd t t)⟩
  refine ⟨⟨by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hl₁, hd₁, Category.comp_id]
    · rw [Category.assoc, Category.assoc, hl₂, hd₂, Category.comp_id, equalizer.condition f g]⟩,
    ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · exact fun s ↦ equalizer.lift s.fst ((H s).1.trans (H s).2.symm)
  · exact fun s ↦ by simp
  · exact fun s ↦ by simpa using (H s).1
  · exact fun s m hm _ ↦ by ext; simp [*]

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Y : AlgebraicSpaces B S hS}

section PredicateSystem

variable {I : Type u} [Category.{u} I] [IsPreconnected I]
  (R : I ⥤ ((SchemesOver Y)ᵒᵖ ⥤ Type (u + 1))) (h : ∀ i, IsAffineAlgebraicSpaceOver Y (R.obj i))

/-- **A connected limit of functors on the test schemes over `Y`, each an algebraic space affine
over `Y`, is an algebraic space affine over `Y`, as soon as the limit of the chosen representing
algebraic spaces is an algebraic space affine over `Y`.** -/
theorem isAffineAlgebraicSpaceOver_of_isLimit_predicateSystem
    (hlim : IsAlgebraicSpace B S hS (limit (predicateSystem B S hS R h))) (i₀ : I)
    (haff : IsAffineHom B S hS
      (limit.π (predicateSystem B S hS R h) i₀ ≫ (predicateSystemProjection B S hS R h).app i₀))
    (c : Cone R) (hc : IsLimit c) : IsAffineAlgebraicSpaceOver Y c.pt :=
  isAffineAlgebraicSpaceOver_of_isLimit B S hS (predicateSystem B S hS R h)
    (predicateSystemProjection B S hS R h) (isAlgebraicSpace_predicateSystem B S hS R h) hlim i₀
    haff ((Cone.postcompose (predicateSystemIso B S hS R h).inv).obj c)
    ((IsLimit.postcomposeInvEquiv (predicateSystemIso B S hS R h) c).symm hc) (Iso.refl _)

end PredicateSystem

section Equalizer

/-- **The equalizer of two morphisms of algebraic spaces over `Y`, the target being affine over
`Y`, is an algebraic space whose morphism to the source is affine.** -/
theorem isAlgebraicSpace_equalizer_and_isAffineHom_ι {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q) (q : Q ⟶ Y.1)
    (hq : IsAffineHom B S hS q) (a b : P ⟶ Q) (hab : a ≫ q = b ≫ q) :
    IsAlgebraicSpace B S hS (equalizer a b) ∧ IsAffineHom B S hS (equalizer.ι a b) := by
  have sq := isPullback_equalizer_pullbackDiagonal a b q hab
  have hQQ := isAlgebraicSpace_pullback B S hS q q hQ hQ Y.2
  refine ⟨(isAlgebraicSpace_pullback B S hS (pullback.lift a b hab) (pullback.diagonal q) hP hQ
    hQQ).of_iso sq.isoPullback.symm, IsAffineHom.of_isPullback sq.flip ?_⟩
  exact isAffineHom_of_isClosedImmersion B S hS _ (isSeparated_of_isAffineHom B S hS q hQ Y.2 hq)

variable {R₁ R₂ : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}

/-- **An equalizer of two morphisms of functors on the test schemes over `Y`, each an algebraic
space affine over `Y`, is an algebraic space affine over `Y`.** -/
theorem isAffineAlgebraicSpaceOver_of_isLimit_fork {a b : R₁ ⟶ R₂}
    (h₁ : IsAffineAlgebraicSpaceOver Y R₁) (h₂ : IsAffineAlgebraicSpaceOver Y R₂) (c : Fork a b)
    (hc : IsLimit c) : IsAffineAlgebraicSpaceOver Y c.pt := by
  let F : AsSmall.{u} WalkingParallelPair ⥤ ((SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) :=
    AsSmall.down ⋙ parallelPair a b
  have h : ∀ j, IsAffineAlgebraicSpaceOver Y (F.obj j) := by
    rintro ⟨_ | _⟩
    · exact h₁
    · exact h₂
  have : IsPreconnected (AsSmall.{u} WalkingParallelPair) :=
    isPreconnected_of_equivalent AsSmall.equiv
  let D := predicateSystem B S hS F h
  let τ := predicateSystemProjection B S hS F h
  let z : AsSmall.{u} WalkingParallelPair := ⟨WalkingParallelPair.zero⟩
  let o : AsSmall.{u} WalkingParallelPair := ⟨WalkingParallelPair.one⟩
  let l : z ⟶ o := ⟨WalkingParallelPairHom.left⟩
  let r : z ⟶ o := ⟨WalkingParallelPairHom.right⟩
  have hab : D.map l ≫ τ.app o = D.map r ≫ τ.app o :=
    (τ.naturality l).trans (τ.naturality r).symm
  obtain ⟨hE, hι⟩ := isAlgebraicSpace_equalizer_and_isAffineHom_ι B S hS
    (isAlgebraicSpace_predicateSystem B S hS _ h z) (isAlgebraicSpace_predicateSystem B S hS _ h o)
    (τ.app o) (isAffineHom_predicateSystemProjection B S hS _ h o) _ _ hab
  let cE : Cone D :=
    { pt := equalizer (D.map l) (D.map r)
      π :=
        { app := fun j => match j with
            | ⟨WalkingParallelPair.zero⟩ => equalizer.ι (D.map l) (D.map r)
            | ⟨WalkingParallelPair.one⟩ => equalizer.ι (D.map l) (D.map r) ≫ D.map l
          naturality := by
            rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _ | _⟩
            · exact (Category.comp_id _).symm.trans (congrArg _ (D.map_id z).symm)
            · exact Category.id_comp _
            · exact (Category.id_comp _).trans (equalizer.condition (D.map l) (D.map r))
            · exact (Category.comp_id _).symm.trans (congrArg _ (D.map_id o).symm) } }
  have hcE : IsLimit cE :=
    { lift := fun s => equalizer.lift (s.π.app z) ((s.π.naturality l).symm.trans
        (s.π.naturality r))
      fac := by
        rintro s ⟨_ | _⟩
        · exact equalizer.lift_ι _ _
        · change (equalizer.lift _ _ ≫ equalizer.ι _ _ ≫ D.map l) = s.π.app o
          rw [equalizer.lift_ι_assoc]
          exact (s.π.naturality l).symm.trans (Category.id_comp _)
      uniq := fun s m hm => equalizer.hom_ext ((hm z).trans (equalizer.lift_ι _ _).symm) }
  let e : limit D ≅ cE.pt := (limit.isLimit D).conePointUniqueUpToIso hcE
  have he : limit.π D z = e.hom ≫ equalizer.ι (D.map l) (D.map r) :=
    ((limit.isLimit D).conePointUniqueUpToIso_hom_comp hcE z).symm
  refine isAffineAlgebraicSpaceOver_of_isLimit_predicateSystem B S hS F h
    (hE.of_iso e.symm) z ?_ (c.whisker AsSmall.down)
    (IsLimit.whiskerEquivalence hc AsSmall.equiv.symm)
  rw [he, Category.assoc]
  exact isAffineHom_iso_comp e.hom (isAffineHom_comp B S hS _ _ hι
    (isAffineHom_predicateSystemProjection B S hS _ h z))

end Equalizer

end AlgebraicGeometry.Space

end
