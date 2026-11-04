module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall

/-!
# The quotient of an étale equivalence relation given by witnesses

An étale equivalence relation on an object `W` of the big fppf site of `S`, presented by two
étale morphisms `s, t : R ⟶ W` which are jointly monic together with witnesses of reflexivity,
symmetry and transitivity, has an algebraic space quotient `X = W/R` (Stacks 02WW): the quotient
map `W ⟶ X` is a surjective étale atlas whose kernel pair is `R`, and every morphism out of `W`
into a sheaf which the two projections equalize factors uniquely through `X`.

This is the step of the descent of a separated algebraic space of finite presentation along a
limit of affine schemes (Stacks 07SK, used in the proof of Stacks 0GI5 for an index of arbitrary
size) which builds the model at a finite stage once the atlas and its kernel pair have been
descended (`AlgebraicGeometry.exists_stage_relation`, `AlgebraicGeometry.exists_relationData`).

## Main results

* `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_relation_of_witnesses`: the relation is an
  étale equivalence relation.
* `AlgebraicGeometry.Space.exists_quotient_of_witnesses`: the quotient and its universal
  property.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The target of `relation B S hS tR sR` is the image of `sR` in schemes over `S`. -/
theorem relation_target_eq {Ro Wo : BigFppfOver B S hS} (sR tR : Ro ⟶ Wo) :
    (relation B S hS tR sR).target = (Over.post (X := B.obj hS) B.inclusion).map sR := by
  dsimp [relation, PreRelation.target]
  rw [prod.lift_fst]

/-- The source of `relation B S hS tR sR` is the image of `tR` in schemes over `S`. -/
theorem relation_source_eq {Ro Wo : BigFppfOver B S hS} (sR tR : Ro ⟶ Wo) :
    (relation B S hS tR sR).source = (Over.post (X := B.obj hS) B.inclusion).map tR := by
  dsimp [relation, PreRelation.source]
  rw [prod.lift_snd]

/-- **Witnesses make an étale equivalence relation.** Two étale morphisms `s, t : R ⟶ W` of the
site which are jointly monic in schemes over `S`, with witnesses of reflexivity, symmetry and
transitivity, form an étale equivalence relation. -/
theorem isEtaleEquivalenceRelation_relation_of_witnesses
    {Wo Ro : BigFppfOver B S hS} (sR tR : Ro ⟶ Wo)
    (hsE : Etale ((BigFppfOver.toScheme B S hS).map sR))
    (htE : Etale ((BigFppfOver.toScheme B S hS).map tR))
    (hjm : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR))
    (refl : Wo ⟶ Ro) (hrefl₁ : refl ≫ sR = 𝟙 Wo) (hrefl₂ : refl ≫ tR = 𝟙 Wo)
    (symm : Ro ⟶ Ro) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ Ro)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR) :
    IsEtaleEquivalenceRelation (relation B S hS tR sR) := by
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have htarget := relation_target_eq B S hS sR tR
  have hsource := relation_source_eq B S hS sR tR
  have hFP : IsPullback (F.map (pullback.fst tR sR)) (F.map (pullback.snd tR sR))
      (F.map tR) (F.map sR) :=
    IsPullback.of_map (Over.forget S) (by rw [← F.map_comp, ← F.map_comp, pullback.condition])
      ((IsPullback.of_hasPullback tR sR).map (BigFppfOver.toScheme B S hS))
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · rw [htarget, hsource]
    refine EquivalenceRelation.isEquivalenceRelation
      { right_cancellation := hjm.right_cancellation
        r := F.map refl
        reflexivity₁ := by rw [← F.map_comp, hrefl₁, F.map_id]
        reflexivity₂ := by rw [← F.map_comp, hrefl₂, F.map_id]
        s := F.map symm
        symmetry₁ := by rw [← F.map_comp, hsymm₁]
        symmetry₂ := by rw [← F.map_comp, hsymm₂]
        c := PullbackCone.mk (F.map (pullback.fst tR sR)) (F.map (pullback.snd tR sR)) hFP.w
        isLimit := hFP.isLimit
        t := F.map comp
        transitivity₁ := by
          show F.map comp ≫ F.map sR = F.map (pullback.fst tR sR) ≫ F.map sR
          rw [← F.map_comp, ← F.map_comp, hcomp₁]
        transitivity₂ := by
          show F.map comp ≫ F.map tR = F.map (pullback.snd tR sR) ≫ F.map tR
          rw [← F.map_comp, ← F.map_comp, hcomp₂] }
  · rw [hsource]
    exact htE
  · rw [htarget]
    exact hsE

/-- **The quotient of an étale equivalence relation given by witnesses** is an algebraic space,
with a surjective étale atlas from `W` whose kernel pair is `R`, and every morphism from `W` to a
sheaf equalized by the two projections factors through it. -/
theorem exists_quotient_of_witnesses
    {Wo Ro : BigFppfOver B S hS} (sR tR : Ro ⟶ Wo)
    (hsE : Etale ((BigFppfOver.toScheme B S hS).map sR))
    (htE : Etale ((BigFppfOver.toScheme B S hS).map tR))
    (hjm : JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map sR)
      ((Over.post (X := B.obj hS) B.inclusion).map tR))
    (refl : Wo ⟶ Ro) (hrefl₁ : refl ≫ sR = 𝟙 Wo) (hrefl₂ : refl ≫ tR = 𝟙 Wo)
    (symm : Ro ⟶ Ro) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ Ro)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
      (q : yoneda.obj Wo ⟶ X),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      IsPullback (yoneda.map sR) (yoneda.map tR) q q := by
  have : EssentiallySmall.{u} B.Schemes := AlgebraicGeometry.essentiallySmall_schemeBelow B.cutoff
  have : EssentiallySmall.{u} (BigFppfOver B S hS) :=
    CategoryTheory.essentiallySmall_over (B.obj hS)
  have : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafifyEssentiallySmallSite _ _
  have : IsEtaleEquivalenceRelation (relation B S hS tR sR) :=
    isEtaleEquivalenceRelation_relation_of_witnesses B S hS sR tR hsE htE hjm refl hrefl₁ hrefl₂
      symm hsymm₁ hsymm₂ comp hcomp₁ hcomp₂
  exact ⟨_, isAlgebraicSpace_quotient_unconditional B S hS tR sR, quotientMap B S hS tR sR,
    quotientMap_surjective_unconditional B S hS tR sR, quotientMap_etale_unconditional B S hS tR sR,
    quotientMap_isPullback B S hS tR sR⟩

end AlgebraicGeometry.Space

end
