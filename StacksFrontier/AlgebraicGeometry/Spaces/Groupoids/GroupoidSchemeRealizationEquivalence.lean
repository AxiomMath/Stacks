module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.RestrictionCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering

/-!
# The quotient stacks of two groupoid schemes related by a fully faithful fppf morphism agree

Let `f : G ⟶ H` be a morphism of groupoid schemes over `S` which is *fully faithful on
generalized points* — every evaluation `G(T) ⥤ H(T)` is a fully faithful functor — and whose map
on object schemes is flat, locally of finite presentation and surjective.  Then the induced
1-morphism `[G] ⟶ [H]` of the quotient stacks of the two realizations is an equivalence over the
big fppf site.

Both clauses of the criterion of **Stacks 046T** are checked at the realization: clause (1), that
the source–target square of the morphism be cartesian, from full faithfulness of the evaluations;
clause (2), that the saturation map be a surjection of fppf sheaves, from the map on objects being
an fppf covering.

This is the step by which a division of a groupoid scheme in the sense of **Stacks 04S4** leaves
the quotient stack unchanged: the descent morphism of a division is fully faithful on generalized
points, and its map on objects is the quotient morphism, which is finite locally free and
surjective.

## Main results

* `AlgebraicGeometry.Stack.faithful_evaluation_of_injective_arrows` and
  `…full_evaluation_of_exists_arrow`: an evaluation of a morphism of groupoids in presheaves is
  faithful, respectively full, as soon as its map on arrows is injective, respectively surjective,
  on the generalized arrows carrying a prescribed source and target.
* `Stacks.Groupoids.GroupoidScheme.fullyFaithful_realizationHom_evaluation`: every evaluation of
  the realization of `f` is fully faithful.
* `Stacks.Groupoids.GroupoidScheme.isPullback_realizationHom`: clause (1) of **Stacks 046T**.
* `Stacks.Groupoids.GroupoidScheme.isLocallySurjective_saturation_realizationHom`: clause (2) of
  **Stacks 046T**.
* `Stacks.Groupoids.GroupoidScheme.nonempty_isEquivalenceOver_quotientStackMap_realizationHom`:
  the induced 1-morphism of quotient stacks is an equivalence over the site.

## Implementation notes

The evaluation of the realization at a test object `T` of the site has the sections of the
represented presheaf of the object scheme as its objects, and
`AlgebraicGeometry.Space.yonedaSchemePointEquiv` identifies those with the generalized points of
the object scheme over the scheme underlying `T`; the arrows carrying a prescribed source and
target are identified with the generalized arrows of the arrow scheme carrying the corresponding
source and target by `AlgebraicGeometry.Space.yonedaSchemePointEquiv_map`.

Fullness and faithfulness are therefore not transported by building an isomorphism of categories
— whose objects would themselves have to be transported along those identifications — but one at
a time, through the two criteria stated first, which ask only for a bijection between generalized
arrows with prescribed endpoints.  That keeps every use of the identifications inside the proof of
a proposition, where it is an equation between morphisms of schemes.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ v₁ w₁

namespace AlgebraicGeometry.Stack

/-- **A criterion for an evaluation of a morphism of groupoids in presheaves to be faithful.**
It suffices that two generalized arrows with the same source, the same target and the same image
be equal. -/
theorem faithful_evaluation_of_injective_arrows {D : Type u₁} [Category.{v₁} D]
    {G H : Deformation.GroupoidInFunctors.{u₁, v₁, w₁} Dᵒᵖ}
    (Φ : Deformation.GroupoidInFunctors.Hom G H) (T : Dᵒᵖ)
    (hinj : ∀ a b : G.arrows.obj T, G.source.app T a = G.source.app T b →
      G.target.app T a = G.target.app T b →
      Φ.mapArrows.app T a = Φ.mapArrows.app T b → a = b) :
    (Φ.evaluation T).Faithful := by
  refine ⟨?_⟩
  intro x y φ ψ hφψ
  refine (G.evaluationArrowEquiv T x y).injective (Subtype.ext ?_)
  refine hinj _ _ ?_ ?_ ?_
  · exact ((G.evaluationArrowEquiv T x y φ).2.1).trans
      ((G.evaluationArrowEquiv T x y ψ).2.1).symm
  · exact ((G.evaluationArrowEquiv T x y φ).2.2).trans
      ((G.evaluationArrowEquiv T x y ψ).2.2).symm
  · exact ((Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow Φ T φ).symm.trans
      (congrArg (fun m => (H.evaluationArrowEquiv T (Φ.mapObjects.app T x)
        (Φ.mapObjects.app T y) m).1) hφψ)).trans
      (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow Φ T ψ)

/-- **A criterion for an evaluation of a morphism of groupoids in presheaves to be full.** It
suffices that every generalized arrow of the target whose source and target are the images of
prescribed generalized points be the image of a generalized arrow with those endpoints. -/
theorem full_evaluation_of_exists_arrow {D : Type u₁} [Category.{v₁} D]
    {G H : Deformation.GroupoidInFunctors.{u₁, v₁, w₁} Dᵒᵖ}
    (Φ : Deformation.GroupoidInFunctors.Hom G H) (T : Dᵒᵖ)
    (hsurj : ∀ (x y : G.objects.obj T) (b : H.arrows.obj T),
      H.source.app T b = Φ.mapObjects.app T x →
      H.target.app T b = Φ.mapObjects.app T y →
      ∃ a : G.arrows.obj T, G.source.app T a = x ∧ G.target.app T a = y ∧
        Φ.mapArrows.app T a = b) :
    (Φ.evaluation T).Full := by
  refine ⟨?_⟩
  intro x y φ
  obtain ⟨a, hsa, hta, hma⟩ := hsurj x y
    (H.evaluationArrowEquiv T (Φ.mapObjects.app T x) (Φ.mapObjects.app T y) φ).1
    (H.evaluationArrowEquiv T (Φ.mapObjects.app T x) (Φ.mapObjects.app T y) φ).2.1
    (H.evaluationArrowEquiv T (Φ.mapObjects.app T x) (Φ.mapObjects.app T y) φ).2.2
  refine ⟨(G.evaluationArrowEquiv T x y).symm ⟨a, hsa, hta⟩, ?_⟩
  refine (H.evaluationArrowEquiv T (Φ.mapObjects.app T x)
    (Φ.mapObjects.app T y)).injective (Subtype.ext ?_)
  refine (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow Φ T _).trans ?_
  refine Eq.trans (congrArg (fun z => Φ.mapArrows.app T z)
    (congrArg Subtype.val ((G.evaluationArrowEquiv T x y).apply_symm_apply _))) ?_
  exact hma

end AlgebraicGeometry.Stack

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

section Dictionary

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left) (T : (BigFppfOver C S hS)ᵒᵖ)

/-- A generalized arrow of the realization has, as its own source, the generalized point of the
object scheme named by the source of the realization. -/
theorem yonedaSchemePointEquiv_realization_source
    (a : (G.realization C hS hU hR hP).arrows.obj.obj T) :
    yonedaSchemePointEquiv C hS hR T a ≫ G.source =
      yonedaSchemePointEquiv C hS hU T
        ((G.realization C hS hU hR hP).toGroupoidInFunctors.source.app T a) :=
  (yonedaSchemePointEquiv_map C hS hR hU G.source T a).symm

/-- A generalized arrow of the realization has, as its own target, the generalized point of the
object scheme named by the target of the realization. -/
theorem yonedaSchemePointEquiv_realization_target
    (a : (G.realization C hS hU hR hP).arrows.obj.obj T) :
    yonedaSchemePointEquiv C hS hR T a ≫ G.target =
      yonedaSchemePointEquiv C hS hU T
        ((G.realization C hS hU hR hP).toGroupoidInFunctors.target.app T a) :=
  (yonedaSchemePointEquiv_map C hS hR hU G.target T a).symm

end Dictionary

section Realization

variable {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) (C : BigFppfSite.{u})
  (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  (hU' : C.Contains H.objects.left) (hR' : C.Contains H.arrows.left)
  (hP' : C.Contains (pullback H.source H.target).left)

/-- The generalized arrow of `H` named by the image of a generalized arrow of `G` under the
realization of `f` is the composite with the map on arrow schemes. -/
theorem yonedaSchemePointEquiv_realizationHom_mapArrows (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (G.realization C hS hU hR hP).arrows.obj.obj T) :
    yonedaSchemePointEquiv C hS hR' T
        ((realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapArrows.app T a) =
      yonedaSchemePointEquiv C hS hR T a ≫ f.mapArrows :=
  yonedaSchemePointEquiv_map C hS hR hR' f.mapArrows T a

/-- The generalized point of the object scheme of `H` named by the image of a generalized point
of the object scheme of `G` under the realization of `f` is the composite with the map on object
schemes. -/
theorem yonedaSchemePointEquiv_realizationHom_mapObjects (T : (BigFppfOver C S hS)ᵒᵖ)
    (x : (G.realization C hS hU hR hP).objects.obj.obj T) :
    yonedaSchemePointEquiv C hS hU' T
        ((realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapObjects.app T x) =
      yonedaSchemePointEquiv C hS hU T x ≫ f.mapObjects :=
  yonedaSchemePointEquiv_map C hS hU hU' f.mapObjects T x

section FullyFaithful

variable (hf : ∀ T : Over S, Nonempty (f.evaluation T).FullyFaithful)

include hf

/-- The evaluation of the realization of a morphism of groupoid schemes which is fully faithful on
generalized points is faithful. -/
theorem faithful_realizationHom_evaluation (T : (BigFppfOver C S hS)ᵒᵖ) :
    ((realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.evaluation T).Faithful := by
  classical
  refine AlgebraicGeometry.Stack.faithful_evaluation_of_injective_arrows _ T ?_
  intro a b hsab htab hmab
  have hs := ((yonedaSchemePointEquiv_realization_source G C hS hU hR hP T a).trans
      (congrArg (yonedaSchemePointEquiv C hS hU T) hsab)).trans
      (yonedaSchemePointEquiv_realization_source G C hS hU hR hP T b).symm
  have ht := ((yonedaSchemePointEquiv_realization_target G C hS hU hR hP T a).trans
      (congrArg (yonedaSchemePointEquiv C hS hU T) htab)).trans
      (yonedaSchemePointEquiv_realization_target G C hS hU hR hP T b).symm
  have hm : yonedaSchemePointEquiv C hS hR T a ≫ f.mapArrows =
      yonedaSchemePointEquiv C hS hR T b ≫ f.mapArrows :=
    ((yonedaSchemePointEquiv_realizationHom_mapArrows f C hS hU hR hP hU' hR' hP' T a).symm.trans
      (congrArg (yonedaSchemePointEquiv C hS hR' T) hmab)).trans
      (yonedaSchemePointEquiv_realizationHom_mapArrows f C hS hU hR hP hU' hR' hP' T b)
  refine (yonedaSchemePointEquiv C hS hR T).injective ?_
  let α : G.EvaluationHom (yonedaSchemePointEquiv C hS hR T a ≫ G.source)
      (yonedaSchemePointEquiv C hS hR T a ≫ G.target) :=
    ⟨yonedaSchemePointEquiv C hS hR T a, rfl, rfl⟩
  let β : G.EvaluationHom (yonedaSchemePointEquiv C hS hR T a ≫ G.source)
      (yonedaSchemePointEquiv C hS hR T a ≫ G.target) :=
    ⟨yonedaSchemePointEquiv C hS hR T b, hs.symm, ht.symm⟩
  refine congrArg EvaluationHom.arrow
    ((hf ((siteToOver C hS).obj T.unop)).some.map_injective (f := α) (g := β) ?_)
  exact EvaluationHom.ext hm

/-- The evaluation of the realization of a morphism of groupoid schemes which is fully faithful on
generalized points is full. -/
theorem full_realizationHom_evaluation (T : (BigFppfOver C S hS)ᵒᵖ) :
    ((realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.evaluation T).Full := by
  classical
  refine AlgebraicGeometry.Stack.full_evaluation_of_exists_arrow _ T ?_
  intro x y b hsb htb
  have hs : yonedaSchemePointEquiv C hS hR' T b ≫ H.source =
      yonedaSchemePointEquiv C hS hU T x ≫ f.mapObjects :=
    ((yonedaSchemePointEquiv_realization_source H C hS hU' hR' hP' T b).trans
      (congrArg (yonedaSchemePointEquiv C hS hU' T) hsb)).trans
      (yonedaSchemePointEquiv_realizationHom_mapObjects f C hS hU hR hP hU' hR' hP' T x)
  have ht : yonedaSchemePointEquiv C hS hR' T b ≫ H.target =
      yonedaSchemePointEquiv C hS hU T y ≫ f.mapObjects :=
    ((yonedaSchemePointEquiv_realization_target H C hS hU' hR' hP' T b).trans
      (congrArg (yonedaSchemePointEquiv C hS hU' T) htb)).trans
      (yonedaSchemePointEquiv_realizationHom_mapObjects f C hS hU hR hP hU' hR' hP' T y)
  let θ : ((f.evaluation ((siteToOver C hS).obj T.unop)).obj
        (yonedaSchemePointEquiv C hS hU T x)) ⟶
      ((f.evaluation ((siteToOver C hS).obj T.unop)).obj
        (yonedaSchemePointEquiv C hS hU T y)) :=
    ⟨yonedaSchemePointEquiv C hS hR' T b, hs, ht⟩
  set e := (hf ((siteToOver C hS).obj T.unop)).some.preimage θ
  have hearrow : EvaluationHom.arrow e ≫ f.mapArrows = yonedaSchemePointEquiv C hS hR' T b :=
    congrArg EvaluationHom.arrow ((hf ((siteToOver C hS).obj T.unop)).some.map_preimage θ)
  have hap := (yonedaSchemePointEquiv C hS hR T).apply_symm_apply (EvaluationHom.arrow e)
  refine ⟨(yonedaSchemePointEquiv C hS hR T).symm (EvaluationHom.arrow e), ?_, ?_, ?_⟩
  · refine (yonedaSchemePointEquiv C hS hU T).injective ?_
    refine Eq.trans (yonedaSchemePointEquiv_realization_source G C hS hU hR hP T _).symm ?_
    exact (congrArg (fun k => k ≫ G.source) hap).trans (EvaluationHom.source_eq e)
  · refine (yonedaSchemePointEquiv C hS hU T).injective ?_
    refine Eq.trans (yonedaSchemePointEquiv_realization_target G C hS hU hR hP T _).symm ?_
    exact (congrArg (fun k => k ≫ G.target) hap).trans (EvaluationHom.target_eq e)
  · refine (yonedaSchemePointEquiv C hS hR' T).injective ?_
    refine Eq.trans
      (yonedaSchemePointEquiv_realizationHom_mapArrows f C hS hU hR hP hU' hR' hP' T _) ?_
    exact (congrArg (fun k => k ≫ f.mapArrows) hap).trans hearrow

/-- **The evaluation of the realization of a morphism of groupoid schemes which is fully faithful
on generalized points is fully faithful.** -/
noncomputable def fullyFaithful_realizationHom_evaluation (T : (BigFppfOver C S hS)ᵒᵖ) :
    ((realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.evaluation T).FullyFaithful :=
  letI := full_realizationHom_evaluation f C hS hU hR hP hU' hR' hP' hf T
  letI := faithful_realizationHom_evaluation f C hS hU hR hP hU' hR' hP' hf T
  Functor.FullyFaithful.ofFullyFaithful _

/-- **Clause (1) of Stacks 046T for the realization of a morphism of groupoid schemes which is
fully faithful on generalized points.** The square formed by the map on arrow spaces, the two
source–target pairs and the self-product of the map on object spaces is cartesian. -/
theorem isPullback_realizationHom :
    IsPullback (realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapArrows
      (prod.lift (G.realization C hS hU hR hP).toGroupoidInFunctors.source
        (G.realization C hS hU hR hP).toGroupoidInFunctors.target)
      (prod.lift (H.realization C hS hU' hR' hP').toGroupoidInFunctors.source
        (H.realization C hS hU' hR' hP').toGroupoidInFunctors.target)
      (prod.map (realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapObjects
        (realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapObjects) :=
  AlgebraicGeometry.Stack.isPullback_mapArrows_of_evaluation_fullyFaithful
    (realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom
    (fullyFaithful_realizationHom_evaluation f C hS hU hR hP hU' hR' hP' hf)

end FullyFaithful

/-- **Clause (2) of Stacks 046T for the realization of a morphism of groupoid schemes whose map on
object schemes is an fppf covering.** The saturation map `U ×_{U', t'} R' ⟶ R' ⟶ U'` is a
surjection of fppf sheaves.

The map on object spaces of the realization is the Yoneda image of the map on object schemes, so
`AlgebraicGeometry.Space.isFppfCovering_yoneda_map` makes the one-element family it forms an fppf
covering, and
`AlgebraicGeometry.Space.isLocallySurjective_source_pullback_of_isFppfCovering_mapObjects`
concludes. -/
theorem isLocallySurjective_saturation_realizationHom
    (hflat : Flat f.mapObjects.left)
    (hlfp : LocallyOfFinitePresentation f.mapObjects.left)
    (hsurj : Surjective f.mapObjects.left) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd
          (ObjectProperty.homMk
            (realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapObjects :
              (G.realization C hS hU hR hP).objects ⟶
                (H.realization C hS hU' hR' hP').objects)
          (H.realization C hS hU' hR' hP').target ≫
        (H.realization C hS hU' hR' hP').source).hom) := by
  have hcov : IsFppfCovering C S hS
      (fun _ : PUnit.{u + 1} => yoneda.obj (schemeSiteObject C hS hU))
      (fun _ => yoneda.map (schemeSiteMap C hS hU hU' f.mapObjects)) := by
    refine isFppfCovering_yoneda_map C S hS (fun _ : PUnit.{u + 1} => schemeSiteObject C hS hU)
      (fun _ => schemeSiteMap C hS hU hU' f.mapObjects) (fun _ => ?_) (fun _ => ?_) (fun z => ?_)
    · rw [toScheme_map_schemeSiteMap_eq C hS hU hU' f.mapObjects]
      exact hflat
    · rw [toScheme_map_schemeSiteMap_eq C hS hU hU' f.mapObjects]
      exact hlfp
    · obtain ⟨y, hy⟩ := hsurj.surj z
      refine ⟨PUnit.unit, y, ?_⟩
      rw [toScheme_map_schemeSiteMap_eq C hS hU hU' f.mapObjects]
      exact hy
  exact isLocallySurjective_source_pullback_of_isFppfCovering_mapObjects C S hS
    (realizationBase C hS) (G.realization C hS hU hR hP) (H.realization C hS hU' hR' hP')
    (realizationHom f C hS hU hR hP hU' hR' hP') hcov

/-- **The quotient stacks of two groupoid schemes related by a morphism which is fully faithful on
generalized points and whose map on object schemes is an fppf covering agree.** The 1-morphism
`[G] ⟶ [H]` of **Stacks 046Q** induced by the realization of `f` is an equivalence over the big
fppf site of `S`.

Both clauses of the criterion of **Stacks 046T** are checked at the realization, by
`Stacks.Groupoids.GroupoidScheme.isPullback_realizationHom` and
`…isLocallySurjective_saturation_realizationHom`. -/
theorem nonempty_isEquivalenceOver_quotientStackMap_realizationHom
    (hf : ∀ T : Over S, Nonempty (f.evaluation T).FullyFaithful)
    (hflat : Flat f.mapObjects.left)
    (hlfp : LocallyOfFinitePresentation f.mapObjects.left)
    (hsurj : Surjective f.mapObjects.left) :
    Nonempty (Functor.IsEquivalenceOver
      (AlgebraicGeometry.Stack.quotientStack (G.realization C hS hU hR hP)).p
      (AlgebraicGeometry.Stack.quotientStack (H.realization C hS hU' hR' hP')).p
      (AlgebraicGeometry.Stack.quotientStackMap
        (realizationHom f C hS hU hR hP hU' hR' hP')).toFunctor) :=
  (AlgebraicGeometry.Stack.quotientStackMap_isEquivalenceOver_iff
    (realizationHom f C hS hU hR hP hU' hR' hP')).mpr
      ⟨isPullback_realizationHom f C hS hU hR hP hU' hR' hP' hf,
        isLocallySurjective_saturation_realizationHom f C hS hU hR hP hU' hR' hP'
          hflat hlfp hsurj⟩

end Realization

end Stacks.Groupoids.GroupoidScheme

end
