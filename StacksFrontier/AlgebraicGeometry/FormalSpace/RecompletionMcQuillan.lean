module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealMapToSpec
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineSupplement

/-!
# The completion of a McQuillan affine formal algebraic space is McQuillan

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a McQuillan affine formal
algebraic space over `S` — condition (4) of **Stacks 0AIC** — and let `W` be a closed set of
points of `X`. This file proves that the completion `X_{/W}` is McQuillan as well, which is
clause (2) of **Stacks 0GVV**.

The argument is the source's. Write `X = Spf(A)`; then `X_{/W} ⟶ X ⟶ Spec(A)` satisfies
condition (2) of Stacks 0AIC, and the library's Stacks 0AIC carries condition (2) to condition (4).
Condition (2) quantifies over the closed immersions of affine schemes of the site into
`X_{/W}`, so what has to be shown is that such a closed immersion composes with the inclusion
`X_{/W} ⟶ X` to a closed immersion; that is the predicate
`AlgebraicGeometry.FormalSpace.CompletionClosedSubscheme`, and it is established here for every
affine formal algebraic space.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CompletionClosedSubscheme`: a closed immersion of an object of
  the site into the completion of `Y` along `W` composes with the inclusion of the completion
  into `Y` to a closed immersion. Stated as a predicate on the pair `(Y, W)` so that it can be
  transported along an isomorphism of the ambient sheaf.

## Main results

* `AlgebraicGeometry.FormalSpace.completionClosedSubscheme_represented`: the predicate for the
  fppf sheaf represented by an *affine* object of the site. This is
  `AlgebraicGeometry.FormalSpace.isClosedImmersionInto_comp_completionSheafInclusion_affineOver`
  of `StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineClosedSubscheme` transported to
  the sheaves of `Type (u + 1)` in which the completions of formal algebraic spaces live.
* `AlgebraicGeometry.FormalSpace.completionClosedSubscheme_of_isAffineFormalAlgebraicSpace`:
  the predicate for every affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.hasAffineClosedImmersionCriterion_completionSheafULift`:
  **condition (2) of Stacks 0AIC passes to a completion**, with the same ring.
* `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheafULift`:
  **clause (2) of Stacks 0GVV** in the ambient spelling, quantified over the space and over the
  closed set of its own points. The registration for Stacks 0GVV clause (2) is on
  `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionAlong'` in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClauses`, which is this theorem in
  the source's spelling `X_{/T}` for `T` a closed subset of the points of a reduction.

## What is assumed

Nothing. In particular the former hypothesis `CompletionOfMcQuillanIsSpf` — the source's step
producing a weakly admissible topological ring presenting the completion — is gone: it is *not*
the cheapest route. The ring of condition (2) is the one `X` already has; only the
closed-immersion clause has to be re-established for the completion, and that is the geometric
content proved here and in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineClosedSubscheme`.

## Implementation notes

The predicate is transported in three steps: from the completion of a represented presheaf of
`Type u` to the completion of its universe lift (`completionClosedSubscheme_uliftRepresented`,
which rewrites the completion *subfunctor*, both completions being its sheafification and both
inclusions the sheafification of its inclusion); along an isomorphism of the ambient sheaf
(`completionClosedSubscheme_of_iso`, using the cartesian completion square of Stacks 0GVT to
commute the inclusions past the isomorphism); and from a represented sheaf to an arbitrary
affine formal algebraic space, by factoring a morphism out of a quasi-compact scheme through a
stage of a presentation (**Stacks 0AIA**) and cutting the factorisation down with the same
cartesian square.

That the stage maps of a presentation are monomorphisms, which is what makes the cut-down
morphism into the stage's completion a closed immersion, is **Stacks 0AI9** followed by
`AlgebraicGeometry.FormalSpace.mono_of_isClosedImmersionInto`.

## References

* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0GVT](https://stacks.math.columbia.edu/tag/0GVT)
* [Stacks Project, Tag 0GVV](https://stacks.math.columbia.edu/tag/0GVV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of fppf sheaves is a closed immersion: it is representable, and every base
change of it along a represented sheaf is an isomorphism of objects of the site, hence a closed
immersion of schemes. -/
private theorem isClosedImmersionInto_of_isIso {X Y : FppfSheaf B S hS} (g : X ⟶ Y) [IsIso g] :
    IsClosedImmersionInto B S hS g := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let ff := Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)
  let _ := ff.full
  let _ := ff.faithful
  refine ⟨Functor.relativelyRepresentable.of_isIso _ _, ?_⟩
  intro A V p fst snd hpb
  have : IsIso ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map snd) :=
    hpb.isIso_snd_of_isIso
  have : IsIso snd := ff.isIso_of_isIso_map snd
  show _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- A closed immersion of an object of the site into the completion of `Y` along `W` composes
with the inclusion of the completion into `Y` to a closed immersion. This is the property that
the affine case of clause (2) of Stacks 0GVV establishes, as a predicate on the pair `(Y, W)`
so that it can be transported. -/
abbrev CompletionClosedSubscheme (Y : FppfSheaf B S hS)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) : Prop :=
  ∀ (Z : BigFppfOver B S hS)
    (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Z ⟶
      Space.completionSheafULift B S hS Y W),
    IsClosedImmersionInto B S hS c →
    IsClosedImmersionInto B S hS (c ≫ Space.completionSheafULiftInclusion B S hS Y W)

private theorem completionClosedSubscheme_uliftRepresented
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (Space.points B S hS X))
    (h : ∀ (Z : BigFppfOver B S hS)
      (c : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Z ⟶
        Space.completionSheaf B S hS X T),
      IsClosedImmersionInto B S hS c →
      IsClosedImmersionInto B S hS (c ≫ Space.completionSheafInclusion B S hS X T)) :
    CompletionClosedSubscheme B S hS ⟨X ⋙ uliftFunctor.{u + 1}, hY⟩
      ((Space.pointsULiftEquiv.{u + 1} B S hS X).symm ⁻¹' T) := by
  simp only [CompletionClosedSubscheme, Space.completionSheafULift,
    Space.completionSheafULiftInclusion]
  rw [← completionSubfunctor_eq_completionSubfunctorULift B S hS X T]
  intro Z c hc
  rw [← Category.assoc]
  exact MorphismProperty.RespectsIso.postcomp _
    (Space.isoSheafifySheaf B S hS
      (⟨X ⋙ uliftFunctor.{u + 1}, hY⟩ : FppfSheaf B S hS)).inv _ (h Z c hc)

/-- The property transports along an isomorphism of the ambient fppf sheaf: the completions are
carried into one another by `completionSheafULiftIsoOfIso`, and the inclusions commute with the
isomorphism by the cartesian completion square. -/
private theorem completionClosedSubscheme_of_iso {Y Y' : FppfSheaf B S hS} (e : Y ≅ Y')
    (W' : Set (Space.pointsULift.{u + 1} B S hS Y'.obj))
    (h : CompletionClosedSubscheme B S hS Y' W') :
    CompletionClosedSubscheme B S hS Y
      (Space.pointsMapULift B S hS Y.obj e.hom.hom ⁻¹' W') := by
  intro Z c hc
  have hsq := Space.isPullback_completionSheafMapULift B S hS e.hom
    (Space.pointsMapULift B S hS Y.obj e.hom.hom ⁻¹' W') W'
    (Set.Subset.refl _) (Set.Subset.refl _)
  have : IsIso (completionSheafULiftIsoOfIso B S hS e W').hom := inferInstance
  have hkey := h Z (c ≫ (completionSheafULiftIsoOfIso B S hS e W').hom)
    (isClosedImmersionInto_comp' _ _ hc
      (isClosedImmersionInto_of_isIso B S hS (completionSheafULiftIsoOfIso B S hS e W').hom))
  rw [Category.assoc,
    show (completionSheafULiftIsoOfIso B S hS e W').hom ≫
        Space.completionSheafULiftInclusion B S hS Y' W' =
      Space.completionSheafULiftInclusion B S hS Y
        (Space.pointsMapULift B S hS Y.obj e.hom.hom ⁻¹' W') ≫ e.hom from hsq.w.symm,
    ← Category.assoc] at hkey
  exact (MorphismProperty.cancel_right_of_respectsIso
    (MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) _ e.hom).mp hkey

/-- **A closed subscheme of the completion of an affine object of the site along a closed set of
its points is a closed subscheme of that object.** -/
theorem completionClosedSubscheme_represented (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (W : Set (Space.pointsULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V).obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V).obj) W) :
    CompletionClosedSubscheme B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V) W := by
  let J := BigFppfOver.topology B S hS
  let hA := contains_spec_globalSections B S hS V
  let fS := globalSectionsStructureMap B S hS V
  let U₀ : BigFppfOver B S hS := affineOver B S hS hA fS
  let Yg : FppfSheaf B S hS := ⟨yoneda.obj U₀ ⋙ uliftFunctor.{u + 1},
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U₀).isSheaf⟩
  let e : (Sheaf.sheafifiedYoneda J).obj V ≅ Yg :=
    ((Sheaf.sheafifiedYoneda J).mapIso (affineOverGlobalSectionsIso B S hS V)).symm ≪≫
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).app U₀
  let _ := Space.pointTopologyULift.{u + 1} B S hS ((Sheaf.sheafifiedYoneda J).obj V).obj
  let _ := Space.pointTopologyULift.{u + 1} B S hS Yg.obj
  let _ := Space.pointTopology B S hS (yoneda.obj U₀)
  have hW' : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Yg.obj)
      (Space.pointsMapULift B S hS Yg.obj e.inv.hom ⁻¹' W) :=
    hW.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS e.inv.hom)
  have hT₀ : @IsClosed _ (Space.pointTopology B S hS (yoneda.obj U₀))
      (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀) ⁻¹'
        (Space.pointsMapULift B S hS Yg.obj e.inv.hom ⁻¹' W)) :=
    hW'.preimage (Space.pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U₀)).continuous
  have hWeq : Space.pointsMapULift B S hS ((Sheaf.sheafifiedYoneda J).obj V).obj e.hom.hom ⁻¹'
      (Space.pointsMapULift B S hS Yg.obj e.inv.hom ⁻¹' W) = W :=
    preimage_pointsMapULift_inv_preimage_hom B S hS e.symm W
  have hbridgeSet : (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀)).symm ⁻¹'
      (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀) ⁻¹'
        (Space.pointsMapULift B S hS Yg.obj e.inv.hom ⁻¹' W)) =
      Space.pointsMapULift B S hS Yg.obj e.inv.hom ⁻¹' W := by
    rw [← Set.preimage_comp, Equiv.self_comp_symm, Set.preimage_id]
  rw [← hWeq]
  refine completionClosedSubscheme_of_iso B S hS e _ ?_
  rw [← hbridgeSet]
  exact completionClosedSubscheme_uliftRepresented B S hS (yoneda.obj U₀)
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U₀).isSheaf _
    (fun Z c hc ↦ isClosedImmersionInto_comp_completionSheafInclusion_affineOver
      B S hS hA fS _ hT₀ Z c hc)

/-- The completion of an affine formal algebraic space along a closed set of its points is an
affine formal algebraic space. -/
private theorem isAffineFormalAlgebraicSpace_completionSheafULift_of_isClosed
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W) :
    IsAffineFormalAlgebraicSpace B S hS (Space.completionSheafULift B S hS X W) :=
  ⟨satisfiesSetTheoreticCondition_completionSheafULift B S hS X hX W hW,
    exists_affinePresentation_completionSheafULift' B S hS X hX W hW⟩

/-- **The key step of clause (2) of Stacks 0GVV.** Let `X` be an affine formal algebraic space
over `S` and let `W` be a closed set of its points. A closed immersion of an object of the site
into the completion `X_{/W}` composes with the inclusion `X_{/W} ⟶ X` to a closed immersion.

The source `Z` of such a closed immersion is affine (Stacks 0AIC), so the composite
`Z ⟶ X` factors through a stage `X_λ` of a presentation of `X` (**Stacks 0AIA**). The cartesian
completion square of Stacks 0GVT lifts the factorisation to a morphism
`Z ⟶ (X_λ)_{/W_λ}`, which is a closed immersion into `(X_λ)_{/W_λ}` because
`(X_λ)_{/W_λ} ⟶ X_{/W}` is a base change of the monomorphism `X_λ ⟶ X` (**Stacks 0AI9**). The
affine case `completionClosedSubscheme_represented` then makes `Z ⟶ X_λ` a closed immersion,
and `X_λ ⟶ X` is one as well. -/
theorem completionClosedSubscheme_of_isAffineFormalAlgebraicSpace (X : FppfSheaf B S hS)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W) :
    CompletionClosedSubscheme B S hS X W := by
  intro Z a ha
  have hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) :=
    isAffine_of_isClosedImmersionInto B S hS
      (isAffineFormalAlgebraicSpace_completionSheafULift_of_isClosed B S hS X hX W hW) a ha
  obtain ⟨-, I, pre, hne, hdir, D, hD, ⟨eX⟩⟩ := id hX
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  obtain ⟨lam, g, hg⟩ := exists_factor_through_thickening' B S hS I D
    (fun _ _ q ↦ (hD q).1) X eX (yoneda.obj Z)
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS Z hZaff)
    (a ≫ Space.completionSheafULiftInclusion B S hS X W)
  let stage : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.obj lam)) ⟶ X :=
    colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) lam ≫ eX.inv
  have hstageci : IsClosedImmersionInto B S hS stage :=
    isClosedImmersionInto_colimitι B S hS D hD X eX.symm lam
  have hstagemono : Mono stage := mono_of_isClosedImmersionInto' stage hstageci
  let _ := Space.pointTopologyULift.{u + 1} B S hS X.obj
  let _ := Space.pointTopologyULift.{u + 1} B S hS
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.obj lam))).obj
  have hWlam : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj lam))).obj)
      (Space.pointsMapULift B S hS _ stage.hom ⁻¹' W) :=
    hW.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS stage.hom)
  have hsq := Space.isPullback_completionSheafMapULift B S hS stage
    (Space.pointsMapULift B S hS _ stage.hom ⁻¹' W) W
    (Set.Subset.refl _) (Set.Subset.refl _)
  have hw : g ≫ stage = a ≫ Space.completionSheafULiftInclusion B S hS X W := hg
  let c := hsq.lift g a hw
  have hcfst : c ≫ Space.completionSheafULiftInclusion B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj lam)))
      (Space.pointsMapULift B S hS _ stage.hom ⁻¹' W) = g := hsq.lift_fst g a hw
  have hcsnd : c ≫ Space.completionSheafMapULift B S hS stage
      (Space.pointsMapULift B S hS _ stage.hom ⁻¹' W) W (Set.Subset.refl _) = a :=
    hsq.lift_snd g a hw
  have := hsq.mono_snd_of_mono
  have hcci : IsClosedImmersionInto B S hS c :=
    isClosedImmersionInto_of_comp_mono' c _ (hsq.mono_snd_of_mono) (hcsnd ▸ ha)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (D.obj lam))) := (D.obj lam).property
  have hgci : IsClosedImmersionInto B S hS g :=
    hcfst ▸ completionClosedSubscheme_represented B S hS
      ((BigAffineFppf.inclusion B S hS).obj (D.obj lam)) _ hWlam Z c hcci
  rw [← hw]
  exact isClosedImmersionInto_comp' _ _ hgci hstageci

/-- **Condition (2) of Stacks 0AIC passes to a completion.** If `X` is a McQuillan affine formal
algebraic space over `S` and `W` is a closed set of its points, then the completion `X_{/W}`
satisfies condition (2) of Stacks 0AIC, with the same ring: the morphism `X_{/W} ⟶ Spec A` is
the one of `X` precomposed with the inclusion, and a closed immersion of an affine scheme into
`X_{/W}` is a closed immersion into `X` by
`completionClosedSubscheme_of_isAffineFormalAlgebraicSpace`.

This is the source's step for clause (2) of Stacks 0GVV: *write `X = Spf(A)` and observe that
`X_{/T} ⟶ X ⟶ Spec(A)` satisfies condition (2) of Stacks 0AIC*. -/
theorem hasAffineClosedImmersionCriterion_completionSheafULift (X : FppfSheaf B S hS)
    (hX : HasSomeSurjectivePresentation B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W) :
    HasAffineClosedImmersionCriterionMapToSpec B S hS (Space.completionSheafULift B S hS X W) := by
  obtain ⟨-, A, φ, hφ⟩ :=
    hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation B S hS hX
  refine ⟨isAffineFormalAlgebraicSpace_completionSheafULift_of_isClosed B S hS X hX.1 W hW, A,
    { app := fun T g ↦ φ.app T (g ≫ Space.completionSheafULiftInclusion B S hS X W)
      app_naturality := fun T T' uu g ↦
        φ.app_naturality T T' uu (g ≫ Space.completionSheafULiftInclusion B S hS X W) }, ?_⟩
  intro T g hg
  exact hφ T _ (completionClosedSubscheme_of_isAffineFormalAlgebraicSpace B S hS X hX.1 W hW
    ((BigAffineFppf.inclusion B S hS).obj T) g hg)

/-- **Clause (2) of Stacks 0GVV, in the ambient spelling.** The completion of a McQuillan affine
formal algebraic space over `S` along a closed set of its points is McQuillan.

Condition (2) of Stacks 0AIC holds for the completion by
`hasAffineClosedImmersionCriterion_completionSheafULift`, and the library's Stacks 0AIC carries
it to condition (4), which is what McQuillan means here. -/
theorem hasSomeSurjectivePresentation_completionSheafULift (X : FppfSheaf B S hS)
    (hX : HasSomeSurjectivePresentation B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W) :
    HasSomeSurjectivePresentation B S hS (Space.completionSheafULift B S hS X W) :=
  (HasAffineClosedImmersionCriterionMapToSpec.hasAllSurjectivePresentations B S hS
    (hasAffineClosedImmersionCriterion_completionSheafULift B S hS X hX W
      hW)).hasSomeSurjectivePresentation B S hS

end AlgebraicGeometry.FormalSpace

end
