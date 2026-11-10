module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineBaseCoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSurjective

/-!
# The affine, atlas and flat-cover criteria for a closed immersion of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. This file adds conditions (3), (4) and (5) of Stacks 0GHY to
the equivalences of
`StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriteria` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent`:

3. for every affine scheme `T` and morphism `T ⟶ Y` the projection `X ×_Y T ⟶ T` is a closed
   immersion;
4. there is a covering `{Y_j ⟶ Y}` as in Stacks 0AIM with each `X ×_Y Y_j ⟶ Y_j` a closed
   immersion;
5. there is a morphism `Z ⟶ Y` of formal algebraic spaces, representable by algebraic spaces,
   surjective, flat and locally of finite presentation, with `X ×_Y Z ⟶ Z` a closed immersion.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasFlatClosedImmersionCover`: condition (5).

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersion_iff_forall_affine`: **Stacks 0GHY** for
  conditions (1) and (3).
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_iff_exists_affineEtaleCover`: **Stacks
  0GHY** for conditions (1) and (4).
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_iff_hasFlatClosedImmersionCover`: **Stacks
  0GHY** for conditions (1) and (5).
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_of_isSurjective_of_flat`: **Stacks
  03Y8** in the form condition (5) needs it — a morphism representable by algebraic spaces,
  flat, locally of finite presentation and surjective *on points* is a surjection of fppf
  sheaves.

## Implementation notes

Condition (3) is condition (2) restricted to the affine objects of the site, so the content is
that the condition on the target is Zariski local. That is proved by covering a scheme-valued
point `T ⟶ Y` by affine ones: every object of the site is covered by affine objects of the
site flat and locally of finite presentation over it, by
`AlgebraicGeometry.BigFppfOver.exists_affine_mem_of_mem_topology` applied to the trivial
covering sieve, and such a family generates a covering sieve, hence induces a surjection of
the coproduct of the corresponding representable sheaves onto the representable sheaf of `T`.
The base change of `X ×_Y T ⟶ T` along a member of that family is the base change of `f` along
the composite affine point, so the descent step
`AlgebraicGeometry.FormalSpace.isClosedImmersion_of_locallySurjectiveFamily` applies; no
hypothesis on `f` is needed, since that step assumes none.

Condition (4) is the covering of Stacks 0AIM, recorded as
`AlgebraicGeometry.FormalSpace.IsAffineEtaleCover`. Its necessity is
`AlgebraicGeometry.FormalSpace.exists_atlas_isClosedImmersion_pullback_snd` and needs the
target to be a formal algebraic space, which is where the covering comes from; its sufficiency
is again the descent step, the covering being a surjection of sheaves, and needs nothing of
`X` and `Y`.

Condition (5) is spelled with the notions the source uses for a morphism representable by
algebraic spaces: surjectivity on points (Stacks 0GHP, which is
`AlgebraicGeometry.FormalSpace.IsSurjective`), and flatness and local finite presentation
tested on every étale chart of each scheme base change (Stacks 0GHV, which is
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartULift` under
`AlgebraicGeometry.Space.HasPropertyULift`). Its necessity is witnessed by the identity of
`Y`: a base change of the identity along a scheme-valued point is an isomorphism onto that
point, and both edges of a chart square of such an isomorphism are étale morphisms of the
site, so étale-local cancellation (Stacks 04R3) gives flatness and local finite presentation
of the chart morphism.

Sufficiency of condition (5) needs surjectivity on points to be upgraded to a surjection of
sheaves, which is Stacks 03Y8: a representable flat morphism locally of finite presentation
which is surjective on points is an fppf covering, so sections lift locally. That is
`AlgebraicGeometry.FormalSpace.isLocallySurjective_of_isSurjective_of_flat`, and it is the
reason condition (5) can be stated with the source's hypothesis rather than with a surjection
of sheaves. Its proof tests `Z ⟶ Y` against a scheme-valued point `ξ` of `Y`; the base change
is an algebraic space, so it has a scheme atlas `a` inside the site, and the composite
`W ⟶ Z ×_Y U ⟶ U` is a single morphism of the site which is

* flat and locally of finite presentation, because the atlas and the identity of `U` are
  étale charts and the chart condition of Stacks 0GHV applies to the square they form, and
* surjective, because a point of `U` is the scheme point of a field-valued point of
  `uliftYoneda U`, that point lifts along the base change by surjectivity on points
  (`AlgebraicGeometry.Space.exists_point_of_isPullbackULift`), the lift is a section over the
  spectrum of a field, and the atlas is surjective after that base change — the scheme point
  underlying a field-valued point depending only on its class, which is
  `AlgebraicGeometry.FormalSpace.schemePointULift_eq_of_class_eq`.

That one morphism therefore generates a covering sieve, over which the section lifts.

## References

* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0GHP](https://stacks.math.columbia.edu/tag/0GHP)
* [Stacks Project, Tag 0GHV](https://stacks.math.columbia.edu/tag/0GHV)
* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine coverings of an object of the site -/

/-- A jointly surjective family of flat morphisms locally of finite presentation of the big
fppf site of `S` generates a covering sieve: the family is an fppf covering of the underlying
schemes, and the covering sieves of the slice are those of the ambient site. -/
private theorem ofArrows_mem_topology_of_flat_lfp
    {U : BigFppfOver B S hS} {I : Type u} (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ U)
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i)).base)
    (hflat : ∀ i, Flat ((BigFppfOver.toScheme B S hS).map (v i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (v i))) :
    Sieve.ofArrows V v ∈ BigFppfOver.topology B S hS U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} U.left :=
    ⟨ULift.{u + 1} I, fun i => (V i.down).left, fun i => (v i.down).left⟩
  have heq : E.presieve₀ =
      Presieve.ofArrows (fun i => (V i).left) (fun i => (v i).left) := by
    funext Z g
    exact propext ⟨fun ⟨i⟩ => ⟨i.down⟩, fun ⟨i⟩ => ⟨ULift.up i⟩⟩
  rw [Sieve.ofArrows, ← heq]
  apply B.generate_mem_topology_of_isFppfCovering E
  rw [IsFppfCovering, Precoverage.mem_comap_iff, heq, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨fun t => hcov t, fun i => ⟨hflat i, hlfp i⟩⟩

/-- A jointly surjective family of flat morphisms locally of finite presentation of the big
fppf site of `S` generates a covering sieve: the family is an fppf covering of the underlying
schemes, and the covering sieves of the slice are those of the ambient site. -/
alias ofArrows_mem_topology_of_flat_lfp' := ofArrows_mem_topology_of_flat_lfp

/-- **Every object of the big fppf site of `S` has an affine covering inside the site.** The
family is indexed by the points of the underlying scheme: through each of them passes an arrow
of the trivial covering sieve with affine source, flat and locally of finite presentation, by
`AlgebraicGeometry.BigFppfOver.exists_affine_mem_of_mem_topology`. -/
private theorem exists_affine_covering (U : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ U),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
        Sieve.ofArrows V v ∈ BigFppfOver.topology B S hS U := by
  classical
  choose V v hVaff hVmem hflat hlfp hrange using fun x =>
    BigFppfOver.exists_affine_mem_of_mem_topology B S hS
      ((BigFppfOver.topology B S hS).top_mem U) x
  exact ⟨(BigFppfOver.toScheme B S hS).obj U, V, v, hVaff,
    ofArrows_mem_topology_of_flat_lfp B S hS V v (fun x => ⟨x, hrange x⟩) hflat hlfp⟩

/-- A family of morphisms of the big fppf site of `S` generating a covering sieve induces a
surjection of fppf sheaves from the coproduct of the representable sheaves of its sources onto
the representable sheaf of its target. -/
private theorem isLocallySurjective_sigmaDesc_yonedaSheaf
    {U : BigFppfOver B S hS} {I : Type u} (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ U)
    (hT : Sieve.ofArrows V v ∈ BigFppfOver.topology B S hS U) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Sigma.desc (fun i : ULift.{u + 1} I =>
      (⟨(uliftYoneda.{u + 1}).map (v i.down)⟩ :
        yonedaSheaf B S hS (V i.down) ⟶ yonedaSheaf B S hS U))) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  rw [Sheaf.isLocallySurjective_sigmaDesc_iff]
  intro W s
  refine ⟨Sieve.pullback s.down (Sieve.ofArrows V v),
    (BigFppfOver.topology B S hS).pullback_stable _ hT, ?_⟩
  rintro Z g ⟨Wi, b, c, ⟨i⟩, hfac⟩
  exact ⟨ULift.up i, ULift.up b, congrArg ULift.up hfac⟩

/-! ### Condition (3): the affine scheme-valued points -/

/-- **Stacks 0GHY**, condition (3) implies condition (2): if every base change of
`f : X ⟶ Y` along an affine-scheme-valued point of `Y` is a closed immersion, then so is every
base change along an arbitrary scheme-valued point.

The affine objects of the site covering the point generate a covering sieve, hence a surjection
of sheaves onto the point; over each member the base change of `X ×_Y T ⟶ T` is the base change
of `f` along the composite affine point, and the descent step assembles them. -/
theorem isClosedImmersion_pullback_snd_of_forall_affine {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (h : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (g : yonedaSheaf B S hS T ⟶ Y), IsClosedImmersion B S hS (pullback.snd f g))
    (T : BigFppfOver B S hS) (g : yonedaSheaf B S hS T ⟶ Y) :
    IsClosedImmersion B S hS (pullback.snd f g) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨I, V, v, hVaff, hT⟩ := exists_affine_covering B S hS T
  refine isClosedImmersion_of_locallySurjectiveFamily B S hS (ULift.{u + 1} I)
    (fun i => yonedaSheaf B S hS (V i.down))
    (fun i => (⟨(uliftYoneda.{u + 1}).map (v i.down)⟩ :
      yonedaSheaf B S hS (V i.down) ⟶ yonedaSheaf B S hS T))
    (isLocallySurjective_sigmaDesc_yonedaSheaf B S hS V v hT) ?_
  intro i
  set c : yonedaSheaf B S hS (V i.down) ⟶ yonedaSheaf B S hS T :=
    ⟨(uliftYoneda.{u + 1}).map (v i.down)⟩
  have hpaste : IsPullback (pullback.fst (pullback.snd f g) c ≫ pullback.fst f g)
      (pullback.snd (pullback.snd f g) c) f (c ≫ g) :=
    (IsPullback.of_hasPullback (pullback.snd f g) c).paste_horiz
      (IsPullback.of_hasPullback f g)
  refine isClosedImmersion_of_isPullback B S hS
    (fst := (hpaste.isoIsPullback _ _ (IsPullback.of_hasPullback f (c ≫ g))).hom)
    (g := 𝟙 (yonedaSheaf B S hS (V i.down))) ?_ (h (V i.down) (hVaff i.down) (c ≫ g))
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **Stacks 0GHY**, the equivalence of conditions (1) and (3): a morphism `f : X ⟶ Y` of
formal algebraic spaces over `S` is a closed immersion if and only if for every *affine*
scheme `T` over the big fppf site of `S` and every morphism `T ⟶ Y` the projection
`X ×_Y T ⟶ T` is a closed immersion. As with the definition of a closed immersion, no
hypothesis that `X` and `Y` are formal algebraic spaces is needed. -/
@[stacks 0GHY "conditions (1) and (3)"]
theorem isClosedImmersion_iff_forall_affine {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsClosedImmersion B S hS f ↔
      ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ (g : yonedaSheaf B S hS T ⟶ Y),
          IsClosedImmersion B S hS (pullback.snd f g) :=
  ⟨fun hf T _ g => isClosedImmersion_pullback_snd B S hS f hf T g,
    fun h => isClosedImmersion_of_forall_scheme B S hS f
      (isClosedImmersion_pullback_snd_of_forall_affine B S hS f h)⟩

/-! ### Condition (4): an affine étale covering of the target -/

/-- **Stacks 0GHY**, the equivalence of conditions (1) and (4): a morphism `f : X ⟶ Y` of
formal algebraic spaces over `S` is a closed immersion if and only if there is a covering
`{Y_j ⟶ Y}` as in Definition 0AIM with every base change `X ×_Y Y_j ⟶ Y_j` a closed immersion.

Necessity takes the atlas of `Y` furnished by its being a formal algebraic space; sufficiency
is the descent step, which asks nothing of `f`, so in particular does not assume `f`
representable by algebraic spaces. -/
@[stacks 0GHY "conditions (1) and (4)"]
theorem isClosedImmersion_iff_exists_affineEtaleCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) :
    IsClosedImmersion B S hS f ↔
      ∃ (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (g : ∀ i, Yi i ⟶ Y),
        IsAffineEtaleCover B S hS Yi g ∧
          ∀ i, IsClosedImmersion B S hS (pullback.snd f (g i)) := by
  constructor
  · intro hf
    obtain ⟨I, Yi, g, haffine, hetale, hsurj, hci⟩ :=
      exists_atlas_isClosedImmersion_pullback_snd B S hS f hY hf
    exact ⟨I, Yi, g, ⟨haffine, hetale, hsurj⟩, hci⟩
  · rintro ⟨I, Yi, g, ⟨-, -, hsurj⟩, hci⟩
    exact isClosedImmersion_of_locallySurjectiveFamily B S hS I Yi g hsurj hci

/-! ### Condition (5): a surjective flat cover locally of finite presentation -/

/-- An étale chart of a universe-lifted Yoneda presheaf is a morphism of the site whose
underlying morphism of schemes is étale: the base change along the identity of the target is
the chart itself. -/
private theorem etale_of_relative_uliftYoneda_map {U V : BigFppfOver B S hS} (γ : U ⟶ V)
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
      ((uliftYoneda.{u + 1}).map γ)) :
    Etale ((BigFppfOver.toScheme B S hS).map γ) :=
  h.property (𝟙 ((uliftYoneda.{u + 1}).obj V)) (𝟙 ((uliftYoneda.{u + 1}).obj U)) γ
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- Every morphism between universe-lifted Yoneda presheaves of objects of the site comes from a
morphism of the site. -/
private theorem exists_map_uliftYoneda_eq {U V : BigFppfOver B S hS}
    (φ : (uliftYoneda.{u + 1}).obj U ⟶ (uliftYoneda.{u + 1}).obj V) :
    ∃ γ : U ⟶ V, (uliftYoneda.{u + 1}).map γ = φ :=
  (ULiftYoneda.fullyFaithful (BigFppfOver B S hS)).map_surjective φ

/-- **An isomorphism onto a universe-lifted Yoneda presheaf has, on every étale chart, every
property which is étale local on the source and target and holds for identities.** Both edges
of a chart square of such an isomorphism are étale charts of a representable presheaf, hence
étale morphisms of the site, and the square identifies the chart morphism as a morphism
between them; étale-local cancellation across that square gives the property. -/
private theorem holdsOnEveryEtaleChartULift_of_isIso {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) (hid : ∀ X : Scheme.{u}, P (𝟙 X))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U₀ : BigFppfOver B S hS}
    (e : F ⟶ (uliftYoneda.{u + 1}).obj U₀) [IsIso e] :
    Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P e := by
  have _ : ((MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _
      (F := uliftYoneda.{u + 1})).respectsIso
  intro U V a b h ha hb hsq
  obtain ⟨α, hα⟩ := exists_map_uliftYoneda_eq B S hS (a ≫ e)
  obtain ⟨β, hβ⟩ := exists_map_uliftYoneda_eq B S hS b
  have hfac : h ≫ β = α :=
    (ULiftYoneda.fullyFaithful (BigFppfOver B S hS)).map_injective
      (by rw [Functor.map_comp, hβ, hα, hsq])
  have hEα : Etale ((BigFppfOver.toScheme B S hS).map α) :=
    etale_of_relative_uliftYoneda_map B S hS α
      (by rw [hα]; exact MorphismProperty.RespectsIso.postcomp _ e a ha)
  have hEβ : Etale ((BigFppfOver.toScheme B S hS).map β) :=
    etale_of_relative_uliftYoneda_map B S hS β (by rwa [hβ])
  refine hP.of_commSq_etale ((BigFppfOver.toScheme B S hS).map α)
    ((BigFppfOver.toScheme B S hS).map β) (𝟙 _) _ hEα hEβ (hid _) ?_
  rw [Category.comp_id, ← Functor.map_comp, hfac]

/-- **Stacks 0GHY, condition (5).** There is a morphism `Z ⟶ Y` of formal algebraic spaces
over `S` which is representable by algebraic spaces, surjective, flat and locally of finite
presentation, such that the base change `X ×_Y Z ⟶ Z` of `f` is a closed immersion.

Surjectivity is Stacks 0GHP, surjectivity on points. Flatness and local finite presentation
are the conditions of Stacks 0GHV on a morphism representable by algebraic spaces: they are
tested, after base change along a scheme-valued point of `Y`, on every étale chart of the
resulting algebraic space. -/
abbrev HasFlatClosedImmersionCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ (Z : FppfSheaf B S hS) (_ : IsFormalAlgebraicSpace B S hS Z) (g : Z ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom),
    IsSurjective B S hS g ∧
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) a.hom) g.hom hrep ∧
    Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
          a.hom) g.hom hrep ∧
    IsClosedImmersion B S hS (pullback.snd f g)

/-! ### Surjectivity on points versus local surjectivity -/

private theorem schemePointULift_eq_of_dominates {U : BigFppfOver B S hS}
    {p q : Space.FieldValuedPointULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U)}
    (h : Space.FieldValuedPointULift.Dominates B S hS ((uliftYoneda.{u + 1}).obj U) p q) :
    Space.schemePointULift B S hS U p = Space.schemePointULift B S hS U q := by
  obtain ⟨f, hf⟩ := h
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj
      (q.siteObject B S hS ((uliftYoneda.{u + 1}).obj U))) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of q.carrier)))
  have hval : p.value.down = f ≫ q.value.down := congrArg ULift.down hf.symm
  change (BigFppfOver.toScheme B S hS).map p.value.down (IsLocalRing.closedPoint p.carrier) =
    (BigFppfOver.toScheme B S hS).map q.value.down (IsLocalRing.closedPoint q.carrier)
  calc (BigFppfOver.toScheme B S hS).map p.value.down (IsLocalRing.closedPoint p.carrier)
      = (BigFppfOver.toScheme B S hS).map q.value.down
          ((BigFppfOver.toScheme B S hS).map f (IsLocalRing.closedPoint p.carrier)) := by
        rw [hval, Functor.map_comp]
        rfl
    _ = (BigFppfOver.toScheme B S hS).map q.value.down
          (IsLocalRing.closedPoint q.carrier) := congrArg _ (Subsingleton.elim _ _)

private theorem schemePointULift_eq_of_class_eq {U : BigFppfOver B S hS}
    {p q : Space.FieldValuedPointULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U)}
    (h : p.class B S hS _ = q.class B S hS _) :
    Space.schemePointULift B S hS U p = Space.schemePointULift B S hS U q := by
  obtain ⟨r, hrp, hrq⟩ :=
    (Space.FieldValuedPointULift.class_eq_class_iff B S hS _ p q).mp h
  exact (schemePointULift_eq_of_dominates B S hS hrp).symm.trans
    (schemePointULift_eq_of_dominates B S hS hrq)

/-- **The scheme point underlying a field-valued point of a represented sheaf depends only on
its class.** Two field-valued points of `h_U` with the same point of Stacks 03BU have the same
image in the scheme underlying `U`: a common extension dominates both, and domination does not
move the underlying scheme point, the spectrum of a field having one point. -/
alias schemePointULift_eq_of_class_eq' := schemePointULift_eq_of_class_eq

private theorem relative_etale_id (U : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1})
      (𝟙 ((uliftYoneda.{u + 1}).obj U)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{u + 1}) _, ?_⟩
  intro A C g fst snd hpb
  have : IsIso ((uliftYoneda.{u + 1}).map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := (ULiftYoneda.fullyFaithful _).isIso_of_isIso_map snd
  change Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- Every point of the scheme underlying an object `U` of the site is the scheme point of a
field-valued point of `h_U`. -/
private theorem exists_schemePointULift_eq (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ p : Space.FieldValuedPointULift.{u + 1} B S hS ((uliftYoneda.{u + 1}).obj U),
      Space.schemePointULift B S hS U p = x := by
  obtain ⟨K, instK, hK, ρ, hρ⟩ := Space.exists_fieldSpec_at_point B U.left.2 x
  let r : B.obj hK ⟶ U.left := B.inclusion.preimage (X := B.obj hK) (Y := U.left) ρ
  let m : (Over.mk (r ≫ U.hom) : BigFppfOver B S hS) ⟶ U := Over.homMk r
  have hmρ : (BigFppfOver.toScheme B S hS).map m = ρ :=
    B.inclusion.map_preimage (X := B.obj hK) (Y := U.left) ρ
  refine ⟨⟨K, hK, B.inclusion.map (r ≫ U.hom), ULift.up m⟩, ?_⟩
  change (BigFppfOver.toScheme B S hS).map m (IsLocalRing.closedPoint K) = x
  rw [hmρ]
  exact hρ _

/-- The base change of a morphism surjective on points along a point of a represented sheaf is
surjective on points. -/
private theorem isSurjectiveULift_pullback_fst {F G : FppfSheaf B S hS} {g : F ⟶ G}
    (hsurj : IsSurjective B S hS g) {U : BigFppfOver B S hS}
    (ξ : (uliftYoneda.{u + 1}).obj U ⟶ G.1) :
    Space.IsSurjectiveULift.{u + 1} B S hS (pullback.fst ξ g.hom) := by
  intro z
  obtain ⟨z', hz'⟩ := hsurj (Space.pointsMapULift B S hS ((uliftYoneda.{u + 1}).obj U) ξ z)
  obtain ⟨v, hv, -⟩ := Space.exists_point_of_isPullbackULift B S hS
    (IsPullback.of_hasPullback ξ g.hom) z z' hz'.symm
  exact ⟨v, hv⟩

/-- If `π : P ⟶ h_U` is surjective on points and `a : h_W ⟶ P` is a surjective chart, then a
morphism `k : W ⟶ U` with `h_k = a ≫ π` is surjective on underlying points. -/
private theorem mem_range_of_isSurjectiveULift {U W : BigFppfOver B S hS}
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {π : P ⟶ (uliftYoneda.{u + 1}).obj U}
    (hπ : Space.IsSurjectiveULift.{u + 1} B S hS π) {a : (uliftYoneda.{u + 1}).obj W ⟶ P}
    (hsa : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) a)
    {k : W ⟶ U} (hk : (uliftYoneda.{u + 1}).map k = a ≫ π)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map k).base := by
  obtain ⟨p, hpx⟩ := exists_schemePointULift_eq B S hS U x
  obtain ⟨wc, hwc⟩ := hπ (p.class B S hS _)
  obtain ⟨w, rfl⟩ := Quot.exists_rep wc
  rw [Space.pointsMapULift_class] at hwc
  set R := w.siteObject B S hS _
  set ζ : (uliftYoneda.{u + 1}).obj R ⟶ P := uliftYonedaEquiv.{u + 1}.symm w.value with hζ
  set c : R ⟶ U := (π.app (Opposite.op R) w.value).down
  have hζπ : ζ ≫ π = (uliftYoneda.{u + 1}).map c := by
    rw [hζ, uliftYonedaEquiv_symm_comp]
    exact uliftYonedaEquiv.{u + 1}.symm_apply_eq.mpr (uliftYonedaEquiv_uliftYoneda_map c).symm
  have hcx : Space.schemePointULift B S hS U (Space.FieldValuedPointULift.map B S hS _ π w) = x :=
    (schemePointULift_eq_of_class_eq B S hS hwc).trans hpx
  set n : hsa.rep.pullback ζ ⟶ R := hsa.rep.snd ζ
  set b : hsa.rep.pullback ζ ⟶ W := hsa.rep.fst' ζ with hb
  have hnsurj : Surjective ((BigFppfOver.toScheme B S hS).map n) := hsa.property_snd ζ
  have hwsq : (uliftYoneda.{u + 1}).map b ≫ a = (uliftYoneda.{u + 1}).map n ≫ ζ := by
    rw [hb, hsa.rep.map_fst' ζ]
    exact hsa.rep.w ζ
  have hbk : b ≫ k = n ≫ c := by
    apply (ULiftYoneda.fullyFaithful (BigFppfOver B S hS)).map_injective
    rw [Functor.map_comp, Functor.map_comp, hk, ← Category.assoc, hwsq, Category.assoc, hζπ]
  obtain ⟨t, ht⟩ := hnsurj.surj (IsLocalRing.closedPoint w.carrier)
  refine ⟨(BigFppfOver.toScheme B S hS).map b t, ?_⟩
  show (BigFppfOver.toScheme B S hS).map k ((BigFppfOver.toScheme B S hS).map b t) = x
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hbk, Functor.map_comp]
  change (BigFppfOver.toScheme B S hS).map c ((BigFppfOver.toScheme B S hS).map n t) = x
  rw [ht]
  exact hcx

/-- A surjective morphism of fppf sheaves that is representable by algebraic spaces, flat and
locally of finite presentation is locally surjective for the fppf topology. -/
theorem isLocallySurjective_of_isSurjective_of_flat
    {F G : FppfSheaf B S hS} {g : F ⟶ G}
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hsurj : IsSurjective B S hS g)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) a.hom) g.hom hrep)
    (hlfp : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ a ↦ Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS
        (@AlgebraicGeometry.LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
          a.hom) g.hom hrep) :
    Sheaf.IsLocallySurjective g := by
  classical
  change Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) g.hom
  refine ⟨?_⟩
  intro U y
  set ξ : (uliftYoneda.{u + 1}).obj U ⟶ G.1 := uliftYonedaEquiv.{u + 1}.symm y with hξ
  have hy : uliftYonedaEquiv.{u + 1} ξ = y := by
    rw [hξ]
    exact uliftYonedaEquiv.{u + 1}.apply_symm_apply y
  obtain ⟨W, a, hsa, hea⟩ := (hrep U ξ).exists_atlas
  set π : pullback ξ g.hom ⟶ (uliftYoneda.{u + 1}).obj U := pullback.fst ξ g.hom with hπ
  obtain ⟨k, hk⟩ := exists_map_uliftYoneda_eq B S hS (a ≫ π)
  have hsq : (uliftYoneda.{u + 1}).map k ≫ 𝟙 ((uliftYoneda.{u + 1}).obj U) = a ≫ π := by
    rw [Category.comp_id, hk]
  have hFlat : Flat ((BigFppfOver.toScheme B S hS).map k) :=
    hflat U ξ W U a (𝟙 ((uliftYoneda.{u + 1}).obj U)) k hea (relative_etale_id B S hS U) hsq
  have hLfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map k) :=
    hlfp U ξ W U a (𝟙 ((uliftYoneda.{u + 1}).obj U)) k hea (relative_etale_id B S hS U) hsq
  have hcov : Sieve.ofArrows (fun _ : PUnit.{u + 1} => W) (fun _ => k) ∈
      BigFppfOver.topology B S hS U :=
    ofArrows_mem_topology_of_flat_lfp B S hS _ _
      (fun x => ⟨PUnit.unit, mem_range_of_isSurjectiveULift B S hS
        (isSurjectiveULift_pullback_fst B S hS hsurj ξ) hsa hk x⟩)
      (fun _ => hFlat) (fun _ => hLfp)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hcov
  rintro V q ⟨Z, b, c, ⟨i⟩, rfl⟩
  refine ⟨uliftYonedaEquiv.{u + 1}
    (((uliftYoneda.{u + 1}).map b ≫ a) ≫ pullback.snd ξ g.hom), ?_⟩
  have hfac : (((uliftYoneda.{u + 1}).map b ≫ a) ≫ pullback.snd ξ g.hom) ≫ g.hom =
      (uliftYoneda.{u + 1}).map (b ≫ k) ≫ ξ := by
    rw [Category.assoc, ← pullback.condition, Functor.map_comp, hk]
    simp only [← hπ, Category.assoc]
  calc g.hom.app (Opposite.op V) (uliftYonedaEquiv.{u + 1}
        (((uliftYoneda.{u + 1}).map b ≫ a) ≫ pullback.snd ξ g.hom))
      = uliftYonedaEquiv.{u + 1} ((((uliftYoneda.{u + 1}).map b ≫ a) ≫
          pullback.snd ξ g.hom) ≫ g.hom) := (uliftYonedaEquiv_comp _ _).symm
    _ = uliftYonedaEquiv.{u + 1} ((uliftYoneda.{u + 1}).map (b ≫ k) ≫ ξ) := by rw [hfac]
    _ = G.obj.map (b ≫ k).op y := by
        rw [← hy]
        exact (uliftYonedaEquiv_naturality.{u + 1} ξ (b ≫ k).op).symm

/-- **Stacks 0GHY**, condition (1) implies condition (5): a closed immersion `f : X ⟶ Y` of
formal algebraic spaces over `S` admits a morphism `Z ⟶ Y` of formal algebraic spaces,
representable by algebraic spaces, surjective, flat and locally of finite presentation, along
which the base change of `f` is a closed immersion.

The identity of `Y` serves: it is representable by algebraic spaces and étale, hence surjective
on points, and each of its base changes along a scheme-valued point of `Y` is an isomorphism
onto that point, so flatness and local finite presentation hold on every étale chart of it.
The base change of `f` along the identity is `f` itself up to the canonical isomorphism. -/
@[stacks 0GHY "condition (1) implies condition (5)"]
theorem hasFlatClosedImmersionCover_of_isClosedImmersion {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) (hf : IsClosedImmersion B S hS f) :
    HasFlatClosedImmersionCover B S hS f := by
  have hid : IsIso ((𝟙 Y : Y ⟶ Y).hom) := inferInstanceAs (IsIso (𝟙 Y.obj))
  have hfst : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.1),
      IsIso (pullback.fst ξ ((𝟙 Y : Y ⟶ Y).hom)) :=
    fun U ξ ↦ (IsPullback.of_hasPullback ξ ((𝟙 Y : Y ⟶ Y).hom)).isIso_fst_of_isIso
  refine ⟨Y, hY, 𝟙 Y, (isRepresentableEtale_id B S hS Y).1, fun y ↦ ⟨y, by simp⟩,
    fun U ξ ↦ ?_, fun U ξ ↦ ?_, ?_⟩
  · have _ := hfst U ξ
    exact holdsOnEveryEtaleChartULift_of_isIso B S hS
      Flat.isEtaleLocalOnSourceAndTarget (fun _ ↦ inferInstance)
      (pullback.fst ξ ((𝟙 Y : Y ⟶ Y).hom))
  · have _ := hfst U ξ
    exact holdsOnEveryEtaleChartULift_of_isIso B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget (fun _ ↦ inferInstance)
      (pullback.fst ξ ((𝟙 Y : Y ⟶ Y).hom))
  · exact isClosedImmersion_of_isPullback B S hS (IsPullback.of_hasPullback f (𝟙 Y)) hf

/-- **Stacks 0GHY**, condition (5) implies condition (1): if there is a morphism `Z ⟶ Y` of
formal algebraic spaces representable by algebraic spaces, surjective, flat and locally of
finite presentation along which the base change of `f` is a closed immersion, then `f` is a
closed immersion.

Surjectivity here is the source's, surjectivity on points; it is upgraded to a surjection of
sheaves by
`AlgebraicGeometry.FormalSpace.isLocallySurjective_of_isSurjective_of_flat`, and the descent
step then applies to the one-member family `{Z ⟶ Y}`. -/
@[stacks 0GHY "condition (5) implies condition (1)"]
theorem isClosedImmersion_of_hasFlatClosedImmersionCover {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : HasFlatClosedImmersionCover B S hS f) : IsClosedImmersion B S hS f := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨Z, -, c, hrep, hsurj, hflat, hlfp, hci⟩ := h
  have _ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) c.hom :=
    isLocallySurjective_of_isSurjective_of_flat B S hS hrep hsurj hflat hlfp
  refine isClosedImmersion_of_locallySurjectiveFamily B S hS PUnit.{u + 2}
    (fun _ ↦ Z) (fun _ ↦ c) ?_ (fun _ ↦ hci)
  rw [Sheaf.isLocallySurjective_sigmaDesc_iff]
  intro V s
  refine ⟨Presheaf.imageSieve c.hom s,
    Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) c.hom s, ?_⟩
  rintro V' q ⟨t, ht⟩
  exact ⟨PUnit.unit, t, ht⟩

/-- **Stacks 0GHY**, the equivalence of conditions (1) and (5): a morphism `f : X ⟶ Y` of
formal algebraic spaces over `S` is a closed immersion if and only if there is a morphism
`Z ⟶ Y` of formal algebraic spaces, representable by algebraic spaces, surjective, flat and
locally of finite presentation, with `X ×_Y Z ⟶ Z` a closed immersion. -/
@[stacks 0GHY "conditions (1) and (5)"]
theorem isClosedImmersion_iff_hasFlatClosedImmersionCover {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y) :
    IsClosedImmersion B S hS f ↔ HasFlatClosedImmersionCover B S hS f :=
  ⟨hasFlatClosedImmersionCover_of_isClosedImmersion B S hS f hY,
    isClosedImmersion_of_hasFlatClosedImmersionCover B S hS⟩

end AlgebraicGeometry.FormalSpace

end
