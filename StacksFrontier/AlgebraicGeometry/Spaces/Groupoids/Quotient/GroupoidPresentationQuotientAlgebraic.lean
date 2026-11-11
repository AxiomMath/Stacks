module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.RestrictionCoverings
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuotientStackAlgebraic
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare

/-!
# Algebraicity of a quotient stack from a flat restriction

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme
`S` of a big fppf site. If the groupoid admits a restriction `(U', R', s', t', c')` along a
morphism `g : U' ⟶ U` whose saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of fppf
sheaves and whose source and target are flat and locally of finite presentation, then the
quotient stack `[U/R]` is an algebraic stack.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_restriction`: the implication of
  Stacks 06PJ towards algebraicity, for a groupoid exhibited as the restriction by a morphism to
  the original groupoid.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_restrictionAlong`: the same for the
  canonical restriction of **Stacks 044B** along `g`.

Stacks 06PJ itself, both implications, is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_iff_restrictionAlong` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraicIffRestriction`.

## Implementation notes

Being the restriction of `(U, R, s, t, c)` along the morphism `g = f_U` that a morphism of
groupoids `f : (U', R', s', t', c') ⟶ (U, R, s, t, c)` induces on objects is the cartesian
condition `hrestriction` of the first result: the square formed by the arrow map of `f` and the
two source–target maps of the two groupoids is a fibre product. This is the condition of **Stacks
046S**, where it is shown to be equivalent to full faithfulness of the induced morphism of
quotient stacks, and it is condition (1) of **Stacks 046T**.

Given that condition, **Stacks 046T** turns surjectivity of the saturation map into an
equivalence `[U'/R'] ⟶ [U/R]` of categories over the site. That equivalence is produced as a
`CategoryTheory.Functor.IsEquivalenceOver`, which does not itself record that its forward functor
lies over the site; the strict commutation is `(quotientStackMap f).w`, and the two together give
a `CategoryTheory.BasedCategory.Equivalence` through
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver` and
`CategoryTheory.StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence`. Algebraicity then
transports along it by **Stacks 03YQ**, in the universe-polymorphic form
`AlgebraicGeometry.Stack.isAlgebraicStack_iff_of_equivalence`; the universe-pinned form does not
apply, the total category of a quotient stack not living in `BasedCategory.{u, u + 1}`.

The second result instantiates the first at the canonical restriction
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict` of **Stacks 044B**, whose specification
supplies the cartesian condition only in the equivalent form of pointwise full faithfulness of
its morphism to `(U, R, s, t, c)`. The passage from that to the cartesian square is the content
of Stacks 046S and is a *private* declaration of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FullFaithfulness`, so it is restated
here as `isPullback_of_evaluation_fullyFaithful`. The specification identifies the object and
arrow spaces of the restriction and its structure maps only up to the transports attached to
those identifications, so the flatness and finite-presentation hypotheses, stated for
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionSource` and `restrictionTarget`, are
moved onto the restricted groupoid's own source and target by
`CategoryTheory.MorphismProperty.RespectsIso`, and the object map of the morphism is `g`
precomposed with such a transport, so the saturation map is the one of `g` precomposed with the
induced isomorphism of fibre products; local surjectivity is insensitive to both.

The algebraicity of `[U'/R']` is **Stacks 06FI** — the quotient stack of a groupoid in algebraic
spaces whose source and target are flat and locally of finite presentation is an algebraic
stack — which is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_flat`.

The converse implication of Stacks 06PJ, producing the restriction from algebraicity of `[U/R]`,
is `AlgebraicGeometry.Stack.exists_restrictionAlong_of_isAlgebraicStack` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraicIffRestriction`,
and **Stacks 06PL** is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_trivialAction_iff`.

## References

* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w u₁ v₁

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- Two sections of a binary product of presheaves of types agree as soon as their two
projections do. -/
private theorem prod_app_ext
    {D : Type u₁} [Category.{v₁} D] {P Q : Dᵒᵖ ⥤ Type v₁} {T : Dᵒᵖ}
    {a b : (P ⨯ Q).obj T}
    (h₁ : (prod.fst : P ⨯ Q ⟶ P).app T a = (prod.fst : P ⨯ Q ⟶ P).app T b)
    (h₂ : (prod.snd : P ⨯ Q ⟶ Q).app T a = (prod.snd : P ⨯ Q ⟶ Q).app T b) : a = b := by
  apply (yonedaEquiv (X := unop T) (F := P ⨯ Q)).symm.injective
  apply prod.hom_ext
  · apply (yonedaEquiv (X := unop T) (F := P)).injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simpa only [Equiv.apply_symm_apply] using h₁
  · apply (yonedaEquiv (X := unop T) (F := Q)).injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp]
    simpa only [Equiv.apply_symm_apply] using h₂

/-- A morphism of groupoids in presheaves whose every evaluation is fully faithful has
cartesian arrow square over the self-product of its object map.

This is the condition of **Stacks 046S**; it is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FullFaithfulness` as a private
declaration, so it is restated here rather than imported. -/
private theorem isPullback_of_evaluation_fullyFaithful
    {D : Type u₁} [Category.{v₁} D]
    {G H : Deformation.GroupoidInFunctors.{u₁, v₁, v₁} Dᵒᵖ}
    (f : Deformation.GroupoidInFunctors.Hom G H)
    (hf : ∀ T, (f.evaluation T).FullyFaithful) :
    IsPullback f.mapArrows (prod.lift G.source G.target)
      (prod.lift H.source H.target) (prod.map f.mapObjects f.mapObjects) := by
  have hw : f.mapArrows ≫ prod.lift H.source H.target =
      prod.lift G.source G.target ≫ prod.map f.mapObjects f.mapObjects := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc]
      ext T a
      exact f.map_source T a
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
      ext T a
      exact f.map_target T a
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun α => α.app T) hw, ?_, ?_⟩
  · intro a b hab
    have hs : G.source.app T a = G.source.app T b := by
      simpa only [← NatTrans.comp_app_apply, prod.lift_fst] using
        congrArg ((prod.fst : G.objects ⨯ G.objects ⟶ G.objects).app T) hab.2
    have ht : G.target.app T a = G.target.app T b := by
      simpa only [← NatTrans.comp_app_apply, prod.lift_snd] using
        congrArg ((prod.snd : G.objects ⨯ G.objects ⟶ G.objects).app T) hab.2
    let x := G.source.app T a
    let y := G.target.app T a
    let m := (G.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
    let n := (G.evaluationArrowEquiv T x y).symm ⟨b, hs.symm, ht.symm⟩
    have hmn : (f.evaluation T).map m = (f.evaluation T).map n := by
      apply (H.evaluationArrowEquiv T _ _).injective
      apply Subtype.ext
      rw [f.evaluation_map_arrow T m, f.evaluation_map_arrow T n]
      simpa only [m, n, Equiv.apply_symm_apply] using hab.1
    have := congrArg (fun k => (G.evaluationArrowEquiv T x y k).1) ((hf T).map_injective hmn)
    simpa [m, n] using this
  · intro a p hap
    let x := (prod.fst : G.objects ⨯ G.objects ⟶ G.objects).app T p
    let y := (prod.snd : G.objects ⨯ G.objects ⟶ G.objects).app T p
    have hs : H.source.app T a = f.mapObjects.app T x := by
      have he := congrArg ((prod.fst : H.objects ⨯ H.objects ⟶ H.objects).app T) hap
      change ((prod.lift H.source H.target ≫ prod.fst).app T) a =
        ((prod.map f.mapObjects f.mapObjects ≫ prod.fst).app T) p at he
      rw [prod.lift_fst, prod.map_fst] at he
      exact he
    have ht : H.target.app T a = f.mapObjects.app T y := by
      have he := congrArg ((prod.snd : H.objects ⨯ H.objects ⟶ H.objects).app T) hap
      change ((prod.lift H.source H.target ≫ prod.snd).app T) a =
        ((prod.map f.mapObjects f.mapObjects ≫ prod.snd).app T) p at he
      rw [prod.lift_snd, prod.map_snd] at he
      exact he
    let m := (H.evaluationArrowEquiv T ((f.evaluation T).obj x)
      ((f.evaluation T).obj y)).symm ⟨a, hs, ht⟩
    let n := (hf T).preimage m
    let b := (G.evaluationArrowEquiv T x y n).1
    refine ⟨b, ?_, ?_⟩
    · have he := congrArg (fun k => (H.evaluationArrowEquiv T _ _ k).1)
        ((hf T).map_preimage m)
      rw [f.evaluation_map_arrow] at he
      simpa only [b, n, m, Equiv.apply_symm_apply] using he
    · apply prod_app_ext
      · simpa only [← NatTrans.comp_app_apply, prod.lift_fst] using
          (G.evaluationArrowEquiv T x y n).2.1
      · simpa only [← NatTrans.comp_app_apply, prod.lift_snd] using
          (G.evaluationArrowEquiv T x y n).2.2

/-- Local surjectivity of a composite out of a fibre product is unaffected by precomposing the
first leg of the cospan with an isomorphism: the two fibre products are canonically isomorphic
over the second factor. -/
private theorem isLocallySurjective_pullbackSnd_comp_of_isIso
    {X X' Y Z W : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : X ⟶ X') [IsIso a] (k : X' ⟶ Y) (t : Z ⟶ Y) (m : Z ⟶ W)
    (h : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.snd k t ≫ m)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.snd (a ≫ k) t ≫ m) := by
  have hc : pullback.fst (a ≫ k) t ≫ a ≫ k = pullback.snd (a ≫ k) t ≫ t :=
    pullback.condition
  have hc' : pullback.fst k t ≫ inv a ≫ a ≫ k = pullback.snd k t ≫ t := by
    rw [IsIso.inv_hom_id_assoc]
    exact pullback.condition
  set φ : pullback (a ≫ k) t ⟶ pullback k t :=
    pullback.lift (pullback.fst (a ≫ k) t ≫ a) (pullback.snd (a ≫ k) t) (by
      rw [Category.assoc]; exact hc) with hφ
  set ψ : pullback k t ⟶ pullback (a ≫ k) t :=
    pullback.lift (pullback.fst k t ≫ inv a) (pullback.snd k t) (by
      rw [Category.assoc]; exact hc') with hψ
  have hf1 : φ ≫ pullback.fst k t = pullback.fst (a ≫ k) t ≫ a := by
    rw [hφ]; exact pullback.lift_fst _ _ _
  have hs1 : φ ≫ pullback.snd k t = pullback.snd (a ≫ k) t := by
    rw [hφ]; exact pullback.lift_snd _ _ _
  have hf2 : ψ ≫ pullback.fst (a ≫ k) t = pullback.fst k t ≫ inv a := by
    rw [hψ]; exact pullback.lift_fst _ _ _
  have hs2 : ψ ≫ pullback.snd (a ≫ k) t = pullback.snd k t := by
    rw [hψ]; exact pullback.lift_snd _ _ _
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hf2, ← Category.assoc, hf1, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hs2, hs1, Category.id_comp]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hs1, hs2, Category.id_comp]
  have : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have := h
  have hfac : φ ≫ (pullback.snd k t ≫ m) = pullback.snd (a ≫ k) t ≫ m := by
    rw [← Category.assoc, hs1]
  rw [← hfac]
  infer_instance

/-- The source of the canonical restriction of **Stacks 044B** has any property of morphisms of
algebraic spaces respecting isomorphisms that the chosen lift of the source on the arrow space
of the restriction has. -/
private theorem prop_restrict_source
    {G : GroupoidInAlgebraicSpaces C S hS B} {U' : AlgebraicSpaces C S hS}
    (g : U' ⟶ G.objects) (Q : MorphismProperty (AlgebraicSpaces C S hS))
    [Q.IsStableUnderBaseChange]
    (h : Q (GroupoidInAlgebraicSpaces.restrictionSource G g)) :
    Q (GroupoidInAlgebraicSpaces.restrict G g).groupoid.source := by
  rw [(GroupoidInAlgebraicSpaces.restrict G g).source_eq]
  exact MorphismProperty.RespectsIso.precomp Q _ _
    (MorphismProperty.RespectsIso.postcomp Q _ _ h)

/-- The target of the canonical restriction of **Stacks 044B** has any property of morphisms of
algebraic spaces respecting isomorphisms that the chosen lift of the target on the arrow space
of the restriction has. -/
private theorem prop_restrict_target
    {G : GroupoidInAlgebraicSpaces C S hS B} {U' : AlgebraicSpaces C S hS}
    (g : U' ⟶ G.objects) (Q : MorphismProperty (AlgebraicSpaces C S hS))
    [Q.IsStableUnderBaseChange]
    (h : Q (GroupoidInAlgebraicSpaces.restrictionTarget G g)) :
    Q (GroupoidInAlgebraicSpaces.restrict G g).groupoid.target := by
  rw [(GroupoidInAlgebraicSpaces.restrict G g).target_eq]
  exact MorphismProperty.RespectsIso.precomp Q _ _
    (MorphismProperty.RespectsIso.postcomp Q _ _ h)

/-- **Algebraicity from a flat restriction.** Let `(U, R, s, t, c)` be a groupoid in algebraic
spaces over `B` and let `f : (U', R', s', t', c') ⟶ (U, R, s, t, c)` exhibit its source as the
restriction of its target along `g = f_U : U' ⟶ U`. If the saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U`
is a surjection of fppf sheaves and `s', t'` are flat and locally of finite presentation, then the
quotient stack `[U/R]` is an algebraic stack. -/
theorem isAlgebraicStack_quotientStack_of_restriction
    (G G' : GroupoidInAlgebraicSpaces C S hS B)
    (f : GroupoidInAlgebraicSpaces.Hom G' G)
    (hrestriction : IsPullback f.toGroupoidHom.mapArrows
      (prod.lift G'.toGroupoidInFunctors.source G'.toGroupoidInFunctors.target)
      (prod.lift G.toGroupoidInFunctors.source G.toGroupoidInFunctors.target)
      (prod.map f.toGroupoidHom.mapObjects f.toGroupoidHom.mapObjects))
    (hsaturation : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd
        (ObjectProperty.homMk f.toGroupoidHom.mapObjects : G'.objects ⟶ G.objects)
        G.target ≫ G.source).hom))
    (hsource : Space.IsFlat C S hS G'.source.hom)
    (htarget : Space.IsFlat C S hS G'.target.hom)
    (hsourceFP : Space.IsLocallyOfFinitePresentation C S hS G'.source.hom)
    (htargetFP : Space.IsLocallyOfFinitePresentation C S hS G'.target.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) := by
  obtain ⟨E⟩ := (quotientStackMap_isEquivalenceOver_iff f).mpr ⟨hrestriction, hsaturation⟩
  have e : BasedCategory.Equivalence (quotientStack G') (quotientStack G) :=
    (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (quotientStackMap f).w E).toBasedEquivalence
  exact (isAlgebraicStack_iff_of_equivalence C S hS e).mp
    (isAlgebraicStack_quotientStack_of_flat G' hsource htarget hsourceFP htargetFP)

/-- **Algebraicity from the flat restriction along `g`.** Let `(U, R, s, t, c)` be a groupoid in
algebraic spaces over `B` and let `g : U' ⟶ U` be a morphism of algebraic spaces such that the
saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of fppf sheaves and the source and target
of the restriction `(U', R', s', t', c')` of `(U, R, s, t, c)` along `g` are flat and locally of
finite presentation. Then the quotient stack `[U/R]` is an algebraic stack. -/
theorem isAlgebraicStack_quotientStack_of_restrictionAlong
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hsaturation : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom))
    (hsource : Space.IsFlat C S hS
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom)
    (htarget : Space.IsFlat C S hS
      (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom)
    (hsourceFP : Space.IsLocallyOfFinitePresentation C S hS
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom)
    (htargetFP : Space.IsLocallyOfFinitePresentation C S hS
      (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) := by
  have hflat := Space.isFlat_isStableUnderBaseChange C S hS
  have hfp := Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS
  have hmo : (ObjectProperty.homMk
      (GroupoidInAlgebraicSpaces.restrict G g).hom.toGroupoidHom.mapObjects :
      (GroupoidInAlgebraicSpaces.restrict G g).groupoid.objects ⟶ G.objects) =
      eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq ≫ g :=
    ObjectProperty.hom_ext _ (GroupoidInAlgebraicSpaces.restrict G g).mapObjects_eq
  refine isAlgebraicStack_quotientStack_of_restriction G
    (GroupoidInAlgebraicSpaces.restrict G g).groupoid
    (GroupoidInAlgebraicSpaces.restrict G g).hom
    (isPullback_of_evaluation_fullyFaithful _ (fun T =>
      ((GroupoidInAlgebraicSpaces.restrict G g).evaluation_fullyFaithful T).some)) ?_
    (prop_restrict_source g
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) hsource)
    (prop_restrict_target g
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) htarget)
    (prop_restrict_source g
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) hsourceFP)
    (prop_restrict_target g
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) htargetFP)
  rw [hmo]
  exact isLocallySurjective_pullbackSnd_comp_of_isIso
    (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq).hom g.hom G.target.hom
    G.source.hom hsaturation

end AlgebraicGeometry.Stack

end
