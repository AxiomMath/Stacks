module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianValuativeCriterionUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocalQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniqueness
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
import all StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal

/-!
# The refined valuative criteria of properness and separation for algebraic stacks

Stacks 0CQM asserts properness of a separated 1-morphism of finite type `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over a locally Noetherian `𝒴` from the existence part of the valuative criterion, tested
only on valuative squares over discrete valuation rings whose generic point factors through a
1-morphism of finite type `h : 𝒰 ⟶ 𝒳` with dense image. Stacks 0E95 is the analogous criterion of
separation.

This file defines these hypotheses and reduces Stacks 0CQM to an affine base and an affine
source: the hypothesis survives base change along a 1-morphism of the target (Stacks 0CLE) and,
along a flat 1-morphism locally of finite presentation, so does the density of the image of `h`
(Stacks 04XH and Stacks 06R7).

## Main definitions

* `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteExistenceAlong`: every valuative square for
  `f` over a discrete valuation ring whose generic point is `u ≫ h` admits a dotted arrow after an
  extension of the fraction field and passage to a dominating valuation ring.
* `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteUniquenessAlong`: for every valuative
  diagram for `f` over a discrete valuation ring whose generic point is `u ≫ h`, the category of
  dotted arrows is empty or a setoid with exactly one isomorphism class.
* `CategoryTheory.DottedArrow.congrTop`: transport of a dotted arrow along an isomorphism of the
  top edge of its square.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.dense_range_pointsMap_fst_of_isFlat`: the base change of
  a 1-morphism with dense image along a flat 1-morphism locally of finite presentation has dense
  image.
* `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteExistenceAlong.of_iso`: the hypothesis holds
  for every square whose generic point is only isomorphic to one through `h`.
* `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteExistenceAlong.baseChange`: the hypothesis
  passes to a base change of `f` and the corresponding base change of `h`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyClosed_of_discreteExistenceAlong_of_affine`
  and `Stack.AlgebraicStacks.universallyClosed_of_discreteExistenceAlong_of_affineSource`: the
  reductions of Stacks 0CQM to an affine locally Noetherian base and then to a source which is
  the algebraic stack of an affine scheme;
  `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_of_discreteExistenceAlong_of_affineCore`
  assembles them: Stacks 0CQM follows from its affine case.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 0CLE](https://stacks.math.columbia.edu/tag/0CLE)
* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0E95](https://stacks.math.columbia.edu/tag/0E95)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe u w

namespace CategoryTheory.DottedArrow

variable {B : Type*} [Bicategory.{w, u} B] {S T X Y : B} {x x' : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y}
  {y : T ⟶ Y} {γ : (j ≫ y) ⟶ (x ≫ f)}

/-- A dotted arrow transported along an isomorphism `θ : x ≅ x'` of the top edge of its square:
the diagonal and the lower triangle are unchanged, the upper triangle is composed with `θ`, and
the square's filler is composed with `θ` whiskered by the right edge. -/
def congrTop (d : DottedArrow x j f y γ) (θ : x ≅ x') :
    DottedArrow x' j f y (γ ≫ (θ.hom ▷ f)) where
  a := d.a
  α := d.α ≫ θ.hom
  β := d.β
  compat := by
    conv_lhs => rw [d.compat]
    simp

end CategoryTheory.DottedArrow

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

/-- **The base change of a 1-morphism with dense image along a flat 1-morphism locally of finite
presentation has dense image.** If `g : 𝒳' ⟶ 𝒳` is flat and locally of finite presentation and
the image of `|h|` is dense in `|𝒳|`, then the image of the first projection of `𝒳' ×_𝒳 𝒰` is
dense in `|𝒳'|`. -/
theorem dense_range_pointsMap_fst_of_isFlat {𝒰 𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒳' ⟶ 𝒳) (h : 𝒰 ⟶ 𝒳) (hflat : IsFlat B S hS g)
    (hlfp : IsLocallyOfFinitePresentation B S hS g)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h))) :
    @Dense _ (pointTopology B S hS 𝒳'.val)
      (Set.range
        (pointsMap B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g h).fst)) := by
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS 𝒳'.val
  set P := Stack.twoFibreProductSquareAlgebraicStacks B S hS g h
  have hsub : pointsMap B S hS g ⁻¹' Set.range (pointsMap B S hS h) ⊆
      Set.range (pointsMap B S hS P.fst) := by
    rintro x' ⟨v, hv⟩
    obtain ⟨p, hp, -⟩ := exists_point_of_isTwoFibreProduct B S hS P
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g h) x' v hv.symm
    exact ⟨p, hp⟩
  exact (hdense.preimage (isOpenMap_pointsMap B S hS g hflat hlfp)).mono hsub

end AlgebraicStacks

variable {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

namespace ValuativeCriterion

/-- **The hypothesis of Stacks 0CQM.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`
satisfies the discrete existence part of the valuative criterion *along* `h : 𝒰 ⟶ 𝒳` when every
valuative square for `f` whose valuation ring is a discrete valuation ring and whose generic point
is `u ≫ h` for some `u` admits a dotted arrow after an extension of the fraction field and passage
to a dominating valuation ring. -/
abbrev DiscreteExistenceAlong (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ q : ValuativeSquare B S hS f, IsDiscreteValuationRing q.R →
    ∀ u : schemeFibredCategory B S hS (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ 𝒰.1,
      q.x = u ≫ h.hom →
        ∃ e : q.DominatingExtension,
          Nonempty (DottedArrow (e.k ≫ q.x) e.j f.hom (e.a ≫ q.y) e.inducedGamma)

/-- **The hypothesis of Stacks 0CQM does not depend on the presentation of the generic point.**
If `f` satisfies the discrete existence part of the valuative criterion along `h`, then every
valuative square for `f` over a discrete valuation ring whose generic point is isomorphic to
`u ≫ h` admits a dotted arrow after a dominating extension. -/
theorem DiscreteExistenceAlong.of_iso {h : 𝒰 ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hf : DiscreteExistenceAlong B S hS h f) (q : ValuativeSquare B S hS f)
    (hq : IsDiscreteValuationRing q.R)
    (u : schemeFibredCategory B S hS (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ 𝒰.1)
    (θ : q.x ≅ u ≫ h.hom) :
    ∃ e : q.DominatingExtension,
      Nonempty (DottedArrow (e.k ≫ q.x) e.j f.hom (e.a ≫ q.y) e.inducedGamma) := by
  obtain ⟨e, ⟨d⟩⟩ := hf { q with x := u ≫ h.hom, γ := q.γ ≫ (θ.hom ▷ f.hom) } hq u rfl
  let E : q.DominatingExtension :=
    { e with }
  have hγ : e.inducedGamma ≫ ((whiskerLeftIso E.k θ).symm.hom ▷ f.hom) = E.inducedGamma := by
    simp only [ValuativeSquare.DominatingExtension.inducedGamma, E, Iso.symm_hom,
      whiskerLeftIso_inv, Category.assoc, whisker_assoc, Iso.inv_hom_id_assoc,
      ← whiskerLeft_comp_assoc, hom_inv_whiskerRight, Category.comp_id]
  exact ⟨E, ⟨hγ ▸ d.congrTop (whiskerLeftIso E.k θ).symm⟩⟩

/-- **The hypothesis of Stacks 0CQM is stable under base change.** Let `P` be a 2-fibre product
of `f` along `g : 𝒴' ⟶ 𝒴` and let `Q` be a 2-commutative square over `P.snd` and `h`. If `f`
satisfies the discrete existence part of the valuative criterion along `h`, then the base change
`P.fst` satisfies it along `Q.fst`. -/
theorem DiscreteExistenceAlong.baseChange {𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (h : 𝒰 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (Q : Bicategory.TwoCommSq P.snd h)
    (hf : DiscreteExistenceAlong B S hS h f) :
    DiscreteExistenceAlong B S hS (𝒰 := Q.pt) Q.fst P.fst := by
  classical
  let φ := baseChangeFiller B S hS f g P
  let ψ := baseChangeFiller B S hS h P.snd Q
  obtain ⟨hcart⟩ := nonempty_isTwoCartesian_baseChange B S hS f g P hP
  intro q hqdvr u hu
  obtain ⟨e, ⟨d⟩⟩ := DiscreteExistenceAlong.of_iso B S hS hf
    { q with
      x := q.x ≫ P.snd.hom
      y := q.y ≫ g.hom
      γ := (α_ q.j q.y g.hom).inv ≫ (q.γ ▷ g.hom) ≫
        (α_ q.x P.fst.hom g.hom).hom ≫ (q.x ◁ φ.hom) ≫
        (α_ q.x P.snd.hom f.hom).inv } hqdvr (u ≫ Q.snd.hom)
    (eqToIso (by simp only [hu]) ≪≫ α_ u Q.fst.hom P.snd.hom ≪≫ whiskerLeftIso u ψ ≪≫
      (α_ u Q.snd.hom h.hom).symm)
  let E : q.DominatingExtension :=
    { e with }
  have hγ : IsIso E.inducedGamma :=
    (CatFiberedInGroupoids.homGroupoid _ _).all_isIso E.inducedGamma
  obtain ⟨E'⟩ := CategoryTheory.DottedArrowBaseChange.dottedArrows_baseChange_equivalence
    E.j (E.k ≫ q.x) P.snd.hom P.fst.hom f.hom (E.a ≫ q.y) g.hom φ
    (asIso E.inducedGamma) hcart
  have hγeq : ((α_ E.j (E.a ≫ q.y) g.hom).symm ≪≫
      Bicategory.whiskerRightIso (asIso E.inducedGamma) g.hom ≪≫
      (α_ (E.k ≫ q.x) P.fst.hom g.hom) ≪≫
      Bicategory.whiskerLeftIso (E.k ≫ q.x) φ ≪≫
      (α_ (E.k ≫ q.x) P.snd.hom f.hom).symm).hom = e.inducedGamma := by
    dsimp only [ValuativeSquare.DominatingExtension.inducedGamma]
    simp only [Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerRightIso_hom,
      Bicategory.whiskerLeftIso_hom]
    exact CatFiberedInGroupoids.pastedGamma e.j e.a e.k q.j q.y q.x P.fst.hom P.snd.hom
      g.hom f.hom e.commute q.γ φ.hom
  exact ⟨E, ⟨E'.inverse.obj
    { a := d.a, α := d.α, β := d.β, compat := hγeq.trans d.compat }⟩⟩

/-- **The hypothesis of Stacks 0E95.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`
satisfies the discrete uniqueness part of the valuative criterion *along* `h : 𝒰 ⟶ 𝒳` when, for
every valuative diagram for `f` whose valuation ring is a discrete valuation ring and whose generic
point is `u ≫ h` for some `u`, the category of dotted arrows is either empty or a setoid with
exactly one isomorphism class.

This is `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteUniqueness` of Stacks 0E80 restricted
to the diagrams whose generic point factors through `h`. -/
abbrev DiscreteUniquenessAlong (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f, @IsDiscreteValuationRing D.R D.ring D.domain →
    ∀ u : schemeFibredCategory B S hS D.generic ⟶ 𝒰.1, D.x = u ≫ h.hom →
      IsSetoidCategory (CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) ∧
        ∀ a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ, Nonempty (a ≅ b)

end ValuativeCriterion

namespace AlgebraicStacks

/-- **An open substack in which the points of a 1-morphism into it are dense.** Let `W` be an open
substack of `𝒞` and `k : 𝒰 ⟶ W` a 1-morphism. If every point of `W`, read in `|𝒞|`, lies in the
closure of the image of `|𝒰|`, then the image of `|k|` is dense in `|W|`. -/
theorem dense_range_pointsMap_of_pointSet_subset_closure {𝒞 𝒰 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒞) (k : 𝒰 ⟶ W.toAlgebraicStack)
    (hW : W.pointSet ⊆ @closure _ (pointTopology B S hS 𝒞.val)
      (Set.range (pointsMap B S hS (k ≫ W.inclusion)))) :
    @Dense _ (pointTopology B S hS W.toAlgebraicStack.val) (Set.range (pointsMap B S hS k)) := by
  let _ := pointTopology B S hS 𝒞.val
  let _ := pointTopology B S hS W.toAlgebraicStack.val
  refine dense_iff_inter_open.2 fun O hO ⟨w, hw⟩ => ?_
  obtain ⟨_, ⟨o, ho, rfl⟩, ⟨v, hv⟩⟩ := mem_closure_iff.1 (hW ⟨w, rfl⟩) _
    (isOpenMap_pointsMap_of_isOpenImmersion B S hS W.inclusion W.isOpenImmersion O hO)
    ⟨w, hw, rfl⟩
  rw [pointsMap_comp] at hv
  exact ⟨o, ho, v, pointsMap_injective_of_fullyFaithful B S hS W.inclusion hv⟩

end AlgebraicStacks

namespace AlgebraicStacks

/-- **Properness of an open substack over the base from the refined valuative criterion.**

Let `p : 𝒞 ⟶ 𝒴` be a 1-morphism to a locally Noetherian algebraic stack, let `W` and `V` be open
substacks of `𝒞` with a factorization `k : V ⟶ W` of the inclusion of `V`, and assume that
`W ⟶ 𝒴` is separated and of finite type, that `k` is of finite type, that every point of `W` lies
in the closure of the points of `V`, and that `W ⟶ 𝒴` satisfies the discrete existence part of the
valuative criterion along `k`. Then `W ⟶ 𝒴` is proper. `h0CQM` is the statement of Stacks 0CQM,
exactly as `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteExistenceAlong` phrases its
hypothesis on dotted arrows. -/
theorem isProper_inclusion_comp_of_refinedValuativeCriterion
    (h0CQM : ∀ (𝒰' 𝒳' 𝒴' : AlgebraicStacks.{u, w} B S hS) (h' : 𝒰' ⟶ 𝒳') (f' : 𝒳' ⟶ 𝒴'),
      HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴' →
      IsFiniteType B S hS f' → IsFiniteType B S hS h' → IsSeparated B S hS f' →
      @Dense _ (pointTopology B S hS 𝒳'.val) (Set.range (pointsMap B S hS h')) →
      ValuativeCriterion.DiscreteExistenceAlong B S hS h' f' → IsProper B S hS f')
    {𝒞 𝒴 : AlgebraicStacks.{u, w} B S hS} (p : 𝒞 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (W V : OpenSubstack 𝒞) (k : V.toAlgebraicStack ⟶ W.toAlgebraicStack)
    (hk : Nonempty (k ≫ W.inclusion ≅ V.inclusion))
    (hsep : IsSeparated B S hS (W.inclusion ≫ p)) (hft : IsFiniteType B S hS (W.inclusion ≫ p))
    (hkft : IsFiniteType B S hS k)
    (hdense : W.pointSet ⊆ @closure _ (pointTopology B S hS 𝒞.val) V.pointSet)
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS k (W.inclusion ≫ p)) :
    IsProper B S hS (W.inclusion ≫ p) := by
  obtain ⟨e⟩ := hk
  refine h0CQM _ _ _ k _ h𝒴 hft hkft hsep ?_ hlift
  refine dense_range_pointsMap_of_pointSet_subset_closure B S hS W k ?_
  rw [pointsMap_eq_of_hom₂ B S hS e.hom]
  exact hdense

end AlgebraicStacks


namespace AlgebraicStacks

/-- **Reduction of Stacks 0CQM to an affine Noetherian base.** Let
`f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` satisfy the hypotheses of Stacks 0CQM. If the conclusion of
Stacks 0CQM, read as universal closedness, holds whenever the target is the algebraic stack of an
affine locally Noetherian scheme of the site, then `f` is universally closed. -/
theorem universallyClosed_of_discreteExistenceAlong_of_affine
    (haff : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (𝒰' 𝒳' : AlgebraicStacks.{u, w} B S hS) (h' : 𝒰' ⟶ 𝒳')
        (f' : 𝒳' ⟶ schemeStack.{u, w} B S hS V),
        IsFiniteType B S hS f' → IsFiniteType B S hS h' → IsSeparated B S hS f' →
        @Dense _ (pointTopology B S hS 𝒳'.val) (Set.range (pointsMap B S hS h')) →
        ValuativeCriterion.DiscreteExistenceAlong B S hS h' f' → UniversallyClosed B S hS f')
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    UniversallyClosed B S hS f := by
  classical
  let _ : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hchart := (exists_scheme_atlas_iff_forall_scheme B S hS
    (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴).1 h𝒴
  obtain ⟨U, a, hasu, hasm, -⟩ := h𝒴
  have hvsm : ∀ i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      IsSmooth B S hS (schemeStackMap.{u, w} B S hS (affineChartHom U i) ≫ a) := fun i =>
    isSmooth_comp B S hS _ a
      (isSmooth_schemeStackMap B S hS _ (smooth_affineChartHom U i)) hasm
  refine universallyClosed_of_universallyClosed_smooth_cover B S hS f
    (fun i : ((BigFppfOver.toScheme B S hS).obj U).affineOpens =>
      schemeStack.{u, w} B S hS (affineChart U i))
    (fun i => schemeStackMap.{u, w} B S hS (affineChartHom U i) ≫ a) hvsm (fun y => ?_)
    (fun i => ?_)
  · obtain ⟨z, rfl⟩ := hasu y
    obtain ⟨i, w, rfl⟩ := exists_affineChart_point.{u, w} B S hS U z
    exact ⟨i, w, by rw [pointsMap_comp]; rfl⟩
  · set v := schemeStackMap.{u, w} B S hS (affineChartHom U i) ≫ a
    set P := twoFibreProductSquareAlgebraicStacks B S hS v f
    have hP := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS v f
    set Q := twoFibreProductSquareAlgebraicStacks B S hS P.snd h
    have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS P.snd h
    have hPsnd : IsSmooth B S hS P.snd :=
      isSmooth_baseChange B S hS v f P.swap (Bicategory.isTwoFibreProduct_swap hP) (hvsm i)
    exact haff (affineChart U i) (isAffine_affineChart U i) (hchart _ v (hvsm i)) Q.pt P.pt
      Q.fst P.fst (isFiniteType_baseChange B S hS f v P hP hf)
      (isFiniteType_baseChange B S hS h P.snd Q hQ hh)
      (isSeparated_baseChange_of_isTwoFibreProduct B S hS f v P.swap
        (Bicategory.isTwoFibreProduct_swap hP) hsep)
      (dense_range_pointsMap_fst_of_isFlat B S hS P.snd h (isFlat_of_isSmooth B S hS _ hPsnd)
        (isLocallyOfFinitePresentation_of_isSmooth B S hS _ hPsnd) hdense)
      (ValuativeCriterion.DiscreteExistenceAlong.baseChange B S hS f v h P hP Q hlift)

/-- **Reduction of Stacks 0CQM to an affine source.** Over the algebraic stack of an affine
scheme `V` of the site, let `f : 𝒳 ⟶ V` and `h : 𝒰 ⟶ 𝒳` be of finite type, with
the image of `|h|` dense and `f` satisfying the discrete existence part of the valuative criterion
along `h`. If universal closedness of `f` follows from the same hypotheses for every 1-morphism
`h'` locally of finite type out of the algebraic stack of an affine scheme, then `f` is
universally closed. -/
theorem universallyClosed_of_discreteExistenceAlong_of_affineSource
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ schemeStack.{u, w} B S hS V)
    (hcore : ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      ∀ h' : schemeStack.{u, w} B S hS U ⟶ 𝒳, IsLocallyOfFiniteType B S hS h' →
        @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h')) →
        ValuativeCriterion.DiscreteExistenceAlong B S hS h' f → UniversallyClosed B S hS f)
    {𝒰 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    UniversallyClosed B S hS f := by
  have h𝒰 : IsQuasiCompactStack.{u, w} B S hS 𝒰.val 𝒰.property :=
    isQuasiCompactStack_of_isQuasiCompactMorphism.{u, w} B S hS (h ≫ f)
      (isQuasiCompactMorphism_comp.{u, w} B S hS h f hh.2 hf.2)
      (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS V hV)
  obtain ⟨U, hU, c, hcsurj, hcsm⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒰).1 h𝒰
  have hcsm' := isSmooth_of_isRelativelySmooth.{u, w} B S hS c hcsm
  refine hcore U hU (c ≫ h) (isLocallyOfFiniteType_comp.{u, w} B S hS c h
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation.{u, w} B S hS
      (isLocallyOfFinitePresentation_of_isSmooth.{u, w} B S hS c hcsm')) hh.1) ?_ ?_
  · rw [pointsMap_comp, Set.range_comp, hcsurj.range_eq, Set.image_univ]
    exact hdense
  · intro q hq u hu
    exact ValuativeCriterion.DiscreteExistenceAlong.of_iso B S hS hlift q hq (u ≫ c.hom)
      (eqToIso hu ≪≫ (α_ u c.hom h.hom).symm)

/-- **Stacks 0CQM, reduced to its affine case.** Let `f : 𝒳 ⟶ 𝒴` and `h : 𝒰 ⟶ 𝒳` satisfy the
hypotheses of Stacks 0CQM. If `f'` is universally closed for every separated `f' : 𝒳' ⟶ V` of
finite type over the algebraic stack of an affine locally Noetherian scheme `V` of the site that
satisfies the discrete existence part of the valuative criterion along a 1-morphism `h'`, locally
of finite type and with dense image, out of the algebraic stack of an affine scheme, then `f` is
proper. -/
theorem isProper_of_discreteExistenceAlong_of_affineCore
    (hcore : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (𝒳' : AlgebraicStacks.{u, w} B S hS) (f' : 𝒳' ⟶ schemeStack.{u, w} B S hS V),
        IsFiniteType B S hS f' → IsSeparated B S hS f' →
        ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        ∀ h' : schemeStack.{u, w} B S hS U ⟶ 𝒳', IsLocallyOfFiniteType B S hS h' →
          @Dense _ (pointTopology B S hS 𝒳'.val) (Set.range (pointsMap B S hS h')) →
          ValuativeCriterion.DiscreteExistenceAlong B S hS h' f' → UniversallyClosed B S hS f')
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (h : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hf : IsFiniteType B S hS f) (hh : IsFiniteType B S hS h) (hsep : IsSeparated B S hS f)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS h)))
    (hlift : ValuativeCriterion.DiscreteExistenceAlong B S hS h f) :
    IsProper B S hS f :=
  ⟨hsep, hf, universallyClosed_of_discreteExistenceAlong_of_affine B S hS
    (fun V hV hVN _ 𝒳' h' f' hf' hh' hsep' hdense' hlift' =>
      universallyClosed_of_discreteExistenceAlong_of_affineSource B S hS V hV f'
        (fun U hU h'' hlft hd hl => hcore V hV hVN 𝒳' f' hf' hsep' U hU h'' hlft hd hl)
        h' hf' hh' hdense' hlift')
    h f h𝒴 hf hh hsep hdense hlift⟩


end AlgebraicStacks

end AlgebraicGeometry.Stack

end
