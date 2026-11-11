module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.AnalyticReformulation
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessOfProper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts

/-!
# The analytic reformulation is equivalent to the compatibility condition

Stacks 0GID ends with the sentence "under some assumptions of faithfulness of the
analytification functor, this requirement will be equivalent to the compatibility condition
formulated above". The requirement is
`AlgebraicGeometry.Artin.ContractionSituation.AnalyticSquareCommutes` and the compatibility
condition (4) is the existence of a
`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness`. The source does not say
which assumptions it means; this module formulates a precise set of them,
`AlgebraicGeometry.Artin.Analytification.FaithfulnessHypotheses`, and proves the equivalence
under them, for `V` a locally Noetherian scheme over `S`, `Z ⊆ |V|` closed, `u' : V ∖ Z ⟶ U'`
and `x̂ : V_{/Z} ⟶ W` adic in the sense of Definition 0AQ3 — exactly conditions (1), (2) and
(3) of the source.

## The assumptions

The assumptions concern only the fictitious category `An_S` and the fictitious functor
`Y ↦ Y^an`, which this library carries as the hypothesis
`AlgebraicGeometry.Artin.Analytification`; none of them is a statement about algebraic spaces,
and none is a result the source proves. They are:

* the inclusions `Y^rig ⟶ Y^an` are natural, and the comparison morphisms
  `can : (Y_{/Z})^rig ⟶ (Y ∖ Z)^an` are natural in the pair `(Y, Z)` — the source says these
  morphisms are *induced*, which is what naturality records;
* for an algebraic space `Y` and a closed `Z ⊆ |Y|`, `Y^an` is glued from the open pieces
  `(Y ∖ Z)^an` and `(Y_{/Z})^an` along their intersection `(Y_{/Z})^rig`, that is the square
  of `rigι`, `can`, and the analytifications of the two inclusions is a pushout in `An_S`;
* the analytification functor is faithful on morphisms from an algebraic space or from the
  completion of one along a closed subset to an algebraic space, and full on morphisms between
  algebraic spaces.

Faithfulness is used to transport the two restriction conditions of a witness from `An_S`
back to algebraic spaces; fullness, the existence half of faithfulness in the sense of a fully
faithful functor, is what produces the morphism `x' : V' ⟶ X'` from a morphism of analytic
spaces. Without some form of fullness the existence of `x'` cannot follow, since the algebraic
data `(u', x̂)` themselves have no common domain on which to compare them; that comparison is
precisely what the passage to `An_S` provides.

## The proof

`V'` is the dilatation of the formal modification `V_{/Z} ×_{x̂, W, g} X'_{/T'} ⟶ V_{/Z}`
(Stacks 0GDN, 0GDU), so its completion `V'_{/Z} ⟶ V_{/Z}` is a formal modification and
`(V'_{/Z})^rig ⟶ (V_{/Z})^rig` is an isomorphism by property (d). Given a witness, the
naturality of `can` along `V' ⟶ V` and along `x' : V' ⟶ X'` gives the square after
precomposition with that isomorphism. Conversely, if the square commutes then the two morphisms
`(V' ∖ Z)^an ⟶ X'^an` and `(V'_{/Z})^an ⟶ X'^an` built from `u'` and `x̂'` agree on
`(V'_{/Z})^rig`, so they glue to `V'^an ⟶ X'^an`; fullness gives `x'`, and faithfulness its two
restriction conditions.

## Main definitions

* `AlgebraicGeometry.Artin.Analytification.FaithfulnessHypotheses`: the assumptions above.

## Main results

* `ContractionSituation.analyticSquareCommutes_iff_nonempty_compatibilityWitness`:
  **Stacks 0GID**, the remark's final claim.

## References

* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GID](https://stacks.math.columbia.edu/tag/0GID)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Artin

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {An : Type v}
  [Category.{w} An]

/-- Pullbacks of fppf sheaves, created by the forgetful functor to presheaves. -/
local instance hasPullbacks_fppfSheaf_analyticReformulationEquivalence :
    HasPullbacks (FormalSpace.FppfSheaf B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf _ _)

local instance (priority := high) hasPullback_fppfSheaf_analyticReformulationEquivalence
    {X Y Z : FormalSpace.FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  HasLimitsOfShape.has_limit _

/-- Assumptions of faithfulness of the analytification functor, under which Stacks 0GID asserts
that its requirement is equivalent to compatibility condition (4). The source does not
formulate them; these are the ones under which the equivalence is proved here. All of them
concern the posited data `d`, none concerns algebraic spaces.

* `rigι_naturality` and `can_naturality`: the inclusions `Y^rig ⟶ Y^an` and the comparison
  morphisms `can : (Y_{/Z})^rig ⟶ (Y ∖ Z)^an`, which the source says are induced, are natural;
* `isPushout`: `Y^an` is glued from `(Y ∖ Z)^an` and `(Y_{/Z})^an` along `(Y_{/Z})^rig`;
* `map_injective`, `map_injective_completion`, `map_surjective`: the analytification functor is
  faithful on morphisms to an algebraic space from an algebraic space or from the completion of
  one along a closed subset, and full on morphisms between algebraic spaces. -/
structure Analytification.FaithfulnessHypotheses (d : Analytification B S hS An) : Prop where
  /-- The inclusions `Y^rig ⟶ Y^an` are natural. -/
  rigι_naturality : ∀ {Y Y' : FormalSpace.FppfSheaf B S hS} (f : Y ⟶ Y'),
    d.rigFunctor.map f ≫ d.rigι Y' = d.rigι Y ≫ d.anFunctor.map f
  /-- The comparison morphisms `can` are natural: if `f : Y ⟶ Y'` is a morphism of algebraic
  spaces restricting to `a : Y ∖ Z ⟶ Y' ∖ Z'` and to `b : Y_{/Z} ⟶ Y'_{/Z'}`, then
  `can ∘ b^rig = a^an ∘ can`. -/
  can_naturality : ∀ {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : Y ⟶ Y') (Z : Set (Space.points B S hS Y))
    (hZ : IsClosed Z) (Z' : Set (Space.points B S hS Y')) (hZ' : IsClosed Z')
    (a : (Space.openSubspaceOfPoints B S hS Y Zᶜ).toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS Y' Z'ᶜ).toFunctor)
    (b : Space.completionSheaf B S hS Y Z ⟶ Space.completionSheaf B S hS Y' Z'),
    a ≫ (Space.openSubspaceOfPoints B S hS Y' Z'ᶜ).ι =
        (Space.openSubspaceOfPoints B S hS Y Zᶜ).ι ≫ f →
      b ≫ Space.completionSheafInclusion B S hS Y' Z' =
        Space.completionSheafInclusion B S hS Y Z ≫ Space.sheafifiedULiftMap B S hS f →
      d.can Y hY Z hZ ≫ d.anFunctor.map (Space.sheafifiedULiftMap B S hS a) =
        d.rigFunctor.map b ≫ d.can Y' hY' Z' hZ'
  /-- For an algebraic space `Y` and a closed `Z ⊆ |Y|`, `Y^an` is the union of the open pieces
  `(Y ∖ Z)^an` and `(Y_{/Z})^an`, glued along their intersection `(Y_{/Z})^rig`. -/
  isPushout : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (Z : Set (Space.points B S hS Y)) (hZ : IsClosed Z),
    IsPushout (d.rigι (Space.completionSheaf B S hS Y Z)) (d.can Y hY Z hZ)
      (d.anFunctor.map (Space.completionSheafInclusion B S hS Y Z))
      (d.anFunctor.map
        (Space.sheafifiedULiftMap B S hS (Space.openSubspaceOfPoints B S hS Y Zᶜ).ι))
  /-- The analytification functor is faithful on morphisms between algebraic spaces. -/
  map_injective : ∀ {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
    IsAlgebraicSpace B S hS X →
      Function.Injective fun f : Y ⟶ X ↦ d.anFunctor.map (Space.sheafifiedULiftMap B S hS f)
  /-- The analytification functor is faithful on morphisms from the completion of an algebraic
  space along a closed subset to an algebraic space. -/
  map_injective_completion : ∀ {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
    IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS X →
      ∀ (Z : Set (Space.points B S hS Y)), IsClosed Z →
        Function.Injective (d.anFunctor.map :
          (Space.completionSheaf B S hS Y Z ⟶ Space.sheafifiedULift B S hS X) → _)
  /-- The analytification functor is full on morphisms between algebraic spaces. -/
  map_surjective : ∀ {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS Y →
    IsAlgebraicSpace B S hS X →
      Function.Surjective fun f : Y ⟶ X ↦ d.anFunctor.map (Space.sheafifiedULiftMap B S hS f)

namespace ContractionSituation

variable (c : ContractionSituation B S hS)

/-- **Stacks 0GID.** In Situation 0GH8 let `V` be a locally Noetherian scheme over `S` and let
`(Z, u', x̂)` satisfy conditions (1), (2) and (3): `Z ⊆ |V|` is closed, `u' : V ∖ Z ⟶ U'`, and
`x̂ : V_{/Z} ⟶ W` is adic. Under the assumptions of faithfulness
`Analytification.FaithfulnessHypotheses` on the analytification data, the requirement that the
remark's square commute is equivalent to compatibility condition (4): the existence of
`V' ⟶ V`, `x̂'` and `x'` witnessing the compatibility of `u'` and `x̂`. -/
@[stacks 0GID "the remark's final claim: under assumptions of faithfulness of the \
analytification functor, the requirement that the displayed square commute is equivalent to \
the compatibility condition (4). The source does not formulate the assumptions; the ones used \
are Analytification.FaithfulnessHypotheses (naturality of Y^rig ⟶ Y^an and of can, Y^an glued \
from (Y ∖ Z)^an and (Y_{/Z})^an along (Y_{/Z})^rig, and the analytification functor faithful \
on morphisms to algebraic spaces from algebraic spaces and their completions, and full on \
morphisms of algebraic spaces). V is a locally Noetherian scheme over S and x̂ is adic in the \
sense of Definition 0AQ3, which are the source's hypotheses. The fiction itself, the square and \
its well-formedness are AlgebraicGeometry.Artin.Analytification, \
AlgebraicGeometry.Artin.ContractionSituation.AnalyticSquareCommutes and \
AlgebraicGeometry.Artin.ContractionSituation.isIso_rigFunctor_map_g_and_range_pointsMap_ι_U'; \
together these cover the whole remark"]
theorem analyticSquareCommutes_iff_nonempty_compatibilityWitness
    {d : Analytification B S hS An} (hd : d.FaithfulnessHypotheses) {V : BigFppfOver B S hS}
    (hVN : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : IsClosed Z)
    (u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor)
    (xhat : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W)
    (hxhat : FormalSpace.IsAdicMorphism B S hS xhat) :
    AnalyticSquareCommutes c d ⟨Z, hZ, u, xhat,
        FormalSpace.isAdicOnEveryAffineEtaleDiagramNoetherian_of_isAdicMorphism B S hS xhat
          hxhat⟩ ↔
      Nonempty (CompatibilityWitness c V Z u xhat) := by
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hVN' := Space.isLocallyNoetherian_yoneda B S hS V hVN
  have hX' := c.isAlgebraicSpace_X'
  -- the formal modification `V_{/Z} ×_{x̂, W, g} X'_{/T'} ⟶ V_{/Z}` (Stacks 0GDN)
  have h𝔣 : FormalSpace.IsFormalModification B S hS (pullback.snd c.g xhat) :=
    FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism B S hS c.g xhat
      (FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hVsp hVN' Z hZ)
      hxhat c.isFormalModification_g
  have hG : d.rigFunctor.map c.g = (gRigIso c d).hom := rfl
  have hpoX : d.rigι (Space.completionSheaf B S hS c.X' c.T') ≫
        d.anFunctor.map (Space.completionSheafInclusion B S hS c.X' c.T') =
      d.can c.X' hX' c.T' c.isClosed_T' ≫
        d.anFunctor.map (Space.sheafifiedULiftMap B S hS c.U'.ι) :=
    (hd.isPushout c.X' hX' c.T' c.isClosed_T').w
  constructor
  · intro hsq
    have hsq' : d.can (yoneda.obj V) hVsp Z hZ ≫
          d.anFunctor.map (Space.sheafifiedULiftMap B S hS u) =
        d.rigFunctor.map xhat ≫ (gRigIso c d).inv ≫ d.can c.X' hX' c.T' c.isClosed_T' := hsq
    -- the dilatation `V' ⟶ V` of that formal modification (Stacks 0GDU)
    obtain ⟨V₃, hV₃, p, hp, hpU, ⟨e⟩⟩ :=
      FormalSpace.exists_isProper_completion_iso_of_isFormalModification hVsp hVN' Z hZ h𝔣
    have := hpU
    let Z₃ := Space.pointsMap B S hS V₃ p ⁻¹' Z
    have hZ₃ : IsClosed Z₃ := hZ.preimage (Space.continuous_pointsMap B S hS p)
    obtain ⟨pZ, hpZ⟩ : ∃ pZ, pZ = Space.completionSheafRestrict B S hS p Z₃ Z (fun _ hz => hz) :=
      ⟨_, rfl⟩
    have hpZincl : pZ ≫ Space.completionSheafInclusion B S hS (yoneda.obj V) Z =
        Space.completionSheafInclusion B S hS V₃ Z₃ ≫ Space.sheafifiedULiftMap B S hS p := by
      rw [hpZ]
      exact Space.completionSheafRestrict_comp_inclusion B S hS p Z₃ Z _
    let eL : Space.completionSheaf B S hS V₃ Z₃ ≅ pullback c.g xhat := (Over.forget _).mapIso e
    have hcompl_p : eL.hom ≫ pullback.snd c.g xhat =
        Space.completionSheafRestrict B S hS p Z₃ Z (fun _ hz => hz) :=
      (Over.w e.hom).trans (Space.completionSheafRestrict_self B S hS p Z _).symm
    obtain ⟨μ, hμdef⟩ : ∃ μ : Space.completionSheaf B S hS V₃ Z₃ ⟶
        Space.completionSheaf B S hS c.X' c.T', μ = eL.hom ≫ pullback.fst c.g xhat := ⟨_, rfl⟩
    have hμ : μ ≫ c.g = pZ ≫ xhat := by
      rw [hμdef, hpZ, ← hcompl_p, Category.assoc, pullback.condition, Category.assoc]
    -- `V' ∖ |p|⁻¹ Z ⟶ V ∖ Z` is an isomorphism
    obtain ⟨k, hkdef⟩ : ∃ k, k = Space.openSubspaceOfPointsRestrict B S hS p Z₃ᶜ Zᶜ
        (fun _ hz => hz) := ⟨_, rfl⟩
    have hk : k ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι =
        (Space.openSubspaceOfPoints B S hS V₃ Z₃ᶜ).ι ≫ p := by
      rw [hkdef]
      rfl
    have hsqo : IsPullback (Space.openSubspaceOfPoints B S hS V₃ Z₃ᶜ).ι k p
        (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι :=
      FormalSpace.isPullback_ι_openSubspaceOfPoints_compl B S hS p Z k hk
    have hkiso : IsIso k := by
      rw [← hsqo.isoPullback_hom_snd]
      infer_instance
    obtain ⟨j, hjdef⟩ : ∃ j, j = inv k ≫ (Space.openSubspaceOfPoints B S hS V₃ Z₃ᶜ).ι :=
      ⟨_, rfl⟩
    have hj : j ≫ p = (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι := by
      rw [hjdef, Category.assoc, hsqo.w, IsIso.inv_hom_id_assoc]
    -- the two morphisms to `X'^an` agree on `(V'_{/Z})^rig`
    have hnat_p : d.can V₃ hV₃ Z₃ hZ₃ ≫ d.anFunctor.map (Space.sheafifiedULiftMap B S hS k) =
        d.rigFunctor.map pZ ≫ d.can (yoneda.obj V) hVsp Z hZ :=
      hd.can_naturality hV₃ hVsp p Z₃ hZ₃ Z hZ k pZ hk hpZincl
    have hrig : d.rigFunctor.map pZ ≫ d.rigFunctor.map xhat ≫ (gRigIso c d).inv =
        d.rigFunctor.map μ := by
      rw [← Functor.map_comp_assoc, ← hμ, Functor.map_comp d.rigFunctor μ c.g, Category.assoc,
        hG, Iso.hom_inv_id, Category.comp_id]
    have hw : d.rigι (Space.completionSheaf B S hS V₃ Z₃) ≫
          d.anFunctor.map (μ ≫ Space.completionSheafInclusion B S hS c.X' c.T') =
        d.can V₃ hV₃ Z₃ hZ₃ ≫
          d.anFunctor.map (Space.sheafifiedULiftMap B S hS (k ≫ u ≫ c.U'.ι)) := by
      simp only [Space.sheafifiedULiftMap_comp, Functor.map_comp]
      rw [reassoc_of% hnat_p, reassoc_of% hsq', ← reassoc_of% hd.rigι_naturality μ, hpoX,
        ← reassoc_of% hrig]
      exact congrArg (d.rigFunctor.map pZ ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (d.rigFunctor.map xhat ≫ ·) (Category.assoc _ _ _))).symm
    let hpo := hd.isPushout V₃ hV₃ Z₃ hZ₃
    -- the glued morphism `V'^an ⟶ X'^an`, and `x'` by fullness
    obtain ⟨x', hx'⟩ := hd.map_surjective hV₃ hX' (hpo.desc _ _ hw)
    have hx' : d.anFunctor.map (Space.sheafifiedULiftMap B S hS x') = hpo.desc _ _ hw := hx'
    have hVZ : IsAlgebraicSpace B S hS
        (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor :=
      (Space.isOpenSubspace_openSubspaceOfPoints B S hS hVsp Zᶜ hZ.isOpen_compl).1
    refine ⟨{ V' := V₃
              isAlgebraicSpace_V' := hV₃
              p := p
              isProper_p := hp
              j := j
              isPullback_j := isPullback_id_of_isIso_pullback_snd _ p j hj
              xhat' := μ
              isPullback_xhat' := ?_
              x' := x'
              restrict_x' := ?_
              completion_x' := ?_ }⟩
    · rw [hμdef]
      refine (IsPullback.of_iso_pullback ⟨?_⟩ eL rfl hcompl_p).flip
      rw [← hcompl_p]
      exact (Category.assoc _ _ _).trans ((congrArg (eL.hom ≫ ·) pullback.condition).trans
        (Category.assoc _ _ _).symm)
    · apply hd.map_injective hVZ hX'
      beta_reduce
      rw [hjdef, Space.sheafifiedULiftMap_comp B S hS _ x', Functor.map_comp, hx',
        Space.sheafifiedULiftMap_comp B S hS (inv k),
        Functor.map_comp d.anFunctor (Space.sheafifiedULiftMap B S hS (inv k)), Category.assoc,
        hpo.inr_desc, ← Functor.map_comp, ← Space.sheafifiedULiftMap_comp,
        IsIso.inv_hom_id_assoc]
    · apply hd.map_injective_completion hV₃ hX' Z₃ hZ₃
      rw [Functor.map_comp, hx', hpo.inl_desc]
  · rintro ⟨w⟩
    let Z₃ := Space.pointsMap B S hS w.V' w.p ⁻¹' Z
    have hZ₃ : IsClosed Z₃ := hZ.preimage (Space.continuous_pointsMap B S hS w.p)
    obtain ⟨pZ, hpZ⟩ : ∃ pZ, pZ = Space.completionSheafRestrict B S hS w.p Z₃ Z
        (fun _ hz => hz) := ⟨_, rfl⟩
    have hpZincl : pZ ≫ Space.completionSheafInclusion B S hS (yoneda.obj V) Z =
        Space.completionSheafInclusion B S hS w.V' Z₃ ≫ Space.sheafifiedULiftMap B S hS w.p := by
      rw [hpZ]
      exact Space.completionSheafRestrict_comp_inclusion B S hS w.p Z₃ Z _
    obtain ⟨k, hkdef⟩ : ∃ k, k = Space.openSubspaceOfPointsRestrict B S hS w.p Z₃ᶜ Zᶜ
        (fun _ hz => hz) := ⟨_, rfl⟩
    have hk : k ≫ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).ι =
        (Space.openSubspaceOfPoints B S hS w.V' Z₃ᶜ).ι ≫ w.p := by
      rw [hkdef]
      rfl
    have hkj : k ≫ w.j = (Space.openSubspaceOfPoints B S hS w.V' Z₃ᶜ).ι := by
      have h1 := w.isPullback_j.lift_fst k _ hk
      have h2 := w.isPullback_j.lift_snd k _ hk
      rw [Category.comp_id] at h1
      rwa [h1] at h2
    have hpb : IsPullback w.xhat' pZ c.g xhat := by
      rw [hpZ]
      exact w.isPullback_xhat'.flip
    -- `(V'_{/Z})^rig ⟶ (V_{/Z})^rig` is an isomorphism, by Stacks 0GDN and property (d)
    have hP : IsIso (d.rigFunctor.map pZ) := by
      have h := d.isIso_rigFunctor_map_of_isFormalModification _ h𝔣
      rw [← hpb.isoPullback_hom_snd, Functor.map_comp]
      infer_instance
    have hnat_p : d.can w.V' w.isAlgebraicSpace_V' Z₃ hZ₃ ≫
          d.anFunctor.map (Space.sheafifiedULiftMap B S hS k) =
        d.rigFunctor.map pZ ≫ d.can (yoneda.obj V) hVsp Z hZ :=
      hd.can_naturality w.isAlgebraicSpace_V' hVsp w.p Z₃ hZ₃ Z hZ k pZ hk hpZincl
    have hxu : (k ≫ u) ≫ c.U'.ι = (Space.openSubspaceOfPoints B S hS w.V' Z₃ᶜ).ι ≫ w.x' := by
      rw [Category.assoc, ← w.restrict_x', ← Category.assoc, hkj]
    have hnat_x : d.can w.V' w.isAlgebraicSpace_V' Z₃ hZ₃ ≫
          d.anFunctor.map (Space.sheafifiedULiftMap B S hS (k ≫ u)) =
        d.rigFunctor.map w.xhat' ≫ d.can c.X' hX' c.T' c.isClosed_T' :=
      hd.can_naturality w.isAlgebraicSpace_V' hX' w.x' Z₃ hZ₃ c.T' c.isClosed_T' (k ≫ u)
        w.xhat' hxu w.completion_x'.symm
    have hxg : w.xhat' ≫ c.g = pZ ≫ xhat := hpb.w
    dsimp only [AnalyticSquareCommutes]
    apply (cancel_epi (d.rigFunctor.map pZ)).1
    have e2 : d.rigFunctor.map pZ ≫ d.rigFunctor.map xhat =
        d.rigFunctor.map w.xhat' ≫ (gRigIso c d).hom := by
      rw [← hG, ← d.rigFunctor.map_comp, ← d.rigFunctor.map_comp, hxg]
    rw [← reassoc_of% hnat_p, ← Functor.map_comp d.anFunctor, ← Space.sheafifiedULiftMap_comp,
      hnat_x]
    have e3 : d.rigFunctor.map pZ ≫ d.rigFunctor.map xhat ≫ (gRigIso c d).inv =
        d.rigFunctor.map w.xhat' := by
      rw [← Category.assoc, e2, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (congrArg (· ≫ d.can c.X' hX' c.T' c.isClosed_T') e3).symm.trans
      ((Category.assoc _ _ _).trans
        (congrArg (d.rigFunctor.map pZ ≫ ·) (Category.assoc _ _ _)))

end ContractionSituation

end AlgebraicGeometry.Artin

end
