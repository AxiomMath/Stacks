module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.AmpleFiniteSet
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.ProjImmersion
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Action
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Equivariant.ActionGroupoidPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientCharts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient of a scheme by a free action of a finite locally free group scheme

Let `G` be a group scheme over a scheme `S`, finite locally free over `S`, acting freely on a
scheme `X` over `S`. If every finite set of points of `X` lying in a single fibre of `X ⟶ S` is
contained in an affine open of `X` — which holds under each of the seven alternatives of
condition (3) of Stacks 07S7 — then the fppf quotient sheaf `X/G` is a scheme, the quotient
morphism `X ⟶ X/G` is surjective and finite locally free, the shear morphism
`G ×_S X ⟶ X ×_{X/G} X` is an isomorphism, and `X ⟶ X/G` has sections fppf locally.

## Main definitions

* `AlgebraicGeometry.HasAffineFinitePointsInFibres`: every finite set of points contained in a
  single fibre of a morphism lies in an affine open of the source.
* `AlgebraicGeometry.HasImmersionToAffine` and `AlgebraicGeometry.HasImmersionToProj`: a scheme
  admitting an immersion into an affine scheme, respectively into the homogeneous spectrum of a
  graded ring.
* `Stacks.Groupoids.GroupoidScheme.equivalenceRelation`: the equivalence relation structure on
  a groupoid scheme whose target and source are jointly monic.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isEquivalenceRelation`: a groupoid scheme whose target and
  source are jointly monic is an equivalence relation.
* `AlgebraicGeometry.jointlyMono₂_actionGroupoid`: for a free action the target and the source
  of the action groupoid are jointly monic.
* `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isAffineHom`,
  `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isQuasiAffineHom`,
  `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isProjective`,
  `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isQuasiProjective`,
  `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_hasImmersionToAffine` and
  `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_hasImmersionToProj`: six of the seven
  alternatives of condition (3) of Stacks 07S7 imply the fibrewise affineness condition.
* `AlgebraicGeometry.exists_isAffineOpen_orbit_subset_of_universallyInjective`: for a radicial
  group scheme every orbit lies in an affine open.
* `AlgebraicGeometry.nonempty_finiteFlatQuotient_actionGroupoid` and
  `AlgebraicGeometry.nonempty_finiteFlatQuotient_actionGroupoid_of_geometry`: the fppf quotient
  sheaf `X/G` is a scheme, under the fibrewise affineness condition and under each of the seven
  alternatives of condition (3) of Stacks 07S7.
* `AlgebraicGeometry.isFppfTorsor_quotientMap`: the shear morphism `G ×_S X ⟶ X ×_{X/G} X` is an
  isomorphism and `X ⟶ X/G` has sections fppf locally, the two conditions of Groupoids,
  Definition 39.11.3 for `X ⟶ X/G` to be an fppf `G`-torsor.

## Implementation notes

The action groupoid is `AlgebraicGeometry.groupoidSchemeOfAction` with the base taken to be `S`
itself, so its objects are `X` pushed along the identity of `S`; on underlying schemes and on
underlying morphisms that push is the identity, and the groupoid's structure morphisms are read
as the projection `G ×_S X ⟶ X` and the action.

For any groupoid scheme the identity, the inverse and the composition are the reflexivity,
symmetry and transitivity witnesses of `CategoryTheory.EquivalenceRelation`, and the object of
composable arrows is the pullback that structure asks for, so joint monicity of the target and
the source makes it an equivalence relation (Groupoids, Lemma 39.10.3). For the action groupoid
joint monicity is monicity of `(g, x) ↦ (g · x, x)`, which is Stacks 07S2 in the form
`AlgebraicGeometry.isFreeAction_iff_mono_leftSMul`.

The torsor property is stated as the two conditions of Groupoids, Definition 39.11.3 rather than
with `AlgebraicGeometry.IsFppfTorsor`, which concerns an action of a group scheme over the
quotient.

## References

* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 049A](https://stacks.math.columbia.edu/tag/049A)
* [Stacks Project, Tag 07S2](https://stacks.math.columbia.edu/tag/07S2)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 07S7](https://stacks.math.columbia.edu/tag/07S7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open Stacks.Groupoids Stacks.Morphisms
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Groupoids

/-- The identity, the inverse and the composition of a groupoid scheme witness reflexivity,
symmetry and transitivity of the pair `(t, s)` of its target and source. -/
noncomputable def GroupoidScheme.equivalenceRelation {S : Scheme.{u}} (H : GroupoidScheme S)
    [JointlyMono₂ H.target H.source] : EquivalenceRelation H.target H.source where
  right_cancellation := JointlyMono₂.right_cancellation
  r := H.identity
  reflexivity₁ := H.target_identity
  reflexivity₂ := H.source_identity
  s := H.inverse
  symmetry₁ := H.target_inverse
  symmetry₂ := H.source_inverse
  c := PullbackCone.mk (pullback.fst H.source H.target) (pullback.snd H.source H.target)
    pullback.condition
  isLimit := pullbackIsPullback H.source H.target
  t := H.comp
  transitivity₁ := H.target_comp
  transitivity₂ := H.source_comp

/-- A groupoid scheme whose target and source are jointly monic is an equivalence relation. -/
theorem GroupoidScheme.isEquivalenceRelation {S : Scheme.{u}} (H : GroupoidScheme S)
    [JointlyMono₂ H.target H.source] : IsEquivalenceRelation H.target H.source :=
  H.equivalenceRelation.isEquivalenceRelation

end Stacks.Groupoids

namespace AlgebraicGeometry

/-- Every finite set of points contained in a single fibre of `f : X ⟶ S` is contained in an
affine open of `X`. -/
def HasAffineFinitePointsInFibres {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (s : S) (E : Set X), E.Finite → (∀ x ∈ E, f.base x = s) →
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ (U : Set X)

/-- A scheme admitting an immersion into an affine scheme. -/
def HasImmersionToAffine (X : Scheme.{u}) : Prop :=
  ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (i : X ⟶ Y), IsImmersion i

/-- A scheme admitting an immersion into the homogeneous spectrum of a graded ring. -/
def HasImmersionToProj (X : Scheme.{u}) : Prop :=
  ∃ (R : Type u) (hR : CommRing R),
    letI : CommRing R := hR
    ∃ (𝒮 : ℕ → AddSubgroup R) (h𝒮 : GradedRing 𝒮),
      letI : GradedRing 𝒮 := h𝒮
      ∃ i : X ⟶ Proj 𝒮, IsImmersion i

section Fibres

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The fibrewise affineness condition holds as soon as, over every affine open `V` of the base,
every finite set of points of `f ⁻¹ᵁ V` lies in an affine open of `f ⁻¹ᵁ V`. -/
theorem hasAffineFinitePointsInFibres_of_forall_isAffineOpen
    (h : ∀ V : S.Opens, IsAffineOpen V → ∀ E : Set (f ⁻¹ᵁ V).toScheme, E.Finite →
      ∃ U : (f ⁻¹ᵁ V).toScheme.Opens, IsAffineOpen U ∧ E ⊆ (U : Set (f ⁻¹ᵁ V).toScheme)) :
    HasAffineFinitePointsInFibres f := by
  intro s E hE hEs
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ s)
  have hEV : ∀ x ∈ E, x ∈ f ⁻¹ᵁ V := fun x hx => show f.base x ∈ V from hEs x hx ▸ hsV
  obtain ⟨U, hU, hEU⟩ := h V hV (Subtype.val ⁻¹' E) (hE.preimage Subtype.val_injective.injOn)
  refine ⟨(f ⁻¹ᵁ V).ι ''ᵁ U, hU.image_of_isOpenImmersion _, fun x hx => ?_⟩
  exact (Scheme.Opens.mem_ι_image_iff _).mpr (hEU (show (⟨x, hEV x hx⟩ : _) ∈ _ from hx))

/-- An affine morphism satisfies the fibrewise affineness condition. -/
theorem hasAffineFinitePointsInFibres_of_isAffineHom [IsAffineHom f] :
    HasAffineFinitePointsInFibres f := by
  refine hasAffineFinitePointsInFibres_of_forall_isAffineOpen f fun V hV E _ => ?_
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  exact ⟨⊤, isAffineOpen_top _, fun x _ => trivial⟩

/-- A quasi-affine morphism satisfies the fibrewise affineness condition. -/
theorem hasAffineFinitePointsInFibres_of_isQuasiAffineHom [IsQuasiAffineHom f] :
    HasAffineFinitePointsInFibres f := by
  refine hasAffineFinitePointsInFibres_of_forall_isAffineOpen f fun V hV E hE => ?_
  have : Scheme.IsQuasiAffine (f ⁻¹ᵁ V).toScheme :=
    IsQuasiAffineHom.isQuasiAffine_preimage V hV
  exact Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_isQuasiAffine hE

/-- A scheme immersed in an affine scheme satisfies the fibrewise affineness condition for every
morphism out of it. -/
theorem hasAffineFinitePointsInFibres_of_hasImmersionToAffine (hX : HasImmersionToAffine X) :
    HasAffineFinitePointsInFibres f := by
  obtain ⟨Y, hY, i, hi⟩ := hX
  exact fun _ E hE _ =>
    Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_affine i hE

/-- A scheme immersed in the homogeneous spectrum of a graded ring satisfies the fibrewise
affineness condition for every morphism out of it. -/
theorem hasAffineFinitePointsInFibres_of_hasImmersionToProj (hX : HasImmersionToProj X) :
    HasAffineFinitePointsInFibres f := by
  obtain ⟨R, hR, 𝒮, h𝒮, i, hi⟩ := hX
  exact fun _ E hE _ =>
    Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj 𝒮 i hE

/-- A quasi-projective morphism satisfies the fibrewise affineness condition. -/
@[sga "4 XIII 3.1" "(ii), special case"]
theorem hasAffineFinitePointsInFibres_of_isQuasiProjective (hf : IsQuasiProjective f) :
    HasAffineFinitePointsInFibres f := by
  obtain ⟨-, L, hL, hample⟩ := hf
  refine hasAffineFinitePointsInFibres_of_forall_isAffineOpen f fun V hV E hE => ?_
  exact Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_of_ample _
    (hample.isAmple_preimage _ _ V hV) hE

/-- A projective morphism satisfies the fibrewise affineness condition. -/
theorem hasAffineFinitePointsInFibres_of_isProjective (hf : IsProjective f) :
    HasAffineFinitePointsInFibres f := by
  obtain ⟨M, -, -, hqc, i, hi, hfi⟩ := hf
  refine hasAffineFinitePointsInFibres_of_forall_isAffineOpen f fun V hV E hE => ?_
  have hpb := Stacks.SymGraded.schemeProjectiveBundle_isPullback M hqc V hV
  have hw : ((f ⁻¹ᵁ V).ι ≫ i) ≫ Stacks.SymGraded.schemeProjectiveBundleToBase M hqc =
      (f ∣_ V) ≫ V.ι := by
    rw [Category.assoc, show i ≫ Stacks.SymGraded.schemeProjectiveBundleToBase M hqc = f from hfi,
      morphismRestrict_ι]
  have himm : IsImmersion ((f ⁻¹ᵁ V).ι ≫ i) := inferInstance
  set l := hpb.lift ((f ⁻¹ᵁ V).ι ≫ i) (f ∣_ V) hw with hldef
  have hcomp : IsImmersion
      (l ≫ (Stacks.SymGraded.schemeProjectiveBundle M hqc).chart V hV) := by
    rwa [hldef, hpb.lift_fst]
  have : IsImmersion l :=
    IsImmersion.of_comp l ((Stacks.SymGraded.schemeProjectiveBundle M hqc).chart V hV)
  exact Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_proj _ l hE

end Fibres

variable {S : Scheme.{u}} (G X : Over S) [GrpObj G] [ModObj G X]

/-- The inverse of the action groupoid, which sends `(g, x)` to `(g⁻¹, g · x)`, followed by the
projection is the action. -/
theorem actionGroupoidInverse_comp_snd :
    actionInverse (Over.mk (𝟙 S)) G X ≫ snd G X = γ[G, X] :=
  Stacks.Groupoids.ActionGroupoid.inverse_source G X

/-- Composing the inverse of the action groupoid with the action returns the projection. -/
theorem actionGroupoidInverse_comp_act :
    actionInverse (Over.mk (𝟙 S)) G X ≫ γ[G, X] = snd G X :=
  Stacks.Groupoids.ActionGroupoid.inverse_target G X

/-- The inverse of the action groupoid is an involution. -/
theorem actionGroupoidInverse_involutive :
    actionInverse (Over.mk (𝟙 S)) G X ≫ actionInverse (Over.mk (𝟙 S)) G X = 𝟙 (G ⊗ X) :=
  Stacks.Groupoids.ActionGroupoid.inverse_comp_inverse G X

/-- The inverse of the action groupoid is an isomorphism. -/
instance isIso_actionGroupoidInverse : IsIso (actionInverse (Over.mk (𝟙 S)) G X) :=
  ⟨actionInverse (Over.mk (𝟙 S)) G X, actionGroupoidInverse_involutive G X,
    actionGroupoidInverse_involutive G X⟩

/-- The source of the action groupoid of a finite locally free group scheme is finite locally
free. -/
instance isFiniteLocallyFree_actionGroupoid_source [IsFiniteLocallyFree G.hom] :
    IsFiniteLocallyFree (actionGroupoid (Over.mk (𝟙 S)) G X).source.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback G.hom X.hom) inferInstance

/-- The target of the action groupoid of a finite locally free group scheme is finite locally
free. -/
instance isFiniteLocallyFree_actionGroupoid_target [IsFiniteLocallyFree G.hom] :
    IsFiniteLocallyFree (actionGroupoid (Over.mk (𝟙 S)) G X).target.left := by
  have hL : (actionInverse (Over.mk (𝟙 S)) G X).left ≫ (snd G X).left = (γ[G, X]).left :=
    congrArg Over.Hom.left (actionGroupoidInverse_comp_snd G X)
  have : IsIso (actionInverse (Over.mk (𝟙 S)) G X).left := by
    refine ⟨(actionInverse (Over.mk (𝟙 S)) G X).left, ?_, ?_⟩ <;>
      simpa using congrArg Over.Hom.left (actionGroupoidInverse_involutive G X)
  change IsFiniteLocallyFree (γ[G, X]).left
  rw [← hL]
  exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree)
    (actionInverse (Over.mk (𝟙 S)) G X).left _
    (isFiniteLocallyFree_actionGroupoid_source G X)

/-- For a free action the target and the source of the action groupoid are jointly monic. -/
theorem jointlyMono₂_actionGroupoid (hfree : IsFreeAction G X) :
    JointlyMono₂ (actionGroupoid (Over.mk (𝟙 S)) G X).target
      (actionGroupoid (Over.mk (𝟙 S)) G X).source := by
  have hmono : Mono (ModObj.leftSMul G X) := (isFreeAction_iff_mono_leftSMul G X).mp hfree
  refine ⟨fun T f g h₁ h₂ => ?_⟩
  have hbase : ∀ k : T ⟶ (actionGroupoid (Over.mk (𝟙 S)) G X).arrows,
      k.left ≫ (G ⊗ X).hom = T.hom := by
    intro k
    calc k.left ≫ (G ⊗ X).hom = k.left ≫ ((G ⊗ X).hom ≫ 𝟙 S) :=
          congrArg (fun z : (G ⊗ X).left ⟶ S => k.left ≫ z)
            (Category.comp_id (G ⊗ X).hom).symm
      _ = T.hom := Over.w k
  let f' : T ⟶ G ⊗ X := Over.homMk f.left (hbase f)
  let g' : T ⟶ G ⊗ X := Over.homMk g.left (hbase g)
  have hfa : f' ≫ γ[G, X] = g' ≫ γ[G, X] :=
    Over.OverMorphism.ext (congrArg Over.Hom.left h₁)
  have hfs : f' ≫ snd G X = g' ≫ snd G X :=
    Over.OverMorphism.ext (congrArg Over.Hom.left h₂)
  have : f' = g' := by
    refine hmono.right_cancellation f' g' ?_
    refine CartesianMonoidalCategory.hom_ext (C := Over S) _ _ ?_ ?_
    · simpa using hfa
    · simpa using hfs
  exact Over.OverMorphism.ext (congrArg Over.Hom.left this)

/-- The orbit of a point of `X` under the action of a finite locally free group scheme is
finite. -/
theorem finite_actionOrbit [IsFiniteLocallyFree G.hom] (u : X.left) :
    ((γ[G, X]).left.base '' ((snd G X).left.base ⁻¹' {u})).Finite := by
  have hfin : IsFinite (snd G X).left :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (snd G X).left).mp (isFiniteLocallyFree_actionGroupoid_source G X) |>.1
  exact Set.Finite.image _ ((snd G X).left.finite_preimage_singleton u)

/-- A point of `X` and its image under the action lie in the same fibre of `X ⟶ S`. -/
theorem hom_base_act_eq (r : (G ⊗ X).left) :
    X.hom.base ((γ[G, X]).left.base r) = X.hom.base ((snd G X).left.base r) := by
  have key : ∀ k : G ⊗ X ⟶ X, X.hom.base (k.left.base r) = (G ⊗ X).hom.base r := fun k => by
    rw [← Over.w k]; rfl
  rw [key γ[G, X], key (snd G X)]

/-- Under the fibrewise affineness hypothesis, every orbit of the action of a finite locally free
group scheme lies in an affine open of `X`. -/
theorem exists_isAffineOpen_orbit_subset [IsFiniteLocallyFree G.hom]
    (hfib : HasAffineFinitePointsInFibres X.hom) (u : X.left) :
    ∃ W : X.left.Opens, IsAffineOpen W ∧
      (γ[G, X]).left.base '' ((snd G X).left.base ⁻¹' {u}) ⊆ (W : Set X.left) :=
  hfib (X.hom.base u) _ (finite_actionOrbit G X u) <| by
    rintro x ⟨r, hr, rfl⟩
    rw [hom_base_act_eq G X r]
    exact congrArg X.hom.base hr

/-- A free action of a finite locally free group scheme all of whose orbits lie in affine opens
has a finite flat quotient. -/
private theorem nonempty_finiteFlatQuotient_of_forall_orbit [IsFiniteLocallyFree G.hom]
    (hfree : IsFreeAction G X)
    (horb : ∀ u : X.left, ∃ W : X.left.Opens, IsAffineOpen W ∧
      (γ[G, X]).left.base '' ((snd G X).left.base ⁻¹' {u}) ⊆ (W : Set X.left)) :
    Nonempty (FiniteFlatQuotient (actionGroupoid (Over.mk (𝟙 S)) G X)) := by
  have := jointlyMono₂_actionGroupoid G X hfree
  have := (actionGroupoid (Over.mk (𝟙 S)) G X).isEquivalenceRelation
  refine AlgebraicGeometry.Space.nonempty_finiteFlatQuotient_of_affineOrbits _ fun Z _ hZne => ?_
  obtain ⟨u, hu⟩ := hZne
  obtain ⟨W, hW, hWsub⟩ := horb u
  exact ⟨u, hu, W, hW, hWsub⟩

/-- The fppf quotient sheaf of a free action of a finite locally free group scheme on a scheme
whose fibrewise finite sets of points lie in affine opens is a scheme: the action groupoid has a
finite flat quotient, so `X/G` is represented by a scheme `M` over `S` with `X ⟶ M` surjective
and finite locally free and with kernel pair `G ×_S X`. -/
@[sga "3 IX 2.3" "2.3(a)",
  sga "3 V 4.1" "special case",
  sga "3 XVI 1.1" "more general",
  sga "3 XXV 4.2" "special case"]
theorem nonempty_finiteFlatQuotient_actionGroupoid [IsFiniteLocallyFree G.hom]
    (hfree : IsFreeAction G X) (hfib : HasAffineFinitePointsInFibres X.hom) :
    Nonempty (FiniteFlatQuotient (actionGroupoid (Over.mk (𝟙 S)) G X)) :=
  nonempty_finiteFlatQuotient_of_forall_orbit G X hfree
    (exists_isAffineOpen_orbit_subset G X hfib)

/-- When `G ⟶ S` is radicial the orbit of a point of `X` is that point alone. -/
theorem orbit_subset_singleton_of_universallyInjective [UniversallyInjective G.hom]
    (u : X.left) :
    (γ[G, X]).left.base '' ((snd G X).left.base ⁻¹' {u}) ⊆ {u} := by
  have hbc : UniversallyInjective (snd G X).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback G.hom X.hom) inferInstance
  have hinj : Function.Injective (snd G X).left.base := Scheme.Hom.injective (snd G X).left
  have hse : (snd G X).left.base ((actionGroupoid (Over.mk (𝟙 S)) G X).identity.left.base u) =
      u :=
    congrArg (fun k => k.base u) (Stacks.Groupoids.identity_left_comp_source_left
      (actionGroupoid (Over.mk (𝟙 S)) G X))
  have hte : (γ[G, X]).left.base ((actionGroupoid (Over.mk (𝟙 S)) G X).identity.left.base u) =
      u :=
    congrArg (fun k => k.base u) (Stacks.Groupoids.identity_left_comp_target_left
      (actionGroupoid (Over.mk (𝟙 S)) G X))
  rintro x ⟨r, hr, rfl⟩
  rw [hinj (hr.trans hse.symm)]
  exact hte

/-- When `G ⟶ S` is radicial every orbit of the action lies in an affine open of `X`. -/
theorem exists_isAffineOpen_orbit_subset_of_universallyInjective [UniversallyInjective G.hom]
    (u : X.left) :
    ∃ W : X.left.Opens, IsAffineOpen W ∧
      (γ[G, X]).left.base '' ((snd G X).left.base ⁻¹' {u}) ⊆ (W : Set X.left) := by
  obtain ⟨W, hW, huW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ u)
  exact ⟨W, hW, (orbit_subset_singleton_of_universallyInjective G X u).trans
    (Set.singleton_subset_iff.mpr huW)⟩

/-- A free action of a finite locally free radicial group scheme has a finite flat quotient. -/
@[sga "3 IX 2.3" "2.3(a)", sga "3 V 4.1" "special case"]
theorem nonempty_finiteFlatQuotient_actionGroupoid_of_universallyInjective
    [IsFiniteLocallyFree G.hom] [UniversallyInjective G.hom] (hfree : IsFreeAction G X) :
    Nonempty (FiniteFlatQuotient (actionGroupoid (Over.mk (𝟙 S)) G X)) :=
  nonempty_finiteFlatQuotient_of_forall_orbit G X hfree
    (exists_isAffineOpen_orbit_subset_of_universallyInjective G X)

/-- Let `S` be a scheme, `G ⟶ S` a group scheme, `X ⟶ S` a
morphism of schemes and `a : G ×_S X ⟶ X` an action. Assume that `G ⟶ S` is finite locally
free, that the action is free, and that `X ⟶ S` is affine, or quasi-affine, or projective, or
quasi-projective, or `X` admits an immersion into an affine scheme, or an immersion into
`Proj A` for a graded ring `A`, or `G ⟶ S` is radicial. Then the fppf quotient sheaf `X/G` is a
scheme: the action groupoid has a finite flat quotient, so there is a scheme `M` over `S`
representing `X/G` on every big fppf site, with `X ⟶ M` surjective and finite locally free and
with kernel pair `G ×_S X`. -/
@[stacks 07S7 "the quotient sheaf is a scheme; all seven alternatives of condition (3)",
  sga "3 IX 2.3" "2.3(a)",
  sga "3 V 4.1" "special case",
  sga "3 V 9.0" "partial",
  sga "3 VIB 9.3" "Case 2° of Remark 9.3 b)",
  sga "3 XVI 1.1" "more general",
  sga "3 XXV 4.2" "special case"]
theorem nonempty_finiteFlatQuotient_actionGroupoid_of_geometry [IsFiniteLocallyFree G.hom]
    (hfree : IsFreeAction G X)
    (hgeom : IsAffineHom X.hom ∨ IsQuasiAffineHom X.hom ∨ IsProjective X.hom ∨
      IsQuasiProjective X.hom ∨ HasImmersionToAffine X.left ∨ HasImmersionToProj X.left ∨
      UniversallyInjective G.hom) :
    Nonempty (FiniteFlatQuotient (actionGroupoid (Over.mk (𝟙 S)) G X)) := by
  have key : HasAffineFinitePointsInFibres X.hom ∨ UniversallyInjective G.hom := by
    rcases hgeom with h | h | h | h | h | h | h
    · exact .inl (hasAffineFinitePointsInFibres_of_isAffineHom X.hom)
    · exact .inl (hasAffineFinitePointsInFibres_of_isQuasiAffineHom X.hom)
    · exact .inl (hasAffineFinitePointsInFibres_of_isProjective X.hom h)
    · exact .inl (hasAffineFinitePointsInFibres_of_isQuasiProjective X.hom h)
    · exact .inl (hasAffineFinitePointsInFibres_of_hasImmersionToAffine X.hom h)
    · exact .inl (hasAffineFinitePointsInFibres_of_hasImmersionToProj X.hom h)
    · exact .inr h
  exact key.elim (nonempty_finiteFlatQuotient_actionGroupoid G X hfree)
    (fun _ => nonempty_finiteFlatQuotient_actionGroupoid_of_universallyInjective G X hfree)

/-- For a finite flat quotient `M = X/G` of the action groupoid, the morphism
`G ×_S X ⟶ X ×_M X` sending `(g, x)` to `(g · x, x)` is an isomorphism, and `X ⟶ M` is itself an
fppf covering of `M` over which `X ⟶ M` has a section, namely the diagonal. These are the two
conditions for `X ⟶ X/G` to be an fppf `G`-torsor. -/
@[stacks 07S7 "the fppf torsor clause: shear isomorphism and fppf-local sections"]
theorem isFppfTorsor_quotientMap [IsFiniteLocallyFree G.hom]
    (Q : FiniteFlatQuotient (actionGroupoid (Over.mk (𝟙 S)) G X)) :
    (∃ e : (G ⊗ X).left ≅ pullback Q.quotientMap.left Q.quotientMap.left,
        e.hom ≫ pullback.fst Q.quotientMap.left Q.quotientMap.left = (γ[G, X]).left ∧
          e.hom ≫ pullback.snd Q.quotientMap.left Q.quotientMap.left = (snd G X).left) ∧
      Presieve.singleton Q.quotientMap.left ∈ Scheme.fppfPrecoverage Q.space.left ∧
      ∃ s : X.left ⟶ pullback Q.quotientMap.left Q.quotientMap.left,
        s ≫ pullback.fst Q.quotientMap.left Q.quotientMap.left = 𝟙 X.left := by
  obtain ⟨-, hflat, hlfp⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Q.quotientMap.left).mp Q.finiteLocallyFree
  refine ⟨⟨Q.isPullback_left.isoPullback, Q.isPullback_left.isoPullback_hom_fst,
    Q.isPullback_left.isoPullback_hom_snd⟩, ?_,
    pullback.lift (𝟙 X.left) (𝟙 X.left) rfl, pullback.lift_fst _ _ _⟩
  exact (Scheme.singleton_mem_precoverage_iff (@Flat ⊓ @LocallyOfFinitePresentation)
    Q.quotientMap.left).mpr ⟨(surjective_iff _).mp Q.surjective, hflat, hlfp⟩

end AlgebraicGeometry

end
