module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import StacksCore.CategoryTheory.Sites.Cocontinuous.CocontinuousDefs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# The small étale topos inside a big étale topos (Stacks 0DF2)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism
of its objects. An algebraic space étale over `Y` becomes an object of the big étale site of
`X` by composing its structure morphism with `f`. This inclusion functor is both continuous
and cocontinuous, so it induces a morphism of topoi from the spaces-étale topos of `Y` to the
big étale topos of `X`, whose inverse image is restriction of sheaves along the inclusion and
which has a further left adjoint preserving fibre products and equalizers.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.inclusionFunctor` is composition of an étale object
  over `Y` with `f`: **Stacks 0DF2**.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBigEtaleMorphism` is the induced morphism of
  topoi and `AlgebraicGeometry.BigEtaleSpaceSite.lowerShriek` the left adjoint of its inverse
  image.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.inclusionFunctor_isCocontinuous` and
  `AlgebraicGeometry.BigEtaleSpaceSite.inclusionFunctor_isContinuous`.
* `AlgebraicGeometry.BigEtaleSpaceSite.lowerShriek_preservesPullbacks` and
  `AlgebraicGeometry.BigEtaleSpaceSite.lowerShriek_preservesEqualizers`.
* `CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj` is the inverse-image
  formula: the sections of the restriction of a big sheaf over `U/Y` are its sections over
  `U/X`.

## Implementation notes

The small site is the full subcategory of the slice over `Y` on the étale objects, which is
`(AlgebraicGeometry.Space.etaleMorphisms B S hS).overObj`; stating it that way makes the
finite limits of the small site and their preservation by the inclusion instances of the
general `CategoryTheory.MorphismProperty` API, once étaleness is known to be multiplicative
(Tag 03FT), stable under base change (Tag 03FU) and to have the cancellation property
(Tag 03FV).

Cocontinuity is proved in two steps: the inclusion of the small site into the slice over `Y`
is cocontinuous, and composition with `f` is cocontinuous for the localized topologies by
`CategoryTheory.map_isCocontinuous`. The first step is the lifting statement
`AlgebraicGeometry.BigEtaleSpaceSite.smallEtale_lifts_covering_sieve`: a covering sieve of
the big site, pulled back to an étale object `A` over `Y`, contains a jointly point-surjective
étale family on `A`. It is proved by induction on the generation of the covering sieve; in the
base case the covering family is base changed to `A` using the base change axiom of the big
site, each base change is étale over `Y` by Tag 03FT, and a point of `A` is lifted by joint
surjectivity of the base-changed family.

Continuity is `CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`
applied to the point-surjective precoverage of the small site. Its hypotheses are that the
precoverage is stable under base change — which is Tag 03H4, lifting a pair of compatible
points to the fibre product — and that the image of a small covering family generates a
covering sieve of the big site, which is
`AlgebraicGeometry.BigEtaleSpaceSite.smallEtale_generator_sieve_covering`: the image family is
an étale covering of algebraic spaces in the sense of Tag 041E, so the big site contains a
combinatorially equivalent chosen representative and the two present the same presieve.

## References

* [Stacks Project, Tag 0DF2](https://stacks.math.columbia.edu/tag/0DF2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X)

/-! ### The inclusion functor and its continuity -/

/-- **Stacks 0DF2.** Composition with `f` regards an algebraic space étale over `Y` as an
object of the big étale site of `X`. -/
@[stacks 0DF2 "the inclusion functor"]
abbrev inclusionFunctor :
    Space.SpacesEtale T.fppfSite S T.fppf_mem Y ⥤ Over X :=
  Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y ⋙ Over.map f

/-- A covering sieve of the big étale site of algebraic spaces, pulled back to an algebraic
space étale over `Y`, is refined by a jointly point-surjective étale family, hence covers in
the spaces-étale site of `Y`. -/
theorem smallEtale_lifts_covering_sieve
    (A : Space.SpacesEtale T.fppfSite S T.fppf_mem Y)
    {W : T.Spaces}
    (g : (Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y).obj A ⟶ W)
    {R : Sieve W} (hR : R ∈ T.topology W) :
    (R.pullback g).functorPullback
      (Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y) ∈
        Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y A := by
  induction hR generalizing A with
  | of W Q hQ =>
    classical
    let G := Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y
    obtain ⟨E, hQE, hE⟩ := T.mem_precoverage_iff.mp hQ
    obtain ⟨P, p₁, p₂, hpb, hP⟩ := T.isSite.2.2 ⟨W, E⟩ hE (G.obj A) g
    have hsurj (x : Space.points T.fppfSite S T.fppf_mem (G.obj A).1) :
        ∃ z : Σ i, Space.points T.fppfSite S T.fppf_mem (P i).1,
          Space.pointsMap T.fppfSite S T.fppf_mem (P z.1).1 (p₂ z.1).hom z.2 = x := by
      have hx : x ∈ ⋃ i, Set.range
          (Space.pointsMap T.fppfSite S T.fppf_mem (P i).1 (p₂ i).hom) := by
        rw [hP.1.jointly_surjective]; exact Set.mem_univ x
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy⟩ := Set.mem_range.mp hx
      exact ⟨⟨i, y⟩, hy⟩
    let lift (x : Space.points T.fppfSite S T.fppf_mem (G.obj A).1) :=
      Classical.choose (hsurj x)
    have hlift (x : Space.points T.fppfSite S T.fppf_mem (G.obj A).1) :=
      Classical.choose_spec (hsurj x)
    let F : PreZeroHypercover.{u + 1} A :=
      ⟨Space.points T.fppfSite S T.fppf_mem (G.obj A).1,
        fun x ↦ ⟨Over.mk (p₂ (lift x).1 ≫ A.1.hom),
          Space.isEtale_comp T.fppfSite S T.fppf_mem (hP.1.etale (lift x).1) A.property⟩,
        fun x ↦ ObjectProperty.homMk (Over.homMk (p₂ (lift x).1) (by simp))⟩
    have hF : Space.SpacesEtale.IsCovering T.fppfSite S T.fppf_mem Y ⟨A, F⟩ :=
      fun x ↦ ⟨x, (lift x).2, by simpa [F, lift, G] using hlift x⟩
    have hFpre : F.presieve₀ ∈
        Space.SpacesEtale.precoverage T.fppfSite S T.fppf_mem Y A := by
      rw [Space.SpacesEtale.mem_precoverage_iff]; exact ⟨F, rfl, hF⟩
    apply (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y).superset_covering
      ?_ (Precoverage.generate_mem_toGrothendieck hFpre)
    rw [Sieve.generate_le_iff]
    intro Z a ha
    obtain ⟨i⟩ := ha
    show (Sieve.generate Q) (p₂ (lift i).1 ≫ g)
    rw [(hpb (lift i).1).w.symm]
    exact (Sieve.generate Q).downward_closed
      (Sieve.le_generate Q (E.X (lift i).1) (E.f (lift i).1)
        (by rw [hQE]; exact E.presieve₀_f (lift i).1)) _
  | top W =>
    rw [Sieve.pullback_top, Sieve.functorPullback_top]
    exact (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y).top_mem A
  | pullback W R hR V f ih =>
    simpa only [Sieve.pullback_comp, Category.assoc] using ih A (g ≫ f)
  | transitive W R Q hR hQ ihR ihQ =>
    let G := Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y
    let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y
    apply J.transitive (ihR A g) ((Q.pullback g).functorPullback G)
    intro C a ha
    have hk : R (G.map a ≫ g) := by simpa [G, Sieve.functorPullback] using ha
    have hrec' : Sieve.functorPullback G
        (Sieve.pullback (G.map a) (Sieve.pullback g Q)) ∈ J C := by
      simpa only [Sieve.pullback_id, Sieve.pullback_comp] using
        ihQ (f := G.map a ≫ g) hk C (𝟙 (G.obj C))
    rwa [Sieve.functorPullback_pullback] at hrec'

/-- The image under the inclusion into algebraic spaces of a jointly point-surjective étale
family of the spaces-étale site of `Y` generates a covering sieve of the big étale site of
algebraic spaces. -/
theorem smallEtale_generator_sieve_covering
    (A : Space.SpacesEtale T.fppfSite S T.fppf_mem Y)
    (F : PreZeroHypercover.{u + 1} A)
    (hF : Space.SpacesEtale.IsCovering T.fppfSite S T.fppf_mem Y ⟨A, F⟩) :
    Sieve.generate
        ((F.map (Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y)).presieve₀) ∈
      T.topology ((Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y).obj A) := by
  let G := Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y
  let E : Covering.{u + 1, u + 1, u + 2} T.Spaces :=
    ⟨G.obj A, { I₀ := ULift.{u + 2, u + 1} F.I₀
                X := fun i ↦ G.obj (F.X i.down)
                f := fun i ↦ G.map (F.f i.down) }⟩
  have hE : Space.IsEtaleCoveringFamily T.fppfSite S T.fppf_mem E := by
    refine ⟨(G.obj A).property, fun i ↦ (G.obj (F.X i.down)).property, fun i ↦ ?_, ?_⟩
    · exact Space.isEtale_of_isEtale_over T.fppfSite S T.fppf_mem
        (G.obj (F.X i.down)).property (G.obj A).property Y.property
        (G.map (F.f i.down)).hom ((F.X i.down).1.hom).hom A.1.hom.hom
        (F.X i.down).property A.property
        (congrArg (fun k ↦ k.hom) (Over.w (F.f i.down).hom))
    · ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      obtain ⟨i, y, hy⟩ := hF x
      exact ⟨ULift.up i, y, by simpa [E, G] using hy⟩
  obtain ⟨E', hE', hEquiv⟩ := T.covering_representative E hE
  obtain ⟨Z, E'fam⟩ := E'
  obtain ⟨hTarget, hComb⟩ := hEquiv
  cases hTarget
  have hE'cover : Sieve.generate E'fam.presieve₀ ∈ T.topology (G.obj A) :=
    Precoverage.generate_mem_toGrothendieck (by rw [T.mem_precoverage_iff]; exact ⟨E'fam, rfl, hE'⟩)
  rw [← PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hComb] at hE'cover
  have hEcover : Sieve.generate E.2.presieve₀ ∈ T.topology E.1 := by simpa using hE'cover
  have hLift : PreZeroHypercover.CombinatoriallyEquivalent (F.map G) E.2 :=
    ⟨⟨fun i ↦ ULift.up i, fun _ ↦ rfl, fun _ ↦ rfl⟩, ⟨fun i ↦ i.down, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩
  rw [← PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hLift] at hEcover
  simpa [E, G, Space.SpacesEtale.toSpaces, Space.SpacesEtale.inclusion] using hEcover

private theorem generate_functorPushforward_eq_generate_map
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {Z : C} (R : Presieve Z) :
    Sieve.generate (Presieve.functorPushforward F R) = Sieve.generate (R.map F) := by
  rw [← Sieve.arrows_generate_map_eq_functorPushforward]; exact Sieve.generate_sieve _

/-- The inclusion of the spaces-étale site of `Y` into the big étale site of `Y` is
cocontinuous. -/
instance spacesEtale_inclusion_isCocontinuous :
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y).IsCocontinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.topology.over Y) := by
  constructor
  intro A R hR
  rw [GrothendieckTopology.mem_over_iff] at hR
  let G := Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y
  let I := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y
  let R' := Sieve.overEquiv A.1 R
  have hle : R'.functorPullback G ≤ R.functorPullback I := by
    intro C a ha
    change R' (G.map a) at ha
    change R (I.map a)
    have h := (Sieve.overEquiv_iff R (G.map a)).mp ha
    let g : Over.mk (G.map a ≫ A.1.hom) ⟶ A.1 := Over.homMk (G.map a)
    let hk : C.1 ⟶ Over.mk (G.map a ≫ A.1.hom) :=
      Over.homMk (𝟙 C.1.left) (by
        simp only [Category.id_comp]
        exact Over.w a.hom)
    have hmap : hk ≫ g = I.map a := by
      apply Over.OverMorphism.ext
      simp [hk, g, I, G, Space.SpacesEtale.inclusion, Space.SpacesEtale.toSpaces]
    rw [← hmap]
    exact R.downward_closed h hk
  apply (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y).superset_covering hle
  simpa [R', G, Sieve.pullback_id] using
    smallEtale_lifts_covering_sieve (T := T) A (𝟙 (G.obj A)) hR

/-- The inclusion of the spaces-étale site into the big étale site preserves pullbacks. -/
public instance inclusionFunctor_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (inclusionFunctor T f) :=
  comp_preservesLimitsOfShape
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y) (Over.map f)

/-- The inclusion of the spaces-étale site into the big étale site preserves equalizers. -/
public noncomputable instance inclusionFunctor_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (inclusionFunctor T f) :=
  comp_preservesLimitsOfShape
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y) (Over.map f)

/-- **Stacks 0DF2.** The inclusion of the spaces-étale site of `Y` into the big étale site of
`X` is cocontinuous. -/
@[stacks 0DF2 "cocontinuity"]
instance inclusionFunctor_isCocontinuous :
    (inclusionFunctor T f).IsCocontinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X) :=
  isCocontinuous_comp (G := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y)
    (G' := Over.map f)
    (J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (K := T.topology.over Y) (L := T.topology.over X)

/-- **Stacks 0DF2.** The inclusion of the spaces-étale site of `Y` into the big étale site of
`X` is continuous: it carries jointly point-surjective étale families and their base changes
to covering families and base changes. -/
instance inclusionFunctor_isContinuous :
    (inclusionFunctor T f).IsContinuous
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X) := by
  let J := Space.SpacesEtale.precoverage T.fppfSite S T.fppf_mem Y
  let K := (T.topology.over X).toPrecoverage
  let G := Space.SpacesEtale.toSpaces T.fppfSite S T.fppf_mem Y
  have _ : J.IsStableUnderBaseChange := by
    dsimp [J]
    constructor
    intro ι A Z f hf V g P p₁ p₂ h
    rw [Space.SpacesEtale.mem_precoverage_iff] at hf
    obtain ⟨E, hRE, hE⟩ := hf
    rw [Space.SpacesEtale.mem_precoverage_iff]
    refine ⟨⟨ι, P, p₁⟩, rfl, ?_⟩
    intro x
    obtain ⟨j, y, hy⟩ := hE (Space.pointsMap T.fppfSite S T.fppf_mem
      (G.obj V).1 (G.map g).hom x)
    obtain ⟨i, hobj, hfac⟩ := Presieve.ofArrows_surj f (E.f j) (by
      rw [hRE]; exact E.presieve₀_f j)
    have hcompat : Space.pointsMap T.fppfSite S T.fppf_mem
          (G.obj (Z i)).1 ((G.map (f i)).hom)
          (Space.pointsMap T.fppfSite S T.fppf_mem (G.obj (E.X j)).1
            ((G.map (eqToHom hobj.symm)).hom) y) =
        Space.pointsMap T.fppfSite S T.fppf_mem (G.obj V).1 (G.map g).hom x := by
      change (Space.pointsMap T.fppfSite S T.fppf_mem (G.obj (Z i)).1 ((G.map (f i)).hom) ∘
        Space.pointsMap T.fppfSite S T.fppf_mem (G.obj (E.X j)).1
          ((G.map (eqToHom hobj.symm)).hom)) y = _
      rw [← Space.pointsMap_comp]
      have hmapcomp : (G.map (eqToHom hobj.symm)).hom ≫ (G.map (f i)).hom =
          (G.map (eqToHom hobj.symm ≫ f i)).hom := by
        simp
      rw [hmapcomp, ← hfac]
      exact hy
    obtain ⟨w, hw₁, -⟩ := Space.exists_point_of_isPullback T.fppfSite S T.fppf_mem
      ((h i).map G) x _ hcompat.symm
    exact ⟨i, w, hw₁⟩
  have hle : J ≤ K.comap (inclusionFunctor T f) := by
    intro A R hR
    rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff]
    rw [Space.SpacesEtale.mem_precoverage_iff] at hR
    obtain ⟨F, rfl, hF⟩ := hR
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    have hEq : Sieve.generate (Presieve.functorPushforward (Over.forget X)
        ((F.map (inclusionFunctor T f)).presieve₀)) =
        Sieve.generate ((F.map G).presieve₀) := by
      rw [PreZeroHypercover.presieve₀_map, generate_functorPushforward_eq_generate_map,
        PreZeroHypercover.presieve₀_map]
      simp [G, inclusionFunctor, Space.SpacesEtale.toSpaces,
        Space.SpacesEtale.inclusion]
    rw [← PreZeroHypercover.presieve₀_map, hEq]
    exact smallEtale_generator_sieve_covering (T := T) A F hF
  have hcont := Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
    (F := inclusionFunctor T f) (J := J) (K := K) hle
  have hK : K.toGrothendieck ≤ T.bigEtaleTopology X :=
    GrothendieckTopology.toGrothendieck_toPrecoverage_le _
  exact ⟨fun G ↦ hcont.op_comp_isSheaf_of_types ⟨G.1, Presheaf.IsSheaf.of_le hK G.2⟩⟩

/-! ### The morphism of topoi -/

/-- **Stacks 0DF2.** The morphism of topoi from the spaces-étale topos of `Y` to the big
étale topos of `X` induced by the inclusion functor. Its inverse image is restriction of
sheaves along the inclusion, so its sections are computed by
`CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj`. -/
@[stacks 0DF2 "the morphism of topoi"]
noncomputable def smallToBigEtaleMorphism :
    MorphismOfTopoi
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1)))
      (Sheaf (T.bigEtaleTopology X) (Type (u + 1))) where
  pushforward := (inclusionFunctor T f).sheafPushforwardCocontinuous (Type (u + 1))
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)
  inverseImage := (inclusionFunctor T f).sheafPushforwardContinuous (Type (u + 1))
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)
  adj := (inclusionFunctor T f).sheafAdjunctionCocontinuous (Type (u + 1))
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)
  preservesFiniteLimits := inferInstance

add_to_stacks 0DF2 "the inverse-image formula"
  CategoryTheory.Functor.sheafPushforwardContinuous_obj_obj_obj
add_to_stacks 0DF2 "existence of lower shriek"
  CategoryTheory.Functor.sheafAdjunctionContinuous

/-- **Stacks 0DF2.** The left adjoint of restriction along the inclusion functor. -/
@[stacks 0DF2 "the lower-shriek functor"]
noncomputable abbrev lowerShriek :
    Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1)) ⥤
      Sheaf (T.bigEtaleTopology X) (Type (u + 1)) :=
  (inclusionFunctor T f).sheafPullback (Type (u + 1))
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)

/-- **Stacks 0DF2.** Lower shriek preserves fibre products. -/
@[stacks 0DF2 "lower shriek preserves fibre products"]
noncomputable instance lowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (lowerShriek T f) :=
  Functor.preservesLimitsOfShape_sheafPullback (inclusionFunctor T f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)
    (I := WalkingCospan)

/-- **Stacks 0DF2.** Lower shriek preserves equalizers. -/
@[stacks 0DF2 "lower shriek preserves equalizers"]
noncomputable instance lowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek T f) :=
  Functor.preservesLimitsOfShape_sheafPullback (inclusionFunctor T f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)
    (I := WalkingParallelPair)

end AlgebraicGeometry.BigEtaleSpaceSite

end
