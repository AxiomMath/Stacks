module

public import StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartNoetherianSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticDensity

/-!
# Stacks 0CPC: flat morphisms of finite presentation between image systems

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms (Situation 0CP6,
`AlgebraicGeometry.Space.NoetherianLimitSystem`), let `f : X ⟶ Y` be a morphism of algebraic
spaces quasi-separated over `B`, let `X = lim X_i` and `Y = lim Y_i` be the limit descriptions
by scheme-theoretic images attached to two diagrams as in Stacks 0CP8 (Stacks 0CP9), and let
`(f_i)_{i ≥ i₀}` be a morphism of these inverse systems with limit `f` (Stacks 0CPA). Stacks
0CPC asserts that if `f` is flat and of finite presentation, then for all sufficiently large
`i₃` the morphism `f_{i₃}` is flat, `X = Y ×_{Y_{i₃}} X_{i₃}`, and `X_i = Y_i ×_{Y_{i₃}} X_{i₃}`
for every `i ≥ i₃`.

The proof is that of the source. By Stacks 07SK the morphism `f` is the base change of a
morphism `u : U ⟶ Y_n` of finite presentation along `Y ⟶ Y_n`, and by Stacks 08K0 the stage
`n` can be chosen so that `u` is flat. The base changes `U_l = Y_l ×_{Y_n} U` then form a second
inverse system with limit `X`, and the image system of `X` is eventually isomorphic to it over
the system `(Y_l)`: the morphism `X ⟶ U` is defined over a stage `X_p`, giving `X_l ⟶ U_l`,
and the morphism `X ⟶ X_p` is defined over a stage `U_l`, giving `U_l ⟶ B_l ×_{B_{i₁}} W`,
which factors through the scheme-theoretic image `X_l` because `X ⟶ U_l` is
scheme-theoretically dense: it is the base change of `Y ⟶ Y_l`, whose image is all of `Y_l`,
along the flat morphism `U_l ⟶ Y_l` (Stacks 089E). The two composites are identities at all
sufficiently late stages by the injectivity half of Stacks 0CP4. For the system `(U_l)` the three
assertions hold on the nose.

Where the source replaces the diagram for `X` by the one coming from `X ⟶ U ⟶ B_n` and then
compares the two image systems (Remark 0CPB), the comparison here is made directly between the
image system of the given diagram and the system of base changes `U_l`.

## Main results

* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_isFlat_isPullback` is
  **Stacks 0CPC**.
* `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.exists_flat_model`: a flat morphism of
  finite presentation is the base change of a flat morphism of finite presentation over a stage
  of the image system of its target.
* `AlgebraicGeometry.Space.GoodDiagram.isLimit_tailCone`: the image system restricted to the
  stages above a later stage still has the limit `X`.
* `AlgebraicGeometry.Space.isLimitBaseChangeCone`: the base change of a cofiltered limit cone of
  algebraic spaces to a stage is a limit cone of the system of base changes.

## Implementation notes

The index type is small for the site, `#I < B.cutoff.ord.cof`, as in the library's forms of
Stacks 0CP9 and 0CPA: it is the condition under which the limits of the affine charts of the
system lie in the big fppf site, so that `X` is the limit of its image system.

The conclusion is stated for every stage `k ≥ i₃` rather than for one stage `i₃ > i₀`; this is
the source's assertion for each such `k`, and it is what makes the statement non-vacuous when
`i₀` is a largest index.

## References

* [Stacks Project, Tag 0CPC](https://stacks.math.columbia.edu/tag/0CPC)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0CPA](https://stacks.math.columbia.edu/tag/0CPA)
* [Stacks Project, Tag 0CPB](https://stacks.math.columbia.edu/tag/0CPB)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/-! ### Flatness and finite presentation of isomorphisms -/

/-- An isomorphism of algebraic spaces over `S` is flat: it is a base change of an identity. -/
theorem isFlat_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G) [IsIso e]
    (algG : IsAlgebraicSpace B S hS G) : IsFlat B S hS e :=
  isFlat_of_isPullback_of_isAlgebraicSpace B S hS
    (IsPullback.of_horiz_isIso (fst := e) (snd := e) (f := 𝟙 G) (g := 𝟙 G) ⟨by simp⟩)
    algG algG (isFlat_id B S hS algG)

/-- Composing a morphism of finite presentation with an isomorphism keeps it of finite
presentation: the composite is a base change of the original morphism. -/
theorem isFinitePresentation_comp_iso {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (algF : IsAlgebraicSpace B S hS F) (algG : IsAlgebraicSpace B S hS G)
    (algG' : IsAlgebraicSpace B S hS G') (f : F ⟶ G) (e : G ≅ G')
    (fp : IsFinitePresentation B S hS f) : IsFinitePresentation B S hS (f ≫ e.hom) :=
  isFinitePresentation_of_isPullback B S hS algF algF algG' algG
    (IsPullback.of_horiz_isIso (fst := 𝟙 F) (snd := f ≫ e.hom) (f := f) (g := e.inv)
      ⟨by simp⟩) fp

/-! ### The base change of a system to a stage -/

section BaseChangeSystem

variable {J : Type u} [Category.{u} J] (Ys : J ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (m : J)
  {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (u : U ⟶ Ys.obj m)

/-- The base changes `Y_l ×_{Y_m} U` of a morphism `u : U ⟶ Y_m` to the stages `l` over `m` of
an inverse system `(Y_l)`. -/
noncomputable abbrev baseChangeSystem : Over m ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  obj l := pullback (Ys.map l.hom) u
  map {l l'} a := pullback.lift (pullback.fst _ _ ≫ Ys.map a.left) (pullback.snd _ _) (by
    rw [Category.assoc, ← Ys.map_comp, Over.w a, pullback.condition])
  map_id l := pullback.hom_ext (by simp) (by simp)
  map_comp a b := pullback.hom_ext (by simp) (by simp)

/-- The cone on the system of base changes whose vertex is the base change `Y ×_{Y_m} U` to the
vertex of a cone on the system. -/
noncomputable abbrev baseChangeCone (c : Cone Ys) : Cone (baseChangeSystem Ys m u) where
  pt := pullback (c.π.app m) u
  π :=
    { app l := pullback.lift (pullback.fst _ _ ≫ c.π.app l.left) (pullback.snd _ _) (by
        rw [Category.assoc, c.w l.hom, pullback.condition])
      naturality l l' a := pullback.hom_ext (by simp [c.w]) (by simp) }

/-- A fibre product commutes with a cofiltered limit: the base change of a limit cone of the
system to `U` is a limit cone of the system of base changes. -/
noncomputable def isLimitBaseChangeCone [IsCofilteredOrEmpty J] {c : Cone Ys} (hc : IsLimit c) :
    IsLimit (baseChangeCone Ys m u c) :=
  isLimitOfPreserves (Over.pullback u ⋙ Over.forget U) (Over.isLimitConePost m hc)

/-- A transition morphism of the system of base changes commutes with the projections to the
stages `Y_l`. -/
@[reassoc (attr := simp)]
lemma baseChangeSystem_map_fst {l l' : Over m} (a : l ⟶ l') :
    (baseChangeSystem Ys m u).map a ≫ pullback.fst (Ys.map l'.hom) u =
      pullback.fst (Ys.map l.hom) u ≫ Ys.map a.left :=
  pullback.lift_fst _ _ _

/-- A transition morphism of the system of base changes commutes with the projections to `U`. -/
@[reassoc (attr := simp)]
lemma baseChangeSystem_map_snd {l l' : Over m} (a : l ⟶ l') :
    (baseChangeSystem Ys m u).map a ≫ pullback.snd (Ys.map l'.hom) u =
      pullback.snd (Ys.map l.hom) u :=
  pullback.lift_snd _ _ _

/-- A leg `Y ×_{Y_m} U ⟶ Y_l ×_{Y_m} U` of the base-changed cone, followed by the projection to
`Y_l`, is the projection to `Y` followed by the leg `Y ⟶ Y_l`. -/
@[reassoc (attr := simp)]
lemma baseChangeCone_π_fst (c : Cone Ys) (l : Over m) :
    (baseChangeCone Ys m u c).π.app l ≫ pullback.fst (Ys.map l.hom) u =
      pullback.fst (c.π.app m) u ≫ c.π.app l.left :=
  pullback.lift_fst _ _ _

/-- A leg of the base-changed cone commutes with the projections to `U`. -/
@[reassoc (attr := simp)]
lemma baseChangeCone_π_snd (c : Cone Ys) (l : Over m) :
    (baseChangeCone Ys m u c).π.app l ≫ pullback.snd (Ys.map l.hom) u =
      pullback.snd (c.π.app m) u :=
  pullback.lift_snd _ _ _

/-- A transition morphism of the system of base changes is the base change of the
corresponding transition morphism of the system. -/
lemma isPullback_baseChangeSystem_map {l l' : Over m} (a : l ⟶ l') :
    IsPullback ((baseChangeSystem Ys m u).map a) (pullback.fst (Ys.map l.hom) u)
      (pullback.fst (Ys.map l'.hom) u) (Ys.map a.left) := by
  refine IsPullback.of_right ?_ (baseChangeSystem_map_fst Ys m u a)
    (IsPullback.of_hasPullback (Ys.map l'.hom) u).flip
  have hcomp : Ys.map a.left ≫ Ys.map l'.hom = Ys.map l.hom := by
    rw [← Ys.map_comp, Over.w a]
  rw [baseChangeSystem_map_snd, hcomp]
  exact (IsPullback.of_hasPullback (Ys.map l.hom) u).flip

/-- The square formed by a leg of the base-changed cone, the base change of the corresponding leg
of the original cone, and the two projections to the stages is cartesian. -/
lemma isPullback_baseChangeCone_π (c : Cone Ys) (l : Over m) :
    IsPullback ((baseChangeCone Ys m u c).π.app l) (pullback.fst (c.π.app m) u)
      (pullback.fst (Ys.map l.hom) u) (c.π.app l.left) := by
  refine IsPullback.of_right ?_ (baseChangeCone_π_fst Ys m u c l)
    (IsPullback.of_hasPullback (Ys.map l.hom) u).flip
  rw [baseChangeCone_π_snd, c.w l.hom]
  exact (IsPullback.of_hasPullback (c.π.app m) u).flip

end BaseChangeSystem

/-- The morphism types of a slice of `Over (op i₀)` are below the cofinality of the cutoff. -/
private theorem cardinal_mk_hom_over_slice_lt {I : Type u} [Preorder I] {i₀ : I}
    (n : Over (op i₀)) (l l' : Over n) : Cardinal.mk (l ⟶ l') < B.cutoff.ord.cof :=
  (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans_lt
    (Cardinal.one_lt_aleph0.trans B.aleph0_lt_cutoff_cof)

/-- The projection of a base change of a morphism of finite presentation, along the other
morphism, is of finite presentation. -/
private theorem isFinitePresentation_fst_pullback {A C U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (algA : IsAlgebraicSpace B S hS A) (algC : IsAlgebraicSpace B S hS C)
    (algU : IsAlgebraicSpace B S hS U) (g : A ⟶ C) (u : U ⟶ C)
    (fp : IsFinitePresentation B S hS u) : IsFinitePresentation B S hS (pullback.fst g u) :=
  isFinitePresentation_of_isPullback B S hS (isAlgebraicSpace_pullback B S hS _ _ algA algU algC)
    algU algA algC (IsPullback.of_hasPullback g u).flip fp

/-! ### The image system of a good diagram on a later tail -/

namespace GoodDiagram

section Tail

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt}
  (G : GoodDiagram B S hS hZ D pX) {i₀ : I} (le : G.index ≤ i₀)

/-- The system of scheme-theoretic images `X_i` of a good diagram, restricted to the stages
`i ≥ i₀` above a later stage `i₀`. -/
noncomputable abbrev tailSystem : Over (op i₀) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.map (homOfLE le).op ⋙ imageSystem G

/-- The canonical cone from `X` to the restricted image system. -/
noncomputable abbrev tailCone : Cone (tailSystem G le) :=
  (imageCone G).whisker (Over.map (homOfLE le).op)

/-- The morphism `X_i ⟶ B_i` from a member of the restricted image system to its stage. -/
noncomputable abbrev tailBase (j : Over (op i₀)) : (tailSystem G le).obj j ⟶ D.system.obj j.left :=
  (stageImage G ((Over.map (homOfLE le).op).obj j)).ι ≫ pullback.fst _ _

/-- **Stacks 0CP9 on a later tail.** The restriction of the image system to the stages above a
later stage still has `X` as its limit, the restriction being along an initial functor. -/
noncomputable def isLimit_tailCone (algX : IsAlgebraicSpace B S hS X)
    (small : Cardinal.mk I < B.cutoff.ord.cof) : IsLimit (tailCone G le) :=
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm (isLimit_imageCone G algX small)

/-- The morphisms `X_i ⟶ B_i` are compatible with the transition morphisms of both systems. -/
@[reassoc]
lemma tailSystem_map_tailBase {j k : Over (op i₀)} (a : j ⟶ k) :
    (tailSystem G le).map a ≫ tailBase G le k = tailBase G le j ≫ D.system.map a.left := by
  simp only [tailBase, Functor.comp_map, imageSystem_map_ι_assoc, stageTargetMap_fst,
    Over.map_map_left, Category.assoc]

/-- The composite `X ⟶ X_i ⟶ B_i` is the structure morphism `X ⟶ B` followed by the projection
`B ⟶ B_i`. -/
@[reassoc]
lemma tailCone_π_tailBase (j : Over (op i₀)) :
    (tailCone G le).π.app j ≫ tailBase G le j = pX ≫ D.limitCone.π.app j.left := by
  simp only [tailBase, Cone.whisker_π, Functor.whiskerLeft_app, imageCone_π_ι_assoc,
    stageMap_fst, Over.map_obj_left]

/-- Each member `X_i` of the restricted image system is an algebraic space. -/
lemma tailSystem_isAlgebraicSpace (j : Over (op i₀)) :
    IsAlgebraicSpace B S hS ((tailSystem G le).obj j) :=
  imageSystem_isAlgebraicSpace G _

/-- Each member `X_i` of the restricted image system is quasi-compact. -/
lemma tailSystem_isQuasiCompactSpace (j : Over (op i₀)) :
    IsQuasiCompactSpace B S hS ((tailSystem G le).obj j) :=
  imageSystem_isQuasiCompactSpace G _

/-- Each member `X_i` of the restricted image system is quasi-separated over `ℤ`. -/
lemma tailSystem_isAbsolutelyQuasiSeparated (algX : IsAlgebraicSpace B S hS X)
    (qsX : IsQuasiSeparated B S hS pX) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (j : Over (op i₀)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((tailSystem G le).obj j) :=
  imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated G small algX qsX _

/-- The transition morphisms of the restricted image system are affine. -/
lemma tailSystem_map_isAffineHom {j k : Over (op i₀)} (a : j ⟶ k) :
    IsAffineHom B S hS ((tailSystem G le).map a) :=
  imageSystem_map_isAffineHom G _

/-- Each member `X_i` of the restricted image system is locally Noetherian. -/
lemma tailSystem_isLocallyNoetherian (j : Over (op i₀)) :
    HasEtaleLocalProperty B S hS ((tailSystem G le).obj j)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  imageSystem_isLocallyNoetherian G _

/-- A member `X_i` of the image system is locally of finite type over its stage `B_i`. -/
lemma isLocallyOfFiniteType_tailBase (j : Over (op i₀)) :
    IsLocallyOfFiniteType B S hS (tailBase G le j) :=
  isLocallyOfFiniteType_comp B S hS (imageSystem_isAlgebraicSpace G _)
    (isAlgebraicSpace_stageTarget G _) (D.system_isAlgebraicSpace j.left.unop) _ _
    (isLocallyOfFiniteType_of_isImmersion B S hS _
      (isImmersion_of_isClosedImmersion B S hS (isClosedSubspace_stageImage G _).2))
    (isLocallyOfFiniteType_stageTarget_fst G _)

/-- A leg `X ⟶ X_i` of the canonical cone is quasi-compact: followed by the closed immersion
`X_i ⟶ B_i ×_{B_{i₁}} W` it is the stage map, which is quasi-compact. -/
lemma isQuasiCompact_tailCone_π (small : Cardinal.mk I < B.cutoff.ord.cof) (j : Over (op i₀)) :
    IsQuasiCompact B S hS ((tailCone G le).π.app j) :=
  isQuasiCompact_of_comp_mono B S hS _ (stageImage G _).ι
    (by rw [Cone.whisker_π, Functor.whiskerLeft_app, imageCone_π_app, toSchemeTheoreticImage_ι]
        exact isQuasiCompact_stageMap G small _)

/-- A leg `X ⟶ X_i` of the canonical cone, followed by the inclusion
`X_i ⟶ B_i ×_{B_{i₁}} W`, is the stage map. -/
@[reassoc]
lemma tailCone_π_ι (j : Over (op i₀)) :
    (tailCone G le).π.app j ≫ (stageImage G ((Over.map (homOfLE le).op).obj j)).ι =
      stageMap G ((Over.map (homOfLE le).op).obj j) :=
  imageCone_π_ι G _

/-- The transition morphism of the restricted image system commutes with the projections of
the base-changed models to the model `W`. -/
lemma tailSystem_map_ι_snd {j k : Over (op i₀)} (a : j ⟶ k) :
    (tailSystem G le).map a ≫ (stageImage G ((Over.map (homOfLE le).op).obj k)).ι ≫
        pullback.snd _ _ =
      (stageImage G ((Over.map (homOfLE le).op).obj j)).ι ≫ pullback.snd _ _ := by
  simp only [Functor.comp_map, imageSystem_map_ι_assoc, stageTargetMap_snd]

/-- The scheme-theoretic image of a leg `X ⟶ X_i` of the canonical cone is all of `X_i`. -/
lemma schemeTheoreticImage_tailCone_π (j : Over (op i₀)) :
    schemeTheoreticImageSubfunctor B S hS ((tailCone G le).π.app j) = ⊤ :=
  schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS _
    (isAlgebraicSpace_stageTarget G _)

end Tail

/-! ### Stacks 0CPC -/

namespace SystemMorphism

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {pX : X ⟶ D.limitCone.pt} {pY : Y ⟶ D.limitCone.pt}

/-- A flat morphism `f : X ⟶ Y` of finite presentation is the base change, along a projection
`Y ⟶ Y_n` of the image system of `Y`, of a flat morphism `u : U ⟶ Y_n` of finite presentation. -/
theorem exists_flat_model (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsY : IsQuasiSeparated B S hS pY)
    (small : Cardinal.mk I < B.cutoff.ord.cof) (GY : GoodDiagram B S hS hZ D pY) {i₀ : I}
    (leY : GY.index ≤ i₀) (f : X ⟶ Y) (flat : IsFlat B S hS f)
    (fp : IsFinitePresentation B S hS f) :
    ∃ (n : Over (op i₀)) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B S hS U) (u : U ⟶ (tailSystem GY leY).obj n) (toU : X ⟶ U),
      IsFlat B S hS u ∧ IsFinitePresentation B S hS u ∧
        IsPullback toU f u ((tailCone GY leY).π.app n) := by
  classical
  let Yr := tailSystem GY leY
  let cY := tailCone GY leY
  have hcY : IsLimit cY := isLimit_tailCone GY leY algY small
  have hJ : Cardinal.mk (Over (op i₀)) < B.cutoff.ord.cof :=
    (cardinal_mk_over_op_le i₀).trans_lt small
  have hJh : ∀ j k : Over (op i₀), Cardinal.mk (j ⟶ k) < B.cutoff.ord.cof :=
    cardinal_mk_hom_over_op_lt B i₀
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have qcYr := tailSystem_isQuasiCompactSpace GY leY
  have qsYr := tailSystem_isAbsolutelyQuasiSeparated GY leY algY qsY small
  have afYr : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom B S hS (Yr.map a) :=
    fun a => tailSystem_map_isAffineHom GY leY a
  let eY : Y ≅ limit Yr := hcY.conePointUniqueUpToIso (limit.isLimit Yr)
  have heY : ∀ j, eY.hom ≫ limit.π Yr j = cY.π.app j :=
    fun j => hcY.conePointUniqueUpToIso_hom_comp (limit.isLimit Yr) j
  have algL : IsAlgebraicSpace B S hS (limit Yr) := Space.isAlgebraicSpace_of_iso B S hS eY algY
  obtain ⟨m, Uo, algU, fpU, ⟨φ⟩⟩ := exists_model_of_finitePresentation B S hS hZ Yr hJ hJh
    aYr afYr qcYr qsYr (Over.mk (f ≫ eY.hom)) algX
    (isFinitePresentation_comp_iso algX algY algL f eY fp)
  let U := Uo.left
  let u : U ⟶ Yr.obj m := Uo.hom
  let toU : X ⟶ U := φ.hom.left ≫ pullback.fst _ _
  have sqU : IsPullback toU f u (cY.π.app m) := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback u (limit.π Yr m))
      ((Over.forget _).mapIso φ.symm) (Iso.refl _) eY.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [toU]
      rfl
    · have hw : φ.inv.left ≫ f ≫ eY.hom = pullback.snd u (limit.π Yr m) := Over.w φ.inv
      rw [← hw]
      simp
    · simp
    · simp [← heY]
  let k := m.left.unop
  let E : (Set.Ici k)ᵒᵖ ⥤ Over (op k) := iciOpToOverOp k
  let M : Over (op k) ⥤ Over (op i₀) := Over.map m.hom
  let base : (Set.Ici k)ᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := E ⋙ M ⋙ Yr
  have : E.Initial := inferInstanceAs (iciOpEquivalenceOverOp k).functor.Initial
  have hcB : IsLimit (cY.whisker (E ⋙ M)) :=
    (Functor.Initial.isLimitWhiskerEquiv (E ⋙ M) cY).symm hcY
  let eB : Y ≅ limit base := hcB.conePointUniqueUpToIso (limit.isLimit base)
  have heB : ∀ j, eB.hom ≫ limit.π base j = cY.π.app ((E ⋙ M).obj j) :=
    fun j => hcB.conePointUniqueUpToIso_hom_comp (limit.isLimit base) j
  let i0 : Set.Ici k := ⟨k, le_rfl⟩
  have qcU : IsQuasiCompactSpace B S hS U :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS u (aYr m) (qcYr m) fpU
  have qsU : IsAbsolutelyQuasiSeparated B S hS hZ U :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ algU (qsYr m) fpU.2.2
  let Dm : MorphismDescentSystem B S hS hZ (Set.Ici k) :=
    { base := base
      indexSize := (Cardinal.mk_subtype_le _).trans_lt small
      base_isAlgebraicSpace := fun i => aYr _
      transition_affine := fun a => afYr _
      limit_isAlgebraicSpace := Space.isAlgebraicSpace_of_iso B S hS eB algY
      initial := i0
      source₀ := U
      target₀ := Yr.obj m
      sourceToBase := u
      targetToBase := 𝟙 _
      map₀ := u
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := algU
      target₀_isAlgebraicSpace := aYr m
      base₀_quasiCompact := qcYr m
      base₀_quasiSeparated := qsYr m
      source₀_quasiCompact := qcU
      source₀_quasiSeparated := qsU
      target₀_quasiCompact := qcYr m
      target₀_quasiSeparated := qsYr m }
  have flatLimit : IsFlat B S hS Dm.mapLimit := by
    let π0 : limit base ⟶ Yr.obj m := limit.π base (op i0)
    have sq' : IsPullback (f ≫ eB.hom) toU π0 u :=
      IsPullback.of_iso sqU.flip (Iso.refl _) eB (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp only [Iso.refl_hom, Category.comp_id]; exact (heB (op i0)).symm) (by simp)
    have algP : IsAlgebraicSpace B S hS (pullback π0 u) := Dm.sourceLimit_isAlgebraicSpace
    have algP' : IsAlgebraicSpace B S hS (pullback π0 (𝟙 (Yr.obj m))) :=
      Dm.targetLimit_isAlgebraicSpace
    have hfst : IsFlat B S hS (pullback.fst π0 u) := by
      rw [← sq'.isoPullback_inv_fst]
      exact isFlat_comp B S hS algP algX Dm.limit_isAlgebraicSpace _ _ (isFlat_of_isIso _ algX)
        (isFlat_comp B S hS algX algY Dm.limit_isAlgebraicSpace _ _ flat
          (isFlat_of_isIso _ Dm.limit_isAlgebraicSpace))
    let ml : pullback π0 u ⟶ pullback π0 (𝟙 (Yr.obj m)) := Dm.mapLimit
    have h1 : ml ≫ pullback.fst π0 (𝟙 (Yr.obj m)) = pullback.fst π0 u := Dm.mapLimit_fst
    have h3 : (ml ≫ pullback.fst π0 (𝟙 (Yr.obj m))) ≫
        inv (pullback.fst π0 (𝟙 (Yr.obj m))) = ml := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    show IsFlat B S hS ml
    rw [← h3, h1]
    exact isFlat_comp B S hS algP Dm.limit_isAlgebraicSpace algP' _ _ hfst
      (isFlat_of_isIso _ algP')
  obtain ⟨i1, le1, flat1⟩ := Dm.exists_isFlat_mapAt flatLimit fpU.1
  let m1 : Over m := Over.mk (M.map (E.map (homOfLE le1).op))
  have flatM1 : IsFlat B S hS (pullback.fst (Yr.map m1.hom) u) := by
    let g1 : Yr.obj ((E ⋙ M).obj (op i1)) ⟶ Yr.obj m := Dm.baseAtToInitial i1 le1
    let ma : pullback g1 u ⟶ pullback g1 (𝟙 (Yr.obj m)) := Dm.mapAt i1 le1
    have h1 : ma ≫ pullback.fst g1 (𝟙 (Yr.obj m)) = pullback.fst g1 u := Dm.mapAt_fst i1 le1
    have algA : IsAlgebraicSpace B S hS (pullback g1 u) := Dm.sourceAt_isAlgebraicSpace i1 le1
    have algB : IsAlgebraicSpace B S hS (pullback g1 (𝟙 (Yr.obj m))) :=
      Dm.targetAt_isAlgebraicSpace i1 le1
    have := isFlat_comp B S hS algA algB (aYr _) ma _ flat1
      (isFlat_of_isIso (pullback.fst g1 (𝟙 (Yr.obj m))) (aYr _))
    rwa [h1] at this
  have sqR : IsPullback (pullback.snd (Yr.map m1.hom) u) (pullback.fst (Yr.map m1.hom) u) u
      (Yr.map m1.hom) := (IsPullback.of_hasPullback (Yr.map m1.hom) u).flip
  refine ⟨m1.left, pullback (Yr.map m1.hom) u,
    isAlgebraicSpace_pullback B S hS _ _ (aYr _) algU (aYr _), pullback.fst _ _,
    pullback.lift (f ≫ cY.π.app m1.left) toU ?_, flatM1,
    isFinitePresentation_of_isPullback B S hS (isAlgebraicSpace_pullback B S hS _ _ (aYr _)
      algU (aYr _)) algU (aYr _) (aYr _) sqR fpU, ?_⟩
  · rw [Category.assoc, cY.w m1.hom]
    exact sqU.w.symm
  · refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) sqR
    rw [pullback.lift_snd, cY.w m1.hom]
    exact sqU

section Comparison

variable {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
  {i₀ : I} {leX : GX.index ≤ i₀} {leY : GY.index ≤ i₀}

/-- The morphism `f_j : X_j ⟶ Y_j` restricts to `f` along the canonical cones. -/
@[reassoc]
lemma tailCone_π_maps (F : SystemMorphism GX GY f i₀ leX leY) (j : Over (op i₀)) :
    (tailCone GX leX).π.app j ≫ F.maps.app j = f ≫ (tailCone GY leY).π.app j :=
  F.induces j

/-- The morphism `f_j : X_j ⟶ Y_j` lies over the stage `B_j`. -/
@[reassoc]
lemma maps_tailBase (F : SystemMorphism GX GY f i₀ leX leY) (j : Over (op i₀)) :
    F.maps.app j ≫ tailBase GY leY j = tailBase GX leX j :=
  F.over_base j

/-- The morphism `f_p : X_p ⟶ Y_p` of the image systems is locally of finite presentation. -/
private theorem isLocallyOfFinitePresentation_maps_app
    (F : SystemMorphism GX GY f i₀ leX leY) (p : Over (op i₀)) :
    IsLocallyOfFinitePresentation B S hS (F.maps.app p) :=
  isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS
    (tailSystem_isAlgebraicSpace GX leX p) (tailSystem_isAlgebraicSpace GY leY p) _
    (tailSystem_isLocallyNoetherian GY leY p)
    (isLocallyOfFiniteType_of_comp B S hS (tailSystem_isAlgebraicSpace GX leX p)
      (tailSystem_isAlgebraicSpace GY leY p) (D.system_isAlgebraicSpace p.left.unop)
      (F.maps.app p) (tailBase GY leY p)
      (by rw [maps_tailBase]; exact isLocallyOfFiniteType_tailBase GX leX p))

/-- The objects constructed in the proof of Stacks 0CPC, from which the comparison of the image
system of `X` with a system of base changes is built: a flat morphism `u : U ⟶ Y_n` of finite
presentation of which `f` is the base change along `Y ⟶ Y_n`, a morphism `t₀ : X_p ⟶ U`
restricting to `X ⟶ U`, and a morphism `s₀ : Y_l ×_{Y_n} U ⟶ X_p` restricting to `X ⟶ X_p`. -/
structure FlatComparison (F : SystemMorphism GX GY f i₀ leX leY) where
  /-- The stage over which `f` descends. -/
  n : Over (op i₀)
  /-- The descended source. -/
  U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The descended source is an algebraic space. -/
  algU : IsAlgebraicSpace B S hS U
  /-- The descended morphism. -/
  u : U ⟶ (tailSystem GY leY).obj n
  /-- The projection `X ⟶ U`. -/
  toU : X ⟶ U
  /-- The descended morphism is flat. -/
  flat : IsFlat B S hS u
  /-- The descended morphism is of finite presentation. -/
  fp : IsFinitePresentation B S hS u
  /-- The morphism `f` is the base change of `u` along `Y ⟶ Y_n`. -/
  sq : IsPullback toU f u ((tailCone GY leY).π.app n)
  /-- The stage of `X` over which `X ⟶ U` is defined. -/
  p : Over (op i₀)
  /-- The stage `p` lies above `n`. -/
  hp : p ⟶ n
  /-- The morphism `X_p ⟶ U`. -/
  t₀ : (tailSystem GX leX).obj p ⟶ U
  /-- The morphism `X_p ⟶ U` restricts to `X ⟶ U`. -/
  t₀_lim : (tailCone GX leX).π.app p ≫ t₀ = toU
  /-- The morphism `X_p ⟶ U` lies over `Y_n`. -/
  t₀_u : t₀ ≫ u = (tailSystem GX leX).map hp ≫ F.maps.app n
  /-- The stage of the base changes over which `X ⟶ X_p` is defined. -/
  l₀ : Over n
  /-- The stage `l₀` lies above `p`. -/
  c₀ : l₀.left ⟶ p
  /-- The morphism `Y_{l₀} ×_{Y_n} U ⟶ X_p`. -/
  s₀ : pullback ((tailSystem GY leY).map l₀.hom) u ⟶ (tailSystem GX leX).obj p
  /-- The morphism `Y_{l₀} ×_{Y_n} U ⟶ X_p` restricts to `X ⟶ X_p`. -/
  s₀_lim : pullback.lift (pullback.fst _ _ ≫ (tailCone GY leY).π.app l₀.left) (pullback.snd _ _)
      (by rw [Category.assoc, (tailCone GY leY).w l₀.hom, pullback.condition]) ≫ s₀ =
    sq.flip.isoPullback.inv ≫ (tailCone GX leX).π.app p
  /-- The morphism `Y_{l₀} ×_{Y_n} U ⟶ X_p` lies over `Y_p`. -/
  s₀_F : s₀ ≫ F.maps.app p =
    pullback.fst ((tailSystem GY leY).map l₀.hom) u ≫ (tailSystem GY leY).map c₀

/-- The objects of `AlgebraicGeometry.Space.GoodDiagram.SystemMorphism.FlatComparison` exist
for a flat morphism of finite presentation. -/
theorem nonempty_flatComparison (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (F : SystemMorphism GX GY f i₀ leX leY) (flat : IsFlat B S hS f)
    (fp : IsFinitePresentation B S hS f) : Nonempty (FlatComparison F) := by
  classical
  let Xr := tailSystem GX leX
  let Yr := tailSystem GY leY
  let cX := tailCone GX leX
  let cY := tailCone GY leY
  have hcX : IsLimit cX := isLimit_tailCone GX leX algX small
  have hcY : IsLimit cY := isLimit_tailCone GY leY algY small
  have hJ : Cardinal.mk (Over (op i₀)) < B.cutoff.ord.cof :=
    (cardinal_mk_over_op_le i₀).trans_lt small
  have hJh : ∀ j k : Over (op i₀), Cardinal.mk (j ⟶ k) < B.cutoff.ord.cof :=
    cardinal_mk_hom_over_op_lt B i₀
  have aXr := tailSystem_isAlgebraicSpace GX leX
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have qcXr := tailSystem_isQuasiCompactSpace GX leX
  have qcYr := tailSystem_isQuasiCompactSpace GY leY
  have qsXr := tailSystem_isAbsolutelyQuasiSeparated GX leX algX qsX small
  have qsYr := tailSystem_isAbsolutelyQuasiSeparated GY leY algY qsY small
  have afXr : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom B S hS (Xr.map a) :=
    fun a => tailSystem_map_isAffineHom GX leX a
  have afYr : ∀ {j k : Over (op i₀)} (a : j ⟶ k), IsAffineHom B S hS (Yr.map a) :=
    fun a => tailSystem_map_isAffineHom GY leY a
  have hind : ∀ j, cX.π.app j ≫ F.maps.app j = f ≫ cY.π.app j := F.induces
  obtain ⟨n, U, algU, u, toU, flatU, fpU, sqU⟩ :=
    exists_flat_model algX algY qsY small GY leY f flat fp
  obtain ⟨_, t, p, a0, hp, ht1, ht2⟩ := exists_stage_map_of_relativelyLimitPreserving B S hS hZ
    Xr cX hcX hJ hJh aXr qcXr qsXr afXr algX algU (aYr n) u fpU.1 toU n (F.maps.app n)
    (by rw [sqU.w, hind])
  let t₀ : Xr.obj p ⟶ U := Xr.map a0 ≫ t
  have ht₀lim : cX.π.app p ≫ t₀ = toU := ht1
  have ht₀u : t₀ ≫ u = Xr.map hp ≫ F.maps.app n := ht2
  clear ht1 ht2
  have hcU : IsLimit (baseChangeCone Yr n u cY) := isLimitBaseChangeCone Yr n u hcY
  let e : X ≅ pullback (cY.π.app n) u := sqU.flip.isoPullback
  have hefst : e.inv ≫ f = pullback.fst (cY.π.app n) u := by
    rw [← sqU.flip.isoPullback_hom_fst, Iso.inv_hom_id_assoc]
  have algP : IsAlgebraicSpace B S hS (pullback (cY.π.app n) u) :=
    isAlgebraicSpace_pullback B S hS _ _ algY algU (aYr n)
  have aUs : ∀ l, IsAlgebraicSpace B S hS ((baseChangeSystem Yr n u).obj l) :=
    fun l => isAlgebraicSpace_pullback B S hS _ _ (aYr _) algU (aYr n)
  have fpUs : ∀ l : Over n, IsFinitePresentation B S hS (pullback.fst (Yr.map l.hom) u) :=
    fun l => isFinitePresentation_fst_pullback (aYr _) (aYr n) algU _ u fpU
  have flatUs : ∀ l : Over n, IsFlat B S hS (pullback.fst (Yr.map l.hom) u) :=
    fun l => isFlat_of_isPullback_of_isAlgebraicSpace B S hS
      (IsPullback.of_hasPullback (Yr.map l.hom) u) algU (aYr n) flatU
  have qcUs : ∀ l, IsQuasiCompactSpace B S hS ((baseChangeSystem Yr n u).obj l) :=
    fun l => isQuasiCompactSpace_of_isFinitePresentation B S hS _ (aYr _) (qcYr _) (fpUs l)
  have qsUs : ∀ l, IsAbsolutelyQuasiSeparated B S hS hZ ((baseChangeSystem Yr n u).obj l) :=
    fun l => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (aUs l) (qsYr _)
      (fpUs l).2.2
  have afUs : ∀ {l l' : Over n} (a : l ⟶ l'),
      IsAffineHom B S hS ((baseChangeSystem Yr n u).map a) :=
    fun a => isAffineHom_of_isPullback (isPullback_baseChangeSystem_map Yr n u a).flip
      (afYr _)
  have hJn : Cardinal.mk (Over n) < B.cutoff.ord.cof :=
    mk_over_lt B.aleph0_lt_cutoff_cof hJ hJh n
  have hJnh := cardinal_mk_hom_over_slice_lt (B := B) n
  have lfpF := isLocallyOfFinitePresentation_maps_app F p
  let pU : Over n := Over.mk hp
  obtain ⟨q0, s', l0, b1, b2, hs1, hs2⟩ := exists_stage_map_of_relativelyLimitPreserving B S hS
    hZ (baseChangeSystem Yr n u) (baseChangeCone Yr n u cY) hcU hJn hJnh aUs qcUs qsUs afUs algP
    (aXr p) (aYr p) (F.maps.app p) lfpF
    (e.inv ≫ cX.π.app p) pU (pullback.fst (Yr.map pU.hom) u)
    (by rw [Category.assoc, hind, ← Category.assoc, hefst, baseChangeCone_π_fst]; rfl)
  let s₀ : (baseChangeSystem Yr n u).obj l0 ⟶ Xr.obj p := (baseChangeSystem Yr n u).map b1 ≫ s'
  have hs₀lim : (baseChangeCone Yr n u cY).π.app l0 ≫ s₀ = e.inv ≫ cX.π.app p := hs1
  have hs₀F : s₀ ≫ F.maps.app p =
      (baseChangeSystem Yr n u).map b2 ≫ pullback.fst (Yr.map pU.hom) u := hs2
  clear hs1 hs2
  refine ⟨⟨n, U, algU, u, toU, flatU, fpU, sqU, p, hp, t₀, ht₀lim, ht₀u, l0, b2.left, s₀,
    hs₀lim, ?_⟩⟩
  rw [hs₀F, baseChangeSystem_map_fst]

namespace FlatComparison

variable {F : SystemMorphism GX GY f i₀ leX leY} (M : FlatComparison F)

/-- The system of base changes `U_l = Y_l ×_{Y_n} U`. -/
noncomputable abbrev Us : Over M.n ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  baseChangeSystem (tailSystem GY leY) M.n M.u

/-- The cone from `Y ×_{Y_n} U` to the system of base changes. -/
noncomputable abbrev cU : Cone M.Us := baseChangeCone (tailSystem GY leY) M.n M.u (tailCone GY leY)

/-- The projection `U_l ⟶ Y_l`. -/
noncomputable abbrev pr (l : Over M.n) : M.Us.obj l ⟶ (tailSystem GY leY).obj l.left :=
  pullback.fst ((tailSystem GY leY).map l.hom) M.u

/-- The identification `X ≅ Y ×_{Y_n} U`. -/
noncomputable abbrev e : X ≅ pullback ((tailCone GY leY).π.app M.n) M.u := M.sq.flip.isoPullback

/-- The morphism `X ⟶ U_l`. -/
noncomputable abbrev d (l : Over M.n) : X ⟶ M.Us.obj l := M.e.hom ≫ M.cU.π.app l

/-- The stage of the base changes corresponding to the stage `p`. -/
noncomputable abbrev pU : Over M.n := Over.mk M.hp

/-- Under `X ≅ Y ×_{Y_n} U`, the projection to `Y` is `f`. -/
lemma e_inv_f : M.e.inv ≫ f = pullback.fst ((tailCone GY leY).π.app M.n) M.u :=
  M.sq.flip.isoPullback_inv_fst

/-- Under `X ≅ Y ×_{Y_n} U`, the projection to `U` is `X ⟶ U`. -/
lemma e_inv_toU : M.e.inv ≫ M.toU = pullback.snd ((tailCone GY leY).π.app M.n) M.u :=
  M.sq.flip.isoPullback_inv_snd

/-- The composite `X ⟶ U_l ⟶ Y_l` is `f` followed by the leg `Y ⟶ Y_l`. -/
lemma d_pr (l : Over M.n) : M.d l ≫ M.pr l = f ≫ (tailCone GY leY).π.app l.left := by
  rw [Category.assoc, baseChangeCone_π_fst, ← Category.assoc, M.sq.flip.isoPullback_hom_fst]

/-- The composite `X ⟶ U_l ⟶ U` is the projection `X ⟶ U`. -/
lemma d_snd (l : Over M.n) :
    M.d l ≫ pullback.snd ((tailSystem GY leY).map l.hom) M.u = M.toU := by
  rw [Category.assoc, baseChangeCone_π_snd, M.sq.flip.isoPullback_hom_snd]

/-- The morphisms `X ⟶ U_l` are compatible with the transition morphisms of `(U_l)`. -/
lemma d_map {l l' : Over M.n} (a : l ⟶ l') : M.d l ≫ M.Us.map a = M.d l' := by
  rw [Category.assoc, M.cU.w a]

/-- The comparison map `T_l : X_l ⟶ U_l`, for a stage `l` above `p`. -/
noncomputable def T (l : Over M.n) (b : l ⟶ M.pU) : (tailSystem GX leX).obj l.left ⟶ M.Us.obj l :=
  pullback.lift (F.maps.app l.left) ((tailSystem GX leX).map b.left ≫ M.t₀) (by
    rw [Category.assoc, M.t₀_u, ← Category.assoc, ← Functor.map_comp, F.maps.naturality,
      Subsingleton.elim (b.left ≫ M.hp) l.hom])

/-- The composite `X_l ⟶ U_l ⟶ Y_l` is `f_l`. -/
@[reassoc (attr := simp)]
lemma T_pr (l : Over M.n) (b : l ⟶ M.pU) : M.T l b ≫ M.pr l = F.maps.app l.left :=
  pullback.lift_fst _ _ _

/-- The composite `X_l ⟶ U_l ⟶ U` is the transition morphism `X_l ⟶ X_p` followed by `X_p ⟶ U`.
-/
@[reassoc (attr := simp)]
lemma T_snd (l : Over M.n) (b : l ⟶ M.pU) :
    M.T l b ≫ pullback.snd ((tailSystem GY leY).map l.hom) M.u =
      (tailSystem GX leX).map b.left ≫ M.t₀ :=
  pullback.lift_snd _ _ _

/-- The composite `X ⟶ X_l ⟶ U_l` is the morphism `X ⟶ U_l`. -/
lemma π_T (l : Over M.n) (b : l ⟶ M.pU) :
    (tailCone GX leX).π.app l.left ≫ M.T l b = M.d l := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, T_pr, M.d_pr]
    exact F.induces l.left
  · rw [Category.assoc, T_snd, ← Category.assoc, (tailCone GX leX).w]
    exact M.t₀_lim.trans (M.d_snd l).symm

/-- The comparison maps `X_l ⟶ U_l` are compatible with the transition morphisms. -/
lemma T_map {l l' : Over M.n} (a : l ⟶ l') (b : l ⟶ M.pU) (b' : l' ⟶ M.pU) :
    M.T l b ≫ M.Us.map a = (tailSystem GX leX).map a.left ≫ M.T l' b' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeSystem_map_fst, ← Category.assoc, T_pr, Category.assoc,
      T_pr, ← F.maps.naturality]
  · rw [Category.assoc, baseChangeSystem_map_snd, T_snd, Category.assoc, T_snd,
      ← Category.assoc, ← Functor.map_comp, Subsingleton.elim (a.left ≫ b'.left) b.left]

/-- The map `s_l : U_l ⟶ X_p`, for a stage `l` above `l₀`. -/
noncomputable def s (l : Over M.n) (c : l ⟶ M.l₀) : M.Us.obj l ⟶ (tailSystem GX leX).obj M.p :=
  M.Us.map c ≫ M.s₀

/-- The map `s_l` is the transition morphism `U_l ⟶ U_{l₀}` followed by `s₀`. -/
lemma s_eq (l : Over M.n) (c : l ⟶ M.l₀) : M.s l c = M.Us.map c ≫ M.s₀ := rfl

/-- The composite `X ⟶ U_l ⟶ X_p` is the leg `X ⟶ X_p` of the canonical cone. -/
lemma d_s (l : Over M.n) (c : l ⟶ M.l₀) : M.d l ≫ M.s l c = (tailCone GX leX).π.app M.p := by
  rw [s_eq, ← Category.assoc, M.d_map c, Category.assoc]
  exact (congrArg (M.e.hom ≫ ·) M.s₀_lim).trans (M.e.hom_inv_id_assoc _)

/-- The composite `U_l ⟶ X_p ⟶ Y_p` is the projection `U_l ⟶ Y_l` followed by the transition
morphism `Y_l ⟶ Y_p`. -/
lemma s_F (l : Over M.n) (c : l ⟶ M.l₀) (w : l.left ⟶ M.p) :
    M.s l c ≫ F.maps.app M.p = M.pr l ≫ (tailSystem GY leY).map w := by
  rw [s_eq, Category.assoc, M.s₀_F, ← Category.assoc, baseChangeSystem_map_fst, Category.assoc,
    ← Functor.map_comp, Subsingleton.elim (c.left ≫ M.c₀) w]

/-- The composite `U_l ⟶ X_p ⟶ B_p` is `U_l ⟶ Y_l ⟶ B_l` followed by the transition morphism
`B_l ⟶ B_p`. -/
lemma s_tailBase (l : Over M.n) (c : l ⟶ M.l₀) (w : l.left ⟶ M.p) :
    M.s l c ≫ tailBase GX leX M.p =
      M.pr l ≫ tailBase GY leY l.left ≫ D.system.map w.left := by
  rw [← maps_tailBase F M.p, ← Category.assoc, M.s_F l c w, Category.assoc,
    tailSystem_map_tailBase]

/-- The morphism `q_l : U_l ⟶ B_l ×_{B_{i₁}} W` into the base-changed model of `GX`, whose
first component is `U_l ⟶ Y_l ⟶ B_l` and whose second is `U_l ⟶ X_p ⟶ W`. -/
noncomputable def q (l : Over M.n) (c : l ⟶ M.l₀) :
    M.Us.obj l ⟶ pullback (D.system.map ((Over.map (homOfLE leX).op).obj l.left).hom)
      GX.modelMap :=
  pullback.lift (M.pr l ≫ tailBase GY leY l.left)
    (M.s l c ≫ (stageImage GX ((Over.map (homOfLE leX).op).obj M.p)).ι ≫ pullback.snd _ _) (by
      have key := M.s_tailBase l c (c.left ≫ M.c₀)
      have hcond : (stageImage GX ((Over.map (homOfLE leX).op).obj M.p)).ι ≫
          pullback.snd _ _ ≫ GX.modelMap =
            tailBase GX leX M.p ≫ D.system.map ((Over.map (homOfLE leX).op).obj M.p).hom := by
        rw [← pullback.condition, Category.assoc]
      simp only [Category.assoc]
      rw [hcond, ← Category.assoc (M.s l c), key]
      simp only [Category.assoc, ← D.system.map_comp]
      exact congrArg (fun g => M.pr l ≫ tailBase GY leY l.left ≫ D.system.map g)
        (Subsingleton.elim _ _))

/-- The first component of `q_l` is `U_l ⟶ Y_l ⟶ B_l`. -/
@[reassoc (attr := simp)]
lemma q_fst (l : Over M.n) (c : l ⟶ M.l₀) :
    M.q l c ≫ pullback.fst _ _ = M.pr l ≫ tailBase GY leY l.left :=
  pullback.lift_fst _ _ _

/-- The second component of `q_l` is `U_l ⟶ X_p ⟶ W`. -/
@[reassoc (attr := simp)]
lemma q_snd (l : Over M.n) (c : l ⟶ M.l₀) :
    M.q l c ≫ pullback.snd _ _ =
      M.s l c ≫ (stageImage GX ((Over.map (homOfLE leX).op).obj M.p)).ι ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The composite `X ⟶ U_l ⟶ B_l ×_{B_{i₁}} W` is the stage map of `GX`. -/
lemma d_q (l : Over M.n) (c : l ⟶ M.l₀) :
    M.d l ≫ M.q l c = stageMap GX ((Over.map (homOfLE leX).op).obj l.left) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, q_fst, ← Category.assoc, M.d_pr, Category.assoc,
      ← tailCone_π_maps_assoc F, maps_tailBase, tailCone_π_tailBase, stageMap_fst]
    rfl
  · rw [Category.assoc, q_snd, ← Category.assoc, M.d_s, tailCone_π_ι_assoc, stageMap_snd,
      stageMap_snd]

/-- The projection `U_l ⟶ Y_l` is flat. -/
lemma isFlat_pr (l : Over M.n) : IsFlat B S hS (M.pr l) :=
  isFlat_of_isPullback_of_isAlgebraicSpace B S hS
    (IsPullback.of_hasPullback ((tailSystem GY leY).map l.hom) M.u) M.algU
    (tailSystem_isAlgebraicSpace GY leY M.n) M.flat

/-- Each base change `U_l` is an algebraic space. -/
lemma isAlgebraicSpace_Us (l : Over M.n) : IsAlgebraicSpace B S hS (M.Us.obj l) :=
  isAlgebraicSpace_pullback B S hS _ _ (tailSystem_isAlgebraicSpace GY leY _) M.algU
    (tailSystem_isAlgebraicSpace GY leY M.n)

/-- The morphism `X ⟶ U_l` is the base change of `U_l ⟶ Y_l` along `Y ⟶ Y_l`. -/
lemma isPullback_d (l : Over M.n) :
    IsPullback (M.d l) f (M.pr l) ((tailCone GY leY).π.app l.left) :=
  IsPullback.of_iso (isPullback_baseChangeCone_π (tailSystem GY leY) M.n M.u (tailCone GY leY) l)
    M.e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc])
    (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, e_inv_f])
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **Density.** The scheme-theoretic image of `X ⟶ U_l` is all of `U_l`: it is the base change
of `Y ⟶ Y_l`, whose image is all of `Y_l`, along the flat morphism `U_l ⟶ Y_l` (Stacks 089E). -/
lemma schemeTheoreticImage_d (algY : IsAlgebraicSpace B S hS Y)
    (small : Cardinal.mk I < B.cutoff.ord.cof) (l : Over M.n) :
    schemeTheoreticImageSubfunctor B S hS (M.d l) = ⊤ := by
  rw [← (M.isPullback_d l).flip.isoPullback_hom_snd, schemeTheoreticImageSubfunctor_comp_of_epi,
    schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact' B S hS (M.pr l)
      ((tailCone GY leY).π.app l.left) (M.isAlgebraicSpace_Us l)
      (tailSystem_isAlgebraicSpace GY leY _) algY (M.isFlat_pr l)
      (isQuasiCompact_tailCone_π GY leY small _),
    schemeTheoreticImage_tailCone_π]
  rfl

/-- The morphism `q_l` factors through the scheme-theoretic image `X_l`. -/
lemma range_q_le (algY : IsAlgebraicSpace B S hS Y) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (l : Over M.n) (c : l ⟶ M.l₀) :
    Subfunctor.range (M.q l c) ≤ stageImage GX ((Over.map (homOfLE leX).op).obj l.left) := by
  have hZc : IsClosedSubspace B S hS
      ((stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).preimage (M.q l c)) :=
    isClosedSubspace_preimage B S hS (M.q l c) _ (isAlgebraicSpace_stageTarget GX _)
      (M.isAlgebraicSpace_Us l) (isClosedSubspace_stageImage GX _)
  have hle : Subfunctor.range (M.d l) ≤
      (stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).preimage (M.q l c) := by
    rintro U x ⟨y, rfl⟩
    have hy : (M.q l c).app U ((M.d l).app U y) =
        (stageMap GX ((Over.map (homOfLE leX).op).obj l.left)).app U y := by
      simpa using congrArg (fun g => g.app U y) (M.d_q l c)
    show (M.q l c).app U ((M.d l).app U y) ∈ (stageImage GX _).obj U
    rw [hy]
    exact range_le_schemeTheoreticImageSubfunctor B S hS _ U ⟨_, rfl⟩
  have htop := schemeTheoreticImageSubfunctor_le B S hS (M.d l) hZc hle
  rw [M.schemeTheoreticImage_d algY small l, top_le_iff] at htop
  exact (Subfunctor.preimage_eq_top_iff _ _).1 htop

/-- The comparison map `U_l ⟶ X_l`: the morphism `q_l` factors through the
scheme-theoretic image `X_l`, because `X ⟶ U_l` is scheme-theoretically dense. -/
noncomputable def back (algY : IsAlgebraicSpace B S hS Y) (small : Cardinal.mk I < B.cutoff.ord.cof)
    (l : Over M.n) (c : l ⟶ M.l₀) : M.Us.obj l ⟶ (tailSystem GX leX).obj l.left :=
  Subfunctor.lift (M.q l c) (M.range_q_le algY small l c)

variable (algY : IsAlgebraicSpace B S hS Y) (small : Cardinal.mk I < B.cutoff.ord.cof)

/-- The comparison map `U_l ⟶ X_l`, followed by the inclusion `X_l ⟶ B_l ×_{B_{i₁}} W`, is
`q_l`. -/
@[reassoc (attr := simp)]
lemma back_ι (l : Over M.n) (c : l ⟶ M.l₀) :
    M.back algY small l c ≫ (stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).ι =
      M.q l c :=
  Subfunctor.lift_ι _ _

/-- The composite `U_l ⟶ X_l ⟶ X_p` is `s_l`. -/
lemma back_map (l : Over M.n) (c : l ⟶ M.l₀) (w : l.left ⟶ M.p) :
    M.back algY small l c ≫ (tailSystem GX leX).map w = M.s l c := by
  refine (cancel_mono (stageImage GX ((Over.map (homOfLE leX).op).obj M.p)).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · have h1 := tailSystem_map_tailBase GX leX w
    have h2 : M.back algY small l c ≫ tailBase GX leX l.left =
        M.pr l ≫ tailBase GY leY l.left := by
      rw [show tailBase GX leX l.left = (stageImage GX _).ι ≫ pullback.fst _ _ from rfl,
        ← Category.assoc, back_ι, q_fst]
    calc ((M.back algY small l c ≫ (tailSystem GX leX).map w) ≫
          (stageImage GX ((Over.map (homOfLE leX).op).obj M.p)).ι) ≫ pullback.fst _ _
        = M.back algY small l c ≫ ((tailSystem GX leX).map w ≫ tailBase GX leX M.p) := by
          simp only [Category.assoc]
      _ = M.pr l ≫ tailBase GY leY l.left ≫ D.system.map w.left := by
          rw [h1, ← Category.assoc, h2, Category.assoc]
      _ = M.s l c ≫ tailBase GX leX M.p := (M.s_tailBase l c w).symm
      _ = _ := by simp only [Category.assoc]
  · rw [Category.assoc, Category.assoc, tailSystem_map_ι_snd, back_ι_assoc, q_snd]
    simp only [Category.assoc]

/-- The composite `U_l ⟶ X_l ⟶ Y_l` is the projection `U_l ⟶ Y_l`. -/
lemma back_F (l : Over M.n) (c : l ⟶ M.l₀) :
    M.back algY small l c ≫ F.maps.app l.left = M.pr l := by
  refine (cancel_mono (stageImage GY ((Over.map (homOfLE leY).op).obj l.left)).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, show (stageImage GY _).ι ≫ pullback.fst _ _ =
      tailBase GY leY l.left from rfl, maps_tailBase, show tailBase GX leX l.left =
      (stageImage GX _).ι ≫ pullback.fst _ _ from rfl, back_ι_assoc, q_fst]
    rfl
  · let w : l.left ⟶ M.p := c.left ≫ M.c₀
    rw [Category.assoc, Category.assoc, ← tailSystem_map_ι_snd GY leY w,
      ← Category.assoc (F.maps.app l.left), ← F.maps.naturality, Category.assoc,
      ← Category.assoc (M.back algY small l c), M.back_map algY small l c w, ← Category.assoc,
      M.s_F l c w, Category.assoc, tailSystem_map_ι_snd]
    simp only [Category.assoc]

/-- If the composite `X_l ⟶ U_l ⟶ X_p` is a transition morphism, then `X_l ⟶ U_l ⟶ X_l` is the
identity. -/
lemma T_back (l : Over M.n) (b : l ⟶ M.pU) (c : l ⟶ M.l₀) (w : l.left ⟶ M.p)
    (h : M.T l b ≫ M.s l c = (tailSystem GX leX).map w) :
    M.T l b ≫ M.back algY small l c = 𝟙 _ := by
  refine (cancel_mono (stageImage GX ((Over.map (homOfLE leX).op).obj l.left)).ι).1 ?_
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, back_ι_assoc, q_fst, ← Category.assoc, T_pr, maps_tailBase,
      Category.id_comp]
  · rw [Category.assoc, Category.assoc, back_ι_assoc, q_snd, ← Category.assoc, h,
      tailSystem_map_ι_snd, Category.id_comp]

/-- If the composite `U_l ⟶ X_p ⟶ U` is the projection, then `U_l ⟶ X_l ⟶ U_l` is the identity.
-/
lemma back_T (l : Over M.n) (b : l ⟶ M.pU) (c : l ⟶ M.l₀)
    (h : M.s l c ≫ M.t₀ = pullback.snd ((tailSystem GY leY).map l.hom) M.u) :
    M.back algY small l c ≫ M.T l b = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, T_pr, back_F, Category.id_comp]
  · rw [Category.assoc, T_snd, ← Category.assoc, back_map, h, Category.id_comp]

/-- The comparison map `T_l` does not depend on the chosen morphism `l ⟶ p`. -/
lemma T_congr (l : Over M.n) (b b' : l ⟶ M.pU) : M.T l b = M.T l b' := by
  rw [Subsingleton.elim b b']

/-- The map `s_l` does not depend on the chosen morphism `l ⟶ l₀`. -/
lemma s_congr (l : Over M.n) (c c' : l ⟶ M.l₀) : M.s l c = M.s l c' := by
  rw [Subsingleton.elim c c']

/-- The maps `s_l` are compatible with the transition morphisms of `(U_l)`. -/
lemma s_map {l l' : Over M.n} (a : l ⟶ l') (c : l ⟶ M.l₀) (c' : l' ⟶ M.l₀) :
    M.Us.map a ≫ M.s l' c' = M.s l c := by
  rw [s_eq, s_eq, ← Category.assoc, ← Functor.map_comp, Subsingleton.elim (a ≫ c') c]

/-- **The comparison maps are eventually inverse.** At every sufficiently late stage `l`, the
composite `X_l ⟶ U_l ⟶ X_p` is the transition morphism and `U_l ⟶ X_p ⟶ U` is the projection;
both hold at one stage by the injectivity half of Stacks 0CP4, applied to the systems `X_l` and
`U_l`, and then at every later stage. -/
lemma exists_eventually_inverse (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY) (small : Cardinal.mk I < B.cutoff.ord.cof) :
    ∃ (l₂ : Over M.n) (b : l₂ ⟶ M.pU) (c : l₂ ⟶ M.l₀), ∀ (l : Over M.n) (a : l ⟶ l₂),
      M.T l (a ≫ b) ≫ M.s l (a ≫ c) = (tailSystem GX leX).map ((a ≫ c).left ≫ M.c₀) ∧
      M.s l (a ≫ c) ≫ M.t₀ = pullback.snd ((tailSystem GY leY).map l.hom) M.u := by
  classical
  have hJ : Cardinal.mk (Over (op i₀)) < B.cutoff.ord.cof :=
    (cardinal_mk_over_op_le i₀).trans_lt small
  have hJh : ∀ j k : Over (op i₀), Cardinal.mk (j ⟶ k) < B.cutoff.ord.cof :=
    cardinal_mk_hom_over_op_lt B i₀
  have hJn : Cardinal.mk (Over M.n) < B.cutoff.ord.cof :=
    mk_over_lt B.aleph0_lt_cutoff_cof hJ hJh M.n
  have hJnh := cardinal_mk_hom_over_slice_lt (B := B) M.n
  have aYr := tailSystem_isAlgebraicSpace GY leY
  have aXr := tailSystem_isAlgebraicSpace GX leX
  have qcYr := tailSystem_isQuasiCompactSpace GY leY
  have qsYr := tailSystem_isAbsolutelyQuasiSeparated GY leY algY qsY small
  have fpUs : ∀ l : Over M.n, IsFinitePresentation B S hS (M.pr l) :=
    fun l => isFinitePresentation_fst_pullback (aYr _) (aYr M.n) M.algU _ M.u M.fp
  have lfpF := isLocallyOfFinitePresentation_maps_app F M.p
  let l₀' : Over M.n := IsCofiltered.min M.l₀ M.pU
  let c0 : l₀' ⟶ M.l₀ := IsCofiltered.minToLeft _ _
  let b0 : l₀' ⟶ M.pU := IsCofiltered.minToRight _ _
  let w0 : l₀'.left ⟶ M.p := c0.left ≫ M.c₀
  obtain ⟨kk, e2, heq⟩ := exists_stage_eq_of_relativelyLimitPreserving B S hS hZ
    (tailSystem GX leX) (tailCone GX leX) (isLimit_tailCone GX leX algX small) hJ hJh aXr
    (tailSystem_isQuasiCompactSpace GX leX)
    (tailSystem_isAbsolutelyQuasiSeparated GX leX algX qsX small)
    (fun a => tailSystem_map_isAffineHom GX leX a) algX (aXr M.p) (aYr M.p) (F.maps.app M.p) lfpF
    l₀'.left (M.T l₀' b0 ≫ M.s l₀' c0) ((tailSystem GX leX).map w0)
    (by rw [← Category.assoc, M.π_T, M.d_s, (tailCone GX leX).w])
    (by rw [Category.assoc, M.s_F l₀' c0 w0, ← Category.assoc, T_pr, F.maps.naturality])
  let l₁ : Over M.n := Over.mk (e2 ≫ l₀'.hom)
  let a1 : l₁ ⟶ l₀' := Over.homMk e2
  have hi : ∀ (l : Over M.n) (a : l ⟶ l₁) (b : l ⟶ M.pU) (c : l ⟶ M.l₀) (w : l.left ⟶ M.p),
      M.T l b ≫ M.s l c = (tailSystem GX leX).map w := by
    intro l a b c w
    rw [← M.s_map (a ≫ a1) c c0, ← Category.assoc, M.T_map (a ≫ a1) b b0, Category.assoc,
      show (a ≫ a1).left = a.left ≫ e2 from rfl, Functor.map_comp, Category.assoc, heq,
      ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      Subsingleton.elim ((a.left ≫ e2) ≫ w0) w]
  let c1 : l₁ ⟶ M.l₀ := a1 ≫ c0
  obtain ⟨l₂, a2, heq2⟩ := exists_stage_eq_of_relativelyLimitPreserving B S hS hZ M.Us M.cU
    (isLimitBaseChangeCone (tailSystem GY leY) M.n M.u (isLimit_tailCone GY leY algY small))
    hJn hJnh M.isAlgebraicSpace_Us
    (fun l => isQuasiCompactSpace_of_isFinitePresentation B S hS _ (aYr _) (qcYr _) (fpUs l))
    (fun l => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (M.isAlgebraicSpace_Us l)
      (qsYr _) (fpUs l).2.2)
    (fun a => isAffineHom_of_isPullback
      (isPullback_baseChangeSystem_map (tailSystem GY leY) M.n M.u a).flip
      (tailSystem_map_isAffineHom GY leY _))
    (isAlgebraicSpace_pullback B S hS _ _ algY M.algU (aYr M.n)) M.algU (aYr M.n) M.u M.fp.1 l₁
    (M.s l₁ c1 ≫ M.t₀) (pullback.snd _ _)
    (by
      have h1 : M.cU.π.app l₁ ≫ M.s l₁ c1 = M.e.inv ≫ (tailCone GX leX).π.app M.p := by
        rw [← M.d_s l₁ c1]
        simp only [d, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, h1, Category.assoc, M.t₀_lim, e_inv_toU, baseChangeCone_π_snd])
    (by
      rw [Category.assoc, M.t₀_u, F.maps.naturality, ← Category.assoc,
        M.s_F l₁ c1 (c1.left ≫ M.c₀), Category.assoc, ← Functor.map_comp, ← pullback.condition,
        Subsingleton.elim ((c1.left ≫ M.c₀) ≫ M.hp) l₁.hom])
  refine ⟨l₂, a2 ≫ a1 ≫ b0, a2 ≫ c1, fun l a => ⟨hi l (a ≫ a2) _ _ _, ?_⟩⟩
  rw [← M.s_map (a ≫ a2) (a ≫ a2 ≫ c1) c1, Functor.map_comp, Category.assoc, Category.assoc,
    heq2, baseChangeSystem_map_snd, baseChangeSystem_map_snd]

end FlatComparison

end Comparison

/-- In Situation 0CP6, let `f : X ⟶ Y` be a morphism of algebraic spaces quasi-separated over `B`,
let `GX` and `GY` be diagrams as in Stacks 0CP8 for `X` and `Y`, and let `(f_i)_{i ≥ i₀}` be a
morphism of the inverse systems of scheme-theoretic images `X = lim X_i` and `Y = lim Y_i` whose
limit is `f`, as in Stacks 0CPA. If `f` is flat and of finite presentation, then there is a stage
`i₃ ≥ i₀` such that for every `k ≥ i₃` the morphism `f_k` is flat, `X = Y ×_{Y_k} X_k`, and
`X_i = Y_i ×_{Y_k} X_k` for every `i ≥ k`. -/
@[stacks 0CPC]
theorem exists_isFlat_isPullback (algX : IsAlgebraicSpace B S hS X)
    (algY : IsAlgebraicSpace B S hS Y) (qsX : IsQuasiSeparated B S hS pX)
    (qsY : IsQuasiSeparated B S hS pY) (small : Cardinal.mk I < B.cutoff.ord.cof)
    {GX : GoodDiagram B S hS hZ D pX} {GY : GoodDiagram B S hS hZ D pY} {f : X ⟶ Y}
    {i₀ : I} {leX : GX.index ≤ i₀} {leY : GY.index ≤ i₀}
    (F : SystemMorphism GX GY f i₀ leX leY)
    (flat : IsFlat B S hS f) (fp : IsFinitePresentation B S hS f) :
    ∃ i₃ : I, i₀ ≤ i₃ ∧ ∀ k : Over (op i₀), i₃ ≤ k.left.unop →
      IsFlat B S hS (F.maps.app k) ∧
      IsPullback ((imageCone GX).π.app ((Over.map (homOfLE leX).op).obj k)) f
        (F.maps.app k) ((imageCone GY).π.app ((Over.map (homOfLE leY).op).obj k)) ∧
      ∀ (j : Over (op i₀)) (a : j ⟶ k),
        IsPullback ((imageSystem GX).map ((Over.map (homOfLE leX).op).map a)) (F.maps.app j)
          (F.maps.app k) ((imageSystem GY).map ((Over.map (homOfLE leY).op).map a)) := by
  obtain ⟨M⟩ := nonempty_flatComparison algX algY qsX qsY small F flat fp
  obtain ⟨l₂, b, c, hinv⟩ := M.exists_eventually_inverse algX algY qsX qsY small
  let Φ : ∀ (l : Over M.n), (l ⟶ l₂) → (M.Us.obj l ≅ (tailSystem GX leX).obj l.left) :=
    fun l a =>
      { hom := M.back algY small l (a ≫ c)
        inv := M.T l (a ≫ b)
        hom_inv_id := M.back_T algY small l (a ≫ b) (a ≫ c) (hinv l a).2
        inv_hom_id := M.T_back algY small l (a ≫ b) (a ≫ c) _ (hinv l a).1 }
  have hΦF : ∀ (l : Over M.n) (a : l ⟶ l₂), (Φ l a).hom ≫ F.maps.app l.left = M.pr l :=
    fun l a => M.back_F algY small l (a ≫ c)
  have hΦnat : ∀ {l l' : Over M.n} (a : l ⟶ l') (h : l ⟶ l₂) (h' : l' ⟶ l₂),
      M.Us.map a ≫ (Φ l' h').hom = (Φ l h).hom ≫ (tailSystem GX leX).map a.left := by
    intro l l' a h h'
    have h1 : (Φ l h).inv ≫ M.Us.map a = (tailSystem GX leX).map a.left ≫ (Φ l' h').inv :=
      M.T_map a _ _
    calc M.Us.map a ≫ (Φ l' h').hom
        = (Φ l h).hom ≫ ((Φ l h).inv ≫ M.Us.map a) ≫ (Φ l' h').hom := by simp
      _ = (Φ l h).hom ≫ (tailSystem GX leX).map a.left := by rw [h1]; simp
  refine ⟨l₂.left.left.unop, leOfHom l₂.left.hom.unop, fun k hk => ?_⟩
  let hkl : k ⟶ l₂.left := Over.homMk (homOfLE hk).op (Subsingleton.elim _ _)
  let lk : Over M.n := Over.mk (hkl ≫ l₂.hom)
  let ak : lk ⟶ l₂ := Over.homMk hkl
  have algUk := M.isAlgebraicSpace_Us lk
  refine ⟨?_, ?_, fun j a => ?_⟩
  · have hF : F.maps.app k = (Φ lk ak).inv ≫ M.pr lk := (M.T_pr lk (ak ≫ b)).symm
    rw [hF]
    have := Iso.isIso_inv (Φ lk ak)
    exact isFlat_comp B S hS (tailSystem_isAlgebraicSpace GX leX k) algUk
      (tailSystem_isAlgebraicSpace GY leY k) _ _ (isFlat_of_isIso _ algUk) (M.isFlat_pr lk)
  · refine IsPullback.of_iso (M.isPullback_d lk) (Iso.refl _) (Φ lk ak) (Iso.refl _)
      (Iso.refl _) ?_ ((Category.comp_id _).trans (Category.id_comp _).symm) ?_
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    · rw [Iso.refl_hom, Category.id_comp, ← M.π_T lk (ak ≫ b), Category.assoc]
      show _ ≫ (Φ lk ak).inv ≫ (Φ lk ak).hom = _
      rw [Iso.inv_hom_id, Category.comp_id]
      rfl
    · rw [Iso.refl_hom, Category.comp_id]
      exact (hΦF lk ak).symm
  · let lj : Over M.n := Over.mk (a ≫ lk.hom)
    let aj : lj ⟶ lk := Over.homMk a
    refine IsPullback.of_iso
      (isPullback_baseChangeSystem_map (tailSystem GY leY) M.n M.u aj)
      (Φ lj (aj ≫ ak)) (Φ lk ak) (Iso.refl _) (Iso.refl _) (hΦnat aj (aj ≫ ak) ak) ?_ ?_
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    · rw [Iso.refl_hom, Category.comp_id]
      exact (hΦF lj (aj ≫ ak)).symm
    · rw [Iso.refl_hom, Category.comp_id]
      exact (hΦF lk ak).symm

end SystemMorphism

end GoodDiagram

end AlgebraicGeometry.Space

end
