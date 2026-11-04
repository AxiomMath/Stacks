module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperArrowNoetherianApproximation

/-!
# Inverse systems bounded by the cutoff, with no condition on the cofinality

The descent results of the chapter on limits of algebraic spaces form, from an inverse system
`D` of algebraic spaces with affine transition morphisms, the limits of the affine charts of
its stages cut out by an affine test object; they hold when those limits lie in the big fppf
site. In this library their first forms ask for that through the index: fewer stages than the
cofinality of the site's cutoff. That bound cannot be met by the output of Stacks 07SU: for a
field `F` with `#F` equal to that cofinality, no inverse system of schemes of finite
presentation over `ℤ` with fewer stages has limit `Spec F`.

`AlgebraicGeometry.Space.IsCutoffBoundedSystem` asks instead for fewer stages than the cutoff
itself, a bound on the hom types, and `AlgebraicGeometry.Space.BaseChangeSizeBounded`: one
cardinal below the cutoff bounding all the base changes of the stages over a stage along a test
morphism. That is the hypothesis of the library's cofinality-free chart limit
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded`; it holds for a
system of algebraic spaces of finite type over `ℤ` indexed by fewer than `B.cutoff` stages.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_limitπ_of_isAffineHom_map_of_baseChangeSizeBounded`:
  Stacks 07SF, part (1), for such a system: the projections from the limit are affine.
* `AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone_of_isCutoffBoundedSystem`: Stacks 0CP9
  for a Noetherian limit system whose system is bounded by the cutoff.
* `AlgebraicGeometry.Space.baseChangeSizeBounded_comp` and
  `AlgebraicGeometry.Space.baseChangeSizeBounded_of_jointlyMono`: the bound passes to a
  reindexing, and to a system mapping to a reindexing of a bounded one by morphisms which are
  jointly monomorphic with the transition morphisms.
* `AlgebraicGeometry.Space.isCutoffBoundedSystem_tail` and
  `AlgebraicGeometry.Space.GoodDiagram.isCutoffBoundedSystem_imageSystem_tail`: the convention
  passes to a tail of a system and to the system of scheme-theoretic images of Stacks 0CP9 over
  a tail.
* `exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedApproximations` and
  `AlgebraicGeometry.Space.exists_descentSituation_arrow_isCutoffBoundedSystem_of_approximations`:
  the assembly of Stacks 0A0X and its form for Stacks 0D3D with the convention taken to be
  `AlgebraicGeometry.Space.IsCutoffBoundedSystem`, the hypotheses on Stacks 0CP9, tails and
  image systems discharged.

Nothing here is registered.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An inverse system bounded by the cutoff.** Fewer stages than the cutoff of the site, one
cardinal below the cutoff bounding the hom types, and uniformly bounded base changes of the
stages (`AlgebraicGeometry.Space.BaseChangeSizeBounded`). No condition on the cofinality of the
cutoff is involved. -/
def IsCutoffBoundedSystem {J : Type u} [Category.{u} J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  #J < B.cutoff ∧ (∃ ν : Cardinal.{u}, ν < B.cutoff ∧ ∀ i j : J, #(i ⟶ j) ≤ ν) ∧
    BaseChangeSizeBounded B S hS D

/-- An inverse system indexed by the opposite of a preorder with fewer elements than the cutoff
and with uniformly bounded base changes is bounded by the cutoff: its hom types have at most
one element. -/
theorem isCutoffBoundedSystem_of_preorder {I : Type u} [Preorder I]
    {D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hI : #I < B.cutoff)
    (hB : BaseChangeSizeBounded B S hS D) : IsCutoffBoundedSystem B S hS D :=
  ⟨(Cardinal.mk_congr equivToOpposite.symm).trans_lt hI,
    ⟨1, one_lt_aleph0.trans B.aleph0_lt_cutoff, fun _ _ => le_one_iff_subsingleton.2 inferInstance⟩,
    hB⟩

/-- The index set of an inverse system indexed by the opposite of a preorder and bounded by the
cutoff has fewer elements than the cutoff. -/
theorem IsCutoffBoundedSystem.mk_lt {I : Type u} [Preorder I]
    {D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hD : IsCutoffBoundedSystem B S hS D) :
    #I < B.cutoff :=
  (Cardinal.mk_congr equivToOpposite).trans_lt hD.1

/-! ### Stacks 07SF, part (1), with no condition on the cofinality -/

/-- **Stacks 07SF, part (1), for a system with uniformly bounded base changes.** Every
projection from the inverse limit of a cofiltered inverse system of presheaves with affine
transition morphisms is affine, when the index category has fewer objects than the site's
cutoff, its hom types are bounded by one cardinal below the cutoff, and the base changes of the
stages are uniformly bounded. The base change of `limit.π D i` along an affine test object is
the limit of the chart system at `i`, which lies in the site by
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded` and is affine.

This is `AlgebraicGeometry.Space.isAffineHom_limitπ` with the bound by the cofinality of the
cutoff traded for `AlgebraicGeometry.Space.BaseChangeSizeBounded`. -/
theorem isAffineHom_limitπ_of_isAffineHom_map_of_baseChangeSizeBounded
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {ν : Cardinal.{u}}
    (hSize : #I < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D) (i : I) : IsAffineHom B S hS (limit.π D i) := by
  intro Z g
  let L := (affineChartSystem B S hS i D Z g hAffine).limitBridgeOfBaseChangeSizeBounded
    hSize hν hHomSize hB
  refine ⟨⟨L.cone.pt, L.isAffine_pt⟩, L.toLimit, yoneda.preimage L.toBase, ?_⟩
  rw [Functor.map_preimage]
  exact L.isPullback

/-- **Stacks 07SF, part (1), for a system bounded by the cutoff.** -/
theorem isAffineHom_limitπ_of_isCutoffBoundedSystem {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : IsCutoffBoundedSystem B S hS D)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i : I) :
    IsAffineHom B S hS (limit.π D i) :=
  let ⟨hSize, ⟨_, hν, hHomSize⟩, hB⟩ := hD
  isAffineHom_limitπ_of_isAffineHom_map_of_baseChangeSizeBounded B S hS D hSize hν hHomSize
    hAffine hB i

/-! ### Passing the bound to other systems -/

/-- **Uniformly bounded base changes pass to a reindexing.** A base change over a stage `j₀` of
`F ⋙ D` along a test morphism is a base change over the stage `F j₀` of `D`, so the cardinal
bounding the latter bounds the former. -/
theorem baseChangeSizeBounded_comp {J I : Type u} [Category.{u} J] [Category.{u} I]
    (F : J ⥤ I) {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hB : BaseChangeSizeBounded B S hS D) : BaseChangeSizeBounded B S hS (F ⋙ D) := by
  intro j₀ Z g
  obtain ⟨μ, hμ, hbound⟩ := hB (F.obj j₀) Z g
  exact ⟨μ, hμ, fun k W p q hpq => hbound (Over.mk (F.map k.hom)) W p q hpq⟩

/-- **Uniformly bounded base changes pass along a jointly monomorphic comparison.** Let
`D : I ⥤ _` be a system of algebraic spaces with affine transitions and uniformly bounded base
changes, `F : J ⥤ I`, and `η : E ⟶ F ⋙ D` a morphism of systems such that for every transition
`a : j ⟶ k` of `E` the two morphisms `E.map a` and `η.app j` are jointly monomorphic. Then `E`
has uniformly bounded base changes: a base change `E k ×_{E j₀} h_Z` maps monomorphically to
the base change `D (F k) ×_{D (F j₀)} h_Z`, which is represented by an object of size at most
`μ`, so `max (2 ^ 2 ^ μ) μ` bounds it.

This contains `AlgebraicGeometry.Space.baseChangeSizeBounded_of_natTrans_mono`, for `F` the
identity. -/
theorem baseChangeSizeBounded_of_jointlyMono {J I : Type u} [Category.{u} J] [Category.{u} I]
    {F : J ⥤ I} {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {E : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (η : E ⟶ F ⋙ D)
    (hη : ∀ {j k : J} (a : j ⟶ k) {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
      (x y : T ⟶ E.obj j), x ≫ E.map a = y ≫ E.map a → x ≫ η.app j = y ≫ η.app j → x = y)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D) : BaseChangeSizeBounded B S hS E := by
  intro j₀ Z g
  obtain ⟨μ, hμ, hbound⟩ := hB (F.obj j₀) Z (g ≫ η.app j₀)
  refine ⟨max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ μ) μ,
    max_lt (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hμ)) hμ, fun k W p q hpq ↦ ?_⟩
  have hrep : yoneda.relativelyRepresentable ((F ⋙ D).map k.hom) :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (hD (F.obj k.left)) (hD (F.obj j₀)) (hAffine (F.map k.hom))).1
  let W' := hrep.pullback (g ≫ η.app j₀)
  have hcomm : (p ≫ η.app k.left) ≫ (F ⋙ D).map k.hom = q ≫ g ≫ η.app j₀ := by
    rw [Category.assoc, ← η.naturality, ← Category.assoc, hpq.w, Category.assoc]
  let m : yoneda.obj W ⟶ yoneda.obj W' :=
    (hrep.isPullback (g ≫ η.app j₀)).lift (p ≫ η.app k.left) q hcomm
  have hm : Mono m := by
    refine ⟨fun a b hab ↦ ?_⟩
    have hq : a ≫ q = b ≫ q := by
      simpa only [Category.assoc, m, IsPullback.lift_snd] using
        congrArg (· ≫ yoneda.map (hrep.snd (g ≫ η.app j₀))) hab
    have hη' : (a ≫ p) ≫ η.app k.left = (b ≫ p) ≫ η.app k.left := by
      simpa only [Category.assoc, m, IsPullback.lift_fst] using
        congrArg (· ≫ hrep.fst (g ≫ η.app j₀)) hab
    have hE : (a ≫ p) ≫ E.map k.hom = (b ≫ p) ≫ E.map k.hom := by
      rw [Category.assoc, Category.assoc, hpq.w, ← Category.assoc, ← Category.assoc, hq]
    exact hpq.hom_ext (hη k.hom _ _ hE hη') hq
  have hW'size : ((BigFppfOver.toScheme B S hS).obj W').size ≤ μ :=
    hbound (Over.mk (F.map k.hom)) W' _ _ (hrep.isPullback (g ≫ η.app j₀))
  exact (size_le_monoSizeBound_of_mono B S hS m hm).trans (max_le_max
    (Cardinal.power_le_power_left two_ne_zero
      ((Scheme.mk_le_two_pow_size _).trans (Cardinal.power_le_power_left two_ne_zero hW'size)))
    hW'size)

/-- A system with uniformly bounded base changes, indexed by the opposite of a preorder injecting
into the index set of a system bounded by the cutoff, is bounded by the cutoff. -/
private theorem isCutoffBoundedSystem_of_injective {J I : Type u} [Preorder J] [Preorder I]
    {D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {E : Jᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hD : IsCutoffBoundedSystem B S hS D) {f : J → I} (hf : Function.Injective f)
    (hE : BaseChangeSizeBounded B S hS E) : IsCutoffBoundedSystem B S hS E :=
  isCutoffBoundedSystem_of_preorder B S hS
    ((Cardinal.mk_le_of_injective hf).trans_lt (hD.mk_lt B S hS)) hE

/-- **The convention passes to a tail.** For a system indexed by the opposite of a directed set
and bounded by the cutoff, its restriction to the tail above `i₁` is bounded by the cutoff. This
is the hypothesis `hTail` of
`AlgebraicGeometry.Space.exists_descentSituation_arrow_conv_of_approximations` for
`AlgebraicGeometry.Space.IsCutoffBoundedSystem`. -/
theorem isCutoffBoundedSystem_tail {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i₁ : I)
    (hD : IsCutoffBoundedSystem B S hS D) :
    IsCutoffBoundedSystem B S hS ((tailInclusion i₁).op ⋙ D) :=
  isCutoffBoundedSystem_of_injective B S hS hD (Subtype.val_injective (p := (i₁ ≤ ·)))
    (baseChangeSizeBounded_comp B S hS _ hD.2.2)

/-! ### Stacks 0CP9 for a Noetherian limit system bounded by the cutoff -/

section NoetherianLimit

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirectedOrder I]

/-- The projections of the chosen limiting cone of a Noetherian limit system bounded by the
cutoff are affine morphisms, by
`AlgebraicGeometry.Space.isAffineHom_limitπ_of_isCutoffBoundedSystem`. -/
theorem NoetherianLimitSystem.isAffineHom_limitCone_π_of_isCutoffBoundedSystem
    (D : NoetherianLimitSystem B S hS hZ I) (hD : IsCutoffBoundedSystem B S hS D.system)
    (k : Iᵒᵖ) : IsAffineHom B S hS (D.limitCone.π.app k) := by
  rw [show D.limitCone.π.app k = D.limitIso.inv ≫ limit.π D.system k by
    rw [← D.limitIso_hom_comp_π, Iso.inv_hom_id_assoc]]
  exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _)
    (isAffineHom_limitπ_of_isCutoffBoundedSystem B S hS D.system hD D.transition_affine k)

namespace GoodDiagram

variable {D : NoetherianLimitSystem B S hS hZ I} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {f : X ⟶ D.limitCone.pt} (G : GoodDiagram B S hS hZ D f)

/-- **The stage maps of a good diagram over a system bounded by the cutoff are
quasi-compact.** As `AlgebraicGeometry.Space.GoodDiagram.isQuasiCompact_stageMap`, with the
affine projections of
`AlgebraicGeometry.Space.NoetherianLimitSystem.isAffineHom_limitCone_π_of_isCutoffBoundedSystem`.
-/
theorem isQuasiCompact_stageMap_of_isCutoffBoundedSystem
    (hD : IsCutoffBoundedSystem B S hS D.system) (j : Over (op G.index)) :
    IsQuasiCompact B S hS (stageMap G j) := by
  have hMalg : IsAlgebraicSpace B S hS
      (pullback (D.limitCone.π.app (op G.index)) G.modelMap) :=
    isAlgebraicSpace_pullback B S hS _ _ D.limit_isAlgebraicSpace G.model_isAlgebraicSpace
      (D.system_isAlgebraicSpace G.index)
  rw [← induced_comp_modelπ G j]
  exact isQuasiCompact_comp B S hS hMalg (isAlgebraicSpace_stageTarget G j) _ _
    (isQuasiCompact_of_isClosedImmersion' B S hS G.isClosedImmersion)
    (isQuasiCompact_of_isAffineHom' B S hS _ hMalg (isAlgebraicSpace_stageTarget G j)
      (isAffineHom_of_isPullback' B S hS (isPullback_modelπ G j)
        (D.isAffineHom_limitCone_π_of_isCutoffBoundedSystem hD j.left)))

/-- **The key inclusion of Stacks 0CP9, for a system bounded by the cutoff.** As
`AlgebraicGeometry.Space.GoodDiagram.imageInter_le_range_induced`, with the chart limit
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded` in place of the
one asking for fewer stages than the cofinality of the cutoff. -/
theorem imageInter_le_range_induced_of_isCutoffBoundedSystem (hX : IsAlgebraicSpace B S hS X)
    (hD : IsCutoffBoundedSystem B S hS D.system) :
    imageInter G ≤ Subfunctor.range G.induced := by
  obtain ⟨hSize, ⟨ν, hν, hHomSize⟩, hB⟩ := id hD
  obtain ⟨A, a, hAaff, hasurj, haetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS G.model
      G.model_isAlgebraicSpace).mp
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS
        (D.system_isAlgebraicSpace G.index) (D.noetherian G.index).1 G.isFiniteType.2)
  exact imageInter_le_range_induced_of_chart G (U₀ := ⟨A, hAaff⟩) a hX hasurj
    (etale_presheaf_of_isEtale' B S hS A a haetale)
    (isQuasiCompact_stageMap_of_isCutoffBoundedSystem G hD)
    ((modelChartSystem G (U₀ := ⟨A, hAaff⟩) a).limitBridgeOfBaseChangeSizeBounded
      hSize hν hHomSize hB)

/-- **Stacks 0CP9, for a system bounded by the cutoff.** In Situation 0CP6, for a diagram as in
Stacks 0CP8 over a Noetherian limit system whose system is bounded by the cutoff
(`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), the canonical cone from `X` to the inverse
system of the scheme-theoretic images `X_{i'}` of `X ⟶ B_{i'} ×_{B_i} W` is a limit cone.

This is `AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone` with the bound by the
cofinality of the cutoff traded for `AlgebraicGeometry.Space.IsCutoffBoundedSystem`, which the
system of Stacks 07SU can satisfy. With `Conv := IsCutoffBoundedSystem B _ hZ` it is the
hypothesis `h0CP9` of
`AlgebraicGeometry.Space.exists_descentSituation_arrow_of_approximations`. -/
def isLimit_imageCone_of_isCutoffBoundedSystem (hX : IsAlgebraicSpace B S hS X)
    (hD : IsCutoffBoundedSystem B S hS D.system) : IsLimit (imageCone G) :=
  isLimit_imageCone_of_imageInter_le G
    (imageInter_le_range_induced_of_isCutoffBoundedSystem G hX hD)

/-- For two stages `j ⟶ k` above the index of a good diagram, the transition morphism of the
image system and the inclusion of `X_j` followed by the projection to the stage of the system
are jointly monomorphic: `X_j` is a subspace of `B_j ×_{B_i} W`, whose second projection
factors through the transition. -/
theorem imageSystem_jointlyMono {j k : Over (op G.index)} (a : j ⟶ k)
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x y : T ⟶ (imageSystem G).obj j)
    (h₁ : x ≫ (imageSystem G).map a = y ≫ (imageSystem G).map a)
    (h₂ : x ≫ (stageImage G j).ι ≫ pullback.fst _ _ = y ≫ (stageImage G j).ι ≫ pullback.fst _ _) :
    x = y := by
  rw [← cancel_mono (stageImage G j).ι]
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h₂
  · simpa only [Category.assoc, imageSystem_map_ι_assoc, stageTargetMap_snd] using
      congrArg (· ≫ (stageImage G k).ι ≫ pullback.snd _ _) h₁

/-- The morphism from the system of scheme-theoretic images of a good diagram to the stages of
the system: the inclusion of `X_j` into `B_j ×_{B_i} W` followed by the first projection. -/
def imageSystemToStages : imageSystem G ⟶ Over.forget (op G.index) ⋙ D.system where
  app j := (stageImage G j).ι ≫ pullback.fst _ _
  naturality j k a := by
    rw [imageSystem_map_ι_assoc, stageTargetMap_fst, Category.assoc]
    rfl

/-- **The system of scheme-theoretic images has uniformly bounded base changes** when the
system of the good diagram has: by
`AlgebraicGeometry.Space.baseChangeSizeBounded_of_jointlyMono` along
`AlgebraicGeometry.Space.GoodDiagram.imageSystemToStages`. -/
theorem baseChangeSizeBounded_imageSystem (hB : BaseChangeSizeBounded B S hS D.system) :
    BaseChangeSizeBounded B S hS (imageSystem G) :=
  baseChangeSizeBounded_of_jointlyMono B S hS (imageSystemToStages G)
    (fun a _ x y h₁ h₂ => imageSystem_jointlyMono G a x y h₁ (by
      simpa only [imageSystemToStages, Category.assoc] using h₂))
    (fun i => D.system_isAlgebraicSpace i.unop) D.transition_affine hB

/-- **The convention passes to the system of scheme-theoretic images over a tail.** For a good
diagram over a Noetherian limit system bounded by the cutoff, the system of the
scheme-theoretic images `X_j` of Stacks 0CP9, indexed by the tail above the index of the
diagram, is bounded by the cutoff. With `Conv := IsCutoffBoundedSystem B _ hZ` this is the
hypothesis `hImage` of
`AlgebraicGeometry.Space.exists_descentSituation_arrow_conv_of_approximations`. -/
theorem isCutoffBoundedSystem_imageSystem_tail (hD : IsCutoffBoundedSystem B S hS D.system) :
    IsCutoffBoundedSystem B S hS (tailOver G.index ⋙ imageSystem G) :=
  isCutoffBoundedSystem_of_injective B S hS hD (Subtype.val_injective (p := (G.index ≤ ·)))
    (baseChangeSizeBounded_comp B S hS _ (baseChangeSizeBounded_imageSystem G hD.2.2))

end GoodDiagram

end NoetherianLimit

/-! ### Systems of finite type have uniformly bounded base changes -/

/-- **A system with affine transition morphisms locally of finite type has uniformly bounded
base changes.** A base change `W = D k ×_{D i₀} h_Z` of a transition along a test morphism is
represented by an object of the site whose morphism to `Z` is affine, hence quasi-compact, and
locally of finite type, so `size W ≤ size Z` (Stacks 04T7); the cardinal `size Z`, below the
cutoff, serves for every `k`. -/
theorem baseChangeSizeBounded_of_isLocallyOfFiniteType {I : Type u} [Category.{u} I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hlft : ∀ {i j : I} (f : i ⟶ j), IsLocallyOfFiniteType B S hS (D.map f)) :
    BaseChangeSizeBounded B S hS D := by
  intro i₀ Z g
  refine ⟨((BigFppfOver.toScheme B S hS).obj Z).size, Z.left.property, fun k W p q hpq => ?_⟩
  have haff := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
    (hD k.left) (hD i₀) (hAffine k.hom)
  have hl := (isLocallyOfFiniteType_iff_presheaf B S hS (hD k.left) (hD i₀) haff.1).1
    (hlft k.hom)
  have hpq' : IsPullback p (yoneda.map (yoneda.preimage q)) (D.map k.hom) g := by
    rwa [Functor.map_preimage]
  have h₁ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (yoneda.preimage q)) :=
    hl.property g p _ hpq'
  have h₂ : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage q)) :=
    haff.2.property g p _ hpq'
  exact Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage q))

/-- **A Noetherian approximation over `ℤ` has uniformly bounded base changes.** Its stages are
quasi-separated and of finite type over `ℤ`, so its transition morphisms are locally of finite
type (Stacks 0462), and they are affine; this is
`AlgebraicGeometry.Space.baseChangeSizeBounded_of_isLocallyOfFiniteType`. So the system of
Stacks 07SU is bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`) as soon
as its index set has fewer elements than the cutoff. -/
theorem NoetherianApproximation.baseChangeSizeBounded {hZ : B.Contains (⊤_ Scheme.{u})}
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X) :
    letI := A.preorder; BaseChangeSizeBounded B (⊤_ Scheme.{u}) hZ A.diagram := by
  let := A.preorder
  refine baseChangeSizeBounded_of_isLocallyOfFiniteType B _ hZ A.diagram A.isAlgebraicSpace
    A.isAffineHom_map fun {i j} f => ?_
  refine isLocallyOfFiniteType_of_comp B _ hZ (A.isAlgebraicSpace i) (A.isAlgebraicSpace j)
    (isAlgebraicSpace_terminal B _ hZ) (A.diagram.map f) (terminal.from _) ?_
  rw [terminal.comp_from]
  exact isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hZ
    (isFinitePresentation_terminal_of_isFiniteType_viewOverIntegers (A.isAlgebraicSpace i)
      (A.isAbsolutelyQuasiSeparated i) (A.isFiniteTypeOverIntegers i)).1.1

/-- **The system of a Noetherian approximation over `ℤ` with fewer stages than the cutoff is
bounded by the cutoff.** This reduces the hypothesis `hconv` of
`exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedApproximations` to the bound
`#A.I < B.cutoff` on the index set of the approximation Stacks 07SU produces. -/
theorem NoetherianApproximation.isCutoffBoundedSystem {hZ : B.Contains (⊤_ Scheme.{u})}
    {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
    (A : NoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ X) (hI : #A.I < B.cutoff) :
    letI := A.preorder; IsCutoffBoundedSystem B (⊤_ Scheme.{u}) hZ A.diagram :=
  let := A.preorder
  isCutoffBoundedSystem_of_preorder B _ hZ hI A.baseChangeSizeBounded

/-! ### The assembly of Stacks 0A0X under the cutoff bound -/

section Assembly

variable {B} (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0A0X, from the approximations it is proved with, under the cutoff bound.** This is
`AlgebraicGeometry.Space.exists_isLimit_isProper_isFinitePresentation_arrow_of_approximations` with
the convention `Conv` taken to be `AlgebraicGeometry.Space.IsCutoffBoundedSystem`, which asks for
no condition on the cofinality of the cutoff, so that the hypothesis `h0CP9` is discharged by
`AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone_of_isCutoffBoundedSystem`. The remaining
hypotheses are the inputs still owed: Stacks 07SU (`hW`, and `hconv` for the convention on its
approximation), Stacks 0A0W (`h0A0W`), and Stacks 07SK and 08K1 under the convention (`h07SK`,
`h08K1`). There is no bound on the index set of the conclusion. -/
theorem exists_isLimit_isProper_isFinitePresentation_arrow_of_cutoffBoundedApproximations
    (hW : ElementaryChart.HasWSystems B hZ)
    (hconv : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y →
      IsAbsolutelyQuasiSeparated B _ hZ hZ Y → HasNoetherianApproximation B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder;
        IsCutoffBoundedSystem B _ hZ A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀])))
    {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (hX : IsAlgebraicSpace B _ hZ X) (hY :
      IsAlgebraicSpace B _ hZ Y)
    (f : X ⟶ Y) (hf : IsProper B _ hZ f) (hYqc : IsQuasiCompactSpace B _ hZ Y)
    (hYqs : IsAbsolutelyQuasiSeparated B _ hZ hZ Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
      (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
      (eX : DX.limitCone.pt ≅ X) (eY : DY.limitCone.pt ≅ Y),
      (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
        eX.hom ≫ f ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
      (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
      (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) :=
  exists_isLimit_isProper_isFinitePresentation_arrow_of_approximations hZ
    (fun D => IsCutoffBoundedSystem B _ hZ D) hW hconv h0A0W h07SK h08K1
    (fun {_} _ _ _ _ hD {_ _} G hX => ⟨G.isLimit_imageCone_of_isCutoffBoundedSystem hX hD⟩)
    hX hY f hf hYqc hYqs

/-- **Stacks 0A0X over an affine target, in the shape the assembly of Stacks 0D3D consumes,
under the cutoff bound.** This is
`AlgebraicGeometry.Space.exists_descentSituation_arrow_conv_of_approximations` with the convention
`Conv` taken to be `AlgebraicGeometry.Space.IsCutoffBoundedSystem`, so that `h0CP9`, `hTail` and
`hImage` are discharged by
`AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone_of_isCutoffBoundedSystem`,
`AlgebraicGeometry.Space.isCutoffBoundedSystem_tail` and
`AlgebraicGeometry.Space.GoodDiagram.isCutoffBoundedSystem_imageSystem_tail`. The remaining
hypotheses `hW`, `hconv`, `h0A0W`, `h07SK` and `h08K1` are the inputs still owed. -/
theorem exists_descentSituation_arrow_isCutoffBoundedSystem_of_approximations
    (hW : ElementaryChart.HasWSystems B hZ)
    (hconv : ∀ Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B _ hZ Y →
      IsQuasiCompactSpace B _ hZ Y →
      IsAbsolutelyQuasiSeparated B _ hZ hZ Y → HasNoetherianApproximation B _ hZ hZ Y →
      ∃ A : NoetherianApproximation B _ hZ hZ Y, letI := A.preorder;
        IsCutoffBoundedSystem B _ hZ A.diagram)
    (h0A0W : ∀ {X Y : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (_ : IsAlgebraicSpace B _ hZ
      X) (_ : IsAlgebraicSpace B _ hZ Y)
      (f : X ⟶ Y) (_ : IsProper B _ hZ f) (_ : IsQuasiCompactSpace B _ hZ Y)
      (_ : IsAbsolutelyQuasiSeparated B _ hZ B.contains_terminal Y),
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (D : Iᵒᵖ ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) (t : D ⟶ (Functor.const
          Iᵒᵖ).obj Y) (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
        (∀ i, IsAlgebraicSpace B _ hZ (D.obj i)) ∧
        (∀ i, IsProper B _ hZ (t.app i) ∧ IsFinitePresentation B _ hZ (t.app i)) ∧
        (∀ ⦃i j : Iᵒᵖ⦄ (e : i ⟶ j), IsClosedImmersion B _ hZ (D.map e)) ∧
        (∀ i, IsClosedImmersion B _ hZ (π.app i)) ∧
        π ≫ t = (Functor.const Iᵒᵖ).map f ∧
        Nonempty (IsLimit (Cone.mk X π)))
    (h07SK : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ j, IsAlgebraicSpace B _ hZ (D.obj j)) →
      (∀ {i j : J} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      (∀ j, IsQuasiCompactSpace B _ hZ (D.obj j)) →
      (∀ j, IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj j)) →
      ∀ Y : Over (limit D), IsAlgebraicSpace B _ hZ Y.left → IsFinitePresentation B _ hZ Y.hom →
        ∃ (j : J) (Yⱼ : Over (D.obj j)), IsAlgebraicSpace B _ hZ Yⱼ.left ∧
          IsFinitePresentation B _ hZ Yⱼ.hom ∧
          Nonempty (Y ≅ (Over.pullback (limit.π D j)).obj Yⱼ))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤
      ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)), IsCutoffBoundedSystem B _ hZ D →
      (∀ i : I, IsAlgebraicSpace B _ hZ (D.obj (op i))) →
      (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom B _ hZ (D.map g)) →
      IsAlgebraicSpace B _ hZ (limit D) →
      ∀ (i₀ : I) {X₀ Y₀ : ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)} (a : X₀ ⟶ D.obj (op i₀))
        (b : Y₀ ⟶ D.obj (op i₀)) (f₀ : X₀ ⟶ Y₀)
        (hf₀ : f₀ ≫ b = a), IsAlgebraicSpace B _ hZ X₀ → IsAlgebraicSpace B _ hZ Y₀ →
        IsQuasiCompactSpace B _ hZ (D.obj (op i₀)) →
        IsAbsolutelyQuasiSeparated B _ hZ hZ (D.obj (op i₀)) →
        IsQuasiCompactSpace B _ hZ X₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ X₀ →
        IsQuasiCompactSpace B _ hZ Y₀ → IsAbsolutelyQuasiSeparated B _ hZ hZ Y₀ →
        IsProper B _ hZ (pullback.map (limit.π D (op i₀)) a (limit.π D (op i₀)) b (𝟙 _) f₀ (𝟙 _)
          (by simp) (by simp [hf₀])) →
        IsLocallyOfFiniteType B _ hZ f₀ →
        ∃ (i : I) (hi : i₀ ≤ i), IsProper B _ hZ (pullback.map (D.map (homOfLE hi).op) a
          (D.map (homOfLE hi).op) b (𝟙 _) f₀ (𝟙 _) (by simp) (by simp [hf₀]))) :
    ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        IsCutoffBoundedSystem B _ hZ DX.system ∧ IsCutoffBoundedSystem B _ hZ DY.system :=
  exists_descentSituation_arrow_conv_of_approximations hZ (fun D => IsCutoffBoundedSystem B _ hZ D)
    hW hconv h0A0W h07SK h08K1
    (fun {_} _ _ _ _ hD {_ _} G hX => ⟨G.isLimit_imageCone_of_isCutoffBoundedSystem hX hD⟩)
    (fun {_} _ _ D i₁ hD => isCutoffBoundedSystem_tail B _ hZ D i₁ hD)
    (fun {_} _ _ _ _ {_ _} G hD => G.isCutoffBoundedSystem_imageSystem_tail hD)

end Assembly

end AlgebraicGeometry.Space

end
