module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.GluedRelationLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.GluedRelationSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleDescentAlongPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FiniteOrderChartLift

/-!
# The limit of the glued relations is `V ×_X V`

The closing claim of the proof of Stacks 07SU: with `R_i = V_i ∪_{W_i} (W_i ×_{U_i} W_i)`,
"`lim W_i ×_{U_i} W_i = W ×_U W` and `V = lim V_i`, so that `R = lim R_i` is the union of
`W ×_U W` and `V` glued along `W`", and since `V ×_X V` is the union of the opens `Δ(V)` and
`W ×_U W` meeting along `Δ(W)`, "there exists a unique isomorphism `R ≅ V ×_X V` compatible with
the projections to `V`". This file proves it on the big fppf site of a scheme `S`, for the system
of glued relations `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.etaleRelationSystem`.

The inputs at the limit are those of the proof: `V = lim V_i` and `W = lim W_i` (limits of
schemes), an open subspace `U ⟶ X` (any monomorphism of presheaves) over which `V ⟶ X` restricts
to `W ⟶ U` by a cartesian square, the identification `W = U ×_{U_i} W_i` at every stage, a
represented kernel pair `K = V ×_X V` of an étale `V ⟶ X`, and the geometric input that `K` is
covered by the diagonal and by the inverse image of `W` (property (6) of the proof).

## Main definitions

* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData`: the inputs at the limit.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData.relCone`: the cone from `K` to
  the glued relations.

## Main results

* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData.isLimit_kernelPairCone`:
  `lim W_i ×_{U_i} W_i = W ×_X W`, the inverse image of `W` in `K`.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData.isLimit_relCone`: `K` is the
  limit of the glued relations, in schemes.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData.relCone_π_source` and
  `relCone_π_target`: compatibly with the two projections to `V`.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.LimitData.hasNoetherianApproximation`:
  over `Spec ℤ`, under finiteness hypotheses on the system, `X` has a Noetherian approximation.

The results on `relCone` are the hypotheses `hR`, `hs` and `ht` of
`AlgebraicGeometry.Space.EtaleRelationSystem.hasNoetherianApproximation`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace KernelPairSystem

variable {J : Type u} [Category.{u} J] {Q : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (W : J ⥤ BigFppfOver B S hS) (b : W ⋙ yoneda ⟶ Q)
  (hb : ∀ j, yoneda.relativelyRepresentable (b.app j))

/-- A point of the kernel pair at a stage, from two points of `W_j` with the same image in
`U_j`. -/
noncomputable def liftApp {T : BigFppfOver B S hS} (j : J) (x y : T ⟶ W.obj j)
    (h : yoneda.map x ≫ b.app j = yoneda.map y ≫ b.app j) : T ⟶ objObj W b hb j :=
  yoneda.preimage ((isPullback_app W b hb j).lift (yoneda.map x) (yoneda.map y) h)

/-- The first projection of `liftApp W b hb j x y h` is `x`. -/
@[reassoc (attr := simp)]
lemma liftApp_fstApp {T : BigFppfOver B S hS} (j : J) (x y : T ⟶ W.obj j)
    (h : yoneda.map x ≫ b.app j = yoneda.map y ≫ b.app j) :
    liftApp W b hb j x y h ≫ fstApp W b hb j = x := by
  apply yoneda.map_injective
  rw [Functor.map_comp, liftApp, Functor.map_preimage, IsPullback.lift_fst]

/-- The second projection of `liftApp W b hb j x y h` is `y`. -/
@[reassoc (attr := simp)]
lemma liftApp_sndApp {T : BigFppfOver B S hS} (j : J) (x y : T ⟶ W.obj j)
    (h : yoneda.map x ≫ b.app j = yoneda.map y ≫ b.app j) :
    liftApp W b hb j x y h ≫ sndApp W b hb j = y := by
  apply yoneda.map_injective
  rw [Functor.map_comp, liftApp, Functor.map_preimage, IsPullback.lift_snd]

end KernelPairSystem

namespace GluedNeighbourhoodRelationData

variable {J : Type u} [Category.{u} J] (G : GluedNeighbourhoodRelationData B S hS J)

/-- **The inputs of the closing step of the proof of Stacks 07SU.** The limits `V = lim V_i`
and `W = lim W_i` in schemes, with the inclusion `W ⟶ V`; a presheaf `U` (the open subspace of
`X`) with compatible maps to the `U_i` such that `W = U ×_{U_i} W_i` at every stage; an étale
`f : V ⟶ X` restricting to `W ⟶ U` over a monomorphism `U ⟶ X` by a cartesian square; a
represented kernel pair `K = V ×_X V` of `f` with its diagonal; and the property that every point
of `K` lies on the diagonal or over `W`. -/
structure LimitData where
  /-- The cone exhibiting `V = lim V_i`. -/
  coneV : Cone G.ambient
  /-- `V` is the limit of the `V_i` in schemes. -/
  isLimitV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone coneV)
  /-- The cone exhibiting `W = lim W_i`. -/
  coneW : Cone G.nbhd
  /-- `W` is the limit of the `W_i` in schemes. -/
  isLimitW : IsLimit ((BigFppfOver.toScheme B S hS).mapCone coneW)
  /-- The inclusion `W ⟶ V`. -/
  inclL : coneW.pt ⟶ coneV.pt
  /-- The inclusion `W ⟶ V` is compatible with the inclusions `W_j ⟶ V_j`. -/
  inclL_π : ∀ j, inclL ≫ coneV.π.app j = coneW.π.app j ≫ G.incl.app j
  /-- The open subspace `U` of `X`. -/
  baseL : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The maps `U ⟶ U_i`. -/
  baseπ : (Functor.const J).obj baseL ⟶ G.base
  /-- The map `W ⟶ U`. -/
  toBaseL : yoneda.obj coneW.pt ⟶ baseL
  /-- `W = U ×_{U_i} W_i` at every stage. -/
  isPullback_toBaseL : ∀ j,
    IsPullback toBaseL (yoneda.map (coneW.π.app j)) (baseπ.app j) (G.toBase.app j)
  /-- The algebraic space `X`. -/
  space : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The étale morphism `f : V ⟶ X`. -/
  atlas : yoneda.obj coneV.pt ⟶ space
  /-- `f` is étale. -/
  etale_atlas : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf atlas
  /-- The open immersion `U ⟶ X`. -/
  baseIncl : baseL ⟶ space
  /-- `U ⟶ X` is a monomorphism. -/
  mono_baseIncl : Mono baseIncl
  /-- `W = V ×_X U`. -/
  isPullback_baseIncl : IsPullback toBaseL (yoneda.map inclL) baseIncl atlas
  /-- The kernel pair `K = V ×_X V`. -/
  kernel : BigFppfOver B S hS
  /-- The first projection `K ⟶ V`. -/
  kernelFst : kernel ⟶ coneV.pt
  /-- The second projection `K ⟶ V`. -/
  kernelSnd : kernel ⟶ coneV.pt
  /-- `K` is the fibre product `V ×_X V`. -/
  isPullback_kernel : IsPullback (yoneda.map kernelFst) (yoneda.map kernelSnd) atlas atlas
  /-- The diagonal `V ⟶ K`. -/
  kernelDiag : coneV.pt ⟶ kernel
  /-- The diagonal is a section of the first projection. -/
  kernelDiag_fst : kernelDiag ≫ kernelFst = 𝟙 _
  /-- The diagonal is a section of the second projection. -/
  kernelDiag_snd : kernelDiag ≫ kernelSnd = 𝟙 _
  /-- Every point of `K` lies on the diagonal or over `W` (property (6) of the proof). -/
  cover : ∀ k : (BigFppfOver.toScheme B S hS).obj kernel,
    k ∈ Set.range ((BigFppfOver.toScheme B S hS).map kernelDiag) ∨
      (BigFppfOver.toScheme B S hS).map kernelSnd k ∈
        Set.range ((BigFppfOver.toScheme B S hS).map inclL)

namespace LimitData

variable {G} (L : G.LimitData)

attribute [instance] mono_baseIncl

/-- The inclusion `W ⟶ V` of schemes is compatible with the inclusions `W_j ⟶ V_j`. -/
lemma inclL_π_toScheme (j : J) :
    (BigFppfOver.toScheme B S hS).map L.inclL ≫
        ((BigFppfOver.toScheme B S hS).mapCone L.coneV).π.app j =
    ((BigFppfOver.toScheme B S hS).mapCone L.coneW).π.app j ≫ G.inclScheme.app j := by
  simp only [Functor.mapCone_π_app, ← CategoryTheory.Functor.map_comp, L.inclL_π]
  rfl

/-- The transition maps `V_i ⟶ V_j` pull the open `W_j` back to `W_i`. -/
lemma hα : ∀ ⦃i j : J⦄ (u : i ⟶ j),
    G.ambientScheme.map u ⁻¹ᵁ (G.inclScheme.app j).opensRange =
      (G.inclScheme.app i).opensRange :=
  fun _ _ u ↦ preimage_opensRange_of_isPullback (G.isPullback_incl u).flip

/-- The transition maps of the kernel pairs `W_i ×_{U_i} W_i` pull the diagonal of stage `j` back
to the diagonal of stage `i`. -/
lemma hβ : ∀ ⦃i j : J⦄ (u : i ⟶ j),
    G.kernelPairScheme.map u ⁻¹ᵁ (G.diagScheme.app j).opensRange =
      (G.diagScheme.app i).opensRange :=
  fun _ _ u ↦ preimage_opensRange_of_isPullback
    (isPullback_section_of_isPullback G.diagScheme G.sndScheme G.diagScheme_sndScheme u
      (KernelPairSystem.isPullback_snd G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep)
        G.isPullback_toBase u)).flip

/-- The second projection `K ⟶ V` is étale. -/
lemma etale_kernelSnd : Etale ((BigFppfOver.toScheme B S hS).map L.kernelSnd) :=
  L.etale_atlas.property L.atlas _ _ L.isPullback_kernel

/-- The first projection `K ⟶ V` is étale. -/
lemma etale_kernelFst : Etale ((BigFppfOver.toScheme B S hS).map L.kernelFst) :=
  L.etale_atlas.property L.atlas _ _ L.isPullback_kernel.flip

/-- The diagonal is a section of the second projection, in schemes. -/
lemma toScheme_kernelDiag_kernelSnd :
    (BigFppfOver.toScheme B S hS).map L.kernelDiag ≫ (BigFppfOver.toScheme B S hS).map
        L.kernelSnd = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, L.kernelDiag_snd, CategoryTheory.Functor.map_id]

/-- The diagonal is a section of the first projection, in schemes. -/
lemma toScheme_kernelDiag_kernelFst :
    (BigFppfOver.toScheme B S hS).map L.kernelDiag ≫ (BigFppfOver.toScheme B S hS).map
        L.kernelFst = 𝟙 _ := by
  rw [← CategoryTheory.Functor.map_comp, L.kernelDiag_fst, CategoryTheory.Functor.map_id]

variable [IsCofiltered J]

/-- The inclusion `W ⟶ V` is an open immersion. -/
instance isOpenImmersion_inclL :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map L.inclL) :=
  isOpenImmersion_ιL G.inclScheme hα L.isLimitV L.isLimitW _ L.inclL_π_toScheme

/-- The diagonal `V ⟶ K` is an open immersion. -/
instance isOpenImmersion_kernelDiag :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map L.kernelDiag) := by
  have := L.etale_kernelSnd
  exact isOpenImmersion_of_section_of_etale _ _ L.toScheme_kernelDiag_kernelSnd

/-- The inverse image `W ×_X W` of `W` in `K`. -/
noncomputable abbrev overW : ((BigFppfOver.toScheme B S hS).obj L.kernel).Opens :=
  (BigFppfOver.toScheme B S hS).map L.kernelSnd ⁻¹ᵁ
    ((BigFppfOver.toScheme B S hS).map L.inclL).opensRange

/-- The second projection `W ×_X W ⟶ W`, of schemes. -/
noncomputable def overWSndS :
    (L.overW : Scheme.{u}) ⟶ (BigFppfOver.toScheme B S hS).obj L.coneW.pt :=
  IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map L.inclL)
    (L.overW.ι ≫ (BigFppfOver.toScheme B S hS).map L.kernelSnd) (by
    rintro _ ⟨x, rfl⟩
    exact x.2)

/-- The second projection `W ×_X W ⟶ W` followed by `W ⟶ V` is the second projection of `K`
restricted to `W ×_X W`. -/
@[reassoc]
lemma overWSndS_inclL :
    L.overWSndS ≫ (BigFppfOver.toScheme B S hS).map L.inclL = L.overW.ι ≫
        (BigFppfOver.toScheme B S hS).map L.kernelSnd :=
  IsOpenImmersion.lift_fac _ _ _

/-- A morphism over `S` commutes with the structure morphisms to `S`, in schemes. -/
private lemma inclusion_map_hom_eq {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    B.inclusion.map X.hom = (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map Y.hom := by
  change _ = B.inclusion.map f.left ≫ _
  rw [← B.inclusion.map_comp, Over.w]

/-- The second projection `W ×_X W ⟶ W` is a morphism over `S`. -/
lemma hom_overWSndS : L.overWSndS ≫ B.inclusion.map L.coneW.pt.hom =
    L.overW.ι ≫ B.inclusion.map L.kernel.hom := by
  rw [inclusion_map_hom_eq L.inclL, ← Category.assoc, L.overWSndS_inclL, Category.assoc,
    inclusion_map_hom_eq L.kernelSnd]

/-- The scheme `W ×_X W` lies in the big fppf site. -/
lemma contains_overW : B.Contains (L.overW : Scheme.{u}) :=
  Scheme.size_lt_of_isOpenImmersion L.overW.ι L.kernel.left.property

/-- `W ×_X W`, as an object of the site. -/
noncomputable abbrev overWObj : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS L.contains_overW (L.overW.ι ≫ B.inclusion.map L.kernel.hom)

/-- The inclusion `W ×_X W ⟶ K`. -/
noncomputable def overWι : L.overWObj ⟶ L.kernel :=
  Over.homMk (ObjectProperty.homMk L.overW.ι) (ObjectProperty.hom_ext _ rfl)

/-- The underlying morphism of schemes of `overWι` is the inclusion of the open `W ×_X W`. -/
lemma toScheme_map_overWι : (BigFppfOver.toScheme B S hS).map L.overWι = L.overW.ι := rfl

/-- The inclusion `W ×_X W ⟶ K` is an open immersion. -/
instance isOpenImmersion_overWι :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map L.overWι) :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion L.overW.ι)

/-- The second projection `W ×_X W ⟶ W`. -/
noncomputable def overWSnd : L.overWObj ⟶ L.coneW.pt :=
  Over.homMk (ObjectProperty.homMk L.overWSndS) (ObjectProperty.hom_ext _ L.hom_overWSndS)

/-- The underlying morphism of schemes of `overWSnd` is `overWSndS`. -/
lemma toScheme_map_overWSnd : (BigFppfOver.toScheme B S hS).map L.overWSnd = L.overWSndS := rfl

/-- The second projection `W ×_X W ⟶ W` followed by `W ⟶ V` is the second projection of `K`
restricted to `W ×_X W`. -/
@[reassoc]
lemma overWSnd_inclL : L.overWSnd ≫ L.inclL = L.overWι ≫ L.kernelSnd :=
  (BigFppfOver.toScheme B S hS).map_injective L.overWSndS_inclL

/-- The maps `W ×_X W ⟶ W ⟶ U ⟶ X` and `W ×_X W ⟶ K ⟶ V ⟶ X`, through the second and first
projections respectively, agree. -/
lemma yoneda_overWι_kernelFst_atlas :
    (yoneda.map L.overWSnd ≫ L.toBaseL) ≫ L.baseIncl =
      yoneda.map (L.overWι ≫ L.kernelFst) ≫ L.atlas := by
  rw [Category.assoc, L.isPullback_baseIncl.w, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, overWSnd_inclL, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc, L.isPullback_kernel.w]

/-- The first projection `W ×_X W ⟶ W`, the restriction of the first projection of `K`: it maps
`W ×_X W` into `W` because `W = V ×_X U` and both projections of `K` agree in `X`. -/
noncomputable def overWFst : L.overWObj ⟶ L.coneW.pt :=
  yoneda.preimage (L.isPullback_baseIncl.lift (yoneda.map L.overWSnd ≫ L.toBaseL)
    (yoneda.map (L.overWι ≫ L.kernelFst)) L.yoneda_overWι_kernelFst_atlas)

/-- The first projection `W ×_X W ⟶ W` followed by `W ⟶ V` is the first projection of `K`
restricted to `W ×_X W`. -/
@[reassoc]
lemma overWFst_inclL : L.overWFst ≫ L.inclL = L.overWι ≫ L.kernelFst := by
  apply yoneda.map_injective
  rw [CategoryTheory.Functor.map_comp, overWFst, Functor.map_preimage, IsPullback.lift_snd]

/-- The two projections `W ×_X W ⟶ W` agree in `U`. -/
@[reassoc]
lemma yoneda_overWFst_toBaseL :
    yoneda.map L.overWFst ≫ L.toBaseL = yoneda.map L.overWSnd ≫ L.toBaseL := by
  rw [overWFst, Functor.map_preimage, IsPullback.lift_fst]

/-- **`W ×_X W` is the kernel pair of `W ⟶ U`.** -/
theorem isPullback_overW :
    IsPullback (yoneda.map L.overWFst) (yoneda.map L.overWSnd) L.toBaseL L.toBaseL := by
  have hA : IsPullback (yoneda.map L.overWSnd) (yoneda.map L.overWι) (yoneda.map L.inclL)
      (yoneda.map L.kernelSnd) := by
    refine Functor.map_isPullback yoneda (isPullback_of_isPullback_toScheme ?_)
    refine IsOpenImmersion.isPullback _ _ _ _ L.overWSndS_inclL.symm ?_
    exact (Scheme.Opens.opensRange_ι L.overW).symm
  have hcomp := hA.paste_vert L.isPullback_kernel.flip
  have e₁ : yoneda.map L.overWι ≫ yoneda.map L.kernelFst =
      yoneda.map L.overWFst ≫ yoneda.map L.inclL := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, overWFst_inclL]
  have hcomp' := hcomp.flip
  rw [e₁, ← L.isPullback_baseIncl.w] at hcomp'
  exact IsPullback.of_right hcomp' L.yoneda_overWFst_toBaseL L.isPullback_baseIncl.flip

/-! ### `lim W_i ×_{U_i} W_i = W ×_X W` -/

/-- The leg `W ×_X W ⟶ W_j ×_{U_j} W_j`. -/
noncomputable def kernelPairLeg (j : J) : L.overWObj ⟶ G.kernelPair.obj j :=
  KernelPairSystem.liftApp G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep) j
    (L.overWFst ≫ L.coneW.π.app j) (L.overWSnd ≫ L.coneW.π.app j) (by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
        Category.assoc, ← (L.isPullback_toBaseL j).w, L.yoneda_overWFst_toBaseL_assoc])

/-- The leg `W ×_X W ⟶ W_j ×_{U_j} W_j` followed by the first projection is the first projection
followed by `W ⟶ W_j`. -/
@[reassoc (attr := simp)]
lemma kernelPairLeg_fst (j : J) :
    L.kernelPairLeg j ≫ G.fst.app j = L.overWFst ≫ L.coneW.π.app j :=
  KernelPairSystem.liftApp_fstApp _ _ _ _ _ _ _

/-- The leg `W ×_X W ⟶ W_j ×_{U_j} W_j` followed by the second projection is the second
projection followed by `W ⟶ W_j`. -/
@[reassoc (attr := simp)]
lemma kernelPairLeg_snd (j : J) :
    L.kernelPairLeg j ≫ G.snd.app j = L.overWSnd ≫ L.coneW.π.app j :=
  KernelPairSystem.liftApp_sndApp _ _ _ _ _ _ _

/-- The legs `W ×_X W ⟶ W_j ×_{U_j} W_j` are compatible with the transition maps. -/
lemma kernelPairLeg_map {j k : J} (u : j ⟶ k) :
    L.kernelPairLeg j ≫ G.kernelPair.map u = L.kernelPairLeg k := by
  refine KernelPairSystem.hom_ext_app G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep) ?_ ?_
  · show L.kernelPairLeg j ≫ G.kernelPair.map u ≫ G.fst.app k = L.kernelPairLeg k ≫ G.fst.app k
    rw [G.fst.naturality u, kernelPairLeg_fst_assoc, kernelPairLeg_fst, L.coneW.w u]
  · show L.kernelPairLeg j ≫ G.kernelPair.map u ≫ G.snd.app k = L.kernelPairLeg k ≫ G.snd.app k
    rw [G.snd.naturality u, kernelPairLeg_snd_assoc, kernelPairLeg_snd, L.coneW.w u]

/-- The cone from `W ×_X W` to the kernel pairs `W_j ×_{U_j} W_j`, in schemes. -/
noncomputable abbrev kernelPairCone : Cone G.kernelPairScheme where
  pt := (L.overW : Scheme.{u})
  π :=
    { app j := (BigFppfOver.toScheme B S hS).map (L.kernelPairLeg j)
      naturality {j k} u := by
        change 𝟙 _ ≫ (BigFppfOver.toScheme B S hS).map (L.kernelPairLeg k) =
          (BigFppfOver.toScheme B S hS).map (L.kernelPairLeg j) ≫
              (BigFppfOver.toScheme B S hS).map (G.kernelPair.map u)
        rw [Category.id_comp, ← CategoryTheory.Functor.map_comp, L.kernelPairLeg_map] }

/-- The legs of `kernelPairCone` are the morphisms of schemes underlying `kernelPairLeg`. -/
lemma kernelPairCone_π_app (j : J) :
    L.kernelPairCone.π.app j = (BigFppfOver.toScheme B S hS).map (L.kernelPairLeg j) := rfl

/-- At every stage, `W ×_X W` is `W ×_{W_j} (W_j ×_{U_j} W_j)` along the second projections. -/
theorem isPullback_kernelPairLeg (j : J) :
    IsPullback (yoneda.map (L.kernelPairLeg j)) (yoneda.map L.overWSnd)
      (yoneda.map (G.snd.app j)) (yoneda.map (L.coneW.π.app j)) := by
  have h₁ := L.isPullback_overW.flip.paste_vert (L.isPullback_toBaseL j)
  have e₁ : yoneda.map (L.kernelPairLeg j) ≫ yoneda.map (G.fst.app j) =
      yoneda.map L.overWFst ≫ yoneda.map (L.coneW.π.app j) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, kernelPairLeg_fst]
  rw [← e₁, (L.isPullback_toBaseL j).w] at h₁
  refine IsPullback.of_right h₁.flip ?_ (KernelPairSystem.isPullback_app G.nbhd G.toBase
    (fun j ↦ (G.etale_toBase j).rep) j)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, kernelPairLeg_snd]

/-- **`lim W_i ×_{U_i} W_i = W ×_X W`**, in schemes. -/
noncomputable def isLimit_kernelPairCone : IsLimit L.kernelPairCone := by
  have : IsConnected J := IsCofiltered.isConnected J
  refine isLimitOfIsPullbackOfIsConnected G.sndScheme L.kernelPairCone
      ((BigFppfOver.toScheme B S hS).mapCone L.coneW)
    { hom := (BigFppfOver.toScheme B S hS).map L.overWSnd
      w := fun j ↦ ?_ } (fun j ↦ ?_) L.isLimitW
  · change (BigFppfOver.toScheme B S hS).map L.overWSnd ≫ (BigFppfOver.toScheme B S hS).map
      (L.coneW.π.app j) =
      (BigFppfOver.toScheme B S hS).map (L.kernelPairLeg j) ≫ (BigFppfOver.toScheme B S hS).map
          (G.snd.app j)
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, kernelPairLeg_snd]
  · exact isPullback_toScheme_of_isPullback_yoneda _ _ _ (L.isPullback_kernelPairLeg j)

/-! ### `lim R_i = V ×_X V` -/

/-- The diagonal `W ⟶ W ×_X W`, of schemes. -/
noncomputable def overWDiagS :
    (BigFppfOver.toScheme B S hS).obj L.coneW.pt ⟶ (L.overW : Scheme.{u}) :=
  IsOpenImmersion.lift L.overW.ι ((BigFppfOver.toScheme B S hS).map (L.inclL ≫ L.kernelDiag)) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((BigFppfOver.toScheme B S hS).map (L.inclL ≫ L.kernelDiag) ≫
      (BigFppfOver.toScheme B S hS).map L.kernelSnd) x ∈
      Set.range ((BigFppfOver.toScheme B S hS).map L.inclL)
    rw [← CategoryTheory.Functor.map_comp, Category.assoc, L.kernelDiag_snd,
      Category.comp_id]
    exact ⟨x, rfl⟩)

/-- The diagonal `W ⟶ W ×_X W` followed by the inclusion into `K` is `W ⟶ V ⟶ K`. -/
@[reassoc]
lemma overWDiagS_ι :
    L.overWDiagS ≫ L.overW.ι =
      (BigFppfOver.toScheme B S hS).map L.inclL ≫ (BigFppfOver.toScheme B S hS).map L.kernelDiag :=
  (IsOpenImmersion.lift_fac _ _ _).trans
    (CategoryTheory.Functor.map_comp _ _ _)

/-- The diagonal `W ⟶ W ×_X W` is a morphism over `S`. -/
lemma hom_overWDiagS : L.overWDiagS ≫ L.overW.ι ≫ B.inclusion.map L.kernel.hom =
    B.inclusion.map L.coneW.pt.hom := by
  rw [overWDiagS_ι_assoc]
  erw [← inclusion_map_hom_eq L.kernelDiag, ← inclusion_map_hom_eq L.inclL]

/-- The diagonal `W ⟶ W ×_X W`. -/
noncomputable def overWDiag : L.coneW.pt ⟶ L.overWObj :=
  BigFppfOver.homMk B S hS L.contains_overW _ L.overWDiagS L.hom_overWDiagS

/-- The underlying morphism of schemes of `overWDiag` is `overWDiagS`. -/
lemma toScheme_map_overWDiag : (BigFppfOver.toScheme B S hS).map L.overWDiag = L.overWDiagS := rfl

/-- The diagonal `W ⟶ W ×_X W` followed by the inclusion into `K` is `W ⟶ V ⟶ K`. -/
lemma overWDiag_overWι : L.overWDiag ≫ L.overWι = L.inclL ≫ L.kernelDiag :=
  (BigFppfOver.toScheme B S hS).map_injective L.overWDiagS_ι

/-- The diagonal `W ⟶ W ×_X W` is a section of a projection which restricts a projection of `K`
to `W`. -/
private lemma overWDiag_comp_eq_id (p : L.overWObj ⟶ L.coneW.pt) (q : L.kernel ⟶ L.coneV.pt)
    (hp : p ≫ L.inclL = L.overWι ≫ q) (hq : L.kernelDiag ≫ q = 𝟙 _) : L.overWDiag ≫ p = 𝟙 _ := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [← cancel_mono ((BigFppfOver.toScheme B S hS).map L.inclL), CategoryTheory.Functor.map_id,
    Category.id_comp, ← CategoryTheory.Functor.map_comp, Category.assoc, hp, ← Category.assoc,
    overWDiag_overWι, Category.assoc, hq, Category.comp_id]

/-- The diagonal `W ⟶ W ×_X W` is a section of the first projection. -/
lemma overWDiag_overWFst : L.overWDiag ≫ L.overWFst = 𝟙 _ :=
  L.overWDiag_comp_eq_id _ _ L.overWFst_inclL L.kernelDiag_fst

/-- The diagonal `W ⟶ W ×_X W` is a section of the second projection. -/
lemma overWDiag_overWSnd : L.overWDiag ≫ L.overWSnd = 𝟙 _ :=
  L.overWDiag_comp_eq_id _ _ L.overWSnd_inclL L.kernelDiag_snd

/-- The diagonal of `W ×_X W` maps to the diagonal of `W_j ×_{U_j} W_j`. -/
lemma overWDiag_kernelPairLeg (j : J) :
    L.overWDiag ≫ L.kernelPairLeg j = L.coneW.π.app j ≫ G.diag.app j := by
  refine KernelPairSystem.hom_ext_app G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep) ?_ ?_
  · show L.overWDiag ≫ L.kernelPairLeg j ≫ G.fst.app j = L.coneW.π.app j ≫ G.diag.app j ≫
      G.fst.app j
    rw [kernelPairLeg_fst, ← Category.assoc, overWDiag_overWFst, Category.id_comp,
      ← NatTrans.comp_app, KernelPairSystem.diag_fst, NatTrans.id_app, Category.comp_id]
  · show L.overWDiag ≫ L.kernelPairLeg j ≫ G.snd.app j = L.coneW.π.app j ≫ G.diag.app j ≫
      G.snd.app j
    rw [kernelPairLeg_snd, ← Category.assoc, overWDiag_overWSnd, Category.id_comp,
      ← NatTrans.comp_app, KernelPairSystem.diag_snd, NatTrans.id_app, Category.comp_id]

/-- The diagonal of `W ×_X W` maps to the diagonal of `W_j ×_{U_j} W_j`, in schemes. -/
lemma overWDiag_kernelPairCone_π (j : J) :
    (BigFppfOver.toScheme B S hS).map L.overWDiag ≫ L.kernelPairCone.π.app j =
      ((BigFppfOver.toScheme B S hS).mapCone L.coneW).π.app j ≫ G.diagScheme.app j := by
  rw [kernelPairCone_π_app, ← CategoryTheory.Functor.map_comp, overWDiag_kernelPairLeg]
  rfl

/-- The diagonal `W ⟶ W ×_X W` is an open immersion. -/
instance isOpenImmersion_overWDiag :
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map L.overWDiag) :=
  isOpenImmersion_dL G.diagScheme hβ L.isLimitW L.isLimit_kernelPairCone _
    L.overWDiag_kernelPairCone_π

/-- The diagonal `W ⟶ W ×_X W` is an open immersion, with source and target given explicitly. -/
instance isOpenImmersion_overWDiag' :
    _root_.AlgebraicGeometry.IsOpenImmersion (X := (BigFppfOver.toScheme B S hS).obj L.coneW.pt)
      (Y := (L.overW : Scheme.{u})) ((BigFppfOver.toScheme B S hS).map L.overWDiag) :=
  L.isOpenImmersion_overWDiag

/-- `K` is the union of the open images of the diagonal and of `W ×_X W`. -/
lemma cover_eq_top : ((BigFppfOver.toScheme B S hS).map L.kernelDiag).opensRange ⊔
    L.overW.ι.opensRange = ⊤ := by
  refine top_unique fun k _ ↦ ?_
  rw [Scheme.Opens.opensRange_ι]
  rcases L.cover k with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The second projection of `K`, restricted to `W ×_X W`, factors through `W ⟶ V`. -/
lemma overW_ι_kernelSnd :
    L.overW.ι ≫ (BigFppfOver.toScheme B S hS).map L.kernelSnd = (BigFppfOver.toScheme B S hS).map
        L.overWSnd ≫ (BigFppfOver.toScheme B S hS).map L.inclL :=
  L.overWSndS_inclL.symm

/-- The first projection of `K`, restricted to `W ×_X W`, factors through `W ⟶ V`. -/
lemma overW_ι_kernelFst :
    L.overW.ι ≫ (BigFppfOver.toScheme B S hS).map L.kernelFst = (BigFppfOver.toScheme B S hS).map
        L.overWFst ≫ (BigFppfOver.toScheme B S hS).map L.inclL := by
  rw [← CategoryTheory.Functor.map_comp, overWFst_inclL]
  rfl

/-- `W ⟶ V ⟶ K` factors as the diagonal `W ⟶ W ×_X W` followed by the inclusion into `K`. -/
lemma inclL_kernelDiag : (BigFppfOver.toScheme B S hS).map L.inclL ≫
    (BigFppfOver.toScheme B S hS).map L.kernelDiag =
    (BigFppfOver.toScheme B S hS).map L.overWDiag ≫ L.overW.ι :=
  L.overWDiagS_ι.symm

/-- The cone from `K` to the glued relations, in schemes: the diagonal piece of `K` goes to
the first piece of `R_j` and `W ×_X W` to the second. -/
noncomputable abbrev relConeScheme : Cone G.relScheme :=
  gluedRelationCone (cV := (BigFppfOver.toScheme B S hS).mapCone L.coneV)
      (cW := (BigFppfOver.toScheme B S hS).mapCone L.coneW)
    (cP := L.kernelPairCone) G.inclScheme G.diagScheme ((BigFppfOver.toScheme B S hS).map L.inclL)
        L.inclL_π_toScheme
    ((BigFppfOver.toScheme B S hS).map L.overWDiag) L.overWDiag_kernelPairCone_π
        ((BigFppfOver.toScheme B S hS).map L.overWSnd)
    ((BigFppfOver.toScheme B S hS).map L.kernelDiag) L.overW.ι
        ((BigFppfOver.toScheme B S hS).map L.kernelSnd) L.toScheme_kernelDiag_kernelSnd
    L.overW_ι_kernelSnd L.inclL_kernelDiag L.cover_eq_top

/-- The leg `K ⟶ R_j`, in schemes. -/
noncomputable def relLeg (j : J) : (BigFppfOver.toScheme B S hS).obj L.kernel ⟶ G.relScheme.obj j :=
  L.relConeScheme.π.app j

/-- The projections of `K` are compatible with the projections of the glued relations. -/
lemma relLeg_proj (p : G.kernelPairScheme ⟶ G.nbhdScheme) (hp : G.diagScheme ≫ p = 𝟙 _)
    (pL : (L.overW : Scheme.{u}) ⟶ (BigFppfOver.toScheme B S hS).obj L.coneW.pt)
    (hpL : ∀ j, pL ≫ ((BigFppfOver.toScheme B S hS).mapCone L.coneW).π.app j =
        L.kernelPairCone.π.app j ≫ p.app j)
    (pK : (BigFppfOver.toScheme B S hS).obj L.kernel ⟶ (BigFppfOver.toScheme B S hS).obj
        L.coneV.pt) (hdpK : (BigFppfOver.toScheme B S hS).map L.kernelDiag ≫ pK = 𝟙 _)
    (hepK : L.overW.ι ≫ pK = pL ≫ (BigFppfOver.toScheme B S hS).map L.inclL) (j : J) :
    pK ≫ (BigFppfOver.toScheme B S hS).map (L.coneV.π.app j) =
      L.relLeg j ≫ (gluedRelationProjNatTrans G.inclScheme G.diagScheme p hp).app j :=
  gluedRelationLeg_proj (cV := (BigFppfOver.toScheme B S hS).mapCone L.coneV)
      (cW := (BigFppfOver.toScheme B S hS).mapCone L.coneW)
    (cP := L.kernelPairCone) G.inclScheme G.diagScheme ((BigFppfOver.toScheme B S hS).map L.inclL)
        L.inclL_π_toScheme
    ((BigFppfOver.toScheme B S hS).map L.overWDiag) L.overWDiag_kernelPairCone_π
        ((BigFppfOver.toScheme B S hS).map L.overWSnd)
    ((BigFppfOver.toScheme B S hS).map L.kernelDiag) L.overW.ι
        ((BigFppfOver.toScheme B S hS).map L.kernelSnd) L.toScheme_kernelDiag_kernelSnd
    L.overW_ι_kernelSnd L.inclL_kernelDiag L.cover_eq_top p hp pL hpL pK hdpK hepK j

/-- The leg `K ⟶ R_j` is compatible with the second projection of `K` and the source map of
`R_j`. -/
lemma relLeg_source (j : J) :
    (BigFppfOver.toScheme B S hS).map L.kernelSnd ≫ (BigFppfOver.toScheme B S hS).map
        (L.coneV.π.app j) = L.relLeg j ≫ G.sourceScheme.app j :=
  L.relLeg_proj G.sndScheme G.diagScheme_sndScheme ((BigFppfOver.toScheme B S hS).map L.overWSnd)
    (fun j ↦ by
      show _ = (BigFppfOver.toScheme B S hS).map (L.kernelPairLeg j) ≫
          (BigFppfOver.toScheme B S hS).map (G.snd.app j)
      rw [← CategoryTheory.Functor.map_comp, kernelPairLeg_snd]
      rfl) _ L.toScheme_kernelDiag_kernelSnd L.overW_ι_kernelSnd j

/-- The leg `K ⟶ R_j` is compatible with the first projection of `K` and the target map of
`R_j`. -/
lemma relLeg_target (j : J) :
    (BigFppfOver.toScheme B S hS).map L.kernelFst ≫ (BigFppfOver.toScheme B S hS).map
        (L.coneV.π.app j) = L.relLeg j ≫ G.targetScheme.app j :=
  L.relLeg_proj G.fstScheme G.diagScheme_fstScheme ((BigFppfOver.toScheme B S hS).map L.overWFst)
    (fun j ↦ by
      show _ = (BigFppfOver.toScheme B S hS).map (L.kernelPairLeg j) ≫
          (BigFppfOver.toScheme B S hS).map (G.fst.app j)
      rw [← CategoryTheory.Functor.map_comp, kernelPairLeg_fst]
      rfl) _ L.toScheme_kernelDiag_kernelFst L.overW_ι_kernelFst j

/-- The leg `K ⟶ R_j` is a morphism over `S`. -/
lemma relLeg_hom (j : J) : L.relLeg j ≫ G.sourceScheme.app j ≫
    B.inclusion.map (G.ambient.obj j).hom = B.inclusion.map L.kernel.hom := by
  rw [← reassoc_of% L.relLeg_source j]
  erw [← inclusion_map_hom_eq (L.coneV.π.app j), ← inclusion_map_hom_eq L.kernelSnd]

/-- **The cone from `K = V ×_X V` to the glued relations.** -/
noncomputable def relCone : Cone G.etaleRelationSystem.rel where
  pt := L.kernel
  π :=
    { app j := Over.homMk (ObjectProperty.homMk (L.relLeg j))
        (ObjectProperty.hom_ext _ (L.relLeg_hom j))
      naturality {j k} u := (BigFppfOver.toScheme B S hS).map_injective (by
        change 𝟙 _ ≫ L.relLeg k = L.relLeg j ≫ G.relScheme.map u
        rw [Category.id_comp]
        exact (L.relConeScheme.w u).symm) }

/-- The legs of `relCone` have underlying morphisms of schemes `relLeg`. -/
lemma toScheme_map_relCone_π_app (j : J) : (BigFppfOver.toScheme B S hS).map (L.relCone.π.app j) =
    L.relLeg j := rfl

/-- **`V ×_X V` is the limit of the glued relations `R_i`**, in schemes. -/
noncomputable def isLimit_relCone : IsLimit ((BigFppfOver.toScheme B S hS).mapCone L.relCone) :=
  isLimitGluedRelationCone G.inclScheme G.diagScheme hα hβ L.isLimitV L.isLimitW
    L.isLimit_kernelPairCone ((BigFppfOver.toScheme B S hS).map L.inclL) L.inclL_π_toScheme
        ((BigFppfOver.toScheme B S hS).map L.overWDiag)
    L.overWDiag_kernelPairCone_π ((BigFppfOver.toScheme B S hS).map L.overWSnd)
        ((BigFppfOver.toScheme B S hS).map L.kernelDiag) L.overW.ι
    ((BigFppfOver.toScheme B S hS).map L.kernelSnd) L.toScheme_kernelDiag_kernelSnd
        L.overW_ι_kernelSnd
    L.inclL_kernelDiag L.cover_eq_top

/-- **The second projection of `V ×_X V` is the limit of the source maps.** -/
lemma relCone_π_source (j : J) :
    L.kernelSnd ≫ L.coneV.π.app j = L.relCone.π.app j ≫ G.etaleRelationSystem.s.app j :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    simp only [Functor.map_comp]
    exact L.relLeg_source j)

/-- **The first projection of `V ×_X V` is the limit of the target maps.** -/
lemma relCone_π_target (j : J) :
    L.kernelFst ≫ L.coneV.π.app j = L.relCone.π.app j ≫ G.etaleRelationSystem.t.app j :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    simp only [Functor.map_comp]
    exact L.relLeg_target j)

end LimitData

section Assembly

variable (hZ : B.Contains (⊤_ Scheme.{u}))
  [HasSheafify (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) (Type u)]

/-- **The conclusion of Stacks 07SU from the glueing data.** Over `Spec ℤ`, if the `V_i` are
quasi-compact and locally of finite type with affine transition morphisms, the kernel pairs
`W_i ×_{U_i} W_i` are quasi-compact, and the étale `V ⟶ X` of the limit data is surjective, then
`X` has a Noetherian approximation: it is the limit of the quotients `V_i / R_i` of the glued
relations. -/
theorem LimitData.hasNoetherianApproximation {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {G : GluedNeighbourhoodRelationData B (⊤_ Scheme.{u}) hZ Iᵒᵖ}
    (L : G.LimitData)
    (hobj : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (G.ambient.map g)))
    (hcpt : ∀ j, CompactSpace (G.ambientScheme.obj j))
    (hlft : ∀ j, LocallyOfFiniteType (terminal.from (G.ambientScheme.obj j)))
    (hkp : ∀ j, CompactSpace (G.kernelPairScheme.obj j))
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) L.space)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) L.atlas) :
    HasNoetherianApproximation B (⊤_ Scheme.{u}) hZ hZ L.space :=
  G.etaleRelationSystem.hasNoetherianApproximation B hZ hobj hcpt hlft
    (fun j ↦ by have := hcpt j; have := hkp j; exact G.compactSpace_rel j) L.coneV L.isLimitV
        L.relCone
    L.isLimit_relCone L.kernelSnd L.kernelFst L.relCone_π_source L.relCone_π_target hX L.atlas
    L.isPullback_kernel hsurj L.etale_atlas

end Assembly

end GluedNeighbourhoodRelationData

end AlgebraicGeometry.Space
