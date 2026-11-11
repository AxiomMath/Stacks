module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeOfRankModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallySplitMono
public import StacksFrontier.CategoryTheory.Subobject.FiltrationMap

/-!
# Inverse images of monomorphisms with invertible cokernel

Let `a : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `ι : 𝒜 ⟶ ℰ` be a
monomorphism of `𝒪_Y`-modules whose cokernel `ℒ` is invertible. Then the inverse image
`a^*ι : a^*𝒜 ⟶ a^*ℰ` is again a monomorphism, for an *arbitrary* morphism `a`, flat or not.

The reason is that the short exact sequence `0 ⟶ 𝒜 ⟶ ℰ ⟶ ℒ ⟶ 0` splits étale locally on `Y`:
`ℒ` has rank one (Stacks 0B8Q), so near every point it is free on one generator, which lifts
locally along the epimorphism `ℰ ⟶ ℒ`. A split monomorphism stays a split monomorphism under any
functor, so `a^*ι` is a split monomorphism on the étale charts of `X` lying over these charts of
`Y`; these charts cover `X`, and injectivity descends along the flat covering they form.

Consequently the inverse image along any morphism of algebraic spaces of a filtration
`0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ` with invertible successive quotients `ℒ_i` is again such a
filtration of `a^*ℰ`, with successive quotients `a^*ℒ_i`. This is the step of the proof of
Stacks 0ESA in which an identity of operations on `CH_*(X)` is tested on every good `Y ⟶ X`:
there the inverse image of the filtration along the test morphism has to be a filtration again,
and the test morphism need not be flat.

## Main results

* `AlgebraicGeometry.Space.isSplitMono_modulePullback_chartToSpace_map`: a morphism of modules
  which is split on the slice of the small étale site at a chart is split after the inverse image
  to the chart space.
* `AlgebraicGeometry.Space.exists_chart_isSplitMono_overFunctor_map`: a monomorphism with
  invertible cokernel is split on an étale chart through any given point.
* `AlgebraicGeometry.Space.mono_modulePullback_map_of_isInvertibleModule_cokernel`: **the inverse
  image of a monomorphism with invertible cokernel is a monomorphism**, along any morphism.
* `AlgebraicGeometry.Space.exists_filtration_modulePullback`: the inverse image of a filtration
  with invertible successive quotients is a filtration with the inverse images as successive
  quotients.

## References

* [Stacks Project, Tag 0ESA](https://stacks.math.columbia.edu/tag/0ESA)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The abelian structure of the `𝒪_Z`-modules, at the universe of the schemes. -/
local instance abelianModulesMonoInvertibleCokernel (Z : AlgebraicSpaces B S hS) :
    Abelian (Modules.{u, u} B S hS Z.1 Z.2) :=
  SheafOfModules.instAbelian _

/-- The `𝒪_Z`-modules have an initial object, from their abelian structure. -/
local instance (priority := 10000) hasInitialModulesMonoInvertibleCokernel
    (Z : AlgebraicSpaces B S hS) : HasInitial (Modules.{u, u} B S hS Z.1 Z.2) :=
  HasZeroObject.hasInitial

/-- The initial morphisms of `𝒪_Z`-modules are monomorphisms. -/
local instance (priority := 10000) initialMonoClassModulesMonoInvertibleCokernel
    (Z : AlgebraicSpaces B S hS) : InitialMonoClass (Modules.{u, u} B S hS Z.1 Z.2) :=
  HasZeroObject.initialMonoClass

/-- A split monomorphism after one functor is a split monomorphism after any isomorphic
functor. -/
private theorem isSplitMono_map_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {M N : C} (f : M ⟶ N) (h : IsSplitMono (F.map f)) : IsSplitMono (G.map f) :=
  IsSplitMono.mk'
    { retraction := e.inv.app N ≫ retraction (F.map f) ≫ e.hom.app M
      id := by rw [e.inv.naturality_assoc, IsSplitMono.id_assoc, Iso.inv_hom_id_app] }

/-- `isSplitMono_map_of_iso` for an isomorphism out of a composite functor, with the hypothesis
read on the two factors. -/
private theorem isSplitMono_map_of_comp_iso {C C' D : Type*} [Category C] [Category C']
    [Category D] {F : C ⥤ C'} {G : C' ⥤ D} {H : C ⥤ D} (e : F ⋙ G ≅ H) {M N : C} (f : M ⟶ N)
    (h : IsSplitMono (G.map (F.map f))) : IsSplitMono (H.map f) :=
  isSplitMono_map_of_iso e f h

/-- `isSplitMono_map_of_iso` for an isomorphism between composite functors, with the hypothesis
and the conclusion read on the factors. -/
private theorem isSplitMono_map_map_of_iso {C C' C'' D : Type*} [Category C] [Category C']
    [Category C''] [Category D] {F : C ⥤ C'} {G : C' ⥤ D} {F' : C ⥤ C''} {G' : C'' ⥤ D}
    (e : F ⋙ G ≅ F' ⋙ G') {M N : C} (f : M ⟶ N) (h : IsSplitMono (G.map (F.map f))) :
    IsSplitMono (G'.map (F'.map f)) :=
  isSplitMono_map_of_iso e f h

/-- Points of étale charts are carried along a morphism of charts compatibly with the structure
morphisms of the charts. -/
private theorem pointsMap_hom_pointsMap_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V W : SmallEtale B S hS F} (f : W ⟶ V)
    (q : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W))) :
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V)) V.1.hom
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W))
          (yoneda.map ((SmallEtale.toOver B S hS F).map f)) q) =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W)) W.1.hom q := by
  have h := congrFun (pointsMap_comp B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj W))
    (yoneda.map ((SmallEtale.toOver B S hS F).map f)) V.obj.hom) q
  rw [show yoneda.map ((SmallEtale.toOver B S hS F).map f) ≫ V.obj.hom = W.obj.hom from
    CostructuredArrow.w f.hom] at h
  exact h.symm

/-- **Restriction to the slice at a chart, followed by the comparison of Stacks 04M0, is the
inverse image to the chart space**, as functors. On objects this is
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionFunctorObjIso` followed by Stacks Equation
03LW for the étale structure morphism of the chart. -/
def overFunctorCompChartSmallEtaleRestrictionFunctorIso (Z : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Z.1) :
    SheafOfModules.overFunctor (structureRingSheaf B S hS Z) V ⋙
        chartSmallEtaleRestrictionFunctor Z V ≅
      modulePullback B S hS (chartToSpace B S hS Z V) :=
  NatIso.ofComponents (fun M ↦ chartSmallEtaleRestrictionFunctorObjIso Z M V)
      (fun _ ↦ by ext U x; rfl) ≪≫
    (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Z V)
      (isEtale_chartToSpace B S hS Z V)).symm

/-- **A morphism split on the slice at a chart is split on the chart space.** If the
restriction of a morphism of `𝒪_Z`-modules to the slice of the small étale site at an étale
chart `V` is a split monomorphism, then so is its inverse image to the chart space of `V`. -/
theorem isSplitMono_modulePullback_chartToSpace_map (Z : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (v : M ⟶ N) (V : SmallEtale B S hS Z.1)
    (h : IsSplitMono ((SheafOfModules.overFunctor (structureRingSheaf B S hS Z) V).map v)) :
    IsSplitMono ((modulePullback B S hS (chartToSpace B S hS Z V)).map v) :=
  isSplitMono_map_of_comp_iso (overFunctorCompChartSmallEtaleRestrictionFunctorIso B S hS Z V) v
    (IsSplitMono.mk' (h.exists_splitMono.some.map (chartSmallEtaleRestrictionFunctor Z V)))

/-- **A monomorphism with invertible cokernel splits étale locally.** For a monomorphism
`ι : 𝒜 ⟶ ℰ` of `𝒪_Y`-modules with invertible cokernel, every point of `Y` lies in the image of an
étale chart `V` on whose slice the restriction of `ι` is a split monomorphism.

The cokernel has rank one (Stacks 0B8Q), so it is free on one generator over a chart through the
point; the generator lifts along `ℰ ⟶ cokernel ι` on a covering sieve of that chart, and over a
member of the sieve through the point the lift splits the sequence. -/
theorem exists_chart_isSplitMono_overFunctor_map (Y : AlgebraicSpaces B S hS)
    {A E : Modules.{u, u} B S hS Y.1 Y.2} (ι : A ⟶ E) [Mono ι]
    (hL : IsInvertibleModule Y (cokernel ι)) (y : points B S hS Y.1) :
    ∃ V : SmallEtale B S hS Y.1,
      IsSplitMono ((SheafOfModules.overFunctor (structureRingSheaf B S hS Y) V).map ι) ∧
      y ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V)) V.1.hom) := by
  obtain ⟨V₀, ⟨κ, ⟨hκ⟩⟩, p, hp⟩ :=
    exists_chart_isColimitCofan_mem_range_of_isFiniteLocallyFreeOfRank B S hS Y (cokernel ι)
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Y hL) y
  have : @Mono (SheafOfModules.{u} (structureRingSheaf B S hS Y)) _ A E ι := ‹_›
  obtain ⟨T, hT, hsplit⟩ := Stacks.SheafOfModules.exists_sieve_isSplitMono_overFunctor_map
    (R := structureRingSheaf B S hS Y) ι V₀ κ hκ
  obtain ⟨W, g, hg, q, hq⟩ := SmallEtale.exists_mem_arrows_pointsMap_eq B S hS Y.1 hT p
  exact ⟨W, hsplit g hg, q,
    (pointsMap_hom_pointsMap_map B S hS g q).symm.trans (by rw [hq]; exact hp)⟩

/-- **The inverse image of a monomorphism with invertible cokernel is a monomorphism.** Let
`a : X ⟶ Y` be an arbitrary morphism of algebraic spaces over `S` and `ι : 𝒜 ⟶ ℰ` a monomorphism
of `𝒪_Y`-modules whose cokernel is invertible. Then `a^*ι : a^*𝒜 ⟶ a^*ℰ` is a monomorphism.

No flatness of `a` is needed: `ι` splits étale locally on `Y`
(`AlgebraicGeometry.Space.exists_chart_isSplitMono_overFunctor_map`), so `a^*ι` is split on every
étale chart of `X` with an affine chart diagram over such a chart of `Y`. These charts of `X` are
jointly surjective, and injectivity descends along the flat family of their structure
morphisms. -/
theorem mono_modulePullback_map_of_isInvertibleModule_cokernel {X Y : AlgebraicSpaces B S hS}
    (a : X ⟶ Y) {A E : Modules.{u, u} B S hS Y.1 Y.2} (ι : A ⟶ E) [Mono ι]
    (hL : IsInvertibleModule Y (cokernel ι)) : Mono ((modulePullback B S hS a).map ι) := by
  let P : SmallEtale B S hS Y.1 → Prop := fun V ↦
    IsSplitMono ((SheafOfModules.overFunctor (structureRingSheaf B S hS Y) V).map ι)
  have hPhom : ∀ {V V' : SmallEtale B S hS Y.1}, (V' ⟶ V) → P V → P V' := fun φ hV ↦
    isSplitMono_map_of_comp_iso (SheafOfModules.overFunctorMap (structureRingSheaf B S hS Y) φ) ι
      (IsSplitMono.mk' ((show IsSplitMono _ from hV).exists_splitMono.some.map
        (SheafOfModules.overMap (structureRingSheaf B S hS Y) φ)))
  have hPcov := exists_chart_isSplitMono_overFunctor_map B S hS Y ι hL
  let I := {W : SmallEtale B S hS X.1 // HasAffineChartDiagramWith B S hS a P W}
  refine mono_of_forall_mono_modulePullback_map_of_isFlat B S hS
    (Z' := fun i : I ↦ chartSpace B S hS X i.1) (fun i ↦ chartToSpace B S hS X i.1)
    (fun i ↦ isFlat_of_isEtale B S hS (isEtale_chartToSpace B S hS X i.1)) ?_ _ fun i ↦ ?_
  · refine (isJointlySurjective_iff B S hS _ _).2 fun x ↦ ?_
    obtain ⟨U, p, hp⟩ := exists_chart_point B S hS X.1 X.2 x
    have hcov := mem_topology_of_hasAffineChartDiagramWith B S hS P a hPhom hPcov U
      (Sieve.generate fun W _ ↦ HasAffineChartDiagramWith B S hS a P W)
      fun W f hW ↦ ⟨W, 𝟙 W, f, hW, Category.id_comp f⟩
    obtain ⟨W, g, ⟨W', g', f', hW', rfl⟩, q, hq⟩ :=
      SmallEtale.exists_mem_arrows_pointsMap_eq B S hS X.1 hcov p
    refine ⟨⟨W', hW'⟩, pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map g')) q, ?_⟩
    refine (pointsMap_hom_pointsMap_map B S hS g' q).trans
      ((pointsMap_hom_pointsMap_map B S hS (g' ≫ f') q).symm.trans ?_)
    rw [hq]
    exact hp
  · obtain ⟨-, V, q, hq, -, hPV⟩ := i.2
    have hsq := chartSpaceMapOver_comp_chartToSpace B S hS a q hq
    have hV := isSplitMono_modulePullback_chartToSpace_map B S hS Y ι V hPV
    have := isSplitMono_map_map_of_iso (modulePullbackCommSquareIso B S hS hsq) ι
      (IsSplitMono.mk' (hV.exists_splitMono.some.map
        (modulePullback B S hS (chartSpaceMapOver B S hS q))))
    exact this.exists_splitMono.some.mono

/-- **The inverse image of a filtration with invertible quotients.** Let `a : X ⟶ Y` be an
arbitrary morphism of algebraic spaces and let `ℰ` be an `𝒪_Y`-module with a filtration
`0 = ℰ_0 ⊂ ℰ_1 ⊂ ⋯ ⊂ ℰ_r = ℰ` with invertible successive quotients `ℰ_i / ℰ_{i-1} ≅ ℒ_i`. Then
`a^*ℰ` has a filtration `0 = ℰ'_0 ⊂ ℰ'_1 ⊂ ⋯ ⊂ ℰ'_r = a^*ℰ` with `ℰ'_i / ℰ'_{i-1} ≅ a^*ℒ_i`.

The inclusions `ℰ_{i-1} ⊂ ℰ_i` stay monomorphisms after `a^*` by
`AlgebraicGeometry.Space.mono_modulePullback_map_of_isInvertibleModule_cokernel`, and `a^*` is a
left adjoint, so it preserves cokernels. This is the form of the filtration consumed by
`AlgebraicGeometry.Space.PrivateChern.totalChernCap_eq_prod_one_add_chernCap_one`
(Stacks 0ESA) on the source of a test morphism. -/
theorem exists_filtration_modulePullback {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y) {r : ℕ}
    {E : Modules.{u, u} B S hS Y.1 Y.2} (L : Fin r → Modules.{u, u} B S hS Y.1 Y.2)
    (hL : ∀ i, IsInvertibleModule Y (L i)) (F : Fin (r + 1) → Subobject E) (hF : Monotone F)
    (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ⊤)
    (e : ∀ i : Fin r, cokernel (ofLE (F i.castSucc) (F i.succ) (hF i.castSucc_le_succ)) ≅ L i) :
    ∃ (F' : Fin (r + 1) → Subobject ((modulePullback B S hS a).obj E)) (hF' : Monotone F'),
      F' 0 = ⊥ ∧ F' (Fin.last r) = ⊤ ∧ ∀ i : Fin r,
        Nonempty (cokernel (ofLE (F' i.castSucc) (F' i.succ) (hF' i.castSucc_le_succ)) ≅
          (modulePullback B S hS a).obj (L i)) := by
  have := (modulePullbackAdjunction B S hS a).isLeftAdjoint
  have : PreservesColimitsOfShape WalkingParallelPair (modulePullback B S hS a) :=
    (modulePullbackAdjunction B S hS a).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (modulePullback B S hS a)
  obtain ⟨F', hF', h0', hr', e'⟩ := exists_filtration_map (modulePullback B S hS a) F hF h0 hr
    fun i ↦ by
      have : IsInvertibleModule Y (L i) := hL i
      exact mono_modulePullback_map_of_isInvertibleModule_cokernel B S hS a _
        (Stacks.SheafOfModules.isInvertible_of_iso _ _ (e i).symm)
  exact ⟨F', hF', h0', hr', fun i ↦ ⟨(e' i).some ≪≫ (modulePullback B S hS a).mapIso (e i)⟩⟩

end AlgebraicGeometry.Space

end
