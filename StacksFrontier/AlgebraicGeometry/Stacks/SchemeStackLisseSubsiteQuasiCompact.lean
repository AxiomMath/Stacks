module

public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackFlatSubsiteQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteLocalFactorizations
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ChosenEtaleQuasiCompactObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleBaseChange

/-!
# The terminal object of the lisse-étale site of an affine scheme is quasi-compact

The lisse-étale twins of
`StacksFrontier/AlgebraicGeometry/Stacks/SchemeStackFlatSubsiteQuasiCompact.lean`:
for a scheme `U`, the lisse-étale site of `(Sch/U)_{fppf}` has the terminal object `U/U`, which
is a quasi-compact object (Stacks 090H) when `U` is quasi-compact; every object is covered by
objects with affine underlying scheme; and over an affine `U` the ring map `O(U/U) → O(Z)` to an
affine smooth object is flat. These are the inputs of the free-resolution step of the proof of
Stacks 07B3 (1).

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isQuasiCompactObject_schemeStack_id`.
* `AlgebraicGeometry.Stack.LisseEtale.generate_isAffine_mem_inclusionTopology_schemeStack`.
* `AlgebraicGeometry.Stack.LisseEtale.flat_structureSheaf_map_schemeStack`.
* `AlgebraicGeometry.Stack.LisseEtale.exists_quasiIso_isFree_schemeStack`: a globally presented
  module on the lisse-étale site of an affine scheme has a resolution by free modules.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The lisse-étale site of the stack of a scheme `U` has a terminal object**, the identity
of `U`: it is terminal in `(Sch/U)` and it is a smooth object. -/
noncomputable def isTerminalSmoothObjectSchemeStackId :
    IsTerminal (⟨Over.mk (𝟙 U), smoothObject_schemeStack_id.{u, w} B S hS U⟩ :
      (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).FullSubcategory) :=
  (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).isTerminalFullSubcategory
    Over.mkIdTerminal _

namespace LisseEtale

/-- The structure morphism of a smooth object of the lisse-étale site of a scheme stack is
smooth. -/
private theorem smooth_map_hom_of_smoothObject
    (x : (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).FullSubcategory) :
    Smooth ((BigFppfOver.toScheme B S hS).map x.obj.hom) :=
  (smoothObject_schemeStack_iff.{u, w} B S hS U x.obj).1 x.property

/-- **The terminal object `U/U` of the lisse-étale site of the stack of a quasi-compact scheme
`U` is a quasi-compact object** (Stacks 090H). It is quasi-compact in the big étale site of the
stack, the big étale site localized at `U`, by
`AlgebraicGeometry.BigFppfSite.isQuasiCompactObject_etaleTopology_of_compactSpace`, and
quasi-compactness descends to the lisse-étale site along the inclusion, which is fully faithful,
continuous and cocontinuous (Stacks 0788 (1)). -/
theorem isQuasiCompactObject_schemeStack_id
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS U)).IsQuasiCompactObject
      ⟨Over.mk (𝟙 U), smoothObject_schemeStack_id.{u, w} B S hS U⟩ := by
  have := isContinuous_inclusion'.{u, w} B S hS (schemeStack.{u, w} B S hS U)
  have := isCocontinuous_inclusion'.{u, w} B S hS (schemeStack.{u, w} B S hS U)
  refine (smoothObject.{u, w} B S hS
    (schemeStack.{u, w} B S hS U)).ι.isQuasiCompactObject_of_isCocontinuous
    (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B))
    (CoverPreserving.of_isContinuous _ _ _) _ ?_
  show (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p
    (etaleTopology B)).IsQuasiCompactObject (Over.mk (𝟙 U))
  rw [associatedTopology_schemeStack]
  exact GrothendieckTopology.isQuasiCompactObject_over _ (Over.mk (𝟙 U))
    (GrothendieckTopology.isQuasiCompactObject_over _ U
      (B.isQuasiCompactObject_etaleTopology_of_compactSpace U.left hU))

/-- **Every object of the lisse-étale site of the stack of a scheme is covered by objects with
affine underlying scheme.** The affine opens of the underlying scheme of a smooth object `x` are
smooth objects (an open immersion is smooth), they cover `x` in the big étale site of the stack
(an open covering is an étale covering), and the inclusion of the lisse-étale site is
cocontinuous, so they cover `x` in the lisse-étale site. -/
theorem generate_isAffine_mem_inclusionTopology_schemeStack
    (x : (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).FullSubcategory) :
    Sieve.generate (fun (Z : (smoothObject.{u, w} B S hS
        (schemeStack.{u, w} B S hS U)).FullSubcategory) (_ : Z ⟶ x) =>
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z.obj.left)) ∈
        inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS U) x := by
  have := isCocontinuous_inclusion'.{u, w} B S hS (schemeStack.{u, w} B S hS U)
  choose Vi ui hu hrange hVaff using
    fun V => BigFppfOver.exists_affineOpen_restrict B S hS x.obj.left V
  let x' : Over U := x.obj
  let W : ∀ V, Over U := fun V => Over.mk (ui V ≫ x'.hom)
  let w : ∀ V, W V ⟶ x' := fun V => Over.homMk (ui V)
  have hW : ∀ V, smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U) (W V) := fun V => by
    have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ui V)) :=
      hu V
    have hx := smooth_map_hom_of_smoothObject.{u, w} B S hS U x
    rw [smoothObject_schemeStack_iff]
    show Smooth ((BigFppfOver.toScheme B S hS).map (ui V ≫ x'.hom))
    rw [Functor.map_comp]
    infer_instance
  have hR' : Sieve.ofArrows W w ∈ (((etaleTopology B).over (B.obj hS)).over U) x' := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    show Sieve.ofArrows Vi ui ∈ (etaleTopology B).over (B.obj hS) x'.left
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    rw [etaleTopology_eq_comap]
    apply Precoverage.generate_mem_toGrothendieck
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun y => ?_, fun V => ?_⟩
    swap
    · have : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (ui V).left) := hu V
      infer_instance
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj x'.left).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨V, ?_⟩
    show y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ui V))
    rw [hrange V]
    exact hV
  have hR : (Sieve.ofArrows W w : Sieve x.obj) ∈ associatedTopology B S hS
      (schemeStack.{u, w} B S hS U).val.val.p (etaleTopology B) x.obj := by
    rw [associatedTopology_schemeStack]
    exact hR'
  refine (inclusionTopology.{u, w} B S hS _).superset_covering ?_
    ((smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).ι.cover_lift
      (inclusionTopology.{u, w} B S hS _) (associatedTopology B S hS _ (etaleTopology B)) hR)
  rintro Y f ⟨_, g, _, ⟨V⟩, hgf⟩
  exact ⟨⟨W V, hW V⟩, ObjectProperty.homMk g, ObjectProperty.homMk (w V), hVaff V,
    (smoothObject.{u, w} B S hS _).ι.map_injective hgf⟩

/-- **Over an affine scheme `U`, the ring map `O(U/U) ⟶ O(Z)` to an affine smooth object is
flat.** The structure sheaf of the lisse-étale site is `Z ↦ Γ(Z)` (Stacks 0788 (1)), the unique
map `Z ⟶ U/U` lies over the structure morphism of `Z`, which is smooth (Stacks 0787), hence
flat, and a flat morphism of affine schemes induces a flat map on global functions. -/
theorem flat_structureSheaf_map_schemeStack
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (Z : (smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U)).FullSubcategory)
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z.obj.left)) :
    ((ringedTopos'.{u, w} B S hS (schemeStack.{u, w} B S hS U)).O.obj.map
      ((isTerminalSmoothObjectSchemeStackId.{u, w} B S hS U).from Z).op).hom.Flat := by
  have hsmooth := smooth_map_hom_of_smoothObject.{u, w} B S hS U Z
  have hleft : ((isTerminalSmoothObjectSchemeStackId.{u, w} B S hS U).from Z).hom.left =
      Z.obj.hom := by
    simpa using Over.w ((isTerminalSmoothObjectSchemeStackId.{u, w} B S hS U).from Z).hom
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    ((isTerminalSmoothObjectSchemeStackId.{u, w} B S hS U).from Z).hom.left).op).hom.Flat
  rw [hleft, Scheme.Γ_map_op]
  have := hU
  have := hZ
  exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)
    (f := (BigFppfOver.toScheme B S hS).map Z.obj.hom)).1 inferInstance

section FreeResolution

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- On the lisse-étale site of an algebraic stack, the sheafification equivalences for
`AddCommGrpCat.{u}`-valued presheaves are the local bijections, the site being essentially
small. -/
theorem wEqualsLocallyBijective_inclusionTopology (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    (inclusionTopology.{u, w} B S hS 𝒳).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _

/-- Abelian sheaves on the lisse-étale site of an algebraic stack have a sheafification, the
site being essentially small. -/
theorem hasSheafify_inclusionTopology (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasSheafify (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u, u, u + 1, u + 1, u} _ _

/-- `wEqualsLocallyBijective_inclusionTopology` for the stack of a scheme, as a local
instance. -/
local instance :
    (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS U)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_inclusionTopology B S hS _

/-- `hasSheafify_inclusionTopology` for the stack of a scheme, as a local instance. -/
local instance : HasSheafify (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS U))
    AddCommGrpCat.{u} :=
  hasSheafify_inclusionTopology B S hS _

/-- **A globally presented module on the lisse-étale site of an affine scheme has a free
resolution** (the free-resolution step of the proof of Stacks 07B3, part (1)): if `U` is affine
and `H` is a sheaf of modules on the lisse-étale site of `(Sch/U)_{fppf}` with a global
presentation (Stacks 03DE), there are a bounded above complex `F` whose terms are direct sums of
copies of the structure sheaf and a quasi-isomorphism `F ⟶ H[0]`. -/
theorem exists_quasiIso_isFree_schemeStack
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (H : SheafOfModules.{u} (Stacks.TensorByBaseModule.ringSheaf
      (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS U))
      (ringedTopos'.{u, w} B S hS (schemeStack.{u, w} B S hS U)).O))
    (hH : H.IsPresentedByGlobalSections) :
    ∃ (F : CochainComplex (SheafOfModules.{u} (Stacks.TensorByBaseModule.ringSheaf
        (inclusionTopology.{u, w} B S hS (schemeStack.{u, w} B S hS U))
        (ringedTopos'.{u, w} B S hS (schemeStack.{u, w} B S hS U)).O)) ℤ)
      (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H),
      F.IsStrictlyLE 0 ∧ QuasiIso π ∧ ∀ n, (F.X n).IsFree :=
  Stacks.TerminalFreeResolution.exists_quasiIso_isFree_of_isPresentedByGlobalSections
    (ringedTopos'.{u, w} B S hS (schemeStack.{u, w} B S hS U)).O
    (isTerminalSmoothObjectSchemeStackId.{u, w} B S hS U)
    (fun Z => IsAffine ((BigFppfOver.toScheme B S hS).obj Z.obj.left))
    (generate_isAffine_mem_inclusionTopology_schemeStack.{u, w} B S hS U)
    (fun Z hZ => flat_structureSheaf_map_schemeStack.{u, w} B S hS U hU Z hZ)
    (isQuasiCompactObject_schemeStack_id.{u, w} B S hS U (by
      have := hU; infer_instance))
    H hH

end FreeResolution

end LisseEtale

end AlgebraicGeometry.Stack
