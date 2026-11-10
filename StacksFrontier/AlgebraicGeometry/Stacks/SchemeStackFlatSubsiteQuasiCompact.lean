module

public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactObjects
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.Over
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.EqualizerCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRingedModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TerminalObjectFreeResolution

/-!
# The terminal object of the flat-fppf site of an affine scheme is quasi-compact

Let `U` be a quasi-compact scheme over `S`. The flat-fppf site of the algebraic stack
`(Sch/U)_{fppf}` has the terminal object `U/U`
(`AlgebraicGeometry.Stack.isTerminalFlatObjectSchemeStackId`). This file shows that it is a
quasi-compact object of that site (Stacks 090H). In the proof of Stacks 07B3 this is what makes
the global sections of a direct sum of copies of the structure sheaf the direct sum of copies of
its global sections (Stacks 0738), so that a global presentation of a sheaf of modules on the
flat-fppf site of an affine scheme comes from a presentation of a module over its ring of
functions.

## Main results

* `CategoryTheory.Functor.isQuasiCompactObject_of_isCocontinuous`: quasi-compactness of an object
  descends along a fully faithful continuous and cocontinuous functor of sites.
* `AlgebraicGeometry.Stack.FlatFppf.isQuasiCompactObject_schemeStack_id`: the terminal object of
  the flat-fppf site of the stack of a quasi-compact scheme is quasi-compact.

## References

* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D] (G : C ⥤ D)
  [G.Full] [G.Faithful] (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **Quasi-compactness descends along a fully faithful continuous and cocontinuous functor.**
If `G x` is a quasi-compact object of `(D, K)` (Stacks 090H), then so is `x` in `(C, J)`: the image
of a covering family of `x` covers `G x`, is refined by a covering family through finitely many
of its members, and the corresponding finite subfamily covers `x` because its image does and `G`
is cocontinuous. -/
theorem isQuasiCompactObject_of_isCocontinuous (hG : CoverPreserving J K G)
    [G.IsCocontinuous J K] (x : C) (hx : K.IsQuasiCompactObject (G.obj x)) :
    J.IsQuasiCompactObject x := by
  intro 𝒰 h𝒰
  have h₁ : (𝒰.map G).sieve₀ ∈ K (G.obj x) := by
    refine K.superset_covering ?_ (hG.cover_preserve h𝒰)
    rintro V g ⟨W, h, f, hf, rfl⟩
    obtain ⟨Y, k, _, ⟨i⟩, rfl⟩ := hf
    exact ⟨_, f ≫ G.map k, _, Presieve.ofArrows.mk i, by simp⟩
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := hx _ h₁
  let T : Set 𝒰.I₀ := Set.range φ.s₀
  let 𝒲 : PreZeroHypercover.{max u v} x :=
    { I₀ := T, X := fun i => 𝒰.X i.1, f := fun i => 𝒰.f i.1 }
  refine ⟨𝒲, { s₀ := Subtype.val, h₀ := fun _ => 𝟙 _, w₀ := fun _ => by simp [𝒲] }, ?_, ?_⟩
  · have h₂ : (𝒲.map G).sieve₀ ∈ K (G.obj x) := by
      refine K.superset_covering ?_ h𝒱
      rintro V g ⟨_, h, _, ⟨j⟩, rfl⟩
      refine ⟨_, h ≫ φ.h₀ j, _, Presieve.ofArrows.mk (⟨φ.s₀ j, j, rfl⟩ : T), ?_⟩
      exact (Category.assoc _ _ _).trans (congrArg (h ≫ ·) (φ.w₀ j))
    refine J.superset_covering ?_ (G.cover_lift J K h₂)
    rintro Y f ⟨W, h, g, ⟨i⟩, hcomp⟩
    obtain ⟨h', rfl⟩ := G.map_surjective h
    exact ⟨_, h', _, Presieve.ofArrows.mk i, G.map_injective (by rwa [G.map_comp])⟩
  · change (Set.range (Subtype.val : T → 𝒰.I₀)).Finite
    rwa [Subtype.range_coe]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack.FlatFppf

universe w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The fppf site of the stack of a scheme `U` is the big fppf site of `S` localized at `U`. -/
theorem associatedTopology_schemeStack :
    associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p B.topology =
      (BigFppfOver.topology B S hS).over U :=
  Over.forget_inheritedTopology (B.topology.over (B.obj hS)) U

/-- **The terminal object `U/U` of the flat-fppf site of the stack of a quasi-compact scheme `U`
is a quasi-compact object** (Stacks 090H). It is quasi-compact in the fppf site of the stack, the
big fppf site localized at `U`, and quasi-compactness descends to the flat-fppf site along the
inclusion, which is fully faithful, continuous and cocontinuous (Stacks 0788 (2)). -/
theorem isQuasiCompactObject_schemeStack_id
    (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    (topology B S hS (schemeStack.{u, w} B S hS U)).IsQuasiCompactObject
      ⟨Over.mk (𝟙 U), flatObject_schemeStack_id.{u, w} B S hS U⟩ := by
  have := isContinuous_inclusion_topology B S hS (schemeStack.{u, w} B S hS U)
  have := isCocontinuous_inclusion_topology B S hS (schemeStack.{u, w} B S hS U)
  refine
    (objectProperty B S hS (schemeStack.{u, w} B S hS U)).ι.isQuasiCompactObject_of_isCocontinuous
    (topology B S hS (schemeStack.{u, w} B S hS U))
    (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p B.topology)
    (CoverPreserving.of_isContinuous _ _ _) _ ?_
  change (associatedTopology B S hS (schemeStack.{u, w} B S hS U).val.val.p
    B.topology).IsQuasiCompactObject (Over.mk (𝟙 U))
  rw [associatedTopology_schemeStack]
  exact GrothendieckTopology.isQuasiCompactObject_over _ (Over.mk (𝟙 U))
    (BigFppfOver.isQuasiCompactObject_of_compactSpace B S hS U hU)

/-- **Every object of the flat-fppf site of the stack of a scheme is covered by objects with affine
underlying scheme.** The affine opens of the underlying scheme of a flat object `x` are flat
objects (an open immersion is flat), they cover `x` in the fppf site of the stack, and the
inclusion of the flat-fppf site is cocontinuous, so they cover `x` in the flat-fppf site. -/
theorem generate_isAffine_mem_topology_schemeStack
    (x : FlatFppf B S hS (schemeStack.{u, w} B S hS U)) :
    Sieve.generate (fun (Z : FlatFppf B S hS (schemeStack.{u, w} B S hS U)) (_ : Z ⟶ x) =>
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z.obj.left)) ∈
        topology B S hS (schemeStack.{u, w} B S hS U) x := by
  have := isCocontinuous_inclusion_topology B S hS (schemeStack.{u, w} B S hS U)
  choose Vi ui hu hrange hVaff using
    fun V => BigFppfOver.exists_affineOpen_restrict B S hS x.obj.left V
  let x' : Over U := x.obj
  let W : ∀ V, Over U := fun V => Over.mk (ui V ≫ x'.hom)
  let w : ∀ V, W V ⟶ x' := fun V => Over.homMk (ui V)
  have hW : ∀ V, flatObject B S hS (schemeStack.{u, w} B S hS U).val (W V) := fun V => by
    have : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ui V)) :=
      hu V
    exact flatObject_of_flat B S hS _ (w V) (show Flat ((BigFppfOver.toScheme B S hS).map (ui V))
      from inferInstance) x.property
  have hR' : Sieve.ofArrows W w ∈ ((BigFppfOver.topology B S hS).over U) x' := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows Vi ui ∈ B.topology.over (B.obj hS) x'.left
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply Precoverage.generate_mem_toGrothendieck
    rw [bigFppfPrecoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun y => ?_, fun V => ?_⟩
    swap
    · have : _root_.AlgebraicGeometry.IsOpenImmersion (B.inclusion.map (ui V).left) := hu V
      exact ⟨inferInstance, inferInstance⟩
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj x'.left).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨V, ?_⟩
    change y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ui V))
    rwa [hrange V]
  have hR : (Sieve.ofArrows W w : Sieve x.obj) ∈ associatedTopology B S hS
      (schemeStack.{u, w} B S hS U).val.val.p B.topology x.obj := by
    rwa [associatedTopology_schemeStack]
  refine (topology B S hS _).superset_covering ?_
    ((objectProperty B S hS (schemeStack.{u, w} B S hS U)).ι.cover_lift
      (topology B S hS _) (associatedTopology B S hS _ B.topology) hR)
  rintro Y f ⟨_, g, _, ⟨V⟩, hgf⟩
  exact ⟨⟨W V, hW V⟩, ObjectProperty.homMk g, ObjectProperty.homMk (w V), hVaff V,
    (objectProperty B S hS _).ι.map_injective hgf⟩

/-- **Over an affine scheme `U`, the ring map `O(U/U) ⟶ O(Z)` to an affine flat object is flat.**
The structure sheaf of the flat-fppf site is `Z ↦ Γ(Z)` (Stacks 06TV, 0788 (2)), the unique map
`Z ⟶ U/U` lies over the structure morphism of `Z`, which is flat (Stacks 0787), and a flat
morphism of affine schemes induces a flat map on global functions. -/
theorem flat_structureSheaf_map_schemeStack
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (Z : FlatFppf B S hS (schemeStack.{u, w} B S hS U))
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z.obj.left)) :
    ((structureSheaf B S hS (schemeStack.{u, w} B S hS U)).obj.map
      ((isTerminalFlatObjectSchemeStackId.{u, w} B S hS U).from Z).op).hom.Flat := by
  have hflat : Flat ((BigFppfOver.toScheme B S hS).map Z.obj.hom) :=
    (flatObject_schemeStack_iff.{u, w} B S hS U Z.obj).1 Z.property
  have hleft : ((isTerminalFlatObjectSchemeStackId.{u, w} B S hS U).from Z).hom.left =
      Z.obj.hom := by
    simpa using Over.w ((isTerminalFlatObjectSchemeStackId.{u, w} B S hS U).from Z).hom
  change (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    ((isTerminalFlatObjectSchemeStackId.{u, w} B S hS U).from Z).hom.left).op).hom.Flat
  rw [hleft, Scheme.Γ_map_op]
  have := hU
  have := hZ
  exact (HasRingHomProperty.iff_of_isAffine (P := @Flat)
    (f := (BigFppfOver.toScheme B S hS).map Z.obj.hom)).1 hflat

section FreeResolution

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- Local bijectivity of sheafification of abelian sheaves on the flat-fppf site of the stack of a
scheme, as a local instance. -/
local instance : (topology B S hS (schemeStack.{u, w} B S hS U)).WEqualsLocallyBijective
    AddCommGrpCat.{u} :=
  AlgebraicGeometry.Stack.FlatFppf.wEqualsLocallyBijective_addCommGrpCat B S hS _

/-- Sheafification of abelian sheaves on the flat-fppf site of the stack of a scheme, as a local
instance. -/
local instance : HasSheafify (topology B S hS (schemeStack.{u, w} B S hS U)) AddCommGrpCat.{u} :=
  AlgebraicGeometry.Stack.FlatFppf.hasSheafify_addCommGrpCat B S hS _

/-- **A globally presented module on the flat-fppf site of an affine scheme has a free
resolution** (the free-resolution step of the proof of Stacks 07B3, part (2)): if `U` is affine
and `H` is a sheaf of modules on the flat-fppf site of `(Sch/U)_{fppf}` with a global
presentation (Stacks 03DE), there are a bounded above complex `F` whose terms are direct sums of
copies of the structure sheaf and a quasi-isomorphism `F ⟶ H[0]`. -/
theorem exists_quasiIso_isFree_schemeStack
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (H : SheafOfModules.{u} (Stacks.TensorByBaseModule.ringSheaf
      (topology B S hS (schemeStack.{u, w} B S hS U))
      (structureSheaf B S hS (schemeStack.{u, w} B S hS U))))
    (hH : H.IsPresentedByGlobalSections) :
    ∃ (F : CochainComplex (SheafOfModules.{u} (Stacks.TensorByBaseModule.ringSheaf
        (topology B S hS (schemeStack.{u, w} B S hS U))
        (structureSheaf B S hS (schemeStack.{u, w} B S hS U)))) ℤ)
      (π : F ⟶ (CochainComplex.singleFunctor _ 0).obj H),
      F.IsStrictlyLE 0 ∧ QuasiIso π ∧ ∀ n, (F.X n).IsFree :=
  Stacks.TerminalFreeResolution.exists_quasiIso_isFree_of_isPresentedByGlobalSections
    (structureSheaf B S hS (schemeStack.{u, w} B S hS U))
    (isTerminalFlatObjectSchemeStackId.{u, w} B S hS U)
    (fun Z => IsAffine ((BigFppfOver.toScheme B S hS).obj Z.obj.left))
    (generate_isAffine_mem_topology_schemeStack B S hS U)
    (fun Z hZ => flat_structureSheaf_map_schemeStack B S hS U hU Z hZ)
    (isQuasiCompactObject_schemeStack_id B S hS U (by
      have := hU; infer_instance))
    H hH

end FreeResolution

end AlgebraicGeometry.Stack.FlatFppf
