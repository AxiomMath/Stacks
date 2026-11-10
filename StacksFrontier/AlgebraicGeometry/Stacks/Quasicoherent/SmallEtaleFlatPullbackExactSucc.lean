module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackColimitFlatInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedPullbackUnivLE
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Faithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections

/-!
# Left exactness of `a_{small}^*` along a flat morphism, at section universe `u + 1`

Let `a : X ⟶ Y` be a flat morphism of schemes of a big étale site `E`.  This file proves that the
inverse image of sheaves of modules along the morphism of small étale ringed sites
`ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` is left exact for modules with sections in `Type (u + 1)`.
At section universe `u` this is
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_smallEtaleStructureMapRing`, proved
through the stalks of algebraic spaces; that route is pinned to universe `u`.

The proof here is the direct one.  The inverse image is the sheafification of the pullback of
presheaves of modules, and that pullback is objectwise extension of scalars followed by the
objectwise filtered colimit `colim_{(V, W ⟶ V ×_Y X)} 𝒪(W) ⊗_{𝒪(V ×_Y X)} (−)` of
`Stacks.PullbackColimitUnivLE`.  The index categories are filtered because base change preserves
finite limits.  An index `(V, W ⟶ V ×_Y X)` with `V` and `W` affine has a flat composite ring map
`𝒪(V) ⟶ 𝒪(W)`, since `W ⟶ V ×_Y X` is étale and `V ×_Y X ⟶ V` is a base change of `a`; and
locally on `W` every index is dominated by such a one, the affine objects being cover-dense on both
small étale sites.  So the presheaf pullback of a monomorphism is locally injective
(`Stacks.PullbackColimitUnivLE.isLocallyInjective_colimitPullback_map_extendScalars_map`), its
sheafification is a monomorphism, and a right exact functor between abelian categories preserving
monomorphisms is left exact.

## Main results

* `AlgebraicGeometry.SmallEtale.pullbackIsoColimitModel`: the pullback of presheaves of modules
  along the structure map of `ε_a` is extension of scalars followed by the colimit model.
* `AlgebraicGeometry.SmallEtale.generate_flat_mem_topology`: locally, every index is dominated
  by one with flat composite ring map.
* `AlgebraicGeometry.SmallEtale.mono_sheafification_pullback_map`: the inverse image of a
  monomorphism, at section universe `u + 1`, is a monomorphism.
* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_sheafificationPullback_succ`: the inverse
  image is left exact, at section universe `u + 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) {X Y : E.Scheme} (a : X ⟶ Y)

/-- **The pullback of presheaves of modules along the structure map of `ε_a` is the colimit
model**: objectwise extension of scalars along `a_{small}^♯` followed by the objectwise colimit
`Stacks.PullbackColimitUnivLE.colimitPullback`, both being left adjoint to the direct image. -/
noncomputable def pullbackIsoColimitModel :
    PresheafOfModules.pullback.{u + 1} (smallEtaleStructureMapRing E a).hom ≅
      Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u + 1}
          (Functor.whiskerRight (structureSharp E a).hom (forget₂ CommRingCat RingCat)) ⋙
        Stacks.PullbackColimitUnivLE.colimitPullback (smallEtaleBaseChange E a)
          (SmallEtale.commRingStructurePresheaf E X.obj X.property) :=
  Adjunction.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction.{u + 1} _)
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalarsAdjunction.{u + 1} _).comp
      (Stacks.PullbackColimitUnivLE.colimitPullbackAdjunction _ _))

/-- The index categories of the colimit model are filtered: base change preserves finite
limits. -/
theorem isFiltered_costructuredArrow_op_smallEtaleBaseChange
    (W : (SmallEtale E X.obj X.property)ᵒᵖ) :
    IsFiltered (CostructuredArrow (smallEtaleBaseChange E a).op W) :=
  IsFiltered.of_equivalence
    (structuredArrowOpEquivalence (smallEtaleBaseChange E a) (Opposite.unop W))

/-- **The composite ring map at an index between affine objects is flat.**  For `V` affine in
`Y_étale`, `W` affine in `X_étale` and `k : W ⟶ V ×_Y X`, the map `𝒪(V) ⟶ 𝒪(V ×_Y X) ⟶ 𝒪(W)`
is the map on global sections of the flat morphism `W ⟶ V ×_Y X ⟶ V` of affine schemes. -/
theorem flat_commRingStructurePresheaf_map_comp_structureSharp (ha : Flat (E.inclusion.map a))
    {W : SmallEtale E X.obj X.property} {V : SmallEtale E Y.obj Y.property}
    (hW : _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme E X.obj X.property).obj W))
    (hV : _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme E Y.obj Y.property).obj V))
    (k : W ⟶ (smallEtaleBaseChange E a).obj V) :
    (((SmallEtale.commRingStructurePresheaf E X.obj X.property).map k.op).hom.comp
      ((structureSharp E a).hom.app (op V)).hom).Flat := by
  let m := (SmallEtale.toScheme E X.obj X.property).map k ≫
    E.inclusion.map (pullback.fst V.obj.hom a)
  have hm : Flat m := MorphismProperty.comp_mem @Flat _ _
    (Etale.iff_flat_and_formallyUnramified.mp
      (etale_toScheme_map (B := E) (S := X.obj) (hS := X.property) k)).1
    (MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback V.obj.hom a).map E.inclusion).flip ha)
  have : _root_.AlgebraicGeometry.IsAffine (E.inclusion.obj V.obj.left) := hV
  have heq : Scheme.Γ.map m.op =
      Scheme.Γ.map (op (E.inclusion.map (pullback.fst V.obj.hom a))) ≫
        Scheme.Γ.map ((SmallEtale.toScheme E X.obj X.property).map k).op :=
    Functor.map_comp _ _ _
  change ((Scheme.Γ.map (op (E.inclusion.map (pullback.fst V.obj.hom a))) ≫
    Scheme.Γ.map ((SmallEtale.toScheme E X.obj X.property).map k).op).hom).Flat
  rw [← heq]
  exact HasRingHomProperty.appTop (P := @Flat) m hm

/-- **Locally, every index is dominated by one with flat composite ring map.**  For an object `W`
of `X_étale` and an index `T = (V, W ⟶ V ×_Y X)`, the arrows `g : W' ⟶ W` along which the
restricted index maps to an index whose composite ring map is flat generate a covering sieve: cover
`V` by affine objects, pull that covering back to `W` along `W ⟶ V ×_Y X`, and cover the members
by affine objects. -/
theorem generate_flat_mem_topology (ha : Flat (E.inclusion.map a))
    (W : SmallEtale E X.obj X.property)
    (T : CostructuredArrow (smallEtaleBaseChange E a).op (op W)) :
    Sieve.generate (fun W' (g : W' ⟶ W) =>
      ∃ (T' : CostructuredArrow (smallEtaleBaseChange E a).op (op W'))
        (_ : CostructuredArrow.mk (T.hom ≫ g.op) ⟶ T'),
          (((SmallEtale.commRingStructurePresheaf E X.obj X.property).map T'.hom).hom.comp
            ((structureSharp E a).hom.app T'.left).hom).Flat) ∈
      SmallEtale.topology E X.obj X.property W := by
  let FF := smallEtaleBaseChange E a
  let JX := SmallEtale.topology E X.obj X.property
  let JY := SmallEtale.topology E Y.obj Y.property
  let GX := SmallAffineEtale.inclusion E X.obj X.property
  let GY := SmallAffineEtale.inclusion E Y.obj Y.property
  have : GX.IsCoverDense JX :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous E X.obj X.property).2.isCoverDense'
  have : GY.IsCoverDense JY :=
    (SmallAffineEtale.inclusion_isSpecialCocontinuous E Y.obj Y.property).2.isCoverDense'
  let h : W ⟶ FF.obj T.left.unop := T.hom.unop
  have hcp : CoverPreserving JY JX FF := Functor.isContinuous_iff_coverPreserving.1 inferInstance
  have h3 : (Sieve.functorPushforward FF (Sieve.coverByImage GY T.left.unop)).pullback h ∈ JX W :=
    JX.pullback_stable h (hcp.cover_preserve (GY.is_cover_of_isCoverDense JY T.left.unop))
  refine JX.transitive h3 _ fun W₁ g₁ hg₁ => ?_
  refine JX.superset_covering ?_ (GX.is_cover_of_isCoverDense JX W₁)
  rintro W₂ p ⟨⟨W₀, lift, q, rfl⟩⟩
  obtain ⟨V₂, m₂, k₂, ⟨⟨Vj, m₃, m, rfl⟩⟩, hk₂⟩ := hg₁
  refine ⟨_, lift, q ≫ g₁, ⟨CostructuredArrow.mk (q ≫ k₂ ≫ FF.map m₃).op,
    CostructuredArrow.homMk m.op ?_, ?_⟩, by rw [Category.assoc]⟩
  · apply Quiver.Hom.unop_inj
    change (q ≫ k₂ ≫ FF.map m₃) ≫ FF.map m = (q ≫ g₁) ≫ h
    rw [Category.assoc, Category.assoc, ← FF.map_comp, Category.assoc]
    exact congrArg (q ≫ ·) hk₂.symm
  · exact flat_commRingStructurePresheaf_map_comp_structureSharp E a ha W₀.property Vj.property
      (q ≫ k₂ ≫ FF.map m₃)

/-- **The inverse image of a monomorphism along a flat morphism is a monomorphism**, at section
universe `u + 1`.  The pullback of presheaves of modules of a monomorphism of sheaves is locally
injective, by the colimit model (`AlgebraicGeometry.SmallEtale.pullbackIsoColimitModel`), the
filteredness of its index categories and the local flatness of
`AlgebraicGeometry.SmallEtale.generate_flat_mem_topology`; sheafification carries a locally
injective morphism to a monomorphism. -/
theorem mono_sheafification_pullback_map (ha : Flat (E.inclusion.map a))
    {M N : SheafOfModules.{u + 1} (SmallEtale.structureSheaf E Y.obj Y.property)} (f : M ⟶ N)
    [Mono f] :
    Mono ((SheafOfModules.forget _ ⋙
      PresheafOfModules.pullback.{u + 1} (smallEtaleStructureMapRing E a).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := (SmallEtale.structureSheaf E X.obj X.property).obj) (𝟙 _)).map f) := by
  let JX := SmallEtale.topology E X.obj X.property
  have hi : ∀ V, Function.Injective (PresheafOfModules.Hom.app f.val V) := fun V => by
    have : PreservesFiniteLimits (SheafOfModules.evaluation.{u + 1}
        (SmallEtale.structureSheaf E Y.obj Y.property) V) :=
      SheafOfModules.Finite.evaluationPreservesFiniteLimits.{u + 1}
        (R := SmallEtale.structureSheaf E Y.obj Y.property) V
    exact (ModuleCat.mono_iff_injective _).1
      ((SheafOfModules.evaluation.{u + 1}
        (SmallEtale.structureSheaf E Y.obj Y.property) V).map_mono f)
  have := fun W => isFiltered_costructuredArrow_op_smallEtaleBaseChange E a W
  have hL := Stacks.PullbackColimitUnivLE.isLocallyInjective_colimitPullback_map_extendScalars_map
    (smallEtaleBaseChange E a) (SmallEtale.commRingStructurePresheaf E X.obj X.property)
    (structureSharp E a).hom JX (generate_flat_mem_topology E a ha) f.val hi
  let iso := pullbackIsoColimitModel E a
  let P := PresheafOfModules.toPresheaf (SmallEtale.structureSheaf E X.obj X.property).obj
  let LE := (Stacks.PullbackColimitUnivLE.colimitPullback (smallEtaleBaseChange E a)
      (SmallEtale.commRingStructurePresheaf E X.obj X.property)).map
    ((Stacks.NoncommChangeOfRings.Presheaf.extendScalars.{u + 1}
      (Functor.whiskerRight (structureSharp E a).hom (forget₂ CommRingCat RingCat))).map f.val)
  have hinjM : ∀ V, Function.Injective (PresheafOfModules.Hom.app (iso.hom.app M.val) V) :=
    fun V => ((PresheafOfModules.evaluation _ V).mapIso (iso.app M.val)).toLinearEquiv.injective
  have h3 : Presheaf.IsLocallyInjective JX (P.map ((PresheafOfModules.pullback.{u + 1}
      (smallEtaleStructureMapRing E a).hom).map f.val)) := by
    refine ⟨fun {U} x y hxy => ?_⟩
    have hnat : ∀ z, PresheafOfModules.Hom.app LE U
          (PresheafOfModules.Hom.app (iso.hom.app M.val) U z) =
        PresheafOfModules.Hom.app (iso.hom.app N.val) U (PresheafOfModules.Hom.app
          ((PresheafOfModules.pullback.{u + 1} (smallEtaleStructureMapRing E a).hom).map f.val)
            U z) :=
      fun z => (congrArg (fun k => PresheafOfModules.Hom.app k U z)
        (iso.hom.naturality f.val)).symm
    have key := hL.equalizerSieve_mem (PresheafOfModules.Hom.app (iso.hom.app M.val) U x)
      (PresheafOfModules.Hom.app (iso.hom.app M.val) U y)
      ((hnat x).trans ((congrArg _ hxy).trans (hnat y).symm))
    refine JX.superset_covering (fun W g hg => hinjM (op W) ?_) key
    exact (PresheafOfModules.naturality_apply (iso.hom.app M.val) g.op x).trans
      (hg.trans (PresheafOfModules.naturality_apply (iso.hom.app M.val) g.op y).symm)
  have hinj := (Sheaf.isLocallyInjective_iff_injective _).mp
    ((Presheaf.isLocallyInjective_presheafToSheaf_map_iff JX _).mpr h3)
  refine ⟨fun x y hxy => ?_⟩
  ext U z
  exact hinj U (congrArg (fun k => k.val.app U z) hxy)

/-- **`a_{small}^*` along a flat morphism is left exact**, at section universe `u + 1`.  It is
right exact, being left adjoint to the direct image, and preserves monomorphisms by
`AlgebraicGeometry.SmallEtale.mono_sheafification_pullback_map`; a functor between abelian
categories with these two properties preserves homology, hence finite limits. -/
theorem preservesFiniteLimits_sheafificationPullback_succ (ha : Flat (E.inclusion.map a)) :
    PreservesFiniteLimits (SheafOfModules.forget (SmallEtale.structureSheaf E Y.obj Y.property) ⋙
      PresheafOfModules.pullback.{u + 1} (smallEtaleStructureMapRing E a).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := (SmallEtale.structureSheaf E X.obj X.property).obj) (𝟙 _)) := by
  let L := SheafOfModules.forget (SmallEtale.structureSheaf E Y.obj Y.property) ⋙
    PresheafOfModules.pullback.{u + 1} (smallEtaleStructureMapRing E a).hom ⋙
      PresheafOfModules.sheafification
        (R₀ := (SmallEtale.structureSheaf E X.obj X.property).obj) (𝟙 _)
  have adj : L ⊣ SheafOfModules.pushforward.{u + 1} (smallEtaleStructureMapRing E a) :=
    SheafOfModules.PullbackConstruction.adjunction.{u + 1} (smallEtaleStructureMapRing E a)
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : L.PreservesMonomorphisms := ⟨fun f _ => mono_sheafification_pullback_map E a ha f⟩
  have : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  have : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  have : L.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels L
  exact L.preservesFiniteLimits_of_preservesHomology

end AlgebraicGeometry.SmallEtale

end
