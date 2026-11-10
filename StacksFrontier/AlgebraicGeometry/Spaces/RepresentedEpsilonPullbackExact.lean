module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonNaiveCotangentMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.PullbackLeftAdjointFlat
public import StacksFrontier.CategoryTheory.Sites.Modules.PullbackRingULift
public import StacksFrontier.Cotangent.Spaces.RepresentableEpsilon

/-!
# `ε^*` for a represented algebraic space is exact at module sections in `Type (u + 1)`

Let `U` be an object of the big fppf site over `S : Scheme.{u}`, with underlying scheme `X₀`,
and let `X = h_U`.  The morphism `ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X₀})` of Stacks 08H7 is
presented by the functor `representedEpsilonFunctor` reading a Zariski open of `X₀` as an étale
chart of `X`, and its pullback of sheaves of modules with sections in `Type (u + 1)` is
`AlgebraicGeometry.Space.representedEpsilonModulePullback`, the one the naive cotangent complex
of Stacks 0D0X needs.  This file proves it exact, which is the second assertion of Stacks 08H8
at that universe.

The site functor of `ε` has a left adjoint, the image of an étale chart in `X₀`
(`AlgebraicGeometry.Space.representedImageOpenEpsilonAdjunction`), étale morphisms being open.  So,
after the structure rings are lifted to the universe of the modules
(`Stacks.UniverseLift.preservesFiniteLimits_pullback_of_liftedRingHom`), `ε^*` is the
sheafification of `M ↦ (V ↦ 𝒪_X(V) ⊗_{𝒪_{X₀}(f(V))} M(f(V)))`
(`Stacks.PullbackLeftAdjoint.pullbackIsoSheafifyModel`), and it is exact as soon as the ring maps
`𝒪_{X₀}(f(V)) ⟶ 𝒪_X(V)` are flat on a covering of every chart
(`Stacks.PullbackLeftAdjoint.preservesFiniteLimits_pullback`).  Those ring maps are the restriction
of functions from the image open (`AlgebraicGeometry.Space.representedTransposeRingHom_app`),
étale hence flat on the affine charts with affine image.

## Main results

* `AlgebraicGeometry.Space.representedTransposeRingHom_app`: the transpose of `ε^♯` along the
  image-open adjunction is the restriction from the image open.
* `AlgebraicGeometry.Space.preservesFiniteLimits_representedEpsilonModulePullback`: **`ε^*` is
  exact** on sheaves of modules with sections in `Type (u + 1)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **On a member of the affine-image covering, the restriction `𝒪_S(f(V)) ⟶ Γ(V, 𝒪_V)` is
flat**, being an étale ring map. -/
theorem flat_imageSectionsRestriction_affineImageCover (T : SmallEtale B S hS)
    (i : AffineImageIndex B S hS T) :
    ((imageSectionsRestriction B S hS).app (op ((affineImageCover B S hS T).X i))).hom.Flat := by
  have himg : imageOpen B S hS ((affineImageCover B S hS T).X i) = (i.down.2.1 : S.Opens) :=
    TopologicalSpace.Opens.ext
      ((imageOpen_coe B S hS _).trans (range_affineImageCover_X B S hS T i))
  have e : (⊤ : ((toScheme B S hS).obj ((affineImageCover B S hS T).X i)).Opens) ≤
      ((affineImageCover B S hS T).X i).obj.hom.hom ⁻¹ᵁ
        imageOpen B S hS ((affineImageCover B S hS T).X i) :=
    fun x _ => ⟨x, rfl⟩
  rw [imageSectionsRestriction_app_eq_appLE B S hS _ e]
  exact ((((affineImageCover B S hS T).X i).obj.hom.hom).appLE_congr e himg rfl
    (fun φ => φ.hom.Flat)).mpr (flat_appLE_affineImageCover B S hS T i _)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The image open is left adjoint to `ε`'s site functor** on the small étale site of `h_U`. -/
def representedImageOpenEpsilonAdjunction :
    representedImageOpenFunctor B S hS U ⊣ representedEpsilonFunctor B S hS U :=
  (representedSmallEtaleEquivalence B S hS U).toAdjunction.comp
    (_root_.AlgebraicGeometry.SmallEtale.imageOpenAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)

/-- `ε^♯` on sections over a Zariski open `Z` of `X₀` is the identification of the sections of
`𝒪_{X₀}` over `Z` with the global functions on the open subscheme `Z`. -/
theorem representedToZariskiRingedToposSiteHom_fSharp_app_apply
    (Z : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (t : ((BigFppfOver.toScheme B S hS).obj U).presheaf.obj (op Z)) :
    ((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom.app (op Z)).hom t =
      (Scheme.Opens.topIso Z).inv.hom t :=
  representedToSchemeZariskiRingedToposHom_forgetFSharp_app B S hS U Z t

/-- The structure sheaf of `X = h_U` is the structure sheaf of the small étale site of `X₀` read
through the equivalence of the two sites, on restriction maps too. -/
theorem representedStructureSheaf_map {V V' : SmallEtale B S hS (yoneda.obj U)} (g : V ⟶ V') :
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map g.op =
      (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
        ((representedSmallEtaleEquivalence B S hS U).functor.map g).op := rfl

/-- The unit of `representedImageOpenEpsilonAdjunction`, read on the small étale site of `X₀`, is
the factorization of an étale `X₀`-scheme through its image open. -/
theorem representedImageOpenEpsilonAdjunction_unit_map (V : SmallEtale B S hS (yoneda.obj U)) :
    (representedSmallEtaleEquivalence B S hS U).functor.map
      ((representedImageOpenEpsilonAdjunction B S hS U).unit.app V) =
    _root_.AlgebraicGeometry.SmallEtale.toImageOpen (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property
      ((representedSmallEtaleEquivalence B S hS U).functor.obj V) := by
  rw [representedImageOpenEpsilonAdjunction, Adjunction.comp_unit_app]
  exact (Functor.map_comp _ _ _).trans
    ((congrArg₂ (· ≫ ·) (representedSmallEtaleEquivalence_functor_map_unit B S hS U V)
      (representedSmallEtaleEquivalence_functor_map_inverse_map B S hS U _)).trans
      (Category.id_comp _))

/-- **The transpose of `ε^♯` along the image-open adjunction is the restriction from the image
open**: on an étale chart `V` of `X`, the ring map `𝒪_{X₀}(f(V)) ⟶ 𝒪_X(V)` is the pullback of
functions along the structure morphism of `V` over its image open. -/
theorem representedTransposeRingHom_app (V : SmallEtale B S hS (yoneda.obj U)) :
    (Stacks.PullbackLeftAdjoint.transposeRingHom (representedImageOpenEpsilonAdjunction B S hS U)
      ((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom)).app (op V) =
    (_root_.AlgebraicGeometry.SmallEtale.imageSectionsRestriction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).app
        (op ((representedSmallEtaleEquivalence B S hS U).functor.obj V)) := by
  refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
  have h1 := representedToZariskiRingedToposSiteHom_fSharp_app_apply B S hS U
    ((representedImageOpenFunctor B S hS U).obj V) t
  change ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O.obj.map
      ((representedImageOpenEpsilonAdjunction B S hS U).unit.app V).op).hom
    (((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom.app
      (op ((representedImageOpenFunctor B S hS U).obj V))).hom t) = _
  rw [h1, representedStructureSheaf_map, representedImageOpenEpsilonAdjunction_unit_map]
  rfl

/-- **The transposed ring maps of `ε^♯` are flat on a covering of every étale chart of `X`**:
the charts corresponding to the affine opens with affine image of an étale `X₀`-scheme. -/
theorem generate_flat_mem_topology (P : SmallEtale B S hS (yoneda.obj U) → Prop)
    (hP : ∀ (Y : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (i : _root_.AlgebraicGeometry.SmallEtale.AffineImageIndex (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property Y),
      P ((representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((_root_.AlgebraicGeometry.SmallEtale.affineImageCover (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property Y).X i)))
    (V : SmallEtale B S hS (yoneda.obj U)) :
    Sieve.generate (fun W (_ : W ⟶ V) => P W) ∈ SmallEtale.topology B S hS (yoneda.obj U) V := by
  let e := representedSmallEtaleEquivalence B S hS U
  rw [← representedSmallEtaleEquivalence_topology B S hS U,
    Functor.mem_inducedTopology_iff_of_isCoverDense]
  refine GrothendieckTopology.superset_covering _ ?_
    (_root_.AlgebraicGeometry.SmallEtale.mem_topology_sieve₀_affineImageCover
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
      (e.functor.obj V))
  refine (Sieve.generate_le_iff _ _).2 ((Presieve.ofArrows_le_iff).2 fun i => ?_)
  refine ⟨e.inverse.obj _, e.inverse.map
      ((_root_.AlgebraicGeometry.SmallEtale.affineImageCover (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property (e.functor.obj V)).f i) ≫
      e.unitIso.inv.app V, 𝟙 _, ⟨_, 𝟙 _, _, hP _ i, Category.id_comp _⟩, ?_⟩
  rw [Functor.map_comp, representedSmallEtaleEquivalence_functor_map_inverse_map,
    representedSmallEtaleEquivalence_functor_map_unitInv]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The transposed ring maps of `ε^♯` are flat on the charts of the affine-image covering. -/
theorem flat_representedTransposeRingHom
    (Y : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (i : _root_.AlgebraicGeometry.SmallEtale.AffineImageIndex (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property Y) :
    ((Stacks.PullbackLeftAdjoint.transposeRingHom (representedImageOpenEpsilonAdjunction B S hS U)
      ((representedToZariskiRingedToposSiteHom B S hS U).fSharp.hom)).app
        (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((_root_.AlgebraicGeometry.SmallEtale.affineImageCover (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property Y).X i)))).hom.Flat := by
  rw [representedTransposeRingHom_app]
  exact _root_.AlgebraicGeometry.SmallEtale.flat_imageSectionsRestriction_affineImageCover
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property Y i

/-- **`ε^*` on sheaves of modules with sections in `Type (u + 1)` is exact** (Stacks 08H8, second
assertion, for the small étale site of an algebraic space represented by a scheme).  After the
universe of the structure rings is raised to that of the modules
(`Stacks.UniverseLift.preservesFiniteLimits_pullback_of_liftedRingHom`), `ε^*` is the
sheafification of the objectwise extension of scalars `M ↦ 𝒪_X(V) ⊗ M(f(V))`, and the ring maps
`𝒪_{X₀}(f(V)) ⟶ 𝒪_X(V)` are étale, hence flat, on the affine charts with affine image. -/
theorem preservesFiniteLimits_representedEpsilonModulePullback :
    PreservesFiniteLimits (representedEpsilonModulePullback B S hS U) := by
  have : (representedToZariskiRingedToposSiteHom B S hS U).u.IsContinuous _ _ :=
    (representedToZariskiRingedToposSiteHom B S hS U).isContinuous
  have := Stacks.UniverseLift.isRightAdjoint_pushforward_liftedRingHom.{u + 1, u + 1}
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing
  refine Stacks.UniverseLift.preservesFiniteLimits_pullback_of_liftedRingHom.{u + 1, u + 1}
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing ?_
  have := Stacks.PullbackLeftAdjoint.isRightAdjoint_sheafPushforward
    (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing)
    (representedImageOpenEpsilonAdjunction B S hS U)
  have h2 : (SheafOfModules.pushforward.{u + 1} (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing)).IsRightAdjoint := this
  refine @Stacks.PullbackLeftAdjoint.preservesFiniteLimits_pullback _ _ _ _ _ _ _ _ _
    (representedImageOpenEpsilonAdjunction B S hS U) _ _ (Stacks.UniverseLift.liftedRingHom.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing) _ _ h2
    (hasSheafify_representedZariski_addCommGrpCat B S hS U)
    (wEqualsLocallyBijective_representedZariski_addCommGrpCat B S hS U)
    (hasSheafify_representedSmallEtale_addCommGrpCat B S hS U) ?_
  refine generate_flat_mem_topology B S hS U _ fun Y i => ?_
  have h := flat_representedTransposeRingHom B S hS U Y i
  rw [← RingHom.Flat.ulift_iff.{u + 1, u + 1}] at h
  exact h

end AlgebraicGeometry.Space

end
