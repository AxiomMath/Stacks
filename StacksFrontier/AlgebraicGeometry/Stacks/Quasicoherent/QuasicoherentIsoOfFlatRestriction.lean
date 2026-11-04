module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardBijectiveOnPresented
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectAtlasCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategorySiteKind
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator

/-!
# A morphism of quasi-coherent modules is detected on the flat objects

Let `𝒳` be an algebraic stack and `φ : 𝓜 ⟶ 𝓝` a morphism of quasi-coherent `𝒪_𝒳`-modules
(**Stacks 06WG**).  If `φ` is an isomorphism over every flat object of `𝒳` (**Stacks 0787**),
that is if `g^*φ` is an isomorphism for the restriction `g^*` to the flat-fppf site, then `φ` is an
isomorphism.

This is the step of **Stacks 07B1** (2)(a) that the source delegates to the comparison with
quasi-coherent modules on a presentation: "the map `g_!g^{-1}𝓕 ⟶ 𝓕` is a map of quasi-coherent
modules on `𝒳` whose restriction to any scheme flat over `𝒳` is an isomorphism ... it is an
isomorphism".  The proof here is local on the site: the flat objects `z` over which both modules
are globally presented cover it
(`AlgebraicGeometry.Stack.coversTop_flatObject_hasGlobalPresentation`), the slice at such a `z`
has the terminal object `𝟙 z`, which is flat, and restriction to the flat objects of the slice is
bijective on morphisms out of a globally presented module
(`Stacks.SheafOfModules.bijective_pushforward_map_of_hasGlobalPresentation`), hence reflects
isomorphisms between globally presented modules.

The module universe is `u + 1`, that of `AlgebraicGeometry.Stack.FlatFppf.moduleInverseImage`.

## Main results

* `AlgebraicGeometry.Stack.isIso_over_of_isIso_val_app_flatObject`: the slice statement.
* `AlgebraicGeometry.Stack.isIso_of_isIso_val_app_flatObject`: the statement on `𝒳`.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_of_isIso_moduleInverseImage_map`: the same with the
  hypothesis read as invertibility of `g^*φ`.

## References

* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The flat objects of the slice of `𝒳` at an object: the arrows `w ⟶ z` with `w` flat. -/
abbrev sliceFlatObject (z : 𝒳.val.val.obj) : ObjectProperty (Over z) :=
  fun w => flatObject B S hS 𝒳.val w.left

/-- The topology of the slice of the fppf site of `𝒳` at an object is the topology the slice
inherits as a category fibred in groupoids over the schemes over `S`. -/
theorem associatedTopology_overForget_comp (z : 𝒳.val.val.obj) :
    BigFppfOver.associatedTopology B S hS (Over.forget z ⋙ 𝒳.val.val.p) .fppf =
      (fppfTopology B S hS 𝒳.val).over z :=
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  Functor.inheritedTopology_overForget_comp 𝒳.val.val.p _ z

/-- The flat objects of a slice are closed under the pullbacks of **Stacks 07AK** (1) for the
fppf topology. -/
theorem isClosedUnderSitePullback_sliceFlatObject (z : 𝒳.val.val.obj) :
    IsClosedUnderSitePullback B S hS (Over.forget z ⋙ 𝒳.val.val.p)
      (sliceFlatObject B S hS 𝒳 z) .fppf :=
  Or.inr ⟨rfl, fun f hflat _ hy => flatObject_of_flat B S hS 𝒳 f.left hflat hy⟩

/-- The slice of `𝒳` at an object, viewed over the schemes over `S` through `Over.forget z`, is
fibred in groupoids. -/
theorem isFiberedInGroupoids_overForget_comp (z : 𝒳.val.val.obj) :
    (Over.forget z ⋙ 𝒳.val.val.p).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.comp _ _ (Functor.IsFiberedInGroupoids.over_forget z)
    𝒳.val.isFiberedInGroupoids

/-- The inclusion of the flat objects of a slice is continuous. -/
theorem isContinuous_ι_sliceFlatObject (z : 𝒳.val.val.obj) :
    (sliceFlatObject B S hS 𝒳 z).ι.IsContinuous
      ((sliceFlatObject B S hS 𝒳 z).ι.inheritedTopology ((fppfTopology B S hS 𝒳.val).over z))
      ((fppfTopology B S hS 𝒳.val).over z) := by
  have h := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    (Over.forget z ⋙ 𝒳.val.val.p) (sliceFlatObject B S hS 𝒳 z) .fppf
    (isFiberedInGroupoids_overForget_comp B S hS 𝒳 z)
    (isClosedUnderSitePullback_sliceFlatObject B S hS 𝒳 z)
  rwa [associatedTopology_overForget_comp] at h

/-- The inclusion of the flat objects of a slice is cocontinuous. -/
theorem isCocontinuous_ι_sliceFlatObject (z : 𝒳.val.val.obj) :
    (sliceFlatObject B S hS 𝒳 z).ι.IsCocontinuous
      ((sliceFlatObject B S hS 𝒳 z).ι.inheritedTopology ((fppfTopology B S hS 𝒳.val).over z))
      ((fppfTopology B S hS 𝒳.val).over z) := by
  have h := isCocontinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    (Over.forget z ⋙ 𝒳.val.val.p) (sliceFlatObject B S hS 𝒳 z) .fppf
    (isFiberedInGroupoids_overForget_comp B S hS 𝒳 z)
    (isClosedUnderSitePullback_sliceFlatObject B S hS 𝒳 z)
  rwa [associatedTopology_overForget_comp] at h

variable {R : Sheaf (fppfTopology B S hS 𝒳.val) RingCat.{u}}

/-- **On the slice at a flat object, a morphism between globally presented modules which is an
isomorphism at every flat object is an isomorphism.** -/
theorem isIso_over_of_isIso_val_app_flatObject {M N : SheafOfModules.{u + 1} R} (φ : M ⟶ N)
    (hφ : ∀ x, flatObject B S hS 𝒳.val x → IsIso (φ.val.app (op x)))
    {z : 𝒳.val.val.obj} (hz : flatObject B S hS 𝒳.val z)
    (hM : (M.over z).HasGlobalPresentation) (hN : (N.over z).HasGlobalPresentation) :
    IsIso (φ.over z) := by
  let P := sliceFlatObject B S hS 𝒳 z
  let K := (fppfTopology B S hS 𝒳.val).over z
  let KP := P.ι.inheritedTopology K
  have := isContinuous_ι_sliceFlatObject B S hS 𝒳 z
  have := isCocontinuous_ι_sliceFlatObject B S hS 𝒳 z
  have : HasSheafify K AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} K
  have : K.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} K
  have : HasSheafify KP AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} KP
  have : KP.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} KP
  let S' := (P.ι.sheafPushforwardContinuous RingCat.{u} KP K).obj (R.over z)
  let G := SheafOfModules.pushforward.{u + 1} (𝟙 S')
  have : PreservesColimitsOfSize.{u + 1, u + 1} G :=
    Stacks.SheafOfModules.pushforward_preservesColimits P.ι (𝟙 S')
  have hZD : IsTerminal (Over.mk (𝟙 z)) := Over.mkIdTerminal
  let ZC : P.FullSubcategory := ⟨Over.mk (𝟙 z), hz⟩
  have hZC : IsTerminal ZC := IsTerminal.isTerminalOfObj P.ι ZC hZD
  refine Stacks.SheafOfModules.isIso_of_isIso_pushforward_map_of_hasGlobalPresentation
    (𝟙 S') hZC hZD (Iso.refl _) hM hN (φ.over z) ?_
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun W => ?_
  have h1 := hφ W.unop.obj.left W.unop.property
  rw [ConcreteCategory.isIso_iff_bijective] at h1 ⊢
  exact h1

/-- **A morphism of quasi-coherent modules on an algebraic stack which is an isomorphism at every
flat object is an isomorphism.** -/
theorem isIso_of_isIso_val_app_flatObject {M N : SheafOfModules.{u + 1} R}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (hφ : ∀ x, flatObject B S hS 𝒳.val x → IsIso (φ.val.app (op x))) : IsIso φ :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over
    (coversTop_flatObject_hasGlobalPresentation B S hS 𝒳 M N hM hN) φ fun i =>
      isIso_over_of_isIso_val_app_flatObject B S hS 𝒳 φ hφ i.2.1 i.2.2.1 i.2.2.2

namespace FlatFppf

/-- **A morphism of quasi-coherent modules on an algebraic stack whose restriction to the
flat-fppf site is an isomorphism is an isomorphism**, at module universe `u + 1`. -/
theorem isIso_of_isIso_moduleInverseImage_map
    {M N : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (hφ : IsIso ((moduleInverseImage B S hS 𝒳).map φ)) : IsIso φ :=
  isIso_of_isIso_val_app_flatObject B S hS 𝒳 hM hN φ fun x hx =>
    Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app ((moduleInverseImage B S hS 𝒳).map φ)
      (op (⟨x, hx⟩ : FlatFppf B S hS 𝒳))

end FlatFppf

end AlgebraicGeometry.Stack
