module

public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Colimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits

/-!
# The localization of a fibred site at an object, as an equivalence of ringed sites

Stacks 06WI tests quasi-coherence of a sheaf of modules on a category `𝒳` fibred in groupoids
over `(Sch/S)_fppf` one object at a time: `𝓕` is quasi-coherent exactly when its restriction to
`𝒳_fppf/x` is quasi-coherent for every object `x`, and `𝒳_fppf/x` *is* the big fppf site
`(Sch/U)_fppf` of the scheme `U = p(x)`.  This file makes that identification an equivalence of
**ringed** sites and uses it to transfer closure of quasi-coherence under colimits from the big
fppf site of a scheme to the associated fppf site of `𝒳`.

Three things are needed and all three are here.  The equivalence of *categories* is the
localization of Stacks 0CN0 followed by the comparison of the iterated slice
`((Sch/S)_fppf)/U` with `(Sch/U)_fppf`.  That it is an equivalence of *sites* needs the
correspondence of coverings of Stacks 0CN0, whose hypothesis — that the topology of `𝒳` is the
one inherited from the base — is verified for `CategoryTheory.Functor.inheritedTopology` itself
in the first section.  And it is an equivalence of *ringed* sites on the nose: the structure
sheaf of `𝒳` is by construction the restriction along `p` of the structure sheaf of
`(Sch/S)_fppf`, and `CategoryTheory.Over.iteratedSliceForward_forget` is an equality of
functors, so the two structure sheaves are equal rather than merely isomorphic.

## Main results

* `CategoryTheory.Functor.coverPreserving_inheritedTopology`: **Stacks 06NW for the structure
  functor** — a fibred category over a site is cover preserving from the topology it inherits to
  the topology of the base.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_over`: quasi-coherence is stable under
  restriction to a slice site.
* `AlgebraicGeometry.FibredSite.localizationEquivalence` and
  `AlgebraicGeometry.FibredSite.isDenseSubsite_localizationEquivalence_functor`:
  **Stacks 06WI, the equivalence of sites `𝒳_fppf/x ≌ (Sch/U)_fppf`.**
* `AlgebraicGeometry.FibredSite.reindexRing_localizationEquivalence`: **its ringed half** — the
  restricted structure sheaf of `𝒳` is the transported structure sheaf of `(Sch/U)_fppf`.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_over_eq_inverseImage` and
  `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_localization_iff`: hence
  quasi-coherence on `𝒳_fppf/x` is quasi-coherence on `(Sch/U)_fppf`, by Stacks 03DM at clause
  (6) of Stacks 03DL.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_iff_forall_objectInverseImage`:
  **Stacks 06WI**, a sheaf of modules on `𝒳` is quasi-coherent exactly when `x^*𝓕` is
  quasi-coherent on `(Sch/U)_fppf` for every object `x` of `𝒳`.
* `AlgebraicGeometry.FibredSite.preservesColimitsOfShape_overFunctor`: restriction to the
  localization commutes with colimits, Modules on Sites, Lemma 03DC.
* `AlgebraicGeometry.FibredSite.closedUnderColimitsOfSize_ringStructureSheafCore_of_base`:
  **the reduction step of Stacks 06WN**, assembled from the three: closure of quasi-coherence
  under colimits on the associated fppf site of an essentially small `𝒳`, granted closure on
  the big fppf site of every scheme of `B`.

## Implementation notes

Only tag 06WI is placed, on the biconditional at `𝓕` rather than on any of the statements that
consume it: that biconditional is its covering set.  Tag 0CN0 is already covered in
`StacksFrontier.CategoryTheory.Sites.Gerbe.Localization`, and tag 03DM is the single assertion that
all eight clauses of Stacks 03DL are intrinsic, of which only clause (6) is available.

The right-hand side of Stacks 06WI is quasi-coherence of `x^*𝓕` on `(Sch/U)_fppf`, not on
`𝒳_fppf/x`, so it is stated for `AlgebraicGeometry.FibredSite.objectInverseImage`: restriction
to `𝒳_fppf/x` followed by transport along `localizationEquivalence`, which is the restriction
along the 1-morphism `(Sch/U)_fppf ⥤ 𝒳` that `x` is.  Sufficiency needs no input beyond
Stacks 03DN at the family of all objects of `𝒳`, because quasi-coherence is local and intrinsic;
necessity is `Stacks.SheafOfModules.isQuasicoherentOnSite_over` on `𝒳` itself.

The two results in the `Stacks.SheafOfModules` namespace duplicate the content of the `private`
declarations `hasGlobalPresentation_iteratedSlice_symm` and `isQuasicoherent_over` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence`; they are restated
here, under different names, because those are private and are being de-privatized by another
change in flight.  When that lands these should be deleted in favour of it.

The witness `CategoryTheory.Functor.isInheritedTopology_inheritedTopology` that Stacks 0CN0
needs — `CategoryTheory.Functor.IsInheritedTopology` is a characterisation of a *given*
topology, so until one topology is shown to satisfy it the tag is unusable — is in
`StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization` and is imported from there.
Its other half is cover preservation of the structure functor, which is
`CategoryTheory.Functor.coverPreserving_inheritedTopology` below: Stacks 06NW applied with
`q = 𝟭` together with the fact that the topology the identity inherits is coarser than the
given one.

## References

* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0CN0](https://stacks.math.columbia.edu/tag/0CN0)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- The topology the identity functor inherits from a topology on `𝒞` is coarser than that
topology: a covering family of the inherited precoverage has a covering family of images, and
the images are the family itself. -/
public theorem inheritedTopology_id_le (J : GrothendieckTopology 𝒞) :
    (𝟭 𝒞).inheritedTopology J ≤ J := by
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.2
  intro X R hR
  simpa using hR.2

/-- **Stacks 06NW for the structure functor.**  A fibred category over a site is cover
preserving from the topology it inherits to the topology of the base. -/
public theorem coverPreserving_inheritedTopology [HasPullbacks 𝒞]
    (p : 𝒮 ⥤ 𝒞) [p.IsFibered] (J : GrothendieckTopology 𝒞) :
    CoverPreserving (p.inheritedTopology J) J p := by
  have : (𝟭 𝒞).IsFibered := isFiberedInGroupoids_id.isFibered
  have := ((isFibredOneMorphism_id p).isContinuous_and_isCocontinuous_inheritedTopology J).1
  have h : CoverPreserving (p.inheritedTopology J) ((𝟭 𝒞).inheritedTopology J) p :=
    CoverPreserving.of_isContinuous p _ _
  exact ⟨fun hS => inheritedTopology_id_le J _ (h.cover_preserve hS)⟩

end CategoryTheory.Functor

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Restriction to the iterated slice over `V` has the same sections as restriction to the slice
over `V.left`, because `CategoryTheory.Over.iteratedSliceForward_forget` is an equality of
functors. -/
public theorem over_over_eq_over_left (M : SheafOfModules.{w} R) (U : C) (V : Over U) :
    (SheafOfModules.pushforward.{w}
      (F := (Over.iteratedSliceEquiv V).functor)
      (S := (R.over U).over V) (R := R.over V.left)
      (𝟙 _ : ((R.over U).over V) ⟶
        ((Over.iteratedSliceEquiv V).functor.sheafPushforwardContinuous
          RingCat ((J.over U).over V) (J.over V.left)).obj (R.over V.left))).obj
      (M.over V.left) = (M.over U).over V := rfl

/-- **A global presentation of the restriction to `V.left` restricts to the iterated slice over
`V`.**  The two restrictions have the same sections — `over_over_eq_over_left` — and the
comparison of the two sites is the equivalence `CategoryTheory.Over.iteratedSliceEquiv`, so
`Stacks.SheafOfModules.hasGlobalPresentation_map` carries the presentation across. -/
public theorem hasGlobalPresentation_overIteratedSlice (M : SheafOfModules.{w} R) (U : C)
    (V : Over U) (h : (M.over V.left).HasGlobalPresentation) :
    ((M.over U).over V).HasGlobalPresentation := by
  let E := Over.iteratedSliceEquiv V
  let φ : ((R.over U).over V) ⟶
      (E.functor.sheafPushforwardContinuous RingCat ((J.over U).over V)
        (J.over V.left)).obj (R.over V.left) := 𝟙 _
  let F₀ := SheafOfModules.pushforward.{w} φ
  let F := SheafOfModules.pushforward.{max (max u v) v w} φ
  let eHi : SheafOfModules.{max (max u v) v w} (R.over V.left) ≌
      SheafOfModules.{max (max u v) v w} ((R.over U).over V) :=
    SheafOfModules.pushforwardPushforwardEquivalence E φ (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  have : F.IsLeftAdjoint := eHi.isLeftAdjoint_functor
  have : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hη₁ : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, w,
      max (max u v) v w} (SheafOfModules.unit (R.over V.left))) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max (max u v) v w}
        (SheafOfModules.unit ((R.over U).over V)) :=
    pushforwardUliftIso.{max u v, v, w, w, max (max u v) v w} φ
      (SheafOfModules.unit (R.over V.left))
  have hηM : F.obj (SheafOfModules.uliftForPresentation.{max u v, v, w, w,
      max (max u v) v w} (M.over V.left)) ≅
      SheafOfModules.uliftForPresentation.{max u v, v, w, w, max (max u v) v w}
        (F₀.obj (M.over V.left)) :=
    pushforwardUliftIso.{max u v, v, w, w, max (max u v) v w} φ (M.over V.left)
  have h' : (F₀.obj (M.over V.left)).HasGlobalPresentation :=
    hasGlobalPresentation_map (F₀ := F₀) (F := F) (M.over V.left) hη₁ hηM h
  rwa [over_over_eq_over_left M U V] at h'

/-- **Quasi-coherence is stable under restriction to a slice site**, the necessity half of
Stacks 03DN for quasi-coherence: the restriction of a quasi-coherent sheaf of modules to the
slice site over an object is quasi-coherent there.  A covering of `V.left` with global
presentations is read in the slice as a covering of `V`, and
`hasGlobalPresentation_overIteratedSlice` carries the presentations. -/
public theorem isQuasicoherentOnSite_over (M : SheafOfModules.{w} R)
    (hM : M.IsQuasicoherentOnSite) (U : C) : (M.over U).IsQuasicoherentOnSite := by
  refine ⟨fun V => ?_⟩
  obtain ⟨I, W, g, hcover, hpres⟩ := hM.locally_hasGlobalPresentation V.left
  refine ⟨I, fun i => Over.mk (g i ≫ V.hom), fun i => Over.homMk (g i) (by simp), ?_,
    fun i => hasGlobalPresentation_overIteratedSlice M U _ (hpres i)⟩
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  simpa using hcover

/-- A sheaf of modules is quasi-coherent once its restriction to every slice site is. -/
private theorem isQuasicoherentOnSite_of_forall_over (M : SheafOfModules.{w} R)
    (h : ∀ U : C, (M.over U).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite := by
  rw [isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite M]
  exact ⟨ULift C, fun i => i.down, coversTop_ulift_self _, fun i => h i.down⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The localization of the associated fppf site of `𝒳` at an object `x`. -/
public abbrev localizedTopology (x : 𝒳) : GrothendieckTopology (Over x) :=
  (BigFppfOver.associatedTopology B S hS p .fppf).over x

/-- The scheme `U = p(x)` an object `x` of `𝒳` lies over. -/
public abbrev baseScheme (x : 𝒳) : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj (p.obj x)

/-- The scheme an object of `𝒳` lies over is one of the big fppf site. -/
public theorem contains_baseScheme (x : 𝒳) : B.Contains (baseScheme B S hS p x) :=
  (p.obj x).left.2

/-- **Stacks 06WI, the equivalence of categories `𝒳/x ≌ (Sch/U)_fppf`.**  It is the
localization of `p` at `x` (Stacks 0CN0) followed by the comparison of the iterated slice
`((Sch/S)_fppf)/U` with `(Sch/U)_fppf`, which is an equality of categories. -/
public noncomputable def localizationEquivalence (x : 𝒳) :
    Over x ≌ BigFppfOver B (baseScheme B S hS p x) (contains_baseScheme B S hS p x) :=
  (hp.overPostEquivalence x).trans (Over.iteratedSliceEquiv (p.obj x))

/-- **Stacks 06WI, the equivalence of sites `𝒳_fppf/x ≌ (Sch/U)_fppf`.**  A sieve of `𝒳_fppf/x`
is covering exactly when its image is: on the `Over.post p` factor this is the correspondence of
coverings of Stacks 0CN0, whose hypothesis is `isInheritedTopology_inheritedTopology`, and on
the iterated-slice factor it is Mathlib's dense-subsite instance for
`CategoryTheory.Over.iteratedSliceEquiv`. -/
public instance isDenseSubsite_localizationEquivalence_functor (x : 𝒳) :
    (localizationEquivalence B S hS p hp x).functor.IsDenseSubsite
      (localizedTopology B S hS p x)
      (BigFppfOver.topology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x)) where
  functorPushforward_mem_iff {Y T} := by
    have hd : (Over.iteratedSliceForward (p.obj x)).IsDenseSubsite
        ((BigFppfOver.baseOverTopology B S hS .fppf).over (p.obj x))
        (BigFppfOver.topology B ((BigFppfOver.toScheme B S hS).obj (p.obj x))
          (p.obj x).left.2) :=
      inferInstanceAs ((Over.iteratedSliceEquiv (p.obj x)).functor.IsDenseSubsite
        ((B.topology.over (B.obj hS)).over (p.obj x)) (B.topology.over (p.obj x).left))
    have : p.IsFibered := hp.isFibered
    have h₁ := Functor.IsInheritedTopology.mem_over_iff_functorPushforward hp
      (Functor.isInheritedTopology_inheritedTopology p
        (BigFppfOver.baseOverTopology B S hS .fppf)) Y T
    have h₂ := Functor.functorPushforward_mem_iff
      (J := (BigFppfOver.baseOverTopology B S hS .fppf).over (p.obj x))
      (K := BigFppfOver.topology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x))
      (G := Over.iteratedSliceForward (p.obj x))
      (S := Sieve.functorPushforward (Over.post (X := x) p) T)
    rw [show (localizationEquivalence B S hS p hp x).functor =
      Over.post (X := x) p ⋙ Over.iteratedSliceForward (p.obj x) from rfl,
      Sieve.functorPushforward_comp]
    exact h₂.trans h₁.symm

/-- The inverse of the equivalence of sites of Stacks 06WI is a dense subsite inclusion too,
which is the form `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` consumes. -/
public instance isDenseSubsite_localizationEquivalence_inverse (x : 𝒳) :
    (localizationEquivalence B S hS p hp x).inverse.IsDenseSubsite
      (BigFppfOver.topology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x))
      (localizedTopology B S hS p x) :=
  letI : (localizationEquivalence B S hS p hp x).symm.inverse.IsDenseSubsite
      (localizedTopology B S hS p x)
      (BigFppfOver.topology B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x)) :=
    isDenseSubsite_localizationEquivalence_functor B S hS p hp x
  inferInstanceAs ((localizationEquivalence B S hS p hp x).symm.functor.IsDenseSubsite _ _)

/-- **The ringed half of the equivalence `(𝒳/x, 𝒪_𝒳|) ≌ ((Sch/U)_fppf, 𝒪)`.**  The structure
sheaf of the associated fppf site of `𝒳`, restricted to `𝒳/x`, is the transport along
`AlgebraicGeometry.FibredSite.localizationEquivalence` of the structure sheaf of the big fppf
site of the scheme `x` lies over — on the nose, because the structure sheaf of `𝒳` is the
restriction along `p` of the structure sheaf of `(Sch/S)_fppf` and because
`CategoryTheory.Over.iteratedSliceForward_forget` is an equality of functors. -/
public theorem reindexRing_localizationEquivalence (x : 𝒳) :
    Stacks.SheafOfModules.reindexRing (localizedTopology B S hS p x)
        (localizationEquivalence B S hS p hp x)
        (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
          (contains_baseScheme B S hS p x)) =
      (ringStructureSheafCore B S hS p hp .fppf).over x := rfl

/-- Sheafification into abelian groups exists on the associated fppf site of an essentially
small category fibred in groupoids. -/
public theorem hasWeakSheafify_associated [EssentiallySmall.{u} 𝒳] :
    HasWeakSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u} := by
  let _ : HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  infer_instance

/-- Weak equivalences of abelian presheaves on the associated fppf site are the locally
bijective maps. -/
public theorem wEqualsLocallyBijective_associated [EssentiallySmall.{u} 𝒳] :
    (BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Sheafification into abelian groups exists on each localization of the associated fppf site
at an object. -/
public theorem hasWeakSheafify_localized [EssentiallySmall.{u} 𝒳] (x : 𝒳) :
    HasWeakSheafify (localizedTopology B S hS p x) AddCommGrpCat.{u} := by
  let _ : EssentiallySmall.{u} (Over x) := inferInstance
  let _ : HasSheafify (localizedTopology B S hS p x) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  infer_instance

/-- Weak equivalences of abelian presheaves on each localization of the associated fppf site
are the locally bijective maps. -/
public theorem wEqualsLocallyBijective_localized [EssentiallySmall.{u} 𝒳] (x : 𝒳) :
    (localizedTopology B S hS p x).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  let : EssentiallySmall.{u} (Over x) := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The equivalence of the two categories of module sheaves induced by the equivalence of
ringed sites `(𝒳/x, 𝒪_𝒳|) ≌ ((Sch/U)_fppf, 𝒪)`. -/
public noncomputable def localizationModulesEquivalence (x : 𝒳) :
    SheafOfModules.{u} (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x)) ≌
      SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x) :=
  Stacks.SheafOfModules.reindexEquivalence (localizationEquivalence B S hS p hp x)
    (BigFppfOver.structureSheaf B (baseScheme B S hS p x) (contains_baseScheme B S hS p x))

/-- **Stacks 03DM at clause (6), for the localization of Stacks 06WI**: quasi-coherence of a
module sheaf on `𝒳/x` is quasi-coherence of the corresponding module sheaf on
`(Sch/U)_fppf`. -/
public theorem isQuasicoherentOnSite_over_eq_inverseImage (x : 𝒳) :
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((ringStructureSheafCore B S hS p hp .fppf).over x) =
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
            (contains_baseScheme B S hS p x))).inverseImage
        (localizationModulesEquivalence B S hS p hp x).inverse := by
  ext M
  show M.IsQuasicoherentOnSite ↔
    ((localizationModulesEquivalence B S hS p hp x).inverse.obj M).IsQuasicoherentOnSite
  rw [← Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
    (J' := localizedTopology B S hS p x) (localizationEquivalence B S hS p hp x)
    (BigFppfOver.structureSheaf B (baseScheme B S hS p x) (contains_baseScheme B S hS p x))
    ((localizationModulesEquivalence B S hS p hp x).inverse.obj M)]
  exact ⟨fun hM => (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      ((localizationModulesEquivalence B S hS p hp x).counitIso.app M).symm hM,
    fun hM => (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      ((localizationModulesEquivalence B S hS p hp x).counitIso.app M) hM⟩

/-- **The inverse image `x^*𝓕` at an object `x`.**  A sheaf of modules on the associated fppf
site of `𝒳` restricts to `𝒳_fppf/x`, and that site with its restricted structure sheaf *is* the
big fppf site of the scheme `U = p(x)`; this is the resulting sheaf of modules on
`(Sch/U)_fppf`. -/
public noncomputable abbrev objectInverseImage (x : 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :
    SheafOfModules.{u} (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
      (contains_baseScheme B S hS p x)) :=
  (localizationModulesEquivalence B S hS p hp x).inverse.obj (M.over x)

/-- **Stacks 03DM at clause (6), read at a single module**: a sheaf of modules on `𝒳_fppf/x` is
quasi-coherent exactly when the corresponding sheaf of modules on `(Sch/U)_fppf` is. -/
public theorem isQuasicoherentOnSite_localization_iff (x : 𝒳)
    (M : SheafOfModules.{u} ((ringStructureSheafCore B S hS p hp .fppf).over x)) :
    M.IsQuasicoherentOnSite ↔
      ((localizationModulesEquivalence B S hS p hp x).inverse.obj M).IsQuasicoherentOnSite :=
  Iff.of_eq (congrFun (isQuasicoherentOnSite_over_eq_inverseImage B S hS p hp x) M)

/-- **Stacks 06WI.**  A sheaf of modules on the associated fppf site of a category fibred in
groupoids is quasi-coherent if and only if its inverse image `x^*𝓕` is a quasi-coherent sheaf on
the big fppf site `(Sch/U)_fppf` of the scheme `U = p(x)`, for every object `x` of `𝒳`.

Necessity is stability of quasi-coherence under restriction to a slice site, transported along
the equivalence of ringed sites `𝒳_fppf/x ≌ (Sch/U)_fppf`.  Sufficiency is Stacks 03DN for the
family of all objects of `𝒳`, which covers the final object: quasi-coherence is a local and
intrinsic property, so no further input is needed. -/
@[stacks 06WI]
public theorem isQuasicoherentOnSite_iff_forall_objectInverseImage
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :
    M.IsQuasicoherentOnSite ↔
      ∀ x : 𝒳, (objectInverseImage B S hS p hp x M).IsQuasicoherentOnSite := by
  refine ⟨fun hM x => (isQuasicoherentOnSite_localization_iff B S hS p hp x (M.over x)).1
    (Stacks.SheafOfModules.isQuasicoherentOnSite_over M hM x), fun h => ?_⟩
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over M fun x =>
    (isQuasicoherentOnSite_localization_iff B S hS p hp x (M.over x)).2 (h x)

/-- Closure of quasi-coherence under colimits of shape `K` on the localization `𝒳/x`, from the
same closure on the big fppf site of the scheme `x` lies over.  This is the transport along the
equivalence of ringed sites of Stacks 06WI. -/
public theorem isClosedUnderColimitsOfShape_over (x : 𝒳) (K : Type u) [Category.{u} K]
    (h : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (BigFppfOver.structureSheaf B (baseScheme B S hS p x)
        (contains_baseScheme B S hS p x))).IsClosedUnderColimitsOfShape K) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((ringStructureSheafCore B S hS p hp .fppf).over x)).IsClosedUnderColimitsOfShape K := by
  rw [isQuasicoherentOnSite_over_eq_inverseImage B S hS p hp x]
  have := h
  infer_instance

/-- Restriction of module sheaves from the associated fppf site of `𝒳` to its localization at an
object preserves colimits.  Both sites are essentially small, so both have sheafification into
abelian groups, and `CategoryTheory.Over.forget` is continuous and cocontinuous; this is
Modules on Sites, Lemma 03DC for the fibred site. -/
public theorem preservesColimitsOfShape_overFunctor [EssentiallySmall.{u} 𝒳] (x : 𝒳)
    (K : Type u) [Category.{u} K] :
    PreservesColimitsOfShape K
      (SheafOfModules.overFunctor.{u} (ringStructureSheafCore B S hS p hp .fppf) x) := by
  have := hasWeakSheafify_associated B S hS p
  have := wEqualsLocallyBijective_associated B S hS p
  have := hasWeakSheafify_localized B S hS p x
  have := wEqualsLocallyBijective_localized B S hS p x
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.pushforward.{u}
      (𝟙 ((ringStructureSheafCore B S hS p hp .fppf).over x))) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (Over.forget x) _
  exact inferInstanceAs (PreservesColimitsOfShape K (SheafOfModules.pushforward.{u}
    (𝟙 ((ringStructureSheafCore B S hS p hp .fppf).over x))))

/-- **The reduction step of Stacks 06WN, discharged.**  If quasi-coherence of module sheaves is
closed under colimits on the big fppf site of every scheme of `B`, then it is closed under
colimits on the associated fppf site of an essentially small category fibred in groupoids `𝒳`.

This is the localization argument of Stacks 06WI.  Quasi-coherence on `𝒳` may be checked on the
family of *all* objects of `𝒳`, which covers the final object
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`);
restriction to `𝒳/x` commutes with colimits (`preservesColimitsOfShape_overFunctor`); and
`𝒳/x` with its restricted structure sheaf *is* the big fppf site of the scheme `x` lies over
with its structure sheaf (`localizationEquivalence` and `reindexRing_localizationEquivalence`),
so the hypothesis applies there.  The hypothesis quantifies over every scheme of `B`, not over
`S` alone, because that is what the identification produces. -/
public theorem closedUnderColimitsOfSize_ringStructureSheafCore_of_base
    [EssentiallySmall.{u} 𝒳]
    (hbase : ∀ (T : Scheme.{u}) (hT : B.Contains T),
      SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
        (BigFppfOver.structureSheaf B T hT)) :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf) := by
  intro K _
  have hslice : ∀ x : 𝒳, ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((ringStructureSheafCore B S hS p hp .fppf).over x)).inverseImage
      (SheafOfModules.overFunctor.{u}
        (ringStructureSheafCore B S hS p hp .fppf) x)).IsClosedUnderColimitsOfShape K := by
    intro x
    have := isClosedUnderColimitsOfShape_over B S hS p hp x K
      (hbase (baseScheme B S hS p x) (contains_baseScheme B S hS p x) K)
    have := preservesColimitsOfShape_overFunctor B S hS p hp x K
    infer_instance
  refine ⟨fun M hM => ?_⟩
  show M.IsQuasicoherentOnSite
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_forall_over M fun x => ?_
  have h2 : SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf) ≤
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((ringStructureSheafCore B S hS p hp .fppf).over x)).inverseImage
        (SheafOfModules.overFunctor.{u}
          (ringStructureSheafCore B S hS p hp .fppf) x) :=
    fun N hN => Stacks.SheafOfModules.isQuasicoherentOnSite_over N hN x
  have := hslice x
  exact ObjectProperty.colimitsOfShape_le _ K M
    (ObjectProperty.colimitsOfShape_monotone K h2 M hM)

end AlgebraicGeometry.FibredSite

end
