module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.StackOfFppfTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorComparisonFibred
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.MorSheafFromIsom

/-!
# The comparison functor of Stacks 04UT is an equivalence of stacks

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over `B`,
with `𝒢` and `ℬ` the sheaves on the big fppf site of `S` that `G` and `B` define. Stacks 04UT
asserts that the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors`, which sends `(U, b, X)` to
`(U, b, 𝒳)` with `𝒳` the total space seen as a sheaf, is an equivalence of stacks in groupoids
over `(Sch/S)_fppf`. This file proves hypothesis (2) of Stacks 046N for the comparison functor,
and shows that the comparison functor is an equivalence exactly when every `𝒢/ℬ`-torsor sheaf
has an algebraic space as total space.

## Main definitions

* `AlgebraicGeometry.Space.FppfTorsors.ofSection`: a torsor of sheaves with a global section over
  its base, viewed as a torsor of algebraic spaces.
* `AlgebraicGeometry.Space.FppfTorsors.ofAlgebraicSpace`: a torsor of sheaves whose total space
  is an algebraic space, viewed as a torsor of algebraic spaces.
* `AlgebraicGeometry.Space.FppfTorsors.isEquivalenceOverComparison`: granted effectivity of
  descent for `G-Torsors`, the comparison functor is an equivalence of stacks in groupoids over
  the big fppf site of `S`.
* `AlgebraicGeometry.Space.FppfTorsors.isEquivalenceOverComparisonOfAlgebraic`: the same
  equivalence, granted that every `𝒢/ℬ`-torsor sheaf has an algebraic space as total space.

## Main results

* `AlgebraicGeometry.Space.FppfTorsors.isAlgebraicSpace_total_of_section`: the total space of a
  torsor of sheaves with a global section over its base is an algebraic space.
* `AlgebraicGeometry.Space.FppfTorsors.locallyEssSurjOnFibers_comparison`: hypothesis (2) of
  Stacks 046N for the comparison functor.
* `AlgebraicGeometry.Space.FppfTorsors.nonempty_isEquivalenceOver_comparison_of_isStack`: if
  both projections are stacks, then the comparison functor is an equivalence over the site.
* `AlgebraicGeometry.Space.FppfTorsors.exists_isFppfCovering_sections`: every torsor of sheaves
  is trivialized by an fppf covering of its base.
* `AlgebraicGeometry.Space.FppfTorsors.isAlgebraicSpace_total_of_isEquivalenceOver`: if the
  comparison functor is an equivalence over the site, then every `𝒢/ℬ`-torsor sheaf has an
  algebraic space as total space.
* `AlgebraicGeometry.Space.FppfTorsors.isAlgebraicSpace_total_of_hasEffectiveDescent`: if
  descent for `G-Torsors` is effective, then every `𝒢/ℬ`-torsor sheaf has an algebraic space as
  total space.
* `FppfTorsors.nonempty_isEquivalenceOver_comparison_iff_isAlgebraicSpace_total`: the comparison
  functor is an equivalence over the site if and only if every `𝒢/ℬ`-torsor sheaf has an
  algebraic space as total space.

## References

* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 0499](https://stacks.math.columbia.edu/tag/0499)
* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
* [Stacks Project, Tag 04US](https://stacks.math.columbia.edu/tag/04US)
* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB}

namespace FppfTorsors

/-! ### A torsor of sheaves with a global section is a torsor of algebraic spaces -/

/-- The total space of a torsor of sheaves under `U ×_{b, ℬ} 𝒢` which has a global section over
its base is an algebraic space. -/
theorem isAlgebraicSpace_total_of_section (T : SheafTorsors G.obj)
    (s : 𝟙_ (Over (yoneda.obj T.base)) ⟶ T.total) :
    IsAlgebraicSpace 𝒞 S hS T.total.left := by
  obtain ⟨e⟩ :=
    (AlgebraicGeometry.isTrivial_iff_exists_globalSection T.group T.total T.isPseudoTorsor).mpr
      ⟨s⟩
  exact isAlgebraicSpace_of_iso 𝒞 S hS
    ((Over.forget _).mapIso ((Mod.forget T.group).mapIso e))
    (fppfPullbackGroup hB G T.base T.sec).property

/-- A torsor of sheaves under `U ×_{b, ℬ} 𝒢` which has a global section over its base, viewed as
an object of `G-Torsors`, with the same base, section of `ℬ`, total space and action, trivialized
by the identity covering of its base. -/
def ofSection (T : SheafTorsors G.obj) (s : 𝟙_ (Over (yoneda.obj T.base)) ⟶ T.total) :
    FppfTorsors hB G where
  base := T.base
  sec := T.sec
  total := T.total
  isAlgebraicSpace := isAlgebraicSpace_total_of_section (hB := hB) (G := G) T s
  action := T.action
  isTorsor :=
    ⟨T.isPseudoTorsor, PUnit.{u + 2}, fun _ => yoneda.obj T.base, fun _ => 𝟙 (yoneda.obj T.base),
      fun _ => isAlgebraicSpace_yoneda 𝒞 S hS T.base,
      isFppfCovering_of_isIso 𝒞 S hS (yoneda.obj T.base) (yoneda.obj T.base)
        (𝟙 (yoneda.obj T.base)) (isAlgebraicSpace_yoneda 𝒞 S hS T.base),
      fun _ => ⟨s ≫ (Over.pullbackId (X := yoneda.obj T.base)).inv.app T.total⟩⟩

/-- The comparison functor sends `ofSection T s` to `T`. -/
@[simp]
theorem comparison_obj_ofSection (T : SheafTorsors G.obj)
    (s : 𝟙_ (Over (yoneda.obj T.base)) ⟶ T.total) :
    (comparison hB G).obj (ofSection (hB := hB) (G := G) T s) = T :=
  rfl

/-! ### Hypothesis (2) of Stacks 046N -/

set_option synthInstance.maxHeartbeats 200000 in
/-- Hypothesis (2) of Stacks 046N for the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors`: every
object of every fibre of `𝒢/ℬ-Torsors` is, locally on its base, in the essential image of the
comparison functor on fibres. -/
theorem locallyEssSurjOnFibers_comparison (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    Functor.LocallyEssSurjOnFibers
      (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
      (comparison_comp_projection hB G) (BigFppfOver.topology 𝒞 S hS) := by
  have hq : (SheafTorsors.projection G.obj).IsFibered :=
    (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
  intro U x
  obtain ⟨T, hT⟩ := x
  have hTb : T.base = U := hT
  refine ⟨Presheaf.imageSieve T.total.hom (eqToHom hTb.symm),
    T.isLocallySurjective.imageSieve_mem (J := BigFppfOver.topology 𝒞 S hS) _, ?_⟩
  intro V f hf
  obtain ⟨t, ht⟩ := hf
  have hsx : yonedaEquiv.symm t ≫ T.total.hom = yoneda.map (f ≫ eqToHom hTb.symm) := by
    apply yonedaEquiv.injective
    have hrhs : yonedaEquiv (yoneda.map (f ≫ eqToHom hTb.symm)) = f ≫ eqToHom hTb.symm :=
      yonedaEquiv_yoneda_map _
    rw [hrhs, yonedaEquiv_comp, Equiv.apply_symm_apply, ht]
    simp
  set Rpt := Functor.IsPreFibered.pullbackObj hT f with hRptDef
  have hRb : Rpt.base = V := Functor.IsPreFibered.pullbackObj_proj hT f
  set φ : Rpt ⟶ T := Functor.IsPreFibered.pullbackMap hT f with hφ
  have hbase : SheafTorsors.Hom.base φ = eqToHom hRb ≫ f ≫ eqToHom hTb.symm :=
    IsHomLift.fac' (SheafTorsors.projection G.obj) f φ
  have hsx' : (yoneda.map (eqToHom hRb) ≫ yonedaEquiv.symm t) ≫ T.total.hom =
      𝟙 (yoneda.obj Rpt.base) ≫ yoneda.map (SheafTorsors.Hom.base φ) := by
    rw [Category.assoc, hsx, ← Functor.map_comp, hbase, Category.id_comp]
  set sec : yoneda.obj Rpt.base ⟶ Rpt.total.left :=
    (SheafTorsors.Hom.isPullback φ).lift (yoneda.map (eqToHom hRb) ≫ yonedaEquiv.symm t)
      (𝟙 (yoneda.obj Rpt.base)) hsx' with hsecDef
  have hw : sec ≫ Rpt.total.hom = 𝟙 (yoneda.obj Rpt.base) :=
    (SheafTorsors.Hom.isPullback φ).lift_snd _ _ hsx'
  refine ⟨⟨ofSection (hB := hB) (G := G) Rpt (Over.homMk sec (by simpa using hw)), hRb⟩, ?_⟩
  exact ⟨Functor.Fiber.isoMk (Iso.refl Rpt) (IsHomLift.id hRb)⟩

/-! ### The equivalence of stacks -/

/-- If descent for `G-Torsors` is effective (`hdesc`), then every torsor of sheaves is
vertically isomorphic to the image of a torsor of algebraic spaces under the comparison
functor. -/
theorem hasVerticalPreimages_comparison (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (hdesc : letI : (projection hB G).IsFibered :=
        (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
      Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS)) :
    Functor.HasVerticalPreimages (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G) := by
  let : (projection hB G).IsFibered :=
    (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
  let : (SheafTorsors.projection G.obj).IsFibered :=
    (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
  have hmor : ∀ (U : BigFppfOver 𝒞 S hS) (x y : (SheafTorsors.projection G.obj).Fiber U),
      Functor.IsMorSheaf (SheafTorsors.projection G.obj) (BigFppfOver.topology 𝒞 S hS) U x y :=
    Functor.isMorSheaf_of_isomIsSheaf (SheafTorsors.projection_isFiberedInGroupoids G.obj)
      (SheafTorsors.projection_isomIsSheaf G.obj hB.isSheaf)
  refine Functor.exists_vertical_iso_of_fiber_essSurj (comparison_comp_projection hB G) ?_
  intro U
  refine ⟨fun x => ?_⟩
  obtain ⟨R, hR, hRess⟩ := locallyEssSurjOnFibers_comparison hB G U x
  exact Functor.exists_iso_of_locally_essImage (isFibredOneMorphism_comparison hB G) hdesc
    (hmor U) x hR hRess

/-- If every descent datum of fppf torsors of algebraic spaces along a covering sieve of the big
fppf site of `S` is effective (`hdesc`, condition (3) of Stacks 02ZI for
`p : G-Torsors ⥤ (Sch/S)_fppf`), then the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors`, which
sends a triple `(U, b, X)` to the triple `(U, b, 𝒳)` with `𝒳` the total space seen as a sheaf, is
an equivalence of stacks in groupoids over the big fppf site of `S`: it has a quasi-inverse which
is again a functor over the site, with vertical unit and counit. -/
@[stacks 04UT "the hypothesis-carrying form, taking hdesc — effectivity of descent for \
G-Torsors, condition (3) of Stacks 02ZI in Stacks 04US. That hypothesis is PROVED, as \
`FppfTorsors.hasEffectiveDescent_projection`, and the form carrying nothing is \
`FppfTorsors.nonempty_isEquivalenceOver_comparison`"]
noncomputable def isEquivalenceOverComparison (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (hdesc : letI : (projection hB G).IsFibered :=
        (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
      Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS)) :
    Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G) :=
  Functor.isEquivalenceOver_of_exists_vertical_iso (comparison_comp_projection hB G)
    (hasVerticalPreimages_comparison hB G hdesc)

/-- If both `p : G-Torsors ⥤ (Sch/S)_fppf` and `p : 𝒢/ℬ-Torsors ⥤ (Sch/S)_fppf` are stacks over
the big fppf site of `S` (Stacks 04US and Stacks 04UM), then the comparison functor is an
equivalence over that site. -/
@[stacks 04UT "the hypothesis-carrying form of the criterion Stacks 046N, taking the two stack \
conditions Stacks 04US and Stacks 04UM as hsource and htarget. BOTH are proved — \
`FppfTorsors.projection_isStack` and `SheafTorsors.projection_isStackInGroupoids` — and the form \
carrying nothing is `FppfTorsors.nonempty_isEquivalenceOver_comparison`"]
theorem nonempty_isEquivalenceOver_comparison_of_isStack (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (hsource : (projection hB G).IsStack (BigFppfOver.topology 𝒞 S hS))
    (htarget : (SheafTorsors.projection G.obj).IsStack (BigFppfOver.topology 𝒞 S hS)) :
    Nonempty (Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G)) :=
  (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers hsource htarget
      (isFibredOneMorphism_comparison hB G)).mpr
    (locallyEssSurjOnFibers_comparison hB G)

/-! ### Algebraicity of the total spaces -/

/-- Every torsor of sheaves is trivialized by an fppf covering of its base by algebraic
spaces. -/
theorem exists_isFppfCovering_sections (T : SheafTorsors G.obj) :
    ∃ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
      (f : ∀ i, Bᵢ i ⟶ yoneda.obj T.base),
      (∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) ∧ IsFppfCovering 𝒞 S hS Bᵢ f ∧
        ∀ i, Nonempty (𝟙_ (Over (Bᵢ i)) ⟶ (Over.pullback (f i)).obj T.total) := by
  have hR : Presheaf.imageSieve T.total.hom (𝟙 T.base) ∈
      BigFppfOver.topology 𝒞 S hS T.base :=
    T.isLocallySurjective.imageSieve_mem (J := BigFppfOver.topology 𝒞 S hS) _
  obtain ⟨E, hE, hle⟩ :=
    exists_covering_refining_sieve 𝒞 ((GrothendieckTopology.mem_over_iff _ _).1 hR)
  refine ⟨E.I₀, fun i => yoneda.obj (Over.mk (E.f i ≫ T.base.hom) : BigFppfOver 𝒞 S hS),
    fun i => yoneda.map (Over.homMk (E.f i) :
      (Over.mk (E.f i ≫ T.base.hom) : BigFppfOver 𝒞 S hS) ⟶ T.base),
    fun _ => isAlgebraicSpace_yoneda 𝒞 S hS _,
    isFppfCovering_yonedaMap_of_isCovering 𝒞 S hS T.base E hE, fun i => ?_⟩
  obtain ⟨t, ht⟩ :=
    (Sieve.overEquiv_iff (Presheaf.imageSieve T.total.hom (𝟙 T.base)) (E.f i)).1 (hle _ _ ⟨i⟩)
  rw [nonempty_unitHom_pullback_iff]
  refine ⟨yonedaEquiv.symm t, ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ht, yonedaEquiv_yoneda_map]
  simp

/-- A torsor of sheaves whose total space is an algebraic space, viewed as an object of
`G-Torsors`, with the same base, section of `ℬ`, total space and action. -/
def ofAlgebraicSpace (T : SheafTorsors G.obj)
    (hX : IsAlgebraicSpace 𝒞 S hS T.total.left) : FppfTorsors hB G where
  base := T.base
  sec := T.sec
  total := T.total
  isAlgebraicSpace := hX
  action := T.action
  isTorsor := ⟨T.isPseudoTorsor, exists_isFppfCovering_sections (hB := hB) (G := G) T⟩

/-- The comparison functor sends `ofAlgebraicSpace T hX` to `T`. -/
@[simp]
theorem comparison_obj_ofAlgebraicSpace (T : SheafTorsors G.obj)
    (hX : IsAlgebraicSpace 𝒞 S hS T.total.left) :
    (comparison hB G).obj (ofAlgebraicSpace (hB := hB) (G := G) T hX) = T :=
  rfl

/-- If every torsor of sheaves has an algebraic space as total space then the comparison
functor is essentially surjective on every fibre. -/
theorem fiber_essSurj_comparison
    (halg : ∀ T : SheafTorsors G.obj, IsAlgebraicSpace 𝒞 S hS T.total.left)
    (U : BigFppfOver 𝒞 S hS) :
    (Functor.Fiber.mapOfComp (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G) (comparison_comp_projection hB G) U).EssSurj := by
  refine ⟨fun x => ?_⟩
  obtain ⟨T, hT⟩ := x
  exact ⟨⟨ofAlgebraicSpace (hB := hB) (G := G) T (halg T), hT⟩,
    ⟨Functor.Fiber.isoMk (Iso.refl T) (IsHomLift.id hT)⟩⟩

/-- The comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` is an equivalence of stacks in groupoids
over the big fppf site of `S` as soon as every torsor of sheaves has an algebraic space as total
space. -/
@[stacks 04UT "the hypothesis-carrying form, taking halg — algebraicity of the total space of \
every 𝒢/ℬ-torsor sheaf, which `isAlgebraicSpace_total_of_isEquivalenceOver` shows the tag's \
conclusion in turn implies, so the two are equivalent. halg is PROVED, via \
`isBootstrapAlgebraicSpaceAlongFlatSurjection`, and the form carrying nothing is \
`FppfTorsors.nonempty_isEquivalenceOver_comparison`"]
noncomputable def isEquivalenceOverComparisonOfAlgebraic
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (halg : ∀ T : SheafTorsors G.obj, IsAlgebraicSpace 𝒞 S hS T.total.left) :
    Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G) :=
  letI : (projection hB G).IsFibered :=
    (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
  letI : (SheafTorsors.projection G.obj).IsFibered :=
    (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
  Functor.isEquivalenceOver_of_exists_vertical_iso (comparison_comp_projection hB G)
    (Functor.exists_vertical_iso_of_fiber_essSurj (comparison_comp_projection hB G)
      (fiber_essSurj_comparison (hB := hB) (G := G) halg))

/-- The isomorphism of total spaces underlying an isomorphism of `𝒢/ℬ-Torsors`. -/
def totalIsoOfIso {T T' : SheafTorsors G.obj} (e : T ≅ T') : T.total.left ≅ T'.total.left where
  hom := SheafTorsors.Hom.map e.hom
  inv := SheafTorsors.Hom.map e.inv
  hom_inv_id := congrArg SheafTorsors.Hom.map e.hom_inv_id
  inv_hom_id := congrArg SheafTorsors.Hom.map e.inv_hom_id

/-- If the comparison functor is an equivalence over the big fppf site of `S` then every
torsor of sheaves has an algebraic space as total space. -/
theorem isAlgebraicSpace_total_of_isEquivalenceOver
    (E : Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G)) (T : SheafTorsors G.obj) :
    IsAlgebraicSpace 𝒞 S hS T.total.left := by
  obtain ⟨X, ⟨e⟩⟩ := (Functor.fiber_essSurj_of_isEquivalenceOver
      (comparison_comp_projection hB G) E T.base).mem_essImage
    (⟨T, rfl⟩ : (SheafTorsors.projection G.obj).Fiber T.base)
  exact isAlgebraicSpace_of_iso 𝒞 S hS
    (totalIsoOfIso (hB := hB) (G := G) (Functor.Fiber.fiberInclusion.mapIso e))
    X.1.isAlgebraicSpace

/-- If every descent datum of fppf torsors of algebraic spaces along a covering sieve of the big
fppf site of `S` is effective, then every torsor of sheaves has an algebraic space as total
space. -/
theorem isAlgebraicSpace_total_of_hasEffectiveDescent (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (hdesc : letI : (projection hB G).IsFibered :=
        (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
      Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS))
    (T : SheafTorsors G.obj) :
    IsAlgebraicSpace 𝒞 S hS T.total.left :=
  isAlgebraicSpace_total_of_isEquivalenceOver (hB := hB) (G := G)
    (isEquivalenceOverComparison hB G hdesc) T

/-- The comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` is an equivalence of stacks in groupoids
over the big fppf site of `S` if and only if every `𝒢/ℬ`-torsor sheaf has an algebraic space as
total space. -/
@[stacks 04UT "the equivalence holds exactly when every 𝒢/ℬ-torsor sheaf has an algebraic \
space as total space; the tag asserts the left-hand side, which this does not prove \
unconditionally"]
theorem nonempty_isEquivalenceOver_comparison_iff_isAlgebraicSpace_total
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB) :
    Nonempty (Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
        (comparison hB G)) ↔
      ∀ T : SheafTorsors G.obj, IsAlgebraicSpace 𝒞 S hS T.total.left :=
  ⟨fun ⟨E⟩ => isAlgebraicSpace_total_of_isEquivalenceOver (hB := hB) (G := G) E,
    fun halg => ⟨isEquivalenceOverComparisonOfAlgebraic hB G halg⟩⟩

end FppfTorsors

end AlgebraicGeometry.Space

end
