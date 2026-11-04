module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.EquationsBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportCounitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsDerivedPullback

/-!
# The derived base-change diagram of a family of global equations

Let `g : X' ⟶ X` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, put
`f'ᵢ = g^♯(fᵢ)`, let `Z ⊆ X` be the common zero locus of the `fᵢ` and let `Z' = g^{-1}(Z)`.
For an `𝒪_X`-module `ℱ` write `ℱ' = g^*ℱ` and let `ℱ^•`, resp. `(ℱ')^•`, be the extended
alternating Čech complex of [Stacks, Tag 0G7I] of `ℱ, f₁, …, f_c`, resp. `ℱ', f'₁, …, f'_c`.

This file proves that the derived diagram of [Stacks, Tag 0G7U],

```
i'_* L(g|_{Z'})^* R𝓗_Z(ℱ) ------> i'_* R𝓗_{Z'}(Lg^*ℱ)
        ‖                                 |
Lg^* i_* R𝓗_Z(ℱ)                   i'_* R𝓗_{Z'}(ℱ')
        ^                                 ^
        |                                 |
Lg^*(ℱ^•) ---------------------------> (ℱ')^•
```

commutes.  The top horizontal arrow and the identification on the left are
[Stacks, Tag 0G78]; the two arrows pointing up are the comparison of [Stacks, Tag 0G7L]; the
lower horizontal arrow is `Lg^*ℱ^• ⟶ g^*ℱ^• ⟶ (ℱ')^•`, the canonical derived-to-underived
comparison followed by the termwise comparison of the two Čech complexes; and the arrow
pointing down is induced by `Lg^*ℱ ⟶ g^*ℱ = ℱ'`.  The commutativity is proved for an
*arbitrary* lower horizontal arrow and an arbitrary down arrow compatible with the two
augmentations of [Stacks, Tag 0G7L], which is all the source's argument uses.

## Main results

* `Stacks.Perfect.SupportedDerivedBaseChange.hom_ext_of_comp_supportPushCounit`: **two maps into
  `i_* R𝓗_T(K)` out of a complex supported on `T` that have the same composite with the
  canonical map `i_* R𝓗_T(K) ⟶ K` of [Stacks, Tag 0G72] are equal.**  This is the cancellation
  the source's proof performs when it says that going around the diagram both ways gives two
  arrows whose composition with `i'_*R𝓗_{Z'}(ℱ') ⟶ ℱ'` is the canonical map.
* `Stacks.Perfect.SupportedDerivedBaseChange.isIso_supportPush_map_supportPushCounit_app`: the
  invertibility that cancellation rests on.
* `Stacks.Perfect.SupportedDerivedBaseChange.supportedPullbackRoute`: the upper route of the
  remark's diagram — its left-hand equal sign followed by its top horizontal arrow — and
  `supportedPullbackRoute_comp_counit`: **the upper route followed by the canonical map
  `i'_* R𝓗_{Z'}(Lp^*K) ⟶ Lp^*K` of [Stacks, Tag 0G72] is `Lp^*` of the canonical map
  `i_* R𝓗_Z(K) ⟶ K`.**  This is the half of the remark's diagram that does not involve the Čech
  complex, and it is the commutative triangle of [Stacks, Tag 0G78].
* `Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback`: the set-theoretic form
  of the assertion `Z' = Z ×_X X'` that opens the setting of [Stacks, Tag 0G7U] — the common zero
  locus of the pulled-back equations is the preimage of the common zero locus of the equations,
  which is the shape [Stacks, Tag 0G78] is stated at.
* `Stacks.Perfect.SupportedDerivedBaseChange.cohomologySupportedOn_derivedPullback_cplx`:
  `Lg^*(ℱ^•)` is supported on `Z'`, which is what makes the cancellation applicable at the
  source of the remark's diagram, and
  `hom_ext_of_comp_supportPushCounit_cplx`: the cancellation there.
* `Stacks.Perfect.SupportedDerivedBaseChange.equationsClosedSet_pullback_subset`: the common zero
  locus of the pulled-back equations is contained in `Z' = g^{-1}(Z)`, the hypothesis the
  comparison of [Stacks, Tag 0G7L] for `ℱ', f'₁, …, f'_c` is stated at.
* `Stacks.Perfect.SupportedDerivedBaseChange.derivedBaseChangeSquare`: **the derived diagram of
  [Stacks, Tag 0G7U] commutes**, for an arbitrary lower horizontal arrow `θ` and an arbitrary
  down arrow `δ` compatible with the augmentations of [Stacks, Tag 0G7L].

## Implementation notes

**The cancellation.** Let `L = i_*^D`, `R = R𝓗_T`, so that `i_* R𝓗_T = R ⋙ L` and the canonical
map of [Stacks, Tag 0G72] is the counit of the adjunction `L ⊣ R` of [Stacks, Tag 0A3B], by
`Stacks.Perfect.SupportCounitComparison`'s
`derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit`.
The counit is invertible at every complex supported on `T`
(`isIso_derivedSupportedSectionsToId_app_of_supported`), in particular at the source `A` and at
`L(R K)`, the latter being supported by `cohomologySupportedOn_derivedSupportedPushforward`.
Invertibility at `L(R K)` turns the left triangle identity into the invertibility of
`L(unit_{R K})`, and then `L` of the right triangle identity exhibits `(R ⋙ L)(counit_K)` as its
inverse, so that too is invertible; hence `α ↦ (R ⋙ L)(α)` is determined by `α ↦ α ≫ counit_K`,
and `α` is recovered from `(R ⋙ L)(α)` by naturality of the counit at `α` together with
invertibility at `A`.  No full faithfulness of `L` is needed.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0A3B](https://stacks.math.columbia.edu/tag/0A3B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation (augmentation)
open Stacks.Perfect.SupportedFraction (supportPush supportPushCounit cohomologySupportedOn_cech
  cechToDerivedSupport cechToDerivedSupport_comp_derivedSupportedSectionsToId)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  isIso_derivedSupportedSectionsToId_app_of_supported
  cohomologySupportedOn_derivedSupportedPushforward)
open Stacks.Perfect.SupportCounitComparison
  (derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedDerivedBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Cancelling the canonical map out of `i_* R𝓗_T` -/

section Cancellation

variable {X : Scheme.{u}} {T : Set X} (hT : IsClosed T)

/-- The canonical map `i_* R𝓗_T ⟶ 𝟭` of [Stacks, Tag 0G72] is the counit of [Stacks, Tag 0A3B]. -/
private theorem supportPushCounit_eq_counit :
    letI := pushforward_preservesFiniteLimits X.toRingedSpace T
    letI := pushforward_preservesFiniteColimits X.toRingedSpace T hT
    supportPushCounit hT = (derivedPushforwardAdjunction X.toRingedSpace T hT).counit :=
  derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit X.toRingedSpace T hT

/-- **`i_* R𝓗_T` applied to the canonical map `i_* R𝓗_T(K) ⟶ K` is invertible.**

Write `L = i_*^D` and `R = R𝓗_T`, so `i_* R𝓗_T = R ⋙ L` and the canonical map of
[Stacks, Tag 0G72] is the counit of the adjunction `L ⊣ R` of [Stacks, Tag 0A3B].  The counit is
invertible at `L(R K)`, which is supported on `T`; the left triangle identity at `R K` then says
that `L(unit_{R K})` is its inverse, hence invertible; and `L` of the right triangle identity at
`K` exhibits `(R ⋙ L)(counit_K)` as the inverse of `L(unit_{R K})`. -/
public theorem isIso_supportPush_map_supportPushCounit_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso ((supportPush hT).map ((supportPushCounit hT).app K)) := by
  let := pushforward_preservesFiniteLimits X.toRingedSpace T
  let := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  set L := (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory
    with hL
  set R := derivedSupportedSectionsOnClosed X.toRingedSpace T hT with hR
  set adj := derivedPushforwardAdjunction X.toRingedSpace T hT with hadj
  have hcounit : supportPushCounit hT = adj.counit := supportPushCounit_eq_counit hT
  have hLRK : IsIso (adj.counit.app (L.obj (R.obj K))) := by
    rw [← hcounit]
    exact isIso_derivedSupportedSectionsToId_app_of_supported X.toRingedSpace T hT _
      (cohomologySupportedOn_derivedSupportedPushforward X T hT K)
  have hunit : IsIso (L.map (adj.unit.app (R.obj K))) := by
    rw [show L.map (adj.unit.app (R.obj K)) =
        CategoryTheory.inv (adj.counit.app (L.obj (R.obj K))) from
      IsIso.eq_inv_of_inv_hom_id (adj.left_triangle_components (R.obj K))]
    infer_instance
  have htri : adj.unit.app (R.obj K) ≫ R.map (adj.counit.app K) = 𝟙 (R.obj K) :=
    adj.right_triangle_components K
  have hmc : L.map (adj.unit.app (R.obj K) ≫ R.map (adj.counit.app K)) =
      L.map (adj.unit.app (R.obj K)) ≫ L.map (R.map (adj.counit.app K)) :=
    L.map_comp _ _
  have hcomp : L.map (adj.unit.app (R.obj K)) ≫ L.map (R.map (adj.counit.app K)) =
      𝟙 (L.obj (R.obj K)) := by
    rw [← hmc, htri]
    exact L.map_id _
  have hfin : IsIso (L.map (R.map (adj.counit.app K))) := by
    rw [show L.map (R.map (adj.counit.app K)) =
        CategoryTheory.inv (L.map (adj.unit.app (R.obj K))) from
      IsIso.eq_inv_of_hom_inv_id hcomp]
    infer_instance
  rw [hcounit]
  exact hfin

/-- **Two maps into `i_* R𝓗_T(K)` out of a complex supported on `T` with the same composite with
the canonical map `i_* R𝓗_T(K) ⟶ K` of [Stacks, Tag 0G72] are equal.**

Naturality of the canonical map at `α` reads
`counit_A ≫ α = (i_* R𝓗_T)(α) ≫ counit_{i_* R𝓗_T(K)}`, and `counit_A` is invertible because `A`
is supported on `T`; so `α` is determined by `(i_* R𝓗_T)(α)`, which is in turn determined by
`α ≫ counit_K` because `(i_* R𝓗_T)(counit_K)` is invertible. -/
public theorem hom_ext_of_comp_supportPushCounit
    {A K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))}
    (hA : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) T A)
    {α β : A ⟶ (supportPush hT).obj K}
    (h : α ≫ (supportPushCounit hT).app K = β ≫ (supportPushCounit hT).app K) : α = β := by
  have hA' : IsIso ((supportPushCounit hT).app A) :=
    isIso_derivedSupportedSectionsToId_app_of_supported X.toRingedSpace T hT A hA
  have hiso := isIso_supportPush_map_supportPushCounit_app hT K
  have hmap : (supportPush hT).map α = (supportPush hT).map β := by
    have hc : (supportPush hT).map α ≫ (supportPush hT).map ((supportPushCounit hT).app K) =
        (supportPush hT).map β ≫ (supportPush hT).map ((supportPushCounit hT).app K) := by
      rw [← Functor.map_comp, ← Functor.map_comp, h]
    exact (cancel_mono _).mp hc
  have hnat : ∀ γ : A ⟶ (supportPush hT).obj K,
      (supportPush hT).map γ ≫ (supportPushCounit hT).app ((supportPush hT).obj K) =
        (supportPushCounit hT).app A ≫ γ :=
    fun γ => (supportPushCounit hT).naturality γ
  have hcancel : (supportPushCounit hT).app A ≫ α = (supportPushCounit hT).app A ≫ β := by
    rw [← hnat α, ← hnat β, hmap]
  exact (cancel_epi ((supportPushCounit hT).app A)).mp hcancel

end Cancellation

/-! ### The top horizontal arrow and the identification on the left -/

section TopRoute

variable {Y Y' : RingedSpace.{u, u}} (p : Y' ⟶ Y) (Z : Set Y.carrier) (hZ : IsClosed Z)

/-- **The composite `Lp^* i_* R𝓗_Z(K) ⟶ i'_* R𝓗_{Z'}(Lp^*K)` made of the identification on the
left of the diagram of [Stacks, Tag 0G7U] and its top horizontal arrow.**

Reading the factors in order: the comparison of [Stacks, Tag 0E2K] passes from the functor
induced by the exact `i_*` to the total right derived `Ri_*`; the base-change transformation of
[Stacks, Tag 08HY], which [Stacks, Tag 0G78] shows to be invertible here, is the remark's equal
sign `Lp^* i_* R𝓗_Z(K) = i'_* L(p|_{Z'})^* R𝓗_Z(K)`; the comparison comes back; and the top
horizontal arrow is `i'_*` of the canonical map of [Stacks, Tag 0G78]. -/
public def supportedPullbackRoute
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    letI := pushforward_preservesFiniteLimits Y Z
    letI := pushforward_preservesFiniteColimits Y Z hZ
    letI := pushforward_preservesFiniteLimits Y' (closedSubsetPreimage p Z)
    letI := pushforward_preservesFiniteColimits Y' (closedSubsetPreimage p Z)
      (isClosed_closedSubsetPreimage p Z hZ)
    (derivedPullback p).obj ((derivedSupportedPushforward Y Z hZ).obj K) ⟶
      (derivedSupportedPushforward Y' (closedSubsetPreimage p Z)
          (isClosed_closedSubsetPreimage p Z hZ)).obj ((derivedPullback p).obj K) :=
  letI := pushforward_preservesFiniteLimits Y Z
  letI := pushforward_preservesFiniteColimits Y Z hZ
  letI := pushforward_preservesFiniteLimits Y' (closedSubsetPreimage p Z)
  letI := pushforward_preservesFiniteColimits Y' (closedSubsetPreimage p Z)
    (isClosed_closedSubsetPreimage p Z hZ)
  (derivedPullback p).map ((closedPushforwardComparison Y Z).hom.app _) ≫
    supportedPullbackBaseChangeMap p Z _ ≫
    (closedPushforwardComparison Y' (closedSubsetPreimage p Z)).inv.app _ ≫
    (modulePushforward (closedSubsetInclusion Y'
        (closedSubsetPreimage p Z))).mapDerivedCategory.map
      (supportedPullbackMap p Z hZ (isClosed_closedSubsetPreimage p Z hZ) K)

/-- **The top route is compatible with the canonical maps of [Stacks, Tag 0G72].**  Composing it
with `i'_* R𝓗_{Z'}(Lp^*K) ⟶ Lp^*K` gives `Lp^*` of `i_* R𝓗_Z(K) ⟶ K`.

This is the commutative triangle of [Stacks, Tag 0G78] (`supportedPullbackMap_triangle`) with the
comparison of [Stacks, Tag 0E2K] prefixed, so that the two occurrences of that comparison on the
left cancel.  It is the half of the remark's diagram that does not involve the Čech complex: the
upper route, followed by the canonical map of [Stacks, Tag 0G72], is `Lp^*` of that canonical
map. -/
public theorem supportedPullbackRoute_comp_counit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    letI := pushforward_preservesFiniteLimits Y Z
    letI := pushforward_preservesFiniteColimits Y Z hZ
    letI := pushforward_preservesFiniteLimits Y' (closedSubsetPreimage p Z)
    letI := pushforward_preservesFiniteColimits Y' (closedSubsetPreimage p Z)
      (isClosed_closedSubsetPreimage p Z hZ)
    supportedPullbackRoute p Z hZ K ≫
        (derivedPushforwardAdjunction Y' (closedSubsetPreimage p Z)
            (isClosed_closedSubsetPreimage p Z hZ)).counit.app ((derivedPullback p).obj K) =
      (derivedPullback p).map ((derivedPushforwardAdjunction Y Z hZ).counit.app K) := by
  let := pushforward_preservesFiniteLimits Y Z
  let := pushforward_preservesFiniteColimits Y Z hZ
  let := pushforward_preservesFiniteLimits Y' (closedSubsetPreimage p Z)
  let := pushforward_preservesFiniteColimits Y' (closedSubsetPreimage p Z)
    (isClosed_closedSubsetPreimage p Z hZ)
  have assoc5 : ∀ {V₀ V₁ V₂ V₃ V₄ V₅ :
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y'))}
      (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (u : V₂ ⟶ V₃) (d : V₃ ⟶ V₄) (e : V₄ ⟶ V₅),
      (a ≫ b ≫ u ≫ d) ≫ e = a ≫ b ≫ u ≫ d ≫ e := by
    intro V₀ V₁ V₂ V₃ V₄ V₅ a b u d e
    rw [Category.assoc, Category.assoc, Category.assoc]
  have map3 : ∀ {W₀ W₁ W₂ W₃ :
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
      (x : W₀ ⟶ W₁) (y : W₁ ⟶ W₂) (z : W₂ ⟶ W₃),
      (derivedPullback p).map x ≫ (derivedPullback p).map y ≫ (derivedPullback p).map z =
        (derivedPullback p).map (x ≫ y ≫ z) := by
    intro W₀ W₁ W₂ W₃ x y z
    rw [← Functor.map_comp, ← Functor.map_comp]
  have key := supportedPullbackMap_triangle p Z hZ (isClosed_closedSubsetPreimage p Z hZ) K
  refine ((assoc5 _ _ _ _ _).trans (whisker_eq _ key)).trans ?_
  refine (map3 _ _ _).trans (congrArg (fun t => (derivedPullback p).map t) ?_)
  exact Iso.hom_inv_id_app_assoc _ _ _

end TopRoute

/-! ### The setting: the common zero locus of the pulled-back equations is the preimage -/

section Setting

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-- **The common zero locus of the pulled-back equations is the preimage of the common zero
locus of the equations.**  This is the set-theoretic form of the assertion `Z' = Z ×_X X'` that
opens the setting of [Stacks, Tag 0G7U]; its scheme-theoretic form is
`AlgebraicGeometry.ExtendedAlternatingCech.isPullback_equationsClosedSubscheme`. -/
public theorem equationsClosedSet_pullback :
    equationsClosedSet (fun j => g.appTop (f j)) =
      closedSubsetPreimage g.toLRSHom.toShHom (equationsClosedSet f) := by
  have hbasic : ∀ i, (X'.basicOpen (g.appTop (f i)) : Set X') =
      ⇑g ⁻¹' (X.basicOpen (f i) : Set X) := fun i =>
    congrArg (fun U : X'.Opens => (U : Set X')) (Scheme.preimage_basicOpen g (f i)).symm
  apply compl_injective
  simp only [equationsClosedSet, closedSubsetPreimage, compl_compl, Set.preimage_compl,
    Opens.coe_iSup, Set.preimage_iUnion, hbasic]
  rfl

/-- The common zero locus of the pulled-back equations is closed. -/
public theorem isClosed_equationsClosedSet_pullback :
    IsClosed (closedSubsetPreimage g.toLRSHom.toShHom (equationsClosedSet f)) :=
  isClosed_closedSubsetPreimage _ _ (isClosed_equationsClosedSet f)

/-- **`Lg^*(ℱ^•)` has its cohomology supported on `Z' = g^{-1}(Z)`.**  The extended alternating
Čech complex is supported on the common zero locus of the equations by [Stacks, Tag 0G7K]
(`cohomologySupportedOn_cech`) and derived pullback preserves cohomological support
(`cohomologySupportedOn_derivedPullback`).

This is what makes the cancellation `hom_ext_of_comp_supportPushCounit` applicable at the source
of the remark's diagram, which is the step its proof performs when it compares the two ways
around the diagram by their composites with `i'_* R𝓗_{Z'}(ℱ') ⟶ ℱ'`. -/
public theorem cohomologySupportedOn_derivedPullback_cplx (F : X.Modules) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X'.toRingedSpace)
      (closedSubsetPreimage g.toLRSHom.toShHom (equationsClosedSet f))
      ((derivedPullback g.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat))) :=
  cohomologySupportedOn_derivedPullback g.toLRSHom.toShHom (equationsClosedSet f) _
    (cohomologySupportedOn_cech f F)

/-- **The cancellation at the source of the remark's diagram.**  Two maps
`Lg^*(ℱ^•) ⟶ i'_* R𝓗_{Z'}(K)` with the same composite with the canonical map
`i'_* R𝓗_{Z'}(K) ⟶ K` of [Stacks, Tag 0G72] are equal.

This is `hom_ext_of_comp_supportPushCounit` at the support statement
`cohomologySupportedOn_derivedPullback_cplx`, in the shape the remark's proof uses it. -/
public theorem hom_ext_of_comp_supportPushCounit_cplx (F : X.Modules)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))}
    {α β : (derivedPullback g.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat)) ⟶
        (supportPush (isClosed_equationsClosedSet_pullback g f)).obj K}
    (h : α ≫ (supportPushCounit (isClosed_equationsClosedSet_pullback g f)).app K =
      β ≫ (supportPushCounit (isClosed_equationsClosedSet_pullback g f)).app K) : α = β :=
  hom_ext_of_comp_supportPushCounit (isClosed_equationsClosedSet_pullback g f)
    (cohomologySupportedOn_derivedPullback_cplx g f F) h

end Setting

/-! ### The derived diagram of Stacks 0G7U commutes -/

section Square

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤))

/-- the common zero locus of the pulled-back equations sits inside `Z' = g^{-1}(Z)` -/
public theorem equationsClosedSet_pullback_subset :
    equationsClosedSet (fun j => g.appTop (f j)) ⊆
      closedSubsetPreimage g.toLRSHom.toShHom (equationsClosedSet f) :=
  (equationsClosedSet_pullback g f).subset

/-- **The derived diagram of Stacks 0G7U commutes**, for any lower horizontal arrow `θ` and any
down arrow `δ` compatible with the augmentations of Stacks 0G7L.

Going around the diagram of [Stacks, Tag 0G7U] both ways gives two maps
`Lg^*(ℱ^•) ⟶ i'_* R𝓗_{Z'}(ℱ')`: counter-clockwise, the comparison of [Stacks, Tag 0G7L] for
`ℱ, f₁, …, f_c` pulled back, followed by the upper route `supportedPullbackRoute` and by
`i'_* R𝓗_{Z'}` of the down arrow `δ`; clockwise, the lower horizontal arrow `θ` followed by the
comparison of [Stacks, Tag 0G7L] for `ℱ', f'₁, …, f'_c`.  They agree because their composites
with the canonical map `i'_* R𝓗_{Z'}(ℱ') ⟶ ℱ'` of [Stacks, Tag 0G72] are both the canonical map
`Lg^*(ℱ^•) ⟶ ℱ'`, and that composition is injective on maps out of `Lg^*(ℱ^•)` by
`hom_ext_of_comp_supportPushCounit_cplx`, the source being supported on `Z'`.

This is the source's own proof.  Its three ingredients are the commuting triangle of
[Stacks, Tag 0G7L] (`cechToDerivedSupport_comp_derivedSupportedSectionsToId`) on each side, the
commuting triangle of [Stacks, Tag 0G78] (`supportedPullbackRoute_comp_counit`) and naturality
of the canonical map of [Stacks, Tag 0G72] at `δ`.

Neither the lower horizontal arrow nor the down arrow is constructed here: the statement holds
for *every* pair `(θ, δ)` satisfying the compatibility `hθ` with the augmentations of
[Stacks, Tag 0G7L], which is all the source's argument uses.  In particular it applies to the
arrows the source writes down, `Lg^*ℱ^• ⟶ g^*ℱ^• ⟶ (ℱ')^•` and the map induced by
`Lg^*ℱ ⟶ g^*ℱ = ℱ'`, once those are built. -/
public theorem derivedBaseChangeSquare (F : X.Modules)
    {θ : (derivedPullback g.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat)) ⟶
        DerivedCategory.Q.obj ((cplx (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F)).extend ComplexShape.embeddingUpNat)}
    {δ : (derivedPullback g.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) ⟶
        (DerivedCategory.singleFunctor X'.Modules 0).obj ((Scheme.Modules.pullback g).obj F)}
    (hθ : θ ≫ augmentation (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) =
      (derivedPullback g.toLRSHom.toShHom).map (augmentation f F) ≫ δ) :
    (derivedPullback g.toLRSHom.toShHom).map
          (cechToDerivedSupport f F (isClosed_equationsClosedSet f) le_rfl) ≫
        supportedPullbackRoute g.toLRSHom.toShHom (equationsClosedSet f)
            (isClosed_equationsClosedSet f)
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
        (supportPush (isClosed_equationsClosedSet_pullback g f)).map δ =
      θ ≫ cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
        (isClosed_equationsClosedSet_pullback g f) (equationsClosedSet_pullback_subset g f) := by
  have hroute : supportedPullbackRoute g.toLRSHom.toShHom (equationsClosedSet f)
          (isClosed_equationsClosedSet f)
          ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
        (supportPushCounit (isClosed_equationsClosedSet_pullback g f)).app
          ((derivedPullback g.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) =
      (derivedPullback g.toLRSHom.toShHom).map
        ((supportPushCounit (isClosed_equationsClosedSet f)).app
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) := by
    rw [supportPushCounit_eq_counit, supportPushCounit_eq_counit]
    exact supportedPullbackRoute_comp_counit g.toLRSHom.toShHom (equationsClosedSet f)
      (isClosed_equationsClosedSet f) ((DerivedCategory.singleFunctor X.Modules 0).obj F)
  have hnat : (supportPush (isClosed_equationsClosedSet_pullback g f)).map δ ≫
        (supportPushCounit (isClosed_equationsClosedSet_pullback g f)).app
          ((DerivedCategory.singleFunctor X'.Modules 0).obj
            ((Scheme.Modules.pullback g).obj F)) =
      (supportPushCounit (isClosed_equationsClosedSet_pullback g f)).app
          ((derivedPullback g.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫ δ :=
    (supportPushCounit (isClosed_equationsClosedSet_pullback g f)).naturality δ
  have hmap : (derivedPullback g.toLRSHom.toShHom).map
          (cechToDerivedSupport f F (isClosed_equationsClosedSet f) le_rfl) ≫
        (derivedPullback g.toLRSHom.toShHom).map
          ((supportPushCounit (isClosed_equationsClosedSet f)).app
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) =
      (derivedPullback g.toLRSHom.toShHom).map (augmentation f F) :=
    Eq.trans ((derivedPullback g.toLRSHom.toShHom).map_comp _ _).symm
      (congrArg (derivedPullback g.toLRSHom.toShHom).map
        (cechToDerivedSupport_comp_derivedSupportedSectionsToId f F
          (isClosed_equationsClosedSet f) le_rfl))
  have hcech' : cechToDerivedSupport (fun j => g.appTop (f j))
            ((Scheme.Modules.pullback g).obj F) (isClosed_equationsClosedSet_pullback g f)
            (equationsClosedSet_pullback_subset g f) ≫
        (supportPushCounit (isClosed_equationsClosedSet_pullback g f)).app
          ((DerivedCategory.singleFunctor X'.Modules 0).obj
            ((Scheme.Modules.pullback g).obj F)) =
      augmentation (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) :=
    cechToDerivedSupport_comp_derivedSupportedSectionsToId (fun j => g.appTop (f j))
      ((Scheme.Modules.pullback g).obj F) (isClosed_equationsClosedSet_pullback g f)
      (equationsClosedSet_pullback_subset g f)
  have key : ∀ {V₀ V₁ V₂ V₃ V₄ V₅ :
        DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))}
      (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (u : V₂ ⟶ V₃) (v : V₃ ⟶ V₄) (w : V₂ ⟶ V₅) (d : V₅ ⟶ V₄)
      (a₂ : V₁ ⟶ V₅) (s : V₀ ⟶ V₅),
      u ≫ v = w ≫ d → b ≫ w = a₂ → a ≫ a₂ = s → (a ≫ b ≫ u) ≫ v = s ≫ d := by
    intro V₀ V₁ V₂ V₃ V₄ V₅ a b u v w d a₂ s h₁ h₂ h₃
    subst h₂
    subst h₃
    simp only [Category.assoc, h₁]
  refine hom_ext_of_comp_supportPushCounit_cplx g f F ?_
  refine Eq.trans (key _ _ _ _ _ δ _ _ hnat hroute hmap) ?_
  refine Eq.trans hθ.symm ?_
  exact Eq.trans (congrArg (fun ψ => θ ≫ ψ) hcech'.symm) (Category.assoc _ _ _).symm

end Square

end Stacks.Perfect.SupportedDerivedBaseChange

end
