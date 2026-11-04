module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FreeAtGenericPointsTransition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The locus where a module is free of a fixed rank, and its image in the base

For an `𝒪_X`-module `F` on a scheme, the set of points near which `F` is free of rank `p` is
open, and the rank is determined by the point. For the family of Situation 05MP and a scheme `T`
over its base, the image in `T` of that locus for the module pulled back to `X ×_S T` is again
open, because the base change of a smooth family is universally open; and a point of `T` lies in
that image exactly when the module is free of rank `p` near the generic point of the fibre over
that point. The generic-point condition of Situation 05MP therefore says precisely that this
image is everything, and the image grows under base change.

## Main definitions

* `AlgebraicGeometry.FreeAtGenericPointsSituation.freeRankLocus` is the locus in `X ×_S T` where
  the pulled-back module is free of rank `p`.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.baseRankLocus` is its image in `T`.

## Main results

* `AlgebraicGeometry.isOpen_setOf_freeAtPointOfRank` and
  `AlgebraicGeometry.freeAtPointOfRank_unique`: freeness of a fixed rank near a point is an open
  condition, and the rank is determined.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.isOpen_baseRankLocus`: the image in the base of
  the free-rank locus is open.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.mem_baseRankLocus_iff`: a point of the base lies
  in that image exactly when the module is free of rank `p` near the generic point of the fibre
  over it.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.condition_iff_baseRankLocus_eq_univ`: the
  generic-point condition over `T` is the assertion that the image is all of `T`.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.preimage_baseRankLocus_subset`: the image pulls
  back into the image for a further base change.

## Implementation notes

`AlgebraicGeometry.FreeAtPointOfRank` is spelled with
`Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank`, whose single field is the same as
that of `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`; the three transport lemmas
`invertibleRank_of_moduleIso`, `invertibleRank_pullback` and `invertibleRank_pullback_comp` state
invariance under an isomorphism of modules, stability under pullback, and the combination of the
two that compares pullbacks along a composite with pullbacks along its factors. The last is what
lets a witness open be shrunk (`invertibleRank_pullback_of_le`) and transported along a transition
morphism of base changes.

Openness of the free-rank locus needs no hypothesis on the module: a witness neighbourhood of one
of its points is a neighbourhood of all of its points, so the locus is a union of opens. That the
rank is determined is read off the fibre rank on the intersection of two witnesses, which is
nonempty because it contains the point.

That a point of the base lies in the image of the locus exactly when the module is free of rank
`p` near the fibre's generic point is the only place where irreducibility of the fibres is used:
a point of the locus over `t` lies in the fibre over `t`, so the preimage in that fibre of its
witness neighbourhood is a nonempty open, and a nonempty open of an irreducible space contains
its generic point.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Transport of finite local freeness of a fixed rank -/

/-- The `Stacks` version of finite local freeness of a fixed rank implies the Mathlib-style one. -/
private theorem isFiniteLocallyFreeOfRank_of_invertible {X : Scheme.{u}} {M : X.Modules} {p : ℕ}
    (h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} M p) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M p :=
  ⟨h.exists_isFiniteLocallyFreeOfRankData⟩

/-- The Mathlib-style version of finite local freeness of a fixed rank implies the `Stacks` one. -/
private theorem invertible_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}} {M : X.Modules} {p : ℕ}
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M p) :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} M p :=
  ⟨h.exists_isFiniteLocallyFreeOfRankData⟩

/-- Finite local freeness of a fixed rank is invariant under an isomorphism of modules. -/
theorem invertibleRank_of_moduleIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (p : ℕ)
    (h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} M p) :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} N p :=
  invertible_of_isFiniteLocallyFreeOfRank
    (SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e
      (isFiniteLocallyFreeOfRank_of_invertible h))

/-- Finite local freeness of a fixed rank is stable under pullback. -/
theorem invertibleRank_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (p : ℕ)
    (h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u} M p) :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj M) p := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact invertible_of_isFiniteLocallyFreeOfRank
    (Stacks.AlgebraicGeometry.ComponentDegrees.rankPullbackData f.base f.toRingCatSheafHom M p
      (isFiniteLocallyFreeOfRank_of_invertible h))

/-- If the pullback of a module along a morphism is finite locally free of rank `p`, then so is
its pullback along that morphism precomposed with any other. -/
theorem invertibleRank_pullback_comp {X Y Z : Scheme.{u}} (F : X.Modules) (p : ℕ)
    {b : Z ⟶ X} {a : Y ⟶ Z} {d : Y ⟶ X} (hd : a ≫ b = d)
    (h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback b).obj F) p) :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback d).obj F) p :=
  invertibleRank_of_moduleIso ((Scheme.Modules.pullbackComp a b).app F ≪≫
    eqToIso (congrArg (fun k : Y ⟶ X => (Scheme.Modules.pullback k).obj F) hd)) p
    (invertibleRank_pullback a _ p h)

/-- Finite local freeness of a fixed rank on an open set passes to a smaller open set. -/
theorem invertibleRank_pullback_of_le {X : Scheme.{u}} (F : X.Modules) (p : ℕ) {U V : X.Opens}
    (hUV : U ≤ V)
    (h : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj F) p) :
    Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) p :=
  invertibleRank_pullback_comp F p (Scheme.homOfLE_ι X hUV) h

/-! ### Freeness of a fixed rank near a point -/

/-- The locus where a module is free of a fixed rank is open: a witness neighbourhood of one of
its points witnesses the condition at every point of that neighbourhood. -/
theorem isOpen_setOf_freeAtPointOfRank {X : Scheme.{u}} (F : X.Modules) (p : ℕ) :
    IsOpen {x : X | FreeAtPointOfRank F x p} :=
  isOpen_iff_forall_mem_open.mpr fun _ ⟨U, hxU, hU⟩ => ⟨U, fun _ hy => ⟨U, hy, hU⟩, U.2, hxU⟩

/-- The rank of a module free of a fixed rank near a point is determined: on the intersection of
two witness neighbourhoods, which contains the point, both ranks are the fibre rank. -/
@[sga "6 I 6.10" "special case"]
theorem freeAtPointOfRank_unique {X : Scheme.{u}} (F : X.Modules) {x : X} {n m : ℕ}
    (hn : FreeAtPointOfRank F x n) (hm : FreeAtPointOfRank F x m) : n = m := by
  obtain ⟨U, hxU, hU⟩ := hn
  obtain ⟨V, hxV, hV⟩ := hm
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_unique
    ((Scheme.Modules.pullback (U ⊓ V).ι).obj F)
    (isFiniteLocallyFreeOfRank_of_invertible
      (invertibleRank_pullback_of_le F n (inf_le_left : U ⊓ V ≤ U) hU))
    (isFiniteLocallyFreeOfRank_of_invertible
      (invertibleRank_pullback_of_le F m (inf_le_right : U ⊓ V ≤ V) hV))
    ⟨x, ⟨hxU, hxV⟩⟩

namespace FreeAtGenericPointsSituation

variable (D : FreeAtGenericPointsSituation.{u}) (p : ℕ)

/-! ### The base change of the family is flat, of finite presentation and open -/

/-- The base change `X ×_S T ⟶ T` of the family along `T ⟶ S` is flat. -/
instance flat_baseChangeMap (T : Over D.S) : Flat (D.baseChangeMap T) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.f T.hom) inferInstance

/-- The base change `X ×_S T ⟶ T` of the family along `T ⟶ S` is locally of finite
presentation. -/
instance locallyOfFinitePresentation_baseChangeMap (T : Over D.S) :
    LocallyOfFinitePresentation (D.baseChangeMap T) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.f T.hom) inferInstance

/-- The base change of the family is an open map: it is flat and locally of finite presentation,
hence universally open. -/
theorem isOpenMap_baseChangeMap (T : Over D.S) : IsOpenMap (D.baseChangeMap T) :=
  Scheme.Hom.isOpenMap _

/-! ### The free-rank locus and its image in the base -/

/-- The locus in `X ×_S T` where the pulled-back module is free of rank `p`. -/
def freeRankLocus (T : Over D.S) : Set ↥(pullback D.f T.hom) :=
  {x | FreeAtPointOfRank (D.baseChangeModule T) x p}

/-- The locus in `X ×_S T` where the pulled-back module is free of rank `p` is an open set. -/
theorem isOpen_freeRankLocus (T : Over D.S) : IsOpen (D.freeRankLocus p T) :=
  isOpen_setOf_freeAtPointOfRank _ _

/-- Freeness of rank `p` at a point of one base change descends from the image of that point in
another: the two modules are pullbacks of the module on the total space. -/
theorem freeAtPointOfRank_transitionHom {T T' : Over D.S} (g : T' ⟶ T)
    {x' : ↥(pullback D.f T'.hom)}
    (h : FreeAtPointOfRank (D.baseChangeModule T) (D.transitionHom g x') p) :
    FreeAtPointOfRank (D.baseChangeModule T') x' p := by
  obtain ⟨A, hA, hrank⟩ := h
  refine ⟨D.transitionHom g ⁻¹ᵁ A, hA, ?_⟩
  refine invertibleRank_of_moduleIso ?_ p
    (invertibleRank_pullback_comp (D.baseChangeModule T) p
      (morphismRestrict_ι (D.transitionHom g) A) hrank)
  exact ((Scheme.Modules.pullbackComp (D.transitionHom g ⁻¹ᵁ A).ι (D.transitionHom g)).app
      (D.baseChangeModule T)).symm ≪≫
    (Scheme.Modules.pullback (D.transitionHom g ⁻¹ᵁ A).ι).mapIso (D.transitionModuleIso g)

/-- The image in `T` of the locus where the pulled-back module is free of rank `p`. -/
def baseRankLocus (T : Over D.S) : Set T.left :=
  D.baseChangeMap T '' D.freeRankLocus p T

/-- The image in `T` of the locus where the pulled-back module is free of rank `p` is an open
set. -/
theorem isOpen_baseRankLocus (T : Over D.S) : IsOpen (D.baseRankLocus p T) :=
  D.isOpenMap_baseChangeMap T _ (D.isOpen_freeRankLocus p T)

/-- A point of the base lies in the image of the free-rank locus exactly when the module is free
of rank `p` near the generic point of the fibre over it. -/
theorem mem_baseRankLocus_iff (T : Over D.S) (t : T.left) :
    t ∈ D.baseRankLocus p T ↔
      ∀ ξ : (D.baseChangeMap T).fiber t, IsGenericPoint ξ (Set.univ : Set _) →
        FreeAtPointOfRank (D.baseChangeModule T) ((D.baseChangeMap T).fiberι t ξ) p := by
  constructor
  · rintro ⟨y, ⟨A, hyA, hA⟩, hyt⟩ ξ hξ
    refine ⟨A, ?_, hA⟩
    obtain ⟨y₀, rfl⟩ : y ∈ Set.range ((D.baseChangeMap T).fiberι t) := by
      rwa [Scheme.Hom.range_fiberι]
    exact mem_of_isGenericPoint hξ (A.2.preimage ((D.baseChangeMap T).fiberι t).continuous)
      hyA (Set.mem_univ y₀)
  · intro h
    obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T t
    exact ⟨(D.baseChangeMap T).fiberι t ξ, h ξ hξ,
      ((D.baseChangeMap T).range_fiberι t).subset ⟨ξ, rfl⟩⟩

/-- The generic-point condition over a scheme over the base is the assertion that the image of the
free-rank locus is all of that scheme. -/
theorem condition_iff_baseRankLocus_eq_univ (T : Over D.S) :
    D.Condition p T ↔ D.baseRankLocus p T = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact forall_congr' fun t => (D.mem_baseRankLocus_iff p T t).symm

/-- The image of the free-rank locus pulls back into the image of the free-rank locus of a further
base change: the generic point of a fibre upstairs lies over the generic point of the fibre
downstairs. -/
theorem preimage_baseRankLocus_subset {T T' : Over D.S} (g : T' ⟶ T) :
    g.left ⁻¹' D.baseRankLocus p T ⊆ D.baseRankLocus p T' := by
  intro t' ht'
  rw [Set.mem_preimage, D.mem_baseRankLocus_iff] at ht'
  rw [D.mem_baseRankLocus_iff]
  intro ξ' hξ'
  obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T (g.left t')
  refine D.freeAtPointOfRank_transitionHom p g ?_
  rw [D.transitionHom_fiberι_of_isGenericPoint g t' hξ' hξ]
  exact ht' ξ hξ

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
