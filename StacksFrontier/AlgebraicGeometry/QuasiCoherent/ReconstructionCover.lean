module

public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.SupportedSerreQuotient

/-!
# The opens produced by Gabriel–Rosenberg reconstruction cover the target

Let `X` and `Y` be schemes and let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  Step 6 of
[Stacks, Tag 0GPJ] attaches to a quasi-compact open `U ⊆ X` with closed complement `Z` an open
`V ⊆ Y` with closed complement `T`, matched in the sense that `e` carries the quasi-coherent
modules supported on `Z` onto those supported on `T`.  This file proves the one assertion of
step 3 that the rest of the development took as a hypothesis: **if the opens `U i` cover `X`,
then the matched opens `V i` cover `Y`.**

The argument is the one the source indicates.  A point `y` outside every `V i` lies in every
`T i`.  Each `T i` is closed, so the closure of `{y}` lies in every `T i`, and there is a
*nonzero* quasi-coherent `𝒪_Y`-module `N` supported inside that closure, namely the direct image
of the structure sheaf of the reduced closed subscheme on `closure {y}`.  Transporting `N` back
along `e` gives a quasi-coherent `𝒪_X`-module supported in every `Z i`; since the `U i` cover
`X` the sets `Z i` have empty intersection, so that module has empty support, hence is zero
([Stacks, Tag 056J]) — and then `N` is zero too, contradicting `y ∈ Supp N`.

## Main results

* `AlgebraicGeometry.exists_isQuasicoherent_mem_supp_of_isClosedImmersion` — the direct image of
  the structure sheaf along a closed immersion with integral source is quasi-coherent, is
  supported inside the range of the immersion, and is nonzero at the image of the generic point.
* `AlgebraicGeometry.exists_isQuasicoherent_mem_supp_subset_closure` — **for every point `y` of
  a scheme there is a quasi-coherent module whose support contains `y` and is contained in
  `closure {y}`.**
* `AlgebraicGeometry.quasicoherentSupportedOn_of_iso` — support containment in a subset is
  invariant under isomorphism of quasi-coherent modules.
* `AlgebraicGeometry.isOpenCover_of_supportedCorrespondence` — **the covering statement**: for
  families of opens `U i ⊆ X` and `V i ⊆ Y` whose closed complements `Z i` and `T i` are matched
  by `e`, if the `U i` cover `X` then the `V i` cover `Y`.
* `AlgebraicGeometry.isOpenCover_opensRange_of_supportedCorrespondence` — the same, phrased for
  the images of the inclusions `(V i).ι`, which is the form the descent datum
  `AlgebraicGeometry.ReconstructionGlue.glueData` consumes.

## Implementation notes

**Why a closed immersion and not a quotient of the structure sheaf.**  The module supported on
`closure {y}` could also be taken to be `𝒪_Y / I` for `I` the vanishing ideal of that closure,
but that would need the support of such a quotient to be computed, which nothing in the
repository does.  The direct image of the structure sheaf of the reduced induced subscheme needs
no new computation: its support is contained in the range of the immersion by
`Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.supp_pushforward_subset` and contains
the image of the generic point by
`Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.mem_supp_pushforward_unit`, and no
Noetherian hypothesis enters either.

**Three categories for one notion.**  The quasi-coherent modules form a full subcategory of
`SheafOfModules Y.ringCatSheaf`, while supports are stated for
`AlgebraicGeometry.Scheme.Modules`; the morphisms of a full subcategory are a structure, so
`CategoryTheory.Limits.IsZero` of an object of the full subcategory is *not* definitionally
`IsZero` of the underlying `Y.Modules`.  Both directions of that bridge are therefore taken
explicitly: `CategoryTheory.Functor.map_isZero` of the inclusion in one direction, and
`CategoryTheory.Functor.map_injective` of the inclusion applied to
`CategoryTheory.Limits.IsZero.iff_id_eq_zero` in the other — the same two steps that
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/SupportedSerreQuotient.lean` uses.  An
*isomorphism*, by contrast, does cross by `CategoryTheory.Functor.mapIso` alone.

**Vanishing of a module with empty support is not re-proved.**
`Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty` is public and is exactly
the statement needed, and `AlgebraicGeometry.supportSet` and `SheafOfModules.supp` are the same
term.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.3 (Tag 0GPG)](https://stacks.math.columbia.edu/tag/0GPG)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-! ### A nonzero quasi-coherent module supported in the closure of a point -/

section PointSupported

variable {Y : Scheme.{u}}

/-- **The direct image of the structure sheaf along a closed immersion with integral source** is
quasi-coherent, is supported inside the range of the immersion, and has the image of the generic
point in its support.

Quasi-coherence is the statement for an affine morphism; the containment of the support uses
only closedness of the range; and the generic point is in the support because a closed immersion
is injective, so the fibre over the image of the generic point is that point alone and the stalk
there is the stalk of the structure sheaf of an integral scheme. -/
theorem exists_isQuasicoherent_mem_supp_of_isClosedImmersion {W : Scheme.{u}} (i : W ⟶ Y)
    [IsClosedImmersion i] [IsIntegral W] :
    ∃ N : Y.Modules, SheafOfModules.IsQuasicoherent N ∧
      i (genericPoint W) ∈ SheafOfModules.supp N ∧
      SheafOfModules.supp N ⊆ Set.range i.base := by
  refine ⟨(Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf),
    Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom i _,
    ?_,
    Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.supp_pushforward_subset i _
      i.isClosedEmbedding.isClosed_range subset_rfl⟩
  refine Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.mem_supp_pushforward_unit i ?_
  exact Set.eq_singleton_iff_unique_mem.2 ⟨rfl, fun _ hz => i.isClosedEmbedding.injective hz⟩

/-- **For every point `y` of a scheme there is a quasi-coherent module whose support contains `y`
and is contained in `closure {y}`.**  It is the direct image of the structure sheaf of the
reduced induced closed subscheme on `closure {y}`, whose generic point is `y`. -/
theorem exists_isQuasicoherent_mem_supp_subset_closure (y : Y) :
    ∃ N : Y.Modules, SheafOfModules.IsQuasicoherent N ∧ y ∈ SheafOfModules.supp N ∧
      SheafOfModules.supp N ⊆ closure ({y} : Set Y) := by
  let _ := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y
  obtain ⟨N, hqc, hmem, hsub⟩ := exists_isQuasicoherent_mem_supp_of_isClosedImmersion
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).subschemeι
  rw [Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.subschemeι_genericPoint_closure
    y] at hmem
  rw [Scheme.IdealSheafData.range_subschemeι_vanishingIdeal] at hsub
  exact ⟨N, hqc, hmem, hsub⟩

end PointSupported

/-! ### The covering statement -/

section Cover

variable {X Y : Scheme.{u}}

/-- **Support containment in a subset is invariant under isomorphism of quasi-coherent
modules.**  The inclusion of the quasi-coherent modules carries the isomorphism to an
isomorphism of the underlying `𝒪_X`-modules, and isomorphic modules have the same support. -/
theorem quasicoherentSupportedOn_of_iso {Z : Set X}
    {A B : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (α : A ≅ B)
    (h : quasicoherentSupportedOn X Z A) : quasicoherentSupportedOn X Z B := by
  have hsupp :
      SheafOfModules.supp (A.obj : X.Modules) = SheafOfModules.supp (B.obj : X.Modules) :=
    SheafOfModules.supp_eq_of_iso ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapIso α)
  intro x hx
  refine h x ?_
  have hx' : x ∈ SheafOfModules.supp (B.obj : X.Modules) := hx
  rw [← hsupp] at hx'
  exact hx'

variable (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)

/-- **The opens matched by an equivalence of quasi-coherent modules cover the target.**  Let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence, let `U i ⊆ X` and `V i ⊆ Y` be opens with closed
complements `Z i` and `T i`, and suppose `e` matches the quasi-coherent modules supported on
`Z i` with those supported on `T i`.  If the `U i` cover `X` then the `V i` cover `Y`.

This is the assertion of step 3 of [Stacks, Tag 0GPJ] that the local steps leave open.  A point
`y` outside every `V i` lies in every `T i`, hence `closure {y} ⊆ T i` for every `i`; the
quasi-coherent module of
`AlgebraicGeometry.exists_isQuasicoherent_mem_supp_subset_closure` is then supported on every
`T i`, so its inverse image under `e` is supported on every `Z i`, hence has empty support
because the `U i` cover `X`, hence is zero, hence so is the module itself — contradicting that
`y` is in its support. -/
theorem isOpenCover_of_supportedCorrespondence {ι : Type v} (U : ι → X.Opens) (V : ι → Y.Opens)
    (Z : ι → Set X) (T : ι → Set Y)
    (hcorr : ∀ (i : ι) (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory),
      quasicoherentSupportedOn X (Z i) E ↔ quasicoherentSupportedOn Y (T i) (e.functor.obj E))
    (hUZ : ∀ i, (U i : Set X) = (Z i)ᶜ) (hVT : ∀ i, (V i : Set Y) = (T i)ᶜ)
    (hUcover : IsOpenCover U) : IsOpenCover V := by
  have key : ∀ y : Y, ∃ i, y ∈ (V i : Set Y) := by
    intro y
    by_contra hy
    push Not at hy
    have hyT : ∀ i, y ∈ T i := by
      intro i
      by_contra h
      exact hy i (by rw [hVT i]; exact h)
    obtain ⟨N, hNqc, hyN, hNsub⟩ := exists_isQuasicoherent_mem_supp_subset_closure y
    set N' : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory := ⟨N, hNqc⟩
    have hTclosed : ∀ i, closure ({y} : Set Y) ⊆ T i := by
      intro i
      refine closure_minimal (Set.singleton_subset_iff.2 (hyT i)) ?_
      have hTc : T i = ((V i : Set Y))ᶜ := by rw [hVT i, compl_compl]
      rw [hTc]
      exact (V i).isOpen.isClosed_compl
    have hN'T : ∀ i, quasicoherentSupportedOn Y (T i) N' := fun i x hx =>
      hTclosed i (hNsub hx)
    have hEZ : ∀ i, quasicoherentSupportedOn X (Z i) (e.inverse.obj N') := fun i =>
      (hcorr i _).2 (quasicoherentSupportedOn_of_iso (e.counitIso.app N').symm (hN'T i))
    have hempty : SheafOfModules.supp ((e.inverse.obj N').obj : X.Modules) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      obtain ⟨i, hi⟩ := hUcover.exists_mem x
      have hxU : x ∈ (U i : Set X) := hi
      rw [hUZ i] at hxU
      exact hxU (hEZ i x hx)
    have hEzero : IsZero (e.inverse.obj N') :=
      (IsZero.iff_id_eq_zero _).2
        ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.map_injective
          ((IsZero.iff_id_eq_zero _).mp
            (Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _ hempty)))
    have hfzero : IsZero (e.functor.obj (e.inverse.obj N')) :=
      IsZero.of_full_of_faithful_of_isZero e.inverse _
        ((e.unitIso.app (e.inverse.obj N')).isZero_iff.1 hEzero)
    have hNm : IsZero (N : Y.Modules) :=
      Functor.map_isZero (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι
        ((e.counitIso.app N').isZero_iff.1 hfzero)
    obtain ⟨a, ha⟩ := hyN
    exact ha ((AddCommGrpCat.subsingleton_of_isZero
      (Functor.map_isZero (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y)
        (Functor.map_isZero (Scheme.Modules.toPresheaf Y) hNm))).elim a 0)
  have huniv : ⋃ i, (V i : Set Y) = Set.univ :=
    Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (key y)
  refine IsOpenCover.mk (SetLike.coe_injective ?_)
  simpa using huniv

/-- `AlgebraicGeometry.isOpenCover_of_supportedCorrespondence` phrased for the images of the
inclusions `(V i).ι`, which is the form in which
`AlgebraicGeometry.ReconstructionGlue.glueData` asks for the covering. -/
theorem isOpenCover_opensRange_of_supportedCorrespondence {ι : Type v} (U : ι → X.Opens)
    (V : ι → Y.Opens) (Z : ι → Set X) (T : ι → Set Y)
    (hcorr : ∀ (i : ι) (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory),
      quasicoherentSupportedOn X (Z i) E ↔ quasicoherentSupportedOn Y (T i) (e.functor.obj E))
    (hUZ : ∀ i, (U i : Set X) = (Z i)ᶜ) (hVT : ∀ i, (V i : Set Y) = (T i)ᶜ)
    (hUcover : IsOpenCover U) : IsOpenCover fun i => ((V i).ι).opensRange := by
  simpa only [Scheme.Opens.opensRange_ι] using
    isOpenCover_of_supportedCorrespondence e U V Z T hcorr hUZ hVT hUcover

end Cover

end AlgebraicGeometry

end
