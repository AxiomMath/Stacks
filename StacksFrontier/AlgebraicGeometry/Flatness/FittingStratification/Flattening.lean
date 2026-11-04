module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.FittingStratification.Exhaustion
public import
  StacksFrontier.AlgebraicGeometry.Flatness.FittingStratification.RankStratumFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The flattening stratification of a finitely presented module

Let `F` be a finitely presented module on a scheme `S`. The disjoint union of the Fitting rank
strata of `F` is a scheme over `S` which represents the condition that a base change of `F` be
flat: a morphism `g : T ⟶ S` factors through it, and then uniquely, exactly when the pullback of
`F` to `T` is flat. On the `r`-th stratum `F` pulls back to a module which is finite locally
free of rank `r`, and the structural morphism of the disjoint union is of finite presentation.

## Main definitions

* `AlgebraicGeometry.flatnessStratification` is the disjoint union of the Fitting rank strata.
* `AlgebraicGeometry.flatnessStratificationHom` is its structural morphism to the base.

## Main results

* `AlgebraicGeometry.flat_iff_existsUnique_lift` is the representing property.
* `AlgebraicGeometry.rankStratum_isFiniteLocallyFreeOfRank` is the rank on a stratum.
* `AlgebraicGeometry.flatnessStratification_finitePresentation` is finite presentation of the
  structural morphism of the disjoint union; finite presentation of each individual stratum is
  `AlgebraicGeometry.finitePresentation_fittingRankStratum`.

## Implementation notes

Flatness of the pullback is converted into finite local freeness, and from there into a constant
value of the fibre rank, by four of the five equivalent conditions of Stacks Tag 05P2
(`AlgebraicGeometry.Scheme.Modules.flat_finitePresentation_locallyFree_tfae`). The strata of the
base change are then the fibres of the fibre rank, a locally constant `ℕ`-valued function, so
they are open and pairwise disjoint; that disjointness is what makes the local factorizations
through the individual strata glue, and what makes the glued factorization unique.

In the converse direction only local freeness of the pullback is needed, and the open cover of
`T` pulled back from the coproduct cover of the stratification supplies it stratum by stratum;
no comparison of stalks across that cover is required.

Quasi-compactness of the structural morphism uses that the Fitting generator opens exhaust the
base: a quasi-compact open of `S` already lies inside one of them, which bounds the strata
meeting it and so writes the preimage as a finite union.

The disjoint union and its structural morphism only need `F` to be of finite type and
quasi-coherent, which is what the Fitting rank strata need, so that is what they assume. Finite
type and quasi-coherence of a finitely presented module are supplied by hand in the statements
of the tagged results, as they are in
`AlgebraicGeometry.finitePresentation_fittingRankStratum`, because the Mathlib instances
`SheafOfModules.instIsFiniteTypeOfIsFinitePresentation` and
`SheafOfModules.instIsQuasicoherentOfIsFinitePresentation` are not found by instance synthesis
from a goal that does not determine the universe parameter of
`SheafOfModules.IsFinitePresentation`.

## References

* [Stacks Project, Tag 05P9](https://stacks.math.columbia.edu/tag/05P9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Transport the rank condition along a further pullback: this is the action of the rank `r`
functor on a morphism of schemes over the base. -/
private theorem rank_pullback_comp {S X Y : Scheme.{u}} (F : S.Modules) (r : ℕ) (q : Y ⟶ S)
    (f : X ⟶ Y)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback q).obj F) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (f ≫ q)).obj F) r :=
  ((rankRFunctor S F r).map (Opposite.op (Over.homMk f (by simp) : Over.mk (f ≫ q) ⟶ Over.mk q))
    (ULift.up (PLift.up h))).down.down

/-- **Stacks Project, Tag 05P9.** The flattening stratification of a module of finite type whose
Fitting rank strata are defined: the disjoint union of those strata. -/
public def flatnessStratification {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] : Scheme.{u} :=
  ∐ fun r : ℕ ↦ (fittingRankStratum F r).left

/-- **Stacks Project, Tag 05P9.** The structural morphism from the flattening stratification to
the base, assembled from the structural morphisms of the strata. -/
public def flatnessStratificationHom {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] : flatnessStratification F ⟶ S :=
  Sigma.desc fun r ↦ (fittingRankStratum F r).hom

section Auxiliary

variable {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent]

/-- Every point of the flattening stratification lies on one of the strata. -/
private theorem exists_eq_sigma_ι {ι : Type*} (X : ι → Scheme.{u}) [Small.{u} ι]
    (x : (∐ X : Scheme)) : ∃ (i : ι) (y : X i), Sigma.ι X i y = x :=
  (sigmaOpenCover X).exists_eq x

/-- The module pulls back to a module of rank `r` on the `r`-th Fitting rank stratum: that
stratum represents the rank `r` functor, and the identity of the stratum is the universal
element. -/
private theorem rankStratum_isFiniteLocallyFreeOfRank_aux (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (fittingRankStratum F r).hom).obj F) r :=
  ((Classical.choice (rankRFunctor_representableBy_fittingRankStratum F r)).homEquiv
    (𝟙 (fittingRankStratum F r))).down.down

/-- Two distinct Fitting rank strata do not meet: on their intersection the module would pull
back to a finite locally free module of two different ranks. -/
private theorem rankStrata_pullback_isEmpty {r s : ℕ} (hrs : r ≠ s) :
    IsEmpty ↑(pullback (fittingRankStratum F r).hom (fittingRankStratum F s).hom) := by
  have hr := rank_pullback_comp F r (fittingRankStratum F r).hom
    (pullback.fst (fittingRankStratum F r).hom (fittingRankStratum F s).hom)
    (rankStratum_isFiniteLocallyFreeOfRank_aux F r)
  have hs := rank_pullback_comp F s (fittingRankStratum F s).hom
    (pullback.snd (fittingRankStratum F r).hom (fittingRankStratum F s).hom)
    (rankStratum_isFiniteLocallyFreeOfRank_aux F s)
  have hr' := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullbackCongr (pullback.condition
      (f := (fittingRankStratum F r).hom) (g := (fittingRankStratum F s).hom))).app F) hr
  exact ⟨fun x ↦ hrs (Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ hr' hs x)⟩

/-- On the `r`-th component of the flattening stratification the structural morphism is the
structural morphism of the `r`-th stratum. -/
private theorem ι_comp_flatnessStratificationHom (r : ℕ) :
    Sigma.ι (fun i : ℕ ↦ (fittingRankStratum F i).left) r ≫ flatnessStratificationHom F =
      (fittingRankStratum F r).hom :=
  Sigma.ι_desc (fun i : ℕ ↦ (fittingRankStratum F i).hom) r

/-- Pointwise form of `ι_comp_flatnessStratificationHom`. -/
private theorem flatnessStratificationHom_ι_apply (r : ℕ)
    (x : (fittingRankStratum F r).left) :
    flatnessStratificationHom F
        (Sigma.ι (fun i : ℕ ↦ (fittingRankStratum F i).left) r x) =
      (fittingRankStratum F r).hom x :=
  congrArg (fun f : (fittingRankStratum F r).left ⟶ S ↦ f x) (ι_comp_flatnessStratificationHom F r)

/-- The structural morphism of the flattening stratification is injective on points: two points
with the same image lie on the same stratum, because distinct strata are disjoint, and the
structural morphism of a stratum is an immersion. -/
private theorem flatnessStratificationHom_injective_aux :
    Function.Injective (flatnessStratificationHom F) := by
  let X := fun r : ℕ ↦ (fittingRankStratum F r).left
  intro x y hxy
  obtain ⟨r, x, rfl⟩ := exists_eq_sigma_ι X x
  obtain ⟨s, y, rfl⟩ := exists_eq_sigma_ι X y
  have heq : (fittingRankStratum F r).hom x = (fittingRankStratum F s).hom y := by
    change (flatnessStratificationHom F) ((Sigma.ι X r) x) =
      (flatnessStratificationHom F) ((Sigma.ι X s) y) at hxy
    simpa only [X, flatnessStratificationHom_ι_apply] using hxy
  have hrs : r = s := by
    by_contra hne
    have hd := Scheme.isEmpty_pullback_iff.mp (rankStrata_pullback_isEmpty F hne)
    exact Set.disjoint_left.mp hd ⟨x, rfl⟩ ⟨y, heq.symm⟩
  subst s
  have : IsImmersion (fittingRankStratum F r).hom := isImmersion_fittingRankStratum F r
  exact congrArg (Sigma.ι X r) ((fittingRankStratum F r).hom.isEmbedding.injective heq)

/-- The Fitting closed subschemes decrease with the index, also on underlying sets. -/
private theorem range_fittingClosedSubscheme_antitone {i j : ℕ} (hij : i ≤ j) :
    Set.range (fittingClosedSubscheme F (j : ℤ)).hom ⊆
      Set.range (fittingClosedSubscheme F (i : ℤ)).hom := by
  obtain ⟨f⟩ := fittingClosedSubscheme_antitone F hij
  rintro _ ⟨y, rfl⟩
  exact ⟨f.left y, by simp [← Scheme.Hom.comp_apply, f.w]⟩

/-- The Fitting generator opens increase with the index, because the Fitting closed subschemes
they are complementary to decrease. -/
private theorem fittingGeneratorOpen_mono {i j : ℕ} (hij : i ≤ j) :
    fittingGeneratorOpen F i ≤ fittingGeneratorOpen F j :=
  fun _ hx hy ↦ hx (range_fittingClosedSubscheme_antitone F hij hy)

/-- The Fitting generator opens exhaust the base, so a compact subset of it lies inside one of
them. -/
private theorem exists_generatorOpen_of_isCompact {K : Set S} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ fittingGeneratorOpen F n := by
  classical
  let U := fittingGeneratorOpen F
  have hcover : K ⊆ ⋃ n, (U n : Set S) := by
    show K ⊆ ⋃ n : ℕ, (Set.range (fittingClosedSubscheme F (n : ℤ)).hom.base)ᶜ
    rw [← Set.compl_iInter, fittingClosedSubscheme_iInter_range_eq_empty, Set.compl_empty]
    exact Set.subset_univ K
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun n ↦ (U n : Set S))
    (fun n ↦ (U n).isOpen) hcover
  refine ⟨t.sup id, fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact fittingGeneratorOpen_mono F (Finset.le_sup (f := id) hi) hx

/-- A point of the `r`-th Fitting rank stratum lies off the `n`-th Fitting generator open for
every `n < r`: it lies in the Fitting closed subscheme of index `r - 1`, hence in the one of
index `n`. -/
private theorem rankStratum_notMem_generatorOpen {n r : ℕ} (hnr : n < r)
    (x : (fittingRankStratum F r).left) :
    (fittingRankStratum F r).hom x ∉ fittingGeneratorOpen F n := by
  have hx : (fittingRankStratum F r).hom x ∈
      Set.range (fittingClosedSubscheme F ((r - 1 : ℕ) : ℤ)).hom := by
    rw [show ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 by omega]
    exact ⟨_, rfl⟩
  exact fun h ↦ h (range_fittingClosedSubscheme_antitone F (by omega) hx)

/-- Two morphisms into strata which agree over the base agree after the inclusions into the
disjoint union: either the two strata coincide, and then the structural morphism of the stratum
is a monomorphism, or they are disjoint, and then the source is empty. -/
private theorem rankStratum_comp_ι_eq {Y : Scheme.{u}} (r s : ℕ)
    (a : Y ⟶ (fittingRankStratum F r).left) (b : Y ⟶ (fittingRankStratum F s).left)
    (hab : a ≫ (fittingRankStratum F r).hom = b ≫ (fittingRankStratum F s).hom) :
    a ≫ Sigma.ι (fun i : ℕ ↦ (fittingRankStratum F i).left) r =
      b ≫ Sigma.ι (fun i : ℕ ↦ (fittingRankStratum F i).left) s := by
  by_cases hrs : r = s
  · subst s
    have : IsImmersion (fittingRankStratum F r).hom := isImmersion_fittingRankStratum F r
    rw [(cancel_mono (fittingRankStratum F r).hom).mp hab]
  · have : IsEmpty Y :=
      ⟨fun y ↦ (rankStrata_pullback_isEmpty F hrs).false (pullback.lift a b hab y)⟩
    exact (isInitialOfIsEmpty (X := Y)).hom_ext _ _

/-- A morphism to the flattening stratification which agrees over the base with a morphism to
the `r`-th stratum factors through the `r`-th inclusion: the two agree on the open cover of the
source pulled back from the coproduct cover. -/
private theorem lift_eq_rankStratum_comp_ι {Y : Scheme.{u}} (r : ℕ)
    (a : Y ⟶ (fittingRankStratum F r).left) (h : Y ⟶ flatnessStratification F)
    (hh : h ≫ flatnessStratificationHom F = a ≫ (fittingRankStratum F r).hom) :
    h = a ≫ Sigma.ι (fun i : ℕ ↦ (fittingRankStratum F i).left) r := by
  let C : (flatnessStratification F).OpenCover :=
    sigmaOpenCover fun i : ℕ ↦ (fittingRankStratum F i).left
  let D : Y.OpenCover := C.pullback₁ h
  refine Scheme.Cover.hom_ext D _ _ fun j ↦ ?_
  have hc : C.f j ≫ flatnessStratificationHom F = (fittingRankStratum F j).hom :=
    ι_comp_flatnessStratificationHom F j
  have hmap : C.pullbackHom h j ≫ C.f j = D.f j ≫ h := C.pullbackHom_map h j
  have hab : C.pullbackHom h j ≫ (fittingRankStratum F j).hom =
      (D.f j ≫ a) ≫ (fittingRankStratum F r).hom := by
    rw [← hc, ← Category.assoc, hmap, Category.assoc, hh, Category.assoc]
  exact hmap.symm.trans
    ((rankStratum_comp_ι_eq F j r (C.pullbackHom h j) (D.f j ≫ a) hab).trans
      (Category.assoc _ _ _))

/-- A base change which factors through the flattening stratification is flat: the open cover of
the base pulled back from the coproduct cover trivializes the pullback stratum by stratum, so
the pullback is locally free. -/
private theorem isFlat_pullback_of_lift {T : Scheme.{u}} {g : T ⟶ S}
    (h : T ⟶ flatnessStratification F) (hfac : h ≫ flatnessStratificationHom F = g) :
    SheafOfModules.IsFlat (C := TopologicalSpace.Opens T.toTopCat)
      (J := Opens.grothendieckTopology T.toTopCat) (O := T.sheaf)
      ((Scheme.Modules.pullback g).obj F) := by
  let G := (Scheme.Modules.pullback g).obj F
  let C : (flatnessStratification F).OpenCover :=
    sigmaOpenCover fun r : ℕ ↦ (fittingRankStratum F r).left
  let D : T.OpenCover := C.pullback₁ h
  have hfl : Scheme.Modules.IsFiniteLocallyFree G := by
    refine Stacks.Modules.isFiniteLocallyFree_of_openCover G D fun r ↦ ?_
    have hι : C.f r ≫ flatnessStratificationHom F = (fittingRankStratum F r).hom :=
      ι_comp_flatnessStratificationHom F r
    have hc : D.f r ≫ h = C.pullbackHom h r ≫ C.f r := (C.pullbackHom_map h r).symm
    have heq : D.f r ≫ g = C.pullbackHom h r ≫ (fittingRankStratum F r).hom := by
      rw [← hfac, ← Category.assoc, hc, Category.assoc, hι]
    have h1 := rank_pullback_comp F r (fittingRankStratum F r).hom (C.pullbackHom h r)
      (rankStratum_isFiniteLocallyFreeOfRank_aux F r)
    have h2 := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.pullbackCongr heq).app F).symm h1
    have h3 := SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (((Scheme.Modules.pullbackComp (D.f r) g).app F).symm ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback (D.f r)).app G).symm) h2
    exact (Scheme.Modules.isFiniteLocallyFree_iff _).2
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} (hM := h3) _ r)
  have : _root_.SheafOfModules.IsLocallyFree.{u, u, u} G :=
    (Scheme.Modules.isLocallyFree_iff_pointwise G).2 fun x ↦ by
      obtain ⟨U, hU, I, -, e⟩ := hfl x
      exact ⟨U, hU, I, e⟩
  exact Scheme.Modules.isFlat_of_isLocallyFree G

variable [F.IsFinitePresentation]

/-- The structural morphism of the flattening stratification is quasi-compact: a quasi-compact
open of the base lies inside one Fitting generator open, which only finitely many strata
meet. -/
private theorem quasiCompact_flatnessStratificationHom :
    QuasiCompact (flatnessStratificationHom F) := by
  classical
  refine ⟨fun U hU hK ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_generatorOpen_of_isCompact F hK
  let X := fun r : ℕ ↦ (fittingRankStratum F r).left
  have heq : (flatnessStratificationHom F) ⁻¹' U =
      ⋃ r ∈ Finset.range (n + 1),
        (Sigma.ι X r) '' ((fittingRankStratum F r).hom ⁻¹' U) := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨r, y, rfl⟩ := exists_eq_sigma_ι X x
      have hy : (fittingRankStratum F r).hom y ∈ U := by
        change (flatnessStratificationHom F) ((Sigma.ι X r) y) ∈ U at hx
        simpa only [X, flatnessStratificationHom_ι_apply] using hx
      have hr : r < n + 1 := by
        by_contra hgt
        exact rankStratum_notMem_generatorOpen F (by omega) y (hn hy)
      exact Set.mem_iUnion₂.mpr ⟨r, Finset.mem_range.mpr hr, y, hy, rfl⟩
    · obtain ⟨r, -, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hx
      show flatnessStratificationHom F (Sigma.ι X r y) ∈ U
      rwa [flatnessStratificationHom_ι_apply]
  rw [heq]
  refine Finset.isCompact_biUnion _ fun r _ ↦ ?_
  have : QuasiCompact (fittingRankStratum F r).hom :=
    (finitePresentation_fittingRankStratum F r).2.1
  exact (QuasiCompact.isCompact_preimage U hU hK).image (Sigma.ι X r).continuous

/-- A flat base change of a finitely presented module factors uniquely through the flattening
stratification: the base is covered by the fibres of the fibre rank of the pullback, each of
them maps to the stratum of that rank, and these local factorizations glue because the fibres
are pairwise disjoint. -/
private theorem existsUnique_lift_of_isFlat {T : Scheme.{u}} (g : T ⟶ S)
    (hflat : SheafOfModules.IsFlat (C := TopologicalSpace.Opens T.toTopCat)
      (J := Opens.grothendieckTopology T.toTopCat) (O := T.sheaf)
      ((Scheme.Modules.pullback g).obj F)) :
    ∃! h : T ⟶ flatnessStratification F, h ≫ flatnessStratificationHom F = g := by
  classical
  let G := (Scheme.Modules.pullback g).obj F
  have hGfp : G.IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ g.toLRSHom.toShHom F
      ‹F.IsFinitePresentation›
  have hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := T.ringCatSheaf) G :=
    ((Scheme.Modules.flat_finitePresentation_locallyFree_tfae G).out 1 4).mp (And.intro hflat hGfp)
  have hGlf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} G :=
    Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree G
  let V : ℕ → T.Opens := fun r ↦ ⟨{x | Scheme.Modules.fiberRank G x = r},
    (Scheme.Modules.isLocallyConstant_fiberRank G).isOpen_fiber r⟩
  have hcover : IsOpenCover V := IsOpenCover.mk <| top_unique fun x _ ↦
    (Opens.mem_iSup).mpr ⟨Scheme.Modules.fiberRank G x, rfl⟩
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover V hcover
  let klift : ∀ r : ℕ, Over.mk ((V r).ι ≫ g) ⟶ fittingRankStratum F r := fun r ↦ by
    have hfixed : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback ((V r).ι ≫ g)).obj F) r :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        ((Scheme.Modules.pullbackComp (V r).ι g).app F)
        (Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq G (V r) r
          fun _ hx ↦ hx)
    let a : (rankRFunctor S F r).obj (Opposite.op (Over.mk ((V r).ι ≫ g))) :=
      ULift.up (PLift.up hfixed)
    exact (Classical.choice
      (rankRFunctor_representableBy_fittingRankStratum F r)).homEquiv.symm a
  let hloc : ∀ r : ℕ, (V r : Scheme) ⟶ flatnessStratification F := fun r ↦
    (klift r).left ≫ Sigma.ι (fun j : ℕ ↦ (fittingRankStratum F j).left) r
  have hloc_fac (r : ℕ) : hloc r ≫ flatnessStratificationHom F = (V r).ι ≫ g := by
    change (klift r).left ≫ (Sigma.ι (fun j : ℕ ↦ (fittingRankStratum F j).left) r ≫
      flatnessStratificationHom F) = _
    rw [ι_comp_flatnessStratificationHom]
    exact (klift r).w
  have hcompatible (i j : ℕ) :
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ hloc i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ hloc j := by
    by_cases hij : i = j
    · subst j
      rw [show pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i) from
        (cancel_mono (V i).ι).1 pullback.condition]
    · have hdisj : Disjoint (Set.range (V i).ι) (Set.range (V j).ι) := by
        rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, Set.disjoint_left]
        intro x hxi hxj
        change Scheme.Modules.fiberRank G x = i at hxi
        change Scheme.Modules.fiberRank G x = j at hxj
        exact hij (hxi.symm.trans hxj)
      have : IsEmpty ↑(pullback (𝒰.f i) (𝒰.f j)) := Scheme.isEmpty_pullback_iff.mpr hdisj
      exact (isInitialOfIsEmpty (X := pullback (𝒰.f i) (𝒰.f j))).hom_ext _ _
  have hloc_eq (h' : T ⟶ flatnessStratification F)
      (hh' : h' ≫ flatnessStratificationHom F = g) (r : ℕ) : (V r).ι ≫ h' = hloc r := by
    apply lift_eq_rankStratum_comp_ι F r (klift r).left ((V r).ι ≫ h')
    rw [Category.assoc, hh', (klift r).w]
    rfl
  refine ⟨𝒰.glueMorphisms hloc hcompatible, ?_, fun h' hh' ↦ 𝒰.hom_ext _ _ fun r ↦
    (hloc_eq h' hh' r).trans (𝒰.ι_glueMorphisms hloc hcompatible r).symm⟩
  refine 𝒰.hom_ext _ _ fun r ↦ ?_
  rw [← Category.assoc, 𝒰.ι_glueMorphisms hloc hcompatible r]
  exact hloc_fac r

end Auxiliary

section Tagged

variable {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation]

/-- **Stacks Project, Tag 05P9.** The module restricts to a finite locally free module of rank
`r` on the `r`-th Fitting rank stratum. -/
@[stacks 05P9 "rank on each stratum"]
public theorem rankStratum_isFiniteLocallyFreeOfRank (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback
        (@fittingRankStratum S F (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
          (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) r).hom).obj F) r :=
  @rankStratum_isFiniteLocallyFreeOfRank_aux S F
    (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
    (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) r

/-- **Stacks Project, Tag 05P9.** A pullback of a finitely presented module is flat exactly when
the morphism to the base factors, necessarily uniquely, through the flattening stratification —
the disjoint union of the Fitting rank strata. -/
@[stacks 05P9 "representability"]
public theorem flat_iff_existsUnique_lift {T : Scheme.{u}} (g : T ⟶ S) :
    SheafOfModules.IsFlat (C := TopologicalSpace.Opens T.toTopCat)
        (J := Opens.grothendieckTopology T.toTopCat) (O := T.sheaf)
        ((Scheme.Modules.pullback g).obj F) ↔
      ∃! h : T ⟶ @flatnessStratification S F
          (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
          (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F),
        h ≫ @flatnessStratificationHom S F
          (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
          (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) = g := by
  refine ⟨@existsUnique_lift_of_isFlat S F
      (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F)
      ‹F.IsFinitePresentation› T g, ?_⟩
  rintro ⟨h, hfac, -⟩
  exact @isFlat_pullback_of_lift S F
    (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
    (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) T g h hfac

/-- **Stacks Project, Tag 05P9.** The structural morphism of the flattening stratification is of
finite presentation: it is locally of finite presentation because each stratum is, quasi-compact
because the Fitting generator opens exhaust the base, and quasi-separated because it is
injective. -/
@[stacks 05P9 "finite presentation of the disjoint union"]
public theorem flatnessStratification_finitePresentation :
    FinitePresentation (@flatnessStratificationHom S F
      (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F)) := by
  have hlfp : LocallyOfFinitePresentation (@flatnessStratificationHom S F
      (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F)) := by
    have : IsZariskiLocalAtSource @LocallyOfFinitePresentation :=
      HasRingHomProperty.instIsZariskiLocalAtSource
        (P := @LocallyOfFinitePresentation) (Q := RingHom.FinitePresentation)
    exact IsZariskiLocalAtSource.sigmaDesc fun r ↦
      (finitePresentation_fittingRankStratum F r).locallyOfFinitePresentation
  have hqs : QuasiSeparated (@flatnessStratificationHom S F
      (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F)) := by
    have := isSeparated_of_injective _ (@flatnessStratificationHom_injective_aux S F
      (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F))
    infer_instance
  exact FinitePresentation.mk hlfp
    (@quasiCompact_flatnessStratificationHom S F
      (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F)
      ‹F.IsFinitePresentation›) hqs

add_to_stacks 05P9 "finite presentation of each stratum"
  AlgebraicGeometry.finitePresentation_fittingRankStratum

end Tagged

end AlgebraicGeometry

end
