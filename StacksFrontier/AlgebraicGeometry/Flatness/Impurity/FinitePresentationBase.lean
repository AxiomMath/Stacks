module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Jacobson
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.FibreSeparation.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Jacobson
public import StacksFrontier.Topology.Jacobson.Subspace

/-!
# An impurity over a finitely presented base, at a closed point of the fibre

An impurity of a finite type quasi-coherent module can always be rearranged so that its test
family is locally of finite presentation over the base and its specialized point is closed in the
fibre over the distinguished point.

## Main results

* `AlgebraicGeometry.isAlgebraic_residueFieldMap_of_isOpenImmersion`: an open immersion induces
  an isomorphism, in particular an algebraic extension, on residue fields.
* `AlgebraicGeometry.exists_impurity_locallyOfFinitePresentation_closedPoint`: an impurity can be
  witnessed over a test family locally of finite presentation over the base, with its specialized
  point closed in the fibre over the distinguished point.

## References

* [Stacks Project, Tag 05FX](https://stacks.math.columbia.edu/tag/05FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For an open immersion `f`, the residue field of `X` at `x` is algebraic over the residue field
of `Y` at `f x`. -/
theorem isAlgebraic_residueFieldMap_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.IsIntegral (Y.residueField (f x)) (X.residueField x) :=
    Algebra.isIntegral_of_surjective
      (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.surjective
  infer_instance

/-- If `m` and `t` form a pullback square over `b` and `a`, a point of the relative assassin of
`t` for a module isomorphic to the pullback of `G` along `m` gives, via `isoPullback`, a point of
the relative assassin of `pullback.snd b a` for the pullback of `G` along `pullback.fst b a`. -/
private theorem isoPullback_mem_relativeAssassin {W X S T : Scheme.{u}} {m : W ⟶ X} {t : W ⟶ T}
    {b : X ⟶ S} {a : T ⟶ S} (hSq : IsPullback m t b a) [LocallyOfFiniteType b]
    [LocallyOfFiniteType t] (G : X.Modules) [G.IsQuasicoherent] {E : W.Modules}
    (e : (Scheme.Modules.pullback m).obj G ≅ E) {w : W}
    (hw : w ∈ Stacks.Divisors.relativeAssassin t E) :
    hSq.isoPullback.hom.base w ∈ Stacks.Divisors.relativeAssassin (pullback.snd b a)
      ((Scheme.Modules.pullback (pullback.fst b a)).obj G) := by
  have hfst := hSq.isoPullback_hom_fst
  have hsnd := hSq.isoPullback_hom_snd
  let H := (Scheme.Modules.pullback (pullback.fst b a)).obj G
  let ePull : (Scheme.Modules.pullback m).obj G ≅
      (Scheme.Modules.pullback hSq.isoPullback.hom).obj H :=
    ((Scheme.Modules.pullbackComp hSq.isoPullback.hom (pullback.fst b a)).app G ≪≫
      (Scheme.Modules.pullbackCongr hfst).app G).symm
  let adj := Scheme.Modules.pullbackPushforwardAdjunction hSq.isoPullback.hom
  have : IsIso (adj.unit.app H) := inferInstance
  let ePush : (Scheme.Modules.pushforward hSq.isoPullback.hom).obj
      ((Scheme.Modules.pullback m).obj G) ≅ H :=
    (Scheme.Modules.pushforward hSq.isoPullback.hom).mapIso ePull ≪≫ (asIso (adj.unit.app H)).symm
  have : LocallyOfFiniteType (hSq.isoPullback.hom ≫ pullback.snd b a) := by
    rw [hsnd]
    infer_instance
  rw [← relativeAssassin_eq_of_moduleIso (pullback.snd b a) ePush,
    relativeAssassin_pushforward_eq_image hSq.isoPullback.hom (pullback.snd b a)]
  refine ⟨w, ?_, rfl⟩
  rw [hsnd, relativeAssassin_eq_of_moduleIso t e]
  exact hw

/-- Restricting the test family of an impurity to an open subset of the test scheme containing
the specialized point keeps the chosen point in the relative assassin. The returned point of the
restricted base change is recorded by its images in the full base change, in the source of the
morphism and in the open subset. -/
private theorem exists_mem_relativeAssassin_restrict_open (P : PrePureSituation.{u})
    (D : ImpurityDiagram P) (hD : IsImpurity P D) (V : D.T.Opens) (ht' : D.t' ∈ V) :
    ∃ ξ : ↥(pullback P.f (V.ι ≫ D.g)),
      ξ ∈ Stacks.Divisors.relativeAssassin (pullback.snd P.f (V.ι ≫ D.g))
          ((Scheme.Modules.pullback (pullback.fst P.f (V.ι ≫ D.g))).obj P.F) ∧
        (pullback.lift (pullback.fst P.f (V.ι ≫ D.g))
            (pullback.snd P.f (V.ι ≫ D.g) ≫ V.ι)
            (by simpa [Category.assoc] using
              pullback.condition (f := P.f) (g := V.ι ≫ D.g))).base ξ =
            D.isPullback.isoPullback.hom D.xi ∧
        pullback.fst P.f (V.ι ≫ D.g) ξ =
          pullback.fst P.f D.g (D.isPullback.isoPullback.hom D.xi) ∧
        pullback.snd P.f (V.ι ≫ D.g) ξ = ⟨D.t', ht'⟩ := by
  classical
  have : LocallyOfFiniteType D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  let Fold := D.pulledBack P
  let W := pullback D.toT V.ι
  let r : W ⟶ D.X_T := pullback.fst D.toT V.ι
  let qV : W ⟶ V.toScheme := pullback.snd D.toT V.ι
  let v' : V.toScheme := ⟨D.t', ht'⟩
  have hcompat : D.toT D.xi = V.ι v' := by
    rw [D.xi_liesOver]
    rfl
  obtain ⟨ζ, hζr, hζq⟩ := Scheme.Pullback.exists_preimage_pullback D.xi v' hcompat
  have hζassW : ζ ∈ Stacks.Divisors.relativeAssassin qV
      ((Scheme.Modules.pullback r).obj Fold) := by
    refine preimage_relativeAssassin_eq_pullback_of_isAlgebraic_residueField D.toT V.ι Fold
      (fun y ↦ isAlgebraic_residueFieldMap_of_isOpenImmersion V.ι y) ▸ ?_
    change r ζ ∈ Stacks.Divisors.relativeAssassin (X := D.X_T) (S := D.T) D.toT Fold
    rw [hζr]
    exact hD.1
  let Xv := pullback P.f (V.ι ≫ D.g)
  let b : Xv ⟶ V.toScheme := pullback.snd P.f (V.ι ≫ D.g)
  have hcompX : (r ≫ D.toX) ≫ P.f = qV ≫ (V.ι ≫ D.g) := by
    simp [r, qV, D.isPullback.w, pullback.condition_assoc]
  let xmap : W ⟶ Xv := pullback.lift (r ≫ D.toX) qV hcompX
  let pV : Xv ⟶ pullback P.f D.g :=
    pullback.lift (pullback.fst P.f (V.ι ≫ D.g)) (pullback.snd P.f (V.ι ≫ D.g) ≫ V.ι)
      (by simpa [Category.assoc] using pullback.condition (f := P.f) (g := V.ι ≫ D.g))
  have hmapfst : xmap ≫ pullback.fst P.f (V.ι ≫ D.g) = r ≫ D.toX := pullback.lift_fst _ _ _
  have hmapsnd : xmap ≫ pullback.snd P.f (V.ι ≫ D.g) = qV := pullback.lift_snd _ _ _
  have hpVfst : pV ≫ pullback.fst P.f D.g = pullback.fst P.f (V.ι ≫ D.g) :=
    pullback.lift_fst _ _ _
  have hpVsnd : pV ≫ pullback.snd P.f D.g = pullback.snd P.f (V.ι ≫ D.g) ≫ V.ι :=
    pullback.lift_snd _ _ _
  have hpcomp : xmap ≫ pV = r ≫ D.isPullback.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · simp [hpVfst, hmapfst]
    · simp [hpVsnd, reassoc_of% hmapsnd, r, qV, pullback.condition]
  have houter' : IsPullback (xmap ≫ pullback.fst P.f (V.ι ≫ D.g)) qV P.f (V.ι ≫ D.g) := by
    simpa only [hmapfst] using (IsPullback.of_hasPullback D.toT V.ι).paste_horiz D.isPullback
  have hπ : IsPullback xmap qV b (𝟙 V.toScheme) :=
    IsPullback.of_right houter' hmapsnd (IsPullback.of_hasPullback P.f (V.ι ≫ D.g))
  let G := (Scheme.Modules.pullback (pullback.fst P.f (V.ι ≫ D.g))).obj P.F
  let ePB : W ≅ pullback b (𝟙 V.toScheme) := hπ.isoPullback
  have hfst : ePB.hom ≫ pullback.fst b (𝟙 V.toScheme) = xmap :=
    IsPullback.isoPullback_hom_fst hπ
  let eD : (Scheme.Modules.pullback xmap).obj G ≅ (Scheme.Modules.pullback r).obj Fold :=
    (Scheme.Modules.pullbackComp xmap (pullback.fst P.f (V.ι ≫ D.g))).app P.F ≪≫
      (Scheme.Modules.pullbackCongr hmapfst).app P.F ≪≫
        (Scheme.Modules.pullbackComp r D.toX).symm.app P.F
  have hζpush := isoPullback_mem_relativeAssassin hπ G eD hζassW
  have hpre : ePB.hom.base ζ ∈ (pullback.fst b (𝟙 V.toScheme)) ⁻¹'
      Stacks.Divisors.relativeAssassin b G :=
    (preimage_relativeAssassin_eq_pullback_of_isAlgebraic_residueField b (𝟙 V.toScheme) G
      (fun y ↦ isAlgebraic_residueFieldMap_of_isOpenImmersion (𝟙 V.toScheme) y)).symm ▸ hζpush
  have hpoint : (pullback.fst b (𝟙 V.toScheme)).base (ePB.hom.base ζ) = xmap.base ζ := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : W ⟶ Xv ↦ m ζ) hfst
  refine ⟨xmap.base ζ, by simpa [hpoint, b, G] using hpre, ?_, ?_, ?_⟩
  · have hh := congrArg (fun m : W ⟶ pullback P.f D.g ↦ m ζ) hpcomp
    change pV (xmap ζ) = D.isPullback.isoPullback.hom (r ζ) at hh
    simpa [hζr, pV, r] using hh
  · calc
      pullback.fst P.f (V.ι ≫ D.g) (xmap.base ζ) = (r ≫ D.toX) ζ := by
        rw [← Scheme.Hom.comp_apply, hmapfst]
      _ = D.toX D.xi := by
        change D.toX ((pullback.fst D.toT V.ι) ζ) = D.toX D.xi
        rw [hζr]
      _ = pullback.fst P.f D.g (D.isPullback.isoPullback.hom D.xi) :=
        (congrArg (fun k : D.X_T ⟶ P.X ↦ k D.xi)
          (IsPullback.isoPullback_hom_fst D.isPullback)).symm
  · exact (congrArg (fun m : W ⟶ V.toScheme ↦ m ζ) hmapsnd).trans hζq

/-- The specialized point of an impurity is not in the image of the closure of the chosen point,
once the latter is viewed inside Mathlib's chosen fibre product as a closed subscheme. -/
private lemma notMem_image_support_vanishingIdeal_closure (P : PrePureSituation.{u})
    (D : ImpurityDiagram P) (hD : IsImpurity P D) :
    D.t ∉ Set.image (pullback.snd P.f D.g)
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({D.isPullback.isoPullback.hom D.xi} :
          Set ↑(pullback P.f D.g)))).support.1 := by
  rintro ⟨z, hz, hzt⟩
  have hs : D.isPullback.isoPullback.hom D.xi ⤳ z :=
    specializes_iff_mem_closure.mpr (by
      simpa [Scheme.IdealSheafData.coe_support_vanishingIdeal] using hz)
  have hs' : D.xi ⤳ D.isPullback.isoPullback.inv z := by
    simpa using hs.map D.isPullback.isoPullback.inv.continuous
  have hzbase : D.toT (D.isPullback.isoPullback.inv z) = D.t :=
    (congrArg (fun m : pullback P.f D.g ⟶ D.T ↦ m z) D.isPullback.isoPullback_inv_snd).trans hzt
  have hmeet : D.isPullback.isoPullback.inv z ∈
      closure ({D.xi} : Set D.X_T) ∩ Set.range (D.toT.fiberι D.t) :=
    ⟨specializes_iff_mem_closure.mp hs',
      ⟨(D.toT.fiberHomeo D.t).symm ⟨D.isPullback.isoPullback.inv z, hzbase⟩, by simp⟩⟩
  exact Set.eq_empty_iff_forall_notMem.mp hD.2 _ hmeet

/-- Over a base locally of finite presentation the specialized point of an impurity can be
replaced by a closed point of the fibre over the distinguished point, to which it specializes and
which the closure of the chosen point still avoids. -/
private theorem exists_closedPoint_fiber_specializes_avoiding (P : PrePureSituation.{u})
    (D : ImpurityDiagram P) (hD : IsImpurity P D) [LocallyOfFinitePresentation D.g] :
    ∃ y : D.g.fiber P.s, y ∈ closedPoints (D.g.fiber P.s) ∧
      D.g.fiberι P.s y ∈ closure ({D.t} : Set D.T) ∧
      closure ({D.xi} : Set D.X_T) ∩ Set.range (D.toT.fiberι (D.g.fiberι P.s y)) = ∅ := by
  classical
  let y : D.g.fiber P.s := (D.g.fiberHomeo P.s).symm ⟨D.t, D.mapsToChosenPoint⟩
  have hsupp : ∀ {Z : Scheme.{u}} (s : Set Z)
      (z : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure s)).subscheme),
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure s)).subschemeι z ∈ closure s := by
    intro Z s z
    have hz : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure s)).subschemeι z ∈
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure s)).support : Set Z) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    simpa [Scheme.IdealSheafData.coe_support_vanishingIdeal] using hz
  let J : (D.g.fiber P.s).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set (D.g.fiber P.s)))
  have hsuppJ := hsupp ({y} : Set (D.g.fiber P.s))
  obtain ⟨yJ, hyJ⟩ : y ∈ Set.range J.subschemeι := by
    rw [J.range_subschemeι]
    exact subset_closure (Set.mem_singleton y)
  let I : D.X_T.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({D.xi} : Set D.X_T))
  have hsuppI := hsupp ({D.xi} : Set D.X_T)
  let q := I.subschemeι ≫ D.toT
  let j := J.subschemeι ≫ D.g.fiberι P.s
  let qJ : pullback q j ⟶ J.subscheme := pullback.snd q j
  have hmeetI : ∀ z : I.subscheme, D.toT (I.subschemeι z) ≠ D.t := fun z hzt ↦
    Set.eq_empty_iff_forall_notMem.mp hD.2 _ ⟨hsuppI z,
      (D.toT.fiberHomeo D.t).symm ⟨I.subschemeι z, hzt⟩,
        D.toT.fiberι_fiberHomeo_symm D.t ⟨I.subschemeι z, hzt⟩⟩
  have hη : yJ ∈ genericPoints J.subscheme := by
    have hcl : closure ({yJ} : Set J.subscheme) = Set.univ := by
      rw [J.subschemeι.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, hyJ]
      exact Set.eq_univ_iff_forall.mpr hsuppJ
    have : IrreducibleSpace J.subscheme := by
      rw [irreducibleSpace_def]
      change IsIrreducible (Set.univ : Set J.subscheme)
      rw [← hcl]
      exact isIrreducible_singleton.closure
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff]
    exact ((genericPoint_spec J.subscheme).eq hcl).symm
  have hηnot : yJ ∉ Set.range qJ := by
    rintro ⟨z, hz⟩
    refine hmeetI (pullback.fst q j z) ?_
    have hzbase : q (pullback.fst q j z) = j yJ :=
      (congrArg (fun m : pullback q j ⟶ D.T ↦ m z) pullback.condition).trans (congrArg j hz)
    change D.toT (I.subschemeι (pullback.fst q j z)) =
      D.g.fiberι P.s (J.subschemeι yJ) at hzbase
    rw [hyJ] at hzbase
    simpa [y, Scheme.Hom.fiberι_fiberHomeo_symm] using hzbase
  have : QuasiCompact D.toT := MorphismProperty.of_isPullback D.isPullback inferInstance
  have : QuasiCompact q := inferInstance
  obtain ⟨U, hηU, hU⟩ := exists_open_nhds_disjoint_range_of_quasiCompact qJ yJ hη hηnot
  have : JacobsonSpace J.subscheme :=
    JacobsonSpace.of_isClosedEmbedding J.subschemeι.isClosedEmbedding
  obtain ⟨y', hy'⟩ :=
    (jacobsonSpace_iff_locallyClosed.mp inferInstance) U ⟨yJ, hηU⟩ U.2.isLocallyClosed
  refine ⟨J.subschemeι y', ?_, ?_, ?_⟩
  · change y' ∈ J.subschemeι ⁻¹' closedPoints (D.g.fiber P.s)
    simpa only [J.subschemeι.isClosedEmbedding.preimage_closedPoints] using hy'.2
  · have hs := (specializes_iff_mem_closure.mpr (hsuppJ y')).map (D.g.fiberι P.s).continuous
    simpa [y, Scheme.Hom.fiberι_fiberHomeo_symm] using specializes_iff_mem_closure.mp hs
  · refine Set.eq_empty_iff_forall_notMem.mpr fun z hz ↦ ?_
    obtain ⟨hzcl, w, hw⟩ := hz
    obtain ⟨zI, hzI⟩ : z ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hzcl
    have hbase : q zI = j y' := by
      change D.toT (I.subschemeι zI) = D.g.fiberι P.s (J.subschemeι y')
      rw [hzI]
      calc
        D.toT z = D.toT (D.toT.fiberι _ w) := congrArg D.toT hw.symm
        _ = D.g.fiberι P.s (J.subschemeι y') := D.toT.apply_fiberι _ w
    obtain ⟨zJ, hzJ⟩ := (Scheme.Pullback.Triplet.mk' zI y' hbase).exists_preimage
    have hzU : zJ ∈ qJ ⁻¹ᵁ U := by
      change qJ zJ ∈ U
      rw [hzJ.2]
      exact hy'.1
    simp_all

/-- Over a base locally of finite presentation an impurity can be refined to one whose
specialized point is closed in the fibre over the distinguished point. -/
private theorem exists_isImpurity_closedPoint_of_locallyOfFinitePresentation
    (P : PrePureSituation.{u}) (D : ImpurityDiagram P) (hD : IsImpurity P D)
    [LocallyOfFinitePresentation D.g] :
    ∃ D' : ImpurityDiagram P, IsImpurity P D' ∧ LocallyOfFinitePresentation D'.g ∧
      ∃ y : D'.g.fiber P.s,
        D'.g.fiberι P.s y = D'.t ∧ y ∈ closedPoints (D'.g.fiber P.s) := by
  obtain ⟨y, hyClosed, hySpecializes, hyAvoids⟩ :=
    exists_closedPoint_fiber_specializes_avoiding P D hD
  refine ⟨{ D with
      t := D.g.fiberι P.s y
      specializes := D.specializes.trans (specializes_iff_mem_closure.mpr hySpecializes)
      mapsToChosenPoint := D.g.apply_fiberι P.s y }, ⟨hD.1, hyAvoids⟩, inferInstance, y, rfl,
    hyClosed⟩

/-- An impurity can be witnessed over a test family which is
locally of finite presentation over the base, with its specialized point closed in the fibre over
the distinguished point. -/
@[stacks 05FX]
theorem exists_impurity_locallyOfFinitePresentation_closedPoint (P : PrePureSituation.{u})
    (h : ∃ D : ImpurityDiagram P, IsImpurity P D) :
    ∃ D : ImpurityDiagram P, IsImpurity P D ∧ LocallyOfFinitePresentation D.g ∧
      ∃ t_fib : D.g.fiber P.s,
        D.g.fiberι P.s t_fib = D.t ∧ t_fib ∈ closedPoints (D.g.fiber P.s) := by
  obtain ⟨D, hD⟩ := h
  let x₀ : ↑(pullback P.f D.g) := D.isPullback.isoPullback.hom D.xi
  let I : (pullback P.f D.g).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x₀} : Set ↑(pullback P.f D.g)))
  obtain ⟨V, htV, T', hT'affine, b, hbLfp, a, hcomp, I', p, q,
      hpFst, hpSnd, hqFst, hqSnd, hAvoid, hI⟩ :=
    exists_affine_locallyFinitePresentation_separation P.f D.g D.t I
      (notMem_image_support_vanishingIdeal_closure P D hD)
  have htV' : D.t' ∈ V.1 := D.specializes.mem_open V.1.isOpen htV
  let v : V.1.toScheme := ⟨D.t, htV⟩
  let v' : V.1.toScheme := ⟨D.t', htV'⟩
  let gV := V.1.ι ≫ D.g
  obtain ⟨xv, hxvAss, hxvRestr, hxvFst, hxvSnd⟩ :=
    exists_mem_relativeAssassin_restrict_open P D hD V.1 htV'
  have hpEq : p = pullback.lift (pullback.fst P.f gV) (pullback.snd P.f gV ≫ V.1.ι)
      (by simpa [gV, Category.assoc] using pullback.condition (f := P.f) (g := gV)) :=
    pullback.hom_ext (hpFst.trans (pullback.lift_fst _ _ _).symm)
      (hpSnd.trans (pullback.lift_snd _ _ _).symm)
  have hpxv : p.base xv = x₀ := by simpa [hpEq] using hxvRestr
  let m : pullback P.f gV ⟶ pullback P.f b :=
    pullback.lift (pullback.fst P.f gV) (pullback.snd P.f gV ≫ a)
      (by rw [Category.assoc, ← hcomp]; exact pullback.condition)
  have hmFst : m ≫ pullback.fst P.f b = pullback.fst P.f gV := pullback.lift_fst _ _ _
  have hmSnd : m ≫ pullback.snd P.f b = pullback.snd P.f gV ≫ a := pullback.lift_snd _ _ _
  have hqEq : q = m := by
    refine pullback.hom_ext ?_ ?_
    · rw [hmFst]; exact hqFst
    · rw [hmSnd]; exact hqSnd
  have hxi'Ass : m.base xv ∈ Stacks.Divisors.relativeAssassin (pullback.snd P.f b)
      ((Scheme.Modules.pullback (pullback.fst P.f b)).obj P.F) := by
    have houter : IsPullback (m ≫ pullback.fst P.f b) (pullback.snd P.f gV) P.f (a ≫ b) := by
      simpa only [hmFst, ← hcomp] using IsPullback.of_hasPullback P.f gV
    have hSq : IsPullback m (pullback.snd P.f gV) (pullback.snd P.f b) a :=
      IsPullback.of_right houter hmSnd (IsPullback.of_hasPullback P.f b)
    let ePB : pullback P.f gV ≅ pullback (pullback.snd P.f b) a := hSq.isoPullback
    have hefst : ePB.hom ≫ pullback.fst (pullback.snd P.f b) a = m :=
      IsPullback.isoPullback_hom_fst hSq
    let G := (Scheme.Modules.pullback (pullback.fst P.f b)).obj P.F
    let eMod : (Scheme.Modules.pullback m).obj G ≅
        (Scheme.Modules.pullback (pullback.fst P.f gV)).obj P.F :=
      (Scheme.Modules.pullbackComp m (pullback.fst P.f b)).app P.F ≪≫
        (Scheme.Modules.pullbackCongr hmFst).app P.F
    have hDC := (mem_relativeAssassin_pullback_iff (pullback.snd P.f b) a G
      (ePB.hom.base xv)).mp (isoPullback_mem_relativeAssassin hSq G eMod hxvAss)
    have hpoint : (pullback.fst (pullback.snd P.f b) a).base (ePB.hom.base xv) = m.base xv := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun k : pullback P.f gV ⟶ pullback P.f b ↦ k xv) hefst
    simpa only [G, hpoint] using hDC.1
  have hclosureSupport : closure ({m.base xv} : Set ↑(pullback P.f b)) ⊆ I'.support.1 := by
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) I'.support.2
    have hxI : xv ∈ (I.comap p).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change p.base xv ∈ I.support.1
      rw [hpxv]
      change x₀ ∈ closure ({x₀} : Set ↑(pullback P.f D.g))
      exact subset_closure (Set.mem_singleton x₀)
    have hsupp := Scheme.IdealSheafData.support_antitone hI hxI
    rw [Scheme.IdealSheafData.support_comap] at hsupp
    change q.base xv ∈ I'.support.1 at hsupp
    exact hqEq ▸ hsupp
  have hAvoidNew : closure ({m.base xv} : Set ↑(pullback P.f b)) ∩
      Set.range ((pullback.snd P.f b).fiberι (a v)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz ↦ ?_
    obtain ⟨hzcl, w, rfl⟩ := hz
    exact hAvoid ⟨(pullback.snd P.f b).fiberι (a v) w, hclosureSupport hzcl,
      (pullback.snd P.f b).apply_fiberι (a v) w⟩
  have hbaseNew : b (a v) = P.s := calc
      b (a v) = D.g (V.1.ι v) := by
        simpa using (congrArg (fun k : V.1.toScheme ⟶ P.S ↦ k v) hcomp).symm
      _ = P.s := by simpa [v] using D.mapsToChosenPoint
  let D' : ImpurityDiagram P :=
    { T := T'
      g := b
      t' := a v'
      t := a v
      specializes := ((subtype_specializes_iff v' v).2 D.specializes).map a.continuous
      mapsToChosenPoint := hbaseNew
      X_T := pullback P.f b
      toX := pullback.fst P.f b
      toT := pullback.snd P.f b
      isPullback := IsPullback.of_hasPullback P.f b
      xi := m.base xv
      xi_liesOver :=
        (congrArg (fun k : pullback P.f gV ⟶ T' ↦ k.base xv) hmSnd).trans (congrArg (a ·) hxvSnd) }
  exact exists_isImpurity_closedPoint_of_locallyOfFinitePresentation P D'
    ⟨hxi'Ass, hAvoidNew⟩

end AlgebraicGeometry

end
