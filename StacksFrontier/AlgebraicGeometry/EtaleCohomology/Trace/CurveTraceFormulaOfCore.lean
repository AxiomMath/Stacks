module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceCoreComplex
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.FiniteReducedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointsDegreeOne

/-!
# The trace formula on a curve from its core

Let `k` be a finite field, `k̄` an algebraically closed extension, `Λ` a finite ring with `#Λ`
invertible in `k`, and `X` a separated scheme of finite type over `k` with a compactification
`j : X ⟶ X̄`. Suppose given finitely many pairwise disjoint opens `Z i` of `X`, each an integral
affine smooth curve over `k` without `k`-rational points, whose complement in `X` is a finite set
of closed points, and a sheaf `F` of `Λ`-modules on `X_étale` with perfect stalks which is locally
constant with finite projective values on (every open subscheme of) each `Z i`. Then
`Stacks.EtaleCohomology.CurveTraceCore` implies the trace formula of [Stacks, Tag 03UG] for `F`:
`RΓ_c(X_k̄, F)` is perfect and

`Tr(π_X^* | RΓ_c(X_k̄, F)) = ∑_{x ∈ X(k)} Tr(π_x | F_x̄)`.

This is the dévissage of Steps 1 to 3 of the source. With `U = ⋃ Z i` and `W = X̄ ∖ U` (reduced
induced structure), Step 1 on `X̄` splits `T''(X̄, j_! F)` into `T''(U, F|_U)`, which vanishes by
the core on each `Z i` (the passage to the pieces is
`Stacks.EtaleCohomology.compactSupportTraceVanishes_of_partition`), and `T''(W, (j_! F)|_W)`.
The latter complex vanishes off the finite set `X ∖ U` of closed points, so Step 2 computes it
(`Stacks.EtaleCohomology.cohomologicalTraceFormula_of_isZero_restriction`). On the local side
`U(k) = ∅`, and the rational points of `X̄` off `X` do not see `j_! F`.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`)
are defined there.

## Main results

All names below are in the namespace `Stacks.EtaleCohomology`.

* `cohomologicalTraceFormula_of_isZero_off_finite`: the trace formula on a proper `k`-scheme for a
  complex vanishing off a finite set of closed points.
* `cohomologicalTraceFormula_extensionByZero_of_curveTraceCore`: the trace formula
  `T''(X̄, j_! F) = T'(X̄, j_! F)` from the core.
* `perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_curveTraceCore`: the trace
  formula `T''(X, F) = T'(X, F)` from the core.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 1 to 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

/-- The image of a closed point under an open immersion into a scheme locally of finite type over
a field is closed: it is locally closed, and the target is a Jacobson space. -/
theorem isClosed_singleton_image_of_isOpenImmersion {k : Type u} [Field k] {X Y : Scheme.{u}}
    (e : X ⟶ Y) [IsOpenImmersion e] (fY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType fY] (x : X)
    (hx : IsClosed ({x} : Set X)) : IsClosed ({e x} : Set Y) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace fY
  refine isClosed_singleton_of_isLocallyClosed_singleton ?_
  have he := e.isOpenEmbedding
  refine ⟨Set.range e, closure {e x}, he.isOpen_range, isClosed_closure, ?_⟩
  ext y
  constructor
  · rintro rfl
    exact ⟨⟨x, rfl⟩, subset_closure rfl⟩
  · rintro ⟨⟨z, rfl⟩, hz⟩
    have hz' : z ∈ closure ({x} : Set X) := by
      rwa [he.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
    rw [hx.closure_eq] at hz'
    rw [hz']
    rfl

section Standard

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- **The trace formula for a complex supported on finitely many closed points.** Let `W` be
proper over `k`, `T` a finite set of closed points of `W`, and `G` a complex with perfect stalks
whose restriction to every open subscheme missing `T` vanishes. Then `T''(W, G) = T'(W, G)`: the
reduced induced structure on `T` is finite étale over `k`, so
`Stacks.EtaleCohomology.cohomologicalTraceFormula_of_isZero_restriction` applies. -/
theorem cohomologicalTraceFormula_of_isZero_off_finite (W : Over (Spec (.of k))) [IsProper W.hom]
    (T : Set W.left) (hT : T.Finite) (hTc : ∀ t ∈ T, IsClosed ({t} : Set W.left))
    (G : CochainComplex.Plus (EtaleModules.{u, 0} Λ W.left)) (hG : HasPerfectStalks Λ G)
    (hz : ∀ (V : Scheme.{u}) (o : V ⟶ W.left) [IsOpenImmersion o], Disjoint (Set.range o) T →
      ∀ n, IsZero ((etaleModuleRestriction.{u, 0} Λ o).obj (G.obj.X n))) :
    CohomologicalTraceFormula Λ kbar p q hcard W G hG := by
  have hTcl : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    exact hT.isClosed_biUnion hTc
  let TC : TopologicalSpace.Closeds W.left := ⟨T, hTcl⟩
  let ι0 := (Scheme.IdealSheafData.vanishingIdeal TC).subschemeι
  have hrange : Set.range ι0 = T := Scheme.IdealSheafData.range_subschemeι_vanishingIdeal TC
  let Z0 : Over (Spec (.of k)) := Over.mk (ι0 ≫ W.hom)
  let i : Z0 ⟶ W := Over.homMk ι0 rfl
  have : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion ι0)
  have : Finite (Scheme.IdealSheafData.vanishingIdeal TC).subscheme := by
    have := hT.to_subtype
    rw [← hrange] at this
    exact Finite.of_injective_finite_range ι0.isClosedEmbedding.injective
  have : IsFinite (ι0 ≫ W.hom) := by
    have : LocallyOfFiniteType ι0 := AlgebraicGeometry.instLocallyOfFiniteTypeOfIsClosedImmersion ι0
    have : LocallyOfFiniteType W.hom := IsProper.toLocallyOfFiniteType
    have : LocallyOfFiniteType (ι0 ≫ W.hom) := locallyOfFiniteType_comp ι0 W.hom
    have : LocallyQuasiFinite (ι0 ≫ W.hom) :=
      (locallyQuasiFinite_iff_finite_preimage_singleton).2 fun _ => Set.toFinite _
    exact IsFinite.of_isProper_of_locallyQuasiFinite _
  have : Etale (ι0 ≫ W.hom) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced (ι0 ≫ W.hom)
  have : IsFinite Z0.hom := inferInstanceAs (IsFinite (ι0 ≫ W.hom))
  have : Etale Z0.hom := inferInstanceAs (Etale (ι0 ≫ W.hom))
  let O : W.left.Opens := ⟨Tᶜ, hTcl.isOpen_compl⟩
  have hij : Set.range O.ι = (Set.range i.left)ᶜ := by
    rw [Scheme.Opens.range_ι]
    change Tᶜ = (Set.range ι0)ᶜ
    rw [hrange]
  refine cohomologicalTraceFormula_of_isZero_restriction Λ kbar p q hcard i O.ι hij G hG
    (hz _ O.ι ?_)
  rw [Scheme.Opens.range_ι]
  exact disjoint_compl_left

/-- `j^{-1} j_! K ≅ K` for an open immersion `j`, degreewise on a bounded below complex. -/
def restrictionExtensionByZeroPlusIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    (etaleModuleRestriction.{u, 0} Λ j).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j).mapCochainComplexPlus.obj K) ≅ K :=
  ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
    (fun n => ((asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit).app (K.obj.X n)).symm)
    (fun _ _ _ => ((asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit).inv.naturality _).symm))

variable [Finite Λ]

/-- **The trace formula `T''(X̄, j_! K) = T'(X̄, j_! K)` for a bounded complex, from the core of
Tag 03UG.** Here `j : X ⟶ X̄` is a compactification of the separated `k`-scheme `X` of finite
type, `Z i` are finitely many pairwise disjoint opens of `X`, each an integral affine smooth curve
without `k`-rational points, with finite complement consisting of closed points, and `K` is a
complex concentrated in degrees `[a, a + N]` with perfect stalks whose terms are locally constant
with finite projective values on every open subscheme of each `Z i`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_bounded
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f]
    (J : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hFs : HasPerfectStalks Λ K) (a : ℤ) (N : ℕ) (hlo : ∀ n, n < a → IsZero (K.obj.X n))
    (hhi : ∀ n, a + N < n → IsZero (K.obj.X n)) {ι : Type*} [Finite ι] (Z : ι → X.Opens)
    (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    [∀ i, IsIntegral (Z i)] [∀ i, IsAffine (Z i)] (hdim : ∀ i, topologicalKrullDim (Z i) = 1)
    [∀ i, Smooth ((Z i).ι ≫ f)] (hrat : ∀ i, IsEmpty (rationalPoints ((Z i).ι ≫ f)))
    (hloc : ∀ i n, a ≤ n → n ≤ a + N → ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e],
      Set.range e.base ⊆ Z i → Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        V.smallEtaleTopology ((etaleModuleRestriction.{u, 0} Λ e).obj (K.obj.X n)))
    (hT : (⋃ i, (Z i : Set X))ᶜ.Finite)
    (hTc : ∀ x ∈ (⋃ i, (Z i : Set X))ᶜ, IsClosed ({x} : Set X)) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion _ hFs) := by
  classical
  have := Fintype.ofFinite ι
  let Y : Over (Spec (.of k)) := Over.mk J.toBase
  let D := (etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K
  have hD : HasPerfectStalks Λ D := hasPerfectStalks_extensionByZero Λ J.immersion _ hFs
  have hJf : J.immersion ≫ J.toBase = f := Over.w J.obj.hom
  -- the finite set of closed points `X ∖ U`, in `X̄`
  let Tc : Set X := (⋃ i, (Z i : Set X))ᶜ
  have hTcX : ∀ x ∈ Tc, IsClosed ({J.immersion x} : Set J.space) := fun x hx =>
    isClosed_singleton_image_of_isOpenImmersion J.immersion J.toBase x (hTc x hx)
  -- the residual part: a complex on a proper scheme vanishing off finitely many closed points
  have hresidual : ∀ (Wo : Over (Spec (.of k))) [IsProper Wo.hom] (iW : Wo.left ⟶ Y.left)
      [IsClosedImmersion iW], Set.range iW ∩ Set.range J.immersion ⊆ J.immersion '' Tc →
      CohomologicalTraceFormula Λ kbar p q hcard Wo
        ((etaleModuleInverseImage.{u, 0} Λ iW).mapCochainComplexPlus.obj D)
        (isPerfect_stalk_inverseImage Λ iW D hD) := by
    intro Wo _ iW _ hW
    refine cohomologicalTraceFormula_of_isZero_off_finite Λ kbar p q hcard Wo
      (iW ⁻¹' (J.immersion '' Tc)) ((hT.image _).preimage iW.isClosedEmbedding.injective.injOn)
      (fun t ht => ?_) _ _ (fun V o _ ho n => ?_)
    · obtain ⟨x, hx, hxt⟩ := ht
      have : ({t} : Set Wo.left) = iW ⁻¹' {J.immersion x} := by
        ext t'
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro rfl
          exact hxt.symm
        · exact fun h => iW.isClosedEmbedding.injective (h.trans hxt)
      rw [this]
      exact (hTcX x hx).preimage iW.continuous
    · refine IsZero.of_iso ?_ ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ o).symm.app _)
      refine IsZero.of_iso ?_ ((etaleModuleInverseImageCompIso.{u, 0} Λ o iW).symm.app _)
      refine isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ (o ≫ iW) J.immersion ?_ _
      rw [Set.disjoint_left]
      rintro _ ⟨v, rfl⟩ hvJ
      obtain ⟨x, hx, hxv⟩ := hW ⟨⟨o v, rfl⟩, hvJ⟩
      exact Set.disjoint_left.1 ho ⟨v, rfl⟩ ⟨x, hx, hxv.trans rfl⟩
  by_cases hι : Nonempty ι
  · -- the good open `U = ⋃ Z i` and its closed complement `W` in `X̄`
    let U : X.Opens := ⟨⋃ i, (Z i : Set X), isOpen_iUnion fun i => (Z i).isOpen⟩
    let jU : U.toScheme ⟶ Y.left := U.ι ≫ J.immersion
    have hjU : Set.range jU = J.immersion '' (U : Set X) := by
      simp only [jU, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      rfl
    let WC : TopologicalSpace.Closeds Y.left :=
      ⟨(Set.range jU)ᶜ, jU.isOpenEmbedding.isOpen_range.isClosed_compl⟩
    let iW := (Scheme.IdealSheafData.vanishingIdeal WC).subschemeι
    have hiW : Set.range iW = (Set.range jU)ᶜ :=
      Scheme.IdealSheafData.range_subschemeι_vanishingIdeal WC
    let Wo : Over (Spec (.of k)) := Over.mk (iW ≫ J.toBase)
    have : IsProper Wo.hom := inferInstanceAs (IsProper (iW ≫ J.toBase))
    let iO : Wo ⟶ Y := Over.homMk iW rfl
    have : IsClosedImmersion iO.left := inferInstanceAs (IsClosedImmersion iW)
    have hij : Set.range jU = (Set.range iO.left)ᶜ := by
      change Set.range jU = (Set.range iW)ᶜ
      rw [hiW, compl_compl]
    refine cohomologicalTraceFormula_of_openClosed Λ kbar p q hcard iO jU hij D hD ?_ ?_
    · -- the open part: the core on the pieces, and no rational points on `U`
      have hK' := hasPerfectStalks_restriction Λ U.ι K hFs
      have hUrat : IsEmpty (rationalPoints (jU ≫ Y.hom)) := by
        refine ⟨fun x => ?_⟩
        have hx2 : x.1 ≫ U.ι ≫ J.immersion ≫ J.toBase = 𝟙 _ := by
          simpa [jU, Y, Category.assoc] using x.2
        have hy : (x.1 ≫ U.ι).base default ∈ Set.range U.ι := ⟨_, rfl⟩
        rw [Scheme.Opens.range_ι] at hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
        rw [← Scheme.Opens.range_ι] at hi
        obtain ⟨z, hz⟩ := hi
        obtain ⟨g, hg⟩ := exists_lift_of_isPreimmersion (Z i).ι (x.1 ≫ U.ι) z hz
        exact (hrat i).false ⟨g, by rw [← hJf, ← Category.assoc, hg, Category.assoc]; exact hx2⟩
      have hV : CompactSupportTraceVanishes Λ kbar p q hcard (U.ι ≫ f) (J.restrictOpen U.ι)
          ((etaleModuleRestriction.{u, 0} Λ U.ι).mapCochainComplexPlus.obj K) :=
        compactSupportTraceVanishes_of_partition f Z hdisj K
          (fun V e _ i he g hg J' =>
            compactSupportTraceVanishes_of_curveTraceCore_of_bounded hcore f (Z i) (hdim i)
              (hrat i) K a N hlo hhi (hloc i) V e he g hg J')
          Finset.univ Finset.univ_nonempty U.toScheme U.ι
          (by rw [Scheme.Opens.range_ι]; ext x; simp [U]) (U.ι ≫ f) rfl (J.restrictOpen U.ι)
      obtain ⟨hp, ht⟩ := hV
      have hFTF : CohomologicalTraceFormula Λ kbar p q hcard Y
          ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj
            ((etaleModuleRestriction.{u, 0} Λ U.ι).mapCochainComplexPlus.obj K))
          (hasPerfectStalks_extensionByZero Λ jU _ hK') :=
        ⟨hp, fun {_} => ht.trans
          (sum_perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero_eq_zero Λ jU kbar
            p q hcard _ (hasPerfectStalks_extensionByZero Λ jU _ hK')).symm⟩
      refine cohomologicalTraceFormula_of_iso Λ kbar p q hcard
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.mapIso
          ((etaleModuleRestriction.{u, 0} Λ U.ι).mapCochainComplexPlus.mapIso
            (restrictionExtensionByZeroPlusIso Λ J.immersion K).symm ≪≫
          (restrictionCompPlusIso U.ι J.immersion D).symm)) _ _ hFTF
    · exact hresidual Wo iW (by
        rintro _ ⟨⟨w, rfl⟩, ⟨x, hx⟩⟩
        refine ⟨x, fun hxU => ?_, hx⟩
        have h1 : iW w ∈ Set.range iW := ⟨w, rfl⟩
        rw [hiW] at h1
        exact h1 (by rw [← hx, hjU]; exact ⟨x, hxU, rfl⟩))
  · -- no piece: `X` is a finite set of closed points
    have hTu : Tc = Set.univ :=
      Set.eq_univ_of_forall fun x hx => hι (Set.mem_iUnion.1 hx).nonempty
    have : IsProper Y.hom := inferInstanceAs (IsProper J.toBase)
    have h := hresidual Y (𝟙 _) (by rw [hTu, Set.image_univ]; exact Set.inter_subset_right)
    refine cohomologicalTraceFormula_of_iso Λ kbar p q hcard
      (ObjectProperty.isoMk _ (HomologicalComplex.Hom.isoOfComponents
        (fun n => (etaleModuleInverseImageIdIso Λ Y.left).app (D.obj.X n))
        (fun _ _ _ => ((etaleModuleInverseImageIdIso Λ Y.left).hom.naturality _).symm))) _ _ h

/-- **The trace formula `T''(X̄, j_! F) = T'(X̄, j_! F)` from the core of Tag 03UG.** Here
`j : X ⟶ X̄` is a compactification of the separated `k`-scheme `X` of finite type, `Z i` are
finitely many pairwise disjoint opens of `X`, each an integral affine smooth curve without
`k`-rational points, with finite complement consisting of closed points, and `F` has perfect stalks
and is locally constant with finite projective values on every open subscheme of each `Z i`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f]
    (J : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, 0} Λ X)
    (hFs : HasPerfectStalks Λ
      ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
    {ι : Type*} [Finite ι] (Z : ι → X.Opens) (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    [∀ i, IsIntegral (Z i)] [∀ i, IsAffine (Z i)] (hdim : ∀ i, topologicalKrullDim (Z i) = 1)
    [∀ i, Smooth ((Z i).ι ≫ f)] (hrat : ∀ i, IsEmpty (rationalPoints ((Z i).ι ≫ f)))
    (hloc : ∀ i (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e], Set.range e.base ⊆ Z i →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ V.smallEtaleTopology
        ((etaleModuleRestriction.{u, 0} Λ e).obj F))
    (hT : (⋃ i, (Z i : Set X))ᶜ.Finite)
    (hTc : ∀ x ∈ (⋃ i, (Z i : Set X))ᶜ, IsClosed ({x} : Set X)) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
      (hasPerfectStalks_extensionByZero Λ J.immersion _ hFs) :=
  cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_bounded Λ kbar p q hcard hcore f J
    _ hFs 0 0 (fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
    (fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)) Z hdisj hdim hrat
    (fun i n hn hn' V e _ he => by
      obtain rfl : n = 0 := by omega
      exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
        ((etaleModuleRestriction.{u, 0} Λ e).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm) (hloc i V e he))
    hT hTc

omit [Finite Λ] in
/-- **From `X̄` to `X`.** For a compactification `j : X ⟶ X̄`, the trace formula
`T''(X̄, j_! K) = T'(X̄, j_! K)` is the trace formula of [Stacks, Tag 03UG] for `K` on `X`:
`RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` by definition, and the rational points of `X̄` off
`X` do not see `j_! K`. -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_cohomologicalTraceFormula
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (J : CompactificationOf (Over.mk f))
    [Fintype (rationalPoints f)] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : HasPerfectStalks Λ K)
    (h : CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion K hK)) :
    ∃ hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar K)),
      perfectDerivedTrace Λ ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard K)) =
        ∑ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hK (rationalGeometricPoint kbar x.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1 K)) := by
  obtain ⟨hp, ht⟩ := h
  have := finite_rationalPoints J.toBase
  have : Fintype (rationalPoints (Over.mk J.toBase).hom) :=
    Fintype.ofFinite (rationalPoints J.toBase)
  exact ⟨hp, ht.trans (sum_perfectDerivedTrace_rationalPointStalkFrobenius_extensionByZero Λ
    (f := f) (Y := Over.mk J.toBase) J.immersion (Over.w J.obj.hom) kbar p q hcard K hK
    (hasPerfectStalks_extensionByZero Λ J.immersion K hK))⟩

/-- **The trace formula of [Stacks, Tag 03UG] on a curve, from its core.** Under the hypotheses of
`Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_curveTraceCore`,
`RΓ_c(X_k̄, F)` is perfect and `Tr(π_X^* | RΓ_c(X_k̄, F)) = ∑_{x ∈ X(k)} Tr(π_x | F_x̄)`. -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_curveTraceCore
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsSeparated f] [Fintype (rationalPoints f)]
    (J : CompactificationOf (Over.mk f)) (F : EtaleModules.{u, 0} Λ X)
    (hFs : HasPerfectStalks Λ
      ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
    {ι : Type*} [Finite ι] (Z : ι → X.Opens) (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    [∀ i, IsIntegral (Z i)] [∀ i, IsAffine (Z i)] (hdim : ∀ i, topologicalKrullDim (Z i) = 1)
    [∀ i, Smooth ((Z i).ι ≫ f)] (hrat : ∀ i, IsEmpty (rationalPoints ((Z i).ι ≫ f)))
    (hloc : ∀ i (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e], Set.range e.base ⊆ Z i →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ V.smallEtaleTopology
        ((etaleModuleRestriction.{u, 0} Λ e).obj F))
    (hT : (⋃ i, (Z i : Set X))ᶜ.Finite)
    (hTc : ∀ x ∈ (⋃ i, (Z i : Set X))ᶜ, IsClosed ({x} : Set X)) :
    ∃ hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f J kbar
          ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)),
      perfectDerivedTrace Λ ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ f J kbar p q hcard
            ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)) =
        ∑ x : rationalPoints f, perfectDerivedTrace Λ ⟨_, hFs (rationalGeometricPoint kbar x.1)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard x.1
            ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)) :=
  perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_cohomologicalTraceFormula Λ kbar
    p q hcard f J _ hFs (cohomologicalTraceFormula_extensionByZero_of_curveTraceCore Λ kbar p q
      hcard hcore f J F hFs Z hdisj hdim hrat hloc hT hTc)

end Standard

end Stacks.EtaleCohomology

end
