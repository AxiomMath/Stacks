module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.ImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic compatibility of the scheme-theoretic image with base change

Over a reduced Noetherian base `T`, a morphism `f : X ⟶ Y` of schemes of finite presentation
over `T` becomes compatible with arbitrary base change after shrinking `T` to a nonempty open
subscheme. This is the generic step of the proof of [Stacks, Tag 0H41]; the stratification of the
lemma is obtained from it by Noetherian induction.

The argument follows the Stacks text. Over an integral affine base with affine source and target
the question is the algebraic one of Stacks 0H40: after inverting one nonzero element of the base
ring, the target algebra and the cokernel of the algebra map become flat, and then the kernel
ideal commutes with base change. An affine cover of the source is handled by replacing the source
with the disjoint union of the cover, which has the same scheme-theoretic image; an affine cover
of the target is handled one piece at a time, and the finitely many good opens of the base are
intersected. Finally a reduced Noetherian base contains a nonempty integral affine open, which
reduces the general case to the integral affine one.

## Main results

* `Stacks.GenericFlatness.exists_good_open_of_isAffine`: the integral affine case with affine
  source and target.
* `Stacks.GenericFlatness.exists_good_open_of_isAffine_target`: the integral affine case with
  affine target and quasi-compact source.
* `Stacks.GenericFlatness.overPullbackOpenCover`: the base change of an open cover of the target.
* `Stacks.GenericFlatness.exists_good_open_of_isIntegral`: the integral affine case.
* `Stacks.GenericFlatness.exists_good_open_of_isReduced`: the reduced Noetherian case.

## References

* [Stacks Project, Tag 0H41](https://stacks.math.columbia.edu/tag/0H41)
* [Stacks Project, Tag 0H40](https://stacks.math.columbia.edu/tag/0H40)
* [Stacks Project, Tag 051T](https://stacks.math.columbia.edu/tag/051T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.GenericFlatness

/-! ### Finite presentation and base change -/

/-- Finite presentation over the base is stable under base change. -/
@[sga "3 III 0.13" "partial"]
theorem finitePresentation_pullback {S T : Scheme.{u}} (g : T ⟶ S)
    (X : Over S) (hX : FinitePresentation X.hom) :
    FinitePresentation ((Over.pullback g).obj X).hom := by
  obtain ⟨hlfp, hqc, hqs⟩ := hX
  change LocallyOfFinitePresentation (pullback.snd X.hom g) ∧
    QuasiCompact (pullback.snd X.hom g) ∧ QuasiSeparated (pullback.snd X.hom g)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-! ### The integral affine case -/

/-- The two ways around a pullback square agree on global sections of the base. -/
private theorem appTop_fst_apply_eq_appTop_snd_apply {X Y S : Scheme.{u}} (p : X ⟶ S)
    (q : Y ⟶ S) (r : Γ(S, ⊤)) :
    (pullback.fst p q).appTop.hom (p.appTop.hom r) =
      (pullback.snd p q).appTop.hom (q.appTop.hom r) := by
  have hw := congrArg (fun h : pullback p q ⟶ S ↦ h.appTop.hom r) pullback.condition
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using hw

/-- Over a standard open of an affine base, the global sections of the base change of an affine
scheme are a localization of its global sections. -/
theorem isLocalizedModule_appTop_pullback_basicOpen
    {T Z : Scheme.{u}} [IsAffine T] [IsAffine Z]
    (p : Z ⟶ T) (h : Γ(T, ⊤)) :
    let U := T.basicOpen h
    letI : Algebra Γ(T, ⊤) Γ(Z, ⊤) := p.appTop.hom.toAlgebra
    letI : Algebra Γ(Z, ⊤) Γ(pullback p U.ι, ⊤) :=
      (pullback.fst p U.ι).appTop.hom.toAlgebra
    letI : Algebra Γ(T, ⊤) Γ(pullback p U.ι, ⊤) :=
      ((pullback.fst p U.ι).appTop.hom.comp p.appTop.hom).toAlgebra
    letI : IsScalarTower Γ(T, ⊤) Γ(Z, ⊤) Γ(pullback p U.ι, ⊤) :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    IsLocalizedModule (Submonoid.powers h)
      (IsScalarTower.toAlgHom Γ(T, ⊤) Γ(Z, ⊤) Γ(pullback p U.ι, ⊤)).toLinearMap := by
  let U := T.basicOpen h
  let ZU := pullback p U.ι
  let P := Γ(U.toScheme, ⊤)
  let B := Γ(Z, ⊤)
  let B' := Γ(ZU, ⊤)
  let _ : Algebra Γ(T, ⊤) P := U.ι.appTop.hom.toAlgebra
  let _ : Algebra Γ(T, ⊤) B := p.appTop.hom.toAlgebra
  let _ : Algebra B B' := (pullback.fst p U.ι).appTop.hom.toAlgebra
  let _ : Algebra P B' := (pullback.snd p U.ι).appTop.hom.toAlgebra
  let _ : Algebra Γ(T, ⊤) B' :=
    ((pullback.fst p U.ι).appTop.hom.comp p.appTop.hom).toAlgebra
  have : IsScalarTower Γ(T, ⊤) B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(T, ⊤) P B' :=
    IsScalarTower.of_algebraMap_eq (appTop_fst_apply_eq_appTop_snd_apply p U.ι)
  have : IsLocalization.Away h P := by
    change IsLocalization.Away h Γ(T.basicOpen h, ⊤)
    infer_instance
  have hs : IsPushout (CommRingCat.ofHom (algebraMap Γ(T, ⊤) B))
      (CommRingCat.ofHom (algebraMap Γ(T, ⊤) P))
      (CommRingCat.ofHom (algebraMap B B'))
      (CommRingCat.ofHom (algebraMap P B')) :=
    isPushout_appTop_of_isPullback (IsPullback.of_hasPullback p U.ι)
  exact isLocalizedModule_of_isPushout_away h hs

/-- **The integral affine case of the generic step of Stacks 0H41.** For a morphism of affine
schemes of finite type over an integral Noetherian affine base, formation of the scheme-theoretic
image commutes with arbitrary base change after restricting the base to a suitable nonempty
standard open. -/
theorem exists_good_open_of_isAffine
    {T : Scheme.{u}} [IsNoetherian T] [IsIntegral T] [IsAffine T]
    (X Y : Over T) [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    (hX : X.hom.appTop.hom.FiniteType)
    (hY : Y.hom.appTop.hom.FiniteType) :
    ∃ U : T.Opens, Nonempty U ∧
      ImageCommutesWithBaseChange ((Over.pullback U.ι).map f) := by
  let R := Γ(T, ⊤)
  let A := Γ(Y.left, ⊤)
  let B := Γ(X.left, ⊤)
  let _ : Algebra R A := Y.hom.appTop.hom.toAlgebra
  let _ : Algebra R B := X.hom.appTop.hom.toAlgebra
  let _ : Algebra A B := f.left.appTop.hom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r ↦ by
    have hw := congrArg (fun q : X.left ⟶ T ↦ q.appTop.hom r) f.w
    change X.hom.appTop.hom r = f.left.appTop.hom (Y.hom.appTop.hom r)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using hw.symm
  have : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  have : Nonempty (⊤ : T.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have : IsDomain R := IsIntegral.component_integral ⊤
  let _ : Algebra.FiniteType R A := hY
  let _ : Algebra.FiniteType R B := hX
  let _ : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType R A B
  obtain ⟨h, hh, hB, hC⟩ :=
    exists_flat_localizedModule_target_and_coker (R := R) (A := A) (B := B)
  let U := T.basicOpen h
  refine ⟨U, ?_, ?_⟩
  · have hn : U ≠ ⊥ := fun he ↦ hh ((basicOpen_eq_bot_iff h).mp he)
    by_contra hnone
    exact hn ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot U).mp fun ⟨x, hx⟩ ↦
      hnone ⟨⟨x, hx⟩⟩)
  · let XU := (Over.pullback U.ι).obj X
    let YU := (Over.pullback U.ι).obj Y
    let fU := (Over.pullback U.ι).map f
    have : IsAffine U.toScheme := inferInstance
    have : IsAffine XU.left := inferInstanceAs (IsAffine (pullback X.hom U.ι))
    have : IsAffine YU.left := inferInstanceAs (IsAffine (pullback Y.hom U.ι))
    let P := Γ(U.toScheme, ⊤)
    let A' := Γ(YU.left, ⊤)
    let B' := Γ(XU.left, ⊤)
    let _ : Algebra R P := U.ι.appTop.hom.toAlgebra
    let _ : Algebra A A' := (pullback.fst Y.hom U.ι).appTop.hom.toAlgebra
    let _ : Algebra B B' := (pullback.fst X.hom U.ι).appTop.hom.toAlgebra
    let _ : Algebra P A' := YU.hom.appTop.hom.toAlgebra
    let _ : Algebra P B' := XU.hom.appTop.hom.toAlgebra
    let _ : Algebra R A' :=
      ((pullback.fst Y.hom U.ι).appTop.hom.comp Y.hom.appTop.hom).toAlgebra
    let _ : Algebra R B' :=
      ((pullback.fst X.hom U.ι).appTop.hom.comp X.hom.appTop.hom).toAlgebra
    have : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : IsLocalization.Away h P := by
      change IsLocalization.Away h Γ(T.basicOpen h, ⊤)
      infer_instance
    let mA : A →ₗ[R] A' := (IsScalarTower.toAlgHom R A A').toLinearMap
    let mB : B →ₗ[R] B' := (IsScalarTower.toAlgHom R B B').toLinearMap
    have hmA : IsLocalizedModule (Submonoid.powers h) mA :=
      isLocalizedModule_appTop_pullback_basicOpen Y.hom h
    have hmB : IsLocalizedModule (Submonoid.powers h) mB :=
      isLocalizedModule_appTop_pullback_basicOpen X.hom h
    have : IsScalarTower R P A' :=
      IsScalarTower.of_algebraMap_eq (appTop_fst_apply_eq_appTop_snd_apply Y.hom U.ι)
    have : IsScalarTower R P B' :=
      IsScalarTower.of_algebraMap_eq (appTop_fst_apply_eq_appTop_snd_apply X.hom U.ι)
    let _ : Algebra A' B' := fU.left.appTop.hom.toAlgebra
    have : IsScalarTower P A' B' := IsScalarTower.of_algebraMap_eq fun r ↦ by
      have hw := congrArg (fun q : XU.left ⟶ U.toScheme ↦ q.appTop.hom r) fU.w
      simpa only [XU, YU, RingHom.algebraMap_toAlgebra, Over.pullback_obj_hom,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
        RingHom.comp_apply] using hw.symm
    let φ' : A' →ₐ[P] B' := IsScalarTower.toAlgHom P A' B'
    have hw : φ'.toLinearMap.restrictScalars R ∘ₗ mA =
        mB ∘ₗ (Algebra.linearMap A B).restrictScalars R := by
      ext a
      have hs := congrArg (fun q : XU.left ⟶ Y.left ↦ q.appTop.hom a)
        (isPullback_overPullback_map f U.ι).w
      simpa only [φ', mA, mB, IsScalarTower.toAlgHom_apply, Algebra.linearMap_apply,
        LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        LinearMap.restrictScalars_apply, RingHom.algebraMap_toAlgebra,
        Over.pullback_obj_hom, Scheme.Hom.comp_appTop,
        CommRingCat.hom_comp, RingHom.comp_apply] using hs
    have : Module.Flat P B' := flat_of_isLocalizedModule_away mB hB
    have : Module.Flat P (B' ⧸ LinearMap.range φ'.toLinearMap) :=
      flat_quotient_of_isLocalizedModule_square (R := R) (P := P) (f := h)
        (M := A) (N := B) (M' := A') (N' := B') mA mB
        ((Algebra.linearMap A B).restrictScalars R) φ'.toLinearMap hw hC
    intro T'' g
    exact (imageCommutesWithBaseChange_of_flat_appTop
      (T := U.toScheme) XU YU fU rfl rfl φ' rfl) g

/-! ### Covers of the source and of the target -/

/-- A quasi-compact scheme over `T` admits a morphism from an affine scheme over `T`, locally of
finite type, which has sections over an affine open cover. -/
theorem exists_affine_source_cover {T : Scheme.{u}} (X : Over T) [CompactSpace X.left] :
    ∃ (Z : Over T) (p : Z ⟶ X) (𝒰 : Scheme.OpenCover.{u, u} X.left),
      IsAffine Z.left ∧ LocallyOfFiniteType p.left ∧ (∀ i, IsAffine (𝒰.X i)) ∧
        ∃ l : ∀ i, 𝒰.X i ⟶ Z.left, ∀ i, l i ≫ p.left = 𝒰.f i := by
  let 𝒰 := X.left.affineCover.finiteSubcover
  let q : (∐ fun i : 𝒰.I₀ ↦ 𝒰.X i) ⟶ X.left := Sigma.desc 𝒰.f
  refine ⟨Over.mk (q ≫ X.hom), Over.homMk q, 𝒰, ?_, ?_, fun i ↦ inferInstance,
    fun i ↦ Sigma.ι _ i, fun i ↦ Sigma.ι_comp_desc _ _⟩
  · change IsAffine (∐ fun i : 𝒰.I₀ ↦ 𝒰.X i)
    infer_instance
  · change LocallyOfFiniteType (Sigma.desc 𝒰.f)
    let _ : IsZariskiLocalAtSource @LocallyOfFiniteType :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
    exact IsZariskiLocalAtSource.sigmaDesc
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ LocallyOfFiniteType f)
      (fun i ↦ inferInstance)

/-- The integral affine case with affine target and merely quasi-compact source: replace the
source by the disjoint union of an affine cover, which has the same scheme-theoretic image. -/
theorem exists_good_open_of_isAffine_target
    {T : Scheme.{u}} [IsNoetherian T] [IsIntegral T] [IsAffine T]
    (X Y : Over T) [IsAffine Y.left] (f : X ⟶ Y)
    [CompactSpace X.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    ∃ U : T.Opens, Nonempty U ∧
      ImageCommutesWithBaseChange ((Over.pullback U.ι).map f) := by
  obtain ⟨Z, p, 𝒰, _, _, _, l, hl⟩ := exists_affine_source_cover X
  have : LocallyOfFiniteType Z.hom := by
    rw [← p.w]
    infer_instance
  obtain ⟨U, hUne, hf⟩ := exists_good_open_of_isAffine Z Y (p ≫ f)
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) Z.hom inferInstance)
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) Y.hom inferInstance)
  exact ⟨U, hUne,
    imageCommutesWithBaseChange_of_openCover_lifts_pullback p f 𝒰 l hl U.ι hf⟩

/-- The base changes of a cover of the target of a morphism over `T` form a cover of the target
of the base changed morphism. -/
noncomputable def overPullbackOpenCover {T T' : Scheme.{u}}
    (Y : Over T) (𝒰 : Y.left.OpenCover) (g : T' ⟶ T) :
    (((Over.pullback g).obj Y).left).OpenCover := by
  let Yi (i : 𝒰.I₀) : Over T := Over.mk (𝒰.f i ≫ Y.hom)
  let bi (i : 𝒰.I₀) : Yi i ⟶ Y := Over.homMk (𝒰.f i)
  let 𝒱 := 𝒰.pullback₁ (pullback.fst Y.hom g)
  let e (i : 𝒰.I₀) : 𝒱.X i ≅ ((Over.pullback g).obj (Yi i)).left :=
    pullbackSymmetry (pullback.fst Y.hom g) (𝒰.f i) ≪≫
      pullbackRightPullbackFstIso Y.hom g (𝒰.f i)
  have hbfst (i : 𝒰.I₀) : ((Over.pullback g).map (bi i)).left ≫ pullback.fst Y.hom g =
      pullback.fst (𝒰.f i ≫ Y.hom) g ≫ 𝒰.f i := overPullback_map_left_fst g (bi i)
  have hbsnd (i : 𝒰.I₀) : ((Over.pullback g).map (bi i)).left ≫ pullback.snd Y.hom g =
      pullback.snd (𝒰.f i ≫ Y.hom) g := overPullback_map_left_snd g (bi i)
  have hei (i : 𝒰.I₀) : (e i).hom =
      (pullbackSymmetry (pullback.fst Y.hom g) (𝒰.f i)).hom ≫
        (pullbackRightPullbackFstIso Y.hom g (𝒰.f i)).hom := rfl
  have he (i : 𝒰.I₀) :
      (e i).hom ≫ ((Over.pullback g).map (bi i)).left = 𝒱.f i := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hbfst, hei,
        pullbackRightPullbackFstIso_hom_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc,
        𝒱, Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
      exact pullback.condition.symm
    · simp only [Category.assoc, hbsnd, hei,
        pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
        𝒱, Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  refine { I₀ := 𝒰.I₀
           X := fun i ↦ ((Over.pullback g).obj (Yi i)).left
           f := fun i ↦ ((Over.pullback g).map (bi i)).left
           mem₀ := ?_ }
  rw [Scheme.presieve₀_mem_precoverage_iff]
  constructor
  · intro y
    obtain ⟨i, ⟨z, hz⟩⟩ := Set.mem_iUnion.mp
      (show y ∈ ⋃ i, Set.range (𝒱.f i) by rw [Scheme.Cover.iUnion_range 𝒱]; trivial)
    refine ⟨i, (e i).hom z, ?_⟩
    have hzi := congrArg (fun q : 𝒱.X i ⟶ ((Over.pullback g).obj Y).left ↦ q z) (he i)
    simpa only [Scheme.Hom.comp_apply] using hzi.trans hz
  · intro i
    change IsOpenImmersion ((Over.pullback g).map (bi i)).left
    have : IsOpenImmersion (bi i).left := 𝒰.map_prop i
    exact MorphismProperty.of_isPullback (isPullback_overPullback_map (bi i) g).flip
      inferInstance

/-- Finitely many nonempty opens of an irreducible space can be shrunk to a single nonempty open
on which all the given monotone conditions hold. -/
theorem exists_nonempty_open_forall_of_finite
    {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    {ι : Type*} [Finite ι] (P : ι → Opens T → Prop)
    (hmono : ∀ i {U V}, V ≤ U → P i U → P i V)
    (hP : ∀ i, ∃ U : Opens T, Nonempty U ∧ P i U) :
    ∃ U : Opens T, Nonempty U ∧ ∀ i, P i U := by
  classical
  let _ := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, ∃ U : Opens T, Nonempty U ∧ ∀ i ∈ s, P i U by
    simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨⊤, ⟨⟨Classical.choice (inferInstance : Nonempty T), trivial⟩⟩, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨U, hUne, hU⟩ := hP i
    obtain ⟨V, hVne, hV⟩ := ih
    have hUV : Nonempty (U ⊓ V : Opens T) := by
      obtain ⟨x, hx⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen
        (Set.nonempty_coe_sort.mp hUne) (Set.nonempty_coe_sort.mp hVne)
      exact ⟨⟨x, hx⟩⟩
    refine ⟨U ⊓ V, hUV, fun j hj ↦ ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hmono _ inf_le_left hU
    · exact hmono _ inf_le_right (hV _ hj)

/-- **The integral affine case of the generic step of Stacks 0H41.** Over an integral Noetherian
affine base, a morphism between schemes of finite presentation becomes compatible with arbitrary
base change after restricting the base to a nonempty open subscheme.

The target is covered by finitely many affine opens; over each the previous case applies, and the
finitely many resulting good opens of the irreducible base meet in a nonempty one. That the
kernel ideal sheaves glue is the statement that an ideal sheaf is determined by its inverse
images along an open cover. -/
theorem exists_good_open_of_isIntegral
    (T : Scheme.{u}) [IsNoetherian T] [IsIntegral T] [IsAffine T]
    (X Y : Over T) (f : X ⟶ Y)
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    ∃ U : T.Opens, Nonempty U ∧
      ImageCommutesWithBaseChange ((Over.pullback U.ι).map f) := by
  have : QuasiSeparated Y.hom := hY.2.2
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiCompact Y.hom := hY.2.1
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiCompact f.left := quasiCompact_of_compactSpace f.left
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : LocallyOfFinitePresentation Y.hom := hY.1
  let 𝒰 := Y.left.affineCover.finiteSubcover
  let Yi (i : 𝒰.I₀) : Over T := Over.mk (𝒰.f i ≫ Y.hom)
  let Xi (i : 𝒰.I₀) : Over T := Over.mk (pullback.fst f.left (𝒰.f i) ≫ X.hom)
  let fi (i : 𝒰.I₀) : Xi i ⟶ Yi i :=
    Over.homMk (pullback.snd f.left (𝒰.f i)) (by
      simp only [Xi, Yi, Over.mk_hom]
      rw [← Category.assoc, ← pullback.condition, Category.assoc, f.w])
  let ai (i : 𝒰.I₀) : Xi i ⟶ X := Over.homMk (pullback.fst f.left (𝒰.f i))
  let bi (i : 𝒰.I₀) : Yi i ⟶ Y := Over.homMk (𝒰.f i)
  have hpb (i : 𝒰.I₀) : IsPullback (fi i).left (ai i).left (bi i).left f.left :=
    (IsPullback.of_hasPullback f.left (𝒰.f i)).flip
  have hgood (i : 𝒰.I₀) : ∃ U : T.Opens, Nonempty U ∧
      ImageCommutesWithBaseChange ((Over.pullback U.ι).map (fi i)) := by
    have : IsAffine (Yi i).left := by
      change IsAffine (𝒰.X i)
      infer_instance
    have : CompactSpace (Xi i).left := by
      have : QuasiCompact (pullback.snd f.left (𝒰.f i)) :=
        quasiCompact_isStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback f.left (𝒰.f i)) inferInstance
      exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd f.left (𝒰.f i))
    have : LocallyOfFiniteType (Yi i).hom := by
      change LocallyOfFiniteType (𝒰.f i ≫ Y.hom)
      have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    have : LocallyOfFiniteType (Xi i).hom := by
      change LocallyOfFiniteType (pullback.fst f.left (𝒰.f i) ≫ X.hom)
      have : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    exact exists_good_open_of_isAffine_target (Xi i) (Yi i) (fi i)
  have hmono : ∀ (i : 𝒰.I₀) {U V : T.Opens}, V ≤ U →
      ImageCommutesWithBaseChange ((Over.pullback U.ι).map (fi i)) →
      ImageCommutesWithBaseChange ((Over.pullback V.ι).map (fi i)) := by
    intro i U V hVU hfU
    have h : ImageCommutesWithBaseChange
        ((Over.pullback (T.homOfLE hVU ≫ U.ι)).map (fi i)) :=
      imageCommutesWithBaseChange_comp U.ι (T.homOfLE hVU) hfU
    intro T'' g
    have hval := h (T' := T'') g
    rw [T.homOfLE_ι hVU] at hval
    exact hval
  obtain ⟨U, hUne, hU⟩ : ∃ U : T.Opens, Nonempty U ∧
      ∀ i, ImageCommutesWithBaseChange ((Over.pullback U.ι).map (fi i)) :=
    exists_nonempty_open_forall_of_finite
      (P := fun i (V : T.Opens) ↦
        ImageCommutesWithBaseChange ((Over.pullback (Scheme.Opens.ι V)).map (fi i)))
      hmono hgood
  refine ⟨U, hUne, ?_⟩
  let X0 := (Over.pullback U.ι).obj X
  let Y0 := (Over.pullback U.ι).obj Y
  let f0 := (Over.pullback U.ι).map f
  let Yi0 (i : 𝒰.I₀) := (Over.pullback U.ι).obj (Yi i)
  let fi0 (i : 𝒰.I₀) := (Over.pullback U.ι).map (fi i)
  let ai0 (i : 𝒰.I₀) := (Over.pullback U.ι).map (ai i)
  let bi0 (i : 𝒰.I₀) := (Over.pullback U.ι).map (bi i)
  let 𝒞 := overPullbackOpenCover Y 𝒰 U.ι
  have hCf (i : 𝒰.I₀) : 𝒞.f i = (bi0 i).left := rfl
  change ImageCommutesWithBaseChange f0
  intro T' g
  let f1 := (Over.pullback g).map f0
  let Yi1 (i : 𝒰.I₀) := (Over.pullback g).obj (Yi0 i)
  let fi1 (i : 𝒰.I₀) := (Over.pullback g).map (fi0 i)
  let ai1 (i : 𝒰.I₀) := (Over.pullback g).map (ai0 i)
  let bi1 (i : 𝒰.I₀) := (Over.pullback g).map (bi0 i)
  have : QuasiCompact f0.left :=
    quasiCompact_isStableUnderBaseChange.of_isPullback
      (isPullback_overPullback_map f U.ι).flip inferInstance
  have : QuasiCompact f1.left :=
    quasiCompact_isStableUnderBaseChange.of_isPullback
      (isPullback_overPullback_map f0 g).flip inferInstance
  have hlocal (i : 𝒰.I₀) :
      f1.left.ker.comap (bi1 i).left =
        (f0.left.ker.comap (pullback.fst Y0.hom g)).comap (bi1 i).left := by
    have hoi : IsOpenImmersion (bi i).left := by
      change IsOpenImmersion (𝒰.f i)
      exact 𝒰.map_prop i
    have : IsOpenImmersion (bi0 i).left :=
      MorphismProperty.of_isPullback (isPullback_overPullback_map (bi i) U.ι).flip inferInstance
    have : IsOpenImmersion (bi1 i).left :=
      MorphismProperty.of_isPullback (isPullback_overPullback_map (bi0 i) g).flip inferInstance
    have hp0 : IsPullback (fi0 i).left (ai0 i).left (bi0 i).left f0.left :=
      isPullback_overPullback_map_of_isPullback f (fi i) (ai i) (bi i) (hpb i) U.ι
    have hp1 : IsPullback (fi1 i).left (ai1 i).left (bi1 i).left f1.left :=
      isPullback_overPullback_map_of_isPullback f0 (fi0 i) (ai0 i) (bi0 i) hp0 g
    have hk0 : (fi0 i).left.ker = f0.left.ker.comap (bi0 i).left :=
      ker_eq_comap_of_isPullback_of_isOpenImmersion f0.left (fi0 i).left (ai0 i).left
        (bi0 i).left hp0
    have hk1 : (fi1 i).left.ker = f1.left.ker.comap (bi1 i).left :=
      ker_eq_comap_of_isPullback_of_isOpenImmersion f1.left (fi1 i).left (ai1 i).left
        (bi1 i).left hp1
    calc
      _ = (fi1 i).left.ker := hk1.symm
      _ = (fi0 i).left.ker.comap (pullback.fst (Yi0 i).hom g) := hU i g
      _ = (f0.left.ker.comap (bi0 i).left).comap (pullback.fst (Yi0 i).hom g) := by rw [hk0]
      _ = f0.left.ker.comap ((bi1 i).left ≫ pullback.fst Y0.hom g) := by
        rw [← Scheme.IdealSheafData.comap_comp,
          (isPullback_overPullback_map (bi0 i) g).w]
      _ = _ := by rw [← Scheme.IdealSheafData.comap_comp]
  let 𝒟 := overPullbackOpenCover Y0 𝒞 g
  let Ci (i : 𝒰.I₀) : Over (Scheme.Opens.toScheme U) := Over.mk (𝒞.f i ≫ Y0.hom)
  let ci (i : 𝒰.I₀) : Ci i ⟶ Y0 := Over.homMk (𝒞.f i)
  let di (i : 𝒰.I₀) : Ci i ≅ Yi0 i :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 (Yi0 i).left ≫ (Yi0 i).hom = 𝒞.f i ≫ Y0.hom
      rw [Category.id_comp, hCf i]
      exact (bi0 i).w.symm)
  let e (i : 𝒰.I₀) : 𝒟.X i ≅ (Yi1 i).left :=
    (Over.forget _).mapIso ((Over.pullback g).mapIso (di i))
  have he (i : 𝒰.I₀) : (e i).hom ≫ (bi1 i).left = 𝒟.f i := by
    have hdi : (di i).hom ≫ bi0 i = ci i := by
      apply Over.OverMorphism.ext
      change (di i).hom.left ≫ (bi0 i).left = 𝒞.f i
      rw [hCf i]
      change (𝟙 (Yi0 i).left) ≫ (bi0 i).left = (bi0 i).left
      simp
    have hmap := congrArg (fun q : Ci i ⟶ Y0 ↦ ((Over.pullback g).map q).left) hdi
    simpa only [Functor.map_comp, Over.comp_left, Functor.mapIso_hom, Over.forget_map,
      e, bi1, 𝒟, overPullbackOpenCover, ci] using hmap
  change f1.left.ker = f0.left.ker.comap (pullback.fst Y0.hom g)
  apply idealSheafData_eq_of_comap_eq_openCover 𝒟
  intro i
  have hi := congrArg
    (fun K : (Yi1 i).left.IdealSheafData ↦ K.comap (e i).hom) (hlocal i)
  simpa only [← Scheme.IdealSheafData.comap_comp, ← Category.assoc, he i] using hi

/-! ### The reduced Noetherian case -/

/-- A nonempty reduced Noetherian scheme has a nonempty integral affine open subscheme. -/
theorem exists_nonempty_integral_affine_open (T : Scheme.{u})
    [IsNoetherian T] [IsReduced T] [Nonempty T] :
    ∃ U : T.Opens, IsAffineOpen U ∧ Nonempty U ∧ IsIntegral U.toScheme := by
  classical
  let x : T := Classical.choice inferInstance
  obtain ⟨V, hV, ⟨y, hy⟩, hVC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hy hV
  change T.Opens at U
  have hUirr : IsIrreducible (U : Set T) :=
    ⟨⟨y, hyU⟩, isIrreducible_irreducibleComponent.2.open_subset U.isOpen (hUV.trans hVC)⟩
  have : IrreducibleSpace U.toScheme := isIrreducible_iff_irreducibleSpace.mp hUirr
  exact ⟨U, hU, ⟨⟨y, hyU⟩⟩, isIntegral_of_irreducibleSpace_of_isReduced U.toScheme⟩

/-- **The generic step of Stacks 0H41.** Over a nonempty reduced Noetherian base, a morphism
between schemes of finite presentation becomes compatible with arbitrary base change after
restricting the base to a nonempty open subscheme. -/
theorem exists_good_open_of_isReduced
    (T : Scheme.{u}) [IsNoetherian T] [IsReduced T] [Nonempty T]
    (X Y : Over T) (f : X ⟶ Y)
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom) :
    ∃ U : T.Opens, Nonempty U ∧
      ImageCommutesWithBaseChange ((Over.pullback U.ι).map f) := by
  obtain ⟨V, hV, hVne, hVint⟩ := exists_nonempty_integral_affine_open T
  have : IsAffine V.toScheme := hV
  have : IsNoetherian V.toScheme := ⟨⟩
  obtain ⟨U, hUne, hU⟩ := exists_good_open_of_isIntegral V.toScheme
    ((Over.pullback V.ι).obj X) ((Over.pullback V.ι).obj Y)
    ((Over.pullback V.ι).map f)
    (finitePresentation_pullback V.ι X hX) (finitePresentation_pullback V.ι Y hY)
  let W : T.Opens := V.ι ''ᵁ U
  have hw : Nonempty W := by
    obtain ⟨x⟩ := hUne
    exact ⟨⟨V.ι x.1, x.1, x.2, rfl⟩⟩
  have hp : ImageCommutesWithBaseChange ((Over.pullback (U.ι ≫ V.ι)).map f) :=
    imageCommutesWithBaseChange_of_isIso
      ((Over.pullbackComp U.ι V.ι).app X) ((Over.pullbackComp U.ι V.ι).app Y)
      ((Over.pullbackComp U.ι V.ι).hom.naturality f) hU
  have hrange : Set.range (U.ι ≫ V.ι).base = Set.range W.ι.base := by
    ext x
    simp only [W, Scheme.Hom.comp_apply, Set.mem_range, Scheme.Opens.range_ι]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let e : U.toScheme ≅ W.toScheme := IsOpenImmersion.isoOfRangeEq (U.ι ≫ V.ι) W.ι hrange
  have hie : e.inv ≫ U.ι ≫ V.ι = W.ι := by
    rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (U.ι ≫ V.ι) W.ι hrange, Iso.inv_hom_id_assoc]
  refine ⟨W, hw, ?_⟩
  rw [← hie]
  exact imageCommutesWithBaseChange_comp (U.ι ≫ V.ι) e.inv hp

end Stacks.GenericFlatness

end
