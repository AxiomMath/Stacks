module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.NodalSingularitiesCharacterization
public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingTwistWithSection
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Open.OverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Strict
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnit
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Twisting an invertible sheaf on a base-changed curve to prescribed low cohomology

Let `k` be a separably closed field, `X` a smooth projective curve over `k`, `K/k` a field
extension and `𝓛` an invertible sheaf on `X_K`. Stacks Tag 0B9Y says there is an invertible
sheaf `𝓛₀` on `X` with `dim_K H⁰(X_K, 𝓛 ⊗ 𝓛₀|_{X_K}) = 1` and `H¹(X_K, 𝓛 ⊗ 𝓛₀|_{X_K}) = 0`.

The descending induction of the source is
`AlgebraicGeometry.exists_hasPrescribedLowCohomology_one`; it consumes two inputs,
`AlgebraicGeometry.AmpleTwistStart` and `AlgebraicGeometry.PointIdealTwistStep`. This file proves
both, and so Tag 0B9Y for an arbitrary pullback square. The fibre-product form, on Picard
classes, is in `StacksFrontier/AlgebraicGeometry/Curves/PrescribedLowCohomologyFieldExtension.lean`.

## Main results

* `AlgebraicGeometry.ampleTwistStart`: for `X` a proper curve over any field and any invertible
  `𝓛` on `X_K`, a power of an ample invertible sheaf on `X` twists `𝓛` to vanishing `H¹` and a
  nonzero `H⁰`.
* `AlgebraicGeometry.exists_isClosed_bijective_residueField_of_isSepClosed`: rational closed
  points are dense on a smooth scheme over a separably closed field.
* `AlgebraicGeometry.pointIdealTwistStep`: one step of the descending induction, twisting by the
  ideal sheaf of a `k`-rational point whose fibre point a chosen section does not vanish at.
* `AlgebraicGeometry.exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed`:
  Stacks Tag 0B9Y, for every base-change square.

## References

* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0383](https://stacks.math.columbia.edu/tag/0383)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction MonoidalCategory

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

universe u

namespace AlgebraicGeometry

/-! ### A nonzero invertible module has a nonzero global section once it is globally generated -/

/-- **A globally generated invertible module on a nonempty scheme has a nonzero global section.**
If every generating section vanished, the epimorphism from the free module they define would be
zero, so the module would be zero; but an invertible module is locally isomorphic to the
structure sheaf, whose sections over a nonempty open are a nonzero ring. -/
theorem exists_ne_zero_of_generatingSections {X : Scheme.{u}} [Nonempty X] (M : X.Modules)
    (hMinv : Stacks.Ample.IsInvertibleModule X M) (σ : M.GeneratingSections) :
    ∃ i, (σ.s i).eval (op ⊤) ≠ 0 := by
  by_contra! h
  -- every generating section is the image of itself under the zero endomorphism
  have hs : σ.s = fun i => SheafOfModules.sectionsMap (0 : M ⟶ M) (σ.s i) := by
    funext i
    ext V
    change (σ.s i).val V = 0
    rw [← PresheafOfModules.sections_property (σ.s i) (homOfLE (le_top (a := V.unop))).op]
    change M.val.map _ ((σ.s i).eval (op ⊤)) = 0
    rw [h i, map_zero]
  have hzero : M.freeHomEquiv.symm σ.s ≫ 𝟙 M = M.freeHomEquiv.symm σ.s ≫ (0 : M ⟶ M) :=
    calc M.freeHomEquiv.symm σ.s ≫ 𝟙 M = M.freeHomEquiv.symm σ.s := Category.comp_id _
      _ = M.freeHomEquiv.symm (fun i => SheafOfModules.sectionsMap (0 : M ⟶ M) (σ.s i)) :=
          congrArg _ hs
      _ = M.freeHomEquiv.symm σ.s ≫ (0 : M ⟶ M) :=
          (SheafOfModules.freeHomEquiv_symm_comp σ.s (0 : M ⟶ M)).symm
  have hM : IsZero M := by
    exact (IsZero.iff_id_eq_zero M).2 (σ.epi.left_cancellation _ _ hzero)
  -- an invertible module is locally the structure sheaf, whose sections near a point are nonzero
  have := hMinv
  obtain ⟨V, hV, htriv⟩ := Stacks.SheafRankOne.exists_cover_trivialization_of_isInvertible
    (X := X.toRingedSpace) X.ringCatSheaf.2 M
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, hxy⟩ : ∃ y, x ∈ V y := by
    have hx : x ∈ (⨆ y, V y) := by rw [hV]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨t⟩ := htriv y
  have hsub : Subsingleton (M.val.obj (op (V y))) :=
    ModuleCat.subsingleton_of_isZero
      ((SheafOfModules.evaluation X.ringCatSheaf (op (V y))).map_isZero hM)
  have hsubO : Subsingleton (X.presheaf.obj (op (V y))) :=
    (t.θ (V y) (𝟙 _)).toEquiv.symm.subsingleton
  have hnt : Nontrivial (X.presheaf.obj (op (V y))) := by
    have := (X.presheaf.germ (V y) x hxy).hom.domain_nontrivial
    exact this
  exact (not_subsingleton _) hsubO

/-! ### The start of the induction -/

/-- **The start of the induction of Stacks Tag 0B9Y.** Let `X` be a proper curve over a field
`k`, `X_K` its base change to a field extension, and `L` an invertible sheaf on `X_K`. A power
`A^{⊗ n}` of an ample invertible sheaf `A` on `X` ([Stacks, Tag 09ND]) twists `L` to a sheaf
with vanishing `H¹` and nonzero, finite dimensional, `H⁰`: the pullback of `A` to `X_K` is ample
because `X_K ⟶ X` is affine, its high twists of the coherent `L` lose their higher cohomology
([Stacks, Tag 0B5T]) and become globally generated ([Stacks, Tag 01Q3]), and the pullback of
`A^{⊗ n}` is the `n`-th power of the pullback of `A` ([Stacks, Tag 01CD]). -/
theorem ampleTwistStart (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X)
    (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsProper f] [IsCurve k f] (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] :
    AmpleTwistStart K f' p L := by
  have hN : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have hS : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  obtain ⟨A, hAinv, hAamp⟩ := Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X
    (IsCurve.topologicalKrullDim_eq_one (k := k) f)
  have hA : Stacks.Ample.IsInvertibleModule X A := hAinv
  -- the base change `X_K ⟶ X` is affine, and `X_K` is proper over `K`
  have hpaff : IsAffineHom p :=
    MorphismProperty.of_isPullback hp.flip (inferInstance : IsAffineHom _)
  have hf'prop : IsProper f' :=
    MorphismProperty.of_isPullback hp (inferInstance : IsProper f)
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian f'
  -- the pullback of `A` is ample
  set B : X'.Modules := (Scheme.Modules.pullback p).obj A with hB
  have hBinv : Stacks.Ample.IsInvertibleModule X' B :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback p A
  have hBamp : Stacks.Ample.IsAmple X' B :=
    Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X' B
      (Scheme.Modules.isAmple_pullback_of_isAffineHom p A hAamp)
  have hLcoh : SheafOfModules.IsCoherent L :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X' L
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f' L B
      hBamp
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple B
    hBamp L inferInstance hLcoh.isFiniteType
  set n : ℕ := max d₀ n₀.toNat with hn
  obtain ⟨σ, -⟩ := hn₀ (n : ℤ) (by omega)
  have hvan := hd₀ n 1 (le_max_left _ _) Nat.one_pos
  -- `X_K` is nonempty
  have : Nonempty X' := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨y⟩ : Nonempty (Spec (.of K)) := inferInstance
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x y
      (Subsingleton.elim (f.base x) _)
    exact ⟨hp.isoPullback.inv.base z⟩
  -- the twist by `A^{⊗ n}` is the twist by the `n`-th power of `B`
  set T : X'.Modules :=
    Stacks.RelativeVeryAmple.tensorModules X' L (Stacks.Ample.tensorPowModule X' B n)
  let e : baseChangeTwist p L (Stacks.Ample.tensorPowModule X A n) ≅ T :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso X' (Iso.refl L)
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso p A n)
  have : SheafOfModules.IsCoherent T :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X' _
  have hfd := finiteDimensional_cohomologyOverField_of_isProper K f' T 0
  let e₂ := Stacks.TensorSheafSpellingIso.monoidalTensorIso X' L
    (Stacks.Ample.tensorPowModule X' B n)
  have hTinv : Stacks.Ample.IsInvertibleModule X' T :=
    Stacks.SheafOfModules.tensorProduct_isInvertible X'.presheaf _ L _
  have hNinv : Stacks.Ample.IsInvertibleModule X' _ :=
    Stacks.Picard.isInvertible_of_iso e₂.symm hTinv
  obtain ⟨i, hi⟩ := exists_ne_zero_of_generatingSections _ hNinv σ
  have hi' : (e₂.hom.app ⊤) ((σ.s i).eval (op ⊤)) ≠ 0 := by
    intro h0
    apply hi
    have := congrArg (e₂.inv.app ⊤) h0
    rw [map_zero] at this
    have key : (σ.s i).eval (op ⊤) = (e₂.inv.app ⊤) ((e₂.hom.app ⊤) ((σ.s i).eval (op ⊤))) := by
      change _ = (e₂.hom ≫ e₂.inv).app ⊤ ((σ.s i).eval (op ⊤))
      rw [e₂.hom_inv_id]
      rfl
    exact key.trans this
  have hnt : Nontrivial (cohomologyOverField K f' T 0) :=
    have : Nontrivial Γ(T, ⊤) := ⟨⟨_, 0, hi'⟩⟩
    (cohomologyOverFieldZeroEquivSections K f' _).nontrivial
  have hpos : 0 < Module.finrank K (cohomologyOverField K f' T 0) :=
    Module.finrank_pos_iff.mpr hnt
  refine ⟨Stacks.Ample.tensorPowModule X A n, Module.finrank K (cohomologyOverField K f' T 0) - 1,
    inferInstance, ?_, ?_, ?_⟩
  · exact ((isZero_cohomologyOverField_iff_isZero_hgroup K f' _ 1).mpr hvan).of_iso
      (cohomologyOverFieldIso K f' e 1)
  · exact LinearEquiv.finiteDimensional (cohomologyOverFieldIso K f' e 0).symm.toLinearEquiv
  · rw [finrank_cohomologyOverField_eq_of_iso K f' e 0]
    omega

/-! ### Rational points of a smooth scheme over a separably closed field -/

/-- **Rational closed points are dense on a smooth scheme over a separably closed field.**
Every nonempty open of `X` contains a closed point `x` at which the canonical map `k ⟶ κ(x)` is
bijective: by [Stacks, Tag 056U] it contains a closed point whose residue field is finite and
separable over `k`, and a finite separable extension of a separably closed field is trivial. -/
@[sga "3 VIA 2.5.4" "special case", sga "6 X 7.18.2" "(a), special case"]
theorem exists_isClosed_bijective_residueField_of_isSepClosed (k : Type u) [Field k]
    [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, IsClosed ({x} : Set X) ∧
      Function.Bijective ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom := by
  obtain ⟨x, hx, hxU⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth f).exists_mem_open hU hne
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have := hx.2.1
  have := hx.2.2
  exact ⟨x, hxU, mem_closedPoints_iff.mp hx.1, IsSepClosed.algebraMap_bijective k _⟩

/-- **The reduced closed subscheme at a rational closed point is the base point.** If `x` is a
closed point of a `k`-scheme with `k ⟶ κ(x)` bijective, the reduced closed subscheme `{x}` maps
isomorphically to `Spec k`: it is `Spec κ(x)`, the kernel of `Spec κ(x) ⟶ X` being the vanishing
ideal of the point. -/
theorem isIso_vanishingIdeal_subschemeι_comp (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {x : X} (hx : IsClosed ({x} : Set X))
    (hbij : Function.Bijective
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom) :
    IsIso ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{x}, hx⟩ : TopologicalSpace.Closeds X)).subschemeι ≫ f) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : TopologicalSpace.Closeds X) with hI
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_isClosedImmersion).mp hx
  have hker : I.subschemeι.ker = (X.fromSpecResidueField x).ker := by
    rw [I.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hI]
    congr 1
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_closure, Scheme.range_fromSpecResidueField]
    exact hx.closure_eq.symm
  let ψ : Spec (X.residueField x) ⟶ I.subscheme :=
    IsClosedImmersion.lift I.subschemeι (X.fromSpecResidueField x) hker.le
  have hψ : ψ ≫ I.subschemeι = X.fromSpecResidueField x := IsClosedImmersion.lift_fac _ _ _
  have : IsIso ψ :=
    IsClosedImmersion.isIso_of_ker_eq (X.fromSpecResidueField x) I.subschemeι ψ hψ hker.symm
  have key : Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X.fromSpecResidueField x ≫ f).appTop ≫
        (Scheme.ΓSpecIso _).hom := by
    conv_rhs => rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ f)]
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpecResidueField_appTop] at key
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have : IsIso (X.fromSpecResidueField x ≫ f) := by
    rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ f), key]
    infer_instance
  have : IsIso (ψ ≫ I.subschemeι ≫ f) := by
    rw [← Category.assoc, hψ]
    infer_instance
  exact IsIso.of_isIso_comp_left ψ _

/-! ### One step of the descending induction -/

/-- **The geometry of one step of the induction of Stacks Tag 0B9Y.** Let `k` be separably
closed, `X` a smooth curve over `k`, `X_K` its base change to a field extension and `L` an
invertible sheaf on `X_K`. If the twist `M = L ⊗ p^*L₀` by an invertible `L₀` on `X` has vanishing
`H¹` and `H⁰` of dimension `t + 2`, choose a nonzero section `s` of `M`, a `k`-rational closed
point `x` of `X` whose fibre point `x_K` lies in the nonvanishing locus of `s` (rational points are
dense, Tag 056U, and `X_K ⟶ X` is open, Tag 0383), and its ideal sheaf `𝓘_x`, invertible by
Tag 0B8Y. Its pullback is the ideal sheaf of the closed subscheme `Z = x_K ≅ Spec K`, and the
sequence `0 ⟶ 𝓘_Z ⊗ M ⟶ M ⟶ i_*i^*M ⟶ 0` is the twist of `M` by `L₁ = 𝓘_x ⊗ L₀`. -/
theorem pointIdealTwistStep (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X)
    (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsCurve k f] [Smooth f] (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] :
    PointIdealTwistStep K f' p L := by
  intro L₀ t hL₀ hM
  have := hL₀
  set M : X'.Modules := baseChangeTwist p L L₀ with hMdef
  set φ := Spec.map (CommRingCat.ofHom (algebraMap k K)) with hφ
  -- invertibility of `M`
  have hMinv : Stacks.Ample.IsInvertibleModule X' M :=
    Stacks.SheafOfModules.tensorProduct_isInvertible X'.presheaf _ L _
  have hMinv' : AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj
      X'.ringCatSheaf.property M :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X'.presheaf _ _).mp hMinv
  -- a nonzero section of `M`
  have hfd := hM.finiteDimensional_zero
  have hnt : Nontrivial (cohomologyOverField K f' M 0) :=
    Module.finrank_pos_iff.mp (by rw [hM.finrank_zero]; omega)
  have : Nontrivial Γ(M, ⊤) := (cohomologyOverFieldZeroEquivSections K f' M).symm.nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : Γ(M, ⊤))
  -- `X_K` is reduced, so the nonvanishing locus of `s` is a nonempty open
  have : Smooth f' := MorphismProperty.of_isPullback hp (inferInstance : Smooth f)
  have : IsReduced X' := isReduced_of_smooth f'
  have hbridge : Stacks.SheafOfModules.nonvanishingLocus (X := X'.toRingedSpace) M
      (Stacks.SheafOfModules.sectionsOfTop M s) = Stacks.Ample.nonvanishingLocus M s :=
    nonvanishingLocus_sectionsOfTop_eq M s
  have hVo : IsOpen (Stacks.Ample.nonvanishingLocus M s) := by
    rw [← hbridge]
    exact Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := X'.toRingedSpace) M _
  have hVne : (Stacks.Ample.nonvanishingLocus M s).Nonempty :=
    hbridge ▸ nonempty_nonvanishingLocus_of_ne_zero M s hs
  -- its image in `X` is open, and contains a rational closed point
  have : UniversallyOpen p :=
    MorphismProperty.of_isPullback hp.flip (universallyOpen_of_field k φ)
  obtain ⟨x, ⟨y, hyV, rfl⟩, hxc, hbij⟩ :=
    exists_isClosed_bijective_residueField_of_isSepClosed k f
      (p.isOpenMap _ hVo) (hVne.image _)
  -- the ideal sheaf of the point is invertible (Tag 0B8Y)
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{p.base y}, hxc⟩ : TopologicalSpace.Closeds X) with hI
  have hIeff : Stacks.Divisors.IsEffectiveCartierDivisor I := by
    let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (p.base y)).hom.toAlgebra
    have hsep := Stacks.Curves.isSeparableExtension_of_bijective_algebraMap k
      (X.residueField (p.base y)) hbij
    have h := smoothAt_closedPoint_tfae_of_isCurve_of_isSeparable k f hxc hsep
    exact (h (InfinitesimalLifting.SmoothAt f (p.base y)) (by simp)
      (Stacks.Divisors.IsEffectiveCartierDivisor I) (by simp [hI])).mp
      (InfinitesimalLifting.smoothAt_of_smooth f _)
  -- its pullback to `X_K`
  have : Flat p := MorphismProperty.of_isPullback hp.flip (inferInstance : Flat φ)
  set C : X'.IdealSheafData := I.comap p with hC
  have hCeff : Stacks.Divisors.IsEffectiveCartierDivisor C :=
    Stacks.Divisors.isPullbackDefined_of_flat p I hIeff
  -- the closed subscheme `Z = x_K` maps isomorphically to `Spec K`
  have hZiso : IsIso (C.subschemeι ≫ f') := by
    have := isIso_vanishingIdeal_subschemeι_comp k f hxc hbij
    have sq := (IsPullback.of_hasPullback p I.subschemeι).flip.paste_vert hp
    have h1 : pullback.fst p I.subschemeι ≫ f' =
        sq.isoPullback.hom ≫ pullback.snd (I.subschemeι ≫ f) φ :=
      (sq.isoPullback_hom_snd).symm
    have h2 : C.subschemeι ≫ f' = (I.comapIso p).hom ≫ pullback.fst p I.subschemeι ≫ f' := by
      rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    rw [h2, h1]
    infer_instance
  have hZsub : Subsingleton C.subscheme :=
    (C.subschemeι ≫ f').homeomorph.injective.subsingleton
  -- the pullback of `M` to `Z` has a one-dimensional space of sections
  have hone : Module.finrank K (cohomologyOverField K (C.subschemeι ≫ f')
      ((Scheme.Modules.pullback C.subschemeι).obj M) 0) = 1 := by
    have hpb : Stacks.SheafOfModules.IsInvertible C.subscheme.presheaf
        (structureSheafRing C.subscheme.toRingedSpace).property
        ((Scheme.Modules.pullback C.subschemeι).obj M) :=
      Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι M hMinv'
    obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology C.subscheme
      ((Scheme.Modules.pullback C.subschemeι).obj M)
    have e' : (Scheme.Modules.pullback C.subschemeι).obj M ≅
        SheafOfModules.unit C.subscheme.ringCatSheaf := e
    rw [finrank_cohomologyOverField_eq_of_iso K (C.subschemeι ≫ f') e' 0,
      finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
    let : Algebra K Γ(C.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (C.subschemeι ≫ f').appTop).hom.toAlgebra
    have : IsIso (C.subschemeι ≫ f').appTop :=
      inferInstanceAs (IsIso ((C.subschemeι ≫ f').app ⊤))
    have hbij : Function.Bijective (Algebra.linearMap K Γ(C.subscheme, ⊤)) :=
      ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of K)).inv ≫
        (C.subschemeι ≫ f').appTop)
    rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]
  -- the point `y` lies on `Z`
  obtain ⟨z, hzy⟩ : y ∈ Set.range C.subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, hC, Scheme.IdealSheafData.support_comap, hI]
    exact Set.mem_singleton _
  -- the twisted ideal sequence of `Z`
  obtain ⟨w₀, hSE₀⟩ := Stacks.Divisors.exists_shortExact_invertibleTwist C M hMinv'
  -- the twist by `L₁ = 𝓘_x ⊗ L₀`
  have hIinv : Stacks.Ample.IsInvertibleModule X (Stacks.Divisors.idealSheafOfModules I) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf _ _).mpr hIeff
  have := hIinv
  set L₁ : X.Modules :=
    Stacks.RelativeVeryAmple.tensorModules X (Stacks.Divisors.idealSheafOfModules I) L₀ with hL₁
  have hL₁inv : Stacks.Ample.IsInvertibleModule X L₁ :=
    Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf _ _ _
  let T : X'.Modules :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj M).obj
      (Stacks.Divisors.idealSheafOfModules C)
  let eT : baseChangeTwist p L L₁ ≅ T :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso X' (Iso.refl L)
        (Stacks.RelativeVeryAmple.pullbackTensorModulesIso p _ L₀ ≪≫
          Stacks.RelativeVeryAmple.tensorModulesMapIso X'
            (Stacks.Divisors.pullbackIdealSheafComapIso p I hCeff) (Iso.refl _)) ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesAssociator X' L _ _).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X'
        (Stacks.Algebraization.tensorModulesBraidingIso X' L _) (Iso.refl _) ≪≫
      Stacks.TensorSheafSpellingIso.tensorModulesAssociator X' _ L _
  let α₀ : T ⟶ M :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.sheaf).flip.obj M).map
      (Stacks.Divisors.idealInclusion C) ≫ (Stacks.Divisors.tensorUnitIso M).hom
  let β : M ⟶ (Scheme.Modules.pushforward C.subschemeι).obj
      ((Scheme.Modules.pullback C.subschemeι).obj M) :=
    (modulePullbackPushforwardAdjunction C.subschemeι.toLRSHom.toShHom).unit.app M
  have w₀' : α₀ ≫ β = 0 := w₀
  have hSE₁ : (ShortComplex.mk α₀ β w₀').ShortExact := hSE₀
  have w : (eT.hom ≫ α₀) ≫ β = 0 :=
    (Category.assoc eT.hom α₀ β).trans ((congrArg (fun g => eT.hom ≫ g) w₀').trans comp_zero)
  have hSE : (ShortComplex.mk (eT.hom ≫ α₀) β w).ShortExact :=
    ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk (S₁ := ShortComplex.mk α₀ β w₀')
        (S₂ := ShortComplex.mk (eT.hom ≫ α₀) β w) eT.symm (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)) hSE₁
  refine ⟨C.subscheme, C.subschemeι, inferInstance, L₁, eT.hom ≫ α₀, β, w, hSE, hL₁inv, hone,
    (cohomologyOverFieldZeroEquivSections K f' M).symm s, ?_⟩
  -- the chosen class has nonzero image
  intro hc
  refine app_top_unit_ne_zero_of_mem_nonvanishingLocus C.subschemeι M s z (hzy ▸ hyV) ?_
  have key := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap K f' β
    ((cohomologyOverFieldZeroEquivSections K f' M).symm s)
  exact ((congrArg (fun t => (Scheme.Modules.Hom.app β ⊤) t)
        (Equiv.apply_symm_apply (cohomologyOverFieldZeroEquivSections K f' M) s).symm).trans
      (key.symm.trans
        ((congrArg (cohomologyOverFieldZeroEquivSections K f'
            ((Scheme.Modules.pushforward C.subschemeι).obj
              ((Scheme.Modules.pullback C.subschemeι).obj M))) hc).trans
          (cohomologyOverFieldZeroEquivSections_zero K f' _))))

/-! ### Stacks Tag 0B9Y -/

/-- **Stacks Project, Tag 0B9Y.** Let `k` be a separably closed field, `X` a smooth projective
curve over `k`, `K/k` a field extension and `X' = X_K` the base change, given as any pullback
square with `X ⟶ Spec k ⟵ Spec K`. For every invertible sheaf `L` on `X'` there is an invertible
sheaf `L₀` on `X` with

`dim_K H⁰(X', L ⊗ p^*L₀) = 1` and `dim_K H¹(X', L ⊗ p^*L₀) = 0`.

The proof is the source's: the start of the descending induction is
`AlgebraicGeometry.ampleTwistStart`, its step is `AlgebraicGeometry.pointIdealTwistStep`, and the
induction joining them is `AlgebraicGeometry.exists_hasPrescribedLowCohomology_one`, whose
cohomology is Tag 0B8Z's step lemma. The genus `g` of the source occurs in neither the assertion
nor the proof and is not a parameter. This form, for an arbitrary pullback square, is the one
`Stacks.PicardFunctor.TwistToNormalized` quantifies over. -/
@[stacks 0B9Y "for X_K given as any pullback square of X ⟶ Spec k along Spec K ⟶ Spec k, with \
L ⊗ L₀|_{X_K} the twist baseChangeTwist p L L₀ = L ⊗ p^*L₀"]
theorem exists_invertible_baseChangeTwist_finrank_eq_one_of_isSepClosed
    (k K : Type u) [Field k] [IsSepClosed k] [Field K] [Algebra k K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) (f' : X' ⟶ Spec (.of K)) (p : X' ⟶ X)
    (hp : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsCurve k f] [Smooth f] (hproj : IsProjective f)
    (L : X'.Modules) [Stacks.Ample.IsInvertibleModule X' L] :
    ∃ L₀ : X.Modules, Stacks.Ample.IsInvertibleModule X L₀ ∧
      Module.finrank K (cohomologyOverField K f' (baseChangeTwist p L L₀) 0) = 1 ∧
      Module.finrank K (cohomologyOverField K f' (baseChangeTwist p L L₀) 1) = 0 := by
  have : IsProper f := hproj.isProper
  obtain ⟨L₀, t, hL₀, h⟩ := ampleTwistStart k K f f' p hp L
  obtain ⟨L₁, hL₁, hfin⟩ := exists_hasPrescribedLowCohomology_one K f' p L
    (pointIdealTwistStep k K f f' p hp L) t L₀ hL₀ h
  exact ⟨L₁, hL₁, hfin.finrank_zero, hfin.finrank_one⟩

end AlgebraicGeometry

end
