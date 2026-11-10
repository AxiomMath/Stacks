module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedStalksOfClosedPoints
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.Decomposition
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTranscendenceDegree
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekTranscendenceDegreeCharts
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.ProjectiveSectionsAlongFibre
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.KoszulLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimensionOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# The map `∧^r Ω_{X/Y} ⟶ ω_{X/Y}` on the smooth locus, [Stacks, Tag 0EA0]

For `f : X ⟶ Y` a morphism of `FTS S` through `P` smooth and proper over a Cohen–Macaulay `Y`,
Koszul at the points of dimension at most one and with residue transcendence degree `r` at the
generic points of `X`, the maps of [Stacks, Tag 0E9Z] on the local complete intersection locus
glue and extend to a map `∧^r Ω_{X/Y} ⟶ H^{-r}(f^!𝒪_Y)` which is an isomorphism at the smooth
points of `f` (`Stacks.Duality.SmoothLocus.exists_map_exteriorPower_isIso_of_smoothAt`).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.SmoothLocus

/-- A morphism smooth at `x` is smooth on an open neighbourhood of `x`. -/
theorem exists_smooth_of_smoothAt {X Y : Scheme.{u}} {f : X ⟶ Y} {x : X}
    (h : InfinitesimalLifting.SmoothAt f x) : ∃ V : X.Opens, x ∈ V ∧ Smooth (V.ι ≫ f) := by
  obtain ⟨V, hxV, hV⟩ := h
  refine ⟨V, hxV, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι (f := f) (U := (⊤ : Y.Opens)) (V := V) (e := le_top)]
  infer_instance

/-- A morphism smooth at `x` is Koszul at `x`. -/
theorem koszulAt_of_smoothAt {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyOfFiniteType f] {x : X}
    (h : InfinitesimalLifting.SmoothAt f x) : KoszulAt f x := by
  obtain ⟨V, hxV, hV⟩ := exists_smooth_of_smoothAt h
  exact ⟨AlgebraicGeometry.finiteTypeAt_of_locallyOfFiniteType f x, V, hxV, V.toScheme, 𝟙 _,
    V.ι ≫ f, inferInstance,
    Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_isOpenImmersion _,
    hV, (Category.id_comp _).symm⟩

/-- A generic point of an irreducible component has no proper generization. -/
private theorem eq_of_specializes_of_closure_mem_irreducibleComponents {X : Scheme.{u}} {ξ y : X}
    (hξ : closure {ξ} ∈ irreducibleComponents X) (hy : y ⤳ ξ) : y = ξ := by
  have hsub : closure {ξ} ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr hy.mem_closure) isClosed_closure
  exact (inseparable_iff_closure_eq.mpr
    (Set.Subset.antisymm (hξ.2 isIrreducible_singleton.closure hsub) hsub)).eq

/-- Every point of a scheme is a specialization of the generic point of an irreducible component,
and that generic point has no proper generization. -/
theorem exists_generic_specializes {X : Scheme.{u}} (x : X) :
    ∃ ξ : X, closure {ξ} ∈ irreducibleComponents X ∧ ξ ⤳ x ∧ ∀ y : X, y ⤳ ξ → y = ξ := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  let ξ := hZ.1.genericPoint
  have hξ : IsGenericPoint ξ Z :=
    hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hmem : closure {ξ} ∈ irreducibleComponents X := hξ.def ▸ hZ
  exact ⟨ξ, hmem, hξ.specializes (hxZ rfl), fun y hy =>
    eq_of_specializes_of_closure_mem_irreducibleComponents hmem hy⟩

/-- The local ring of a fibre at a point with no proper generization is zero-dimensional. -/
theorem ringKrullDim_stalk_fiber_eq_zero {P Z : Scheme.{u}} (p : P ⟶ Z) (ξ : P)
    (hξ : ∀ y : P, y ⤳ ξ → y = ξ) :
    ringKrullDim ((p.fiber (p.base ξ)).presheaf.stalk (p.asFiber ξ)) = 0 := by
  have hmax : IsMax (p.asFiber ξ) := by
    intro y hy
    have hspec : (p.fiberι (p.base ξ)).base y ⤳ ξ := by
      simpa using (show y ⤳ p.asFiber ξ from hy).map (p.fiberι (p.base ξ)).continuous
    refine le_of_eq ((p.fiberι (p.base ξ)).isEmbedding.injective ?_)
    rw [hξ _ hspec]
    exact (Scheme.Hom.fiberι_asFiber p ξ).symm
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_eq_zero.mpr hmax

/-- **A smooth morphism has fibre dimension `r` at `x` when its residue field extensions at the
generic points of `X` have transcendence degree `r`.** -/
theorem topologicalKrullDimAt_fiber_eq_of_smoothAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (r : ℕ)
    (htr : ∀ ξ : X, closure {ξ} ∈ irreducibleComponents X →
      Stacks.Chow.residueTrdeg f ξ = (r : Cardinal)) {x : X}
    (hx : InfinitesimalLifting.SmoothAt f x) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (r : WithBot ℕ∞) := by
  obtain ⟨V, hxV, hsm⟩ := exists_smooth_of_smoothAt hx
  let h := V.ι ≫ f
  have hCM := isCohenMacaulay_fiber_of_smooth h
  let t := relativeDimensionFunction h hCM ⟨x, hxV⟩
  let D := relativeDimensionOpen h hCM t
  obtain ⟨ξ, hξc, hξx, hξmax⟩ := exists_generic_specializes x
  obtain ⟨ξ', hξ'D, hξ'⟩ : ξ ∈ V.ι ''ᵁ D := hξx.mem_open (V.ι ''ᵁ D).isOpen
    ⟨_, (mem_relativeDimensionOpen h hCM t ⟨x, hxV⟩).2 rfl, rfl⟩
  have hmax' : ∀ y : V.toScheme, y ⤳ ξ' → y = ξ' := fun y hy =>
    V.ι.isOpenEmbedding.injective ((hξmax _ (hξ' ▸ hy.map V.ι.continuous)).trans hξ'.symm)
  have h02FX := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg h ξ'
  rw [ringKrullDim_stalk_fiber_eq_zero h ξ' hmax', zero_add, relativeDimensionFunction_apply h hCM,
    (mem_relativeDimensionOpen h hCM t ξ').1 hξ'D] at h02FX
  have htrξ : Stacks.Chow.residueTrdeg h ξ' = (r : Cardinal) := by
    rw [Stacks.Chow.residueTrdeg_of_surjective_residueFieldMap_comp V.ι f ξ'
      (ConcreteCategory.bijective_of_isIso (V.ι.residueFieldMap ξ')).2]
    exact hξ' ▸ htr ξ hξc
  change ((t : ℕ) : WithBot ℕ∞) = (Cardinal.toENat (Stacks.Chow.residueTrdeg h ξ') : WithBot ℕ∞)
    at h02FX
  rw [htrξ, Cardinal.toENat_nat] at h02FX
  have hsq := fiberDimensionAt_eq_of_open_square V.ι f h (𝟙 Y) (Category.comp_id _).symm ⟨x, hxV⟩
  change _ = topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) at hsq
  rw [← hsq]
  refine (relativeDimensionFunction_apply h hCM _).trans ?_
  exact_mod_cast h02FX

/-- **The rank of `Ω` at a point of a smooth composite through an immersion.** If `i ≫ p` is
smooth, with `p` smooth, the conormal sheaf of `i` of rank `c` and `i^*Ω_p` of rank `d`, then the
fibre dimension of `i ≫ p` is `d - c`. -/
theorem sub_eq_topologicalKrullDimAt_fiber {Z P S : Scheme.{u}} (i : Z ⟶ P) [IsImmersion i]
    (p : P ⟶ S) [IsLocallyNoetherian S] [Smooth p] [Smooth (i ≫ p)] (c d : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat
        (Opens.grothendieckTopology ↥Z.toLocallyRingedSpace.toRingedSpace.carrier)
        Z.toLocallyRingedSpace.toRingedSpace.sheaf)
      (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i : Z.Modules) c]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat
        (Opens.grothendieckTopology ↥Z.toLocallyRingedSpace.toRingedSpace.carrier)
        Z.toLocallyRingedSpace.toRingedSpace.sheaf)
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) d] (z : Z) :
    c ≤ d ∧ (((d - c : ℕ) : ℕ) : WithBot ℕ∞) = topologicalKrullDimAt ((i ≫ p).fiber ((i ≫ p) z))
      ((i ≫ p).asFiber z) := by
  obtain ⟨hcd, ⟨b⟩⟩ := (Stacks.ConormalSequenceRight.smoothAt_iff_nonempty_basis i p c d z).1
    (InfinitesimalLifting.smoothAt_of_smooth _ z)
  refine ⟨hcd, ?_⟩
  rw [← finrank_stalk_relativeDifferentials_eq_fiberDimensionAt]
  have : Nontrivial ↑(TopCat.Presheaf.stalk Z.toLocallyRingedSpace.toRingedSpace.sheaf.obj z) :=
    (Z.toLocallyRingedSpace.isLocalRing z).toNontrivial
  exact congrArg (fun n : ℕ => ((n : ℕ∞) : WithBot ℕ∞))
    ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin _)).symm

open ClosedOpenProperFactorization in
/-- **On a piece of [Stacks, Tag 0E9Z], the exponent at a smooth point is the transcendence
degree at the generic points.** -/
theorem sub_eq_of_smoothAt {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
    {P : Scheme.{u}} (ι : X.left ⟶ P) [IsImmersion ι] (g : P ⟶ Y.left) [Smooth g] [IsProper g]
    (hfac : ι ≫ g = f.left) (d : ℕ) (O : P.Opens) (hOd : O ≤ dimensionOpen g d)
    (hOc : O ≤ ι.coborderRange)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf ι)] (m : ℕ)
    (hm : ∀ x ∈ ι ⁻¹ᵁ O, Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheaf ι) x = m)
    (r : ℕ) (htr : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left →
      Stacks.Chow.residueTrdeg f.left ξ = (r : Cardinal))
    {x : X.left} (hxO : x ∈ ι ⁻¹ᵁ O) (hx : InfinitesimalLifting.SmoothAt f.left x) :
    (d : ℤ) - m = r := by
  obtain ⟨V, hxV, hsm⟩ := exists_smooth_of_smoothAt hx
  obtain ⟨t, ht, hts⟩ := ι.isEmbedding.isInducing.isOpen_iff.1 V.isOpen
  let T : P.Opens := ⟨t, ht⟩
  let O' := O ⊓ T
  have hOd' : O' ≤ dimensionOpen g d := inf_le_left.trans hOd
  have hOc' : O' ≤ ι.coborderRange := inf_le_left.trans hOc
  have hW'V : ι ⁻¹ᵁ O' ≤ V := fun y hy => by
    have : y ∈ ι ⁻¹' t := hy.2
    rwa [hts] at this
  have hxO' : x ∈ ι ⁻¹ᵁ O' := ⟨hxO, by
    change x ∈ ι ⁻¹' t
    rw [hts]
    exact hxV⟩
  let i := pieceImmersion ι g d O' hOd'
  have : IsClosedImmersion i := isClosedImmersion_pieceImmersion ι g d O' hOd' hOc'
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := (ι ⁻¹ᵁ O').toScheme.ringCatSheaf) (Stacks.Conormal.conormalSheaf i) m :=
    isFiniteLocallyFreeOfRank_pieceImmersion ι g d O' hOd' hOc' m
      (fun y hy => hm y hy.1)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology
        ↥(ι ⁻¹ᵁ O').toScheme.toLocallyRingedSpace.toRingedSpace.carrier)
        (ι ⁻¹ᵁ O').toScheme.toLocallyRingedSpace.toRingedSpace.sheaf)
      (conormalModules (pieceOpen g d O') i) m := ‹_›
  have := isFiniteLocallyFreeOfRank_pullback_relativeDifferentials (pieceOpen g d O') i
    ((dimensionOpen g d).ι ≫ g) d
  have := isFiniteLocallyFreeOfRank_conormalSheaf_comp (pieceOpen g d O') i m
  have hfac' : (i ≫ (pieceOpen g d O').ι) ≫ (dimensionOpen g d).ι ≫ g = (ι ⁻¹ᵁ O').ι ≫ f.left :=
    (Category.assoc _ _ _).trans (pieceImmersion_fac f ι g hfac d O' hOd')
  have : Smooth ((i ≫ (pieceOpen g d O').ι) ≫ (dimensionOpen g d).ι ≫ g) := by
    rw [hfac', ← X.left.homOfLE_ι hW'V, Category.assoc]
    infer_instance
  obtain ⟨hmd, heq⟩ := sub_eq_topologicalKrullDimAt_fiber (i ≫ (pieceOpen g d O').ι)
    ((dimensionOpen g d).ι ≫ g) m d ⟨x, hxO'⟩
  have hsq := fiberDimensionAt_eq_of_open_square (ι ⁻¹ᵁ O').ι f.left
    ((i ≫ (pieceOpen g d O').ι) ≫ (dimensionOpen g d).ι ≫ g) (𝟙 _)
    (by rw [hfac', Category.comp_id]) ⟨x, hxO'⟩
  change _ = topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) at hsq
  rw [hsq, topologicalKrullDimAt_fiber_eq_of_smoothAt f.left r htr hx] at heq
  have : d - m = r := by exact_mod_cast heq
  omega

/-- The cohomology sheaves of `f^!𝒪_Y` are coherent. -/
theorem isCoherent_upperShriekHomology {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S}
    (f : X ⟶ Y) (j : CompactificationOf (Over.mk f.left)) (k : ℤ) :
    _root_.SheafOfModules.IsCoherent (ClosedOpenProperFactorization.upperShriekHomology f j k) := by
  have : AlgebraicGeometry.IsNoetherian X.left := ⟨⟩
  refine isCoherent_homology_of_finiteTildeModels (fun x => ?_) k
  obtain ⟨U, hU, V, hV, hUV, hxU, -, p, ⟨e⟩⟩ := exists_chart_of_upperShriekStructureSheafCharts f j
    (upperShriekStructureSheafCharts f j) x ⊤ trivial
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  exact ⟨U, hU, hxU, _, fun i => Dualizing.finite_homology_upperShriekFunctor p i, ⟨e⟩⟩

/-- The stalk of a sheaf of modules on a scheme, with Mathlib's module structure over `𝒪_{X,x}`,
is the value of `Stacks.Duality.schemeStalkModuleFunctor`. -/
def presheafStalkLinearEquivSchemeStalk {Z : Scheme.{u}} (F : Z.Modules) (z : Z) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val z
    TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z ≃ₗ[Z.presheaf.stalk z]
      (schemeStalkModuleFunctor z).obj F :=
  letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val z
  { toFun m := m
    invFun m := m
    map_add' _ _ := rfl
    map_smul' r m := by
      obtain ⟨V, hV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq Z.presheaf r
      obtain ⟨W, hW, n, rfl⟩ := TopCat.Presheaf.exists_germ_eq
        (C := AddCommGrpCat.{u}) F.val.presheaf m
      have ea : Z.presheaf.germ V z hV a = Z.presheaf.germ (V ⊓ W) z ⟨hV, hW⟩
          (Z.presheaf.map (homOfLE inf_le_left).op a) :=
        (Z.presheaf.germ_res_apply _ _ _ _).symm
      have en : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.val.presheaf W z hW n =
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.val.presheaf (V ⊓ W) z ⟨hV, hW⟩
            (F.val.presheaf.map (homOfLE inf_le_right).op n) :=
        (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
      rw [ea, en, RingHom.id_apply]
      have h1 := PresheafOfModules.germ_smul F.val z (V ⊓ W) ⟨hV, hW⟩
        (Z.presheaf.map (homOfLE inf_le_left).op a)
        (F.val.presheaf.map (homOfLE inf_le_right).op n)
      have h2 := schemeStalkModuleFunctor_germ_smul z F (V ⊓ W) ⟨hV, hW⟩
        (Z.presheaf.map (homOfLE inf_le_left).op a) (F.val.presheaf.map (homOfLE inf_le_right).op n)
      exact h1.symm.trans h2
    left_inv _ := rfl
    right_inv _ := rfl }

/-- **The depth of `ω_{X/Y}` at a point of dimension at least two.** Under the hypotheses of
[Stacks, Tag 0E9V], at a point `x` with `dim 𝒪_{X,x} ≥ 2` the stalk of `H^{-r}(f^!𝒪_Y)` has depth
at least two (it is `⊤` when the stalk vanishes). -/
theorem two_le_depth_stalk_upperShriekHomology {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S}
    (f : X ⟶ Y) (j : CompactificationOf (Over.mk f.left)) (r : ℕ) (x : X.left)
    (hCM : IsCohenMacaulayLocalRing (Y.left.presheaf.stalk (f.left.base x)))
    (htrdeg : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left → x ∈ closure {ξ} →
      Stacks.Chow.residueTrdeg f.left ξ ≤ (r : Cardinal))
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.left.presheaf.stalk x)) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (ClosedOpenProperFactorization.upperShriekHomology f j (-(r : ℤ))).val x
    (2 : ℕ∞) ≤ Module.depth (X.left.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (ClosedOpenProperFactorization.upperShriekHomology f j (-(r : ℤ))).val.presheaf x) := by
  let F := ClosedOpenProperFactorization.upperShriekHomology f j (-(r : ℤ))
  let e := presheafStalkLinearEquivSchemeStalk F x
  refine le_of_le_of_eq ?_ (Module.depth_eq_depth_of_linearEquiv
    (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x)) e).symm
  rcases subsingleton_or_nontrivial ((modulesStalkFunctor x).obj F) with hs | hnt
  · have : Subsingleton ((schemeStalkModuleFunctor x).obj F) := hs
    have : IsLocalRing.maximalIdeal (X.left.presheaf.stalk x) •
        (⊤ : Submodule (X.left.presheaf.stalk x) ((schemeStalkModuleFunctor x).obj F)) = ⊤ := by
      ext m
      simp only [Submodule.mem_top, iff_true]
      rw [Subsingleton.elim m 0]
      exact Submodule.zero_mem _
    simp [Module.depth, this]
  · have := module_finite_modulesStalk_homology_upperShriek f j x (-(r : ℤ))
    have h := min_two_ringKrullDim_le_moduleDepth_modulesStalk_homology_upperShriek f j x r hCM
      htrdeg hnt
    have h2 : (2 : ℕ∞) ≤ (ringKrullDim (X.left.presheaf.stalk x)).unbotD 0 := by
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot (by simp) hdim)
      rw [← hd, WithBot.unbotD_coe]
      rw [← hd] at hdim
      exact WithBot.coe_le_coe.mp hdim
    rw [min_eq_left h2] at h
    change (2 : ℕ∞) ≤ Module.depth _ _ ((modulesStalkFunctor x).obj F)
    exact le_of_le_of_eq h moduleDepth_eq_depth

/-- **Extension of a map from an open.** If `B ⟶ j_*(B|_U)` is an isomorphism, every map
`A|_U ⟶ B|_U` is the restriction of a map `A ⟶ B`. -/
theorem exists_hom_restrict_eq_of_isIso_unit {Z : Scheme.{u}} (U : Z.Opens) {A B : Z.Modules}
    (hB : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app B))
    (ψ : (Scheme.Modules.restrictFunctor U.ι).obj A ⟶ (Scheme.Modules.restrictFunctor U.ι).obj B) :
    ∃ φ : A ⟶ B, (Scheme.Modules.restrictFunctor U.ι).map φ = ψ := by
  let adj := Scheme.Modules.restrictAdjunction U.ι
  have hunit : adj.unit.app B ≫ (Scheme.Modules.pushforward U.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app B) =
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app B :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ B
  have : IsIso (adj.unit.app B) := by
    rw [← hunit] at hB
    exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward U.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app B))
  refine ⟨adj.homEquiv _ _ ψ ≫ inv (adj.unit.app B), ?_⟩
  have h1 : (adj.homEquiv _ _ ψ ≫ inv (adj.unit.app B)) ≫ adj.unit.app B = adj.homEquiv _ _ ψ := by
    simp
  have h2 := congrArg (adj.homEquiv _ _).symm h1
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_counit, adj.left_triangle_components B] at h2
  exact (Category.comp_id _).symm.trans h2

/-- The stalk at `x` of the restriction to an open of a map of modules is its stalk at `x`. -/
theorem isIso_stalkAb_restrictFunctor_map_iff {Z : Scheme.{u}} (U : Z.Opens) {A B : Z.Modules}
    (φ : A ⟶ B) (x : U.toScheme) :
    IsIso ((Stacks.ConormalSequenceRight.stalkAb U.toScheme x).map
        ((Scheme.Modules.restrictFunctor U.ι).map φ)) ↔
      IsIso ((Stacks.ConormalSequenceRight.stalkAb Z (U.ι x)).map φ) := by
  let e := Scheme.Modules.restrictStalkNatIso U.ι x
  have hA : Function.Bijective (e.hom.app A) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (Iso.isIso_hom (e.app A))
  have hB : Function.Bijective (e.hom.app B) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (Iso.isIso_hom (e.app B))
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective ((Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ x).map φ) ↔
    Function.Bijective ((Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor _ (U.ι x)).map φ)
  have hcomp : (e.hom.app B) ∘ ((Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ x).map φ) =
      ((Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor _ (U.ι x)).map φ) ∘
        (e.hom.app A) :=
    funext fun s => congrArg (fun k => (ConcreteCategory.hom k) s) (e.hom.naturality φ)
  rw [← Function.Bijective.of_comp_iff' hB, hcomp]
  exact Function.Bijective.of_comp_iff _ hA

/-- **Maps glue along a partition into open subschemes.** For pairwise disjoint opens covering
`Z`, maps given on each of them are the restrictions of one map. -/
theorem exists_hom_restrict_eq_of_pairwise_disjoint {Z : Scheme.{u}} {ι : Type u}
    (V : ι → Z.Opens) (hV : ⨆ i, V i = ⊤) (hd : Pairwise (Function.onFun Disjoint V))
    {A B : Z.Modules}
    (ψ : ∀ i, (Scheme.Modules.restrictFunctor (V i).ι).obj A ⟶
      (Scheme.Modules.restrictFunctor (V i).ι).obj B) :
    ∃ φ : A ⟶ B, ∀ i, (Scheme.Modules.restrictFunctor (V i).ι).map φ = ψ i := by
  have hg : ⨆ i, (V i).ι ''ᵁ (⊤ : (V i).toScheme.Opens) = ⊤ := by
    simpa only [Scheme.Opens.ι_image_top] using hV
  obtain ⟨φ, hφ, -⟩ := Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover
    (fun i => (V i).ι) hg ψ (fun i j W₁ W₂ W h₁ h₂ => by
      by_cases hij : i = j
      · subst hij
        exact Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_congr _ _ h₁ h₂
      · have hW : W = ⊥ := by
          refine eq_bot_iff.2 fun z hz => ?_
          have hmem : ∀ k (U : (V k).toScheme.Opens), (V k).ι ''ᵁ U = W → z ∈ V k := fun k U h => by
            rw [← h] at hz
            obtain ⟨y, -, rfl⟩ := hz
            exact y.2
          exact (TopologicalSpace.Opens.coe_disjoint.mpr (hd hij)).le_bot
            ⟨hmem i _ h₁, hmem j _ h₂⟩
        subst hW
        ext s
        exact @Subsingleton.elim _ (AlgebraicGeometry.subsingleton_sections_bot Z B) _ _)
  exact ⟨φ, hφ⟩

/-- A point of a scheme with no proper generization is the generic point of an irreducible
component. -/
theorem closure_mem_irreducibleComponents {X : Scheme.{u}} {ξ : X}
    (hξ : ∀ y : X, y ⤳ ξ → y = ξ) : closure {ξ} ∈ irreducibleComponents X := by
  refine ⟨isIrreducible_singleton.closure, fun Z hZ hsub => ?_⟩
  have hZc : IsIrreducible (closure Z) := hZ.closure
  have hη : IsGenericPoint hZc.genericPoint (closure Z) :=
    hZc.isGenericPoint_genericPoint isClosed_closure
  have hηξ : hZc.genericPoint ⤳ ξ := hη.specializes (subset_closure (hsub (subset_closure rfl)))
  rw [hξ _ hηξ] at hη
  rw [hη.def]
  exact subset_closure

/-- The no-proper-generization points of an open are those of the ambient scheme lying in it. -/
theorem forall_specializes_eq_of_isOpenImmersion {X : Scheme.{u}} (U : X.Opens) {ξ : U.toScheme}
    (hξ : ∀ y : U.toScheme, y ⤳ ξ → y = ξ) : ∀ y : X, y ⤳ U.ι ξ → y = U.ι ξ := fun y hy =>
  congrArg Subtype.val
    (hξ ⟨y, hy.mem_open U.isOpen ξ.2⟩ (U.ι.isEmbedding.isInducing.specializes_iff.1 hy))

open ClosedOpenProperFactorization in
/-- **Stacks Project, Tag 0EA0.** Let `S` be Noetherian, `f : X ⟶ Y` a morphism of `FTS S` and
`r ≥ 0`. Assume
1. `Y` is Cohen–Macaulay,
2. `f` factors as an immersion `ι : X ⟶ P` followed by a smooth proper `g : P ⟶ Y`,
3. `f` is Koszul at every `x ∈ X` with `dim 𝒪_{X,x} ≤ 1`, and
4. `trdeg_{κ(f(ξ))} κ(ξ) = r` at every generic point `ξ` of an irreducible component of `X`.

Then, with `ω_{X/Y} = H^{-r}(f^!𝒪_Y)` (`f^!` at any compactification `j`), there is a map
`∧^r Ω_{X/Y} ⟶ ω_{X/Y}` which is an isomorphism at every point where `f` is smooth.

Two steps of the source's proof are corrected. The locally constant function of
[Stacks, Tag 0E9Z] on the local complete intersection locus `U` is `r` only on the pieces where it
equals `r` (in general it is `r - dim 𝒪_{Y,f(ξ)}` at generic points `ξ`); every smooth point lies
on such a piece, and on the others `ω_{X/Y}` vanishes and the map is taken to be zero. The
extension across `X ∖ U` by [Stacks, Tag 0E9I] needs `depth(ω_{X/Y,x}) ≥ 2` there; the `(S₂)`
property of [Stacks, Tag 0E9V] does not give this alone, and it is proved as
`min(2, dim 𝒪_{X,x}) ≤ depth(ω_{X/Y,x})`
(`Stacks.Duality.min_two_ringKrullDim_le_moduleDepth_modulesStalk_homology_upperShriek`). -/
@[stacks 0EA0]
theorem exists_map_exteriorPower_isIso_of_smoothAt {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FTS S} (f : X ⟶ Y) (r : ℕ) (hY : AlgebraicGeometry.IsCohenMacaulay Y.left)
    {P : Scheme.{u}} (ι : X.left ⟶ P) [IsImmersion ι] (g : P ⟶ Y.left) [Smooth g] [IsProper g]
    (hfac : ι ≫ g = f.left)
    (hK : ∀ x : X.left, ringKrullDim (X.left.presheaf.stalk x) ≤ 1 → KoszulAt f.left x)
    (htr : ∀ ξ : X.left, closure {ξ} ∈ irreducibleComponents X.left →
      Stacks.Chow.residueTrdeg f.left ξ = (r : Cardinal))
    (j : CompactificationOf (Over.mk f.left)) :
    ∃ φ : Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) (r : ℤ) ⟶
        upperShriekHomology f j (-(r : ℤ)),
      ∀ x : X.left, InfinitesimalLifting.SmoothAt f.left x →
        IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
          (Sheaf.toRingCat (Opens.grothendieckTopology
            ↥X.left.toLocallyRingedSpace.toRingedSpace.carrier)
            X.left.toLocallyRingedSpace.toRingedSpace.sheaf) x φ) := by
  have hXN : AlgebraicGeometry.IsNoetherian X.left := ⟨⟩
  have htr' : ∀ ξ : X.left, (∀ y : X.left, y ⤳ ξ → y = ξ) →
      Stacks.Chow.residueTrdeg f.left ξ = (r : Cardinal) := fun ξ h =>
    htr ξ (closure_mem_irreducibleComponents h)
  -- the Koszul locus `U`, as an object of `FTS S`
  let U : X.left.Opens := ⟨{x | KoszulAt f.left x}, isOpen_koszulAt f.left⟩
  let XU : FTS S := FTS.mk (U.ι ≫ X.hom)
  let jU : XU ⟶ X := MorphismProperty.Over.homMk U.ι rfl
  have : IsOpenImmersion jU.left := inferInstanceAs (IsOpenImmersion U.ι)
  let fU := jU ≫ f
  let ιU : XU.left ⟶ P := U.ι ≫ ι
  have : IsImmersion ιU := inferInstanceAs (IsImmersion (U.ι ≫ ι))
  have hfacU : ιU ≫ g = fU.left := by
    change (U.ι ≫ ι) ≫ g = U.ι ≫ f.left
    rw [Category.assoc, hfac]
  have hlciU : IsLocalCompleteIntersectionMorphism fU.left := fun z =>
    koszulAt_precomp_openImmersion f.left U.ι z z.2
  have htrU : ∀ ξ : XU.left, closure {ξ} ∈ irreducibleComponents XU.left →
      Stacks.Chow.residueTrdeg fU.left ξ = (r : Cardinal) := fun ξ hξ => by
    let ξ' : U.toScheme := ξ
    have h : ∀ y : U.toScheme, y ⤳ ξ' → y = ξ' := fun y hy =>
      eq_of_specializes_of_closure_mem_irreducibleComponents hξ hy
    have hres := Stacks.Chow.residueTrdeg_of_surjective_residueFieldMap_comp (X' := U.toScheme)
      U.ι f.left ξ' (ConcreteCategory.bijective_of_isIso
        (Scheme.Hom.residueFieldMap (X := U.toScheme) U.ι ξ')).2
    change Stacks.Chow.residueTrdeg (U.ι ≫ f.left) ξ' = _
    rw [hres]
    exact htr' _ (forall_specializes_eq_of_isOpenImmersion U h)
  -- the pieces of `U` of [Stacks, Tag 0E9Z]
  have := isFiniteLocallyFree_conormalSheaf fU ιU g hfacU hlciU
  let C : XU.left.Modules := Stacks.Conormal.conormalSheaf ιU
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := XU.left.ringCatSheaf) C :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.toFiniteLocallyFree C ‹_›
  let mf : XU.left → ℕ := Scheme.Modules.fiberRank C
  have hmf : IsLocallyConstant mf := Scheme.Modules.isLocallyConstant_fiberRank C
  let df : LocallyConstant P ℕ := relativeDimensionFunction g (isCohenMacaulay_fiber_of_smooth g)
  have hT : ∀ m : ℕ, ∃ T : P.Opens, ∀ x : XU.left, x ∈ ιU ⁻¹ᵁ T ↔ mf x = m := by
    intro m
    obtain ⟨t, ht, hts⟩ := ιU.isEmbedding.isInducing.isOpen_iff.1 (hmf.isOpen_fiber m)
    exact ⟨⟨t, ht⟩, fun x => Set.ext_iff.1 hts x⟩
  choose T hT using hT
  let O : ℕ × ℕ → P.Opens := fun a => T a.2 ⊓ dimensionOpen g a.1 ⊓ ιU.coborderRange
  have hmem : ∀ a x, x ∈ ιU ⁻¹ᵁ O a ↔ mf x = a.2 ∧ df (ιU x) = a.1 := by
    intro a x
    have h2 : ιU x ∈ ιU.coborderRange := subset_coborder ⟨x, rfl⟩
    change (ιU x ∈ T a.2 ∧ ιU x ∈ dimensionOpen g a.1) ∧ ιU x ∈ ιU.coborderRange ↔ _
    have h3 := mem_relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) a.1 (ιU x)
    exact ⟨fun h => ⟨(hT a.2 x).1 h.1.1, h3.1 h.1.2⟩,
      fun h => ⟨⟨(hT a.2 x).2 h.1, h3.2 h.2⟩, h2⟩⟩
  have hOd : ∀ a, O a ≤ dimensionOpen g a.1 := fun a => inf_le_left.trans inf_le_right
  have hOc : ∀ a, O a ≤ ιU.coborderRange := fun a => inf_le_right
  have hm : ∀ a, ∀ x ∈ ιU ⁻¹ᵁ O a, Scheme.Modules.fiberRank C x = a.2 :=
    fun a x hx => ((hmem a x).1 hx).1
  let c := j.precompOpen jU.left
  -- the maps on the pieces, with exponent `r`
  have key : ∀ (V : XU.left.Opens) (n : ℤ), n = r →
      (∃ ψ : (Scheme.Modules.restrictFunctor V.ι).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials fU.left) n) ⟶
        (Scheme.Modules.restrictFunctor V.ι).obj (upperShriekHomology fU c (-n)),
        ∀ y : V.toScheme, IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
            (Sheaf.toRingCat (Opens.grothendieckTopology
              ↥V.toScheme.toLocallyRingedSpace.toRingedSpace.carrier)
              V.toScheme.toLocallyRingedSpace.toRingedSpace.sheaf) y ψ) ↔
          InfinitesimalLifting.SmoothAt fU.left (V.ι y)) →
      ∃ ψ : (Scheme.Modules.restrictFunctor V.ι).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials fU.left) (r : ℤ)) ⟶
        (Scheme.Modules.restrictFunctor V.ι).obj (upperShriekHomology fU c (-(r : ℤ))),
        ∀ y : V.toScheme, InfinitesimalLifting.SmoothAt fU.left (V.ι y) →
          IsIso ((Stacks.ConormalSequenceRight.stalkAb V.toScheme y).map ψ) := by
    rintro V n rfl ⟨ψ, hψ⟩
    exact ⟨ψ, fun y hy => (isIso_stalkMap_iff_isIso_stalkAb y ψ).1 ((hψ y).2 hy)⟩
  have hψ : ∀ a : ULift.{u} (ℕ × ℕ), ∃ ψ : (Scheme.Modules.restrictFunctor
        (ιU ⁻¹ᵁ O a.down).ι).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials fU.left) (r : ℤ)) ⟶
        (Scheme.Modules.restrictFunctor (ιU ⁻¹ᵁ O a.down).ι).obj
          (upperShriekHomology fU c (-(r : ℤ))),
        ∀ y : (ιU ⁻¹ᵁ O a.down).toScheme,
          InfinitesimalLifting.SmoothAt fU.left ((ιU ⁻¹ᵁ O a.down).ι y) →
            IsIso ((Stacks.ConormalSequenceRight.stalkAb (ιU ⁻¹ᵁ O a.down).toScheme y).map ψ) := by
    rintro ⟨a⟩
    by_cases h : (a.1 : ℤ) - a.2 = r
    · exact key _ _ h (upperShriekHomology_piece fU ιU g hfacU a.1 (O a) (hOd a) (hOc a) hlciU
        a.2 (hm a) c).2
    · refine ⟨0, fun y hy => absurd ?_ h⟩
      exact Stacks.Duality.SmoothLocus.sub_eq_of_smoothAt fU ιU g hfacU a.1 (O a) (hOd a)
        (hOc a) a.2 (hm a) r htrU y.2 hy
  choose ψ hψs using hψ
  have hcover : ⨆ a : ULift.{u} (ℕ × ℕ), ιU ⁻¹ᵁ O a.down = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨(df (ιU x), mf x)⟩, (hmem _ x).2 ⟨rfl, rfl⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun a : ULift.{u} (ℕ × ℕ) => ιU ⁻¹ᵁ O a.down) := by
    intro a b hab
    refine TopologicalSpace.Opens.coe_disjoint.mp (Set.disjoint_left.2 fun x hxa hxb => hab ?_)
    obtain ⟨h1, h2⟩ := (hmem a.down x).1 hxa
    obtain ⟨h3, h4⟩ := (hmem b.down x).1 hxb
    exact ULift.ext (Prod.ext (h2.symm.trans h4) (h1.symm.trans h3))
  obtain ⟨Φ, hΦ⟩ := exists_hom_restrict_eq_of_pairwise_disjoint _ hcover hdisj ψ
  have hΦs : ∀ y : XU.left, InfinitesimalLifting.SmoothAt fU.left y →
      IsIso ((Stacks.ConormalSequenceRight.stalkAb XU.left y).map Φ) := by
    intro y hy
    let a : ULift.{u} (ℕ × ℕ) := ⟨(df (ιU y), mf y)⟩
    have hya : y ∈ ιU ⁻¹ᵁ O a.down := (hmem _ y).2 ⟨rfl, rfl⟩
    refine (isIso_stalkAb_restrictFunctor_map_iff (ιU ⁻¹ᵁ O a.down) Φ ⟨y, hya⟩).1 ?_
    rw [hΦ a]
    exact hψs a ⟨y, hya⟩ hy
  -- transport to the restriction to `U` of the objects on `X`
  let Ψ := (exteriorPowerRestrictIso jU f (r : ℤ)).hom ≫ Φ ≫
    (upperShriekHomologyRestrictIso jU f j (-(r : ℤ))).hom
  have hΨs : ∀ y : XU.left, InfinitesimalLifting.SmoothAt fU.left y →
      IsIso ((Stacks.ConormalSequenceRight.stalkAb XU.left y).map Ψ) := by
    intro y hy
    have := hΦs y hy
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  -- extension across `X ∖ U`
  have hdepth : ∀ x : X.left, x ∉ (U : Set X.left) →
      let M := TopCat.Presheaf.stalk (C := Ab.{u})
        (upperShriekHomology f j (-(r : ℤ))).val.presheaf x
      let : Module (X.left.presheaf.stalk x) M :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (upperShriekHomology f j (-(r : ℤ))).val x
      (2 : ℕ∞) ≤ Module.depth (X.left.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x)) M := by
    intro x hx
    have h1 : (1 : WithBot ℕ∞) < ringKrullDim (X.left.presheaf.stalk x) :=
      lt_of_not_ge fun h => hx (hK x h)
    have h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.left.presheaf.stalk x) := by
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt h1)
      rw [← hd] at h1 ⊢
      have h1' : (1 : ℕ∞) < d := WithBot.coe_lt_coe.mp h1
      exact WithBot.coe_le_coe.mpr (Order.add_one_le_of_lt h1')
    exact two_le_depth_stalk_upperShriekHomology f j r x
      (isCohenMacaulayLocalRing_stalk Y.left hY _)
      (fun ξ hξ _ => (htr ξ hξ).le) h2
  have := isCoherent_upperShriekHomology f j (-(r : ℤ))
  have hunit := isIso_unit_restrict_pushforward_of_depth_ge_two X.left
    (upperShriekHomology f j (-(r : ℤ))) U hdepth
  obtain ⟨φ, hφ⟩ := exists_hom_restrict_eq_of_isIso_unit U hunit Ψ
  refine ⟨φ, fun x hx => ?_⟩
  have hxU : x ∈ U := koszulAt_of_smoothAt hx
  rw [isIso_stalkMap_iff_isIso_stalkAb]
  refine (isIso_stalkAb_restrictFunctor_map_iff U φ ⟨x, hxU⟩).1 ?_
  rw [hφ]
  exact hΨs ⟨x, hxU⟩ ((InfinitesimalLifting.smoothAt_comp_iff_of_etale U.ι f.left ⟨x, hxU⟩).2 hx)

end Stacks.Duality.SmoothLocus
