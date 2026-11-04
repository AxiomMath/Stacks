module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedPartFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ExtensionByZeroFiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenReductionSupplement

/-!
# Splitting the constant sheaf over the connected components (the first step of Tag 0A5B)

Stacks Tag 0A5B begins: "Since `X` is smooth, we see that `X` is a finite disjoint union of smooth
curves and points. The higher étale cohomology of any sheaf on a point is trivial. Hence we may
assume `X` is a smooth curve." This file carries out that reduction for the eight assertions of
Tag 03SC and the constant sheaf `Z/ℓ` on a normal separated scheme `X` of finite type and
dimension at most one over an algebraically closed field.

* A clopen decomposition `X = U ⊔ V` splits a constructible sheaf killed by a prime: the
  localization sequence of Tag 095L is `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0`, extension by zero
  along the clopen `j` is the direct image `j_*`, and Tag 0A5D moves the eight assertions from
  `U` and `V` to `X` (`TorsionCurveAssertions.of_isClopen`).
* The eight assertions hold for every sheaf on a scheme finite over the field
  (`TorsionCurveAssertions.of_isFinite`): this is the point case.
* A connected normal Noetherian scheme is integral; of dimension one it is a curve, and smooth
  over the perfect field `k` because a normal scheme of dimension at most one is regular
  (Tag 0BX2).
* Induction on the number of irreducible components
  (`TorsionCurveAssertions.constantZModAb_of_smoothCurve`) reduces the eight assertions for `Z/ℓ`
  on `X` to the same on every smooth curve over `k`.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_isClopen`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_isFinite`.
* `Stacks.EtaleCohomology.TorsionCurveAssertions.constantZModAb_of_smoothCurve`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- An open immersion with closed image is a closed immersion. -/
theorem isClosedImmersion_of_isOpenImmersion_of_isClosed {X U : Scheme.{u}} (ι : U ⟶ X)
    [IsOpenImmersion ι] (hι : IsClosed (Set.range ι.base)) : IsClosedImmersion ι :=
  .of_isPreimmersion _ hι

/-- **Extension by zero along a clopen immersion is the direct image.** If `j : V ⟶ X` is both an
open and a closed immersion, with open complement `i : U ⟶ X`, then `j_! H ≅ j_* H`. -/
theorem nonempty_extensionByZero_iso_directImage {X V U : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion j] (i : U ⟶ X) [IsOpenImmersion i]
    (hji : Set.range i.base = (Set.range j.base)ᶜ)
    (H : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty ((extensionByZero.{u, u + 1} j).obj H ≅
      (etaleAbelianDirectImage.{u, u + 1} j).obj H) := by
  set G := (extensionByZero.{u, u + 1} j).obj H
  have hS := openClosedShortComplex_shortExact.{u, u + 1} j i hji G
  have hdisj : Disjoint (Set.range i.base) (Set.range j.base) := hji ▸ disjoint_compl_left
  have hz₀ := isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, u + 1} i j hdisj H
  have hz : IsZero ((extensionByZero.{u, u + 1} i).obj ((etaleRestriction.{u, u + 1} i).obj G)) :=
    (extensionByZero.{u, u + 1} i).map_isZero
      (hz₀.of_iso ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} i).app G).symm)
  have : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} j).unit.app G) :=
    hS.isIso_g_iff.mpr hz
  obtain ⟨e⟩ := nonempty_inverseImage_extensionByZero_iso j H
  exact ⟨asIso ((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} j).unit.app G) ≪≫
    (etaleAbelianDirectImage.{u, u + 1} j).mapIso e⟩

/-- The restriction of a constructible sheaf along an open immersion with closed image is
constructible. -/
theorem IsConstructibleSmallEtaleSheaf.etaleRestriction_of_isClosed {X U : Scheme.{u}} (ι : U ⟶ X)
    [IsOpenImmersion ι] (hι : IsClosed (Set.range ι.base))
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F) :
    IsConstructibleSmallEtaleSheaf ((etaleRestriction.{u, u + 1} ι).obj F) := by
  have := isClosedImmersion_of_isOpenImmersion_of_isClosed ι hι
  obtain ⟨B, hX, hB⟩ := IsConstructibleSmallEtaleSheaf.inverseImage_of_mono ι hF
  exact ⟨B, hX, IsConstructibleEtaleSheafIn.of_iso
    ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} ι).app F) hB⟩

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
theorem isNoetherian_opens {Y : Scheme.{u}} [IsNoetherian Y] (V : Y.Opens) :
    IsNoetherian (V : Scheme.{u}) :=
  have : CompactSpace (V : Scheme.{u}) :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact (V : Set Y))
  { }

/-- A point of an open subscheme lies in the open. -/
theorem ι_apply_mem {Y : Scheme.{u}} (U : Y.Opens) (x : (U : Scheme.{u})) : U.ι.base x ∈ U := by
  have : U.ι.base x ∈ Set.range U.ι.base := ⟨x, rfl⟩
  rwa [U.range_ι] at this

/-- A point of an open `U` lies in the image of the inclusion of a smaller open `W` exactly when
its image in `Y` lies in `W`. -/
theorem mem_range_homOfLE {Y : Scheme.{u}} {U W : Y.Opens} (h : W ≤ U) (x : (U : Scheme.{u})) :
    x ∈ Set.range (Y.homOfLE h).base ↔ U.ι.base x ∈ W := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact ι_apply_mem W y
  · intro hx
    obtain ⟨y, hy⟩ : U.ι.base x ∈ Set.range W.ι.base := by rwa [W.range_ι]
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, hy]

/-- In a space with finitely many irreducible components, an open `W ⊆ V` disjoint from a
nonempty open `W' ⊆ V` meets fewer irreducible components than `V`. -/
theorem ncard_irreducibleComponents_inter_lt {α : Type*} [TopologicalSpace α]
    (hfin : (irreducibleComponents α).Finite) {V W W' : Set α} (hW : W ⊆ V) (hW' : W' ⊆ V)
    (hWo : IsOpen W) (hW'o : IsOpen W') (hWW' : Disjoint W W') (hne : W'.Nonempty) :
    {Z | Z ∈ irreducibleComponents α ∧ (Z ∩ W).Nonempty}.ncard <
      {Z | Z ∈ irreducibleComponents α ∧ (Z ∩ V).Nonempty}.ncard := by
  obtain ⟨x, hx⟩ := hne
  have hsub : {Z | Z ∈ irreducibleComponents α ∧ (Z ∩ W).Nonempty} ⊆
      {Z | Z ∈ irreducibleComponents α ∧ (Z ∩ V).Nonempty} :=
    fun Z hZ => ⟨hZ.1, hZ.2.mono (Set.inter_subset_inter_right _ hW)⟩
  refine Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).mpr ⟨irreducibleComponent x,
    ⟨irreducibleComponent_mem_irreducibleComponents x, x, mem_irreducibleComponent, hW' hx⟩,
    fun hZ => ?_⟩) (hfin.subset fun Z hZ => hZ.1)
  obtain ⟨y, -, hyW⟩ := (isIrreducible_irreducibleComponent (x := x)).isPreirreducible _ _
    hWo hW'o hZ.2 ⟨x, mem_irreducibleComponent, hx⟩
  exact Set.disjoint_left.mp hWW' hyW.1 hyW.2

namespace TorsionCurveAssertions

variable {k : Type u} [Field k]

/-- **The eight assertions over a clopen decomposition.** Let `ιU : U ⟶ X` and `ιV : V ⟶ X` be
open immersions with complementary images, and `F` constructible and killed by a prime `ℓ`. If
the eight assertions hold for `F|_U` over `U` and for `F|_V` over `V`, they hold for `F` over
`X`. -/
theorem of_isClopen {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsNoetherian X]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : IsConstructibleSmallEtaleSheaf F)
    (hℓF : ℓ • 𝟙 F = 0) {U V : Scheme.{u}} (ιU : U ⟶ X) (ιV : V ⟶ X) [IsOpenImmersion ιU]
    [IsOpenImmersion ιV] (hUV : Set.range ιV.base = (Set.range ιU.base)ᶜ)
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hUF : TorsionCurveAssertions (ιU ≫ f) ((etaleRestriction.{u, u + 1} ιU).obj F))
    (hVF : TorsionCurveAssertions (ιV ≫ f) ((etaleRestriction.{u, u + 1} ιV).obj F)) :
    TorsionCurveAssertions f F := by
  have hVcl : IsClosed (Set.range ιV.base) :=
    hUV ▸ ιU.isOpenEmbedding.isOpen_range.isClosed_compl
  have hVU : Set.range ιU.base = (Set.range ιV.base)ᶜ := by rw [hUV, compl_compl]
  have hUcl : IsClosed (Set.range ιU.base) :=
    hVU ▸ ιV.isOpenEmbedding.isOpen_range.isClosed_compl
  have := isClosedImmersion_of_isOpenImmersion_of_isClosed ιU hUcl
  have := isClosedImmersion_of_isOpenImmersion_of_isClosed ιV hVcl
  have hS := openClosedShortComplex_shortExact.{u, u + 1} ιU ιV hUV F
  refine of_shortExact f hS ?_ ?_
  · obtain ⟨e⟩ := nonempty_extensionByZero_iso_directImage ιV ιU hVU
      ((etaleRestriction.{u, u + 1} ιV).obj F)
    exact of_iso f e.symm (of_directImage_of_nsmul f ιV hℓ
      (IsConstructibleSmallEtaleSheaf.etaleRestriction_of_isClosed ιV hVcl hF)
      (nsmul_id_map_eq_zero _ hℓF) hVF)
  · exact of_iso f ((etaleAbelianDirectImage.{u, u + 1} ιU).mapIso
      ((etaleAbelianInverseImageRestrictionIso.{u, u + 1} ιU).app F)).symm
      (of_directImage_of_nsmul f ιU hℓ
        (IsConstructibleSmallEtaleSheaf.etaleRestriction_of_isClosed ιU hUcl hF)
        (nsmul_id_map_eq_zero _ hℓF) hUF)

/-- **The constant sheaf over a clopen decomposition.** If the eight assertions hold for `Z/ℓ`
over `U` and over `V`, for open immersions `U ⟶ X` and `V ⟶ X` with complementary images, then
they hold for `Z/ℓ` over `X`. -/
theorem constantZModAb_of_isClopen {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsNoetherian X]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] {ℓ : ℕ} (hℓ : ℓ.Prime)
    {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V] (ιU : U ⟶ X) (ιV : V ⟶ X)
    [IsOpenImmersion ιU] [IsOpenImmersion ιV] (hUV : Set.range ιV.base = (Set.range ιU.base)ᶜ)
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hU : TorsionCurveAssertions (ιU ≫ f) (StrongTorsionCurveAssertions.constantZModAb U ℓ))
    (hV : TorsionCurveAssertions (ιV ≫ f) (StrongTorsionCurveAssertions.constantZModAb V ℓ)) :
    TorsionCurveAssertions f (StrongTorsionCurveAssertions.constantZModAb X ℓ) :=
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  of_isClopen f hℓ _ (isConstructibleEtaleSheaf_constantSheaf X _)
    (nsmul_id_constantSheaf_zmod.{u + 1} ℓ X.smallEtaleTopology) ιU ιV hUV
    (of_iso _ (etaleRestrictionConstantSheafIso ιU _).symm hU)
    (of_iso _ (etaleRestrictionConstantSheafIso ιV _).symm hV)

/-- **Induction on the components meeting an open.** On a normal Noetherian scheme `Y`, if the
eight assertions hold for `Z/ℓ` over every connected open, they hold for `Z/ℓ` over every
open. A disconnected open splits into two disjoint opens, each meeting fewer irreducible
components of `Y`, and `constantZModAb_of_isClopen` glues. -/
theorem constantZModAb_opens_of_isConnected {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k))
    [IsNoetherian Y] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hconn : ∀ V : Y.Opens, _root_.IsConnected (V : Set Y) →
      TorsionCurveAssertions (V.ι ≫ pY) (StrongTorsionCurveAssertions.constantZModAb V ℓ))
    (V : Y.Opens) :
    TorsionCurveAssertions (V.ι ≫ pY) (StrongTorsionCurveAssertions.constantZModAb V ℓ) := by
  suffices h : ∀ n : ℕ, ∀ V : Y.Opens,
      {Z | Z ∈ irreducibleComponents (Y : Type u) ∧ (Z ∩ (V : Set Y)).Nonempty}.ncard = n →
      TorsionCurveAssertions (V.ι ≫ pY) (StrongTorsionCurveAssertions.constantZModAb V ℓ) from
    h _ V rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V hn
  by_cases hne : (V : Set Y).Nonempty
  swap
  · have : IsEmpty (V : Scheme.{u}) := ⟨fun x => hne ⟨x.1, x.2⟩⟩
    exact of_isZero _ (isZero_of_isEmpty _)
  by_cases hpc : _root_.IsPreconnected (V : Set Y)
  · exact hconn V ⟨hne, hpc⟩
  rw [_root_.IsPreconnected] at hpc
  push Not at hpc
  obtain ⟨u₁, u₂, hu₁, hu₂, hcov, hV₁, hV₂, hdisj⟩ := hpc
  let V₁ : Y.Opens := V ⊓ ⟨u₁, hu₁⟩
  let V₂ : Y.Opens := V ⊓ ⟨u₂, hu₂⟩
  have h₁ : V₁ ≤ V := inf_le_left
  have h₂ : V₂ ≤ V := inf_le_left
  have hdisj' : Disjoint (V₁ : Set Y) V₂ := Set.disjoint_left.mpr fun y hy₁ hy₂ =>
    (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hy₁.1, hy₁.2, hy₂.2⟩
  have hlt₁ := ncard_irreducibleComponents_inter_lt NoetherianSpace.finite_irreducibleComponents
    h₁ h₂ V₁.isOpen V₂.isOpen hdisj' hV₂
  have hlt₂ := ncard_irreducibleComponents_inter_lt NoetherianSpace.finite_irreducibleComponents
    h₂ h₁ V₂.isOpen V₁.isOpen
    hdisj'.symm hV₁
  subst hn
  have := isNoetherian_opens V
  have := isNoetherian_opens V₁
  have := isNoetherian_opens V₂
  have hrange : Set.range (Y.homOfLE h₂).base = (Set.range (Y.homOfLE h₁).base)ᶜ := by
    ext x
    rw [Set.mem_compl_iff, mem_range_homOfLE, mem_range_homOfLE]
    have hxV := ι_apply_mem V x
    constructor
    · exact fun hx₂ hx₁ => Set.disjoint_left.mp hdisj' hx₁ hx₂
    · intro hx₁
      rcases hcov hxV with hx | hx
      · exact absurd ⟨hxV, hx⟩ hx₁
      · exact ⟨hxV, hx⟩
  refine constantZModAb_of_isClopen (V.ι ≫ pY) hℓ (Y.homOfLE h₁) (Y.homOfLE h₂) hrange ?_ ?_ <;>
    rw [← Category.assoc, Scheme.homOfLE_ι]
  · exact ih _ hlt₁ V₁ rfl
  · exact ih _ hlt₂ V₂ rfl

variable [IsAlgClosed k]

/-- **The eight assertions on a scheme finite over the field**, for every sheaf: the higher
cohomology vanishes, the global sections of a constructible sheaf are finite, and the comparison
maps are bijective. This is the point case of Tag 0A5B. -/
theorem of_isFinite {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsFinite f]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : TorsionCurveAssertions f Q := by
  have : IsFinite (𝟙 X ≫ f) := by rwa [Category.id_comp]
  have : Finite X := finite_of_isFinite_over_field f
  have : IsEmpty ((⊥ : X.Opens) : Scheme.{u}) := ⟨fun x => x.2⟩
  have hij : Set.range (⊥ : X.Opens).ι.base = (Set.range (𝟙 X : X ⟶ X).base)ᶜ := by simp
  exact of_isZero_etaleRestriction_of_constructible f (𝟙 X) (⊥ : X.Opens).ι hij Q
    (isZero_of_isEmpty _) finite_sheafH_zero_of_isConstructibleEtaleSheaf

/-- A space of Krull dimension at most one which is not of dimension zero, and nonnegative, has
dimension one. -/
theorem topologicalKrullDim_eq_one_of_ne_zero {α : Type*} [TopologicalSpace α]
    (h0 : 0 ≤ topologicalKrullDim α) (hle : topologicalKrullDim α ≤ 1)
    (hne : topologicalKrullDim α ≠ 0) : topologicalKrullDim α = 1 := by
  generalize topologicalKrullDim α = d at h0 hle hne ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hle (by decide)
    | coe n =>
      have hle' : n ≤ 1 := by exact_mod_cast hle
      have hne' : n ≠ 0 := by
        rintro rfl
        exact hne rfl
      obtain rfl : n = 1 := by omega
      rfl

/-- **The reduction of Tag 0A5B to smooth curves.** Let `Y` be a normal separated scheme of
finite type and dimension at most one over an algebraically closed field `k`. If the eight
assertions of Tag 03SC hold for `Z/ℓ` on every smooth curve over `k`, they hold for `Z/ℓ` on `Y`.

`Y` is the disjoint union of its connected components, each a connected normal Noetherian
scheme, hence integral; one of dimension zero is finite over `k`
(`TorsionCurveAssertions.of_isFinite`), one of dimension one is a curve, regular by Tag 0BX2 and
so smooth over the perfect field `k`. -/
theorem constantZModAb_of_smoothCurve {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hsm : ∀ (C : Scheme.{u}) (pC : C ⟶ Spec (.of k)) [IsCurve k pC] [Smooth pC],
      TorsionCurveAssertions pC (StrongTorsionCurveAssertions.constantZModAb C ℓ))
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) [IsSeparated pY] [LocallyOfFiniteType pY]
    [QuasiCompact pY] [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim Y ≤ 1) (hN : IsNormal Y) :
    TorsionCurveAssertions pY (StrongTorsionCurveAssertions.constantZModAb Y ℓ) := by
  have : IsNoetherian Y := isNoetherian_of_finiteType pY
  have hconn : ∀ V : Y.Opens, _root_.IsConnected (V : Set Y) →
      TorsionCurveAssertions (V.ι ≫ pY) (StrongTorsionCurveAssertions.constantZModAb V ℓ) := by
    intro V hV
    have := isNoetherian_opens V
    have : ConnectedSpace (V : Scheme.{u}) := isConnected_iff_connectedSpace.mp hV
    have : IrreducibleSpace (V : Scheme.{u}) :=
      irreducibleSpace_of_isNormal_of_connectedSpace (V : Scheme.{u}) inferInstance
    have : IsIntegral (V : Scheme.{u}) := isIntegral_of_irreducibleSpace_of_isReduced _
    have hdimV : topologicalKrullDim (V : Scheme.{u}) ≤ 1 :=
      (Topology.IsInducing.topologicalKrullDim_le
        V.ι.isOpenEmbedding.isEmbedding.isInducing).trans hdim
    have h0 : 0 ≤ topologicalKrullDim (V : Scheme.{u}) := by
      have : Nonempty (IrreducibleCloseds (V : Scheme.{u})) :=
        ⟨irreducibleClosedsOfPoint (Classical.arbitrary _)⟩
      exact Order.krullDim_nonneg
    by_cases hz : topologicalKrullDim (V : Scheme.{u}) = 0
    · have : IsFinite (V.ι ≫ pY) := isFinite_of_finiteType_of_dimension_zero k _ hz
      exact of_isFinite _ _
    · have h1 := topologicalKrullDim_eq_one_of_ne_zero h0 hdimV hz
      have : IsCurve k (V.ι ≫ pY) := { topologicalKrullDim_eq_one := h1 }
      have : Smooth (V.ι ≫ pY) := smooth_of_isRegular_of_perfectField k _
        (isRegular_of_isNormal_of_topologicalKrullDim_le_one _ hdimV)
      exact hsm _ _
  have htop := constantZModAb_opens_of_isConnected pY hℓ hconn ⊤
  have := isNoetherian_opens (⊤ : Y.Opens)
  have := isNoetherian_opens (⊥ : Y.Opens)
  have : IsEmpty ((⊥ : Y.Opens) : Scheme.{u}) := ⟨fun x => x.2⟩
  have hrange : Set.range (⊥ : Y.Opens).ι.base = (Set.range (⊤ : Y.Opens).ι.base)ᶜ := by simp
  exact constantZModAb_of_isClopen pY hℓ (⊤ : Y.Opens).ι (⊥ : Y.Opens).ι hrange htop
    (of_isZero _ (isZero_of_isEmpty _))

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
