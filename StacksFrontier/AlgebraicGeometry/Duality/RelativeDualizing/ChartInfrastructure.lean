module

public import StacksFrontier.RingTheory.Dualizing.NoetherianPairings.Ports.DualizingModuleLocalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.LocalizedRestriction
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affine charts for the relative dualizing module of a quasi-finite morphism

This file concerns the affine charts of a morphism `f : Y ⟶ X`, the normalised localization maps of
algebraic relative dualizing modules, and restriction of sections of a sheaf of modules.

## Main definitions

* `Stacks.Discriminant.RelativeDualizingChartIndex` indexes the affine charts of `f` lying in a
  given open of the source: a pair of an affine open `U` of the base and an affine open `V` of the
  source with `V ≤ f ⁻¹ᵁ U` and `V` inside the given open.
* `Stacks.Discriminant.relativeDualizingChartOpen` is the source-side open of such a chart.
* `Stacks.Discriminant.DualizingChartOverlapRefinement` records the data refining two charts at a
  common point of their source-side opens to a single chart: a principal open of the base presented
  as a principal open of either base chart, and a principal open of the source presented as a
  principal open of either source chart.

## Main results

* `Stacks.Discriminant.exists_localizedDualizingModuleMap_eq_id'`: a localization map of algebraic
  dualizing modules whose induced comparison of Tag 0BT2 part (2) is the identity always *exists*,
  and `Stacks.Discriminant.exists_localizedDualizingModuleMap_eq_id` builds one from any
  localization map of the dualizing module of `F`.
* `Stacks.Discriminant.localizedDualizingModuleMap_eq_of_eq_id`: that map is *unique*.
* `Stacks.Discriminant.relativeDualizingChart_cover`: the source-side opens of the charts lying in
  an open `W` of the source cover `W`.
* `Stacks.Discriminant.relativeDualizingChart_basis`: those opens, for `W = ⊤`, form a basis of the
  source.
* `Stacks.Discriminant.exists_dualizingChartOverlapRefinement`: two charts can be refined at any
  common point.
* `AlgebraicGeometry.Scheme.Modules.restrictionLinearMap_comp` and
  `AlgebraicGeometry.Scheme.Modules.restrictionLinearMap_heq_of_eq`: functoriality of restriction
  of sections of a sheaf of modules, and its invariance under equality of the source open.

## Implementation notes

`localizedDualizingModuleMap_eq_of_eq_id` is proved by transporting the `IsLocalizedModule`
comparison of the two maps along naturality in the source factorization
(`localizedModule_dualizingModule_equiv_natural_in_source`), taking both factorizations equal so
that the comparison of Tag 0BT1 is the identity. The comparison is first upgraded from a `B`-linear
to a `Bg`-linear map, which is where the surjectivity of the localization is used.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u v w x y z

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction of sections of a sheaf of modules is functorial. -/
public lemma restrictionLinearMap_comp {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (i : U ⟶ V) (j : V ⟶ W) (s : Γ(M, W)) :
    restrictionLinearMap M i (restrictionLinearMap M j s) =
      restrictionLinearMap M (i ≫ j) s := by
  show ((M.presheaf.map j.op) ≫ (M.presheaf.map i.op)).hom s =
    (M.presheaf.map (i ≫ j).op).hom s
  rw [show (i ≫ j).op = j.op ≫ i.op from Subsingleton.elim _ _, ← M.presheaf.map_comp]

/-- Restriction of sections of a sheaf of modules depends only on the pair of opens, so two
restriction maps with equal sources are heterogeneously equal on every section. -/
public lemma restrictionLinearMap_heq_of_eq {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hUV : U = V) (i : U ⟶ W) (j : V ⟶ W) (s : Γ(M, W)) :
    HEq (restrictionLinearMap M i s) (restrictionLinearMap M j s) := by
  cases hUV
  obtain rfl : i = j := Subsingleton.elim _ _
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Discriminant

/-- A localization map of algebraic relative dualizing modules is determined by the requirement
that the comparison it induces (Tag 0BT2 part (2)) is the identity. -/
public theorem localizedDualizingModuleMap_eq_of_eq_id
    {A B Bg : Type u} [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra A Bg] [Algebra B Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, u, u} A B)
    (G : FiniteOpenFactorization.{u, u, u} A Bg)
    [Module B (dualizingModule G)]
    [IsScalarTower B Bg (dualizingModule G)]
    (r₁ r₂ : dualizingModule F →ₗ[B] dualizingModule G)
    (hr₁ : IsLocalizedModule (Submonoid.powers g) r₁)
    (hr₂ : IsLocalizedModule (Submonoid.powers g) r₂)
    (h₁ : ∀ m : dualizingModule G,
      localizedModule_dualizingModule_equiv g F G r₁ hr₁ m = m)
    (h₂ : ∀ m : dualizingModule G,
      localizedModule_dualizingModule_equiv g F G r₂ hr₂ m = m) :
    r₁ = r₂ := by
  let cB : dualizingModule G ≃ₗ[B] dualizingModule G :=
    IsLocalizedModule.linearEquiv (Submonoid.powers g) r₁ r₂
  have hcB (x : dualizingModule F) : cB (r₁ x) = r₂ x := by
    simp [cB]
  let comparison : dualizingModule G →ₗ[Bg] dualizingModule G :=
    { toFun := cB
      map_add' := cB.map_add
      map_smul' := by
        intro q m
        obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g) q
        let sB : B := s
        have heq : algebraMap B Bg sB • cB (q • m) =
            algebraMap B Bg sB • (q • cB m) := by
          calc
            algebraMap B Bg sB • cB (q • m) = cB (sB • (q • m)) := by
              rw [IsScalarTower.algebraMap_smul (R := B) (A := Bg), ← cB.map_smul]
            _ = cB ((algebraMap B Bg b) • m) := by
              congr 1
              rw [← IsScalarTower.algebraMap_smul (R := B) (A := Bg),
                smul_smul, mul_comm, hs]
            _ = algebraMap B Bg b • cB m := by
              rw [IsScalarTower.algebraMap_smul (R := B) (A := Bg), cB.map_smul,
                IsScalarTower.algebraMap_smul (R := B) (A := Bg)]
            _ = algebraMap B Bg s • (q • cB m) := by rw [smul_smul, mul_comm, hs]
        have hinj : Function.Injective (fun x : dualizingModule G =>
            algebraMap B Bg sB • x) := by
          have hunit := (Module.End.isUnit_iff _).mp (hr₁.map_units s)
          intro x y hxy
          apply hunit.1
          simpa [Module.algebraMap_end_apply, IsScalarTower.algebraMap_smul] using hxy
        exact hinj heq }
  have hcomparison (x : dualizingModule F) :
      comparison (r₁ x) = r₂ (dualizingModuleEquiv F F x) := by
    show cB (r₁ x) = r₂ (dualizingModuleEquiv F F x)
    rw [dualizingModuleEquiv_refl]
    exact hcB x
  have hcomparison_id : ∀ m : dualizingModule G, comparison m = m := by
    intro m
    have hnat := localizedModule_dualizingModule_equiv_natural_in_source
      g F F G G r₁ hr₁ r₂ hr₂ comparison hcomparison m
    rw [h₁, h₂, dualizingModuleEquiv_refl] at hnat
    exact hnat.symm
  ext x
  have h := hcomparison x
  rw [hcomparison_id] at h
  change r₁ x = r₂ (dualizingModuleEquiv F F x) at h
  rw [dualizingModuleEquiv_refl] at h
  exact h

/-- A normalised localization map of algebraic relative dualizing modules, one whose induced
comparison (Tag 0BT2 part (2)) is the identity, exists as soon as the dualizing module of `F` has a
localization map at `g`. -/
public theorem exists_localizedDualizingModuleMap_eq_id
    {A : Type u} {B : Type v} {Bg : Type w} {M : Type x}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra A Bg] [Algebra B Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, w, z} A Bg)
    [AddCommGroup M] [Module B M] [Module Bg M] [IsScalarTower B Bg M]
    (r₀ : dualizingModule F →ₗ[B] M)
    (hr₀ : IsLocalizedModule (Submonoid.powers g) r₀)
    [Module B (dualizingModule G)]
    [IsScalarTower B Bg (dualizingModule G)] :
    ∃ (r : dualizingModule F →ₗ[B] dualizingModule G)
      (hr : IsLocalizedModule (Submonoid.powers g) r),
      ∀ m : dualizingModule G,
        localizedModule_dualizingModule_equiv g F G r hr m = m := by
  let e : M ≃ₗ[Bg] dualizingModule G :=
    localizedModule_dualizingModule_equiv g F G r₀ hr₀
  let eB : M ≃ₗ[B] dualizingModule G := e.restrictScalars B
  refine ⟨eB.toLinearMap.comp r₀,
    IsLocalizedModule.of_linearEquiv (Submonoid.powers g) r₀ eB, ?_⟩
  intro m
  obtain ⟨n, rfl⟩ := e.surjective m
  have hcomp : ∀ x : dualizingModule F,
      e.toLinearMap (r₀ x) =
        (eB.toLinearMap.comp r₀) (dualizingModuleEquiv F F x) := by
    intro x
    rw [dualizingModuleEquiv_refl]
    rfl
  have hnat := localizedModule_dualizingModule_equiv_natural_in_source
    g F F G G r₀ hr₀ (eB.toLinearMap.comp r₀)
    (IsLocalizedModule.of_linearEquiv (Submonoid.powers g) r₀ eB)
    e.toLinearMap hcomp n
  rw [dualizingModuleEquiv_refl] at hnat
  exact hnat.symm

/-- A normalised localization map of algebraic relative dualizing modules, one whose induced
comparison (Tag 0BT2 part (2)) is the identity, always exists. -/
public theorem exists_localizedDualizingModuleMap_eq_id'
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra A Bg] [Algebra B Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.QuasiFinite A B]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, y} A B)
    (G : FiniteOpenFactorization.{u, w, z} A Bg)
    [Module B (dualizingModule G)]
    [IsScalarTower B Bg (dualizingModule G)] :
    ∃ (r : dualizingModule F →ₗ[B] dualizingModule G)
      (hr : IsLocalizedModule (Submonoid.powers g) r),
      ∀ m : dualizingModule G,
        localizedModule_dualizingModule_equiv g F G r hr m = m := by
  let : Module Bg (LocalizedModule (Submonoid.powers g) (dualizingModule F)) :=
    LocalizedModule.moduleOfIsLocalization (T := Bg)
  exact exists_localizedDualizingModuleMap_eq_id g F G
    (LocalizedModule.mkLinearMap (Submonoid.powers g) (dualizingModule F)) inferInstance

/-- The affine charts of `f : Y ⟶ X` lying inside an open `W` of the source: an affine open `U` of
the base together with an affine open `V` of the source contained in both `f ⁻¹ᵁ U` and `W`. -/
public abbrev RelativeDualizingChartIndex {X Y : Scheme.{u}} (f : Y ⟶ X) (W : Y.Opens) :=
  Σ U : X.affineOpens, {V : Y.affineOpens // V.1 ≤ f ⁻¹ᵁ U.1 ∧ V.1 ≤ W}

/-- The source-side open of an affine chart. -/
public def relativeDualizingChartOpen {X Y : Scheme.{u}} {f : Y ⟶ X}
    {W : Y.Opens} (i : RelativeDualizingChartIndex f W) : Y.Opens := i.2.1.1

/-- Every point of `W` lies in the source-side open of some affine chart inside `W`. -/
private lemma exists_relativeDualizingChartIndex_of_mem {X Y : Scheme.{u}} (f : Y ⟶ X)
    {W : Y.Opens} {y : Y} (hy : y ∈ W) :
    ∃ i : RelativeDualizingChartIndex f W, y ∈ relativeDualizingChartOpen i := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
  have hyWU : y ∈ W ⊓ f ⁻¹ᵁ U := ⟨hy, hyU⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVWU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyWU (W.2.inter (f ⁻¹ᵁ U).2)
  exact ⟨⟨⟨U, hU⟩, ⟨⟨V, hV⟩, ⟨hVWU.trans inf_le_right, hVWU.trans inf_le_left⟩⟩⟩, hyV⟩

/-- The source-side opens of the affine charts lying inside `W` cover `W`. -/
public lemma relativeDualizingChart_cover {X Y : Scheme.{u}} (f : Y ⟶ X)
    (W : Y.Opens) : iSup (relativeDualizingChartOpen (f := f) (W := W)) = W := by
  refine le_antisymm (iSup_le fun i => i.2.2.2) fun y hy => ?_
  obtain ⟨i, hi⟩ := exists_relativeDualizingChartIndex_of_mem f hy
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

/-- The source-side opens of the affine charts of `f` form a basis of the source. -/
public lemma relativeDualizingChart_basis {X Y : Scheme.{u}} (f : Y ⟶ X) :
    TopologicalSpace.Opens.IsBasis (Set.range (relativeDualizingChartOpen
      (f := f) (W := ⊤))) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro O y hy
  obtain ⟨i, hyi⟩ := exists_relativeDualizingChartIndex_of_mem f hy
  exact ⟨i.2.1.1, ⟨⟨i.1, i.2.1, i.2.2.1, le_top⟩, rfl⟩, hyi, i.2.2.2⟩

/-- Data refining two affine charts of `f` at a common point `y` of their source-side opens: a
principal open of the base presented as a principal open of either base chart and containing `f y`,
a principal open of the first source chart inside the second and over that base open, and a
principal open of the source containing `y` presented as a principal open of either source
chart. -/
public structure DualizingChartOverlapRefinement {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U₁ U₂ : X.affineOpens) (V₁ V₂ : Y.affineOpens)
    (hV₁U₁ : V₁.1 ≤ f ⁻¹ᵁ U₁.1) (hV₂U₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1)
    (y : Y) (hy₁ : y ∈ V₁.1) (hy₂ : y ∈ V₂.1) where
  /-- The refining base function on the first base chart. -/
  base₁ : Γ(X, U₁.1)
  /-- The refining base function on the second base chart. -/
  base₂ : Γ(X, U₂.1)
  /-- The two base functions cut out the same open of the base. -/
  base_eq : X.basicOpen base₁ = X.basicOpen base₂
  /-- The image of `y` lies in that open. -/
  base_mem : f y ∈ X.basicOpen base₁
  /-- The refining source function on the first source chart. -/
  source₁ : Γ(Y, V₁.1)
  /-- `y` lies in the open it cuts out. -/
  source₁_mem : y ∈ Y.basicOpen source₁
  /-- That open lies in the second source chart. -/
  source₁_le₂ : Y.basicOpen source₁ ≤ V₂.1
  /-- That open lies over the refined base open. -/
  source₁_base : Y.basicOpen source₁ ≤ f ⁻¹ᵁ (X.basicOpen base₁)
  /-- A further refining function on that open. -/
  source₂₁ : Γ(Y, Y.basicOpen source₁)
  /-- The same open presented on the second source chart. -/
  source₂₂ : Γ(Y, V₂.1)
  /-- The two presentations agree. -/
  source₂_eq : Y.basicOpen source₂₁ = Y.basicOpen source₂₂
  /-- `y` lies in the resulting open. -/
  source₂_mem : y ∈ Y.basicOpen source₂₁

/-- Any two affine charts of `f` admit a common refinement at any common point of their source-side
opens. -/
public lemma exists_dualizingChartOverlapRefinement {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U₁ U₂ : X.affineOpens) (V₁ V₂ : Y.affineOpens)
    (hV₁U₁ : V₁.1 ≤ f ⁻¹ᵁ U₁.1) (hV₂U₂ : V₂.1 ≤ f ⁻¹ᵁ U₂.1)
    (y : Y) (hy₁ : y ∈ V₁.1) (hy₂ : y ∈ V₂.1) :
    Nonempty (DualizingChartOverlapRefinement f U₁ U₂ V₁ V₂ hV₁U₁ hV₂U₂ y hy₁ hy₂) := by
  obtain ⟨a₁, a₂, ha, hya⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f y) ⟨hV₁U₁ hy₁, hV₂U₂ hy₂⟩
  let Ua₁ : X.affineOpens := X.affineBasicOpen a₁
  have hyUa : y ∈ f ⁻¹ᵁ Ua₁.1 := hya
  obtain ⟨g, hg, hyg⟩ := V₁.2.exists_basicOpen_le
    ⟨y, show y ∈ V₂.1 ⊓ f ⁻¹ᵁ Ua₁.1 from ⟨hy₂, hyUa⟩⟩ hy₁
  let W₁ : Y.affineOpens := ⟨Y.basicOpen g, V₁.2.basicOpen g⟩
  have hyW₁ : y ∈ W₁.1 := hyg
  have hW₁V₂ : W₁.1 ≤ V₂.1 := hg.trans inf_le_left
  have hW₁Ua : W₁.1 ≤ f ⁻¹ᵁ Ua₁.1 := hg.trans inf_le_right
  obtain ⟨b₁, b₂, hb, hyb⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter W₁.2 V₂.2 y ⟨hyW₁, hy₂⟩
  exact ⟨{
    base₁ := a₁
    base₂ := a₂
    base_eq := ha
    base_mem := hya
    source₁ := g
    source₁_mem := hyg
    source₁_le₂ := hW₁V₂
    source₁_base := hW₁Ua
    source₂₁ := b₁
    source₂₂ := b₂
    source₂_eq := hb
    source₂_mem := hyb }⟩

end Stacks.Discriminant

end
