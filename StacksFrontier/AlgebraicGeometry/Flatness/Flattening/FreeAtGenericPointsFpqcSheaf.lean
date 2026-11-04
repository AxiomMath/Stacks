module

public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.FiniteDegree
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Restriction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsAffineBridge
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsStalkDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocusPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibrePointFreeness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree

/-!
# Fpqc-locality of the generic-point freeness condition, and the fpqc sheaf property

This file closes the first assertion of [Stacks, Tag 05MS], the one left open by
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsDescent`: the functor of
Situation [Stacks, Tag 05MP] recording whether a finite type quasi-coherent module is free of
rank `p` near the generic point of every fibre satisfies the sheaf property for the fpqc
topology.

Two of the three steps of the source's argument are already available. Descent along an fpqc
covering of the base gives a *free stalk* of rank `p` at the generic point of every fibre
(`AlgebraicGeometry.FreeAtGenericPointsSituation.stalkFreeOfRank_of_fpqcCover`), and the
ring-theoretic engine turns `p` generating sections on an affine open meeting every fibre over an
affine open of the base into a *basis* of them
(`AlgebraicGeometry.nonempty_basis_sections_of_forall_stalkFreeOfRank`). What is supplied here is
the middle step — the source's one sentence "after shrinking `T` we may assume that `U → T` is
surjective" — together with the reading of the resulting basis as the generic-point condition and
the assembly of the sheaf statement.

*The shrinking.* Fix an affine open `V₀` of the base around the image point and an affine open of
the source around the generic point of the fibre on which `p` sections of the module span. Shrink
that open to a basic open `U` lying inside `g ⁻¹ᵁ V₀`: the sections survive because `Γ(F, U)` is
then a localization of them (`AlgebraicGeometry.span_sections_basicOpen_of_span`). Now `g` is
smooth, hence flat and locally of finite presentation, hence open, so `g '' U` is an open
neighbourhood of the image point and therefore contains a basic open `V = Y.basicOpen a` of `V₀`
around it. Taking `U' = X.basicOpen (g.appLE V₀ U _ a) = U ⊓ g ⁻¹ᵁ V` keeps the open affine and
makes it surject onto `V`, and one more localization carries the sections along.

*The algebra hypotheses for the pair `(U', V)`.* The engine asks for flatness, finite presentation
and geometric integrality of the induced map of functions `g.appLE V U' _`. The first two are
`AlgebraicGeometry.HasRingHomProperty.appLE` for `Smooth`, projected through `Algebra.Smooth`. The
third is geometric integrality of `g.resLE V U' _`, which holds by
`AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyIrreducible_hom` because that
restriction is smooth and, being surjective, still has geometrically irreducible fibres
(`AlgebraicGeometry.geometricallyIrreducible_resLE`).

## Main results

* `AlgebraicGeometry.span_sections_basicOpen_of_span`: sections spanning on an affine open still
  span on a basic open of it.
* `AlgebraicGeometry.exists_affineOpen_le_span_sections_of_stalkFreeOfRank`: the affine open of
  `AlgebraicGeometry.exists_affineOpen_span_sections_of_stalkFreeOfRank` can be taken inside a
  prescribed open neighbourhood.
* `AlgebraicGeometry.exists_affineOpen_surjective_span_sections_of_stalkFreeOfRank`: **the
  shrinking** — a pair of affine opens, the source one surjecting onto the target one, carrying
  `p` spanning sections.
* `AlgebraicGeometry.flat_appLE_algebra`, `AlgebraicGeometry.finitePresentation_appLE_algebra` and
  `AlgebraicGeometry.geometricallyIntegral_specMap_algebraMap_appLE_of_smooth`: the hypotheses of
  [Stacks, Tag 05IA] for such a pair of affine opens of a smooth morphism with geometrically
  irreducible fibres.
* `AlgebraicGeometry.freeAtPointOfRank_of_module_affineOpen`: a module whose sections on an affine
  open are finite locally free of rank `p` is free of rank `p` near every point of that open.
* `AlgebraicGeometry.freeAtPointOfRank_of_forall_stalkFreeOfRank`: **the locality statement** — for
  a smooth morphism with geometrically irreducible fibres, a free stalk of rank `p` at the generic
  point of every fibre forces freeness of rank `p` on a neighbourhood of each of them.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.freeAtGenericPointsFunctor_isSheaf_fpqc`: **the
  first assertion of [Stacks, Tag 05MS]**.

## Implementation notes

The engine records its algebra hypotheses for `AlgebraicGeometry.Scheme.Hom.appLE`, while
geometric integrality is available for the morphism of affine schemes `g.resLE V U _`; the two are
compared by `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE`, which exhibits
`Spec.map (g.appLE V U _)` as `g.resLE V U _` conjugated by the two isomorphisms
`AlgebraicGeometry.IsAffineOpen.isoSpec`.

Reading a basis of the sections back as the condition of Situation 05MP goes through
`Module.IsFiniteLocallyFreeOfRank.of_basis'` and the affine-local criterion
`Stacks.Modules.isFiniteLocallyFreeOfRank_restrict_fromSpec`; only the *pointwise* consequence is
wanted, so the trivialisation is read off on an open neighbourhood with
`Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion` rather than assembled over a cover,
and turned into `AlgebraicGeometry.FreeAtPointOfRank` by
`AlgebraicGeometry.freeAtPointOfRank_of_restrict_iso_free`.

## References

* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace AlgebraicGeometry

/-! ### Sections on a basic open -/

/-- **Sections spanning on an affine open still span on a basic open of it.** The sections of a
quasi-coherent module over the basic open of `a` are the localization of its sections over the
affine open away from `a`, and the image of a spanning family spans a localization. -/
theorem span_sections_basicOpen_of_span {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) {ι : Type*} (s : ι → Γ(F, U))
    (hs : Submodule.span Γ(X, U) (Set.range s) = ⊤) :
    Submodule.span Γ(X, X.basicOpen a)
      (Set.range fun i ↦ restrictₗ F (X.basicOpen_le a) (s i)) = ⊤ := by
  classical
  let := algebraOfLE X (X.basicOpen_le a)
  have := hU.isLocalization_basicOpen a
  let := moduleOfLE F (X.basicOpen_le a)
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen a) Γ(F, X.basicOpen a) :=
    isScalarTowerOfLE F (X.basicOpen_le a)
  have := isLocalizedModule_restrictₗ F hU a rfl (X.basicOpen_le a)
  have himg : Submodule.span Γ(X, X.basicOpen a)
      (restrictₗ F (X.basicOpen_le a) '' Set.range s) = ⊤ := by
    rw [Submodule.span_image_eq_top_iff Γ(X, X.basicOpen a) (Submonoid.powers a)
      (restrictₗ F (X.basicOpen_le a)) (Set.range s)]
    intro m
    exact ⟨1, by rw [hs]; exact Submodule.mem_top⟩
  rwa [← Set.range_comp] at himg

/-! ### Generators on an affine open inside a prescribed neighbourhood -/

/-- **The affine open of `exists_affineOpen_span_sections_of_stalkFreeOfRank` can be taken inside
a prescribed open neighbourhood of the point.** Intersect the affine open produced there with the
prescribed one and shrink to a basic open inside the intersection; the spanning sections survive
by `AlgebraicGeometry.span_sections_basicOpen_of_span`. -/
theorem exists_affineOpen_le_span_sections_of_stalkFreeOfRank {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (x : X) (W : X.Opens) (hxW : x ∈ W) (p : ℕ)
    (h : StalkFreeOfRank F x p) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (_ : U ≤ W) (s : Fin p → Γ(F, U)),
      Submodule.span Γ(X, U) (Set.range s) = ⊤ := by
  obtain ⟨U₁, hU₁, hxU₁, s₁, hs₁⟩ :=
    exists_affineOpen_span_sections_of_stalkFreeOfRank F x p h
  obtain ⟨b, hble, hxb⟩ :=
    hU₁.exists_basicOpen_le (V := U₁ ⊓ W) ⟨x, hxU₁, hxW⟩ hxU₁
  exact ⟨X.basicOpen b, hU₁.basicOpen b, hxb, hble.trans inf_le_right,
    fun i ↦ restrictₗ F (X.basicOpen_le b) (s₁ i),
    span_sections_basicOpen_of_span F hU₁ b s₁ hs₁⟩

/-! ### The shrinking -/

/-- **The shrinking step of the proof of the first assertion of [Stacks, Tag 05MS].** Let `g` be
smooth, let `F` be quasi-coherent of finite type with free stalk of rank `p` at a point `x` lying
over `y`. Then there are an affine open `V ∋ y` of the target and an affine open `U ∋ x` of the
source with `U ≤ g ⁻¹ᵁ V`, such that `U` surjects onto `V` and `p` sections of `F` span `Γ(F, U)`.

This is the source's "after shrinking `T` we may assume that `U → T` is surjective". A smooth
morphism is open, so the image of an affine open carrying `p` spanning sections and lying over an
affine open `V₀` of the target contains a basic open `V` of `V₀` around `y`; intersecting with
`g ⁻¹ᵁ V` keeps the source open affine — it is a basic open of it, by
`AlgebraicGeometry.Scheme.basicOpen_appLE` — makes it surject onto `V`, and preserves the spanning
sections because its sections are a localization. -/
theorem exists_affineOpen_surjective_span_sections_of_stalkFreeOfRank {X Y : Scheme.{u}}
    (g : X ⟶ Y) [Smooth g] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (y : Y) (x : X)
    (hgx : g.base x = y) (p : ℕ) (h : StalkFreeOfRank F x p) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : y ∈ V) (U : X.Opens) (_ : IsAffineOpen U)
      (_ : x ∈ U) (_ : U ≤ g ⁻¹ᵁ V) (_ : ∀ w ∈ V, ∃ z ∈ U, g.base z = w)
      (s : Fin p → Γ(F, U)), Submodule.span Γ(X, U) (Set.range s) = ⊤ := by
  obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV₀, s, hs⟩ := exists_affineOpen_le_span_sections_of_stalkFreeOfRank F x
    (g ⁻¹ᵁ V₀) (show g.base x ∈ V₀ from hgx ▸ hyV₀) p h
  obtain ⟨a, hale, hya⟩ := hV₀.exists_basicOpen_le
    (V := (⟨g.base '' (U : Set X), g.isOpenMap _ U.isOpen⟩ : Y.Opens)) ⟨y, x, hxU, hgx⟩ hyV₀
  have hbo := Scheme.basicOpen_appLE g U V₀ hUV₀ a
  have hmem : ∀ z ∈ U, g.base z ∈ Y.basicOpen a →
      z ∈ X.basicOpen (g.appLE V₀ U hUV₀ a) := fun z hz hza ↦ hbo ▸ ⟨hz, hza⟩
  refine ⟨Y.basicOpen a, hV₀.basicOpen a, hya, X.basicOpen (g.appLE V₀ U hUV₀ a),
    hU.basicOpen _, hmem x hxU (hgx ▸ hya), hbo ▸ inf_le_right, fun w hw ↦ ?_,
    fun i ↦ restrictₗ F (X.basicOpen_le (g.appLE V₀ U hUV₀ a)) (s i),
    span_sections_basicOpen_of_span F hU (g.appLE V₀ U hUV₀ a) s hs⟩
  obtain ⟨z, hzU, hzw⟩ := hale hw
  exact ⟨z, hmem z hzU (hzw ▸ hw), hzw⟩

/-! ### The algebra hypotheses of Stacks 05IA on a pair of affine opens -/

/-- The functions on an affine open of the source of a smooth morphism form a smooth algebra over
the functions on an affine open of the target it lies over. -/
theorem algebraSmooth_appLE {X Y : Scheme.{u}} (g : X ⟶ Y) [Smooth g] {V : Y.Opens}
    (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ g ⁻¹ᵁ V) :
    letI := (g.appLE V U hUV).hom.toAlgebra
    Algebra.Smooth Γ(Y, V) Γ(X, U) := by
  let := (g.appLE V U hUV).hom.toAlgebra
  exact RingHom.smooth_algebraMap.1
    (HasRingHomProperty.appLE @Smooth g ‹Smooth g› ⟨V, hV⟩ ⟨U, hU⟩ hUV)

/-- The functions on an affine open of the source of a smooth morphism form an algebra of finite
presentation over the functions on an affine open of the target it lies over. -/
theorem finitePresentation_appLE_algebra {X Y : Scheme.{u}} (g : X ⟶ Y) [Smooth g] {V : Y.Opens}
    (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ g ⁻¹ᵁ V) :
    letI := (g.appLE V U hUV).hom.toAlgebra
    Algebra.FinitePresentation Γ(Y, V) Γ(X, U) := by
  let := (g.appLE V U hUV).hom.toAlgebra
  exact (algebraSmooth_appLE g hV hU hUV).2

/-- The functions on an affine open of the source of a smooth morphism are flat over the functions
on an affine open of the target it lies over. -/
theorem flat_appLE_algebra {X Y : Scheme.{u}} (g : X ⟶ Y) [Smooth g] {V : Y.Opens}
    (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ g ⁻¹ᵁ V) :
    letI := (g.appLE V U hUV).hom.toAlgebra
    Module.Flat Γ(Y, V) Γ(X, U) := by
  let := (g.appLE V U hUV).hom.toAlgebra
  have := algebraSmooth_appLE g hV hU hUV
  exact Algebra.Smooth.flat Γ(Y, V) Γ(X, U)

/-- A geometrically integral restriction of a morphism to a pair of affine opens induces a map of
functions whose spectrum is again geometrically integral.

`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE` exhibits `Spec.map (g.appLE V U _)` as
`g.resLE V U _` conjugated by the two isomorphisms of
`AlgebraicGeometry.IsAffineOpen.isoSpec`, and geometric integrality respects isomorphisms. -/
theorem geometricallyIntegral_specMap_appLE {X Y : Scheme.{u}} (g : X ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ g ⁻¹ᵁ V)
    (hg : GeometricallyIntegral (g.resLE V U hUV)) :
    GeometricallyIntegral (Spec.map (g.appLE V U hUV)) := by
  have : IsIso U.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  have : IsIso V.toSpecΓ := by rw [← hV.isoSpec_hom]; infer_instance
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral)
    U.toSpecΓ (Spec.map (g.appLE V U hUV))).mp ?_
  rw [Scheme.Opens.toSpecΓ_SpecMap_appLE]
  exact MorphismProperty.RespectsIso.postcomp _ V.toSpecΓ _ hg

/-- **The geometric integrality hypothesis of [Stacks, Tag 05IA] for a pair of affine opens of a
smooth morphism with geometrically irreducible fibres.** The source open is assumed to surject onto
the target open, which is what keeps the fibres of the restriction geometrically irreducible. -/
theorem geometricallyIntegral_specMap_algebraMap_appLE_of_smooth {X Y : Scheme.{u}} (g : X ⟶ Y)
    [Smooth g] [GeometricallyIrreducible g] {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ g ⁻¹ᵁ V) [Surjective (g.resLE V U hUV)] :
    letI := (g.appLE V U hUV).hom.toAlgebra
    GeometricallyIntegral (Spec.map (ofHom (algebraMap Γ(Y, V) Γ(X, U)))) := by
  let := (g.appLE V U hUV).hom.toAlgebra
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @Smooth.{u}) (Q := RingHom.Smooth)
  let _ := HasRingHomProperty.instIsZariskiLocalAtTarget
    (P := @Smooth.{u}) (Q := RingHom.Smooth)
  have : Smooth (g.resLE V U hUV) := IsZariskiLocalAtSource.resLE hUV ‹Smooth g›
  have := geometricallyIrreducible_resLE g V U hUV
  exact geometricallyIntegral_specMap_appLE g hV hU hUV
    (geometricallyIntegral_of_smooth_of_geometricallyIrreducible_hom (g.resLE V U hUV) ‹_›)

/-! ### Reading a basis of the sections back as freeness near a point -/

/-- **A quasi-coherent module whose sections on an affine open are finite locally free of rank `n`
is free of rank `n` near every point of that open.** The restriction to `Spec Γ(X, U)` is finite
locally free of rank `n` by [Stacks, Tag 05JM], and a trivialisation there is a trivialisation on
an open neighbourhood in `X`. -/
theorem freeAtPointOfRank_of_module_affineOpen {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (n : ℕ)
    (h : Module.IsFiniteLocallyFreeOfRank Γ(X, U) Γ(F, U) n) :
    FreeAtPointOfRank F x n := by
  have hxr : x ∈ Set.range hU.fromSpec.base := by
    rw [← Scheme.Hom.coe_opensRange, hU.opensRange_fromSpec]
    exact hx
  obtain ⟨z, hz⟩ := hxr
  obtain ⟨W, hxW, -, ⟨e⟩⟩ := Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion
    hU.fromSpec F n z (Stacks.Modules.isFiniteLocallyFreeOfRank_restrict_fromSpec F hU n h)
  exact freeAtPointOfRank_of_restrict_iso_free F (hz ▸ hxW) n e

/-! ### Locality of the generic-point freeness condition -/

/-- **A free stalk at the generic point of every fibre forces freeness of rank `p` near each of
them.** Let `g` be smooth with geometrically irreducible fibres and let `F` be quasi-coherent of
finite type. If the stalk of `F` at the generic point of every fibre of `g` is free of rank `p`,
then `F` is finite locally free of rank `p` on a neighbourhood of each of those generic points.

The shrinking of `AlgebraicGeometry.exists_affineOpen_surjective_span_sections_of_stalkFreeOfRank`
supplies a pair of affine opens satisfying the hypotheses of the engine
`AlgebraicGeometry.nonempty_basis_sections_of_forall_stalkFreeOfRank`, which turns the spanning
sections into a basis; a basis of the sections on an affine open is freeness of that rank near each
of its points. -/
theorem freeAtPointOfRank_of_forall_stalkFreeOfRank {X Y : Scheme.{u}} (g : X ⟶ Y) [Smooth g]
    [GeometricallyIrreducible g] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (p : ℕ)
    (hstalk : ∀ (y : Y) (ξ : g.fiber y), IsGenericPoint ξ (Set.univ : Set (g.fiber y)) →
      StalkFreeOfRank F (g.fiberι y ξ) p)
    (y : Y) (ξ : g.fiber y) (hξ : IsGenericPoint ξ (Set.univ : Set (g.fiber y))) :
    FreeAtPointOfRank F (g.fiberι y ξ) p := by
  classical
  have hgx : g.base (g.fiberι y ξ) = y := by
    have hr : g.fiberι y ξ ∈ Set.range (g.fiberι y) := ⟨ξ, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at hr
  obtain ⟨V, hV, hyV, U, hU, hxU, hUV, hcov, s, hs⟩ :=
    exists_affineOpen_surjective_span_sections_of_stalkFreeOfRank g F y (g.fiberι y ξ) hgx p
      (hstalk y ξ hξ)
  have hsurj : Function.Surjective fun k : Fin p → Γ(X, U) ↦ ∑ i, k i • s i := by
    intro v
    exact (Submodule.mem_span_range_iff_exists_fun Γ(X, U)).mp (hs.ge Submodule.mem_top)
  have : Surjective (g.resLE V U hUV) := ⟨fun w ↦ by
    obtain ⟨z, hzU, hzw⟩ := hcov w.1 w.2
    exact ⟨⟨z, hzU⟩, Subtype.ext ((Scheme.Hom.coe_resLE_apply g hUV _).trans hzw)⟩⟩
  obtain ⟨bas⟩ := nonempty_basis_sections_of_forall_stalkFreeOfRank g hV hU hUV hcov
    (finitePresentation_appLE_algebra g hV hU hUV) (flat_appLE_algebra g hV hU hUV)
    (geometricallyIntegral_specMap_algebraMap_appLE_of_smooth g hV hU hUV) F p s hsurj hstalk
  exact freeAtPointOfRank_of_module_affineOpen F hU hxU p
    (Module.IsFiniteLocallyFreeOfRank.of_basis' bas)

namespace FreeAtGenericPointsSituation

/-- **Stacks Project, Tag 05MS, part (1).** The generic-rank functor satisfies the sheaf property
for the fpqc topology.

By `freeAtGenericPointsFunctor_isSheaf_fpqc_of_fpqcCover` this is fpqc-locality of the
generic-point condition, and the source proves that locality in two steps: descent along the
covering gives a free stalk of rank `p` at the generic point of every fibre over the base
(`stalkFreeOfRank_of_fpqcCover`), and
`AlgebraicGeometry.freeAtPointOfRank_of_forall_stalkFreeOfRank` spreads those free stalks out to
neighbourhoods. -/
@[stacks 05MS "part (1), the generic-rank functor is an fpqc sheaf"]
theorem freeAtGenericPointsFunctor_isSheaf_fpqc (D : FreeAtGenericPointsSituation.{u}) (p : ℕ) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over D.S) (D.freeAtGenericPointsFunctor p) := by
  have : GeometricallyIrreducible D.f :=
    (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber D.f).mpr
      D.geometricallyIrreducibleFibers
  refine D.freeAtGenericPointsFunctor_isSheaf_fpqc_of_fpqcCover p fun T 𝒰 h t ξ hξ ↦ ?_
  have : Smooth (D.baseChangeMap T) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.f T.hom) inferInstance
  have : GeometricallyIrreducible (D.baseChangeMap T) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback D.f T.hom) inferInstance
  exact freeAtPointOfRank_of_forall_stalkFreeOfRank (D.baseChangeMap T) (D.baseChangeModule T) p
    (D.stalkFreeOfRank_of_fpqcCover p T 𝒰 h) t ξ hξ

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
