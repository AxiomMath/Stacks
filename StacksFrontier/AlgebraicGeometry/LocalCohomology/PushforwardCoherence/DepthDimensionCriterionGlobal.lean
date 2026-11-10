module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Injective
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.ClosureStalkHeight
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionAffine
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Locality
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk

/-!
# [Stacks, Tag 0BJY]

Let `X` be a locally Noetherian universally catenary scheme, let `j : U → X` be the inclusion of
an open subscheme, let `ℱ` be a coherent `𝒪_U`-module and let `n` be a natural number. Assume the
formal fibres of `𝒪_{X,z}` satisfy Serre's condition `(Sₙ)` for every `z ∉ U`. Then `R^p j_* ℱ` is
coherent for every `0 ≤ p < n` if and only if

  `depth_{𝒪_{U,x}}(ℱ_x) + dim(𝒪_{closure {j(x)}, z}) > n`

for every `x ∈ Supp(ℱ)` and every `z ∉ U` lying in the closure of `{j(x)}`, where `closure {j(x)}`
carries its reduced induced scheme structure.

This is [Stacks, Tag 0BJY], and it is proved here.

## Main results

* `AlgebraicGeometry.range_subschemeι_vanishingIdeal_closure` — the reduced closure of a point
  `x` has the closure of `{x}` as its underlying set.
* `AlgebraicGeometry.ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim` — the dimension of the
  local ring of the reduced closure of `x` at a point `z` is the codimension of `closure {z}` in
  `closure {x}` ([Stacks, Tag 02IZ] for the scheme `closure {x}`).

* `AlgebraicGeometry.mem_range_morphismRestrict_iff` — a point of an open `V` of the target is in
  the image of `j ∣_ V` exactly when it is in the image of `j`.
* `AlgebraicGeometry.formalFibersHavePropertySk_stalk_opens_iff` — Serre's condition on the formal
  fibres of a stalk is the same read on an open subscheme.
* `LocalCohomologySequence.forall_lt_depth_add_topCodim_restrict_iff` — the depth–dimension
  condition for `j ∣_ V` is the condition for `j` at the points lying over `V`.
* `LocalCohomologySequence.forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived` — the
  criterion with `dim(𝒪_{closure {j(x)}, z})` written as the codimension
  `codim(closure {z}, closure {j(x)})`.
* `LocalCohomologySequence.forall_lt_depth_add_ringKrullDim_iff_forall_isCoherent_rightDerived` —
  **[Stacks, Tag 0BJY]**, in the source's terms.
* `LocalCohomologySequence.forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens_ι`
  — the same at the inclusion of an open subscheme, the shape the tag is stated in.

## Implementation notes

The criterion is proved first with the codimension `codim(closure {z}, closure {j(x)})` in the
place of `dim(𝒪_{closure {j(x)}, z})`, because that is the quantity the affine case computes, and
then rewritten pointwise by `ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim`. A point `z`
of `X` in the closure of `{j(x)}` is the same thing as a point of the reduced closed subscheme on
that closure, by `range_subschemeι_vanishingIdeal_closure`.

The source's proof opens *"the question is local on `X`, hence we may assume `X` is affine"*, and
both sides of the equivalence are local on `X`, which is what makes that legitimate here:

* the **coherence** side by
  `ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_forall_isAffineOpen`, whose hypotheses
  an open immersion into a locally Noetherian scheme satisfies, exactly as in
  `Stacks.LocalCohomologySequence.isCoherent_rightDerived_of_isFiniteLocallyFree` for
  [Stacks, Tag 0BLT];
* the **depth–dimension** side because a pair `x`, `z` entering the condition is never split
  across a cover: `z ∈ closure {j(x)}` means `j(x) ⤳ z`, so by `specializes_iff_forall_open`
  **every** open containing `z` contains `j(x)`. An affine open `V` containing `z` therefore
  contains the whole pair, and the condition at the pair is the condition read inside `V`. There
  is no gluing step.

The affine case is
`LocalCohomologySequence.forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_affine`,
applied to `j ∣_ V` over an affine open `V` of `X`. Its three hypotheses come from the tag's:
`V.toScheme` is affine and locally Noetherian; it is universally catenary because `V.ι` is
locally of finite type ([Stacks, Tag 02J9]); and the formal fibres of its stalks are those of
`X` by `formalFibersHavePropertySk_stalk_opens_iff`, the stalk map of an open immersion being an
isomorphism.

The four terms of the condition are moved between `j` and `j ∣_ V` by
`forall_lt_depth_add_topCodim_restrict_iff`: the support by
`AlgebraicGeometry.Scheme.Modules.supp_restrict`, the depth by
`AlgebraicGeometry.Scheme.Modules.depth_stalk_restrict`, the codimension by
`IrreducibleClosedsCodim.topCodim_closureSingleton_map_isOpenEmbedding` — the codimension between
the closures of two points of `V` is the same computed in `V` and in `X` — and the two
memberships by `AlgebraicGeometry.mem_range_morphismRestrict_iff` and
`Topology.IsInducing.specializes_iff`.

For the direction that reads the condition off the coherence, the coherence of `R^p j_* ℱ` has to
be restricted to `V` first; that is [Stacks, Tag 01E5], in the same four steps as in
[Stacks, Tag 0BLT]'s proof.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0BLT](https://stacks.math.columbia.edu/tag/0BLT)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace
open TopologicalSpace.IrreducibleCloseds (closureSingleton)
open IrreducibleClosedsCodim (topCodim topCodim_closureSingleton_map_isOpenEmbedding)
open Stacks.AlgebraicGeometry.CoherentDevissage (isCoherent_of_iso)
open Stacks.AlgebraicGeometry.ProperCohomologyFinite
  (isCoherent_rightDerivedPlus_of_forall_isAffineOpen)
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (rightDerivedPlusRestrictObjIso)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Two readings of an open of the target -/

/-- **A point of an open `V` of the target lies in the image of `j ∣_ V` exactly when it lies in
the image of `j`.** The square `(j ∣_ V) ≫ V.ι = (j ⁻¹ᵁ V).ι ≫ j` of
`AlgebraicGeometry.morphismRestrict_ι` gives one direction on the nose; for the other, a point of
`U` over `z ∈ V` lies in `j ⁻¹ᵁ V`, and `V.ι` is injective. -/
public theorem mem_range_morphismRestrict_iff {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (V : X.Opens) (z : V.toScheme) :
    z ∈ Set.range (j ∣_ V).base ↔ V.ι.base z ∈ Set.range j.base := by
  have hVemb : IsOpenEmbedding V.ι.base := V.ι.isOpenEmbedding
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨x, hx⟩ := hz
    exact ⟨(j ⁻¹ᵁ V).ι.base x,
      (morphismRestrict_base_coe j V x).symm.trans (congrArg Subtype.val hx)⟩
  · obtain ⟨y, hy⟩ := hz
    have hyV : y ∈ j ⁻¹ᵁ V := by
      change j.base y ∈ V
      rw [hy]
      exact z.2
    exact ⟨(⟨y, hyV⟩ : (j ⁻¹ᵁ V).toScheme),
      hVemb.injective ((morphismRestrict_base_coe j V ⟨y, hyV⟩).trans hy)⟩

/-- **Serre's condition on the formal fibres is the same read on an open subscheme.** The stalk of
`V.toScheme` at `z` and the stalk of `X` at `V.ι z` are isomorphic rings, the stalk map of an open
immersion being an isomorphism, so
`Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv` applies. -/
public theorem formalFibersHavePropertySk_stalk_opens_iff {X : Scheme.{u}} (V : X.Opens)
    (z : V.toScheme) (n : ℕ) :
    Stacks.LocalCohomology.FormalFibersHavePropertySk (X.presheaf.stalk (V.ι.base z)) n ↔
      Stacks.LocalCohomology.FormalFibersHavePropertySk (V.toScheme.presheaf.stalk z) n :=
  Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv
    (asIso (V.ι.stalkMap z)).commRingCatIsoToRingEquiv n

/-! ### The local ring of the reduced closure of a point -/

/-- **The reduced closure of a point `x` lies over the closure of `{x}`.** The image of the
closed immersion of the reduced closed subscheme on `closure {x}` is that closure; the
declaration is `Stacks.Chow.range_subschemeι_vanishingIdeal_closure`. -/
alias range_subschemeι_vanishingIdeal_closure :=
  Stacks.Chow.range_subschemeι_vanishingIdeal_closure

/-- **The dimension of the local ring of the reduced closure of a point is a codimension.** Let
`x` be a point of a scheme `X` and let `y` be a point of the reduced closed subscheme on the
closure of `{x}`, lying over `z ∈ X`. Then `dim(𝒪_{closure {x}, z})` is the codimension of
`closure {z}` in `closure {x}`.

This is [Stacks, Tag 02IZ] for the integral scheme `closure {x}`, read in `X`. Both sides are
the height of the image of the prime of `z` in `Γ(X, V) ⧸ 𝔭_x` for an affine open `V` containing
`z`, which also contains `x` because `x ⤳ z`:
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.ringKrullDim_stalk_vanishingIdeal_closure`
for the left side and `topCodim_closureSingleton_eq_height_primeIdealOf` for the right. -/
@[ega "IV 21.6.2" "special case"]
public theorem ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim {X : Scheme.{u}} (x : X)
    (y : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subscheme) :
    ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subscheme.presheaf.stalk y) =
      (topCodim (closureSingleton ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι.base y)) (closureSingleton x) :
        WithBot ℕ∞) := by
  have hzx : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι.base y ∈ closure ({x} : Set X) := by
    rw [← range_subschemeι_vanishingIdeal_closure x]
    exact ⟨y, rfl⟩
  obtain ⟨V, hzV⟩ : ∃ V : X.affineOpens, (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι.base y ∈ (V : X.Opens) := by
    have hz' : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι.base y ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hz'
    exact TopologicalSpace.Opens.mem_iSup.mp hz'
  have hxV : x ∈ (V : X.Opens) :=
    specializes_iff_forall_open.mp (specializes_iff_mem_closure.mpr hzx) _
      (V : X.Opens).isOpen hzV
  rw [Stacks.AlgebraicGeometry.CodimensionOneObstruction.ringKrullDim_stalk_vanishingIdeal_closure
      V.2 hxV rfl y hzV,
    topCodim_closureSingleton_eq_height_primeIdealOf V.2 hxV hzV hzx]

end AlgebraicGeometry

namespace Stacks.LocalCohomologySequence

/-! ### The depth–dimension condition over an open of the base -/

/-- **The depth–dimension condition of [Stacks, Tag 0BJY] for `j ∣_ V` is the condition for `j`
read at the points lying over `V`.** Let `j : U ⟶ X` be an open immersion, let `V` be an open of
`X` and let `ℱ` be an `𝒪_U`-module. Then the condition

  `depth_{𝒪_{U,x}}(ℱ_x) + codim(closure {z}, closure {j(x)}) > n`
  for every `x ∈ Supp(ℱ)` and every `z ∉ j(U)` with `z ∈ closure {j(x)}`

holds for `j ∣_ V` and `ℱ|_{j⁻¹V}` exactly when it holds for `j` and `ℱ` at the pairs with
`j(x) ∈ V` and `z ∈ V`.

The support moves by `AlgebraicGeometry.Scheme.Modules.supp_restrict`, the depth by
`AlgebraicGeometry.Scheme.Modules.depth_stalk_restrict`, the codimension by
`IrreducibleClosedsCodim.topCodim_closureSingleton_map_isOpenEmbedding` and the two memberships
by `AlgebraicGeometry.mem_range_morphismRestrict_iff` and `Topology.IsInducing.specializes_iff`;
the two underlying maps are compared by `AlgebraicGeometry.morphismRestrict_base_coe`. -/
public theorem forall_lt_depth_add_topCodim_restrict_iff {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (V : X.Opens) (F : U.Modules) (n : ℕ) :
    (∀ x : (j ⁻¹ᵁ V).toScheme, x ∈ SheafOfModules.supp (F.restrict (j ⁻¹ᵁ V).ι) →
        ∀ z : V.toScheme, z ∉ Set.range (j ∣_ V).base →
          z ∈ closure ({(j ∣_ V).base x} : Set V.toScheme) →
          (n : ℕ∞) <
            Module.depth ((j ⁻¹ᵁ V).toScheme.presheaf.stalk x)
                (IsLocalRing.maximalIdeal ((j ⁻¹ᵁ V).toScheme.presheaf.stalk x))
                ((F.restrict (j ⁻¹ᵁ V).ι).presheaf.stalk x) +
              topCodim (closureSingleton z) (closureSingleton ((j ∣_ V).base x))) ↔
      ∀ x : U, j.base x ∈ V → x ∈ SheafOfModules.supp F →
        ∀ z : X, z ∈ V → z ∉ Set.range j.base → z ∈ closure ({j.base x} : Set X) →
          (n : ℕ∞) <
            Module.depth (U.presheaf.stalk x) (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
                (F.presheaf.stalk x) +
              topCodim (closureSingleton z) (closureSingleton (j.base x)) := by
  have hVemb : IsOpenEmbedding V.ι.base := V.ι.isOpenEmbedding
  have hbase : ∀ x : (j ⁻¹ᵁ V).toScheme,
      V.ι.base ((j ∣_ V).base x) = j.base ((j ⁻¹ᵁ V).ι.base x) :=
    fun x => morphismRestrict_base_coe j V x
  have hclos : ∀ y z : V.toScheme, (z ∈ closure ({y} : Set V.toScheme) ↔
      V.ι.base z ∈ closure ({V.ι.base y} : Set X)) := by
    intro y z
    rw [← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
    exact hVemb.isInducing.specializes_iff.symm
  refine ⟨fun hcond x hxV hx z hzV hz hzx => ?_, fun hcond x hx z hz hzx => ?_⟩
  · have hx' : (⟨x, hxV⟩ : (j ⁻¹ᵁ V).toScheme) ∈
        SheafOfModules.supp (F.restrict (j ⁻¹ᵁ V).ι) := by
      rw [Scheme.Modules.supp_restrict (j ⁻¹ᵁ V).ι F]
      exact hx
    have key := hcond ⟨x, hxV⟩ hx' ⟨z, hzV⟩
      (fun hc => hz ((mem_range_morphismRestrict_iff j V ⟨z, hzV⟩).mp hc))
      ((hclos ((j ∣_ V).base ⟨x, hxV⟩) ⟨z, hzV⟩).mpr (by rw [hbase ⟨x, hxV⟩]; exact hzx))
    rw [Scheme.Modules.depth_stalk_restrict (j ⁻¹ᵁ V).ι F ⟨x, hxV⟩,
      ← topCodim_closureSingleton_map_isOpenEmbedding hVemb (⟨z, hzV⟩ : V.toScheme)
        ((j ∣_ V).base ⟨x, hxV⟩), hbase ⟨x, hxV⟩] at key
    exact key
  · have hx' : (j ⁻¹ᵁ V).ι.base x ∈ SheafOfModules.supp F := by
      rw [Scheme.Modules.supp_restrict (j ⁻¹ᵁ V).ι F] at hx
      exact hx
    have key := hcond ((j ⁻¹ᵁ V).ι.base x) x.2 hx' (V.ι.base z) z.2
      (fun hc => hz ((mem_range_morphismRestrict_iff j V z).mpr hc))
      (by rw [← hbase x]; exact (hclos ((j ∣_ V).base x) z).mp hzx)
    rw [Scheme.Modules.depth_stalk_restrict (j ⁻¹ᵁ V).ι F x,
      ← topCodim_closureSingleton_map_isOpenEmbedding hVemb z ((j ∣_ V).base x), hbase x]
    exact key

/-! ### Tag 0BJY -/

/-- **[Stacks, Tag 0BJY], with the dimension written as a codimension.** Let `X` be a locally
Noetherian universally catenary scheme, let `j : U → X` be the inclusion of an open subscheme, let
`ℱ` be a coherent `𝒪_U`-module and let `n` be a natural number. Assume the formal fibres of
`𝒪_{X,z}` satisfy Serre's condition `(Sₙ)` for every `z ∉ U`. Then `R^p j_* ℱ` is coherent for
every `0 ≤ p < n` if and only if

  `depth_{𝒪_{U,x}}(ℱ_x) + codim(closure {z}, closure {j(x)}) > n`

for every `x ∈ Supp(ℱ)` and every `z ∉ U` lying in the closure of `{j(x)}`. The codimension is
`dim(𝒪_{closure {j(x)}, z})` by `ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim`, and the
tag, in those terms, is
`forall_lt_depth_add_ringKrullDim_iff_forall_isCoherent_rightDerived`.

The inclusion is taken to be an arbitrary open immersion `j`, which is the same statement: an
open immersion is the inclusion of its open image composed with an isomorphism.

Both sides are local on `X`. The coherence side is local by
`…ProperCohomologyFinite.isCoherent_rightDerivedPlus_of_forall_isAffineOpen`; the depth–dimension
side is local because a pair `x`, `z` with `z ∈ closure {j(x)}` lies inside every open containing
`z`, so an affine open containing `z` contains the pair. The affine case is
`forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_affine` at `j ∣_ V`, and the two
conditions are matched by `forall_lt_depth_add_topCodim_restrict_iff`. -/
@[sga "2 VIII 2.3" "(i) ⇔ (iv)"]
public theorem forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived {U X : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (F : U.Modules) [F.IsCoherent]
    (n : ℕ) (hX : Scheme.IsUniversallyCatenary X)
    (hformal : ∀ z : X, z ∉ Set.range j.base →
      Stacks.LocalCohomology.FormalFibersHavePropertySk (X.presheaf.stalk z) n) :
    (∀ x : U, x ∈ SheafOfModules.supp F →
        ∀ z : X, z ∉ Set.range j.base → z ∈ closure ({j.base x} : Set X) →
          (n : ℕ∞) <
            Module.depth (U.presheaf.stalk x) (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
                (F.presheaf.stalk x) +
              topCodim (closureSingleton z) (closureSingleton (j.base x))) ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward j).rightDerived p).obj F).IsCoherent := by
  have hUN : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  obtain ⟨hqc, -⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have := hqc
  -- the criterion at an affine open of `X`, for `j ∣_ V`
  have hstepV : ∀ V : X.affineOpens,
      ((∀ x : U, j.base x ∈ (V : X.Opens) → x ∈ SheafOfModules.supp F →
          ∀ z : X, z ∈ (V : X.Opens) → z ∉ Set.range j.base →
            z ∈ closure ({j.base x} : Set X) →
            (n : ℕ∞) <
              Module.depth (U.presheaf.stalk x) (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
                  (F.presheaf.stalk x) +
                topCodim (closureSingleton z) (closureSingleton (j.base x))) ↔
        ∀ p : ℕ, p < n →
          (((Scheme.Modules.pushforward (j ∣_ (V : X.Opens))).rightDerived p).obj
            (F.restrict (j ⁻¹ᵁ (V : X.Opens)).ι)).IsCoherent) := by
    intro V
    let hVaff : IsAffine (V : X.Opens).toScheme := V.2
    let hVN : IsLocallyNoetherian (V : X.Opens).toScheme :=
      isLocallyNoetherian_of_isOpenImmersion (V : X.Opens).ι
    have hVcat : Scheme.IsUniversallyCatenary (V : X.Opens).toScheme := by
      intro Y f _
      have hι : LocallyOfFiniteType (V : X.Opens).ι :=
        @locallyOfFiniteType_of_isOpenImmersion _ _ (V : X.Opens).ι inferInstance
      exact @Scheme.IsUniversallyCatenary.isCatenarySpace X _ _ hX (f ≫ (V : X.Opens).ι)
        (@locallyOfFiniteType_comp _ _ _ f (V : X.Opens).ι ‹_› hι)
    have hFVcoh : (F.restrict (j ⁻¹ᵁ (V : X.Opens)).ι).IsCoherent :=
      Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion
        (j ⁻¹ᵁ (V : X.Opens)).ι F ‹F.IsCoherent›
    have := hFVcoh
    refine Iff.trans (forall_lt_depth_add_topCodim_restrict_iff j (V : X.Opens) F n).symm ?_
    refine forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_affine
      (j ∣_ (V : X.Opens)) (F.restrict (j ⁻¹ᵁ (V : X.Opens)).ι) n hVcat (fun z hz => ?_)
    exact (formalFibersHavePropertySk_stalk_opens_iff (V : X.Opens) z n).mp
      (hformal _ (fun hc => hz ((mem_range_morphismRestrict_iff j (V : X.Opens) z).mpr hc)))
  -- coherence of a higher direct image restricts to an affine open of `X`
  have hrestrictCoh : ∀ (V : X.affineOpens) (p : ℕ),
      (((Scheme.Modules.pushforward j).rightDerived p).obj F).IsCoherent →
      (((Scheme.Modules.pushforward (j ∣_ (V : X.Opens))).rightDerived p).obj
        (F.restrict (j ⁻¹ᵁ (V : X.Opens)).ι)).IsCoherent := by
    intro V p hp
    have h2 : (((Scheme.Modules.pushforward j).rightDerivedPlus (p : ℤ)).obj F).IsCoherent := by
      have := hp
      exact isCoherent_of_iso
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward j) p).app F).symm
    have h3 : ((Scheme.Modules.restrictFunctor (V : X.Opens).ι).obj
        (((Scheme.Modules.pushforward j).rightDerivedPlus (p : ℤ)).obj F)).IsCoherent :=
      Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion
        (V : X.Opens).ι _ h2
    have h4 : (((Scheme.Modules.pushforward (j ∣_ (V : X.Opens))).rightDerivedPlus (p : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (j ⁻¹ᵁ (V : X.Opens)).ι).obj F)).IsCoherent := by
      have := h3
      exact isCoherent_of_iso (rightDerivedPlusRestrictObjIso j (V : X.Opens) p F)
    have := h4
    exact isCoherent_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso
        (Scheme.Modules.pushforward (j ∣_ (V : X.Opens))) p).app _)
  refine ⟨fun hcond p hp => ?_, fun hcoh x hx z hz hzx => ?_⟩
  · have key : (((Scheme.Modules.pushforward j).rightDerivedPlus (p : ℤ)).obj F).IsCoherent := by
      refine isCoherent_rightDerivedPlus_of_forall_isAffineOpen j F p (fun V => ?_)
      exact (hstepV V).mp (fun x _ hx' z _ hz' hzx' => hcond x hx' z hz' hzx') p hp
    have := key
    exact isCoherent_of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward j) p).app F)
  · obtain ⟨V, hzV⟩ : ∃ V : X.affineOpens, z ∈ (V : X.Opens) := by
      have hz' : z ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hz'
      exact TopologicalSpace.Opens.mem_iSup.mp hz'
    have hxV : j.base x ∈ (V : X.Opens) :=
      specializes_iff_forall_open.mp (specializes_iff_mem_closure.mpr hzx) _
        (V : X.Opens).isOpen hzV
    exact (hstepV V).mpr (fun p hp => hrestrictCoh V p (hcoh p hp)) x hxV hx z hzV hz hzx

/-- **[Stacks, Tag 0BJY].** Let `X` be a locally Noetherian scheme, let `j : U → X` be the
inclusion of an open subscheme with complement `Z`, let `ℱ` be a coherent `𝒪_U`-module and let
`n ≥ 0` be an integer. Assume that `X` is universally catenary and that the formal fibres of
`𝒪_{X,z}` are `(Sₙ)` for every `z ∈ Z`. Then the following are equivalent:

* (a) for `x ∈ Supp(ℱ)` and `z ∈ Z ∩ closure {x}` we have
  `depth_{𝒪_{X,x}}(ℱ_x) + dim(𝒪_{closure {x}, z}) > n`;
* (b) `R^p j_* ℱ` is coherent for `0 ≤ p < n`.

The closure `closure {j(x)}` carries its reduced induced scheme structure, the closed subscheme
cut out by `Scheme.IdealSheafData.vanishingIdeal`, and a point `z ∈ Z ∩ closure {j(x)}` is a point
`y` of that subscheme whose image lies outside `j(U)`, by
`AlgebraicGeometry.range_subschemeι_vanishingIdeal_closure`. The depth is taken in the local ring
of `U` at `x`, which is that of `X` at `j(x)`. The inclusion is an arbitrary open immersion `j`,
which is the same statement: an open immersion is the inclusion of its open image composed with
an isomorphism.

The proof rewrites (a) pointwise by
`AlgebraicGeometry.ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim` into the condition of
`forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived`. -/
@[stacks 0BJY, sga "2 VIII 2.3" "(i) ⇔ (iv)"]
public theorem forall_lt_depth_add_ringKrullDim_iff_forall_isCoherent_rightDerived
    {U X : Scheme.{u}} [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (F : U.Modules)
    [F.IsCoherent] (n : ℕ) (hX : Scheme.IsUniversallyCatenary X)
    (hformal : ∀ z : X, z ∉ Set.range j.base →
      Stacks.LocalCohomology.FormalFibersHavePropertySk (X.presheaf.stalk z) n) :
    (∀ x : U, x ∈ SheafOfModules.supp F →
        ∀ y : (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j.base x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({j.base x} : Set X))).subschemeι.base y ∉ Set.range j.base →
          (((n : ℕ∞) : WithBot ℕ∞) <
            (Module.depth (U.presheaf.stalk x) (IsLocalRing.maximalIdeal (U.presheaf.stalk x))
                (F.presheaf.stalk x) : WithBot ℕ∞) +
              ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
                (Closeds.closure ({j.base x} : Set X))).subscheme.presheaf.stalk y))) ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward j).rightDerived p).obj F).IsCoherent := by
  refine Iff.trans ?_
    (forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived j F n hX hformal)
  refine forall_congr' fun x => forall_congr' fun _ => ⟨fun h z hz hzx => ?_, fun h y hy => ?_⟩
  · rw [← range_subschemeι_vanishingIdeal_closure (j.base x)] at hzx
    obtain ⟨y, rfl⟩ := hzx
    have key := h y hz
    rw [ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim, ← WithBot.coe_add,
      WithBot.coe_lt_coe] at key
    exact key
  · have hyx : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j.base x} : Set X))).subschemeι.base y ∈
          closure ({j.base x} : Set X) := by
      rw [← range_subschemeι_vanishingIdeal_closure (j.base x)]
      exact ⟨y, rfl⟩
    rw [ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim, ← WithBot.coe_add,
      WithBot.coe_lt_coe]
    exact h _ hy hyx

/-! ### Tag 0BJY at the inclusion of an open subscheme -/

/-- **[Stacks, Tag 0BJY] at the inclusion of an open subscheme**, which is the shape the tag is
stated in: `U` is an open of `X` and `j = U.ι`. It is
`forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived` at `j = U.ι`, the image of
`U.ι` being `U` by `AlgebraicGeometry.Scheme.Opens.range_ι`.

It carries no tag attribute of its own: the tag is registered on
`forall_lt_depth_add_ringKrullDim_iff_forall_isCoherent_rightDerived`, and this is the special
case `j = U.ι` of its codimension form. -/
public theorem forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens_ι
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens) (F : U.toScheme.Modules)
    [F.IsCoherent] (n : ℕ) (hX : Scheme.IsUniversallyCatenary X)
    (hformal : ∀ z : X, z ∉ (U : Set X) →
      Stacks.LocalCohomology.FormalFibersHavePropertySk (X.presheaf.stalk z) n) :
    (∀ x : U.toScheme, x ∈ SheafOfModules.supp F →
        ∀ z : X, z ∉ (U : Set X) → z ∈ closure ({U.ι.base x} : Set X) →
          (n : ℕ∞) <
            Module.depth (U.toScheme.presheaf.stalk x)
                (IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk x))
                (F.presheaf.stalk x) +
              topCodim (closureSingleton z) (closureSingleton (U.ι.base x))) ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward U.ι).rightDerived p).obj F).IsCoherent := by
  have hrange : ∀ z : X, (z ∉ Set.range U.ι.base ↔ z ∉ (U : Set X)) := by
    intro z
    rw [Scheme.Opens.range_ι]
  refine Iff.trans ?_
    (forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived U.ι F n hX
      (fun z hz => hformal z ((hrange z).mp hz)))
  exact forall_congr' fun x => imp_congr_right fun _ => forall_congr' fun z =>
    imp_congr_left (hrange z).symm

end Stacks.LocalCohomologySequence

end
