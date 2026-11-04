module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.FiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleConeEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ExtendedIntegers
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.QuasiRegularNormalCone
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral

/-!
# The normal bundle of a regular immersion and the excess normal sheaf

Let `i : Z ⟶ X` be an immersion of schemes and `𝒩` a virtual normal sheaf for `i`, that is a
finite locally free `𝒪_Z`-module with a surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` (Stacks 0FBQ), and write
`p : N = Spec_Z(Sym(𝒩^∨)) ⟶ Z` for its vector bundle, with the closed immersion `ι : C_ZX ⟶ N` of
the normal cone.

* If `i` is a regular immersion and `σ` is an isomorphism, then `ι` is an isomorphism: the normal
  cone of a regular immersion is the vector bundle of its conormal sheaf (Stacks 063M). This
  applies to the normal bundle `𝒞_{Z/X}^∨` of a regular immersion, whose `σ` is the reflexivity
  isomorphism. This is the step of the proof of Stacks 0FBM which identifies `C_ZX` with `N`.
* If the conormal sheaf `𝒞_{Z/X}` is finite locally free — for instance if `i` is regular — the
  kernel of `σ` is finite locally free, and the short exact sequence

    `0 ⟶ ℰ^∨ ⟶ 𝒩^∨ ⟶ 𝒞_{Z/X} ⟶ 0`

  defines the *excess normal sheaf* `ℰ`, a quotient of `𝒩`, of rank `rank 𝒩 - r` when `𝒞_{Z/X}`
  has constant rank `r`. Applied to the pullback of a virtual normal sheaf to `Z ×_X Y` for
  `Y ⟶ X` with `Z ×_X Y ⟶ Y` regular (Stacks 0FBJ), this is the excess normal sheaf of the
  situation preceding Stacks 0FBM. Dually, `0 ⟶ 𝒞_{Z/X}^∨ ⟶ 𝒩 ⟶ ℰ ⟶ 0` is short exact and its
  inclusion dualizes to a factorization of `σ` through the reflexivity isomorphism of
  `𝒞_{Z/X}`; this is the input of Stacks 0FBL that reduces Stacks 0FBM to the case `ℰ = 0`.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.conormalSurjection` — `σ` with its target read as an
  `𝒪_Z`-module, so that its kernel is formed among `𝒪_Z`-modules.
* `Stacks.Chow.VirtualNormalBundle.excessNormalSheaf` — the excess normal sheaf
  `ℰ = (ker σ)^∨`.
* `Stacks.Chow.VirtualNormalBundle.excessInclusion` and
  `Stacks.Chow.VirtualNormalBundle.excessProjection` — the two maps of the short exact sequence
  `0 ⟶ 𝒞_{Z/X}^∨ ⟶ 𝒩 ⟶ ℰ ⟶ 0`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_vectorBundleMap_left` — the vector bundle of an
  isomorphism of quasi-coherent modules is an isomorphism.
* `Stacks.Chow.VirtualNormalBundle.isIso_normalConeEmbedding` — `ι : C_ZX ⟶ N` is an isomorphism
  for a regular immersion and an isomorphism `σ`, in particular for
  `Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`.
* `Stacks.Chow.surjective_of_isAffineSpaceBundle` and
  `Stacks.Chow.schemeDeltaDimension_le_sub_of_flat_of_surjective` — a vector bundle projection of
  rank `r` is surjective, so `dim_δ(Z) ≤ n - r` as soon as `dim_δ(N) ≤ n`.
* `Stacks.Chow.VirtualNormalBundle.shortExact_kernel_surjection`,
  `Stacks.Chow.VirtualNormalBundle.isFiniteLocallyFree_excessNormalSheaf`,
  `Stacks.Chow.VirtualNormalBundle.isFiniteLocallyFreeOfRank_excessNormalSheaf` — the sequence
  `0 ⟶ ℰ^∨ ⟶ 𝒩^∨ ⟶ 𝒞_{Z/X} ⟶ 0` and the local freeness and rank of `ℰ`.
* `Stacks.Chow.VirtualNormalBundle.shortExact_excess` and
  `Stacks.Chow.VirtualNormalBundle.dualMap_excessInclusion_comp_surjection` — the dual sequence
  `0 ⟶ 𝒞_{Z/X}^∨ ⟶ 𝒩 ⟶ ℰ ⟶ 0` and the factorization of `σ` through the normal bundle of the
  regular immersion.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

/-! ### The vector bundle of an isomorphism -/

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) {F G : SheafOfModules.{u} X.ringCatSheaf} [F.IsQuasicoherent]
  [G.IsQuasicoherent]

/-- **`𝐕(f)` is an isomorphism when `f` is**: `𝐕` is a functor. -/
theorem isIso_vectorBundleMap (f : F ⟶ G) [IsIso f] : IsIso (vectorBundleMap X f) :=
  ⟨⟨vectorBundleMap X (inv f), by rw [← vectorBundleMap_comp, IsIso.inv_hom_id, vectorBundleMap_id],
    by rw [← vectorBundleMap_comp, IsIso.hom_inv_id, vectorBundleMap_id]⟩⟩

/-- **`𝐕(f) : 𝐕(𝒢) ⟶ 𝐕(ℱ)` is an isomorphism of schemes when `f` is an isomorphism.** -/
theorem isIso_vectorBundleMap_left (f : F ⟶ G) [IsIso f] : IsIso (vectorBundleMap X f).left :=
  have := isIso_vectorBundleMap X f
  (Over.forget X).map_isIso (vectorBundleMap X f)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Chow

/-! ### The normal cone of a regular immersion -/

section NormalCone

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]

/-- **The canonical closed immersion `N_ZX ⟶ N` is an isomorphism when `σ` is.** -/
theorem VirtualNormalBundle.isIso_normalBundleEmbedding (N : VirtualNormalBundle i)
    [IsIso N.surjection] : IsIso N.normalBundleEmbedding := by
  have : IsIso N.conormalDegreeOneSurjection := by
    unfold VirtualNormalBundle.conormalDegreeOneSurjection
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹IsIso N.surjection› (Iso.isIso_hom _)
  exact @Scheme.Modules.isIso_vectorBundleMap_left Z _ _ _ _ N.conormalDegreeOneSurjection this

/-- **The normal cone of a regular immersion is the vector bundle of a virtual normal sheaf whose
surjection `σ` is an isomorphism.** For a regular immersion the canonical morphism
`C_ZX ⟶ N_ZX` is an isomorphism (Stacks 063M), and `N_ZX ⟶ N` is an isomorphism because `σ` is;
so `ι : C_ZX ⟶ N` is an isomorphism. -/
theorem VirtualNormalBundle.isIso_normalConeEmbedding (N : VirtualNormalBundle i)
    [IsIso N.surjection] (hi : IsRegularImmersion i) : IsIso N.normalConeEmbedding := by
  have := Stacks.Conormal.isIso_normalConeToNormalBundle_of_isRegularImmersion i hi
  have := N.isIso_normalBundleEmbedding
  unfold VirtualNormalBundle.normalConeEmbedding
  infer_instance

/-- The structural surjection of the normal bundle of a regular immersion is an isomorphism: it is
the inverse of the reflexivity isomorphism of the conormal sheaf. -/
instance VirtualNormalBundle.isIso_ofIsRegularImmersion_surjection [IsLocallyNoetherian Z]
    (hi : IsRegularImmersion i) :
    IsIso (VirtualNormalBundle.ofIsRegularImmersion i hi).surjection :=
  inferInstanceAs (IsIso (conormalReflexiveIso i hi).inv)

/-- **The normal cone of a regular immersion is its normal bundle**: for the virtual normal
sheaf `𝒞_{Z/X}^∨` of a regular immersion `i`, with `σ` the reflexivity isomorphism, the closed
immersion `ι : C_ZX ⟶ N` is an isomorphism over `Z`. This is the identification
`p : N = C_ZX ⟶ Z` of the proof of Stacks 0FBM. -/
theorem VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion [IsLocallyNoetherian Z]
    (hi : IsRegularImmersion i) :
    IsIso (VirtualNormalBundle.ofIsRegularImmersion i hi).normalConeEmbedding :=
  VirtualNormalBundle.isIso_normalConeEmbedding _ hi

/-- The normal bundle of a regular immersion whose conormal sheaf has constant rank `r` has rank
`r`. -/
instance VirtualNormalBundle.isFiniteLocallyFreeOfRank_ofIsRegularImmersion_bundle
    [IsLocallyNoetherian Z] (hi : IsRegularImmersion i) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle r :=
  inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (dualSheaf (conormalModule i)) r)

end NormalCone

/-! ### Vector bundle projections are surjective -/

/-- **An affine-space bundle is surjective**: locally it is the projection of affine space,
which has the zero section. -/
theorem surjective_of_isAffineSpaceBundle {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℕ)
    (h : IsAffineSpaceBundle f r) : Function.Surjective f.base := by
  intro y
  obtain ⟨U, hy, e, he⟩ := h y
  let s : U.toScheme ⟶ 𝔸(ULift.{u} (Fin r); U.toScheme) :=
    AffineSpace.homOfVector (𝟙 U.toScheme) 0
  have hs : s ≫ (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme) = 𝟙 U.toScheme :=
    AffineSpace.homOfVector_over _ _
  let y' : U.toScheme := ⟨y, hy⟩
  have h1 : (f ∣_ U).base (e.inv.base (s.base y')) = y' := by
    have h := congrArg (fun φ : U.toScheme ⟶ U.toScheme => φ.base y')
      (show s ≫ e.inv ≫ (f ∣_ U) = 𝟙 U.toScheme by rw [← he, e.inv_hom_id_assoc, hs])
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] using h
  refine ⟨(f ⁻¹ᵁ U).ι.base (e.inv.base (s.base y')), ?_⟩
  have h2 := congrArg (fun φ : (f ⁻¹ᵁ U).toScheme ⟶ Y => φ.base (e.inv.base (s.base y')))
    (morphismRestrict_ι f U)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
  rw [← h2, h1]
  rfl

/-- **The projection of the vector bundle of a virtual normal sheaf of constant rank is
surjective.** -/
theorem VirtualNormalBundle.surjective_projection {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]
    (N : VirtualNormalBundle i) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r] :
    Function.Surjective N.projection.base :=
  surjective_of_isAffineSpaceBundle _ r
    (isAffineSpaceBundle_vectorBundleToBase (dualSheaf N.bundle) r)

/-- **Stacks 02R8 read backwards.** If `p : P ⟶ Z` is flat of relative dimension `r` and
surjective, and `dim_δ(P) ≤ n`, then `dim_δ(Z) ≤ n - r`: the `δ`-dimension of `P` is that of `Z`
plus `r`. -/
theorem schemeDeltaDimension_le_sub_of_flat_of_surjective (C : ChowSituation.{u})
    {P Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (p : P ⟶ Z) [LocallyOfFiniteType p] [Flat p] (hp : p ≫ sZ = sP)
    (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension p r)
    (hsurj : Function.Surjective p.base) {n : ℤ}
    (hP : schemeDeltaDimension C sP ≤ (n : EInt)) :
    schemeDeltaDimension C sZ ≤ ((n - (r : ℤ) : ℤ) : EInt) := by
  have hmeets : ∀ V : irreducibleComponents Z, ∃ x : P, p.base x ∈ (V : Set Z) := by
    intro V
    obtain ⟨z, hz⟩ := V.2.1.nonempty
    obtain ⟨x, hx⟩ := hsurj z
    exact ⟨x, hx ▸ hz⟩
  have h := schemeDeltaDimension_comp_eq_add C sZ p r hrel hmeets
  rw [schemeDeltaDimension_congr C hp] at h
  have h' : eintAddRight (r : ℤ) (schemeDeltaDimension C sZ) ≤
      eintAddRight (r : ℤ) ((n - (r : ℤ) : ℤ) : EInt) := by
    rw [eintAddRight_apply, eintAddRight_apply, ← h, ← coe_add_coe_eq_coe_add, sub_add_cancel]
    exact hP
  exact (eintAddRight (r : ℤ)).le_iff_le.mp h'

/-! ### The excess normal sheaf -/

section Excess

variable {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] (N : VirtualNormalBundle i)

/-- The dual `𝒩^∨` of a virtual normal sheaf is finite locally free. -/
theorem VirtualNormalBundle.isFiniteLocallyFree_dualSheaf :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf N.bundle) :=
  isFiniteLocallyFree_dualSheaf_of_schemeOpens N.bundle N.isFiniteLocallyFree

/-- The surjection `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` of a virtual normal sheaf, with its target read as a
module on `Z`, `Stacks.Chow.conormalModule`, so that kernels and duals of it are formed in the
category of `𝒪_Z`-modules. -/
def VirtualNormalBundle.conormalSurjection : dualSheaf N.bundle ⟶ conormalModule i :=
  N.surjection

/-- The morphism `σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` of a virtual normal sheaf is an epimorphism. -/
instance VirtualNormalBundle.epi_conormalSurjection : Epi N.conormalSurjection :=
  N.epi

/-- **The excess normal sheaf** `ℰ = (ker σ)^∨` of a virtual normal sheaf `𝒩` for `i`, with
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` its surjection. When `𝒞_{Z/X}` is finite locally free the sequence
`0 ⟶ ℰ^∨ ⟶ 𝒩^∨ ⟶ 𝒞_{Z/X} ⟶ 0` is short exact and `ℰ` is a finite locally free quotient of
`𝒩`. -/
abbrev VirtualNormalBundle.excessNormalSheaf : Z.Modules :=
  dualSheaf (kernel N.conormalSurjection)

/-- **The sequence `0 ⟶ ker σ ⟶ 𝒩^∨ ⟶ 𝒞_{Z/X} ⟶ 0` is short exact.** -/
theorem VirtualNormalBundle.shortExact_kernel_surjection :
    (ShortComplex.mk (kernel.ι N.conormalSurjection) N.conormalSurjection
      (kernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_kernel N.conormalSurjection }

/-- The kernel of `σ` is finite locally free as soon as the conormal sheaf is: the kernel of an
epimorphism of finite locally free modules is finite locally free. -/
theorem VirtualNormalBundle.isFiniteLocallyFree_kernel_surjection
    (hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (kernel N.conormalSurjection) :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFree_kernel_of_epi N.conormalSurjection
    inferInstance
    N.isFiniteLocallyFree_dualSheaf hC

/-- **The excess normal sheaf is finite locally free** as soon as the conormal sheaf is. -/
theorem VirtualNormalBundle.isFiniteLocallyFree_excessNormalSheaf
    (hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N.excessNormalSheaf :=
  isFiniteLocallyFree_dualSheaf_of_schemeOpens _ (N.isFiniteLocallyFree_kernel_surjection hC)

/-- **The excess normal sheaf has rank `m - r`** when `𝒩` has constant rank `m` and the conormal
sheaf has constant rank `r`. -/
theorem VirtualNormalBundle.isFiniteLocallyFreeOfRank_excessNormalSheaf (m r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle m]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.excessNormalSheaf
      (m - r) :=
  @isFiniteLocallyFreeOfRank_dualSheaf Z (kernel N.conormalSurjection) (m - r)
    (Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
      N.conormalSurjection inferInstance m r inferInstance inferInstance)

variable [IsLocallyNoetherian Z]

/-- The dual of the zero morphism is zero. -/
theorem dualMap_zero {W : Scheme.{u}} {F G : W.Modules} : dualMap (0 : F ⟶ G) = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext t
  refine (eq_zero_of_dualPairing_eq_zero fun V x => ?_).trans ?_
  · rw [dualPairing_dualMap]
    simp only [dualPairing, Scheme.Modules.Hom.zero_app]
    exact map_zero _
  · simp

/-- **The inclusion `𝒞_{Z/X}^∨ ⟶ 𝒩` of the excess sequence**: the dual of `σ`, read on `𝒩`
through the reflexivity isomorphism `𝒩 ≅ 𝒩^∨∨`. -/
def VirtualNormalBundle.excessInclusion : dualSheaf (conormalModule i) ⟶ N.bundle :=
  haveI := isIso_toDoubleDual_of_isFiniteLocallyFree N.bundle N.isFiniteLocallyFree
  dualMap N.conormalSurjection ≫ inv (toDoubleDual N.bundle)

/-- **The projection `𝒩 ⟶ ℰ` of the excess sequence**: the reflexivity isomorphism
`𝒩 ≅ 𝒩^∨∨` followed by the dual of the inclusion `ker σ ⟶ 𝒩^∨`. -/
def VirtualNormalBundle.excessProjection : N.bundle ⟶ N.excessNormalSheaf :=
  toDoubleDual N.bundle ≫ dualMap (kernel.ι N.conormalSurjection)

/-- The composite `𝒞_{Z/X}^∨ ⟶ 𝒩 ⟶ ℰ` of the excess sequence is zero. -/
theorem VirtualNormalBundle.excessInclusion_comp_excessProjection :
    N.excessInclusion ≫ N.excessProjection = 0 := by
  have := isIso_toDoubleDual_of_isFiniteLocallyFree N.bundle N.isFiniteLocallyFree
  show dualMap N.conormalSurjection ≫ inv (toDoubleDual N.bundle) ≫ toDoubleDual N.bundle ≫
    dualMap (kernel.ι N.conormalSurjection) = 0
  rw [IsIso.inv_hom_id_assoc, ← dualMap_comp, kernel.condition]
  exact dualMap_zero

/-- **The excess sequence `0 ⟶ 𝒞_{Z/X}^∨ ⟶ 𝒩 ⟶ ℰ ⟶ 0` is short exact** when the conormal sheaf
is finite locally free: it is the dual of `0 ⟶ ker σ ⟶ 𝒩^∨ ⟶ 𝒞_{Z/X} ⟶ 0`, a short exact sequence
of finite locally free modules (Stacks 0FV8), read on `𝒩` through reflexivity. -/
theorem VirtualNormalBundle.shortExact_excess
    (hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i)) :
    (ShortComplex.mk N.excessInclusion N.excessProjection
      N.excessInclusion_comp_excessProjection).ShortExact := by
  have := isIso_toDoubleDual_of_isFiniteLocallyFree N.bundle N.isFiniteLocallyFree
  obtain ⟨w, hse⟩ := exists_dualSheaf_shortExact (kernel.ι N.conormalSurjection)
    N.conormalSurjection
    (kernel.condition _) inferInstance inferInstance
    (ShortComplex.exact_kernel N.conormalSurjection)
    (N.isFiniteLocallyFree_kernel_surjection hC)
    N.isFiniteLocallyFree_dualSheaf
    hC
  refine ShortComplex.shortExact_of_iso
    (S₁ := ShortComplex.mk (dualMap N.conormalSurjection)
      (dualMap (kernel.ι N.conormalSurjection)) w)
    (ShortComplex.isoMk (Iso.refl _) (asIso (toDoubleDual N.bundle)).symm (Iso.refl _) ?_ ?_) hse
  · exact (Category.id_comp _).symm
  · exact (IsIso.inv_hom_id_assoc (toDoubleDual N.bundle)
      (dualMap (kernel.ι N.conormalSurjection))).trans (Category.comp_id _).symm

/-- **The inclusion of the excess sequence dualizes to a factorization of `σ`** through the
reflexivity isomorphism of the conormal sheaf, which is the surjection of the normal bundle of
the regular immersion: `σ = σ' ∘ (𝒩^∨ ⟶ 𝒞_{Z/X}^∨∨)`. This is the hypothesis of Stacks 0FBL for
the sequence `0 ⟶ 𝒞_{Z/X}^∨ ⟶ 𝒩 ⟶ ℰ ⟶ 0`. -/
theorem VirtualNormalBundle.dualMap_excessInclusion_comp_surjection (hi : IsRegularImmersion i) :
    dualMap N.excessInclusion ≫ (VirtualNormalBundle.ofIsRegularImmersion i hi).surjection =
      N.surjection := by
  have := isIso_toDoubleDual_of_isFiniteLocallyFree N.bundle N.isFiniteLocallyFree
  have hdual : dualMap (inv (toDoubleDual N.bundle)) = toDoubleDual (dualSheaf N.bundle) := by
    have h1 : toDoubleDual (dualSheaf N.bundle) ≫ dualMap (toDoubleDual N.bundle) = 𝟙 _ :=
      toDoubleDual_dualMap_comp N.bundle
    have h2 : dualMap (inv (toDoubleDual N.bundle)) ≫ dualMap (toDoubleDual N.bundle) = 𝟙 _ := by
      rw [← dualMap_comp, IsIso.hom_inv_id, dualMap_id]
    have : IsIso (dualMap (toDoubleDual N.bundle)) :=
      ⟨⟨dualMap (inv (toDoubleDual N.bundle)), by rw [← dualMap_comp, IsIso.inv_hom_id,
        dualMap_id], h2⟩⟩
    exact (cancel_mono (dualMap (toDoubleDual N.bundle))).mp (h2.trans h1.symm)
  show _ = N.conormalSurjection
  rw [VirtualNormalBundle.excessInclusion, dualMap_comp, hdual,
    VirtualNormalBundle.ofIsRegularImmersion_surjection, regularNormalSurjection]
  have hnat := toDoubleDual_naturality N.conormalSurjection
  exact (congrArg (fun φ : dualSheaf N.bundle ⟶ dualSheaf (dualSheaf (conormalModule i)) =>
      φ ≫ (conormalReflexiveIso i hi).inv) hnat.symm).trans
    (((Category.assoc _ _ _).trans
      (congrArg (N.conormalSurjection ≫ ·) (conormalReflexiveIso i hi).hom_inv_id)).trans
      (Category.comp_id _))

end Excess

end Stacks.Chow

end
