module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Branches
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The zero scheme of a tensor product of two sections is the union of the two zero schemes

Let `X` be a scheme, let `M` and `N` be invertible `𝒪_X`-modules and let `a ∈ Γ(X, M)`,
`b ∈ Γ(X, N)`. The zero scheme of `a ⊗ b` always contains the scheme-theoretic union of `Z(a)` and
`Z(b)` (`Stacks.Divisors.zeroScheme_tensorSection_le_inf`). This file proves the converse under the
hypothesis that the restriction of `b` to `Z(a)` is a *regular* section of the restricted module,
and so identifies `Z(a ⊗ b)` with that union. This is clause (5) of
[Stacks, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97), whose local content is the ideal
identity `(α) ∩ (β) = (αβ)` for `β` a nonzerodivisor modulo `α`.

Throughout, the order on `AlgebraicGeometry.Scheme.IdealSheafData` is the order on *ideals*, so
`⊓` of two ideal sheaves is the ideal sheaf of the scheme-theoretic *union* of the two closed
subschemes; the equality below therefore reads `Z(a) ∪ Z(b) = Z(a ⊗ b)`.

## Main results

* `Stacks.Divisors.zeroScheme_ideal_tensorSection_of_generators`: the local equation of `Z(a ⊗ b)`
  on an affine open carrying local generators of `M` and of `N` is the product of the two local
  equations.
* `Stacks.Divisors.isSMulRegular_app_subschemeι_of_isRegularSection`: if the restriction of `b` to
  a closed subscheme `Z` is a regular section, then on an affine open `U` of `X` over which the
  restricted module is trivial, the image of a local equation of `Z(b)` in
  `Γ(Z, i⁻¹U) = Γ(X, U)/ℐ_Z(U)` is a nonzerodivisor.
* `Stacks.Divisors.inf_zeroScheme_le_zeroScheme_tensorSection`: `Z(a) ⊓ Z(b) ≤ Z(a ⊗ b)`.
* `Stacks.Divisors.zeroScheme_tensorSection_eq_inf`: the equality `Z(a) ⊓ Z(b) = Z(a ⊗ b)`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules (GeneratorSections generatorRestrict generator_restrict_self
  tmulGenerator)

universe u

namespace Stacks.Divisors

/-! ### Two ring-theoretic steps -/

/-- If `β` is a nonzerodivisor modulo `α`, witnessed by a ring map `q` whose kernel is `(α)`, then
`(α) ∩ (β) ⊆ (αβ)`. -/
theorem inf_span_singleton_le_span_singleton_mul_of_ker {R S : Type*} [CommRing R] [CommRing S]
    (q : R →+* S) (α β : R) (hα : q α = 0) (hker : RingHom.ker q ≤ Ideal.span {α})
    (hreg : IsSMulRegular S (q β)) :
    Ideal.span ({α} : Set R) ⊓ Ideal.span ({β} : Set R) ≤ Ideal.span ({α * β} : Set R) := by
  have hspan : Ideal.span ({α} : Set R) ≤ RingHom.ker q :=
    Ideal.span_le.mpr (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker] using hα)
  rintro x ⟨hxα, hxβ⟩
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hxβ
  have hv : q v = 0 := hreg <| by
    simp only [smul_eq_mul, mul_zero]
    rw [mul_comm, ← map_mul]
    exact hspan hxα
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp (hker hv)
  exact Ideal.mem_span_singleton'.mpr ⟨w, by ring⟩

/-- If `α` is a unit, then `(α) ∩ (β) ⊆ (αβ)`. -/
theorem inf_span_singleton_le_span_singleton_mul_of_isUnit {R : Type*} [CommRing R] {α : R}
    (hα : IsUnit α) (β : R) :
    Ideal.span ({α} : Set R) ⊓ Ideal.span ({β} : Set R) ≤ Ideal.span ({α * β} : Set R) := by
  obtain ⟨u, rfl⟩ := hα
  rintro x ⟨-, hxβ⟩
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.mp hxβ
  refine Ideal.mem_span_singleton'.mpr ⟨(↑u⁻¹ : R) * v, ?_⟩
  calc (↑u⁻¹ * v) * ((u : R) * β) = ((↑u⁻¹ : R) * (u : R)) * (v * β) := by ring
    _ = v * β := by rw [u.inv_mul, one_mul]

/-! ### Local generators and their coordinates -/

variable {X : Scheme.{u}}

/-- The section underlying a local generator, as an element of `Γ(L, U)`, the type carrying the
`Γ(X, U)`-module structure on the sections of an `𝒪_X`-module. -/
abbrev generatorVal (L : X.Modules) {U : X.Opens}
    (g : GeneratorSections X.toRingedSpace L U) : Γ(L, U) :=
  g.val

/-- Multiplication by a local generator is bijective on the open it is a generator over. -/
theorem bijective_smul_generator (L : X.Modules) {U : X.Opens}
    (g : GeneratorSections X.toRingedSpace L U) :
    Function.Bijective (fun r : Γ(X, U) => r • generatorVal L g) := by
  have hbij := g.property U le_rfl
  rwa [generator_restrict_self L U g] at hbij

/-- The restriction of a local generator is the restriction of its section. -/
theorem generatorVal_generatorRestrict (L : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (g : GeneratorSections X.toRingedSpace L U) :
    generatorVal L (generatorRestrict L h g) = L.presheaf.map (homOfLE h).op (generatorVal L g) :=
  rfl

/-- The coordinate of the restriction of a global section in the frame of a local generator. -/
theorem exists_coord_of_generator (L : X.Modules) (s : Γ(L, ⊤)) {U : X.Opens}
    (g : GeneratorSections X.toRingedSpace L U) :
    ∃ α : Γ(X, U), L.presheaf.map (homOfLE le_top).op s = α • generatorVal L g := by
  obtain ⟨α, hα⟩ :=
    (bijective_smul_generator L g).surjective (L.presheaf.map (homOfLE le_top).op s)
  exact ⟨α, hα.symm⟩

/-- The coordinate of a global section in the frame of a local generator restricts to its
coordinate in the frame of the restricted generator. -/
theorem coord_restrict_of_generator (L : X.Modules) (s : Γ(L, ⊤)) {U V : X.Opens} (h : V ≤ U)
    (g : GeneratorSections X.toRingedSpace L U) (α : Γ(X, U))
    (hα : L.presheaf.map (homOfLE le_top).op s = α • generatorVal L g) :
    L.presheaf.map (homOfLE le_top).op s =
      X.presheaf.map (homOfLE h).op α • generatorVal L (generatorRestrict L h g) := by
  rw [← Scheme.Modules.map_map_le_top L s h, hα, Scheme.Modules.map_smul,
    generatorVal_generatorRestrict]

/-! ### The local equation of the zero scheme of a tensor product -/

variable (M N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- The ideal of the zero scheme of `s` on an affine open with a generator `g` is spanned by the
coordinate of `s` in the frame `g`. -/
private theorem zeroScheme_ideal_eq_span_of_generator (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (U : X.affineOpens) (g : GeneratorSections X.toRingedSpace L U.1) (α : Γ(X, U.1))
    (h : L.presheaf.map (homOfLE le_top).op s = α • generatorVal L g) :
    (zeroScheme X L s).ideal U = Ideal.span ({α} : Set Γ(X, U.1)) :=
  zeroScheme_ideal_eq_span_singleton_of_bijective_smul X L s U (generatorVal L g)
    (bijective_smul_generator L g) α h

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] in
/-- Scaling the first argument of `Stacks.Divisors.tensorSection` scales the result. -/
theorem tensorSection_smul_left (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    tensorSection M N U (r • m) n = r • tensorSection M N U m n :=
  (tensorSectionRight_apply M N U n (r • m)).symm.trans
    ((map_smul (tensorSectionRight M N U n) r m).trans
      (congrArg (fun z => r • z) (tensorSectionRight_apply M N U n m)))

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] in
/-- Scaling the second argument of `Stacks.Divisors.tensorSection` scales the result. -/
theorem tensorSection_smul_right (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
    tensorSection M N U m (r • n) = r • tensorSection M N U m n :=
  (tensorSectionLeft_apply M N U m (r • n)).symm.trans
    ((map_smul (tensorSectionLeft M N U m) r n).trans
      (congrArg (fun z => r • z) (tensorSectionLeft_apply M N U m n)))

/-- On an affine open carrying a generator `g` of `M` and a generator `w` of `N`, the ideal of
`Z(a ⊗ b)` is generated by the product `α β` of the coordinates in `a = α · g` and `b = β · w`. -/
theorem zeroScheme_ideal_tensorSection_of_generators (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (U : X.affineOpens)
    (g : GeneratorSections X.toRingedSpace M U.1) (w : GeneratorSections X.toRingedSpace N U.1)
    (α β : Γ(X, U.1)) (ha : M.presheaf.map (homOfLE le_top).op a = α • generatorVal M g)
    (hb : N.presheaf.map (homOfLE le_top).op b = β • generatorVal N w) :
    (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b)).ideal U =
      Ideal.span ({α * β} : Set Γ(X, U.1)) := by
  have hprod : tensorSection M N U.1 (generatorVal M g) (generatorVal N w) =
      generatorVal (tensorModules M N) (tmulGenerator g w) := rfl
  refine zeroScheme_ideal_eq_span_singleton_of_bijective_smul X (tensorModules M N)
    (tensorSection M N ⊤ a b) U (generatorVal (tensorModules M N) (tmulGenerator g w))
    (bijective_smul_generator (tensorModules M N) (tmulGenerator g w)) (α * β) ?_
  rw [tensorSection_restrict M N (homOfLE (le_top : U.1 ≤ ⊤)) a b, ha, hb,
    tensorSection_smul_left, tensorSection_smul_right, smul_smul, hprod]

/-! ### The regularity hypothesis on an affine open -/

/-- Let `i : Z → X` be the closed subscheme cut out by a quasi-coherent ideal sheaf and suppose
the restriction `i^*b` of a global section `b` of an invertible module `N` is a regular section of
`i^*N`. Let `U` be an affine open of `X` over which `i^*N` is trivial and let `β` generate the
ideal of `Z(b)` on `U`. Then the image of `β` in `Γ(Z, i⁻¹U)` is a nonzerodivisor. -/
theorem isSMulRegular_app_subschemeι_of_isRegularSection (I : X.IdealSheafData) (b : Γ(N, ⊤))
    (hb : AlgebraicGeometry.IsRegularSection I.subscheme.sheaf.obj
      I.subscheme.ringCatSheaf.property
      (sectionsOfTop ((Scheme.Modules.pullback I.subschemeι).obj N)
        (AlgebraicGeometry.pullbackGlobalSections I.subschemeι N b)))
    (U : X.affineOpens) (β : Γ(X, U.1))
    (hβ : (zeroScheme X N b).ideal U = Ideal.span ({β} : Set Γ(X, U.1)))
    (he : Nonempty
      (Γ((Scheme.Modules.pullback I.subschemeι).obj N, I.subschemeι ⁻¹ᵁ U.1)
        ≃ₗ[Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)] Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1))) :
    IsSMulRegular Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) ((I.subschemeι.app U.1).hom β) := by
  obtain ⟨e⟩ := he
  obtain ⟨γ, hγ1, hγreg⟩ : ∃ γ : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1),
      (zeroScheme I.subscheme ((Scheme.Modules.pullback I.subschemeι).obj N)
            (AlgebraicGeometry.pullbackGlobalSections I.subschemeι N b)).ideal
          ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage I.subschemeι⟩ =
        Ideal.span ({γ} : Set Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)) ∧ IsRegular γ := by
    refine ⟨e (((Scheme.Modules.pullback I.subschemeι).obj N).presheaf.map (homOfLE le_top).op
      (AlgebraicGeometry.pullbackGlobalSections I.subschemeι N b)), ?_, ?_⟩
    · exact zeroScheme_ideal_of_trivialization I.subscheme
        ((Scheme.Modules.pullback I.subschemeι).obj N)
        (AlgebraicGeometry.pullbackGlobalSections I.subschemeι N b)
        ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage I.subschemeι⟩ e _ rfl
    · have h := AlgebraicGeometry.isRegular_coordinate_of_isRegularSection I.subscheme
        ((Scheme.Modules.pullback I.subschemeι).obj N)
        (sectionsOfTop ((Scheme.Modules.pullback I.subschemeι).obj N)
          (AlgebraicGeometry.pullbackGlobalSections I.subschemeι N b)) hb
        ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage I.subschemeι⟩ e
      rwa [sectionsOfTop_eval_top] at h
  have h2 : (zeroScheme I.subscheme ((Scheme.Modules.pullback I.subschemeι).obj N)
          (AlgebraicGeometry.pullbackGlobalSections I.subschemeι N b)).ideal
        ⟨I.subschemeι ⁻¹ᵁ U.1, U.2.preimage I.subschemeι⟩ =
      Ideal.span ({(I.subschemeι.app U.1).hom β} :
        Set Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)) := by
    rw [zeroScheme_pullback I.subschemeι N b,
      Stacks.IdealSheaf.ideal_comap_of_isAffineHom (zeroScheme X N b) I.subschemeι U, hβ,
      Ideal.map_span, Set.image_singleton]
  have h3 : γ ∈ Ideal.span ({(I.subschemeι.app U.1).hom β} :
      Set Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)) := by
    rw [← h2, hγ1]
    exact Ideal.mem_span_singleton_self γ
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h3
  have hreg : IsRegular ((I.subschemeι.app U.1).hom β) :=
    IsRegular.of_mul_left (b := d) (by rwa [mul_comm, hd])
  exact hreg.left

/-! ### The inequality and the equality -/

/-- Every point of an open has an affine open neighbourhood inside it carrying a generator of `M`
and a generator of `N`. -/
theorem exists_affineOpens_generator_pair (x : X) (V : X.Opens) (hx : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (GeneratorSections X.toRingedSpace M U.1) ∧
      Nonempty (GeneratorSections X.toRingedSpace N U.1) := by
  obtain ⟨U₁, hx₁, ⟨g₁⟩⟩ := AlgebraicGeometry.exists_affineOpens_generator M x
  obtain ⟨U₂, hx₂, ⟨w₂⟩⟩ := AlgebraicGeometry.exists_affineOpens_generator N x
  obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V ⊓ U₁.1 ⊓ U₂.1 from ⟨⟨hx, hx₁⟩, hx₂⟩) (V ⊓ U₁.1 ⊓ U₂.1).isOpen
  exact ⟨⟨W, hW⟩, hxW, fun y hy => (hWle hy).1.1,
    ⟨generatorRestrict M (fun y hy => (hWle hy).1.2) g₁⟩,
    ⟨generatorRestrict N (fun y hy => (hWle hy).2) w₂⟩⟩

/-- On an affine open carrying a generator `g` of `M` and a generator `w` of `N`, with
`a = α · g` and `b = β · w`, if `(α) ∩ (β) ⊆ (αβ)` then the ideal of `Z(a) ⊓ Z(b)` is contained in
the ideal of `Z(a ⊗ b)`. -/
theorem ideal_inf_le_of_generators (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) (U : X.affineOpens)
    (g : GeneratorSections X.toRingedSpace M U.1) (w : GeneratorSections X.toRingedSpace N U.1)
    (α β : Γ(X, U.1)) (ha : M.presheaf.map (homOfLE le_top).op a = α • generatorVal M g)
    (hb : N.presheaf.map (homOfLE le_top).op b = β • generatorVal N w)
    (hkey : Ideal.span ({α} : Set Γ(X, U.1)) ⊓ Ideal.span ({β} : Set Γ(X, U.1)) ≤
      Ideal.span ({α * β} : Set Γ(X, U.1))) :
    (zeroScheme X M a).ideal U ⊓ (zeroScheme X N b).ideal U ≤
      (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b)).ideal U := by
  rw [zeroScheme_ideal_eq_span_of_generator M a U g α ha,
    zeroScheme_ideal_eq_span_of_generator N b U w β hb,
    zeroScheme_ideal_tensorSection_of_generators M N a b U g w α β ha hb]
  exact hkey

/-- If the restriction of `b` to `Z(a)` is a regular section, every point of `X` has an affine
open neighbourhood on which the ideal of `Z(a) ⊓ Z(b)` is contained in the ideal of `Z(a ⊗ b)`. -/
theorem exists_affineOpens_inf_ideal_le (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (hb : AlgebraicGeometry.IsRegularSection (zeroScheme X M a).subscheme.sheaf.obj
      (zeroScheme X M a).subscheme.ringCatSheaf.property
      (sectionsOfTop ((Scheme.Modules.pullback (zeroScheme X M a).subschemeι).obj N)
        (AlgebraicGeometry.pullbackGlobalSections (zeroScheme X M a).subschemeι N b)))
    (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      (zeroScheme X M a).ideal U ⊓ (zeroScheme X N b).ideal U ≤
        (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b)).ideal U := by
  classical
  obtain ⟨W, hxW, -, ⟨g₀⟩, ⟨w₀⟩⟩ := exists_affineOpens_generator_pair M N x ⊤ trivial
  obtain ⟨α₀, hα₀⟩ := exists_coord_of_generator M a g₀
  obtain ⟨β₀, hβ₀⟩ := exists_coord_of_generator N b w₀
  have key : ∀ (V : X.affineOpens) (hV : V.1 ≤ W.1),
      Ideal.span {X.presheaf.map (homOfLE hV).op α₀} ⊓
          Ideal.span {X.presheaf.map (homOfLE hV).op β₀} ≤
        Ideal.span {X.presheaf.map (homOfLE hV).op α₀ * X.presheaf.map (homOfLE hV).op β₀} →
      (zeroScheme X M a).ideal V ⊓ (zeroScheme X N b).ideal V ≤
        (zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b)).ideal V :=
    fun V hV hk => ideal_inf_le_of_generators M N a b V
      (generatorRestrict M hV g₀) (generatorRestrict N hV w₀)
      (X.presheaf.map (homOfLE hV).op α₀) (X.presheaf.map (homOfLE hV).op β₀)
      (coord_restrict_of_generator M a hV g₀ α₀ hα₀)
      (coord_restrict_of_generator N b hV w₀ β₀ hβ₀) hk
  by_cases hx : x ∈ (zeroScheme X M a).supportSet
  · obtain ⟨y, hy⟩ : ∃ y, (zeroScheme X M a).subschemeι.base y = x := by
      change x ∈ Set.range (zeroScheme X M a).subschemeι
      rwa [Scheme.IdealSheafData.range_subschemeι]
    have hVaff : IsAffineOpen ((zeroScheme X M a).subschemeι ⁻¹ᵁ W.1) :=
      W.2.preimage (zeroScheme X M a).subschemeι
    have hyV : y ∈ (zeroScheme X M a).subschemeι ⁻¹ᵁ W.1 := by
      change (zeroScheme X M a).subschemeι.base y ∈ W.1
      rwa [hy]
    obtain ⟨k, hyk, -, ⟨e⟩⟩ := AlgebraicGeometry.exists_basicOpen_linearEquiv
      ((Scheme.Modules.pullback (zeroScheme X M a).subschemeι).obj N)
      ⟨(zeroScheme X M a).subschemeι ⁻¹ᵁ W.1, hVaff⟩ y hyV
    obtain ⟨f, hf⟩ := Scheme.IdealSheafData.subschemeι_app_surjective (zeroScheme X M a) W k
    have hpre : (zeroScheme X M a).subschemeι ⁻¹ᵁ X.basicOpen f =
        (zeroScheme X M a).subscheme.basicOpen k := by
      rw [Scheme.preimage_basicOpen, hf]
    have hyf : y ∈ (zeroScheme X M a).subschemeι ⁻¹ᵁ X.basicOpen f := by
      rwa [hpre]
    have hxf : x ∈ X.basicOpen f := by
      rw [← hy]
      exact hyf
    have hUW : X.basicOpen f ≤ W.1 := X.basicOpen_le f
    have he : Nonempty
        (Γ((Scheme.Modules.pullback (zeroScheme X M a).subschemeι).obj N,
              (zeroScheme X M a).subschemeι ⁻¹ᵁ X.basicOpen f)
            ≃ₗ[Γ((zeroScheme X M a).subscheme,
              (zeroScheme X M a).subschemeι ⁻¹ᵁ X.basicOpen f)]
          Γ((zeroScheme X M a).subscheme,
            (zeroScheme X M a).subschemeι ⁻¹ᵁ X.basicOpen f)) := by
      rw [hpre]
      exact ⟨e⟩
    refine ⟨⟨X.basicOpen f, W.2.basicOpen f⟩, hxf, key _ hUW ?_⟩
    have hIa : (zeroScheme X M a).ideal ⟨X.basicOpen f, W.2.basicOpen f⟩ =
        Ideal.span ({X.presheaf.map (homOfLE hUW).op α₀} : Set Γ(X, X.basicOpen f)) :=
      zeroScheme_ideal_eq_span_of_generator M a ⟨X.basicOpen f, W.2.basicOpen f⟩
        (generatorRestrict M hUW g₀) _ (coord_restrict_of_generator M a hUW g₀ α₀ hα₀)
    have hker : RingHom.ker ((zeroScheme X M a).subschemeι.app (X.basicOpen f)).hom =
        Ideal.span ({X.presheaf.map (homOfLE hUW).op α₀} : Set Γ(X, X.basicOpen f)) := by
      rw [← hIa, ← Scheme.Hom.ker_apply (zeroScheme X M a).subschemeι
        ⟨X.basicOpen f, W.2.basicOpen f⟩, Scheme.IdealSheafData.ker_subschemeι]
    have hαzero : ((zeroScheme X M a).subschemeι.app (X.basicOpen f)).hom
        (X.presheaf.map (homOfLE hUW).op α₀) = 0 :=
      RingHom.mem_ker.1 (hker.ge (Ideal.mem_span_singleton_self _))
    exact inf_span_singleton_le_span_singleton_mul_of_ker
      ((zeroScheme X M a).subschemeι.app (X.basicOpen f)).hom _ _ hαzero hker.le
      (isSMulRegular_app_subschemeι_of_isRegularSection N (zeroScheme X M a) b hb
        ⟨X.basicOpen f, W.2.basicOpen f⟩ _
        (zeroScheme_ideal_eq_span_of_generator N b _ (generatorRestrict N hUW w₀) _
          (coord_restrict_of_generator N b hUW w₀ β₀ hβ₀)) he)
  · have hIW : (zeroScheme X M a).ideal W = Ideal.span ({α₀} : Set Γ(X, W.1)) :=
      zeroScheme_ideal_eq_span_of_generator M a W g₀ α₀ hα₀
    have hz : x ∉ X.zeroLocus (U := W.1) ((zeroScheme X M a).ideal W : Set Γ(X, W.1)) := fun h =>
      hx ((Scheme.IdealSheafData.mem_supportSet_iff_of_mem hxW).mpr h)
    rw [hIW] at hz
    have hxb : x ∈ X.basicOpen α₀ := by
      by_contra hcon
      refine hz ((X.mem_zeroLocus_iff _ x).mpr fun r hr hmem => hcon ?_)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      rw [Scheme.basicOpen_mul] at hmem
      exact hmem.2
    have hUW : X.basicOpen α₀ ≤ W.1 := X.basicOpen_le α₀
    exact ⟨⟨X.basicOpen α₀, W.2.basicOpen α₀⟩, hxb, key _ hUW
      (inf_span_singleton_le_span_singleton_mul_of_isUnit
        (X.toRingedSpace.isUnit_res_basicOpen α₀) _)⟩

/-- If the restriction of `b` to the zero scheme of `a` is a regular section of the restricted
module, then the scheme-theoretic union of `Z(a)` and `Z(b)` is contained in `Z(a ⊗ b)`; in the
order on ideal sheaves, which is the order on ideals, this reads `Z(a) ⊓ Z(b) ≤ Z(a ⊗ b)`. -/
theorem inf_zeroScheme_le_zeroScheme_tensorSection (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (hb : AlgebraicGeometry.IsRegularSection (zeroScheme X M a).subscheme.sheaf.obj
      (zeroScheme X M a).subscheme.ringCatSheaf.property
      (sectionsOfTop ((Scheme.Modules.pullback (zeroScheme X M a).subschemeι).obj N)
        (AlgebraicGeometry.pullbackGlobalSections (zeroScheme X M a).subschemeι N b))) :
    zeroScheme X M a ⊓ zeroScheme X N b ≤
      zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b) := by
  classical
  choose U hxU hle using exists_affineOpens_inf_ideal_le M N a b hb
  exact Scheme.IdealSheafData.le_of_iSup_eq_top U
    (eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩) hle

/-- If the restriction of `b` to the zero scheme of `a` is a regular section of the restricted
module, then the zero scheme of `a ⊗ b` is the scheme-theoretic union of `Z(a)` and `Z(b)`; in the
order on ideal sheaves, which is the order on ideals, this reads `Z(a) ⊓ Z(b) = Z(a ⊗ b)`. -/
theorem zeroScheme_tensorSection_eq_inf (a : Γ(M, ⊤)) (b : Γ(N, ⊤))
    (hb : AlgebraicGeometry.IsRegularSection (zeroScheme X M a).subscheme.sheaf.obj
      (zeroScheme X M a).subscheme.ringCatSheaf.property
      (sectionsOfTop ((Scheme.Modules.pullback (zeroScheme X M a).subschemeι).obj N)
        (AlgebraicGeometry.pullbackGlobalSections (zeroScheme X M a).subschemeι N b))) :
    zeroScheme X M a ⊓ zeroScheme X N b =
      zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b) :=
  le_antisymm (inf_zeroScheme_le_zeroScheme_tensorSection M N a b hb)
    (zeroScheme_tensorSection_le_inf M N a b)

end Stacks.Divisors

end
