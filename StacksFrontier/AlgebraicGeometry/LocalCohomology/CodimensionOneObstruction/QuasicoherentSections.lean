module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Modules.QcqsLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a quasi-coherent module away from a codimension-one point

Let `X` be an integral locally Noetherian scheme, `V₀` an affine open, `z` a point of `V₀` whose
local ring has dimension at most one, and `S` a nonempty open of `V₀` not containing `z`. This
file proves that for a quasi-coherent `𝒪_X`-module `M` whose stalk at the generic point is
nonzero, `Γ(M, S)` is **not** a finite `Γ(X, V₀)`-module, and that the direct image along
`S → X` of the restriction of `M` to `S` is not coherent.

This generalizes `Stacks.AlgebraicGeometry.CodimensionOneObstruction.not_moduleFinite_sections`,
which is the case `M = 𝒪_X`, from the structure sheaf to an arbitrary quasi-coherent module. It
is the first paragraph of [Stacks, Tag 0AWC] for a general coherent module, in the case where the
associated point in question is the generic point of `X` itself.

## Main results

* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_section_germ_ne_zero`: if the stalk
  of `M` at the generic point is nonzero then already some section of `M` over `S` has nonzero
  germ there.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.not_moduleFinite_sections_of_germ_ne_zero`:
  a section of `M` over `S` with nonzero germ at the generic point makes `Γ(M, S)` not finite
  over `Γ(X, V₀)`.
* `not_moduleFinite_sections_of_modStalk_ne_zero`, in the same namespace: if the stalk of `M` at
  the generic point is nonzero then `Γ(M, S)` is not finite over `Γ(X, V₀)`.
* `Stacks.AlgebraicGeometry.CodimensionOneObstruction.isLocalizedModule_germₗ`: the stalk of `M`
  at the generic point is the localization of `Γ(M, S)` at the prime of `Γ(X, V₀)` attached to `z`.
* `not_isCoherent_pushforward_restrict_of_modStalk_ne_zero`, in the same namespace: if the stalk
  of `M` at the generic point is nonzero then `(S → X)_* (M|_S)` is not coherent.

## Implementation notes

Stalks of modules are spelled with `Stacks.SheafOfModules.SheafHomStalk.modStalk` and
`Stacks.SheafOfModules.SheafHomStalk.germAt`, whose scalars live in
`Stacks.SheafOfModules.SheafHomStalk.ringStalk X.sheaf x`. That is the same local ring as
`X.presheaf.stalk x`, but the two spellings are not interchangeable for instance search, which is
why `ringGermAt` below is provided and why the `Field X.functionField` instance is reached
through an explicit transport inside `isUnit_ringGermAt_genericPoint`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.SheafHomStalk
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.QcqsLocalization

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

variable {X : Scheme.{u}}

/-! ### Germs at the generic point -/

/-- The generic point of an irreducible scheme lies in every nonempty open. -/
theorem genericPoint_mem [IrreducibleSpace X] (S : X.Opens) [h : Nonempty S.toScheme] :
    genericPoint X ∈ S :=
  ((genericPoint_spec X).mem_open_set_iff S.isOpen).mpr (by simpa using h)

/-- The germ of a function, spelled at the `ringStalk` form of the local ring in which the
scalars of `Stacks.SheafOfModules.SheafHomStalk.modStalk` live. -/
noncomputable abbrev ringGermAt (X : Scheme.{u}) (S : X.Opens) (x : X) (hx : x ∈ S)
    (a : Γ(X, S)) : ringStalk X.sheaf x :=
  TopCat.Presheaf.germ X.sheaf.obj S x hx a

/-- Germs of sections of a module are unchanged by restriction. -/
theorem germAt_map (M : X.Modules) {S T : X.Opens} (h : T ≤ S) {x : X} (hx : x ∈ T)
    (m : Γ(M, S)) :
    germAt M T x hx (M.presheaf.map (homOfLE h).op m) = germAt M S x (h hx) m :=
  germAt_resLE M h hx m

/-- Germs of functions are unchanged by restriction. -/
theorem ringGermAt_map {S T : X.Opens} (h : T ≤ S) {x : X} (hx : x ∈ T) (a : Γ(X, S)) :
    ringGermAt X T x hx (X.presheaf.map (homOfLE h).op a) = ringGermAt X S x (h hx) a :=
  TopCat.Presheaf.germ_res_apply X.sheaf.obj (homOfLE h) x hx a

/-- The germ of a scalar multiple, with the scalar action spelled as the one instance search
finds on `Γ(M, S)`: the germ of `a • m` is the germ of `a` times the germ of `m`. -/
theorem germAt_smul' (M : X.Modules) {S : X.Opens} {x : X} (hx : x ∈ S) (a : Γ(X, S))
    (m : Γ(M, S)) :
    germAt M S x hx (a • m) = ringGermAt X S x hx a • germAt M S x hx m :=
  germAt_smul M hx a m

/-- On an integral scheme the germ at the generic point of a nonzero function is a unit, because
the local ring there is the function field. -/
theorem isUnit_ringGermAt_genericPoint [IsIntegral X] {S : X.Opens}
    (hS : genericPoint X ∈ S) {a : Γ(X, S)} (ha : a ≠ 0) :
    IsUnit (ringGermAt X S (genericPoint X) hS a) := by
  have h : IsUnit (X.presheaf.germ S (genericPoint X) hS a) := by
    refine Ne.isUnit fun h0 => ha ?_
    exact germ_injective_of_isIntegral (X := X) (genericPoint X) hS (by rw [h0, map_zero])
  exact h

/-! ### A generically nonvanishing section has zero annihilator -/

/-- On an integral scheme, a section of `M` over `S` with nonzero germ at the generic point has
zero annihilator: if `a • m = 0` then `a = 0`. -/
theorem eq_zero_of_smul_eq_zero [IsIntegral X] (M : X.Modules) {S : X.Opens}
    (hS : genericPoint X ∈ S) {m : Γ(M, S)} (hm : germAt M S (genericPoint X) hS m ≠ 0)
    {a : Γ(X, S)} (hma : a • m = 0) : a = 0 := by
  by_contra ha
  refine hm ?_
  have h1 : ringGermAt X S (genericPoint X) hS a • germAt M S (genericPoint X) hS m = 0 := by
    rw [← germAt_smul' M hS a m, hma]
    exact germAt_zero M hS
  exact (isUnit_ringGermAt_genericPoint hS ha).smul_eq_zero.mp h1

/-- Multiplication by a fixed section of `M` over `S`, as a `Γ(X, V₀)`-linear map from the
functions on `S`. -/
noncomputable def smulSectionₗ (M : X.Modules) {V₀ S : X.Opens} (hSV : S ≤ V₀) (m : Γ(M, S)) :
    letI := resAlgebra hSV
    letI := moduleOfLE M hSV
    Γ(X, S) →ₗ[Γ(X, V₀)] Γ(M, S) :=
  let := resAlgebra hSV
  let := moduleOfLE M hSV
  { toFun := fun a => a • m
    map_add' := fun a b => add_smul a b m
    map_smul' := fun r a => by
      have h : (X.presheaf.map (homOfLE hSV).op r * a) • m
          = (X.presheaf.map (homOfLE hSV).op r) • (a • m) := mul_smul _ _ _
      exact h }

/-- Let `X` be integral and locally Noetherian, let `V₀` be an affine open containing a point `z`
whose local ring has dimension at most one, and let `S` be a nonempty open of `V₀` avoiding `z`.
If `M` has a section over `S` whose germ at the generic point is nonzero, then `Γ(M, S)` is not a
finite `Γ(X, V₀)`-module. -/
theorem not_moduleFinite_sections_of_germ_ne_zero [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (M : X.Modules) (m : Γ(M, S))
    (hm : germAt M S (genericPoint X) (genericPoint_mem S) m ≠ 0) :
    ¬ (letI := moduleOfLE M hSV; Module.Finite Γ(X, V₀) Γ(M, S)) := by
  intro hfin
  have : Nonempty V₀.toScheme := ⟨⟨z, hz⟩⟩
  let := resAlgebra hSV
  let := moduleOfLE M hSV
  have := hfin
  have : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  have hinj : Function.Injective (smulSectionₗ M hSV m) := by
    intro a b hab
    have hab' : a • m = b • m := hab
    have h0 : (a - b) • m = 0 := by rw [sub_smul, hab', sub_self]
    exact eq_of_sub_eq_zero
      (eq_zero_of_smul_eq_zero M (genericPoint_mem S) hm h0)
  exact not_moduleFinite_sections hV₀ hz hdim hSV hzS
    (Module.Finite.of_injective (smulSectionₗ M hSV m) hinj)

/-! ### Producing a generically nonvanishing section over `S` -/

/-- A function on an affine open that is outside the prime of a point is nonzero. -/
private theorem ne_zero_of_mem_primeCompl_primeIdealOf {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    {z : X} (hz : z ∈ V₀) {g : Γ(X, V₀)}
    (hg : g ∈ (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl) : g ≠ 0 :=
  fun h0 => hg (by rw [h0]; exact Ideal.zero_mem _)

/-- A function `g` on `V₀` that is nonzero at `z` has a basic open, after restriction to `S`,
which contains the generic point and lies inside any given open `W` containing it. -/
private theorem exists_mem_primeCompl_basicOpen_res_le [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) {W : X.Opens} (hgenW : genericPoint X ∈ W) :
    ∃ g : Γ(X, V₀), g ∈ (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl ∧
      genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE hSV).op g) ∧
      X.basicOpen (X.presheaf.map (homOfLE hSV).op g) ≤ W := by
  obtain ⟨g, hzg, hle⟩ := exists_basicOpen_inter_le hV₀ hz hdim (S := S) (W := W) hzS hgenW
  have hbas : X.basicOpen (X.presheaf.map (homOfLE hSV).op g) = S ⊓ X.basicOpen g :=
    Scheme.basicOpen_res _ _ _
  have : Nonempty (X.basicOpen g) := ⟨⟨z, hzg⟩⟩
  exact ⟨g, (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hz g).mp hzg,
    hbas ▸ ⟨genericPoint_mem S, genericPoint_mem _⟩, hbas ▸ hle⟩

/-- **Clearing denominators at the generic point.** For a quasi-coherent `M`, every element `t`
of the stalk of `M` at the generic point of `X` becomes the germ of a section of `M` over `S` after
multiplication by the germ of a function `g` on `V₀` that does not vanish at `z`. -/
theorem exists_mem_primeCompl_smul_eq_germ [IsIntegral X] [IsLocallyNoetherian X] {V₀ : X.Opens}
    (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (M : X.Modules) [M.IsQuasicoherent]
    (t : modStalk M (genericPoint X)) :
    ∃ g : Γ(X, V₀), ∃ y : Γ(M, S),
      g ∈ (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl ∧
        ringGermAt X V₀ (genericPoint X) (hSV (genericPoint_mem S)) g • t
          = germAt M S (genericPoint X) (genericPoint_mem S) y := by
  classical
  obtain ⟨W, hgenW, s, hs⟩ := exists_germ_eq M t
  have hs' : ∀ h : genericPoint X ∈ W, germAt M W (genericPoint X) h s = t := fun _ => hs
  obtain ⟨g, hg, hgenbas, hsubW⟩ := exists_mem_primeCompl_basicOpen_res_le hV₀ hz hdim hSV hzS hgenW
  set gS : Γ(X, S) := X.presheaf.map (homOfLE hSV).op g with hgS
  have hgenS : genericPoint X ∈ S := genericPoint_mem S
  obtain ⟨n, y, hy⟩ := exists_eq_pow_smul_of_isCompact_of_isQuasiSeparated M
    (isCompact_of_le_isAffineOpen hV₀ hSV)
    ((isQuasiSeparated_univ (α := X)).of_subset (Set.subset_univ _)) gS
    (M.presheaf.map (homOfLE hsubW).op s)
  have e1 : germAt M (X.basicOpen gS) (genericPoint X) hgenbas
      (M.presheaf.map (homOfLE hsubW).op s) = t := by
    rw [germAt_map M hsubW hgenbas s]; exact hs' _
  have hgpow : ringGermAt X (X.basicOpen gS) (genericPoint X) hgenbas
      (X.presheaf.map (homOfLE (X.basicOpen_le gS)).op gS ^ n)
      = ringGermAt X S (genericPoint X) hgenS gS ^ n := by
    have h1 : ringGermAt X (X.basicOpen gS) (genericPoint X) hgenbas
        (X.presheaf.map (homOfLE (X.basicOpen_le gS)).op gS ^ n)
        = ringGermAt X (X.basicOpen gS) (genericPoint X) hgenbas
            (X.presheaf.map (homOfLE (X.basicOpen_le gS)).op gS) ^ n := map_pow _ _ _
    rw [h1, ringGermAt_map (X.basicOpen_le gS) hgenbas gS]
  have e2 : germAt M (X.basicOpen gS) (genericPoint X) hgenbas
        ((X.presheaf.map (homOfLE (X.basicOpen_le gS)).op gS) ^ n •
          M.presheaf.map (homOfLE hsubW).op s)
      = ringGermAt X S (genericPoint X) hgenS gS ^ n • t := by
    rw [germAt_smul' M hgenbas _ _, hgpow, e1]
  have e3 : germAt M S (genericPoint X) hgenS y
      = ringGermAt X S (genericPoint X) hgenS gS ^ n • t := by
    have h0 := congrArg (germAt M (X.basicOpen gS) (genericPoint X) hgenbas) hy
    rw [germAt_map M (X.basicOpen_le gS) hgenbas y, e2] at h0
    exact h0
  have hscal : ringGermAt X V₀ (genericPoint X) (hSV hgenS) (g ^ n)
      = ringGermAt X S (genericPoint X) hgenS gS ^ n := by
    rw [← ringGermAt_map hSV hgenS (g ^ n), map_pow]
    exact map_pow _ _ _
  exact ⟨g ^ n, y, Submonoid.pow_mem _ hg n, by rw [hscal, e3]⟩

/-- If the stalk of a quasi-coherent `M` at the generic point is nonzero then some section of
`M` over `S` already has nonzero germ there. -/
theorem exists_section_germ_ne_zero [IsIntegral X] [IsLocallyNoetherian X] {V₀ : X.Opens}
    (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (M : X.Modules) [M.IsQuasicoherent]
    {t : modStalk M (genericPoint X)} (ht : t ≠ 0) :
    ∃ m : Γ(M, S), germAt M S (genericPoint X) (genericPoint_mem S) m ≠ 0 := by
  obtain ⟨g, y, hg, he⟩ :=
    exists_mem_primeCompl_smul_eq_germ hV₀ hz hdim hSV hzS M t
  refine ⟨y, ?_⟩
  rw [← he]
  exact fun h0 => ht ((isUnit_ringGermAt_genericPoint (hSV (genericPoint_mem S))
    (ne_zero_of_mem_primeCompl_primeIdealOf hV₀ hz hg)).smul_eq_zero.mp h0)

/-- Let `X` be integral and locally Noetherian, let `V₀` be an affine open containing a point `z`
whose local ring has dimension at most one, and let `S` be a nonempty open of `V₀` avoiding `z`.
If `M` is quasi-coherent with nonzero stalk at the generic point, then `Γ(M, S)` is not a finite
`Γ(X, V₀)`-module.

For `M = 𝒪_X` this is
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.not_moduleFinite_sections`. -/
theorem not_moduleFinite_sections_of_modStalk_ne_zero [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∃ t : modStalk M (genericPoint X), t ≠ 0) :
    ¬ (letI := moduleOfLE M hSV; Module.Finite Γ(X, V₀) Γ(M, S)) := by
  obtain ⟨t, ht⟩ := hM
  obtain ⟨m, hm⟩ := exists_section_germ_ne_zero hV₀ hz hdim hSV hzS M ht
  exact not_moduleFinite_sections_of_germ_ne_zero hV₀ hz hdim hSV hzS M m hm

/-! ### Comparing two sections with the same germ -/

/-- Two sections of a quasi-coherent `M` over `S` with the same germ at the generic point agree
after multiplication by the restriction of a function `g` on `V₀` that does not vanish at `z`. -/
theorem exists_mem_primeCompl_smul_eq_of_germ_eq [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (M : X.Modules) [M.IsQuasicoherent] (y₁ y₂ : Γ(M, S))
    (h : germAt M S (genericPoint X) (genericPoint_mem S) y₁
      = germAt M S (genericPoint X) (genericPoint_mem S) y₂) :
    ∃ g : Γ(X, V₀), g ∈ (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl ∧
      X.presheaf.map (homOfLE hSV).op g • y₁ = X.presheaf.map (homOfLE hSV).op g • y₂ := by
  classical
  have hgenS : genericPoint X ∈ S := genericPoint_mem S
  obtain ⟨W, hgenW, iU, iV, e⟩ :=
    TopCat.Presheaf.germ_eq (commVal M).presheaf (genericPoint X) hgenS hgenS y₁ y₂ h
  have hWS : W ≤ S := leOfHom iU
  have e' : M.presheaf.map (homOfLE hWS).op y₁ = M.presheaf.map (homOfLE hWS).op y₂ := by
    rw [Subsingleton.elim iU (homOfLE hWS), Subsingleton.elim iV (homOfLE hWS)] at e
    exact e
  obtain ⟨g, hg, -, hsubW⟩ := exists_mem_primeCompl_basicOpen_res_le hV₀ hz hdim hSV hzS hgenW
  set gS : Γ(X, S) := X.presheaf.map (homOfLE hSV).op g with hgS
  have hres : M.presheaf.map (homOfLE (X.basicOpen_le gS)).op y₁
      = M.presheaf.map (homOfLE (X.basicOpen_le gS)).op y₂ := by
    rw [← map_map M hsubW hWS (X.basicOpen_le gS) y₁,
      ← map_map M hsubW hWS (X.basicOpen_le gS) y₂, e']
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_of_res_eq_of_isCompact M
    (isCompact_of_le_isAffineOpen hV₀ hSV) gS rfl (X.basicOpen_le gS) y₁ y₂ hres
  exact ⟨g ^ n, Submonoid.pow_mem _ hg n, by rw [map_pow]; exact hn⟩

/-! ### The stalk at the generic point as a localization of the sections over `S` -/

/-- The `Γ(X, S)`-module structure on the stalk of `M` at a point of `S`, obtained by restricting
scalars along the germ map of the structure sheaf. -/
@[instance_reducible] noncomputable def stalkModule (M : X.Modules) {S : X.Opens} {x : X}
    (hx : x ∈ S) : Module Γ(X, S) (modStalk M x) :=
  Module.compHom _ (TopCat.Presheaf.germ X.sheaf.obj S x hx).hom

/-- The germ map on sections, as a `Γ(X, S)`-linear map into the stalk. -/
noncomputable def germₗ (M : X.Modules) {S : X.Opens} {x : X} (hx : x ∈ S) :
    letI := stalkModule M hx
    Γ(M, S) →ₗ[Γ(X, S)] modStalk M x :=
  let := stalkModule M hx
  { toFun := germAt M S x hx
    map_add' := germAt_add M hx
    map_smul' := germAt_smul' M hx }

/-- The germ map `germₗ M hx` sends a section `m` over `S` to its germ `germAt M S x hx m`. -/
theorem germₗ_apply (M : X.Modules) {S : X.Opens} {x : X} (hx : x ∈ S) (m : Γ(M, S)) :
    letI := stalkModule M hx
    germₗ M hx m = germAt M S x hx m := rfl

/-- A function whose germ at `x` is a unit acts invertibly on the stalk at `x`. -/
theorem isUnit_algebraMap_end_of_isUnit_ringGermAt (M : X.Modules) {S : X.Opens} {x : X}
    (hx : x ∈ S) (a : Γ(X, S)) (ha : IsUnit (ringGermAt X S x hx a)) :
    letI := stalkModule M hx
    IsUnit (algebraMap Γ(X, S) (Module.End Γ(X, S) (modStalk M x)) a) := by
  let := stalkModule M hx
  obtain ⟨v, hv⟩ := ha
  have key : ∀ (c : Γ(X, S)) (t : modStalk M x),
      (↑v⁻¹ : ringStalk X.sheaf x) • (c • t) = c • ((↑v⁻¹ : ringStalk X.sheaf x) • t) := by
    intro c t
    show (↑v⁻¹ : ringStalk X.sheaf x) • (ringGermAt X S x hx c • t)
      = ringGermAt X S x hx c • ((↑v⁻¹ : ringStalk X.sheaf x) • t)
    rw [smul_smul, smul_smul, mul_comm]
  refine ⟨⟨algebraMap Γ(X, S) (Module.End Γ(X, S) (modStalk M x)) a,
    { toFun := fun t ↦ (↑v⁻¹ : ringStalk X.sheaf x) • t
      map_add' := fun t w ↦ smul_add _ _ _
      map_smul' := key }, ?_, ?_⟩, rfl⟩
  · refine LinearMap.ext fun t ↦ ?_
    show ringGermAt X S x hx a • ((↑v⁻¹ : ringStalk X.sheaf x) • t) = t
    rw [← hv, smul_smul, Units.mul_inv, one_smul]
  · refine LinearMap.ext fun t ↦ ?_
    show (↑v⁻¹ : ringStalk X.sheaf x) • (ringGermAt X S x hx a • t) = t
    rw [← hv, smul_smul, Units.inv_mul, one_smul]

/-- **The stalk of `M` at the generic point is the localization of `Γ(M, S)` at `q`.** Here `q`
is the prime of `Γ(X, V₀)` attached to a point `z` of the affine open `V₀` outside `S` whose local
ring has dimension at most one.

This is the module-valued form of
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.isLocalization_functionField_sections`, which
is the case `M = 𝒪_X`: there the stalk at the generic point is the function field. -/
theorem isLocalizedModule_germₗ [IsIntegral X] [IsLocallyNoetherian X] {V₀ : X.Opens}
    (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (M : X.Modules) [M.IsQuasicoherent] :
    letI := resAlgebra hSV
    letI := stalkModule M (genericPoint_mem S)
    IsLocalizedModule
      (Algebra.algebraMapSubmonoid Γ(X, S) (hV₀.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl)
      (germₗ M (genericPoint_mem S)) := by
  let := resAlgebra hSV
  let := stalkModule M (genericPoint_mem S)
  have hgenS : genericPoint X ∈ S := genericPoint_mem S
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, g, hg, rfl⟩
    have hgne := ne_zero_of_mem_primeCompl_primeIdealOf hV₀ hz hg
    have h1 : IsUnit (ringGermAt X S (genericPoint X) hgenS
        (X.presheaf.map (homOfLE hSV).op g)) := by
      rw [ringGermAt_map hSV hgenS g]
      exact isUnit_ringGermAt_genericPoint (hSV hgenS) hgne
    exact isUnit_algebraMap_end_of_isUnit_ringGermAt M hgenS _ h1
  · intro t
    obtain ⟨g, y, hg, he⟩ := exists_mem_primeCompl_smul_eq_germ hV₀ hz hdim hSV hzS M t
    refine ⟨⟨y, ⟨algebraMap Γ(X, V₀) Γ(X, S) g, ⟨g, hg, rfl⟩⟩⟩, ?_⟩
    have h2 : ringGermAt X S (genericPoint X) hgenS (X.presheaf.map (homOfLE hSV).op g) • t
        = germAt M S (genericPoint X) hgenS y := by
      rw [ringGermAt_map hSV hgenS g]; exact he
    exact h2
  · intro y₁ y₂ h
    obtain ⟨g, hg, he⟩ :=
      exists_mem_primeCompl_smul_eq_of_germ_eq hV₀ hz hdim hSV hzS M y₁ y₂ h
    exact ⟨⟨algebraMap Γ(X, V₀) Γ(X, S) g, ⟨g, hg, rfl⟩⟩, he⟩

/-! ### Ascent to non-coherence -/

/-- **A module whose sections over `V₀` surject onto `Γ(M, S)` is not coherent.** Under the
hypotheses of `not_moduleFinite_sections_of_modStalk_ne_zero`, an `𝒪_X`-module `N` admitting a
`Γ(X, V₀)`-linear surjection `Γ(N, V₀) → Γ(M, S)` is not coherent. -/
theorem not_isCoherent_of_sections_surjective [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S : X.Opens} [Nonempty S.toScheme]
    (hSV : S ≤ V₀) (hzS : z ∉ S) (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∃ t : modStalk M (genericPoint X), t ≠ 0) (N : X.Modules)
    (φ : letI := moduleOfLE M hSV; Γ(N, V₀) →ₗ[Γ(X, V₀)] Γ(M, S))
    (hφ : Function.Surjective φ) : ¬ N.IsCoherent := by
  intro hcoh
  let := moduleOfLE M hSV
  have hfin : Module.Finite Γ(X, V₀) Γ(N, V₀) :=
    AlgebraicGeometry.moduleFinite_sections N ⟨V₀, hV₀⟩
  exact not_moduleFinite_sections_of_modStalk_ne_zero hV₀ hz hdim hSV hzS M hM
    (Module.Finite.of_surjective φ hφ)

/-! ### The direct image of a restricted quasi-coherent module -/

/-- The sections over `W` of the direct image along `S → X` of the restriction of `M`, as a module
over `Γ(X, W)`, map to the sections of `M` over `S ⊓ W` with its restriction action. The source
is definitionally `Γ(M, S.ι ''ᵁ (S.ι ⁻¹ᵁ W))`, and the map is restriction of sections of `M` to
`S ⊓ W`. -/
noncomputable def pushforwardRestrictSectionsHom (M : X.Modules) (S W : X.Opens) :
    letI := moduleOfLE M (inf_le_right : S ⊓ W ≤ W)
    Γ((Scheme.Modules.pushforward S.ι).obj (M.restrict S.ι), W) →ₗ[Γ(X, W)] Γ(M, S ⊓ W) :=
  let := moduleOfLE M (inf_le_right : S ⊓ W ≤ W)
  { toFun := fun m =>
      M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op m
    map_add' := fun m n => by
      change M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op (m + n)
        = M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op m
          + M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op n
      exact map_add _ _ _
    map_smul' := fun r m => by
      have hρ : ∀ (c : Γ(X, S.ι ''ᵁ (S.ι ⁻¹ᵁ W))) (x : Γ(M, S.ι ''ᵁ (S.ι ⁻¹ᵁ W))),
          M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op (c • x)
            = X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op c •
              M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op x :=
        fun c x => M.map_smul _ c x
      have hone : X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op
            ((S.ι.appIso (S.ι ⁻¹ᵁ W)).inv ((S.ι.app W) r))
          = X.presheaf.map (homOfLE (inf_le_right : S ⊓ W ≤ W)).op r := by
        rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
        have h2 : (ConcreteCategory.hom (S.ι.app W ≫
            X.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op)) r
              = (X.presheaf.map (homOfLE (inf_le_right : S ⊓ W ≤ W)).op) r := by
          rw [ι_app_comp_mapInfLE]
        exact h2
      exact (hρ _ m).trans (congrArg (fun c =>
        c • M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op m) hone) }

/-- The map `pushforwardRestrictSectionsHom M S W` is surjective. -/
theorem pushforwardRestrictSectionsHom_surjective (M : X.Modules) (S W : X.Opens) :
    Function.Surjective (pushforwardRestrictSectionsHom M S W) := by
  have hid : ∀ f : op (S ⊓ W) ⟶ op (S ⊓ W), M.presheaf.map f = 𝟙 Γ(M, S ⊓ W) := fun f => by
    rw [Subsingleton.elim f (𝟙 (op (S ⊓ W))), M.presheaf.map_id]
  have key : ∀ y : Γ(M, S ⊓ W),
      M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W).symm)).op
        (M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W))).op y) = y := by
    intro y
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp, ← op_comp, hid]
    rfl
  exact fun y =>
    ⟨M.presheaf.map (homOfLE (le_of_eq (ι_image_preimage_eq_inf S W))).op y, key y⟩

/-- **The direct image of a quasi-coherent module from an open subscheme avoiding a
codimension-one point is not coherent.** Let `X` be integral and locally Noetherian, `S` a
nonempty open subscheme, `z` a point outside `S` whose local ring has dimension at most one, and
`M` a quasi-coherent `𝒪_X`-module whose stalk at the generic point is nonzero. Then
`(S → X)_* (M|_S)` is not coherent.

For `M = 𝒪_X` this is `not_isCoherent_pushforward_structureSheaf_of_dim_le_one`, in the same
namespace. It is the first paragraph of [Stacks, Tag 0AWC] for every coherent module on `U = S`
that extends to `X`, in the case where the associated point in question is the generic point of
`X` itself. -/
@[ega "IV 7.8.3" "(ix)"]
theorem not_isCoherent_pushforward_restrict_of_modStalk_ne_zero [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1)
    {S : X.Opens} [Nonempty S.toScheme] (hzS : z ∉ S) (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∃ t : modStalk M (genericPoint X), t ≠ 0) :
    ¬ ((Scheme.Modules.pushforward S.ι).obj (M.restrict S.ι)).IsCoherent := by
  obtain ⟨V₀, hV₀, hz, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := z) trivial
  have hgenS : genericPoint X ∈ S := genericPoint_mem S
  have hgenV₀ : genericPoint X ∈ V₀ :=
    ((genericPoint_spec X).mem_open_set_iff V₀.isOpen).mpr
      (by simpa using (⟨⟨z, hz⟩⟩ : Nonempty V₀.toScheme))
  have : Nonempty (S ⊓ V₀ : X.Opens).toScheme := ⟨⟨genericPoint X, ⟨hgenS, hgenV₀⟩⟩⟩
  exact not_isCoherent_of_sections_surjective hV₀ hz hdim
    (inf_le_right : S ⊓ V₀ ≤ V₀) (fun h => hzS h.1) M hM _
    (pushforwardRestrictSectionsHom M S V₀) (pushforwardRestrictSectionsHom_surjective M S V₀)

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
