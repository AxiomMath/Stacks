module

public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic

/-!
# An invertible module has no torsion along an effective Cartier divisor

Let `X` be a scheme, let `D ⊆ X` be an effective Cartier divisor with ideal sheaf `ℐ_D` and
closed immersion `i : D ⟶ X`, and let `L` be an invertible `𝒪_X`-module. This file proves that
`L` has no `ℐ_D`-torsion, and the consequence that `L` has no sections supported on `D`:

`Hom_{𝒪_X}(i_* G, L) = 0` for **every** `𝒪_D`-module `G`.

In particular, taking `G` to be the normal sheaf `𝒩 = i^* 𝒪_X(D)` and `L = 𝒪_X(D)`, the group
`Hom_{𝒪_X}(i_* 𝒩, 𝒪_X(D))` vanishes.

## Main results

* `Stacks.Divisors.exists_nonZeroDivisor_subschemeι_app_eq_zero`: every point of `X` has an open
  neighbourhood `W` such that over *every* open `V ≤ W` the ideal sheaf contains a section which,
  read in `Γ(X, V)`, is a nonzerodivisor. This is the local equation of the divisor.
* `Stacks.Divisors.eq_zero_of_isInvertible_of_smul_eq_zero`: **an invertible module has no
  `ℐ_D`-torsion.** A section of `L` over `U` all of whose restrictions are annihilated by the
  sections of `ℐ_D` is zero.
* `Stacks.Divisors.hom_pushforward_eq_zero_of_isInvertible`: **an invertible module has no
  sections supported on `D`.** Every morphism `i_* G ⟶ L` of `𝒪_X`-modules is zero, for `G` an
  arbitrary `𝒪_D`-module.
* `Stacks.Divisors.subsingleton_hom_pushforward_of_isInvertible`: the same statement as the
  vanishing of the hom-group.

## Implementation notes

The local equation is produced from invertibility alone, with no appeal to the affine-local
characterisation of an effective Cartier divisor ([Stacks, Tag 01WS],
`Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal`). Invertibility of `ℐ_D` gives, around
every point, a linear equivalence `Γ(ℐ_D, V) ≃ₗ[Γ(X, V)] Γ(X, V)` for every smaller open `V`
(`Stacks.SheafOfModules.Scheme.exists_nonempty_linearEquiv_of_isInvertible`, the converse half of
[Stacks, Tag 0B8M]); the generator it names is a nonzerodivisor because the *inclusion*
`ℐ_D ⟶ 𝒪_X` is injective on sections (`Stacks.Divisors.idealSheafSection_injective`), so a scalar
killing the generator kills a section of the free rank-one module `Γ(ℐ_D, V)`. Tag 01WS would
deliver a nonzerodivisor only on an affine open, and would then have to be transported to the
arbitrary opens `V` on which the trivialisation of `L` is available; this route avoids the
transport entirely, which is why the two trivialising neighbourhoods can simply be intersected.

Both halves of the torsion argument are statements about sections over an *arbitrary* open, not
over an affine one, and that is what makes them compose: `L` is trivialised over every open inside
a neighbourhood of a point, and so is `ℐ_D`, so one intersection of three opens carries all the
data. Vanishing is then propagated from those opens to `U` by
`TopCat.Presheaf.IsSheaf.section_ext`.

The annihilation of `Γ(i_* G, V)` by a section of `𝒪_X` killed by `i^♯` is inlined: the module
structure on `Γ(i_* G, V) = Γ(G, i⁻¹V)` is restriction of scalars along `i^♯` on `V`, so the
statement is `change` followed by `zero_smul`.

## References

* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-! ### The local equation of an effective Cartier divisor -/

/-- **An invertible module mapping injectively and linearly into `𝒪_X` provides local
nonzerodivisors.** If `M` is invertible and `f` is a family of injective `Γ(X, V)`-linear maps
`Γ(M, V) ⟶ Γ(X, V)`, then every point has a neighbourhood `W` over every open subset `V` of which
some section of `M` has nonzerodivisor image. -/
theorem exists_mem_nonZeroDivisors_of_isInvertible (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (f : ∀ V : X.Opens, Γ(M, V) → Γ(X, V))
    (hf : ∀ (V : X.Opens) (c : Γ(X, V)) (y : Γ(M, V)), f V (c • y) = c * f V y)
    (hinj : ∀ V : X.Opens, Function.Injective (f V)) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, V ≤ W →
      ∃ y : Γ(M, V), f V y ∈ nonZeroDivisors Γ(X, V) := by
  obtain ⟨W, hxW, hW⟩ :=
    Stacks.SheafOfModules.Scheme.exists_nonempty_linearEquiv_of_isInvertible X M x
  refine ⟨W, hxW, fun V hVW => ?_⟩
  obtain ⟨e⟩ := hW V hVW
  refine ⟨e.symm 1, ?_⟩
  have hmul : ∀ c : Γ(X, V), f V (e.symm c) = c * f V (e.symm 1) := by
    intro c
    have h := e.symm.map_smul c (1 : Γ(X, V))
    rw [smul_eq_mul, mul_one] at h
    rw [h, hf]
  have key : ∀ c : Γ(X, V), c * f V (e.symm 1) = 0 → c = 0 := by
    intro c hc
    refine e.symm.injective (hinj V ?_)
    rw [hmul c, hmul 0, hc, zero_mul]
  exact mem_nonZeroDivisors_iff.2 ⟨fun c hc => key c (by rw [mul_comm]; exact hc), key⟩

/-- **The local equation of an effective Cartier divisor.** Every point of `X` has an open
neighbourhood `W` such that over every open `V ≤ W` there is a section `g` of `𝒪_X` which is
annihilated by the closed immersion of `D` — that is, a section of the ideal sheaf `ℐ_D` — and
which is a nonzerodivisor in `Γ(X, V)`. -/
theorem exists_nonZeroDivisor_subschemeι_app_eq_zero [IsEffectiveCartierDivisor D] (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ V : X.Opens, V ≤ W →
      ∃ g : Γ(X, V), D.subschemeι.app V g = 0 ∧ g ∈ nonZeroDivisors Γ(X, V) := by
  obtain ⟨W, hxW, hW⟩ := exists_mem_nonZeroDivisors_of_isInvertible (negativeTwist' D)
    (fun _ y => idealSheafSection D y)
    (fun _ c y => idealSheafSection_smulSectionMap D y c)
    (fun _ => idealSheafSection_injective D) x
  refine ⟨W, hxW, fun V hVW => ?_⟩
  obtain ⟨y, hy⟩ := hW V hVW
  exact ⟨idealSheafSection D y, subschemeι_app_idealSheafSection D y, hy⟩

/-! ### An invertible module has no `ℐ_D`-torsion -/

/-- **An invertible module has no `ℐ_D`-torsion.** Let `D` be an effective Cartier divisor on `X`
and `L` an invertible `𝒪_X`-module. A section of `L` over `U` whose restriction to every open
`V ≤ U` is annihilated by every section of `ℐ_D` over `V` is zero. -/
theorem eq_zero_of_isInvertible_of_smul_eq_zero [IsEffectiveCartierDivisor D] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    {U : X.Opens} (t : Γ(L, U))
    (ht : ∀ (V : X.Opens) (hVU : V ≤ U) (g : Γ(X, V)), D.subschemeι.app V g = 0 →
      g • L.presheaf.map (homOfLE hVU).op t = 0) :
    t = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext (F := L.presheaf) L.isSheaf (U := op U) ?_
  intro x hx
  obtain ⟨W₁, hxW₁, h₁⟩ := exists_nonZeroDivisor_subschemeι_app_eq_zero D x
  obtain ⟨W₂, hxW₂, h₂⟩ :=
    Stacks.SheafOfModules.Scheme.exists_nonempty_linearEquiv_of_isInvertible X L x
  refine ⟨U ⊓ (W₁ ⊓ W₂), inf_le_left, ⟨hx, hxW₁, hxW₂⟩, ?_⟩
  obtain ⟨g, hg, hgnzd⟩ := h₁ (U ⊓ (W₁ ⊓ W₂)) (inf_le_right.trans inf_le_left)
  obtain ⟨e⟩ := h₂ (U ⊓ (W₁ ⊓ W₂)) (inf_le_right.trans inf_le_right)
  rw [map_zero]
  refine e.map_eq_zero_iff.1 ((mem_nonZeroDivisors_iff.1 hgnzd).1 _ ?_)
  rw [← smul_eq_mul, ← e.map_smul, ht (U ⊓ (W₁ ⊓ W₂)) inf_le_left g hg, map_zero]

/-! ### An invertible module has no sections supported on `D` -/

/-- **An invertible module has no sections supported on an effective Cartier divisor.** For `D` an
effective Cartier divisor on `X` with closed immersion `i : D ⟶ X`, `G` an arbitrary
`𝒪_D`-module and `L` an invertible `𝒪_X`-module,

`Hom_{𝒪_X}(i_* G, L) = 0`. -/
theorem hom_pushforward_eq_zero_of_isInvertible [IsEffectiveCartierDivisor D]
    {G : D.subscheme.Modules} {L : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (φ : (Scheme.Modules.pushforward D.subschemeι).obj G ⟶ L) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  show φ.app U m = 0
  refine eq_zero_of_isInvertible_of_smul_eq_zero D L (φ.app U m) ?_
  intro V hVU g hg
  have hnat : L.presheaf.map (homOfLE hVU).op (φ.app U m) =
      φ.app V (((Scheme.Modules.pushforward D.subschemeι).obj G).presheaf.map
        (homOfLE hVU).op m) :=
    (PresheafOfModules.naturality_apply φ.val (homOfLE hVU).op m).symm
  have hz : g • (((Scheme.Modules.pushforward D.subschemeι).obj G).presheaf.map
      (homOfLE hVU).op m) = 0 := by
    show (D.subschemeι.app V g) • (show Γ(G, D.subschemeι ⁻¹ᵁ V) from _) = 0
    rw [hg, zero_smul]
  rw [hnat, ← Scheme.Modules.Hom.app_smul, hz, map_zero]

/-- **An invertible module has no sections supported on an effective Cartier divisor**, stated as
the vanishing of the hom-group: there is at most one morphism `i_* G ⟶ L`, namely zero. -/
instance subsingleton_hom_pushforward_of_isInvertible [IsEffectiveCartierDivisor D]
    {G : D.subscheme.Modules} {L : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    Subsingleton ((Scheme.Modules.pushforward D.subschemeι).obj G ⟶ L) :=
  ⟨fun φ ψ => by
    rw [hom_pushforward_eq_zero_of_isInvertible D φ, hom_pushforward_eq_zero_of_isInvertible D ψ]⟩

end Stacks.Divisors

end
