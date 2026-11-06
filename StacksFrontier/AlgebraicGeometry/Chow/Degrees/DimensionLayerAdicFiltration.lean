module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTelescope
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Graded
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ideal-adic filtration of a coherent module in a dimension layer

Let `(S, δ)` be a base situation with a dimension function, let `X` be a scheme locally of finite
type over `S` — hence locally Noetherian, but not Noetherian — and let `k ∈ ℤ`. Let `F` be a
coherent `𝒪_X`-module whose support has delta-dimension at most `k` and is contained in a closed
set `Z`, and write `J` for the ideal sheaf of the reduced induced structure on `Z`.

On a *Noetherian* scheme [Stacks, Tag 01Y9] gives one exponent `N` with `J^N · F = 0`, so the
ideal-adic filtration `F ⊇ J·F ⊇ J²·F ⊇ …` is finite and the class of `F` in
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` is the sum of the classes of its graded pieces. Over a scheme
that is merely locally of finite type over the base no such `N` exists; what survives is that
each *quasi-compact* open carries one, which says exactly that the supports of the terms form a
**locally finite** family. That is enough: the direct sum `⨁_{p ≥ 0} J^p · F` is then coherent
and the telescope of
`Stacks.Chow.of_eq_natCoproduct_cokernel_of_filtration` applies.

The conclusion is `Stacks.Chow.of_eq_natCoproduct_adicGraded`:

`[F] = [⨁_{p ≥ 0} J^p·F / J^{p+1}·F]` in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`,

with no Noetherian hypothesis on `X`. Every graded piece is annihilated by `J`, so this reduces
the remaining content of Tag 02S9 — that the class of `F` is the class of the direct sum of
structure sheaves prescribed by its cycle — to modules annihilated by the ideal sheaf of the
support, which is the shape [Stacks, Tag 01YE] consumes.

## Main results

* `Stacks.Chow.exists_forall_notMem_supp_idealPowSmul` — **[Stacks, Tag 01Y9] on one affine
  open**: for a coherent module supported inside `Z` and an affine open `U`, some power of the
  ideal sheaf of `Z` already annihilates the sections over `U`, so `J^p·F` has empty support
  inside `U` for all large `p`.
* `Stacks.Chow.locallyFinite_supp_idealPowSmul` — hence the supports of the terms of the
  ideal-adic filtration form a locally finite family.
* `Stacks.Chow.of_eq_natCoproduct_adicGraded` — **the class of `F` is the class of the direct sum
  of the graded pieces of its ideal-adic filtration**, for `X` locally of finite type over the
  base.

## Implementation notes

The exponent on an affine open is taken from
`Stacks.AlgebraicGeometry.IdealPowerSmul.exists_pow_mul_le_annihilator_of_isLocallyNoetherian`,
which needs only local Noetherianity of `X`: its proof reads the Noetherian ring off the single
affine open it works on, and quasi-compactness enters only in the companion statement that turns
finitely many exponents into one. It is applied with both of its two closed sets equal to `Z`,
which produces a power of `J · J` and hence the power `J^{t + t}` wanted.

A point of an affine open on which the sections of a quasi-coherent submodule vanish is outside
its support, which is
`Stacks.AlgebraicGeometry.IdealPowerSmul.notMem_supp_of_smul_eq_zero` applied with the scalar
`1`: the hypothesis that the scalar lies outside the prime of the point is then the properness of
that prime.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.IdealPowerSmul
open Stacks.AlgebraicGeometry.IrreducibleDevissage (idealPowStep mono_idealPowStep
  isIso_idealPowSmulHom_zero)

universe u

namespace Stacks.Chow

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The ideal-adic filtration dies on every affine open -/

/-- **[Stacks, Tag 01Y9] on one affine open.** For a coherent `𝒪_X`-module `F` on a locally
Noetherian scheme whose support is contained in a closed set `Z`, and an affine open `U`, there is
an exponent `t` beyond which `J^p · F` has no support inside `U`, where `J` is the ideal sheaf of
`Z`: a power of `J(U)` annihilates the sections of `F` over `U`, because the support of those
sections lies in the zero locus of `J(U)` and `J(U)` is finitely generated. -/
@[ega "I 9.3.4" "special case"]
theorem exists_forall_notMem_supp_idealPowSmul [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsCoherent] (Z : Closeds X)
    (hZ : SheafOfModules.supp F ⊆ (Z : Set X)) (U : X.affineOpens) :
    ∃ t : ℕ, ∀ p, t ≤ p → ∀ x ∈ U.1,
      x ∉ SheafOfModules.supp (idealPowSmul (closedIdeal Z) p F).toSheafOfModules := by
  obtain ⟨t, ht⟩ := exists_pow_mul_le_annihilator_of_isLocallyNoetherian F Z Z (by simpa using hZ) U
  refine ⟨t + t, fun p hp x hx hmem ↦ ?_⟩
  have hann : (closedIdeal Z).ideal U ^ p ≤ Module.annihilator Γ(X, U.1) Γ(F, U.1) := by
    refine le_trans (Ideal.pow_le_pow_right hp) (le_trans (le_of_eq ?_) ht)
    rw [mul_pow, ← pow_add]
  have hbot : (closedIdeal Z).ideal U ^ p • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) = ⊥ := by
    rw [← Submodule.le_annihilator_iff]
    rwa [Submodule.annihilator_top]
  refine notMem_supp_of_smul_eq_zero F (idealPowSmul (closedIdeal Z) p F)
    (isQuasicoherent_idealPowSmul _ p F) U x hx 1 ?_ ?_ hmem
  · exact fun h ↦ (U.2.primeIdealOf ⟨x, hx⟩).2.ne_top ((Ideal.eq_top_iff_one _).2 h)
  · intro m hm
    rw [obj_idealPowSmul (closedIdeal Z) p F U, hbot] at hm
    rw [Submodule.mem_bot] at hm
    rw [hm, smul_zero]

/-- **The supports of the terms of the ideal-adic filtration form a locally finite family.** Every
point has an affine neighbourhood on which some power of the ideal sheaf already annihilates the
module, and beyond that exponent the terms miss the neighbourhood altogether. -/
theorem locallyFinite_supp_idealPowSmul [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsCoherent] (Z : Closeds X)
    (hZ : SheafOfModules.supp F ⊆ (Z : Set X)) :
    LocallyFinite fun p : ULift.{u} ℕ ↦
      SheafOfModules.supp (idealPowSmul (closedIdeal Z) p.down F).toSheafOfModules := by
  intro x
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨t, ht⟩ := exists_forall_notMem_supp_idealPowSmul F Z hZ ⟨V, hV⟩
  refine ⟨(V : Set X), V.2.mem_nhds hxV, ?_⟩
  refine Set.Finite.subset (Set.Finite.preimage (Set.injOn_of_injective fun _ _ h ↦ ULift.ext h)
    (Set.finite_Iio t)) ?_
  rintro p ⟨y, hy, hyU⟩
  by_contra hlt
  exact ht p.down (not_lt.1 hlt) y hyU hy

/-! ### The class of the direct sum of the graded pieces -/

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- **The class of a coherent module is the class of the direct sum of the graded pieces of its
ideal-adic filtration**, on a scheme locally of finite type over the base and with no Noetherian
hypothesis. Let `F` be coherent with support of delta-dimension at most `k` contained in a closed
set `Z`, and let `J` be the ideal sheaf of `Z`. Then in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))`

`[F] = [⨁_{p ≥ 0} J^p·F / J^{p+1}·F]`.

The filtration `F ⊇ J·F ⊇ …` is locally finite because on every affine open a power of `J`
annihilates `F`, so the telescope of
`Stacks.Chow.of_eq_natCoproduct_cokernel_of_filtration` applies to it. -/
theorem of_eq_natCoproduct_adicGraded (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent]
    (Z : Closeds X) (hZ : SheafOfModules.supp F ⊆ (Z : Set X))
    (G H : CoherentModulesDimLE C f k) (hG : G.obj.obj = F)
    (hH : H.obj.obj =
      natCoproduct fun p ↦ cokernel (idealPowStep (closedIdeal Z) F p)) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj G) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj H) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdimF : ∀ x ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction f x ≤ k := by
    intro x hx
    exact relativeDimension_le_of_mem_supp_dimLE C f k G x (hG ▸ hx)
  have hsub : ∀ p, SheafOfModules.supp
      (idealPowSmulModule (closedIdeal Z) p F) ⊆ SheafOfModules.supp F := fun p ↦
    @supp_subset_of_mono X _ _ (idealPowSmulHom (closedIdeal Z) p F)
      (inferInstanceAs (Mono (idealPowSmul (closedIdeal Z) p F).ι))
  have hcA : ∀ p, (idealPowSmulModule (closedIdeal Z) p F).IsCoherent := fun p ↦
    isCoherent_idealPowSmul (closedIdeal Z) p F
  have hdimA : ∀ p, ∀ x ∈ SheafOfModules.supp (idealPowSmulModule (closedIdeal Z) p F),
      relativeDimension C.dimensionFunction f x ≤ k := fun p x hx ↦ hdimF x (hsub p hx)
  have hLF : LocallyFinite fun p : ULift.{u} ℕ ↦
      SheafOfModules.supp (idealPowSmulModule (closedIdeal Z) p.down F) :=
    locallyFinite_supp_idealPowSmul F Z hZ
  have h := of_eq_natCoproduct_cokernel_of_filtration C f k
    (fun p ↦ idealPowSmulModule (closedIdeal Z) p F)
    (fun p ↦ idealPowStep (closedIdeal Z) F p)
    (fun p ↦ mono_idealPowStep (closedIdeal Z) F p) hcA hLF hdimA
    (dimLEObj C f k _ (hcA 0) (hdimA 0)) H rfl hH
  refine Eq.trans ?_ h
  refine (of_eq_of_module_iso C f k (dimLEObj C f k _ (hcA 0) (hdimA 0)) G ?_).symm
  exact (@asIso _ _ _ _ (idealPowSmulHom (closedIdeal Z) 0 F)
    (isIso_idealPowSmulHom_zero (closedIdeal Z) F)) ≪≫ eqToIso hG.symm

end Stacks.Chow

end
