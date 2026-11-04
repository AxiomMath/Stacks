module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of a finite locally free sheaf is additive in a short exact sequence

A finite locally free sheaf of rank `r` on a scheme has, at every point, a stalk which is free
of rank `r` over the local ring. Since the stalk functor is exact, a short exact sequence of
finite locally free sheaves of constant ranks `r₁, r₂, r₃` gives a short exact sequence of free
modules at every point of the scheme, and rank additivity for free modules gives
`r₂ = r₁ + r₃`.

## Main results

* `AlgebraicGeometry.SheafOfModules.nonempty_stalkLinearEquiv_fin`: the stalk of a finite
  locally free sheaf of rank `r` is isomorphic to the free module of rank `r` over the local
  ring.
* `AlgebraicGeometry.SheafOfModules.free_stalk_of_isFiniteLocallyFreeOfRank` and
  `AlgebraicGeometry.SheafOfModules.rank_stalk_of_isFiniteLocallyFreeOfRank`: freeness and the
  value of the rank of that stalk.
* `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact`: additivity of the constant rank
  along a short exact sequence, on a nonempty scheme.

## Implementation notes

The ranks are natural numbers given as separate arguments, as
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` takes them; the conclusion is
their additivity as natural numbers, obtained from the additivity of `Module.rank` as
cardinals. One point of the scheme suffices, which is why the statement needs the scheme to be
nonempty and takes the point as an argument rather than quantifying over it.

The stalk is spelled `Stacks.SheafOfModules.FlatShortExact.abStalk`, with its canonical module
structure `Stacks.SheafOfModules.FlatShortExact.stalkModule` over the local ring, because that
is the spelling in which stalkwise short exactness is available
(`Stacks.SheafOfModules.FlatShortExact.stalkShortExact`). It is definitionally the stalk of the
underlying presheaf of abelian groups, which is the spelling of the trivialisation results of
`Stacks.StalkFreeBridge`, so the two are interchanged by `change`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.FlatShortExact

namespace AlgebraicGeometry.SheafOfModules

universe u

variable {X : Scheme.{u}}

/-- The stalk of a finite locally free sheaf of rank `r` is isomorphic to the free module
`Fin r →₀ 𝒪_{X,x}` of rank `r` over the local ring. -/
public theorem nonempty_stalkLinearEquiv_fin (F : X.Modules) (r : ℕ)
    [hF : IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : X) :
    letI := stalkModule (X := X.toRingedSpace) F x
    Nonempty (abStalk (X := X.toRingedSpace) F x ≃ₗ[X.presheaf.stalk x]
      (Fin r →₀ X.presheaf.stalk x)) := by
  let := stalkModule (X := X.toRingedSpace) F x
  obtain ⟨q, hq, hr⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  have := hq
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff (X : Type u) q.X).mp q.coversTop).exists_mem x
  obtain ⟨e⟩ := Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv_of_isLocallyFreeData F q i hi
  exact ⟨e.trans (Finsupp.domLCongr (hr i).some)⟩

/-- The stalk of a finite locally free sheaf is free over the local ring. -/
public theorem free_stalk_of_isFiniteLocallyFreeOfRank (F : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : X) :
    letI := stalkModule (X := X.toRingedSpace) F x
    Module.Free (X.presheaf.stalk x) (abStalk (X := X.toRingedSpace) F x) := by
  let := stalkModule (X := X.toRingedSpace) F x
  exact Module.Free.of_equiv (nonempty_stalkLinearEquiv_fin F r x).some.symm

/-- The rank over the local ring of the stalk of a finite locally free sheaf of rank `r`
is `r`. -/
public theorem rank_stalk_of_isFiniteLocallyFreeOfRank (F : X.Modules) (r : ℕ)
    [IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : X) :
    letI := stalkModule (X := X.toRingedSpace) F x
    Module.rank (X.presheaf.stalk x) (abStalk (X := X.toRingedSpace) F x) = r := by
  let := stalkModule (X := X.toRingedSpace) F x
  rw [(nonempty_stalkLinearEquiv_fin F r x).some.rank_eq]
  simp

/-- **Additivity of the constant rank along a short exact sequence.** If
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` is a short exact sequence of finite locally free sheaves of constant
ranks `r₁`, `r₂`, `r₃` on a scheme with a point `x`, then `r₂ = r₁ + r₃`. -/
@[sga "6 I 6.0" "(ii), special case"]
public theorem rank_add_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (r₁ r₂ r₃ : ℕ)
    [IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ r₂]
    [IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₃] (x : X) :
    r₂ = r₁ + r₃ := by
  let R := X.presheaf.stalk x
  let := stalkModule (X := X.toRingedSpace) S.X₁ x
  let := stalkModule (X := X.toRingedSpace) S.X₂ x
  let := stalkModule (X := X.toRingedSpace) S.X₃ x
  have := free_stalk_of_isFiniteLocallyFreeOfRank S.X₁ r₁ x
  have := free_stalk_of_isFiniteLocallyFreeOfRank S.X₂ r₂ x
  have := free_stalk_of_isFiniteLocallyFreeOfRank S.X₃ r₃ x
  have : StrongRankCondition R := commRing_strongRankCondition R
  obtain ⟨f, g, hf, hfg, hg⟩ := stalkShortExact (X := X.toRingedSpace) S hS x
  let T : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (by
      ext m
      exact congrFun hfg.comp_eq_zero m)
  have : Mono T.f := (ModuleCat.mono_iff_injective _).2 hf
  have : Epi T.g := (ModuleCat.epi_iff_surjective _).2 hg
  have hT : T.ShortExact := ShortComplex.ShortExact.mk
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).2 hfg)
  have he := ModuleCat.free_shortExact_rank_add hT
  change Module.rank R (abStalk (X := X.toRingedSpace) S.X₂ x) =
    Module.rank R (abStalk (X := X.toRingedSpace) S.X₁ x) +
      Module.rank R (abStalk (X := X.toRingedSpace) S.X₃ x) at he
  rw [rank_stalk_of_isFiniteLocallyFreeOfRank S.X₁ r₁ x,
    rank_stalk_of_isFiniteLocallyFreeOfRank S.X₂ r₂ x,
    rank_stalk_of_isFiniteLocallyFreeOfRank S.X₃ r₃ x] at he
  exact_mod_cast he

end AlgebraicGeometry.SheafOfModules

end
