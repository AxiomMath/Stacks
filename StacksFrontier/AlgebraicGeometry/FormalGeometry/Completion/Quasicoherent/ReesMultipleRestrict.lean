module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.SubmoduleRestrict.Basic

/-!
# `ℐⁿℱ` restricted to an open subscheme is `(ℐ𝒪_U)ⁿ(ℱ|_U)`

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, `ℱ` a quasi-coherent
`𝒪_X`-module and `U` an open of `X`. Restricting the subsheaf
`ℐⁿℱ = Stacks.Blowup.reesMultiple` to `U` as a *concrete* submodule, by
`Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo`, gives the subsheaf `(ℐ𝒪_U)ⁿ(ℱ|_U)` of
`ℱ|_U` built from the inverse image ideal sheaf on `U`. This file proves that, in every integer
degree.

Since `Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules'` is a definitional
equality, the consequence `Stacks.Blowup.reesMultiple_restrictFunctor_eq` is that the restriction
to `U` of the sheaf of modules `ℐⁿℱ` **is** the `n`-th piece of
`Stacks.Blowup.reesGradedModule` for the inverse image ideal on `U`. That is what carries the
finiteness of [Stacks, Tag 02O8], which is proved on an affine chart of the base, to the graded
module `Stacks.Blowup.pushforwardReesGradedModulePlus` on the base.

## Main results

* `Stacks.Blowup.reesMultiple_comap_ι`: **the restriction identity**, an equality of concrete
  submodules of `ℱ|_U`.
* `Stacks.Blowup.reesMultiple_restrictFunctor_eq`: the same, read as an equality of
  `𝒪_U`-modules.

## Implementation notes

**No ideal is computed here.** The affine-local comparison of the two ideal-power multiples is
already in the tree as `Stacks.Algebraization.mem_idealPowerMultiple_restrict_affine_iff`, which
says that over an affine open `W` of `U` membership in `(ℐ𝒪_U)ⁿ(ℱ|_U)` is membership of the same
section in `ℐⁿℱ` over the image open; that is where
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion` and the comparison of
the two rings of sections are discharged. This file only has to spread that affine statement to
arbitrary opens, in both directions, and to cross from
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`'s model of `ℐⁿℱ` to
`Stacks.Blowup.reesMultiple`'s, which is
`Stacks.Blowup.reesMultiple_natCast_eq_idealPowerMultiple`.

Spreading is possible because membership in a subsheaf is local
(`Stacks.Blowup.mem_submodule_of_cover`) and because the affine opens of `U` are a basis of its
topology. The affine opens are produced on the side of `U` and transported forward, never pulled
back: a point of `U.ι ''ᵁ W` is the image of a point of `W`, and an affine open of `U` containing
that point has an affine image (`AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`).
Pulling an affine open of `X` back to `U` would need it to be affine there, a further argument
that is not used.

Negative degrees are disposed of first: `Stacks.Blowup.reesMultiple_eq_bot_of_neg` makes both
sides the zero subsheaf, and `Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_bot` says the
restriction of the zero subsheaf is the zero subsheaf.

## References

* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SubmoduleRestrict

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.SubmoduleRestrict

/-- The restriction of the zero subsheaf along an open immersion is the zero subsheaf. -/
public theorem restrictTo_bot {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {F : X.Modules} : restrictTo f (⊥ : F.Submodule) = ⊥ := by
  refine le_antisymm (fun V x hx => ?_) bot_le
  have h : x ∈ (⊥ : F.Submodule).obj (op (f ''ᵁ V.unop)) := hx
  exact (SheafOfModules.Submodule.bot_obj (F.restrict f) V).ge
    ((SheafOfModules.Submodule.bot_obj F (op (f ''ᵁ V.unop))).le h)

end Stacks.AlgebraicGeometry.SubmoduleRestrict

namespace Stacks.Blowup

variable {X : Scheme.{u}} (K : X.IdealSheafData) (U : X.Opens) (F : X.Modules)

/-- An affine open of `U` inside a given open and containing a given point of it. The affine
opens of a scheme are a basis of its topology. -/
private theorem exists_affine_image_mem (W : U.toScheme.Opens) (y : U.toScheme)
    (hy : y ∈ W) : ∃ W₀ : U.toScheme.affineOpens, y ∈ W₀.1 ∧ W₀.1 ≤ W := by
  obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hyW₀, hW₀W⟩ :=
    U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open hy W.2
  exact ⟨⟨W₀, hW₀⟩, hyW₀, hW₀W⟩

/-- **The restriction identity.** The subsheaf `ℐⁿℱ` of `ℱ`, restricted to an open `U` as a
concrete submodule, is the subsheaf `(ℐ𝒪_U)ⁿ(ℱ|_U)` of `ℱ|_U`.

Both inclusions spread `Stacks.Algebraization.mem_idealPowerMultiple_restrict_affine_iff` from
the affine opens of `U` to all opens, membership in a subsheaf being local. -/
public theorem reesMultiple_comap_ι [F.IsQuasicoherent] (n : ℤ) :
    reesMultiple (K.comap U.ι) n (F.restrict U.ι) =
      restrictTo U.ι (reesMultiple K n F) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [reesMultiple_eq_bot_of_neg (K.comap U.ι) n (F.restrict U.ι) hn,
      reesMultiple_eq_bot_of_neg K n F hn, restrictTo_bot]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [reesMultiple_natCast_eq_idealPowerMultiple (K.comap U.ι) m (F.restrict U.ι),
    reesMultiple_natCast_eq_idealPowerMultiple K m F]
  refine le_antisymm (fun W s hs => ?_) (fun W s hs => ?_)
  · change s ∈ (Stacks.Algebraization.idealPowerMultiple K m F).toSubmodule.obj
      (op (U.ι ''ᵁ W.unop))
    refine mem_submodule_of_cover _ (U.ι ''ᵁ W.unop) s ?_
    rintro x ⟨y, hyW, rfl⟩
    obtain ⟨W₀, hyW₀, hW₀W⟩ := exists_affine_image_mem U W.unop y hyW
    refine ⟨U.ι ''ᵁ W₀.1, U.ι.image_mono hW₀W, ⟨y, hyW₀, rfl⟩, ?_⟩
    exact (Stacks.Algebraization.mem_idealPowerMultiple_restrict_affine_iff U.ι K m F W₀ _).1
      ((Stacks.Algebraization.idealPowerMultiple (K.comap U.ι) m
        (F.restrict U.ι)).toSubmodule.map_mem (homOfLE hW₀W).op hs)
  · have hs' : s ∈ (Stacks.Algebraization.idealPowerMultiple K m F).toSubmodule.obj
        (op (U.ι ''ᵁ W.unop)) := hs
    refine mem_submodule_of_cover _ W.unop s ?_
    intro y hyW
    obtain ⟨W₀, hyW₀, hW₀W⟩ := exists_affine_image_mem U W.unop y hyW
    refine ⟨W₀.1, hW₀W, hyW₀, ?_⟩
    exact (Stacks.Algebraization.mem_idealPowerMultiple_restrict_affine_iff U.ι K m F W₀ _).2
      ((Stacks.Algebraization.idealPowerMultiple K m F).toSubmodule.map_mem
        (homOfLE (U.ι.image_mono hW₀W)).op hs')

/-- **The restriction identity, as an equality of `𝒪_U`-modules.** The `n`-th piece of
`Stacks.Blowup.reesGradedModule` for the inverse image ideal sheaf on `U` is the restriction to
`U` of the sheaf of modules `ℐⁿℱ`. -/
public theorem reesMultiple_restrictFunctor_eq [F.IsQuasicoherent] (n : ℤ) :
    ((reesMultiple (K.comap U.ι) n (F.restrict U.ι)).toSheafOfModules :
        U.toScheme.Modules) =
      (Scheme.Modules.restrictFunctor U.ι).obj
        ((reesMultiple K n F).toSheafOfModules : X.Modules) :=
  (congrArg (fun N : (F.restrict U.ι).Submodule => N.toSheafOfModules)
      (reesMultiple_comap_ι K U F n)).trans
    (restrictTo_toSheafOfModules' U.ι (reesMultiple K n F))

end Stacks.Blowup

end
