module

public import Mathlib.LinearAlgebra.Quotient.Pi
public import StacksFrontier.Algebra.Module.StablyFree
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreFreeStalk
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicSystemsOnComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic

/-!
# Finite free stalks of the completion of a finite locally free module

Let `S` be an algebraization situation, `U = Spec A ∖ V(a)` its open subscheme, `ℐ = I 𝒪_U` the
ideal sheaf `Stacks.Algebraization.idealOnOpen S` and `𝒢` a coherent `𝒪_U`-module. The `m`-th
term of the completion `Stacks.Algebraization.completionFunctor` of `𝒢` along `ℐ` is the
quotient `𝒢 / ℐ ᵐ⁺¹ 𝒢`, a module over the `m`-th infinitesimal neighbourhood of the closed
subscheme cut out by `ℐ`. This file computes its stalks when `𝒢` is finite locally free: at every
point `y` of `U` the stalk of `𝒢 / ℐ ᵐ⁺¹ 𝒢` is a finite free module over
`𝒪_{U,y} / ℐ_y ᵐ⁺¹`.

The argument is the stalkwise one. Finite local freeness gives a linear equivalence
`𝒢_y ≃ₗ (𝒪_{U,y})ʳ` for some `r`, because the stalk of a finite locally free module is free of
finite rank. The stalk functor on modules over a scheme is exact, so it carries the quotient
`𝒢 / ℐ ᵐ⁺¹ 𝒢` to `𝒢_y / ℐ_y ᵐ⁺¹ 𝒢_y`; this is
`Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv`. Finally, dividing a finite product
of copies of a ring by an ideal multiple of the whole module is the same as dividing each
factor, which is `Submodule.quotientPi` together with the description of `J • ⊤` inside `ιᵣ → R`
as the submodule of tuples with all coordinates in `J` (`Module.ideal_smul_top_pi`).

This is the shape of hypothesis that the principal short exact sequences of
`Stacks.Coherent.IsCoherentAdicSystem.shortExact_principalShortComplex` consume, and the reason
it is stated with an existential rank rather than a basis: only the existence of some finite free
presentation of the stalk is ever used.

## Main results

* `Stacks.FreeStalkQuotient.exists_linearEquiv_pi` — a finite free module over a commutative
  ring is linearly equivalent to `Fin r → R` for some `r`.
* `Stacks.FreeStalkQuotient.quotientSmulTopPiEquiv` — the quotient of `ι → R` by `J • ⊤` is
  `ι → R ⧸ J`, for a finite index type `ι`.
* `Stacks.FreeStalkQuotient.quotientSmulTopEquivOfFreeEquiv` — the same read through a linear
  equivalence `M ≃ₗ[R] (ι → R)`: the quotient `M / J M` is `ι → R ⧸ J`.
* `Stacks.Algebraization.hasFiniteFreeStalks_completionFunctor_of_isFiniteLocallyFree` — the
  stalks of the terms of the completion of a finite locally free coherent module are finite free
  over the infinitesimal neighbourhoods.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u v w t

namespace Stacks.FreeStalkQuotient

/-- **A finite free module is a finite product of copies of the ring.** Choosing a basis of a
free module which is moreover finite gives a finite index type, and reindexing it by
`Fin (Fintype.card _)` turns the representation into a linear equivalence with `Fin r → R`. -/
theorem exists_linearEquiv_pi (R : Type v) [CommRing R] (M : Type w) [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] :
    ∃ r : ℕ, Nonempty (M ≃ₗ[R] (Fin r → R)) := by
  classical
  exact ⟨Fintype.card (Module.Free.ChooseBasisIndex R M),
    ⟨((Module.Free.chooseBasis R M).reindex (Fintype.equivFin _)).equivFun⟩⟩

/-- **Dividing a finite product of copies of a ring by an ideal multiple.** The submodule
`J • ⊤` of `ι → R` consists of the tuples all of whose coordinates lie in `J`, so the quotient
is the product of the quotients `R ⧸ J`. -/
def quotientSmulTopPiEquiv {R : Type v} [CommRing R] {ι : Type t} [Fintype ι] [DecidableEq ι]
    (J : Ideal R) :
    ((ι → R) ⧸ (J • (⊤ : Submodule R (ι → R)))) ≃ₗ[R] (ι → R ⧸ J) :=
  (Submodule.quotEquivOfEq _ _ (Module.ideal_smul_top_pi J)).trans
    (Submodule.quotientPi fun _ : ι => (J : Submodule R R))

/-- **Dividing a finite free module by an ideal multiple.** A linear equivalence
`e : M ≃ₗ[R] (ι → R)` carries `J • ⊤` to `J • ⊤`, so it descends to an identification of
`M / J M` with the product of the quotients `R ⧸ J`. -/
def quotientSmulTopEquivOfFreeEquiv {R : Type v} [CommRing R] {M : Type w} [AddCommGroup M]
    [Module R M] {ι : Type t} [Fintype ι] [DecidableEq ι] (e : M ≃ₗ[R] (ι → R)) (J : Ideal R) :
    (M ⧸ (J • (⊤ : Submodule R M))) ≃ₗ[R] (ι → R ⧸ J) :=
  (Submodule.Quotient.equiv _ _ e
      (by rw [Submodule.map_smul'', Submodule.map_top, e.range])).trans
    (quotientSmulTopPiEquiv J)

end Stacks.FreeStalkQuotient

namespace Stacks.Algebraization

/-- **The completion of a finite locally free coherent module has finite free stalks over the
infinitesimal neighbourhoods.** Let `S` be an algebraization situation with open subscheme `U`
and ideal sheaf `ℐ = I 𝒪_U`, and let `𝒢` be a coherent `𝒪_U`-module which is finite locally
free. Then for every `m` and every point `y` of `U` the stalk at `y` of the `m`-th term
`𝒢 / ℐ ᵐ⁺¹ 𝒢` of the completion of `𝒢` is a finite free `𝒪_{U,y} / ℐ_y ᵐ⁺¹`-module.

The stalk `𝒢_y` is free of finite rank over `𝒪_{U,y}`, so it is `(𝒪_{U,y})ʳ` for some `r`; the
stalk of the quotient is the quotient of the stalks by
`Stacks.Algebraization.idealPowerQuotientStalkLinearEquiv`; and the quotient of `(𝒪_{U,y})ʳ` by
`ℐ_y ᵐ⁺¹` acting on all of it is `(𝒪_{U,y} / ℐ_y ᵐ⁺¹)ʳ`. -/
theorem hasFiniteFreeStalks_completionFunctor_of_isFiniteLocallyFree
    (S : AlgebraizationSituation.{u})
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules S.U.toScheme.ringCatSheaf)
    (hG : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj)
    (m : ℕ) (y : S.U.toScheme) :
    ∃ r : ℕ, Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
        (((completionFunctor S.U.toScheme (idealOnOpen S)).obj G).obj.obj (Opposite.op m))
      ≃ₗ[S.U.toScheme.presheaf.stalk y]
      (Fin r → (S.U.toScheme.presheaf.stalk y ⧸
        AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y ^ (m + 1)))) := by
  classical
  have : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G.obj :=
    (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff G.obj).mp hG
  obtain ⟨hfree, hfin⟩ : Module.Free (S.U.toScheme.presheaf.stalk y)
        ((modulesStalkFunctor S.U.toScheme y).obj G.obj) ∧
      Module.Finite (S.U.toScheme.presheaf.stalk y)
        ((modulesStalkFunctor S.U.toScheme y).obj G.obj) :=
    Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree G.obj y
  obtain ⟨r, ⟨e⟩⟩ := Stacks.FreeStalkQuotient.exists_linearEquiv_pi
    (S.U.toScheme.presheaf.stalk y) ((modulesStalkFunctor S.U.toScheme y).obj G.obj)
  refine ⟨r, ⟨?_⟩⟩
  rw [completionFunctor_obj]
  exact (idealPowerQuotientStalkLinearEquiv (idealOnOpen S) (m + 1) G.obj y).symm.trans
    (Stacks.FreeStalkQuotient.quotientSmulTopEquivOfFreeEquiv e
      (AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y ^ (m + 1)))

end Stacks.Algebraization

end
