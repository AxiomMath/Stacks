module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSignTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRelocalization

/-!
# The twist of a quasi-coherent module by a locally free rank one abelian sheaf

Let `X` be an algebraic space over a scheme `S`, let `L` be an abelian sheaf on the spaces-étale
site of `X` which is locally free of rank one, and let `ℱ` be a quasi-coherent `𝒪_X`-module on
the ringed spaces-étale site.  Then `ℱ ⊗_ℤ L` is again quasi-coherent.

This is [Stacks, Tag 072A] read on the spaces-étale site itself.  The tag is proved for modules
on the *small* étale site of a quotient, as
`AlgebraicGeometry.Space.SignTwistSetup.isQuasicoherentOnSite_twist`, where the twist arrives
by the comparison of [Stacks, Tag 03G1]; the alternating Čech development of
[Stacks, Tag 0728] works on the spaces-étale site throughout, and this is the same statement
there, with the comparison functor replaced by the identity.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isQuasicoherentOnSite_tensorAbelianModule`:
  **[Stacks, Tag 072A] on the spaces-étale site** — the tensor product of a quasi-coherent
  module with a locally free rank one abelian sheaf is quasi-coherent.

## Implementation notes

The proof is the source's: quasi-coherence may be checked locally
(`Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_iso`), the trivializing covering of the
final object pulls back to a covering of any object, and on a member of it a generating integral
section of `L` identifies `ℱ ⊗_ℤ L` with `ℱ`
(`Stacks.SheafOfModules.nonempty_over_iso_of_tensor_generator`).  Both of those and
`Stacks.SheafOfModules.exists_generator_on_over` are stated for an arbitrary cocontinuous
functor of sites; here that functor is the identity.

## References

* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **[Stacks, Tag 072A] on the spaces-étale site.**  If `ℱ` is a quasi-coherent `𝒪_X`-module
on the ringed spaces-étale site of `X` and `L` is an abelian sheaf which is locally free of rank
one, then `ℱ ⊗_ℤ L` is quasi-coherent. -/
theorem isQuasicoherentOnSite_tensorAbelianModule
    (L : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hL : IsLocallyFreeOfRankOne B S hS X L)
    (M : SheafOfModules.{u + 1}
      (ringSheaf (spacesEtaleRingedSite B S hS X).O))
    (hM : M.IsQuasicoherentOnSite) :
    (Stacks.SheafOfModules.tensorAbelianModule M L.obj).IsQuasicoherentOnSite := by
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_of_locally_iso (M := M) hM fun V => ?_
  obtain ⟨E, hE, he⟩ := hL
  have hcover : E.sieve₀ ∈ (topology B S hS X) (final B S hS X) :=
    Precoverage.generate_mem_toGrothendieck (J := precoverage B S hS X) ⟨E, rfl, hE⟩
  let q := (final_isTerminal B S hS X).from V
  let T := E.sieve₀.pullback q
  refine ⟨{a : Over V // T.arrows a.hom}, fun a => a.1.left, fun a => a.1.hom, ?_, ?_⟩
  · have hEq : Sieve.ofArrows (fun a : {a : Over V // T.arrows a.hom} => a.1.left)
        (fun a => a.1.hom) = T := by
      refine le_antisymm (fun Z g hg => ?_) fun Z g hg => ?_
      · rw [Sieve.mem_ofArrows_iff] at hg
        obtain ⟨a, b, rfl⟩ := hg
        exact T.downward_closed a.2 b
      · exact Sieve.ofArrows_mk (fun a : {a : Over V // T.arrows a.hom} => a.1.left)
          (fun a => a.1.hom) ⟨Over.mk g, hg⟩
    rw [hEq]
    exact (topology B S hS X).pullback_stable q hcover
  · rintro ⟨a, ha⟩
    have ha' : Sieve.ofArrows E.X E.f (a.hom ≫ q) := ha
    rw [Sieve.mem_ofArrows_iff] at ha'
    obtain ⟨i, b, _⟩ := ha'
    obtain ⟨s, hs⟩ := Stacks.SheafOfModules.exists_generator_on_over
      (topology B S hS X) (topology B S hS X) (𝟭 (SpacesEtale B S hS X))
      L a.left (E.X i) b (he i).some
    exact Stacks.SheafOfModules.nonempty_over_iso_of_tensor_generator M
      (Stacks.SheafOfModules.tensorAbelianModule M L.obj) L.obj
      (Stacks.SheafOfModules.toTensorAbelianModule M L.obj)
      (Stacks.SheafOfModules.toTensorAbelianModule_mem M L.obj)
      (Stacks.SheafOfModules.toTensorAbelianModule_smul_tmul M L.obj) a.left s hs

end AlgebraicGeometry.Space.SpacesEtale

end
