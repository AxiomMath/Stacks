module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.TangentSpace.BijectiveDifferential
public import StacksFrontier.Deformation.VersalObject.MinimalVersalOrbitBijection

/-!
# The orbit condition of Stacks 06T6 holds when the differential is bijective

Stacks 06T6 is the assertion that the differential `dξ : Der_Λ(R, k) → T𝓕` of a formal object
is bijective on `Der_Λ(k, k)`-orbits, recorded as a condition on the formal object by
`Deformation.HasBijectiveDifferentialOnDerivationOrbits`. This file establishes it for a formal
object whose differential is bijective in the ordinary sense, Stacks 06IM: bijectivity on orbits
is a consequence of bijectivity, since the orbits on the source are the fibres of `D ↦ D + δ ∘ q`
and the equivariance of the differential matches them with the orbits on the target.

Three of the four clauses of 06T6 need nothing: well-definedness and equivariance hold for every
formal object of a predeformation category, and one direction of the orbit comparison holds as
well. Surjectivity of the differential on tangent vectors is the surjectivity half of 06IM, and
the remaining direction of the orbit comparison — two derivations whose tangent vectors differ by
`δ` differ by `δ ∘ q` — is where injectivity enters: equivariance produces a derivation
`E' = D + δ ∘ q` with the same tangent vector as `E`, and injectivity identifies `E` with it.

For the minimal versal formal object of a predeformation category satisfying (S2) the condition
holds without any bijectivity hypothesis; that is Stacks 06T8,
`Deformation.minimalVersal_hasBijectiveDifferentialOnDerivationOrbits`, which is registered under
this tag as well. The two together are the two hypotheses under which Theorem 06IX asserts 06T6:
part (1) of that theorem asks for a minimal versal formal object satisfying 06IM, and part (2) for
one satisfying 06T6, so the result below is also the implication (1) ⟹ (2) of 06IX, which the
source obtains through (3).

## Main results

* `Deformation.hasBijectiveDifferentialOnDerivationOrbits_of_hasBijectiveDifferential`:
  **Stacks 06T6** for a formal object with bijective differential.

## References

* [Stacks Project, Tag 06T6](https://stacks.math.columbia.edu/tag/06T6)
* [Stacks Project, Tag 06IM](https://stacks.math.columbia.edu/tag/06IM)
* [Stacks Project, Tag 06T8](https://stacks.math.columbia.edu/tag/06T8)
* [Stacks Project, Tag 06IX](https://stacks.math.columbia.edu/tag/06IX)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]

/-- **Stacks Project, Tag 06T6.** The condition holds for a formal object whose differential is
bijective: the differential of such an object is a well-defined, equivariant and surjective map
from derivations of its underlying complete local algebra to the tangent space, and it is
bijective on `Der_Λ(k, k)`-orbits. -/
@[stacks 06T6 "the condition holds for a formal object with bijective differential"]
public theorem hasBijectiveDifferentialOnDerivationOrbits_of_hasBijectiveDifferential
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (ξ : FormalObject p)
    (hbij : HasBijectiveDifferential hp.cofibered ξ) :
    HasBijectiveDifferentialOnDerivationOrbits.{u, v, w} p hp ξ := by
  let : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  obtain ⟨P, hP⟩ := hbij
  refine ⟨existsUnique_derivationDifferentialGraph hp ξ, ?_,
    exists_derivationDifferentialGraph_action.{u, v, w} hp ξ,
    fun D E y z hy hz => ⟨?_, eq_action_of_eq_add.{u, v, w} hp ξ D E y z hy hz⟩⟩
  · intro y
    obtain ⟨d, hd⟩ := hP.2 y
    exact ⟨standardToDerivation ξ d, hd ▸ derivationToTangent_graph hp ξ P d⟩
  · rintro ⟨δ, hδ⟩
    obtain ⟨E', hE', hgraph⟩ :=
      exists_derivationDifferentialGraph_action.{u, v, w} hp ξ D δ y hy
    have hzE : z = derivationToTangent.{u, v, w} hp.cofibered ξ P (derivationToStandard ξ E) :=
      derivationDifferentialGraph_eq_derivationToTangent hp ξ P E z hz
    have hzE' : z = derivationToTangent.{u, v, w} hp.cofibered ξ P (derivationToStandard ξ E') :=
      derivationDifferentialGraph_eq_derivationToTangent hp ξ P E' z (hδ ▸ hgraph)
    have heq : derivationToStandard ξ E = derivationToStandard ξ E' := hP.1 (hzE.symm.trans hzE')
    refine ⟨δ, fun r => ?_⟩
    rw [← hE' r, ← derivationToStandard_apply ξ E r, heq, derivationToStandard_apply]

end Deformation

end
