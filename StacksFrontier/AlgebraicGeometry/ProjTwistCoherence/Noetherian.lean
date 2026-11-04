module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.AlgebraicGeometry.ProjTwistCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A twist of a coherent sheaf on `Proj` of a Noetherian graded ring is coherent

Let `S` be a Noetherian graded ring, `X = Proj S` and `ℱ` a coherent `𝒪_X`-module. Then `ℱ(q)` is
coherent for every integer `q`, with **no hypothesis of generation in degree one**.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistSheafOfModules_of_isNoetherianRing`:
  `ℱ` coherent implies `ℱ(q)` coherent, for `Proj` of a Noetherian graded ring.

## Implementation notes

**This is not the same theorem as
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistSheafOfModules`**, and neither implies
the other. That one assumes `Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤` and *no* Noetherian
hypothesis: there `𝒪(q)` is invertible, and the tensor product of a coherent sheaf with an
invertible one is coherent without any finiteness of the base. This one assumes
`[IsNoetherianRing S]` and no generation hypothesis: here `𝒪(q)` need not be invertible, and the
input is instead that it is *coherent* — which it is, being the sheaf associated with the finite
graded module `S(q)` — together with the closure of coherence under tensor products,
[Stacks, Tag 01CE] clause (6). The two hypothesis sets are incomparable.

Coherence of `𝒪(q)` itself is *not* taken from
`AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistingSheaf`, which routes through
invertibility and so needs generation in degree one. It is assembled instead from the
finite-type side of [Stacks, Tag 01XZ]: a Noetherian graded ring is of finite type over its
degree-zero part (`Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing`), whence `𝒪(q)`
is of finite type (`AlgebraicGeometry.ProjectiveSpectrum.Proj.isFiniteType_twistingSheaf`); it is
quasi-coherent for free, and `Proj` of a Noetherian graded ring is a Noetherian scheme
([Stacks, Tag 0B5Q]), so quasi-coherent of finite type is coherent. No generation hypothesis
enters at any step.

The tensor application is written with `@` and positional instance arguments because
`structureSheafRing` is `instance_reducible` rather than `reducible`, so instance search does not
cross it to find the two coherence hypotheses.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

/-- **The twisting sheaves on `Proj` of a Noetherian graded ring are coherent**, with no
hypothesis of generation in degree one. On a Noetherian scheme a quasi-coherent module of finite
type is coherent, and `𝒪(q)` is of finite type because `S` is of finite type over `S₀`. -/
@[ega "III 2.3.4" "partial"]
public theorem isCoherent_twistingSheaf_of_isNoetherianRing {S : Type u} {σ : Type w}
    [CommRing S] [IsNoetherianRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ)
    [GradedRing 𝒮] (q : ℤ) :
    _root_.SheafOfModules.IsCoherent (twistingSheaf 𝒮 q) :=
  have : Algebra.FiniteType (𝒮 0) S :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒮
  have hqc : SheafOfModules.IsQuasicoherent.{u, u, u} (twistingSheaf 𝒮 q) := inferInstance
  let F : (AlgebraicGeometry.Proj 𝒮).Modules := twistingSheaf 𝒮 q
  let _ : F.IsQuasicoherent := hqc
  have : SheafOfModules.IsFiniteType.{u, u, u} F := isFiniteType_twistingSheaf 𝒮 q
  Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent'_of_isQuasicoherent_of_isFiniteType
    (X := AlgebraicGeometry.Proj 𝒮) F

/-- **A twist of a coherent sheaf on `Proj` of a Noetherian graded ring is coherent.** The
twisting sheaf `𝒪(q)` is coherent by `isCoherent_twistingSheaf_of_isNoetherianRing`, and the
tensor product of two coherent sheaves of modules is coherent. -/
public theorem isCoherent_twistSheafOfModules_of_isNoetherianRing {S : Type u} {σ : Type w}
    [CommRing S] [IsNoetherianRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ)
    [GradedRing 𝒮] (F : (AlgebraicGeometry.Proj 𝒮).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (q : ℤ) :
    _root_.SheafOfModules.IsCoherent (twistSheafOfModules 𝒮 F q) :=
  @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace F (twistingSheaf 𝒮 q) hF
    (isCoherent_twistingSheaf_of_isNoetherianRing 𝒮 q)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end
