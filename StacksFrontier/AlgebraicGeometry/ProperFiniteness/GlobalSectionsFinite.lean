module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Devissage
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree-zero case of [Stacks, Tag 02O6] for the structure sheaf

`AlgebraicGeometry.FiniteGlobalSectionsOfProper` names the assertion that for a Noetherian ring
`A` and a proper morphism `g : V ⟶ Spec A` the ring map `Γ(Spec A, ⊤) ⟶ Γ(V, ⊤)` is finite. This
file proves it, from the two conclusions of [Stacks, Tag 02O5] and [Stacks, Tag 02O6] that
`StacksFrontier/AlgebraicGeometry/ProperCoherenceWitness/ChowStalk.lean` establishes with no
hypothesis.

The route is the direct-image half of [Stacks, Tag 02O5]: `V` is Noetherian, being proper over a
Noetherian affine base, so its structure sheaf is coherent ([Stacks, Tag 01XZ]), hence
`g_* 𝒪_V` is a coherent `𝒪_{Spec A}`-module, and [Stacks, Tag 01PB] makes the sections of a
coherent module over an affine open a finite module over the sections of the structure sheaf
there. Over `⊤` those sections are `Γ(V, ⊤)` with scalars restricted along `g.appTop`, the
preimage of `⊤` being `⊤`, which is `Γ(Spec A, ⊤) ⟶ Γ(V, ⊤)` being finite.

## Main results

* `AlgebraicGeometry.finiteGlobalSectionsOfProper`:
  `AlgebraicGeometry.FiniteGlobalSectionsOfProper` holds.

## Implementation notes

No tag attribute is attached here. The statement is the degree-zero case of [Stacks, Tag 02O6]
for one module, so it is a corollary of a tag rather than a tag, and [Stacks, Tag 02O6] itself is
registered on `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`.

Finiteness of the sections is read off [Stacks, Tag 01PB] rather than off
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` at degree zero, which would
need the degree-zero value of the right derived functor of global sections to be identified with
global sections themselves. The two inputs are the same theorem — `moduleFinite_cohomology` is
proved from the witness sheaves that also give the coherence of `g_* 𝒪_V` used here — and the
coherence route needs no comparison of indexings.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **The degree-zero case of [Stacks, Tag 02O6] for the structure sheaf holds.** For a
Noetherian ring `A` and a proper morphism `g : V ⟶ Spec A`, the ring map
`Γ(Spec A, ⊤) ⟶ Γ(V, ⊤)` is finite.

`V` is Noetherian, being proper over a Noetherian affine base, so its structure sheaf is
coherent; the direct image `g_* 𝒪_V` is then coherent by [Stacks, Tag 02O5], and
[Stacks, Tag 01PB] makes its sections over `⊤` a finite `Γ(Spec A, ⊤)`-module. Those sections
are `Γ(V, ⊤)` with scalars restricted along `g.appTop`. -/
theorem finiteGlobalSectionsOfProper : FiniteGlobalSectionsOfProper.{u} := by
  intro A _ hA V g hg
  have : IsNoetherianRing A := hA
  have : IsProper g := hg
  have : IsNoetherian V := ProperCoherentImage.isNoetherian_of_isProper_of_isAffine g
  have : IsLocallyNoetherian V := inferInstance
  have hcoh :
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit V.ringCatSheaf)).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward g (SheafOfModules.unit V.ringCatSheaf)
  have hqc :
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit V.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hft :
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit V.ringCatSheaf)).IsFiniteType :=
    SheafOfModules.IsCoherent.isFiniteType
  exact Stacks.AlgebraicGeometry.CoherentFinite.finite_sections
    ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit V.ringCatSheaf))
    (isAffineOpen_top (Spec (.of A)))

end AlgebraicGeometry

end
