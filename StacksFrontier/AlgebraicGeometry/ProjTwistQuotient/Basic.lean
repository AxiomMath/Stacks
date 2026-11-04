module

public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleEventualGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Assertion (1) of Tag 0B5Q from the ample machine, for a graded ring generated in degree one

[Stacks, Tag 0B5Q] assertion (1) — every coherent module on `Proj 𝒜` is a quotient of a finite
direct sum of twisting sheaves — is recorded in this library as having no mathematics behind
it: `Stacks.AlgebraicGeometry.ProjSerreDevissage.HasTwistQuotients` carries it as a hypothesis,
names it the first of three absences and says of the one statement of its shape,
`Stacks.AmpleGlobalGeneration`
`.IsQuotientOfNegativeTwists`, that it "is for an *ample invertible* module and is itself a `def`,
not a theorem".

**That reading is too pessimistic, and this file shows by how much.** The `def` has two
sorry-free theorems producing it — `Stacks.AmpleEventualGeneration`
`.isQuotientOfNegativeTwists_of_isEventuallyFinGenPowers` and `Stacks.AmpleGlobalGeneration`
`.isQuotientOfNegativeTwists_of_isEventuallyGloballyGenerated`, the latter resting on
`exists_shortExact_biproduct_of_generatingSections` — so it is a predicate with a proof machine
behind it, and the machine is exactly the content of assertion (1). What separates the machine
from the tag's statement is not Serre's theorem; it is the list in "What remains" below, every
item of which is a named statement rather than a theory.

Two things had to be true for the machine to be applicable at all, and both are checked here
rather than assumed:

* **The categories agree.** `(AlgebraicGeometry.Proj 𝒜).Modules` and the tag's
  `SheafOfModules (projRingSheaf 𝒜)` are the same type — `rfl` — so no bridge between a scheme's
  module category and the `Proj` structure-sheaf spelling is needed, and no model
  mismatch of the 08KS/02O5 kind arises.
* **The invertibility classes bridge.** The ample machine asks `Stacks.Ample.IsInvertibleModule`;
  `Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one`
  supplies the other Tag 01CS class, `Stacks.SheafOfModules.IsInvertible`. They are bridged by
  `Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`, in the
  direction needed here, giving `isInvertibleModule_twistingSheaf_of_adjoin_degree_one` below.

## Main results

All names below live in the namespace `Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute`.

* `isInvertibleModule_twistingSheaf_of_adjoin_degree_one`: for `𝒜` generated in degree one over
  `𝒜 0`, every twisting sheaf `𝒪(n)` on `Proj 𝒜` is invertible in the class the ampleness theory
  uses.
* `exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists`: assertion (1)'s conclusion,
  for a quasi-coherent module of finite type, from the ample machine's conclusion for `𝒪(1)` plus
  the identification of the tensor powers of `𝒪(1)` with the twisting sheaves.
* `exists_epi_coproduct_twistingSheaf_of_isCoherent`: the same at the tag's hypothesis, a coherent
  module, by way of `Stacks.AlgebraicGeometry.CoherentTFAE`
  `.isQuasicoherent_isFiniteType_of_isCoherent`.

## What remains, named

Assertion (1) for `𝒜` generated in degree one is, after this file, exactly these:

1. `𝒪(1) ^⊗ n ≅ 𝒪(n)` — the `htw` hypothesis below. This is `IsIso` of
   `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap`, which
   `Stacks.AlgebraicGeometry.ProjInvertibleLocus.isGoodOpen_basicOpen_mul_of_isIso_mul` and
   `Stacks.AlgebraicGeometry.ProjInvertibleLocus.ratioLocus_le_whereInvertible_of_isIso_mul`
   likewise carry as a *hypothesis*. Under degree-one generation both `𝒪(a)` and `𝒪(b)` are
   invertible, by
   `isInvertibleModule_twistingSheaf_of_adjoin_degree_one`, so this is a comparison of invertible
   modules rather than a general tensor computation; it is nevertheless not proved anywhere.
2. `Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers` and `.IsFinGenAfterSomeTwist` for
   `𝒪(1)` on `Proj 𝒜` — the two halves of Tag 01Q3 clause (7). These are the ample machine's own
   hypotheses and nothing instantiates them on `Proj`; this is where the global sections of the
   twists enter, and so where the genuinely projective input lives.

Item 3 of `ProjSerreDevissage`'s list — flatness of the twisting sheaves, "not a theorem at the
tag's hypotheses" — does not arise on this route: it is discharged by
`TwistFlatness.preservesMonomorphisms_twistFunctor_of_adjoin_degree_one` under the same degree-one
hypothesis this file assumes throughout.

## Why this is not Tag 0B5Q, and not a renaming

The tag assumes `𝒜` merely Noetherian, with no degree-one generation, and that is not a
hypothesis any statement here can drop: for `𝒜` not generated in degree one `𝒪(1)` is genuinely
not invertible, so `Stacks.Ample.tensorPowModule` cannot even be formed. The passage from
Noetherian to degree-one generated is the Veronese reduction that [Stacks, Tag 0B5Q]'s own proof
makes, through [Stacks, Tag 0B5J]; its geometric half is proved
(`Stacks.Veronese.veroneseProjIso` and `Stacks.Veronese.veroneseTwistingSheafIso`, two of the
components of the tag's single carrier `Stacks.Veronese.tag0B5J`) and its algebraic input —
that `𝒜 ^(d)` is generated in degree one for suitably divisible `d` — is absent from both trees
and from pinned Mathlib.

No `stacks` attribute is attached. Every statement below carries the degree-one generation
hypothesis, which the tag does not grant, so there is no covering set for the label
`finite_twist_surjection`; and the two items above are hypotheses, not theorems.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u w

namespace Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Tag 0B5Q's module category is the ample machine's module category**, definitionally.

Tag 0B5Q's statement is over `SheafOfModules (projRingSheaf 𝒜)`, where `projRingSheaf` is the
composite of the `Proj` structure sheaf with `forget₂ CommRingCat RingCat`; the ampleness
development is over `X.Modules` for a scheme `X`. For `X = Proj 𝒜` these are the same type, so
nothing needs transporting between them. Recorded as a lemma because a model mismatch of this
kind can block an argument, and here there is none. -/
theorem modules_eq_sheafOfModules_projRingSheaf :
    (AlgebraicGeometry.Proj 𝒜).Modules = SheafOfModules.{u} (projRingSheaf 𝒜) :=
  rfl

/-- **Every twisting sheaf on `Proj 𝒜` is invertible in the ampleness theory's class**, when `𝒜`
is generated in degree one over `𝒜 0`.

`TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one` proves invertibility in the Tag
01CS class `Stacks.SheafOfModules.IsInvertible`; the ampleness development's
`Stacks.Ample.IsInvertibleModule` is the other realisation of that tag, and instance search does
not cross between them. The crossing is
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. -/
@[ega "II 2.6.1", ega "II 3.2.5" "special case"]
theorem isInvertibleModule_twistingSheaf_of_adjoin_degree_one
    (hgen : Algebra.adjoin (𝒜 0) (Set.range fun f : 𝒜 1 => (f : S)) = ⊤) (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 n) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      (AlgebraicGeometry.Proj 𝒜).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒜))
      (twistingSheaf 𝒜 n)).mp
    (Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_twistingSheaf_of_adjoin_degree_one
      𝒜 hgen n)

section AmpleRoute

variable [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)]

/-- **[Stacks, Tag 0B5Q] assertion (1)'s conclusion from the ample machine.** Given

* `htw`, the identification of the tensor powers of `𝒪(1)` with the twisting sheaves, and
* `hamp`, the ample machine's conclusion `Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists`
  for `𝒪(1)`,

every quasi-coherent `𝒪_{Proj 𝒜}`-module of finite type is the target of an epimorphism from a
finite coproduct of twisting sheaves — which is the tag's conclusion verbatim.

The proof is bookkeeping, and the two steps worth naming are both about the direct sum. The
machine delivers its summands as a `Bicone` with `IsBilimit`, deliberately, so that no
`HasBiproduct` instance term appears in its conclusion; the tag asks for `∐`. The two are
identified by `IsColimit.coconePointUniqueUpToIso` against `colimit.isColimit`, which is where the
ambient coproduct instance is introduced — once, at the point of use, rather than inside a
reusable statement. The re-indexing of the summands along `htw` is then
`HasColimit.isoOfNatIso (Discrete.natIso …)`. -/
theorem exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists
    (htw : ∀ n : ℤ,
      Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n ≅
        twistingSheaf 𝒜 n)
    (hamp : Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists
      (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1))
    (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    (hqc : F.IsQuasicoherent) (hft : SheafOfModules.IsFiniteType.{u, u, u} F) :
    ∃ (r : ℕ) (d : Fin r → ℤ),
      ∃ φ : (∐ fun j : Fin r => twistingSheaf 𝒜 (d j)) ⟶ F, Epi φ := by
  obtain ⟨T, r, d, b, hb, e, hse, hX₃, _, _⟩ := hamp 0 F hqc hft
  subst hX₃
  -- The machine's bicone of tensor powers, compared with the ambient coproduct.
  have hbc : b.pt ≅
      ∐ fun j : Fin r =>
        Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) (-(d j)) :=
    hb.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)
  -- Re-index the summands along `htw`.
  have hre : (∐ fun j : Fin r =>
        Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) (-(d j))) ≅
      ∐ fun j : Fin r => twistingSheaf 𝒜 (-(d j)) :=
    HasColimit.isoOfNatIso (Discrete.natIso fun j => htw (-(d j.as)))
  -- One iso from the tag's coproduct to the machine's middle term.
  obtain ⟨ι⟩ : Nonempty ((∐ fun j : Fin r => twistingSheaf 𝒜 (-(d j))) ≅ T.X₂) :=
    ⟨hre.symm.trans (hbc.symm.trans e.symm)⟩
  have hιiso : IsIso ι.hom := ι.isIso_hom
  have hιepi : Epi ι.hom := IsIso.epi_of_iso ι.hom
  exact ⟨r, fun j => -(d j), ι.hom ≫ T.g, epi_comp' hιepi hse.epi_g⟩

/-- **[Stacks, Tag 0B5Q] assertion (1)'s conclusion at the tag's hypothesis.** The same as
`exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists`, with the module coherent
rather than quasi-coherent of finite type; a coherent module is both, by
`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent`.

The coherence predicate here is `Stacks.SheafOfModules.IsCoherent`; the tag's is the root
`SheafOfModules.IsCoherent`, and the two are interchangeable by
`AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent`, which elaborates to a
reflexive `Iff`. -/
theorem exists_epi_coproduct_twistingSheaf_of_isCoherent
    (htw : ∀ n : ℤ,
      Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n ≅
        twistingSheaf 𝒜 n)
    (hamp : Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists
      (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1))
    (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ (r : ℕ) (d : Fin r → ℤ),
      ∃ φ : (∐ fun j : Fin r => twistingSheaf 𝒜 (d j)) ⟶ F, Epi φ := by
  have hF' : Stacks.SheafOfModules.IsCoherent F :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent.mp hF
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  exact exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists 𝒜 htw hamp F hqc hft

end AmpleRoute

end Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute

end
