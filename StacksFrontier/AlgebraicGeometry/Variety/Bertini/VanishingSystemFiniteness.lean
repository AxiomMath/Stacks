module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingFamilyDivisorsOnX

/-!
# The finiteness hypotheses of the Bertini linear system, discharged from properness

The Bertini statements built on the linear system `V_n` of [Stacks, Tag 0FD5] carry three
finiteness hypotheses as assumed instances: `Γ(X, ℒ ^⊗ n)` is finite dimensional over `k`, so is
`V_n`, and `Γ(Z, ℒ ^⊗ n|_Z)` is a finite `k`-module. All three are Serre finiteness in degree
zero — `AlgebraicGeometry.finiteDimensional_globalSectionsOverField`, which this repository provides
as an instance for a coherent module on a scheme proper over a field — and none of them is
discharged by it directly, because the Bertini files write global sections with
`Stacks.Bertini.globalSections` and that instance is stated for
`AlgebraicGeometry.globalSectionsOverField`.

The two definitions have the same underlying abelian group and differ only in the ring map the
scalars are restricted along: `(Scheme.ΓSpecIso _).inv ≫ f.appTop` for the first and
`(Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ ⊤ _` for the second. Those two morphisms are equal —
`Stacks.AffineAlgebraEquivalence.appLE_top_top` — though not definitionally, which is why the
`Module k` instances are distinct and why that instance does not apply directly. Rewriting along
that equality
identifies the two `ModuleCat k` objects outright, and the existing instance transports.

## Main results

* `Stacks.Bertini.globalSections_eq_globalSectionsOverField` and
  `Stacks.Bertini.finrank_globalSections_eq`: the identification of the two spellings, as an
  equality of `k`-modules and as an equality of their dimensions. The second is what carries a
  dimension computation performed in one spelling over to the other.
* `Stacks.Bertini.finiteDimensional_globalSections`: **Serre finiteness in degree zero in the
  Bertini spelling** — the global sections of a coherent module on a scheme proper over a field
  are a finite-dimensional `k`-vector space. `FiniteDimensional k (V_n)` follows from this with no
  further work, `V_n` being a `k`-submodule of `Γ(X, ℒ ^⊗ n)`.
* `Stacks.SectionsVanishingOnSubscheme.finiteDimensional_globalSections_tensorPowModule`: the same
  for `ℒ ^⊗ n` with `ℒ` invertible, where the coherence side condition is supplied rather than
  assumed.
* `Stacks.SectionsVanishingOnSubscheme.moduleFinite_subschemeSections`: `Γ(Z, ℒ ^⊗ n|_Z)` is a
  finite `k`-module, for `Z` the closed subscheme cut out by any quasi-coherent sheaf of ideals.

## Implementation notes

**The coherence of `ℒ ^⊗ n` is derived, not assumed.** An invertible module on a locally
Noetherian scheme is coherent, which is
`AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible` ([Stacks, Tag 01XZ]), and `X` is
locally Noetherian because `f` is proper, hence locally of finite type. The invertibility that
instance wants is written with the ring sheaf as `X.sheaf.obj` and `X.ringCatSheaf.property`,
where `Stacks.Ample.IsInvertibleModule` writes `X.presheaf` and
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf`; the two spellings are interchangeable at
an argument position, so the instance is passed as an explicit term, which is what
`Stacks.SectionsVanishingOnSubscheme.ambientFamilyDivisors` does for its own `isInvertible`
field.

**`Γ(Z, ℒ ^⊗ n|_Z)` needs the properness of the composite, not of `f` alone.** The closed
immersion `Z ⟶ X` is proper, so `Z ⟶ Spec k` is; and the pullback of a coherent module along a
morphism with locally Noetherian source is coherent ([Stacks, Tag 0EBF],
`AlgebraicGeometry.isCoherent_pullback`), the source `Z` being a closed subscheme of the locally
Noetherian `X`.

No `@[stacks]` attribute is attached. What is proved here is the degree-zero case of
[Stacks, Tag 02O6] read in a second spelling of the space of global sections; the tag is already
registered against `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` and its
over-a-field consequence against
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`, and nothing here is a new
mathematical assertion.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample

universe u

namespace Stacks.Bertini

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The two spellings of the space of global sections over the base field are the same
`k`-module.** `Stacks.Bertini.globalSections` restricts scalars along
`(Scheme.ΓSpecIso _).inv ≫ f.appTop` and `AlgebraicGeometry.globalSectionsOverField` along
`(Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ ⊤ _`; those two morphisms agree by
`Stacks.AffineAlgebraEquivalence.appLE_top_top`, so the two restrictions of scalars are the same
functor and the two objects are equal, not merely isomorphic. -/
theorem globalSections_eq_globalSectionsOverField (F : X.Modules) :
    globalSections k f F = AlgebraicGeometry.globalSectionsOverField k f F := by
  unfold globalSections AlgebraicGeometry.globalSectionsOverField
  congr 1
  rw [Stacks.AffineAlgebraEquivalence.appLE_top_top]
  rfl

/-- The dimensions the two spellings measure agree, by
`Stacks.Bertini.globalSections_eq_globalSectionsOverField`. This is what carries a dimension
computation performed in one spelling over to the other; the two carry different `Module k`
instances on one underlying abelian group, so the equality of objects has to be turned into a
linear equivalence before `Module.finrank` can be rewritten under it. -/
theorem finrank_globalSections_eq (F : X.Modules) :
    Module.finrank k (globalSections k f F) =
      Module.finrank k (AlgebraicGeometry.globalSectionsOverField k f F) :=
  (eqToIso (globalSections_eq_globalSectionsOverField k f F)).toLinearEquiv.finrank_eq

/-- **The global sections of a coherent module on a scheme proper over a field are a
finite-dimensional vector space**, in the spelling `Stacks.Bertini.globalSections` that the
Bertini linear systems use.

This is `AlgebraicGeometry.finiteDimensional_globalSectionsOverField` transported along
`Stacks.Bertini.globalSections_eq_globalSectionsOverField`. -/
instance finiteDimensional_globalSections [IsProper f] (F : X.Modules) [F.IsCoherent] :
    FiniteDimensional k (globalSections k f F) := by
  rw [globalSections_eq_globalSectionsOverField k f F]
  infer_instance

end Stacks.Bertini

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (I : X.IdealSheafData) {L : X.Modules} [IsInvertibleModule X L] (n : ℤ)

/-- **`Γ(X, ℒ ^⊗ n)` is finite dimensional over `k`** for `ℒ` invertible and `X` proper over `k`.
The coherence of `ℒ ^⊗ n` is [Stacks, Tag 01XZ] on the locally Noetherian `X`, properness giving
both. -/
instance finiteDimensional_globalSections_tensorPowModule [IsProper f] :
    FiniteDimensional k (Stacks.Bertini.globalSections k f (tensorPowModule X L n)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L n) := (inferInstance : IsInvertibleModule X (tensorPowModule X L n))
  infer_instance

/-- **`Γ(Z, ℒ ^⊗ n|_Z)` is a finite `k`-module**, for `Z` the closed subscheme cut out by `I` and
`X` proper over `k`. This is the space of linear conditions that `V_n` is cut out by, and the
hypothesis the Bertini statements carry about it.

The composite `Z ⟶ X ⟶ Spec k` is proper, the closed immersion being so, and the restriction
`ℒ ^⊗ n|_Z` is coherent by [Stacks, Tag 0EBF]. -/
instance moduleFinite_subschemeSections [IsProper f] :
    Module.Finite k (subschemeSections k f I (L := L) n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (tensorPowModule X L n) := (inferInstance : IsInvertibleModule X (tensorPowModule X L n))
  have : IsLocallyNoetherian I.subscheme := isLocallyNoetherian_of_isClosedImmersion I.subschemeι
  have : ((Scheme.Modules.pullback I.subschemeι).obj (tensorPowModule X L n)).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback I.subschemeι (tensorPowModule X L n)
  exact Stacks.Bertini.finiteDimensional_globalSections k (I.subschemeι ≫ f) _

end Stacks.SectionsVanishingOnSubscheme

end
