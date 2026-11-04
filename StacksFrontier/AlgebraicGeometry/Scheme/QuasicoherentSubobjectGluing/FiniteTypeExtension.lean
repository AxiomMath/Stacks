module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenExtension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a finite type quasi-coherent module across a quasi-compact open

Let `X` be a quasi-compact and quasi-separated scheme and `U ⊆ X` a quasi-compact open. A
quasi-coherent `𝒪_U`-module of finite type is the restriction of a quasi-coherent `𝒪_X`-module of
finite type. Unlike [Stacks, Tag 01PF], the module on `U` is *not* given as a submodule of the
restriction of something on `X`: it is an abstract module, and the ambient module to apply 01PF
inside is produced first.

That ambient module is the one [Stacks, Tag 01PE] supplies,
`AlgebraicGeometry.exists_quasicoherent_restrict_iso`: the direct image `H = j_*G` along the
inclusion is quasi-coherent and satisfies `H|_U ≅ G`. The isomorphism `H|_U ≅ G` presents `G` as
the subobject `Subobject.mk e.inv` of `H|_U`, which is quasi-coherent and of finite type because
`G` is, so `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension` — 01PF — extends
it to a quasi-coherent subobject of `H` of finite type whose restriction to `U` is that subobject,
hence isomorphic to `G`.

On a locally Noetherian scheme finite type and quasi-coherent together are coherence
(`AlgebraicGeometry.isCoherent_of_isQuasicoherent_of_isFiniteType`), which turns the same
statement into the extension of a coherent module across a quasi-compact open.

## Main results

* `AlgebraicGeometry.exists_isFiniteType_quasicoherent_restrict_iso`: a finite type
  quasi-coherent module on a quasi-compact open of a quasi-compact quasi-separated scheme extends
  to a finite type quasi-coherent module on the whole scheme.
* `AlgebraicGeometry.exists_isCoherent_restrict_iso`: the same for a coherent module on a locally
  Noetherian scheme.
* `AlgebraicGeometry.exists_isCoherent_module_finite_sections_restrict_iso`: over an affine
  Noetherian base, the same with the finiteness of the extension recorded as finiteness of its
  global sections as a module over the base ring.

## Implementation notes

**No `@[stacks 0G41]` or `@[stacks 0BK0]` attribute is attached, and none may be.** The first
result above is the finite *type* assertion of [Stacks, Tag 0G41]; the companion assertion of that
tag, for a module of finite *presentation*, is not available here, since it rests on the extension
lemma [Stacks, Tag 0G40] (Properties of Schemes, Lemma 28.23.4) rather than on 01PF. The second
result is the extension assertion of [Stacks, Tag 0BK0], one of four assertions of that tag; the
other three concern the comparison of the cohomology of an open with local cohomology and are
discussed in the module docstring of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.SectionsFiniteness`.

The hypotheses are quasi-compactness and quasi-separatedness of `X` as a topological space and
quasi-compactness of `U` as a set; the quasi-compactness of the *morphism* `U.ι` that 01PE needs is
derived from them, exactly as in the proof of 01PF, through retrocompactness of `U`.

## References

* [Stacks Project, Tag 0G41](https://stacks.math.columbia.edu/tag/0G41)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The finite type assertion of [Stacks, Tag 0G41].** Let `X` be a quasi-compact and
quasi-separated scheme and `U ⊆ X` a quasi-compact open. Every quasi-coherent `𝒪_U`-module of
finite type is isomorphic to the restriction to `U` of a quasi-coherent `𝒪_X`-module of finite
type.

[Stacks, Tag 01PE] extends `G` to a quasi-coherent module `H` on `X` with `H|_U ≅ G`; that
isomorphism makes `G` a quasi-coherent subobject of `H|_U` of finite type, and [Stacks, Tag 01PF]
extends that subobject to a finite type quasi-coherent subobject of `H` restricting to it. -/
@[ega "I 9.4.5" "special case", ega "I 9.4.8" "more general"]
theorem exists_isFiniteType_quasicoherent_restrict_iso {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (G : U.toScheme.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ F : X.Modules, F.IsQuasicoherent ∧ F.IsFiniteType ∧
      Nonempty (F.restrict U.ι ≅ G) := by
  have hQC : QuasiCompact U.ι := quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hU.isRetrocompact U.2))
  obtain ⟨H, _, ⟨e⟩⟩ := exists_quasicoherent_restrict_iso U.ι G
  have hGiso : ((Subobject.mk e.inv : Subobject (H.restrict U.ι)) : U.toScheme.Modules) ≅ G :=
    Subobject.underlyingIso e.inv
  have : ((Subobject.mk e.inv : Subobject (H.restrict U.ι)) :
      U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso hGiso.symm
      inferInstance
  have : ((Subobject.mk e.inv : Subobject (H.restrict U.ι)) :
      U.toScheme.Modules).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} hGiso.symm
  obtain ⟨C, hCqc, hCft, e', -⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension H U hU (Subobject.mk e.inv)
  exact ⟨(C : X.Modules), hCqc, hCft, ⟨e'.trans hGiso⟩⟩

/-- **The extension assertion of [Stacks, Tag 0BK0].** On a quasi-compact, quasi-separated and
locally Noetherian scheme `X`, a coherent module on a quasi-compact open `U ⊆ X` is isomorphic to
the restriction to `U` of a coherent `𝒪_X`-module.

Coherence on a locally Noetherian scheme is quasi-coherence together with finite type
([Stacks, Tag 01XZ]), so this is
`AlgebraicGeometry.exists_isFiniteType_quasicoherent_restrict_iso` read through that equivalence,
on `U` to feed it and on `X` to state the conclusion. -/
@[ega "I 9.4.8" "special case"]
theorem exists_isCoherent_restrict_iso {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (G : U.toScheme.Modules) [G.IsCoherent] :
    ∃ F : X.Modules, F.IsCoherent ∧ Nonempty (F.restrict U.ι ≅ G) := by
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G
  obtain ⟨F, _, _, he⟩ := exists_isFiniteType_quasicoherent_restrict_iso U hU G
  have hFcoh : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType F
  exact ⟨F, hFcoh, he⟩

/-- **The extension assertion of [Stacks, Tag 0BK0], in the finite-module form the tag states it
in.** Let `R` be a Noetherian ring and `V ⊆ Spec R` an open. A coherent `𝒪_V`-module is the
restriction to `V` of a coherent module on `Spec R` whose global sections are a finite
`R`-module.

`Spec R` is quasi-compact, quasi-separated and — `R` being Noetherian — a Noetherian space, so
every open of it is quasi-compact and
`AlgebraicGeometry.exists_isCoherent_restrict_iso` applies. Finiteness of the global sections of
the resulting coherent module is `AlgebraicGeometry.moduleFinite_of_isFiniteType_qc`, a coherent
module being quasi-coherent and of finite type. -/
@[ega "I 9.4.8" "special case"]
theorem exists_isCoherent_module_finite_sections_restrict_iso (R : CommRingCat.{u})
    [IsNoetherianRing R] (V : (Spec R).Opens) (G : V.toScheme.Modules) [G.IsCoherent] :
    ∃ F : (Spec R).Modules, F.IsCoherent ∧
      Module.Finite (ToType R) Γ(F, (⊤ : (Spec R).Opens)) ∧
      Nonempty (F.restrict V.ι ≅ G) := by
  have hVc : IsCompact (V : Set (Spec R)) :=
    TopologicalSpace.NoetherianSpace.isCompact (V : Set (Spec R))
  obtain ⟨F, hFcoh, he⟩ := exists_isCoherent_restrict_iso V hVc G
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  exact ⟨F, hFcoh, moduleFinite_of_isFiniteType_qc R F, he⟩

end AlgebraicGeometry

end
