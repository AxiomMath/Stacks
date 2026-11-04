module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.GlobalSectionsComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ExtensionCohomologicalDimensionOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CanonicalExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor

/-!
# Uniqueness of a canonical coherent extension, and extension to `X`

In the algebraization situation, a coherent adic system on the open complement `U` which
canonically extends comes with a coherent adic system on `X` pro-isomorphic to the system
associated to its global sections. Two such extensions, each with a chosen pro-isomorphism,
are isomorphic by exactly one isomorphism compatible with the two choices.

The same system is then the restriction of a coherent adic system on `X` as an inverse system,
not merely as a pro-object: on the quasi-compact open `U ⊆ X = Spec(A)` every term `ℱₙ` is the
restriction of the quasi-coherent sheaf on `X` associated to the `A`-module `H⁰(U, ℱₙ)`, and the
pro-isomorphism of the canonical extension therefore transports to an isomorphism of systems
on `U`.

## Main definitions

* `Stacks.Algebraization.canonicalExtension` — the chosen coherent adic system on `X`,
  together with its pro-isomorphism.

## Main results

* `Stacks.Algebraization.existsUnique_compatibleIso` — the unique compatible isomorphism
  between two coherent adic systems presenting the same pro-object.
* `Stacks.Algebraization.extendsToX_kerComapSystem_of_canonicallyExtends` — part (2) of
  [Stacks, Tag 0EIR]: a coherent adic system on `U` which canonically extends to `X` extends
  to `X`.

## Implementation notes

Existence of the canonical extension is a choice from `CanonicallyExtends`, whose statement
already asserts exactly this pro-isomorphism. Uniqueness is full faithfulness of the pro-object
functor of Tag 0EIQ: the compatibility equation pins the isomorphism itself down, not merely its
isomorphism class.

Extension to `X` is `Stacks.Algebraization.extendsToX_of_canonicallyExtends` applied to the
comparison `Stacks.Algebraization.tildeGlobalSectionsPullbackIso`, which identifies the
restriction to `U` of the system of sheaves associated to the global sections with the system
itself.

`Stacks.Algebraization.ExtendsToX` is stated for a system along `S.Yι.ker.comap S.U.ι` while
`Stacks.Algebraization.extendsToX_of_canonicallyExtends` produces one along
`Stacks.Algebraization.toKerSystem`, the transport of the system along the equality of that
ideal sheaf with `Stacks.Algebraization.idealOnOpen`. The two presentations of the system are
compared through their common underlying diagram, by
`Stacks.Algebraization.exists_restrictionIso_of_eq_diagram` and
`Stacks.Algebraization.extendsToX_mk`, both of which keep that diagram a variable: comparing the
systems as objects instead would ask the kernel to identify the two ideal sheaves definitionally,
which unfolds `AlgebraicGeometry.Scheme.ΓSpecIso`.

## References

* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM), extension to `X`.
* [Stacks Project, Tag 0EIP](https://stacks.math.columbia.edu/tag/0EIP), canonical extension.
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0EIR.** A coherent adic system on `X` extending `F`, together with
a chosen pro-isomorphism from the sheaves associated to the global sections of `F`. -/
@[stacks 0EIR "unique_extension"]
public noncomputable def canonicalExtension
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (h : CanonicallyExtends S F) :
    Σ G : Stacks.Coherent.CoherentAdicSystems (idealOnX S),
      Stacks.Coherent.diagramToPro (tildeGlobalSectionsSystem S F) ≅
        (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G :=
  ⟨Classical.choose h, Classical.choice (Classical.choose_spec h)⟩

/-- **Stacks Project, Tag 0EIR.** Two coherent adic extensions of the same pro-object are
isomorphic by exactly one isomorphism compatible with their chosen pro-isomorphisms. -/
@[stacks 0EIR "unique_extension"]
public theorem existsUnique_compatibleIso
    (S : AlgebraizationSituation.{u})
    (P : (Ind (Scheme.QuasicoherentModules S.X)ᵒᵖ)ᵒᵖ)
    (G H : Stacks.Coherent.CoherentAdicSystems (idealOnX S))
    (φ : P ≅ (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj G)
    (ψ : P ≅ (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).obj H) :
    ∃! e : G ≅ H,
      φ ≪≫ (Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)).mapIso e = ψ := by
  let F := Stacks.Coherent.coherentAdicToPro S.X (idealOnX S)
  let hF : F.FullyFaithful :=
    Classical.choice (Stacks.Coherent.coherentAdicToPro_fullyFaithful S.X (idealOnX S))
  have hh : F.mapIso (hF.preimageIso (φ.symm ≪≫ ψ)) = φ.symm ≪≫ ψ :=
    hF.isoEquiv.apply_symm_apply _
  refine ⟨hF.preimageIso (φ.symm ≪≫ ψ), ?_, ?_⟩
  · change φ ≪≫ F.mapIso _ = ψ
    rw [hh]
    simp
  · intro e he
    apply hF.isoEquiv.injective
    change F.mapIso e = F.mapIso _
    change φ ≪≫ F.mapIso e = ψ at he
    simpa [hh] using congrArg (fun x => φ.symm ≪≫ x) he

section ExtensionToX

open CategoryTheory.Limits Opposite

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-! ### Part (2) of Stacks 0EIR -/

/-- `Stacks.Algebraization.ExtendsToX` for the system presented by its underlying diagram. -/
public theorem extendsToX_mk {D : ℕᵒᵖ ⥤ S.U.toScheme.Modules}
    (hD : Stacks.Coherent.IsCoherentAdicSystem (S.Yι.ker.comap S.U.ι) D)
    (h : ∃ G : Stacks.Coherent.CoherentAdicSystems S.Yι.ker,
      Nonempty (G.obj ⋙ Scheme.Modules.restrictFunctor S.U.ι ≅ D)) :
    ExtendsToX S ⟨D, hD⟩ := h

/-- **Part (2) of Stacks Project, Tag 0EIR.** A coherent `I`-adic system on the open complement
`U` which canonically extends to `X` is the restriction to `U` of a coherent `I`-adic system
on `X`. -/
@[stacks 0EIR "part (2): the implication CanonicallyExtends → ExtendsToX, for a coherent adic \
system on the open complement of an algebraization situation"]
public theorem extendsToX_kerComapSystem_of_canonicallyExtends (h : CanonicallyExtends S F) :
    ExtendsToX S (kerComapSystem S F) :=
  extendsToX_mk S (isCoherentAdicSystem_kerComap S F)
    (exists_restrictionIso_congr S (toKerSystem_obj S F)
      (extendsToX_of_canonicallyExtends S F (tildeGlobalSectionsPullbackIso S F) h))

end ExtensionToX

end Stacks.Algebraization

end
