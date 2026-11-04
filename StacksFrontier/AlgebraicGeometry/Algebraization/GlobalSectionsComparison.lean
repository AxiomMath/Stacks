module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CanonicalExtensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# A coherent adic system on the open complement from its global sections

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`. Let `(ℱₙ)` be an object of
`Coh(U, I𝒪_U)`. Each `A`-module `H⁰(U, ℱₙ)` has an associated quasi-coherent sheaf on `X`, and
this file proves that the restriction of that sheaf to `U` is `ℱₙ` again, as an isomorphism of
inverse systems.

## Main definitions

* `Stacks.Algebraization.pushforwardGlobalSectionsIso` — the global sections on `X` of the
  direct image of an `𝒪_U`-module are its global sections on `U`, as `A`-modules.
* `Stacks.Algebraization.tildeGlobalSectionsRestrictIso` — the comparison
  `(H⁰(U, ℱₙ)~)|_U ≅ ℱₙ` as `𝒪_U`-modules.
* `Stacks.Algebraization.tildeGlobalSectionsPullbackIso` — the same comparison read in
  quasi-coherent modules, which is the form the algebraization theorems use.

## Implementation notes

The comparison comes from the direct image rather than from the structure of `Coh(U, I𝒪_U)`:
the ideal `𝔞` is finitely generated, so `j : U ⟶ X` is quasi-compact and `j_*ℱₙ` is
quasi-coherent by Stacks 01LC; on the affine `X` the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` of the tilde-global-sections adjunction is
therefore an isomorphism `H⁰(X, j_*ℱₙ)~ ≅ j_*ℱₙ`; and `H⁰(X, j_*ℱₙ) = H⁰(U, ℱₙ)` as `A`-modules
while `(j_*ℱₙ)|_U ≅ ℱₙ` by the counit
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` of the
restriction-direct-image adjunction along an open immersion. Each step is a natural
transformation, so the composite is an isomorphism of inverse systems.

`Stacks.Algebraization.globalSectionsSystem` spells the sections functor with Mathlib's
`SheafOfModules.evaluation`, which is written `_root_.SheafOfModules.evaluation` here: in the
namespace `Stacks` the unqualified name resolves instead to `Stacks.SheafOfModules.evaluation`.

## References

* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- The open immersion `U ⟶ X` is quasi-compact: `U` is the complement of the zero locus of the
finitely generated ideal `𝔞`. -/
public instance quasiCompact_U_ι : QuasiCompact S.U.ι :=
  quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
      (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg (IsNoetherian.noetherian S.a)))

/-- The two `A`-actions on the sections of an `𝒪_U`-module over `U` agree: acting through
`A ⟶ Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)` is acting through `Stacks.Algebraization.scalarMap`. -/
public theorem appTop_ΓSpecIso_inv_smul (N : S.U.toScheme.Modules) (r : S.A) (x : Γ(N, ⊤)) :
    (S.U.ι.appTop ((Scheme.ΓSpecIso (.of S.A)).inv r)) • x = (scalarMap S r) • x := rfl

/-- The global sections on `X` of the direct image of an `𝒪_U`-module are its global sections
on `U`, as `A`-modules: the underlying abelian groups are the same, since `U ⟶ X` pulls `⊤`
back to `⊤`, and the two `A`-actions agree. -/
public def pushforwardGlobalSectionsIsoApp (N : S.U.toScheme.Modules) :
    (Scheme.Modules.pushforward S.U.ι ⋙ moduleSpecΓFunctor (R := .of S.A)).obj N ≅
      (_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (scalarMap S)).obj N :=
  (AddEquiv.toLinearEquiv
    (M := ↑((Scheme.Modules.pushforward S.U.ι ⋙
      moduleSpecΓFunctor (R := .of S.A)).obj N))
    (M₂ := ↑((_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars (scalarMap S)).obj N))
    (by rfl) (appTop_ΓSpecIso_inv_smul S N)).toModuleIso

/-- Taking the global sections on `X` of the direct image along `U ⟶ X` is taking the global
sections on `U`, naturally in the `𝒪_U`-module and as `A`-modules. -/
public def pushforwardGlobalSectionsIso :
    Scheme.Modules.pushforward S.U.ι ⋙ moduleSpecΓFunctor (R := .of S.A) ≅
      _root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars (scalarMap S) :=
  NatIso.ofComponents (pushforwardGlobalSectionsIsoApp S) fun _ ↦ rfl

variable (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The terms of a coherent adic system are quasi-coherent, being coherent. -/
public theorem isQuasicoherent_systemObj (n : ℕᵒᵖ) : (F.obj.obj n).IsQuasicoherent :=
  let : (F.obj.obj n).IsCoherent := F.property.1 n.unop
  isQuasicoherent_of_isCoherent (F.obj.obj n)

/-- The sheaf on `X` associated to the `A`-module `H⁰(U, ℱₙ)` is the direct image of `ℱₙ` along
`U ⟶ X`, naturally in `n`: that direct image is quasi-coherent, so the counit of the
tilde-global-sections adjunction on the affine `X` is an isomorphism on it. -/
public def tildeGlobalSectionsPushforwardIso :
    globalSectionsSystem S F ⋙ tilde.functor (.of S.A) ≅
      F.obj ⋙ Scheme.Modules.pushforward S.U.ι := by
  haveI (n : ℕᵒᵖ) : (F.obj.obj n).IsQuasicoherent := isQuasicoherent_systemObj S F n
  let h := Functor.whiskerLeft (F.obj ⋙ Scheme.Modules.pushforward S.U.ι)
    (Scheme.Modules.fromTildeΓNatTrans (R := .of S.A))
  haveI : ∀ n : ℕᵒᵖ, IsIso (h.app n) := fun n =>
    inferInstanceAs (IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward S.U.ι).obj (F.obj.obj n))))
  haveI : IsIso h := NatIso.isIso_of_isIso_app h
  exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F.obj (pushforwardGlobalSectionsIso S)).symm
      (tilde.functor (.of S.A)) ≪≫ asIso h ≪≫
    Functor.rightUnitor (F.obj ⋙ Scheme.Modules.pushforward S.U.ι)

/-- The restriction to `U` of the sheaf on `X` associated to the `A`-module `H⁰(U, ℱₙ)` is `ℱₙ`,
naturally in `n`. -/
public def tildeGlobalSectionsRestrictIso :
    (globalSectionsSystem S F ⋙ tilde.functor (.of S.A)) ⋙
      Scheme.Modules.pullback S.U.ι ≅ F.obj :=
  Functor.isoWhiskerLeft (globalSectionsSystem S F ⋙ tilde.functor (.of S.A))
      (Scheme.Modules.restrictFunctorIsoPullback S.U.ι).symm ≪≫
    Functor.isoWhiskerRight (tildeGlobalSectionsPushforwardIso S F)
      (Scheme.Modules.restrictFunctor S.U.ι) ≪≫
    Functor.isoWhiskerLeft F.obj (Scheme.Modules.restrictFunctorAdjCounitIso S.U.ι) ≪≫
    Functor.rightUnitor F.obj

/-- The comparison `(H⁰(U, ℱₙ)~)|_U ≅ ℱₙ` at a single stage, in quasi-coherent modules. -/
public def tildeGlobalSectionsPullbackIsoApp (n : ℕᵒᵖ) :
    (tildeGlobalSectionsSystem S F ⋙
        Stacks.Coherent.quasicoherentModulesPullback S.U.ι).obj n ≅
      (Stacks.Coherent.quasicoherentDiagram F).obj n :=
  ObjectProperty.isoMk _ ((tildeGlobalSectionsRestrictIso S F).app n)

/-- **Stacks Project, Tag 0EIR (the comparison).** The system of quasi-coherent sheaves on `X`
associated to the global sections of a coherent adic system on `U` restricts on `U` to the
system itself. -/
public def tildeGlobalSectionsPullbackIso :
    tildeGlobalSectionsSystem S F ⋙ Stacks.Coherent.quasicoherentModulesPullback S.U.ι ≅
      Stacks.Coherent.quasicoherentDiagram F :=
  NatIso.ofComponents (tildeGlobalSectionsPullbackIsoApp S F) (fun {n m} f => by
    apply ObjectProperty.hom_ext
    exact (tildeGlobalSectionsRestrictIso S F).hom.naturality f)

end Stacks.Algebraization

end
