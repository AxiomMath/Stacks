module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# A quasi-coherent module with free global sections is the structure sheaf

Let `R` be a commutative ring and let `M` be a quasi-coherent `𝒪_{Spec R}`-module whose module of
global sections is free of rank one over `Γ(Spec R, 𝒪)`.  Then `M` is isomorphic to the structure
sheaf.  Quasi-coherence makes the counit `Γ(M)^~ ⟶ M` of the tilde–Gamma adjunction an
isomorphism, `tilde` carries an isomorphism of `R`-modules to an isomorphism of sheaves, and the
tilde of `R` itself *is* the structure sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.gammaTopLinearEquivOfIso` and
  `AlgebraicGeometry.Scheme.Modules.gammaTopTransport`: an isomorphism of `𝒪_X`-modules is a
  linear equivalence on global sections, and transports a trivialisation of the global sections.
* `AlgebraicGeometry.specGammaLinearEquiv`: a trivialisation of the global sections over
  `Γ(Spec R, 𝒪)` read as one over `R`.

## Main results

* `AlgebraicGeometry.nonempty_iso_unit_of_isQuasicoherent_of_gammaSpec`: **a quasi-coherent
  `𝒪_{Spec R}`-module whose global sections are free of rank one is the structure sheaf.**
* `AlgebraicGeometry.nonempty_iso_unit_of_isQuasicoherent_of_gammaTop`: the same for a scheme
  presented as the spectrum of a ring by an equality of schemes, which is the form a consumer
  holding such a presentation can apply.

## Implementation notes

Two rings act on the global sections of an `𝒪_{Spec R}`-module: `Γ(Spec R, 𝒪)`, which is the ring
the sheaf of modules is indexed by, and `R` itself, along `AlgebraicGeometry.Scheme.ΓSpecIso`,
which is the ring `AlgebraicGeometry.moduleSpecΓFunctor` and therefore `tilde` use.  The
comparison of the two actions is definitional, and `AlgebraicGeometry.specGammaLinearEquiv`
performs it: the underlying additive equivalence is the given one followed by the ring
equivalence, and its `R`-linearity is that scalar law.  The intermediate `Module R` instance is
introduced by hand because instance search does not see through the `Sheaf` projections of
`AlgebraicGeometry.Scheme.ringCatSheaf` to the structure presheaf.

"Free of rank one" is spelled as a linear equivalence with the ring of global functions, matching
`Stacks.SheafOfModules.Invertible.module_invertible_iff_nonempty_linearEquiv`; the conclusion is
`Nonempty` because the isomorphism depends on the choice of a generator.

No `stacks` attribute is attached: this is the affine comparison of Stacks 01I8 and Stacks 0B8M
run backwards at one module, not a clause of any tag, and each ingredient — the quasi-coherent
counit `Γ(M)^~ ≅ M` and `tilde (R) = 𝒪` — is Mathlib's.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- An isomorphism of `𝒪_X`-modules is a linear equivalence on the global sections. -/
def Scheme.Modules.gammaTopLinearEquivOfIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e).toLinearEquiv

/-- A trivialisation of the global sections of an `𝒪_X`-module transports along an isomorphism
of `𝒪_X`-modules. -/
def Scheme.Modules.gammaTopTransport {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)) : Γ(N, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
  (Scheme.Modules.gammaTopLinearEquivOfIso e).symm.trans h

/-- **A trivialisation of the global sections over `Γ(Spec R, 𝒪)` is one over `R`.** The `R`-action
on the global sections is the `Γ(Spec R, 𝒪)`-action read along `AlgebraicGeometry.Scheme.ΓSpecIso`,
so composing with that ring equivalence turns a `Γ(Spec R, 𝒪)`-linear equivalence into an
`R`-linear one. -/
def specGammaLinearEquiv {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (e : Γ(M, ⊤) ≃ₗ[Γ(Spec R, ⊤)] Γ(Spec R, ⊤)) :
    (moduleSpecΓFunctor.obj M : Type u) ≃ₗ[R] R := by
  letI : Module R (Γ(M, ⊤) : Type u) := (moduleSpecΓFunctor.obj M).isModule
  letI a : (Γ(M, ⊤) : Type u) ≃+ R :=
    e.toAddEquiv.trans (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toAddEquiv
  refine a.toLinearEquiv (fun c x => ?_)
  change (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv (e (c • x)) =
    c * (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv (e x)
  have hc : (c • x : (Γ(M, ⊤) : Type u)) = (Scheme.ΓSpecIso R).inv.hom c • x := rfl
  rw [hc, LinearEquiv.map_smul, smul_eq_mul, map_mul]
  refine congrArg (fun z => z * _) ?_
  change (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom c) = c
  simp

/-- **A quasi-coherent `𝒪_{Spec R}`-module whose global sections are free of rank one is the
structure sheaf.**  Quasi-coherence makes `Γ(M)^~ ⟶ M` an isomorphism, `tilde` carries the
trivialisation of `Γ(M)` to an isomorphism of sheaves, and `tilde (R)` is the structure sheaf. -/
theorem nonempty_iso_unit_of_isQuasicoherent_of_gammaSpec {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (hM : M.IsQuasicoherent)
    (e : Γ(M, ⊤) ≃ₗ[Γ(Spec R, ⊤)] Γ(Spec R, ⊤)) :
    Nonempty (M ≅ SheafOfModules.unit (Spec R).ringCatSheaf) := by
  have : M.IsQuasicoherent := hM
  exact ⟨(asIso (Scheme.Modules.fromTildeΓ M)).symm ≪≫
    (tilde.functor R).mapIso (specGammaLinearEquiv M e).toModuleIso ≪≫ tildeSelf⟩

/-- **A quasi-coherent module on a scheme which is the spectrum of a ring, whose global sections
are free of rank one, is the structure sheaf.**  The presentation of the scheme is taken as an
equality, which is the shape a consumer holding the spectrum of a chosen ring has. -/
theorem nonempty_iso_unit_of_isQuasicoherent_of_gammaTop {T : Scheme.{u}} {R : CommRingCat.{u}}
    (hT : T = Spec R) (M : T.Modules) (hM : M.IsQuasicoherent)
    (e : Γ(M, ⊤) ≃ₗ[Γ(T, ⊤)] Γ(T, ⊤)) :
    Nonempty (M ≅ SheafOfModules.unit T.ringCatSheaf) := by
  subst hT
  exact nonempty_iso_unit_of_isQuasicoherent_of_gammaSpec M hM e

end AlgebraicGeometry

end
