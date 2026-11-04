module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSections
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.CategoryTheory.NatIsoOfEpiCone
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences

/-!
# The sheaf tower on the complement is the sheafified algebraic tower

Fix a Noetherian ring `A` with ideals `I ⊆ 𝔞`, write `X = Spec(A)` and let `U = X ∖ V(𝔞)` be the
open complement. For an `A`-module `M` there are two towers of `𝒪_U`-modules in play, and the
algebraization statements of Stacks chapter 52 need them to be the same tower:

* the *sheaf* tower `Stacks.Algebraization.quotientSystemNearVanishing`, whose term at `n` is the
  quotient `(M^~|_U) / (I 𝒪_U)ⁿ (M^~|_U)` of the restricted associated sheaf by the `n`-th power
  of the ideal sheaf `I 𝒪_U`. This is the tower `Stacks.Algebraization.formalSections` evaluates,
  and therefore the one the comparison map of Stacks 0EG2 lands in;
* the *algebraic* tower `n ↦ (M/IⁿM)^~|_U`, the restricted associated sheaves of the module
  quotients. This is what every algebraic statement about `M` computes with.

This file identifies them, as an isomorphism of functors `ℕᵒᵖ ⥤ U.Modules`.

## Main results

* `Stacks.Algebraization.idealSheafNearVanishing_eq_idealOnOpen` — the two names the library uses
  for the ideal sheaf `I 𝒪_U` agree.
* `Stacks.Algebraization.quotientSystemNearVanishingIso` — **the bridge**: the sheaf tower of
  ideal-power quotients of `M^~|_U` is the tower of the sheafified module quotients `M/IⁿM`.
* `Stacks.Algebraization.cokernel_π_comp_adicQuotientSystemRestrictedTildeIso` — the bridge is
  normalized: at each level it carries the sheaf quotient projection to the sheafification of the
  algebraic quotient map `M ⟶ M/IⁿM`. Since those projections are epimorphisms this pins the
  bridge down uniquely.
* `Stacks.Algebraization.formalSectionsRestrictedTildeIso` — the bridge on sections, which is the
  form the algebraization arguments consume: `Stacks.Algebraization.formalSections` is the inverse
  system `n ↦ Γ(U, (M/IⁿM)^~)`.
* `Stacks.Algebraization.restrictedTildeQuotientTower_sections_obj` — those sections, written over
  the image of `U` in `Spec(A)`. This is the shape
  `Stacks.Algebraization.ComplementTower.sectionsModPower` of Stacks 0EII is stated in, so it is
  the identification through which 0EII is transported to `formalSections`.

## Implementation notes

The termwise statement is `Stacks.Algebraization.restrictedTilde_quotient_transition`, taken at
the identity map of `M/IⁿM`, whose kernel and range are `⊥` and `⊤`, so both of its torsion
hypotheses hold for trivial reasons. All this file adds is naturality in `n`, and that comes for
free from the normalization: after precomposition with the level-`i` quotient projection, an
epimorphism, both composites around a naturality square become the sheafification of
`M ⟶ M/IʲM`.

The two towers are indexed in the same way, by the exponent itself, so no level shift is
involved. The level-`0` terms agree too, both being zero: the zeroth power of the ideal sheaf is
the unit ideal, and `M/I⁰M = 0`.

Both sides mention `I 𝒪_U` under different names — `idealSheafNearVanishing` for the
near-vanishing machinery and `idealOnOpen` for the finite-module-model machinery. They are equal
but not definitionally so, the first being `ofIdealTop` of the extension of `I` to `Γ(U, 𝒪_U)`
and the second the pullback along `U ⟶ X` of `ofIdealTop` of the extension of `I` to
`Γ(X, 𝒪_X)`. Rather than transport along that equality, which would leave `eqToHom`s in the
normalization, the construction is stated for an arbitrary ideal sheaf `J` presented as
`I 𝒪_U`; the hypothesis is then discharged by substitution, and the near-vanishing spelling is
the instance at `idealSheafNearVanishing`.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0DXT](https://stacks.math.columbia.edu/tag/0DXT)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology (complementTilde complementZeroLocus idealPowerQuotientTower
  idealPowerQuotientCone)


/-- **The two names for the ideal sheaf `I 𝒪_U`.** `idealSheafNearVanishing` extends `I` to
`Γ(U, 𝒪_U)` and takes the quasi-coherent ideal sheaf of the result; `idealOnOpen` extends `I` to
`Γ(X, 𝒪_X)` and pulls the resulting ideal sheaf back along the open immersion. -/
public theorem idealSheafNearVanishing_eq_idealOnOpen (S : AlgebraizationSituation.{u}) :
    idealSheafNearVanishing S.A S.I S.a = idealOnOpen S :=
  Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_comap S.A S.I S.U.ι

section

variable (S : AlgebraizationSituation.{u}) (M : ModuleCat.{u} S.A)

/-- The tower `n ↦ (M/IⁿM)^~|_U` of sheafified algebraic quotients on the complement. -/
public abbrev restrictedTildeQuotientTower : ℕᵒᵖ ⥤ S.U.toScheme.Modules :=
  idealPowerQuotientTower.{u, u} S.I M ⋙ restrictedTildeFunctor S

variable {J : S.U.toScheme.IdealSheafData} (hJ : J = idealOnOpen S)

include hJ

/-- **The level-`n` comparison of the two towers**, together with its normalization against the
quotient projections.

This is `Stacks.Algebraization.restrictedTilde_quotient_transition` at the identity map of
`M/IⁿM`: the identity has kernel `⊥` and range `⊤`, so both torsion hypotheses hold. -/
public theorem exists_adicQuotientTermIso (n : ℕᵒᵖ) :
    ∃ e : (adicQuotientSystem J ((restrictedTildeFunctor S).obj M)).obj n ≅
        (restrictedTildeQuotientTower S M).obj n,
      cokernel.π (C := S.U.toScheme.Modules)
          (idealPowerMultiple J n.unop ((restrictedTildeFunctor S).obj M)).ι ≫ e.hom =
        (restrictedTildeFunctor S).map
          ((idealPowerQuotientCone.{u, u} S.I M).π.app n) := by
  subst hJ
  have htriv : ∀ (N : Type u) (_ : AddCommGroup N) (_ : Module S.A N) (_ : Subsingleton N),
      IsIPowerTorsion S.A N S.a :=
    fun _ _ _ _ _ => ⟨1, Nat.one_pos, fun _ _ => Subsingleton.elim _ _⟩
  exact restrictedTilde_quotient_transition_idealPowerQuotient S M
    (ModuleCat.of S.A (M ⧸ S.I ^ n.unop • (⊤ : Submodule S.A M))) n.unop LinearMap.id
    ⟨htriv _ _ _ (by rw [LinearMap.ker_id]; infer_instance),
      htriv _ _ _ (by rw [LinearMap.range_id]; infer_instance)⟩

/-- **The bridge.** The sheaf tower of ideal-power quotients of `M^~|_U` along `I 𝒪_U` is the
tower of the sheafifications of the module quotients `M/IⁿM`.

Naturality is forced by the normalization: after precomposition with the level-`i` quotient
projection, which is an epimorphism, both sides of a naturality square become the sheafification
of `M ⟶ M/IʲM`. -/
public def adicQuotientSystemRestrictedTildeIso :
    adicQuotientSystem J ((restrictedTildeFunctor S).obj M) ≅ restrictedTildeQuotientTower S M :=
  CategoryTheory.natIsoOfEpiNormalizedCone ((restrictedTildeFunctor S).obj M)
    (fun n => (adicQuotientCone J ((restrictedTildeFunctor S).obj M)).π.app n)
    (fun n => (restrictedTildeFunctor S).map ((idealPowerQuotientCone.{u, u} S.I M).π.app n))
    (fun f => (adicQuotientCone J ((restrictedTildeFunctor S).obj M)).w f)
    (fun f => ((restrictedTildeFunctor S).map_comp _ _).symm.trans
      (congrArg (restrictedTildeFunctor S).map ((idealPowerQuotientCone.{u, u} S.I M).w f)))
    (fun n => show Epi (cokernel.π (C := S.U.toScheme.Modules)
      (idealPowerMultiple J n.unop ((restrictedTildeFunctor S).obj M)).ι) from inferInstance)
    (fun n => (exists_adicQuotientTermIso S M hJ n).choose)
    (fun n => (exists_adicQuotientTermIso S M hJ n).choose_spec)

/-- **The bridge is normalized.** At each level it carries the sheaf quotient projection
`M^~|_U ⟶ (M^~|_U)/Jⁿ(M^~|_U)` to the sheafification of the algebraic quotient map
`M ⟶ M/IⁿM`. Since the projection is an epimorphism, this determines the bridge uniquely. -/
public theorem cokernel_π_comp_adicQuotientSystemRestrictedTildeIso (n : ℕᵒᵖ) :
    cokernel.π (C := S.U.toScheme.Modules)
        (idealPowerMultiple J n.unop ((restrictedTildeFunctor S).obj M)).ι ≫
      (adicQuotientSystemRestrictedTildeIso S M hJ).hom.app n =
      (restrictedTildeFunctor S).map ((idealPowerQuotientCone.{u, u} S.I M).π.app n) :=
  (exists_adicQuotientTermIso S M hJ n).choose_spec

/-- **The bridge, in the near-vanishing spelling.** The tower
`Stacks.Algebraization.quotientSystemNearVanishing` of ideal-power quotients of `M^~|_U` — the
tower `Stacks.Algebraization.formalSections` evaluates, hence the target of the comparison map of
Stacks 0EG2 — is the tower `n ↦ (M/IⁿM)^~|_U` of sheafified algebraic quotients. -/
public def quotientSystemNearVanishingIso :
    quotientSystemNearVanishing S.A S.I S.a
        (complementTilde S.A S.a M : (complementZeroLocus S.A S.a : Scheme).Modules) ≅
      restrictedTildeQuotientTower S M :=
  adicQuotientSystemRestrictedTildeIso S M (idealSheafNearVanishing_eq_idealOnOpen S)

/-- **The bridge on sections.** `Stacks.Algebraization.formalSections`, the inverse system
`n ↦ Γ(U, (M^~|_U)/(I𝒪_U)ⁿ(M^~|_U))` whose limit the comparison map of Stacks 0EG2 lands in, is
the inverse system `n ↦ Γ(U, (M/IⁿM)^~)` of sections of the sheafified module quotients.

This is `Stacks.Algebraization.quotientSystemNearVanishingIso` evaluated on all of `U`, and it
is the form the algebraization arguments use: the right-hand side is what the algebra computes
with, the left-hand side is what `Stacks.Algebraization.comparisonAt` maps into. -/
public def formalSectionsRestrictedTildeIso :
    formalSections S.A S.I S.a
        (complementTilde S.A S.a M : (complementZeroLocus S.A S.a : Scheme).Modules) ≅
      restrictedTildeQuotientTower S M ⋙ Scheme.Modules.toPresheaf _ ⋙
        (CategoryTheory.evaluation _ Ab.{u}).obj (op ⊤) :=
  Functor.isoWhiskerRight (quotientSystemNearVanishingIso S M)
    (Scheme.Modules.toPresheaf _ ⋙ (CategoryTheory.evaluation _ Ab.{u}).obj (op ⊤))

omit hJ in
/-- The `n`-th term of the sheafified algebraic tower, read on all of `U`, is the module of
sections of `(M/IⁿM)^~` over the image of `U` in `Spec(A)`.

This is the shape `Stacks.Algebraization.ComplementTower.sectionsModPower` is stated in, so it is
the identification through which Stacks 0EII is transported to `formalSections`; the two differ
only in writing the open set as `U` or as its image under the open immersion, which
`AlgebraicGeometry.Scheme.Opens.ι_image_top` reconciles. -/
public theorem restrictedTildeQuotientTower_sections_obj (n : ℕᵒᵖ) :
    (restrictedTildeQuotientTower S M ⋙ Scheme.Modules.toPresheaf _ ⋙
        (CategoryTheory.evaluation _ Ab.{u}).obj (op ⊤)).obj n =
      ((Scheme.Modules.toPresheaf (Spec (CommRingCat.of S.A))).obj
          (tilde (ModuleCat.of S.A (M ⧸ S.I ^ n.unop • (⊤ : Submodule S.A M))))).obj
        (op (S.U.ι ''ᵁ ⊤)) :=
  rfl

end

end Stacks.Algebraization

end
