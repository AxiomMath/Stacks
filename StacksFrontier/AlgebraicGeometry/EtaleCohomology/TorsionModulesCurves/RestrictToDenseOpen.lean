module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Finiteness.Finsupp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ClosedComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.RingTheory.Noetherian.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of cohomology and restriction to an open subscheme

Let `Λ` be a Noetherian ring, let `X` be a scheme, let `j : X' ⟶ X` be an open immersion and let
`i : Z ⟶ X` be a closed immersion onto the complement of the image of `j`. For a sheaf `ℱ` of
`Λ`-modules on `X_étale` the localization short exact sequence

```
0 ⟶ j_!j^{-1}ℱ ⟶ ℱ ⟶ i_*i^{-1}ℱ ⟶ 0
```

relates the cohomology of `ℱ` to that of `j_!j^{-1}ℱ`. If the cohomology of `i_*i^{-1}ℱ` is
concentrated in degree zero and is a finite `Λ`-module there, then in every degree
`H^q_étale(X, ℱ)` is a finite `Λ`-module if and only if `H^q_étale(X, j_!j^{-1}ℱ)` is.

## Main definitions

* `Stacks.EtaleCohomology.TorsionModules.moduleEtaleCohomology` — étale cohomology of a sheaf of
  `Λ`-modules, the right derived functor of global sections.
* `Stacks.EtaleCohomology.TorsionModules.moduleRestriction`,
  `moduleExtensionByZero`, `moduleDirectImage`, `moduleInverseImage` — the four functors
  `j^{-1}`, `j_!`, `i_*`, `i^{-1}` on sheaves of `Λ`-modules of the small étale sites, with
  their two adjunctions. These are the constructions of
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic` and
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction` with coefficients in
  `ModuleCat Λ` instead of `AddCommGrpCat`.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.module_finite_of_exact` — over a Noetherian ring, the
  middle term of a three-term exact sequence of modules with finite outer terms is finite.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_iff_extensionByZero` —
  **Stacks Tag 0GJE**, in the form described above.

## Implementation notes

**What is proved here.** The long exact cohomology sequence of the localization sequence, read
through the `δ`-functor `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, and
the module algebra over a Noetherian ring that turns it into the biconditional. Both implications
are proved. Writing `A^q = H^q(X, j_!j^{-1}ℱ)`, `B^q = H^q(X, ℱ)` and `C^q = H^q(X, i_*i^{-1}ℱ)`,
the inputs used are the three exact segments `A^q → B^q → C^q`, `C^{q-1} → A^q → B^q` and the
monomorphism `A^0 ↪ B^0`. In one direction `B^q` sits between the finite modules `A^q` and `C^q`;
in the other `A^q` sits between `C^{q-1}` and `B^q`, with `C^{q-1}` finite because it is either
`C^0` or zero, and `A^0` is a submodule of the finite module `B^0`. Noetherianness of `Λ` enters
exactly where a submodule of a finite module has to be finite.

**What is assumed, and why.** Two things.

*The localization sequence for module coefficients.* Tag 095L is in the tree, but only for
abelian sheaves — `Stacks.EtaleCohomology.openClosedShortComplex_shortExact` is stated for
`Sheaf X.smallEtaleTopology AddCommGrpCat`. Its proof is stalkwise and does not transport to
`ModuleCat Λ` coefficients without an independent argument, so the statement is carried as the
hypothesis `h095L`, in its general form: universally quantified over every scheme, every closed
immersion, every open immersion onto the complement and every sheaf of `Λ`-modules, and
instantiated only inside the proof at `i`, `j` and `ℱ`. It is a different tag, and it mentions
neither cohomology nor finiteness.

*The cohomology of the closed part.* The hypotheses `h0` and `hpos` say that
`H^0(X, i_*i^{-1}ℱ)` is a finite `Λ`-module and that `H^q(X, i_*i^{-1}ℱ)` vanishes for `q > 0`.
This is **not** a Stacks tag; it is the place where the whole geometric content of Tag 0GJE
sits, and it is what this file does not deliver. In the source it is obtained as follows: `X` is
separated of finite type of dimension at most one over an algebraically closed field `k` and
`X'` is dense, so `Z = X \ X'` is zero-dimensional and hence a finite set of `k`-rational
points; `i` is a closed immersion, hence finite, so Proposition 03QP and the Leray collapse
(Lemma 0733) give `H^q(X, i_*i^{-1}ℱ) = H^q(Z, i^{-1}ℱ)`; `Z` is a disjoint union of spectra of
algebraically closed fields, so that vanishes for `q > 0` and is the direct sum of the stalks
`ℱ_{x_1}, …, ℱ_{x_n}` in degree zero; and those stalks are finite `Λ`-modules because `ℱ` is
constructible.

None of the four steps of that chain is available in this repository. Tag 03QP is not proved
(see the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FinitePushforwardStalk.lean`); there is no notion
of the dimension of a scheme in the tree, only `topologicalKrullDim` of its carrier; the étale
cohomology of a spectrum of an algebraically closed field with module coefficients is not
computed; and the stalks of a constructible sheaf of `Λ`-modules
(`AlgebraicGeometry.IsConstructibleModuleSheaf`) are not shown to be finite. Accordingly the
hypotheses of the source statement that feed only into that chain — `k` algebraically closed,
`X` separated of finite type over `k` of dimension at most one, `X'` dense in `X`, and `ℱ`
constructible — do not appear in the statement below, which is correspondingly more general.

## References

* [Stacks Project, Tag 0GJE](https://stacks.math.columbia.edu/tag/0GJE)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
* [Stacks Project, Tag 0GJG](https://stacks.math.columbia.edu/tag/0GJG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u w r s

namespace Stacks.EtaleCohomology.TorsionModules

/-! ### Module algebra over a Noetherian ring -/

section ModuleAlgebra

variable (Λ : Type r) [CommRing Λ]

/-- A module which is a zero object of `ModuleCat Λ` is a finite `Λ`-module. -/
lemma module_finite_of_isZero {M : ModuleCat.{s} Λ} (h : IsZero M) : Module.Finite Λ M :=
  have := ModuleCat.subsingleton_of_isZero h
  have : Finite M := Finite.of_subsingleton
  inferInstance

variable [IsNoetherianRing Λ]

/-- **The middle term of a three-term exact sequence of modules over a Noetherian ring is finite
if the outer two are.** The image of `X₂` in `X₃` is a submodule of a finite module, hence
finite, and `X₂` is an extension of it by a quotient of `X₁`. -/
lemma module_finite_of_exact (T : ShortComplex (ModuleCat.{s} Λ)) (hT : T.Exact)
    (h₁ : Module.Finite Λ T.X₁) (h₃ : Module.Finite Λ T.X₃) : Module.Finite Λ T.X₂ := by
  have hrange : LinearMap.range T.f.hom = LinearMap.ker T.g.hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker T).mp hT
  have := h₁
  have := h₃
  have : IsNoetherian Λ T.X₃ := isNoetherian_of_isNoetherianRing_of_finite Λ _
  have : Module.Finite Λ (LinearMap.range T.g.hom) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  exact Module.Finite.of_exact (R := Λ) (f := T.f.hom) (g := T.g.hom.rangeRestrict)
    (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]; exact hrange.symm)
    (by rw [← LinearMap.range_eq_top, LinearMap.range_rangeRestrict])

/-- A module admitting a monomorphism into a finite module over a Noetherian ring is finite. -/
lemma module_finite_of_mono {M N : ModuleCat.{s} Λ} (f : M ⟶ N) (hf : Mono f)
    (hN : Module.Finite Λ N) : Module.Finite Λ M :=
  have := hN
  have : IsNoetherian Λ N := isNoetherian_of_isNoetherianRing_of_finite Λ _
  Module.Finite.of_injective (σ := RingHom.id Λ) (σ' := RingHom.id Λ) f.hom
    ((ModuleCat.mono_iff_injective f).mp hf)

end ModuleAlgebra

/-! ### Sheaves of `Λ`-modules on small étale sites -/

section Setup

variable (Λ : Type r) [CommRing Λ]

/-- Sheafification exists for presheaves of `Λ`-modules on the small étale site of any scheme;
this is `AlgebraicGeometry.Scheme.comparisonSheafification_exists`, recorded as an instance so
that the étale cohomology of a sheaf of `Λ`-modules can be spoken about unconditionally. -/
instance hasSheafify_smallEtaleTopology_moduleCat (W : Scheme.{u}) :
    HasSheafify W.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) :=
  (Scheme.comparisonSheafification_exists.{u, w, r} W Λ).1

/-- Global sections of sheaves on a site with a terminal object are additive, being the sections
over that object; this is what makes `CategoryTheory.Sheaf.Γ` usable as the functor whose right
derived functors are cohomology. -/
instance additive_sheafΓ {C : Type*} [Category* C] (J : GrothendieckTopology C) [HasTerminal C]
    (A : Type*) [Category* A] [Preadditive A] [HasWeakSheafify J A]
    [HasGlobalSectionsFunctor J A] : (Sheaf.Γ J A).Additive :=
  have : ((sheafSections J A).obj (op (terminal C))).Additive := ⟨by intros; rfl⟩
  Functor.additive_of_iso (Sheaf.ΓNatIsoSheafSections J A terminalIsTerminal).symm

/-- **Étale cohomology of a sheaf of `Λ`-modules**: the `q`-th right derived functor of global
sections on the small étale site. -/
abbrev moduleEtaleCohomology (X : Scheme.{u}) (q : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) ⥤
      ModuleCat.{max (u + 1) w r} Λ :=
  (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ)).rightDerived q

/-- The restriction `j^{-1}` of sheaves of `Λ`-modules along an étale morphism `j : U ⟶ X`:
precomposition with `AlgebraicGeometry.Scheme.Etale.smallEtaleCompose`. -/
abbrev moduleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) ⥤
      Sheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) :=
  (Scheme.Etale.smallEtaleCompose j).sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) w r} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- **Extension by zero `j_!` of sheaves of `Λ`-modules** along an étale morphism `j : U ⟶ X`:
the left adjoint of restriction, the sheafification of the left Kan extension along composition
with `j`. -/
abbrev moduleExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    Sheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.Etale.smallEtaleCompose j)
    (ModuleCat.{max (u + 1) w r} Λ) U.smallEtaleTopology X.smallEtaleTopology

/-- Extension by zero is left adjoint to restriction, on sheaves of `Λ`-modules. -/
def moduleExtensionByZeroAdj {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    moduleExtensionByZero.{u, w, r} Λ j ⊣ moduleRestriction.{u, w, r} Λ j :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The direct image `i_*` of sheaves of `Λ`-modules along a morphism `i : Z ⟶ X`:
precomposition with base change along `i`. -/
abbrev moduleDirectImage {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) :=
  (smallEtaleBaseChange i).sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) w r} Λ) X.smallEtaleTopology Z.smallEtaleTopology

/-- The inverse image `i^{-1}` of sheaves of `Λ`-modules along a morphism `i : Z ⟶ X`. -/
abbrev moduleInverseImage {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) ⥤
      Sheaf Z.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange i)
    (ModuleCat.{max (u + 1) w r} Λ) X.smallEtaleTopology Z.smallEtaleTopology

/-- The inverse image is left adjoint to the direct image, on sheaves of `Λ`-modules. -/
def moduleInverseImageDirectImageAdj {Z X : Scheme.{u}} (i : Z ⟶ X) :
    moduleInverseImage.{u, w, r} Λ i ⊣ moduleDirectImage.{u, w, r} Λ i :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

end Setup

/-! ### The localization sequence and finiteness -/

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- The localization short complex of a closed immersion `i` and the open immersion `j` of its
complement, for coefficients in `ModuleCat Λ`: the counit of `j_! ⊣ j^{-1}` followed by the unit
of `i^{-1} ⊣ i_*`, given a proof that the composite vanishes. This is
`Stacks.EtaleCohomology.openClosedShortComplex` with module coefficients. -/
abbrev openClosedModuleShortComplex {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]
    (ℱ : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ))
    (hz : (moduleExtensionByZeroAdj.{u, w, r} Λ j).counit.app ℱ ≫
      (moduleInverseImageDirectImageAdj.{u, w, r} Λ i).unit.app ℱ = 0) :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ)) :=
  ShortComplex.mk ((moduleExtensionByZeroAdj.{u, w, r} Λ j).counit.app ℱ)
    ((moduleInverseImageDirectImageAdj.{u, w, r} Λ i).unit.app ℱ) hz

/-- **Stacks Project, Tag 0GJE**, granted Tag 095L for sheaves of `Λ`-modules as the hypothesis
`h095L`, and the cohomology of `i_*i^{-1}ℱ` as the hypotheses `h0` and `hpos`.

Let `Λ` be a Noetherian ring, let `X` be a scheme, let `j : X' ⟶ X` be an open immersion and let
`i : Z ⟶ X` be a closed immersion whose image is the complement of the image of `j`. Let `ℱ` be
a sheaf of `Λ`-modules on `X_étale`. If `H^0_étale(X, i_*i^{-1}ℱ)` is a finite `Λ`-module and
`H^q_étale(X, i_*i^{-1}ℱ) = 0` for `q > 0`, then for every `q`

  `H^q_étale(X, ℱ)` is a finite `Λ`-module  ↔  `H^q_étale(X, j_!j^{-1}ℱ)` is a finite
  `Λ`-module.

The hypothesis `h095L` is the general statement of Tag 095L for sheaves of `Λ`-modules: for
*every* scheme, *every* closed immersion into it, *every* open immersion onto the complement and
*every* sheaf of `Λ`-modules, the localization short complex exists and is short exact. It is a
different tag, it quantifies over all of its own inputs, it is instantiated only inside the
proof, and it says nothing about cohomology or finiteness.

The hypotheses `h0` and `hpos` are not a Stacks tag. They are the cohomological consequence of
the geometric hypotheses of the source — `X` separated of finite type of dimension at most one
over an algebraically closed field, `X'` dense, `ℱ` constructible — and are the part of Tag 0GJE
this declaration does **not** prove; see the implementation notes of this file for the chain of
four absent results they stand in for. They concern `i_*i^{-1}ℱ` only, and so are independent of
the conclusion, which concerns `ℱ` and `j_!j^{-1}ℱ`. -/
@[stacks 0GJE "granted 095L for Λ-module sheaves as h095L; closed part's cohomology as h0, hpos"]
theorem module_finite_cohomology_iff_extensionByZero
    {X Z X' : Scheme.{u}} (i : Z ⟶ X) (j : X' ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (h095L : ∀ {W Z' U' : Scheme.{u}} (i' : Z' ⟶ W) (j' : U' ⟶ W) [IsClosedImmersion i']
        [IsOpenImmersion j'], Set.range j'.base = (Set.range i'.base)ᶜ →
      ∀ 𝒢 : Sheaf W.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ),
        ∃ hz : (moduleExtensionByZeroAdj.{u, w, r} Λ j').counit.app 𝒢 ≫
            (moduleInverseImageDirectImageAdj.{u, w, r} Λ i').unit.app 𝒢 = 0,
          (openClosedModuleShortComplex.{u, w, r} Λ i' j' 𝒢 hz).ShortExact)
    (ℱ : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ))
    (h0 : Module.Finite Λ ((moduleEtaleCohomology.{u, w, r} Λ X 0).obj
      ((moduleDirectImage.{u, w, r} Λ i).obj ((moduleInverseImage.{u, w, r} Λ i).obj ℱ))))
    (hpos : ∀ q, 0 < q → IsZero ((moduleEtaleCohomology.{u, w, r} Λ X q).obj
      ((moduleDirectImage.{u, w, r} Λ i).obj ((moduleInverseImage.{u, w, r} Λ i).obj ℱ))))
    (q : ℕ) :
    Module.Finite Λ ((moduleEtaleCohomology.{u, w, r} Λ X q).obj ℱ) ↔
      Module.Finite Λ ((moduleEtaleCohomology.{u, w, r} Λ X q).obj
        ((moduleExtensionByZero.{u, w, r} Λ j).obj
          ((moduleRestriction.{u, w, r} Λ j).obj ℱ))) := by
  obtain ⟨hz, hS⟩ := h095L i j hij ℱ
  set S := openClosedModuleShortComplex.{u, w, r} Λ i j ℱ hz with hSdef
  set F := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) with hF
  set D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F with hD
  -- the cohomology of the closed part is finite in every degree
  have hC : ∀ n : ℕ, Module.Finite Λ ((D.functor n).obj S.X₃) := by
    intro n
    match n with
    | 0 => exact h0
    | (n + 1) => exact module_finite_of_isZero Λ (hpos (n + 1) n.succ_pos)
  constructor
  · -- `B^q` finite implies `A^q` finite
    intro hB
    match q with
    | 0 =>
      exact module_finite_of_mono Λ ((D.functor 0).map S.f) (D.mono_map_f hS) hB
    | (n + 1) =>
      exact module_finite_of_exact Λ _ (D.exact_δ₂ hS n) (hC n) hB
  · -- `A^q` finite implies `B^q` finite
    intro hA
    exact module_finite_of_exact Λ _ (D.exact_map hS q) hA (hC q)

end Stacks.EtaleCohomology.TorsionModules

end
