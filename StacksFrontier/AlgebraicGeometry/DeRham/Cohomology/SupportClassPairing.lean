module

public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.CechTermPairing
public import StacksFrontier.AlgebraicGeometry.DeRham.Cohomology.DegreeZeroCupProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroBilinear

/-!
# Pairing a module with the local cohomology sheaf along the equations

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = d + 1` cut out a closed subset
`T`, and let `μ : ℳ × 𝒩 ⟶ 𝒫` be a pairing of `𝒪_X`-modules. This file descends the pairing of
`StacksFrontier/AlgebraicGeometry/DeRham/Cohomology/CechTermPairing.lean` from the top term of the
extended alternating Čech complex to the degree-`c` local cohomology sheaf, producing

`ℳ × i_*ℋ^c_T(𝒩) ⟶ i_*ℋ^c_T(𝒫)`,

and identifies it on the classes of the class map of [Stacks, Tag 0G7Q]: the pairing of a
section of `ℳ` with the class of `s / (f₁ ⋯ f_c)` is the class of `μ(m, s) / (f₁ ⋯ f_c)`.

**Why no derived tensor identification is needed.** In the equation-chart model the degree-`c`
local cohomology sheaf *is* the cokernel of the last differential
(`Stacks.Perfect.SupportedFraction.cokernelLastDifToSupport`, invertible by Stacks 0G7M), so
descending a pairing past it is the universal property of a cokernel in the category of sheaves
of modules, applied to the internal hom. A bilinear map out of a sheaf of modules is a morphism
into `SheafOfModules.moduleHomSheaf`, which is a sheaf by [Stacks, Tag 03EM], so `cokernel.desc`
applies verbatim; no K-flatness, no right exactness of a tensor product and no excision enter.

**Why no base change for the class map is needed.** The input pairing is the Čech-term pairing,
which exists because each term is `j_*j^*𝒩` for an open immersion `j` and the first argument is
restricted along `j`. [Stacks, Tag 0G7U] is nowhere used.

## Main definitions

* `Stacks.Perfect.CechPairing.cokPair`: the descended pairing on the cokernels of the last
  differentials.
* `Stacks.Perfect.CechPairing.supportPair`: the same pairing read on `i_*ℋ^c_T`, through the
  identification of Stacks 0G7M.

## Main results

* `Stacks.Perfect.CechPairing.cokPair_cokernelπ`: the descended pairing computes the Čech-term
  pairing on classes — the equation that `cokernel.desc` is chosen to satisfy.
* `Stacks.Perfect.CechPairing.pairVal_fractionHom`: **the pairing on the fraction cochain.**
  Pairing with `s / (f₁ ⋯ f_c)` is `μ(m, s) / (f₁ ⋯ f_c)`; the proof is
  `Stacks.BilinearMap.map_smul_right` against `Ring.inverse (∏ f)`.
* `Stacks.Perfect.CechPairing.supportPair_supportedFractionSource`: **the pairing is compatible
  with the class map of [Stacks, Tag 0G7Q]**, which is the form in which the Gysin projection
  formula consumes it.
* `Stacks.Perfect.CechPairing.rightMulHom_flip_supportPair`: **the pairing with a global first
  argument is the canonical functorial action** `supportCohomologySheafMap` of the
  multiplication morphism, in which no family of equations occurs. This is what says the
  pairing does not depend on the chosen equations on the arguments its consumers use.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechPairing

variable {X : Scheme.{u}} {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
variable {M N P : X.Modules} (μ : Stacks.BilinearMap M.val N.val P.val)

/-! ### Descending the pairing to the cokernel of the last differential -/

/-- The Čech-term pairing followed by the projection onto the cokernel of the last
differential, with the Čech term read as the first variable so that it can be curried. -/
def cokSource :
    Stacks.BilinearMap (prodTerm f N d).val M.val (cokernel (lastDif f P)).val :=
  ((cechPair f μ d).postcomp (cokernel.π (lastDif f P)).val).flip

/-- The sheaf-hom from `ℳ` into the cokernel of the last differential, as a sheaf of modules
on `X`. The ascription is what makes the additive structure on morphisms into it available. -/
def cokHomSheaf (f : Fin (d + 1) → Γ(X, ⊤)) (M P : X.Modules) : X.Modules :=
  SheafOfModules.moduleHomSheaf X.sheaf M (cokernel (lastDif f P))

/-- The curried form of `cokSource`: a morphism from the top Čech term into the sheaf-hom. -/
def cokCurried : prodTerm f N d ⟶ cokHomSheaf f M P :=
  SheafOfModules.bilinearCurry X.sheaf (cokSource f μ)

/-- **The curried pairing kills the last differential.** This is the commutation of the
pairing with the differential together with `cokernel.condition`, and it is what lets the
pairing descend to the cokernel. -/
theorem lastDif_comp_cokCurried : lastDif f N ≫ cokCurried f μ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun y => ?_)
  refine SheafOfModules.homSheafExt X.sheaf M (cokernel (lastDif f P)) (op V) fun W z => ?_
  have hres : (term f N d).presheaf.map W.unop.hom.op y =
      PresheafOfModules.restrictₛₗ (term f N d).val W.unop.hom.op y := rfl
  have hnat : PresheafOfModules.restrictₛₗ (prodTerm f N d).val W.unop.hom.op
        ((lastDif f N).app V y) =
      (lastDif f N).app W.unop.left ((term f N d).presheaf.map W.unop.hom.op y) := by
    rw [hres]
    exact (PresheafOfModules.restrictₛₗ_naturality_apply (lastDif f N).val W.unop.hom.op y).symm
  have hzero : (cokernel.π (lastDif f P)).app W.unop.left
      ((lastDif f P).app W.unop.left
        ((termPair f μ d).app (op W.unop.left) z
          ((term f N d).presheaf.map W.unop.hom.op y))) = 0 :=
    congrArg (fun φ : term f P d ⟶ cokernel (lastDif f P) => φ.app W.unop.left _)
      (cokernel.condition (lastDif f P))
  refine Eq.trans (SheafOfModules.homSheafApp_bilinearCurryHom X.sheaf (cokSource f μ) (op V)
    ((lastDif f N).app V y) W z) ?_
  refine Eq.trans (congrArg
    (fun w : Γ(prodTerm f N d, W.unop.left) => (cokSource f μ).app (op W.unop.left) w z)
    hnat) ?_
  exact Eq.trans (congrArg
    (fun w : Γ(prodTerm f P d, W.unop.left) =>
      (cokernel.π (lastDif f P)).app W.unop.left w)
    (termPair_dif f μ d W.unop.left z _)) hzero

/-- The descended morphism into the sheaf-hom, out of the cokernel of the last
differential. -/
def cokDesc : cokernel (lastDif f N) ⟶ cokHomSheaf f M P :=
  cokernel.desc (lastDif f N) (cokCurried f μ) (lastDif_comp_cokCurried f μ)

/-- **The pairing of `ℳ` with the cokernel of the last differential.** -/
def cokPair :
    Stacks.BilinearMap M.val (cokernel (lastDif f N)).val (cokernel (lastDif f P)).val :=
  (SheafOfModules.bilinearUncurry X.sheaf (cokDesc f μ)).flip

/-- **The descended pairing on a class.** Pairing with the class of a top-degree Čech cochain
is the class of the paired cochain. -/
theorem cokPair_cokernelπ (V : X.Opens) (m : Γ(M, V)) (x : Γ(prodTerm f N d, V)) :
    (cokPair f μ).app (op V) m ((cokernel.π (lastDif f N)).app V x) =
      (cokernel.π (lastDif f P)).app V (pairVal f μ d V m x) := by
  have hdesc : (cokDesc f μ).app V ((cokernel.π (lastDif f N)).app V x) =
      (cokCurried f μ).app V x :=
    congrArg (fun φ : prodTerm f N d ⟶ cokHomSheaf f M P => φ.app V x)
      (cokernel.π_desc (lastDif f N) (cokCurried f μ) (lastDif_comp_cokCurried f μ))
  refine Eq.trans (congrArg
    (fun α : (cokHomSheaf f M P).val.obj (op V) =>
      SheafOfModules.homSheafEval X.sheaf M (cokernel (lastDif f P)) (op V) α m) hdesc) ?_
  exact SheafOfModules.bilinearUncurry_curry_app X.sheaf (cokSource f μ) (op V) x m

/-! ### The pairing on the fraction cochain -/

/-- **The pairing on the fraction cochain.** Pairing a section of `ℳ` with the fraction
`s / (f₁ ⋯ f_c)` gives the fraction `μ(m, s) / (f₁ ⋯ f_c)`: the pairing is linear in its
second argument, so the scalar `Ring.inverse (∏ f)` passes through it. -/
theorem pairVal_fractionHom (V : X.Opens) (m : Γ(M, V)) (s : Γ(N, V)) :
    pairVal f μ d V m ((fractionHom f N d).app V s) =
      (fractionHom f P d).app V (μ.app (op V) m s) := by
  refine (secIso f P d V).injective (funext fun q => ?_)
  refine Eq.trans (congrFun (secIso_pairVal f μ d V m _) q) ?_
  refine Eq.trans ?_ (fractionHom_secIso f P d V (μ.app (op V) m s) q).symm
  refine Eq.trans (congrArg
    (fun z => μ.app (op (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1))
      (M.presheaf.map (homOfLE (interLe f d q V)).op m) z)
    (fractionHom_secIso f N d V s q)) ?_
  rw [fractionCochain_apply]
  refine Eq.trans (μ.map_smul_right _ _ _ _) ?_
  refine Eq.trans ?_ (fractionCochain_apply f P d V (μ.app (op V) m s) q).symm
  exact congrArg _ (μ.naturality (homOfLE (interLe f d q V)).op m s).symm

/-! ### The pairing on the local cohomology sheaf -/

variable [N.IsQuasicoherent] [P.IsQuasicoherent]
variable {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
  (hTsub : T ⊆ equationsClosedSet f)

/-- **The pairing of `ℳ` with the degree-`c` local cohomology sheaf along the equations**,
`ℳ × i_*ℋ^c_T(𝒩) ⟶ i_*ℋ^c_T(𝒫)`: the pairing on the cokernels of the last differentials,
transported along the identification of [Stacks, Tag 0G7M].

The two inclusions say that `T` is the common zero locus of the equations, which is the closed
subset the tags are about; the identification of the cokernel with `i_*ℋ^c_T` is an
isomorphism exactly then, by `Stacks.Perfect.SupportedFraction.isIso_cokernelLastDifToSupport`,
and a pairing on the target has to be transported back across it. -/
def supportPair :
    Stacks.BilinearMap M.val (supportCohomologySheaf hT N ((d + 1 : ℕ) : ℤ)).val
      (supportCohomologySheaf hT P ((d + 1 : ℕ) : ℤ)).val :=
  haveI : IsIso (cokernelLastDifToSupport f N hT hTf) :=
    isIso_cokernelLastDifToSupport f N hT hTf hTsub
  ((cokPair f μ).compRight (inv (cokernelLastDifToSupport f N hT hTf)).val).postcomp
    (cokernelLastDifToSupport f P hT hTf).val

/-- The class map of [Stacks, Tag 0G7Q] read on the coefficient module, on sections: the class
in `i_*ℋ^c_T(ℱ)` of a section is the image of the class of its fraction cochain. -/
theorem supportedFractionSource_app (F : X.Modules) [F.IsQuasicoherent] (V : X.Opens)
    (s : Γ(F, V)) :
    (supportedFractionSource f F hT hTf).app V s =
      (cokernelLastDifToSupport f F hT hTf).app V
        ((cokernel.π (lastDif f F)).app V ((fractionHom f F d).app V s)) :=
  congrArg
    (fun z : Γ(cokernel (lastDif f F), V) =>
      (cokernelLastDifToSupport f F hT hTf).app V z)
    (supportedFractionClass_mk f F V s)

/-- The pairing, read through the identification of Stacks 0G7M, sends a class to the class of
the paired Čech cochain. -/
private theorem supportPair_app_cokernelπ (V : X.Opens) (m : Γ(M, V))
    (x : Γ(prodTerm f N d, V)) :
    (supportPair f μ hT hTf hTsub).app (op V) m
        ((cokernelLastDifToSupport f N hT hTf).app V ((cokernel.π (lastDif f N)).app V x)) =
      (cokernelLastDifToSupport f P hT hTf).app V
        ((cokernel.π (lastDif f P)).app V (pairVal f μ d V m x)) := by
  have : IsIso (cokernelLastDifToSupport f N hT hTf) :=
    isIso_cokernelLastDifToSupport f N hT hTf hTsub
  have hinv : (inv (cokernelLastDifToSupport f N hT hTf)).app V
      ((cokernelLastDifToSupport f N hT hTf).app V
        ((cokernel.π (lastDif f N)).app V x)) =
      (cokernel.π (lastDif f N)).app V x :=
    congrArg (fun φ : cokernel (lastDif f N) ⟶ cokernel (lastDif f N) => φ.app V _)
      (IsIso.hom_inv_id (cokernelLastDifToSupport f N hT hTf))
  refine Eq.trans (congrArg
    (fun z : Γ(cokernel (lastDif f P), V) =>
      (cokernelLastDifToSupport f P hT hTf).app V z)
    (congrArg (fun z : Γ(cokernel (lastDif f N), V) => (cokPair f μ).app (op V) m z) hinv)) ?_
  exact congrArg
    (fun z : Γ(cokernel (lastDif f P), V) =>
      (cokernelLastDifToSupport f P hT hTf).app V z) (cokPair_cokernelπ f μ V m x)

/-- **The pairing is compatible with the class map of [Stacks, Tag 0G7Q].** Pairing a local
section `m` of `ℳ` with the class of `s / (f₁ ⋯ f_c)` in `i_*ℋ^c_T(𝒩)` gives the class of
`μ(m, s) / (f₁ ⋯ f_c)` in `i_*ℋ^c_T(𝒫)`. -/
theorem supportPair_supportedFractionSource (V : X.Opens) (m : Γ(M, V)) (s : Γ(N, V)) :
    (supportPair f μ hT hTf hTsub).app (op V) m
        ((supportedFractionSource f N hT hTf).app V s) =
      (supportedFractionSource f P hT hTf).app V (μ.app (op V) m s) := by
  rw [supportedFractionSource_app f hT hTf N V s,
    supportedFractionSource_app f hT hTf P V (μ.app (op V) m s),
    supportPair_app_cokernelπ f μ hT hTf hTsub, pairVal_fractionHom]

/-! ### The pairing with a global first argument -/

omit [N.IsQuasicoherent] [P.IsQuasicoherent] in
/-- **Pairing with a global section of the first factor is the functorial action of the
multiplication morphism, already on the Čech terms.** For a global section `ω` of `ℳ` the
Čech-term pairing is `prodMap` of the morphism `𝒩 ⟶ 𝒫`, `t ↦ μ(ω, t)`. -/
theorem pairVal_eval (ω : M.val.sections) (p : ℕ) (V : X.Opens)
    (x : Γ(prodTerm f N p, V)) :
    pairVal f μ p V (ω.eval (op V)) x =
      (prodMap f (Stacks.Cohomology.rightMulHom μ.flip ω) p).app V x := by
  refine (secIso f P p V).injective (funext fun q => ?_)
  refine Eq.trans (congrFun (secIso_pairVal f μ p V (ω.eval (op V)) x) q) ?_
  refine Eq.trans ?_ (prodMap_section f (Stacks.Cohomology.rightMulHom μ.flip ω) p V x q).symm
  exact congrArg
    (fun z => μ.app (op (CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) q.1)) z
      (secIso f N p V x q))
    (PresheafOfModules.sections_property ω (homOfLE (interLe f p q V)).op)

/-- **The identification of Stacks 0G7M is natural in the coefficient module**, in the form
needed below: precomposed with the projection onto the cokernel of the last differential. -/
theorem cokernelπ_comp_cokernelLastDifToSupport_comp_map (φ : N ⟶ P) :
    cokernel.π (lastDif f N) ≫ cokernelLastDifToSupport f N hT hTf ≫
        supportCohomologySheafMap hT φ ((d + 1 : ℕ) : ℤ) =
      prodMap f φ d ≫ cokernel.π (lastDif f P) ≫ cokernelLastDifToSupport f P hT hTf := by
  have h1 := comp_cokernelπ_comp_cokernelLastDifToSupport f N hT hTf (𝟙 (prodTerm f N d))
  rw [Category.id_comp] at h1
  have h2 := comp_cokernelπ_comp_cokernelLastDifToSupport f P hT hTf (prodMap f φ d)
  have h3 := homologyMap_cplxMap_comp_cechHomologyToSupport f φ hT hTf (d + 1)
  have h4 := cechCocycleClass_top_comp_homologyMap_cplxMap f φ (𝟙 (prodTerm f N d))
  rw [Category.id_comp] at h4
  rw [h2, ← Category.assoc, h1, Category.assoc, ← h3, ← Category.assoc, h4]

/-- **Pairing with a global section of the first factor is the canonical functorial action.**
For a global section `ω` of `ℳ`, pairing with `ω` on `i_*ℋ^c_T(𝒩)` is `i_*ℋ^c_T` applied to
the morphism `𝒩 ⟶ 𝒫`, `t ↦ μ(ω, t)`.

This is what makes the pairing canonical. It is built from a chosen family of equations, and
nothing in its construction says that another family would give the same map; but on a global
first argument it agrees with `Stacks.Perfect.SupportedFraction.supportCohomologySheafMap`, the
functorial action of the local cohomology sheaf, in which no family of equations occurs. -/
theorem rightMulHom_flip_supportPair (ω : M.val.sections) :
    Stacks.Cohomology.rightMulHom (supportPair f μ hT hTf hTsub).flip ω =
      supportCohomologySheafMap hT (Stacks.Cohomology.rightMulHom μ.flip ω)
        ((d + 1 : ℕ) : ℤ) := by
  have : IsIso (cokernelLastDifToSupport f N hT hTf) :=
    isIso_cokernelLastDifToSupport f N hT hTf hTsub
  refine (cancel_epi (cokernel.π (lastDif f N) ≫ cokernelLastDifToSupport f N hT hTf)).mp ?_
  refine Eq.trans ?_ (Eq.trans (Category.assoc _ _ _)
    (cokernelπ_comp_cokernelLastDifToSupport_comp_map f hT hTf
      (Stacks.Cohomology.rightMulHom μ.flip ω))).symm
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  refine Eq.trans (supportPair_app_cokernelπ f μ hT hTf hTsub V (ω.eval (op V)) x) ?_
  exact congrArg
    (fun z : Γ(prodTerm f P d, V) =>
      (cokernelLastDifToSupport f P hT hTf).app V ((cokernel.π (lastDif f P)).app V z))
    (pairVal_eval f μ ω d V x)

end Stacks.Perfect.CechPairing

end
