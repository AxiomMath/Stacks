module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCocycleBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcision
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassSpellings

/-!
# The class map of Tag 0G7Q is local, for any number of equations

[Stacks, Tag 0G7U] says that the canonical map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] is local.
The repository proves it for an open immersion in
`Stacks.Gysin.map_supportedFractionSource_comp_supportCohomologyRestrictIso`, and only for
`c = d + 1`: that statement is about
`Stacks.Perfect.SupportedFraction.supportedFractionSource`, which factors through the cokernel of
`Stacks.Perfect.SupportedFraction.lastDif` — the differential of the extended alternating Čech
complex into its *top* degree — and an empty family of equations gives a complex with only
degree `0` and no such differential.

This file proves it for **every** `c`, zero included, about
`Stacks.Perfect.FractionClass.classMapToSupport`, which is the same map built without a top
differential.  It is the locality the `c = 0` case of [Stacks, Tag 0G86] needs: the overlap
agreement of two equation charts reduces to it, and at conormal rank `0` a chart carries an empty
family of equations.

## Main results

* `Stacks.Gysin.restrictCplxIso_hom_f_zero_eq_id`: in degree `0` the comparison of the restricted
  Čech complex with the Čech complex of the restricted equations is the identity.
* `Stacks.Gysin.map_fracTermTop_comp_restrictCplxIso_zero`: for an **empty** family the fraction
  in the top term is carried to the fraction in the top term.
* `Stacks.Gysin.map_classMap_comp_cechHomologyImmersionIso`: **base change of the fraction class
  of [Stacks, Tag 0G7Q] along an open immersion**, for any number of equations, given that base
  change for its numerator.
* `Stacks.Gysin.map_classMapToSupport_comp_supportCohomologyRestrictIso`: **[Stacks, Tag 0G7U] for
  an open immersion, for any number of equations**, on
  `Stacks.Perfect.FractionClass.classMapToSupport`.
* `Stacks.Gysin.classMapToSupport_naturality`: **[Stacks, Tag 0G7T] for any number of
  equations** — functoriality in the coefficient module.
* `Stacks.Gysin.classMapToSupport_comp_eqToHom`: its transport along an identification of the
  zero locus of the equations with a given closed subset.

## Implementation notes

**Why the numerator's base change is a hypothesis and not a lemma here.**  The fraction in the
top term, `Stacks.Perfect.FractionClass.fracTermTop`, is defined by cases on the number of
equations: for `c = 0` it is the identity of the coefficient module, the denominator being the
empty product `1`, and for `c = d + 1` it is the fraction with the product of the equations as
denominator.  Its base change therefore has two cases with nothing in common, and only the first
is proved here, because only the first is what `c = 0` needs — the `c = d + 1` case is already
available downstream through `supportedFractionSource`.  Taking it as a hypothesis keeps the two
results above general in `c` rather than stating them twice.

**Why the positive-degree cocycle base change cannot be used.**
`Stacks.Gysin.map_cechCocycleClass_comp_cechHomologyImmersionIso` states the base change for a
class in degree `p + 1` represented by a cocycle in
`Stacks.Perfect.SupportedFraction.prodTerm`; in degree `0` the term of the complex is the
coefficient module instead.  What is used here is
`Stacks.Gysin.map_cocycleClass_comp_cechHomologyImmersionIso`, the degree-generic form, of which
that one is the positive-degree reading.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.CechDerivedSupportImmersion
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.FractionClass
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Gysin

variable {X X' : Scheme.{u}} (g : X' ⟶ X) [IsOpenImmersion g]

/-- **In degree `0` the comparison of the restricted extended alternating Čech complex with the
Čech complex of the restricted equations is the identity.**

`Stacks.Perfect.CechDerivedSupportImmersion.restrictCplxIso_hom_f_zero` reads that comparison in
degree `0` as the two identifications of the degree-`0` term with the coefficient module, and
those identifications are `Iso.refl`: the degree-`0` term of the complex *is* the coefficient
module.  The number of equations is arbitrary; nothing below degree `1` depends on it. -/
theorem restrictCplxIso_hom_f_zero_eq_id {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules) :
    (restrictCplxIso g e F).hom.f 0 = 𝟙 ((Scheme.Modules.restrictFunctor g).obj F) := by
  rw [restrictCplxIso_hom_f_zero]
  rfl

/-- **For an empty family of equations the fraction in the top term is carried to the fraction in
the top term.**  Both are the identity of the coefficient module — the denominator is the empty
product `1`, so the fraction is the section itself — and the comparison of the complexes is the
identity in degree `0` by `restrictCplxIso_hom_f_zero_eq_id`. -/
theorem map_fracTermTop_comp_restrictCplxIso_zero (e : Fin 0 → Γ(X, ⊤)) (F : X.Modules) :
    (Scheme.Modules.restrictFunctor g).map (fracTermTop e F) ≫
        (restrictCplxIso g e F).hom.f 0 =
      fracTermTop (fun j => g.appTop (e j)) ((Scheme.Modules.restrictFunctor g).obj F) := by
  rw [restrictCplxIso_hom_f_zero_eq_id]
  change (Scheme.Modules.restrictFunctor g).map (𝟙 F) ≫ _ = 𝟙 _
  rw [(Scheme.Modules.restrictFunctor g).map_id, Category.id_comp]

/-- **Base change of the fraction class of [Stacks, Tag 0G7Q] along an open immersion, for any
number of equations.**  The restriction along `g` of the class of the fraction
`s / (f₁ ⋯ f_c)` in the degree-`c` cohomology of the extended alternating Čech complex, read
across `Stacks.Gysin.cechHomologyImmersionIso`, is the class of the fraction of the restricted
equations.

`Stacks.Perfect.FractionClass.classMap` is by definition the class of
`Stacks.Perfect.FractionClass.fracTermTop` as a degree-`c` cocycle — the differential out of the
top degree vanishes, by `Stacks.Perfect.FractionClass.d_top_eq_zero`, for every `c` — so this is
`map_cocycleClass_comp_cechHomologyImmersionIso` at that cocycle, together with the hypothesis
that the cocycle itself is carried across.  The hypothesis is
`map_fracTermTop_comp_restrictCplxIso_zero` at `c = 0`; see the module's implementation notes for
why it is a hypothesis. -/
theorem map_classMap_comp_cechHomologyImmersionIso {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (hfrac : (Scheme.Modules.restrictFunctor g).map (fracTermTop f F) ≫
        (restrictCplxIso g f F).hom.f c =
      fracTermTop (fun j => g.appTop (f j)) ((Scheme.Modules.restrictFunctor g).obj F)) :
    (Scheme.Modules.restrictFunctor g).map (classMap f F) ≫
        (cechHomologyImmersionIso g f F c).hom =
      classMap (fun j => g.appTop (f j)) ((Scheme.Modules.restrictFunctor g).obj F) := by
  have hu' : fracTermTop (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) ≫
      (cplx (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F)).d c (c + 1) = 0 := by
    rw [d_top_eq_zero]
    exact comp_zero
  have hu : ((Scheme.Modules.restrictFunctor g).map (fracTermTop f F) ≫
        (restrictCplxIso g f F).hom.f c) ≫
      (cplx (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F)).d c (c + 1) = 0 := by
    rw [hfrac]
    exact hu'
  exact Eq.trans
    (map_cocycleClass_comp_cechHomologyImmersionIso g f F c (fracTermTop f F)
      (by rw [d_top_eq_zero]; exact comp_zero) hu)
    (cocycleClass_congr (CochainComplex.next ℕ c) hu hu' hfrac)

/-- Composing two carried factors, at a variable category. -/
private theorem chaseTwo {V : Type*} [Category* V] {o₁ o₂ o₃ o₄ o₅ : V}
    (a : o₁ ⟶ o₂) (b : o₂ ⟶ o₃) (d : o₃ ⟶ o₄) (r : o₂ ⟶ o₅) (s : o₅ ⟶ o₄) (t : o₁ ⟶ o₅)
    (hA : b ≫ d = r ≫ s) (hB : a ≫ r = t) : (a ≫ b) ≫ d = t ≫ s := by
  rw [Category.assoc, hA, ← Category.assoc, hB]

/-- **Stacks Project, Tag 0G7U for an open immersion, for any number of equations: the class map
of [Stacks, Tag 0G7Q] is local.**  The restriction along `g` of the canonical map
`ℱ ⟶ i_*ℋ ᶜ_T(ℱ)`, followed by the excision isomorphism of [Stacks, Tag 0G78] on degree-`c`
cohomology sheaves, is the canonical map of the restricted equations with coefficients in `g^*ℱ`.

This is `map_supportedFractionSource_comp_supportCohomologyRestrictIso` with the `c = d + 1`
removed.  Both factors of `Stacks.Perfect.FractionClass.classMapToSupport` are carried: the
cohomology class of the fraction by `map_classMap_comp_cechHomologyImmersionIso`, and the
comparison of [Stacks, Tag 0G7L] in degree `c` by
`map_cechHomologyToSupport_comp_supportCohomologyOpenImmersionIso`, which is already stated for
any number of equations and any degree. -/
theorem map_classMapToSupport_comp_supportCohomologyRestrictIso {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (hT' : IsClosed (restrictClosedSubset g T))
    (hTf' : equationsClosedSet (fun j => g.appTop (f j)) ⊆ restrictClosedSubset g T)
    (hfrac : (Scheme.Modules.restrictFunctor g).map (fracTermTop f F) ≫
        (restrictCplxIso g f F).hom.f c =
      fracTermTop (fun j => g.appTop (f j)) ((Scheme.Modules.restrictFunctor g).obj F)) :
    (Scheme.Modules.restrictFunctor g).map (classMapToSupport f F hT hTf) ≫
        (supportCohomologyOpenImmersionIso g hT hT' (c : ℤ) F).hom =
      classMapToSupport (fun j => g.appTop (f j))
        ((Scheme.Modules.restrictFunctor g).obj F) hT' hTf' := by
  refine Eq.trans (congrArg (fun z => z ≫
      (supportCohomologyOpenImmersionIso g hT hT' (c : ℤ) F).hom)
    ((Scheme.Modules.restrictFunctor g).map_comp (classMap f F)
      (cechHomologyToSupport f F hT hTf c))) ?_
  exact chaseTwo _ _ _ _ _ _
    (map_cechHomologyToSupport_comp_supportCohomologyOpenImmersionIso
      g f F hT hTf hT' hTf' c)
    (map_classMap_comp_cechHomologyImmersionIso g f F hfrac)

/-! ### Functoriality in the coefficient module, and transport of the closed subset -/

/-- **For an empty family of equations the fraction in the top term is natural in the coefficient
module.**  It is then the identity of the coefficient module, and the degree-`0` component of the
induced map of Čech complexes is the morphism itself. -/
theorem fracTermTop_naturality_zero (f : Fin 0 → Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G) :
    fracTermTop f F ≫ (cplxMap f φ).f 0 = φ ≫ fracTermTop f G := by
  change 𝟙 F ≫ φ = φ ≫ 𝟙 G
  rw [Category.id_comp, Category.comp_id]

/-- **The fraction class of [Stacks, Tag 0G7Q] is natural in the coefficient module, for any
number of equations**, given that its numerator is.

Both sides are the class of a single cocycle — the numerator carried across by the induced map of
complexes — by `Stacks.Perfect.SupportedFraction.comp_cocycleClass` on the left and
`Stacks.Perfect.SupportedFraction.cocycleClass_comp_homologyMap` on the right; the hypothesis
identifies the two numerators.  See the module's implementation notes for why that hypothesis is
carried rather than proved. -/
theorem classMap_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules} (φ : F ⟶ G)
    (hfrac : fracTermTop f F ≫ (cplxMap f φ).f c = φ ≫ fracTermTop f G) :
    φ ≫ classMap f G = classMap f F ≫ HomologicalComplex.homologyMap (cplxMap f φ) c := by
  refine Eq.trans (comp_cocycleClass (K := cplx f G) (CochainComplex.next ℕ c)
    (fracTermTop f G) (by rw [d_top_eq_zero]; exact comp_zero) φ) ?_
  refine Eq.trans ?_ (cocycleClass_comp_homologyMap (cplxMap f φ) (CochainComplex.next ℕ c)
    (fracTermTop f F) (by rw [d_top_eq_zero]; exact comp_zero)).symm
  exact cocycleClass_congr _ _ _ hfrac.symm

/-- **Stacks Project, Tag 0G7T for any number of equations: the class map of [Stacks, Tag 0G7Q]
read on the coefficient module is natural in it.**

This is `Stacks.Perfect.SupportedFraction.supportedFractionSource_natural` with the `c = d + 1`
removed.  Its two steps are `classMap_naturality` and the naturality
`Stacks.Perfect.SupportedFraction.homologyMap_cplxMap_comp_cechHomologyToSupport` of the
comparison of [Stacks, Tag 0G7L] in degree `c`, which is already stated for any number of
equations. -/
theorem classMapToSupport_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T)
    (hfrac : fracTermTop f F ≫ (cplxMap f φ).f c = φ ≫ fracTermTop f G) :
    φ ≫ classMapToSupport f G hT hTf =
      classMapToSupport f F hT hTf ≫ (supportCohomologySheafFunctor hT (c : ℤ)).map φ := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun ψ => ψ ≫ cechHomologyToSupport f G hT hTf c)
    (classMap_naturality f φ hfrac)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun ψ => classMap f F ≫ ψ)
    (homologyMap_cplxMap_comp_cechHomologyToSupport f φ hT hTf c)) ?_
  exact (Category.assoc _ _ _).symm

/-- **Transport of the class map of [Stacks, Tag 0G7Q] along the identification of the zero locus
of the equations with a given closed subset, for any number of equations.**

This is `Stacks.Gysin.supportedFractionSource_comp_eqToHom` with the `c = d + 1` removed.
Substituting the closed subset reduces the statement to the reflexivity case, in which the
transport is the identity, the two proofs of closedness being then two proofs of one
proposition. -/
theorem classMapToSupport_comp_eqToHom {Y : Scheme.{u}} {c : ℕ} (g : Fin c → Γ(Y, ⊤))
    (F : Y.Modules) [F.IsQuasicoherent] {T : Set Y} (hT : IsClosed T)
    (hgT : equationsClosedSet g = T) {G : Y.Modules}
    (h : supportCohomologySheaf hT F (c : ℤ) ⟶ G) :
    classMapToSupport g F (isClosed_equationsClosedSet g) subset_rfl ≫
        eqToHom (supportCohomologySheaf_congr hgT (isClosed_equationsClosedSet g) hT
          (c : ℤ) F) ≫ h =
      classMapToSupport g F hT hgT.le ≫ h := by
  subst hgT
  have hproof : hT = isClosed_equationsClosedSet g := rfl
  subst hproof
  rw [eqToHom_refl, Category.id_comp]

end Stacks.Gysin

end
