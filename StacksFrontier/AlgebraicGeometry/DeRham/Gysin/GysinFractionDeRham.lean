module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamDifferential

/-!
# Differentiating the Gysin fraction, and the square of Stacks 0G85 for the Gysin formula

Let `π : X ⟶ S` be a morphism of schemes and let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global equations
with `c = n + 1`.  The class map `c_{f₁,…,f_c}` of [Stacks, Tag 0G7Q] carries a local section `s`
of a quasi-coherent module `ℱ` to the class of the fraction `s / (f₁ ⋯ f_c)`, a section of the top
term of the extended alternating Čech complex `ℱ^•` of [Stacks, Tag 0G7I], in
`i_*ℋ ᶜ_Z(ℱ)`.  The proof of [Stacks, Tag 0G85] says that applying `d` to
`(ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c) / (f₁ ⋯ f_c)` replaces `ω̃` by `d ω̃`, "which is clear", and that the
passage from a top-degree Čech cochain to `i_*ℋ ᶜ_Z(ℱ)` is functorial on **all** abelian sheaves
on `X`.

This file proves the first of those two assertions and reduces the square of [Stacks, Tag 0G85]
for the Gysin formula to the second.  The missing input the computation needed —
the sectionwise description of the fraction, which the division by a product of equations made
unavailable to a merely additive morphism — is supplied here.

## Main definitions

* `Stacks.Perfect.GysinFractionDeRham.gysinWedgePresheafHom` and
  `gysinNumeratorPresheafHom`: the wedge factor `ω ↦ ω ∧ d f₁ ∧ ⋯ ∧ d f_c` of the Gysin formula
  and the composite `ω ↦ d ω ∧ d f₁ ∧ ⋯ ∧ d f_c`, as morphisms of the underlying abelian
  presheaves on `X` with the target degree spelled as a natural number.
* `Stacks.Perfect.GysinFractionDeRham.cokernelLastDifToPushforward` and `topCechClass`: the
  identification `Coker(lastDif f ℱ) ≅ i_*ℋ ᶜ_Z(ℱ)` of [Stacks, Tag 0G7L] and
  [Stacks, Tag 0G7M] **in the spelling the Gysin map is built in**, and the class of a top-degree
  Čech cochain in `i_*ℋ ᶜ_Z(ℱ)`.
* `Stacks.Perfect.GysinFractionDeRham.TopCechClassAbelianNatural`: **the one statement still
  missing for [Stacks, Tag 0G85]** — that `topCechClass` is natural in an arbitrary morphism of
  the underlying abelian sheaves of the coefficient modules.  A proposition, proved nowhere.

## Main results

* `Stacks.Perfect.GysinFractionDeRham.secIso_fracTerm` and `fracTerm_eq_fractionHom`: **the
  sectionwise description of the fraction `s / (f₁ ⋯ f_c)` of [Stacks, Tag 0G7Q]** — on local
  sections it is multiplication of the restriction of `s` by the inverse of the restriction of the
  product of the equations, i.e. `Stacks.Perfect.SupportedFraction.fractionCochain`.  This
  identifies `Stacks.Perfect.FractionClass.fracTerm`, which the Gysin map is built from and which
  is defined by inverting multiplication by `f₁ ⋯ f_c` on the top Čech term, with
  `Stacks.Perfect.SupportedFraction.fractionHom`, which is defined sectionwise.  **No localized
  module is involved**: over an open set on which the product is a unit, dividing by it is
  multiplication by its inverse.
* `Stacks.Perfect.GysinFractionDeRham.d_smul_gysinWedgeHom_app` and
  `sectionsHom_d_smul_gysinWedgeHom`: the localized Leibniz rule
  `AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_of_mul_eq_one` restated with the wedge
  factor written as `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` and with the degree bookkeeping
  carried by `HomologicalComplex.XIsoOfEq`, which is the spelling the Čech complex reads it in.
* `Stacks.Perfect.GysinFractionDeRham.prodTermAbApp_fracTerm_of_smul` and
  `fracTerm_comm_prodTermPre_of_smul`: **the fraction of [Stacks, Tag 0G7Q] is natural in a
  morphism of the underlying abelian sheaves that commutes with dividing by the product of the
  equations.**  This is the general form of the computation: the fraction is *not* natural in an
  arbitrary additive morphism, and the hypothesis is exactly what repairs that.
* `Stacks.Perfect.GysinFractionDeRham.prodTermAbApp_fracTerm_gysinWedgeHom`,
  `gysinFraction_comm_prodTermPre` and `gysinFraction_comm_prodTermAb`: **the Čech-level square of
  [Stacks, Tag 0G85]** — on local sections, as a square of morphisms of abelian presheaves, and as
  a square of morphisms of abelian sheaves: the de Rham differential carries the Gysin fraction
  `(ω ∧ d f₁ ∧ ⋯ ∧ d f_c) / (f₁ ⋯ f_c)` to the Gysin fraction of `d ω`.  This is the "almost
  trivial calculation" of the source: step (iii) and the localized Leibniz rule together.
* `Stacks.Perfect.GysinFractionDeRham.classMap_eq_fracTerm_comp` and `formFractionClass_eq`:
  **the fraction class of [Stacks, Tag 0G7Q] factored through the top term of the Čech complex**,
  i.e. `AlgebraicGeometry.Scheme.Hom.formFractionClass = fracTerm ≫ topCechClass`.  This is what
  connects the Gysin map's construction, which goes through the degree-`c` homology of the complex
  and `Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso`, to the Čech cochain the
  computation above takes place on.
* `Stacks.Perfect.GysinFractionDeRham.gysinFormulaCommutesWithDeRham_of_topCechClassNatural`:
  **the square of [Stacks, Tag 0G85] for the Gysin formula follows from
  `TopCechClassAbelianNatural`.**  A reduction, not a proof.

## Implementation notes

**`AlgebraicGeometry.Scheme.Hom.FormFractionClassCommutesWithDeRham` is false, and that is why
the reduction here goes through the Gysin formula and not through the class map alone.**  That
proposition asserts that the class map `c_{f₁,…,f_c}` by itself commutes with `d`.  It does not:
by the Leibniz rule
`d(s / (f₁ ⋯ f_c)) = d(s) / (f₁ ⋯ f_c) - s · d(f₁ ⋯ f_c) / (f₁ ⋯ f_c)²`,
and the error term does not vanish for a general numerator.  Taking `X = 𝔸¹_k = Spec k[t]`,
`S = Spec k`, one equation `f₁ = t`, so `Z = {0}` and `c = 1`, and `q = 0`: the left-hand side of
that proposition sends the global section `1` of `Ω⁰_{X/S} = 𝒪_X` to the class of
`d(1/t) = -dt/t²` in `ℋ ¹_Z(Ω¹_{X/S}) = Ω¹(X_t)/Ω¹(X)`, which is nonzero, while the right-hand
side sends it to `c_{f₁}(d 1) = 0`.  The error term is killed only *after* the wedge with
`d f₁ ∧ ⋯ ∧ d f_c`, because `d(f₁ ⋯ f_c)` is a sum of multiples of the `d f_j` and each already
occurs in the wedge — that is
`AlgebraicGeometry.SheafOfModules.formProduct_exactOne_prod_prodDegOne_eq_zero`, and it is
exactly what `AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_of_mul_eq_one` consumes.  So the
hypothesis of
`AlgebraicGeometry.Scheme.Hom.gysinFormulaCommutesWithDeRham_of_formFractionClass` is unprovable
and that reduction, while true, cannot be used;
`gysinFormulaCommutesWithDeRham_of_topCechClassNatural` replaces it with a hypothesis that
concerns the comparison of [Stacks, Tag 0G7L] alone and in which no differential occurs.

**Carried hypotheses.**  `secIso_fracTerm`, `fracTerm_eq_fractionHom`,
`prodTermAbApp_fracTerm_of_smul` and `fracTerm_comm_prodTermPre_of_smul` carry nothing beyond a
nonempty family of equations, written `Fin (n + 1)`; in particular no quasi-coherence and no
hypothesis on the coefficient module.  `d_smul_gysinWedgeHom_app` and
`sectionsHom_d_smul_gysinWedgeHom` carry a one-sided inverse `v` of the restriction of
`f₁ ⋯ f_c` to the open set in question, exactly as
`AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_of_mul_eq_one` does, and no hypothesis on the
equations: they need not be a regular sequence and need not cut out a subscheme of the expected
codimension.  `cokernelLastDifToPushforward`, `topCechClass`, `formFractionClass_eq` and
everything in the final section carry quasi-coherence of the coefficient module, which is where
[Stacks, Tag 0G7M] enters; for the de Rham terms that is a theorem,
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms`, declared as a local
instance.  The closed subset is specialised throughout to the common zero locus of the equations,
which is a specialisation and not a hypothesis.

**Why the degree spellings are named.**  The target of
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` is `Ω^{(p : ℤ) + (c : ℤ)}` while the de Rham
differential and the Čech fraction read that term as `Ω^{((p + c : ℕ) : ℤ)}`.  The two are equal
by unfolding `Int.add`, but a statement mixing them forces the kernel to descend through that
conversion inside every subterm of `prodTerm` and `secIso`, which does not terminate in the
allotted budget.  `gysinWedgePresheafHom` and `gysinNumeratorPresheafHom` fix the nat-cast
spelling once, so that no later statement contains both.  For the same reason the two general
lemmas `prodTermAbApp_fracTerm_of_smul` and `fracTerm_comm_prodTermPre_of_smul` are stated for
abstract modules and abstract morphisms of their underlying abelian presheaves and instantiated
once; and `reassoc₅` performs in an abstract category a reassociation that the `Category.assoc`
rewrite does not fire on here.

**No declaration here carries a `@[stacks ...]` attribute.**  The Čech-level square is the
calculation of [Stacks, Tag 0G85], but the square of that tag is not proved: see
`TopCechClassAbelianNatural`.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.GysinFractionDeRham

/-- Reassociation of a fivefold composite.  Stated for an abstract category because the
associativity rewrite does not fire on the composites of `X.Modules` occurring below, whose
sources and targets are spelled through several different definitions of the same object. -/
private theorem reassoc₅ {C : Type*} [Category* C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) (e : F ⟶ G) :
    ((a ≫ b ≫ c) ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

variable {X : Scheme.{u}}

section Fraction

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) (F : X.Modules)

/-- The product of the equations indexed by an increasing `(n+1)`-tuple of indices of
`Fin (n+1)` is the product of all the equations: a strictly monotone self-map of a finite linear
order is bijective. -/
public theorem prod_ordIndex (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    ∏ k, f (t.1 k) = ∏ i, f i :=
  Fintype.prod_bijective t.1 (Finite.injective_iff_bijective.mp t.2.injective) _ _ fun _ => rfl

/-- The product of the equations restricts to a unit on the intersection of the basic opens of
an increasing tuple of equations inside `V`. -/
private theorem isUnit_map_prod_inter (V : X.Opens)
    (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    IsUnit (X.presheaf.map (homOfLE (show
      CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) t.1 ≤ ⊤ from le_top)).op
        (∏ i, f i)) := by
  rw [← prod_ordIndex f t]
  exact SupportedFraction.isUnit_prodEquations f V n t

/-- **The sectionwise description of the fraction of [Stacks, Tag 0G7Q].** -/
public theorem secIso_fracTerm (V : X.Opens) (s : Γ(F, V))
    (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    secIso f F n V ((FractionClass.fracTerm f F).app V s) t =
      SupportedFraction.fractionCochain f F n V s t := by
  have hπ : (Pi.π (fun u : CechCochains.OrdIndex (I := Fin (n + 1)) n =>
        restrictedModule f F n u) t).app V ((FractionClass.fracTerm f F).app V s) =
      (FractionClass.fracFactor f F t).app V s := by
    rw [← comp_app_apply, FractionClass.fracTerm_comp_π]
  have hmul := congrArg (fun ψ : F ⟶ restrictedModule f F n t => ψ.app V s)
    (FractionClass.fracFactor_comp_smulHom f F t)
  simp only [comp_app_apply, FractionClass.smulHom_app_apply] at hmul
  have hkey := congrArg (restrictedModuleSection f F n t V) hmul
  rw [SupportedFraction.restrictedModuleSection_smul, augR_section,
    SupportedFraction.ringMap_collapse (homOfLE (show V ≤ ⊤ from le_top))
      (homOfLE (interLe f n t V))
      (homOfLE (show CechCochains.inter (fun i => V ⊓ X.basicOpen (f i)) t.1 ≤ ⊤ from le_top))]
    at hkey
  rw [secIso_apply, hπ, SupportedFraction.fractionCochain_apply, prod_ordIndex, ← hkey,
    SupportedFraction.ringInverse_smul_smul (isUnit_map_prod_inter f V t)]

/-- **The fraction of [Stacks, Tag 0G7Q] is the fraction cochain.** -/
public theorem fracTerm_eq_fractionHom :
    FractionClass.fracTerm f F = SupportedFraction.fractionHom f F n := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine (secIso f F n V).injective (funext fun t => ?_)
  rw [secIso_fracTerm, SupportedFraction.fractionHom_secIso]

end Fraction

/-! ### Differentiating the Gysin fraction -/

section Wedge

variable {S : Scheme.{u}}

open AlgebraicGeometry.Scheme.Hom

/-- The canonical isomorphism between two terms of the de Rham complex of equal degree acts
trivially on local sections.  This restates the private helper `XIsoOfEq_app_eq` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/LocalizedLeibniz.lean`. -/
private theorem deRham_XIsoOfEq_app_eq (π : X ⟶ S) {m n : ℕ} (h : m = n) (U : X.Opensᵒᵖ)
    (x : (relativeDifferentialForms π (m : ℤ)).val.obj U)
    (y : (relativeDifferentialForms π (n : ℤ)).val.obj U) (hxy : HEq x y) :
    ((deRhamComplex π).XIsoOfEq h).hom.val.app U x = y := by
  subst h
  cases eq_of_heq hxy
  rw [HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- **Differentiating the Gysin fraction differentiates its numerator alone**, in the spelling
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` of the wedge factor and with the degree bookkeeping
carried by `HomologicalComplex.XIsoOfEq`.  This is
`AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_of_mul_eq_one` restated. -/
public theorem d_smul_gysinWedgeHom_app (π : X ⟶ S) {m : ℕ} (f : Fin m → Γ(X, ⊤)) (p : ℕ)
    (V : X.Opens) (v : Γ(X, V))
    (hgv : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (∏ j, f j) * v = 1)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V))
    (α : Γ(relativeDifferentialForms π ((p + m : ℕ) : ℤ), V))
    (hα : (gysinWedgeHom π f (p : ℤ)).app V ω = α)
    (β : Γ(relativeDifferentialForms π ((p + m + 1 : ℕ) : ℤ), V))
    (hβ : ((deRhamComplex π).XIsoOfEq (show p + 1 + m = p + m + 1 by omega)).hom.val.app (op V)
        ((gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)).app V
          (((deRhamComplex π).d p (p + 1)).val.app (op V) ω)) = β) :
    ((deRhamComplex π).d (p + m) (p + m + 1)).val.app (op V) (v • α) = v • β := by
  subst hα
  subst hβ
  refine Eq.trans (d_smul_equationsWedge_of_mul_eq_one π f p (op V) _ v rfl hgv ω) ?_
  refine congrArg (fun z : Γ(relativeDifferentialForms π ((p + m + 1 : ℕ) : ℤ), V) => v • z) ?_
  exact (deRham_XIsoOfEq_app_eq π (show p + 1 + m = p + m + 1 by omega) (op V) _ _
    (AlgebraicGeometry.SheafOfModules.reindexForm_heq (deRhamAlgebras π)
      (show p + 1 + m = p + m + 1 by omega) (op V) _).symm).symm

/-- Applying a composite of morphisms of abelian presheaves to a section. -/
private theorem sectionsHom_comp {F G H : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (χ : Scheme.Modules.presheaf G ⟶ Scheme.Modules.presheaf H) (V : X.Opens) (x : Γ(F, V)) :
    AbelianFraction.sectionsHom (ψ ≫ χ) V x =
      AbelianFraction.sectionsHom χ V (AbelianFraction.sectionsHom ψ V x) := rfl

/-- **The wedge factor of the Gysin formula as a morphism of the underlying abelian presheaves**,
with its target degree spelled as the natural number `p + c` rather than as a sum of integers:
that is the spelling in which the de Rham differential and the Čech fraction read it, and naming
the morphism here keeps the two spellings from ever meeting. -/
public def gysinWedgePresheafHom (π : X ⟶ S) {m : ℕ} (f : Fin m → Γ(X, ⊤)) (p : ℕ) :
    Scheme.Modules.presheaf (relativeDifferentialForms π (p : ℤ)) ⟶
      Scheme.Modules.presheaf (relativeDifferentialForms π ((p + m : ℕ) : ℤ)) :=
  Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f (p : ℤ))

/-- On local sections `gysinWedgePresheafHom` is the wedge with `d f₁ ∧ ⋯ ∧ d f_c`. -/
public theorem sectionsHom_gysinWedgePresheafHom (π : X ⟶ S) {m : ℕ} (f : Fin m → Γ(X, ⊤))
    (p : ℕ) (W : X.Opens) (y : Γ(relativeDifferentialForms π (p : ℤ), W)) :
    AbelianFraction.sectionsHom (gysinWedgePresheafHom π f p) W y =
      (gysinWedgeHom π f (p : ℤ)).app W y := rfl

/-- **The numerator of the Gysin formula in degree `p + 1`**, as a morphism of the underlying
abelian presheaves: differentiate, wedge with `d f₁ ∧ ⋯ ∧ d f_c`, and read the result in the
degree `p + c + 1` of the de Rham complex. -/
public def gysinNumeratorPresheafHom (π : X ⟶ S) {m : ℕ} (f : Fin m → Γ(X, ⊤)) (p : ℕ) :
    Scheme.Modules.presheaf (relativeDifferentialForms π (p : ℤ)) ⟶
      Scheme.Modules.presheaf (relativeDifferentialForms π ((p + m + 1 : ℕ) : ℤ)) :=
  deRhamDifferentialPresheafHom π p ≫ gysinWedgePresheafHom π f (p + 1) ≫
    deRhamReindexPresheafHom π (show p + 1 + m = p + m + 1 by omega)

/-- `d_smul_gysinWedgeHom_app` in the vocabulary of morphisms of abelian presheaves: dividing by
an invertible restriction of the product of the equations commutes with the de Rham differential
on the image of the Gysin wedge factor. -/
public theorem sectionsHom_d_smul_gysinWedgeHom (π : X ⟶ S) {m : ℕ} (f : Fin m → Γ(X, ⊤))
    (p : ℕ) (W : X.Opens) (v : Γ(X, W))
    (hv : X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (∏ j, f j) * v = 1)
    (y : Γ(relativeDifferentialForms π (p : ℤ), W)) :
    AbelianFraction.sectionsHom (deRhamDifferentialPresheafHom π (p + m)) W
        (v • AbelianFraction.sectionsHom (gysinWedgePresheafHom π f p) W y) =
      v • AbelianFraction.sectionsHom (gysinNumeratorPresheafHom π f p) W y :=
  d_smul_gysinWedgeHom_app π f p W v hv y _ rfl _ rfl

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))

/-- **The fraction of [Stacks, Tag 0G7Q] is natural in a morphism of the underlying abelian
sheaves that commutes with dividing by the product of the equations.**  The division by
`f₁ ⋯ f_c` is not natural in a merely additive morphism, so the hypothesis is exactly the
localized identity that makes it so over every open on which that product is invertible. -/
public theorem prodTermAbApp_fracTerm_of_smul {E F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (u : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf F)
    (w : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf G)
    (h : ∀ (W : X.Opens) (v : Γ(X, W)) (y : Γ(E, W)),
      X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (∏ j, f j) * v = 1 →
      AbelianFraction.sectionsHom ψ W (v • AbelianFraction.sectionsHom u W y) =
        v • AbelianFraction.sectionsHom w W y)
    (V : X.Opens) (x : Γ(E, V)) :
    AbelianFraction.prodTermAbApp f ψ n V
        ((FractionClass.fracTerm f F).app V (AbelianFraction.sectionsHom u V x)) =
      (FractionClass.fracTerm f G).app V (AbelianFraction.sectionsHom w V x) := by
  refine (secIso f G n V).injective (funext fun t => ?_)
  rw [AbelianFraction.secIso_prodTermAbApp, secIso_fracTerm f F, secIso_fracTerm f G,
    SupportedFraction.fractionCochain_apply, SupportedFraction.fractionCochain_apply,
    prod_ordIndex, ← AbelianFraction.sectionsHom_naturality,
    ← AbelianFraction.sectionsHom_naturality]
  exact h _ _ _ (Ring.mul_inverse_cancel _ (isUnit_map_prod_inter f V t))

/-- **The Čech-level square of [Stacks, Tag 0G85]**: the Gysin fraction
`(ω ∧ d f₁ ∧ ⋯ ∧ d f_c) / (f₁ ⋯ f_c)` is carried by the de Rham differential to the Gysin
fraction of `d ω`. -/
public theorem prodTermAbApp_fracTerm_gysinWedgeHom (π : X ⟶ S) (p : ℕ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    AbelianFraction.prodTermAbApp f (deRhamDifferentialPresheafHom π (p + (n + 1))) n V
        ((FractionClass.fracTerm f (relativeDifferentialForms π ((p + (n + 1) : ℕ) : ℤ))).app V
          (AbelianFraction.sectionsHom (gysinWedgePresheafHom π f p) V ω)) =
      (FractionClass.fracTerm f
            (relativeDifferentialForms π ((p + (n + 1) + 1 : ℕ) : ℤ))).app V
          (AbelianFraction.sectionsHom (gysinNumeratorPresheafHom π f p) V ω) :=
  prodTermAbApp_fracTerm_of_smul f (deRhamDifferentialPresheafHom π (p + (n + 1)))
    (gysinWedgePresheafHom π f p) (gysinNumeratorPresheafHom π f p)
    (fun W v y hv => sectionsHom_d_smul_gysinWedgeHom π f p W v hv y) V ω

end Wedge

/-! ### The class map of Stacks 0G7Q through the cokernel of the last Čech differential -/

section Cokernel

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))

/-- **The identification `Coker(lastDif f ℱ) ≅ i_*ℋ ᶜ_Z(ℱ)` in the spelling the Gysin map uses.**
It is the identification of the cokernel of the last Čech differential with the degree-`c`
cohomology of the extended alternating Čech complex, followed by the comparison of the two
constructions of that complex ([Stacks, Tag 0G7I]) and by [Stacks, Tag 0G7M]. -/
public def cokernelLastDifToPushforward (F : X.Modules) [F.IsQuasicoherent] :
    cokernel (SupportedFraction.lastDif f F) ⟶
      AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f F :=
  (SupportedFraction.cokernelLastDifIsoHomology f F).hom ≫
    HomologicalComplex.homologyMap (CechComparison.complexIso f F).inv (n + 1) ≫
      (CechLocalCohomology.pushforwardLocalCohomologyIso f F (n + 1)).inv

/-- **The class in `i_*ℋ ᶜ_Z(ℱ)` of a top-degree Čech cochain.**  Every section of the top term of
the extended alternating Čech complex is a cocycle, and this is its class. -/
public def topCechClass (F : X.Modules) [F.IsQuasicoherent] :
    prodTerm f F n ⟶ AlgebraicGeometry.Scheme.Hom.pushforwardLocalCohomology f F :=
  cokernel.π (SupportedFraction.lastDif f F) ≫ cokernelLastDifToPushforward f F

/-- **The fraction class of [Stacks, Tag 0G7Q] is the class of the fraction**, read through the
cokernel of the last Čech differential rather than through the degree-`c` homology. -/
public theorem classMap_eq_fracTerm_comp (F : X.Modules) :
    FractionClass.classMap f F =
      FractionClass.fracTerm f F ≫ cokernel.π (SupportedFraction.lastDif f F) ≫
        (SupportedFraction.cokernelLastDifIsoHomology f F).hom := by
  have hc : FractionClass.fracCycle f F =
      FractionClass.fracTerm f F ≫ (SupportedFraction.topCyclesIso f F).hom := by
    rw [← cancel_mono ((cplx f F).iCycles (n + 1)), FractionClass.fracCycle_comp_iCycles,
      Category.assoc, SupportedFraction.topCyclesIso_hom_iCycles]
    exact (Category.comp_id _).symm
  rw [SupportedFraction.cokernelπ_comp_cokernelLastDifIsoHomology,
    show FractionClass.classMap f F =
        FractionClass.fracCycle f F ≫ (cplx f F).homologyπ (n + 1) from rfl,
    hc, Category.assoc]

/-- **The fraction class of a differential form is the class of its Gysin fraction.**  This is
`AlgebraicGeometry.Scheme.Hom.formFractionClass` factored through the top term of the extended
alternating Čech complex, which is where the localized Leibniz rule lives. -/
public theorem formFractionClass_eq (π : X ⟶ S) (q : ℤ)
    [(AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q).IsQuasicoherent] :
    AlgebraicGeometry.Scheme.Hom.formFractionClass π f q =
      FractionClass.fracTerm f (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q) ≫
        topCechClass f (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q) := by
  have h0 : AlgebraicGeometry.Scheme.Hom.formFractionClass π f q =
      cokernel.π (FractionClass.equationsMap f
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q)) ≫
        FractionClass.quotientClassMapData f
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q) ≫
          (CechLocalCohomology.pushforwardLocalCohomologyIso f
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q) (n + 1)).inv := rfl
  rw [h0, ← Category.assoc
      (cokernel.π (FractionClass.equationsMap f
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q)))
      (FractionClass.quotientClassMapData f
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q))
      ((CechLocalCohomology.pushforwardLocalCohomologyIso f
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms π q) (n + 1)).inv),
    FractionClass.cokernelπ_comp_quotientClassMapData, classMap_eq_fracTerm_comp]
  simp only [topCechClass, cokernelLastDifToPushforward]
  exact reassoc₅ _ _ _ _ _

end Cokernel

/-! ### The square of Stacks 0G85 for the Gysin formula -/

section Assembly

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentialForms

open AlgebraicGeometry.Scheme.Hom
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)

variable {S : Scheme.{u}} {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))

/-- The underlying abelian-sheaf morphism of the Gysin wedge factor is
`gysinWedgePresheafHom`. -/
private theorem abelianSheaf_map_gysinWedgeHom (π : X ⟶ S) (p : ℕ) :
    (abelianSheaf X).map (gysinWedgeHom π f (p : ℤ)) = abHom (gysinWedgePresheafHom π f p) := rfl

/-- The right-hand composite of the square of [Stacks, Tag 0G85] is the numerator of the Gysin
formula in degree `p + 1`. -/
private theorem abHom_gysinNumeratorPresheafHom (π : X ⟶ S) (p : ℕ) :
    abHom (deRhamDifferentialPresheafHom π p) ≫
        abHom (Scheme.Modules.Hom.mapPresheaf (gysinWedgeHom π f ((p + 1 : ℕ) : ℤ)) ≫
          deRhamReindexPresheafHom π (show p + 1 + (n + 1) = p + (n + 1) + 1 by omega)) =
      abHom (gysinNumeratorPresheafHom π f p) := rfl

/-- `prodTermAbApp_fracTerm_of_smul` as an equality of morphisms of abelian presheaves. -/
public theorem fracTerm_comm_prodTermPre_of_smul {E F G : X.Modules}
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
    (u : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf F)
    (w : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf G)
    (h : ∀ (W : X.Opens) (v : Γ(X, W)) (y : Γ(E, W)),
      X.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (∏ j, f j) * v = 1 →
      AbelianFraction.sectionsHom ψ W (v • AbelianFraction.sectionsHom u W y) =
        v • AbelianFraction.sectionsHom w W y) :
    u ≫ Scheme.Modules.Hom.mapPresheaf (FractionClass.fracTerm f F) ≫
        AbelianFraction.prodTermPre f ψ n =
      w ≫ Scheme.Modules.Hom.mapPresheaf (FractionClass.fracTerm f G) := by
  refine NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_))
  exact prodTermAbApp_fracTerm_of_smul f ψ u w h U.unop x

/-- **The Čech-level square of [Stacks, Tag 0G85] as a square of morphisms of abelian
presheaves.** -/
public theorem gysinFraction_comm_prodTermPre (π : X ⟶ S) (p : ℕ) :
    gysinWedgePresheafHom π f p ≫
        Scheme.Modules.Hom.mapPresheaf (FractionClass.fracTerm f
          (relativeDifferentialForms π ((p + (n + 1) : ℕ) : ℤ))) ≫
          AbelianFraction.prodTermPre f (deRhamDifferentialPresheafHom π (p + (n + 1))) n =
      gysinNumeratorPresheafHom π f p ≫
        Scheme.Modules.Hom.mapPresheaf (FractionClass.fracTerm f
          (relativeDifferentialForms π ((p + (n + 1) + 1 : ℕ) : ℤ))) :=
  fracTerm_comm_prodTermPre_of_smul f (deRhamDifferentialPresheafHom π (p + (n + 1)))
    (gysinWedgePresheafHom π f p) (gysinNumeratorPresheafHom π f p)
    (fun W v y hv => sectionsHom_d_smul_gysinWedgeHom π f p W v hv y)

/-- **The Čech-level square of [Stacks, Tag 0G85] as a square of morphisms of abelian
sheaves.** -/
public theorem gysinFraction_comm_prodTermAb (π : X ⟶ S) (p : ℕ) :
    abHom (gysinWedgePresheafHom π f p) ≫
        abHom (Scheme.Modules.Hom.mapPresheaf (FractionClass.fracTerm f
          (relativeDifferentialForms π ((p + (n + 1) : ℕ) : ℤ)))) ≫
          AbelianFraction.prodTermAb f (deRhamDifferentialPresheafHom π (p + (n + 1))) n =
      abHom (gysinNumeratorPresheafHom π f p) ≫
        abHom (Scheme.Modules.Hom.mapPresheaf (FractionClass.fracTerm f
          (relativeDifferentialForms π ((p + (n + 1) + 1 : ℕ) : ℤ)))) :=
  congrArg (abHom (F := relativeDifferentialForms π (p : ℤ))
      (G := prodTerm f (relativeDifferentialForms π ((p + (n + 1) + 1 : ℕ) : ℤ)) n))
    (gysinFraction_comm_prodTermPre f π p)

/-- **The one statement still missing for [Stacks, Tag 0G85]**: the class in `i_*ℋ ᶜ_Z(ℱ)` of a
top-degree Čech cochain is natural in an arbitrary morphism of the **underlying abelian sheaves**
of the coefficient modules, not merely in an `𝒪_X`-linear one.

This is the clause the source states as "the map onto `i_*ℋ ᶜ_Z(ℱ)` appearing in the construction
of `c_{f₁,…,f_c}` is well defined and functorial on the category of all abelian sheaves on `X`",
whose `𝒪_X`-linear case is
`Stacks.Perfect.GysinAbelianSquare.cokernelLastDifToSupport_abelian_square_mapPresheaf`.  It is a
statement about the comparison of [Stacks, Tag 0G7L] and [Stacks, Tag 0G7M] alone: no differential
and no wedge occurs in it.  Nothing in this file proves it; it is proved by
`Stacks.Perfect.SupportedEndoForgetDegreewise.topCechClassAbelianNatural`. -/
public def TopCechClassAbelianNatural {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) : Prop :=
  (abelianSheaf X).map (topCechClass f F) ≫
      GysinAbelianSquare.gysinTargetAbelianMap f (abHom ψ) =
    AbelianFraction.prodTermAb f ψ n ≫ (abelianSheaf X).map (topCechClass f G)

/-- **The comparison square of [Stacks, Tag 0G85] for the Gysin formula follows from the
naturality of the class map of [Stacks, Tag 0G7Q] in an arbitrary morphism of abelian sheaves.**

Everything else in the source's proof is discharged here: step (iii) is the commutation of the
wedge factor with `d`, and step (ii-b) is the localized Leibniz rule, both of them folded into the
Čech-level square `gysinFraction_comm_prodTermPre`; the passage from the Čech cochain to
`i_*ℋ ᶜ_Z` is `formFractionClass_eq`.  What remains is exactly
`TopCechClassAbelianNatural`, which is a statement about the comparison of
[Stacks, Tag 0G7L] and nothing else.

This is a reduction and not in itself a proof of [Stacks, Tag 0G85].  Its hypothesis is discharged
by `Stacks.Perfect.SupportedEndoForgetDegreewise.topCechClassAbelianNatural`, which is what makes
`Stacks.Perfect.SupportedEndoForgetDegreewise.gysinFormulaCommutesWithDeRham` unconditional. -/
public theorem gysinFormulaCommutesWithDeRham_of_topCechClassNatural (π : X ⟶ S) (p : ℕ)
    (hnat : TopCechClassAbelianNatural f (deRhamDifferentialPresheafHom π (p + (n + 1)))) :
    GysinFormulaCommutesWithDeRham π f p := by
  have hsq := gysinFraction_comm_prodTermAb f π p
  simp only [TopCechClassAbelianNatural] at hnat
  simp only [GysinFormulaCommutesWithDeRham, deRhamDifferentialAbHom, gysinTargetDeRhamMap]
  rw [show gysinFormulaHom π f (p : ℤ) = gysinWedgeHom π f (p : ℤ) ≫
        formFractionClass π f ((p + (n + 1) : ℕ) : ℤ) from rfl,
    formFractionClass_eq, formFractionClass_eq, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, hnat, abelianSheaf_map_gysinWedgeHom,
    AbelianFraction.abelianSheaf_map (FractionClass.fracTerm f
      (relativeDifferentialForms π ((p + (n + 1) : ℕ) : ℤ))),
    AbelianFraction.abelianSheaf_map (FractionClass.fracTerm f
      (relativeDifferentialForms π ((p + (n + 1) + 1 : ℕ) : ℤ))),
    ← Category.assoc, ← Category.assoc, Category.assoc (abHom (gysinWedgePresheafHom π f p)),
    hsq, Category.assoc (abHom (gysinNumeratorPresheafHom π f p)),
    ← Category.assoc (abHom (deRhamDifferentialPresheafHom π p)),
    abHom_gysinNumeratorPresheafHom]

end Assembly

end Stacks.Perfect.GysinFractionDeRham

end
