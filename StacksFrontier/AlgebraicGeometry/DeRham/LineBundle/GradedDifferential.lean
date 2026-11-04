module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.GradedLeibniz
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentDlog

/-!
# The relative de Rham differential preserves the grading on the punctured line bundle

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of the associated line bundle. The relative de Rham differential

`d : Ω^p_{L^⋆/S} ⟶ Ω^{p+1}_{L^⋆/S}`

is read here on the sections of the pushforward `π_* Ω^p_{L^⋆/S}` over an open of `X`, which is
the spelling the grading of [Stacks, Tag 0FU9] is stated in: its degree-`n` part
`Stacks.LineBundle.Situation.gradedLaurentForms` is a submodule of
`Situation.laurentFormsPushforward`, so a statement about `d` and the grading is a statement
about these sections.

The differential **preserves the degree**: the differential of a homogeneous form of degree `n`
is a homogeneous form of degree `n`, hence a section of `Ω^{p+1}_{L^⋆/S, n}`. That is the
structural fact the weight-zero complex `Ω^•_{L^⋆/S, 0}` of [Stacks, Tag 0FUF] rests on; its
affine counterpart is `LaurentDeRham.deRhamDifferential_mem_weightComponent` of
`StacksFrontier.RingTheory.DeRham.LaurentResidue`, proved there for `A[T;T⁻¹]` over `R`.

## Main definitions

* `Stacks.LineBundle.Situation.gradedDiff`: **the relative de Rham differential of `L^⋆`**, read
  on the sections of the pushforward over an open of `X`.

## Main results

* `Stacks.LineBundle.Situation.gradedDiff_smul_one`: **in degree zero the differential of a
  multiple of the constant form `1` is the differential of the function**, which is the de Rham
  rule in the one degree it determines the differential outright.
* `Stacks.LineBundle.Situation.gradedDiff_gradedD`: **`d (d g) = 0`** for a function `g` on
  `π⁻¹U`.
* `Stacks.LineBundle.Situation.gradedDiff_gradedWedge_of_gradedDiff_eq_zero`: the graded Leibniz
  rule `AlgebraicGeometry.SheafOfModules.d_formProduct_one` in the case of a closed one-form
  factor, in which the signed second term of the rule drops out.
* `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_gradedDiff`: **the differential of a
  homogeneous form of degree `n` is a homogeneous form of degree `n`.**
* `Stacks.LineBundle.Situation.gradedDiff_mem_gradedLaurentForms`: **hence it is a section of
  `Ω^{p+1}_{L^⋆/S, n}`.** This is the sectionwise degree-stability that the `hN` hypothesis of
  `SheafOfModules.Submodule.subcomplex` asks for, on the homogeneous generators of the degree-`n`
  part.
* `Stacks.LineBundle.Situation.gradedDiff_smul` and
  `Situation.laurentFunctionOfOpen_smul_one`: the two inputs that lift that from the generators to
  every section of the degree-`n` part.
* `Stacks.LineBundle.Situation.pushDiff_mem_gradedLaurentForms_of_mem` and
  `Situation.gradedDiff_mem_gradedLaurentForms_of_mem`: **the differential of an arbitrary section
  of `Ω^p_{L^⋆/S, n}` over an arbitrary open of `X` is a section of `Ω^{p+1}_{L^⋆/S, n}`** — the
  degree stability of the grading of [Stacks, Tag 0FU9] under the relative de Rham differential,
  which is the `hN` hypothesis of `SheafOfModules.Submodule.subcomplex` for the family
  `Situation.gradedLaurentForms p n`, `p : ℕ`.

## Implementation notes

The recursion defining `Stacks.LineBundle.Situation.IsHomogeneousLaurentForm` wedges on the right
with the differential of a homogeneous function, so the induction needs exactly the Leibniz rule
`AlgebraicGeometry.SheafOfModules.d_formProduct_one` for a wedge with a one-form, and that
one-form is closed, so the signed second term of the rule contributes nothing and no sign
bookkeeping occurs. With no wedge factors the form is a multiple of the constant form `1`, and
the de Rham rule `AlgebraicGeometry.Scheme.Hom.deRhamComplex_degreeZero` computes the
differential as the differential of the coefficient; that coefficient is a homogeneous function
of degree `n`, whose differential is a homogeneous one-form of degree `n` by the recursion
itself.

Everything here is about *sections*: no restriction of scalars to `f^{-1}𝒪_S` occurs even though
the differential is only `f^{-1}𝒪_S`-linear, because no morphism of sheaves on `X` is constructed
here. That linearity is also what stops `SheafOfModules.Submodule.subcomplex` from turning the
grading into the weight-zero complex of [Stacks, Tag 0FUF]: that mechanism cuts a subcomplex out
of a complex `K` of sheaves of `R`-modules, and `Situation.gradedLaurentForms p n` is a submodule
of `Situation.laurentFormsPushforward p`, an `𝒪_X`-module, on which there is no differential —
already `d (a ω) = d a ∧ ω + a d ω`, and `AlgebraicGeometry.SheafOfModules.d_smul` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.LocalizedLeibniz` is that identity in the generality
that rules the `𝒪_X`-module reading out.

**Lifting the degree stability from the generators to every section.** The `hN` hypothesis of
`SheafOfModules.Submodule.subcomplex` is degree stability for *every* section over *every* open,
not only for the homogeneous generators over an affine one. The route is the minimality principle
`Situation.gradedLaurentForms_le_iff` against the sub-`𝒪_X`-module sheaf of the sections whose
differential stays in the degree-`n` part, exactly as
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistRaising` does for multiplication
by a homogeneous function (`Situation.RaisesDegree` and the four private declarations after it).
Two features of that condition are not optional. It has to be imposed over every *smaller* open,
which is what makes it restriction-stable and local; and it has to be carried *together with* the
condition that the wedge with the differential of a degree-zero homogeneous function stays in the
degree-`n` part, because by `Situation.gradedDiff_smul` the first condition is not an
`𝒪_X`-module condition on its own — the Leibniz error term `ω ∧ d π^⋆r` is an instance of the
second, at the degree-zero homogeneous function `Situation.laurentFunctionOfOpen_smul_one`. The
second condition is `𝒪_X`-stable by itself, wedging being `𝒪_X`-bilinear.

**The spelling the machinery has to be written in.** The condition is stated with
`Situation.pushDiff`, `Situation.pushWedge` and `Situation.pushD`, which take their arguments at
`(laurentFormsPushforward p).val.obj (op U)` rather than at `Γ(Situation.gradedAmbient p, U)`,
and that is not cosmetic. `Situation.gradedAmbient` ascribes its type as `D.X.Modules`, so
unifying a `Γ(Situation.gradedAmbient p, V.unop)` against the
`(ModuleCat.restrictScalars …).obj ((laurentFormsPushforward p).val.obj V)` that
`PresheafOfModules.map_smul` produces in the `smul_mem'` field has to cross the
`AlgebraicGeometry.Scheme.Modules` versus `SheafOfModules D.X.ringCatSheaf` seam *as well as*
`restrictScalars`; written that way the construction fails `FunLike` synthesis in `smul_mem'` and
exceeds 200000 heartbeats at `isDefEq`. This is why
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.HomogeneousTwistRaising` states its whole
`RaisesDegree` condition with `Situation.laurentSmul` and `Situation.laurentFormsPushforward` and
never with `Situation.gradedSmul`: inside the submodule machinery only the pushforward spelling
unifies cheaply, and the `Γ(·, ·)` spellings belong over affine opens. Two further details of that
file's idiom are load-bearing and were arrived at the hard way: `map_zero` and `map_add` are
applied to `((laurentFormsPushforward p).val.map g).hom` and not to the morphism itself, whose
codomain is the `restrictScalars` object that instance search will not see through; and the
`𝒪_X`-action is moved by `PresheafOfModules.map_smul`, the lemma about the presheaf, rather than
by the generic `map_smul` on a morphism.

**What the ambient complex would take.** It exists over `f^{-1}𝒪_S` rather than over `𝒪_X`,
namely as `π_* Ω^•_{L^⋆/S}` read in sheaves of `f^{-1}𝒪_S`-modules on `X`, and the direct image
of the de Rham complex in sheaves of modules is not in the development:
`StacksFrontier.AlgebraicGeometry.DeRham.Functoriality` constructs it only in abelian sheaves
(`Scheme.Hom.deRhamAbelianPushforwardMap`), and its implementation notes record that the
module-level form would need the base-change morphism of the square — here
`f^{-1}𝒪_S ⟶ π_*((π ≫ f)^{-1}𝒪_S)`. Concretely, the two things to build are a morphism of ringed
spaces `inverseImageBase D.laurentToBase ⟶ inverseImageBase D.f` over `π` — whose structure map
is the unit of the pullback-pushforward adjunction for `π.base`, so it needs the identification
of `(π ≫ f)^{-1}𝒪_S` with `π^{-1}(f^{-1}𝒪_S)`, i.e. a pullback-composition isomorphism for
`TopCat.Sheaf.pullback` — and then the transport of each `Situation.gradedLaurentForms p n`
across restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`, which does not change the underlying
sheaf of abelian groups, so the transported family has the same `obj` sets and the same
`isSheaf` proof. With that in hand, the degree-stability below and
`SheafOfModules.Submodule.subcomplex` give `Ω^•_{L^⋆/S, 0}` directly.

`Situation.gradedDiff` is the differential of the de Rham complex of `L^⋆ ⟶ S` evaluated on the
inverse image `π⁻¹U`, with its value typed as a section of `Situation.gradedAmbient` so that the
degree-`n` parts can be spoken of. `AlgebraicGeometry.Scheme.Hom.deRhamComplex` is
`AlgebraicGeometry.SheafOfModules.relativeDeRhamComplex` of the algebra package, which is an
abbreviation for the complex of the constructed differential, so statements about an arbitrary de
Rham differential apply to it with no transport.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The relative de Rham differential of `L^⋆`**, read on the sections of the pushed-forward
forms over an open `U` of `X`: the arrow of the de Rham complex of `L^⋆ ⟶ S` out of degree `p`,
evaluated on the inverse image of `U`. -/
def Situation.gradedDiff (p : ℕ) (U : D.X.Opens) (ω : Γ(D.gradedAmbient p, U)) :
    Γ(D.gradedAmbient (p + 1), U) :=
  ((Scheme.Hom.deRhamComplex D.laurentToBase).d p (p + 1)).val.app
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ω

/-- **In degree zero the differential of a multiple of the constant form `1` is the differential
of the function**: this is the de Rham rule, whose degree-zero case is
`AlgebraicGeometry.Scheme.Hom.deRhamComplex_degreeZero`. -/
theorem Situation.gradedDiff_smul_one (U : D.X.Opens)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    D.gradedDiff 0 U (b • D.laurentFormsAlgebra.one.eval
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) = D.gradedD U b :=
  eq_of_heq (Scheme.Hom.deRhamComplex_degreeZero D.laurentToBase
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) b)

/-- **The differential of the differential of a function vanishes.** -/
theorem Situation.gradedDiff_gradedD (U : D.X.Opens)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    D.gradedDiff 1 U (D.gradedD U b) = 0 := by
  rw [← D.gradedDiff_smul_one U b]
  exact congrArg
    (fun g : SheafOfModules.deRhamTerm (Scheme.Hom.deRhamAlgebras D.laurentToBase) 0 ⟶
        SheafOfModules.deRhamTerm (Scheme.Hom.deRhamAlgebras D.laurentToBase) (1 + 1) =>
      g.val.app (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) _)
    ((Scheme.Hom.deRhamComplex D.laurentToBase).d_comp_d 0 1 (1 + 1))

/-- **The Leibniz rule for a wedge with a closed one-form**: when the one-form factor is closed
the signed second term of the graded Leibniz rule
`AlgebraicGeometry.SheafOfModules.d_formProduct_one` drops out, so the differential passes to the
`p`-form factor with no sign. -/
theorem Situation.gradedDiff_gradedWedge_of_gradedDiff_eq_zero (p : ℕ) (U : D.X.Opens)
    (η : Γ(D.gradedAmbient p, U)) (ξ : Γ(D.gradedAmbient 1, U))
    (hξ : D.gradedDiff 1 U ξ = 0) :
    D.gradedDiff (p + 1) U (D.gradedWedge p U η ξ) =
      D.gradedWedge (p + 1) U (D.gradedDiff p U η) ξ := by
  have hz : SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras D.laurentToBase) p 2
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) η
      (((Scheme.Hom.deRhamComplex D.laurentToBase).d 1 (1 + 1)).val.app
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ξ) = 0 := by
    rw [show ((Scheme.Hom.deRhamComplex D.laurentToBase).d 1 (1 + 1)).val.app
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ξ = 0 from hξ]
    exact map_zero ((D.laurentFormsAlgebra.mul (p : ℤ) 2).app
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) η)
  refine Eq.trans (SheafOfModules.d_formProduct_one
    (Scheme.Hom.deRhamAlgebras D.laurentToBase) (SheafOfModules.deRhamDifferential _) p
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) η ξ) ?_
  exact (congrArg₂ (· + ·) rfl
      ((congrArg ((-1 : ℤ) ^ p • ·) hz).trans (smul_zero _))).trans (add_zero _)

/-! ### Elementary rules for the differential on sections -/

/-- The differential as an additive map on sections, **pinned at the `Situation.gradedAmbient`
spelling** of the pushed-forward forms. The terms of the de Rham complex are restrictions of
scalars to `f^{-1}𝒪_S`, so the morphism's own domain and codomain are written in a spelling whose
carriers are those of `Situation.gradedAmbient` but whose instances are not found for it; the
ascription in this definition pays that defeq check once, and the rules below are then stated and
proved against an honest `AddMonoidHom`. -/
def Situation.gradedDiffHom (p : ℕ) (U : D.X.Opens) :
    Γ(D.gradedAmbient p, U) →+ Γ(D.gradedAmbient (p + 1), U) :=
  (((Scheme.Hom.deRhamComplex D.laurentToBase).d p (p + 1)).val.app
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U))).hom.toAddMonoidHom

/-- The pinned additive map is the differential. -/
@[simp]
theorem Situation.gradedDiffHom_apply (p : ℕ) (U : D.X.Opens) (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedDiffHom p U ω = D.gradedDiff p U ω :=
  rfl

/-- **The differential is additive.** -/
theorem Situation.gradedDiff_add (p : ℕ) (U : D.X.Opens) (ω η : Γ(D.gradedAmbient p, U)) :
    D.gradedDiff p U (ω + η) = D.gradedDiff p U ω + D.gradedDiff p U η :=
  map_add (D.gradedDiffHom p U) ω η

/-- **The differential kills the zero form.** -/
theorem Situation.gradedDiff_zero (p : ℕ) (U : D.X.Opens) :
    D.gradedDiff p U 0 = 0 :=
  map_zero (D.gradedDiffHom p U)

/-- **Restriction on the pushed-forward forms is restriction on the terms of the de Rham
complex.** The two sides differ only in which spelling of the sheaf — the `𝒪_X`-module
`Situation.gradedAmbient` or the restriction of scalars to `f^{-1}𝒪_S` carried by the complex —
the restriction map is read on, and that holds by `rfl`. Having it as an equation is what lets
the naturality of the differential be stated at the `Situation.gradedAmbient` spelling, where the
degree-`n` parts live. -/
theorem Situation.gradedAmbient_map_eq_deRhamComplex_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (ω : Γ(D.gradedAmbient p, U)) :
    (D.gradedAmbient p).presheaf.map (homOfLE hWU).op ω =
      ((Scheme.Hom.deRhamComplex D.laurentToBase).X p).val.map
        (D.laurentPreimageHom hWU).op ω :=
  rfl

/-- **The differential commutes with restriction** to a smaller open of `X`: the naturality of
the arrow of the de Rham complex, read at the `Situation.gradedAmbient` spelling. -/
theorem Situation.gradedDiff_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (ω : Γ(D.gradedAmbient p, U)) :
    (D.gradedAmbient (p + 1)).presheaf.map (homOfLE hWU).op (D.gradedDiff p U ω) =
      D.gradedDiff p W ((D.gradedAmbient p).presheaf.map (homOfLE hWU).op ω) := by
  rw [D.gradedAmbient_map_eq_deRhamComplex_map (p + 1) hWU (D.gradedDiff p U ω),
    D.gradedAmbient_map_eq_deRhamComplex_map p hWU ω]
  exact (PresheafOfModules.naturality_apply
    ((Scheme.Hom.deRhamComplex D.laurentToBase).d p (p + 1)).val
    (D.laurentPreimageHom hWU).op ω).symm

/-! ### Wedging with a degree-zero form, and the Leibniz rule against a scalar -/

/-- **Wedging a pushed-forward `p`-form with a pushed-forward `0`-form.** The degree
`((p + 0 : ℕ) : ℤ)` of the target is `(p : ℤ) + 0` by `rfl`, so no transport along an equality of
degrees occurs, as for `Situation.gradedWedge`. -/
def Situation.gradedWedgeZero (p : ℕ) (U : D.X.Opens) (ω : Γ(D.gradedAmbient p, U))
    (c : Γ(D.gradedAmbient 0, U)) : Γ(D.gradedAmbient p, U) :=
  (D.laurentFormsAlgebra.mul (p : ℤ) 0).app (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ω c

/-- **Wedging with a multiple of the constant form `1` is multiplication by the function**: the
graded multiplication is linear in the second factor and `1` is a right unit. -/
theorem Situation.gradedWedgeZero_gradedSmul_gradedOne (p : ℕ) (U : D.X.Opens)
    (a : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))
    (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedWedgeZero p U ω (D.gradedSmul 0 U a (D.gradedOne U)) = D.gradedSmul p U a ω :=
  ((D.laurentFormsAlgebra.mul (p : ℤ) 0).map_smul_right
      (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) a ω
      (D.laurentFormsAlgebra.one.eval (op (D.laurentSpectrumToBase ⁻¹ᵁ U)))).trans
    (congrArg (fun z : Γ(D.gradedAmbient p, U) => D.gradedSmul p U a z)
      (eq_of_heq (D.laurentFormsAlgebra.mul_one (p : ℤ)
        (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ω)))

/-- **The Leibniz rule against a function pulled back from `X`**:

`d (r ω) = r d ω + (-1)^p (ω ∧ d π^⋆r)`

for `r` a function on an open `U` of `X`, the action of `r` on the pushed-forward forms being
multiplication by its pullback. This is the graded Leibniz rule
`AlgebraicGeometry.SheafOfModules.d_formProduct_zero` applied to `ω` and the degree-zero form
`π^⋆r · 1`, whose differential is `d π^⋆r` by the de Rham rule in degree zero. It is the rule the
degree-`n` part has to be stable under in order to be an `𝒪_X`-submodule condition. -/
theorem Situation.gradedDiff_smul (p : ℕ) (U : D.X.Opens) (r : Γ(D.X, U))
    (ω : Γ(D.gradedAmbient p, U)) :
    D.gradedDiff p U (r • ω) =
      r • D.gradedDiff p U ω +
        (-1 : ℤ) ^ p • D.gradedWedge p U ω
          (D.gradedD U (D.laurentPullbackFunction U r)) := by
  have hsrc : (r • ω : Γ(D.gradedAmbient p, U)) =
      D.gradedWedgeZero p U ω
        (D.gradedSmul 0 U (D.laurentPullbackFunction U r) (D.gradedOne U)) :=
    ((D.gradedSmul_pullback p U r ω).symm).trans
      (D.gradedWedgeZero_gradedSmul_gradedOne p U (D.laurentPullbackFunction U r) ω).symm
  rw [hsrc]
  refine Eq.trans (SheafOfModules.d_formProduct_zero
    (Scheme.Hom.deRhamAlgebras D.laurentToBase) (SheafOfModules.deRhamDifferential _) p
    (op (D.laurentSpectrumToBase ⁻¹ᵁ U)) ω
    (D.gradedSmul 0 U (D.laurentPullbackFunction U r) (D.gradedOne U))) ?_
  refine congrArg₂ (· + ·)
    (((D.gradedWedgeZero_gradedSmul_gradedOne (p + 1) U (D.laurentPullbackFunction U r)
        (D.gradedDiff p U ω)).trans
      (D.gradedSmul_pullback (p + 1) U r (D.gradedDiff p U ω)))) ?_
  exact congrArg (fun z : Γ(D.gradedAmbient 1, U) =>
      (-1 : ℤ) ^ p • D.gradedWedge p U ω z)
    (D.gradedDiff_smul_one U (D.laurentPullbackFunction U r))

/-! ### The differential preserves the degree -/

/-- **The relative de Rham differential of a homogeneous form of degree `n` is a homogeneous form
of degree `n`**, over an affine open of `X`. With no wedge factors the form is `g · 1` for a
homogeneous function `g` of degree `n`, whose differential is `1 ∧ d g`; each further factor is a
closed one-form, so the differential passes to the other factor by the Leibniz rule. -/
theorem Situation.isHomogeneousLaurentForm_gradedDiff (U : D.X.affineOpens) :
    ∀ (p : ℕ) (n : ℤ) (ω : Γ(D.gradedAmbient p, U.1)),
      D.IsHomogeneousLaurentForm U p n ω →
        D.IsHomogeneousLaurentForm U (p + 1) n (D.gradedDiff p U.1 ω) := by
  intro p
  induction p with
  | zero =>
      rintro n ω ⟨x, rfl⟩
      rw [D.gradedDiff_smul_one U.1 (D.laurentFunction n U x)]
      have h := D.isHomogeneousLaurentForm_gradedWedge 0 0 n n (zero_add n) U
        (D.isHomogeneousLaurentForm_gradedOne U) x
      rwa [D.gradedWedge_gradedOne_left] at h
  | succ q ih =>
      rintro n ω ⟨i, j, hij, η, x, hη, rfl⟩
      rw [show (D.laurentFormsAlgebra.mul (q : ℤ) 1).app
            (op (D.laurentSpectrumToBase ⁻¹ᵁ U.1)) η
            (D.laurentDifferential (D.laurentSpectrumToBase ⁻¹ᵁ U.1)
              (D.laurentFunction j U x)) =
          D.gradedWedge q U.1 η (D.gradedD U.1 (D.laurentFunction j U x)) from rfl,
        D.gradedDiff_gradedWedge_of_gradedDiff_eq_zero q U.1 η _
          (D.gradedDiff_gradedD U.1 (D.laurentFunction j U x))]
      exact D.isHomogeneousLaurentForm_gradedWedge (q + 1) i j n hij U (ih i η hη) x

/-- **The differential of a homogeneous form of degree `n` is a section of
`Ω^{p+1}_{L^⋆/S, n}`.** -/
theorem Situation.gradedDiff_mem_gradedLaurentForms (U : D.X.affineOpens) (p : ℕ) (n : ℤ)
    {ω : Γ(D.gradedAmbient p, U.1)} (hω : D.IsHomogeneousLaurentForm U p n ω) :
    D.gradedDiff p U.1 ω ∈ (D.gradedLaurentForms (p + 1) n).obj (op U.1) :=
  D.mem_gradedLaurentForms U (D.isHomogeneousLaurentForm_gradedDiff U p n ω hω)

/-! ### The pullback of a function as a degree-zero homogeneous function -/

/-- **A function pulled back from `X` is the homogeneous function of degree zero** attached to
the corresponding multiple of the unit of the Laurent algebra, over an arbitrary open of `X`.
This is `Situation.laurentPullbackFunction_eq` with the affineness hypothesis removed, which is
what lets the Leibniz rule be fed to a condition quantified over arbitrary opens. -/
theorem Situation.laurentFunctionOfOpen_smul_one (U : D.X.Opens) (r : Γ(D.X, U)) :
    D.laurentFunctionOfOpen 0 U
        (r • id (α := Γ(D.tensorPower 0, U)) (D.laurentAlgebra.one.eval (op U))) =
      D.laurentPullbackFunction U r :=
  ((D.laurentFunctionOfOpen_smul 0 U r _).trans
      (congrArg (D.laurentPullbackFunction U r * ·) (D.laurentFunctionOfOpen_one U))).trans
    (mul_one (D.laurentPullbackFunction U r))


/-! ### The differential and the wedge at the pushforward spelling -/

/-- **The differential, with its argument and value typed at the
`Situation.laurentFormsPushforward` spelling** of the pushed-forward forms rather than at
`Situation.gradedAmbient`. It is `Situation.gradedDiff`, and the only difference is which of the
two definitionally equal spellings of the sheaf its type is written in; see this file's
implementation notes for why the submodule machinery needs this one. -/
def Situation.pushDiff (p : ℕ) (U : D.X.Opens)
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)) :
    (D.laurentFormsPushforward ((p + 1 : ℕ) : ℤ)).val.obj (op U) :=
  D.gradedDiff p U ω

/-- The differential at the two spellings is the same map. -/
theorem Situation.pushDiff_eq_gradedDiff (p : ℕ) (U : D.X.Opens)
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)) :
    D.pushDiff p U ω = D.gradedDiff p U ω :=
  rfl

/-- **Wedging with a one-form at the pushforward spelling**: `Situation.gradedWedge` with its
arguments typed at `Situation.laurentFormsPushforward`. -/
def Situation.pushWedge (p : ℕ) (U : D.X.Opens)
    (η : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U))
    (ξ : (D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.obj (op U)) :
    (D.laurentFormsPushforward ((p + 1 : ℕ) : ℤ)).val.obj (op U) :=
  D.gradedWedge p U η ξ

/-- **The differential of a function at the pushforward spelling**: `Situation.gradedD` with its
value typed at `Situation.laurentFormsPushforward`. -/
def Situation.pushD (U : D.X.Opens)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    (D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.obj (op U) :=
  D.gradedD U b

/-- The differential kills the zero form. -/
theorem Situation.pushDiff_zero (p : ℕ) (U : D.X.Opens) : D.pushDiff p U 0 = 0 :=
  D.gradedDiff_zero p U

/-- The differential is additive. -/
theorem Situation.pushDiff_add (p : ℕ) (U : D.X.Opens)
    (ω η : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)) :
    D.pushDiff p U (ω + η) = D.pushDiff p U ω + D.pushDiff p U η :=
  D.gradedDiff_add p U ω η

/-- The differential commutes with restriction. -/
theorem Situation.pushDiff_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)) :
    (D.laurentFormsPushforward ((p + 1 : ℕ) : ℤ)).val.map (homOfLE hWU).op
        (D.pushDiff p U ω) =
      D.pushDiff p W ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWU).op ω) :=
  D.gradedDiff_map p hWU ω

/-- **The Leibniz rule against a function pulled back from `X`**, at the pushforward spelling.
This is the rule whose error term makes the first half of `Situation.DStable` depend on the
second. -/
theorem Situation.pushDiff_smul (p : ℕ) (U : D.X.Opens)
    (r : D.X.ringCatSheaf.obj.obj (op U))
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)) :
    D.pushDiff p U (r • ω) =
      r • D.pushDiff p U ω +
        (-1 : ℤ) ^ p • D.pushWedge p U ω (D.pushD U (D.laurentPullbackFunction U r)) :=
  D.gradedDiff_smul p U r ω

/-- Wedging the zero form gives zero. -/
theorem Situation.pushWedge_zero_left (p : ℕ) (U : D.X.Opens)
    (ξ : (D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.obj (op U)) :
    D.pushWedge p U 0 ξ = 0 :=
  D.gradedWedge_zero_left p U ξ

/-- Wedging is additive in the `p`-form. -/
theorem Situation.pushWedge_add_left (p : ℕ) (U : D.X.Opens)
    (η₁ η₂ : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U))
    (ξ : (D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.obj (op U)) :
    D.pushWedge p U (η₁ + η₂) ξ = D.pushWedge p U η₁ ξ + D.pushWedge p U η₂ ξ :=
  D.gradedWedge_add_left p U η₁ η₂ ξ

/-- Wedging is `𝒪_X(U)`-linear in the `p`-form. -/
theorem Situation.pushWedge_smul_left (p : ℕ) (U : D.X.Opens)
    (r : D.X.ringCatSheaf.obj.obj (op U))
    (η : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U))
    (ξ : (D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.obj (op U)) :
    D.pushWedge p U (r • η) ξ = r • D.pushWedge p U η ξ :=
  D.gradedWedge_smul_left p U r η ξ

/-- Wedging commutes with restriction. -/
theorem Situation.pushWedge_map (p : ℕ) {U W : D.X.Opens} (hWU : W ≤ U)
    (η : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U))
    (ξ : (D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.obj (op U)) :
    (D.laurentFormsPushforward ((p + 1 : ℕ) : ℤ)).val.map (homOfLE hWU).op
        (D.pushWedge p U η ξ) =
      D.pushWedge p W ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWU).op η)
        ((D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.map (homOfLE hWU).op ξ) :=
  D.gradedWedge_map p hWU η ξ

/-- The differential of a function commutes with restriction. -/
theorem Situation.pushD_map {U W : D.X.Opens} (hWU : W ≤ U)
    (b : D.laurentSpectrum.sheaf.obj.obj (op (D.laurentSpectrumToBase ⁻¹ᵁ U))) :
    (D.laurentFormsPushforward ((1 : ℕ) : ℤ)).val.map (homOfLE hWU).op (D.pushD U b) =
      D.pushD W ((D.laurentSpectrum.sheaf.obj.map (D.laurentPreimageHom hWU).op).hom b) :=
  D.gradedD_map hWU b

/-- **The differential of a homogeneous form of degree `n` is a section of
`Ω^{p+1}_{L^⋆/S, n}`**, at the pushforward spelling. -/
theorem Situation.pushDiff_mem_gradedLaurentForms (U : D.X.affineOpens) (p : ℕ) (n : ℤ)
    {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U.1)}
    (hω : D.IsHomogeneousLaurentForm U p n ω) :
    D.pushDiff p U.1 ω ∈ (D.gradedLaurentForms (p + 1) n).obj (op U.1) :=
  D.gradedDiff_mem_gradedLaurentForms U p n hω

/-- **The wedge of a homogeneous form of degree `n` with the differential of a degree-zero
homogeneous function is a section of `Ω^{p+1}_{L^⋆/S, n}`**: the degrees add to `n + 0 = n`. -/
theorem Situation.pushWedge_mem_gradedLaurentForms (U : D.X.affineOpens) (p : ℕ) (n : ℤ)
    {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U.1)}
    (hω : D.IsHomogeneousLaurentForm U p n ω)
    (x : (D.laurentAlgebra.piece 0).val.obj (op U.1)) :
    D.pushWedge p U.1 ω (D.pushD U.1 (D.laurentFunctionOfOpen 0 U.1 x)) ∈
      (D.gradedLaurentForms (p + 1) n).obj (op U.1) := by
  refine D.mem_gradedLaurentForms_of_eq (p + 1) n
    (congrArg (fun f => D.pushWedge p U.1 ω (D.pushD U.1 f))
      (D.laurentFunctionOfOpen_affine 0 U x)) ?_
  exact D.mem_gradedLaurentForms U
    (D.isHomogeneousLaurentForm_gradedWedge p n 0 n (add_zero n) U hω x)

/-! ### Degree stability over an arbitrary open -/

/-- The condition cutting out the sections whose differential lands in the degree-`n` part, *and*
whose wedge with the differential of a degree-zero homogeneous function does too. The two halves
travel together because the first is not an `𝒪_X`-module condition on its own: the Leibniz rule
`Situation.pushDiff_smul` turns `d (r ω)` into `r d ω` plus a wedge of `ω` with `d π^⋆r`, and
`π^⋆r` is a degree-zero homogeneous function by
`Situation.laurentFunctionOfOpen_smul_one`, so stability under the `𝒪_X`-action of the first half
needs the second. The second half is `𝒪_X`-stable on its own, wedging being `𝒪_X`-bilinear.

As in `Situation.RaisesDegree`, the condition is imposed over *every smaller open*, which is what
makes it local: the restriction of a section satisfying it satisfies it, and a section satisfying
it near every point satisfies it. -/
private def Situation.DStable (p : ℕ) (n : ℤ) {U : (Opens D.X)ᵒᵖ}
    (ω : (D.laurentFormsPushforward (p : ℤ)).val.obj U) : Prop :=
  (∀ (V : (Opens D.X)ᵒᵖ) (g : U ⟶ V),
      D.gradedDiff p V.unop ((D.laurentFormsPushforward (p : ℤ)).val.map g ω) ∈
        (D.gradedLaurentForms (p + 1) n).obj V) ∧
    ∀ (V : (Opens D.X)ᵒᵖ) (g : U ⟶ V) (x : (D.laurentAlgebra.piece 0).val.obj V),
      D.gradedWedge p V.unop ((D.laurentFormsPushforward (p : ℤ)).val.map g ω)
          (D.gradedD V.unop (D.laurentFunctionOfOpen 0 V.unop x)) ∈
        (D.gradedLaurentForms (p + 1) n).obj V

/-- The condition is stable under restriction, each of its instances for the restricted section
being one of its instances for the section. -/
private theorem Situation.dStable_map (p : ℕ) (n : ℤ) {U V : (Opens D.X)ᵒᵖ} (g : U ⟶ V)
    {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj U} (hω : D.DStable p n ω) :
    D.DStable p n ((D.laurentFormsPushforward (p : ℤ)).val.map g ω) :=
  ⟨fun V' g' => D.mem_gradedLaurentForms_of_eq (p + 1) n
      (congrArg (fun η => D.pushDiff p V'.unop η)
        ((D.laurentFormsPushforward (p : ℤ)).val.map_comp_apply g g' ω).symm)
      (hω.1 V' (g ≫ g')),
    fun V' g' x => D.mem_gradedLaurentForms_of_eq (p + 1) n
      (congrArg (fun η => D.pushWedge p V'.unop η
          (D.pushD V'.unop (D.laurentFunctionOfOpen 0 V'.unop x)))
        ((D.laurentFormsPushforward (p : ℤ)).val.map_comp_apply g g' ω).symm)
      (hω.2 V' (g ≫ g') x)⟩

/-- Restricting twice is restricting once, whatever the (unique) composite morphism is. -/
private theorem Situation.laurentFormsPushforward_map_map (p : ℕ) {U V W : (Opens D.X)ᵒᵖ}
    (g : U ⟶ V) (h : V ⟶ W) (k : U ⟶ W) (s : (D.laurentFormsPushforward (p : ℤ)).val.obj U) :
    (D.laurentFormsPushforward (p : ℤ)).val.map h
        ((D.laurentFormsPushforward (p : ℤ)).val.map g s) =
      (D.laurentFormsPushforward (p : ℤ)).val.map k s :=
  ((D.laurentFormsPushforward (p : ℤ)).val.map_comp_apply g h s).symm.trans
    ((D.laurentFormsPushforward (p : ℤ)).val.congr_map_apply (Subsingleton.elim _ _) s)

/-- **The condition is local on the open**: a section satisfying it on a neighbourhood of every
point satisfies it. Each of its instances is a membership in a graded piece, and those are local
by `Situation.mem_gradedLaurentForms_of_locally`; the neighbourhood is cut down by the open the
instance is asked over, so that the two restrictions of the section being compared agree. -/
private theorem Situation.dStable_of_locally (p : ℕ) (n : ℤ) {U : (Opens D.X)ᵒᵖ}
    (s : (D.laurentFormsPushforward (p : ℤ)).val.obj U)
    (hs : ∀ z ∈ U.unop, ∃ (W : D.X.Opens) (hW : W ≤ U.unop), z ∈ W ∧
      D.DStable p n ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hW).op s)) :
    D.DStable p n s := by
  have hboth : ∀ (V : (Opens D.X)ᵒᵖ) (g : U ⟶ V) (W : D.X.Opens) (hWU : W ≤ U.unop),
      (D.laurentFormsPushforward (p : ℤ)).val.map
          (homOfLE (inf_le_right : W ⊓ V.unop ≤ V.unop)).op
          ((D.laurentFormsPushforward (p : ℤ)).val.map g s) =
        (D.laurentFormsPushforward (p : ℤ)).val.map
          (homOfLE (inf_le_left : W ⊓ V.unop ≤ W)).op
          ((D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWU).op s) := by
    intro V g W hWU
    exact (D.laurentFormsPushforward_map_map p g _ (g ≫ (homOfLE inf_le_right).op) s).trans
      (D.laurentFormsPushforward_map_map p (homOfLE hWU).op _ _ s).symm
  refine ⟨fun V g => ?_, fun V g x => ?_⟩
  · refine D.mem_gradedLaurentForms_of_locally (p + 1) n _ ?_
    intro z hz
    obtain ⟨W, hWU, hzW, hW⟩ := hs z (leOfHom g.unop hz)
    refine ⟨W ⊓ V.unop, inf_le_right, ⟨hzW, hz⟩, ?_⟩
    refine D.mem_gradedLaurentForms_of_eq (p + 1) n
      ((D.pushDiff_map p (inf_le_right : W ⊓ V.unop ≤ V.unop) _).trans
        (congrArg (fun η => D.pushDiff p (W ⊓ V.unop) η) (hboth V g W hWU))) ?_
    exact hW.1 (op (W ⊓ V.unop)) (homOfLE (inf_le_left : W ⊓ V.unop ≤ W)).op
  · refine D.mem_gradedLaurentForms_of_locally (p + 1) n _ ?_
    intro z hz
    obtain ⟨W, hWU, hzW, hW⟩ := hs z (leOfHom g.unop hz)
    refine ⟨W ⊓ V.unop, inf_le_right, ⟨hzW, hz⟩, ?_⟩
    refine D.mem_gradedLaurentForms_of_eq (p + 1) n
      ((D.pushWedge_map p (inf_le_right : W ⊓ V.unop ≤ V.unop) _ _).trans
        (congrArg₂ (fun η ξ => D.pushWedge p (W ⊓ V.unop) η ξ) (hboth V g W hWU)
          ((D.pushD_map (inf_le_right : W ⊓ V.unop ≤ V.unop) _).trans
            (congrArg (D.pushD (W ⊓ V.unop))
              (D.laurentFunctionOfOpen_map 0 (inf_le_right : W ⊓ V.unop ≤ V.unop) x))))) ?_
    exact hW.2 (op (W ⊓ V.unop)) (homOfLE (inf_le_left : W ⊓ V.unop ≤ W)).op _

/-- The sections satisfying the condition, as a sub-`𝒪_X`-module of the pushed-forward forms. The
`𝒪_X`-action on the first half is the Leibniz rule `Situation.pushDiff_smul`, whose error term
is an instance of the second half at the degree-zero homogeneous function of
`Situation.laurentFunctionOfOpen_smul_one`. -/
private def Situation.dStableSubmodule (p : ℕ) (n : ℤ) :
    (D.laurentFormsPushforward (p : ℤ)).val.Submodule where
  obj V :=
    { carrier := {ω | D.DStable p n ω}
      zero_mem' := ⟨fun V' g => D.mem_gradedLaurentForms_of_eq (p + 1) n
          ((congrArg (fun η => D.pushDiff p V'.unop η)
              (map_zero ((D.laurentFormsPushforward (p : ℤ)).val.map g).hom)).trans
            (D.pushDiff_zero p V'.unop))
          (Submodule.zero_mem _),
        fun V' g x => D.mem_gradedLaurentForms_of_eq (p + 1) n
          ((congrArg (fun η => D.pushWedge p V'.unop η
                (D.pushD V'.unop (D.laurentFunctionOfOpen 0 V'.unop x)))
              (map_zero ((D.laurentFormsPushforward (p : ℤ)).val.map g).hom)).trans
            (D.pushWedge_zero_left p V'.unop _))
          (Submodule.zero_mem _)⟩
      add_mem' := fun ha hb =>
        ⟨fun V' g => D.mem_gradedLaurentForms_of_eq (p + 1) n
            ((congrArg (fun η => D.pushDiff p V'.unop η)
                (map_add ((D.laurentFormsPushforward (p : ℤ)).val.map g).hom _ _)).trans
              (D.pushDiff_add p V'.unop _ _))
            (Submodule.add_mem _ (ha.1 V' g) (hb.1 V' g)),
          fun V' g x => D.mem_gradedLaurentForms_of_eq (p + 1) n
            ((congrArg (fun η => D.pushWedge p V'.unop η
                  (D.pushD V'.unop (D.laurentFunctionOfOpen 0 V'.unop x)))
                (map_add ((D.laurentFormsPushforward (p : ℤ)).val.map g).hom _ _)).trans
              (D.pushWedge_add_left p V'.unop _ _ _))
            (Submodule.add_mem _ (ha.2 V' g x) (hb.2 V' g x))⟩
      smul_mem' := fun r ω ha =>
        ⟨fun V' g => by
            refine D.mem_gradedLaurentForms_of_eq (p + 1) n
              ((congrArg (fun η => D.pushDiff p V'.unop η)
                  ((D.laurentFormsPushforward (p : ℤ)).val.map_smul g r ω)).trans
                (D.pushDiff_smul p V'.unop _ _)) ?_
            refine Submodule.add_mem _ (Submodule.smul_mem _ _ (ha.1 V' g)) ?_
            refine _root_.zsmul_mem ?_ _
            refine D.mem_gradedLaurentForms_of_eq (p + 1) n
              (congrArg (fun f => D.pushWedge p V'.unop _ (D.pushD V'.unop f))
                (D.laurentFunctionOfOpen_smul_one V'.unop _).symm) ?_
            exact ha.2 V' g _,
          fun V' g x => D.mem_gradedLaurentForms_of_eq (p + 1) n
            ((congrArg (fun η => D.pushWedge p V'.unop η
                  (D.pushD V'.unop (D.laurentFunctionOfOpen 0 V'.unop x)))
                ((D.laurentFormsPushforward (p : ℤ)).val.map_smul g r ω)).trans
              (D.pushWedge_smul_left p V'.unop _ _ _))
            (Submodule.smul_mem _ _ (ha.2 V' g x))⟩ }
  map g _ hω := D.dStable_map p n g hω

/-- **The sections satisfying the condition form a sub-`𝒪_X`-module *sheaf***: the `isSheaf`
field is `Situation.dStable_of_locally`. -/
private def Situation.dStableSubsheaf (p : ℕ) (n : ℤ) :
    (D.laurentFormsPushforward (p : ℤ)).Submodule where
  toSubmodule := D.dStableSubmodule p n
  isSheaf {U} s hs := D.dStable_of_locally p n s fun z hz => by
    obtain ⟨W, f, hWmem, hzW⟩ := hs z hz
    exact ⟨W, leOfHom f, hzW, hWmem⟩

/-- **Every section of the degree-`n` part satisfies the condition**: by the induction principle
`Situation.gradedLaurentForms_le_iff` it is enough to check it on the homogeneous forms of degree
`n` over an affine open, where the differential is handled by
`Situation.pushDiff_mem_gradedLaurentForms` and the wedge by
`Situation.pushWedge_mem_gradedLaurentForms`. Both are checked on
an affine neighbourhood inside the open the instance is asked over, membership being local. -/
private theorem Situation.gradedLaurentForms_le_dStableSubsheaf (p : ℕ) (n : ℤ) :
    D.gradedLaurentForms p n ≤ D.dStableSubsheaf p n := by
  refine (D.gradedLaurentForms_le_iff _).mpr ?_
  intro U ω hω
  have hres : ∀ (V : (Opens D.X)ᵒᵖ) (g : op U.1 ⟶ V) (W : D.X.Opens) (hWV : W ≤ V.unop),
      (D.laurentFormsPushforward (p : ℤ)).val.map (homOfLE hWV).op
          ((D.laurentFormsPushforward (p : ℤ)).val.map g ω) =
        (D.laurentFormsPushforward (p : ℤ)).val.map
          (homOfLE (hWV.trans (leOfHom g.unop))).op ω := by
    intro V g W hWV
    exact D.laurentFormsPushforward_map_map p g _ _ ω
  refine ⟨fun V g => ?_, fun V g x => ?_⟩
  · refine D.mem_gradedLaurentForms_of_locally (p + 1) n _ ?_
    intro z hz
    obtain ⟨W, hWaff, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens hz
    refine ⟨W, hWV, hzW, ?_⟩
    refine D.mem_gradedLaurentForms_of_eq (p + 1) n
      ((D.pushDiff_map p hWV _).trans
        (congrArg (fun η => D.pushDiff p W η) (hres V g W hWV))) ?_
    exact D.pushDiff_mem_gradedLaurentForms ⟨W, hWaff⟩ p n
      (D.isHomogeneousLaurentForm_map (U' := ⟨W, hWaff⟩)
        (hWV.trans (leOfHom g.unop)) p n ω hω)
  · refine D.mem_gradedLaurentForms_of_locally (p + 1) n _ ?_
    intro z hz
    obtain ⟨W, hWaff, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens hz
    refine ⟨W, hWV, hzW, ?_⟩
    refine D.mem_gradedLaurentForms_of_eq (p + 1) n
      ((D.pushWedge_map p hWV _ _).trans
        (congrArg₂ (fun η ξ => D.pushWedge p W η ξ) (hres V g W hWV)
          ((D.pushD_map hWV _).trans
            (congrArg (D.pushD W) (D.laurentFunctionOfOpen_map 0 hWV x))))) ?_
    exact D.pushWedge_mem_gradedLaurentForms ⟨W, hWaff⟩ p n
      (D.isHomogeneousLaurentForm_map (U' := ⟨W, hWaff⟩)
        (hWV.trans (leOfHom g.unop)) p n ω hω) _

/-- **The differential of a section of `Ω^p_{L^⋆/S, n}` is a section of `Ω^{p+1}_{L^⋆/S, n}`**,
over an arbitrary open of `X` and for an arbitrary section — not only for a homogeneous form over
an affine open, which is `Situation.pushDiff_mem_gradedLaurentForms`.

This is the degree stability of the grading of [Stacks, Tag 0FU9] under the relative de Rham
differential, in the shape the `hN` hypothesis of `SheafOfModules.Submodule.subcomplex` asks
for: it says that the family `Situation.gradedLaurentForms p n`, `p : ℕ`, is stable under the
differential. -/
theorem Situation.pushDiff_mem_gradedLaurentForms_of_mem (p : ℕ) (n : ℤ) {U : D.X.Opens}
    {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)}
    (hω : ω ∈ (D.gradedLaurentForms p n).obj (op U)) :
    D.pushDiff p U ω ∈ (D.gradedLaurentForms (p + 1) n).obj (op U) := by
  have hst : D.DStable p n ω := D.gradedLaurentForms_le_dStableSubsheaf p n (op U) hω
  refine D.mem_gradedLaurentForms_of_locally (p + 1) n _ ?_
  intro z hz
  obtain ⟨W, -, hzW, hWU⟩ := Opens.isBasis_iff_nbhd.mp D.X.isBasis_affineOpens hz
  refine ⟨W, hWU, hzW, ?_⟩
  refine D.mem_gradedLaurentForms_of_eq (p + 1) n (D.pushDiff_map p hWU ω) ?_
  exact hst.1 (op W) (homOfLE hWU).op

/-- The same, read at the `Situation.gradedAmbient` spelling of the differential. -/
theorem Situation.gradedDiff_mem_gradedLaurentForms_of_mem (p : ℕ) (n : ℤ) {U : D.X.Opens}
    {ω : (D.laurentFormsPushforward (p : ℤ)).val.obj (op U)}
    (hω : ω ∈ (D.gradedLaurentForms p n).obj (op U)) :
    D.gradedDiff p U ω ∈ (D.gradedLaurentForms (p + 1) n).obj (op U) :=
  D.pushDiff_mem_gradedLaurentForms_of_mem p n hω

end Stacks.LineBundle

end
