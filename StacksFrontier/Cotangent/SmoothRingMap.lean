module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.EtaleVanishing
public import StacksFrontier.Cotangent.PolynomialAlgebra
public import StacksFrontier.Cotangent.Triangle.VanishingVertex
public import StacksFrontier.RingTheory.Kaehler.PolynomialAlgebra

/-!
# Smooth ring maps

Section 92.9 of the Stacks Project, [Stacks, Tag 08R4], consists of Lemma 92.9.1,
[Stacks, Tag 08R5]: if `A → B` is a smooth ring map then `L_{B/A} = Ω_{B/A}[0]`.

This file proves the conclusion of that lemma for a **standard smooth** ring map, and — as the
statement the standard smooth case is deduced from — for a ring map presented by a *chart*, that
is a factorization `A → P → B` with `P` a polynomial algebra over `A` and `P → B` étale, both for
fundamental distinguished triangles taken as parameters. The lemma itself, for an arbitrary
smooth ring map and with Proposition 08QX supplied, is
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional` in
`StacksFrontier.Cotangent.SmoothUnconditional`, and the section tag 08R4 is registered there on its
existence form
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_smooth_unconditional`.
Neither tag is registered in this file.

## Main results

* `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale`:
  `L_{B/A} = Ω[B⁄A][0]` for a chart `A → P → B`, given the fundamental distinguished triangles of
  the towers `A → P → B` and `B → B ⊗_P B → B`.
* `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth`:
  the same for `Algebra.IsStandardSmooth A B`, given `CommAlgCat.HasFundamentalTriangles`. The
  chart is produced rather than assumed.

## Implementation notes

*The source's proof and the part of it carried out here.* The source argues: the agreement in
cohomological degree `0` is Lemma 08QF; it therefore suffices to kill the other cohomology
groups, which is local on `Spec(B)` because `L_{B_g/A} = (L_{B/A})_g` by Lemma 08R3; so one may
assume `A → B` standard smooth by Algebra, Lemma 00TA, that is, that `A → B` factors as
`A → A[x_1, …, x_n] → B` with `A[x_1, …, x_n] → B` étale; and then Lemmas 08R2 and 08R3 give
`L_{B/A} = L_{A[x_1, …, x_n]/A} ⊗ B`, whence the conclusion by Lemma 08QH.

This file carries out the standard smooth case. Lemma 08R2 item (5) gives `L_{B/P} = 0` because
`P → B` is étale, Lemma 08R3 then identifies `L_{B/A}` with `L_{P/A} ⊗^𝐋_P B`, and Lemma 08QH
identifies `L_{P/A}` with `Ω[P⁄A][0]`. Since `Ω[P⁄A]` is a free, hence projective, `P`-module,
the derived base change of that single complex is computed by the termwise one, and
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` identifies `B ⊗_P Ω[P⁄A]` with
`Ω[B⁄A]`. The full isomorphism in `D(B)` comes out at once rather than degree by degree.

*The chart is produced, not assumed.* Mathlib proves that a standard smooth algebra factors
through a polynomial algebra with étale second map, as
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`, which is exactly the source's
"we can factor `A → B` as `A → A[x_1, …, x_n] → B` with `A[x_1, …, x_n] → B` étale". The
`Fin n` of Mathlib's statement is transported to `ULift (Fin n)` by `MvPolynomial.renameEquiv`
to meet the universe of `Algebra.IsPolynomialAlgebra`.

*The smooth case.* The localization step of the source's proof is carried out in
`StacksFrontier.Cotangent.SmoothVanishing`, through Lemma 00TA
(`Algebra.Smooth.exists_span_eq_top_isStandardSmooth`) and the vanishing of the cohomology of
`L_{B/A}` being local on `Spec(B)`.

*The triangle parameters.* They are all instances of Proposition 08QX — that the three vertices
of the display of Equation 92.7.0.1 form a distinguished triangle for arbitrary ring maps
`A → B → C`. This file is upstream of its proof,
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, which `StacksFrontier.Cotangent.SmoothUnconditional`
applies. The first result takes two specific instances, as
`CommAlgCat.isZero_cotangentComplexDerived_of_etale` already does; the second takes the
proposition in the quantified form `CommAlgCat.HasFundamentalTriangles`, because the chart it
builds is not in scope when the statement is read.

*The remark that opens the section.* Before the lemma the source calls a surjection `C → B` with
kernel `I` "weakly quasi-regular" when `I/I²` is flat over `B` and `Tor_*^C(B, B)` is the
exterior algebra on `I/I²`, and observes that the generalization of Lemma 08R2 from étale to
smooth ring maps would look at flat `A → B` with `B ⊗_A B → B` weakly quasi-regular. It then
says "For the moment we just stick to smooth ring maps", so that generalization is not part of
the section's content and nothing is defined for it here.

## References

* [Stacks Project, Tag 08R4](https://stacks.math.columbia.edu/tag/08R4), the section.
* [Stacks Project, Tag 08R5](https://stacks.math.columbia.edu/tag/08R5), its lemma.
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH), the cotangent complex
  of a polynomial algebra.
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), the vanishing for an
  étale ring map.
* [Stacks Project, Tag 08R3](https://stacks.math.columbia.edu/tag/08R3), the identification made
  by a vanishing third vertex.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the proposition the
  triangle parameters are instances of.
* [Stacks Project, Tag 08QF](https://stacks.math.columbia.edu/tag/08QF), the degree-`0`
  agreement, which the argument used here does not need separately.
* [Stacks Project, Tag 00TA](https://stacks.math.columbia.edu/tag/00TA), the reduction to the
  standard smooth case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

attribute [local instance] diagonalAlgebra

/-- **The fundamental distinguished triangle, as a hypothesis.** For all ring maps
`R → S → T` the three vertices `L_{S/R} ⊗^𝐋_S T`, `L_{T/R}` and `L_{T/S}` of the display of
Equation 92.7.0.1 fit into a distinguished triangle in `D(T)`.

This is the statement of Proposition 08QX, recorded here as a `Prop` because this file is
upstream of its proof; `CommAlgCat.hasFundamentalTriangles` of
`StacksFrontier.Cotangent.SmoothUnconditional` proves it from
`CommAlgCat.productFundamentalTriangle_distinguished`. -/
def HasFundamentalTriangles : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] (T : Type u) [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T],
    ∃ (α : fundamentalVertex₁.{u, u} R S T ⟶ fundamentalVertex₂.{u, u} R T)
      (β : fundamentalVertex₂.{u, u} R T ⟶ fundamentalVertex₃.{u, u} S T)
      (γ : fundamentalVertex₃.{u, u} S T ⟶ (fundamentalVertex₁.{u, u} R S T)⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} T))

section Chart

variable (A : Type u) [CommRing A] (P : Type u) [CommRing P] [Algebra A P]
  (B : Type u) [CommRing B] [Algebra A B] [Algebra P B] [IsScalarTower A P B]

/-- Extension of scalars along `P → B` in the sense of `ModuleCat.extendScalars` tensors with
`B` regarded as a `P`-module through `Module.compHom`; the identity identifies that factor with
`B` itself, hence the carrier with the algebra tensor product `B ⊗[P] M`. -/
private def extendScalarsObjIso (M : ModuleCat.{u} P) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap P B)).obj M ≅
      ModuleCat.of B (B ⊗[P] M) :=
  let X := (ModuleCat.restrictScalars (algebraMap P B)).obj (ModuleCat.of B B)
  have : IsScalarTower P B X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : X ≃ₗ[B] B := LinearEquiv.refl B B
  (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl P M)).toModuleIso

/-- Every term of the single complex of a projective module is projective: the term in degree `0`
is the module and the others are zero. -/
private theorem projective_singleFunctor_obj_X (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    [CategoryTheory.Projective M] (i : ℤ) :
    CategoryTheory.Projective
      (((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M).X i) := by
  by_cases hi : i = 0
  · subst hi
    exact Projective.of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm inferInstance
  · exact Projective.of_iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi).isoZero.symm
      inferInstance

/-- **The cotangent complex of a chart, for given triangles.**

Let `A → P → B` be ring maps with `P` a polynomial algebra over `A` and `P → B` étale. Then
`L_{B/A} = Ω[B⁄A][0]` in `D(B)`.

This is the statement the standard smooth case is deduced from in
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth`, where
the chart is built rather than assumed. `Algebra.IsPolynomialAlgebra` allows an arbitrary type of
variables, so the hypothesis here is not merely the standard smooth case.

The two triangle parameters are instances of Proposition 08QX, which
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale_unconditional`
supplies from `CommAlgCat.productFundamentalTriangle_distinguished`.

* `hT` is the distinguished triangle of the display of Equation 92.7.0.1 for the tower
  `A → P → B`. It is what Lemma 08R3 consumes, in the form
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero`, to turn
  `L_{B/P} = 0` into `L_{B/A} = L_{P/A} ⊗^𝐋_P B`.
* `hT'` is the distinguished triangle of the same display for the tower `B → B ⊗_P B → B`, which
  `CommAlgCat.isZero_cotangentComplexDerived_of_etale` — Lemma 08R2 item (5) — takes on its way
  through Lemma 08R1.

The hypothesis `hP` and the instance `Algebra.Etale P B` are both load-bearing: `hP` is the
input to Lemma 08QH and the source of the projectivity of `Ω[P⁄A]` that makes the termwise
extension of scalars compute the derived one, and étaleness supplies both the vanishing of
`L_{B/P}` through Lemma 08R2 item (5) and, through
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, the identification of `B ⊗_P Ω[P⁄A]`
with `Ω[B⁄A]`. -/
theorem nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale
    (hP : Algebra.IsPolynomialAlgebra A P) [Algebra.Etale P B]
    {α : fundamentalVertex₁.{u, u} A P B ⟶ fundamentalVertex₂.{u, u} A B}
    {β : fundamentalVertex₂.{u, u} A B ⟶ fundamentalVertex₃.{u, u} P B}
    {γ : fundamentalVertex₃.{u, u} P B ⟶ (fundamentalVertex₁.{u, u} A P B)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} B)))
    {α' : fundamentalVertex₁.{u, u} B (B ⊗[P] B) B ⟶ fundamentalVertex₂.{u, u} B B}
    {β' : fundamentalVertex₂.{u, u} B B ⟶ fundamentalVertex₃.{u, u} (B ⊗[P] B) B}
    {γ' : fundamentalVertex₃.{u, u} (B ⊗[P] B) B ⟶
      (fundamentalVertex₁.{u, u} B (B ⊗[P] B) B)⟦(1 : ℤ)⟧}
    (hT' : Triangle.mk α' β' γ' ∈ distTriang (DerivedCategory (ModuleCat.{u} B))) :
    Nonempty
      (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
          (ModuleCat.of B (KaehlerDifferential A B))) := by
  -- Lemma 08R2 item (5): `L_{B/P} = 0`, `P → B` being étale.
  have hzero : IsZero (fundamentalVertex₃.{u, u} P B) :=
    isZero_cotangentComplexDerived_of_etale P B hT'
  -- Lemma 08R3: a vanishing third vertex makes the first arrow invertible.
  obtain ⟨e₁⟩ :=
    nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero.{u, u} A P B hT hzero
  -- Lemma 08QH: `L_{P/A} = Ω[P⁄A][0]`.
  obtain ⟨e₂⟩ := cotangentComplex_iso_kaehlerDifferential A (CommAlgCat.of A P) hP
  -- `Ω[P⁄A]` is projective, so its single complex is a bounded-above complex of projectives and
  -- the termwise extension of scalars along `P → B` computes the derived one.
  have : CategoryTheory.Projective (ModuleCat.of P (KaehlerDifferential A P)) :=
    have := KaehlerDifferential.projective_of_isPolynomialAlgebra hP
    inferInstance
  set M : ModuleCat.{u} P := ModuleCat.of P (KaehlerDifferential A P)
  set K := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M
  have : ∀ i, CategoryTheory.Projective (K.X i) := projective_singleFunctor_obj_X P M
  set F := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap P B)
  have : IsIso (F.comparison.app K) := F.comparison_isIso_of_projective K 0
  let e₃ : F.functor.obj (DerivedCategory.Q.obj K) ≅
      (CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral
        (algebraMap P B)).obj K := asIso (F.comparison.app K)
  -- Termwise extension of scalars of a single complex is the single complex of the extension.
  let e₄ := DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.extendScalars.{u, u, u} (algebraMap P B)) (ComplexShape.up ℤ) 0).app M)
  -- `B ⊗_P Ω[P⁄A] = Ω[B⁄A]`, `P → B` being formally étale.
  let e₅ := (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso
    (extendScalarsObjIso P B M ≪≫
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A P B).toModuleIso)
  exact ⟨e₁.symm ≪≫ F.functor.mapIso e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅⟩

end Chart

section StandardSmooth

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- The diagonal tower `B → B ⊗_P B → B` is a tower of rings: the composite of `b ↦ b ⊗ 1` with
the multiplication map is the identity. Needed because `CommAlgCat.diagonalAlgebra` supplies the
algebra structure on `B` over `B ⊗_P B` but nothing supplies the tower condition. -/
private theorem isScalarTower_diagonal (P : Type u) [CommRing P] [Algebra P B] :
    IsScalarTower B (B ⊗[P] B) B := by
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun b => ?_).symm
  rw [RingHom.comp_apply, algebraMap_diagonalAlgebra]
  simp

/-- **The cotangent complex of a standard smooth ring map, for given triangles.**

Let `A → B` be standard smooth. Then `L_{B/A} = Ω[B⁄A][0]` in `D(B)`.

The chart `A → A[x_1, …, x_n] → B` with étale second map is *built*, not assumed: it is Mathlib's
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`, which is the content of the source's appeal
to Algebra, Lemma 00TA. The conclusion is then
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale`.

The parameter `hQX : CommAlgCat.HasFundamentalTriangles` is Proposition 08QX in quantified form,
because the two towers it is needed for — `A → A[x_1, …, x_n] → B` and
`B → B ⊗_{A[x_1, …, x_n]} B → B` — are built inside the proof. It is supplied in
`nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth_unconditional`
in `CommAlgCat`.
The smooth case, [Stacks, Tag 08R5], is
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`. -/
theorem nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth
    [Algebra.IsStandardSmooth A B] (hQX : HasFundamentalTriangles.{u}) :
    Nonempty
      (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
          (ModuleCat.of B (KaehlerDifferential A B))) := by
  -- Algebra, Lemma 00TA: a chart `A → A[x_1, …, x_n] → B` with étale second map.
  obtain ⟨n, g, hgC, hg⟩ :=
    (RingHom.isStandardSmooth_algebraMap.2 ‹Algebra.IsStandardSmooth A B›)
      |>.exists_etale_mvPolynomial
  let _ : Algebra (MvPolynomial (Fin n) A) B := g.toAlgebra
  have hmap : algebraMap (MvPolynomial (Fin n) A) B = g := RingHom.algebraMap_toAlgebra g
  have : Algebra.Etale (MvPolynomial (Fin n) A) B := RingHom.etale_algebraMap.1 (hmap ▸ hg)
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq' (by rw [hmap, ← hgC]; rfl)
  have : IsScalarTower B (B ⊗[MvPolynomial (Fin n) A] B) B :=
    isScalarTower_diagonal B (MvPolynomial (Fin n) A)
  -- Proposition 08QX for the two towers the chart produces.
  obtain ⟨α, β, γ, hT⟩ := hQX A (MvPolynomial (Fin n) A) B
  obtain ⟨α', β', γ', hT'⟩ := hQX B (B ⊗[MvPolynomial (Fin n) A] B) B
  exact nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale
    A (MvPolynomial (Fin n) A) B
    ⟨ULift.{u} (Fin n), ⟨MvPolynomial.renameEquiv A Equiv.ulift⟩⟩ hT hT'

end StandardSmooth

end CommAlgCat

end
