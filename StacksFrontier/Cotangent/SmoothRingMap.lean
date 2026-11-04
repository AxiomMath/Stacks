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

This file proves that lemma for a **standard smooth** ring map, and — as the lemma the standard
smooth case is deduced from — for a ring map presented by a *chart*, that is a factorization
`A → P → B` with `P` a polynomial algebra over `A` and `P → B` étale. The step from standard
smooth to smooth, which in the source is a localization argument, is not available here; see the
implementation notes.

## Main results

* `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale`:
  **[Stacks, Tag 08R5]** for a chart `A → P → B`, with two carried instances of the fundamental
  distinguished triangle.
* `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth`:
  **[Stacks, Tag 08R5]** for `Algebra.IsStandardSmooth A B`, and the covering declaration for
  the section tag **[Stacks, Tag 08R4]**. The chart is produced rather than assumed; what is
  carried instead is `CommAlgCat.HasFundamentalTriangles`.

## Implementation notes

*The source's proof and the part of it carried out here.* The source argues: the agreement in
cohomological degree `0` is Lemma 08QF; it therefore suffices to kill the other cohomology
groups, which is local on `Spec(B)` because `L_{B_g/A} = (L_{B/A})_g` by Lemma 08R3; so one may
assume `A → B` standard smooth by Algebra, Lemma 00TA, that is, that `A → B` factors as
`A → A[x_1, …, x_n] → B` with `A[x_1, …, x_n] → B` étale; and then Lemmas 08R2 and 08R3 give
`L_{B/A} = L_{A[x_1, …, x_n]/A} ⊗ B`, whence the conclusion by Lemma 08QH.

Everything from the standard smooth case onwards is carried out. Lemma 08R2 item (5) gives
`L_{B/P} = 0` because `P → B` is étale, Lemma 08R3 then identifies `L_{B/A}` with
`L_{P/A} ⊗^𝐋_P B`, and Lemma 08QH identifies `L_{P/A}` with `Ω[P⁄A][0]`. Since `Ω[P⁄A]` is a
free, hence projective, `P`-module, the derived base change of that single complex is computed by
the termwise one, and `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale` identifies
`B ⊗_P Ω[P⁄A]` with `Ω[B⁄A]`. The full isomorphism in `D(B)` comes out at once rather than degree
by degree, so Lemma 08QF is not needed here as a separate step: the degree-`0` agreement comes
with the rest.

*The chart is produced, not assumed.* Mathlib proves that a standard smooth algebra factors
through a polynomial algebra with étale second map, as
`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` (and for a ring map,
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`), which is exactly the source's
"we can factor `A → B` as `A → A[x_1, …, x_n] → B` with `A[x_1, …, x_n] → B` étale". So the
chart hypothesis of the first result is discharged in the second, and the second assumes only
`Algebra.IsStandardSmooth A B`. The `Fin n` of Mathlib's statement is transported to
`ULift (Fin n)` by `MvPolynomial.renameEquiv` to meet the universe of
`Algebra.IsPolynomialAlgebra`.

*What still separates this from the smooth case.* Lemma 00TA is available, as
`Algebra.Smooth.exists_span_eq_top_isStandardSmooth_and_syntomic` in
`StacksFrontier.RingTheory.Smooth.Syntomic`, and it produces for a smooth `A → B` a set `s` with
`Ideal.span s = ⊤` such that `Algebra.IsStandardSmooth A (Localization.Away g)` for every
`g ∈ s`. Combined with the second result below that already gives the conclusion of Lemma 08R5
for each `B_g`. Two steps are then missing, and neither is a matter of assembly.

1. `L_{B_g/A} = (L_{B/A})_g` is Lemma 08R3 for the tower `A → B → B_g` together with
   `L_{B_g/B} = 0`, which is Lemma 08R2 item (3) — a localization is a flat epimorphism. The
   implementation notes of `StacksFrontier.Cotangent.EtaleVanishing` record that item (3) is *not*
   claimed there: flatness is Mathlib's `IsLocalization.flat`, but no declaration in this library
   or in Mathlib makes a localization an epimorphism of rings, which is what
   `CommAlgCat.isZero_cotangentComplexDerived_of_flat_of_bijective` consumes.
2. Even granting that, passing from the local statements over a standard open cover of `Spec(B)`
   to one isomorphism in `D(B)` is a descent statement for objects of a derived category along a
   Zariski cover, and this library has nothing of the kind for `L_{B/A}`.

Neither result below is therefore the full smooth case, and neither is a weakening of the
conclusion: the conclusion is the source's, in the spelling Tag 08QH uses.

*The carried hypotheses.* All of them are instances of, or the whole of, Proposition 08QX — that
the three vertices of the display of Equation 92.7.0.1 form a distinguished triangle for
arbitrary ring maps `A → B → C`. It is not formalized in this library; see the
`No @[stacks 08QX]` section of `StacksFrontier.Cotangent.Triangle.Distinguished` for the three steps
that are missing. No `@[stacks 08QX]` attribute is claimed here. The first result carries two
specific instances, in the shape Proposition 08QX gives them and exactly as
`CommAlgCat.isIso_of_isZero_fundamentalVertex₃` and
`CommAlgCat.isZero_cotangentComplexDerived_of_etale` already do; the second carries the
proposition itself, as `CommAlgCat.HasFundamentalTriangles`, because the chart it builds is not
in scope when the statement is read and so no particular instance can be named in it. Neither
can be avoided: the triangle for `A → P → B` is the input to Lemma 08R3, and the triangle for
`B → B ⊗_P B → B` is the input Lemma 08R2 item (5) passes on to Lemma 08R1. The other form of
Lemma 08R3 in `StacksFrontier.Cotangent.Triangle.VanishingVertex`, which carries no triangle, needs
`P → B` injective and reads the vanishing hypothesis at the third vertex of the triangle of Tag
08SD rather than at `L_{B/P}`; identifying the two is the "key fact" of Tag 08SD, which rests on
Tag 08RX and is unavailable, so it is no cheaper here.

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
  carried hypotheses are instances of.
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

This is the statement of Proposition 08QX, which is not formalized in this library — see the
`No @[stacks 08QX]` section of `StacksFrontier.Cotangent.Triangle.Distinguished`. It is recorded
here as a `Prop` so that it can be carried as a hypothesis by a statement which builds the tower
it is needed for, and therefore cannot name the particular instance it uses. No
`@[stacks 08QX]` attribute is claimed for it: proving it is other work. -/
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

/-- **Stacks Project, Tag 08R5**, for a ring map presented by a chart.

Let `A → P → B` be ring maps with `P` a polynomial algebra over `A` and `P → B` étale. Then
`L_{B/A} = Ω[B⁄A][0]` in `D(B)`.

This is the lemma the standard smooth case is deduced from in
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth`, where
the chart is built rather than assumed. It is kept separate because its carried hypotheses are
two named instances of Proposition 08QX rather than the whole proposition, and because
`Algebra.IsPolynomialAlgebra` allows an arbitrary type of variables, so the hypothesis here is
not merely the standard smooth case.

Two hypotheses are carried, and both are instances of Proposition 08QX, which is not formalized
in this library (see the `No @[stacks 08QX]` section of
`StacksFrontier.Cotangent.Triangle.Distinguished`); no `@[stacks 08QX]` is claimed anywhere here.

* `hT` is the distinguished triangle of the display of Equation 92.7.0.1 for the tower
  `A → P → B`. It is what Lemma 08R3 consumes, in the form
  `CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero`, to turn
  `L_{B/P} = 0` into `L_{B/A} = L_{P/A} ⊗^𝐋_P B`. Proposition 08QX would discharge it.
* `hT'` is the distinguished triangle of the same display for the tower `B → B ⊗_P B → B`. It is
  the hypothesis that `CommAlgCat.isZero_cotangentComplexDerived_of_etale` — Lemma 08R2 item (5)
  — already carries, on its way through Lemma 08R1, and it is passed straight through.
  Proposition 08QX would discharge it too.

The hypothesis `hP` and the instance `Algebra.Etale P B` are both load-bearing: `hP` is the
input to Lemma 08QH and the source of the projectivity of `Ω[P⁄A]` that makes the termwise
extension of scalars compute the derived one, and étaleness supplies both the vanishing of
`L_{B/P}` through Lemma 08R2 item (5) and, through
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`, the identification of `B ⊗_P Ω[P⁄A]`
with `Ω[B⁄A]`. -/
@[stacks 08R5 "the lemma for a ring map `A → B` presented by a CHART: a factorization \
`A → P → B` with `P` a polynomial algebra over `A` and `P → B` étale. This is the lemma from \
which the standard-smooth case is deduced in \
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth`, \
which carries the 08R4 tag as well; neither is the FULL SMOOTH case, the localization step of \
the source's proof being unavailable (it needs Lemma 08R2 item (3), which \
`StacksFrontier.Cotangent.EtaleVanishing` records as not claimed, and a Zariski-descent statement \
in `D(B)`). TWO carried hypotheses, both instances of Proposition 08QX (NOT formalized here, \
and no `@[stacks 08QX]` is claimed): `hT`, the fundamental triangle of `A → P → B`, which \
Lemma 08R3 consumes, and `hT'`, the fundamental triangle of `B → B ⊗_P B → B`, which \
`CommAlgCat.isZero_cotangentComplexDerived_of_etale` (Lemma 08R2 item (5)) already carries and \
which is passed through. The conclusion is the source's, `L_{B/A} = Ω_{B/A}[0]`, read as an \
isomorphism in `D(B)` in the same spelling as Tag 08QH"]
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

/-- **Stacks Project, Tag 08R5** for a standard smooth ring map, and the covering declaration
for the section tag **08R4**.

Let `A → B` be standard smooth. Then `L_{B/A} = Ω[B⁄A][0]` in `D(B)`.

The chart `A → A[x_1, …, x_n] → B` with étale second map is *built*, not assumed: it is Mathlib's
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`, which is the content of the source's appeal
to Algebra, Lemma 00TA. The conclusion is then
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale`.

One hypothesis is carried, `hQX : CommAlgCat.HasFundamentalTriangles`, which is Proposition 08QX
— the display of Equation 92.7.0.1 is a distinguished triangle for every tower of ring maps.
Proposition 08QX is not formalized in this library (see the `No @[stacks 08QX]` section of
`StacksFrontier.Cotangent.Triangle.Distinguished`) and no `@[stacks 08QX]` attribute is claimed for
it here. It is carried as the whole proposition rather than as named instances because the two
towers it is needed for — `A → A[x_1, …, x_n] → B` and `B → B ⊗_{A[x_1, …, x_n]} B → B` — are
built inside the proof and so cannot be referred to in the statement.

This is **not** the full smooth case of Lemma 08R5. Lemma 00TA is available, and gives a standard
open cover of `Spec(B)` on which a smooth `A → B` is standard smooth, so this result applies to
each `B_g`; what is missing is `L_{B_g/A} = (L_{B/A})_g`, which needs Lemma 08R2 item (3), and
descent along the cover in `D(B)`. See the module docstring. -/
@[stacks 08R4 "the SECTION tag `\\section{Smooth ring maps}`; its lemma is 08R5", stacks 08R5 "\
the lemma for a STANDARD SMOOTH ring map, `Algebra.IsStandardSmooth A B`. The chart \
`A → A[x_1, …, x_n] → B` with étale second map is BUILT, not assumed — it is Mathlib's \
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`, which is the content of the source's \
appeal to Algebra, Lemma 00TA — and the conclusion then comes from \
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale`, which carries \
the 08R5 tag too. This is NOT the full smooth case: Lemma 00TA gives a cover of `Spec(B)` on \
which a smooth map is standard smooth, so this applies to each `B_g`, but \
`L_{B_g/A} = (L_{B/A})_g` needs Lemma 08R2 item (3) (which \
`StacksFrontier.Cotangent.EtaleVanishing` records as not claimed) and descent along the cover in \
`D(B)` is absent. ONE carried hypothesis, `hQX : CommAlgCat.HasFundamentalTriangles`, which is \
Proposition 08QX itself, carried whole rather than as instances because the towers it is needed \
for are built inside the proof; 08QX is NOT formalized in this library and no \
`@[stacks 08QX]` is claimed here. The conclusion is the source's, `L_{B/A} = Ω_{B/A}[0]`, read \
as an isomorphism in `D(B)` in the same spelling as Tag 08QH. As for 08R4: the section's only \
mathematical content is Lemma 08R5, so this declaration covers it; the definitional remark \
opening the section introduces `weakly quasi-regular` ring maps only to say what a \
generalization of Lemma 08R2 would look at, and the source then says `For the moment we just \
stick to smooth ring maps`, so it states no result and nothing is defined for it"]
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
