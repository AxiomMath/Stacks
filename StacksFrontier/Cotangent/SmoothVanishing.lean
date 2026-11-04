module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import StacksFrontier.Cotangent.EtaleVanishing
public import StacksFrontier.Cotangent.Triangle.VanishingVertex
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso

/-!
# The cotangent complex of a smooth ring map

For a smooth ring map `A → B` the cotangent complex `L_{B/A}` is concentrated in cohomological
degree `0`, where it is the module of Kähler differentials: `L_{B/A} = Ω[B⁄A][0]` in `D(B)`.
This is Lemma 92.9.1 of the Stacks Project, [Stacks, Tag 08R5].

## Main results

* `CommAlgCat.isZero_homology_cotangentComplex_of_etale_mvPolynomial`: for a tower
  `A → A[σ] → B` whose second map is étale, `Hⁱ(L_{B/A}) = 0` for every `i ≠ 0`.
* `CommAlgCat.isZero_homology_cotangentComplex_of_isStandardSmooth`: the same for a standard
  smooth `A → B`.
* `CommAlgCat.isZero_homology_cotangentComplex_of_smooth`: **[Stacks, Tag 08R5]**, the vanishing
  of `Hⁱ(L_{B/A})` for `i ≠ 0` when `A → B` is smooth.
* `CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmooth`: **[Stacks, Tag 08R5]** in
  full, the isomorphism `L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)`, with
  `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_smooth` its existence
  form.

## Implementation notes

*The shape of the statement.* The source's equality `L_{B/A} = Ω_{B/A}[0]` is read as an
isomorphism in the derived category of `B`-modules, between `L_{B/A}` and the module of Kähler
differentials placed in degree `0`. Degree `0` already agrees by
`CommAlgCat.cotangentComplex_homologyZeroIso`, [Stacks, Tag 08QF]; the content is that every
other cohomology vanishes, and the two are assembled through the t-structure on `D(B)`: a
complex which is both `IsLE 0` and `IsGE 0` is a single module in degree `0`, and that module is
identified with `Ω[B⁄A]` by its degree-`0` cohomology.

*The one carried hypothesis.* Proposition 08QX — that the three vertices
`L_{B/A} ⊗^𝐋_B C`, `L_{C/A}`, `L_{C/B}` of a tower `A → B → C` form a distinguished triangle —
is not formalized in this library; see the `No @[stacks 08QX]` section of
`StacksFrontier.Cotangent.Triangle.Distinguished`. Both
`CommAlgCat.isZero_cotangentComplexDerived_of_etale` ([Stacks, Tag 08R2] item (5)) and
`CommAlgCat.nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero` ([Stacks, Tag 08R3])
therefore take the triangle of a single tower as a hypothesis. The proof below needs that
triangle for several towers whose members are only produced during the argument — the polynomial
subalgebra of a standard smooth presentation, the localizations of `B` at a covering family, and
the diagonal towers of the étale maps involved — so the hypothesis is carried in the quantified
form `CommAlgCat.HasFundamentalTriangle`, carried as `h08QX`, which is Tag 08QX itself for
towers of rings in one universe. It is a theorem of the source and not an extra condition on
`A → B`; nothing beyond it is assumed, and smoothness is load-bearing everywhere it is used.
The quantified shape is forced rather than chosen: the towers at which Tag 08QX is used are
`A → B → B_f` for every `f` in a spanning set that smoothness produces,
`A → A[ULift (Fin n_f)] → B_f` for a polynomial index set whose size depends on `f`, and the
diagonal tower of each of those étale maps, so they cannot be enumerated in the statement.

*The reduction.* The vanishing is local on `Spec B`. Mathlib's
`Algebra.Smooth.exists_span_eq_top_isStandardSmooth` covers `Spec B` by basic opens `D(f)` on
which `B` is standard smooth over `A`, `Module.eq_zero_of_isLocalized_span` reduces vanishing of
a `B`-module to vanishing of its localizations at such a family, and
`CochainComplex.DerivedTensor.derivedExtensionScalarsAwayHomologyIso` identifies
`(Hⁱ(L_{B/A}))_f` with `Hⁱ(L_{B/A} ⊗^𝐋_B B_f)`, which Tag 08R3 identifies with `Hⁱ(L_{B_f/A})`
because `B → B_f` is étale. On a standard smooth algebra
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial` factors `A → B` as `A → A[σ] → B` with the
second map étale, Tag 08R3 gives `L_{B/A} = L_{A[σ]/A} ⊗^𝐋_{A[σ]} B`, and since an étale map is
flat the cohomology of that derived base change is the extension of scalars of the cohomology of
`L_{A[σ]/A}`, which is a single module in degree `0` by [Stacks, Tag 08QH].

## References

* [Stacks Project, Tag 08R5](https://stacks.math.columbia.edu/tag/08R5), Lemma 92.9.1.
* [Stacks Project, Tag 08QF](https://stacks.math.columbia.edu/tag/08QF), degree `0`.
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH), the polynomial case.
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), vanishing for an étale
  map.
* [Stacks Project, Tag 08R3](https://stacks.math.columbia.edu/tag/08R3), the vanishing vertex.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle.
* [Stacks Project, Tag 00TA](https://stacks.math.columbia.edu/tag/00TA), a smooth ring map is
  standard smooth on a cover, through Mathlib's
  `Algebra.Smooth.exists_span_eq_top_isStandardSmooth`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace DerivedCategory

/-- An object of the derived category which is a single module in degree `0` has no cohomology
outside degree `0`. -/
theorem isZero_homologyFunctor_singleFunctor_obj (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
      ((singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact isZero_of_isGE _ 0 i h
  · exact isZero_of_isLE _ 0 i h

end DerivedCategory

namespace ModuleCat

/-- A module over `R` is zero as soon as its localizations at the elements of a family generating
the unit ideal are all zero. -/
theorem isZero_of_span_eq_top_of_isZero_localizedModule {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (s : Set R) (hs : Ideal.span s = ⊤)
    (h : ∀ f ∈ s, IsZero (ModuleCat.of R (LocalizedModule (Submonoid.powers f) M))) :
    IsZero M := by
  refine isZero_iff_subsingleton.mpr (subsingleton_of_forall_eq 0 fun x => ?_)
  refine Module.eq_zero_of_isLocalized_span s hs
    (fun r : s => LocalizedModule (Submonoid.powers r.1) M)
    (fun r : s => LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) x (fun r => ?_)
  exact (isZero_iff_subsingleton.mp (h r.1 r.2)).elim _ _

end ModuleCat

namespace CommAlgCat

attribute [local instance] diagonalAlgebra

/-- **Proposition 08QX for towers of rings in a single universe.** Every tower `A → B → C`
admits a distinguished triangle `L_{B/A} ⊗^𝐋_B C ⟶ L_{C/A} ⟶ L_{C/B} ⟶ (L_{B/A} ⊗^𝐋_B C)[1]`
on the vertices of the fundamental display of Equation 92.7.0.1. -/
def HasFundamentalTriangle : Prop :=
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Algebra B C] [IsScalarTower A B C],
    ∃ (α : fundamentalVertex₁.{u, u} A B C ⟶ fundamentalVertex₂.{u, u} A C)
      (β : fundamentalVertex₂.{u, u} A C ⟶ fundamentalVertex₃.{u, u} B C)
      (γ : fundamentalVertex₃.{u, u} B C ⟶ (fundamentalVertex₁.{u, u} A B C)⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} C))

/-- **[Stacks, Tag 08R2] item (5)**, with the triangle supplied by Proposition 08QX. If `P → B`
is étale then `L_{B/P} = 0` in `D(B)`. -/
theorem isZero_cotangentComplexDerived_of_etale_of_hasFundamentalTriangle
    (h08QX : HasFundamentalTriangle.{u}) (P : Type u) [CommRing P] (B : Type u) [CommRing B]
    [Algebra P B] [Algebra.Etale P B] :
    IsZero (cotangentComplexDerived.{u, u} P (CommAlgCat.of P B)) := by
  have : IsScalarTower B (B ⊗[P] B) B :=
    IsScalarTower.of_algebraMap_eq (fun b => by rw [algebraMap_diagonalAlgebra]; simp)
  obtain ⟨α, β, γ, hT⟩ := h08QX B (B ⊗[P] B) B
  exact isZero_cotangentComplexDerived_of_etale P B hT

/-- For a tower `A → B → C` with `B → C` étale, `L_{B/A} ⊗^𝐋_B C ≅ L_{C/A}` in `D(C)`. -/
private theorem nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_etale
    (h08QX : HasFundamentalTriangle.{u}) (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Algebra.Etale B C] :
    Nonempty (fundamentalVertex₁.{u, u} A B C ≅ fundamentalVertex₂.{u, u} A C) := by
  obtain ⟨α, β, γ, hT⟩ := h08QX A B C
  exact nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_isZero A B C hT
    (isZero_cotangentComplexDerived_of_etale_of_hasFundamentalTriangle h08QX B C)

/-- If `A → B` factors as `A → A[σ] → B` with `A[σ] → B` étale, the cotangent complex `L_{B/A}`
has no cohomology outside degree `0`.

By [Stacks, Tag 08R2] the cotangent complex of `A[σ] → B` vanishes, so [Stacks, Tag 08R3]
identifies `L_{B/A}` with `L_{A[σ]/A} ⊗^𝐋_{A[σ]} B`; an étale map is flat, so cohomology
commutes with that base change, and `L_{A[σ]/A}` is `Ω[A[σ]⁄A][0]` by [Stacks, Tag 08QH]. -/
theorem isZero_homology_cotangentComplex_of_etale_mvPolynomial
    (h08QX : HasFundamentalTriangle.{u}) (A : Type u) [CommRing A] (σ : Type u) (B : Type u)
    [CommRing B] [Algebra A B] [Algebra (MvPolynomial σ A) B]
    [IsScalarTower A (MvPolynomial σ A) B] [Algebra.Etale (MvPolynomial σ A) B]
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((cotangentComplex A (CommAlgCat.of A B)).homology i) := by
  obtain ⟨e⟩ := nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_etale h08QX A
    (MvPolynomial σ A) B
  obtain ⟨eP⟩ := cotangentComplex_iso_kaehlerDifferential A
    (CommAlgCat.of A (MvPolynomial σ A)) ⟨σ, ⟨AlgEquiv.refl⟩⟩
  have hP : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (MvPolynomial σ A)) i).obj
      (cotangentComplexDerived.{u, u} A (CommAlgCat.of A (MvPolynomial σ A)))) :=
    IsZero.of_iso (DerivedCategory.isZero_homologyFunctor_singleFunctor_obj _ _ i hi)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (MvPolynomial σ A)) i).mapIso eP)
  have hflat : (algebraMap (MvPolynomial σ A) B).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).app
    (cotangentComplex A (CommAlgCat.of A B))).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso e).symm
  refine IsZero.of_iso ?_ ((CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso
      (algebraMap (MvPolynomial σ A) B) hflat i).app
    (cotangentComplexDerived.{u, u} A (CommAlgCat.of A (MvPolynomial σ A))))
  exact (ModuleCat.extendScalars (algebraMap (MvPolynomial σ A) B)).map_isZero hP

/-- For a standard smooth ring map `A → B` the cotangent complex `L_{B/A}` has no cohomology
outside degree `0`.

A standard smooth ring map factors as `A → A[x₁, …, xₙ] → B` with the second map étale, by
Mathlib's `RingHom.IsStandardSmooth.exists_etale_mvPolynomial`. -/
theorem isZero_homology_cotangentComplex_of_isStandardSmooth
    (h08QX : HasFundamentalTriangle.{u}) (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Algebra.IsStandardSmooth A B] (i : ℤ) (hi : i ≠ 0) :
    IsZero ((cotangentComplex A (CommAlgCat.of A B)).homology i) := by
  obtain ⟨n, g₀, hcomp, hEtale⟩ :=
    RingHom.IsStandardSmooth.exists_etale_mvPolynomial (f := algebraMap A B)
      ((RingHom.isStandardSmooth_algebraMap (R := A) (S := B)).2 inferInstance)
  let e : MvPolynomial (ULift.{u} (Fin n)) A ≃ₐ[A] MvPolynomial (Fin n) A :=
    MvPolynomial.renameEquiv A Equiv.ulift
  let g : MvPolynomial (ULift.{u} (Fin n)) A →+* B := g₀.comp e.toRingEquiv.toRingHom
  let : Algebra (MvPolynomial (ULift.{u} (Fin n)) A) B := g.toAlgebra
  have : IsScalarTower A (MvPolynomial (ULift.{u} (Fin n)) A) B :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      show algebraMap A B a = g₀ (e (algebraMap A (MvPolynomial (ULift.{u} (Fin n)) A) a))
      rw [e.commutes]
      exact congrArg (fun h : A →+* B => h a) hcomp.symm)
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) A) B :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective e.bijective) hEtale
  exact isZero_homology_cotangentComplex_of_etale_mvPolynomial h08QX A
    (ULift.{u} (Fin n)) B i hi

/-- Cohomology of the cotangent complex localizes: if `Hⁱ(L_{B_f/A})` vanishes for the
localization `B_f` of `B` at a single element `f`, then the localization of `Hⁱ(L_{B/A})` at `f`
vanishes.

The map `B → B_f` is étale, so [Stacks, Tag 08R3] identifies `L_{B_f/A}` with
`L_{B/A} ⊗^𝐋_B B_f`, whose cohomology is the localization of the cohomology of `L_{B/A}`. -/
theorem isZero_localizedModule_homology_cotangentComplex
    (h08QX : HasFundamentalTriangle.{u}) (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] (f : B) (i : ℤ)
    (h : IsZero ((cotangentComplex A (CommAlgCat.of A (Localization.Away f))).homology i)) :
    IsZero (ModuleCat.of B (LocalizedModule (Submonoid.powers f)
      ((cotangentComplex A (CommAlgCat.of A B)).homology i))) := by
  have : Algebra.Etale B (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  obtain ⟨e⟩ := nonempty_fundamentalVertex₁_iso_fundamentalVertex₂_of_etale h08QX A B
    (Localization.Away f)
  have hD : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away f)) i).obj (cotangentComplexDerivedBaseChange.{u, u} A
        (CommAlgCat.of A B) (Localization.Away f))) := by
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away f)) i).mapIso e)
    exact IsZero.of_iso h ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} (Localization.Away f)) i).app _)
  have hL : IsZero ((CochainComplex.DerivedTensor.localizedModuleFunctor
      (Submonoid.powers f)).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)))) := by
    refine IsZero.of_iso ?_
      ((CochainComplex.DerivedTensor.derivedExtensionScalarsAwayHomologyIso f i).app
        (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B))).symm
    exact (ModuleCat.restrictScalars (algebraMap B (Localization.Away f))).map_isZero hD
  exact IsZero.of_iso hL ((CochainComplex.DerivedTensor.localizedModuleFunctor
    (Submonoid.powers f)).mapIso ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} B) i).app (cotangentComplex A (CommAlgCat.of A B))).symm)

/-- **[Stacks, Tag 08R5], the vanishing.** For a smooth ring map `A → B` the cotangent complex
`L_{B/A}` has no cohomology outside degree `0`.

A smooth ring map is standard smooth on a cover of `Spec B` by basic opens, [Stacks, Tag 00TA],
and the cohomology of `L_{B/A}` is a `B`-module whose localizations along that cover vanish. -/
@[stacks 08R5 "the vanishing: `Hⁱ(L_{B/A}) = 0` for every `i ≠ 0`, which together with Tag \
08QF in degree 0 is the lemma. One carried hypothesis `h08QX`: Tag 08QX, that the fundamental \
triangle is distinguished, which is not formalized in this library; it is quantified over towers \
because the towers are produced by the proof itself and cannot be enumerated"]
theorem isZero_homology_cotangentComplex_of_smooth (h08QX : HasFundamentalTriangle.{u})
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((cotangentComplex A (CommAlgCat.of A B)).homology i) := by
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth A B
  refine ModuleCat.isZero_of_span_eq_top_of_isZero_localizedModule _ s hs fun f hf => ?_
  have : Algebra.IsStandardSmooth A (Localization.Away f) := hstd f hf
  exact isZero_localizedModule_homology_cotangentComplex h08QX A B f i
    (isZero_homology_cotangentComplex_of_isStandardSmooth h08QX A (Localization.Away f) i hi)

/-- **[Stacks, Tag 08R5].** For a smooth ring map `A → B`, the identification
`L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)` of the cotangent complex with the module of Kähler
differentials placed in cohomological degree `0`.

The cohomology vanishes outside degree `0` and is `Ω[B⁄A]` in degree `0` by [Stacks, Tag 08QF],
so the t-structure on `D(B)` exhibits `L_{B/A}` as a single module in degree `0`. -/
@[stacks 08R5 "the lemma in full and as data: the isomorphism `L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)`. \
One carried hypothesis `h08QX`: Tag 08QX, not formalized in this library. Nothing else is \
assumed, and the conclusion is the source's whole equality rather than only its degree 0 part"]
noncomputable def cotangentComplexDerivedIsoKaehlerDifferentialOfSmooth
    (h08QX : HasFundamentalTriangle.{u}) (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] :
    cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (KaehlerDifferential A B)) := by
  have hLE : (cotangentComplex A (CommAlgCat.of A B)).IsStrictlyLE 0 :=
    ((cotangentComplex A (CommAlgCat.of A B)).isStrictlyLE_iff 0).2
      fun i hi => cotangentComplex_isZero_pos A (CommAlgCat.of A B) i hi
  have hGE : (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)).IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact IsZero.of_iso (isZero_homology_cotangentComplex_of_smooth h08QX A B i (by omega))
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).app _)
  have hLE' : (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)).IsLE 0 :=
    (DerivedCategory.isLE_Q_obj_iff _ 0).2 inferInstance
  let hex := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) 0
  let Y : ModuleCat.{u} B := hex.choose
  let e : cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj Y :=
    hex.choose_spec.some
  refine e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso ?_
  refine (((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).app Y).symm) ≪≫ ?_
  exact (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) 0).app _ ≪≫
    cotangentComplex_homologyZeroIso A (CommAlgCat.of A B)

/-- **[Stacks, Tag 08R5].** For a smooth ring map `A → B` the cotangent complex `L_{B/A}` is
isomorphic in `D(B)` to the module of Kähler differentials placed in cohomological degree `0`:
`L_{B/A} = Ω[B⁄A][0]`. This is the existence form of
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmooth`. -/
theorem nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_smooth
    (h08QX : HasFundamentalTriangle.{u}) (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] :
    Nonempty (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (KaehlerDifferential A B))) :=
  ⟨cotangentComplexDerivedIsoKaehlerDifferentialOfSmooth h08QX A B⟩

end CommAlgCat

end
