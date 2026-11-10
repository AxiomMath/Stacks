module

public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.PolynomialAlgebra
public import StacksFrontier.Cotangent.ResolutionCotangentDerived
public import StacksFrontier.Cotangent.StandardResolutionIsResolution
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Cotangent.StandardResolution
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.PolynomialAlgebra

/-!
# The standard resolution over a polynomial base

Let `A → B → C` be ring maps with `B` a polynomial algebra over `A`. The standard resolution
`P• ⟶ C` of `C` over `B` is then, read over `A`, a resolution of `C` over `A` as well: its terms
are polynomial algebras over `A` because a polynomial algebra over a polynomial algebra is one,
and its augmentation of underlying simplicial sets does not depend on the base ring. For each
`n` the differentials of the tower `A → B → Pₙ` moreover form a split short exact sequence
`0 → Pₙ ⊗[B] Ω[B⁄A] → Ω[Pₙ⁄A] → Ω[Pₙ⁄B] → 0`, because `Pₙ` is a polynomial algebra over `B`.
Base changing it to `C` and passing to associated complexes gives a short exact sequence of
complexes of `C`-modules
`Ω[B⁄A] ⊗[B] C → Ω[P•⁄A] ⊗[P•] C → Ω[P•⁄B] ⊗[P•] C`
whose last term is `L_{C/B}` and whose first term is `Ω[B⁄A] ⊗[B] C` in degree `0`. Its
distinguished triangle is the triangle of Tag 08SA, once the middle term is identified with
`L_{C/A}`; that identification is the canonical isomorphism of Tag 08PU, which is not available
in this library and is taken here as an explicit hypothesis. Tag 08SA is therefore carried, with
that hypothesis named in its attribute, by
`CommAlgCat.exists_distTriang_derivedExtensionScalars_of_isPolynomialAlgebra` — see the first
implementation note.

## Main definitions

* `CommAlgCat.restrictScalars`: restriction of scalars along `A → B` on commutative algebras.
* `CommAlgCat.restrictedCotangentSimplicialModule` and
  `CommAlgCat.restrictedCotangentComplex`: the simplicial `C`-module `Ω[P•⁄A] ⊗[P•] C` of the
  standard resolution `P•` of `C` over `B` read over `A`, and its associated complex.
* `CommAlgCat.restrictedCotangentShortComplex` and
  `CommAlgCat.restrictedCotangentComplexShortComplex`: the sequence of differentials of that
  resolution, as a short complex of simplicial `C`-modules and of complexes of `C`-modules.

## Main results

* `Algebra.IsPolynomialAlgebra.trans`: a polynomial algebra over a polynomial algebra is a
  polynomial algebra.
* `Algebra.IsPolynomialAlgebra.formallySmooth`: a polynomial algebra is formally smooth.
* `CommAlgCat.standardResolution_obj_isPolynomialAlgebra_of_isPolynomialAlgebra`: every term of
  the standard resolution of `C` over `B` is a polynomial algebra over `A`.
* `CommAlgCat.standardResolution_isResolution_restrictScalars`: that standard resolution is a
  resolution of `C` over `A`.
* `KaehlerDifferential.exists_retraction_mapBaseChange_of_isPolynomialAlgebra`: the split short
  exact sequence of differentials of a tower whose upper step is a polynomial algebra.
* `CommAlgCat.restrictedCotangentShortComplex_shortExact_app` and
  `CommAlgCat.restrictedCotangentComplexShortComplex_shortExact`: short exactness of the
  sequence of differentials, degreewise and as a sequence of complexes.
* `CommAlgCat.nonempty_restrictedCotangentComplexShortComplex_X₁_iso`: the first term of that
  sequence is `Ω[B⁄A] ⊗[B] C` in degree `0`.
* `CommAlgCat.exists_distTriang_kaehlerDifferential_of_iso` and
  `CommAlgCat.exists_distTriang_derivedExtensionScalars_of_iso`: the distinguished triangle,
  conditional on the isomorphism of Tag 08PU for the resolution in play, with the first term
  written as `Ω[B⁄A] ⊗[B] C` in degree `0` and as `L_{B/A} ⊗^L_B C`.
* `CommAlgCat.nonempty_derivedExtensionScalars_cotangentComplex_iso_of_isPolynomialAlgebra`:
  the derived base change along `B → C` of Tag 08QH, namely `L_{B/A} ⊗^L_B C ≅ Ω[B⁄A] ⊗[B] C`
  in degree `0`.
* `CommAlgCat.exists_distTriang_derivedExtensionScalars_of_isPolynomialAlgebra`: **Tag 08SA**,
  that distinguished triangle again, now conditional on Tag 08PU alone.

## Implementation notes

**What is not proved, and what the attribute's qualifier names.** Tag 08SA asserts a
distinguished triangle on the three objects `L_{B/A} ⊗^L_B C`, `L_{C/A}` and `L_{C/B}`. Two of
the three are reached here on the nose: the last term of the sequence of differentials *is*
`L_{C/B}`, because `L_{C/B}` is by definition (`StacksFrontier.Cotangent.Complex`) computed from
the standard resolution of `C` over `B`, which is the resolution the source's proof chooses; and
the first term is `Ω[B⁄A] ⊗[B] C` in degree `0`, which is `L_{B/A} ⊗^L_B C` by Tag 08QH
together with the projectivity of `Ω[B⁄A]`, both of which are available.

The middle term is not. The complex produced by the sequence is `Ω[P•⁄A] ⊗[P•] C` for `P•` the
standard resolution of `C` over **`B`**, whereas `L_{C/A}` is `Ω[Q•⁄A] ⊗[Q•] C` for `Q•` the
standard resolution of `C` over **`A`**. Both `P•` and `Q•` are resolutions of `C` over `A` —
that `P•` is one is `CommAlgCat.standardResolution_isResolution_restrictScalars`, the first step
of the source's proof, and it is proved here — and the identification of the two complexes is
exactly the assertion of Tag 08PU that *any* resolution computes the cotangent complex. That
assertion is now available in `D(B)`, as
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` of
`StacksFrontier/Cotangent/ResolutionCotangentDerived.lean`, and it is what discharges `h08PU` in
`CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex` below. Notes elsewhere
recording Tag 08PU as absent — in `StacksFrontier/Cotangent/PolynomialAlgebra.lean` and
`StacksFrontier/Cotangent/AtiyahClass.lean` — predate that and are stale. There is no cheap
substitute for the *choice* of resolution, though: the sequence above is short exact
only because each `Pₙ` is formally smooth over `B`, which fails for the terms of `Q•` as soon as
`B → C` is not injective, so the source's choice of resolution is forced and the comparison is
unavoidable.

The conditional forms below therefore state the triangle with that identification as an
explicit hypothesis `h08PU`. Exactly one declaration carries the tag, namely
`CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex`, which needs no such
hypothesis: Tag 08PU is available in `D(B)`, so the identification is discharged and the
statement is the tag's own. The conditional forms are kept beside it because they hold at two
universes and for arbitrary `B`, where the tagged statement takes the three rings in one
universe — no restriction for the tag, since three rings with maps between them always lie in a
common universe. The remaining declarations below (the resolution over `A`, the split
sequence of differentials, its short exactness degreewise and as a sequence of complexes, the
first term, the derived base change of Tag 08QH, and the two intermediate forms of the triangle)
are proof ingredients of Tag 08SA rather than clauses of its conclusion, so they carry no
attribute.

Transitivity is the composite of `MvPolynomial.sumAlgEquiv`, which splits the variables of
`A[ι ⊕ κ]` into `A[κ][ι]`, with the coefficient change `A[κ] ≃ₐ[A] B` and the given
equivalence `B[ι] ≃ₐ[B] P` read over `A`. The two polynomial generating types are allowed to
differ, so the composite type `ι ⊕ κ` of generators of `P` over `A` is the one produced.

The `A`-algebra structure on a term of the standard resolution of `C` over `B` is the composite
`A → B → Pₙ`, so it is supplied by `Algebra.compHom` and makes `A → B → Pₙ` a scalar tower by
reflexivity. Restriction of scalars leaves the underlying ring and the underlying map of a
morphism unchanged, so composing it with the forgetful functor to sets gives the forgetful
functor over `B` on the nose; the trivial Kan fibration condition of `CommAlgCat.IsResolution`
is therefore the very same condition over `A` as over `B`.

The split short exactness is **Stacks 031K** at the tower `A → B → Pₙ`, whose hypothesis of
formal smoothness of `B → Pₙ` holds because `Pₙ` is a polynomial algebra over `B`. Exactness at
`Ω[Pₙ⁄A]` and surjectivity onto `Ω[Pₙ⁄B]` are `KaehlerDifferential.exact_mapBaseChange_map` and
`KaehlerDifferential.map_surjective`, so the retraction is the remaining content.

The simplicial module `Ω[P•⁄A] ⊗[P•] C` is built exactly as the cotangent simplicial module of
`StacksFrontier.Cotangent.Complex`, with the differentials taken over `A` instead of over `B`: the
`A`-algebra structure on `Pₙ` is the composite `A → B → Pₙ`, the structure maps are the
`C`-linear extensions of `ω ↦ 1 ⊗ Ω[Pᵢ⁄A] → Ω[Pⱼ⁄A]`, and maps out of a term are determined by
their values on the pure differentials `1 ⊗ d p`. Degreewise short exactness is obtained by
splitting the untensored sequence with the retraction above and transporting the splitting
along extension of scalars, which is additive; the only identification needed is the
cancellation `C ⊗[Pₙ] (Pₙ ⊗[B] Ω[B⁄A]) ≅ C ⊗[B] Ω[B⁄A]`. Short exactness of the sequence of
complexes is checked in each cohomological degree: in the degrees in the image of the
embedding it is the simplicial degree just treated, and in the others all three terms vanish.

The triangle is stated existentially, as in the source: the two hypotheses are isomorphisms of
objects of `D(C)`, which transport a distinguished triangle to one with the named objects by
`CategoryTheory.Pretriangulated.exists_distinguished_of_objIso`. Tag 08QH is available only as
an existence statement, so no canonical morphism may be extracted from it; it is used through
the second hypothesis, which is its derived base change along `B → C`.

That second hypothesis is in fact implied by polynomiality of `B` over `A`: the differentials
`Ω[B⁄A]` are then a projective `B`-module, and a projective module placed in degree `0`
computes derived extension of scalars by `comparison_isIso_of_projective`, so Tag 08QH base
changes to an isomorphism `L_{B/A} ⊗^L_B C ≅ Ω[B⁄A] ⊗[B] C` in degree `0`. The derived
extension of scalars of a module is the categorical `ModuleCat.extendScalars`, whose value
carries the module structure of `Module.compHom` rather than that of the algebra, so the last
step of the identification is the comparison of those two structures on `C ⊗[B] Ω[B⁄A]`, which
is the identity on pure tensors.

## References

* [Stacks Project, Tag 08SA](https://stacks.math.columbia.edu/tag/08SA)
* [Stacks Project, Tag 031K](https://stacks.math.columbia.edu/tag/031K)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open scoped ChangeOfRings TensorProduct

universe u v w

namespace Algebra

/-- A polynomial algebra over a polynomial algebra is a polynomial algebra: if `B = A[κ]` and
`P = B[ι]`, then `P = A[ι ⊕ κ]`. -/
public theorem IsPolynomialAlgebra.trans {A : Type u} {B P : Type w} [CommRing A] [CommRing B]
    [CommRing P] [Algebra A B] [Algebra B P] [Algebra A P] [IsScalarTower A B P]
    (hB : IsPolynomialAlgebra A B) (hP : IsPolynomialAlgebra B P) :
    IsPolynomialAlgebra A P := by
  obtain ⟨κ, ⟨eB⟩⟩ := hB
  obtain ⟨ι, ⟨eP⟩⟩ := hP
  exact ⟨ι ⊕ κ, ⟨(MvPolynomial.sumAlgEquiv A ι κ).trans
    ((MvPolynomial.mapAlgEquiv ι eB).trans (eP.restrictScalars A))⟩⟩

/-- A polynomial algebra is formally smooth. -/
@[ega "0 19.10.3", ega "0 19.3.3"]
public theorem IsPolynomialAlgebra.formallySmooth {A : Type u} {P : Type w} [CommRing A]
    [CommRing P] [Algebra A P] (hP : IsPolynomialAlgebra A P) : FormallySmooth A P := by
  obtain ⟨ι, ⟨e⟩⟩ := hP
  exact FormallySmooth.of_equiv e

end Algebra

namespace CommAlgCat

/-- If `B` is a polynomial algebra over `A`, then every term of the standard resolution of a
`B`-algebra `C` over `B` is a polynomial algebra over `A`; this is condition (1) of Tag 08QI for
that same simplicial algebra to be a resolution of `C` over `A`. -/
public theorem standardResolution_obj_isPolynomialAlgebra_of_isPolynomialAlgebra
    (A : Type u) [CommRing A] (B : Type w) [CommRing B] [Algebra A B] (C : CommAlgCat.{w} B)
    (hB : Algebra.IsPolynomialAlgebra A B) (n : SimplexCategoryᵒᵖ) :
    letI : Algebra A ((standardResolution.{w, w} B C).left.obj n : Type w) :=
      Algebra.compHom _ (algebraMap A B)
    Algebra.IsPolynomialAlgebra A ((standardResolution.{w, w} B C).left.obj n : Type w) := by
  let _ : Algebra A ((standardResolution.{w, w} B C).left.obj n : Type w) :=
    Algebra.compHom _ (algebraMap A B)
  have : IsScalarTower A B ((standardResolution.{w, w} B C).left.obj n : Type w) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact hB.trans (standardResolution_obj_isPolynomialAlgebra.{w, w} B C n)

/-- Restriction of scalars along `A → B`, from commutative `B`-algebras to commutative
`A`-algebras: the underlying ring is unchanged and `A` acts through `B`. -/
public def restrictScalars (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B] :
    CommAlgCat.{w} B ⥤ CommAlgCat.{w} A where
  obj P :=
    letI : Algebra A (P : Type w) := Algebra.compHom (P : Type w) (algebraMap A B)
    CommAlgCat.of A (P : Type w)
  map {P Q} f :=
    letI : Algebra A (P : Type w) := Algebra.compHom (P : Type w) (algebraMap A B)
    letI : Algebra A (Q : Type w) := Algebra.compHom (Q : Type w) (algebraMap A B)
    letI : IsScalarTower A B (P : Type w) := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A B (Q : Type w) := IsScalarTower.of_algebraMap_eq' rfl
    CommAlgCat.ofHom (f.hom.restrictScalars A)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- If `B` is a polynomial algebra over `A`, then the standard resolution of a `B`-algebra `C`
over `B` is, read over `A`, also a resolution of `C` over `A`. This is the first step of the
proof of Tag 08SA. -/
public theorem standardResolution_isResolution_restrictScalars (A : Type u) [CommRing A]
    (B : Type w) [CommRing B] [Algebra A B] (C : CommAlgCat.{w} B)
    (hB : Algebra.IsPolynomialAlgebra A B) :
    letI : Algebra A (C : Type w) := Algebra.compHom (C : Type w) (algebraMap A B)
    IsResolution A C ((standardResolution.{w, w} B C).left ⋙ restrictScalars.{u, w, w} A B)
      (Functor.whiskerRight (standardResolution.{w, w} B C).hom
          (restrictScalars.{u, w, w} A B) ≫ (Functor.constComp _ _ _).hom) := by
  let _ : Algebra A (C : Type w) := Algebra.compHom (C : Type w) (algebraMap A B)
  refine ⟨fun n => ?_, ?_⟩
  · exact standardResolution_obj_isPolynomialAlgebra_of_isPolynomialAlgebra A B C hB n
  · exact (standardResolution_isResolution.{w, w} B C).trivialKanFibration

end CommAlgCat

namespace KaehlerDifferential

/-- **Stacks Project, Tag 031K** at a tower whose upper step is a polynomial algebra. For
`A → B → P` with `P` a polynomial algebra over `B`, the canonical injection
`P ⊗[B] Ω[B⁄A] → Ω[P⁄A]` admits a `P`-linear retraction, so
`0 → P ⊗[B] Ω[B⁄A] → Ω[P⁄A] → Ω[P⁄B] → 0` is a split short exact sequence. The tag's own
statement is `KaehlerDifferential.exists_retraction_mapBaseChange`, which this specialises; no
attribute is placed here for that reason. -/
@[sga "1 II 4.4" "special case"]
public theorem exists_retraction_mapBaseChange_of_isPolynomialAlgebra (A : Type u) (B : Type v)
    (P : Type w) [CommRing A] [CommRing B] [CommRing P] [Algebra A B] [Algebra B P]
    [Algebra A P] [IsScalarTower A B P] (hP : Algebra.IsPolynomialAlgebra B P) :
    ∃ r : Ω[P⁄A] →ₗ[P] P ⊗[B] Ω[B⁄A],
      r ∘ₗ KaehlerDifferential.mapBaseChange A B P = LinearMap.id := by
  have := hP.formallySmooth
  exact KaehlerDifferential.exists_retraction_mapBaseChange A B P

end KaehlerDifferential



namespace CategoryTheory.Pretriangulated

/-- A triangle whose three objects are isomorphic to those of a distinguished triangle is, for a
suitable choice of its three morphisms, itself distinguished. -/
public theorem exists_distinguished_of_objIso {D : Type*} [Category* D] [Limits.HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : Triangle D) (hT : T ∈ distinguishedTriangles) (X Y Z : D) (a : X ≅ T.obj₁)
    (b : Y ≅ T.obj₂) (c : Z ≅ T.obj₃) :
    ∃ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles := by
  refine ⟨a.hom ≫ T.mor₁ ≫ b.inv, b.hom ≫ T.mor₂ ≫ c.inv,
    c.hom ≫ T.mor₃ ≫ a.inv⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ T a b c ?_ ?_ ?_)
  · simp
  · simp
  · simp [← Functor.map_comp]

end CategoryTheory.Pretriangulated

namespace CommAlgCat

/-- The standard resolution of `C` over `B`, for a `B`-algebra `C` presented by an `Algebra`
instance. -/
public noncomputable abbrev standardResolutionOver (B : Type w) [CommRing B] (C : Type w)
    [CommRing C] [Algebra B C] : SimplicialObject.Augmented (CommAlgCat.{w} B) :=
  standardResolution.{w, w} B (CommAlgCat.of B C)

/-- The underlying ring of the term of `CommAlgCat.standardResolutionOver` in simplicial degree
`n`. -/
public noncomputable abbrev standardResolutionOverObj (B : Type w) [CommRing B] (C : Type w)
    [CommRing C] [Algebra B C] (n : SimplexCategoryᵒᵖ) : Type w :=
  ((standardResolutionOver B C).left.obj n : Type w)

/-- The augmentation `Pₙ → C` of `CommAlgCat.standardResolutionOver`, as a ring homomorphism. -/
public noncomputable abbrev standardResolutionOverAug (B : Type w) [CommRing B] (C : Type w)
    [CommRing C] [Algebra B C] (n : SimplexCategoryᵒᵖ) :
    standardResolutionOverObj B C n →+* C :=
  standardResolutionAugmentationHom.{w, w} B (CommAlgCat.of B C) n

/-- The cotangent complex `L_{C/A}` of an `A`-algebra `C` presented by an `Algebra` instance,
as a complex of `C`-modules. -/
public noncomputable abbrev cotangentComplexOfAlgebra (A : Type u) [CommRing A]
    (C : Type (max u v)) [CommRing C] [Algebra A C] :
    CochainComplex (ModuleCat.{max u v} C) ℤ :=
  cotangentComplex.{u, v} A (CommAlgCat.of A C)

section

variable (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
  (C : Type (max u v)) [CommRing C] [Algebra B C]

/-- The `A`-algebra structure on a term of the standard resolution of `C` over `B` given by the
composite `A → B → Pₙ`. -/
noncomputable local instance algebraStandardResolutionOverObj (n : SimplexCategoryᵒᵖ) :
    Algebra A (standardResolutionOverObj.{max u v} B C n) :=
  Algebra.compHom _ (algebraMap A B)

/-- `A → B → Pₙ` is a scalar tower. -/
local instance isScalarTowerStandardResolutionOverObj (n : SimplexCategoryᵒᵖ) :
    IsScalarTower A B (standardResolutionOverObj.{max u v} B C n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The module `C ⊗[Pₙ] Ω[Pₙ⁄A]` of differentials over `A`, in simplicial degree `n`, of the
standard resolution of `C` over `B`. -/
public noncomputable def restrictedCotangentTerm (n : SimplexCategoryᵒᵖ) : ModuleCat.{max u v} C :=
  (ModuleCat.extendScalars (standardResolutionOverAug B C n)).obj
    (ModuleCat.of (standardResolutionOverObj.{max u v} B C n)
      (KaehlerDifferential A (standardResolutionOverObj.{max u v} B C n)))

/-- The pure differential `1 ⊗ d p` in `CommAlgCat.restrictedCotangentTerm`. -/
public noncomputable def restrictedCotangentDifferential (n : SimplexCategoryᵒᵖ)
    (p : standardResolutionOverObj.{max u v} B C n) : restrictedCotangentTerm.{u, v} A B C n :=
  (1 : C) ⊗ₜ KaehlerDifferential.D A (standardResolutionOverObj.{max u v} B C n) p

/-- Two `C`-linear maps out of `CommAlgCat.restrictedCotangentTerm` agreeing on every pure
differential are equal. -/
public theorem restrictedCotangentTerm_hom_ext (n : SimplexCategoryᵒᵖ)
    {N : ModuleCat.{max u v} C} (α β : restrictedCotangentTerm.{u, v} A B C n ⟶ N)
    (h : ∀ p : standardResolutionOverObj.{max u v} B C n,
      α (restrictedCotangentDifferential.{u, v} A B C n p) =
        β (restrictedCotangentDifferential.{u, v} A B C n p)) : α = β :=
  ModuleCat.extendScalars_kaehlerDifferential_hom_ext (standardResolutionOverAug B C n) α β h

/-- The `Pᵢ`-linear map `Ω[Pᵢ⁄A] → C ⊗[Pⱼ] Ω[Pⱼ⁄A]`, `ω ↦ 1 ⊗ ω`, attached to a simplicial
operator `i ⟶ j`; it is adjoint to `CommAlgCat.restrictedCotangentMap`. -/
public noncomputable def restrictedCotangentMapAdjoint {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    ModuleCat.of (standardResolutionOverObj.{max u v} B C i)
      (KaehlerDifferential A (standardResolutionOverObj.{max u v} B C i)) ⟶
    (ModuleCat.restrictScalars (standardResolutionOverAug B C i)).obj
      (restrictedCotangentTerm.{u, v} A B C j) := by
  let P := standardResolutionOverObj.{max u v} B C i
  let Q := standardResolutionOverObj.{max u v} B C j
  let g := (standardResolutionOver.{max u v} B C).left.map f
  letI : Algebra P Q := g.hom.toRingHom.toAlgebra
  letI : Algebra P C := (standardResolutionOverAug B C i).toAlgebra
  letI : Algebra Q C := (standardResolutionOverAug B C j).toAlgebra
  haveI : IsScalarTower A P Q := IsScalarTower.of_algebraMap_eq (fun a => by
    change _ = g.hom (algebraMap A P a)
    rw [show (algebraMap A P a) = algebraMap B P (algebraMap A B a) from rfl, g.hom.commutes]
    rfl)
  haveI : IsScalarTower P Q C := IsScalarTower.of_algebraMap_eq' (by
    exact (standardResolutionAugmentationHom_naturality.{max u v, max u v} B
      (CommAlgCat.of B C) f).symm)
  let M := ModuleCat.of P (KaehlerDifferential A P)
  let N := restrictedCotangentTerm.{u, v} A B C j
  let d : M ⟶ (ModuleCat.restrictScalars (standardResolutionOverAug B C i)).obj N :=
    ModuleCat.ofHom (X := M)
      (Y := (ModuleCat.restrictScalars (standardResolutionOverAug B C i)).obj N)
    { toFun := fun x => (1 : C) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x)
      map_add' := by
        intro x y
        change (TensorProduct.mk Q C (KaehlerDifferential A Q) 1)
            (KaehlerDifferential.map A A P Q (x + y)) = _
        rw [map_add]
        exact (TensorProduct.mk Q C (KaehlerDifferential A Q) 1).map_add _ _
      map_smul' := by
        intro p x
        change (1 : C) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q (p • x)) =
          (standardResolutionOverAug B C i) p •
            ((1 : C) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q x))
        rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        congr 1 }
  exact d

/-- The simplicial structure map of `CommAlgCat.restrictedCotangentTerm`: the `C`-linear
extension of `CommAlgCat.restrictedCotangentMapAdjoint`. -/
public noncomputable def restrictedCotangentMap {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    restrictedCotangentTerm.{u, v} A B C i ⟶ restrictedCotangentTerm.{u, v} A B C j :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (standardResolutionOverAug B C i) (restrictedCotangentMapAdjoint.{u, v} A B C f)

/-- `CommAlgCat.restrictedCotangentMap` sends a pure differential to the pure differential of
the image. -/
@[simp]
public theorem restrictedCotangentMap_D {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (p : standardResolutionOverObj.{max u v} B C i) :
    restrictedCotangentMap.{u, v} A B C f (restrictedCotangentDifferential.{u, v} A B C i p) =
      restrictedCotangentDifferential.{u, v} A B C j
        ((standardResolutionOver.{max u v} B C).left.map f p) := by
  have key : restrictedCotangentMap.{u, v} A B C f
      (restrictedCotangentDifferential.{u, v} A B C i p) =
      (1 : C) • (restrictedCotangentMapAdjoint.{u, v} A B C f)
        (KaehlerDifferential.D A (standardResolutionOverObj.{max u v} B C i) p) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (standardResolutionOverAug B C i) (restrictedCotangentMapAdjoint.{u, v} A B C f) (1 : C)
      (KaehlerDifferential.D A (standardResolutionOverObj.{max u v} B C i) p)
  rw [key, one_smul]
  let P := standardResolutionOverObj.{max u v} B C i
  let Q := standardResolutionOverObj.{max u v} B C j
  let g := (standardResolutionOver.{max u v} B C).left.map f
  let _ : Algebra P Q := g.hom.toRingHom.toAlgebra
  let _ : Algebra P C := (standardResolutionOverAug B C i).toAlgebra
  let _ : Algebra Q C := (standardResolutionOverAug B C j).toAlgebra
  have : IsScalarTower A P Q := IsScalarTower.of_algebraMap_eq (fun a => by
    change _ = g.hom (algebraMap A P a)
    rw [show (algebraMap A P a) = algebraMap B P (algebraMap A B a) from rfl, g.hom.commutes]
    rfl)
  have : IsScalarTower P Q C := IsScalarTower.of_algebraMap_eq' (by
    exact (standardResolutionAugmentationHom_naturality.{max u v, max u v} B
      (CommAlgCat.of B C) f).symm)
  change (1 : C) ⊗ₜ[Q] (KaehlerDifferential.map A A P Q (KaehlerDifferential.D A P p)) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- The simplicial `C`-module `Ω[P•⁄A] ⊗[P•] C` of the standard resolution `P•` of `C` over
`B`, read over `A`. -/
public noncomputable def restrictedCotangentSimplicialModule :
    SimplicialObject (ModuleCat.{max u v} C) where
  obj := restrictedCotangentTerm.{u, v} A B C
  map := fun f => restrictedCotangentMap.{u, v} A B C f
  map_id := by
    intro i
    apply restrictedCotangentTerm_hom_ext.{u, v} A B C i
    intro p
    simp
  map_comp := by
    intro i j k f g
    apply restrictedCotangentTerm_hom_ext.{u, v} A B C i
    intro p
    simp

/-- The complex `Ω[P•⁄A] ⊗[P•] C` associated to the standard resolution `P•` of `C` over `B`
read over `A`; by Tag 08PU it computes `L_{C/A}`. -/
public noncomputable def restrictedCotangentComplex : CochainComplex (ModuleCat.{max u v} C) ℤ :=
  (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} C)).obj
    (restrictedCotangentSimplicialModule.{u, v} A B C)).extend
      (ComplexShape.embeddingUpIntLE 0))

/-- The degreewise map `Ω[Pₙ⁄A] ⊗[Pₙ] C → Ω[Pₙ⁄B] ⊗[Pₙ] C` of the differential sequence. -/
public noncomputable def restrictedCotangentToRelative (n : SimplexCategoryᵒᵖ) :
    restrictedCotangentTerm.{u, v} A B C n ⟶
      cotangentTerm.{max u v, max u v} B (CommAlgCat.of B C) n :=
  (ModuleCat.extendScalars (standardResolutionOverAug B C n)).map
    (ModuleCat.ofHom (KaehlerDifferential.map A B
      (standardResolutionOverObj.{max u v} B C n)
      (standardResolutionOverObj.{max u v} B C n)))

/-- `CommAlgCat.restrictedCotangentToRelative` sends a pure differential over `A` to the pure
differential over `B`. -/
@[simp]
public theorem restrictedCotangentToRelative_D (n : SimplexCategoryᵒᵖ)
    (p : standardResolutionOverObj.{max u v} B C n) :
    restrictedCotangentToRelative.{u, v} A B C n
        (restrictedCotangentDifferential.{u, v} A B C n p) =
      cotangentTermDifferential.{max u v, max u v} B (CommAlgCat.of B C) n p := by
  have e1 := ModuleCat.ExtendScalars.map_tmul (standardResolutionOverAug B C n)
      (ModuleCat.ofHom (KaehlerDifferential.map A B
        (standardResolutionOverObj.{max u v} B C n)
        (standardResolutionOverObj.{max u v} B C n))) (1 : C)
      (KaehlerDifferential.D A (standardResolutionOverObj.{max u v} B C n) p)
  refine e1.trans ?_
  simp only [ModuleCat.hom_ofHom, KaehlerDifferential.map_D]
  rfl

/-- Cancelling the intermediate base change: `C ⊗[Pₙ] (Pₙ ⊗[B] Ω[B⁄A]) ≅ C ⊗[B] Ω[B⁄A]`. -/
public noncomputable def restrictedCotangentCancelIso (n : SimplexCategoryᵒᵖ) :
    (ModuleCat.extendScalars (standardResolutionOverAug B C n)).obj
        (ModuleCat.of (standardResolutionOverObj.{max u v} B C n)
          (standardResolutionOverObj.{max u v} B C n ⊗[B] KaehlerDifferential A B)) ≅
      ModuleCat.of C (C ⊗[B] KaehlerDifferential A B) :=
  letI : Algebra (standardResolutionOverObj.{max u v} B C n) C :=
    (standardResolutionOverAug B C n).toAlgebra
  haveI : IsScalarTower B (standardResolutionOverObj.{max u v} B C n) C :=
    IsScalarTower.of_algebraMap_eq (fun b =>
      (((standardResolutionOver.{max u v} B C).hom.app n).hom.commutes b).symm)
  (TensorProduct.AlgebraTensorModule.cancelBaseChange B
    (standardResolutionOverObj.{max u v} B C n) C C (KaehlerDifferential A B)).toModuleIso

/-- The degreewise map `C ⊗[B] Ω[B⁄A] → Ω[Pₙ⁄A] ⊗[Pₙ] C` of the differential sequence. -/
public noncomputable def restrictedCotangentFromBase (n : SimplexCategoryᵒᵖ) :
    ModuleCat.of C (C ⊗[B] KaehlerDifferential A B) ⟶ restrictedCotangentTerm.{u, v} A B C n :=
  (restrictedCotangentCancelIso.{u, v} A B C n).inv ≫
    (ModuleCat.extendScalars (standardResolutionOverAug B C n)).map
      (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange A B
        (standardResolutionOverObj.{max u v} B C n)))

/-- `CommAlgCat.restrictedCotangentFromBase` sends `1 ⊗ d b` to the pure differential of the
image of `b`. -/
@[simp]
public theorem restrictedCotangentFromBase_D (n : SimplexCategoryᵒᵖ) (b : B) :
    restrictedCotangentFromBase.{u, v} A B C n
        ((1 : C) ⊗ₜ[B] KaehlerDifferential.D A B b) =
      restrictedCotangentDifferential.{u, v} A B C n
        (algebraMap B (standardResolutionOverObj.{max u v} B C n) b) := by
  have h : KaehlerDifferential.mapBaseChange A B
        (standardResolutionOverObj.{max u v} B C n)
        ((1 : standardResolutionOverObj.{max u v} B C n) ⊗ₜ[B]
          KaehlerDifferential.D A B b) =
      KaehlerDifferential.D A (standardResolutionOverObj.{max u v} B C n)
        (algebraMap B (standardResolutionOverObj.{max u v} B C n) b) := by
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  have e1 := ModuleCat.ExtendScalars.map_tmul (standardResolutionOverAug B C n)
      (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange A B
        (standardResolutionOverObj.{max u v} B C n))) (1 : C)
      ((1 : standardResolutionOverObj.{max u v} B C n) ⊗ₜ[B] KaehlerDifferential.D A B b)
  refine e1.trans ?_
  simp only [ModuleCat.hom_ofHom, h]
  rfl

/-- The first map of the differential sequence is constant in the simplicial degree. -/
public theorem restrictedCotangentFromBase_naturality {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    restrictedCotangentFromBase.{u, v} A B C i ≫ restrictedCotangentMap.{u, v} A B C f =
      restrictedCotangentFromBase.{u, v} A B C j := by
  refine ModuleCat.baseChange_kaehlerDifferential_hom_ext (A := A) (R := B) _ _ fun b => ?_
  change restrictedCotangentMap.{u, v} A B C f
    (restrictedCotangentFromBase.{u, v} A B C i _) = _
  rw [restrictedCotangentFromBase_D, restrictedCotangentMap_D, restrictedCotangentFromBase_D]
  exact congrArg (restrictedCotangentDifferential.{u, v} A B C j)
    (((standardResolutionOver.{max u v} B C).left.map f).hom.commutes b)

/-- The second map of the differential sequence is simplicial. -/
public theorem restrictedCotangentToRelative_naturality {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    restrictedCotangentMap.{u, v} A B C f ≫ restrictedCotangentToRelative.{u, v} A B C j =
      restrictedCotangentToRelative.{u, v} A B C i ≫
        cotangentMap.{max u v, max u v} B (CommAlgCat.of B C) f := by
  refine restrictedCotangentTerm_hom_ext.{u, v} A B C i _ _ fun p => ?_
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, restrictedCotangentMap_D,
    restrictedCotangentToRelative_D, restrictedCotangentToRelative_D, cotangentMap_D]

/-- The short complex of simplicial `C`-modules
`Ω[B⁄A] ⊗[B] C → Ω[P•⁄A] ⊗[P•] C → Ω[P•⁄B] ⊗[P•] C` of the standard resolution `P•` of `C`
over `B`, with the first term constant. Its short exactness is
`CommAlgCat.restrictedCotangentShortComplex_shortExact_app`. -/
public noncomputable def restrictedCotangentShortComplex :
    ShortComplex (SimplicialObject (ModuleCat.{max u v} C)) where
  X₁ := (Functor.const SimplexCategoryᵒᵖ).obj (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B))
  X₂ := restrictedCotangentSimplicialModule.{u, v} A B C
  X₃ := (cotangentSimplicialModule.{max u v, max u v} B (CommAlgCat.of B C)).object
  f := { app := fun n => restrictedCotangentFromBase.{u, v} A B C n
         naturality := fun i j f => by
           change 𝟙 (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B)) ≫
               restrictedCotangentFromBase.{u, v} A B C j =
             restrictedCotangentFromBase.{u, v} A B C i ≫
               restrictedCotangentMap.{u, v} A B C f
           rw [Category.id_comp, restrictedCotangentFromBase_naturality] }
  g := { app := fun n => restrictedCotangentToRelative.{u, v} A B C n
         naturality := fun i j f =>
           restrictedCotangentToRelative_naturality.{u, v} A B C f }
  zero := by
    apply NatTrans.ext
    funext n
    change restrictedCotangentFromBase.{u, v} A B C n ≫
        restrictedCotangentToRelative.{u, v} A B C n = 0
    refine ModuleCat.baseChange_kaehlerDifferential_hom_ext (A := A) (R := B) _ _ fun b => ?_
    rw [ModuleCat.comp_apply, restrictedCotangentFromBase_D, restrictedCotangentToRelative_D,
      cotangentTermDifferential_algebraMap]
    simp

/-- In every simplicial degree the differential sequence of the standard resolution of `C` over
`B` is short exact, because `Pₙ` is a polynomial algebra over `B`, so that the sequence of
Tag 031K is split before base change to `C`. -/
public theorem restrictedCotangentShortComplex_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((restrictedCotangentShortComplex.{u, v} A B C).map
      ((CategoryTheory.evaluation SimplexCategoryᵒᵖ
        (ModuleCat.{max u v} C)).obj n)).ShortExact := by
  let P := standardResolutionOverObj.{max u v} B C n
  let _ : Algebra P C := (standardResolutionOverAug B C n).toAlgebra
  have : IsScalarTower B P C := IsScalarTower.of_algebraMap_eq (fun b =>
    (((standardResolutionOver.{max u v} B C).hom.app n).hom.commutes b).symm)
  let F := ModuleCat.extendScalars (standardResolutionOverAug B C n)
  let S := ShortComplex.moduleCatMk (KaehlerDifferential.mapBaseChange A B P)
    (KaehlerDifferential.map A B P P)
    (LinearMap.ext (KaehlerDifferential.exact_mapBaseChange_map A B P).apply_apply_eq_zero)
  have hSexact : S.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
      (KaehlerDifferential.exact_mapBaseChange_map A B P)
  have hepi : Epi S.g :=
    (ModuleCat.epi_iff_surjective _).2 (KaehlerDifferential.map_surjective A B P)
  obtain ⟨r, hr⟩ := KaehlerDifferential.exists_retraction_mapBaseChange_of_isPolynomialAlgebra
    A B P (standardResolution_obj_isPolynomialAlgebra.{max u v, max u v} B
      (CommAlgCat.of B C) n)
  let sp : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hSexact
    (ModuleCat.ofHom r) (ModuleCat.hom_ext hr) hepi
  have : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (standardResolutionOverAug B C n)).isLeftAdjoint
  have : Limits.PreservesBinaryBiproducts F :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let _ : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hSI : (S.map F).ShortExact := (sp.map F).shortExact
  have hIso : ((restrictedCotangentShortComplex.{u, v} A B C).map
      ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} C)).obj n)) ≅
      S.map F :=
    ShortComplex.isoMk (restrictedCotangentCancelIso.{u, v} A B C n).symm (Iso.refl _)
      (Iso.refl _)
      (by simp only [Iso.refl_hom, Iso.symm_hom]; rfl)
      (by simp only [Iso.refl_hom]; rfl)
  exact (ShortComplex.shortExact_iff_of_iso hIso).2 hSI

/-- The differential sequence of the standard resolution of `C` over `B`, as a short complex of
complexes of `C`-modules; its middle term is `CommAlgCat.restrictedCotangentComplex` and its
last term is `L_{C/B}`. -/
public noncomputable def restrictedCotangentComplexShortComplex :
    ShortComplex (CochainComplex (ModuleCat.{max u v} C) ℤ) :=
  (restrictedCotangentShortComplex.{u, v} A B C).map
    (AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} C) ⋙
      (ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{max u v} C))

end

/-- Extending a map of simplicial objects to the associated complexes is compatible with the
identification of the degree `e.f k` of the extension with the simplicial degree `k`. -/
public theorem extendMap_alternatingFaceMapComplex_comm {C : Type w} [CommRing C]
    {X Y : SimplicialObject (ModuleCat.{w} C)} (φ : X ⟶ Y) {i : ℤ}
    {k : ℕ} (hk : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f k = i) :
    (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} C)).obj X).extendXIso
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) hk).hom ≫ φ.app (op ⦋k⦌) =
      (HomologicalComplex.extendMap
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} C)).map φ)
        (ComplexShape.embeddingUpIntLE (0 : ℤ))).f i ≫
      (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{w} C)).obj Y).extendXIso
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) hk).hom := by
  rw [HomologicalComplex.extendMap_f _ _ hk]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

section

variable (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
  (C : Type (max u v)) [CommRing C] [Algebra B C]

/-- The differential sequence of the standard resolution of `C` over `B` is a short exact
sequence of complexes of `C`-modules. -/
public theorem restrictedCotangentComplexShortComplex_shortExact :
    (restrictedCotangentComplexShortComplex.{u, v} A B C).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i
  by_cases h : ∃ k : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f k = i
  · obtain ⟨k, hk⟩ := h
    have hIso : (restrictedCotangentComplexShortComplex.{u, v} A B C).map
          (HomologicalComplex.eval (ModuleCat.{max u v} C) (ComplexShape.up ℤ) i) ≅
        (restrictedCotangentShortComplex.{u, v} A B C).map
          ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (ModuleCat.{max u v} C)).obj
            (op ⦋k⦌)) :=
      ShortComplex.isoMk
        (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} C)).obj
          (restrictedCotangentShortComplex.{u, v} A B C).X₁).extendXIso _ hk)
        (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} C)).obj
          (restrictedCotangentShortComplex.{u, v} A B C).X₂).extendXIso _ hk)
        (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} C)).obj
          (restrictedCotangentShortComplex.{u, v} A B C).X₃).extendXIso _ hk)
        (extendMap_alternatingFaceMapComplex_comm.{max u v}
          (restrictedCotangentShortComplex.{u, v} A B C).f hk)
        (extendMap_alternatingFaceMapComplex_comm.{max u v}
          (restrictedCotangentShortComplex.{u, v} A B C).g hk)
    exact (ShortComplex.shortExact_iff_of_iso hIso).2
      (restrictedCotangentShortComplex_shortExact_app.{u, v} A B C (op ⦋k⦌))
  · have hz : ∀ X : SimplicialObject (ModuleCat.{max u v} C),
        Limits.IsZero ((((AlgebraicTopology.alternatingFaceMapComplex
          (ModuleCat.{max u v} C)).obj X).extend
            (ComplexShape.embeddingUpIntLE (0 : ℤ))).X i) := fun X =>
      HomologicalComplex.isZero_extend_X _ _ i (fun k hk => h ⟨k, hk⟩)
    exact (ShortComplex.Splitting.mk
      (S := (restrictedCotangentComplexShortComplex.{u, v} A B C).map
        (HomologicalComplex.eval (ModuleCat.{max u v} C) (ComplexShape.up ℤ) i))
      0 0 ((hz _).eq_of_src _ _) ((hz _).eq_of_src _ _) ((hz _).eq_of_src _ _)).shortExact

attribute [local instance] HasDerivedCategory.standard

/-- The first term of the differential sequence computes `Ω[B⁄A] ⊗[B] C` in degree `0`: the
complex of a constant simplicial module is homotopy equivalent to that module in degree `0`. -/
public theorem nonempty_restrictedCotangentComplexShortComplex_X₁_iso :
    Nonempty (DerivedCategory.Q.obj
        (restrictedCotangentComplexShortComplex.{u, v} A B C).X₁ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} C) 0).obj
        (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B))) := by
  let X : ModuleCat.{max u v} C := ModuleCat.of C (C ⊗[B] KaehlerDifferential A B)
  let he : HomotopyEquiv
      ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} C)).obj
        ((Functor.const SimplexCategoryᵒᵖ).obj X))
      ((ChainComplex.single₀ (ModuleCat.{max u v} C)).obj X) :=
    (HomotopyEquiv.ofIso
      ((AlgebraicTopology.alternatingFaceMapComplexConst).app X)).trans
        (ChainComplex.alternatingConstHomotopyEquiv X)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} C)
    (HomologicalComplex.extendMap he.hom (ComplexShape.embeddingUpIntLE (0 : ℤ)))).2
      inferInstance
  exact ⟨(@asIso _ _ _ _ (DerivedCategory.Q.map (HomologicalComplex.extendMap he.hom
      (ComplexShape.embeddingUpIntLE (0 : ℤ)))) hiso) ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) X 0 0 (by simp))⟩

end

section

attribute [local instance] HasDerivedCategory.standard

/-- **The triangle of Tag 08SA, conditional on Tag 08PU, with its first term written as
`Ω[B⁄A] ⊗[B] C` in degree `0`.** For ring maps `A → B → C`, granting the isomorphism of Tag
08PU for the standard resolution of `C` over `B` read over `A`, there is a distinguished
triangle `Ω[B⁄A] ⊗[B] C → L_{C/A} → L_{C/B} → (Ω[B⁄A] ⊗[B] C)[1]` in `D(C)`.

The hypothesis `h08PU` is what the tag's proof gets from Tag 08PU; because it is a hypothesis
the source does not have, no attribute is placed here. Tag 08PU is now available in `D(B)`, so
the unconditional form is
`CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex`, which carries the tag;
this conditional statement is kept because it holds at two universes and for arbitrary `B`.
Polynomiality of `B` over `A` is not needed for this statement — the
differential sequence is short exact for any `B`, since each `Pₙ` is a polynomial algebra over
`B` by construction. It is needed for `h08PU` to be true, and to rewrite the first term as
`L_{B/A} ⊗^L_B C`. -/
public theorem exists_distTriang_kaehlerDifferential_of_iso
    (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
    (C : Type (max u v)) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (h08PU : Nonempty (DerivedCategory.Q.obj (restrictedCotangentComplex.{u, v} A B C) ≅
      DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C))) :
    ∃ (f : (DerivedCategory.singleFunctor (ModuleCat.{max u v} C) 0).obj
          (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B)) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C))
      (g : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{max u v, max u v} B C))
      (h : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{max u v, max u v} B C) ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} C) 0).obj
          (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B)))⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g h ∈
        Pretriangulated.distinguishedTriangles (C := DerivedCategory (ModuleCat.{max u v} C)) := by
  obtain ⟨b⟩ := h08PU
  obtain ⟨a⟩ := nonempty_restrictedCotangentComplexShortComplex_X₁_iso.{u, v} A B C
  exact Pretriangulated.exists_distinguished_of_objIso _
    (DerivedCategory.triangleOfSES_distinguished
      (restrictedCotangentComplexShortComplex_shortExact.{u, v} A B C))
    _ _ _ a.symm b.symm (Iso.refl _)

/-- **The triangle of Tag 08SA, conditional on Tag 08PU and on the derived base change of Tag
08QH.** For ring maps `A → B → C` there is a distinguished triangle
`L_{B/A} ⊗^L_B C → L_{C/A} → L_{C/B} → (L_{B/A} ⊗^L_B C)[1]` in `D(C)`, granting the
isomorphism of Tag 08PU for the standard resolution of `C` over `B` read over `A` and the
identification of `L_{B/A} ⊗^L_B C` with `Ω[B⁄A] ⊗[B] C` in degree `0`.

The second is discharged from polynomiality of `B` over `A` in
`CommAlgCat.exists_distTriang_derivedExtensionScalars_of_isPolynomialAlgebra`; the tag itself is
carried by `CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex`. -/
public theorem exists_distTriang_derivedExtensionScalars_of_iso
    (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
    (C : Type (max u v)) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (h08PU : Nonempty (DerivedCategory.Q.obj (restrictedCotangentComplex.{u, v} A B C) ≅
      DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C)))
    (hbaseChange : Nonempty
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
          (algebraMap B C)).functor.obj
        (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} C) 0).obj
        (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B)))) :
    ∃ (f : (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            (algebraMap B C)).functor.obj
          (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A B)) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C))
      (g : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{max u v, max u v} B C))
      (h : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{max u v, max u v} B C) ⟶
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            (algebraMap B C)).functor.obj
          (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A B)))⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g h ∈
        Pretriangulated.distinguishedTriangles (C := DerivedCategory (ModuleCat.{max u v} C)) := by
  obtain ⟨e⟩ := hbaseChange
  obtain ⟨f, g, h, hT⟩ :=
    exists_distTriang_kaehlerDifferential_of_iso.{u, v} A B C h08PU
  exact Pretriangulated.exists_distinguished_of_objIso _ hT _ _ _ e (Iso.refl _) (Iso.refl _)

end

section

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars along `algebraMap R S` carries an `R`-module `M` to its base change
`S ⊗[R] M`, by the identity on pure tensors. -/
private noncomputable def extendScalarsObjTensorIso {R S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] (M : ModuleCat.{w} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  let X : Type w := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  letI : Module S (X ⊗[R] (M : Type w)) :=
    inferInstanceAs (Module S ((ModuleCat.extendScalars (algebraMap R S)).obj M : Type w))
  let eS : X ≃ₗ[R] S :=
    { AddEquiv.refl S with
      map_smul' r x := (Algebra.smul_def (R := R) (A := S) r x).symm }
  let e := TensorProduct.congr eS (LinearEquiv.refl R (M : Type w))
  have key : ∀ (s : S) (z : X ⊗[R] (M : Type w)), e (s • z) = s • e z := by
    intro s z
    induction z using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add z z' hz hz' => rw [smul_add, map_add, map_add, smul_add, hz, hz']
  exact LinearEquiv.toModuleIso { e.toAddEquiv with map_smul' := key }

/-- A projective module placed in degree `0` computes derived extension of scalars: the derived
base change of `M` along `f : R →+* S` is `S ⊗[R] M` in degree `0`. -/
private noncomputable def derivedExtensionScalarsSingleIsoOfProjective {R S : Type w}
    [CommRing R] [CommRing S] (f : R →+* S) (M : ModuleCat.{w} R) [Module.Projective R M] :
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{w, w, w}
          f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{w} R) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{w} S) 0).obj
        ((ModuleCat.extendScalars.{w, w, w} f).obj M) := by
  let Mod := ModuleCat.{w} R
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{w, w, w} f
  let F := ModuleCat.extendScalars.{w, w, w} f
  let P := (CochainComplex.singleFunctor Mod 0).obj M
  have hstrict : P.IsStrictlyLE 0 := inferInstance
  have hproj : ∀ i : ℤ, Projective (P.X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      change Projective M
      exact inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi).projective
  let eP : (DerivedCategory.singleFunctor Mod 0).obj M ≅ DerivedCategory.Q.obj P :=
    (DerivedCategory.singleFunctorIsoCompQ Mod 0).app M
  let eSingle :=
    HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0 |>.app M
  let eQ := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{w} S) 0).app (F.obj M)
  have hcomp : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P 0
  exact (D.functor.mapIso eP.symm).symm ≪≫ asIso (D.comparison.app P) ≪≫
    DerivedCategory.Q.mapIso eSingle ≪≫ eQ.symm

/-- **Stacks Project, Tag 08QH** base changed along `B → C`. For ring maps `A → B → C` with `B`
a polynomial algebra over `A`, the derived base change `L_{B/A} ⊗^L_B C` is `Ω[B⁄A] ⊗[B] C` in
degree `0`, because `Ω[B⁄A]` is then a projective `B`-module. -/
public theorem nonempty_derivedExtensionScalars_cotangentComplex_iso_of_isPolynomialAlgebra
    (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
    (C : Type (max u v)) [CommRing C] [Algebra B C]
    (hB : Algebra.IsPolynomialAlgebra A B) :
    Nonempty
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
          (algebraMap B C)).functor.obj
        (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} C) 0).obj
        (ModuleCat.of C (C ⊗[B] KaehlerDifferential A B))) := by
  have : Module.Projective B (KaehlerDifferential A B) :=
    KaehlerDifferential.projective_of_isPolynomialAlgebra hB
  obtain ⟨e⟩ := cotangentComplex_iso_kaehlerDifferential.{u, v} A (CommAlgCat.of A B) hB
  exact ⟨(CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
      (algebraMap B C)).functor.mapIso e ≪≫
    derivedExtensionScalarsSingleIsoOfProjective.{max u v} (algebraMap B C)
      (ModuleCat.of B (KaehlerDifferential A B)) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} C) 0).mapIso
      (extendScalarsObjTensorIso.{max u v} (ModuleCat.of B (KaehlerDifferential A B)))⟩

/-- **Stacks 08SA**, granting Tag 08PU for the resolution in play. For ring maps `A → B → C`
with `B` a polynomial algebra over `A` there is a distinguished triangle
`L_{B/A} ⊗^L_B C → L_{C/A} → L_{C/B} → (L_{B/A} ⊗^L_B C)[1]` in `D(C)`.

This is the statement of Tag 08SA except for the hypothesis `h08PU`, which the tag's proof gets
from Tag 08PU. Being a hypothesis the source does not have, it weakens the statement, so no
attribute is placed here; the unconditional form, which carries the tag, is
`CommAlgCat.exists_distTriang_derivedExtensionScalars_cotangentComplex`. This statement is kept
because it holds at two universes, where the tagged one is stated at a single universe. -/
public theorem exists_distTriang_derivedExtensionScalars_of_isPolynomialAlgebra
    (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B] [Algebra A B]
    (C : Type (max u v)) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : Algebra.IsPolynomialAlgebra A B)
    (h08PU : Nonempty (DerivedCategory.Q.obj (restrictedCotangentComplex.{u, v} A B C) ≅
      DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C))) :
    ∃ (f : (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            (algebraMap B C)).functor.obj
          (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A B)) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C))
      (g : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A C) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{max u v, max u v} B C))
      (h : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{max u v, max u v} B C) ⟶
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            (algebraMap B C)).functor.obj
          (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, v} A B)))⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g h ∈
        Pretriangulated.distinguishedTriangles (C := DerivedCategory (ModuleCat.{max u v} C)) :=
  exists_distTriang_derivedExtensionScalars_of_iso.{u, v} A B C h08PU
    (nonempty_derivedExtensionScalars_cotangentComplex_iso_of_isPolynomialAlgebra.{u, v}
      A B C hB)

end

/-! ### Discharging Tag 08PU for the resolution in play -/

/-- Transitivity of polynomiality with the type of variables named: if `B = A[ι_B]` and
`P = B[ι_P]`, then `P = A[ι_P ⊕ ι_B]`. This is the construction behind
`Algebra.IsPolynomialAlgebra.trans`, kept at the level of the equivalences so that the resulting
set of variables may be bounded. The scalar tower is an explicit hypothesis on the structure
maps rather than an instance, so that the `A`-algebra structure on `P` may be the one restriction
of scalars produces. -/
public noncomputable def mvPolynomialSumAlgEquivOfTrans {A : Type u} {B P : Type w} [CommRing A]
    [CommRing B] [CommRing P] [Algebra A B] [Algebra B P] [Algebra A P]
    (h : algebraMap A P = (algebraMap B P).comp (algebraMap A B))
    {ιB ιP : Type w} (eB : MvPolynomial ιB A ≃ₐ[A] B) (eP : MvPolynomial ιP B ≃ₐ[B] P) :
    MvPolynomial (ιP ⊕ ιB) A ≃ₐ[A] P :=
  haveI : IsScalarTower A B P := IsScalarTower.of_algebraMap_eq' h
  (MvPolynomial.sumAlgEquiv A ιP ιB).trans
    ((MvPolynomial.mapAlgEquiv ιP eB).trans (eP.restrictScalars A))

/-- **Restriction of scalars of a polynomial algebra over a polynomial algebra is bounded by the
disjoint union of the two sets of variables.** If `B = A[ι_B]` and `P = B[ι]`, then `P`, read as
an `A`-algebra through `B`, is a polynomial algebra over `A` on at most `κ` variables for any
bound `κ` containing `ι ⊕ ι_B`. -/
public theorem isPolynomialAlgebraBelow_restrictScalars_of_mvPolynomialAlgEquiv
    {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {ιB : Type u}
    (eB : MvPolynomial ιB A ≃ₐ[A] B) (P : CommAlgCat.{u} B) {ι : Type u}
    (eP : MvPolynomial ι B ≃ₐ[B] P) {κ : Cardinal.{u}} (hκ : Cardinal.mk (ι ⊕ ιB) ≤ κ) :
    IsPolynomialAlgebraBelow A κ ((restrictScalars.{u, u, u} A B).obj P) :=
  let : Algebra A (P : Type u) := Algebra.compHom (P : Type u) (algebraMap A B)
  ⟨ι ⊕ ιB, hκ, ⟨mvPolynomialSumAlgEquivOfTrans.{u, u} (P := (P : Type u)) rfl eB eP⟩⟩

section Restricted

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra B C]

/-- `C` read as an `A`-algebra through `B`, as an object of `CommAlgCat.{u} A`: the value of
`CommAlgCat.restrictScalars` at `C`. Writing the target of the resolution this way needs no
`Algebra A C` instance; the `A`-algebra structure carried is the composite `A → B → C`. -/
public noncomputable abbrev restrictedBase : CommAlgCat.{u} A :=
  (restrictScalars.{u, u, u} A B).obj (CommAlgCat.of B C)

/-- The standard resolution of `C` over `B`, read as a simplicial `A`-algebra. By
`CommAlgCat.standardResolution_isResolution_restrictScalars` it is a resolution of `C` over `A`
as soon as `B` is a polynomial algebra over `A`. -/
public noncomputable abbrev restrictedResolution : SimplicialObject (CommAlgCat.{u} A) :=
  (standardResolutionOver B C).left ⋙ restrictScalars.{u, u, u} A B

/-- The augmentation of `CommAlgCat.restrictedResolution` to `C`, read over `A`: restriction of
scalars changes neither the underlying rings nor the underlying maps. -/
public noncomputable abbrev restrictedResolutionAug :
    restrictedResolution A B C ⟶
      (SimplicialObject.const (CommAlgCat.{u} A)).obj (restrictedBase A B C) :=
  Functor.whiskerRight (standardResolutionOver B C).hom (restrictScalars.{u, u, u} A B) ≫
    (Functor.constComp _ _ _).hom

/-- **`(i^*Ω_{𝒪/A})(P_•, ε) = Ω[P_•⁄A] ⊗[P_•] C` for the standard resolution of `C` over `B`.**
No comparison map is involved: `CommAlgCat.overDifferentialsFunctor` and
`CommAlgCat.restrictedCotangentSimplicialModule` are built from the same formula, the first for
an arbitrary `A`-algebra augmented to `C` and the second for the terms of that resolution read
over `A`. -/
public noncomputable def restrictedResolutionOverDifferentialsIso :
    resolutionOver (restrictedResolutionAug A B C) ⋙ overDifferentialsFunctor ≅
      restrictedCotangentSimplicialModule.{u, u} A B C :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- Every term of the standard resolution of `C` over `B`, read over `A`, is a polynomial
`A`-algebra on at most `κ` variables, for `κ` the cardinality of the disjoint union of a type of
variables of `B` over `A` with the index types of the terms of that resolution over `B`: the
degree `n` term is `B[ι_n]`, hence `A[ι_n ⊕ ι_B]`, and `ι_n ⊕ ι_B` injects into that disjoint
union. -/
public theorem restrictedResolution_isPolynomialAlgebraBelow {ιB : Type u}
    (eB : MvPolynomial ιB A ≃ₐ[A] B) (κ : Cardinal.{u})
    (hκ : Cardinal.mk ((Σ m : ℕ, (((polynomialComonad.{u, u} B).toFunctor.iterate m).obj
      (CommAlgCat.of B C) : Type u)) ⊕ ιB) ≤ κ) (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A κ ((restrictedResolution A B C).obj n) := by
  obtain ⟨ι, hι, ⟨eP⟩⟩ :=
    standardResolution_isPolynomialAlgebraBelow.{u} B (CommAlgCat.of B C) n
  obtain ⟨f⟩ := (Cardinal.le_def ι _).mp hι
  exact isPolynomialAlgebraBelow_restrictScalars_of_mvPolynomialAlgEquiv eB _ eP
    (le_trans (Cardinal.mk_le_of_injective (f := Sum.map f id)
      (Function.Injective.sumMap f.injective Function.injective_id)) hκ)

/-- **The augmentation of `CommAlgCat.restrictedResolution` is a trivial Kan fibration on
underlying simplicial sets.** This is the second condition of Tag 08QI for it to be a resolution
of `C` over `A`, and it is the very same condition over `A` as over `B`: restriction of scalars
changes neither the underlying sets nor the underlying maps. The first condition is
`CommAlgCat.restrictedResolution_isPolynomialAlgebraBelow`; both together are
`CommAlgCat.standardResolution_isResolution_restrictScalars`. -/
public theorem restrictedResolution_trivialKanFibration :
    SSet.trivialKanFibrations
      (Functor.whiskerRight (restrictedResolutionAug A B C) (forget (CommAlgCat.{u} A))) :=
  (standardResolution_isResolution.{u, u} B (CommAlgCat.of B C)).trivialKanFibration

/-- **Tag 08PU in `D(C)` for the standard resolution of `C` over `B` read over `A`.** For `B` a
polynomial algebra over `A` that resolution is a resolution of `C` over `A`, so the complex
`Ω[P_•⁄A] ⊗[P_•] C` it produces is derived lower shriek of the sheaf `i^*Ω_{𝒪/A}` on the small
model of the site `C_{C/A}` restricted to polynomial algebras on at most `κ` variables. -/
public noncomputable def restrictedCotangentDerivedLowerShriekIso (κ : Cardinal.{u})
    (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ ((restrictedResolution A B C).obj n)) :
    DerivedCategory.Q.obj (restrictedCotangentComplex.{u, u} A B C) ≅
      smallPolynomialCotangentDerivedLowerShriek A (restrictedBase A B C) κ :=
  (DerivedCategory.Q.mapIso
      (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{u} C)).mapIso
        ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} C)).mapIso
          (restrictedResolutionOverDifferentialsIso A B C)))).symm ≪≫
    smallResolutionCotangentDerivedLowerShriekIso (restrictedResolutionAug A B C) κ hPκ
      (restrictedResolution_trivialKanFibration A B C)

/-- **Tag 08PU for the resolution in play, with `C` read over `A` through `B`.** For `B` a
polynomial algebra over `A`, the complex `Ω[P_•⁄A] ⊗[P_•] C` of the standard resolution `P_•` of
`C` over `B` computes `L_{C/A}` in `D(C)`.

Both complexes are derived lower shriek of the sheaf `i^*Ω_{𝒪/A}` on the small model of the site
`C_{C/A}` restricted to polynomial algebras on at most `κ` variables, for `κ` large enough to
contain both resolutions: `P_•` read over `A` by
`CommAlgCat.restrictedCotangentDerivedLowerShriekIso`, and the standard resolution of `C` over
`A` by `CommAlgCat.standardResolutionCotangentDerivedLowerShriekIsoOfLE`. That the right-hand
side mentions no resolution is the content of Tag 08QI's remark that any resolution computes the
cotangent complex.

The isomorphism is produced, not canonical: the comparison it rests on is built from a chosen
projective resolution of the coefficient sheaf. It is therefore stated existentially, which is
what the triangle of Tag 08SA consumes. -/
public theorem nonempty_q_restrictedCotangentComplex_iso_cotangentComplex_restrictedBase
    (hB : Algebra.IsPolynomialAlgebra A B) :
    Nonempty (DerivedCategory.Q.obj (restrictedCotangentComplex.{u, u} A B C) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, u} A (restrictedBase A B C))) := by
  obtain ⟨ιB, ⟨eB⟩⟩ := hB
  refine ⟨restrictedCotangentDerivedLowerShriekIso A B C
      (max (standardResolutionVarCardinal A (restrictedBase A B C))
        (Cardinal.mk ((Σ m : ℕ, (((polynomialComonad.{u, u} B).toFunctor.iterate m).obj
          (CommAlgCat.of B C) : Type u)) ⊕ ιB)))
      (restrictedResolution_isPolynomialAlgebraBelow A B C eB _ (le_max_right _ _)) ≪≫
    (standardResolutionCotangentDerivedLowerShriekIsoOfLE A (restrictedBase A B C) _
      (le_max_left _ _)).symm⟩

end Restricted

section RestrictedTower

attribute [local instance] HasDerivedCategory.standard

/-- **Tag 08PU for the resolution in play.** For ring maps `A → B → C` with `B` a polynomial
algebra over `A`, the complex `Ω[P_•⁄A] ⊗[P_•] C` of the standard resolution `P_•` of `C` over
`B` computes `L_{C/A}` in `D(C)`. This is
`CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex_restrictedBase` read for
an arbitrary `A`-algebra structure on `C` making `A → B → C` a scalar tower: such a structure
is *equal* to the composite one, two algebra structures with the same structure map being
equal. -/
public theorem nonempty_q_restrictedCotangentComplex_iso_cotangentComplex
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (C : Type u) [CommRing C] [Algebra B C] [instAC : Algebra A C] [IsScalarTower A B C]
    (hB : Algebra.IsPolynomialAlgebra A B) :
    Nonempty (DerivedCategory.Q.obj (restrictedCotangentComplex.{u, u} A B C) ≅
      DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, u} A C)) := by
  have h : Algebra.compHom C (algebraMap A B) = instAC :=
    Algebra.algebra_ext _ _ fun a => (IsScalarTower.algebraMap_apply A B C a).symm
  subst h
  exact nonempty_q_restrictedCotangentComplex_iso_cotangentComplex_restrictedBase A B C hB

/-- **Stacks Project, Tag 08SA.** Let `A → B → C` be ring maps. If `B` is a polynomial algebra
over `A`, then there is a distinguished triangle

`L_{B/A} ⊗^𝐋_B C → L_{C/A} → L_{C/B} → (L_{B/A} ⊗^𝐋_B C)[1]`

in `D(C)`. This is the lemma as stated.

The proof is the source's. The standard resolution `P_•` of `C` over `B` is, read over `A`, also
a resolution of `C` over `A` (`CommAlgCat.standardResolution_isResolution_restrictScalars`); the
differentials of the tower `A → B → Pₙ` form a split short exact sequence because `Pₙ` is a
polynomial algebra over `B`, and base changing it to `C` gives a short exact sequence of
complexes of `C`-modules
`Ω[B⁄A] ⊗[B] C → Ω[P_•⁄A] ⊗[P_•] C → Ω[P_•⁄B] ⊗[P_•] C`
(`CommAlgCat.restrictedCotangentComplexShortComplex_shortExact`) whose distinguished triangle is
the one asserted. Its last term is `L_{C/B}` by definition; its first term is `Ω[B⁄A] ⊗[B] C` in
degree `0`, which is `L_{B/A} ⊗^𝐋_B C` by Tag 08QH and the projectivity of `Ω[B⁄A]`
(`CommAlgCat.nonempty_derivedExtensionScalars_cotangentComplex_iso_of_isPolynomialAlgebra`); and
its middle term is `L_{C/A}` because `P_•` and the standard resolution of `C` over `A` are two
resolutions of `C` over `A`, so by Tag 08PU both compute derived lower shriek of `i^*Ω_{𝒪/A}` on
the site `C_{C/A}`
(`CommAlgCat.nonempty_q_restrictedCotangentComplex_iso_cotangentComplex`).

The triangle is stated existentially, as in the source: the identifications of the first and
middle terms are isomorphisms of objects of `D(C)`, which transport a distinguished triangle to
one with the named objects. The three rings are taken in one universe, which is no restriction:
three rings with maps between them always live in a common universe. The conditional form at two
universes, with the identification of the middle term as a hypothesis, is
`CommAlgCat.exists_distTriang_derivedExtensionScalars_of_isPolynomialAlgebra`. -/
@[stacks 08SA]
public theorem exists_distTriang_derivedExtensionScalars_cotangentComplex
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (C : Type u) [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : Algebra.IsPolynomialAlgebra A B) :
    ∃ (f : (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            (algebraMap B C)).functor.obj
          (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, u} A B)) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, u} A C))
      (g : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, u} A C) ⟶
        DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, u} B C))
      (h : DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, u} B C) ⟶
        ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
            (algebraMap B C)).functor.obj
          (DerivedCategory.Q.obj (cotangentComplexOfAlgebra.{u, u} A B)))⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk f g h ∈
        Pretriangulated.distinguishedTriangles (C := DerivedCategory (ModuleCat.{u} C)) :=
  exists_distTriang_derivedExtensionScalars_of_isPolynomialAlgebra.{u, u} A B C hB
    (nonempty_q_restrictedCotangentComplex_iso_cotangentComplex A B C hB)

end RestrictedTower

end CommAlgCat

end
