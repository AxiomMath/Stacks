module

public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso

/-!
# The stalks of the naive cotangent complex

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space `X` and let
`x` be a point of `X`.  The stalk at `x` of the naive cotangent complex `NL_{B/A}` is the naive
cotangent complex `NL_{Bₓ/Aₓ}` of the induced map of stalks.

The two complexes are built from two different presentations of `Bₓ` as a quotient of a
polynomial algebra over `Aₓ`: the stalk of the canonical presentation `A[B] ⟶ B` of sheaves on
the one hand, and the canonical presentation `Aₓ[Bₓ] ⟶ Bₓ` of rings on the other.  The content
of the statement is that those two presentations agree: the stalk `(A[B])ₓ` of the free algebra
is the polynomial algebra `Aₓ[Bₓ]` (Stacks 08TU on stalks), and the stalk of `A[B] ⟶ B` is the
evaluation `Aₓ[Bₓ] → Bₓ` at the variables.  The two terms and the differential of `NL_{B/A}` are
then carried onto those of `NL_{Bₓ/Aₓ}` by the maps on conormal modules and cotangent spaces
induced by that isomorphism of presentations.

## Main definitions

* `Stacks.SheafOfModules.canonicalStalkRingEquiv`: the identification `(A[B])ₓ ≅ Aₓ[Bₓ]`.
* `Stacks.SheafOfModules.canonicalStalkExtension`: the extension of `Bₓ` over `Aₓ` given by the
  stalk of the canonical presentation of `B` over `A`.
* `Stacks.SheafOfModules.canonicalStalkExtensionHom` and
  `Stacks.SheafOfModules.canonicalStalkExtensionInvHom`: the two morphisms of extensions between
  it and `Algebra.Generators.self Aₓ Bₓ`.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv` and
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv`: the identifications of the two
  terms of the stalk of `NL_{B/A}` with the two terms of `NL_{Bₓ/Aₓ}`.

## Main results

* `Stacks.SheafOfModules.bijective_presentationStalkVariable_id`: the stalk of the underlying
  presheaf of sets of `B` is the stalk of `B`.
* `Stacks.SheafOfModules.aeval_canonicalStalkRingEquiv`: the stalk of the canonical presentation
  `A[B] ⟶ B` is, under `(A[B])ₓ ≅ Aₓ[Bₓ]`, the canonical presentation `Aₓ[Bₓ] ⟶ Bₓ`.
* `Stacks.SheafOfModules.bijective_cotangentMap_canonicalStalkExtensionHom` and
  `Stacks.SheafOfModules.bijective_cotangentSpaceMap_canonicalStalkExtensionHom`: the maps the
  isomorphism of presentations induces on conormal modules and on cotangent spaces are bijective.
* `Stacks.SheafOfModules.naiveCotangentStalk_d_eq_cotangentComplex`: under those identifications
  the stalk of the differential of `NL_{B/A}` is the differential of `NL_{Bₓ/Aₓ}`.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_semilinear` and
  `Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv_semilinear`: the two
  identifications are semilinear over the stalk `(A[B])ₓ → Bₓ` of the canonical presentation,
  which, that map being surjective, makes them `Bₓ`-linear.
* `Stacks.SheafOfModules.naiveCotangentStalk_eq_naiveCotangentComplexStalk`: **Stacks 0D09**,
  the three preceding statements in one, which is the isomorphism of two-term complexes of
  `Bₓ`-modules `NL_{B/A, x} = NL_{Bₓ/Aₓ}`.
* `Stacks.SheafOfModules.naiveCotangentComplex_X_negOne_eq_conormalSheaf`,
  `Stacks.SheafOfModules.naiveCotangentComplex_X_zero_eq_tensorDifferentialsSheaf` and
  `Stacks.SheafOfModules.canonicalConormalSequence_f_eq_conormalSequenceFHom`: the objects the
  three statements above are about are the two terms and the differential of `NL_{B/A}`.

## Implementation notes

The terms of `NL_{B/A}` are named here as the two terms of the canonical conormal sequence, which
is what they are: `Stacks.SheafOfModules.naiveCotangentComplex_X_negOne`,
`Stacks.SheafOfModules.naiveCotangentComplex_X_zero` and
`Stacks.SheafOfModules.naiveCotangentComplex_d_negOne_zero` identify the degree `-1` term, the
degree `0` term and the differential of the complex with the conormal sheaf, the
tensor-differentials sheaf and the left-hand map of that sequence.  Working with the sequence
rather than with the complex avoids transporting the stalks across those three equalities.

The two identifications of terms are recorded as additive equivalences together with their
semilinearity over the stalk of the presentation, rather than as linear equivalences: the first
leg of each is linear over `(A[B])ₓ` and the second is linear over `Bₓ`, and the stalk of a
conormal sheaf does not carry the two actions as a scalar tower by instance search.

The canonical presentation is spelled `Stacks.SheafOfModules.presentation … (𝟙 _)`, the
presentation attached to the identity family of generators, which is definitionally
`Stacks.Sites.FreeAlgebra.canonicalPresentation` (`canonicalPresentation_eq_desc`); this is the
spelling the stalk lemmas of
`StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPresentationQuasiIso` are stated in.

## References

* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of the
  naive cotangent complex.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical
  polynomial presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

/-! ### The stalk of the underlying presheaf of sets -/

section Variables

variable {X : TopCat.{u}} (B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)

/-- **The stalk of the underlying presheaf of sets of `B` is the stalk of `B`.** The comparison
map is the one induced by the identity family of generators, which carries the germ of a section
to its germ in the sheaf of rings. -/
theorem bijective_presentationStalkVariable_id :
    Function.Bijective (presentationStalkVariable B
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) x) := by
  constructor
  · intro ξ₁ ξ₂ h
    obtain ⟨U₁, h₁, t₁, rfl⟩ :=
      exists_germ_eq (underlyingPresheaf (Opens.grothendieckTopology X) B) ξ₁
    obtain ⟨U₂, h₂, t₂, rfl⟩ :=
      exists_germ_eq (underlyingPresheaf (Opens.grothendieckTopology X) B) ξ₂
    rw [presentationStalkVariable_germ, presentationStalkVariable_germ] at h
    obtain ⟨W, hW, iU, iV, e⟩ := germ_eq B.obj x h₁ h₂ _ _ h
    exact germ_ext (underlyingPresheaf (Opens.grothendieckTopology X) B) W hW iU iV e
  · intro t
    obtain ⟨U, hx, b, rfl⟩ := exists_germ_eq B.obj t
    exact ⟨(germ (underlyingPresheaf (Opens.grothendieckTopology X) B) U x hx).hom b,
      presentationStalkVariable_germ B (underlyingPresheaf (Opens.grothendieckTopology X) B)
        (𝟙 _) x U hx b⟩

end Variables

/-! ### The stalk of the canonical presentation is the canonical presentation of the stalk -/

section Extension

open Stacks.RelativeDifferentialStalk (algebraStalk)

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (x : X)

/-- **The identification `(A[B])ₓ ≅ Aₓ[Bₓ]`.** It is the identification of the stalk of the free
algebra with a polynomial algebra on the stalk of the underlying presheaf of sets of `B`,
followed by the renaming of the variables along the identification of that stalk with `Bₓ`. -/
def canonicalStalkRingEquiv :
    ToType (TopCat.Presheaf.stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x) ≃+*
      MvPolynomial (ToType (TopCat.Presheaf.stalk B.obj x))
        (ToType (TopCat.Presheaf.stalk A.obj x)) :=
  (freeAlgebraSheafStalkRingEquiv A (underlyingPresheaf (Opens.grothendieckTopology X) B) x).trans
    (MvPolynomial.renameEquiv (ToType (TopCat.Presheaf.stalk A.obj x))
      (Equiv.ofBijective _ (bijective_presentationStalkVariable_id B x))).toRingEquiv

/-- The identification carries the image of a coefficient to a constant polynomial. -/
theorem canonicalStalkRingEquiv_coefficientMap (r : ToType (TopCat.Presheaf.stalk A.obj x)) :
    canonicalStalkRingEquiv A B x
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)).hom).hom r) =
      MvPolynomial.C r := by
  refine Eq.trans (congrArg (MvPolynomial.rename
      (Equiv.ofBijective _ (bijective_presentationStalkVariable_id B x)))
    (freeAlgebraSheafStalkRingEquiv_coefficientMap A
      (underlyingPresheaf (Opens.grothendieckTopology X) B) x r)) ?_
  exact MvPolynomial.rename_C _ r

/-- **The stalk of the canonical presentation is the canonical presentation of the stalk.**
Under the identification `(A[B])ₓ ≅ Aₓ[Bₓ]` the stalk of `A[B] ⟶ B` is the evaluation
`Aₓ[Bₓ] → Bₓ`, `[b] ↦ b`, of the canonical presentation of `Bₓ` over `Aₓ`. -/
theorem aeval_canonicalStalkRingEquiv
    (p : ToType (TopCat.Presheaf.stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x)) :
    letI := algebraStalk a.hom x
    MvPolynomial.aeval (R := ToType (TopCat.Presheaf.stalk A.obj x)) _root_.id
        (canonicalStalkRingEquiv A B x p) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom p := by
  let := algebraStalk a.hom x
  refine Eq.trans ?_ (stalkFunctor_map_presentation_apply A B a
    (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) x p).symm
  refine Eq.trans (MvPolynomial.aeval_def _ _) ?_
  exact MvPolynomial.eval₂_rename _ _ _ _

/-- The extension of `Bₓ` over `Aₓ` given by the stalk of the canonical presentation
`A[B] ⟶ B`. -/
abbrev canonicalStalkExtension :
    letI := algebraStalk a.hom x
    Algebra.Extension.{u} (ToType (TopCat.Presheaf.stalk A.obj x))
      (ToType (TopCat.Presheaf.stalk B.obj x)) :=
  stalkExtension A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) a x
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B
      (underlyingPresheaf (Opens.grothendieckTopology X) B) a (𝟙 _))

/-- The identification `(A[B])ₓ ≅ Aₓ[Bₓ]` is a homomorphism of `Aₓ`-algebras. -/
theorem canonicalStalkRingEquiv_algebraMap (r : ToType (TopCat.Presheaf.stalk A.obj x)) :
    letI := algebraStalk a.hom x
    canonicalStalkRingEquiv A B x
        (algebraMap (ToType (TopCat.Presheaf.stalk A.obj x))
          (canonicalStalkExtension A B a x).Ring r) =
      algebraMap (ToType (TopCat.Presheaf.stalk A.obj x))
        (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.Ring
        (algebraMap (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk A.obj x)) r) := by
  let := algebraStalk a.hom x
  refine Eq.trans (canonicalStalkRingEquiv_coefficientMap A B x r) ?_
  exact DFunLike.congr_fun (MvPolynomial.algebraMap_eq
    (ToType (TopCat.Presheaf.stalk A.obj x)) (ToType (TopCat.Presheaf.stalk B.obj x))).symm r

/-- The identification `(A[B])ₓ ≅ Aₓ[Bₓ]` is compatible with the two presentations of `Bₓ`. -/
theorem algebraMap_canonicalStalkRingEquiv
    (p : ToType (TopCat.Presheaf.stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x)) :
    letI := algebraStalk a.hom x
    algebraMap (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.Ring
        (ToType (TopCat.Presheaf.stalk B.obj x)) (canonicalStalkRingEquiv A B x p) =
      algebraMap (ToType (TopCat.Presheaf.stalk B.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))
        (algebraMap (canonicalStalkExtension A B a x).Ring
          (ToType (TopCat.Presheaf.stalk B.obj x)) p) := by
  let := algebraStalk a.hom x
  exact aeval_canonicalStalkRingEquiv A B a x p

/-- **The stalk of the canonical presentation of `B` over `A` is the canonical presentation of
`Bₓ` over `Aₓ`**, as a morphism of extensions of `Bₓ` over `Aₓ` whose underlying ring
homomorphism is the identification `(A[B])ₓ ≅ Aₓ[Bₓ]`. -/
def canonicalStalkExtensionHom :
    letI := algebraStalk a.hom x
    (canonicalStalkExtension A B a x).Hom
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension :=
  letI := algebraStalk a.hom x
  { toRingHom := (canonicalStalkRingEquiv A B x).toRingHom
    toRingHom_algebraMap := canonicalStalkRingEquiv_algebraMap A B a x
    algebraMap_toRingHom := algebraMap_canonicalStalkRingEquiv A B a x }

/-- The morphism of extensions in the other direction, with underlying ring homomorphism the
inverse identification `Aₓ[Bₓ] ≅ (A[B])ₓ`. -/
def canonicalStalkExtensionInvHom :
    letI := algebraStalk a.hom x
    (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.Hom
      (canonicalStalkExtension A B a x) :=
  letI := algebraStalk a.hom x
  { toRingHom := (canonicalStalkRingEquiv A B x).symm.toRingHom
    toRingHom_algebraMap := fun r =>
      (RingEquiv.symm_apply_eq _).mpr (canonicalStalkRingEquiv_algebraMap A B a x r).symm
    algebraMap_toRingHom := fun q =>
      ((congrArg (algebraMap (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
            (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.Ring
          (ToType (TopCat.Presheaf.stalk B.obj x)))
        ((canonicalStalkRingEquiv A B x).apply_symm_apply q)).symm.trans
        (algebraMap_canonicalStalkRingEquiv A B a x
          ((canonicalStalkRingEquiv A B x).symm q))).symm }

/-- The two morphisms of extensions compose to the identity. -/
theorem canonicalStalkExtensionInvHom_comp_hom :
    letI := algebraStalk a.hom x
    (canonicalStalkExtensionInvHom A B a x).comp (canonicalStalkExtensionHom A B a x) =
      Algebra.Extension.Hom.id (canonicalStalkExtension A B a x) := by
  let := algebraStalk a.hom x
  refine Algebra.Extension.Hom.ext (RingHom.ext fun p => ?_)
  exact (canonicalStalkRingEquiv A B x).symm_apply_apply p

/-- The two morphisms of extensions compose to the identity in the other order. -/
theorem canonicalStalkExtensionHom_comp_invHom :
    letI := algebraStalk a.hom x
    (canonicalStalkExtensionHom A B a x).comp (canonicalStalkExtensionInvHom A B a x) =
      Algebra.Extension.Hom.id (Algebra.Generators.self
        (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension := by
  let := algebraStalk a.hom x
  refine Algebra.Extension.Hom.ext (RingHom.ext fun q => ?_)
  exact (canonicalStalkRingEquiv A B x).apply_symm_apply q

/-- **The conormal modules of the two presentations agree.** -/
theorem bijective_cotangentMap_canonicalStalkExtensionHom :
    letI := algebraStalk a.hom x
    Function.Bijective
      (Algebra.Extension.Cotangent.map (canonicalStalkExtensionHom A B a x)) := by
  let := algebraStalk a.hom x
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Algebra.Extension.Cotangent.map (canonicalStalkExtensionInvHom A B a x), fun z => ?_,
      fun z => ?_⟩
  · have := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp
      (f := canonicalStalkExtensionHom A B a x) (g := canonicalStalkExtensionInvHom A B a x)) z
    rw [canonicalStalkExtensionInvHom_comp_hom, Algebra.Extension.Cotangent.map_id] at this
    exact this.symm
  · have := DFunLike.congr_fun (Algebra.Extension.Cotangent.map_comp
      (f := canonicalStalkExtensionInvHom A B a x) (g := canonicalStalkExtensionHom A B a x)) z
    rw [canonicalStalkExtensionHom_comp_invHom, Algebra.Extension.Cotangent.map_id] at this
    exact this.symm

/-- **The cotangent spaces of the two presentations agree.** -/
theorem bijective_cotangentSpaceMap_canonicalStalkExtensionHom :
    letI := algebraStalk a.hom x
    Function.Bijective
      (Algebra.Extension.CotangentSpace.map (canonicalStalkExtensionHom A B a x)) := by
  let := algebraStalk a.hom x
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Algebra.Extension.CotangentSpace.map (canonicalStalkExtensionInvHom A B a x), fun z => ?_,
      fun z => ?_⟩
  · have := DFunLike.congr_fun (Algebra.Extension.CotangentSpace.map_comp
      (f := canonicalStalkExtensionHom A B a x) (g := canonicalStalkExtensionInvHom A B a x)) z
    rw [canonicalStalkExtensionInvHom_comp_hom, Algebra.Extension.CotangentSpace.map_id] at this
    exact this.symm
  · have := DFunLike.congr_fun (Algebra.Extension.CotangentSpace.map_comp
      (f := canonicalStalkExtensionInvHom A B a x) (g := canonicalStalkExtensionHom A B a x)) z
    rw [canonicalStalkExtensionHom_comp_invHom, Algebra.Extension.CotangentSpace.map_id] at this
    exact this.symm

/-! ### The stalk of the naive cotangent complex -/

/-- **The degree `-1` terms agree.** The stalk at `x` of the conormal sheaf of the canonical
presentation of `B` over `A`, which is the degree `-1` term of `NL_{B/A}`
(`Stacks.SheafOfModules.naiveCotangentComplex_X_negOne`), is the conormal module of the
canonical presentation of `Bₓ` over `Aₓ`, which is the degree `1` term of `NL_{Bₓ/Aₓ}`. -/
def naiveCotangentStalkCotangentEquiv :
    letI := algebraStalk a.hom x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (conormalSheaf (Opens.grothendieckTopology X)
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)
      ≃+ (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.Cotangent :=
  letI := algebraStalk a.hom x
  (conormalSheafStalkLinearEquiv (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x).toAddEquiv.trans
    (AddEquiv.ofBijective
      (Algebra.Extension.Cotangent.map
        (canonicalStalkExtensionHom A B a x)).toAddMonoidHom
      (bijective_cotangentMap_canonicalStalkExtensionHom A B a x))

/-- `naiveCotangentStalkCotangentEquiv` sends a germ `ξ` to the image under the map of conormal
modules induced by `canonicalStalkExtensionHom` of the element of the conormal module of the
stalk presentation corresponding to `ξ`. -/
theorem naiveCotangentStalkCotangentEquiv_apply
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    naiveCotangentStalkCotangentEquiv A B a x ξ =
      Algebra.Extension.Cotangent.map (canonicalStalkExtensionHom A B a x)
        (conormalSheafStalkLinearEquiv (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x ξ) := rfl

/-- **The degree `0` terms agree.** The stalk at `x` of `B ⊗[A[B]] Ω[A[B]/A]`, which is the
degree `0` term of `NL_{B/A}` (`Stacks.SheafOfModules.naiveCotangentComplex_X_zero`), is
`Bₓ ⊗[Aₓ[Bₓ]] Ω[Aₓ[Bₓ]/Aₓ]`, the degree `0` term of `NL_{Bₓ/Aₓ}`. -/
def naiveCotangentStalkCotangentSpaceEquiv :
    letI := algebraStalk a.hom x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
          (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B))
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)
      ≃+ (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.CotangentSpace :=
  letI := algebraStalk a.hom x
  letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  (cotangentSpaceStalkLinearEquiv A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x).toAddEquiv.trans
    (AddEquiv.ofBijective
      (Algebra.Extension.CotangentSpace.map
        (canonicalStalkExtensionHom A B a x)).toAddMonoidHom
      (bijective_cotangentSpaceMap_canonicalStalkExtensionHom A B a x))

/-- `naiveCotangentStalkCotangentSpaceEquiv` sends a germ `ξ` to the image under the map of
cotangent spaces induced by `canonicalStalkExtensionHom` of the element of the cotangent space of
the stalk presentation corresponding to `ξ`. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_apply
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    naiveCotangentStalkCotangentSpaceEquiv A B a x ξ =
      Algebra.Extension.CotangentSpace.map (canonicalStalkExtensionHom A B a x)
        (cotangentSpaceStalkLinearEquiv A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B))
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x ξ) := rfl

/-- **The identification of the degree `-1` terms is semilinear** over the stalk
`(A[B])ₓ → Bₓ` of the canonical presentation.  That map is surjective
(`Stacks.Sites.Conormal.stalkMap_surjective`), so this says the identification is a
`Bₓ`-isomorphism. -/
theorem naiveCotangentStalkCotangentEquiv_semilinear
    (r : ToType (TopCat.Presheaf.stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    naiveCotangentStalkCotangentEquiv A B a x (r • ξ) =
      (show ToType (TopCat.Presheaf.stalk B.obj x) from
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
            (presentation (Opens.grothendieckTopology X) A B a
              (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r) •
        naiveCotangentStalkCotangentEquiv A B a x ξ := by
  let := algebraStalk a.hom x
  refine Eq.trans (naiveCotangentStalkCotangentEquiv_apply A B a x _) ?_
  refine Eq.trans ?_ (congrArg (fun z => (show ToType (TopCat.Presheaf.stalk B.obj x) from
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r) • z)
    (naiveCotangentStalkCotangentEquiv_apply A B a x ξ).symm)
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map
    (canonicalStalkExtensionHom A B a x)) (map_smul (conormalSheafStalkLinearEquiv
      (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x) r ξ)) ?_
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map
      (canonicalStalkExtensionHom A B a x))
    (Algebra.Extension.Cotangent.val_smul' (P := canonicalStalkExtension A B a x) r _).symm) ?_
  exact map_smul (Algebra.Extension.Cotangent.map (canonicalStalkExtensionHom A B a x)) _ _

/-- **The identification of the degree `0` terms is semilinear** over the stalk `(A[B])ₓ → Bₓ`
of the canonical presentation, hence a `Bₓ`-isomorphism. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_semilinear
    (r : ToType (TopCat.Presheaf.stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    naiveCotangentStalkCotangentSpaceEquiv A B a x (r • ξ) =
      (show ToType (TopCat.Presheaf.stalk B.obj x) from
          ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
            (presentation (Opens.grothendieckTopology X) A B a
              (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r) •
        naiveCotangentStalkCotangentSpaceEquiv A B a x ξ := by
  let := algebraStalk a.hom x
  let := algebraStalk (presentation (Opens.grothendieckTopology X) A B a
    (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom x
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  refine Eq.trans (naiveCotangentStalkCotangentSpaceEquiv_apply A B a x _) ?_
  refine Eq.trans ?_ (congrArg (fun z => (show ToType (TopCat.Presheaf.stalk B.obj x) from
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r) • z)
    (naiveCotangentStalkCotangentSpaceEquiv_apply A B a x ξ).symm)
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
    (canonicalStalkExtensionHom A B a x)) (map_smul (cotangentSpaceStalkLinearEquiv A
      (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B))
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x) r ξ)) ?_
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
      (canonicalStalkExtensionHom A B a x))
    (algebraMap_smul (ToType (TopCat.Presheaf.stalk B.obj x)) r
      ((cotangentSpaceStalkLinearEquiv A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x) ξ)).symm) ?_
  exact map_smul (Algebra.Extension.CotangentSpace.map
    (canonicalStalkExtensionHom A B a x)) _ _

/-! ### The two terms and the differential of `NL_{B/A}`

These three statements name the degree `-1` term, the degree `0` term and the differential of
`NL_{B/A}` in the spelling the stalk identifications above are stated in. -/

/-- The degree `-1` term of `NL_{B/A}` is the conormal sheaf of the canonical presentation. -/
theorem naiveCotangentComplex_X_negOne_eq_conormalSheaf :
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a).X (-1) =
      conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) :=
  naiveCotangentComplex_X_negOne.{u, u, u, u} (Opens.grothendieckTopology X) A B a

/-- The degree `0` term of `NL_{B/A}` is the tensor-differentials sheaf of the canonical
presentation. -/
theorem naiveCotangentComplex_X_zero_eq_tensorDifferentialsSheaf :
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a).X 0 =
      tensorDifferentialsSheaf (Opens.grothendieckTopology X) A
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) :=
  naiveCotangentComplex_X_zero.{u, u, u, u} (Opens.grothendieckTopology X) A B a

/-- The differential of `NL_{B/A}` is, up to the two identifications of terms above, the
left-hand map of the canonical conormal sequence
(`Stacks.SheafOfModules.naiveCotangentComplex_d_negOne_zero`), and that map is the one whose
stalk `Stacks.Sites.Conormal.conormalSequenceStalkMapF` is. -/
theorem canonicalConormalSequence_f_eq_conormalSequenceFHom :
    (canonicalConormalSequence.{u, u, u, u} (Opens.grothendieckTopology X) A B a).f =
      conormalSequenceFHom A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) := rfl

/-- **Under the identifications of the terms the differentials correspond**: the stalk of the
differential of `NL_{B/A}` is the differential of `NL_{Bₓ/Aₓ}`. -/
theorem naiveCotangentStalk_d_eq_cotangentComplex
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (conormalSheaf (Opens.grothendieckTopology X)
        (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
        (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _))).val.presheaf x)) :
    letI := algebraStalk a.hom x
    naiveCotangentStalkCotangentSpaceEquiv A B a x
        (conormalSequenceStalkMapF A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B))
          (presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x ξ) =
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
          (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.cotangentComplex
        (naiveCotangentStalkCotangentEquiv A B a x ξ) := by
  let := algebraStalk a.hom x
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  have hd := conormalSequenceStalkMapF_eq_cotangentComplex' A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x a
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X) A B
      (underlyingPresheaf (Opens.grothendieckTopology X) B) a (𝟙 _)) ξ
  refine Eq.trans (naiveCotangentStalkCotangentSpaceEquiv_apply A B a x _) ?_
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
    (canonicalStalkExtensionHom A B a x)) hd) ?_
  exact (Algebra.Extension.CotangentSpace.map_cotangentComplex
    (canonicalStalkExtensionHom A B a x) _).trans
    (congrArg (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
        (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.cotangentComplex
      (naiveCotangentStalkCotangentEquiv_apply A B a x ξ).symm)

/-- `NL_{𝓑/𝓐, x} = NL_{𝓑ₓ/𝓐ₓ}`: the stalk at `x` of the naive cotangent complex of `B` over `A`
is the naive cotangent complex of `Bₓ` over `Aₓ`.

The underlying additive bijections of the two terms are
`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv` in degree `-1` and
`Stacks.SheafOfModules.naiveCotangentStalkCotangentSpaceEquiv` in degree `0`; the three clauses
say that both are semilinear over the stalk `(A[B])ₓ → Bₓ` of the canonical presentation, which
is surjective, so they are `Bₓ`-linear, and that they commute with the differentials. -/
@[stacks 0D09]
theorem naiveCotangentStalk_eq_naiveCotangentComplexStalk :
    letI := algebraStalk a.hom x
    (∀ (r : ToType (TopCat.Presheaf.stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x)) ξ,
        naiveCotangentStalkCotangentEquiv A B a x (r • ξ) =
          (show ToType (TopCat.Presheaf.stalk B.obj x) from
              ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
                (presentation (Opens.grothendieckTopology X) A B a
                  (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r) •
            naiveCotangentStalkCotangentEquiv A B a x ξ) ∧
      (∀ (r : ToType (TopCat.Presheaf.stalk (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj x)) ξ,
        naiveCotangentStalkCotangentSpaceEquiv A B a x (r • ξ) =
          (show ToType (TopCat.Presheaf.stalk B.obj x) from
              ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
                (presentation (Opens.grothendieckTopology X) A B a
                  (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom).hom r) •
            naiveCotangentStalkCotangentSpaceEquiv A B a x ξ) ∧
      ∀ ξ, naiveCotangentStalkCotangentSpaceEquiv A B a x
            (conormalSequenceStalkMapF A (freeAlgebraSheaf (Opens.grothendieckTopology X) A
              (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
              (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
                (underlyingPresheaf (Opens.grothendieckTopology X) B))
              (presentation (Opens.grothendieckTopology X) A B a
                (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x ξ) =
          (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj x))
              (ToType (TopCat.Presheaf.stalk B.obj x))).toExtension.cotangentComplex
            (naiveCotangentStalkCotangentEquiv A B a x ξ) :=
  ⟨naiveCotangentStalkCotangentEquiv_semilinear A B a x,
    naiveCotangentStalkCotangentSpaceEquiv_semilinear A B a x,
    naiveCotangentStalk_d_eq_cotangentComplex A B a x⟩

end Extension

end Stacks.SheafOfModules

end

end
