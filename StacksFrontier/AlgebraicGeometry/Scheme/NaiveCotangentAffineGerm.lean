module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineComparison

/-!
# The germ of the comparison on sections of the naive cotangent complex

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space `X`, let `U`
be an open of `X` and let `x` be a point of `U`.  Taking sections over `U` gives the canonical map

`NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)`

of `Stacks.SheafOfModules.sectionsNaiveCotangentComparison`, and taking stalks at `x` gives the
identification `NL_{B/A, x} = NL_{Bₓ/Aₓ}` of Stacks 0D09.  This file identifies the germ at `x`
of the first with the map of naive cotangent complexes induced by the morphism of extensions

`Generators.self A(U) B(U) ⟶ Generators.self Aₓ Bₓ`

attached to the commuting square of germ maps.  This is the step the proof of Stacks 0D0I needs
in order to compare its sheaf-level comparison map with the stalkwise quasi-isomorphism of
`Stacks.NaiveCotangentAffineComparison.isQuasiIso_nlExtensionBaseChangeMap_canonicalStalkHom`.

## Main definitions

* `Stacks.SheafOfModules.moduleGerm` is the germ at `x` of a section of a presheaf of modules.
* `Stacks.SheafOfModules.algebraGerm` and `Stacks.SheafOfModules.algebraGermComp` are the algebra
  structures the germ maps give, and `Stacks.SheafOfModules.isScalarTower_germ` is the tower they
  form.
* `Stacks.SheafOfModules.germPolynomialHom` is the map `A(U)[B(U)] ⟶ Aₓ[Bₓ]` acting on
  coefficients and on variables by the germ maps, and
  `Stacks.SheafOfModules.germSelfHom` is the morphism of extensions
  `Generators.self A(U) B(U) ⟶ Generators.self Aₓ Bₓ` it underlies.

## Main results

* `Stacks.SheafOfModules.canonicalStalkRingEquiv_germ_freeAlgebraSectionsMap`: **the bridge.**
  Under the identification `(A[B])ₓ ≅ Aₓ[Bₓ]` of
  `Stacks.SheafOfModules.canonicalStalkRingEquiv`, the germ at `x` of the lax comparison
  `A(U)[B(U)] ⟶ (A[B])(U)` is `Stacks.SheafOfModules.germPolynomialHom`.  Both halves of the
  comparison on sections are built from the lax comparison and both halves of the identification
  of stalks are built from `(A[B])ₓ ≅ Aₓ[Bₓ]`, so this single formula is what relates them.
* `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_germ_sectionsConormalComparison`: the
  germ of the degree `-1` component of the comparison on sections is
  `Algebra.Extension.Cotangent.map` of the morphism of extensions given by the germ maps.
* the same in degree `0`, on the elements `1 ⊗ d p`, with
  `Algebra.Extension.CotangentSpace.map`, in the same namespace:
  `naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_one_tmul`.
* `Stacks.NaiveCotangent.cotangentSpace_hom_ext`: two additive maps out of the cotangent space of
  an extension agreeing on the elements `b ⊗ d p` are equal.
* `Stacks.SheafOfModules.presentation_freeAlgebraSectionsMap`: the lax comparison followed by the
  presentation `A[B] ⟶ B` on sections is the structural map of the canonical presentation of
  `B(U)` over `A(U)`.
* `Stacks.SheafOfModules.toAssociatedModule_quotient_mk_tmul`: the image under the unit of
  sheafification of `[s] ⊗ ω` is the image of `s` under the presentation acting on the image of
  `1 ⊗ ω`.  This is how a scalar of the degree `0` comparison is absorbed into the left factor of
  a pure tensor, which is what the degree `0` formula for a general element `b ⊗ d p` needs.

## Implementation notes

**Why the germ of a section of a presheaf of modules is named.**  Identifying the type of a
section of a concrete presheaf of modules with the type of a section of its underlying presheaf of
abelian groups is a definitional unfolding of a sheafification, and at the concrete presentation
`A[B] ⟶ B` it exhausts the elaborator's budget.  `Stacks.SheafOfModules.moduleGerm` performs that
identification once over an abstract presheaf of modules, where the terms are small; instantiating
it afterwards does no unification at all.  The same device is why
`Stacks.SheafOfModules.toAssociatedModule_quotient_mk_tmul` is stated over abstract sheaves of
rings rather than at the canonical presentation.

**Rewriting versus composing.**  The two germ formulas are proved by rewriting the goal with the
section-level formulas `Stacks.SheafOfModules.sectionsConormalComparison_mk` and
`Stacks.SheafOfModules.sectionsTensorComparison_tmul` first, and only then composing with
`Eq.trans`.  Supplying the same rewrite as `congrArg` applied to the identification of stalks
makes the elaborator solve a higher-order unification problem whose solution needs the same
unfolding of a sheafification, and it does not terminate within the budget.

The degree `0` formula is proved here only on the elements `1 ⊗ d p`; the general element
`b ⊗ d p` is treated in `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineGermTensor`.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is a
  step.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical polynomial
  presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

/-! ### Maps out of the cotangent space of an extension -/

namespace Stacks.NaiveCotangent

/-- **Two additive maps out of the cotangent space agreeing on the elements `b ⊗ d p` are
equal.**  Those elements generate `S ⊗[P] Ω[P⁄R]` as an abelian group: the pure tensors generate,
and the universal differentials span `Ω[P⁄R]` over `P`, a scalar `r` being absorbed into the left
factor. -/
theorem cotangentSpace_hom_ext {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) {M : Type*} [AddCommGroup M]
    (Φ Ψ : P.CotangentSpace →+ M)
    (h : ∀ (b : S) (p : P.Ring),
      Φ (b ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p) =
        Ψ (b ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p)) :
    Φ = Ψ := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => rw [map_add, map_add, hz, hw]
  | tmul b₀ ω₀ =>
      have hω : ∀ (ω : KaehlerDifferential R P.Ring) (b : S),
          Φ (b ⊗ₜ[P.Ring] ω) = Ψ (b ⊗ₜ[P.Ring] ω) := by
        intro ω
        have mem : ω ∈ Submodule.span P.Ring
            (Set.range (KaehlerDifferential.D R P.Ring)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction mem using Submodule.span_induction with
        | mem y hy => obtain ⟨y, rfl⟩ := hy; exact fun b => h b y
        | zero =>
            intro b
            rw [TensorProduct.tmul_zero, map_zero, map_zero]
        | add ω₁ ω₂ _ _ ih₁ ih₂ =>
            intro b
            rw [TensorProduct.tmul_add, map_add, map_add, ih₁ b, ih₂ b]
        | smul r ω _ ih =>
            intro b
            rw [← TensorProduct.smul_tmul r b ω]
            exact ih (r • b)
      exact hω ω₀ b₀

end Stacks.NaiveCotangent

/-! ### The germ of the lax comparison on sections -/

namespace Stacks.SheafOfModules

open TopCat.Presheaf Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

/-- **The germ at `x` of a section over `U` of a presheaf of modules.**  This is
`TopCat.Presheaf.germ` of the underlying presheaf of abelian groups. -/
abbrev moduleGerm {X : TopCat.{u}} {O : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} O)
    (x : X) (U : Opens X) (hx : x ∈ U) (s : M.obj (op U)) :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
  TopCat.Presheaf.germ M.presheaf U x hx s

section Germ

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (x : X)
  (U : Opens X) (hx : x ∈ U)

/-- **The stalk of a sheaf of rings as an algebra over its sections**, through the germ map at a
point of the open.  This is the change of base along which the comparison on sections is compared
with the comparison on stalks. -/
abbrev algebraGerm : Algebra (ToType (F.obj.obj (op U))) (ToType (stalk F.obj x)) :=
  (germ F.obj U x hx).hom.toAlgebra

end Germ

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) (x : X) (U : Opens X) (hx : x ∈ U)

open TopCat.Presheaf.ExtensionByInitial in
/-- **The germ of the lax comparison is evaluation at germs.**  Under the identification
`(A[B])ₓ ≅ Aₓ[Bₓ]` of the stalk of the free algebra with a polynomial algebra on the stalk of the
underlying presheaf of sets of `B`, the germ at `x` of the image of `p ∈ A(U)[B(U)]` under the
lax comparison `A(U)[B(U)] ⟶ (A[B])(U)` is the evaluation of `p` at the germs of its coefficients
and of its variables. -/
theorem freeAlgebraSheafStalkRingEquiv_germ_freeAlgebraSectionsMap
    (p : MvPolynomial (ToType (B.obj.obj (op U))) (ToType (A.obj.obj (op U)))) :
    freeAlgebraSheafStalkRingEquiv A (underlyingPresheaf (Opens.grothendieckTopology X) B) x
        ((germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj U x hx).hom
          (freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) p)) =
      polynomialStalkEval A (underlyingPresheaf (Opens.grothendieckTopology X) B) x U hx p := by
  have h0 : (germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj U x hx).hom
        (freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) p) =
      (stalkSheafifyIso (polynomialPresheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) x).hom.hom
        (polynomialGermHom A (underlyingPresheaf (Opens.grothendieckTopology X) B) x U hx p) :=
    (stalkFunctor_map_germ_apply U x hx
      ((toSheafification (Opens.grothendieckTopology X) CommRingCat.{u}).app
        (polynomialPresheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B))) p).symm
  rw [h0, freeAlgebraSheafStalkRingEquiv_sheafify, polynomialStalkHom_germ]

/-- **The polynomial map induced by the germ maps.**  The map `A(U)[B(U)] ⟶ Aₓ[Bₓ]` acting on
coefficients by the germ map of `A` and sending the variable `X_b` to the variable indexed by the
germ of `b`. -/
def germPolynomialHom :
    MvPolynomial (ToType (B.obj.obj (op U))) (ToType (A.obj.obj (op U))) →+*
      MvPolynomial (ToType (stalk B.obj x)) (ToType (stalk A.obj x)) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (germ A.obj U x hx).hom)
    (fun b => MvPolynomial.X ((germ B.obj U x hx).hom b))

/-- The polynomial map induced by the germ maps acts on coefficients by the germ map of `A`. -/
theorem germPolynomialHom_C (r : ToType (A.obj.obj (op U))) :
    germPolynomialHom A B x U hx (MvPolynomial.C r) =
      MvPolynomial.C ((germ A.obj U x hx).hom r) :=
  MvPolynomial.eval₂Hom_C _ _ r

/-- The polynomial map induced by the germ maps carries the variable `X_b` to the variable
indexed by the germ of `b`. -/
theorem germPolynomialHom_X (b : ToType (B.obj.obj (op U))) :
    germPolynomialHom A B x U hx (MvPolynomial.X b) =
      MvPolynomial.X ((germ B.obj U x hx).hom b) :=
  MvPolynomial.eval₂Hom_X' _ _ b

/-- **The bridge.**  Under the identification `(A[B])ₓ ≅ Aₓ[Bₓ]` of
`Stacks.SheafOfModules.canonicalStalkRingEquiv`, the germ at `x` of the lax comparison on
sections is the polynomial map induced by the germ maps on coefficients and on variables.

This is what relates the comparison on sections of
`Stacks.SheafOfModules.sectionsNaiveCotangentComparison` to the identification of stalks of
Stacks 0D09: everything the former is built from is the image of a polynomial under the lax
comparison, and everything the latter is built from is a polynomial over `Aₓ`. -/
theorem canonicalStalkRingEquiv_germ_freeAlgebraSectionsMap
    (p : MvPolynomial (ToType (B.obj.obj (op U))) (ToType (A.obj.obj (op U)))) :
    canonicalStalkRingEquiv A B x
        ((germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A
            (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj U x hx).hom
          (freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) p)) =
      germPolynomialHom A B x U hx p := by
  refine Eq.trans (congrArg (MvPolynomial.rename
      (Equiv.ofBijective _ (bijective_presentationStalkVariable_id B x)))
    (freeAlgebraSheafStalkRingEquiv_germ_freeAlgebraSectionsMap A B x U hx p)) ?_
  refine DFunLike.congr_fun (?_ : ((MvPolynomial.rename
      (Equiv.ofBijective _ (bijective_presentationStalkVariable_id B x))).toRingHom.comp
      (polynomialStalkEval A (underlyingPresheaf (Opens.grothendieckTopology X) B) x U hx)) =
    germPolynomialHom A B x U hx) p
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun b => ?_)
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      polynomialStalkEval_C, MvPolynomial.rename_C, germPolynomialHom_C]
  · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      polynomialStalkEval_X, MvPolynomial.rename_X, germPolynomialHom_X]
    exact congrArg MvPolynomial.X (presentationStalkVariable_germ B
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _) x U hx b)

/-! ### The morphism of extensions given by the germ maps -/

/-- **`Bₓ` as an algebra over `A(U)`**, through the sections of `a` over `U` followed by the germ
map of `B`.  This is the base of the two scalar towers the germ square gives. -/
abbrev algebraGermComp :
    Algebra (ToType (A.obj.obj (op U))) (ToType (stalk B.obj x)) :=
  ((germ B.obj U x hx).hom.comp (a.hom.app (op U)).hom).toAlgebra

/-- **The germ square commutes**, as a scalar tower `A(U) → Aₓ → Bₓ`: taking the germ of a
section of `A` and then its image in `Bₓ` is taking the image in `B(U)` and then the germ. -/
theorem isScalarTower_germ :
    letI := algebraGerm A x U hx
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGermComp A B a x U hx
    IsScalarTower (ToType (A.obj.obj (op U))) (ToType (stalk A.obj x))
      (ToType (stalk B.obj x)) := by
  let := algebraGerm A x U hx
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := algebraGermComp A B a x U hx
  exact IsScalarTower.of_algebraMap_eq fun r =>
    (stalkFunctor_map_germ_apply U x hx a.hom r).symm

/-- **The morphism of canonical presentations given by the germ maps.**  For a point `x` of an
open `U` the morphism of extensions

`Generators.self A(U) B(U) ⟶ Generators.self Aₓ Bₓ`

attached to the commuting square of germ maps.  Its underlying map of polynomial rings is
`Stacks.SheafOfModules.germPolynomialHom`. -/
def germSelfHom :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    (Algebra.Generators.self (ToType (A.obj.obj (op U)))
        (ToType (B.obj.obj (op U)))).toExtension.Hom
      (Algebra.Generators.self (ToType (stalk A.obj x))
        (ToType (stalk B.obj x))).toExtension := by
  letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  letI := algebraGerm A x U hx
  letI := algebraGerm B x U hx
  exact Stacks.NaiveCotangentAffineComparison.selfSquareHom
    fun r => (stalkFunctor_map_germ_apply U x hx a.hom r).symm

/-- The underlying map of polynomial rings of
`Stacks.SheafOfModules.germSelfHom` is the polynomial map induced by the germ maps. -/
theorem germSelfHom_toRingHom :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    (germSelfHom A B a x U hx).toRingHom = germPolynomialHom A B x U hx := rfl

/-! ### The germ of the comparison on sections in degree `-1` -/

/-- **The germ of the degree `-1` comparison is the degree `-1` comparison of stalks.**  Under the
identification of the stalk at `x` of the degree `-1` term of `NL_{B/A}` with the conormal module
of the canonical presentation of `Bₓ` over `Aₓ` (Stacks 0D09), the germ at `x` of the degree `-1`
component of the comparison on sections over `U` is the conormal map of the morphism of extensions
given by the germ maps. -/
theorem naiveCotangentStalkCotangentEquiv_germ_sectionsConormalComparison :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    letI := algebraGermComp A B a x U hx
    haveI := isScalarTower_germ A B a x U hx
    ∀ c : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
      (ToType (B.obj.obj (op U)))).toExtension.Cotangent,
      naiveCotangentStalkCotangentEquiv A B a x
          (moduleGerm _ x U hx
            (sectionsConormalComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a
              (op U) c)) =
        Algebra.Extension.Cotangent.map (germSelfHom A B a x U hx) c := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := algebraGerm A x U hx
  let := algebraGerm B x U hx
  let := algebraGermComp A B a x U hx
  have _ := isScalarTower_germ A B a x U hx
  intro c
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
  have h1 := conormalSheafStalkLinearEquiv_germ_conormalClass
      (freeAlgebraSheaf (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x A
      (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
        (underlyingPresheaf (Opens.grothendieckTopology X) B)) U hx
      ⟨freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) g.1,
        ker_le_comap_freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B a (op U) g.2⟩
  rw [sectionsConormalComparison_mk.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U) g,
    naiveCotangentStalkCotangentEquiv_apply]
  refine Eq.trans (congrArg (Algebra.Extension.Cotangent.map
    (canonicalStalkExtensionHom A B a x)) h1) ?_
  refine Eq.trans (Algebra.Extension.Cotangent.map_mk
    (canonicalStalkExtensionHom A B a x) _) ?_
  refine Eq.symm (Eq.trans (Algebra.Extension.Cotangent.map_mk
    (germSelfHom A B a x U hx) g) ?_)
  exact congrArg Algebra.Extension.Cotangent.mk (Subtype.ext
    (canonicalStalkRingEquiv_germ_freeAlgebraSectionsMap A B x U hx g.1).symm)

/-! ### The structural map of the canonical presentation on sections -/

/-- **The lax comparison followed by the presentation is the structural map.**  For a polynomial
`q` over `A(U)` in the sections of `B`, the image of `λ(q)` under the presentation `A[B] ⟶ B` on
sections is the image of `q` under the structural map of the canonical presentation of `B(U)`
over `A(U)`.  This is `Stacks.SheafOfModules.freeAlgebraSectionsMap_presentation` read through
`Algebra.Generators.algebraMap_apply`. -/
theorem presentation_freeAlgebraSectionsMap :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    ∀ q : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
      (ToType (B.obj.obj (op U)))).toExtension.Ring,
      ((presentation (Opens.grothendieckTopology X) A B a
            (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom.app (op U)).hom
          (freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) q) =
        algebraMap ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
            (ToType (B.obj.obj (op U)))).toExtension.Ring) (ToType (B.obj.obj (op U))) q := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  intro q
  refine Eq.trans (freeAlgebraSectionsMap_presentation (Opens.grothendieckTopology X) A B a
    (op U) q) ?_
  exact Eq.trans (MvPolynomial.aeval_def _ q).symm
    (Algebra.Generators.algebraMap_apply (Algebra.Generators.self
      (ToType (A.obj.obj (op U))) (ToType (B.obj.obj (op U)))) q).symm

/-- **A scalar is absorbed into the left factor of a pure tensor.**  The image under the unit of
sheafification of `[s] ⊗ ω`, for `s` a section of the source of a presentation, is the image of
`s` under the presentation acting on the image of `1 ⊗ ω`. -/
theorem toAssociatedModule_quotient_mk_tmul {X : TopCat.{u}}
    (R A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (a : R ⟶ A) (φ : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ.hom] (Y : (Opens X)ᵒᵖ)
    (s : A.obj.obj Y) (ω : (differentialsPresheaf a.hom).obj Y) :
    toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A B φ
        (tensorPresheaf φ.hom a.hom) Y
        ((Ideal.Quotient.mk (kernelIdeal φ.hom Y) s) ⊗ₜ[A.obj.obj Y] ω) =
      (φ.hom.app Y).hom s •
        toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A B φ
          (tensorPresheaf φ.hom a.hom) Y
          ((1 : A.obj.obj Y ⧸ kernelIdeal φ.hom Y) ⊗ₜ[A.obj.obj Y] ω) := by
  have e1 : s • (1 : A.obj.obj Y ⧸ kernelIdeal φ.hom Y) =
      Ideal.Quotient.mk (kernelIdeal φ.hom Y) s := by
    rw [Algebra.smul_def, mul_one]
    rfl
  refine Eq.trans (congrArg (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A B φ
      (tensorPresheaf φ.hom a.hom) Y) ?_)
    (toAssociatedModule_smul.{u, u, u, u} (Opens.grothendieckTopology X) A B φ
      (tensorPresheaf φ.hom a.hom) Y (Ideal.Quotient.mk (kernelIdeal φ.hom Y) s)
      ((1 : A.obj.obj Y ⧸ kernelIdeal φ.hom Y) ⊗ₜ[A.obj.obj Y] ω))
  refine Eq.trans (congrArg (fun z : A.obj.obj Y ⧸ kernelIdeal φ.hom Y =>
    z ⊗ₜ[A.obj.obj Y] ω) e1.symm) ?_
  exact (TensorProduct.smul_tmul' s (1 : A.obj.obj Y ⧸ kernelIdeal φ.hom Y) ω).symm

/-! ### The germ of the comparison on sections in degree `0` -/

/-- **The germ of the degree `0` comparison is the degree `0` comparison of stalks, on the
universal differentials.**  Under the identification of the stalk at `x` of the degree `0` term of
`NL_{B/A}` with the cotangent space of the canonical presentation of `Bₓ` over `Aₓ`
(Stacks 0D09), the germ at `x` of the degree `0` component of the comparison on sections over `U`
agrees with the cotangent-space map of the morphism of extensions given by the germ maps, on the
elements `1 ⊗ d p`. -/
theorem naiveCotangentStalkCotangentSpaceEquiv_germ_sectionsTensorComparison_one_tmul :
    letI := algebraSections (Opens.grothendieckTopology X) A B a (op U)
    letI := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
    letI := algebraGerm A x U hx
    letI := algebraGerm B x U hx
    letI := algebraGermComp A B a x U hx
    haveI := isScalarTower_germ A B a x U hx
    letI : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
    ∀ p : (Algebra.Generators.self (ToType (A.obj.obj (op U)))
      (ToType (B.obj.obj (op U)))).toExtension.Ring,
      naiveCotangentStalkCotangentSpaceEquiv A B a x
          (moduleGerm _ x U hx
            (sectionsTensorComparison.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U)
              ((1 : ToType (B.obj.obj (op U)))
                ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                    (ToType (B.obj.obj (op U)))).toExtension.Ring]
                  KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                    ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                      (ToType (B.obj.obj (op U)))).toExtension.Ring) p))) =
        Algebra.Extension.CotangentSpace.map (germSelfHom A B a x U hx)
          ((1 : ToType (B.obj.obj (op U)))
            ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj (op U)))
                (ToType (B.obj.obj (op U)))).toExtension.Ring]
              KaehlerDifferential.D (ToType (A.obj.obj (op U)))
                ((Algebra.Generators.self (ToType (A.obj.obj (op U)))
                  (ToType (B.obj.obj (op U)))).toExtension.Ring) p) := by
  let := algebraSections (Opens.grothendieckTopology X) A B a (op U)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a.hom x
  let := algebraGerm A x U hx
  let := algebraGerm B x U hx
  let := algebraGermComp A B a x U hx
  have _ := isScalarTower_germ A B a x U hx
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds x)) := Classical.decEq _
  intro p
  have h := cotangentSpaceStalkLinearEquiv_germ_tmul_d A
    (freeAlgebraSheaf (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B)) B
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X) A
      (underlyingPresheaf (Opens.grothendieckTopology X) B))
    (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)) x U hx 1
    (freeAlgebraSectionsMap (Opens.grothendieckTopology X) A B (op U) p)
  rw [sectionsTensorComparison_tmul.{u, u, u, u} (Opens.grothendieckTopology X) A B a (op U) 1 p,
    one_smul, naiveCotangentStalkCotangentSpaceEquiv_apply]
  refine Eq.trans (congrArg (Algebra.Extension.CotangentSpace.map
    (canonicalStalkExtensionHom A B a x)) h) ?_
  refine Eq.trans (Algebra.Extension.CotangentSpace.map_tmul
    (canonicalStalkExtensionHom A B a x) _ _) ?_
  refine Eq.trans ?_ (Algebra.Extension.CotangentSpace.map_tmul
    (germSelfHom A B a x U hx) 1 p).symm
  refine congrArg₂ (fun (bb : ToType (stalk B.obj x))
      (q : (Algebra.Generators.self (ToType (stalk A.obj x))
        (ToType (stalk B.obj x))).toExtension.Ring) =>
      bb ⊗ₜ[(Algebra.Generators.self (ToType (stalk A.obj x))
          (ToType (stalk B.obj x))).toExtension.Ring]
        KaehlerDifferential.D (ToType (stalk A.obj x))
          ((Algebra.Generators.self (ToType (stalk A.obj x))
            (ToType (stalk B.obj x))).toExtension.Ring) q) ?_ ?_
  · simp only [Algebra.algebraMap_self_apply, map_one]
    refine Eq.trans (congrArg (stalkQuotientLinearEquiv
      (presentation (Opens.grothendieckTopology X) A B a
        (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom x)
      (map_one (Ideal.quotientMap
        (stalkKernelIdeal (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom x)
        (germ (freeAlgebraSheaf (Opens.grothendieckTopology X) A
          (underlyingPresheaf (Opens.grothendieckTopology X) B)).obj U x hx).hom
        (kernelIdeal_le_comap_germ (presentation (Opens.grothendieckTopology X) A B a
          (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom x U hx)))) ?_
    exact map_one (stalkQuotientRingEquiv (presentation (Opens.grothendieckTopology X) A B a
      (underlyingPresheaf (Opens.grothendieckTopology X) B) (𝟙 _)).hom x)
  · exact canonicalStalkRingEquiv_germ_freeAlgebraSectionsMap A B x U hx p

end Stacks.SheafOfModules

end

end
