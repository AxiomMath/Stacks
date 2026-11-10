module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalIdealRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraBaseChangeSurjective
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraConormalBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentPresentationComparison
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveExtComparison
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism

/-!
# The obstruction class of two solutions of a square-zero extension problem of ringed topoi

Let `S` be the square-zero extension problem of [Stacks Project, Tag 08UF]: a morphism of ringed
topoi `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, a first order thickening `𝒪_{ℬ'} ⟶ 𝒪_ℬ` of the base with
ideal `𝒥`, an `𝒪`-module `G` and a map `c : f⁻¹𝒥 ⟶ G`. Write `A = f⁻¹𝒪_ℬ` and `A' = f⁻¹𝒪_{ℬ'}`.
Given two solutions `𝒪'₁`, `𝒪'₂`, Step 1 of the proof of [Stacks Project, Tag 08UG], as used in
[Stacks Project, Tag 08UK], attaches to them a class `o(𝒪'₁, 𝒪'₂) ∈ Ext¹_𝒪(NL_{𝒪/A}, G)`:

* take a family of generators `ℰ` with maps `β₁ : ℰ ⟶ 𝒪'₁` and `β₂ : ℰ ⟶ 𝒪'₂` over the same
  `α : ℰ ⟶ 𝒪`, such that `A[ℰ] ⟶ 𝒪` is surjective (a `PairDatum`); the canonical one is the
  sheaf of sets underlying `𝒪'₁ ×_𝒪 𝒪'₂`;
* the two `A'`-algebra maps `φᵢ : A'[ℰ] ⟶ 𝒪'ᵢ` sending the variables to `βᵢ` agree after
  reduction, so on the kernel `ℐ'` of `A'[ℰ] ⟶ 𝒪` their difference `φ₂ − φ₁` is a map
  `ℐ' ⟶ G`; it kills the kernel of `A'[ℰ] ⟶ A[ℰ]`, hence descends along the surjection
  `ℐ' ⟶ ℐ` onto the kernel `ℐ` of `A[ℰ] ⟶ 𝒪`, and then to the conormal sheaf, giving
  `D̄₁₂ : ℐ/ℐ² ⟶ G`;
* the class of `D̄₁₂` in `Ext¹_𝒪(NL(α), G)` is transported to `Ext¹_𝒪(NL_{𝒪/A}, G)` along the
  isomorphism `NL(α) ≅ NL_{𝒪/A}` of [Stacks Project, Tag 08TY].

The class does not depend on the family of generators: every pair datum maps to the canonical
one, and the class is natural under morphisms of pair data.

## Main definitions

* `...CompatibleFirstOrderThickening.PairDatum`: a family of generators for a pair of solutions.
* `...PairDatum.difference`: the difference `φ₂ − φ₁` on `ℐ'`, as a restriction datum.
* `...PairDatum.conormalMap`: the difference map `D̄₁₂ : ℐ/ℐ² ⟶ G`.
* `...PairDatum.extClass` and `...PairDatum.obstruction`: its class in `Ext¹_𝒪(NL(α), G)` and the
  transported class in `Ext¹_𝒪(NL_{𝒪/A}, G)`.
* `...CompatibleFirstOrderThickening.pairDatum`: the canonical pair datum `𝒪'₁ ×_𝒪 𝒪'₂`.
* `...CompatibleFirstOrderThickening.pairDatumObstruction` and
  `...CompatibleFirstOrderThickening.pairObstruction`: the class `o(𝒪'₁, 𝒪'₂)`, the latter in
  `S.f.naiveCotangentExt (targetG S) 1`.
* `Stacks.Sites.Conormal.IdealRestriction.descend`: a restriction datum for `ψ ≫ φ` killing
  `Ker ψ` descends to one for `φ` when `ψ` is locally surjective.

## Main results

* `...PairDatum.conormalMap_conormalClass`: `D̄₁₂` sends the conormal class of the image of a
  local section `p` of `ℐ'` to `φ₂(p) − φ₁(p)`, read in `G`.
* `...PairDatum.difference_eq_zero_of_baseChange`: the difference kills the kernel of
  `A'[ℰ] ⟶ A[ℰ]`; this rests on
  `...CompatibleFirstOrderThickening.desc_polynomialUnit_eq_incl`, which says that a polynomial
  with coefficients in `f⁻¹𝒥` has the same image in `G` under both solutions.
* `...PairDatum.Hom.presentationConormalMap_comp_conormalMap`,
  `...PairDatum.Hom.Q_map_comp_extClass` and `...PairDatum.Hom.obstruction_eq`: naturality of
  `D̄₁₂`, of its class, and invariance of the transported class under morphisms of pair data.
* `...PairDatum.obstruction_eq_pairDatumObstruction` and
  `...PairDatum.obstruction_eq_pairObstruction`: every pair datum gives `o(𝒪'₁, 𝒪'₂)`.
* `Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_comp_conormalExtClass`: the first
  Ext class of a conormal homomorphism is natural in the presentation.

## Implementation notes

The kernel of `A'[ℰ] ⟶ A[ℰ]` is not computed as a sheaf of ideals. What is used is that a local
section killed by it is, locally, a polynomial whose coefficients lie in `f⁻¹𝒥`
(`Stacks.Sites.FreeAlgebra.exists_covering_polynomial_of_baseChange_eq_zero`), and on such a
polynomial both solutions take the same value: a coefficient goes to its image under `c`, and
a monomial in the generators acts on `G` through its reduction, which is the same monomial in
`α` for both solutions. The descent to `ℐ` is done section by section, gluing the values on
local lifts in the sheaf `G`.

**Universes.** Everything is stated for `X : RingedTopos.{v, u, max u v w}`, with the conormal
sheaves and the naive cotangent complex at the module universe `max u v w` written with the
auxiliary universe `w`, which is the spelling `Stacks.SheafOfModules.presentationConormalExtClass`
uses. `AlgebraicGeometry.RingedToposHom.naiveCotangentExt` writes the same module universe with
the auxiliary universe `u`; the two spellings of `NL_{𝒪/A}` are isomorphic but not equal, so
`pairObstruction` is stated for `X : RingedTopos.{v, u, max u v}`, where they coincide, and
`pairDatumObstruction` is the class in full generality.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u w v' u' w' z

/-! ### Changing the coefficients of a free algebra sheaf -/

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ : Sheaf J CommRingCat.{w}} (r : A₁ ⟶ A₂) (E : Functor Cᵒᵖ (Type w))

/-- Changing the coefficients of polynomials commutes with the restriction maps of the presheaf
of polynomial rings. -/
theorem polynomialPresheaf_map_comp_map {U V : Cᵒᵖ} (g : U ⟶ V) :
    (polynomialPresheaf J A₁ E).map g ≫ CommRingCat.ofHom (MvPolynomial.map (r.hom.app V).hom) =
      CommRingCat.ofHom (MvPolynomial.map (r.hom.app U).hom) ≫
        (polynomialPresheaf J A₂ E).map g := by
  dsimp only [polynomialPresheaf]
  ext a <;> simp [NatTrans.naturality_apply r.hom g]

/-- `Stacks.Sites.FreeAlgebra.polynomialPresheaf_map_comp_map` on a section. -/
theorem map_polynomialPresheaf_map {U V : Cᵒᵖ} (g : U ⟶ V)
    (p : (polynomialPresheaf J A₁ E).obj U) :
    MvPolynomial.map (r.hom.app V).hom ((polynomialPresheaf J A₁ E).map g p) =
      (polynomialPresheaf J A₂ E).map g (MvPolynomial.map (r.hom.app U).hom p) :=
  ConcreteCategory.congr_hom (polynomialPresheaf_map_comp_map J r E g) p

variable [HasWeakSheafify J CommRingCat.{w}]

/-- On the image of the polynomial model, changing the coefficients of the free algebra sheaf is
changing the coefficients of the polynomials. -/
theorem polynomialUnit_comp_baseChange (U : Cᵒᵖ) :
    (polynomialUnit J A₁ E).app U ≫ (baseChange J r E).hom.app U =
      CommRingCat.ofHom (MvPolynomial.map (r.hom.app U).hom) ≫
        (polynomialUnit J A₂ E).app U := by
  refine (NatTrans.congr_app (polynomialUnit_comp_desc J A₁
    (freeAlgebraSheaf J A₂ E) E (r ≫ freeAlgebraSheafCoefficientMap J A₂ E)
    (freeAlgebraSheafVariable J A₂ E)) U).trans ?_
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    refine (polynomialEvaluation_app_C J A₁ E _ _ _ U a).trans ?_
    change (polynomialUnit J A₂ E).app U (MvPolynomial.C (r.hom.app U a)) =
      (polynomialUnit J A₂ E).app U (MvPolynomial.map (r.hom.app U).hom (MvPolynomial.C a))
    rw [MvPolynomial.map_C]
  · intro x
    refine (polynomialEvaluation_app_X J A₁ E _ _ _ U x).trans ?_
    change (polynomialUnit J A₂ E).app U (MvPolynomial.X x) =
      (polynomialUnit J A₂ E).app U (MvPolynomial.map (r.hom.app U).hom (MvPolynomial.X x))
    rw [MvPolynomial.map_X]

/-- `Stacks.Sites.FreeAlgebra.polynomialUnit_comp_baseChange` on a section. -/
theorem baseChange_app_polynomialUnit (U : Cᵒᵖ) (p : (polynomialPresheaf J A₁ E).obj U) :
    (baseChange J r E).hom.app U ((polynomialUnit J A₁ E).app U p) =
      (polynomialUnit J A₂ E).app U (MvPolynomial.map (r.hom.app U).hom p) :=
  ConcreteCategory.congr_hom (polynomialUnit_comp_baseChange J r E U) p

/-- Renaming the variables along `h : E₁ ⟶ E₂` and then classifying `(a, e)` classifies
`(a, h ≫ e)`. -/
theorem freeAlgebraMap_comp_desc (A T : Sheaf J CommRingCat.{w}) {E₁ E₂ : Functor Cᵒᵖ (Type w)}
    (h : E₁ ⟶ E₂) (a : A ⟶ T) (e : E₂ ⟶ underlyingPresheaf J T) :
    Stacks.SheafOfModules.freeAlgebraMap J A E₁ E₂ h ≫ freeAlgebraSheafDesc J A T E₂ a e =
      freeAlgebraSheafDesc J A T E₁ a (h ≫ e) := by
  refine freeAlgebraSheaf_hom_ext J A T E₁ ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_desc,
      freeAlgebraSheafCoefficientMap_comp_desc, freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc, Category.assoc, freeAlgebraSheafVariable_comp_desc,
      freeAlgebraSheafVariable_comp_desc]

/-- Renaming the variables commutes with changing the coefficients. -/
theorem freeAlgebraMap_comp_baseChange {E₁ E₂ : Functor Cᵒᵖ (Type w)} (h : E₁ ⟶ E₂) :
    Stacks.SheafOfModules.freeAlgebraMap J A₁ E₁ E₂ h ≫ baseChange J r E₂ =
      baseChange J r E₁ ≫ Stacks.SheafOfModules.freeAlgebraMap J A₂ E₁ E₂ h := by
  rw [baseChange, freeAlgebraMap_comp_desc, baseChange]
  refine freeAlgebraSheaf_hom_ext J A₁ _ E₁ ?_ ?_
  · rw [freeAlgebraSheafCoefficientMap_comp_desc, ← Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc, Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [freeAlgebraSheafVariable_comp_desc, Functor.map_comp, Functor.whiskerRight_comp,
      ← Category.assoc, freeAlgebraSheafVariable_comp_desc, freeAlgebraSheafVariable_comp_desc]

variable [J.WEqualsLocallyBijective CommRingCat.{w}]

/-- **A local section killed by a change of coefficients is locally a polynomial with
coefficients in the kernel.** -/
theorem exists_covering_polynomial_of_baseChange_eq_zero {X : C}
    (k : (freeAlgebraSheaf J A₁ E).obj.obj (op X))
    (hk : (baseChange J r E).hom.app (op X) k = 0) :
    ∃ T : Sieve X, T ∈ J X ∧ ∀ (Z : C) (g : Z ⟶ X), T g →
      ∃ q : (polynomialPresheaf J A₁ E).obj (op Z),
        MvPolynomial.map (r.hom.app (op Z)).hom q = 0 ∧
          (polynomialUnit J A₁ E).app (op Z) q = (freeAlgebraSheaf J A₁ E).obj.map g.op k := by
  let T : Sieve X :=
    { arrows Z g := ∃ q : (polynomialPresheaf J A₁ E).obj (op Z),
        MvPolynomial.map (r.hom.app (op Z)).hom q = 0 ∧
          (polynomialUnit J A₁ E).app (op Z) q = (freeAlgebraSheaf J A₁ E).obj.map g.op k
      downward_closed := by
        rintro Z W g ⟨q, hq, hqk⟩ h
        refine ⟨(polynomialPresheaf J A₁ E).map h.op q, ?_, ?_⟩
        · rw [map_polynomialPresheaf_map, hq]
          exact map_zero _
        · rw [NatTrans.naturality_apply, hqk, op_comp, Functor.map_comp_apply] }
  refine ⟨T, J.transitive (Presheaf.imageSieve_mem J (polynomialUnit J A₁ E) k) _ ?_,
    fun _ _ h ↦ h⟩
  rintro Y f ⟨p, hp⟩
  have hzero : (polynomialUnit J A₂ E).app (op Y) (MvPolynomial.map (r.hom.app (op Y)).hom p) =
      (polynomialUnit J A₂ E).app (op Y) 0 := by
    rw [← baseChange_app_polynomialUnit, hp, NatTrans.naturality_apply, hk, map_zero, map_zero]
  refine J.superset_covering ?_
    (Presheaf.equalizerSieve_mem J (polynomialUnit J A₂ E) _ _ hzero)
  intro Z g hg
  refine ⟨(polynomialPresheaf J A₁ E).map g.op p, ?_, ?_⟩
  · rw [map_polynomialPresheaf_map]
    exact hg.trans (map_zero _)
  · rw [NatTrans.naturality_apply, hp, op_comp, Functor.map_comp_apply]

end Stacks.Sites.FreeAlgebra

/-! ### Descending a restriction datum along a locally surjective change of presentation -/

namespace Stacks.Sites.Conormal.IdealRestriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ B : Sheaf J CommRingCat.{w}} {ψ : A₁ ⟶ A₂} {φ : A₂ ⟶ B}
  {G : SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)}
  (ρ : IdealRestriction (ψ ≫ φ) G)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A local section of `A₁` lying over a local section of `Ker φ` lies in `Ker (ψ ≫ φ)`. -/
theorem mem_kernelIdeal_comp {U : Cᵒᵖ} (k : A₁.obj.obj U)
    (hk : ψ.hom.app U k ∈ kernelIdeal φ.hom U) : k ∈ kernelIdeal (ψ ≫ φ).hom U :=
  hk

variable (hρ : ∀ (U : Cᵒᵖ) (k : kernelIdeal (ψ ≫ φ).hom U), ψ.hom.app U k = 0 → ρ.app U k = 0)

include hρ in
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A restriction datum killing `Ker ψ` takes the same value on two local sections with the same
image under `ψ`. -/
theorem app_congr_of_kernel {U : Cᵒᵖ} (k k' : kernelIdeal (ψ ≫ φ).hom U)
    (h : ψ.hom.app U k = ψ.hom.app U k') : ρ.app U k = ρ.app U k' := by
  have h0 : ρ.app U (k - k') = 0 := hρ U _ (by
    change ψ.hom.app U ((k : A₁.obj.obj U) - k') = 0
    rw [map_sub, h, sub_self])
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

/-- The sheaf of sets underlying `G`. -/
noncomputable abbrev typeSheaf : Sheaf J (Type (max w u v z)) :=
  (sheafCompose J (forget AddCommGrpCat.{max w u v z})).obj ((SheafOfModules.toSheaf _).obj G)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sheaf of sets underlying `G` satisfies the sheaf condition for every covering sieve. -/
theorem isSheaf_typeSheaf : Presieve.IsSheaf J (typeSheaf (G := G)).obj :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (typeSheaf (G := G)).property

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A local lift through `ψ` of a restriction of a local section of `Ker φ` lies in
`Ker (ψ ≫ φ)`. -/
theorem lift_mem_kernelIdeal {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) {Y : C} (f : Y ⟶ U.unop)
    (k : A₁.obj.obj (op Y)) (hk : ψ.hom.app (op Y) k = A₂.obj.map f.op p) :
    k ∈ kernelIdeal (ψ ≫ φ).hom (op Y) := by
  exact mem_kernelIdeal_comp k (by rw [hk]; exact map_kernel φ.hom f.op p.2)

variable [Presheaf.IsLocallySurjective J ψ.hom]

/-- The values of `ρ` on chosen local lifts through `ψ` of a local section of `Ker φ`. -/
noncomputable def descendFamily {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) :
    Presieve.FamilyOfElements (typeSheaf (G := G)).obj
      (Presheaf.imageSieve ψ.hom (U := U.unop) (p : A₂.obj.obj U)).arrows :=
  fun Y f hf ↦ ρ.app (op Y) ⟨hf.choose, lift_mem_kernelIdeal p f _ hf.choose_spec⟩

include hρ in
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [Presheaf.IsLocallySurjective J ψ.hom] in
/-- The values of `ρ` on local lifts of a local section of `Ker φ` glue. -/
theorem descendFamily_compatible {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) :
    (descendFamily ρ p).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  change G.val.map g₁.op (ρ.app _ _) = G.val.map g₂.op (ρ.app _ _)
  rw [← ρ.app_map, ← ρ.app_map]
  apply app_congr_of_kernel ρ hρ
  change ψ.hom.app _ (A₁.obj.map g₁.op h₁.choose) = ψ.hom.app _ (A₁.obj.map g₂.op h₂.choose)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h₁.choose_spec, h₂.choose_spec,
    ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]

/-- The value of the descended restriction datum on a local section `p` of `Ker φ`: the gluing
of the values of `ρ` on local lifts of `p` through `ψ`. -/
noncomputable def descendApp {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) : G.val.obj U :=
  (isSheaf_typeSheaf (G := G) _ (Presheaf.imageSieve_mem J ψ.hom (p : A₂.obj.obj U))).amalgamate
    (descendFamily ρ p) (descendFamily_compatible ρ hρ p)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The restriction of the descended value along an arrow over which `p` lifts is the value of
`ρ` on the lift. -/
theorem map_descendApp {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) {Y : C} (f : Y ⟶ U.unop)
    (k : kernelIdeal (ψ ≫ φ).hom (op Y)) (hk : ψ.hom.app (op Y) k = A₂.obj.map f.op p) :
    G.val.map f.op (descendApp ρ hρ p) = ρ.app (op Y) k := by
  have hf : Presheaf.imageSieve ψ.hom (U := U.unop) (p : A₂.obj.obj U) f := ⟨k, hk⟩
  refine ((isSheaf_typeSheaf (G := G) _ (Presheaf.imageSieve_mem J ψ.hom
    (p : A₂.obj.obj U))).valid_glue (descendFamily_compatible ρ hρ p) f hf).trans ?_
  exact app_congr_of_kernel ρ hρ _ _ (hf.choose_spec.trans hk.symm)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descended value is characterised by its restrictions to a covering sieve over which `p`
lifts. -/
theorem descendApp_eq {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) (y : G.val.obj U) (T : Sieve U.unop)
    (hT : T ∈ J U.unop)
    (h : ∀ (Y : C) (f : Y ⟶ U.unop), T f → ∃ k : kernelIdeal (ψ ≫ φ).hom (op Y),
      ψ.hom.app (op Y) k = A₂.obj.map f.op p ∧ G.val.map f.op y = ρ.app (op Y) k) :
    descendApp ρ hρ p = y :=
  (isSheaf_typeSheaf (G := G) _ hT).isSeparatedFor.ext fun Y f hf ↦ by
    obtain ⟨k, hk, hy⟩ := h Y f hf
    exact (map_descendApp ρ hρ p f k hk).trans hy.symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- On the image of a local section of `Ker (ψ ≫ φ)` the descended value is the value of
`ρ`. -/
theorem descendApp_mk {U : Cᵒᵖ} (k : kernelIdeal (ψ ≫ φ).hom U)
    (hk : ψ.hom.app U k ∈ kernelIdeal φ.hom U) :
    descendApp ρ hρ ⟨ψ.hom.app U k, hk⟩ = ρ.app U k := by
  refine descendApp_eq ρ hρ _ _ ⊤ (J.top_mem _) fun Y f _ ↦
    ⟨⟨A₁.obj.map f.op k, map_kernel _ f.op k.2⟩, ?_, (ρ.app_map f.op k).symm⟩
  exact NatTrans.naturality_apply ψ.hom f.op (k : A₁.obj.obj U)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descended values commute with the restriction maps. -/
theorem descendApp_map {U V : Cᵒᵖ} (g : U ⟶ V) (p : kernelIdeal φ.hom U) :
    descendApp ρ hρ ⟨A₂.obj.map g p, map_kernel φ.hom g p.2⟩ =
      G.val.map g (descendApp ρ hρ p) := by
  refine descendApp_eq ρ hρ _ _
    ((Presheaf.imageSieve ψ.hom (U := U.unop) (p : A₂.obj.obj U)).pullback g.unop)
    (J.pullback_stable _ (Presheaf.imageSieve_mem J ψ.hom _)) fun Y f hf ↦ ?_
  obtain ⟨k, hk⟩ := hf
  refine ⟨⟨k, lift_mem_kernelIdeal p (f ≫ g.unop) k hk⟩, ?_, ?_⟩
  · refine hk.trans ?_
    rw [op_comp, Functor.map_comp_apply]
    rfl
  · refine Eq.trans ?_ (map_descendApp ρ hρ p (f ≫ g.unop) _ hk)
    exact (((typeSheaf (G := G)).obj).map_comp_apply g f.op _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descended values are additive. -/
theorem descendApp_add {U : Cᵒᵖ} (p p' : kernelIdeal φ.hom U) :
    descendApp ρ hρ (p + p') = descendApp ρ hρ p + descendApp ρ hρ p' := by
  refine descendApp_eq ρ hρ _ _
    (Presheaf.imageSieve ψ.hom (U := U.unop) (p : A₂.obj.obj U) ⊓
      Presheaf.imageSieve ψ.hom (U := U.unop) (p' : A₂.obj.obj U))
    (J.intersection_covering (Presheaf.imageSieve_mem J ψ.hom _)
      (Presheaf.imageSieve_mem J ψ.hom _)) fun Y f hf ↦ ?_
  obtain ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩ := hf
  let K : kernelIdeal (ψ ≫ φ).hom (op Y) := ⟨k, lift_mem_kernelIdeal p f k hk⟩
  let K' : kernelIdeal (ψ ≫ φ).hom (op Y) := ⟨k', lift_mem_kernelIdeal p' f k' hk'⟩
  refine ⟨K + K', ?_, ?_⟩
  · change ψ.hom.app (op Y) (k + k') = A₂.obj.map f.op ((p : A₂.obj.obj U) + p')
    rw [map_add, hk, hk', map_add]
  · rw [map_add, map_add, map_descendApp ρ hρ p f K hk, map_descendApp ρ hρ p' f K' hk']
    rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descended values are linear over `A₂` acting through `φ`. -/
theorem descendApp_smul {U : Cᵒᵖ} (a : A₂.obj.obj U) (p : kernelIdeal φ.hom U) :
    descendApp ρ hρ (a • p) = presentationScalar φ U a • descendApp ρ hρ p := by
  refine descendApp_eq ρ hρ _ _
    (Presheaf.imageSieve ψ.hom (U := U.unop) a ⊓
      Presheaf.imageSieve ψ.hom (U := U.unop) (p : A₂.obj.obj U))
    (J.intersection_covering (Presheaf.imageSieve_mem J ψ.hom _)
      (Presheaf.imageSieve_mem J ψ.hom _)) fun Y f hf ↦ ?_
  obtain ⟨⟨s, hs⟩, ⟨k, hk⟩⟩ := hf
  let K : kernelIdeal (ψ ≫ φ).hom (op Y) := ⟨k, lift_mem_kernelIdeal p f k hk⟩
  refine ⟨s • K, ?_, ?_⟩
  · change ψ.hom.app (op Y) (s * k) = A₂.obj.map f.op (a * (p : A₂.obj.obj U))
    rw [map_mul, hs, hk, map_mul]
  · rw [PresheafOfModules.map_smul, map_descendApp ρ hρ p f K hk, ρ.app_smul]
    congr 1
    change B.obj.map f.op (φ.hom.app U a) = φ.hom.app (op Y) (ψ.hom.app (op Y) s)
    rw [hs]
    exact (NatTrans.naturality_apply φ.hom f.op a).symm

/-- **A restriction datum for `ψ ≫ φ` killing `Ker ψ` descends to a restriction datum for `φ`**,
when `ψ` is locally surjective: its value on a local section of `Ker φ` is glued from its values
on local lifts through `ψ`. -/
noncomputable def descend : IdealRestriction φ G where
  app _ := AddMonoidHom.mk' (descendApp ρ hρ) (descendApp_add ρ hρ)
  app_smul _ a p := descendApp_smul ρ hρ a p
  app_map g p := descendApp_map ρ hρ g p

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The descended restriction datum takes the value of `ρ` on the image of a local section of
`Ker (ψ ≫ φ)`. -/
theorem descend_app_mk {U : Cᵒᵖ} (k : kernelIdeal (ψ ≫ φ).hom U)
    (hk : ψ.hom.app U k ∈ kernelIdeal φ.hom U) :
    (descend ρ hρ).app U ⟨ψ.hom.app U k, hk⟩ = ρ.app U k :=
  descendApp_mk ρ hρ k hk

section Naturality

variable {A₁' A₂' : Sheaf J CommRingCat.{w}} {ψ' : A₁' ⟶ A₂'} {φ' : A₂' ⟶ B}
  [Presheaf.IsLocallySurjective J ψ'.hom]
  (ρ' : IdealRestriction (ψ' ≫ φ') G)
  (hρ' : ∀ (U : Cᵒᵖ) (k : kernelIdeal (ψ' ≫ φ').hom U), ψ'.hom.app U k = 0 → ρ'.app U k = 0)
  (Φ₁ : A₁ ⟶ A₁') (Φ₂ : A₂ ⟶ A₂') (hΦ : Φ₁ ≫ ψ' = ψ ≫ Φ₂) (hφ : Φ₂ ≫ φ' = φ)

include hΦ hφ in
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [Presheaf.IsLocallySurjective J ψ.hom]
  [Presheaf.IsLocallySurjective J ψ'.hom] in
/-- A local section of `Ker (ψ ≫ φ)` is carried by `Φ₁` into `Ker (ψ' ≫ φ')`. -/
theorem map_mem_kernelIdeal {U : Cᵒᵖ} (k : kernelIdeal (ψ ≫ φ).hom U) :
    Φ₁.hom.app U k ∈ kernelIdeal (ψ' ≫ φ').hom U := by
  exact Stacks.Sites.Conormal.kernelIdeal_le_comap _ _ Φ₁.hom
    (Stacks.Sites.Conormal.hom_of_comp_eq (by rw [← Category.assoc, hΦ, Category.assoc, hφ])) U k.2

include hφ in
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [Presheaf.IsLocallySurjective J ψ.hom]
  [Presheaf.IsLocallySurjective J ψ'.hom] in
/-- A local section of `Ker φ` is carried by `Φ₂` into `Ker φ'`. -/
theorem map_mem_kernelIdeal' {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) :
    Φ₂.hom.app U p ∈ kernelIdeal φ'.hom U := by
  exact Stacks.Sites.Conormal.kernelIdeal_le_comap _ _ Φ₂.hom
    (Stacks.Sites.Conormal.hom_of_comp_eq hφ) U p.2

include hρ hρ' in
omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Descent is natural.** If a commutative square of changes of presentation carries `ρ` to
`ρ'`, then the descended restriction data agree along it. -/
theorem descend_app_map
    (hρρ' : ∀ (U : Cᵒᵖ) (k : kernelIdeal (ψ ≫ φ).hom U),
      ρ'.app U ⟨Φ₁.hom.app U k, map_mem_kernelIdeal Φ₁ Φ₂ hΦ hφ k⟩ = ρ.app U k)
    {U : Cᵒᵖ} (p : kernelIdeal φ.hom U) :
    (descend ρ' hρ').app U ⟨Φ₂.hom.app U p, map_mem_kernelIdeal' Φ₂ hφ p⟩ =
      (descend ρ hρ).app U p := by
  refine descendApp_eq ρ' hρ' _ _ (Presheaf.imageSieve ψ.hom (U := U.unop) (p : A₂.obj.obj U))
    (Presheaf.imageSieve_mem J ψ.hom _) fun Y f hf ↦ ?_
  obtain ⟨k, hk⟩ := hf
  let K : kernelIdeal (ψ ≫ φ).hom (op Y) := ⟨k, lift_mem_kernelIdeal p f k hk⟩
  refine ⟨⟨Φ₁.hom.app (op Y) k, map_mem_kernelIdeal Φ₁ Φ₂ hΦ hφ K⟩, ?_, ?_⟩
  · change (Φ₁ ≫ ψ').hom.app (op Y) k = A₂'.obj.map f.op (Φ₂.hom.app U p)
    rw [hΦ]
    change Φ₂.hom.app (op Y) (ψ.hom.app (op Y) k) = _
    rw [hk]
    exact NatTrans.naturality_apply Φ₂.hom f.op (p : A₂.obj.obj U)
  · exact (map_descendApp ρ hρ p f K hk).trans (hρρ' (op Y) K).symm

end Naturality

end Stacks.Sites.Conormal.IdealRestriction

/-! ### Changing the presentation of a first Ext class of the naive cotangent complex -/

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{max w u v}]
  (A B : Sheaf J CommRingCat.{max w u v}) (a : A ⟶ B)
  (E₁ E₂ : Cᵒᵖ ⥤ Type (max w u v)) (h : E₁ ⟶ E₂)
  (α₁ : E₁ ⟶ underlyingPresheaf J B) (α₂ : E₂ ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  (hα : h ≫ α₂ = α₁)
  [HasSheafify J AddCommGrpCat.{max w u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  [HasDerivedCategory.{t} (_root_.SheafOfModules.{max w u v}
    (Stacks.SheafOfModules.Tensor.ringSheaf B))]
  (G : _root_.SheafOfModules.{max w u v} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- **The first Ext class of a conormal homomorphism is natural in the presentation.** Pulling
the class of `f : K₂/K₂² ⟶ G` back along the chain map `NL(α₁) ⟶ NL(α₂)` of a morphism of
presentations gives the class of `f` precomposed with the induced map `K₁/K₁² ⟶ K₂/K₂²`. -/
theorem presentationNaiveCotangentComplexMap_comp_conormalExtClass
    (f : (presentationConormalSequence.{v, u, max w u v, w} J A B a E₂ α₂).X₁ ⟶ G) :
    DerivedCategory.Q.map
        (presentationNaiveCotangentComplexMap.{v, u, max w u v, w} J A E₁ E₂ h B a α₁ α₂ hα) ≫
      presentationConormalExtClass.{v, u, w, t} J A B a E₂ α₂ G f =
    presentationConormalExtClass.{v, u, w, t} J A B a E₁ α₁ G
      (presentationConormalMap.{v, u, max w u v, w} J A E₁ E₂ h B a α₁ α₂ hα ≫ f) := by
  rw [presentationConormalExtClass, presentationConormalExtClass, ← Category.assoc,
    ← Functor.map_comp]
  refine congrArg (fun k ↦ DerivedCategory.Q.map k ≫
    ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app G) ?_
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.mkHomToSingle_f, presentationNaiveCotangentComplexMap_f_negOne]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end Stacks.SheafOfModules

/-! ### The difference of two solutions on a family of generators -/

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafCoefficientMap freeAlgebraSheafVariable baseChange polynomialUnit
  polynomialPresheaf polynomialEvaluation)
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal conormalDesc presentationScalar)

variable {X : RingedTopos.{v, u, max u v w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}

attribute [local instance] CategoryTheory.Sheaf.wEqualsLocallyBijective_commRingCat

variable (S) in
/-- The map `f⁻¹𝒪_{B'}[ℰ] ⟶ f⁻¹𝒪_B[ℰ]` changing the coefficients along the inverse image of the
base reduction is locally surjective. -/
instance isLocallySurjective_baseChange_inverseImage (E : X.Cᵒᵖ ⥤ Type (max u v w)) :
    Presheaf.IsLocallySurjective X.J
      (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) E).hom :=
  haveI : Presheaf.IsLocallySurjective X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom :=
    Stacks.Sheaves.ToposPushforward.isLocallySurjective_inverseImageCommRingFunctor_map
      S.f.toToposHom S.baseReduction S.baseLocallySurjective
  Stacks.Sites.FreeAlgebra.isLocallySurjective_baseChange X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) E

variable (S) in
/-- A local section of `f⁻¹𝒪_{B'}` killed by the inverse image of the base reduction is the image
of a unique local section of `f⁻¹J`; this is the chosen one. -/
noncomputable def idealPreimage {U : X.Cᵒᵖ}
    (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
    (ha : ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a = 0) :
    S.I.val.obj U :=
  (S.idealUniversal U a ha).exists.choose

variable (S) in
/-- The chosen local section of `f⁻¹J` maps to the given local section of `f⁻¹𝒪_{B'}`. -/
theorem idealInclusion_idealPreimage {U : X.Cᵒᵖ}
    (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
    (ha : ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a = 0) :
    (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
      S.idealInclusion.val.app U (idealPreimage S a ha)) = a :=
  (S.idealUniversal U a ha).exists.choose_spec

variable (S) in
/-- A polynomial killed by the inverse image of the base reduction has its coefficients in
`f⁻¹J`. -/
theorem coeff_eq_zero_of_map_eq_zero {E : X.Cᵒᵖ ⥤ Type (max u v w)} {Z : X.Cᵒᵖ}
    {q : MvPolynomial (E.obj Z)
      (((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj Z)}
    (hq : MvPolynomial.map
      (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app Z).hom q = 0)
    (m : E.obj Z →₀ ℕ) :
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app Z
      (q.coeff m) = 0 :=
  (MvPolynomial.coeff_map _ q m).symm.trans (congrArg (fun q ↦ q.coeff m) hq)

namespace CompatibleFirstOrderThickening

/-- The inclusion of `G` into a solution commutes with finite sums. -/
theorem incl_sum (Q : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ} {ι : Type*}
    (s : Finset ι) (g : ι → S.G.val.obj U) :
    Q.incl (∑ i ∈ s, g i) = ∑ i ∈ s, Q.incl (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Q.incl_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Q.incl_add, ih]

variable (S) in
/-- The section of `G` attached to a polynomial with coefficients in `f⁻¹J`, for a family of
generators `α : ℰ ⟶ 𝒪`: the sum over the monomials of the value of the monomial at `α` acting
on the image under `c` of the coefficient. -/
noncomputable def idealPolynomialSection {E : X.Cᵒᵖ ⥤ Type (max u v w)}
    (α : E ⟶ underlyingPresheaf X.J X.O) {Z : X.Cᵒᵖ}
    (q : MvPolynomial (E.obj Z)
      (((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj Z))
    (hq : MvPolynomial.map
      (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app Z).hom q = 0) :
    S.G.val.obj Z :=
  ∑ m ∈ q.support,
    (show ↥(((sheafCompose X.J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj
      X.O).obj.obj Z) from (∏ i ∈ m.support, (α.app Z i : X.O.obj.obj Z) ^ m i :
        X.O.obj.obj Z)) •
      (show S.G.val.obj Z from S.c.val.app Z
        (idealPreimage S (q.coeff m) (coeff_eq_zero_of_map_eq_zero S hq m)))

/-- The map from `f⁻¹𝒪_{B'}` of a solution sends a local section of `f⁻¹J` to the image under
`c` of its preimage, read in the thickened structure sheaf. -/
theorem baseMap_app_eq_incl (Q : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
    (ha : ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a = 0) :
    Q.baseMap.hom.app U a = Q.incl (S.c.val.app U (idealPreimage S a ha)) :=
  (congrArg (Q.baseMap.hom.app U) (idealInclusion_idealPreimage S a ha).symm).trans
    (Q.baseMap_ideal U _)

/-- **On a polynomial with coefficients in `f⁻¹J`, the map `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪'` of a solution
does not depend on the solution.** If `β : ℰ ⟶ 𝒪'` lies over `α : ℰ ⟶ 𝒪`, the image of such a
polynomial is the section `idealPolynomialSection S α q` of `G`: each coefficient goes to its
image under `c`, and a section of `G` is multiplied through the reduction, which sends the
monomial in `β` to the monomial in `α`. -/
theorem desc_polynomialUnit_eq_incl (Q : S.CompatibleFirstOrderThickening)
    {E : X.Cᵒᵖ ⥤ Type (max u v w)} (α : E ⟶ underlyingPresheaf X.J X.O)
    (β : E ⟶ underlyingPresheaf X.J Q.extension)
    (hβ : β ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{max u v w}) = α)
    {Z : X.Cᵒᵖ} (q : MvPolynomial (E.obj Z)
      (((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj Z))
    (hq : MvPolynomial.map
      (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app Z).hom q = 0) :
    (freeAlgebraSheafDesc X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
        Q.extension E Q.baseMap β).hom.app Z
        ((polynomialUnit X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
          E).app Z q) =
      Q.incl (idealPolynomialSection S α q hq) := by
  have hred : ∀ i, Q.reduction.hom.app Z (β.app Z i) = α.app Z i := fun i ↦
    ConcreteCategory.congr_hom (NatTrans.congr_app hβ Z) i
  refine (congrArg (fun k ↦ k.app Z q) (Stacks.Sites.FreeAlgebra.polynomialUnit_comp_desc X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) Q.extension E Q.baseMap
      β)).trans ?_
  change MvPolynomial.eval₂ (Q.baseMap.hom.app Z).hom (β.app Z) q = _
  refine (MvPolynomial.eval₂_eq _ _ q).trans ?_
  rw [idealPolynomialSection, incl_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have hprod : Q.reduction.hom.app Z (∏ i ∈ m.support, β.app Z i ^ m i) =
      ∏ i ∈ m.support, (α.app Z i : X.O.obj.obj Z) ^ m i := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [map_pow, hred]
  rw [baseMap_app_eq_incl Q _ (coeff_eq_zero_of_map_eq_zero S hq m), mul_comm]
  refine (Q.mul_incl _ _).trans ?_
  exact congrArg (fun s : ↥(((sheafCompose X.J
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj X.O).obj.obj Z) ↦
      Q.incl (s • (show S.G.val.obj Z from S.c.val.app Z
        (idealPreimage S (q.coeff m) (coeff_eq_zero_of_map_eq_zero S hq m))))) hprod

/-- The map `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪'` of a solution determined by `β : ℰ ⟶ 𝒪'`, followed by the
reduction, is the presentation `f⁻¹𝒪_{B'}[ℰ] ⟶ f⁻¹𝒪_B[ℰ] ⟶ 𝒪` of the family `α` that `β` lies
over. -/
theorem desc_comp_reduction (Q : S.CompatibleFirstOrderThickening)
    {E : X.Cᵒᵖ ⥤ Type (max u v w)} (α : E ⟶ underlyingPresheaf X.J X.O)
    (β : E ⟶ underlyingPresheaf X.J Q.extension)
    (hβ : β ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{max u v w}) = α) :
    freeAlgebraSheafDesc X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
        Q.extension E Q.baseMap β ≫ Q.reduction =
      baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) E ≫
        Stacks.SheafOfModules.presentation X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
            α := by
  rw [Stacks.Sites.FreeAlgebra.baseChange_comp_desc]
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext X.J _ X.O E ?_ ?_
  · rw [← Category.assoc, Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc, Q.baseMap_reduction]
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc]
    exact hβ

section LiftSection

variable (Q : S.CompatibleFirstOrderThickening) {E : X.Cᵒᵖ ⥤ Type (max u v w)}
  (α : E ⟶ underlyingPresheaf X.J X.O) (β : E ⟶ underlyingPresheaf X.J Q.extension)
  (hβ : β ≫ Functor.whiskerRight Q.reduction.hom (forget CommRingCat.{max u v w}) = α)

include hβ in
/-- The map `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪'` of a solution carries the kernel `ℐ'` of the presentation
`f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪` into the square-zero ideal. -/
theorem reduction_desc_eq_zero {U : X.Cᵒᵖ}
    (p : kernelIdeal (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction) E ≫ Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
          α).hom U) :
    Q.reduction.hom.app U ((freeAlgebraSheafDesc X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) Q.extension E Q.baseMap
        β).hom.app U p) = 0 :=
  (congrArg (fun t : freeAlgebraSheaf X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) E ⟶ X.O ↦ t.hom.app U p.1)
      (desc_comp_reduction Q α β hβ)).trans p.2

/-- The local section of `G` that a local section `p` of `ℐ'` is carried to by the map
`f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪'` of a solution. -/
noncomputable def liftSection {U : X.Cᵒᵖ}
    (p : kernelIdeal (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction) E ≫ Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
          α).hom U) :
    S.G.val.obj U :=
  (Q.exists_incl _ (reduction_desc_eq_zero Q α β hβ p)).choose

/-- The section `liftSection` is the image of `p`, read in the thickened structure sheaf. -/
theorem incl_liftSection {U : X.Cᵒᵖ}
    (p : kernelIdeal (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction) E ≫ Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
          α).hom U) :
    Q.incl (liftSection Q α β hβ p) = (freeAlgebraSheafDesc X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) Q.extension E Q.baseMap
        β).hom.app U p :=
  (Q.exists_incl _ (reduction_desc_eq_zero Q α β hβ p)).choose_spec

/-- `liftSection` is additive. -/
theorem liftSection_add {U : X.Cᵒᵖ}
    (p p' : kernelIdeal (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction) E ≫ Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
          α).hom U) :
    liftSection Q α β hβ (p + p') = liftSection Q α β hβ p + liftSection Q α β hβ p' :=
  Q.incl_injective (by
    rw [Q.incl_add, incl_liftSection, incl_liftSection, incl_liftSection]
    exact map_add (ConcreteCategory.hom ((freeAlgebraSheafDesc X.J _ Q.extension E Q.baseMap
      β).hom.app U)) p.1 p'.1)

/-- `liftSection` is linear over `f⁻¹𝒪_{B'}[ℰ]` acting on `G` through the presentation. -/
theorem liftSection_smul {U : X.Cᵒᵖ}
    (r : (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj
      S.baseExtension) E).obj.obj U)
    (p : kernelIdeal (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction) E ≫ Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
          α).hom U) :
    liftSection Q α β hβ (r • p) =
      (S.G.val.obj U).isModule.toSMul.smul (presentationScalar (baseChange X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) E ≫
          Stacks.SheafOfModules.presentation X.J
            ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
              α) U r) (liftSection Q α β hβ p) :=
  Q.incl_injective (by
    rw [incl_liftSection]
    refine (map_mul (ConcreteCategory.hom ((freeAlgebraSheafDesc X.J _ Q.extension E Q.baseMap
      β).hom.app U)) r p.1).trans ?_
    rw [← incl_liftSection Q α β hβ p, Q.mul_incl]
    exact congrArg (fun s : ↥(((sheafCompose X.J
      (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj X.O).obj.obj U) ↦
        Q.incl (s • liftSection Q α β hβ p))
      (congrArg (fun t ↦ t.hom.app U r) (desc_comp_reduction Q α β hβ)))

/-- `liftSection` commutes with the restriction maps of the site. -/
theorem liftSection_map {U V : X.Cᵒᵖ} (g : U ⟶ V)
    (p : kernelIdeal (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction) E ≫ Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage E
          α).hom U) :
    liftSection Q α β hβ ⟨_, Stacks.Sites.Conormal.map_kernel _ g p.2⟩ =
      S.G.val.map g (liftSection Q α β hβ p) :=
  Q.incl_injective (by
    rw [incl_liftSection, Q.incl_naturality, incl_liftSection]
    exact NatTrans.naturality_apply (freeAlgebraSheafDesc X.J _ Q.extension E Q.baseMap β).hom g
      p.1)

end LiftSection

/-! ### Pairs of solutions on a common family of generators -/

/-- A family of generators for a pair of solutions: a presheaf of sets `ℰ` with a map
`α : ℰ ⟶ 𝒪` and lifts `β₁ : ℰ ⟶ 𝒪'₁` and `β₂ : ℰ ⟶ 𝒪'₂` of it, such that the
presentation `f⁻¹𝒪_B[ℰ] ⟶ 𝒪` of `α` is surjective. This is the datum of Step 1 of the proof of
[Stacks Project, Tag 08UG], for two solutions of the same problem. -/
structure PairDatum (Q₁ Q₂ : S.CompatibleFirstOrderThickening) where
  /-- The presheaf of generators. -/
  E : X.Cᵒᵖ ⥤ Type (max u v w)
  /-- The generators, as local sections of `𝒪`. -/
  α : E ⟶ underlyingPresheaf X.J X.O
  /-- The generators, as local sections of the first thickened structure sheaf. -/
  β₁ : E ⟶ underlyingPresheaf X.J Q₁.extension
  /-- The generators, as local sections of the second thickened structure sheaf. -/
  β₂ : E ⟶ underlyingPresheaf X.J Q₂.extension
  /-- The first family lies over `α`. -/
  comm₁ : β₁ ≫ Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w}) = α
  /-- The second family lies over `α`. -/
  comm₂ : β₂ ≫ Functor.whiskerRight Q₂.reduction.hom (forget CommRingCat.{max u v w}) = α
  /-- The presentation `f⁻¹𝒪_B[ℰ] ⟶ 𝒪` is surjective. -/
  isLocallySurjective : Presheaf.IsLocallySurjective X.J
    (Stacks.SheafOfModules.presentation X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
      X.O S.f.fSharpInverseImage E α).hom

namespace PairDatum

variable {Q₁ Q₂ : S.CompatibleFirstOrderThickening} (d : PairDatum Q₁ Q₂)

/-- The family of generators `α : ℰ ⟶ 𝒪` of the datum. -/
abbrev generatorsMap : d.E ⟶ underlyingPresheaf X.J X.O :=
  d.α

/-- The first family lies over `α`. -/
theorem β₁_comp_reduction :
    d.β₁ ≫ Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w}) =
      d.generatorsMap :=
  d.comm₁

/-- The second family lies over `α`. -/
theorem β₂_comp_reduction :
    d.β₂ ≫ Functor.whiskerRight Q₂.reduction.hom (forget CommRingCat.{max u v w}) =
      d.generatorsMap :=
  d.comm₂

/-- The presentation `f⁻¹𝒪_B[ℰ] ⟶ 𝒪` of the datum. -/
noncomputable abbrev presentation :
    freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E ⟶ X.O :=
  Stacks.SheafOfModules.presentation X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
    X.O S.f.fSharpInverseImage d.E d.generatorsMap

/-- The presentation of a pair datum is surjective. -/
instance isLocallySurjective_presentation :
    Presheaf.IsLocallySurjective X.J d.presentation.hom :=
  d.isLocallySurjective

/-- The presentation `f⁻¹𝒪_{B'}[ℰ] ⟶ f⁻¹𝒪_B[ℰ] ⟶ 𝒪` of the datum with the coefficients of the
thickened base. -/
noncomputable abbrev restrictedPresentation :
    freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) d.E ⟶
      X.O :=
  baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E ≫
    d.presentation

/-- The map `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪'₁` sending the variables to `β₁`. -/
noncomputable abbrev lift₁ :
    freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) d.E ⟶
      Q₁.extension :=
  freeAlgebraSheafDesc X.J _ Q₁.extension d.E Q₁.baseMap d.β₁

/-- The map `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪'₂` sending the variables to `β₂`. -/
noncomputable abbrev lift₂ :
    freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) d.E ⟶
      Q₂.extension :=
  freeAlgebraSheafDesc X.J _ Q₂.extension d.E Q₂.baseMap d.β₂

/-- The difference of the two lifts on the kernel `ℐ'` of `f⁻¹𝒪_{B'}[ℰ] ⟶ 𝒪`, read in `G`:
`p ↦ φ₂(p) − φ₁(p)`. It is a restriction datum for the presentation with the coefficients of
the thickened base. -/
noncomputable def difference :
    IdealRestriction.{v, u, max u v w, w} d.restrictedPresentation (targetG S) where
  app U := AddMonoidHom.mk'
    (fun p ↦ liftSection Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction p -
      liftSection Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction p)
    (fun p p' ↦ by
      rw [liftSection_add, liftSection_add]
      abel)
  app_smul U r p := by
    refine (congrArg₂ (fun a b ↦ a - b)
      (liftSection_smul Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction r p)
      (liftSection_smul Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction r p)).trans ?_
    exact (smul_sub (presentationScalar d.restrictedPresentation U r)
      (show (targetG S).val.obj U from liftSection Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction p)
      (show (targetG S).val.obj U from
        liftSection Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction p)).symm
  app_map g p :=
    (congrArg₂ (fun a b ↦ a - b)
      (liftSection_map Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction g p)
      (liftSection_map Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction g p)).trans
      (map_sub (S.G.val.map g).hom _ _).symm

/-- **The difference datum on a local section of `ℐ'`**: if the two lifts send `p` to the
inclusions of `g₁` and `g₂`, the difference datum takes the value `g₂ - g₁`. -/
theorem difference_app_eq {U : X.Cᵒᵖ} (p : kernelIdeal d.restrictedPresentation.hom U)
    (g₁ g₂ : S.G.val.obj U) (h₁ : Q₁.incl g₁ = d.lift₁.hom.app U p)
    (h₂ : Q₂.incl g₂ = d.lift₂.hom.app U p) :
    d.difference.app U p = g₂ - g₁ := by
  change liftSection Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction p -
    liftSection Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction p = g₂ - g₁
  rw [Q₂.incl_injective ((incl_liftSection Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction
      p).trans h₂.symm),
    Q₁.incl_injective ((incl_liftSection Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction
      p).trans h₁.symm)]

/-- **The difference datum kills the kernel of `f⁻¹𝒪_{B'}[ℰ] ⟶ f⁻¹𝒪_B[ℰ]`.** Such a local
section is locally a polynomial with coefficients in `f⁻¹J`, which both solutions send to the
same section of `G`. -/
theorem difference_eq_zero_of_baseChange {U : X.Cᵒᵖ}
    (k : kernelIdeal d.restrictedPresentation.hom U)
    (hk : (baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
      d.E).hom.app U k = 0) :
    d.difference.app U k = 0 := by
  obtain ⟨T, hT, hq⟩ := Stacks.Sites.FreeAlgebra.exists_covering_polynomial_of_baseChange_eq_zero
    X.J ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) d.E (X := U.unop)
      k.1 hk
  refine (Stacks.Sites.Conormal.IdealRestriction.isSheaf_typeSheaf (G := targetG S) T
    hT).isSeparatedFor.ext fun Y f hf ↦ ?_
  obtain ⟨q, hq0, hqk⟩ := hq Y f hf
  change (targetG S).val.map f.op (d.difference.app U k) = (targetG S).val.map f.op 0
  rw [← d.difference.app_map, map_zero]
  refine (d.difference_app_eq _ (idealPolynomialSection S d.generatorsMap q hq0)
    (idealPolynomialSection S d.generatorsMap q hq0) ?_ ?_).trans (sub_self _)
  · refine (desc_polynomialUnit_eq_incl Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction q
      hq0).symm.trans ?_
    exact congrArg (d.lift₁.hom.app (op Y)) hqk
  · refine (desc_polynomialUnit_eq_incl Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction q
      hq0).symm.trans ?_
    exact congrArg (d.lift₂.hom.app (op Y)) hqk

/-- The difference datum, descended to the kernel `ℐ` of `f⁻¹𝒪_B[ℰ] ⟶ 𝒪`. -/
noncomputable def descendedDifference :
    IdealRestriction.{v, u, max u v w, w} d.presentation (targetG S) :=
  Stacks.Sites.Conormal.IdealRestriction.descend d.difference
    fun _ k hk ↦ d.difference_eq_zero_of_baseChange k hk

/-- **The difference map `D̄₁₂ : ℐ/ℐ² ⟶ G`** of the two solutions on the family of generators:
the morphism out of the conormal sheaf of `f⁻¹𝒪_B[ℰ] ⟶ 𝒪` determined by
`p ↦ φ₂(p) − φ₁(p)` on local sections of `ℐ'`. -/
noncomputable def conormalMap :
    (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max u v w, w} X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
        d.generatorsMap).X₁ ⟶ targetG S :=
  conormalDesc.{v, u, max u v w, w} d.presentation (targetG S) d.descendedDifference

/-- **The value of `D̄₁₂` on the conormal class of the image of a local section `p` of `ℐ'`** is
`φ₂(p) − φ₁(p)`, read in `G`. -/
theorem conormalMap_conormalClass {U : X.Cᵒᵖ} (p : kernelIdeal d.restrictedPresentation.hom U)
    (g₁ g₂ : S.G.val.obj U) (h₁ : Q₁.incl g₁ = d.lift₁.hom.app U p)
    (h₂ : Q₂.incl g₂ = d.lift₂.hom.app U p) :
    d.conormalMap.val.app U (Stacks.Sites.Conormal.conormalClass.{v, u, max u v w, w} X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
      (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E) X.O
      (freeAlgebraSheafCoefficientMap X.J _ d.E) d.presentation U
        ⟨(baseChange X.J ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
          d.E).hom.app U p, p.2⟩) = g₂ - g₁ :=
  (Stacks.Sites.Conormal.conormalDesc_conormalClass d.presentation (targetG S) _ _
    d.descendedDifference U _).trans
    ((Stacks.Sites.Conormal.IdealRestriction.descend_app_mk d.difference _ p p.2).trans
      (d.difference_app_eq p g₁ g₂ h₁ h₂))

/-! ### The class of a pair datum -/

section Class

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- The first Ext class of `D̄₁₂` in `Ext¹_𝒪(NL(α), G)`, for the presentation `α` of the
datum. -/
noncomputable def extClass :
    DerivedCategory.Ext (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.presentationNaiveCotangentComplex.{v, u, max u v w, w} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
          d.generatorsMap))
      ((DerivedCategory.singleFunctor _ 0).obj (targetG S)) 1 :=
  Stacks.SheafOfModules.presentationConormalExtClass.{v, u, w, t} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
    d.generatorsMap (targetG S) d.conormalMap

/-- The canonical comparison `NL(α) ⟶ NL_{𝒪/f⁻¹𝒪_B}` of the presentation of the datum becomes an
isomorphism in `D(𝒪)`, by [Stacks Project, Tag 08TY]. -/
instance isIso_Q_map_naiveCotangentComplexComparison :
    IsIso (DerivedCategory.Q.map
      (Stacks.SheafOfModules.naiveCotangentComplexComparison.{v, u, max u v w, w} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
        d.generatorsMap)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison_site.{v, u, max u v w, w}
      X.J _ X.O S.f.fSharpInverseImage d.E d.generatorsMap)

/-- **The obstruction class of a pair datum** in `Ext¹_𝒪(NL_{𝒪/f⁻¹𝒪_B}, G)`: the class of
`D̄₁₂` in `Ext¹_𝒪(NL(α), G)`, transported along the inverse of the isomorphism
`NL(α) ≅ NL_{𝒪/f⁻¹𝒪_B}` of [Stacks Project, Tag 08TY]. -/
noncomputable def obstruction :
    DerivedCategory.Ext (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, w} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage))
      ((DerivedCategory.singleFunctor _ 0).obj (targetG S)) 1 :=
  inv (DerivedCategory.Q.map
      (Stacks.SheafOfModules.naiveCotangentComplexComparison.{v, u, max u v w, w} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
        d.generatorsMap)) ≫ d.extClass

/-- The obstruction class of a pair datum, pulled back along the comparison
`NL(α) ⟶ NL_{𝒪/f⁻¹𝒪_B}`, is the class of `D̄₁₂`. -/
theorem Q_map_comparison_comp_obstruction :
    DerivedCategory.Q.map
        (Stacks.SheafOfModules.naiveCotangentComplexComparison.{v, u, max u v w, w} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
          d.generatorsMap) ≫ d.obstruction = d.extClass :=
  IsIso.hom_inv_id_assoc _ _

end Class

/-! ### Morphisms of pair data -/

/-- A morphism of pair data: a morphism of the presheaves of generators compatible with the two
families of local sections of the thickened structure sheaves. -/
structure Hom (d d' : PairDatum Q₁ Q₂) where
  /-- The morphism of presheaves of generators. -/
  hom : d.E ⟶ d'.E
  /-- It is compatible with the first family. -/
  comm₁ : hom ≫ d'.β₁ = d.β₁
  /-- It is compatible with the second family. -/
  comm₂ : hom ≫ d'.β₂ = d.β₂

namespace Hom

variable {d} {d' : PairDatum Q₁ Q₂} (e : Hom d d')

/-- A morphism of pair data is a morphism of the families of generators of `𝒪`. -/
theorem comp_generatorsMap : e.hom ≫ d'.generatorsMap = d.generatorsMap := by
  rw [generatorsMap, generatorsMap, ← d'.comm₁, ← Category.assoc, e.comm₁, d.comm₁]

/-- The first lift of the target, precomposed with the renaming of the variables, is the first
lift of the source. -/
theorem freeAlgebraMap_comp_lift₁ :
    Stacks.SheafOfModules.freeAlgebraMap X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) d.E d'.E e.hom ≫
      d'.lift₁ = d.lift₁ := by
  rw [Stacks.Sites.FreeAlgebra.freeAlgebraMap_comp_desc, e.comm₁]

/-- The second lift of the target, precomposed with the renaming of the variables, is the second
lift of the source. -/
theorem freeAlgebraMap_comp_lift₂ :
    Stacks.SheafOfModules.freeAlgebraMap X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) d.E d'.E e.hom ≫
      d'.lift₂ = d.lift₂ := by
  rw [Stacks.Sites.FreeAlgebra.freeAlgebraMap_comp_desc, e.comm₂]

/-- The renaming of the variables carries the difference datum of the source to that of the
target. -/
theorem difference_app_freeAlgebraMap {U : X.Cᵒᵖ}
    (k : kernelIdeal d.restrictedPresentation.hom U)
    (hk : (Stacks.SheafOfModules.freeAlgebraMap X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) d.E d'.E
          e.hom).hom.app U k ∈ kernelIdeal d'.restrictedPresentation.hom U) :
    d'.difference.app U ⟨_, hk⟩ = d.difference.app U k := by
  refine (d'.difference_app_eq _
    (liftSection Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction k)
    (liftSection Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction k) ?_ ?_).trans rfl
  · refine (incl_liftSection Q₁ d.generatorsMap d.β₁ d.β₁_comp_reduction k).trans ?_
    exact (congrArg (fun t ↦ t.hom.app U k.1) e.freeAlgebraMap_comp_lift₁).symm
  · refine (incl_liftSection Q₂ d.generatorsMap d.β₂ d.β₂_comp_reduction k).trans ?_
    exact (congrArg (fun t ↦ t.hom.app U k.1) e.freeAlgebraMap_comp_lift₂).symm

/-- **`D̄₁₂` is natural in the pair datum**: precomposed with the map of conormal sheaves of a
morphism of pair data, the difference map of the target is that of the source. -/
theorem presentationConormalMap_comp_conormalMap :
    Stacks.SheafOfModules.presentationConormalMap.{v, u, max u v w, w} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E d'.E e.hom X.O
        S.f.fSharpInverseImage d.generatorsMap d'.generatorsMap e.comp_generatorsMap ≫
      d'.conormalMap = d.conormalMap := by
  refine Stacks.Sites.Conormal.conormal_hom_ext d.presentation (targetG S) fun U x ↦ ?_
  have h1 := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{v, u, max u v w, w} X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O
    (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E)
    (freeAlgebraSheaf X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d'.E)
    (freeAlgebraSheafCoefficientMap X.J _ d.E) (freeAlgebraSheafCoefficientMap X.J _ d'.E)
    d.presentation d'.presentation
    (Stacks.SheafOfModules.freeAlgebraMap X.J _ d.E d'.E e.hom)
    (Stacks.SheafOfModules.freeAlgebraMap_comp_presentation X.J _ d.E d'.E e.hom X.O
      S.f.fSharpInverseImage d.generatorsMap d'.generatorsMap e.comp_generatorsMap) U x
  have h2 := Stacks.Sites.Conormal.conormalDesc_conormalClass d'.presentation (targetG S)
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
    (freeAlgebraSheafCoefficientMap X.J _ d'.E) d'.descendedDifference U
    ⟨(Stacks.SheafOfModules.freeAlgebraMap X.J _ d.E d'.E e.hom).hom.app U x.1,
      Stacks.Sites.Conormal.kernelIdeal_le_comap _ _ _ (Stacks.Sites.Conormal.hom_of_comp_eq
        (Stacks.SheafOfModules.freeAlgebraMap_comp_presentation X.J _ d.E d'.E e.hom X.O
          S.f.fSharpInverseImage d.generatorsMap d'.generatorsMap e.comp_generatorsMap)) U x.2⟩
  have h3 := Stacks.Sites.Conormal.IdealRestriction.descend_app_map d.difference
    (fun _ k hk ↦ d.difference_eq_zero_of_baseChange k hk) d'.difference
    (fun _ k hk ↦ d'.difference_eq_zero_of_baseChange k hk)
    (Stacks.SheafOfModules.freeAlgebraMap X.J _ d.E d'.E e.hom)
    (Stacks.SheafOfModules.freeAlgebraMap X.J _ d.E d'.E e.hom)
    (Stacks.Sites.FreeAlgebra.freeAlgebraMap_comp_baseChange X.J _ e.hom)
    (Stacks.SheafOfModules.freeAlgebraMap_comp_presentation X.J _ d.E d'.E e.hom X.O
      S.f.fSharpInverseImage d.generatorsMap d'.generatorsMap e.comp_generatorsMap)
    (fun U k ↦ e.difference_app_freeAlgebraMap k _) x
  have h4 := Stacks.Sites.Conormal.conormalDesc_conormalClass d.presentation (targetG S)
    ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)
    (freeAlgebraSheafCoefficientMap X.J _ d.E) d.descendedDifference U x
  exact ((congrArg (d'.conormalMap.val.app U) h1).trans (h2.trans h3)).trans h4.symm

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- The class of `D̄₁₂` is natural in the pair datum. -/
theorem Q_map_comp_extClass :
    DerivedCategory.Q.map
        (Stacks.SheafOfModules.presentationNaiveCotangentComplexMap.{v, u, max u v w, w} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) d.E d'.E e.hom X.O
          S.f.fSharpInverseImage d.generatorsMap d'.generatorsMap e.comp_generatorsMap) ≫
      d'.extClass = d.extClass := by
  rw [extClass, extClass,
    Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_comp_conormalExtClass,
    e.presentationConormalMap_comp_conormalMap]

include e in
/-- **The obstruction class does not depend on the pair datum**: a morphism of pair data
preserves it. This is where [Stacks Project, Tag 08TY] enters, through the compatibility of the
comparison maps with morphisms of presentations. -/
theorem obstruction_eq : d.obstruction = d'.obstruction := by
  rw [← cancel_epi (DerivedCategory.Q.map
      (Stacks.SheafOfModules.naiveCotangentComplexComparison.{v, u, max u v w, w} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage d.E
        d.generatorsMap)), Q_map_comparison_comp_obstruction,
    ← Stacks.SheafOfModules.naiveCotangentComplexComparison_naturality.{v, u, max u v w, w} X.J
      _ X.O S.f.fSharpInverseImage d.E d'.E e.hom d.generatorsMap d'.generatorsMap
      e.comp_generatorsMap,
    Functor.map_comp, Category.assoc, Q_map_comparison_comp_obstruction, e.Q_map_comp_extClass]

end Hom

end PairDatum

/-! ### The canonical pair datum: the fibre product of the two solutions -/

variable (Q₁ Q₂ : S.CompatibleFirstOrderThickening)

/-- The sheaf of sets `ℰ = 𝒪'₁ ×_𝒪 𝒪'₂` underlying the fibre product of the two thickened
structure sheaves over `𝒪`. -/
def pairGenerators : X.Cᵒᵖ ⥤ Type (max u v w) where
  obj U := {x : Q₁.extension.obj.obj U × Q₂.extension.obj.obj U //
    Q₁.reduction.hom.app U x.1 = Q₂.reduction.hom.app U x.2}
  map {U V} g := TypeCat.ofHom fun x ↦ ⟨(Q₁.extension.obj.map g x.1.1,
    Q₂.extension.obj.map g x.1.2), by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, x.2]⟩
  map_id U := by
    ext x
    · exact CategoryTheory.congr_fun (Q₁.extension.obj.map_id U) x.1.1
    · exact CategoryTheory.congr_fun (Q₂.extension.obj.map_id U) x.1.2
  map_comp f g := by
    ext x
    · exact CategoryTheory.congr_fun (Q₁.extension.obj.map_comp f g) x.1.1
    · exact CategoryTheory.congr_fun (Q₂.extension.obj.map_comp f g) x.1.2

/-- The first projection `𝒪'₁ ×_𝒪 𝒪'₂ ⟶ 𝒪'₁`. -/
def pairFst : pairGenerators Q₁ Q₂ ⟶ underlyingPresheaf X.J Q₁.extension where
  app _ := TypeCat.ofHom fun x ↦ x.1.1
  naturality _ _ _ := rfl

/-- The second projection `𝒪'₁ ×_𝒪 𝒪'₂ ⟶ 𝒪'₂`. -/
def pairSnd : pairGenerators Q₁ Q₂ ⟶ underlyingPresheaf X.J Q₂.extension where
  app _ := TypeCat.ofHom fun x ↦ x.1.2
  naturality _ _ _ := rfl

/-- The two projections lie over the same map to `𝒪`. -/
theorem pairFst_comp_reduction :
    pairFst Q₁ Q₂ ≫ Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w}) =
      pairSnd Q₁ Q₂ ≫ Functor.whiskerRight Q₂.reduction.hom (forget CommRingCat.{max u v w}) := by
  ext U x
  exact x.2

/-- The map `𝒪'₁ ×_𝒪 𝒪'₂ ⟶ 𝒪` is locally surjective, both reductions being so. -/
theorem isLocallySurjective_pairFst_comp_reduction :
    Presheaf.IsLocallySurjective X.J
      (pairFst Q₁ Q₂ ≫ Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w})) where
  imageSieve_mem {U} s := by
    have h₁ := (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q₁.reduction.hom).mp
      Q₁.locallySurjective
    have h₂ := (Presheaf.isLocallySurjective_iff_whisker_forget X.J Q₂.reduction.hom).mp
      Q₂.locallySurjective
    refine X.J.superset_covering ?_ (X.J.intersection_covering
      (Presheaf.imageSieve_mem X.J
        (Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w})) s)
      (Presheaf.imageSieve_mem X.J
        (Functor.whiskerRight Q₂.reduction.hom (forget CommRingCat.{max u v w})) s))
    rintro V f ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩
    exact ⟨⟨(q₁, q₂), hq₁.trans hq₂.symm⟩, hq₁⟩

/-- The presentation `f⁻¹𝒪_B[𝒪'₁ ×_𝒪 𝒪'₂] ⟶ 𝒪` is surjective. -/
theorem isLocallySurjective_pairPresentation :
    Presheaf.IsLocallySurjective X.J
      (Stacks.SheafOfModules.presentation X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
        (pairGenerators Q₁ Q₂)
        (pairFst Q₁ Q₂ ≫
          Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w}))).hom := by
  have := isLocallySurjective_pairFst_comp_reduction Q₁ Q₂
  exact (Presheaf.isLocallySurjective_iff_whisker_forget X.J _).mpr
    (Presheaf.isLocallySurjective_of_isLocallySurjective_fac X.J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O (pairGenerators Q₁ Q₂)
        S.f.fSharpInverseImage
        (pairFst Q₁ Q₂ ≫ Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w}))))

/-- **The canonical pair datum** of two solutions: the generators are the local sections of the
fibre product `𝒪'₁ ×_𝒪 𝒪'₂`, sent to their two projections. -/
def pairDatum : PairDatum Q₁ Q₂ where
  E := pairGenerators Q₁ Q₂
  α := pairFst Q₁ Q₂ ≫ Functor.whiskerRight Q₁.reduction.hom (forget CommRingCat.{max u v w})
  β₁ := pairFst Q₁ Q₂
  β₂ := pairSnd Q₁ Q₂
  comm₁ := rfl
  comm₂ := (pairFst_comp_reduction Q₁ Q₂).symm
  isLocallySurjective := isLocallySurjective_pairPresentation Q₁ Q₂

variable {Q₁ Q₂}

/-- Every pair datum maps to the canonical one, by the pair of its two families. -/
def PairDatum.toPairDatum (d : PairDatum Q₁ Q₂) : PairDatum.Hom d (pairDatum Q₁ Q₂) where
  hom :=
    { app U := TypeCat.ofHom fun x ↦ ⟨(d.β₁.app U x, d.β₂.app U x),
        ConcreteCategory.congr_hom (NatTrans.congr_app (d.comm₁.trans d.comm₂.symm) U) x⟩
      naturality U V g := by
        ext x
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact NatTrans.naturality_apply d.β₁ g x
        · exact NatTrans.naturality_apply d.β₂ g x }
  comm₁ := rfl
  comm₂ := rfl

variable [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, w} X.J X.O)]

/-- **The obstruction class `o(𝒪'₁, 𝒪'₂)` of two solutions** of the square-zero extension problem,
in `Ext¹_𝒪(NL_{𝒪/f⁻¹𝒪_B}, G)`: the class of the difference map `D̄₁₂ : ℐ/ℐ² ⟶ G` of the
canonical pair datum, transported to the naive cotangent complex. By
`PairDatum.obstruction_eq_pairDatumObstruction` every pair datum gives the same class. -/
noncomputable def pairDatumObstruction (Q₁ Q₂ : S.CompatibleFirstOrderThickening) :
    DerivedCategory.Ext (DerivedCategory.Q.obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, w} X.J
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage))
      ((DerivedCategory.singleFunctor _ 0).obj (targetG S)) 1 :=
  (pairDatum Q₁ Q₂).obstruction

/-- **The obstruction class does not depend on the family of generators**: the class of the
difference map of any pair datum is `o(𝒪'₁, 𝒪'₂)`. -/
theorem PairDatum.obstruction_eq_pairDatumObstruction (d : PairDatum Q₁ Q₂) :
    Eq d.obstruction (pairDatumObstruction Q₁ Q₂) :=
  d.toPairDatum.obstruction_eq

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

/-! ### The obstruction class in `Ext¹_𝒪(NL_f, G)` -/

namespace Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

variable {X : RingedTopos.{v, u, max u v}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{max u v})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, v, u} X.J X.O)]

/-- **The obstruction class `o(𝒪'₁, 𝒪'₂)` of two solutions** of the square-zero extension problem
of [Stacks Project, Tag 08UF], in `Ext¹_𝒪(NL_f, G)` for the naive cotangent complex `NL_f` of
`f`. -/
noncomputable def pairObstruction (Q₁ Q₂ : S.CompatibleFirstOrderThickening) :
    S.f.naiveCotangentExt (targetG S) 1 :=
  pairDatumObstruction Q₁ Q₂

/-- **`o(𝒪'₁, 𝒪'₂)` does not depend on the family of generators**: the class of the difference
map `D̄₁₂` of any pair datum, transported to `Ext¹_𝒪(NL_f, G)`, is `o(𝒪'₁, 𝒪'₂)`. -/
theorem PairDatum.obstruction_eq_pairObstruction {Q₁ Q₂ : S.CompatibleFirstOrderThickening}
    (d : PairDatum Q₁ Q₂) : Eq d.obstruction (pairObstruction Q₁ Q₂) :=
  d.obstruction_eq_pairDatumObstruction

end Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening
