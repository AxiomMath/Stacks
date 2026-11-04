module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafNaturality

/-!
# Multiplication on the cohomology of the twists of projective space

Let `X = ℙⁿ_R = Proj R[T₀, …, Tₙ]` with `n ≥ 1`, and let `f ∈ R[T₀, …, Tₙ]` be homogeneous of
degree `m`. Multiplication by `f` is a map `𝒪_X(d) → 𝒪_X(d + m)`. Through the identifications of
Equation [Stacks, Tag 01XU], `H⁰(X, 𝒪_X(d)) = R[T₀, …, Tₙ]_d` and
`Hⁿ(X, 𝒪_X(d)) = Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`, the induced map on `H⁰` is multiplication by
`f`, and the induced map on `Hⁿ` is the transpose of multiplication by `f`,
`(R[T₀, …, Tₙ])_{-n-1-(d+m)} → (R[T₀, …, Tₙ])_{-n-1-d}` ([Stacks, Tag 01XV]).

The map on sheaf cohomology is read on the monomial Čech complex: multiplication by `f` on the
twists acts on it by multiplication by `f` on Laurent monomials, and the identifications in degree
zero and in top degree intertwine it with multiplication by `f`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology_degreeZero_mul`: multiplication by `f`
  on `H⁰` is multiplication by `f` on `R[T₀, …, Tₙ]_d`.
* `Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology_degreeTop_mul`: multiplication by `f`
  on `Hⁿ` is the transpose of multiplication by `f`.

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf Stacks.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] Stacks.ProjectiveSpace.Cohomology.laurentCechComplex

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The inverse of a composite of two isomorphisms, followed by a morphism, stated on
variables. -/
theorem trans_inv_comp {C : Type*} [Category* C] {A B D T : C} (e₁ : A ≅ B) (e₂ : B ≅ D)
    (g : A ⟶ T) : (e₁ ≪≫ e₂).inv ≫ g = e₂.inv ≫ e₁.inv ≫ g := by
  rw [Iso.trans_inv, Category.assoc]

/-- Two commuting squares of complexes, read on homology, stated on variables. -/
theorem homologyMap_comm {C : Type*} [Category* C] [HasZeroMorphisms C] {κ : Type*}
    {c : ComplexShape κ} {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (a : K₁ ⟶ K₂) (b₁ : K₁ ⟶ L₁)
    (b₂ : K₂ ⟶ L₂) (m : L₁ ⟶ L₂) (h : a ≫ b₂ = b₁ ≫ m) (p : κ) [K₁.HasHomology p]
    [K₂.HasHomology p] [L₁.HasHomology p] [L₂.HasHomology p] :
    HomologicalComplex.homologyMap a p ≫ HomologicalComplex.homologyMap b₂ p =
      HomologicalComplex.homologyMap b₁ p ≫ HomologicalComplex.homologyMap m p := by
  rw [← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_comp]

/-! ### Multiplication by a homogeneous polynomial on the monomial Čech complex -/

/-- **Multiplication by `f`, homogeneous of degree `m`, as a morphism of monomial Čech
complexes** from that of `𝒪(d)` to that of `𝒪(e)`, `d + m = e`. -/
def laurentCechComplexMul {m d e : ℤ} (f : twistChart R n m (∅ : Set (Fin (n + 1))))
    (hde : d + m = e) : laurentCechComplex R n d ⟶ laurentCechComplex R n e :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (laurentCechCochainMul f hde q)) fun q => by
    rw [laurentCechComplex_d, laurentCechComplex_d]
    ext c
    exact (LinearMap.congr_fun (laurentCechDiffRestrict_laurentCechCochainMul f hde q) c).symm

/-- The degree-`q` component of `laurentCechComplexMul`. -/
@[simp]
theorem laurentCechComplexMul_f {m d e : ℤ} (f : twistChart R n m (∅ : Set (Fin (n + 1))))
    (hde : d + m = e) (q : ℕ) :
    (laurentCechComplexMul R n f hde).f q = ModuleCat.ofHom (laurentCechCochainMul f hde q) :=
  rfl

/-- **On the ordered Čech cochains of the standard cover, the sheaf-level multiplication map is
multiplication by `f` on the monomial cochains.** -/
theorem twistOrdCochainEquiv_twistScalarSheafMap {i : ℕ} {d e : ℤ}
    (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1)))) (hde : d + (i : ℤ) = e)
    (hk : (i : ℤ) + d = e) (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of (AlgebraicGeometry.Proj (polyGrading R n)))
      (basicOpenXAtUniverse R n)
      (abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p) :
    twistOrdCochainEquiv R n e p
        (ConcreteCategory.hom (ordCochainModuleMap
          (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens) (basicOpenXAtUniverse R n)
          (iSup_basicOpenXAtUniverse_eq_top R n).symm
          (twistScalarSheafMap (polyGrading R n) i d e hk
            ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R), polyOfLaurent_mem f.2⟩) p) s) =
      laurentCechCochainMul f hde p (twistOrdCochainEquiv R n d p s) := by
  refine (ordChartEquiv R n e p).injective (funext fun t => Subtype.ext ?_)
  exact (coe_twistOrdCochainEquiv_apply R n e p _ t).trans
    ((coe_ordInterChartAddEquiv_twistScalarSheafMap R n f hde hk p (ordIndexUp n p t) _).trans
      (congrArg (laurentMul _) (coe_twistOrdCochainEquiv_apply R n d p s t).symm))

/-- **The monomial model of the ordered Čech complex carries the morphism of Čech complexes
induced by multiplication by `f` to multiplication by `f` on the monomial cochains.** -/
theorem twistOrderedComplexIsoLaurent_twistScalarSheafMap {i : ℕ} {d e : ℤ}
    (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1)))) (hde : d + (i : ℤ) = e)
    (hk : (i : ℤ) + d = e) :
    ((ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
        (twistOrderedMap R n (twistScalarSheafMap (polyGrading R n) i d e hk
          ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R), polyOfLaurent_mem f.2⟩)) ≫
        (twistOrderedComplexIsoLaurent R n e).hom =
      (twistOrderedComplexIsoLaurent R n d).hom ≫ laurentCechComplexMul R n f hde := by
  ext p s
  exact twistOrdCochainEquiv_twistScalarSheafMap R n f hde hk p s

/-- **The identification of the cohomology of `𝒪(d)` with the homology of the monomial Čech
complex carries the map induced by multiplication by `f` to the map induced by multiplication by
`f` on the monomial cochains.** -/
theorem twistCohomologyIsoLaurentHomology_twistScalarSheafMap {i : ℕ} {d e : ℤ}
    (f : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1)))) (hde : d + (i : ℤ) = e)
    (hk : (i : ℤ) + d = e) (q : ℕ) :
    (ModuleCat.restrictScalars.{u} (coeffScalar R n)).map
          (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n))
            ⊤).rightDerived q).map (twistScalarSheafMap (polyGrading R n) i d e hk
              ⟨polyOfLaurent (f : (Fin (n + 1) → ℤ) →₀ R), polyOfLaurent_mem f.2⟩)) ≫
        (twistCohomologyIsoLaurentHomology R n e q).hom =
      (twistCohomologyIsoLaurentHomology R n d q).hom ≫
        HomologicalComplex.homologyMap (laurentCechComplexMul R n f hde) q :=
  paste_two _ _ _ _ _ _ _ (twistCohomologyIsoOrderedHomology_naturality R n _ q)
    (homologyMap_comm _ _ _ _ (twistOrderedComplexIsoLaurent_twistScalarSheafMap R n f hde hk) q)

/-! ### The degree-zero and top-degree readings of the monomial Čech homology -/

/-- The degree-zero homology of the monomial Čech complex, as cocycles inside the degree-zero
cochains. -/
def homologyZeroι (N : ℕ) (d : ℤ) :
    (laurentCechComplex R (N + 1) d).homology 0 ⟶ (laurentCechComplex R (N + 1) d).X 0 :=
  ((laurentCechComplex R (N + 1) d).isoHomologyπ 0 0 (by simp)
      ((laurentCechComplex R (N + 1) d).shape 0 0 (by simp))).inv ≫
    (laurentCechComplex R (N + 1) d).iCycles 0

/-- The inclusion of the degree-zero homology into the degree-zero cochains is a monomorphism. -/
instance mono_homologyZeroι (N : ℕ) (d : ℤ) : Mono (homologyZeroι R N d) := by
  rw [homologyZeroι]
  infer_instance

/-- A morphism of monomial Čech complexes acts on the degree-zero homology through its
degree-zero component. -/
theorem homologyMap_homologyZeroι {N : ℕ} {d e : ℤ}
    (M : laurentCechComplex R (N + 1) d ⟶ laurentCechComplex R (N + 1) e) :
    HomologicalComplex.homologyMap M 0 ≫ homologyZeroι R N e = homologyZeroι R N d ≫ M.f 0 := by
  rw [homologyZeroι, homologyZeroι, ← cancel_epi
    ((laurentCechComplex R (N + 1) d).isoHomologyπ 0 0 (by simp)
      ((laurentCechComplex R (N + 1) d).shape 0 0 (by simp))).hom]
  simp only [Category.assoc, HomologicalComplex.isoHomologyπ_hom,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc, HomologicalComplex.cyclesMap_i]

/-- **The degree-zero identification of [Stacks, Equation 01XU] sends a cocycle to the
corresponding element of the degree-`d` part of `R[T₀, …, Tₙ]`**: read back in the degree-zero
cochains, the inverse of `homologyZeroIso` is the diagonal cocycle. -/
theorem homologyZeroIso_inv_homologyZeroι (N : ℕ) (d : ℤ) :
    (homologyZeroIso R N d).inv ≫ homologyZeroι R N d =
      ModuleCat.ofHom ((LinearMap.ker (laurentCechDiffRestrict R (N + 1) d 0)).subtype ∘ₗ
        (laurentCechCohomologyZeroEquiv (R := R) (n := N + 1) (d := d)
          N.succ_pos).toLinearMap) := by
  simp only [homologyZeroIso, homologyZeroι, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    HomologicalComplex.isoHomologyπ_hom, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
    HomologicalComplex.cyclesIsoSc'_inv_iCycles]
  refine (trans_inv_comp _ _ _).trans ((congrArg (fun t => _ ≫ t)
    (ShortComplex.moduleCatCyclesIso_inv_iCycles _)).trans ?_)
  ext z
  rfl

/-- **On the degree-zero homology, multiplication by `f` is multiplication by `f` on the
degree-`d` part of `R[T₀, …, Tₙ]`**, through `homologyZeroIso`. -/
theorem homologyMap_laurentCechComplexMul_homologyZeroIso {N : ℕ} {m d e : ℤ}
    (f : twistChart R (N + 1) m (∅ : Set (Fin (N + 1 + 1)))) (hde : d + m = e) :
    HomologicalComplex.homologyMap (laurentCechComplexMul R (N + 1) f hde) 0 ≫
        (homologyZeroIso R N e).hom =
      (homologyZeroIso R N d).hom ≫
        ModuleCat.ofHom (chartMul f hde (∅ : Set (Fin (N + 1 + 1)))) := by
  rw [← cancel_epi (homologyZeroIso R N d).inv, Iso.inv_hom_id_assoc,
    ← cancel_mono (homologyZeroIso R N e).inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ← cancel_mono (homologyZeroι R N e), Category.assoc,
    homologyMap_homologyZeroι, ← Category.assoc, homologyZeroIso_inv_homologyZeroι,
    Category.assoc, homologyZeroIso_inv_homologyZeroι]
  ext z
  exact Subtype.ext (laurentCochainMul_laurentDiagonalCochain f hde z)

/-- The top-degree cochains of the monomial Čech complex, onto its top-degree homology. -/
def homologyTopπ (N : ℕ) (d : ℤ) :
    (laurentCechComplex R (N + 1) d).X (N + 1) ⟶
      (laurentCechComplex R (N + 1) d).homology (N + 1) :=
  (laurentCechComplex R (N + 1) d).pOpcycles (N + 1) ≫
    ((laurentCechComplex R (N + 1) d).isoHomologyι (N + 1) (N + 1 + 1) (by simp)
      (laurentCechComplex_d_eq_zero_of_lt (by omega))).inv

/-- The projection of the top-degree cochains onto the top-degree homology is an epimorphism. -/
instance epi_homologyTopπ (N : ℕ) (d : ℤ) : Epi (homologyTopπ R N d) := by
  rw [homologyTopπ]
  infer_instance

/-- A morphism of monomial Čech complexes acts on the top-degree homology through its top-degree
component. -/
theorem homologyTopπ_homologyMap {N : ℕ} {d e : ℤ}
    (M : laurentCechComplex R (N + 1) d ⟶ laurentCechComplex R (N + 1) e) :
    homologyTopπ R N d ≫ HomologicalComplex.homologyMap M (N + 1) =
      M.f (N + 1) ≫ homologyTopπ R N e := by
  rw [homologyTopπ, homologyTopπ, ← cancel_mono
    ((laurentCechComplex R (N + 1) e).isoHomologyι (N + 1) (N + 1 + 1) (by simp)
      (laurentCechComplex_d_eq_zero_of_lt (by omega))).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [HomologicalComplex.isoHomologyι_hom, HomologicalComplex.homologyι_naturality,
    ← Category.assoc ((laurentCechComplex R (N + 1) d).isoHomologyι (N + 1) (N + 1 + 1) (by simp)
      (laurentCechComplex_d_eq_zero_of_lt (by omega))).inv, ← HomologicalComplex.isoHomologyι_hom,
    Iso.inv_hom_id, Category.id_comp, HomologicalComplex.p_opcyclesMap]
  · simp
  · exact laurentCechComplex_d_eq_zero_of_lt (by omega)

/-- **The top-degree identification of [Stacks, Equation 01XU] sends the class of a cochain to
the functional it represents.** -/
theorem homologyTopπ_homologyTopIso (N : ℕ) (d : ℤ) :
    homologyTopπ R N d ≫ (homologyTopIso R N d).hom =
      ModuleCat.ofHom ((laurentCechCohomologyTopEquiv R N d).toLinearMap ∘ₗ
        (LinearMap.range (laurentCechDiffRestrict R (N + 1) d N)).mkQ) := by
  simp only [homologyTopπ, homologyTopIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc, HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ _)
    (ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom _)).trans ?_)
  ext c
  rfl

/-- **On the top-degree homology, multiplication by `f` is the contragredient of multiplication
by `f`**, through `homologyTopIso`. -/
theorem homologyMap_laurentCechComplexMul_homologyTopIso {N : ℕ} {m d e : ℤ}
    (f : twistChart R (N + 1) m (∅ : Set (Fin (N + 1 + 1)))) (hde : d + m = e) :
    HomologicalComplex.homologyMap (laurentCechComplexMul R (N + 1) f hde) (N + 1) ≫
        (homologyTopIso R N e).hom =
      (homologyTopIso R N d).hom ≫ ModuleCat.ofHom
        (chartMul f (dualDegree_add_of_add N hde) (∅ : Set (Fin (N + 1 + 1)))).dualMap := by
  rw [← cancel_epi (homologyTopπ R N d), ← Category.assoc, homologyTopπ_homologyMap,
    Category.assoc, homologyTopπ_homologyTopIso, ← Category.assoc, homologyTopπ_homologyTopIso]
  ext c h
  exact laurentCechCohomologyTopEquiv_laurentCechCochainMul f hde c h

/-! ### A homogeneous polynomial as a monomial chart element -/

/-- The polynomial with given Laurent coefficients, as a linear map. -/
def polyOfLaurentLinear :
    ((Fin (n + 1) → ℤ) →₀ R) →ₗ[R] MvPolynomial (Fin (n + 1)) R :=
  Finsupp.lsum R fun a => MvPolynomial.monomial (laurentToNatExp a)

/-- `polyOfLaurentLinear` sends Laurent coefficients `f` to the polynomial `polyOfLaurent f`. -/
theorem polyOfLaurentLinear_apply (f : (Fin (n + 1) → ℤ) →₀ R) :
    polyOfLaurentLinear R n f = polyOfLaurent f :=
  Finsupp.lsum_apply _ _ _

/-- The monomial chart isomorphism on a single Laurent monomial. -/
theorem coe_twistChartEmptyLinearEquiv_single {i : ℕ}
    (a : laurentMonomials n (i : ℤ) (∅ : Set (Fin (n + 1)))) (c : R) :
    ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg i)
        ((Finsupp.supportedEquivFinsupp (R := R) _).symm (Finsupp.single a c)) :
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (i : ℤ).toNat) :
            MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.monomial (laurentToNatExp (a : Fin (n + 1) → ℤ)) c := by
  show ((AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R)
      {m : Fin (n + 1) →₀ ℕ | m.degree = (i : ℤ).toNat}).symm
        (Finsupp.domLCongr (laurentMonomialsEmptyEquiv n (Int.natCast_nonneg i))
          (Finsupp.supportedEquivFinsupp (R := R) (M := R)
            (laurentMonomials n (i : ℤ) (∅ : Set (Fin (n + 1))))
            ((Finsupp.supportedEquivFinsupp (R := R) _).symm (Finsupp.single a c)))) :
        AddMonoidAlgebra R (Fin (n + 1) →₀ ℕ)) = _
  rw [LinearEquiv.apply_symm_apply, Finsupp.domLCongr_single]
  show AddMonoidAlgebra.ofCoeff (((Finsupp.supportedEquivFinsupp (R := R) (M := R)
      {m : Fin (n + 1) →₀ ℕ | m.degree = (i : ℤ).toNat}).symm
        (Finsupp.single (laurentMonomialsEmptyEquiv n (Int.natCast_nonneg i) a) c) :
          (Fin (n + 1) →₀ ℕ) →₀ R)) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single, AddMonoidAlgebra.ofCoeff_single]
  rfl

/-- **The monomial basis of the polynomial chart is the polynomial with those Laurent
coefficients.** -/
theorem coe_twistChartEmptyLinearEquiv {i : ℕ}
    (x : twistChart R n (i : ℤ) (∅ : Set (Fin (n + 1)))) :
    ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg i) x :
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (i : ℤ).toNat) :
          MvPolynomial (Fin (n + 1)) R) = polyOfLaurent (x : (Fin (n + 1) → ℤ) →₀ R) := by
  have key : (Submodule.subtype _).comp
        ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg i)).toLinearMap.comp
          (Finsupp.supportedEquivFinsupp (R := R) _).symm.toLinearMap) =
      (polyOfLaurentLinear R n).comp ((Submodule.subtype _).comp
        (Finsupp.supportedEquivFinsupp (R := R) _).symm.toLinearMap) := by
    refine Finsupp.lhom_ext fun a c => ?_
    refine (coe_twistChartEmptyLinearEquiv_single R n a c).trans ?_
    show _ = polyOfLaurentLinear R n
      ((Finsupp.supportedEquivFinsupp (R := R) _).symm (Finsupp.single a c) :
        (Fin (n + 1) → ℤ) →₀ R)
    rw [Finsupp.supportedEquivFinsupp_symm_single, polyOfLaurentLinear_apply, polyOfLaurent,
      Finsupp.sum_single_index (by simp)]
  have e := (Finsupp.supportedEquivFinsupp (R := R) (M := R)
    (laurentMonomials n (i : ℤ) (∅ : Set (Fin (n + 1))))).symm_apply_apply x
  calc ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg i) x :
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (i : ℤ).toNat) :
            MvPolynomial (Fin (n + 1)) R)
      = ((twistChartEmptyLinearEquiv (R := R) n (Int.natCast_nonneg i)
          ((Finsupp.supportedEquivFinsupp (R := R) _).symm
            (Finsupp.supportedEquivFinsupp (R := R) _ x)) :
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (i : ℤ).toNat) :
            MvPolynomial (Fin (n + 1)) R) := by rw [e]
    _ = polyOfLaurentLinear R n (((Finsupp.supportedEquivFinsupp (R := R) _).symm
          (Finsupp.supportedEquivFinsupp (R := R) _ x) : Finsupp.supported R R _) :
            (Fin (n + 1) → ℤ) →₀ R) :=
      LinearMap.congr_fun key (Finsupp.supportedEquivFinsupp (R := R) _ x)
    _ = polyOfLaurent (x : (Fin (n + 1) → ℤ) →₀ R) := by rw [e, polyOfLaurentLinear_apply]

/-- **A homogeneous polynomial of degree `i` is the polynomial with the Laurent coefficients of
its monomial chart element.** -/
theorem polyOfLaurent_chartOfHomogeneous {i : ℕ} (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f.IsHomogeneous i) :
    polyOfLaurent ((chartOfHomogeneous R n f hf : twistChart R n (i : ℤ) ∅) :
      (Fin (n + 1) → ℤ) →₀ R) = f :=
  (coe_twistChartEmptyLinearEquiv R n _).symm.trans
    (congrArg Subtype.val ((twistChartEmptyLinearEquiv (R := R) n
      (Int.natCast_nonneg i)).apply_symm_apply _))

/-! ### Multiplication by a homogeneous polynomial on `H⁰` and `Hⁿ` -/

/-- A homogeneous polynomial, as an element of the graded piece of `R[T₀, …, Tₙ]` along which the
twisting sheaves are multiplied, is the polynomial of its monomial chart element. -/
theorem homogeneous_eq_polyOfLaurent {i : ℕ} (f : MvPolynomial (Fin (n + 1)) R)
    (hf : f.IsHomogeneous i) :
    (⟨f, (MvPolynomial.mem_homogeneousSubmodule i f).2 hf⟩ : polyGrading R n i) =
      ⟨polyOfLaurent ((chartOfHomogeneous R n f hf : twistChart R n (i : ℤ) ∅) :
          (Fin (n + 1) → ℤ) →₀ R), polyOfLaurent_mem (chartOfHomogeneous R n f hf).2⟩ :=
  Subtype.ext (polyOfLaurent_chartOfHomogeneous R n f hf).symm

/-- **[Stacks, Tag 01XV], multiplication on `H⁰`.** For `f ∈ R[T₀, …, Tₙ]` homogeneous of degree
`m`, the map `H⁰(ℙⁿ_R, 𝒪(d)) ⟶ H⁰(ℙⁿ_R, 𝒪(d + m))` induced by the morphism of sheaves
`𝒪(d) ⟶ 𝒪(d + m)` given by multiplication by `f` is, through the identification of
[Stacks, Equation 01XU] of `H⁰(ℙⁿ_R, 𝒪(d))` with `(R[T₀, …, Tₙ])_d`, multiplication by `f`
`(R[T₀, …, Tₙ])_d ⟶ (R[T₀, …, Tₙ])_{d+m}`. Here `n = N + 1` and `d` is any integer. -/
@[stacks 01XV "multiplication by a homogeneous f on H^0, through Equation 01XU"]
theorem serreTwistCohomology_degreeZero_mul (N : ℕ) {m : ℕ} {d e : ℤ}
    (f : MvPolynomial (Fin (N + 1 + 1)) R) (hf : f.IsHomogeneous m) (hde : d + m = e) :
    (ModuleCat.restrictScalars.{u} (coeffScalar R (N + 1))).map
          (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R (N + 1)))
            ⊤).rightDerived 0).map (twistScalarSheafMap (polyGrading R (N + 1)) m d e
              (by omega) ⟨f, (MvPolynomial.mem_homogeneousSubmodule m f).2 hf⟩)) ≫
        (serreTwistCohomology R N e).degreeZero.hom =
      (serreTwistCohomology R N d).degreeZero.hom ≫
        ModuleCat.ofHom (chartMul (chartOfHomogeneous R (N + 1) f hf) hde ∅) := by
  rw [homogeneous_eq_polyOfLaurent R (N + 1) f hf]
  exact paste_two _ _ _ _ _ _ _
    (twistCohomologyIsoLaurentHomology_twistScalarSheafMap R (N + 1) _ hde _ 0)
    (homologyMap_laurentCechComplexMul_homologyZeroIso R _ hde)

/-- **[Stacks, Tag 01XV], multiplication on `Hⁿ`.** For `f ∈ R[T₀, …, Tₙ]` homogeneous of degree
`m`, the map `Hⁿ(ℙⁿ_R, 𝒪(d)) ⟶ Hⁿ(ℙⁿ_R, 𝒪(d + m))` induced by the morphism of sheaves
`𝒪(d) ⟶ 𝒪(d + m)` given by multiplication by `f` is, through the identifications of
[Stacks, Equation 01XU] of `Hⁿ(ℙⁿ_R, 𝒪(d))` with `Hom_R((R[T₀, …, Tₙ])_{-n-1-d}, R)`, the
contragredient of multiplication by `f`
`(R[T₀, …, Tₙ])_{-n-1-(d+m)} ⟶ (R[T₀, …, Tₙ])_{-n-1-d}`. Here `n = N + 1` and `d` is any
integer. -/
@[stacks 01XV "multiplication by a homogeneous f on H^n is the contragredient, through Equation 01XU"]
theorem serreTwistCohomology_degreeTop_mul (N : ℕ) {m : ℕ} {d e : ℤ}
    (f : MvPolynomial (Fin (N + 1 + 1)) R) (hf : f.IsHomogeneous m) (hde : d + m = e) :
    (ModuleCat.restrictScalars.{u} (coeffScalar R (N + 1))).map
          (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R (N + 1)))
            ⊤).rightDerived (N + 1)).map (twistScalarSheafMap (polyGrading R (N + 1)) m d e
              (by omega) ⟨f, (MvPolynomial.mem_homogeneousSubmodule m f).2 hf⟩)) ≫
        (serreTwistCohomology R N e).degreeTop.hom =
      (serreTwistCohomology R N d).degreeTop.hom ≫
        ModuleCat.ofHom
          (chartMul (chartOfHomogeneous R (N + 1) f hf)
            (dualDegree_add_of_add N hde) ∅).dualMap := by
  rw [homogeneous_eq_polyOfLaurent R (N + 1) f hf]
  exact paste_two _ _ _ _ _ _ _
    (twistCohomologyIsoLaurentHomology_twistScalarSheafMap R (N + 1) _ hde _ (N + 1))
    (homologyMap_laurentCechComplexMul_homologyTopIso R _ hde)

end Stacks.ProjectiveSpace.Cohomology

end
