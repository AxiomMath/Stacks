module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.JacobianSituation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# Unramifiedness and étaleness from a full-rank Jacobian

A system of `m` polynomial equations in `n` variables over `R` whose Jacobian has full column rank
at a prime cuts out a scheme which is unramified over `Spec R` at the corresponding point; there
are then at least as many equations as variables, and when the two numbers agree the morphism is
flat, hence étale, at that point. The proof is the Jacobian criterion: away from the determinant
of a maximal Jacobian minor the quotient by the corresponding `n` equations has a submersive
presentation of relative dimension zero, so it is standard smooth of relative dimension zero and
therefore étale.

## Main results

* `AlgebraicGeometry.FullRankJacobianSituation.unramifiedAt_over` gives unramifiedness of the
  structure morphism at the selected point, for any number of equations.
* `AlgebraicGeometry.FullRankJacobianSituation.numVariables_le_numEquations` records that a
  full-rank Jacobian forces at least as many equations as variables.
* `AlgebraicGeometry.FullRankJacobianSituation.etaleAt_over_of_square` gives étaleness of the
  structure morphism at the selected point when the number of equations equals the number of
  variables.
* `AlgebraicGeometry.FullRankJacobianSituation.isFlatAt_over_of_square` deduces flatness of the
  structure morphism at the selected point in the same situation.

## Implementation notes

The ring-theoretic core is `AlgebraicGeometry.FullRankJacobianSituation.etale_away_jacobianDet`:
any localization of the polynomial quotient away from the Jacobian determinant of a square system
is étale over the base. It is obtained by composing Mathlib's naive pre-submersive presentation of
the quotient with the pre-submersive presentation of a localization away from one element; the
Jacobian of the composite is the product of the two Jacobians, hence a unit after inverting the
determinant.

For a general number of equations no square system is available, so a maximal minor of the
Jacobian is selected instead: full column rank over the residue field produces `n` rows which are
linearly independent, and the determinant of the corresponding `n` equations is then outside the
prime. The quotient by all the equations, localized away from that determinant, is a quotient of
the localized quotient by the selected `n` equations alone. Unramifiedness is inherited by
quotients — formal unramifiedness because an epimorphism cannot separate two lifts, finite type
because the image of a finitely generated algebra is finitely generated — while étaleness is not,
which is why the general case is stated for unramifiedness only. There is no separate definition
of a maximal minor: the determinant of the rows selected by `rows : Fin n → Fin m` is
`jacobianDet` applied to the corresponding subsystem of the equations, and a repeated row makes
that determinant zero, so a determinant outside the prime selects the rows injectively of itself.

The geometric step takes the affine open to be the basic open of the chosen determinant inside the
zero scheme. The algebra structure of the sections over that basic open is transported from the
global sections along `AlgebraicGeometry.Scheme.ΓSpecIso`, which is also what identifies the
`appLE` map with the composite of the two structure maps.

Flatness is deduced from étaleness at the same point: an étale ring map is flat, and flatness
passes to the localizations at the two primes cut out by the point and its image, which are the
stalks of the structure morphism.

## References

* [Stacks Project, Tag 024Y](https://stacks.math.columbia.edu/tag/024Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial Algebra

universe u

namespace AlgebraicGeometry

namespace FullRankJacobianSituation

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The determinant of the Jacobian matrix of a square system of polynomial equations. -/
public noncomputable def jacobianDet (v : Fin n → MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  (Matrix.of fun i j => (MvPolynomial.pderiv j) (v i)).det

/-- The Jacobian of the naive pre-submersive presentation of a square polynomial quotient is the
class of the Jacobian determinant. -/
private theorem jacobian_naive (v : Fin n → MvPolynomial (Fin n) R) :
    (PreSubmersivePresentation.naive (v := v) id Function.injective_id).jacobian
      = Ideal.Quotient.mk (Ideal.span (Set.range v)) (jacobianDet v) := by
  classical
  have hval : (PreSubmersivePresentation.naive (v := v) id Function.injective_id).val
      = fun i => Ideal.Quotient.mk (Ideal.span (Set.range v)) (X i) :=
    funext fun i => by
      simp [PreSubmersivePresentation.naive_toPresentation, Presentation.naive_toGenerators]
  have halg : (aeval (R := R)
      (fun i => Ideal.Quotient.mk (Ideal.span (Set.range v)) (X i)) :
        MvPolynomial (Fin n) R →ₐ[R] _) = Ideal.Quotient.mkₐ R _ := by
    apply MvPolynomial.algHom_ext; intro i; simp
  have hM : (PreSubmersivePresentation.naive (v := v) id Function.injective_id).jacobiMatrix
      = (Matrix.of fun i j => (MvPolynomial.pderiv j) (v i)).transpose :=
    Matrix.ext fun i j => by
      rw [PreSubmersivePresentation.jacobiMatrix_naive]; rfl
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.Generators.algebraMap_apply, hval, hM, Matrix.det_transpose, jacobianDet]
  exact DFunLike.congr_fun halg _

/-- A localization of a square polynomial quotient away from the Jacobian determinant is étale
over the base ring. -/
public theorem etale_away_jacobianDet (v : Fin n → MvPolynomial (Fin n) R)
    {I : Ideal (MvPolynomial (Fin n) R)} (hI : I = Ideal.span (Set.range v)) (T : Type u)
    [CommRing T] [Algebra (MvPolynomial (Fin n) R ⧸ I) T]
    [IsLocalization.Away (Ideal.Quotient.mk I (jacobianDet v)) T] :
    RingHom.Etale
      ((algebraMap (MvPolynomial (Fin n) R ⧸ I) T).comp
        (algebraMap R (MvPolynomial (Fin n) R ⧸ I))) := by
  classical
  subst hI
  let d : MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v) :=
    Ideal.Quotient.mk (Ideal.span (Set.range v)) (jacobianDet v)
  let P : PreSubmersivePresentation R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v))
      (Fin n) (Fin n) := PreSubmersivePresentation.naive id Function.injective_id
  let Q : PreSubmersivePresentation (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) T
      Unit Unit := PreSubmersivePresentation.localizationAway T d
  let _ : Algebra R T :=
    ((algebraMap (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) T).comp
      (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)))).toAlgebra
  have _ : IsScalarTower R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hunit : IsUnit ((Q.comp P).jacobian) := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      show P.jacobian = d from jacobian_naive v,
      show Q.jacobian = algebraMap _ T d from
        PreSubmersivePresentation.localizationAway_jacobian (S := T) d,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (S := T) d).mul
      (IsLocalization.Away.algebraMap_isUnit (S := T) d)
  have _ : Algebra.IsStandardSmoothOfRelativeDimension 0 R T :=
    SubmersivePresentation.isStandardSmoothOfRelativeDimension
      { __ := Q.comp P, jacobian_isUnit := hunit } (by simp [Algebra.Presentation.dimension])
  exact (inferInstance : Algebra.Etale R T)

/-- A square matrix over a field whose rank is the number of its rows has nonzero
determinant. -/
private theorem det_ne_zero_of_rank_eq {K : Type*} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (h : M.rank = n) : M.det ≠ 0 := by
  intro hd
  obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hrank : Module.finrank K (LinearMap.range M.mulVecLin)
      + Module.finrank K (LinearMap.ker M.mulVecLin) = n := by
    simpa using LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hker : LinearMap.ker M.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp (by rw [Matrix.rank] at h; omega)
  exact hw (by
    simpa [hker] using (LinearMap.mem_ker (f := M.mulVecLin)).mpr (by simpa using hMw))

variable {m : ℕ}

/-- A matrix over a field whose rank is its number of columns has a selection of that many of its
rows with nonzero determinant. -/
private theorem exists_rows_det_ne_zero {K : Type*} [Field K] (M : Matrix (Fin m) (Fin n) K)
    (h : M.rank = n) : ∃ rows : Fin n → Fin m, (M.submatrix rows id).det ≠ 0 := by
  classical
  have hdim : Module.finrank K (Submodule.span K (Set.range M.row)) = n :=
    M.rank_eq_finrank_span_row.symm.trans h
  obtain ⟨w, hw, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range M.row)
  let e : Fin n ≃ Fin (Module.finrank K (Submodule.span K (Set.range M.row))) := finCongr hdim.symm
  refine ⟨fun i => Classical.choose (hw (e i)),
    Matrix.nonsingular_iff_det_ne_zero.1 (Matrix.Nonsingular.of_linearIndependent_row ?_)⟩
  have hrow : (M.submatrix (fun i => Classical.choose (hw (e i))) id).row = fun i => w (e i) :=
    funext fun i => Classical.choose_spec (hw (e i))
  rw [hrow]
  exact hli.comp e e.injective

/-- The Jacobian determinant of a system lies outside a prime if its image in the residue field
is nonzero. -/
private theorem jacobianDet_notMem_of_det_ne_zero (v : Fin n → MvPolynomial (Fin n) R)
    (P : Ideal (MvPolynomial (Fin n) R)) [P.IsPrime]
    (h : ((Matrix.of fun i j => (MvPolynomial.pderiv j) (v i)).map
      (algebraMap (MvPolynomial (Fin n) R) P.ResidueField)).det ≠ 0) :
    jacobianDet v ∉ P := fun hmem => h (by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Ideal.algebraMap_residueField_eq_zero.mpr hmem)

/-- In a full-rank Jacobian situation with as many equations as variables, the Jacobian
determinant does not lie in the selected prime. -/
private theorem jacobianDet_notMem_prime (S : FullRankJacobianSituation R n n) :
    jacobianDet S.equations ∉ S.prime := by
  have _ : S.prime.IsPrime := S.prime_isPrime
  exact jacobianDet_notMem_of_det_ne_zero _ _ (det_ne_zero_of_rank_eq _ S.jacobian_rank)

/-- Some choice of as many of the equations as there are variables has Jacobian determinant
outside the selected prime. -/
private theorem exists_rows_jacobianDet_notMem_prime (S : FullRankJacobianSituation R n m) :
    ∃ rows : Fin n → Fin m, jacobianDet (fun i => S.equations (rows i)) ∉ S.prime := by
  have _ : S.prime.IsPrime := S.prime_isPrime
  obtain ⟨rows, hrows⟩ := exists_rows_det_ne_zero _ S.jacobian_rank
  exact ⟨rows, jacobianDet_notMem_of_det_ne_zero _ _ hrows⟩

/-- The selected point lies in the basic open of the class of any polynomial outside the selected
prime. -/
private theorem point_mem_basicOpen (S : FullRankJacobianSituation R n m)
    {a : MvPolynomial (Fin n) R} (ha : a ∉ S.prime) :
    S.point ∈ S.zeroScheme.basicOpen
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸ S.equationIdeal))).inv
        (Ideal.Quotient.mk S.equationIdeal a)) := by
  have hle : S.equationIdeal ≤ S.prime :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr S.equations_mem_prime)
  rw [show S.zeroScheme.basicOpen
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸ S.equationIdeal))).inv
        (Ideal.Quotient.mk S.equationIdeal a))
      = PrimeSpectrum.basicOpen (Ideal.Quotient.mk S.equationIdeal a) from by
    simpa using basicOpen_eq_of_affine
      (R := .of (MvPolynomial (Fin n) R ⧸ S.equationIdeal)) (Ideal.Quotient.mk S.equationIdeal a)]
  refine (PrimeSpectrum.mem_basicOpen _ S.point).2 fun hmem => ?_
  exact ha ((Ideal.mem_quotient_iff_mem (I := S.equationIdeal) hle).1 hmem)

/-- On the basic open of a global section, the `appLE` map of the structure morphism is the
structure map of the polynomial quotient followed by the restriction. -/
private theorem appLE_basicOpen_eq (S : FullRankJacobianSituation R n m)
    (g : Γ(S.zeroScheme, ⊤)) :
    S.over.appLE ⊤ (S.zeroScheme.basicOpen g) le_top
      = (Scheme.ΓSpecIso (.of R)).hom
        ≫ CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ S.equationIdeal))
        ≫ (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸ S.equationIdeal))).inv
        ≫ S.zeroScheme.presheaf.map (homOfLE (S.zeroScheme.basicOpen_le g)).op := by
  have hnat := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ S.equationIdeal)))
  rw [show S.over.appLE ⊤ (S.zeroScheme.basicOpen g) le_top = S.over.appTop
        ≫ S.zeroScheme.presheaf.map (homOfLE (S.zeroScheme.basicOpen_le g)).op from rfl,
    show S.over.appTop = (Scheme.ΓSpecIso (.of R)).hom
        ≫ CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ S.equationIdeal))
        ≫ (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸ S.equationIdeal))).inv from by
      rw [← Iso.eq_comp_inv] at hnat; exact hnat]
  simp only [Category.assoc]

/-- A localization of a polynomial quotient away from the Jacobian determinant of as many of the
defining equations as there are variables is unramified over the base ring. -/
private theorem unramified_away_jacobianDet (v : Fin n → MvPolynomial (Fin n) R)
    {I : Ideal (MvPolynomial (Fin n) R)} (hI : Ideal.span (Set.range v) ≤ I) (D : Type u)
    [CommRing D] [Algebra (MvPolynomial (Fin n) R ⧸ I) D] [Algebra R D]
    [IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) D]
    [IsLocalization.Away (Ideal.Quotient.mk I (jacobianDet v)) D] :
    Algebra.Unramified R D := by
  classical
  let J : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range v)
  let d : MvPolynomial (Fin n) R ⧸ J := Ideal.Quotient.mk J (jacobianDet v)
  have hetale : RingHom.Etale
      ((algebraMap (MvPolynomial (Fin n) R ⧸ J) (Localization.Away d)).comp
        (algebraMap R (MvPolynomial (Fin n) R ⧸ J))) :=
    etale_away_jacobianDet v (I := J) rfl (Localization.Away d)
  rw [← IsScalarTower.algebraMap_eq, RingHom.etale_algebraMap] at hetale
  have : Algebra.Etale R (Localization.Away d) := hetale
  let φ : (MvPolynomial (Fin n) R ⧸ J) →ₐ[R] MvPolynomial (Fin n) R ⧸ I :=
    Ideal.Quotient.factorₐ R hI
  have : IsLocalization.Away (φ d) D :=
    show IsLocalization.Away (Ideal.Quotient.mk I (jacobianDet v)) D from inferInstance
  have hsurj : Function.Surjective (IsLocalization.Away.mapₐ (Localization.Away d) D φ d) :=
    IsLocalization.Away.mapₐ_surjective_of_surjective d (Ideal.Quotient.factor_surjective hI)
  exact ⟨Algebra.FormallyUnramified.of_surjective _ hsurj,
    Algebra.FiniteType.of_surjective _ hsurj⟩

/-- A polynomial quotient whose Jacobian has full rank at a prime is unramified over the base at
the corresponding point of its zero scheme. -/
@[stacks 024Y "unramified_point"]
public theorem unramifiedAt_over (S : FullRankJacobianSituation R n m) :
    UnramifiedAt S.over S.point := by
  classical
  obtain ⟨rows, hrows⟩ := S.exists_rows_jacobianDet_notMem_prime
  have hspan : Ideal.span (Set.range fun i => S.equations (rows i)) ≤ S.equationIdeal :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i => Ideal.subset_span ⟨rows i, rfl⟩)
  -- the class of the selected minor in the quotient, and the basic open it cuts out
  let d : MvPolynomial (Fin n) R ⧸ S.equationIdeal :=
    Ideal.Quotient.mk S.equationIdeal (jacobianDet fun i => S.equations (rows i))
  let g : Γ(S.zeroScheme, ⊤) :=
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸ S.equationIdeal))).inv d
  let _ : Algebra (MvPolynomial (Fin n) R ⧸ S.equationIdeal)
      Γ(S.zeroScheme, S.zeroScheme.basicOpen g) :=
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸ S.equationIdeal))).inv ≫
      S.zeroScheme.presheaf.map (homOfLE (S.zeroScheme.basicOpen_le g)).op).hom.toAlgebra
  have _ : IsLocalization.Away d Γ(S.zeroScheme, S.zeroScheme.basicOpen g) :=
    IsLocalization.of_ringEquiv_left (M₁ := Submonoid.powers g) (M₂ := Submonoid.powers d)
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸
        S.equationIdeal))).commRingCatIsoToRingEquiv.symm
      (Submonoid.map_powers _ d) fun _ => rfl
  -- the algebra structures carried by the structure maps and by `appLE`
  let _ : Algebra R Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom.toAlgebra
  let _ : Algebra Γ(Spec (.of R), ⊤) Γ(S.zeroScheme, S.zeroScheme.basicOpen g) :=
    (S.over.appLE ⊤ (S.zeroScheme.basicOpen g) le_top).hom.toAlgebra
  let _ : Algebra R Γ(S.zeroScheme, S.zeroScheme.basicOpen g) :=
    ((S.over.appLE ⊤ (S.zeroScheme.basicOpen g) le_top).hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  have _ : IsScalarTower R Γ(Spec (.of R), ⊤)
      Γ(S.zeroScheme, S.zeroScheme.basicOpen g) := IsScalarTower.of_algebraMap_eq' rfl
  have hmor : (Scheme.ΓSpecIso (.of R)).inv ≫
      S.over.appLE ⊤ (S.zeroScheme.basicOpen g) le_top
      = CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ S.equationIdeal))
        ≫ (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) R ⧸ S.equationIdeal))).inv
        ≫ S.zeroScheme.presheaf.map (homOfLE (S.zeroScheme.basicOpen_le g)).op := by
    rw [S.appLE_basicOpen_eq g, Iso.inv_hom_id_assoc]
  have _ : IsScalarTower R (MvPolynomial (Fin n) R ⧸ S.equationIdeal)
      Γ(S.zeroScheme, S.zeroScheme.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hmor)
  have _ : Algebra.Unramified R Γ(S.zeroScheme, S.zeroScheme.basicOpen g) :=
    unramified_away_jacobianDet (fun i => S.equations (rows i)) hspan
      Γ(S.zeroScheme, S.zeroScheme.basicOpen g)
  exact ⟨S.zeroScheme.basicOpen g, (isAffineOpen_top S.zeroScheme).basicOpen g,
    S.point_mem_basicOpen hrows, ⊤, isAffineOpen_top _, le_top,
    ⟨Algebra.FormallyUnramified.of_restrictScalars R Γ(Spec (.of R), ⊤)
      Γ(S.zeroScheme, S.zeroScheme.basicOpen g),
      Algebra.FiniteType.of_restrictScalars_finiteType R Γ(Spec (.of R), ⊤)
        Γ(S.zeroScheme, S.zeroScheme.basicOpen g)⟩⟩

/-- A full-rank Jacobian needs at least as many equations as variables. -/
@[stacks 024Y "enough_equations"]
public theorem numVariables_le_numEquations (S : FullRankJacobianSituation R n m) : n ≤ m :=
  have _ : S.prime.IsPrime := S.prime_isPrime
  S.jacobian_rank.symm.trans_le (Matrix.rank_le_height _)

/-- A polynomial quotient with a square, full-rank Jacobian at a prime is étale over the base at
the corresponding point. -/
@[stacks 024Y "square_etale"]
public theorem etaleAt_over_of_square (S : FullRankJacobianSituation R n m) (h : m = n) :
    EtaleAt S.over S.point := by
  classical
  subst h
  -- the distinguished element of the quotient and the basic open it cuts out
  let d : MvPolynomial (Fin m) R ⧸ S.equationIdeal :=
    Ideal.Quotient.mk S.equationIdeal (jacobianDet S.equations)
  let g : Γ(S.zeroScheme, ⊤) := (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m) R ⧸
    S.equationIdeal))).inv d
  let W : S.zeroScheme.Opens := S.zeroScheme.basicOpen g
  let res : Γ(S.zeroScheme, ⊤) ⟶ Γ(S.zeroScheme, W) :=
    S.zeroScheme.presheaf.map (homOfLE (S.zeroScheme.basicOpen_le g)).op
  let _ : Algebra (MvPolynomial (Fin m) R ⧸ S.equationIdeal) Γ(S.zeroScheme, W) :=
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin m) R ⧸ S.equationIdeal))).inv ≫ res).hom.toAlgebra
  have _ : IsLocalization.Away d Γ(S.zeroScheme, W) :=
    IsLocalization.of_ringEquiv_left (M₁ := Submonoid.powers g) (M₂ := Submonoid.powers d)
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m) R ⧸
        S.equationIdeal))).commRingCatIsoToRingEquiv.symm
      (Submonoid.map_powers _ d) fun _ => rfl
  refine ⟨W, (isAffineOpen_top S.zeroScheme).basicOpen g, ?_, ⊤,
    isAffineOpen_top _, le_top, ?_⟩
  · -- the selected point lies in the basic open of the Jacobian determinant
    exact S.point_mem_basicOpen S.jacobianDet_notMem_prime
  · -- the induced map on coordinate rings is the composite of the two structure maps
    have happ : S.over.appLE ⊤ W le_top
        = (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom
          ((algebraMap (MvPolynomial (Fin m) R ⧸ S.equationIdeal) Γ(S.zeroScheme, W)).comp
            (algebraMap R (MvPolynomial (Fin m) R ⧸ S.equationIdeal))) :=
      S.appLE_basicOpen_eq g
    rw [happ]
    exact (RingHom.Etale.respectsIso.cancel_left_isIso _ _).2
      (etale_away_jacobianDet S.equations (I := S.equationIdeal) rfl Γ(S.zeroScheme, W))

/-- A square system of equations whose Jacobian has full rank at a prime defines a morphism flat
at the corresponding point of its zero scheme. -/
@[stacks 024Y "square_flat"]
public theorem isFlatAt_over_of_square (S : FullRankJacobianSituation R n n) :
    IsFlatAt S.over.toLRSHom.toShHom S.point := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEtale⟩ := S.etaleAt_over_of_square rfl
  let _ := (S.over.appLE V U hUV).hom.toAlgebra
  let p := (hV.primeIdealOf ⟨S.over S.point, hUV hxU⟩).asIdeal
  let q := (hU.primeIdealOf ⟨S.point, hxU⟩).asIdeal
  have hqp : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU).1).symm⟩
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  exact show (S.over.stalkMap S.point).hom.Flat from
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso S.over V hV U hU hUV hxU)).mpr
      (RingHom.Flat.localRingHom
        ((RingHom.Etale.iff_flat_and_formallyUnramified.mp hEtale).1) q p hqp.1)

end FullRankJacobianSituation

end AlgebraicGeometry

end
