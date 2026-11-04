module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InternalHomOfProductOfUnits
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulDerivedDualNaive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.NaiveDualDifferential

/-!
# The naive dual of the Koszul complex, degreewise

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. In the
alternating Čech model that [Stacks, Tag 0A0E] is stated in, the degree-`p` term of
`AlgebraicGeometry.RingedSite.koszulPowerComplex` is the product of copies of `𝒪` indexed by the
`p`-element subsets of `Fin r`, so the degree-`n` term of its naive termwise dual is the internal
Hom of that product into `𝒪` **over the same index set**: no complement arises, and the dual term
collapses back onto the Koszul term itself.

This file assembles the two inputs — the degreewise collapse
`AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso` of [Stacks, Tag 08DM], which turns the
degree-`n` term of `SheafHom^•(K, 𝒪[0])` into `𝓗om(K^{-n}, 𝒪)`, and
`AlgebraicGeometry.RingedSite.internalHomPiUnitIso`, which turns the internal Hom of a finite
product of copies of `𝒪` into that product again — into the degreewise identification

`SheafHom^n(K(𝒪, f^{m+1}), 𝒪[0]) ≅ K(𝒪, f^{m+1})^{-n}`,

and then into an isomorphism of complexes, and finally of *towers* of complexes: the dual
differential is the transpose of the Koszul differential, which is the Koszul contraction, and
the transition map of the Koszul tower is its own transpose, being diagonal.

## Main definitions

* `AlgebraicGeometry.RingedSite.koszulNaiveDualDegreeIso`: **the degree-`n` term of the naive
  dual of the Koszul complex is its degree-`(-n)` term.**
* `AlgebraicGeometry.RingedSite.koszulNaiveDualD`: the dual differential read through that
  identification — the transpose of the Koszul differential, up to the sign `(-1)^n`.
* `AlgebraicGeometry.RingedSite.koszulNaiveDualComplex`: the Koszul terms with that
  differential, as a complex.
* `AlgebraicGeometry.RingedSite.koszulNaiveDualComplexIso`: **the naive dual of the Koszul
  complex IS that complex**, as an isomorphism of complexes.
* `AlgebraicGeometry.RingedSite.koszulNaiveDualComplexMap`: the transition map of the tower of
  naive duals.

## Main results

* `AlgebraicGeometry.RingedSite.koszulNaiveDualDegreeIso_hom_comp_π`: the characterising clause
  — the component at a subset `S` is the degree projection of the Hom complex followed by
  evaluation against the inclusion of the factor indexed by `S`.
* `AlgebraicGeometry.RingedSite.d_comp_koszulNaiveDualDegreeIso_hom`: the degreewise
  identification carries the differential of the naive dual to `koszulNaiveDualD`.
* `AlgebraicGeometry.RingedSite.koszulNaiveDualComplexIso_hom_f` and
  `koszulNaiveDualComplexMap_f`: the characterising clauses of the two data above.
* `AlgebraicGeometry.RingedSite.homMap_comp_koszulNaiveDualComplexIso_hom`: **the degreewise
  identifications are an isomorphism of towers**, which is the shape [Stacks, Tag 0BLX]
  consumes.

## Implementation notes

No transport is needed to see the Koszul term as a product of copies of `𝒪`: it is
`CategoryTheory.AlternatingCech.term` of the constant functor at `𝒪`, which is that product
definitionally, exactly as in
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_koszulPowerComplex_X`.

The differential of the naive dual is `AlgebraicGeometry.RingedSite`'s
`d_comp_homStructureSheafDegreeIso_hom`: `(-1)^{n+1}` times precomposition with the differential
of the Koszul complex. Turning that into the contraction differential on the right-hand side of
the isomorphism above is the transposition of a matrix of endomorphisms of `𝒪` through
`internalHomPiUnitIso`, which is
`AlgebraicGeometry.RingedSite.internalHomPre_comp_internalHomPiUnitIso_hom`.

`koszulNaiveDualD` is not shown to square to zero by a computation in the Koszul index
combinatorics. The differential of a complex does square to zero and the degreewise
identification is an isomorphism, so `d_comp_koszulNaiveDualDegreeIso_hom` transports the
relation; this is why that lemma is proved before `koszulNaiveDualComplex` exists.

**Why the pastings are done against variables.** The degreewise collapse lands at
`internalHomSheaf X (E.X (-n)) 𝒪` while `internalHomPiUnitIso` starts from
`internalHomSheaf X (∏ 𝒪) 𝒪`; those are the same sheaf of modules only after unfolding
`koszulPowerComplex`, which is not reducible, so a composite built around both is not
type-correct at the transparency at which `rw` rebuilds a term. The private `zsmulPasting` and
`pasting` state the rearrangement between variables, where it is, and the use sites apply them
as terms, which elaborate at default transparency.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (m : ℕ)

/-- **The degree-`n` term of the naive termwise dual of the Koszul complex is its degree-`(-n)`
term.** The degreewise collapse of [Stacks, Tag 08DM] identifies it with `𝓗om(K^{-n}, 𝒪)`, and
`K^{-n}` is the product of copies of `𝒪` indexed by the subsets of `Fin r` of cardinality `-n`,
so internal Hom out of it into `𝒪` is that product again. -/
def koszulNaiveDualDegreeIso (n : ℤ) :
    (sheafHomComplex X (koszulPowerComplex X f m) (structureSheafComplex X)).obj.X n ≅
      AlternatingCech.term (koszulPowerFunctor X f m) (-n) :=
  homStructureSheafDegreeIso X (koszulPowerComplex X f m)
      (finite_support_koszulPowerComplex X f m) n ≪≫
    internalHomPiUnitIso X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (AlternatingCech.Idx r (-n))

/-- **The characterising clause of `koszulNaiveDualDegreeIso`.** Its component at a subset `S` of
cardinality `-n` is the degreewise collapse followed by precomposition with the inclusion of the
factor indexed by `S` and the trivialisation `𝓗om(𝒪, 𝒪) ≅ 𝒪`. -/
@[reassoc]
theorem koszulNaiveDualDegreeIso_hom_comp_π (n : ℤ) (S : AlternatingCech.Idx r (-n)) :
    (koszulNaiveDualDegreeIso X f m n).hom ≫
        Pi.π (fun _ : AlternatingCech.Idx r (-n) =>
          SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) S =
      (homStructureSheafDegreeIso X (koszulPowerComplex X f m)
          (finite_support_koszulPowerComplex X f m) n).hom ≫
        internalHomPre X (C := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (piConstι (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) S) ≫
          (Stacks.SheafOfModules.InternalHom.unitSheafInternalHomIso X
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (homStructureSheafDegreeIso X (koszulPowerComplex X f m)
        (finite_support_koszulPowerComplex X f m) n).hom ≫ z)
      (internalHomPiUnitIso_hom_comp_π X
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (AlternatingCech.Idx r (-n)) S))

/-! ### The naive dual as a complex -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The pasting of the two inputs of `d_comp_koszulNaiveDualDegreeIso_hom`, with every morphism
a variable. Abstracting them is what makes the associativity rearrangements go through: the
degreewise collapse lands at `internalHomSheaf X (E.X (-n)) 𝒪` while `internalHomPiUnitIso`
starts from `internalHomSheaf X (∏ 𝒪) 𝒪`, and those two sheaves of modules are the same only up
to unfolding `AlgebraicGeometry.RingedSite.koszulPowerComplex`, so a composite built around both
is not type-correct at the transparency at which `rw` rebuilds a term. -/
private lemma zsmulPasting
    {A B C P Q R : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (u : ℤˣ)
    (dd : A ⟶ B) (c₁ : B ⟶ C) (b₁ : C ⟶ R) (c₀ : A ⟶ P) (b₀ : P ⟶ Q) (g : P ⟶ C) (t : Q ⟶ R)
    (h₁ : dd ≫ c₁ = u • (c₀ ≫ g)) (h₂ : g ≫ b₁ = b₀ ≫ t) :
    dd ≫ c₁ ≫ b₁ = (c₀ ≫ b₀) ≫ (u • t) := by
  rw [← Category.assoc, h₁]
  simp only [Units.smul_def]
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc, h₂, Category.assoc]

/-- **The differential of the naive dual of the Koszul complex**, read through the degreewise
identification `koszulNaiveDualDegreeIso`: `(-1)^{n'}` times the transpose of the Koszul
differential. The transpose of a matrix of multiplications by monomials in the `f_i` is the
Koszul contraction. -/
def koszulNaiveDualD (n n' : ℤ) :
    AlternatingCech.term (koszulPowerFunctor X f m) (-n) ⟶
      AlternatingCech.term (koszulPowerFunctor X f m) (-n') :=
  n'.negOnePow • piConstTranspose (J := AlternatingCech.Idx r (-n'))
    (K := AlternatingCech.Idx r (-n))
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((koszulPowerComplex X f m).d (-n') (-n))

/-- **The degreewise identification carries the differential of the naive dual to
`koszulNaiveDualD`.** This is `d_comp_homStructureSheafDegreeIso_hom`, which says the dual
differential is `(-1)^{n'}` times precomposition with the Koszul differential, followed by
`internalHomPre_comp_internalHomPiUnitIso_hom`, which says that `internalHomPiUnitIso`
transposes that matrix. -/
theorem d_comp_koszulNaiveDualDegreeIso_hom (n n' : ℤ) (hnn' : n + 1 = n') :
    (sheafHomComplex X (koszulPowerComplex X f m) (structureSheafComplex X)).obj.d n n' ≫
        (koszulNaiveDualDegreeIso X f m n').hom =
      (koszulNaiveDualDegreeIso X f m n).hom ≫ koszulNaiveDualD X f m n n' := by
  exact zsmulPasting X _ _ _ _ _ _ _ _
    (d_comp_homStructureSheafDegreeIso_hom X (koszulPowerComplex X f m)
      (finite_support_koszulPowerComplex X f m) n n' hnn')
    (internalHomPre_comp_internalHomPiUnitIso_hom X (AlternatingCech.Idx r (-n'))
      (AlternatingCech.Idx r (-n)) ((koszulPowerComplex X f m).d (-n') (-n)))

/-- The transposed differential squares to zero, since the differential of the naive dual does
and the degreewise identification is an isomorphism. -/
theorem koszulNaiveDualD_comp_koszulNaiveDualD (n : ℤ) :
    koszulNaiveDualD X f m n (n + 1) ≫ koszulNaiveDualD X f m (n + 1) (n + 1 + 1) = 0 := by
  refine (Iso.cancel_iso_hom_left (koszulNaiveDualDegreeIso X f m n) _ _).mp ?_
  rw [comp_zero, ← Category.assoc,
    ← d_comp_koszulNaiveDualDegreeIso_hom X f m n (n + 1) rfl, Category.assoc,
    ← d_comp_koszulNaiveDualDegreeIso_hom X f m (n + 1) (n + 1 + 1) rfl, ← Category.assoc,
    HomologicalComplex.d_comp_d, zero_comp]

/-- **The naive termwise dual of the Koszul complex, as a complex on the Koszul terms
themselves**: in degree `n` it is the degree-`(-n)` Koszul term, with the transposed Koszul
differential `koszulNaiveDualD`. -/
def koszulNaiveDualComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  CochainComplex.of (fun n => AlternatingCech.term (koszulPowerFunctor X f m) (-n))
    (fun n => koszulNaiveDualD X f m n (n + 1)) (koszulNaiveDualD_comp_koszulNaiveDualD X f m)

/-- The degree-`n` term of `koszulNaiveDualComplex` is the Koszul term in degree `-n`. -/
@[simp]
theorem koszulNaiveDualComplex_X (n : ℤ) :
    (koszulNaiveDualComplex X f m).X n = AlternatingCech.term (koszulPowerFunctor X f m) (-n) :=
  rfl

/-- The differential of `koszulNaiveDualComplex` from degree `n` to degree `n + 1` is
`koszulNaiveDualD`. -/
@[simp]
theorem koszulNaiveDualComplex_d (n : ℤ) :
    (koszulNaiveDualComplex X f m).d n (n + 1) = koszulNaiveDualD X f m n (n + 1) :=
  CochainComplex.of_d (fun p => AlternatingCech.term (koszulPowerFunctor X f m) (-p))
    (fun p => koszulNaiveDualD X f m p (p + 1)) n

/-- **The naive termwise dual of the Koszul complex IS the Koszul complex with the transposed
differential**, as an isomorphism of complexes: the degreewise identifications
`koszulNaiveDualDegreeIso` commute with the differentials by
`d_comp_koszulNaiveDualDegreeIso_hom`. -/
def koszulNaiveDualComplexIso :
    (sheafHomComplex X (koszulPowerComplex X f m) (structureSheafComplex X)).obj ≅
      koszulNaiveDualComplex X f m :=
  HomologicalComplex.Hom.isoOfComponents (fun n => koszulNaiveDualDegreeIso X f m n)
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      rw [koszulNaiveDualComplex_d]
      exact (d_comp_koszulNaiveDualDegreeIso_hom X f m i (i + 1) rfl).symm)

/-- The degree-`n` component of `koszulNaiveDualComplexIso` is the degreewise identification
`koszulNaiveDualDegreeIso`. -/
@[simp]
theorem koszulNaiveDualComplexIso_hom_f (n : ℤ) :
    (koszulNaiveDualComplexIso X f m).hom.f n = (koszulNaiveDualDegreeIso X f m n).hom :=
  rfl

/-- The degree-`n` component of the inverse of `koszulNaiveDualComplexIso` is the inverse of the
degreewise identification `koszulNaiveDualDegreeIso`. -/
@[simp]
theorem koszulNaiveDualComplexIso_inv_f (n : ℤ) :
    (koszulNaiveDualComplexIso X f m).inv.f n = (koszulNaiveDualDegreeIso X f m n).inv :=
  rfl

/-! ### The tower -/

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The pasting of the two inputs of `homMap_comp_koszulNaiveDualDegreeIso_hom`, with every
morphism a variable, for the reason recorded at `zsmulPasting`. -/
private lemma pasting
    {A B C P Q R : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (dd : A ⟶ B) (c₁ : B ⟶ C) (b₁ : C ⟶ R) (c₀ : A ⟶ P) (b₀ : P ⟶ Q) (g : P ⟶ C) (t : Q ⟶ R)
    (h₁ : dd ≫ c₁ = c₀ ≫ g) (h₂ : g ≫ b₁ = b₀ ≫ t) :
    dd ≫ c₁ ≫ b₁ = (c₀ ≫ b₀) ≫ t := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **The degreewise identification is compatible with the transition map of the Koszul
tower.** Dualizing `koszulPowerComplexMap` is `homMap` against the identity of `𝒪[0]`, and in
degree `n` the identification carries it to the degree-`(-n)` component of the transition map of
the Koszul system itself: that component is a diagonal matrix, hence its own transpose
(`CategoryTheory.Limits.piConstTranspose_piMap`).

This is what makes the degreewise identifications an isomorphism of *towers*, which is the shape
[Stacks, Tag 0BLX] consumes. -/
theorem homMap_comp_koszulNaiveDualDegreeIso_hom (n : ℤ) :
    (homMap X (koszulPowerComplexMap X f m) (𝟙 (structureSheafComplex X))).f n ≫
        (koszulNaiveDualDegreeIso X f m n).hom =
      (koszulNaiveDualDegreeIso X f (m + 1) n).hom ≫
        AlternatingCech.mapX (koszulPowerTrans X f m) (-n) := by
  have htr : piConstTranspose (J := AlternatingCech.Idx r (-n))
      (K := AlternatingCech.Idx r (-n))
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((koszulPowerComplexMap X f m).f (-n)) =
      AlternatingCech.mapX (koszulPowerTrans X f m) (-n) :=
    piConstTranspose_piMap (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      fun S : AlternatingCech.Idx r (-n) => (koszulPowerTrans X f m).app S.1
  have h₂ := (internalHomPre_comp_internalHomPiUnitIso_hom X (AlternatingCech.Idx r (-n))
      (AlternatingCech.Idx r (-n)) ((koszulPowerComplexMap X f m).f (-n))).trans
    (congrArg (fun z =>
      (internalHomPiUnitIso X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (AlternatingCech.Idx r (-n))).hom ≫ z) htr)
  exact pasting X _ _ _ _ _ _ _
    (homStructureSheafDegreeIso_naturality X (koszulPowerComplex X f (m + 1))
      (koszulPowerComplex X f m) (finite_support_koszulPowerComplex X f (m + 1))
      (finite_support_koszulPowerComplex X f m) (koszulPowerComplexMap X f m) n) h₂

/-- **The transition map of the tower of naive duals.** It is the dual of
`koszulPowerComplexMap` conjugated through `koszulNaiveDualComplexIso`; its degree-`n` component
is the degree-`(-n)` component of the transition map of the Koszul system, by
`koszulNaiveDualComplexMap_f`. -/
def koszulNaiveDualComplexMap :
    koszulNaiveDualComplex X f (m + 1) ⟶ koszulNaiveDualComplex X f m :=
  (koszulNaiveDualComplexIso X f (m + 1)).inv ≫
    homMap X (koszulPowerComplexMap X f m) (𝟙 (structureSheafComplex X)) ≫
      (koszulNaiveDualComplexIso X f m).hom

/-- **The characterising clause of `koszulNaiveDualComplexMap`**: in degree `n` it is the
degree-`(-n)` component of the transition map of the Koszul system. -/
@[simp]
theorem koszulNaiveDualComplexMap_f (n : ℤ) :
    (koszulNaiveDualComplexMap X f m).f n =
      AlternatingCech.mapX (koszulPowerTrans X f m) (-n) := by
  have h : (koszulNaiveDualDegreeIso X f (m + 1) n).inv ≫
      ((homMap X (koszulPowerComplexMap X f m) (𝟙 (structureSheafComplex X))).f n ≫
        (koszulNaiveDualDegreeIso X f m n).hom) =
      AlternatingCech.mapX (koszulPowerTrans X f m) (-n) := by
    rw [homMap_comp_koszulNaiveDualDegreeIso_hom]
    exact Iso.inv_hom_id_assoc _ _
  exact h

/-- **The naive dual of the Koszul tower IS the Koszul tower with the transposed
differentials.** The isomorphisms of complexes `koszulNaiveDualComplexIso` commute with the
transition maps, so they are an isomorphism of towers; this is the statement
[Stacks, Tag 0BLX] consumes. -/
theorem homMap_comp_koszulNaiveDualComplexIso_hom :
    homMap X (koszulPowerComplexMap X f m) (𝟙 (structureSheafComplex X)) ≫
        (koszulNaiveDualComplexIso X f m).hom =
      (koszulNaiveDualComplexIso X f (m + 1)).hom ≫ koszulNaiveDualComplexMap X f m :=
  (Iso.hom_inv_id_assoc (koszulNaiveDualComplexIso X f (m + 1))
    (homMap X (koszulPowerComplexMap X f m) (𝟙 (structureSheafComplex X)) ≫
      (koszulNaiveDualComplexIso X f m).hom)).symm

end AlgebraicGeometry.RingedSite

end
