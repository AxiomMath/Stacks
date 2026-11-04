module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.HomBicomplex
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.Complex

/-!
# The Hom bicomplex of the Koszul complex of an algebraic space

Let `X` be an algebraic space over a scheme `S`, let `U` be an algebraic space étale over `X`
and let `F` be an abelian sheaf on the spaces-étale site of `X`.  Writing `K^•` for the Koszul
complex `K^p = ∧^{p+1} j_{U!} ℤ` and `F ⟶ I^•` for a resolution of `F`, this file builds the
bicomplex `Hom(K^p, I^q)` and the canonical map from the alternating Čech complex
`Č^•_alt(f, F) = Hom(K^•, F)` into its total complex.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.koszulCochainComplex` is the Koszul complex read in
  nonpositive cochain degrees, `K^p` sitting in degree `-p`.
* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechCochainComplex` is the complex
  `Hom(K^•, G)` of abelian groups, indexed by `ℤ`.
* `AlgebraicGeometry.Space.SpacesEtale.koszulHomBicomplex` is the bicomplex whose `(p, q)` term
  is `Hom(K^p, I^q)`.
* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechToTotal` is the canonical map
  `Hom(K^•, F) ⟶ Tot(Hom(K^•, I^•))` attached to a map `F ⟶ I^0` killed by `I^0 ⟶ I^1`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechCochainComplexXIsoAlternatingCech`
  identifies the terms of `Hom(K^•, G)` in nonnegative degrees with the terms of the
  alternating Čech complex of Stacks 0724.
* `AlgebraicGeometry.Space.SpacesEtale.koszulHomBicomplex_diagonalFinite` and
  `AlgebraicGeometry.Space.SpacesEtale.isZero_koszulHomBicomplex_X_X_of_neg`: the diagonals of
  the bicomplex are finite and it vanishes in negative Koszul degrees, so its total complex
  exists; these are the two inputs to Stacks 0133 that do not ask `K^•` to be a resolution.

## Implementation notes

The Hom bicomplex is `CochainComplex.homBicomplex`, whose `(p, q)` term is `Hom(K^{-p}, I^q)`
for a cochain complex `K`; the Koszul complex is a chain complex indexed by `ℕ`, so it is first
extended by zero to the nonpositive cochain degrees, which puts `K^p` in degree `-p` and makes
the first index of the bicomplex the Koszul degree.  The complex `Hom(K^•, G)` is built from the
same opposite complex, so that its term in degree `p` is the `(p, q)` term of the bicomplex on
the nose for a sheaf `G` appearing as `I^q`.

The complex `Hom(K^•, G)` is the alternating Čech complex of Stacks 0724 reindexed by `ℤ`: both
have `Hom(K^p, G)` in degree `p` and precomposition with the differential of `K^•` as
differential.  Only the identification of the terms is proved, by
`alternatingCechCochainComplexXIsoAlternatingCech`; the identification of the two complexes
would in addition have to move the differential across the extension of `K^•` by zero and the
reindexing by negation of `CochainComplex.opEquivalence`.

Stacks 0725 asserts more than is proved here: that the map built here becomes, in the derived
category, a map to `RΓ(X, F)`.  That rests on the augmentation `K^• ⟶ ℤ[0]` of Stacks 0723 being
a quasi-isomorphism — equivalently, on the rows `Hom(K^•, I^q)` being exact in positive degrees
with `H^0` the sections of `I^q` — which is not proved here and is the remaining input to
Stacks 0133.  The two hypotheses of Stacks 0133 that do not depend on it are proved.

## References

* [Stacks, Tag 0725](https://stacks.math.columbia.edu/tag/0725)
* [Stacks, Tag 0724](https://stacks.math.columbia.edu/tag/0724)
* [Stacks, Tag 0723](https://stacks.math.columbia.edu/tag/0723)
* [Stacks, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The Koszul complex in nonpositive cochain degrees -/

/-- The Koszul complex `K^•` of `U`, read as a cochain complex indexed by `ℤ` with `K^p` in
degree `-p` and zero in the positive degrees. -/
def koszulCochainComplex (U : SpacesEtale B S hS X) :
    CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ :=
  (koszulComplex B S hS X U).extend ComplexShape.embeddingDownNat

/-- The term of `K^•` read in cochain degree `-p` is `K^p`. -/
def koszulCochainComplexXIso (U : SpacesEtale B S hS X) (p : ℕ) :
    (koszulCochainComplex B S hS X U).X (-(p : ℤ)) ≅ (koszulComplex B S hS X U).X p :=
  HomologicalComplex.extendXIso _ _ (by simp)

/-- `K^•` read in cochain degrees vanishes in the positive degrees. -/
theorem isZero_koszulCochainComplex_X (U : SpacesEtale B S hS X) (p : ℤ) (hp : 0 < p) :
    IsZero ((koszulCochainComplex B S hS X U).X p) :=
  HomologicalComplex.isZero_extend_X _ _ _ fun n hn => by
    simp only [ComplexShape.embeddingDownNat_f] at hn; omega

/-- `K^•` read in cochain degrees is strictly concentrated in degrees `≤ 0`. -/
instance (U : SpacesEtale B S hS X) :
    CochainComplex.IsStrictlyLE (koszulCochainComplex B S hS X U) 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE
    ((koszulComplex B S hS X U).extend ComplexShape.embeddingDownNat) 0)

/-- `K^•` read in cochain degrees is bounded above. -/
theorem koszulCochainComplex_minus (U : SpacesEtale B S hS X) :
    CochainComplex.minus _ (koszulCochainComplex B S hS X U) :=
  (CochainComplex.minus_iff _).2 ⟨0, inferInstance⟩

/-- The opposite complex of `K^•`, the contravariant argument of the Hom bicomplex: its term in
degree `p` is `op K^p`. -/
abbrev koszulOpComplex (U : SpacesEtale B S hS X) :
    CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})ᵒᵖ ℤ :=
  (CochainComplex.opEquivalence (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})).functor.obj
    (op (koszulCochainComplex B S hS X U))

/-! ### The alternating Čech complex, indexed by `ℤ` -/

/-- The complex `Hom(K^•, G)` of abelian groups, indexed by `ℤ`: its term in degree `p` is
`Hom(K^p, G)` and its differential is precomposition with the differential of `K^•`.  For `G`
an abelian sheaf on the spaces-étale site of `X` this is the alternating Čech complex of
Stacks 0724, read in integer degrees. -/
def alternatingCechCochainComplex (U : SpacesEtale B S hS X)
    (G : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  (((preadditiveCoyoneda
      (C := Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})).flip.obj G).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (koszulOpComplex B S hS X U)

/-- The term of `Hom(K^•, G)` in degree `-p` is `Hom(K^p, G)`. -/
def alternatingCechCochainComplexXIso (U : SpacesEtale B S hS X)
    (G : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (alternatingCechCochainComplex B S hS X U G).X (p : ℤ) ≅
      AddCommGrpCat.of ((koszulComplex B S hS X U).X p ⟶ G) :=
  ((preadditiveCoyoneda
      (C := Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})).flip.obj G).mapIso
    (koszulCochainComplexXIso B S hS X U p).symm.op

/-- The term of `Hom(K^•, G)` in degree `p` is the term `Hom(K^p, G)` of the alternating Čech
complex of Stacks 0724 in degree `p`. -/
def alternatingCechCochainComplexXIsoAlternatingCech (U : SpacesEtale B S hS X)
    (G : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    (alternatingCechCochainComplex B S hS X U G).X (p : ℤ) ≅
      (alternatingCechComplex B S hS X U G).X p :=
  (alternatingCechCochainComplexXIso B S hS X U G p).trans
    (eqToIso (alternatingCechComplex_X B S hS X U G p).symm)

/-! ### The Hom bicomplex -/

/-- The bicomplex `Hom(K^p, I^q)` attached to the Koszul complex of `U` and a cochain complex
`I^•` of abelian sheaves: its `(p, q)` term is `Hom(K^p, I^q)`, the differential in `p` is
precomposition with the differential of `K^•` and the differential in `q` is postcomposition
with the differential of `I^•`. -/
abbrev koszulHomBicomplex (U : SpacesEtale B S hS X)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CochainComplex.homBicomplex (koszulCochainComplex B S hS X U) I

/-- The bicomplex `Hom(K^p, I^q)` vanishes in negative Koszul degrees. -/
theorem isZero_koszulHomBicomplex_X_X_of_neg (U : SpacesEtale B S hS X)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) (p q : ℤ)
    (hp : p < 0) : IsZero (((koszulHomBicomplex B S hS X U I).X p).X q) :=
  CochainComplex.isZero_homBicomplex_X_X_of_isZero_left _ _ _ _
    (isZero_koszulCochainComplex_X B S hS X U (-p) (by omega))

/-- Each diagonal of `Hom(K^p, I^q)` carries only finitely many nonzero terms, for `I^•`
bounded below. -/
theorem koszulHomBicomplex_diagonalFinite (U : SpacesEtale B S hS X)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ)
    (hI : CochainComplex.plus _ I) (n : ℤ) :
    {pq : ℤ × ℤ |
      ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n ∧
        ¬ IsZero (((koszulHomBicomplex B S hS X U I).X pq.1).X pq.2)}.Finite :=
  CochainComplex.homBicomplex_finite_diagonals _ _
    (koszulCochainComplex_minus B S hS X U) hI n

/-- The total complex of `Hom(K^p, I^q)` exists when `I^•` is bounded below. -/
theorem koszulHomBicomplex_hasTotal (U : SpacesEtale B S hS X)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ)
    (hI : CochainComplex.plus _ I) :
    (koszulHomBicomplex B S hS X U I).HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _
    (koszulHomBicomplex_diagonalFinite B S hS X U I hI)

/-! ### The canonical map into the total complex -/

variable (U : SpacesEtale B S hS X)
    {F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}}
    {I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ}

/-- Postcomposition with a map `ε : F ⟶ I^0`, read as a map from the degree `p` term
`Hom(K^p, F)` of the alternating Čech complex to the `(p, 0)` term `Hom(K^p, I^0)` of the Hom
bicomplex. -/
def alternatingCechToBicomplexRowZero (ε : F ⟶ I.X 0) (p : ℤ) :
    (alternatingCechCochainComplex B S hS X U F).X p ⟶
      ((koszulHomBicomplex B S hS X U I).X p).X 0 :=
  (preadditiveCoyoneda.obj ((koszulOpComplex B S hS X U).X p)).map ε

/-- Postcomposition with `ε : F ⟶ I^0` is killed by the differential `I^0 ⟶ I^1` as soon as
`ε` is. -/
theorem alternatingCechToBicomplexRowZero_comp_d (ε : F ⟶ I.X 0) (hε : ε ≫ I.d 0 1 = 0)
    (p q : ℤ) (hq : q = 1) :
    alternatingCechToBicomplexRowZero B S hS X U ε p ≫
      ((koszulHomBicomplex B S hS X U I).X p).d 0 q = 0 := by
  subst hq
  have h : (preadditiveCoyoneda.obj ((koszulOpComplex B S hS X U).X p)).map ε ≫
      (preadditiveCoyoneda.obj ((koszulOpComplex B S hS X U).X p)).map (I.d 0 1) = 0 := by
    rw [← Functor.map_comp, hε, Functor.map_zero]
  exact h

/-- Postcomposition with `ε : F ⟶ I^0` commutes with precomposition with the differential of
`K^•`. -/
theorem alternatingCechToBicomplexRowZero_naturality (ε : F ⟶ I.X 0) (p q : ℤ) :
    alternatingCechToBicomplexRowZero B S hS X U ε p ≫
        ((koszulHomBicomplex B S hS X U I).d p q).f 0 =
      (alternatingCechCochainComplex B S hS X U F).d p q ≫
        alternatingCechToBicomplexRowZero B S hS X U ε q :=
  (preadditiveCoyoneda.map ((koszulOpComplex B S hS X U).d p q)).naturality ε

/-- The canonical map from the complex `Hom(K^•, F)` into the total complex of
`Hom(K^•, I^•)`, attached to a map `ε : F ⟶ I^0` whose composite with `I^0 ⟶ I^1` vanishes: in
degree `p` it is postcomposition with `ε` followed by the inclusion of the summand
`Hom(K^p, I^0)`. -/
def alternatingCechToTotal (ε : F ⟶ I.X 0) (hε : ε ≫ I.d 0 1 = 0)
    [(koszulHomBicomplex B S hS X U I).HasTotal (ComplexShape.up ℤ)] :
    alternatingCechCochainComplex B S hS X U F ⟶
      (koszulHomBicomplex B S hS X U I).total (ComplexShape.up ℤ) where
  f p := alternatingCechToBicomplexRowZero B S hS X U ε p ≫
    (koszulHomBicomplex B S hS X U I).ιTotal (ComplexShape.up ℤ) p 0 p (by simp)
  comm' p q (hpq : p + 1 = q) := by
    subst hpq
    rw [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ _ p 0 p (add_zero p),
      Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul]
    simp only [← Category.assoc]
    rw [alternatingCechToBicomplexRowZero_comp_d B S hS X U ε hε p (0 + 1) (zero_add 1),
      Limits.zero_comp, smul_zero, add_zero,
      alternatingCechToBicomplexRowZero_naturality B S hS X U ε p (p + 1)]

/-- The components of the comparison map: postcomposition with `ε : F ⟶ I^0`, followed by the
inclusion of the summand `Hom(K^p, I^0)` of the total complex. -/
@[simp]
theorem alternatingCechToTotal_f (ε : F ⟶ I.X 0) (hε : ε ≫ I.d 0 1 = 0)
    [(koszulHomBicomplex B S hS X U I).HasTotal (ComplexShape.up ℤ)] (p : ℤ) :
    (alternatingCechToTotal B S hS X U ε hε).f p =
      alternatingCechToBicomplexRowZero B S hS X U ε p ≫
        (koszulHomBicomplex B S hS X U I).ιTotal (ComplexShape.up ℤ) p 0 p (by simp) :=
  rfl

end AlgebraicGeometry.Space.SpacesEtale

end
