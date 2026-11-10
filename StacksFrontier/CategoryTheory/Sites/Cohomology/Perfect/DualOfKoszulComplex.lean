module

public import StacksFrontier.Algebra.Homology.SignedDualComplex
public import StacksFrontier.Algebra.Homology.SignedDualComplexFunctorial
public import StacksFrontier.Algebra.Homology.DualComplexOfSignedMateDuals
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualComplexKFlat
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPerfect
public import StacksCore.CategoryTheory.Monoidal.Rigid.Biproducts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dual of the Koszul complex is a Koszul complex in degrees `-r, …, 0`

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let

`K_n = K(𝒪, f_1^{n+1}, …, f_r^{n+1})`

be the Koszul complex of `AlgebraicGeometry.RingedSite.koszulPowerComplex`, in the grading of
[Stacks, Tag 0913] in which its degree-`p` term is the product `∏_{|S| = p} 𝒪` of copies of `𝒪`
indexed by the subsets of `{1, …, r}` of cardinality `p`. This file identifies its dual with the
*same* terms read in the opposite degrees:

* the dual complex `𝑆heafHom^•(K_n, 𝒪)` of [Stacks, Tag 0FPR], whose degree-`j` term is the dual
  sheaf of `∏_{|S| = -j} 𝒪`, is isomorphic to the complex whose degree-`j` term is
  `∏_{|S| = -j} 𝒪` itself, which is concentrated in degrees `-r, …, 0`
  (`AlgebraicGeometry.RingedSite.dualComplexKoszulPowerComplexIso`);
* hence the derived dual `K_n^∨ = R𝑆heafHom_𝒪(K_n, 𝒪)` of [Stacks, Tag 08JD] is the image in
  `D(𝒪)` of that complex (`AlgebraicGeometry.RingedSite.derivedDualKoszulPowerComplexIso`) —
  the `K_n` of the displayed formula of [Stacks, Tag 0A0E].

The engine is a general statement about `CochainComplex.dualComplex`, which is in this file for
want of a place beside the construction itself: **the dual complex does not depend on the choice
of degreewise duals.** `CochainComplex.dualComplex K D q` is built from a family `D : ℤ → C` of
degreewise duals of the terms of `K` with pairings `q`, and its differential is the signed
transpose of the differential of `K`. Two such families give *isomorphic* complexes, by the
degreewise uniqueness isomorphism of duals, and no compatibility between the families has to be
assumed: the mate of a composite is the composite of the mates, so the square

```
D^{-(n+1)}  --(-1)^n (d^n)^∨-->  D^{-n}
   |                                |
   ≅                                ≅
   v                                v
D'^{-(n+1)} --(-1)^n (d^n)^∨-->  D'^{-n}
```

commutes for formal reasons. Applied here with `D j` the dual sheaves and `D' j = K_n^{-j}`, it
replaces the dual sheaves by the Koszul complex's own terms with no mate ever computed.

## Main definitions

* `CochainComplex.dualXIsoAt`: the uniqueness isomorphism `D^{-n} ≅ D'^{-n}` of duals of `K^n`.
* `CochainComplex.dualXIsoIn`: the same, re-indexed by the degree of the dual complex, in the
  device of `CochainComplex.signedTransposeIn`: the degree of `K` is an argument the type does
  not mention, so two instances of it at propositionally equal degrees are equal by `subst` and
  no `eqToHom` is produced.
* `CochainComplex.dualComplexIso`: **the isomorphism of the two dual complexes.**
* `AlgebraicGeometry.RingedSite.exactPairingKoszulPowerComplexX`: **a term of the Koszul complex
  is its own dual**, a finite product of copies of `𝒪` being a finite biproduct of copies of the
  monoidal unit.
* `AlgebraicGeometry.RingedSite.koszulPowerDualComplex`: **the Koszul complex placed in degrees
  `-r, …, 0`**, with terms `K_n^{-j}` and the signed transpose of the Koszul differential.
* `AlgebraicGeometry.RingedSite.koszulPowerDualComplexSystem`: **the tower of those complexes**,
  the diagram of dual complexes of the direct system `koszulPowerSystem`.
* `AlgebraicGeometry.RingedSite.dualComplexKoszulPowerComplexIso`,
  `AlgebraicGeometry.RingedSite.derivedDualKoszulPowerComplexIso`: the two identifications above.

## Main results

* `CochainComplex.signedTransposeAt_comp_dualXIsoAt` and
  `CochainComplex.dualD_comp_dualXIsoIn`: the commuting square, at the degrees of `K` and at the
  degrees of the dual complexes.
* `CochainComplex.dualMate_comp_dualXIsoAt`,
  `CochainComplex.dualComplexMapX_comp_dualXIsoIn` and
  `CochainComplex.dualComplexMap_comp_dualComplexIso`: **the isomorphism of the two dual
  complexes is natural in the complex**, so an objectwise family of such identifications over a
  diagram of complexes is an isomorphism of the diagrams of dual complexes.
* `AlgebraicGeometry.RingedSite.koszulPowerDualComplex_X`,
  `AlgebraicGeometry.RingedSite.koszulPowerDualComplex_d`: the terms and the differential of the
  target complex.
* `AlgebraicGeometry.RingedSite.isZero_koszulPowerDualComplex_X_of_pos` and
  `AlgebraicGeometry.RingedSite.isZero_koszulPowerDualComplex_X_of_lt`: it is concentrated in
  degrees `-r, …, 0`.

## Implementation notes

**Why the terms are self-dual.** The degree-`p` term is `∏_{S} 𝒪` over the finite index type
`CategoryTheory.AlternatingCech.Idx r p`; a finite product is a finite biproduct
(`CategoryTheory.Limits.biproduct.isoProduct`), the monoidal unit of the strict structure on
`Mod(𝒪)` *is* `SheafOfModules.unit` so `CategoryTheory.exactPairingUnit` pairs each factor with
itself, and `CategoryTheory.ExactPairing.biproduct` ([Stacks, Tag 0FFT]) assembles those into a
pairing of the biproduct with itself. None of this computes a coevaluation or an evaluation.

**Which spelling of the monoidal structure.** Everything up to and including
`dualComplexKoszulPowerComplexIso` is at
`Stacks.SheafOfModules.Strict.monoidalCategory`, the spelling the dual complex of
[Stacks, Tag 0FPR] is stated at, supplied by `letI` rather than by synthesis because `Mod(𝒪)`
carries a second monoidal structure with the same tensor product. The derived statement is in a
separate section, where the re-seated structure that the derived tensor product of
[Stacks, Tag 0FPT] is built from is a local instance; the two sections therefore never have both
structures in scope at once.

**What is not here.** The differential of `koszulPowerDualComplex` is a *signed mate*
(`koszulPowerDualComplex_d`), not yet the explicit Koszul contraction
`∏_{|T| = p+1} 𝒪 ⟶ ∏_{|S| = p} 𝒪` whose component at `S ⊆ T` is multiplication by
`f_{T ∖ S}^{n+1}` with the alternating sign. Making it explicit needs a lemma computing a mate
in terms of biproduct components — that the mate of a map of biproducts is the map with the
transposed matrix of mates — and neither this repository nor Mathlib has one:
`CategoryTheory.ExactPairing.biproduct` gives the pairing with no accessors for its coevaluation
and evaluation in the family case, and `CategoryTheory.rightAdjointMate` is never related to
`CategoryTheory.Limits.biproduct.π`, `.ι`, `Pi.lift` or `Pi.π` anywhere. The tool to prove such
a lemma does exist: `CategoryTheory.ExactPairing.eq_mate` of
`StacksFrontier/CategoryTheory/Monoidal/MateAsInternalHomPre.lean` pins a candidate down from the
identity `g ▷ X ≫ ε_X = Y' ◁ f ≫ ε_Y` without unfolding the mate.

**What naturality is claimed.** `AlgebraicGeometry.RingedSite.koszulPowerDualComplexSystem`
assembles the complexes `koszulPowerDualComplex X f n` into a tower, by the functoriality of
`CochainComplex.dualComplex` of
`StacksFrontier.Algebra.Homology.SignedDualComplexFunctorial`; its transition maps are the
degreewise mates of `AlgebraicGeometry.RingedSite.koszulPowerComplexMap`.
`CochainComplex.dualComplexMap_comp_dualComplexIso` makes the *generic* identification of two
dual complexes natural in the complex, which is the half of the comparison that holds for formal
reasons. The Koszul statements below remain objectwise: `dualComplexKoszulPowerComplexIso` and
`derivedDualKoszulPowerComplexIso` are stated at one `n`, and
`Stacks.SheafOfModules.Strict.dualComplex` still has no functoriality of its own, so the dual
complexes of [Stacks, Tag 0FPR] are not assembled into a tower here.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0FFT](https://stacks.math.columbia.edu/tag/0FFT)
* [Stacks Project, Tag 0FNK](https://stacks.math.columbia.edu/tag/0FNK)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/
@[expose] public section

open CategoryTheory Limits MonoidalCategory

noncomputable section

universe v u

/-- Mates of a morphism commute with the mates of identities relating two choices of duals. -/
private theorem mate_comp_mate_id_comm {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {X X' Y Y' Z Z' : C} (a : ExactPairing X Y)
    (a' : ExactPairing X Y') (b : ExactPairing X' Z) (b' : ExactPairing X' Z') (f : X ⟶ X') :
    ExactPairing.mate a b f ≫ ExactPairing.mate a' a (𝟙 X) =
      ExactPairing.mate b' b (𝟙 X') ≫ ExactPairing.mate a' b' f := by
  rw [← ExactPairing.comp_mate a' a b, ← ExactPairing.comp_mate a' b' b, Category.id_comp,
    Category.comp_id]

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

variable (K : CochainComplex C ℤ) (D D' : ℤ → C)
  (q : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D j))
  (q' : ∀ i j : ℤ, i + j = 0 → ExactPairing (K.X i) (D' j))

/-- **The uniqueness isomorphism of two duals of `K^n`.** -/
def dualXIsoAt (n : ℤ) : D (-n) ≅ D' (-n) :=
  rightDualIso (dualPairing K D q n) (dualPairing K D' q' n)

/-- The uniqueness isomorphism read as an isomorphism of the degree-`j` terms of the two dual
complexes, the degree `n` of `K` whose duals it compares being pinned by the equation. -/
def dualXIsoIn (n j : ℤ) (h : n + j = 0) : D j ≅ D' j := by
  obtain rfl : j = -n := by omega
  exact dualXIsoAt K D D' q q' n

omit [MonoidalPreadditive C] in
/-- At the degree `-n`, `dualXIsoIn` is the uniqueness isomorphism `dualXIsoAt` of the duals of
`K^n`. -/
theorem dualXIsoIn_eq (n : ℤ) (h : n + -n = 0) :
    dualXIsoIn K D D' q q' n (-n) h = dualXIsoAt K D D' q q' n := rfl

omit [MonoidalPreadditive C] in
/-- **The square comparing the two signed transposes commutes.** -/
theorem signedTransposeAt_comp_dualXIsoAt (n : ℤ) :
    signedTransposeAt K D q n ≫ (dualXIsoAt K D D' q q' n).hom =
      (dualXIsoAt K D D' q q' (n + 1)).hom ≫ signedTransposeAt K D' q' n := by
  rw [signedTransposeAt_eq_mate, signedTransposeAt_eq_mate, Linear.units_smul_comp,
    Linear.comp_units_smul]
  exact congrArg _ (mate_comp_mate_id_comm (dualPairing K D q n) (dualPairing K D' q' n)
    (dualPairing K D q (n + 1)) (dualPairing K D' q' (n + 1)) (K.d n (n + 1)))

omit [MonoidalPreadditive C] in
/-- **The square comparing the two signed transposes, at the degrees of the dual complexes.**
The three integers are the degree `n` of `K` whose differential is transposed, read off the
target degree `j'`, and the degrees `j`, `j'` of the dual complexes; the first argument `m` of
the left-hand isomorphism is a separate parameter so that a consumer may supply it in whatever
form its own indexing produces. -/
theorem dualD_comp_dualXIsoIn (n m j j' : ℤ) (hm : m + j = 0) (h : n + j' = 0)
    (h' : n + 1 + j = 0) :
    (dualXIsoIn K D D' q q' m j hm).hom ≫ dualD K D' q' j j' =
      dualD K D q j j' ≫ (dualXIsoIn K D D' q q' n j' h).hom := by
  obtain rfl : m = n + 1 := by omega
  obtain rfl : j' = -n := by omega
  obtain rfl : j = -(n + 1) := by omega
  rw [dualD_eq K D q n _ _ h h', dualD_eq K D' q' n _ _ h h', signedTransposeIn_eq,
    signedTransposeIn_eq, dualXIsoIn_eq, dualXIsoIn_eq]
  exact (signedTransposeAt_comp_dualXIsoAt K D D' q q' n).symm

/-- **The two dual complexes are isomorphic.** The isomorphism is degreewise the uniqueness
isomorphism of duals, and it commutes with the signed-transpose differentials. -/
def dualComplexIso : dualComplex K D q ≅ dualComplex K D' q' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => dualXIsoIn K D D' q q' (-j) j (by omega))
    (fun i j hij => by
      have hij' : i + 1 = j := hij
      exact dualD_comp_dualXIsoIn K D D' q q' (-j) (-i) i j (by omega) (by omega) (by omega))

/-- The degree-`j` component of `dualComplexIso` is the uniqueness isomorphism of the duals of
`K^{-j}`. -/
theorem dualComplexIso_hom_f (j : ℤ) :
    (dualComplexIso K D D' q q').hom.f j =
      (dualXIsoIn K D D' q q' (-j) j (by omega)).hom :=
  rfl

section Naturality

variable (K' : CochainComplex C ℤ) (E E' : ℤ → C)
  (r : ∀ i j : ℤ, i + j = 0 → ExactPairing (K'.X i) (E j))
  (r' : ∀ i j : ℤ, i + j = 0 → ExactPairing (K'.X i) (E' j))
  (φ : K ⟶ K')

omit [MonoidalPreadditive C] in
/-- **The uniqueness isomorphism of duals is natural in the complex**, at the degrees of `K`:
the mate of `φ^n` for one pair of dual families, followed by the uniqueness isomorphism of the
duals of `K^n`, is the uniqueness isomorphism of the duals of `K'^n` followed by the mate of
`φ^n` for the other pair.

As with `CochainComplex.signedTransposeAt_comp_dualXIsoAt`, no mate is computed: both composites
are `CategoryTheory.ExactPairing.comp_mate` applied to a factorisation of `φ^n` through an
identity, the uniqueness isomorphism of duals *being* the mate of an identity. -/
theorem dualMate_comp_dualXIsoAt (n : ℤ) :
    ExactPairing.mate (dualPairing K D q n) (dualPairing K' E r n) (φ.f n) ≫
        (dualXIsoAt K D D' q q' n).hom =
      (dualXIsoAt K' E E' r r' n).hom ≫
        ExactPairing.mate (dualPairing K D' q' n) (dualPairing K' E' r' n) (φ.f n) := by
  exact mate_comp_mate_id_comm (dualPairing K D q n) (dualPairing K D' q' n)
    (dualPairing K' E r n) (dualPairing K' E' r' n) (φ.f n)

omit [MonoidalPreadditive C] in
/-- The same square at the degrees of the dual complexes: the degree `n` of the complexes is
pinned to `-j` by the equation, as in `CochainComplex.dualD_comp_dualXIsoIn`. -/
theorem dualComplexMapX_comp_dualXIsoIn (n j : ℤ) (h : n + j = 0) :
    dualComplexMapX K D q K' E r φ j ≫ (dualXIsoIn K D D' q q' n j h).hom =
      (dualXIsoIn K' E E' r r' n j h).hom ≫ dualComplexMapX K D' q' K' E' r' φ j := by
  obtain rfl : j = -n := by omega
  rw [dualXIsoIn_eq, dualXIsoIn_eq, dualComplexMapX_eq K D q K' E r φ n (-n) (by omega),
    dualComplexMapX_eq K D' q' K' E' r' φ n (-n) (by omega), dualMate_eq_mate_dualPairing,
    dualMate_eq_mate_dualPairing]
  exact dualMate_comp_dualXIsoAt K D D' q q' K' E E' r r' φ n

/-- **The isomorphism of the two dual complexes is natural in the complex.** A morphism
`φ : K ⟶ K'` induces morphisms of dual complexes for each choice of degreewise duals
(`CochainComplex.dualComplexMap`), and the square formed by those two morphisms and the two
uniqueness isomorphisms `CochainComplex.dualComplexIso` commutes.

This is what assembles the objectwise identifications of a tower of dual complexes into an
isomorphism of towers. -/
theorem dualComplexMap_comp_dualComplexIso :
    dualComplexMap K D q K' E r φ ≫ (dualComplexIso K D D' q q').hom =
      (dualComplexIso K' E E' r r').hom ≫ dualComplexMap K D' q' K' E' r' φ :=
  HomologicalComplex.hom_ext _ _ fun j => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, dualComplexMap_f,
      dualComplexIso_hom_f, dualComplexIso_hom_f, dualComplexMap_f]
    exact dualComplexMapX_comp_dualXIsoIn K D D' q q' K' E E' r r' φ (-j) j (by omega)

end Naturality

end CochainComplex

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **A term of the Koszul complex is its own dual.** The degree-`p` term is a finite product of
copies of `𝒪`; a finite product is a finite biproduct, the monoidal unit is `𝒪`, and the
biproduct of exact pairings is an exact pairing. -/
@[instance_reducible]
def exactPairingKoszulPowerComplexX (n : ℕ) (p : ℤ) :
    letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
    ExactPairing ((koszulPowerComplex X f n).X p) ((koszulPowerComplex X f n).X p) :=
  letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  letI : HasFiniteBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : ∀ S : AlternatingCech.Idx r p,
      ExactPairing ((koszulPowerFunctor X f n).obj S.1) ((koszulPowerFunctor X f n).obj S.1) :=
    fun _ => exactPairingUnit
  letI : ExactPairing (⨁ fun S : AlternatingCech.Idx r p => (koszulPowerFunctor X f n).obj S.1)
      (⨁ fun S : AlternatingCech.Idx r p => (koszulPowerFunctor X f n).obj S.1) :=
    ExactPairing.biproduct
  exactPairingCongr
    (biproduct.isoProduct fun S : AlternatingCech.Idx r p =>
      (koszulPowerFunctor X f n).obj S.1).symm
    (biproduct.isoProduct fun S : AlternatingCech.Idx r p =>
      (koszulPowerFunctor X f n).obj S.1).symm

/-- The self-duality of the terms of the Koszul complex, indexed by a pair of degrees summing to
zero: the shape `CochainComplex.dualComplex` asks a family of degreewise duals to carry. -/
@[instance_reducible]
def exactPairingKoszulPowerComplexIn (n : ℕ) (i j : ℤ) (h : i + j = 0) :
    letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
    ExactPairing ((koszulPowerComplex X f n).X i) ((koszulPowerComplex X f n).X (-j)) := by
  obtain rfl : i = -j := by omega
  exact exactPairingKoszulPowerComplexX X f n (-j)

/-- **The Koszul complex placed in degrees `-r, …, 0`.** Its degree-`j` term is the degree-`(-j)`
term of `K(𝒪, f_1^{n+1}, …, f_r^{n+1})` — the product of copies of `𝒪` indexed by the subsets of
`{1, …, r}` of cardinality `-j` — and its differential is the signed transpose of the Koszul
differential, by `CochainComplex.dualComplex_d`. -/
def koszulPowerDualComplex (n : ℕ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  CochainComplex.dualComplex (koszulPowerComplex X f n)
    (fun j => (koszulPowerComplex X f n).X (-j)) (exactPairingKoszulPowerComplexIn X f n)

/-- The degree-`j` term of the Koszul complex in degrees `-r, …, 0` is the degree-`(-j)` term of
the Koszul complex. -/
theorem koszulPowerDualComplex_X (n : ℕ) (j : ℤ) :
    (koszulPowerDualComplex X f n).X j = (koszulPowerComplex X f n).X (-j) :=
  rfl

/-- **The differential of the Koszul complex in degrees `-r, …, 0` is the signed transpose of
the Koszul differential**: from degree `-(p+1)` to degree `-p` it is `(-1)^p` times the mate of
`d^p : ∏_{|S| = p} 𝒪 ⟶ ∏_{|T| = p+1} 𝒪`, taken at the self-dualities
`AlgebraicGeometry.RingedSite.exactPairingKoszulPowerComplexX` of the terms. -/
theorem koszulPowerDualComplex_d (n : ℕ) (p : ℤ) :
    letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
    letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
    (koszulPowerDualComplex X f n).d (-(p + 1)) (-p) =
      CochainComplex.signedTransposeAt (koszulPowerComplex X f n)
        (fun j => (koszulPowerComplex X f n).X (-j))
        (exactPairingKoszulPowerComplexIn X f n) p :=
  let : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  let : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  CochainComplex.dualComplex_d (koszulPowerComplex X f n)
    (fun j => (koszulPowerComplex X f n).X (-j)) (exactPairingKoszulPowerComplexIn X f n) p

/-- The Koszul complex in degrees `-r, …, 0` vanishes in positive degrees. -/
theorem isZero_koszulPowerDualComplex_X_of_pos (n : ℕ) {j : ℤ} (hj : 0 < j) :
    IsZero ((koszulPowerDualComplex X f n).X j) :=
  isZero_koszulPowerComplex_X_of_neg X f n (by omega)

/-- The Koszul complex in degrees `-r, …, 0` vanishes below degree `-r`. -/
theorem isZero_koszulPowerDualComplex_X_of_lt (n : ℕ) {j : ℤ} (hj : j < -(r : ℤ)) :
    IsZero ((koszulPowerDualComplex X f n).X j) :=
  isZero_koszulPowerComplex_X_of_lt X f n (by omega)

/-- **The tower of the Koszul complexes in degrees `-r, …, 0`.**
`AlgebraicGeometry.RingedSite.koszulPowerSystem` is a *direct* system of complexes, so the
diagram of the dual complexes of its terms runs the other way and is a tower, an
`ℕᵒᵖ`-diagram: its object at `n` is `AlgebraicGeometry.RingedSite.koszulPowerDualComplex`, the
Koszul complex `K(𝒪, f^{n+1})` read in degrees `-r, …, 0`, and its transition map from `n + 1`
to `n` is the degreewise mate of
`AlgebraicGeometry.RingedSite.koszulPowerComplexMap`. -/
@[ega "III 1.1.6" "(1.1.6.1)"]
def koszulPowerDualComplexSystem :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  CochainComplex.dualDiagram (koszulPowerSystem X f)
    (fun n j => (koszulPowerComplex X f n).X (-j))
    (fun n => exactPairingKoszulPowerComplexIn X f n)

/-- The terms of the tower are the Koszul complexes in degrees `-r, …, 0`. -/
@[simp]
theorem koszulPowerDualComplexSystem_obj (n : ℕ) :
    (koszulPowerDualComplexSystem X f).obj (Opposite.op n) = koszulPowerDualComplex X f n :=
  rfl

/-- The transition maps of the tower are the maps of dual complexes induced by the transition
maps of `AlgebraicGeometry.RingedSite.koszulPowerSystem`. -/
theorem koszulPowerDualComplexSystem_map {a b : ℕᵒᵖ} (g : a ⟶ b) :
    letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
    letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
    (koszulPowerDualComplexSystem X f).map g =
      CochainComplex.dualComplexMap (koszulPowerComplex X f b.unop)
        (fun j => (koszulPowerComplex X f b.unop).X (-j))
        (exactPairingKoszulPowerComplexIn X f b.unop)
        (koszulPowerComplex X f a.unop)
        (fun j => (koszulPowerComplex X f a.unop).X (-j))
        (exactPairingKoszulPowerComplexIn X f a.unop)
        ((koszulPowerSystem X f).map g.unop) :=
  rfl

section DualComplex

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The dual complex of [Stacks, Tag 0FPR] of the Koszul complex is the Koszul complex in
degrees `-r, …, 0`.** The terms of the dual complex are the dual sheaves
`𝑆heafHom(∏_{|S| = -j} 𝒪, 𝒪)`, and the terms of the target are the products
`∏_{|S| = -j} 𝒪` themselves; both are duals of the degree-`(-j)` term of the Koszul complex, so
they are identified by uniqueness of duals, and the identification commutes with the differentials
because the signed transpose of one family of duals is carried to the signed transpose of the
other.

The differential of the target is the signed transpose of the Koszul differential, in the sense
of `CochainComplex.dualComplex_d`. -/
def dualComplexKoszulPowerComplexIso (n : ℕ)
    (hterm : ∀ p : ℤ, Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) ((koszulPowerComplex X f n).X p)) :
    Stacks.SheafOfModules.Strict.dualComplex X.O (koszulPowerComplex X f n) hterm ≅
      koszulPowerDualComplex X f n :=
  letI : MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)
  letI : MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.Strict.monoidalPreadditiveRingSheaf X.O
  CochainComplex.dualComplexIso (koszulPowerComplex X f n) _ _
    (Stacks.SheafOfModules.Strict.dualComplexPairing X.O (koszulPowerComplex X f n) hterm)
    (exactPairingKoszulPowerComplexIn X f n)

end DualComplex

/-! ### The derived dual -/

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The terms of the Koszul complex are *locally* direct summands of finite free `𝒪`-modules —
the hypothesis of [Stacks, Tag 0FNY] — being direct summands of finite free `𝒪`-modules
globally. -/
theorem isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X (n : ℕ) (p : ℤ) :
    Stacks.SheafOfModules.IsLocallyDirectSummandOfFiniteFree X.O.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O) ((koszulPowerComplex X f n).X p) :=
  isLocallyDirectSummandOfFiniteFree_of_isDirectSummandOfFiniteFree X _
    (isDirectSummandOfFiniteFree_koszulPowerComplex_X X f n p)

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The Koszul complex of `f^{n+1}` vanishes in every degree outside `[0, r]`. -/
theorem isZero_koszulPowerComplex_X_of_not_mem_Icc (n : ℕ) (m : ℤ)
    (hm : m ∉ Finset.Icc (0 : ℤ) (r : ℤ)) : IsZero ((koszulPowerComplex X f n).X m) := by
  rw [Finset.mem_Icc, not_and_or] at hm
  rcases hm with h | h
  · exact isZero_koszulPowerComplex_X_of_neg X f n (by omega)
  · exact isZero_koszulPowerComplex_X_of_lt X f n (by omega)

/-- **The derived dual of the Koszul complex is the Koszul complex in degrees `-r, …, 0`.** This
is the `K_n` of the displayed formula of [Stacks, Tag 0A0E]: the derived dual
`K_n^∨ = R𝑆heafHom_𝒪(K(𝒪, f^{n+1}), 𝒪)` of [Stacks, Tag 08JD] is the image in `D(𝒪)` of the
explicit complex `AlgebraicGeometry.RingedSite.koszulPowerDualComplex`, whose degree-`j` term is
the degree-`(-j)` term `∏_{|S| = -j} 𝒪` of the Koszul complex and whose differential is the
signed transpose of the Koszul differential.

The two halves are `AlgebraicGeometry.RingedSite.derivedDualIsoQDualComplex`, which computes the
derived dual by the dual complex of [Stacks, Tag 0FPR], and
`AlgebraicGeometry.RingedSite.dualComplexKoszulPowerComplexIso`, which replaces the dual sheaves
of the terms by the terms themselves. -/
def derivedDualKoszulPowerComplexIso (n : ℕ) :
    derivedDual X (DerivedCategory.Q.obj (koszulPowerComplex X f n)) ≅
      DerivedCategory.Q.obj (koszulPowerDualComplex X f n) :=
  derivedDualIsoQDualComplex X (koszulPowerComplex X f n)
      (isLocallyDirectSummandOfFiniteFree_koszulPowerComplex_X X f n)
      (Finset.Icc (0 : ℤ) (r : ℤ)) (isZero_koszulPowerComplex_X_of_not_mem_Icc X f n)
      (kFlatComplexes_of_isStrictlyPerfect X _ (isStrictlyPerfect_koszulPowerComplex X f n))
      (kFlatComplexes_dualComplex X (koszulPowerComplex X f n) _
        (isStrictlyPerfect_koszulPowerComplex X f n)) ≪≫
    DerivedCategory.Q.mapIso (dualComplexKoszulPowerComplexIso X f n _)

end Derived

end AlgebraicGeometry.RingedSite

end

end
