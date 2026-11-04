module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.SetTheory.Cardinal.NatCard
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeAffine
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal

/-!
# Sections of a complex of finite free modules over an open, in chosen bases

Let `X` be a scheme, `U ⊆ X` an open and `ℳ^•` a cochain complex of `𝒪_X`-modules.  The sections
`Γ(U, ℳ^i)` form a cochain complex of `Γ(X, U)`-modules.  If each `Γ(U, ℳ^i)` is free with a
chosen basis indexed by `Fin rᵢ`, and `rᵢ = 0` for all but finitely many `i`, then that complex
of sections is *isomorphic as a complex* to the complex of a `BoundedComplex Γ(X, U)`: each term
becomes literally `Fin rᵢ → Γ(X, U)` and each differential the matrix of `dⁱ` in the chosen
bases.  This is what lets the matrix-level constructions of More on Algebra, Section 15.98 — the
determinantal ideals and the operator `η_f`, in particular the finite local freeness of its terms
of Tag 0F7W — be applied to a complex of sheaves over an affine chart; the derived-category
comparison of Tag 06Z0 does not give a termwise presentation.

The comparison is natural in the restriction maps: for `V ⊆ U`, restriction of sections is
semilinear over the restriction `Γ(X, U) → Γ(X, V)` of functions, and in the chosen bases on both
opens it is given by matrices over `Γ(X, V)` which intertwine the base change of the matrix
complex on `U` with the matrix complex on `V`.

## Main definitions

* `Stacks.Eta.BasisPresentation`: chosen finite bases for the terms of a cochain complex of
  modules, almost all of rank zero.
* `Stacks.Eta.BasisPresentation.toBoundedComplex`: the resulting bounded matrix complex.
* `Stacks.Eta.BasisPresentation.iso`: the isomorphism of complexes onto it.
* `Stacks.Eta.BasisPresentation.semilinearMatrix` and
  `Stacks.Eta.BasisPresentation.semilinearHom`: the matrices of a semilinear morphism of
  complexes in the chosen bases, and the induced morphism from the base-changed matrix complex.
* `Stacks.Eta.Sections.complex`: sections over an open of a cochain complex of `𝒪_X`-modules,
  built from `AlgebraicGeometry.sectionsOn`.
* `Stacks.Eta.Sections.presentation` and `Stacks.Eta.Sections.iso`: the chosen-basis presentation
  of the complex of sections, and the isomorphism of complexes onto a `BoundedComplex Γ(X, U)`.
* `Stacks.Eta.Sections.restrictionMap`, `Stacks.Eta.Sections.restrictionMatrix` and
  `Stacks.Eta.Sections.restrictionHom`: restriction of sections as a semilinear map, its matrices
  in the chosen bases, and the morphism of matrix complexes they define.

## Main results

* `Stacks.Eta.BasisPresentation.semilinearMatrix_mulVec` and
  `Stacks.Eta.Sections.restrictionMatrix_mulVec`: the naturality of the comparison in coordinates.
* `Stacks.Eta.Sections.restrictionMatrix_comm`: the matrices of the restriction maps intertwine
  the base change along `Γ(X, U) → Γ(X, V)` of the matrix complex over `U` with the matrix
  complex over `V`.
* `Stacks.Eta.Sections.exists_boundedComplex_iso` and
  `Stacks.Eta.Sections.exists_boundedComplex_iso_of_isFiniteLocallyFree`: a complex of
  `𝒪_X`-modules whose modules of sections over `U` are free, finite, and zero in all but finitely
  many degrees, has its complex of sections over `U` isomorphic to the complex of a
  `BoundedComplex Γ(X, U)`.

## Implementation notes

The differentials are read off with `LinearMap.toMatrix`, whose rows are indexed by the target
basis and columns by the source basis, matching the shape `Matrix (Fin rᵢ₊₁) (Fin rᵢ)` of a
`BoundedComplex`.  The cochain condition comes from `LinearMap.toMatrix_comp` together with
`HomologicalComplex.d_comp_d`, and the squares of the comparison from
`LinearMap.toMatrix_mulVec_repr`.

The matrix of the differential is given its own name `BasisPresentation.dMatrix`, rather than
being written out inside `toBoundedComplex`, so that the matrix identities of the naturality
statements are typed by `rank` directly: a product of matrices indexed by
`toBoundedComplex.rank` on one side and by `rank` on the other has no multiplication instance,
even though the two are definitionally equal.

Freeness of `Γ(U, ℳ^i)` is an honest extra hypothesis and not a consequence of finite local
freeness of `ℳ^i`: a basis is what the construction needs, and finite local freeness provides
only one after further shrinking of `U`.  Finite local freeness is used only for finiteness of
the module, through `Module.isFiniteLocallyFree_iff_finite_projective`; the spelling is
`Module.IsFiniteLocallyFree`, in which that characterization and the sheaf-to-module comparison
of Tag 05JM are both available.

In the degrees where `Γ(U, ℳ^i)` vanishes the rank is taken to be `0` and the basis to be the
empty one, rather than whatever a chosen basis of the zero module happens to be indexed by; this
is what turns "almost all terms vanish" into the boundedness condition on the ranks.

## References

* [Stacks Project, Tag 0F7W](https://stacks.math.columbia.edu/tag/0F7W)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace BoundedComplex

/-- Composing multiplication by two matrices is multiplication by their product.  Stated for
matrices with explicit index ranks so that it can be applied in term mode to the differentials of
a bounded matrix complex, whose index types are not syntactically of this form. -/
private theorem ofHom_mulVecLin_comp {B : Type u} [CommRing B] {k l m : ℕ}
    (S : Matrix (Fin l) (Fin k) B) (T : Matrix (Fin m) (Fin l) B) (T' : Matrix (Fin m) (Fin k) B)
    (h : T * S = T') :
    ModuleCat.ofHom S.mulVecLin ≫ ModuleCat.ofHom T.mulVecLin =
      ModuleCat.ofHom T'.mulVecLin := by
  rw [← ModuleCat.ofHom_comp, ← Matrix.mulVecLin_mul, h]

/-- A family of matrices intertwining the differentials of two bounded matrix complexes defines
a morphism between the associated complexes of modules. -/
def homOfMatrices {B : Type u} [CommRing B] (C D : BoundedComplex B)
    (R : ∀ i : ℤ, Matrix (Fin (D.rank i)) (Fin (C.rank i)) B)
    (hR : ∀ i : ℤ, R (i + 1) * C.d i = D.d i * R i) :
    C.toCochainComplex ⟶ D.toCochainComplex where
  f i := ModuleCat.ofHom (R i).mulVecLin
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    simp only [toCochainComplex_d]
    exact (ofHom_mulVecLin_comp (R i) (D.d i) _ rfl).trans
      (ofHom_mulVecLin_comp (C.d i) (R (i + 1)) _ (hR i)).symm

/-- In degree `i` the morphism defined by a family of matrices is multiplication by the `i`-th
matrix. -/
@[simp] theorem homOfMatrices_f {B : Type u} [CommRing B] (C D : BoundedComplex B)
    (R : ∀ i : ℤ, Matrix (Fin (D.rank i)) (Fin (C.rank i)) B)
    (hR : ∀ i : ℤ, R (i + 1) * C.d i = D.d i * R i) (i : ℤ) :
    (homOfMatrices C D R hR).f i = ModuleCat.ofHom (R i).mulVecLin := rfl

end BoundedComplex

namespace Stacks.Eta

variable {A : Type u} [CommRing A]

/-! ### Chosen bases for a complex of modules -/

/-- Chosen finite bases for the terms of a cochain complex of `A`-modules, all but finitely many
of them of rank zero: the data of a presentation of the complex as a bounded complex of finite
free modules written in bases. -/
structure BasisPresentation (K : CochainComplex (ModuleCat.{u} A) ℤ) where
  /-- The rank `rᵢ` of the `i`-th term. -/
  rank : ℤ → ℕ
  /-- The chosen basis of the `i`-th term. -/
  basis : ∀ i : ℤ, Module.Basis (Fin (rank i)) A (K.X i)
  /-- All but finitely many of the ranks vanish. -/
  bounded : {i : ℤ | rank i ≠ 0}.Finite

namespace BasisPresentation

variable {K : CochainComplex (ModuleCat.{u} A) ℤ} (P : BasisPresentation K)

/-- The matrix of the differential `dⁱ` in the chosen bases. -/
def dMatrix (i : ℤ) : Matrix (Fin (P.rank (i + 1))) (Fin (P.rank i)) A :=
  LinearMap.toMatrix (P.basis i) (P.basis (i + 1)) (K.d i (i + 1)).hom

/-- The matrices of two consecutive differentials compose to zero. -/
theorem dMatrix_mul_dMatrix (i : ℤ) : P.dMatrix (i + 1) * P.dMatrix i = 0 := by
  rw [dMatrix, dMatrix,
    ← LinearMap.toMatrix_comp (P.basis i) (P.basis (i + 1)) (P.basis (i + 1 + 1))]
  have h1 : K.d i (i + 1) ≫ K.d (i + 1) (i + 1 + 1) = 0 := K.d_comp_d i (i + 1) (i + 1 + 1)
  have h2 : (K.d (i + 1) (i + 1 + 1)).hom.comp (K.d i (i + 1)).hom = 0 := by
    rw [← ModuleCat.hom_comp, h1]
    simp
  rw [h2, map_zero]

/-- The bounded complex of finite free modules recorded by a chosen-basis presentation: the
ranks of the terms and the matrices of the differentials. -/
def toBoundedComplex : BoundedComplex A where
  rank := P.rank
  d := P.dMatrix
  dd := P.dMatrix_mul_dMatrix
  bounded := P.bounded

/-- The ranks of the associated bounded matrix complex are the chosen ranks. -/
@[simp] theorem toBoundedComplex_rank : P.toBoundedComplex.rank = P.rank := rfl

/-- The differentials of the associated bounded matrix complex are the matrices of the
differentials in the chosen bases. -/
@[simp] theorem toBoundedComplex_d (i : ℤ) : P.toBoundedComplex.d i = P.dMatrix i := rfl

/-- In degree `i` the comparison with the associated bounded matrix complex is the coordinate
isomorphism of the chosen basis. -/
def termIso (i : ℤ) : K.X i ≅ P.toBoundedComplex.toCochainComplex.X i :=
  (P.basis i).equivFun.toModuleIso

/-- **A complex of modules with chosen finite bases is the complex of a bounded matrix
complex.**  Degreewise the isomorphism is the coordinate isomorphism of the chosen basis, and the
differentials correspond to their matrices. -/
def iso : K ≅ P.toBoundedComplex.toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents P.termIso (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp only [termIso, BoundedComplex.toCochainComplex_d, LinearEquiv.toModuleIso_hom,
      toBoundedComplex_d, dMatrix]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change ((LinearMap.toMatrix (P.basis i) (P.basis (i + 1))) ((K.d i (i + 1)).hom)).mulVec
        ((P.basis i).equivFun x) = (P.basis (i + 1)).equivFun ((K.d i (i + 1)).hom x)
    exact LinearMap.toMatrix_mulVec_repr (P.basis i) (P.basis (i + 1)) _ x)

/-- The comparison sends a section to its coordinate vector in the chosen basis. -/
theorem iso_hom_f_apply (i : ℤ) (x : K.X i) :
    (P.iso.hom.f i).hom x = (P.basis i).equivFun x := rfl

/-- A cochain complex of free finite modules whose terms vanish in all but finitely many degrees
admits a chosen-basis presentation.  The ranks are taken to be zero in the degrees where the term
vanishes, which is what makes them almost all zero. -/
theorem exists_of_free (hfree : ∀ i : ℤ, Module.Free A (K.X i))
    (hfin : ∀ i : ℤ, Module.Finite A (K.X i))
    (hzero : {i : ℤ | ¬ Subsingleton (K.X i)}.Finite) : Nonempty (BasisPresentation K) := by
  classical
  have key : ∀ i : ℤ, ∃ r : ℕ, Nonempty (Module.Basis (Fin r) A (K.X i)) ∧
      (Subsingleton (K.X i) → r = 0) := by
    intro i
    by_cases hs : Subsingleton (K.X i)
    · exact ⟨0, ⟨Module.Basis.empty _⟩, fun _ => rfl⟩
    · exact ⟨Nat.card (Module.Free.ChooseBasisIndex A (K.X i)),
        ⟨(Module.Free.chooseBasis A (K.X i)).reindex (Finite.equivFin _)⟩, fun h => absurd h hs⟩
  choose r hr hr0 using key
  exact ⟨{ rank := r
           basis := fun i => (hr i).some
           bounded := hzero.subset fun i hi hs => hi (hr0 i hs) }⟩

/-! ### Naturality in a semilinear morphism of complexes -/

section Semilinear

variable {B : Type u} [CommRing B] {L : CochainComplex (ModuleCat.{u} B) ℤ}
  (ρ : A →+* B) (Q : BasisPresentation L) (θ : ∀ i : ℤ, K.X i →ₛₗ[ρ] L.X i)

/-- The matrix of a `ρ`-semilinear map `K^i → L^i` in the chosen bases: its columns are the
coordinate vectors of the images of the chosen basis of `K^i`. -/
def semilinearMatrix (i : ℤ) : Matrix (Fin (Q.rank i)) (Fin (P.rank i)) B :=
  Matrix.of fun j k => (Q.basis i).repr (θ i ((P.basis i) k)) j

/-- **Naturality of the comparison in coordinates.**  Applying a semilinear map and then taking
coordinates is multiplying the image under `ρ` of the coordinate vector by the matrix of the
map. -/
theorem semilinearMatrix_mulVec (i : ℤ) (x : K.X i) :
    (semilinearMatrix P ρ Q θ i).mulVec (fun k => ρ ((P.basis i).equivFun x k)) =
      (Q.basis i).equivFun (θ i x) := by
  classical
  set c : Fin (P.rank i) → A := (P.basis i).equivFun x with hc
  have hx : ∑ k, c k • (P.basis i) k = x := (P.basis i).sum_equivFun x
  funext j
  rw [← hx]
  simp only [map_sum, map_smulₛₗ, Matrix.mulVec, dotProduct, semilinearMatrix, Matrix.of_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **The matrices of a semilinear morphism of complexes intertwine the differentials.**  On the
left they are composed with the base change along `ρ` of the matrices of the differentials of
`K`, on the right with the matrices of the differentials of `L`. -/
theorem semilinearMatrix_comm
    (hθ : ∀ (i : ℤ) (x : K.X i), θ (i + 1) ((K.d i (i + 1)).hom x) =
      (L.d i (i + 1)).hom (θ i x)) (i : ℤ) :
    semilinearMatrix P ρ Q θ (i + 1) * (P.dMatrix i).map ρ =
      Q.dMatrix i * semilinearMatrix P ρ Q θ i := by
  ext j k
  have hcol : ∀ l, ((P.dMatrix i).map ρ) l k =
      ρ ((P.basis (i + 1)).equivFun ((K.d i (i + 1)).hom ((P.basis i) k)) l) := by
    intro l
    rw [Matrix.map_apply, dMatrix, LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]
  have e1 : (semilinearMatrix P ρ Q θ (i + 1) * (P.dMatrix i).map ρ) j k =
      (semilinearMatrix P ρ Q θ (i + 1)).mulVec
        (fun l => ρ ((P.basis (i + 1)).equivFun ((K.d i (i + 1)).hom ((P.basis i) k)) l)) j := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun l _ => by rw [hcol l]
  have e2 : (Q.dMatrix i * semilinearMatrix P ρ Q θ i) j k =
      (Q.dMatrix i).mulVec ((Q.basis i).equivFun (θ i ((P.basis i) k))) j := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, semilinearMatrix, Matrix.of_apply,
      Module.Basis.equivFun_apply]
  rw [e1, e2, semilinearMatrix_mulVec, dMatrix]
  simp only [Module.Basis.equivFun_apply]
  rw [LinearMap.toMatrix_mulVec_repr, hθ]

/-- A semilinear morphism of complexes, read in the chosen bases, is a morphism of complexes from
the base change along `ρ` of the matrix complex of `K` to the matrix complex of `L`. -/
def semilinearHom (hθ : ∀ (i : ℤ) (x : K.X i), θ (i + 1) ((K.d i (i + 1)).hom x) =
      (L.d i (i + 1)).hom (θ i x)) :
    (P.toBoundedComplex.baseChange ρ).toCochainComplex ⟶ Q.toBoundedComplex.toCochainComplex :=
  BoundedComplex.homOfMatrices _ _ (fun i => semilinearMatrix P ρ Q θ i)
    (fun i => semilinearMatrix_comm P ρ Q θ hθ i)

/-- In degree `i` the morphism of matrix complexes induced by a semilinear morphism is
multiplication by the matrix of that morphism in the chosen bases. -/
@[simp] theorem semilinearHom_f (hθ : ∀ (i : ℤ) (x : K.X i), θ (i + 1) ((K.d i (i + 1)).hom x) =
      (L.d i (i + 1)).hom (θ i x)) (i : ℤ) :
    (semilinearHom P ρ Q θ hθ).f i = ModuleCat.ofHom (semilinearMatrix P ρ Q θ i).mulVecLin :=
  rfl

end Semilinear

end BasisPresentation

/-! ### Sections over an open of a scheme -/

namespace Sections

variable {X : Scheme.{u}}

/-- The complex of sections of a cochain complex of `𝒪_X`-modules over an open `U`, a cochain
complex of `Γ(X, U)`-modules. -/
def complex (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) :
    CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ :=
  ((_root_.AlgebraicGeometry.sectionsOn X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj ℳ

/-- In degree `i` the complex of sections is the module of sections of `ℳ^i`. -/
@[simp] theorem complex_X (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (i : ℤ) :
    (complex U ℳ).X i = ModuleCat.of Γ(X, U) Γ(ℳ.X i, U) := rfl

/-- The differentials of the complex of sections are the differentials of `ℳ^•` on sections. -/
@[simp] theorem complex_d (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (i j : ℤ) :
    (complex U ℳ).d i j = (_root_.AlgebraicGeometry.sectionsOn X U).map (ℳ.d i j) := rfl

/-- Chosen bases for the modules of sections over `U` of the terms of a complex of
`𝒪_X`-modules, almost all of rank zero, as a presentation of the complex of sections. -/
def presentation (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (r : ℤ → ℕ)
    (b : ∀ i : ℤ, Module.Basis (Fin (r i)) Γ(X, U) Γ(ℳ.X i, U))
    (hr : {i : ℤ | r i ≠ 0}.Finite) : BasisPresentation (complex U ℳ) where
  rank := r
  basis := b
  bounded := hr

/-- The ranks of a chosen-basis presentation of the sections are the chosen ranks. -/
@[simp] theorem presentation_rank (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (r : ℤ → ℕ)
    (b : ∀ i : ℤ, Module.Basis (Fin (r i)) Γ(X, U) Γ(ℳ.X i, U))
    (hr : {i : ℤ | r i ≠ 0}.Finite) : (presentation U ℳ r b hr).rank = r := rfl

/-- **The sections of a complex of finite free `𝒪_X`-modules over an open, in chosen bases.**
In each degree the module of sections `Γ(U, ℳ^i)` is identified with `Fin rᵢ → Γ(X, U)` by the
chosen basis, and the differential `dⁱ` with its matrix, so that the complex of sections is the
complex of a `BoundedComplex Γ(X, U)`.  Unlike a derived-category comparison, this is an
isomorphism of complexes and is termwise given by coordinates. -/
def iso (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (r : ℤ → ℕ)
    (b : ∀ i : ℤ, Module.Basis (Fin (r i)) Γ(X, U) Γ(ℳ.X i, U))
    (hr : {i : ℤ | r i ≠ 0}.Finite) :
    complex U ℳ ≅ (presentation U ℳ r b hr).toBoundedComplex.toCochainComplex :=
  (presentation U ℳ r b hr).iso

/-- The bounded matrix complex of a chosen-basis presentation of the sections has the chosen
ranks. -/
@[simp] theorem toBoundedComplex_rank (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (r : ℤ → ℕ)
    (b : ∀ i : ℤ, Module.Basis (Fin (r i)) Γ(X, U) Γ(ℳ.X i, U))
    (hr : {i : ℤ | r i ≠ 0}.Finite) :
    (presentation U ℳ r b hr).toBoundedComplex.rank = r := rfl

/-- The differential of the bounded matrix complex of a chosen-basis presentation of the sections
is the matrix of the differential of `ℳ^•` on sections. -/
theorem toBoundedComplex_d (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (r : ℤ → ℕ)
    (b : ∀ i : ℤ, Module.Basis (Fin (r i)) Γ(X, U) Γ(ℳ.X i, U))
    (hr : {i : ℤ | r i ≠ 0}.Finite) (i : ℤ) :
    (presentation U ℳ r b hr).toBoundedComplex.d i =
      LinearMap.toMatrix (b i) (b (i + 1))
        ((_root_.AlgebraicGeometry.sectionsOn X U).map (ℳ.d i (i + 1))).hom := rfl

/-- The comparison sends a section over `U` to its coordinate vector in the chosen basis. -/
theorem iso_hom_f_apply (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ) (r : ℤ → ℕ)
    (b : ∀ i : ℤ, Module.Basis (Fin (r i)) Γ(X, U) Γ(ℳ.X i, U))
    (hr : {i : ℤ | r i ≠ 0}.Finite) (i : ℤ) (x : Γ(ℳ.X i, U)) :
    ((iso U ℳ r b hr).hom.f i).hom x = (b i).equivFun x := rfl

/-- **The complex of sections over `U` is the complex of a bounded complex of finite free
`Γ(X, U)`-modules**, as soon as the modules of sections are free and finite and vanish in all but
finitely many degrees. -/
theorem exists_boundedComplex_iso (U : X.Opens) (ℳ : CochainComplex X.Modules ℤ)
    (hfree : ∀ i : ℤ, Module.Free Γ(X, U) Γ(ℳ.X i, U))
    (hfin : ∀ i : ℤ, Module.Finite Γ(X, U) Γ(ℳ.X i, U))
    (hzero : {i : ℤ | ¬ Subsingleton Γ(ℳ.X i, U)}.Finite) :
    ∃ C : BoundedComplex Γ(X, U), Nonempty (complex U ℳ ≅ C.toCochainComplex) := by
  obtain ⟨P⟩ := BasisPresentation.exists_of_free (K := complex U ℳ) hfree hfin hzero
  exact ⟨P.toBoundedComplex, ⟨P.iso⟩⟩

/-- The same statement with finiteness of the modules of sections supplied by finite local
freeness, which is how it arrives from a finite locally free `𝒪_X`-module over an affine open.
Freeness remains a separate hypothesis: finite local freeness gives a basis only after further
shrinking. -/
theorem exists_boundedComplex_iso_of_isFiniteLocallyFree (U : X.Opens)
    (ℳ : CochainComplex X.Modules ℤ)
    (hfree : ∀ i : ℤ, Module.Free Γ(X, U) Γ(ℳ.X i, U))
    (hflf : ∀ i : ℤ, Module.IsFiniteLocallyFree Γ(X, U) Γ(ℳ.X i, U))
    (hzero : {i : ℤ | ¬ Subsingleton Γ(ℳ.X i, U)}.Finite) :
    ∃ C : BoundedComplex Γ(X, U), Nonempty (complex U ℳ ≅ C.toCochainComplex) :=
  exists_boundedComplex_iso U ℳ hfree
    (fun i => ((Module.isFiniteLocallyFree_iff_finite_projective _ _).mp (hflf i)).1) hzero

/-! ### Naturality in the restriction maps -/

section Restriction

variable (ℳ : CochainComplex X.Modules ℤ) {U V : X.Opens} (h : V ≤ U)

/-- Restriction of sections from `U` to a smaller open `V`, as a map semilinear over the
restriction `Γ(X, U) → Γ(X, V)` of functions. -/
def restrictionMap (F : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    Γ(F, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(F, V) where
  toFun := F.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r x := F.map_smul (homOfLE h) r x

/-- Restriction of sections is the restriction map of the underlying presheaf. -/
@[simp] theorem restrictionMap_apply (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (x : Γ(F, U)) :
    restrictionMap F h x = F.presheaf.map (homOfLE h).op x := rfl

/-- Restriction of sections commutes with the differentials of the complex of sections. -/
theorem restrictionMap_comm (i j : ℤ) (x : Γ(ℳ.X i, U)) :
    restrictionMap (ℳ.X j) h (((complex U ℳ).d i j).hom x) =
      ((complex V ℳ).d i j).hom (restrictionMap (ℳ.X i) h x) :=
  (congr($((ℳ.d i j).mapPresheaf.naturality (homOfLE h).op) x)).symm

variable (P : BasisPresentation (complex U ℳ)) (Q : BasisPresentation (complex V ℳ))

/-- The matrix over `Γ(X, V)` of the restriction map on sections in degree `i`, read in the
chosen bases over `U` and over `V`. -/
def restrictionMatrix (i : ℤ) : Matrix (Fin (Q.rank i)) (Fin (P.rank i)) Γ(X, V) :=
  P.semilinearMatrix (X.presheaf.map (homOfLE h).op).hom Q
    (fun i => restrictionMap (ℳ.X i) h) i

/-- **Naturality of the comparison in the restriction maps, in coordinates.**  Restricting a
section from `U` to `V` and then taking coordinates in the basis over `V` is multiplying the
restriction to `V` of its coordinate vector over `U` by the matrix of the restriction map. -/
theorem restrictionMatrix_mulVec (i : ℤ) (x : Γ(ℳ.X i, U)) :
    (restrictionMatrix ℳ h P Q i).mulVec
        (fun k => X.presheaf.map (homOfLE h).op ((P.basis i).equivFun x k)) =
      (Q.basis i).equivFun (restrictionMap (ℳ.X i) h x) :=
  P.semilinearMatrix_mulVec (X.presheaf.map (homOfLE h).op).hom Q
    (fun i => restrictionMap (ℳ.X i) h) i x

/-- **The matrices of the restriction maps intertwine the two matrix complexes.**  Composed with
the base change along `Γ(X, U) → Γ(X, V)` of the matrices of the differentials over `U` they give
the matrices of the differentials over `V`. -/
theorem restrictionMatrix_comm (i : ℤ) :
    restrictionMatrix ℳ h P Q (i + 1) *
        (P.dMatrix i).map (X.presheaf.map (homOfLE h).op).hom =
      Q.dMatrix i * restrictionMatrix ℳ h P Q i :=
  P.semilinearMatrix_comm (X.presheaf.map (homOfLE h).op).hom Q
    (fun i => restrictionMap (ℳ.X i) h) (fun i x => restrictionMap_comm ℳ h i (i + 1) x) i

/-- **Naturality of the comparison in the restriction maps.**  The matrices of the restriction
maps form a morphism of complexes from the base change along `Γ(X, U) → Γ(X, V)` of the matrix
complex of the sections over `U` to the matrix complex of the sections over `V`. -/
def restrictionHom :
    (P.toBoundedComplex.baseChange (X.presheaf.map (homOfLE h).op).hom).toCochainComplex ⟶
      Q.toBoundedComplex.toCochainComplex :=
  P.semilinearHom (X.presheaf.map (homOfLE h).op).hom Q (fun i => restrictionMap (ℳ.X i) h)
    (fun i x => restrictionMap_comm ℳ h i (i + 1) x)

/-- In degree `i` the morphism of matrix complexes given by restriction is multiplication by
the matrix of the restriction map. -/
@[simp] theorem restrictionHom_f (i : ℤ) :
    (restrictionHom ℳ h P Q).f i =
      ModuleCat.ofHom (restrictionMatrix ℳ h P Q i).mulVecLin := rfl

end Restriction

end Sections

end Stacks.Eta

end
