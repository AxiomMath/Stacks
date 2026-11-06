module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverVanishing
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard open covers as faithfully flat algebras

A finite standard open covering `D(f₁), …, D(f_m)` of `Spec R` gives a faithfully flat
`R`-algebra `A = ∏ᵢ R_{fᵢ}`, and the ring in degree `d` of the Čech conerve of `R → A` is the
product of the localizations at all `(d + 1)`-fold products of the `fᵢ`. Faithfully flat
descent along `R → A` therefore recovers the classical statements about a standard cover, and
the exactness of the Čech complex in higher degrees is the vanishing of the Čech cohomology of
a quasi-coherent sheaf on an affine.

## Main definitions

* `CommAlgCat.tensorPowObj` is the `n`-fold tensor power of a commutative algebra, built as an
  iterated binary cofan, with `CommAlgCat.tensorPowι` its coprojections and
  `CommAlgCat.tensorPowDesc` the map out of it determined by `n` maps.
* `CommAlgCat.cechConerveTensorPowEquiv` identifies degree `n` of the Čech conerve of `R ⟶ A`
  with the `(n + 1)`-fold tensor power of `A`.
* `Localization.awayTensorAwayEquiv` is the identification
  `R_a ⊗[R] R_b ≃ₐ[R] R_{a * b}`.
* `PrimeSpectrum.standardCoverCechDegreeEquiv` is the ring in each degree of the Čech conerve
  of a standard cover.

## Main results

* `PrimeSpectrum.faithfullyFlat_standardCoverAlgebra`: the product of the principal
  localizations of a standard cover is a faithfully flat `R`-algebra.
* `Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover` (elsewhere): the
  positive-degree Čech cohomology of a quasi-coherent sheaf on a finite standard cover of an
  affine vanishes.

## Implementation notes

The tensor power is built as an iterated binary cofan rather than as a concrete tensor power,
and its universal property is proved by hand (`tensorPowι_comp_tensorPowDesc` and
`tensorPowDesc_unique`) so that `tensorPowCoconeIsColimit` exhibits it as the wide pushout which
the Čech conerve is defined to be. The degreewise identification is then an algebra equivalence
and not merely a ring isomorphism.

The product of principal localizations is a dependent function type, so the degreewise
identification is assembled from `Algebra.TensorProduct.piRight`,
`Localization.awayTensorAwayEquiv` and the reindexing equivalences `AlgEquiv.piProdCurry` and
`Fin.consFunEquiv`.

## References

* [Stacks Project, Tag 023O](https://stacks.math.columbia.edu/tag/023O)
-/

@[expose] public section

open CategoryTheory Limits
open scoped MonoidalCategory TensorProduct

universe u

namespace CommAlgCat

/-- The `n`-fold tensor power of a commutative `R`-algebra `A` over `R`, built as an iterated
binary cofan in `CommAlgCat R`, with the empty power equal to `R`. -/
def tensorPowObj (R : Type u) [CommRing R] (A : CommAlgCat R) : ℕ → CommAlgCat R
  | 0 => CommAlgCat.of R R
  | n + 1 => (CommAlgCat.binaryCofan (tensorPowObj R A n) A).pt

/-- The `i`-th coprojection of `A` into its `n`-fold tensor power. -/
def tensorPowι (R : Type u) [CommRing R] (A : CommAlgCat R) :
    (n : ℕ) → Fin n → Quiver.Hom A (tensorPowObj R A n)
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases ((CommAlgCat.binaryCofan (tensorPowObj R A n) A).inr)
      (fun j => tensorPowι R A n j ≫ (CommAlgCat.binaryCofan (tensorPowObj R A n) A).inl) i

/-- The map out of the `n`-fold tensor power of `A` determined by `n` maps `A ⟶ B`. -/
def tensorPowDesc (R : Type u) [CommRing R] (A B : CommAlgCat R) :
    (n : ℕ) → (Fin n → Quiver.Hom A B) → Quiver.Hom (tensorPowObj R A n) B := fun n =>
  Nat.rec (motive := fun n => (Fin n → Quiver.Hom A B) → Quiver.Hom (tensorPowObj R A n) B)
    (fun (_ : Fin 0 → Quiver.Hom A B) =>
      CommAlgCat.ofHom (Algebra.ofId R B))
    (fun n ih (g : Fin (n + 1) → Quiver.Hom A B) =>
      BinaryCofan.IsColimit.desc (CommAlgCat.binaryCofanIsColimit (tensorPowObj R A n) A)
        (ih (fun i => g i.succ)) (g 0)) n

/-- Restricting `tensorPowDesc` along the first factor of the last binary cofan drops the
leading map. -/
theorem inl_comp_tensorPowDesc (R : Type u) [CommRing R] (A B : CommAlgCat R)
    (n : ℕ) (g : Fin (n + 1) → Quiver.Hom A B) :
    (CommAlgCat.binaryCofan (tensorPowObj R A n) A).inl ≫ tensorPowDesc R A B (n + 1) g =
      tensorPowDesc R A B n (fun i => g i.succ) := by
  exact BinaryCofan.IsColimit.inl_desc (CommAlgCat.binaryCofanIsColimit (tensorPowObj R A n) A) _ _

/-- Restricting `tensorPowDesc` along the second factor of the last binary cofan recovers the
leading map. -/
theorem inr_comp_tensorPowDesc (R : Type u) [CommRing R] (A B : CommAlgCat R)
    (n : ℕ) (g : Fin (n + 1) → Quiver.Hom A B) :
    (CommAlgCat.binaryCofan (tensorPowObj R A n) A).inr ≫ tensorPowDesc R A B (n + 1) g = g 0 := by
  exact BinaryCofan.IsColimit.inr_desc (CommAlgCat.binaryCofanIsColimit (tensorPowObj R A n) A) _ _

/-- `tensorPowDesc` restricts along the `i`-th coprojection to the `i`-th given map. -/
theorem tensorPowι_comp_tensorPowDesc (R : Type u) [CommRing R] (A B : CommAlgCat R)
    (n : ℕ) (g : Fin n → Quiver.Hom A B) (i : Fin n) :
    tensorPowι R A n i ≫ tensorPowDesc R A B n g = g i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases (inr_comp_tensorPowDesc R A B n g) (fun j => ?_) i
    let L : Quiver.Hom ((CommAlgCat.binaryCofan (tensorPowObj R A n) A).pt) B :=
      tensorPowDesc R A B (n + 1) g
    show (tensorPowι R A n j ≫ (CommAlgCat.binaryCofan (tensorPowObj R A n) A).inl) ≫ L = _
    rw [Category.assoc, show (CommAlgCat.binaryCofan (tensorPowObj R A n) A).inl ≫ L =
      tensorPowDesc R A B n (fun k => g k.succ) from inl_comp_tensorPowDesc R A B n g]
    exact ih _ j

/-- A map out of the `n`-fold tensor power is determined by its restrictions along the
coprojections. -/
theorem tensorPowDesc_unique (R : Type u) [CommRing R] (A B : CommAlgCat R)
    (n : ℕ) (g : Fin n → Quiver.Hom A B) (h : Quiver.Hom (tensorPowObj R A n) B)
    (hh : ∀ i, tensorPowι R A n i ≫ h = g i) :
    h = tensorPowDesc R A B n g := by
  induction n with
  | zero => exact CommAlgCat.hom_ext (by ext)
  | succ n ih =>
    change Quiver.Hom ((CommAlgCat.binaryCofan (tensorPowObj R A n) A).pt) B at h
    refine BinaryCofan.IsColimit.hom_ext
      (CommAlgCat.binaryCofanIsColimit (tensorPowObj R A n) A) ?_ ?_
    · exact (ih _ _ fun i => hh i.succ).trans (inl_comp_tensorPowDesc R A B n g).symm
    · exact (hh 0).trans (inr_comp_tensorPowDesc R A B n g).symm

/-- The wide-pushout diagram whose colimit is the `n`-fold tensor power of `A`. -/
def tensorPowDiagram (R : Type u) [CommRing R] (A : CommAlgCat R) (n : ℕ) :
    WidePushoutShape (Fin n) ⥤ CommAlgCat R :=
  WidePushoutShape.wideSpan (CommAlgCat.of R R) (fun _ : Fin n => A)
    (fun _ => CommAlgCat.ofHom (Algebra.ofId R A))

/-- The `n`-fold tensor power of `A`, as a cocone on `tensorPowDiagram`. -/
def tensorPowCocone (R : Type u) [CommRing R] (A : CommAlgCat R) (n : ℕ) :
    Cocone (tensorPowDiagram R A n) :=
  WidePushoutShape.mkCocone
    (CommAlgCat.ofHom (Algebra.ofId R (tensorPowObj R A n)))
    (fun i => tensorPowι R A n i)
    (fun _ => CommAlgCat.hom_ext (by ext))

/-- The `n`-fold tensor power of `A` is the colimit of `tensorPowDiagram`. -/
noncomputable def tensorPowCoconeIsColimit (R : Type u) [CommRing R] (A : CommAlgCat R) (n : ℕ) :
    IsColimit (tensorPowCocone R A n) := by
  refine IsColimit.mk (fun s => tensorPowDesc R A s.pt n fun i => s.ι.app (some i)) ?_
    fun s m hm => tensorPowDesc_unique R A s.pt n _ m fun i => hm (some i)
  intro s j
  cases j with
  | none => exact CommAlgCat.hom_ext (by ext)
  | some i => exact tensorPowι_comp_tensorPowDesc R A s.pt n _ i

/-- In degree `n` the Čech conerve of `R ⟶ A` is the `(n + 1)`-fold tensor power of `A`. -/
noncomputable def cechConerveTensorPowEquiv (R : Type u) [CommRing R]
    (A : CommAlgCat R) (n : ℕ) :
    ((Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))).cechConerve).obj (SimplexCategory.mk n)
      ≃ₐ[R] tensorPowObj R A (n+1) := by
  change widePushout (C := CommAlgCat R) (CommAlgCat.of R R) (fun _ : Fin (n+1) => A)
      (fun _ => CommAlgCat.ofHom (Algebra.ofId R A)) ≃ₐ[R] tensorPowObj R A (n+1)
  exact CommAlgCat.algEquivOfIso
    ((colimit.isColimit (tensorPowDiagram R A (n+1))).coconePointUniqueUpToIso
      (tensorPowCoconeIsColimit R A (n+1)))

end CommAlgCat

namespace Localization

/-- The tensor product of the localizations away from `a` and from `b` is the localization away
from `a * b`. -/
@[ega "III 6.7.1" "special case"]
noncomputable def awayTensorAwayEquiv (R : Type u) [CommRing R] (a b : R) :
    Localization.Away a ⊗[R] Localization.Away b ≃ₐ[R] Localization.Away (a*b) := by
  let T := Localization.Away (algebraMap R (Localization.Away a) b)
  let e : Localization.Away a ⊗[R] Localization.Away b ≃ₐ[Localization.Away a] T :=
    IsLocalization.Away.tensorEquiv (S := Localization.Away a) b (Localization.Away b)
  have : IsLocalization.Away (a*b) T := by
    simpa [T, mul_comm] using
      (inferInstance : IsLocalization.Away (b*a)
        (Localization.Away (algebraMap R (Localization.Away a) b)))
  exact (AlgEquiv.restrictScalars R e).trans
    (IsLocalization.algEquiv (Submonoid.powers (a*b)) T (Localization.Away (a*b)))

end Localization

namespace AlgEquiv

/-- Currying a doubly indexed product of `R`-algebras. -/
def piProdCurry (R : Type u) [CommRing R] {I J : Type*}
    (A : I → J → Type*) [∀ i j, CommRing (A i j)] [∀ i j, Algebra R (A i j)] :
    ((i : I) → (j : J) → A i j) ≃ₐ[R] ((p : I × J) → A p.1 p.2) where
  toFun x p := x p.1 p.2
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end AlgEquiv

namespace Fin

/-- Prepending an index: a function on `Fin (n + 1)` is a value together with a function on
`Fin n`. -/
def consFunEquiv (n m : ℕ) : Fin m × (Fin n → Fin m) ≃ (Fin (n+1) → Fin m) where
  toFun p := Fin.cons p.1 p.2
  invFun g := (g 0, fun j => g j.succ)
  left_inv p := by rcases p with ⟨i,t⟩; simp [Fin.cons]
  right_inv g := by funext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp [Fin.cons]

end Fin

namespace PrimeSpectrum

variable (R : Type u) [CommRing R] {m : ℕ} (f : Fin m → R)

/-- The product of the principal localizations of a standard cover is faithfully flat. -/
@[stacks 023O "faithfully flat product"]
public theorem faithfullyFlat_standardCoverAlgebra
    (hf : PrimeSpectrum.IsStandardOpenCoverOfSpectrum f) :
    Module.FaithfullyFlat R (∀ i : Fin m, Localization.Away (f i)) := by
  classical
  have hcover : (⨆ i : Fin m, PrimeSpectrum.basicOpen (f i)) = ⊤ := by
    simpa only [PrimeSpectrum.IsStandardOpenCoverOfSpectrum, PrimeSpectrum.IsStandardOpenCover,
      PrimeSpectrum.basicOpen_one] using hf
  have hspan := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hcover
  rw [← RingHom.faithfullyFlat_algebraMap_iff,
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R (Fin m) fun i => Localization.Away (f i)).symm),
    fun p => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin m, f i ∉ p.asIdeal := by
    by_contra! h
    have hle : Ideal.span (Set.range f) ≤ p.asIdeal := Ideal.span_le.2 (Set.range_subset_iff.2 h)
    exact p.2.ne_top (top_le_iff.mp (hspan ▸ hle))
  obtain ⟨q, hq⟩ :
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (f i)))) := by
    rw [PrimeSpectrum.localization_comap_range (R := R)
      (S := Localization.Away (f i)) (Submonoid.powers (f i))]
    exact (Ideal.disjoint_powers_iff_notMem_of_isPrime (f i)).2 hi
  refine ⟨q.comap (Pi.evalRingHom (fun j : Fin m => Localization.Away (f j)) i), ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  convert hq using 1
  ext x
  rfl

/-- The `(n + 1)`-fold tensor power of the product of the principal localizations of a standard
cover is the product of the localizations at all `(n + 1)`-fold products of its covering
elements. -/
noncomputable def standardCoverTensorPowEquiv (R : Type u) [CommRing R]
    (m : ℕ) (f : Fin m → R) : (n : ℕ) →
    (CommAlgCat.tensorPowObj R (CommAlgCat.of R (∀ i : Fin m, Localization.Away (f i))) (n+1)) ≃ₐ[R]
      (∀ t : Fin (n+1) → Fin m, Localization.Away (∏ j, f (t j)))
  | 0 => by
      change R ⊗[R] (∀ i : Fin m, Localization.Away (f i)) ≃ₐ[R] _
      let e₁ := Algebra.TensorProduct.lid R (∀ i : Fin m, Localization.Away (f i))
      let idx : Fin m ≃ (Fin 1 → Fin m) := {
        toFun := fun i _ => i
        invFun := fun t => t 0
        left_inv := fun i => rfl
        right_inv := fun t => by funext j; exact congrArg t (Subsingleton.elim 0 j)
      }
      let e₂ := AlgEquiv.piCongrLeft' R (fun i : Fin m => Localization.Away (f i)) idx
      let e₃ : (∀ t : Fin 1 → Fin m, Localization.Away (f (idx.symm t))) ≃ₐ[R]
          (∀ t : Fin 1 → Fin m, Localization.Away (∏ j : Fin 1, f (t j))) :=
        AlgEquiv.piCongrRight (R := R)
          (A₁ := fun t : Fin 1 → Fin m => Localization.Away (f (idx.symm t)))
          (A₂ := fun t : Fin 1 → Fin m => Localization.Away (∏ j : Fin 1, f (t j)))
          (fun t : Fin 1 → Fin m => by
            have h : f (idx.symm t) = ∏ j : Fin 1, f (t j) := by
              rw [Fin.prod_univ_succ]
              simp [idx]
            change Localization.Away (f (idx.symm t)) ≃ₐ[R]
              Localization.Away (∏ j : Fin 1, f (t j))
            rw [h])
      exact e₁.trans (e₂.trans e₃)
  | n+1 => by
      change (CommAlgCat.tensorPowObj R
            (CommAlgCat.of R (∀ i : Fin m, Localization.Away (f i))) (n+1)) ⊗[R]
          (∀ i : Fin m, Localization.Away (f i)) ≃ₐ[R] _
      let e₁ := Algebra.TensorProduct.piRight R R
        (CommAlgCat.tensorPowObj R (CommAlgCat.of R (∀ i : Fin m, Localization.Away (f i))) (n+1))
        (fun i : Fin m => Localization.Away (f i))
      let e₂ := AlgEquiv.piCongrRight (fun i : Fin m =>
        Algebra.TensorProduct.congr (standardCoverTensorPowEquiv R m f n)
          (AlgEquiv.refl (R := R) (A₁ := Localization.Away (f i))))
      let e₃ := AlgEquiv.piCongrRight (fun i : Fin m =>
        Algebra.TensorProduct.comm R
          (∀ t : Fin (n+1) → Fin m, Localization.Away (∏ j, f (t j))) (Localization.Away (f i)))
      let e₄ := AlgEquiv.piCongrRight (fun i : Fin m =>
        Algebra.TensorProduct.piRight R R (Localization.Away (f i))
          (fun t : Fin (n+1) → Fin m => Localization.Away (∏ j, f (t j))))
      let e₅ := AlgEquiv.piCongrRight (fun i : Fin m =>
        AlgEquiv.piCongrRight (fun t : Fin (n+1) → Fin m =>
          Localization.awayTensorAwayEquiv R (f i) (∏ j, f (t j))))
      let e₆ := AlgEquiv.piProdCurry R (fun (i : Fin m) (t : Fin (n+1) → Fin m) =>
        Localization.Away (f i * ∏ j, f (t j)))
      let e₇ := AlgEquiv.piCongrLeft' R
        (fun p : Fin m × (Fin (n+1) → Fin m) => Localization.Away (f p.1 * ∏ j, f (p.2 j)))
        (Fin.consFunEquiv (n+1) m)
      let e₈ : (∀ t : Fin (n+2) → Fin m,
          Localization.Away (f ((Fin.consFunEquiv (n+1) m).symm t).1 *
            ∏ j, f (((Fin.consFunEquiv (n+1) m).symm t).2 j))) ≃ₐ[R]
          (∀ t : Fin (n+2) → Fin m, Localization.Away (∏ j, f (t j))) :=
        AlgEquiv.piCongrRight (R := R)
          (A₁ := fun t : Fin (n+2) → Fin m =>
            Localization.Away (f ((Fin.consFunEquiv (n+1) m).symm t).1 *
              ∏ j, f (((Fin.consFunEquiv (n+1) m).symm t).2 j)))
          (A₂ := fun t : Fin (n+2) → Fin m => Localization.Away (∏ j, f (t j)))
          (fun t : Fin (n+2) → Fin m => by
            have hd : f (t 0) * ∏ j : Fin (n+1), f (t j.succ) = ∏ j : Fin (n+2), f (t j) :=
              (Fin.prod_univ_succ fun j => f (t j)).symm
            change Localization.Away (f (t 0) * ∏ j : Fin (n+1), f (t j.succ)) ≃ₐ[R]
              Localization.Away (∏ j : Fin (n+2), f (t j))
            rw [hd])
      exact e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans (e₇.trans e₈))))))

/-- In degree `d`, the Čech algebra of a standard cover is the product of the
localizations at all `(d + 1)`-fold products of its covering elements. -/
@[stacks 023O "degree-wise Čech algebra"]
public noncomputable def standardCoverCechDegreeEquiv (d : ℕ) :
    ((Arrow.mk (CommAlgCat.ofHom
      (Algebra.ofId R (∀ i : Fin m, Localization.Away (f i))))).cechConerve).obj
        (SimplexCategory.mk d) ≃ₐ[R]
      (∀ i : Fin (d + 1) → Fin m, Localization.Away (∏ j, f (i j))) :=
  (CommAlgCat.cechConerveTensorPowEquiv R
    (CommAlgCat.of R (∀ i : Fin m, Localization.Away (f i))) d).trans
    (standardCoverTensorPowEquiv R m f d)

add_to_stacks 023O "Čech cohomology vanishing"
  Stacks.Cohomology.Cech.isZero_cechCohomology_of_isStandardOpenCover

end PrimeSpectrum

end
