module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PolynomialTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.UnitsSheafStalk
public import StacksFrontier.RingTheory.Henselian.StrictlyHenselianOfStandardEtaleRoots

/-!
# Exact functors carry strictly henselian sheaves of rings to strictly henselian rings

Let `X` be a ringed topos and `q` a functor from sheaves of sets on `X` to sets which preserves
finite limits and is a left adjoint — a point of the topos, or the composite of the inverse image
of a morphism of topoi with such a point.  Then `q(O_X)` is a ring (with the transported
operations) and this file shows that it is local, respectively strictly henselian, as soon as
`O_X` is so *locally*: every section `a` has, locally, `a` or `1 - a` invertible; and every
monic polynomial whose standard étale algebra has nonzero fibres over the locus where some unit
`c` lives has, locally, a root at which `g f'` is invertible.  These are steps of the proof of
Stacks 04KL, which recovers a morphism of algebraic spaces from a morphism of their small étale
ringed topoi by reading off strictly henselian local rings at points.

The local property is the image of the epimorphism `O^* ⨿ O^* ⟶ O`, `(u, v) ↦ (u, 1 - v)`.  The
henselian property goes through the root criterion `strictlyHenselianLocalRing_of_exists_root`:
the polynomials are specialized from universal ones with coefficients in
`MvPolynomial ι (ULift ℤ)`, so that the non-nilpotence condition becomes the invertibility of one
of finitely many universal polynomials `p` in the coefficients
(`AdjoinRoot.exists_coeffs_not_isNilpotent_iff`), and the roots are the points of a finite limit
`rootLocus` over the locus `N ⊆ O^ι` where `p` is invertible.  The hypothesis makes the projection
from the root locus to `N` locally surjective, `q` makes it surjective, and the transport of
polynomial maps along `q` turns a point of `q(rootLocus)` into a root.

## Main results

* `AlgebraicGeometry.RingedTopos.isLocalRing_map_of_isUnit_or_isUnit_one_sub`: `q(O_X)` is
  local.
* `AlgebraicGeometry.RingedTopos.exists_root_map_of_local_roots`: local roots of a polynomial
  with universal coefficients give roots in `q(O_X)`.
* `AlgebraicGeometry.RingedTopos.strictlyHenselianLocalRing_map`: `q(O_X)` is strictly
  henselian.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial

universe t w v u

/-! ### Evaluating integral polynomials -/

namespace MvPolynomial

variable {ι : Type*}

/-- The unique ring homomorphism from `ULift ℤ`. -/
def uliftIntCast (S : Type*) [Ring S] : ULift.{w} ℤ →+* S :=
  (Int.castRingHom S).comp ULift.ringEquiv.toRingHom

/-- Every ring homomorphism from `ULift ℤ` is `MvPolynomial.uliftIntCast`. -/
theorem eq_uliftIntCast {S : Type*} [Ring S] (f : ULift.{w} ℤ →+* S) : f = uliftIntCast S := by
  ext x
  have h := RingHom.ext_int (f.comp ULift.ringEquiv.symm.toRingHom)
    ((uliftIntCast S).comp ULift.ringEquiv.symm.toRingHom)
  exact congrArg (fun φ : ℤ →+* S => φ x.down) h

/-- Evaluation of a polynomial with coefficients in `ULift ℤ` at a family of elements of a
commutative ring. -/
def evalULiftInt (S : Type*) [CommRing S] (s : ι → S) : MvPolynomial ι (ULift.{w} ℤ) →+* S :=
  eval₂Hom (uliftIntCast S) s

/-- Evaluation of integral polynomials commutes with ring homomorphisms. -/
theorem comp_evalULiftInt {S S' : Type*} [CommRing S] [CommRing S'] (k : S →+* S') (s : ι → S) :
    k.comp (evalULiftInt.{w} S s) = evalULiftInt S' (k ∘ s) := by
  rw [evalULiftInt, comp_eval₂Hom, eq_uliftIntCast (k.comp (uliftIntCast S))]
  rfl

/-- Evaluation of integral polynomials commutes with ring homomorphisms, elementwise. -/
theorem map_evalULiftInt {S S' : Type*} [CommRing S] [CommRing S'] (k : S →+* S') (s : ι → S)
    (p : MvPolynomial ι (ULift.{w} ℤ)) :
    k (evalULiftInt S s p) = evalULiftInt S' (k ∘ s) p :=
  RingHom.congr_fun (comp_evalULiftInt k s) p

/-- A ring homomorphism applied to the value of a one-variable polynomial with integral
polynomial coefficients. -/
theorem map_eval₂_evalULiftInt {S S' : Type*} [CommRing S] [CommRing S'] (k : S →+* S')
    (s : ι → S) (F : (MvPolynomial ι (ULift.{w} ℤ))[X]) (r : S) :
    k (F.eval₂ (evalULiftInt S s) r) = (F.map (evalULiftInt S' (k ∘ s))).eval (k r) := by
  rw [Polynomial.hom_eval₂, comp_evalULiftInt, Polynomial.eval_map]

/-- `MvPolynomial.evalULiftInt` at a variable. -/
@[simp]
theorem evalULiftInt_X {S : Type*} [CommRing S] (s : ι → S) (i : ι) :
    evalULiftInt.{w} S s (X i) = s i :=
  eval₂Hom_X' _ _ i

/-- The universal monic polynomial of degree `d`, with the coefficients below the top one as
variables. -/
def universalMonic (d m : ℕ) : (MvPolynomial (Fin d ⊕ Fin (m + 1)) (ULift.{w} ℤ))[X] :=
  Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (X (Sum.inl j)) * Polynomial.X ^ (j : ℕ)

/-- The universal polynomial of degree at most `m`. -/
def universalPoly (d m : ℕ) : (MvPolynomial (Fin d ⊕ Fin (m + 1)) (ULift.{w} ℤ))[X] :=
  ∑ k : Fin (m + 1), Polynomial.C (X (Sum.inr k)) * Polynomial.X ^ (k : ℕ)

/-- The universal monic polynomial is monic. -/
theorem universalMonic_monic (d m : ℕ) : (universalMonic.{w} d m).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)

/-- Specializing the universal monic polynomial at the coefficients of a monic polynomial of
degree `d` gives it back. -/
theorem map_universalMonic {S : Type*} [CommRing S] {f : S[X]} (hf : f.Monic) (m : ℕ)
    (y : Fin (m + 1) → S) :
    (universalMonic.{w} f.natDegree m).map
      (evalULiftInt S (Sum.elim (fun j : Fin f.natDegree => f.coeff j) y)) = f := by
  conv_rhs => rw [hf.as_sum]
  simp only [universalMonic, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, evalULiftInt_X, Sum.elim_inl]
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (f.coeff i) * Polynomial.X ^ i)]

/-- Specializing the universal polynomial of degree at most `m` at the coefficients of a
polynomial of degree `m` gives it back. -/
theorem map_universalPoly {S : Type*} [CommRing S] (d : ℕ) (x : Fin d → S) (g : S[X]) :
    (universalPoly.{w} d g.natDegree).map
      (evalULiftInt S (Sum.elim x (fun k : Fin (g.natDegree + 1) => g.coeff k))) = g := by
  conv_rhs => rw [g.as_sum_range_C_mul_X_pow]
  simp only [universalPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, evalULiftInt_X, Sum.elim_inr]
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (g.coeff i) * Polynomial.X ^ i)]

end MvPolynomial

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Surjectivity after a left adjoint -/

/-- A morphism of sheaves of sets is locally surjective as soon as every section of the target
lifts locally along it. -/
theorem isLocallySurjective_of_exists {A B : Sheaf J (Type w)} (φ : A ⟶ B)
    (h : ∀ (W : C) (s : B.obj.obj (op W)), ∃ T : Sieve W, T ∈ J W ∧
      ∀ ⦃W' : C⦄ (i : W' ⟶ W), T i →
        ∃ a : A.obj.obj (op W'), φ.hom.app (op W') a = B.obj.map i.op s) :
    Presheaf.IsLocallySurjective J φ.hom where
  imageSieve_mem {W} s := by
    obtain ⟨T, hT, hTs⟩ := h W s
    exact J.superset_covering (fun W' i hi ↦ hTs i hi) hT

/-- A left adjoint from sheaves of sets to sets carries a locally surjective morphism to a
surjective map: the morphism is an epimorphism and left adjoints preserve epimorphisms. -/
theorem surjective_map_of_isLocallySurjective (q : Sheaf J (Type w) ⥤ Type t) [q.IsLeftAdjoint]
    {A B : Sheaf J (Type w)} (φ : A ⟶ B) [Presheaf.IsLocallySurjective J φ.hom] :
    Function.Surjective (q.map φ) :=
  (epi_iff_surjective _).mp (q.map_epi φ)

/-- An element of the image of a binary coproduct under a functor to sets preserving it comes
from one of the two summands. -/
theorem exists_map_inl_or_map_inr {D : Type*} [Category D] (q : D ⥤ Type t) {A B : D}
    [HasBinaryCoproduct A B] [PreservesColimit (pair A B) q] (y : q.obj (A ⨿ B)) :
    (∃ a, q.map coprod.inl a = y) ∨ (∃ b, q.map coprod.inr b = y) := by
  set e := PreservesColimitPair.iso q A B
  have hy : e.hom (e.inv y) = y := by simp
  have hinl : ∀ a, e.hom ((coprod.inl : q.obj A ⟶ q.obj A ⨿ q.obj B) a) = q.map coprod.inl a :=
    fun a ↦ (types_comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom (coprodComparison_inl (F := q) (A := A) (B := B)) a)
  have hinr : ∀ b, e.hom ((coprod.inr : q.obj B ⟶ q.obj A ⨿ q.obj B) b) = q.map coprod.inr b :=
    fun b ↦ (types_comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom (coprodComparison_inr (F := q) (A := A) (B := B)) b)
  set x := e.inv y
  have hx : (Types.binaryCoproductIso _ _).inv ((Types.binaryCoproductIso _ _).hom x) = x := by
    simp
  rcases hs : (Types.binaryCoproductIso (q.obj A) (q.obj B)).hom x with a | b
  · left
    refine ⟨a, ?_⟩
    rw [← hinl, ← hy]
    congr 1
    rw [← hx, hs]
    exact ((types_comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inl_comp_inv (q.obj A) (q.obj B)) a)).symm
  · right
    refine ⟨b, ?_⟩
    rw [← hinr, ← hy]
    congr 1
    rw [← hx, hs]
    exact ((types_comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom
      (Types.binaryCoproductIso_inr_comp_inv (q.obj A) (q.obj B)) b)).symm

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.RingedTopos

open CategoryTheory.Sheaf

variable (X : RingedTopos.{v, u, w}) [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sections of the underlying sheaf of rings of the structure sheaf of a ringed topos
commute. -/
theorem sections_mul_comm (Z : X.Cᵒᵖ)
    (x y : (sectionsFunctor X.J Z).obj (ringSheaf (ringStructureSheaf X))) : x * y = y * x :=
  mul_comm (G := X.O.obj.obj Z) x y

/-- The endomorphism `a ↦ 1 - a` of the underlying sheaf of sets of the structure sheaf. -/
def oneSubHom : ringSheaf (ringStructureSheaf X) ⟶ ringSheaf (ringStructureSheaf X) :=
  1 - 𝟙 _

variable (q : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits q]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- After a left-exact functor to sets, `oneSubHom` is `a ↦ 1 - a` in the transported ring. -/
theorem map_oneSubHom_apply (x : q.obj (ringSheaf (ringStructureSheaf X))) :
    letI := ringObjRing (ringStructureSheaf X) q
    q.map (oneSubHom X) x = 1 - x := by
  let := ringObjRing (ringStructureSheaf X) q
  refine (map_sub (evalRingHom q x) 1 (𝟙 _)).trans ?_
  rw [map_one, evalRingHom_apply, q.map_id, types_id_apply]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On sections, `oneSubHom` is `a ↦ 1 - a`. -/
theorem sectionsFunctor_map_oneSubHom (Z : X.Cᵒᵖ)
    (x : (sectionsFunctor X.J Z).obj (ringSheaf (ringStructureSheaf X))) :
    (sectionsFunctor X.J Z).map (oneSubHom X) x = 1 - x := by
  refine (map_sub (sectionsEvalRingHom Z x) 1 (𝟙 _)).trans ?_
  rw [map_one, sectionsEvalRingHom_apply, (sectionsFunctor X.J Z).map_id, types_id_apply]

/-- The morphism `O^* ⨿ O^* ⟶ O` which is the inclusion on the first summand and `u ↦ 1 - u` on
the second. It is locally surjective exactly when, locally, every section `a` or `1 - a` is
invertible. -/
def unitsOrOneSub [HasBinaryCoproduct (units X) (units X)] :
    units X ⨿ units X ⟶ ringSheaf (ringStructureSheaf X) :=
  coprod.desc (unitsIncl X) (unitsIncl X ≫ oneSubHom X)

/-- **A left-exact left adjoint carries a sheaf of rings that is locally local to a local ring.**
Let `X` be a ringed topos in which every section `a` of `O_X` is, locally, invertible or has
`1 - a` invertible, and let `q` be a left-exact functor from sheaves of sets to sets which is a
left adjoint.  If the ring `q(O_X)` is nonzero, it is local.

The morphism `O^* ⨿ O^* ⟶ O`, `(u, v) ↦ (u, 1 - v)`, is locally surjective, hence an epimorphism;
`q` carries it to a surjection and preserves the coproduct, and carries `O^*` to the units of
`q(O_X)` (`AlgebraicGeometry.RingedTopos.isUnit_iff_exists_map_unitsIncl`). -/
theorem isLocalRing_map_of_isUnit_or_isUnit_one_sub [HasBinaryCoproduct (units X) (units X)]
    [q.IsLeftAdjoint] [Nontrivial (q.obj (ringSheaf (ringStructureSheaf X)))]
    (hloc : ∀ (W : X.C) (a : X.O.obj.obj (op W)), ∃ T : Sieve W, T ∈ X.J W ∧
      ∀ ⦃W' : X.C⦄ (i : W' ⟶ W), T i →
        IsUnit ((X.O.obj.map i.op) a) ∨ IsUnit ((X.O.obj.map i.op) (1 - a))) :
    letI := ringObjCommRing (sections_mul_comm X) q
    IsLocalRing (q.obj (ringSheaf (ringStructureSheaf X))) := by
  let := ringObjCommRing (sections_mul_comm X) q
  have : Presheaf.IsLocallySurjective X.J (unitsOrOneSub X).hom := by
    refine isLocallySurjective_of_exists _ fun W s ↦ ?_
    obtain ⟨T, hT, hTs⟩ := hloc W s
    refine ⟨T, hT, fun W' i hi ↦ ?_⟩
    set F := sectionsFunctor X.J (op W')
    rcases hTs i hi with ⟨v, hv⟩ | ⟨v, hv⟩
    · refine ⟨F.map coprod.inl (unitsMk X (op W') (v.1 : F.obj (ringSheaf (ringStructureSheaf X)))
        v.2 v.3), ?_⟩
      show F.map (unitsOrOneSub X) (F.map coprod.inl _) = _
      rw [← F.map_comp_apply, unitsOrOneSub, coprod.inl_desc]
      exact hv
    · refine ⟨F.map coprod.inr (unitsMk X (op W') (v.1 : F.obj (ringSheaf (ringStructureSheaf X)))
        v.2 v.3), ?_⟩
      show F.map (unitsOrOneSub X) (F.map coprod.inr _) = _
      rw [← F.map_comp_apply, unitsOrOneSub, coprod.inr_desc, F.map_comp_apply,
        sectionsFunctor_map_oneSubHom]
      show 1 - (v.1 : X.O.obj.obj (op W')) = (X.O.obj.map i.op) s
      rw [hv]
      exact (congrArg (1 - ·) (((X.O.obj.map i.op).hom.map_sub 1 s).trans
        (congrArg (· - _) (X.O.obj.map i.op).hom.map_one))).trans (sub_sub_cancel _ _)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  obtain ⟨y, rfl⟩ := surjective_map_of_isLocallySurjective q (unitsOrOneSub X) a
  rcases exists_map_inl_or_map_inr q y with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · left
    rw [← q.map_comp_apply, unitsOrOneSub, coprod.inl_desc]
    exact (isUnit_iff_exists_map_unitsIncl X q _).mpr ⟨u, rfl⟩
  · right
    rw [← q.map_comp_apply, unitsOrOneSub, coprod.inr_desc, q.map_comp_apply,
      map_oneSubHom_apply, sub_sub_cancel]
    exact (isUnit_iff_exists_map_unitsIncl X q _).mpr ⟨u, rfl⟩

/-! ### Roots of polynomials -/

section Roots

open MvPolynomial

variable [q.IsLeftAdjoint] {ι : Type} [Finite ι] (F E : (MvPolynomial ι (ULift.{w} ℤ))[X])
  (p : MvPolynomial ι (ULift.{w} ℤ))

/-- The coefficient sheaf `O^ι`. -/
abbrev coeffSheaf (ι : Type) [Finite ι] : Sheaf X.J (Type w) :=
  ∏ᶜ (fun _ : ι => ringSheaf (ringStructureSheaf X))

/-- The value of the integral polynomial `p` at the coordinates of `O^ι`. -/
def coeffPolyHom : coeffSheaf X ι ⟶ ringSheaf (ringStructureSheaf X) :=
  letI := homCommRing (sections_mul_comm X) (coeffSheaf X ι)
  evalULiftInt _ (fun k => Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k) p

/-- The locus `N ⊆ O^ι` where `p` is invertible. -/
abbrev unitLocus : Sheaf X.J (Type w) := pullback (coeffPolyHom X p) (unitsIncl X)

/-- The coefficients and a candidate root: `N × O`. -/
abbrev rootCandidates : Sheaf X.J (Type w) :=
  unitLocus X p ⨯ ringSheaf (ringStructureSheaf X)

/-- The coefficient coordinates on `N × O`. -/
def rootCoeff (k : ι) : rootCandidates X p ⟶ ringSheaf (ringStructureSheaf X) :=
  prod.fst ≫ pullback.fst _ _ ≫ Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k

/-- The value of a one-variable polynomial with integral polynomial coefficients on `N × O`:
its coefficients evaluated at the coefficient coordinates, evaluated at the root coordinate. -/
def rootPolyHom (G : (MvPolynomial ι (ULift.{w} ℤ))[X]) :
    rootCandidates X p ⟶ ringSheaf (ringStructureSheaf X) :=
  letI := homCommRing (sections_mul_comm X) (rootCandidates X p)
  G.eval₂ (evalULiftInt _ (rootCoeff X p)) prod.snd

/-- The zero locus of `F` in `N × O`. -/
abbrev rootLocus₁ : Sheaf X.J (Type w) :=
  pullback (rootPolyHom X p F) (ringZeroHom (ringStructureSheaf X))

/-- The locus in `N × O` where `F` vanishes and `E` is invertible. -/
abbrev rootLocus : Sheaf X.J (Type w) :=
  pullback (pullback.fst _ _ ≫ rootPolyHom X p E : rootLocus₁ X F p ⟶ _) (unitsIncl X)

/-- The projection from the root locus to the coefficients. -/
def rootLocusπ : rootLocus X F E p ⟶ unitLocus X p :=
  pullback.fst _ _ ≫ pullback.fst _ _ ≫ prod.fst

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Applying a finite-limit preserving functor to sets and evaluating, on the coefficient
sheaf. -/
theorem map_coeffPolyHom (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P]
    (z : P.obj (coeffSheaf X ι)) :
    letI := ringObjCommRing (sections_mul_comm X) P
    P.map (coeffPolyHom X p) z =
      evalULiftInt _ (fun k => P.map (Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k) z)
        p := by
  let := homCommRing (sections_mul_comm X) (coeffSheaf X ι)
  let := ringObjCommRing (sections_mul_comm X) P
  exact map_evalULiftInt (evalRingHom (R := ringStructureSheaf X) P z) _ p

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Applying a finite-limit preserving functor to sets and evaluating, on `N × O`: the
polynomial with coefficients evaluated at the coefficient coordinates, evaluated at the root
coordinate, computed in the transported ring. -/
theorem map_rootPolyHom (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P]
    (G : (MvPolynomial ι (ULift.{w} ℤ))[X]) (z : P.obj (rootCandidates X p)) :
    letI := ringObjCommRing (sections_mul_comm X) P
    P.map (rootPolyHom X p G) z =
      (G.map (evalULiftInt _ (fun k => P.map (rootCoeff X p k) z))).eval (P.map prod.snd z) := by
  let := homCommRing (sections_mul_comm X) (rootCandidates X p)
  let := ringObjCommRing (sections_mul_comm X) P
  exact map_eval₂_evalULiftInt (evalRingHom (R := ringStructureSheaf X) P z) _ G _

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The zero section after a finite-limit preserving functor to sets is the transported zero. -/
theorem map_ringZeroHom_apply (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P]
    (x : P.obj (⊤_ Sheaf X.J (Type w))) :
    letI := ringObjRing (ringStructureSheaf X) P
    P.map (ringZeroHom (ringStructureSheaf X)) x = 0 :=
  congrArg (P.map (ringZeroHom (ringStructureSheaf X))) (Subsingleton.elim _ _)

/-- **A point of the root locus gives a root.** After a finite-limit preserving functor `P` to
sets, a point of the root locus lies over a point `z` of `N × O` at which `F` vanishes and `E`
is invertible. -/
theorem map_rootPolyHom_of_rootLocus (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P]
    (r : P.obj (rootLocus X F E p)) :
    letI := ringObjCommRing (sections_mul_comm X) P
    P.map (rootPolyHom X p F) (P.map (pullback.fst _ _ ≫ pullback.fst _ _) r) = 0 ∧
      IsUnit (P.map (rootPolyHom X p E) (P.map (pullback.fst _ _ ≫ pullback.fst _ _) r)) := by
  let := ringObjCommRing (sections_mul_comm X) P
  refine ⟨?_, ?_⟩
  · rw [← P.map_comp_apply, Category.assoc, pullback.condition, ← Category.assoc,
      P.map_comp_apply]
    exact map_ringZeroHom_apply X P _
  · rw [← P.map_comp_apply, Category.assoc, pullback.condition, P.map_comp_apply]
    exact (isUnit_iff_exists_map_unitsIncl X P _).mpr ⟨_, rfl⟩

/-- A point `(n, a)` of `N × O` at which `F` vanishes and `E` is a unit of `O` comes, after a
finite-limit preserving functor `P` to sets, from a point of the root locus over `n`. -/
private theorem exists_rootLocus_of_eq {X : RingedTopos.{v, u, w}}
    [X.J.HasSheafCompose (forget RingCat.{w})] (F E : (MvPolynomial ι (ULift.{w} ℤ))[X])
    (p : MvPolynomial ι (ULift.{w} ℤ)) (P : Sheaf X.J (Type w) ⥤ Type t)
    [PreservesFiniteLimits P] (n : P.obj (unitLocus X p))
    (a : P.obj (ringSheaf (ringStructureSheaf X)))
    (u : P.obj (units X))
    (hF : P.map (rootPolyHom X p F) (Functor.prodObjMk n a) =
      P.map (ringZeroHom (ringStructureSheaf X)) (default : P.obj (⊤_ Sheaf X.J (Type w))))
    (hE : P.map (rootPolyHom X p E) (Functor.prodObjMk n a) = P.map (unitsIncl X) u) :
    ∃ r : P.obj (rootLocus X F E p), P.map (rootLocusπ X F E p) r = n := by
  obtain ⟨r₁, hr₁, -⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback (rootPolyHom X p F) (ringZeroHom (ringStructureSheaf X))).map P)
    (Functor.prodObjMk n a) default hF
  obtain ⟨r, hr, -⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback
      (pullback.fst _ _ ≫ rootPolyHom X p E : rootLocus₁ X F p ⟶ _) (unitsIncl X)).map P)
    r₁ u (by rw [P.map_comp_apply, hr₁, hE])
  refine ⟨r, ?_⟩
  rw [rootLocusπ, P.map_comp_apply, P.map_comp_apply, hr, hr₁, Functor.map_fst_prodObjMk]

/-- **A root gives a point of the root locus.** After a finite-limit preserving functor `P` to
sets, a point `n` of `N` and a point `a` of `O` at which `F` vanishes and `E` is invertible
come from a point of the root locus over `n`. -/
theorem exists_rootLocus_of (P : Sheaf X.J (Type w) ⥤ Type t) [PreservesFiniteLimits P]
    (n : P.obj (unitLocus X p)) (a : P.obj (ringSheaf (ringStructureSheaf X))) :
    letI := ringObjCommRing (sections_mul_comm X) P
    P.map (rootPolyHom X p F) (Functor.prodObjMk n a) = 0 →
      IsUnit (P.map (rootPolyHom X p E) (Functor.prodObjMk n a)) →
      ∃ r : P.obj (rootLocus X F E p), P.map (rootLocusπ X F E p) r = n := by
  let := ringObjCommRing (sections_mul_comm X) P
  intro hF hE
  obtain ⟨u, hu⟩ := (isUnit_iff_exists_map_unitsIncl X P _).mp hE
  exact exists_rootLocus_of_eq F E p P n a u (hF.trans (map_ringZeroHom_apply X P _).symm) hu.symm

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `AlgebraicGeometry.RingedTopos.map_coeffPolyHom` on sections, computed in the ring of
sections. -/
theorem sectionsFunctor_map_coeffPolyHom (W : X.Cᵒᵖ)
    (z : (sectionsFunctor X.J W).obj (coeffSheaf X ι)) :
    (sectionsFunctor X.J W).map (coeffPolyHom X p) z =
      evalULiftInt (X.O.obj.obj W)
        (fun k => (sectionsFunctor X.J W).map
          (Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k) z) p := by
  let := homCommRing (sections_mul_comm X) (coeffSheaf X ι)
  let := ringSectionsCommRing (sections_mul_comm X) W
  exact map_evalULiftInt (sectionsEvalRingHom (R := ringStructureSheaf X) W z) _ p

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `AlgebraicGeometry.RingedTopos.map_rootPolyHom` on sections, computed in the ring of
sections. -/
theorem sectionsFunctor_map_rootPolyHom (W : X.Cᵒᵖ) (G : (MvPolynomial ι (ULift.{w} ℤ))[X])
    (z : (sectionsFunctor X.J W).obj (rootCandidates X p)) :
    (sectionsFunctor X.J W).map (rootPolyHom X p G) z =
      (G.map (evalULiftInt (X.O.obj.obj W)
        (fun k => (sectionsFunctor X.J W).map (rootCoeff X p k) z))).eval
        ((sectionsFunctor X.J W).map prod.snd z) := by
  let := homCommRing (sections_mul_comm X) (rootCandidates X p)
  let := ringSectionsCommRing (sections_mul_comm X) W
  exact map_eval₂_evalULiftInt (sectionsEvalRingHom (R := ringStructureSheaf X) W z) _ G _

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `AlgebraicGeometry.RingedTopos.exists_rootLocus_of` on sections, with the ring of
sections. -/
theorem exists_rootLocus_of_sections (W : X.Cᵒᵖ)
    (n : (sectionsFunctor X.J W).obj (unitLocus X p)) (a : X.O.obj.obj W)
    (hF : (sectionsFunctor X.J W).map (rootPolyHom X p F)
      (Functor.prodObjMk n (a : (sectionsFunctor X.J W).obj (ringSheaf (ringStructureSheaf X))))
        = (0 : X.O.obj.obj W))
    (hE : IsUnit (M := X.O.obj.obj W) ((sectionsFunctor X.J W).map (rootPolyHom X p E)
      (Functor.prodObjMk n (a : (sectionsFunctor X.J W).obj (ringSheaf (ringStructureSheaf X)))))) :
    ∃ r : (sectionsFunctor X.J W).obj (rootLocus X F E p),
      (sectionsFunctor X.J W).map (rootLocusπ X F E p) r = n := by
  obtain ⟨v, hv⟩ := hE
  exact exists_rootLocus_of_eq F E p (sectionsFunctor X.J W : Sheaf X.J (Type w) ⥤ Type w) n a
    (unitsMk X W (v.1 : (sectionsFunctor X.J W).obj (ringSheaf (ringStructureSheaf X))) v.2 v.3)
    hF hv.symm

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Local roots make the root locus locally surjective over the coefficients.** If, for every
family of sections `s` of `O` over `W` at which `p` is invertible, the polynomial `F` with
coefficients evaluated at `s` has, locally on `W`, a root at which `E` is invertible, then the
projection from the root locus to the locus `N` where `p` is invertible is locally surjective. -/
theorem isLocallySurjective_rootLocusπ
    (h : ∀ (W : X.C) (s : ι → X.O.obj.obj (op W)), IsUnit (evalULiftInt _ s p) →
      ∃ T : Sieve W, T ∈ X.J W ∧ ∀ ⦃W' : X.C⦄ (i : W' ⟶ W), T i →
        ∃ a : X.O.obj.obj (op W'),
          (F.map (evalULiftInt _ (fun k => X.O.obj.map i.op (s k)))).eval a = 0 ∧
          IsUnit ((E.map (evalULiftInt _ (fun k => X.O.obj.map i.op (s k)))).eval a)) :
    Presheaf.IsLocallySurjective X.J (rootLocusπ X F E p).hom := by
  refine isLocallySurjective_of_exists _ fun W n₀ ↦ ?_
  set P := sectionsFunctor X.J (op W)
  set n : P.obj (unitLocus X p) := n₀
  set s : ι → X.O.obj.obj (op W) := fun k =>
    P.map (pullback.fst _ _ ≫ Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k) n
  have hu : IsUnit (evalULiftInt _ s p) := by
    have hc := congrArg (fun m => P.map m n) (pullback.condition (f := coeffPolyHom X p)
      (g := unitsIncl X))
    dsimp only at hc
    rw [P.map_comp_apply, P.map_comp_apply, sectionsFunctor_map_coeffPolyHom] at hc
    refine ⟨P.map (pullback.snd _ _) n, Eq.trans ?_ hc.symm⟩
    congr 1
  obtain ⟨T, hT, hTs⟩ := h W s hu
  refine ⟨T, hT, fun W' i hi ↦ ?_⟩
  obtain ⟨a, haF, haE⟩ := hTs i hi
  set P' := sectionsFunctor X.J (op W')
  set n' : P'.obj (unitLocus X p) := (unitLocus X p).obj.map i.op n
  have hcoeff : ∀ k, P'.map (rootCoeff X p k)
      (Functor.prodObjMk (B := ringSheaf (ringStructureSheaf X)) n' a) =
        X.O.obj.map i.op (s k) := by
    intro k
    refine (P'.map_comp_apply prod.fst
      (pullback.fst _ _ ≫ Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k) _).trans ?_
    refine (congrArg (P'.map (pullback.fst _ _ ≫
      Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k))
      (Functor.map_fst_prodObjMk (P := P') (B := ringSheaf (ringStructureSheaf X)) n' a)).trans ?_
    exact NatTrans.naturality_apply
      (pullback.fst _ _ ≫ Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k).hom i.op n
  have hroot : P'.map prod.snd
      (Functor.prodObjMk (B := ringSheaf (ringStructureSheaf X)) n' a) = a :=
    Functor.map_snd_prodObjMk _ _
  have hfun : (fun k => P'.map (rootCoeff X p k)
      (Functor.prodObjMk (B := ringSheaf (ringStructureSheaf X)) n' a)) =
      fun k => X.O.obj.map i.op (s k) := funext hcoeff
  obtain ⟨r, hr⟩ := exists_rootLocus_of_sections X F E p (op W') n' a
    (by rw [sectionsFunctor_map_rootPolyHom, hroot, hfun]; exact haF)
    (by rw [sectionsFunctor_map_rootPolyHom, hroot, hfun]; exact haE)
  exact ⟨r, hr⟩

/-- **Local roots give roots after a left-exact left adjoint.** Under the hypothesis of
`AlgebraicGeometry.RingedTopos.isLocallySurjective_rootLocusπ`, for every family `x` of
elements of the transported ring `q(O)` at which `p` is invertible, the polynomial `F` with
coefficients evaluated at `x` has a root at which `E` is invertible.

The family `x` is a point of `q(O^ι)` lying in `q(N)`; the projection from the root locus to
`N` is locally surjective, so `q` of it is surjective, and a point over `x` of `q` of the root
locus is a root. -/
theorem exists_root_map_of_local_roots
    (h : ∀ (W : X.C) (s : ι → X.O.obj.obj (op W)), IsUnit (evalULiftInt _ s p) →
      ∃ T : Sieve W, T ∈ X.J W ∧ ∀ ⦃W' : X.C⦄ (i : W' ⟶ W), T i →
        ∃ a : X.O.obj.obj (op W'),
          (F.map (evalULiftInt _ (fun k => X.O.obj.map i.op (s k)))).eval a = 0 ∧
          IsUnit ((E.map (evalULiftInt _ (fun k => X.O.obj.map i.op (s k)))).eval a))
    (x : ι → q.obj (ringSheaf (ringStructureSheaf X))) :
    letI := ringObjCommRing (sections_mul_comm X) q
    IsUnit (evalULiftInt _ x p) →
      ∃ a, (F.map (evalULiftInt _ x)).eval a = 0 ∧ IsUnit ((E.map (evalULiftInt _ x)).eval a) := by
  let := ringObjCommRing (sections_mul_comm X) q
  intro hx
  have := isLocallySurjective_rootLocusπ X F E p h
  set z : q.obj (coeffSheaf X ι) := Functor.piObjMk x
  have hz : (fun k => q.map (Pi.π (fun _ : ι => ringSheaf (ringStructureSheaf X)) k) z) = x :=
    funext fun k => Functor.map_piπ_piObjMk x k
  obtain ⟨u, hu⟩ := (isUnit_iff_exists_map_unitsIncl X q _).mp
    (by rwa [map_coeffPolyHom, hz] : IsUnit (q.map (coeffPolyHom X p) z))
  obtain ⟨n, hn, -⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback (coeffPolyHom X p) (unitsIncl X)).map q) z u hu.symm
  obtain ⟨r, hr⟩ := surjective_map_of_isLocallySurjective q (rootLocusπ X F E p) n
  obtain ⟨hF, hE⟩ := map_rootPolyHom_of_rootLocus X F E p q r
  set e := q.map (pullback.fst _ _ ≫ pullback.fst _ _) r
  have hcoeff : (fun k => q.map (rootCoeff X p k) e) = x := by
    refine Eq.trans (funext fun k => ?_) hz
    rw [rootCoeff, ← q.map_comp_apply, ← Category.assoc, ← Category.assoc,
      Category.assoc (pullback.fst _ _), ← rootLocusπ, q.map_comp_apply, q.map_comp_apply, hr,
      hn]
  rw [map_rootPolyHom, hcoeff] at hF hE
  exact ⟨_, hF, hE⟩

end Roots

/-! ### Strict henselianity -/

section StrictlyHenselian

open MvPolynomial

/-- **A left-exact left adjoint carries a locally strictly henselian sheaf of rings to a strictly
henselian ring.** Let `X` be a ringed topos and `q` a left-exact functor from sheaves of sets to
sets which is a left adjoint, with `q(O_X)` nonzero.  Suppose that

* locally, every section `a` of `O_X` or `1 - a` is invertible (`hloc`), and
* for every monic `f` and every `g` over `O_X(W)` and every unit `c` of `O_X(W)` such that the
  image of `g f'` in `K[X]/(f)` is not nilpotent for every point `ψ : O_X(W) → K` to a field at
  which `c` does not vanish, the polynomial `f` has, locally on `W`, a root at which `g f'` is
  invertible (`hroot`).

Then the ring `q(O_X)` is strictly henselian.

It is local by `AlgebraicGeometry.RingedTopos.isLocalRing_map_of_isUnit_or_isUnit_one_sub`.  For
the root criterion `strictlyHenselianLocalRing_of_exists_root`, write `f` and `g` as
specializations of the universal monic polynomial `F` of degree `d` and the universal polynomial
`G` of degree at most `m`; `AdjoinRoot.exists_coeffs_not_isNilpotent_iff` cuts out the
non-nilpotence of `G F'` by finitely many universal coefficients `cᵢ`, one of which specializes
to a unit of `q(O_X)` because the residue field of `q(O_X)` is such a point.  Then `hroot`, with
`c` the specialization of that `cᵢ`, is exactly the hypothesis of
`AlgebraicGeometry.RingedTopos.exists_root_map_of_local_roots`. -/
theorem strictlyHenselianLocalRing_map (q : Sheaf X.J (Type w) ⥤ Type w) [PreservesFiniteLimits q]
    [q.IsLeftAdjoint] [HasBinaryCoproduct (units X) (units X)]
    [Nontrivial (q.obj (ringSheaf (ringStructureSheaf X)))]
    (hloc : ∀ (W : X.C) (a : X.O.obj.obj (op W)), ∃ T : Sieve W, T ∈ X.J W ∧
      ∀ ⦃W' : X.C⦄ (i : W' ⟶ W), T i →
        IsUnit ((X.O.obj.map i.op) a) ∨ IsUnit ((X.O.obj.map i.op) (1 - a)))
    (hroot : ∀ (W : X.C) (f g : (X.O.obj.obj (op W))[X]), f.Monic → ∀ c : X.O.obj.obj (op W),
      IsUnit c → (∀ (K : Type w) [Field K] (ψ : X.O.obj.obj (op W) →+* K), ψ c ≠ 0 →
        ¬ IsNilpotent (AdjoinRoot.mk (f.map ψ) ((g * derivative f).map ψ))) →
      ∃ T : Sieve W, T ∈ X.J W ∧ ∀ ⦃W' : X.C⦄ (i : W' ⟶ W), T i →
        ∃ a, (f.map (X.O.obj.map i.op).hom).eval a = 0 ∧
          IsUnit (((g * derivative f).map (X.O.obj.map i.op).hom).eval a)) :
    letI := ringObjCommRing (sections_mul_comm X) q
    StrictlyHenselianLocalRing (q.obj (ringSheaf (ringStructureSheaf X))) := by
  let := ringObjCommRing (sections_mul_comm X) q
  have := isLocalRing_map_of_isUnit_or_isUnit_one_sub X q hloc
  refine strictlyHenselianLocalRing_of_exists_root fun f g hf hnil ↦ ?_
  set d := f.natDegree
  set m := g.natDegree
  set F := universalMonic.{w} d m
  set E := universalPoly.{w} d m * derivative F
  have hFm : F.Monic := universalMonic_monic d m
  obtain ⟨n, c, hc⟩ := AdjoinRoot.exists_coeffs_not_isNilpotent_iff F E hFm
  set x : Fin d ⊕ Fin (m + 1) → q.obj (ringSheaf (ringStructureSheaf X)) :=
    Sum.elim (fun j => f.coeff j) (fun k => g.coeff k)
  have hFx : F.map (evalULiftInt _ x) = f := map_universalMonic hf m _
  have hEx : E.map (evalULiftInt _ x) = g * derivative f := by
    rw [Polynomial.map_mul, ← Polynomial.derivative_map, hFx, map_universalPoly d _ g]
  obtain ⟨i, hi⟩ := (hc (IsLocalRing.ResidueField _)
    ((IsLocalRing.residue _).comp (evalULiftInt _ x))).mp (by
      rw [← Polynomial.map_map, ← Polynomial.map_map, hFx, hEx]
      exact hnil)
  have hunit : IsUnit (evalULiftInt _ x (c i)) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hi
  obtain ⟨a, ha₁, ha₂⟩ := exists_root_map_of_local_roots X q F E (c i) (fun W s hs ↦ by
    obtain ⟨T, hT, hTs⟩ := hroot W (F.map (evalULiftInt _ s))
      ((universalPoly.{w} d m).map (evalULiftInt _ s)) (hFm.map _) _ hs (fun K _ ψ hψ ↦ by
        have h := (hc K (ψ.comp (evalULiftInt _ s))).mpr ⟨i, hψ⟩
        rwa [Polynomial.derivative_map, ← Polynomial.map_mul, Polynomial.map_map,
          Polynomial.map_map])
    refine ⟨T, hT, fun W' j hj ↦ ?_⟩
    obtain ⟨a, ha₁, ha₂⟩ := hTs j hj
    refine ⟨a, ?_, ?_⟩
    · rwa [Polynomial.map_map, comp_evalULiftInt] at ha₁
    · rwa [Polynomial.derivative_map, ← Polynomial.map_mul, Polynomial.map_map,
        comp_evalULiftInt] at ha₂) x hunit
  exact ⟨a, by rwa [hFx] at ha₁, by rwa [hEx] at ha₂⟩

end StrictlyHenselian

end AlgebraicGeometry.RingedTopos

