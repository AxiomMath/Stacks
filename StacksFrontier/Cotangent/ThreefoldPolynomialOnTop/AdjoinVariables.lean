module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.InitialObjectDerivedColimit
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteShriek
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmall
public import StacksFrontier.Cotangent.ThreefoldPolynomialSiteSmall

/-!
# The tower site when the top ring is a polynomial algebra

Let `A → B → C` be ring maps with `C = B[E]` a polynomial algebra over `B`, and let `C_{C/B/A}`
be the threefold site of Tag 08QT. Choosing a resolution `ε : P_• → B` of `B` over `A`, the
towers `U_n = (P_n → B, P_n[E] → C)` form a cosimplicial object of `C_{C/B/A}` whose image under
`u₃` is the constant cosimplicial object with value the identity augmentation `C → C`. That
cosimplicial object satisfies the hypothesis of the criterion of Tag 08Q9, so `Lπ_!(g₃^{-1}ℱ)`
is computed by the constant simplicial abelian group `ℱ(C → C)`, which is `π_{3,!}ℱ`. The
resolution is a choice made inside the source's proof, and it is made here too: the final
statements take the standard resolution of Tag 08PM, whose augmentation is a trivial Kan
fibration by Tag 08QI, so nothing about a resolution is left as a hypothesis. The middle term
`Lπ_{3,!}ℱ` is `π_{3,!}ℱ` because `C → C` is an initial object of `C_{C/B}`, which makes
`π_{3,!}` an evaluation and hence exact.

## Main definitions

* `CommAlgCat.mvPolynomialFunctor`: adjoining a set of variables, as a functor on `A`-algebras.
* `CommAlgCat.mvPolynomialSupported` and `CommAlgCat.mvPolynomialSupportedDiagram`: the
  simplicial set of polynomials over a simplicial `A`-algebra whose monomials lie in a given
  finite set of exponents, and its dependence on that finite set.
* `CommAlgCat.towerVariablesAugmentation` and `CommAlgCat.towerCommaOfResolution`: the
  augmentation `P_n[E] → C` and the tower `(P_n → B, P_n[E] → C)` it belongs to.
* `CommAlgCat.towerCosimplicialObject`, `CommAlgCat.boundedTowerCosimplicialObject` and
  `CommAlgCat.smallTowerCosimplicialObject`: the cosimplicial object `U_•` of the site
  `C_{C/B/A}`, of its footnote-restricted version, and of the small model of the latter.
* `CommAlgCat.towerMor`: the simplicial set `Mor_{C_{C/B/A}}(U_•, W)`, written out, together
  with `CommAlgCat.towerMorIso` identifying it with the simplicial set of the criterion.
* `CommAlgCat.boundedTowerIdentityAugmentation` and `CommAlgCat.smallTowerIdentityObj`: the
  identity augmentation `C → C`, as an object of the restricted site `C_{C/B}` and of its
  small model.

## Main results

* `CommAlgCat.trivialKanFibrations_mvPolynomialWhiskerRight`: if `R_• → S_•` is a trivial Kan
  fibration of underlying simplicial sets, then so is `R_•[E] → S_•[E]`; this is the source's
  filtered colimit `R[E] = colim_Σ ∏_{I ∈ Σ} R` of products, through
  `CommAlgCat.isColimitMvPolynomialSupportedCocone` and
  `CommAlgCat.isLimitMvPolynomialSupportedFan`.
* `CommAlgCat.trivialKanFibrations_towerVariablesAugmentationNatTrans`: hence `P_•[E] → C` is a
  trivial Kan fibration, `C = B[E]` identifying it with the coefficientwise `ε`.
* `CommAlgCat.trivialKanFibrations_towerMor` and
  `CommAlgCat.exists_homotopyEquivalences_towerMor`: each `Mor_{C_{C/B/A}}(U_•, W)` is homotopy
  equivalent to a singleton, by filling the two layers of a lifting problem separately.
* `CommAlgCat.isPointResolution_smallTowerCosimplicialObject` and
  `CommAlgCat.smallTowerLeftDerivedColimitNatIso`: the criterion of Tag 08Q9 applies to `U_•`
  in the small model, so `L_nπ_!` is the homology of the Moore complex of `ℱ(U_•)`.
* `CommAlgCat.smallTowerThirdConstIso`: `u₃(U_•)` is the constant cosimplicial object with
  value the identity augmentation `C → C`, which is initial in the small model of `C_{C/B}`.
* `CommAlgCat.colimitSmallTowerIdentityIso`: `π_{3,!}ℱ = ℱ(C → C)`, Tag 08QG at that model.
* `CommAlgCat.leftDerivedColimitThirdInverseImageZeroIso` and
  `CommAlgCat.isZero_leftDerivedColimitThirdInverseImage_succ`: for an arbitrary resolution `ε`
  of `B` over `A`, the degree-zero identification `π_!(g₃^{-1}ℱ) = π_{3,!}ℱ` together with the
  vanishing of `L_nπ_!(g₃^{-1}ℱ)` in positive degrees.
* `CommAlgCat.leftDerivedColimitThirdZeroIso` and
  `CommAlgCat.isZero_leftDerivedColimitThird_succ`: the middle term of the chain,
  `Lπ_{3,!}ℱ = π_{3,!}ℱ`, read as right exactness of `π_{3,!}` together with the vanishing of
  `L_nπ_{3,!}ℱ` for `n > 0`, the latter because the identity augmentation `C → C` is an initial
  object of the model.
* `CommAlgCat.standardLeftDerivedColimitThirdInverseImageZeroIso`,
  `CommAlgCat.isZero_standardLeftDerivedColimitThirdInverseImage_succ` and
  `CommAlgCat.standardLeftDerivedColimitThirdChainIso`:
  `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ` with no hypothesis beyond `C` being a polynomial
  algebra over `B` -- the resolution the source picks inside its proof is the standard one of
  Tag 08PM, and the trivial Kan fibration hypothesis the statements above carry is then Tag 08QI
  -- but still at the small models of the footnote-restricted sites, and so **not** Tag 08QV.

**Tag 08QV itself** is `CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso` together
with `CommAlgCat.polynomialSiteDerivedColimitThirdIso`, in
`StacksFrontier.Cotangent.ThreefoldPolynomialOnTopLargeSite`: the two equalities of the chain read
at `C_{C/B/A}` and `C_{C/B}` themselves. Everything in this file that the criterion of Tag 08Q9
needs is proved at those sites and nowhere else -- the point-resolution hypothesis by
`CommAlgCat.exists_homotopyEquivalences_towerMor` and the identification of `u₃(U_•)` by
`CommAlgCat.towerThirdSimplicialConstIso` -- and the restricted statements below descend from
them. What forced the restriction was the degreewise form of the criterion of Tag 08Q9, which
asks for a small site; the derived-category form carries no smallness hypothesis.

## Implementation notes

**The cardinal bounds.** The site of Tag 08QT carries the section's footnote restricting the
two layers of variables, and only the restricted site has a small model, which is what the
criterion of Tag 08Q9 needs. The bounds are parameters: `κ` bounds the variables of the terms
of the resolution over `A` and is a hypothesis on the resolution, exactly as for the twofold
site; `μ` bounds the second layer and only has to satisfy `#E ≤ μ`, because the second layer of
`U_n` is `E` itself. For the standard resolution a correct `κ` is
`CommAlgCat.standardResolutionVarCardinal`, and that is the only constraint the unconditional
statements place on `κ`: they ask `standardResolutionVarCardinal A B ≤ κ`, which is the
footnote's "sufficiently large cardinal" and not a hypothesis of the source's lemma.

**Why the product decomposition is carried out on a lifting problem.** The source writes
`Mor_{C_{C/B/A}}(U_•, W)` as `∏_{s ∈ S} F_s × ∏_{t ∈ T} F'_t` for presentations `P = A[S]`,
`Q = A[S ⨿ T]` and concludes by Tag 08Q4. Here the decomposition is applied directly to a
lifting problem for `Mor(U_•, W) → ∗`: a boundary `∂Δ[n] ⟶ Mor(U_•, W)` is the same thing as a
family of maps `∂Δ[n] ⟶ P_•` indexed by `S` and a family `∂Δ[n] ⟶ P_•[E]` indexed by `T`, each
with constant augmentation, which `P_• → B` resp. `P_•[E] → C` fill, and the fillers assemble
because a morphism of towers out of `(A[S] → B, A[S][T] → C)` is a function on `S` together with
a function on `T`. The normal form used is `Q = P[T]` rather than `Q = A[S ⨿ T]`: it is what the
definition of the site provides, and the two layers of generators are exactly what a morphism of
towers out of `W` is determined by.

**`u₃(U_•)` is constant by terminality.** The source says `u₃(U_•)` is the constant cosimplicial
object with value `(C → C)`. Here that is proved by showing each `u₃(U_n)` initial in the small
model of `C_{C/B}` — the augmentation `B ⊗_{P_n} P_n[E] → C` is bijective, being
`B ⊗_{P_n} P_n[E] = B[E] = C` — so the comparison with the constant object is the unique
morphism out of an initial object and its naturality is automatic.

## References

* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QG](https://stacks.math.columbia.edu/tag/08QG)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CommAlgCat

/-! ### Adjoining variables to a simplicial algebra -/

section MvPolynomialFunctor

variable (A : Type u) [CommRing A] (E : Type u)

/-- Adjoining the set `E` of variables, as a functor on `A`-algebras: `R ↦ R[E]`, a map of
`A`-algebras acting on the coefficients. -/
def mvPolynomialFunctor : CommAlgCat.{u} A ⥤ CommAlgCat.{u} A where
  obj R := CommAlgCat.of A (MvPolynomial E R)
  map f := CommAlgCat.ofHom (MvPolynomial.mapAlgHom (CommAlgCat.Hom.hom f))
  map_id R := by
    apply CommAlgCat.hom_ext
    refine AlgHom.ext fun p => ?_
    change MvPolynomial.map (RingHom.id _) p = p
    rw [MvPolynomial.map_id]
  map_comp f g := by
    apply CommAlgCat.hom_ext
    refine AlgHom.ext fun p => ?_
    change MvPolynomial.map _ p = MvPolynomial.map _ (MvPolynomial.map _ p)
    rw [MvPolynomial.map_map]
    rfl

/-- `R_•[E]` on underlying simplicial sets: adjoining variables degreewise to a simplicial
`A`-algebra. -/
abbrev mvPolynomialSSet (R : SimplicialObject (CommAlgCat.{u} A)) : SSet.{u} :=
  (R ⋙ mvPolynomialFunctor A E) ⋙ forget (CommAlgCat.{u} A)

end MvPolynomialFunctor

/-! ### Polynomials with prescribed monomials -/

section Supported

variable {A : Type u} [CommRing A] {E : Type u}

/-- A sum of monomials indexed by a finite set `s` of exponents is supported in `s`. -/
lemma support_sum_monomial_subset {R : Type u} [CommRing R] (s : Finset (E →₀ ℕ))
    (a : {x // x ∈ s} → R) :
    (∑ i ∈ s.attach, MvPolynomial.monomial (i : E →₀ ℕ) (a i)).support ⊆ s := by
  classical
  intro j hj
  by_contra hjs
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum] at hj
  refine hj (Finset.sum_eq_zero fun i _ => ?_)
  rw [MvPolynomial.coeff_monomial, ite_eq_right]
  exact fun h => hjs (h ▸ i.2)

/-- The coefficient of a sum of monomials indexed by a finite set of exponents, at one of those
exponents. -/
lemma coeff_sum_monomial {R : Type u} [CommRing R] (s : Finset (E →₀ ℕ))
    (a : {x // x ∈ s} → R) (i : {x // x ∈ s}) :
    MvPolynomial.coeff (i : E →₀ ℕ)
        (∑ j ∈ s.attach, MvPolynomial.monomial (j : E →₀ ℕ) (a j)) = a i := by
  classical
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · simp [MvPolynomial.coeff_monomial]
  · intro j _ hji
    rw [MvPolynomial.coeff_monomial, ite_eq_right]
    exact fun h => hji (Subtype.ext h)
  · exact fun h => absurd (Finset.mem_attach s i) h

/-- Two polynomials supported in a finite set of exponents and with the same coefficients
there are equal. -/
lemma mvPolynomial_ext_of_support_subset {R : Type u} [CommRing R] (s : Finset (E →₀ ℕ))
    {p q : MvPolynomial E R} (hp : p.support ⊆ s) (hq : q.support ⊆ s)
    (h : ∀ i ∈ s, MvPolynomial.coeff i p = MvPolynomial.coeff i q) : p = q := by
  refine MvPolynomial.ext _ _ fun i => ?_
  by_cases hi : i ∈ s
  · exact h i hi
  · rw [MvPolynomial.notMem_support_iff.mp (mt (@hp i) hi),
      MvPolynomial.notMem_support_iff.mp (mt (@hq i) hi)]

end Supported

/-! ### The diagram of polynomials with prescribed monomials -/

section SupportedDiagram

variable {A : Type u} [CommRing A] (E : Type u) (R : SimplicialObject (CommAlgCat.{u} A))

/-- The polynomials in the variables `E` over the degree-`m` term of a simplicial `A`-algebra
whose monomials all lie in a given finite set of exponents. -/
abbrev mvPolynomialSupportedType (s : Finset (E →₀ ℕ)) (m : SimplexCategoryᵒᵖ) : Type u :=
  { p : MvPolynomial E (R.obj m) // p.support ⊆ s }

/-- The simplicial set of polynomials in the variables `E` over a simplicial `A`-algebra whose
monomials all lie in a given finite set of exponents: a simplicial subset of `R_•[E]`, the
structure maps acting on the coefficients and so not enlarging the support. -/
def mvPolynomialSupported (s : Finset (E →₀ ℕ)) : SSet.{u} where
  obj m := mvPolynomialSupportedType E R s m
  map {m m'} f := ↾fun p =>
    (⟨MvPolynomial.map (CommAlgCat.Hom.hom (R.map f)).toRingHom p.1,
      (MvPolynomial.support_map_subset _ _).trans p.2⟩ : mvPolynomialSupportedType E R s m')
  map_id m := ConcreteCategory.ext_apply fun p => Subtype.ext (by
    change MvPolynomial.map (CommAlgCat.Hom.hom (R.map (𝟙 m))).toRingHom p.1 = p.1
    rw [R.map_id]
    change MvPolynomial.map (RingHom.id _) p.1 = p.1
    rw [MvPolynomial.map_id])
  map_comp f g := ConcreteCategory.ext_apply fun p => Subtype.ext (by
    change MvPolynomial.map (CommAlgCat.Hom.hom (R.map (f ≫ g))).toRingHom p.1 =
      MvPolynomial.map (CommAlgCat.Hom.hom (R.map g)).toRingHom
        (MvPolynomial.map (CommAlgCat.Hom.hom (R.map f)).toRingHom p.1)
    rw [MvPolynomial.map_map, R.map_comp]
    rfl)

/-- Enlarging the finite set of exponents, as a diagram indexed by the finite sets of
exponents: the inclusion of one simplicial subset of `R_•[E]` into another. -/
def mvPolynomialSupportedDiagram : Finset (E →₀ ℕ) ⥤ SSet.{u} where
  obj s := mvPolynomialSupported E R s
  map {_ t} h :=
    { app := fun m => ↾fun p => (⟨p.1, p.2.trans (leOfHom h)⟩ :
        mvPolynomialSupportedType E R t m)
      naturality := fun _ _ _ => ConcreteCategory.ext_apply fun _ => Subtype.ext rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone on `CommAlgCat.mvPolynomialSupportedDiagram` with vertex `R_•[E]`, given by the
inclusions. -/
def mvPolynomialSupportedCocone : Cocone (mvPolynomialSupportedDiagram E R) where
  pt := mvPolynomialSSet A E R
  ι :=
    { app := fun _ => { app := fun m => ↾fun p => (p.1 : MvPolynomial E (R.obj m))
                        naturality := fun _ _ _ => ConcreteCategory.ext_apply fun _ => rfl }
      naturality := fun _ _ _ => NatTrans.ext (funext fun _ =>
        ConcreteCategory.ext_apply fun _ => rfl) }

/-- **`R_•[E]` is the filtered colimit of its subsets of polynomials with prescribed
monomials**, the source's presentation
`R[E] = colim_{Σ ⊆ Map(E, ℤ_{≥ 0}) finite} ∏_{I ∈ Σ} R`: every polynomial has finite support. -/
def isColimitMvPolynomialSupportedCocone : IsColimit (mvPolynomialSupportedCocone E R) := by
  refine evaluationJointlyReflectsColimits _ fun m => ?_
  refine ⟨fun c => ↾fun (p : MvPolynomial E (R.obj m)) =>
    c.ι.app p.support ⟨p, subset_rfl⟩, ?_, ?_⟩
  · intro c s
    refine ConcreteCategory.ext_apply fun p => ?_
    have hw := ConcreteCategory.congr_hom (c.w (homOfLE p.2))
      (⟨p.1, subset_rfl⟩ : mvPolynomialSupportedType E R p.1.support m)
    change c.ι.app p.1.support ⟨p.1, subset_rfl⟩ = c.ι.app s p
    refine hw.symm.trans ?_
    change c.ι.app s _ = _
    exact congrArg (c.ι.app s) (Subtype.ext rfl)
  · intro c f hf
    refine ConcreteCategory.ext_apply fun p => ?_
    exact ConcreteCategory.congr_hom (hf (MvPolynomial.support p))
      (⟨p, subset_rfl⟩ : mvPolynomialSupportedType E R (MvPolynomial.support p) m)

/-- The polynomial with monomials in a finite set `s` of exponents assembled from a family of
coefficients indexed by `s`. -/
def mvPolynomialOfCoeffs (s : Finset (E →₀ ℕ)) (m : SimplexCategoryᵒᵖ)
    (a : {x // x ∈ s} → (R.obj m : Type u)) : mvPolynomialSupportedType E R s m :=
  ⟨∑ i ∈ s.attach, MvPolynomial.monomial (i : E →₀ ℕ) (a i), support_sum_monomial_subset s _⟩

/-- The coefficients of `CommAlgCat.mvPolynomialOfCoeffs` are the given family. -/
lemma coeff_mvPolynomialOfCoeffs (s : Finset (E →₀ ℕ)) (m : SimplexCategoryᵒᵖ)
    (a : {x // x ∈ s} → (R.obj m : Type u)) (i : {x // x ∈ s}) :
    MvPolynomial.coeff (i : E →₀ ℕ) (mvPolynomialOfCoeffs E R s m a).1 = a i :=
  coeff_sum_monomial s a i

/-- A polynomial with monomials in a finite set of exponents is determined by its coefficients
there. -/
lemma mvPolynomialSupported_ext {s : Finset (E →₀ ℕ)} {m : SimplexCategoryᵒᵖ}
    {p q : mvPolynomialSupportedType E R s m}
    (h : ∀ i : {x // x ∈ s}, MvPolynomial.coeff (i : E →₀ ℕ) p.1 =
      MvPolynomial.coeff (i : E →₀ ℕ) q.1) : p = q :=
  Subtype.ext (mvPolynomial_ext_of_support_subset s p.2 q.2 fun i hi => h ⟨i, hi⟩)

/-- The cone exhibiting the polynomials with monomials in a finite set `s` of exponents as the
product of copies of `R_•` indexed by `s`: the coefficients at the exponents of `s`. -/
def mvPolynomialSupportedFan (s : Finset (E →₀ ℕ)) :
    Fan fun _ : {x // x ∈ s} => R ⋙ forget (CommAlgCat.{u} A) :=
  Fan.mk (mvPolynomialSupported E R s)
    fun i =>
      { app := fun m => ↾fun p =>
          (MvPolynomial.coeff (i : E →₀ ℕ) p.1 : (R.obj m : Type u))
        naturality := fun m m' f => ConcreteCategory.ext_apply fun p => by
          rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
          change MvPolynomial.coeff (i : E →₀ ℕ)
              (MvPolynomial.map (CommAlgCat.Hom.hom (R.map f)).toRingHom p.1) =
            (CommAlgCat.Hom.hom (R.map f)) (MvPolynomial.coeff (i : E →₀ ℕ) p.1)
          exact MvPolynomial.coeff_map _ _ _ }

/-- **A polynomial with monomials in a finite set of exponents is its family of coefficients
there.** -/
def isLimitMvPolynomialSupportedFan (s : Finset (E →₀ ℕ)) :
    IsLimit (mvPolynomialSupportedFan E R s) := by
  refine evaluationJointlyReflectsLimits _ fun m => ?_
  refine ⟨fun c => ↾fun z => mvPolynomialOfCoeffs E R s m fun i => c.π.app ⟨i⟩ z, ?_, ?_⟩
  · intro c i
    refine ConcreteCategory.ext_apply fun z => ?_
    exact coeff_mvPolynomialOfCoeffs E R s m _ i.as
  · intro c f hf
    refine ConcreteCategory.ext_apply fun z => mvPolynomialSupported_ext E R fun i => ?_
    refine Eq.trans ?_ (coeff_mvPolynomialOfCoeffs E R s m (fun j => c.π.app ⟨j⟩ z) i).symm
    exact ConcreteCategory.congr_hom (hf ⟨i⟩) z

end SupportedDiagram

/-! ### Adjoining variables preserves trivial Kan fibrations -/

section TrivialKanFibration

variable {A : Type u} [CommRing A] (E : Type u)
  {R S : SimplicialObject (CommAlgCat.{u} A)} (φ : R ⟶ S)

/-- The morphism of diagrams of polynomials with prescribed monomials induced by a morphism of
simplicial `A`-algebras. -/
def mvPolynomialSupportedDiagramMap :
    mvPolynomialSupportedDiagram E R ⟶ mvPolynomialSupportedDiagram E S where
  app s :=
    { app := fun m => ↾fun p =>
        (⟨MvPolynomial.map (CommAlgCat.Hom.hom (φ.app m)).toRingHom p.1,
          (MvPolynomial.support_map_subset _ _).trans p.2⟩ :
          mvPolynomialSupportedType E S s m)
      naturality := fun m m' f => ConcreteCategory.ext_apply fun p => by
        rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
        refine Subtype.ext ?_
        change MvPolynomial.map (CommAlgCat.Hom.hom (φ.app m')).toRingHom
            (MvPolynomial.map (CommAlgCat.Hom.hom (R.map f)).toRingHom p.1) =
          MvPolynomial.map (CommAlgCat.Hom.hom (S.map f)).toRingHom
            (MvPolynomial.map (CommAlgCat.Hom.hom (φ.app m)).toRingHom p.1)
        refine MvPolynomial.ext _ _ fun j => ?_
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, MvPolynomial.coeff_map,
          MvPolynomial.coeff_map]
        have h := ConcreteCategory.congr_hom (φ.naturality f)
          (MvPolynomial.coeff j p.1)
        rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h
        exact h }
  naturality _ _ _ := NatTrans.ext (funext fun _ =>
    ConcreteCategory.ext_apply fun _ => Subtype.ext rfl)

/-- **Adjoining a set of variables preserves trivial Kan fibrations.** If `R_• → S_•` is a
morphism of simplicial `A`-algebras whose underlying morphism of simplicial sets is a trivial
Kan fibration, then so is the one underlying `R_•[E] → S_•[E]`.

This is the source's argument: for any ring `R` one has
`R[E] = colim_{Σ finite} ∏_{I ∈ Σ} R`, a filtered colimit, so the map in question is a filtered
colimit of products of copies of `R_• → S_•`; trivial Kan fibrations are stable under products
(Tag 08NR) and under filtered colimits (Tag 08Q5). -/
theorem trivialKanFibrations_mvPolynomialWhiskerRight
    (hφ : SSet.trivialKanFibrations (Functor.whiskerRight φ (forget (CommAlgCat.{u} A)))) :
    SSet.trivialKanFibrations
      (Functor.whiskerRight (Functor.whiskerRight φ (mvPolynomialFunctor A E))
        (forget (CommAlgCat.{u} A))) := by
  refine MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := SSet.trivialKanFibrations.{u}) (J := Finset (E →₀ ℕ)) _ _
    (mvPolynomialSupportedCocone E R) (mvPolynomialSupportedCocone E S)
    (isColimitMvPolynomialSupportedCocone E R) (isColimitMvPolynomialSupportedCocone E S)
    (mvPolynomialSupportedDiagramMap E φ) (fun s => ?_) _
    (fun _ => rfl)
  refine MorphismProperty.IsStableUnderLimitsOfShape.condition
    (W := SSet.trivialKanFibrations.{u}) (J := Discrete {x // x ∈ s}) _ _
    (mvPolynomialSupportedFan E R s) (mvPolynomialSupportedFan E S s)
    (isLimitMvPolynomialSupportedFan E R s) (isLimitMvPolynomialSupportedFan E S s)
    (Discrete.natTrans fun _ => Functor.whiskerRight φ (forget (CommAlgCat.{u} A)))
    (fun _ => hφ) _ (fun i => ?_)
  refine NatTrans.ext (funext fun m => ConcreteCategory.ext_apply fun p => ?_)
  show MvPolynomial.coeff (i.as : E →₀ ℕ)
      (MvPolynomial.map (CommAlgCat.Hom.hom (φ.app m)).toRingHom p.1) =
    (CommAlgCat.Hom.hom (φ.app m)) (MvPolynomial.coeff (i.as : E →₀ ℕ) p.1)
  exact MvPolynomial.coeff_map _ _ _

end TrivialKanFibration

end CommAlgCat

end
