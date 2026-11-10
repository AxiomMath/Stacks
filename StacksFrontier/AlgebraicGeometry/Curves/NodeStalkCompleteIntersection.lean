module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.CompleteIntersection
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria

/-!
# The local ring at a node is a complete intersection

Let `k` be a field. For a scheme `X` locally of finite type over `k` the two renderings of
"the local ring at a point is a complete intersection" agree: the base-dependent one of
Definition 00SD and the completion-based one of Definition 09Q3. At a node of a one-dimensional
such scheme the second holds, because the completed local ring is a two-variable power-series
ring modulo a nondegenerate binary quadratic form.

## Main results

* `AlgebraicGeometry.isCompleteIntersection_stalk_iff_isCompleteIntersectionRing` — at a point
  of a scheme locally of finite type over a field, `IsCompleteIntersection` over the field and
  `LocalCompleteIntersection.IsCompleteIntersectionRing` agree.
* `Stacks.Curves.isCompleteIntersectionRing_stalk_of_isNode` — the local ring at a node is a
  complete intersection ring.

## Implementation notes

The first result is Stacks 09Q6 (1) read at a stalk: an affine open neighbourhood presents the
stalk as a localization at a prime of a finite type `k`-algebra, and both predicates transport
along the comparison isomorphism with `Localization.AtPrime`.

The second goes through condition (3) of Stacks 0C49, which supplies the presentation
`𝒪_{X,x}^∧ ≅ κ(x)[[s, t]]/(a s² + b s t + c t²)` with `4ac - b² ≠ 0`. The quadratic form is a
nonzero element of the maximal ideal of the regular local ring `κ(x)[[s, t]]`, hence a regular
sequence of length one, which is exactly the data Definition 09Q3 asks for.

## References

* [Stacks Project, Tag 09Q6](https://stacks.math.columbia.edu/tag/09Q6)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing MvPowerSeries

universe u

namespace Stacks.Curves

/-! ### The nodal quadratic form as a regular sequence -/

/-- The nodal binary quadratic form is the sum of the three monomials `a s²`, `b s t`, `c t²`. -/
private theorem nodalBinaryQuadratic_eq_monomial_add {K : Type u} [Field K] (a b c : K) :
    nodalBinaryQuadratic a b c =
      monomial (Finsupp.single (0 : Fin 2) 2) a +
        monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) b +
        monomial (Finsupp.single (1 : Fin 2) 2) c := by
  rw [nodalBinaryQuadratic, X_pow_eq, X_pow_eq, X_def, X_def,
    ← monomial_zero_eq_C_apply a, ← monomial_zero_eq_C_apply b, ← monomial_zero_eq_C_apply c,
    monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial]
  simp

/-- A nondegenerate binary quadratic form is a nonzero power series: were it zero, each of its
three coefficients would vanish and the discriminant `4ac - b²` would be zero. -/
private theorem nodalBinaryQuadratic_ne_zero {K : Type u} [Field K] (a b c : K)
    (hdet : 4 * a * c - b ^ 2 ≠ 0) : nodalBinaryQuadratic a b c ≠ 0 := by
  intro h
  rw [nodalBinaryQuadratic_eq_monomial_add] at h
  have : Finsupp.single (0 : Fin 2) 2 ≠
        Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 ∧
      Finsupp.single (0 : Fin 2) 2 ≠ Finsupp.single (1 : Fin 2) 2 ∧
      Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 ≠
        Finsupp.single (1 : Fin 2) 2 := by
    simp [Finsupp.ext_iff, Fin.forall_fin_two]
  obtain ⟨h12, h13, h23⟩ := this
  have ha : a = 0 := by
    simpa [coeff_monomial, h12, h13] using congrArg (coeff (Finsupp.single (0 : Fin 2) 2)) h
  have hb : b = 0 := by
    have h' := congrArg
      (coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1)) h
    simpa [coeff_monomial, h12.symm, h23] using h'
  have hc : c = 0 := by
    simpa [coeff_monomial, h13.symm, h23.symm] using
      congrArg (coeff (Finsupp.single (1 : Fin 2) 2)) h
  exact hdet (by simp [ha, hb, hc])

/-- A Noetherian local `k`-algebra whose completion at the maximal ideal is a two-variable
power-series hypersurface cut out by a nondegenerate binary quadratic form is a complete
intersection ring: the power-series ring over the residue field is regular local, and the
quadratic form, being a nonzero element of its maximal ideal, is a regular sequence of
length one whose span is the kernel of the presentation. -/
private theorem isCompleteIntersectionRing_of_hasNodalCompletion (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra k A]
    (h : HasNodalCompletion k A) :
    LocalCompleteIntersection.IsCompleteIntersectionRing A := by
  obtain ⟨a, b, c, hdet, ⟨e⟩⟩ := h
  let R := MvPowerSeries (Fin 2) (ResidueField A)
  let q : R := nodalBinaryQuadratic a b c
  have _ : IsRegularLocalRing R := MvPowerSeries.isRegularLocalRing (ResidueField A) 2
  have _ : IsDomain R := IsRegularLocalRing.isDomain _
  have hq0 : q ≠ 0 := nodalBinaryQuadratic_ne_zero a b c hdet
  have hmem : q ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp [q, nodalBinaryQuadratic]
  have _ : Nontrivial (R ⧸ Ideal.span {q}) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
        ((Ideal.span_singleton_le_iff_mem _).mpr hmem))
  have _ : Nontrivial (AdicCompletion (maximalIdeal A) A) := e.toEquiv.nontrivial
  let π : R →+* R ⧸ Ideal.span {q} := Ideal.Quotient.mk (Ideal.span {q})
  let f : R →+* AdicCompletion (maximalIdeal A) A := e.symm.toRingHom.comp π
  have hf : Function.Surjective f := e.symm.surjective.comp Ideal.Quotient.mk_surjective
  have hreg : RingTheory.Sequence.IsRegular R [q] :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hmem)).mpr
      ((RingTheory.Sequence.isWeaklyRegular_singleton_iff R q).mpr
        fun _ _ h => mul_left_cancel₀ hq0 h)
  have hker : Ideal.ofList [q] = RingHom.ker f := by
    rw [Ideal.ofList_singleton, RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]
  exact ⟨R, inferInstance, inferInstance, f, hf, IsLocalHom.of_surjective f hf, [q], hreg, hker⟩

end Stacks.Curves

namespace AlgebraicGeometry

/-! ### The two renderings of a complete-intersection local ring agree at a stalk -/

/-- **Stacks Project, Tag 09Q6, part (1), at a stalk.** For a scheme locally of finite type over
a field `k`, the local ring at a point is a complete intersection over `k` in the sense of
Definition 00SD if and only if it is a complete intersection ring in the completion-based sense
of Definition 09Q3.

An affine open neighbourhood presents the stalk as the localization of a finite type
`k`-algebra at a prime, where Stacks 09Q6 (1) applies; both predicates transport along the
comparison isomorphism with `Localization.AtPrime`. -/
theorem isCompleteIntersection_stalk_iff_isCompleteIntersectionRing
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x : X) :
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (IsCompleteIntersection k (X.presheaf.stalk x) ↔
      LocalCompleteIntersection.IsCompleteIntersectionRing (X.presheaf.stalk x)) := by
  let _ : Algebra k (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨-, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  let _ : Algebra Γ(Spec (.of k), ⊤) Γ(X, U.1) := (f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  let _ : Algebra k Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  let _ : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU).hom.toAlgebra
  have _ : IsScalarTower k Γ(X, U.1) (X.presheaf.stalk x) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    simp only [RingHom.algebraMap_toAlgebra]
    change (X.presheaf.germ ⊤ x (by simp))
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom z) =
      (X.presheaf.germ U.1 x hxU)
        ((f.appTop ≫ X.presheaf.map (homOfLE le_top).op)
          (((Scheme.ΓSpecIso (.of k)).inv).hom z))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← X.presheaf.germ_res_apply (homOfLE le_top) x hxU]
  -- `Γ(X, U)` is of finite type over `k`, through `Γ(Spec k, ⊤)`.
  have _ : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, U.1) :=
    f.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)
  let _ : Algebra k Γ(Spec (.of k), ⊤) :=
    (CommRingCat.ofHom (RingHom.id k) ≫ (Scheme.ΓSpecIso (.of k)).inv).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap k Γ(Spec (.of k), ⊤)) := by
    change Function.Bijective
      (((Scheme.ΓSpecIso (.of k)).inv).hom.comp (RingHom.id k))
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).comp
      Function.bijective_id
  have _ : IsScalarTower k Γ(Spec (.of k), ⊤) Γ(X, U.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    simp only [RingHom.algebraMap_toAlgebra]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom z =
      (f.appLE ⊤ U.1 (by simp)).hom
        ((CommRingCat.ofHom (RingHom.id k) ≫ (Scheme.ΓSpecIso (.of k)).inv).hom z)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rfl
  have _ : Algebra.FiniteType k Γ(Spec (.of k), ⊤) :=
    RingHom.finiteType_algebraMap.mp
      (RingHom.FiniteType.of_surjective (algebraMap k Γ(Spec (.of k), ⊤)) hbij.2)
  have _ : Algebra.FiniteType k Γ(X, U.1) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k Γ(Spec (.of k), ⊤))
      (inferInstance : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, U.1))
  let q : Ideal Γ(X, U.1) := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  have _ : q.IsPrime := (U.2.primeIdealOf ⟨x, hxU⟩).isPrime
  have _ : IsLocalization.AtPrime (X.presheaf.stalk x) q := U.2.isLocalization_stalk ⟨x, hxU⟩
  have _ : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have _ : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  -- Both predicates transport along the comparison with `Localization.AtPrime q`.
  let eStalk : X.presheaf.stalk x ≃ₐ[Γ(X, U.1)] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x) (Localization.AtPrime q)
  have hCI : IsCompleteIntersection k (X.presheaf.stalk x) ↔
      IsCompleteIntersection k (Localization.AtPrime q) :=
    ((IsCompleteIntersection.localization_atPrime_tfae.{u, u, u, u} k Γ(X, U.1) q
        (X.presheaf.stalk x)).out 1 2).trans
      ((IsCompleteIntersection.localization_atPrime_tfae.{u, u, u, u} k Γ(X, U.1) q
        (Localization.AtPrime q)).out 1 2).symm
  have hCIR : LocalCompleteIntersection.IsCompleteIntersectionRing (X.presheaf.stalk x) ↔
      LocalCompleteIntersection.IsCompleteIntersectionRing (Localization.AtPrime q) :=
    ⟨LocalCompleteIntersection.isCompleteIntersectionRing_of_ringEquiv eStalk.toRingEquiv,
      LocalCompleteIntersection.isCompleteIntersectionRing_of_ringEquiv eStalk.toRingEquiv.symm⟩
  rw [hCI, hCIR]
  exact LocalCompleteIntersection.isCompleteIntersection_atPrime_iff_isCompleteIntersectionRing
    k Γ(X, U.1) q

end AlgebraicGeometry

namespace Stacks.Curves

/-! ### The local ring at a node -/

/-- **Stacks Project, Tag 0C49 at a node.** The local ring at a node of a one-dimensional
scheme locally of finite type over a field is a complete intersection ring.

Condition (3) of Tag 0C49 presents the completion of the local ring as
`κ(x)[[s, t]]/(a s² + b s t + c t²)` with `4ac - b² ≠ 0`, and the quadratic form is a regular
sequence of length one in the regular local ring `κ(x)[[s, t]]`. -/
theorem isCompleteIntersectionRing_stalk_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsNode k X x) :
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    LocalCompleteIntersection.IsCompleteIntersectionRing (X.presheaf.stalk x) := by
  have _ : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let kToStalk : k →+* X.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom
  let _ : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let _ : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  obtain ⟨-, hcomp⟩ := ((isNodalAlgebra_tfae k (X.presheaf.stalk x)).out 1 3).mp
    ((isNode_iff_isNodalAlgebra_stalk k X hX x).mp hx)
  exact isCompleteIntersectionRing_of_hasNodalCompletion k (X.presheaf.stalk x) hcomp

end Stacks.Curves

end
