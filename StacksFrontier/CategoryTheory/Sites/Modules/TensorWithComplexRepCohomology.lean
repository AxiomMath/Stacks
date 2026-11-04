module

public import StacksFrontier.Algebra.DifferentialGraded.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRegularExt

/-!
# The cohomology of the endomorphism algebra of a K-injective complex

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The
degree-`n` cohomology of `E` is the degree-`n` cohomology of the complex of morphisms `K → K`,
that is the group of homotopy classes of maps `K → K[n]`. When `K` is K-injective these are the
morphisms `K → K[n]` of `D(O)`:

`H^n(E) = Ext^n_{D(O)}(K, K)`,

which is equation (36.18.0.1) (Tag 09M6) in the proof of Tag 09M5. In particular `E` has only
finitely many nonzero cohomology groups as soon as only finitely many of the `Ext^n(K, K)` are
nonzero.

## Main results

* `AlgebraicGeometry.RingedSite.repCohomologyEquivCohomologyClass`: `H^n(E)` is the group of
  cohomology classes of degree `n` of the complex of morphisms `K → K`.
* `AlgebraicGeometry.RingedSite.repCohomologyEquivDerivedHom`: **Tag 09M6**, for K-injective `K`,
  `H^n(E) ≃ Hom_{D(O)}(K, K[n])`.
* `AlgebraicGeometry.RingedSite.finite_setOf_nontrivial_cohomology_rep`: for K-injective `K`, if
  only finitely many `Hom_{D(O)}(K, K[n])` are nonzero, then only finitely many `H^n(E)` are
  nonzero.

## References

* [Stacks Project, Tag 09M6](https://stacks.math.columbia.edu/tag/09M6)
* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u v w t s

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- The differential of the endomorphism algebra is the differential of the complex of
morphisms, in any pair of consecutive degrees. -/
theorem rep_algebraHom_d (m n : ℤ) (h : m + 1 = n)
    (c : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading m)
    (hc : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d c ∈
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading n) :
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom n
        ⟨(Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d c, hc⟩ =
      δ m n ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom m c) := by
  subst h
  exact (Rep.{u, v, w, t, s, 0} X ℤ K).algebra_d m c

/-- A homogeneous element of degree `n` of the endomorphism algebra is a cocycle exactly when the
corresponding cochain is. -/
theorem rep_d_eq_zero_iff (n : ℤ) (a : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading n) :
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d a = 0 ↔
      δ n (n + 1) ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom n a) = 0 := by
  rw [← rep_algebraHom_d.{u, v, w, t, s} X K n (n + 1) rfl a
      ((Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d_mem n a a.2), LinearEquiv.map_eq_zero_iff]
  exact ⟨fun h => Subtype.ext h, congrArg Subtype.val⟩

/-- A degree-`n` element `x` of the endomorphism algebra is the differential of `c` exactly when
the corresponding cochains satisfy the same relation. -/
private theorem rep_algebraHom_eq_δ_iff (n : ℤ)
    (x : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading n)
    (c : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading (n - 1)) :
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom n x =
        δ (n - 1) n ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom (n - 1) c) ↔
      x.1 = (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d c := by
  have hmem : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d c ∈
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading n := by
    simpa only [sub_add_cancel] using (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d_mem (n - 1) c c.2
  rw [← rep_algebraHom_d.{u, v, w, t, s} X K (n - 1) n (by omega) c hmem,
    EmbeddingLike.apply_eq_iff_eq]
  exact ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩

/-- The cocycle of the complex of morphisms `K → K` attached to a cocycle of the endomorphism
algebra. -/
def repCocycle (n : ℤ) (a : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.Cocycle n) :
    Cocycle (liftComplex.{u, v, w, t, s} X K) (liftComplex.{u, v, w, t, s} X K) n :=
  Cocycle.mk ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom n a.1) (n + 1) rfl
    ((rep_d_eq_zero_iff.{u, v, w, t, s} X K n a.1).1 a.2)

/-- If two cocycles `a` and `b` of the endomorphism algebra differ by the coboundary `d c`, then
the corresponding cocycles of the complex of morphisms differ by the coboundary of the cochain
attached to `c`. -/
theorem repCocycle_sub (n : ℤ) (a b : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.Cocycle n)
    (c : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading (n - 1))
    (hc : (a.1 : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.A) - b.1 =
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d c) :
    (repCocycle.{u, v, w, t, s} X K n a).1 - (repCocycle.{u, v, w, t, s} X K n b).1 =
      δ (n - 1) n ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom (n - 1) c) := by
  have := (rep_algebraHom_eq_δ_iff.{u, v, w, t, s} X K n (a.1 - b.1) c).2 hc
  rw [map_sub] at this
  exact this

/-- The map from the cohomology of the endomorphism algebra to the cohomology classes of the
complex of morphisms `K → K`. -/
def repCohomologyToCohomologyClass (n : ℤ) :
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.Cohomology n →
      CohomologyClass (liftComplex.{u, v, w, t, s} X K) (liftComplex.{u, v, w, t, s} X K) n :=
  Quotient.lift (fun a => CohomologyClass.mk (repCocycle.{u, v, w, t, s} X K n a))
    (fun a b ⟨c, hc⟩ => by
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)]
      exact ⟨_, (repCocycle_sub.{u, v, w, t, s} X K n a b c hc).symm⟩)

/-- The map `repCohomologyToCohomologyClass` from the cohomology of the endomorphism algebra to
the cohomology classes of the complex of morphisms `K → K` is bijective. -/
theorem repCohomologyToCohomologyClass_bijective (n : ℤ) :
    Function.Bijective (repCohomologyToCohomologyClass.{u, v, w, t, s} X K n) := by
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · obtain ⟨a, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective y
    change CohomologyClass.mk (repCocycle.{u, v, w, t, s} X K n a) =
      CohomologyClass.mk (repCocycle.{u, v, w, t, s} X K n b) at h
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)] at h
    obtain ⟨β, hβ⟩ := h
    let c := ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom (n - 1)).symm β
    refine Quotient.sound ⟨c, ?_⟩
    refine (rep_algebraHom_eq_δ_iff.{u, v, w, t, s} X K n (a.1 - b.1) c).1 ?_
    rw [map_sub, LinearEquiv.apply_symm_apply]
    exact hβ.symm
  · obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
    let a := ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom n).symm z.1
    have ha : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.d a = 0 := by
      rw [rep_d_eq_zero_iff, LinearEquiv.apply_symm_apply]
      exact (Cocycle.mem_iff n (n + 1) rfl _).1 z.2
    refine ⟨Quotient.mk _ ⟨a, ha⟩, ?_⟩
    show CohomologyClass.mk (repCocycle.{u, v, w, t, s} X K n ⟨a, ha⟩) = _
    congr 1
    ext1
    exact LinearEquiv.apply_symm_apply _ _

/-- The cohomology of the endomorphism algebra of `K` is the cohomology of the complex of
morphisms `K → K`. -/
def repCohomologyEquivCohomologyClass (n : ℤ) :
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.Cohomology n ≃
      CohomologyClass (liftComplex.{u, v, w, t, s} X K) (liftComplex.{u, v, w, t, s} X K) n :=
  Equiv.ofBijective _ (repCohomologyToCohomologyClass_bijective.{u, v, w, t, s} X K n)

/-- **Equation 09M6 of the proof of Tag 09M5.** *"Since `K^•` is K-injective we have
`H^n(E) = Ext^n_{D(O)}(K^•, K^•)` for all `n ∈ ℤ`."* For `K` (more precisely `liftComplex K`,
the complex the endomorphism algebra is formed from) K-injective, the degree-`n` cohomology of
`E = Hom_{Comp^dg(O)}(K, K)` is in bijection with `Hom_{D(O)}(K, K[n])`. -/
def repCohomologyEquivDerivedHom [(liftComplex.{u, v, w, t, s} X K).IsKInjective] (n : ℤ) :
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.Cohomology n ≃
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) ⟶
        (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧) :=
  (repCohomologyEquivCohomologyClass.{u, v, w, t, s} X K n).trans
    ((CohomologyClass.homAddEquiv (K := liftComplex.{u, v, w, t, s} X K)
      (L := liftComplex.{u, v, w, t, s} X K) (n := n)).toEquiv.trans
      ((Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective _
        ((liftComplex.{u, v, w, t, s} X K)⟦n⟧))).trans
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso _).app _)
          ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
            (Functor.commShiftIso (DerivedCategory.Q (C := TensorModO.{u, v, w, t, s} X)) n).app
              (liftComplex.{u, v, w, t, s} X K)))))

/-- **Finitely many nonzero cohomology groups.** If `liftComplex K` is K-injective and only
finitely many of the groups `Hom_{D(O)}(K, K[n])` are nonzero, then the endomorphism algebra of
`K` has only finitely many nonzero cohomology groups. -/
theorem finite_setOf_nontrivial_cohomology_rep [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
    (h : {n : ℤ | ¬ Subsingleton (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) ⟶
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧)}.Finite) :
    {n : ℤ | Nontrivial ((Rep.{u, v, w, t, s, 0} X ℤ K).algebra.Cohomology n)}.Finite :=
  h.subset fun n hn hs => not_subsingleton_iff_nontrivial.2 hn
    ((repCohomologyEquivDerivedHom.{u, v, w, t, s} X K n).subsingleton_congr.2 hs)

end AlgebraicGeometry.RingedSite

end
