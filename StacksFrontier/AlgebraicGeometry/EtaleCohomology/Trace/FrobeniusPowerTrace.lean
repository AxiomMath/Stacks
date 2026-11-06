module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.FieldTheory.Finite.ExtensionInAlgClosure

/-!
# The traces of the powers of `π_X^*` through finite extensions of the base field

Let `X` be a separated scheme of finite type over a finite field `k` with `p ^ q` elements, and
`k ⊆ k' ⊆ k̄` an intermediate field with `p ^ (q m)` elements. The identification
`RΓ_c(X'_k̄, K|_{X'}) ≅ RΓ_c(X_k̄, K)` for `X' = X ×_k k'` carries the canonical Frobenius of `X'`
over `k'` to the `m`-th power of that of `X` over `k`
(`Stacks.EtaleCohomology.compactSupportFieldExtensionIso_comm`). Hence perfectness transfers and
`Tr((π_X^*)^m | RΓ_c(X_k̄, K)) = Tr(π_{X'}^* | RΓ_c(X'_k̄, K|_{X'}))`: the traces of the powers
of Frobenius are the traces of Frobenius over the extensions `k_m`.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_pow_canonicalCompactSupportFrobenius_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius CategoryTheory.FilteredDerived

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (k' : Type u) [Field k'] [Algebra k k']
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra k' kbar] [IsScalarTower k k' kbar]
  [Fintype k'] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
  (hcard : Fintype.card k = p ^ q)

/-- **The trace of `(π_X^*)^m` is the trace of the Frobenius of `X ×_k k'`**, for `k'` with
`p ^ (q m)` elements. -/
theorem perfectDerivedTrace_pow_canonicalCompactSupportFrobenius_eq (m : ℕ) (hm : 0 < m)
    (hcard' : Fintype.card k' = p ^ (q * m)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hperf' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ (pullback.snd f (specAlgebraMap k k'))
        (compactificationFieldBaseChange f j k') kbar
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj K)))) :
    ∃ hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K)),
      perfectDerivedTrace Λ ⟨_, hperf⟩
          (((End.of (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard K))) ^ m :
              End (DerivedCategory.Plus.ι.obj
                (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K))).asHom) =
        perfectDerivedTrace Λ ⟨_, hperf'⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ (pullback.snd f (specAlgebraMap k k'))
            (compactificationFieldBaseChange f j k') kbar p (q * m) hcard'
            ((etaleModuleInverseImage.{u, 0} Λ
              (pullback.fst f (specAlgebraMap k k'))).mapCochainComplexPlus.obj K))) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  let e := DerivedCategory.Plus.ι.mapIso (compactSupportFieldExtensionIso Λ f j k' kbar K)
  refine ⟨StacksDraft.Perfect.isPerfect_of_iso e.symm hperf', ?_⟩
  refine (perfectDerivedTrace_congr Λ ⟨_, hperf'⟩ ⟨_, _⟩ e _ _ ?_).symm
  have hc := congrArg DerivedCategory.Plus.ι.map
    (compactSupportFieldExtensionIso_comm Λ f j k' kbar p q hcard n hcard' K)
  refine ((DerivedCategory.Plus.ι.map_comp _ _).symm.trans hc).trans
    ((DerivedCategory.Plus.ι.map_comp _ _).trans ?_)
  congr 1
  exact congrArg End.asHom (map_pow (DerivedCategory.Plus.ι.mapEnd
    (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar K))
    (End.of (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard K)) (n + 1))

/-- **A finite projective representative of an endomorphism of a perfect complex.** An
endomorphism `φ` of a perfect complex `K` is represented by a chain endomorphism of a bounded
complex of finite projective modules. -/
theorem exists_finiteProjectiveComplex_endo {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat.{v} R)) (hK : StacksDraft.Perfect.IsPerfect K) (φ : K ⟶ K) :
    ∃ (Q : CochainComplex (ModuleCat.{v} R) ℤ) (_ : finiteProjectiveComplex R Q) (g : Q ⟶ Q)
      (eM : DerivedCategory.Q.obj Q ≅ K), DerivedCategory.Q.map g = eM.hom ≫ φ ≫ eM.inv := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff R K).mp hK
  have := isKProjective_of_finiteProjectiveComplex R hP
  obtain ⟨g, hg⟩ := exists_map_eq_of_isKProjective P P (e.hom ≫ φ ≫ e.inv)
  exact ⟨P, hP, g, e, hg⟩

end Stacks.EtaleCohomology
