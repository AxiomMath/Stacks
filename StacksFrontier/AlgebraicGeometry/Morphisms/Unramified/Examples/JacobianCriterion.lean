module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.JacobianMinor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.SquareJacobian

/-!
# The Jacobian criterion for unramifiedness and étaleness

Let `R` be a ring, let `g₁, …, g_m` be polynomials in `n` variables over `R`, and let `q` be a
prime of `R[x₁, …, x_n]` containing them at which the matrix `(∂gᵢ/∂x_j)` has rank `n`. Then the
structure morphism of `Z = Spec (R[x₁, …, x_n]/(g₁, …, g_m))` to `Spec R` is unramified at the
point of `Z` determined by `q`; in particular there are at least as many equations as variables.
In the extreme case of as many equations as variables, the morphism is moreover flat at that
point, hence étale there.

## Main results

* `AlgebraicGeometry.FullRankJacobianSystem.numVariables_le_numEquations`: a full-rank Jacobian
  forces at least as many equations as variables.
* `AlgebraicGeometry.FullRankJacobianSystem.unramifiedAt_of_jacobian_rank`: unramifiedness at
  the distinguished point.
* `AlgebraicGeometry.FullRankJacobianSystem.etaleAt_of_square_jacobian_rank`: étaleness there
  when the Jacobian is square.
* `AlgebraicGeometry.FullRankJacobianSystem.flatAt_of_square_jacobian`: flatness there when the
  Jacobian is square.

## Implementation notes

All four statements are read off one affine neighbourhood of the distinguished point: inverting
a maximal Jacobian minor that avoids the prime produces a basic open subset of the zero scheme
whose ring of sections is, over `R`, the corresponding localization of the quotient. The
unramified case uses the vanishing of the module of differentials of that localization, and the
square case uses that it is étale over `R` because it is standard smooth of relative dimension
zero. Flatness is then deduced from étaleness by passing to local rings.

## References

* [Stacks Project, Tag 024Y](https://stacks.math.columbia.edu/tag/024Y)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace FullRankJacobianSystem

variable {R : Type u} [CommRing R] {n m : ℕ}

/-- A full-rank Jacobian needs at least as many equations as variables. -/
@[stacks 024Y "enough_equations"]
public theorem numVariables_le_numEquations (S : FullRankJacobianSystem R n m) : n ≤ m :=
  S.jacobian_rank.symm.trans_le (Matrix.rank_le_height _)

/-- A polynomial avoiding the selected prime cuts out a basic affine open neighbourhood of the
distinguished point of the zero scheme whose ring of sections is the localization of the
quotient at the image of that polynomial, compatibly with the structure morphism. -/
private theorem exists_isAffineOpen_ringEquiv_localizationAway
    (S : FullRankJacobianSystem R n m) {g : MvPolynomial (Fin n) R} (hg : g ∉ S.prime) :
    ∃ (U : S.zeroScheme.Opens) (_ : IsAffineOpen U) (_ : S.point ∈ U)
      (e : U ≤ S.over ⁻¹ᵁ ⊤)
      (φ : Localization.Away (Ideal.Quotient.mk S.equationIdeal g) ≃+* Γ(S.zeroScheme, U)),
      ∀ r : R,
        φ (algebraMap R (Localization.Away (Ideal.Quotient.mk S.equationIdeal g)) r) =
          (S.over.appLE ⊤ U e).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
  classical
  let B := MvPolynomial (Fin n) R ⧸ S.equationIdeal
  let gB : B := Ideal.Quotient.mk S.equationIdeal g
  let X := S.zeroScheme
  let A := Γ(X, ⊤)
  let γR := (Scheme.ΓSpecIso (.of R)).inv
  let : Algebra R Γ(Spec (.of R), ⊤) := γR.hom.toAlgebra
  let : Algebra Γ(Spec (.of R), ⊤) A := S.over.appTop.hom.toAlgebra
  let : Algebra R A := (S.over.appTop.hom.comp γR.hom).toAlgebra
  let : IsScalarTower R Γ(Spec (.of R), ⊤) A := IsScalarTower.of_algebraMap_eq' rfl
  let eBA : B ≃ₐ[R] A := AlgEquiv.ofRingEquiv
    (f := (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv) fun r =>
      congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of A => h.hom r)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R B)))
  let gA : A := eBA gB
  let : IsLocalization.Away (eBA.toAlgHom gB) (Localization.Away gA) := by
    simpa [gA] using (inferInstance : IsLocalization.Away gA (Localization.Away gA))
  let eLQ : Localization.Away gB ≃ₐ[R] Localization.Away gA :=
    AlgEquiv.ofBijective
      (IsLocalization.Away.mapₐ (Localization.Away gB) (Localization.Away gA) eBA.toAlgHom gB)
      ⟨IsLocalization.Away.mapₐ_injective_of_injective (f := eBA.toAlgHom) gB
          (EquivLike.injective eBA),
        IsLocalization.Away.mapₐ_surjective_of_surjective (f := eBA.toAlgHom) gB
          (EquivLike.surjective eBA)⟩
  let U : X.Opens := X.basicOpen gA
  let hle : U ≤ ⊤ := X.basicOpen_le gA
  let : Algebra A Γ(X, U) := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : IsLocalization.Away gA Γ(X, U) := (isAffineOpen_top X).isLocalization_basicOpen gA
  let eQD : Localization.Away gA ≃ₐ[A] Γ(X, U) :=
    IsLocalization.algEquiv (.powers gA) (Localization.Away gA) Γ(X, U)
  let : Algebra R Γ(X, U) := ((S.over.appLE ⊤ U hle).hom.comp γR.hom).toAlgebra
  let : IsScalarTower R A Γ(X, U) := IsScalarTower.of_algebraMap_eq' (by
    ext r
    have happ := Scheme.Hom.appLE_map S.over (U := ⊤) (by simp) (homOfLE hle).op
    change (S.over.appLE ⊤ U hle).hom (γR.hom r) =
      (X.presheaf.map (homOfLE hle).op).hom (S.over.appTop.hom (γR.hom r))
    exact (congrArg
      (fun h : Γ(Spec (.of R), ⊤) ⟶ Γ(X, U) => h.hom (γR.hom r)) happ).symm)
  have hxU : S.point ∈ U := by
    have hTop := isAffineOpen_top X
    have hp : hTop.primeIdealOf ⟨S.point, by simp⟩ = X.isoSpec.hom S.point := by
      change (⊤ : X.Opens).toSpecΓ ⟨S.point, by simp⟩ = X.isoSpec.hom S.point
      rw [Scheme.Opens.toSpecΓ_top, Scheme.isoSpec_hom]
      rfl
    have hnotA : gA ∉ (hTop.primeIdealOf ⟨S.point, by simp⟩).asIdeal := by
      rw [hp, Scheme.isoSpec_Spec_hom]
      change (Scheme.ΓSpecIso (.of B)).hom.hom gA ∉ S.point.asIdeal
      rw [show (Scheme.ΓSpecIso (.of B)).hom.hom gA = gB from
        eBA.toRingEquiv.symm_apply_apply gB]
      exact S.mk_notMem_point_asIdeal hg
    change ((⟨S.point, by simp⟩ : (⊤ : X.Opens)) : X) ∈ U
    rw [← hTop.fromSpec_primeIdealOf ⟨S.point, by simp⟩]
    change hTop.primeIdealOf ⟨S.point, by simp⟩ ∈ hTop.fromSpec ⁻¹ᵁ U
    rw [hTop.fromSpec_preimage_basicOpen]
    exact hnotA
  exact ⟨U, (isAffineOpen_top X).basicOpen gA, hxU, hle,
    (eLQ.trans (eQD.restrictScalars R)).toRingEquiv,
    fun r => (eLQ.trans (eQD.restrictScalars R)).commutes r⟩

/-- **Stacks Project, Tag 024Y.** Full column rank of the Jacobian at a prime makes the
corresponding point of the zero scheme unramified over the base. -/
@[stacks 024Y "unramified_point"]
public theorem unramifiedAt_of_jacobian_rank (S : FullRankJacobianSystem R n m) :
    UnramifiedAt S.over S.point := by
  classical
  obtain ⟨rows, hminor, hΩ⟩ := exists_jacobianMinor_differentials_subsingleton S
  obtain ⟨U, hU, hxU, e, φ, hφ⟩ := exists_isAffineOpen_ringEquiv_localizationAway S hminor
  let : Algebra.Unramified R
      (Localization.Away (Ideal.Quotient.mk S.equationIdeal (jacobianMinor S rows))) :=
    ⟨⟨hΩ⟩, inferInstance⟩
  let : Algebra R Γ(S.zeroScheme, U) :=
    ((S.over.appLE ⊤ U e).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  let : Algebra.Unramified R Γ(S.zeroScheme, U) :=
    Algebra.Unramified.of_equiv (AlgEquiv.ofRingEquiv (f := φ) hφ)
  let : Algebra R Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom.toAlgebra
  let : Algebra Γ(Spec (.of R), ⊤) Γ(S.zeroScheme, U) := (S.over.appLE ⊤ U e).hom.toAlgebra
  let : IsScalarTower R Γ(Spec (.of R), ⊤) Γ(S.zeroScheme, U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact ⟨U, hU, hxU, ⊤, isAffineOpen_top _, e,
    ⟨Algebra.FormallyUnramified.of_restrictScalars R _ _,
      Algebra.FiniteType.of_restrictScalars_finiteType R _ _⟩⟩

/-- **Stacks Project, Tag 024Y.** A polynomial quotient with a square Jacobian of full rank at a
prime is étale over the base at the corresponding point. -/
@[stacks 024Y "square_etale"]
public theorem etaleAt_of_square_jacobian_rank (S : FullRankJacobianSystem R n m) (h : m = n) :
    EtaleAt S.over S.point := by
  subst h
  obtain ⟨U, hU, hxU, e, φ, hφ⟩ :=
    exists_isAffineOpen_ringEquiv_localizationAway S (jacobianDet_notMem_prime S)
  let : Algebra R Γ(S.zeroScheme, U) :=
    ((S.over.appLE ⊤ U e).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra
  have : Algebra.Etale R
      (Localization.Away (Ideal.Quotient.mk S.equationIdeal (jacobianDet S))) :=
    etale_localizationAway_jacobianDet S
  have : Algebra.Etale R Γ(S.zeroScheme, U) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofRingEquiv (f := φ) hφ)
  refine ⟨U, hU, hxU, ⊤, isAffineOpen_top _, e, ?_⟩
  refine (RingHom.Etale.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of R)).inv (S.over.appLE ⊤ U e)).mp ?_
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- **Stacks Project, Tag 024Y.** A polynomial quotient with a square Jacobian of full rank at a
prime is flat over the base at the corresponding point. -/
@[stacks 024Y "square_flat"]
public theorem flatAt_of_square_jacobian (S : FullRankJacobianSystem R n n) :
    IsFlatAt S.over.toLRSHom.toShHom S.point := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEtale⟩ := etaleAt_of_square_jacobian_rank S rfl
  let := (S.over.appLE V U hUV).hom.toAlgebra
  let p := (hV.primeIdealOf ⟨S.over S.point, hUV hxU⟩).asIdeal
  let q := (hU.primeIdealOf ⟨S.point, hxU⟩).asIdeal
  have hqp : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  exact show (S.over.stalkMap S.point).hom.Flat from
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso S.over V hV U hU hUV hxU)).mpr
      (RingHom.Flat.localRingHom
        ((RingHom.Etale.iff_flat_and_formallyUnramified.mp hEtale).1) q p hqp.1)

end FullRankJacobianSystem

end AlgebraicGeometry
