module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeCompositeIso

/-!
# The base change of a completed de Rham complex along an invertible map is an isomorphism

`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_id` says that the base change of a
completed de Rham complex along the *identity* of the coefficient ring is an isomorphism of
complexes.  This module says the same for a base change along a ring map which has a two-sided
inverse, the comparison of forms being invertible as well.

The only hypothesis beyond the invertibility is the `p`-adic completeness of the module, which is
[Stacks, Tag 07JB] and a field of `Crystalline.Pair`; in particular no square-zero condition and
no integrability enters, because the statement is proved degreewise on the values of the
connection, where there is no differential.

## Main results

* `Crystalline.CompletedConnection.baseChangeValuesComposite_bijective` — the comparison of the
  twice base-changed completed tensor product with the once base-changed one is bijective.  This
  is `Crystalline.CompletedConnection.baseChangeComposite_bijective` read on the values of a
  connection.
* `Crystalline.CompletedConnection.baseChangeValues_bijective_of_inverse` — **for ring maps
  `D → D'` and `D' → D` inverse to each other, and comparisons of forms `ψ`, `ψ'` inverse to each
  other, the map `ψ_*` induced on the values of a connection is bijective.**
* `Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_of_inverse` — consequently the base
  change map of completed de Rham complexes along such a map is an isomorphism of complexes.

## Implementation notes

The proof never inverts anything by hand.  Write `f` for the map induced by `ψ` and `g` for the
map induced by `ψ'` out of the base-changed module.  The composition law
`Crystalline.CompletedConnection.baseChangeValues_comp`, applied to the composite `D → D' → D`,
identifies `c ∘ g ∘ f` with the base change along the identity of `D`, where `c` is the
comparison of the twice base-changed module with the once base-changed one; that base change is
bijective by `Crystalline.CompletedConnection.baseChangeValues_id_bijective` and `c` is bijective
by the first result above, so `g ∘ f` is bijective.  Applied to `D' → D → D'` instead, with the
base-changed module in place of `M` — it is `p`-adically complete by
`Crystalline.CompletedConnection.isPAdicallyComplete_baseChangeCarrier`, so the same two inputs
are available — the law shows that some composite beginning with `g` is bijective, whence `g` is
injective.  An injective `g` with `g ∘ f` bijective is itself bijective, and then so is `f`.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Crystalline

open DividedPowers

universe u

namespace CompletedConnection

section CompositeValues

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  (D'' : Type u) [CommRing D''] [Algebra D' D''] [Algebra D D'']
  [IsScalarTower D D' D''] (M : Type u) [AddCommGroup M] [Module D M]
  (Omega : Type u) [AddCommGroup Omega] [Module D'' Omega]

/-- **The comparison of the twice base-changed completed tensor product with the once
base-changed one is bijective.**

It is `Crystalline.CompletedConnection.baseChangeComposite` tensored with the identity of the
forms and completed, which is the shape of
`Crystalline.CompletedDeRham.horizontalTerm`; the comparison itself is bijective with no
hypothesis, by `Crystalline.CompletedConnection.baseChangeComposite_bijective`, and tensoring an
isomorphism with an identity and completing preserves bijectivity. -/
public theorem baseChangeValuesComposite_bijective :
    Function.Bijective (baseChangeValuesComposite p D D' D'' M Omega) := by
  exact (congrArg Function.Bijective (funext fun z ↦
    CompletedDeRham.horizontalTerm_baseChangeComposite p D D' D'' M (fun _ : ℕ ↦ Omega) 0 z)).mp
    (CompletedDeRham.horizontalTerm_bijective p D''
      (baseChangeCarrier p D' D'' (baseChangeCarrier p D D' M)) (baseChangeCarrier p D D'' M)
      (fun _ : ℕ ↦ Omega) (baseChangeCompositeEquiv p D D' D'' M) 0)

end CompositeValues

section InverseValues

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  [Algebra D' D] [IsScalarTower D D' D] [IsScalarTower D' D D']
  (M : Type u) [AddCommGroup M] [Module D M]
  (Omega : Type u) [AddCommGroup Omega] [Module D Omega]
  (Omega' : Type u) [AddCommGroup Omega'] [Module D' Omega']
  (psi : Omega →ₛₗ[algebraMap D D'] Omega') (psi' : Omega' →ₛₗ[algebraMap D' D] Omega)
  (hpsi'psi : ∀ omega : Omega, psi' (psi omega) = omega)
  (hpsipsi' : ∀ omega : Omega', psi (psi' omega) = omega)

omit [IsScalarTower D' D D'] in
include hpsi'psi in
/-- The composite of the two induced maps, in the order `ψ` then `ψ'`, is bijective: after the
comparison of the twice base-changed module with the once base-changed one it is the base change
along the identity of `D`. -/
private theorem baseChangeValues_comp_bijective (hM : IsPAdicallyComplete p D M) :
    Function.Bijective (fun z : CompletedTensor p D Omega M ↦
      baseChangeValues p D' D (baseChangeCarrier p D D' M) Omega' Omega psi'
        (baseChangeValues p D D' M Omega Omega' psi z)) := by
  refine ((baseChangeValuesComposite_bijective p D D' D M Omega).of_comp_iff' _).mp ?_
  exact (congrArg Function.Bijective (funext fun z ↦
    baseChangeValues_comp p D D' D M Omega Omega' Omega psi psi' LinearMap.id
      (fun omega ↦ (hpsi'psi omega).symm) z)).mpr (baseChangeValues_id_bijective p D M Omega hM)

omit [IsScalarTower D D' D] in
include hpsipsi' in
/-- The map induced by `ψ'` out of the base-changed module is injective: the base-changed module
is `p`-adically complete, so the previous argument applies to it with the roles of the two rings
and the two comparisons interchanged. -/
private theorem baseChangeValues_injective_of_inverse :
    Function.Injective
      (baseChangeValues p D' D (baseChangeCarrier p D D' M) Omega' Omega psi') := by
  intro x y hxy
  exact (baseChangeValues_comp_bijective p D' D (baseChangeCarrier p D D' M) Omega' Omega psi' psi
    hpsipsi' (isPAdicallyComplete_baseChangeCarrier p D D' M)).1
    (congrArg (baseChangeValues p D D' _ Omega Omega' psi) hxy)

include hpsi'psi hpsipsi' in
/-- **The map induced on the values of a completed connection by a base change along an
invertible ring map is bijective.**

`ψ_*` followed by `ψ'_*` is bijective, and `ψ'_*` is injective; an injective map whose composite
after a given map is bijective is itself bijective, and then the given map is bijective too. -/
public theorem baseChangeValues_bijective_of_inverse (hM : IsPAdicallyComplete p D M) :
    Function.Bijective (baseChangeValues p D D' M Omega Omega' psi) := by
  have hcomp := baseChangeValues_comp_bijective p D D' M Omega Omega' psi psi' hpsi'psi hM
  have hginj := baseChangeValues_injective_of_inverse p D D' M Omega Omega' psi psi' hpsipsi'
  exact (Function.Bijective.of_comp_iff' ⟨hginj, hcomp.2.of_comp⟩ _).mp hcomp

end InverseValues

end CompletedConnection

namespace CompletedDeRham

section InverseComplex

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u) [CommRing D'] [Algebra D D']
  [Algebra D' D] [IsScalarTower D D' D] [IsScalarTower D' D D']
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[algebraMap D D'] Om' i)
  (psi' : ∀ i, Om' i →ₛₗ[algebraMap D' D] Om i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} (d' : D' → Om' 1) (nabla : CompletedConnection p D (Om 1) d M)
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, psi 1 (d x) = d' (algebraMap D D' x))
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')
  (hpsi_wedge : ∀ (i : ℕ) (omega : Om i) (eta : Om 1),
    psi (i + 1) (wedge i omega eta) = wedge' i (psi i omega) (psi 1 eta))
  (hpsi_deRham : ∀ (i : ℕ) (omega : Om i),
    psi (i + 1) (deRham i omega) = deRham' i (psi i omega))
  (hpsi'psi : ∀ (i : ℕ) (omega : Om i), psi' i (psi i omega) = omega)
  (hpsipsi' : ∀ (i : ℕ) (omega : Om' i), psi i (psi' i omega) = omega)

include hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hpsi'psi hpsipsi' in
/-- **The base change map of completed de Rham complexes along an invertible ring map is an
isomorphism of complexes.**

The ring maps `D → D'` and `D' → D` are inverse to each other — that is the pair of instances
`IsScalarTower D D' D` and `IsScalarTower D' D D'`, the algebra maps `D → D` and `D' → D'` being
the identities — and so are the graded comparisons of forms, by `hpsi'psi` and `hpsipsi'`.  Every
component of the base change map is then bijective by
`Crystalline.CompletedConnection.baseChangeValues_bijective_of_inverse`, and a chain map of
complexes of abelian groups with bijective components is an isomorphism.

The only other hypothesis is `hM`, the `p`-adic completeness of `M`, which is
[Stacks, Tag 07JB]; the two square-zero conditions are what make the two complexes exist and are
not used otherwise. -/
public theorem isIso_baseChangeComplexHom_of_inverse (hM : IsPAdicallyComplete p D M)
    (hsq : IsSquareZero p D Om wedge deRham M nabla hleib)
    (hsq' : IsSquareZero p D' Om' wedge' deRham'
      (CompletedConnection.baseChangeCarrier p D D' M)
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d' (psi 1) nabla hd'add hd'leib
        hpsi1) hleib') :
    IsIso (baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham' d' nabla
      hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq') := by
  have : ∀ i : ℕ, IsIso ((baseChangeComplexHom p D D' M Om Om' psi wedge wedge' deRham deRham'
      d' nabla hd'add hd'leib hpsi1 hleib hleib' hpsi_wedge hpsi_deRham hsq hsq').f i) :=
    fun i ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
      (CompletedConnection.baseChangeValues_bijective_of_inverse p D D' M (Om i) (Om' i)
        (psi i) (psi' i) (hpsi'psi i) (hpsipsi' i) hM)
  exact HomologicalComplex.Hom.isIso_of_components _

end InverseComplex

end CompletedDeRham

end Crystalline

end
