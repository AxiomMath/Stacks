module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.StrictHenselizationStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.StrictHenselizationStalkDerived
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of `R^j α_* ℱ` at `Spec k̄` as a `G_k`-module

Let `k` be a finite field, `k̄` an algebraic closure of `k`, `G_k = Gal(k̄/k)`, and
`α : X ⟶ Spec k` quasi-compact and quasi-separated. For an abelian sheaf `ℱ` on `X_étale` and every
`j ≥ 0`, Étale Cohomology, Theorem 03Q9 identifies the stalk `(R^j α_* ℱ)_{Spec k̄}` with
`H^j(X_{k̄}, ℱ|_{X_{k̄}})`: here the strict henselization of `Spec k` at `Spec k̄` is `Spec k̄`
itself, `k` being perfect. Tag 03ST asserts that this identification is an isomorphism of
`G_k`-modules, the stalk carrying the Galois action of Étale Cohomology Section 03QW and the
cohomology the action `σ ↦ (Spec σ × id_X)^*`.

## Main results

* `Stacks.Frobenius.isIso_fibreComparisonNatTrans` — the degree-zero comparison is an
  isomorphism: Stacks 03Q9 in degree zero.
* `Stacks.Frobenius.acyclic_fieldBaseChangePullbackAb_of_injective` — restriction to `X_K`
  carries injective sheaves to `Γ(X_K, -)`-acyclic ones: the input of 03Q9 in positive degrees.
* `Stacks.Frobenius.galoisCohomologyAction_one`, `Stacks.Frobenius.galoisCohomologyAction_mul` —
  `σ ↦ (Spec σ × id_X)^*` is a left action of `G_k` on `H^j(X_K, ℱ|_{X_K})`.
* `Stacks.Frobenius.higherDirectImageFibreMap_isIso_galoisEquivariant` — **Tag 03ST.**
* `Stacks.Frobenius.higherDirectImageFibreAddEquiv_smul` — the same, as an isomorphism of
  `G_k`-modules `Stacks.Frobenius.higherDirectImageFibreAddEquiv`.

## Implementation notes

*The hypothesis on `α`.* The source places 03ST "in the situation above", a scheme `X` over the
finite field `k`, and appeals to Theorem 03Q9 for the identification. Theorem 03Q9 is stated for a
quasi-compact and quasi-separated morphism, and the identification it provides exists only then:
for `X` an infinite disjoint union of copies of `Spec k` and `ℱ` the sheaf whose stalk on the
`n`-th copy is the `G_k`-module of locally constant functions on `G_k / U_n` for a strictly
decreasing sequence of open subgroups `U_n`, the stalk `colim_L Π_n (ℱ_n)^{G_L}` is a proper
subgroup of `H^0(X_{k̄}, ℱ) = Π_n ℱ_n`. The theorem below therefore carries the hypothesis of
03Q9, `α` quasi-compact and quasi-separated, and nothing else.

*The identification.* It is `Stacks.Frobenius.higherDirectImageFibreMap`: the degree-zero
comparison of 03Q9, which restricts a germ of a section of `α_* ℱ` over an étale neighbourhood of
`Spec k̄` to the geometric fibre, passed to right derived functors. It is an isomorphism by the two
inputs of 03Q9 — degree zero and acyclicity on injectives — proved over an arbitrary base for a
quasi-compact quasi-separated morphism in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/StrictHenselizationStalkSections.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/StrictHenselizationStalkDerived.lean`, and transported to `X_{k̄}` along the isomorphism
`X_{k̄} ≅ X ×_k Spec 𝒪^{sh}` of
`Stacks.Frobenius.isIso_geometricFibreToStrictHenselizationBaseChange_fieldGeometricPoint`.

## References

* [Stacks Project, Tag 03ST](https://stacks.math.columbia.edu/tag/03ST)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03QW](https://stacks.math.columbia.edu/tag/03QW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology Stacks.RightDerivedComp

universe u

namespace Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
  (X : Over (Spec (.of k)))

/-- **Stacks 03Q9 in degree zero at `Spec K ⟶ Spec k`.** For `α : X ⟶ Spec k` quasi-compact and
quasi-separated and `K` separable over `k`, the comparison `(α_* F)_{Spec K} ⟶ Γ(X_K, F|_{X_K})`
is an isomorphism. -/
theorem isIso_fibreComparisonNatTrans [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [Algebra.IsSeparable k K] : IsIso (fibreComparisonNatTrans K X) := by
  rw [← fibreSectionsComparisonAb_eq K X fieldBigEtaleSite fieldBigEtaleSite_contains,
    fibreSectionsComparisonAb_def]
  have := isIso_geometricFibreToStrictHenselizationBaseChange_fieldGeometricPoint K
    fieldBigEtaleSite fieldBigEtaleSite_contains X
  have : ∀ F, IsIso ((pushforwardStalkToStrictHenselizationSectionsAb fieldBigEtaleSite
      fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K)).app F) := fun F =>
    LimitExt.isIso_pushforwardStalkToStrictHenselizationSectionsAb_app fieldBigEtaleSite
      fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K) F
  have := NatIso.isIso_of_isIso_app (pushforwardStalkToStrictHenselizationSectionsAb
    fieldBigEtaleSite fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K))
  infer_instance

/-- **The input of Stacks 03Q9 in positive degrees at `Spec K ⟶ Spec k`.** For `α : X ⟶ Spec k`
quasi-compact and quasi-separated and `K` separable over `k`, restriction to `X_K` carries
injective sheaves on `X_étale` to `Γ(X_K, -)`-acyclic ones. -/
theorem acyclic_fieldBaseChangePullbackAb_of_injective [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [Algebra.IsSeparable k K] (Z : Sheaf (smallEtaleTopology X.left) Ab.{u + 1})
    (hZ : Injective Z) :
    acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
      ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj Z) := by
  have := hZ
  have := isIso_geometricFibreToStrictHenselizationBaseChange_fieldGeometricPoint K
    fieldBigEtaleSite fieldBigEtaleSite_contains X
  have := isEquivalence_smallEtalePullbackAb_of_isIso
    (geometricFibreToStrictHenselizationBaseChange fieldBigEtaleSite fieldBigEtaleSite_contains
      X.hom (fieldGeometricPoint K))
  have hN := (rightAcyclic_iff_acyclic _ _).1
    (LimitExt.rightAcyclic_strictHenselizationPullback_of_injective fieldBigEtaleSite
      fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K) Z)
  have hι : acyclic (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
      ((smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange fieldBigEtaleSite
        fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K))).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource fieldBigEtaleSite
          fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K))).obj Z)) :=
    fun n hn => (hN n hn).of_iso
      ((objIsoOfAcyclicImage
          (smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange fieldBigEtaleSite
            fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K)))
          (Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1})
          (fun m hm => isZero_rightDerived_obj_of_exact _ _ m hm)
          (fun Y hY => have := hY
            have := (smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange
              fieldBigEtaleSite fieldBigEtaleSite_contains X.hom
                (fieldGeometricPoint K))).injective_obj Y
            acyclic_of_injective _ _) n).symm ≪≫
        ((Stacks.DerivedFunctor.rightDerivedIso
          (asIso (smallEtaleGlobalSectionsRestrictionAb
            (geometricFibreToStrictHenselizationBaseChange fieldBigEtaleSite
              fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K)))) n).app _).symm)
  exact acyclic_of_iso _ ((geometricFibrePullbackAbCompIso fieldBigEtaleSite
    fieldBigEtaleSite_contains X.hom (fieldGeometricPoint K)).app Z) hι

section GaloisModule

variable [QuasiCompact X.hom] [QuasiSeparated X.hom] [Algebra.IsSeparable k K]

/-- The comparison of Theorem 03Q9 in degree `j` is an isomorphism. -/
@[sga "4½ Rapport 1.4" "special case", sga "7 XXII 2.2" "partial"]
instance isIso_higherDirectImageFibreMap_of_quasiCompact (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    IsIso (higherDirectImageFibreMap K X
      (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F) :=
  isIso_higherDirectImageFibreMap K X (isIso_fibreComparisonNatTrans K X)
    (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F

/-- The Galois action on `H^j(X_K, F|_{X_K})` is the Galois action on the stalk of `R^j α_* F`,
conjugated by the comparison of Theorem 03Q9. -/
theorem galoisCohomologyAction_eq_inv_comp (σ : K ≃ₐ[k] K) (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    galoisCohomologyAction K X σ j F =
      inv (higherDirectImageFibreMap K X (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F) ≫
        (fieldGaloisStalkAction K σ).app (((smallEtalePushforwardAb X.hom).rightDerived j).obj F) ≫
          higherDirectImageFibreMap K X
            (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F := by
  rw [galoisStalkAction_comp_higherDirectImageFibreMap, IsIso.inv_hom_id_assoc]

/-- The identity of `K` acts as the identity on `H^j(X_K, F|_{X_K})`. -/
theorem galoisCohomologyAction_one (j : ℕ) (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    galoisCohomologyAction K X (1 : K ≃ₐ[k] K) j F = 𝟙 _ := by
  rw [galoisCohomologyAction_eq_inv_comp, fieldGaloisStalkAction_one, NatTrans.id_app,
    Category.id_comp, IsIso.inv_hom_id]

/-- `σ ↦ (Spec σ × id_X)^*` is a left action of `G_k` on `H^j(X_K, F|_{X_K})`. -/
theorem galoisCohomologyAction_mul (σ τ : K ≃ₐ[k] K) (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    galoisCohomologyAction K X (σ * τ) j F =
      galoisCohomologyAction K X τ j F ≫ galoisCohomologyAction K X σ j F := by
  rw [galoisCohomologyAction_eq_inv_comp, galoisCohomologyAction_eq_inv_comp K X τ,
    galoisCohomologyAction_eq_inv_comp K X σ, fieldGaloisStalkAction_mul, NatTrans.comp_app]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

end GaloisModule

section Packaging

variable [QuasiCompact X.hom] [QuasiSeparated X.hom] [Algebra.IsSeparable k K]

/-- **`H^j(X_K, F|_{X_K})` as a `G_k`-module**, `σ` acting by `(Spec σ × id_X)^*`. -/
@[instance_reducible]
def galoisCohomologyDistribMulAction (j : ℕ) (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    DistribMulAction (K ≃ₐ[k] K)
      (((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F)) where
  smul σ x := ConcreteCategory.hom (galoisCohomologyAction K X σ j F) x
  one_smul x := ConcreteCategory.congr_hom (galoisCohomologyAction_one K X j F) x
  mul_smul σ τ x := ConcreteCategory.congr_hom (galoisCohomologyAction_mul K X σ τ j F) x
  smul_zero σ := map_zero (galoisCohomologyAction K X σ j F).hom
  smul_add σ x y := map_add (galoisCohomologyAction K X σ j F).hom x y

/-- **The identification of Theorem 03Q9 in degree `j`, as an additive equivalence**
`(R^j α_* F)_{Spec K} ≃+ H^j(X_K, F|_{X_K})`. -/
@[sga "7 XXII 2.2" "partial"]
def higherDirectImageFibreAddEquiv (j : ℕ) (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    ((smallEtalePushforwardAb X.hom).rightDerived j ⋙
        smallEtaleStalkAb (specAlgebraMap k K)).obj F ≃+
      ((Sheaf.Γ (smallEtaleTopology (fieldBaseChange X K)) Ab.{u + 1}).rightDerived j).obj
        ((smallEtalePullbackAb (pullback.fst X.hom (specAlgebraMap k K))).obj F) :=
  (asIso (higherDirectImageFibreMap K X (acyclic_fieldBaseChangePullbackAb_of_injective K X) j
    F)).addCommGroupIsoToAddEquiv

/-- **The identification of Theorem 03Q9 is a map of `G_k`-modules**, the stalk carrying the
`G_k`-module structure `Stacks.Frobenius.galoisHigherDirectImageStalkDistribMulAction` of Étale
Cohomology Section 03QW and the cohomology `Stacks.Frobenius.galoisCohomologyDistribMulAction`. -/
@[sga "7 XXII 2.2" "more general"]
theorem higherDirectImageFibreAddEquiv_smul (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) (σ : K ≃ₐ[k] K)
    (x : ((smallEtalePushforwardAb X.hom).rightDerived j ⋙
        smallEtaleStalkAb (specAlgebraMap k K)).obj F) :
    higherDirectImageFibreAddEquiv K X j F
        (@HSMul.hSMul _ _ _
          (@instHSMul _ _ (galoisHigherDirectImageStalkDistribMulAction K X j F).toSMul) σ x) =
      @HSMul.hSMul _ _ _
        (@instHSMul _ _ (galoisCohomologyDistribMulAction K X j F).toSMul) σ
        (higherDirectImageFibreAddEquiv K X j F x) :=
  ConcreteCategory.congr_hom
    (galoisStalkAction_comp_higherDirectImageFibreMap K X σ
      (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F) x

end Packaging

/-- **Stacks Project, Tag 03ST.** Let `k` be a finite field, `K` an algebraic closure of `k`,
`G_k = Gal(K/k)`, `α : X ⟶ Spec k` quasi-compact and quasi-separated, and `ℱ` an abelian sheaf on
`X_étale`. For every `j`, the identification `(R^j α_* ℱ)_{Spec K} ≅ H^j(X_K, ℱ|_{X_K})` of
Étale Cohomology, Theorem 03Q9 is an isomorphism of `G_k`-modules:

* it is an isomorphism;
* it carries the Galois action of Étale Cohomology Section 03QW on the stalk at `Spec K` of the
  `j`-th higher direct image (`Stacks.Frobenius.fieldGaloisStalkAction`, which is the base's
  `Stacks.Frobenius.galoisStalkAction` at the rational point `𝟙 (Spec k)`) to the action
  `σ ↦ (Spec σ × id_X)^*` on cohomology (`Stacks.Frobenius.galoisCohomologyAction`);
* the latter is a left action of `G_k`, as the former is (`fieldGaloisStalkAction_one`,
  `fieldGaloisStalkAction_mul`).

The identification is `Stacks.Frobenius.higherDirectImageFibreMap`: the degree-zero comparison of
03Q9 — restriction of the germ of a section of `α_* ℱ` over an étale neighbourhood of `Spec K` to
the geometric fibre `X_K` — passed to right derived functors; the strict henselization of `Spec k`
at `Spec K` is `Spec K`, the finite field `k` being perfect. The hypothesis on `α` is that of
Theorem 03Q9, whose identification exists only then; see the module docstring.

In the language of modules: `Stacks.Frobenius.higherDirectImageFibreAddEquiv` is an additive
equivalence which is `G_k`-equivariant (`Stacks.Frobenius.higherDirectImageFibreAddEquiv_smul`) for
the `G_k`-module structures `Stacks.Frobenius.galoisHigherDirectImageStalkDistribMulAction` and
`Stacks.Frobenius.galoisCohomologyDistribMulAction`. -/
@[stacks 03ST,
  sga "4½ Arcata 2.3.3" "special case",
  sga "4½ Rapport 1.4" "special case",
  sga "7 XXII 2.2" "more general"]
theorem higherDirectImageFibreMap_isIso_galoisEquivariant [Finite k] [Algebra.IsAlgebraic k K]
    [QuasiCompact X.hom] [QuasiSeparated X.hom] (j : ℕ)
    (F : Sheaf (smallEtaleTopology X.left) Ab.{u + 1}) :
    IsIso (higherDirectImageFibreMap K X (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F) ∧
      (∀ σ : K ≃ₐ[k] K,
        (fieldGaloisStalkAction K σ).app (((smallEtalePushforwardAb X.hom).rightDerived j).obj F) ≫
            higherDirectImageFibreMap K X (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F =
          higherDirectImageFibreMap K X (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F ≫
            galoisCohomologyAction K X σ j F) ∧
      galoisCohomologyAction K X (1 : K ≃ₐ[k] K) j F = 𝟙 _ ∧
      ∀ σ τ : K ≃ₐ[k] K, galoisCohomologyAction K X (σ * τ) j F =
        galoisCohomologyAction K X τ j F ≫ galoisCohomologyAction K X σ j F :=
  ⟨inferInstance,
    fun σ => galoisStalkAction_comp_higherDirectImageFibreMap K X σ
      (acyclic_fieldBaseChangePullbackAb_of_injective K X) j F,
    galoisCohomologyAction_one K X j F, fun σ τ => galoisCohomologyAction_mul K X σ τ j F⟩

end Stacks.Frobenius

end
