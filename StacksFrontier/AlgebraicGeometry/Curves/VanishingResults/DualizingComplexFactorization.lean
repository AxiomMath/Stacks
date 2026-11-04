module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dualizing complex under a factorization of the structure morphism

Let `X` be a proper scheme over a field `k` and suppose `X ⟶ Spec k` factors as
`X ⟶ Spec k' ⟶ Spec k` for a field `k'`. Then `k'/k` is finite and the dualizing complex
`ω_X^• = f^×(𝒪_{Spec k})` of [Stacks, Tag 0BS2] is the dualizing complex of `X` over `k'`; this is
part (1) of [Stacks, Tag 0E32].

The source proves `a = a' ∘ b` and `b(𝒪_{Spec k}) = 𝒪_{Spec k'}`, `b` being the right adjoint of
`Rg_*` for `g : Spec k' ⟶ Spec k`. Here the two dualizing complexes are compared through what they
represent: by clause (4) of [Stacks, Tag 0BS2] in degree zero
(`Stacks.Duality.dualityAddEquivZero`) both represent `K ↦ Hom(H⁰(X, K), -)` on `D_QCoh(𝒪_X)`,
into `k` and into `k'` respectively; `H⁰(X, K)` over `k` is `H⁰(X, K)` over `k'` with its scalars
restricted, by the composition formula for `Rf_*` and [Stacks, Tag 0DJK]; and for a finite
extension `k'/k` and a nonzero `k`-linear form `l` on `k'`, `ψ ↦ l ∘ ψ` identifies `k'`-linear
forms with `k`-linear forms, because `c ↦ (a ↦ l(ac))` identifies `k'` with `Hom_k(k', k)`. The
Yoneda lemma concludes.

## Main definitions

* `ModuleCat.restrictScalarsDualAddEquiv` — `Hom_{k'}(V, k') = Hom_k(V, k)`, naturally in `V`.
* `Stacks.Duality.derivedCohomologyOverFieldChangeIso` — `Hⁱ(X, -)` over `k` is `Hⁱ(X, -)` over
  `k'` with its scalars restricted.
* `Stacks.Duality.dualizingComplexOverFieldFactorIso` — **[Stacks, Tag 0E32], part (1)**:
  `ω_X^•` over `k` is `ω_X^•` over `k'`.
* `Stacks.Duality.dualizingSheafOverFieldFactorIso` — the same for `ω_X = H^{-1}(ω_X^•)`.
* `Stacks.Duality.extDualityAddEquivOfFactor` — clause (4) of [Stacks, Tag 0BS2] over `k'` for
  `ω_X^•`.

## Main results

* `Stacks.Duality.finite_of_isProper_comp` — `k'/k` is finite when `X` is nonempty.

## References

* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0DJK](https://stacks.math.columbia.edu/tag/0DJK)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

section FieldExtensionDual

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- The pairing `k' → Hom_k(k', k)`, `c ↦ (a ↦ l(a c))`, of a `k`-linear form `l` on `k'`. -/
@[sga "1 I 4.10" "special case"]
def traceFormPairing (l : k' →ₗ[k] k) : k' →ₗ[k] Module.Dual k k' where
  toFun c := l ∘ₗ LinearMap.mulRight k c
  map_add' c d := by ext a; simp [mul_add]
  map_smul' r c := by ext a; simp [mul_smul_comm]

/-- The pairing evaluates as `c ↦ (a ↦ l(a c))`. -/
theorem traceFormPairing_apply (l : k' →ₗ[k] k) (c a : k') :
    traceFormPairing l c a = l (a * c) :=
  rfl

/-- For a finite extension and a nonzero form, the pairing `c ↦ (a ↦ l(a c))` is bijective. -/
theorem traceFormPairing_bijective [Module.Finite k k'] (l : k' →ₗ[k] k) (hl : l ≠ 0) :
    Function.Bijective (traceFormPairing l) := by
  have hinj : Function.Injective (traceFormPairing l) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hc0
    apply hl
    ext a
    have := LinearMap.congr_fun hc (a * c⁻¹)
    rw [traceFormPairing_apply, mul_assoc, inv_mul_cancel₀ hc0, mul_one] at this
    simpa using this
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp hinj⟩

/-- For a finite field extension `k'/k` and a nonzero `k`-linear form `l` on `k'`, the pairing
`c ↦ (a ↦ l(a c))` is a `k`-linear isomorphism `k' ≃ Hom_k(k', k)`. -/
@[sga "1 I 4.10" "special case"]
noncomputable def traceFormPairingEquiv [Module.Finite k k'] (l : k' →ₗ[k] k) (hl : l ≠ 0) :
    k' ≃ₗ[k] Module.Dual k k' :=
  LinearEquiv.ofBijective _ (traceFormPairing_bijective l hl)

/-- `ModuleCat.traceFormPairingEquiv` evaluates as `c ↦ (a ↦ l(a c))`. -/
theorem traceFormPairingEquiv_apply [Module.Finite k k'] (l : k' →ₗ[k] k) (hl : l ≠ 0)
    (c a : k') : traceFormPairingEquiv l hl c a = l (a * c) :=
  rfl

/-- The inverse of the pairing recovers a linear form from its values. -/
theorem traceFormPairingEquiv_symm_spec [Module.Finite k k'] (l : k' →ₗ[k] k) (hl : l ≠ 0)
    (g : Module.Dual k k') (a : k') : l (a * (traceFormPairingEquiv l hl).symm g) = g a := by
  rw [← traceFormPairingEquiv_apply l hl, LinearEquiv.apply_symm_apply]

variable {V : Type*} [AddCommGroup V] [Module k' V] [Module k V] [IsScalarTower k k' V]

/-- The `k`-linear form `a ↦ g(a v)` on `k'` attached to a `k`-linear form `g` on a
`k'`-module `V` and `v ∈ V`. -/
def orbitForm (g : V →ₗ[k] k) (v : V) : Module.Dual k k' :=
  g ∘ₗ (LinearMap.toSpanSingleton k' V v).restrictScalars k

/-- `ModuleCat.orbitForm g v` evaluates as `a ↦ g(a v)`. -/
theorem orbitForm_apply (g : V →ₗ[k] k) (v : V) (a : k') : orbitForm g v a = g (a • v) :=
  rfl

/-- **`Hom_{k'}(V, k') = Hom_k(V, k)`** for a finite field extension `k'/k` and a nonzero
`k`-linear form `l` on `k'`: a `k'`-linear form `ψ` goes to `l ∘ ψ`. -/
noncomputable def dualEquivOfFieldExtension [Module.Finite k k'] (l : k' →ₗ[k] k) (hl : l ≠ 0) :
    (V →ₗ[k'] k') ≃ (V →ₗ[k] k) where
  toFun ψ := l ∘ₗ ψ.restrictScalars k
  invFun g :=
    { toFun v := (traceFormPairingEquiv l hl).symm (orbitForm g v)
      map_add' v w := by
        rw [← map_add]
        congr 1
        ext a
        simp [orbitForm_apply, smul_add]
      map_smul' b v := by
        apply (traceFormPairingEquiv l hl).injective
        ext a
        rw [traceFormPairingEquiv_apply, traceFormPairingEquiv_symm_spec, RingHom.id_apply,
          smul_eq_mul, traceFormPairingEquiv_apply, ← mul_assoc, traceFormPairingEquiv_symm_spec,
          orbitForm_apply, orbitForm_apply, mul_smul] }
  left_inv ψ := by
    ext v
    apply (traceFormPairingEquiv l hl).injective
    ext a
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [traceFormPairingEquiv_apply, traceFormPairingEquiv_symm_spec, orbitForm_apply,
      traceFormPairingEquiv_apply]
    simp [map_smul]
  right_inv g := by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearMap.coe_mk, AddHom.coe_mk]
    have := traceFormPairingEquiv_symm_spec l hl (orbitForm g v) 1
    rwa [one_mul, orbitForm_apply, one_smul] at this

/-- `ModuleCat.dualEquivOfFieldExtension` is composition with `l`. -/
theorem dualEquivOfFieldExtension_apply [Module.Finite k k'] (l : k' →ₗ[k] k) (hl : l ≠ 0)
    (ψ : V →ₗ[k'] k') : dualEquivOfFieldExtension (V := V) l hl ψ = l ∘ₗ ψ.restrictScalars k :=
  rfl

end FieldExtensionDual

section RestrictScalarsDual

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [Module.Finite k k']

/-- A `k'`-linear form `ψ` on `V` gives the `k`-linear form `l ∘ ψ` on `V` with its scalars
restricted. -/
def restrictScalarsDualMap (l : k' →ₗ[k] k) {V : ModuleCat.{u} k'} (ψ : V ⟶ of k' k') :
    (restrictScalars (algebraMap k k')).obj V ⟶ of k k :=
  ofHom
  { toFun v := l (ψ.hom v)
    map_add' v w := by
      change l (ψ.hom (v + w)) = l (ψ.hom v) + l (ψ.hom w)
      rw [map_add, map_add]
    map_smul' r v := by
      change l (ψ.hom (algebraMap k k' r • v)) = r • l (ψ.hom v)
      rw [map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul] }

/-- The inverse of `ModuleCat.restrictScalarsDualMap`. -/
noncomputable def restrictScalarsDualInv (l : k' →ₗ[k] k) (hl : l ≠ 0) {V : ModuleCat.{u} k'}
    (g : (restrictScalars (algebraMap k k')).obj V ⟶ of k k) : V ⟶ of k' k' := by
  letI : Module k V := Module.compHom V (algebraMap k k')
  haveI : IsScalarTower k k' V := ⟨fun r a v => by
    change (r • a) • v = algebraMap k k' r • (a • v)
    rw [Algebra.smul_def, mul_smul]⟩
  exact ofHom ((dualEquivOfFieldExtension (V := V) l hl).symm g.hom)

/-- `ModuleCat.restrictScalarsDualInv` is a right inverse of `ModuleCat.restrictScalarsDualMap`. -/
theorem restrictScalarsDualMap_inv (l : k' →ₗ[k] k) (hl : l ≠ 0) {V : ModuleCat.{u} k'}
    (g : (restrictScalars (algebraMap k k')).obj V ⟶ of k k) :
    restrictScalarsDualMap l (restrictScalarsDualInv l hl g) = g := by
  let : Module k V := Module.compHom V (algebraMap k k')
  have : IsScalarTower k k' V := ⟨fun r a v => by
    show (r • a) • v = algebraMap k k' r • (a • v)
    rw [Algebra.smul_def, mul_smul]⟩
  ext v
  exact congrArg (fun h => h v)
    ((dualEquivOfFieldExtension (V := V) l hl).apply_symm_apply g.hom)

/-- `ModuleCat.restrictScalarsDualInv` is a left inverse of `ModuleCat.restrictScalarsDualMap`. -/
theorem restrictScalarsDualInv_map (l : k' →ₗ[k] k) (hl : l ≠ 0) {V : ModuleCat.{u} k'}
    (ψ : V ⟶ of k' k') : restrictScalarsDualInv l hl (restrictScalarsDualMap l ψ) = ψ := by
  let : Module k V := Module.compHom V (algebraMap k k')
  have : IsScalarTower k k' V := ⟨fun r a v => by
    show (r • a) • v = algebraMap k k' r • (a • v)
    rw [Algebra.smul_def, mul_smul]⟩
  ext v
  exact congrArg (fun h => h v)
    ((dualEquivOfFieldExtension (V := V) l hl).symm_apply_apply ψ.hom)

/-- **`Hom_{k'}(V, k') = Hom_k(V, k)`** for a `k'`-module `V`, `k'/k` a finite field extension and
`l` a nonzero `k`-linear form on `k'`, as an isomorphism of groups of morphisms of modules: a
`k'`-linear form `ψ` goes to `l ∘ ψ`. -/
noncomputable def restrictScalarsDualAddEquiv (l : k' →ₗ[k] k) (hl : l ≠ 0)
    (V : ModuleCat.{u} k') :
    (V ⟶ of k' k') ≃+ ((restrictScalars (algebraMap k k')).obj V ⟶ of k k) where
  toFun := restrictScalarsDualMap l
  invFun := restrictScalarsDualInv l hl
  left_inv := restrictScalarsDualInv_map l hl
  right_inv := restrictScalarsDualMap_inv l hl
  map_add' ψ ψ' := by
    ext v
    exact map_add l (ψ.hom v) (ψ'.hom v)

/-- `ModuleCat.restrictScalarsDualAddEquiv` is natural in `V`. -/
theorem restrictScalarsDualAddEquiv_naturality (l : k' →ₗ[k] k) (hl : l ≠ 0)
    {V W : ModuleCat.{u} k'} (h : V ⟶ W) (ψ : W ⟶ of k' k') :
    restrictScalarsDualAddEquiv l hl V (h ≫ ψ) =
      (restrictScalars (algebraMap k k')).map h ≫ restrictScalarsDualAddEquiv l hl W ψ :=
  rfl

end RestrictScalarsDual


end ModuleCat

namespace Stacks.Duality

open DerivedPushforward

/-- `RΓ(Spec R, -)` on `D_QCoh(𝒪_{Spec R})` commutes with shifts, re-registered at the locally
small models. -/
instance commShift_derivedGlobalSectionsQuasicoherent (R : CommRingCat.{u}) :
    (derivedGlobalSectionsQuasicoherent R).CommShift ℤ :=
  derivedGlobalSectionsQuasicoherent_commShift R

/-- The derived Spec–Γ equivalence `D(R) ≌ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0], with
functor `(-)^~` and inverse `RΓ(Spec R, -)`. -/
def derivedTildeQuasicoherentEquivalence (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} R) ≌ quasiCoherentDerivedCategory (Spec R) :=
  have := derivedGlobalSectionsQuasicoherent_isEquivalence R
  (derivedTildeQuasicoherentAdjunction R).toEquivalence

/-- `RΓ(X, -) = RΓ(Spec R, Rf_* -)` on `D_QCoh(𝒪_X)` for `X` quasi-compact and quasi-separated
over `Spec R`. -/
def derivedGlobalSectionsOverAffine {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
    [QuasiCompact f] [QuasiSeparated f] :
    quasiCoherentDerivedCategory X ⥤ DerivedCategory (ModuleCat.{u} R) :=
  qcqsRestrictedDerivedPushforward f ⋙ derivedGlobalSectionsQuasicoherent R

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) {X : Scheme.{u}} (f' : X ⟶ Spec S)
  [QuasiCompact f'] [QuasiSeparated f']

/-- `R(f' ≫ g)_* ≅ Rf'_* ⋙ Rg_*` on the quasi-coherent derived categories. -/
def qcqsRestrictedDerivedPushforwardCompIso {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] [CompactSpace Y]
    [CompactSpace Z] :
    qcqsRestrictedDerivedPushforward (f ≫ g) ≅
      qcqsRestrictedDerivedPushforward f ⋙ qcqsRestrictedDerivedPushforward g :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPushforwardCompIso f g).symm.app K.obj))
    fun e => ObjectProperty.hom_ext _ ((derivedPushforwardCompIso f g).inv.naturality e.hom)

/-- `Rg_*` along `g = Spec φ`, read through the derived Spec–Γ equivalences, is derived restriction
of scalars along `φ`: `RΓ(Spec R, Rg_* M) ≅ RΓ(Spec S, M)` as `R`-complexes. This is
[Stacks, Tag 0DJK]. -/
def derivedGlobalSectionsQuasicoherentPushforwardIso :
    qcqsRestrictedDerivedPushforward (Spec.map φ) ⋙ derivedGlobalSectionsQuasicoherent R ≅
      derivedGlobalSectionsQuasicoherent S ⋙ (ModuleCat.restrictScalars φ.hom).mapDerivedCategory :=
  Functor.isoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (derivedTildeQuasicoherentEquivalence S).counitIso.symm _)
      _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (derivedGlobalSectionsQuasicoherent S)
      (derivedTildeCompDerivedQuasicoherentPushforwardIso φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (derivedTildeQuasicoherentEquivalence R).unitIso.symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

/-- **`RΓ(X, -)` over `R` is `RΓ(X, -)` over `S` with scalars restricted**, for `X` over `S` and
`R → S`: the composition formula for derived direct image followed by
`Stacks.Duality.derivedGlobalSectionsQuasicoherentPushforwardIso`. -/
def derivedGlobalSectionsOverAffineCompIso :
    derivedGlobalSectionsOverAffine (f' ≫ Spec.map φ) ≅
      derivedGlobalSectionsOverAffine f' ⋙ (ModuleCat.restrictScalars φ.hom).mapDerivedCategory :=
  Functor.isoWhiskerRight (qcqsRestrictedDerivedPushforwardCompIso f' (Spec.map φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedGlobalSectionsQuasicoherentPushforwardIso φ) ≪≫
    (Functor.associator _ _ _).symm

/-- **`RΓ(X, -)` over a field is `RΓ(Spec k, Rf_* -)`** on `D_QCoh(𝒪_X)`: the Leray
identification `AlgebraicGeometry.derivedGlobalSectionsOverIsoDerivedPushforwardOfField`, read on
the quasi-coherent derived category. -/
def derivedGlobalSectionsOverIsoAffine {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [QuasiSeparated f] :
    ObjectProperty.ι (Coherator.quasiCoherentProp X) ⋙ derivedGlobalSectionsOver f ≅
      derivedGlobalSectionsOverAffine f :=
  Functor.isoWhiskerLeft _ (derivedGlobalSectionsOverIsoDerivedPushforwardOfField k f)

section FieldChange

variable {k k' : Type u} [Field k] [Field k'] (φ : CommRingCat.of k ⟶ CommRingCat.of k')
  {X : Scheme.{u}} (f' : X ⟶ Spec (.of k')) [QuasiCompact f'] [QuasiSeparated f']

/-- `RΓ(X, -)` over `k` is `RΓ(X, -)` over `k'` followed by restriction of scalars along `φ`, on
`D_QCoh(𝒪_X)`, for `X` over `k'` regarded as a scheme over `k` through `Spec φ`. -/
def derivedGlobalSectionsOverFieldChangeIso :
    ObjectProperty.ι (Coherator.quasiCoherentProp X) ⋙ derivedGlobalSectionsOver (f' ≫ Spec.map φ) ≅
      (ObjectProperty.ι (Coherator.quasiCoherentProp X) ⋙ derivedGlobalSectionsOver f') ⋙
        (ModuleCat.restrictScalars φ.hom).mapDerivedCategory :=
  derivedGlobalSectionsOverIsoAffine (f' ≫ Spec.map φ) ≪≫
    derivedGlobalSectionsOverAffineCompIso φ f' ≪≫
    Functor.isoWhiskerRight (derivedGlobalSectionsOverIsoAffine f').symm _

/-- `Hⁱ(X, K)` over `k` is `Hⁱ(X, K)` over `k'` with its scalars restricted along `φ`, naturally in
`K ∈ D_QCoh(𝒪_X)`. -/
def derivedCohomologyOverFieldChangeIso (i : ℤ) :
    (ObjectProperty.ι (Coherator.quasiCoherentProp X) ⋙
      derivedGlobalSectionsOver (f' ≫ Spec.map φ)) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k) i ≅
      (ObjectProperty.ι (Coherator.quasiCoherentProp X) ⋙ derivedGlobalSectionsOver f') ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} k') i ⋙
          ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (derivedGlobalSectionsOverFieldChangeIso φ f') _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (ModuleCat.restrictScalars φ.hom) i)

end FieldChange

/-- The underlying morphism of `Stacks.Duality.qcohHom g` is `g`. -/
@[simp]
theorem qcohHom_hom {X : Scheme.{u}} {K L : quasiCoherentDerivedCategory X}
    (g : K.obj ⟶ L.obj) : (qcohHom g).hom = g :=
  ι_map_qcohHom g

section FieldChangeDuality

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
  (f' : X ⟶ Spec (.of k')) [QuasiCompact f'] [QuasiSeparated f']

/-- For a finite extension `k'/k`, a nonzero `k`-linear form `l` on `k'` and `X` over `k'`, maps
into the dualizing complex of `X` over `k` are maps into the dualizing complex of `X` over `k'`:
both are linear forms on `H⁰(X, K)`, over `k` and over `k'` respectively, and these correspond
by composing with `l`. -/
noncomputable def dualizingComplexOverFieldChangeHomAddEquiv [Module.Finite k k']
    (l : k' →ₗ[k] k) (hl : l ≠ 0) (K : quasiCoherentDerivedCategory X) :
    (K.obj ⟶ (dualizingComplexOverField
        (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj) ≃+
      (K.obj ⟶ (dualizingComplexOverField f').obj) :=
  (dualityAddEquivZero (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) K).trans <|
    (precompAddEquiv ((derivedCohomologyOverFieldChangeIso
      (CommRingCat.ofHom (algebraMap k k')) f' 0).app K)).trans <|
    (ModuleCat.restrictScalarsDualAddEquiv l hl _).symm.trans (dualityAddEquivZero f' K).symm

/-- The explicit form of `Stacks.Duality.dualizingComplexOverFieldChangeHomAddEquiv`. -/
theorem dualizingComplexOverFieldChangeHomAddEquiv_apply [Module.Finite k k']
    (l : k' →ₗ[k] k) (hl : l ≠ 0) (K : quasiCoherentDerivedCategory X)
    (α : K.obj ⟶ (dualizingComplexOverField
        (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj) :
    dualizingComplexOverFieldChangeHomAddEquiv f' l hl K α =
      (dualityAddEquivZero f' K).symm ((ModuleCat.restrictScalarsDualAddEquiv l hl _).symm
        ((derivedCohomologyOverFieldChangeIso (CommRingCat.ofHom (algebraMap k k')) f' 0).inv.app
          K ≫ dualityAddEquivZero (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) K α)) :=
  rfl

/-- `Stacks.Duality.dualizingComplexOverFieldChangeHomAddEquiv` is natural in `K`. -/
theorem dualizingComplexOverFieldChangeHomAddEquiv_naturality [Module.Finite k k']
    (l : k' →ₗ[k] k) (hl : l ≠ 0) {K L : quasiCoherentDerivedCategory X} (g : K.obj ⟶ L.obj)
    (α : L.obj ⟶ (dualizingComplexOverField
        (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj) :
    dualizingComplexOverFieldChangeHomAddEquiv f' l hl K (g ≫ α) =
      g ≫ dualizingComplexOverFieldChangeHomAddEquiv f' l hl L α := by
  have he := (derivedCohomologyOverFieldChangeIso (CommRingCat.ofHom (algebraMap k k')) f'
    0).inv.naturality (qcohHom (X := X) g)
  simp only [Functor.comp_map, ι_map_qcohHom] at he
  apply (dualityAddEquivZero f' K).injective
  rw [dualityAddEquivZero_naturality, dualizingComplexOverFieldChangeHomAddEquiv_apply,
    dualizingComplexOverFieldChangeHomAddEquiv_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, dualityAddEquivZero_naturality, ← Category.assoc, ← he,
    Category.assoc]
  apply (ModuleCat.restrictScalarsDualAddEquiv l hl _).injective
  rw [AddEquiv.apply_symm_apply, ModuleCat.restrictScalarsDualAddEquiv_naturality,
    AddEquiv.apply_symm_apply]
  rfl

omit [QuasiCompact f'] [QuasiSeparated f'] in
/-- A field extension carries a nonzero linear form over the smaller field. -/
theorem exists_linearForm_ne_zero : ∃ l : k' →ₗ[k] k, l ≠ 0 := by
  by_contra h
  exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff k (1 : k')).mp
    (fun l => by rw [not_not.mp (fun hl => h ⟨l, hl⟩)]; rfl))

/-- The dualizing complexes of `X` over `k` and over `k'` agree, for a finite extension `k'/k`
and a nonzero `k`-linear form `l` on `k'`: they represent the same functor on `D_QCoh(𝒪_X)`, by
`Stacks.Duality.dualizingComplexOverFieldChangeHomAddEquiv`. -/
noncomputable def dualizingComplexOverFieldChangeIsoOfForm [Module.Finite k k']
    (l : k' →ₗ[k] k) (hl : l ≠ 0) :
    dualizingComplexOverField (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) ≅
      dualizingComplexOverField f' :=
  Yoneda.ext _ _
    (fun {Z} h => qcohHom (dualizingComplexOverFieldChangeHomAddEquiv f' l hl Z h.hom))
    (fun {Z} h => qcohHom ((dualizingComplexOverFieldChangeHomAddEquiv f' l hl Z).symm h.hom))
    (fun {Z} h => by
      apply ObjectProperty.hom_ext
      rw [qcohHom_hom, qcohHom_hom, AddEquiv.symm_apply_apply])
    (fun {Z} h => by
      apply ObjectProperty.hom_ext
      rw [qcohHom_hom, qcohHom_hom, AddEquiv.apply_symm_apply])
    (fun {Z Z'} g h => by
      apply ObjectProperty.hom_ext
      rw [qcohHom_hom, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.FullSubcategory.comp_hom, qcohHom_hom,
        dualizingComplexOverFieldChangeHomAddEquiv_naturality])

omit [QuasiCompact f'] [QuasiSeparated f'] in
/-- **A field between `k` and the global functions of a nonempty proper `k`-scheme is finite over
`k`.** If `X ⟶ Spec k` is proper and factors through `Spec k'`, then `k'` embeds `k`-linearly
into `H⁰(X, 𝒪_X)`, which is finite-dimensional over `k` by [Stacks, Tag 02O6]. -/
theorem finite_of_isProper_comp [Nonempty X]
    [IsProper (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))] : Module.Finite k k' := by
  set f := f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))
  set r := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  set ψ := ((Scheme.ΓSpecIso (.of k')).inv ≫ f'.appTop).hom
  have hr : r = ψ.comp (algebraMap k k') := by
    simp only [r, ψ, f, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hfin := forall_finiteDimensional_cohomologyOverField_unit k f 0
  let e :=
    (cohomologyOverFieldZeroIsoSections k f (SheafOfModules.unit X.ringCatSheaf)).toLinearEquiv
  have : FiniteDimensional k ((ModuleCat.restrictScalars r).obj
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).obj
        (SheafOfModules.unit X.ringCatSheaf))) := Module.Finite.equiv e
  have : Nontrivial Γ(X, ⊤) := Stacks.EmptyLimitCounterexample.nontrivial_Γ_of_nonempty X
    (Classical.arbitrary X)
  let L : k' →ₗ[k] (ModuleCat.restrictScalars r).obj
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
    { toFun c := ψ c
      map_add' c d := ψ.map_add c d
      map_smul' a c := by
        rw [Algebra.smul_def, map_mul, RingHom.id_apply]
        show ψ (algebraMap k k' a) * ψ c = r a * ψ c
        rw [hr]
        rfl }
  exact Module.Finite.of_injective L ψ.injective

/-- On an empty scheme every object of `D_QCoh(𝒪_X)` is zero. -/
theorem isZero_quasiCoherentDerivedCategory_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y]
    (K : quasiCoherentDerivedCategory Y) : IsZero K := by
  have hM : ∀ M : Y.Modules, IsZero M := fun M =>
    (IsZero.iff_id_eq_zero M).mpr (Subsingleton.elim _ _)
  have hobj : IsZero K.obj :=
    Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj K.obj fun n => hM _
  rw [IsZero.iff_id_eq_zero]
  exact ObjectProperty.hom_ext _ (hobj.eq_of_src _ _)

end FieldChangeDuality

section Factorization

variable {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsProper f] (φ : CommRingCat.of k ⟶ CommRingCat.of k') (f' : X ⟶ Spec (.of k'))

/-- A proper `k`-scheme factoring through `Spec k'` is proper over `k'`. -/
theorem isProper_of_comp_eq (hf : f' ≫ Spec.map φ = f) : IsProper f' := by
  subst hf
  exact IsProper.of_comp f' (Spec.map φ)

/-- **[Stacks, Tag 0E32], part (1).** Let `X` be proper over a field `k` and suppose
`X ⟶ Spec k` factors as `X ⟶ Spec k' ⟶ Spec k` for a field `k'`. Then the dualizing complex
`ω_X^•` of `X` over `k` is the dualizing complex of `X` over `k'`; hence `ω_X^•` and `ω_X`
satisfy the properties of [Stacks, Tag 0BS2] with `k` replaced by `k'`.

As in the source, `k'/k` is finite because `k' ⊆ H⁰(X, 𝒪_X)`
(`Stacks.Duality.finite_of_isProper_comp`), and the two dualizing complexes both represent
`K ↦ Hom(H⁰(X, K), -)`, the `k`-dual and the `k'`-dual corresponding through a nonzero
`k`-linear form on `k'` (`Stacks.Duality.dualizingComplexOverFieldChangeIsoOfForm`). -/
@[stacks 0E32 "part (1), in the form the proof states it: omega_X^bullet over k is \
omega_X^bullet over k', along which the properties of Tag 0BS2 over k' transfer; omega_X is \
dualizingSheafOverFieldFactorIso and clause (4) over k' is extDualityAddEquivOfFactor"]
noncomputable def dualizingComplexOverFieldFactorIso (hf : f' ≫ Spec.map φ = f) :
    haveI := isProper_of_comp_eq f φ f' hf
    dualizingComplexOverField f ≅ dualizingComplexOverField f' := by
  haveI := isProper_of_comp_eq f φ f' hf
  letI := φ.hom.toAlgebra
  subst hf
  by_cases hX : Nonempty X
  · haveI : IsProper (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'))) := ‹_›
    haveI : Module.Finite k k' := finite_of_isProper_comp f'
    exact dualizingComplexOverFieldChangeIsoOfForm f' (exists_linearForm_ne_zero).choose
      (exists_linearForm_ne_zero).choose_spec
  · haveI : IsEmpty X := not_nonempty_iff.mp hX
    exact (isZero_quasiCoherentDerivedCategory_of_isEmpty _).iso
      (isZero_quasiCoherentDerivedCategory_of_isEmpty _)

/-- **[Stacks, Tag 0E32], part (1), for the dualizing sheaf**: `ω_X = H^{-1}(ω_X^•)` over `k` is
`ω_X` over `k'`. -/
noncomputable def dualizingSheafOverFieldFactorIso (hf : f' ≫ Spec.map φ = f) :
    haveI := isProper_of_comp_eq f φ f' hf
    dualizingSheafOverField f ≅ dualizingSheafOverField f' :=
  haveI := isProper_of_comp_eq f φ f' hf
  (DerivedCategory.homologyFunctor X.Modules (-1)).mapIso
    ((ObjectProperty.ι _).mapIso (dualizingComplexOverFieldFactorIso f φ f' hf))

/-- **Clause (4) of [Stacks, Tag 0BS2] over `k'`**, for the dualizing complex of `X` over `k`:
`Extⁱ_X(K, ω_X^•) = Hom_{k'}(H^{-i}(X, K), k')`, through
`Stacks.Duality.dualizingComplexOverFieldFactorIso`. -/
noncomputable def extDualityAddEquivOfFactor (hf : f' ≫ Spec.map φ = f)
    (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    haveI := isProper_of_comp_eq f φ f' hf
    DerivedCategory.Ext K.obj (dualizingComplexOverField f).obj i ≃+
      (derivedCohomologyOverField f' K.obj (-i) ⟶ ModuleCat.of k' k') :=
  haveI := isProper_of_comp_eq f φ f' hf
  (homCongrAddEquiv (Iso.refl K.obj) ((shiftFunctor (DerivedCategory X.Modules) i).mapIso
    ((ObjectProperty.ι _).mapIso (dualizingComplexOverFieldFactorIso f φ f' hf)))).trans
    (extDualityAddEquiv f' K i)

end Factorization

end Stacks.Duality
