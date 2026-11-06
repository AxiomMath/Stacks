module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantCompactSupportTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDegreeZeroDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CyclotomicRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpPairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionCoeffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceRestrictScalars
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.TraceTarget
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ForgetCoefficients

/-!
# The Galois-equivariant trace `H²_c(X_k̄, μ_n) ⟶ ℚ/ℤ`

Let `X` be a smooth geometrically connected curve over `k`, `k̄` an algebraic closure which is
separable over `k`, `j : X ⟶ X̄` a compactification and `n` an integer invertible in `k̄`. Write
`ρ_μ` for `μ_n(k̄)` as a `ℤ/n`-module with its action of `π₁(X)`
(`AlgebraicGeometry.cyclotomicContinuousModule`), `ℱ_μ` for its sheaf, `K₀` for an injective
resolution of `j_! ℱ_μ` on `X̄` and `K = res_ℤ K₀`, a complex of abelian sheaves. This file
provides the trace of the Poincaré pairing of Tag 03VM.

* **The trace** `tr : H²_c(X_k̄, ℱ_μ) ⟶ ℚ/ℤ` (`AlgebraicGeometry.compactSupportCyclotomicTrace`) is
  Tag 03VK at `ρ_μ`: `Ψ : H²_c(X_k̄, ℱ_μ) ≅ Hom(μ_n, (ρ_μ)_N) = Hom(μ_n, μ_n) = ℤ/n ⊂ ℚ/ℤ`, the
  middle identification being the scalar of an endomorphism of the cyclic group `μ_n`
  (`Stacks.CharacterModule.cyclicEndScalar`). No root of unity is chosen. It is invariant under
  `Aut_k(k̄)` on the Galois module `H²(RΓ^Gal_c(X_k̄, ℱ_μ))`
  (`AlgebraicGeometry.compactSupportCyclotomicTrace_galois`): `Ψ` is equivariant for the action on
  `Hom(μ_n, μ_n)` by conjugation (Tag 03VK), and the scalar of a conjugate is the scalar.
* **Change of coefficients for `Γ^Gal`**: `Γ^Gal_ℤ(res_ℤ L) ≅ res_ℤ Γ^Gal_Λ(L)` as discrete Galois
  modules, naturally in the sheaf `L` of `Λ`-modules
  (`Stacks.EtaleCohomology.galoisGlobalSectionsRestrictScalarsIntIso`). It is Galois-equivariant
  because the twist by `id × Spec σ` commutes with restriction of scalars
  (`Stacks.EtaleCohomology.selfMapTwist_restrictScalars`).
* **The chain model as Galois modules**: for an injective resolution `I` of `j_! F`,
  `Hᵐ(Γ^Gal(I)) ≅ Hᵐ(RΓ^Gal_c(X_k̄, F))` as Galois modules
  (`Stacks.EtaleCohomology.galoisCompactSupportResolutionGaloisIso`), with underlying map the
  identification `Hᵐ(Γ(X̄_k̄, I|)) ≅ Hᵐ_c(X_k̄, F)` of
  `Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`
  (`Stacks.EtaleCohomology.galoisCompactSupportResolutionGaloisIso_underlying`).
* **Vanishing above degree `2`**: `Q(Γ^Gal(K))` is `≤ 2`
  (`AlgebraicGeometry.isLE_galoisHomOpG_cyclotomic`), its cohomology being
  `res_ℤ Hᵐ(RΓ^Gal_c(X_k̄, ℱ_μ))` (`AlgebraicGeometry.galoisHomOpGCyclotomicDerivedIso`).
* **The trace as a map of discrete Galois modules**
  `H²(RΓ^Gal_c(X_k̄, ℱ_μ)) ⟶ ℚ/ℤ` (`AlgebraicGeometry.compactSupportCyclotomicTraceGaloisHom`),
  built from an invariant additive map (`Stacks.ContinuousCohomology.ratCircleHomMkOfForget`), and
  **on `H²(Γ^Gal(K))`** (`AlgebraicGeometry.galoisHomOpCyclotomicTrace`), with its formula on
  underlying groups through `AlgebraicGeometry.galoisHomOpCyclotomicUnderlyingIso` and
  `Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`
  (`AlgebraicGeometry.galoisHomOpCyclotomicTrace_apply`).

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology

universe u v w

/-! ### Roots of unity -/

namespace AlgebraicGeometry

section RootsOfUnity

variable (kbar : Type u) [Field kbar] (n : ℕ) [NeZero n]

/-- `μ_n(k̄) = μ_{#ℤ/n}(k̄)`: the identity, along `#ℤ/n = n`. -/
def rootsOfUnityCardZModAddEquiv :
    Additive (_root_.rootsOfUnity n kbar) ≃+
      Additive (_root_.rootsOfUnity (Fintype.card (ZMod n)) kbar) :=
  MulEquiv.toAdditive (MulEquiv.subgroupCongr (by rw [ZMod.card]))

/-- The underlying element of `k̄` is unchanged by `rootsOfUnityCardZModAddEquiv`. -/
@[simp]
lemma rootsOfUnityCardZModAddEquiv_coe (z : Additive (_root_.rootsOfUnity n kbar)) :
    (((rootsOfUnityCardZModAddEquiv kbar n z).toMul : kbarˣ) : kbar) = ((z.toMul : kbarˣ) : kbar) :=
  rfl

variable [IsAlgClosed kbar]

/-- `μ_n(k̄)` has `n` elements for `n` invertible in `k̄`. -/
theorem natCard_additive_rootsOfUnity (hn : IsUnit ((n : ℕ) : kbar)) :
    Nat.card (Additive (_root_.rootsOfUnity n kbar)) = n :=
  (exists_isPrimitiveRoot_of_isUnit hn).choose_spec.card_rootsOfUnity

omit [IsAlgClosed kbar] in
/-- `#ℤ/n = n` is invertible in `k̄`. -/
theorem isUnit_card_zmod (hn : IsUnit ((n : ℕ) : kbar)) :
    IsUnit ((Fintype.card (ZMod n) : ℕ) : kbar) := by
  rw [ZMod.card]
  exact hn

end RootsOfUnity

end AlgebraicGeometry

/-! ### Maps to `ℚ/ℤ` with the trivial action -/

namespace Stacks.ContinuousCohomology

section RatCircleHom

variable (Q : Type v) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]

/-- The `ℤ`-linear map `M ⟶ ℚ/ℤ` underlying an additive map `t : M →+ ℚ/ℤ`, for `M` the underlying
abelian group of a discrete `Q`-module (`ℚ/ℤ` lifted to the module universe). -/
def ratCircleHomMkHom (M : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q)
    (t : M.obj.obj.V →+ AddCircle (1 : ℚ)) :
    M.obj.obj.V ⟶ (trivialRatCircleULift.{v, w} Q).obj.obj.V :=
  (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).preimage (AddCommGrpCat.ofHom
    ((AddEquiv.ulift.{0, w} (α := AddCircle (1 : ℚ))).symm.toAddMonoidHom.comp t))

omit [CompactSpace Q] in
/-- `x ↦ t(x)`. -/
lemma ratCircleHomMkHom_apply (M : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q)
    (t : M.obj.obj.V →+ AddCircle (1 : ℚ)) (x : M.obj.obj.V) :
    (ratCircleHomMkHom.{v, w} Q M t).hom x = ULift.up (t x) := by
  have h : (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).map
      (ratCircleHomMkHom.{v, w} Q M t) = AddCommGrpCat.ofHom
        ((AddEquiv.ulift.{0, w} (α := AddCircle (1 : ℚ))).symm.toAddMonoidHom.comp t) := by
    unfold ratCircleHomMkHom
    exact Functor.map_preimage _ _
  exact ConcreteCategory.congr_hom h x

/-- **An invariant additive map to `ℚ/ℤ` is a map of discrete `Q`-modules** to `ℚ/ℤ` with the
trivial action: `t : M →+ ℚ/ℤ` with `t(g · x) = t(x)` for all `g ∈ Q`. -/
def ratCircleHomMk (M : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q)
    (t : M.obj.obj.V →+ AddCircle (1 : ℚ))
    (ht : ∀ (g : Q) (x : M.obj.obj.V), t ((M.obj.obj.ρ g).asHom.hom x) = t x) :
    M ⟶ trivialRatCircleULift.{v, w} Q :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ratCircleHomMkHom.{v, w} Q M t
      comm := fun g => ModuleCat.hom_ext (LinearMap.ext fun x => by
        change (ratCircleHomMkHom.{v, w} Q M t).hom ((M.obj.obj.ρ g).asHom.hom x) =
          ((trivialRatCircleULift.{v, w} Q).obj.obj.ρ g).asHom.hom
            ((ratCircleHomMkHom.{v, w} Q M t).hom x)
        rw [ratCircleHomMkHom_apply, ratCircleHomMkHom_apply, ht]
        rfl) })

omit [CompactSpace Q] in
/-- `x ↦ t(x)`. -/
lemma ratCircleHomMk_apply (M : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q)
    (t : M.obj.obj.V →+ AddCircle (1 : ℚ))
    (ht : ∀ (g : Q) (x : M.obj.obj.V), t ((M.obj.obj.ρ g).asHom.hom x) = t x) (x : M.obj.obj.V) :
    (ratCircleHomMk.{v, w} Q M t ht).hom.hom.hom.hom x = ULift.up (t x) :=
  ratCircleHomMkHom_apply.{v, w} Q M t x

/-- **A map to `ℚ/ℤ` out of a discrete `R`-`Q`-module after forgetting `R`**: given an `R`-linear
map `g : M ⟶ N` and `t : N →+ ℚ/ℤ` with `t(g(σ · x)) = t(g(x))`, the map `x ↦ t(g(x))` of
discrete `Q`-modules (`Stacks.ContinuousCohomology.ratCircleHomMk`). Taking `g` and `t` apart
lets the invariance be supplied exactly in the form it is proved. -/
def ratCircleHomMkOfForget {R : Type} [Ring R]
    (M : Stacks.Injectives.ContinuousModule.{0, v, w} R Q) (N : ModuleCat.{w} R)
    (g : (Stacks.Injectives.continuousModuleUnderlying.{0, v, w} R Q).obj M ⟶ N)
    (t : N →+ AddCircle (1 : ℚ))
    (ht : ∀ (σ : Q) (x : M.obj.obj.V), t (g ((M.obj.obj.ρ σ).asHom.hom x)) = t (g x)) :
    (continuousModuleForget.{0, v, w} R Q).obj M ⟶ trivialRatCircleULift.{v, w} Q :=
  ratCircleHomMk.{v, w} Q ((continuousModuleForget.{0, v, w} R Q).obj M)
    (t.comp (ConcreteCategory.hom g).toAddMonoidHom) (fun σ x => ht σ x)

omit [CompactSpace Q] in
/-- `x ↦ t(g(x))`. -/
lemma ratCircleHomMkOfForget_apply {R : Type} [Ring R]
    (M : Stacks.Injectives.ContinuousModule.{0, v, w} R Q) (N : ModuleCat.{w} R)
    (g : (Stacks.Injectives.continuousModuleUnderlying.{0, v, w} R Q).obj M ⟶ N)
    (t : N →+ AddCircle (1 : ℚ))
    (ht : ∀ (σ : Q) (x : M.obj.obj.V), t (g ((M.obj.obj.ρ σ).asHom.hom x)) = t (g x))
    (x : M.obj.obj.V) :
    (ratCircleHomMkOfForget.{v, w} Q M N g t ht).hom.hom.hom.hom x = ULift.up (t (g x)) :=
  ratCircleHomMk_apply.{v, w} Q ((continuousModuleForget.{0, v, w} R Q).obj M)
    (t.comp (ConcreteCategory.hom g).toAddMonoidHom) (fun σ x => ht σ x) x

end RatCircleHom

end Stacks.ContinuousCohomology

namespace AlgebraicGeometry

/-! ### The trace `H²_c(X_k̄, ℱ_μ) ⟶ ℚ/ℤ` -/

section CyclotomicTrace

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat
attribute [local instance 3000] Stacks.EtaleCohomology.etaleModules_enoughInjectives_galoisAction
  Stacks.EtaleCohomology.galoisModules_enoughInjectives_galoisAction

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]

/-- **`(ρ_μ)_N = μ_n`**: the image `N` of `π₁(X_k̄, η̄)` acts trivially on `μ_n(k̄)`
(`AlgebraicGeometry.cyclotomicContinuousModule_ρ_eq_one_of_mem_range`), so the quotient map
`μ_n ⟶ (ρ_μ)_N` is bijective; this is its inverse, `[z] ↦ z`. -/
def cyclotomicNormalCoinvariantsAddHom :
    letI := connectedSpace_of_isCurve B X f
    (geometricNormalCoinvariants B X f kbar (ZMod n) y
      (cyclotomicContinuousModule B X f kbar y n)).obj.obj.obj.V →+
        Additive (_root_.rootsOfUnity n kbar) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  Stacks.Trace.coinvariantsAddLift
    ((finiteTypeContinuousModuleRepresentation (ZMod n) _
      (cyclotomicContinuousModule B X f kbar y n)).comp
        (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)
    AddEquiv.ulift.toAddMonoidHom (fun g z => by
      have h := cyclotomicContinuousModule_ρ_eq_one_of_mem_range B X f kbar y n g.1 g.2
      change (((cyclotomicContinuousModule B X f kbar y n).obj.obj.obj.ρ g.1).asHom.hom z).down = z.down
      rw [h]
      rfl)

/-- `[z] ↦ z`. -/
lemma cyclotomicNormalCoinvariantsAddHom_mk
    (z : ULift.{u + 1} (Additive (_root_.rootsOfUnity n kbar))) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    cyclotomicNormalCoinvariantsAddHom B X f kbar y n
        (Stacks.Trace.coinvariantsMk ((finiteTypeContinuousModuleRepresentation (ZMod n) _
          (cyclotomicContinuousModule B X f kbar y n)).comp
            (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range.subtype)
          z) = z.down :=
  rfl

variable (j : CompactificationOf (Over.mk f))

/-- **The trace `tr : H²_c(X_k̄, ℱ_μ) ⟶ ℚ/ℤ`** at `ρ_μ = μ_n(k̄)`: Tag 03VK gives
`Ψ : H²_c(X_k̄, ℱ_μ) ≅ Hom(μ_n, (ρ_μ)_N)` (`AlgebraicGeometry.compactSupportCanonicalTwistEquiv`);
then `(ρ_μ)_N = μ_n` (`AlgebraicGeometry.cyclotomicNormalCoinvariantsAddHom`), an endomorphism of
the cyclic group `μ_n` is multiplication by a scalar `e ∈ ℤ/n`
(`Stacks.CharacterModule.cyclicEndScalar`), and `e ↦ e/n` embeds `ℤ/n` in `ℚ/ℤ`. No root of
unity is chosen. The formula is `AlgebraicGeometry.compactSupportCyclotomicTrace_apply`. -/
def compactSupportCyclotomicTrace (hn : IsUnit ((n : ℕ) : kbar)) :
    letI := connectedSpace_of_isCurve B X f
    galoisCompactSupportCohomologyGroup.{u, 0} (ZMod n) f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ (ZMod n)).obj
            (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ) →+ AddCircle (1 : ℚ) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  (Stacks.CharacterModule.zmodToRatCircle n).comp
    ((Stacks.CharacterModule.cyclicEndScalarHom (natCard_additive_rootsOfUnity kbar n hn)).comp
      ((AddMonoidHom.compHom (cyclotomicNormalCoinvariantsAddHom B X f kbar y n)).comp
        ((AddMonoidHom.compHom.flip (rootsOfUnityCardZModAddEquiv kbar n).toAddMonoidHom).comp
          (compactSupportCanonicalTwistEquiv B X f kbar (ZMod n) y j (isUnit_card_zmod kbar n hn)
            (cyclotomicContinuousModule B X f kbar y n)).toAddMonoidHom)))

/-- **The formula for the trace**: `tr(x) = e/n`, `e` the scalar of
`μ_n ≅ μ_{#ℤ/n} ⟶ (ρ_μ)_N = μ_n`, the middle map being `Ψ(x)`. -/
theorem compactSupportCyclotomicTrace_apply (hn : IsUnit ((n : ℕ) : kbar))
    (x : letI := connectedSpace_of_isCurve B X f
      galoisCompactSupportCohomologyGroup.{u, 0} (ZMod n) f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((representationSheaf B X _ (ZMod n)).obj
            (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)) :
    compactSupportCyclotomicTrace B X f kbar y n j hn x =
      Stacks.CharacterModule.zmodToRatCircle n
        (Stacks.CharacterModule.cyclicEndScalar (natCard_additive_rootsOfUnity kbar n hn)
          ((cyclotomicNormalCoinvariantsAddHom B X f kbar y n).comp
            ((compactSupportCanonicalTwistEquiv B X f kbar (ZMod n) y j
              (isUnit_card_zmod kbar n hn) (cyclotomicContinuousModule B X f kbar y n) x).comp
                (rootsOfUnityCardZModAddEquiv kbar n).toAddMonoidHom))) :=
  rfl

/-- `σ` acts on `(ρ_μ)_N = μ_n` as on `μ_n`. -/
theorem cyclotomicNormalCoinvariantsAddHom_galois (σ : kbar ≃ₐ[k] kbar)
    (c : letI := connectedSpace_of_isCurve B X f
      (geometricNormalCoinvariants B X f kbar (ZMod n) y
        (cyclotomicContinuousModule B X f kbar y n)).obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    cyclotomicNormalCoinvariantsAddHom B X f kbar y n
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar (ZMod n) y
          (cyclotomicContinuousModule B X f kbar y n) σ c) =
      Additive.ofMul (galoisRootsOfUnity k kbar n σ
        (cyclotomicNormalCoinvariantsAddHom B X f kbar y n c).toMul) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  obtain ⟨γ, rfl⟩ := exists_geometricQuotientGaloisEquiv_mk_eq B X f kbar y σ
  obtain ⟨z, rfl⟩ := Stacks.Trace.coinvariantsMk_surjective _ c
  exact congrArg (cyclotomicNormalCoinvariantsAddHom B X f kbar y n)
    (geometricNormalCoinvariantsGaloisRepresentation_mk B X f kbar (ZMod n) y
      (cyclotomicContinuousModule B X f kbar y n) γ _)

/-- The trace is invariant under conjugation of `Ψ(x)` by the Galois action. -/
theorem cyclicEndScalar_rootsOfUnityHomRepresentation (hn : IsUnit ((n : ℕ) : kbar))
    (σ : kbar ≃ₐ[k] kbar)
    (g : letI := connectedSpace_of_isCurve B X f
      Additive (_root_.rootsOfUnity (Fintype.card (ZMod n)) kbar) →+
        (geometricNormalCoinvariants B X f kbar (ZMod n) y
          (cyclotomicContinuousModule B X f kbar y n)).obj.obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    Stacks.CharacterModule.cyclicEndScalar (natCard_additive_rootsOfUnity kbar n hn)
        ((cyclotomicNormalCoinvariantsAddHom B X f kbar y n).comp
          ((rootsOfUnityHomRepresentation k kbar (Fintype.card (ZMod n)) (ZMod n)
            (geometricNormalCoinvariantsGaloisRepresentation B X f kbar (ZMod n) y
              (cyclotomicContinuousModule B X f kbar y n)) σ g).comp
                (rootsOfUnityCardZModAddEquiv kbar n).toAddMonoidHom)) =
      Stacks.CharacterModule.cyclicEndScalar (natCard_additive_rootsOfUnity kbar n hn)
        ((cyclotomicNormalCoinvariantsAddHom B X f kbar y n).comp
          (g.comp (rootsOfUnityCardZModAddEquiv kbar n).toAddMonoidHom)) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  let s : Additive (_root_.rootsOfUnity n kbar) →+ Additive (_root_.rootsOfUnity n kbar) :=
    (galoisRootsOfUnity k kbar n σ).toAdditive
  let s' : Additive (_root_.rootsOfUnity n kbar) →+ Additive (_root_.rootsOfUnity n kbar) :=
    (galoisRootsOfUnity k kbar n σ⁻¹).toAdditive
  have hss' : ∀ a, s (s' a) = a := fun a => by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    show σ (σ⁻¹ (((a.toMul : kbarˣ) : kbar))) = (((a.toMul : kbarˣ) : kbar))
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have key : (cyclotomicNormalCoinvariantsAddHom B X f kbar y n).comp
      ((rootsOfUnityHomRepresentation k kbar (Fintype.card (ZMod n)) (ZMod n)
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar (ZMod n) y
          (cyclotomicContinuousModule B X f kbar y n)) σ g).comp
            (rootsOfUnityCardZModAddEquiv kbar n).toAddMonoidHom) =
      s.comp (((cyclotomicNormalCoinvariantsAddHom B X f kbar y n).comp
        (g.comp (rootsOfUnityCardZModAddEquiv kbar n).toAddMonoidHom)).comp s') := by
    refine AddMonoidHom.ext fun a => ?_
    show cyclotomicNormalCoinvariantsAddHom B X f kbar y n
        (geometricNormalCoinvariantsGaloisRepresentation B X f kbar (ZMod n) y
          (cyclotomicContinuousModule B X f kbar y n) σ
          (g (Additive.ofMul (galoisRootsOfUnity k kbar (Fintype.card (ZMod n)) σ⁻¹
            (rootsOfUnityCardZModAddEquiv kbar n a).toMul)))) = _
    rw [cyclotomicNormalCoinvariantsAddHom_galois]
    rfl
  rw [key]
  exact Stacks.CharacterModule.cyclicEndScalar_conj _ _ s s' hss'

/-- **The trace is Galois-invariant**: on the Galois module `H²(RΓ^Gal_c(X_k̄, ℱ_μ))`, read in
`H²_c(X_k̄, ℱ_μ)` through `Stacks.EtaleCohomology.galoisCompactSupportGroupForgetIso`,
`tr(σ · x) = tr(x)`. By Tag 03VK, `Ψ(σ · x) = σ ∘ Ψ(x) ∘ σ⁻¹`, and the scalar of a conjugate
endomorphism of `μ_n` is the scalar. -/
theorem compactSupportCyclotomicTrace_galois (hn : IsUnit ((n : ℕ) : kbar)) (σ : kbar ≃ₐ[k] kbar)
    (x : letI := connectedSpace_of_isCurve B X f
      ((DerivedCategory.Plus.homologyFunctor (GaloisModules (ZMod n) k kbar) ((2 : ℕ) : ℤ)).obj
        (galoisDerivedCompactSupport (ZMod n) f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ (ZMod n)).obj
              (cyclotomicContinuousModule B X f kbar y n))))).obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    compactSupportCyclotomicTrace B X f kbar y n j hn
        ((galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ (ZMod n)).obj
              (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom
          ((((DerivedCategory.Plus.homologyFunctor (GaloisModules (ZMod n) k kbar)
            ((2 : ℕ) : ℤ)).obj (galoisDerivedCompactSupport (ZMod n) f j kbar
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                ((representationSheaf B X _ (ZMod n)).obj
                  (cyclotomicContinuousModule B X f kbar y n))))).obj.obj.ρ σ).asHom.hom x)) =
      compactSupportCyclotomicTrace B X f kbar y n j hn
        ((galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf B X _ (ZMod n)).obj
              (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom x) := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  have h := compactSupportCanonicalTwistEquiv_galoisCompactSupportGroupForgetIso B X f kbar (ZMod n)
    y j (isUnit_card_zmod kbar n hn) σ (cyclotomicContinuousModule B X f kbar y n) x
  rw [compactSupportCyclotomicTrace_apply, compactSupportCyclotomicTrace_apply, h,
    cyclicEndScalar_rootsOfUnityHomRepresentation B X f kbar y n hn]

/-- **The trace `H²(RΓ^Gal_c(X_k̄, ℱ_μ)) ⟶ ℚ/ℤ` as a morphism of discrete Galois modules**, after
forgetting the `ℤ/n`-module structure, `ℚ/ℤ` with the trivial action:
`AlgebraicGeometry.compactSupportCyclotomicTrace` read through
`Stacks.EtaleCohomology.galoisCompactSupportGroupForgetIso`, invariant by
`AlgebraicGeometry.compactSupportCyclotomicTrace_galois`.

The sheaf `ℱ_μ` is written `representationSheaf.{u, 0}` here so that its category instance is
spelled as in the statements of `AlgebraicGeometry.compactSupportCyclotomicTrace` and
`AlgebraicGeometry.compactSupportCyclotomicTrace_galois`; without the universe annotation the
instance is elaborated with the universe `max 1 (u + 2)` instead of `u + 2`, and comparing the two
spellings inside an applied map exhausts the recursion depth. -/
def compactSupportCyclotomicTraceGaloisHom [CompactSpace (kbar ≃ₐ[k] kbar)]
    (hn : IsUnit ((n : ℕ) : kbar)) :
    letI := connectedSpace_of_isCurve B X f
    (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)).obj
        ((DerivedCategory.Plus.homologyFunctor (GaloisModules (ZMod n) k kbar) ((2 : ℕ) : ℤ)).obj
          (galoisDerivedCompactSupport (ZMod n) f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((representationSheaf.{u, 0} B X _ (ZMod n)).obj
                (cyclotomicContinuousModule B X f kbar y n))))) ⟶
      Stacks.ContinuousCohomology.ratCircle.{u, u + 1} (kbar ≃ₐ[k] kbar) :=
  letI := connectedSpace_of_isCurve B X f
  Stacks.ContinuousCohomology.ratCircleHomMkOfForget.{u, u + 1} (kbar ≃ₐ[k] kbar)
    ((DerivedCategory.Plus.homologyFunctor (GaloisModules (ZMod n) k kbar) ((2 : ℕ) : ℤ)).obj
          (galoisDerivedCompactSupport (ZMod n) f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((representationSheaf.{u, 0} B X _ (ZMod n)).obj
                (cyclotomicContinuousModule B X f kbar y n))))) _
    (galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf.{u, 0} B X _ (ZMod n)).obj
              (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom
    (compactSupportCyclotomicTrace B X f kbar y n j hn)
    (by
      intro σ x
      have h := compactSupportCyclotomicTrace_galois B X f kbar y n j hn σ x
      rw [h])

/-- `x ↦ tr(x)`. -/
theorem compactSupportCyclotomicTraceGaloisHom_apply [CompactSpace (kbar ≃ₐ[k] kbar)]
    (hn : IsUnit ((n : ℕ) : kbar))
    (z : letI := connectedSpace_of_isCurve B X f
      ((DerivedCategory.Plus.homologyFunctor (GaloisModules (ZMod n) k kbar) ((2 : ℕ) : ℤ)).obj
          (galoisDerivedCompactSupport (ZMod n) f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((representationSheaf.{u, 0} B X _ (ZMod n)).obj
                (cyclotomicContinuousModule B X f kbar y n))))).obj.obj.V) :
    letI := connectedSpace_of_isCurve B X f
    (compactSupportCyclotomicTraceGaloisHom B X f kbar y n j hn).hom.hom.hom.hom z =
      ULift.up (compactSupportCyclotomicTrace B X f kbar y n j hn
        ((galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((representationSheaf.{u, 0} B X _ (ZMod n)).obj
              (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom z)) := by
  unfold compactSupportCyclotomicTraceGaloisHom
  rw [Stacks.ContinuousCohomology.ratCircleHomMkOfForget_apply]

end CyclotomicTrace

end AlgebraicGeometry

/-! ### Change of coefficients for `Γ^Gal` -/

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
attribute [local instance 3000] Stacks.EtaleCohomology.hasGlobalSectionsFunctor_galoisAction

section RestrictScalarsTwist

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ') {Y S : Scheme.{u}} (f : Y ⟶ S)
  (φ : Y ⟶ Y) (w : φ ≫ f = f)

/-- The adjoint form of the twist by an endomorphism over the base commutes with `res_ρ`. -/
theorem selfMapTwistAdj_restrictScalars (L : EtaleModules.{u, 0} Λ' S) :
    (etaleModuleRestrictScalars ρ S).map ((selfMapTwistAdj.{u, 0} Λ' f φ w).app L) =
      (selfMapTwistAdj.{u, 0} Λ f φ w).app ((etaleModuleRestrictScalars ρ S).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ f).map ((etaleModuleDirectImage.{u, 0} Λ φ).map
          (inverseImageRestrictScalarsApp ρ f L)) := by
  simp only [selfMapTwistAdj, selfMapDirectImageComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, Functor.map_comp]
  rw [restrictScalars_map_inverseImageAdj_unit ρ f L]
  have e3 := congrArg Iso.inv (restrictScalars_mapIso_directImageComp_app ρ φ f f w.symm
    ((etaleModuleInverseImage.{u, 0} Λ' f).obj L))
  simp only [Functor.mapIso_inv, Iso.app_inv] at e3
  rw [e3, Category.assoc]
  exact congrArg (_ ≫ ·) ((etaleModuleDirectImageComp.{u, 0} Λ φ f f w.symm).inv.naturality
    (inverseImageRestrictScalarsApp ρ f L))

/-- **The twist `f^{-1} ⟶ φ_* ∘ f^{-1}` by an endomorphism `φ` over the base commutes with
restriction of scalars**, along the comparison `f^{-1} ∘ res_ρ ⟶ res_ρ ∘ f^{-1}`. -/
theorem selfMapTwist_restrictScalars (L : EtaleModules.{u, 0} Λ' S) :
    (selfMapTwist.{u, 0} Λ f φ w).app ((etaleModuleRestrictScalars ρ S).obj L) ≫
        (etaleModuleDirectImage.{u, 0} Λ φ).map (inverseImageRestrictScalarsApp ρ f L) =
      inverseImageRestrictScalarsApp ρ f L ≫
        (etaleModuleRestrictScalars ρ Y).map ((selfMapTwist.{u, 0} Λ' f φ w).app L) := by
  have hT : ∀ (Λ₀ : Type) [Ring Λ₀] (M : EtaleModules.{u, 0} Λ₀ S),
      (etaleModuleInverseImageAdj.{u, 0} Λ₀ f).unit.app M ≫
        (etaleModuleDirectImage.{u, 0} Λ₀ f).map ((selfMapTwist.{u, 0} Λ₀ f φ w).app M) =
        (selfMapTwistAdj.{u, 0} Λ₀ f φ w).app M := by
    intro Λ₀ _ M
    rw [selfMapTwist_app]
    exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [Functor.map_comp, reassoc_of% (hT Λ ((etaleModuleRestrictScalars ρ S).obj L)),
    ← selfMapTwistAdj_restrictScalars ρ f φ w L, ← hT Λ' L, Functor.map_comp]
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  exact (congrArg (· ≫ _) (restrictScalars_map_inverseImageAdj_unit ρ f L)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((etaleModuleDirectImage.{u, 0} Λ f).map_comp (inverseImageRestrictScalarsApp ρ f L)
        ((etaleModuleRestrictScalars ρ Y).map ((selfMapTwist.{u, 0} Λ' f φ w).app L))).symm))

end RestrictScalarsTwist

section GlobalSectionsRestrictScalars

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ')

/-- `Γ(X, res_ρ M) = res_ρ Γ(X, M)` followed by restriction to `U` is `res_ρ` of restriction. -/
theorem etaleModuleGlobalSectionsRestrictScalars_hom_app_ΓRes {X : Scheme.{u}}
    (M : EtaleModules.{u, 0} Λ' X) (U : X.Etaleᵒᵖ) :
    (etaleModuleGlobalSectionsRestrictScalars ρ X).hom.app M ≫
        Sheaf.ΓRes ((etaleModuleRestrictScalars ρ X).obj M) U =
      (ModuleCat.restrictScalars.{u + 1} ρ).map (Sheaf.ΓRes M U) := by
  have h1 := Sheaf.ΓRes_map ((etaleModuleRestrictScalars ρ X).obj M)
    (terminal.from U.unop).op
  have h2 := Sheaf.ΓRes_map M (terminal.from U.unop).op
  have e := etaleModuleGlobalSectionsRestrictScalars_hom_app_comp_ΓNatIso ρ X M
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_general, Sheaf.ΓNatIsoSheafSections_hom_app_general] at e
  rw [← h1, ← h2, Functor.map_comp, ← e]
  rfl

/-- `Γ(Y, g_* M) ≅ Γ(X, M)` followed by restriction to the final object `g^{-1} Y` is
restriction of `g_* M` to `Y`. -/
theorem etaleModuleGlobalSectionsDirectImageIso_hom_app_ΓRes {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Λ₀ : Type) [Ring Λ₀] (M : EtaleModules.{u, 0} Λ₀ X) :
    (etaleModuleGlobalSectionsDirectImageIso.{u, 0} g Λ₀).hom.app M ≫
        Sheaf.ΓRes M (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale))) =
      Sheaf.ΓRes ((etaleModuleDirectImage.{u, 0} Λ₀ g).obj M) (op (⊤_ Y.Etale)) := by
  let hT1 : IsTerminal ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal
  let ΓY₁ := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ₀)
    (terminalIsTerminal (C := Y.Etale))
  let ΓX₁ := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ₀) hT1
  have cR : (etaleModuleGlobalSectionsDirectImageIso.{u, 0} g Λ₀).hom.app M ≫ ΓX₁.hom.app M =
      ΓY₁.hom.app ((etaleModuleDirectImage.{u, 0} Λ₀ g).obj M) := by
    show (ΓY₁.hom.app ((etaleModuleDirectImage.{u, 0} Λ₀ g).obj M) ≫ ΓX₁.inv.app M) ≫
      ΓX₁.hom.app M = _
    exact (Category.assoc _ _ _).trans ((congrArg _ (Iso.inv_hom_id_app ΓX₁ M)).trans
      (Category.comp_id _))
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_general] at cR
  exact cR.trans (Sheaf.ΓNatIsoSheafSections_hom_app_general _ _)

/-- **`Γ(Y, g_* -) ≅ Γ(X, -)` commutes with restriction of scalars.** -/
theorem etaleModuleGlobalSectionsDirectImageIso_restrictScalars {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : EtaleModules.{u, 0} Λ' X) :
    (ModuleCat.restrictScalars.{u + 1} ρ).map
        ((etaleModuleGlobalSectionsDirectImageIso.{u, 0} g Λ').hom.app M) ≫
        (etaleModuleGlobalSectionsRestrictScalars ρ X).hom.app M =
      (etaleModuleGlobalSectionsRestrictScalars ρ Y).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ' g).obj M) ≫
        (etaleModuleGlobalSectionsDirectImageIso.{u, 0} g Λ).hom.app
          ((etaleModuleRestrictScalars ρ X).obj M) := by
  let hT1 : IsTerminal ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal
  have hiso : IsIso (((etaleModuleRestrictScalars ρ X).obj M).ΓRes
      (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)))) := by
    rw [← Sheaf.ΓNatIsoSheafSections_hom_app_general hT1 ((etaleModuleRestrictScalars ρ X).obj M)]
    infer_instance
  have hmono : Mono (((etaleModuleRestrictScalars ρ X).obj M).ΓRes
      (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)))) :=
    @IsIso.mono_of_iso _ _ _ _ _ hiso
  refine (@cancel_mono _ _ _ _ _ _ hmono _ _).1 ?_
  have a1 := etaleModuleGlobalSectionsRestrictScalars_hom_app_ΓRes ρ M
    (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)))
  have a2 := etaleModuleGlobalSectionsDirectImageIso_hom_app_ΓRes g Λ' M
  have a3 := etaleModuleGlobalSectionsDirectImageIso_hom_app_ΓRes g Λ
    ((etaleModuleRestrictScalars ρ X).obj M)
  have a4 := etaleModuleGlobalSectionsRestrictScalars_hom_app_ΓRes ρ
    ((etaleModuleDirectImage.{u, 0} Λ' g).obj M) (op (⊤_ Y.Etale))
  exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) a1).trans
    (((ModuleCat.restrictScalars.{u + 1} ρ).map_comp _ _).symm.trans
      (congrArg (ModuleCat.restrictScalars.{u + 1} ρ).map a2)))).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) a3).trans a4)).symm

end GlobalSectionsRestrictScalars

section GaloisRestrictScalars

variable {Λ Λ' : Type} [Ring Λ] [Ring Λ'] (ρ : Λ →+* Λ') {k : Type u} [Field k]
  (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`Γ(Y_k̄, (res_ρ K)|_{Y_k̄}) ≅ res_ρ Γ(Y_k̄, K|_{Y_k̄})`**: `Γ(Y_k̄, -)` of the comparison
`(res_ρ K)|_{Y_k̄} ≅ res_ρ (K|_{Y_k̄})`, then `Γ(Y_k̄, res_ρ -) = res_ρ Γ(Y_k̄, -)`. -/
def fieldBaseChangeGlobalSectionsRestrictScalarsIso (K : EtaleModules.{u, 0} Λ' Y.left) :
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj
          ((etaleModuleRestrictScalars ρ Y.left).obj K)) ≅
      (ModuleCat.restrictScalars.{u + 1} ρ).obj
        ((etaleModuleGlobalSections.{u, 0} Λ' (fieldBaseChange Y kbar)).obj
          ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K)) :=
  (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).mapIso
      ((etaleModuleInverseImageRestrictScalars ρ (fieldBaseChangeProj Y kbar)).app K) ≪≫
    ((etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).app _).symm

/-- The forward map of `fieldBaseChangeGlobalSectionsRestrictScalarsIso` is the global sections of
the inverse-image comparison followed by the inverse of the global-sections comparison. -/
lemma fieldBaseChangeGlobalSectionsRestrictScalarsIso_hom (K : EtaleModules.{u, 0} Λ' Y.left) :
    (fieldBaseChangeGlobalSectionsRestrictScalarsIso ρ Y kbar K).hom =
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).map
          (inverseImageRestrictScalarsApp ρ (fieldBaseChangeProj Y kbar) K) ≫
        (etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).inv.app _ :=
  rfl

/-- The comparison is natural in `K`. -/
theorem fieldBaseChangeGlobalSectionsRestrictScalarsIso_hom_naturality
    {K K' : EtaleModules.{u, 0} Λ' Y.left} (v : K ⟶ K') :
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).map
          ((etaleModuleRestrictScalars ρ Y.left).map v)) ≫
        (fieldBaseChangeGlobalSectionsRestrictScalarsIso ρ Y kbar K').hom =
      (fieldBaseChangeGlobalSectionsRestrictScalarsIso ρ Y kbar K).hom ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).map
          ((etaleModuleGlobalSections.{u, 0} Λ' (fieldBaseChange Y kbar)).map
            ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).map v)) := by
  rw [fieldBaseChangeGlobalSectionsRestrictScalarsIso_hom,
    fieldBaseChangeGlobalSectionsRestrictScalarsIso_hom, ← Functor.map_comp_assoc,
    Category.assoc]
  have h1 :=
    (inverseImageRestrictScalarsTwoSquare ρ (fieldBaseChangeProj Y kbar)).natTrans.naturality v
  have h2 := (etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).inv.naturality
    ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).map v)
  simp only [Functor.comp_map] at h1 h2
  rw [← h2]
  exact (congrArg (fun t => (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).map t ≫ _)
    h1).trans (by rw [Functor.map_comp, Category.assoc])

/-- **The comparison is Galois-equivariant**: the action of `σ` through `id_Y × Spec σ` commutes
with restriction of scalars. -/
theorem fieldBaseChangeGlobalSectionsGaloisAction_restrictScalars (σ : kbar ≃ₐ[k] kbar)
    (K : EtaleModules.{u, 0} Λ' Y.left) :
    fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y kbar σ
        ((etaleModuleRestrictScalars ρ Y.left).obj K) ≫
        (fieldBaseChangeGlobalSectionsRestrictScalarsIso ρ Y kbar K).hom =
      (fieldBaseChangeGlobalSectionsRestrictScalarsIso ρ Y kbar K).hom ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).map
          (fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ' Y kbar σ K) := by
  have hT := selfMapTwist_restrictScalars ρ (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
    (galoisBaseChange_comp_fst Y kbar σ) K
  have hD :=
    (etaleModuleGlobalSectionsDirectImageIso.{u, 0} (galoisBaseChange Y kbar σ) Λ).hom.naturality
      (inverseImageRestrictScalarsApp ρ (fieldBaseChangeProj Y kbar) K)
  have hR := etaleModuleGlobalSectionsDirectImageIso_restrictScalars ρ (galoisBaseChange Y kbar σ)
    ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K)
  have hN := (etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).inv.naturality
    ((selfMapTwist.{u, 0} Λ' (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
      (galoisBaseChange_comp_fst Y kbar σ)).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hD hN
  have hR' : (etaleModuleGlobalSectionsDirectImageIso.{u, 0} (galoisBaseChange Y kbar σ) Λ).hom.app
        ((etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).obj
          ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K)) ≫
        ((etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).app
          ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K)).inv =
      ((etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).app
          ((etaleModuleDirectImage.{u, 0} Λ' (galoisBaseChange Y kbar σ)).obj
            ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K))).inv ≫
        (ModuleCat.restrictScalars.{u + 1} ρ).map
          ((etaleModuleGlobalSectionsDirectImageIso.{u, 0} (galoisBaseChange Y kbar σ) Λ').hom.app
            ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K)) :=
    (Iso.comp_inv_eq _).2 (((Iso.eq_inv_comp _).2 hR.symm).trans (Category.assoc _ _ _).symm)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)
  let Γ' := etaleModuleGlobalSections.{u, 0} Λ' (fieldBaseChange Y kbar)
  let R := ModuleCat.restrictScalars.{u + 1} ρ
  let tw := (selfMapTwist.{u, 0} Λ (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
    (galoisBaseChange_comp_fst Y kbar σ)).app ((etaleModuleRestrictScalars ρ Y.left).obj K)
  let tw' := (selfMapTwist.{u, 0} Λ' (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
    (galoisBaseChange_comp_fst Y kbar σ)).app K
  let c := inverseImageRestrictScalarsApp ρ (fieldBaseChangeProj Y kbar) K
  let D := (etaleModuleGlobalSectionsDirectImageIso.{u, 0} (galoisBaseChange Y kbar σ) Λ).hom.app
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj
      ((etaleModuleRestrictScalars ρ Y.left).obj K))
  let D₂ := (etaleModuleGlobalSectionsDirectImageIso.{u, 0} (galoisBaseChange Y kbar σ) Λ).hom.app
    ((etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).obj
      ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K))
  let D' := (etaleModuleGlobalSectionsDirectImageIso.{u, 0} (galoisBaseChange Y kbar σ) Λ').hom.app
    ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K)
  let Gi := ((etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).app
    ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K)).inv
  let Gi₂ := ((etaleModuleGlobalSectionsRestrictScalars ρ (fieldBaseChange Y kbar)).app
    ((etaleModuleDirectImage.{u, 0} Λ' (galoisBaseChange Y kbar σ)).obj
      ((etaleModuleInverseImage.{u, 0} Λ' (fieldBaseChangeProj Y kbar)).obj K))).inv
  have hD' : Γ.map ((etaleModuleDirectImage.{u, 0} Λ (galoisBaseChange Y kbar σ)).map c) ≫ D₂ =
      D ≫ Γ.map c := hD
  have hN' : Γ.map ((etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).map
      tw') ≫ Gi₂ =
      Gi ≫ R.map (Γ'.map tw') :=
    hN
  have hT' : tw ≫ (etaleModuleDirectImage.{u, 0} Λ (galoisBaseChange Y kbar σ)).map c =
      c ≫ (etaleModuleRestrictScalars ρ (fieldBaseChange Y kbar)).map
        tw' := hT
  have hR'' : D₂ ≫ Gi = Gi₂ ≫ R.map D' := hR'
  show (Γ.map tw ≫ D) ≫ (Γ.map c ≫ Gi) = (Γ.map c ≫ Gi) ≫ R.map (Γ'.map tw' ≫ D')
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% hD'.symm, ← Γ.map_comp_assoc, hT', hR'']
  erw [Functor.map_comp, Category.assoc, reassoc_of% hN']

end GaloisRestrictScalars

section GaloisModulesRestrictScalars

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

/-- **`Γ^Gal_ℤ(res_ℤ K) ≅ res_ℤ Γ^Gal_Λ(K)` as discrete Galois modules**, naturally in the sheaf
`K` of `Λ`-modules: the comparison
`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsRestrictScalarsIso` is Galois-equivariant
(`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction_restrictScalars`). -/
def galoisGlobalSectionsRestrictScalarsIntIso :
    etaleModuleRestrictScalars (Int.castRingHom Λ) Y.left ⋙ galoisGlobalSections ℤ Y kbar ≅
      galoisGlobalSections Λ Y kbar ⋙
        Stacks.ContinuousCohomology.continuousModuleForget Λ (kbar ≃ₐ[k] kbar) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Action.mkIso
      (fieldBaseChangeGlobalSectionsRestrictScalarsIso (Int.castRingHom Λ) Y kbar K)
      (fun σ => fieldBaseChangeGlobalSectionsGaloisAction_restrictScalars (Int.castRingHom Λ) Y
        kbar σ K))))
    (fun v => ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Action.hom_ext _ _
      (fieldBaseChangeGlobalSectionsRestrictScalarsIso_hom_naturality (Int.castRingHom Λ) Y
        kbar v))))

/-- The underlying map of `Stacks.EtaleCohomology.galoisGlobalSectionsRestrictScalarsIntIso`. -/
lemma galoisGlobalSectionsRestrictScalarsIntIso_hom_app_hom (K : EtaleModules.{u, 0} Λ Y.left) :
    ((galoisGlobalSectionsRestrictScalarsIntIso Λ Y kbar).hom.app K).hom.hom.hom =
      (fieldBaseChangeGlobalSectionsRestrictScalarsIso (Int.castRingHom Λ) Y kbar K).hom :=
  rfl

end GaloisModulesRestrictScalars

/-! ### `H^m(Γ^Gal(I)) ≅ H^m(RΓ^Gal_c(X_k̄, F))` for an injective resolution `I` of `j_! F` -/

section ExactHomology

attribute [local instance] HasDerivedCategory.standard

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] (T : A ⥤ B)
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- **An exact functor commutes with cohomology**, `T(Hᵐ(K)) ≅ Hᵐ(T K)` for a bounded below
complex `K`, read through the derived categories: `Hᵐ` of `Q(K)`, the comparison
`Stacks.DerivedFunctor.derivedHomologyIso`, and `Q ⋙ T⁺ ≅ T ⋙ Q`
(`CategoryTheory.Functor.mapDerivedCategoryPlusQIso`). This is the form in which the derived
comparisons of the Galois actions are stated. -/
def exactFunctorPlusHomologyIso (K : CochainComplex.Plus A) (m : ℤ) :
    T.obj (K.obj.homology m) ≅ ((T.mapHomologicalComplex _).obj K.obj).homology m :=
  T.mapIso ((DerivedCategory.homologyFunctorFactors A m).app K.obj).symm ≪≫
    ((Stacks.DerivedFunctor.derivedHomologyIso T m).app (DerivedCategory.Q.obj K.obj)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor B m).mapIso ((T.mapDerivedCategoryPlusQIso).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors B m).app ((T.mapHomologicalComplex _).obj K.obj)

end ExactHomology

section ResolutionGalois

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat
attribute [local instance 3000] Stacks.EtaleCohomology.etaleModules_enoughInjectives_galoisAction
  Stacks.EtaleCohomology.galoisModules_enoughInjectives_galoisAction

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

variable {Λ f j} in
/-- The augmentation `j_! F[0] ⟶ I` of an injective resolution of `j_! F`, as a morphism of
bounded below complexes. -/
def compactSupportResolutionMap (F : EtaleModules Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero Λ j.immersion).obj F))) :
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ⟶ I.cocomplexPlus :=
  (mapCochainComplexPlusSinglePlusIso (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) F).hom ≫
    ObjectProperty.homMk I.ι

/-- The image of `compactSupportResolutionMap F I` in the bounded below derived category is an
isomorphism. -/
instance isIso_Q_map_compactSupportResolutionMap (F : EtaleModules Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero Λ j.immersion).obj F))) :
    IsIso (DerivedCategory.Plus.Q.map (compactSupportResolutionMap F I)) := by
  have : QuasiIso (compactSupportResolutionMap F I).hom := by
    change QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) (ComplexShape.up ℤ) 0).hom.app F ≫ I.ι)
    infer_instance
  have : IsIso (DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (compactSupportResolutionMap F I))) :=
    inferInstanceAs (IsIso (DerivedCategory.Q.map (compactSupportResolutionMap F I).hom))
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

/-- **`Hᵐ(Γ^Gal(I)) ≅ Hᵐ(RΓ^Gal_c(X_k̄, F))` as Galois modules** for an injective resolution `I`
of `j_! F` on `X̄`: `I` is a bounded below complex of injectives, so `Γ^Gal(I)` computes
`RΓ^Gal(X̄_k̄, j_! F)`. Its underlying map is
`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`
(`Stacks.EtaleCohomology.galoisCompactSupportResolutionGaloisIso_underlying`). -/
def galoisCompactSupportResolutionGaloisIso (F : EtaleModules Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero Λ j.immersion).obj F))) (m : ℤ) :
    (((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapHomologicalComplex _).obj
        I.cocomplex).homology m ≅
      (DerivedCategory.Plus.homologyFunctor (GaloisModules Λ k kbar) m).obj
        (galoisDerivedCompactSupport Λ f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F)) :=
  haveI := isIso_Q_map_compactSupportResolutionMap Λ f j F I
  (galoisGlobalSections Λ (Over.mk j.toBase) kbar).homologyIsoRightDerivedFunctorPlusOfRightAcyclic
      I.cocomplexPlus (fun n => (galoisGlobalSections Λ (Over.mk j.toBase)
        kbar).rightAcyclic_of_injective (I.cocomplex.X n)) m ≪≫
    (DerivedCategory.Plus.homologyFunctor _ m).mapIso
      ((galoisGlobalSections Λ (Over.mk j.toBase) kbar).rightDerivedFunctorPlus.mapIso
        (asIso (DerivedCategory.Plus.Q.map (compactSupportResolutionMap F I)))).symm

omit [Algebra.IsSeparable k kbar] in
/-- The comparison of `RΓ^Gal_c(X_k̄, K)` with `RΓ_c(X_k̄, K)`, componentwise. -/
lemma galoisCompactSupportForgetIso_hom_eq (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    [Algebra.IsSeparable k kbar] :
    (galoisCompactSupportForgetIso Λ f j kbar K).hom =
      (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk j.toBase) kbar).hom.app
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)) ≫
        (etaleModuleGlobalSections.{u, 0} Λ
            (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusQIso (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar))).hom.app
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)) := by
  simp only [galoisCompactSupportForgetIso, galoisCompactSupportForgetNatIso, Iso.app_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Iso.symm_hom, Category.id_comp, Category.comp_id]

set_option maxHeartbeats 1000000 in
/-- **The underlying map of `Hᵐ(Γ^Gal(I)) ≅ Hᵐ(RΓ^Gal_c(X_k̄, F))` is
`Hᵐ(Γ(X̄_k̄, I|)) ≅ Hᵐ_c(X_k̄, F)`** (`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`),
read through `U(Hᵐ(-)) ≅ Hᵐ(U -)` and `Stacks.EtaleCohomology.galoisCompactSupportGroupForgetIso`.
The input is the comparison of the units of `RΓ^Gal` and of `RΓ(X̄_k̄, -|)`
(`Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso_fac`). -/
theorem galoisCompactSupportResolutionGaloisIso_underlying (F : EtaleModules Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero Λ j.immersion).obj F))) (m : ℤ) :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)).map
        (galoisCompactSupportResolutionGaloisIso Λ f j kbar F I m).hom ≫
      (galoisCompactSupportGroupForgetIso Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) m).hom =
    (exactFunctorPlusHomologyIso
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar))
        ((galoisGlobalSections Λ (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          I.cocomplexPlus) m).hom ≫
      (galoisCompactSupportResolutionIso (f := f) kbar F I m).hom := by
  have := isIso_Q_map_compactSupportResolutionMap Λ f j F I
  let U := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)
  let Γg := galoisGlobalSections Λ (Over.mk j.toBase) kbar
  let res := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar)
  let C := I.cocomplexPlus
  let J := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F)
  let ι' := compactSupportResolutionMap F I
  have : IsIso (DerivedCategory.Plus.Q.map (res.mapCochainComplexPlus.map ι')) :=
    isIso_Q_map_compactSupportResolutionRestrictionMap (kbar := kbar) F I
  -- (1) the inverse of `Q(ι')` against `Q ⋙ res⁺ ≅ res ⋙ Q`
  have hq : (res.mapDerivedCategoryPlusQIso).inv.app C ≫
      res.mapDerivedCategoryPlus.map (inv (DerivedCategory.Plus.Q.map ι')) ≫
        (res.mapDerivedCategoryPlusQIso).hom.app J =
      inv (DerivedCategory.Plus.Q.map (res.mapCochainComplexPlus.map ι')) := by
    apply IsIso.eq_inv_of_hom_inv_id
    have hn := (res.mapDerivedCategoryPlusQIso).inv.naturality ι'
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  -- (2) naturality of `RΓ^Gal ⋙ U ≅ res⁺ ⋙ RΓ` and the comparison of units
  have hfg := (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk j.toBase) kbar).hom.naturality
    (inv (DerivedCategory.Plus.Q.map ι'))
  simp only [Functor.comp_map] at hfg
  have hfac := galoisDerivedGlobalSectionsForgetIso_fac Λ (Over.mk j.toBase) kbar C
  -- (3) the derived equation (★)
  have hstar : U.mapDerivedCategoryPlus.map (Γg.mapCochainComplexPlusDerivedUnit.app C) ≫
      U.mapDerivedCategoryPlus.map (Γg.rightDerivedFunctorPlus.map
        (inv (DerivedCategory.Plus.Q.map ι'))) ≫
      (galoisCompactSupportForgetIso Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F)).hom =
      (U.mapDerivedCategoryPlusQIso).hom.app (Γg.mapCochainComplexPlus.obj C) ≫
        Γ.mapCochainComplexPlusDerivedUnit.app (res.mapCochainComplexPlus.obj C) ≫
        Γ.rightDerivedFunctorPlus.map
          (inv (DerivedCategory.Plus.Q.map (res.mapCochainComplexPlus.map ι'))) := by
    rw [galoisCompactSupportForgetIso_hom_eq]
    let a := U.mapDerivedCategoryPlus.map (Γg.mapCochainComplexPlusDerivedUnit.app C)
    let b := U.mapDerivedCategoryPlus.map (Γg.rightDerivedFunctorPlus.map
      (inv (DerivedCategory.Plus.Q.map ι')))
    let c := (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk j.toBase) kbar).hom.app
      (DerivedCategory.Plus.Q.obj J)
    let c' := (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk j.toBase) kbar).hom.app
      (DerivedCategory.Plus.Q.obj C)
    let d := Γ.rightDerivedFunctorPlus.map ((res.mapDerivedCategoryPlusQIso).hom.app J)
    let e := Γ.rightDerivedFunctorPlus.map
      (res.mapDerivedCategoryPlus.map (inv (DerivedCategory.Plus.Q.map ι')))
    let mi := Γ.rightDerivedFunctorPlus.map ((res.mapDerivedCategoryPlusQIso).inv.app C)
    let mU := (U.mapDerivedCategoryPlusQIso).hom.app (Γg.mapCochainComplexPlus.obj C)
    let uΓ := Γ.mapCochainComplexPlusDerivedUnit.app (res.mapCochainComplexPlus.obj C)
    have e1 : b ≫ c = c' ≫ e := hfg
    have e2 : a ≫ c' = mU ≫ uΓ ≫ mi := hfac
    have e3 : mi ≫ e ≫ d = Γ.rightDerivedFunctorPlus.map
        (inv (DerivedCategory.Plus.Q.map (res.mapCochainComplexPlus.map ι'))) := by
      rw [← hq, Functor.map_comp, Functor.map_comp]
    show a ≫ b ≫ c ≫ d = mU ≫ uΓ ≫ _
    calc a ≫ b ≫ c ≫ d = a ≫ (b ≫ c) ≫ d := congrArg (a ≫ ·) (Category.assoc b c d).symm
      _ = a ≫ (c' ≫ e) ≫ d := congrArg (fun t => a ≫ t ≫ d) e1
      _ = (a ≫ c') ≫ e ≫ d :=
          (congrArg (a ≫ ·) (Category.assoc c' e d)).trans (Category.assoc a c' (e ≫ d)).symm
      _ = (mU ≫ uΓ ≫ mi) ≫ e ≫ d := congrArg (· ≫ e ≫ d) e2
      _ = mU ≫ uΓ ≫ (mi ≫ e ≫ d) :=
          (Category.assoc _ _ _).trans (congrArg (mU ≫ ·) (Category.assoc _ _ _))
      _ = _ := congrArg (fun t => mU ≫ uΓ ≫ t) e3
  -- (4) assemble on homology
  have hdhi := (Stacks.DerivedFunctor.derivedHomologyIso U m).inv.naturality
    (DerivedCategory.Plus.ι.map (Γg.mapCochainComplexPlusDerivedUnit.app C ≫
      Γg.rightDerivedFunctorPlus.map (inv (DerivedCategory.Plus.Q.map ι'))))
  simp only [Functor.comp_map] at hdhi
  have hH := congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) m).map hstar
  simp only [Functor.map_comp] at hH
  let PH := DerivedCategory.Plus.homologyFunctor (GaloisModules Λ k kbar) m
  let PHM := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) m
  let fG := (DerivedCategory.homologyFunctorFactors (GaloisModules Λ k kbar) m).app
    ((Γg.mapHomologicalComplex _).obj C.obj)
  let uG := Γg.mapCochainComplexPlusDerivedUnit.app C
  let φ := inv (DerivedCategory.Plus.Q.map ι')
  let M := galoisDerivedCompactSupport Λ f j kbar
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0).obj F)
  let dHI := Stacks.DerivedFunctor.derivedHomologyIso U m
  let gc := (galoisCompactSupportForgetIso Λ f j kbar
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ X) 0).obj F)).hom
  let mU := (U.mapDerivedCategoryPlusQIso).hom.app (Γg.mapCochainComplexPlus.obj C)
  let fU := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ) m).app
    ((U.mapHomologicalComplex _).obj (Γg.mapCochainComplexPlus.obj C).obj)
  let uΓ := Γ.mapCochainComplexPlusDerivedUnit.app (res.mapCochainComplexPlus.obj C)
  let rr := Γ.rightDerivedFunctorPlus.map
    (inv (DerivedCategory.Plus.Q.map (res.mapCochainComplexPlus.map ι')))
  have hdhi' : U.map (PH.map (uG ≫ Γg.rightDerivedFunctorPlus.map φ)) ≫
      dHI.inv.app (DerivedCategory.Plus.ι.obj M) =
      dHI.inv.app (DerivedCategory.Q.obj (Γg.mapCochainComplexPlus.obj C).obj) ≫
        PHM.map (U.mapDerivedCategoryPlus.map (uG ≫ Γg.rightDerivedFunctorPlus.map φ)) := hdhi
  have hH' : PHM.map (U.mapDerivedCategoryPlus.map (uG ≫ Γg.rightDerivedFunctorPlus.map φ)) ≫
      PHM.map gc = PHM.map mU ≫ PHM.map uΓ ≫ PHM.map rr :=
    (congrArg (· ≫ PHM.map gc) ((congrArg PHM.map (U.mapDerivedCategoryPlus.map_comp uG
      (Γg.rightDerivedFunctorPlus.map φ))).trans (PHM.map_comp _ _))).trans
      ((Category.assoc _ _ _).trans (hH.trans (congrArg (PHM.map mU ≫ ·) (PHM.map_comp uΓ rr))))
  show U.map (fG.inv ≫ PH.map uG ≫ PH.map (Γg.rightDerivedFunctorPlus.map φ)) ≫
      dHI.inv.app (DerivedCategory.Plus.ι.obj M) ≫ PHM.map gc =
    (U.map fG.inv ≫ dHI.inv.app (DerivedCategory.Q.obj (Γg.mapCochainComplexPlus.obj C).obj) ≫
      PHM.map mU ≫ fU.hom) ≫ (fU.inv ≫ PHM.map uΓ) ≫ PHM.map rr
  have hmid : U.map (PH.map uG ≫ PH.map (Γg.rightDerivedFunctorPlus.map φ)) ≫
      dHI.inv.app (DerivedCategory.Plus.ι.obj M) ≫ PHM.map gc =
      dHI.inv.app (DerivedCategory.Q.obj (Γg.mapCochainComplexPlus.obj C).obj) ≫
        PHM.map mU ≫ PHM.map uΓ ≫ PHM.map rr := by
    rw [← PH.map_comp]
    exact (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ PHM.map gc) hdhi').trans
      (Category.assoc _ _ _)).trans (congrArg (_ ≫ ·) hH'))
  have r1 : fU.hom ≫ (fU.inv ≫ PHM.map uΓ) ≫ PHM.map rr = PHM.map uΓ ≫ PHM.map rr :=
    (congrArg (fU.hom ≫ ·) (Category.assoc _ _ _)).trans (Iso.hom_inv_id_assoc fU _)
  have hR : (U.map fG.inv ≫
      dHI.inv.app (DerivedCategory.Q.obj (Γg.mapCochainComplexPlus.obj C).obj) ≫
      PHM.map mU ≫ fU.hom) ≫ (fU.inv ≫ PHM.map uΓ) ≫ PHM.map rr =
      U.map fG.inv ≫ dHI.inv.app (DerivedCategory.Q.obj (Γg.mapCochainComplexPlus.obj C).obj) ≫
        PHM.map mU ≫ PHM.map uΓ ≫ PHM.map rr :=
    (Category.assoc _ _ _).trans (congrArg (U.map fG.inv ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (PHM.map mU ≫ ·) r1)))))
  rw [hR, U.map_comp, Category.assoc]
  exact congrArg (U.map fG.inv ≫ ·) hmid

end ResolutionGalois

end Stacks.EtaleCohomology

/-! ### The trace on `H²(Γ^Gal(K))` for an injective resolution `K` of `j_! ℱ_μ` -/

namespace AlgebraicGeometry

section GaloisTrace

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat
attribute [local instance 3000] Stacks.EtaleCohomology.etaleModules_enoughInjectives_galoisAction
  Stacks.EtaleCohomology.galoisModules_enoughInjectives_galoisAction

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))))

/-- `K = res_ℤ K₀`: the injective resolution `K₀` of `j_! ℱ_μ` as a complex of abelian sheaves. -/
abbrev cyclotomicIntResolution :
    CochainComplex (EtaleModules.{u, 0} ℤ (Over.mk j.toBase).left) ℤ :=
  ((etaleModuleRestrictScalars (Int.castRingHom (ZMod n))
    (Over.mk j.toBase).left).mapHomologicalComplex _).obj K₀.cocomplex

/-- **`Γ^Gal_ℤ(res_ℤ K₀) = res_ℤ Γ^Gal_{ℤ/n}(K₀)`** as complexes of discrete Galois modules
(`Stacks.EtaleCohomology.galoisGlobalSectionsRestrictScalarsIntIso`, degreewise). -/
def galoisHomOpGCyclotomicIso :
    Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
        (cyclotomicIntResolution B X f kbar y n j K₀) ≅
      ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
        (kbar ≃ₐ[k] kbar)).mapHomologicalComplex _).obj
          (((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapHomologicalComplex
            _).obj K₀.cocomplex) :=
  haveI : (galoisGlobalSections ℤ (Over.mk j.toBase) kbar).Additive :=
    Stacks.EtaleCohomology.galoisGlobalSections_additive ℤ (Over.mk j.toBase) kbar
  haveI : (etaleModuleRestrictScalars (Int.castRingHom (ZMod n))
      (Over.mk j.toBase).left).Additive :=
    inferInstance
  haveI : (etaleModuleRestrictScalars (Int.castRingHom (ZMod n)) (Over.mk j.toBase).left ⋙
      galoisGlobalSections ℤ (Over.mk j.toBase) kbar).Additive := inferInstance
  haveI : (galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar ⋙
      Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)).Additive :=
    inferInstance
  (NatIso.mapHomologicalComplex
    (galoisGlobalSectionsRestrictScalarsIntIso (ZMod n) (Over.mk j.toBase) kbar) _).app K₀.cocomplex

/-- **`Hᵐ(Γ^Gal_ℤ(res_ℤ K₀)) = res_ℤ Hᵐ(Γ^Gal_{ℤ/n}(K₀))`** as discrete Galois modules. -/
def galoisHomOpGCyclotomicHomologyIso (m : ℤ) :
    (DerivedCategory.homologyFunctor (GaloisModules ℤ k kbar) m).obj
        (DerivedCategory.Q.obj (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
          (cyclotomicIntResolution B X f kbar y n j K₀))) ≅
      (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)).obj
        ((((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapHomologicalComplex
          _).obj K₀.cocomplex).homology m) :=
  (DerivedCategory.homologyFunctorFactors _ m).app _ ≪≫
    (HomologicalComplex.homologyFunctor _ _ m).mapIso
      (galoisHomOpGCyclotomicIso B X f kbar y n j K₀) ≪≫
    (Stacks.EtaleCohomology.exactFunctorPlusHomologyIso
      (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar))
      ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
        K₀.cocomplexPlus) m).symm

/-- **`Hᵐ(Γ^Gal_ℤ(res_ℤ K₀)) = res_ℤ Hᵐ(RΓ^Gal_c(X_k̄, ℱ_μ))`** as discrete Galois modules. -/
def galoisHomOpGCyclotomicDerivedIso (m : ℤ) :
    (DerivedCategory.homologyFunctor (GaloisModules ℤ k kbar) m).obj
        (DerivedCategory.Q.obj (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
          (cyclotomicIntResolution B X f kbar y n j K₀))) ≅
      letI := connectedSpace_of_isCurve B X f
      (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)).obj
        ((DerivedCategory.Plus.homologyFunctor (GaloisModules (ZMod n) k kbar) m).obj
          (galoisDerivedCompactSupport (ZMod n) f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((representationSheaf B X _ (ZMod n)).obj
                (cyclotomicContinuousModule B X f kbar y n))))) :=
  letI := connectedSpace_of_isCurve B X f
  galoisHomOpGCyclotomicHomologyIso B X f kbar y n j K₀ m ≪≫
    (Stacks.ContinuousCohomology.continuousModuleForget (ZMod n) (kbar ≃ₐ[k] kbar)).mapIso
      (galoisCompactSupportResolutionGaloisIso (ZMod n) f j kbar _ K₀ m)

/-- **`Γ^Gal(res_ℤ K₀)` has no cohomology above degree `2`**: its cohomology is that of
`RΓ^Gal_c(X_k̄, ℱ_μ)` (`AlgebraicGeometry.galoisHomOpGCyclotomicDerivedIso`), and `Hᵐ_c` of a
curve vanishes for `m > 2`
(`Stacks.EtaleCohomology.isZero_galoisCompactSupportCohomologyGroup_of_two_lt`). -/
instance isLE_galoisHomOpG_cyclotomic :
    (DerivedCategory.Q.obj (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
      (cyclotomicIntResolution B X f kbar y n j K₀))).IsLE 2 := by
  let := connectedSpace_of_isCurve B X f
  rw [DerivedCategory.isLE_iff]
  intro i hi
  refine IsZero.of_iso ?_ (galoisHomOpGCyclotomicDerivedIso B X f kbar y n j K₀ i)
  apply Functor.map_isZero
  let U := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar)
  have : U.Faithful :=
    ⟨fun h => ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (Action.hom_ext _ _ h))⟩
  have hU := (isZero_galoisCompactSupportCohomologyGroup_of_two_lt f j kbar (ZMod n)
    ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)) i
      hi).of_iso (galoisCompactSupportGroupForgetIso (ZMod n) f j kbar _ i)
  rw [IsZero.iff_id_eq_zero]
  apply U.map_injective
  rw [U.map_id, U.map_zero]
  exact hU.eq_of_src _ _

/-- **The identification `H²(Γ^Gal_ℤ(res_ℤ K₀)) = res_ℤ H²(Γ(X̄_k̄, K₀|_{X̄_k̄}))` of underlying
groups**: the coefficient change `Γ^Gal_ℤ(res_ℤ K₀) = res_ℤ Γ^Gal_{ℤ/n}(K₀)`, then forgetting the
Galois action (`Stacks.EtaleCohomology.exactFunctorPlusHomologyIso`). -/
def galoisHomOpCyclotomicUnderlyingIso :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).obj
        ((DerivedCategory.homologyFunctor (GaloisModules ℤ k kbar) 2).obj
          (DerivedCategory.Q.obj (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
            (cyclotomicIntResolution B X f kbar y n j K₀)))) ≅
      (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod n))).obj
        ((((etaleModuleGlobalSections.{u, 0} (ZMod n)
          (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
            (((etaleModuleInverseImage.{u, 0} (ZMod n)
              (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
                K₀.cocomplex)).homology ((2 : ℕ) : ℤ)) :=
  (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} ℤ (kbar ≃ₐ[k] kbar)).mapIso
      (galoisHomOpGCyclotomicHomologyIso B X f kbar y n j K₀ ((2 : ℕ) : ℤ)) ≪≫
    (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod n))).mapIso
      (Stacks.EtaleCohomology.exactFunctorPlusHomologyIso
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar))
        ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          K₀.cocomplexPlus) ((2 : ℕ) : ℤ))

omit [CompactSpace (kbar ≃ₐ[k] kbar)] in
/-- The comparison `U(H²(RΓ^Gal_c(X_k̄, ℱ_μ))) ≅ H²_c(X_k̄, ℱ_μ)` with `ℱ_μ` written
`representationSheaf.{u, 0}` (as in `AlgebraicGeometry.compactSupportCyclotomicTraceGaloisHom`) is
the same map as with `ℱ_μ` written without the universe annotation (as in the injective resolution
`K₀`); the two only differ in how a universe of a category instance is spelled. -/
theorem galoisCompactSupportGroupForgetIso_hom_cyclotomic_eq :
    letI := connectedSpace_of_isCurve B X f
    (galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf.{u, 0} B X _ (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom =
    (galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf B X _ (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom :=
  rfl

/-- **The Galois-equivariant trace `tr : H²(Γ^Gal(res_ℤ K₀)) ⟶ ℚ/ℤ`**, a morphism of discrete
`ℤ[Aut_k(k̄)]`-modules, `ℚ/ℤ` with the trivial action:
`H²(Γ^Gal(res_ℤ K₀)) = res_ℤ H²(RΓ^Gal_c(X_k̄, ℱ_μ))`
(`AlgebraicGeometry.galoisHomOpGCyclotomicDerivedIso`), then the trace
(`AlgebraicGeometry.compactSupportCyclotomicTraceGaloisHom`, Tag 03VK at `ρ_μ`). Its formula is
`AlgebraicGeometry.galoisHomOpCyclotomicTrace_apply`. -/
def galoisHomOpCyclotomicTrace (hn : IsUnit ((n : ℕ) : kbar)) :
    (DerivedCategory.homologyFunctor (GaloisModules ℤ k kbar) 2).obj
        (DerivedCategory.Q.obj (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
          (cyclotomicIntResolution B X f kbar y n j K₀))) ⟶
      Stacks.ContinuousCohomology.ratCircle.{u, u + 1} (kbar ≃ₐ[k] kbar) :=
  (galoisHomOpGCyclotomicDerivedIso B X f kbar y n j K₀ ((2 : ℕ) : ℤ)).hom ≫
    compactSupportCyclotomicTraceGaloisHom B X f kbar y n j hn

/-- **The formula for the Galois-equivariant trace**: on underlying groups, `tr(x)` is
`AlgebraicGeometry.compactSupportCyclotomicTrace` (Tag 03VK at `ρ_μ`, then the scalar in
`ℤ/n ⊂ ℚ/ℤ`) of the class in `H²_c(X_k̄, ℱ_μ)` which
`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso` attaches to the image of `x` in
`H²(Γ(X̄_k̄, K₀|))` under `AlgebraicGeometry.galoisHomOpCyclotomicUnderlyingIso`. The input is the
comparison `Stacks.EtaleCohomology.galoisCompactSupportResolutionGaloisIso_underlying` of the chain
model with `RΓ^Gal_c`. -/
theorem galoisHomOpCyclotomicTrace_apply (hn : IsUnit ((n : ℕ) : kbar))
    (x : ((DerivedCategory.homologyFunctor (GaloisModules ℤ k kbar) 2).obj
      (DerivedCategory.Q.obj (Stacks.EtaleCohomology.galoisHomOpG (Over.mk j.toBase) kbar
        (cyclotomicIntResolution B X f kbar y n j K₀)))).obj.obj.V) :
    ((galoisHomOpCyclotomicTrace B X f kbar y n j K₀ hn).hom.hom.hom.hom x).down =
      compactSupportCyclotomicTrace B X f kbar y n j hn
        ((galoisCompactSupportResolutionIso (f := f) kbar _ K₀ ((2 : ℕ) : ℤ)).hom
          ((galoisHomOpCyclotomicUnderlyingIso B X f kbar y n j K₀).hom x)) := by
  let := connectedSpace_of_isCurve B X f
  -- The derived comparison and the class `w` of `x` in `H²(Γ^Gal(K₀))`.
  let D := galoisHomOpGCyclotomicDerivedIso B X f kbar y n j K₀ ((2 : ℕ) : ℤ)
  let w := (galoisHomOpGCyclotomicHomologyIso B X f kbar y n j K₀ ((2 : ℕ) : ℤ)).hom.hom.hom.hom x
  have h1 : (galoisHomOpCyclotomicTrace B X f kbar y n j K₀ hn).hom.hom.hom.hom x =
      (compactSupportCyclotomicTraceGaloisHom B X f kbar y n j hn).hom.hom.hom.hom
        (D.hom.hom.hom.hom x) := rfl
  have e1 := h1.trans (compactSupportCyclotomicTraceGaloisHom_apply B X f kbar y n j hn
    (D.hom.hom.hom.hom x))
  have e2 := ConcreteCategory.congr_hom
    (galoisCompactSupportGroupForgetIso_hom_cyclotomic_eq B X f kbar y n j) (D.hom.hom.hom.hom x)
  have hU := ConcreteCategory.congr_hom
    (Stacks.EtaleCohomology.galoisCompactSupportResolutionGaloisIso_underlying (ZMod n) f j kbar _
      K₀ ((2 : ℕ) : ℤ)) w
  have e3 : D.hom.hom.hom.hom x =
      ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar)).map
        (galoisCompactSupportResolutionGaloisIso (ZMod n) f j kbar _ K₀ ((2 : ℕ) : ℤ)).hom) w := rfl
  have e4 : (galoisHomOpCyclotomicUnderlyingIso B X f kbar y n j K₀).hom x =
      (Stacks.EtaleCohomology.exactFunctorPlusHomologyIso
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar))
        ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          K₀.cocomplexPlus) ((2 : ℕ) : ℤ)).hom w := rfl
  -- Chain the comparisons elementwise; `beta_reduce` puts the coercions of the instantiated
  -- equations in one form, so that each junction is a syntactic match.
  have eA := e2.trans (congrArg (ConcreteCategory.hom
    (galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf B X _ (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom) e3)
  have eB := (ConcreteCategory.comp_apply
      ((Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar)).map
        (galoisCompactSupportResolutionGaloisIso (ZMod n) f j kbar _ K₀ ((2 : ℕ) : ℤ)).hom)
      (galoisCompactSupportGroupForgetIso (ZMod n) f j kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
        ((representationSheaf B X _ (ZMod n)).obj
          (cyclotomicContinuousModule B X f kbar y n))) ((2 : ℕ) : ℤ)).hom w).symm.trans hU
  have eC := ConcreteCategory.comp_apply (Stacks.EtaleCohomology.exactFunctorPlusHomologyIso
        (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} (ZMod n) (kbar ≃ₐ[k] kbar))
        ((galoisGlobalSections (ZMod n) (Over.mk j.toBase) kbar).mapCochainComplexPlus.obj
          K₀.cocomplexPlus) ((2 : ℕ) : ℤ)).hom
    (galoisCompactSupportResolutionIso (f := f) kbar _ K₀ ((2 : ℕ) : ℤ)).hom w
  have eD := congrArg
    (ConcreteCategory.hom (galoisCompactSupportResolutionIso (f := f) kbar _ K₀ ((2 : ℕ) : ℤ)).hom)
    e4.symm
  have eL := congrArg ULift.down e1
  beta_reduce at eA eB eC eD eL ⊢
  exact eL.trans (congrArg (compactSupportCyclotomicTrace B X f kbar y n j hn)
    ((eA.trans eB).trans (eC.trans eD)))

end GaloisTrace

end AlgebraicGeometry
