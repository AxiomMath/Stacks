module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroFirstProjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineCompactSupport

/-!
# The geometric fibres of the first projection of Laumon's plane

For the first projection `pr₁ : 𝔸² = Spec k'[x][t] → 𝔸¹_x = Spec k'[x]` of the plane of Laumon's
argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) and a point `Spec Ω → 𝔸¹_x` given
by `φ : k'[x] → Ω`, the fibre is `Spec Ω[t]`, with `Spec Ω[t] → 𝔸²` the spectrum of
`φ[t] : k'[x][t] → Ω[t]` (`Stacks.EtaleCohomology.isPullback_laumonFamilyPr₁_fibre`). Along it the
kernel `μ_h : 𝔸² → 𝔸¹`, `(x, t) ↦ t h(x)` (`Stacks.EtaleCohomology.laumonKernelMap`) becomes the
coordinate `t ↦ a t` with `a = φ(h)`
(`Stacks.EtaleCohomology.specMap_mapRingHom_comp_laumonKernelMap`), and for `a ≠ 0` this coordinate
exhibits the fibre as the base change `𝔸¹_{k'} ×_{k'} Spec Ω`
(`Stacks.EtaleCohomology.isPullback_specMap_scaledCoordinate`).

The vanishing of the cohomology sheaves of `Rf_! K` is checked on the geometric fibres at the
algebraic closures of the residue fields, with any presentation of these fibres as fibre products
(`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_isPullback_geometricFibres`).

## Main definitions

* `Stacks.EtaleCohomology.laumonKernelMap`.

## Main results

* `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_isPullback_geometricFibres`.
* `Stacks.EtaleCohomology.isPullback_laumonFamilyPr₁_fibre`.
* `Stacks.EtaleCohomology.specMap_mapRingHom_comp_laumonKernelMap`.
* `Stacks.EtaleCohomology.isPullback_specMap_scaledCoordinate`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so does the fibre criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

section Fibres

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))

/-- **`H^q(Rf_! K) = 0` as soon as it vanishes on presentations of the geometric fibres**: for
every point `y` of `Y`, a cartesian square `P = X ×_Y Spec Ω` over the geometric point at an
algebraic closure `Ω` of `κ(y)` with `H^q(Rf'_!(K|_P)) = 0`, for `K` killed by a positive
integer (proper base change for `Rf_!`, Tag 0F7L). -/
theorem isZero_homology_derivedLowerShriek_of_isPullback_geometricFibres
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (m : ℕ) (hm : 0 < m) (hK : m • 𝟙 K = 0)
    (q : ℤ)
    (h : ∀ y : Y, ∃ (P : Scheme.{u}) (u : P ⟶ X)
      (f' : P ⟶ Spec (.of (GeometricPoint.ofPoint Y y).residueField))
      (sq : IsPullback u f' f (GeometricPoint.ofPoint Y y).hom),
      IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((derivedLowerShriek.{u, 0} f' (j.baseChange sq) Λ).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ u).obj K)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj K)) := by
  refine isZero_of_forall_isZero_etaleModuleInverseImage Λ
    (fun y : Y => (GeometricPoint.ofPoint Y y).hom) (iUnion_range_geometricPoint_ofPoint Y) _
    fun y => ?_
  obtain ⟨P, u, f', sq, hy⟩ := h y
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K
    (isTorsionPlus_of_nsmul_id_eq_zero K m hm hK)
  obtain ⟨e⟩ := nonempty_homology_etaleModuleDerivedInverseImagePlus_iso Λ
    (GeometricPoint.ofPoint Y y).hom ((derivedLowerShriek.{u, 0} f j Λ).obj K) q
  exact hy.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K)).symm ≪≫ e).symm

end Fibres

section Square

variable (k' : Type u) [Field k'] {Ω : Type u} [Field Ω]

/-- **The fibre of `pr₁ : Spec k'[x][t] → Spec k'[x]` over `Spec φ : Spec Ω → Spec k'[x]` is
`Spec Ω[t]`**, mapping to the plane by `Spec φ[t]`. -/
theorem isPullback_laumonFamilyPr₁_fibre (φ : Polynomial k' →+* Ω) :
    IsPullback (Spec.map (CommRingCat.ofHom (mapRingHom φ)))
      (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω)))
      (laumonFamilyPr₁ k') (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra (Polynomial k') Ω := φ.toAlgebra
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom (Polynomial k') Ω)).flip

/-- **The kernel `μ_h : 𝔸² → 𝔸¹`, `(x, t) ↦ t h(x)`**, the spectrum of `X ↦ h(x) t`. -/
public abbrev laumonKernelMap (h : Polynomial k') :
    Spec (.of (Polynomial (Polynomial k'))) ⟶ Spec (.of (Polynomial k')) :=
  Spec.map (CommRingCat.ofHom (eval₂RingHom ((C : Polynomial k' →+* Polynomial (Polynomial k')).comp
    (C : k' →+* Polynomial k')) (C h * Polynomial.X)))

/-- **On the fibre over `Spec φ`, the kernel `μ_h` is the coordinate `t ↦ φ(h) t`.** -/
theorem specMap_mapRingHom_comp_laumonKernelMap (φ : Polynomial k' →+* Ω) (h : Polynomial k') :
    Spec.map (CommRingCat.ofHom (mapRingHom φ)) ≫ laumonKernelMap k' h =
      Spec.map (CommRingCat.ofHom (eval₂RingHom ((C : Ω →+* Polynomial Ω).comp
        (φ.comp (C : k' →+* Polynomial k'))) (C (φ h) * Polynomial.X))) := by
  rw [← Spec.map_comp]
  congr 1
  ext : 1
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp
  · simp

/-- **The scaled coordinate `t ↦ a t`, `a ≠ 0`, exhibits `Spec Ω[t]` as
`𝔸¹_{k'} ×_{k'} Spec Ω`.** -/
theorem isPullback_specMap_scaledCoordinate (ι : k' →+* Ω) (a : Ω) (ha : a ≠ 0) :
    IsPullback (Spec.map (CommRingCat.ofHom (eval₂RingHom ((C : Ω →+* Polynomial Ω).comp ι)
        (C a * Polynomial.X))))
      (Spec.map (CommRingCat.ofHom (C : Ω →+* Polynomial Ω))) (affineLineStructureMap k')
      (Spec.map (CommRingCat.ofHom ι)) := by
  let : Algebra k' Ω := ι.toAlgebra
  have h₀ := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom k' Ω)).flip
  -- the automorphism `t ↦ a⁻¹ t` of `Ω[t]`
  let τ : Polynomial Ω ≃+* Polynomial Ω := RingEquiv.ofRingHom
    (eval₂RingHom (C : Ω →+* Polynomial Ω) (C a⁻¹ * Polynomial.X))
    (eval₂RingHom (C : Ω →+* Polynomial Ω) (C a * Polynomial.X))
    (Polynomial.ringHom_ext (fun b => by simp) (by
      simp [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha]))
    (Polynomial.ringHom_ext (fun b => by simp) (by
      simp [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha]))
  -- precomposition with `τ` on the level of spectra
  have key : ∀ {R : CommRingCat.{u}} (A B : R ⟶ .of (Polynomial Ω)),
      B ≫ τ.toCommRingCatIso.hom = A → Spec.map A =
        (Scheme.Spec.mapIso τ.toCommRingCatIso.op).hom ≫ Spec.map B := by
    rintro R A B rfl
    simp
  refine h₀.of_iso (Scheme.Spec.mapIso τ.toCommRingCatIso.op) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · refine key _ _ (CommRingCat.hom_ext (Polynomial.ringHom_ext (fun b => ?_) ?_))
    · simp [τ, RingHom.algebraMap_toAlgebra]
    · simp [τ, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha]
  · exact key _ _ (CommRingCat.hom_ext (RingHom.ext fun b => by simp [τ]))

end Square

end Stacks.EtaleCohomology

end
