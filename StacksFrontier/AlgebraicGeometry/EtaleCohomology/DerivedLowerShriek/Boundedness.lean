module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimensionPlus

/-!
# Boundedness of `Rf_!` for torsion coefficients

Let `f : X ⟶ Y` be a morphism of schemes with `Y` quasi-compact, `j : X ⟶ X̄` a compactification
of `X` over `Y`, and `Λ` a ring annihilated by a positive integer. The functor
`Rf_! = Rf̄_* ∘ Rj_!` of `Stacks.EtaleCohomology.derivedLowerShriek` has bounded cohomological
amplitude: there is `N` such that for every `K` in `D⁺(X_étale, Λ)` whose cohomology sheaves
vanish outside `[a, a + n]`, the cohomology sheaves of `Rf_! K` vanish outside `[a, a + n + N]`.
This is part (3) of Stacks 0G2A for a torsion coefficient ring.

## Main results

* `Stacks.EtaleCohomology.exists_isLE_derivedLowerShriek_of_nsmul_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f))

/-- If `m • 1 = 0` in `Λ` with `m > 0`, the underlying abelian sheaf of every sheaf of
`Λ`-modules on `X_étale` is torsion: it is annihilated by `m`. -/
theorem torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero (m : ℕ) (hm : 0 < m)
    (hΛ : (m : Λ) = 0) {Z : Scheme.{u}} (G : EtaleModules.{u, 0} Λ Z) :
    Stacks.Torsion.torsionSheafProperty Z.smallEtaleTopology
      ((etaleModuleForgetAb.{u, 0} Λ Z).obj G) := by
  intro U x
  refine ⟨⊤, Z.smallEtaleTopology.top_mem U, fun V g _ => ⟨m, hm, ?_⟩⟩
  show m • (G.obj.map g.op x : G.obj.obj (Opposite.op V)) = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]

/-- `Rf_!` preserves the lower bound of a bounded below complex, `Rj_!` being exact and `Rf̄_*`
the right derived functor of a left exact functor. -/
theorem isGE_derivedLowerShriek_obj (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (a : ℤ)
    [K.IsGE a] : ((derivedLowerShriek.{u, 0} f j Λ).obj K).IsGE a :=
  have : ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj K).IsGE a :=
    Functor.isGE_rightDerivedFunctorPlus_obj
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) K a
  Functor.isGE_rightDerivedFunctorPlus_obj (etaleModuleDirectImage.{u, 0} Λ j.toBase)
    ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj K) a

/-- **The cohomological amplitude of `Rf_!` is bounded, for a torsion coefficient ring.** If
`m • 1 = 0` in `Λ` with `m > 0` and `Y` is quasi-compact, there is `N` such that `Rf_!` carries
every object of `D⁺(X_étale, Λ)` with cohomology in degrees `[a, a + n]` to an object with
cohomology in degrees `≤ a + n + N`. (Part (3) of Stacks 0G2A for a torsion ring; the lower
bound is `Stacks.EtaleCohomology.isGE_derivedLowerShriek_obj`.) -/
theorem exists_isLE_derivedLowerShriek_of_nsmul_eq_zero [CompactSpace Y] (m : ℕ) (hm : 0 < m)
    (hΛ : (m : Λ) = 0) :
    ∃ N : ℕ, ∀ (a : ℤ) (n : ℕ) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)),
      K.IsGE a → K.IsLE (a + n) →
        (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj K)).IsLE
          (a + n + N) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_le j.toBase
  refine ⟨2 * d, fun a n K hGE hLE => ?_⟩
  refine Stacks.BoundedCohomologicalDimension.isLE_map_obj_of_cohomology_mem
    (derivedLowerShriek.{u, 0} f j Λ ⋙ DerivedCategory.Plus.ι) ⊤ inferInstance (2 * d : ℕ)
    (fun q M _ => ?_) a n K hGE hLE (fun _ _ _ => trivial)
  let e : (DerivedCategory.Plus.singleFunctor _ q).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj M) ≅
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion).obj
        ((DerivedCategory.Plus.singleFunctor _ q).obj M) :=
    (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) q).app M
  have h := Stacks.BoundedCohomologicalDimension.isLE_rightDerivedFunctorPlus_single
    (etaleModuleDirectImage.{u, 0} Λ j.toBase)
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj M) (2 * d : ℕ) q
    (fun p hp => isZero_rightDerived_etaleModuleDirectImage_of_isProper Λ j.toBase d hd _
      (torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero Λ m hm hΛ _) p
      (by exact_mod_cast hp))
  have : DerivedCategory.TStructure.t.IsLE (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase).obj
        ((DerivedCategory.Plus.singleFunctor _ q).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj M)))) (q + (2 * d : ℕ)) := h
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (DerivedCategory.Plus.ι.mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase).mapIso e)) _

/-- Integer-indexed form of an amplitude bound for `Rf_!`: if `K` has cohomology in degrees
`[a, b]`, then `Rf_! K` has cohomology in degrees `≤ b + N`. -/
private theorem isLE_derivedLowerShriek_obj_of_isLE_of_bound (N : ℕ)
    (hN : ∀ (a : ℤ) (n : ℕ) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)),
      K.IsGE a → K.IsLE (a + n) →
        (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj K)).IsLE
          (a + n + N))
    (a b : ℤ) (hab : a ≤ b) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hGE : K.IsGE a) (hLE : K.IsLE b) :
    (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj K)).IsLE (b + N) := by
  have hLE' : K.IsLE (a + ((b - a).toNat : ℕ)) := by
    rw [Int.toNat_of_nonneg (by omega)]; simpa using hLE
  have h := hN a (b - a).toNat K hGE hLE'
  rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at h

/-- **`Rf_!` of a complex with finitely many nonzero cohomology sheaves has finitely many nonzero
cohomology sheaves**, for a torsion coefficient ring and `Y` quasi-compact: there is `N` such
that `Hⁱ(Rf_! K) = 0` for `i` outside `[a, b + N]` whenever `Hⁱ(K) = 0` for `i` outside
`[a, b]`. (Part (3) of Stacks 0G2A for a torsion ring and bounded `K`.) -/
theorem exists_isZero_homology_derivedLowerShriek_of_nsmul_eq_zero [CompactSpace Y] (m : ℕ)
    (hm : 0 < m) (hΛ : (m : Λ) = 0) :
    ∃ N : ℕ, ∀ (a b : ℤ), a ≤ b → ∀ (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)),
      K.IsGE a → K.IsLE b → ∀ i : ℤ, (i < a ∨ b + N < i) →
        IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
          ((derivedLowerShriek.{u, 0} f j Λ).obj K)) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedLowerShriek_of_nsmul_eq_zero Λ f j m hm hΛ
  refine ⟨N, fun a b hab K hGE hLE i hi => ?_⟩
  rcases hi with hi | hi
  · have := isGE_derivedLowerShriek_obj Λ f j K a
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ a i hi
  · have h := isLE_derivedLowerShriek_obj_of_isLE_of_bound Λ f j N hN a b hab K hGE hLE
    exact DerivedCategory.isZero_of_isLE _ (b + N) i hi

/-- `Rf_!` is a triangulated functor, being the composite of `Rj_!` and `Rf̄_*`. -/
instance derivedLowerShriek_isTriangulated_univZero :
    (derivedLowerShriek.{u, 0} f j Λ).IsTriangulated :=
  inferInstanceAs ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j.immersion ⋙
    etaleModuleDerivedDirectImage.{u, 0} Λ j.toBase).IsTriangulated)

/-- **Part (1) of Stacks 0G2A.** For `E` in `D⁺(X_étale, Λ)` and `i ≤ a`, the map
`Hⁱ(Rf_!(τ_{≤ a} E)) ⟶ Hⁱ(Rf_! E)` is an isomorphism: the third vertex `Rf_!(τ_{≥ a+1} E)` of
the image of the truncation triangle lives in degrees `≥ a + 1`. -/
theorem isIso_homology_derivedLowerShriek_map_truncLEι
    (E : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map ((derivedLowerShriek.{u, 0} f j Λ).map
      ((DerivedCategory.Plus.TStructure.t.truncLEι a).app E))) := by
  let t := DerivedCategory.Plus.TStructure.t (C := EtaleModules.{u, 0} Λ X)
  let T := (t.triangleLEGE a (a + 1) rfl).obj E
  have hT := t.triangleLEGE_distinguished a (a + 1) rfl E
  have h3 : ((derivedLowerShriek.{u, 0} f j Λ).mapTriangle.obj T).obj₃.IsGE (a + 1) :=
    isGE_derivedLowerShriek_obj Λ f j ((t.truncGE (a + 1)).obj E) (a + 1)
  exact DerivedCategory.Plus.isIso_homologyMap_mor₁_of_isGE₃ _
    ((derivedLowerShriek.{u, 0} f j Λ).map_distinguished T hT) i (a + 1) h3 (by omega)

/-- **Part (2) of Stacks 0G2A, for a torsion coefficient ring.** If `m • 1 = 0` in `Λ` with
`m > 0` and `Y` is quasi-compact, there is `N` such that for every `E` in `D⁺(X_étale, Λ)` and
`i ≥ b`, the map `Hⁱ(Rf_! E) ⟶ Hⁱ(Rf_!(τ_{≥ b - N} E))` is an isomorphism: the first vertex
`Rf_!(τ_{≤ b-N-1} E)` of the image of the truncation triangle lives in degrees `≤ b - 1` by
part (3). -/
theorem exists_isIso_homology_derivedLowerShriek_map_truncGEπ [CompactSpace Y] (m : ℕ)
    (hm : 0 < m) (hΛ : (m : Λ) = 0) :
    ∃ N : ℕ, ∀ (E : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (b i : ℤ), b ≤ i →
      IsIso ((DerivedCategory.Plus.homologyFunctor _ i).map ((derivedLowerShriek.{u, 0} f j Λ).map
        ((DerivedCategory.Plus.TStructure.t.truncGEπ (b - N)).app E))) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedLowerShriek_of_nsmul_eq_zero Λ f j m hm hΛ
  refine ⟨N, fun E b i hbi => ?_⟩
  let t := DerivedCategory.Plus.TStructure.t (C := EtaleModules.{u, 0} Λ X)
  obtain ⟨a₀, ha₀⟩ := E.property
  let a := min a₀ (b - N - 1)
  have hEa : E.IsGE a := by
    have : (DerivedCategory.Plus.ι.obj E).IsGE a₀ := ha₀
    exact (DerivedCategory.Plus.isGE_ι_obj_iff E a).1
      (DerivedCategory.TStructure.t.isGE_of_ge _ a a₀ (min_le_left _ _))
  let T := (t.triangleLEGE (b - N - 1) (b - N) (by omega)).obj E
  have hT := t.triangleLEGE_distinguished (b - N - 1) (b - N) (by omega) E
  let L := (t.truncLE (b - N - 1)).obj E
  have h1GE : L.IsGE a := inferInstance
  have h1LE : L.IsLE (b - N - 1) := t.isLE_truncLE_obj E _ _ le_rfl
  have hLE := isLE_derivedLowerShriek_obj_of_isLE_of_bound Λ f j N hN a (b - N - 1)
    (min_le_right _ _) L h1GE h1LE
  let R := derivedLowerShriek.{u, 0} f j Λ ⋙ DerivedCategory.Plus.ι
  have hLE' : (R.mapTriangle.obj T).obj₁.IsLE (b - 1) := by
    show (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f j Λ).obj L)).IsLE (b - 1)
    rwa [show b - 1 = b - N - 1 + N by omega]
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ (R.mapTriangle.obj T)
    (R.map_distinguished T hT) i (b - 1) hLE' (by omega)

end Stacks.EtaleCohomology

end
