module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.DenseOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperLocallyConstantDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.StratumPurityDuality

/-!
# Compactly supported cohomology near the top degree only sees a dense open

Let `W` be a scheme of finite type over a separably closed field `k`, `N > 0` and `Λ = ℤ/N`, with a
compactification `j : W → X̄` (an open immersion into a proper `k`-scheme), and let `i : Z → W` be
a closed subscheme of dimension at most `d`. Then `H^q_c(Z, M) = Ext^q_X̄(Λ, j_! i_* M)` vanishes
for `q > 2d`: `j_! i_* M = ῑ_* t_! M` for the closure `ῑ : Z̄ → X̄` of `Z` and the open immersion
`t : Z → Z̄`, `Ext_X̄(Λ, ῑ_* -) = Ext_Z̄(Λ, -)`, the dimension of `Z̄` is at most that of its dense
open `Z` (`AlgebraicGeometry.topologicalKrullDim_le_of_isOpen_of_dense`), and Tag 095U applies on
the proper scheme `Z̄`.

Consequently, for an open `U` of `W` with closed complement `Z` of dimension at most `d`, the
short exact sequence `0 → U_! U^{-1} L → L → i_* i^{-1} L → 0` (Tag 095L) shows that
`H^q_c(U, L) → H^q_c(W, L)` is bijective for `q > 2d + 1`. For `W` of dimension `e` and `U` dense,
`d = e - 1` and this covers the degrees `q ≥ 2e`.

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_constantModuleSheaf_zmod_of_proper`: Tag 095U with
  `ℤ/N` coefficients, read in `Ext`.
* `Stacks.EtaleCohomology.subsingleton_ext_extensionByZero_directImage_of_closed`:
  `H^q_c(Z, M) = 0` for `q > 2 dim Z`.
* `Stacks.EtaleCohomology.bijective_ext_extensionByZero_counit_of_closed`:
  `H^q_c(U, L) ≅ H^q_c(W, L)` for `q > 2 dim (W \ U) + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize comp_preservesFiniteLimits

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` below get stuck on a universe
-- constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- **Tag 095U with `ℤ/N` coefficients, read in `Ext`**: on a scheme `T` proper over a separably
closed field, of dimension at most `d`, `Ext^q(ℤ/N, K) = 0` for `q > 2d`. -/
theorem subsingleton_ext_constantModuleSheaf_zmod_of_proper {k : Type u} [Field k]
    [IsSepClosed k] {T : Scheme.{u}} (g : T ⟶ Spec (.of k)) [IsProper g] (d : ℕ)
    (hdim : topologicalKrullDim T ≤ d) (N : ℕ) [NeZero N] (K : EtaleModules.{u, 0} (ZMod N) T)
    (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} (ZMod N)
      T.smallEtaleTopology) K q) := by
  have h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian T (ZMod N)).obj K) q) :=
    properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
      properDirectImageVanishingStatement k g d hdim _
      (torsionSheafProperty_etaleModuleUnderlyingAbelian_zmod N K) q hq
  exact (extForgetSheafHAddEquiv (ZMod N) T K q).toEquiv.subsingleton

variable {ℓ : ℕ} [NeZero ℓ] {k : Type u} [Field k] [IsSepClosed k] {W : Scheme.{u}}
  {f : W ⟶ Spec (.of k)} [QuasiCompact f]
  (jc : CompactificationOf (Over.mk f))

/-- **`H^q_c(Z, M) = 0` for `q > 2 dim Z`.** For a closed subscheme `i : Z → W` of dimension at
most `d` and a compactification `j : W → X̄`, `Ext^q_X̄(Λ, j_! i_* M) = 0` for `q > 2d`: it is
`Ext^q_{Z̄}(Λ, t_! M)` on the closure `Z̄` of `Z` (Tag 095U, `dim Z̄ = dim Z`). -/
theorem subsingleton_ext_extensionByZero_directImage_of_closed
    [TopologicalSpace.NoetherianSpace jc.space] {Z : Scheme.{u}} (i : Z ⟶ W)
    [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (M : EtaleModules.{u, 0} (ZMod ℓ) Z) (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj M)) q) := by
  let t := (jc.closedImmersion i).toImage
  let ι : jc.closedSpace i ⟶ jc.space := jc.closedSpaceι i
  have : @IsClosedImmersion _ jc.space ι := (inferInstance : IsClosedImmersion (jc.closedSpaceι i))
  have : @IsIntegralHom _ jc.space ι := (inferInstance : IsIntegralHom (jc.closedSpaceι i))
  let sq := jc.isPullback_restrictClosed i
  let uS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) t
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) ι
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod ℓ) ι
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (ZMod ℓ) ι
  have : PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι) :=
    etaleModuleDirectImage_preservesFiniteColimits_of_isIntegralHom (ZMod ℓ) ι
  have : TopologicalSpace.NoetherianSpace (jc.restrictClosed i).space :=
    ι.isClosedEmbedding.isInducing.noetherianSpace
  have hdimZ : topologicalKrullDim (jc.restrictClosed i).space ≤ d :=
    calc topologicalKrullDim (jc.restrictClosed i).space
        ≤ topologicalKrullDim (Set.range t.base) :=
          topologicalKrullDim_le_of_isOpen_of_dense k _ (jc.restrictClosed i).toBase _
            t.isOpenEmbedding.isOpen_range t.denseRange
      _ = topologicalKrullDim Z :=
          t.isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq.symm
      _ ≤ d := hd
  have : Subsingleton (Ext (unitSheaf (X := jc.closedSpace i) ℓ) (uS.obj M) q) :=
    subsingleton_ext_constantModuleSheaf_zmod_of_proper (jc.restrictClosed i).toBase d hdimZ ℓ _
      q hq
  have hι : Subsingleton (Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).obj (uS.obj M)) q) := by
    refine Function.Injective.subsingleton
      (f := fun x => (Ext.mk₀ ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) ι).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).inv).comp
        (Stacks.ExtAdjunction.extMap adj (unitSheaf (X := jc.space) ℓ) (uS.obj M) q x)
        (zero_add q)) ?_
    exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).1.comp
      (Stacks.ExtAdjunction.extMap_bijective adj _ _ q).1
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    ((etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i t jc.immersion ι sq).app M).symm
    q hι

/-- **`H^q_c(U, L) ≅ H^q_c(W, L)` above twice the dimension of the complement, plus one.** For an
open `U` of `W` with closed complement `i : Z → W` of dimension at most `d` and a compactification
`j : W → X̄`, the counit `U_! U^{-1} L → L` induces a bijection
`Ext^q_X̄(Λ, j_! U_! U^{-1} L) → Ext^q_X̄(Λ, j_! L)` for `q > 2d + 1`: in the long exact sequence
of `0 → j_! U_! U^{-1} L → j_! L → j_! i_* i^{-1} L → 0` (Tag 095L) the third terms in degrees
`q - 1` and `q` vanish (`subsingleton_ext_extensionByZero_directImage_of_closed`). -/
theorem bijective_ext_extensionByZero_counit_of_closed [TopologicalSpace.NoetherianSpace jc.space]
    (U : W.Opens) {Z : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    (hiU : Set.range U.ι.base = (Set.range i.base)ᶜ) (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : EtaleModules.{u, 0} (ZMod ℓ) W) (q : ℕ) (hq : 2 * d + 1 < q) :
    Function.Bijective (fun x : Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj L)) q =>
      x.comp (Ext.mk₀ ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) U.ι).counit.app L))) (add_zero q)) := by
  let Φ := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion
  obtain ⟨h, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage (ZMod ℓ) i U.ι hiU L
  have hS' := hS.map_of_exact Φ
  have hvan : ∀ m, 2 * d < m → Subsingleton (Ext (unitSheaf (X := jc.space) ℓ)
      (Φ.obj ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) i).obj L))) m) := fun m hm =>
    subsingleton_ext_extensionByZero_directImage_of_closed jc i d hd _ m hm
  refine ⟨?_, fun x₂ => ?_⟩
  · let φ := (Ext.mk₀ (Φ.map ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) U.ι).counit.app
      L))).postcomp (unitSheaf (X := jc.space) ℓ) (add_zero q)
    change Function.Injective φ
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (unitSheaf (X := jc.space) ℓ) hS' x hx
      (show q - 1 + 1 = q by omega)
    rw [← hx₃, @Subsingleton.elim _ (hvan (q - 1) (by omega)) x₃ 0, Ext.zero_comp]
  · exact Ext.covariant_sequence_exact₂ (unitSheaf (X := jc.space) ℓ) hS' x₂
      (@Subsingleton.elim _ (hvan q (by omega)) _ _)

end Stacks.EtaleCohomology
