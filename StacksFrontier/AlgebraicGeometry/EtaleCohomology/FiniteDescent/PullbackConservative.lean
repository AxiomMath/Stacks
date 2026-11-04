module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image along a surjection is conservative on abelian étale sheaves

Let `f : X ⟶ Y` be a surjective morphism of schemes. The inverse image functor `f⁻¹` on abelian
sheaves of the small étale sites kills no nonzero sheaf, and being exact it therefore reflects
monomorphisms, epimorphisms and isomorphisms.

The only input is that for a surjective morphism the unit `F ⟶ f_* f⁻¹F` is a monomorphism,
`Stacks.EtaleCohomology.mono_smallEtaleUnitAb_of_surjective`: if `f⁻¹F` vanishes then so does
`f_*f⁻¹F`, because direct image is additive, and a sheaf with a monomorphism into a zero object
is zero.

## Main results

* `Stacks.EtaleCohomology.isZero_of_isZero_smallEtalePullbackAb` — `f⁻¹F = 0` forces `F = 0`.
* `Stacks.EtaleCohomology.mono_of_mono_smallEtalePullbackAb_map`,
  `Stacks.EtaleCohomology.epi_of_epi_smallEtalePullbackAb_map` — inverse image reflects
  monomorphisms and epimorphisms.
* `Stacks.EtaleCohomology.isIso_of_isIso_smallEtalePullbackAb_map` and
  `Stacks.EtaleCohomology.reflectsIsomorphisms_smallEtalePullbackAb` — inverse image reflects
  isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Inverse image along a surjection kills no nonzero abelian étale sheaf.** If the inverse
image `f⁻¹F` of an abelian sheaf `F` on the small étale site of `Y` is a zero object, then so is
`F`. -/
public theorem isZero_of_isZero_smallEtalePullbackAb [Surjective f]
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    (hF : IsZero ((smallEtalePullbackAb f).obj F)) : IsZero F :=
  (IsZero.iff_id_eq_zero F).2 <| (mono_smallEtaleUnitAb_of_surjective f F).right_cancellation _ _
    (((smallEtalePushforwardAb f).map_isZero hF).eq_of_tgt _ _)

/-- **Inverse image along a surjection reflects monomorphisms of abelian étale sheaves.** -/
public theorem mono_of_mono_smallEtalePullbackAb_map [Surjective f]
    {F G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : F ⟶ G)
    (hφ : Mono ((smallEtalePullbackAb f).map φ)) : Mono φ := by
  rw [Preadditive.mono_iff_isZero_kernel]
  exact isZero_of_isZero_smallEtalePullbackAb f <|
    (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (smallEtalePullbackAb f) φ)

/-- **Inverse image along a surjection reflects epimorphisms of abelian étale sheaves.** -/
public theorem epi_of_epi_smallEtalePullbackAb_map [Surjective f]
    {F G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : F ⟶ G)
    (hφ : Epi ((smallEtalePullbackAb f).map φ)) : Epi φ := by
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact isZero_of_isZero_smallEtalePullbackAb f <|
    (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso (smallEtalePullbackAb f) φ)

/-- **Inverse image along a surjection reflects isomorphisms of abelian étale sheaves.** -/
public theorem isIso_of_isIso_smallEtalePullbackAb_map [Surjective f]
    {F G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (φ : F ⟶ G)
    (hφ : IsIso ((smallEtalePullbackAb f).map φ)) : IsIso φ := by
  have : Mono φ := mono_of_mono_smallEtalePullbackAb_map f φ inferInstance
  have : Epi φ := epi_of_epi_smallEtalePullbackAb_map f φ inferInstance
  exact isIso_of_mono_of_epi φ

/-- Inverse image along a surjection reflects isomorphisms. -/
public theorem reflectsIsomorphisms_smallEtalePullbackAb [Surjective f] :
    (smallEtalePullbackAb f).ReflectsIsomorphisms where
  reflects φ hφ := isIso_of_isIso_smallEtalePullbackAb_map f φ hφ

/-- **Inverse image along a surjection is faithful on abelian étale sheaves.** -/
@[sga "4 VIII 9.1" "special case"]
public theorem faithful_smallEtalePullbackAb [Surjective f] :
    (smallEtalePullbackAb f).Faithful where
  map_injective {F G} φ ψ h := by
    have hnat (χ : F ⟶ G) : χ ≫ (smallEtaleAdjunctionAb f).unit.app G =
        (smallEtaleAdjunctionAb f).unit.app F ≫
          (smallEtalePullbackAb f ⋙ smallEtalePushforwardAb f).map χ :=
      (smallEtaleAdjunctionAb f).unit.naturality χ
    refine (mono_smallEtaleUnitAb_of_surjective f G).right_cancellation _ _ ?_
    rw [hnat φ, hnat ψ, Functor.comp_map, Functor.comp_map, h]

/-- **Inverse image along a surjection reflects exactness of short complexes of abelian étale
sheaves.** -/
public theorem exact_of_exact_map_smallEtalePullbackAb [Surjective f]
    (S : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}))
    (hS : (S.map (smallEtalePullbackAb f)).Exact) : S.Exact := by
  let : (smallEtalePullbackAb f).Faithful := faithful_smallEtalePullbackAb f
  exact (ShortComplex.exact_map_iff_of_faithful S (smallEtalePullbackAb f)).1 hS

end Stacks.EtaleCohomology

end
