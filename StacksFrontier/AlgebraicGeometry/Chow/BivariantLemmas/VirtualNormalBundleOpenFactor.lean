module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# Virtual normal bundles along an open factorization of an immersion

Let `i : Z ⟶ X` be an immersion of schemes and let `U ⊆ X` be an open subscheme such that `i`
factors as `i = i' ≫ ι_U`. The conormal sheaf of `i` (Stacks 01R2) is the conormal sheaf of `i'`
(Stacks 01R3 (1)), so a virtual normal bundle for `i` in the sense of Stacks 0FBQ (2) is the same
thing as a virtual normal bundle for `i'`. This is what makes item (3) of Stacks 0FBQ statable:
it chooses an open `U` through which `i` factors as a closed immersion `Z ⟶ U` and applies the
construction for closed immersions to the virtual normal bundle `𝒩`, read as one for `Z ⟶ U`.

## Main definitions

* `Stacks.Chow.immersionConormalSheafFactorIso` — `𝒞_{Z/X} ≅ 𝒞_{Z/U}` for `i = i' ≫ ι_U`.
* `Stacks.Chow.VirtualNormalBundle.toOpenFactor`, `Stacks.Chow.VirtualNormalBundle.ofOpenFactor`
  — a virtual normal bundle for `i = i' ≫ ι_U` read as one for `i'`, and conversely.
* `Stacks.Chow.VirtualNormalBundle.openFactorEquiv` — the two are mutually inverse.

## Main results

* `Stacks.Chow.exists_isClosedImmersion_comp_ι_eq` — every immersion factors through a closed
  immersion into an open subscheme of its target, which is the choice Stacks 0FBQ (3) makes.

## References

* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

add_to_stacks 0FBQ "(1): the conormal sheaf of an immersion, Stacks 01R2"
  Stacks.Thickenings.immersionConormalSheaf

variable {Z X : Scheme.{u}}

/-- **Stacks 0FBQ (3), the choice of `U`.** Every immersion `i : Z ⟶ X` factors as a closed
immersion `i' : Z ⟶ U` into an open subscheme `U ⊆ X` followed by the inclusion of `U`. -/
theorem exists_isClosedImmersion_comp_ι_eq (i : Z ⟶ X) [IsImmersion i] :
    ∃ (U : X.Opens) (i' : Z ⟶ U.toScheme), IsClosedImmersion i' ∧ i' ≫ U.ι = i :=
  ⟨i.coborderRange, i.liftCoborder, inferInstance, i.liftCoborder_ι⟩

/-- **`𝒞_{Z/X} ≅ 𝒞_{Z/U}`.** The conormal sheaf of an immersion `i : Z ⟶ X` which factors as
`i = i' ≫ ι_U` through an open subscheme `U ⊆ X` is the conormal sheaf of the immersion
`i' : Z ⟶ U`: both are identified with the ringed-space conormal sheaves of the two morphisms by
`Stacks.Immersion.conormalSheafSelfIso`, and those agree by
`Stacks.Immersion.conormalSheafFactorIso`. -/
noncomputable def immersionConormalSheafFactorIso {i : Z ⟶ X} [IsImmersion i] (U : X.Opens)
    (i' : Z ⟶ U.toScheme) [IsImmersion i'] (hU : i' ≫ U.ι = i) :
    Stacks.Thickenings.immersionConormalSheaf i ≅
      Stacks.Thickenings.immersionConormalSheaf i' := by
  subst hU
  exact (Stacks.Immersion.conormalSheafSelfIso (i' ≫ U.ι)).symm ≪≫
    Stacks.Immersion.conormalSheafFactorIso U i' ≪≫ Stacks.Immersion.conormalSheafSelfIso i'

variable {i : Z ⟶ X} [IsImmersion i] {U : X.Opens} {i' : Z ⟶ U.toScheme} [IsImmersion i']
  (hU : i' ≫ U.ι = i)

/-- A virtual normal bundle for an immersion `i = i' ≫ ι_U` is a virtual normal bundle for `i'`:
the same finite locally free module, with its surjection onto `𝒞_{Z/X}` read as one onto
`𝒞_{Z/U}` through `Stacks.Chow.immersionConormalSheafFactorIso`. -/
noncomputable def VirtualNormalBundle.toOpenFactor (N : VirtualNormalBundle i) :
    VirtualNormalBundle i' where
  bundle := N.bundle
  surjection := N.surjection ≫ (immersionConormalSheafFactorIso U i' hU).hom
  epi := @epi_comp _ _ _ _ _ _ N.epi _
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))

/-- A virtual normal bundle for `i'` is a virtual normal bundle for `i = i' ≫ ι_U`. -/
noncomputable def VirtualNormalBundle.ofOpenFactor (N : VirtualNormalBundle i') :
    VirtualNormalBundle i where
  bundle := N.bundle
  surjection := N.surjection ≫ (immersionConormalSheafFactorIso U i' hU).inv
  epi := @epi_comp _ _ _ _ _ _ N.epi _
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))

/-- The module of `N.toOpenFactor hU` is the module of `N`. -/
@[simp]
theorem VirtualNormalBundle.toOpenFactor_bundle (N : VirtualNormalBundle i) :
    (N.toOpenFactor hU).bundle = N.bundle :=
  rfl

/-- The surjection of `N.toOpenFactor hU` is that of `N` followed by the isomorphism
`immersionConormalSheafFactorIso U i' hU`. -/
@[simp]
theorem VirtualNormalBundle.toOpenFactor_surjection (N : VirtualNormalBundle i) :
    (N.toOpenFactor hU).surjection =
      N.surjection ≫ (immersionConormalSheafFactorIso U i' hU).hom :=
  rfl

/-- The module of `N.ofOpenFactor hU` is the module of `N`. -/
@[simp]
theorem VirtualNormalBundle.ofOpenFactor_bundle (N : VirtualNormalBundle i') :
    (N.ofOpenFactor hU).bundle = N.bundle :=
  rfl

/-- The surjection of `N.ofOpenFactor hU` is that of `N` followed by the inverse of the
isomorphism `immersionConormalSheafFactorIso U i' hU`. -/
@[simp]
theorem VirtualNormalBundle.ofOpenFactor_surjection (N : VirtualNormalBundle i') :
    (N.ofOpenFactor hU).surjection =
      N.surjection ≫ (immersionConormalSheafFactorIso U i' hU).inv :=
  rfl

/-- Reading a virtual normal bundle of `i` as one of `i'` keeps the rank of the module. -/
instance VirtualNormalBundle.isFiniteLocallyFreeOfRank_toOpenFactor (N : VirtualNormalBundle i)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N.bundle r] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (N.toOpenFactor hU).bundle r :=
  ‹_›

/-- The virtual normal bundles of `i = i' ≫ ι_U` and of `i'` correspond. -/
noncomputable def VirtualNormalBundle.openFactorEquiv :
    VirtualNormalBundle i ≃ VirtualNormalBundle i' where
  toFun N := N.toOpenFactor hU
  invFun N := N.ofOpenFactor hU
  left_inv N := by
    obtain ⟨E, s⟩ := N
    simp only [VirtualNormalBundle.ofOpenFactor, VirtualNormalBundle.toOpenFactor]
    congr 1
    exact (Category.assoc _ _ _).trans
      ((congrArg (s ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id s))
  right_inv N := by
    obtain ⟨E, s⟩ := N
    simp only [VirtualNormalBundle.ofOpenFactor, VirtualNormalBundle.toOpenFactor]
    congr 1
    exact (Category.assoc _ _ _).trans
      ((congrArg (s ≫ ·) (Iso.inv_hom_id _)).trans (Category.comp_id s))

end Stacks.Chow

end
