module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.KInjective.ChangeOfRings

/-!
# Coextension of scalars is the Hom complex out of the target ring

Let `f : A →+* B` be a homomorphism of commutative rings. Coextension of scalars is the functor
`Hom_A(B, -) : Mod(A) ⥤ Mod(B)`, and applied degreewise to a complex `I` of `A`-modules it gives
the complex `Hom_A(B, I)` whose derived incarnation is `RHom_A(B, -)` of [stacks 0A70]. The
*internal* derived Hom of [stacks 0A63] is computed, at a K-injective second argument, by the
ordinary Hom complex `CochainComplex.HomComplexR`. The two descriptions of `RHom_A(B, I)`
therefore meet at a comparison of complexes of `A`-modules,

`Hom^•_A(B[0], I) ≅ Hom_A(B, I)` ,

which is what this file proves, as
`Dualizing.coextendComplexIsoHomComplexSingle`. Both sides have `Hom_A(B, I^n)` in degree `n`
and both differentials are postcomposition with the differential of `I`; the Hom complex has no
sign to contribute because the single complex `B[0]` has zero differential.

## Main definitions

* `Dualizing.targetAsModule` — the target ring `B`, universe-lifted and viewed as an `A`-module
  by restriction of scalars along `f`. This is the object `B[0]` above.
* `Dualizing.coextendScalarsHomLinearEquiv` — the carrier of `Hom_A(B, M)`, viewed as an
  `A`-module by restriction of scalars, is `A`-linearly the module of `A`-linear maps out of
  `Dualizing.targetAsModule`.
* `Dualizing.cochainFromSingleLinearEquiv` — the `A`-linear form of
  `CochainComplex.HomComplex.Cochain.fromSingleEquiv`: degree-`n` cochains out of a single
  complex in degree `0` are the maps into degree `n` of the target.

## Main results

* `Dualizing.coextendComplexIsoHomComplexSingle` — the comparison of complexes displayed above.

## Implementation notes

The `A`-module structure that restriction of scalars puts on `Hom_A(B, M)` is `a • g = x ↦
g (x * f a)`, whereas the one on `Hom_A(B, M)` read as a module of `A`-linear maps is `a • g =
x ↦ a • g x`; these agree because `g` is `A`-linear and `B` is commutative, which is the only
place commutativity of `B` is used.

Universes: the carrier of `(ModuleCat.coextendScalars f).obj M` is `B →ₗ[A] M` with `B` taken at
its own universe, so the first argument of the Hom complex is the universe lift of `B`, and the
two descriptions differ by `ULift.up`.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v

namespace Dualizing

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- The target ring `B` of `f : A →+* B`, universe-lifted and viewed as an `A`-module by
restriction of scalars along `f`. Placed in degree zero it is the first argument of the derived
Hom `RHom_A(B, -)` that derived coextension of scalars computes. -/
noncomputable abbrev targetAsModule : ModuleCat.{max v u} A :=
  (ModuleCat.restrictScalars.{max v u} f).obj (ModuleCat.of B (ULift.{max v u} B))

/-- **Coextension of scalars is Hom out of the target ring.** The carrier of `Hom_A(B, M)`,
viewed as an `A`-module by restriction of scalars along `f`, is `A`-linearly the module of
`A`-linear maps from `Dualizing.targetAsModule` to `M`. -/
noncomputable def coextendScalarsHomLinearEquiv (M : ModuleCat.{max v u} A) :
    ((ModuleCat.restrictScalars.{max v u} f).obj
        ((ModuleCat.coextendScalars.{u, u, max v u} f).obj M) : Type (max v u)) ≃ₗ[A]
      ((targetAsModule.{u, v} f : Type (max v u)) →ₗ[A] (M : Type (max v u))) where
  toFun w := show (targetAsModule.{u, v} f : Type (max v u)) →ₗ[A] (M : Type (max v u)) from
    { toFun := fun x => ModuleCat.CoextendScalars.equiv f M w x.down
      map_add' := fun x y => (ModuleCat.CoextendScalars.equiv f M w).map_add _ _
      map_smul' := fun a x => (ModuleCat.CoextendScalars.equiv f M w).map_smul a x.down }
  invFun h := (ModuleCat.CoextendScalars.equiv f M).symm
    { toFun := fun b => h (ULift.up b)
      map_add' := fun x y => h.map_add _ _
      map_smul' := fun a x => h.map_smul a (ULift.up x) }
  left_inv w := by
    apply (ModuleCat.CoextendScalars.equiv f M).injective
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  right_inv h := by
    ext x
    simp only [LinearEquiv.apply_symm_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rfl
  map_add' w w' := by ext x; simp; rfl
  map_smul' a w := by
    ext x
    have h := (ModuleCat.CoextendScalars.equiv f M w).map_smul a x.down
    change (ModuleCat.CoextendScalars.equiv f M w) (x.down * f a) = _
    rw [mul_comm]
    exact h

/-- `Dualizing.coextendScalarsHomLinearEquiv` is natural: coextension of scalars acts on
`Hom_A(B, -)` by postcomposition. -/
theorem coextendScalarsHomLinearEquiv_naturality {M N : ModuleCat.{max v u} A} (d : M ⟶ N)
    (w : ((ModuleCat.restrictScalars.{max v u} f).obj
      ((ModuleCat.coextendScalars.{u, u, max v u} f).obj M) : Type (max v u))) :
    coextendScalarsHomLinearEquiv.{u, v} f N
        (((ModuleCat.restrictScalars.{max v u} f).map
          ((ModuleCat.coextendScalars.{u, u, max v u} f).map d)).hom w)
      = d.hom.comp (coextendScalarsHomLinearEquiv.{u, v} f M w) :=
  rfl

/-- The `A`-linear form of `CochainComplex.HomComplex.Cochain.fromSingleEquiv`: degree-`n`
cochains from a complex concentrated in degree `0` are the maps out of that module into degree
`n` of the target. -/
noncomputable def cochainFromSingleLinearEquiv (P : ModuleCat.{max v u} A)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ) :
    Cochain ((singleFunctor (ModuleCat.{max v u} A) 0).obj P) I n ≃ₗ[A]
      ((P : Type (max v u)) →ₗ[A] (I.X n : Type (max v u))) :=
  { (Cochain.fromSingleEquiv (p := 0) (q := n) (n := n) (by omega)).trans
      ModuleCat.homAddEquiv with
    map_smul' := fun a z => by
      ext x
      simp [Cochain.fromSingleEquiv, Cochain.smul_v] }

/-- The inverse of `Dualizing.cochainFromSingleLinearEquiv` is
`CochainComplex.HomComplex.Cochain.fromSingleMk`. -/
theorem cochainFromSingleLinearEquiv_symm_apply (P : ModuleCat.{max v u} A)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ)
    (h : (P : Type (max v u)) →ₗ[A] (I.X n : Type (max v u))) :
    (cochainFromSingleLinearEquiv.{u, v} P I n).symm h
      = Cochain.fromSingleMk (ModuleCat.ofHom h) (by omega : (0 : ℤ) + n = n) :=
  rfl

/-- **Degreewise coextension of scalars is the Hom complex out of the target ring.** For a
homomorphism of commutative rings `f : A →+* B` and a complex `I` of `A`-modules, the complex
`Hom_A(B, I)` of `B`-modules, read as a complex of `A`-modules by restriction of scalars, is the
Hom complex `Hom^•_A(B[0], I)`. Both have `Hom_A(B, I^n)` in degree `n`, with postcomposition
by the differential of `I` as differential; no sign appears because `B[0]` has zero
differential. -/
noncomputable def coextendComplexIsoHomComplexSingle
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    ((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((coextendComplex.{u, u, v} f).obj I) ≅
      CochainComplex.HomComplexR A
        ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (targetAsModule.{u, v} f)) I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((coextendScalarsHomLinearEquiv.{u, v} f (I.X n)).trans
      (cochainFromSingleLinearEquiv.{u, v} (targetAsModule.{u, v} f) I n).symm).toModuleIso)
    (fun i j _ => by
      ext w
      change δ i j (Cochain.fromSingleMk
            (ModuleCat.ofHom (coextendScalarsHomLinearEquiv.{u, v} f (I.X i) w))
            (by omega : (0 : ℤ) + i = i))
          = Cochain.fromSingleMk (ModuleCat.ofHom
              (coextendScalarsHomLinearEquiv.{u, v} f (I.X j)
                (((ModuleCat.restrictScalars.{max v u} f).map
                  ((ModuleCat.coextendScalars.{u, u, max v u} f).map (I.d i j))).hom w)))
            (by omega : (0 : ℤ) + j = j)
      rw [Cochain.δ_fromSingleMk _ (by omega : (0 : ℤ) + i = i) j j (by omega)]
      congr 1)

end Dualizing

end
