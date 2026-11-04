module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.CechLevelPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.MonadCobar
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SmallEtaleBaseChangeAbBridge

/-!
# A Čech level of a finite morphism computes a power of the monad `f_*f^{-1}`

Let `f : X ⟶ Y` be a finite morphism of schemes and let `f_n : cechScheme f n ⟶ Y` be the
structure map of the degree-`n` level of its Čech nerve, the `(n + 1)`-fold fibre product
`X ×_Y ⋯ ×_Y X`. On abelian sheaves of the small étale sites, `f` carries the
inverse-image/direct-image adjunction `f^{-1} ⊣ f_*` and hence the monad `T = f_*f^{-1}`; the
same for each `f_n`, with monad `Φ n = f_{n,*}f_n^{-1}`.

This file proves that `Φ n` is the `(n + 1)`-st power of `T`:

```
Φ n ≅ T^{n+1},
```

the direction chosen for the isomorphism being this one, with the power as the *target*, so that
the augmentation `F ⟶ Φ 0 F` of Stacks 09Z2 composes with it on the right.

The induction is on `n`. At `n + 1` the two factorisations `f_{n+1} = p ≫ f_n = q ≫ f` of the
structure map through the last face map `p = cechLastFace f n` and the last leg
`q = cechLastLeg f n` give, by the composition isomorphisms for direct and inverse image,
`Φ (n+1) ≅ f^{-1} ⋙ (q^{-1} ⋙ p_*) ⋙ f_{n,*}`; the one geometric input — the finite base change
theorem at the cartesian square of `Stacks.EtaleCohomology.isPullback_cechScheme_succ`, whose
comparison `f_* ⋙ f_n^{-1} ⟶ q^{-1} ⋙ p_*` is invertible — replaces the middle factor by
`f_* ⋙ f_n^{-1}`, which is to say `Φ (n+1) ≅ T ⋙ Φ n`.

At `n = 0` there is no geometry: the single leg `ℓ : cechScheme f 0 ⟶ X` of a one-fold fibre
product is an isomorphism, so `f_0 = ℓ ≫ f`, and the composition isomorphisms together with the
invertibility of the unit of the adjunction of `ℓ`
(`Stacks.EtaleCohomology.isIso_smallEtaleAdjunctionAb_unit_of_isIso`) give `Φ 0 ≅ T`.
The isomorphism is built so that it carries the unit of `f_0` to the unit of `f`: the
inverse-image composition isomorphism is by construction the conjugate, under the two
adjunctions, of the direct-image one, and `CategoryTheory.unit_conjugateEquiv` is exactly the
statement that conjugate transformations match up the units.

## Implementation notes

The invertibility of the base change comparison is available as
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_cechScheme_succ`, a statement about
`Stacks.EtaleCohomology.etaleAbelianBaseChange`, whose inverse image is the left Kan extension
construction `CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`. The functors of
this file are built from `Stacks.EtaleCohomology.smallEtalePullbackAb`, the *abstract* left
adjoint `CategoryTheory.Functor.sheafPullback`; these two are isomorphic but not definitionally
equal — only the direct images of the two developments are literally the same functor,
`Stacks.EtaleCohomology.etaleAbelianDirectImage_eq_smallEtalePushforwardAb`. The passage is
therefore made with the bridge
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange`, which
transfers invertibility from one comparison to the other.

## Main definitions

* `Stacks.EtaleCohomology.cechBaseChangeIso` — the invertible finite base change comparison at a
  Čech level, as an isomorphism of functors.
* `Stacks.EtaleCohomology.cechSheafAugIso` — `Φ 0 ≅ T`.
* `Stacks.EtaleCohomology.cechSheafIterateStepIso` — `Φ (n+1) ≅ T ⋙ Φ n`.
* `Stacks.EtaleCohomology.cechSheafIterateIso` — **`Φ n ≅ T^{n+1}`**.
* `Stacks.EtaleCohomology.cechSheafIterateObjIso` — the same isomorphism evaluated at a sheaf.

## Main results

* `Stacks.EtaleCohomology.cechSheafIterateObjIso_zero_unit` — **at `n = 0` the isomorphism
  carries the augmentation to the unit of `f`.**

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 0G5M](https://stacks.math.columbia.edu/tag/0G5M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Iterating an endofunctor once more, with the new copy taken on the *outside*:
`Z^{n+2} = Z ∘ Z^{n+1}`. `CategoryTheory.Functor.iterate` adds each new copy on the inside, so
this is `CategoryTheory.Functor.iterate_add` at `m = 1`, after `n + 1 + 1` is rewritten as
`1 + (n + 1)`. -/
public theorem functorIterate_succ_comp {C : Type*} [Category* C] (Z : C ⥤ C) (n : ℕ) :
    Z.iterate (n + 1 + 1) = Z ⋙ Z.iterate (n + 1) := by
  rw [show n + 1 + 1 = 1 + (n + 1) from by omega, Z.iterate_add]
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Finite base change at a Čech level, as an isomorphism.** For `f` finite, the base change
comparison `f_* ⋙ f_n^{-1} ⟶ (cechLastLeg f n)^{-1} ⋙ (cechLastFace f n)_*` of the cartesian
square `Stacks.EtaleCohomology.isPullback_cechScheme_succ` is invertible
([Stacks, Tag 0959]). -/
public def cechBaseChangeIso [IsFinite f] (n : ℕ) :
    smallEtalePushforwardAb f ⋙ smallEtalePullbackAb (cechProjection f n) ≅
      smallEtalePullbackAb (cechLastLeg f n) ⋙ smallEtalePushforwardAb (cechLastFace f n) :=
  haveI := isIso_smallEtaleBaseChangeAb_of_isIso_etaleAbelianBaseChange (cechProjection f n) f
    (cechLastFace f n) (cechLastLeg f n) (isPullback_cechScheme_succ f n).w
    (isIso_etaleAbelianBaseChange_cechScheme_succ f n)
  asIso (smallEtaleBaseChangeAb (cechProjection f n) f (cechLastFace f n) (cechLastLeg f n)
    (isPullback_cechScheme_succ f n).w)

/-- **One step of the induction.** The degree-`n + 1` monad of the Čech nerve is the monad of `f`
followed by the degree-`n` monad: `Φ (n+1) ≅ T ⋙ Φ n`. The two factorisations
`f_{n+1} = cechLastFace f n ≫ f_n = cechLastLeg f n ≫ f` of the structure map are fed to the
composition isomorphisms for direct and for inverse image, and the resulting middle factor
`(cechLastLeg f n)^{-1} ⋙ (cechLastFace f n)_*` is replaced by `f_* ⋙ f_n^{-1}` using the
inverse of the base change comparison `Stacks.EtaleCohomology.cechBaseChangeIso`. -/
public def cechSheafIterateStepIso [IsFinite f] (n : ℕ) :
    smallEtalePullbackAb (cechProjection f (n + 1)) ⋙
        smallEtalePushforwardAb (cechProjection f (n + 1)) ≅
      Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f) ⋙
        (smallEtalePullbackAb (cechProjection f n) ⋙
          smallEtalePushforwardAb (cechProjection f n)) :=
  Functor.isoWhiskerRight
      (smallEtalePullbackAbCompIso' (cechLastLeg f n) f (cechProjection f (n + 1))
        (cechLastLeg_comp f n).symm).symm
      (smallEtalePushforwardAb (cechProjection f (n + 1))) ≪≫
    Functor.isoWhiskerLeft
        (smallEtalePullbackAb f ⋙ smallEtalePullbackAb (cechLastLeg f n))
        (smallEtalePushforwardAbCompIso' (cechLastFace f n) (cechProjection f n)
          (cechProjection f (n + 1)) (cechLastFace_comp_cechProjection f n).symm).symm ≪≫
      Functor.isoWhiskerLeft (smallEtalePullbackAb f)
        (Functor.isoWhiskerRight (cechBaseChangeIso f n).symm
          (smallEtalePushforwardAb (cechProjection f n)))

/-- The single leg `cechScheme f 0 ⟶ X` of the degree-zero level of the Čech nerve of `f`, the
projection of a one-fold fibre product. It is an isomorphism,
`Stacks.EtaleCohomology.isIso_cechLeg_zero`, and composing it with `f` gives the structure map
`cechProjection f 0`, `Stacks.EtaleCohomology.cechLeg_zero_comp`. -/
public abbrev cechLegZero : cechScheme f 0 ⟶ X :=
  WidePullback.π (fun _ : Fin 1 => f) 0

/-- **The degree-zero level of the Čech nerve carries the monad of `f` itself**: `Φ 0 ≅ T`. The
structure map of the degree-zero level is `cechLegZero f ≫ f` with `cechLegZero f` invertible, so
the composition isomorphisms for direct and inverse image exhibit `Φ 0` as
`f^{-1} ⋙ ((cechLegZero f)^{-1} ⋙ (cechLegZero f)_*) ⋙ f_*`, whose middle factor is the
identity by `Stacks.EtaleCohomology.isIso_smallEtaleAdjunctionAb_unit_of_isIso`. -/
public def cechSheafAugIso :
    smallEtalePullbackAb (cechProjection f 0) ⋙ smallEtalePushforwardAb (cechProjection f 0) ≅
      Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f) :=
  Functor.isoWhiskerRight
      (smallEtalePullbackAbCompIso' (cechLegZero f) f (cechProjection f 0)
        (cechLeg_zero_comp f).symm).symm
      (smallEtalePushforwardAb (cechProjection f 0)) ≪≫
    Functor.isoWhiskerLeft
        (smallEtalePullbackAb f ⋙ smallEtalePullbackAb (cechLegZero f))
        (smallEtalePushforwardAbCompIso' (cechLegZero f) f (cechProjection f 0)
          (cechLeg_zero_comp f).symm).symm ≪≫
      Functor.isoWhiskerLeft (smallEtalePullbackAb f)
        (Functor.isoWhiskerRight
          (asIso (smallEtaleAdjunctionAb (cechLegZero f)).unit).symm
          (smallEtalePushforwardAb f))

/-- The three factors of `Stacks.EtaleCohomology.cechSheafAugIso` at a sheaf `F`. -/
public theorem cechSheafAugIso_hom_app (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (cechSheafAugIso f).hom.app F =
      (smallEtalePushforwardAb (cechProjection f 0)).map
          ((smallEtalePullbackAbCompIso' (cechLegZero f) f (cechProjection f 0)
            (cechLeg_zero_comp f).symm).inv.app F) ≫
        (smallEtalePushforwardAbCompIso' (cechLegZero f) f (cechProjection f 0)
            (cechLeg_zero_comp f).symm).inv.app
          ((smallEtalePullbackAb f ⋙ smallEtalePullbackAb (cechLegZero f)).obj F) ≫
          (smallEtalePushforwardAb f).map
            ((asIso (smallEtaleAdjunctionAb (cechLegZero f)).unit).inv.app
              ((smallEtalePullbackAb f).obj F)) :=
  rfl

/-- **The isomorphism `Φ 0 ≅ T` carries the augmentation to the unit of `f`**: the unit of the
adjunction of `cechProjection f 0`, followed by `Stacks.EtaleCohomology.cechSheafAugIso`, is the
unit of the adjunction of `f`. -/
public theorem cechSheafAugIso_unit (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtaleAdjunctionAb (cechProjection f 0)).unit.app F ≫ (cechSheafAugIso f).hom.app F =
      (smallEtaleAdjunctionAb f).unit.app F := by
  have hleg : (smallEtaleAdjunctionAb (cechLegZero f)).unit.app
        ((smallEtalePullbackAb f).obj F) ≫
      (asIso (smallEtaleAdjunctionAb (cechLegZero f)).unit).inv.app
        ((smallEtalePullbackAb f).obj F) = 𝟙 _ :=
    (asIso (smallEtaleAdjunctionAb (cechLegZero f)).unit).hom_inv_id_app _
  have hcancel : (smallEtalePushforwardAb f).map
        ((smallEtaleAdjunctionAb (cechLegZero f)).unit.app ((smallEtalePullbackAb f).obj F)) ≫
      (smallEtalePushforwardAb f).map
        ((asIso (smallEtaleAdjunctionAb (cechLegZero f)).unit).inv.app
          ((smallEtalePullbackAb f).obj F)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hleg, CategoryTheory.Functor.map_id]
  have hconj : conjugateEquiv
        ((smallEtaleAdjunctionAb f).comp (smallEtaleAdjunctionAb (cechLegZero f)))
        (smallEtaleAdjunctionAb (cechProjection f 0))
        (smallEtalePullbackAbCompIso' (cechLegZero f) f (cechProjection f 0)
          (cechLeg_zero_comp f).symm).inv =
      (smallEtalePushforwardAbCompIso' (cechLegZero f) f (cechProjection f 0)
        (cechLeg_zero_comp f).symm).hom := by
    rw [smallEtalePullbackAbCompIso'_def]
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have key := unit_conjugateEquiv
    ((smallEtaleAdjunctionAb f).comp (smallEtaleAdjunctionAb (cechLegZero f)))
    (smallEtaleAdjunctionAb (cechProjection f 0))
    (smallEtalePullbackAbCompIso' (cechLegZero f) f (cechProjection f 0)
      (cechLeg_zero_comp f).symm).inv F
  rw [hconj] at key
  rw [cechSheafAugIso_hom_app, ← Category.assoc, ← key, Adjunction.comp_unit_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, hcancel]
  exact Category.comp_id _

/-- **A Čech level of a finite morphism computes a power of the monad `f_*f^{-1}`.** For
`f : X ⟶ Y` finite, the monad `Φ n = f_{n,*}f_n^{-1}` of the degree-`n` level of the Čech nerve
of `f` is the `(n + 1)`-st power of the monad `T = f_*f^{-1}` of `f` itself.

The induction is `Stacks.EtaleCohomology.cechSheafAugIso` at `n = 0` and
`Stacks.EtaleCohomology.cechSheafIterateStepIso` at `n + 1`, the latter followed by the induction
hypothesis and by the identification `T ⋙ T^{n+1} = T^{n+2}` of
`Stacks.EtaleCohomology.functorIterate_succ_comp`. -/
public def cechSheafIterateIso [IsFinite f] : (n : ℕ) →
    (smallEtalePullbackAb (cechProjection f n) ⋙ smallEtalePushforwardAb (cechProjection f n) ≅
      (Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f)).iterate (n + 1))
  | 0 => cechSheafAugIso f
  | n + 1 =>
    cechSheafIterateStepIso f n ≪≫
      Functor.isoWhiskerLeft
          (Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f))
          (cechSheafIterateIso n) ≪≫
        eqToIso (functorIterate_succ_comp
          (Stacks.Cobar.mnd (smallEtalePullbackAb f) (smallEtalePushforwardAb f)) n).symm

/-- **A Čech level of a finite morphism computes a power of the monad `f_*f^{-1}`, degreewise.**
`Stacks.EtaleCohomology.cechSheafIterateIso` evaluated at an abelian sheaf `F` on the small étale
site of the base. -/
public def cechSheafIterateObjIso [IsFinite f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtalePushforwardAb (cechProjection f n)).obj
        ((smallEtalePullbackAb (cechProjection f n)).obj F) ≅
      ((Stacks.Cobar.mnd (smallEtalePullbackAb f)
        (smallEtalePushforwardAb f)).iterate (n + 1)).obj F :=
  (cechSheafIterateIso f n).app F

/-- **The augmentations agree.** At `n = 0` the isomorphism
`Stacks.EtaleCohomology.cechSheafIterateObjIso` carries the unit of the adjunction of
`cechProjection f 0` — the augmentation `F ⟶ f_{0,*}f_0^{-1}F` of Stacks 09Z2 — to the unit
`F ⟶ f_*f^{-1}F` of the adjunction of `f`. -/
public theorem cechSheafIterateObjIso_zero_unit [IsFinite f]
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtaleAdjunctionAb (cechProjection f 0)).unit.app F ≫
        (cechSheafIterateObjIso f 0 F).hom =
      (smallEtaleAdjunctionAb f).unit.app F :=
  cechSheafAugIso_unit f F

end Stacks.EtaleCohomology

end
