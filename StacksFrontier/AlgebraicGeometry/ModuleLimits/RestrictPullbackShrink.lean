module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSquarePaste
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictLEPullback
/-!
# Shrinking the two opens of `restrictPullbackIso`, and composing

`Stacks.Modules.restrictPullbackIso` identifies, for `V ≤ f ⁻¹ᵁ U`, the restriction to `V` of a
pullback along `f` with the pullback along `f|_V : V ⟶ U` of the restriction to `U`.  It therefore
carries a morphism `ξ : M|_U ⟶ N|_U` to a morphism `(f^*M)|_V ⟶ (f^*N)|_V`, the *conjugate*
`pullbackHomOfRestrict f e ξ`.

This file proves that this conjugation is compatible with the three ways the data can be moved.

* **(B1)** shrinking `V`: restricting `pullbackHomOfRestrict f e ξ` to a smaller `V' ≤ V` is the
  conjugate of the *same* `ξ` for the smaller open.
* **(B2)** shrinking `U`: conjugating the restriction of `ξ` to a smaller `U' ≤ U` gives the
  conjugate of `ξ` itself.
* **(B)** the two together: shrinking the source open and shrinking the target open give the same
  morphism.  The two halves compose freely, because `V' ≤ f ⁻¹ᵁ U` is a `Prop` and the two routes
  produce two proofs of it.
* **(C)** composition: conjugating along `f` and then along `g` is conjugating along `f ≫ g`, up to
  the canonical identification `Stacks.AlgebraicGeometry.ModuleLimits.canHom` of the iterated
  pullback with the pullback of the composite.

## The route

Each statement is an equality of two conjugations, so by
`Stacks.AlgebraicGeometry.ModuleLimits.conj_shrink_target`,
`Stacks.AlgebraicGeometry.ModuleLimits.conj_shrink_source` and
`Stacks.AlgebraicGeometry.ModuleLimits.conj_comp` it reduces to a commuting square of the
comparison isomorphisms with `ξ` eliminated — the three `restrictPullbackIso_hom_*` lemmas below.
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq` is what puts the sectionwise
`restrictHomOfLE` into conjugated form, and
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso_hom_restrictFunctorIsoPullback_hom` is what
puts the comparison it conjugates by onto the pullback side.

With those two bridges in hand every `restrictFunctor`-side comparison in the square becomes a
pullback-side one and every `restrictFunctorIsoPullback` factor cancels by naturality, leaving a
statement about `canHom` alone: `Stacks.AlgebraicGeometry.ModuleLimits.canHom_paste_target` for
(B1), a single `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp` for (B2), and
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_paste_comp` for (C).

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.pullbackHomOfRestrict`: the conjugate of
  `ξ : M|_U ⟶ N|_U` by `Stacks.Modules.restrictPullbackIso`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_pullbackHomOfRestrict`: **(B1)**.
* `Stacks.AlgebraicGeometry.ModuleLimits.pullbackHomOfRestrict_restrictHomOfLE`: **(B2)**.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_pullbackHomOfRestrict_comm`: **(B)**.
* `Stacks.AlgebraicGeometry.ModuleLimits.pullbackHomOfRestrict_comp`: **(C)**.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-! ### `restrictPullbackIso` and `restrictLEIso` at a module, on the pullback side -/

/-- `Stacks.Modules.restrictPullbackIso` at a single module, with its two pullback comparisons
collected into `Stacks.AlgebraicGeometry.ModuleLimits.canHom` and
`Stacks.AlgebraicGeometry.ModuleLimits.canNatIso`.

This is the form in which the coherence of the pullback pseudofunctor applies to it. -/
theorem restrictPullbackIso_hom_app (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (M : Y.Modules) :
    (Stacks.Modules.restrictPullbackIso f e).hom.app M =
      (restrictFunctorIsoPullback V.ι).hom.app ((pullback f).obj M) ≫
        canHom V.ι f (V.ι ≫ f) rfl M ≫
          (canNatIso (f.resLE U V e) U.ι (V.ι ≫ f) (Scheme.Hom.resLE_comp_ι f e)).inv.app M ≫
            (pullback (f.resLE U V e)).map ((restrictFunctorIsoPullback U.ι).inv.app M) := by
  simp only [Stacks.Modules.restrictPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc, canHom, canNatIso,
    Iso.trans_inv, pullbackCongr_rfl_hom_app, Category.id_comp]
  rfl

/-- `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso_hom_restrictFunctorIsoPullback_hom` at a
single module, with the pullback comparison collected into
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`. -/
theorem restrictLEIso_hom_app_canHom {W : Scheme.{u}} {V V' : W.Opens} (e : V' ≤ V)
    (P : W.Modules) :
    (restrictLEIso e).hom.app P ≫ (restrictFunctorIsoPullback V'.ι).hom.app P =
      (restrictFunctor (W.homOfLE e)).map ((restrictFunctorIsoPullback V.ι).hom.app P) ≫
        (restrictFunctorIsoPullback (W.homOfLE e)).hom.app ((pullback V.ι).obj P) ≫
          canHom (W.homOfLE e) V.ι V'.ι (W.homOfLE_ι e) P := by
  have h := NatTrans.congr_app (restrictLEIso_hom_restrictFunctorIsoPullback_hom e) P
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, canHom] using h

/-! ### The conjugate of a morphism of restrictions -/

/-- **The pullback of a morphism of restrictions, restricted.**  For `V ≤ f ⁻¹ᵁ U` and
`ξ : M|_U ⟶ N|_U`, the conjugate of the pullback of `ξ` along `f|_V : V ⟶ U` by
`Stacks.Modules.restrictPullbackIso`; a morphism `(f^*M)|_V ⟶ (f^*N)|_V`. -/
noncomputable def pullbackHomOfRestrict (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) {M N : Y.Modules}
    (ξ : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    (restrictFunctor V.ι).obj ((pullback f).obj M) ⟶
      (restrictFunctor V.ι).obj ((pullback f).obj N) :=
  (Stacks.Modules.restrictPullbackIso f e).hom.app M ≫
    (pullback (f.resLE U V e)).map ξ ≫ (Stacks.Modules.restrictPullbackIso f e).inv.app N

/-! ### (B1): shrinking the open of the source -/

/-- **The square of comparisons for shrinking `V`.**  Restricting
`Stacks.Modules.restrictPullbackIso f e` to a smaller `V' ≤ V` and then identifying the iterated
pullback is `Stacks.Modules.restrictPullbackIso f e2` for the smaller open.

This is the hypothesis of `Stacks.AlgebraicGeometry.ModuleLimits.conj_shrink_target` for (B1).
After the two bridges are applied and the `restrictFunctorIsoPullback` factors cancel by
naturality, what is left is `canHom_paste_target` for the two squares
`V.ι ≫ f = f.resLE U V e ≫ U.ι` and its shrinking along `X.homOfLE hV`. -/
theorem restrictPullbackIso_hom_shrink_target (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}
    (hV : V' ≤ V) (e : V ≤ f ⁻¹ᵁ U) (e2 : V' ≤ f ⁻¹ᵁ U) (P : Y.Modules) :
    (restrictLEIso hV).inv.app ((pullback f).obj P) ≫
        (restrictFunctor (X.homOfLE hV)).map
          ((Stacks.Modules.restrictPullbackIso f e).hom.app P) ≫
        (pullbackShrinkIso (X.homOfLE hV) (f.resLE U V e) (f.resLE U V' e2)
          (Scheme.Hom.map_resLE f e hV)).hom.app ((restrictFunctor U.ι).obj P) =
      (Stacks.Modules.restrictPullbackIso f e2).hom.app P := by
  have hnatc := (canNatIso (X.homOfLE hV) (f.resLE U V e) (f.resLE U V' e2)
    (Scheme.Hom.map_resLE f e hV)).hom.naturality
      ((restrictFunctorIsoPullback U.ι).inv.app P)
  dsimp only [Functor.comp_map] at hnatc
  simp only [canNatIso_hom_app] at hnatc
  have core : (pullback (X.homOfLE hV)).map (canHom V.ι f (V.ι ≫ f) rfl P) ≫
      (pullback (X.homOfLE hV)).map
        ((canNatIso (f.resLE U V e) U.ι (V.ι ≫ f) (Scheme.Hom.resLE_comp_ι f e)).inv.app P) ≫
      (pullback (X.homOfLE hV)).map ((pullback (f.resLE U V e)).map
        ((restrictFunctorIsoPullback U.ι).inv.app P)) ≫
      canHom (X.homOfLE hV) (f.resLE U V e) (f.resLE U V' e2)
        (Scheme.Hom.map_resLE f e hV) ((restrictFunctor U.ι).obj P) =
      canHom (X.homOfLE hV) V.ι V'.ι (X.homOfLE_ι hV) ((pullback f).obj P) ≫
        canHom V'.ι f (V'.ι ≫ f) rfl P ≫
          (canNatIso (f.resLE U V' e2) U.ι (V'.ι ≫ f)
            (Scheme.Hom.resLE_comp_ι f e2)).inv.app P ≫
            (pullback (f.resLE U V' e2)).map
              ((restrictFunctorIsoPullback U.ι).inv.app P) := by
    rw [hnatc, reassoc_of% (canHom_paste_target f U.ι V.ι V'.ι (X.homOfLE hV)
      (f.resLE U V e) (f.resLE U V' e2) (X.homOfLE_ι hV)
      (Scheme.Hom.map_resLE f e hV) (Scheme.Hom.resLE_comp_ι f e)
      (Scheme.Hom.resLE_comp_ι f e2) P)]
  have hnatBig := (restrictFunctorIsoPullback (X.homOfLE hV)).hom.naturality
    ((Stacks.Modules.restrictPullbackIso f e).hom.app P)
  have hnatV := (restrictFunctorIsoPullback (X.homOfLE hV)).hom.naturality
    ((restrictFunctorIsoPullback V.ι).hom.app ((pullback f).obj P))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnatBig hnatV
  rw [← cancel_epi ((restrictLEIso hV).hom.app ((pullback f).obj P)),
    Iso.hom_inv_id_app_assoc, restrictPullbackIso_hom_app f e2 P,
    reassoc_of% (restrictLEIso_hom_app_canHom hV ((pullback f).obj P)),
    pullbackShrinkIso_hom_app, reassoc_of% hnatBig, restrictPullbackIso_hom_app f e P]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnatV, core]

/-- **(B1): `pullbackHomOfRestrict` is compatible with shrinking the open of the source.**
Restricting the conjugate of `ξ` to a smaller open `V' ≤ V` is the conjugate of `ξ` for `V'`. -/
theorem restrictHomOfLE_pullbackHomOfRestrict (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}
    (hV : V' ≤ V) (e : V ≤ f ⁻¹ᵁ U) (e2 : V' ≤ f ⁻¹ᵁ U) {M N : Y.Modules}
    (ξ : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    restrictHomOfLE hV (pullbackHomOfRestrict f e ξ) = pullbackHomOfRestrict f e2 ξ := by
  rw [restrictHomOfLE_eq]
  simp only [pullbackHomOfRestrict]
  exact conj_shrink_target (restrictFunctor U.ι) (pullback (f.resLE U V e))
    (pullback (f.resLE U V' e2)) (restrictFunctor (X.homOfLE hV))
    (Stacks.Modules.restrictPullbackIso f e) (Stacks.Modules.restrictPullbackIso f e2)
    (Functor.isoWhiskerLeft (pullback f) (restrictLEIso hV))
    (pullbackShrinkIso (X.homOfLE hV) (f.resLE U V e) (f.resLE U V' e2)
      (Scheme.Hom.map_resLE f e hV))
    (fun P => restrictPullbackIso_hom_shrink_target f hV e e2 P) ξ

/-! ### (B2): shrinking the open of the target -/

/-- **The square of comparisons for shrinking `U`.**  `Stacks.Modules.restrictPullbackIso f e'`
for the smaller open `U' ≤ U` is `Stacks.Modules.restrictPullbackIso f e2` followed by the
comparison that pulls a restriction to `U'` back along `f|_V : V ⟶ U'`.

This is the hypothesis of `Stacks.AlgebraicGeometry.ModuleLimits.conj_shrink_source` for (B2).
Here the pure-pullback residue is a single `canHom_comp`, for the three morphisms
`f.resLE U' V e'`, `Y.homOfLE hU` and `U.ι`. -/
theorem restrictPullbackIso_hom_shrink_source (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}
    (hU : U' ≤ U) (e' : V ≤ f ⁻¹ᵁ U') (e2 : V ≤ f ⁻¹ᵁ U) (P : Y.Modules) :
    (Stacks.Modules.restrictPullbackIso f e').hom.app P =
      (Stacks.Modules.restrictPullbackIso f e2).hom.app P ≫
        (pullbackShrinkSourceIso (Y.homOfLE hU) (f.resLE U' V e') (f.resLE U V e2)
          (Scheme.Hom.resLE_map f e' hU)).inv.app ((restrictFunctor U.ι).obj P) ≫
        (pullback (f.resLE U' V e')).map ((restrictLEIso hU).hom.app P) := by
  have pent := canHom_comp (f.resLE U' V e') (Y.homOfLE hU) U.ι (f.resLE U V e2)
    (Scheme.Hom.resLE_map f e' hU) U'.ι (Y.homOfLE_ι hU) (V.ι ≫ f)
    (Scheme.Hom.resLE_comp_ι f e2) (Scheme.Hom.resLE_comp_ι f e') P
  simp only [← canNatIso_hom_app] at pent
  have pinv : (canNatIso (f.resLE U' V e') U'.ι (V.ι ≫ f)
        (Scheme.Hom.resLE_comp_ι f e')).inv.app P =
      (canNatIso (f.resLE U V e2) U.ι (V.ι ≫ f) (Scheme.Hom.resLE_comp_ι f e2)).inv.app P ≫
        (canNatIso (f.resLE U' V e') (Y.homOfLE hU) (f.resLE U V e2)
          (Scheme.Hom.resLE_map f e' hU)).inv.app ((pullback U.ι).obj P) ≫
        (pullback (f.resLE U' V e')).map
          ((canNatIso (Y.homOfLE hU) U.ι U'.ι (Y.homOfLE_ι hU)).hom.app P) := by
    rw [← cancel_epi ((canNatIso (f.resLE U V e2) U.ι (V.ι ≫ f)
        (Scheme.Hom.resLE_comp_ι f e2)).hom.app P), Iso.hom_inv_id_app_assoc,
      ← cancel_epi ((canNatIso (f.resLE U' V e') (Y.homOfLE hU) (f.resLE U V e2)
        (Scheme.Hom.resLE_map f e' hU)).hom.app ((pullback U.ι).obj P)),
      Iso.hom_inv_id_app_assoc, ← reassoc_of% pent]
    simp
  have eH : (restrictFunctor (Y.homOfLE hU)).map ((restrictFunctorIsoPullback U.ι).inv.app P) ≫
      (restrictFunctor (Y.homOfLE hU)).map ((restrictFunctorIsoPullback U.ι).hom.app P) =
      𝟙 _ := by
    simp
  have hbr := restrictLEIso_hom_app_canHom hU P
  rw [← canNatIso_hom_app] at hbr
  have hbrA : (restrictLEIso hU).hom.app P =
      (restrictFunctor (Y.homOfLE hU)).map ((restrictFunctorIsoPullback U.ι).hom.app P) ≫
        (restrictFunctorIsoPullback (Y.homOfLE hU)).hom.app ((pullback U.ι).obj P) ≫
          (canNatIso (Y.homOfLE hU) U.ι U'.ι (Y.homOfLE_ι hU)).hom.app P ≫
            (restrictFunctorIsoPullback U'.ι).inv.app P := by
    rw [← reassoc_of% hbr, Iso.hom_inv_id_app]
    simp
  have hbr2 : (restrictFunctorIsoPullback (Y.homOfLE hU)).inv.app ((pullback U.ι).obj P) ≫
      (restrictFunctor (Y.homOfLE hU)).map ((restrictFunctorIsoPullback U.ι).inv.app P) ≫
      (restrictLEIso hU).hom.app P =
      (canNatIso (Y.homOfLE hU) U.ι U'.ι (Y.homOfLE_ι hU)).hom.app P ≫
        (restrictFunctorIsoPullback U'.ι).inv.app P := by
    rw [hbrA, reassoc_of% eH, Iso.inv_hom_id_app_assoc]
  have hnatcw := (canNatIso (f.resLE U' V e') (Y.homOfLE hU) (f.resLE U V e2)
    (Scheme.Hom.resLE_map f e' hU)).inv.naturality
      ((restrictFunctorIsoPullback U.ι).inv.app P)
  dsimp only [Functor.comp_map] at hnatcw
  have hnatw := (restrictFunctorIsoPullback (Y.homOfLE hU)).inv.naturality
    ((restrictFunctorIsoPullback U.ι).inv.app P)
  have core : (canNatIso (f.resLE U' V e') U'.ι (V.ι ≫ f)
        (Scheme.Hom.resLE_comp_ι f e')).inv.app P ≫
      (pullback (f.resLE U' V e')).map ((restrictFunctorIsoPullback U'.ι).inv.app P) =
      (canNatIso (f.resLE U V e2) U.ι (V.ι ≫ f) (Scheme.Hom.resLE_comp_ι f e2)).inv.app P ≫
        (pullback (f.resLE U V e2)).map ((restrictFunctorIsoPullback U.ι).inv.app P) ≫
          (canNatIso (f.resLE U' V e') (Y.homOfLE hU) (f.resLE U V e2)
            (Scheme.Hom.resLE_map f e' hU)).inv.app ((restrictFunctor U.ι).obj P) ≫
            (pullback (f.resLE U' V e')).map
              ((restrictFunctorIsoPullback (Y.homOfLE hU)).inv.app
                ((restrictFunctor U.ι).obj P)) ≫
              (pullback (f.resLE U' V e')).map ((restrictLEIso hU).hom.app P) := by
    rw [pinv, reassoc_of% hnatcw]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
    rw [reassoc_of% hnatw, hbr2]
  rw [restrictPullbackIso_hom_app f e' P, restrictPullbackIso_hom_app f e2 P,
    pullbackShrinkSourceIso_inv_app]
  simp only [Category.assoc]
  rw [core]

/-- **(B2): `pullbackHomOfRestrict` is compatible with shrinking the open of the target.**
Conjugating the restriction of `ξ` to a smaller open `U' ≤ U` gives the conjugate of `ξ`
itself. -/
theorem pullbackHomOfRestrict_restrictHomOfLE (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}
    (hU : U' ≤ U) (e' : V ≤ f ⁻¹ᵁ U') (e2 : V ≤ f ⁻¹ᵁ U) {M N : Y.Modules}
    (ξ : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    pullbackHomOfRestrict f e' (restrictHomOfLE hU ξ) = pullbackHomOfRestrict f e2 ξ := by
  rw [restrictHomOfLE_eq]
  simp only [pullbackHomOfRestrict]
  exact conj_shrink_source (restrictFunctor U.ι) (restrictFunctor U'.ι)
    (restrictFunctor (Y.homOfLE hU)) (pullback (f.resLE U V e2))
    (pullback (f.resLE U' V e'))
    (Stacks.Modules.restrictPullbackIso f e2) (Stacks.Modules.restrictPullbackIso f e')
    (restrictLEIso hU)
    (pullbackShrinkSourceIso (Y.homOfLE hU) (f.resLE U' V e') (f.resLE U V e2)
      (Scheme.Hom.resLE_map f e' hU))
    (fun P => restrictPullbackIso_hom_shrink_source f hU e' e2 P) ξ

/-! ### (B): shrinking both opens -/

/-- **(B): `pullbackHomOfRestrict` is compatible with shrinking both opens.**  Restricting the
conjugate of `ξ` to `V' ≤ V` is the conjugate, for the smaller pair, of the restriction of `ξ` to
`U' ≤ U`.

The two halves compose with no further computation: `hV.trans e` and `e'` are both proofs that
`V' ≤ f ⁻¹ᵁ U` and `V' ≤ f ⁻¹ᵁ U'`, and (B1) and (B2) are stated with the proof as a parameter. -/
theorem restrictHomOfLE_pullbackHomOfRestrict_comm (f : X ⟶ Y) {U U' : Y.Opens}
    {V V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')
    {M N : Y.Modules} (ξ : (restrictFunctor U.ι).obj M ⟶ (restrictFunctor U.ι).obj N) :
    restrictHomOfLE hV (pullbackHomOfRestrict f e ξ) =
      pullbackHomOfRestrict f e' (restrictHomOfLE hU ξ) :=
  (restrictHomOfLE_pullbackHomOfRestrict f hV e (hV.trans e) ξ).trans
    (pullbackHomOfRestrict_restrictHomOfLE f hU e' (hV.trans e) ξ).symm

/-! ### (C): composition -/

/-- **The square of comparisons for a composition.**  `Stacks.Modules.restrictPullbackIso f eV`
followed by the pullback of `Stacks.Modules.restrictPullbackIso g eU` and the canonical
identification of the iterated pullback along the restricted morphisms is
`Stacks.Modules.restrictPullbackIso (f ≫ g) e`, up to the canonical identification of
`pullback g ⋙ pullback f` with `pullback (f ≫ g)`.

This is the hypothesis of `Stacks.AlgebraicGeometry.ModuleLimits.conj_comp` for (C); the
pure-pullback residue is `canHom_paste_comp`. -/
theorem restrictPullbackIso_hom_comp (f : X ⟶ Y) (g : Y ⟶ Z) {W : Z.Opens} {U : Y.Opens}
    {V : X.Opens} (eU : U ≤ g ⁻¹ᵁ W) (eV : V ≤ f ⁻¹ᵁ U) (e : V ≤ (f ≫ g) ⁻¹ᵁ W)
    (P : Z.Modules) :
    (Stacks.Modules.restrictPullbackIso f eV).hom.app ((pullback g).obj P) ≫
        (pullback (f.resLE U V eV)).map
          ((Stacks.Modules.restrictPullbackIso g eU).hom.app P) ≫
        canHom (f.resLE U V eV) (g.resLE W U eU) ((f ≫ g).resLE W V e)
          (Scheme.Hom.resLE_comp_resLE f eV g eU) ((restrictFunctor W.ι).obj P) =
      (restrictFunctor V.ι).map (canHom f g (f ≫ g) rfl P) ≫
        (Stacks.Modules.restrictPullbackIso (f ≫ g) e).hom.app P := by
  have eU2 : (pullback (f.resLE U V eV)).map
        ((restrictFunctorIsoPullback U.ι).inv.app ((pullback g).obj P)) ≫
      (pullback (f.resLE U V eV)).map
        ((restrictFunctorIsoPullback U.ι).hom.app ((pullback g).obj P)) = 𝟙 _ := by
    simp
  have hnatXi := (canNatIso (f.resLE U V eV) (g.resLE W U eU) ((f ≫ g).resLE W V e)
    (Scheme.Hom.resLE_comp_resLE f eV g eU)).hom.naturality
      ((restrictFunctorIsoPullback W.ι).inv.app P)
  dsimp only [Functor.comp_map] at hnatXi
  simp only [canNatIso_hom_app] at hnatXi
  have hnatV := (restrictFunctorIsoPullback V.ι).hom.naturality
    ((canNatIso f g (f ≫ g) rfl).hom.app P)
  dsimp only [Functor.comp_obj] at hnatV
  simp only [canNatIso_hom_app] at hnatV
  rw [restrictPullbackIso_hom_app f eV ((pullback g).obj P),
    restrictPullbackIso_hom_app g eU P, restrictPullbackIso_hom_app (f ≫ g) e P]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [reassoc_of% eU2, hnatXi, reassoc_of% hnatV,
    reassoc_of% (canHom_paste_comp f g V.ι U.ι W.ι (f.resLE U V eV) (g.resLE W U eU)
      ((f ≫ g).resLE W V e) (Scheme.Hom.resLE_comp_ι f eV) (Scheme.Hom.resLE_comp_ι g eU)
      (Scheme.Hom.resLE_comp_ι (f ≫ g) e) (Scheme.Hom.resLE_comp_resLE f eV g eU) P)]

/-- **(C): `pullbackHomOfRestrict` is compatible with composition.**  Conjugating `ξ` along `g`
and then along `f` is conjugating it along `f ≫ g`, read through the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` of the iterated pullback with the pullback of the
composite. -/
theorem pullbackHomOfRestrict_comp (f : X ⟶ Y) (g : Y ⟶ Z) {W : Z.Opens} {U : Y.Opens}
    {V : X.Opens} (eU : U ≤ g ⁻¹ᵁ W) (eV : V ≤ f ⁻¹ᵁ U) (e : V ≤ (f ≫ g) ⁻¹ᵁ W)
    {M N : Z.Modules} (ξ : (restrictFunctor W.ι).obj M ⟶ (restrictFunctor W.ι).obj N) :
    pullbackHomOfRestrict f eV (pullbackHomOfRestrict g eU ξ) ≫
        (restrictFunctor V.ι).map (canHom f g (f ≫ g) rfl N) =
      (restrictFunctor V.ι).map (canHom f g (f ≫ g) rfl M) ≫
        pullbackHomOfRestrict (f ≫ g) e ξ := by
  simp only [pullbackHomOfRestrict]
  exact conj_comp (pullback g) (pullback f) (restrictFunctor W.ι) (restrictFunctor V.ι)
    (pullback (g.resLE W U eU)) (pullback (f.resLE U V eV))
    (pullback ((f ≫ g).resLE W V e))
    (Stacks.Modules.restrictPullbackIso g eU) (Stacks.Modules.restrictPullbackIso f eV)
    (Stacks.Modules.restrictPullbackIso (f ≫ g) e) (canNatIso f g (f ≫ g) rfl)
    (canNatIso (f.resLE U V eV) (g.resLE W U eU) ((f ≫ g).resLE W V e)
      (Scheme.Hom.resLE_comp_resLE f eV g eU))
    (fun P => restrictPullbackIso_hom_comp f g eU eV e P) ξ

end Stacks.AlgebraicGeometry.ModuleLimits

end
