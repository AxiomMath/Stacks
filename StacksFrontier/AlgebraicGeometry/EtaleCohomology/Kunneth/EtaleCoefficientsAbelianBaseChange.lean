module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelianPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeTransportCompat

/-!
# The base change map for sheaves of `ℤ/mℤ̲`-modules and for abelian sheaves

Let

```
X' <-h-- Y
|f'      |e
S  <-g-- T
```

be a commutative square of schemes, `h ≫ f' = e ≫ g`, and `m` a natural number. On abelian sheaves
on the small étale sites the base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` on `D⁺` is
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`: the descent
(`Stacks.Cohomology.BaseChange.derived`) of the mate of the identification `e_*g_* ≅ h_*f'_*` of
the two composite direct images. This file builds the same map for sheaves of `ℤ/mℤ̲`-modules on
the small models of the étale sites, `derivedBaseChangePlus`, and proves that **forgetting the
module structure carries the one to the other**: the square

```
U(f'⁻¹Rg_*K) --U(bc)--> U(Rh_*e⁻¹K)
     ≅                       ≅
(f')⁻¹Rg_*U(K) --bc--> Rh_*e⁻¹U(K)
```

commutes for every `K ∈ D⁺(T_étale, ℤ/m)`, the horizontal isomorphisms being the commutation
isomorphisms of the right derived functors with `U`. In particular each is invertible exactly
when the other is (`isIso_derivedBaseChangePlus_app_iff`).

## The construction

The identification of the composite direct images of sheaves of `Λ̲`-modules is the canonical
one: the direct image along a composite `p ≫ f` is the composite of the direct images, through
the identification `baseChangeComp p f` of the underlying base change functors of the small
models (`pushforwardCompIso`, which is
`AlgebraicGeometry.RingedToposSiteHom.pushforwardToposIsoOfIso` followed by
`AlgebraicGeometry.RingedToposSiteHom.pushforwardToposCompIso`). For a square this gives
`pushforwardSquareIso : e_*g_* ≅ h_*f'_*`; the underived base change map `moduleBaseChange` is its
mate, and `derivedBaseChangePlus` is its descent to `D⁺`.

## The proof

* **The composite direct images correspond** (`pushforwardCompIso_compCompat`): on
  sections every map in sight restricts along a morphism of the small model of `X_étale`, so the
  statement is an identity between morphisms of the small model,
  `baseChangeComp_inv_app_fromEtale`, which is the naturality of the associativity isomorphism of
  fibre products in the unit of the comparison with the small model.
* **The underived maps correspond** (`moduleBaseChange_natTransCompat`), by
  `Stacks.Cohomology.BaseChange.mate_exactTransport_app`: the underlying abelian sheaf carries the
  unit and the counit of `f⁻¹ ⊣ f_*` to those on abelian sheaves (`etaleToSheaf_map_unit`,
  `etaleToSheaf_map_counit`).
* **Their descents correspond**, by `Stacks.Cohomology.BaseChange.derived_exactTransport_app`
  (through `Stacks.Cohomology.BaseChange.isIso_derived_app_iff_of_natTransCompat`), the
  underlying abelian sheaf of an injective sheaf of modules being acyclic for the direct image.

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `pushforwardCompIso` — `(p ≫ f)_* ≅ p_* ⋙ f_*` on sheaves of `Λ̲`-modules.
* `pushforwardSquareIso` — `e_* ⋙ g_* ≅ h_* ⋙ f'_*` on sheaves of `Λ̲`-modules.
* `moduleBaseChange` — the underived base change map `(f')⁻¹g_* ⟶ h_*e⁻¹`.
* `derivedBaseChangePlus` — **the base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` on `D⁺`.**

## Main results

* `pushforwardCompIso_compCompat` — the composite direct images correspond.
* `moduleBaseChange_natTransCompat` — the underived maps correspond.
* `isIso_derivedBaseChangePlus_app_iff` — **the base change maps on `D⁺` are invertible
  together.**

## Implementation notes

The direct image `smallEtalePushforwardAb` is a definition, so the composite of
`siteAbelianDirectImageIso` (stated with `etaleAbelianDirectImage`) with a map of
`smallEtalePushforwardAb` is well typed only up to unfolding it. Lemmas stated that way are not
type correct at the transparency `rw` and `simp` use, and they stall. The statements here are
phrased through `pushforwardEtaleToSheafIso` and `smallEtalePushforwardAb` throughout, and their
values on sections are read off by `rfl`. The compatibilities are stated as the named
propositions of `Stacks.Cohomology.BaseChange` (`CompCompat`, `SquareCompat`, `NatTransCompat`),
so that the kernel compares them with the hypotheses of the transport lemmas argument by
argument.

`Stacks.Cohomology.BaseChange.derived` and `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`
are built under the standard model of the derived category, which fixes the model in the derived
section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing siteSheafEquiv)
open Stacks.Cohomology.BaseChange (CompCompat SquareCompat SquareCompat.of_compCompat NatTransCompat
  NatTransCompat.mate isIso_derived_app_iff_of_natTransCompat)

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

/-! ### The composite direct images -/

section Composite

variable (Λ : Type (u + 1)) [CommRing Λ] {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S)

/-- **The identity behind the composition of direct images**, between morphisms of the small
model of `W_étale`: base change along `p ≫ f`, compared with base change along `f` then `p` on the
small models (`baseChangeComp`) and on the small étale sites (`smallEtaleBaseChangeComp`), through
the comparisons of the small models with the small étale sites. -/
theorem baseChangeComp_inv_app_fromEtale (V : S.Etale) :
    (fromEtaleCompBaseChangeIso p).inv.app ((smallEtaleBaseChange f).obj V) ≫
        (baseChange p).map ((fromEtaleCompBaseChangeIso f).inv.app V) ≫
        (baseChangeComp p f).inv.app ((fromEtale S).obj V) =
      (fromEtale W).map ((smallEtaleBaseChangeComp p f).inv.app V) ≫
        (fromEtaleCompBaseChangeIso (p ≫ f)).inv.app V := by
  simp only [fromEtaleCompBaseChangeIso, baseChangeComp, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.leftUnitor_inv_app, Iso.symm_inv, Functor.comp_obj, Functor.comp_map, Category.id_comp,
    Category.comp_id, ← Functor.map_comp]
  congr 1
  have hn := (smallEtaleBaseChangeComp p f).inv.naturality ((equiv S).unitIso.hom.app V)
  simp only [Functor.comp_map] at hn
  have h3 : (equiv X).unitIso.hom.app ((smallEtaleBaseChange f).obj V) ≫
      (toEtale X).map ((fromEtale X).map ((smallEtaleBaseChange f).map
        ((equiv S).unitIso.hom.app V))) ≫
      (equiv X).unitIso.inv.app ((smallEtaleBaseChange f).obj ((toEtale S).obj
        ((fromEtale S).obj V))) =
        (smallEtaleBaseChange f).map ((equiv S).unitIso.hom.app V) := by
    have hX := (equiv X).unitIso.hom.naturality
      ((smallEtaleBaseChange f).map ((equiv S).unitIso.hom.app V))
    dsimp at hX
    rw [← reassoc_of% hX]
    simp
  rw [← h3] at hn
  simp only [Functor.map_comp, Category.assoc] at hn
  exact hn

/-- **The direct image along a composite is the composite of the direct images**, on sheaves of
`Λ̲`-modules on the small models: `(p ≫ f)_* ≅ p_* ⋙ f_*`, through the identification
`baseChangeComp p f` of the morphism of ringed topoi of `p ≫ f` with the composite of those of
`f` and `p` (`fSharpCompatible_comp`). -/
def pushforwardCompIso :
    (ringedToposHom Λ (p ≫ f)).pushforwardTopos ≅
      (ringedToposHom Λ p).pushforwardTopos ⋙ (ringedToposHom Λ f).pushforwardTopos :=
  (RingedToposSiteHom.pushforwardToposIsoOfIso (fSharpCompatible_comp Λ p f)).symm ≪≫
    RingedToposSiteHom.pushforwardToposCompIso (ringedToposHom Λ p) (ringedToposHom Λ f)

/-- **The composite direct images correspond under the underlying abelian sheaf**: `U` carries
`pushforwardCompIso` to the composition isomorphism `smallEtalePushforwardAbCompIso` of direct
images of abelian sheaves, through `pushforwardEtaleToSheafIso`. -/
theorem pushforwardCompIso_compCompat :
    CompCompat (pushforwardEtaleToSheafIso Λ p) (pushforwardEtaleToSheafIso Λ f)
      (pushforwardEtaleToSheafIso Λ (p ≫ f)) (pushforwardCompIso Λ p f)
      (smallEtalePushforwardAbCompIso p f) := by
  intro y
  let G := (SheafOfModules.toSheaf.{u + 1} (etaleRing Λ W)).obj y
  have h₁ (V : S.Etale) :
      ((etaleToSheaf Λ S).map ((pushforwardCompIso Λ p f).hom.app y)).hom.app (op V) =
        G.obj.map ((baseChangeComp p f).inv.app ((fromEtale S).obj V)).op := rfl
  have h₂ (V : S.Etale) : ((pushforwardEtaleToSheafIso Λ f).hom.app
      ((ringedToposHom Λ p).pushforwardTopos.obj y)).hom.app (op V) =
      G.obj.map ((baseChange p).map ((fromEtaleCompBaseChangeIso f).inv.app V)).op := rfl
  have h₃ (V : S.Etale) : ((smallEtalePushforwardAb f).map
      ((pushforwardEtaleToSheafIso Λ p).hom.app y)).hom.app (op V) =
      G.obj.map ((fromEtaleCompBaseChangeIso p).inv.app ((smallEtaleBaseChange f).obj V)).op :=
    rfl
  have h₄ (V : S.Etale) : ((pushforwardEtaleToSheafIso Λ (p ≫ f)).hom.app y).hom.app (op V) =
      G.obj.map ((fromEtaleCompBaseChangeIso (p ≫ f)).inv.app V).op := rfl
  have h₅ (V : S.Etale) : ((smallEtalePushforwardAbCompIso p f).inv.app
      ((etaleToSheaf Λ W).obj y)).hom.app (op V) =
      G.obj.map ((fromEtale W).map ((smallEtaleBaseChangeComp p f).inv.app V)).op := rfl
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  induction V with | op V => ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [h₁, h₂, h₃, h₄, h₅]
  have key := congrArg (fun φ => G.obj.map φ.op) (baseChangeComp_inv_app_fromEtale p f V)
  simp only [op_comp, Functor.map_comp, Category.assoc] at key
  exact key

/-- **Base change along a morphism `c` equal to a composite `p ≫ f`**, on the small models: base
change along `f` then `p`, through `baseChangeComp p f`. -/
def baseChangeCompOfEq (c : W ⟶ S) (hc : p ≫ f = c) :
    baseChange c ≅ baseChange f ⋙ baseChange p :=
  eqToIso (congrArg baseChange hc.symm) ≪≫ baseChangeComp p f

/-- `baseChangeCompOfEq` carries the structure map of the composite morphism of ringed topoi to
that of `c`. -/
theorem fSharpCompatible_compOfEq (c : W ⟶ S) (hc : p ≫ f = c) :
    RingedToposSiteHom.FSharpCompatible ((ringedToposHom Λ f).comp (ringedToposHom Λ p))
      (ringedToposHom Λ c) (baseChangeCompOfEq p f c hc) := by
  subst hc
  simpa only [baseChangeCompOfEq, eqToIso_refl, Iso.refl_trans] using fSharpCompatible_comp Λ p f

/-- **The direct image along a morphism `c = p ≫ f` is the composite of the direct images**, on
sheaves of `Λ̲`-modules: `pushforwardCompIso` with the composite named. -/
def pushforwardCompIsoOfEq (c : W ⟶ S) (hc : p ≫ f = c) :
    (ringedToposHom Λ c).pushforwardTopos ≅
      (ringedToposHom Λ p).pushforwardTopos ⋙ (ringedToposHom Λ f).pushforwardTopos :=
  (RingedToposSiteHom.pushforwardToposIsoOfIso (fSharpCompatible_compOfEq Λ p f c hc)).symm ≪≫
    RingedToposSiteHom.pushforwardToposCompIso (ringedToposHom Λ p) (ringedToposHom Λ f)

/-- With the composite written out, `pushforwardCompIsoOfEq` is `pushforwardCompIso`. -/
theorem pushforwardCompIsoOfEq_rfl :
    pushforwardCompIsoOfEq Λ p f (p ≫ f) rfl = pushforwardCompIso Λ p f := by
  have key : ∀ {a b : (ringedToposHom Λ (p ≫ f)).u ≅
      ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).u}
      (ha : RingedToposSiteHom.FSharpCompatible _ _ a)
      (hb : RingedToposSiteHom.FSharpCompatible _ _ b), a = b →
        RingedToposSiteHom.pushforwardToposIsoOfIso ha =
          RingedToposSiteHom.pushforwardToposIsoOfIso hb := by
    rintro _ _ _ _ rfl
    rfl
  rw [pushforwardCompIsoOfEq, pushforwardCompIso,
    key (fSharpCompatible_compOfEq Λ p f (p ≫ f) rfl) (fSharpCompatible_comp Λ p f)
      (by simp [baseChangeCompOfEq]; rfl)]

/-- **`pushforwardCompIso_compCompat` with the composite named.** -/
theorem pushforwardCompIsoOfEq_compCompat (c : W ⟶ S) (hc : p ≫ f = c) :
    CompCompat (pushforwardEtaleToSheafIso Λ p) (pushforwardEtaleToSheafIso Λ f)
      (pushforwardEtaleToSheafIso Λ c) (pushforwardCompIsoOfEq Λ p f c hc)
      (smallEtalePushforwardAbCompIso p f ≪≫ eqToIso (congrArg smallEtalePushforwardAb hc)) := by
  subst hc
  rw [pushforwardCompIsoOfEq_rfl,
    show smallEtalePushforwardAbCompIso p f ≪≫ eqToIso (congrArg smallEtalePushforwardAb rfl) =
      smallEtalePushforwardAbCompIso p f by simp]
  exact pushforwardCompIso_compCompat Λ p f

end Composite

/-! ### The base change square -/

section Square

variable (Λ : Type (u + 1)) [CommRing Λ] {X' Y S T : Scheme.{u}}
  (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)

/-- **The identification `e_* ⋙ g_* ≅ h_* ⋙ f'_*` of the two composite direct images of a
commutative square**, on sheaves of `Λ̲`-modules: both are the direct image along
`e ≫ g = h ≫ f'`. -/
abbrev pushforwardSquareIso :
    (ringedToposHom Λ e).pushforwardTopos ⋙ (ringedToposHom Λ g).pushforwardTopos ≅
      (ringedToposHom Λ h).pushforwardTopos ⋙ (ringedToposHom Λ f').pushforwardTopos :=
  (pushforwardCompIsoOfEq Λ e g (h ≫ f') w.symm).symm ≪≫ pushforwardCompIso Λ h f'

/-- **`pushforwardSquareIso` is carried by the underlying abelian sheaf to the identification of
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`**, through `pushforwardEtaleToSheafIso`. -/
theorem pushforwardSquareIso_squareCompat :
    SquareCompat (pushforwardEtaleToSheafIso Λ e) (pushforwardEtaleToSheafIso Λ g)
      (pushforwardEtaleToSheafIso Λ h) (pushforwardEtaleToSheafIso Λ f')
      (pushforwardSquareIso Λ f' g h e w)
      ((smallEtalePushforwardAbCompIso e g).trans
        ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
          (smallEtalePushforwardAbCompIso h f').symm)) :=
  SquareCompat.of_compCompat (pushforwardCompIsoOfEq_compCompat Λ e g (h ≫ f') w.symm)
    (pushforwardCompIso_compCompat Λ h f')

end Square

/-! ### The underived base change map -/

section BaseChange

variable (Λ : Type (u + 1)) [CommRing Λ] {X' Y S T : Scheme.{u}}
  (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)

/-- **The underived base change map `(f')⁻¹g_* ⟶ h_*e⁻¹`** on sheaves of `Λ̲`-modules of a
commutative square: the mate of the identification `pushforwardSquareIso` of the two composite
direct images under the adjunctions `(f')⁻¹ ⊣ f'_*` and `e⁻¹ ⊣ e_*`. -/
def moduleBaseChange :
    (ringedToposHom Λ g).pushforwardTopos ⋙ (ringedToposHom Λ f').pullbackTopos ⟶
      (ringedToposHom Λ e).pullbackTopos ⋙ (ringedToposHom Λ h).pushforwardTopos :=
  Stacks.Cohomology.BaseChange.mate (ringedToposHom Λ f').pullbackPushforwardAdjunctionTopos
    (ringedToposHom Λ e).pullbackPushforwardAdjunctionTopos (ringedToposHom Λ g).pushforwardTopos
    (ringedToposHom Λ h).pushforwardTopos (pushforwardSquareIso Λ f' g h e w)

variable (m : ℕ)

/-- **The underived base change maps correspond under the underlying abelian sheaf**, for
`ℤ/mℤ`-coefficients: `U` carries `moduleBaseChange` to
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, through the commutation isomorphisms of the
direct and inverse images with `U`. -/
theorem moduleBaseChange_natTransCompat :
    NatTransCompat (pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod m)) g)
      (pushforwardEtaleToSheafIso (ULift.{u + 1} (ZMod m)) h) (pullbackEtaleToSheafIso m f')
      (pullbackEtaleToSheafIso m e) (moduleBaseChange (ULift.{u + 1} (ZMod m)) f' g h e w)
      (smallEtaleBaseChangeAb f' g h e w) :=
  NatTransCompat.mate _ _ (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e)
    (etaleToSheaf_map_counit m f') (etaleToSheaf_map_unit m e)
    (pushforwardSquareIso_squareCompat _ f' g h e w)

end BaseChange

/-! ### The base change map on bounded below objects -/

section Derived

-- `Stacks.Cohomology.BaseChange.derived`
-- (`StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap`) and
-- `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`
-- (`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition`) are
-- built under the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (Λ : Type (u + 1)) [CommRing Λ] {X' Y S T : Scheme.{u}}
  (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)

/-- The inverse image of sheaves of `Λ̲`-modules is additive, being a left adjoint. -/
instance additive_pullbackTopos_ringedToposHom {Z Z' : Scheme.{u}} (k : Z ⟶ Z') :
    (ringedToposHom Λ k).pullbackTopos.Additive :=
  Adjunction.left_adjoint_additive (ringedToposHom Λ k).pullbackPushforwardAdjunctionTopos

/-- **The base change map `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` on `D⁺`** for sheaves of `Λ̲`-modules: the
descent `Stacks.Cohomology.BaseChange.derived` of `moduleBaseChange`, the inverse images being
exact. -/
def derivedBaseChangePlus :
    (ringedToposHom Λ g).pushforwardTopos.rightDerivedFunctorPlus ⋙
        (ringedToposHom Λ f').pullbackTopos.rightDerivedFunctorPlus ⟶
      (ringedToposHom Λ e).pullbackTopos.rightDerivedFunctorPlus ⋙
        (ringedToposHom Λ h).pushforwardTopos.rightDerivedFunctorPlus :=
  Stacks.Cohomology.BaseChange.derived (ringedToposHom Λ g).pushforwardTopos
    (ringedToposHom Λ h).pushforwardTopos (ringedToposHom Λ f').pullbackTopos
    (ringedToposHom Λ e).pullbackTopos (moduleBaseChange Λ f' g h e w)
    (asIso (ringedToposHom Λ f').pullbackTopos.rightDerivedFunctorPlusUnith)

variable (m : ℕ)

/-- The underlying complex of abelian sheaves reflects isomorphisms in `D⁺(X_étale, Λ)`. -/
instance reflectsIsomorphisms_etaleToSheaf_mapDerivedCategoryPlus (Z : Scheme.{u}) :
    (etaleToSheaf Λ Z).mapDerivedCategoryPlus.ReflectsIsomorphisms where
  reflects {A B} φ _ := by
    have h₁ : IsIso ((forgetDerived Λ Z).map (DerivedCategory.Plus.ι.map φ)) :=
      inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
        ((etaleToSheaf Λ Z).mapDerivedCategoryPlus.map φ)))
    have := (isIso_iff_isIso_forgetDerived_map Λ Z _).2 h₁
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

/-- **The base change maps on `D⁺` are invertible together**: for `K ∈ D⁺(T_étale, ℤ/m)` the base
change map `derivedBaseChangePlus` of sheaves of `ℤ/mℤ̲`-modules is invertible at `K` exactly
when the abelian base change map `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` is
invertible at the underlying complex of abelian sheaves of `K`. The underlying abelian sheaf
carries the one to the other (`moduleBaseChange_natTransCompat`,
`Stacks.Cohomology.BaseChange.derived_exactTransport_app`), and it reflects isomorphisms. -/
theorem isIso_derivedBaseChangePlus_app_iff
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso ((derivedBaseChangePlus (ULift.{u + 1} (ZMod m)) f' g h e w).app K) ↔
      IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
        ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K)) :=
  isIso_derived_app_iff_of_natTransCompat (hτ := moduleBaseChange_natTransCompat f' g h e w m)
    (hF := rightAcyclic_smallEtalePushforwardAb_etaleToSheaf _ g)
    (hF' := rightAcyclic_smallEtalePushforwardAb_etaleToSheaf _ h)
    (hG := fun _ _ => (smallEtalePullbackAb f').rightAcyclic_of_exact _)
    (hG' := fun _ _ => (smallEtalePullbackAb e).rightAcyclic_of_exact _) (M := K)

end Derived

end Stacks.EtaleCohomology.EtaleCoefficients

end
