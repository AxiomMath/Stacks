module

public import StacksFrontier.Homology.Tor.IndependenceBaseChange
import all StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# Equations for the derived base-change comparison

Let `R → A` and `R → R'` be homomorphisms of commutative rings, let `A → A'` and `R' → A'`
complete the square, and let `K` be a complex of `A`-modules. Tag 065Z provides the canonical
comparison `K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'` as
`RingTheory.TorIndependence.derivedBaseChangeComparison`, and Tag 0661 says it is invertible
when `A` and `R'` are Tor independent over `R`. Invertibility is all that was recorded about it,
which makes every isomorphism built from it opaque to a diagram chase. This file records the
equations the comparison satisfies.

## Main results

* `RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_tmul`: the underived
  comparison sends `r' ⊗ m` to `i r' ⊗ m`.
* `RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_eq_unit_comp_counit`: the
  underived comparison **built from a unit and a counit**: the unit of extension of scalars
  along `R' → A'` at `R' ⊗_R M`, then a merge of the two extensions of scalars, then extension
  of scalars along `A → A'` of the counit of extension of scalars along `R → A` at `M`, is the
  comparison.
* `derivedBaseChangeComparison_fst_app_eq_unit_comp_counit_extendScalarsComp`: the same with
  the merge taken canonically, from `ModuleCat.extendScalarsComp` at both ends and the transport
  along the square. This needs the four rings in one universe, which the general statement does
  not have and the local rings of a cartesian square of schemes do.
* `RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_comp_counit`: the
  compatibility of the derived comparison with the two counits of derived extension of scalars,
  at an object. This is the defining equation: the comparison is the derived lift of the
  underived one, so composing it with the counit of derived extension of scalars along `A → A'`
  and restricting gives the counit along `R → R'` followed by the underived comparison.
* `RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_eq`: the comparison is
  *computed* at every object at which the counit along `A → A'` is invertible — in particular at
  every K-flat complex — by solving the previous equation.
* `RingTheory.TorIndependence.derivedBaseChangeComparison_snd_eq`: the comparison is the unique
  transformation satisfying that equation at K-flat complexes.

## Implementation notes

The two components of `derivedBaseChangeComparison` are reached by `Sigma'`/subtype projections:
`.1` is the underived comparison, `.2.1` the derived one, and `.2.2.1`, `.2.2.2` are their
characterizing properties. The definition itself carries `@[no_expose]`, so those projections
are the only handle on it; the point of this file is that they are enough. The whiskered form
`.2.2.2` is an equation between natural transformations whose two sides are built from
associators and whiskerings of the comparison maps `alpha_g`, `alpha_h` and the factorizations
of `Functor.mapDerivedCategory`; evaluating at an object and discharging the coherence
isomorphisms — the two `Functor.mapHomologicalComplexCompIso (Iso.refl _)` are identities — turns
it into the square recorded here. That reduction was being redone inline by each of the two
existing consumers.

Additivity of extension of scalars along a bare ring homomorphism is the `private`
`extendScalarsAdditive` of `StacksFrontier.Homology.Tor.IndependenceBaseChange`, reached by
`import all` so that the statements here use the same instance as
`derivedBaseChangeComparison`'s own signature rather than a second copy of it. The two
`Functor.IsLeftAdjoint` hypotheses are what the module universe `max v uR uA uRp uAp` needs in
order for the two extension functors to be seen as additive at that universe; they are discharged
by `ModuleCat.extendRestrictScalarsAdj`.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open scoped TensorProduct ChangeOfRings

namespace RingTheory.TorIndependence

universe uR uA uRp uAp v

attribute [local instance] extendScalarsAdditive
attribute [local instance_reducible] CochainComplex.extendScalarsLarge

/-- Two transformations between functors on a localization are equal as soon as they agree on
the images of the objects of a class through which every object admits a resolution. -/
private theorem natTrans_eq_of_left_resolutions
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (Y : C), P Y ∧ ∃ p : Y ⟶ X, W p)
    {F G : D ⥤ H} (τ τ' : F ⟶ G)
    (hτ : ∀ X : C, P X → τ.app (Q.obj X) = τ'.app (Q.obj X)) : τ = τ' := by
  refine Localization.natTrans_ext Q W ?_
  intro X
  obtain ⟨Y, hY, p, hp⟩ := hP X
  have : IsIso (Q.map p) := Localization.inverts Q W p hp
  rw [← cancel_epi (F.map (Q.map p)), τ.naturality, τ'.naturality, hτ Y hY]

/-- The underived comparison of `RingTheory.TorIndependence.derivedBaseChangeComparison` carries
the pure tensor `r' ⊗ m` of `R' ⊗_R M` to the pure tensor `i r' ⊗ m` of `A' ⊗_A M`. -/
theorem derivedBaseChangeComparison_fst_app_tmul
    {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R)]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R')]
    [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A')]
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    [(ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).IsLeftAdjoint]
    [(ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).IsLeftAdjoint]
    (sq : h.comp f = i.comp g)
    (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R'))
    (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A'))
    (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R) ⋙ L_g ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ L_h ⟶
      (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [L_g.IsLeftDerivedFunctor alpha_g
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} R) (ComplexShape.up ℤ))]
    [L_h.IsLeftDerivedFunctor alpha_h
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))]
    (M : ModuleCat.{max v uR uA uRp uAp} A) (r' : R') (m : M) :
    (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
      L_g L_h alpha_g alpha_h).1.app M (r' ⊗ₜ[R,g] m) = (i r') ⊗ₜ[A,h] m :=
  (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
    L_g L_h alpha_g alpha_h).2.2.1 M r' m

variable {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R')]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A')]
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
  [(ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).IsLeftAdjoint]
  [(ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).IsLeftAdjoint]
  (sq : h.comp f = i.comp g)
  (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R'))
  (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A'))
  (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R) ⋙ L_g ⟶
    (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ L_h ⟶
    (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [L_g.IsLeftDerivedFunctor alpha_g
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} R) (ComplexShape.up ℤ))]
  [L_h.IsLeftDerivedFunctor alpha_h
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))]

/-- **The underived comparison of Stacks 065Z, built from a unit, a merge and a counit.** The
unit of extension of scalars along `R' → A'` at `R' ⊗_R M`, followed by any morphism `mu` that
merges the two extensions of scalars — it is only asked to carry `1 ⊗ (1 ⊗ m)` to `1 ⊗ (1 ⊗ m)`
— and then by extension of scalars along `A → A'` of the counit of extension of scalars along
`R → A` at `M`, is the comparison.

The merge is left abstract because the two composite extension functors `Ext_g ⋙ Ext_i` and
`Ext_f ⋙ Ext_h` are only equal through `ModuleCat.extendScalarsComp` at both ends and a
transport along `sq`, and a consumer arriving from geometry presents that identification in
whatever shape its own chase produced — one that lives, moreover, at four rings in four
universes, where `ModuleCat.extendScalarsComp` cannot even be stated. All that is used of the
merge is that it carries `1 ⊗ (1 ⊗ m)` to `1 ⊗ (1 ⊗ m)`, and that is written with the four
units rather than with nested pure tensors: the nested pure tensor `1 ⊗ₜ[A,h] (1 ⊗ₜ[R,f] m)`
asks for a `Module A` structure on a tensor product that only the `ModuleCat` object carries,
and the instances a nested spelling does produce are equal to the right ones only at default
transparency, which puts the hypothesis out of reach of `rw` in a consumer's hands. -/
theorem derivedBaseChangeComparison_fst_app_eq_unit_comp_counit
    (M : ModuleCat.{max v uR uA uRp uAp} A)
    (mu : (ModuleCat.extendScalars.{uRp, uAp, max v uR uA uRp uAp} i).obj
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).obj
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M)) ⟶
        (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj
          ((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp uAp} f).obj
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M)))
    (hmu : ∀ m : (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M,
      mu ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uRp, uAp} i).unit.app
            ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M))
          ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uRp} g).unit.app
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M) m)) =
        (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uA, uAp} h).unit.app
            ((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp uAp} f).obj
              ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M))
          ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uA} f).unit.app
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M) m)) :
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uRp, uAp} i).unit.app
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).obj
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M)) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).map
          (mu ≫ (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).map
            ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uA}
              f).counit.app M)) =
      (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
        L_g L_h alpha_g alpha_h).1.app M := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  have hR := derivedBaseChangeComparison_fst_app_tmul.{uR, uA, uRp, uAp, v} f g h i sq
    L_g L_h alpha_g alpha_h M 1 m
  rw [map_one] at hR
  refine Eq.trans ?_ hR.symm
  show (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).map
      ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uA} f).counit.app M)
        (mu ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uRp, uAp} i).unit.app
          ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).obj
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M))
          ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uRp} g).unit.app
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M) m))) = _
  have hc : (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp uAp, uR, uA} f).counit.app M
      ((1 : A) ⊗ₜ[R,f] m) = m :=
    ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul.{uR, uA, max v uR uA uRp uAp}
      f M m
  rw [hmu m]
  exact congrArg (fun y => (1 : A') ⊗ₜ[A,h] y) hc

/-- **The counit compatibility of the derived base-change comparison, at an object.** Composing
the comparison at `K` with the counit of derived extension of scalars along `A → A'`, restricted
along `R' → A'`, is the same as the counit of derived extension of scalars along `R → R'` at the
restriction of `K`, followed by the underived comparison. This is the equation that characterizes
the comparison as a derived lift; `derivedBaseChangeComparison_snd_eq` says it does
characterize it. -/
theorem derivedBaseChangeComparison_snd_app_comp_counit
    (K : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A) ℤ) :
    (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
          L_g L_h alpha_g alpha_h).2.1.app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory.map
          (alpha_h.app K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) =
      L_g.map
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.app
            K) ≫
        alpha_g.app (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
            L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app K) := by
  have hfac := congr_app
    (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
      L_g L_h alpha_g alpha_h).2.2.2 K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.assoc,
    show ∀ (X : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A) ℤ),
        DerivedCategory.Q.map ((mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h ⋙
            ModuleCat.restrictScalars.{max v uR uA uRp uAp} i))
          (ComplexShape.up ℤ)).hom.app X) = CategoryStruct.id _ from
      fun X => CategoryTheory.Functor.map_id _ _,
    show ∀ (X : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A) ℤ),
        DerivedCategory.Q.map ((mapHomologicalComplexCompIso
          (Iso.refl (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f ⋙
            ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g))
          (ComplexShape.up ℤ)).hom.app X) = CategoryStruct.id _ from
      fun X => CategoryTheory.Functor.map_id _ _,
    Functor.comp_obj, Category.comp_id, Category.id_comp] at hfac
  exact hfac

/-- **The derived base-change comparison, computed.** Wherever the counit of derived extension of
scalars along `A → A'` is invertible — which it is at every K-flat complex — the counit
compatibility determines the comparison outright. -/
theorem derivedBaseChangeComparison_snd_app_eq
    (K : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A) ℤ) [IsIso (alpha_h.app K)] :
    (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
        L_g L_h alpha_g alpha_h).2.1.app (DerivedCategory.Q.obj K) =
      (L_g.map
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.app
            K) ≫
        alpha_g.app (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
            L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app K)) ≫
      inv ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory.map
          (alpha_h.app K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) := by
  rw [IsIso.eq_comp_inv]
  exact derivedBaseChangeComparison_snd_app_comp_counit f g h i sq L_g L_h alpha_g alpha_h K

/-- **The derived base-change comparison is the unique solution of its counit equation.** A
transformation from derived base change over `R` to derived base change over `A` that satisfies
the counit compatibility of `derivedBaseChangeComparison_snd_app_comp_counit` at every K-flat
complex is the comparison. K-flat complexes suffice because every complex of `A`-modules admits
a K-flat resolution and the comparison maps are inverted by the localization. -/
theorem derivedBaseChangeComparison_snd_eq
    (tau : (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory ⋙ L_g ⟶
      L_h ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory)
    (htau : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A) ℤ,
      CochainComplex.KFlat.{uA, max v uR uRp uAp} K →
      tau.app (DerivedCategory.Q.obj K) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory.map
            (alpha_h.app K) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) =
        L_g.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.app
              K) ≫
          alpha_g.app (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
              L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app K)) :
    tau = (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
      L_g L_h alpha_g alpha_h).2.1 := by
  refine natTrans_eq_of_left_resolutions DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))
    (fun K => CochainComplex.KFlat.{uA, max v uR uRp uAp} K) ?_ tau _ ?_
  · intro X
    obtain ⟨Y, p, hY, _, hp, _⟩ :=
      CochainComplex.KFlat.exists_kFlat_resolution.{uA, max v uR uRp uAp} X
    exact ⟨Y, hY, p, hp⟩
  · intro K hK
    have : IsIso (alpha_h.app K) :=
      isIso_extendScalarsCounit_app_of_kFlat.{uA, uAp, max v uR uRp} h L_h alpha_h K hK
    rw [derivedBaseChangeComparison_snd_app_eq f g h i sq L_g L_h alpha_g alpha_h K,
      IsIso.eq_comp_inv]
    exact htau K hK

section CanonicalMerge

universe u

/-- The transport of extension of scalars along an equation of ring homomorphisms, on a pure
tensor: it changes the homomorphism the tensor is taken along and nothing else. -/
private theorem extendScalars_eqToHom_tmul {S T : Type u} [CommRing S] [CommRing T]
    {k₁ k₂ : S →+* T} (hk : k₁ = k₂) (N : ModuleCat.{u} S) (t : T) (n : N) :
    eqToHom (congrArg (fun φ : S →+* T =>
        (ModuleCat.extendScalars.{u, u, u} φ).obj N) hk) (t ⊗ₜ[S,k₁] n) = t ⊗ₜ[S,k₂] n := by
  subst hk
  rfl

/-- The composition isomorphism of `ModuleCat.extendScalarsComp` cancelled against its own
inverse, at an element. -/
private theorem extendScalarsComp_inv_app_hom_app {R₁ R₂ R₃ : Type u}
    [CommRing R₁] [CommRing R₂] [CommRing R₃] (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃)
    (N : ModuleCat.{u} R₁)
    (x : (ModuleCat.extendScalars.{u, u, u} (f₂₃.comp f₁₂)).obj N) :
    (ModuleCat.extendScalarsComp f₁₂ f₂₃).inv.app N
        ((ModuleCat.extendScalarsComp f₁₂ f₂₃).hom.app N x) = x := by
  rw [← ConcreteCategory.comp_apply, (ModuleCat.extendScalarsComp f₁₂ f₂₃).hom_inv_id_app]
  rfl

/-- **The merge of the two extensions of scalars, taken canonically.**  This is
`derivedBaseChangeComparison_fst_app_eq_unit_comp_counit` with the abstract merge replaced by the
composition isomorphism of `ModuleCat.extendScalarsComp` for `g` and `i` read backwards, the
transport along the square, and the composition isomorphism for `f` and `h` read forwards.  It
says the identity is not vacuous: the canonical identification of `Ext_g ⋙ Ext_i` with
`Ext_f ⋙ Ext_h` does satisfy the hypothesis there.

Stated with the four rings in one universe, which is what `ModuleCat.extendScalarsComp` needs
and what the four local rings of a cartesian square of schemes over a single universe provide. -/
theorem derivedBaseChangeComparison_fst_app_eq_unit_comp_counit_extendScalarsComp
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} R')] [HasDerivedCategory (ModuleCat.{u} A')]
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    [(ModuleCat.extendScalars.{u, u, u} g).IsLeftAdjoint]
    [(ModuleCat.extendScalars.{u, u, u} h).IsLeftAdjoint]
    (sq : h.comp f = i.comp g)
    (L_g : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R'))
    (L_h : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A'))
    (alpha_g : DerivedCategory.Q (C := ModuleCat.{u} R) ⋙ L_g ⟶
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (alpha_h : DerivedCategory.Q (C := ModuleCat.{u} A) ⋙ L_h ⟶
      (ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [L_g.IsLeftDerivedFunctor alpha_g
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [L_h.IsLeftDerivedFunctor alpha_h
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (M : ModuleCat.{u} A) :
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} i).unit.app
          ((ModuleCat.extendScalars.{u, u, u} g).obj
            ((ModuleCat.restrictScalars.{u} f).obj M)) ≫
        (ModuleCat.restrictScalars.{u} i).map
          (((ModuleCat.extendScalarsComp g i).inv.app
                ((ModuleCat.restrictScalars.{u} f).obj M) ≫
              eqToHom (congrArg (fun φ : R →+* A' =>
                  (ModuleCat.extendScalars.{u, u, u} φ).obj
                    ((ModuleCat.restrictScalars.{u} f).obj M)) sq.symm) ≫
              (ModuleCat.extendScalarsComp f h).hom.app
                ((ModuleCat.restrictScalars.{u} f).obj M)) ≫
            (ModuleCat.extendScalars.{u, u, u} h).map
              ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).counit.app M)) =
      (derivedBaseChangeComparison.{u, u, u, u, u} f g h i sq
        L_g L_h alpha_g alpha_h).1.app M := by
  refine derivedBaseChangeComparison_fst_app_eq_unit_comp_counit.{u, u, u, u, u} f g h i sq
    L_g L_h alpha_g alpha_h M _ fun m => ?_
  have e0 : (ModuleCat.extendScalarsComp g i).hom.app ((ModuleCat.restrictScalars.{u} f).obj M)
        ((1 : A') ⊗ₜ[R,i.comp g] m) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} i).unit.app
          ((ModuleCat.extendScalars.{u, u, u} g).obj ((ModuleCat.restrictScalars.{u} f).obj M))
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
          ((ModuleCat.restrictScalars.{u} f).obj M) m) :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul g i
      ((ModuleCat.restrictScalars.{u} f).obj M) m
  have e2 : (ModuleCat.extendScalarsComp f h).hom.app ((ModuleCat.restrictScalars.{u} f).obj M)
        ((1 : A') ⊗ₜ[R,h.comp f] m) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} h).unit.app
          ((ModuleCat.extendScalars.{u, u, u} f).obj ((ModuleCat.restrictScalars.{u} f).obj M))
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app
          ((ModuleCat.restrictScalars.{u} f).obj M) m) :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul f h
      ((ModuleCat.restrictScalars.{u} f).obj M) m
  rw [← e0, ← e2, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  refine Eq.trans (congrArg (fun z => (ModuleCat.extendScalarsComp f h).hom.app
      ((ModuleCat.restrictScalars.{u} f).obj M)
      (eqToHom (congrArg (fun φ : R →+* A' =>
        (ModuleCat.extendScalars.{u, u, u} φ).obj
          ((ModuleCat.restrictScalars.{u} f).obj M)) sq.symm) z))
    (extendScalarsComp_inv_app_hom_app g i ((ModuleCat.restrictScalars.{u} f).obj M) _)) ?_
  exact congrArg (fun z => (ModuleCat.extendScalarsComp f h).hom.app
      ((ModuleCat.restrictScalars.{u} f).obj M) z)
    (extendScalars_eqToHom_tmul (S := R) (T := A') sq.symm
      ((ModuleCat.restrictScalars.{u} f).obj M) 1 m)

end CanonicalMerge

end RingTheory.TorIndependence

end
