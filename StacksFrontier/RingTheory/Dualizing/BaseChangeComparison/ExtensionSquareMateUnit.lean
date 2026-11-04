module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMate
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ExtensionSquareMateDerived

/-!
# The unit identity behind the mate of the base-change square, at four arbitrary models

For a commutative square

```
  R ---> A
  |      |
  v      v
  R' --> A'
```

of commutative rings, with `A'` at the universe `max uA uRp`, and four arbitrary models of derived
extension of scalars, one along each edge, this file proves the following identity at the class of
a cochain complex: the unit of [stacks 0GMT] along the bottom edge, followed by the composite
comparison along `R → R' → A'`, agrees with the base change of the unit along the top edge, then
the comparison of [stacks 065Z], then the composite comparison along `R → A → A'`. No Tor
independence, K-flatness or condition on the chosen models is assumed. This is the identity to
which `Dualizing.derivedBaseChangeSquareIso_mate_eq` reduces the Beck--Chevalley description of
the base-change square isomorphism.

## Main results

* `StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq_app_eq` — the composite
  comparison of two models at a cochain complex is the second model applied to the first model's
  comparison, followed by the second model's comparison and the localization of the degreewise
  composition isomorphism.
* `RingTheory.TorIndependence.unit_comp_derivedBaseChangeComparison_fst_complex` — the module
  level identity `RingTheory.TorIndependence.unit_comp_derivedBaseChangeComparison_fst`, read
  degreewise on a cochain complex.
* `RingTheory.TorIndependence.unit_comp_compComparisonOfEq` — at the class of a cochain complex
  `P` of `R`-modules, the unit of [stacks 0GMT] along `R' → A'` at `L_g P`, followed by the
  restriction of the composite comparison along `R → R' → A'`, equals `L_g` of the unit along
  `R → A`, then the comparison of [stacks 065Z], then the restriction of the composite comparison
  along `R → A → A'`.

## Implementation notes

The universe `uAp` of `A'` is specialised to `max uA uRp`, the universe of `A ⊗_R R'`, so that the
universe levels of these statements agree syntactically with those of the square
`R → A`, `R → R'`, `A → A ⊗_R R'`, `R' → A ⊗_R R'`.

The two `Functor.IsLeftAdjoint` hypotheses make the two extension functors additive at the module
universe; they are the ones `RingTheory.TorIndependence.derivedBaseChangeComparison` carries.
Additivity of degreewise extension of scalars along a bare ring homomorphism is the local instance
`Dualizing.extendScalarsAdditiveOfRingHom`.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

namespace StacksDraft.DerivedExtensionScalarsModelComp

universe u₁ u₂ u₃ v w₁ w₂ w₃

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom
attribute [local instance_reducible] CochainComplex.extendScalarsLarge

variable {R : Type u₁} {A : Type u₂} {B : Type u₃} [CommRing R] [CommRing A] [CommRing B]
  [HasDerivedCategory.{w₃} (ModuleCat.{max v u₁ u₂ u₃} B)]
  [HasDerivedCategory.{w₁} (ModuleCat.{max v u₁ u₂ u₃} R)]
  [HasDerivedCategory.{w₂} (ModuleCat.{max v u₁ u₂ u₃} A)]
  (f : R →+* A) (g : A →+* B)
  (F : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} R) ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A))
  (α : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (G : DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} A) ⥤
    DerivedCategory (ModuleCat.{max v u₁ u₂ u₃} B))
  (β : DerivedCategory.Q ⋙ G ⟶
    (ModuleCat.extendScalars.{u₂, u₃, max v u₁ u₂ u₃} g).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

/-- The composite comparison `compComparisonOfEq` of two models of derived extension of scalars,
at a cochain complex `P`: `G` applied to the comparison `α` at `P`, followed by the comparison `β`
at the extension of `P` along `f` and the localization of the degreewise composition isomorphism
along `g.comp f = h`. -/
theorem compComparisonOfEq_app_eq (h : R →+* B) (hfg : g.comp f = h)
    (P : CochainComplex (ModuleCat.{max v u₁ u₂ u₃} R) ℤ) :
    (compComparisonOfEq f g F α G β h hfg).app P =
      G.map (α.app P) ≫
        β.app (((ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u₁, u₂, u₃, v} f g h hfg)
          (ComplexShape.up ℤ)).app P) := by
  subst hfg
  simp [compComparisonOfEq, RingTheory.TorIndependence.extendScalarsCompInvOfEq]
  rfl

end StacksDraft.DerivedExtensionScalarsModelComp

namespace RingTheory.TorIndependence

universe uR uA uRp v

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom
attribute [local instance_reducible] CochainComplex.extendScalarsLarge

variable {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type (max uA uRp)}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [HasDerivedCategory.{max v uR uA uRp + 1} (ModuleCat.{max v uR uA uRp} R)]
  [HasDerivedCategory.{max v uR uA uRp + 1} (ModuleCat.{max v uR uA uRp} A)]
  [HasDerivedCategory.{max v uR uA uRp + 1} (ModuleCat.{max v uR uA uRp} R')]
  [HasDerivedCategory.{max v uR uA uRp + 1} (ModuleCat.{max v uR uA uRp} A')]
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
  [(ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} g).IsLeftAdjoint]
  [(ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp} h).IsLeftAdjoint]
  (hc : R →+* A') (h1 : h.comp f = hc) (h2 : i.comp g = hc)
  (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A'))
  (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp} R) ⋙ L_g ⟶
    (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} g).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp} A) ⋙ L_h ⟶
    (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp} h).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [L_g.IsLeftDerivedFunctor alpha_g
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [L_h.IsLeftDerivedFunctor alpha_h
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]

include h1 h2 in
/-- `RingTheory.TorIndependence.unit_comp_derivedBaseChangeComparison_fst` degreewise on a cochain
complex `P`: the unit of extension--restriction along `i` at the extension of `P` along `g`,
followed by the restriction of the composition isomorphism along `R → R' → A'`, equals the
extension along `g` of the unit along `f`, followed by the first component of
`RingTheory.TorIndependence.derivedBaseChangeComparison` and the restriction of the composition
isomorphism along `R → A → A'`. -/
theorem unit_comp_derivedBaseChangeComparison_fst_complex
    (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uRp, max uA uRp} i).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.restrictScalars.{max v uR uA uRp} i).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (extendScalarsCompInvOfEq.{uR, uRp, max uA uRp, max v uA} g i hc h2)
            (ComplexShape.up ℤ)).app P) =
      ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P) ≫
        (NatTrans.mapHomologicalComplex
            (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} f g h i (h1.trans h2.symm)
              L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app
          (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.restrictScalars.{max v uR uA uRp} i).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp} f h hc h1)
            (ComplexShape.up ℤ)).app P) :=
  HomologicalComplex.hom_ext _ _ (fun n =>
    unit_comp_derivedBaseChangeComparison_fst.{uR, uA, uRp, max uA uRp, v} f g h i hc h1 h2
      L_g L_h alpha_g alpha_h (P.X n))

variable
  (L_f : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alpha_f : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp} R) ⋙ L_f ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (L_i : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A'))
  (alpha_i : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp} R') ⋙ L_i ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp} i).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [L_f.IsLeftDerivedFunctor alpha_f
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [L_i.IsLeftDerivedFunctor alpha_i
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include h1 h2 in
/-- At the class of a cochain complex `P` of `R`-modules, the unit of [stacks 0GMT] along `i` at
`L_g P`, followed by the restriction of the composite comparison along `R → R' → A'`, equals
`L_g` of the unit along `f`, then the comparison of [stacks 065Z], then the restriction of the
composite comparison along `R → A → A'`. -/
theorem unit_comp_compComparisonOfEq (P : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ) :
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR} i L_i alpha_i).unit.app
          (L_g.obj (DerivedCategory.Q.obj P)) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategory.map
          ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp, max uA uRp,
            max v uA} g i L_g alpha_g L_i alpha_i hc h2).app P) =
      L_g.map ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} f L_f alpha_f).unit.app
            (DerivedCategory.Q.obj P)) ≫
        (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} f g h i (h1.trans h2.symm)
            L_g L_h alpha_g alpha_h).2.1.app (L_f.obj (DerivedCategory.Q.obj P)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategory.map
            ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA, max uA uRp,
              max v uRp} f h L_f alpha_f L_h alpha_h hc h1).app P) := by
  have hAR := StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq_app_eq.{uR, uRp,
    max uA uRp, max v uA} g i L_g alpha_g L_i alpha_i hc h2 P
  have hAL := StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq_app_eq.{uR, uA,
    max uA uRp, max v uRp} f h L_f alpha_f L_h alpha_h hc h1 P
  have hmain :
      (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR} i L_i alpha_i).unit.app
            (L_g.obj (DerivedCategory.Q.obj P)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategory.map
            (L_i.map (alpha_g.app P) ≫
              alpha_i.app (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
              DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex
                  (extendScalarsCompInvOfEq.{uR, uRp, max uA uRp, max v uA} g i hc h2)
                  (ComplexShape.up ℤ)).app P)) =
        L_g.map ((derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} f L_f alpha_f).unit.app
              (DerivedCategory.Q.obj P)) ≫
          (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} f g h i (h1.trans h2.symm)
              L_g L_h alpha_g alpha_h).2.1.app (L_f.obj (DerivedCategory.Q.obj P)) ≫
            (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategory.map
              (L_h.map (alpha_f.app P) ≫
                alpha_h.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
                DerivedCategory.Q.map
                  ((NatTrans.mapHomologicalComplex
                    (extendScalarsCompInvOfEq.{uR, uA, max uA uRp, max v uRp} f h hc h1)
                    (ComplexShape.up ℤ)).app P)) := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map]
    slice_lhs 1 2 => rw [Adjunction.unit_naturality]
    slice_lhs 2 3 => rw [derivedExtensionScalarsAdjunction_unit_app.{uRp, max uA uRp, max v uR}
      i L_i alpha_i (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)]
    simp only [Category.assoc]
    have hphi : ∀ {X Y : CochainComplex (ModuleCat.{max v uR uA uRp} A') ℤ} (φ : X ⟶ Y),
        DerivedCategory.Q.map
          (((ModuleCat.restrictScalars.{max v uR uA uRp} i).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategoryFactors.inv.app Y =
        (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategoryFactors.inv.app X ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategory.map
            (DerivedCategory.Q.map φ) :=
      fun φ =>
        (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategoryFactors.inv.naturality φ
    slice_lhs 3 4 => rw [← hphi]
    slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
    rw [unit_comp_derivedBaseChangeComparison_fst_complex.{uR, uA, uRp, v} f g h i hc h1 h2
      L_g L_h alpha_g alpha_h P]
    have hnatC := (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} f g h i
      (h1.trans h2.symm) L_g L_h alpha_g alpha_h).2.1.naturality (alpha_f.app P)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hnatC
    slice_rhs 2 3 => rw [← hnatC]
    slice_rhs 1 2 => rw [← CategoryTheory.Functor.map_comp,
      derivedExtensionScalarsAdjunction_unit_app.{uR, uA, max v uRp} f L_f alpha_f P,
      CategoryTheory.Functor.map_comp]
    have hcounit := derivedBaseChangeComparison_snd_app_comp_counit.{uR, uA, uRp, max uA uRp, v}
      f g h i (h1.trans h2.symm) L_g L_h alpha_g alpha_h
      (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
    have hstep : (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} f g h i
              (h1.trans h2.symm) L_g L_h alpha_g alpha_h).2.1.app
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategory.map
            (alpha_h.app (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
        (L_g.map ((ModuleCat.restrictScalars.{max v uR uA uRp}
                f).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
            alpha_g.app (((ModuleCat.restrictScalars.{max v uR uA uRp}
                f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
              (derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} f g h i (h1.trans h2.symm)
                L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P))) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp} i).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp} h).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) := by
      rw [← hcounit]
      simp
    slice_rhs 3 4 => rw [hstep]
    simp only [Category.assoc]
    slice_rhs 2 3 => rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Category.assoc]
    have hnatg := alpha_g.naturality
      (((ModuleCat.extendRestrictScalarsAdj.{max v uR uRp, uR, uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app P)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hnatg
    slice_rhs 1 2 => rw [hnatg]
    slice_rhs 4 5 => rw [← hphi]
    slice_rhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
    slice_rhs 2 3 => rw [← CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    dsimp only [Functor.id_obj]
  rw [hAR, hAL]
  exact hmain

end RingTheory.TorIndependence

end
