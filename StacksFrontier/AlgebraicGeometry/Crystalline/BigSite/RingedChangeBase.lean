module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.RingedStructureMorphism

/-!
# Change of divided power base, as a morphism of ringed topoi

[Stacks, Tag 07MG] asserts that, in the situation of [Stacks, Tag 07IC] -- a morphism of
divided power schemes `(S, I, γ) ⟶ (S', I', γ')` and a morphism `X ⟶ Y` over the closed fibres --
the square
```
(X/S)_CRIS ──f_CRIS──> (Y/S')_CRIS
    │                      │
    ▼                      ▼
Sh((Sch/S)_Zar) ──────> Sh((Sch/S')_Zar)
```
whose vertical arrows are the structure morphisms is a commutative diagram of *ringed* topoi.
`StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureMorphism` proves the commutativity of
the underlying square of topoi,
`Crystalline.GlobalCrystallineSituation.changeBaseStructureSquare`; this file carries the ring
structures.

The corners are ringed as in
`StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.RingedStructureMorphism`: the big Zariski topoi
by `𝒪 : T ↦ Γ(T, 𝒪_T)` and the big crystalline topoi by `U_{X/S}⁻¹𝒪`, the sheaf
`\underline{𝐆_a} : (U, T, δ) ↦ Γ(U, 𝒪_U)` of [Stacks, Tag 07IN] (that file records why this, and
not `𝒪_{X/S}`, is the structure sheaf for which the structure morphisms are morphisms of ringed
topoi).  The vertical arrows are `Crystalline.GlobalCrystallineSituation.structureMorphismRinged`
and the bottom arrow is `AlgebraicGeometry.zariskiOverRingedMorphism` along `S ⟶ S'`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.changeBaseRingedMorphism` -- the morphism of crystalline
  topoi `f_CRIS : (X/S)_CRIS ⟶ (Y/S')_CRIS` of [Stacks, Tag 07IC] as a morphism of ringed topoi.
  Its structure map is invertible.
* `Crystalline.GlobalCrystallineSituation.changeBaseZariskiSquareRinged` -- the square formed by
  `f_CRIS`, the two crystalline-to-Zariski comparisons and the big Zariski arrow along `X ⟶ Y`
  commutes as a square of ringed topoi.
* `Crystalline.GlobalCrystallineSituation.changeBaseStructureSquareRinged` -- the square of
  [Stacks, Tag 07MG] commutes as a square of ringed topoi.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IN](https://stacks.math.columbia.edu/tag/07IN)
* [Stacks Project, Tag 07MG](https://stacks.math.columbia.edu/tag/07MG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry

/-- **Equal morphisms of schemes give 2-isomorphic ringed big Zariski arrows.** -/
noncomputable def zariskiOverRingedMorphismCongr {X Y : Scheme.{u}} {a b : X ⟶ Y}
    (hab : a = b) :
    RingedToposHom.TwoIso.{u, u + 1, u + 1, u, u + 1, u + 1}
      (zariskiOverRingedMorphism a) (zariskiOverRingedMorphism b) := by
  subst hab
  exact RingedToposHom.TwoIso.refl.{u, u + 1, u + 1, u, u + 1, u + 1} _

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation

section ChangeBase

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **The two routes `(X/S)_CRIS ⟶ Sh((Sch/Y)_Zar)` have isomorphic inverse images.**  The mate
of `Crystalline.GlobalCrystallineSituation.changeBaseZariskiSquare` under the two adjunctions. -/
noncomputable def changeBaseZariskiSquareInverseImage :
    ((zariskiComparison S').comp (changeBaseMorphism S S' f g h)).inverseImage ≅
      ((zariskiOverMorphism g).comp (zariskiComparison S)).inverseImage :=
  Adjunction.leftAdjointUniq
    (((zariskiComparison S').comp (changeBaseMorphism S S' f g h)).adj.ofNatIsoRight
      (changeBaseZariskiSquare S S' f g h).symm)
    ((zariskiOverMorphism g).comp (zariskiComparison S)).adj

/-- **The inverse image along `f_CRIS` of the structure sheaf of `(Y/S')_CRIS` is the structure
sheaf of `(X/S)_CRIS`.**  Both are the inverse image of `T ↦ Γ(T, 𝒪_T)` along a route from
`(X/S)_CRIS` to the big Zariski topos of `Y`, and
`Crystalline.GlobalCrystallineSituation.changeBaseZariskiSquare` identifies the two routes. -/
noncomputable def changeBaseStructureInverseImageIso :
    (inverseImageCommRingFunctor (changeBaseMorphism S S' f g h)).obj
        (crystallineZariskiRingedTopos S').O ≅
      (crystallineZariskiRingedTopos S).O :=
  (inverseImageCommRingComp (zariskiComparison S') (changeBaseMorphism S S' f g h)).app
      (zariskiOverStructureSheaf S'.X) ≪≫
    pullbackCommRingSheafCongr (topology S) (changeBaseZariskiSquareInverseImage S S' f g h)
      (zariskiOverStructureSheaf S'.X) ≪≫
    ((inverseImageCommRingComp (zariskiOverMorphism g) (zariskiComparison S)).app
      (zariskiOverStructureSheaf S'.X)).symm ≪≫
    (inverseImageCommRingFunctor (zariskiComparison S)).mapIso
      (zariskiOverStructureInverseImageIso g)

/-- **Stacks Project, Tag 07MG.**  The morphism of crystalline topoi
`f_CRIS : (X/S)_CRIS ⟶ (Y/S')_CRIS` of [Stacks, Tag 07IC] as a morphism of ringed topoi -- the
top arrow of the square.  Its structure map is invertible, being the identification of the two
routes to the big Zariski topos of `Y`. -/
@[stacks 07MG "the top arrow of the square, as a morphism of ringed topoi"]
noncomputable def changeBaseRingedMorphism :
    RingedToposHom (crystallineZariskiRingedTopos S) (crystallineZariskiRingedTopos S') :=
  RingedToposHom.ofInverseImageIso (X := crystallineZariskiRingedTopos S)
    (Y := crystallineZariskiRingedTopos S') (changeBaseMorphism S S' f g h)
    (changeBaseStructureInverseImageIso S S' f g h)

@[simp]
theorem changeBaseRingedMorphism_toToposHom :
    (changeBaseRingedMorphism S S' f g h).toToposHom = changeBaseMorphism S S' f g h := rfl

/-- **The structure map of the ringed `f_CRIS` is invertible.** -/
theorem isIso_changeBaseRingedMorphism_fSharpInverseImage :
    IsIso (changeBaseRingedMorphism S S' f g h).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := crystallineZariskiRingedTopos S) (Y := crystallineZariskiRingedTopos S')
    (changeBaseMorphism S S' f g h) (changeBaseStructureInverseImageIso S S' f g h)

/-- The structure map of the ringed `f_CRIS`, in inverse-image form. -/
theorem changeBaseRingedMorphism_fSharpInverseImage :
    (changeBaseRingedMorphism S S' f g h).fSharpInverseImage =
      (changeBaseStructureInverseImageIso S S' f g h).hom :=
  RingedToposHom.ofInverseImageIso_fSharpInverseImage
    (X := crystallineZariskiRingedTopos S) (Y := crystallineZariskiRingedTopos S')
    (changeBaseMorphism S S' f g h) (changeBaseStructureInverseImageIso S S' f g h)

/-- The four factors of the identification of inverse images along `f_CRIS`, spelled out. -/
theorem changeBaseStructureInverseImageIso_hom :
    (changeBaseStructureInverseImageIso S S' f g h).hom =
      (inverseImageCommRingComp (zariskiComparison S')
            (changeBaseMorphism S S' f g h)).hom.app (zariskiOverStructureSheaf S'.X) ≫
        (pullbackCommRingSheafCongr (topology S)
            (changeBaseZariskiSquareInverseImage S S' f g h)
            (zariskiOverStructureSheaf S'.X)).hom ≫
          (inverseImageCommRingComp (zariskiOverMorphism g) (zariskiComparison S)).inv.app
              (zariskiOverStructureSheaf S'.X) ≫
            (inverseImageCommRingFunctor (zariskiComparison S)).map
              (zariskiOverStructureInverseImageIso g).hom :=
  rfl

/-- **The square of `f_CRIS` and the crystalline-to-Zariski comparisons, at the spelling of its
type carried by the two composites of morphisms of ringed topoi.** -/
noncomputable def changeBaseZariskiSquareRingedPushforward :
    (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
      (Y := zariskiOverRingedTopos S.X) (Z := zariskiOverRingedTopos S'.X)
      (zariskiOverRingedMorphism g) (zariskiComparisonRinged S)).toToposHom.pushforward ≅
    (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
      (Y := crystallineZariskiRingedTopos S') (Z := zariskiOverRingedTopos S'.X)
      (zariskiComparisonRinged S')
      (changeBaseRingedMorphism S S' f g h)).toToposHom.pushforward :=
  changeBaseZariskiSquare S S' f g h

/-- **The square formed by `f_CRIS`, the comparisons `U_{X/S}`, `U_{Y/S'}` and the big Zariski
arrow along `X ⟶ Y` commutes as a square of ringed topoi**: `U_{Y/S'} ∘ f_CRIS` and
`f_big ∘ U_{X/S}` are 2-isomorphic as morphisms of ringed topoi, the underlying 2-isomorphism of
topoi being `Crystalline.GlobalCrystallineSituation.changeBaseZariskiSquare`. -/
noncomputable def changeBaseZariskiSquareRinged :
    RingedToposHom.TwoIso.{u, u + 1, u + 1, u, u + 1, u + 1}
      (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
        (Y := zariskiOverRingedTopos S.X) (Z := zariskiOverRingedTopos S'.X)
        (zariskiOverRingedMorphism g) (zariskiComparisonRinged S))
      (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
        (Y := crystallineZariskiRingedTopos S') (Z := zariskiOverRingedTopos S'.X)
        (zariskiComparisonRinged S') (changeBaseRingedMorphism S S' f g h)) :=
  RingedToposHom.TwoIso.ofPushforwardIsoCommRing.{u, u + 1, u + 1, u, u + 1, u + 1}
    (changeBaseZariskiSquareRingedPushforward S S' f g h) (by
      have h1 : (inverseImageCommRingFunctor (changeBaseMorphism S S' f g h)).map
          (zariskiComparisonRinged S').fSharpInverseImage =
          𝟙 ((inverseImageCommRingFunctor (changeBaseMorphism S S' f g h)).obj
            (crystallineZariskiRingedTopos S').O) :=
        (congrArg (inverseImageCommRingFunctor (changeBaseMorphism S S' f g h)).map
          (zariskiComparisonRinged_fSharpInverseImage S')).trans
          (CategoryTheory.Functor.map_id _ _)
      have hf : (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
            (Y := zariskiOverRingedTopos S.X) (Z := zariskiOverRingedTopos S'.X)
            (zariskiOverRingedMorphism g) (zariskiComparisonRinged S)).fSharpInverseImage =
          (inverseImageCommRingComp (zariskiOverMorphism g) (zariskiComparison S)).inv.app
              (zariskiOverStructureSheaf S'.X) ≫
            (inverseImageCommRingFunctor (zariskiComparison S)).map
              (zariskiOverStructureInverseImageIso g).hom :=
        (RingedToposHom.comp_fSharpInverseImage_eq
            (zariskiOverRingedMorphism g) (zariskiComparisonRinged S)).trans
          (congrArg (fun m ↦ (inverseImageCommRingComp (zariskiOverMorphism g)
                (zariskiComparison S)).inv.app (zariskiOverStructureSheaf S'.X) ≫ m)
            (((congrArg (fun m ↦ (inverseImageCommRingFunctor (zariskiComparison S)).map m ≫
                    (zariskiComparisonRinged S).fSharpInverseImage)
                  (zariskiOverRingedMorphism_fSharpInverseImage g)).trans
                (congrArg (fun m ↦ (inverseImageCommRingFunctor (zariskiComparison S)).map
                    (zariskiOverStructureInverseImageIso g).hom ≫ m)
                  (zariskiComparisonRinged_fSharpInverseImage S))).trans
              (Category.comp_id _)))
      have hg : (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
            (Y := crystallineZariskiRingedTopos S') (Z := zariskiOverRingedTopos S'.X)
            (zariskiComparisonRinged S')
            (changeBaseRingedMorphism S S' f g h)).fSharpInverseImage =
          (pullbackCommRingSheafCongr (topology S)
              (changeBaseZariskiSquareInverseImage S S' f g h)
              (zariskiOverStructureSheaf S'.X)).hom ≫
            (inverseImageCommRingComp (zariskiOverMorphism g) (zariskiComparison S)).inv.app
                (zariskiOverStructureSheaf S'.X) ≫
              (inverseImageCommRingFunctor (zariskiComparison S)).map
                (zariskiOverStructureInverseImageIso g).hom :=
        (RingedToposHom.comp_fSharpInverseImage_eq
            (zariskiComparisonRinged S') (changeBaseRingedMorphism S S' f g h)).trans
          ((congrArg (fun m ↦ (inverseImageCommRingComp (zariskiComparison S')
                  (changeBaseMorphism S S' f g h)).inv.app
                (zariskiOverStructureSheaf S'.X) ≫ m)
              (((congrArg (fun m ↦ (inverseImageCommRingFunctor
                      (changeBaseMorphism S S' f g h)).map
                        (zariskiComparisonRinged S').fSharpInverseImage ≫ m)
                    (changeBaseRingedMorphism_fSharpInverseImage S S' f g h)).trans
                  ((congrArg (fun m ↦ m ≫
                        (changeBaseStructureInverseImageIso S S' f g h).hom) h1).trans
                    (Category.id_comp _))).trans
                (changeBaseStructureInverseImageIso_hom S S' f g h))).trans
            (Iso.inv_hom_id_app_assoc _ _ _))
      rw [hf, hg]
      rfl)

/-- **Stacks Project, Tag 07MG.**  The square
```
(X/S)_CRIS ──f_CRIS──> (Y/S')_CRIS
    │                      │
    ▼                      ▼
Sh((Sch/S)_Zar) ──────> Sh((Sch/S')_Zar)
```
whose vertical arrows are the structure morphisms is a commutative diagram of *ringed* topoi: the
two composites `(X/S)_CRIS ⟶ Sh((Sch/S')_Zar)` are 2-isomorphic as morphisms of ringed topoi.
It is pasted out of the ringed square of
`Crystalline.GlobalCrystallineSituation.changeBaseZariskiSquareRinged` and the ringed big Zariski
triangles along `X ⟶ Y ⟶ S'` and `X ⟶ S ⟶ S'`, which have the same composite. -/
@[stacks 07MG "the square of structure morphisms is a commutative diagram of ringed topoi"]
noncomputable def changeBaseStructureSquareRinged :
    RingedToposHom.TwoIso.{u, u + 1, u + 1, u, u + 1, u + 1}
      (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
        (Y := zariskiOverRingedTopos S.S.scheme) (Z := zariskiOverRingedTopos S'.S.scheme)
        (zariskiOverRingedMorphism f.hom) (structureMorphismRinged S))
      (RingedToposHom.comp (X := crystallineZariskiRingedTopos S)
        (Y := crystallineZariskiRingedTopos S') (Z := zariskiOverRingedTopos S'.S.scheme)
        (structureMorphismRinged S') (changeBaseRingedMorphism S S' f g h)) :=
  -- `f_big ∘ (b_S ∘ U_{X/S}) ≅ (f_big ∘ b_S) ∘ U_{X/S} ≅ (b_{S'} ∘ g_big) ∘ U_{X/S}`
  ((RingedToposHom.TwoIso.associator (zariskiComparisonRinged S)
        (zariskiOverRingedMorphism (sourceToBase S)) (zariskiOverRingedMorphism f.hom)).trans
      (RingedToposHom.TwoIso.whiskerLeft.{u, u + 1, u + 1, u, u + 1, u + 1, u, u + 1, u + 1}
        (zariskiComparisonRinged S)
        (((zariskiOverRingedMorphismComp (sourceToBase S) f.hom).trans
            (zariskiOverRingedMorphismCongr (comp_sourceToBase (h := h)).symm)).trans
          (zariskiOverRingedMorphismComp g (sourceToBase S')).symm))).trans
    -- `≅ b_{S'} ∘ (g_big ∘ U_{X/S}) ≅ b_{S'} ∘ (U_{Y/S'} ∘ f_CRIS) ≅ (b_{S'} ∘ U_{Y/S'}) ∘ f_CRIS`
    (((RingedToposHom.TwoIso.associator (zariskiComparisonRinged S)
          (zariskiOverRingedMorphism g) (zariskiOverRingedMorphism (sourceToBase S'))).symm.trans
        (RingedToposHom.TwoIso.whiskerRight (changeBaseZariskiSquareRinged S S' f g h)
          (zariskiOverRingedMorphism (sourceToBase S')))).trans
      (RingedToposHom.TwoIso.associator (changeBaseRingedMorphism S S' f g h)
        (zariskiComparisonRinged S') (zariskiOverRingedMorphism (sourceToBase S'))))

end ChangeBase

end Crystalline.GlobalCrystallineSituation

end
