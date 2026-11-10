module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.UnboundedDerivedBaseChangeRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleRightDerivedViaPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorConnectingMorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans

/-!
# The unbounded and the bounded below base change maps on higher direct images

Let `F : A ⥤ B` and `F' : C ⥤ D` be additive (direct images), `G : B ⥤ D` and `G' : A ⥤ C`
exact (inverse images), and `τ : F ⋙ G ⟶ G' ⋙ F'`. The base change map on higher direct images
`G (Rᵠ F X) ⟶ Rᵠ F' (G' X)` can be read off two derived base change maps:

* the bounded below one, `Stacks.Cohomology.BaseChange.derived`, through the comparisons
  `Stacks.DerivedIndexing.rightDerivedIso` of `Rᵠ` with the cohomology of the bounded below right
  derived functor and `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`,
  `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` for the exact functors (this is how
  `Stacks.EtaleCohomology.higherBaseChangeMapAb` is built);
* an unbounded one `bc : RF ⋙ G ⟶ G' ⋙ RF'` satisfying `UnboundedFac`, through the comparisons
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` of `Rᵠ` with the cohomology
  of the unbounded right derived functor and
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`,
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` for the exact functors (this is how
  `Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange` is built).

**This file proves that the two readings agree**, first with the same exact functors on both sides
and then with the unbounded side built from other exact functors `P ≅ G`, `P' ≅ G'`.

## Main results

* `Stacks.Cohomology.BaseChange.unboundedHigher_eq_boundedHigher` — the two readings agree.
* `Stacks.Cohomology.BaseChange.mapDerivedNatTrans_app_single_comp_mapDerivedCategorySingleFunctor`
  — the comparison of the degreewise action with the degree-zero embedding is natural in the exact
  functor.
* `Stacks.Cohomology.BaseChange.unboundedFac_conj` — an unbounded base change map for `P`, `P'`,
  conjugated by `P ≅ G` and `P' ≅ G'`, satisfies `UnboundedFac` for the conjugated `τ`.
* `Stacks.Cohomology.BaseChange.unboundedHigher_conj_eq_boundedHigher` — the two readings agree
  when the unbounded side is built from `P`, `P'`.

## Implementation notes

The comparison of the two readings is
`Stacks.Cohomology.BaseChange.ι_map_derived_app_of_unboundedFac` at `X[0]`,
together with the agreement of the two crossings of `Rᵠ`
(`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso`)
and of the two homology comparisons for an exact functor
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`,
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_eq_derivedHomologyIso`). The
rearrangements are done at variables (`homology_chase` and its helpers), where reassociation is
free.

## References

* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DerivedFunctor
  (singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso)

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Chase

variable {𝒞 : Type*} [Category* 𝒞]

/-- A four-fold composite carried through a functor. At variables. -/
theorem map_comp_four {𝒟 : Type*} [Category* 𝒟] (H : 𝒟 ⥤ 𝒞) {P Q R S T U : 𝒟}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {d : S ⟶ U} {e : P ⟶ T} {f : T ⟶ U}
    (h : a ≫ b ≫ c ≫ d = e ≫ f) :
    H.map a ≫ H.map b ≫ H.map c ≫ H.map d = H.map e ≫ H.map f := by
  simp only [← H.map_comp, h]

/-- A retraction solved for: from `s ≫ r = t` and `s` invertible with inverse `s'`,
`r ≫ t' = s'` where `t'` is the inverse of `t`. At variables. -/
theorem comp_eq_inv_of_hom_comp {P Q R : 𝒞} {s : P ⟶ Q} {s' : Q ⟶ P} {r : Q ⟶ R} {t : P ⟶ R}
    {t' : R ⟶ P} (h : s ≫ r = t) (hs : s' ≫ s = 𝟙 Q) (ht : t ≫ t' = 𝟙 P) : r ≫ t' = s' := by
  rw [← h, Category.assoc] at ht
  rw [← Category.id_comp r, ← hs, Category.assoc, Category.assoc, ht, Category.comp_id]

/-- The inverse of the second factor of a known composite. At variables. -/
theorem inv_eq_of_hom_comp {P Q R : 𝒞} {s : P ⟶ Q} {r : Q ⟶ R} {r' : R ⟶ Q} {t : P ⟶ R}
    {t' : R ⟶ P} (h : s ≫ r = t) (hr : r ≫ r' = 𝟙 Q) (ht : t' ≫ t = 𝟙 R) : r' = t' ≫ s := by
  rw [← Category.id_comp r', ← ht, ← h, Category.assoc, Category.assoc, hr, Category.comp_id]

/-- A composite carried through a functor. At variables. -/
theorem map_comp_eq {𝒟 : Type*} [Category* 𝒟] (H : 𝒟 ⥤ 𝒞) {P Q R : 𝒟} {a : P ⟶ Q} {b : Q ⟶ R}
    {c : P ⟶ R} (h : a ≫ b = c) : H.map a ≫ H.map b = H.map c := by
  rw [← H.map_comp, h]

/-- A factorisation carried through two functors. At variables. -/
theorem map_map_eq_comp {𝒟 ℰ : Type*} [Category* 𝒟] [Category* ℰ] (H : ℰ ⥤ 𝒞) (K : 𝒟 ⥤ ℰ)
    {P Q R : 𝒟} {a : P ⟶ R} {b : P ⟶ Q} {c : Q ⟶ R} (h : a = b ≫ c) :
    H.map (K.map a) = H.map (K.map b) ≫ H.map (K.map c) := by
  rw [h, K.map_comp, H.map_comp]

/-- The rearrangement behind `unboundedHigher_eq_boundedHigher`, at variables. -/
theorem homology_chase {O0 O1 O2 O3 O4 O5 O6 O7 O1' O2' O3' O4' : 𝒞}
    {g1 : O0 ⟶ O1} {E : O1 ⟶ O3} {h2 : O3 ⟶ O4} {h3 : O4 ⟶ O5} {R : O5 ⟶ O7}
    {d0 : O1 ⟶ O2} {h1 : O2 ⟶ O3} (e2 : E = d0 ≫ h1)
    {h4 : O5 ⟶ O6} {s' : O6 ⟶ O7} (e7 : R = h4 ≫ s')
    {k3 : O4 ⟶ O3'} {k4 : O3' ⟶ O6} (e8 : h3 ≫ h4 = k3 ≫ k4)
    {k5 : O3' ⟶ O4'} {m : O4' ⟶ O6} (e6 : k4 = k5 ≫ m)
    {gb : O2 ⟶ O1'} {hb : O1' ⟶ O4'} (e5 : h1 ≫ h2 ≫ k3 ≫ k5 = gb ≫ hb)
    {gH : O1 ⟶ O2'} {d1 : O2' ⟶ O1'} (e4 : d0 ≫ gb = gH ≫ d1)
    {gs : O0 ⟶ O2'} (e1 : g1 ≫ gH = gs) {d1' : O2' ⟶ O1'} (e3 : d1 = d1') :
    gs ≫ d1' ≫ hb ≫ m ≫ s' = g1 ≫ E ≫ h2 ≫ h3 ≫ R := by
  subst e2 e7 e6 e3
  rw [← e1]
  simp only [Category.assoc]
  rw [reassoc_of% e8, reassoc_of% e5, reassoc_of% e4]

/-- A square carried through a functor. At variables. -/
theorem map_square {𝒟 : Type*} [Category* 𝒟] (H : 𝒟 ⥤ 𝒞) {P Q Q' R : 𝒟} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : P ⟶ Q'} {d : Q' ⟶ R} (h : a ≫ b = c ≫ d) :
    H.map a ≫ H.map b = H.map c ≫ H.map d := by
  rw [← H.map_comp, h, H.map_comp]

/-- A three-fold composite carried through a functor. At variables. -/
theorem map_comp_three_eq {𝒟 : Type*} [Category* 𝒟] (H : 𝒟 ⥤ 𝒞) {P Q R S : 𝒟} {a : P ⟶ Q}
    {b : Q ⟶ R} {c : R ⟶ S} {d : P ⟶ S} (h : a ≫ b ≫ c = d) :
    H.map a ≫ H.map b ≫ H.map c = H.map d := by
  rw [← H.map_comp, ← H.map_comp, h]

/-- A square of isomorphisms read with two sides inverted. At variables. -/
theorem inv_comp_eq_comp_inv {P Q Q' R : 𝒞} {a : P ⟶ Q} {b : Q ⟶ R} {c : P ⟶ Q'} {d : Q' ⟶ R}
    {b' : R ⟶ Q} {c' : Q' ⟶ P} (h : a ≫ b = c ≫ d) (hb : b ≫ b' = 𝟙 Q) (hc : c' ≫ c = 𝟙 Q') :
    c' ≫ a = d ≫ b' := by
  rw [← Category.comp_id a, ← hb, ← Category.assoc, ← Category.assoc, Category.assoc c', h,
    ← Category.assoc, hc, Category.id_comp]

/-- The rearrangement behind `unboundedFac_conj`, at variables. -/
theorem conj_chase {O0 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 : 𝒞}
    {x1 : O0 ⟶ O1} {x2 : O1 ⟶ O2} {x3 : O2 ⟶ O3} {x4 : O3 ⟶ O4} {x5 : O4 ⟶ O5}
    {y1 : O1 ⟶ O6} {y2 : O6 ⟶ O3} (c1 : x2 ≫ x3 = y1 ≫ y2)
    {z1 : O0 ⟶ O7} {z2 : O7 ⟶ O6} (c2 : x1 ≫ y1 = z1 ≫ z2)
    {w1 : O7 ⟶ O8} {w2 : O8 ⟶ O9} {w3 : O9 ⟶ O4} (hP : z2 ≫ y2 ≫ x4 = w1 ≫ w2 ≫ w3)
    {v1 : O9 ⟶ O10} {v2 : O10 ⟶ O5} (c3 : w3 ≫ x5 = v1 ≫ v2)
    {t1 : O8 ⟶ O11} {t2 : O11 ⟶ O10} (c4 : w2 ≫ v1 = t1 ≫ t2)
    {r : O0 ⟶ O11} (c5 : z1 ≫ w1 ≫ t1 = r) :
    x1 ≫ x2 ≫ x3 ≫ x4 ≫ x5 = r ≫ t2 ≫ v2 := by
  rw [reassoc_of% c1, reassoc_of% c2, reassoc_of% hP, c3, reassoc_of% c4, ← c5, Category.assoc,
    Category.assoc]

/-- The rearrangement behind `unboundedHigher_conj`, at variables. -/
theorem conj_higher_chase {O0 O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 : 𝒞}
    {i0 : O0 ⟶ O1} {pS : O1 ⟶ O3} {gS : O0 ⟶ O2} {i1 : O2 ⟶ O3} (f1 : gS ≫ i1 = i0 ≫ pS)
    {gD : O2 ⟶ O4} {hm : O4 ⟶ O5} {pD : O3 ⟶ O5} (f2 : gD ≫ hm = i1 ≫ pD)
    {hb : O5 ⟶ O6} {hx : O6 ⟶ O7} {hg : O7 ⟶ O8} {hp : O6 ⟶ O9} {hsg : O9 ⟶ O8}
    (f3 : hx ≫ hg = hp ≫ hsg)
    {sG : O8 ⟶ O10} {sP : O9 ⟶ O11} {rinv : O11 ⟶ O10} {rhom : O10 ⟶ O11}
    (f4 : hsg ≫ sG = sP ≫ rinv) (f5 : rinv ≫ rhom = 𝟙 O11)
    {hc : O4 ⟶ O7} (e0 : hc = hm ≫ hb ≫ hx) :
    i0 ≫ pS ≫ pD ≫ hb ≫ hp ≫ sP = (gS ≫ gD ≫ hc ≫ hg ≫ sG) ≫ rhom := by
  subst e0
  simp only [Category.assoc]
  rw [reassoc_of% f3, reassoc_of% f4, f5, Category.comp_id, reassoc_of% f2, reassoc_of% f1]

end Chase

section Same

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (uF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  (RF' : DerivedCategory C ⥤ DerivedCategory D)
  (uF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  (bc : RF ⋙ G.mapDerivedCategory ⟶ G'.mapDerivedCategory ⋙ RF')
  [RF.IsRightDerivedFunctor uF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [RF'.IsRightDerivedFunctor uF' (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

omit [EnoughInjectives C] in
/-- The bounded below comparison of `G'` with `X ↦ X[0]` is the unbounded one composed with the
comparison of `G'` on bounded below derived categories. -/
theorem ι_map_exactSingleFunctorRightDerivedPlusIso_inv_app (X : A) :
    DerivedCategory.Plus.ι.map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).inv.app X) =
      DerivedCategory.Plus.ι.map ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G').inv.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
        (G'.mapDerivedCategorySingleFunctor 0).hom.app X := by
  change DerivedCategory.Plus.ι.map
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G').inv.app _ ≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle G' 0).hom.app X) = _
  rw [Functor.map_comp, Stacks.DerivedFunctor.ι_map_exactMapDerivedCategoryPlusSingle_hom_app]
  rfl

/-- **The unbounded and the bounded below readings of the base change map on `Rᵠ` agree.** For
an unbounded base change map `bc` satisfying `UnboundedFac`, its degree-`q` cohomology at `X[0]`,
read through `singleCompDerivedCompHomologyIsoRightDerived` and the comparisons of `G`, `G'` with
`Hᵠ` and with `X ↦ X[0]`, is the degree-`q` cohomology of the bounded below base change map
`derived F F' G G' τ` read through `Stacks.DerivedIndexing.rightDerivedIso` and the bounded below
comparisons. -/
theorem unboundedHigher_eq_boundedHigher (hbc : UnboundedFac F F' G G' τ RF uF RF' uF' bc)
    (q : ℕ) (X : A) :
    G.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF uF hresA
        q).inv.app X) ≫
      (G.mapDerivedCategoryHomologyIso (q : ℤ)).inv.app
        (RF.obj ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        (bc.app ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        (RF'.map ((G'.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F' RF' uF' hresC
        q).hom.app (G'.obj X) =
    G.map ((Stacks.DerivedIndexing.rightDerivedIso F q).hom.app X) ≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso G (q : ℤ)).inv.app
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map
        ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map
        (F'.rightDerivedFunctorPlus.map
          ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).inv.app X)) ≫
      (Stacks.DerivedIndexing.rightDerivedIso F' q).inv.app (G'.obj X) := by
  let H := DerivedCategory.homologyFunctor D (q : ℤ)
  let X0 := (DerivedCategory.Plus.singleFunctor A 0).obj X
  let bdF := F.boundedDerivedIso RF uF hresA
  let bdF' := F'.boundedDerivedIso RF' uF' hresC
  let y := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).inv.app X
  have e2 : (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso G (q : ℤ)).inv.app
        (F.rightDerivedFunctorPlus.obj X0) =
      (Stacks.DerivedFunctor.derivedHomologyIso G (q : ℤ)).inv.app
          (DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj X0)) ≫
        H.map (DerivedCategory.Plus.ι.map
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).hom.app
            (F.rightDerivedFunctorPlus.obj X0))) := rfl
  have e7 : (Stacks.DerivedIndexing.rightDerivedIso F' q).inv.app (G'.obj X) =
      H.map (bdF'.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj (G'.obj X))) ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F' RF' uF' hresC
          q).hom.app (G'.obj X) :=
    inv_eq_of_hom_comp (singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso
        F' RF' uF' hresC q (G'.obj X))
      (Iso.hom_inv_id_app (Stacks.DerivedIndexing.rightDerivedIso F' q) (G'.obj X))
      (Iso.hom_inv_id_map (bdF'.app ((DerivedCategory.Plus.singleFunctor C 0).obj (G'.obj X))) H)
  have e8 : H.map (DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlus.map y)) ≫
      H.map (bdF'.hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj (G'.obj X))) =
      H.map (bdF'.hom.app (G'.rightDerivedFunctorPlus.obj X0)) ≫
        H.map (RF'.map (DerivedCategory.Plus.ι.map y)) :=
    map_square H (bdF'.hom.naturality y)
  have e6 : H.map (RF'.map (DerivedCategory.Plus.ι.map y)) =
      H.map (RF'.map (DerivedCategory.Plus.ι.map
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G').inv.app X0))) ≫
        H.map (RF'.map ((G'.mapDerivedCategorySingleFunctor 0).hom.app X)) :=
    map_map_eq_comp H RF' (ι_map_exactSingleFunctorRightDerivedPlusIso_inv_app G' X)
  have e5 := map_comp_four H
    (ι_map_derived_app_of_unboundedFac F F' G G' τ RF uF RF' uF' bc hresA hresC hbc X0)
  have e4 := ((Stacks.DerivedFunctor.derivedHomologyIso G (q : ℤ)).inv.naturality
    (bdF.hom.app X0)).symm
  have e1 : G.map ((Stacks.DerivedIndexing.rightDerivedIso F q).hom.app X) ≫
      G.map ((DerivedCategory.homologyFunctor B (q : ℤ)).map (bdF.hom.app X0)) =
      G.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF uF hresA
        q).inv.app X) := by
    have h := singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso
      F RF uF hresA q X
    exact map_comp_eq G (comp_eq_inv_of_hom_comp h (Iso.inv_hom_id_app _ X)
      (Iso.inv_hom_id_map (bdF.app X0) (DerivedCategory.homologyFunctor B (q : ℤ))))
  have e3 : (Stacks.DerivedFunctor.derivedHomologyIso G (q : ℤ)).inv.app
        (RF.obj ((DerivedCategory.singleFunctor A 0).obj X)) =
      (G.mapDerivedCategoryHomologyIso (q : ℤ)).inv.app
        (RF.obj ((DerivedCategory.singleFunctor A 0).obj X)) := by
    rw [Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso,
      Functor.mapDerivedCategoryHomologyFunctorIso_eq_derivedHomologyIso]
  exact homology_chase e2 e7 e8 e6 e5 e4 e1 e3

end Same

section Conj

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C) (P : B ⥤ D) (P' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [P.Additive] [P'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits P'] [PreservesFiniteColimits P']
  (ιs : G ≅ P) (ιx : G' ≅ P')
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (uF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  (RF' : DerivedCategory C ⥤ DerivedCategory D)
  (uF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  (bcP : RF ⋙ P.mapDerivedCategory ⟶ P'.mapDerivedCategory ⋙ RF')

/-- **An unbounded base change map for `P`, `P'`, read for `G`, `G'`**: conjugated by the
identifications `G ≅ P` and `G' ≅ P'` on derived categories. -/
def conjBaseChange : RF ⋙ G.mapDerivedCategory ⟶ G'.mapDerivedCategory ⋙ RF' :=
  Functor.whiskerLeft RF
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso G P ιs).hom ≫
    bcP ≫
    Functor.whiskerRight
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso G' P' ιx).inv RF'

/-- A transformation on derived categories whose value at `Q K` is `τ` degreewise, read through
the factorisations, is `mapDerivedNatTrans τ`. -/
private theorem eq_mapDerivedNatTrans_of_app_Q {X Y : Type*} [Category* X] [Category* Y]
    [Abelian X] [Abelian Y] (T S : X ⥤ Y) [T.Additive] [S.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (τ : T ⟶ S)
    (θ : T.mapDerivedCategory ⟶ S.mapDerivedCategory)
    (h : ∀ K : CochainComplex X ℤ, θ.app (DerivedCategory.Q.obj K) =
      T.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K) ≫
          S.mapDerivedCategoryFactors.inv.app K) :
    θ = Stacks.DerivedFunctor.mapDerivedNatTrans τ := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso X (ComplexShape.up ℤ)) fun K => ?_
  rw [h, ← cancel_mono (S.mapDerivedCategoryFactors.hom.app K),
    Stacks.DerivedFunctor.mapDerivedNatTrans_factors_app]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rfl

omit [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] in
/-- The identification on derived categories of two isomorphic exact functors is the
transformation induced by the isomorphism. -/
theorem mapDerivedCategoryIsoOfNatIso_hom_eq (T S : B ⥤ D) [T.Additive] [S.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (e : T ≅ S) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso T S e).hom =
      Stacks.DerivedFunctor.mapDerivedNatTrans e.hom :=
  eq_mapDerivedNatTrans_of_app_Q T S e.hom _
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q T S e)

omit [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] in
/-- The inverse of the identification on derived categories of two isomorphic exact functors is
the transformation induced by the inverse. -/
theorem mapDerivedCategoryIsoOfNatIso_inv_eq (T S : A ⥤ C) [T.Additive] [S.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (e : T ≅ S) :
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso T S e).inv =
      Stacks.DerivedFunctor.mapDerivedNatTrans e.inv :=
  eq_mapDerivedNatTrans_of_app_Q S T e.inv _
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q T S e)

omit [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] in
/-- **The conjugated unbounded base change map satisfies the factorisation for the conjugated
comparison.** If `bcP` satisfies `UnboundedFac` for `τ' : F ⋙ P ⟶ P' ⋙ F'`, then
`conjBaseChange` satisfies it for `τ = ιs ≫ τ' ≫ ιx⁻¹`. -/
theorem unboundedFac_conj (τ : F ⋙ G ⟶ G' ⋙ F') (τ' : F ⋙ P ⟶ P' ⋙ F')
    (hτ : τ = Functor.whiskerLeft F ιs.hom ≫ τ' ≫ Functor.whiskerRight ιx.inv F')
    (h : UnboundedFac F F' P P' τ' RF uF RF' uF' bcP) :
    UnboundedFac F F' G G' τ RF uF RF' uF' (conjBaseChange G G' P P' ιs ιx RF RF' bcP) := by
  intro K
  have c1 := (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso G P ιs).hom.naturality
    (uF.app K)
  have c2 :
      G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso G P ιs).hom.app
        (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ιs.hom (ComplexShape.up ℤ)).app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
        P.mapDerivedCategoryFactorsh.inv.app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
    rw [mapDerivedCategoryIsoOfNatIso_hom_eq]
    exact (Stacks.DerivedFunctor.Qh_map_comp_mapDerivedCategoryFactorsh_inv_app ιs.hom _).symm
  have c3 : RF'.map (P'.mapDerivedCategoryFactorsh.inv.app K) ≫
      RF'.map ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso G' P' ιx).inv.app
        (DerivedCategory.Qh.obj K)) =
      RF'.map (DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory ιx.inv (ComplexShape.up ℤ)).app K)) ≫
        RF'.map (G'.mapDerivedCategoryFactorsh.inv.app K) := by
    refine map_square RF' ?_
    rw [mapDerivedCategoryIsoOfNatIso_inv_eq]
    exact (Stacks.DerivedFunctor.Qh_map_comp_mapDerivedCategoryFactorsh_inv_app ιx.inv _).symm
  have c4 := (uF'.naturality ((NatTrans.mapHomotopyCategory ιx.inv (ComplexShape.up ℤ)).app K)).symm
  have c5h : (NatTrans.mapHomotopyCategory ιs.hom (ComplexShape.up ℤ)).app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory τ' (ComplexShape.up ℤ)).app K ≫
      (F'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory ιx.inv (ComplexShape.up ℤ)).app K) =
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K := by
    subst hτ
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app]
    rfl
  exact conj_chase c1 c2 (h K) c3 c4 (map_comp_three_eq DerivedCategory.Qh c5h)

variable [RF.IsRightDerivedFunctor uF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [RF'.IsRightDerivedFunctor uF' (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

omit [EnoughInjectives B] in
/-- **The unbounded reading of the base change map on `Rᵠ` for `P`, `P'` is that for `G`, `G'`
of the conjugated map**, up to the identifications `G ≅ P` at the source and `G' ≅ P'` at the
target. -/
theorem unboundedHigher_conj (q : ℕ) (X : A) :
    ιs.hom.app ((F.rightDerived q).obj X) ≫
      P.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF uF hresA
        q).inv.app X) ≫
      (P.mapDerivedCategoryHomologyIso (q : ℤ)).inv.app
        (RF.obj ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        (bcP.app ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        (RF'.map ((P'.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F' RF' uF' hresC
        q).hom.app (P'.obj X) =
    (G.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF uF hresA
        q).inv.app X) ≫
      (G.mapDerivedCategoryHomologyIso (q : ℤ)).inv.app
        (RF.obj ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        ((conjBaseChange G G' P P' ιs ιx RF RF' bcP).app
          ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        (RF'.map ((G'.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F' RF' uF' hresC
        q).hom.app (G'.obj X)) ≫
      (F'.rightDerived q).map (ιx.hom.app X) := by
  let H := DerivedCategory.homologyFunctor D (q : ℤ)
  let X0 := (DerivedCategory.singleFunctor A 0).obj X
  let mIs := Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso G P ιs
  let mIx := Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso G' P' ιx
  have f1 := ιs.hom.naturality
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF uF hresA
      q).inv.app X)
  have f2 : (G.mapDerivedCategoryHomologyIso (q : ℤ)).inv.app (RF.obj X0) ≫
      H.map (mIs.hom.app (RF.obj X0)) =
      ιs.hom.app ((DerivedCategory.homologyFunctor B (q : ℤ)).obj (RF.obj X0)) ≫
        (P.mapDerivedCategoryHomologyIso (q : ℤ)).inv.app (RF.obj X0) := by
    rw [Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso,
      Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso]
    exact inv_comp_eq_comp_inv
      (Functor.mapDerivedCategoryHomologyFunctorIso_isoOfNatIso_app G P ιs (q : ℤ) (RF.obj X0))
      (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _)
  have f3 : H.map (RF'.map (mIx.inv.app X0)) ≫
      H.map (RF'.map ((G'.mapDerivedCategorySingleFunctor 0).hom.app X)) =
      H.map (RF'.map ((P'.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
        H.map (RF'.map ((DerivedCategory.singleFunctor C 0).map (ιx.inv.app X))) := by
    refine map_square H (map_square RF' ?_)
    exact inv_comp_eq_comp_inv
      (Functor.mapDerivedCategorySingleFunctor_isoOfNatIso_app G' P' ιx 0 X).symm
      (Iso.hom_inv_id_map (ιx.app X) (DerivedCategory.singleFunctor C 0))
      (Iso.inv_hom_id_app _ _)
  have f4 := (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F' RF' uF' hresC
    q).hom.naturality (ιx.inv.app X)
  have f5 := Iso.inv_hom_id_map (ιx.app X) (F'.rightDerived q)
  have e0 : H.map ((conjBaseChange G G' P P' ιs ιx RF RF' bcP).app X0) =
      H.map (mIs.hom.app (RF.obj X0)) ≫ H.map (bcP.app X0) ≫ H.map (RF'.map (mIx.inv.app X0)) :=
    (map_comp_three_eq H rfl).symm
  exact conj_higher_chase f1 f2 f3 f4 f5 e0

omit [EnoughInjectives B] in
/-- **The unbounded reading for `P`, `P'` and the bounded below reading for `G`, `G'` of the base
change map on `Rᵠ` agree**, up to the identifications `G ≅ P` and `G' ≅ P'`, as soon as the
unbounded base change map `bcP` satisfies `UnboundedFac` for `τ'` and `τ = ιs ≫ τ' ≫ ιx⁻¹`. -/
theorem unboundedHigher_conj_eq_boundedHigher [EnoughInjectives B] (τ : F ⋙ G ⟶ G' ⋙ F')
    (τ' : F ⋙ P ⟶ P' ⋙ F')
    (hτ : τ = Functor.whiskerLeft F ιs.hom ≫ τ' ≫ Functor.whiskerRight ιx.inv F')
    (h : UnboundedFac F F' P P' τ' RF uF RF' uF' bcP) (q : ℕ) (X : A) :
    ιs.hom.app ((F.rightDerived q).obj X) ≫
      P.map ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F RF uF hresA
        q).inv.app X) ≫
      (P.mapDerivedCategoryHomologyIso (q : ℤ)).inv.app
        (RF.obj ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        (bcP.app ((DerivedCategory.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.homologyFunctor D (q : ℤ)).map
        (RF'.map ((P'.mapDerivedCategorySingleFunctor 0).hom.app X)) ≫
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived F' RF' uF' hresC
        q).hom.app (P'.obj X) =
    (G.map ((Stacks.DerivedIndexing.rightDerivedIso F q).hom.app X) ≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso G (q : ℤ)).inv.app
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map
        ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor D (q : ℤ)).map
        (F'.rightDerivedFunctorPlus.map
          ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso G' 0).inv.app X)) ≫
      (Stacks.DerivedIndexing.rightDerivedIso F' q).inv.app (G'.obj X)) ≫
      (F'.rightDerived q).map (ιx.hom.app X) := by
  rw [unboundedHigher_conj F F' G G' P P' ιs ιx RF uF RF' uF' bcP hresA hresC q X,
    unboundedHigher_eq_boundedHigher F F' G G' τ RF uF RF' uF'
      (conjBaseChange G G' P P' ιs ιx RF RF' bcP) hresA hresC
      (unboundedFac_conj F F' G G' P P' ιs ιx RF uF RF' uF' bcP τ τ' hτ h) q X]

end Conj

end Stacks.Cohomology.BaseChange

end
