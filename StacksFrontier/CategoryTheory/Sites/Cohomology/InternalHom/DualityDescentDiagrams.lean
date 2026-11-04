module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# The diagram chases of the derived-duality cluster, over an abstract category

The derived-duality cluster of **Stacks 0FPC** and **Stacks 0FPU** -- the composition law (C) of
the composition morphism of Stacks 0A8V against the application morphism of Stacks 08J8, the two
unit laws (UL) and (UR), the equation (E1) tying the comparison of Stacks 08I1 to the evaluation
of the derived dual, and the compatibility of the associativity constraint of Stacks 0FPT with
the canonical map of Stacks 06YU -- is proved twice in this development: for a ringed space, in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLaw` and its
neighbours, and for a ringed site, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionApplicationLawOnASite` and
its neighbours.

Every one of those proofs ends in a diagram chase that mentions no sheaf, no complex and no
derived category: a transport of a square along isomorphisms of its corners, or a paste of two
squares. **Those chases are collected here**, over an arbitrary category and -- where a
bifunctor is involved -- over an arbitrary bifunctor, with every object and morphism a variable.
Each is used by `exact` on the two sides, which is the point: the goals they are applied to
mention the source of a derived internal Hom at two definitionally equal spellings, so they are
not type-correct at the `implicit` transparency level and no rewriting tactic acts on them. One
`exact` against a statement whose every corner is a variable pays that crossing once.

## Main results

* `Stacks.Cohomology.DualityDescent.inv_comp_eq_of_transport`,
  `Stacks.Cohomology.DualityDescent.leg_of_inv_comp`: a leg built from the inverse of an
  isomorphism transported along a naturality square, in the two shapes the unit laws use beside
  `Stacks.SheafOfModules.transport_leg`.
* `Stacks.Cohomology.DualityDescent.bifunctor_target_naturality`: the paste of a bifunctor
  contravariant in its first variable and covariant in its second out of a naturality square in
  the second variable, the counterpart of `Stacks.SheafOfModules.hom_bifunctor_paste`.
* `Stacks.Cohomology.DualityDescent.transport_target`,
  `Stacks.Cohomology.DualityDescent.transport_middle`,
  `Stacks.Cohomology.DualityDescent.transport_source`: transport of the composition law (C)
  along an isomorphism of its target, of its intermediate object and of its source.
* `Stacks.Cohomology.DualityDescent.comp_app_descent`: the composition law against application,
  descended along three comparisons.
* `Stacks.Cohomology.DualityDescent.assoc_descent`: descent of an associativity square along
  isomorphisms of its three variables.
* `Stacks.Cohomology.DualityDescent.paste_composition_unit`: a composition law and a right unit
  law paste into a contraction law, over an arbitrary monoidal category.

## Implementation notes

Four further chases of the cluster — `Stacks.SheafOfModules.transport_leg`,
`Stacks.SheafOfModules.hom_bifunctor_paste`, `Stacks.SheafOfModules.paste_cancel` and
`Stacks.SheafOfModules.map_op_app_comp` — are stated, in exactly this generality, in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw`, and the
ringed-site unit laws read them from there rather than from a second copy here.

## Nothing here is tagged

These are statements of elementary category theory, asserted by no published statement of the
source.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace Stacks.Cohomology.DualityDescent

/-! ### Transport of a leg along a naturality square -/

/-- A retraction and a cancelling isomorphism are stripped off a commuting square. Stated over
an arbitrary category with every object and morphism a variable, for the reason given on
`Stacks.SheafOfModules.transport_leg`. -/
theorem inv_comp_eq_of_transport {D : Type*} [Category D]
    {FHc FHm Hc Hm T S : D} (A : FHc ≅ Hc) (A' : FHm ≅ Hm) (c : Hm ≅ Hc)
    (w : FHc ⟶ FHm) (q : FHm ⟶ T) (t : T ≅ S) {m : Hc ⟶ S} {g : Hm ⟶ T}
    (hnat : w ≫ A'.hom = A.hom ≫ c.inv)
    (hlanded : A.inv ≫ w ≫ q ≫ t.hom = m)
    (hrhs : c.hom ≫ m ≫ t.inv = g) :
    A'.inv ≫ q = g := by
  have hAw : A.inv ≫ w = c.inv ≫ A'.inv := by
    rw [← Iso.eq_comp_inv] at hnat
    rw [hnat, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← hrhs, ← hlanded, ← Category.assoc A.inv, hAw]
  simp

/-- A leg is cancelled off the front of a composite that an isomorphism factors. Stated over an
arbitrary category with every object and morphism a variable, for the reason given on
`Stacks.SheafOfModules.transport_leg`. -/
theorem leg_of_inv_comp {D : Type*} [Category D] {a b p q r : D}
    (c : a ≅ p) (w : a ⟶ b) (q' : b ⟶ q) (t : q ≅ r) {m : p ⟶ r} {g : a ⟶ q}
    (h1 : c.inv ≫ w ≫ q' ≫ t.hom = m) (h2 : c.hom ≫ m ≫ t.inv = g) :
    w ≫ q' = g := by
  subst h1 h2
  simp

/-! ### Pastes for a bifunctor contravariant in its first variable -/

/-- A square of a bifunctor contravariant in its first variable and covariant in its second,
pasted out of a naturality square in the *second* variable. The second-variable counterpart of
`Stacks.SheafOfModules.hom_bifunctor_paste`. -/
theorem bifunctor_target_naturality {D : Type*} [Category D] (F : Dᵒᵖ ⥤ D ⥤ D)
    {A A' M M' N N' : D} (a : A' ⟶ A) (m : M ⟶ M') (φ : N ⟶ M) (φ' : N' ⟶ M') (n : N ⟶ N')
    (h : n ≫ φ' = φ ≫ m) :
    ((F.map a.op).app N ≫ (F.obj (op A')).map n) ≫ (F.obj (op A')).map φ' =
      (F.obj (op A)).map φ ≫ ((F.map a.op).app M ≫ (F.obj (op A')).map m) := by
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_comp,
    ← Category.assoc, ← (F.map a.op).naturality φ, Category.assoc]

/-! ### Transport of the composition law (C) -/

/-- Two factorisations of a morphism give equal composites of the components of `F.map` at `K`. -/
private theorem app_map_comp_congr {C : Type*} [Category C] (F : C ⥤ C ⥤ C) (K : C)
    {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z} (h : f ≫ g = f' ≫ g') :
    (F.map f).app K ≫ (F.map g).app K = (F.map f').app K ≫ (F.map g').app K := by
  rw [← NatTrans.comp_app, ← Functor.map_comp, h, Functor.map_comp, NatTrans.comp_app]

/-- Transport of the composition law along an isomorphism of the target object. -/
theorem transport_target {C : Type*} [Category C] (F : C ⥤ C ⥤ C)
    {HLM HLM' HKL HKM HKM' K L M M' : C}
    (comp : (F.obj HLM).obj HKL ⟶ HKM) (comp' : (F.obj HLM').obj HKL ⟶ HKM')
    (εKM : (F.obj HKM).obj K ⟶ M) (εKM' : (F.obj HKM').obj K ⟶ M') (εKL : (F.obj HKL).obj K ⟶ L)
    (εLM : (F.obj HLM).obj L ⟶ M) (εLM' : (F.obj HLM').obj L ⟶ M')
    (α : (F.obj ((F.obj HLM).obj HKL)).obj K ⟶ (F.obj HLM).obj ((F.obj HKL).obj K))
    (α' : (F.obj ((F.obj HLM').obj HKL)).obj K ⟶ (F.obj HLM').obj ((F.obj HKL).obj K))
    (m : M ⟶ M') (mK : HKM ⟶ HKM') (mL : HLM ⟶ HLM') [IsIso mL]
    (hcomp : comp ≫ mK = (F.map mL).app HKL ≫ comp')
    (hεK : (F.map mK).app K ≫ εKM' = εKM ≫ m) (hεL : (F.map mL).app L ≫ εLM' = εLM ≫ m)
    (hα : (F.map ((F.map mL).app HKL)).app K ≫ α' = α ≫ (F.map mL).app ((F.obj HKL).obj K))
    (h : (F.map comp).app K ≫ εKM = α ≫ (F.obj HLM).map εKL ≫ εLM) :
    (F.map comp').app K ≫ εKM' = α' ≫ (F.obj HLM').map εKL ≫ εLM' := by
  rw [← cancel_epi ((F.map ((F.map mL).app HKL)).app K), ← Category.assoc,
    app_map_comp_congr F K hcomp.symm, Category.assoc, hεK, reassoc_of% h, reassoc_of% hα,
    ← NatTrans.naturality_assoc, hεL]

/-- Transport of the composition law along an isomorphism of the intermediate object. -/
theorem transport_middle {C : Type*} [Category C] (F : C ⥤ C ⥤ C)
    {HLM HL'M HKL HKL' HKM K L L' M : C}
    (comp : (F.obj HLM).obj HKL ⟶ HKM) (comp' : (F.obj HL'M).obj HKL' ⟶ HKM)
    (εKM : (F.obj HKM).obj K ⟶ M) (εKL : (F.obj HKL).obj K ⟶ L) (εKL' : (F.obj HKL').obj K ⟶ L')
    (εLM : (F.obj HLM).obj L ⟶ M) (εL'M : (F.obj HL'M).obj L' ⟶ M)
    (α : (F.obj ((F.obj HLM).obj HKL)).obj K ⟶ (F.obj HLM).obj ((F.obj HKL).obj K))
    (αm : (F.obj ((F.obj HL'M).obj HKL)).obj K ⟶ (F.obj HL'M).obj ((F.obj HKL).obj K))
    (α' : (F.obj ((F.obj HL'M).obj HKL')).obj K ⟶ (F.obj HL'M).obj ((F.obj HKL').obj K))
    (l : L ⟶ L') (lK : HKL ⟶ HKL') (lM : HL'M ⟶ HLM) [IsIso lK]
    (hcomp : (F.obj HL'M).map lK ≫ comp' = (F.map lM).app HKL ≫ comp)
    (hεK : (F.map lK).app K ≫ εKL' = εKL ≫ l)
    (hεM : (F.obj HL'M).map l ≫ εL'M = (F.map lM).app L ≫ εLM)
    (hα₁ : (F.map ((F.map lM).app HKL)).app K ≫ α = αm ≫ (F.map lM).app ((F.obj HKL).obj K))
    (hα₂ : (F.map ((F.obj HL'M).map lK)).app K ≫ α' = αm ≫ (F.obj HL'M).map ((F.map lK).app K))
    (h : (F.map comp).app K ≫ εKM = α ≫ (F.obj HLM).map εKL ≫ εLM) :
    (F.map comp').app K ≫ εKM = α' ≫ (F.obj HL'M).map εKL' ≫ εL'M := by
  rw [← cancel_epi ((F.map ((F.obj HL'M).map lK)).app K), ← Category.assoc,
    app_map_comp_congr F K hcomp, Category.assoc, h, reassoc_of% hα₁, reassoc_of% hα₂,
    ← Functor.map_comp_assoc, hεK, Functor.map_comp_assoc, hεM, NatTrans.naturality_assoc]

/-- Transport of the composition law along an isomorphism of the source object. -/
theorem transport_source {C : Type*} [Category C] (F : C ⥤ C ⥤ C)
    {HLM HKL HK'L HKM HK'M K K' L M : C}
    (comp : (F.obj HLM).obj HKL ⟶ HKM) (comp' : (F.obj HLM).obj HK'L ⟶ HK'M)
    (εKM : (F.obj HKM).obj K ⟶ M) (εK'M : (F.obj HK'M).obj K' ⟶ M)
    (εKL : (F.obj HKL).obj K ⟶ L) (εK'L : (F.obj HK'L).obj K' ⟶ L)
    (εLM : (F.obj HLM).obj L ⟶ M)
    (α : (F.obj ((F.obj HLM).obj HKL)).obj K ⟶ (F.obj HLM).obj ((F.obj HKL).obj K))
    (αm : (F.obj ((F.obj HLM).obj HKL)).obj K' ⟶ (F.obj HLM).obj ((F.obj HKL).obj K'))
    (α' : (F.obj ((F.obj HLM).obj HK'L)).obj K' ⟶ (F.obj HLM).obj ((F.obj HK'L).obj K'))
    (k : K' ⟶ K) (kM : HKM ⟶ HK'M) (kL : HKL ⟶ HK'L) [IsIso kL] [IsIso k]
    (hcomp : comp ≫ kM = (F.obj HLM).map kL ≫ comp')
    (hεM : (F.obj HKM).map k ≫ εKM = (F.map kM).app K' ≫ εK'M)
    (hεL : (F.obj HKL).map k ≫ εKL = (F.map kL).app K' ≫ εK'L)
    (hα₁ : (F.obj _).map k ≫ α = αm ≫ (F.obj HLM).map ((F.obj HKL).map k))
    (hα₂ : (F.map ((F.obj HLM).map kL)).app K' ≫ α' = αm ≫ (F.obj HLM).map ((F.map kL).app K'))
    (h : (F.map comp).app K ≫ εKM = α ≫ (F.obj HLM).map εKL ≫ εLM) :
    (F.map comp').app K' ≫ εK'M = α' ≫ (F.obj HLM).map εK'L ≫ εLM := by
  rw [← cancel_epi ((F.map ((F.obj HLM).map kL)).app K'), ← Category.assoc,
    app_map_comp_congr F K' hcomp.symm, Category.assoc, ← hεM,
    ← NatTrans.naturality_assoc, h, reassoc_of% hα₁, reassoc_of% hα₂,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hεL]

/-! ### Descent of the composition law along comparisons -/

/-- **Composition against application, transported along comparisons**, for an arbitrary
bifunctor `F`. The conclusion is an identity of morphisms out of `F(F(RH, RG), QP)`; after
precomposition with the invertible `F(F(σH, σG), QP)` both sides are computed by the hypotheses
on the source side of the comparisons `σ`. -/
theorem comp_app_descent {C : Type*} [Category C] (F : C ⥤ C ⥤ C)
    {QH QG QE RH RG RE QP QJ QI THG THGP TGP THGP2 THJ : C}
    (σH : QH ⟶ RH) (σG : QG ⟶ RG) (σE : QE ⟶ RE) (hσH : IsIso σH) (hσG : IsIso σG)
    (comp : (F.obj RH).obj RG ⟶ RE) (appKM : (F.obj RE).obj QP ⟶ QI)
    (appKL : (F.obj RG).obj QP ⟶ QJ) (appLM : (F.obj RH).obj QJ ⟶ QI)
    (αR : (F.obj ((F.obj RH).obj RG)).obj QP ⟶ (F.obj RH).obj ((F.obj RG).obj QP))
    (αQ : (F.obj ((F.obj QH).obj QG)).obj QP ⟶ (F.obj QH).obj ((F.obj QG).obj QP))
    (tHG : (F.obj QH).obj QG ⟶ THG) (tHGP : (F.obj THG).obj QP ⟶ THGP)
    (tGP : (F.obj QG).obj QP ⟶ TGP) (tHGP2 : (F.obj QH).obj TGP ⟶ THGP2)
    (tHJ : (F.obj QH).obj QJ ⟶ THJ)
    (mDC : THG ⟶ QE) (mUU : THGP ⟶ QI) (qα : THGP ⟶ THGP2) (mWE : THGP2 ⟶ THJ)
    (evGP : TGP ⟶ QJ) (evHJ : THJ ⟶ QI)
    (h1 : (F.map σH).app QG ≫ (F.obj RH).map σG ≫ comp = tHG ≫ mDC ≫ σE)
    (h2a : (F.map mDC).app QP ≫ (F.map σE).app QP ≫ appKM = tHGP ≫ mUU)
    (h2b : (F.map σG).app QP ≫ appKL = tGP ≫ evGP)
    (h2c : (F.map σH).app QJ ≫ appLM = tHJ ≫ evHJ)
    (h3 : (F.obj QH).map evGP ≫ tHJ = tHGP2 ≫ mWE)
    (h4 : (F.map tHG).app QP ≫ tHGP ≫ qα = αQ ≫ (F.obj QH).map tGP ≫ tHGP2)
    (h5 : mUU = qα ≫ mWE ≫ evHJ)
    (hα : (F.map ((F.map σH).app QG ≫ (F.obj RH).map σG)).app QP ≫ αR =
      αQ ≫ (F.map σH).app ((F.obj QG).obj QP) ≫ (F.obj RH).map ((F.map σG).app QP)) :
    (F.map comp).app QP ≫ appKM = αR ≫ (F.obj RH).map appKL ≫ appLM := by
  have := hσH
  have := hσG
  rw [← cancel_epi ((F.map ((F.map σH).app QG ≫ (F.obj RH).map σG)).app QP)]
  have eL : (F.map ((F.map σH).app QG ≫ (F.obj RH).map σG)).app QP ≫
      (F.map comp).app QP ≫ appKM =
        αQ ≫ (F.obj QH).map ((F.map σG).app QP ≫ appKL) ≫ (F.map σH).app QJ ≫ appLM := by
    rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, Category.assoc, h1,
      Functor.map_comp, Functor.map_comp, NatTrans.comp_app, NatTrans.comp_app, Category.assoc,
      Category.assoc, h2a, h5, reassoc_of% h4, h2b, h2c, Functor.map_comp, Category.assoc,
      reassoc_of% h3]
  have eR : (F.map ((F.map σH).app QG ≫ (F.obj RH).map σG)).app QP ≫ αR ≫
      (F.obj RH).map appKL ≫ appLM =
        αQ ≫ (F.obj QH).map ((F.map σG).app QP ≫ appKL) ≫ (F.map σH).app QJ ≫ appLM := by
    rw [reassoc_of% hα, ← reassoc_of% (F.obj RH).map_comp, ← NatTrans.naturality_assoc]
  rw [eL, eR]

/-! ### Descent of an associativity square -/

/-- **Descent of an associativity square along isomorphisms**, for an arbitrary bifunctor `F`
with a family of associativity morphisms. If the square holds for `A'`, `B'`, `D'`, the maps `t`
are natural along `a`, `b`, `d`, `q` and the associativity morphisms are natural along `a`, `b`,
`d`, with `a`, `b`, `d` invertible, then it holds for `A`, `B`, `D`. -/
theorem assoc_descent {C : Type*} [Category C] (F : C ⥤ C ⥤ C)
    {A A' B B' D D' AB AB' BD BD' L L' R R' : C}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) [IsIso a] [IsIso b] [IsIso d]
    (tAB : (F.obj A).obj B ⟶ AB) (tAB' : (F.obj A').obj B' ⟶ AB') (mAB : AB' ⟶ AB)
    (hAB : (F.map a).app B' ≫ (F.obj A).map b ≫ tAB = tAB' ≫ mAB)
    (tBD : (F.obj B).obj D ⟶ BD) (tBD' : (F.obj B').obj D' ⟶ BD') (mBD : BD' ⟶ BD)
    (hBD : (F.map b).app D' ≫ (F.obj B).map d ≫ tBD = tBD' ≫ mBD)
    (tL : (F.obj AB).obj D ⟶ L) (tL' : (F.obj AB').obj D' ⟶ L') (mL : L' ⟶ L)
    (hL : (F.map mAB).app D' ≫ (F.obj AB).map d ≫ tL = tL' ≫ mL)
    (tR : (F.obj A).obj BD ⟶ R) (tR' : (F.obj A').obj BD' ⟶ R') (mR : R' ⟶ R)
    (hR : (F.map a).app BD' ≫ (F.obj A).map mBD ≫ tR = tR' ≫ mR)
    (q : L ⟶ R) (q' : L' ⟶ R') (hq : mL ≫ q = q' ≫ mR)
    (α : (F.obj ((F.obj A).obj B)).obj D ⟶ (F.obj A).obj ((F.obj B).obj D))
    (α' : (F.obj ((F.obj A').obj B')).obj D' ⟶ (F.obj A').obj ((F.obj B').obj D'))
    (hα : (F.map ((F.map a).app B' ≫ (F.obj A).map b)).app D' ≫
        (F.obj ((F.obj A).obj B)).map d ≫ α =
      α' ≫ (F.map a).app ((F.obj B').obj D') ≫ (F.obj A).map ((F.map b).app D' ≫ (F.obj B).map d))
    (h' : (F.map tAB').app D' ≫ tL' ≫ q' = α' ≫ (F.obj A').map tBD' ≫ tR') :
    (F.map tAB).app D ≫ tL ≫ q = α ≫ (F.obj A).map tBD ≫ tR := by
  rw [← cancel_epi ((F.map ((F.map a).app B' ≫ (F.obj A).map b)).app D' ≫
    (F.obj ((F.obj A).obj B)).map d)]
  have e1 : ((F.map ((F.map a).app B' ≫ (F.obj A).map b)).app D' ≫
      (F.obj ((F.obj A).obj B)).map d) ≫ (F.map tAB).app D =
        (F.map tAB').app D' ≫ (F.map mAB).app D' ≫ (F.obj AB).map d := by
    rw [Category.assoc, NatTrans.naturality (F.map tAB) d, ← Category.assoc,
      ← NatTrans.comp_app, ← Functor.map_comp, Category.assoc, hAB, Functor.map_comp,
      NatTrans.comp_app, Category.assoc]
  have e2 : α' ≫ (F.map a).app ((F.obj B').obj D') ≫
      (F.obj A).map ((F.map b).app D' ≫ (F.obj B).map d) ≫ (F.obj A).map tBD =
        α' ≫ (F.obj A').map tBD' ≫ (F.map a).app BD' ≫ (F.obj A).map mBD := by
    rw [← (F.obj A).map_comp, Category.assoc, hBD, (F.obj A).map_comp, ← Category.assoc
      ((F.map a).app _), ← NatTrans.naturality (F.map a) tBD', Category.assoc]
  simp only [Category.assoc]
  rw [reassoc_of% e1, reassoc_of% hL, hq, reassoc_of% h', reassoc_of% hα, reassoc_of% e2, hR]

/-! ### The paste of a composition law with a right unit law -/

/-- **A composition law and a right unit law paste into a contraction law.** Over an arbitrary
monoidal category: if a morphism `cmp : H ⊗ D ⟶ P` satisfies the composition law `hC` against
`appP`, `ev` and `appU`, and `v : M ⟶ H` satisfies the right unit law `hUR` against `appU`, then
`v ▷ D ≫ cmp` contracts against `ev`.

Stated with every object and morphism a variable, and applied by `exact`: the derived-level
goals it is applied to mention the source of a derived internal Hom at two definitionally equal
spellings, across which no rewriting tactic fires, and one `exact` pays that crossing once. The
three moves are `CategoryTheory.MonoidalCategory.comp_whiskerRight`, the naturality of the
associator in its left variable, and the interchange law; no braiding and no coherence diagram
is used. -/
theorem paste_composition_unit {C : Type*} [Category C] [MonoidalCategory C]
    {M H D L P : C} (v : M ⟶ H) (cmp : H ⊗ D ⟶ P) (ev : D ⊗ L ⟶ 𝟙_ C)
    (appP : P ⊗ L ⟶ M) (appU : H ⊗ 𝟙_ C ⟶ M)
    (hC : cmp ▷ L ≫ appP = (α_ H D L).hom ≫ (H ◁ ev) ≫ appU)
    (hUR : v ▷ 𝟙_ C ≫ appU = (ρ_ M).hom) :
    (v ▷ D ≫ cmp) ▷ L ≫ appP = (α_ M D L).hom ≫ (M ◁ ev) ≫ (ρ_ M).hom := by
  rw [comp_whiskerRight, Category.assoc, hC, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, hUR]

end Stacks.Cohomology.DualityDescent

end
