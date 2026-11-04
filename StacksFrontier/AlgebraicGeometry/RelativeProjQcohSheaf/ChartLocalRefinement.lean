module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongrNaturality

/-!
# The local datum of the glueing of `ψ` at a refinement of a chart

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), `d` an integer, `f : T ⟶ S` a
test scheme and `L` an invertible `𝒪_T`-module. Step (1) of the proof of Tag 01NV glues the map
`ψ` of a quadruple out of the maps given on the members of a covering of `T` by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, whose compatibility
hypothesis compares two members on the sections over an open of `T` that both of them see. This
file discharges that hypothesis, reducing it to **two relations over a common refinement** of the
two members: the two identifications of the chart module differ by an isomorphism `β`, and `β`
carries the one pulled-back `ψ` to the other.

## The local datum, and what it is over a refinement

`...RelativeProjQcohSheaf.chartLocalApp` is a morphism of *restrictions*;
`...RelativeProjQcohSheaf.chartLocalApp_eq_ofPullback` writes it as
`Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` of a morphism of *inverse images*, and
`...RelativeProjQcohSheaf.chartLocalPullback` is that morphism. The content of the file is
`...RelativeProjQcohSheaf.transport_chartLocalPullback`: carrying it along a further open
immersion `k` produces the local datum of the inverse image of `ψ` along `k`, taken at the
identification `...RelativeProjQcohSheaf.refineChartIso` of the inverse image of the chart module
over the refinement. Three facts go into it and nothing else — the associativity coherence
`...RelativeProjQcohSheaf.compComparison_assoc` of the contraction of an iterated inverse image,
the definition of `...RelativeProjQcohSheaf.Twisting.pullbackApp`, and the composition law
`...RelativeProjQcohSheaf.laurentPullbackCongrIso_pullback` of the chart comparison.

The degreewise comparison of the integral tensor powers is functorial in the identification
(`...LaurentCongr.congrIso_trans_hom`), so two local data over one scheme built from
identifications differing by `β` agree as soon as the two families differ by the degreewise
comparison attached to `β`: that is
`...RelativeProjQcohSheaf.chartLocalPullback_eq_of_congrIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.chartLocalPullback`: the local datum of the
  glueing of `ψ` as a morphism of inverse images.
* `...RelativeProjQcohSheaf.refineChartIso`: the identification of the inverse image of the chart
  module over a refinement of the chart.
* `...RelativeProjQcohSheaf.refineApp`: the family of homogeneous components of a `ψ` pulled back
  to a refinement of its chart, read over the base morphism the refinement carries.

## Main results

* `...RelativeProjQcohSheaf.Quadruple.twisting_app_comp_congrIso_witness` and
  `...Quadruple.twisting_app_comp_congrIso_witnessOver`: **the canonical comparison of two
  strictly equivalent quadruples carries `ψ` to `ψ'` in every integral degree**, read through
  `...LaurentCongr.congrIso` rather than through the accompanying isomorphism of Laurent
  algebras. The two are the same in every degree by
  `...RelativeProjQcohSheaf.laurent_app_eq_of_app_one`, both having the given isomorphism of the
  invertible modules as their degree-one component.
* `...RelativeProjQcohSheaf.transport_chartLocalPullback`: **the local datum read over a
  refinement of its chart.**
* `...RelativeProjQcohSheaf.chartLocalPullback_eq_of_congrIso`: **two local data over one scheme
  whose identifications differ by `β` and whose families differ by `congrIso β` are equal.**
* `...RelativeProjQcohSheaf.localApp_chartLocalApp_eq`: **the compatibility hypothesis of
  `...ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the local data of the glueing of
  `ψ`**, from those two relations over a common refinement.

## Implementation notes

Every collapse of a composite is performed by `exact` against a helper stated in a bare category
with every object and morphism free (`transportCollapse`, `cancelThroughUnit`). That is the cure
this directory prescribes for the two `rfl`-equal, syntactically distinct spellings of the inverse
image of sheaves of modules on schemes — `AlgebraicGeometry.Scheme.Modules.pullback` and
`Stacks.RingedSpace.pullbackFunctor` of the underlying morphism of ringed spaces
(`...RelativeProjQcohSheaf.modulesPullback_eq_pullbackFunctor`) — together with the two spellings
`(k ≫ a) ≫ f` and `k ≫ a ≫ f` of a triple composite, which are equal by `rfl` and not
syntactically equal: a goal containing both is not type-correct at `implicit` transparency and
`rw` reports a failed pattern rather than the cause.

## No tag is claimed

Nothing here states a clause of a tag; the file transports a presentation of local morphism data
along a refinement of its chart.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T S V' V'' : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

namespace Quadruple

/-- **The canonical comparison of two strictly equivalent quadruples carries `ψ` to `ψ'` in every
integral degree, read through the degreewise comparison of the integral tensor powers.** -/
theorem twisting_app_comp_congrIso_witness {f : T ⟶ S} {P Q : Quadruple f A d}
    (h : StrictlyEquivalent P Q) (n : ℤ) :
    P.twisting.app n ≫ (congrIso (witness h) n).hom = Q.twisting.app n := by
  have hone : (laurentWitness h).hom.app 1 ≫ (oneIsoL Q.L).hom =
      (oneIsoL P.L).hom ≫ (witness h).hom := by
    have h1 : (laurentWitness h).hom.app 1 = P.oneIso.hom ≫ (witness h).hom ≫ Q.oneIso.inv :=
      laurentWitness_app_one h
    rw [h1]
    simp
  have hone' : (laurentCongrIso (witness h)).hom.app 1 ≫ (oneIsoL Q.L).hom =
      (oneIsoL P.L).hom ≫ (witness h).hom := by
    rw [laurentCongrIso_app_one]
    simp
  have key := laurent_app_eq_of_app_one hone hone' n
  refine Eq.trans (congrArg (fun z => P.twisting.app n ≫ z)
    ((key.trans (laurentCongrIso_app (witness h) n)).symm)) ?_
  exact twisting_app_comp_laurentWitness h n

/-- `twisting_app_comp_congrIso_witness` over base morphisms that are equal rather than
identical. -/
theorem twisting_app_comp_congrIso_witnessOver {g g' : T ⟶ S} {h : g = g'}
    {P : Quadruple g A d} {Q : Quadruple g' A d} (e : StrictlyEquivalentOver h P Q) (n : ℤ) :
    P.twisting.app n ≫ (congrIso (witnessOver e) n).hom =
      (Scheme.Modules.pullbackCongr h).hom.app (A.piece (n * d)) ≫ Q.twisting.app n := by
  subst h
  rw [ModuleHomGlue.pullbackCongr_rfl, witnessOver_rfl]
  simp only [Iso.refl_hom]
  exact twisting_app_comp_congrIso_witness _ n

end Quadruple

/-! ### The local datum as a morphism of inverse images -/

section Local

/-- **The local datum of the glueing of `ψ` as a morphism of inverse images**: the contraction of
the iterated inverse image on the source, the given family, and the chart comparison on the
target. `...RelativeProjQcohSheaf.chartLocalApp` is
`Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` of this. -/
def chartLocalPullback (f : T ⟶ S) (a : V' ⟶ T)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V'.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V'.toRingedSpace.presheaf (isSheafStruct V') L']
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (q : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (a ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent L').piece i) (i : ℤ) :
    (Scheme.Modules.pullback a).obj
        ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))) ⟶
      (Scheme.Modules.pullback a).obj ((laurent L).piece i) :=
  (Scheme.Modules.pullbackComp a f).hom.app (A.piece (i * d)) ≫ q i ≫
    (laurentPullbackCongrIso a L e i).inv

/-- `...RelativeProjQcohSheaf.chartLocalApp` is
`Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` of
`...RelativeProjQcohSheaf.chartLocalPullback`. -/
theorem chartLocalApp_eq_ofPullback_chartLocalPullback (f : T ⟶ S) (a : V' ⟶ T)
    [IsOpenImmersion a]
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V'.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V'.toRingedSpace.presheaf (isSheafStruct V') L']
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L')
    (q : ∀ i : ℤ, (pullbackFunctor (ringedSpaceHom (a ≫ f))).obj (A.piece (i * d)) ⟶
      (laurent L').piece i) (i : ℤ) :
    chartLocalApp f a A d L e q i =
      ModuleHomGlue.ofPullback a (chartLocalPullback f a A d L e q i) :=
  chartLocalApp_eq_ofPullback f a A d L e q i

/-- **The identification of the inverse image of the chart module over a refinement.** -/
def refineChartIso (a : V' ⟶ T) (k : V'' ⟶ V') {b : V'' ⟶ T} (hk : k ≫ a = b)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V'.toRingedSpace)}
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L') :
    (pullbackFunctor (ringedSpaceHom b)).obj L ≅
      (pullbackFunctor (ringedSpaceHom k)).obj L' :=
  ((Scheme.Modules.pullbackCongr hk).app L).symm ≪≫ compCongrIso a k L e

/-- Collapsing a five-fold composite against three identities, stated in a bare category with
every object and morphism free: the source identity, the definition of the degreewise pullback,
and the target identity. Applied by `exact` with every argument explicit, for the reason recorded
in `...RelativeProjQcohSheaf.reassocFivefold`. -/
private theorem transportCollapse {C : Type*} [Category C]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    (cc : X₁ ⟶ X₂) (pc : X₂ ⟶ X₃) (q : X₃ ⟶ Y₁) (lA : Y₁ ⟶ Y₂) (cm : Y₂ ⟶ Y₃)
    (m : X₂ ⟶ Y₂) (cmb : X₁ ≅ X₄) (ccb : X₄ ⟶ X₃) (lp : Y₁ ⟶ Y₄) (lB : Y₄ ⟶ Y₃)
    (q' : X₄ ⟶ Y₄)
    (hm : m = pc ≫ q ≫ lA) (h1 : cmb.inv ≫ cc ≫ pc = ccb) (h2 : ccb ≫ q ≫ lp = q')
    (h3 : lA ≫ cm = lp ≫ lB) :
    cc ≫ m ≫ cm = cmb.hom ≫ q' ≫ lB := by
  subst hm
  subst h2
  simp only [Category.assoc]
  rw [← h3, ← h1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **The family of homogeneous components of a `ψ` pulled back to a refinement of its chart**,
read over the base morphism the refinement carries. -/
def refineApp (f : T ⟶ S) (a : V' ⟶ T) (k : V'' ⟶ V') {b : V'' ⟶ T} (hb : b ≫ f = k ≫ a ≫ f)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    {L' : SheafOfModules.{u} (structureRingSheaf V'.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V'.toRingedSpace.presheaf (isSheafStruct V') L']
    (ψ : Twisting (a ≫ f) A d L') (j : ℤ) :
    (pullbackFunctor (ringedSpaceHom (b ≫ f))).obj (A.piece (j * d)) ⟶
      (laurent ((pullbackFunctor (ringedSpaceHom k)).obj L')).piece j :=
  (Scheme.Modules.pullbackCongr hb).hom.app (A.piece (j * d)) ≫ (ψ.pullback k).app j

/-- Cancelling a comparison against its inverse out of a three-fold composite, stated in a bare
category with every object and morphism free. -/
private theorem cancelThroughUnit {C : Type*} [Category C] {X Y Z W : C}
    (u : X ⟶ Y) (v : Y ⟶ Z) (w : Z ⟶ W) (D : X ⟶ W) (c : W ⟶ Z)
    (h : u ≫ v = D ≫ c) (hc : c ≫ w = CategoryStruct.id W) : u ≫ v ≫ w = D := by
  rw [← Category.assoc, h, Category.assoc, hc, Category.comp_id]

/-- **The local datum of the glueing of `ψ`, read over a refinement of the chart.** The transport
of `...RelativeProjQcohSheaf.chartLocalPullback` along `k` is the local datum built from the
inverse image of `ψ` along `k` and the identification
`...RelativeProjQcohSheaf.refineChartIso`.

The source half is the associativity coherence
`...RelativeProjQcohSheaf.compComparison_assoc` of the contraction of an iterated inverse image,
the target half is the composition law
`...RelativeProjQcohSheaf.laurentPullbackCongrIso_pullback` of the chart comparison, and the
middle is the definition of `...RelativeProjQcohSheaf.Twisting.pullbackApp`. -/
theorem transport_chartLocalPullback (f : T ⟶ S) (a : V' ⟶ T) (k : V'' ⟶ V')
    {b : V'' ⟶ T} (hk : k ≫ a = b) (hb : b ≫ f = k ≫ a ≫ f)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L' : SheafOfModules.{u} (structureRingSheaf V'.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V'.toRingedSpace.presheaf (isSheafStruct V') L']
    (e : (pullbackFunctor (ringedSpaceHom a)).obj L ≅ L') (ψ : Twisting (a ≫ f) A d L')
    (i : ℤ) :
    (Scheme.Modules.pullbackCongr hk).inv.app
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))) ≫
        (Scheme.Modules.pullbackComp k a).inv.app
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))) ≫
        (Scheme.Modules.pullback k).map (chartLocalPullback f a A d L e ψ.app i) ≫
        (Scheme.Modules.pullbackComp k a).hom.app ((laurent L).piece i) ≫
        (Scheme.Modules.pullbackCongr hk).hom.app ((laurent L).piece i) =
      chartLocalPullback f b A d L (refineChartIso a k hk L e)
        (refineApp f a k hb A d ψ) i := by
  subst hk
  have hid : (Scheme.Modules.pullbackCongr (rfl : k ≫ a = k ≫ a)) =
      Iso.refl (Scheme.Modules.pullback (k ≫ a)) := ModuleHomGlue.pullbackCongr_rfl
  have hcongr : (Scheme.Modules.pullbackCongr hb) =
      Iso.refl (Scheme.Modules.pullback (k ≫ a ≫ f)) := ModuleHomGlue.pullbackCongr_rfl
  have hR : refineChartIso a k (rfl : k ≫ a = k ≫ a) L e = compCongrIso a k L e := by
    have hrefl : ((Iso.refl (Scheme.Modules.pullback (k ≫ a))).app L).symm =
        Iso.refl ((Scheme.Modules.pullback (k ≫ a)).obj L) := rfl
    rw [refineChartIso, hid, hrefl]
    exact Iso.refl_trans _
  simp only [chartLocalPullback, refineApp, hR, hid, hcongr, Iso.refl_hom, Iso.refl_inv]
  simp only [← compComparison_eq_pullbackComp_inv, pullbackComp_hom_app_eq_compCmp]
  -- the three identities, in the inverse-image spelling of this directory
  have hca : (compCmp (k ≫ a) f (A.piece (i * d))).inv ≫
        compComparison k a ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))) =
      compComparison k (a ≫ f) (A.piece (i * d)) ≫
        (pullbackFunctor (ringedSpaceHom k)).map (compComparison a f (A.piece (i * d))) := by
    rw [← compComparison_eq_compCmp_inv]
    exact compComparison_assoc k a f (A.piece (i * d))
  have hc : (pullbackFunctor (ringedSpaceHom k)).map (compComparison a f (A.piece (i * d))) ≫
        (pullbackFunctor (ringedSpaceHom k)).map ((compCmp a f (A.piece (i * d))).hom) =
      CategoryStruct.id ((pullbackFunctor (ringedSpaceHom k)).obj
        ((pullbackFunctor (ringedSpaceHom (a ≫ f))).obj (A.piece (i * d)))) :=
    ((pullbackFunctor (ringedSpaceHom k)).map_comp _ _).symm.trans
      ((congrArg (pullbackFunctor (ringedSpaceHom k)).map
          (compComparison_comp_compCmp a f (A.piece (i * d)))).trans
        ((pullbackFunctor (ringedSpaceHom k)).map_id _))
  have h1 := cancelThroughUnit
    ((compCmp (k ≫ a) f (A.piece (i * d))).inv)
    (compComparison k a ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))))
    ((pullbackFunctor (ringedSpaceHom k)).map ((compCmp a f (A.piece (i * d))).hom))
    (compComparison k (a ≫ f) (A.piece (i * d)))
    ((pullbackFunctor (ringedSpaceHom k)).map (compComparison a f (A.piece (i * d))))
    hca hc
  have h3 : (pullbackFunctor (ringedSpaceHom k)).map (laurentPullbackCongrIso a L e i).inv ≫
        (compCmp k a ((laurent L).piece i)).hom =
      laurentPullback k L' i ≫
        (laurentPullbackCongrIso (k ≫ a) L (compCongrIso a k L e) i).inv := by
    refine (Iso.eq_comp_inv _).mpr ?_
    rw [Category.assoc, laurentPullbackCongrIso_pullback a k L e i, ← Category.assoc,
      ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact transportCollapse
    (compComparison k a ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (i * d))))
    ((pullbackFunctor (ringedSpaceHom k)).map ((compCmp a f (A.piece (i * d))).hom))
    ((pullbackFunctor (ringedSpaceHom k)).map (ψ.app i))
    ((pullbackFunctor (ringedSpaceHom k)).map (laurentPullbackCongrIso a L e i).inv)
    ((compCmp k a ((laurent L).piece i)).hom)
    ((pullbackFunctor (ringedSpaceHom k)).map
      ((compCmp a f (A.piece (i * d))).hom ≫ ψ.app i ≫ (laurentPullbackCongrIso a L e i).inv))
    (compCmp (k ≫ a) f (A.piece (i * d)))
    (compComparison k (a ≫ f) (A.piece (i * d)))
    (laurentPullback k L' i)
    ((laurentPullbackCongrIso (k ≫ a) L (compCongrIso a k L e) i).inv)
    ((ψ.pullback k).app i)
    (((pullbackFunctor (ringedSpaceHom k)).map_comp _ _).trans
      (congrArg (fun z => (pullbackFunctor (ringedSpaceHom k)).map
          ((compCmp a f (A.piece (i * d))).hom) ≫ z)
        ((pullbackFunctor (ringedSpaceHom k)).map_comp _ _)))
    h1 rfl h3

/-- **Two local data over one scheme, built from identifications of the chart module that differ
by an isomorphism carrying the one family to the other, are the same.** The chart comparison
`...RelativeProjQcohSheaf.laurentPullbackCongrIso` is functorial in the identification
(`...LaurentCongr.congrIso_trans_hom`), so the two comparisons differ by exactly the degreewise
comparison the two families differ by, and it cancels. -/
theorem chartLocalPullback_eq_of_congrIso (f : T ⟶ S) (b : V'' ⟶ T)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {L₁ L₂ : SheafOfModules.{u} (structureRingSheaf V''.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible V''.toRingedSpace.presheaf (isSheafStruct V'') L₁]
    [Stacks.SheafOfModules.IsInvertible V''.toRingedSpace.presheaf (isSheafStruct V'') L₂]
    (E₁ : (pullbackFunctor (ringedSpaceHom b)).obj L ≅ L₁)
    (E₂ : (pullbackFunctor (ringedSpaceHom b)).obj L ≅ L₂) (β : L₁ ≅ L₂)
    (hβ : E₁ ≪≫ β = E₂)
    (q₁ : ∀ j : ℤ, (pullbackFunctor (ringedSpaceHom (b ≫ f))).obj (A.piece (j * d)) ⟶
      (laurent L₁).piece j)
    (q₂ : ∀ j : ℤ, (pullbackFunctor (ringedSpaceHom (b ≫ f))).obj (A.piece (j * d)) ⟶
      (laurent L₂).piece j)
    (hq : ∀ j : ℤ, q₁ j ≫ (congrIso β j).hom = q₂ j) (i : ℤ) :
    chartLocalPullback f b A d L E₁ q₁ i = chartLocalPullback f b A d L E₂ q₂ i := by
  have hlpc : (laurentPullbackCongrIso b L E₁ i).hom ≫ (congrIso β i).hom =
      (laurentPullbackCongrIso b L E₂ i).hom := by
    rw [laurentPullbackCongrIso_hom, laurentPullbackCongrIso_hom, Category.assoc,
      congrIso_trans_hom, hβ]
  have hinv : (laurentPullbackCongrIso b L E₁ i).inv =
      (congrIso β i).hom ≫ (laurentPullbackCongrIso b L E₂ i).inv :=
    (Iso.eq_comp_inv _).mpr ((Iso.inv_comp_eq _).mpr hlpc.symm)
  exact congrArg (fun z => (Scheme.Modules.pullbackComp b f).hom.app (A.piece (i * d)) ≫ z)
    ((congrArg (fun z => q₁ i ≫ z) hinv).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun z => z ≫ (laurentPullbackCongrIso b L E₂ i).inv) (hq i))))

/-- **The compatibility hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the local data of
the glueing of `ψ`.** Over a common refinement of two charts, the two identifications of the
chart module differ by an isomorphism `β` which carries the one pulled-back family to the other;
then the two local data have the same action on the sections over an open of `T` seen by both
charts.

Nothing beyond those two relations enters:
`...RelativeProjQcohSheaf.transport_chartLocalPullback` reads each local datum over the
refinement, `...RelativeProjQcohSheaf.chartLocalPullback_eq_of_congrIso` identifies the two there,
and `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement` descends the
identity to sections. -/
theorem localApp_chartLocalApp_eq (f : T ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
    {Z₁ Z₂ Z : Scheme.{u}} (g₁ : Z₁ ⟶ T) [IsOpenImmersion g₁] (g₂ : Z₂ ⟶ T) [IsOpenImmersion g₂]
    {g : Z ⟶ T} [IsOpenImmersion g]
    (k₁ : Z ⟶ Z₁) [IsOpenImmersion k₁] (hk₁ : k₁ ≫ g₁ = g)
    (k₂ : Z ⟶ Z₂) [IsOpenImmersion k₂] (hk₂ : k₂ ≫ g₂ = g)
    (hb₁ : g ≫ f = k₁ ≫ g₁ ≫ f) (hb₂ : g ≫ f = k₂ ≫ g₂ ≫ f)
    {L₁ : SheafOfModules.{u} (structureRingSheaf Z₁.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible Z₁.toRingedSpace.presheaf (isSheafStruct Z₁) L₁]
    {L₂ : SheafOfModules.{u} (structureRingSheaf Z₂.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible Z₂.toRingedSpace.presheaf (isSheafStruct Z₂) L₂]
    (e₁ : (pullbackFunctor (ringedSpaceHom g₁)).obj L ≅ L₁)
    (e₂ : (pullbackFunctor (ringedSpaceHom g₂)).obj L ≅ L₂)
    (ψ₁ : Twisting (g₁ ≫ f) A d L₁) (ψ₂ : Twisting (g₂ ≫ f) A d L₂)
    (β : (pullbackFunctor (ringedSpaceHom k₁)).obj L₁ ≅
      (pullbackFunctor (ringedSpaceHom k₂)).obj L₂)
    (hE : refineChartIso g₁ k₁ hk₁ L e₁ ≪≫ β = refineChartIso g₂ k₂ hk₂ L e₂)
    (hq : ∀ j : ℤ, refineApp f g₁ k₁ hb₁ A d ψ₁ j ≫ (congrIso β j).hom =
      refineApp f g₂ k₂ hb₂ A d ψ₂ j)
    (i : ℤ) {W₁ : Z₁.Opens} {W₂ : Z₂.Opens} {W : Z.Opens} {V : T.Opens}
    (h₁ : g₁ ''ᵁ W₁ = V) (h₂ : g₂ ''ᵁ W₂ = V) (h : g ''ᵁ W = V) :
    ModuleHomGlue.localApp g₁ (chartLocalApp f g₁ A d L e₁ ψ₁.app i) h₁ =
      ModuleHomGlue.localApp g₂ (chartLocalApp f g₂ A d L e₂ ψ₂.app i) h₂ := by
  rw [chartLocalApp_eq_ofPullback_chartLocalPullback,
    chartLocalApp_eq_ofPullback_chartLocalPullback]
  refine ModuleHomGlue.localApp_ofPullback_eq_of_refinement g₁ g₂ k₁ hk₁ k₂ hk₂
    (chartLocalPullback f g₁ A d L e₁ ψ₁.app i) (chartLocalPullback f g₂ A d L e₂ ψ₂.app i)
    (chartLocalPullback f g A d L (refineChartIso g₁ k₁ hk₁ L e₁)
      (refineApp f g₁ k₁ hb₁ A d ψ₁) i)
    (transport_chartLocalPullback f g₁ k₁ hk₁ hb₁ A d L e₁ ψ₁ i) ?_ h₁ h₂ h
  refine Eq.trans (transport_chartLocalPullback f g₂ k₂ hk₂ hb₂ A d L e₂ ψ₂ i) ?_
  exact (chartLocalPullback_eq_of_congrIso f g A d L (refineChartIso g₁ k₁ hk₁ L e₁)
    (refineChartIso g₂ k₂ hk₂ L e₂) β hE (refineApp f g₁ k₁ hb₁ A d ψ₁)
    (refineApp f g₂ k₂ hb₂ A d ψ₂) hq i).symm

end Local

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
