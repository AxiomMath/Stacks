module

public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDualTriangleFirstMapSectionsCore
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitudeModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality

/-!
# Tag 0E2N by adjointness is its model map; Tag 0B4C at a perfect `Ri_* 𝒪_Z`

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces. For `K` and `M` in `D(𝒪_X)` there
are two descriptions in this library of the canonical map

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

of [Stacks, Tag 0E2N]: `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap`, the map
adjoint under `i_* ⊣ R ℰom(𝒪_Z, -)` ([Stacks, Tag 0A76]) to the projection formula followed by
the trace, and `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomModelMap`, the class of
a morphism of complexes between a K-injective model of `K` and a K-flat model of `M`, whose
pushforward is the morphism of [Stacks, Tag 0BYR]. **This file proves that they are equal**, for
every `K` and `M` and every closed quotient morphism, and draws the consequences for the
canonical map of [Stacks, Tag 0B4C].

## Main results

* `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap_eq_modelMap`: the two
  descriptions agree. The model map satisfies the adjunction equation
  (`map_tensorDerivedSheafHomModelMap_comp_counit`), which determines the canonical map
  (`tensorDerivedSheafHomMap_unique`).
* `Stacks.Duality.TensorHomTorAmplitude.isIso_tensorDerivedSheafHomMap_of_isPerfect`: when
  `Ri_* 𝒪_Z` is perfect, the canonical map is an isomorphism for every `K` and `M`: after the
  identification it is the diagonal of [Stacks, Tag 0BYS] at `(M, K, Ri_* 𝒪_Z)`, which is
  invertible at a perfect source by [Stacks, Tag 0ATN] part (1).
* `…ClosedQuotientMorphismOfRingedSpaces`
  `.derivedPullbackTensorSheafHomMap_eq_tensorDerivedSheafHomMap`:
  the map of [Stacks, Tag 0B4C] is that of [Stacks, Tag 0E2N] at the structure sheaf, between the
  commutativity constraint on `D(𝒪_Z)` and the left unit constraint on `D(𝒪_X)`.
* `…ClosedQuotientMorphismOfRingedSpaces.derivedPullbackTensorSheafHomMap_natural`: the map of
  [Stacks, Tag 0B4C] is natural in `K`.
* `…ClosedQuotientMorphismOfRingedSpaces.isIso_derivedPullbackTensorSheafHomMap_of_isPerfect`:
  the map of [Stacks, Tag 0B4C] is an isomorphism for every `K` when `Ri_* 𝒪_Z` is perfect. For
  the closed immersion of an effective Cartier divisor this is the computation of
  [Stacks, Tag 0AA4].

## The proof of the identification

The adjunction equation is an identity in `D(𝒪_X)` between two morphisms out of
`Ri_*(R ℰom(𝒪_Z, K) ⊗^L Li^*M)`, and both sides are computed on the models.

* The model map, pushed forward, is the class of `pushedMap`, and the trace at the class of the
  K-injective `J` is the class of the degreewise trace (`map_modelIso_inv_comp_counit`). At the
  level of complexes, the identification of [Stacks, Tag 0E2I] followed by the trace is
  evaluation at the unit section of `i_* 𝒪_Z` (`pushHomIso_inv_comp_modelTrace`, from the identity
  of sections behind [Stacks, Tag 0B4B]); the morphism of [Stacks, Tag 0BYR] followed by that
  evaluation is the flat model tensored with the same evaluation
  (`AlgebraicGeometry.RingedSite`
  `.derivedTensorHomMapOfModels_comp_homMap_comp_structureSheafHomEvaluation`).
  So the left-hand side is the inverse complex-level projection formula followed by the model
  trace on `I` tensored with `A` (`pushedMap_comp_modelTrace`).
* On the right-hand side, the projection-formula map of [Stacks, Tag 0B53] at the models is the
  complex-level projection formula
  (`…ClosedEmbeddingProjectionFormulaComplexes.projectionFormulaMap_eq_derivedModelIso`), the
  comparison of the two models of pushforward of [Stacks, Tag 0E2K] at the class of a complex is
  the identification of `i_*` followed by the comparison with the derived pushforward
  (`derivedPushforwardComparison_hom_app_Q`), and the trace at `K` is again the model trace
  (`pushforwardComparisonQ_comp_counit_injModel`).

The two sides then agree by the naturality of the K-flat comparison in its left complex.

## Implementation notes

In this context the ringed-space spelling `structureSheafRing S.X` and the site spelling
`(ambientRingedSite S).ringSheaf` of one sheaf of rings, and the spellings `S.X.sheaf` and
`Sheaf (Opens.grothendieckTopology _) CommRingCat` of its structure sheaf, are definitionally but
not reducibly equal, so most goals here are not type-correct at `implicit` transparency and `rw`
fails on them; a statement mixing them may also exhaust the elaboration budget when its two sides
are unified as a whole. Every assembly below is therefore made through a lemma about composites in
a bare category (or across a bare functor), whose hypotheses are the individual identities stated
by the library and are matched against them by unification at default transparency; composites
whose endpoints must be named are given as abbreviations with their type written out
(`srcCmp`, `mateModelSource`).

## References

* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0B4C](https://stacks.math.columbia.edu/tag/0B4C)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSite

section InterchangeUnit

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})

/-- **The interchange morphism of [Stacks, Tag 0BYR] out of `O[0]`, followed by evaluation at the
unit section, is `A` tensored with evaluation at the unit section.** Both sides send the pure
tensor of a section `a` of `A` and a section `φ` of `SheafHom(O[0], I)` to `a ⊗ φ(1)`. -/
theorem tensorHomInterchange_comp_structureSheafHomEvaluation
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorHomInterchange X A I (structureSheafComplex X) ≫
        structureSheafHomEvaluation X (tensorTotal X A I) =
      tensorTotalMap X (𝟙 A) (structureSheafHomEvaluation X I) := by
  refine tensorTotal_hom_ext X fun U t r a φ => ?_
  rw [HomologicalComplex.comp_f, comp_val_app_apply', structureSheafHomEvaluation_apply,
    tensorHomInterchange_applyHomSection X A I (structureSheafComplex X) U t r 0 r (t + r)
      (zero_add r) (by omega) a φ, tensorTotalMap_tensorTotalSection,
    ← structureSheafHomEvaluation_apply]
  rfl

/-- **The model map of [Stacks, Tag 0BYR] followed by evaluation along a unit.** For a morphism of
complexes `cu : O[0] ⟶ E`, the complex-level morphism `Tot(A ⊗ SheafHom(E, I)) ⟶ SheafHom(E, J)`
followed by restriction along `cu` and evaluation at the unit section is `A` tensored with the
same evaluation on `SheafHom(E, I)`, followed by `q`. -/
theorem derivedTensorHomMapOfModels_comp_homMap_comp_structureSheafHomEvaluation
    {A I E J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (cu : structureSheafComplex X ⟶ E) (q : tensorTotal X A I ⟶ J) :
    derivedTensorHomMapOfModels X (N := E) q ≫ homMap X cu (𝟙 J) ≫
        structureSheafHomEvaluation X J =
      tensorTotalMap X (𝟙 A) (homMap X cu (𝟙 I) ≫ structureSheafHomEvaluation X I) ≫ q := by
  rw [← Category.assoc, derivedTensorHomMapOfModels_naturality_source X cu q, Category.assoc,
    derivedTensorHomMapOfModels, Category.assoc, structureSheafHomEvaluation_naturality,
    ← Category.assoc (tensorHomInterchange X A I (structureSheafComplex X)),
    tensorHomInterchange_comp_structureSheafHomEvaluation, ← Category.assoc,
    tensorTotalMap_comp, Category.comp_id]

end InterchangeUnit

end AlgebraicGeometry.RingedSite

/-- A rearrangement of composites in a bare category, used to assemble the complex-level
identity `pushedMap_comp_modelTrace` without rewriting under mixed spellings. -/
private theorem chain₇ {C : Type*} [Category C]
    {P₀ P₁ P₂ P₂' P₃ P₃' P₄ P₄' P₅ P₆ J : C}
    {pm : P₀ ⟶ P₆} {cpf : P₀ ⟶ P₁} {tph : P₁ ⟶ P₂} {fl : P₂ ⟶ P₃} {tt : P₃ ⟶ P₄}
    {om : P₄ ⟶ P₅} {ph : P₅ ⟶ P₆} {mt : P₆ ⟶ J} {ev : P₅ ⟶ J} {ttm : P₄ ⟶ P₄'} {q : P₄' ⟶ J}
    {bev : P₃ ⟶ P₃'} {tt' : P₃' ⟶ P₄'} {tev : P₂ ⟶ P₂'} {fl' : P₂' ⟶ P₃'} {tmt : P₁ ⟶ P₂'}
    (e0 : pm = (cpf ≫ tph ≫ fl ≫ tt) ≫ om ≫ ph) (h2 : ph ≫ mt = ev)
    (h3 : om ≫ ev = ttm ≫ q) (h4 : tt ≫ ttm = bev ≫ tt') (h5 : tev ≫ fl' = fl ≫ bev)
    (e7 : tmt = tph ≫ tev) :
    pm ≫ mt = cpf ≫ tmt ≫ fl' ≫ tt' ≫ q := by
  subst e0 e7
  simp only [Category.assoc, h2, h3, reassoc_of% h4, reassoc_of% h5]

/-- If `a ≫ x = y` and `a` has a left inverse `b`, then `x = b ≫ y`. -/
private theorem eq_comp_of_comp_eq_of_inv_comp {C : Type*} [Category C] {P Q R : C}
    {a : P ⟶ Q} {b : Q ⟶ P} {x : Q ⟶ R} {y : P ⟶ R} (hb : b ≫ a = 𝟙 _) (h : a ≫ x = y) :
    x = b ≫ y := by
  rw [← h, ← Category.assoc, hb, Category.id_comp]

/-- Transport of a commuting square `f ≫ p = q ≫ g` to the square `g ≫ j = i ≫ f`, where `i` and
`j` are sections of `q` and `p`. -/
private theorem comp_eq_of_square_of_sections {C : Type*} [Category C] {A B A' B' : C}
    {f : A ⟶ B} {p : B ⟶ B'} {q : A ⟶ A'} {g : A' ⟶ B'} {i : A' ⟶ A} {j : B' ⟶ B}
    (h : f ≫ p = q ≫ g) (hq : i ≫ q = 𝟙 _) (hp : p ≫ j = 𝟙 _) : g ≫ j = i ≫ f := by
  rw [← Category.id_comp (g ≫ j), ← hq, Category.assoc, ← reassoc_of% h, hp,
    Category.comp_id]

/-- A rearrangement in a bare category, used for `derivedPushforwardComparison_hom_app_Q`. -/
private theorem chainL5 {C : Type*} [Category C] {GQ GQh RQ RQh QF W : C}
    {cmpQ : GQ ⟶ RQ} {cmpQh : GQh ⟶ RQh} {gq : GQh ⟶ GQ} {gqi : GQ ⟶ GQh} {rq : RQh ⟶ RQ}
    {fac : GQ ⟶ QF} {qX : W ⟶ QF} {qXi : QF ⟶ W} {fh : GQh ⟶ W} {fi : W ⟶ GQh}
    {un : W ⟶ RQh}
    (hfac : fi ≫ cmpQh = un) (hnat : gq ≫ cmpQ = cmpQh ≫ rq) (hh : fh ≫ qX = gq ≫ fac)
    (hf : fh ≫ fi = 𝟙 _) (hq : qX ≫ qXi = 𝟙 _) (hg' : gqi ≫ gq = 𝟙 _) :
    cmpQ = fac ≫ qXi ≫ un ≫ rq := by
  rw [eq_comp_of_comp_eq_of_inv_comp hg' hh.symm, ← hfac]
  simp only [Category.assoc, reassoc_of% hq, reassoc_of% hf]
  rw [← hnat, reassoc_of% hg']

/-- A rearrangement in a bare category, used for `pushforwardComparisonQ_comp_counit_injModel`. -/
private theorem chainD1 {C : Type*} [Category C] {PQ QI RQ RG PG Kc PQI QIc : C}
    {fac : PQ ⟶ QI} {facI : QI ⟶ PQ} {pfc : QI ⟶ RQ} {cmpH : PQ ⟶ RQ} {cq : RQ ⟶ PQ}
    {Rm : RQ ⟶ RG} {cg : RG ⟶ PG} {Pm : PQ ⟶ PG} {eps : PG ⟶ Kc} {m1 : PQ ⟶ PQI}
    {m2 : PQI ⟶ PG} {eQ : PQI ⟶ QIc} {inj : QIc ⟶ Kc} {qmt : QI ⟶ QIc}
    (h5 : cmpH = fac ≫ pfc) (hfac : facI ≫ fac = 𝟙 _) (hci : cmpH ≫ cq = 𝟙 _)
    (hn : Rm ≫ cg = cq ≫ Pm) (hPm : Pm = m1 ≫ m2) (hc : m2 ≫ eps = eQ ≫ inj)
    (h1 : m1 ≫ eQ = fac ≫ qmt) :
    pfc ≫ Rm ≫ cg ≫ eps = qmt ≫ inj := by
  rw [eq_comp_of_comp_eq_of_inv_comp hfac h5.symm, Category.assoc, reassoc_of% hn,
    reassoc_of% hci, hPm, Category.assoc, hc, reassoc_of% h1, reassoc_of% hfac]

/-- A rearrangement in a bare category, used for `Q_map_comp_tensorModelIso_inv`. -/
private theorem chainG7 {C : Type*} [Category C] {A B₀ B₁ B₂ B₃ : C} {T : A ≅ B₃}
    {a₁ : A ⟶ B₀} {a₁' : B₀ ⟶ A} {a₂ : B₀ ⟶ B₁} {a₂' : B₁ ⟶ B₀} {c : B₁ ⟶ B₂} {c' : B₂ ⟶ B₁}
    {x : B₂ ⟶ B₃}
    (hT : T.hom = a₁ ≫ a₂ ≫ c ≫ x) (h₁ : a₁' ≫ a₁ = 𝟙 _) (h₂ : a₂' ≫ a₂ = 𝟙 _)
    (h₃ : c' ≫ c = 𝟙 _) :
    x ≫ T.inv = c' ≫ a₂' ≫ a₁' := by
  rw [Iso.comp_inv_eq, hT, Category.assoc, Category.assoc, reassoc_of% h₁, reassoc_of% h₂,
    reassoc_of% h₃]

/-- A rearrangement across a functor, used for `srcCmp_comp_inv_projectionFormulaMap`. -/
private theorem chainD2 {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {c₀ c₁ c₂ c₃ c₂' : C} {sIinv : c₀ ⟶ c₃} {tmh : c₀ ⟶ c₁} {lfl : c₁ ⟶ c₂} {ze' : c₂ ⟶ c₃}
    {ze : c₁ ⟶ c₂'} {lfl' : c₂' ⟶ c₃}
    {d₁ d₂ d₃ d₄ d₅ e₀ : D}
    {a : e₀ ⟶ F.obj c₀} {pfQ : d₁ ⟶ F.obj c₁} {smiInv : d₁ ⟶ d₂} {smiHom : d₂ ⟶ d₁}
    {qc : d₂ ⟶ e₀} {qci : e₀ ⟶ d₂} {xe : d₁ ⟶ d₃} {pfQA : d₃ ⟶ F.obj c₂'} {xf : d₃ ⟶ d₄}
    {pfM : d₄ ⟶ F.obj c₃} {pfMi : F.obj c₃ ⟶ d₄} {cRi : d₂ ⟶ d₅} {xp : d₅ ⟶ d₁}
    (hsI : sIinv = (tmh ≫ lfl) ≫ ze') (h8 : F.map (lfl ≫ ze') = F.map (ze ≫ lfl'))
    (hpf : pfQ = smiInv ≫ qc ≫ a ≫ F.map tmh)
    (h4 : xe ≫ pfQA = pfQ ≫ F.map ze) (h5 : xf ≫ pfM = pfQA ≫ F.map lfl')
    (hsmi : smiHom ≫ smiInv = 𝟙 _) (hq : qci ≫ qc = 𝟙 _) (hsmiHom : smiHom = cRi ≫ xp)
    (hpfi : pfM ≫ pfMi = 𝟙 _) :
    (a ≫ F.map sIinv) ≫ pfMi = qci ≫ cRi ≫ xp ≫ xe ≫ xf := by
  have key : a ≫ F.map sIinv = (qci ≫ smiHom ≫ xe ≫ xf) ≫ pfM := by
    rw [hsI, Category.assoc, F.map_comp, h8, F.map_comp]
    simp only [Category.assoc]
    rw [h5, reassoc_of% h4, hpf]
    simp only [Category.assoc]
    rw [reassoc_of% hsmi, reassoc_of% hq]
  rw [key, Category.assoc, hpfi, Category.comp_id, hsmiHom]
  simp only [Category.assoc]

/-- The rearrangement assembling the adjunction equation of the model map. -/
private theorem chainMate {C D : Type*} [Category C] [Category D] {G : C ⥤ D}
    {z₀ z₁ z₂ z₃ z₄ : C} {sIh : z₀ ⟶ z₁} {sIi : z₁ ⟶ z₀} {zq : z₁ ⟶ z₂} {mJi : z₂ ⟶ z₃}
    {Rti : z₃ ⟶ z₄} {mm : z₀ ⟶ z₄}
    {KM QJ P PJ QS QT1 QT2 QT3 Y1 Y2 Y3 Y4 RS RT X0 X1 X2 X3 X4 : D}
    {εKM : G.obj z₄ ⟶ KM} {εJ : G.obj z₃ ⟶ QJ} {tmIi : QJ ⟶ KM} {facJ : G.obj z₂ ⟶ PJ}
    {QmTJ : PJ ⟶ QJ} {facS : G.obj z₁ ⟶ P} {Qpush : P ⟶ PJ} {Qcpfi : P ⟶ QS}
    {QTmt : QS ⟶ QT1} {Qfl : QT1 ⟶ QT2} {Qtti : QT2 ⟶ QT3} {Qq : QT3 ⟶ QJ}
    {cRIi : QT1 ⟶ Y1} {cRIh : Y1 ⟶ QT1} {tka : Y1 ⟶ Y2} {tei : Y2 ⟶ KM} {cRHi : QS ⟶ Y3}
    {cRHh : Y3 ⟶ QS} {tmt : Y3 ⟶ Y1} {idp : Y1 ⟶ Y1}
    {mate : G.obj z₀ ⟶ KM} {cmpT : G.obj z₀ ⟶ RT} {ipf : RT ⟶ X0} {tci : X0 ⟶ X1}
    {teps : X1 ⟶ KM} {cmpS : G.obj z₁ ⟶ RS} {RfsIi : RS ⟶ RT} {pcQS : P ⟶ RS}
    {tpc : Y3 ⟶ X2} {tre : X2 ⟶ X3} {tk : X3 ⟶ X0} {tci' : X3 ⟶ X4} {tk' : X4 ⟶ X1}
    {teps' : X4 ⟶ Y4} {tkK : Y4 ⟶ KM} {tei' : Y1 ⟶ Y4}
    (hθ : mm = sIh ≫ zq ≫ mJi ≫ Rti)
    (hcn : G.map Rti ≫ εKM = εJ ≫ tmIi) (hL1J : G.map mJi ≫ εJ = facJ ≫ QmTJ)
    (hfn : G.map zq ≫ facJ = facS ≫ Qpush)
    (hpz : Qpush ≫ QmTJ = Qcpfi ≫ QTmt ≫ Qfl ≫ Qtti ≫ Qq)
    (hG7 : Qfl ≫ Qtti ≫ Qq ≫ tmIi = cRIi ≫ tka ≫ tei)
    (hcRraw : tmt ≫ idp ≫ cRIh = cRHh ≫ QTmt) (hidp : idp = 𝟙 _) (hcRI : cRIh ≫ cRIi = 𝟙 _)
    (hcRH : cRHi ≫ cRHh = 𝟙 _)
    (eR : mate = cmpT ≫ ipf ≫ tci ≫ teps) (hcmp : G.map sIi ≫ cmpT = cmpS ≫ RfsIi)
    (hPs : G.map sIh ≫ G.map sIi = 𝟙 _)
    (hL5 : cmpS = facS ≫ pcQS) (hD2 : (pcQS ≫ RfsIi) ≫ ipf = Qcpfi ≫ cRHi ≫ tpc ≫ tre ≫ tk)
    (hn1 : tk ≫ tci = tci' ≫ tk') (hn2 : tk' ≫ teps = teps' ≫ tkK) (hn3 : tka ≫ tei = tei' ≫ tkK)
    (hD1 : tpc ≫ tre ≫ tci' ≫ teps' = tmt ≫ tei') :
    G.map mm ≫ εKM = mate := by
  have hcR : QTmt ≫ cRIi = cRHi ≫ tmt := by
    rw [hidp, Category.id_comp] at hcRraw
    exact comp_eq_of_square_of_sections hcRraw hcRH hcRI
  rw [hθ, eR, eq_comp_of_comp_eq_of_inv_comp hPs hcmp, hL5]
  simp only [Functor.map_comp, Category.assoc]
  rw [hcn, reassoc_of% hL1J, reassoc_of% hfn, reassoc_of% hpz, hG7, reassoc_of% hcR, hn3]
  have hD2' := hD2
  simp only [Category.assoc] at hD2'
  rw [reassoc_of% hD2', reassoc_of% hn1, hn2, reassoc_of% hD1]

/-- A functor applied to a fivefold composite. -/
private theorem functor_map_comp₅ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c d e f : C} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d) (x : d ⟶ e) (y : e ⟶ f) :
    F.map (u ≫ v ≫ w ≫ x ≫ y) = F.map u ≫ F.map v ≫ F.map w ≫ F.map x ≫ F.map y := by
  simp only [Functor.map_comp]

/-- A functor into a functor category applied to a fourfold composite, then evaluated. -/
private theorem functor_map_app_comp₄ {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) {a b c d e : C} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d) (x : d ⟶ e) (y : D) :
    (F.map (u ≫ v ≫ w ≫ x)).app y =
      (F.map u).app y ≫ (F.map v).app y ≫ (F.map w).app y ≫ (F.map x).app y := by
  simp only [Functor.map_comp, NatTrans.comp_app]

/-- A rearrangement across a functor, used for
`derivedPullbackTensorSheafHomMap_eq_tensorDerivedSheafHomMap`. -/
private theorem chainB {C D : Type*} [Category C] [Category D] {G : C ⥤ D}
    {c₀ c₁ c₂ c₃ : C} {d₀ d₁ d₂ d₃ d₄ : D} {b : c₀ ⟶ c₁} {θ : c₁ ⟶ c₂} {gl : c₂ ⟶ c₃}
    {mm : c₀ ⟶ c₃} {e : G.obj c₃ ⟶ d₄} {e' : G.obj c₂ ⟶ d₃} {l : d₃ ⟶ d₄}
    {c : G.obj c₁ ⟶ d₀} {i : d₀ ⟶ d₁} {t₁ : d₁ ⟶ d₂} {t₂ : d₂ ⟶ d₃} {τm : G.obj c₀ ⟶ d₄}
    (hm : mm = b ≫ θ ≫ gl) (hc : G.map gl ≫ e = e' ≫ l) (hθ : G.map θ ≫ e' = c ≫ i ≫ t₁ ≫ t₂)
    (hτ : τm = G.map b ≫ c ≫ i ≫ t₁ ≫ t₂ ≫ l) :
    G.map mm ≫ e = τm := by
  rw [hm, hτ, G.map_comp, G.map_comp, Category.assoc, Category.assoc, hc, reassoc_of% hθ]

/-- A rearrangement across a functor, used for `derivedPullbackTensorSheafHomMateMap_natural`. -/
private theorem chainN {C D : Type*} [Category C] [Category D] {G : C ⥤ D}
    {a₀ a₁ b₀ b₁ : C} {d₀ d₁ e₀ e₁ f₀ f₁ g₀ g₁ K L : D}
    {x : a₀ ⟶ b₀} {bK : a₀ ⟶ a₁} {bL : b₀ ⟶ b₁} {y : a₁ ⟶ b₁}
    {cK : G.obj a₁ ⟶ d₀} {cL : G.obj b₁ ⟶ d₁} {ry : d₀ ⟶ d₁}
    {pK : e₀ ⟶ d₀} {pL : e₁ ⟶ d₁} {ipK : d₀ ⟶ e₀} {ipL : d₁ ⟶ e₁} {tk₀ : e₀ ⟶ e₁}
    {uK : e₀ ⟶ f₀} {uL : e₁ ⟶ f₁} {tk₁ : f₀ ⟶ f₁} {vK : f₀ ⟶ g₀} {vL : f₁ ⟶ g₁}
    {tk₂ : g₀ ⟶ g₁} {lK : g₀ ⟶ K} {lL : g₁ ⟶ L} {k : K ⟶ L} {θK : G.obj a₀ ⟶ K}
    {θL : G.obj b₀ ⟶ L}
    (hK : θK = G.map bK ≫ cK ≫ ipK ≫ uK ≫ vK ≫ lK)
    (hL : θL = G.map bL ≫ cL ≫ ipL ≫ uL ≫ vL ≫ lL)
    {i₁ : b₀ ⟶ b₀} {i₂ : a₁ ⟶ a₁}
    (hb : x ≫ i₁ ≫ bL = bK ≫ i₂ ≫ y) (hi₁ : i₁ = 𝟙 _) (hi₂ : i₂ = 𝟙 _)
    (hc : G.map y ≫ cL = cK ≫ ry) (hr : tk₀ ≫ pL = pK ≫ ry)
    (hpK : ipK ≫ pK = 𝟙 _) (hpL : pL ≫ ipL = 𝟙 _)
    (h1 : tk₀ ≫ uL = uK ≫ tk₁) (h2 : tk₁ ≫ vL = vK ≫ tk₂) (hl : tk₂ ≫ lL = lK ≫ k) :
    G.map x ≫ θL = θK ≫ k := by
  have hip := comp_eq_of_square_of_sections hr hpK hpL
  rw [hi₁, hi₂, Category.id_comp, Category.id_comp] at hb
  rw [hK, hL, ← G.map_comp_assoc, hb, G.map_comp, Category.assoc, reassoc_of% hc,
    reassoc_of% hip, reassoc_of% h1, reassoc_of% h2, hl]
  simp only [Category.assoc]

namespace Stacks.Duality.TensorHomTorAmplitude

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The trace of [Stacks, Tag 0A76] on the model `homZ F` of `R ℰom(𝒪_Z, F)`**, at the level of
complexes: the pushforward of evaluation at the unit section on `Z`, followed by the degreewise
underived trace `i_* ℰom(𝒪_Z, F) ⟶ F` of [Stacks, Tag 0A75]. -/
def modelTrace (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj (homZ S F) ⟶ F :=
  ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (RingedSite.structureSheafHomEvaluation (Stacks.SheafOfModules.ringedSite S.Z.sheaf)
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)) ≫
    (Adjunction.mapHomologicalComplexAdjunction
      S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app F

/-- The model comparison of `R ℰom(𝒪_Z, Q F)` with the class of `homZ F`, read backwards and
followed by the K-injective comparison with the class of `ℰom^•(𝒪_Z, F)`, is the inverse model
comparison of `R ℰom_Z(𝒪_Z[0], -)` followed by its trivialisation. -/
theorem modelIso_inv_comp_kInjectiveIso_hom
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [F.IsKInjective] :
    (derivedSheafHomExactSupportModelIso S F).inv ≫
        (S.derivedSheafHomExactSupportKInjectiveIso F).hom =
      (@RingedSite.derivedSheafHomComparison (Stacks.SheafOfModules.ringedSite S.Z.sheaf) _
        (structureComplexZ S) ((S.sheafHomExactSupport.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F) (S.isKInjective_sheafHomExactSupport F)).inv ≫
        (RingedSite.derivedStructureSheafHomNatIso
          (Stacks.SheafOfModules.ringedSite S.Z.sheaf)).hom.app
          (DerivedCategory.Q.obj ((S.sheafHomExactSupport.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F)) := by
  simp only [derivedSheafHomExactSupportModelIso, Iso.trans_inv,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The model comparison of `R ℰom(𝒪_Z, Q F)` with the class of `homZ F`, read backwards and
followed by the K-injective comparison, is the class of evaluation at the unit section: the
degreewise `ℰom(𝒪_Z, F)` is K-injective, where the trivialisation of `R ℰom_Z(𝒪_Z[0], -)` is
evaluation at the unit section. -/
theorem modelIso_inv_comp_kInjectiveIso_hom_eq_Q_map
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [F.IsKInjective] :
    (derivedSheafHomExactSupportModelIso S F).inv ≫
        (S.derivedSheafHomExactSupportKInjectiveIso F).hom =
      DerivedCategory.Q.map
        (RingedSite.structureSheafHomEvaluation (Stacks.SheafOfModules.ringedSite S.Z.sheaf)
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)) := by
  have := S.isKInjective_sheafHomExactSupport F
  refine (modelIso_inv_comp_kInjectiveIso_hom S F).trans ?_
  refine (congrArg (fun t => _ ≫ t)
    (ClosedQuotientMorphismOfRingedSpaces.derivedStructureSheafHomNatIso_hom_app_Q S.Z
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj F))).trans ?_
  exact Iso.inv_hom_id_assoc _ _

/-- **The derived trace of [Stacks, Tag 0A76] on the model of `R ℰom(𝒪_Z, Q F)`.** For a
K-injective `F`, the pushforward of the inverse model comparison followed by the trace at `Q F` is
the identification of `Ri_*` with the degreewise pushforward followed by the class of
`modelTrace F`. -/
theorem map_modelIso_inv_comp_counit
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) [F.IsKInjective] :
    (modulePushforward S.i).mapDerivedCategory.map
        (derivedSheafHomExactSupportModelIso S F).inv ≫
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
        (DerivedCategory.Q.obj F) =
    (modulePushforward S.i).mapDerivedCategoryFactors.hom.app (homZ S F) ≫
      DerivedCategory.Q.map (modelTrace S F) := by
  rw [S.derivedModulePushforwardSheafHomExactSupportAdjunction_counit_app_Q_of_isKInjective F,
    ← Functor.map_comp_assoc, modelIso_inv_comp_kInjectiveIso_hom_eq_Q_map S F, modelTrace,
    Functor.map_comp]
  have hnat := (modulePushforward S.i).mapDerivedCategoryFactors_hom_naturality
    (RingedSite.structureSheafHomEvaluation (Stacks.SheafOfModules.ringedSite S.Z.sheaf)
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ DerivedCategory.Q.map
    ((Adjunction.mapHomologicalComplexAdjunction
      S.modulePushforwardSheafHomExactSupportAdjunction (ComplexShape.up ℤ)).counit.app F))
    hnat).trans (Category.assoc _ _ _))

/-- The unit `𝒪_X[0] ⟶ i_*(𝒪_Z[0])`, as a morphism of complexes: the unit `𝒪_X ⟶ i_* 𝒪_Z` in
degree zero, read through the comparison of pushforward with the single functor. -/
def unitCochain :
    RingedSite.structureSheafComplex (Stacks.SheafOfModules.ringedSite S.X.sheaf) ⟶
      pushforwardStructureComplexX S :=
  (CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing S.X)) 0).map
      (structureSheafModuleHom S.i) ≫
    ((modulePushforward S.i).mapCochainComplexSingleFunctor 0).inv.app
      (SheafOfModules.unit (structureSheafRing S.Z))

/-- The degree-zero component of `unitCochain` is the unit `𝒪_X ⟶ i_* 𝒪_Z`. -/
theorem unitCochain_f_zero : (unitCochain S).f 0 = structureSheafModuleHom S.i :=
  rfl

/-- Evaluation at the unit section of `i_* 𝒪_Z`: restriction along `unitCochain`, followed by
evaluation at the unit section of `𝒪_X`. -/
def evalAtUnit (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S) F).obj ⟶ F :=
  (ambientRingedSite S).homMap (unitCochain S) (𝟙 F) ≫
    (ambientRingedSite S).structureSheafHomEvaluation F

/-- **The complex-level identification of [Stacks, Tag 0E2I], read backwards and followed by the
model trace, is evaluation at the unit section of `i_* 𝒪_Z`.** This is
`…ClosedQuotientMorphismOfRingedSpaces.cochainCore_of_sectionsCore` with the identity of sections
`…ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardSectionsCore` and the unit
`unitCochain`. -/
theorem pushHomIso_inv_comp_modelTrace
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (pushHomIso S F).inv ≫ modelTrace S F = evalAtUnit S F :=
  (Category.assoc _ _ _).symm.trans (S.cochainCore_of_sectionsCore
    (ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardSectionsCore S) (unitCochain S)
    (unitCochain_f_zero S) F)

/-- `pushHomIso_inv_comp_modelTrace`, read forwards: the identification of [Stacks, Tag 0E2I]
followed by evaluation at the unit section of `i_* 𝒪_Z` is the model trace. -/
theorem pushHomIso_hom_comp_evalAtUnit
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (pushHomIso S F).hom ≫ evalAtUnit S F = modelTrace S F :=
  (congrArg (fun t => (pushHomIso S F).hom ≫ t) (pushHomIso_inv_comp_modelTrace S F)).symm.trans
    (Iso.hom_inv_id_assoc _ _)

/-- The Koszul symmetry of the total tensor product is natural in the left complex, with the
two sides written through `Stacks.SheafOfModules.Tensor.tensorComplex` at the ringed-space
spelling of the complexes. -/
private theorem tensorComplex_map_app_comp_flipIso_hom
    {A B : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ} (f : A ⟶ B)
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map f).app F ≫
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf B F).hom =
      (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf A F).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).obj F).map f :=
  Stacks.SheafOfModules.tensorComplexFlipIso_hom_naturality (R := S.X.sheaf) f (𝟙 F)

variable (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))

/-- **The morphism of [Stacks, Tag 0BYR] at the models, followed by evaluation at the unit section
of `i_* 𝒪_Z`**, is the tensor product of the flat model with the same evaluation on the
injective model, followed by the augmentation into `J`. -/
theorem omega_comp_evalAtUnit :
    omega S K M ≫ evalAtUnit S (tensorInjModel S K M) =
      (ambientRingedSite S).tensorTotalMap (𝟙 (flatModel S M)) (evalAtUnit S (injModel S K)) ≫
        tensorInjAug S K M :=
  RingedSite.derivedTensorHomMapOfModels_comp_homMap_comp_structureSheafHomEvaluation
    (ambientRingedSite S) (unitCochain S) (tensorInjAug S K M)

/-- **The pushforward of the model map, followed by the model trace**, at the level of
complexes. -/
theorem pushedMap_comp_modelTrace :
    pushedMap S K M ≫ modelTrace S (tensorInjModel S K M) =
      (Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso S.i
          S.isClosedEmbedding (homZ S (injModel S K)) (flatModel S M)).inv ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map
          (modelTrace S (injModel S K))).app (flatModel S M) ≫
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf (injModel S K)
          (flatModel S M)).hom ≫
        ((ambientRingedSite S).tensorTotalIsoTensorComplex (flatModel S M)
          (injModel S K)).inv ≫
        tensorInjAug S K M := by
  have h2 := pushHomIso_inv_comp_modelTrace S (tensorInjModel S K M)
  have h3 := omega_comp_evalAtUnit S K M
  have h4 := (ambientRingedSite S).tensorTotalIsoTensorComplex_naturality (𝟙 (flatModel S M))
    (evalAtUnit S (injModel S K))
  have h6 := pushHomIso_hom_comp_evalAtUnit S (injModel S K)
  have e0 : pushedMap S K M =
      ((Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso S.i
          S.isClosedEmbedding (homZ S (injModel S K)) (flatModel S M)).inv ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map
          (pushHomIso S (injModel S K)).hom).app (flatModel S M) ≫
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf
          ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S)
            (injModel S K)).obj (flatModel S M)).hom ≫
        ((ambientRingedSite S).tensorTotalIsoTensorComplex (flatModel S M)
          ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S)
            (injModel S K)).obj).inv) ≫
        omega S K M ≫ (pushHomIso S (tensorInjModel S K M)).inv :=
    rfl
  have h4' : ((ambientRingedSite S).tensorTotalIsoTensorComplex (flatModel S M)
          ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S)
            (injModel S K)).obj).inv ≫
        (ambientRingedSite S).tensorTotalMap (𝟙 (flatModel S M)) (evalAtUnit S (injModel S K)) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).obj (flatModel S M)).map
          (evalAtUnit S (injModel S K)) ≫
        ((ambientRingedSite S).tensorTotalIsoTensorComplex (flatModel S M) (injModel S K)).inv :=
    h4
  have h5' : ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map
          (evalAtUnit S (injModel S K))).app (flatModel S M) ≫
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf (injModel S K)
          (flatModel S M)).hom =
      (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf
          ((ambientRingedSite S).sheafHomComplex (pushforwardStructureComplexX S)
            (injModel S K)).obj (flatModel S M)).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).obj (flatModel S M)).map
          (evalAtUnit S (injModel S K)) :=
    tensorComplex_map_app_comp_flipIso_hom S (evalAtUnit S (injModel S K)) (flatModel S M)
  have e7 : ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map
          (modelTrace S (injModel S K))).app (flatModel S M) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map
          (pushHomIso S (injModel S K)).hom).app (flatModel S M) ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map
          (evalAtUnit S (injModel S K))).app (flatModel S M) :=
    (congrArg (fun t => ((Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf).map t).app
      (flatModel S M)) h6).symm.trans
      (NatTrans.congr_app (Functor.map_comp (Stacks.SheafOfModules.Tensor.tensorComplex S.X.sheaf)
        (pushHomIso S (injModel S K)).hom (evalAtUnit S (injModel S K))) (flatModel S M))
  exact chain₇ e0 h2 h3 h4' h5' e7

/-- **The comparison of [Stacks, Tag 0E2K] at the class of a complex** is the identification of
the functor induced by `i_*` with the degreewise pushforward, followed by the canonical
comparison `Q(i_* C) ⟶ Ri_*(Q C)` of degreewise with derived pushforward. -/
theorem derivedPushforwardComparison_hom_app_Q
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ) :
    S.derivedPushforwardComparison.hom.app (DerivedCategory.Q.obj C) =
      (modulePushforward S.i).mapDerivedCategoryFactors.hom.app C ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
          S.i C := by
  have hfac := Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app
    (modulePushforward S.i) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)
  have hnat := S.derivedPushforwardComparison.hom.naturality
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).hom.app C)
  have hh :=
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso_hom
    (modulePushforward S.i) C
  exact chainL5 hfac hnat hh (Iso.hom_inv_id_app _ _) (Iso.hom_inv_id_app _ _)
    ((modulePushforward S.i).mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing S.Z))).app
        C)).inv_hom_id

/-- **The counit factor of the adjunction-equation composite, on the model `homZ I`.** The
comparison `Q(i_* homZ I) ⟶ Ri_*(Q homZ I)`, the model identification `Q homZ I ≅ R ℰom(𝒪_Z, K)`,
the comparison of [Stacks, Tag 0E2K] backwards and the trace at `K` compose to the class of
`modelTrace I` followed by the identification of `I` with `K`. -/
theorem pushforwardComparisonQ_comp_counit_injModel :
    Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ S.i
        (homZ S (injModel S K)) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i).map
        ((derivedSheafHomExactSupportModelIso S (injModel S K)).inv ≫
          S.derivedSheafHomExactSupport.map (injModelIso S K).hom) ≫
      S.derivedPushforwardComparison.inv.app (S.derivedSheafHomExactSupport.obj K) ≫
      S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app K =
    DerivedCategory.Q.map (modelTrace S (injModel S K)) ≫ (injModelIso S K).hom := by
  have h5 := derivedPushforwardComparison_hom_app_Q S (homZ S (injModel S K))
  have hn := S.derivedPushforwardComparison.inv.naturality
    ((derivedSheafHomExactSupportModelIso S (injModel S K)).inv ≫
          S.derivedSheafHomExactSupport.map (injModelIso S K).hom)
  have hc := S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.naturality
    (injModelIso S K).hom
  have h1 := map_modelIso_inv_comp_counit S (injModel S K)
  exact chainD1 h5
    (Iso.inv_hom_id_app (modulePushforward S.i).mapDerivedCategoryFactors (homZ S (injModel S K)))
    (Iso.hom_inv_id_app S.derivedPushforwardComparison
      (DerivedCategory.Q.obj (homZ S (injModel S K)))) hn
    (Functor.map_comp _ _ _) hc h1

/-- The source comparison of the adjunction-equation composite on the models: the comparison
`Q(i_* sourceZ) ⟶ Ri_*(Q sourceZ)` followed by `Ri_*` of the inverse of `sourceIso`. -/
abbrev srcCmp :
    DerivedCategory.Q.obj (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sourceZ S K M)) ⟶
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i).obj
        (((derivedTensorProductFunctor S.Z.sheaf).obj (S.derivedSheafHomExactSupport.obj K)).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i).obj M)) :=
  Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ S.i
      (sourceZ S K M) ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i).map
      (sourceIso S K M).inv

/-- **The comparison of `K ⊗^L M` with the class of `J`, read backwards from the resolution.** The
Koszul symmetry, the comparison of the two total tensor complexes and the augmentation into `J`,
followed by the inverse of `tensorModelIso`, are the inverse K-flat comparison followed by the
identifications of the models with `M` and `K`. -/
theorem Q_map_comp_tensorModelIso_inv :
    DerivedCategory.Q.map
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf (injModel S K)
          (flatModel S M)).hom ≫
      DerivedCategory.Q.map ((ambientRingedSite S).tensorTotalIsoTensorComplex (flatModel S M)
          (injModel S K)).inv ≫
      DerivedCategory.Q.map (tensorInjAug S K M) ≫ (tensorModelIso S K M).inv =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.X.sheaf).comparisonRight
          (injModel S K) (flatModel S M) ((ambientRingedSite S).isKFlat_kFlatModel M)).inv ≫
        ((derivedTensorProductFunctor S.X.sheaf).obj
          (DerivedCategory.Q.obj (injModel S K))).map (flatModelIso S M).hom ≫
        ((derivedTensorProductFunctor S.X.sheaf).map (injModelIso S K).hom).app M := by
  have hT : (tensorModelIso S K M).hom =
      ((derivedTensorProductFunctor S.X.sheaf).map (injModelIso S K).inv).app M ≫
        ((derivedTensorProductFunctor S.X.sheaf).obj
          (DerivedCategory.Q.obj (injModel S K))).map (flatModelIso S M).inv ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.X.sheaf).comparisonRight
          (injModel S K) (flatModel S M) ((ambientRingedSite S).isKFlat_kFlatModel M)).hom ≫
        DerivedCategory.Q.map
          (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso S.X.sheaf (injModel S K)
            (flatModel S M)).hom ≫
        DerivedCategory.Q.map ((ambientRingedSite S).tensorTotalIsoTensorComplex (flatModel S M)
          (injModel S K)).inv ≫
        DerivedCategory.Q.map (tensorInjAug S K M) :=
    rfl
  refine (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (fun t => t ≫ (tensorModelIso S K M).inv) (Category.assoc _ _ _)).trans ?_
  exact chainG7 hT
    (NatTrans.congr_app
      ((derivedTensorProductFunctor S.X.sheaf).mapIso (injModelIso S K)).hom_inv_id M)
    (((derivedTensorProductFunctor S.X.sheaf).obj
      (DerivedCategory.Q.obj (injModel S K))).mapIso (flatModelIso S M)).hom_inv_id
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.X.sheaf).comparisonRight
          (injModel S K) (flatModel S M) ((ambientRingedSite S).isKFlat_kFlatModel M)).inv_hom_id

/-- The right-hand side of `srcCmp_comp_inv_projectionFormulaMap`: the inverse complex-level
projection formula, the inverse K-flat comparison, and the comparisons in the two tensor factors,
as one morphism out of the pushed-forward source model. -/
abbrev mateModelSource :
    DerivedCategory.Q.obj (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (sourceZ S K M)) ⟶
      ((derivedTensorProductFunctor S.X.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i).obj
          (S.derivedSheafHomExactSupport.obj K))).obj M :=
  DerivedCategory.Q.map
        (Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso
          S.i S.isClosedEmbedding (homZ S (injModel S K)) (flatModel S M)).inv ≫
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.X.sheaf).comparisonRight
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (homZ S (injModel S K))) (flatModel S M)
          ((ambientRingedSite S).isKFlat_kFlatModel M)).inv ≫
      ((derivedTensorProductFunctor S.X.sheaf).map
        (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ S.i
          (homZ S (injModel S K)))).app (DerivedCategory.Q.obj (flatModel S M)) ≫
      ((derivedTensorProductFunctor S.X.sheaf).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i).map
          ((derivedSheafHomExactSupportModelIso S (injModel S K)).inv ≫
            S.derivedSheafHomExactSupport.map (injModelIso S K).hom))).app
        (DerivedCategory.Q.obj (flatModel S M)) ≫
      ((derivedTensorProductFunctor S.X.sheaf).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i).obj
          (S.derivedSheafHomExactSupport.obj K))).map (flatModelIso S M).hom

open Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes in
/-- **The projection formula of the adjunction-equation composite, on the models.** The source
comparison followed by the inverse of the projection-formula map of [Stacks, Tag 0B53] is
`mateModelSource`: the inverse complex-level projection formula of [Stacks, Tag 0B55], the
inverse K-flat comparison, and the comparisons in the two tensor factors. This is
`…ClosedEmbeddingProjectionFormulaComplexes.projectionFormulaMap_eq_derivedModelIso` transported
along the naturality of the projection-formula map in both variables. -/
theorem srcCmp_comp_inv_projectionFormulaMap :
    srcCmp S K M ≫
      CategoryTheory.inv (I := isIso_projectionFormulaMap_derivedSheafHomExactSupport S K M)
        (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap S.i
          (S.derivedSheafHomExactSupport.obj K) M) = mateModelSource S K M := by
  have hpf := projectionFormulaMap_eq_derivedModelIso S.i S.isClosedEmbedding
    (homZ S (injModel S K)) (flatModel S M) ((ambientRingedSite S).isKFlat_kFlatModel M)
  have hl := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left S.i
    ((derivedSheafHomExactSupportModelIso S (injModel S K)).inv ≫
      S.derivedSheafHomExactSupport.map (injModelIso S K).hom)
    (DerivedCategory.Q.obj (flatModel S M))
  have hr := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right S.i
    (S.derivedSheafHomExactSupport.obj K) (flatModelIso S M).hom
  have hb := congrArg (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i).map
    (((derivedTensorProductFunctor S.Z.sheaf).map
      ((derivedSheafHomExactSupportModelIso S (injModel S K)).inv ≫
        S.derivedSheafHomExactSupport.map (injModelIso S K).hom)).naturality
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i).map
        (flatModelIso S M).hom))
  exact chainD2 (F := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward S.i)
    (sIinv := (sourceIso S K M).inv) rfl hb hpf hl hr
    (Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.sourceModelIso S.i
      S.isClosedEmbedding (homZ S (injModel S K)) (flatModel S M)
      ((ambientRingedSite S).isKFlat_kFlatModel M)).hom_inv_id
    ((DerivedCategory.Q.mapIso
      (Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso
        S.i S.isClosedEmbedding (homZ S (injModel S K)) (flatModel S M))).inv_hom_id)
    (congrArg (fun t => ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        S.X.sheaf).comparisonRight
        (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (homZ S (injModel S K))) (flatModel S M)
        ((ambientRingedSite S).isKFlat_kFlatModel M)).inv ≫ t)
      (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_right
        (derivedTensorProductFunctor S.X.sheaf)
        (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ S.i
          (homZ S (injModel S K))) (DerivedCategory.Q.obj (flatModel S M))))
    (@IsIso.hom_inv_id _ _ _ _ _ (isIso_projectionFormulaMap_derivedSheafHomExactSupport S K M))

/-- **The model map of [Stacks, Tag 0E2N] satisfies the adjunction equation of the canonical
map**: pushed forward and followed by the trace of [Stacks, Tag 0A76] at `K ⊗^L M`, it is the
composite `tensorDerivedSheafHomMateMap` that the canonical map is adjoint to. -/
theorem map_tensorDerivedSheafHomModelMap_comp_counit :
    (modulePushforward S.i).mapDerivedCategory.map (tensorDerivedSheafHomModelMap S K M) ≫
        S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app
          (((derivedTensorProductFunctor S.X.sheaf).obj K).obj M) =
      tensorDerivedSheafHomMateMap S K M := by
  have hcn := S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.naturality
    (tensorModelIso S K M).inv
  have hL1J := map_modelIso_inv_comp_counit S (tensorInjModel S K M)
  have hfn := (modulePushforward S.i).mapDerivedCategoryFactors_hom_naturality (zMap S K M)
  have hpz : DerivedCategory.Q.map
        (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map (zMap S K M)) ≫
      DerivedCategory.Q.map (modelTrace S (tensorInjModel S K M)) = _ :=
    ((DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
      ((congrArg (fun t => t ≫ modelTrace S (tensorInjModel S K M)) (pushforward_zMap S K M)).trans
        (pushedMap_comp_modelTrace S K M)))).trans (functor_map_comp₅ _ _ _ _ _ _)
  have hG7 := Q_map_comp_tensorModelIso_inv S K M
  have hcR := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    S.X.sheaf).comparisonRight_naturality (modelTrace S (injModel S K)) (𝟙 (flatModel S M))
    ((ambientRingedSite S).isKFlat_kFlatModel M) ((ambientRingedSite S).isKFlat_kFlatModel M)
  have hcmp := S.derivedPushforwardComparison.hom.naturality (sourceIso S K M).inv
  have hL5 := derivedPushforwardComparison_hom_app_Q S (sourceZ S K M)
  have hD2 := srcCmp_comp_inv_projectionFormulaMap S K M
  have hD1 := pushforwardComparisonQ_comp_counit_injModel S K
  have hD1' := (functor_map_app_comp₄ (derivedTensorProductFunctor S.X.sheaf) _ _ _ _
    (DerivedCategory.Q.obj (flatModel S M))).symm.trans
      ((congrArg (fun t => ((derivedTensorProductFunctor S.X.sheaf).map t).app
        (DerivedCategory.Q.obj (flatModel S M))) hD1).trans
      (NatTrans.congr_app (Functor.map_comp (derivedTensorProductFunctor S.X.sheaf) _ _)
        (DerivedCategory.Q.obj (flatModel S M))))
  exact chainMate (sIi := (sourceIso S K M).inv) rfl hcn hL1J hfn hpz hG7 hcR
    ((Functor.congr_map _ (DerivedCategory.Q.map_id _)).trans (CategoryTheory.Functor.map_id _ _))
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.X.sheaf).comparisonRight
      (injModel S K) (flatModel S M) ((ambientRingedSite S).isKFlat_kFlatModel M)).hom_inv_id
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.X.sheaf).comparisonRight
      (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homZ S (injModel S K))) (flatModel S M)
      ((ambientRingedSite S).isKFlat_kFlatModel M)).inv_hom_id rfl hcmp
    ((modulePushforward S.i).mapDerivedCategory.mapIso (sourceIso S K M)).hom_inv_id hL5 hD2
    (((derivedTensorProductFunctor S.X.sheaf).map
      (S.derivedPushforwardComparison.inv.app (S.derivedSheafHomExactSupport.obj K))).naturality
        (flatModelIso S M).hom)
    (((derivedTensorProductFunctor S.X.sheaf).map
      (S.derivedModulePushforwardSheafHomExactSupportAdjunction.counit.app K)).naturality
        (flatModelIso S M).hom)
    (((derivedTensorProductFunctor S.X.sheaf).map (injModelIso S K).hom).naturality
        (flatModelIso S M).hom)
    hD1'

/-- **The canonical map of [Stacks, Tag 0E2N], defined by adjointness, is the model map.** The
model map satisfies the adjunction equation, which determines the canonical map. -/
theorem tensorDerivedSheafHomMap_eq_modelMap :
    tensorDerivedSheafHomMap S K M = tensorDerivedSheafHomModelMap S K M :=
  (tensorDerivedSheafHomMap_unique S K M _
    (map_tensorDerivedSheafHomModelMap_comp_counit S K M)).symm

/-- **The canonical map of [Stacks, Tag 0E2N] is invertible as soon as the diagonal of
[Stacks, Tag 0BYS] at `(M, K, Ri_* 𝒪_Z)` is.** -/
theorem isIso_tensorDerivedSheafHomMap_of_isIso_diagonal
    (hd : IsIso ((ambientRingedSite S).derivedTensorHomDiagonal M K
      (pushforwardDerivedStructureSheaf S))) :
    IsIso (tensorDerivedSheafHomMap S K M) := by
  rw [tensorDerivedSheafHomMap_eq_modelMap]
  exact isIso_tensorDerivedSheafHomModelMap_of_isIso_diagonal S K M hd

/-- **When `Ri_* 𝒪_Z` is perfect, the canonical map of [Stacks, Tag 0E2N] is an isomorphism for
every `K` and every `M`**, by the invertibility of the diagonal of [Stacks, Tag 0BYS] at a perfect
source, [Stacks, Tag 0ATN] part (1). -/
theorem isIso_tensorDerivedSheafHomMap_of_isPerfect
    (hG : (ambientRingedSite S).IsPerfect (pushforwardDerivedStructureSheaf S)) :
    IsIso (tensorDerivedSheafHomMap S K M) := by
  have hd := (ambientRingedSite S).isIso_derivedTensorHomDiagonal_of_isPerfect M K
    (pushforwardDerivedStructureSheaf S) hG
  exact isIso_tensorDerivedSheafHomMap_of_isIso_diagonal S K M hd

end Stacks.Duality.TensorHomTorAmplitude

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The map of [Stacks, Tag 0B4C] is the map of [Stacks, Tag 0E2N] at the structure sheaf**,
between the commutativity constraint on `D(𝒪_Z)` and the left unit constraint on `D(𝒪_X)`: both
are characterised by their adjunction equations, and the composite of [Stacks, Tag 0B4C] is that of
[Stacks, Tag 0E2N] at `𝒪_X` between the two constraints. -/
theorem derivedPullbackTensorSheafHomMap_eq_tensorDerivedSheafHomMap
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    S.derivedPullbackTensorSheafHomMap K =
      ((canonicalDerivedTensorProduct S.Z.sheaf).braidingIso S.closedSite
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i).obj K)
          S.derivedSheafHomStructureSheaf).hom ≫
        Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap S
          S.ambientStructureSheafObject K ≫
        S.derivedSheafHomExactSupport.map
          ((canonicalDerivedTensorProduct S.X.sheaf).leftUnitIso S.ambientSite K).hom :=
  (S.derivedPullbackTensorSheafHomMap_unique K _ (chainB rfl
    (S.derivedSheafHomAdjunction.counit.naturality
      ((canonicalDerivedTensorProduct S.X.sheaf).leftUnitIso S.ambientSite K).hom)
    (Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap_mate S
      S.ambientStructureSheafObject K) rfl)).symm

/-- **[Stacks, Tag 0B4C], the adjunction-equation composite is natural in the complex.** -/
theorem derivedPullbackTensorSheafHomMateMap_natural
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))} (k : K ⟶ L) :
    (modulePushforward S.i).mapDerivedCategory.map (S.derivedPullbackTensorSheafHom.map k) ≫
        S.derivedPullbackTensorSheafHomMateMap L =
      S.derivedPullbackTensorSheafHomMateMap K ≫ k := by
  have hb := (canonicalDerivedTensorProduct S.Z.sheaf).braidingIso_hom_naturality S.closedSite
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i).map k)
    (𝟙 S.derivedSheafHomStructureSheaf)
  have hc := S.derivedPushforwardComparison.hom.naturality
    (((derivedTensorProductFunctor S.Z.sheaf).obj S.derivedSheafHomStructureSheaf).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i).map k))
  have hr := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right S.i
    S.derivedSheafHomStructureSheaf k
  have h1 := ((derivedTensorProductFunctor S.X.sheaf).map
    (S.derivedPushforwardComparison.inv.app S.derivedSheafHomStructureSheaf)).naturality k
  have h2 := ((derivedTensorProductFunctor S.X.sheaf).map
    (S.derivedSheafHomAdjunction.counit.app S.ambientStructureSheafObject)).naturality k
  have hl := (canonicalDerivedTensorProduct S.X.sheaf).leftUnitIso_naturality S.ambientSite k
  exact chainN rfl rfl hb (CategoryTheory.Functor.map_id _ _)
    ((NatTrans.congr_app (CategoryTheory.Functor.map_id _ _) _).trans (NatTrans.id_app _ _)) hc hr
    (@IsIso.inv_hom_id _ _ _ _ _ (S.isIso_projectionFormulaMap_derivedSheafHomStructureSheaf K))
    (@IsIso.hom_inv_id _ _ _ _ _ (S.isIso_projectionFormulaMap_derivedSheafHomStructureSheaf L))
    h1 h2 hl

/-- **[Stacks, Tag 0B4C], functoriality in the complex.** The canonical map
`Li^*K ⊗^L R ℰom(𝒪_Z, 𝒪_X) ⟶ R ℰom(𝒪_Z, K)` is natural in `K`. -/
theorem derivedPullbackTensorSheafHomMap_natural
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))} (k : K ⟶ L) :
    S.derivedPullbackTensorSheafHom.map k ≫ S.derivedPullbackTensorSheafHomMap L =
      S.derivedPullbackTensorSheafHomMap K ≫ S.derivedSheafHomExactSupport.map k := by
  apply (S.derivedSheafHomAdjunction.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  simp only [derivedPullbackTensorSheafHomMap, Equiv.symm_apply_apply]
  exact S.derivedPullbackTensorSheafHomMateMap_natural k

/-- **The map of [Stacks, Tag 0B4C] is an isomorphism when `Ri_* 𝒪_Z` is perfect**, for every
complex `K`: it is the map of [Stacks, Tag 0E2N] at the structure sheaf between two
isomorphisms, and that map is invertible at a perfect `Ri_* 𝒪_Z`. -/
theorem isIso_derivedPullbackTensorSheafHomMap_of_isPerfect
    (hG : (Stacks.Duality.TensorHomTorAmplitude.ambientRingedSite S).IsPerfect
      (Stacks.Duality.TensorHomTorAmplitude.pushforwardDerivedStructureSheaf S))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    IsIso (S.derivedPullbackTensorSheafHomMap K) := by
  rw [derivedPullbackTensorSheafHomMap_eq_tensorDerivedSheafHomMap]
  have := Stacks.Duality.TensorHomTorAmplitude.isIso_tensorDerivedSheafHomMap_of_isPerfect S
    S.ambientStructureSheafObject K hG
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ this (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _)))

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
