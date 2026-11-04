module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison

/-!
# The comparison map of Stacks 0E5P under base change, abstractly

Let `f : X ⟶ Y` and `f' : X' ⟶ Y'` carry the data of
`AlgebraicGeometry.Space.PullbackComparisonData`, with right adjoints `a`, `a'` of the two
pushforwards, and let `G : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_{Y'})`, `G' : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{X'})`
(the derived pullbacks along the horizontal arrows of a cartesian square) come with
* an invertible natural base change map `β : G ∘ Rf_* ⟶ Rf'_* ∘ G'`,
* maps `α : G' ∘ a ⟶ a' ∘ G` compatible with the traces (the form of Stacks 0E5L),
* comparisons `c : G' ∘ Lf^* ⟶ Lf'^* ∘ G`,
* tensor comparisons `μ_Y`, `μ_X` for `G` and `G'`,
such that the projection formula maps and `β` satisfy the hexagon of Stacks 0E48. Then the
two-variable comparison maps of Stacks 0E5P are compatible with `G'`, `α` and the tensor
comparisons; given unit objects and right unitors compatible with `μ_Y`, so are the one-variable
maps. This is the commutativity of the square of Stacks 0E5R, read through the
characterization of the comparison maps by the traces.

## Main results

* `CategoryTheory.Adjunction.comparison_baseChange`: the statement over abstract adjunctions.
* `CategoryTheory.Adjunction.comparison_baseChange_unit`: its one-variable form at a unit object.
* `AlgebraicGeometry.Space.PullbackComparisonData.compareWithPullbackTensor_baseChange`.

## References

* [Stacks Project, Tag 0E5R](https://stacks.math.columbia.edu/tag/0E5R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Adjunction

variable {CX CY CX' CY' : Type*} [Category CX] [Category CY] [Category CX'] [Category CY']
  {R : CX ⥤ CY} {R' : CX' ⥤ CY'} {P : CY ⥤ CX} {P' : CY' ⥤ CX'}
  {TX : CX ⥤ CX ⥤ CX} {TY : CY ⥤ CY ⥤ CY} {TX' : CX' ⥤ CX' ⥤ CX'} {TY' : CY' ⥤ CY' ⥤ CY'}
  {a : CY ⥤ CX} (adja : R ⊣ a) {a' : CY' ⥤ CX'} (adja' : R' ⊣ a')
  (p : ∀ E K, (TY.obj K).obj (R.obj E) ⟶ R.obj ((TX.obj (P.obj K)).obj E)) [∀ E K, IsIso (p E K)]
  (p' : ∀ E K, (TY'.obj K).obj (R'.obj E) ⟶ R'.obj ((TX'.obj (P'.obj K)).obj E))
  [∀ E K, IsIso (p' E K)]
  (hp' : ∀ {E E'} (φ : E ⟶ E') K, (TY'.obj K).map (R'.map φ) ≫ p' E' K =
    p' E K ≫ R'.map ((TX'.obj (P'.obj K)).map φ))
  (cmp : ∀ K L, (TX.obj (P.obj K)).obj (a.obj L) ⟶ a.obj ((TY.obj K).obj L))
  (hcmp : ∀ K L, R.map (cmp K L) ≫ adja.counit.app ((TY.obj K).obj L) =
    inv (p (a.obj L) K) ≫ (TY.obj K).map (adja.counit.app L))
  (cmp' : ∀ K L, (TX'.obj (P'.obj K)).obj (a'.obj L) ⟶ a'.obj ((TY'.obj K).obj L))
  (hcmp' : ∀ K L, R'.map (cmp' K L) ≫ adja'.counit.app ((TY'.obj K).obj L) =
    inv (p' (a'.obj L) K) ≫ (TY'.obj K).map (adja'.counit.app L))
  (G : CY ⥤ CY') (G' : CX ⥤ CX')
  (β : ∀ E, G.obj (R.obj E) ⟶ R'.obj (G'.obj E)) [∀ E, IsIso (β E)]
  (hβ : ∀ {E E'} (φ : E ⟶ E'), G.map (R.map φ) ≫ β E' = β E ≫ R'.map (G'.map φ))
  (α : ∀ L, G'.obj (a.obj L) ⟶ a'.obj (G.obj L))
  (hα : ∀ L, β (a.obj L) ≫ R'.map (α L) ≫ adja'.counit.app (G.obj L) =
    G.map (adja.counit.app L))
  (c : ∀ K, G'.obj (P.obj K) ⟶ P'.obj (G.obj K))
  (μY : ∀ K L, G.obj ((TY.obj K).obj L) ⟶ (TY'.obj (G.obj K)).obj (G.obj L))
  (hμY : ∀ K {L L'} (φ : L ⟶ L'), μY K L ≫ (TY'.obj (G.obj K)).map (G.map φ) =
    G.map ((TY.obj K).map φ) ≫ μY K L')
  (μX : ∀ M N, G'.obj ((TX.obj M).obj N) ⟶ (TX'.obj (G'.obj M)).obj (G'.obj N))
  (hhex : ∀ E K, μY K (R.obj E) ≫ (TY'.obj (G.obj K)).map (β E) ≫ p' (G'.obj E) (G.obj K) =
    G.map (p E K) ≫ β ((TX.obj (P.obj K)).obj E) ≫
      R'.map (μX _ E ≫ (TX'.map (c K)).app (G'.obj E)))

include hp' hcmp hcmp' hβ hα hμY hhex in
/-- **Compatibility of the comparison maps of Stacks 0E5P with base change, over abstract
adjunctions** (the argument of Stacks 0E5R): the comparison map for `(K, L)` transported along
`G'` and `α` is the comparison map for `(G K, G L)` after the tensor comparisons and `c`. -/
theorem comparison_baseChange (K L : CY) :
    G'.map (cmp K L) ≫ α _ ≫ a'.map (μY K L) =
      μX (P.obj K) (a.obj L) ≫ (TX'.map (c K)).app _ ≫
        (TX'.obj (P'.obj (G.obj K))).map (α L) ≫ cmp' (G.obj K) (G.obj L) := by
  apply (adja'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [← cancel_epi (G.map (p (a.obj L) K) ≫ β ((TX.obj (P.obj K)).obj (a.obj L)))]
  have e1 := adja'.counit.naturality (μY K L)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at e1
  have e4 : p (a.obj L) K ≫ R.map (cmp K L) ≫ adja.counit.app ((TY.obj K).obj L) =
      (TY.obj K).map (adja.counit.app L) := by
    rw [hcmp, IsIso.hom_inv_id_assoc]
  rw [Category.assoc, e1, ← reassoc_of% (hβ (cmp K L)), reassoc_of% (hα ((TY.obj K).obj L)),
    ← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, e4]
  refine (hμY K (adja.counit.app L)).symm.trans ?_
  have f2' : p' (G'.obj (a.obj L)) (G.obj K) ≫ R'.map ((TX'.obj (P'.obj (G.obj K))).map (α L)) ≫
      inv (p' (a'.obj (G.obj L)) (G.obj K)) = (TY'.obj (G.obj K)).map (R'.map (α L)) := by
    rw [← reassoc_of% (hp' (α L) (G.obj K)), IsIso.hom_inv_id, Category.comp_id]
  have f3 := hhex (a.obj L) K
  rw [Functor.map_comp] at f3
  rw [hcmp', Category.assoc, ← reassoc_of% f3, reassoc_of% f2',
    ← (TY'.obj (G.obj K)).map_comp, ← (TY'.obj (G.obj K)).map_comp, hα L]
  rfl

include hp' hcmp hcmp' hβ hα hμY hhex in
/-- **The square of Stacks 0E5R over abstract adjunctions**: for unit objects `O_Y`, `O_{Y'}`
with `ε : G O_Y ≅ O_{Y'}` and right unitors `ρ`, `ρ'` compatible with `μ_Y`, the one-variable
comparison map `P K ⊗ a O_Y ⟶ a K` transported along `G'` and `α` is the one for `G K`, after
`μ_X`, `c` and `α` followed by `a'(ε)` on `a O_Y`. -/
theorem comparison_baseChange_unit (OY : CY) (OY' : CY') (ε : G.obj OY ⟶ OY')
    (ρ : TY.flip.obj OY ⟶ 𝟭 CY) (ρ' : TY'.flip.obj OY' ⟶ 𝟭 CY')
    (hunit : ∀ K, μY K OY ≫ (TY'.obj (G.obj K)).map ε ≫ ρ'.app (G.obj K) = G.map (ρ.app K))
    (hαnat : ∀ {L L'} (φ : L ⟶ L'), G'.map (a.map φ) ≫ α L' = α L ≫ a'.map (G.map φ))
    (hcmp'nat : ∀ K {L L'} (φ : L ⟶ L'), (TX'.obj (P'.obj K)).map (a'.map φ) ≫ cmp' K L' =
      cmp' K L ≫ a'.map ((TY'.obj K).map φ))
    (K : CY) :
    G'.map (cmp K OY ≫ a.map (ρ.app K)) ≫ α K =
      μX (P.obj K) (a.obj OY) ≫ (TX'.map (c K)).app _ ≫
        (TX'.obj (P'.obj (G.obj K))).map (α OY ≫ a'.map ε) ≫ cmp' (G.obj K) OY' ≫
          a'.map (ρ'.app (G.obj K)) := by
  have h2 := comparison_baseChange adja adja' p p' hp' cmp hcmp cmp' hcmp' G G' β hβ α hα c μY
    hμY μX hhex K OY
  have h3 := hcmp'nat (G.obj K) ε
  have h4 : G'.map (a.map (ρ.app K)) ≫ α K =
      α ((TY.obj K).obj OY) ≫ a'.map (G.map (ρ.app K)) := hαnat (ρ.app K)
  rw [G'.map_comp, Category.assoc, h4, ← hunit K, a'.map_comp, a'.map_comp,
    reassoc_of% h2, (TX'.obj (P'.obj (G.obj K))).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h3]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space.PullbackComparisonData

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS Y.1 Y.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS Y.1 Y.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS X'.1 X'.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X'.1 X'.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS Y'.1 Y'.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS Y'.1 Y'.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (D : PullbackComparisonData B S hS f) (D' : PullbackComparisonData B S hS f')
  [∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2),
    IsIso (D.projectionFormulaMap E K)]
  [∀ (E : QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y'.1 Y'.2),
    IsIso (D'.projectionFormulaMap E K)]
  {a : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2}
  (adja : D.pushforward ⊣ a)
  {a' : QuasicoherentDerivedCategory.{u, u} B S hS Y'.1 Y'.2 ⥤
    QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2}
  (adja' : D'.pushforward ⊣ a')

/-- **The comparison maps of Stacks 0E5P under base change** (the argument of Stacks 0E5R), for
the data of two morphisms of algebraic spaces related by functors `G`, `G'` with a natural
invertible base change map `β`, maps `α` compatible with the traces, identifications `c` and
tensor comparisons satisfying the hexagon of Stacks 0E48. -/
theorem compareWithPullbackTensor_baseChange
    (G : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y'.1 Y'.2)
    (G' : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2)
    (β : ∀ E, G.obj (D.pushforward.obj E) ⟶ D'.pushforward.obj (G'.obj E)) [∀ E, IsIso (β E)]
    (hβ : ∀ {E E'} (φ : E ⟶ E'), G.map (D.pushforward.map φ) ≫ β E' =
      β E ≫ D'.pushforward.map (G'.map φ))
    (α : ∀ L, G'.obj (a.obj L) ⟶ a'.obj (G.obj L))
    (hα : ∀ L, β (a.obj L) ≫ D'.pushforward.map (α L) ≫ adja'.counit.app (G.obj L) =
      G.map (adja.counit.app L))
    (c : ∀ K, G'.obj (D.pullback.obj K) ⟶ D'.pullback.obj (G.obj K))
    (μY : ∀ K L, G.obj ((D.tensorY.obj K).obj L) ⟶ (D'.tensorY.obj (G.obj K)).obj (G.obj L))
    (hμY : ∀ K {L L'} (φ : L ⟶ L'), μY K L ≫ (D'.tensorY.obj (G.obj K)).map (G.map φ) =
      G.map ((D.tensorY.obj K).map φ) ≫ μY K L')
    (μX : ∀ M N, G'.obj ((D.tensorX.obj M).obj N) ⟶ (D'.tensorX.obj (G'.obj M)).obj (G'.obj N))
    (hhex : ∀ E K, μY K (D.pushforward.obj E) ≫ (D'.tensorY.obj (G.obj K)).map (β E) ≫
        D'.projectionFormulaMap (G'.obj E) (G.obj K) =
      G.map (D.projectionFormulaMap E K) ≫ β ((D.tensorX.obj (D.pullback.obj K)).obj E) ≫
        D'.pushforward.map (μX _ E ≫ (D'.tensorX.map (c K)).app (G'.obj E)))
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    G'.map (D.compareWithPullbackTensor adja K L) ≫ α _ ≫ a'.map (μY K L) =
      μX (D.pullback.obj K) (a.obj L) ≫ (D'.tensorX.map (c K)).app _ ≫
        (D'.tensorX.obj (D'.pullback.obj (G.obj K))).map (α L) ≫
          D'.compareWithPullbackTensor adja' (G.obj K) (G.obj L) :=
  CategoryTheory.Adjunction.comparison_baseChange adja adja' D.projectionFormulaMap
    D'.projectionFormulaMap (fun φ K => D'.projectionFormulaMap_naturality_right φ K)
    (D.compareWithPullbackTensor adja) (D.map_compareWithPullbackTensor_comp_counit adja)
    (D'.compareWithPullbackTensor adja') (D'.map_compareWithPullbackTensor_comp_counit adja')
    G G' β hβ α hα c μY hμY μX hhex K L

end AlgebraicGeometry.Space.PullbackComparisonData

end
