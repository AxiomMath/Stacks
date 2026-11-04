module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.MorphismOfFamilies

/-!
# Pulling a descent datum back along a morphism of families

A morphism from a family of schemes over one base to a family over another base pulls a
descent datum for the target family back to a descent datum for the source family.

## Main definitions

* `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatum` is the pulled-back descent
  datum.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatumObjIso` identifies each of its
  components with the corresponding base change, and
  `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatumSourceMap` and
  `...TargetMap` are the induced maps on the fibre products carrying the gluing data.

## Main results

* `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatum_obj` identifies every
  component with the corresponding pullback.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.pulledBackDatum_gluing` identifies the gluing
  isomorphism with the pullback of the original gluing isomorphism.

## Implementation notes

For a morphism of families with index map `s₀` and component maps `h₀ i`, the component at
`i` is the base change of the object at `s₀ i` along `h₀ i`, and its transition is the
pullback of the original transition along the product of two component maps. These data are
packaged directly as a descent datum.

The gluing isomorphism is built from a forward and a backward map between the two fibre
products, each defined by its two projections, together with the two composites being the
identity. The cocycle condition is then checked after composing with the inclusion of the
local fibre products into the global ones, where the naturality lemmas for the triple
product maps apply.

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.MorphismOfSchemeFamilies

private noncomputable def sourceObjectIso {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (V : ∀ i, Over (X i))
    (e : ∀ i, V i ≅ D.obj i) (i j : ι) :
    Over.mk (prod.map (structureMap (f i) (V i)) (𝟙 (Over.mk (f j)))) ≅
      Over.mk (prod.map (structureMap (f i) (D.obj i))
        (𝟙 (Over.mk (f j)))) := by
  refine Over.isoMk
    (prod.mapIso ((Over.map (f i)).mapIso (e i)) (Iso.refl _)) ?_
  have hi : (Over.map (f i)).map (e i).hom ≫
      structureMap (f i) (D.obj i) = structureMap (f i) (V i) :=
    Over.OverMorphism.ext (Over.w (e i).hom)
  simp [prod.mapIso_hom, prod.map_map, hi]

private noncomputable def targetObjectIso {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (V : ∀ i, Over (X i))
    (e : ∀ i, V i ≅ D.obj i) (i j : ι) :
    Over.mk (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (V j))) ≅
      Over.mk (prod.map (𝟙 (Over.mk (f i)))
        (structureMap (f j) (D.obj j))) := by
  refine Over.isoMk
    (prod.mapIso (Iso.refl _) ((Over.map (f j)).mapIso (e j))) ?_
  have hj : (Over.map (f j)).map (e j).hom ≫
      structureMap (f j) (D.obj j) = structureMap (f j) (V j) :=
    Over.OverMorphism.ext (Over.w (e j).hom)
  simp [prod.mapIso_hom, prod.map_map, hj]

private noncomputable def transportGluing {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (V : ∀ i, Over (X i))
    (e : ∀ i, V i ≅ D.obj i) (i j : ι) :
    Over.mk (prod.map (structureMap (f i) (V i)) (𝟙 (Over.mk (f j)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk (f i))) (structureMap (f j) (V j))) :=
  sourceObjectIso D V e i j ≪≫ D.gluing i j ≪≫
    (targetObjectIso D V e i j).symm

private lemma transportGluing_hom {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (V : ∀ i, Over (X i))
    (e : ∀ i, V i ≅ D.obj i) (i j : ι) :
    (transportGluing D V e i j).hom.left =
      (prod.map ((Over.map (f i)).map (e i).hom)
        (𝟙 (Over.mk (f j)))) ≫
        (D.gluing i j).hom.left ≫
        (prod.map (𝟙 (Over.mk (f i)))
          ((Over.map (f j)).map (e j).inv)) := by
  simp [transportGluing, sourceObjectIso, targetObjectIso,
    prod.mapIso_hom, prod.mapIso_inv]


/-- Two paths around a naturality square, each followed by a projection, agree. -/
private lemma comparison_proj_eq {C₁ C₂ : Type*} [Category C₁] [Category C₂] {G : C₁ ⥤ C₂}
    {U U' P Q : C₁} {V V' P' Q' Z : C₂} {Φ : U ⟶ U'} {p : U ⟶ P} {φ : P ⟶ Q}
    {T : G.obj U ⟶ V} {T' : G.obj U' ⟶ V'} {Ψ : V ⟶ V'} {π : V' ⟶ Z} {p' : V ⟶ P'}
    {ψ : P' ⟶ Q'} {σ : Q' ⟶ Z} {κ : G.obj P ⟶ P'} {κ' : G.obj Q ⟶ Q'}
    {r : G.obj U' ⟶ Z} {s : G.obj Q ⟶ Z}
    (h₁ : T' ≫ π = r) (h₂ : G.map Φ ≫ r = G.map p ≫ G.map φ ≫ s)
    (h₃ : Ψ ≫ π = p' ≫ ψ ≫ σ) (h₄ : T ≫ p' = G.map p ≫ κ)
    (h₅ : G.map φ ≫ κ' = κ ≫ ψ) (h₆ : κ' ≫ σ = s) :
    G.map Φ ≫ T' ≫ π = T ≫ Ψ ≫ π := by
  rw [h₁, h₂, h₃, reassoc_of% h₄, ← h₆, reassoc_of% h₅]

section ProductComparisonNaturality
variable {C₁ C₂ : Type*} [Category C₁] [HasBinaryProducts C₁]
  [Category C₂] [HasBinaryProducts C₂]
variable (G : C₁ ⥤ C₂)
variable {A B C D E : C₁} {A' B' C' D' E' : C₂}

private def tripleComparison (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C') :
    G.obj ((A ⨯ B) ⨯ C) ⟶ (A' ⨯ B') ⨯ C' :=
  prodComparison G _ _ ≫ prod.map (prodComparison G _ _ ≫ prod.map a b) c

private lemma tripleComparison_fst_fst (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C') :
    tripleComparison G a b c ≫ prod.fst ≫ prod.fst =
      G.map (prod.fst : (A ⨯ B) ⨯ C ⟶ A ⨯ B) ≫
        G.map (prod.fst : A ⨯ B ⟶ A) ≫ a := by
  simp [tripleComparison, Category.assoc]

private lemma tripleComparison_fst_snd (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C') :
    tripleComparison G a b c ≫ prod.fst ≫ prod.snd =
      G.map (prod.fst : (A ⨯ B) ⨯ C ⟶ A ⨯ B) ≫
        G.map (prod.snd : A ⨯ B ⟶ B) ≫ b := by
  simp [tripleComparison, Category.assoc]

private lemma tripleComparison_snd (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C') :
    tripleComparison G a b c ≫ prod.snd =
      G.map (prod.snd : (A ⨯ B) ⨯ C ⟶ C) ≫ c := by
  simp [tripleComparison, Category.assoc]

private lemma tripleComparison_lastPair (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C') :
    tripleComparison G a b c ≫
        prod.lift (prod.fst ≫ prod.snd) prod.snd =
      G.map (prod.lift (prod.fst ≫ prod.snd) prod.snd) ≫
        prodComparison G B C ≫ prod.map b c := by
  apply prod.hom_ext <;>
  · simp [tripleComparison, Category.assoc]
    simp only [← Functor.map_comp_assoc]
    simp

omit [HasBinaryProducts C₂] in
private lemma prodMapLastTwo_map_fst_snd (φ : B ⨯ C ⟶ D ⨯ E) :
    G.map (prodMapLastTwo (A := A) φ) ≫
        G.map (prod.fst : (A ⨯ D) ⨯ E ⟶ A ⨯ D) ≫
          G.map (prod.snd : A ⨯ D ⟶ D) =
      G.map (prod.lift (prod.fst ≫ prod.snd) prod.snd :
        (A ⨯ B) ⨯ C ⟶ B ⨯ C) ≫ G.map φ ≫
          G.map (prod.fst : D ⨯ E ⟶ D) := by
  simp only [← Functor.map_comp_assoc]
  simp [prodMapLastTwo, Category.assoc]
  simp only [← Functor.map_comp]
  simp

omit [HasBinaryProducts C₂] in
private lemma prodMapLastTwo_map_snd (φ : B ⨯ C ⟶ D ⨯ E) :
    G.map (prodMapLastTwo (A := A) φ) ≫
        G.map (prod.snd : (A ⨯ D) ⨯ E ⟶ E) =
      G.map (prod.lift (prod.fst ≫ prod.snd) prod.snd :
        (A ⨯ B) ⨯ C ⟶ B ⨯ C) ≫ G.map φ ≫
          G.map (prod.snd : D ⨯ E ⟶ E) := by
  simp only [← Functor.map_comp_assoc]
  simp [prodMapLastTwo, Category.assoc]
  simp only [← Functor.map_comp]
  simp

private lemma prodMapLastTwo_fst_snd (ψ : B' ⨯ C' ⟶ D' ⨯ E') :
    prodMapLastTwo (A := A') ψ ≫
        (prod.fst : (A' ⨯ D') ⨯ E' ⟶ A' ⨯ D') ≫
          (prod.snd : A' ⨯ D' ⟶ D') =
      (prod.lift (prod.fst ≫ prod.snd) prod.snd :
        (A' ⨯ B') ⨯ C' ⟶ B' ⨯ C') ≫ ψ ≫ prod.fst := by
  simp [prodMapLastTwo]

private lemma prodMapLastTwo_snd (ψ : B' ⨯ C' ⟶ D' ⨯ E') :
    prodMapLastTwo (A := A') ψ ≫
        (prod.snd : (A' ⨯ D') ⨯ E' ⟶ E') =
      (prod.lift (prod.fst ≫ prod.snd) prod.snd :
        (A' ⨯ B') ⨯ C' ⟶ B' ⨯ C') ≫ ψ ≫ prod.snd := by
  simp [prodMapLastTwo]

private lemma prodMapLastTwo_comparison
    (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C')
    (d : G.obj D ⟶ D') (e : G.obj E ⟶ E')
    (φ : B ⨯ C ⟶ D ⨯ E)
    (ψ : B' ⨯ C' ⟶ D' ⨯ E')
    (h : G.map φ ≫ (prodComparison G D E ≫ prod.map d e) =
      (prodComparison G B C ≫ prod.map b c) ≫ ψ) :
    G.map (prodMapLastTwo φ) ≫ tripleComparison G a d e =
      tripleComparison G a b c ≫ prodMapLastTwo ψ := by
  apply prod.hom_ext
  · apply prod.hom_ext
    · simp [tripleComparison, prodMapLastTwo, Category.assoc]
      simp only [← Functor.map_comp_assoc]
      simp
    · simpa only [Category.assoc] using comparison_proj_eq (tripleComparison_fst_snd G a d e)
        ((reassoc_of% prodMapLastTwo_map_fst_snd G φ) d) (prodMapLastTwo_fst_snd ψ)
        (tripleComparison_lastPair G a b c) h (by simp)
  · simpa only [Category.assoc] using comparison_proj_eq (tripleComparison_snd G a d e)
      ((reassoc_of% prodMapLastTwo_map_snd G φ) e) (prodMapLastTwo_snd ψ)
      (tripleComparison_lastPair G a b c) h (by simp)

private lemma prodMapFirstTwo_comparison
    (a : G.obj A ⟶ A') (b : G.obj B ⟶ B')
    (c : G.obj C ⟶ C') (d : G.obj D ⟶ D') (e : G.obj E ⟶ E')
    (φ : A ⨯ B ⟶ D ⨯ E) (ψ : A' ⨯ B' ⟶ D' ⨯ E')
    (h : G.map φ ≫ (prodComparison G D E ≫ prod.map d e) =
      (prodComparison G A B ≫ prod.map a b) ≫ ψ) :
    G.map (prod.map φ (𝟙 C)) ≫ tripleComparison G d e c =
      tripleComparison G a b c ≫ prod.map ψ (𝟙 C') := by
  unfold tripleComparison
  simp only [← Category.assoc]
  rw [prodComparison_natural]
  simp only [Category.assoc, prod.map_map,
    Category.comp_id]
  rw [h]
  simp [Category.assoc]

private lemma tripleComparison_firstThirdPair (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C') :
    tripleComparison G a b c ≫
        prod.lift (prod.fst ≫ prod.fst) prod.snd =
      G.map (prod.lift (prod.fst ≫ prod.fst) prod.snd) ≫
        prodComparison G A C ≫ prod.map a c := by
  apply prod.hom_ext <;>
  · simp [tripleComparison, Category.assoc]
    simp only [← Functor.map_comp_assoc]
    simp

omit [HasBinaryProducts C₂] in
private lemma prodMapFirstThird_map_fst_fst (φ : A ⨯ C ⟶ D ⨯ E) :
    G.map (prodMapFirstThird (B := B) φ) ≫
        G.map (prod.fst : (D ⨯ B) ⨯ E ⟶ D ⨯ B) ≫
          G.map (prod.fst : D ⨯ B ⟶ D) =
      G.map (prod.lift (prod.fst ≫ prod.fst) prod.snd :
        (A ⨯ B) ⨯ C ⟶ A ⨯ C) ≫ G.map φ ≫
          G.map (prod.fst : D ⨯ E ⟶ D) := by
  simp only [← Functor.map_comp]
  simp [prodMapFirstThird, prodMapLastTwo]

omit [HasBinaryProducts C₂] in
private lemma prodMapFirstThird_map_fst_snd (φ : A ⨯ C ⟶ D ⨯ E) :
    G.map (prodMapFirstThird (B := B) φ) ≫
        G.map (prod.fst : (D ⨯ B) ⨯ E ⟶ D ⨯ B) ≫
          G.map (prod.snd : D ⨯ B ⟶ B) =
      G.map (prod.fst : (A ⨯ B) ⨯ C ⟶ A ⨯ B) ≫
        G.map (prod.snd : A ⨯ B ⟶ B) := by
  simp only [← Functor.map_comp]
  simp [prodMapFirstThird, prodMapLastTwo]

omit [HasBinaryProducts C₂] in
private lemma prodMapFirstThird_map_snd (φ : A ⨯ C ⟶ D ⨯ E) :
    G.map (prodMapFirstThird (B := B) φ) ≫
        G.map (prod.snd : (D ⨯ B) ⨯ E ⟶ E) =
      G.map (prod.lift (prod.fst ≫ prod.fst) prod.snd :
        (A ⨯ B) ⨯ C ⟶ A ⨯ C) ≫ G.map φ ≫
          G.map (prod.snd : D ⨯ E ⟶ E) := by
  simp only [← Functor.map_comp]
  simp [prodMapFirstThird, prodMapLastTwo]

private lemma prodMapFirstThird_fst_fst (ψ : A' ⨯ C' ⟶ D' ⨯ E') :
    prodMapFirstThird (B := B') ψ ≫
        (prod.fst : (D' ⨯ B') ⨯ E' ⟶ D' ⨯ B') ≫
          (prod.fst : D' ⨯ B' ⟶ D') =
      (prod.lift (prod.fst ≫ prod.fst) prod.snd :
        (A' ⨯ B') ⨯ C' ⟶ A' ⨯ C') ≫ ψ ≫ prod.fst := by
  simp [prodMapFirstThird, prodMapLastTwo]

private lemma prodMapFirstThird_fst_snd (ψ : A' ⨯ C' ⟶ D' ⨯ E') :
    prodMapFirstThird (B := B') ψ ≫
        (prod.fst : (D' ⨯ B') ⨯ E' ⟶ D' ⨯ B') ≫
          (prod.snd : D' ⨯ B' ⟶ B') =
      (prod.fst : (A' ⨯ B') ⨯ C' ⟶ A' ⨯ B') ≫
        (prod.snd : A' ⨯ B' ⟶ B') := by
  simp [prodMapFirstThird, prodMapLastTwo]

private lemma prodMapFirstThird_snd (ψ : A' ⨯ C' ⟶ D' ⨯ E') :
    prodMapFirstThird (B := B') ψ ≫
        (prod.snd : (D' ⨯ B') ⨯ E' ⟶ E') =
      (prod.lift (prod.fst ≫ prod.fst) prod.snd :
        (A' ⨯ B') ⨯ C' ⟶ A' ⨯ C') ≫ ψ ≫ prod.snd := by
  simp [prodMapFirstThird, prodMapLastTwo]

private lemma prodMapFirstThird_comparison
    (a : G.obj A ⟶ A')
    (b : G.obj B ⟶ B') (c : G.obj C ⟶ C')
    (d : G.obj D ⟶ D') (e : G.obj E ⟶ E')
    (φ : A ⨯ C ⟶ D ⨯ E)
    (ψ : A' ⨯ C' ⟶ D' ⨯ E')
    (h : G.map φ ≫ (prodComparison G D E ≫ prod.map d e) =
      (prodComparison G A C ≫ prod.map a c) ≫ ψ) :
    G.map (prodMapFirstThird (B := B) φ) ≫ tripleComparison G d b e =
      tripleComparison G a b c ≫ prodMapFirstThird (B := B') ψ := by
  apply prod.hom_ext
  · apply prod.hom_ext
    · simpa only [Category.assoc] using comparison_proj_eq (tripleComparison_fst_fst G d b e)
        ((reassoc_of% prodMapFirstThird_map_fst_fst G φ) d) (prodMapFirstThird_fst_fst ψ)
        (tripleComparison_firstThirdPair G a b c) h (by simp)
    · calc
        _ = G.map (prodMapFirstThird (B := B) φ) ≫
              (tripleComparison G d b e ≫ prod.fst ≫ prod.snd) := by
                simp only [Category.assoc]
        _ = G.map (prodMapFirstThird (B := B) φ) ≫
              (G.map (prod.fst : (D ⨯ B) ⨯ E ⟶ D ⨯ B) ≫
                G.map (prod.snd : D ⨯ B ⟶ B) ≫ b) := by
                  rw [tripleComparison_fst_snd]
        _ = G.map (prod.fst : (A ⨯ B) ⨯ C ⟶ A ⨯ B) ≫
              G.map (prod.snd : A ⨯ B ⟶ B) ≫ b := by
                have hx := congrArg (fun q ↦ q ≫ b)
                  (prodMapFirstThird_map_fst_snd (G := G) (B := B) φ)
                simpa [prodMapFirstThird, Category.assoc] using hx
        _ = tripleComparison G a b c ≫ prod.fst ≫ prod.snd := by
              rw [tripleComparison_fst_snd]
        _ = tripleComparison G a b c ≫
              prodMapFirstThird (B := B') ψ ≫ prod.fst ≫ prod.snd := by
                simp [prodMapFirstThird, Category.assoc]
        _ = _ := by simp only [Category.assoc]
  · simpa only [Category.assoc] using comparison_proj_eq (tripleComparison_snd G d b e)
      ((reassoc_of% prodMapFirstThird_map_snd G φ) e) (prodMapFirstThird_snd ψ)
      (tripleComparison_firstThirdPair G a b c) h (by simp)

end ProductComparisonNaturality

private lemma transportGluing_naturality {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (V : ∀ i, Over (X i))
    (e : ∀ i, V i ≅ D.obj i) (i j : ι) :
    (transportGluing D V e i j).hom.left ≫
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (e j).hom) =
      prod.map ((Over.map (f i)).map (e i).hom) (𝟙 (Over.mk (f j))) ≫
        (D.gluing i j).hom.left := by
  rw [transportGluing_hom, Category.assoc, Category.assoc]
  simp

private lemma transportGluing_cocycle {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (V : ∀ i, Over (X i))
    (e : ∀ i, V i ≅ D.obj i) (i j k : ι) :
    prod.map (transportGluing D V e i j).hom.left (𝟙 (Over.mk (f k))) ≫
        prodMapLastTwo (transportGluing D V e j k).hom.left =
      prodMapFirstThird (transportGluing D V e i k).hom.left := by
  let a := (Over.map (f i)).map (e i).hom
  let b := (Over.map (f j)).map (e j).hom
  let c := (Over.map (f k)).map (e k).hom
  let ai : Over.mk (f i) ⟶ Over.mk (f i) := 𝟙 _
  let bj : Over.mk (f j) ⟶ Over.mk (f j) := 𝟙 _
  let ck : Over.mk (f k) ⟶ Over.mk (f k) := 𝟙 _
  let sourceIncl := prod.map (prod.map a bj) ck
  let targetIncl := prod.map (prod.map ai bj) c
  let middleIncl := prod.map (prod.map ai b) ck
  let localFirst := prod.map (transportGluing D V e i j).hom.left
    (𝟙 (Over.mk (f k)))
  let globalFirst := prod.map (D.gluing i j).hom.left (𝟙 (Over.mk (f k)))
  let localTail := prodMapLastTwo (A := Over.mk (f i))
    (transportGluing D V e j k).hom.left
  let globalTail := prodMapLastTwo (A := Over.mk (f i))
    (D.gluing j k).hom.left
  have htarget : Mono targetIncl := by
    dsimp [targetIncl, ai, bj, c]
    infer_instance
  have hhead : localFirst ≫ middleIncl = sourceIncl ≫ globalFirst := by
    simp only [localFirst, middleIncl, sourceIncl, globalFirst,
      prod.map_map, Category.id_comp, Category.comp_id]
    rw [transportGluing_naturality D V e i j]
  have htail : middleIncl ≫ globalTail = localTail ≫ targetIncl :=
    prodMapLastTwo_naturality ai b ck bj c _ _
      (transportGluing_naturality D V e j k).symm
  apply (cancel_mono targetIncl).mp
  calc
    (localFirst ≫ localTail) ≫ targetIncl =
        sourceIncl ≫ (globalFirst ≫ globalTail) := by
      rw [Category.assoc, ← htail, ← Category.assoc, hhead, Category.assoc]
    _ = sourceIncl ≫ prodMapFirstThird (D.gluing i k).hom.left := by
      rw [D.cocycle i j k]
    _ = prodMapFirstThird (transportGluing D V e i k).hom.left ≫ targetIncl :=
      prodMapFirstThird_naturality a bj ck ai c _ _
        (transportGluing_naturality D V e i k).symm

private noncomputable def transportDatum {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (V : ∀ i, Over (X i))
    (e : ∀ i, V i ≅ D.obj i) : DescentData f where
  obj := V
  gluing := transportGluing D V e
  cocycle := transportGluing_cocycle D V e

public abbrev localObj (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    Over (F.sourceFamily.X i) :=
  (Over.pullback (F.familyHom.h₀ i)).obj (D.obj (F.familyHom.s₀ i))

public noncomputable def localSourceMap (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pullback ((localObj F D i).hom ≫ F.sourceFamily.f i)
        (F.sourceFamily.f j) ⟶
      pullback ((D.obj (F.familyHom.s₀ i)).hom ≫
          F.targetFamily.f (F.familyHom.s₀ i))
        (F.targetFamily.f (F.familyHom.s₀ j)) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ F.familyHom.h₀ j) (by
      simp only [Category.assoc, pullback.condition_assoc, F.familyHom.w₀]
      rw [← Over.pullback_obj_hom]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ F.baseHom)
        (pullback.condition (f := (localObj F D i).hom ≫ F.sourceFamily.f i)
          (g := F.sourceFamily.f j)))

public noncomputable def localTargetMap (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pullback (F.sourceFamily.f i)
        ((localObj F D j).hom ≫ F.sourceFamily.f j) ⟶
      pullback (F.targetFamily.f (F.familyHom.s₀ i))
        ((D.obj (F.familyHom.s₀ j)).hom ≫
          F.targetFamily.f (F.familyHom.s₀ j)) :=
  pullback.lift (pullback.fst _ _ ≫ F.familyHom.h₀ i)
    (pullback.snd _ _ ≫ pullback.fst _ _) (by
      simp only [Category.assoc, pullback.condition_assoc, F.familyHom.w₀]
      rw [← Over.pullback_obj_hom])

/-- The first projection of `localSourceMap` is the composite of the two first
projections of the source fibre product. -/
@[reassoc]
private lemma localSourceMap_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localSourceMap F D i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The second projection of `localSourceMap` is the second projection of the source
fibre product followed by the component map at `j`. -/
@[reassoc]
private lemma localSourceMap_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localSourceMap F D i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ F.familyHom.h₀ j :=
  pullback.lift_snd _ _ _

/-- The first projection of `localTargetMap` is the first projection of the source fibre
product followed by the component map at `i`. -/
@[reassoc]
private lemma localTargetMap_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localTargetMap F D i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ F.familyHom.h₀ i :=
  pullback.lift_fst _ _ _

/-- The second projection of `localTargetMap` is the composite of the two second
projections of the source fibre product. -/
@[reassoc]
private lemma localTargetMap_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localTargetMap F D i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  pullback.lift_snd _ _ _

lemma gluingPullback_fst {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (D.obj i).hom := by
  simp only [DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map]
  simp only [Category.assoc]
  have hp := Over.prodLeftIsoPullback_hom_fst (Over.mk (f i))
    ((Over.map (f j)).obj (D.obj j))
  change (Over.prodLeftIsoPullback (Over.mk (f i))
    ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.fst (f i) ((D.obj j).hom ≫ f j) = _ at hp
  have hg := congrArg Over.Hom.left (D.gluing_hom_fst i j)
  simp only [Over.comp_left] at hg
  rw [hp, hg]
  simp

lemma gluingPullback_snd {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).hom ≫ pullback.snd _ _ ≫ (D.obj j).hom =
      pullback.snd _ _ := by
  simp only [DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Over.forget_map]
  simp only [Category.assoc]
  have hp := Over.prodLeftIsoPullback_hom_snd (Over.mk (f i))
    ((Over.map (f j)).obj (D.obj j))
  change (Over.prodLeftIsoPullback (Over.mk (f i))
    ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.snd (f i) ((D.obj j).hom ≫ f j) = _ at hp
  have hg := congrArg Over.Hom.left (D.gluing_hom_snd_structureMap i j)
  simp only [Over.comp_left] at hg
  change (D.gluing i j).hom.left.left ≫ (prod.snd :
    Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶
      (Over.map (f j)).obj (D.obj j)).left ≫ (D.obj j).hom =
      (prod.snd : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶
        Over.mk (f j)).left at hg
  have hp' := congrArg (fun q ↦ q ≫ (D.obj j).hom) hp
  simp only [Category.assoc] at hp'
  rw [hp', hg]
  simp

private lemma gluingPullback_inv_fst {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).inv ≫ pullback.fst _ _ ≫ (D.obj i).hom =
      pullback.fst _ _ := by
  rw [Iso.inv_comp_eq]
  exact (gluingPullback_fst D i j).symm

private lemma gluingPullback_inv_snd {ι : Type*} {S : Scheme.{u}}
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : DescentData f) (i j : ι) :
    (D.gluingPullbackIso i j).inv ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (D.obj j).hom := by
  rw [Iso.inv_comp_eq]
  exact (gluingPullback_snd D i j).symm

public noncomputable def localForward (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pullback ((localObj F D i).hom ≫ F.sourceFamily.f i)
        (F.sourceFamily.f j) ⟶
      pullback (F.sourceFamily.f i)
        ((localObj F D j).hom ≫ F.sourceFamily.f j) :=
  pullback.lift
    (pullback.fst _ _ ≫ (localObj F D i).hom)
    (pullback.lift
      (localSourceMap F D i j ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫
        pullback.snd _ _)
      (pullback.snd _ _) (by
        simp only [Category.assoc, gluingPullback_snd]
        exact localSourceMap_snd F D i j)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ F.sourceFamily.f j) (pullback.lift_snd _ _ _).symm)

public noncomputable def localBackward (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pullback (F.sourceFamily.f i)
        ((localObj F D j).hom ≫ F.sourceFamily.f j) ⟶
      pullback ((localObj F D i).hom ≫ F.sourceFamily.f i)
        (F.sourceFamily.f j) :=
  pullback.lift
    (pullback.lift
      (localTargetMap F D i j ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).inv ≫
        pullback.fst _ _)
      (pullback.fst _ _) (by
        simp only [Category.assoc, gluingPullback_inv_fst]
        exact localTargetMap_fst F D i j))
    (pullback.snd _ _ ≫ (localObj F D j).hom) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ F.sourceFamily.f i) (pullback.lift_snd _ _ _))

/-- The first projection of `localForward` is the first projection of its source followed
by the structure map of the pulled-back object at `i`. -/
@[reassoc]
public lemma localForward_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localForward F D i j ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫
        pullback.snd (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) :=
  pullback.lift_fst _ _ _

/-- The second projection of `localForward`, followed by the structure map of the
pulled-back object at `j`, is the second projection of its source. -/
@[reassoc]
public lemma localForward_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localForward F D i j ≫ pullback.snd _ _ ≫
        pullback.snd (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) =
      pullback.snd _ _ :=
  (pullback.lift_snd_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

/-- The second projection of `localForward`, followed by the first projection of the
pulled-back object at `j`, is cut out by the transition isomorphism of `D`. -/
@[reassoc]
private lemma localForward_snd_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localForward F D i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      localSourceMap F D i j ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫
          pullback.snd _ _ :=
  (pullback.lift_snd_assoc _ _ _ _).trans (pullback.lift_fst _ _ _)

/-- The second projection of `localBackward` is the second projection of its source
followed by the structure map of the pulled-back object at `j`. -/
@[reassoc]
private lemma localBackward_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localBackward F D i j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫
        pullback.snd (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) :=
  pullback.lift_snd _ _ _

/-- The first projection of `localBackward`, followed by the structure map of the
pulled-back object at `i`, is the first projection of its source. -/
@[reassoc]
private lemma localBackward_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localBackward F D i j ≫ pullback.fst _ _ ≫
        pullback.snd (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) =
      pullback.fst _ _ :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_snd _ _ _)

/-- The first projection of `localBackward`, followed by the first projection of the
pulled-back object at `i`, is cut out by the inverse transition isomorphism of `D`. -/
@[reassoc]
private lemma localBackward_fst_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localBackward F D i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      localTargetMap F D i j ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).inv ≫
          pullback.fst _ _ :=
  (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_fst _ _ _)

private lemma localForward_comm (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localForward F D i j ≫ localTargetMap F D i j =
      localSourceMap F D i j ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, localTargetMap_fst, localForward_fst_assoc,
      gluingPullback_fst, localSourceMap_fst_assoc, pullback.condition]
  · simp only [Category.assoc, localTargetMap_snd, localForward_snd_fst]

private lemma localBackward_comm (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localBackward F D i j ≫ localSourceMap F D i j =
      localTargetMap F D i j ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, localSourceMap_fst, localBackward_fst_fst]
  · simp only [Category.assoc, localSourceMap_snd, localBackward_snd_assoc,
      gluingPullback_inv_snd, localTargetMap_snd_assoc, pullback.condition]

public lemma localForward_backward (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localForward F D i j ≫ localBackward F D i j = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc
        (localForward F D i j ≫ localBackward F D i j) ≫
            pullback.fst _ _ ≫ pullback.fst _ _ =
          localForward F D i j ≫
            (localBackward F D i j ≫ localSourceMap F D i j) ≫
              pullback.fst _ _ := by simp only [Category.assoc, localSourceMap_fst]
        _ = (localForward F D i j ≫ localTargetMap F D i j) ≫
            (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).inv ≫
              pullback.fst _ _ := by rw [localBackward_comm]; simp [Category.assoc]
        _ = (localSourceMap F D i j ≫
            (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom) ≫
            (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).inv ≫
              pullback.fst _ _ := by rw [localForward_comm]
        _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, localSourceMap_fst]
    · simp only [Category.assoc, Category.id_comp, localBackward_fst,
        localForward_fst]
  · simp only [Category.assoc, Category.id_comp, localBackward_snd,
      localForward_snd]

public lemma localBackward_forward (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    localBackward F D i j ≫ localForward F D i j = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Category.id_comp, localForward_fst,
      localBackward_fst]
  · apply pullback.hom_ext
    · calc
        (localBackward F D i j ≫ localForward F D i j) ≫
            pullback.snd _ _ ≫ pullback.fst _ _ =
          localBackward F D i j ≫
            (localForward F D i j ≫ localTargetMap F D i j) ≫
              pullback.snd _ _ := by simp only [Category.assoc, localTargetMap_snd]
        _ = (localBackward F D i j ≫ localSourceMap F D i j) ≫
            (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫
              pullback.snd _ _ := by rw [localForward_comm]; simp [Category.assoc]
        _ = (localTargetMap F D i j ≫
            (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).inv) ≫
            (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫
              pullback.snd _ _ := by rw [localBackward_comm]
        _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc, localTargetMap_snd]
    · simp only [Category.assoc, Category.id_comp, localForward_snd,
        localBackward_snd]

public noncomputable def localIso (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    pullback ((localObj F D i).hom ≫ F.sourceFamily.f i)
        (F.sourceFamily.f j) ≅
      pullback (F.sourceFamily.f i)
        ((localObj F D j).hom ≫ F.sourceFamily.f j) where
  hom := localForward F D i j
  inv := localBackward F D i j
  hom_inv_id := localForward_backward F D i j
  inv_hom_id := localBackward_forward F D i j

public noncomputable def localGluing (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    Over.mk (prod.map
        (structureMap (F.sourceFamily.f i) (localObj F D i))
        (𝟙 (Over.mk (F.sourceFamily.f j)))) ≅
      Over.mk (prod.map
        (𝟙 (Over.mk (F.sourceFamily.f i)))
        (structureMap (F.sourceFamily.f j) (localObj F D j))) := by
  let e := (Over.prodLeftIsoPullback
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))) ≪≫
    localIso F D i j ≪≫
    (Over.prodLeftIsoPullback (Over.mk (F.sourceFamily.f i))
      ((Over.map (F.sourceFamily.f j)).obj (localObj F D j))).symm
  have hfst : e.hom ≫ (prod.fst :
      Over.mk (F.sourceFamily.f i) ⨯
        (Over.map (F.sourceFamily.f j)).obj (localObj F D j) ⟶
          Over.mk (F.sourceFamily.f i)).left =
      (prod.fst : (Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
        Over.mk (F.sourceFamily.f j) ⟶
          (Over.map (F.sourceFamily.f i)).obj (localObj F D i)).left ≫
        (localObj F D i).hom := by
    simp only [Over.mk_left, Over.map_obj_left, Over.pullback_obj_left,
      Over.map_obj_hom, Over.pullback_obj_hom, Over.mk_hom, localIso,
      Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Over.prodLeftIsoPullback_inv_fst, e]
    have hf := localForward_fst F D i j
    simp only [localObj, Over.pullback_obj_hom] at hf
    rw [hf]
    have hp := Over.prodLeftIsoPullback_hom_fst
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))
    change (Over.prodLeftIsoPullback
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))).hom ≫
        pullback.fst ((localObj F D i).hom ≫ F.sourceFamily.f i)
          (F.sourceFamily.f j) = _ at hp
    simp only [localObj, Over.pullback_obj_hom] at hp
    have hp' := congrArg (fun q ↦ q ≫
      pullback.snd (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i)) hp
    simp only [Category.assoc] at hp'
    rw [hp']
  have hsnd : e.hom ≫ (prod.snd :
      Over.mk (F.sourceFamily.f i) ⨯
        (Over.map (F.sourceFamily.f j)).obj (localObj F D j) ⟶
          (Over.map (F.sourceFamily.f j)).obj (localObj F D j)).left ≫
        (localObj F D j).hom =
      (prod.snd : (Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
        Over.mk (F.sourceFamily.f j) ⟶ Over.mk (F.sourceFamily.f j)).left := by
    simp only [Over.map_obj_left, Over.pullback_obj_left, Over.mk_left,
      Over.map_obj_hom, Over.pullback_obj_hom, Over.mk_hom, localIso,
      Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Over.prodLeftIsoPullback_inv_snd_assoc, e]
    have hs := localForward_snd F D i j
    simp only [localObj, Over.pullback_obj_hom] at hs
    rw [hs]
    have hp := Over.prodLeftIsoPullback_hom_snd
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))
    change (Over.prodLeftIsoPullback
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))).hom ≫
        pullback.snd ((localObj F D i).hom ≫ F.sourceFamily.f i)
          (F.sourceFamily.f j) = _ at hp
    simp only [localObj, Over.pullback_obj_hom] at hp
    rw [hp]
  have hover : e.hom ≫
      (Over.mk (F.sourceFamily.f i) ⨯
        (Over.map (F.sourceFamily.f j)).obj (localObj F D j)).hom =
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
        Over.mk (F.sourceFamily.f j)).hom := by
    calc
      e.hom ≫ _ = e.hom ≫ (prod.fst :
          Over.mk (F.sourceFamily.f i) ⨯
            (Over.map (F.sourceFamily.f j)).obj (localObj F D j) ⟶
              Over.mk (F.sourceFamily.f i)).left ≫ F.sourceFamily.f i := by
        simpa only [Category.assoc, show (Over.mk (F.sourceFamily.f i)).hom =
          F.sourceFamily.f i from rfl] using congrArg (fun q ↦ e.hom ≫ q)
          (Over.w (prod.fst :
            Over.mk (F.sourceFamily.f i) ⨯
              (Over.map (F.sourceFamily.f j)).obj (localObj F D j) ⟶
                Over.mk (F.sourceFamily.f i))).symm
      _ = (prod.fst : (Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
          Over.mk (F.sourceFamily.f j) ⟶
            (Over.map (F.sourceFamily.f i)).obj (localObj F D i)).left ≫
              (localObj F D i).hom ≫ F.sourceFamily.f i := by
        simpa only [Category.assoc] using congrArg
          (fun q ↦ q ≫ F.sourceFamily.f i) hfst
      _ = _ := by
        simpa only [Over.map_obj_hom] using (Over.w (prod.fst :
          (Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
            Over.mk (F.sourceFamily.f j) ⟶
              (Over.map (F.sourceFamily.f i)).obj (localObj F D i)))
  refine Over.isoMk (Over.isoMk e hover) ?_
  apply prod.hom_ext
  · apply Over.OverMorphism.ext
    simpa [prod.map_fst, Category.assoc] using hfst
  · apply Over.OverMorphism.ext
    simpa [prod.map_snd, Category.assoc] using hsnd

private lemma localGluing_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (localGluing F D i j).hom.left ≫ prod.fst =
      prod.fst ≫ structureMap (F.sourceFamily.f i) (localObj F D i) := by
  simpa using congrArg (fun g ↦ g ≫ prod.fst)
    (Over.w (localGluing F D i j).hom)

private lemma localGluing_snd (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (localGluing F D i j).hom.left ≫ prod.snd ≫
        structureMap (F.sourceFamily.f j) (localObj F D j) = prod.snd := by
  simpa using congrArg (fun g ↦ g ≫ prod.snd)
    (Over.w (localGluing F D i j).hom)

private lemma localGluing_snd_scheme (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (localGluing F D i j).hom.left.left ≫
        (prod.snd : Over.mk (F.sourceFamily.f i) ⨯
          (Over.map (F.sourceFamily.f j)).obj (localObj F D j) ⟶
          (Over.map (F.sourceFamily.f j)).obj (localObj F D j)).left ≫
          (localObj F D j).hom =
      (prod.snd : (Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
        Over.mk (F.sourceFamily.f j) ⟶ Over.mk (F.sourceFamily.f j)).left := by
  have h := congrArg Over.Hom.left (localGluing_snd F D i j)
  simp only [Over.comp_left] at h
  change _ ≫ _ ≫ (localObj F D j).hom = _ at h
  exact h

private lemma localGluing_snd_pullback (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (localGluing F D i j).hom.left.left ≫
        (prod.snd : Over.mk (F.sourceFamily.f i) ⨯
          (Over.map (F.sourceFamily.f j)).obj (localObj F D j) ⟶
          (Over.map (F.sourceFamily.f j)).obj (localObj F D j)).left ≫
          pullback.snd (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) =
      (prod.snd : (Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
        Over.mk (F.sourceFamily.f j) ⟶ Over.mk (F.sourceFamily.f j)).left := by
  simpa only [localObj, Over.pullback_obj_hom] using localGluing_snd_scheme F D i j

private noncomputable def localToGlobalV (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    (Over.map F.baseHom).obj
        ((Over.map (F.sourceFamily.f i)).obj (localObj F D i)) ⟶
      (Over.map (F.targetFamily.f (F.familyHom.s₀ i))).obj
        (D.obj (F.familyHom.s₀ i)) :=
  Over.homMk (pullback.fst _ _) (by
    simp only [Over.map_obj_hom, localObj, Over.pullback_obj_hom, Category.assoc]
    rw [pullback.condition_assoc, F.familyHom.w₀])

private def localToGlobalX (F : MorphismOfSchemeFamilies.{u})
    (i : F.sourceFamily.I₀) :
    (Over.map F.baseHom).obj (Over.mk (F.sourceFamily.f i)) ⟶
      Over.mk (F.targetFamily.f (F.familyHom.s₀ i)) :=
  Over.homMk (F.familyHom.h₀ i) (F.familyHom.w₀ i)

private noncomputable def localSourceIncl (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (Over.map F.baseHom).obj
        ((Over.map (F.sourceFamily.f i)).obj (localObj F D i) ⨯
          Over.mk (F.sourceFamily.f j)) ⟶
      (Over.map (F.targetFamily.f (F.familyHom.s₀ i))).obj
          (D.obj (F.familyHom.s₀ i)) ⨯
        Over.mk (F.targetFamily.f (F.familyHom.s₀ j)) :=
  prodComparison (Over.map F.baseHom) _ _ ≫
    prod.map (localToGlobalV F D i) (localToGlobalX F j)

private noncomputable def localTargetIncl (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (Over.map F.baseHom).obj
        (Over.mk (F.sourceFamily.f i) ⨯
          (Over.map (F.sourceFamily.f j)).obj (localObj F D j)) ⟶
      Over.mk (F.targetFamily.f (F.familyHom.s₀ i)) ⨯
        (Over.map (F.targetFamily.f (F.familyHom.s₀ j))).obj
          (D.obj (F.familyHom.s₀ j)) :=
  prodComparison (Over.map F.baseHom) _ _ ≫
    prod.map (localToGlobalX F i) (localToGlobalV F D j)

private lemma localSourceIncl_pullback (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (Over.prodLeftIsoPullback
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))).inv ≫
      (localSourceIncl F D i j).left ≫
      (Over.prodLeftIsoPullback
        ((Over.map (F.targetFamily.f (F.familyHom.s₀ i))).obj
          (D.obj (F.familyHom.s₀ i)))
        (Over.mk (F.targetFamily.f (F.familyHom.s₀ j)))).hom =
      localSourceMap F D i j := by
  apply pullback.hom_ext
  · simp only [localSourceIncl,
      Category.assoc, Over.prodLeftIsoPullback_hom_fst,
      ← Over.comp_left, prod.map_fst]
    simp only [Over.map_obj_left, Over.pullback_obj_left, Over.mk_left,
      Over.map_obj_hom, Over.pullback_obj_hom, Over.mk_hom, localToGlobalV,
      prodComparison_fst_assoc, Over.comp_left, Over.map_map_left,
      Over.homMk_left, Over.prodLeftIsoPullback_inv_fst_assoc]
    exact (localSourceMap_fst F D i j).symm
  · simp only [localSourceIncl,
      Category.assoc, Over.prodLeftIsoPullback_hom_snd,
      ← Over.comp_left, prod.map_snd]
    simp only [Over.map_obj_left, Over.pullback_obj_left, Over.mk_left,
      Over.map_obj_hom, Over.pullback_obj_hom, Over.mk_hom, localToGlobalX,
      prodComparison_snd_assoc, Over.comp_left, Over.map_map_left,
      Over.homMk_left, Over.prodLeftIsoPullback_inv_snd_assoc]
    exact (localSourceMap_snd F D i j).symm

private lemma localGluing_naturality (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    (Over.map F.baseHom).map (localGluing F D i j).hom.left ≫
        localTargetIncl F D i j =
      localSourceIncl F D i j ≫
        (D.gluing (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom.left := by
  apply prod.hom_ext
  · simp only [Over.mk_left, localTargetIncl, localToGlobalX, localToGlobalV,
      Category.assoc, prod.map_fst, prodComparison_fst_assoc, localSourceIncl,
      D.gluing_hom_fst, prod.map_fst_assoc]
    rw [← Functor.map_comp_assoc, localGluing_fst]
    simp only [localObj, structureMap, Over.pullback_obj_hom, Functor.map_comp,
      Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simpa [Over.comp_left] using
      (pullback.condition (f := (D.obj (F.familyHom.s₀ i)).hom)
        (g := F.familyHom.h₀ i)).symm
  · simp only [Over.mk_left, localTargetIncl, localToGlobalX, localToGlobalV,
      Category.assoc, prod.map_snd, prodComparison_snd_assoc]
    apply Over.OverMorphism.ext
    apply (cancel_epi (Over.prodLeftIsoPullback
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))).inv).mp
    have h := congrArg (fun q ↦ q ≫ pullback.snd _ _)
      (localForward_comm F D i j)
    let eU := Over.prodLeftIsoPullback
      ((Over.map (F.sourceFamily.f i)).obj (localObj F D i))
      (Over.mk (F.sourceFamily.f j))
    let eV := Over.prodLeftIsoPullback
      ((Over.map (F.targetFamily.f (F.familyHom.s₀ i))).obj
        (D.obj (F.familyHom.s₀ i)))
      (Over.mk (F.targetFamily.f (F.familyHom.s₀ j)))
    have hsource : eU.inv ≫ (localSourceIncl F D i j).left =
        localSourceMap F D i j ≫ eV.inv := by
      have hx := congrArg (fun q ↦ q ≫ eV.inv)
        (localSourceIncl_pullback F D i j)
      simpa [eU, eV, Category.assoc] using hx
    simp only [DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Over.forget_map, Category.assoc] at h
    dsimp only [eV] at hsource
    simp only [← Category.assoc] at h
    rw [← hsource] at h
    simp only [Category.assoc] at h
    have hp := Over.prodLeftIsoPullback_hom_snd
      (Over.mk (F.targetFamily.f (F.familyHom.s₀ i)))
      ((Over.map (F.targetFamily.f (F.familyHom.s₀ j))).obj
        (D.obj (F.familyHom.s₀ j)))
    change (Over.prodLeftIsoPullback
      (Over.mk (F.targetFamily.f (F.familyHom.s₀ i)))
      ((Over.map (F.targetFamily.f (F.familyHom.s₀ j))).obj
        (D.obj (F.familyHom.s₀ j)))).hom ≫
        pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
          ((D.obj (F.familyHom.s₀ j)).hom ≫
            F.targetFamily.f (F.familyHom.s₀ j)) = _ at hp
    rw [hp] at h
    simp only [Over.map_obj_left, Over.pullback_obj_left, Over.mk_left,
      Over.map_obj_hom, Over.pullback_obj_hom, Over.mk_hom, localGluing,
      Over.isoMk_hom_left, Over.comp_left, Over.map_map_left, Iso.trans_hom,
      Iso.symm_hom, Over.homMk_left, Category.assoc,
      Over.prodLeftIsoPullback_inv_snd_assoc, Iso.inv_hom_id_assoc]
    simpa only [localTargetMap, pullback.lift_snd, Category.assoc,
      localIso, eU, localObj, Over.pullback_obj_hom] using h

private lemma localCocycle_fst (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j k : F.sourceFamily.I₀) :
    (prod.map (localGluing F D i j).hom.left
        (𝟙 (Over.mk (F.sourceFamily.f k))) ≫
      prodMapLastTwo (localGluing F D j k).hom.left ≫
      prod.snd).left ≫
        pullback.fst (D.obj (F.familyHom.s₀ k)).hom (F.familyHom.h₀ k) =
      (prodMapFirstThird (B := Over.mk (F.sourceFamily.f j))
        (localGluing F D i k).hom.left ≫ prod.snd).left ≫
        pullback.fst (D.obj (F.familyHom.s₀ k)).hom (F.familyHom.h₀ k) := by
  let G := Over.map F.baseHom
  let vi := localToGlobalV F D i
  let vj := localToGlobalV F D j
  let vk := localToGlobalV F D k
  let xi := localToGlobalX F i
  let xj := localToGlobalX F j
  let xk := localToGlobalX F k
  have hij := prodMapFirstTwo_comparison G vi xj xk xi vj
    (localGluing F D i j).hom.left
    (D.gluing (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom.left
    (by simpa [G, vi, xj, xi, vj, localSourceIncl, localTargetIncl]
      using localGluing_naturality F D i j)
  have hjk := prodMapLastTwo_comparison G xi vj xk xj vk
    (localGluing F D j k).hom.left
    (D.gluing (F.familyHom.s₀ j) (F.familyHom.s₀ k)).hom.left
    (by simpa [G, vj, xk, xj, vk, localSourceIncl, localTargetIncl]
      using localGluing_naturality F D j k)
  have hik := prodMapFirstThird_comparison G vi xj xk xi vk
    (localGluing F D i k).hom.left
    (D.gluing (F.familyHom.s₀ i) (F.familyHom.s₀ k)).hom.left
    (by simpa [G, vi, xk, xi, vk, localSourceIncl, localTargetIncl]
      using localGluing_naturality F D i k)
  have hcomp :
      G.map (prod.map (localGluing F D i j).hom.left
          (𝟙 (Over.mk (F.sourceFamily.f k))) ≫
        prodMapLastTwo (localGluing F D j k).hom.left) ≫
        tripleComparison G xi xj vk =
      G.map (prodMapFirstThird (B := Over.mk (F.sourceFamily.f j))
        (localGluing F D i k).hom.left) ≫
        tripleComparison G xi xj vk := by
    calc
      _ = G.map (prod.map (localGluing F D i j).hom.left
            (𝟙 (Over.mk (F.sourceFamily.f k)))) ≫
          (G.map (prodMapLastTwo (localGluing F D j k).hom.left) ≫
            tripleComparison G xi xj vk) := by simp [Functor.map_comp, Category.assoc]
      _ = G.map (prod.map (localGluing F D i j).hom.left
            (𝟙 (Over.mk (F.sourceFamily.f k)))) ≫
          (tripleComparison G xi vj xk ≫
            prodMapLastTwo
              (D.gluing (F.familyHom.s₀ j) (F.familyHom.s₀ k)).hom.left) := by
              rw [hjk]
      _ = (tripleComparison G vi xj xk ≫
          prod.map (D.gluing (F.familyHom.s₀ i)
            (F.familyHom.s₀ j)).hom.left
            (𝟙 (Over.mk (F.targetFamily.f (F.familyHom.s₀ k))))) ≫
            prodMapLastTwo
              (D.gluing (F.familyHom.s₀ j) (F.familyHom.s₀ k)).hom.left := by
              rw [← hij]
              simp [Category.assoc]
      _ = tripleComparison G vi xj xk ≫
          prodMapFirstThird
            (D.gluing (F.familyHom.s₀ i) (F.familyHom.s₀ k)).hom.left := by
              simp only [Category.assoc]
              rw [D.cocycle (F.familyHom.s₀ i)
                (F.familyHom.s₀ j) (F.familyHom.s₀ k)]
              rfl
      _ = _ := by rw [← hik]
  have hk := congrArg (fun q ↦ q ≫ prod.snd) hcomp
  simp only [Category.assoc, tripleComparison_snd] at hk
  have hk' := congrArg Over.Hom.left hk
  simpa only [G, vk, localToGlobalV, Over.comp_left,
    Over.map_map_left, Over.homMk_left, Category.assoc] using hk'

/-- Pull a descent datum back componentwise along a morphism of families.  If the morphism has
index map `α` and component maps `gᵢ`, its objects are `gᵢ * Y_(α i)` and its gluing
isomorphisms are the pullbacks of the original gluing isomorphisms along `gᵢ × gᵢ'`. -/
@[stacks 02VS "pulled_back_datum"]
noncomputable def pulledBackDatum (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) :
    DescentData F.sourceFamily.f :=
  { obj := localObj F D
    gluing := localGluing F D
    cocycle i j k := by
      apply prod.hom_ext
      · apply prod.hom_ext
        · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc,
            localGluing_fst]
        · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc,
            localGluing_fst, localGluing_snd]
      · apply Over.OverMorphism.ext
        apply pullback.hom_ext
        · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc,
            localGluing_fst, Over.comp_left,
            prod.comp_lift, prod.comp_lift_assoc]
          simpa [prodMapLastTwo, prodMapFirstThird, Category.assoc,
            Over.comp_left, prod.comp_lift, prod.comp_lift_assoc] using
            localCocycle_fst F D i j k
        · simp [prodMapLastTwo, prodMapFirstThird, Category.assoc,
            localGluing_fst, localGluing_snd_pullback, Over.comp_left,
            prod.comp_lift, prod.comp_lift_assoc]
          simp only [← Over.comp_left, prod.lift_snd] }

/-- The component of the pulled-back datum at `i` is the pullback of the component at
`F.familyHom.s₀ i`. -/
@[stacks 02VS "pulled_back_datum"]
lemma pulledBackDatum_obj (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    (pulledBackDatum F D).obj i =
      (Over.pullback (F.familyHom.h₀ i)).obj (D.obj (F.familyHom.s₀ i)) :=
  rfl

-- The accepted definitions below must generate their own auxiliary pullback proofs.
-- The local construction above generates proofs of the same propositions, which
-- Lean would otherwise reuse and thereby change the definitions' recorded values.
run_meta do
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {}

/-- The canonical identification of a component of the pulled-back datum with its
chosen pullback. -/
noncomputable def pulledBackDatumObjIso (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    (pulledBackDatum F D).obj i ≅
      (Over.pullback (F.familyHom.h₀ i)).obj (D.obj (F.familyHom.s₀ i)) :=
  eqToIso (pulledBackDatum_obj F D i)

/-- The identification of a component of the pulled-back datum with its chosen pullback is
the identity on underlying schemes. -/
private lemma pulledBackDatumObjIso_hom_left (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i : F.sourceFamily.I₀) :
    (pulledBackDatumObjIso F D i).hom.left = 𝟙 _ :=
  rfl

/-- The canonical map from the source of a pulled-back transition map to the source of
the original transition map. -/
noncomputable def pulledBackDatumSourceMap (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i i' : F.sourceFamily.I₀) :
    pullback (((pulledBackDatum F D).obj i).hom ≫ F.sourceFamily.f i)
        (F.sourceFamily.f i') ⟶
      pullback ((D.obj (F.familyHom.s₀ i)).hom ≫
          F.targetFamily.f (F.familyHom.s₀ i))
        (F.targetFamily.f (F.familyHom.s₀ i')) :=
  pullback.lift
    (pullback.fst _ _ ≫ (pulledBackDatumObjIso F D i).hom.left ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ F.familyHom.h₀ i') (by
      simp only [Category.assoc, pullback.condition_assoc, F.familyHom.w₀]
      rw [← Over.pullback_obj_hom, Over.w_assoc]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ F.baseHom)
        (pullback.condition (f := ((pulledBackDatum F D).obj i).hom ≫
          F.sourceFamily.f i) (g := F.sourceFamily.f i')))

/-- The canonical map from the target of a pulled-back transition map to the target of
the original transition map. -/
noncomputable def pulledBackDatumTargetMap (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i i' : F.sourceFamily.I₀) :
    pullback (F.sourceFamily.f i)
        (((pulledBackDatum F D).obj i').hom ≫ F.sourceFamily.f i') ⟶
      pullback (F.targetFamily.f (F.familyHom.s₀ i))
        ((D.obj (F.familyHom.s₀ i')).hom ≫
          F.targetFamily.f (F.familyHom.s₀ i')) :=
  pullback.lift (pullback.fst _ _ ≫ F.familyHom.h₀ i)
    (pullback.snd _ _ ≫ (pulledBackDatumObjIso F D i').hom.left ≫ pullback.fst _ _) (by
      simp only [Category.assoc, pullback.condition_assoc, F.familyHom.w₀]
      rw [← Over.pullback_obj_hom, Over.w_assoc])

/-- On each pair of indices, the gluing isomorphism of the pulled-back datum is the
pullback of the original gluing isomorphism along the two component morphisms. -/
@[stacks 02VS "pulled_back_datum"]
lemma pulledBackDatum_gluing (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i i' : F.sourceFamily.I₀) :
    ((pulledBackDatum F D).gluingPullbackIso i i').hom ≫
        pulledBackDatumTargetMap F D i i' =
      pulledBackDatumSourceMap F D i i' ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ i')).hom := by
  have hs : pulledBackDatumSourceMap F D i i' = localSourceMap F D i i' := by
    apply pullback.hom_ext <;>
      simp [pulledBackDatumSourceMap, localSourceMap, pulledBackDatum,
        pullback.lift_fst, pullback.lift_snd, pulledBackDatumObjIso_hom_left]
  have ht : pulledBackDatumTargetMap F D i i' = localTargetMap F D i i' := by
    apply pullback.hom_ext <;>
      simp [pulledBackDatumTargetMap, localTargetMap, pulledBackDatum,
        pullback.lift_fst, pullback.lift_snd, pulledBackDatumObjIso_hom_left]
  rw [hs, ht]
  simpa [pulledBackDatum, DescentData.gluingPullbackIso, localGluing,
    localIso] using localForward_comm F D i i'

end AlgebraicGeometry.MorphismOfSchemeFamilies
