module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical distinguished triangles of the truncations of a complex

Let `K` be a cochain complex in an abelian category `C` and let `a : ℤ`. Write `τ_{≤a} K` and
`τ_{≥a} K` for the canonical truncations of `K` (`CochainComplex.truncLE`,
`CochainComplex.truncGE`): `τ_{≤a} K` is `K` in degrees `< a`, the cycles `ker(d^a)` in degree
`a` and `0` above, and `τ_{≥a} K` is `0` below `a`, the cokernel of `d^{a-1}` in degree `a` and
`K` above. This file builds, in `D(C)`, the three canonical distinguished triangles of
Stacks 08J5:
```
τ_{≤a} K ⟶ K ⟶ τ_{≥a+1} K ⟶ (τ_{≤a} K)[1]
τ_{≤a} K ⟶ τ_{≤a+1} K ⟶ H^{a+1}(K)[-a-1] ⟶ (τ_{≤a} K)[1]
H^a(K)[-a] ⟶ τ_{≥a} K ⟶ τ_{≥a+1} K ⟶ (H^a(K)[-a])[1]
```
Each vertex is the image under `DerivedCategory.Q` of a complex, `H^n(K)[-n]` being the complex
`(HomologicalComplex.single C (ComplexShape.up ℤ) n).obj (K.homology n)` with `H^n(K)` in degree
`n`, and the first two maps of each triangle are the images of the canonical maps of complexes.

## Main definitions

* `DerivedCategory.triangleTruncLETruncGE`: the triangle `τ_{≤a} K ⟶ K ⟶ τ_{≥a+1} K ⟶ …`, whose
  connecting map is the one of the short exact sequence `0 ⟶ τ_{≤a} K ⟶ K ⟶ K/τ_{≤a} K ⟶ 0`
  composed with the inverse of the quasi-isomorphism `K/τ_{≤a} K ⟶ τ_{≥a+1} K`.
* `DerivedCategory.triangleTruncLETruncLESucc`: the triangle
  `τ_{≤a} K ⟶ τ_{≤a+1} K ⟶ H^{a+1}(K)[-a-1] ⟶ …`.
* `DerivedCategory.triangleTruncGETruncGESucc`: the triangle
  `H^a(K)[-a] ⟶ τ_{≥a} K ⟶ τ_{≥a+1} K ⟶ …`.

## Main results

* `DerivedCategory.triangleTruncLETruncGE_distinguished`,
  `DerivedCategory.triangleTruncLETruncLESucc_distinguished` and
  `DerivedCategory.triangleTruncGETruncGESucc_distinguished`: the three triangles are
  distinguished.
* `DerivedCategory.exists_iso_triangleTruncLETruncGE_triangleLEGE`: the first triangle is
  isomorphic, by an isomorphism which is the identity on `K`, to the truncation triangle
  `TStructure.t.triangleLEGE` of the canonical t-structure.

## Implementation notes

The second and third triangles are obtained, as in Stacks, from the first one: the second is the
first one for the complex `τ_{≤a+1} K`, and the third is the first one for `τ_{≥a}K`, after the
identifications `τ_{≤a} τ_{≤a+1} K ≅ τ_{≤a} K`, `τ_{≥a+1} τ_{≤a+1} K ≅ H^{a+1}(K)[-a-1]`,
`τ_{≤a} τ_{≥a} K ≅ H^a(K)[-a]` and `τ_{≥a+1} τ_{≥a} K ≅ τ_{≥a+1} K`. The two identifications with
single complexes are isomorphisms of complexes (`CochainComplex.isoSingleHomology`), the other
two are images in `D(C)` of quasi-isomorphisms.

## References

* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A cochain complex concentrated in the single degree `n` is isomorphic to its term in degree
`n` placed in degree `n`. -/
def isoSingle (M : CochainComplex C ℤ) (n : ℤ) [M.IsStrictlyGE n] [M.IsStrictlyLE n] :
    M ≅ (single C (ComplexShape.up ℤ) n).obj (M.X n) where
  hom := mkHomToSingle (𝟙 _) (fun i hi ↦
    (M.isZero_of_isStrictlyGE n i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_src _ _)
  inv := mkHomFromSingle (𝟙 _) (fun i hi ↦
    (M.isZero_of_isStrictlyLE n i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  hom_inv_id := by
    ext i
    obtain hi | rfl | hi := lt_trichotomy i n
    · apply (M.isZero_of_isStrictlyGE n i (by omega)).eq_of_src
    · simp [mkHomToSingle_f, mkHomFromSingle_f]
    · apply (M.isZero_of_isStrictlyLE n i (by omega)).eq_of_tgt
  inv_hom_id := by
    apply from_single_hom_ext
    simp [mkHomToSingle_f, mkHomFromSingle_f]

/-- A cochain complex concentrated in the single degree `n` is isomorphic to its cohomology in
degree `n` placed in degree `n`. -/
def isoSingleHomology (M : CochainComplex C ℤ) (n : ℤ) [M.IsStrictlyGE n] [M.IsStrictlyLE n] :
    M ≅ (single C (ComplexShape.up ℤ) n).obj (M.homology n) :=
  M.isoSingle n ≪≫ (single C (ComplexShape.up ℤ) n).mapIso
    ((singleObjHomologySelfIso (ComplexShape.up ℤ) n (M.X n)).symm ≪≫
      (homologyFunctor C (ComplexShape.up ℤ) n).mapIso (M.isoSingle n).symm)

variable (K : CochainComplex C ℤ)

/-- The canonical inclusion `τ_{≤a} K ⟶ τ_{≤b} K` of truncations of a cochain complex,
for `a ≤ b`. -/
def ιTruncLEOfLE (a b : ℤ) (h : a ≤ b) : K.truncLE a ⟶ K.truncLE b :=
  have := (K.truncLE a).isStrictlyLE_of_le a b h
  inv ((K.truncLE a).ιTruncLE b) ≫ truncLEMap (K.ιTruncLE a) b

@[reassoc (attr := simp)]
lemma ιTruncLEOfLE_ιTruncLE (a b : ℤ) (h : a ≤ b) :
    K.ιTruncLEOfLE a b h ≫ K.ιTruncLE b = K.ιTruncLE a := by
  have := (K.truncLE a).isStrictlyLE_of_le a b h
  simp [ιTruncLEOfLE, CochainComplex.ιTruncLE_naturality]

/-- The canonical projection `τ_{≥a} K ⟶ τ_{≥b} K` of truncations of a cochain complex,
for `a ≤ b`. -/
def πTruncGEOfLE (a b : ℤ) (h : a ≤ b) : K.truncGE a ⟶ K.truncGE b :=
  have := (K.truncGE b).isStrictlyGE_of_ge a b h
  truncGEMap (K.πTruncGE b) a ≫ inv ((K.truncGE b).πTruncGE a)

@[reassoc (attr := simp)]
lemma πTruncGE_πTruncGEOfLE (a b : ℤ) (h : a ≤ b) :
    K.πTruncGE a ≫ K.πTruncGEOfLE a b h = K.πTruncGE b := by
  have := (K.truncGE b).isStrictlyGE_of_ge a b h
  simp [πTruncGEOfLE, reassoc_of% (CochainComplex.πTruncGE_naturality (K.πTruncGE b) a)]

/-- The isomorphism of complexes `τ_{≥n} τ_{≤n} K ≅ H^n(K)[-n]`. -/
def truncGETruncLEIsoSingleHomology (n : ℤ) :
    (K.truncLE n).truncGE n ≅ (single C (ComplexShape.up ℤ) n).obj (K.homology n) :=
  ((K.truncLE n).truncGE n).isoSingleHomology n ≪≫ (single C (ComplexShape.up ℤ) n).mapIso
    ((isoOfQuasiIsoAt ((K.truncLE n).πTruncGE n) n).symm ≪≫
      isoOfQuasiIsoAt (K.ιTruncLE n) n)

/-- The isomorphism of complexes `H^n(K)[-n] ≅ τ_{≤n} τ_{≥n} K`. -/
def singleHomologyIsoTruncLETruncGE (n : ℤ) :
    (single C (ComplexShape.up ℤ) n).obj (K.homology n) ≅ (K.truncGE n).truncLE n :=
  (single C (ComplexShape.up ℤ) n).mapIso
    (isoOfQuasiIsoAt (K.πTruncGE n) n ≪≫ (isoOfQuasiIsoAt ((K.truncGE n).ιTruncLE n) n).symm) ≪≫
    (((K.truncGE n).truncLE n).isoSingleHomology n).symm

/-- The canonical map of complexes `τ_{≤n} K ⟶ H^n(K)[-n]`, the projection
`τ_{≤n} K ⟶ τ_{≥n} τ_{≤n} K` followed by the isomorphism `truncGETruncLEIsoSingleHomology`; its
component in degree `n` is the projection `ker(d^n) ⟶ H^n(K)`. -/
def truncLEToSingleHomology (n : ℤ) :
    K.truncLE n ⟶ (single C (ComplexShape.up ℤ) n).obj (K.homology n) :=
  (K.truncLE n).πTruncGE n ≫ (K.truncGETruncLEIsoSingleHomology n).hom

/-- The canonical map of complexes `H^n(K)[-n] ⟶ τ_{≥n} K`, the isomorphism
`singleHomologyIsoTruncLETruncGE` followed by the inclusion `τ_{≤n} τ_{≥n} K ⟶ τ_{≥n} K`; its
component in degree `n` is the inclusion `H^n(K) ⟶ coker(d^{n-1})`. -/
def singleHomologyToTruncGE (n : ℤ) :
    (single C (ComplexShape.up ℤ) n).obj (K.homology n) ⟶ K.truncGE n :=
  (K.singleHomologyIsoTruncLETruncGE n).hom ≫ (K.truncGE n).ιTruncLE n

end CochainComplex

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open CochainComplex

lemma isIso_Q_map_shortComplexTruncLEX₃ToTruncGE (K : CochainComplex C ℤ) (a b : ℤ)
    (h : a + 1 = b) : IsIso (Q.map (K.shortComplexTruncLEX₃ToTruncGE a b h)) := by
  rw [isIso_Q_map_iff_quasiIso]
  exact inferInstanceAs (QuasiIso (HomologicalComplex.shortComplexTruncLEX₃ToTruncGE K
    (ComplexShape.Embedding.embeddingUpInt_areComplementary a b h)))

lemma isIso_Q_map_truncLEMap_ιTruncLE (K : CochainComplex C ℤ) (a b : ℤ) (h : a ≤ b) :
    IsIso (Q.map (truncLEMap (K.ιTruncLE b) a)) := by
  rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncLEMap_iff]
  intro i hi
  exact K.quasiIsoAt_ιTruncLE b i (by omega)

lemma isIso_Q_map_truncGEMap_πTruncGE (K : CochainComplex C ℤ) (a b : ℤ) (h : a ≤ b) :
    IsIso (Q.map (truncGEMap (K.πTruncGE a) b)) := by
  rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEMap_iff]
  intro i hi
  exact K.quasiIsoAt_πTruncGE a i (by omega)

/-- The connecting map `τ_{≥a+1} K ⟶ (τ_{≤a} K)[1]` in `D(C)`: the connecting map of the short
exact sequence `0 ⟶ τ_{≤a} K ⟶ K ⟶ K/τ_{≤a} K ⟶ 0` composed with the inverse of the
quasi-isomorphism `K/τ_{≤a} K ⟶ τ_{≥a+1} K`. -/
def truncLETruncGEδ (K : CochainComplex C ℤ) (a : ℤ) :
    Q.obj (K.truncGE (a + 1)) ⟶ (Q.obj (K.truncLE a))⟦(1 : ℤ)⟧ :=
  have := isIso_Q_map_shortComplexTruncLEX₃ToTruncGE K a (a + 1) rfl
  inv (Q.map (K.shortComplexTruncLEX₃ToTruncGE a (a + 1) rfl)) ≫
    triangleOfSESδ (K.shortComplexTruncLE_shortExact a)

/-- The triangle `τ_{≤a} K ⟶ K ⟶ τ_{≥a+1} K ⟶ (τ_{≤a} K)[1]` in `D(C)` attached to a cochain
complex `K`: its first two maps are the canonical maps of complexes, and its third map is the
connecting map `truncLETruncGEδ K a` of the short exact sequence
`0 ⟶ τ_{≤a} K ⟶ K ⟶ K/τ_{≤a} K ⟶ 0`. -/
def triangleTruncLETruncGE (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map (K.ιTruncLE a)) (Q.map (K.πTruncGE (a + 1))) (truncLETruncGEδ K a)

/-- **Stacks Project, Tag 08J5** (1). For a complex `K` and an integer `a`, the triangle
`τ_{≤a} K ⟶ K ⟶ τ_{≥a+1} K ⟶ (τ_{≤a} K)[1]` on the canonical truncations of `K`, with the
canonical maps, is distinguished in `D(C)`. -/
@[stacks 08J5 "(1) the triangle τ_{≤a}K → K → τ_{≥a+1}K → (τ_{≤a}K)[1] on the truncations of \
the complex K, with connecting map from the short exact sequence 0 → τ_{≤a}K → K → K/τ_{≤a}K → 0"]
theorem triangleTruncLETruncGE_distinguished (K : CochainComplex C ℤ) (a : ℤ) :
    triangleTruncLETruncGE K a ∈ distTriang (DerivedCategory C) := by
  have h := K.shortComplexTruncLE_shortExact a
  have := isIso_Q_map_shortComplexTruncLEX₃ToTruncGE K a (a + 1) rfl
  refine isomorphic_distinguished _ (triangleOfSES_distinguished h) _ (Iso.symm ?_)
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (@asIso _ _ _ _ (Q.map (K.shortComplexTruncLEX₃ToTruncGE a (a + 1) rfl)) this) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Q.map_comp _ _).symm.trans
      ((congrArg Q.map (K.g_shortComplexTruncLEX₃ToTruncGE a (a + 1) rfl)).trans
        (Category.id_comp _).symm)
  · have e : triangleOfSESδ h ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        (𝟙 (Q.obj (K.shortComplexTruncLE a).X₁)) = triangleOfSESδ h := by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact e.trans (@IsIso.hom_inv_id_assoc _ _ _ _
      (Q.map (K.shortComplexTruncLEX₃ToTruncGE a (a + 1) rfl)) this _ (triangleOfSESδ h)).symm

/-- The triangle `triangleTruncLETruncGE K a` is isomorphic, by an isomorphism which is the
identity on `K`, to the truncation triangle of the canonical t-structure on `D(C)`. -/
theorem exists_iso_triangleTruncLETruncGE_triangleLEGE (K : CochainComplex C ℤ) (a : ℤ) :
    ∃ e : triangleTruncLETruncGE K a ≅
        (TStructure.t.triangleLEGE a (a + 1) rfl).obj (Q.obj K),
      e.hom.hom₂ = 𝟙 _ := by
  let T := triangleTruncLETruncGE K a
  have hT : T ∈ distTriang _ := triangleTruncLETruncGE_distinguished K a
  have hT' := TStructure.t.triangleLEGE_distinguished a (a + 1) rfl (Q.obj K)
  have h₃ : TStructure.t.IsGE T.obj₃ (a + 1) :=
    inferInstanceAs ((Q.obj (K.truncGE (a + 1))).IsGE (a + 1))
  have h₁ : TStructure.t.IsLE T.obj₁ a := inferInstanceAs ((Q.obj (K.truncLE a)).IsLE a)
  have hiso := TStructure.t.isIso₁_truncLE_map_of_isGE T hT a (a + 1) rfl h₃
  have := (TStructure.t.isLE_iff_isIso_truncLEι_app a T.obj₁).1 h₁
  let u : T.obj₁ ⟶ ((TStructure.t.triangleLEGE a (a + 1) rfl).obj (Q.obj K)).obj₁ :=
    inv ((TStructure.t.truncLEι a).app T.obj₁) ≫ (TStructure.t.truncLE a).map T.mor₁
  have hnat : (TStructure.t.truncLE a).map T.mor₁ ≫ (TStructure.t.truncLEι a).app T.obj₂ =
      (TStructure.t.truncLEι a).app T.obj₁ ≫ T.mor₁ := (TStructure.t.truncLEι a).naturality T.mor₁
  have hu' : T.mor₁ = (inv ((TStructure.t.truncLEι a).app T.obj₁) ≫
      (TStructure.t.truncLE a).map T.mor₁) ≫ (TStructure.t.truncLEι a).app T.obj₂ := by
    rw [Category.assoc, hnat, IsIso.inv_hom_id_assoc]
  have hu : T.mor₁ ≫ 𝟙 _ = u ≫ ((TStructure.t.triangleLEGE a (a + 1) rfl).obj (Q.obj K)).mor₁ := by
    rw [Category.comp_id]
    exact hu'
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism _ _ hT hT' u (𝟙 _) hu
  let φ : T ⟶ (TStructure.t.triangleLEGE a (a + 1) rfl).obj (Q.obj K) :=
    { hom₁ := u, hom₂ := 𝟙 _, hom₃ := c, comm₁ := hu, comm₂ := hc₂, comm₃ := hc₃ }
  have h₁' : IsIso φ.hom₁ := @IsIso.comp_isIso _ _ _ _ _ _ _ (IsIso.inv_isIso) hiso
  have h₂' : IsIso φ.hom₂ := by change IsIso (𝟙 _); infer_instance
  have := isIso₃_of_isIso₁₂ φ hT hT' h₁' h₂'
  have : IsIso φ := Triangle.isIso_of_isIsos φ h₁' h₂' this
  exact ⟨asIso φ, rfl⟩

/-- The triangle `τ_{≤a} K ⟶ τ_{≤a+1} K ⟶ H^{a+1}(K)[-a-1] ⟶ (τ_{≤a} K)[1]` in `D(C)` attached
to a cochain complex `K`: its first map is the canonical inclusion of truncations, its second
map is the canonical map `CochainComplex.truncLEToSingleHomology` (in degree `a+1` the
projection `ker(d^{a+1}) ⟶ H^{a+1}(K)`), and its third map is the connecting map of
`truncLETruncGEδ (τ_{≤a+1} K) a` transported along these identifications. -/
def triangleTruncLETruncLESucc (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map (K.ιTruncLEOfLE a (a + 1) (by omega)))
    (Q.map (K.truncLEToSingleHomology (a + 1)))
    (Q.map (K.truncGETruncLEIsoSingleHomology (a + 1)).inv ≫
      truncLETruncGEδ (K.truncLE (a + 1)) a ≫
        (Q.map (truncLEMap (K.ιTruncLE (a + 1)) a))⟦(1 : ℤ)⟧')

/-- **Stacks Project, Tag 08J5** (2). For a complex `K` and an integer `a`, the triangle
`τ_{≤a} K ⟶ τ_{≤a+1} K ⟶ H^{a+1}(K)[-a-1] ⟶ (τ_{≤a} K)[1]`, whose first map is the canonical
inclusion of truncations and whose second map is the canonical projection onto the cohomology in
degree `a + 1`, is distinguished in `D(C)`. -/
@[stacks 08J5 "(2) the triangle τ_{≤a}K → τ_{≤a+1}K → H^{a+1}(K)[-a-1] → (τ_{≤a}K)[1] on the \
truncations of the complex K, with the canonical maps"]
theorem triangleTruncLETruncLESucc_distinguished (K : CochainComplex C ℤ) (a : ℤ) :
    triangleTruncLETruncLESucc K a ∈ distTriang (DerivedCategory C) := by
  have := isIso_Q_map_truncLEMap_ιTruncLE K a (a + 1) (by omega)
  refine isomorphic_distinguished _
    (triangleTruncLETruncGE_distinguished (K.truncLE (a + 1)) a) _ ?_
  refine Triangle.isoMk _ _
    (@asIso _ _ _ _ (Q.map (truncLEMap (K.ιTruncLE (a + 1)) a)) this).symm
    (Iso.refl _) (Q.mapIso (K.truncGETruncLEIsoSingleHomology (a + 1))).symm ?_ ?_ ?_
  · change Q.map (K.ιTruncLEOfLE a (a + 1) (by omega)) ≫ 𝟙 _ =
      inv (Q.map (truncLEMap (K.ιTruncLE (a + 1)) a)) ≫ Q.map ((K.truncLE (a + 1)).ιTruncLE a)
    rw [Category.comp_id, IsIso.eq_inv_comp, ← Q.map_comp]
    congr 1
    have : Mono (K.ιTruncLE (a + 1)) := inferInstanceAs
      (Mono (HomologicalComplex.ιTruncLE K (ComplexShape.embeddingUpIntLE (a + 1))))
    rw [← cancel_mono (K.ιTruncLE (a + 1)), Category.assoc,
      CochainComplex.ιTruncLEOfLE_ιTruncLE, CochainComplex.ιTruncLE_naturality]
  · change Q.map (K.truncLEToSingleHomology (a + 1)) ≫
        Q.map (K.truncGETruncLEIsoSingleHomology (a + 1)).inv =
      𝟙 _ ≫ Q.map ((K.truncLE (a + 1)).πTruncGE (a + 1))
    rw [Category.id_comp, ← Q.map_comp, truncLEToSingleHomology, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  · change (Q.map (K.truncGETruncLEIsoSingleHomology (a + 1)).inv ≫
        truncLETruncGEδ (K.truncLE (a + 1)) a ≫
          (Q.map (truncLEMap (K.ιTruncLE (a + 1)) a))⟦(1 : ℤ)⟧') ≫
        (inv (Q.map (truncLEMap (K.ιTruncLE (a + 1)) a)))⟦(1 : ℤ)⟧' =
      Q.map (K.truncGETruncLEIsoSingleHomology (a + 1)).inv ≫
        truncLETruncGEδ (K.truncLE (a + 1)) a
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]

/-- The triangle `H^a(K)[-a] ⟶ τ_{≥a} K ⟶ τ_{≥a+1} K ⟶ (H^a(K)[-a])[1]` in `D(C)` attached to a
cochain complex `K`: its first map is the canonical map `CochainComplex.singleHomologyToTruncGE`
(in degree `a` the inclusion `H^a(K) ⟶ coker(d^{a-1})`), its second map is the canonical
projection of truncations, and its third map is the connecting map of
`truncLETruncGEδ (τ_{≥a} K) a` transported along these identifications. -/
def triangleTruncGETruncGESucc (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map (K.singleHomologyToTruncGE a))
    (Q.map (K.πTruncGEOfLE a (a + 1) (by omega)))
    (Q.map (truncGEMap (K.πTruncGE a) (a + 1)) ≫
      truncLETruncGEδ (K.truncGE a) a ≫
        (Q.map (K.singleHomologyIsoTruncLETruncGE a).inv)⟦(1 : ℤ)⟧')

/-- **Stacks Project, Tag 08J5** (3). For a complex `K` and an integer `a`, the triangle
`H^a(K)[-a] ⟶ τ_{≥a} K ⟶ τ_{≥a+1} K ⟶ (H^a(K)[-a])[1]`, whose first map is the canonical
inclusion of the cohomology in degree `a` and whose second map is the canonical projection of
truncations, is distinguished in `D(C)`. -/
@[stacks 08J5 "(3) the triangle H^a(K)[-a] → τ_{≥a}K → τ_{≥a+1}K → H^a(K)[-a+1] on the \
truncations of the complex K, with the canonical maps"]
theorem triangleTruncGETruncGESucc_distinguished (K : CochainComplex C ℤ) (a : ℤ) :
    triangleTruncGETruncGESucc K a ∈ distTriang (DerivedCategory C) := by
  have := isIso_Q_map_truncGEMap_πTruncGE K a (a + 1) (by omega)
  refine isomorphic_distinguished _
    (triangleTruncLETruncGE_distinguished (K.truncGE a) a) _ ?_
  refine Triangle.isoMk _ _ (Q.mapIso (K.singleHomologyIsoTruncLETruncGE a))
    (Iso.refl _) (@asIso _ _ _ _ (Q.map (truncGEMap (K.πTruncGE a) (a + 1))) this) ?_ ?_ ?_
  · change Q.map (K.singleHomologyToTruncGE a) ≫ 𝟙 _ =
      Q.map (K.singleHomologyIsoTruncLETruncGE a).hom ≫ Q.map ((K.truncGE a).ιTruncLE a)
    rw [Category.comp_id, ← Q.map_comp]
    rfl
  · change Q.map (K.πTruncGEOfLE a (a + 1) (by omega)) ≫
        Q.map (truncGEMap (K.πTruncGE a) (a + 1)) =
      𝟙 _ ≫ Q.map ((K.truncGE a).πTruncGE (a + 1))
    rw [Category.id_comp, ← Q.map_comp]
    congr 1
    have : Epi (K.πTruncGE a) := inferInstanceAs
      (Epi (HomologicalComplex.πTruncGE K (ComplexShape.embeddingUpIntGE a)))
    rw [← cancel_epi (K.πTruncGE a), CochainComplex.πTruncGE_πTruncGEOfLE_assoc,
      CochainComplex.πTruncGE_naturality]
  · change (Q.map (truncGEMap (K.πTruncGE a) (a + 1)) ≫
        truncLETruncGEδ (K.truncGE a) a ≫
          (Q.map (K.singleHomologyIsoTruncLETruncGE a).inv)⟦(1 : ℤ)⟧') ≫
        (Q.map (K.singleHomologyIsoTruncLETruncGE a).hom)⟦(1 : ℤ)⟧' =
      Q.map (truncGEMap (K.πTruncGE a) (a + 1)) ≫ truncLETruncGEδ (K.truncGE a) a
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Q.map_comp, Iso.inv_hom_id,
      Q.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

end DerivedCategory

end
