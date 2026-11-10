module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.CoproductComparison

/-!
# Glueing objects and compact objects across two localizations

This file isolates the formal half of the inductive step of the theorem of Bondal–van den Bergh,
[Stacks, Tag 09IS], in the form [Stacks, Tag 08DG] and [Stacks, Tag 09IM] use it. Let `T` be a
pretriangulated category — `D_QCoh(𝒪_X)` for a scheme `X = U ∪ V` — together with two
"restrictions" `a_U : T ⥤ T_U` and `a_V : T ⥤ T_V`, each left adjoint to a fully faithful
functor `R_U`, `R_V` (the derived direct images), and two further restrictions
`b_U : T_U ⥤ T_W`, `b_V : T_V ⥤ T_W` to the overlap, left adjoint to fully faithful `S_U`, `S_V`.

* `CategoryTheory.Pretriangulated.exists_glue` — **glueing**. If `a_V R_U ≅ S_V b_U` and
  `a_U R_V ≅ S_U b_V` objectwise (base change for the two open immersions), then for objects
  `A` of `T_U` and `Q` of `T_V` with `b_U A ≅ b_V Q` there is an object `R` of `T` with
  `a_U R ≅ A` and `a_V R ≅ Q`. It is the fibre of a map `R_U A ⊞ R_V Q ⟶ R_V S_V b_V Q`.
* `CategoryTheory.Pretriangulated.isCompactObject_of_isCompactObject_restrict` — **compactness
  is local**. If every object killed by `a_V` is in the essential image of `R_U` and the `R`'s
  commute with direct sums, an object whose two restrictions are compact is compact.

The only triangulated input of the glueing is the elementary
`CategoryTheory.Pretriangulated.isIso_comp_fst_of_isIso_inr_comp`: the fibre of a morphism out of
a direct sum which is invertible on one summand is the other summand.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

@[expose] public section

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Pretriangulated

open Category Limits Preadditive

/-! ### The fibre of a map out of a direct sum -/

section Fibre

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The fibre of a map out of a direct sum which is invertible on the second summand is the
first summand.** Let `R ⟶ M₁ ⊕ M₂ ⟶ M₃ ⟶ R⟦1⟧` be a distinguished triangle whose second map is
invertible on `M₂`. Then `R ⟶ M₁ ⊕ M₂ ⟶ M₁` is an isomorphism.

An automorphism of `M₁ ⊕ M₂` turns the second map into the projection to `M₂` followed by an
isomorphism, and the fibre of the projection is the split triangle of the direct sum. -/
lemma isIso_comp_fst_of_isIso_inr_comp {R M₁ M₂ M₃ : D} (B : BinaryBicone M₁ M₂)
    (hB : B.fst ≫ B.inl + B.snd ≫ B.inr = 𝟙 B.pt) (u : R ⟶ B.pt) (d : B.pt ⟶ M₃)
    (w : M₃ ⟶ R⟦(1 : ℤ)⟧) (hT : Triangle.mk u d w ∈ distTriang D) (hd : IsIso (B.inr ≫ d)) :
    IsIso (u ≫ B.fst) := by
  set e := B.inr ≫ d with he
  let ψ : B.pt ⟶ B.pt := 𝟙 _ - B.fst ≫ B.inl ≫ d ≫ inv e ≫ B.inr
  let ψ' : B.pt ⟶ B.pt := 𝟙 _ + B.fst ≫ B.inl ≫ d ≫ inv e ≫ B.inr
  have hψψ' : ψ ≫ ψ' = 𝟙 _ := by
    simp only [ψ, ψ', sub_comp, comp_add, id_comp, comp_id, assoc, BinaryBicone.inr_fst_assoc,
      zero_comp, comp_zero]
    abel
  have hψ'ψ : ψ' ≫ ψ = 𝟙 _ := by
    simp only [ψ, ψ', add_comp, comp_sub, id_comp, comp_id, assoc, BinaryBicone.inr_fst_assoc,
      zero_comp, comp_zero]
    abel
  have : IsIso ψ := ⟨⟨ψ', hψψ', hψ'ψ⟩⟩
  have hd' : d = B.fst ≫ B.inl ≫ d + B.snd ≫ e := by
    conv_lhs => rw [← id_comp d, ← hB]
    simp [he, add_comp]
  have hψd : ψ ≫ d = B.snd ≫ e := by
    have h₁ : ψ ≫ d = d - B.fst ≫ B.inl ≫ d := by
      simp only [ψ, sub_comp, id_comp, assoc, ← he, IsIso.inv_hom_id, comp_id]
    rw [h₁]
    nth_rw 1 [hd']
    abel
  let eB : B.pt ≅ M₁ ⊞ M₂ :=
    { hom := biprod.lift B.fst B.snd
      inv := biprod.desc B.inl B.inr
      hom_inv_id := by rw [biprod.lift_desc, hB]
      inv_hom_id := by apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp }
  have hinl : B.inl ≫ eB.hom = biprod.inl := by apply biprod.hom_ext <;> simp [eB]
  have hT₀ : Triangle.mk B.inl B.snd (0 : M₂ ⟶ M₁⟦(1 : ℤ)⟧) ∈ distTriang D := by
    refine isomorphic_distinguished _ (binaryBiproductTriangle_distinguished M₁ M₂) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) eB (Iso.refl _) ?_ ?_ ?_
    · exact hinl.trans (id_comp _).symm
    · simp [eB, binaryBiproductTriangle]
    · simp [binaryBiproductTriangle]
  obtain ⟨a, ha₁, ha₂⟩ := complete_distinguished_triangle_morphism₁ _ _ hT₀ hT ψ e hψd.symm
  let φ : Triangle.mk B.inl B.snd (0 : M₂ ⟶ M₁⟦(1 : ℤ)⟧) ⟶ Triangle.mk u d w :=
    { hom₁ := a
      hom₂ := ψ
      hom₃ := e
      comm₁ := ha₁
      comm₂ := hψd.symm
      comm₃ := ha₂ }
  have : IsIso a := isIso₁_of_isIso₂₃ φ hT₀ hT (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  have hau : a ≫ u ≫ B.fst = 𝟙 _ := by
    have : a ≫ u = B.inl ≫ ψ := ha₁.symm
    rw [← assoc, this]
    simp [ψ, sub_comp]
  have : u ≫ B.fst = inv a := by
    rw [← cancel_epi a, hau, IsIso.hom_inv_id]
  rw [this]
  infer_instance

/-- **The fibre of a map out of a direct sum which is invertible on the first summand is the
second summand**: `isIso_comp_fst_of_isIso_inr_comp` for the swapped bicone. -/
lemma isIso_comp_snd_of_isIso_inl_comp {R M₁ M₂ M₃ : D} (B : BinaryBicone M₁ M₂)
    (hB : B.fst ≫ B.inl + B.snd ≫ B.inr = 𝟙 B.pt) (u : R ⟶ B.pt) (d : B.pt ⟶ M₃)
    (w : M₃ ⟶ R⟦(1 : ℤ)⟧) (hT : Triangle.mk u d w ∈ distTriang D) (hd : IsIso (B.inl ≫ d)) :
    IsIso (u ≫ B.snd) :=
  isIso_comp_fst_of_isIso_inr_comp
    { pt := B.pt, fst := B.snd, snd := B.fst, inl := B.inr, inr := B.inl }
    ((add_comm _ _).trans hB) u d w hT hd

end Fibre

/-! ### Units of an adjunction with invertible counit -/

section Unit

variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
  {a : C ⥤ E} {R : E ⥤ C} (adj : a ⊣ R)

/-- For an adjunction with invertible counit, the left adjoint inverts the unit. -/
private lemma isIso_map_unit_app [IsIso adj.counit] (X : C) : IsIso (a.map (adj.unit.app X)) :=
  isIso_of_comp_hom_eq_id (adj.counit.app (a.obj X)) (adj.left_triangle_components X)

include adj in
/-- For an adjunction with invertible counit, the unit is invertible at every object in the image
of the right adjoint: the triangle identity exhibits it as the inverse of `R ε`. -/
lemma isIso_unit_app_obj [IsIso adj.counit] (Y : E) : IsIso (adj.unit.app (R.obj Y)) :=
  isIso_of_comp_hom_eq_id (R.map (adj.counit.app Y)) (adj.right_triangle_components Y)

include adj in
/-- Invertibility of the unit is invariant under isomorphism of the object. -/
lemma isIso_unit_app_of_iso {X X' : C} (e : X ≅ X') (h : IsIso (adj.unit.app X')) :
    IsIso (adj.unit.app X) := by
  have hη : adj.unit.app X = e.hom ≫ adj.unit.app X' ≫ R.map (a.map e.inv) := by
    have := adj.unit.naturality e.hom
    dsimp at this
    rw [reassoc_of% this, ← R.map_comp, ← a.map_comp, e.hom_inv_id, a.map_id, R.map_id,
      comp_id]
  rw [hη]
  infer_instance

include adj in
/-- For an adjunction with invertible counit whose right adjoint commutes with the shift, the
objects at which the unit is invertible are closed under the shift. -/
lemma isIso_unit_app_shift [IsIso adj.counit] [HasShift C ℤ] [HasShift E ℤ] [R.CommShift ℤ]
    {X : C} (h : IsIso (adj.unit.app X)) (n : ℤ) : IsIso (adj.unit.app (X⟦n⟧)) :=
  isIso_unit_app_of_iso adj
    ((shiftFunctor C n).mapIso (asIso (adj.unit.app X)) ≪≫ (R.commShiftIso n).symm.app _)
    (isIso_unit_app_obj adj _)

include adj in
/-- If the right adjoint preserves a direct sum, the objects at which the unit is invertible are
closed under that direct sum. -/
lemma isIso_unit_app_of_isColimit {I : Type*} {A : I → C} {S : C} (j : ∀ i, A i ⟶ S)
    (hc : IsColimit (Cofan.mk S j)) [PreservesColimitsOfShape (Discrete I) R]
    (hA : ∀ i, IsIso (adj.unit.app (A i))) : IsIso (adj.unit.app S) := by
  have := adj.leftAdjoint_preservesColimits
  let hc' : IsColimit (Cofan.mk ((a ⋙ R).obj S) fun i => (a ⋙ R).map (j i)) :=
    isColimitCofanMkObjOfIsColimit (a ⋙ R) A j hc
  let ψ : (a ⋙ R).obj S ⟶ S := Cofan.IsColimit.desc hc' fun i => inv (adj.unit.app (A i)) ≫ j i
  have hψ : ∀ i, R.map (a.map (j i)) ≫ ψ = inv (adj.unit.app (A i)) ≫ j i := fun i =>
    Cofan.IsColimit.fac hc' _ i
  have hnat : ∀ i, j i ≫ adj.unit.app S = adj.unit.app (A i) ≫ R.map (a.map (j i)) := fun i =>
    adj.unit.naturality (j i)
  refine ⟨ψ, ?_, ?_⟩
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    change j i ≫ _ = j i ≫ _
    rw [reassoc_of% (hnat i), hψ, IsIso.hom_inv_id_assoc]
    exact (comp_id _).symm
  · refine Cofan.IsColimit.hom_ext hc' _ _ fun i => ?_
    change R.map (a.map (j i)) ≫ _ = R.map (a.map (j i)) ≫ _
    rw [reassoc_of% (hψ i), hnat, IsIso.inv_hom_id_assoc]
    exact (comp_id _).symm

end Unit

/-! ### Glueing -/

section Glue

variable {T : Type u₁} [Category.{v₁} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
  {TU : Type u₂} [Category.{v₂} TU] [Preadditive TU] [HasZeroObject TU] [HasShift TU ℤ]
  [∀ n : ℤ, (shiftFunctor TU n).Additive] [Pretriangulated TU]
  {TV : Type u₃} [Category.{v₃} TV] [Preadditive TV] [HasZeroObject TV] [HasShift TV ℤ]
  [∀ n : ℤ, (shiftFunctor TV n).Additive] [Pretriangulated TV]
  {TW : Type u₄} [Category.{v₄} TW] [Preadditive TW] [HasZeroObject TW] [HasShift TW ℤ]
  [∀ n : ℤ, (shiftFunctor TW n).Additive] [Pretriangulated TW]
  {aU : T ⥤ TU} {aV : T ⥤ TV} {RU : TU ⥤ T} {RV : TV ⥤ T}
  {bU : TU ⥤ TW} {bV : TV ⥤ TW} {SU : TW ⥤ TU} {SV : TW ⥤ TV}

/-- **Glueing along two localizations** ([Stacks, Tag 08DG]). Let `a_U ⊣ R_U`, `a_V ⊣ R_V`,
`b_V ⊣ S_V` be adjunctions with invertible counits between pretriangulated categories, with the
`a`'s, `b_V` and `R_V` exact, and assume the base change isomorphisms `a_V R_U ≅ S_V b_U` and
`a_U R_V ≅ S_U b_V` objectwise. Then for `A` in `T_U`, `Q` in `T_V` and an isomorphism
`b_U A ≅ b_V Q` there is an object `R` of `T` with `a_U R ≅ A` and `a_V R ≅ Q`.

`R` is the fibre of `(d₁, d₂) : R_U A ⊕ R_V Q ⟶ R_V S_V b_V Q`, where `d₂ = R_V(η)` for the unit
`η : Q ⟶ S_V b_V Q` and `d₁` is adjoint to `a_V R_U A ≅ S_V b_U A ≅ S_V b_V Q`. Restricted to `U`,
`d₂` becomes invertible, because its cone is `R_V` of an object killed by `b_V`, which `a_U`
kills by base change; restricted to `V`, `d₁` is invertible by construction. In both cases
`CategoryTheory.Pretriangulated.isIso_comp_fst_of_isIso_inr_comp` identifies the restriction of
the fibre with the other summand. -/
theorem exists_glue (adjU : aU ⊣ RU) (adjV : aV ⊣ RV) (adjV' : bV ⊣ SV)
    [aU.Additive] [aV.Additive] [SU.PreservesZeroMorphisms]
    [aU.CommShift ℤ] [aU.IsTriangulated] [aV.CommShift ℤ] [aV.IsTriangulated]
    [bV.CommShift ℤ] [bV.IsTriangulated] [RV.CommShift ℤ] [RV.IsTriangulated]
    [IsIso adjU.counit] [IsIso adjV.counit] [IsIso adjV'.counit]
    (βVU : ∀ A : TU, aV.obj (RU.obj A) ≅ SV.obj (bU.obj A))
    (βUV : ∀ Q : TV, aU.obj (RV.obj Q) ≅ SU.obj (bV.obj Q))
    (A : TU) (Q : TV) (φ : bU.obj A ≅ bV.obj Q) :
    ∃ R : T, Nonempty (aU.obj R ≅ A) ∧ Nonempty (aV.obj R ≅ Q) := by
  let d₁ : RU.obj A ⟶ RV.obj (SV.obj (bV.obj Q)) :=
    adjV.homEquiv _ _ ((βVU A).hom ≫ SV.map φ.hom)
  let d₂ : RV.obj Q ⟶ RV.obj (SV.obj (bV.obj Q)) := RV.map (adjV'.unit.app Q)
  obtain ⟨R, u, w, hT⟩ := distinguished_cocone_triangle₁ (biprod.desc d₁ d₂)
  refine ⟨R, ⟨?_⟩, ⟨?_⟩⟩
  · have hB := congrArg aU.map (biprod.total (X := RU.obj A) (Y := RV.obj Q))
    rw [aU.map_add, aU.map_comp, aU.map_comp, aU.map_id] at hB
    have hd : IsIso (aU.map biprod.inr ≫ aU.map (biprod.desc d₁ d₂)) := by
      rw [← aU.map_comp, biprod.inr_desc]
      obtain ⟨C, g, h, hC⟩ := distinguished_cocone_triangle (adjV'.unit.app Q)
      have hbη : IsIso (bV.map (adjV'.unit.app Q)) := isIso_map_unit_app adjV' Q
      have hbC : IsZero (bV.obj C) :=
        Triangle.isZero₃_of_isIso₁ _ (bV.map_distinguished _ hC) hbη
      have haC : IsZero (aU.obj (RV.obj C)) :=
        (SU.map_isZero hbC).of_iso (βUV C)
      exact (Triangle.isZero₃_iff_isIso₁ _
        (aU.map_distinguished _ (RV.map_distinguished _ hC))).1 haC
    have : IsIso (aU.map u ≫ aU.map biprod.fst) :=
      isIso_comp_fst_of_isIso_inr_comp (aU.mapBinaryBicone (BinaryBiproduct.bicone _ _)) hB
        (aU.map u) (aU.map (biprod.desc d₁ d₂)) _ (aU.map_distinguished _ hT) hd
    exact asIso (aU.map u ≫ aU.map biprod.fst) ≪≫ asIso (adjU.counit.app A)
  · have hB := congrArg aV.map (biprod.total (X := RU.obj A) (Y := RV.obj Q))
    rw [aV.map_add, aV.map_comp, aV.map_comp, aV.map_id] at hB
    have hd : IsIso (aV.map biprod.inl ≫ aV.map (biprod.desc d₁ d₂)) := by
      rw [← aV.map_comp, biprod.inl_desc]
      have h₁ : (adjV.homEquiv _ _).symm d₁ = (βVU A).hom ≫ SV.map φ.hom :=
        Equiv.symm_apply_apply _ _
      rw [Adjunction.homEquiv_counit] at h₁
      have h₂ : aV.map d₁ = ((βVU A).hom ≫ SV.map φ.hom) ≫ inv (adjV.counit.app _) := by
        rw [← h₁, assoc, IsIso.hom_inv_id, comp_id]
      rw [h₂]
      infer_instance
    have : IsIso (aV.map u ≫ aV.map biprod.snd) :=
      isIso_comp_snd_of_isIso_inl_comp (aV.mapBinaryBicone (BinaryBiproduct.bicone _ _)) hB
        (aV.map u) (aV.map (biprod.desc d₁ d₂)) _ (aV.map_distinguished _ hT) hd
    exact asIso (aV.map u ≫ aV.map biprod.snd) ≪≫ asIso (adjV.counit.app Q)

end Glue

/-! ### Compactness from two restrictions -/

section Compact

variable {T : Type u₁} [Category.{v₁} T] [Preadditive T]
  {TU : Type u₂} [Category.{v₂} TU] [Preadditive TU]
  {a : T ⥤ TU} {R : TU ⥤ T}

/-- **Compactness against objects in the image of a fully faithful right adjoint.** Let `a ⊣ R`
be an adjunction of additive functors and `K` an object whose image `a K` is compact. Then the
compactness map of `K` is bijective against every direct sum, indexed by `Type w`, of objects at
which the unit is invertible, provided the unit is invertible at the direct sum too. -/
lemma bijective_cofanMap_of_isIso_unit (adj : a ⊣ R) [a.Additive] [R.Additive] (K : T)
    (hK : IsCompactObject.{w} (a.obj K)) {I : Type w} [DecidableEq I] {A : I → T} {S : T}
    (j : ∀ i, A i ⟶ S) (hc : IsColimit (Cofan.mk S j))
    (hA : ∀ i, IsIso (adj.unit.app (A i))) (hS : IsIso (adj.unit.app S)) :
    Function.Bijective (cofanMap K j) := by
  have := adj.leftAdjoint_preservesColimits
  refine bijective_cofanMap_of_iso K _ j (fun i => (asIso (adj.unit.app (A i))).symm)
    (asIso (adj.unit.app S)).symm (fun i => ?_)
    (bijective_cofanMap_of_adjunction adj K hK (fun i => a.map (j i))
      (isColimitCofanMkObjOfIsColimit a A j hc))
  have := adj.unit.naturality (j i)
  dsimp at this ⊢
  rw [← cancel_epi (adj.unit.app (A i)), IsIso.hom_inv_id_assoc, ← reassoc_of% this,
    IsIso.hom_inv_id, comp_id]

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]
  {TV : Type u₃} [Category.{v₃} TV] [Preadditive TV] [HasZeroObject TV] [HasShift TV ℤ]
  [∀ n : ℤ, (shiftFunctor TV n).Additive] [Pretriangulated TV] [HasShift TU ℤ]
  {aU : T ⥤ TU} {aV : T ⥤ TV} {RU : TU ⥤ T} {RV : TV ⥤ T}

/-- **Compactness is local for two localizations.** Let `a_U ⊣ R_U` and `a_V ⊣ R_V` be
adjunctions of additive functors with invertible counits, with `a_V` exact, `R_U` commuting with
the shift, both `R`'s commuting with direct sums indexed by `Type w`, and suppose that every
object killed by `a_V` lies in the essential image of `R_U`, i.e. the unit of `a_U ⊣ R_U` is
invertible there. Then an object `K` of `T` whose images `a_U K` and `a_V K` are compact is
compact.

Every object `E` sits in the triangle `E ⟶ R_V a_V E ⟶ N ⟶ E⟦1⟧` of the unit, with `a_V N = 0`;
the compactness map of `K` is bijective against direct sums of objects of the shape `R_V a_V E`
and against direct sums of shifts of objects like `N`, by
`CategoryTheory.Pretriangulated.bijective_cofanMap_of_isIso_unit`; and a direct sum of
distinguished triangles is distinguished, so the four lemma
`CategoryTheory.surjective_cofanMap_of_triangleHom` concludes. -/
theorem isCompactObject_of_isCompactObject_restrict [HasCoproducts.{w} T]
    (adjU : aU ⊣ RU) (adjV : aV ⊣ RV) [aU.Additive] [aV.Additive] [RU.Additive] [RV.Additive]
    [aV.CommShift ℤ] [aV.IsTriangulated] [RU.CommShift ℤ]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) RU]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) RV]
    [IsIso adjU.counit] [IsIso adjV.counit]
    (hker : ∀ N : T, IsZero (aV.obj N) → IsIso (adjU.unit.app N))
    (K : T) (hU : IsCompactObject.{w} (aU.obj K)) (hV : IsCompactObject.{w} (aV.obj K)) :
    IsCompactObject.{w} K := by
  constructor
  intro I _ E _
  change Function.Bijective (cofanMap K (Limits.Sigma.ι E))
  refine ⟨injective_cofanMap K _ (coproductIsCoproduct E), ?_⟩
  choose N g h hT using fun i => distinguished_cocone_triangle (adjV.unit.app (E i))
  let Tt : I → Triangle T := fun i => Triangle.mk (adjV.unit.app (E i)) (g i) (h i)
  let φ : ∀ i, Tt i ⟶ coproductTriangle Tt := fun i =>
    { hom₁ := Limits.Sigma.ι (fun i => (Tt i).obj₁) i
      hom₂ := Limits.Sigma.ι (fun i => (Tt i).obj₂) i
      hom₃ := Limits.Sigma.ι (fun i => (Tt i).obj₃) i
      comm₁ := by simp [coproductTriangle]
      comm₂ := by simp [coproductTriangle]
      comm₃ := by simp [coproductTriangle] }
  have hNzero : ∀ i, IsZero (aV.obj (N i)) := fun i =>
    Triangle.isZero₃_of_isIso₁ _ (aV.map_distinguished _ (hT i)) (isIso_map_unit_app adjV _)
  have hNU : ∀ i, IsIso (adjU.unit.app (N i)) := fun i => hker _ (hNzero i)
  have hsumN : IsIso (adjU.unit.app (∐ N)) :=
    isIso_unit_app_of_isColimit adjU _ (coproductIsCoproduct N) hNU
  refine surjective_cofanMap_of_triangleHom K Tt (coproductTriangle Tt) φ hT
    (coproductTriangle_distinguished Tt hT) ?_ (injective_cofanMap K _ (coproductIsCoproduct _)) ?_
  · exact (bijective_cofanMap_of_isIso_unit adjV K hV _ (coproductIsCoproduct _)
      (fun i => isIso_unit_app_obj adjV _) (isIso_unit_app_of_isColimit adjV _
        (coproductIsCoproduct _) fun i => isIso_unit_app_obj adjV _)).2
  · have hc : IsColimit (Cofan.mk ((∐ N)⟦(-1 : ℤ)⟧)
        fun i => (Limits.Sigma.ι N i)⟦(-1 : ℤ)⟧') :=
      isColimitCofanMkObjOfIsColimit (shiftFunctor T (-1 : ℤ)) N _ (coproductIsCoproduct N)
    exact (bijective_cofanMap_of_isIso_unit adjU K hU _ hc
      (fun i => isIso_unit_app_shift adjU (hNU i) _) (isIso_unit_app_shift adjU hsumN _)).2

end Compact

end CategoryTheory.Pretriangulated
