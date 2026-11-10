module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PairingFiveLemma

/-!
# The five lemma for pushed-forward pairings, at every shift

Let `T : C₁ ⥤ C₂ ⥤ C` and `T' : D ⥤ D ⥤ D` be bifunctors, written `K ⊗ L`, and `R : C ⥤ D` a
functor. The proof of [Stacks, Tag 0G8K] pairs complexes `K` and `L` upstairs by a pairing
`β : K ⊗ L ⟶ M` and then pushes the pairing down: with a natural "cup product"
`μ : R₁K ⊗ R₂L ⟶ R(K ⊗ L)` and a trace `τ : RM ⟶ N` it considers

`μ ≫ R(β) ≫ τ : R₁K ⊗ R₂L ⟶ N`.

There `C₁ = C₂ = C` is the derived category of `(X, f⁻¹𝒪_S)`, `R₁ = R₂ = R` is `Rf_*`, `μ` is the
relative cup product and `τ` the trace. Perfectness of such pairings is proved by the five lemma
([Stacks, Tag 014A]) along two distinguished triangles upstairs. The five lemma also involves the
pairings of the shifted vertices `K₃[-1] ⊗ L₃[1]` and `K₁[1] ⊗ L₁[-1]`; these are shifts of the
given pairings upstairs, and their perfectness downstairs would follow from that of the given ones
if `μ` commuted with the shifts. Instead of proving that, this file carries the whole family of
shifted pushings along: a `PairingPushData` is a choice of `R₁`, `R₂` and `μ` with the exactness
properties the five lemma needs, `PairingPushData.shift` precomposes `R₁` and `R₂` with shifts,
and a pairing is called *perfect at every shift* (`PairingPushData.AllPerf`) when its pushings
along all the data reachable by shifting are perfect. The five lemma then propagates that
property, with no compatibility of `μ` with the shifts needed at all
(`PairingPushData.allPerf_of_triangles`).

## Main definitions

* `CategoryTheory.Functor.PairingPushData`: functors `R₁`, `R₂` and a natural `μ`, with the
  exactness of `Hom(Z, R₁ -)` and of `Hom(Z ⊗ R₂ -, N)` along distinguished triangles.
* `CategoryTheory.Functor.PairingPushData.ofIsTriangulated`: the data of triangulated functors.
* `CategoryTheory.Functor.PairingPushData.shift`: the data precomposed with shifts.
* `CategoryTheory.Functor.PairingPushData.pushedPairing`: the pairing `μ ≫ R(β) ≫ τ`.
* `CategoryTheory.Functor.PairingPushData.AllPerf`: perfectness at every reachable shift.

## Main results

* `CategoryTheory.Functor.PairingPushData.bijective_pairingPrecomp_of_triangles`: the five lemma
  for pushed pairings.
* `CategoryTheory.Functor.PairingPushData.allPerf_of_triangles`: the five lemma for pairings
  perfect at every shift.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

section ShiftedPairingId

variable {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] (T : C₁ ⥤ C₂ ⥤ C) [T.CommShift₂Int]

/-- The shift of a pairing is the given pairing preceded by the shift of the identity pairing. -/
theorem shiftedPairing_eq_comp {K : C₁} {L : C₂} {M : C} (φ : (T.obj K).obj L ⟶ M) (n m : ℤ)
    (h : n + m = 0) :
    T.shiftedPairing φ n m h = T.shiftedPairing (𝟙 _) n m h ≫ φ := by
  simp [shiftedPairing]

/-- The shift of the identity pairing is natural in the first variable. -/
theorem shiftedPairing_id_natural_left {K K' : C₁} (e : K ⟶ K') (L : C₂) (n m : ℤ)
    (h : n + m = 0) :
    (T.map (e⟦n⟧')).app (L⟦m⟧) ≫ T.shiftedPairing (𝟙 ((T.obj K').obj L)) n m h =
      T.shiftedPairing (𝟙 ((T.obj K).obj L)) n m h ≫ (T.map e).app L := by
  have h₁ := NatTrans.shift_app_comm (T.map (e⟦n⟧')) m L
  have h₂ := ((T.flip.obj L).commShiftIso n).hom.naturality e
  have h₃ := (shiftFunctorCompIsoId C n m h).hom.naturality ((T.map e).app L)
  simp only [Functor.comp_obj, Functor.flip_obj_obj, Functor.comp_map, Functor.flip_obj_map,
    Functor.id_obj, Functor.id_map] at h₁ h₂ h₃
  simp only [shiftedPairing]
  rw [← reassoc_of% h₁, ← Functor.map_comp_assoc, h₂, Functor.map_comp_assoc]
  simp only [Functor.id_obj, Category.comp_id, Category.assoc] at h₃ ⊢
  rw [h₃]

/-- The shift of the identity pairing is natural in the second variable. -/
theorem shiftedPairing_id_natural_right (K : C₁) {L L' : C₂} (e : L ⟶ L') (n m : ℤ)
    (h : n + m = 0) :
    (T.obj (K⟦n⟧)).map (e⟦m⟧') ≫ T.shiftedPairing (𝟙 ((T.obj K).obj L')) n m h =
      T.shiftedPairing (𝟙 ((T.obj K).obj L)) n m h ≫ (T.obj K).map e := by
  have h₁ := ((T.obj (K⟦n⟧)).commShiftIso m).hom.naturality e
  have h₂ := NatTrans.shift_app_comm (T.flip.map e) n K
  have h₃ := (shiftFunctorCompIsoId C n m h).hom.naturality ((T.obj K).map e)
  simp only [Functor.comp_obj, Functor.flip_obj_obj, Functor.comp_map, Functor.flip_map_app,
    Functor.id_obj, Functor.id_map] at h₁ h₂ h₃
  simp only [shiftedPairing]
  rw [reassoc_of% h₁, ← Functor.map_comp_assoc, ← h₂, Functor.map_comp_assoc]
  simp only [Functor.id_obj, Category.comp_id, Category.assoc] at h₃ ⊢
  rw [h₃]

end ShiftedPairingId

section Data

variable {C₁ C₂ C D : Type*} [Category* C₁] [Category* C₂] [Category* C] [Category* D]
  [HasZeroObject C₁] [HasZeroObject C₂] [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂]
  (T : C₁ ⥤ C₂ ⥤ C) (T' : D ⥤ D ⥤ D) (R : C ⥤ D)

/-- **Data for pushing pairings down along `R`**: additive functors `R₁ : C₁ ⥤ D` and
`R₂ : C₂ ⥤ D` and a natural "cup product" `μ : R₁K ⊗ R₂L ⟶ R(K ⊗ L)`, such that `Hom(Z, R₁ -)`
is exact at the second and third vertices of every distinguished triangle and `Hom(Z ⊗ R₂ -, N)`
at the second and third vertices of every distinguished triangle. These are the properties the
five lemma uses; triangulated functors have them (`PairingPushData.ofIsTriangulated`). -/
structure PairingPushData where
  /-- The functor applied to the first variable. -/
  R₁ : C₁ ⥤ D
  /-- The functor applied to the second variable. -/
  R₂ : C₂ ⥤ D
  /-- The functor `R₁` is additive. -/
  additive₁ : R₁.Additive := by infer_instance
  /-- The functor `R₂` is additive. -/
  additive₂ : R₂.Additive := by infer_instance
  /-- The cup product `R₁K ⊗ R₂L ⟶ R(K ⊗ L)`. -/
  μ (K : C₁) (L : C₂) : (T'.obj (R₁.obj K)).obj (R₂.obj L) ⟶ R.obj ((T.obj K).obj L)
  μ_natural_left {K K' : C₁} (e : K ⟶ K') (L : C₂) :
    (T'.map (R₁.map e)).app (R₂.obj L) ≫ μ K' L = μ K L ≫ R.map ((T.map e).app L)
  μ_natural_right (K : C₁) {L L' : C₂} (e : L ⟶ L') :
    (T'.obj (R₁.obj K)).map (R₂.map e) ≫ μ K L' = μ K L ≫ R.map ((T.obj K).map e)
  exact₁₂ (S : Triangle C₁) (hS : S ∈ distTriang C₁) {Z : D} (v : Z ⟶ R₁.obj S.obj₂)
    (hv : v ≫ R₁.map S.mor₂ = 0) : ∃ u : Z ⟶ R₁.obj S.obj₁, v = u ≫ R₁.map S.mor₁
  exact₁₃ (S : Triangle C₁) (hS : S ∈ distTriang C₁) {Z : D} (v : Z ⟶ R₁.obj S.obj₃)
    (hv : v ≫ R₁.map S.mor₃ = 0) : ∃ u : Z ⟶ R₁.obj S.obj₂, v = u ≫ R₁.map S.mor₂
  exact₂₂ (S : Triangle C₂) (hS : S ∈ distTriang C₂) (Z : D) {N : D}
    (g : (T'.obj Z).obj (R₂.obj S.obj₂) ⟶ N) (hg : (T'.obj Z).map (R₂.map S.mor₁) ≫ g = 0) :
    ∃ h : (T'.obj Z).obj (R₂.obj S.obj₃) ⟶ N, g = (T'.obj Z).map (R₂.map S.mor₂) ≫ h
  exact₂₃ (S : Triangle C₂) (hS : S ∈ distTriang C₂) (Z : D) {N : D}
    (g : (T'.obj Z).obj (R₂.obj S.obj₃) ⟶ N) (hg : (T'.obj Z).map (R₂.map S.mor₂) ≫ g = 0) :
    ∃ h : (T'.obj Z).obj (R₂.obj (S.obj₁⟦(1 : ℤ)⟧)) ⟶ N, g = (T'.obj Z).map (R₂.map S.mor₃) ≫ h

namespace PairingPushData

attribute [instance] additive₁ additive₂
attribute [reassoc] μ_natural_left μ_natural_right

variable {T T' R}

section OfIsTriangulated

variable [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- **The push data of triangulated functors.** For triangulated `R₁`, `R₂` and a bifunctor `T'`
triangulated in its second variable, the exactness properties of a `PairingPushData` are the
long exact sequences of `Hom(Z, -)` and `Hom(-, N)` along distinguished triangles. -/
@[simps R₁ R₂ μ]
def ofIsTriangulated (R₁ : C₁ ⥤ D) (R₂ : C₂ ⥤ D) [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    [R₁.IsTriangulated] [R₂.IsTriangulated] [∀ Z, (T'.obj Z).CommShift ℤ]
    [∀ Z, (T'.obj Z).IsTriangulated]
    (μ : ∀ (K : C₁) (L : C₂), (T'.obj (R₁.obj K)).obj (R₂.obj L) ⟶ R.obj ((T.obj K).obj L))
    (hl : ∀ {K K' : C₁} (e : K ⟶ K') (L : C₂),
      (T'.map (R₁.map e)).app (R₂.obj L) ≫ μ K' L = μ K L ≫ R.map ((T.map e).app L))
    (hr : ∀ (K : C₁) {L L' : C₂} (e : L ⟶ L'),
      (T'.obj (R₁.obj K)).map (R₂.map e) ≫ μ K L' = μ K L ≫ R.map ((T.obj K).map e)) :
    PairingPushData T T' R where
  R₁ := R₁
  R₂ := R₂
  μ := μ
  μ_natural_left := hl
  μ_natural_right := hr
  exact₁₂ S hS _ v hv := Triangle.coyoneda_exact₂ _ (R₁.map_distinguished S hS) v hv
  exact₁₃ S hS _ v hv := Triangle.coyoneda_exact₃ _ (R₁.map_distinguished S hS) v
    (by rw [reassoc_of% hv, zero_comp] :
      v ≫ R₁.map S.mor₃ ≫ (R₁.commShiftIso (1 : ℤ)).hom.app S.obj₁ = 0)
  exact₂₂ S hS Z _ g hg := Triangle.yoneda_exact₂ _
    ((T'.obj Z).map_distinguished _ (R₂.map_distinguished S hS)) g hg
  exact₂₃ S hS Z N g hg := by
    obtain ⟨h, hh⟩ : ∃ h : ((T'.obj Z).obj (R₂.obj S.obj₁))⟦(1 : ℤ)⟧ ⟶ N,
        g = ((T'.obj Z).map (R₂.map S.mor₃ ≫ (R₂.commShiftIso (1 : ℤ)).hom.app S.obj₁) ≫
          ((T'.obj Z).commShiftIso (1 : ℤ)).hom.app (R₂.obj S.obj₁)) ≫ h :=
      Triangle.yoneda_exact₃ _ ((T'.obj Z).map_distinguished _ (R₂.map_distinguished S hS)) g hg
    refine ⟨(T'.obj Z).map ((R₂.commShiftIso (1 : ℤ)).hom.app S.obj₁) ≫
      ((T'.obj Z).commShiftIso (1 : ℤ)).hom.app _ ≫ h, ?_⟩
    rw [hh]
    simp only [Functor.map_comp, Category.assoc]

end OfIsTriangulated

/-- An additive functor carries a sign `ε • f`, `ε` a unit of `ℤ`, to `ε • F f`. -/
theorem map_units_smul {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] {X Y : A} (ε : ℤˣ) (f : X ⟶ Y) : F.map (ε • f) = ε • F.map f := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

section Shift

variable [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive]

/-- **The push data precomposed with shifts**: `R₁` is replaced by `K ↦ R₁(K[a])`, `R₂` by
`L ↦ R₂(L[b])`, for `a + b = 0`, and the cup product by
`R₁(K[a]) ⊗ R₂(L[b]) ⟶ R(K[a] ⊗ L[b]) ⟶ R(K ⊗ L)`, the second map being `R` of the shift of the
identity pairing. Pushing a pairing along it is pushing its shift along the given data
(`PairingPushData.pushedPairing_shift`). -/
@[simps R₁ R₂ μ]
noncomputable def shift (P : PairingPushData T T' R) (a b : ℤ) (h : a + b = 0) :
    PairingPushData T T' R where
  R₁ := shiftFunctor C₁ a ⋙ P.R₁
  R₂ := shiftFunctor C₂ b ⋙ P.R₂
  μ K L := P.μ (K⟦a⟧) (L⟦b⟧) ≫ R.map (T.shiftedPairing (𝟙 _) a b h)
  μ_natural_left e L := by
    simp only [Functor.comp_map, Functor.comp_obj, Category.assoc]
    rw [P.μ_natural_left_assoc, ← R.map_comp, ← R.map_comp, shiftedPairing_id_natural_left]
  μ_natural_right K _ _ e := by
    simp only [Functor.comp_map, Functor.comp_obj, Category.assoc]
    rw [P.μ_natural_right_assoc, ← R.map_comp, ← R.map_comp, shiftedPairing_id_natural_right]
  exact₁₂ S hS Z v hv := by
    have hS' : (Triangle.shiftFunctor C₁ a).obj S ∈ distTriang C₁ :=
      Triangle.shift_distinguished S hS a
    obtain ⟨u, hu⟩ : ∃ u : Z ⟶ P.R₁.obj (S.obj₁⟦a⟧),
        v = u ≫ P.R₁.map (a.negOnePow • S.mor₁⟦a⟧') := P.exact₁₂ _ hS' v (by
      change v ≫ P.R₁.map (a.negOnePow • S.mor₂⟦a⟧') = 0
      change v ≫ P.R₁.map (S.mor₂⟦a⟧') = 0 at hv
      rw [map_units_smul, Linear.comp_units_smul, hv, smul_zero])
    refine ⟨a.negOnePow • u, ?_⟩
    rw [hu, map_units_smul, Linear.comp_units_smul, Linear.units_smul_comp]
    rfl
  exact₁₃ S hS Z v hv := by
    have hS' : (Triangle.shiftFunctor C₁ a).obj S ∈ distTriang C₁ :=
      Triangle.shift_distinguished S hS a
    obtain ⟨u, hu⟩ : ∃ u : Z ⟶ P.R₁.obj (S.obj₂⟦a⟧),
        v = u ≫ P.R₁.map (a.negOnePow • S.mor₂⟦a⟧') := P.exact₁₃ _ hS' v (by
      change v ≫ P.R₁.map (a.negOnePow • (S.mor₃⟦a⟧' ≫
        (shiftFunctorComm C₁ 1 a).hom.app S.obj₁)) = 0
      change v ≫ P.R₁.map (S.mor₃⟦a⟧') = 0 at hv
      rw [map_units_smul, Linear.comp_units_smul, Functor.map_comp, reassoc_of% hv, zero_comp,
        smul_zero])
    refine ⟨a.negOnePow • u, ?_⟩
    rw [hu, map_units_smul, Linear.comp_units_smul, Linear.units_smul_comp]
    rfl
  exact₂₂ S hS Z N g hg := by
    have hS' : (Triangle.shiftFunctor C₂ b).obj S ∈ distTriang C₂ :=
      Triangle.shift_distinguished S hS b
    obtain ⟨k, hk⟩ : ∃ k : (T'.obj Z).obj (P.R₂.obj (S.obj₃⟦b⟧)) ⟶ N,
        g = (T'.obj Z).map (P.R₂.map (b.negOnePow • S.mor₂⟦b⟧')) ≫ k := P.exact₂₂ _ hS' Z g (by
      change (T'.obj Z).map (P.R₂.map (b.negOnePow • S.mor₁⟦b⟧')) ≫ g = 0
      change (T'.obj Z).map (P.R₂.map (S.mor₁⟦b⟧')) ≫ g = 0 at hg
      rw [map_units_smul, map_units_smul, Linear.units_smul_comp, hg, smul_zero])
    refine ⟨b.negOnePow • k, ?_⟩
    rw [hk, map_units_smul, map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
    rfl
  exact₂₃ S hS Z N g hg := by
    have hS' : (Triangle.shiftFunctor C₂ b).obj S ∈ distTriang C₂ :=
      Triangle.shift_distinguished S hS b
    obtain ⟨k, hk⟩ : ∃ k : (T'.obj Z).obj (P.R₂.obj ((S.obj₁⟦b⟧)⟦(1 : ℤ)⟧)) ⟶ N,
        g = (T'.obj Z).map (P.R₂.map (b.negOnePow • (S.mor₃⟦b⟧' ≫
          (shiftFunctorComm C₂ 1 b).hom.app S.obj₁))) ≫ k := P.exact₂₃ _ hS' Z g (by
      change (T'.obj Z).map (P.R₂.map (b.negOnePow • S.mor₂⟦b⟧')) ≫ g = 0
      change (T'.obj Z).map (P.R₂.map (S.mor₂⟦b⟧')) ≫ g = 0 at hg
      rw [map_units_smul, map_units_smul, Linear.units_smul_comp, hg, smul_zero])
    refine ⟨b.negOnePow • ((T'.obj Z).map
      (P.R₂.map ((shiftFunctorComm C₂ 1 b).hom.app S.obj₁)) ≫ k), ?_⟩
    rw [hk, map_units_smul, map_units_smul, Functor.map_comp, Functor.map_comp,
      Linear.units_smul_comp, Category.assoc, Linear.comp_units_smul]
    rfl

end Shift

section Pushed

/-- **The pushed pairing** `μ ≫ R(β) ≫ τ : R₁K ⊗ R₂L ⟶ N` of a pairing `β : K ⊗ L ⟶ M`, for a
trace `τ : RM ⟶ N`. -/
def pushedPairing (P : PairingPushData T T' R) {K : C₁} {L : C₂} {M : C} {N : D}
    (τ : R.obj M ⟶ N) (β : (T.obj K).obj L ⟶ M) :
    (T'.obj (P.R₁.obj K)).obj (P.R₂.obj L) ⟶ N :=
  P.μ K L ≫ R.map β ≫ τ

/-- Compatible pairings upstairs push down to compatible pairings. -/
theorem pairingCompatible_pushedPairing (P : PairingPushData T T' R) {K K' : C₁} {L L' : C₂}
    {M : C} {N : D} (τ : R.obj M ⟶ N) {β : (T.obj K).obj L ⟶ M} {β' : (T.obj K').obj L' ⟶ M}
    {e : K ⟶ K'} {e' : L' ⟶ L} (hc : T.PairingCompatible β β' e e') :
    T'.PairingCompatible (P.pushedPairing τ β) (P.pushedPairing τ β') (P.R₁.map e)
      (P.R₂.map e') := by
  have hc' : (T.map e).app L' ≫ β' = (T.obj K).map e' ≫ β := hc
  simp only [PairingCompatible, pushedPairing]
  rw [P.μ_natural_left_assoc, P.μ_natural_right_assoc, ← R.map_comp_assoc, hc',
    R.map_comp_assoc]

variable [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive]

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive] in
/-- Pushing the negative of a pairing gives the negative of the pushed pairing. -/
theorem pushedPairing_neg [R.Additive] (P : PairingPushData T T' R) {K : C₁} {L : C₂} {M : C}
    {N : D} (τ : R.obj M ⟶ N) (β : (T.obj K).obj L ⟶ M) :
    P.pushedPairing τ (-β) = -P.pushedPairing τ β := by
  simp [pushedPairing]

/-- Pushing a pairing along the shifted data is pushing its shift along the given data. -/
theorem pushedPairing_shift (P : PairingPushData T T' R) (a b : ℤ) (h : a + b = 0) {K : C₁}
    {L : C₂} {M : C} {N : D} (τ : R.obj M ⟶ N) (β : (T.obj K).obj L ⟶ M) :
    (P.shift a b h).pushedPairing τ β = P.pushedPairing τ (T.shiftedPairing β a b h) := by
  change (P.μ (K⟦a⟧) (L⟦b⟧) ≫ R.map (T.shiftedPairing (𝟙 _) a b h)) ≫ R.map β ≫ τ =
    P.μ (K⟦a⟧) (L⟦b⟧) ≫ R.map (T.shiftedPairing β a b h) ≫ τ
  rw [Category.assoc, shiftedPairing_eq_comp T β a b h, R.map_comp, Category.assoc]

end Pushed

section Five

/-- The images of the first two maps of the inverse rotation of a distinguished triangle
compose to zero. -/
private theorem map_invRotate_comp_eq_zero {A B : Type*} [Category* A] [Category* B]
    [HasZeroObject A] [Preadditive A] [Preadditive B] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A] (F : A ⥤ B) [F.Additive]
    {S : Triangle A} (hS : S ∈ distTriang A) :
    F.map S.invRotate.mor₁ ≫ F.map S.invRotate.mor₂ = 0 := by
  rw [← F.map_comp, comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang _ hS), F.map_zero]

variable [∀ L : D, (T'.flip.obj L).Additive] [∀ Z : D, (T'.obj Z).Additive]

/-- **The five lemma for pushed pairings** ([Stacks, Tag 014A], as used in the proof of
[Stacks, Tag 0G8K]). Let `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` and `L₃ ⟶ L₂ ⟶ L₁ ⟶ L₃[1]` be distinguished
triangles upstairs and `βᵢ : Kᵢ ⊗ Lᵢ ⟶ M` pairings compatible along their maps, the connecting
maps being paired through pairings `β₀ : K₃[-1] ⊗ L₃[1] ⟶ M` and `β₄ : K₁[1] ⊗ L₁[-1] ⟶ M`. If at
`Z` the pushed pairings of `β₁` and `β₃` are perfect, that of `β₀` surjective and that of `β₄`
injective, then the pushed pairing of `β₂` is perfect at `Z`. -/
theorem bijective_pairingPrecomp_of_triangles (P : PairingPushData T T' R) {M : C} {N : D}
    (τ : R.obj M ⟶ N) (S : Triangle C₁) (hS : S ∈ distTriang C₁) (S' : Triangle C₂)
    (hS' : S' ∈ distTriang C₂)
    {β₀ : (T.obj (S.obj₃⟦(-1 : ℤ)⟧)).obj (S'.obj₁⟦(1 : ℤ)⟧) ⟶ M}
    {β₁ : (T.obj S.obj₁).obj S'.obj₃ ⟶ M} {β₂ : (T.obj S.obj₂).obj S'.obj₂ ⟶ M}
    {β₃ : (T.obj S.obj₃).obj S'.obj₁ ⟶ M}
    {β₄ : (T.obj (S.obj₁⟦(1 : ℤ)⟧)).obj (S'.obj₃⟦(-1 : ℤ)⟧) ⟶ M}
    (c₀ : T.PairingCompatible β₀ β₁ S.invRotate.mor₁ S'.mor₃)
    (c₁ : T.PairingCompatible β₁ β₂ S.mor₁ S'.mor₂)
    (c₂ : T.PairingCompatible β₂ β₃ S.mor₂ S'.mor₁)
    (c₃ : T.PairingCompatible β₃ β₄ S.mor₃ S'.invRotate.mor₁) (Z : D)
    (b₀ : Function.Surjective (T'.pairingPrecomp (P.pushedPairing τ β₀) Z))
    (b₁ : Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β₁) Z))
    (b₃ : Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β₃) Z))
    (b₄ : Function.Injective (T'.pairingPrecomp (P.pushedPairing τ β₄) Z)) :
    Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β₂) Z) :=
  bijective_pairingPrecomp_of_five (P.pairingCompatible_pushedPairing τ c₀)
    (P.pairingCompatible_pushedPairing τ c₁) (P.pairingCompatible_pushedPairing τ c₂)
    (P.pairingCompatible_pushedPairing τ c₃)
    (map_invRotate_comp_eq_zero P.R₁ hS)
    (map_invRotate_comp_eq_zero P.R₂ hS') Z
    (fun v hv => P.exact₁₂ S hS v hv) (fun v hv => P.exact₁₃ S hS v hv)
    (fun g hg => P.exact₂₃ S' hS' Z g hg) (fun g hg => P.exact₂₂ S' hS' Z g hg) b₀ b₁ b₃ b₄

end Five

section AllPerf

variable [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive]

/-- The pushed pairing of `β` is perfect: the map `v ↦ (v ⊗ 1) ≫ μ ≫ R(β) ≫ τ` out of
`Hom(Z, R₁K)` is bijective for every `Z`. -/
def Perf (P : PairingPushData T T' R) {K : C₁} {L : C₂} {M : C} {N : D} (τ : R.obj M ⟶ N)
    (β : (T.obj K).obj L ⟶ M) : Prop :=
  ∀ Z : D, Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β) Z)

/-- The push data reachable from `P₀` by finitely many shifts. -/
inductive Reachable (P₀ : PairingPushData T T' R) : PairingPushData T T' R → Prop
  | refl : Reachable P₀ P₀
  | shift {P : PairingPushData T T' R} (a b : ℤ) (h : a + b = 0) :
      Reachable P₀ P → Reachable P₀ (P.shift a b h)

/-- **The pushed pairings of `β` are perfect at every shift**: along every push datum reachable
from `P₀` by shifts. -/
def AllPerf (P₀ : PairingPushData T T' R) {K : C₁} {L : C₂} {M : C} {N : D} (τ : R.obj M ⟶ N)
    (β : (T.obj K).obj L ⟶ M) : Prop :=
  ∀ P, P₀.Reachable P → P.Perf τ β

/-- If the pushed pairings of `β` are perfect at every shift, the pushed pairing of `β` along
`P₀` itself is perfect. -/
theorem AllPerf.perf {P₀ : PairingPushData T T' R} {K : C₁} {L : C₂} {M : C} {N : D}
    {τ : R.obj M ⟶ N} {β : (T.obj K).obj L ⟶ M} (h : P₀.AllPerf τ β) : P₀.Perf τ β :=
  h P₀ .refl

/-- Perfectness of the shift of a pairing along `P` is perfectness of the pairing along the
shifted data. -/
theorem perf_shiftedPairing_iff (P : PairingPushData T T' R) (a b : ℤ) (h : a + b = 0) {K : C₁}
    {L : C₂} {M : C} {N : D} (τ : R.obj M ⟶ N) (β : (T.obj K).obj L ⟶ M) :
    P.Perf τ (T.shiftedPairing β a b h) ↔ (P.shift a b h).Perf τ β := by
  simp only [Perf, pushedPairing_shift]
  exact Iff.rfl

/-- A pairing perfect at every shift has shifts perfect at every shift. -/
theorem AllPerf.shiftedPairing {P₀ : PairingPushData T T' R} {K : C₁} {L : C₂} {M : C} {N : D}
    {τ : R.obj M ⟶ N} {β : (T.obj K).obj L ⟶ M} (hβ : P₀.AllPerf τ β) (a b : ℤ)
    (h : a + b = 0) : P₀.AllPerf τ (T.shiftedPairing β a b h) := fun P hP =>
  (P.perf_shiftedPairing_iff a b h τ β).2 (hβ _ (.shift a b h hP))

/-- A pairing is perfect at every shift exactly when its negative is. -/
theorem allPerf_neg_iff [R.Additive] (P₀ : PairingPushData T T' R) {K : C₁} {L : C₂} {M : C}
    {N : D} (τ : R.obj M ⟶ N) (β : (T.obj K).obj L ⟶ M) :
    P₀.AllPerf τ (-β) ↔ P₀.AllPerf τ β := by
  simp only [AllPerf, Perf, pushedPairing_neg, bijective_pairingPrecomp_neg_iff]

variable [∀ L : D, (T'.flip.obj L).Additive]

/-- **The five lemma for pairings perfect at every shift** ([Stacks, Tag 014A], as used in the
proof of [Stacks, Tag 0G8K]). Let `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` and `L₃ ⟶ L₂ ⟶ L₁ ⟶ L₃[1]` be
distinguished triangles upstairs and `βᵢ : Kᵢ ⊗ Lᵢ ⟶ M` pairings compatible along all the maps of
the two triangles, the connecting maps being paired through the shifts of the outer pairings. If
the pushed pairings of `β₁` and `β₃` are perfect at every shift, then so are those of `β₂`. -/
theorem allPerf_of_triangles (P₀ : PairingPushData T T' R) {M : C} {N : D} (τ : R.obj M ⟶ N)
    (S : Triangle C₁) (hS : S ∈ distTriang C₁) (S' : Triangle C₂) (hS' : S' ∈ distTriang C₂)
    {β₁ : (T.obj S.obj₁).obj S'.obj₃ ⟶ M} {β₂ : (T.obj S.obj₂).obj S'.obj₂ ⟶ M}
    {β₃ : (T.obj S.obj₃).obj S'.obj₁ ⟶ M}
    (c₀ : T.PairingCompatible (T.shiftedPairing β₃ (-1) 1 (by omega)) β₁ S.invRotate.mor₁
      S'.mor₃)
    (c₁ : T.PairingCompatible β₁ β₂ S.mor₁ S'.mor₂)
    (c₂ : T.PairingCompatible β₂ β₃ S.mor₂ S'.mor₁)
    (c₃ : T.PairingCompatible β₃ (T.shiftedPairing β₁ 1 (-1) (by omega)) S.mor₃
      S'.invRotate.mor₁)
    (h₁ : P₀.AllPerf τ β₁) (h₃ : P₀.AllPerf τ β₃) : P₀.AllPerf τ β₂ := fun P hP Z =>
  P.bijective_pairingPrecomp_of_triangles τ S hS S' hS' c₀ c₁ c₂ c₃ Z
    ((h₃.shiftedPairing (-1) 1 (by omega)) P hP Z).2 (h₁ P hP Z) (h₃ P hP Z)
    ((h₁.shiftedPairing 1 (-1) (by omega)) P hP Z).1

/-- **The five lemma for pairings perfect at every shift, with a sign at the first connecting
map**: as `allPerf_of_triangles`, the first connecting maps being paired through minus the shift
of the third pairing. -/
theorem allPerf_of_triangles_neg [R.Additive] (P₀ : PairingPushData T T' R) {M : C} {N : D}
    (τ : R.obj M ⟶ N) (S : Triangle C₁) (hS : S ∈ distTriang C₁) (S' : Triangle C₂)
    (hS' : S' ∈ distTriang C₂)
    {β₁ : (T.obj S.obj₁).obj S'.obj₃ ⟶ M} {β₂ : (T.obj S.obj₂).obj S'.obj₂ ⟶ M}
    {β₃ : (T.obj S.obj₃).obj S'.obj₁ ⟶ M}
    (c₀ : T.PairingCompatible (-T.shiftedPairing β₃ (-1) 1 (by omega)) β₁ S.invRotate.mor₁
      S'.mor₃)
    (c₁ : T.PairingCompatible β₁ β₂ S.mor₁ S'.mor₂)
    (c₂ : T.PairingCompatible β₂ β₃ S.mor₂ S'.mor₁)
    (c₃ : T.PairingCompatible β₃ (T.shiftedPairing β₁ 1 (-1) (by omega)) S.mor₃
      S'.invRotate.mor₁)
    (h₁ : P₀.AllPerf τ β₁) (h₃ : P₀.AllPerf τ β₃) : P₀.AllPerf τ β₂ := fun P hP Z =>
  P.bijective_pairingPrecomp_of_triangles τ S hS S' hS' c₀ c₁ c₂ c₃ Z
    (((P₀.allPerf_neg_iff τ _).2 (h₃.shiftedPairing (-1) 1 (by omega))) P hP Z).2 (h₁ P hP Z)
    (h₃ P hP Z) ((h₁.shiftedPairing 1 (-1) (by omega)) P hP Z).1

end AllPerf

end PairingPushData

end Data

end CategoryTheory.Functor
