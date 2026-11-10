module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit

/-!
# Units of adjunctions between derived categories, detected on cohomology objects

Let `F : D(A) ⥤ D(B)` and `G : D(B) ⥤ D(A)` be triangulated functors between derived
categories of abelian categories with `F ⊣ G`, let `F` be t-exact and let `P` be a property of
objects of `A`. Suppose the unit `η : 𝟭 ⟶ F ⋙ G` is an isomorphism at `G[n]` for every `G`
satisfying `P` and every `n`. Then `η` is an isomorphism at every bounded below object all of
whose cohomology objects satisfy `P`; and, granted that the objects with such cohomology (and
their images under `F`) are derived limits of their towers of truncations `τ_{≥ -n}`, at every
such object at all.

This is the formal part of the argument of Stacks 0DGR: there `F = Lε_X^*`, `G = Rε_{X,*}` and
the cohomology objects are those of `Lπ_X^*K` for `K` in `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_unit_app_of_isGE_of_isLE`: the bounded
  case, by induction on the length of the cohomological interval.
* `Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_unit_app_of_isGE`: the bounded below
  case.
* `Stacks.DerivedCategory.AdjunctionUnitTruncations.isGE_obj_of_isLE_obj`: a right adjoint of a
  functor preserving `D^{≤ n}` preserves `D^{≥ n}`.

## Implementation notes

Only the long exact cohomology sequences of the truncation triangles are used, together with
the naturality of `η`; the compatibility of `η` with the shift is never needed. In each
truncation triangle `τ_{≤ n} X ⟶ X ⟶ τ_{≥ n+1} X` one of the two outer terms has vanishing
cohomology in the two degrees around the degree under consideration, so the relevant map on
cohomology is an isomorphism both for the triangle and for its image under `F ⋙ G`, and `H^q(η)`
is compared with `H^q(η)` at a smaller object.

The derived categories are arbitrary models (`HasDerivedCategory` instances), so nothing here
depends on a choice of model.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated

namespace Stacks.DerivedCategory.AdjunctionUnitTruncations

/-! ### Cohomology along the two maps of a distinguished triangle -/

section Homology

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, the first map is an isomorphism on
`H^q` as soon as `H^{q-1}(X₃)` and `H^q(X₃)` vanish. -/
theorem isIso_homologyMap_mor₁_of_isZero (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (q : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C (q - 1)).obj T.obj₃))
    (h₂ : IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor C q).map T.mor₁) := by
  have : Epi ((DerivedCategory.homologyFunctor C q).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT q]
    exact h₂.eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor C q).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (q - 1) q (by omega)]
    exact h₁.eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, the second map is an isomorphism on
`H^q` as soon as `H^q(X₁)` and `H^{q+1}(X₁)` vanish. -/
theorem isIso_homologyMap_mor₂_of_isZero (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (q : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₁))
    (h₂ : IsZero ((DerivedCategory.homologyFunctor C (q + 1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor C q).map T.mor₂) := by
  have : Epi ((DerivedCategory.homologyFunctor C q).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT q (q + 1) rfl]
    exact h₂.eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor C q).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT q]
    exact h₁.eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- The truncation triangle `τ_{≤ n} X ⟶ X ⟶ τ_{≥ n+1} X`. -/
abbrev truncTriangle (X : DerivedCategory C) (n : ℤ) : Triangle (DerivedCategory C) :=
  (DerivedCategory.TStructure.t.triangleLEGE n (n + 1) rfl).obj X

/-- The truncation triangle `τ_{≤ n} X ⟶ X ⟶ τ_{≥ n+1} X` is distinguished. -/
theorem truncTriangle_distinguished (X : DerivedCategory C) (n : ℤ) :
    truncTriangle X n ∈ distTriang (DerivedCategory C) :=
  DerivedCategory.TStructure.t.triangleLEGE_distinguished n (n + 1) rfl X

/-- The first object `τ_{≤ n} X` of the truncation triangle lies in `D^{≤ n}`. -/
instance (X : DerivedCategory C) (n : ℤ) : (truncTriangle X n).obj₁.IsLE n :=
  inferInstanceAs (((DerivedCategory.TStructure.t.truncLE n).obj X).IsLE n)

/-- The third object `τ_{≥ n+1} X` of the truncation triangle lies in `D^{≥ n+1}`. -/
instance (X : DerivedCategory C) (n : ℤ) : (truncTriangle X n).obj₃.IsGE (n + 1) :=
  inferInstanceAs (((DerivedCategory.TStructure.t.truncGE (n + 1)).obj X).IsGE (n + 1))

/-- The first object `τ_{≤ n} X` of the truncation triangle lies in `D^{≥ a}` if `X` does. -/
private theorem isGE_truncTriangle_obj₁ (X : DerivedCategory C) (n a : ℤ) [X.IsGE a] :
    (truncTriangle X n).obj₁.IsGE a :=
  inferInstanceAs (((DerivedCategory.TStructure.t.truncLE n).obj X).IsGE a)

/-- `H^q(τ_{≤ n} X) ⟶ H^q(X)` is an isomorphism for `q ≤ n`. -/
theorem isIso_homologyMap_truncTriangle_mor₁ (X : DerivedCategory C) (n q : ℤ) (hq : q ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor C q).map (truncTriangle X n).mor₁) :=
  isIso_homologyMap_mor₁_of_isZero _ (truncTriangle_distinguished X n) q
    (DerivedCategory.isZero_of_isGE _ (n + 1) (q - 1) (by omega))
    (DerivedCategory.isZero_of_isGE _ (n + 1) q (by omega))

/-- `H^q(X) ⟶ H^q(τ_{≥ n+1} X)` is an isomorphism for `n + 1 ≤ q`. -/
theorem isIso_homologyMap_truncTriangle_mor₂ (X : DerivedCategory C) (n q : ℤ) (hq : n < q) :
    IsIso ((DerivedCategory.homologyFunctor C q).map (truncTriangle X n).mor₂) :=
  isIso_homologyMap_mor₂_of_isZero _ (truncTriangle_distinguished X n) q
    (DerivedCategory.isZero_of_isLE _ n q hq)
    (DerivedCategory.isZero_of_isLE _ n (q + 1) (by omega))

end Homology

/-! ### The cohomology condition -/

section Condition

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Every cohomology object of `X` satisfies `P` or is zero. -/
def HomologyIn (P : ObjectProperty C) (X : DerivedCategory C) : Prop :=
  ∀ q : ℤ, P ((DerivedCategory.homologyFunctor C q).obj X) ∨
    IsZero ((DerivedCategory.homologyFunctor C q).obj X)

variable {P : ObjectProperty C} [P.IsClosedUnderIsomorphisms]

/-- Satisfying `P` or being zero is invariant under isomorphism of `H^q`. -/
private theorem prop_or_isZero_of_iso {X Y : DerivedCategory C} {q : ℤ}
    (e : (DerivedCategory.homologyFunctor C q).obj X ≅ (DerivedCategory.homologyFunctor C q).obj Y)
    (h : P ((DerivedCategory.homologyFunctor C q).obj X) ∨
      IsZero ((DerivedCategory.homologyFunctor C q).obj X)) :
    P ((DerivedCategory.homologyFunctor C q).obj Y) ∨
      IsZero ((DerivedCategory.homologyFunctor C q).obj Y) :=
  h.imp (P.prop_of_iso e) fun hX ↦ hX.of_iso e.symm

/-- The condition `HomologyIn P` is invariant under isomorphism. -/
theorem HomologyIn.of_iso {X Y : DerivedCategory C} (e : X ≅ Y) (h : HomologyIn P X) :
    HomologyIn P Y := fun q ↦
  prop_or_isZero_of_iso ((DerivedCategory.homologyFunctor C q).mapIso e) (h q)

/-- If every cohomology object of `X` satisfies `P` or is zero, then so does every cohomology
object of `τ_{≤ n} X`. -/
theorem HomologyIn.truncTriangle_obj₁ {X : DerivedCategory C} (h : HomologyIn P X) (n : ℤ) :
    HomologyIn P (truncTriangle X n).obj₁ := by
  intro q
  by_cases hq : q ≤ n
  · have := isIso_homologyMap_truncTriangle_mor₁ X n q hq
    exact prop_or_isZero_of_iso (asIso ((DerivedCategory.homologyFunctor C q).map
      (truncTriangle X n).mor₁)).symm (h q)
  · exact Or.inr (DerivedCategory.isZero_of_isLE _ n q (by omega))

/-- If every cohomology object of `X` satisfies `P` or is zero, then so does every cohomology
object of `τ_{≥ n+1} X`. -/
theorem HomologyIn.truncTriangle_obj₃ {X : DerivedCategory C} (h : HomologyIn P X) (n : ℤ) :
    HomologyIn P (truncTriangle X n).obj₃ := by
  intro q
  by_cases hq : n < q
  · have := isIso_homologyMap_truncTriangle_mor₂ X n q hq
    exact prop_or_isZero_of_iso (asIso ((DerivedCategory.homologyFunctor C q).map
      (truncTriangle X n).mor₂)) (h q)
  · exact Or.inr (DerivedCategory.isZero_of_isGE _ (n + 1) q (by omega))

end Condition

/-! ### Left t-exactness of a right adjoint -/

section Adjoint

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {F : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
  {G : _root_.DerivedCategory B ⥤ _root_.DerivedCategory A}

/-- **A right adjoint of a functor preserving `D^{≤ n}` preserves `D^{≥ n}`.** If `F ⊣ G` and `F`
carries `D^{≤ n - 1}` into `D^{≤ n - 1}`, then `G` carries `D^{≥ n}` into `D^{≥ n}`: a morphism
`Z ⟶ G(Y)` from `Z ∈ D^{≤ n - 1}` is the transpose of a morphism `F(Z) ⟶ Y`, which vanishes. -/
theorem isGE_obj_of_isLE_obj (adj : F ⊣ G) [G.PreservesZeroMorphisms]
    (hF : ∀ (X : _root_.DerivedCategory A) (n : ℤ), X.IsLE n → (F.obj X).IsLE n)
    (Y : _root_.DerivedCategory B) (n : ℤ) [Y.IsGE n] : (G.obj Y).IsGE n := by
  apply (DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega) _).2
  intro Z f hZ
  have : (F.obj Z).IsLE (n - 1) := hF Z (n - 1) hZ
  have h0 : (adj.homEquiv Z Y).symm f = 0 :=
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (n - 1) n (by omega) inferInstance
      inferInstance
  rw [← (adj.homEquiv Z Y).apply_symm_apply f, h0, Adjunction.homEquiv_unit, G.map_zero,
    comp_zero]

end Adjoint

/-! ### Invertibility of a unit depends only on the left adjoint -/

section UnitCriterion

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C}

/-- **The unit at `X` is invertible exactly when `F` is bijective on morphisms into `X`.** The
transpose of `F.map f` is `f ≫ η_X`, so the criterion is the Yoneda criterion for `η_X`. In
particular it depends only on `F`, not on the right adjoint or the adjunction. -/
theorem isIso_unit_app_iff_bijective (adj : F ⊣ G) (X : C) :
    IsIso (adj.unit.app X) ↔ ∀ Z : C, Function.Bijective (fun f : Z ⟶ X ↦ F.map f) := by
  have key : ∀ Z : C, (fun f : Z ⟶ X ↦ F.map f) =
      (adj.homEquiv Z (F.obj X)).symm ∘ (fun f : Z ⟶ X ↦ f ≫ adj.unit.app X) := by
    intro Z
    funext f
    simp only [Function.comp_apply]
    rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit]
    exact (adj.unit.naturality f).symm
  rw [isIso_iff_yoneda_map_bijective]
  refine forall_congr' fun Z ↦ ?_
  rw [key Z]
  exact ⟨fun h ↦ (adj.homEquiv Z (F.obj X)).symm.bijective.comp h,
    fun h ↦ (Function.Bijective.of_comp_iff' (adj.homEquiv Z (F.obj X)).symm.bijective _).1 h⟩

/-- Two adjunctions with the same left adjoint have their units invertible at the same objects. -/
theorem isIso_unit_app_iff_of_adjunction {G' : D ⥤ C} (adj : F ⊣ G) (adj' : F ⊣ G') (X : C) :
    IsIso (adj.unit.app X) ↔ IsIso (adj'.unit.app X) := by
  rw [isIso_unit_app_iff_bijective adj, isIso_unit_app_iff_bijective adj']

/-- If `F` is bijective on morphisms `Z ⟶ X` and `X ≅ X'`, then `F` is bijective on morphisms
`Z ⟶ X'`. -/
theorem bijective_map_of_iso {Z X X' : C} (e : X ≅ X')
    (h : Function.Bijective (fun f : Z ⟶ X ↦ F.map f)) :
    Function.Bijective (fun f : Z ⟶ X' ↦ F.map f) := by
  have : (fun f : Z ⟶ X' ↦ F.map f) =
      (fun g : F.obj Z ⟶ F.obj X ↦ g ≫ F.map e.hom) ∘ (fun f : Z ⟶ X ↦ F.map f) ∘
        (fun f : Z ⟶ X' ↦ f ≫ e.inv) := by
    funext f
    simp only [Function.comp_apply, ← F.map_comp, assoc, e.inv_hom_id, comp_id]
  rw [this]
  refine Function.Bijective.comp ⟨fun a b hab ↦ ?_, fun g ↦ ⟨g ≫ F.map e.inv, ?_⟩⟩
    (Function.Bijective.comp h ⟨fun a b hab ↦ ?_, fun g ↦ ⟨g ≫ e.hom, by simp⟩⟩)
  · simpa [← F.map_comp] using congrArg (· ≫ F.map e.inv) hab
  · simp [← F.map_comp]
  · simpa using congrArg (· ≫ e.hom) hab

end UnitCriterion

section ShiftCriterion

variable {C : Type*} [Category* C] {D : Type*} [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

/-- `F` is bijective on morphisms `Z⟦m⟧ ⟶ Y⟦m⟧` as soon as it is on morphisms `Z ⟶ Y`: the shift
functors are fully faithful and `F` commutes with them. -/
theorem bijective_map_shift {Z Y : C} (m : ℤ)
    (h : Function.Bijective (fun f : Z ⟶ Y ↦ F.map f)) :
    Function.Bijective (fun f : Z⟦m⟧ ⟶ Y⟦m⟧ ↦ F.map f) := by
  have hC := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C m))
  have hD := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D m))
  have : (fun f : Z⟦m⟧ ⟶ Y⟦m⟧ ↦ F.map f) =
      (fun g : (F.obj Z)⟦m⟧ ⟶ (F.obj Y)⟦m⟧ ↦
          (F.commShiftIso m).hom.app Z ≫ g ≫ (F.commShiftIso m).inv.app Y) ∘
        (fun g : F.obj Z ⟶ F.obj Y ↦ g⟦m⟧') ∘ (fun f : Z ⟶ Y ↦ F.map f) ∘
          (fun f : Z⟦m⟧ ⟶ Y⟦m⟧ ↦ hC.homEquiv.symm f) := by
    funext f
    simp only [Function.comp_apply]
    rw [← Functor.commShiftIso_hom_naturality_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).trans (congrArg F.map (hC.map_preimage f)) |>.symm
  rw [this]
  refine Function.Bijective.comp ⟨fun a b hab ↦ ?_, fun g ↦ ⟨(F.commShiftIso m).inv.app Z ≫ g ≫
    (F.commShiftIso m).hom.app Y, by simp⟩⟩ (Function.Bijective.comp (hD.map_bijective _ _)
      (Function.Bijective.comp h hC.homEquiv.symm.bijective))
  simpa using congrArg (fun g ↦ (F.commShiftIso m).inv.app Z ≫ g ≫ (F.commShiftIso m).hom.app Y) hab

variable {G : D ⥤ C}

/-- **The unit at `X⟦m⟧` is invertible as soon as the unit at `X` is**, for a left adjoint
commuting with the shift, with no compatibility between the unit and the shift. -/
theorem isIso_unit_app_shift (adj : F ⊣ G) (X : C) (m : ℤ) [IsIso (adj.unit.app X)] :
    IsIso (adj.unit.app (X⟦m⟧)) := by
  have hX := (isIso_unit_app_iff_bijective adj X).1 inferInstance
  rw [isIso_unit_app_iff_bijective adj]
  intro Z
  have e : Z ≅ (Z⟦-m⟧)⟦m⟧ := (shiftFunctorCompIsoId C (-m) m (by omega)).symm.app Z
  have hb := bijective_map_shift F m (hX (Z⟦-m⟧))
  -- transport along `e` in the source
  have : (fun f : Z ⟶ X⟦m⟧ ↦ F.map f) =
      (fun g : F.obj ((Z⟦-m⟧)⟦m⟧) ⟶ F.obj (X⟦m⟧) ↦ F.map e.hom ≫ g) ∘
        (fun f : (Z⟦-m⟧)⟦m⟧ ⟶ X⟦m⟧ ↦ F.map f) ∘ (fun f : Z ⟶ X⟦m⟧ ↦ e.inv ≫ f) := by
    funext f
    simp only [Function.comp_apply, ← F.map_comp, e.hom_inv_id_assoc]
  rw [this]
  refine Function.Bijective.comp
    ⟨fun a b hab ↦ ?_, fun g ↦ ⟨F.map e.inv ≫ g, by simp [← F.map_comp_assoc]⟩⟩
    (Function.Bijective.comp hb ⟨fun a b hab ↦ ?_, fun g ↦ ⟨e.hom ≫ g, by simp⟩⟩)
  · simpa [← F.map_comp_assoc] using congrArg (F.map e.inv ≫ ·) hab
  · simpa using congrArg (e.hom ≫ ·) hab

end ShiftCriterion

/-! ### The unit on bounded and on bounded below objects -/

section Unit

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {F : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
  {G : _root_.DerivedCategory B ⥤ _root_.DerivedCategory A}
  (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
  (hη : ∀ M : A, P M → ∀ n : ℤ,
    IsIso (adj.unit.app ((DerivedCategory.singleFunctor A n).obj M)))

local notation "H" q => DerivedCategory.homologyFunctor A q

/-- If `H^q(f)` and `H^q(G F f)` are isomorphisms, the unit is invertible on `H^q` at `X` exactly
when it is at `Y`. -/
private theorem isIso_homologyMap_unit_app_iff
    {F : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    {G : _root_.DerivedCategory B ⥤ _root_.DerivedCategory A} (adj : F ⊣ G)
    {X Y : _root_.DerivedCategory A} (f : X ⟶ Y)
    (q : ℤ) (h₁ : IsIso ((H q).map f)) (h₂ : IsIso ((H q).map ((F ⋙ G).map f))) :
    IsIso ((H q).map (adj.unit.app X)) ↔ IsIso ((H q).map (adj.unit.app Y)) := by
  have hnat := (H q).congr_map (adj.unit.naturality f)
  simp only [Functor.map_comp, Functor.id_map] at hnat
  rw [← isIso_comp_left_iff ((H q).map f), hnat, isIso_comp_right_iff]

omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- The unit is an isomorphism at a zero object. -/
theorem isIso_unit_app_of_isZero [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    {X : _root_.DerivedCategory A} (hX : IsZero X) : IsIso (adj.unit.app X) :=
  have hGF : IsZero ((F ⋙ G).obj X) := (F ⋙ G).map_isZero hX
  ⟨⟨0, hX.eq_of_src _ _, hGF.eq_of_src _ _⟩⟩

omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- The unit is an isomorphism at an object isomorphic to one where it is. -/
theorem isIso_unit_app_of_iso {X Y : _root_.DerivedCategory A} (e : X ≅ Y)
    [IsIso (adj.unit.app Y)] : IsIso (adj.unit.app X) := by
  have h := adj.unit.naturality e.hom
  simp only [Functor.id_map] at h
  have : adj.unit.app X = e.hom ≫ adj.unit.app Y ≫ (F ⋙ G).map e.inv := by
    rw [reassoc_of% h]
    simp only [Functor.comp_map, ← Functor.map_comp, e.hom_inv_id]
    simp
  rw [this]
  infer_instance

omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- If the unit is an isomorphism at `Y`, then `H^q(Y)` and `H^q(G F Y)` agree. -/
theorem isZero_homology_obj_of_isIso {Y : _root_.DerivedCategory A} [IsIso (adj.unit.app Y)]
    (q : ℤ) (hY : IsZero ((H q).obj Y)) : IsZero ((H q).obj ((F ⋙ G).obj Y)) :=
  hY.of_iso ((H q).mapIso (asIso (adj.unit.app Y))).symm

include hη in
omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- The unit is an isomorphism at an object concentrated in one degree whose cohomology there
satisfies `P` or is zero. -/
theorem isIso_unit_app_of_isGE_of_isLE_self [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (X : _root_.DerivedCategory A) (a : ℤ) [X.IsGE a] [X.IsLE a]
    (hX : HomologyIn P X) : IsIso (adj.unit.app X) := by
  rcases hX a with hP | hZ
  · obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero X a
      (fun i hi ↦ by
        rcases lt_or_gt_of_ne hi with h | h
        · exact DerivedCategory.isZero_of_isGE X a i h
        · exact DerivedCategory.isZero_of_isLE X a i h)
    have := hη _ hP a
    exact isIso_unit_app_of_iso adj e
  · refine isIso_unit_app_of_isZero adj ?_
    have : X.IsGE (a + 1) := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      rcases lt_or_eq_of_le (show i ≤ a by omega) with h | rfl
      · exact DerivedCategory.isZero_of_isGE X a i h
      · exact hZ
    exact DerivedCategory.TStructure.t.isZero X a (a + 1) (by omega)

include hη in
/-- **The bounded case.** The unit is an isomorphism at every object of `D^{[a, a + k]}` all of
whose cohomology objects satisfy `P` or are zero, by induction on `k`. -/
theorem isIso_unit_app_of_isGE_of_isLE (k : ℕ) :
    ∀ (X : _root_.DerivedCategory A) (a : ℤ), X.IsGE a → X.IsLE (a + k) → HomologyIn P X →
      IsIso (adj.unit.app X) := by
  induction k with
  | zero =>
    intro X a hGE hLE hX
    have := hGE
    have : X.IsLE a := by simpa using hLE
    exact isIso_unit_app_of_isGE_of_isLE_self adj P hη X a hX
  | succ k ih =>
    intro X a hGE hLE hX
    have := hGE
    have := hLE
    let T := truncTriangle X (a + k)
    have hT' : (F ⋙ G).mapTriangle.obj T ∈ distTriang _ :=
      (F ⋙ G).map_distinguished T (truncTriangle_distinguished X (a + k))
    -- the left term `τ_{≤ a + k} X`
    have hY : IsIso (adj.unit.app T.obj₁) :=
      ih T.obj₁ a (isGE_truncTriangle_obj₁ X _ a) (by dsimp [T]; infer_instance)
        (hX.truncTriangle_obj₁ _)
    -- the right term `τ_{≥ a + k + 1} X`
    have : T.obj₃.IsLE (a + k + 1) := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact (DerivedCategory.isZero_of_isLE X (a + ((k + 1 : ℕ) : ℤ)) i
        (by push_cast; omega)).of_iso (@asIso _ _ _ _ ((H i).map T.mor₂)
          (isIso_homologyMap_truncTriangle_mor₂ X (a + k) i (by omega))).symm
    have : T.obj₃.IsGE (a + k + 1) := by dsimp [T]; infer_instance
    have hZ : IsIso (adj.unit.app T.obj₃) :=
      isIso_unit_app_of_isGE_of_isLE_self adj P hη T.obj₃ (a + k + 1)
        (hX.truncTriangle_obj₃ _)
    change IsIso (adj.unit.app T.obj₂)
    rw [DerivedCategory.isIso_iff]
    intro q
    by_cases hq : q ≤ a + k
    · have h₁ := isIso_homologyMap_truncTriangle_mor₁ X (a + k) q hq
      have h₂ : IsIso ((H q).map ((F ⋙ G).mapTriangle.obj T).mor₁) :=
        isIso_homologyMap_mor₁_of_isZero _ hT' q
          (isZero_homology_obj_of_isIso adj (q - 1)
            (DerivedCategory.isZero_of_isGE T.obj₃ (a + k + 1) (q - 1) (by omega)))
          (isZero_homology_obj_of_isIso adj q
            (DerivedCategory.isZero_of_isGE T.obj₃ (a + k + 1) q (by omega)))
      exact (isIso_homologyMap_unit_app_iff adj T.mor₁ q h₁ h₂).1 (Functor.map_isIso _ _)
    · have h₁ := isIso_homologyMap_truncTriangle_mor₂ X (a + k) q (by omega)
      have h₂ : IsIso ((H q).map ((F ⋙ G).mapTriangle.obj T).mor₂) :=
        isIso_homologyMap_mor₂_of_isZero _ hT' q
          (isZero_homology_obj_of_isIso adj q
            (DerivedCategory.isZero_of_isLE T.obj₁ (a + k) q (by omega)))
          (isZero_homology_obj_of_isIso adj (q + 1)
            (DerivedCategory.isZero_of_isLE T.obj₁ (a + k) (q + 1) (by omega)))
      exact (isIso_homologyMap_unit_app_iff adj T.mor₂ q h₁ h₂).2 (Functor.map_isIso _ _)

include hη in
/-- **The bounded below case.** If `F` and `G` preserve `D^{≥ n}` for every `n`, the unit is an
isomorphism at every bounded below object all of whose cohomology objects satisfy `P` or are
zero: in degree `q` it is compared with the unit at `τ_{≤ n} X` for `n ≥ q`, which is bounded,
the term `τ_{≥ n + 1} X` and its image under `F ⋙ G` having no cohomology in degrees `≤ n`. -/
theorem isIso_unit_app_of_isGE
    (hFGE : ∀ (X : _root_.DerivedCategory A) (n : ℤ), X.IsGE n → ((F ⋙ G).obj X).IsGE n)
    (X : _root_.DerivedCategory A) (a : ℤ) [X.IsGE a] (hX : HomologyIn P X) :
    IsIso (adj.unit.app X) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  let n := max q a
  change IsIso ((H q).map (adj.unit.app (truncTriangle X n).obj₂))
  let T := truncTriangle X n
  have hT' : (F ⋙ G).mapTriangle.obj T ∈ distTriang _ :=
    (F ⋙ G).map_distinguished T (truncTriangle_distinguished X n)
  have : IsIso (adj.unit.app T.obj₁) :=
    isIso_unit_app_of_isGE_of_isLE adj P hη (n - a).toNat T.obj₁ a
      (isGE_truncTriangle_obj₁ X n a)
      (by
        have : T.obj₁.IsLE n := by dsimp [T]; infer_instance
        exact DerivedCategory.TStructure.t.isLE_of_le _ n _ (by omega))
      (hX.truncTriangle_obj₁ _)
  have : ((F ⋙ G).obj T.obj₃).IsGE (n + 1) := hFGE _ _ inferInstance
  have h₁ := isIso_homologyMap_truncTriangle_mor₁ X n q (by omega)
  have h₂ : IsIso ((H q).map ((F ⋙ G).mapTriangle.obj T).mor₁) :=
    isIso_homologyMap_mor₁_of_isZero _ hT' q
      (DerivedCategory.isZero_of_isGE ((F ⋙ G).obj T.obj₃) (n + 1) (q - 1) (by omega))
      (DerivedCategory.isZero_of_isGE ((F ⋙ G).obj T.obj₃) (n + 1) q (by omega))
  exact (isIso_homologyMap_unit_app_iff adj T.mor₁ q h₁ h₂).1 (Functor.map_isIso _ _)

end Unit

/-! ### Derived limits of towers -/

section DerivedLimit

variable {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Derived limits transfer along isomorphisms of towers compatible with the successor
maps.** Only the successor transition maps enter the definition of a derived limit. -/
theorem isDerivedLimit_of_succIso {F G : ℕᵒᵖ ⥤ D} [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩] (e : ∀ n : ℕ, F.obj ⟨n⟩ ≅ G.obj ⟨n⟩)
    (he : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op)
    (K : D) (hK : IsDerivedLimit F K) : IsDerivedLimit G K := by
  obtain ⟨p, δ, hT⟩ := hK
  let φ : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩ :=
    { hom := Pi.lift fun n ↦ Pi.π _ n ≫ (e n).hom
      inv := Pi.lift fun n ↦ Pi.π _ n ≫ (e n).inv
      hom_inv_id := Pi.hom_ext _ _ fun n ↦ by simp
      inv_hom_id := Pi.hom_ext _ _ fun n ↦ by simp }
  have hd : (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) ≫ φ.hom =
      φ.hom ≫ (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [φ, Preadditive.sub_comp, Preadditive.comp_sub, he]
  refine ⟨p ≫ φ.hom, φ.inv ≫ δ, isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _) φ.symm φ.symm ?_ ?_ ?_
  · simp
  · dsimp only [Triangle.mk_mor₂, Iso.symm_hom]
    rw [Iso.comp_inv_eq, assoc, hd, Iso.inv_hom_id_assoc]
  · simp

/-- **Two derived limits of the same tower are isomorphic** (not canonically). -/
theorem nonempty_iso_of_isDerivedLimit (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (K K' : D) (hK : IsDerivedLimit F K) (hK' : IsDerivedLimit F K') : Nonempty (K ≅ K') := by
  obtain ⟨p, δ, hT⟩ := hK
  obtain ⟨p', δ', hT'⟩ := hK'
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ (rot_of_distTriang _ hT)
    (rot_of_distTriang _ hT') (Iso.refl _)
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D (1 : ℤ))).preimageIso
    (Triangle.π₃.mapIso e)⟩

end DerivedLimit

section TruncationTower

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The cone of the tower of truncations: the product of the truncation maps. -/
abbrev truncGETowerCone (E : _root_.DerivedCategory C)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩] :
    E ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩ :=
  Pi.lift fun n : ℕ ↦ ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E :
    E ⟶ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩)

/-- The `n`-th component of `truncGETowerCone E` is the truncation map `E ⟶ τ_{≥ -n} E`. -/
theorem truncGETowerCone_π (E : _root_.DerivedCategory C)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩] (n : ℕ) :
    truncGETowerCone E ≫ Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) n =
      ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E :
        E ⟶ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) :=
  Pi.lift_comp_π _ _

/-- The truncation maps are compatible with the transition maps of the tower. -/
theorem truncGEπ_comp_truncGETower_map_succ (E : _root_.DerivedCategory C) (n : ℕ) :
    ((DerivedCategory.TStructure.t.truncGEπ (-((n + 1 : ℕ) : ℤ))).app E :
        E ⟶ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n + 1⟩) ≫
      (Stacks.DerivedLimit.truncGETower C E).map (homOfLE (Nat.le_succ n)).op =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E := by
  rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
  exact TStructure.π_natTransTruncGEOfLE_app _ _ _ _ _

/-- **An object is a derived limit of its truncation tower as soon as every comparison map to a
derived limit is an isomorphism.** This converts the conclusion of Stacks 0D6P, which is stated
for an arbitrary derived limit `L` with a map `c : E ⟶ L` compatible with the truncations, into
the statement that `E` itself is a derived limit of the tower. -/
theorem isDerivedLimit_truncGETower_of_forall_isIso (E : _root_.DerivedCategory C)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩]
    (h : ∀ (L : _root_.DerivedCategory C) (c : E ⟶ L)
      (q : L ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩),
      (∃ δ : (∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk q (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) (n + 1) ≫
              (Stacks.DerivedLimit.truncGETower C E).map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang (_root_.DerivedCategory C)) →
      (∀ n : ℕ, c ≫ q ≫ Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) → IsIso c) :
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower C E) E := by
  obtain ⟨L, q, δ, hT⟩ := exists_isDerivedLimit (Stacks.DerivedLimit.truncGETower C E)
  have hzero : truncGETowerCone E ≫ (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower C E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower C E).map (homOfLE (Nat.le_succ n)).op) = 0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [assoc, Pi.lift_comp_π, zero_comp, Preadditive.comp_sub, ← assoc, truncGETowerCone_π,
      truncGETowerCone_π]
    exact sub_eq_zero.mpr (truncGEπ_comp_truncGETower_map_succ E n).symm
  obtain ⟨c, hc⟩ := Triangle.coyoneda_exact₂ _ hT (truncGETowerCone E) hzero
  have hc' : c ≫ q = truncGETowerCone E := hc.symm
  have hiso : IsIso c := h L c q ⟨δ, hT⟩ (fun n ↦ by
    rw [reassoc_of% hc']
    exact truncGETowerCone_π E n)
  refine ⟨c ≫ q, δ ≫ (inv c)⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ (asIso c) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp only [Triangle.mk_mor₁, Iso.refl_hom, comp_id, asIso_hom]
  · simp only [Triangle.mk_mor₂, Iso.refl_hom, comp_id, id_comp]
  · simp only [Triangle.mk_mor₃, assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, comp_id, Iso.refl_hom, id_comp, asIso_hom]

/-- `H^q(X) ⟶ H^q(τ_{≥ m} X)` is an isomorphism for `m ≤ q`. -/
theorem isIso_homologyMap_truncGEπ_app (X : _root_.DerivedCategory C) (m q : ℤ) (hq : m ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncGEπ m).app X)) :=
  isIso_homologyMap_mor₂_of_isZero _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished m X)
    q (DerivedCategory.isZero_of_isLE _ (m - 1) q (by omega))
    (DerivedCategory.isZero_of_isLE _ (m - 1) (q + 1) (by omega))

/-- If every cohomology object of `X` satisfies `P` or is zero, then so does every cohomology
object of `τ_{≥ m} X`. -/
theorem HomologyIn.truncGE {P : ObjectProperty C} [P.IsClosedUnderIsomorphisms]
    {X : _root_.DerivedCategory C} (h : HomologyIn P X) (m : ℤ) :
    HomologyIn P ((DerivedCategory.TStructure.t.truncGE m).obj X) := by
  intro q
  by_cases hq : m ≤ q
  · have := isIso_homologyMap_truncGEπ_app X m q hq
    exact prop_or_isZero_of_iso (asIso ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncGEπ m).app X))) (h q)
  · exact Or.inr (DerivedCategory.isZero_of_isGE _ m q (by omega))

end TruncationTower

section TExact

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (F : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
  (hFLE : ∀ (X : _root_.DerivedCategory A) (n : ℤ), X.IsLE n → (F.obj X).IsLE n)
  (hFGE : ∀ (X : _root_.DerivedCategory A) (n : ℤ), X.IsGE n → (F.obj X).IsGE n)

include hFGE in
/-- The comparison `τ_{≥ m}(F E) ⟶ F(τ_{≥ m} E)` for a functor `F` preserving `D^{≥ m}`. -/
def truncGEComparison (E : _root_.DerivedCategory A) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncGE m).obj (F.obj E) ⟶
      F.obj ((DerivedCategory.TStructure.t.truncGE m).obj E) :=
  haveI := hFGE ((DerivedCategory.TStructure.t.truncGE m).obj E) m inferInstance
  DerivedCategory.TStructure.t.descTruncGE
    (F.map ((DerivedCategory.TStructure.t.truncGEπ m).app E)) m

include hFGE in
omit [F.CommShift ℤ] [F.IsTriangulated] in
/-- Precomposing `truncGEComparison F hFGE E m` with the truncation map `F E ⟶ τ_{≥ m}(F E)`
gives `F` applied to the truncation map `E ⟶ τ_{≥ m} E`. -/
theorem π_truncGEComparison (E : _root_.DerivedCategory A) (m : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ m).app (F.obj E) ≫ truncGEComparison F hFGE E m =
      F.map ((DerivedCategory.TStructure.t.truncGEπ m).app E) := by
  have := hFGE ((DerivedCategory.TStructure.t.truncGEπ m).app E |> fun _ ↦
    (DerivedCategory.TStructure.t.truncGE m).obj E) m inferInstance
  exact TStructure.π_descTruncGE _ _ _

include hFLE hFGE in
/-- **A t-exact functor commutes with the truncations `τ_{≥ m}`.** -/
theorem isIso_truncGEComparison (E : _root_.DerivedCategory A) (m : ℤ) :
    IsIso (truncGEComparison F hFGE E m) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  by_cases hq : m ≤ q
  · have h₁ := isIso_homologyMap_truncGEπ_app (F.obj E) m q hq
    have hT := F.map_distinguished _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished m E)
    have : (F.mapTriangle.obj
        ((DerivedCategory.TStructure.t.triangleLTGE m).obj E)).obj₁.IsLE (m - 1) :=
      hFLE ((DerivedCategory.TStructure.t.truncLT m).obj E) _ inferInstance
    have h₂ : IsIso ((DerivedCategory.homologyFunctor B q).map
        (F.map ((DerivedCategory.TStructure.t.truncGEπ m).app E))) :=
      isIso_homologyMap_mor₂_of_isZero _ hT q
        (DerivedCategory.isZero_of_isLE _ (m - 1) q (by omega))
        (DerivedCategory.isZero_of_isLE _ (m - 1) (q + 1) (by omega))
    have h := (DerivedCategory.homologyFunctor B q).congr_map (π_truncGEComparison F hFGE E m)
    rw [Functor.map_comp] at h
    have : IsIso ((DerivedCategory.homologyFunctor B q).map
        ((DerivedCategory.TStructure.t.truncGEπ m).app (F.obj E)) ≫
        (DerivedCategory.homologyFunctor B q).map (truncGEComparison F hFGE E m)) := by
      rw [h]; exact h₂
    exact IsIso.of_isIso_comp_left ((DerivedCategory.homologyFunctor B q).map
      ((DerivedCategory.TStructure.t.truncGEπ m).app (F.obj E))) _
  · have := hFGE ((DerivedCategory.TStructure.t.truncGE m).obj E) m inferInstance
    exact ⟨⟨0, (DerivedCategory.isZero_of_isGE _ m q (by omega)).eq_of_src _ _,
      (DerivedCategory.isZero_of_isGE _ m q (by omega)).eq_of_src _ _⟩⟩

include hFLE hFGE in
/-- **The tower `n ↦ τ_{≥ -n}(F E)` is the image under `F` of the tower `n ↦ τ_{≥ -n} E`**, so
`F E` is a derived limit of the latter as soon as it is one of the former. -/
theorem isDerivedLimit_map_truncGETower (E : _root_.DerivedCategory A)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower B (F.obj E)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower A E ⋙ F).obj ⟨n⟩]
    (h : IsDerivedLimit (Stacks.DerivedLimit.truncGETower B (F.obj E)) (F.obj E)) :
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower A E ⋙ F) (F.obj E) := by
  refine isDerivedLimit_of_succIso (fun n ↦ @asIso _ _ _ _ (truncGEComparison F hFGE E (-(n : ℤ)))
    (isIso_truncGEComparison F hFLE hFGE E _)) (fun n ↦ ?_) _ h
  have := hFGE ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E) (-(n : ℤ)) inferInstance
  have : (F.obj ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E)).IsGE
      (-((n + 1 : ℕ) : ℤ)) := DerivedCategory.TStructure.t.isGE_of_ge _ _ (-(n : ℤ)) (by omega)
  dsimp only [asIso_hom, Functor.comp_map]
  rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ,
    Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
  change (DerivedCategory.TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
      (by omega)).app (F.obj E) ≫ truncGEComparison F hFGE E (-(n : ℤ)) =
    truncGEComparison F hFGE E (-((n + 1 : ℕ) : ℤ)) ≫
      F.map ((DerivedCategory.TStructure.t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (by omega)).app E)
  refine DerivedCategory.TStructure.t.from_truncGE_obj_ext ?_
  rw [← assoc, TStructure.π_natTransTruncGEOfLE_app, π_truncGEComparison,
    reassoc_of% (π_truncGEComparison F hFGE E _), ← Functor.map_comp,
    TStructure.π_natTransTruncGEOfLE_app]

end TExact

/-! ### The unit on all objects -/

section Unbounded

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  [HasLimitsOfShape (Discrete ℕ) (_root_.DerivedCategory A)]
  [HasLimitsOfShape (Discrete ℕ) (_root_.DerivedCategory B)]
  {F : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
  {G : _root_.DerivedCategory B ⥤ _root_.DerivedCategory A}
  (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
  (hη : ∀ M : A, P M → ∀ n : ℤ,
    IsIso (adj.unit.app ((DerivedCategory.singleFunctor A n).obj M)))
  (hFLE : ∀ (X : _root_.DerivedCategory A) (n : ℤ), X.IsLE n → (F.obj X).IsLE n)
  (hFGE : ∀ (X : _root_.DerivedCategory A) (n : ℤ), X.IsGE n → (F.obj X).IsGE n)
  (hA : ∀ E : _root_.DerivedCategory A, HomologyIn P E →
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower A E) E)
  (hB : ∀ E : _root_.DerivedCategory A, HomologyIn P E →
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower B (F.obj E)) (F.obj E))

local notation "H" q => DerivedCategory.homologyFunctor A q

include adj hFLE hFGE in
omit [HasLimitsOfShape (Discrete ℕ) (_root_.DerivedCategory A)]
  [HasLimitsOfShape (Discrete ℕ) (_root_.DerivedCategory B)] [F.CommShift ℤ] [F.IsTriangulated] in
/-- If `F` is t-exact and `F ⊣ G`, then `F ⋙ G` carries `D^{≥ n}` into `D^{≥ n}`. -/
theorem isGE_comp_obj (X : _root_.DerivedCategory A) (n : ℤ) (hX : X.IsGE n) :
    ((F ⋙ G).obj X).IsGE n :=
  have := hFGE X n hX
  isGE_obj_of_isLE_obj adj hFLE (F.obj X) n

include hη hFLE hFGE hA hB in
/-- **`G F E ≅ E` for every `E` whose cohomology objects satisfy `P`**, non-canonically: `E`
and `F E` are derived limits of their truncation towers, `G` preserves derived limits (being a
right adjoint), and the unit identifies the image under `F ⋙ G` of the truncation tower of `E`
with that tower, the unit being invertible on bounded below objects. -/
theorem nonempty_comp_obj_iso (E : _root_.DerivedCategory A) (hE : HomologyIn P E) :
    Nonempty ((F ⋙ G).obj E ≅ E) := by
  have : G.IsRightAdjoint := adj.isRightAdjoint
  have h₁ : IsDerivedLimit (Stacks.DerivedLimit.truncGETower A E ⋙ F) (F.obj E) :=
    isDerivedLimit_map_truncGETower F hFLE hFGE E (hB E hE)
  obtain ⟨_, h₂⟩ := ModuleSystemRlimTensor.isDerivedLimit_map_of_iso G
    (Stacks.DerivedLimit.truncGETower A E ⋙ F) ((Stacks.DerivedLimit.truncGETower A E ⋙ F) ⋙ G)
    (Iso.refl _) (F.obj E) h₁
  have hunit : ∀ n : ℕ, IsIso (adj.unit.app ((Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩)) :=
    fun n ↦
    have : ((Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩).IsGE (-(n : ℤ)) :=
      inferInstanceAs (((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E).IsGE (-(n : ℤ)))
    isIso_unit_app_of_isGE adj P hη (isGE_comp_obj adj hFLE hFGE) _ (-(n : ℤ))
      (hE.truncGE _)
  have h₃ : IsDerivedLimit (Stacks.DerivedLimit.truncGETower A E) (G.obj (F.obj E)) := by
    refine isDerivedLimit_of_succIso
      (fun n ↦ (@asIso _ _ _ _ (adj.unit.app ((Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩))
        (hunit n)).symm)
      (fun n ↦ ?_) _ h₂
    have := hunit n
    have := hunit (n + 1)
    dsimp only [Iso.symm_hom, asIso_inv, Functor.comp_map]
    rw [IsIso.comp_inv_eq, assoc, IsIso.eq_inv_comp]
    exact (adj.unit.naturality _).symm
  exact nonempty_iso_of_isDerivedLimit _ _ _ h₃ (hA E hE)

include hη hFLE hFGE hA hB in
/-- **The unit is an isomorphism at every object whose cohomology objects satisfy `P` or
vanish.** In degree `q`, compare with the unit at `τ_{≥ q} E`, which is bounded below; the
term `τ_{≤ q-1} E` and its image under `F ⋙ G`, which is isomorphic to it, have no cohomology in
degrees `q` and `q + 1`. -/
theorem isIso_unit_app (E : _root_.DerivedCategory A) (hE : HomologyIn P E) :
    IsIso (adj.unit.app E) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  let T := truncTriangle E (q - 1)
  change IsIso ((H q).map (adj.unit.app T.obj₂))
  have hT : T ∈ distTriang _ := truncTriangle_distinguished E (q - 1)
  have hT' : (F ⋙ G).mapTriangle.obj T ∈ distTriang _ := (F ⋙ G).map_distinguished T hT
  have : T.obj₃.IsGE q := by
    have : T.obj₃.IsGE (q - 1 + 1) := inferInstance
    simpa using this
  have : IsIso (adj.unit.app T.obj₃) :=
    isIso_unit_app_of_isGE adj P hη (isGE_comp_obj adj hFLE hFGE) _ q
      (hE.truncTriangle_obj₃ _)
  obtain ⟨e⟩ := nonempty_comp_obj_iso adj P hη hFLE hFGE hA hB T.obj₁ (hE.truncTriangle_obj₁ _)
  have h₁ := isIso_homologyMap_truncTriangle_mor₂ E (q - 1) q (by omega)
  have h₂ : IsIso ((H q).map ((F ⋙ G).mapTriangle.obj T).mor₂) :=
    isIso_homologyMap_mor₂_of_isZero _ hT' q
      ((DerivedCategory.isZero_of_isLE T.obj₁ (q - 1) q (by omega)).of_iso ((H q).mapIso e))
      ((DerivedCategory.isZero_of_isLE T.obj₁ (q - 1) (q + 1) (by omega)).of_iso
        ((H (q + 1)).mapIso e))
  exact (isIso_homologyMap_unit_app_iff adj T.mor₂ q h₁ h₂).2 (Functor.map_isIso _ _)

end Unbounded

section DegreeZero

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {F : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
  {G : _root_.DerivedCategory B ⥤ _root_.DerivedCategory A}
  (adj : F ⊣ G) [F.CommShift ℤ]

/-- **Degree zero suffices**: if the unit is invertible at `M[0]`, it is invertible at `M[n]` for
every `n`, the left adjoint commuting with the shift. -/
theorem isIso_unit_app_singleFunctor_obj (M : A)
    [IsIso (adj.unit.app ((DerivedCategory.singleFunctor A 0).obj M))] (n : ℤ) :
    IsIso (adj.unit.app ((DerivedCategory.singleFunctor A n).obj M)) := by
  have e : ((DerivedCategory.singleFunctor A 0).obj M)⟦-n⟧ ≅
      (DerivedCategory.singleFunctor A n).obj M :=
    ((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app M
  have := isIso_unit_app_shift F adj ((DerivedCategory.singleFunctor A 0).obj M) (-n)
  exact isIso_unit_app_of_iso adj e.symm

end DegreeZero

end Stacks.DerivedCategory.AdjunctionUnitTruncations

end
