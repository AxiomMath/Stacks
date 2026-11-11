module

public import StacksFrontier.CategoryTheory.Triangulated.Localization.Pretriangulated
import StacksCore.Tactic.StacksAttribute

/-!
# The Ore conditions from MS6, and the objects killed by a localization functor

For a class `W` of morphisms of a pre-triangulated category satisfying MS6, this file shows
that `W` contains every isomorphism once it contains the identities, that under MS1 the axiom
MS5 in the form `f ∈ W ⇔ f[1] ∈ W` is equivalent to stability under every shift, and that MS1,
MS5 and MS6 imply both Ore conditions of MS2. It then characterises the objects `Z` whose image
under a localization functor `Q : 𝒟 ⥤ 𝒟_S` is zero, by seven equivalent conditions.

## References

* [Stacks, Tag 05R2](https://stacks.math.columbia.edu/tag/05R2),
  [Tag 05R3](https://stacks.math.columbia.edu/tag/05R3),
  [Tag 0H30](https://stacks.math.columbia.edu/tag/0H30),
  [Tag 05R8](https://stacks.math.columbia.edu/tag/05R8).
-/

section

@[expose] public section

/-!
### Isomorphisms and the Ore conditions from MS6

If a class `W` of morphisms of a pre-triangulated category contains the identities and
satisfies MS6 (`MorphismProperty.HasMS6`), then it contains every isomorphism. If `W` is
multiplicative and compatible with the triangulated structure (MS1, MS5 and MS6), then it
satisfies both Ore conditions of MS2: every right fraction is completed to a commutative square
by a left fraction (LMS2), and every left fraction by a right fraction (RMS2). Only these two
existence conditions are asserted, not the cancellation conditions that
`MorphismProperty.HasLeftCalculusOfFractions` and `MorphismProperty.HasRightCalculusOfFractions`
also contain.
-/

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

universe u v

namespace CategoryTheory.MorphismProperty

/-- MS6 without the separate shift-stability axiom MS5. -/
class HasMS6 {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C) : Prop where
  /-- A morphism of `W` between the first two objects of two distinguished triangles
  extends to a morphism of `W` between their third objects. -/
  exists_lift (T₁ T₂ : Triangle C) (hT₁ : T₁ ∈ distinguishedTriangles)
    (hT₂ : T₂ ∈ distinguishedTriangles) (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (ha : W a) (hb : W b) (hab : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, W c ∧ T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃

/-- A class of morphisms compatible with the triangulated structure satisfies MS6. -/
instance hasMS6_of_isCompatibleWithTriangulation
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C) [W.IsCompatibleWithTriangulation] :
    W.HasMS6 where
  exists_lift T₁ T₂ hT₁ hT₂ a b ha hb hab :=
    (W.compatible_with_triangulation T₁ T₂ hT₁ hT₂ a b ha hb hab).imp
      fun _ ⟨hc, h₁, h₂⟩ => ⟨hc, h₁, h₂⟩

/-- If `W` contains all identities and satisfies MS6, then `W` contains every isomorphism of
`C`. -/
@[stacks 05R3 "(1)"]
theorem isIso_mem_of_hasMS6
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C)
    [W.ContainsIdentities] [W.HasMS6]
    {X Y : C} (f : X ⟶ Y) [IsIso f] : W f := by
  let : Zero C := HasZeroObject.zero' C
  have hd {Y' : C} (g : X ⟶ Y') [IsIso g] :
      Triangle.mk (0 : (0 : C) ⟶ X) g 0 ∈ distinguishedTriangles :=
    (Triangle.distinguished_iff_of_isZero₁ _ (isZero_zero C)).2 (by dsimp; infer_instance)
  obtain ⟨c, hc, hc₂, _⟩ := HasMS6.exists_lift _ _ (hd (𝟙 X)) (hd f) (𝟙 (0 : C)) (𝟙 X)
    (W.id_mem _) (W.id_mem _) (by simp)
  have hcf : c = f := by simpa using hc₂
  rwa [hcf] at hc

/-- In the presence of MS1 and MS6, the axiom MS5 in the form `f ∈ W ⇔ f[1] ∈ W` is equivalent
to `W` being stable under every shift `[n]`, `n : ℤ`, which is
`MorphismProperty.IsCompatibleWithShift ℤ`. By MS6 and the identities of MS1, `W` contains every
isomorphism, so by MS1 it is closed under isomorphism of arrows; since `f[n][1]` is isomorphic
to `f[n + 1]` as an arrow, `f[n] ∈ W ⇔ f[n + 1] ∈ W` for every `n`, and induction on `n` from
`f[0] ≅ f` gives `f[n] ∈ W ⇔ f ∈ W`. -/
theorem isCompatibleWithShift_iff_of_hasMS6
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C) [W.IsMultiplicative] [W.HasMS6] :
    W.IsCompatibleWithShift ℤ ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W (f⟦(1 : ℤ)⟧') := by
  refine ⟨fun _ _ _ f => (IsCompatibleWithShift.iff W f (1 : ℤ)).symm, fun h => ?_⟩
  have : W.RespectsIso := respectsIso_of_isStableUnderComposition fun _ _ f hf => by
    have : IsIso f := hf
    exact W.isIso_mem_of_hasMS6 f
  have key (a b : ℤ) (hab : a + 1 = b) {X Y : C} (f : X ⟶ Y) :
      W (f⟦b⟧') ↔ W (f⟦a⟧') :=
    (W.arrow_iso_iff
      (Arrow.isoOfNatIso (shiftFunctorAdd' C a 1 b hab) (CategoryTheory.Arrow.mk f))).trans
      (h (f⟦a⟧')).symm
  have hn (n : ℤ) : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W (f⟦n⟧') ↔ W f := by
    induction n with
    | zero => exact fun X Y f =>
        W.arrow_iso_iff (Arrow.isoOfNatIso (shiftFunctorZero C ℤ) (CategoryTheory.Arrow.mk f))
    | succ i ih => exact fun X Y f => (key i (i + 1) rfl f).trans (ih f)
    | pred i ih => exact fun X Y f => (key (-i - 1) (-i) (by omega) f).symm.trans (ih f)
  exact ⟨fun n => MorphismProperty.ext _ _ fun _ _ f => hn n f⟩

/-- For a class `W` satisfying MS1, being compatible with the triangulated structure in the
sense of `MorphismProperty.IsCompatibleWithTriangulation` is equivalent to the two axioms as
Stacks states them: MS5 in the form `f ∈ W ⇔ f[1] ∈ W`, and MS6. The passage between the two
forms of MS5 is `isCompatibleWithShift_iff_of_hasMS6`. -/
@[stacks 05R2 "with MS5 in the form `f ∈ S ⇔ f[1] ∈ S`"]
theorem isCompatibleWithTriangulation_iff_shift_one_and_hasMS6
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C) [W.IsMultiplicative] :
    W.IsCompatibleWithTriangulation ↔
      (∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W (f⟦(1 : ℤ)⟧')) ∧ W.HasMS6 := by
  refine ⟨fun _ => ⟨fun _ _ f => (IsCompatibleWithShift.iff W f (1 : ℤ)).symm, inferInstance⟩,
    fun ⟨h5, h6⟩ => ?_⟩
  have : W.IsCompatibleWithShift ℤ := (W.isCompatibleWithShift_iff_of_hasMS6).2 h5
  exact
    { compatible_with_triangulation := fun T₁ T₂ hT₁ hT₂ a b ha hb hab =>
        (h6.exists_lift T₁ T₂ hT₁ hT₂ a b ha hb hab).imp fun _ ⟨hc, h₁, h₂⟩ => ⟨hc, h₁, h₂⟩ }

end CategoryTheory.MorphismProperty


/-- **LMS2**, the left Ore condition: if `W` is multiplicative and compatible with the
triangulated structure, every right fraction can be completed to a commuting square by a left
fraction. -/
theorem isCompatibleWithTriangulation_lms2
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C)
    [W.IsMultiplicative]
    [W.IsCompatibleWithTriangulation]
    ⦃X Y : C⦄ (φ : W.RightFraction X Y) :
    ∃ ψ : W.LeftFraction X Y, φ.f ≫ ψ.s = φ.s ≫ ψ.f := by
  obtain ⟨Z, g, h, hT₁⟩ := distinguished_cocone_triangle₁ φ.f
  obtain ⟨Y', f', h', hT₂⟩ := distinguished_cocone_triangle (g ≫ φ.s)
  obtain ⟨s', hs', hcomm, _⟩ := W.compatible_with_triangulation
    (Triangle.mk g φ.f h) (Triangle.mk (g ≫ φ.s) f' h')
    hT₁ hT₂ (𝟙 Z) φ.s (W.id_mem _) φ.hs (by simp)
  with_implicit exact ⟨MorphismProperty.LeftFraction.mk f' s' hs', hcomm⟩

/-- **RMS2**, the right Ore condition: if `W` is multiplicative and compatible with the
triangulated structure, every left fraction can be completed to a commuting square by a right
fraction. -/
theorem isCompatibleWithTriangulation_rms2
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C)
    [W.IsMultiplicative]
    [W.IsCompatibleWithTriangulation]
    ⦃X Y : C⦄ (φ : W.LeftFraction X Y) :
    ∃ ψ : W.RightFraction X Y, ψ.s ≫ φ.f = ψ.f ≫ φ.s := by
  obtain ⟨Z, g, h, hT₁⟩ := distinguished_cocone_triangle φ.f
  obtain ⟨X', f', h', hT₂⟩ := distinguished_cocone_triangle₁ (φ.s ≫ g)
  have hd₁ : Triangle.mk g h (-φ.f⟦(1 : ℤ)⟧') ∈ distinguishedTriangles := by
    with_implicit simpa only [Triangle.rotate, Triangle.mk] using rot_of_distTriang _ hT₁
  have hd₂ : Triangle.mk (φ.s ≫ g) h' (-f'⟦(1 : ℤ)⟧') ∈ distinguishedTriangles := by
    with_implicit simpa only [Triangle.rotate, Triangle.mk] using rot_of_distTriang _ hT₂
  obtain ⟨c, hc, _, hcomm⟩ := W.compatible_with_triangulation
    (Triangle.mk (φ.s ≫ g) h' (-f'⟦(1 : ℤ)⟧')) (Triangle.mk g h (-φ.f⟦(1 : ℤ)⟧'))
    hd₂ hd₁ φ.s (𝟙 Z) φ.hs (W.id_mem _) (by simp)
  refine ⟨MorphismProperty.RightFraction.mk ((shiftFunctor C (1 : ℤ)).preimage c) ?_ f', ?_⟩
  · apply (MorphismProperty.IsCompatibleWithShift.iff W _ (1 : ℤ)).1
    with_implicit simpa only [Functor.map_preimage] using hc
  · apply (shiftFunctor C (1 : ℤ)).map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    simpa only [Triangle.mk_mor₃, Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
      using hcomm.symm

/-- If `W` satisfies MS1 (`W.IsMultiplicative`), MS5 and MS6
(`W.IsCompatibleWithTriangulation`), then `W` satisfies MS2: both the left (LMS2) and the right
(RMS2) Ore conditions hold. -/
@[stacks 05R3 "(2)"]
theorem isCompatibleWithTriangulation_oreConditions
    {C : Type u} [Category.{v} C] [HasShift C ℤ] [Preadditive C]
    [Limits.HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] (W : MorphismProperty C)
    [W.IsMultiplicative]
    [W.IsCompatibleWithTriangulation] :
    (∀ ⦃X Y : C⦄ (φ : W.RightFraction X Y),
        ∃ ψ : W.LeftFraction X Y, φ.f ≫ ψ.s = φ.s ≫ ψ.f)
    ∧
    (∀ ⦃X Y : C⦄ (φ : W.LeftFraction X Y),
        ∃ ψ : W.RightFraction X Y, ψ.s ≫ φ.f = ψ.f ≫ φ.s) :=
  ⟨fun _ _ φ => isCompatibleWithTriangulation_lms2 W φ,
   fun _ _ φ => isCompatibleWithTriangulation_rms2 W φ⟩

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-!
### The objects killed by a localization functor

Let `S` be a multiplicative system of a pre-triangulated category `𝒟`, compatible with the
triangulated structure, and let `Q : 𝒟 ⥤ 𝒟_S` be a localization functor for `S`. For an object
`Z` of `𝒟`, the following are equivalent: `Q.obj Z` is zero (`Cond1`); some zero morphism
`Z ⟶ Z'` lies in `S` (`Cond2`); some zero morphism `Z' ⟶ Z` lies in `S` (`Cond3`); some
`Z ⊞ Z'` is the third object of a distinguished triangle whose first morphism lies in `S`
(`Cond4`). When `S` is saturated, they are also equivalent to: the morphism `0 ⟶ Z` from a zero
object lies in `S` (`Cond5`); the morphism `Z ⟶ 0` to a zero object lies in `S` (`Cond6`); `Z` is
the third object of a distinguished triangle whose first morphism lies in `S` (`Cond7`).
-/

namespace StacksLocalizationKernel

variable {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟]
  [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

/-- Condition (1): the image `Q(Z)` is a zero object of `S⁻¹𝒟`. -/
@[sga "4½ Etat_0 2.2"]
def Cond1 {𝒟_S : Type*} [Category 𝒟_S] (Q : 𝒟 ⥤ 𝒟_S) (Z : 𝒟) : Prop :=
  IsZero (Q.obj Z)

/-- Condition (2): the zero morphism `Z ⟶ Z'` lies in `S` for some target `Z'`. -/
def Cond2 (S : MorphismProperty 𝒟) (Z : 𝒟) : Prop :=
  ∃ Z' : 𝒟, S (0 : Z ⟶ Z')

/-- Condition (3): the zero morphism `Z' ⟶ Z` lies in `S` for some source `Z'`. -/
def Cond3 (S : MorphismProperty 𝒟) (Z : 𝒟) : Prop :=
  ∃ Z' : 𝒟, S (0 : Z' ⟶ Z)

/-- Condition (4): a distinguished triangle `X → Y → Z ⊞ Z' → X⟦1⟧` with first map in `S`. -/
def Cond4 (S : MorphismProperty 𝒟) (Z : 𝒟) : Prop :=
  ∃ (Z' X Y : 𝒟) (f : X ⟶ Y) (g : Y ⟶ Z ⊞ Z')
    (h : (Z ⊞ Z') ⟶ (shiftFunctor 𝒟 (1 : ℤ)).obj X),
    Triangle.mk f g h ∈ distinguishedTriangles ∧ S f

/-- Condition (5): the unique morphism `O ⟶ Z` from some zero object `O` lies in `S`. -/
def Cond5 (S : MorphismProperty 𝒟) (Z : 𝒟) : Prop :=
  ∃ O : 𝒟, IsZero O ∧ S (0 : O ⟶ Z)

/-- Condition (6): the unique morphism `Z ⟶ O` to some zero object `O` lies in `S`. -/
def Cond6 (S : MorphismProperty 𝒟) (Z : 𝒟) : Prop :=
  ∃ O : 𝒟, IsZero O ∧ S (0 : Z ⟶ O)

/-- Condition (7): a distinguished triangle `X → Y → Z → X⟦1⟧` with first map in `S`. -/
def Cond7 (S : MorphismProperty 𝒟) (Z : 𝒟) : Prop :=
  ∃ (X Y : 𝒟) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ (shiftFunctor 𝒟 (1 : ℤ)).obj X),
    Triangle.mk f g h ∈ distinguishedTriangles ∧ S f

section SubLemmas

variable (S : MorphismProperty 𝒟)
  {𝒟_S : Type*} [Category 𝒟_S] (Q : 𝒟 ⥤ 𝒟_S) [Q.IsLocalization S] (Z : 𝒟)

omit [HasShift 𝒟 ℤ] in
omit [HasZeroObject 𝒟] [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If `Q.obj Z` is zero, then some zero morphism `Z' ⟶ Z` lies in `S`. -/
lemma A_one_imp_three (hR : S.HasRightCalculusOfFractions)
    (hL : S.HasLeftCalculusOfFractions) :
    Cond1 Q Z → Cond3 S Z := by
  intro hZ
  let : Preadditive 𝒟_S := Localization.preadditive Q S
  let : Q.Additive := Localization.functor_additive Q S
  have hmap : Q.map (𝟙 Z) = Q.map (0 : Z ⟶ Z) := hZ.eq_of_src _ _
  rw [MorphismProperty.map_eq_iff_precomp Q S (𝟙 Z) (0 : Z ⟶ Z)] at hmap
  obtain ⟨Z', s, hs, heq⟩ := hmap
  rw [Category.comp_id, comp_zero] at heq
  exact ⟨Z', heq ▸ hs⟩

omit [HasShift 𝒟 ℤ] in
omit [HasZeroObject 𝒟] [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If `Q.obj Z` is zero, then some zero morphism `Z ⟶ Z'` lies in `S`. -/
lemma A_one_imp_two (hL : S.HasLeftCalculusOfFractions) :
    Cond1 Q Z → Cond2 S Z := by
  intro hZ
  let : Preadditive 𝒟_S := Localization.preadditive Q S
  let : Q.Additive := Localization.functor_additive Q S
  have hmap : Q.map (𝟙 Z) = Q.map (0 : Z ⟶ Z) := hZ.eq_of_src _ _
  rw [MorphismProperty.map_eq_iff_postcomp Q S (𝟙 Z) (0 : Z ⟶ Z)] at hmap
  obtain ⟨Z', s, hs, heq⟩ := hmap
  rw [Category.id_comp, zero_comp] at heq
  exact ⟨Z', heq ▸ hs⟩

omit [HasShift 𝒟 ℤ] in
omit [HasZeroObject 𝒟] [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If some zero morphism `Z ⟶ Z'` lies in `S`, then `Q.obj Z` is zero. -/
lemma A_two_imp_one (hL : S.HasLeftCalculusOfFractions) :
    Cond2 S Z → Cond1 Q Z := by
  rintro ⟨Z', h⟩
  let : Preadditive 𝒟_S := Localization.preadditive Q S
  let : Q.Additive := Localization.functor_additive Q S
  let e : Q.obj Z ≅ Q.obj Z' := Localization.isoOfHom Q S (0 : Z ⟶ Z') h
  have hhom : e.hom = 0 := Q.map_zero Z Z'
  change IsZero (Q.obj Z)
  rw [IsZero.iff_id_eq_zero, ← e.hom_inv_id, hhom, zero_comp]

omit [HasShift 𝒟 ℤ] in
omit [HasZeroObject 𝒟] [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If some zero morphism `Z' ⟶ Z` lies in `S`, then `Q.obj Z` is zero. -/
lemma A_three_imp_one (hL : S.HasLeftCalculusOfFractions) :
    Cond3 S Z → Cond1 Q Z := by
  rintro ⟨Z', h⟩
  let : Preadditive 𝒟_S := Localization.preadditive Q S
  let : Q.Additive := Localization.functor_additive Q S
  let e : Q.obj Z' ≅ Q.obj Z := Localization.isoOfHom Q S (0 : Z' ⟶ Z) h
  have hhom : e.hom = 0 := Q.map_zero Z' Z
  change IsZero (Q.obj Z)
  rw [IsZero.iff_id_eq_zero, ← e.inv_hom_id, hhom, comp_zero]

/-- If some zero morphism `Z ⟶ Z'` lies in `S`, then some `Z ⊞ Z''` is the third object of a
distinguished triangle whose first morphism lies in `S`. -/
lemma A_two_imp_four (hcompat : S.IsCompatibleWithTriangulation) :
    Cond2 S Z → Cond4 S Z := by
  rintro ⟨W, hf⟩
  let W' := (shiftFunctor 𝒟 (-1:ℤ)).obj W
  have hBdist : binaryBiproductTriangle W' Z ∈ distinguishedTriangles :=
    binaryBiproductTriangle_distinguished W' Z
  have hIR : (binaryBiproductTriangle W' Z).invRotate ∈ distinguishedTriangles :=
    inv_rot_of_distTriang _ hBdist
  have hmor1 : (binaryBiproductTriangle W' Z).invRotate.mor₁ = 0 := by
    simp [Triangle.invRotate, binaryBiproductTriangle, Triangle.mk]
  have hSmor1 : S ((binaryBiproductTriangle W' Z).invRotate.mor₁) := by
    rw [hmor1]
    change S (0 : (shiftFunctor 𝒟 (-1:ℤ)).obj Z ⟶ (shiftFunctor 𝒟 (-1:ℤ)).obj W)
    have hcond := hcompat.toIsCompatibleWithShift.condition (-1 : ℤ)
    rw [show (0 : (shiftFunctor 𝒟 (-1:ℤ)).obj Z ⟶ (shiftFunctor 𝒟 (-1:ℤ)).obj W)
        = (shiftFunctor 𝒟 (-1:ℤ)).map (0 : Z ⟶ W) from (Functor.map_zero _ _ _).symm]
    change S.inverseImage (shiftFunctor 𝒟 (-1:ℤ)) (0 : Z ⟶ W)
    rw [hcond]; exact hf
  refine ⟨W', (binaryBiproductTriangle W' Z).invRotate.obj₁,
    (binaryBiproductTriangle W' Z).invRotate.obj₂,
    (binaryBiproductTriangle W' Z).invRotate.mor₁,
    (binaryBiproductTriangle W' Z).invRotate.mor₂ ≫ (biprod.braiding W' Z).hom,
    (biprod.braiding Z W').hom ≫ (binaryBiproductTriangle W' Z).invRotate.mor₃, ?_, hSmor1⟩
  apply isomorphic_distinguished _ hIR
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (biprod.braiding Z W') ?_ ?_ ?_ <;>
    simp [biprod.braiding, Triangle.invRotate, binaryBiproductTriangle, Triangle.mk]

/-- If a distinguished triangle has first morphism in `S`, then `Q` kills its third object. -/
private lemma isZero_obj_of_distinguished_of_mem (hL : S.HasLeftCalculusOfFractions)
    (hcompat : S.IsCompatibleWithTriangulation) {X Y Z' : 𝒟} {f : X ⟶ Y} {g : Y ⟶ Z'}
    {h : Z' ⟶ (shiftFunctor 𝒟 (1 : ℤ)).obj X} (hdist : Triangle.mk f g h ∈ distinguishedTriangles)
    (hf : S f) : IsZero (Q.obj Z') := by
  have := hL
  have := hcompat
  have : S.IsCompatibleWithShift ℤ := hcompat.toIsCompatibleWithShift
  let : HasShift 𝒟_S ℤ := HasShift.localized Q S ℤ
  let : Q.CommShift ℤ := Functor.CommShift.localized Q S ℤ
  let : Preadditive 𝒟_S := Localization.preadditive Q S
  let : Q.Additive := Localization.functor_additive Q S
  have : Q.EssSurj := Localization.essSurj Q S
  let : HasZeroObject 𝒟_S := Q.hasZeroObject_of_additive
  let : ∀ n : ℤ, (shiftFunctor 𝒟_S n).Additive := fun n => by
    rw [Localization.functor_additive_iff Q S]
    exact Functor.additive_of_iso (Q.commShiftIso n)
  let : Pretriangulated 𝒟_S := Triangulated.Localization.pretriangulated Q S
  have : Q.IsTriangulated := Triangulated.Localization.isTriangulated_functor Q S
  exact (Triangle.isZero₃_iff_isIso₁ _ (Q.map_distinguished _ hdist)).mpr
    (Localization.inverts Q S f hf)

/-- If some `Z ⊞ Z'` is the third object of a distinguished triangle whose first morphism lies
in `S`, then `Q.obj Z` is zero. -/
lemma A_four_imp_one (hL : S.HasLeftCalculusOfFractions)
    (hcompat : S.IsCompatibleWithTriangulation) : Cond4 S Z → Cond1 Q Z := by
  rintro ⟨Z', X, Y, f, g, h, hdist, hf⟩
  let : Preadditive 𝒟_S := Localization.preadditive Q S
  let : Q.Additive := Localization.functor_additive Q S
  exact (isZero_obj_of_distinguished_of_mem S Q hL hcompat hdist hf).of_mono
    (Q.map (biprod.inl : Z ⟶ Z ⊞ Z'))

/-- If `S` is saturated and `O` is a zero object, the composite `O ⟶ Z ⟶ O` of zero morphisms
lies in `S`. -/
private lemma zero_comp_zero_mem {C : Type*} [Category C] [Preadditive C]
    (S : MorphismProperty C) (Z : C) (hsat : S.IsSaturatedMultiplicative) {O : C}
    (hO : IsZero O) : S ((0 : O ⟶ Z) ≫ (0 : Z ⟶ O)) := by
  have : S.ContainsIdentities := hsat.toIsMultiplicative.toContainsIdentities
  rw [zero_comp, hO.eq_of_src 0 (𝟙 O)]
  exact S.id_mem O

omit [HasShift 𝒟 ℤ] in
omit [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If `S` is saturated and some zero morphism `Z ⟶ Z'` lies in `S`, then so does the morphism
`Z ⟶ O` to some zero object `O`. -/
lemma B_two_imp_six (hsat : S.IsSaturatedMultiplicative) :
    Cond2 S Z → Cond6 S Z := by
  rintro ⟨Z', hZ'⟩
  obtain ⟨O, hO⟩ := (inferInstance : HasZeroObject 𝒟).zero
  refine ⟨O, hO, hsat.mem_of_comp_mem_comp (0 : O ⟶ Z) (0 : Z ⟶ O) (0 : O ⟶ Z')
    (zero_comp_zero_mem S Z hsat hO) ?_⟩
  rw [zero_comp]; exact hZ'

omit [HasShift 𝒟 ℤ] in
omit [HasZeroObject 𝒟] [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If the morphism `Z ⟶ O` to a zero object lies in `S`, then so does a zero morphism out of
`Z`. -/
lemma B_six_imp_two : Cond6 S Z → Cond2 S Z :=
  fun ⟨O, _, hO⟩ => ⟨O, hO⟩

omit [HasShift 𝒟 ℤ] in
omit [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If `S` is saturated and some zero morphism `Z' ⟶ Z` lies in `S`, then so does the morphism
`O ⟶ Z` from some zero object `O`. -/
lemma B_three_imp_five (hsat : S.IsSaturatedMultiplicative) :
    Cond3 S Z → Cond5 S Z := by
  rintro ⟨Z', hZ'⟩
  obtain ⟨O, hO⟩ := (inferInstance : HasZeroObject 𝒟).zero
  refine ⟨O, hO, hsat.mem_of_comp_mem_comp (0 : Z' ⟶ O) (0 : O ⟶ Z) (0 : Z ⟶ O) ?_
    (zero_comp_zero_mem S Z hsat hO)⟩
  rw [zero_comp]; exact hZ'

omit [HasShift 𝒟 ℤ] in
omit [HasZeroObject 𝒟] [∀ (n : ℤ), (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] in
/-- If the morphism `O ⟶ Z` from a zero object lies in `S`, then so does a zero morphism into
`Z`. -/
lemma B_five_imp_three : Cond5 S Z → Cond3 S Z :=
  fun ⟨O, _, hO⟩ => ⟨O, hO⟩

/-- If `S` is saturated and `Q.obj Z` is zero, then `Z` is the third object of a distinguished
triangle whose first morphism lies in `S`. -/
lemma B_one_imp_seven (hL : S.HasLeftCalculusOfFractions)
    (hR : S.HasRightCalculusOfFractions) (hsat : S.IsSaturatedMultiplicative) :
    Cond1 Q Z → Cond7 S Z := by
  intro hZ
  have h3 : Cond3 S Z := A_one_imp_three S Q Z hR hL hZ
  obtain ⟨O, hO, hf⟩ := B_three_imp_five S Z hsat h3
  set T₀ : Triangle 𝒟 := (contractibleTriangle Z).invRotate with hT₀def
  have hT₀ : T₀ ∈ distinguishedTriangles :=
    inv_rot_of_distTriang _ (contractible_distinguished Z)
  have hzero₁ : IsZero T₀.obj₁ := by
    change IsZero ((shiftFunctor 𝒟 (-1 : ℤ)).obj (contractibleTriangle Z).obj₃)
    exact Functor.map_isZero (shiftFunctor 𝒟 (-1)) (isZero_zero 𝒟)
  refine ⟨O, Z, (0 : O ⟶ Z), (𝟙 Z), (0 : Z ⟶ (shiftFunctor 𝒟 (1 : ℤ)).obj O), ?_, hf⟩
  refine isomorphic_distinguished _ hT₀ _ ?_
  refine Triangle.isoMk _ _ (hO.iso hzero₁) (Iso.refl Z) (Iso.refl Z) ?_ ?_ ?_
  · apply hO.eq_of_src
  · rfl
  · apply (Functor.map_isZero (shiftFunctor 𝒟 (1 : ℤ)) hzero₁).eq_of_tgt

/-- If `Z` is the third object of a distinguished triangle whose first morphism lies in `S`, then
`Q.obj Z` is zero. -/
lemma B_seven_imp_one (hL : S.HasLeftCalculusOfFractions)
    (hcompat : S.IsCompatibleWithTriangulation) : Cond7 S Z → Cond1 Q Z := by
  rintro ⟨X, Y, f, g, h, hdist, hf⟩
  exact isZero_obj_of_distinguished_of_mem S Q hL hcompat hdist hf

end SubLemmas

/-- Let `S` be a multiplicative system compatible with the triangulated structure and `Q` a
localization functor for `S`. For an object `Z`, the conditions `Cond1` to `Cond4` are
equivalent. -/
@[stacks 05R8 "(1)-(4)"]
theorem statementA
    (S : MorphismProperty 𝒟)
    {𝒟_S : Type*} [Category 𝒟_S] (Q : 𝒟 ⥤ 𝒟_S) [Q.IsLocalization S]
    (Z : 𝒟)
    (hL : S.HasLeftCalculusOfFractions)
    (hR : S.HasRightCalculusOfFractions) (hcompat : S.IsCompatibleWithTriangulation) :
    [Cond1 Q Z, Cond2 S Z, Cond3 S Z, Cond4 S Z].TFAE := by
  tfae_have 1 → 2 := A_one_imp_two S Q Z hL
  tfae_have 2 → 1 := A_two_imp_one S Q Z hL
  tfae_have 1 → 3 := A_one_imp_three S Q Z hR hL
  tfae_have 3 → 1 := A_three_imp_one S Q Z hL
  tfae_have 2 → 4 := A_two_imp_four S Z hcompat
  tfae_have 4 → 1 := A_four_imp_one S Q Z hL hcompat
  tfae_finish

/-- Let `S` be a saturated multiplicative system compatible with the triangulated structure and
`Q` a localization functor for `S`. For an object `Z`, the conditions `Cond1` to `Cond7` are
equivalent. -/
@[stacks 05R8 "(5)-(7)"]
theorem statementB
    (S : MorphismProperty 𝒟)
    {𝒟_S : Type*} [Category 𝒟_S] (Q : 𝒟 ⥤ 𝒟_S) [Q.IsLocalization S]
    (Z : 𝒟)
    (hL : S.HasLeftCalculusOfFractions)
    (hR : S.HasRightCalculusOfFractions) (hcompat : S.IsCompatibleWithTriangulation)
    (hsat : S.IsSaturatedMultiplicative) :
    [Cond1 Q Z, Cond2 S Z, Cond3 S Z, Cond4 S Z,
     Cond5 S Z, Cond6 S Z, Cond7 S Z].TFAE := by
  tfae_have 1 → 2 := A_one_imp_two S Q Z hL
  tfae_have 2 → 1 := A_two_imp_one S Q Z hL
  tfae_have 1 → 3 := A_one_imp_three S Q Z hR hL
  tfae_have 3 → 1 := A_three_imp_one S Q Z hL
  tfae_have 2 → 4 := A_two_imp_four S Z hcompat
  tfae_have 4 → 1 := A_four_imp_one S Q Z hL hcompat
  tfae_have 2 → 6 := B_two_imp_six S Z hsat
  tfae_have 6 → 2 := B_six_imp_two S Z
  tfae_have 3 → 5 := B_three_imp_five S Z hsat
  tfae_have 5 → 3 := B_five_imp_three S Z
  tfae_have 1 → 7 := B_one_imp_seven S Q Z hL hR hsat
  tfae_have 7 → 1 := B_seven_imp_one S Q Z hL hcompat
  tfae_finish

end StacksLocalizationKernel

end

end
