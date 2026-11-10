module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Yoneda

/-!
# The invertibility locus of an adjoint transpose is a triangulated subcategory

Let `C`, `D₁` and `D₂` be pretriangulated categories, let `S₁ : C ⥤ D₁` and `S₂ : C ⥤ D₂` be
functors, let `G : D₁ ⥤ D₂` be an additive functor with a left adjoint `F`, and let
`ψ : S₂ ⟶ S₁ ⋙ G` be a natural transformation. Its adjoint transpose at `X` is a morphism
`F (S₂ X) ⟶ S₁ X`, and this file studies the objects `X` at which that transpose is invertible.

By the Yoneda lemma the transpose at `X` is invertible exactly when, for every object `Y` of
`D₁`, the map `h ↦ ψ_X ≫ G h` from `S₁ X ⟶ Y` to `S₂ X ⟶ G Y` is bijective. That reformulation
involves `ψ` and `G` only, and it makes the locus accessible to a five-lemma argument on the
long exact sequences of morphism groups out of a distinguished triangle. What that argument uses
of `S₁` and `S₂` is very little:

* each of them carries the first two morphisms of a distinguished triangle to the first two
  morphisms of *some* distinguished triangle (`CategoryTheory.Functor.IsWeaklyTriangulated`) —
  no commutation with the translation is asked for, because the squares of the five lemma that
  involve the third morphism of a triangle commute by the naturality of `ψ` alone;
* and, for every `X`, some isomorphisms `S₁ (X⟦1⟧) ≅ (S₁ X)⟦1⟧` and `S₂ (X⟦1⟧) ≅ (S₂ X)⟦1⟧`
  intertwine `ψ_{X⟦1⟧}` with `ψ_X⟦1⟧` up to one natural isomorphism
  `G (Z⟦1⟧) ≅ (G Z)⟦1⟧`; no coherence of these isomorphisms with the structure of the
  translations is needed either.

Under these two hypotheses the locus is a triangulated subcategory.

## Main definitions

* `CategoryTheory.Functor.IsWeaklyTriangulated`: the first condition above.
* `CategoryTheory.Pretriangulated.transposeMap`: the map `h ↦ ψ_X ≫ G h`.
* `CategoryTheory.Pretriangulated.transposeLocus`: the objects at which all of these maps are
  bijective.

## Main results

* `AddMonoidHom.bijective_of_five`: the five lemma for additive maps.
* `CategoryTheory.Pretriangulated.isIso_homEquiv_symm_iff`: the transpose of `p` is invertible
  exactly when `h ↦ p ≫ G h` is bijective on every morphism group.
* `CategoryTheory.Pretriangulated.transposeLocus_shift_iff`: the locus contains `X⟦1⟧` exactly
  when it contains `X`.
* `CategoryTheory.Pretriangulated.transposeLocus_isTriangulated`: the locus is a triangulated
  subcategory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v₀ v₁ v₂ u₀ u₁ u₂

/-! ### The five lemma for additive maps -/

namespace AddMonoidHom

/-- **The five lemma for additive maps.** In a commutative ladder of additive maps whose two rows
are exact at the second, third and fourth places, the middle vertical map is bijective as soon as
the first is surjective, the second and fourth are bijective and the fifth is injective. -/
theorem bijective_of_five {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup A₄] [AddCommGroup A₅]
    [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃] [AddCommGroup B₄] [AddCommGroup B₅]
    (f₁ : A₁ →+ A₂) (f₂ : A₂ →+ A₃) (f₃ : A₃ →+ A₄) (f₄ : A₄ →+ A₅)
    (g₁ : B₁ →+ B₂) (g₂ : B₂ →+ B₃) (g₃ : B₃ →+ B₄) (g₄ : B₄ →+ B₅)
    (a₁ : A₁ →+ B₁) (a₂ : A₂ →+ B₂) (a₃ : A₃ →+ B₃) (a₄ : A₄ →+ B₄) (a₅ : A₅ →+ B₅)
    (h₁ : ∀ x, a₂ (f₁ x) = g₁ (a₁ x)) (h₂ : ∀ x, a₃ (f₂ x) = g₂ (a₂ x))
    (h₃ : ∀ x, a₄ (f₃ x) = g₃ (a₃ x)) (h₄ : ∀ x, a₅ (f₄ x) = g₄ (a₄ x))
    (hf₁₂ : ∀ x, f₂ (f₁ x) = 0) (hf₃ : ∀ x, f₃ x = 0 → ∃ y, f₂ y = x)
    (hf₄ : ∀ x, f₄ x = 0 → ∃ y, f₃ y = x)
    (hg₂ : ∀ x, g₂ x = 0 → ∃ y, g₁ y = x) (hg₃ : ∀ x, g₃ x = 0 → ∃ y, g₂ y = x)
    (hg₃₄ : ∀ x, g₄ (g₃ x) = 0)
    (ha₁ : Function.Surjective a₁) (ha₂ : Function.Bijective a₂)
    (ha₄ : Function.Bijective a₄) (ha₅ : Function.Injective a₅) :
    Function.Bijective a₃ := by
  refine ⟨(injective_iff_map_eq_zero a₃).2 fun x hx ↦ ?_, fun b ↦ ?_⟩
  · have hfx : f₃ x = 0 := ha₄.1 (by rw [h₃, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := hf₃ x hfx
    obtain ⟨z, hz⟩ := hg₂ _ (by rw [← h₂, hx])
    obtain ⟨w, rfl⟩ := ha₁ z
    obtain rfl : f₁ w = y := ha₂.1 (by rw [h₁, hz])
    exact hf₁₂ w
  · obtain ⟨c, hc⟩ := ha₄.2 (g₃ b)
    obtain ⟨x, rfl⟩ := hf₄ c (ha₅ (by rw [h₄, hc, hg₃₄, map_zero]))
    obtain ⟨y', hy'⟩ := hg₃ (b - a₃ x) (by rw [map_sub, ← h₃, hc, sub_self])
    obtain ⟨y, rfl⟩ := ha₂.2 y'
    exact ⟨x + f₂ y, by rw [map_add, h₂, hy', add_sub_cancel]⟩

end AddMonoidHom

namespace CategoryTheory

/-! ### Weakly triangulated functors -/

namespace Functor

variable {C : Type u₀} [Category.{v₀} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₁} [Category.{v₁} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A functor between pretriangulated categories is *weakly triangulated* if it carries the
first two morphisms of every distinguished triangle to the first two morphisms of some
distinguished triangle. No commutation with the translation is involved: an exact functor is
weakly triangulated, but the converse needs a choice of isomorphisms `S (X⟦1⟧) ≅ (S X)⟦1⟧`
compatible with the third morphisms. -/
def IsWeaklyTriangulated (S : C ⥤ D) : Prop :=
  ∀ T ∈ distTriang C, ∃ δ : S.obj T.obj₃ ⟶ (S.obj T.obj₁)⟦(1 : ℤ)⟧,
    Triangle.mk (S.map T.mor₁) (S.map T.mor₂) δ ∈ distTriang D

variable {S : C ⥤ D}

/-- The images of the first two morphisms of a distinguished triangle compose to zero. -/
theorem IsWeaklyTriangulated.map_comp_eq_zero (hS : S.IsWeaklyTriangulated) (T : Triangle C)
    (hT : T ∈ distTriang C) : S.map T.mor₁ ≫ S.map T.mor₂ = 0 := by
  obtain ⟨δ, hδ⟩ := hS T hT
  exact comp_distTriang_mor_zero₁₂ _ hδ

/-- Morphisms out of the image of the second object of a distinguished triangle that vanish on
the image of the first object factor through the image of the third object. -/
theorem IsWeaklyTriangulated.exists_eq_comp (hS : S.IsWeaklyTriangulated) (T : Triangle C)
    (hT : T ∈ distTriang C) {Y : D} (k : S.obj T.obj₂ ⟶ Y) (hk : S.map T.mor₁ ≫ k = 0) :
    ∃ k' : S.obj T.obj₃ ⟶ Y, S.map T.mor₂ ≫ k' = k := by
  obtain ⟨δ, hδ⟩ := hS T hT
  obtain ⟨k', hk'⟩ := Triangle.yoneda_exact₂ _ hδ k hk
  exact ⟨k', hk'.symm⟩

/-- A weakly triangulated functor carries zero objects to zero objects: it carries the identity
of a zero object, which is the first morphism of a contractible triangle followed by a zero
morphism, to a morphism that composes to zero with the identity. -/
theorem IsWeaklyTriangulated.map_isZero (hS : S.IsWeaklyTriangulated) {Z : C} (hZ : IsZero Z) :
    IsZero (S.obj Z) := by
  have h : S.map (𝟙 Z) ≫ S.map (0 : Z ⟶ 0) = 0 :=
    hS.map_comp_eq_zero _ (contractible_distinguished Z)
  rw [S.map_id, Category.id_comp] at h
  rw [IsZero.iff_id_eq_zero, ← S.map_id, hZ.eq_of_src (𝟙 Z) ((0 : Z ⟶ 0) ≫ 0), S.map_comp, h,
    zero_comp]

end Functor

/-! ### The transpose maps and their bijectivity locus -/

namespace Pretriangulated

section Transpose

variable {C : Type u₀} [Category.{v₀} C] {D₁ : Type u₁} [Category.{v₁} D₁] [Preadditive D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂] [Preadditive D₂]
  {S₁ : C ⥤ D₁} {S₂ : C ⥤ D₂} {G : D₁ ⥤ D₂} [G.Additive] (ψ : S₂ ⟶ S₁ ⋙ G)

/-- The map `h ↦ ψ_X ≫ G h` from `S₁ X ⟶ Y` to `S₂ X ⟶ G Y`. When `G` has a left adjoint `F` it
is the adjoint transpose of postcomposition with the transpose `F (S₂ X) ⟶ S₁ X` of `ψ_X`. -/
def transposeMap (X : C) (Y : D₁) : (S₁.obj X ⟶ Y) →+ (S₂.obj X ⟶ G.obj Y) where
  toFun h := ψ.app X ≫ G.map h
  map_zero' := by simp
  map_add' _ _ := by simp

/-- The transpose map sends `h` to `ψ_X ≫ G h`. -/
@[simp] theorem transposeMap_apply (X : C) (Y : D₁) (h : S₁.obj X ⟶ Y) :
    transposeMap ψ X Y h = ψ.app X ≫ G.map h :=
  rfl

/-- The transpose maps are natural in the object of `C`. -/
theorem transposeMap_naturality {X X' : C} (f : X ⟶ X') {Y : D₁} (h : S₁.obj X' ⟶ Y) :
    transposeMap ψ X Y (S₁.map f ≫ h) = S₂.map f ≫ transposeMap ψ X' Y h := by
  have hψ := ψ.naturality f
  dsimp only [Functor.comp_map] at hψ
  simp only [transposeMap_apply, G.map_comp, ← Category.assoc, hψ]

/-- The transpose maps are natural in the object of `D₁`. -/
theorem transposeMap_comp {X : C} {Y Y' : D₁} (h : S₁.obj X ⟶ Y) (k : Y ⟶ Y') :
    transposeMap ψ X Y' (h ≫ k) = transposeMap ψ X Y h ≫ G.map k := by
  simp [Category.assoc]

/-- **The locus of `ψ`**: the objects `X` of `C` at which every transpose map
`h ↦ ψ_X ≫ G h` is bijective. -/
def transposeLocus : ObjectProperty C :=
  fun X ↦ ∀ Y : D₁, Function.Bijective (transposeMap ψ X Y)

/-- Precomposition with an isomorphism is bijective. -/
private theorem bijective_comp_iso {D : Type*} [Category D] {X X' Y : D} (e : X ≅ X') :
    Function.Bijective (fun h : X' ⟶ Y ↦ e.hom ≫ h) :=
  (Equiv.mk (fun h : X' ⟶ Y ↦ e.hom ≫ h) (fun h ↦ e.inv ≫ h) (fun _ ↦ by simp)
    (fun _ ↦ by simp)).bijective

/-- Postcomposition with an isomorphism is bijective. -/
private theorem bijective_iso_comp {D : Type*} [Category D] {X Y Y' : D} (e : Y ≅ Y') :
    Function.Bijective (fun h : X ⟶ Y ↦ h ≫ e.hom) :=
  (Equiv.mk (fun h : X ⟶ Y ↦ h ≫ e.hom) (fun h ↦ h ≫ e.inv) (fun _ ↦ by simp)
    (fun _ ↦ by simp)).bijective

/-- Bijectivity of a transpose map only depends on the target up to isomorphism. -/
theorem bijective_transposeMap_iff_of_iso (X : C) {Y Y' : D₁} (e : Y ≅ Y') :
    Function.Bijective (transposeMap ψ X Y) ↔ Function.Bijective (transposeMap ψ X Y') := by
  have h : (transposeMap ψ X Y' : _ → _) ∘ (fun h ↦ h ≫ e.hom) =
      (fun m ↦ m ≫ (G.mapIso e).hom) ∘ (transposeMap ψ X Y : _ → _) := by
    funext h
    exact transposeMap_comp ψ h e.hom
  rw [← Function.Bijective.of_comp_iff _ (bijective_iso_comp e), h,
    Function.Bijective.of_comp_iff' (bijective_iso_comp (G.mapIso e))]

/-- The locus is closed under isomorphisms, by the naturality of the transpose maps. -/
instance transposeLocus_isClosedUnderIsomorphisms :
    (transposeLocus ψ).IsClosedUnderIsomorphisms where
  of_iso {X X'} e hX Y := by
    have h : (transposeMap ψ X Y : _ → _) ∘ (fun h ↦ (S₁.mapIso e).hom ≫ h) =
        (fun m ↦ (S₂.mapIso e).hom ≫ m) ∘ (transposeMap ψ X' Y : _ → _) := by
      funext h
      exact transposeMap_naturality ψ e.hom h
    rw [← Function.Bijective.of_comp_iff' (bijective_comp_iso (S₂.mapIso e)), ← h]
    exact (hX Y).comp (bijective_comp_iso (S₁.mapIso e))

omit [Preadditive D₁] [Preadditive D₂] [G.Additive] in
/-- **The Yoneda reformulation.** For an adjunction `F ⊣ G`, the transpose of `p : A ⟶ G B` is
invertible exactly when `h ↦ p ≫ G h` is bijective on every morphism group out of `B`. -/
theorem isIso_homEquiv_symm_iff {F : D₂ ⥤ D₁} (adj : F ⊣ G) {A : D₂} {B : D₁}
    (p : A ⟶ G.obj B) :
    IsIso ((adj.homEquiv A B).symm p) ↔
      ∀ Y : D₁, Function.Bijective (fun h : B ⟶ Y ↦ p ≫ G.map h) := by
  have key : ∀ Y : D₁, (fun h : B ⟶ Y ↦ p ≫ G.map h) =
      (adj.homEquiv A Y) ∘ (fun h ↦ (adj.homEquiv A B).symm p ≫ h) := by
    intro Y
    funext h
    simp [Adjunction.homEquiv_naturality_right]
  simp only [key, Function.Bijective.of_comp_iff' (adj.homEquiv _ _).bijective]
  refine ⟨fun h Y ↦ ?_, fun h ↦ isIso_of_coyoneda_map_bijective _ h⟩
  exact bijective_comp_iso (asIso ((adj.homEquiv A B).symm p))

/-- The transpose of `ψ_X` is invertible exactly when `X` lies in the locus of `ψ`. -/
theorem isIso_homEquiv_symm_app_iff {F : D₂ ⥤ D₁} (adj : F ⊣ G) (X : C) :
    IsIso ((adj.homEquiv _ _).symm (ψ.app X)) ↔ transposeLocus ψ X :=
  isIso_homEquiv_symm_iff adj (ψ.app X)

omit [Preadditive D₁] [Preadditive D₂] [G.Additive] in
/-- Bijectivity of all the maps `h ↦ p ≫ G h` is invariant under conjugating `p` by
isomorphisms of its source and of the object `G` is applied to. -/
theorem forall_bijective_iff_of_eq {A A' : D₂} {B B' : D₁} (p : A ⟶ G.obj B)
    (p' : A' ⟶ G.obj B') (α : A ≅ A') (β : B ≅ B') (h : p = α.hom ≫ p' ≫ G.map β.inv) :
    (∀ Y : D₁, Function.Bijective (fun k : B ⟶ Y ↦ p ≫ G.map k)) ↔
      ∀ Y : D₁, Function.Bijective (fun k : B' ⟶ Y ↦ p' ≫ G.map k) := by
  refine forall_congr' fun Y ↦ ?_
  have e : (fun k : B ⟶ Y ↦ p ≫ G.map k) =
      (fun m ↦ α.hom ≫ m) ∘ (fun k : B' ⟶ Y ↦ p' ≫ G.map k) ∘ (fun k ↦ β.inv ≫ k) := by
    funext k
    simp [h, Category.assoc]
  rw [e, Function.Bijective.of_comp_iff' (bijective_comp_iso α)]
  exact Function.Bijective.of_comp_iff _ (bijective_comp_iso β.symm)

/-- The adjoint transposes of the components of `ψ`, as a natural transformation
`S₂ ⋙ F ⟶ S₁`. -/
@[simps]
def transposeNatTrans {F : D₂ ⥤ D₁} (adj : F ⊣ G) : S₂ ⋙ F ⟶ S₁ where
  app X := (adj.homEquiv _ _).symm (ψ.app X)
  naturality X Y f := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    exact congrArg _ (ψ.naturality f)

/-- The locus of `ψ` is the invertibility locus of its adjoint transpose. -/
theorem transposeLocus_iff_isIso {F : D₂ ⥤ D₁} (adj : F ⊣ G) (X : C) :
    transposeLocus ψ X ↔ IsIso ((transposeNatTrans ψ adj).app X) :=
  (isIso_homEquiv_symm_app_iff ψ adj X).symm

end Transpose

section Triangulated

variable {C : Type u₀} [Category.{v₀} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D₁ : Type u₁} [Category.{v₁} D₁] [Preadditive D₁] [HasZeroObject D₁] [HasShift D₁ ℤ]
  [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [Pretriangulated D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂] [Preadditive D₂] [HasZeroObject D₂] [HasShift D₂ ℤ]
  [∀ n : ℤ, (shiftFunctor D₂ n).Additive] [Pretriangulated D₂]
  {S₁ : C ⥤ D₁} {S₂ : C ⥤ D₂} {G : D₁ ⥤ D₂} [G.Additive] (ψ : S₂ ⟶ S₁ ⋙ G)

/-- The data that make the transpose maps at `X⟦1⟧` and at `X` correspond: isomorphisms
`S₁ (X⟦1⟧) ≅ (S₁ X)⟦1⟧` and `S₂ (X⟦1⟧) ≅ (S₂ X)⟦1⟧` intertwining `ψ_{X⟦1⟧}` and `ψ_X⟦1⟧`, for a
fixed natural isomorphism `e : G (Z⟦1⟧) ≅ (G Z)⟦1⟧`. -/
def ShiftSquare (e : shiftFunctor D₁ (1 : ℤ) ⋙ G ≅ G ⋙ shiftFunctor D₂ (1 : ℤ)) (X : C) :
    Prop :=
  ∃ (c₁ : S₁.obj (X⟦(1 : ℤ)⟧) ≅ (S₁.obj X)⟦(1 : ℤ)⟧)
    (c₂ : S₂.obj (X⟦(1 : ℤ)⟧) ≅ (S₂.obj X)⟦(1 : ℤ)⟧),
    ψ.app (X⟦(1 : ℤ)⟧) ≫ G.map c₁.hom = c₂.hom ≫ (ψ.app X)⟦(1 : ℤ)⟧' ≫ e.inv.app (S₁.obj X)

/-- The translation by `1` is bijective on morphisms, after composing with an isomorphism. -/
private theorem bijective_shift_comp {D : Type*} [Category D] [HasShift D ℤ] {X Y : D} {Z : D}
    (β : Y⟦(1 : ℤ)⟧ ≅ Z) :
    Function.Bijective (fun k : X ⟶ Y ↦ k⟦(1 : ℤ)⟧' ≫ β.hom) :=
  (bijective_iso_comp β).comp
    ⟨(shiftFunctor D (1 : ℤ)).map_injective, (shiftFunctor D (1 : ℤ)).map_surjective⟩

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D₁] [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [Pretriangulated D₁]
  [HasZeroObject D₂] [∀ n : ℤ, (shiftFunctor D₂ n).Additive] [Pretriangulated D₂] in
/-- **The locus is stable under translation by `1`, in both directions**, as soon as the
transpose maps at `X⟦1⟧` and at `X` are intertwined as in `ShiftSquare`. -/
theorem transposeLocus_shift_iff
    (e : shiftFunctor D₁ (1 : ℤ) ⋙ G ≅ G ⋙ shiftFunctor D₂ (1 : ℤ)) {X : C}
    (hX : ShiftSquare ψ e X) :
    transposeLocus ψ (X⟦(1 : ℤ)⟧) ↔ transposeLocus ψ X := by
  obtain ⟨c₁, c₂, hsq⟩ := hX
  let ε : ∀ Y : D₁, (Y⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ Y := fun Y ↦
    (shiftFunctorCompIsoId D₁ (-1 : ℤ) (1 : ℤ) (by norm_num)).app Y
  have key : ∀ Y : D₁, Function.Bijective (transposeMap ψ (X⟦(1 : ℤ)⟧) Y) ↔
      Function.Bijective (transposeMap ψ X (Y⟦(-1 : ℤ)⟧)) := by
    intro Y
    have h : (transposeMap ψ (X⟦(1 : ℤ)⟧) Y : _ → _) ∘
          (fun k : S₁.obj X ⟶ Y⟦(-1 : ℤ)⟧ ↦ c₁.hom ≫ k⟦(1 : ℤ)⟧' ≫ (ε Y).hom) =
        (fun m : S₂.obj X ⟶ G.obj (Y⟦(-1 : ℤ)⟧) ↦
            c₂.hom ≫ m⟦(1 : ℤ)⟧' ≫ ((e.app (Y⟦(-1 : ℤ)⟧)).symm ≪≫ G.mapIso (ε Y)).hom) ∘
          (transposeMap ψ X (Y⟦(-1 : ℤ)⟧) : _ → _) := by
      funext k
      have hn := e.inv.naturality k
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      simp only [Function.comp_apply, transposeMap_apply, Iso.trans_hom, Iso.symm_hom,
        Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      rw [reassoc_of% hsq, ← reassoc_of% hn]
    have hb₁ : Function.Bijective
        (fun k : S₁.obj X ⟶ Y⟦(-1 : ℤ)⟧ ↦ c₁.hom ≫ k⟦(1 : ℤ)⟧' ≫ (ε Y).hom) :=
      (bijective_comp_iso c₁).comp (bijective_shift_comp (ε Y))
    have hb₂ : Function.Bijective
        (fun m : S₂.obj X ⟶ G.obj (Y⟦(-1 : ℤ)⟧) ↦
          c₂.hom ≫ m⟦(1 : ℤ)⟧' ≫ ((e.app (Y⟦(-1 : ℤ)⟧)).symm ≪≫ G.mapIso (ε Y)).hom) :=
      (bijective_comp_iso c₂).comp (bijective_shift_comp _)
    rw [← Function.Bijective.of_comp_iff _ hb₁, h, Function.Bijective.of_comp_iff' hb₂]
  exact ⟨fun h Y ↦ (bijective_transposeMap_iff_of_iso ψ X ((shiftFunctorCompIsoId D₁ (1 : ℤ)
    (-1 : ℤ) (by norm_num)).app Y)).1 ((key _).1 (h _)), fun h Y ↦ (key Y).2 (h _)⟩

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D₁] [∀ n : ℤ, (shiftFunctor D₁ n).Additive] [Pretriangulated D₁]
  [HasZeroObject D₂] [∀ n : ℤ, (shiftFunctor D₂ n).Additive] [Pretriangulated D₂] in
/-- Under the hypotheses of `transposeLocus_shift_iff` at an object isomorphic to each object,
the locus is stable under every translation. -/
theorem transposeLocus_isStableUnderShift
    (e : shiftFunctor D₁ (1 : ℤ) ⋙ G ≅ G ⋙ shiftFunctor D₂ (1 : ℤ))
    (hsq : ∀ X : C, ∃ X' : C, Nonempty (X ≅ X') ∧ ShiftSquare ψ e X') :
    (transposeLocus ψ).IsStableUnderShift ℤ := by
  have hiff : ∀ X : C, transposeLocus ψ (X⟦(1 : ℤ)⟧) ↔ transposeLocus ψ X := by
    intro X
    obtain ⟨X', ⟨i⟩, hX'⟩ := hsq X
    rw [(transposeLocus ψ).prop_iff_of_iso i, (transposeLocus ψ).prop_iff_of_iso
      ((shiftFunctor C (1 : ℤ)).mapIso i)]
    exact transposeLocus_shift_iff ψ e hX'
  have hneg : ∀ X : C, transposeLocus ψ X → transposeLocus ψ (X⟦(-1 : ℤ)⟧) := fun X hX ↦
    (hiff _).1 ((transposeLocus ψ).prop_of_iso
      ((shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by norm_num)).app X).symm hX)
  have hall : ∀ (n : ℤ) (X : C), transposeLocus ψ X → transposeLocus ψ (X⟦n⟧) := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      intro X hX
      exact (transposeLocus ψ).prop_of_iso ((shiftFunctorZero C ℤ).app X).symm hX
    | succ n ih =>
      intro X hX
      exact (transposeLocus ψ).prop_of_iso
        ((shiftFunctorAdd' C (n : ℤ) 1 (n + 1) rfl).app X).symm
        ((hiff _).2 (ih X hX))
    | pred n ih =>
      intro X hX
      exact (transposeLocus ψ).prop_of_iso
        ((shiftFunctorAdd' C (-(n : ℤ)) (-1) (-(n : ℤ) - 1) (by omega)).app X).symm
        (hneg _ (ih X hX))
  exact ⟨fun n ↦ ⟨hall n⟩⟩

/-- **Two out of three for the locus.** If the first and third objects of a distinguished
triangle lie in the locus, and so do the translate of the first and the inverse translate of the
third, then so does the second. This is the five lemma for the long exact sequences of morphism
groups `S₁ (-) ⟶ Y` and `S₂ (-) ⟶ G Y`, whose exactness is what weak triangulatedness gives at
the triangle, its rotation and its inverse rotation, and whose squares commute by the
naturality of `ψ`. -/
theorem transposeLocus_ext₂ (hS₁ : S₁.IsWeaklyTriangulated) (hS₂ : S₂.IsWeaklyTriangulated)
    (T : Triangle C) (hT : T ∈ distTriang C) (h₁ : transposeLocus ψ T.obj₁)
    (h₃ : transposeLocus ψ T.obj₃) (h₁' : transposeLocus ψ (T.obj₁⟦(1 : ℤ)⟧))
    (h₃' : transposeLocus ψ (T.obj₃⟦(-1 : ℤ)⟧)) :
    transposeLocus ψ T.obj₂ := by
  intro Y
  have hR := rot_of_distTriang T hT
  have hI := inv_rot_of_distTriang T hT
  refine AddMonoidHom.bijective_of_five
    (Preadditive.leftComp Y (S₁.map T.mor₃)) (Preadditive.leftComp Y (S₁.map T.mor₂))
    (Preadditive.leftComp Y (S₁.map T.mor₁))
    (Preadditive.leftComp Y (S₁.map T.invRotate.mor₁))
    (Preadditive.leftComp (G.obj Y) (S₂.map T.mor₃))
    (Preadditive.leftComp (G.obj Y) (S₂.map T.mor₂))
    (Preadditive.leftComp (G.obj Y) (S₂.map T.mor₁))
    (Preadditive.leftComp (G.obj Y) (S₂.map T.invRotate.mor₁))
    (transposeMap ψ _ Y) (transposeMap ψ _ Y) (transposeMap ψ _ Y) (transposeMap ψ _ Y)
    (transposeMap ψ _ Y)
    (fun x ↦ transposeMap_naturality ψ _ x) (fun x ↦ transposeMap_naturality ψ _ x)
    (fun x ↦ transposeMap_naturality ψ _ x) (fun x ↦ transposeMap_naturality ψ _ x)
    (fun x ↦ ?_) (fun x hx ↦ hS₁.exists_eq_comp T hT x hx)
    (fun x hx ↦ hS₁.exists_eq_comp _ hI x hx) (fun x hx ↦ hS₂.exists_eq_comp _ hR x hx)
    (fun x hx ↦ hS₂.exists_eq_comp T hT x hx) (fun x ↦ ?_)
    (h₁' Y).2 (h₃ Y) (h₁ Y) (h₃' Y).1
  · change S₁.map T.mor₂ ≫ S₁.map T.mor₃ ≫ x = 0
    rw [← Category.assoc, show S₁.map T.mor₂ ≫ S₁.map T.mor₃ = 0 from
      hS₁.map_comp_eq_zero _ hR, zero_comp]
  · change S₂.map T.invRotate.mor₁ ≫ S₂.map T.mor₁ ≫ x = 0
    rw [← Category.assoc, show S₂.map T.invRotate.mor₁ ≫ S₂.map T.mor₁ = 0 from
      hS₂.map_comp_eq_zero _ hI, zero_comp]

/-- The locus contains the zero objects, as soon as `S₁` and `S₂` are weakly triangulated. -/
theorem transposeLocus_of_isZero (hS₁ : S₁.IsWeaklyTriangulated)
    (hS₂ : S₂.IsWeaklyTriangulated) {Z : C} (hZ : IsZero Z) : transposeLocus ψ Z := fun _ ↦
  ⟨fun _ _ _ ↦ (hS₁.map_isZero hZ).eq_of_src _ _, fun _ ↦ ⟨0, (hS₂.map_isZero hZ).eq_of_src _ _⟩⟩

/-- **The locus of `ψ` is a triangulated subcategory** as soon as `S₁` and `S₂` are weakly
triangulated and the transpose maps at `X⟦1⟧` and at `X` are intertwined for an object `X`
isomorphic to each object. -/
theorem transposeLocus_isTriangulated (hS₁ : S₁.IsWeaklyTriangulated)
    (hS₂ : S₂.IsWeaklyTriangulated)
    (e : shiftFunctor D₁ (1 : ℤ) ⋙ G ≅ G ⋙ shiftFunctor D₂ (1 : ℤ))
    (hsq : ∀ X : C, ∃ X' : C, Nonempty (X ≅ X') ∧ ShiftSquare ψ e X') :
    (transposeLocus ψ).IsTriangulated := by
  have := transposeLocus_isStableUnderShift ψ e hsq
  refine { exists_zero := ⟨0, isZero_zero C, transposeLocus_of_isZero ψ hS₁ hS₂ (isZero_zero C)⟩
           ext₂' := fun T hT h₁ h₃ ↦ ?_ }
  exact (transposeLocus ψ).le_isoClosure _ (transposeLocus_ext₂ ψ hS₁ hS₂ T hT h₁ h₃
    ((transposeLocus ψ).le_shift (1 : ℤ) _ h₁) ((transposeLocus ψ).le_shift (-1 : ℤ) _ h₃))

end Triangulated

end Pretriangulated

end CategoryTheory
