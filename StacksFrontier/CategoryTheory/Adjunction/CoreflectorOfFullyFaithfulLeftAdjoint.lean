module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# A coreflector built from a fully faithful left adjoint

Let `G ⊣ R` be an adjunction `G : D ⥤ C`, `R : C ⥤ D` whose unit is an isomorphism, so that
`G` is fully faithful and `T = G ⋙ R`-conjugate `R ⋙ G` is an idempotent comonad on `C`.  Let
`P ≤ L` be two properties of objects of `C` such that

* `G (R F)` satisfies `P` whenever `F` satisfies `L`, and
* the counit `G (R M) ⟶ M` is an isomorphism whenever `M` satisfies `P`.

Then `F ↦ G (R F)` is a right adjoint of the inclusion `P ⊆ L`, whose counit at `F` is the counit
`G (R F) ⟶ F` of `G ⊣ R`; its composite with the inclusion is the identity of `P`.

This is the shape of **Stacks 0778** read through **Stacks 07B1** (2)(c): for an algebraic
stack `𝒳`, `C = Mod(𝒪_𝒳)`, `R = g^*` the restriction to the flat-fppf site, `G = g_!` its left
adjoint (**Stacks 07AS**, with `g^* g_! = id` by **Stacks 0789**), `P = QCoh(𝒪_𝒳)` and
`L = LQCoh^fbc(𝒪_𝒳)`; the coherator is `Q = g_! g^*`.  The kernel of the coreflector is the
kernel of `R` (`CategoryTheory.ObjectProperty.isZero_coreflectorOfLeftAdjoint_obj_iff`), which for
`R = g^*` is the class of parasitic modules (**Stacks 0779** (1)), and `R` inverts the counit
(`CategoryTheory.ObjectProperty.isIso_map_counit_of_isIso_unit`), so that for an exact `R` the
kernel and the cokernel of the counit are killed by `R` (**Stacks 0779** (2)).

## Main definitions

* `CategoryTheory.ObjectProperty.coreflectorOfLeftAdjoint`: the functor
  `L.FullSubcategory ⥤ P.FullSubcategory`, `F ↦ G (R F)`.
* `CategoryTheory.ObjectProperty.coreflectorOfLeftAdjointAdjunction`: the adjunction
  `P.ιOfLE hPL ⊣ coreflectorOfLeftAdjoint G R P L hA`.
* `CategoryTheory.ObjectProperty.coreflectorOfLeftAdjointCompIso`: the composite of the inclusion
  with the coreflector is the identity.

## Main results

* `CategoryTheory.ObjectProperty.coreflectorOfLeftAdjointAdjunction_counit_app_hom`: the counit
  of the new adjunction is the counit of `G ⊣ R`.
* `CategoryTheory.ObjectProperty.isZero_coreflectorOfLeftAdjoint_obj_iff`: the kernel of the
  coreflector is the kernel of `R`.
* `CategoryTheory.ObjectProperty.isIso_map_counit_of_isIso_unit`: `R` inverts every component of
  the counit of `G ⊣ R`.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 07B1](https://stacks.math.columbia.edu/tag/07B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Functor

variable (G : D ⥤ C) (R : C ⥤ D) (P L : ObjectProperty C)
  (hA : ∀ F, L F → P (G.obj (R.obj F)))

/-- **The coreflector `F ↦ G (R F)`** from `L` to `P`, for a pair of functors `G`, `R` such that
`G (R F)` satisfies `P` whenever `F` satisfies `L`. -/
def coreflectorOfLeftAdjoint : L.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (L.ι ⋙ R ⋙ G) fun F => hA _ F.2

/-- The underlying object of the coreflector at `F` is `G (R F)`. -/
@[simp]
lemma coreflectorOfLeftAdjoint_obj_obj (F : L.FullSubcategory) :
    ((coreflectorOfLeftAdjoint G R P L hA).obj F).obj = G.obj (R.obj F.obj) :=
  rfl

/-- The underlying morphism of the coreflector applied to `f` is `G (R f)`. -/
@[simp]
lemma coreflectorOfLeftAdjoint_map_hom {F F' : L.FullSubcategory} (f : F ⟶ F') :
    ((coreflectorOfLeftAdjoint G R P L hA).map f).hom = G.map (R.map f.hom) :=
  rfl

/-- The coreflector followed by the inclusion of `P` is `R ⋙ G` on `L`. -/
def coreflectorOfLeftAdjointCompιIso :
    coreflectorOfLeftAdjoint G R P L hA ⋙ P.ι ≅ L.ι ⋙ R ⋙ G :=
  Iso.refl _

end Functor

variable {G : D ⥤ C} {R : C ⥤ D} (adj : G ⊣ R)

/-- For an adjunction with invertible unit, `R` of the counit at `F` is the inverse of the unit at
`R F`. -/
private theorem map_counit_eq_inv_unit [IsIso adj.unit] (F : C) :
    R.map (adj.counit.app F) = inv (adj.unit.app (R.obj F)) := by
  rw [← cancel_epi (adj.unit.app (R.obj F)), adj.right_triangle_components F, IsIso.hom_inv_id]
  rfl

/-- **`R` inverts the counit** of an adjunction `G ⊣ R` with invertible unit. -/
theorem isIso_map_counit_of_isIso_unit [IsIso adj.unit] (F : C) :
    IsIso (R.map (adj.counit.app F)) := by
  rw [map_counit_eq_inv_unit adj]
  infer_instance

/-- For an adjunction with invertible unit, `G` applied to `R` of the counit at `F` is the
counit at `G (R F)`. -/
theorem map_map_counit_eq_counit_app [IsIso adj.unit] (F : C) :
    G.map (R.map (adj.counit.app F)) = adj.counit.app (G.obj (R.obj F)) := by
  rw [map_counit_eq_inv_unit adj, Functor.map_inv,
    ← cancel_epi (G.map (adj.unit.app (R.obj F))), IsIso.hom_inv_id,
    adj.left_triangle_components (R.obj F)]
  rfl

/-- The map `ψ ↦ ε_M⁻¹ ≫ G (R ψ)`, for `M` at which the counit is invertible. -/
def coreflectorOfLeftAdjointLift {M F : C} (hM : IsIso (adj.counit.app M)) (ψ : M ⟶ F) :
    M ⟶ G.obj (R.obj F) :=
  (@asIso _ _ _ _ (adj.counit.app M) hM).inv ≫ G.map (R.map ψ)

/-- The lift of `ψ : M ⟶ F` followed by the counit at `F` is `ψ`. -/
theorem coreflectorOfLeftAdjointLift_comp_counit {M F : C} (hM : IsIso (adj.counit.app M))
    (ψ : M ⟶ F) : coreflectorOfLeftAdjointLift adj hM ψ ≫ adj.counit.app F = ψ := by
  have hn := adj.counit.naturality ψ
  dsimp at hn
  rw [coreflectorOfLeftAdjointLift, Category.assoc, hn]
  exact (@asIso _ _ _ _ (adj.counit.app M) hM).inv_hom_id_assoc ψ

/-- The lift of `ψ ≫ f` is the lift of `ψ` followed by `G (R f)`. -/
theorem coreflectorOfLeftAdjointLift_comp {M F F' : C} (hM : IsIso (adj.counit.app M))
    (ψ : M ⟶ F) (f : F ⟶ F') :
    coreflectorOfLeftAdjointLift adj hM (ψ ≫ f) =
      coreflectorOfLeftAdjointLift adj hM ψ ≫ G.map (R.map f) := by
  simp [coreflectorOfLeftAdjointLift]

variable [IsIso adj.unit] {P L : ObjectProperty C} (hPL : P ≤ L)
  (hA : ∀ F, L F → P (G.obj (R.obj F)))
  (hB : ∀ M, P M → IsIso (adj.counit.app M))

/-- For an adjunction with invertible unit, the lift of `φ ≫ ε_F` is `φ`, for every
`φ : M ⟶ G (R F)`. -/
theorem coreflectorOfLeftAdjointLift_counit_comp {M F : C} (hM : IsIso (adj.counit.app M))
    (φ : M ⟶ G.obj (R.obj F)) :
    coreflectorOfLeftAdjointLift adj hM (φ ≫ adj.counit.app F) = φ := by
  have hn := adj.counit.naturality φ
  dsimp at hn
  rw [coreflectorOfLeftAdjointLift, Functor.map_comp, Functor.map_comp,
    map_map_counit_eq_counit_app adj, hn]
  exact (@asIso _ _ _ _ (adj.counit.app M) hM).inv_hom_id_assoc φ

/-- The bijection `Hom_L(M, F) ≃ Hom_P(M, G (R F))` underlying the coreflection: a map
`M ⟶ G (R F)` is composed with the counit at `F`, and a map `ψ : M ⟶ F` is sent to
`ε_M⁻¹ ≫ G (R ψ)`. -/
def coreflectorOfLeftAdjointHomEquiv (M : P.FullSubcategory) (F : L.FullSubcategory) :
    ((ιOfLE hPL).obj M ⟶ F) ≃ (M ⟶ (coreflectorOfLeftAdjoint G R P L hA).obj F) where
  toFun ψ := homMk (coreflectorOfLeftAdjointLift adj (hB M.obj M.2) ψ.hom)
  invFun φ := homMk ((φ.hom : M.obj ⟶ G.obj (R.obj F.obj)) ≫ adj.counit.app F.obj)
  left_inv ψ := InducedCategory.hom_ext
    (coreflectorOfLeftAdjointLift_comp_counit adj (hB M.obj M.2) ψ.hom)
  right_inv φ := InducedCategory.hom_ext
    (coreflectorOfLeftAdjointLift_counit_comp adj (hB M.obj M.2) φ.hom)

/-- **The coreflection of Stacks 0778**, abstractly: `F ↦ G (R F)` is right adjoint to the
inclusion `P ⊆ L`. -/
def coreflectorOfLeftAdjointAdjunction :
    ιOfLE hPL ⊣ coreflectorOfLeftAdjoint G R P L hA :=
  Adjunction.mkOfHomEquiv
    { homEquiv := coreflectorOfLeftAdjointHomEquiv adj hPL hA hB
      homEquiv_naturality_left_symm := by
        intro M M' F f g
        exact InducedCategory.hom_ext (Category.assoc _ _ _)
      homEquiv_naturality_right := by
        intro M F F' f g
        exact InducedCategory.hom_ext
          (coreflectorOfLeftAdjointLift_comp adj (hB M.obj M.2) f.hom g.hom) }

/-- The counit of the coreflection at `F` is the counit `G (R F) ⟶ F` of `G ⊣ R`. -/
@[simp]
theorem coreflectorOfLeftAdjointAdjunction_counit_app_hom (F : L.FullSubcategory) :
    ((coreflectorOfLeftAdjointAdjunction adj hPL hA hB).counit.app F).hom =
      adj.counit.app F.obj := by
  change 𝟙 _ ≫ adj.counit.app F.obj = _
  exact Category.id_comp _

/-- **The coreflector fixes `P`**: its composite with the inclusion is the identity. -/
def coreflectorOfLeftAdjointCompIso :
    ιOfLE hPL ⋙ coreflectorOfLeftAdjoint G R P L hA ≅ 𝟭 P.FullSubcategory :=
  (asIso (coreflectorOfLeftAdjointAdjunction adj hPL hA hB).unit).symm

include adj in
/-- **The kernel of the coreflector is the kernel of `R`.** -/
theorem isZero_coreflectorOfLeftAdjoint_obj_iff [Preadditive C] [Preadditive D]
    [G.PreservesZeroMorphisms] [R.PreservesZeroMorphisms] (F : L.FullSubcategory) :
    IsZero ((coreflectorOfLeftAdjoint G R P L hA).obj F) ↔ IsZero (R.obj F.obj) := by
  have e : ∀ X : P.FullSubcategory, IsZero X ↔ IsZero X.obj := fun X => by
    rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero]
    exact ⟨fun h => congrArg InducedCategory.Hom.hom h,
      fun h => InducedCategory.hom_ext h⟩
  rw [e, coreflectorOfLeftAdjoint_obj_obj]
  refine ⟨fun h => ?_, fun h => G.map_isZero h⟩
  exact (R.map_isZero h).of_iso (asIso (adj.unit.app (R.obj F.obj)))

end CategoryTheory.ObjectProperty
