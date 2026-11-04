module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Filtered.FinallySmall

/-!
# Cofiltered limits of schemes with affine transitions at an independent index universe

`Mathlib.AlgebraicGeometry.AffineTransitionLimit` develops inverse limits of schemes with affine
transition morphisms, but every declaration in that file is stated for an index category
`I : Type u` with `[Category.{u} I]`, where `u` is *the same* universe as that of the schemes
`Scheme.{u}`. A statement whose index category lives at a universe independent of the scheme
universe therefore cannot invoke those results directly.

This file removes that coupling. Mathlib's results are recovered for `I : Type uI` with
`[Category.{v} I]` and `D : I ⥤ Scheme.{u}`, at the cost of two hypotheses on `I`:

* `CategoryTheory.LocallySmall.{u} I`: the hom types of `I` are `u`-small;
* `CategoryTheory.InitiallySmall.{u} I`: there is an initial functor into `I` from a `u`-small
  category.

Both are Mathlib notions. The second is exactly the needed cofinality condition: by
`CategoryTheory.initiallySmall_iff_exists_small_weakly_initial_set`, for cofiltered `I` it says
that `I` has a `u`-small weakly initial (that is, cofinal) set of objects. Given the two,
`CategoryTheory.InitiallySmall.fromCofilteredInitialModel` supplies an initial functor
`A ⥤ I` from a `u`-small cofiltered `A`, and `CategoryTheory.Functor.Initial.isLimitWhiskerEquiv`
transports the limit cone to `A`. Mathlib's results apply to the reindexed diagram, and the
conclusions are pushed back along the functor.

## Main results

Each result is Mathlib's statement of the same name with the suffix `_of_initiallySmall`, under
the two extra hypotheses above and with the index universes freed:

* `AlgebraicGeometry.Scheme.nonempty_of_isLimit_of_initiallySmall` (Stacks 01Z2),
* `AlgebraicGeometry.Scheme.compactSpace_of_isLimit_of_initiallySmall` and
  `AlgebraicGeometry.isAffineHom_π_app_of_initiallySmall`,
* `AlgebraicGeometry.exists_map_eq_top_of_initiallySmall`,
* `AlgebraicGeometry.exists_preimage_eq_of_initiallySmall`,
  `AlgebraicGeometry.exists_isAffineOpen_preimage_eq_of_initiallySmall` and
  `AlgebraicGeometry.exists_map_preimage_eq_map_preimage_of_initiallySmall` (Stacks 01Z4),
* `AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit_of_initiallySmall` (Stacks 01Z5),
* `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit_of_initiallySmall` (Stacks 01Z6),
* `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_finite_of_initiallySmall`,
  `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_initiallySmall` and
  `AlgebraicGeometry.Scheme.OpenCover.exists_of_isCofiltered_of_finite_of_initiallySmall`,
* `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isLimit_of_initiallySmall`,
  `AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit_of_initiallySmall`,
  `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit_of_initiallySmall`,
  `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit_of_initiallySmall` and
  `AlgebraicGeometry.preservesLimit_Γ_rightOp_of_initiallySmall`,
* `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_initiallySmall`
  (Stacks 01ZC),
* `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall`.

`CategoryTheory.initiallySmall_of_small_of_locallySmall` discharges the second hypothesis when the
objects of `I` form a `u`-small type.

## Implementation notes

The hypotheses cannot be dropped. `InitiallySmall.{u} I` is a genuine cofinality restriction: for
instance the ordinals `Ordinal.{u}` form a directed preorder no `u`-small subset of which is
cofinal, so `(Ordinal.{u})ᵒᵖ` is not `InitiallySmall.{u}`, and a reindexing of a diagram over it by
a `u`-small cofiltered category does not exist. Accordingly these are stated as hypotheses rather
than discharged.

They are, however, automatic in the situations that arise in practice.
`CategoryTheory.locallySmall_of_thin` gives `LocallySmall.{u} I` for any thin `I` — in particular
for a preorder, or the opposite of one — and `CategoryTheory.locallySmall_of_univLE` gives it
whenever `UnivLE.{v, u}`. `CategoryTheory.initiallySmall_of_essentiallySmall` together with
`CategoryTheory.essentiallySmall_of_small_of_locallySmall` gives `InitiallySmall.{u} I` from
`Small.{u} I` and `LocallySmall.{u} I`. So for an index category that is the opposite of a
`u`-small preorder both hypotheses hold by instance search.

Mathlib's `AlgebraicGeometry.Scheme.nonempty_of_isLimit` assumes only `IsCofilteredOrEmpty I`;
the version here assumes `IsCofiltered I`, which is what
`CategoryTheory.InitiallySmall.fromCofilteredInitialModel` needs.

## References

* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

universe w v uI u

open CategoryTheory Limits CategoryTheory.InitiallySmall

namespace CategoryTheory

/-- A category whose objects form a `w`-small type and whose hom types are `w`-small admits an
initial functor from a `w`-small category, namely an equivalence with a small model. Mathlib has
`CategoryTheory.initiallySmall_of_essentiallySmall` and the instance
`CategoryTheory.essentiallySmall_of_small_of_locallySmall`, but neither the composite nor the
former is an instance, so this is the form in which the hypothesis
`CategoryTheory.InitiallySmall.{w}` is usually discharged.

Note that `CategoryTheory.locallySmall_of_thin` makes `LocallySmall.{w} J` automatic for a thin
`J`, such as a preorder or the opposite of one. -/
public theorem initiallySmall_of_small_of_locallySmall (J : Type uI) [Category.{v} J]
    [Small.{w} J] [LocallySmall.{w} J] : InitiallySmall.{w} J :=
  initiallySmall_of_essentiallySmall J

end CategoryTheory

namespace AlgebraicGeometry

variable {I : Type uI} [Category.{v} I] {S X : Scheme.{u}}
  (D : I ⥤ Scheme.{u}) (c : Cone D)

section

variable [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]

/-! ### Transport of the diagram along the small cofiltered model -/

/-- A limit cone over `D` restricts to a limit cone over the reindexed diagram. -/
private noncomputable def isLimit_whisker_fromCofilteredInitialModel {D : I ⥤ Scheme.{u}}
    (c : Cone D) (hc : IsLimit c) : IsLimit (c.whisker (fromCofilteredInitialModel.{u} I)) :=
  (Functor.Initial.isLimitWhiskerEquiv (fromCofilteredInitialModel.{u} I) c).symm hc

/-- The transition maps of the reindexed diagram are affine. -/
private theorem isAffineHom_map_fromCofilteredInitialModel
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] :
    ∀ {a b : CofilteredInitialModel.{u} I} (g : a ⟶ b),
      IsAffineHom ((fromCofilteredInitialModel.{u} I ⋙ D).map g) := by
  intros; dsimp; infer_instance

/-- The objects of the reindexed diagram are compact. -/
private theorem compactSpace_obj_fromCofilteredInitialModel [∀ i, CompactSpace (D.obj i)] :
    ∀ a, CompactSpace ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
  intro a; dsimp; infer_instance

/-- The objects of the reindexed diagram are quasi-separated. -/
private theorem quasiSeparatedSpace_obj_fromCofilteredInitialModel
    [∀ i, QuasiSeparatedSpace (D.obj i)] :
    ∀ a, QuasiSeparatedSpace ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
  intro a; dsimp; infer_instance

/-- Mathlib's `AlgebraicGeometry.Scheme.nonempty_of_isLimit` (Stacks 01Z2) with the index
universes independent of the scheme universe. -/
public theorem Scheme.nonempty_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, Nonempty (D.obj i)]
    [∀ i, CompactSpace (D.obj i)] : Nonempty c.pt := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₂ : ∀ a, Nonempty ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  exact Scheme.nonempty_of_isLimit _ _ (isLimit_whisker_fromCofilteredInitialModel c hc)

/-- Mathlib's `AlgebraicGeometry.Scheme.compactSpace_of_isLimit` with the index universes
independent of the scheme universe. -/
public theorem Scheme.compactSpace_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)] :
    CompactSpace c.pt := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  exact Scheme.compactSpace_of_isLimit _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc)

/-- Mathlib's `AlgebraicGeometry.isAffineHom_π_app` with the index universes independent of the
scheme universe. -/
public theorem isAffineHom_π_app_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (i : I) : IsAffineHom (c.π.app i) := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have key : IsAffineHom
      (c.π.app ((fromCofilteredInitialModel.{u} I).obj
        (Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i))) :=
    isAffineHom_π_app (fromCofilteredInitialModel.{u} I ⋙ D) _
      (isLimit_whisker_fromCofilteredInitialModel c hc)
      (Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)
  rw [← c.w (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i)]
  infer_instance

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit` (Stacks 01Z5) with the
index universes independent of the scheme universe. -/
public theorem Scheme.exists_isQuasiAffine_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] [IsQuasiAffine c.pt] :
    ∃ i, IsQuasiAffine (D.obj i) := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  have h₅ : IsQuasiAffine (Cone.whisker (fromCofilteredInitialModel.{u} I) c).pt :=
    inferInstanceAs (IsQuasiAffine c.pt)
  obtain ⟨a, ha⟩ := Scheme.exists_isQuasiAffine_of_isLimit _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc)
  exact ⟨_, ha⟩

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_isAffine_of_isLimit` (Stacks 01Z6) with the index
universes independent of the scheme universe. -/
public theorem Scheme.exists_isAffine_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] [IsAffine c.pt] :
    ∃ i, IsAffine (D.obj i) := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  have h₅ : IsAffine (Cone.whisker (fromCofilteredInitialModel.{u} I) c).pt :=
    inferInstanceAs (IsAffine c.pt)
  obtain ⟨a, ha⟩ := Scheme.exists_isAffine_of_isLimit _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc)
  exact ⟨_, ha⟩

/-- Mathlib's `AlgebraicGeometry.exists_preimage_eq` (Stacks 01Z4 (1)) with the index universes
independent of the scheme universe. -/
public theorem exists_preimage_eq_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V = U := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  obtain ⟨a, V, hV, hVU⟩ := exists_preimage_eq _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc) U hU
  exact ⟨_, V, hV, hVU⟩

/-- Mathlib's `AlgebraicGeometry.exists_isAffineOpen_preimage_eq` (Stacks 01Z4 (1)) with the index
universes independent of the scheme universe. -/
public theorem exists_isAffineOpen_preimage_eq_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (U : c.pt.Opens) (hU : IsAffineOpen U) :
    ∃ (i : I) (V : (D.obj i).Opens), IsAffineOpen V ∧ c.π.app i ⁻¹ᵁ V = U := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  obtain ⟨a, V, hV, hVU⟩ := exists_isAffineOpen_preimage_eq _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc) U hU
  exact ⟨_, V, hV, hVU⟩

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine_of_finite` with the index
universes independent of the scheme universe. -/
public theorem Scheme.exists_isOpenCover_and_isAffine_of_finite_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    {J : Type*} [Finite J] (U : J → c.pt.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (hU' : ∀ j, IsAffineOpen (U j)) :
    ∃ (i : I) (V : J → (D.obj i).Opens),
      TopologicalSpace.IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  obtain ⟨a, V, hV, hV'⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc) U hU hU'
  exact ⟨_, V, hV, hV'⟩

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_isOpenCover_and_isAffine` with the index universes
independent of the scheme universe. -/
public theorem Scheme.exists_isOpenCover_and_isAffine_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    {J : Type*} (U : J → c.pt.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (hU' : ∀ j, IsAffineOpen (U j)) :
    ∃ (i : I) (s : Finset J) (V : s → (D.obj i).Opens),
      TopologicalSpace.IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  obtain ⟨a, s, V, hV, hV'⟩ := Scheme.exists_isOpenCover_and_isAffine _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc) U hU hU'
  exact ⟨_, s, V, hV, hV'⟩

/-- Mathlib's `AlgebraicGeometry.Scheme.OpenCover.exists_of_isCofiltered_of_finite` with the index
universes independent of the scheme universe. -/
public theorem Scheme.OpenCover.exists_of_isCofiltered_of_finite_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (𝒰 : Scheme.OpenCover.{w} c.pt) [∀ j, IsAffine (𝒰.X j)] [Finite 𝒰.I₀] :
    ∃ (i : I) (R : 𝒰.I₀ → CommRingCat.{u}) (f : ∀ (a : 𝒰.I₀), Spec (R a) ⟶ (D.obj i))
      (_ : Presieve.ofArrows _ f ∈ zariskiPrecoverage _) (g : ∀ (j : 𝒰.I₀), 𝒰.X j ⟶ Spec (R j)),
      ∀ (j : 𝒰.I₀), IsPullback (g j) (𝒰.f j) (f j) (c.π.app i) := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  obtain ⟨a, R, f, hf, g, hg⟩ := Scheme.OpenCover.exists_of_isCofiltered_of_finite _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc) 𝒰
  exact ⟨_, R, f, hf, g, hg⟩

/-- Mathlib's `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` with the index universes
independent of the scheme universe. -/
public theorem exists_appTop_π_eq_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (s : Γ(c.pt, ⊤)) :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), s = (c.π.app i).appTop t := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  obtain ⟨a, t, ht⟩ := exists_appTop_π_eq_of_isLimit _ _
    (isLimit_whisker_fromCofilteredInitialModel c hc) s
  exact ⟨_, t, ht⟩

/-- Mathlib registers `AlgebraicGeometry.Scheme.Γ.rightOp` as preserving a cofiltered limit of
qcqs schemes with affine transitions as an instance, for an index category at the scheme universe.
This is the same statement with the index universes independent of the scheme universe. -/
public theorem preservesLimit_Γ_rightOp_of_initiallySmall
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] :
    PreservesLimit D Scheme.Γ.rightOp := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  exact Functor.Initial.preservesLimit_of_comp (fromCofilteredInitialModel.{u} I)

/-! ### Results naming an index of the original diagram

For a statement of the form "there is a later stage at which ...", the reindexing has to carry
the given index `i : I` into the small model. `CategoryTheory.Functor.Initial.lift` and
`CategoryTheory.Functor.Initial.homToLift` provide an object `a` of the model and a morphism
`g : A.obj a ⟶ i`; the data at `i` is transported along `D.map g`, Mathlib's result is applied at
`a`, and the resulting morphism `A.obj b ⟶ A.obj a` is composed with `g`. -/

/-- Mathlib's `AlgebraicGeometry.exists_map_eq_top` with the index universes independent of the
scheme universe. -/
public theorem exists_map_eq_top_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    {i : I} (U : (D.obj i).Opens) (hU : c.π.app i ⁻¹ᵁ U = ⊤) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹ᵁ U = ⊤ := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  obtain ⟨b, h, hb⟩ := exists_map_eq_top (fromCofilteredInitialModel.{u} I ⋙ D) _
    (isLimit_whisker_fromCofilteredInitialModel c hc)
    (i := Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)
    (D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i) ⁻¹ᵁ U)
    (by simpa only [Cone.whisker_π, Functor.whiskerLeft_app, ← Scheme.Hom.comp_preimage,
      c.w] using hU)
  refine ⟨_, (fromCofilteredInitialModel.{u} I).map h ≫
    Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i, ?_⟩
  rw [Functor.map_comp, Scheme.Hom.comp_preimage]
  exact hb

/-- Mathlib's `AlgebraicGeometry.exists_map_preimage_eq_map_preimage` (Stacks 01Z4 (2)) with the
index universes independent of the scheme universe. -/
public theorem exists_map_preimage_eq_map_preimage_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    {i : I} {U V : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (hV : IsCompact (V : Set (D.obj i))) (H : c.π.app i ⁻¹ᵁ U = c.π.app i ⁻¹ᵁ V) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹ᵁ U = D.map fji ⁻¹ᵁ V := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  obtain ⟨b, h, hb⟩ := exists_map_preimage_eq_map_preimage
    (fromCofilteredInitialModel.{u} I ⋙ D) _
    (isLimit_whisker_fromCofilteredInitialModel c hc)
    (i := Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)
    (U := D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i) ⁻¹ᵁ U)
    (V := D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i) ⁻¹ᵁ V)
    (QuasiCompact.isCompact_preimage _ U.isOpen hU)
    (QuasiCompact.isCompact_preimage _ V.isOpen hV)
    (by simpa only [Cone.whisker_π, Functor.whiskerLeft_app, ← Scheme.Hom.comp_preimage,
      c.w] using H)
  refine ⟨_, (fromCofilteredInitialModel.{u} I).map h ≫
    Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i, ?_⟩
  rw [Functor.map_comp, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  exact hb

/-- Mathlib's `AlgebraicGeometry.exists_appTop_map_eq_zero_of_isLimit` with the index universes
independent of the scheme universe. -/
public theorem exists_appTop_map_eq_zero_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    {i : I} [CompactSpace (D.obj i)] (s : Γ(D.obj i, ⊤))
    (hs : (c.π.app i).appTop s = 0) :
    ∃ (j : I) (fji : j ⟶ i), (D.map fji).appTop s = 0 := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ : CompactSpace ((fromCofilteredInitialModel.{u} I ⋙ D).obj
      (Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)) :=
    QuasiCompact.compactSpace_of_compactSpace
      (D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i))
  obtain ⟨b, h, hb⟩ := exists_appTop_map_eq_zero_of_isLimit
    (fromCofilteredInitialModel.{u} I ⋙ D) _
    (isLimit_whisker_fromCofilteredInitialModel c hc)
    (i := Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)
    ((D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i)).appTop s)
    (by simp only [Cone.whisker_π, Functor.whiskerLeft_app]
        rw [← elementwise_of% Scheme.Hom.comp_appTop, c.w]
        exact hs)
  refine ⟨_, (fromCofilteredInitialModel.{u} I).map h ≫
    Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i, ?_⟩
  rw [Functor.map_comp, elementwise_of% Scheme.Hom.comp_appTop]
  exact hb

/-- Mathlib's `AlgebraicGeometry.exists_app_map_eq_zero_of_isLimit` with the index universes
independent of the scheme universe. -/
public theorem exists_app_map_eq_zero_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i))) (s : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = 0) :
    ∃ (j : I) (fji : j ⟶ i), (D.map fji).app U s = 0 := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  obtain ⟨b, h, hb⟩ := exists_app_map_eq_zero_of_isLimit
    (fromCofilteredInitialModel.{u} I ⋙ D) _
    (isLimit_whisker_fromCofilteredInitialModel c hc)
    (i := Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)
    (U := D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i) ⁻¹ᵁ U)
    (QuasiCompact.isCompact_preimage _ U.isOpen hU)
    ((D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i)).app U s)
    (by simp only [Cone.whisker_π, Functor.whiskerLeft_app]
        rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_app]
        exact Eq.mpr (congrArg (fun φ : c.pt ⟶ D.obj i => (Scheme.Hom.app φ U) s = 0)
          (c.w (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i))) hs)
  refine ⟨_, (fromCofilteredInitialModel.{u} I).map h ≫
    Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i, ?_⟩
  rw [Functor.map_comp, Scheme.Hom.comp_app]
  exact hb

/-- Mathlib's `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit` with the index universes
independent of the scheme universe. -/
public theorem exists_app_map_eq_map_of_isLimit_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i))) (s s' : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = (c.π.app i).app U s') :
    ∃ (j : I) (fji : j ⟶ i), (D.map fji).app U s = (D.map fji).app U s' := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  obtain ⟨b, h, hb⟩ := exists_app_map_eq_map_of_isLimit
    (fromCofilteredInitialModel.{u} I ⋙ D) _
    (isLimit_whisker_fromCofilteredInitialModel c hc)
    (i := Functor.Initial.lift (fromCofilteredInitialModel.{u} I) i)
    (U := D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i) ⁻¹ᵁ U)
    (QuasiCompact.isCompact_preimage _ U.isOpen hU)
    ((D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i)).app U s)
    ((D.map (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i)).app U s')
    (by simp only [Cone.whisker_π, Functor.whiskerLeft_app]
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← Scheme.Hom.comp_app]
        exact Eq.mpr (congrArg (fun φ : c.pt ⟶ D.obj i =>
          (Scheme.Hom.app φ U) s = (Scheme.Hom.app φ U) s')
          (c.w (Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i))) hs)
  refine ⟨_, (fromCofilteredInitialModel.{u} I).map h ≫
    Functor.Initial.homToLift (fromCofilteredInitialModel.{u} I) i, ?_⟩
  rw [Functor.map_comp, Scheme.Hom.comp_app]
  exact hb

/-! ### Diagrams over a base scheme -/

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`
(the injective part of (1) ⇒ (3) of Stacks 01ZC) with the index universes independent of the
scheme universe. -/
public theorem Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType_of_initiallySmall
    (τ : D ⟶ (Functor.const I).obj S) (f : X ⟶ S) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, CompactSpace (D.obj i)]
    [LocallyOfFiniteType f]
    {i : I} (a : D.obj i ⟶ X) (ha : τ.app i = a ≫ f)
    {j : I} (b : D.obj j ⟶ X) (hb : τ.app j = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : I) (hik : k ⟶ i) (hjk : k ⟶ j), D.map hik ≫ a = D.map hjk ≫ b := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  -- The two chosen lifts of `i` and `j`, and a common predecessor of them in the small model.
  set ι : CofilteredInitialModel.{u} I ⥤ I := fromCofilteredInitialModel.{u} I with hι
  have : ι.Initial := hι ▸ inferInstance
  set α : ι.obj (IsCofiltered.min (Functor.Initial.lift ι i) (Functor.Initial.lift ι j)) ⟶ i :=
    ι.map (IsCofiltered.minToLeft _ _) ≫ Functor.Initial.homToLift ι i with hα
  set β : ι.obj (IsCofiltered.min (Functor.Initial.lift ι i) (Functor.Initial.lift ι j)) ⟶ j :=
    ι.map (IsCofiltered.minToRight _ _) ≫ Functor.Initial.homToLift ι j with hβ
  obtain ⟨k, hik, hjk, hk⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
    (ι ⋙ D)
    ({ app x := τ.app (ι.obj x), naturality := fun x y g ↦ τ.naturality (ι.map g) })
    f _ ((Functor.Initial.isLimitWhiskerEquiv ι c).symm hc)
    (i := IsCofiltered.min (Functor.Initial.lift ι i) (Functor.Initial.lift ι j))
    (D.map α ≫ a) (by simpa [ha] using (τ.naturality α).symm)
    (j := IsCofiltered.min (Functor.Initial.lift ι i) (Functor.Initial.lift ι j))
    (D.map β ≫ b) (by simpa [hb] using (τ.naturality β).symm)
    (by simp only [Cone.whisker_π, Functor.whiskerLeft_app, ← Category.assoc, c.w, hab])
  refine ⟨ι.obj k, ι.map hik ≫ α, ι.map hjk ≫ β, ?_⟩
  simpa only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc] using hk

/-- Mathlib's `AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` with
the index universes independent of the scheme universe. -/
public theorem Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_initiallySmall
    (τ : D ⟶ (Functor.const I).obj S) (f : X ⟶ S) (hc : IsLimit c)
    [LocallyOfFinitePresentation f] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (a : c.pt ⟶ X) (ha : c.π ≫ τ = (Functor.const I).map (a ≫ f)) :
    ∃ (i : I) (g : D.obj i ⟶ X), c.π.app i ≫ g = a ∧ g ≫ f = τ.app i := by
  have h₁ := @isAffineHom_map_fromCofilteredInitialModel _ _ D _ _ _ _
  have h₃ := compactSpace_obj_fromCofilteredInitialModel D
  have h₄ := quasiSeparatedSpace_obj_fromCofilteredInitialModel D
  obtain ⟨b, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (fromCofilteredInitialModel.{u} I ⋙ D)
    ({ app x := τ.app ((fromCofilteredInitialModel.{u} I).obj x),
       naturality := fun x y g ↦ τ.naturality _ })
    f _ (isLimit_whisker_fromCofilteredInitialModel c hc)
    a (by ext x; exact NatTrans.congr_app ha ((fromCofilteredInitialModel.{u} I).obj x))
  exact ⟨_, g, hg₁, hg₂⟩

end

end AlgebraicGeometry
