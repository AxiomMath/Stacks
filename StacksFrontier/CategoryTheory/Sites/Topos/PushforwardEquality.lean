module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! # Pushforward along a cover-dense functor reflects injections and surjections

Let `u : C ⥤ D` be a continuous functor between sites whose image covers every object of `D`.
Then the pushforward `f_* : Sheaf K A ⥤ Sheaf J A` is faithful, and therefore reflects both
monomorphisms and epimorphisms.

## Main results

* `val_app_comp_eq_on_image_arrow`: two morphisms of sheaves with the same pushforward agree
  after restriction along any arrow out of an object in the image of `u`.
* `val_app_eq_of_pushforward_eq`: hence they agree componentwise.
* `sheafPushforwardContinuous_faithful_of_isCoverDense`: the pushforward is faithful.
* `sheafPushforwardContinuous_reflectsMonomorphisms_of_isCoverDense`,
  `sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense`: the pushforward reflects
  injections and surjections (Stacks 04D9).

Tags covered: 04D9.
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (A : Type u₃) [Category.{v₃} A]

/-- If `u_*(f) = u_*(g)`, then `f` and `g` agree after restriction along any arrow
`u.obj U ⟶ V`, by naturality applied to a `congrArg` on objects of the form `u.obj U`. -/
@[stacks 04D9]
lemma val_app_comp_eq_on_image_arrow
    [u.IsContinuous J K] {X Y : Sheaf K A} (f g : X ⟶ Y)
    (h : (u.sheafPushforwardContinuous A J K).map f =
         (u.sheafPushforwardContinuous A J K).map g)
    {V : D} {U : C} (p : u.obj U ⟶ V) :
    f.hom.app (op V) ≫ Y.obj.map p.op = g.hom.app (op V) ≫ Y.obj.map p.op := by
  rw [← f.hom.naturality p.op, ← g.hom.naturality p.op,
      show f.hom.app (op (u.obj U)) = g.hom.app (op (u.obj U)) from
        congrArg (fun φ => φ.hom.app (op U)) h]

/-- The componentwise equality `f.hom.app V = g.hom.app V`, deduced from cover density
by checking on the sieve `Sieve.coverByImage u V`. -/
lemma val_app_eq_of_pushforward_eq
    [u.IsContinuous J K] [u.IsCoverDense K] {X Y : Sheaf K A} (f g : X ⟶ Y)
    (h : (u.sheafPushforwardContinuous A J K).map f =
         (u.sheafPushforwardContinuous A J K).map g) (V : Dᵒᵖ) :
    f.hom.app V = g.hom.app V := by
  refine Y.property.hom_ext
    ⟨Sieve.coverByImage u V.unop, Functor.IsCoverDense.is_cover (G := u) V.unop⟩
    (f.hom.app V) (g.hom.app V) ?_
  rintro ⟨W, φ, ⟨s⟩⟩
  dsimp only
  rw [show (φ : W ⟶ V.unop) = s.lift ≫ s.map from s.fac.symm, op_comp, Functor.map_comp,
      ← Category.assoc, ← Category.assoc, val_app_comp_eq_on_image_arrow u J K A f g h s.map]

/-- **Faithfulness of the pushforward.** If `u : C ⥤ D` is a continuous, cover-dense
functor between sites, then `u.sheafPushforwardContinuous A J K` is faithful. -/
lemma sheafPushforwardContinuous_faithful_of_isCoverDense
    [u.IsContinuous J K] [u.IsCoverDense K] :
    (u.sheafPushforwardContinuous A J K).Faithful where
  map_injective {_ _} f g h := Sheaf.hom_ext <| by
    ext V
    exact val_app_eq_of_pushforward_eq u J K A f g h V

/-- **Stacks 04D9.** If `u : C ⥤ D` is a continuous functor between sites
which is also cover dense (i.e. every object of `D` is covered by
images of objects of `C` under `u`), then the pushforward functor on
sheaves `f_* : Sheaf K A ⥤ Sheaf J A` reflects monomorphisms. -/
theorem sheafPushforwardContinuous_reflectsMonomorphisms_of_isCoverDense
    [u.IsContinuous J K] [u.IsCoverDense K] :
    (u.sheafPushforwardContinuous A J K).ReflectsMonomorphisms :=
  have := sheafPushforwardContinuous_faithful_of_isCoverDense u J K A
  Functor.reflectsMonomorphisms_of_faithful _

/-- **Stacks 04D9.** If `u : C ⥤ D` is a continuous functor between sites
which is also cover dense (i.e. every object of `D` is covered by
images of objects of `C` under `u`), then the pushforward functor on
sheaves `f_* : Sheaf K A ⥤ Sheaf J A` reflects epimorphisms. -/
theorem sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense
    [u.IsContinuous J K] [u.IsCoverDense K] :
    (u.sheafPushforwardContinuous A J K).ReflectsEpimorphisms :=
  have := sheafPushforwardContinuous_faithful_of_isCoverDense u J K A
  Functor.reflectsEpimorphisms_of_faithful _
