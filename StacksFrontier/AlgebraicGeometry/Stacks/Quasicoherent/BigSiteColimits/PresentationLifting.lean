module

public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Lifting generators along a presentation

Let `b : P ⟶ N` present a sheaf of modules `N` as a quotient of a coproduct `P` of copies of
the structure sheaf, and let `F` be another such coproduct.  A morphism `g : F ⟶ N` lifts to a
morphism `l : F ⟶ P` with `l ≫ b = g` as soon as `b` is surjective on *global sections*.  This
is the one hypothesis of
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` that is not a formal
consequence of the two presentations it starts from, and this file supplies it from that
surjectivity.

Nothing here is restricted to finite index types: the passage from the lift of a single
generator to the lift of a whole family is the universal property of the coproduct, which holds
for an arbitrary index type.  The surjectivity hypothesis carries all the content, and it is
already needed for a single generator.

On a site with a terminal object `Z` the global sections of a sheaf of modules are its sections
over `Z`, because a compatible family is determined by its value there and every value there
extends to one.  That identification is made explicit, so the hypothesis may be read either as
surjectivity of `PresheafOfModules.sectionsMap` or as surjectivity of the map on sections over
`Z`.  Over the slice site at an object `U` the terminal object is `CategoryTheory.Over.mk (𝟙 U)`
and the hypothesis says that the map of sections over `U` is surjective; for `U` affine in a
site of schemes that is the vanishing of the first cohomology of the kernel of `b`.

## Main definitions

* `ModuleCat.uliftSelfGen` is the lift of `1` in the universe lift of a ring, and
  `ModuleCat.uliftSelfHom` the linear map out of that lift carrying it to a prescribed element.
* `PresheafOfModules.overTerminal` is the family of sections obtained from a section over a
  terminal object by restricting along the unique morphisms to it.
* `PresheafOfModules.sectionsEquivObjOfIsTerminal` identifies the global sections of a presheaf
  of modules on a site with a terminal object with its sections over that object.
* `SheafOfModules.fromUliftUnit` is the morphism out of the universe lift of the structure sheaf
  carrying `ModuleCat.uliftSelfGen` to a prescribed section over a terminal object, and
  `SheafOfModules.uliftUnitHomEquiv` the resulting bijection.

## Main results

* `CategoryTheory.Limits.exists_lift_of_isColimit_cofan`: a morphism out of a coproduct lifts
  along a morphism along which every morphism out of a summand lifts.
* `PresheafOfModules.surjective_sectionsMap_of_surjective_app` and
  `PresheafOfModules.surjective_app_of_surjective_sectionsMap`: on a site with a terminal object,
  surjectivity on global sections and surjectivity on sections over that object agree.
* `SheafOfModules.exists_lift_of_surjective_val_app`: a morphism out of the universe lift of the
  structure sheaf lifts along a morphism that is surjective on sections over a terminal object.
* `SheafOfModules.exists_lift_cofan_of_surjective_val_app`: **the lift.**  A morphism out of a
  coproduct of copies of the universe lift of the structure sheaf lifts along a morphism that is
  surjective on sections over a terminal object, whatever the index type of the coproduct.
* `SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app`: the
  cokernel step of a global presentation, with the lift replaced by surjectivity of the
  presenting morphism on sections over a terminal object.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v r m t

namespace CategoryTheory.Limits

/-- A morphism out of a coproduct lifts along `b` as soon as every morphism out of a summand
lifts along `b`: lift the components and take the induced morphism.  The index type is
arbitrary. -/
theorem exists_lift_of_isColimit_cofan {D : Type u} [Category.{v} D] {I : Type w}
    {O F P N : D} {ν : ∀ _ : I, O ⟶ F} (hF : IsColimit (Cofan.mk F ν)) {b : P ⟶ N}
    (hb : ∀ h : O ⟶ N, ∃ k : O ⟶ P, k ≫ b = h) (g : F ⟶ N) :
    ∃ l : F ⟶ P, l ≫ b = g := by
  choose k hk using fun i ↦ hb (ν i ≫ g)
  refine ⟨Cofan.IsColimit.desc hF k, Cofan.IsColimit.hom_ext hF _ _ fun i ↦ ?_⟩
  change (Cofan.mk F ν).inj i ≫ _ ≫ b = _
  rw [← Category.assoc, Cofan.IsColimit.fac hF k i, hk i]
  rfl

end CategoryTheory.Limits

namespace ModuleCat

/-- The lift of `1` in the universe lift of a ring `A`, a generator of `ULift A` as an
`A`-module. -/
def uliftSelfGen (A : RingCat.{r}) : ULift.{t} A := ULift.up 1

/-- `ModuleCat.uliftSelfGen` generates: every element of the universe lift of a ring is a
multiple of it. -/
@[simp]
lemma smul_uliftSelfGen {A : RingCat.{r}} (a : ULift.{t} A) :
    a.down • uliftSelfGen.{r, t} A = a :=
  ULift.ext (mul_one a.down)

/-- The `A`-linear map from the universe lift of a ring `A` to an `A`-module `M` sending
`ModuleCat.uliftSelfGen` to a prescribed element `y` of `M`, that is, sending the lift of `a`
to `a • y`. -/
noncomputable def uliftSelfHom {A : RingCat.{r}} (M : ModuleCat.{max t r} A) (y : M) :
    ModuleCat.of A (ULift.{t} A) ⟶ M :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton A M y).comp
    (ULift.moduleEquiv (R := A) (M := A)).toLinearMap)

/-- `ModuleCat.uliftSelfHom M y` sends the lift of `a` to `a • y`. -/
@[simp]
lemma uliftSelfHom_apply {A : RingCat.{r}} (M : ModuleCat.{max t r} A) (y : M)
    (a : ULift.{t} A) : uliftSelfHom.{r, t} M y a = a.down • y := rfl

/-- `ModuleCat.uliftSelfHom` does send `ModuleCat.uliftSelfGen` to the prescribed element. -/
@[simp]
lemma uliftSelfHom_uliftSelfGen {A : RingCat.{r}} (M : ModuleCat.{max t r} A) (y : M) :
    uliftSelfHom.{r, t} M y (uliftSelfGen.{r, t} A) = y := one_smul _ y

/-- **Every linear map out of the universe lift of a ring is a `ModuleCat.uliftSelfHom`**, namely
the one at the image of `ModuleCat.uliftSelfGen`. -/
lemma uliftSelfHom_eq {A : RingCat.{r}} {M : ModuleCat.{max t r} A}
    (g : ModuleCat.of A (ULift.{t} A) ⟶ M) :
    uliftSelfHom.{r, t} M (g (uliftSelfGen.{r, t} A)) = g := by
  apply ModuleCat.hom_ext
  ext a
  rw [uliftSelfHom_apply, ← map_smul g.hom, smul_uliftSelfGen]

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{r}}

/-- **The family of sections restricted from a section over a terminal object `Z`**: restrict
along the unique morphism `Y ⟶ Z`. -/
noncomputable def overTerminal (M : PresheafOfModules.{w} R) {Z : C} (hZ : IsTerminal Z)
    (x : M.obj (op Z)) (Y : Cᵒᵖ) : M.obj Y :=
  M.map (hZ.from Y.unop).op x

/-- The sections restricted from a terminal object form a compatible family. -/
lemma overTerminal_map (M : PresheafOfModules.{w} R) {Z : C} (hZ : IsTerminal Z)
    (x : M.obj (op Z)) {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') :
    M.map f (M.overTerminal hZ x Y) = M.overTerminal hZ x Y' := by
  rw [overTerminal, overTerminal, ← map_comp_apply]
  exact M.congr_map_apply (Quiver.Hom.unop_inj (hZ.hom_ext _ _)) x

/-- The global section restricted from a section over a terminal object. -/
noncomputable def sectionsOfIsTerminal (M : PresheafOfModules.{w} R) {Z : C}
    (hZ : IsTerminal Z) (x : M.obj (op Z)) : M.sections :=
  sectionsMk (M.overTerminal hZ x) (fun {_ _} f ↦ M.overTerminal_map hZ x f)

/-- At the terminal object itself, restriction gives back the section it came from. -/
lemma overTerminal_self (M : PresheafOfModules.{w} R) {Z : C} (hZ : IsTerminal Z)
    (x : M.obj (op Z)) : M.overTerminal hZ x (op Z) = x := by
  rw [overTerminal]
  refine (M.congr_map_apply
    (congrArg Quiver.Hom.op (hZ.hom_ext (hZ.from Z) (𝟙 Z))) x).trans ?_
  rw [op_id]
  exact CategoryTheory.congr_fun (M.map_id (op Z)) x

/-- **Global sections of a presheaf of modules on a site with a terminal object `Z` are the
sections over `Z`.**  A compatible family is determined by its value at `Z`, and every value at
`Z` extends to one by `PresheafOfModules.overTerminal`. -/
noncomputable def sectionsEquivObjOfIsTerminal (M : PresheafOfModules.{w} R) {Z : C}
    (hZ : IsTerminal Z) : M.sections ≃ M.obj (op Z) where
  toFun s := s.val (op Z)
  invFun := M.sectionsOfIsTerminal hZ
  left_inv s := sections_ext _ _ fun _ ↦ sections_property s _
  right_inv := M.overTerminal_self hZ

/-- A morphism of presheaves of modules surjective on sections over a terminal object is
surjective on global sections. -/
lemma surjective_sectionsMap_of_surjective_app {M N : PresheafOfModules.{w} R} (f : M ⟶ N)
    {Z : C} (hZ : IsTerminal Z) (hf : Function.Surjective (Hom.app f (op Z))) :
    Function.Surjective (sectionsMap f) := by
  intro t
  obtain ⟨x, hx⟩ := hf (t.val (op Z))
  refine ⟨M.sectionsOfIsTerminal hZ x, sections_ext _ _ fun Y ↦ ?_⟩
  change Hom.app f Y (M.overTerminal hZ x Y) = t.val Y
  rw [overTerminal, naturality_apply, hx, sections_property]

/-- A morphism of presheaves of modules surjective on global sections is surjective on sections
over a terminal object. -/
lemma surjective_app_of_surjective_sectionsMap {M N : PresheafOfModules.{w} R} (f : M ⟶ N)
    {Z : C} (hZ : IsTerminal Z) (hf : Function.Surjective (sectionsMap f)) :
    Function.Surjective (Hom.app f (op Z)) := by
  intro x
  obtain ⟨s, hs⟩ := hf (N.sectionsOfIsTerminal hZ x)
  exact ⟨s.val (op Z), (congrArg (fun z : N.sections ↦ z.val (op Z)) hs).trans
    (N.overTerminal_self hZ x)⟩

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **The lift of the unit section of the structure sheaf**, a global section generating the
universe lift of the structure sheaf. -/
def uliftUnitGen (R : Sheaf J RingCat.{r}) (Y : Cᵒᵖ) :
    (uliftForPresentation.{u, v, r, r, t} (unit R)).val.obj Y :=
  ModuleCat.uliftSelfGen.{r, t} (R.obj.obj Y)

/-- `SheafOfModules.uliftUnitGen` is a global section: it is preserved by every restriction
map. -/
lemma uliftForPresentation_unit_val_map_uliftUnitGen {Y Y' : Cᵒᵖ} (f : Y ⟶ Y') :
    (uliftForPresentation.{u, v, r, r, t} (unit R)).val.map f
        (uliftUnitGen.{u, v, r, t} R Y) = uliftUnitGen.{u, v, r, t} R Y' :=
  congrArg ULift.up (PresheafOfModules.unit_map_one (R := R.obj) f)

/-- **The morphism out of the universe lift of the structure sheaf determined by a section over
a terminal object `Z`**: it carries `SheafOfModules.uliftUnitGen` to the prescribed section,
hence the lift of `a` to `a` times the restriction of that section. -/
noncomputable def fromUliftUnit {X : SheafOfModules.{max t r} R} {Z : C} (hZ : IsTerminal Z)
    (x : X.val.obj (op Z)) : uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ X where
  val :=
    { app := fun Y ↦ ModuleCat.uliftSelfHom.{r, t} (X.val.obj Y) (X.val.overTerminal hZ x Y)
      naturality := fun {Y Y'} f ↦ by
        have key : ∀ a : ULift.{t} (R.obj.obj Y),
            ModuleCat.uliftSelfHom.{r, t} (X.val.obj Y') (X.val.overTerminal hZ x Y')
                (ULift.up (R.obj.map f a.down)) =
              X.val.map f (ModuleCat.uliftSelfHom.{r, t} (X.val.obj Y)
                (X.val.overTerminal hZ x Y) a) := fun a ↦ by
          rw [ModuleCat.uliftSelfHom_apply, ModuleCat.uliftSelfHom_apply,
            PresheafOfModules.map_smul, X.val.overTerminal_map hZ x f]
          rfl
        apply ModuleCat.hom_ext
        ext a
        exact key a }

/-- On each object `Y`, the morphism `SheafOfModules.fromUliftUnit hZ x` is the linear map
`ModuleCat.uliftSelfHom` at the restriction of `x` to `Y`. -/
lemma fromUliftUnit_val_app {X : SheafOfModules.{max t r} R} {Z : C} (hZ : IsTerminal Z)
    (x : X.val.obj (op Z)) (Y : Cᵒᵖ) :
    (fromUliftUnit.{u, v, r, t} hZ x).val.app Y =
      ModuleCat.uliftSelfHom.{r, t} (X.val.obj Y) (X.val.overTerminal hZ x Y) := rfl

/-- The section over a terminal object `Z` that a morphism out of the universe lift of the
structure sheaf carries `SheafOfModules.uliftUnitGen` to determines that morphism, through
`SheafOfModules.fromUliftUnit`. -/
lemma fromUliftUnit_val_app_uliftUnitGen {X : SheafOfModules.{max t r} R} {Z : C}
    (hZ : IsTerminal Z) (φ : uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ X) :
    fromUliftUnit.{u, v, r, t} hZ (φ.val.app (op Z) (uliftUnitGen.{u, v, r, t} R (op Z))) = φ := by
  have h2 : ∀ Y : Cᵒᵖ,
      X.val.overTerminal hZ (φ.val.app (op Z) (uliftUnitGen.{u, v, r, t} R (op Z))) Y =
        φ.val.app Y (uliftUnitGen.{u, v, r, t} R Y) := fun Y ↦ by
    rw [PresheafOfModules.overTerminal, ← PresheafOfModules.naturality_apply,
      uliftForPresentation_unit_val_map_uliftUnitGen.{u, v, r, t}]
  refine (forget R).map_injective (PresheafOfModules.hom_ext fun Y ↦ ?_)
  exact (congrArg (ModuleCat.uliftSelfHom.{r, t} (X.val.obj Y)) (h2 Y)).trans
    (ModuleCat.uliftSelfHom_eq (A := R.obj.obj Y) (φ.val.app Y))

/-- **Morphisms out of the universe lift of the structure sheaf are sections over a terminal
object `Z`**, by evaluation at `SheafOfModules.uliftUnitGen`. -/
noncomputable def uliftUnitHomEquiv {Z : C} (hZ : IsTerminal Z) (X : SheafOfModules.{max t r} R) :
    (uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ X) ≃ X.val.obj (op Z) where
  toFun φ := φ.val.app (op Z) (uliftUnitGen.{u, v, r, t} R (op Z))
  invFun := fromUliftUnit.{u, v, r, t} hZ
  left_inv := fromUliftUnit_val_app_uliftUnitGen.{u, v, r, t} hZ
  right_inv x := by
    change ModuleCat.uliftSelfHom.{r, t} (X.val.obj (op Z)) (X.val.overTerminal hZ x (op Z))
      (ModuleCat.uliftSelfGen.{r, t} (R.obj.obj (op Z))) = x
    rw [ModuleCat.uliftSelfHom_uliftSelfGen, X.val.overTerminal_self hZ]

/-- Evaluation at `ModuleCat.uliftSelfGen` is natural in the target. -/
lemma uliftUnitHomEquiv_comp {Z : C} (hZ : IsTerminal Z) {X Y : SheafOfModules.{max t r} R}
    (φ : uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ X) (p : X ⟶ Y) :
    uliftUnitHomEquiv.{u, v, r, t} hZ Y (φ ≫ p) =
      p.val.app (op Z) (uliftUnitHomEquiv.{u, v, r, t} hZ X φ) := rfl

/-- **A morphism out of the universe lift of the structure sheaf lifts along a morphism that is
surjective on sections over a terminal object `Z`.**  Lift the image of
`ModuleCat.uliftSelfGen` and read the lift off `SheafOfModules.uliftUnitHomEquiv`. -/
theorem exists_lift_of_surjective_val_app {P N : SheafOfModules.{max t r} R} {b : P ⟶ N}
    {Z : C} (hZ : IsTerminal Z) (hb : Function.Surjective (b.val.app (op Z)))
    (h : uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ N) :
    ∃ k : uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ P, k ≫ b = h := by
  obtain ⟨x, hx⟩ := hb (uliftUnitHomEquiv.{u, v, r, t} hZ N h)
  refine ⟨fromUliftUnit.{u, v, r, t} hZ x,
    (uliftUnitHomEquiv.{u, v, r, t} hZ N).injective ?_⟩
  rw [uliftUnitHomEquiv_comp,
    show uliftUnitHomEquiv.{u, v, r, t} hZ P (fromUliftUnit.{u, v, r, t} hZ x) = x from
      (uliftUnitHomEquiv.{u, v, r, t} hZ P).apply_symm_apply x, hx]

/-- **The lift.**  A morphism `g : F ⟶ N` out of a coproduct of copies of the universe lift of
the structure sheaf lifts along a morphism `b : P ⟶ N` that is surjective on sections over a
terminal object `Z`.

The index type `I` of the coproduct is arbitrary: the passage from one generator to a family is
the universal property of the coproduct.  The surjectivity hypothesis carries all the content,
and it is already needed when `I` is a singleton. -/
theorem exists_lift_cofan_of_surjective_val_app {I : Type w} {P N F : SheafOfModules.{max t r} R}
    {ν : ∀ _ : I, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ F}
    (hF : IsColimit (Cofan.mk F ν)) {b : P ⟶ N} {Z : C} (hZ : IsTerminal Z)
    (hb : Function.Surjective (b.val.app (op Z))) (g : F ⟶ N) :
    ∃ l : F ⟶ P, l ≫ b = g :=
  exists_lift_of_isColimit_cofan hF (exists_lift_of_surjective_val_app.{u, v, r, t} hZ hb) g

/-- **The cokernel step of a global presentation, from surjectivity on sections.**  This is
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift` with its lift
hypothesis replaced by surjectivity of the presenting morphism `b` on sections over a terminal
object `Z` of the site, which supplies that lift by
`SheafOfModules.exists_lift_cofan_of_surjective_val_app`.

Over the slice site at an object `U`, with `Z` the terminal object `CategoryTheory.Over.mk (𝟙 U)`
supplied by `CategoryTheory.Over.mkIdTerminal`, the hypothesis reads: the presenting morphism is
surjective on sections over `U`. -/
theorem HasGlobalPresentation.of_isColimit_cokernelCofork_of_surjective_val_app
    {M N T : SheafOfModules.{m} R} {f : M ⟶ N} {π : N ⟶ T}
    {I K I' : Type (max u v r m)} {P Q F : SheafOfModules.{max u v r m} R}
    {ι : ∀ _ : I,
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ P}
    {κ : ∀ _ : K,
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ Q}
    {ν : ∀ _ : I',
      uliftForPresentation.{u, v, r, r, max u v m} (SheafOfModules.unit R) ⟶ F}
    (hP : IsColimit (Cofan.mk P ι)) (hQ : IsColimit (Cofan.mk Q κ))
    (hF : IsColimit (Cofan.mk F ν)) [HasBinaryCoproduct Q F]
    {a : Q ⟶ P} {b : P ⟶ uliftForPresentation.{u, v, r, m, max u v r} N}
    (hab : a ≫ b = 0) (hb : IsColimit (CokernelCofork.ofπ b hab))
    {Z : C} (hZ : IsTerminal Z) (hbΓ : Function.Surjective (b.val.app (op Z)))
    {p : F ⟶ uliftForPresentation.{u, v, r, m, max u v r} M} [Epi p]
    (hfπ : uliftForPresentationMap.{u, v, r, m, max u v r} f ≫
      uliftForPresentationMap.{u, v, r, m, max u v r} π = 0)
    (hπ : IsColimit (CokernelCofork.ofπ
      (uliftForPresentationMap.{u, v, r, m, max u v r} π) hfπ)) :
    HasGlobalPresentation T :=
  have ⟨_, hl⟩ := exists_lift_cofan_of_surjective_val_app hF hZ hbΓ
    (p ≫ uliftForPresentationMap.{u, v, r, m, max u v r} f)
  HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift hP hQ hF hab hb hl hfπ hπ

end SheafOfModules

end
