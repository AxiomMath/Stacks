module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# Functoriality of the comparison map of sheaves of differentials

Let `X'' --g--> X' --f--> X` over `Y'' ⟶ Y' ⟶ Y` be a commutative diagram of algebraic spaces
over a scheme `S`.  Stacks 04CX attaches to each square its comparison map
`c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}`, characterized by sending `f^*d_{X/Y}(t)` to `d_{X'/Y'}(f♯ t)`
on local sections, and Stacks 05Z7 asserts that these compose: `c_{f∘g} = c_g ∘ g^*c_f`.

The characterization of Stacks 04CX is
`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`, and its uniqueness clause is
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`.  So Stacks 05Z7 is the assertion
that `c_g ∘ g^*c_f` satisfies that characterization for the outer square, which is exactly the
proof the Stacks project indicates; the equation of the source then follows from uniqueness.
This file carries out that verification, and the one clause of Stacks 03LU that it needs.

## Main results

* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_comp`: **Stacks 05Z7**, the
  characterization — the composite `c_g ∘ g^*c_f`, taken through the comparison
  `(g ≫ f)^* ≅ g^*f^*` of inverse images, has the characterizing property of Stacks 04CX for
  the outer square.
* `AlgebraicGeometry.Space.eq_comp_of_isSheafOfDifferentialsMap`: **Stacks 05Z7** itself,
  `c_{g ≫ f} = c_g ∘ g^*c_f`, each of the three comparison maps being named by its
  characterizing property, which by `eq_of_isSheafOfDifferentialsMap` determines it uniquely.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app`: the comparison
  `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images of `𝒪`-modules of Stacks 03LU is the geometric
  comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), on
  underlying sheaves of sets.  The comparison appears in the transported form that
  `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` identifies it with;
  `AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_eq` is that identification at a
  single module.
* `AlgebraicGeometry.Space.structureSharpSet_comp`: Stacks 03G8, compatibility with
  composition, at the level of sheaves of sets.
* `AlgebraicGeometry.Space.homEquiv_comp_modulePullbackCompIso_inv_app`: the transpose of
  `c_g ∘ g^*c_f` for the outer square is the transpose of `c_f`, the direct image of the
  transpose of `c_g`, and the comparison of direct images.
* `AlgebraicGeometry.Space.universalDerivationHom_comp_transpose_comp_half₁` and
  `AlgebraicGeometry.Space.universalDerivationHom_comp_transpose_comp_half₂`: the two halves of
  the substitution chain of Stacks 05Z7 — the characterizing property of `c_f`, that of `c_g`
  along the direct image, the naturality of the geometric comparison, and the composition law
  for the structure map.

## Implementation notes

The iterated direct image of a module has two spellings of its underlying sheaf of sets,
`Sheaf.moduleSheafFunctor` of `AlgebraicGeometry.Space.modulePushforward` and the iterated
`AlgebraicGeometry.Space.smallEtaleDirectImage`, and identifying them unfolds
`modulePushforward`, `pushforwardModules` and `SheafOfModules.restrictScalars`.  The two halves
of the substitution chain each cross between the spellings once, which is affordable; gluing
them as *sheaves* of sets would cross again inside a statement that already crosses, and the
nested identifications that this forces on the implicit objects of the composites are not.

So the two halves are glued on *sections*:
`AlgebraicGeometry.Space.universalDerivationHom_comp_transpose_comp_half₁_sections` evaluates
the first half at a single local section, where the identification needed is between two types
rather than between two sheaves of types, and
`AlgebraicGeometry.Space.universalDerivationHom_comp_transpose_comp_factored` keeps the rest of
the chain inside the module spelling, where no identification arises at all.  This is possible
because `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` is itself a statement about
sections, so the conclusion never has to be assembled as an equation of sheaf morphisms.

## References

* [Stacks Project, Tag 05Z7](https://stacks.math.columbia.edu/tag/05Z7)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

/-- Congruence for the second factor of a two-factor composite. -/
theorem comp_congr_of_eq {C : Type u₀} [Category.{v₀} C] {A A' A'' : C} (a : A ⟶ A')
    {c c' : A' ⟶ A''} (h : c = c') : a ≫ c = a ≫ c' :=
  congrArg (fun m ↦ a ≫ m) h

/-- Regrouping of a four-factor composite onto its first three factors. -/
theorem comp_assoc₃ {C : Type u₀} [Category.{v₀} C] {O₀ O₁ O₂ O₃ O₄ : C} (a : O₀ ⟶ O₁)
    (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃) (d : O₃ ⟶ O₄) : a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

/-- The first half of a substitution chain: a three-factor composite rewritten by
factorizations of its two consecutive pairs. -/
theorem comp_eq_of_factorizations₁ {C : Type u₀} [Category.{v₀} C] {O₀ O₁ O₂ O₃ O₅ O₆ : C}
    {A : O₀ ⟶ O₁} {a : O₁ ⟶ O₂} {b : O₂ ⟶ O₃} {s : O₀ ⟶ O₅} {m : O₅ ⟶ O₂} {d : O₅ ⟶ O₆}
    {e : O₆ ⟶ O₃} (h₁ : A ≫ a = s ≫ m) (h₂ : m ≫ b = d ≫ e) : A ≫ a ≫ b = s ≫ d ≫ e := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- The second half of a substitution chain: a composite whose first three factors are
already factorized, rewritten by a factorization of its last pair and the composition law for
the first three. -/
theorem comp_eq_of_factorizations₂ {C : Type u₀} [Category.{v₀} C] {O₀ O₃ O₄ O₅ O₆ O₇ : C}
    {c : O₃ ⟶ O₄} {s : O₀ ⟶ O₅} {d : O₅ ⟶ O₆} {e : O₆ ⟶ O₃} {k : O₆ ⟶ O₇} {D : O₇ ⟶ O₄}
    {t : O₀ ⟶ O₇} (h₃ : e ≫ c = k ≫ D) (h₄ : s ≫ d ≫ k = t) :
    (s ≫ d ≫ e) ≫ c = t ≫ D := by
  rw [Category.assoc, Category.assoc, h₃, ← Category.assoc d k D,
    ← Category.assoc s (d ≫ k) D, h₄]

namespace Sheaf

universe w₀ v₄ u₄

/-- Equal morphisms of sheaves of types agree on every section. -/
theorem sections_congr {C : Type u₄} [Category.{v₄} C] {J : GrothendieckTopology C}
    {A E : Sheaf J (Type w₀)} {m m' : A ⟶ E} (h : m = m') (X : Cᵒᵖ)
    (s : (sectionsFunctor J X).obj A) :
    (sectionsFunctor J X).map m s = (sectionsFunctor J X).map m' s :=
  congrArg (fun n ↦ (sectionsFunctor J X).map n s) h

end Sheaf

namespace Functor

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂} {E : Type u₃}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} E]

/-- A functor applied to a composition comparison transported along equalities of functors:
the transports contribute nothing, so the image is the image of the untransported
comparison. -/
theorem map_compIsoCongr_hom_app {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {pq pq' : A₀ ⥤ A₂}
    (hp : p = p') (hq : q = q') (hpq : pq = pq') (P : p ⋙ q ≅ pq) (F : A₂ ⥤ E) (M : A₀)
    {T₁ T₂ : E} {t : T₁ ⟶ T₂} (ht : HEq (F.map (P.hom.app M)) t)
    (u : F.obj ((p' ⋙ q').obj M) ⟶ F.obj (pq'.obj M)) (hu : HEq u t) :
    F.map ((compIsoCongr hp hq hpq P).hom.app M) = u := by
  subst hp hq hpq
  have h1 : F.map ((compIsoCongr (rfl : p = p) (rfl : q = q) (rfl : pq = pq) P).hom.app M) =
      F.map (P.hom.app M) := by simp [compIsoCongr]
  exact h1.trans (eq_of_heq (ht.trans hu.symm))

end Functor

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comp

variable {X Y Z : AlgebraicSpaces B S hS}

/-- Equal morphisms of sheaves of modules have equal underlying morphisms of sheaves of
sets. -/
theorem moduleSheafFunctor_map_congr {W : AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS W.1 W.2} {c c' : M ⟶ N} (h : c = c') :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map c =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map c' :=
  congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS W)).map h

/-- The comparison of direct images of modules at the level of the morphisms of ringed topoi is
the geometric comparison of Stacks 03G2, part (3), on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((pushforwardModulesCompAt B S hS f g).hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  ((congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        (show (pushforwardModulesCompAt B S hS f g).hom.app F =
            (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
                (smallEtaleRingedToposHom B S hS g)).inv.app F ≫
              (pushforwardModulesCompTransport B S hS f g).hom.app F from rfl)).trans
      (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map_comp _ _).trans
        (congrArg₂ (fun a b ↦ a ≫ b)
          (moduleSheafFunctor_map_pushforwardModulesCompIso_inv_app B S hS f g F)
          (moduleSheafFunctor_map_pushforwardModulesCompTransport_hom_app B S hS f g F)))).trans
    (Category.id_comp _)

/-- The sheaf of sets underlying an iterated direct image of modules along the morphisms of
ringed topoi of Stacks 03G8 is the iterated direct image of sheaves of sets. -/
theorem moduleSheaf_pushforwardModules_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
        (((smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
          (smallEtaleRingedToposHom B S hS g).pushforwardModules).obj F) =
      (smallToposMorphismTypeU B S hS g).pushforward.obj
        ((smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := rfl

/-- The sheaf of sets underlying the direct image of modules along the morphism of ringed topoi
of Stacks 03G8 of a composite is the direct image of sheaves of sets of the composite. -/
theorem moduleSheaf_pushforwardModules_obj (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
        ((smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModules.obj F) := rfl

/-- The sheaf of sets underlying an iterated direct image of `𝒪`-modules is the iterated direct
image of sheaves of sets. -/
theorem moduleSheaf_modulePushforward_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
        ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F) =
      (smallToposMorphismTypeU B S hS g).pushforward.obj
        ((smallToposMorphismTypeU B S hS f).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) := rfl

/-- The sheaf of sets underlying the direct image of `𝒪`-modules along a composite is the
direct image of sheaves of sets along the composite. -/
theorem moduleSheaf_modulePushforward_obj (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.obj
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
        ((modulePushforward B S hS (f ≫ g)).obj F) := rfl

/-- The geometric comparison of Stacks 03G2, part (3), read on the iterated direct image of
modules taken through the morphisms of ringed topoi of Stacks 03G8: the underlying sheaf of
sets is the iterated direct image, so this is reflexivity. -/
theorem heq_smallToposMorphismTypeU_comp_hom_app_pushforwardModules (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq (show (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            (((smallEtaleRingedToposHom B S hS f).pushforwardModules ⋙
              (smallEtaleRingedToposHom B S hS g).pushforwardModules).obj F) ⟶
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            ((smallEtaleRingedToposHom B S hS (f ≫ g)).pushforwardModules.obj F) from
        (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
      (show (smallToposMorphismTypeU B S hS g).pushforward.obj
            ((smallToposMorphismTypeU B S hS f).pushforward.obj
              ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) ⟶
          (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.obj
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) from
        (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  HEq.refl _

/-- The geometric comparison of Stacks 03G2, part (3), read on the iterated direct image of
`𝒪`-modules: the underlying sheaf of sets is the iterated direct image, so this is
reflexivity. -/
theorem heq_smallToposMorphismTypeU_comp_hom_app_modulePushforward (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    HEq (show (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            ((modulePushforward B S hS f ⋙ modulePushforward B S hS g).obj F) ⟶
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).obj
            ((modulePushforward B S hS (f ≫ g)).obj F) from
        (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
      (show (smallToposMorphismTypeU B S hS g).pushforward.obj
            ((smallToposMorphismTypeU B S hS f).pushforward.obj
              ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) ⟶
          (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.obj
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) from
        (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) :=
  HEq.refl _

/-- **Stacks 03LU.**  The comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images of `𝒪`-modules is
the geometric comparison `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2,
part (3), on underlying sheaves of sets.  The comparison appears in the transported form that
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` identifies it with, and
`AlgebraicGeometry.Space.modulePushforwardCompIso_hom_app_eq` is that identification at a
single module. -/
@[stacks 03LU "the composition comparison for direct images is the geometric comparison"]
theorem moduleSheafFunctor_map_compIsoCongr_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS f)
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
          (pushforwardModulesCompAt B S hS f g)).hom.app F) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  CategoryTheory.Functor.map_compIsoCongr_hom_app
    (pushforwardModules_eq_modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS g)
    (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
    (pushforwardModulesCompAt B S hS f g)
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)) F
    (heq_of_eq (moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app B S hS f g F))
    ((smallToposMorphismTypeU_comp B S hS f g).hom.app
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F))
    ((heq_smallToposMorphismTypeU_comp_hom_app_modulePushforward B S hS f g F).trans
      (heq_smallToposMorphismTypeU_comp_hom_app_pushforwardModules B S hS f g F).symm)

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` on the underlying
natural transformations. -/
theorem modulePushforwardCompIso_hom_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePushforwardCompIso B S hS f g).hom =
      (CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS f)
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
          (pushforwardModulesCompAt B S hS f g)).hom :=
  congrArg Iso.hom (modulePushforwardCompIso_eq_compIsoCongr B S hS f g)

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr` at a single module. -/
theorem modulePushforwardCompIso_hom_app_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardCompIso B S hS f g).hom.app F =
      (CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS f)
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
          (pushforwardModulesCompAt B S hS f g)).hom.app F :=
  CategoryTheory.NatTrans.congr_app (modulePushforwardCompIso_hom_eq B S hS f g) F

/-- `AlgebraicGeometry.Space.moduleSheafFunctor_map_compIsoCongr_hom_app` with its equation
read at the direct images of sheaves of sets. -/
theorem moduleSheafFunctor_map_compIsoCongr_hom_app' (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (show (smallToposMorphismTypeU B S hS g).pushforward.obj
          ((smallToposMorphismTypeU B S hS f).pushforward.obj
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)) ⟶
        (smallToposMorphismTypeU B S hS (f ≫ g)).pushforward.obj
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) from
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS f)
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
          (pushforwardModulesCompAt B S hS f g)).hom.app F)) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F) :=
  moduleSheafFunctor_map_compIsoCongr_hom_app B S hS f g F

/-- **Stacks 03G8**, compatibility with composition, at the level of sheaves of sets. -/
theorem structureSharpSet_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSharpSet B S hS g ≫
        (smallEtaleDirectImage B S hS g).map (structureSharpSet B S hS f) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) =
      structureSharpSet B S hS (f ≫ g) := by
  refine (Iso.cancel_iso_hom_right _ _
    ((smallEtaleDirectImageRanIso B S hS (f ≫ g)).app (structureSetSheaf B S hS X))).mp ?_
  refine Eq.trans ?_ (structureSharpSet_comp_ranIso B S hS (f ≫ g)).symm
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans
    (congrArg (fun m ↦ structureSharpSet B S hS g ≫ m) (Category.assoc _ _ _)) ?_)
  exact (structureSharpSet_comp_formula B S hS f g).trans
    (structureSharpRanSet_comp B S hS f g)

/-- The direct image of modules is the direct image of sheaves of sets on the underlying
sheaves. -/
theorem moduleSheafFunctor_map_modulePushforward_map (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2} (m : M ⟶ N) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforward B S hS f).map m) =
      (smallEtaleDirectImage B S hS f).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map m) := rfl

/-- `AlgebraicGeometry.Space.modulePullbackCompIso` is the comparison of the two left adjoints
of `(f ≫ g)_*`, stated as an equation. -/
theorem modulePullbackCompIso_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompIso B S hS f g =
      Adjunction.leftAdjointUniq (moduleCompAdjunction B S hS f g)
        (modulePullbackAdjunction B S hS (f ≫ g)) := rfl

/-- `AlgebraicGeometry.Space.moduleCompAdjunction` written out. -/
theorem moduleCompAdjunction_eq (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleCompAdjunction B S hS f g =
      ((modulePullbackAdjunction B S hS g).comp
        (modulePullbackAdjunction B S hS f)).ofNatIsoRight
          (modulePushforwardCompIso B S hS f g) := rfl

/-- The transpose of a morphism out of `(f ≫ g)^*M`, written through the comparison of inverse
images: it is the iterated transpose, followed by the comparison of direct images. -/
theorem homEquiv_modulePullbackCompIso_inv_app_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (ψ : (modulePullback B S hS g ⋙ modulePullback B S hS f).obj M ⟶ N) :
    (modulePullbackAdjunction B S hS (f ≫ g)).homEquiv M N
        ((modulePullbackCompIso B S hS f g).inv.app M ≫ ψ) =
      (modulePullbackAdjunction B S hS g).homEquiv M _
          ((modulePullbackAdjunction B S hS f).homEquiv _ N ψ) ≫
        (modulePushforwardCompIso B S hS f g).hom.app N := by
  rw [modulePullbackCompIso_eq, Adjunction.homEquiv_leftAdjointUniq_inv_app_comp,
    moduleCompAdjunction_eq, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  rfl

end Comp

section Differentials

variable {X Y X' Y' X'' Y'' : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.pushforwardUniversalDerivationHom` written out. -/
theorem pushforwardUniversalDerivationHom_eq (f : X' ⟶ X) (p' : X' ⟶ Y') :
    pushforwardUniversalDerivationHom B S hS f p' =
      structureSharpSet B S hS f ≫
        (smallEtaleDirectImage B S hS f).map (universalDerivationHom B S hS p') := rfl

/-- **Stacks 04CX**, the characterizing property on underlying sheaves of sets: the universal
derivation followed by the transpose of `c_f` is `f♯` followed by the direct image of
`d_{X'/Y'}`. -/
theorem universalDerivationHom_comp_homEquiv (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    {c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (h : IsSheafOfDifferentialsMap B S hS f p p' c) :
    universalDerivationHom B S hS p ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
            (sheafOfDifferentials B S hS p') c) =
      structureSharpSet B S hS f ≫
        (smallEtaleDirectImage B S hS f).map (universalDerivationHom B S hS p') :=
  CategoryTheory.Sheaf.hom_ext_sections (fun U t ↦ h U t)

/-- The transpose of `c_g ∘ g^*c_f` for the outer square: the transpose of `c_f`, the direct
image of the transpose of `c_g`, and the comparison of direct images. -/
theorem homEquiv_comp_modulePullbackCompIso_inv_app (f : X' ⟶ X) (g : X'' ⟶ X') (p : X ⟶ Y)
    (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    (cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p')
    (cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p'') :
    (modulePullbackAdjunction B S hS (g ≫ f)).homEquiv
        (sheafOfDifferentials B S hS p) (sheafOfDifferentials B S hS p'')
        ((modulePullbackCompIso B S hS g f).inv.app (sheafOfDifferentials B S hS p) ≫
          (modulePullback B S hS g).map cf ≫ cg) =
      (modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
          (sheafOfDifferentials B S hS p') cf ≫
        (modulePushforward B S hS f).map
          ((modulePullbackAdjunction B S hS g).homEquiv (sheafOfDifferentials B S hS p')
            (sheafOfDifferentials B S hS p'') cg) ≫
        (CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS f)
          (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
          (pushforwardModulesCompAt B S hS g f)).hom.app
          (sheafOfDifferentials B S hS p'') := by
  rw [homEquiv_modulePullbackCompIso_inv_app_comp, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Category.assoc,
    modulePushforwardCompIso_hom_app_eq]

/-- The naturality of the geometric comparison of Stacks 03G2, part (3), at the universal
derivation. -/
theorem smallToposMorphismTypeU_comp_hom_naturality_universalDerivationHom (f : X' ⟶ X)
    (g : X'' ⟶ X') (p'' : X'' ⟶ Y'') :
    (smallEtaleDirectImage B S hS f).map
        ((smallEtaleDirectImage B S hS g).map (universalDerivationHom B S hS p'')) ≫
        (smallToposMorphismTypeU_comp B S hS g f).hom.app
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X'')).obj
            (sheafOfDifferentials B S hS p'')) =
      (smallToposMorphismTypeU_comp B S hS g f).hom.app (structureSetSheaf B S hS X'') ≫
        (smallEtaleDirectImage B S hS (g ≫ f)).map (universalDerivationHom B S hS p'') :=
  (smallToposMorphismTypeU_comp B S hS g f).hom.naturality _

/-- An iterated direct image of modules followed by the comparison of direct images, on
underlying sheaves of sets: the three factors separately. -/
theorem moduleSheafFunctor_map_comp_modulePushforward_map (f : X' ⟶ X) (g : X'' ⟶ X')
    {M : Modules.{u, u} B S hS X.1 X.2} {N : Modules.{u, u} B S hS X'.1 X'.2}
    {P : Modules.{u, u} B S hS X''.1 X''.2} (a : M ⟶ (modulePushforward B S hS f).obj N)
    (b : N ⟶ (modulePushforward B S hS g).obj P) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        (a ≫ (modulePushforward B S hS f).map b ≫
          (CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS f)
          (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
          (pushforwardModulesCompAt B S hS g f)).hom.app P) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map a ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePushforward B S hS f).map b) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((CategoryTheory.Functor.compIsoCongr
          (pushforwardModules_eq_modulePushforward B S hS g)
          (pushforwardModules_eq_modulePushforward B S hS f)
          (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
          (pushforwardModulesCompAt B S hS g f)).hom.app P) :=
  ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).trans
    (CategoryTheory.comp_congr_of_eq _
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _))

/-- The direct image along `f` of the characterizing property of `c_g`, with the direct image
of the transpose written through the direct image of modules. -/
theorem smallEtaleDirectImage_map_universalDerivationHom_comp (f : X' ⟶ X) (g : X'' ⟶ X')
    (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''}
    (hg : IsSheafOfDifferentialsMap B S hS g p' p'' cg) :
    (smallEtaleDirectImage B S hS f).map (universalDerivationHom B S hS p') ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePushforward B S hS f).map
            ((modulePullbackAdjunction B S hS g).homEquiv (sheafOfDifferentials B S hS p')
              (sheafOfDifferentials B S hS p'') cg)) =
      (smallEtaleDirectImage B S hS f).map (structureSharpSet B S hS g) ≫
        (smallEtaleDirectImage B S hS f).map
          ((smallEtaleDirectImage B S hS g).map (universalDerivationHom B S hS p'')) :=
  (CategoryTheory.comp_congr_of_eq _
      (moduleSheafFunctor_map_modulePushforward_map B S hS f _)).trans
    ((((smallEtaleDirectImage B S hS f).map_comp _ _).symm.trans
        (congrArg (smallEtaleDirectImage B S hS f).map
          (universalDerivationHom_comp_homEquiv B S hS g p' p'' hg))).trans
      ((smallEtaleDirectImage B S hS f).map_comp _ _))

/-- The transpose of `c_g ∘ g^*c_f`, composed with the universal derivation, written through
the transposes of `c_f` and `c_g`. -/
theorem universalDerivationHom_comp_transpose_comp_aux (f : X' ⟶ X) (g : X'' ⟶ X') (p : X ⟶ Y)
    (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''} :
    universalDerivationHom B S hS p ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackAdjunction B S hS (g ≫ f)).homEquiv
            (sheafOfDifferentials B S hS p) (sheafOfDifferentials B S hS p'')
            ((modulePullbackCompIso B S hS g f).inv.app (sheafOfDifferentials B S hS p) ≫
              (modulePullback B S hS g).map cf ≫ cg)) =
      universalDerivationHom B S hS p ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
          (sheafOfDifferentials B S hS p') cf ≫
            (modulePushforward B S hS f).map
              ((modulePullbackAdjunction B S hS g).homEquiv (sheafOfDifferentials B S hS p')
            (sheafOfDifferentials B S hS p'') cg) ≫
            (CategoryTheory.Functor.compIsoCongr
            (pushforwardModules_eq_modulePushforward B S hS g)
            (pushforwardModules_eq_modulePushforward B S hS f)
            (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
            (pushforwardModulesCompAt B S hS g f)).hom.app
              (sheafOfDifferentials B S hS p'')) :=
  CategoryTheory.comp_congr_of_eq _
    (moduleSheafFunctor_map_congr B S hS
      (homEquiv_comp_modulePullbackCompIso_inv_app B S hS f g p p' p'' cf cg))

/-- The naturality of the geometric comparison of Stacks 03G2, part (3), with the comparison
replaced by the comparison of direct images of modules on underlying sheaves of sets. -/
theorem smallToposMorphismTypeU_comp_hom_naturality_universalDerivationHom' (f : X' ⟶ X)
    (g : X'' ⟶ X') (p'' : X'' ⟶ Y'') :
    (smallEtaleDirectImage B S hS f).map
        ((smallEtaleDirectImage B S hS g).map (universalDerivationHom B S hS p'')) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((CategoryTheory.Functor.compIsoCongr
            (pushforwardModules_eq_modulePushforward B S hS g)
            (pushforwardModules_eq_modulePushforward B S hS f)
            (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
            (pushforwardModulesCompAt B S hS g f)).hom.app
            (sheafOfDifferentials B S hS p'')) =
      (smallToposMorphismTypeU_comp B S hS g f).hom.app (structureSetSheaf B S hS X'') ≫
        (smallEtaleDirectImage B S hS (g ≫ f)).map (universalDerivationHom B S hS p'') :=
  (CategoryTheory.comp_congr_of_eq _
      (moduleSheafFunctor_map_compIsoCongr_hom_app' B S hS g f
        (sheafOfDifferentials B S hS p''))).trans
    (smallToposMorphismTypeU_comp_hom_naturality_universalDerivationHom B S hS f g p'')

/-- The first half of the substitution chain of Stacks 05Z7: the characterizing property of
`c_f`, then that of `c_g` along the direct image.  Read from the sheaves of sets, so that its
equation is typed at the direct images of sheaves of sets. -/
theorem universalDerivationHom_comp_transpose_comp_half₁ (f : X' ⟶ X) (g : X'' ⟶ X') (p : X ⟶ Y)
    (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''}
    (hf : IsSheafOfDifferentialsMap B S hS f p p' cf)
    (hg : IsSheafOfDifferentialsMap B S hS g p' p'' cg) :
      structureSharpSet B S hS f ≫
        (smallEtaleDirectImage B S hS f).map (structureSharpSet B S hS g) ≫
        (smallEtaleDirectImage B S hS f).map
          ((smallEtaleDirectImage B S hS g).map (universalDerivationHom B S hS p'')) =
      universalDerivationHom B S hS p ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
            (sheafOfDifferentials B S hS p') cf) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePushforward B S hS f).map
            ((modulePullbackAdjunction B S hS g).homEquiv (sheafOfDifferentials B S hS p')
              (sheafOfDifferentials B S hS p'') cg)) :=
  (CategoryTheory.comp_eq_of_factorizations₁
    (universalDerivationHom_comp_homEquiv B S hS f p p' hf)
    (smallEtaleDirectImage_map_universalDerivationHom_comp B S hS f g p' p'' hg)).symm

/-- The second half of the substitution chain of Stacks 05Z7: the naturality of the geometric
comparison of Stacks 03G2, part (3), then the composition law for the structure map. -/
theorem universalDerivationHom_comp_transpose_comp_half₂ (f : X' ⟶ X) (g : X'' ⟶ X')
    (p'' : X'' ⟶ Y'') :
    (structureSharpSet B S hS f ≫
        (smallEtaleDirectImage B S hS f).map (structureSharpSet B S hS g) ≫
        (smallEtaleDirectImage B S hS f).map
          ((smallEtaleDirectImage B S hS g).map (universalDerivationHom B S hS p''))) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((CategoryTheory.Functor.compIsoCongr
            (pushforwardModules_eq_modulePushforward B S hS g)
            (pushforwardModules_eq_modulePushforward B S hS f)
            (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
            (pushforwardModulesCompAt B S hS g f)).hom.app
            (sheafOfDifferentials B S hS p'')) =
      structureSharpSet B S hS (g ≫ f) ≫
        (smallEtaleDirectImage B S hS (g ≫ f)).map
          (universalDerivationHom B S hS p'') :=
  CategoryTheory.comp_eq_of_factorizations₂
    (smallToposMorphismTypeU_comp_hom_naturality_universalDerivationHom' B S hS f g p'')
    (structureSharpSet_comp B S hS g f)

/-- The transpose of `c_g ∘ g^*c_f` for the outer square, read on underlying sheaves of sets
and regrouped: the universal derivation, the transpose of `c_f`, the direct image of the
transpose of `c_g`, and then the comparison of direct images, all spelled with the underlying
sheaf of sets of a direct image *of modules*. -/
theorem universalDerivationHom_comp_transpose_comp_factored (f : X' ⟶ X) (g : X'' ⟶ X')
    (p : X ⟶ Y) (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''} :
    universalDerivationHom B S hS p ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackAdjunction B S hS (g ≫ f)).homEquiv
            (sheafOfDifferentials B S hS p) (sheafOfDifferentials B S hS p'')
            ((modulePullbackCompIso B S hS g f).inv.app (sheafOfDifferentials B S hS p) ≫
              (modulePullback B S hS g).map cf ≫ cg)) =
      (universalDerivationHom B S hS p ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
              (sheafOfDifferentials B S hS p') cf) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((modulePushforward B S hS f).map
              ((modulePullbackAdjunction B S hS g).homEquiv (sheafOfDifferentials B S hS p')
                (sheafOfDifferentials B S hS p'') cg))) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((CategoryTheory.Functor.compIsoCongr
            (pushforwardModules_eq_modulePushforward B S hS g)
            (pushforwardModules_eq_modulePushforward B S hS f)
            (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
            (pushforwardModulesCompAt B S hS g f)).hom.app
            (sheafOfDifferentials B S hS p'')) :=
  (universalDerivationHom_comp_transpose_comp_aux B S hS f g p p' p'').trans
    ((CategoryTheory.comp_congr_of_eq _
        (moduleSheafFunctor_map_comp_modulePushforward_map B S hS f g
          ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
            (sheafOfDifferentials B S hS p') cf)
          ((modulePullbackAdjunction B S hS g).homEquiv (sheafOfDifferentials B S hS p')
            (sheafOfDifferentials B S hS p'') cg))).trans
      (CategoryTheory.comp_assoc₃ _ _ _ _))

/-- The first half of the substitution chain of Stacks 05Z7, read on a single local section
`t` over an étale chart `U` and composed with the comparison of direct images.  The two
spellings of the iterated direct image are identified here on *sections*, where the
identification is between two types, rather than between two sheaves of types. -/
theorem universalDerivationHom_comp_transpose_comp_half₁_sections (f : X' ⟶ X) (g : X'' ⟶ X')
    (p : X ⟶ Y) (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''}
    (hf : IsSheafOfDifferentialsMap B S hS f p p' cf)
    (hg : IsSheafOfDifferentialsMap B S hS g p' p'' cg)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U) :
    (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        ((universalDerivationHom B S hS p ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
              (sheafOfDifferentials B S hS p') cf) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((modulePushforward B S hS f).map
              ((modulePullbackAdjunction B S hS g).homEquiv (sheafOfDifferentials B S hS p')
                (sheafOfDifferentials B S hS p'') cg))) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((CategoryTheory.Functor.compIsoCongr
              (pushforwardModules_eq_modulePushforward B S hS g)
              (pushforwardModules_eq_modulePushforward B S hS f)
              (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
              (pushforwardModulesCompAt B S hS g f)).hom.app
              (sheafOfDifferentials B S hS p''))) t =
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
        ((structureSharpSet B S hS f ≫
          (smallEtaleDirectImage B S hS f).map (structureSharpSet B S hS g) ≫
          (smallEtaleDirectImage B S hS f).map
            ((smallEtaleDirectImage B S hS g).map
              (universalDerivationHom B S hS p''))) ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((CategoryTheory.Functor.compIsoCongr
              (pushforwardModules_eq_modulePushforward B S hS g)
              (pushforwardModules_eq_modulePushforward B S hS f)
              (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
              (pushforwardModulesCompAt B S hS g f)).hom.app
              (sheafOfDifferentials B S hS p''))) t :=
  congrArg
    ((Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) U).map
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((CategoryTheory.Functor.compIsoCongr
            (pushforwardModules_eq_modulePushforward B S hS g)
            (pushforwardModules_eq_modulePushforward B S hS f)
            (pushforwardModules_eq_modulePushforward B S hS (g ≫ f))
            (pushforwardModulesCompAt B S hS g f)).hom.app
            (sheafOfDifferentials B S hS p''))))
    (Sheaf.sections_congr
      (universalDerivationHom_comp_transpose_comp_half₁ B S hS f g p p' p'' hf hg).symm U t)

/-- **Stacks 05Z7**, the characterization: for two stacked commutative squares, the composite
`c_g ∘ g^*c_f` of the comparison maps of the inner squares, read through the comparison
`(g ≫ f)^* ≅ g^*f^*` of inverse images of Stacks 03LU, has the characterizing property of
Stacks 04CX for the outer square. -/
@[stacks 05Z7 "the composite satisfies the characterization of `c_{g ≫ f}`"]
theorem isSheafOfDifferentialsMap_comp (f : X' ⟶ X) (g : X'' ⟶ X') (p : X ⟶ Y) (p' : X' ⟶ Y')
    (p'' : X'' ⟶ Y'')
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''}
    (hf : IsSheafOfDifferentialsMap B S hS f p p' cf)
    (hg : IsSheafOfDifferentialsMap B S hS g p' p'' cg) :
    IsSheafOfDifferentialsMap B S hS (g ≫ f) p p''
      ((modulePullbackCompIso B S hS g f).inv.app (sheafOfDifferentials B S hS p) ≫
        (modulePullback B S hS g).map cf ≫ cg) :=
  fun U t ↦ (Sheaf.sections_congr (universalDerivationHom_comp_transpose_comp_factored
      B S hS f g p p' p'' (cf := cf) (cg := cg)) U t).trans
    ((universalDerivationHom_comp_transpose_comp_half₁_sections B S hS f g p p' p'' hf hg U t).trans
      (Sheaf.sections_congr
        (universalDerivationHom_comp_transpose_comp_half₂ B S hS f g p'') U t))

/-- **Stacks 05Z7.**  The comparison maps of Stacks 04CX compose: for two stacked commutative
squares with top edges `g : X'' ⟶ X'` and `f : X' ⟶ X`, the comparison map of the outer square
is the comparison map of the inner right square pulled back along `g`, followed by the
comparison map of the inner left square, the two being composable through the comparison
`(g ≫ f)^* ≅ g^*f^*` of Stacks 03LU.  Each of the three comparison maps appears through its
characterizing property of Stacks 04CX, which determines it uniquely. -/
@[stacks 05Z7]
theorem eq_comp_of_isSheafOfDifferentialsMap (f : X' ⟶ X) (g : X'' ⟶ X') (p : X ⟶ Y)
    (p' : X' ⟶ Y') (p'' : X'' ⟶ Y'')
    {c : (modulePullback B S hS (g ≫ f)).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p''}
    {cf : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    {cg : (modulePullback B S hS g).obj (sheafOfDifferentials B S hS p') ⟶
      sheafOfDifferentials B S hS p''}
    (hc : IsSheafOfDifferentialsMap B S hS (g ≫ f) p p'' c)
    (hf : IsSheafOfDifferentialsMap B S hS f p p' cf)
    (hg : IsSheafOfDifferentialsMap B S hS g p' p'' cg) :
    c = (modulePullbackCompIso B S hS g f).inv.app (sheafOfDifferentials B S hS p) ≫
      (modulePullback B S hS g).map cf ≫ cg :=
  eq_of_isSheafOfDifferentialsMap B S hS (g ≫ f) p p'' hc
    (isSheafOfDifferentialsMap_comp B S hS f g p p' p'' hf hg)

end Differentials

end AlgebraicGeometry.Space

end
