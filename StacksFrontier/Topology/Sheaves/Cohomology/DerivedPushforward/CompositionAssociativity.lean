module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Associativity of the pushforward-composition comparison

For morphisms of ringed spaces `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W` there are two ways to
identify the pushforward `(f ≫ g ≫ h)_*` of sheaves of modules along the composite with the
threefold composite `f_* ⋙ g_* ⋙ h_*` of degreewise pushforwards: through `g ≫ h`, or through
`f ≫ g`.  This file proves that they agree, on complexes and on the unbounded homotopy category,
and describes the inverse of the composition isomorphism
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso` of derived
pushforward at a complex.  It deduces the cocycle identity and the unit laws for the composition
isomorphisms of derived pushforward and of derived pullback.

## Main definitions

* `Stacks.Cohomology.DerivedPushforwardAssociativity.pushforwardCompComplex`: the comparison
  `(f ≫ g)_* ⟶ f_* ⋙ g_*` on complexes of sheaves of modules.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.pushforwardCompHomotopy`: the same
  comparison on the unbounded homotopy categories.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.modulePushforwardIdComplex` and
  `modulePushforwardIdHomotopy`: the unit isomorphism
  `RingedSpaceModuleAdjunction.modulePushforwardId` of degreewise pushforward,
  `(𝟙 X)_* ≅ 𝟭`, on complexes and on the unbounded homotopy category.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso`: the unit
  isomorphism `R(𝟙 X)_* ≅ 𝟭` for derived pushforward.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso`: the unit isomorphism
  `L(𝟙 X)^* ≅ 𝟭` for derived pullback.

## Main results

* `Stacks.Cohomology.DerivedPushforwardAssociativity.pushforwardCompComplex_assoc`: the cocycle
  identity on complexes.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.pushforwardCompHomotopy_assoc`: the cocycle
  identity on the unbounded homotopy categories.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardUnit_comp_compIso_inv`:
  the comparison for `R(f ≫ g)_*`, followed by the inverse of the composition isomorphism of
  Tag 079W, is the degreewise comparison followed by the comparisons for `Rg_*` and for `Rf_*`.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardCompIso_assoc`: the
  cocycle identity for the composition isomorphism of Tag 079W on the unbounded derived
  categories.
* `derivedPullbackCompIsoCanonical_eq_leftAdjointCompIso`: the canonical composition isomorphism
  for derived pullback is the left-adjoint companion of the one for derived pushforward.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc`:
  the resulting cocycle identity for derived pullback, the coherence of Tag 0D5S.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.pushforwardCompComplex_id_comp`,
  `pushforwardCompComplex_comp_id`, `pushforwardCompHomotopy_id_comp` and
  `pushforwardCompHomotopy_comp_id`: the two unit laws for the degreewise comparison, on
  complexes and on the unbounded homotopy categories.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardCompIso_id_comp` and
  `derivedPushforwardCompIso_comp_id`: the two unit laws for the composition isomorphism of
  Tag 079W.
* `Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_id_comp`
  and `derivedPullbackCompIsoCanonical_comp_id`: the resulting unit laws for derived pullback,
  the unit coherence of Tag 0D5S.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPushforwardComposition
  (derivedPushforwardCompUnit_comp_derivedPushforwardCompIso derivedPushforwardCompUnit_app)

namespace Stacks.Cohomology.DerivedPushforwardAssociativity

universe u

noncomputable section

/-- An identity of morphisms of complexes holds in the homotopy category. -/
theorem quotient_map_congr {V : Type*} [Category V] [Preadditive V] {ι : Type*}
    {c : ComplexShape ι} {A B : HomologicalComplex V c} {p q : A ⟶ B} (e : p = q) :
    (HomotopyCategory.quotient V c).map p = (HomotopyCategory.quotient V c).map q :=
  congrArg (HomotopyCategory.quotient V c).map e

variable {X Y Z W : RingedSpace.{u, u}}

/-- The comparison `(f ≫ g)_* ⟶ f_* ⋙ g_*` of degreewise pushforwards of sheaves of modules, on
complexes. -/
abbrev pushforwardCompComplex (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePushforward (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso (modulePushforwardComp f g)
    (ComplexShape.up ℤ)).inv

/-- The comparison `(f ≫ g)_* ⟶ f_* ⋙ g_*` of degreewise pushforwards of sheaves of modules, on
the unbounded homotopy categories. -/
abbrev pushforwardCompHomotopy (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePushforward (f ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp f g)
    (ComplexShape.up ℤ)).inv

/-- Each component of `pushforwardCompComplex f g` is the identity of the pushforward along
`f ≫ g`. -/
theorem pushforwardCompComplex_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (pushforwardCompComplex f g).app K =
      𝟙 (((modulePushforward (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  rfl

/-- Each component of `pushforwardCompComplex f g` is the identity of the iterated pushforward
along `f` and then `g`. -/
theorem pushforwardCompComplex_app' (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (pushforwardCompComplex f g).app K =
      𝟙 (((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  rfl

/-- The cocycle identity for the pushforward-composition comparison, on complexes:
comparing `(f ≫ g ≫ h)_*` with `f_* ⋙ (g ≫ h)_*` and then with `f_* ⋙ g_* ⋙ h_*` agrees with
comparing it with `(f ≫ g)_* ⋙ h_*` and then pushing the comparison for `f ≫ g` forward along
`h`. -/
theorem pushforwardCompComplex_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (pushforwardCompComplex f (g ≫ h)).app K ≫
        (pushforwardCompComplex g h).app
          (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (pushforwardCompComplex (f ≫ g) h).app K ≫
        ((modulePushforward h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((pushforwardCompComplex f g).app K) :=
  HomologicalComplex.hom_ext _ _ fun _ => rfl

/-- The cocycle identity for the pushforward-composition comparison, on the unbounded homotopy
categories: comparing `(f ≫ g ≫ h)_*` with `f_* ⋙ (g ≫ h)_*` and then with `f_* ⋙ g_* ⋙ h_*`
agrees with comparing it with `(f ≫ g)_* ⋙ h_*` and then pushing the comparison for `f ≫ g`
forward along `h`. -/
theorem pushforwardCompHomotopy_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (pushforwardCompHomotopy f (g ≫ h)).app K ≫
        (pushforwardCompHomotopy g h).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (pushforwardCompHomotopy (f ≫ g) h).app K ≫
        ((modulePushforward h).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((pushforwardCompHomotopy f g).app K) := by
  obtain ⟨K⟩ := K
  exact quotient_map_congr (pushforwardCompComplex_assoc f g h K)

attribute [local instance] HasDerivedCategory.standard

/-- The comparison from degreewise pushforward along `f ≫ g` to `R(f ≫ g)_*`, followed by the
inverse of the composition isomorphism `derivedPushforwardCompIso f g`, is the degreewise
comparison `(f ≫ g)_* ⟶ f_* ⋙ g_*`, then the comparison for `Rg_*`, then `Rg_*` of the
comparison for `Rf_*`. -/
theorem derivedPushforwardUnit_comp_compIso_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (f ≫ g)).app K ≫
        (derivedPushforwardCompIso f g).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((pushforwardCompHomotopy f g).app K) ≫
        (derivedPushforwardUnit g).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (derivedPushforward g).map ((derivedPushforwardUnit f).app K) := by
  rw [← derivedPushforwardCompUnit_comp_derivedPushforwardCompIso f g K, Category.assoc,
    Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.comp_id, derivedPushforwardCompUnit_app]

/-- `derivedPushforwardUnit_comp_compIso_inv` at the pair `(f ≫ g, h)`, with the threefold
composite written in the right-bracketed form `f ≫ g ≫ h`. -/
theorem derivedPushforwardUnit_comp_compIso_inv_left (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (f ≫ g ≫ h)).app K ≫
        (derivedPushforwardCompIso (f ≫ g) h).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((pushforwardCompHomotopy (f ≫ g) h).app K) ≫
        (derivedPushforwardUnit h).app
          (((modulePushforward (f ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (derivedPushforward h).map ((derivedPushforwardUnit (f ≫ g)).app K) :=
  derivedPushforwardUnit_comp_compIso_inv (f ≫ g) h K

/-- A naturality chase with every term a variable: a morphism `c` that factors as
`p ≫ q ≫ T.map a` meets a natural transformation `θ : T ⟶ S` by moving `θ` across the naturality
square at `a` and then rewriting the exposed two-factor head `q ≫ θ.app A`. -/
private theorem comp_app_of_naturality {D E : Type*} [Category D] [Category E]
    {T S : D ⥤ E} (θ : T ⟶ S) {A B : D} {a : A ⟶ B} {V U R₁ R₂ : E}
    {c : V ⟶ T.obj B} {p : V ⟶ U} {q : U ⟶ T.obj A} {r : U ⟶ R₁} {s : R₁ ⟶ R₂}
    {t : R₂ ⟶ S.obj A} (h₁ : c = p ≫ q ≫ T.map a) (h₂ : q ≫ θ.app A = r ≫ s ≫ t) :
    c ≫ θ.app B = p ≫ r ≫ s ≫ t ≫ S.map a := by
  have hn : T.map a ≫ θ.app B = θ.app A ≫ S.map a := θ.naturality a
  rw [h₁]
  simp only [Category.assoc, hn, reassoc_of% h₂]

/-- The same chase one level further out: a morphism `c` that factors as `p ≫ e ≫ F.map m` is
composed with `F.map n`, and the two images under `F` are merged, rewritten by a factorization
of `m ≫ n`, and split again. -/
private theorem comp_map_of_map_comp {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {A B B' R₁ R₂ : C} {m : A ⟶ B} {n : B ⟶ B'} {r : A ⟶ R₁} {s : R₁ ⟶ R₂} {t : R₂ ⟶ B'}
    {V U : E} {c : V ⟶ F.obj B} {p : V ⟶ U} {e : U ⟶ F.obj A}
    (h₁ : c = p ≫ e ≫ F.map m) (h₂ : m ≫ n = r ≫ s ≫ t) :
    c ≫ F.map n = p ≫ e ≫ F.map r ≫ F.map s ≫ F.map t := by
  have h₂' : F.map m ≫ F.map n = F.map r ≫ F.map s ≫ F.map t := by
    rw [← F.map_comp, h₂, F.map_comp, F.map_comp]
  rw [h₁]
  simp only [Category.assoc, h₂']

/-- Naturality of a comparison `η : G ⋙ Q ⟶ Q' ⋙ F`, read against a factorization of `α₁ ≫ α₂`
through `G.map ψ`: the two whiskered images of `ψ` are exchanged across the square. -/
private theorem comp_app_of_whisker_naturality {C D E E' : Type*} [Category C] [Category D]
    [Category E] [Category E'] {G : C ⥤ E} {Q : E ⥤ E'} {Q' : C ⥤ D} {F : D ⥤ E'}
    (η : G ⋙ Q ⟶ Q' ⋙ F) {A B : C} {ψ : A ⟶ B} {T M : E} {α₁ : T ⟶ M} {α₂ : M ⟶ G.obj B}
    {β : T ⟶ G.obj A} (hα : α₁ ≫ α₂ = β ≫ G.map ψ) :
    Q.map α₁ ≫ Q.map α₂ ≫ η.app B = Q.map β ≫ η.app A ≫ F.map (Q'.map ψ) := by
  have hn : Q.map (G.map ψ) ≫ η.app B = η.app A ≫ F.map (Q'.map ψ) := η.naturality ψ
  rw [← Category.assoc (Q.map α₁), ← Q.map_comp, hα, Q.map_comp, Category.assoc, hn]

/-- Two five-factor composites with the same last two factors agree as soon as their
three-factor heads do. -/
private theorem comp_three_congr {E : Type*} [Category E] {V₁ V₂ V₃ V₄ V₅ V₆ V₇ V₈ : E}
    {a₁ : V₁ ⟶ V₂} {a₂ : V₂ ⟶ V₃} {a₃ : V₃ ⟶ V₄} {b₁ : V₁ ⟶ V₅} {b₂ : V₅ ⟶ V₆} {b₃ : V₆ ⟶ V₄}
    (hhead : a₁ ≫ a₂ ≫ a₃ = b₁ ≫ b₂ ≫ b₃) (c : V₄ ⟶ V₇) (d : V₇ ⟶ V₈) :
    a₁ ≫ a₂ ≫ a₃ ≫ c ≫ d = b₁ ≫ b₂ ≫ b₃ ≫ c ≫ d := by
  have hhead' := hhead
  simp only [← Category.assoc] at hhead' ⊢
  rw [hhead']

/-- A three-factor identity, reassociated to the right on both sides. -/
private theorem comp_assoc_both {E : Type*} [Category E] {A B₁ B₂ D B₁' B₂' : E}
    {x : A ⟶ B₁} {y : B₁ ⟶ B₂} {z : B₂ ⟶ D} {x' : A ⟶ B₁'} {y' : B₁' ⟶ B₂'} {z' : B₂' ⟶ D}
    (e : (x ≫ y) ≫ z = (x' ≫ y') ≫ z') : x ≫ y ≫ z = x' ≫ y' ≫ z' := by
  simpa only [Category.assoc] using e

/-- Two isomorphisms into `Rk_*` are equal as soon as their inverses agree after composition with
the comparison from degreewise pushforward, at every object. -/
private theorem iso_ext_of_unit_comp (k : X ⟶ Z)
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    (e₁ e₂ : G ≅ derivedPushforward k)
    (h : ∀ K, (derivedPushforwardUnit k).app K ≫ e₁.inv.app (DerivedCategory.Qh.obj K) =
      (derivedPushforwardUnit k).app K ≫ e₂.inv.app (DerivedCategory.Qh.obj K)) : e₁ = e₂ :=
  Iso.ext ((Iso.inv_eq_inv _ _).1 (Functor.rightDerived_ext (derivedPushforward k)
    (derivedPushforwardUnit k)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ _ _ (NatTrans.ext (funext h))))

/-- The two inverse comparisons `R(f ≫ g ≫ h)_* ⟶ Rf_* ⋙ Rg_* ⋙ Rh_*` agree after composition
with the comparison for `R(f ≫ g ≫ h)_*`. -/
private theorem compIso_inv_app_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (f ≫ g ≫ h)).app K ≫
        (derivedPushforwardCompIso f (g ≫ h)).inv.app (DerivedCategory.Qh.obj K) ≫
          (derivedPushforwardCompIso g h).inv.app
            ((derivedPushforward f).obj (DerivedCategory.Qh.obj K)) =
      (derivedPushforwardUnit (f ≫ g ≫ h)).app K ≫
        (derivedPushforwardCompIso (f ≫ g) h).inv.app (DerivedCategory.Qh.obj K) ≫
          (derivedPushforward h).map
            ((derivedPushforwardCompIso f g).inv.app (DerivedCategory.Qh.obj K)) := by
  refine comp_assoc_both (Eq.trans (comp_app_of_naturality (derivedPushforwardCompIso g h).inv
      (derivedPushforwardUnit_comp_compIso_inv f (g ≫ h) K)
      (derivedPushforwardUnit_comp_compIso_inv g h
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)))
    (Eq.trans ?_ (comp_map_of_map_comp (derivedPushforward h)
      (derivedPushforwardUnit_comp_compIso_inv_left f g h K)
      (derivedPushforwardUnit_comp_compIso_inv f g K)).symm))
  exact comp_three_congr (comp_app_of_whisker_naturality (derivedPushforwardUnit h)
    (pushforwardCompHomotopy_assoc f g h K)) _ _

/-- The cocycle identity for the composition isomorphism of derived pushforward: the two ways of
identifying `Rf_* ⋙ Rg_* ⋙ Rh_*` with `R(f ≫ g ≫ h)_*` — through `g ≫ h` on the left, or through
`f ≫ g` on the right — agree. -/
theorem derivedPushforwardCompIso_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.isoWhiskerLeft (derivedPushforward f) (derivedPushforwardCompIso g h) ≪≫
        derivedPushforwardCompIso f (g ≫ h) =
      (Functor.associator (derivedPushforward f) (derivedPushforward g)
            (derivedPushforward h)).symm ≪≫
        Functor.isoWhiskerRight (derivedPushforwardCompIso f g) (derivedPushforward h) ≪≫
          derivedPushforwardCompIso (f ≫ g) h := by
  refine iso_ext_of_unit_comp _ _ _ fun K => ?_
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id, Category.assoc]
  exact compIso_inv_app_assoc f g h K

/-- A transformation `θ : R₁ ⟶ R₂` is the conjugate of `α : L₂ ⟶ L₁` as soon as, for every `d`,
`L₂.map (θ.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d`. -/
private theorem conjugateEquiv_eq {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (θ : R₁ ⟶ R₂)
    (h : ∀ d, L₂.map (θ.app d) ≫ adj₂.counit.app d = α.app (R₁.obj d) ≫ adj₁.counit.app d) :
    conjugateEquiv adj₁ adj₂ α = θ := by
  ext d
  refine (adj₂.homEquiv (R₁.obj d) d).symm.injective ?_
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit, h d]

/-- Under the composite derived adjunction `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*` and the derived adjunction
for `f ≫ g`, the conjugate of the inverse of the canonical composition isomorphism of derived
pullback is the composition isomorphism `derivedPushforwardCompIso f g` of derived
pushforward. -/
theorem conjugateEquiv_derivedPullbackCompIsoCanonical_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv ((derivedAdjunction g).comp (derivedAdjunction f))
        (derivedAdjunction (f ≫ g))
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).inv =
      (derivedPushforwardCompIso f g).hom := by
  refine conjugateEquiv_eq _ _ _ _ fun K => ?_
  simp only [Adjunction.comp_counit_app]
  exact derivedAdjunction_comp_counit f g K

/-- The canonical composition isomorphism for derived pullback is the left-adjoint companion of
the composition isomorphism for derived pushforward. -/
theorem derivedPullbackCompIsoCanonical_eq_leftAdjointCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g =
      Adjunction.leftAdjointCompIso (derivedAdjunction g) (derivedAdjunction f)
        (derivedAdjunction (f ≫ g)) (derivedPushforwardCompIso f g) := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).1
    ((conjugateEquiv ((derivedAdjunction g).comp (derivedAdjunction f))
      (derivedAdjunction (f ≫ g))).injective ?_))
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  exact conjugateEquiv_derivedPullbackCompIsoCanonical_inv f g

/-- The cocycle identity for the canonical composition isomorphism of derived pullback: the two
ways of identifying `Lh^* ⋙ Lg^* ⋙ Lf^*` with `L(f ≫ g ≫ h)^*` — through `f ≫ g` on the left, or
through `g ≫ h` on the right — agree. -/
theorem derivedPullbackCompIsoCanonical_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    Functor.isoWhiskerLeft (derivedPullback h)
          (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g) ≪≫
        Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical (f ≫ g) h =
      (Functor.associator (derivedPullback h) (derivedPullback g) (derivedPullback f)).symm ≪≫
        Functor.isoWhiskerRight
            (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g h)
            (derivedPullback f) ≪≫
          Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f (g ≫ h) := by
  simp only [derivedPullbackCompIsoCanonical_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (derivedPushforwardCompIso_assoc f g h)

/-- The two identifications of
`Lh^* ⋙ Lg^* ⋙ Lf^*` with `L(f ≫ g ≫ h)^*` agree at every object. -/
theorem derivedPullbackCompIsoCanonical_assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f g).hom.app
          ((derivedPullback h).obj M) ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical (f ≫ g) h).hom.app M =
      (derivedPullback f).map
          ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g h).hom.app M) ≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f (g ≫ h)).hom.app
          M := by
  have h₀ := congr_app (congrArg Iso.hom (derivedPullbackCompIsoCanonical_assoc f g h)) M
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] using h₀

/-! ### Pushforward along an identity morphism -/

/-- A natural isomorphism of additive functors induces one between the functors they induce on
the homotopy categories of homological complexes. -/
def natIsoMapHomotopyCategory {V W : Type*} [Category V] [Category W] [Preadditive V]
    [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ≅ G)
    {ι : Type*} (c : ComplexShape ι) :
    F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory α.hom c
  inv := NatTrans.mapHomotopyCategory α.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, α.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, α.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- The functor induced on the homotopy category by the identity functor acts as the identity on
morphisms. -/
theorem mapHomotopyCategory_id_map (V : Type*) [Category V] [Preadditive V] {ι : Type*}
    (c : ComplexShape ι) {K L : HomotopyCategory V c} (φ : K ⟶ L) :
    ((𝟭 V).mapHomotopyCategory c).map φ = φ := by
  obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient V c).map_surjective φ
  rfl

/-- The identity functor induces the identity functor on the homotopy category of homological
complexes. -/
def mapHomotopyCategoryIdIso (V : Type*) [Category V] [Preadditive V] {ι : Type*}
    (c : ComplexShape ι) : (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun φ =>
    Eq.trans (Category.comp_id _)
      (Eq.trans (mapHomotopyCategory_id_map V c φ) (Category.id_comp φ).symm)

/-- The components of `CategoryTheory.Functor.mapHomologicalComplexIdIso` are identities. -/
theorem mapHomologicalComplexIdIso_inv_app (V : Type*) [Category V]
    [Limits.HasZeroMorphisms V] {ι : Type*} (c : ComplexShape ι) (K : HomologicalComplex V c) :
    (Functor.mapHomologicalComplexIdIso V c).inv.app K = 𝟙 K := rfl

/-- Pushforward along the identity is the identity functor on complexes of sheaves of
modules. -/
def modulePushforwardIdComplex (X : RingedSpace.{u, u}) :
    (modulePushforward (𝟙 X)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :=
  NatIso.mapHomologicalComplex (modulePushforwardId X) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)

/-- Pushforward along the identity is the identity functor on the unbounded homotopy category of
sheaves of modules. -/
def modulePushforwardIdHomotopy (X : RingedSpace.{u, u}) :
    (modulePushforward (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
  natIsoMapHomotopyCategory (modulePushforwardId X) (ComplexShape.up ℤ) ≪≫
    mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)

/-- `modulePushforwardIdHomotopy` is the class of `modulePushforwardIdComplex`. -/
theorem modulePushforwardIdHomotopy_inv_app_eq (X : RingedSpace.{u, u})
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (modulePushforwardIdHomotopy X).inv.app K =
      (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).map
        ((modulePushforwardIdComplex X).inv.app K.as) :=
  rfl

/-- The left unit law for the pushforward-composition comparison, on complexes: the comparison
`(𝟙 ≫ g)_* ⟶ (𝟙)_* ⋙ g_*` is `g_*` applied to the unit isomorphism of `(𝟙)_*`. -/
theorem pushforwardCompComplex_id_comp (g : Y ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (pushforwardCompComplex (𝟙 Y) g).app K =
      ((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((modulePushforwardIdComplex Y).inv.app K) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [modulePushforwardIdComplex, Iso.trans_inv, NatTrans.comp_app,
    mapHomologicalComplexIdIso_inv_app, HomologicalComplex.comp_f, HomologicalComplex.id_f,
    Functor.mapHomologicalComplex_map_f]
  exact ((modulePushforward g).map_id (K.X i)).symm

/-- Every component of `pushforwardCompHomotopy` is the class of the corresponding component of
`pushforwardCompComplex`. -/
theorem pushforwardCompHomotopy_app_as (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (pushforwardCompHomotopy f g).app K =
      (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Z))
          (ComplexShape.up ℤ)).map
        ((pushforwardCompComplex f g).app K.as) :=
  rfl

/-- The left unit law for the pushforward-composition comparison, on the unbounded homotopy
categories: the comparison `(𝟙 ≫ g)_* ⟶ (𝟙)_* ⋙ g_*` is `g_*` applied to the unit isomorphism of
`(𝟙)_*`. -/
theorem pushforwardCompHomotopy_id_comp (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (pushforwardCompHomotopy (𝟙 Y) g).app K =
      ((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((modulePushforwardIdHomotopy Y).inv.app K) :=
  Eq.trans (pushforwardCompHomotopy_app_as (𝟙 Y) g K)
    (Eq.trans (quotient_map_congr (pushforwardCompComplex_id_comp g K.as))
      (CategoryTheory.Functor.congr_map
        ((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ))
        (modulePushforwardIdHomotopy_inv_app_eq Y K).symm))

/-- The localization functor factors the degreewise pushforward along the identity: `(𝟙)_*`
followed by `Q` is `Q`. -/
def pushforwardIdToDerived (X : RingedSpace.{u, u}) :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ≅
      pushforwardToDerivedCategory (𝟙 X) :=
  DerivedCategory.Qh.rightUnitor ≪≫
    (Functor.isoWhiskerRight (modulePushforwardIdHomotopy X) DerivedCategory.Qh ≪≫
      DerivedCategory.Qh.leftUnitor).symm

/-- `pushforwardIdToDerived` is the localization of the unit isomorphism of `(𝟙)_*`. -/
theorem pushforwardIdToDerived_hom_app (X : RingedSpace.{u, u})
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (pushforwardIdToDerived X).hom.app K =
      DerivedCategory.Qh.map ((modulePushforwardIdHomotopy X).inv.app K) := by
  simp [pushforwardIdToDerived]

/-- Derived pushforward along the identity is the identity functor, `R(𝟙 X)_* ≅ 𝟭`. -/
def derivedPushforwardIdIso (X : RingedSpace.{u, u}) :
    derivedPushforward (𝟙 X) ≅ 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  haveI := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) (pushforwardIdToDerived X)
  (Functor.rightDerivedNatIso (𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (derivedPushforward (𝟙 X)) (pushforwardIdToDerived X).inv (derivedPushforwardUnit (𝟙 X))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (Iso.refl (pushforwardToDerivedCategory (𝟙 X)))).symm

/-- On the image of the localization functor, the inverse of `derivedPushforwardIdIso X` is
`pushforwardIdToDerived X` followed by the comparison for `R(𝟙 X)_*`. -/
theorem derivedPushforwardIdIso_inv_app (X : RingedSpace.{u, u})
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardIdIso X).inv.app (DerivedCategory.Qh.obj K) =
      (pushforwardIdToDerived X).hom.app K ≫ (derivedPushforwardUnit (𝟙 X)).app K := by
  have hd := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) (pushforwardIdToDerived X)
  have h : (pushforwardIdToDerived X).inv.app K ≫
      (derivedPushforwardIdIso X).inv.app (DerivedCategory.Qh.obj K) =
      (derivedPushforwardUnit (𝟙 X)).app K := by
    have h0 := Functor.rightDerivedNatTrans_app
      (𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))) (derivedPushforward (𝟙 X))
      (pushforwardIdToDerived X).inv (derivedPushforwardUnit (𝟙 X))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
      (𝟙 (pushforwardToDerivedCategory (𝟙 X))) K
    rw [NatTrans.id_app, Category.id_comp] at h0
    exact h0
  rw [← h, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- A two-factor identity extended by a third factor, reassociated on both sides. -/
private theorem comp_assoc_of_comp {E : Type*} [Category E] {A B C D F : E}
    {p : A ⟶ B} {q : B ⟶ C} {r : A ⟶ F} {s : F ⟶ C} (h : p ≫ q = r ≫ s) (m : C ⟶ D) :
    p ≫ q ≫ m = r ≫ s ≫ m := by
  rw [← Category.assoc, h, Category.assoc]

/-- `derivedPushforwardUnit_comp_compIso_inv` at `(𝟙 Y, g)`, with the degreewise comparison
written as `g_*` of the unit isomorphism of `(𝟙)_*`. -/
theorem derivedPushforwardUnit_comp_compIso_inv_id (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit (𝟙 Y ≫ g)).app K ≫
        (derivedPushforwardCompIso (𝟙 Y) g).inv.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          (((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map
            ((modulePushforwardIdHomotopy Y).inv.app K)) ≫
        (derivedPushforwardUnit g).app
            (((modulePushforward (𝟙 Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          (derivedPushforward g).map ((derivedPushforwardUnit (𝟙 Y)).app K) :=
  Eq.trans (derivedPushforwardUnit_comp_compIso_inv (𝟙 Y) g K)
    (eq_whisker (CategoryTheory.Functor.congr_map DerivedCategory.Qh
      (pushforwardCompHomotopy_id_comp g K)) _)

/-- The inverse of the right-hand side of the unit law, read at an object of the image of the
localization functor. -/
theorem derivedPushforwardIdIso_whiskerRight_inv_app (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (Functor.isoWhiskerRight (derivedPushforwardIdIso Y) (derivedPushforward g) ≪≫
        (derivedPushforward g).leftUnitor).inv.app (DerivedCategory.Qh.obj K) =
      (derivedPushforward g).map ((pushforwardIdToDerived Y).hom.app K) ≫
        (derivedPushforward g).map ((derivedPushforwardUnit (𝟙 Y)).app K) := by
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Category.id_comp,
    derivedPushforwardIdIso_inv_app, Functor.map_comp]

/-- The left unit law for the composition isomorphism of derived pushforward: identifying
`R(𝟙 Y)_* ⋙ Rg_*` with `R(𝟙 Y ≫ g)_*` is the unit isomorphism of `R(𝟙 Y)_*` pushed forward
along `g`. -/
theorem derivedPushforwardCompIso_id_comp (g : Y ⟶ Z) :
    derivedPushforwardCompIso (𝟙 Y) g =
      Functor.isoWhiskerRight (derivedPushforwardIdIso Y) (derivedPushforward g) ≪≫
        (derivedPushforward g).leftUnitor := by
  refine iso_ext_of_unit_comp _ _ _ fun K => ?_
  refine Eq.trans (derivedPushforwardUnit_comp_compIso_inv_id g K) ?_
  rw [derivedPushforwardIdIso_whiskerRight_inv_app, pushforwardIdToDerived_hom_app]
  have hnat := (derivedPushforwardUnit g).naturality
    ((modulePushforwardIdHomotopy Y).inv.app K)
  simp only [Functor.comp_map] at hnat
  exact comp_assoc_of_comp hnat _

/-- The right unit law for the pushforward-composition comparison, on complexes: the comparison
`(f ≫ 𝟙)_* ⟶ f_* ⋙ (𝟙)_*` is the unit isomorphism of `(𝟙)_*` at `f_*`. -/
theorem pushforwardCompComplex_comp_id (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (pushforwardCompComplex f (𝟙 Y)).app K =
      (modulePushforwardIdComplex Y).inv.app
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [modulePushforwardIdComplex, Iso.trans_inv, NatTrans.comp_app,
    mapHomologicalComplexIdIso_inv_app, HomologicalComplex.comp_f, HomologicalComplex.id_f]
  exact (Category.id_comp _).symm

/-- The right unit law for the pushforward-composition comparison, on the unbounded homotopy
categories: the comparison `(f ≫ 𝟙)_* ⟶ f_* ⋙ (𝟙)_*` is the unit isomorphism of `(𝟙)_*` at
`f_*`. -/
theorem pushforwardCompHomotopy_comp_id (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (pushforwardCompHomotopy f (𝟙 Y)).app K =
      (modulePushforwardIdHomotopy Y).inv.app
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) :=
  Eq.trans (pushforwardCompHomotopy_app_as f (𝟙 Y) K)
    (Eq.trans (quotient_map_congr (pushforwardCompComplex_comp_id f K.as))
      (modulePushforwardIdHomotopy_inv_app_eq Y
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)).symm)

/-- The inverse of the right-hand side of the right unit law, at an arbitrary object. -/
theorem derivedPushforwardIdIso_whiskerLeft_inv_app (f : X ⟶ Y)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (Functor.isoWhiskerLeft (derivedPushforward f) (derivedPushforwardIdIso Y) ≪≫
        (derivedPushforward f).rightUnitor).inv.app M =
      (derivedPushforwardIdIso Y).inv.app ((derivedPushforward f).obj M) := by
  simp

/-- A two-factor identity whose head factors again, reassociated. -/
private theorem assoc_comp_eq {E : Type*} [Category E] {A B C D F : E}
    {p : A ⟶ B} {q : B ⟶ C} {m : C ⟶ D} {t : A ⟶ C} {r : A ⟶ F} {s : F ⟶ D}
    (h1 : p ≫ q = t) (h2 : t ≫ m = r ≫ s) : p ≫ q ≫ m = r ≫ s := by
  rw [← Category.assoc, h1, h2]

/-- `derivedPushforwardIdIso_inv_app` at the degreewise pushforward of a complex along `f`, with
the comparison for `R(𝟙)_*` exposed through the degreewise right unit law. -/
theorem derivedPushforwardIdIso_inv_app_pushforward (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardIdIso Y).inv.app
          (DerivedCategory.Qh.obj
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((pushforwardCompHomotopy f (𝟙 Y)).app K) ≫
        (derivedPushforwardUnit (𝟙 Y)).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  rw [derivedPushforwardIdIso_inv_app, pushforwardIdToDerived_hom_app,
    pushforwardCompHomotopy_comp_id]
  rfl

/-- The right unit law for the composition isomorphism of derived pushforward: identifying
`Rf_* ⋙ R(𝟙 Y)_*` with `R(f ≫ 𝟙 Y)_*` is the unit isomorphism of `R(𝟙 Y)_*` at `Rf_*`. -/
theorem derivedPushforwardCompIso_comp_id (f : X ⟶ Y) :
    derivedPushforwardCompIso f (𝟙 Y) =
      Functor.isoWhiskerLeft (derivedPushforward f) (derivedPushforwardIdIso Y) ≪≫
        (derivedPushforward f).rightUnitor := by
  refine iso_ext_of_unit_comp _ _ _ fun K => ?_
  refine Eq.trans (derivedPushforwardUnit_comp_compIso_inv f (𝟙 Y) K) ?_
  rw [derivedPushforwardIdIso_whiskerLeft_inv_app]
  have hnat := (derivedPushforwardIdIso Y).inv.naturality ((derivedPushforwardUnit f).app K)
  simp only [Functor.id_map] at hnat
  exact assoc_comp_eq (derivedPushforwardIdIso_inv_app_pushforward f K).symm hnat.symm

/-! ### Pullback along an identity morphism -/

/-- Derived pullback along the identity is the identity functor, `L(𝟙 X)^* ≅ 𝟭`. -/
def derivedPullbackIdIso (X : RingedSpace.{u, u}) :
    derivedPullback (𝟙 X) ≅ 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  (derivedAdjunction (𝟙 X)).leftAdjointIdIso (derivedPushforwardIdIso X)

/-- The left unit law for the canonical composition isomorphism of derived pullback: identifying
`Lg^* ⋙ L(𝟙 Y)^*` with `L(𝟙 Y ≫ g)^*` is the unit isomorphism of `L(𝟙 Y)^*` whiskered by
`Lg^*`. -/
theorem derivedPullbackCompIsoCanonical_id_comp (g : Y ⟶ Z) :
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical (𝟙 Y) g =
      Functor.isoWhiskerLeft (derivedPullback g) (derivedPullbackIdIso Y) ≪≫
        (derivedPullback g).rightUnitor :=
  Eq.trans (derivedPullbackCompIsoCanonical_eq_leftAdjointCompIso (𝟙 Y) g)
    (Adjunction.leftAdjointCompIso_comp_id (derivedAdjunction g) (derivedAdjunction (𝟙 Y))
      (derivedPushforwardCompIso (𝟙 Y) g) (derivedPushforwardIdIso Y)
      (derivedPushforwardCompIso_id_comp g))

/-- The right unit law for the canonical composition isomorphism of derived pullback: identifying
`L(𝟙 Y)^* ⋙ Lf^*` with `L(f ≫ 𝟙 Y)^*` is the unit isomorphism of `L(𝟙 Y)^*` whiskered by
`Lf^*`. -/
theorem derivedPullbackCompIsoCanonical_comp_id (f : X ⟶ Y) :
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical f (𝟙 Y) =
      Functor.isoWhiskerRight (derivedPullbackIdIso Y) (derivedPullback f) ≪≫
        (derivedPullback f).leftUnitor :=
  Eq.trans (derivedPullbackCompIsoCanonical_eq_leftAdjointCompIso f (𝟙 Y))
    (Adjunction.leftAdjointCompIso_id_comp (derivedAdjunction (𝟙 Y)) (derivedAdjunction f)
      (derivedPushforwardCompIso f (𝟙 Y)) (derivedPushforwardIdIso Y)
      (derivedPushforwardCompIso_comp_id f))

end

end Stacks.Cohomology.DerivedPushforwardAssociativity

end
