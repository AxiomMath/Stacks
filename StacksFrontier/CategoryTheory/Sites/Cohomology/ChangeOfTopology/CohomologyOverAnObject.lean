module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.VanishingConditionSucc

/-!
# Cohomology over an object of a localized site

Let `(C, J)` be a site, `X` an object of `C` and `ℱ` an abelian sheaf on the localized site
`C_J/X`. For `V` an object of `C_J/X` the cohomology of `ℱ` over `V` is the cohomology, over the
terminal object of `C_J/V.left`, of the restriction of `ℱ` along `V.hom`:

`H^i(V, ℱ) ≅ H^i(Over.mk (𝟙 V.left), ℱ|_V)`,

naturally in `V`. This transports statements about the *global* sections of a localized site to
statements about the sections over an arbitrary object of it.

## Main definitions

* `Stacks.Cohomology.Localization.overMapSheafCohomologyIso`: the isomorphism
  `H^i((Over.map u) W, ℱ) ≅ H^i(W, ℱ|_u)` for `u : Y ⟶ X` and `W` an object of `C_J/Y`.
* `Stacks.Cohomology.Localization.sheafCohomologyOverIso`: its value at the terminal object,
  `H^i(V, ℱ) ≅ H^i(Over.mk (𝟙 V.left), ℱ|_V)`.
* `Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescentRange`: the descent
  statement for a single covering arrow of the distinguished class, with both of its covering
  conditions replaced by membership in the image of the change-of-topology map on cohomology.

## Main results

* `Stacks.Cohomology.Localization.overMapSheafCohomologyIso_hom_comp_restriction` and
  `Stacks.Cohomology.Localization.sheafCohomologyOverIso_hom_comp_restriction`: the two
  isomorphisms are natural in the object.
* `Stacks.ComparingTopologies.mem_range_cohomologyComparison_over_iff`: **Stacks 0EZC**, the
  description of the image of the change-of-topology map on cohomology, over an arbitrary object
  of the localized site rather than over its terminal object.
* `Stacks.ComparingTopologies.CohomologyComparison.singleCoveringDescent_iff_range`: the descent
  statement of Stacks 0EZE and its purely derived form are equivalent under `(V_n)`.

## Implementation notes

Restriction along `u : Y ⟶ X` is exact and preserves injective objects, and sections over `W`
of a restricted sheaf are sections over `(Over.map u) W` of the sheaf itself — on the nose, since
restriction precomposes the underlying presheaf with `(Over.map u).op`. So the two sides of the
isomorphism are the right derived functors of one functor and of a composite ending in it, and
the isomorphism is the collapse isomorphism `Stacks.RightDerivedComp.objIso`. Naturality in the
object is naturality of that collapse in the functor one derives, because the restriction map on
cohomology along `k : W' ⟶ W` is the derived functor of the restriction map on sections.

The terminal object of `C_J/V.left` is `Over.mk (𝟙 V.left)`, whose image under `Over.map V.hom`
is `Over.mk (𝟙 V.left ≫ V.hom)` rather than `V`; the comparison between the two is carried by
the isomorphism `Over.mk (𝟙 V.left ≫ V.hom) ≅ V` of the slice category.

`Stacks.Cohomology.LocalizedSite.overMapPullbackRightDerivedSectionsIso` is the same
isomorphism, obtained instead from the exactness of evaluation of presheaves and stated as an
isomorphism of functors in the sheaf; what is added here is its naturality in the object, in the
shape in which the restriction maps on cohomology classes occur.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 0EZC](https://stacks.math.columbia.edu/tag/0EZC)
* [Stacks Project, Tag 0EZE](https://stacks.math.columbia.edu/tag/0EZE)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.RightDerivedComp

variable {A₀ B₀ E₀ : Type*} [Category* A₀] [Category* B₀] [Category* E₀]
  [Abelian A₀] [Abelian B₀] [Abelian E₀]
  [HasInjectiveResolutions A₀] [HasInjectiveResolutions B₀]
  (G : A₀ ⥤ B₀) [G.Additive] {M : A₀} (I : InjectiveResolution M) [PreservesFiniteLimits G]
  (hM : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj M)) [G.PreservesInjectiveObjects]

section Cancel

variable {W X Y Z Z' : E₀}

omit [Abelian E₀] in
/-- Cancelling an isomorphism between two composites, in a context where the types involved are
syntactically fixed. -/
private lemma comp_inv_comp_hom_comp (f : W ⟶ Y) (e : X ≅ Y) (g : Y ⟶ Z) :
    (f ≫ e.inv) ≫ e.hom ≫ g = f ≫ g := by
  rw [Category.assoc, Iso.inv_hom_id_assoc]

omit [Abelian E₀] in
/-- Cancelling an isomorphism between two composites, with one extra factor in front. -/
private lemma comp_comp_inv_comp_hom_comp (f : W ⟶ Z') (m : Z' ⟶ Y) (e : X ≅ Y) (g : Y ⟶ Z) :
    (f ≫ m ≫ e.inv) ≫ e.hom ≫ g = f ≫ m ≫ g := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

end Cancel

/-- **The collapse isomorphism is natural in the functor one derives.** Both sides are computed
on the same complex, namely `G` applied degreewise to the resolution, and the two induced maps
on its homology are the same. -/
lemma objIso_hom_natTrans {T T' : B₀ ⥤ E₀} [T.Additive] [T'.Additive] (α : T ⟶ T') (n : ℕ) :
    (objIso G I hM T n).hom ≫ (NatTrans.rightDerived α n).app (G.obj M) =
      (NatTrans.rightDerived (Functor.whiskerLeft G α) n).app M ≫ (objIso G I hM T' n).hom := by
  have hM₁ : (NatTrans.mapHomologicalComplex (Functor.whiskerLeft G α)
        (ComplexShape.up ℕ)).app I.cocomplex =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app (mapCocomplex G I) := by
    ext i
    rfl
  rw [objIso_hom, objIso_hom, InjectiveResolution.rightDerived_app_eq α (mapOfAcyclic G I hM) n,
    InjectiveResolution.rightDerived_app_eq (Functor.whiskerLeft G α) I n, hM₁]
  exact (comp_inv_comp_hom_comp _ _ _).trans (comp_comp_inv_comp_hom_comp _ _ _ _).symm

end Stacks.RightDerivedComp

namespace Stacks

variable {D : Type u} [Category.{v} D] (J : GrothendieckTopology D)

/-- Restriction of cohomology classes along an identity is the identity. -/
@[simp]
lemma sheafCohomologyRestriction_id (U : D) (n : ℕ) (F : Sheaf J Ab.{max u v}) :
    sheafCohomologyRestriction J (𝟙 U) n F = 𝟙 _ := by
  simp [sheafCohomologyRestriction]

/-- Restriction of cohomology classes is functorial, as an identity of maps. -/
lemma sheafCohomologyRestriction_comp' {Z Y U : D} (k : Z ⟶ Y) (h : Y ⟶ U) (n : ℕ)
    (F : Sheaf J Ab.{max u v}) :
    sheafCohomologyRestriction J (k ≫ h) n F =
      sheafCohomologyRestriction J h n F ≫ sheafCohomologyRestriction J k n F := by
  simp [sheafCohomologyRestriction, op_comp]

/-- An isomorphism of objects of the site induces an isomorphism of the cohomology over them. -/
@[simps]
def sheafCohomologyIsoOfIso {U V : D} (e : U ≅ V) (n : ℕ) (F : Sheaf J Ab.{max u v}) :
    sheafCohomology J F V n ≅ sheafCohomology J F U n where
  hom := sheafCohomologyRestriction J e.hom n F
  inv := sheafCohomologyRestriction J e.inv n F
  hom_inv_id := by
    rw [← sheafCohomologyRestriction_comp', e.inv_hom_id, sheafCohomologyRestriction_id]
  inv_hom_id := by
    rw [← sheafCohomologyRestriction_comp', e.hom_inv_id, sheafCohomologyRestriction_id]

/-- The sieve of arrows into `U` along which a cohomology class over `U` restricts to zero. -/
def sheafCohomologyVanishingSieve [HasSheafify J Ab.{max u v}] (F : Sheaf J Ab.{max u v}) (n : ℕ)
    {U : D}
    (ξ : sheafCohomology J F U n) : Sieve U where
  arrows _ h := sheafCohomologyRestriction J h n F ξ = 0
  downward_closed := by
    intro Y Z h hh g
    rw [sheafCohomologyRestriction_comp]
    change sheafCohomologyRestriction J h n F ξ = 0 at hh
    rw [hh, map_zero]

/-- An element of `Ab` dies under an isomorphism exactly when it is zero. -/
private lemma eq_zero_iff_of_iso {A B : Ab.{u}} (e : A ≅ B) (x : A) : e.hom x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  have hx : e.inv (e.hom x) = e.inv 0 := by rw [h]
  rwa [← ConcreteCategory.comp_apply, e.hom_inv_id, ConcreteCategory.id_apply, map_zero] at hx

end Stacks

namespace Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Cohomology over an object of a localized site is cohomology of the restriction.** For
`u : Y ⟶ X` a morphism of the site, `ℱ` an abelian sheaf on `C_J/X` and `W` an object of
`C_J/Y`,

`H^i((Over.map u) W, ℱ) ≅ H^i(W, ℱ|_u)`.

Restriction along `u` is exact and preserves injective objects, so it carries an injective
resolution of `ℱ` to one of `ℱ|_u`; sections over `W` of the restriction are sections over
`(Over.map u) W` of `ℱ` on the nose. -/
def overMapSheafCohomologyIso {Y X : C} (u : Y ⟶ X) (F : Sheaf (J.over X) Ab.{max u v}) (W : Over Y)
    (i : ℕ) :
    Stacks.sheafCohomology (J.over X) F ((Over.map u).obj W) i ≅
      Stacks.sheafCohomology (J.over Y) ((J.overMapPullback Ab.{max u v} u).obj F) W i :=
  Stacks.RightDerivedComp.objIso (J.overMapPullback Ab.{max u v} u) (injectiveResolution F)
    (fun n hn ↦ Stacks.Cohomology.isZero_rightDerived_obj_of_preservesHomology
      (J.overMapPullback Ab.{max u v} u) F n hn)
    ((sheafSections (J.over Y) Ab.{max u v}).obj (op W)) i

/-- **The isomorphism of `overMapSheafCohomologyIso` is natural in the object.** -/
lemma overMapSheafCohomologyIso_hom_comp_restriction {Y X : C} (u : Y ⟶ X)
    (F : Sheaf (J.over X) Ab.{max u v}) {W' W : Over Y} (k : W' ⟶ W) (i : ℕ) :
    (overMapSheafCohomologyIso J u F W i).hom ≫
        Stacks.sheafCohomologyRestriction (J.over Y) k i
          ((J.overMapPullback Ab.{max u v} u).obj F) =
      Stacks.sheafCohomologyRestriction (J.over X) ((Over.map u).map k) i F ≫
        (overMapSheafCohomologyIso J u F W' i).hom :=
  Stacks.RightDerivedComp.objIso_hom_natTrans (J.overMapPullback Ab.{max u v} u)
    (injectiveResolution F) _ ((sheafSections (J.over Y) Ab.{max u v}).map k.op) i

/-- The image of the terminal object of `C_J/V.left` under `Over.map V.hom` is isomorphic to `V`
in the slice category over `X`. -/
def overMkIdCompIso {X : C} (V : Over X) : (Over.mk (𝟙 V.left ≫ V.hom) : Over X) ≅ V :=
  Over.isoMk (Iso.refl V.left) (by simp)

/-- **Cohomology over an object of a localized site is global cohomology of the restriction.**
For `ℱ` an abelian sheaf on `C_J/X` and `V` an object of `C_J/X`,

`H^i(V, ℱ) ≅ H^i(Over.mk (𝟙 V.left), ℱ|_V)`,

the right-hand side being cohomology over the terminal object of `C_J/V.left`. -/
def sheafCohomologyOverIso {X : C} (F : Sheaf (J.over X) Ab.{max u v}) (V : Over X) (i : ℕ) :
    Stacks.sheafCohomology (J.over X) F V i ≅
      Stacks.sheafCohomology (J.over V.left) ((J.overMapPullback Ab.{max u v} V.hom).obj F)
        (Over.mk (𝟙 V.left)) i :=
  Stacks.sheafCohomologyIsoOfIso (J.over X) (overMkIdCompIso V) i F ≪≫
    overMapSheafCohomologyIso J V.hom F (Over.mk (𝟙 V.left)) i

/-- The forward map of `sheafCohomologyOverIso` is the restriction along `(overMkIdCompIso V).hom`
followed by the forward map of `overMapSheafCohomologyIso`. -/
lemma sheafCohomologyOverIso_hom {X : C} (F : Sheaf (J.over X) Ab.{max u v}) (V : Over X) (i : ℕ) :
    (sheafCohomologyOverIso J F V i).hom =
      Stacks.sheafCohomologyRestriction (J.over X) (overMkIdCompIso V).hom i F ≫
        (overMapSheafCohomologyIso J V.hom F (Over.mk (𝟙 V.left)) i).hom :=
  rfl

/-- **The isomorphism of `sheafCohomologyOverIso` is natural in the object.** Restricting a class
over `V` along `w : Z ⟶ V.left` and then comparing is comparing and then restricting along the
corresponding arrow of `C_J/V.left`. -/
lemma sheafCohomologyOverIso_hom_comp_restriction {X : C} (F : Sheaf (J.over X) Ab.{max u v})
    (V : Over X) (i : ℕ) {Z : C} (w : Z ⟶ V.left) :
    (sheafCohomologyOverIso J F V i).hom ≫
        Stacks.sheafCohomologyRestriction (J.over V.left)
          (Over.homMk w : Over.mk w ⟶ Over.mk (𝟙 V.left)) i
          ((J.overMapPullback Ab.{max u v} V.hom).obj F) =
      Stacks.sheafCohomologyRestriction (J.over X)
          (Over.homMk w : Over.mk (w ≫ V.hom) ⟶ V) i F ≫
        (overMapSheafCohomologyIso J V.hom F (Over.mk w) i).hom := by
  have hk : (Over.map V.hom).map (Over.homMk w : Over.mk w ⟶ Over.mk (𝟙 V.left)) ≫
      (overMkIdCompIso V).hom = (Over.homMk w : Over.mk (w ≫ V.hom) ⟶ V) := by
    ext
    simp [overMkIdCompIso]
  rw [sheafCohomologyOverIso_hom, Category.assoc,
    overMapSheafCohomologyIso_hom_comp_restriction, ← Category.assoc,
    ← Stacks.sheafCohomologyRestriction_comp', hk]

/-- Restricting along `w : Z ⟶ V.left` kills the comparison of a class over `V` exactly when it
kills the class itself. -/
lemma sheafCohomologyOverIso_restriction_eq_zero_iff {X : C} (F : Sheaf (J.over X) Ab.{max u v})
    (V : Over X) (i : ℕ) {Z : C} (w : Z ⟶ V.left)
    (ξ : Stacks.sheafCohomology (J.over X) F V i) :
    Stacks.sheafCohomologyRestriction (J.over V.left)
        (Over.homMk w : Over.mk w ⟶ Over.mk (𝟙 V.left)) i
        ((J.overMapPullback Ab.{max u v} V.hom).obj F)
          ((sheafCohomologyOverIso J F V i).hom ξ) = 0 ↔
      Stacks.sheafCohomologyRestriction (J.over X)
        (Over.homMk w : Over.mk (w ≫ V.hom) ⟶ V) i F ξ = 0 := by
  have h : Stacks.sheafCohomologyRestriction (J.over V.left)
        (Over.homMk w : Over.mk w ⟶ Over.mk (𝟙 V.left)) i
        ((J.overMapPullback Ab.{max u v} V.hom).obj F) ((sheafCohomologyOverIso J F V i).hom ξ) =
      (overMapSheafCohomologyIso J V.hom F (Over.mk w) i).hom
        (Stacks.sheafCohomologyRestriction (J.over X)
          (Over.homMk w : Over.mk (w ≫ V.hom) ⟶ V) i F ξ) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      sheafCohomologyOverIso_hom_comp_restriction]
  rw [h]
  exact Stacks.eq_zero_iff_of_iso _ _

end Stacks.Cohomology.Localization

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

/-- A class of positive degree dies on a covering of its domain for the coarser topology exactly
when the sieve on which it restricts to zero is a covering sieve. -/
lemma exists_coarseCover_iff_vanishingSieve_mem (S : CohomologyComparison C) (m : ℕ) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (V : Over X)
    (ξ : Stacks.sheafCohomology (S.fineCoverage.toGrothendieck.over X) F V m) :
    (∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover V, ∀ g : R.Arrow,
        Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) g.f m F ξ = 0) ↔
      Stacks.sheafCohomologyVanishingSieve (S.fineCoverage.toGrothendieck.over X) F m ξ ∈
        S.coarseCoverage.toGrothendieck.over X V := by
  refine ⟨fun ⟨R, hR⟩ ↦ ?_, fun h ↦ ⟨⟨_, h⟩, fun g ↦ g.hf⟩⟩
  exact (S.coarseCoverage.toGrothendieck.over X).superset_covering
    (fun _ h hh ↦ hR ⟨_, h, hh⟩) R.2

/-- **Stacks 0EZC, over an arbitrary object of the localized site.** Under `(Vₙ)`, a class of
degree `n + 1` over an object `V` of `C_τ/X` dies on a covering of `V` for the coarser topology
precisely when its comparison over `V.left` lies in the image of the change-of-topology map on
cohomology.

The tag is proved over the terminal object of a localized site; the identification of cohomology
over `V` with cohomology over the terminal object of `C_τ/V.left` is
`Stacks.Cohomology.Localization.sheafCohomologyOverIso`, and the class `𝒜` is stable under
restriction by Stacks 0EZ9. -/
theorem mem_range_cohomologyComparison_over_iff (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (hF : S.fineWeakSerre X F)
    (V : Over X)
    (ξ : Stacks.sheafCohomology (S.fineCoverage.toGrothendieck.over X) F V (n + 1)) :
    (∃ η : Stacks.sheafCohomology (S.coarseCoverage.toGrothendieck.over V.left)
        ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine
          V.left).obj
            ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} V.hom).obj F))
        (Over.mk (𝟙 V.left)) (n + 1),
        (cohomologyComparison S V.left (n + 1)).app
            ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} V.hom).obj F) η =
          (sheafCohomologyOverIso S.fineCoverage.toGrothendieck F V (n + 1)).hom ξ) ↔
      ∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover V, ∀ g : R.Arrow,
        Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) g.f
          (n + 1) F ξ = 0 := by
  refine (mem_range_cohomologyComparison_iff S n hV V.left
    ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} V.hom).obj F)
    (CohomologyComparison.fineWeakSerre_overMapPullback S V.hom F hF) _).trans ?_
  constructor
  · rintro ⟨R, hRmem, hR⟩
    have hR' : ∀ ⦃Z : C⦄ (w : Z ⟶ V.left), R w →
        Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X)
          (Over.homMk w : Over.mk (w ≫ V.hom) ⟶ V) (n + 1) F ξ = 0 :=
      fun _ w hw ↦ (sheafCohomologyOverIso_restriction_eq_zero_iff
        S.fineCoverage.toGrothendieck F V (n + 1) w ξ).1 (hR w hw)
    refine (exists_coarseCover_iff_vanishingSieve_mem S (n + 1) X F V ξ).2 ?_
    refine (S.coarseCoverage.toGrothendieck.over X).superset_covering ?_
      (S.coarseCoverage.toGrothendieck.overEquiv_symm_mem_over V _
        (S.coarseCoverage.generate_mem_toGrothendieck hRmem))
    intro Z h hh
    obtain ⟨Y₁, b, r, hRr, hbr⟩ : Sieve.generate R h.left := hh
    have hbrw : b ≫ (Over.mk (r ≫ V.hom) : Over X).hom = Z.hom := by
      change b ≫ r ≫ V.hom = Z.hom
      rw [← Category.assoc, hbr]
      exact Over.w h
    have hfac : (Over.homMk b hbrw : Z ⟶ Over.mk (r ≫ V.hom)) ≫
        (Over.homMk r : Over.mk (r ≫ V.hom) ⟶ V) = h := by
      ext
      exact hbr
    change Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) h
      (n + 1) F ξ = 0
    rw [← hfac, Stacks.sheafCohomologyRestriction_comp, hR' r hRr, map_zero]
  · rintro ⟨R, hR⟩
    obtain ⟨R₀, hR₀mem, hR₀le⟩ :=
      S.coarseCoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp
        ((S.coarseCoverage.toGrothendieck.mem_over_iff R.1).1 R.2)
    exact ⟨R₀, hR₀mem, fun Z w hw ↦ (sheafCohomologyOverIso_restriction_eq_zero_iff
      S.fineCoverage.toGrothendieck F V (n + 1) w ξ).2
      (hR ⟨_, _, (Sieve.overEquiv_iff R.1 w).1 (hR₀le _ w hw)⟩)⟩

/-- **The descent statement for a single covering arrow of the distinguished class, in purely
derived form.** For `f : W ⟶ V` a morphism of the site localized at `X` whose underlying arrow
lies in the distinguished class and which by itself is a covering for the finer topology, and for
`ℱ` in `𝒜_X`, a class of degree `m` over `V` whose restriction to `W` is in the image of the
change-of-topology map on cohomology over `W.left` is itself in the image of that map over
`V.left`.

This is `Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescent` with both of its
covering conditions replaced by the derived condition which Stacks 0EZC shows equivalent to
them. -/
def CohomologyComparison.SingleCoveringDescentRange (S : CohomologyComparison C) (m : ℕ) : Prop :=
  ∀ (X : C) (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}), S.fineWeakSerre X F →
    ∀ (V W : Over X) (f : W ⟶ V), S.morphismProperty f.left →
      Presieve.singleton f.left ∈ S.fineCoverage V.left →
        ∀ ζ : Stacks.sheafCohomology (S.fineCoverage.toGrothendieck.over X) F V m,
          (∃ η : Stacks.sheafCohomology (S.coarseCoverage.toGrothendieck.over W.left)
              ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine
                W.left).obj
                  ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} W.hom).obj F))
              (Over.mk (𝟙 W.left)) m,
              (cohomologyComparison S W.left m).app
                  ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} W.hom).obj F) η =
                (sheafCohomologyOverIso S.fineCoverage.toGrothendieck F W m).hom
                  (Stacks.sheafCohomologyRestriction
                    (S.fineCoverage.toGrothendieck.over X) f m F ζ)) →
          ∃ η : Stacks.sheafCohomology (S.coarseCoverage.toGrothendieck.over V.left)
              ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine
                V.left).obj
                  ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} V.hom).obj F))
              (Over.mk (𝟙 V.left)) m,
            (cohomologyComparison S V.left m).app
                ((S.fineCoverage.toGrothendieck.overMapPullback Ab.{max u v} V.hom).obj F) η =
              (sheafCohomologyOverIso S.fineCoverage.toGrothendieck F V m).hom ζ

/-- **The descent statement of Stacks 0EZE and its purely derived form are equivalent under
`(Vₙ)`.** The two covering conditions of
`Stacks.ComparingTopologies.CohomologyComparison.SingleCoveringDescent` are the two sides of
Stacks 0EZC over an arbitrary object of the localized site, so assuming it is the same as
assuming the statement about the image of the change-of-topology map on cohomology, in which no
covering occurs. -/
theorem CohomologyComparison.singleCoveringDescent_iff_range (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) :
    S.SingleCoveringDescent (n + 1) ↔ S.SingleCoveringDescentRange (n + 1) := by
  constructor
  · intro h X F hF V W f hPf hcov ζ hζ
    refine (mem_range_cohomologyComparison_over_iff S n hV X F hF V ζ).2
      (h X F hF V W f hPf hcov ζ ?_)
    obtain ⟨R, hR⟩ := (mem_range_cohomologyComparison_over_iff S n hV X F hF W
      (Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) f
        (n + 1) F ζ)).1 hζ
    exact ⟨R, fun g ↦ by rw [Stacks.sheafCohomologyRestriction_comp]; exact hR g⟩
  · intro h X F hF V W f hPf hcov ζ hζ
    refine (mem_range_cohomologyComparison_over_iff S n hV X F hF V ζ).1
      (h X F hF V W f hPf hcov ζ ?_)
    obtain ⟨R, hR⟩ := hζ
    refine (mem_range_cohomologyComparison_over_iff S n hV X F hF W _).2
      ⟨R, fun g ↦ ?_⟩
    rw [← Stacks.sheafCohomologyRestriction_comp]
    exact hR g

/-- **Stacks 0EZE**, granted the descent statement in its purely derived form. -/
theorem CohomologyComparison.vanishingCondition_succ_of_range (S : CohomologyComparison C)
    (n : ℕ) (hV : S.vanishingCondition n) (hdesc : S.SingleCoveringDescentRange (n + 1)) :
    S.vanishingCondition (n + 1) :=
  S.vanishingCondition_succ_of_singleCoveringDescent n hV
    ((S.singleCoveringDescent_iff_range n hV).2 hdesc)

end Stacks.ComparingTopologies

end
