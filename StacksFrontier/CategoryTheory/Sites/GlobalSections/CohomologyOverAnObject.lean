module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaf cohomology over an object is global cohomology on the slice site

Let `(C, J)` be a site, `U : C` an object and `F` an abelian sheaf on `(C, J)`. Mathlib's
`CategoryTheory.Sheaf.H' F n U` is the `Ext`-group from the free abelian sheaf on `yoneda.obj U`
to `F`, while `CategoryTheory.Sheaf.H G n` is the `Ext`-group from the constant sheaf with
value `ULift ℤ` to `G`. This file identifies the first with the second applied to the
restriction `F.over U` of `F` to the slice site `(Over U, J.over U)`; the statement is a `TODO`
of `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, which asks for an isomorphism
`(F.cohomologyPresheaf n).obj (Opposite.op U) ≃+ Sheaf.H (F.over U) n`.

The proof has two halves, both of independent interest.

The first is a comparison of `Ext`-groups along an exact adjunction `L ⊣ R` of abelian
categories: if `R` is exact and preserves injective objects and the target of `L` has enough
injectives, then `Ext^n (L X, Y) ≅ Ext^n (X, R Y)`. The comparison map is `Ext`-functoriality of
the exact functor `R` followed by composition with the unit of the adjunction; bijectivity is an
induction on `n` along an injective presentation of `Y`, using that the covariant `Ext`-sequence
of a short exact sequence is exact and that `Ext^{n+1}` out of anything into an injective
vanishes. Specialized to `j_! ⊣ j^*` for the localization `j : Over U ⥤ C` this is the change-of-
site statement that makes the comparison possible at all: the two cohomologies live in different
sheaf categories.

The second is that the free abelian sheaf on `yoneda.obj U` is the image under `j_!` of the free
abelian sheaf on `yoneda.obj (Over.mk (𝟙 U))`. Both are shown to corepresent the same functor
`F ↦ F(U)` with values in types: the free abelian sheaf on `yoneda.obj X` corepresents
evaluation at `X` by composing the sheafification adjunction, the free-forgetful adjunction on
abelian groups and the Yoneda lemma, and `j^*` does not change the sections over
`Over.mk (𝟙 U)`.

## Main definitions

* `Stacks.Cohomology.OverObjectCohomology.extAdjEquiv`: **the `Ext`-comparison along an exact
  adjunction** `Ext^n (L X, Y) ≃+ Ext^n (X, R Y)`.
* `Stacks.Cohomology.OverObjectCohomology.freeYonedaSheafHomEquiv`: the free abelian sheaf on
  `yoneda.obj X` corepresents evaluation at `X`.
* `Stacks.Cohomology.OverObjectCohomology.freeYonedaSheafOverIso`: `j_!` takes the free abelian
  sheaf on `yoneda.obj (Over.mk (𝟙 U))` to the free abelian sheaf on `yoneda.obj U`.

## Main results

* `Stacks.Cohomology.OverObjectCohomology.h'IsoHOver` and `h'AddEquivHOver`: **the comparison**
  `H^n(U, F) ≅ H^n(F|_U)`, as an isomorphism in `AddCommGrpCat` and as an additive equivalence
  of the underlying groups; `h'AddEquivHOverSheafPullback` is the same with the extension by
  zero taken to be Mathlib's `CategoryTheory.Functor.sheafPullback`.
* `Stacks.Cohomology.OverObjectCohomology.subsingleton_H_over_iff_subsingleton_H'`: the
  vanishing of the one is the vanishing of the other.

## Implementation notes

No `@[stacks]` attribute is placed: this compares two of Mathlib's definitions. The closest
statement of the Stacks project, 03F3(2), is the same comparison for modules over a ringed site
rather than for abelian sheaves, and its proof is the same two ingredients — restriction to the
slice site preserves injectives, and the sections over `U` do not change.

The extension by zero `j_!` enters as an explicit adjunction `L ⊣ J.overPullback _ U` rather
than through `CategoryTheory.Functor.sheafPullback`, so that no existence hypothesis for the
left Kan extension along `(Over.forget U).op` has to be carried; `Functor.sheafPullback`
together with `Functor.sheafAdjunctionContinuous` provides such an `L` whenever that Kan
extension exists; `h'AddEquivHOverSheafPullback` carries out that instantiation. The properties
of the localization that the comparison genuinely needs are exactness of `j^*` (left exactness
because `j^*` is a right adjoint, right exactness because it is also a left adjoint,
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`) and that `j^*` preserves injectives
(`Functor.PreservesInjectiveObjects`, equivalent to left exactness of `j_!`); these are carried
as instance hypotheses. Additivity of `j^*` is proved outright: it acts on morphisms by
precomposition.

`Sheaf.H` is stated for coefficients in `AddCommGrpCat.{w}` and `Sheaf.H'` for coefficients in
`AddCommGrpCat.{v}` with `v` the universe of the homs of `C`; the comparison therefore exists
only at `w = v`, which is how both are instantiated throughout this repository. Note that the
homs of `Over U` are again in `Type v`, so the slice site takes the same coefficients.

## References

* `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, where the statement is a `TODO`.
* `Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`, whose proof that a fully faithful
  exact functor preserving injectives induces bijections on `Ext` is the model for the induction
  in `extAdjHom_bijective`.
* [The Stacks project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3), part (2), for the
  same comparison for modules over a ringed site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w w' v v' u u'

namespace Stacks.Cohomology.OverObjectCohomology

/-! ### `Ext`-groups along an exact adjunction -/

section ExactAdjunction

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} C] [HasExt.{w} D]

/-- The comparison map `Ext^n (L X, Y) → Ext^n (X, R Y)` attached to an adjunction `L ⊣ R` with
`R` exact: apply `R` to an `Ext`-class and compose with the unit of the adjunction. -/
def extAdjHom (X : D) (Y : C) (n : ℕ) : Ext.{w} (L.obj X) Y n →+ Ext.{w} X (R.obj Y) n :=
  ((Ext.mk₀ (adj.unit.app X)).precomp (R.obj Y) (zero_add n)).comp
    (R.mapExtAddHom (L.obj X) Y n)

/-- The comparison map sends `e` to the composite of the unit `X ⟶ R (L X)`, viewed in degree `0`,
with the image of `e` under `R`. -/
lemma extAdjHom_apply (X : D) (Y : C) (n : ℕ) (e : Ext.{w} (L.obj X) Y n) :
    extAdjHom adj X Y n e =
      (Ext.mk₀ (adj.unit.app X)).comp (Ext.mapExactFunctor R e) (zero_add n) := rfl

/-- In degree `0` the comparison map is the bijection of the adjunction. -/
lemma extAdjHom_mk₀ (X : D) (Y : C) (f : L.obj X ⟶ Y) :
    extAdjHom adj X Y 0 (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv X Y f) := by
  rw [extAdjHom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, adj.homEquiv_unit]

/-- In degree `0` the comparison map `Ext^0 (L X, Y) → Ext^0 (X, R Y)` is bijective. -/
lemma extAdjHom_bijective_zero (X : D) (Y : C) :
    Function.Bijective (extAdjHom adj X Y 0) := by
  have h : (extAdjHom adj X Y 0 : Ext.{w} (L.obj X) Y 0 → _) ∘ Ext.mk₀ =
      Ext.mk₀ ∘ (adj.homEquiv X Y) :=
    funext (extAdjHom_mk₀ adj X Y)
  refine ((Ext.mk₀_bijective (L.obj X) Y).of_comp_iff _).mp ?_
  rw [h]
  exact (Ext.mk₀_bijective X (R.obj Y)).comp (adj.homEquiv X Y).bijective

/-- The comparison map sends a composite `e.comp β` to the composite of the comparison of `e`
with the image of `β` under `R`. -/
private lemma extAdjHom_comp (X : D) {Y Z : C} {a b c : ℕ} (e : Ext.{w} (L.obj X) Y a)
    (β : Ext.{w} Y Z b) (h : a + b = c) :
    extAdjHom adj X Z c (e.comp β h) =
      (extAdjHom adj X Y a e).comp (Ext.mapExactFunctor R β) h := by
  rw [extAdjHom_apply, extAdjHom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by omega)).symm

/-- The comparison map is compatible with the covariant functoriality of `Ext` in its second
variable. -/
lemma extAdjHom_postcomp (X : D) {Y Y' : C} (g : Y ⟶ Y') (n : ℕ) :
    (extAdjHom adj X Y' n).comp ((Ext.mk₀ g).postcomp (L.obj X) (add_zero n)) =
      ((Ext.mk₀ (R.map g)).postcomp X (add_zero n)).comp (extAdjHom adj X Y n) := by
  ext e
  change extAdjHom adj X Y' n (e.comp (Ext.mk₀ g) (add_zero n)) =
    (extAdjHom adj X Y n e).comp (Ext.mk₀ (R.map g)) (add_zero n)
  rw [extAdjHom_comp, Ext.mapExactFunctor_mk₀]

/-- The comparison map is compatible with the connecting maps of the covariant `Ext`-sequence of
a short exact sequence. -/
lemma extAdjHom_extClass (X : D) {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℕ)
    (h : n₀ + 1 = n₁) :
    (extAdjHom adj X S.X₁ n₁).comp (hS.extClass.postcomp (L.obj X) h) =
      ((hS.map_of_exact R).extClass.postcomp X h).comp (extAdjHom adj X S.X₃ n₀) := by
  ext e
  change extAdjHom adj X S.X₁ n₁ (e.comp hS.extClass h) =
    (extAdjHom adj X S.X₃ n₀ e).comp (hS.map_of_exact R).extClass h
  rw [extAdjHom_comp, Ext.mapExactFunctor_extClass]

attribute [local instance] Ext.subsingleton_of_injective in
/-- **The `Ext`-comparison along an exact adjunction is bijective.** Both covariant
`Ext`-sequences attached to an injective presentation of `Y` are exact, and `Ext^{n+1}` into an
injective object vanishes, so the comparison in degree `n + 1` is squeezed between comparisons
in degree `n`. -/
lemma extAdjHom_bijective [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (X : D) (Y : C) (n : ℕ) : Function.Bijective (extAdjHom adj X Y n) := by
  induction n generalizing Y with
  | zero => exact extAdjHom_bijective_zero adj X Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map R).X₂ :=
      Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extAdjHom adj X S.X₂ n) (extAdjHom adj X S.X₃ n) (extAdjHom adj X S.X₁ (n + 1))
      (extAdjHom_postcomp adj X S.g n).symm (extAdjHom_extClass adj X hS n (n + 1) rfl).symm
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj X) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X (hS.map_of_exact R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁ (by subsingleton) rfl)

/-- **`Ext`-groups along an exact adjunction.** For an adjunction `L ⊣ R` of abelian categories
with `R` exact and preserving injectives, and with enough injectives in the target of `L`, one
has `Ext^n (L X, Y) ≅ Ext^n (X, R Y)`. -/
def extAdjEquiv [EnoughInjectives C] [R.PreservesInjectiveObjects] (X : D) (Y : C) (n : ℕ) :
    Ext.{w} (L.obj X) Y n ≃+ Ext.{w} X (R.obj Y) n :=
  AddEquiv.ofBijective (extAdjHom adj X Y n) (extAdjHom_bijective adj X Y n)

end ExactAdjunction

/-! ### The free abelian sheaf on a representable presheaf -/

section FreeYoneda

variable {C : Type u} [Category.{v} C]

/-- The sheaf corepresenting `CategoryTheory.Sheaf.H' · n X`: the sheafification of the free
abelian presheaf on `yoneda.obj X`. -/
abbrev freeYonedaSheaf (K : GrothendieckTopology C) [HasWeakSheafify K AddCommGrpCat.{v}]
    (X : C) : Sheaf K AddCommGrpCat.{v} :=
  (presheafToSheaf K AddCommGrpCat.{v}).obj (yoneda.obj X ⋙ AddCommGrpCat.free)

variable (K : GrothendieckTopology C) [HasWeakSheafify K AddCommGrpCat.{v}]

/-- **The free abelian sheaf on `yoneda.obj X` corepresents evaluation at `X`**: morphisms from
it to a sheaf `F` are the sections of `F` over `X`. This is the sheafification adjunction, the
free-forgetful adjunction on abelian groups and the Yoneda lemma, composed. -/
@[sga "4 XVIII 1.4.24" "(a), special case", sga "7 VII 1.4" "partial"]
def freeYonedaSheafHomEquiv (X : C) (F : Sheaf K AddCommGrpCat.{v}) :
    (freeYonedaSheaf K X ⟶ F) ≃ F.obj.obj (op X) :=
  ((sheafificationAdjunction K AddCommGrpCat.{v}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj X) F.obj).trans yonedaEquiv)

/-- The corepresentation `freeYonedaSheafHomEquiv` is natural in the sheaf. -/
lemma freeYonedaSheafHomEquiv_comp (X : C) {F F' : Sheaf K AddCommGrpCat.{v}}
    (α : freeYonedaSheaf K X ⟶ F) (g : F ⟶ F') :
    freeYonedaSheafHomEquiv K X F' (α ≫ g) =
      g.hom.app (op X) (freeYonedaSheafHomEquiv K X F α) := by
  dsimp only [freeYonedaSheafHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  exact yonedaEquiv_comp _ _

/-- The inverse form of the naturality of `freeYonedaSheafHomEquiv`: the morphism attached to a
section pushed along `g` is the morphism attached to the section, followed by `g`. -/
lemma freeYonedaSheafHomEquiv_symm_comp (X : C) {F F' : Sheaf K AddCommGrpCat.{v}} (g : F ⟶ F')
    (x : F.obj.obj (op X)) :
    (freeYonedaSheafHomEquiv K X F').symm (g.hom.app (op X) x) =
      (freeYonedaSheafHomEquiv K X F).symm x ≫ g := by
  apply (freeYonedaSheafHomEquiv K X F').injective
  rw [Equiv.apply_symm_apply, freeYonedaSheafHomEquiv_comp, Equiv.apply_symm_apply]

end FreeYoneda

/-! ### Extension by zero of the free abelian sheaf on the slice site -/

section Slice

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasWeakSheafify J AddCommGrpCat.{v}] [HasWeakSheafify (J.over U) AddCommGrpCat.{v}]
  {L : Sheaf (J.over U) AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{v}}

/-- Restriction to the slice site is additive: it acts on a morphism of sheaves by
precomposition with `(Over.forget U).op`, and addition of morphisms of sheaves is computed
objectwise. -/
instance : (J.overPullback AddCommGrpCat.{v} U).Additive where
  map_add := rfl

/-- Morphisms from the free abelian sheaf on `yoneda.obj (Over.mk (𝟙 U))` to the restriction of
`F` to the slice site are the sections of `F` over `U`: restriction does not change the sections
over `Over.mk (𝟙 U)`, whose underlying object is `U`. -/
def sliceSectionsEquiv (F : Sheaf J AddCommGrpCat.{v}) :
    (freeYonedaSheaf (J.over U) (Over.mk (𝟙 U)) ⟶ (J.overPullback AddCommGrpCat.{v} U).obj F) ≃
      F.obj.obj (op U) :=
  freeYonedaSheafHomEquiv (J.over U) (Over.mk (𝟙 U)) ((J.overPullback AddCommGrpCat.{v} U).obj F)

omit [HasWeakSheafify J AddCommGrpCat.{v}] in
/-- The inverse of `sliceSectionsEquiv` is natural in the sheaf. -/
lemma sliceSectionsEquiv_symm_comp {F F' : Sheaf J AddCommGrpCat.{v}} (g : F ⟶ F')
    (x : F.obj.obj (op U)) :
    (sliceSectionsEquiv J U F').symm (g.hom.app (op U) x) =
      (sliceSectionsEquiv J U F).symm x ≫ (J.overPullback AddCommGrpCat.{v} U).map g :=
  freeYonedaSheafHomEquiv_symm_comp (J.over U) (Over.mk (𝟙 U))
    ((J.overPullback AddCommGrpCat.{v} U).map g) x

/-- **The two corepresenting sheaves agree.** Morphisms out of the free abelian sheaf on
`yoneda.obj U` and out of the extension by zero of the free abelian sheaf on
`yoneda.obj (Over.mk (𝟙 U))` are the same thing: both are sections over `U`, the second because
restriction to the slice site does not change the sections over `Over.mk (𝟙 U)`. -/
def homEquivOverPullback (adj : L ⊣ J.overPullback AddCommGrpCat.{v} U)
    (F : Sheaf J AddCommGrpCat.{v}) :
    (freeYonedaSheaf J U ⟶ F) ≃ (L.obj (freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))) ⟶ F) :=
  (freeYonedaSheafHomEquiv J U F).trans
    ((sliceSectionsEquiv J U F).symm.trans (adj.homEquiv _ F).symm)

/-- The bijection `homEquivOverPullback` is natural in the sheaf. -/
lemma homEquivOverPullback_comp (adj : L ⊣ J.overPullback AddCommGrpCat.{v} U)
    {F F' : Sheaf J AddCommGrpCat.{v}} (α : freeYonedaSheaf J U ⟶ F) (g : F ⟶ F') :
    homEquivOverPullback J U adj F' (α ≫ g) = homEquivOverPullback J U adj F α ≫ g := by
  dsimp only [homEquivOverPullback, Equiv.trans_apply]
  rw [freeYonedaSheafHomEquiv_comp, sliceSectionsEquiv_symm_comp,
    Adjunction.homEquiv_naturality_right_symm]

/-- **Extension by zero of the free abelian sheaf on the slice site.** For `T = Over.mk (𝟙 U)`,
the terminal object of `Over U`, the sheaf `j_!` of the free abelian sheaf on `yoneda.obj T` is
the free abelian sheaf on `yoneda.obj U`. Both corepresent the sections over `U`. -/
def freeYonedaSheafOverIso (adj : L ⊣ J.overPullback AddCommGrpCat.{v} U) :
    L.obj (freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))) ≅ freeYonedaSheaf J U :=
  Functor.CorepresentableBy.uniqueUpToIso
    (F := coyoneda.obj (op (freeYonedaSheaf J U)))
    { homEquiv := fun {F} => (homEquivOverPullback J U adj F).symm
      homEquiv_comp := fun {F F'} g f => by
        apply (homEquivOverPullback J U adj F').injective
        rw [Equiv.apply_symm_apply]
        change _ = homEquivOverPullback J U adj F' ((homEquivOverPullback J U adj F).symm f ≫ g)
        rw [homEquivOverPullback_comp, Equiv.apply_symm_apply] }
    { homEquiv := Equiv.refl _
      homEquiv_comp := fun _ _ => rfl }

end Slice

/-! ### The comparison on cohomology -/

section Comparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify (J.over U) AddCommGrpCat.{v}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w'} (Sheaf (J.over U) AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [PreservesFiniteLimits (J.overPullback AddCommGrpCat.{v} U)]
  [PreservesFiniteColimits (J.overPullback AddCommGrpCat.{v} U)]
  [(J.overPullback AddCommGrpCat.{v} U).PreservesInjectiveObjects]
  {L : Sheaf (J.over U) AddCommGrpCat.{v} ⥤ Sheaf J AddCommGrpCat.{v}}

/-- **Sheaf cohomology over an object is global cohomology on the slice site.** For an abelian
sheaf `F` on a site `(C, J)`, a degree `n` and an object `U : C`,
`H^n(U, F) ≅ H^n(F|_U)`, the cohomology of the restriction of `F` to `(Over U, J.over U)`.

The three steps are: the corepresenting sheaf of `H^n(U, ·)` is the extension by zero of the
corepresenting sheaf of `H^n(Over.mk (𝟙 U), ·)` on the slice site; `Ext` transforms along the
adjunction `j_! ⊣ j^*`; and `Over.mk (𝟙 U)` is terminal in `Over U`. -/
def h'IsoHOver (adj : L ⊣ J.overPullback AddCommGrpCat.{v} U) (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) : Sheaf.H' F n U ≅ AddCommGrpCat.of (Sheaf.H.{w'} (F.over U) n) :=
  ((extFunctor n).mapIso (freeYonedaSheafOverIso J U adj).op).app F ≪≫
    (extAdjEquiv adj (freeYonedaSheaf (J.over U) (Over.mk (𝟙 U))) F n).toAddCommGrpIso ≪≫
      TerminalCohomology.h'IsoH (J.over U) (F.over U) n (Over.mk (𝟙 U)) Over.mkIdTerminal

/-- The comparison `H^n(U, F) ≅ H^n(F|_U)` of `h'IsoHOver`, read as an additive equivalence of
the underlying groups. This is the `TODO` of `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
asking for `(F.cohomologyPresheaf n).obj (Opposite.op U) ≃+ Sheaf.H (F.over U) n`. -/
def h'AddEquivHOver (adj : L ⊣ J.overPullback AddCommGrpCat.{v} U)
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    Sheaf.H' F n U ≃+ Sheaf.H.{w'} (F.over U) n :=
  (h'IsoHOver J U adj F n).addCommGroupIsoToAddEquiv

/-- **Vanishing over an object is vanishing on the slice site.** A vanishing theorem whose
conclusion is about `CategoryTheory.Sheaf.H'` over an object `U` is a vanishing theorem about the
global cohomology of the restricted sheaf, and conversely. -/
theorem subsingleton_H_over_iff_subsingleton_H'
    (adj : L ⊣ J.overPullback AddCommGrpCat.{v} U) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    Subsingleton (Sheaf.H.{w'} (F.over U) n) ↔ Subsingleton (Sheaf.H' F n U) :=
  (h'AddEquivHOver J U adj F n).toEquiv.subsingleton_congr.symm

/-- **The comparison, with `j_!` supplied by Mathlib.** The same statement as
`h'AddEquivHOver`, with the extension by zero taken to be
`CategoryTheory.Functor.sheafPullback` along `Over.forget U`; this is the form in which the
`TODO` of `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` is phrased. -/
def h'AddEquivHOverSheafPullback
    [∀ G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{v}, (Over.forget U).op.HasLeftKanExtension G]
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    (F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H.{w'} (F.over U) n :=
  h'AddEquivHOver J U
    (Functor.sheafAdjunctionContinuous (Over.forget U) AddCommGrpCat.{v} (J.over U) J) F n

end Comparison

end Stacks.Cohomology.OverObjectCohomology

end
