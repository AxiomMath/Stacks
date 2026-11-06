module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-! # The single-complex model crossing is the `D⁺` crossing

For an additive `w : A ⥤ B` with `A` having enough injectives and K-injective resolutions, and an
unbounded right derived functor `(Rw, α)` of `w`, two isomorphisms

> `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)`

are available. `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` reads both
sides off the chosen injective resolution: the left-hand side because the extended resolution is
K-injective, so `α` is invertible there, and the right-hand side by definition. The other route
goes through `D⁺`: `CategoryTheory.Functor.boundedDerivedIso` identifies `Rw` on the bounded below
objects with the right derived functor `Rw⁺` built from injective resolutions, and
`Stacks.DerivedIndexing.rightDerivedIso` compares the two indexings of that one.

**This file proves the two agree.** The model crossing carried, until now, no compatibility lemma
at all — not even a `_hom_app`; after this a statement proved in the
`CategoryTheory.Functor.rightDerivedPlus` model may be read at the unbounded model, and
conversely.

The one place this is needed. [Stacks, Tag 089W],
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`, is two descents through the
universal property of `rightDerivedFunctorPlus`; the route conclusion (c) of [Stacks, Tag 0EX3]
takes to the same isomorphism is a descent through the universal property of the unbounded total
right derived functor, namely the Leray comparison of
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison` followed by the cohomology edge
morphism. Comparing them is comparing the two models.

## Main results

All in the namespace `Stacks.DerivedFunctor`.

* `comp_boundedDerivedIso_inv_app`: **`α` followed by the `D⁺` crossing is the unit of `Rw⁺`.**
  This is the second, and it is the pinning
  `CategoryTheory.Functor.boundedDerivedIso_hom_app` in the shape a chase meets. No invertibility
  of either unit is needed.
* `comp_resCompUnitIso_inv_app_comp`: **the two routes agree before cohomology is taken** — `Rw`
  of the comparison with the resolution, `α` inverted, the unit of `Rw⁺` and the comparison
  upstairs inverted, is the `D⁺` crossing at `X[0]`.
* `singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso` and
  `…_hom_app`: **the two crossings agree.**

## Implementation notes

*The first of the two differences between the routes is not proved here — it already exists.*
That the comparison `X[0] ≅ Qh(resH X)` is the same in `D⁺(A)` and in `D(A)` is
`Stacks.DerivedIndexing.ι_map_singleIsoResPlusQh_hom_app_eq`
(`StacksFrontier/Homology/DerivedIndexing/Composite.lean:985`), whose right-hand side is this
file's `singleIsoResCompQh` written out — `CategoryTheory.DerivedCategory.singleFunctorIsoCompQh`
followed by `Qh` of the augmentation — so the two agree by `rfl` and the chase below applies it
through that `rfl`; nothing about it is re-proved here.

*`comp_boundedDerivedIso_inv_app` at the direct image is one step from an existing lemma.* At
`F = RingedSpaceModuleAdjunction.modulePushforward f` it is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.boundedDerivedPushforwardIso_hom_app`
(`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/BoundedComparison.lean:194`)
composed with `CategoryTheory.Iso.hom_inv_id_app`; what is proved here is that step at an
arbitrary additive functor, which is what a statement about sections needs.

*Every coherence between the two routes is the identity.*
`CategoryTheory.DerivedCategory.Plus.singleFunctorιIso`,
`CategoryTheory.DerivedCategory.Plus.QhCompιIsoιCompQh`,
`Stacks.DerivedIndexing.resPlusCompιIso` and `Stacks.DerivedIndexing.mapPlusCompιIso` are all
`Iso.refl`, and `CategoryTheory.DerivedCategory.Plus.homologyFunctor` is by definition
`Plus.ι ⋙ homologyFunctor`. So the five steps of
`Stacks.DerivedIndexing.rightDerivedPlusIsoRes` contribute only two morphisms — the comparison
with the resolution and the inverted unit of `Rw⁺` — and the two routes differ by exactly the two
lemmas above together with the naturality of the `D⁺` crossing.

*Elaboration facts about the assembly.* (1) The
statement `Hⁿ(crossing) ≫ (rightDerivedIso w n).hom.app X = …` is type-correct only at default
transparency, because `CategoryTheory.DerivedCategory.Plus.homologyFunctor` has to unfold to
`Plus.ι ⋙ homologyFunctor` at the junction; consequently `simp only [Iso.trans_inv]` cannot
descend into the second factor and the five-step chain
`Stacks.DerivedIndexing.rightDerivedPlusIsoRes` stays folded, however many expansion lemmas are
supplied. Composing the statement with `(rightDerivedIso w n).hom` instead — so that each side is
separately reducibly type-correct — does let `Stacks.DerivedIndexing.rightDerivedIsoRes` cancel,
and that form is the one to start from. (2) `CategoryTheory.Iso.trans_inv` iterated produces a
**left**-associated composite, so an expansion of `rightDerivedPlusIsoRes.inv` into its five
`zStep` components is `rfl` only when written `((((e ≫ d) ≫ c) ≫ b) ≫ a)`; the right-associated
spelling is not definitionally equal. (3) `Stacks.DerivedIndexing.zStep₃` is a whiskering of
`Stacks.DerivedIndexing.plusHomologyIso`, which is itself a two-step composite, so its component
is not a single component of `CategoryTheory.DerivedCategory.homologyFunctorFactorsh`; and its
`.app` sits at different universe arguments than that one, so no `rfl` relates them.

(4) The three identity factors must carry the spelling that makes the expansion `rfl`:
`(w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ HomotopyCategory.homologyFunctor B _ n).map (𝟙 _)`,
**not** `(HomotopyCategory.homologyFunctor B _ n).map (𝟙 _)` — the latter is the same morphism but
needs `CategoryTheory.Functor.map_id` for the inner functor, which `rfl` will not do. So the
`map_id` arguments handed to `collapse_chain` carry their functor explicitly instead of by
underscore; left to the unifier, it solves them to the second spelling and the application fails.

*Why the component statements, and not the natural isomorphisms.* At an object the grouping of a
threefold functor composite does not arise. Note that the blanket claim that `(E ⋙ G) ⋙ H` and
`E ⋙ (G ⋙ H)` "are not unifiable" is **wrong** (see also
`DerivedFunctorSingleRightDerived.lean`): the obstruction is a metavariable
in the middle of an `Iso.trans` chain, not the regrouping itself, and
`CompositionViaPlus.lean` composes the two groupings with no reassociation at all.

## References

* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 05T5](https://stacks.math.columbia.edu/tag/05T5)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Cancelling a retraction off the end of a known composite. Stated at variables of an
abstract category, where the reassociation is free; at the concrete spelling of a derived functor
`CategoryTheory.Category.assoc` is not available to `rw`, the type of the composite not being
type-correct at `implicit` transparency. -/
private lemma comp_cancel_right {C : Type*} [Category* C] {X Y Z : C} {a : X ⟶ Y} {b : X ⟶ Z}
    {c : Z ⟶ Y} (h : a = b ≫ c) {d : Y ⟶ Z} (hcd : c ≫ d = 𝟙 Z) : a ≫ d = b := by
  rw [h, Category.assoc, hcd, Category.comp_id]

variable (w : A ⥤ B) [w.Additive]
  (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **`α` followed by the `D⁺` crossing is the unit of `Rw⁺`.** The pinning
`CategoryTheory.Functor.boundedDerivedIso_hom_app` reads
`ι(unit of Rw⁺) ≫ crossing = α`; composed with the crossing's inverse this is the form the chase
below meets, and it needs no invertibility of either unit. -/
theorem comp_boundedDerivedIso_inv_app
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (K : HomotopyCategory.Plus A) :
    α.app ((HomotopyCategory.Plus.ι A).obj K) ≫
        (Functor.boundedDerivedIso w Rw α hres).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.ι.map (w.rightDerivedFunctorPlusUnith.app K) :=
  comp_cancel_right (Functor.boundedDerivedIso_hom_app w Rw α hres K).symm
    (Iso.hom_inv_id_app (Functor.boundedDerivedIso w Rw α hres)
      (DerivedCategory.Plus.Qh.obj K))

/-- The four-step chase that compares the two crossings, at variables of an abstract category.
Its four hypotheses are, in order: the two comparisons with the resolution agree, `α` followed by
the `D⁺` crossing is the unit of `Rw⁺`, the naturality of the crossing, and the cancellation of
the comparison with the resolution upstairs. -/
private lemma chase_four {C : Type*} [Category* C] {P Q R S T : C}
    {a a' : P ⟶ Q} (haa : a = a') {b : Q ⟶ R} {u : R ⟶ S} {m : Q ⟶ S} (hbu : b ≫ u = m)
    {g : P ⟶ T} {k : T ⟶ S} (ham : a' ≫ m = g ≫ k) {v : S ⟶ T} (hkv : k ≫ v = 𝟙 T) :
    a ≫ b ≫ u ≫ v = g := by
  rw [haa, ← Category.assoc b, hbu, ← Category.assoc]
  exact comp_cancel_right ham hkv

/-- A retraction read off a composite that is known on the other side. At variables. -/
private lemma inv_comp_eq {C : Type*} [Category* C] {X Y Z : C} {p : X ⟶ Y} {q : Y ⟶ X}
    (hpq : q ≫ p = 𝟙 Y) {f : X ⟶ Z} {g : Y ⟶ Z} (h : p ≫ g = f) : q ≫ f = g := by
  rw [← h, ← Category.assoc, hpq, Category.id_comp]

/-- Two functors applied to a pair of mutually inverse morphisms. At variables. -/
private lemma map_map_comp_eq_id {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (G : C ⥤ D) (H : D ⥤ E) {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} (h : f ≫ g = 𝟙 X) :
    H.map (G.map f) ≫ H.map (G.map g) = 𝟙 (H.obj (G.obj X)) := by
  rw [← H.map_comp, ← G.map_comp, h, G.map_id, H.map_id]

/-- **The two models of the right derived functor agree, before taking cohomology.** The route
through the chosen injective resolution — `Rw` of the comparison `X[0] ≅ Qh(resH X)`, then `α`
inverted, then the unit of `Rw⁺` and the comparison upstairs inverted — is the `D⁺`-to-`D`
crossing at `X[0]`.

The four steps are `Stacks.DerivedIndexing.ι_map_singleIsoResPlusQh_hom_app_eq`,
`comp_boundedDerivedIso_inv_app`, the
naturality of the crossing at the comparison with the resolution, and the cancellation of that
comparison under `Rw⁺`; `chase_four` puts them together at variables, where the reassociations
are free. -/
theorem comp_resCompUnitIso_inv_app_comp
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (X : A) :
    Rw.map ((singleIsoResCompQh (A := A)).hom.app X) ≫
        (resCompUnitIso w Rw α hres).inv.app X ≫
          DerivedCategory.Plus.ι.map
              (w.rightDerivedFunctorPlusUnith.app (Stacks.DerivedIndexing.resPlus.obj X)) ≫
            DerivedCategory.Plus.ι.map (w.rightDerivedFunctorPlus.map
              ((Stacks.DerivedIndexing.singleIsoResPlusQh (C := A)).inv.app X)) =
      (Functor.boundedDerivedIso w Rw α hres).inv.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) :=
  chase_four
    (congrArg Rw.map
      ((rfl : (singleIsoResCompQh (A := A)).hom.app X =
            (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app X ≫
              DerivedCategory.Qh.map (Stacks.DerivedIndexing.resUnit.app X)).trans
        (Stacks.DerivedIndexing.ι_map_singleIsoResPlusQh_hom_app_eq (C := A) X).symm))
    (inv_comp_eq
      (Iso.inv_hom_id_app (resCompUnitIso w Rw α hres) X)
      (comp_boundedDerivedIso_inv_app w Rw α hres (Stacks.DerivedIndexing.resPlus.obj X)))
    ((Functor.boundedDerivedIso w Rw α hres).inv.naturality
      ((Stacks.DerivedIndexing.singleIsoResPlusQh (C := A)).hom.app X))
    (map_map_comp_eq_id w.rightDerivedFunctorPlus DerivedCategory.Plus.ι
      (Iso.hom_inv_id_app (Stacks.DerivedIndexing.singleIsoResPlusQh (C := A)) X))

/-- **The five steps of `Stacks.DerivedIndexing.rightDerivedPlusIsoRes`, inverted and written
out.** Three of the five contribute a functor image of an identity and the fourth contributes the
inverse of `CategoryTheory.DerivedCategory.homologyFunctorFactorsh`; what is left is the unit of
`Rw⁺` at the extended chosen resolution and the comparison of the single complex with that
resolution, both read in `D(B)` through the inclusion.

It is `rfl`, in the **left**-associated bracketing: `CategoryTheory.Iso.trans_inv` iterated
produces that bracketing and composition is not definitionally associative, so the
right-associated spelling is not definitionally equal. -/
private lemma rightDerivedPlusIsoRes_inv_app_eq (n : ℤ) (X : A) :
    (Stacks.DerivedIndexing.rightDerivedPlusIsoRes w n).inv.app X =
      ((((w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
                HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map (𝟙 _) ≫
              (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) n).map (𝟙 _)) ≫
            (DerivedCategory.homologyFunctorFactorsh B n).inv.app
                ((HomotopyCategory.Plus.ι B).obj
                  (w.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj X))) ≫
              (DerivedCategory.homologyFunctor B n).map (𝟙 _)) ≫
          (DerivedCategory.homologyFunctor B n).map
            (DerivedCategory.Plus.ι.map
              (w.rightDerivedFunctorPlusUnith.app (Stacks.DerivedIndexing.resPlus.obj X)))) ≫
        (DerivedCategory.homologyFunctor B n).map
          (DerivedCategory.Plus.ι.map (w.rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.singleIsoResPlusQh (C := A)).inv.app X))) :=
  rfl

/-- The collapse of that chain against the comparison standing in front of it, at variables of an
abstract category: three of its factors are identities and a fourth cancels the comparison, so
what the whole composite does is what its last two factors do. -/
private lemma collapse_chain {C : Type*} [Category* C] {P Q R S T U₀ : C}
    (a : P ⟶ Q) (b : Q ⟶ R) {h : R ⟶ S} {hi : S ⟶ R} (hh : h ≫ hi = 𝟙 R)
    {e₁ e₂ : S ⟶ S} (he₁ : e₁ = 𝟙 S) (he₂ : e₂ = 𝟙 S) {e₃ : R ⟶ R} (he₃ : e₃ = 𝟙 R)
    {u : R ⟶ T} {v : T ⟶ U₀} {ch : S ⟶ U₀}
    (hch : ch = (((e₁ ≫ e₂) ≫ hi ≫ e₃) ≫ u) ≫ v)
    {g : P ⟶ U₀} (hg : a ≫ b ≫ u ≫ v = g) :
    a ≫ b ≫ h ≫ ch = g := by
  subst hch he₁ he₂ he₃
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Category.assoc h hi, hh, Category.id_comp]
  exact hg

/-- A four-fold composite carried through a functor. At variables. -/
private lemma map_four {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {P Q R T U₀ : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {u : R ⟶ T} {v : T ⟶ U₀} {g : P ⟶ U₀}
    (h : a ≫ b ≫ u ≫ v = g) :
    F.map a ≫ F.map b ≫ F.map u ≫ F.map v = F.map g := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, h]

/-- **The two models of the right derived functor at a single complex agree.** For an additive
`w : A ⥤ B` with `A` having enough injectives and K-injective resolutions, and any unbounded right
derived functor `(Rw, α)` of `w`, the crossing
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` — read off the chosen
injective resolution — is the `D⁺`-to-`D` crossing
`CategoryTheory.Functor.boundedDerivedIso` followed by the comparison
`Stacks.DerivedIndexing.rightDerivedIso` of the two indexings:

> `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` is `Hⁿ(crossing)` followed by `Rⁿ⁺w(X) ≅ Rⁿw(X)`.

Stated with the indexing comparison on the left, so that each side is separately type-correct at
`implicit` transparency: at the spelling with it moved to the right
`CategoryTheory.DerivedCategory.Plus.homologyFunctor` has to unfold at the junction, and then
`simp` cannot descend into the five-step chain
`Stacks.DerivedIndexing.rightDerivedPlusIsoRes` at all.

This is the compatibility that lets a statement proved in the
`CategoryTheory.Functor.rightDerivedPlus` model — [Stacks, Tag 089W] among them — be read at the
unbounded model, and conversely. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (n : ℕ) (X : A) :
    (singleCompDerivedCompHomologyIsoRightDerived w Rw α hres n).hom.app X ≫
        (Stacks.DerivedIndexing.rightDerivedIso w n).hom.app X =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        ((Functor.boundedDerivedIso w Rw α hres).inv.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  simp only [singleCompDerivedCompHomologyIsoRightDerived, Stacks.DerivedIndexing.rightDerivedIso,
    resCompQhReassocIso, resCompMapQhHomologyIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.refl_hom, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc, Functor.comp_obj,
    Functor.comp_map]
  exact collapse_chain _ _
    (Iso.hom_inv_id_app (DerivedCategory.homologyFunctorFactorsh B (n : ℤ))
      ((HomotopyCategory.Plus.ι B).obj
        (w.mapHomotopyCategoryPlus.obj (Stacks.DerivedIndexing.resPlus.obj X))))
    (CategoryTheory.Functor.map_id (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)) _)
    (CategoryTheory.Functor.map_id
      (HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ)) _)
    (CategoryTheory.Functor.map_id (DerivedCategory.homologyFunctor B (n : ℤ)) _)
    (rightDerivedPlusIsoRes_inv_app_eq w (n : ℤ) X)
    (map_four (DerivedCategory.homologyFunctor B (n : ℤ))
      (comp_resCompUnitIso_inv_app_comp w Rw α hres X))

/-- **The two models of the right derived functor at a single complex agree**, solved for the
crossing of `DerivedFunctorSingleRightDerived.lean`:

> `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` is `Hⁿ` of the `D⁺`-to-`D` crossing followed by the comparison of the
> two indexings, inverted.

This is `singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso` with
`Stacks.DerivedIndexing.rightDerivedIso` carried to the other side; it is the form in which a
consumer holding a statement about `CategoryTheory.Functor.rightDerived` — [Stacks, Tag 089W] is
one — reads it at the unbounded model.

It is not `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app`, which
writes the same component as the four-factor composite through the chosen resolution; this one
writes it through `CategoryTheory.Functor.boundedDerivedIso`. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_hom_app_boundedDerivedIso
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) (n : ℕ) (X : A) :
    (singleCompDerivedCompHomologyIsoRightDerived w Rw α hres n).hom.app X =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          ((Functor.boundedDerivedIso w Rw α hres).inv.app
            ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
        (Stacks.DerivedIndexing.rightDerivedIso w n).inv.app X :=
  (comp_cancel_right
    (singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso
      w Rw α hres n X).symm
    (Iso.hom_inv_id_app (Stacks.DerivedIndexing.rightDerivedIso w n) X)).symm

end Stacks.DerivedFunctor

end
