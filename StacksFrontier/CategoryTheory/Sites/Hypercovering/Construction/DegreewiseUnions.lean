module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Types.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoskeletalAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.DisjointUnions
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf

/-!
# Degreewise disjoint unions in a hypercovering

Let `C` be a site with fibre products and equalizers and let `K` be a hypercovering, that is, a
hypercovering of the final presheaf.  If the coproduct of the objects indexed in each degree of
`K` exists and the resulting map from the coproduct of their representable presheaves to the
presheaf represented by the coproduct becomes an isomorphism after sheafification, then
replacing each degree by the one-element family on that coproduct again gives a hypercovering.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.degreewiseUnions` replaces each degree of a simplicial
  semi-representable object by the one-element family on the coproduct of its objects.
* `Stacks.CategoryTheory.Hypercovering.toDegreewiseUnions` is the canonical morphism to it,
  given in each degree by the coproduct inclusions.
* `Stacks.CategoryTheory.Hypercovering.unionsAugmentation` is the unique augmentation of the
  degreewise disjoint unions towards the final presheaf.
* `Stacks.CategoryTheory.Hypercovering.hypercoveringDegreewiseUnions` is the hypercovering
  structure carried by `degreewiseUnions` under those two hypotheses.

## Implementation notes

The construction is the one of `takeUnionsSimplicial`, carried out on an arbitrary site rather
than on a slice `Over X`: the present remark is the absolute statement, whose hypotheses are the
degreewise existence of the coproducts and a condition on sheafifications, whereas the relative
statement over an object instead assumes a decomposition of fibre products and a condition on
coverings.

Hypothesis (b) of the source, that `∐ h_{U_{n,i}} → h_{U_n}` induces an isomorphism on
sheafifications, is stated as local bijectivity — Mathlib's `Presheaf.IsLocallyInjective`
together with `Presheaf.IsLocallySurjective` — of the image of `toDegreewiseUnions` under the
functor `F` of the source, `associatedPresheafFunctor`.  This keeps the index universe `w` of
the semi-representable objects free: sheafification of a `Type (max w v)`-valued presheaf is
unavailable for general `w`, whereas local injectivity and surjectivity are intrinsic
conditions on the map of presheaves.

Since the augmentation of a hypercovering of the final presheaf is the unique map to a terminal
presheaf, no augmentation has to be transported: the two augmentations are related by the only
triangle there is, which is what lets conditions (1) and (2) be obtained by cancellation.

Conditions (1), (2) and (3) all rest on one statement: a morphism between limits, over a finite
index category, of a transformation that is locally bijective in every component is locally
surjective.  It is proved once, as `homLocallySurjective_of_isLimit`, for morphisms tested on an
arbitrary functor from the site, so that it applies both in the presheaf category — for
condition (2), whose fibre product is taken over the augmentation target and so is not
semi-representable — and in the category of semi-representable objects itself, for condition
(3), where it avoids having to know that `F` preserves the limits defining the matching objects.

## References

* [Stacks Project, Tag 0DB1](https://stacks.math.columbia.edu/tag/0DB1)
-/

@[expose] public section

universe t s w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

section HomLocal

variable {A : Type t} [Category.{s} A]

private lemma mem_homLifts (T : C ⥤ A) {X Y : A} (p : X ⟶ Y) {U V : C}
    (s : T.obj U ⟶ Y) (g : V ⟶ U) :
    (homLifts T p s).arrows g ↔ ∃ r : T.obj V ⟶ X, r ≫ p = T.map g ≫ s :=
  Iff.rfl

/-- The sieve of morphisms `g : V ⟶ U` along which two maps out of `T.obj U` agree. -/
private def homEqualizerSieve (T : C ⥤ A) {X : A} {U : C} (a b : T.obj U ⟶ X) : Sieve U where
  arrows V g := T.map g ≫ a = T.map g ≫ b
  downward_closed := by
    intro V W g hg h
    simp only [T.map_comp, Category.assoc]
    rw [hg]

private lemma mem_homEqualizerSieve (T : C ⥤ A) {X : A} {U V : C} (a b : T.obj U ⟶ X)
    (g : V ⟶ U) :
    (homEqualizerSieve T a b).arrows g ↔ T.map g ≫ a = T.map g ≫ b :=
  Iff.rfl

/-- Local injectivity of a morphism of `A`, tested on the objects `T.obj U`. -/
private def HomLocallyInjective (J : GrothendieckTopology C) (T : C ⥤ A) {X Y : A}
    (p : X ⟶ Y) : Prop :=
  ∀ (U : C) (a b : T.obj U ⟶ X), a ≫ p = b ≫ p → homEqualizerSieve T a b ∈ J U

/-- A morphism between limits over a finite index category, compatible with a transformation
that is locally bijective in every component, is locally surjective. -/
private theorem homLocallySurjective_of_isLimit (J : GrothendieckTopology C) (T : C ⥤ A)
    {I : Type} [SmallCategory I] [FinCategory I] {D₁ D₂ : I ⥤ A} (α : D₁ ⟶ D₂)
    (hsurj : ∀ i, HomLocallySurjective J T (α.app i))
    (hinj : ∀ i, HomLocallyInjective J T (α.app i))
    {c₁ : Cone D₁} (h₁ : IsLimit c₁) {c₂ : Cone D₂} (h₂ : IsLimit c₂)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ i, φ ≫ c₂.π.app i = c₁.π.app i ≫ α.app i) :
    HomLocallySurjective J T φ := by
  classical
  intro U s
  refine J.transitive (J.iInf_covering
    (fun i : I ↦ homLifts T (α.app i) (s ≫ c₂.π.app i)) (fun i ↦ hsurj i U _)) _ ?_
  intro V g hg
  choose r hr using fun i : I ↦ (mem_homLifts T (α.app i) (s ≫ c₂.π.app i) g).1
    (iInf_le (fun i : I ↦ homLifts T (α.app i) (s ≫ c₂.π.app i)) i g hg)
  have key : ∀ e : (p : I × I) × (p.1 ⟶ p.2),
      homEqualizerSieve T (r e.1.1 ≫ D₁.map e.2) (r e.1.2) ∈ J V := by
    intro e
    refine hinj e.1.2 V _ _ ?_
    have h1 : (r e.1.1 ≫ D₁.map e.2) ≫ α.app e.1.2 =
        (r e.1.1 ≫ α.app e.1.1) ≫ D₂.map e.2 := by
      rw [Category.assoc, α.naturality e.2, Category.assoc]
    rw [h1, hr e.1.1, hr e.1.2, Category.assoc, Category.assoc, c₂.w e.2]
  refine J.superset_covering ?_ (J.iInf_covering _ key)
  intro W h hh
  have hcompat : ∀ {i j : I} (e : i ⟶ j),
      (T.map h ≫ r i) ≫ D₁.map e = T.map h ≫ r j := by
    intro i j e
    have := (mem_homEqualizerSieve T (r i ≫ D₁.map e) (r j) h).1
      (iInf_le (fun e : (p : I × I) × (p.1 ⟶ p.2) ↦
        homEqualizerSieve T (r e.1.1 ≫ D₁.map e.2) (r e.1.2)) ⟨(i, j), e⟩ h hh)
    simpa only [Category.assoc] using this
  refine (mem_homLifts T φ s _).2 ⟨h₁.lift
    { pt := T.obj W
      π := { app := fun i ↦ T.map h ≫ r i
             naturality := fun i j e ↦ by simpa using (hcompat e).symm } }, ?_⟩
  refine h₂.hom_ext fun i ↦ ?_
  rw [Category.assoc, hφ i, ← Category.assoc, h₁.fac _ i, Category.assoc, hr i,
    Category.assoc, T.map_comp, Category.assoc]

/-- A morphism of fibre products, compatible with two locally surjective maps on the sources and
a locally injective map on the targets, is locally surjective. -/
private theorem homLocallySurjective_of_pullback (J : GrothendieckTopology C) (T : C ⥤ A)
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : A} {f₁ : X₁ ⟶ Z₁} {g₁ : Y₁ ⟶ Z₁} {f₂ : X₂ ⟶ Z₂} {g₂ : Y₂ ⟶ Z₂}
    {a : X₁ ⟶ X₂} {b : Y₁ ⟶ Y₂} {c : Z₁ ⟶ Z₂}
    (wa : f₁ ≫ c = a ≫ f₂) (wb : g₁ ≫ c = b ≫ g₂)
    (ha : HomLocallySurjective J T a) (hb : HomLocallySurjective J T b)
    (hc : HomLocallyInjective J T c) [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (φ : pullback f₁ g₁ ⟶ pullback f₂ g₂)
    (hfst : φ ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ ≫ a)
    (hsnd : φ ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ ≫ b) :
    HomLocallySurjective J T φ := by
  intro U s
  refine J.transitive (J.intersection_covering (ha U (s ≫ pullback.fst f₂ g₂))
    (hb U (s ≫ pullback.snd f₂ g₂))) _ ?_
  rintro V g ⟨hga, hgb⟩
  obtain ⟨ra, hra⟩ := (mem_homLifts T a _ g).1 hga
  obtain ⟨rb, hrb⟩ := (mem_homLifts T b _ g).1 hgb
  have heq : (ra ≫ f₁) ≫ c = (rb ≫ g₁) ≫ c := by
    rw [Category.assoc, Category.assoc, wa, wb, reassoc_of% hra, reassoc_of% hrb]
    simp only [pullback.condition]
  refine J.superset_covering ?_ (hc V _ _ heq)
  intro W h hh
  have hh' := (mem_homEqualizerSieve T (ra ≫ f₁) (rb ≫ g₁) h).1 hh
  have hmap : ∀ {Z : A} (z : pullback f₂ g₂ ⟶ Z),
      (T.map (h ≫ g) ≫ s) ≫ z = T.map h ≫ T.map g ≫ s ≫ z := by
    intro Z z
    rw [T.map_comp]
    simp only [Category.assoc]
  refine (mem_homLifts T φ s _).2
    ⟨pullback.lift (T.map h ≫ ra) (T.map h ≫ rb) ?_, ?_⟩
  · simpa only [Category.assoc] using hh'
  · refine pullback.hom_ext ?_ ?_
    · rw [hmap, Category.assoc, hfst, pullback.lift_fst_assoc, Category.assoc, hra]
    · rw [hmap, Category.assoc, hsnd, pullback.lift_snd_assoc, Category.assoc, hrb]

end HomLocal

section Presheaves

variable (J : GrothendieckTopology C)

private lemma uliftYonedaEquiv_precomp {Q : Cᵒᵖ ⥤ Type (max w v)} {U V : C} (g : V ⟶ U)
    (s : uliftYoneda.{w}.obj U ⟶ Q) :
    uliftYonedaEquiv.{w} (uliftYoneda.{w}.map g ≫ s) = Q.map g.op (uliftYonedaEquiv.{w} s) :=
  (uliftYonedaEquiv_naturality.{w} (X := op U) (Y := op V) s g.op).symm

private lemma homLocallySurjective_uliftYoneda_iff {P Q : Cᵒᵖ ⥤ Type (max w v)} (f : P ⟶ Q) :
    HomLocallySurjective J uliftYoneda.{w} f ↔ Presheaf.IsLocallySurjective J f := by
  have key : ∀ (U : C) (s : uliftYoneda.{w}.obj U ⟶ Q),
      homLifts uliftYoneda.{w} f s = Presheaf.imageSieve f (uliftYonedaEquiv.{w} s) := by
    intro U s
    refine Sieve.ext fun V g ↦ ⟨?_, ?_⟩
    · rintro ⟨r, hr⟩
      refine ⟨uliftYonedaEquiv.{w} r, ?_⟩
      change f.app (op V) (uliftYonedaEquiv.{w} r) = Q.map g.op (uliftYonedaEquiv.{w} s)
      rw [← uliftYonedaEquiv_comp, hr, uliftYonedaEquiv_precomp]
    · rintro ⟨x, hx⟩
      replace hx : f.app (op V) x = Q.map g.op (uliftYonedaEquiv.{w} s) := hx
      refine ⟨uliftYonedaEquiv.{w}.symm x, ?_⟩
      rw [uliftYonedaEquiv_symm_comp, hx, ← uliftYonedaEquiv_precomp, Equiv.symm_apply_apply]
  refine ⟨fun h ↦ ⟨fun {U} x ↦ ?_⟩, fun h U s ↦ ?_⟩
  · have := h U (uliftYonedaEquiv.{w}.symm x)
    rwa [key, Equiv.apply_symm_apply] at this
  · rw [key]
    exact h.imageSieve_mem _

private lemma homLocallyInjective_uliftYoneda_iff {P Q : Cᵒᵖ ⥤ Type (max w v)} (f : P ⟶ Q) :
    HomLocallyInjective J uliftYoneda.{w} f ↔ Presheaf.IsLocallyInjective J f := by
  have key : ∀ (U : C) (a b : uliftYoneda.{w}.obj U ⟶ P),
      homEqualizerSieve uliftYoneda.{w} a b =
        Presheaf.equalizerSieve (F := P) (X := op U)
          (uliftYonedaEquiv.{w} a) (uliftYonedaEquiv.{w} b) := by
    intro U a b
    refine Sieve.ext fun V g ↦ ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
    · change P.map g.op (uliftYonedaEquiv.{w} a) = P.map g.op (uliftYonedaEquiv.{w} b)
      rw [← uliftYonedaEquiv_precomp, ← uliftYonedaEquiv_precomp]
      exact congrArg _ hg
    · replace hg : P.map g.op (uliftYonedaEquiv.{w} a) = P.map g.op (uliftYonedaEquiv.{w} b) := hg
      rw [← uliftYonedaEquiv_precomp, ← uliftYonedaEquiv_precomp] at hg
      exact uliftYonedaEquiv.{w}.injective hg
  refine ⟨fun h ↦ ⟨fun {Z} x y hxy ↦ ?_⟩, fun h U a b hab ↦ ?_⟩
  · replace hxy : f.app Z x = f.app Z y := hxy
    have := h Z.unop (uliftYonedaEquiv.{w}.symm x) (uliftYonedaEquiv.{w}.symm y)
      (by rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, hxy])
    rwa [key, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  · rw [key]
    refine h.equalizerSieve_mem (X := op U) (uliftYonedaEquiv.{w} a) (uliftYonedaEquiv.{w} b) ?_
    change f.app (op U) (uliftYonedaEquiv.{w} a) = f.app (op U) (uliftYonedaEquiv.{w} b)
    rw [← uliftYonedaEquiv_comp, ← uliftYonedaEquiv_comp, hab]

end Presheaves

section Sections

variable (J : GrothendieckTopology C)

private lemma homLocallySurjective_incl_iff {P Q : FormalCoproduct.{w} C} (p : P ⟶ Q) :
    HomLocallySurjective J (FormalCoproduct.incl C) p ↔
      Presheaf.IsLocallySurjective J ((associatedPresheafFunctor.{v}).map p) := by
  have key : ∀ (U : C) (s : (FormalCoproduct.incl C).obj U ⟶ Q),
      homLifts (FormalCoproduct.incl C) p s =
        Presheaf.imageSieve ((associatedPresheafFunctor.{v}).map p)
          ((sectionEquiv Q U).symm s) := by
    intro U s
    refine Sieve.ext fun V g ↦ ⟨?_, ?_⟩
    · rintro ⟨r, hr⟩
      refine ⟨(sectionEquiv P V).symm r, ?_⟩
      change ((associatedPresheafFunctor.{v}).map p).app (op V) ((sectionEquiv P V).symm r) =
        ((associatedPresheafFunctor.{v}).obj Q).map g.op ((sectionEquiv Q U).symm s)
      rw [← sectionEquiv_symm_postcomp, hr, sectionEquiv_symm_precomp]
    · rintro ⟨x, hx⟩
      replace hx : ((associatedPresheafFunctor.{v}).map p).app (op V) x =
        ((associatedPresheafFunctor.{v}).obj Q).map g.op ((sectionEquiv Q U).symm s) := hx
      refine ⟨sectionEquiv P V x, ?_⟩
      apply (sectionEquiv Q V).symm.injective
      rw [sectionEquiv_symm_postcomp, sectionEquiv_symm_precomp, Equiv.symm_apply_apply, hx]
  refine ⟨fun h ↦ ⟨fun {U} x ↦ ?_⟩, fun h U s ↦ ?_⟩
  · have := h U (sectionEquiv Q U x)
    rwa [key, Equiv.symm_apply_apply] at this
  · rw [key]
    exact h.imageSieve_mem _

private lemma homLocallyInjective_incl_iff {P Q : FormalCoproduct.{w} C} (p : P ⟶ Q) :
    HomLocallyInjective J (FormalCoproduct.incl C) p ↔
      Presheaf.IsLocallyInjective J ((associatedPresheafFunctor.{v}).map p) := by
  have key : ∀ (U : C) (a b : (FormalCoproduct.incl C).obj U ⟶ P),
      homEqualizerSieve (FormalCoproduct.incl C) a b =
        Presheaf.equalizerSieve (F := (associatedPresheafFunctor.{v}).obj P) (X := op U)
          ((sectionEquiv P U).symm a) ((sectionEquiv P U).symm b) := by
    intro U a b
    refine Sieve.ext fun V g ↦ ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
    · change ((associatedPresheafFunctor.{v}).obj P).map g.op ((sectionEquiv P U).symm a) =
        ((associatedPresheafFunctor.{v}).obj P).map g.op ((sectionEquiv P U).symm b)
      rw [← sectionEquiv_symm_precomp, ← sectionEquiv_symm_precomp]
      exact congrArg _ hg
    · replace hg : ((associatedPresheafFunctor.{v}).obj P).map g.op
          ((sectionEquiv P U).symm a) =
        ((associatedPresheafFunctor.{v}).obj P).map g.op ((sectionEquiv P U).symm b) := hg
      rw [← sectionEquiv_symm_precomp, ← sectionEquiv_symm_precomp] at hg
      exact (sectionEquiv P V).symm.injective hg
  refine ⟨fun h ↦ ⟨fun {Z} x y hxy ↦ ?_⟩, fun h U a b hab ↦ ?_⟩
  · replace hxy : ((associatedPresheafFunctor.{v}).map p).app Z x =
      ((associatedPresheafFunctor.{v}).map p).app Z y := hxy
    have := h Z.unop (sectionEquiv P Z.unop x) (sectionEquiv P Z.unop y)
      (by apply (sectionEquiv Q Z.unop).symm.injective
          rw [sectionEquiv_symm_postcomp, sectionEquiv_symm_postcomp,
            Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          exact hxy)
    rwa [key, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · rw [key]
    refine h.equalizerSieve_mem (X := op U) ((sectionEquiv P U).symm a)
      ((sectionEquiv P U).symm b) ?_
    change ((associatedPresheafFunctor.{v}).map p).app (op U) ((sectionEquiv P U).symm a) =
      ((associatedPresheafFunctor.{v}).map p).app (op U) ((sectionEquiv P U).symm b)
    rw [← sectionEquiv_symm_postcomp, ← sectionEquiv_symm_postcomp, hab]

end Sections

section Construction

/-- Take disjoint unions in each degree of a simplicial semi-representable object.  Only the
coproducts of the objects actually occurring are required to exist. -/
@[stacks 0DB1 "the simplicial object of degreewise disjoint unions"]
noncomputable def degreewiseUnions (K : SimplicialObject (FormalCoproduct.{w} C))
    (hsum : ∀ n, HasCoproduct (K.obj n).obj) : SimplicialObject (FormalCoproduct.{w} C) :=
  ((SimplicialObject.whiskering _ _).obj (takeUnions (C := C))).obj
    (ObjectProperty.lift (fun U : FormalCoproduct.{w} C ↦ HasCoproduct U.obj) K hsum)

/-- The canonical morphism from a summable semi-representable object to the one-element family
on its coproduct, given by the coproduct inclusions. -/
noncomputable def toTakeUnions : summableInclusion (C := C) ⟶ takeUnions.{w} (C := C) where
  app U :=
    letI := U.property
    { f := fun _ ↦ PUnit.unit
      φ := fun i ↦ Sigma.ι U.obj.obj i }
  naturality U V f := by
    have := U.property
    have := V.property
    refine FormalCoproduct.hom_ext (funext fun _ ↦ rfl) fun i ↦ ?_
    refine Eq.trans (Category.comp_id _) ?_
    exact (Sigma.ι_comp_map' f.hom.f f.hom.φ i).symm

/-- The canonical morphism from a simplicial semi-representable object to its degreewise
disjoint unions, given in each degree by the coproduct inclusions. -/
noncomputable def toDegreewiseUnions (K : SimplicialObject (FormalCoproduct.{w} C))
    (hsum : ∀ n, HasCoproduct (K.obj n).obj) : K ⟶ degreewiseUnions K hsum :=
  Functor.whiskerLeft
    (ObjectProperty.lift (fun U : FormalCoproduct.{w} C ↦ HasCoproduct U.obj) K hsum)
    toTakeUnions

end Construction

section Augmentation

/-- The final presheaf, lifted into the universe of the augmentations of a hypercovering, is
terminal. -/
noncomputable def isTerminalLiftedTerminal :
    IsTerminal (liftedPresheaf.{v, w} (C := C) (⊤_ (Cᵒᵖ ⥤ Type v))) :=
  IsTerminal.isTerminalObj
    ((Functor.whiskeringRight Cᵒᵖ (Type v) (Type (max v w v))).obj uliftFunctor.{max w v})
    (⊤_ (Cᵒᵖ ⥤ Type v)) terminalIsTerminal

/-- The unique augmentation of the degreewise disjoint unions towards the final presheaf. -/
noncomputable def unionsAugmentation (K : SimplicialObject (FormalCoproduct.{w} C))
    (hsum : ∀ n, HasCoproduct (K.obj n).obj) :
    associatedSimplicialPresheaf.{v} (degreewiseUnions K hsum) ⟶
      (SimplicialObject.const _).obj (liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v))) where
  app _ := isTerminalLiftedTerminal.from _
  naturality _ _ _ := isTerminalLiftedTerminal.hom_ext _ _

end Augmentation

section Conditions

/-- If a morphism of simplicial presheaves augmented towards a terminal presheaf is locally
bijective in degree zero, then local surjectivity of the degree-one matching map passes from its
source to its target. -/
private lemma locallySurjective_oneMatchingMap (J : GrothendieckTopology C)
    {P : Cᵒᵖ ⥤ Type (max w v)} (hP : IsTerminal P)
    {X Y : SimplicialObject (Cᵒᵖ ⥤ Type (max w v))} (ε : X ⟶ Y)
    (aX : X ⟶ (SimplicialObject.const _).obj P) (aY : Y ⟶ (SimplicialObject.const _).obj P)
    [Presheaf.IsLocallyInjective J (ε.app (op (SimplexCategory.mk 0)))]
    [Presheaf.IsLocallySurjective J (ε.app (op (SimplexCategory.mk 0)))]
    [Presheaf.IsLocallySurjective J (oneMatchingMap X P aX)] :
    Presheaf.IsLocallySurjective J (oneMatchingMap Y P aY) := by
  have htri : ε.app (op (SimplexCategory.mk 0)) ≫ aY.app (op (SimplexCategory.mk 0)) =
      aX.app (op (SimplexCategory.mk 0)) := hP.hom_ext _ _
  have hcond : (pullback.fst (aX.app (op (SimplexCategory.mk 0)))
        (aX.app (op (SimplexCategory.mk 0))) ≫ ε.app (op (SimplexCategory.mk 0))) ≫
      aY.app (op (SimplexCategory.mk 0)) =
    (pullback.snd (aX.app (op (SimplexCategory.mk 0)))
        (aX.app (op (SimplexCategory.mk 0))) ≫ ε.app (op (SimplexCategory.mk 0))) ≫
      aY.app (op (SimplexCategory.mk 0)) := by
    rw [Category.assoc, Category.assoc, htri, pullback.condition]
  set φ := pullback.lift (f := aY.app (op (SimplexCategory.mk 0)))
    (g := aY.app (op (SimplexCategory.mk 0)))
    (pullback.fst (aX.app (op (SimplexCategory.mk 0)))
      (aX.app (op (SimplexCategory.mk 0))) ≫ ε.app (op (SimplexCategory.mk 0)))
    (pullback.snd (aX.app (op (SimplexCategory.mk 0)))
      (aX.app (op (SimplexCategory.mk 0))) ≫ ε.app (op (SimplexCategory.mk 0))) hcond with hφ
  have hφs : Presheaf.IsLocallySurjective J φ := by
    rw [← homLocallySurjective_uliftYoneda_iff]
    exact homLocallySurjective_of_pullback J uliftYoneda.{w} (c := 𝟙 P)
      (by rw [Category.comp_id]; exact htri.symm)
      (by rw [Category.comp_id]; exact htri.symm)
      ((homLocallySurjective_uliftYoneda_iff _ _).2 inferInstance)
      ((homLocallySurjective_uliftYoneda_iff _ _).2 inferInstance)
      ((homLocallyInjective_uliftYoneda_iff _ _).2 inferInstance) φ
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hfac : ε.app (op (SimplexCategory.mk 1)) ≫ oneMatchingMap Y P aY =
      oneMatchingMap X P aX ≫ φ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hφ, pullback.lift_fst,
        ← Category.assoc (oneMatchingMap X _ _), oneMatchingMap_fst, oneMatchingMap_fst]
      exact (SimplicialObject.δ_naturality ε 0).symm
    · rw [Category.assoc, Category.assoc, hφ, pullback.lift_snd,
        ← Category.assoc (oneMatchingMap X _ _), oneMatchingMap_snd, oneMatchingMap_snd]
      exact (SimplicialObject.δ_naturality ε 1).symm
  have := hφs
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac

/-- If a morphism of simplicial semi-representable objects is locally bijective in every degree,
then the morphism it induces on matching objects is locally surjective. -/
private lemma locallySurjective_coskeletonMap (J : GrothendieckTopology C)
    {K L : SimplicialObject (FormalCoproduct.{w} C)} (ε : K ⟶ L)
    (hinj : ∀ n, Presheaf.IsLocallyInjective J ((associatedPresheafFunctor.{v}).map (ε.app n)))
    (hsurj : ∀ n, Presheaf.IsLocallySurjective J ((associatedPresheafFunctor.{v}).map (ε.app n)))
    (n : ℕ)
    [∀ F : SimplicialObject.Truncated (FormalCoproduct.{w} C) n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (r : SimplexCategoryᵒᵖ)
    [FinCategory (StructuredArrow r (SimplexCategory.Truncated.inclusion n).op)] :
    Presheaf.IsLocallySurjective J
      ((associatedPresheafFunctor.{v}).map (((SimplicialObject.cosk n).map ε).app r)) := by
  rw [← homLocallySurjective_incl_iff]
  exact homLocallySurjective_of_isLimit J (FormalCoproduct.incl C)
    (Functor.whiskerLeft (StructuredArrow.proj r (SimplexCategory.Truncated.inclusion n).op)
      ((SimplicialObject.truncation n).map ε))
    (fun _ ↦ (homLocallySurjective_incl_iff _ _).2 (hsurj _))
    (fun _ ↦ (homLocallyInjective_incl_iff _ _).2 (hinj _))
    (matchingIsLimit K n r) (matchingIsLimit L n r) _
    (coskeleton_map_comp_matchingCone_π ε n r)

end Conditions

section Hypercovering

variable [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)

/-- **Stacks Project, Tag 0DB1.** Let `K` be a hypercovering on a site with fibre products and
equalizers.  If the coproduct of the objects in each degree of `K` exists and the map from the
coproduct of their representable presheaves to the presheaf represented by that coproduct
becomes an isomorphism after sheafification, then the degreewise disjoint unions again form a
hypercovering. -/
@[stacks 0DB1 "the degreewise disjoint unions again form a hypercovering"]
noncomputable def hypercoveringDegreewiseUnions (K : HypercoveringOfTerminal.{w} J)
    (hsum : ∀ n, HasCoproduct (K.toSimplicialObject.obj n).obj)
    (hinj : ∀ n, Presheaf.IsLocallyInjective J.toGrothendieck
      ((associatedPresheafFunctor.{v}).map
        ((toDegreewiseUnions K.toSimplicialObject hsum).app n)))
    (hsurj : ∀ n, Presheaf.IsLocallySurjective J.toGrothendieck
      ((associatedPresheafFunctor.{v}).map
        ((toDegreewiseUnions K.toSimplicialObject hsum).app n))) :
    HypercoveringOfTerminal.{w} J where
  toSimplicialObject := degreewiseUnions K.toSimplicialObject hsum
  augmentation := unionsAugmentation K.toSimplicialObject hsum
  locallySurjective_zero := by
    have := K.locallySurjective_zero
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (f₁ := (associatedPresheafFunctor.{v}).map
        ((toDegreewiseUnions K.toSimplicialObject hsum).app (op (SimplexCategory.mk 0))))
      (f₃ := K.augmentation.app (op (SimplexCategory.mk 0)))
      (isTerminalLiftedTerminal.hom_ext _ _)
  locallySurjective_one := by
    have := K.locallySurjective_one
    have h0 : Presheaf.IsLocallyInjective J.toGrothendieck
        ((Functor.whiskerRight (toDegreewiseUnions K.toSimplicialObject hsum)
          (associatedPresheafFunctor.{v})).app (op (SimplexCategory.mk 0))) :=
      hinj (op (SimplexCategory.mk 0))
    have h1 : Presheaf.IsLocallySurjective J.toGrothendieck
        ((Functor.whiskerRight (toDegreewiseUnions K.toSimplicialObject hsum)
          (associatedPresheafFunctor.{v})).app (op (SimplexCategory.mk 0))) :=
      hsurj (op (SimplexCategory.mk 0))
    exact locallySurjective_oneMatchingMap J.toGrothendieck isTerminalLiftedTerminal
      (Functor.whiskerRight (toDegreewiseUnions K.toSimplicialObject hsum)
        (associatedPresheafFunctor.{v}))
      K.augmentation (unionsAugmentation K.toSimplicialObject hsum)
  locallySurjective_succ := by
    intro n hn
    let := hasPositiveCoskeleta.{w} (C := C) n hn
    let := Construction.finCategoryTruncatedStructuredArrow n (op (SimplexCategory.mk (n + 1)))
    have := K.locallySurjective_succ n hn
    have := locallySurjective_coskeletonMap J.toGrothendieck
      (toDegreewiseUnions K.toSimplicialObject hsum) hinj hsurj n
      (op (SimplexCategory.mk (n + 1)))
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
      (f₃ := higherMatchingMap.{v} K.toSimplicialObject n hn ≫
        (associatedPresheafFunctor.{v}).map
          (((positiveCoskeleton n hn).map
            (toDegreewiseUnions K.toSimplicialObject hsum)).app
              (op (SimplexCategory.mk (n + 1)))))
      (higherMatchingMap_naturality (toDegreewiseUnions K.toSimplicialObject hsum) n hn)

/-- The underlying simplicial object of `hypercoveringDegreewiseUnions J K hsum hinj hsurj` is
`degreewiseUnions K.toSimplicialObject hsum`. -/
@[simp]
lemma hypercoveringDegreewiseUnions_toSimplicialObject (K : HypercoveringOfTerminal.{w} J)
    (hsum : ∀ n, HasCoproduct (K.toSimplicialObject.obj n).obj)
    (hinj : ∀ n, Presheaf.IsLocallyInjective J.toGrothendieck
      ((associatedPresheafFunctor.{v}).map
        ((toDegreewiseUnions K.toSimplicialObject hsum).app n)))
    (hsurj : ∀ n, Presheaf.IsLocallySurjective J.toGrothendieck
      ((associatedPresheafFunctor.{v}).map
        ((toDegreewiseUnions K.toSimplicialObject hsum).app n))) :
    (hypercoveringDegreewiseUnions J K hsum hinj hsurj).toSimplicialObject =
      degreewiseUnions K.toSimplicialObject hsum :=
  rfl

end Hypercovering

end Stacks.CategoryTheory.Hypercovering

end
