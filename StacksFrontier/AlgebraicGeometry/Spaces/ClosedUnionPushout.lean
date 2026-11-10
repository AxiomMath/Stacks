module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedUnionIntersectionEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedUnionPushoutRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickeningCriteria

/-!
# The scheme-theoretic union of two closed subspaces is a pushout of algebraic spaces

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site and let `Y, Z ⊆ X`
be closed subspaces, with `Y ∪ Z` and `Y ∩ Z` the scheme-theoretic union and intersection of
Definition 0CYZ.  This file proves the third assertion of [Stacks Project, Tag 0CZ1]: the square

```
Y ∩ Z ⟶ Y
  ↓        ↓
  Z   ⟶ Y ∪ Z
```

is cocartesian in the category of algebraic spaces over `S`.

The target of the morphism being produced is required to be an algebraic space over `S`, as in
the source: the square is *not* a pushout square in the larger category of all fppf sheaves on
the big fppf site, so the universal property genuinely has to be tested against algebraic spaces
only.  That is why the proof below goes through [Stacks Project, Tag 0EDP], a statement about
algebraic-space targets, rather than through any colimit of sheaves.

## Main results

* `AlgebraicGeometry.Space.existsUnique_desc_of_eq_schemeTheoreticUnion`: the universal property
  for a **representable** ambient space.
* `AlgebraicGeometry.Space.existsUnique_desc_preimage` and
  `AlgebraicGeometry.Space.desc_preimage_comp_eq`: the universal property pulled back along an
  étale morphism from a representable algebraic space, and the fact that the restriction of a
  descent along a further morphism is again a descent.
* `AlgebraicGeometry.Space.existsUnique_desc_schemeTheoreticUnion`: the universal property in
  general.
* `AlgebraicGeometry.Space.isPushout_schemeTheoreticUnion`: **the third assertion of Tag 0CZ1**,
  the square is a pushout square of algebraic spaces over `S`.

## Implementation notes

For a representable ambient space `h_V` the argument is the dictionary of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentableClosedSubspaceIdeal.lean` together with
`AlgebraicGeometry.Space.isPushout_yoneda_of_ker_eq_inf`: the two closed subspaces, their
intersection and their union are the ranges of four closed immersions of the site whose sheaves
of ideals are `I`, `J`, `I ⊔ J` and `I ⊓ J`, and the range of a monomorphism is isomorphic to its
source, so the square of subfunctors is isomorphic to a square of representable presheaves which
is a pushout square.

For a general `X` the argument is étale descent along a surjective étale chart
`φ : h_U ⟶ X`, in the form `AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`.  The
inverse image `φ⁻¹(Y ∪ Z)` is a closed subspace of `h_U`, representable by an object `P` of the
site, and the projection `h_P ⟶ Y ∪ Z` is a surjective étale chart; the representable case on
`U` produces a morphism `h_P ⟶ T`.  Its cocycle condition on the kernel pair of that chart is
the representable case *again*, on the object `Q` of the site representing `h_U ×_X h_U`: the
kernel pair maps to `Q`, the two composites `h_P ⟶ T` factor through the two descents over `Q`,
and both descents agree with the one over `U` because the restriction of a descent is a descent,
which is the uniqueness half on `Q`.  Étaleness enters only through
`AlgebraicGeometry.Space.preimage_schemeTheoreticUnion`, the compatibility of the
scheme-theoretic union with étale localization.

No separatedness hypothesis on the target appears anywhere, matching the source, which asks for
nothing beyond `T` being an algebraic space over `S`.

The three lemmas about `CategoryTheory.Subfunctor` opening this file are stated in the generality
of the Mathlib file they belong to.  Each of them had been proved before as a `private` lemma
specialised to the big fppf site — the composition of two inclusions in
`StacksFrontier/AlgebraicGeometry/Spaces/RationalFunctions.lean`, the criterion for landing in an
inverse image in `StacksFrontier/AlgebraicGeometry/Spaces/FibreSquareOverIsoSubspace.lean` — and
is needed here in a form those private copies cannot supply.

## References

* [Stacks Project, Tag 0CZ1](https://stacks.math.columbia.edu/tag/0CZ1)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F F' : C ⥤ Type w}

/-- The inclusion of subfunctors is functorial in the containment. -/
@[reassoc]
theorem homOfLe_comp {G₁ G₂ G₃ : Subfunctor F} (h : G₁ ≤ G₂) (h' : G₂ ≤ G₃) :
    homOfLe h ≫ homOfLe h' = homOfLe (h.trans h') := rfl

/-- Taking the inverse image of subfunctors along a fixed morphism is monotone. -/
theorem preimage_le_preimage {G G' : Subfunctor F} (h : G ≤ G') (p : F' ⟶ F) :
    G.preimage p ≤ G'.preimage p := fun _ _ hx => h _ hx

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The universal property for a representable ambient space -/

/-- **The universal property of the scheme-theoretic union of two closed subspaces of a
representable algebraic space.**

A closed subspace `Wv` of `h_V` which equals the scheme-theoretic union of `Y` and `Z` receives a
unique morphism to an algebraic space `G` from a pair of morphisms out of `Y` and out of `Z` which
agree on the scheme-theoretic intersection.

The four closed subspaces involved are the ranges of four closed immersions of the site whose
sheaves of ideals are `I`, `J`, `I ⊔ J` and `I ⊓ J`, by
`AlgebraicGeometry.Space.exists_closedImmersion_range`,
`AlgebraicGeometry.Space.exists_closedImmersion_ker_eq`,
`AlgebraicGeometry.Space.range_yoneda_map_inf_eq` and
`AlgebraicGeometry.Space.schemeTheoreticUnion_eq_range_yoneda_map`; the range of a monomorphism
is isomorphic to its source, so the statement is
`AlgebraicGeometry.Space.isPushout_yoneda_of_ker_eq_inf` read through those four
isomorphisms. -/
theorem existsUnique_desc_of_eq_schemeTheoreticUnion (V : BigFppfOver B S hS)
    (Y Z Wv : ClosedSubspaces B S hS (yoneda.obj V))
    (hW : (schemeTheoreticUnion B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
      Y Z).1 = Wv.1)
    (hYv : Y.1 ≤ Wv.1) (hZv : Z.1 ≤ Wv.1)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (f : Y.1.toFunctor ⟶ G) (g : Z.1.toFunctor ⟶ G)
    (hfg : Subfunctor.homOfLe (inf_le_left : Y.1 ⊓ Z.1 ≤ Y.1) ≫ f =
      Subfunctor.homOfLe (inf_le_right : Y.1 ⊓ Z.1 ≤ Z.1) ≫ g) :
    ∃! h : Wv.1.toFunctor ⟶ G,
      Subfunctor.homOfLe hYv ≫ h = f ∧ Subfunctor.homOfLe hZv ≫ h = g := by
  obtain ⟨Ys, hYs⟩ := Y
  obtain ⟨Zs, hZs⟩ := Z
  obtain ⟨Ws, hWs⟩ := Wv
  obtain ⟨R₁, j₁, hj₁, rfl⟩ := exists_closedImmersion_range B S hS Ys hYs
  obtain ⟨R₂, j₂, hj₂, rfl⟩ := exists_closedImmersion_range B S hS Zs hZs
  obtain ⟨R₃, j₃, hj₃, hk₃⟩ := exists_closedImmersion_ker_eq B S hS V
    (((BigFppfOver.toScheme B S hS).map j₁).ker ⊔ ((BigFppfOver.toScheme B S hS).map j₂).ker)
  obtain ⟨R₄, j₄, hj₄, hk₄⟩ := exists_closedImmersion_ker_eq B S hS V
    (((BigFppfOver.toScheme B S hS).map j₁).ker ⊓ ((BigFppfOver.toScheme B S hS).map j₂).ker)
  obtain ⟨a₁, ha₁⟩ := exists_comp_eq_of_ker_le B S hS j₁ j₃ hj₁ (by rw [hk₃]; exact le_sup_left)
  obtain ⟨a₂, ha₂⟩ := exists_comp_eq_of_ker_le B S hS j₂ j₃ hj₂ (by rw [hk₃]; exact le_sup_right)
  obtain ⟨b₁, hb₁⟩ := exists_comp_eq_of_ker_le B S hS j₄ j₁ hj₄ (by rw [hk₄]; exact inf_le_left)
  obtain ⟨b₂, hb₂⟩ := exists_comp_eq_of_ker_le B S hS j₄ j₂ hj₄ (by rw [hk₄]; exact inf_le_right)
  have := hj₁
  have := hj₂
  have := hj₃
  have := hj₄
  have : Mono (yoneda.map j₁) := mono_yoneda_map_of_mono_toScheme_map B S hS j₁ inferInstance
  have : Mono (yoneda.map j₂) := mono_yoneda_map_of_mono_toScheme_map B S hS j₂ inferInstance
  have : Mono (yoneda.map j₃) := mono_yoneda_map_of_mono_toScheme_map B S hS j₃ inferInstance
  have : Mono (yoneda.map j₄) := mono_yoneda_map_of_mono_toScheme_map B S hS j₄ inferInstance
  have hinter : Subfunctor.range (yoneda.map j₁) ⊓ Subfunctor.range (yoneda.map j₂) =
      Subfunctor.range (yoneda.map j₃) :=
    range_yoneda_map_inf_eq B S hS j₁ j₂ j₃ hj₁ hj₂ hj₃ hk₃
  have hunion : Ws = Subfunctor.range (yoneda.map j₄) :=
    hW.symm.trans (schemeTheoreticUnion_eq_range_yoneda_map B S hS j₁ j₂ j₄ hj₁ hj₂ hj₄ hk₄)
  have : IsIso (Subfunctor.lift (yoneda.map j₃) hinter.ge) :=
    Subfunctor.isIso_lift hinter.ge hinter.le
  have : IsIso (Subfunctor.lift (yoneda.map j₄) hunion.ge) :=
    Subfunctor.isIso_lift hunion.ge hunion.le
  -- the four comparison identities between the site morphisms and the subfunctor inclusions
  have ha₁e : yoneda.map a₁ ≫ Subfunctor.toRange (yoneda.map j₁) =
      Subfunctor.lift (yoneda.map j₃) hinter.ge ≫ Subfunctor.homOfLe
        (inf_le_left : Subfunctor.range (yoneda.map j₁) ⊓ Subfunctor.range (yoneda.map j₂) ≤
          Subfunctor.range (yoneda.map j₁)) :=
    (cancel_mono (Subfunctor.range (yoneda.map j₁)).ι).1 (by
      rw [Category.assoc, Category.assoc, Subfunctor.toRange_ι, Subfunctor.homOfLe_ι,
        Subfunctor.lift_ι, ← Functor.map_comp, ha₁])
  have ha₂e : yoneda.map a₂ ≫ Subfunctor.toRange (yoneda.map j₂) =
      Subfunctor.lift (yoneda.map j₃) hinter.ge ≫ Subfunctor.homOfLe
        (inf_le_right : Subfunctor.range (yoneda.map j₁) ⊓ Subfunctor.range (yoneda.map j₂) ≤
          Subfunctor.range (yoneda.map j₂)) :=
    (cancel_mono (Subfunctor.range (yoneda.map j₂)).ι).1 (by
      rw [Category.assoc, Category.assoc, Subfunctor.toRange_ι, Subfunctor.homOfLe_ι,
        Subfunctor.lift_ι, ← Functor.map_comp, ha₂])
  have hb₁e : yoneda.map b₁ ≫ Subfunctor.lift (yoneda.map j₄) hunion.ge =
      Subfunctor.toRange (yoneda.map j₁) ≫ Subfunctor.homOfLe hYv :=
    (cancel_mono Ws.ι).1 (by
      rw [Category.assoc, Category.assoc, Subfunctor.lift_ι, Subfunctor.homOfLe_ι,
        Subfunctor.toRange_ι, ← Functor.map_comp, hb₁])
  have hb₂e : yoneda.map b₂ ≫ Subfunctor.lift (yoneda.map j₄) hunion.ge =
      Subfunctor.toRange (yoneda.map j₂) ≫ Subfunctor.homOfLe hZv :=
    (cancel_mono Ws.ι).1 (by
      rw [Category.assoc, Category.assoc, Subfunctor.lift_ι, Subfunctor.homOfLe_ι,
        Subfunctor.toRange_ι, ← Functor.map_comp, hb₂])
  -- the pushout square of representable algebraic spaces
  have hpush := isPushout_yoneda_of_ker_eq_inf B S hS j₁ j₂ j₃ j₄ hj₁ hj₂ hj₃ hj₄
    a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hk₃ hk₄
  have hcond : (ObjectProperty.homMk (yoneda.map a₁) :
        yonedaSpace B S hS R₃ ⟶ yonedaSpace B S hS R₁) ≫
      (ObjectProperty.homMk (Subfunctor.toRange (yoneda.map j₁) ≫ f) :
        yonedaSpace B S hS R₁ ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) =
      (ObjectProperty.homMk (yoneda.map a₂) :
        yonedaSpace B S hS R₃ ⟶ yonedaSpace B S hS R₂) ≫
      (ObjectProperty.homMk (Subfunctor.toRange (yoneda.map j₂) ≫ g) :
        yonedaSpace B S hS R₂ ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) := by
    apply ObjectProperty.hom_ext
    change yoneda.map a₁ ≫ Subfunctor.toRange (yoneda.map j₁) ≫ f =
      yoneda.map a₂ ≫ Subfunctor.toRange (yoneda.map j₂) ≫ g
    rw [← Category.assoc, ha₁e, ← Category.assoc, ha₂e, Category.assoc, Category.assoc, hfg]
  refine ⟨inv (Subfunctor.lift (yoneda.map j₄) hunion.ge) ≫ (hpush.desc _ _ hcond).hom,
    ⟨?_, ?_⟩, ?_⟩
  · refine (cancel_epi (Subfunctor.toRange (yoneda.map j₁))).1 ?_
    rw [← Category.assoc, ← hb₁e, Category.assoc, IsIso.hom_inv_id_assoc]
    exact congrArg (fun m => m.hom) (hpush.inl_desc _ _ hcond)
  · refine (cancel_epi (Subfunctor.toRange (yoneda.map j₂))).1 ?_
    rw [← Category.assoc, ← hb₂e, Category.assoc, IsIso.hom_inv_id_assoc]
    exact congrArg (fun m => m.hom) (hpush.inr_desc _ _ hcond)
  · rintro h ⟨h₁, h₂⟩
    have hdesc : (ObjectProperty.homMk (Subfunctor.lift (yoneda.map j₄) hunion.ge ≫ h) :
        yonedaSpace B S hS R₄ ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) =
        hpush.desc _ _ hcond := by
      refine hpush.hom_ext ?_ ?_
      · apply ObjectProperty.hom_ext
        refine Eq.trans ?_ (congrArg (fun m => m.hom) (hpush.inl_desc _ _ hcond)).symm
        change yoneda.map b₁ ≫ Subfunctor.lift (yoneda.map j₄) hunion.ge ≫ h =
          Subfunctor.toRange (yoneda.map j₁) ≫ f
        rw [← Category.assoc, hb₁e, Category.assoc, h₁]
      · apply ObjectProperty.hom_ext
        refine Eq.trans ?_ (congrArg (fun m => m.hom) (hpush.inr_desc _ _ hcond)).symm
        change yoneda.map b₂ ≫ Subfunctor.lift (yoneda.map j₄) hunion.ge ≫ h =
          Subfunctor.toRange (yoneda.map j₂) ≫ g
        rw [← Category.assoc, hb₂e, Category.assoc, h₂]
    rw [show (hpush.desc _ _ hcond).hom = Subfunctor.lift (yoneda.map j₄) hunion.ge ≫ h from
      (congrArg (fun m => m.hom) hdesc).symm, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

/-! ### The general case -/

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {A₀ B₀ C₀ : C ⥤ Type w}

/-- A morphism lands in the inverse image of a subfunctor exactly when its composite with the
morphism one pulls back along lands in the subfunctor. -/
theorem range_le_preimage_iff (p : A₀ ⟶ B₀) (q : B₀ ⟶ C₀) (G : Subfunctor C₀) :
    Subfunctor.range p ≤ G.preimage q ↔ Subfunctor.range (p ≫ q) ≤ G := by
  rw [← Subfunctor.image_le_iff, Subfunctor.range_comp]

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section General

variable (X : AlgebraicSpaces B S hS) (Y Z W : ClosedSubspaces B S hS X.1)

/-- **The inverse image of a closed subspace along a morphism from a representable algebraic
space is a closed subspace**, by Stacks 083Q. -/
theorem isClosedSubspace_preimage_yoneda {A : BigFppfOver B S hS} (m : yoneda.obj A ⟶ X.1)
    (W : ClosedSubspaces B S hS X.1) : IsClosedSubspace B S hS (W.1.preimage m) :=
  isClosedSubspace_preimage B S hS m W.1 X.2 (isAlgebraicSpace_yoneda B S hS A) W.2

/-- **The inverse image of a closed subspace along a morphism of the site over `X` lands in the
inverse image over the target.** -/
theorem range_preimage_ι_comp_le (W : Subfunctor X.1) {A A' : BigFppfOver B S hS}
    (m : yoneda.obj A ⟶ X.1) (n : A' ⟶ A) (m' : yoneda.obj A' ⟶ X.1)
    (hnm : yoneda.map n ≫ m = m') :
    Subfunctor.range ((W.preimage m').ι ≫ yoneda.map n) ≤ W.preimage m := by
  rw [Subfunctor.range_le_preimage_iff, Category.assoc, hnm,
    show (W.preimage m').ι ≫ m' = W.fromPreimage m' ≫ W.ι from
      (Subfunctor.fromPreimage_ι W m').symm]
  exact (Subfunctor.range_comp_le _ _).trans (le_of_eq (Subfunctor.range_ι W))

variable {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (f : Y.1.toFunctor ⟶ G) (g : Z.1.toFunctor ⟶ G)
    (hW : (schemeTheoreticUnion B S hS X.1 X.2 Y Z).1 = W.1)
    (hYW : Y.1 ≤ W.1) (hZW : Z.1 ≤ W.1)

include hG hW in
/-- **The universal property of the scheme-theoretic union, pulled back along an étale morphism
from a representable algebraic space.**

The inverse images of `Y`, of `Z` and of `Y ∪ Z` are closed subspaces of `h_A`, and the inverse
image of the union is the union of the inverse images by
`AlgebraicGeometry.Space.preimage_schemeTheoreticUnion`, so this is the representable case
`AlgebraicGeometry.Space.existsUnique_desc_of_eq_schemeTheoreticUnion` applied on `A`. -/
theorem existsUnique_desc_preimage
    (hfg : Subfunctor.homOfLe (inf_le_left : Y.1 ⊓ Z.1 ≤ Y.1) ≫ f =
      Subfunctor.homOfLe (inf_le_right : Y.1 ⊓ Z.1 ≤ Z.1) ≫ g)
    {A : BigFppfOver B S hS} (m : yoneda.obj A ⟶ X.1) (hm : IsEtale B S hS m) :
    ∃! h : (W.1.preimage m).toFunctor ⟶ G,
      Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hYW m) ≫ h =
          Subfunctor.fromPreimage Y.1 m ≫ f ∧
        Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hZW m) ≫ h =
          Subfunctor.fromPreimage Z.1 m ≫ g := by
  refine existsUnique_desc_of_eq_schemeTheoreticUnion B S hS A
    ⟨Y.1.preimage m, isClosedSubspace_preimage_yoneda B S hS X m Y⟩
    ⟨Z.1.preimage m, isClosedSubspace_preimage_yoneda B S hS X m Z⟩
    ⟨W.1.preimage m, isClosedSubspace_preimage_yoneda B S hS X m W⟩
    ((preimage_schemeTheoreticUnion B S hS
        (ObjectProperty.homMk m : yonedaSpace B S hS A ⟶ X) hm Y Z).symm.trans
      (congrArg (fun T : Subfunctor X.1 => T.preimage m) hW))
    (Subfunctor.preimage_le_preimage hYW m)
    (Subfunctor.preimage_le_preimage hZW m) hG _ _ ?_
  have hρ : Subfunctor.range ((Y.1.preimage m ⊓ Z.1.preimage m).ι ≫ m) ≤ Y.1 ⊓ Z.1 := by
    refine le_inf ?_ ?_
    · rw [← Subfunctor.range_le_preimage_iff, Subfunctor.range_ι]
      exact inf_le_left
    · rw [← Subfunctor.range_le_preimage_iff, Subfunctor.range_ι]
      exact inf_le_right
  have hV : ∀ (V : Subfunctor X.1) (h₁ : Y.1.preimage m ⊓ Z.1.preimage m ≤ V.preimage m)
      (h₂ : Y.1 ⊓ Z.1 ≤ V), Subfunctor.homOfLe h₁ ≫ Subfunctor.fromPreimage V m =
      Subfunctor.lift ((Y.1.preimage m ⊓ Z.1.preimage m).ι ≫ m) hρ ≫ Subfunctor.homOfLe h₂ :=
    fun V h₁ h₂ => (cancel_mono V.ι).1 (by
      rw [Category.assoc, Category.assoc, Subfunctor.fromPreimage_ι,
        Subfunctor.homOfLe_ι_assoc, Subfunctor.homOfLe_ι, Subfunctor.lift_ι])
  rw [← Category.assoc, hV Y.1 inf_le_left inf_le_left, ← Category.assoc,
    hV Z.1 inf_le_right inf_le_right, Category.assoc, Category.assoc, hfg]

include hG hW in
/-- **The restriction of a descent is a descent.**  If `h` descends the pair `(f, g)` over an
étale `m : h_A ⟶ X` and `h'` descends it over `m' = n ≫ m`, then `h'` is the restriction of `h`
along any morphism `θ` of the inverse images over `n`.

This is the uniqueness half of
`AlgebraicGeometry.Space.existsUnique_desc_preimage` over `A'`: the composite `θ ≫ h` restricts
to `f` and to `g` on the inverse images of `Y` and `Z` over `A'`, because `θ` carries those
inverse images to the ones over `A`. -/
theorem desc_preimage_comp_eq
    (hfg : Subfunctor.homOfLe (inf_le_left : Y.1 ⊓ Z.1 ≤ Y.1) ≫ f =
      Subfunctor.homOfLe (inf_le_right : Y.1 ⊓ Z.1 ≤ Z.1) ≫ g)
    {A A' : BigFppfOver B S hS} (m : yoneda.obj A ⟶ X.1)
    (n : A' ⟶ A) (m' : yoneda.obj A' ⟶ X.1) (hm' : IsEtale B S hS m')
    (hnm : yoneda.map n ≫ m = m')
    (h : (W.1.preimage m).toFunctor ⟶ G)
    (hh₁ : Subfunctor.homOfLe
        (Subfunctor.preimage_le_preimage hYW m) ≫ h =
      Subfunctor.fromPreimage Y.1 m ≫ f)
    (hh₂ : Subfunctor.homOfLe
        (Subfunctor.preimage_le_preimage hZW m) ≫ h =
      Subfunctor.fromPreimage Z.1 m ≫ g)
    (h' : (W.1.preimage m').toFunctor ⟶ G)
    (hh'₁ : Subfunctor.homOfLe
        (Subfunctor.preimage_le_preimage hYW m') ≫ h' =
      Subfunctor.fromPreimage Y.1 m' ≫ f)
    (hh'₂ : Subfunctor.homOfLe
        (Subfunctor.preimage_le_preimage hZW m') ≫ h' =
      Subfunctor.fromPreimage Z.1 m' ≫ g)
    (θ : (W.1.preimage m').toFunctor ⟶ (W.1.preimage m).toFunctor)
    (hθ : θ ≫ (W.1.preimage m).ι = (W.1.preimage m').ι ≫ yoneda.map n) :
    θ ≫ h = h' := by
  obtain ⟨w, -, huniq⟩ :=
    existsUnique_desc_preimage B S hS X Y Z W hG f g hW hYW hZW hfg m' hm'
  have key : ∀ (V : Subfunctor X.1) (hVW : V ≤ W.1) (f' : V.toFunctor ⟶ G),
      Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hVW m) ≫ h =
        Subfunctor.fromPreimage V m ≫ f' →
      Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hVW m') ≫ θ ≫ h =
        Subfunctor.fromPreimage V m' ≫ f' := by
    intro V hVW f' hh
    have hρ : Subfunctor.range ((V.preimage m').ι ≫ yoneda.map n) ≤ V.preimage m :=
      range_preimage_ι_comp_le B S hS X V m n m' hnm
    have hstep : Subfunctor.homOfLe
          (Subfunctor.preimage_le_preimage hVW m') ≫ θ =
        Subfunctor.lift ((V.preimage m').ι ≫ yoneda.map n) hρ ≫ Subfunctor.homOfLe
          (Subfunctor.preimage_le_preimage hVW m) :=
      (cancel_mono (W.1.preimage m).ι).1 (by
        rw [Category.assoc, hθ, Category.assoc, Subfunctor.homOfLe_ι_assoc,
          Subfunctor.homOfLe_ι, Subfunctor.lift_ι])
    have hfrom : Subfunctor.lift ((V.preimage m').ι ≫ yoneda.map n) hρ ≫
        Subfunctor.fromPreimage V m = Subfunctor.fromPreimage V m' :=
      (cancel_mono V.ι).1 (by
        rw [Category.assoc, Subfunctor.fromPreimage_ι, Subfunctor.fromPreimage_ι,
          Subfunctor.lift_ι_assoc, Category.assoc, hnm])
    rw [← Category.assoc, hstep, Category.assoc, hh, ← Category.assoc, hfrom]
  exact (huniq (θ ≫ h) ⟨key Y.1 hYW f hh₁, key Z.1 hZW g hh₂⟩).trans
    (huniq h' ⟨hh'₁, hh'₂⟩).symm


include hG hW in
/-- **The universal property of the scheme-theoretic union of two closed subspaces of an
algebraic space over `S`.**

A pair of morphisms out of `Y` and out of `Z` to an algebraic space `G` which agree on the
scheme-theoretic intersection extends uniquely to the scheme-theoretic union.

The proof is étale descent along a surjective étale chart `φ : h_U ⟶ X`.  The base change
`α` of `φ` along the inclusion of the union is a surjective étale chart of the union whose
source is representable, `h_P` representing the inverse image `φ⁻¹(Y ∪ Z)`, so
`AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas` reduces the problem to a
morphism `h_P ⟶ G` satisfying the cocycle condition on the kernel pair of `α`.  That morphism
is the representable case over `U`, `AlgebraicGeometry.Space.existsUnique_desc_preimage`; the
kernel pair maps to the object of the site representing `h_U ×_X h_U`, and both composites with
it factor through the representable case over that object, because the restriction of a descent
is a descent, `AlgebraicGeometry.Space.desc_preimage_comp_eq`.  The two restriction identities
for the descended morphism are checked on the surjective étale charts of `Y` and of `Z`
obtained by base change, using
`AlgebraicGeometry.Space.eq_of_comp_eq_of_surjectiveEtale`. -/
theorem existsUnique_desc_schemeTheoreticUnion
    (hfg : Subfunctor.homOfLe (inf_le_left : Y.1 ⊓ Z.1 ≤ Y.1) ≫ f =
      Subfunctor.homOfLe (inf_le_right : Y.1 ⊓ Z.1 ≤ Z.1) ≫ g) :
    ∃! h : W.1.toFunctor ⟶ G,
      Subfunctor.homOfLe hYW ≫ h = f ∧ Subfunctor.homOfLe hZW ≫ h = g := by
  classical
  obtain ⟨U, φ, hsurj, hetale⟩ := X.2.exists_atlas
  have hφet : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hetale
  -- the self base change of the chart and its two projections
  have hQpb := hsurj.1.isPullback φ
  have hψet : IsEtale B S hS (yoneda.map (hsurj.1.snd φ) ≫ φ) :=
    isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@AlgebraicGeometry.Etale.{u}) (hsurj.1.snd φ)).2
        (hetale.2 φ (hsurj.1.fst φ) (hsurj.1.snd φ) hQpb))) hφet
  have hQw : yoneda.map (yoneda.preimage (hsurj.1.fst φ)) ≫ φ =
      yoneda.map (hsurj.1.snd φ) ≫ φ := by
    rw [Functor.map_preimage]; exact hQpb.w
  -- the chart of the union obtained by base change along its inclusion
  have hWpb := W.2.2.1.isPullback φ
  have hchart : ∀ V : ClosedSubspaces B S hS X.1,
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (V.2.2.1.fst φ) ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (V.2.2.1.fst φ) := fun V =>
    ⟨(MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback (V.2.2.1.isPullback φ).flip hsurj,
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback (V.2.2.1.isPullback φ).flip hetale⟩
  obtain ⟨hαsurj, hαetale⟩ := hchart W
  have hrangeq : Subfunctor.range (yoneda.map (W.2.2.1.snd φ)) = W.1.preimage φ :=
    range_yoneda_snd_eq_preimage B S hS φ W.2.2.1
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (W.2.2.1.snd φ)) :=
    W.2.2.2 φ (W.2.2.1.fst φ) (W.2.2.1.snd φ) hWpb
  have : Mono (yoneda.map (W.2.2.1.snd φ)) :=
    mono_yoneda_map_of_mono_toScheme_map B S hS _ inferInstance
  have : IsIso (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le) :=
    Subfunctor.isIso_lift hrangeq.le hrangeq.ge
  have hLq : inv (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le) ≫
      yoneda.map (W.2.2.1.snd φ) ≫ φ = (W.1.preimage φ).ι ≫ φ := by
    rw [← Category.assoc, (IsIso.inv_comp_eq _).2 (Subfunctor.lift_ι _ _).symm]
  -- the descents over the chart and over its self base change
  obtain ⟨hφdesc, ⟨hφ1, hφ2⟩, hφuniq⟩ :=
    existsUnique_desc_preimage B S hS X Y Z W hG f g hW hYW hZW hfg φ hφet
  obtain ⟨hψdesc, ⟨hψ1, hψ2⟩, -⟩ :=
    existsUnique_desc_preimage B S hS X Y Z W hG f g hW hYW hZW hfg _ hψet
  have hθs : Subfunctor.range ((W.1.preimage (yoneda.map (hsurj.1.snd φ) ≫ φ)).ι ≫
      yoneda.map (hsurj.1.snd φ)) ≤ W.1.preimage φ :=
    range_preimage_ι_comp_le B S hS X W.1 φ (hsurj.1.snd φ) _ rfl
  have hθt : Subfunctor.range ((W.1.preimage (yoneda.map (hsurj.1.snd φ) ≫ φ)).ι ≫
      yoneda.map (yoneda.preimage (hsurj.1.fst φ))) ≤ W.1.preimage φ :=
    range_preimage_ι_comp_le B S hS X W.1 φ (yoneda.preimage (hsurj.1.fst φ)) _ hQw
  have hθseq : Subfunctor.lift _ hθs ≫ hφdesc = hψdesc :=
    desc_preimage_comp_eq B S hS X Y Z W hG f g hW hYW hZW hfg φ (hsurj.1.snd φ) _ hψet rfl
      hφdesc hφ1 hφ2 hψdesc hψ1 hψ2 (Subfunctor.lift _ hθs) (Subfunctor.lift_ι _ hθs)
  have hθteq : Subfunctor.lift _ hθt ≫ hφdesc = hψdesc :=
    desc_preimage_comp_eq B S hS X Y Z W hG f g hW hYW hZW hfg φ
      (yoneda.preimage (hsurj.1.fst φ)) _ hψet hQw
      hφdesc hφ1 hφ2 hψdesc hψ1 hψ2 (Subfunctor.lift _ hθt) (Subfunctor.lift_ι _ hθt)
  -- the kernel pair of the chart of the union, and its map to the self base change
  have hαpb : IsPullback (yoneda.map (yoneda.preimage (hαsurj.1.fst (W.2.2.1.fst φ))))
      (yoneda.map (hαsurj.1.snd (W.2.2.1.fst φ))) (W.2.2.1.fst φ) (W.2.2.1.fst φ) := by
    rw [Functor.map_preimage]; exact hαsurj.1.isPullback (W.2.2.1.fst φ)
  have hmapt : yoneda.map (yoneda.preimage (hsurj.1.fst φ)) = hsurj.1.fst φ :=
    Functor.map_preimage _ _
  have hcw : (yoneda.map (yoneda.preimage (hαsurj.1.fst (W.2.2.1.fst φ))) ≫
        yoneda.map (W.2.2.1.snd φ)) ≫ φ =
      (yoneda.map (hαsurj.1.snd (W.2.2.1.fst φ)) ≫ yoneda.map (W.2.2.1.snd φ)) ≫ φ :=
    calc (yoneda.map (yoneda.preimage (hαsurj.1.fst (W.2.2.1.fst φ))) ≫
            yoneda.map (W.2.2.1.snd φ)) ≫ φ
        = yoneda.map (yoneda.preimage (hαsurj.1.fst (W.2.2.1.fst φ))) ≫
            W.2.2.1.fst φ ≫ W.1.ι := by rw [Category.assoc, ← hWpb.w]
      _ = (yoneda.map (yoneda.preimage (hαsurj.1.fst (W.2.2.1.fst φ))) ≫
            W.2.2.1.fst φ) ≫ W.1.ι := by rw [Category.assoc]
      _ = (yoneda.map (hαsurj.1.snd (W.2.2.1.fst φ)) ≫ W.2.2.1.fst φ) ≫ W.1.ι := by
            rw [hαpb.w]
      _ = yoneda.map (hαsurj.1.snd (W.2.2.1.fst φ)) ≫ yoneda.map (W.2.2.1.snd φ) ≫ φ := by
            rw [Category.assoc, hWpb.w]
      _ = (yoneda.map (hαsurj.1.snd (W.2.2.1.fst φ)) ≫ yoneda.map (W.2.2.1.snd φ)) ≫ φ := by
            rw [Category.assoc]
  have hc : Subfunctor.range (hQpb.lift _ _ hcw) ≤
      W.1.preimage (yoneda.map (hsurj.1.snd φ) ≫ φ) := by
    rw [Subfunctor.range_le_preimage_iff, ← Category.assoc, hQpb.lift_snd _ _ hcw,
      Category.assoc, ← hWpb.w]
    exact (Subfunctor.range_comp_le _ _).trans
      ((Subfunctor.range_comp_le _ _).trans (le_of_eq (Subfunctor.range_ι W.1)))
  -- the cocycle condition
  have hcocycle : yoneda.map (yoneda.preimage (hαsurj.1.fst (W.2.2.1.fst φ))) ≫
      (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le ≫ hφdesc) =
      yoneda.map (hαsurj.1.snd (W.2.2.1.fst φ)) ≫
        (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le ≫ hφdesc) := by
    have hleft : yoneda.map (yoneda.preimage (hαsurj.1.fst (W.2.2.1.fst φ))) ≫
        Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le =
        Subfunctor.lift (hQpb.lift _ _ hcw) hc ≫ Subfunctor.lift _ hθt :=
      (cancel_mono (W.1.preimage φ).ι).1 (by
        simp only [Category.assoc, Subfunctor.lift_ι, Subfunctor.lift_ι_assoc]
        rw [hmapt, hQpb.lift_fst _ _ hcw])
    have hright : yoneda.map (hαsurj.1.snd (W.2.2.1.fst φ)) ≫
        Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le =
        Subfunctor.lift (hQpb.lift _ _ hcw) hc ≫ Subfunctor.lift _ hθs :=
      (cancel_mono (W.1.preimage φ).ι).1 (by
        simp only [Category.assoc, Subfunctor.lift_ι, Subfunctor.lift_ι_assoc]
        rw [hQpb.lift_snd _ _ hcw])
    rw [← Category.assoc, hleft, ← Category.assoc, hright, Category.assoc, Category.assoc,
      hθseq, hθteq]
  -- the descended morphism
  obtain ⟨d, hd, hduniq⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS W.2.1.isSheaf
    (W.2.2.1.fst φ) hαpb hαsurj hαetale hG.isSheaf
    (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le ≫ hφdesc) hcocycle
  -- the two restriction identities, checked on charts of the two subspaces
  have hrestrict : ∀ (Y' : ClosedSubspaces B S hS X.1) (hY'W : Y'.1 ≤ W.1)
      (f' : Y'.1.toFunctor ⟶ G),
      Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hY'W φ) ≫ hφdesc =
        Subfunctor.fromPreimage Y'.1 φ ≫ f' →
      Subfunctor.homOfLe hY'W ≫ d = f' := by
    intro Y' hY'W f' hf'
    have hYpb := Y'.2.2.1.isPullback φ
    obtain ⟨hαYsurj, hαYetale⟩ := hchart Y'
    have hrangeqY : Subfunctor.range (yoneda.map (Y'.2.2.1.snd φ)) = Y'.1.preimage φ :=
      range_yoneda_snd_eq_preimage B S hS φ Y'.2.2.1
    have hmem : Y'.2.2.1.snd φ ∈
        (Subfunctor.range (yoneda.map (W.2.2.1.snd φ))).obj (op (Y'.2.2.1.pullback φ)) := by
      rw [hrangeq]
      refine Subfunctor.preimage_le_preimage hY'W φ _ ?_
      rw [← hrangeqY]
      exact ⟨𝟙 (Y'.2.2.1.pullback φ), Category.id_comp (Y'.2.2.1.snd φ)⟩
    obtain ⟨e, he⟩ := hmem
    have he' : e ≫ W.2.2.1.snd φ = Y'.2.2.1.snd φ := he
    have hLY : Subfunctor.lift (yoneda.map (Y'.2.2.1.snd φ)) hrangeqY.le ≫
        Subfunctor.fromPreimage Y'.1 φ = Y'.2.2.1.fst φ :=
      (cancel_mono Y'.1.ι).1 (by
        simp only [Category.assoc]
        rw [Subfunctor.fromPreimage_ι, Subfunctor.lift_ι_assoc, hYpb.w])
    have heL : yoneda.map e ≫ Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le =
        Subfunctor.lift (yoneda.map (Y'.2.2.1.snd φ)) hrangeqY.le ≫
          Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hY'W φ) :=
      (cancel_mono (W.1.preimage φ).ι).1 (by
        simp only [Category.assoc, Subfunctor.lift_ι, Subfunctor.homOfLe_ι]
        rw [← Functor.map_comp, he'])
    have hαYW : Y'.2.2.1.fst φ ≫ Subfunctor.homOfLe hY'W = yoneda.map e ≫ W.2.2.1.fst φ :=
      (cancel_mono W.1.ι).1 (by
        simp only [Category.assoc, Subfunctor.homOfLe_ι]
        rw [hYpb.w, hWpb.w, ← Category.assoc, ← Functor.map_comp, he'])
    refine eq_of_comp_eq_of_surjectiveEtale B S hS Y'.2.1 hG.isSheaf (Y'.2.2.1.fst φ)
      hαYsurj hαYetale ?_
    calc Y'.2.2.1.fst φ ≫ Subfunctor.homOfLe hY'W ≫ d
        = (Y'.2.2.1.fst φ ≫ Subfunctor.homOfLe hY'W) ≫ d := by rw [Category.assoc]
      _ = (yoneda.map e ≫ W.2.2.1.fst φ) ≫ d := by rw [hαYW]
      _ = yoneda.map e ≫ Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le ≫ hφdesc := by
            rw [Category.assoc, hd]
      _ = (yoneda.map e ≫ Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le) ≫
            hφdesc := by rw [Category.assoc]
      _ = (Subfunctor.lift (yoneda.map (Y'.2.2.1.snd φ)) hrangeqY.le ≫
            Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hY'W φ)) ≫ hφdesc := by
            rw [heL]
      _ = Subfunctor.lift (yoneda.map (Y'.2.2.1.snd φ)) hrangeqY.le ≫
            Subfunctor.fromPreimage Y'.1 φ ≫ f' := by rw [Category.assoc, hf']
      _ = (Subfunctor.lift (yoneda.map (Y'.2.2.1.snd φ)) hrangeqY.le ≫
            Subfunctor.fromPreimage Y'.1 φ) ≫ f' := by rw [Category.assoc]
      _ = Y'.2.2.1.fst φ ≫ f' := by rw [hLY]
  refine ⟨d, ⟨hrestrict Y hYW f hφ1, hrestrict Z hZW g hφ2⟩, ?_⟩
  rintro h ⟨h₁, h₂⟩
  refine hduniq h ?_
  have hinv : inv (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le) ≫
      W.2.2.1.fst φ ≫ h = hφdesc := by
    have key : ∀ (V : ClosedSubspaces B S hS X.1) (hVW : V.1 ≤ W.1) (f' : V.1.toFunctor ⟶ G),
        Subfunctor.homOfLe hVW ≫ h = f' →
        Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hVW φ) ≫
          inv (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le) ≫ W.2.2.1.fst φ ≫ h =
        Subfunctor.fromPreimage V.1 φ ≫ f' := by
      intro V hVW f' hh
      have hs : Subfunctor.homOfLe (Subfunctor.preimage_le_preimage hVW φ) ≫
          inv (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le) ≫ W.2.2.1.fst φ =
          Subfunctor.fromPreimage V.1 φ ≫ Subfunctor.homOfLe hVW :=
        (cancel_mono W.1.ι).1 (by
          simp only [Category.assoc]
          rw [hWpb.w, hLq, Subfunctor.homOfLe_ι_assoc, Subfunctor.homOfLe_ι,
            Subfunctor.fromPreimage_ι])
      rw [reassoc_of% hs, hh]
    exact hφuniq _ ⟨key Y hYW f h₁, key Z hZW g h₂⟩
  calc W.2.2.1.fst φ ≫ h
      = Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le ≫
          inv (Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le) ≫
            W.2.2.1.fst φ ≫ h := by rw [IsIso.hom_inv_id_assoc]
    _ = Subfunctor.lift (yoneda.map (W.2.2.1.snd φ)) hrangeq.le ≫ hφdesc := by rw [hinv]

end General

/-! ### The cocartesian square -/

/-- **[Stacks, Tag 0CZ1], third assertion.** Let `X` be an algebraic space over a scheme `S` and
let `Y, Z ⊆ X` be closed subspaces, with `Y ∪ Z` and `Y ∩ Z` the scheme-theoretic union and
intersection of [Stacks Project, Tag 0CYZ].  Then the square

```
Y ∩ Z ⟶ Y
  ↓        ↓
  Z   ⟶ Y ∪ Z
```

of the four closed subspaces and the four inclusions is cocartesian in the category of algebraic
spaces over `S`, that is, `Y ∪ Z = Y ⨿_{Y ∩ Z} Z`.

This is `AlgebraicGeometry.Space.existsUnique_desc_schemeTheoreticUnion` packaged as a colimit;
the square commutes because both composites are the inclusion of `Y ∩ Z` into `Y ∪ Z`. -/
@[stacks 0CZ1 "the square of the two subspaces, their scheme-theoretic intersection and their \
scheme-theoretic union is cocartesian in the category of algebraic spaces over the base"]
theorem isPushout_schemeTheoreticUnion (X : AlgebraicSpaces B S hS)
    (Y Z : ClosedSubspaces B S hS X.1) :
    IsPushout
      (ObjectProperty.homMk (Subfunctor.homOfLe (inf_le_left : Y.1 ⊓ Z.1 ≤ Y.1)) :
        closedSubspaceToSpace B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 Y Z) ⟶
          closedSubspaceToSpace B S hS X Y)
      (ObjectProperty.homMk (Subfunctor.homOfLe (inf_le_right : Y.1 ⊓ Z.1 ≤ Z.1)) :
        closedSubspaceToSpace B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 Y Z) ⟶
          closedSubspaceToSpace B S hS X Z)
      (ObjectProperty.homMk
          (Subfunctor.homOfLe (le_schemeTheoreticUnion_left B S hS X.2 Y Z)) :
        closedSubspaceToSpace B S hS X Y ⟶
          closedSubspaceToSpace B S hS X (schemeTheoreticUnion B S hS X.1 X.2 Y Z))
      (ObjectProperty.homMk
          (Subfunctor.homOfLe (le_schemeTheoreticUnion_right B S hS X.2 Y Z)) :
        closedSubspaceToSpace B S hS X Z ⟶
          closedSubspaceToSpace B S hS X (schemeTheoreticUnion B S hS X.1 X.2 Y Z)) := by
  classical
  refine IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.isColimitAux' _ fun t => ?_)
  · apply ObjectProperty.hom_ext
    change Subfunctor.homOfLe (inf_le_left : Y.1 ⊓ Z.1 ≤ Y.1) ≫
        Subfunctor.homOfLe (le_schemeTheoreticUnion_left B S hS X.2 Y Z) =
      Subfunctor.homOfLe (inf_le_right : Y.1 ⊓ Z.1 ≤ Z.1) ≫
        Subfunctor.homOfLe (le_schemeTheoreticUnion_right B S hS X.2 Y Z)
    rw [Subfunctor.homOfLe_comp, Subfunctor.homOfLe_comp]
  have h := existsUnique_desc_schemeTheoreticUnion B S hS X Y Z
    (schemeTheoreticUnion B S hS X.1 X.2 Y Z) t.pt.property t.inl.hom t.inr.hom rfl
    (le_schemeTheoreticUnion_left B S hS X.2 Y Z)
    (le_schemeTheoreticUnion_right B S hS X.2 Y Z) (congrArg (·.hom) t.condition)
  exact ⟨ObjectProperty.homMk h.choose, ObjectProperty.hom_ext _ h.choose_spec.1.1,
    ObjectProperty.hom_ext _ h.choose_spec.1.2, fun {m} h₁ h₂ => ObjectProperty.hom_ext _
      (h.choose_spec.2 m.hom ⟨congrArg (·.hom) h₁, congrArg (·.hom) h₂⟩)⟩

end AlgebraicGeometry.Space

end
