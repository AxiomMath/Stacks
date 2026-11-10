module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelocalizationRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationOfTopoi
public import StacksCore.Tactic.StacksAttribute

/-!
# The slice comparison for the relocalization of a ringed topos

Let `X = (Sh(C), O)` be a ringed topos, let `s : G ⟶ F` be a morphism of sheaves of sets on its
site, and let `Sh(C/F) ⟶ Sh(C)` and `Sh(C/G) ⟶ Sh(C/F)` be the localization and relocalization
morphisms of topoi
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RelocalizationRingedTopos.lean`).
[Stacks, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4) asserts that, once the two
localizations are identified with the slice topoi `Sh(C)/F` and `Sh(C)/G`, the inverse image of
the relocalization morphism *is* base change along `s`, and that the comparison is pinned down by
its compatibility with the two localization comparisons.

That assertion has an existence half and a uniqueness half. This file proves the **uniqueness**
half, and does so for an arbitrary pair of comparison isomorphisms, so that it applies to whatever
identification of `Sh(C/F)` with `Sh(C)/F` is eventually used; see the implementation notes for
what the existence half still needs. On the way it extracts the two pieces of
[Stacks, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE) that Tag 0791 already supplies: the
equivalence of the localized topos with the slice, and the identification of the lower shriek with
the forgetful functor from the slice.

The engine is a general fact about whiskering, proved first: if `J : A ⥤ B` has a **faithful** left
adjoint and `Q : B ⥤ D` **preserves monomorphisms**, then `θ ↦ J.whiskerLeft θ` is injective on
natural transformations with target `Q`. Specialized to the localization morphism this says that a
natural transformation out of `Sh(C)/F` is determined by its values on the objects pulled back
from `Sh(C)`, which is exactly the uniqueness clause of Tag 04J4.

## Main definitions

* `Stacks.Sheaves.LocalizedRingedTopos.sliceEquivalence` — **Stacks 04IE**: the equivalence of the
  localization of `X` at `F` with the slice topos `Sh(C)/F`.
* `Stacks.Sheaves.LocalizedRingedTopos.shriekAdjunction` — **Stacks 04IE**, part (3): the lower
  shriek of the localization morphism is the forgetful functor of the slice, as an adjunction
  `Sh(C)/F → Sh(C)` left adjoint to the inverse image.

## Main results

* `CategoryTheory.NatTrans.ext_of_whiskerLeft`, `CategoryTheory.Iso.ext_of_isoWhiskerLeft` and
  `CategoryTheory.Iso.ext_of_isoWhiskerLeft_trans` — the whiskering-injectivity criterion, in its
  natural-transformation, isomorphism, and "composed with a fixed isomorphism" forms.
* `Stacks.Sheaves.LocalizedRingedTopos.sliceEquivalenceFibers` — **Stacks 04IE**: the equivalence
  is the canonical fibre construction, on underlying presheaves.
* `Stacks.Sheaves.LocalizedRingedTopos.relocalization_inverseImage_unique` — **Stacks 04J4**: the
  uniqueness half of the comparison of the relocalization inverse image with base change. Two
  comparisons which agree after whiskering with the inverse image of the localization at `F` are
  equal.
* `Stacks.Sheaves.LocalizedRingedTopos.relocalization_inverseImage_unique_of_eq` — the same in the
  shape the source's `∃!` uses: two comparisons satisfying the same compatibility equation with a
  fixed isomorphism are equal.

## Implementation notes

* **Why faithfulness of the lower shriek is the right hypothesis.** The inverse image
  `j_F^{-1} : Sh(C) ⥤ Sh(C/F)` is *not* essentially surjective — its image consists of the
  "constant" objects `E × F ⟶ F` — so a natural transformation defined on that image does not
  extend uniquely to all of `Sh(C)/F`, and the whiskering map is in general *not surjective*. It
  is nevertheless injective, because the unit of `j_{F!} ⊣ j_F^{-1}` is a monomorphism as soon as
  `j_{F!}` is faithful (`CategoryTheory.Adjunction.unit_mono_of_L_faithful`), and `j_{F!}` is
  faithful here for the cheapest possible reason: it is an equivalence followed by `Over.forget`.
  On the slice model the unit at `(A, a)` is `(1, a) : A ⟶ A × F`, so this is the observation that
  every object of `Sh(C)/F` embeds in a constant one.
* **What the existence half still needs, and why it is not provable here.** The source's statement
  is an `∃!` whose property mentions the comparison isomorphisms of the localizations at `F` and at
  `G`. Uniqueness, proved below, holds for *every* choice of those; existence does not, and cannot:
  whiskering with `j_F^{-1}` is not surjective, so the prescribed isomorphism has to actually lie
  in its image, which is a statement about the particular comparison isomorphisms. (For a concrete
  failure, take `Sh(C)` the topos of `H`-sets for a group `H`, `F = H/K`, `G = H` and `s` the
  quotient map; then base change along `s` is the forgetful functor `K`-sets `⥤` sets, the constant
  objects are the restrictions of `H`-sets, and the two automorphism groups of those functors are
  `K` and `H` respectively, so the whiskering map is the inclusion `K ⊆ H`. Twisting a comparison
  isomorphism by an element of `H ∖ K` leaves a statement with no solution.) So the existence half
  needs the *construction* of those comparisons — Tag 04IE part (1) — and then the identification
  of restriction along postcomposition with base change, which is Tag 04J4's own mathematical
  content. Neither is done here, and nothing below is weakened in order to avoid them: the
  uniqueness statement takes the comparison isomorphisms as parameters.
* **Universes.** `Stacks.Sheaves.LocallyRingedTopos.RingedTopos` keeps the site, its homs and the
  sections of the
  structure sheaf in a single universe `u`; nothing here narrows that further. The general
  whiskering lemmas are at three independent object universes and three independent hom universes.

## References

* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {D : Type u₃} [Category.{v₃} D]

/-- **Whiskering with a functor having a faithful left adjoint is injective.** Let `L ⊣ J` with
`L : B ⥤ A` faithful, and let `P Q : B ⥤ D` with `Q` preserving monomorphisms. Then a natural
transformation `P ⟶ Q` is determined by its restriction along `J`, i.e. by its components at the
objects in the image of `J`.

Faithfulness of `L` makes every component of the unit `T ⟶ J.obj (L.obj T)` a monomorphism, and
`Q` preserves it; naturality of `θ` at the unit then expresses `θ.app T` through the component of
`J.whiskerLeft θ` at `L.obj T`. -/
theorem NatTrans.ext_of_whiskerLeft {L : B ⥤ A} {J : A ⥤ B} (adj : L ⊣ J) [L.Faithful]
    {P Q : B ⥤ D} [Q.PreservesMonomorphisms] {θ θ' : P ⟶ Q}
    (h : Functor.whiskerLeft J θ = Functor.whiskerLeft J θ') : θ = θ' := by
  ext T
  have h1 : P.map (adj.unit.app T) ≫ θ.app (J.obj (L.obj T))
      = θ.app T ≫ Q.map (adj.unit.app T) := θ.naturality (adj.unit.app T)
  have h2 : P.map (adj.unit.app T) ≫ θ'.app (J.obj (L.obj T))
      = θ'.app T ≫ Q.map (adj.unit.app T) := θ'.naturality (adj.unit.app T)
  have key : θ.app (J.obj (L.obj T)) = θ'.app (J.obj (L.obj T)) :=
    congrArg (fun t ↦ NatTrans.app t (L.obj T)) h
  rw [← cancel_mono (Q.map (adj.unit.app T)), ← h1, ← h2, key]

/-- `CategoryTheory.NatTrans.ext_of_whiskerLeft` for isomorphisms of functors. -/
theorem Iso.ext_of_isoWhiskerLeft {L : B ⥤ A} {J : A ⥤ B} (adj : L ⊣ J) [L.Faithful]
    {P Q : B ⥤ D} [Q.PreservesMonomorphisms] {γ γ' : P ≅ Q}
    (h : Functor.isoWhiskerLeft J γ = Functor.isoWhiskerLeft J γ') : γ = γ' :=
  Iso.ext (NatTrans.ext_of_whiskerLeft adj (congrArg Iso.hom h))

/-- `CategoryTheory.Iso.ext_of_isoWhiskerLeft` after composing with a fixed isomorphism. This is
the shape in which a comparison isomorphism is pinned down by a compatibility equation: the
equation determines the whiskering of the comparison, and the whiskering determines the
comparison. -/
theorem Iso.ext_of_isoWhiskerLeft_trans {L : B ⥤ A} {J : A ⥤ B} (adj : L ⊣ J) [L.Faithful]
    {P Q : B ⥤ D} [Q.PreservesMonomorphisms] {R : A ⥤ D} (Φ : J ⋙ Q ≅ R) {γ γ' : P ≅ Q}
    (h : Functor.isoWhiskerLeft J γ ≪≫ Φ = Functor.isoWhiskerLeft J γ' ≪≫ Φ) : γ = γ' := by
  refine Iso.ext_of_isoWhiskerLeft adj (Iso.ext ?_)
  have h' : Functor.whiskerLeft J γ.hom ≫ Φ.hom = Functor.whiskerLeft J γ'.hom ≫ Φ.hom :=
    congrArg Iso.hom h
  exact (cancel_mono Φ.hom).1 h'

end CategoryTheory

namespace Stacks.Sheaves.LocalizedRingedTopos

open Stacks.Sheaves.LocallyRingedTopos

universe u

variable {X : RingedTopos.{u}} {G F : X.Topos}

/-- **Stacks 04IE**, the equivalence with the slice topos: sheaves on the site of elements of `F`
are the same thing as sheaves on `C` over `F`. This is the sheaf-level restriction of the
canonical equivalence of Tag 0791, taken from
`CategoryTheory.Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda`. -/
@[stacks 04IE "equivalence with the slice topos",
  sga "3 IV 4.5.4" "more general",
  sga "4 III 5.4" "special case"]
noncomputable def sliceEquivalence (X : RingedTopos.{u}) (F : X.Topos) :
    (localizedRingedTopos X F).Topos ≌ Over F :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2))

/-- **Stacks 04IE**, part (3): the lower shriek of the localization morphism on sheaves of sets is
the forgetful functor of the slice. Concretely, `Sh(C/F) ≌ Sh(C)/F` followed by `Over.forget F` is
left adjoint to the inverse image of the localization morphism, which is restriction along the
projection from the site of elements. -/
@[stacks 04IE "part (3): lower shriek on sets", sga "4 III 5.5" "Clause 3), special case"]
noncomputable def shriekAdjunction (X : RingedTopos.{u}) (F : X.Topos) :
    (sliceEquivalence X F).functor ⋙ Over.forget F ⊣
      (localizationToposMorphism X F).inverseImage :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2))).2.some

/-- **Stacks 04IE**: the equivalence with the slice topos is the canonical fibre construction and
not merely an abstract equivalence. On underlying presheaves, the inverse of `sliceEquivalence`
sends an object `φ : A ⟶ F` of `Sh(C)/F` to the presheaf `(U, t) ↦ {x ∈ A(U) | φ(x) = t}` on the
site of elements of `F`. -/
@[stacks 04IE "canonical identification with the slice topos"]
noncomputable def sliceEquivalenceFibers (X : RingedTopos.{u}) (F : X.Topos) :
    (sliceEquivalence X F).inverse ⋙ sheafToPresheaf (elementTopology X F) (Type u) ≅
      Over.post (X := F) (sheafToPresheaf X.J (Type u)) ⋙
        (overEquivPresheafCostructuredArrow F.obj).functor :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda F.property).2.2))).1.some

/-- **Stacks 04J4**, the uniqueness half of the identification of the relocalization inverse image
with base change. Fix an identification `eF` of the localization of `X` at `F` with the slice topos
`Sh(C)/F` whose composite with `Over.forget F` is the lower shriek, i.e. is left adjoint to the
inverse image of the localization morphism (the canonical such identification is
`sliceEquivalence`, with `shriekAdjunction`). Then two isomorphisms of a functor `P` with
`eF ⋙ (base change along s)` which agree after whiskering with the inverse image of the
localization at `F` are equal.

`P` is arbitrary; the case of interest is `P = (relocalization inverse image) ⋙ eG`, for an
identification `eG` of the localization at `G` with `Sh(C)/G`. The hypothesis on `eF` is used only
through the faithfulness of the lower shriek. -/
@[stacks 04J4 "uniqueness of the comparison with base change on slice topoi"]
theorem relocalization_inverseImage_unique (s : G ⟶ F)
    {eF : (localizedRingedTopos X F).Topos ≌ Over F}
    (adjF : eF.functor ⋙ Over.forget F ⊣ (localizationToposMorphism X F).inverseImage)
    {P : (localizedRingedTopos X F).Topos ⥤ Over G}
    {γ γ' : P ≅ eF.functor ⋙ Over.pullback s}
    (h : Functor.isoWhiskerLeft (localizationToposMorphism X F).inverseImage γ
      = Functor.isoWhiskerLeft (localizationToposMorphism X F).inverseImage γ') :
    γ = γ' :=
  Iso.ext_of_isoWhiskerLeft adjF h

/-- **Stacks 04J4**, the uniqueness half in the shape of the source's `∃!`: a comparison of the
relocalization inverse image with base change is determined by a compatibility equation with the
localization comparisons. Here `Φ` is the isomorphism against which the compatibility is stated
and `Ψ` is the prescribed value; both are arbitrary, so this covers any choice of the comparison
isomorphisms for the localizations at `F` and at `G`. -/
@[stacks 04J4 "the comparison with base change is pinned down by the localization comparisons"]
theorem relocalization_inverseImage_unique_of_eq (s : G ⟶ F)
    {eF : (localizedRingedTopos X F).Topos ≌ Over F}
    (adjF : eF.functor ⋙ Over.forget F ⊣ (localizationToposMorphism X F).inverseImage)
    {P : (localizedRingedTopos X F).Topos ⥤ Over G} {R : X.Topos ⥤ Over G}
    (Φ : (localizationToposMorphism X F).inverseImage ⋙ (eF.functor ⋙ Over.pullback s) ≅ R)
    (Ψ : (localizationToposMorphism X F).inverseImage ⋙ P ≅ R)
    {γ γ' : P ≅ eF.functor ⋙ Over.pullback s}
    (hγ : Functor.isoWhiskerLeft (localizationToposMorphism X F).inverseImage γ ≪≫ Φ = Ψ)
    (hγ' : Functor.isoWhiskerLeft (localizationToposMorphism X F).inverseImage γ' ≪≫ Φ = Ψ) :
    γ = γ' :=
  Iso.ext_of_isoWhiskerLeft_trans adjF Φ (hγ.trans hγ'.symm)

end Stacks.Sheaves.LocalizedRingedTopos

end
