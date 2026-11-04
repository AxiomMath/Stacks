module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms between representable categories fibred in groupoids

Let `𝒞` be a category and let `𝒳`, `𝒴` be categories fibred in groupoids over `𝒞` which are
*representable*, by objects `X`, `Y` of `𝒞`: each is equivalent over `𝒞` to a slice category
`𝒞/X`, resp. `𝒞/Y` (`StacksRepresentableCFG.RepresentableBy`). Stacks 04SF says that
`Mor_{Cat/𝒞}(𝒳, 𝒴)` modulo 2-isomorphism is `Mor_𝒞(X, Y)`, and more precisely that every
`φ : X ⟶ Y` is induced by a 1-morphism `𝒳 ⟶ 𝒴` which is unique up to unique 2-isomorphism.

## Main results

* `CategoryTheory.Functor.isoClassPresheafHomEquiv`: for `p`, `q` whose presheaves of isomorphism
  classes are representable by `X`, `Y`, the maps `\overline{𝒳} ⟶ \overline{𝒴}` of presheaves are
  the morphisms `X ⟶ Y` of `𝒞`. This is the Yoneda step of the source's proof.
* `CategoryTheory.Functor.twoIsoQuotientEquivHomOfRepresentableBy`: **Stacks 04SF**, the bijection
  `Mor_{Cat/𝒞}(𝒳, 𝒴)/2\text{-isomorphism} = Mor_𝒞(X, Y)`.
* `CategoryTheory.Functor.exists_oneMorphism_inducing_hom`: **Stacks 04SF**, "more precisely":
  a `φ : X ⟶ Y` is induced by a 1-morphism, unique up to unique 2-isomorphism.

## Implementation notes

The source's proof is: `𝒞/X = 𝒮_{h_X}` (Stacks 0044), so by Stacks 04SC
`Mor(𝒳, 𝒴)/2\text{-iso} = Mor_{PSh(𝒞)}(h_X, h_Y)`, which is `Mor_𝒞(X, Y)` by Yoneda
(Stacks 001P). Here the Stacks 04SC step is `CategoryTheory.Functor.isoClassMapEquiv`, and the
remaining two steps are combined into `isoClassPresheafHomEquiv`: rather than first identifying
`\overline{𝒳}` with `h_X` as presheaves — which would force the universe of the objects of `𝒳` to
agree with the hom universe of `𝒞` — the Yoneda argument is run directly on the natural family of
bijections `\overline{𝒳}(U) ≃ (U ⟶ X)` that representability supplies
(`StacksRepresentableCFG.IsoClassRepresentableBy`). The bijection sends a map of presheaves `t` to
`t` evaluated at the "universal" class, the one corresponding to `𝟙 X`, and a morphism `φ` to
`c ↦ (equiv U)⁻¹ (equiv U c ≫ φ)`.

Representability is not an extra hypothesis on top of "fibred in groupoids": a category over `𝒞`
equivalent over `𝒞` to a slice is automatically fibred in setoids, hence in groupoids
(`StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver` applied to
`StacksRepresentableCFG.over_isFiberedInSetoids`), which is why the statements below take only the
representability data. The "more precisely" clause is stated with the data of Stacks 04S9,
`StacksRepresentableCFG.IsoClassRepresentableBy`, since "induces `φ` on isomorphism classes of
objects" refers to those bijections; by Stacks 02Y3 having them, together with being fibred in
setoids, is the same as being representable.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.Functor

universe v₁ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 𝒴 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₁} 𝒴]

/-- Two maps of `Type`-valued presheaves agree as soon as they agree on elements. This is stated
so that the pointwise goals appear as `t.app U c = s.app U c`, rather than in the unfolded form
that `ext` leaves behind for the concrete category `Type`. -/
lemma presheafHom_ext {F G : 𝒞ᵒᵖ ⥤ Type u₂} {t s : F ⟶ G}
    (h : ∀ (U : 𝒞ᵒᵖ) (c : F.obj U), t.app U c = s.app U c) : t = s := by
  ext U c
  exact h U c

/-- A category over `𝒞` representable by `X` is fibred in setoids: it is equivalent over `𝒞` to a
slice category, and a slice category is fibred in setoids. -/
lemma isFiberedInSetoids_of_representableBy {p : 𝒳 ⥤ 𝒞} {X : 𝒞}
    (hX : StacksRepresentableCFG.RepresentableBy p X) : p.IsFiberedInSetoids :=
  StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver hX
    (StacksRepresentableCFG.over_isFiberedInSetoids X)

/-- Representability of the presheaf of isomorphism classes, as supplied by
`StacksRepresentableCFG.IsoClassRepresentableBy`, is naturality of the family of bijections with
respect to the restriction maps of `CategoryTheory.Functor.isoClassPresheaf`: the chosen pullback
is a pullback in the sense of `StacksRepresentableCFG.IsPullbackOver`. -/
lemma isoClassRepresentableBy_equiv_isoClassPresheaf_map {p : 𝒳 ⥤ 𝒞} [p.IsFibered] {X : 𝒞}
    (hX : StacksRepresentableCFG.IsoClassRepresentableBy p X) {V U : 𝒞} (g : V ⟶ U)
    (c : p.isoClassPresheaf.obj (op U)) :
    hX.equiv V (p.isoClassPresheaf.map g.op c) = g ≫ hX.equiv U c := by
  induction c using _root_.Quotient.ind with
  | _ x =>
    refine hX.naturality g x (pullbackFiber p x g)
      ⟨IsPreFibered.pullbackMap x.2 g,
        (IsPreFibered.pullbackMap.IsCartesian x.2 g).toIsHomLift, ?_⟩
    exact IsFibered.isStronglyCartesian_of_isCartesian p g (IsPreFibered.pullbackMap x.2 g)

/-- `CategoryTheory.Functor.isoClassRepresentableBy_equiv_isoClassPresheaf_map` with the morphism
of the base taken in `𝒞ᵒᵖ`, which is the form in which the naturality of a map of presheaves
presents it. -/
lemma isoClassRepresentableBy_equiv_isoClassPresheaf_map' {p : 𝒳 ⥤ 𝒞} [p.IsFibered] {X : 𝒞}
    (hX : StacksRepresentableCFG.IsoClassRepresentableBy p X) {U V : 𝒞ᵒᵖ} (g : U ⟶ V)
    (c : p.isoClassPresheaf.obj U) :
    hX.equiv V.unop (p.isoClassPresheaf.map g c) = g.unop ≫ hX.equiv U.unop c :=
  isoClassRepresentableBy_equiv_isoClassPresheaf_map hX g.unop c

section

variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} [p.IsFibered] [q.IsFibered] {X Y : 𝒞}
  (hX : StacksRepresentableCFG.IsoClassRepresentableBy p X)
  (hY : StacksRepresentableCFG.IsoClassRepresentableBy q Y)

include hX hY in
/-- The map of presheaves attached to a morphism `φ : X ⟶ Y` of `𝒞` by representability: on
`\overline{𝒳}(U)` it is composition with `φ`, read through the bijections
`\overline{𝒳}(U) ≃ (U ⟶ X)` and `\overline{𝒴}(U) ≃ (U ⟶ Y)`. -/
noncomputable def isoClassPresheafHomOfHom (φ : X ⟶ Y) :
    p.isoClassPresheaf ⟶ q.isoClassPresheaf where
  app U := ↾fun c => (hY.equiv U.unop).symm (hX.equiv U.unop c ≫ φ)
  naturality {U V} g := by
    ext c
    dsimp
    refine (hY.equiv V.unop).injective ?_
    have h1 := isoClassRepresentableBy_equiv_isoClassPresheaf_map' hY g
      ((hY.equiv U.unop).symm (hX.equiv U.unop c ≫ φ))
    have h2 := isoClassRepresentableBy_equiv_isoClassPresheaf_map' hX g c
    rw [Equiv.apply_symm_apply, h1, Equiv.apply_symm_apply, h2, Category.assoc]

include hX hY in
/-- The value of `CategoryTheory.Functor.isoClassPresheafHomOfHom` at an isomorphism class `c`
over `U`: transport `c` to a morphism `U ⟶ X`, compose with `φ`, and transport back. -/
lemma isoClassPresheafHomOfHom_app (φ : X ⟶ Y) (U : 𝒞) (c : p.isoClassPresheaf.obj (op U)) :
    (isoClassPresheafHomOfHom hX hY φ).app (op U) c
      = (hY.equiv U).symm (hX.equiv U c ≫ φ) :=
  rfl

include hX hY in
/-- The morphism `X ⟶ Y` of `𝒞` attached to a map `\overline{𝒳} ⟶ \overline{𝒴}` of presheaves by
representability: its value at the class corresponding to `𝟙 X`. -/
noncomputable def isoClassPresheafHomToHom (t : p.isoClassPresheaf ⟶ q.isoClassPresheaf) :
    X ⟶ Y :=
  hY.equiv X (t.app (op X) ((hX.equiv X).symm (𝟙 X)))

include hX hY in
/-- `CategoryTheory.Functor.isoClassPresheafHomToHom` unfolded: the morphism `X ⟶ Y` attached to
a map `t` of presheaves is the value of `t` at the class corresponding to `𝟙 X`. -/
lemma isoClassPresheafHomToHom_eq (t : p.isoClassPresheaf ⟶ q.isoClassPresheaf) :
    isoClassPresheafHomToHom hX hY t
      = hY.equiv X (t.app (op X) ((hX.equiv X).symm (𝟙 X))) :=
  rfl

include hX hY in
/-- **The Yoneda step of Stacks 04SF.** For categories over `𝒞` whose presheaves of isomorphism
classes are representable by `X` and `Y`, the maps `\overline{𝒳} ⟶ \overline{𝒴}` of presheaves
are exactly the morphisms `X ⟶ Y` of `𝒞`. A map of presheaves is recovered from its value at the
class corresponding to `𝟙 X`, which is the Yoneda lemma. -/
@[ega "0 8.1.8" "special case"]
noncomputable def isoClassPresheafHomEquiv :
    (p.isoClassPresheaf ⟶ q.isoClassPresheaf) ≃ (X ⟶ Y) where
  toFun := isoClassPresheafHomToHom hX hY
  invFun := isoClassPresheafHomOfHom hX hY
  left_inv t := presheafHom_ext fun U c => by
    obtain ⟨U⟩ := U
    refine (hY.equiv U).injective ?_
    have hA := isoClassPresheafHomOfHom_app hX hY (isoClassPresheafHomToHom hX hY t) U c
    have hc : p.isoClassPresheaf.map (hX.equiv U c).op ((hX.equiv X).symm (𝟙 X)) = c := by
      refine (hX.equiv U).injective ?_
      have h2 := isoClassRepresentableBy_equiv_isoClassPresheaf_map hX (hX.equiv U c)
        ((hX.equiv X).symm (𝟙 X))
      rw [h2, Equiv.apply_symm_apply, Category.comp_id]
    have hnat := NatTrans.naturality_apply t (hX.equiv U c).op ((hX.equiv X).symm (𝟙 X))
    rw [hc] at hnat
    have h3 := isoClassRepresentableBy_equiv_isoClassPresheaf_map hY (hX.equiv U c)
      (t.app (op X) ((hX.equiv X).symm (𝟙 X)))
    rw [hA, Equiv.apply_symm_apply, hnat, h3, isoClassPresheafHomToHom_eq]
  right_inv φ := by
    have hA := isoClassPresheafHomOfHom_app hX hY φ X ((hX.equiv X).symm (𝟙 X))
    rw [isoClassPresheafHomToHom_eq, hA, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Category.id_comp]

/-- `CategoryTheory.Functor.isoClassPresheafHomOfHom_app` read through the bijection for `𝒴`. -/
private lemma equiv_isoClassPresheafHomOfHom_app (φ : X ⟶ Y) (U : 𝒞)
    (c : p.isoClassPresheaf.obj (op U)) :
    hY.equiv U ((isoClassPresheafHomOfHom hX hY φ).app (op U) c) = hX.equiv U c ≫ φ :=
  Equiv.apply_symm_apply ..

variable [p.IsFiberedInSetoids] [q.IsFiberedInSetoids]

include hX hY in
/-- **Stacks 04SF**, in terms of the data of Stacks 04S9: for categories fibred in setoids over
`𝒞` whose presheaves of isomorphism classes are representable by `X` and `Y`, the 1-morphisms
`𝒳 ⟶ 𝒴` over `𝒞` modulo 2-isomorphism are the morphisms `X ⟶ Y` of `𝒞`. -/
noncomputable def twoIsoQuotientEquivHom :
    _root_.Quotient (twoIsoSetoid p q) ≃ (X ⟶ Y) :=
  (isoClassMapEquiv p q).trans (isoClassPresheafHomEquiv hX hY)

include hX hY in
/-- **Stacks 04SF**, the precise form: given `φ : X ⟶ Y` there is a 1-morphism `G : 𝒳 ⥤ 𝒴` over
`𝒞` which induces `φ` on isomorphism classes of objects, and any 1-morphism inducing `φ` is
related to it by a unique 2-isomorphism. Inducing `φ` is spelled out through the bijections
`\overline{𝒳}(U) ≃ (U ⟶ X)` and `\overline{𝒴}(U) ≃ (U ⟶ Y)` that representability supplies. -/
@[stacks 04SF "Given `φ : X ⟶ Y` there is a 1-morphism inducing it, unique up to unique
2-isomorphism."]
theorem exists_oneMorphism_inducing_hom (φ : X ⟶ Y) :
    ∃ (G : 𝒳 ⥤ 𝒴) (hG : G ⋙ q = p),
      (∀ (U : 𝒞) (c : p.isoClassPresheaf.obj (op U)),
        hY.equiv U ((isoClassMapOfCompEq hG).app (op U) c) = hX.equiv U c ≫ φ) ∧
      ∀ (H : 𝒳 ⥤ 𝒴) (hH : H ⋙ q = p),
        (∀ (U : 𝒞) (c : p.isoClassPresheaf.obj (op U)),
          hY.equiv U ((isoClassMapOfCompEq hH).app (op U) c) = hX.equiv U c ≫ φ) →
        ∃! e : G ≅ H, ∀ x : 𝒳, q.IsHomLift (𝟙 (p.obj x)) (e.hom.app x) := by
  obtain ⟨G, hG, hGt⟩ := exists_oneMorphism_isoClassMap_eq (isoClassPresheafHomOfHom hX hY φ)
  refine ⟨G, hG, fun U c => ?_, fun H hH hHφ => ?_⟩
  · rw [hGt, equiv_isoClassPresheafHomOfHom_app]
  · refine existsUnique_twoIso_of_isoClassMap_eq hG hH
      (hGt.trans (presheafHom_ext fun U c => (hY.equiv U.unop).injective ?_))
    rw [equiv_isoClassPresheafHomOfHom_app, hHφ U.unop c]

end

section

variable {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {X Y : 𝒞}
  (hX : StacksRepresentableCFG.RepresentableBy p X)
  (hY : StacksRepresentableCFG.RepresentableBy q Y)

include hX hY in
/-- **Stacks 04SF.** Let `𝒳`, `𝒴` be categories fibred in groupoids over `𝒞` representable by
objects `X`, `Y` of `𝒞`. Then `Mor_{Cat/𝒞}(𝒳, 𝒴)` modulo 2-isomorphism is `Mor_𝒞(X, Y)`. The
bijection is the composite of Stacks 04SC, which identifies the left-hand side with the maps
`\overline{𝒳} ⟶ \overline{𝒴}` of presheaves of isomorphism classes, with the Yoneda step
`CategoryTheory.Functor.isoClassPresheafHomEquiv`. -/
@[stacks 04SF]
noncomputable def twoIsoQuotientEquivHomOfRepresentableBy :
    _root_.Quotient (twoIsoSetoid p q) ≃ (X ⟶ Y) :=
  letI := isFiberedInSetoids_of_representableBy hX
  letI := isFiberedInSetoids_of_representableBy hY
  twoIsoQuotientEquivHom
    (StacksRepresentableCFG.isoClassRepresentableBy_of_equivalenceOver hX)
    (StacksRepresentableCFG.isoClassRepresentableBy_of_equivalenceOver hY)

end

end CategoryTheory.Functor
