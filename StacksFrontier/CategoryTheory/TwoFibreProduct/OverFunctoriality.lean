module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.CategoryTheory.TwoFibreProductOverReindex

/-!
# Functoriality of the 2-fibre product over a base in its target and in its second factor

Fix a base category `𝒞`. For categories `T`, `𝒜`, `ℬ` over `𝒞` with structure functors `pT`,
`p𝒜`, `pℬ` and 1-morphisms `G : T ⥤ ℬ`, `F : 𝒜 ⥤ ℬ` over `𝒞`, the 2-fibre product over `𝒞` of
Stacks 0040 is `CategoryTheory.TwoFibreProductOver pT p𝒜 pℬ G F`. This file records the two
ways of replacing one of the three categories entering it by an equivalent one, *keeping the
first factor `T` and the 1-morphism `G` out of it fixed*:

* `CategoryTheory.TwoFibreProductOver.mapBase` postcomposes both legs with a 1-morphism
  `b : ℬ ⥤ 𝒟` over `𝒞`, giving `T ×_ℬ 𝒜 ⥤ T ×_𝒟 𝒜`; it is an equivalence as soon as `b` is
  **fully faithful**, which is strictly weaker than `b` being an equivalence and is what
  Stacks 0BPU needs of the inclusion of a closed substack;
* `CategoryTheory.TwoFibreProductOver.precomposeSnd` precomposes the second leg with a
  1-morphism `a : 𝒜' ⥤ 𝒜` over `𝒞`, giving `T ×_{G, ℬ, a ⋙ F} 𝒜' ⥤ T ×_{G, ℬ, F} 𝒜`; it is an
  equivalence as soon as `a` is and the three structure functors involved are fibred in
  groupoids.

Both commute with the first projection on the nose, so both are 1-morphisms of categories over
`T`; together with
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` this turns each of them into
an equivalence over `T` in the sense of `StacksRepresentableCFG.EquivalenceOver`, which is the
shape `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` consumes.

These complement `StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison`, which replaces
the second factor by an equivalent one given as unbundled equivalence data and produces the
unit and the counit by hand, and
`StacksFrontier.CategoryTheory.TwoFibreProductOverReindex`, which replaces a leg by an isomorphic
one. Here the equivalence data is produced instead by Stacks 003Z (2),
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`, from the bare statement that
the comparison functor is an equivalence of the underlying categories; that is cheaper and is
all a representability argument needs, since the predicates of Stacks 04SV and 02ZW ask only
for a `Nonempty` equivalence over the site.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.mapBase`: change of target.
* `CategoryTheory.TwoFibreProductOver.precomposeSnd`: change of second factor.

## Main results

* `StacksRepresentableCFG.equivalenceOverOfIsEquivalence` and
  `StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`: a 1-morphism of
  categories fibred in groupoids over `𝒞` which is an equivalence of the underlying categories
  is an equivalence over `𝒞`; the first form keeps that 1-morphism as the forward one on the
  nose, which is what a consumer computing with the equivalence needs.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase` and
  `CategoryTheory.TwoFibreProductOver.isEquivalence_precomposeSnd`.
* `CategoryTheory.TwoFibreProductOver.mapBase_comp_fst` and
  `CategoryTheory.TwoFibreProductOver.precomposeSnd_comp_fst`: both comparisons are strictly
  over the first factor, which is what feeds them into
  `StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`.
* `CategoryTheory.TwoFibreProductOver.mapBase_comp_structureFunctor` and
  `CategoryTheory.TwoFibreProductOver.precomposeSnd_comp_structureFunctor`: both are strictly
  over `𝒞` as well, which is the commuting equation
  `StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` takes when the two sides are
  read as categories fibred in groupoids over the site rather than over the first factor.

## Implementation notes

`AlgebraicGeometry.Stack.RepresentabilityInvariance` carries file-private copies of the two
functors and of their equivalence proofs, under the names `product_postcompose` and
`product_precompose_source`; they are the same constructions, and the proofs here are those.
That file should be refactored onto these public names.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
-/

@[expose] public section

open CategoryTheory

namespace StacksRepresentableCFG

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- If `A ⋙ q = p` and `B ⋙ p = q`, then `B ∘ A` does not change the `p`-image of an object. -/
private theorem obj_comp_eq {𝒞 : Type u₁} [Category.{v₁} 𝒞] {D₁ : Type u₂} [Category.{v₂} D₁]
    {D₂ : Type u₃} [Category.{v₃} D₂] {p : D₁ ⥤ 𝒞} {q : D₂ ⥤ 𝒞} {A : D₁ ⥤ D₂} {B : D₂ ⥤ D₁}
    (hA : A ⋙ q = p) (hB : B ⋙ p = q) (X : D₁) : p.obj ((A ⋙ B).obj X) = p.obj X :=
  Functor.congr_obj (show (A ⋙ B) ⋙ p = p by rw [Functor.assoc, hB, hA]) X

/-- **Stacks 003Z (2), as quasi-inverse data on a named 1-morphism.** A 1-morphism `K` of
categories fibred in groupoids over `𝒞` whose underlying functor is an equivalence of categories
has a quasi-inverse strictly over `𝒞` with vertical unit and counit. This is
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over` with its conclusion repackaged
as the structure `CategoryTheory.Functor.IsEquivalenceOver`, whose verticality clauses read the
base object at the source of each component. -/
theorem nonempty_isEquivalenceOver_of_isEquivalence {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {D₁ : Type u₂} [Category.{v₂} D₁] {D₂ : Type u₃} [Category.{v₃} D₂]
    {p₁ : D₁ ⥤ 𝒞} {p₂ : D₂ ⥤ 𝒞} (h₁ : p₁.IsFiberedInGroupoids)
    (h₂ : p₂.IsFiberedInGroupoids) (K : D₁ ⥤ D₂) (hK : K ⋙ p₂ = p₁)
    (hKe : K.IsEquivalence) : Nonempty (Functor.IsEquivalenceOver p₁ p₂ K) := by
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over p₁ p₂ h₁ h₂ K hK hKe
  refine ⟨{ inv := F, inv_over := hF, unitIso := η, counitIso := ε,
            unit_vertical := fun X => ?_, counit_vertical := fun Y => ?_ }⟩
  · rw [obj_comp_eq hK hF X]
    exact hη X
  · rw [obj_comp_eq hF hK Y]
    exact hε Y

/-- **Stacks 003Z (2), in the shape `StacksRepresentableCFG.EquivalenceOver` wants, with the
forward 1-morphism named.** A 1-morphism `K` of categories fibred in groupoids over `𝒞` whose
underlying functor is an equivalence of categories, read as an equivalence over `𝒞` *whose
forward 1-morphism is `K` on the nose*
(`StacksRepresentableCFG.equivalenceOverOfIsEquivalence_hom`); only the quasi-inverse, the unit
and the counit come from a choice.

Naming `K` is what a consumer that has to *compute* with the equivalence needs — for instance
one reading a section of a representing presheaf off an object through
`CategoryTheory.PresheafOfCategories.sectionOfObj`, which is defined by applying the forward
1-morphism, so that an equivalence known only to exist names no section at all. -/
noncomputable def equivalenceOverOfIsEquivalence {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {D₁ : Type u₂} [Category.{v₂} D₁] {D₂ : Type u₃} [Category.{v₃} D₂]
    {p₁ : D₁ ⥤ 𝒞} {p₂ : D₂ ⥤ 𝒞} (h₁ : p₁.IsFiberedInGroupoids)
    (h₂ : p₂.IsFiberedInGroupoids) (K : D₁ ⥤ D₂) (hK : K ⋙ p₂ = p₁)
    (hKe : K.IsEquivalence) : EquivalenceOver p₁ p₂ :=
  EquivalenceOver.ofFunctorIsEquivalenceOver hK
    (nonempty_isEquivalenceOver_of_isEquivalence h₁ h₂ K hK hKe).some

/-- The forward 1-morphism of `StacksRepresentableCFG.equivalenceOverOfIsEquivalence` is the
given one. -/
@[simp] theorem equivalenceOverOfIsEquivalence_hom {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {D₁ : Type u₂} [Category.{v₂} D₁] {D₂ : Type u₃} [Category.{v₃} D₂]
    {p₁ : D₁ ⥤ 𝒞} {p₂ : D₂ ⥤ 𝒞} (h₁ : p₁.IsFiberedInGroupoids)
    (h₂ : p₂.IsFiberedInGroupoids) (K : D₁ ⥤ D₂) (hK : K ⋙ p₂ = p₁)
    (hKe : K.IsEquivalence) :
    (equivalenceOverOfIsEquivalence h₁ h₂ K hK hKe).hom.functor = K := rfl

/-- **Stacks 003Z (2), in the shape `StacksRepresentableCFG.EquivalenceOver` wants.** A
1-morphism `K` of categories fibred in groupoids over `𝒞` whose underlying functor is an
equivalence of categories is an equivalence over `𝒞`: a quasi-inverse strictly over `𝒞`
exists, with vertical unit and counit.

Only `Nonempty` is asserted, because
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` and
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` both ask for no more. When the
forward 1-morphism has to be named, use
`StacksRepresentableCFG.equivalenceOverOfIsEquivalence`. -/
theorem nonempty_equivalenceOver_of_isEquivalence {𝒞 : Type u₁} [Category.{v₁} 𝒞]
    {D₁ : Type u₂} [Category.{v₂} D₁] {D₂ : Type u₃} [Category.{v₃} D₂]
    {p₁ : D₁ ⥤ 𝒞} {p₂ : D₂ ⥤ 𝒞} (h₁ : p₁.IsFiberedInGroupoids)
    (h₂ : p₂.IsFiberedInGroupoids) (K : D₁ ⥤ D₂) (hK : K ⋙ p₂ = p₁)
    (hKe : K.IsEquivalence) : Nonempty (EquivalenceOver p₁ p₂) :=
  ⟨equivalenceOverOfIsEquivalence h₁ h₂ K hK hKe⟩

end StacksRepresentableCFG

namespace CategoryTheory.TwoFibreProductOver

universe vC vT vA vB vD uC uT uA uB uD

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {T : Type uT} [Category.{vT} T]

section MapBase

variable {𝒜 : Type uA} [Category.{vA} 𝒜] {ℬ : Type uB} [Category.{vB} ℬ]
  {𝒟 : Type uD} [Category.{vD} 𝒟]
  {pT : T ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}

/-- Postcomposition of both legs of a 2-fibre product over `𝒞` with a 1-morphism
`b : ℬ ⥤ 𝒟` over `𝒞`: an object `(U, t, x, φ : G t ≅ F x)` of `T ×_ℬ 𝒜` is sent to
`(U, t, x, b φ)`, an object of `T ×_𝒟 𝒜` taken along the two composed legs. Verticality of
`b φ` is verticality of `φ` because `b` is over `𝒞`. -/
def mapBase (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (b : ℬ ⥤ 𝒟) (hb : b ⋙ p𝒟 = pℬ) :
    TwoFibreProductOver pT p𝒜 pℬ G F ⥤ TwoFibreProductOver pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b) where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := b.mapIso P.iso
      vertical := by
        have := P.vertical
        have h := Functor.isHomLift_map_of_comp_eq hb (𝟙 P.base) P.iso.hom
        simpa using h }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.a
      b := f.b
      ha := f.ha
      hb := f.hb
      w := by
        simpa only [Functor.comp_map, Functor.mapIso_hom, Functor.map_comp] using
          congrArg b.map f.w }
  map_id P := by apply TwoFibreProductOver.Hom.ext <;> rfl
  map_comp f g := by apply TwoFibreProductOver.Hom.ext <;> rfl

/-- `mapBase` commutes with the first projection on the nose. -/
@[simp] lemma mapBase_comp_fst (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (b : ℬ ⥤ 𝒟) (hb : b ⋙ p𝒟 = pℬ) :
    mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb ⋙ fst pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b) =
      fst pT p𝒜 pℬ G F :=
  rfl

/-- `mapBase` is strictly over `𝒞`: it changes neither the base object of an object nor the base
morphism of a morphism. -/
@[simp] lemma mapBase_comp_structureFunctor (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (b : ℬ ⥤ 𝒟)
    (hb : b ⋙ p𝒟 = pℬ) :
    mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb ⋙ structureFunctor pT p𝒜 p𝒟 (G ⋙ b) (F ⋙ b) =
      structureFunctor pT p𝒜 pℬ G F :=
  rfl

/-- **Changing the target of a 2-fibre product over `𝒞` along a fully faithful 1-morphism is an
equivalence**: fullness and faithfulness come from those of `b`, and essential surjectivity from
the preimage under `b` of the comparison isomorphism of an object, which is again vertical.

Full faithfulness of `b` suffices — `b` need not be an equivalence. The objects of the target
2-fibre product carry a comparison isomorphism between objects of the *images* of `G ⋙ b` and
`F ⋙ b`, never between arbitrary objects of `𝒟`, so fullness already produces a preimage for it
and faithfulness makes that preimage an isomorphism; no quasi-inverse is used anywhere.

That generality is what the source's step "since `𝒳 → 𝒴'` factors through the closed substack
`𝒴` we see that `𝒳 ×_𝒴 𝒳 = 𝒳 ×_{𝒴'} 𝒳`" (Stacks 0BPU) needs: there `b` is the inclusion of a
closed substack, which is fully faithful by Stacks 04ZZ but is very far from an equivalence. -/
theorem isEquivalence_mapBase {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟} (hb : b ⋙ p𝒟 = pℬ)
    [b.Full] [b.Faithful] :
    (mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).IsEquivalence := by
  let K := mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb
  have hfaith : K.Faithful := by
    constructor
    intro P Q f g h
    exact TwoFibreProductOver.Hom.ext'
      (by simpa only [K, mapBase] using congrArg TwoFibreProductOver.Hom.a h)
      (by simpa only [K, mapBase] using congrArg TwoFibreProductOver.Hom.b h)
  have hfull : K.Full := by
    constructor
    intro P Q f
    refine ⟨⟨f.hbase, f.a, f.b, f.ha, f.hb, ?_⟩, ?_⟩
    · apply b.map_injective
      simpa only [K, mapBase, Functor.comp_map, Functor.mapIso_hom, Functor.map_comp] using f.w
    · apply TwoFibreProductOver.Hom.ext' <;> rfl
  have hess : K.EssSurj := by
    constructor
    intro Q
    let i : G.obj Q.x ≅ F.obj Q.y := (Functor.FullyFaithful.ofFullyFaithful b).preimageIso Q.iso
    have hi : b.mapIso i = Q.iso :=
      Iso.ext ((Functor.FullyFaithful.ofFullyFaithful b).map_preimage Q.iso.hom)
    have hivert : pℬ.IsHomLift (𝟙 Q.base) i.hom :=
      (Functor.isHomLift_map_iff_of_comp_eq pℬ p𝒟 b hb (𝟙 Q.base) i.hom).1 <| by
        rw [show b.map i.hom = Q.iso.hom from congrArg Iso.hom hi]; exact Q.vertical
    let P : TwoFibreProductOver pT p𝒜 pℬ G F :=
      { base := Q.base, x := Q.x, y := Q.y, hx := Q.hx, hy := Q.hy,
        iso := i, vertical := hivert }
    have hobj : K.obj P = Q := by
      apply TwoFibreProductOver.obj_ext
      simpa [P, K, mapBase] using hi
    exact ⟨P, ⟨eqToIso hobj⟩⟩
  exact { faithful := hfaith, full := hfull, essSurj := hess }

end MapBase

section PrecomposeSnd

variable {𝒜' : Type uA} [Category.{vA} 𝒜'] {𝒜 : Type uB} [Category.{vB} 𝒜]
  {ℬ : Type uD} [Category.{vD} ℬ]
  {pT : T ⥤ 𝒞} {p𝒜' : 𝒜' ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞}

/-- Precomposition of the second leg of a 2-fibre product over `𝒞` with a 1-morphism
`a : 𝒜' ⥤ 𝒜` over `𝒞`: an object `(U, t, x', φ : G t ≅ F (a x'))` of `T ×_{G, ℬ, a ⋙ F} 𝒜'`
is sent to `(U, t, a x', φ)`, an object of `T ×_{G, ℬ, F} 𝒜`. -/
def precomposeSnd (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (a : 𝒜' ⥤ 𝒜) (hA : a ⋙ p𝒜 = p𝒜') :
    TwoFibreProductOver pT p𝒜' pℬ G (a ⋙ F) ⥤ TwoFibreProductOver pT p𝒜 pℬ G F where
  obj P :=
    { base := P.base
      x := P.x
      y := a.obj P.y
      hx := P.hx
      hy := by
        have h := congrArg (fun k : 𝒜' ⥤ 𝒞 => k.obj P.y) hA
        simpa only [Functor.comp_obj] using h.trans P.hy
      iso := P.iso
      vertical := P.vertical }
  map {P Q} f :=
    { hbase := f.hbase
      a := f.a
      b := a.map f.b
      ha := f.ha
      hb := by
        let : p𝒜'.IsHomLift f.hbase f.b := f.hb
        exact Functor.isHomLift_map_of_comp_eq (p := p𝒜') (q := p𝒜) (G := a) hA f.hbase f.b
      w := by simpa only [Functor.comp_map] using f.w }
  map_id P := by apply TwoFibreProductOver.Hom.ext <;> simp
  map_comp f g := by apply TwoFibreProductOver.Hom.ext <;> simp

/-- `precomposeSnd` commutes with the first projection on the nose. -/
@[simp] lemma precomposeSnd_comp_fst (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (a : 𝒜' ⥤ 𝒜)
    (hA : a ⋙ p𝒜 = p𝒜') :
    precomposeSnd (pT := pT) (pℬ := pℬ) G F a hA ⋙ fst pT p𝒜 pℬ G F =
      fst pT p𝒜' pℬ G (a ⋙ F) :=
  rfl

/-- `precomposeSnd` is strictly over `𝒞`: it changes neither the base object of an object nor the
base morphism of a morphism. -/
@[simp] lemma precomposeSnd_comp_structureFunctor (G : T ⥤ ℬ) (F : 𝒜 ⥤ ℬ) (a : 𝒜' ⥤ 𝒜)
    (hA : a ⋙ p𝒜 = p𝒜') :
    precomposeSnd (pT := pT) (pℬ := pℬ) G F a hA ⋙ structureFunctor pT p𝒜 pℬ G F =
      structureFunctor pT p𝒜' pℬ G (a ⋙ F) :=
  rfl

/-- Changing the second factor of a 2-fibre product over `𝒞` along a full and faithful
1-morphism `a` over `𝒞` is an equivalence, as soon as the second component of every object of the
target 2-fibre product is isomorphic, over an identity, to an object in the image of `a`.
Essential surjectivity is where the fibred hypotheses enter: the isomorphism has to be vertical
before it can be absorbed into the comparison isomorphism of the object.

Fullness and faithfulness of `a` are explicit arguments rather than instance ones, for the reason
recorded at `CategoryTheory.TwoFibreProductOver.isEquivalence_precomposeFst`: at a call site the
categories involved are typically total categories of `CategoryTheory.BasedCategory.ofFunctor`,
whose `Category` instance is not the one instance search finds for the same type. -/
theorem isEquivalence_precomposeSnd_of_full_of_faithful {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {a : 𝒜' ⥤ 𝒜}
    (hpT : pT.IsFiberedInGroupoids) (hp𝒜 : p𝒜.IsFiberedInGroupoids) (hA : a ⋙ p𝒜 = p𝒜')
    (hfull : a.Full) (hfaith : a.Faithful) (hF : F ⋙ pℬ = p𝒜)
    (hlift : ∀ P : TwoFibreProductOver pT p𝒜 pℬ G F, ∃ (x' : 𝒜') (_ : p𝒜'.obj x' = p𝒜.obj P.y)
      (e : P.y ≅ a.obj x'), p𝒜.IsHomLift (𝟙 (p𝒜.obj P.y)) e.hom) :
    (precomposeSnd (pT := pT) (pℬ := pℬ) G F a hA).IsEquivalence := by
  have := hfull
  have := hfaith
  let K := precomposeSnd (pT := pT) (pℬ := pℬ) G F a hA
  have hfaith : K.Faithful := by
    constructor
    intro P Q f g h
    exact TwoFibreProductOver.Hom.ext'
      (by simpa only [K, precomposeSnd] using congrArg TwoFibreProductOver.Hom.a h)
      (a.map_injective
        (by simpa only [K, precomposeSnd] using congrArg TwoFibreProductOver.Hom.b h))
  have hfull : K.Full := by
    constructor
    intro P Q f
    obtain ⟨v, hv⟩ := a.map_surjective f.b
    have hvlift : p𝒜'.IsHomLift f.hbase v :=
      (Functor.isHomLift_map_iff_of_comp_eq p𝒜' p𝒜 a hA f.hbase v).1
        (by simpa [K, precomposeSnd, hv] using f.hb)
    refine ⟨⟨f.hbase, f.a, v, f.ha, hvlift, ?_⟩, TwoFibreProductOver.Hom.ext' rfl hv⟩
    simpa [K, precomposeSnd, Functor.comp_map, hv] using f.w
  have hess : K.EssSurj := by
    constructor
    intro P
    obtain ⟨x', hx', e, he⟩ := hlift P
    have heInv : p𝒜.IsHomLift (𝟙 (p𝒜.obj P.y)) e.inv :=
      IsHomLift.lift_id_inv p𝒜 (p𝒜.obj P.y) e
    have hvFe : pℬ.IsHomLift (𝟙 P.base) (F.map e.hom) := by
      rw [← P.hy]
      exact Functor.isHomLift_map_of_comp_eq hF (𝟙 (p𝒜.obj P.y)) e.hom
    have hvIso : pℬ.IsHomLift (𝟙 P.base) ((P.iso ≪≫ F.mapIso e).hom) := by
      have : pℬ.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
      dsimp only [Iso.trans_hom, Functor.mapIso_hom]
      infer_instance
    let Q : TwoFibreProductOver pT p𝒜' pℬ G (a ⋙ F) :=
      { base := P.base, x := P.x, y := x', hx := P.hx,
        hy := hx'.trans P.hy,
        iso := P.iso ≪≫ F.mapIso e, vertical := hvIso }
    let Φ : K.obj Q ⟶ P := by
      dsimp [K, precomposeSnd, Q]
      exact TwoFibreProductOver.Hom.mk' (𝟙 P.x) e.inv (by
          rw [IsHomLift.fac' p𝒜 (𝟙 (p𝒜.obj P.y)) e.inv]
          simp [eqToHom_trans]) (by simp [Category.assoc])
    have hΦ : (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F).IsHomLift (𝟙 P.base) Φ := by
      have hmap : (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F).map Φ = 𝟙 P.base := by
        change eqToHom P.hx.symm ≫ pT.map (𝟙 P.x) ≫ eqToHom P.hx = 𝟙 P.base
        simp
      rw [← hmap]
      exact IsHomLift.map (TwoFibreProductOver.structureFunctor pT p𝒜 pℬ G F) Φ
    have : IsIso Φ := TwoFibreProductOver.isIso_of_isHomLift_id hpT hp𝒜 Φ hΦ
    exact ⟨Q, ⟨asIso Φ⟩⟩
  exact { faithful := hfaith, full := hfull, essSurj := hess }

/-- Changing the second factor of a 2-fibre product over `𝒞` along an equivalence over `𝒞` is
an equivalence: an equivalence between categories fibred in groupoids reaches every object up to a
vertical isomorphism. -/
theorem isEquivalence_precomposeSnd {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {a : 𝒜' ⥤ 𝒜}
    (hpT : pT.IsFiberedInGroupoids) (hp𝒜' : p𝒜'.IsFiberedInGroupoids)
    (hp𝒜 : p𝒜.IsFiberedInGroupoids) (hA : a ⋙ p𝒜 = p𝒜') [Functor.IsEquivalence a]
    (hF : F ⋙ pℬ = p𝒜) :
    (precomposeSnd (pT := pT) (pℬ := pℬ) G F a hA).IsEquivalence :=
  isEquivalence_precomposeSnd_of_full_of_faithful hpT hp𝒜 hA inferInstance inferInstance hF
    fun P =>
    Functor.quasiInverse_choice p𝒜' p𝒜 hp𝒜' hp𝒜 a hA (inferInstance : a.IsEquivalence) P.y

end PrecomposeSnd

end CategoryTheory.TwoFibreProductOver

end
