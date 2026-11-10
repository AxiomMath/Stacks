module

public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningPushoutFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Stack.SingleMorphismDescent

/-!
# Gluing squares of a stack in groupoids, and descent of a local preimage

Let `p : 𝒳 ⥤ 𝒮` be a category fibred in groupoids and let

```
X --i--> X'
|        |
f        a
v        v
Y --b--> Y'
```

be a commutative square of the base. The comparison functor
`Deformation.Artin.fiberSquareComparison` from the fibre over `Y'` to the two-fibre product of the
fibres over `Y` and `X'` over the fibre over `X` is full and faithful exactly when the chosen
cartesian lifts of the square, at every object over `Y'`, form a pushout in `𝒳` relative to `p`:
this is `Deformation.Artin.IsGluingSquare`, and
`Deformation.Artin.isGluingSquare_of_full_of_faithful` is the implication that is used here.

The main result of the file is the local-to-global step of the proof of Stacks 07WN, for a stack in
groupoids over an arbitrary site with fibre products: if the square is a gluing square after base
change along `q : Y'₁ ⟶ Y'` and along the two- and threefold fibre products of `q` with itself,
and `q` generates a covering sieve, then an object of the two-fibre product which, after base
change along `q`, comes from an object over `Y'₁`, comes from an object over `Y'`. The proof
glues the object over `Y'₁` along `q` (Stacks 02ZF, in the form
`CategoryTheory.Functor.exists_descent_of_mem_singleton_sieve`), the descent isomorphism being
obtained from the gluing property over `Y'₁ ×_{Y'} Y'₁` and its cocycle condition from the one
over `Y'₁ ×_{Y'} Y'₁ ×_{Y'} Y'₁`, and then glues the two comparison isomorphisms along the base
changes of `q`.

## Main definitions

* `Deformation.Artin.IsGluingSquare`: the cartesian lifts of a commutative square form a pushout in
  `𝒳` relative to `p`.
* `Deformation.Artin.baseChangeLeft` and `Deformation.Artin.baseChangeTop`: the base changes of the
  two sides out of the corner `X` along a morphism `T ⟶ Y'`, with the corners chosen by
  `CategoryTheory.Limits.pullback`.
* `Deformation.Artin.LocalPreimage`: an object over `Y'₁` whose restrictions to the base changes
  of `Y` and `X'` are identified with those of an object of the two-fibre product, compatibly over
  the base change of `X`.

## Main results

* `Deformation.Artin.isGluingSquare_of_full_of_faithful`: a full and faithful comparison functor
  makes the square a gluing square.
* `Deformation.Artin.mem_essImage_fiberSquareComparison_of_hom`: an object of the two-fibre product
  is in the essential image as soon as both its components map compatibly to one object over
  `Y'`.
* `Deformation.Artin.side_conv`, `Deformation.Artin.side_fwd`, `Deformation.Artin.side_refl` and
  `Deformation.Artin.side_trans`: the descent isomorphism over `Y'₁ ×_{Y'} Y'₁`, read on one side
  of the square, and its reflexivity and transitivity.
* `Deformation.Artin.mem_essImage_fiberSquareComparison_of_localPreimage`: the local-to-global
  step.

## Implementation notes

All the gluing is done with morphisms of the total category `𝒳` lying over morphisms of the base:
a category fibred in groupoids has every morphism cartesian, so a morphism lying over a given
morphism of the base into a given object is unique once its composite with any morphism of `𝒳` is
fixed (`Deformation.Artin.eq_of_comp_eq`) and exists as soon as the bases factor
(`Deformation.Artin.exists_factor`). The chosen pullbacks appear only where the descent of objects
is invoked and where the comparison functor is read.

## References

* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 02ZF](https://stacks.math.columbia.edu/tag/02ZF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Deformation.Artin

-- `Fiber` and its inclusion must unfold for the endpoints of the composites below to be seen as
-- equal at `implicit` transparency.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-! ### Factorizations in a category fibred in groupoids -/

section Factor

variable {p : 𝒳 ⥤ 𝒮} (hgpd : p.IsFiberedInGroupoids)
include hgpd

/-- In a category fibred in groupoids every morphism over `g ≫ f` into the target of a morphism
over `f` factors through it by a morphism over `g`. -/
lemma exists_factor {R R' S : 𝒮} {a b t : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
    (ψ : t ⟶ b) (f' : R' ⟶ S) [p.IsHomLift f' ψ] (g : R' ⟶ R) (h : f' = g ≫ f) :
    ∃ χ : t ⟶ a, p.IsHomLift g χ ∧ χ ≫ φ = ψ := by
  have := hgpd.isStronglyCartesian_homLift f φ
  exact ⟨IsStronglyCartesian.map p f φ h ψ, inferInstance, IsStronglyCartesian.fac p f φ h ψ⟩

/-- In a category fibred in groupoids two morphisms over one and the same morphism of the base
which agree after a morphism of `𝒳` are equal. -/
lemma eq_of_comp_eq {R R' S : 𝒮} {a b t : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ]
    (g : R' ⟶ R) {χ χ' : t ⟶ a} [p.IsHomLift g χ] [p.IsHomLift g χ'] (h : χ ≫ φ = χ' ≫ φ) :
    χ = χ' := by
  have := hgpd.isStronglyCartesian_homLift f φ
  exact IsStronglyCartesian.ext p f φ g h

end Factor

/-- Transport of a lift along an equality of morphisms of the base. -/
lemma isHomLift_of_eq {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f f' : R ⟶ S} (φ : a ⟶ b)
    [p.IsHomLift f φ] (h : f = f') : p.IsHomLift f' φ :=
  h ▸ inferInstance

/-! ### Gluing squares -/

section GluingSquare

variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
variable {X X' Y Y' : 𝒮} (f : X ⟶ Y) (i : X ⟶ X') (b : Y ⟶ Y') (a : X' ⟶ Y')

/-- The cartesian lifts of the commutative square `f ≫ b = i ≫ a` form a pushout in `𝒳` relative
to `p`: for strongly cartesian morphisms `r : B ⟶ z` over `b` and `s : C ⟶ z` over `a`, a pair of
morphisms out of `B` and `C`, lying over `b ≫ g` and `a ≫ g` and agreeing on every common lift of
the corner `X`, comes from a unique morphism out of `z` lying over `g`. -/
structure IsGluingSquare : Prop where
  /-- Existence of the glued morphism. -/
  exists_desc : ∀ {z B C t : 𝒳} {W : 𝒮} (r : B ⟶ z) (s : C ⟶ z) (g : Y' ⟶ W) (mY : B ⟶ t)
    (mX' : C ⟶ t), p.IsStronglyCartesian b r → p.IsStronglyCartesian a s →
    p.IsHomLift (b ≫ g) mY → p.IsHomLift (a ≫ g) mX' →
    (∀ {D : 𝒳} (uX : D ⟶ B) (vX : D ⟶ C), p.IsHomLift f uX → p.IsHomLift i vX →
      uX ≫ r = vX ≫ s → uX ≫ mY = vX ≫ mX') →
    ∃ m : z ⟶ t, p.IsHomLift g m ∧ r ≫ m = mY ∧ s ≫ m = mX'
  /-- Uniqueness of the glued morphism. -/
  hom_ext : ∀ {z B C t : 𝒳} {W : 𝒮} (r : B ⟶ z) (s : C ⟶ z) (g : Y' ⟶ W) (α β : z ⟶ t),
    p.IsStronglyCartesian b r → p.IsStronglyCartesian a s → p.IsHomLift g α → p.IsHomLift g β →
    r ≫ α = r ≫ β → s ≫ α = s ≫ β → α = β

variable {p f i b a}

/-- The composite of the chosen cartesian lifts of `b` and `g` is strongly cartesian over `b ≫ g`.
-/
lemma isStronglyCartesian_pullbackMap_comp {W : 𝒮} (g : Y' ⟶ W) (t : p.Fiber W) :
    p.IsStronglyCartesian (b ≫ g)
      (IsPreFibered.pullbackMap (pullbackFiber p t g).2 b ≫ IsPreFibered.pullbackMap t.2 g) :=
  have : p.IsStronglyCartesian b (IsPreFibered.pullbackMap (pullbackFiber p t g).2 b) :=
    inferInstance
  have : p.IsStronglyCartesian g (IsPreFibered.pullbackMap t.2 g) := inferInstance
  IsStronglyCartesian.comp p (f := b) (g := g)
    (φ := IsPreFibered.pullbackMap (pullbackFiber p t g).2 b)
    (ψ := IsPreFibered.pullbackMap t.2 g)

/-- A strongly cartesian morphism over `k` into an object `z` factors through the chosen
cartesian lift of `k` at `z` by an isomorphism lying over an identity. -/
lemma exists_iso_pullbackMap {U V : 𝒮} (k : V ⟶ U) (z : p.Fiber U) {B : 𝒳} (r : B ⟶ z.1)
    [p.IsStronglyCartesian k r] :
    ∃ j : (pullbackFiber p z k).1 ⟶ B, IsIso j ∧ p.IsHomLift (𝟙 V) j ∧
      j ≫ r = IsPreFibered.pullbackMap z.2 k := by
  let j := IsStronglyCartesian.map p k r (f' := k) (g := 𝟙 V) (Category.id_comp k).symm
    (IsPreFibered.pullbackMap z.2 k)
  have hj : j ≫ r = IsPreFibered.pullbackMap z.2 k := IsStronglyCartesian.fac p k r _ _
  have : p.IsStronglyCartesian (𝟙 V) j := by
    have : p.IsStronglyCartesian (𝟙 V ≫ k) (j ≫ r) := by
      rw [hj, Category.id_comp]
      infer_instance
    exact IsStronglyCartesian.of_comp p (f := 𝟙 V) (g := k) (φ := j) (ψ := r)
  exact ⟨j, IsStronglyCartesian.isIso_of_base_isIso p (𝟙 V) j, inferInstance, hj⟩

omit [p.IsFibered] in
/-- A morphism lying over `k` from an object of the fibre over `U` into the target of a strongly
cartesian morphism over `k` out of another object of that fibre factors through it by a morphism of
the fibre. -/
private lemma exists_fiber_hom_comp_eq {U W : 𝒮} (k : U ⟶ W) (z w : p.Fiber U) {t : 𝒳} (ψ : w.1 ⟶ t)
    [p.IsStronglyCartesian k ψ] (α : z.1 ⟶ t) [p.IsHomLift k α] :
    ∃ α' : z ⟶ w, Fiber.fiberInclusion.map α' ≫ ψ = α :=
  ⟨⟨IsStronglyCartesian.map p k ψ (f' := k) (g := 𝟙 U) (Category.id_comp k).symm α, inferInstance⟩,
    IsStronglyCartesian.fac p k ψ (f' := k) (g := 𝟙 U) (Category.id_comp k).symm α⟩

/-- A full comparison functor lifts a pair of morphisms of the fibres over `Y` and `X'`, compatible
through the structure isomorphisms over `X`, to a morphism of the fibre over `Y'`. -/
private lemma exists_hom_of_full (w : f ≫ b = i ≫ a)
    [(fiberSquareComparison p p.chosenPullbacks f i b a w).Full] {z t : p.Fiber Y'}
    (u : pullbackFiber p z b ⟶ pullbackFiber p t b) (v : pullbackFiber p z a ⟶ pullbackFiber p t a)
    (huv : pullbackFiberHom u f ≫
        ((fiberSquareComparison p p.chosenPullbacks f i b a w).obj t).iso.hom =
      ((fiberSquareComparison p p.chosenPullbacks f i b a w).obj z).iso.hom ≫
        pullbackFiberHom v i) :
    ∃ m : z ⟶ t, pullbackFiberHom m b = u ∧ pullbackFiberHom m a = v := by
  let ψ : (fiberSquareComparison p p.chosenPullbacks f i b a w).obj z ⟶
      (fiberSquareComparison p p.chosenPullbacks f i b a w).obj t :=
    { fst := u
      snd := v
      w := by
        change p.chosenPullbacks.homMap f u ≫ _ = _ ≫ p.chosenPullbacks.homMap i v
        rw [chosenPullbacks_homMap, chosenPullbacks_homMap]
        exact huv }
  have hm := (fiberSquareComparison p p.chosenPullbacks f i b a w).map_preimage ψ
  exact ⟨_, (chosenPullbacks_homMap p b _).symm.trans (congrArg CategoricalPullback.Hom.fst hm),
    (chosenPullbacks_homMap p a _).symm.trans (congrArg CategoricalPullback.Hom.snd hm)⟩

/-- If the comparison functor of the square is full, the cartesian lifts of the square have the
existence property of `Deformation.Artin.IsGluingSquare`. -/
private lemma exists_desc_of_full (w : f ≫ b = i ≫ a)
    [(fiberSquareComparison p p.chosenPullbacks f i b a w).Full] {z B C t : 𝒳} {W : 𝒮}
    (r : B ⟶ z) (s : C ⟶ z) (g : Y' ⟶ W) (mY : B ⟶ t) (mX' : C ⟶ t)
    [p.IsStronglyCartesian b r] [p.IsStronglyCartesian a s] [p.IsHomLift (b ≫ g) mY]
    [p.IsHomLift (a ≫ g) mX']
    (hm : ∀ {D : 𝒳} (uX : D ⟶ B) (vX : D ⟶ C), p.IsHomLift f uX → p.IsHomLift i vX →
      uX ≫ r = vX ≫ s → uX ≫ mY = vX ≫ mX') :
    ∃ m : z ⟶ t, p.IsHomLift g m ∧ r ≫ m = mY ∧ s ≫ m = mX' := by
  let φ : ∀ z : p.Fiber Y', pullbackFiber p (pullbackFiber p z b) f ⟶
      pullbackFiber p (pullbackFiber p z a) i :=
    fun z => ((fiberSquareComparison p p.chosenPullbacks f i b a w).obj z).iso.hom
  have hiso : ∀ z : p.Fiber Y', Fiber.fiberInclusion.map (φ z) ≫
      IsPreFibered.pullbackMap (pullbackFiber p z a).2 i ≫ IsPreFibered.pullbackMap z.2 a =
      IsPreFibered.pullbackMap (pullbackFiber p z b).2 f ≫ IsPreFibered.pullbackMap z.2 b :=
    fun z => AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_iso_fac p f i b a w z
  have hz : p.obj z = Y' := IsHomLift.codomain_eq p b r
  let z' : p.Fiber Y' := ⟨z, hz⟩
  obtain ⟨jr, hjr, hjrl, hjr'⟩ := exists_iso_pullbackMap b z' r
  obtain ⟨js, hjs, hjsl, hjs'⟩ := exists_iso_pullbackMap a z' s
  have ht : p.obj t = W := IsHomLift.codomain_eq p (b ≫ g) mY
  let t' : p.Fiber W := ⟨t, ht⟩
  let tg := pullbackFiber p t' g
  have hcb := isStronglyCartesian_pullbackMap_comp (b := b) g t'
  have hca := isStronglyCartesian_pullbackMap_comp (b := a) g t'
  obtain ⟨mY', hmY'⟩ := exists_fiber_hom_comp_eq (b ≫ g) (pullbackFiber p z' b)
    (pullbackFiber p tg b) (IsPreFibered.pullbackMap tg.2 b ≫ IsPreFibered.pullbackMap t'.2 g)
    (jr ≫ mY)
  obtain ⟨mX'', hmX''⟩ := exists_fiber_hom_comp_eq (a ≫ g) (pullbackFiber p z' a)
    (pullbackFiber p tg a) (IsPreFibered.pullbackMap tg.2 a ≫ IsPreFibered.pullbackMap t'.2 g)
    (js ≫ mX')
  have : p.IsHomLift (𝟙 X) (Fiber.fiberInclusion.map (φ z')) := (φ z').2
  have hcorner : IsPreFibered.pullbackMap (pullbackFiber p z' b).2 f ≫ jr ≫ mY =
      Fiber.fiberInclusion.map (φ z') ≫
        IsPreFibered.pullbackMap (pullbackFiber p z' a).2 i ≫ js ≫ mX' := by
    simpa only [Category.assoc] using
      hm (IsPreFibered.pullbackMap (pullbackFiber p z' b).2 f ≫ jr)
        (Fiber.fiberInclusion.map (φ z') ≫
          IsPreFibered.pullbackMap (pullbackFiber p z' a).2 i ≫ js) inferInstance
        inferInstance (by rw [Category.assoc, Category.assoc, Category.assoc, hjr', hjs',
          hiso z'])
  have hcart : p.IsStronglyCartesian (i ≫ a ≫ g)
      (IsPreFibered.pullbackMap (pullbackFiber p tg a).2 i ≫
        IsPreFibered.pullbackMap tg.2 a ≫ IsPreFibered.pullbackMap t'.2 g) :=
    IsStronglyCartesian.comp p (f := i) (g := a ≫ g)
      (φ := IsPreFibered.pullbackMap (pullbackFiber p tg a).2 i)
      (ψ := IsPreFibered.pullbackMap tg.2 a ≫ IsPreFibered.pullbackMap t'.2 g)
  have hw : pullbackFiberHom mY' f ≫ φ tg = φ z' ≫ pullbackFiberHom mX'' i := by
    refine fiber_hom_ext_of_cartesian (i ≫ a ≫ g)
      (IsPreFibered.pullbackMap (pullbackFiber p tg a).2 i ≫
        IsPreFibered.pullbackMap tg.2 a ≫ IsPreFibered.pullbackMap t'.2 g) inferInstance _ _ ?_
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hiso tg), pullbackFiberHom_fac_assoc, pullbackFiberHom_fac_assoc,
      hmY', hmX'', hcorner]
  obtain ⟨m₀, hm₀b, hm₀a⟩ := exists_hom_of_full w mY' mX'' hw
  refine ⟨Fiber.fiberInclusion.map m₀ ≫ IsPreFibered.pullbackMap t'.2 g, inferInstance, ?_, ?_⟩
  · have e := pullbackFiberHom_fac_assoc m₀ b (IsPreFibered.pullbackMap t'.2 g)
    rw [hm₀b, hmY'] at e
    rw [← cancel_epi jr, reassoc_of% hjr', ← e]
  · have e := pullbackFiberHom_fac_assoc m₀ a (IsPreFibered.pullbackMap t'.2 g)
    rw [hm₀a, hmX''] at e
    rw [← cancel_epi js, reassoc_of% hjs', ← e]

/-- If the comparison functor of the square is faithful, the cartesian lifts of the square have the
uniqueness property of `Deformation.Artin.IsGluingSquare`. -/
private lemma hom_ext_of_faithful_fiberSquareComparison (w : f ≫ b = i ≫ a)
    [(fiberSquareComparison p p.chosenPullbacks f i b a w).Faithful] {z B C t : 𝒳} {W : 𝒮}
    (r : B ⟶ z) (s : C ⟶ z) (g : Y' ⟶ W) (α β : z ⟶ t) [p.IsStronglyCartesian b r]
    [p.IsStronglyCartesian a s] [p.IsHomLift g α] [p.IsHomLift g β] (hb : r ≫ α = r ≫ β)
    (ha : s ≫ α = s ≫ β) : α = β := by
  have hz : p.obj z = Y' := IsHomLift.codomain_eq p b r
  let z' : p.Fiber Y' := ⟨z, hz⟩
  obtain ⟨jr, hjr, hjrl, hjr'⟩ := exists_iso_pullbackMap b z' r
  obtain ⟨js, hjs, hjsl, hjs'⟩ := exists_iso_pullbackMap a z' s
  have ht : p.obj t = W := IsHomLift.codomain_eq p g α
  let t' : p.Fiber W := ⟨t, ht⟩
  obtain ⟨α', hα'⟩ := exists_fiber_hom_comp_eq g z' (pullbackFiber p t' g)
    (IsPreFibered.pullbackMap t'.2 g) α
  obtain ⟨β', hβ'⟩ := exists_fiber_hom_comp_eq g z' (pullbackFiber p t' g)
    (IsPreFibered.pullbackMap t'.2 g) β
  have hcb := isStronglyCartesian_pullbackMap_comp (b := b) g t'
  have hca := isStronglyCartesian_pullbackMap_comp (b := a) g t'
  have h₁ : pullbackFiberHom α' b = pullbackFiberHom β' b :=
    fiber_hom_ext_of_cartesian (b ≫ g) (IsPreFibered.pullbackMap (pullbackFiber p t' g).2 b ≫
      IsPreFibered.pullbackMap t'.2 g) inferInstance _ _ (by
      rw [pullbackFiberHom_fac_assoc, pullbackFiberHom_fac_assoc, hα', hβ', ← hjr',
        Category.assoc, Category.assoc, hb])
  have h₂ : pullbackFiberHom α' a = pullbackFiberHom β' a :=
    fiber_hom_ext_of_cartesian (a ≫ g) (IsPreFibered.pullbackMap (pullbackFiber p t' g).2 a ≫
      IsPreFibered.pullbackMap t'.2 g) inferInstance _ _ (by
      rw [pullbackFiberHom_fac_assoc, pullbackFiberHom_fac_assoc, hα', hβ', ← hjs',
        Category.assoc, Category.assoc, ha])
  have : (fiberSquareComparison p p.chosenPullbacks f i b a w).map α' =
      (fiberSquareComparison p p.chosenPullbacks f i b a w).map β' :=
    CategoricalPullback.hom_ext ((chosenPullbacks_homMap p b α').trans
      (h₁.trans (chosenPullbacks_homMap p b β').symm))
      ((chosenPullbacks_homMap p a α').trans (h₂.trans (chosenPullbacks_homMap p a β').symm))
  rw [← hα', ← hβ', (fiberSquareComparison p p.chosenPullbacks f i b a w).map_injective this]

variable (p f i b a) in
/-- **A full and faithful comparison functor makes a gluing square.** If the comparison functor of
the square, from the fibre over `Y'` to the two-fibre product of the fibres over `Y` and `X'`, is
full and faithful, then the cartesian lifts of the square form a pushout in `𝒳` relative to `p`.
-/
theorem isGluingSquare_of_full_of_faithful (w : f ≫ b = i ≫ a)
    (hF : (fiberSquareComparison p p.chosenPullbacks f i b a w).Full ∧
      (fiberSquareComparison p p.chosenPullbacks f i b a w).Faithful) :
    IsGluingSquare p f i b a := by
  obtain ⟨_, _⟩ := hF
  exact ⟨fun r s g mY mX' _ _ _ _ hm => exists_desc_of_full (p := p) w r s g mY mX' hm,
    fun r s g α β _ _ _ _ hb ha =>
      hom_ext_of_faithful_fiberSquareComparison (p := p) w r s g α β hb ha⟩

end GluingSquare

/-! ### Objects of the essential image -/

section EssImage

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered]
variable {X X' Y Y' : 𝒮} {f : X ⟶ Y} {i : X ⟶ X'} {b : Y ⟶ Y'} {a : X' ⟶ Y'}

/-- An object `e` of the two-fibre product lies in the essential image of the comparison functor as
soon as there are an object `y` over `Y'` and morphisms from the two components of `e` to `y`,
lying over `b` and `a`, which agree on the corner `X` through the structure isomorphism of `e`. -/
lemma mem_essImage_fiberSquareComparison_of_hom (hgpd : p.IsFiberedInGroupoids)
    (w : f ≫ b = i ≫ a)
    (e : CategoricalPullback (p.chosenPullbacks.pullbackFunctor f)
      (p.chosenPullbacks.pullbackFunctor i))
    (y : p.Fiber Y') (uY : e.fst.1 ⟶ y.1) (uX' : e.snd.1 ⟶ y.1) [p.IsHomLift b uY]
    [p.IsHomLift a uX']
    (h : p.chosenPullbacks.map f e.fst ≫ uY =
      (Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd) ≫ uX') :
    (fiberSquareComparison p p.chosenPullbacks f i b a w).essImage e := by
  have := hgpd.isStronglyCartesian_homLift b uY
  have := hgpd.isStronglyCartesian_homLift a uX'
  let αY : e.fst ≅ p.chosenPullbacks.obj b y :=
    fiberIsoOfCartesian b uY (p.chosenPullbacks.map b y) inferInstance inferInstance
  let αX : e.snd ≅ p.chosenPullbacks.obj a y :=
    fiberIsoOfCartesian a uX' (p.chosenPullbacks.map a y) inferInstance inferInstance
  have hαY : Fiber.fiberInclusion.map αY.hom ≫ p.chosenPullbacks.map b y = uY :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hαX : Fiber.fiberInclusion.map αX.hom ≫ p.chosenPullbacks.map a y = uX' :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hiso := AlgebraicGeometry.Stack.ThickeningPushout.fiberSquareComparison_iso_fac p f i b a w y
  have hcart : p.IsStronglyCartesian (i ≫ a)
      (p.chosenPullbacks.map i (p.chosenPullbacks.obj a y) ≫ p.chosenPullbacks.map a y) :=
    IsStronglyCartesian.comp p (f := i) (g := a)
      (φ := p.chosenPullbacks.map i (p.chosenPullbacks.obj a y)) (ψ := p.chosenPullbacks.map a y)
  let φy : p.chosenPullbacks.obj f (p.chosenPullbacks.obj b y) ⟶
      p.chosenPullbacks.obj i (p.chosenPullbacks.obj a y) :=
    ((fiberSquareComparison p p.chosenPullbacks f i b a w).obj y).iso.hom
  have hiso' : Fiber.fiberInclusion.map φy ≫ p.chosenPullbacks.map i (p.chosenPullbacks.obj a y) ≫
      p.chosenPullbacks.map a y =
      p.chosenPullbacks.map f (p.chosenPullbacks.obj b y) ≫ p.chosenPullbacks.map b y := hiso
  let ε : p.chosenPullbacks.obj f e.fst ⟶ p.chosenPullbacks.obj i e.snd := e.iso.hom
  have h' : p.chosenPullbacks.map f e.fst ≫ uY =
      (Fiber.fiberInclusion.map ε ≫ p.chosenPullbacks.map i e.snd) ≫ uX' := h
  have key : p.chosenPullbacks.homMap f αY.hom ≫ φy =
      ε ≫ p.chosenPullbacks.homMap i αX.hom := by
    refine fiber_hom_ext_of_cartesian (i ≫ a)
      (p.chosenPullbacks.map i (p.chosenPullbacks.obj a y) ≫ p.chosenPullbacks.map a y)
      inferInstance _ _ ?_
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hiso',
      p.chosenPullbacks.homMap_fac_assoc, hαY, p.chosenPullbacks.homMap_fac_assoc, hαX, h',
      Category.assoc]
  exact ⟨y, ⟨(CategoricalPullback.mkIso αY αX key).symm⟩⟩

end EssImage

/-! ### Base change of a square, and local preimages -/

section BaseChange

variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered]
variable [HasPullbacks 𝒮] {X X' Y Y' : 𝒮} (f : X ⟶ Y) (i : X ⟶ X') (b : Y ⟶ Y') (a : X' ⟶ Y')

/-- The base change `X ×_{Y'} T ⟶ Y ×_{Y'} T` of `f` along `t : T ⟶ Y'`. -/
noncomputable abbrev baseChangeLeft {T : 𝒮} (t : T ⟶ Y') : pullback (f ≫ b) t ⟶ pullback b t :=
  pullback.lift (pullback.fst _ _ ≫ f) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

/-- The base change `X ×_{Y'} T ⟶ X' ×_{Y'} T` of `i` along `t : T ⟶ Y'`. -/
noncomputable abbrev baseChangeTop (w : f ≫ b = i ≫ a) {T : 𝒮} (t : T ⟶ Y') :
    pullback (f ≫ b) t ⟶ pullback a t :=
  pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
    (by rw [Category.assoc, ← w, pullback.condition])

variable (p : 𝒳 ⥤ 𝒮) [p.IsFibered]

/-- A *local preimage* of an object `e` of the two-fibre product along `q : Y'₁ ⟶ Y'`: an object
`obj` over `Y'₁` together with identifications of its restrictions to `Y₁ = Y ×_{Y'} Y'₁` and
`X'₁ = X' ×_{Y'} Y'₁` with the restrictions of the two components of `e`, compatible over
`X₁ = X ×_{Y'} Y'₁` with the structure isomorphism of `e`.

Each identification is recorded as a span of morphisms of `𝒳`: an object `zY` over `Y₁` with
morphisms to `obj` and to `e.fst` lying over the two projections of `Y₁`, and similarly over
`X'₁`; since the category is fibred in groupoids, every morphism lying over a given morphism of
the base is cartesian, so such a span is the same thing as an isomorphism between the two
restrictions. The compatibility over `X₁` is a common restriction `zX` of the two spans whose two
images in `obj` agree, and whose two images in the components of `e` agree through the
structure isomorphism of `e`. -/
structure LocalPreimage (w : f ≫ b = i ≫ a)
    (e : CategoricalPullback (p.chosenPullbacks.pullbackFunctor f)
      (p.chosenPullbacks.pullbackFunctor i))
    {Y'₁ : 𝒮} (q : Y'₁ ⟶ Y') where
  /-- The object over `Y'₁`. -/
  obj : p.Fiber Y'₁
  /-- The common restriction of `obj` and `e.fst` to `Y ×_{Y'} Y'₁`. -/
  zY : 𝒳
  /-- The common restriction of `obj` and `e.snd` to `X' ×_{Y'} Y'₁`. -/
  zX' : 𝒳
  /-- The common restriction to `X ×_{Y'} Y'₁`. -/
  zX : 𝒳
  /-- The restriction morphism from `zY` to `obj`. -/
  sY : zY ⟶ obj.1
  /-- The restriction morphism from `zY` to `e.fst`. -/
  tY : zY ⟶ e.fst.1
  /-- The restriction morphism from `zX'` to `obj`. -/
  sX' : zX' ⟶ obj.1
  /-- The restriction morphism from `zX'` to `e.snd`. -/
  tX' : zX' ⟶ e.snd.1
  /-- The restriction morphism from `zX` to `zY`. -/
  lY : zX ⟶ zY
  /-- The restriction morphism from `zX` to `zX'`. -/
  lX' : zX ⟶ zX'
  /-- The restriction morphism from `zX` to the chosen pullback of `e.fst` to `X`. -/
  lam : zX ⟶ (p.chosenPullbacks.obj f e.fst).1
  isHomLift_sY : p.IsHomLift (pullback.snd b q) sY
  isHomLift_tY : p.IsHomLift (pullback.fst b q) tY
  isHomLift_sX' : p.IsHomLift (pullback.snd a q) sX'
  isHomLift_tX' : p.IsHomLift (pullback.fst a q) tX'
  isHomLift_lY : p.IsHomLift (baseChangeLeft f b q) lY
  isHomLift_lX' : p.IsHomLift (baseChangeTop f i b a w q) lX'
  isHomLift_lam : p.IsHomLift (pullback.fst (f ≫ b) q) lam
  /-- The two images of `zX` in `obj` agree. -/
  lY_sY : lY ≫ sY = lX' ≫ sX'
  /-- `lam` is the restriction of `lY ≫ tY` to the chosen pullback of `e.fst`. -/
  lam_map : lam ≫ p.chosenPullbacks.map f e.fst = lY ≫ tY
  /-- The two images of `zX` in the components of `e` agree through the structure isomorphism. -/
  lam_iso : lam ≫ Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd = lX' ≫ tX'

attribute [instance] LocalPreimage.isHomLift_sY LocalPreimage.isHomLift_tY
  LocalPreimage.isHomLift_sX' LocalPreimage.isHomLift_tX' LocalPreimage.isHomLift_lY
  LocalPreimage.isHomLift_lX' LocalPreimage.isHomLift_lam

end BaseChange

/-! ### The descent isomorphism, on one side of the square -/

section Side

variable [HasPullbacks 𝒮] {p : 𝒳 ⥤ 𝒮} {Y Y' Y'₁ : 𝒮} (b : Y ⟶ Y') (q : Y'₁ ⟶ Y')

/-- The two morphisms `Y ×_{Y'} (Y'₁ ×_{Y'} Y'₁) ⟶ Y ×_{Y'} Y'₁` induced by the two projections
of `Y'₁ ×_{Y'} Y'₁`; `k = 1` is the first and `k = 2` the second. -/
noncomputable abbrev sideMap₁ : pullback b (pullback.fst q q ≫ q) ⟶ pullback b q :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst q q)
    (pullback.condition.trans (Category.assoc _ _ _).symm)

/-- See `Deformation.Artin.sideMap₁`. -/
noncomputable abbrev sideMap₂ : pullback b (pullback.fst q q ≫ q) ⟶ pullback b q :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd q q)
    (pullback.condition.trans (by simp only [Category.assoc, pullback.condition (f := q) (g := q)]))

variable {b q}

omit [HasPullbacks 𝒮] in
/-- Two lifts of one morphism lie over one and the same morphism of the base. -/
lemma base_eq_of_isHomLift_of_isHomLift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {x x' : 𝒳} {φ : x ⟶ x'} {f f' : R ⟶ S}
    (_ : p.IsHomLift f φ) (_ : p.IsHomLift f' φ) : f = f' := by
  rw [IsHomLift.fac p f φ, IsHomLift.fac p f' φ]

/-- **The descent relation on one side of the square, from left to right.** Fix the data of a
side `Y` of the square: an object `η` over `Y'₁`, and a span `η ← zY → yY` over the two projections
of `Y ×_{Y'} Y'₁` identifying the restrictions of `η` and of `yY`. Let `d₁, d₂ : P ⟶ η` lie over
the two projections of `Y'₁ ×_{Y'} Y'₁`, and suppose that, restricted along a strongly cartesian
`r₁` to `Y ×_{Y'} (Y'₁ ×_{Y'} Y'₁)`, the pair `(d₁, d₂)` is the pair of morphisms which
corresponds, through the span, to the identity of the restriction of `yY`. Then every morphism
`n` into `P` sends two factorizations `β`, `β'` through `zY` of `n ≫ d₁` and `n ≫ d₂`, lying over
morphisms with the same image in `Y`, to the same morphism into `yY`. -/
lemma side_conv (hgpd : p.IsFiberedInGroupoids) {η : p.Fiber Y'₁} {zY yY : 𝒳} (sY : zY ⟶ η.1)
    (tY : zY ⟶ yY) [p.IsHomLift (pullback.snd b q) sY] [p.IsHomLift (pullback.fst b q) tY]
    {P : 𝒳} (d₁ d₂ : P ⟶ η.1) [p.IsHomLift (pullback.fst q q) d₁]
    [p.IsHomLift (pullback.snd q q) d₂] {B₁ : 𝒳} (r₁ : B₁ ⟶ P)
    [p.IsHomLift (pullback.snd b (pullback.fst q q ≫ q)) r₁] (ω₁ ω₂ : B₁ ⟶ zY)
    [p.IsHomLift (sideMap₁ b q) ω₁] [p.IsHomLift (sideMap₂ b q) ω₂]
    (hω₁ : ω₁ ≫ sY = r₁ ≫ d₁) (hω₂ : ω₂ ≫ sY = r₁ ≫ d₂) (hω : ω₁ ≫ tY = ω₂ ≫ tY)
    {Z : 𝒮} {B : 𝒳} (kn : Z ⟶ pullback q q) (h h' : Z ⟶ pullback b q) (n : B ⟶ P)
    (β β' : B ⟶ zY) [p.IsHomLift kn n] [p.IsHomLift h β] [p.IsHomLift h' β']
    (hh : h ≫ pullback.fst b q = h' ≫ pullback.fst b q) (hβ : β ≫ sY = n ≫ d₁)
    (hβ' : β' ≫ sY = n ≫ d₂) :
    β ≫ tY = β' ≫ tY := by
  have hk₁ : kn ≫ pullback.fst q q = h ≫ pullback.snd b q := by
    have h₀ : p.IsHomLift (h ≫ pullback.snd b q) (n ≫ d₁) := by rw [← hβ]; infer_instance
    exact base_eq_of_isHomLift_of_isHomLift (φ := n ≫ d₁) inferInstance h₀
  have hk₂ : kn ≫ pullback.snd q q = h' ≫ pullback.snd b q := by
    have h₀ : p.IsHomLift (h' ≫ pullback.snd b q) (n ≫ d₂) := by rw [← hβ']; infer_instance
    exact base_eq_of_isHomLift_of_isHomLift (φ := n ≫ d₂) inferInstance h₀
  let l : Z ⟶ pullback b (pullback.fst q q ≫ q) := pullback.lift (h ≫ pullback.fst b q) kn (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hk₁, Category.assoc])
  have hl₁ : l ≫ sideMap₁ b q = h := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hk₁]
  have hl₂ : l ≫ sideMap₂ b q = h' := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hh]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hk₂]
  obtain ⟨ñ, hñ, hñn⟩ := exists_factor hgpd (pullback.snd b (pullback.fst q q ≫ q)) r₁ n kn l
    (pullback.lift_snd _ _ _).symm
  have h₁ : ñ ≫ ω₁ = β := by
    have : p.IsHomLift h (ñ ≫ ω₁) := isHomLift_of_eq _ hl₁
    refine eq_of_comp_eq hgpd (pullback.snd b q) sY h ?_
    rw [Category.assoc, hω₁, reassoc_of% hñn, hβ]
  have h₂ : ñ ≫ ω₂ = β' := by
    have : p.IsHomLift h' (ñ ≫ ω₂) := isHomLift_of_eq _ hl₂
    refine eq_of_comp_eq hgpd (pullback.snd b q) sY h' ?_
    rw [Category.assoc, hω₂, reassoc_of% hñn, hβ']
  rw [← h₁, ← h₂, Category.assoc, hω, Category.assoc]

/-- **The descent relation on one side of the square, from right to left.** In the situation of
`Deformation.Artin.side_conv`, two morphisms `β`, `β'` into `zY`, lying over morphisms with the
same image in `Y` and agreeing in `yY`, are the two components `n ≫ d₁` and `n ≫ d₂` of one
morphism `n` into `P`, after composing with `zY ⟶ η`. -/
lemma side_fwd (hgpd : p.IsFiberedInGroupoids) {η : p.Fiber Y'₁} {zY yY : 𝒳} (sY : zY ⟶ η.1)
    (tY : zY ⟶ yY) [p.IsHomLift (pullback.snd b q) sY] [p.IsHomLift (pullback.fst b q) tY]
    {P : 𝒳} (d₁ d₂ : P ⟶ η.1) [p.IsHomLift (pullback.fst q q) d₁]
    [p.IsHomLift (pullback.snd q q) d₂] {B₁ : 𝒳} (r₁ : B₁ ⟶ P)
    [p.IsHomLift (pullback.snd b (pullback.fst q q ≫ q)) r₁] (ω₁ ω₂ : B₁ ⟶ zY)
    [p.IsHomLift (sideMap₁ b q) ω₁] [p.IsHomLift (sideMap₂ b q) ω₂]
    (hω₁ : ω₁ ≫ sY = r₁ ≫ d₁) (hω₂ : ω₂ ≫ sY = r₁ ≫ d₂) (hω : ω₁ ≫ tY = ω₂ ≫ tY)
    {Z : 𝒮} {B : 𝒳} (h h' : Z ⟶ pullback b q) (β β' : B ⟶ zY) [p.IsHomLift h β]
    [p.IsHomLift h' β'] (hh : h ≫ pullback.fst b q = h' ≫ pullback.fst b q)
    (ht : β ≫ tY = β' ≫ tY) :
    ∃ n : B ⟶ P, n ≫ d₁ = β ≫ sY ∧ n ≫ d₂ = β' ≫ sY := by
  let kn : Z ⟶ pullback q q := pullback.lift (h ≫ pullback.snd b q) (h' ≫ pullback.snd b q) (by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hh])
  obtain ⟨n, hn, hnd⟩ := exists_factor hgpd (pullback.fst q q) d₁ (β ≫ sY)
    (h ≫ pullback.snd b q) kn (pullback.lift_fst _ _ _).symm
  obtain ⟨β'', hβ'', hβ''n⟩ := exists_factor hgpd (pullback.snd b q) sY (n ≫ d₂)
    (kn ≫ pullback.snd q q) h' (pullback.lift_snd _ _ _)
  have hc := side_conv hgpd sY tY d₁ d₂ r₁ ω₁ ω₂ hω₁ hω₂ hω kn h h' n β β'' hh hnd.symm hβ''n
  have : β'' = β' := eq_of_comp_eq hgpd (pullback.fst b q) tY h' (hc.symm.trans ht)
  exact ⟨n, hnd, by rw [← hβ''n, this]⟩

/-- **Reflexivity on one side.** In the situation of `Deformation.Artin.side_conv`, let `s : A ⟶ P`
lie over a section of the diagonal of `Y'₁ ×_{Y'} Y'₁`, so that `s ≫ d₁` and `s ≫ d₂` both lie over
the identity of `Y'₁`. Then they agree after restriction to `Y ×_{Y'} Y'₁`. -/
lemma side_refl (hgpd : p.IsFiberedInGroupoids) {η : p.Fiber Y'₁} {zY yY : 𝒳} (sY : zY ⟶ η.1)
    (tY : zY ⟶ yY) [p.IsHomLift (pullback.snd b q) sY] [p.IsHomLift (pullback.fst b q) tY]
    {P : 𝒳} (d₁ d₂ : P ⟶ η.1) [p.IsHomLift (pullback.fst q q) d₁]
    [p.IsHomLift (pullback.snd q q) d₂] {B₁ : 𝒳} (r₁ : B₁ ⟶ P)
    [p.IsHomLift (pullback.snd b (pullback.fst q q ≫ q)) r₁] (ω₁ ω₂ : B₁ ⟶ zY)
    [p.IsHomLift (sideMap₁ b q) ω₁] [p.IsHomLift (sideMap₂ b q) ω₂]
    (hω₁ : ω₁ ≫ sY = r₁ ≫ d₁) (hω₂ : ω₂ ≫ sY = r₁ ≫ d₂) (hω : ω₁ ≫ tY = ω₂ ≫ tY)
    {A : 𝒳} (ℓ : Y'₁ ⟶ pullback q q) (hℓ₁ : ℓ ≫ pullback.fst q q = 𝟙 Y'₁)
    (hℓ₂ : ℓ ≫ pullback.snd q q = 𝟙 Y'₁) (s : A ⟶ P) [p.IsHomLift ℓ s] {B : 𝒳} (r : B ⟶ A)
    [p.IsHomLift (pullback.snd b q) r] :
    r ≫ s ≫ d₂ = r ≫ s ≫ d₁ := by
  have h₁ : p.IsHomLift (𝟙 (pullback b q) ≫ pullback.snd b q) (r ≫ s ≫ d₁) :=
    isHomLift_of_eq (f := pullback.snd b q ≫ ℓ ≫ pullback.fst q q) _
      (by rw [hℓ₁, Category.comp_id, Category.id_comp])
  have h₂ : p.IsHomLift (𝟙 (pullback b q) ≫ pullback.snd b q) (r ≫ s ≫ d₂) :=
    isHomLift_of_eq (f := pullback.snd b q ≫ ℓ ≫ pullback.snd q q) _
      (by rw [hℓ₂, Category.comp_id, Category.id_comp])
  obtain ⟨β, hβ, hβs⟩ := exists_factor hgpd (pullback.snd b q) sY (r ≫ s ≫ d₁)
    (𝟙 (pullback b q) ≫ pullback.snd b q) (𝟙 _) rfl
  obtain ⟨β', hβ', hβ's⟩ := exists_factor hgpd (pullback.snd b q) sY (r ≫ s ≫ d₂)
    (𝟙 (pullback b q) ≫ pullback.snd b q) (𝟙 _) rfl
  have hc := side_conv hgpd sY tY d₁ d₂ r₁ ω₁ ω₂ hω₁ hω₂ hω (pullback.snd b q ≫ ℓ) (𝟙 _) (𝟙 _)
    (r ≫ s) β β' rfl (by rw [hβs, Category.assoc]) (by rw [hβ's, Category.assoc])
  rw [← hβs, ← hβ's, eq_of_comp_eq hgpd (pullback.fst b q) tY (𝟙 _) hc]

/-- The threefold fibre product `Y'₁ ×_{Y'} Y'₁ ×_{Y'} Y'₁`, with its map to `Y'`. -/
noncomputable abbrev tripleMap (q : Y'₁ ⟶ Y') :
    pullback (pullback.snd q q) (pullback.fst q q) ⟶ Y' :=
  pullback.fst _ _ ≫ pullback.fst q q ≫ q

/-- **Transitivity on one side.** In the situation of `Deformation.Artin.side_conv`, let
`m, m', m'' : A ⟶ P` lie over the three projections of the threefold fibre product to the twofold
one, with `m ≫ d₂ = m' ≫ d₁` and `m'' ≫ d₁ = m ≫ d₁`. Then `m'' ≫ d₂` and `m' ≫ d₂` agree after
restriction to `Y ×_{Y'} (Y'₁ ×_{Y'} Y'₁ ×_{Y'} Y'₁)`. -/
lemma side_trans (hgpd : p.IsFiberedInGroupoids) {η : p.Fiber Y'₁} {zY yY : 𝒳} (sY : zY ⟶ η.1)
    (tY : zY ⟶ yY) [p.IsHomLift (pullback.snd b q) sY] [p.IsHomLift (pullback.fst b q) tY]
    {P : 𝒳} (d₁ d₂ : P ⟶ η.1) [p.IsHomLift (pullback.fst q q) d₁]
    [p.IsHomLift (pullback.snd q q) d₂] {B₁ : 𝒳} (r₁ : B₁ ⟶ P)
    [p.IsHomLift (pullback.snd b (pullback.fst q q ≫ q)) r₁] (ω₁ ω₂ : B₁ ⟶ zY)
    [p.IsHomLift (sideMap₁ b q) ω₁] [p.IsHomLift (sideMap₂ b q) ω₂]
    (hω₁ : ω₁ ≫ sY = r₁ ≫ d₁) (hω₂ : ω₂ ≫ sY = r₁ ≫ d₂) (hω : ω₁ ≫ tY = ω₂ ≫ tY)
    {A : 𝒳} (ℓ : pullback (pullback.snd q q) (pullback.fst q q) ⟶ pullback q q)
    (hℓ₂ : ℓ ≫ pullback.snd q q =
      pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
    (m m' m'' : A ⟶ P) [p.IsHomLift (pullback.fst (pullback.snd q q) (pullback.fst q q)) m]
    [p.IsHomLift (pullback.snd (pullback.snd q q) (pullback.fst q q)) m'] [p.IsHomLift ℓ m'']
    (h₁ : m ≫ d₂ = m' ≫ d₁) (h₂ : m'' ≫ d₁ = m ≫ d₁) {B : 𝒳} (r : B ⟶ A)
    [p.IsHomLift (pullback.snd b (tripleMap q)) r] :
    r ≫ m'' ≫ d₂ = r ≫ m' ≫ d₂ := by
  have e₁ : pullback.fst b (tripleMap q) ≫ b = (pullback.snd b (tripleMap q) ≫
      pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) ≫ q :=
    (pullback.condition (f := b) (g := tripleMap q)).trans (by simp only [Category.assoc])
  have e₂ : pullback.fst b (tripleMap q) ≫ b = (pullback.snd b (tripleMap q) ≫
      pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) ≫ q :=
    e₁.trans (by simp only [Category.assoc, pullback.condition (f := q) (g := q)])
  have e₃ : pullback.fst b (tripleMap q) ≫ b = (pullback.snd b (tripleMap q) ≫
      pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) ≫ q :=
    e₂.trans (by
      simp only [Category.assoc]
      rw [pullback.condition_assoc (f := pullback.snd q q) (g := pullback.fst q q)]
      exact congrArg (fun x => pullback.snd b (tripleMap q) ≫
        pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ x) pullback.condition)
  have fac : ∀ {g : pullback b (tripleMap q) ⟶ Y'₁}
      (e : pullback.fst b (tripleMap q) ≫ b = g ≫ q) (x : B ⟶ η.1) [p.IsHomLift g x],
      ∃ β : B ⟶ zY, p.IsHomLift (pullback.lift _ _ e) β ∧ β ≫ sY = x := fun e x _ =>
    exists_factor hgpd (pullback.snd b q) sY x _ (pullback.lift _ _ e)
      (pullback.lift_snd _ _ _).symm
  obtain ⟨βa, hβa, hβas⟩ := fac e₁ (r ≫ m ≫ d₁)
  obtain ⟨βb, hβb, hβbs⟩ := fac e₂ (r ≫ m ≫ d₂)
  obtain ⟨βc, hβc, hβcs⟩ := fac e₃ (r ≫ m' ≫ d₂)
  have : p.IsHomLift (pullback.snd b (tripleMap q) ≫ pullback.snd (pullback.snd q q)
      (pullback.fst q q) ≫ pullback.snd q q) (r ≫ m'' ≫ d₂) :=
    isHomLift_of_eq (f := pullback.snd b (tripleMap q) ≫ ℓ ≫ pullback.snd q q) _ (by rw [hℓ₂])
  obtain ⟨βd, hβd, hβds⟩ := fac e₃ (r ≫ m'' ≫ d₂)
  have hab : βa ≫ tY = βb ≫ tY := side_conv hgpd sY tY d₁ d₂ r₁ ω₁ ω₂ hω₁ hω₂ hω
    (pullback.snd b (tripleMap q) ≫ pullback.fst (pullback.snd q q) (pullback.fst q q))
    (pullback.lift _ _ e₁) (pullback.lift _ _ e₂) (r ≫ m) βa βb
    (by rw [pullback.lift_fst, pullback.lift_fst]) (by rw [hβas, Category.assoc])
    (by rw [hβbs, Category.assoc])
  have hbc : βb ≫ tY = βc ≫ tY := side_conv hgpd sY tY d₁ d₂ r₁ ω₁ ω₂ hω₁ hω₂ hω
    (pullback.snd b (tripleMap q) ≫ pullback.snd (pullback.snd q q) (pullback.fst q q))
    (pullback.lift _ _ e₂) (pullback.lift _ _ e₃) (r ≫ m') βb βc
    (by rw [pullback.lift_fst, pullback.lift_fst]) (by rw [hβbs, Category.assoc, h₁])
    (by rw [hβcs, Category.assoc])
  have had : βa ≫ tY = βd ≫ tY := side_conv hgpd sY tY d₁ d₂ r₁ ω₁ ω₂ hω₁ hω₂ hω
    (pullback.snd b (tripleMap q) ≫ ℓ) (pullback.lift _ _ e₁) (pullback.lift _ _ e₃) (r ≫ m'')
    βa βd (by rw [pullback.lift_fst, pullback.lift_fst]) (by rw [hβas, Category.assoc, h₂])
    (by rw [hβds, Category.assoc])
  have : βd = βc := eq_of_comp_eq hgpd (pullback.fst b q) tY (pullback.lift _ _ e₃)
    (had.symm.trans (hab.trans hbc))
  rw [← hβds, ← hβcs, this]

end Side

/-! ### The local-to-global step -/

section LocalToGlobal

variable [HasPullbacks 𝒮]

/-- The base change of a morphism generating a covering sieve generates a covering sieve. -/
lemma generate_singleton_pullback_fst_mem {J : GrothendieckTopology 𝒮} {Y' Y'₁ Z : 𝒮}
    {q : Y'₁ ⟶ Y'} (hq : Sieve.generate (Presieve.singleton q) ∈ J Y') (k : Z ⟶ Y') :
    Sieve.generate (Presieve.singleton (pullback.fst k q)) ∈ J Z := by
  refine J.superset_covering ?_ (J.pullback_stable k hq)
  rintro W g ⟨V, h, c, ⟨⟩, hhc⟩
  exact ⟨_, pullback.lift g h hhc.symm, pullback.fst k q, Presieve.singleton.mk,
    pullback.lift_fst _ _ _⟩

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}
variable {X X' Y Y' Y'₁ : 𝒮} {f : X ⟶ Y} {i : X ⟶ X'} {b : Y ⟶ Y'} {a : X' ⟶ Y'}

/-- The base change of `f` along `Y'₁ ×_{Y'} Y'₁ ⟶ Y'` followed by the first side map is the first
side map followed by the base change of `f` along `q`. -/
private lemma sideMap₁_comp_baseChangeLeft (q : Y'₁ ⟶ Y') :
    sideMap₁ (f ≫ b) q ≫ baseChangeLeft f b q =
      baseChangeLeft f b (pullback.fst q q ≫ q) ≫ sideMap₁ b q := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, baseChangeLeft, sideMap₁]

/-- See `Deformation.Artin.sideMap₁_comp_baseChangeLeft`. -/
private lemma sideMap₂_comp_baseChangeLeft (q : Y'₁ ⟶ Y') :
    sideMap₂ (f ≫ b) q ≫ baseChangeLeft f b q =
      baseChangeLeft f b (pullback.fst q q ≫ q) ≫ sideMap₂ b q := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, baseChangeLeft, sideMap₂]

/-- The base change of `i` along `Y'₁ ×_{Y'} Y'₁ ⟶ Y'` followed by the first side map is the first
side map followed by the base change of `i` along `q`. -/
private lemma sideMap₁_comp_baseChangeTop (w : f ≫ b = i ≫ a) (q : Y'₁ ⟶ Y') :
    sideMap₁ (f ≫ b) q ≫ baseChangeTop f i b a w q =
      baseChangeTop f i b a w (pullback.fst q q ≫ q) ≫ sideMap₁ a q := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, baseChangeTop, sideMap₁]

/-- See `Deformation.Artin.sideMap₁_comp_baseChangeTop`. -/
private lemma sideMap₂_comp_baseChangeTop (w : f ≫ b = i ≫ a) (q : Y'₁ ⟶ Y') :
    sideMap₂ (f ≫ b) q ≫ baseChangeTop f i b a w q =
      baseChangeTop f i b a w (pullback.fst q q ≫ q) ≫ sideMap₂ a q := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, baseChangeTop, sideMap₂]

/-- **Compatibility on the corner.** Let `L` be a local preimage along `q`, let `d₁ : P ⟶ L.obj`
and let `ω₁, ω₂` (resp. `ω₁', ω₂'`) identify the two pullbacks of `L.obj` to the base change of `Y`
(resp. `X'`) along `Y'₁ ×_{Y'} Y'₁ ⟶ Y'`, through `r₁` (resp. `s₁`). Then `ω₂ ≫ L.sY` and
`ω₂' ≫ L.sX'` agree on every common lift of the corner. -/
private lemma LocalPreimage.comp_sY_eq_comp_sX' (hgpd : p.IsFiberedInGroupoids) {w : f ≫ b = i ≫ a}
    {e : CategoricalPullback (p.chosenPullbacks.pullbackFunctor f)
      (p.chosenPullbacks.pullbackFunctor i)} {q : Y'₁ ⟶ Y'}
    (L : LocalPreimage (p := p) (f := f) (i := i) (b := b) (a := a) w e q) {P B₁ C₁ D : 𝒳}
    (d₁ : P ⟶ L.obj.1) (r₁ : B₁ ⟶ P) (s₁ : C₁ ⟶ P) (ω₁ ω₂ : B₁ ⟶ L.zY) (ω₁' ω₂' : C₁ ⟶ L.zX')
    [p.IsHomLift (sideMap₁ b q) ω₁] [p.IsHomLift (sideMap₂ b q) ω₂]
    [p.IsHomLift (sideMap₁ a q) ω₁'] [p.IsHomLift (sideMap₂ a q) ω₂']
    (hω₁ : ω₁ ≫ L.sY = r₁ ≫ d₁) (hω₂ : ω₂ ≫ L.tY = ω₁ ≫ L.tY) (hω₁' : ω₁' ≫ L.sX' = s₁ ≫ d₁)
    (hω₂' : ω₂' ≫ L.tX' = ω₁' ≫ L.tX') (uX : D ⟶ B₁) (vX : D ⟶ C₁)
    [p.IsHomLift (baseChangeLeft f b (pullback.fst q q ≫ q)) uX]
    [p.IsHomLift (baseChangeTop f i b a w (pullback.fst q q ≫ q)) vX] (huv : uX ≫ r₁ = vX ≫ s₁) :
    uX ≫ ω₂ ≫ L.sY = vX ≫ ω₂' ≫ L.sX' := by
  obtain ⟨n₀, hn₀l, hn₀⟩ := exists_factor hgpd f (p.chosenPullbacks.map f e.fst)
    (uX ≫ ω₁ ≫ L.tY) (baseChangeLeft f b (pullback.fst q q ≫ q) ≫ sideMap₁ b q ≫ pullback.fst b q)
    (pullback.fst (f ≫ b) (pullback.fst q q ≫ q)) (by rw [pullback.lift_fst, pullback.lift_fst])
  obtain ⟨κ₁, hκ₁l, hκ₁⟩ := exists_factor hgpd (pullback.fst (f ≫ b) q) L.lam n₀
    (pullback.fst (f ≫ b) (pullback.fst q q ≫ q)) (sideMap₁ (f ≫ b) q)
    (pullback.lift_fst _ _ _).symm
  obtain ⟨κ₂, hκ₂l, hκ₂⟩ := exists_factor hgpd (pullback.fst (f ≫ b) q) L.lam n₀
    (pullback.fst (f ≫ b) (pullback.fst q q ≫ q)) (sideMap₂ (f ≫ b) q)
    (pullback.lift_fst _ _ _).symm
  have : p.IsHomLift (sideMap₁ (f ≫ b) q ≫ baseChangeLeft f b q) (uX ≫ ω₁) :=
    isHomLift_of_eq _ (sideMap₁_comp_baseChangeLeft q).symm
  have : p.IsHomLift (sideMap₁ (f ≫ b) q ≫ baseChangeTop f i b a w q) (vX ≫ ω₁') :=
    isHomLift_of_eq _ (sideMap₁_comp_baseChangeTop w q).symm
  have : p.IsHomLift (sideMap₂ (f ≫ b) q ≫ baseChangeLeft f b q) (uX ≫ ω₂) :=
    isHomLift_of_eq _ (sideMap₂_comp_baseChangeLeft q).symm
  have : p.IsHomLift (sideMap₂ (f ≫ b) q ≫ baseChangeTop f i b a w q) (vX ≫ ω₂') :=
    isHomLift_of_eq _ (sideMap₂_comp_baseChangeTop w q).symm
  have h₁Y : κ₁ ≫ L.lY = uX ≫ ω₁ :=
    eq_of_comp_eq hgpd (pullback.fst b q) L.tY (sideMap₁ (f ≫ b) q ≫ baseChangeLeft f b q) (by
      rw [Category.assoc, ← L.lam_map, reassoc_of% hκ₁, hn₀, Category.assoc])
  have h₁X : κ₁ ≫ L.lX' = vX ≫ ω₁' :=
    eq_of_comp_eq hgpd (pullback.snd a q) L.sX' (sideMap₁ (f ≫ b) q ≫ baseChangeTop f i b a w q)
      (by rw [Category.assoc, ← L.lY_sY, reassoc_of% h₁Y, hω₁, reassoc_of% huv]
          simp only [Category.assoc, hω₁'])
  have hn₀i : n₀ ≫ Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd =
      vX ≫ ω₂' ≫ L.tX' := by
    rw [← hκ₁, Category.assoc, L.lam_iso, reassoc_of% h₁X, hω₂']
  have h₂Y : κ₂ ≫ L.lY = uX ≫ ω₂ :=
    eq_of_comp_eq hgpd (pullback.fst b q) L.tY (sideMap₂ (f ≫ b) q ≫ baseChangeLeft f b q) (by
      rw [Category.assoc, ← L.lam_map, reassoc_of% hκ₂, hn₀, Category.assoc, hω₂])
  have h₂X : κ₂ ≫ L.lX' = vX ≫ ω₂' :=
    eq_of_comp_eq hgpd (pullback.fst a q) L.tX' (sideMap₂ (f ≫ b) q ≫ baseChangeTop f i b a w q)
      (by rw [Category.assoc, ← L.lam_iso, reassoc_of% hκ₂, hn₀i, Category.assoc])
  rw [← reassoc_of% h₂Y, L.lY_sY, reassoc_of% h₂X]

/-- **Reflexivity of the glued descent datum.** In the situation of
`Deformation.Artin.LocalPreimage.comp_sY_eq_comp_sX'`, let `d₂ : P ⟶ L.obj` be glued from
`ω₂ ≫ L.sY` and `ω₂' ≫ L.sX'`. If the base change of the square along `q` is a gluing square, then
`(d₁, d₂)` is reflexive. -/
private lemma LocalPreimage.descent_refl (hgpd : p.IsFiberedInGroupoids) {w : f ≫ b = i ≫ a}
    {e : CategoricalPullback (p.chosenPullbacks.pullbackFunctor f)
      (p.chosenPullbacks.pullbackFunctor i)} {q : Y'₁ ⟶ Y'}
    (hglue₁ : IsGluingSquare p (baseChangeLeft f b q) (baseChangeTop f i b a w q)
      (pullback.snd b q) (pullback.snd a q))
    (L : LocalPreimage (p := p) (f := f) (i := i) (b := b) (a := a) w e q) {P B₁ C₁ : 𝒳}
    (d₁ d₂ : P ⟶ L.obj.1) [p.IsHomLift (pullback.fst q q) d₁] [p.IsHomLift (pullback.snd q q) d₂]
    (r₁ : B₁ ⟶ P) (s₁ : C₁ ⟶ P) [p.IsHomLift (pullback.snd b (pullback.fst q q ≫ q)) r₁]
    [p.IsHomLift (pullback.snd a (pullback.fst q q ≫ q)) s₁] (ω₁ ω₂ : B₁ ⟶ L.zY)
    (ω₁' ω₂' : C₁ ⟶ L.zX') [p.IsHomLift (sideMap₁ b q) ω₁] [p.IsHomLift (sideMap₂ b q) ω₂]
    [p.IsHomLift (sideMap₁ a q) ω₁'] [p.IsHomLift (sideMap₂ a q) ω₂']
    (hω₁ : ω₁ ≫ L.sY = r₁ ≫ d₁) (hd₂Y : r₁ ≫ d₂ = ω₂ ≫ L.sY) (hω₂ : ω₂ ≫ L.tY = ω₁ ≫ L.tY)
    (hω₁' : ω₁' ≫ L.sX' = s₁ ≫ d₁) (hd₂X : s₁ ≫ d₂ = ω₂' ≫ L.sX')
    (hω₂' : ω₂' ≫ L.tX' = ω₁' ≫ L.tX') {A : 𝒳} (ℓ : Y'₁ ⟶ pullback q q)
    (hℓ₁ : ℓ ≫ pullback.fst q q = 𝟙 Y'₁) (hℓ₂ : ℓ ≫ pullback.snd q q = 𝟙 Y'₁) (s : A ⟶ P)
    (u : A ⟶ L.obj.1) [p.IsHomLift ℓ s] (hsu : s ≫ d₁ = u) : s ≫ d₂ = u := by
  have hA : p.obj A = Y'₁ := IsHomLift.domain_eq p ℓ s
  let A' : p.Fiber Y'₁ := ⟨A, hA⟩
  have h₁ : p.IsHomLift (𝟙 Y'₁) (s ≫ d₂) := isHomLift_of_eq (f := ℓ ≫ pullback.snd q q) _ hℓ₂
  have h₂ : p.IsHomLift (𝟙 Y'₁) u := by
    rw [← hsu]
    exact isHomLift_of_eq (f := ℓ ≫ pullback.fst q q) _ hℓ₁
  refine hglue₁.hom_ext (IsPreFibered.pullbackMap A'.2 (pullback.snd b q))
    (IsPreFibered.pullbackMap A'.2 (pullback.snd a q)) (𝟙 Y'₁) (s ≫ d₂) u inferInstance
    inferInstance h₁ h₂ ?_ ?_ <;> rw [← hsu]
  · exact side_refl (b := b) (q := q) hgpd L.sY L.tY d₁ d₂ r₁ ω₁ ω₂ hω₁ hd₂Y.symm hω₂.symm ℓ
      hℓ₁ hℓ₂ s _
  · exact side_refl (b := a) (q := q) hgpd L.sX' L.tX' d₁ d₂ s₁ ω₁' ω₂' hω₁' hd₂X.symm hω₂'.symm
      ℓ hℓ₁ hℓ₂ s _

/-- **Transitivity of the glued descent datum.** In the situation of
`Deformation.Artin.LocalPreimage.descent_refl`, if the base change of the square along
`Y'₁ ×_{Y'} Y'₁ ×_{Y'} Y'₁ ⟶ Y'` is a gluing square, then `(d₁, d₂)` is transitive. -/
private lemma LocalPreimage.descent_trans (hgpd : p.IsFiberedInGroupoids) {w : f ≫ b = i ≫ a}
    {e : CategoricalPullback (p.chosenPullbacks.pullbackFunctor f)
      (p.chosenPullbacks.pullbackFunctor i)} {q : Y'₁ ⟶ Y'}
    (hglue₃ : IsGluingSquare p (baseChangeLeft f b (tripleMap q))
      (baseChangeTop f i b a w (tripleMap q)) (pullback.snd b (tripleMap q))
      (pullback.snd a (tripleMap q)))
    (L : LocalPreimage (p := p) (f := f) (i := i) (b := b) (a := a) w e q) {P B₁ C₁ : 𝒳}
    (d₁ d₂ : P ⟶ L.obj.1) [p.IsHomLift (pullback.fst q q) d₁] [p.IsHomLift (pullback.snd q q) d₂]
    (r₁ : B₁ ⟶ P) (s₁ : C₁ ⟶ P) [p.IsHomLift (pullback.snd b (pullback.fst q q ≫ q)) r₁]
    [p.IsHomLift (pullback.snd a (pullback.fst q q ≫ q)) s₁] (ω₁ ω₂ : B₁ ⟶ L.zY)
    (ω₁' ω₂' : C₁ ⟶ L.zX') [p.IsHomLift (sideMap₁ b q) ω₁] [p.IsHomLift (sideMap₂ b q) ω₂]
    [p.IsHomLift (sideMap₁ a q) ω₁'] [p.IsHomLift (sideMap₂ a q) ω₂']
    (hω₁ : ω₁ ≫ L.sY = r₁ ≫ d₁) (hd₂Y : r₁ ≫ d₂ = ω₂ ≫ L.sY) (hω₂ : ω₂ ≫ L.tY = ω₁ ≫ L.tY)
    (hω₁' : ω₁' ≫ L.sX' = s₁ ≫ d₁) (hd₂X : s₁ ≫ d₂ = ω₂' ≫ L.sX')
    (hω₂' : ω₂' ≫ L.tX' = ω₁' ≫ L.tX') {A : 𝒳}
    (ℓ : pullback (pullback.snd q q) (pullback.fst q q) ⟶ pullback q q)
    (hℓ₂ : ℓ ≫ pullback.snd q q =
      pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
    (m m' m'' : A ⟶ P) [p.IsHomLift (pullback.fst (pullback.snd q q) (pullback.fst q q)) m]
    [p.IsHomLift (pullback.snd (pullback.snd q q) (pullback.fst q q)) m'] [p.IsHomLift ℓ m'']
    (h₁ : m ≫ d₂ = m' ≫ d₁) (h₂ : m'' ≫ d₁ = m ≫ d₁) : m'' ≫ d₂ = m' ≫ d₂ := by
  have hA : p.obj A = pullback (pullback.snd q q) (pullback.fst q q) :=
    IsHomLift.domain_eq p (pullback.fst (pullback.snd q q) (pullback.fst q q)) m
  let A' : p.Fiber (pullback (pullback.snd q q) (pullback.fst q q)) := ⟨A, hA⟩
  have h₃ : p.IsHomLift (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫
      pullback.snd q q) (m'' ≫ d₂) := isHomLift_of_eq (f := ℓ ≫ pullback.snd q q) _ hℓ₂
  exact hglue₃.hom_ext (IsPreFibered.pullbackMap A'.2 (pullback.snd b (tripleMap q)))
    (IsPreFibered.pullbackMap A'.2 (pullback.snd a (tripleMap q)))
    (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) (m'' ≫ d₂)
    (m' ≫ d₂) inferInstance inferInstance h₃ inferInstance
    (side_trans (b := b) (q := q) hgpd L.sY L.tY d₁ d₂ r₁ ω₁ ω₂ hω₁ hd₂Y.symm hω₂.symm ℓ hℓ₂ m
      m' m'' h₁ h₂ _)
    (side_trans (b := a) (q := q) hgpd L.sX' L.tX' d₁ d₂ s₁ ω₁' ω₂' hω₁' hd₂X.symm hω₂'.symm ℓ
      hℓ₂ m m' m'' h₁ h₂ _)

/-- **The local-to-global step of Stacks 07WN.** Let `p : 𝒳 ⥤ 𝒮` be a stack in groupoids over a
site with fibre products, let `f ≫ b = i ≫ a` be a commutative square of the base, and let
`q : Y'₁ ⟶ Y'` generate a covering sieve of `Y'`. Suppose that the base changes of the square
along `q`, along `Y'₁ ×_{Y'} Y'₁ ⟶ Y'` and along `Y'₁ ×_{Y'} Y'₁ ×_{Y'} Y'₁ ⟶ Y'` are gluing
squares (`Deformation.Artin.IsGluingSquare`; this holds when their comparison functors are full
and faithful, `Deformation.Artin.isGluingSquare_of_full_of_faithful`). Then every object of the
two-fibre product admitting a local preimage along `q` lies in the essential image of the
comparison functor of the square. -/
theorem mem_essImage_fiberSquareComparison_of_localPreimage (hgpd : p.IsFiberedInGroupoids)
    (hst : p.IsStack J) (w : f ≫ b = i ≫ a) (q : Y'₁ ⟶ Y')
    (hq : Sieve.generate (Presieve.singleton q) ∈ J Y')
    (hglue₁ : IsGluingSquare p (baseChangeLeft f b q) (baseChangeTop f i b a w q)
      (pullback.snd b q) (pullback.snd a q))
    (hglue₂ : IsGluingSquare p (baseChangeLeft f b (pullback.fst q q ≫ q))
      (baseChangeTop f i b a w (pullback.fst q q ≫ q)) (pullback.snd b (pullback.fst q q ≫ q))
      (pullback.snd a (pullback.fst q q ≫ q)))
    (hglue₃ : IsGluingSquare p (baseChangeLeft f b (tripleMap q))
      (baseChangeTop f i b a w (tripleMap q)) (pullback.snd b (tripleMap q))
      (pullback.snd a (tripleMap q)))
    (e : CategoricalPullback (p.chosenPullbacks.pullbackFunctor f)
      (p.chosenPullbacks.pullbackFunctor i))
    (L : LocalPreimage (p := p) (f := f) (i := i) (b := b) (a := a) w e q) :
    (fiberSquareComparison p p.chosenPullbacks f i b a w).essImage e := by
  let η := L.obj
  let P : p.Fiber (pullback q q) := pullbackFiber p η (pullback.fst q q)
  let d₁ : P.1 ⟶ η.1 := IsPreFibered.pullbackMap η.2 (pullback.fst q q)
  -- the restrictions of `P` to the two sides of the square over `Y'₁ ×_{Y'} Y'₁`
  let r₁ := IsPreFibered.pullbackMap P.2 (pullback.snd b (pullback.fst q q ≫ q))
  let s₁ := IsPreFibered.pullbackMap P.2 (pullback.snd a (pullback.fst q q ≫ q))
  -- the identifications of the two pullbacks of `η` on the two sides
  obtain ⟨ω₁, hω₁l, hω₁⟩ := exists_factor hgpd (pullback.snd b q) L.sY (r₁ ≫ d₁)
    (pullback.snd b (pullback.fst q q ≫ q) ≫ pullback.fst q q) (sideMap₁ b q)
    (pullback.lift_snd _ _ _).symm
  obtain ⟨ω₂, hω₂l, hω₂⟩ := exists_factor hgpd (pullback.fst b q) L.tY (ω₁ ≫ L.tY)
    (sideMap₁ b q ≫ pullback.fst b q) (sideMap₂ b q)
    ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm)
  obtain ⟨ω₁', hω₁'l, hω₁'⟩ := exists_factor hgpd (pullback.snd a q) L.sX' (s₁ ≫ d₁)
    (pullback.snd a (pullback.fst q q ≫ q) ≫ pullback.fst q q) (sideMap₁ a q)
    (pullback.lift_snd _ _ _).symm
  obtain ⟨ω₂', hω₂'l, hω₂'⟩ := exists_factor hgpd (pullback.fst a q) L.tX' (ω₁' ≫ L.tX')
    (sideMap₁ a q ≫ pullback.fst a q) (sideMap₂ a q)
    ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm)
  -- the second morphism `d₂ : P ⟶ η`, glued from the two sides over `Y'₁ ×_{Y'} Y'₁`
  have hmY : p.IsHomLift (pullback.snd b (pullback.fst q q ≫ q) ≫ pullback.snd q q)
      (ω₂ ≫ L.sY) := isHomLift_of_eq (f := sideMap₂ b q ≫ pullback.snd b q) _
      (pullback.lift_snd _ _ _)
  have hmX : p.IsHomLift (pullback.snd a (pullback.fst q q ≫ q) ≫ pullback.snd q q)
      (ω₂' ≫ L.sX') := isHomLift_of_eq (f := sideMap₂ a q ≫ pullback.snd a q) _
      (pullback.lift_snd _ _ _)
  obtain ⟨d₂, hd₂l, hd₂Y, hd₂X⟩ := hglue₂.exists_desc r₁ s₁ (pullback.snd q q) (ω₂ ≫ L.sY)
    (ω₂' ≫ L.sX') inferInstance inferInstance hmY hmX fun uX vX _ _ huv =>
      L.comp_sY_eq_comp_sX' hgpd d₁ r₁ s₁ ω₁ ω₂ ω₁' ω₂' hω₁ hω₂ hω₁' hω₂' uX vX huv
  -- the descent of `η` along `q`
  obtain ⟨y, κ, hκc, hκ⟩ := exists_descent_of_mem_singleton_sieve q hst hq η d₁ d₂
    (fun ℓ hℓ₁ hℓ₂ s u _ hsu => L.descent_refl hgpd hglue₁ d₁ d₂ r₁ s₁ ω₁ ω₂ ω₁' ω₂' hω₁ hd₂Y
      hω₂ hω₁' hd₂X hω₂' ℓ hℓ₁ hℓ₂ s u hsu)
    (fun ℓ _ hℓ₂ m m' m'' _ _ _ h₁ h₂ => L.descent_trans hgpd hglue₃ d₁ d₂ r₁ s₁ ω₁ ω₂ ω₁' ω₂'
      hω₁ hd₂Y hω₂ hω₁' hd₂X hω₂' ℓ hℓ₂ m m' m'' h₁ h₂)
  -- the two morphisms from the components of `e` to the descended object
  have := hgpd.isStronglyCartesian_homLift (pullback.fst b q) L.tY
  have := hgpd.isStronglyCartesian_homLift (pullback.fst a q) L.tX'
  have := hgpd.isStronglyCartesian_homLift (pullback.fst (f ≫ b) q) L.lam
  have hκY : p.IsHomLift (pullback.fst b q ≫ b) (L.sY ≫ κ) :=
    isHomLift_of_eq (f := pullback.snd b q ≫ q) _ pullback.condition.symm
  have hκX : p.IsHomLift (pullback.fst a q ≫ a) (L.sX' ≫ κ) :=
    isHomLift_of_eq (f := pullback.snd a q ≫ q) _ pullback.condition.symm
  obtain ⟨uY, huYl, huY⟩ := exists_comp_eq_of_mem_singleton_sieve (pullback.fst b q) hst
    (generate_singleton_pullback_fst_mem hq b) (x := e.fst) L.tY b (L.sY ≫ κ)
    (fun {t} α₁ α₂ h₁ h₂ hα => by
      obtain ⟨n, hn₁, hn₂⟩ := side_fwd (b := b) (q := q) hgpd L.sY L.tY d₁ d₂ r₁ ω₁ ω₂ hω₁
        hd₂Y.symm hω₂.symm (pullback.fst (pullback.fst b q) (pullback.fst b q))
        (pullback.snd (pullback.fst b q) (pullback.fst b q)) α₁ α₂ pullback.condition hα
      rw [← Category.assoc, ← hn₁, Category.assoc, hκ, ← Category.assoc, hn₂, Category.assoc])
  obtain ⟨uX, huXl, huX⟩ := exists_comp_eq_of_mem_singleton_sieve (pullback.fst a q) hst
    (generate_singleton_pullback_fst_mem hq a) (x := e.snd) L.tX' a (L.sX' ≫ κ)
    (fun {t} α₁ α₂ h₁ h₂ hα => by
      obtain ⟨n, hn₁, hn₂⟩ := side_fwd (b := a) (q := q) hgpd L.sX' L.tX' d₁ d₂ s₁ ω₁' ω₂' hω₁'
        hd₂X.symm hω₂'.symm (pullback.fst (pullback.fst a q) (pullback.fst a q))
        (pullback.snd (pullback.fst a q) (pullback.fst a q)) α₁ α₂ pullback.condition hα
      rw [← Category.assoc, ← hn₁, Category.assoc, hκ, ← Category.assoc, hn₂, Category.assoc])
  -- their compatibility over the corner `X`
  have hβ₀ : p.IsHomLift (𝟙 X ≫ i)
      (Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd) :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ (𝟙 X) i (Fiber.fiberInclusion.map e.iso.hom)
      (p.chosenPullbacks.map i e.snd) e.iso.hom.2
      (p.chosenPullbacks.isStronglyCartesian i e.snd).toIsHomLift
  have hβ₁ : p.IsHomLift ((𝟙 X ≫ i) ≫ a)
      ((Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd) ≫ uX) :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ (𝟙 X ≫ i) a _ uX hβ₀ huXl
  have hβ : p.IsHomLift (f ≫ b)
      ((Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd) ≫ uX) :=
    isHomLift_of_eq (f := (𝟙 X ≫ i) ≫ a) _ (by rw [Category.id_comp, w])
  refine mem_essImage_fiberSquareComparison_of_hom hgpd w e y uY uX ?_
  refine eq_of_comp_eq_of_mem_singleton_sieve (pullback.fst (f ≫ b) q) hst
    (generate_singleton_pullback_fst_mem hq (f ≫ b)) (x := p.chosenPullbacks.obj f e.fst) L.lam
    (f ≫ b) _ _ inferInstance hβ ?_
  calc L.lam ≫ p.chosenPullbacks.map f e.fst ≫ uY = L.lY ≫ L.sY ≫ κ := by
        rw [reassoc_of% L.lam_map, huY]
    _ = L.lX' ≫ L.tX' ≫ uX := by rw [reassoc_of% L.lY_sY, huX]
    _ = (L.lam ≫ Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd) ≫ uX := by
        rw [L.lam_iso, Category.assoc]
    _ = L.lam ≫ (Fiber.fiberInclusion.map e.iso.hom ≫ p.chosenPullbacks.map i e.snd) ≫ uX :=
        Category.assoc _ _ _

end LocalToGlobal

end Deformation.Artin
