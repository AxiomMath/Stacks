module

public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# The diagonal square of a fully faithful 1-morphism of cospans, over a base (Stacks 0CBB)

Let `𝒞` be a category and let

```text
    𝒳 --f--> 𝒴
    |         |
   I|         |J
    v         v
    𝒳' -f'-> 𝒴'
```

be a square of categories over `𝒞`, strictly over `𝒞` in each arrow, commuting up to a vertical
isomorphism `E : f ⋙ J ≅ I ⋙ f'`. Applying `I` to both factors carries the 2-fibre product
`𝒳 ×_𝒴 𝒳` to `𝒳' ×_{𝒴'} 𝒳'`, and the resulting square

```text
    𝒳  --Δ_f-->  𝒳 ×_𝒴 𝒳
    |                 |
    |                 |
    v                 v
    𝒳' --Δ_{f'}-> 𝒳' ×_{𝒴'} 𝒳'
```

is 2-cartesian as soon as `I` is fully faithful and `J` is faithful. This is **Stacks 0CBB** —
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_monomorphism_diagonalComparison` — read
over the base `𝒞` and with the target of the cospan allowed to grow from `𝒴` to `𝒴'`: the source
states it for `𝒳 ⟶ 𝒳' ⟶ 𝒴`, which is the case `𝒴 = 𝒴'`, `J = 𝟙`, `E = 𝟙`.

As throughout this directory, being 2-cartesian is rendered as the comparison functor into the
explicit 2-fibre product of the cospan being an equivalence.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.selfProductMap`: the 1-morphism
  `𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` which applies `I` to both factors, reading the comparison
  isomorphism of an object through `J` and `E`.
* `CategoryTheory.TwoFibreProductOver.selfProductDiagonalFiller`: the 2-cell of the square. Both
  components of each of its components are **identities**: the image under `selfProductMap` of
  the diagonal of `x` is the diagonal of `I x`, because `E` cancels against itself when the
  comparison isomorphism being transported is one.
* `CategoryTheory.TwoFibreProductOver.selfProductDiagonalComparison`: the comparison functor
  into the explicit 2-fibre product of the cospan `(selfProductMap, Δ_{f'})`.

## Main results

* `CategoryTheory.TwoFibreProductOver.isHomLift_selfProductDiagonalFiller`: every component of
  the 2-cell is vertical, so the square is one of categories *over* `𝒞`.
* `CategoryTheory.TwoFibreProductOver.isEquivalence_selfProductDiagonalComparison`:
  **Stacks 0CBB over `𝒞`**, the square is 2-cartesian.

Untagged: the `@[stacks 0CBB]` attribute sits on the absolute form
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_monomorphism_diagonalComparison`, as the
`02XC`, `02XD` and `04YR` tags sit on absolute forms while their over-the-base companions live
untagged in `StacksFrontier.CategoryTheory.TwoFibreProduct.OverComposable`, `.OverComparison` and
`.OverDiagonalBaseChange`. The over-the-base form is not an instance of the absolute one: the
comparison isomorphism of an object is arbitrary there and vertical here.

## Implementation notes

The three halves of the equivalence use the three hypotheses separately, and the proofs are the
source's:

* faithfulness needs only faithfulness of `I`, being read off the `𝒳'`-component;
* fullness needs `I` full and faithful. The compatibility square of a morphism of the pullback
  forces both components of its `𝒳 ×_𝒴 𝒳`-part to have the same image under `I`, namely its
  `𝒳'`-component, so both agree with that component's preimage;
* essential surjectivity needs `I` full and faithful and `J` faithful. The two components of the
  comparison isomorphism of an object compose to an isomorphism `I x ≅ I y`, whose preimage
  `γ : x ≅ y` has `J (f γ) = J φ` by naturality of `E`; faithfulness of `J` upgrades that to
  `f γ = φ`, which is exactly the hypothesis of
  `CategoryTheory.TwoFibreProductOver.homDiagonal`.

Faithfulness of `J` is the one hypothesis with no counterpart in the source's 0CBB, where
`J = 𝟙`. It is what the growing target costs, and it is available wherever this is used: in
Stacks 0BPU the 1-morphism `J` is a thickening, hence a monomorphism, hence fully faithful.

The hypotheses are explicit binders rather than section variables because several of them appear
only in the *bodies* of the declarations below, and a section variable which the signature does
not mention is not included.

**Duplication to be resolved.** `CategoryTheory.TwoFibreProductOver.selfProductMap` is the same
functor as `CategoryTheory.TwoFibreProductOver.stackifyMap`, in this same namespace, at
`StacksFrontier.CategoryTheory.Sites.Stackification.TwoFibreProduct`: instantiating that one at
`𝒵 := 𝒳`, `𝒵' := 𝒳'`, `g := f`, `g' := f'`, `k := i`, `α := β := E.symm` gives this one's object
and morphism parts verbatim. The two differ only in hypothesis strength and universe generality,
both in this one's favour: `stackifyMap` asks for `CategoryTheory.Functor.IsFibredOneMorphism`
in each of its three functors, whose `map_isStronglyCartesian` field its own body never uses,
and it pins all seven categories to one morphism universe. Consuming it here would therefore
add two dead hypotheses, collapse the five independent universe pairs below to one, and make a
statement about relative diagonals depend on the stackification tower. The consolidation that
costs nothing is the other direction — weaken `stackifyMap` to the plain `comp_eq` its proof
uses, give it independent universes, and delete the functor below in its favour — and that is a
change to an existing declaration's signature, so it is left for a deliberate dedup pass rather
than taken here.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
* [Stacks Project, Tag 0CBB](https://stacks.math.columbia.edu/tag/0CBB)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
  {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒳' : Type u₃} [Category.{v₃} 𝒳']
  {𝒴 : Type u₄} [Category.{v₄} 𝒴] {𝒴' : Type u₅} [Category.{v₅} 𝒴']
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒴' : 𝒴' ⥤ 𝒞}
  {f : 𝒳 ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {I : 𝒳 ⥤ 𝒳'} {J : 𝒴 ⥤ 𝒴'}

-- The two components of `Δ_f x` are the same object of `𝒳`, and the comparison isomorphisms of
-- the objects below are identities only after unfolding `diagonal`; both unifications need that
-- at instance transparency, which a plain `def` does not provide. This is the same local
-- attribute that `StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal` sets for its own use.
attribute [local instance_reducible] diagonal

/-- **Naturality of `E`, solved for the `f'`-image of an `I`-image.** For `g : x ⟶ y` in `𝒳`,
the morphism `f' (I g)` of `𝒴'` is `J (f g)` read through the two relevant components of
`E : f ⋙ J ≅ I ⋙ f'`. -/
lemma map_comp_map_eq_of_natIso (E : f ⋙ J ≅ I ⋙ f') {x y : 𝒳} (g : x ⟶ y) :
    f'.map (I.map g) = E.inv.app x ≫ J.map (f.map g) ≫ E.hom.app y := by
  have nat := E.hom.naturality g
  simp only [Functor.comp_map] at nat
  rw [nat, ← Category.assoc]
  simp

section SelfProductMap

/-- **Applying `I` to both factors of a self-product.** The 1-morphism
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` carrying `(U, x, y, φ)` to `(U, I x, I y, E_x⁻¹ ≫ J φ ≫ E_y)`: the
comparison isomorphism `φ : f x ≅ f y` is pushed into `𝒴'` by `J` and then read as an
isomorphism `f' (I x) ≅ f' (I y)` through the two relevant components of `E`.

The resulting comparison isomorphism is vertical because all three of its factors are: the
components of `E` by hypothesis, and `J φ` because `J` is strictly over `𝒞`. -/
def selfProductMap (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
    (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x)) :
    TwoFibreProductOver p𝒳 p𝒳 p𝒴 f f ⥤ TwoFibreProductOver p𝒳' p𝒳' p𝒴' f' f' where
  obj P :=
    { base := P.base
      x := I.obj P.x
      y := I.obj P.y
      hx := (Functor.congr_obj hI P.x).trans P.hx
      hy := (Functor.congr_obj hI P.y).trans P.hy
      iso := (E.app P.x).symm ≪≫ J.mapIso P.iso ≪≫ E.app P.y
      vertical := by
        have h1 : p𝒴'.IsHomLift (𝟙 P.base) (E.app P.x).hom := by
          rw [← P.hx]; exact hE P.x
        have h2 : p𝒴'.IsHomLift (𝟙 P.base) (E.app P.x).inv :=
          IsHomLift.lift_id_inv p𝒴' P.base (E.app P.x)
        have h3 : p𝒴'.IsHomLift (𝟙 P.base) (J.map P.iso.hom) :=
          have := P.vertical
          Functor.isHomLift_map_of_comp_eq hJ (𝟙 P.base) P.iso.hom
        have h4 : p𝒴'.IsHomLift (𝟙 P.base) (E.app P.y).hom := by
          rw [← P.hy]; exact hE P.y
        change p𝒴'.IsHomLift (𝟙 P.base)
          ((E.app P.x).inv ≫ J.map P.iso.hom ≫ (E.app P.y).hom)
        infer_instance }
  map {P Q} φ :=
    { hbase := φ.hbase
      a := I.map φ.a
      b := I.map φ.b
      ha :=
        have := φ.ha
        Functor.isHomLift_map_of_comp_eq hI φ.hbase φ.a
      hb :=
        have := φ.hb
        Functor.isHomLift_map_of_comp_eq hI φ.hbase φ.b
      w := by
        have hw := φ.w
        change f'.map (I.map φ.a) ≫ E.inv.app Q.x ≫ J.map Q.iso.hom ≫ E.hom.app Q.y =
          (E.inv.app P.x ≫ J.map P.iso.hom ≫ E.hom.app P.y) ≫ f'.map (I.map φ.b)
        rw [map_comp_map_eq_of_natIso E φ.a, map_comp_map_eq_of_natIso E φ.b]
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
        rw [← Functor.map_comp_assoc, hw, Functor.map_comp]
        simp }
  map_id P := by refine Hom.ext' ?_ ?_ <;> simp
  map_comp φ ψ := by refine Hom.ext' ?_ ?_ <;> simp

attribute [local instance_reducible] selfProductMap

variable (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
  (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x))

/-- The first object of the image of `P` under `selfProductMap` is `I` applied to `P.x`. -/
@[simp] lemma selfProductMap_obj_x (P : TwoFibreProductOver p𝒳 p𝒳 p𝒴 f f) :
    ((selfProductMap hI hJ E hE).obj P).x = I.obj P.x := rfl

/-- The second object of the image of `P` under `selfProductMap` is `I` applied to `P.y`. -/
@[simp] lemma selfProductMap_obj_y (P : TwoFibreProductOver p𝒳 p𝒳 p𝒴 f f) :
    ((selfProductMap hI hJ E hE).obj P).y = I.obj P.y := rfl

/-- The comparison morphism of the image of `P` under `selfProductMap` is `J` applied to that of
`P`, conjugated by the components of `E`. -/
@[simp] lemma selfProductMap_obj_iso_hom (P : TwoFibreProductOver p𝒳 p𝒳 p𝒴 f f) :
    ((selfProductMap hI hJ E hE).obj P).iso.hom =
      E.inv.app P.x ≫ J.map P.iso.hom ≫ E.hom.app P.y := rfl

/-- The first component of the image of `φ` under `selfProductMap` is `I` applied to `φ.a`. -/
@[simp] lemma selfProductMap_map_a {P Q : TwoFibreProductOver p𝒳 p𝒳 p𝒴 f f} (φ : P ⟶ Q) :
    ((selfProductMap hI hJ E hE).map φ).a = I.map φ.a := rfl

/-- The second component of the image of `φ` under `selfProductMap` is `I` applied to `φ.b`. -/
@[simp] lemma selfProductMap_map_b {P Q : TwoFibreProductOver p𝒳 p𝒳 p𝒴 f f} (φ : P ⟶ Q) :
    ((selfProductMap hI hJ E hE).map φ).b = I.map φ.b := rfl

/-- **`selfProductMap` is faithful as soon as `I` is.** Both components of the image of a
morphism are its components' images under `I`. -/
instance faithful_selfProductMap [I.Faithful] : (selfProductMap hI hJ E hE).Faithful where
  map_injective {_ _} {φ ψ} h :=
    have ha : ((selfProductMap hI hJ E hE).map φ).a = ((selfProductMap hI hJ E hE).map ψ).a :=
      congrArg Hom.a h
    have hb : ((selfProductMap hI hJ E hE).map φ).b = ((selfProductMap hI hJ E hE).map ψ).b :=
      congrArg Hom.b h
    Hom.ext' (I.map_injective ha) (I.map_injective hb)

/-- **`selfProductMap` is full as soon as `I` is full and faithful and `J` is faithful.** The two
components of a morphism of the target between images have preimages under `I`, which lie over the
same base morphism because `I` is strictly over `𝒞`; that the pair is a morphism of the source is
the compatibility square of the given one read through `J`, since
`CategoryTheory.TwoFibreProductOver.map_comp_map_eq_of_natIso` expresses `f'` on an `I`-image by
`J` conjugated with `E`, and `J` is faithful. -/
instance full_selfProductMap [I.Full] [I.Faithful] [J.Faithful] :
    (selfProductMap hI hJ E hE).Full where
  map_surjective {P Q} Φ := by
    have hax : p𝒳'.IsHomLift Φ.hbase (I.map (I.preimage Φ.a)) := by
      rw [I.map_preimage]; exact Φ.ha
    have hbx : p𝒳'.IsHomLift Φ.hbase (I.map (I.preimage Φ.b)) := by
      rw [I.map_preimage]; exact Φ.hb
    have ha : p𝒳.IsHomLift Φ.hbase (I.preimage Φ.a) :=
      have := hax
      Functor.isHomLift_of_isHomLift_map hI Φ.hbase (I.preimage Φ.a)
    have hb : p𝒳.IsHomLift Φ.hbase (I.preimage Φ.b) :=
      have := hbx
      Functor.isHomLift_of_isHomLift_map hI Φ.hbase (I.preimage Φ.b)
    have nA := E.hom.naturality (I.preimage Φ.a)
    have nB := E.hom.naturality (I.preimage Φ.b)
    simp only [Functor.comp_map, I.map_preimage] at nA nB
    have h := Φ.w
    simp only [selfProductMap_obj_iso_hom] at h
    have h2 := congrArg (fun t => E.hom.app P.x ≫ t ≫ E.inv.app Q.y) h
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc] at h2
    refine ⟨⟨Φ.hbase, I.preimage Φ.a, I.preimage Φ.b, ha, hb, ?_⟩, ?_⟩
    · refine J.map_injective ?_
      have e1 : J.map (f.map (I.preimage Φ.a)) = E.hom.app P.x ≫ f'.map Φ.a ≫ E.inv.app Q.x := by
        rw [← Category.assoc, ← nA, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      have e2 : J.map (f.map (I.preimage Φ.b)) = E.hom.app P.y ≫ f'.map Φ.b ≫ E.inv.app Q.y := by
        rw [← Category.assoc, ← nB, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      simp only [Functor.map_comp, e1, e2]
      simpa using h2
    · exact Hom.ext' (I.map_preimage _) (I.map_preimage _)

/-- `selfProductMap` is strictly over `𝒞`: it changes neither the base object of an object nor
the base morphism of a morphism. -/
lemma selfProductMap_comp_structureFunctor :
    selfProductMap hI hJ E hE ⋙ structureFunctor p𝒳' p𝒳' p𝒴' f' f' =
      structureFunctor p𝒳 p𝒳 p𝒴 f f :=
  rfl

end SelfProductMap

section Filler

/-- **The 2-cell filling the diagonal square**, in the direction
`Δ_f ⋙ selfProductMap ≅ I ⋙ Δ_{f'}`. Both components of each of its components are identities:
the image of `Δ_f x = (x, x, 𝟙)` under `selfProductMap` is `(I x, I x, E_x⁻¹ ≫ J 𝟙 ≫ E_x)`, and
`E_x⁻¹ ≫ E_x` is the identity, so that object carries the same data as `Δ_{f'} (I x)`. -/
noncomputable def selfProductDiagonalFillerApp (hf : f ⋙ p𝒴 = p𝒳) (hf' : f' ⋙ p𝒴' = p𝒳')
    (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
    (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x)) (x : 𝒳) :
    (selfProductMap hI hJ E hE).obj ((diagonal hf).obj x) ≅ (diagonal hf').obj (I.obj x) :=
  isoMkVertical (U := p𝒳.obj x) (Iso.refl (I.obj x)) (Iso.refl (I.obj x))
    (IsHomLift.id (Functor.congr_obj hI x)) (IsHomLift.id (Functor.congr_obj hI x))
    (by simp)

attribute [local instance_reducible] selfProductDiagonalFillerApp

/-- The first component of `selfProductDiagonalFillerApp` at `x` is the identity of `I.obj x`. -/
@[simp] lemma selfProductDiagonalFillerApp_hom_a (hf : f ⋙ p𝒴 = p𝒳) (hf' : f' ⋙ p𝒴' = p𝒳')
    (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
    (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x)) (x : 𝒳) :
    (selfProductDiagonalFillerApp hf hf' hI hJ E hE x).hom.a = 𝟙 (I.obj x) := rfl

/-- The second component of `selfProductDiagonalFillerApp` at `x` is the identity of `I.obj x`. -/
@[simp] lemma selfProductDiagonalFillerApp_hom_b (hf : f ⋙ p𝒴 = p𝒳) (hf' : f' ⋙ p𝒴' = p𝒳')
    (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
    (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x)) (x : 𝒳) :
    (selfProductDiagonalFillerApp hf hf' hI hJ E hE x).hom.b = 𝟙 (I.obj x) := rfl

/-- **The 2-cell filling the diagonal square**, assembled from
`CategoryTheory.TwoFibreProductOver.selfProductDiagonalFillerApp`. Naturality holds because both
components of the image of a morphism under either route are its image under `I`. -/
noncomputable def selfProductDiagonalFiller (hf : f ⋙ p𝒴 = p𝒳) (hf' : f' ⋙ p𝒴' = p𝒳')
    (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
    (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x)) :
    diagonal hf ⋙ selfProductMap hI hJ E hE ≅ I ⋙ diagonal hf' :=
  NatIso.ofComponents (selfProductDiagonalFillerApp hf hf' hI hJ E hE)
    (fun φ => by refine Hom.ext' ?_ ?_ <;> simp)

variable (hf : f ⋙ p𝒴 = p𝒳) (hf' : f' ⋙ p𝒴' = p𝒳')
  (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
  (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x))

/-- The first component of the component at `x` of `selfProductDiagonalFiller` is the identity of
`I.obj x`. -/
@[simp] lemma selfProductDiagonalFiller_hom_app_a (x : 𝒳) :
    ((selfProductDiagonalFiller hf hf' hI hJ E hE).hom.app x).a = 𝟙 (I.obj x) := rfl

/-- The second component of the component at `x` of `selfProductDiagonalFiller` is the identity
of `I.obj x`. -/
@[simp] lemma selfProductDiagonalFiller_hom_app_b (x : 𝒳) :
    ((selfProductDiagonalFiller hf hf' hI hJ E hE).hom.app x).b = 𝟙 (I.obj x) := rfl

/-- Every component of `CategoryTheory.TwoFibreProductOver.selfProductDiagonalFiller` is
vertical: both of its own components are identities, and a morphism of a 2-fibre product over
`𝒞` lies over a morphism of the base as soon as its first component does. -/
lemma isHomLift_selfProductDiagonalFiller (x : 𝒳) :
    (structureFunctor p𝒳' p𝒳' p𝒴' f' f').IsHomLift (𝟙 (p𝒳.obj x))
      ((selfProductDiagonalFiller hf hf' hI hJ E hE).hom.app x) :=
  structureFunctor_isHomLift _ (𝟙 (p𝒳.obj x)) (by
    rw [selfProductDiagonalFiller_hom_app_a]
    exact IsHomLift.id (Functor.congr_obj hI x))

end Filler

section Comparison

/-- The explicit 2-fibre product of the cospan `(selfProductMap, Δ_{f'})`: an object is an
object `u` of `𝒳 ×_𝒴 𝒳`, an object `v` of `𝒳'` over the same base, and a vertical isomorphism
between the image of `u` and the diagonal of `v` in `𝒳' ×_{𝒴'} 𝒳'`. -/
abbrev SelfProductDiagonalPullback (hf' : f' ⋙ p𝒴' = p𝒳') (hI : I ⋙ p𝒳' = p𝒳)
    (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
    (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x)) : Type _ :=
  TwoFibreProductOver (structureFunctor p𝒳 p𝒳 p𝒴 f f) p𝒳'
    (structureFunctor p𝒳' p𝒳' p𝒴' f' f') (selfProductMap hI hJ E hE) (diagonal hf')

/-- **The comparison functor of the diagonal square.** It carries `x : 𝒳` to the object
`(Δ_f x, I x)` of the explicit 2-fibre product of the cospan `(selfProductMap, Δ_{f'})`, with
comparison isomorphism the component at `x` of
`CategoryTheory.TwoFibreProductOver.selfProductDiagonalFiller`. Stacks 0CBB, and the second
assertion of Stacks 0BPU, are the statement that it is an equivalence. -/
noncomputable def selfProductDiagonalComparison (hf : f ⋙ p𝒴 = p𝒳) (hf' : f' ⋙ p𝒴' = p𝒳')
    (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
    (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x)) :
    𝒳 ⥤ SelfProductDiagonalPullback hf' hI hJ E hE where
  obj x :=
    { base := p𝒳.obj x
      x := (diagonal hf).obj x
      y := I.obj x
      hx := rfl
      hy := Functor.congr_obj hI x
      iso := (selfProductDiagonalFiller hf hf' hI hJ E hE).app x
      vertical := isHomLift_selfProductDiagonalFiller hf hf' hI hJ E hE x }
  map {x y} φ :=
    { hbase := p𝒳.map φ
      a := (diagonal hf).map φ
      b := I.map φ
      ha := structureFunctor_isHomLift _ (p𝒳.map φ) (by
        rw [diagonal_map_a]
        exact IsHomLift.map (p := p𝒳) φ)
      hb :=
        have : p𝒳.IsHomLift (p𝒳.map φ) φ := IsHomLift.map (p := p𝒳) φ
        Functor.isHomLift_map_of_comp_eq hI (p𝒳.map φ) φ
      w := (selfProductDiagonalFiller hf hf' hI hJ E hE).hom.naturality φ }
  map_id x := by refine Hom.ext' ?_ ?_ <;> simp
  map_comp φ ψ := by refine Hom.ext' ?_ ?_ <;> simp

attribute [local instance_reducible] selfProductDiagonalComparison

variable (hf : f ⋙ p𝒴 = p𝒳) (hf' : f' ⋙ p𝒴' = p𝒳')
  (hI : I ⋙ p𝒳' = p𝒳) (hJ : J ⋙ p𝒴' = p𝒴) (E : f ⋙ J ≅ I ⋙ f')
  (hE : ∀ x : 𝒳, p𝒴'.IsHomLift (𝟙 (p𝒳.obj x)) (E.hom.app x))

/-- The comparison isomorphism of the image of `x` under `selfProductDiagonalComparison` is the
component at `x` of `selfProductDiagonalFiller`. -/
@[simp] lemma selfProductDiagonalComparison_obj_iso (x : 𝒳) :
    ((selfProductDiagonalComparison hf hf' hI hJ E hE).obj x).iso =
      (selfProductDiagonalFiller hf hf' hI hJ E hE).app x := rfl

/-- The first component of the comparison isomorphism of the image of `x` under
`selfProductDiagonalComparison` is the identity of `I.obj x`. -/
@[simp] lemma selfProductDiagonalComparison_obj_iso_hom_a (x : 𝒳) :
    ((selfProductDiagonalComparison hf hf' hI hJ E hE).obj x).iso.hom.a = 𝟙 (I.obj x) := rfl

/-- The second component of the comparison isomorphism of the image of `x` under
`selfProductDiagonalComparison` is the identity of `I.obj x`. -/
@[simp] lemma selfProductDiagonalComparison_obj_iso_hom_b (x : 𝒳) :
    ((selfProductDiagonalComparison hf hf' hI hJ E hE).obj x).iso.hom.b = 𝟙 (I.obj x) := rfl

/-- The first component of the image of `φ` under `selfProductDiagonalComparison` is `Δ_f φ`. -/
@[simp] lemma selfProductDiagonalComparison_map_a {x y : 𝒳} (φ : x ⟶ y) :
    ((selfProductDiagonalComparison hf hf' hI hJ E hE).map φ).a = (diagonal hf).map φ := rfl

/-- The second component of the image of `φ` under `selfProductDiagonalComparison` is `I.map φ`. -/
@[simp] lemma selfProductDiagonalComparison_map_b {x y : 𝒳} (φ : x ⟶ y) :
    ((selfProductDiagonalComparison hf hf' hI hJ E hE).map φ).b = I.map φ := rfl

/-- The comparison functor is strictly over `𝒞`. -/
lemma selfProductDiagonalComparison_comp_structureFunctor :
    selfProductDiagonalComparison hf hf' hI hJ E hE ⋙
        structureFunctor (structureFunctor p𝒳 p𝒳 p𝒴 f f) p𝒳'
          (structureFunctor p𝒳' p𝒳' p𝒴' f' f') (selfProductMap hI hJ E hE) (diagonal hf') =
      p𝒳 :=
  rfl

/-- The comparison functor is faithful as soon as `I` is: its `𝒳'`-component is `I` itself. -/
instance faithful_selfProductDiagonalComparison [I.Faithful] :
    (selfProductDiagonalComparison hf hf' hI hJ E hE).Faithful where
  map_injective h := I.map_injective (congrArg Hom.b h)

/-- The comparison functor is full as soon as `I` is full and faithful. A morphism
`(Δ_f x, I x) ⟶ (Δ_f y, I y)` of the pullback is a morphism `Φ_a : Δ_f x ⟶ Δ_f y` together with
`Φ_b : I x ⟶ I y`, and its compatibility square — both comparison isomorphisms being identities
— says that `I` carries *both* components of `Φ_a` to `Φ_b`. So the preimage of `Φ_b` under `I`
is both of them, and the morphism is its image. -/
instance full_selfProductDiagonalComparison [I.Full] [I.Faithful] :
    (selfProductDiagonalComparison hf hf' hI hJ E hE).Full where
  map_surjective {x y} Φ := by
    have hwa : I.map Φ.a.a = Φ.b :=
      (Category.comp_id (I.map Φ.a.a)).symm.trans
        ((congrArg Hom.a Φ.w).trans (Category.id_comp Φ.b))
    have hwb : I.map Φ.a.b = Φ.b :=
      (Category.comp_id (I.map Φ.a.b)).symm.trans
        ((congrArg Hom.b Φ.w).trans (Category.id_comp Φ.b))
    obtain ⟨γ, hγ⟩ := Functor.Full.map_surjective (F := I) Φ.b
    refine ⟨γ, Hom.ext' (Hom.ext' ?_ ?_) hγ⟩
    · change ((diagonal hf).map γ).a = Φ.a.a
      rw [diagonal_map_a]
      exact I.map_injective (hγ.trans hwa.symm)
    · change ((diagonal hf).map γ).b = Φ.a.b
      rw [diagonal_map_b]
      exact I.map_injective (hγ.trans hwb.symm)

/-- The comparison functor is essentially surjective as soon as `I` is full and faithful and `J`
is faithful.

Let `(u, v, θ)` be an object of the pullback, with `u = (x, y, φ)`. The two components
`a : I x ≅ v` and `b : I y ≅ v` of `θ` compose to an isomorphism `I x ≅ I y`, whose preimage
`γ : x ≅ y` satisfies `f' (I γ) = E_x⁻¹ ≫ J φ ≫ E_y` by the compatibility square of `θ`, while
naturality of `E` at `γ` evaluates the left-hand side as `E_x⁻¹ ≫ J (f γ) ≫ E_y`. So
`J (f γ) = J φ`, hence `f γ = φ` because `J` is faithful, and
`CategoryTheory.TwoFibreProductOver.homDiagonal` turns that into an isomorphism `Δ_f x ≅ u`
whose first component is an identity and whose second is `γ`. Paired with `a` it is an
isomorphism from the image of `x` to the given object. -/
instance essSurj_selfProductDiagonalComparison [I.Full] [I.Faithful] [J.Faithful] :
    (selfProductDiagonalComparison hf hf' hI hJ E hE).EssSurj where
  mem_essImage W := by
    -- both components of the comparison isomorphism are invertible, being its images under the
    -- two projections of the self-product
    let aIso : I.obj W.x.x ≅ W.y := (fst p𝒳' p𝒳' p𝒴' f' f').mapIso W.iso
    let bIso : I.obj W.x.y ≅ W.y := (snd p𝒳' p𝒳' p𝒴' f' f').mapIso W.iso
    let γIso : W.x.x ≅ W.x.y := I.preimageIso (aIso ≪≫ bIso.symm)
    have hγ : I.map γIso.hom = W.iso.hom.a ≫ W.iso.inv.b := I.map_preimage _
    have hb : W.iso.hom.b ≫ W.iso.inv.b = 𝟙 (I.obj W.x.y) := bIso.hom_inv_id
    have hb' : W.iso.inv.b ≫ W.iso.hom.b = 𝟙 W.y := bIso.inv_hom_id
    have hbf : f'.map W.iso.hom.b ≫ f'.map W.iso.inv.b = 𝟙 (f'.obj (I.obj W.x.y)) :=
      (f'.map_comp _ _).symm.trans ((congrArg f'.map hb).trans (f'.map_id _))
    -- the compatibility square of the comparison isomorphism, read on `I γ`
    have hw : f'.map W.iso.hom.a ≫ 𝟙 (f'.obj W.y) =
        (E.inv.app W.x.x ≫ J.map W.x.iso.hom ≫ E.hom.app W.x.y) ≫
          f'.map W.iso.hom.b := W.iso.hom.w
    have h1 : f'.map W.iso.hom.a =
        (E.inv.app W.x.x ≫ J.map W.x.iso.hom ≫ E.hom.app W.x.y) ≫
          f'.map W.iso.hom.b := (Category.comp_id _).symm.trans hw
    have key : f'.map (I.map γIso.hom) =
        E.inv.app W.x.x ≫ J.map W.x.iso.hom ≫ E.hom.app W.x.y :=
      (congrArg f'.map hγ).trans <|
        (f'.map_comp _ _).trans <|
          (congrArg (· ≫ f'.map W.iso.inv.b) h1).trans <|
            (Category.assoc _ _ _).trans <|
              (congrArg
                (fun t => (E.inv.app W.x.x ≫ J.map W.x.iso.hom ≫ E.hom.app W.x.y) ≫ t)
                hbf).trans (Category.comp_id _)
    have hJfγ : J.map (f.map γIso.hom) = J.map W.x.iso.hom := by
      have h2 : E.inv.app W.x.x ≫ J.map (f.map γIso.hom) ≫ E.hom.app W.x.y =
          E.inv.app W.x.x ≫ J.map W.x.iso.hom ≫ E.hom.app W.x.y := by
        rw [← map_comp_map_eq_of_natIso E γIso.hom, key]
      have h3 := congrArg (fun t => E.hom.app W.x.x ≫ t ≫ E.inv.app W.x.y) h2
      simpa using h3
    have hfγ : f.map γIso.hom = W.x.iso.hom := J.map_injective hJfγ
    -- the isomorphism `Δ_f x ≅ u` it carries, exactly as in `essImage_diagonal`
    have h₁ : IsIso (homDiagonal hf W.x γIso.hom hfγ).hbase := by
      rw [homDiagonal_hbase]; infer_instance
    have h₂ : IsIso (homDiagonal hf W.x γIso.hom hfγ).a := by
      rw [homDiagonal_a]; exact IsIso.id W.x.x
    have h₃ : IsIso (homDiagonal hf W.x γIso.hom hfγ).b := by
      rw [homDiagonal_b]
      exact ⟨⟨γIso.inv, γIso.hom_inv_id, γIso.inv_hom_id⟩⟩
    have hD : IsIso (homDiagonal hf W.x γIso.hom hfγ) :=
      isIso_of_components (homDiagonal hf W.x γIso.hom hfγ)
    refine ⟨W.x.x, ⟨isoMkVertical (U := W.base)
      (asIso (homDiagonal hf W.x γIso.hom hfγ)) aIso
      (structureFunctor_isHomLift _ (𝟙 W.base) (by
        change p𝒳.IsHomLift (𝟙 W.base) (homDiagonal hf W.x γIso.hom hfγ).a
        rw [homDiagonal_a]
        exact IsHomLift.id (W.x.hx.trans W.hx)))
      (isHomLift_a W.iso.hom (𝟙 W.base) W.vertical) (Hom.ext' ?_ ?_)⟩⟩
    · exact (congrArg (· ≫ W.iso.hom.a) (I.map_id W.x.x)).trans
        (congrArg (fun t => t ≫ W.iso.hom.a) rfl)
    · exact (congrArg (· ≫ W.iso.hom.b) hγ).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (fun t => W.iso.hom.a ≫ t) hb').trans <|
            (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Stacks 0CBB over the base `𝒞`, with a growing target.** For a square of categories over
`𝒞` commuting up to a vertical isomorphism `E : f ⋙ J ≅ I ⋙ f'` with `I` fully faithful and `J`
faithful, the square comparing the relative diagonal of `f` with that of `f'` is 2-cartesian:
the comparison functor into the explicit 2-fibre product of the cospan is an equivalence.

The case `𝒴 = 𝒴'`, `J = 𝟙`, `E = 𝟙` is the source's Stacks 0CBB for `𝒳 ⟶ 𝒳' ⟶ 𝒴`; the general
case is what the second assertion of Stacks 0BPU needs, where `J` is a thickening of the target
and hence fully faithful. -/
theorem isEquivalence_selfProductDiagonalComparison [I.Full] [I.Faithful] [J.Faithful] :
    (selfProductDiagonalComparison hf hf' hI hJ E hE).IsEquivalence where

end Comparison

end CategoryTheory.TwoFibreProductOver

end
