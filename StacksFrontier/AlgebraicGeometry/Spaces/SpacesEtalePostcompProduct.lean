module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcomp

/-!
# The base change of an étale morphism, read over the base, is a product

Let `τ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Then `U` itself is an object of the spaces-étale site of `X`, and for every
object `V` of that site there are two readings of the fibre product `V ×_X U`:

* base change along `τ`, which produces an object of the spaces-étale site of `U`, followed by
  postcomposition with `τ`, which reads that object back over `X`; and
* the binary product `U ⨯ V` of the spaces-étale site of `X`, whose terminal object is the
  identity of `X` and whose fibre products are those of the underlying algebraic spaces.

This file identifies the two: the postcomposition along `τ` of the base change of `V` along
`τ`, with the structure morphism of the base change as its projection to `U` and the cartesian
projection of the base change as its projection to `V`, **is** the binary product of `U` with
`V` in the spaces-étale site of `X`.

## Main definitions

* `AlgebraicGeometry.Space.etaleOverObj` is the source of an étale morphism `τ : U ⟶ X`, read
  as an object of the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.postcompBaseChangeFst` and
  `AlgebraicGeometry.Space.postcompBaseChangeSnd` are the two projections.

## Main results

* `AlgebraicGeometry.Space.isLimitBinaryFanOfIsPullbackOverEtale`: a cartesian square over `τ`
  in the underlying algebraic spaces exhibits a binary product of the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.isLimitBinaryFanPostcompBaseChange`: the two projections exhibit the
  postcomposed base change as the binary product `U ⨯ V`.
* `AlgebraicGeometry.Space.postcompBaseChange_map_fst` and
  `AlgebraicGeometry.Space.postcompBaseChange_map_snd`: the two projections are natural in `V`,
  the first one being constant and the second one lying over the morphism of the site.  Together
  with the previous result this says that the composite functor is a binary-product functor
  `V ↦ U ⨯ V`, with the projections as its structure maps.
* `AlgebraicGeometry.Space.isPullback_postcompBaseChange_isTerminal`: the same statement in the
  cartesian form, as a fibre product over the terminal object of the site.

## Implementation notes

The statement is made for an arbitrary cartesian base-change datum
`AlgebraicGeometry.Space.SpacesBaseChange`, not only for the canonical one
`AlgebraicGeometry.Space.spacesBaseChange`, because that is the shape in which the datum's
existing consumers hold it and because the chosen fibre products of two base changes need not
be equal on the nose.  Only the two fields `projection` and `isPullback` of the datum are used:
the universal property of the product is deduced from the universal property of the cartesian
square, so no product API of the spaces-étale site — and in particular no
`CategoryTheory.Limits.HasBinaryProducts` instance — is needed, and the result holds for the
chosen fibre products of any such datum.

What makes the identification possible without any further geometry is that a morphism of the
spaces-étale site of `X` to `U` read as an object over `X` is exactly a morphism of algebraic
spaces to `U` over `X`, i.e. a factorization of the structure morphism through `τ`; the two
projections of the product are then the two legs of the cartesian square, and the lift of a
pair of morphisms is the lift of the square.  Étaleness of `τ` enters only in making `U` an
object of the site at all.

Everything is therefore proved first for an abstract object `Z` of the site equipped with two
morphisms whose underlying square is cartesian, where no composite of functors appears in any
type, and the postcomposed base change is fed to it once, in
`AlgebraicGeometry.Space.isPullback_postcompBaseChange`, which is the single declaration that
has to identify `((spacesEtalePostcomp τ hτ).obj (bc.functor.obj V)).obj.left` with the fibre
product the datum's cartesian square is about.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U : AlgebraicSpaces B S hS}

/-- The source of an étale morphism `τ : U ⟶ X`, read as an object of the spaces-étale site
of `X`. -/
abbrev etaleOverObj (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom) : SpacesEtale B S hS X :=
  ⟨Over.mk τ, hτ⟩

variable (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)

/-! ### The product from a cartesian square over `τ` -/

/-- A morphism of the spaces-étale site of `X` to `U` and a morphism to `V` have the same
composite to `X`, which is the common structure morphism of their source. -/
theorem etaleOver_lift_w {V W : SpacesEtale B S hS X} (x : W ⟶ etaleOverObj B S hS τ hτ)
    (y : W ⟶ V) :
    y.hom.left ≫ V.1.hom = x.hom.left ≫ τ :=
  (Over.w y.hom).trans (Over.w x.hom).symm

variable {Z V : SpacesEtale B S hS X} (pU : Z ⟶ etaleOverObj B S hS τ hτ) (pV : Z ⟶ V)

/-- The lift of a pair of morphisms through two morphisms of the site whose underlying square
over `τ` is cartesian: the lift of that square. -/
noncomputable def isPullbackOverEtaleLift
    (h : IsPullback pV.hom.left pU.hom.left V.1.hom τ) {W : SpacesEtale B S hS X}
    (x : W ⟶ etaleOverObj B S hS τ hτ) (y : W ⟶ V) : W ⟶ Z :=
  ObjectProperty.homMk (Over.homMk
    (h.lift y.hom.left x.hom.left (etaleOver_lift_w B S hS τ hτ x y))
    (by rw [← Over.w pU.hom, ← Category.assoc, h.lift_snd]; exact Over.w x.hom))

/-- The lift `isPullbackOverEtaleLift` composed with the leg to `U` is the first given morphism. -/
@[simp]
theorem isPullbackOverEtaleLift_fst (h : IsPullback pV.hom.left pU.hom.left V.1.hom τ)
    {W : SpacesEtale B S hS X} (x : W ⟶ etaleOverObj B S hS τ hτ) (y : W ⟶ V) :
    isPullbackOverEtaleLift B S hS τ hτ pU pV h x y ≫ pU = x :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (h.lift_snd _ _ _))

/-- The lift `isPullbackOverEtaleLift` composed with the leg to `V` is the second given
morphism. -/
@[simp]
theorem isPullbackOverEtaleLift_snd (h : IsPullback pV.hom.left pU.hom.left V.1.hom τ)
    {W : SpacesEtale B S hS X} (x : W ⟶ etaleOverObj B S hS τ hτ) (y : W ⟶ V) :
    isPullbackOverEtaleLift B S hS τ hτ pU pV h x y ≫ pV = y :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (h.lift_fst _ _ _))

/-- A morphism into the source of a cartesian square over `τ` is determined by its composites
with the two legs. -/
theorem isPullbackOverEtale_hom_ext (h : IsPullback pV.hom.left pU.hom.left V.1.hom τ)
    {W : SpacesEtale B S hS X} {m m' : W ⟶ Z} (h₁ : m ≫ pU = m' ≫ pU)
    (h₂ : m ≫ pV = m' ≫ pV) :
    m = m' :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (h.hom_ext
    (congrArg (fun k ↦ k.hom.left) h₂) (congrArg (fun k ↦ k.hom.left) h₁)))

/-- **The product comparison of the proof of Stacks 03M8, in the abstract form it is used in.**
Let `τ : U ⟶ X` be an étale morphism of algebraic spaces, let `V` and `Z` be objects of the
spaces-étale site of `X`, and let `pU : Z ⟶ U` and `pV : Z ⟶ V` be morphisms of that site
whose underlying square

```
Z ⟶ V
↓    ↓
U ⟶ X
```

of algebraic spaces is cartesian.  Then `pU` and `pV` exhibit `Z` as the binary product
`U ⨯ V` of the spaces-étale site of `X`.

No product API of the site is used: the universal property of the product is the universal
property of the cartesian square, because a morphism of the site into `U` read as an object
over `X` is exactly a factorization of the structure morphism through `τ`. -/
noncomputable def isLimitBinaryFanOfIsPullbackOverEtale
    (h : IsPullback pV.hom.left pU.hom.left V.1.hom τ) :
    IsLimit (BinaryFan.mk pU pV) :=
  BinaryFan.isLimitMk
    (fun s ↦ isPullbackOverEtaleLift B S hS τ hτ pU pV h s.fst s.snd)
    (fun s ↦ isPullbackOverEtaleLift_fst B S hS τ hτ pU pV h s.fst s.snd)
    (fun s ↦ isPullbackOverEtaleLift_snd B S hS τ hτ pU pV h s.fst s.snd)
    (fun s _m h₁ h₂ ↦ isPullbackOverEtale_hom_ext B S hS τ hτ pU pV h
      (h₁.trans (isPullbackOverEtaleLift_fst B S hS τ hτ pU pV h s.fst s.snd).symm)
      (h₂.trans (isPullbackOverEtaleLift_snd B S hS τ hτ pU pV h s.fst s.snd).symm))

/-- The same statement in the cartesian form: the two legs of a cartesian square over `τ`
exhibit its source as the fibre product of `U` and `V` over any terminal object of the
spaces-étale site of `X` — for instance over the identity of `X`.

This is the form the one-element sheaf condition of Stacks 03H7 consumes. -/
theorem isPullback_isTerminal_of_isPullbackOverEtale
    (h : IsPullback pV.hom.left pU.hom.left V.1.hom τ) {T : SpacesEtale B S hS X}
    (hT : IsTerminal T) :
    IsPullback pU pV (hT.from (etaleOverObj B S hS τ hτ)) (hT.from V) :=
  IsPullback.of_is_product' (isLimitBinaryFanOfIsPullbackOverEtale B S hS τ hτ pU pV h) hT

/-! ### The postcomposed base change -/

section

variable (bc : SpacesBaseChange B S hS τ)

/-- The projection of the postcomposed base change of `V` to `U`: the structure morphism of the
base change, read as a triangle over `X`. -/
noncomputable def postcompBaseChangeFst (V : SpacesEtale B S hS X) :
    (spacesEtalePostcomp B S hS τ hτ).obj (bc.functor.obj V) ⟶ etaleOverObj B S hS τ hτ :=
  ObjectProperty.homMk (Over.homMk (bc.functor.obj V).1.hom rfl)

/-- The projection of the postcomposed base change of `V` to `V`: the cartesian projection of
the base change, read as a triangle over `X`. -/
noncomputable def postcompBaseChangeSnd (V : SpacesEtale B S hS X) :
    (spacesEtalePostcomp B S hS τ hτ).obj (bc.functor.obj V) ⟶ V :=
  ObjectProperty.homMk (Over.homMk (bc.projection.app V) (bc.isPullback V).w)

/-- The underlying square of the two projections of the postcomposed base change is the
cartesian square of the base-change datum.

This is the one declaration that identifies the underlying algebraic space of
`(spacesEtalePostcomp τ hτ).obj (bc.functor.obj V)` with the one the datum's square is about;
postcomposition with `τ` changes neither it nor the two morphisms. -/
theorem isPullback_postcompBaseChange (V : SpacesEtale B S hS X) :
    IsPullback (postcompBaseChangeSnd B S hS τ hτ bc V).hom.left
      (postcompBaseChangeFst B S hS τ hτ bc V).hom.left V.1.hom τ :=
  bc.isPullback V

/-- **The product comparison of the proof of Stacks 03M8.**  Let `τ : U ⟶ X` be an étale
morphism of algebraic spaces and let `V` be an object of the spaces-étale site of `X`.  Then
the base change of `V` along `τ`, read back over `X` by postcomposition with `τ`, is the
binary product `U ⨯ V` of the spaces-étale site of `X`: the structure morphism of the base
change is the projection to `U`, the cartesian projection of the base change is the projection
to `V`, and that fan is a limit.

Equivalently, and this is how the proof of Stacks 03M8 uses it, the sections of a sheaf on the
spaces-étale site of `X` over the product `U ⨯ V` are its sections over the fibre product
`V ×_X U`, read over `U`. -/
noncomputable def isLimitBinaryFanPostcompBaseChange (V : SpacesEtale B S hS X) :
    IsLimit (BinaryFan.mk (postcompBaseChangeFst B S hS τ hτ bc V)
      (postcompBaseChangeSnd B S hS τ hτ bc V)) :=
  isLimitBinaryFanOfIsPullbackOverEtale B S hS τ hτ _ _
    (isPullback_postcompBaseChange B S hS τ hτ bc V)

/-- **The product comparison of the proof of Stacks 03M8, in cartesian form.**  The two
projections of the postcomposed base change exhibit it as the fibre product of `U` and `V`
over the terminal object of the spaces-étale site of `X`, which is the identity of `X`. -/
theorem isPullback_postcompBaseChange_isTerminal {T : SpacesEtale B S hS X} (hT : IsTerminal T)
    (V : SpacesEtale B S hS X) :
    IsPullback (postcompBaseChangeFst B S hS τ hτ bc V)
      (postcompBaseChangeSnd B S hS τ hτ bc V) (hT.from (etaleOverObj B S hS τ hτ))
      (hT.from V) :=
  isPullback_isTerminal_of_isPullbackOverEtale B S hS τ hτ _ _
    (isPullback_postcompBaseChange B S hS τ hτ bc V) hT

/-- The projection to `U` is natural in `V`, being constant: the composite of the base change
of a morphism `k : V ⟶ V'` with the structure morphism of the base change of `V'` is the
structure morphism of the base change of `V`. -/
@[simp]
theorem postcompBaseChange_map_fst {V V' : SpacesEtale B S hS X} (k : V ⟶ V') :
    (spacesEtalePostcomp B S hS τ hτ).map (bc.functor.map k) ≫
        postcompBaseChangeFst B S hS τ hτ bc V' =
      postcompBaseChangeFst B S hS τ hτ bc V :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (Over.w (bc.functor.map k).hom))

/-- The projection to `V` is natural in `V`: the cartesian projections of a base change form a
natural transformation, which is the field
`AlgebraicGeometry.Space.SpacesBaseChange.projection` of the datum. -/
@[simp]
theorem postcompBaseChange_map_snd {V V' : SpacesEtale B S hS X} (k : V ⟶ V') :
    (spacesEtalePostcomp B S hS τ hτ).map (bc.functor.map k) ≫
        postcompBaseChangeSnd B S hS τ hτ bc V' =
      postcompBaseChangeSnd B S hS τ hτ bc V ≫ k :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (bc.projection.naturality k))

end

/-! ### Change of the étale morphism -/

section

variable {R : AlgebraicSpaces B S hS} {ρ : R ⟶ X} (hρ : IsEtale B S hS ρ.hom) (θ : R ⟶ U)
    (hθ : θ ≫ τ = ρ) (bcρ : SpacesBaseChange B S hS ρ) (bcτ : SpacesBaseChange B S hS τ)

/-- A morphism `θ : R ⟶ U` of algebraic spaces whose composite with `τ` is `ρ`, read as a
morphism `R ⟶ U` of the spaces-étale site of `X`. -/
abbrev etaleOverMap : etaleOverObj B S hS ρ hρ ⟶ etaleOverObj B S hS τ hτ :=
  ObjectProperty.homMk (Over.homMk θ hθ)

/-- The morphism induced by `θ` on the postcomposed base changes: the base change of `V` along
`ρ`, read over `X`, maps to the base change of `V` along `τ`, read over `X`, over `θ` and over
the identity of `V`.

In the proof of Stacks 03M8 this is the arrow `V ×_Y R ⟶ V ×_Y U` induced by one of the two
projections `t, s : R ⟶ U` of the relation of an étale chart. -/
noncomputable def postcompBaseChangeOverMap (V : SpacesEtale B S hS X) :
    (spacesEtalePostcomp B S hS ρ hρ).obj (bcρ.functor.obj V) ⟶
      (spacesEtalePostcomp B S hS τ hτ).obj (bcτ.functor.obj V) :=
  isPullbackOverEtaleLift B S hS τ hτ (postcompBaseChangeFst B S hS τ hτ bcτ V)
    (postcompBaseChangeSnd B S hS τ hτ bcτ V)
    (isPullback_postcompBaseChange B S hS τ hτ bcτ V)
    (postcompBaseChangeFst B S hS ρ hρ bcρ V ≫ etaleOverMap B S hS τ hτ hρ θ hθ)
    (postcompBaseChangeSnd B S hS ρ hρ bcρ V)

/-- The morphism `postcompBaseChangeOverMap` lies over `θ`: composed with the projection to `U`
it is the projection to `R` followed by `θ`. -/
@[reassoc (attr := simp)]
theorem postcompBaseChangeOverMap_fst (V : SpacesEtale B S hS X) :
    postcompBaseChangeOverMap B S hS τ hτ hρ θ hθ bcρ bcτ V ≫
        postcompBaseChangeFst B S hS τ hτ bcτ V =
      postcompBaseChangeFst B S hS ρ hρ bcρ V ≫ etaleOverMap B S hS τ hτ hρ θ hθ :=
  isPullbackOverEtaleLift_fst B S hS τ hτ _ _ _ _ _

/-- The morphism `postcompBaseChangeOverMap` lies over the identity of `V`: it commutes with the
two projections to `V`. -/
@[reassoc (attr := simp)]
theorem postcompBaseChangeOverMap_snd (V : SpacesEtale B S hS X) :
    postcompBaseChangeOverMap B S hS τ hτ hρ θ hθ bcρ bcτ V ≫
        postcompBaseChangeSnd B S hS τ hτ bcτ V =
      postcompBaseChangeSnd B S hS ρ hρ bcρ V :=
  isPullbackOverEtaleLift_snd B S hS τ hτ _ _ _ _ _

end

end AlgebraicGeometry.Space

end
