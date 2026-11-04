module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningFunctorial

/-!
# Base change of the universal first-order thickening of algebraic spaces

Let `g : X ⟶ Y` and `q : W' ⟶ Y` be morphisms of algebraic spaces over a scheme `S`, let
`W ⊆ W'` be a subfunctor and write `Z' = X ×_Y W'` for the fibre product, `r : Z' ⟶ W'` and
`p : Z' ⟶ X` for its projections and `Z = r⁻¹(W)` for the inverse image of `W`, which is the
fibre product `X ×_Y W`.  So the square

```
  Z --h--→ X
  |        |
  f        g
  ↓        ↓
  W --h'-→ Y
```

with `h = Z.ι ≫ p.hom` and `h' = W.ι ≫ q.hom` is cartesian.  Stacks 060B asserts that if `h'`
is formally unramified then so is `h`, that if `W ⊂ W'` is the universal first-order thickening
of `W` over `Y` then `Z ⊂ Z'` is the universal first-order thickening of `Z` over `X`, and that
consequently the canonical map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of Stacks 060A is surjective.

Stacks 060C sharpens the last two of those assertions when `g` is flat: the induced morphism
`r : X ×_Y W' ⟶ W'` of universal first-order thickenings is then flat, and the canonical map of
conormal sheaves is not merely surjective but an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeThickening`: the fibre product `X ×_Y W'`, with its two
  projections `AlgebraicGeometry.Space.baseChangeThickeningFst` and
  `AlgebraicGeometry.Space.baseChangeThickeningSnd`.
* `AlgebraicGeometry.Space.baseChangeSub`: the inverse image `r⁻¹(W) = X ×_Y W`, as a subfunctor
  of `X ×_Y W'`.
* `AlgebraicGeometry.Space.universalThickeningBaseChangeProjection`: the projection
  `X ×_Y W ⟶ W`, the morphism `f`
  of the square.

## Main results

* `AlgebraicGeometry.Space.formallyUnramified_of_isPullback`: **Stacks 060B, the first
  assertion** (Stacks 0600), for an arbitrary fibre product diagram: `h` is formally unramified
  when `h'` is.  `AlgebraicGeometry.Space.formallyUnramified_baseChangeSub` is the case of the
  square `X ×_Y W = r⁻¹(W)` of the second assertion.
* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_baseChange`: **Stacks 060B, the
  second assertion**: `X ×_Y W ⊂ X ×_Y W'` is the universal first-order thickening of
  `X ×_Y W` over `X`.
* `AlgebraicGeometry.Space.universalThickeningMap_baseChange`: the canonical morphism of
  Stacks 060A attached to the square is the projection `r : X ×_Y W' ⟶ W'`.
* `AlgebraicGeometry.Space.epi_universalThickeningConormalMap_baseChange`: **Stacks 060B, the
  third assertion**: the induced map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of conormal modules is surjective.
* `AlgebraicGeometry.Space.isFirstOrderThickening_baseChangeSub`: `X ×_Y W ⊆ X ×_Y W'` is a
  first-order thickening, by Stacks 09ZX.
* `AlgebraicGeometry.Space.isFlat_baseChangeThickeningSnd`: **Stacks 060C, the first
  assertion**: if `g` is flat then so is the induced morphism `r : X ×_Y W' ⟶ W'` of universal
  first-order thickenings.
* `AlgebraicGeometry.Space.isIso_universalThickeningConormalMap_baseChange`: **Stacks 060C, the
  second assertion**: the induced map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of conormal modules is an
  isomorphism.  Its hypothesis is flatness of `g` in the chartwise sense of Stacks 03ML
  part (1), as in the source;
  `AlgebraicGeometry.Space.isIso_universalThickeningConormalMap_baseChange_of_isFlatRingedTopos`
  is the same conclusion from flatness of the induced morphism of small étale ringed topoi,
  which is the form the flat clause of Stacks 04CQ consumes.

## Implementation notes

**The fibre product is taken as an inverse image.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChange.lean`, the corner `X ×_Y W` of
the cartesian square is realized as the inverse image `r⁻¹(W)` inside `X ×_Y W'`; that it is the
fibre product of `X` and `W` over `Y` is the pasting of the two cartesian squares
`CategoryTheory.Subfunctor.isPullback_preimage` and
`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_fiberProduct`, which is what the proof of
the first assertion uses.  Writing `Z` as that inverse image is also what makes the third
assertion an instance of the surjectivity clause of Stacks 04CQ,
`AlgebraicGeometry.Space.epi_conormalMap`, which is stated for exactly that configuration.

**Formal unramifiedness of `h'` is not a hypothesis of the second and third assertions.**  The
source assumes `h'` formally unramified and then speaks of *the* universal first-order
thickening `W ⊂ W'` of `W` over `Y`, which exists by Stacks 0606; the second and third assertions
are stated for any universal first-order thickening `W ⊂ W'`, which is the source's "if" clause,
and they hold without formal unramifiedness of `h'`.

**The square-zero condition upstairs.**  That `Z = r⁻¹(W)` is a *first-order* thickening of
`Z' = X ×_Y W'` is part (2) of Stacks 09ZX — a base change of a first-order thickening is a
first-order thickening — along the morphism `r`, which is
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage`.

**The lifting property is the mapping property of the fibre product.**  A morphism `T' ⟶ X ×_Y W'`
is a pair of morphisms to `X` and to `W'` agreeing over `Y`.  The morphism to `X` is the one the
solid diagram already provides, and the morphism to `W'` is produced by the universal property
of `W ⊂ W'` applied to the pushed-forward diagram; uniqueness is uniqueness there plus the
uniqueness in the mapping property of the fibre product.

## References

* [Stacks Project, Tag 060B](https://stacks.math.columbia.edu/tag/060B)
* [Stacks Project, Tag 060C](https://stacks.math.columbia.edu/tag/060C)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 0600](https://stacks.math.columbia.edu/tag/0600)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y W' : AlgebraicSpaces B S hS}

/-! ### The base-changed thickening -/

/-- The fibre product `X ×_Y W'` of algebraic spaces over `S`. -/
noncomputable abbrev baseChangeThickening (q : W' ⟶ Y) (g : X ⟶ Y) : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS g q

/-- The projection `X ×_Y W' ⟶ X`, the structure morphism of the base-changed thickening. -/
noncomputable abbrev baseChangeThickeningFst (q : W' ⟶ Y) (g : X ⟶ Y) :
    baseChangeThickening B S hS q g ⟶ X :=
  ObjectProperty.homMk (pullback.fst g.hom q.hom)

/-- The projection `X ×_Y W' ⟶ W'`. -/
noncomputable abbrev baseChangeThickeningSnd (q : W' ⟶ Y) (g : X ⟶ Y) :
    baseChangeThickening B S hS q g ⟶ W' :=
  ObjectProperty.homMk (pullback.snd g.hom q.hom)

/-- The fibre product `X ×_Y W`, realized as the inverse image of `W ⊆ W'` along the projection
`X ×_Y W' ⟶ W'`. -/
noncomputable abbrev baseChangeSub (W : Subfunctor W'.obj) (q : W' ⟶ Y) (g : X ⟶ Y) :
    Subfunctor (baseChangeThickening B S hS q g).obj :=
  W.preimage (baseChangeThickeningSnd B S hS q g).hom

/-- The projection `X ×_Y W ⟶ W`, the morphism `f` of the square of Stacks 060B. -/
noncomputable abbrev universalThickeningBaseChangeProjection (W : Subfunctor W'.obj)
    (q : W' ⟶ Y) (g : X ⟶ Y) :
    (baseChangeSub B S hS W q g).toFunctor ⟶ W.toFunctor :=
  W.fromPreimage (baseChangeThickeningSnd B S hS q g).hom

variable (W : Subfunctor W'.obj) (q : W' ⟶ Y) (g : X ⟶ Y)

/-- The inclusion of `X ×_Y W` into `X ×_Y W'` followed by the projection to `W'` is the
projection `X ×_Y W ⟶ W` followed by the inclusion of `W`. -/
theorem baseChangeSub_ι_snd :
    (baseChangeSub B S hS W q g).ι ≫ (baseChangeThickeningSnd B S hS q g).hom =
      universalThickeningBaseChangeProjection B S hS W q g ≫ W.ι :=
  (Subfunctor.fromPreimage_ι W (baseChangeThickeningSnd B S hS q g).hom).symm

/-- The square of Stacks 060B commutes, in the form the universal property of Stacks 0602 and
the canonical morphism of Stacks 060A consume. -/
theorem baseChangeThickening_square :
    (baseChangeSub B S hS W q g).ι ≫
        (baseChangeThickeningFst B S hS q g).hom ≫ g.hom =
      universalThickeningBaseChangeProjection B S hS W q g ≫ W.ι ≫ q.hom := by
  rw [← Category.assoc, ← Category.assoc, ← baseChangeSub_ι_snd B S hS W q g,
    Category.assoc, Category.assoc]
  exact congrArg _ pullback.condition

/-! ### The first assertion: the base change is formally unramified -/

/-- **The first assertion of Stacks 060B, in the configuration of the second.**  In the cartesian
square `X ×_Y W = r⁻¹(W)`, if `h' : W ⟶ Y` is formally unramified then so is its base change
`h : X ×_Y W ⟶ X`.  The first assertion for an arbitrary fibre product diagram is
`AlgebraicGeometry.Space.formallyUnramified_of_isPullback`.

The square is cartesian because it is the pasting of the cartesian square exhibiting
`X ×_Y W = r⁻¹(W)` as a fibre product of `W` along `r` (Stacks 083Q) with the cartesian square
exhibiting `X ×_Y W'` as a fibre product (Stacks 02X2); the assertion is then Stacks 0600. -/
theorem formallyUnramified_baseChangeSub (closedW : IsClosedSubspace B S hS W)
    (unramified : FormallyUnramified (W.ι ≫ q.hom)) :
    FormallyUnramified ((baseChangeSub B S hS W q g).ι ≫
      (baseChangeThickeningFst B S hS q g).hom) := by
  have hZ : IsClosedSubspace B S hS (baseChangeSub B S hS W q g) :=
    isClosedSubspace_preimage B S hS (baseChangeThickeningSnd B S hS q g).hom W W'.2
      (baseChangeThickening B S hS q g).2 closedW
  let Ws : AlgebraicSpaces B S hS := ⟨W.toFunctor, closedW.1⟩
  let Zs : AlgebraicSpaces B S hS := ⟨(baseChangeSub B S hS W q g).toFunctor, hZ.1⟩
  have hleft : IsPullback
      (ObjectProperty.homMk (baseChangeSub B S hS W q g).ι :
        Zs ⟶ baseChangeThickening B S hS q g)
      (ObjectProperty.homMk (universalThickeningBaseChangeProjection B S hS W q g) : Zs ⟶ Ws)
      (baseChangeThickeningSnd B S hS q g)
      (ObjectProperty.homMk W.ι : Ws ⟶ W') :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T))
      (Subfunctor.isPullback_preimage (baseChangeThickeningSnd B S hS q g).hom W).flip
  exact formallyUnramified_of_isPullback B S hS
    ((ObjectProperty.homMk W.ι : Ws ⟶ W') ≫ q) g _ _
    (hleft.paste_horiz (AlgebraicSpaces.isPullback_fiberProduct B S hS g q)) unramified

/-! ### The second assertion: the base change is a universal first-order thickening -/

/-- **The square-zero condition upstairs.**  If `W ⊆ W'` is a universal first-order
thickening then its inverse image `X ×_Y W ⊆ X ×_Y W'` along the projection `r` is a first-order
thickening.

This is part (2) of Stacks 09ZX, `AlgebraicGeometry.Space.isFirstOrderThickening_preimage`,
which holds along an arbitrary morphism of algebraic spaces. -/
theorem isFirstOrderThickening_baseChangeSub
    (univW : IsUniversalFirstOrderThickening B S hS W q) :
    IsFirstOrderThickening B S hS (baseChangeThickening B S hS q g)
      (baseChangeSub B S hS W q g) :=
  isFirstOrderThickening_preimage B S hS W (baseChangeThickeningSnd B S hS q g) univW.firstOrder

/-- **Stacks 060B, the second assertion.**  Let `W ⊂ W'` be a universal first-order thickening
of `W` over `Y`, with structure morphism `q : W' ⟶ Y`, and let `g : X ⟶ Y` be a morphism of
algebraic spaces.  Then `X ×_Y W ⊂ X ×_Y W'` is a universal first-order thickening of
`X ×_Y W` over `X`, with structure morphism the projection `p : X ×_Y W' ⟶ X`.

A morphism `T' ⟶ X ×_Y W'` is a pair of morphisms to `X` and to `W'` agreeing over `Y`.  Given
a solid diagram over `X` built from a first-order thickening `T ⊂ T'` and a morphism
`T ⟶ X ×_Y W`, the morphism to `X` is the one the diagram supplies and the morphism to `W'` is
the unique one furnished by the universal property of `W ⊂ W'` for the diagram pushed forward
along `X ×_Y W ⟶ W`; uniqueness of the resulting morphism is uniqueness there together with the
mapping property of the fibre product.  That `X ×_Y W ⊆ X ×_Y W'` is a first-order thickening
is `AlgebraicGeometry.Space.isFirstOrderThickening_baseChangeSub`, from Stacks 09ZX. -/
@[stacks 060B "the second assertion: the base change of the universal first-order thickening is \
the universal first-order thickening of the base change"]
theorem isUniversalFirstOrderThickening_baseChange
    (univW : IsUniversalFirstOrderThickening B S hS W q) :
    IsUniversalFirstOrderThickening B S hS (baseChangeSub B S hS W q g)
      (baseChangeThickeningFst B S hS q g) := by
  refine ⟨isFirstOrderThickening_baseChangeSub B S hS W q g univW, ?_⟩
  intro T' T hT a b hcompat
  have hsnd := baseChangeSub_ι_snd B S hS W q g
  have hP : IsPullback (baseChangeThickeningFst B S hS q g).hom
      (baseChangeThickeningSnd B S hS q g).hom g.hom q.hom :=
    IsPullback.of_hasPullback g.hom q.hom
  -- Push the solid diagram forward along `X ×_Y W ⟶ W` and lift it by universality of `W'`.
  have hcompat' : T.ι ≫ b ≫ g.hom =
      (a ≫ universalThickeningBaseChangeProjection B S hS W q g) ≫ W.ι ≫ q.hom := by
    rw [← Category.assoc, hcompat]
    simp only [Category.assoc]
    rw [hP.w, ← Category.assoc ((baseChangeSub B S hS W q g).ι), hsnd, Category.assoc]
  obtain ⟨d, hd, hdu⟩ := univW.existsUnique_lift T hT
    (a ≫ universalThickeningBaseChangeProjection B S hS W q g) (b ≫ g.hom) hcompat'
  refine ⟨hP.lift b d hd.2.symm, ⟨?_, hP.lift_fst b d hd.2.symm⟩, ?_⟩
  · refine hP.hom_ext ?_ ?_
    · rw [Category.assoc, hP.lift_fst, Category.assoc]
      exact hcompat
    · rw [Category.assoc, hP.lift_snd, Category.assoc, hsnd, ← Category.assoc]
      exact hd.1
  · intro c hc
    have hdc : c ≫ (baseChangeThickeningSnd B S hS q g).hom = d := by
      refine hdu _ ⟨?_, ?_⟩
      · rw [← Category.assoc, hc.1, Category.assoc, hsnd, ← Category.assoc]
      · rw [Category.assoc, ← hP.w, ← Category.assoc, hc.2]
    exact hP.hom_ext (hc.2.trans (hP.lift_fst _ _ _).symm) (hdc.trans (hP.lift_snd _ _ _).symm)

/-! ### The third assertion: surjectivity of the map of conormal modules -/

/-- **The canonical morphism of Stacks 060A attached to the square of Stacks 060B is the
projection.**  For the cartesian square of the source, the unique morphism `X ×_Y W' ⟶ W'`
restricting to `X ×_Y W ⟶ W` and lying over `Y` is the projection `r`. -/
theorem universalThickeningMap_baseChange
    (univW : IsUniversalFirstOrderThickening B S hS W q) :
    universalThickeningMap B S hS g (universalThickeningBaseChangeProjection B S hS W q g)
        (isUniversalFirstOrderThickening_baseChange B S hS W q g univW) univW
        (baseChangeThickening_square B S hS W q g) =
      baseChangeThickeningSnd B S hS q g :=
  (eq_universalThickeningMap B S hS g (universalThickeningBaseChangeProjection B S hS W q g)
    (isUniversalFirstOrderThickening_baseChange B S hS W q g univW) univW
    (baseChangeThickening_square B S hS W q g) (baseChangeThickeningSnd B S hS q g)
    (baseChangeSub_ι_snd B S hS W q g)
    (ObjectProperty.hom_ext _ pullback.condition.symm)).symm

/-- The canonical map of conormal modules of Stacks 060A for the square of Stacks 060B is the
conormal map of the projection `r : X ×_Y W' ⟶ W'`. -/
private theorem universalThickeningConormalMap_baseChange_eq
    (univW : IsUniversalFirstOrderThickening B S hS W q) :
    ∃ hc, universalThickeningConormalMap B S hS g
        (universalThickeningBaseChangeProjection B S hS W q g)
        (isUniversalFirstOrderThickening_baseChange B S hS W q g univW) univW
        (baseChangeThickening_square B S hS W q g) =
      conormalMap B S hS
        ⟨baseChangeSub B S hS W q g,
          (IsNthOrderThickening.isThickening B S hS
            (isFirstOrderThickening_baseChangeSub B S hS W q g univW)).1⟩
        ⟨W, (IsNthOrderThickening.isThickening B S hS univW.firstOrder).1⟩
        (baseChangeThickeningSnd B S hS q g)
        (ObjectProperty.homMk (universalThickeningBaseChangeProjection B S hS W q g)) hc := by
  have key : ∀ (c : baseChangeThickening B S hS q g ⟶ W')
      (hc : subspaceInclusion B S hS (baseChangeThickening B S hS q g)
            ⟨baseChangeSub B S hS W q g,
              (IsNthOrderThickening.isThickening B S hS
                (isFirstOrderThickening_baseChangeSub B S hS W q g univW)).1⟩ ≫ c =
          (ObjectProperty.homMk (universalThickeningBaseChangeProjection B S hS W q g)) ≫
            subspaceInclusion B S hS W'
              ⟨W, (IsNthOrderThickening.isThickening B S hS univW.firstOrder).1⟩),
      c = baseChangeThickeningSnd B S hS q g → ∃ hc', conormalMap B S hS
        ⟨baseChangeSub B S hS W q g,
          (IsNthOrderThickening.isThickening B S hS
            (isFirstOrderThickening_baseChangeSub B S hS W q g univW)).1⟩
        ⟨W, (IsNthOrderThickening.isThickening B S hS univW.firstOrder).1⟩ c
        (ObjectProperty.homMk (universalThickeningBaseChangeProjection B S hS W q g)) hc =
      conormalMap B S hS
        ⟨baseChangeSub B S hS W q g,
          (IsNthOrderThickening.isThickening B S hS
            (isFirstOrderThickening_baseChangeSub B S hS W q g univW)).1⟩
        ⟨W, (IsNthOrderThickening.isThickening B S hS univW.firstOrder).1⟩
        (baseChangeThickeningSnd B S hS q g)
        (ObjectProperty.homMk (universalThickeningBaseChangeProjection B S hS W q g)) hc' := by
    rintro c hc rfl
    exact ⟨hc, rfl⟩
  exact key _ _ (universalThickeningMap_baseChange B S hS W q g univW)

/-- **Stacks 060B, the third assertion.**  The canonical map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of
conormal modules of Stacks 060A, attached to the cartesian square of the source, is surjective.

By `AlgebraicGeometry.Space.universalThickeningMap_baseChange` the morphism of ambient spaces of
that map is the projection `r : X ×_Y W' ⟶ W'`, and the closed subspace upstairs is the inverse
image `r⁻¹(W)`, so the map is the one of the fibre product square of
`AlgebraicGeometry.Space.epi_conormalMap`, the surjectivity clause of Stacks 04CQ. -/
@[stacks 060B "the third assertion: surjectivity of the induced map of conormal modules"]
theorem epi_universalThickeningConormalMap_baseChange
    (univW : IsUniversalFirstOrderThickening B S hS W q) :
    Epi (universalThickeningConormalMap B S hS g
      (universalThickeningBaseChangeProjection B S hS W q g)
      (isUniversalFirstOrderThickening_baseChange B S hS W q g univW) univW
      (baseChangeThickening_square B S hS W q g)) := by
  obtain ⟨_, h⟩ := universalThickeningConormalMap_baseChange_eq B S hS W q g univW
  rw [h]
  exact epi_conormalMap B S hS (baseChangeThickeningSnd B S hS q g)
    ⟨W, (IsNthOrderThickening.isThickening B S hS univW.firstOrder).1⟩

/-! ### Stacks 060C -/

/-- **Stacks 060C, the first assertion.**  In the cartesian square of Stacks 060B, if `g` is flat
then so is the induced morphism `r : X ×_Y W' ⟶ W'` of universal first-order thickenings.

The projection `r` is the base change of `g` along `q : W' ⟶ Y`, and flatness of morphisms of
algebraic spaces is stable under base change by Stacks 03MO.  That `r` is the induced morphism
of universal first-order thickenings — the canonical morphism of Stacks 060A for this square —
is `AlgebraicGeometry.Space.universalThickeningMap_baseChange`.

Flatness is `AlgebraicGeometry.Space.IsFlat`, the chartwise flatness of Stacks 03ML part (1),
which is the notion the source assumes of `g`. -/
@[stacks 060C "the first assertion: the induced morphism of universal first-order thickenings \
is flat"]
theorem isFlat_baseChangeThickeningSnd (g_flat : IsFlat B S hS g.hom) :
    IsFlat B S hS (baseChangeThickeningSnd B S hS q g).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g q) g_flat

/-- The canonical map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of conormal modules of Stacks 060A, attached to the
cartesian square of Stacks 060B, is an isomorphism when the morphism of small étale ringed topoi
induced by the projection `r : X ×_Y W' ⟶ W'` is flat in the sense of Stacks 04JB.

The argument is that of `AlgebraicGeometry.Space.epi_universalThickeningConormalMap_baseChange`
with the surjectivity clause of Stacks 04CQ replaced by its flat clause,
`AlgebraicGeometry.Space.isIso_conormalMap_of_isFlat`: by
`AlgebraicGeometry.Space.universalThickeningMap_baseChange` the morphism of ambient spaces is the
projection `r` and the closed subspace upstairs is the inverse image `r⁻¹(W)`, so the map is the
one at the fibre product square of `r`.

This is the form in which the flat clause of Stacks 04CQ states its hypothesis, and it is kept
for consumers that have flatness in that form; the assertion of the source is
`AlgebraicGeometry.Space.isIso_universalThickeningConormalMap_baseChange`, which takes the
chartwise flatness of `g` instead and carries the attribute. -/
theorem isIso_universalThickeningConormalMap_baseChange_of_isFlatRingedTopos
    (univW : IsUniversalFirstOrderThickening B S hS W q)
    (hflat : (smallEtaleRingedToposHom B S hS
      (baseChangeThickeningSnd B S hS q g)).IsFlat) :
    IsIso (universalThickeningConormalMap B S hS g
      (universalThickeningBaseChangeProjection B S hS W q g)
      (isUniversalFirstOrderThickening_baseChange B S hS W q g univW) univW
      (baseChangeThickening_square B S hS W q g)) := by
  obtain ⟨_, h⟩ := universalThickeningConormalMap_baseChange_eq B S hS W q g univW
  rw [h]
  exact isIso_conormalMap_of_isFlat B S hS (baseChangeThickeningSnd B S hS q g)
    ⟨W, (IsNthOrderThickening.isThickening B S hS univW.firstOrder).1⟩ hflat

/-- **Stacks 060C, the second assertion.**  In the cartesian square of Stacks 060B, if `g` is
flat then the canonical map `f^*𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of conormal modules of Stacks 060A is an
isomorphism.

Flatness of `g` is `AlgebraicGeometry.Space.IsFlat`, the chartwise flatness of Stacks 03ML
part (1), which is the notion the source assumes.  It passes to the projection
`r : X ×_Y W' ⟶ W'` by `AlgebraicGeometry.Space.isFlat_baseChangeThickeningSnd`, and from there
to flatness of the induced morphism of small étale ringed topoi by Stacks 073C,
`AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat`, which is the hypothesis the
flat clause of Stacks 04CQ consumes; the conclusion is then
`AlgebraicGeometry.Space.isIso_universalThickeningConormalMap_baseChange_of_isFlatRingedTopos`.

Together with `AlgebraicGeometry.Space.isFlat_baseChangeThickeningSnd` this is Stacks 060C as the
source states it: no hypothesis beyond the configuration of Stacks 060B and flatness of `g`. -/
@[stacks 060C "the second assertion: the induced map of conormal modules is an isomorphism"]
theorem isIso_universalThickeningConormalMap_baseChange
    (univW : IsUniversalFirstOrderThickening B S hS W q) (g_flat : IsFlat B S hS g.hom) :
    IsIso (universalThickeningConormalMap B S hS g
      (universalThickeningBaseChangeProjection B S hS W q g)
      (isUniversalFirstOrderThickening_baseChange B S hS W q g univW) univW
      (baseChangeThickening_square B S hS W q g)) :=
  isIso_universalThickeningConormalMap_baseChange_of_isFlatRingedTopos B S hS W q g univW
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS
      (baseChangeThickeningSnd B S hS q g)).mp
        (isFlat_baseChangeThickeningSnd B S hS q g g_flat))

end AlgebraicGeometry.Space

end
