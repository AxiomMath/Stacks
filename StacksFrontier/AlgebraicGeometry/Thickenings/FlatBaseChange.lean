module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareEpi
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal first-order thickenings under a flat base change

Let
```
Z --h--→ X
|        |
f        g
↓        ↓
W --h'-→ Y
```
be a cartesian square of schemes and let `W ⊂ W'` be a universal first-order thickening of `h'`
over `Y`. The fibre product `X ×_Y W'` is then a universal first-order thickening of `h` over
`X`: it is a first-order thickening of `Z = X ×_Y W` because `Z ⟶ X ×_Y W'` is the base change
of `W ⟶ W'`, and its universal property follows from that of `W'` together with the mapping
property of the fibre product. That, together with stability of formal unramifiedness under base
change and surjectivity of the resulting map of conormal sheaves, is
[Stacks Project, Tag 04F8].

When in addition `g` is flat, [Stacks Project, Tag 04F9] draws two conclusions, and both are
read off that description: the canonical morphism `Z' ⟶ W'` of [Stacks Project, Tag 04F7] is the
second projection `X ×_Y W' ⟶ W'`, which is a base change of `g` and hence flat; and the square
of inclusions `(Z ⊂ Z') ⟶ (W ⊂ W')` is cartesian with flat ambient map, so the canonical map of
conormal sheaves `f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` is an isomorphism by [Stacks Project, Tag 0473].

## Main definitions

* `Stacks.Thickenings.baseChangeAmbient`, `Stacks.Thickenings.baseChangeInclusion` and
  `Stacks.Thickenings.baseChangeToBase` are the fibre product `X ×_Y W'`, the inclusion of `Z`
  into it, and its structure morphism to `X`.
* `Stacks.Thickenings.baseChangeThickening` packages them as a
  `Stacks.Thickenings.UniversalFirstOrderThickening` of `h`.

## Main results

* `Stacks.Thickenings.formallyUnramified_of_isPullback` is part (1) of
  [Stacks Project, Tag 04F8].
* `Stacks.Thickenings.isUniversal_baseChange` is part (2) of [Stacks Project, Tag 04F8]:
  `X ×_Y W'` is a universal first-order thickening of `Z` over `X`.
* `Stacks.Thickenings.isPullback_inclusion_universalFirstOrderThickeningMap`: for *any* universal
  first-order thickening `Z ⊂ Z'` of `h`, the square of inclusions over the canonical morphism
  `Z' ⟶ W'` is cartesian.
* `Stacks.Thickenings.epi_immersionConormalSheafMap_of_isPullback` and
  `Stacks.Thickenings.epi_universalConormalSheafMap_of_isPullback` are part (3) of
  [Stacks Project, Tag 04F8]: the canonical map `f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` is surjective, with no
  flatness hypothesis.
* `Stacks.Thickenings.flat_universalFirstOrderThickeningMap` is the flatness conclusion of
  [Stacks Project, Tag 04F9].
* `Stacks.Thickenings.isIso_immersionConormalSheafMap_of_isPullback_of_flat` and
  `Stacks.Thickenings.isIso_universalConormalSheafMap_of_isPullback_of_flat` are the
  conormal-sheaf conclusion of [Stacks Project, Tag 04F9], for the map of
  [Stacks Project, Tag 01R4] and for the map of [Stacks Project, Tag 04F7] respectively.

## Implementation notes

Everything is stated for *given* universal first-order thickenings rather than for the chosen
ones of [Stacks Project, Tag 04F3]. The source assumes `h'` formally unramified, which is what
makes `W'` exist and, by stability of formal unramifiedness under base change, makes `Z'` exist
too; once the thickenings are given no such hypothesis is used, so the statements here generalize
the source and specialize to it at `Stacks.Thickenings.universalFirstOrderThickening`.

Both conclusions are first established at the particular thickening `X ×_Y W'` and then
transported to an arbitrary `Z ⊂ Z'` along
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalMap`, which is an isomorphism over
`X` by `Stacks.Thickenings.UniversalFirstOrderThickening.isIso_of_inclusion_of_toBase`. The
transport of the *cartesian square* is itself a pasting: an isomorphism on one corner of a
square is a cartesian square with identity bottom edge, so
`CategoryTheory.IsPullback.of_right` applies.

The conormal-sheaf conclusion is stated twice because the library carries two spellings of the
canonical map. `Stacks.Immersion.immersionConormalSheafMap` is the map of
[Stacks Project, Tag 01R4] between the conormal sheaves of *immersions*, which is the spelling
that [Stacks Project, Tag 0473] is proved at and the spelling in which
`Stacks.Thickenings.universalConormalSheaf` — the conormal sheaf `𝒞_{Z/X}` of
[Stacks Project, Tag 04F4] — is defined. `Stacks.Thickenings.universalConormalSheafMap` is the
map of [Stacks Project, Tag 04F7], built on the ringed-space conormal sheaf of the inclusion
itself rather than of its coborder factorization. The two differ exactly by conjugation with the
isomorphisms `Stacks.Immersion.conormalSheafSelfIso`, by definition of
`Stacks.Immersion.immersionConormalSheafMap`, so each is invertible if and only if the other is.

## References

* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7)
* [Stacks Project, Tag 04F8](https://stacks.math.columbia.edu/tag/04F8)
* [Stacks Project, Tag 04F9](https://stacks.math.columbia.edu/tag/04F9)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

variable {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {f : Z ⟶ W} {g : X ⟶ Y} {h' : W ⟶ Y}

/-! ### Formal unramifiedness of the base change -/

/-- In a cartesian square of schemes, the base change of a formally unramified morphism is
formally unramified. -/
@[stacks 04F8 "part (1): the base change of a formally unramified morphism"]
theorem formallyUnramified_of_isPullback (sq : IsPullback h f g h')
    [FormallyUnramified h'] : FormallyUnramified h :=
  MorphismProperty.of_isPullback (P := @FormallyUnramified) sq.flip inferInstance

/-! ### The base-changed thickening `X ×_Y W'` -/

/-- The fibre product `X ×_Y W'` of the base `X` with the ambient scheme of a universal
first-order thickening of `h' : W ⟶ Y`. -/
noncomputable abbrev baseChangeAmbient (g : X ⟶ Y) (t : UniversalFirstOrderThickening h') :
    Scheme.{u} :=
  pullback g t.toBase

/-- The structure morphism `X ×_Y W' ⟶ X`, the first projection. -/
noncomputable abbrev baseChangeToBase (g : X ⟶ Y) (t : UniversalFirstOrderThickening h') :
    baseChangeAmbient g t ⟶ X :=
  pullback.fst g t.toBase

/-- The two composites `Z ⟶ Y`, through `X` and through `W ⊂ W'`, agree. -/
theorem baseChange_lift_comm (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    h ≫ g = (f ≫ t.inclusion) ≫ t.toBase := by
  rw [Category.assoc, t.isUniversal.inclusion_toBase, sq.w]

/-- The inclusion of `Z = X ×_Y W` into `X ×_Y W'`, induced by `h : Z ⟶ X` and by `f : Z ⟶ W`
followed by the inclusion of `W` into `W'`. -/
noncomputable def baseChangeInclusion (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') : Z ⟶ baseChangeAmbient g t :=
  pullback.lift h (f ≫ t.inclusion) (baseChange_lift_comm sq t)

/-- The inclusion of `Z` into `X ×_Y W'` followed by the structure morphism is `h`. -/
@[simp]
theorem baseChangeInclusion_comp_fst (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    baseChangeInclusion sq t ≫ baseChangeToBase g t = h :=
  pullback.lift_fst _ _ _

/-- The inclusion of `Z` into `X ×_Y W'` followed by the projection to `W'` is `f` followed by
the inclusion of `W` into `W'`. -/
@[simp]
theorem baseChangeInclusion_comp_snd (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    baseChangeInclusion sq t ≫ pullback.snd g t.toBase = f ≫ t.inclusion :=
  pullback.lift_snd _ _ _

/-- **`Z ⟶ X ×_Y W'` is the base change of `W ⟶ W'`.** The square with horizontal maps
`Z ⟶ X ×_Y W'` and `W ⟶ W'` and vertical maps `f` and the second projection is cartesian. -/
theorem isPullback_baseChangeInclusion (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    IsPullback (baseChangeInclusion sq t) f (pullback.snd g t.toBase) t.inclusion := by
  refine IsPullback.of_right (h₁₂ := baseChangeToBase g t) ?_
    (baseChangeInclusion_comp_snd sq t) (IsPullback.of_hasPullback g t.toBase)
  rwa [baseChangeInclusion_comp_fst sq t, t.isUniversal.inclusion_toBase]

/-- `Z ⟶ X ×_Y W'` is a first-order thickening, being a base change of the first-order
thickening `W ⟶ W'`. -/
theorem isFirstOrderThickening_baseChangeInclusion (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    IsFirstOrderThickening (baseChangeInclusion sq t) :=
  isFirstOrderThickening_of_isPullback (isPullback_baseChangeInclusion sq t)
    t.isUniversal.isFirstOrderThickening

/-- **The fibre product `X ×_Y W'` is a universal first-order thickening of `Z = X ×_Y W` over
`X`.** -/
@[stacks 04F8 "part (2): X ×_Y W' is the universal first-order thickening of Z over X"]
theorem isUniversal_baseChange (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    IsUniversalFirstOrderThickening h (baseChangeInclusion sq t) (baseChangeToBase g t) := by
  refine ⟨isFirstOrderThickening_baseChangeInclusion sq t,
    baseChangeInclusion_comp_fst sq t, ?_⟩
  intro T T' jT hjT aT bT hcomm
  obtain ⟨c, ⟨hc₁, hc₂⟩, hcu⟩ :=
    t.isUniversal.existsUnique_lift jT hjT (aT ≫ f) (bT ≫ g)
      (by rw [← Category.assoc, hcomm, Category.assoc, sq.w, Category.assoc])
  refine ⟨pullback.lift bT c hc₂.symm, ⟨?_, pullback.lift_fst _ _ _⟩, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.assoc,
        baseChangeInclusion_comp_fst sq t, hcomm]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc,
        baseChangeInclusion_comp_snd sq t, hc₁, Category.assoc]
  · intro a'' ⟨ha''₁, ha''₂⟩
    refine pullback.hom_ext (by rwa [pullback.lift_fst]) ?_
    rw [pullback.lift_snd]
    refine hcu _ ⟨?_, ?_⟩
    · rw [← Category.assoc, ha''₁, Category.assoc, baseChangeInclusion_comp_snd sq t,
        Category.assoc]
    · rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha''₂]

/-- The universal first-order thickening `X ×_Y W'` of `Z` over `X`, packaged as a
`Stacks.Thickenings.UniversalFirstOrderThickening`. -/
noncomputable abbrev baseChangeThickening (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') : UniversalFirstOrderThickening h :=
  { ambient := baseChangeAmbient g t
    inclusion := baseChangeInclusion sq t
    toBase := baseChangeToBase g t
    isUniversal := isUniversal_baseChange sq t }

/-- The inclusion of the packaged thickening `X ×_Y W'` is
`Stacks.Thickenings.baseChangeInclusion`. -/
@[simp]
theorem baseChangeThickening_inclusion (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    (baseChangeThickening sq t).inclusion = baseChangeInclusion sq t :=
  rfl

/-- The structure morphism of the packaged thickening `X ×_Y W'` is the first projection. -/
@[simp]
theorem baseChangeThickening_toBase (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    (baseChangeThickening sq t).toBase = baseChangeToBase g t :=
  rfl

/-! ### The canonical morphism of thickenings of a base change -/

/-- **At the thickening `X ×_Y W'`, the canonical morphism of [Stacks Project, Tag 04F7] is the
second projection.** -/
theorem universalFirstOrderThickeningMap_baseChangeThickening (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    universalFirstOrderThickeningMap (baseChangeThickening sq t) t f g sq.w =
      pullback.snd g t.toBase :=
  (universalFirstOrderThickeningMap_unique (baseChangeThickening sq t) t f g sq.w
    (pullback.snd g t.toBase) (baseChangeInclusion_comp_snd sq t)
    pullback.condition.symm).symm

variable (tZ : UniversalFirstOrderThickening h)

/-- The canonical morphism `Z' ⟶ X ×_Y W'` comparing an arbitrary universal first-order
thickening of `h` with the fibre product is an isomorphism. -/
theorem isIso_canonicalMap_baseChangeThickening (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    IsIso (UniversalFirstOrderThickening.canonicalMap tZ (baseChangeThickening sq t)) :=
  UniversalFirstOrderThickening.isIso_of_inclusion_of_toBase _ _ _
    (UniversalFirstOrderThickening.canonicalMap_inclusion _ _)
    (UniversalFirstOrderThickening.canonicalMap_toBase _ _)

/-- **The canonical morphism `Z' ⟶ W'` factors through the fibre product.** It is the canonical
comparison `Z' ⟶ X ×_Y W'` followed by the second projection. -/
theorem canonicalMap_comp_snd (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    UniversalFirstOrderThickening.canonicalMap tZ (baseChangeThickening sq t) ≫
        pullback.snd g t.toBase =
      universalFirstOrderThickeningMap tZ t f g sq.w := by
  refine universalFirstOrderThickeningMap_unique tZ t f g sq.w _ ?_ ?_
  · rw [← Category.assoc, UniversalFirstOrderThickening.canonicalMap_inclusion,
      baseChangeThickening_inclusion, baseChangeInclusion_comp_snd sq t]
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      UniversalFirstOrderThickening.canonicalMap_toBase tZ (baseChangeThickening sq t)]

/-! ### The flatness conclusion of Tag 04F9 -/

/-- Let
```
Z --h--→ X
|        |
f        g
↓        ↓
W --h'-→ Y
```
be a cartesian square of schemes with `g` flat, let `Z ⊂ Z'` be a universal first-order
thickening of `h` over `X` and `W ⊂ W'` one of `h'` over `Y`. Then the canonical morphism
`Z' ⟶ W'` of [Stacks Project, Tag 04F7] is flat. -/
@[stacks 04F9 "the morphism Z' ⟶ W' of universal first-order thickenings is flat"]
theorem flat_universalFirstOrderThickeningMap (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') [Flat g] :
    Flat (universalFirstOrderThickeningMap tZ t f g sq.w) := by
  have hiso := isIso_canonicalMap_baseChangeThickening tZ sq t
  rw [← canonicalMap_comp_snd tZ sq t]
  infer_instance

/-! ### The conormal-sheaf conclusion of Tag 04F9 -/

/-- **The square of inclusions of the thickenings is cartesian.** For a cartesian square as in
[Stacks Project, Tag 04F9] and any universal first-order thickening `Z ⊂ Z'` of `h`, the square
with horizontal maps the two inclusions and vertical maps `f` and the canonical morphism
`Z' ⟶ W'` is cartesian. -/
theorem isPullback_inclusion_universalFirstOrderThickeningMap (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    IsPullback tZ.inclusion f (universalFirstOrderThickeningMap tZ t f g sq.w) t.inclusion := by
  have hiso := isIso_canonicalMap_baseChangeThickening tZ sq t
  refine IsPullback.of_right
    (h₁₂ := UniversalFirstOrderThickening.canonicalMap tZ (baseChangeThickening sq t))
    (h₂₂ := 𝟙 t.ambient) ?_
    (universalFirstOrderThickeningMap_inclusion tZ t f g sq.w)
    (IsPullback.of_horiz_isIso (CommSq.mk (by rw [Category.comp_id, canonicalMap_comp_snd])))
  rw [UniversalFirstOrderThickening.canonicalMap_inclusion, Category.comp_id,
    baseChangeThickening_inclusion]
  exact isPullback_baseChangeInclusion sq t

/-- For a cartesian square of schemes, with no flatness hypothesis on `g`, the canonical map of
conormal sheaves `f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 01R4] between the inclusions of
universal first-order thickenings is surjective. -/
@[stacks 04F8 "part (3): the canonical map f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X} is surjective",
  ega "IV 17.13.1" "more general"]
theorem epi_immersionConormalSheafMap_of_isPullback (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    Epi (Stacks.Immersion.immersionConormalSheafMap tZ.inclusion t.inclusion f
      (universalFirstOrderThickeningMap tZ t f g sq.w)
      (Stacks.Immersion.toShHom_square
        (universalFirstOrderThickeningMap_inclusion tZ t f g sq.w))) :=
  Stacks.Immersion.epi_immersionConormalSheafMap tZ.inclusion t.inclusion f _
    (isPullback_inclusion_universalFirstOrderThickeningMap tZ sq t)

/-- For a cartesian square of schemes, the morphism of conormal sheaves
`Stacks.Thickenings.universalConormalSheafMap` of [Stacks Project, Tag 04F7], induced by the
canonical morphism of universal first-order thickenings, is surjective. -/
@[stacks 04F8 "part (3): the canonical map of conormal sheaves of Tag 04F7 is surjective"]
theorem epi_universalConormalSheafMap_of_isPullback (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') :
    Epi (universalConormalSheafMap tZ t f g sq.w) := by
  have hcomp : Epi
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map
          (Stacks.Immersion.conormalSheafSelfIso t.inclusion).inv ≫
        universalConormalSheafMap tZ t f g sq.w ≫
          (Stacks.Immersion.conormalSheafSelfIso tZ.inclusion).hom) :=
    epi_immersionConormalSheafMap_of_isPullback tZ sq t
  rwa [epi_comp_iff_of_epi, epi_comp_iff_of_isIso] at hcomp

/-- For a cartesian square of schemes with `g` flat, the canonical map of conormal sheaves
`f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X}` of [Stacks Project, Tag 01R4] between the inclusions of the two
universal first-order thickenings is an isomorphism. -/
@[stacks 04F9 "the induced map f^* 𝒞_{W/Y} ⟶ 𝒞_{Z/X} of conormal sheaves is an isomorphism"]
theorem isIso_immersionConormalSheafMap_of_isPullback_of_flat (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') [Flat g] :
    IsIso (Stacks.Immersion.immersionConormalSheafMap tZ.inclusion t.inclusion f
      (universalFirstOrderThickeningMap tZ t f g sq.w)
      (Stacks.Immersion.toShHom_square
        (universalFirstOrderThickeningMap_inclusion tZ t f g sq.w))) := by
  have := flat_universalFirstOrderThickeningMap tZ sq t
  exact Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat tZ.inclusion t.inclusion f _
    (isPullback_inclusion_universalFirstOrderThickeningMap tZ sq t)

/-- For a cartesian square of schemes with `g` flat, the morphism of conormal sheaves
`Stacks.Thickenings.universalConormalSheafMap` of [Stacks Project, Tag 04F7], induced by the
canonical morphism of universal first-order thickenings, is an isomorphism. -/
@[stacks 04F9 "the induced map of conormal sheaves of Tag 04F7 is an isomorphism"]
theorem isIso_universalConormalSheafMap_of_isPullback_of_flat (sq : IsPullback h f g h')
    (t : UniversalFirstOrderThickening h') [Flat g] :
    IsIso (universalConormalSheafMap tZ t f g sq.w) := by
  have hcomp : IsIso
      ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map
          (Stacks.Immersion.conormalSheafSelfIso t.inclusion).inv ≫
        universalConormalSheafMap tZ t f g sq.w ≫
          (Stacks.Immersion.conormalSheafSelfIso tZ.inclusion).hom) :=
    isIso_immersionConormalSheafMap_of_isPullback_of_flat tZ sq t
  rwa [isIso_comp_left_iff, isIso_comp_right_iff] at hcomp

end Stacks.Thickenings

end
