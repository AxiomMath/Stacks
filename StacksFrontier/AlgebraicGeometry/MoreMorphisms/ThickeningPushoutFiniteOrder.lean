module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningRestrict
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFirstOrder
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT

/-!
# Pushouts along a finite-order thickening and an affine morphism

Let `i : X ⟶ X'` be a finite-order thickening of schemes and `f : X ⟶ Y` an affine morphism.
Then the pushout `Y' = Y ⨿_X X'` exists in the category of schemes, `Y ⟶ Y'` is again a
thickening, the pushout square is simultaneously cartesian, and the structure sheaf of `Y'` is
the fibre product `𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}`.  These are the four assertions of
[Stacks Project, Tag 07RT] for a thickening of finite order.

## Main results

* `Stacks.Pushout.exists_isPushout_isPullback_isThickening_of_isFiniteOrderThickening`
  constructs a scheme carrying the square and proves it cocartesian, cartesian, and a
  thickening of `Y` all at once.
* `Stacks.Pushout.hasPushout_of_isFiniteOrderThickening_of_isAffineHom` is the first assertion:
  the pushout exists.
* `Stacks.Pushout.pushout_inr_isThickening_of_isFiniteOrderThickening` is the second: the map
  from `Y` into the pushout is a thickening.
* `Stacks.Pushout.isPullback_pushout_of_isFiniteOrderThickening_of_isAffineHom` is the third:
  the pushout square is cartesian, that is, `X = Y ×_{Y'} X'`.
* `Stacks.Pushout.pushout_structureSheaf_isPullback_of_isFiniteOrderThickening` is the fourth:
  over every open of the pushout the ring of sections is the fibre product of the rings of
  sections on `Y` and on `X'` over the one on `X`.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal` and
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT` prove all four assertions
for an arbitrary thickening, granted a universally quantified hypothesis `H` asserting
[Stacks Project, Tag 06AD] — *a thickening of an affine scheme is affine*.  That hypothesis
enters at exactly one point, through
`Stacks.Pushout.isAffineOpen_opensCongr_preimage_of_isThickening`, and only for thickenings of
the form `i ∣_ V'`.  For a thickening of finite order it is therefore discharged outright:
`Stacks.Thickenings.IsFiniteOrderThickening.morphismRestrict` keeps the order under
restriction, and `Stacks.Thickenings.isAffine_of_isFiniteOrderThickening` is the finite-order
case of Tag 06AD, proved through Serre's criterion.  Everything downstream of the chart
condition — the gluing of the apex, cartesianness, the thickening, the structure sheaf — is
already hypothesis-free in those two files and is reused here unchanged.

The general case is `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional`,
which discharges `H` for an arbitrary thickening from
`Stacks.Thickenings.forall_isAffine_of_isThickening`.  This file remains of interest because it
reaches the four assertions for a thickening of finite order without that route to Tag 06AD,
which passes through the affineness of the target of a finite surjective morphism.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {X X' Y : Scheme.{u}}

/-! ### Discharging the affineness hypothesis -/

/-- **The open of the ambient scheme matching the preimage of an affine open is affine**, for a
finite-order thickening.  The open `hi.isThickening.opensCongr (f ⁻¹ᵁ V)` of `X'` is a
finite-order thickening of `f ⁻¹ᵁ V`, which is affine because `f` is an affine morphism; so the
finite-order case of [Stacks Project, Tag 06AD] applies.

This discharges the hypothesis `H` of
`Stacks.Pushout.isAffineOpen_opensCongr_preimage_of_isThickening`, which is the only place the
global statement of [Stacks Project, Tag 07RT] uses Tag 06AD. -/
theorem isAffineOpen_opensCongr_preimage_of_isFiniteOrderThickening {i : X ⟶ X'}
    (hi : IsFiniteOrderThickening i) (f : X ⟶ Y) [IsAffineHom f] {V : Y.Opens}
    (hV : IsAffineOpen V) : IsAffineOpen (hi.isThickening.opensCongr (f ⁻¹ᵁ V)) := by
  have : IsAffine (i ⁻¹ᵁ hi.isThickening.opensCongr (f ⁻¹ᵁ V)).toScheme := by
    rw [hi.isThickening.preimage_opensCongr]
    exact hV.preimage f
  exact isAffine_of_isFiniteOrderThickening (hi.morphismRestrict _)

/-- **Every point of a pushout along a finite-order thickening lies in an open with affine
preimages.**  The map from `Y` is surjective on points by
`Stacks.Pushout.surjective_of_isPushout_base_of_isThickening`; around a preimage of the given
point take an affine open `V` of `Y`, pair it with the open of `X'` matching `f ⁻¹ᵁ V`, which is
affine by `Stacks.Pushout.isAffineOpen_opensCongr_preimage_of_isFiniteOrderThickening`, and span
the two by an open of the apex.

This is the chart condition that every remaining step of [Stacks Project, Tag 07RT] takes as its
input. -/
theorem exists_opens_isAffineOpen_preimage_of_isFiniteOrderThickening {i : X ⟶ X'}
    (hi : IsFiniteOrderThickening i) (f : X ⟶ Y) [IsAffineHom f]
    {P : LocallyRingedSpace.{u}} {a : Scheme.forgetToLocallyRingedSpace.obj X' ⟶ P}
    {b : Scheme.forgetToLocallyRingedSpace.obj Y ⟶ P}
    (hbase : IsPushout (Scheme.forgetToLocallyRingedSpace.map i).base
      (Scheme.forgetToLocallyRingedSpace.map f).base a.base b.base)
    (p : P) :
    ∃ W : Opens P, p ∈ W ∧ IsAffineOpen ((Opens.map a.base).obj W) ∧
      IsAffineOpen ((Opens.map b.base).obj W) := by
  have := hi.1
  obtain ⟨y, hy⟩ : ∃ y : Y, b.base y = p :=
    surjective_of_isPushout_base_of_isThickening hi.isThickening f hbase p
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  obtain ⟨W, hWset, hWa, hWb⟩ := exists_opens_preimage_eq_of_isPushout_base' i f hbase
    i.isClosedEmbedding.injective (hi.isThickening.opensCongr (f ⁻¹ᵁ V)) V
    (hi.isThickening.preimage_opensCongr _)
  refine ⟨W, ?_, hWa ▸ isAffineOpen_opensCongr_preimage_of_isFiniteOrderThickening hi f hV,
    hWb ▸ hV⟩
  change (p : P) ∈ (W : Set P)
  rw [hWset]
  exact Or.inr ⟨y, hyV, hy⟩

/-! ### The four assertions of Tag 07RT for a finite-order thickening -/

/-- **The pushout of a finite-order thickening and an affine morphism, with its cocartesian
square one layer down.**  The apex is the pushout of locally ringed spaces, which is a scheme
because its points have affine charts; the chart condition is retained because it is the input
of the three remaining assertions of [Stacks Project, Tag 07RT]. -/
theorem exists_isPushout_forgetToLocallyRingedSpace_of_isFiniteOrderThickening (i : X ⟶ X')
    (f : X ⟶ Y) (hi : IsFiniteOrderThickening i) [IsAffineHom f] :
    ∃ (Q : Scheme.{u}) (A : X' ⟶ Q) (B : Y ⟶ Q),
      IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)
        (Scheme.forgetToLocallyRingedSpace.map A)
        (Scheme.forgetToLocallyRingedSpace.map B) ∧
      ∀ p : Q, ∃ W : Q.Opens, p ∈ W ∧ IsAffineOpen (A ⁻¹ᵁ W) ∧ IsAffineOpen (B ⁻¹ᵁ W) := by
  have := hi.1
  have hcol : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.left)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.right) :=
    IsPushout.of_isColimit_cocone (colimit.isColimit
      (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)))
  exact exists_scheme_isPushout_of_isPushout i f hcol
    (exists_opens_isAffineOpen_preimage_of_isFiniteOrderThickening hi f
      (isPushout_base_of_isPushout hcol))

/-- **Stacks Project, Tag 07RT for a finite-order thickening, on an explicitly constructed
apex.**  For a finite-order thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` there is
a scheme `Q` with maps `A : X' ⟶ Q` and `B : Y ⟶ Q` whose square is cocartesian, is
simultaneously cartesian, and has `B` a thickening. -/
@[stacks 07RT "the existence of the pushout, that Y ⊂ Y' is a thickening and that the square is \
cartesian; for a thickening of finite order"]
theorem exists_isPushout_isPullback_isThickening_of_isFiniteOrderThickening (i : X ⟶ X')
    (f : X ⟶ Y) (hi : IsFiniteOrderThickening i) [IsAffineHom f] :
    ∃ (Q : Scheme.{u}) (A : X' ⟶ Q) (B : Y ⟶ Q),
      IsPushout i f A B ∧ IsPullback i f A B ∧ IsThickening B := by
  have := hi.1
  obtain ⟨Q, A, B, hcol, hch⟩ :=
    exists_isPushout_forgetToLocallyRingedSpace_of_isFiniteOrderThickening i f hi
  exact ⟨Q, A, B, IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace hcol,
    isPullback_of_isPushout_forgetToLocallyRingedSpace i f A B hcol hch,
    isThickening_of_isPushout_forgetToLocallyRingedSpace hi.isThickening f hcol hch⟩

/-- **Stacks Project, Tag 07RT, first assertion, for a finite-order thickening.**  A finite-order
thickening and an affine morphism have a pushout in the category of schemes. -/
@[stacks 07RT "the existence of the pushout, for a thickening of finite order"]
theorem hasPushout_of_isFiniteOrderThickening_of_isAffineHom (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsFiniteOrderThickening i) [IsAffineHom f] : HasPushout i f := by
  obtain ⟨Q, A, B, hpo, -, -⟩ :=
    exists_isPushout_isPullback_isThickening_of_isFiniteOrderThickening i f hi
  exact hpo.hasPushout

/-- **Stacks Project, Tag 07RT, third assertion, for a finite-order thickening.**  The pushout
square of a finite-order thickening and an affine morphism is also cartesian, that is,
`X = Y ×_{Y'} X'`; stated for Mathlib's canonical pushout. -/
@[stacks 07RT "that the square is cartesian, X = Y ×_{Y'} X'; for a thickening of finite order"]
theorem isPullback_pushout_of_isFiniteOrderThickening_of_isAffineHom (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsFiniteOrderThickening i) [IsAffineHom f] [HasPushout i f] :
    IsPullback i f (pushout.inl i f) (pushout.inr i f) := by
  obtain ⟨Q, A, B, hpo, hpb, -⟩ :=
    exists_isPushout_isPullback_isThickening_of_isFiniteOrderThickening i f hi
  rw [← hpo.inl_isoPushout_hom, ← hpo.inr_isoPushout_hom]
  exact hpb.of_iso' (Iso.refl X) (Iso.refl X') (Iso.refl Y) hpo.isoPushout.symm (by simp)
    (by simp) (by simp) (by simp)

/-- **Stacks Project, Tag 07RT, second assertion, for a finite-order thickening.**  The map from
`Y` into the pushout of a finite-order thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y`
is again a thickening; stated for Mathlib's canonical pushout. -/
@[stacks 07RT "that Y ⊂ Y' is a thickening, for a thickening of finite order"]
theorem pushout_inr_isThickening_of_isFiniteOrderThickening (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsFiniteOrderThickening i) [IsAffineHom f] [HasPushout i f] :
    IsThickening (pushout.inr i f) := by
  obtain ⟨Q, A, B, hpo, -, hci, hsurj⟩ :=
    exists_isPushout_isPullback_isThickening_of_isFiniteOrderThickening i f hi
  have : Surjective B := ⟨hsurj⟩
  rw [← hpo.inr_isoPushout_hom]
  exact ⟨inferInstance, (B ≫ hpo.isoPushout.hom).surjective⟩

/-- **Stacks Project, Tag 07RT, fourth assertion, for a finite-order thickening.**  On every open
`U` of the pushout of a finite-order thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y`
the ring of sections is the fibre product of the rings of sections over the two preimages of `U`
in `Y` and `X'` above the ring of sections over their common preimage in `X`; this is
`𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}`. -/
@[stacks 07RT "the description of 𝒪_{Y'} as 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}; for a thickening of \
finite order"]
theorem pushout_structureSheaf_isPullback_of_isFiniteOrderThickening (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsFiniteOrderThickening i) [IsAffineHom f] [HasPushout i f] (U : (pushout i f).Opens) :
    IsPullback ((pushout.inr i f).app U) ((pushout.inl i f).app U)
      (f.app (pushout.inr i f ⁻¹ᵁ U))
      (i.app (pushout.inl i f ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V : X.Opens ↦ Γ(X, V))
        (congrArg (fun g : X ⟶ pushout i f ↦ g ⁻¹ᵁ U)
          (pushout.condition (f := i) (g := f))))) := by
  obtain ⟨Q, A, B, hcol, -⟩ :=
    exists_isPushout_forgetToLocallyRingedSpace_of_isFiniteOrderThickening i f hi
  have hpo : IsPushout i f A B :=
    IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace hcol
  have hcol' : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f)
      (Scheme.forgetToLocallyRingedSpace.map (pushout.inl i f))
      (Scheme.forgetToLocallyRingedSpace.map (pushout.inr i f)) :=
    hcol.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (Scheme.forgetToLocallyRingedSpace.mapIso hpo.isoPushout).symm
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Scheme.forgetToLocallyRingedSpace.map_comp, hpo.inl_isoPushout_inv])
      (by rw [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.id_comp,
        ← Scheme.forgetToLocallyRingedSpace.map_comp, hpo.inr_isoPushout_inv])
  exact isPullback_app_of_isPushout_forgetToLocallyRingedSpace hcol' U
    (congrArg (fun g : X ⟶ pushout i f ↦ g ⁻¹ᵁ U) (pushout.condition (f := i) (g := f)))

end Stacks.Pushout

end
