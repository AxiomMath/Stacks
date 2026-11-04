module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport

/-!
# Fibres of a morphism over a base, and how they move under a change of base and of point

Let `c : X ⟶ Y` be a morphism of schemes over `S` and `t : T ⟶ S` a morphism, typically the
spectrum of a field. Write `X_t`, `Y_t` for the fibre products with `T` and `c_t : X_t ⟶ Y_t` for
the induced morphism (`AlgebraicGeometry.C1590Private.fibreHom`; at the closed point of a local
ring this is `AlgebraicGeometry.ContractionUniquenessComplete.specialMap`). This file records how
these fibres behave under a commutative square

```
  T' --t'--> S'
  |τ         |σ
  T  --t-->  S
```

together with a base change `X' ⟶ X`, `Y' ⟶ Y` of the data along `σ`:

* the induced maps of fibres form cartesian squares (`isPullback_fibreMap`,
  `isPullback_fibreHom`);
* the two conditions `𝒪_{Y_t} ≅ c_{t,*}𝒪_{X_t}` and `R¹c_{t,*}𝒪_{X_t} = 0` pass from `t` to `t'`
  when `τ` is flat, and back when `τ` is moreover surjective, provided the fibres of `c_t` have
  dimension at most one (`fibreConditions_of_isPullback`,
  `fibreConditions_of_isPullback_of_surjective`).

These are the bookkeeping steps of the proof of [Stacks, Tag 0E89]: the conditions of the tag on
the fibre at `s` are moved to the closed point of a completion, to a residue field presented in
another way, or along a field extension.

The higher direct image is `((Scheme.Modules.pushforward c).rightDerived 1).obj 𝒪`, the spelling
of `Stacks.Curves.StableModel.IsStableContraction` and of the complete case of the tag
(`AlgebraicGeometry.exists_iso_comp_eq_of_specialFibre_of_isAdicComplete_holds`); the base change
results of `StacksDraft.AlgebraicGeometry.TopDegreeBaseChange` are stated for the derived-category
indexing `Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf`, and the two
are compared by `Stacks.DerivedIndexing.rightDerivedIso` (`isZero_rightDerived_one_iff`).

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

open Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-! ### The two indexings of `R¹` -/

/-- `R¹c_*𝒪_X = 0` reads the same in the two indexings of the right derived functors. -/
theorem isZero_rightDerived_one_iff {X Y : Scheme.{u}} (c : X ⟶ Y) :
    IsZero (((Scheme.Modules.pushforward c).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) ↔
      IsZero (firstDirectImageStructureSheaf c) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard Y.Modules
  exact ⟨fun h => h.of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward c) 1).app _).symm,
    fun h => h.of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward c) 1).app _)⟩

/-! ### Fibres over a point and their maps -/

section Fibres

variable {S T : Scheme.{u}} (t : T ⟶ S) {X Y : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)

/-- The morphism `c_t : X_t ⟶ Y_t` of fibres over `t : T ⟶ S` induced by `c : X ⟶ Y` over `S`. -/
abbrev fibreHom (c : X ⟶ Y) (hc : c ≫ fY = fX) : pullback fX t ⟶ pullback fY t :=
  pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by simp [hc]) (by simp)

/-- The map `c_t` followed by the projection `Y_t ⟶ Y` equals the projection `X_t ⟶ X` followed
by `c`. -/
@[reassoc (attr := simp)]
theorem fibreHom_fst (c : X ⟶ Y) (hc : c ≫ fY = fX) :
    fibreHom t fX fY c hc ≫ pullback.fst fY t = pullback.fst fX t ≫ c :=
  pullback.lift_fst _ _ _

/-- The map `c_t` commutes with the projections of the fibres to `T`. -/
@[reassoc (attr := simp)]
theorem fibreHom_snd (c : X ⟶ Y) (hc : c ≫ fY = fX) :
    fibreHom t fX fY c hc ≫ pullback.snd fY t = pullback.snd fX t :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The fibre of `X` over `t` is the fibre product over `Y` of `X` and the fibre of `Y` over
`t`. -/
theorem isPullback_fibreHom_fst (c : X ⟶ Y) (hc : c ≫ fY = fX) :
    IsPullback (pullback.fst fX t) (fibreHom t fX fY c hc) c (pullback.fst fY t) := by
  refine IsPullback.of_bot ?_ (fibreHom_fst t fX fY c hc).symm (IsPullback.of_hasPullback fY t)
  rw [fibreHom_snd, hc]
  exact IsPullback.of_hasPullback fX t

/-- The map of fibres induced by a composite `c ≫ d` is the composite of the induced maps. -/
theorem fibreHom_comp {Z : Scheme.{u}} (fZ : Z ⟶ S) (c : X ⟶ Y) (hc : c ≫ fY = fX)
    (d : Y ⟶ Z) (hd : d ≫ fZ = fY) :
    fibreHom t fX fZ (c ≫ d) (by rw [Category.assoc, hd, hc]) =
      fibreHom t fX fY c hc ≫ fibreHom t fY fZ d hd := by
  apply pullback.hom_ext <;> simp

end Fibres

/-! ### Change of base and of point -/

section Change

variable {S S' T T' : Scheme.{u}} {σ : S' ⟶ S} {t : T ⟶ S} {t' : T' ⟶ S'} {τ : T' ⟶ T}
  (hst : t' ≫ σ = τ ≫ t)

include hst

/-- The map of fibres `Y'_{t'} ⟶ Y_t` induced by a morphism `p : Y' ⟶ Y` over `σ`. -/
abbrev fibreMap {Y Y' : Scheme.{u}} (fY : Y ⟶ S) (fY' : Y' ⟶ S') (p : Y' ⟶ Y)
    (hp : fY' ≫ σ = p ≫ fY) : pullback fY' t' ⟶ pullback fY t :=
  pullback.map fY' t' fY t p τ σ hp hst

/-- The map `Y'_{t'} ⟶ Y_t` followed by the projection to `Y` equals the projection to `Y'`
followed by `p`. -/
@[reassoc (attr := simp)]
theorem fibreMap_fst {Y Y' : Scheme.{u}} (fY : Y ⟶ S) (fY' : Y' ⟶ S') (p : Y' ⟶ Y)
    (hp : fY' ≫ σ = p ≫ fY) :
    fibreMap hst fY fY' p hp ≫ pullback.fst fY t = pullback.fst fY' t' ≫ p :=
  pullback.lift_fst _ _ _

/-- The map `Y'_{t'} ⟶ Y_t` followed by the projection to `T` equals the projection to `T'`
followed by `τ`. -/
@[reassoc (attr := simp)]
theorem fibreMap_snd {Y Y' : Scheme.{u}} (fY : Y ⟶ S) (fY' : Y' ⟶ S') (p : Y' ⟶ Y)
    (hp : fY' ≫ σ = p ≫ fY) :
    fibreMap hst fY fY' p hp ≫ pullback.snd fY t = pullback.snd fY' t' ≫ τ :=
  pullback.lift_snd _ _ _

/-- If `Y'` is the base change of `Y` along `σ`, the fibre of `Y'` over `t'` is the base change of
the fibre of `Y` over `t` along `τ`. -/
theorem isPullback_fibreMap {Y Y' : Scheme.{u}} (fY : Y ⟶ S) (fY' : Y' ⟶ S') (p : Y' ⟶ Y)
    (hp : fY' ≫ σ = p ≫ fY) (hY : IsPullback p fY' fY σ) :
    IsPullback (fibreMap hst fY fY' p hp) (pullback.snd fY' t') (pullback.snd fY t) τ := by
  refine IsPullback.of_right ?_ (fibreMap_snd hst fY fY' p hp) (IsPullback.of_hasPullback fY t)
  rw [fibreMap_fst, ← hst]
  exact (IsPullback.of_hasPullback fY' t').paste_horiz hY

/-- The maps of fibres induced by a base change of `c : X ⟶ Y` form a cartesian square. -/
theorem isPullback_fibreHom {X Y X' Y' : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    (fX' : X' ⟶ S') (fY' : Y' ⟶ S') (q : X' ⟶ X) (p : Y' ⟶ Y)
    (hq : fX' ≫ σ = q ≫ fX) (hp : fY' ≫ σ = p ≫ fY) (c : X ⟶ Y) (hc : c ≫ fY = fX)
    (c' : X' ⟶ Y') (hc' : c' ≫ fY' = fX') (hcc : c' ≫ p = q ≫ c)
    (hsq : IsPullback q c' c p) :
    IsPullback (fibreMap hst fX fX' q hq) (fibreHom t' fX' fY' c' hc') (fibreHom t fX fY c hc)
      (fibreMap hst fY fY' p hp) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_fibreHom_fst t fX fY c hc)
  · rw [fibreMap_fst, fibreMap_fst]
    exact (isPullback_fibreHom_fst t' fX' fY' c' hc').paste_horiz hsq
  · apply pullback.hom_ext <;> simp [hcc]

end Change

/-! ### Transport of the two fibre conditions -/

section Conditions

variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- **The two fibre conditions pass to a flat base change.** In a cartesian square with `g` flat
and `f` proper with fibres of dimension at most one, `𝒪 ≅ f_*𝒪` and `R¹f_*𝒪 = 0` pass from `f`
to `f'`. -/
theorem fibreConditions_of_isPullback (H : IsPullback g' f' f g) [Flat g] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    IsIso (Scheme.Modules.unitToPushforwardUnit f') ∧
      IsZero (((Scheme.Modules.pushforward f').rightDerived 1).obj
        (SheafOfModules.unit X'.ringCatSheaf)) := by
  obtain ⟨hR', h0'⟩ := isZero_and_isIso_of_isPullback H hdim
    ((isZero_rightDerived_one_iff f).1 hR) h0
  exact ⟨h0', (isZero_rightDerived_one_iff f').2 hR'⟩

/-- **The two fibre conditions descend along a faithfully flat base change.** -/
theorem fibreConditions_of_isPullback_of_surjective (H : IsPullback g' f' f g) [Flat g]
    [Surjective g] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit f'))
    (hR : IsZero (((Scheme.Modules.pushforward f').rightDerived 1).obj
      (SheafOfModules.unit X'.ringCatSheaf))) :
    IsIso (Scheme.Modules.unitToPushforwardUnit f) ∧
      IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  obtain ⟨hR', h0'⟩ := isZero_and_isIso_of_isPullback_of_surjective H hdim
    ((isZero_rightDerived_one_iff f').1 hR) h0
  exact ⟨h0', (isZero_rightDerived_one_iff f).2 hR'⟩

end Conditions

end AlgebraicGeometry.C1590Private

end
