module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreRefinement
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreWitness
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# The relative weak assassin under base change

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `g : Y' ⟶ Y` be
arbitrary and let `X' = X ×_Y Y'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`. For an
`𝒪_X`-module `F` write `F' = (g')^*F`. The fibre of `f'` over a field-valued point `q` of `Y'`
is the fibre of `f` over the image of `q` in `Y`, because the two cartesian squares paste, and
under that identification `F'` restricted to the one fibre is `F` restricted to the other.
Weak association is therefore carried from `WeakAss_{X'/Y'}(F')` to `WeakAss_{X/Y}(F)` by
`g'`, and a witness on the fibre over a representative of a prescribed point of `Y'` produces a
point of `WeakAss_{X'/Y'}(F')` above both that point and a given point of `WeakAss_{X/Y}(F)`.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeFibreIso`: the fibre of `f'` over a field-valued point of
  `Y'` is the fibre of `f` over its image in `Y`.
* `AlgebraicGeometry.Space.baseChangeFibreMap`: that identification as a morphism of algebraic
  spaces.

## Main results

* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_baseChange`: **Stacks 0CV2,
  part (1)**, the image of a point of `WeakAss_{X'/Y'}(F')` lies in `WeakAss_{X/Y}(F)`.
* `AlgebraicGeometry.Space.exists_isRelativeWeaklyAssociatedPoint_baseChange`: the same
  conclusion with the witness read at a prescribed field-valued representative of the point of
  `Y'`.
* `AlgebraicGeometry.Space.exists_isRelativeWeaklyAssociatedPoint_baseChange_of_pointsMap_eq`:
  **Stacks 0CV2, part (2)**, for a point of `WeakAss_{X/Y}(F)` and an arbitrary point of `Y'`
  with the same image in `Y`.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_baseChange_subset_range`:
  **Stacks 0CW2**, a containment of `WeakAss_{X/Y}(F)` in an image is preserved by base change.

## References

* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 05DC](https://stacks.math.columbia.edu/tag/05DC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_spaceBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_spaceBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_spaceBaseChange B S hS).has_limit _

variable
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-! ### The fibre of a base change -/


/-- In a cartesian square with vertical morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y'`, the fibre of
`f'` over a field-valued point `q` of `Y'` is a fibre product of `f` with the morphism
presented by the image of `q` in `Y`. -/
theorem isPullback_fibreAtFieldValuedPoint_baseChange
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (q : FieldValuedPoint B S hS Y'.1) :
    IsPullback (pullback.fst f'.hom (fieldMorphism B S hS Y'.1 q) ≫ g'.hom)
      (pullback.snd f'.hom (fieldMorphism B S hS Y'.1 q)) f.hom
      (fieldMorphism B S hS Y.1 (FieldValuedPoint.map B S hS Y'.1 g.hom q)) := by
  rw [fieldMorphism_map]
  exact (IsPullback.of_hasPullback f'.hom (fieldMorphism B S hS Y'.1 q)).paste_horiz sq

/-- The fibre of `f'` over a field-valued point `q` of `Y'` is isomorphic to the fibre of `f`
over the image of `q` in `Y`, compatibly with the projections to `X'` and `X`. -/
noncomputable def baseChangeFibreIso (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (q : FieldValuedPoint B S hS Y'.1) :
    (fibreAtFieldValuedPoint B S hS f' q).1 ≅
      (fibreAtFieldValuedPoint B S hS f (FieldValuedPoint.map B S hS Y'.1 g.hom q)).1 :=
  (isPullback_fibreAtFieldValuedPoint_baseChange B S hS sq q).isoIsPullback _ _
    (IsPullback.of_hasPullback f.hom
      (fieldMorphism B S hS Y.1 (FieldValuedPoint.map B S hS Y'.1 g.hom q)))

/-- The identification of the two fibres as a morphism of algebraic spaces. -/
noncomputable def baseChangeFibreMap (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (q : FieldValuedPoint B S hS Y'.1) :
    fibreAtFieldValuedPoint B S hS f' q ⟶
      fibreAtFieldValuedPoint B S hS f (FieldValuedPoint.map B S hS Y'.1 g.hom q) :=
  ObjectProperty.homMk (baseChangeFibreIso B S hS sq q).hom

/-- The identification of the two fibres is compatible with their projections, read on the
underlying presheaves. -/
theorem baseChangeFibreMap_hom_comp_projection (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (q : FieldValuedPoint B S hS Y'.1) :
    (baseChangeFibreMap B S hS sq q).hom ≫
        (fibreAtFieldValuedPointProjection B S hS f
          (FieldValuedPoint.map B S hS Y'.1 g.hom q)).hom =
      (fibreAtFieldValuedPointProjection B S hS f' q).hom ≫ g'.hom :=
  (isPullback_fibreAtFieldValuedPoint_baseChange B S hS sq q).isoIsPullback_hom_fst _ _ _

/-- The identification of the two fibres is compatible with their projections. -/
theorem baseChangeFibreMap_comp_projection (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (q : FieldValuedPoint B S hS Y'.1) :
    baseChangeFibreMap B S hS sq q ≫
        fibreAtFieldValuedPointProjection B S hS f
          (FieldValuedPoint.map B S hS Y'.1 g.hom q) =
      fibreAtFieldValuedPointProjection B S hS f' q ≫ g' :=
  (ObjectProperty.fullyFaithfulι _).map_injective
    (baseChangeFibreMap_hom_comp_projection B S hS sq q)

/-- The identification of the two fibres is étale, being an isomorphism. -/
theorem isEtale_baseChangeFibreMap (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (q : FieldValuedPoint B S hS Y'.1) :
    IsEtale B S hS (baseChangeFibreMap B S hS sq q).hom :=
  have : IsIso (baseChangeFibreMap B S hS sq q).hom :=
    inferInstanceAs (IsIso (baseChangeFibreIso B S hS sq q).hom)
  isEtale_of_isIso B S hS _

/-- The projection of the identified point of the fibre of `f` over the image of `q` is the
image under `g'` of the projection of the original point. -/
theorem pointsMap_baseChangeFibreMap (sq : IsPullback g'.hom f'.hom f.hom g.hom)
    (q : FieldValuedPoint B S hS Y'.1)
    (θ : points B S hS (fibreAtFieldValuedPoint B S hS f' q).1) :
    pointsMap B S hS
        (fibreAtFieldValuedPoint B S hS f (FieldValuedPoint.map B S hS Y'.1 g.hom q)).1
        (fibreAtFieldValuedPointProjection B S hS f
          (FieldValuedPoint.map B S hS Y'.1 g.hom q)).hom
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS f' q).1
          (baseChangeFibreMap B S hS sq q).hom θ) =
      pointsMap B S hS X'.1 g'.hom
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS f' q).1
          (fibreAtFieldValuedPointProjection B S hS f' q).hom θ) := by
  simpa only [pointsMap_comp, Function.comp_apply] using congrArg
    (fun k ↦ pointsMap B S hS _ k θ) (baseChangeFibreMap_hom_comp_projection B S hS sq q)

/-- The restriction of `(g')^*F` to the fibre of `f'` over `q` is the pullback along the
identification of fibres of the restriction of `F` to the fibre of `f` over the image of
`q`. -/
noncomputable def baseChangeFibreModulePullbackIso
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (q : FieldValuedPoint B S hS Y'.1)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f' q)).obj
        ((modulePullback B S hS g').obj F) ≅
      (modulePullback B S hS (baseChangeFibreMap B S hS sq q)).obj
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f
          (FieldValuedPoint.map B S hS Y'.1 g.hom q))).obj F) :=
  (modulePullbackCompIso B S hS (fibreAtFieldValuedPointProjection B S hS f' q) g').app F ≪≫
    eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj F)
      (baseChangeFibreMap_comp_projection B S hS sq q).symm) ≪≫
    ((modulePullbackCompIso B S hS (baseChangeFibreMap B S hS sq q)
      (fibreAtFieldValuedPointProjection B S hS f
        (FieldValuedPoint.map B S hS Y'.1 g.hom q))).app F).symm

/-- A point of the fibre of `f'` over `q` is weakly associated to the restriction of `(g')^*F`
exactly when the corresponding point of the fibre of `f` over the image of `q` is weakly
associated to the restriction of `F`. -/
theorem isWeaklyAssociatedPoint_baseChangeFibre_iff
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (q : FieldValuedPoint B S hS Y'.1)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (θ : points B S hS (fibreAtFieldValuedPoint B S hS f' q).1) :
    IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f' q)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f' q)).obj
          ((modulePullback B S hS g').obj F)) θ ↔
      IsWeaklyAssociatedPoint B S hS
        (fibreAtFieldValuedPoint B S hS f (FieldValuedPoint.map B S hS Y'.1 g.hom q))
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f
          (FieldValuedPoint.map B S hS Y'.1 g.hom q))).obj F)
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS f' q).1
          (baseChangeFibreMap B S hS sq q).hom θ) :=
  (isWeaklyAssociatedPoint_congr B S hS
      (baseChangeFibreModulePullbackIso B S hS sq q F) θ).trans
    (isWeaklyAssociatedPoint_modulePullback_iff B S hS (baseChangeFibreMap B S hS sq q)
      (isEtale_baseChangeFibreMap B S hS sq q) _ θ)

/-! ### Stacks 0CV2 -/

/-- In a cartesian square of algebraic spaces over `S` with vertical morphisms `f : X ⟶ Y` and
`f' : X' ⟶ Y'` and horizontal morphisms `g : Y' ⟶ Y` and `g' : X' ⟶ X`, and for an
`𝒪_X`-module `F` with `F' = (g')^*F`, the image under `g'` of a point of `WeakAss_{X'/Y'}(F')`
lies in `WeakAss_{X/Y}(F)`. -/
@[stacks 0CV2 "part (1), for the relative weak assassin of Stacks 0CV0 and with no finiteness \
hypothesis on f, which part (1) does not use: the two fibres are identified outright by pasting \
the cartesian squares"]
theorem isRelativeWeaklyAssociatedPoint_of_baseChange
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    {x' : points B S hS X'.1}
    (hx' : IsRelativeWeaklyAssociatedPoint B S hS f' ((modulePullback B S hS g').obj F) x') :
    IsRelativeWeaklyAssociatedPoint B S hS f F (pointsMap B S hS X'.1 g'.hom x') := by
  obtain ⟨q, hq, θ, hθ, hwa⟩ := hx'
  refine ⟨FieldValuedPoint.map B S hS Y'.1 g.hom q, ?_,
    pointsMap B S hS (fibreAtFieldValuedPoint B S hS f' q).1
      (baseChangeFibreMap B S hS sq q).hom θ, ?_,
    (isWeaklyAssociatedPoint_baseChangeFibre_iff B S hS sq q F θ).1 hwa⟩
  · rw [← pointsMap_class, hq, ← Function.comp_apply (f := pointsMap B S hS Y'.1 g.hom),
      ← pointsMap_comp, ← sq.w, pointsMap_comp, Function.comp_apply]
  · rw [pointsMap_baseChangeFibreMap B S hS sq q θ, hθ]

/-- **Part (2) of Stacks 0CV2 at a prescribed representative.** If some point of the fibre of
`f` over the image of a field-valued point `q` of `Y'`, lying above `x`, is weakly associated to
the restriction of `F`, then there is a point of `WeakAss_{X'/Y'}(F')` whose image under `g'` is
`x` and whose image under `f'` is the point of `Y'` presented by `q`. -/
theorem exists_isRelativeWeaklyAssociatedPoint_baseChange
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (q : FieldValuedPoint B S hS Y'.1) {x : points B S hS X.1}
    (hx : IsWeaklyAssociatedOnFibre B S hS f F
      (FieldValuedPoint.map B S hS Y'.1 g.hom q) x) :
    ∃ x' : points B S hS X'.1,
      IsRelativeWeaklyAssociatedPoint B S hS f' ((modulePullback B S hS g').obj F) x' ∧
        pointsMap B S hS X'.1 g'.hom x' = x ∧
          pointsMap B S hS X'.1 f'.hom x' = q.class B S hS Y'.1 := by
  obtain ⟨θ, hθ, hwa⟩ := hx
  have : IsIso (baseChangeFibreMap B S hS sq q).hom :=
    inferInstanceAs (IsIso (baseChangeFibreIso B S hS sq q).hom)
  obtain ⟨θ', hinv⟩ := pointsMap_surjective_of_isIso B S hS (baseChangeFibreMap B S hS sq q).hom θ
  have hwa' : IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f' q)
      ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f' q)).obj
        ((modulePullback B S hS g').obj F)) θ' :=
    (isWeaklyAssociatedPoint_baseChangeFibre_iff B S hS sq q F θ').2 (by rwa [hinv])
  have hclass : pointsMap B S hS X'.1 f'.hom
      (pointsMap B S hS (fibreAtFieldValuedPoint B S hS f' q).1
        (fibreAtFieldValuedPointProjection B S hS f' q).hom θ') = q.class B S hS Y'.1 :=
    (range_pointsMap_fibre_fieldMorphism B S hS f'.hom q).le ⟨θ', rfl⟩
  refine ⟨pointsMap B S hS (fibreAtFieldValuedPoint B S hS f' q).1
    (fibreAtFieldValuedPointProjection B S hS f' q).hom θ',
    ⟨q, hclass.symm, θ', rfl, hwa'⟩, ?_, hclass⟩
  rw [← pointsMap_baseChangeFibreMap B S hS sq q θ', hinv, hθ]

/-- In a cartesian square of algebraic spaces over `S` with vertical morphisms `f : X ⟶ Y` and
`f' : X' ⟶ Y'` and horizontal morphisms `g : Y' ⟶ Y` and `g' : X' ⟶ X`, and for a
quasi-coherent `𝒪_X`-module `F` with `F' = (g')^*F`: for every point `x` of `WeakAss_{X/Y}(F)`
and every point `y'` of `Y'` whose image in `Y` is the image of `x`, there is a point of
`WeakAss_{X'/Y'}(F')` whose image under `g'` is `x` and whose image under `f'` is `y'`. -/
@[stacks 0CV2 "part (2), for the relative weak assassin of Stacks 0CV0 and with no finiteness \
hypothesis on f, which the proof does not use: in place of the source's appeal to Stacks 05DC \
the witness is carried to a representative coming from y' by the ascent of weak association \
along the flat surjective base change identifying the two fibres"]
theorem exists_isRelativeWeaklyAssociatedPoint_baseChange_of_pointsMap_eq
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) {x : points B S hS X.1} {y' : points B S hS Y'.1}
    (hx : IsRelativeWeaklyAssociatedPoint B S hS f F x)
    (hy' : pointsMap B S hS Y'.1 g.hom y' = pointsMap B S hS X.1 f.hom x) :
    ∃ x' : points B S hS X'.1,
      IsRelativeWeaklyAssociatedPoint B S hS f' ((modulePullback B S hS g').obj F) x' ∧
        pointsMap B S hS X'.1 g'.hom x' = x ∧
          pointsMap B S hS X'.1 f'.hom x' = y' := by
  obtain ⟨q, hq, hfib⟩ :=
    exists_fieldValuedPoint_isWeaklyAssociatedOnFibre_of_pointsMap_eq B S hS f F hF hx g hy'
  obtain ⟨x', hx'wa, hx'g, hx'f⟩ :=
    exists_isRelativeWeaklyAssociatedPoint_baseChange B S hS sq F q hfib
  exact ⟨x', hx'wa, hx'g, hx'f.trans hq⟩

/-! ### Stacks 0CW2 -/

/-- Pasting the cartesian squares presenting `XZ = X ×_Y Z` and `X'Z = XZ ×_X X'` exhibits
`X'Z` as a fibre product of `X' ⟶ Y` with `Z ⟶ Y`, that is, as the base change of `X'` along
`Z ⟶ Y`. -/
theorem isPullback_comp_of_baseChange {X Y Z X'' XZ X'Z : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : X'' ⟶ X} {h : Z ⟶ Y} {pZ : XZ ⟶ X} {qZ : XZ ⟶ Z} {gZ : X'Z ⟶ XZ} {rZ : X'Z ⟶ X''}
    (sq : IsPullback pZ.hom qZ.hom f.hom h.hom)
    (sq' : IsPullback gZ.hom rZ.hom pZ.hom g.hom) :
    IsPullback rZ.hom (gZ.hom ≫ qZ.hom) (g.hom ≫ f.hom) h.hom :=
  sq'.flip.paste_vert sq

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `g : X'' ⟶ X` be a
morphism of algebraic spaces, and let `F` be an `𝒪_X`-module. If `WeakAss_{X/Y}(F)` is
contained in the image of `|X''| → |X|`, then for every `Z ⟶ Y` the set `WeakAss_{X_Z/Z}(F_Z)`
is contained in the image of `|X''_Z| → |X_Z|`, where `X_Z = X ×_Y Z` and
`X''_Z = X_Z ×_X X''`. -/
@[stacks 0CW2 "for the relative weak assassin of Stacks 0CV0, stated for an arbitrary module \
in place of a quasi-coherent one and with no finiteness hypothesis on f, neither of which is \
used by part (1) of Stacks 0CV2 or by Stacks 03H4. The base changes are presented by cartesian \
squares, X'_Z as X_Z ×_X X' exactly as the source's proof does, so g is not required to be \
given as a morphism over Y"]
theorem relativeWeaklyAssociatedPoints_baseChange_subset_range
    {X Y Z X'' XZ X'Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : X'' ⟶ X} {h : Z ⟶ Y}
    {pZ : XZ ⟶ X} {qZ : XZ ⟶ Z} {gZ : X'Z ⟶ XZ} {rZ : X'Z ⟶ X''}
    (sq : IsPullback pZ.hom qZ.hom f.hom h.hom)
    (sq' : IsPullback gZ.hom rZ.hom pZ.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : relativeWeaklyAssociatedPoints B S hS f F ⊆
      Set.range (pointsMap B S hS X''.1 g.hom)) :
    relativeWeaklyAssociatedPoints B S hS qZ ((modulePullback B S hS pZ).obj F) ⊆
      Set.range (pointsMap B S hS X'Z.1 gZ.hom) := by
  intro x hx
  obtain ⟨x'', hx''⟩ := hF (isRelativeWeaklyAssociatedPoint_of_baseChange B S hS sq F hx)
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS sq' x x'' hx''.symm
  exact ⟨w, hw⟩

end AlgebraicGeometry.Space

end
