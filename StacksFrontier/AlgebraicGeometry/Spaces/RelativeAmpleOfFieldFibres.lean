module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType

/-!
# Relative ampleness of a proper morphism from its fibres over fields

Stacks 0D3D gives, for a proper morphism `f : X ⟶ Y` of algebraic spaces and an invertible
`𝒪_X`-module `L`, an open subspace `V ⊆ Y` such that a morphism `g : Y' ⟶ Y` factors through `V`
exactly when the pullback of `L` is ample on `X ×_Y Y' ⟶ Y'` (Stacks 0D31). This file reads that
open subspace on field-valued points: `g` factors through `V` exactly when, over every
field-valued point of `Y'`, the fibre of `f` carries the pullback of `L` as a relatively ample
module. In particular `L` is ample relative to `f` as soon as it is ample on every fibre of `f`
over a field.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_fieldFibres_of_isProper`: the open
  subspace of Stacks 0D3D, with its characterization on field-valued points.
* `AlgebraicGeometry.Space.isRelativelyAmple_of_isProper_of_fieldFibres`: a module ample on every
  fibre over a field is ample relative to `f`.
* `AlgebraicGeometry.Space.isRelativelyAmple_of_isProper_of_schemeFibres`: the same, with each
  fibre presented by a scheme on which the restriction of `L` is invertible and relatively ample
  in the sense of schemes (Stacks 01VH), read through Stacks 0D32.

Nothing here is registered: these are the forms of Stacks 0D3D consumed by the moduli of curves.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The tautological field-valued point of the scheme of a field-valued point `t` maps to `t`. -/
theorem fieldValuedPoint_map_tautological {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (t : FieldValuedPoint B S hS F) :
    FieldValuedPoint.map B S hS (yoneda.obj t.siteObject) (yonedaEquiv.symm t.value)
      ⟨t.carrier, t.contained, t.toBase, 𝟙 t.siteObject⟩ = t := by
  obtain ⟨K, hK, tb, v⟩ := t
  simp only [FieldValuedPoint.map, FieldValuedPoint.mk.injEq, heq_eq_eq, true_and]
  change F.map (𝟙 _).op v = v
  simp

/-- The class of a field-valued point `t` of `F` lies in the image of the points of the scheme
of `t` under the morphism `t` classifies. -/
theorem class_mem_range_pointsMap_yonedaEquiv_symm {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (t : FieldValuedPoint B S hS F) :
    t.class B S hS F ∈ Set.range
      (pointsMap B S hS (yoneda.obj t.siteObject) (yonedaEquiv.symm t.value)) :=
  ⟨FieldValuedPoint.class B S hS _ ⟨t.carrier, t.contained, t.toBase, 𝟙 t.siteObject⟩, by
    rw [pointsMap_class, fieldValuedPoint_map_tautological]⟩

/-- **Stacks 0D3D, read on field-valued points.** Let `f : X ⟶ Y` be a proper morphism of
algebraic spaces over `S` and `L` an invertible `𝒪_X`-module. There is an open subspace
`V ⊆ Y` such that

* a morphism `g : Y' ⟶ Y` of algebraic spaces factors through `V` if and only if the pullback of
  `L` to `X' = Y' ×_Y X` is ample on `X'/Y'` (Stacks 0D3D, with ampleness as in Stacks 0D31);
* a morphism `g : Y' ⟶ Y` factors through `V` if and only if, for every field-valued point
  `t : Spec K ⟶ Y'`, some (equivalently every) fibre `X_t` of `f` over `g ∘ t` carries the
  pullback of `L` as a module ample relative to `X_t ⟶ Spec K`.

The second clause is the first at the field-valued points of `Y'`, with Stacks 03IE: a morphism
factors through an open subspace exactly when it does so on points. -/
theorem exists_isOpenSubspace_factors_iff_fieldFibres_of_isProper
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      (∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L))) ∧
      ∀ ⦃Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y),
        (∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
          ∀ t : FieldValuedPoint B S hS Y'.1,
            ∃ (X'' : AlgebraicSpaces B S hS) (p'' : X'' ⟶ X)
              (f'' : X'' ⟶ schemeSpace t.siteObject),
              IsPullback p'' f'' f (ObjectProperty.homMk (yonedaEquiv.symm t.value) ≫ g) ∧
                IsRelativelyAmple B S hS f'' ((modulePullback B S hS p'').obj L) := by
  obtain ⟨V, hV, hVf⟩ :=
      exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper B S hS hf hL
  refine ⟨V, hV, hVf, fun Y' g => ⟨?_, fun hfib => ?_⟩⟩
  · rintro ⟨l, hl⟩ t
    let a : schemeSpace t.siteObject ⟶ Y :=
      ObjectProperty.homMk (yonedaEquiv.symm t.value) ≫ g
    have hsq := AlgebraicSpaces.isPullback_fiberProduct B S hS f a
    refine ⟨_, _, _, hsq, (hVf a _ _ hsq).mp ⟨yonedaEquiv.symm t.value ≫ l, ?_⟩⟩
    refine (Category.assoc _ _ _).trans ?_
    rw [hl]
    rfl
  · refine (factorsThrough_openSubspace_iff_points B S hS Y.2 Y'.2 V hV g.hom).mpr ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := Quot.exists_rep y
    obtain ⟨X'', p'', f'', hsq, hamp⟩ := hfib t
    obtain ⟨l, hl⟩ := (hVf _ p'' f'' hsq).mpr hamp
    obtain ⟨w, hw⟩ := class_mem_range_pointsMap_yonedaEquiv_symm t
    refine ⟨pointsMap B S hS _ l w, ?_⟩
    refine (pointsMap_comp_apply B S hS l V.ι w).symm.trans ?_
    rw [hl]
    change pointsMap B S hS _ (yonedaEquiv.symm t.value ≫ g.hom) w = _
    rw [pointsMap_comp_apply]
    exact congrArg (pointsMap B S hS Y'.1 g.hom) hw

/-- **A module ample on the fibres over fields of a proper morphism is relatively ample.** Let
`f : X ⟶ Y` be a proper morphism of algebraic spaces and `L` an invertible `𝒪_X`-module such that
over every field-valued point `t : Spec K ⟶ Y` some fibre `X_t` of `f` carries the pullback of
`L` as a module ample relative to `X_t ⟶ Spec K`. Then `L` is ample relative to `f`.

By `exists_isOpenSubspace_factors_iff_fieldFibres_of_isProper` the identity of `Y` factors
through the open subspace of Stacks 0D3D, and the pullback of `L` along the identity is `L`. -/
theorem isRelativelyAmple_of_isProper_of_fieldFibres
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (hfib : ∀ t : FieldValuedPoint B S hS Y.1,
      ∃ (X'' : AlgebraicSpaces B S hS) (p'' : X'' ⟶ X)
        (f'' : X'' ⟶ schemeSpace t.siteObject),
        IsPullback p'' f'' f (ObjectProperty.homMk (yonedaEquiv.symm t.value)) ∧
          IsRelativelyAmple B S hS f'' ((modulePullback B S hS p'').obj L)) :
    IsRelativelyAmple B S hS f L := by
  obtain ⟨V, -, hVf, hVpts⟩ := exists_isOpenSubspace_factors_iff_fieldFibres_of_isProper hf hL
  have hid := (hVpts (𝟙 Y)).mpr fun t => by simpa only [Category.comp_id] using hfib t
  have hsq : IsPullback (𝟙 X) f f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (isRelativelyAmple_congr f ((modulePullbackIdIso B S hS X).app L)).mp
    ((hVf (𝟙 Y) (𝟙 X) f hsq).mp hid)

/-- **The fibre of a morphism over a field, presented by a scheme, in the sense of 0D31.** Let
`L` be an invertible `𝒪_X`-module on an algebraic space `X`, `t` a field-valued point of an
algebraic space `Y`, and `V` a scheme over `Spec K` with a morphism `q` to `X` (in the
application, a scheme presenting the fibre of a morphism `X ⟶ Y` over `t`). If
the restriction of `L` to `V` is invertible and ample relative to `V ⟶ Spec K` in the sense of
schemes (Stacks 01VH), then the pullback of `L` to that fibre is ample relative to the fibre in
the sense of Stacks 0D31. This is Stacks 0D32, clause (2) implies clause (1). -/
theorem isRelativelyAmple_fibre_of_scheme
    {X Y : AlgebraicSpaces B S hS} {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (t : FieldValuedPoint B S hS Y.1) (V : BigFppfOver B S hS) (v : V ⟶ t.siteObject)
    (q : yoneda.obj V ⟶ X.1)
    (hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj V)
      (baseChangeModule B S hS L V q))
    (hamp : @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B S hS).map v)
      (baseChangeModule B S hS L V q) hinv) :
    IsRelativelyAmple B S hS
      (ObjectProperty.homMk (yoneda.map v) : representedAlgebraicSpace B S hS V ⟶
        representedAlgebraicSpace B S hS t.siteObject)
      ((modulePullback B S hS (ObjectProperty.homMk q :
        representedAlgebraicSpace B S hS V ⟶ X)).obj L) := by
  let p'' : representedAlgebraicSpace B S hS V ⟶ X := ObjectProperty.homMk q
  have hL'' := Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (f := smallEtaleRingedToposModulesHom B S hS p'') (L := L) (hL := hL)
  refine isRelativelyAmple_of_exists_scheme _ _ hL'' t.siteObject (Iso.refl _)
    ⟨V, Iso.refl _, ?_⟩
  have e : baseChangeModule B S hS L V q ≅
      baseChangeModule B S hS ((modulePullback B S hS p'').obj L) V (Iso.refl _).hom :=
    baseChangeModuleCompIso B S hS p'' L V (𝟙 _)
  have hpre : yoneda.preimage ((Iso.refl (yoneda.obj V)).hom ≫
      (ObjectProperty.homMk (yoneda.map v) : representedAlgebraicSpace B S hS V ⟶
        representedAlgebraicSpace B S hS t.siteObject).hom ≫
      (Iso.refl (yoneda.obj t.siteObject)).hom) = v := by
    apply yoneda.map_injective
    simp
  rw [hpre]
  have := hinv
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj V)
      (baseChangeModule B S hS ((modulePullback B S hS p'').obj L) V (Iso.refl _).hom) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
  exact ⟨inferInstance, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp hamp⟩

/-- **A module relatively ample on scheme fibres over fields of a proper morphism is relatively
ample.** Let `f : X ⟶ Y` be a proper morphism of algebraic spaces and `L` an invertible
`𝒪_X`-module. Suppose that over every field-valued point `t : Spec K ⟶ Y` some scheme `V` over
`Spec K` presents the fibre of `f` (a cartesian square of presheaves), and that the restriction
of `L` to `V` is invertible and ample relative to `V ⟶ Spec K` in the sense of Stacks 01VH. Then
`L` is ample relative to `f` (Stacks 0D31).

This is `isRelativelyAmple_of_isProper_of_fieldFibres`, with each fibre read through Stacks 0D32
(`isRelativelyAmple_fibre_of_scheme`). -/
theorem isRelativelyAmple_of_isProper_of_schemeFibres
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (hfib : ∀ t : FieldValuedPoint B S hS Y.1,
      ∃ (V : BigFppfOver B S hS) (v : V ⟶ t.siteObject) (q : yoneda.obj V ⟶ X.1),
        IsPullback q (yoneda.map v) f.hom (yonedaEquiv.symm t.value) ∧
          ∃ hinv : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj V)
              (baseChangeModule B S hS L V q),
            @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B S hS).map v)
              (baseChangeModule B S hS L V q) hinv) :
    IsRelativelyAmple B S hS f L := by
  refine isRelativelyAmple_of_isProper_of_fieldFibres hf hL fun t => ?_
  obtain ⟨V, v, q, hsq, hinv, hamp⟩ := hfib t
  exact ⟨representedAlgebraicSpace B S hS V, ObjectProperty.homMk q,
    ObjectProperty.homMk (yoneda.map v),
    isPullback_homMk B S hS X.2 (isAlgebraicSpace_yoneda B S hS _) Y.2
      (isAlgebraicSpace_yoneda B S hS _) hsq,
    isRelativelyAmple_fibre_of_scheme hL t V v q hinv hamp⟩

end AlgebraicGeometry.Space

end
