module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent

/-!
# Pushforward of quasi-coherent modules along a morphism of affine schemes is restriction of
scalars

For a ring map `φ : R ⟶ S`, `Stacks.Descent.pullbackQcohConjugateIso` of
`StacksFrontier/AlgebraicGeometry/Descent/FpqcQuasicoherent.lean` identifies pullback of
quasi-coherent modules along `Spec.map φ` with extension of scalars along `φ`, conjugated by
the equivalence `AlgebraicGeometry.tildeEquiv`.  This file does the same for the *pushforward*,
which was missing:  `Spec.map φ` being an affine morphism, pushforward preserves quasi-coherence,
and the resulting functor is restriction of scalars along `φ`.

## Main definitions

* `Stacks.Descent.pushforwardTildeΓIso`:  the global sections over `Spec R` of the pushforward
  along `Spec.map φ` of `M^~`, for an `S`-module `M`, are `M` viewed as an `R`-module, naturally
  in `M`.
* `Stacks.Descent.tildeΓPushforwardTildeIso`:  the counit `fromTildeΓ` is invertible on those
  pushforwards, naturally in `M`.
* `Stacks.Descent.restrictScalarsCompTildeIso`:  the module associated to a restriction of
  scalars is the pushforward of the associated module, `(M_R)^~ ≅ (Spec.map φ)_* (M^~)`, naturally
  in the `S`-module `M`.  This is the pushforward counterpart of
  `Stacks.Descent.extendScalarsCompTildeIso`.
* `Stacks.Descent.restrictScalarsCompTildeEquivIso`: the same, phrased for the equivalence
  `AlgebraicGeometry.tildeEquiv` and the functor `Stacks.Descent.pushforwardQcoh`.
* `Stacks.Descent.pushforwardQcohConjugateIso`:  **the comparison.**  `pushforwardQcoh φ` is,
  up to `AlgebraicGeometry.tildeEquiv`, restriction of scalars along `φ`.

## Main results

* `Stacks.Descent.moduleSpecΓFunctor_map_restrictScalarsCompTildeIso_hom_app`: **the
  normalisation.**  On global sections `restrictScalarsCompTildeIso` is the canonical
  identification, namely `pushforwardSpecΓIso` composed with the unit of the tilde-`Γ`
  adjunction.  This is what makes the isomorphism usable:  it identifies it as *the* comparison
  map rather than as some isomorphism between the two sides.
* `Stacks.Descent.reflectsIsomorphisms_pushforwardQcoh`:  pushforward of quasi-coherent modules
  along a morphism of affine schemes reflects isomorphisms, transported from restriction of
  scalars along the comparison.

## Implementation notes

Unlike `extendScalarsCompTildeIso`, this comparison cannot be obtained by conjugating an
isomorphism of adjoints.  There, `ModuleCat.extendScalars φ ⋙ tilde` and
`tilde ⋙ Scheme.Modules.pullback (Spec.map φ)` are both composites of two *left* adjoints, so
`CategoryTheory.conjugateIsoEquiv` turns `pushforwardSpecΓIso` into the comparison.  Here
`AlgebraicGeometry.tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)` is a left adjoint
followed by a right adjoint, and `Scheme.Modules.pushforward (Spec.map φ)` has no left adjoint
available, so there is nothing to conjugate.

The construction instead goes through the counit `AlgebraicGeometry.Scheme.Modules.fromTildeΓ`,
which is invertible on the quasi-coherent modules by
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`, and in particular on the pushforward
of an associated sheaf by Mathlib's `AlgebraicGeometry.isIso_fromTildeΓ_pushforward`:  writing
`A := tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)`, the natural transformation
`Scheme.Modules.fromTildeΓNatTrans` whiskered by `A` is a natural isomorphism
`(A ⋙ Γ) ⋙ tilde.functor R ≅ A`, and `pushforwardTildeΓIso` identifies `A ⋙ Γ` with restriction
of scalars.

The normalisation lemma is proved from the right triangle identity of
`AlgebraicGeometry.tilde.adjunction`, which is the only description of
`moduleSpecΓFunctor.map (Scheme.Modules.fromTildeΓ _)` available:  it says that this map is a
retraction of the unit, which is what the naturality of the unit then turns into the claim.

Two steps have to be taken in term mode rather than by `rw`.  `Functor.map_comp` for
`moduleSpecΓFunctor` cannot be rewritten with, because the composition appearing under it is at
the category instance of `AlgebraicGeometry.Scheme.Modules`, which is a different instance from
the one on `SheafOfModules` that `rw` matches against;  `exact (…).map_comp _ _` crosses it, and
the isomorphism `asIso` of the counit likewise takes its `IsIso` argument positionally rather
than by instance search.  This is the crossing recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean`.

**No `@[stacks]` attribute is placed here.**  This is one of the two sub-statements the affine
case of the base-change assertion of [Stacks, Tag 02KG] is reduced to, and not that assertion;
the reduction of the general case to the affine one is
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_affineBases`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Descent

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The global sections over `Spec R` of the pushforward along `Spec.map φ` of the module
associated to an `S`-module `M` are `M` regarded as an `R`-module, naturally in `M`. -/
noncomputable def pushforwardTildeΓIso :
    tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) ⋙
        moduleSpecΓFunctor (R := R) ≅
      ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerLeft (tilde.functor S) (pushforwardSpecΓIso φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (tilde.toTildeΓNatIso (R := S)).symm
      (ModuleCat.restrictScalars φ.hom) ≪≫
    (ModuleCat.restrictScalars φ.hom).leftUnitor

/-- The counit `AlgebraicGeometry.Scheme.Modules.fromTildeΓ` is invertible on the pushforward
along `Spec.map φ` of an associated sheaf, naturally in the `S`-module. -/
noncomputable def tildeΓPushforwardTildeIso :
    (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)) ⋙
        moduleSpecΓFunctor (R := R) ⋙ tilde.functor R ≅
      tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) :=
  NatIso.ofComponents
    (fun M ↦ @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pushforward (Spec.map φ)).obj ((tilde.functor S).obj M)))
      (isIso_fromTildeΓ_pushforward φ ((tilde.functor S).obj M)))
    fun f ↦ Scheme.Modules.fromTildeΓNatTrans.naturality
      ((tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)).map f)

/-- **The module associated to a restriction of scalars is the pushforward of the associated
module:** `(M_R)^~ ≅ (Spec.map φ)_* (M^~)`, naturally in the `S`-module `M`.  This is the
pushforward counterpart of `Stacks.Descent.extendScalarsCompTildeIso`. -/
noncomputable def restrictScalarsCompTildeIso :
    ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R ≅
      tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) :=
  Functor.isoWhiskerRight (pushforwardTildeΓIso φ).symm (tilde.functor R) ≪≫
    tildeΓPushforwardTildeIso φ

/-- **The normalisation of `Stacks.Descent.restrictScalarsCompTildeIso`.**  On global sections
over `Spec R` the comparison is the canonical identification of both sides with `M` regarded as
an `R`-module:  the left-hand side by the unit of the tilde-`Γ` adjunction over `R`, the
right-hand side by `Stacks.Descent.pushforwardSpecΓIso` followed by the unit over `S`. -/
theorem moduleSpecΓFunctor_map_restrictScalarsCompTildeIso_hom_app (M : ModuleCat.{u} S) :
    (moduleSpecΓFunctor (R := R)).map ((restrictScalarsCompTildeIso φ).hom.app M) ≫
        (pushforwardSpecΓIso φ).hom.app ((tilde.functor S).obj M) =
      ((tilde.toTildeΓNatIso (R := R)).app
            ((ModuleCat.restrictScalars φ.hom).obj M)).inv ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((tilde.toTildeΓNatIso (R := S)).hom.app M) := by
  have hps : (pushforwardSpecΓIso φ).hom.app ((tilde.functor S).obj M) =
      (pushforwardTildeΓIso φ).hom.app M ≫ (ModuleCat.restrictScalars φ.hom).map
        ((tilde.toTildeΓNatIso (R := S)).hom.app M) := by
    simp [pushforwardTildeΓIso]
  have hrs : (restrictScalarsCompTildeIso φ).hom.app M =
      (tilde.functor R).map ((pushforwardTildeΓIso φ).inv.app M) ≫
        Scheme.Modules.fromTildeΓ ((Scheme.Modules.pushforward (Spec.map φ)).obj
          ((tilde.functor S).obj M)) := by
    simp only [restrictScalarsCompTildeIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerRight_app]
    rfl
  have hrs2 : (moduleSpecΓFunctor (R := R)).map ((restrictScalarsCompTildeIso φ).hom.app M) =
      (moduleSpecΓFunctor (R := R)).map
          ((tilde.functor R).map ((pushforwardTildeΓIso φ).inv.app M)) ≫
        (moduleSpecΓFunctor (R := R)).map (Scheme.Modules.fromTildeΓ
          ((Scheme.Modules.pushforward (Spec.map φ)).obj ((tilde.functor S).obj M))) := by
    rw [hrs]
    exact (moduleSpecΓFunctor (R := R)).map_comp _ _
  have hnat := (tilde.toTildeΓNatIso (R := R)).hom.naturality
    ((pushforwardTildeΓIso φ).inv.app M)
  have htri : (tilde.toTildeΓNatIso (R := R)).hom.app ((moduleSpecΓFunctor (R := R)).obj
        ((Scheme.Modules.pushforward (Spec.map φ)).obj ((tilde.functor S).obj M))) ≫
      (moduleSpecΓFunctor (R := R)).map (Scheme.Modules.fromTildeΓ
        ((Scheme.Modules.pushforward (Spec.map φ)).obj ((tilde.functor S).obj M))) = 𝟙 _ :=
    (tilde.adjunction (R := R)).right_triangle_components _
  simp only [Functor.comp_map, Functor.id_map] at hnat
  rw [Iso.eq_inv_comp, Iso.app_hom, hps, hrs2]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat, reassoc_of% htri]
  simp

/-- `AlgebraicGeometry.tildeEquiv` intertwines restriction of scalars with pushforward of
quasi-coherent modules. -/
noncomputable def restrictScalarsCompTildeEquivIso :
    ModuleCat.restrictScalars φ.hom ⋙ (tildeEquiv (R := R)).functor ≅
      (tildeEquiv (R := S)).functor ⋙ pushforwardQcoh φ :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _) (restrictScalarsCompTildeIso φ)

/-- **Pushforward of quasi-coherent modules along `Spec.map φ` is, up to the equivalence
`AlgebraicGeometry.tildeEquiv`, restriction of scalars along `φ`.**  This is the pushforward
counterpart of `Stacks.Descent.pullbackQcohConjugateIso`. -/
noncomputable def pushforwardQcohConjugateIso :
    pushforwardQcoh φ ≅
      (tildeEquiv (R := S)).inverse ⋙ ModuleCat.restrictScalars φ.hom ⋙
        (tildeEquiv (R := R)).functor :=
  ((tildeEquiv (R := S)).invFunIdAssoc (pushforwardQcoh φ)).symm ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := S)).inverse
      (restrictScalarsCompTildeEquivIso φ).symm

/-- Pushforward of quasi-coherent modules along a morphism of affine schemes reflects
isomorphisms:  a morphism of quasi-coherent modules on `Spec S` whose pushforward along
`Spec.map φ` is invertible is itself invertible.  Transported along
`Stacks.Descent.pushforwardQcohConjugateIso` from the corresponding fact for restriction of
scalars. -/
lemma reflectsIsomorphisms_pushforwardQcoh : (pushforwardQcoh φ).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_iso (pushforwardQcohConjugateIso φ).symm

end Stacks.Descent

end
