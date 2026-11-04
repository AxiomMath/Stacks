module

public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace

/-!
# The inverse-image ringed space of a composite

Let `(S, 𝒪_S)` be a ringed space and let `j : W ⟶ X` and `i : X ⟶ S` be continuous maps. The
inverse-image ringed spaces `(X, i⁻¹𝒪_S)` and `(W, (j ∘ i)⁻¹𝒪_S)` are related by a canonical
morphism of ringed spaces lying over `j`, and its composite with the projection of
`(X, i⁻¹𝒪_S)` to `(S, 𝒪_S)` is the projection of `(W, (j ∘ i)⁻¹𝒪_S)`. Pullback of modules along
it is the sheaf-theoretic inverse image `j⁻¹` read on modules over the inverse images of `𝒪_S`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.inverseImageCompHom` is the structure map
  `i⁻¹𝒪_S ⟶ j_*((j ∘ i)⁻¹𝒪_S)`.
* `AlgebraicGeometry.RingedSpace.inverseImageCompProjection` is the morphism of ringed spaces
  `(W, (j ∘ i)⁻¹𝒪_S) ⟶ (X, i⁻¹𝒪_S)` over `j`.
* `AlgebraicGeometry.RingedSpace.inverseImageCompModulePullback` is the induced inverse image
  `j⁻¹ : Mod(i⁻¹𝒪_S) ⥤ Mod((j ∘ i)⁻¹𝒪_S)`, with
  `AlgebraicGeometry.RingedSpace.inverseImageCompModulePushforward` its right adjoint.

## Main results

* `AlgebraicGeometry.RingedSpace.inverseImageCompProjection_comp`: the triangle over `(S, 𝒪_S)`,
  which characterises the morphism: its structure map is the unique one whose transpose along
  `i⁻¹ ⊣ i_*` is the unit of `(j ∘ i)⁻¹ ⊣ (j ∘ i)_*` at `𝒪_S`.
* `AlgebraicGeometry.RingedSpace.homEquiv_inverseImageCompHom`: the transpose of the structure
  map along `i⁻¹ ⊣ i_*` is that unit.
* `AlgebraicGeometry.RingedSpace.inverseImageCompProjection_base` and
  `AlgebraicGeometry.RingedSpace.inverseImageCompProjection_c`: the underlying continuous map is
  `j` and the structure map is `inverseImageCompHom`.

## Implementation notes

The direct image of a sheaf along a composite is the composite of the direct images *on the
nose*, `TopCat.Presheaf.Pushforward.comp_eq`, so the unit of `(j ∘ i)⁻¹ ⊣ (j ∘ i)_*` at `𝒪_S`
already has the type that the transpose along `i⁻¹ ⊣ i_*` consumes, and no comparison
isomorphism between the two inverse images of `𝒪_S` on `W` intervenes in the construction.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 008C](https://stacks.math.columbia.edu/tag/008C)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public section

open CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpace

variable (S : RingedSpace.{u, u}) {X W : TopCat.{u}} (i : X ⟶ S.carrier) (j : W ⟶ X)

/-- The structure map `i⁻¹𝒪_S ⟶ j_*((j ∘ i)⁻¹𝒪_S)`: the transpose along `i⁻¹ ⊣ i_*` of the unit
of `(j ∘ i)⁻¹ ⊣ (j ∘ i)_*` at `𝒪_S`. -/
noncomputable def inverseImageCompHom :
    (TopCat.Sheaf.pullback CommRingCat.{u} i).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} j).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (j ≫ i)).obj S.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).homEquiv _ _).symm
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (j ≫ i)).unit.app S.sheaf)

/-- The structure map is recovered from the unit of `(j ∘ i)⁻¹ ⊣ (j ∘ i)_*` at `𝒪_S` by
adjunction. -/
theorem homEquiv_inverseImageCompHom :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).homEquiv S.sheaf
        ((TopCat.Sheaf.pushforward CommRingCat.{u} j).obj
          ((TopCat.Sheaf.pullback CommRingCat.{u} (j ≫ i)).obj S.sheaf))
        (inverseImageCompHom S i j) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (j ≫ i)).unit.app S.sheaf :=
  Equiv.apply_symm_apply _ _

/-- The canonical morphism of ringed spaces `(W, (j ∘ i)⁻¹𝒪_S) ⟶ (X, i⁻¹𝒪_S)`: the continuous
map `j`, with structure map `inverseImageCompHom`. -/
noncomputable def inverseImageCompProjection :
    inverseImage S (j ≫ i) ⟶ inverseImage S i :=
  InducedCategory.homMk
    { base := j
      c := (inverseImageCompHom S i j).hom }

/-- The continuous map underlying `inverseImageCompProjection` is `j`. -/
@[simp]
theorem inverseImageCompProjection_base :
    (inverseImageCompProjection S i j).hom.base = j := rfl

/-- The structure map of `inverseImageCompProjection` is `inverseImageCompHom`. -/
@[simp]
theorem inverseImageCompProjection_c :
    (inverseImageCompProjection S i j).hom.c = (inverseImageCompHom S i j).hom := rfl

/-- **The triangle over `(S, 𝒪_S)`**: the canonical morphism followed by the projection of
`(X, i⁻¹𝒪_S)` is the projection of `(W, (j ∘ i)⁻¹𝒪_S)`. This characterises the structure map,
being the statement that its transpose is the unit at `𝒪_S`. -/
theorem inverseImageCompProjection_comp :
    inverseImageCompProjection S i j ≫ inverseImageProjection S i =
      inverseImageProjection S (j ≫ i) := by
  refine InducedCategory.hom_ext (PresheafedSpace.hext _ _ rfl (heq_of_eq ?_))
  exact congrArg (fun t => t.hom) (homEquiv_inverseImageCompHom S i j)

/-- The inverse image `j⁻¹ : Mod(i⁻¹𝒪_S) ⥤ Mod((j ∘ i)⁻¹𝒪_S)`: pullback of sheaves of modules
along `inverseImageCompProjection`. -/
noncomputable abbrev inverseImageCompModulePullback :
    SheafOfModules.{u} (structureSheafRing (inverseImage S i)) ⥤
      SheafOfModules.{u} (structureSheafRing (inverseImage S (j ≫ i))) :=
  modulePullback (inverseImageCompProjection S i j)

/-- The direct image `j_* : Mod((j ∘ i)⁻¹𝒪_S) ⥤ Mod(i⁻¹𝒪_S)` along the canonical morphism. -/
noncomputable abbrev inverseImageCompModulePushforward :
    SheafOfModules.{u} (structureSheafRing (inverseImage S (j ≫ i))) ⥤
      SheafOfModules.{u} (structureSheafRing (inverseImage S i)) :=
  modulePushforward (inverseImageCompProjection S i j)

/-- The inverse image of modules along the canonical morphism is left adjoint to the direct
image. -/
noncomputable def inverseImageCompModuleAdjunction :
    inverseImageCompModulePullback S i j ⊣ inverseImageCompModulePushforward S i j :=
  modulePullbackPushforwardAdjunction (inverseImageCompProjection S i j)

end AlgebraicGeometry.RingedSpace

end
