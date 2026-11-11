module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSource
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessinger
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Morphism

/-!
# The endpoints of a deformation of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. Forgetting the arrow and one of its
two endpoints sends a deformation of `f` to a deformation of `X`, respectively of `Y`; taking
both at once is the morphism of deformation categories
`Def_{X ⟶ Y} ⟶ Def_X × Def_Y`
which supplies two of the arrows of the exact sequence of [Stacks Project, Tag 0E3V].

This file builds the target-forgetful functor (the source-forgetful one is
`Deformation.Examples.schemeMorphismSourceForgetful`), reads both as morphisms of categories
over `𝒞_Λ`, and constructs the two arrows of Tag 0E3V that they induce:

* on infinitesimal automorphisms, `Inf(Def_{X ⟶ Y}) → Inf(Def_X) × Inf(Def_Y)`, which is
  **injective** — the exactness of `0 → Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)` asserted at the
  first spot of the source's sequence;
* on tangent spaces, `T Def_{X ⟶ Y} → T Def_X × T Def_Y`, whose **image** consists exactly of
  the pairs of first-order deformations of `X` and of `Y` between which `f` deforms.

## Main definitions

* `Deformation.Examples.schemeMorphismTargetForgetful`: the functor from deformations of
  `f : X ⟶ Y` to deformations of its target `Y`.
* `Deformation.Examples.schemeMorphismSourceBased`,
  `Deformation.Examples.schemeMorphismTargetBased`: the two forgetful functors as morphisms of
  categories over `𝒞_Λ`.
* `Deformation.Examples.schemeMorphismInfinitesimalPair`: the arrow
  `Inf(Def_{X ⟶ Y}) → Inf(Def_X) × Inf(Def_Y)` of Tag 0E3V.
* `Deformation.Examples.schemeMorphismTangentPair`: the arrow
  `T Def_{X ⟶ Y} → T Def_X × T Def_Y` of Tag 0E3V.

## Main results

* `Deformation.Examples.schemeMorphismTargetForgetful_comp_projection`: the target-forgetful
  functor commutes with the two projections to `𝒞_Λ`.
* `Deformation.Examples.eq_id_of_endpoints_eq_id`: a self-arrow of a deformation of `f` both
  of whose endpoint components are the identity is the identity. This is the faithfulness that
  makes the infinitesimal arrow injective.
* `Deformation.Examples.injective_schemeMorphismInfinitesimalPair`: **Tag 0E3V, exactness at
  the first spot.**
* `Deformation.Examples.exists_schemeMorphismTangentPair_eq_iff`: **Tag 0E3V, the image of the
  arrow `T Def_{X ⟶ Y} → T(Def_X × Def_Y)`**, described as in the last paragraph of the
  source's proof: a pair of first-order deformations is hit exactly when `f` deforms along it.
* `Deformation.Examples.schemeMorphismDeformation_endpointArrows`: the package of the three
  preceding assertions.

## Implementation notes

The criterion that makes the infinitesimal arrow injective —
`Deformation.injective_prod_inducedInfinitesimalLinearMapOfEq`, for two `1`-morphisms out of
one category that are jointly faithful on self-arrows — is general, and lives in
`StacksFrontier.Deformation.Applications.TwoFibreProductInfRow`, where the same argument gives
exactness of the `Inf`-row of Tag 06L5 at its first spot. Only the faithfulness itself,
`Deformation.Examples.eq_id_of_endpoints_eq_id`, is geometric and so is here.

The source writes `Inf(Def_X × Def_Y)` and `T(Def_X × Def_Y)` for the invariants of the
`2`-fibre product of `Def_X` and `Def_Y` over `𝒞_Λ`. Those are the plain products
`Inf(Def_X) × Inf(Def_Y)` and `T Def_X × T Def_Y` of the invariants of the two factors, and the
arrows of the sequence are the pairs of the arrows induced by the two forgetful functors; that
is how they are written here, with `LinearMap.prod`, exactly as
`Deformation.tangentProjPair` does for a `2`-fibre product. No universe lift is needed: the two
deformation categories of the endpoints have the same object universe.

Four of the six arrows of the source's sequence are **not** here, and neither is any of the
remaining exactness. The missing terms are `Der_k(𝒪_Y, f_*𝒪_X)` and
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`, and the missing arrows are the two into and out of the
derivations and the obstruction map into the Ext group; all three rest on the geometric form of
[Stacks Project, Tag 08U8] for the pair of endpoint deformations, which this library has only
for a diagram of sheaves of rings on a single space
(`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction`). What is proved of the last
paragraph of the source's proof is its geometric content — which pairs of first-order
deformations of the endpoints `f` deforms along — with the identification of the obstruction to
that with an Ext class left out.

Three hypotheses are carried rather than proved. That `Def_{X ⟶ Y}` is a deformation category
is the second assertion of [Stacks Project, Tag 0E3U], which the library proves
as `Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategoryProjection` in
`StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional`, a
module this file does not import; and
that `Def_X` and `Def_Y` are deformation categories is the assertion of
[Stacks Project, Tag 0DY8] for `Deformation.Examples.SchemeDeformationCategory`, which the
library proves for the category of all flat families of schemes
(`Deformation.Examples.satisfiesRS_flatSchemeFamilyProjection`) but not for the deformations of
a fixed scheme, that category being given directly rather than as a slice.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 07W6](https://stacks.math.columbia.edu/tag/07W6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-! ### The target-forgetful functor -/

section TargetForgetful

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- The functor from deformations of a morphism `f : X ⟶ Y` of schemes over the residue field
to deformations of its target `Y`, keeping the family that deforms `Y` together with its
identification of the fibre over the closed point and forgetting the family that deforms
`X`. -/
@[stacks 0E3V "the target-forgetting functor Def_{X ⟶ Y} ⟶ Def_Y, one half of the \
morphism of deformation categories Def_{X ⟶ Y} ⟶ Def_X × Def_Y of the source's proof"]
def schemeMorphismTargetForgetful :
    schemeMorphismDeformationCategory f pX pY hf ⥤
      SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY) where
  obj P :=
    { base := P.left.base
      scheme := P.left.target
      toBase := P.left.targetToBase
      flat := P.left.target_flat
      specialMap := P.hom.target
      specialCartesian := by
        simpa [schemeMorphismFamilySpecialFiber, baseSpecMap_eq_residueSpecMap]
          using P.hom.target_pullback }
  map {P Q} h :=
    { base := h.left.base
      map := h.left.target
      cartesian := h.left.target_pullback
      special_compat := congrArg SchemeMorphismFamily.Hom.target (Over.w h) }
  map_id _ := by apply SchemeDeformationCategory.Hom.ext <;> rfl
  map_comp := fun {_ _ _} h g => by apply SchemeDeformationCategory.Hom.ext <;> rfl

/-- The deformation of the target attached to a deformation `P` of `f` has the base of `P`. -/
@[simp]
theorem schemeMorphismTargetForgetful_obj_base
    (P : schemeMorphismDeformationCategory f pX pY hf) :
    ((schemeMorphismTargetForgetful f pX pY hf).obj P).base = P.left.base :=
  rfl

/-- The target-forgetful functor sends a morphism `h` of deformations of `f` to a morphism
with the same base map as `h`. -/
@[simp]
theorem schemeMorphismTargetForgetful_map_base
    {P Q : schemeMorphismDeformationCategory f pX pY hf} (h : P ⟶ Q) :
    ((schemeMorphismTargetForgetful f pX pY hf).map h).base = h.left.base :=
  rfl

/-- The target-forgetful functor commutes with the projections of the two deformation
categories to `𝒞_Λ`, so it is a morphism of categories over the base category. -/
@[stacks 0E3V "that the target-forgetting functor is a morphism of deformation categories \
over the base category"]
theorem schemeMorphismTargetForgetful_comp_projection :
    schemeMorphismTargetForgetful f pX pY hf ⋙
        schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY) =
      schemeMorphismDeformationCategoryProjection f pX pY hf :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

/-- The target-forgetful functor reflects isomorphisms: an arrow of deformations of `f` whose
target component is invertible has invertible component on bases, and an arrow of flat families
over an isomorphism of bases is an isomorphism. -/
instance schemeMorphismTargetForgetful_reflectsIsomorphisms :
    (schemeMorphismTargetForgetful f pX pY hf).ReflectsIsomorphisms where
  reflects {P Q} h _ := by
    have hbase : IsIso h.left.base := by
      rw [← schemeMorphismTargetForgetful_map_base f pX pY hf h]
      exact (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
        (Over.mk pY)).map_isIso ((schemeMorphismTargetForgetful f pX pY hf).map h)
    have hleft : IsIso h.left := SchemeMorphismFamily.isIso_of_isIso_base h.left
    have hmap : IsIso ((Over.forget
      (schemeMorphismFamilySpecialFiber f pX pY hf)).map h) := hleft
    exact isIso_of_reflects_iso h (Over.forget _)

/-- The two endpoint-forgetting functors are jointly faithful on self-arrows: an arrow from a
deformation of `f` to itself is a triple consisting of a map of bases and maps of the two
endpoint families, and the two endpoint components of such an arrow determine the map of bases
as well. -/
theorem eq_id_of_endpoints_eq_id {P : schemeMorphismDeformationCategory f pX pY hf} (g : P ⟶ P)
    (hs : (schemeMorphismSourceForgetful f pX pY hf).map g = 𝟙 _)
    (ht : (schemeMorphismTargetForgetful f pX pY hf).map g = 𝟙 _) :
    g = 𝟙 P := by
  apply Over.OverMorphism.ext
  refine SchemeMorphismFamily.Hom.ext ?_ ?_ ?_
  · exact congrArg SchemeDeformationCategory.Hom.base hs
  · exact congrArg SchemeDeformationCategory.Hom.map hs
  · exact congrArg SchemeDeformationCategory.Hom.map ht

/-! ### The two forgetful functors as morphisms over the base category -/

/-- The source-forgetful functor `Def_{X ⟶ Y} ⟶ Def_X`, as a morphism of categories over
`𝒞_Λ`. -/
@[stacks 0E3V "the source component of the morphism Def_{X → Y} → Def_X × Def_Y"]
def schemeMorphismSourceBased :
    BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf) ⥤ᵇ
      BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) where
  toFunctor := schemeMorphismSourceForgetful f pX pY hf
  w := schemeMorphismSourceForgetful_comp_projection f pX pY hf

/-- The target-forgetful functor `Def_{X ⟶ Y} ⟶ Def_Y`, as a morphism of categories over
`𝒞_Λ`. -/
@[stacks 0E3V "the target component of the morphism Def_{X → Y} → Def_X × Def_Y"]
def schemeMorphismTargetBased :
    BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf) ⥤ᵇ
      BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)) where
  toFunctor := schemeMorphismTargetForgetful f pX pY hf
  w := schemeMorphismTargetForgetful_comp_projection f pX pY hf

/-! ### The two arrows of Tag 0E3V out of the deformation category of the morphism -/

/-- **Stacks 0E3V**, the arrow `Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)`: the pair of the
`k`-linear maps on infinitesimal automorphisms induced by the two endpoint-forgetting morphisms
of deformation categories. -/
@[stacks 0E3V "the arrow Inf(Def_{X → Y}) → Inf(Def_X × Def_Y), as the pair of the maps \
induced on infinitesimal automorphisms by the two endpoint-forgetting 1-morphisms"]
def schemeMorphismInfinitesimalPair
    (hM : SatisfiesRS (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    {x₀ : schemeMorphismDeformationCategory f pX pY hf}
    (PM : ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf) x₀)
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj x₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup PM hM
    letI := naturalLocalizedTangentModule PM hM
    letI := naturalLocalizedTangentAddCommGroup QX hX
    letI := naturalLocalizedTangentModule QX hX
    letI := naturalLocalizedTangentAddCommGroup QY hY
    letI := naturalLocalizedTangentModule QY hY
    localizedAutomorphismFunctorTangent PM →ₗ[k]
      localizedAutomorphismFunctorTangent QX × localizedAutomorphismFunctorTangent QY :=
  letI := naturalLocalizedTangentAddCommGroup PM hM
  letI := naturalLocalizedTangentModule PM hM
  letI := naturalLocalizedTangentAddCommGroup QX hX
  letI := naturalLocalizedTangentModule QX hX
  letI := naturalLocalizedTangentAddCommGroup QY hY
  letI := naturalLocalizedTangentModule QY hY
  LinearMap.prod
    (inducedInfinitesimalLinearMapOfEq (schemeMorphismSourceForgetful f pX pY hf)
      (schemeMorphismSourceForgetful_comp_projection f pX pY hf) hM hX PM QX)
    (inducedInfinitesimalLinearMapOfEq (schemeMorphismTargetForgetful f pX pY hf)
      (schemeMorphismTargetForgetful_comp_projection f pX pY hf) hM hY PM QY)

/-- **Stacks 0E3V, exactness at the first spot.** The arrow
`Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)` is injective, so the sequence
`0 → Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)` is exact: an infinitesimal automorphism of a
deformation of `f` is a pair of infinitesimal automorphisms of the two endpoint deformations
compatible with the arrow, and such a pair determines it. -/
@[stacks 0E3V "exactness at the first spot: the arrow Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) \
is injective"]
theorem injective_schemeMorphismInfinitesimalPair
    (hM : SatisfiesRS (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : SatisfiesRS (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    {x₀ : schemeMorphismDeformationCategory f pX pY hf}
    (PM : ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf) x₀)
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj x₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj x₀)) :
    letI := naturalLocalizedTangentAddCommGroup PM hM
    letI := naturalLocalizedTangentModule PM hM
    letI := naturalLocalizedTangentAddCommGroup QX hX
    letI := naturalLocalizedTangentModule QX hX
    letI := naturalLocalizedTangentAddCommGroup QY hY
    letI := naturalLocalizedTangentModule QY hY
    Function.Injective (schemeMorphismInfinitesimalPair f pX pY hf hM hX hY PM QX QY) :=
  injective_prod_inducedInfinitesimalLinearMapOfEq
    (schemeMorphismSourceForgetful f pX pY hf) (schemeMorphismTargetForgetful f pX pY hf)
    (schemeMorphismSourceForgetful_comp_projection f pX pY hf)
    (schemeMorphismTargetForgetful_comp_projection f pX pY hf) hM hX hY PM QX QY
    (fun _ g h₁ h₂ => eq_id_of_endpoints_eq_id f pX pY hf g h₁ h₂)

/-- **Stacks 0E3V**, the arrow `T Def_{X ⟶ Y} → T(Def_X × Def_Y)`: the pair of the `k`-linear
maps on tangent modules induced by the two endpoint-forgetting morphisms of deformation
categories. -/
@[stacks 0E3V "the arrow T Def_{X → Y} → T(Def_X × Def_Y), as the pair of the maps induced \
on tangent modules by the two endpoint-forgetting 1-morphisms"]
def schemeMorphismTangentPair
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k) :
    ↥(tangentModuleAt.{u, u, u}
        (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
        hM M) →ₗ[k]
      ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M) ×
        ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M) :=
  LinearMap.prod
    (tangentMapAt.{u, u, u} hM hX (schemeMorphismSourceBased f pX pY hf) M)
    (tangentMapAt.{u, u, u} hM hY (schemeMorphismTargetBased f pX pY hf) M)

/-- `schemeMorphismTangentPair` sends a tangent vector `t` to the pair of its images under the
tangent maps of the source-forgetful and target-forgetful functors. -/
@[simp]
theorem schemeMorphismTangentPair_apply
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    (t : ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf))
      hM M)) :
    schemeMorphismTangentPair f pX pY hf hM hX hY M t =
      (tangentMapAt.{u, u, u} hM hX (schemeMorphismSourceBased f pX pY hf) M t,
        tangentMapAt.{u, u, u} hM hY (schemeMorphismTargetBased f pX pY hf) M t) :=
  rfl

/-- The image of the class of `mε` under a tangent map equals the class of `y` exactly when the
image of `mε` in the fibre is isomorphic to `y`. -/
private theorem tangentMapAt_tangentClassAt_eq_iff
    {𝓕 𝓖 : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k)}
    (h𝓕 : IsDeformationCategory.{u, u, u} 𝓕.p) (h𝓖 : IsDeformationCategory.{u, u, u} 𝓖.p)
    (φ : 𝓕 ⥤ᵇ 𝓖) (M : FGModuleCat.{u} k)
    (mε : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (y : 𝓖.p.Fiber ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    tangentMapAt.{u, u, u} h𝓕 h𝓖 φ M (tangentClassAt.{u, u, u} 𝓕 h𝓕 M mε) =
        tangentClassAt.{u, u, u} 𝓖 h𝓖 M y ↔
      IsIsomorphic ((fiberFunctor φ ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε)
        y := by
  rw [tangentMapAt_tangentClassAt, tangentClassAt_eq_iff]

/-- **Stacks 0E3V**, the image of the arrow `T Def_{X ⟶ Y} → T(Def_X × Def_Y)`. A pair of
first-order deformations `X_ε` of `X` and `Y_ε` of `Y` is in the image exactly when `f` deforms
along it, that is, when some first-order deformation of `f` has the two given deformations as
its endpoints up to isomorphism in the fibre. This is the content of the last paragraph of the
source's proof; the identification of the obstruction to such a deformation with a class in
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` is not proved here. -/
@[stacks 0E3V "the image of the arrow T Def_{X → Y} → T(Def_X × Def_Y): a pair of first-order \
deformations of X and of Y is hit exactly when f deforms along it. The identification of the \
obstruction with a class in Ext^1(Lf^* NL_{Y/k}, O_X) is NOT proved"]
theorem exists_schemeMorphismTangentPair_eq_iff
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) :
    (∃ t, schemeMorphismTangentPair f pX pY hf hM hX hY M t =
        (tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M xε,
          tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M yε)) ↔
      ∃ mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M),
        IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) xε ∧
          IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) yε := by
  have hX' := tangentMapAt_tangentClassAt_eq_iff hM hX (schemeMorphismSourceBased f pX pY hf) M
  have hY' := tangentMapAt_tangentClassAt_eq_iff hM hY (schemeMorphismTargetBased f pX pY hf) M
  constructor
  · rintro ⟨t, hts⟩
    obtain ⟨mε, rfl⟩ := tangentClassAt_surjective.{u, u, u}
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM M t
    exact ⟨mε, (hX' mε xε).mp (congrArg Prod.fst hts), (hY' mε yε).mp (congrArg Prod.snd hts)⟩
  · rintro ⟨mε, hs, ht⟩
    exact ⟨_, Prod.ext ((hX' mε xε).mpr hs) ((hY' mε yε).mpr ht)⟩

/-- **Stacks 0E3V, the part of the six-term exact sequence that this file establishes.**

For a morphism `f : X ⟶ Y` of schemes over `k`, the morphism of deformation categories
`Def_{X ⟶ Y} ⟶ Def_X × Def_Y` of the source's proof induces two of the six arrows of the
source's sequence, and the package records them together with what is proved about exactness:

1. the sequence `0 → Inf(Def_{X ⟶ Y}) → Inf(Def_X × Def_Y)` is exact, i.e. the arrow on
   infinitesimal automorphisms is injective;
2. the arrow on tangent spaces is the pair of the maps induced by the two forgetful morphisms;
3. a pair of first-order deformations of `X` and of `Y` is in the image of that arrow exactly
   when `f` deforms along it.

The three remaining arrows of the source's sequence — the two involving
`Der_k(𝒪_Y, f_*𝒪_X)` and the obstruction map into
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` — and exactness at the second, third and fourth spots are not
proved; see the implementation notes of this file.

The deformation hypothesis on `Def_{X ⟶ Y}` is supplied by
`Deformation.Examples.isDeformationCategory_schemeMorphismDeformationCategory` from condition
(RS) for the category of all flat families of morphisms of schemes. -/
@[stacks 0E3V "PARTIAL. Of the six-term exact sequence this establishes: the arrow \
Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) and the arrow T Def_{X → Y} → T(Def_X × Def_Y), both as \
the pairs of the maps induced by the source- and target-forgetting 1-morphisms \
Def_{X → Y} → Def_X and Def_{X → Y} → Def_Y; exactness at the FIRST spot, i.e. exactness of \
0 → Inf(Def_{X → Y}) → Inf(Def_X × Def_Y); and the description of the IMAGE of \
T Def_{X → Y} → T(Def_X × Def_Y) as the pairs of first-order deformations of X and Y along \
which f deforms. NOT established: the terms Der_k(O_Y, f_*O_X) and Ext^1(Lf^* NL_{Y/k}, O_X), \
the three arrows Inf(Def_X × Def_Y) → Der_k(O_Y, f_*O_X), Der_k(O_Y, f_*O_X) → T Def_{X → Y} \
and T(Def_X × Def_Y) → Ext^1(Lf^* NL_{Y/k}, O_X), and exactness at the second, third and \
fourth spots. Hypotheses carried rather than proved: condition (RS) for Example 0E3T, and \
that Def_X and Def_Y are deformation categories"]
theorem schemeMorphismDeformation_endpointArrows
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    {x₀ : schemeMorphismDeformationCategory f pX pY hf}
    (PM : ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf) x₀)
    (QX : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj x₀))
    (QY : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj x₀))
    (M : FGModuleCat.{u} k) :
    letI := naturalLocalizedTangentAddCommGroup PM hM.satisfiesRS
    letI := naturalLocalizedTangentModule PM hM.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QX hX.satisfiesRS
    letI := naturalLocalizedTangentModule QX hX.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup QY hY.satisfiesRS
    letI := naturalLocalizedTangentModule QY hY.satisfiesRS
    Function.Injective (schemeMorphismInfinitesimalPair f pX pY hf hM.satisfiesRS
        hX.satisfiesRS hY.satisfiesRS PM QX QY) ∧
      (∀ t, schemeMorphismTangentPair f pX pY hf hM hX hY M t =
        (tangentMapAt.{u, u, u} hM hX (schemeMorphismSourceBased f pX pY hf) M t,
          tangentMapAt.{u, u, u} hM hY (schemeMorphismTargetBased f pX pY hf) M t)) ∧
      ∀ (xε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
        (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)),
        (∃ t, schemeMorphismTangentPair f pX pY hf hM hX hY M t =
            (tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
                (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M xε,
              tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
                (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
                hY M yε)) ↔
          ∃ mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber
              ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M),
            IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf)
                ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) xε ∧
              IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf)
                ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) yε :=
  ⟨injective_schemeMorphismInfinitesimalPair f pX pY hf hM.satisfiesRS hX.satisfiesRS
      hY.satisfiesRS PM QX QY,
    fun _ => rfl,
    fun xε yε => exists_schemeMorphismTangentPair_eq_iff f pX pY hf hM hX hY M xε yε⟩

end TargetForgetful

end Deformation.Examples

end
