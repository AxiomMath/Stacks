module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedConservativity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullback
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing descends along `ε` on a Zariski slice

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 08H7.  The zero-detection assertion of Stacks 08H8 says that `ε^*` reflects the zero
object: `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_general`.  That statement
is global on `S`, and a descent which proceeds by induction on a cohomological gap needs it
*localized*: from the vanishing of `ε^*𝓕` over the étale site of an open `V` of `S` one has to
conclude the vanishing of `𝓕|_V`.

This module proves that localization, and it does so formally — no part of the proof of
Stacks 08H8 is re-run.  Two inputs suffice.

* **The unit of `ε^* ⊣ ε_*` is a monomorphism.**  Its image under `ε^*` is a split monomorphism,
  by the triangle identity of the adjunction, and `ε^*` reflects monomorphisms
  (`AlgebraicGeometry.SmallEtale.reflectsMonomorphisms_associatedModule`, which is itself left
  exactness of `ε^*` together with zero detection).  So the unit is a monomorphism, which is
  strictly more than zero detection and is where Stacks 08H8 enters.
* **`ε_*` commutes with restriction to a slice**:
  `AlgebraicGeometry.SmallEtale.pushforwardOverIso` below, the pushforward square
  `ε_* ⋙ (- |_V) ≅ (- |_{ε(V)}) ⋙ (ε_V)_*`.  It is the right-adjoint companion of the
  localization square `AlgebraicGeometry.SmallEtale.associatedModuleOverIso`, and like it it comes
  from `SheafOfModules.pushforwardComp` and `SheafOfModules.pushforwardCongr₂`: the two routes
  `(C/V) ⥤ S_étale` round the square are *equal* functors, so the comparison of continuous
  functors is the identity.

Given these, restriction to the slice over `V` is exact, so it carries the unit to a
monomorphism `𝓕|_V ⟶ (ε_*ε^*𝓕)|_V ≅ (ε_V)_*((ε^*𝓕)|_{ε(V)})`, whose target vanishes with
`(ε^*𝓕)|_{ε(V)}`; a subobject of a zero object is zero.

## Main definitions

* `AlgebraicGeometry.SmallEtale.pushforwardOverIso`: the pushforward square
  `ε_* ⋙ (- |_V) ≅ (- |_{ε(V)}) ⋙ (ε_V)_*`.

## Main results

* `AlgebraicGeometry.SmallEtale.mono_associatedModuleAdjunction_unit`: the unit of `ε^* ⊣ ε_*` is
  a monomorphism.
* `AlgebraicGeometry.SmallEtale.isZero_over_of_isZero_over_associatedModule`: **vanishing of
  `ε^*𝓕` on the étale site of an open `V` forces vanishing of `𝓕|_V`.**
* `AlgebraicGeometry.SmallEtale.isZero_homology_over_of_isZero_homology_over_associatedModule`:
  the same for a cohomology sheaf of an object of `D(𝒪_S)`, through the comparison
  `AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso`.
* `Stacks.SheafOfModules.isZero_over_over_of_isZero_over`: a bookkeeping lemma on iterated
  slices — if `𝓕|_{W.left}` vanishes then so does `(𝓕|_U)|_W`.

## Implementation notes

**No `@[stacks]` attribute is attached to anything here.**  The zero-detection assertion of
Stacks 08H8 is carried by
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_toZariskiModulePullback`; what is below is its
localization, which is not a clause of 08H8 or of any other tag.

The functor `ε^*` is spelled `SheafOfModules.pullback (structureMap B S hS)` — which is
`AlgebraicGeometry.SmallEtale.associatedModule` by definition — rather than
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, because that is the spelling in which the
localization square `AlgebraicGeometry.SmallEtale.associatedModuleOverIso` is stated.  The
`OfSheaf` retyping is the one at which `reflectsMonomorphisms_associatedModule` lives, and the
passage between the two is a `have` with an explicit type, which is a definitional check rather
than a synthesis; this is the device documented in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedConservativity.lean`.

## References

* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u w w'

namespace Stacks.SheafOfModules

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **An iterated-slice bookkeeping lemma.**  If the restriction of `𝓕` to the slice over
`W.left` vanishes, then the restriction of `𝓕|_U` to the iterated slice over `W : Over U`
vanishes.

Both are read off the same sections of `𝓕`: the sections of `(𝓕|_U)|_W` over an object `Z` of
`(C/U)/W` are the sections of `𝓕` over `Z.left.left`, and `Z.left.left` carries an arrow to
`W.left`, so those sections are among the ones `𝓕|_{W.left}` has. -/
public theorem isZero_over_over_of_isZero_over (M : _root_.SheafOfModules.{w} R) (U : C)
    (W : Over U) (h : IsZero (M.over W.left)) : IsZero ((M.over U).over W) := by
  refine isZero_of_forall_subsingleton_sections _ fun Z => ?_
  exact Stacks.subsingleton_of_isZero h (op (Over.mk Z.unop.hom.left))

/-- **Restriction to a smaller slice preserves vanishing.**  If `𝓕|_T` vanishes and there is an
arrow `Z ⟶ T`, then `𝓕|_Z` vanishes: the sections of `𝓕|_Z` are sections of `𝓕` over objects
which, composing with that arrow, already lie over `T`. -/
public theorem isZero_over_of_hom (M : _root_.SheafOfModules.{w} R) {Z T : C} (g : Z ⟶ T)
    (h : IsZero (M.over T)) : IsZero (M.over Z) := by
  refine isZero_of_forall_subsingleton_sections _ fun W => ?_
  exact Stacks.subsingleton_of_isZero h (op (Over.mk (W.unop.hom ≫ g)))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `ε_*` commutes with restriction to a slice -/

/-- Restriction to the slice over an open `V` of `S`, followed by the inclusion of that slice,
is the inclusion of the small Zariski site followed by nothing: the two routes
`(S_Zar/V) ⥤ S_étale` round the localization square of `ε` at `V` are the *same* functor, both
sending an open `W ≤ V` to the object `ε(W)` of the small étale site.

This is `CategoryTheory.Over.post_comp_forget` at the inclusion, recorded as an isomorphism
because that is what `SheafOfModules.pushforwardCongr₂` consumes. -/
public def forgetPostIso (V : S.Opens) :
    Over.forget V ⋙ opensToSmallEtale B S hS ≅
      Over.post (opensToSmallEtale B S hS) ⋙
        Over.forget ((opensToSmallEtale B S hS).obj V) :=
  Iso.refl _

/-- The route "restrict to the slice over `V`, then include the small Zariski site into the small
étale site" is continuous: it is a composite of continuous functors. -/
public instance isContinuous_forget_opensToSmallEtale (V : S.Opens) :
    (Over.forget V ⋙ opensToSmallEtale B S hS).IsContinuous
      ((Opens.grothendieckTopology ↥S).over V) (topology B S hS) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ↥S) _

/-- The route "intersect with `V` inside the small étale site, then forget down to the small
étale site" is continuous: it is a composite of continuous functors. -/
public instance isContinuous_post_forget (V : S.Opens) :
    (Over.post (opensToSmallEtale B S hS) ⋙
        Over.forget ((opensToSmallEtale B S hS).obj V)).IsContinuous
      ((Opens.grothendieckTopology ↥S).over V) (topology B S hS) :=
  Functor.isContinuous_comp _ _ _ ((topology B S hS).over
    ((opensToSmallEtale B S hS).obj V)) _

/-- **`ε_*` commutes with restriction to a slice.**  For an open `V` of `S`, restricting an
`𝒪`-module on the small étale site of `S` to the slice over `ε(V)` and then pushing forward along
the localized comparison `AlgebraicGeometry.SmallEtale.sliceStructureMap` agrees with pushing
forward along `ε` and restricting to the slice over `V`.

This is the right-adjoint companion of the localization square
`AlgebraicGeometry.SmallEtale.associatedModuleOverIso`.  Both sides are pushforwards of sheaves
of modules along the two routes round the square; those routes are equal functors
(`AlgebraicGeometry.SmallEtale.forgetPostIso`) and the two composite comparisons of structure
sheaves agree, so `SheafOfModules.pushforwardComp` and `SheafOfModules.pushforwardCongr₂`
identify them. -/
public def pushforwardOverIso (V : S.Opens) :
    SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
          ((opensToSmallEtale B S hS).obj V) ⋙
        SheafOfModules.pushforward.{u} (sliceStructureMap B S hS V) ≅
      SheafOfModules.pushforward.{u} (structureMap B S hS) ⋙
        SheafOfModules.overFunctor.{u} S.ringCatSheaf V :=
  SheafOfModules.pushforwardComp.{u} (sliceStructureMap B S hS V) (𝟙 _) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _ (forgetPostIso B S hS V) (by ext : 2; rfl) ≪≫
    (SheafOfModules.pushforwardComp.{u} (𝟙 _) (structureMap B S hS)).symm

/-! ### The unit of `ε^* ⊣ ε_*` is a monomorphism -/

/-- **The unit of `ε^* ⊣ ε_*` is a monomorphism.**  Its image under `ε^*` is a split
monomorphism, by the triangle identity of the adjunction, and `ε^*` reflects monomorphisms
(`AlgebraicGeometry.SmallEtale.reflectsMonomorphisms_associatedModule`), so the unit is a
monomorphism.

This is strictly stronger than the zero-detection assertion of Stacks 08H8 and is deduced from
it: zero detection plus left exactness is what makes `ε^*` reflect monomorphisms. -/
public theorem mono_associatedModuleAdjunction_unit
    (𝓕 : SheafOfModules.{u} S.ringCatSheaf) :
    Mono ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).unit.app 𝓕) := by
  have hrefl : (SheafOfModules.pullback.{u} (structureMap B S hS)).ReflectsMonomorphisms :=
    reflectsMonomorphisms_associatedModule B S hS
  have hsplit : IsSplitMono ((SheafOfModules.pullback.{u} (structureMap B S hS)).map
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).unit.app 𝓕)) :=
    IsSplitMono.mk' ⟨(SheafOfModules.pullbackPushforwardAdjunction.{u}
        (structureMap B S hS)).counit.app _,
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (structureMap B S hS)).left_triangle_components 𝓕⟩
  exact hrefl.reflects _ inferInstance

/-! ### Vanishing descends along `ε` on a slice -/

/-- **Vanishing descends along `ε` on a Zariski slice.**  Let `V` be an open of `S` and let `𝓕`
be an `𝒪_S`-module.  If the restriction of `ε^*𝓕` to the small étale site of `V` — that is, to
the slice of `S_étale` over `ε(V)` — vanishes, then `𝓕|_V` vanishes.

Restriction to a slice is exact, so it carries the monomorphism
`AlgebraicGeometry.SmallEtale.mono_associatedModuleAdjunction_unit` to a monomorphism
`𝓕|_V ⟶ (ε_*ε^*𝓕)|_V`; the square
`AlgebraicGeometry.SmallEtale.pushforwardOverIso` identifies the target with
`(ε_V)_*((ε^*𝓕)|_{ε(V)})`, which vanishes with its argument because `(ε_V)_*` is additive. -/
public theorem isZero_over_of_isZero_over_associatedModule (V : S.Opens)
    (𝓕 : SheafOfModules.{u} S.ringCatSheaf)
    (h : IsZero (((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕).over
      ((opensToSmallEtale B S hS).obj V))) :
    IsZero (𝓕.over V) := by
  have hpush : IsZero ((SheafOfModules.pushforward.{u} (sliceStructureMap B S hS V)).obj
      (((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕).over
        ((opensToSmallEtale B S hS).obj V))) :=
    (SheafOfModules.pushforward.{u} (sliceStructureMap B S hS V)).map_isZero h
  have htgt : IsZero ((((SheafOfModules.pushforward.{u} (structureMap B S hS)).obj
      ((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕))).over V) :=
    hpush.of_iso ((pushforwardOverIso B S hS V).app
      ((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕)).symm
  let := mono_associatedModuleAdjunction_unit B S hS 𝓕
  let : PreservesFiniteLimits (SheafOfModules.overFunctor.{u} S.ringCatSheaf V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  let : (SheafOfModules.overFunctor.{u} S.ringCatSheaf V).PreservesMonomorphisms :=
    inferInstance
  exact IsZero.of_mono ((SheafOfModules.overFunctor.{u} S.ringCatSheaf V).map
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS)).unit.app 𝓕)) htgt

section Derived

variable [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **Vanishing of a cohomology sheaf descends along `ε^*_D` on a Zariski slice.**  If the
restriction of `Hⁿ(ε^*_D E)` to the small étale site of an open `V` of `S` vanishes, then so does
`Hⁿ(E)|_V`, for an arbitrary `E : D(𝒪_S)`.

This is `AlgebraicGeometry.SmallEtale.isZero_over_of_isZero_over_associatedModule` fed with the
comparison `AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso`, which turns
the hypothesis into vanishing of `(ε^*Hⁿ E)|_{ε(V)}`. -/
public theorem isZero_homology_over_of_isZero_homology_over_associatedModule (V : S.Opens)
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (n : ℤ)
    (h : IsZero (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheaf B S hS)) n).obj
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E)).over
        ((opensToSmallEtale B S hS).obj V))) :
    IsZero (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} S.ringCatSheaf) n).obj E).over V) := by
  refine isZero_over_of_isZero_over_associatedModule B S hS V _ ?_
  exact h.of_iso ((SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
    ((opensToSmallEtale B S hS).obj V)).mapIso
      ((associatedModuleDerivedHomologyIso B S hS n).app E).symm)

end Derived

end AlgebraicGeometry.SmallEtale

end
