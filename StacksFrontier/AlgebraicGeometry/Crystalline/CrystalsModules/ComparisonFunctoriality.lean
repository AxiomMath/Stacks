module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal
public import StacksFrontier.Topology.OpensMapFinal

/-!
# Functoriality of the crystalline comparison map, and the crystal property of `𝒪_{X/S}`

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation.  A morphism `f : (U, T, δ) ⟶ (U', T', δ')` of that site gives the comparison map
`c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules, [Stacks, Tag 07IQ] at sheaf level, and `F`
is a *crystal in `𝒪_{X/S}`-modules* when every `c_f` is an isomorphism.

The proof of [Stacks, Tag 07IT] argues that a quasi-coherent `F` is a crystal by pulling a
presentation `⊕_J 𝒪 → ⊕_I 𝒪 → F → 0` back along `f^*`: in other words it uses that `c_f` is a
map *natural in `F`*, between two functors of `F` that commute with the coproducts and the
cokernel of a presentation, and that it is an isomorphism at `F = 𝒪_{X/S}`.  Neither of those two
inputs was available in this library, and this file supplies them:

* `c_f` is natural in the module, at the level of the `f`-map and at the level of the comparison
  map itself;
* `c_f` is an isomorphism at `F = 𝒪_{X/S}`, that is, the structure sheaf of the big crystalline
  site is a crystal in `𝒪_{X/S}`-modules.

Along the way it proves the composition law for the restriction of a morphism of `CRIS(X/S)` over
an open of the ambient scheme of its target, which is what makes the `f`-map a cocycle and is the
shape in which the source's Zariski-local reduction moves a morphism along a covering.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionMap` — the restriction to
  the ambient scheme of an object of a morphism of presheaves of `𝒪_{X/S}`-modules.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheafMap` — the same for a
  morphism of sheaves of `𝒪_{X/S}`-modules, making the restriction `F ↦ F_T` functorial in `F` at
  sheaf level.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_comp` — **the restrictions of
  a morphism of `CRIS(X/S)` over the opens of the ambient scheme compose**: the restriction of
  `f ≫ g` over an open `W` is the restriction of `f` over the preimage of `W` followed by the
  restriction of `g` over `W`.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleFMap_naturality` and
  `Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheaf_naturality` — **the `f`-map
  `F_{T'} ⟶ f_* F_T` is natural in the module**, for presheaves and for sheaves of modules.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf_naturality` — **the
  comparison map `c_f : f^* F_{T'} ⟶ F_T` of sheaves of modules is natural in the module.**
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf_unit` — the comparison
  map at `F = 𝒪_{X/S}` is Mathlib's canonical map from the pullback of the unit to the unit.
* `Crystalline.GlobalCrystallineSituation.isSheafCrystal_unit` — **the structure sheaf `𝒪_{X/S}`
  of the big crystalline site is a crystal in `𝒪_{X/S}`-modules.**
* `Stacks.Topology.final_opensMap` — the preimage functor on the opens of a continuous map of
  spaces is final.  This is what makes the pullback of a free sheaf of modules along it free, and
  so is the hypothesis under which a presentation travels along a comparison map; it is used by
  `StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.CrystalPresentationPullback` as well
  as here.

## What is proved elsewhere

The implications of [Stacks, Tag 07IT] are not proved here, and this file carries **no**
`@[stacks 07IT]` attribute: what it adds are two of the inputs the source's argument for
"quasi-coherent implies a crystal" consumes, namely that the comparison map is natural in the
module and that it is an isomorphism at `𝒪_{X/S}`.

That implication, (1) ⇒ (2)(b), is
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal` on the big site
and `Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite` of
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentCrystal` on the small one; the
other half, (1) ⇒ (2)(a), is
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` and its
small-site twin.  The propagation from the unit to a module with a presentation is carried out
through `Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp`, a test of the crystal
condition that names no pullback functor and so survives the universe lift of the module sections
at which a global presentation on a crystalline site lives; the Zariski locality that
quasi-coherence forces, quasi-coherence supplying a presentation only on a covering of the target,
uses the composition law for the restriction of a morphism proved here together with
`Crystalline.GlobalCrystallineSituation.Thickening.fmapComp_comp`, the resulting cocycle for
composition with the `f`-map, and `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`.

## Implementation notes

The composition law for the restriction of a morphism over an open is proved by cancelling the
structure morphism of the restriction of the target, which is a monomorphism: both composites are
then the morphism to the target itself through the structure morphism of the source.  The two
sides have the same type only because the preimage of an open under a composite is the iterated
preimage, which holds definitionally; `rw` cannot be used to relate them, since the equation is
not type-correct at the reduced transparency at which the rewriting tactics operate, so the proof
goes through `cancel_mono` and leaves the normalisation to `simp`.

Naturality in the module is immediate on sections: the `f`-map is, over an open `W` of the ambient
scheme of the target, the restriction map of the module along the restriction of the morphism over
`W`, so its naturality square is the naturality square of the morphism of modules.  Naturality of
the comparison map follows by transposing along the adjunction between pullback and pushforward of
sheaves of modules, the `f`-map being the transpose of the comparison map: the two transposed
sides are the two sides of the `f`-map's naturality square.

That the comparison map at the unit is an isomorphism is Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`, which the comparison map at `𝒪_{X/S}` equals
definitionally — the restriction of `𝒪_{X/S}` to the ambient scheme *is* the unit of the restricted
structure sheaf, and the `f`-map at the unit *is* `SheafOfModules.unitToPushforwardObjUnit`.  The
hypothesis of Mathlib's invertibility is that the functor of Zariski sites along which one pulls
back is final, which for the preimage functor on opens holds because the opens of a space form a
poset with a greatest element: the structured arrow category at an open `W` has the terminal open
as a terminal object, every square in a poset commuting.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}} {A B C : Thickening S}

/-- **The restrictions of a morphism of `CRIS(X/S)` over the opens of the ambient schemes
compose.**  For `f : (U, T, δ) ⟶ (U', T', δ')` and `g : (U', T', δ') ⟶ (U'', T'', δ'')` and an
open `W` of `T''`, the restriction of `f ≫ g` over `W` is the restriction of `f` over `g⁻¹W`
followed by the restriction of `g` over `W`.

This is the cocycle condition that makes the `f`-maps of
[Stacks, Tag 07IQ] compose, and it is the form in which the Zariski-local reduction in the proof
of [Stacks, Tag 07IT] moves a morphism along a covering of its target. -/
theorem restrictOpenMap_comp (g : A ⟶ B) (h : B ⟶ C) (W : C.thickening.target.scheme.Opens) :
    restrictOpenMap (g ≫ h) W =
      restrictOpenMap g (h.targetHom.hom ⁻¹ᵁ W) ≫ restrictOpenMap h W := by
  refine (cancel_mono (C.restrictOpenHom W)).1 ?_
  simpa using restrictOpenMap_restrictOpenHom (g ≫ h) W

/-- **The restrictions of a morphism of `CRIS(X/S)` over the opens of the ambient schemes
compose**, read on the natural transformation
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctorMap` whose components they
are. -/
theorem restrictOpenFunctorMap_app_comp (g : A ⟶ B) (h : B ⟶ C)
    (W : C.thickening.target.scheme.Opens) :
    (restrictOpenFunctorMap (g ≫ h)).app W =
      (restrictOpenFunctorMap g).app (h.targetHom.hom ⁻¹ᵁ W) ≫
        (restrictOpenFunctorMap h).app W :=
  restrictOpenMap_comp g h W

/-- **The restriction to the ambient scheme of an object of a morphism of presheaves of
`𝒪_{X/S}`-modules.**  Over an open `W` it is the given morphism over the restriction of the object
to `W`; this makes the restriction `F ↦ F_T` of [Stacks, Tag 07IQ] a functor in the module, being
the image under the pushforward along the restrictions to the opens of the ambient scheme. -/
noncomputable def moduleRestrictionMap {M N : PresheafOfModules.{u} (crisRing S)} (φ : M ⟶ N)
    (A : Thickening S) : moduleRestriction M A ⟶ moduleRestriction N A :=
  (PresheafOfModules.pushforward₀ A.restrictOpenFunctor (crisRing S)).map φ

/-- **The `f`-map of [Stacks, Tag 07IQ] is natural in the presheaf of modules.**  Over an open `W`
of the ambient scheme of the target both sides are the restriction map along the restriction of
the morphism over `W` followed, in the two possible orders, by the given morphism of presheaves of
modules; so the square is the naturality square of that morphism. -/
theorem moduleFMap_naturality {M N : PresheafOfModules.{u} (crisRing S)} (φ : M ⟶ N)
    (g : A ⟶ B) :
    moduleRestrictionMap φ B ≫ moduleFMap N g =
      moduleFMap M g ≫ (PresheafOfModules.pushforward (F := Opens.map g.targetHom.hom.base)
        (restrictionFMap (crisRing S) g)).map (moduleRestrictionMap φ A) := by
  ext W x
  exact (PresheafOfModules.naturality_apply φ (restrictOpenMap g W.unop).op x).symm

/-- **The restriction to the ambient scheme of an object of a morphism of sheaves of
`𝒪_{X/S}`-modules.**  It is the restriction of the underlying morphism of presheaves of modules,
the restriction of a sheaf being computed on the same sections; this makes the restriction
`F ↦ F_T` a functor in the module at sheaf level, which is the level at which the crystal
condition of [Stacks, Tag 07IS] is read. -/
noncomputable def moduleRestrictionSheafMap
    {M N : SheafOfModules.{u} (crystallineStructureSheaf S)} (ψ : M ⟶ N) (A : Thickening S) :
    moduleRestrictionSheaf M A ⟶ moduleRestrictionSheaf N A :=
  ⟨moduleRestrictionMap ψ.val A⟩

/-- The underlying morphism of presheaves of modules of `moduleRestrictionSheafMap ψ A` is
`moduleRestrictionMap ψ.val A`. -/
@[simp]
theorem moduleRestrictionSheafMap_val
    {M N : SheafOfModules.{u} (crystallineStructureSheaf S)} (ψ : M ⟶ N) (A : Thickening S) :
    (moduleRestrictionSheafMap ψ A).val = moduleRestrictionMap ψ.val A := rfl

/-- **The `f`-map of [Stacks, Tag 07IQ] for sheaves of modules is natural in the module.**  A
morphism of sheaves of modules is its underlying morphism of presheaves of modules, so this is
`Crystalline.GlobalCrystallineSituation.Thickening.moduleFMap_naturality`. -/
theorem moduleFMapSheaf_naturality {M N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (ψ : M ⟶ N) (g : A ⟶ B) :
    moduleRestrictionSheafMap ψ B ≫ moduleFMapSheaf N g =
      moduleFMapSheaf M g ≫
        (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g)).map
          (moduleRestrictionSheafMap ψ A) :=
  SheafOfModules.Hom.ext (moduleFMap_naturality ψ.val g)

/-- **The comparison map `c_f : f^* F_{T'} ⟶ F_T` of sheaves of modules is natural in the
module.**  This is the sense in which the proof of [Stacks, Tag 07IT] treats `c_f`: a map between
two functors of `F`, so that knowing it at `𝒪_{X/S}` and knowing that both functors commute with
the coproducts and the cokernel of a presentation determines it on every module with a
presentation.

The proof transposes along the adjunction between pullback and pushforward of sheaves of modules,
under which the comparison map corresponds to the `f`-map; the two transposed sides are the two
sides of
`Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheaf_naturality`. -/
theorem moduleComparisonSheaf_naturality
    {M N : SheafOfModules.{u} (crystallineStructureSheaf S)} (ψ : M ⟶ N) (g : A ⟶ B) :
    (SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).map
          (moduleRestrictionSheafMap ψ B) ≫ moduleComparisonSheaf N g =
      moduleComparisonSheaf M g ≫ moduleRestrictionSheafMap ψ A := by
  refine ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B)
      (moduleRestrictionSheaf N A)).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    ← moduleFMapSheaf_eq_moduleComparisonSheaf, ← moduleFMapSheaf_eq_moduleComparisonSheaf]
  exact moduleFMapSheaf_naturality ψ g

/-- **The restriction of the structure sheaf of the big crystalline site to the ambient scheme of
an object is the unit module of the restricted structure sheaf.**  Both have the ring of sections
of `𝒪_{X/S}` over the restriction of the object as their sections over an open. -/
theorem moduleRestrictionSheaf_unit (A : Thickening S) :
    moduleRestrictionSheaf (SheafOfModules.unit (crystallineStructureSheaf S)) A =
      SheafOfModules.unit A.ringRestrictionSheaf := rfl

/-- **The `f`-map of the structure sheaf of the big crystalline site is the canonical map from the
unit to the pushforward of the unit.**  Over an open of the ambient scheme of the target it is the
restriction map of `𝒪_{X/S}` along the restriction of the morphism, which is the component of the
`f`-map of the restricted structure sheaves. -/
theorem moduleFMapSheaf_unit (g : A ⟶ B) :
    moduleFMapSheaf (SheafOfModules.unit (crystallineStructureSheaf S)) g =
      SheafOfModules.unitToPushforwardObjUnit (ringRestrictionSheafFMap g) := rfl

/-- **The comparison map of the structure sheaf of the big crystalline site is the canonical map
from the pullback of the unit to the unit.**  Both are the transpose, along the adjunction between
pullback and pushforward of sheaves of modules, of the canonical map from the unit to the
pushforward of the unit. -/
theorem moduleComparisonSheaf_unit (g : A ⟶ B) :
    moduleComparisonSheaf (SheafOfModules.unit (crystallineStructureSheaf S)) g =
      SheafOfModules.pullbackObjUnitToUnit (ringRestrictionSheafFMap g) := rfl

/-- **The comparison map of the structure sheaf of the big crystalline site is an isomorphism.**
The pullback of the unit module of a sheaf of rings along a continuous functor of sites is the
unit module as soon as that functor is final, and the preimage functor on the opens of the ambient
schemes is final because the opens of a space form a poset with a greatest element. -/
theorem isIso_moduleComparisonSheaf_unit (g : A ⟶ B) :
    IsIso (moduleComparisonSheaf (SheafOfModules.unit (crystallineStructureSheaf S)) g) := by
  have hfinal : (Opens.map g.targetHom.hom.base).Final := Stacks.Topology.final_opensMap _
  exact inferInstanceAs
    (IsIso (SheafOfModules.pullbackObjUnitToUnit (ringRestrictionSheafFMap g)))

end Thickening

/-- **The structure sheaf `𝒪_{X/S}` of the big crystalline site is a crystal in
`𝒪_{X/S}`-modules.**  For every morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `CRIS(X/S)` the
comparison map `c_f : f^* 𝒪_{T'} ⟶ 𝒪_T` of sheaves of modules is an isomorphism.

This is the base case of the direction "quasi-coherent implies a crystal" of [Stacks, Tag 07IT]:
the source's argument pulls a presentation of a module by copies of `𝒪_{X/S}` back along `f^*`,
which identifies the comparison map of the module from the comparison maps of the copies of the
structure sheaf.  That implication itself is not proved; see the module documentation. -/
theorem isSheafCrystal_unit (S : GlobalCrystallineSituation.{u}) :
    IsSheafCrystal (SheafOfModules.unit (crystallineStructureSheaf S)) :=
  fun _ _ k ↦ Thickening.isIso_moduleComparisonSheaf_unit k

end Crystalline.GlobalCrystallineSituation

end
