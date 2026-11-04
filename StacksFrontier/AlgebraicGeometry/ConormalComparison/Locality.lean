module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Restriction

/-!
# Locality of the conormal sheaf, and the restriction behaviour of its quotient generators

For a morphism of schemes `f : Z ⟶ X` and an open `V` of `X`, the restriction to `f ⁻¹ᵁ V` of
the inverse image along `f` of the ideal sheaf of `f` is the inverse image along `f ∣_ V` of the
ideal sheaf of `f ∣_ V`. This file constructs that isomorphism, characterizes it through the
adjunction units, and specializes it to the conormal sheaf of an immersion. It also shows that a
section of the ideal sheaf is determined by its image in the structure sheaf, and that the
generator identity `conormalSheaf i .val.map _ c = conormalQuotientMap i U i' hfac .val.app _ x`
of [Stacks, Tag 01R3] passes from an open to every smaller open.

Nothing here is affine, Noetherian, finite or quasi-compact; the morphism `f` of the first
section is arbitrary.

## Main definitions

* `Stacks.Conormal.Locality.pullbackRestrictIsoOf`: for a morphism `f : Z ⟶ X`, an open
  `V ≤ X`, a module `M` on `X` and an identification `ρ` of its restriction to `V` with a
  module `N` on `V`, the restriction to `f ⁻¹ᵁ V` of `f^* M` is the inverse image along
  `f ∣_ V` of `N`.
* `Stacks.Conormal.Locality.conormalRestrictIso`: the restriction to `f ⁻¹ᵁ V` of
  `f^* I(f)` is `(f ∣_ V)^* I(f ∣_ V)`; this is `pullbackRestrictIsoOf` at the ideal sheaf, with
  `ρ` the comparison `Stacks.Conormal.Restriction.restrictIdealSheafIso'`.
* `Stacks.Conormal.Locality.conormalSheafRestrictIso`: for a closed-immersion factorization
  `i' : Z ⟶ U` of an immersion `i` and an open `V' ≤ U`, the restriction of
  `Stacks.Conormal.conormalSheaf i` to `i' ⁻¹ᵁ V'` is `(i' ∣_ V')^* I(i' ∣_ V')`.

## Main results

* `Stacks.Conormal.Locality.unit_comp_map_pullbackRestrictIsoOf` and
  `Stacks.Conormal.Locality.unit_comp_map_conormalRestrictIso`: the adjoint characterization of
  the two locality isomorphisms. Adjoint transposition is a bijection, so this determines them.
* `Stacks.Conormal.Locality.idealSheaf_section_injective`: the inclusion of the ideal sheaf into
  the structure sheaf is injective on sections, so a section of the ideal sheaf is determined by
  its image in the structure sheaf.
* `Stacks.Conormal.Locality.idealSheaf_section_restrict`: the section of the ideal sheaf named by
  an element of an ambient ideal over a smaller open is the restriction of the one named over a
  larger open.
* `Stacks.Conormal.Locality.conormalQuotientMap_restrict`: `Stacks.Conormal.conormalQuotientMap`
  commutes with restriction.
* `Stacks.Conormal.Locality.generator_of_le`: the generator identity at an open `W'` implies it at
  every smaller open `W ≤ W'`.

## Implementation notes

`Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` compares `f^*` followed by
restriction to `f ⁻¹ᵁ V` with restriction to `V` followed by `(f ∣_ V)^*`, and
`Stacks.Conormal.Restriction.restrictIdealSheafIso'` identifies the restriction to `V` of the
ideal sheaf of `f` with the ideal sheaf of `f ∣_ V`; the composite is the locality isomorphism.

Two spellings of one category are in play, `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules (structureSheafRing X.toSheafedSpace)`; they agree definitionally but not at the
elaborator's implicit transparency. So `pullbackRestrictIsoOf` and
`unit_comp_map_pullbackRestrictIsoOf` are stated for an arbitrary `M : X.Modules`, and the
ideal-sheaf cases are obtained by application, whose argument types are checked at default
transparency.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.IdealSheafRestrict
open Stacks.AlgebraicGeometry.AffinePushforward

universe u

namespace Stacks.Conormal.Locality

/-! ### Locality of the inverse image -/

variable {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)

/-- The restriction to `f ⁻¹ᵁ V` of the inverse image `f^* M`, computed from an
identification `ρ` of the restriction of `M` to `V` with a module `N` on `V`.

This is `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` followed by the
inverse image along `f ∣_ V` of `ρ`. -/
noncomputable def pullbackRestrictIsoOf (M : X.Modules) (N : V.toScheme.Modules)
    (ρ : (Scheme.Modules.restrictFunctor V.ι).obj M ≅ N) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj ((Scheme.Modules.pullback f).obj M) ≅
      (Scheme.Modules.pullback (f ∣_ V)).obj N :=
  (pullbackRestrictIso f V).app M ≪≫ (Scheme.Modules.pullback (f ∣_ V)).mapIso ρ

/-- **The adjoint characterization of `pullbackRestrictIsoOf`.** Both locality comparisons go
to the same place after transposition: the unit of the adjunction for
`pullback f ⋙ restrictFunctor (f ⁻¹ᵁ V).ι`, followed by the direct image of the comparison, is
the unit of the adjunction for `restrictFunctor V.ι ⋙ pullback (f ∣_ V)` followed by the
direct image of the inverse image of `ρ`.

Adjoint transposition is a bijection, so this determines `pullbackRestrictIsoOf`, and a formula
on generators can be pushed through it. The first factor is
`Stacks.Conormal.Restriction.unit_comp_map_pullbackRestrictIso_hom_app`; the second is carried
along by functoriality of the direct image. -/
theorem unit_comp_map_pullbackRestrictIsoOf (M : X.Modules) (N : V.toScheme.Modules)
    (ρ : (Scheme.Modules.restrictFunctor V.ι).obj M ≅ N) :
    (pullbackRestrictAdjunction f V).unit.app M ≫
        (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map
          (pullbackRestrictIsoOf f V M N ρ).hom =
      ((restrictPullbackAdjunction f V).ofNatIsoRight
          (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V))).unit.app M ≫
        (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map
          ((Scheme.Modules.pullback (f ∣_ V)).map ρ.hom) := by
  simp only [pullbackRestrictIsoOf, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    ← Category.assoc, Iso.app_hom]
  exact congrArg (fun t => t ≫ (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map
    ((Scheme.Modules.pullback (f ∣_ V)).map ρ.hom))
    (Restriction.unit_comp_map_pullbackRestrictIso_hom_app f V M)

/-- **Locality of the conormal sheaf of a morphism.** The restriction to `f ⁻¹ᵁ V` of the
inverse image along `f` of the ideal sheaf of `f` is the inverse image along `f ∣_ V` of the
ideal sheaf of `f ∣_ V`.

This is `pullbackRestrictIsoOf` with `ρ` the comparison
`Stacks.Conormal.Restriction.restrictIdealSheafIso'`. -/
noncomputable def conormalRestrictIso :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj
        ((Scheme.Modules.pullback f).obj
          (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)) ≅
      (Scheme.Modules.pullback (f ∣_ V)).obj
        (Stacks.ClosedImmersion.idealSheaf (f ∣_ V).toLRSHom.toShHom) :=
  pullbackRestrictIsoOf f V (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom)
    (Stacks.ClosedImmersion.idealSheaf (f ∣_ V).toLRSHom.toShHom)
    (Restriction.restrictIdealSheafIso' f V)

/-- `unit_comp_map_pullbackRestrictIsoOf` at the ideal sheaf: the adjoint characterization of
`conormalRestrictIso`. -/
theorem unit_comp_map_conormalRestrictIso :
    (pullbackRestrictAdjunction f V).unit.app
          (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom) ≫
        (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map (conormalRestrictIso f V).hom =
      ((restrictPullbackAdjunction f V).ofNatIsoRight
          (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V))).unit.app
            (Stacks.ClosedImmersion.idealSheaf f.toLRSHom.toShHom) ≫
        (Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f)).map
          ((Scheme.Modules.pullback (f ∣_ V)).map (Restriction.restrictIdealSheafIso' f V).hom) :=
  unit_comp_map_pullbackRestrictIsoOf f V _ _ _

/-! ### Sections of the ideal sheaf -/

/-- **A section of the ideal sheaf is determined by its image in the structure sheaf.** The
inclusion of the ideal sheaf is `CategoryTheory.Limits.kernel.ι`, hence a monomorphism, hence
injective on sections over every open. -/
theorem idealSheaf_section_injective {U : Scheme.{u}} (k : Z ⟶ U) (W : U.Opens) :
    Function.Injective
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom k.toLRSHom.toShHom))).val.app (.op W)).hom := by
  have : Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom k.toLRSHom.toShHom))).val := (SheafOfModules.forget _).map_mono _
  exact PresheafOfModules.injective_of_mono _ (.op W)

/-! ### Locality of the conormal sheaf of an immersion -/

/-- **Locality of the conormal sheaf of an immersion.** For a factorization of an immersion
`i : Z ⟶ X` as a closed immersion `i' : Z ⟶ U` followed by the inclusion of the open `U`, and
an open `V' ≤ U`, the restriction of `Stacks.Conormal.conormalSheaf i` to `i' ⁻¹ᵁ V'` is the
inverse image along `i' ∣_ V'` of the ideal sheaf of `i' ∣_ V'`.

`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf` replaces the conormal sheaf by the
inverse image of the ideal sheaf of the given factorization, and `conormalRestrictIso`
restricts. -/
noncomputable def conormalSheafRestrictIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V' : U.toScheme.Opens) :
    (Scheme.Modules.restrictFunctor (i' ⁻¹ᵁ V').ι).obj (Stacks.Conormal.conormalSheaf i) ≅
      (Scheme.Modules.pullback (i' ∣_ V')).obj
        (Stacks.ClosedImmersion.idealSheaf (i' ∣_ V').toLRSHom.toShHom) :=
  (Scheme.Modules.restrictFunctor (i' ⁻¹ᵁ V').ι).mapIso
      (Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf i U i' hfac) ≪≫
    conormalRestrictIso i' V'

/-! ### Restriction of the quotient generators -/

/-- The restriction maps of a module pushforward are the restriction maps of the source
module, on the nose. -/
theorem modulePushforward_val_map {Z X : Scheme.{u}} (k : Z ⟶ X)
    (M : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace))
    {W W' : X.Opens} (h : W ≤ W')
    (y : ((modulePushforward k.toLRSHom.toShHom).obj M).val.obj (.op W')) :
    ((modulePushforward k.toLRSHom.toShHom).obj M).val.map (homOfLE h).op y =
      M.val.map (homOfLE (k.preimage_mono h)).op y :=
  rfl

/-- **`Stacks.Conormal.conormalQuotientMap` commutes with restriction.** This is naturality of
a morphism of sheaves of modules, read through `modulePushforward_val_map`. -/
theorem conormalQuotientMap_restrict {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    {W W' : U.toScheme.Opens} (hWW' : W ≤ W')
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op W')) :
    (Stacks.Conormal.conormalSheaf i).val.map (homOfLE (i'.preimage_mono hWW')).op
        ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op W') x) =
      (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op W)
        ((Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
          (homOfLE hWW').op x) :=
  (modulePushforward_val_map i' (Stacks.Conormal.conormalSheaf i) hWW' _).symm.trans
    (PresheafOfModules.naturality_apply
      (Stacks.Conormal.conormalQuotientMap i U i' hfac).val (homOfLE hWW').op x).symm

/-- The structure sheaf as a module over itself restricts like the structure sheaf. -/
theorem unitModule_val_map {U : Scheme.{u}} {W W' : U.Opens} (h : W ≤ W')
    (y : (SheafOfModules.unit (structureSheafRing U.toLocallyRingedSpace.toRingedSpace)).val.obj
      (.op W')) :
    (SheafOfModules.unit (structureSheafRing U.toLocallyRingedSpace.toRingedSpace)).val.map
        (homOfLE h).op y =
      (U.presheaf.map (homOfLE h).op).hom y :=
  rfl

/-- **The section of the ideal sheaf named by an ambient section restricts.** If `x'` over
`W'` and `x` over `W ≤ W'` both have as image in the structure sheaf the restriction of the
same `r : Γ(X, V)`, then `x` is the restriction of `x'`.

Both are sections of the ideal sheaf over `W` whose images in the structure sheaf agree, by
`AlgebraicGeometry.Scheme.Hom.appLE_map`, so `idealSheaf_section_injective` identifies
them. -/
theorem idealSheaf_section_restrict {Z : Scheme.{u}} {X : Scheme.{u}}
    (U : X.Opens) (i' : Z ⟶ U.toScheme) (V : X.Opens) (r : Γ(X, V))
    {W W' : U.toScheme.Opens} (hWW' : W ≤ W') (hW' : W' ≤ U.ι ⁻¹ᵁ V)
    (x' : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op W'))
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op W))
    (hx' : (U.ι.appLE V W' hW').hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op W') x')
    (hx : (U.ι.appLE V W (hWW'.trans hW')).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op W) x) :
    x = (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
      (homOfLE hWW').op x' := by
  refine idealSheaf_section_injective i' W ?_
  refine hx.symm.trans ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i'.toLRSHom.toShHom))).val (homOfLE hWW').op x').symm
  refine Eq.trans ?_ (unitModule_val_map hWW' _).symm
  refine Eq.trans ?_ (congrArg (U.toScheme.presheaf.map (homOfLE hWW').op).hom hx')
  rw [← U.ι.appLE_map hW' (homOfLE hWW').op]
  rfl

/-- **The generator identity of [Stacks, Tag 01R3] passes to smaller opens.** The identity

`conormalSheaf i .val.map (homOfLE _).op c = conormalQuotientMap i U i' hfac .val.app W x`

at an open `W'` of a closed-immersion factorization implies it at every smaller open
`W ≤ W'`, for the section of the ideal sheaf named there by the same ambient `r`. The sections
are matched by `idealSheaf_section_restrict` and the two sides transported by
`conormalQuotientMap_restrict` and functoriality of the conormal sheaf. -/
theorem generator_of_le {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : X.Opens) (r : Γ(X, V))
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    {W W' : U.toScheme.Opens} (hWW' : W ≤ W') (hW' : W' ≤ U.ι ⁻¹ᵁ V)
    (le1 : i' ⁻¹ᵁ W' ≤ i ⁻¹ᵁ V) (le2 : i' ⁻¹ᵁ W ≤ i ⁻¹ᵁ V)
    (c : (Stacks.Conormal.conormalSheaf i).val.obj (.op (i ⁻¹ᵁ V)))
    (x' : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op W'))
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (.op W))
    (hx' : (U.ι.appLE V W' hW').hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op W') x')
    (hx : (U.ι.appLE V W (hWW'.trans hW')).hom r =
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (.op W) x)
    (h : (Stacks.Conormal.conormalSheaf i).val.map (homOfLE le1).op c =
      (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op W') x') :
    (Stacks.Conormal.conormalSheaf i).val.map (homOfLE le2).op c =
      (Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op W) x := by
  have hxx : x = (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.map
      (homOfLE hWW').op x' :=
    idealSheaf_section_restrict U i' V r hWW' hW' x' x hx' hx
  refine Eq.trans (show (Stacks.Conormal.conormalSheaf i).val.map (homOfLE le2).op c =
      (Stacks.Conormal.conormalSheaf i).val.map (homOfLE (i'.preimage_mono hWW')).op
        ((Stacks.Conormal.conormalSheaf i).val.map (homOfLE le1).op c) from
    (Stacks.Conormal.conormalSheaf i).val.map_comp_apply
      (homOfLE le1).op (homOfLE (i'.preimage_mono hWW')).op c) ?_
  refine Eq.trans (congrArg
    ((Stacks.Conormal.conormalSheaf i).val.map (homOfLE (i'.preimage_mono hWW')).op) h) ?_
  refine Eq.trans (conormalQuotientMap_restrict i U i' hfac hWW' x') ?_
  exact congrArg ((Stacks.Conormal.conormalQuotientMap i U i' hfac).val.app (.op W)) hxx.symm

end Stacks.Conormal.Locality

end
