module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ModulePullbackSquareCubeSideRelativeSquare
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeSquareBasePullbackIdealIsoHom
public import StacksFrontier.Deformation.ToposThickening.Helpers.IdealSquareCompatibleOfCube

/-!
# `f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥` in the spelling of the cube lemma

The identification `AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`
of the pulled-back ideal of a relative square of `Coh_{X/B}` is the composite of four isomorphisms
(`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso_eq_trans`), the last
of which is the comparison `AlgebraicGeometry.Space.modulePullbackSquare` of Stacks 03LU at the
ideal of the test scheme, in the categories of `Modules`. The cube lemma
`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq` asks for its map as
`B.hom ≫ P(eqToHom Z) ≫ P(ρ.hom) ≫ σ.hom.app N`, with `σ` read in the categories of the
adjunctions `AlgebraicGeometry.Space.spaceModuleAdj`, its maps and spaces given explicitly, and `N`
the ideal of the affine thickening. This file proves that form
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareBasePullbackIdealIso_hom_eq_cubeSide`)
for every morphism `h : T ⟶ T'` of first order thickenings, from a statement over plain categories
(`CategoryTheory.Iso.hom_eq_of_eq_trans_mapIso`) whose categories and functors are fixed by the
adjunctions and the equations `L = P` of the cube lemma, instantiated once: its hypothesis
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareBasePullbackIdealIso_eq_trans_cubeSide`)
holds by definition. Its type is then the side hypothesis `hR` of the instance of the cube lemma
at the relative squares, which is matched without comparing spellings. The more general
`CategoryTheory.Iso.hom_eq_comp_map_comp_map_comp_app_of_eq_trans` and the identification of the two
readings of `σ` at fvar spaces (`AlgebraicGeometry.Space.heq_modulePullbackSquare_app`) are kept for
other spellings of the pieces.

This is used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA). This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace CategoryTheory

/-- **The map of a composite `a ≪≫ P(e) ≪≫ P(ρ') ≪≫ s` read through identifications of its
pieces**: if `R' = a ≪≫ P(e) ≪≫ P(ρ') ≪≫ s` and the functor, the objects, `R'`, `a`,
`e = eqToIso Z`, `ρ'` and `s = σ.app N` are identified with the corresponding pieces, then
`R.hom = B.hom ≫ P(eqToHom Z) ≫ P(ρ.hom) ≫ σ.hom.app N`. The equations `L = P` only fix the
functors `P` from the terms proving them. The equation `H` comes first, so that its
pieces are determined by the term proving it; each identification is a separate hypothesis. -/
theorem Iso.hom_eq_comp_map_comp_map_comp_app_of_eq_trans {𝒯₁ 𝒳 𝒯 𝒱 : Type*} [Category* 𝒯₁]
    [Category* 𝒳] [Category* 𝒯] [Category* 𝒱] {Lf Pf : 𝒯₁ ⥤ 𝒳} {Li Pi : 𝒳 ⥤ 𝒱} {Lt Pt : 𝒯₁ ⥤ 𝒯}
    {Lp Pp : 𝒯 ⥤ 𝒱} (_hf : Lf = Pf) (_hi : Li = Pi) (_ht : Lt = Pt) (_hp : Lp = Pp)
    {σ : Pf ⋙ Pi ≅ Pt ⋙ Pp} {N : 𝒯₁} {F F' : 𝒳} (Zq : F = F') {ρ : F' ≅ Pf.obj N}
    {Q : 𝒱}
    {B : Q ≅ Pi.obj F} {R : Q ≅ Pp.obj (Pt.obj N)}
    {P : 𝒳 ⥤ 𝒱} {Q' : 𝒱} {X Y Z : 𝒳} {W : 𝒱} {R' : Q' ≅ W} {a : Q' ≅ P.obj X} {e : X ≅ Y}
    {ρ' : Y ≅ Z} {s : P.obj Z ≅ W}
    (H : R' = a ≪≫ P.mapIso e ≪≫ P.mapIso ρ' ≪≫ s)
    (eP : P = Pi) (eQ : Q' = Q) (eX : X = F) (eY : Y = F') (eZ : Z = Pf.obj N)
    (eW : W = Pp.obj (Pt.obj N)) (eR : HEq R' R) (ea : HEq a B) (ee : HEq e (eqToIso Zq))
    (eρ : HEq ρ' ρ) (es : HEq s (σ.app N)) :
    R.hom = B.hom ≫ Pi.map (eqToHom Zq) ≫ Pi.map ρ.hom ≫ σ.hom.app N := by
  subst eP eQ eX eY eZ eW
  obtain rfl := eq_of_heq eR
  obtain rfl := eq_of_heq ea
  obtain rfl := eq_of_heq ee
  obtain rfl := eq_of_heq eρ
  obtain rfl := eq_of_heq es
  subst H
  rfl

/-- **The map of an isomorphism equal to a composite `B ≪≫ P(eqToIso Z) ≪≫ P(ρ) ≪≫ σ.app N`**,
with the categories and the functors `P` fixed by adjunctions `L ⊣ R` and equations `L = P`, as
in `Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`: if
`R = B ≪≫ P(eqToIso Z) ≪≫ P(ρ) ≪≫ σ.app N`, then
`R.hom = B.hom ≫ P(eqToHom Z) ≫ P(ρ.hom) ≫ σ.hom.app N`.
The adjunctions only fix the categories, so that an instance of this lemma has the types of the
side hypotheses of the cube lemma. -/
theorem Iso.hom_eq_of_eq_trans_mapIso {𝒯₁ 𝒳 𝒯 𝒱 : Type*} [Category* 𝒯₁] [Category* 𝒳]
    [Category* 𝒯] [Category* 𝒱] {Lf : 𝒯₁ ⥤ 𝒳} {Rf : 𝒳 ⥤ 𝒯₁} (_af : Lf ⊣ Rf)
    {Li : 𝒳 ⥤ 𝒱} {Ri : 𝒱 ⥤ 𝒳} (_ai : Li ⊣ Ri) {Lt : 𝒯₁ ⥤ 𝒯} {Rt : 𝒯 ⥤ 𝒯₁} (_at : Lt ⊣ Rt)
    {Lp : 𝒯 ⥤ 𝒱} {Rp : 𝒱 ⥤ 𝒯} (_ap : Lp ⊣ Rp)
    {Pf : 𝒯₁ ⥤ 𝒳} {Pi : 𝒳 ⥤ 𝒱} {Pt : 𝒯₁ ⥤ 𝒯} {Pp : 𝒯 ⥤ 𝒱}
    (_hf : Lf = Pf) (_hi : Li = Pi) (_ht : Lt = Pt) (_hp : Lp = Pp)
    (σ : Pf ⋙ Pi ≅ Pt ⋙ Pp) (N : 𝒯₁) {F F' : 𝒳} (Z : F = F') (ρ : F' ≅ Pf.obj N) {Q : 𝒱}
    (B : Q ≅ Pi.obj F) (R : Q ≅ Pp.obj (Pt.obj N))
    (eR : R = B ≪≫ Pi.mapIso (eqToIso Z) ≪≫ Pi.mapIso ρ ≪≫ σ.app N) :
    R.hom = B.hom ≫ Pi.map (eqToHom Z) ≫ Pi.map ρ.hom ≫ σ.hom.app N := by
  subst eR
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The two readings of `AlgebraicGeometry.Space.modulePullbackSquare` at an object**: in the
categories of `Modules` (`Iso.app`), and in the categories of the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj` with the pullbacks `P` given by the equations `L = P`, for
a second square whose spaces, maps and object are identified with those of the first by separate
hypotheses. -/
theorem heq_modulePullbackSquare_app {V W X Z X' Z' : AlgebraicSpaces B S hS} {e : V ⟶ W}
    {l : W ⟶ Z} {r : V ⟶ X} {q : X ⟶ Z} {k : V ⟶ Z} {l' : W ⟶ Z'} {r' : V ⟶ X'} {q' : X' ⟶ Z'}
    {k' : V ⟶ Z'} {Pl Pe Pq Pr}
    (hl : (smallEtaleRingedToposHom B S hS l').toModulesHom.pullbackModules = Pl)
    (he : (smallEtaleRingedToposHom B S hS e).toModulesHom.pullbackModules = Pe)
    (hq : (smallEtaleRingedToposHom B S hS q').toModulesHom.pullbackModules = Pq)
    (hr : (smallEtaleRingedToposHom B S hS r').toModulesHom.pullbackModules = Pr)
    (ePl : Pl = (smallEtaleRingedToposHom B S hS l').toRingedToposModulesHom.pullbackModules)
    (ePe : Pe = (smallEtaleRingedToposHom B S hS e).toRingedToposModulesHom.pullbackModules)
    (ePq : Pq = (smallEtaleRingedToposHom B S hS q').toRingedToposModulesHom.pullbackModules)
    (ePr : Pr = (smallEtaleRingedToposHom B S hS r').toRingedToposModulesHom.pullbackModules)
    (hk : e ≫ l = k) (hk' : r ≫ q = k) (hk₂ : e ≫ l' = k') (hk₂' : r' ≫ q' = k')
    (hX : X = X') (hZ : Z = Z') (el : HEq l l') (er : HEq r r') (eq : HEq q q') (ek : HEq k k')
    (N : spaceModules Z) (N' : spaceModules Z') (eN : HEq N N')
    (σ' : Pl ⋙ Pe ≅ Pq ⋙ Pr) (eσ : HEq σ' (modulePullbackSquare B S hS hk₂ hk₂')) :
    HEq ((modulePullbackSquare B S hS hk hk').app N) (σ'.app N') := by
  subst ePl ePe ePq ePr hX hZ
  cases el
  cases er
  cases eq
  cases ek
  cases eN
  obtain rfl := eq_of_heq eσ
  exact HEq.rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

-- Local priority 10000, as in `CoherentStackRelativeIdealSquareReduction`: the searches through
-- `relBaseTop`/`relBaseBottom` and `smallEtaleRingedTopos` are slow otherwise.
attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- **`f̃^*t̃^*𝒥̃ ≅ f_T^*𝒥` as a composite, at the ideal of the affine thickening and in the
categories of the cube lemma**:
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso` for the relative
square of `h : T ⟶ T'` is the composite of
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIsoPullback`, the
identification `AlgebraicGeometry.Space.QuotientSituation.relBaseRight_pullbackIdeal_eq`,
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareRelBasePullbackIdealIso` and the comparison
`AlgebraicGeometry.Space.modulePullbackSquare` at the ideal
`AlgebraicGeometry.Space.affineThickeningIdeal` of `T ⊂ T'`, all read in the categories of the
adjunctions `AlgebraicGeometry.Space.spaceModuleAdj`. Stated as the hypothesis of
`CategoryTheory.Iso.hom_eq_of_eq_trans_mapIso` at these pieces; it holds by definition. -/
theorem relativeSquareBasePullbackIdealIso_eq_trans_cubeSide :
    premise (CategoryTheory.Iso.hom_eq_of_eq_trans_mapIso
      (spaceModuleAdj (X := D.relativeSquareSituation.space T')
        (Y := (schemeSpaceFunctor B S hS).obj T'.left)
        (D.relativeSquareSituation.projection T'))
      (spaceModuleAdj (X := D.relativeSquareSituation.space ξ.T)
        (Y := D.relativeSquareSituation.space T')
        (D.relativeSquareSituation.relativeMap h))
      (spaceModuleAdj (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Y := (schemeSpaceFunctor B S hS).obj T'.left) ((schemeSpaceFunctor B S hS).map h.left))
      (spaceModuleAdj (X := D.relativeSquareSituation.space ξ.T)
        (Y := (schemeSpaceFunctor B S hS).obj ξ.T.left) (D.relativeSquareSituation.projection ξ.T))
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (modulePullbackSquare B S hS (V := D.relativeSquareSituation.space ξ.T)
        (W := D.relativeSquareSituation.space T') (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Z := (schemeSpaceFunctor B S hS).obj T'.left)
        (e := D.relativeSquareSituation.relativeMap h)
        (l := D.relativeSquareSituation.projection T')
        (r := D.relativeSquareSituation.projection ξ.T)
        (q := (schemeSpaceFunctor B S hS).map h.left)
        (k := D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h.left)
        (D.relativeSquareSituation.relativeMap_comp_projection h) rfl)
      (affineThickeningIdeal h.left (isIso_toRange_testSchemeMap h hh)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh)).I
      (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h hh)
      (D.relativeSquareSituation.relativeSquareRelBasePullbackIdealIso h hh)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIsoPullback h hh)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h hh)) :=
  rfl

/-- **The identification `R` of the pulled-back ideal of the relative square of `h : T ⟶ T'`, in the
spelling of the side hypotheses `hR` of the cube lemma**
(`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`, instantiated in
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap_reduction_aux`):
`R.hom = B.hom ≫ P(eqToHom Z) ≫ P(ρ.hom) ≫ σ.hom.app N` for the four isomorphisms of
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareBasePullbackIdealIso_eq_trans_cubeSide`. -/
theorem relativeSquareBasePullbackIdealIso_hom_eq_cubeSide :
    type_of% (CategoryTheory.Iso.hom_eq_of_eq_trans_mapIso
      (spaceModuleAdj (X := D.relativeSquareSituation.space T')
        (Y := (schemeSpaceFunctor B S hS).obj T'.left)
        (D.relativeSquareSituation.projection T'))
      (spaceModuleAdj (X := D.relativeSquareSituation.space ξ.T)
        (Y := D.relativeSquareSituation.space T')
        (D.relativeSquareSituation.relativeMap h))
      (spaceModuleAdj (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Y := (schemeSpaceFunctor B S hS).obj T'.left) ((schemeSpaceFunctor B S hS).map h.left))
      (spaceModuleAdj (X := D.relativeSquareSituation.space ξ.T)
        (Y := (schemeSpaceFunctor B S hS).obj ξ.T.left) (D.relativeSquareSituation.projection ξ.T))
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (modulePullbackSquare B S hS (V := D.relativeSquareSituation.space ξ.T)
        (W := D.relativeSquareSituation.space T') (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Z := (schemeSpaceFunctor B S hS).obj T'.left)
        (e := D.relativeSquareSituation.relativeMap h)
        (l := D.relativeSquareSituation.projection T')
        (r := D.relativeSquareSituation.projection ξ.T)
        (q := (schemeSpaceFunctor B S hS).map h.left)
        (k := D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h.left)
        (D.relativeSquareSituation.relativeMap_comp_projection h) rfl)
      (affineThickeningIdeal h.left (isIso_toRange_testSchemeMap h hh)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh)).I
      (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h hh)
      (D.relativeSquareSituation.relativeSquareRelBasePullbackIdealIso h hh)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIsoPullback h hh)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h hh)
      (relativeSquareBasePullbackIdealIso_eq_trans_cubeSide h hh)) :=
  CategoryTheory.Iso.hom_eq_of_eq_trans_mapIso
      (spaceModuleAdj (X := D.relativeSquareSituation.space T')
        (Y := (schemeSpaceFunctor B S hS).obj T'.left)
        (D.relativeSquareSituation.projection T'))
      (spaceModuleAdj (X := D.relativeSquareSituation.space ξ.T)
        (Y := D.relativeSquareSituation.space T')
        (D.relativeSquareSituation.relativeMap h))
      (spaceModuleAdj (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Y := (schemeSpaceFunctor B S hS).obj T'.left) ((schemeSpaceFunctor B S hS).map h.left))
      (spaceModuleAdj (X := D.relativeSquareSituation.space ξ.T)
        (Y := (schemeSpaceFunctor B S hS).obj ξ.T.left) (D.relativeSquareSituation.projection ξ.T))
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom _)
      (modulePullbackSquare B S hS (V := D.relativeSquareSituation.space ξ.T)
        (W := D.relativeSquareSituation.space T') (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Z := (schemeSpaceFunctor B S hS).obj T'.left)
        (e := D.relativeSquareSituation.relativeMap h)
        (l := D.relativeSquareSituation.projection T')
        (r := D.relativeSquareSituation.projection ξ.T)
        (q := (schemeSpaceFunctor B S hS).map h.left)
        (k := D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h.left)
        (D.relativeSquareSituation.relativeMap_comp_projection h) rfl)
      (affineThickeningIdeal h.left (isIso_toRange_testSchemeMap h hh)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh)).I
      (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h hh)
      (D.relativeSquareSituation.relativeSquareRelBasePullbackIdealIso h hh)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIsoPullback h hh)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h hh)
      (relativeSquareBasePullbackIdealIso_eq_trans_cubeSide h hh)

end AlgebraicGeometry.Space.CoherentSituation
