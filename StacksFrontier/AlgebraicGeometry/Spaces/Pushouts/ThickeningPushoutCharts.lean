module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatFibreSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeChartSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Algebraic spaces over a pushout of schemes along a thickening, chart by chart

Let `Y' = Y ⨿_Z Z'` be a pushout of schemes along a thickening `Z ⟶ Z'` and an affine
morphism `Z ⟶ Y` (Stacks 07RT), and let `P ⟶ Y'` be an algebraic space with base changes
`V = P ×_{Y'} Y`, `U' = P ×_{Y'} Z'` and `U = V ×_Y Z`.  Over every diagram of étale charts
`W ⟶ T` of `P ⟶ Y'` this file builds the eight charts `T_Y, T_{Z'}, T_Z, W_Y, W_{Z'}, W_Z`
obtained by base change, and shows that, when `W` and `T` are affine, their rings form a relative
Milnor square in the sense of `MilnorPatching.IsRelativeSquare` (the situation of Stacks 08KK):
`Γ(T)` is the fibre product `Γ(T_Y) ×_{Γ(T_Z)} Γ(T_{Z'})` because `T` is flat over `Y'`, and the
rings of the charts of `V`, `U'`, `U` are the base changes of `Γ(W)`.

## Main definitions

* `AlgebraicGeometry.Space.ThickeningPushoutSpaces`: the situation, as a proposition about the
  morphisms of schemes and of algebraic spaces involved.

## Main results

* `AlgebraicGeometry.Space.ThickeningPushoutSpaces.isRelativeSquare`.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 08KK](https://stacks.math.columbia.edu/tag/08KK)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The pullback square of a representable morphism along the Yoneda image of a morphism. -/
private theorem isPullback_snd_fst'_of_map_eq {X Y Z : BigFppfOver B S hS} {f : X ⟶ Z}
    (hf : yoneda.relativelyRepresentable (yoneda.map f)) {g : Y ⟶ Z}
    {g' : yoneda.obj Y ⟶ yoneda.obj Z} (hg : yoneda.map g = g') :
    IsPullback (hf.snd g') (hf.fst' g') g f := by
  subst hg
  exact (hf.isPullback_of_map g).flip

/-- If `d ≫ b = c ≫ a`, the composite of the two pullback projections over `z` factors through
the two pullback projections of `c` and `a`. -/
private theorem fst_comp_comp_eq_of_comm {G H K L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {c : G ⟶ H} {a : H ⟶ K} {d : G ⟶ L} {b : L ⟶ K} (hw : d ≫ b = c ≫ a)
    (hc : yoneda.relativelyRepresentable c) (ha : yoneda.relativelyRepresentable a)
    {T : BigFppfOver B S hS} (z : yoneda.obj T ⟶ K) :
    (hc.fst (ha.fst z) ≫ d) ≫ b = yoneda.map (hc.snd (ha.fst z) ≫ ha.snd z) ≫ z := by
  rw [Category.assoc, hw, ← Category.assoc, hc.w, Category.assoc, ha.w, ← Category.assoc,
    ← yoneda.map_comp]

/-- An affine morphism of the site is an affine morphism of the represented algebraic spaces. -/
theorem isAffineHom_yoneda_map_of_isAffineHom {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (hφ : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map φ)) :
    IsAffineHom B S hS (yoneda.map φ) :=
  isAffineHom_of_presheaf ((presheaf_yoneda_map_iff B S hS
    (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance φ).2 hφ)

/-- **An algebraic space over a pushout of schemes along a thickening, with its three base
changes.**  A cocartesian square `Y' = Y ⨿_Z Z'` of schemes of the big fppf site along a
thickening `i : Z ⟶ Z'` and an affine morphism `f : Z ⟶ Y` ([Stacks Project, Tag 07RT]), an
algebraic space `P` over `Y'`, and algebraic spaces `V = P ×_{Y'} Y`, `U' = P ×_{Y'} Z'` and
`U = V ×_Y Z` presented by cartesian squares, with the two maps `U ⟶ P` agreeing.  This is the
situation of [Stacks Project, Tag 08KV] for a pushout of schemes. -/
structure ThickeningPushoutSpaces {Z Z' Y Y' : BigFppfOver B S hS} (i : Z ⟶ Z') (f : Z ⟶ Y)
    (g : Z' ⟶ Y') (h : Y ⟶ Y') {P V U' U : AlgebraicSpaces B S hS}
    (p : P ⟶ (schemeSpaceFunctor B S hS).obj Y') (pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y)
    (pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z') (pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z)
    (a : V ⟶ P) (b : U' ⟶ P) (c : U ⟶ V) (d : U ⟶ U') : Prop where
  isPushout : IsPushout ((BigFppfOver.toScheme B S hS).map i)
    ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map g)
    ((BigFppfOver.toScheme B S hS).map h)
  isThickening : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i)
  isAffineHom : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f)
  isPullback_a : IsPullback a pV p ((schemeSpaceFunctor B S hS).map h)
  isPullback_b : IsPullback b pU' p ((schemeSpaceFunctor B S hS).map g)
  isPullback_c : IsPullback c pU pV ((schemeSpaceFunctor B S hS).map f)
  comm_d : d ≫ pU' = pU ≫ (schemeSpaceFunctor B S hS).map i
  comm : c ≫ a = d ≫ b

namespace ThickeningPushoutSpaces

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
include E

/-- The commutative square of the pushout, in the site. -/
theorem w : f ≫ h = i ≫ g :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact E.isPushout.w.symm)

/-- `Y ⟶ Y'` is a thickening, by the second assertion of [Stacks Project, Tag 07RT]. -/
theorem isThickening_h :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map h) := by
  let := E.isPushout.hasPushout
  have := E.isAffineHom
  have h0 := Stacks.Pushout.pushout_inr_isThickening' ((BigFppfOver.toScheme B S hS).map i)
    ((BigFppfOver.toScheme B S hS).map f) E.isThickening
  rw [← E.isPushout.inr_isoPushout_inv]
  exact ⟨by have := h0.1; infer_instance, by
    have : Surjective (pushout.inr ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map f)) := ⟨h0.2⟩
    exact (inferInstance : Surjective (pushout.inr _ _ ≫ E.isPushout.isoPushout.inv)).1⟩

/-- `Y ⟶ Y'` is affine. -/
theorem isAffineHom_h :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map h) :=
  have := E.isThickening_h.1
  inferInstance

/-- `Z' ⟶ Y'` is affine: `Z ⟶ Z'` being a thickening, this follows from `Z ⟶ Y` being affine. -/
theorem isAffineHom_g :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g) := by
  let := E.isPushout.hasPushout
  have := E.isAffineHom
  have := Stacks.Pushout.isAffineHom_pushout_inl_of_isThickening
    ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map f) E.isThickening
  rw [← E.isPushout.inl_isoPushout_inv]
  infer_instance

/-- `Z ⟶ Y` is affine. -/
theorem isAffineHom_f :
    _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f) :=
  E.isAffineHom

/-! ### Affineness and representability of the morphisms of the situation -/

/-- The morphism of algebraic spaces `Y ⟶ Y'` is affine. -/
theorem isAffineHom_sp_h : IsAffineHom B S hS ((schemeSpaceFunctor B S hS).map h).hom :=
  isAffineHom_yoneda_map_of_isAffineHom h E.isAffineHom_h

/-- The morphism of algebraic spaces `Z' ⟶ Y'` is affine. -/
theorem isAffineHom_sp_g : IsAffineHom B S hS ((schemeSpaceFunctor B S hS).map g).hom :=
  isAffineHom_yoneda_map_of_isAffineHom g E.isAffineHom_g

/-- The morphism of algebraic spaces `Z ⟶ Y` is affine. -/
theorem isAffineHom_sp_f : IsAffineHom B S hS ((schemeSpaceFunctor B S hS).map f).hom :=
  isAffineHom_yoneda_map_of_isAffineHom f E.isAffineHom_f

/-- `V ⟶ P` is affine. -/
theorem isAffineHom_a : IsAffineHom B S hS a.hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS E.isPullback_a.flip)
    E.isAffineHom_sp_h

/-- `U' ⟶ P` is affine. -/
theorem isAffineHom_b : IsAffineHom B S hS b.hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS E.isPullback_b.flip)
    E.isAffineHom_sp_g

/-- `U ⟶ V` is affine. -/
theorem isAffineHom_c : IsAffineHom B S hS c.hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS E.isPullback_c.flip)
    E.isAffineHom_sp_f

omit E in
/-- The morphism of sheaves underlying `Y ⟶ Y'` is relatively representable. -/
theorem rep_h : yoneda.relativelyRepresentable ((schemeSpaceFunctor B S hS).map h).hom :=
  relativelyRepresentable_yoneda_map B S hS h

omit E in
/-- The morphism of sheaves underlying `Z' ⟶ Y'` is relatively representable. -/
theorem rep_g : yoneda.relativelyRepresentable ((schemeSpaceFunctor B S hS).map g).hom :=
  relativelyRepresentable_yoneda_map B S hS g

omit E in
/-- The morphism of sheaves underlying `Z ⟶ Y` is relatively representable. -/
theorem rep_f : yoneda.relativelyRepresentable ((schemeSpaceFunctor B S hS).map f).hom :=
  relativelyRepresentable_yoneda_map B S hS f

/-- The morphism of sheaves underlying `V ⟶ P` is relatively representable. -/
theorem rep_a : yoneda.relativelyRepresentable a.hom :=
  relativelyRepresentable_of_isAffineHom B S hS a E.isAffineHom_a

/-- The morphism of sheaves underlying `U' ⟶ P` is relatively representable. -/
theorem rep_b : yoneda.relativelyRepresentable b.hom :=
  relativelyRepresentable_of_isAffineHom B S hS b E.isAffineHom_b

/-- The morphism of sheaves underlying `U ⟶ V` is relatively representable. -/
theorem rep_c : yoneda.relativelyRepresentable c.hom :=
  relativelyRepresentable_of_isAffineHom B S hS c E.isAffineHom_c

/-! ### The charts above a chart diagram of `P` over `Y'` -/

variable (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom)

/-- The chart `T ×_{Y'} Y` of `Y`. -/
abbrev TY : SmallEtale B S hS ((schemeSpaceFunctor B S hS).obj Y).1 :=
  (smallBaseChange B S hS _
    (relativelyRepresentable_of_isAffineHom B S hS _ E.isAffineHom_sp_h)).obj dT.V

/-- The chart `T ×_{Y'} Z'` of `Z'`. -/
abbrev TZ' : SmallEtale B S hS ((schemeSpaceFunctor B S hS).obj Z').1 :=
  (smallBaseChange B S hS _
    (relativelyRepresentable_of_isAffineHom B S hS _ E.isAffineHom_sp_g)).obj dT.V

/-- The chart `T_Y ×_Y Z` of `Z`. -/
abbrev TZ : SmallEtale B S hS ((schemeSpaceFunctor B S hS).obj Z).1 :=
  (smallBaseChange B S hS _ (rep_f (f := f))).obj (E.TY dT)

/-- The chart `W ×_P V` of `V`. -/
abbrev WY : SmallEtale B S hS V.1 := (smallBaseChange B S hS a E.rep_a).obj dT.U

/-- The chart `W ×_P U'` of `U'`. -/
abbrev WZ' : SmallEtale B S hS U'.1 := (smallBaseChange B S hS b E.rep_b).obj dT.U

/-- The chart `W_Y ×_V U` of `U`. -/
abbrev WZ : SmallEtale B S hS U.1 := (smallBaseChange B S hS c E.rep_c).obj (E.WY dT)

/-- `T_Y ⟶ T`. -/
abbrev dTY := smallBaseChangeDiagram ((schemeSpaceFunctor B S hS).map h)
  (relativelyRepresentable_of_isAffineHom B S hS _ E.isAffineHom_sp_h) dT.V

/-- `T_{Z'} ⟶ T`. -/
abbrev dTZ' := smallBaseChangeDiagram ((schemeSpaceFunctor B S hS).map g)
  (relativelyRepresentable_of_isAffineHom B S hS _ E.isAffineHom_sp_g) dT.V

/-- `T_Z ⟶ T_Y`. -/
abbrev dTZ :=
  smallBaseChangeDiagram ((schemeSpaceFunctor B S hS).map f) (rep_f (f := f)) (E.TY dT)

/-- `W_Y ⟶ W`. -/
abbrev dWY := smallBaseChangeDiagram a E.rep_a dT.U

/-- `W_{Z'} ⟶ W`. -/
abbrev dWZ' := smallBaseChangeDiagram b E.rep_b dT.U

/-- `W_Z ⟶ W_Y`. -/
abbrev dWZ := smallBaseChangeDiagram c E.rep_c (E.WY dT)

/-- `W_Y ⟶ T_Y`, over `V ⟶ Y`. -/
abbrev dWYT := chartDiagramOfSquare B S hS pV a ((schemeSpaceFunctor B S hS).map h) p
  (rep_h (h := h)) E.rep_a dT E.isPullback_a.w.symm

/-- `W_{Z'} ⟶ T_{Z'}`, over `U' ⟶ Z'`. -/
abbrev dWZ'T := chartDiagramOfSquare B S hS pU' b ((schemeSpaceFunctor B S hS).map g) p
  (rep_g (g := g)) E.rep_b dT E.isPullback_b.w.symm

/-- `W_Z ⟶ T_Z`, over `U ⟶ Z`. -/
abbrev dWZT := chartDiagramOfSquare B S hS pU c ((schemeSpaceFunctor B S hS).map f) pV
  (rep_f (f := f)) E.rep_c (E.dWYT dT) E.isPullback_c.w.symm

/-- The composites `T_Z ⟶ Z ⟶ Z' ⟶ Y'` and `T_Z ⟶ T_Y ⟶ T ⟶ Y'` agree. -/
theorem TZ_cond :
    ((E.TZ dT).1.hom ≫ ((schemeSpaceFunctor B S hS).map i).hom) ≫
        ((schemeSpaceFunctor B S hS).map g).hom =
      yoneda.map ((rep_f (f := f)).snd (E.TY dT).1.hom ≫ (rep_h (h := h)).snd dT.V.1.hom) ≫
        dT.V.1.hom := by
  have hw : ((schemeSpaceFunctor B S hS).map i).hom ≫ ((schemeSpaceFunctor B S hS).map g).hom =
      ((schemeSpaceFunctor B S hS).map f).hom ≫ ((schemeSpaceFunctor B S hS).map h).hom := by
    change yoneda.map i ≫ yoneda.map g = yoneda.map f ≫ yoneda.map h
    rw [← yoneda.map_comp, ← yoneda.map_comp, E.w]
  exact fst_comp_comp_eq_of_comm hw (rep_f (f := f)) (rep_h (h := h)) dT.V.1.hom

/-- The morphism `T_Z ⟶ T_{Z'}` over `Z ⟶ Z'`. -/
def mapTZ :
    (SmallEtale.toOver B S hS _).obj (E.TZ dT) ⟶ (SmallEtale.toOver B S hS _).obj (E.TZ' dT) :=
  (rep_g (g := g)).lift _ _ (E.TZ_cond dT)

/-- `T_Z ⟶ T_{Z'}`, over `Z ⟶ Z'`. -/
abbrev dTZZ' : ChartDiagram B S hS ((schemeSpaceFunctor B S hS).obj Z).1
    ((schemeSpaceFunctor B S hS).obj Z').1 ((schemeSpaceFunctor B S hS).map i).hom where
  U := E.TZ dT
  V := E.TZ' dT
  g := E.mapTZ dT
  comm := ((rep_g (g := g)).lift_fst _ _ (E.TZ_cond dT)).symm

/-- The composites `W_Z ⟶ U ⟶ U' ⟶ P` and `W_Z ⟶ W_Y ⟶ W ⟶ P` agree. -/
theorem WZ_cond :
    ((E.WZ dT).1.hom ≫ d.hom) ≫ b.hom =
      yoneda.map (E.rep_c.snd (E.WY dT).1.hom ≫ E.rep_a.snd dT.U.1.hom) ≫ dT.U.1.hom := by
  have hw : d.hom ≫ b.hom = c.hom ≫ a.hom := congrArg (fun k => k.hom) E.comm.symm
  exact fst_comp_comp_eq_of_comm hw E.rep_c E.rep_a dT.U.1.hom

/-- The morphism `W_Z ⟶ W_{Z'}` over `U ⟶ U'`. -/
def mapWZ :
    (SmallEtale.toOver B S hS _).obj (E.WZ dT) ⟶ (SmallEtale.toOver B S hS _).obj (E.WZ' dT) :=
  E.rep_b.lift _ _ (E.WZ_cond dT)

/-- `W_Z ⟶ W_{Z'}`, over `U ⟶ U'`. -/
abbrev dWZZ' : ChartDiagram B S hS U.1 U'.1 d.hom where
  U := E.WZ dT
  V := E.WZ' dT
  g := E.mapWZ dT
  comm := (E.rep_b.lift_fst _ _ (E.WZ_cond dT)).symm

/-! ### The four charts of the base, as a square of schemes -/

/-- The morphism of the site underlying the structure morphism of the chart `T` of `Y'`. -/
abbrev tT : dT.V.1.left ⟶ Y' := yoneda.preimage dT.V.1.hom

omit E in
/-- The image of `tT dT` under the Yoneda embedding is the structure morphism of `T`. -/
theorem yoneda_map_tT : yoneda.map (tT dT) = dT.V.1.hom := yoneda.map_preimage _

omit E in
/-- `T_Y = T ×_{Y'} Y`, in the site. -/
theorem isPullback_TY_site :
    IsPullback ((rep_h (h := h)).snd dT.V.1.hom) ((rep_h (h := h)).fst' dT.V.1.hom) (tT dT) h :=
  isPullback_snd_fst'_of_map_eq (rep_h (h := h)) (yoneda_map_tT dT)

omit E in
/-- `T_{Z'} = T ×_{Y'} Z'`, in the site. -/
theorem isPullback_TZ'_site :
    IsPullback ((rep_g (g := g)).snd dT.V.1.hom) ((rep_g (g := g)).fst' dT.V.1.hom) (tT dT) g :=
  isPullback_snd_fst'_of_map_eq (rep_g (g := g)) (yoneda_map_tT dT)

/-- `T_Z = T_Y ×_Y Z`, in the site. -/
theorem isPullback_TZ_site :
    IsPullback ((rep_f (f := f)).snd (E.TY dT).1.hom) ((rep_f (f := f)).fst' (E.TY dT).1.hom)
      ((rep_h (h := h)).fst' dT.V.1.hom) f :=
  isPullback_snd_fst'_of_map_eq (rep_f (f := f)) ((rep_h (h := h)).map_fst' dT.V.1.hom)

/-- The composite `T_Z ⟶ T_{Z'} ⟶ T` is `T_Z ⟶ T_Y ⟶ T`. -/
theorem mapTZ_snd : E.mapTZ dT ≫ (rep_g (g := g)).snd dT.V.1.hom =
    (rep_f (f := f)).snd (E.TY dT).1.hom ≫ (rep_h (h := h)).snd dT.V.1.hom :=
  (rep_g (g := g)).lift_snd _ _ _

/-- The composite `T_Z ⟶ T_{Z'} ⟶ Z'` is `T_Z ⟶ Z ⟶ Z'`. -/
theorem mapTZ_fst :
    E.mapTZ dT ≫ (rep_g (g := g)).fst' dT.V.1.hom = (rep_f (f := f)).fst' (E.TY dT).1.hom ≫ i :=
  yoneda.map_injective <| (yoneda.map_comp _ _).trans <|
    (congrArg (yoneda.map (E.mapTZ dT) ≫ ·) ((rep_g (g := g)).map_fst' _)).trans <|
    ((rep_g (g := g)).lift_fst _ _ _).trans <|
    (congrArg (· ≫ yoneda.map i) ((rep_f (f := f)).map_fst' _).symm).trans
      (yoneda.map_comp _ _).symm

/-- `T_Z = T_{Z'} ×_{Z'} Z`, in the site: cancel `T_{Z'} = T ×_{Y'} Z'` from the pasting of
`T_Z = T_Y ×_Y Z` and `T_Y = T ×_{Y'} Y`. -/
theorem isPullback_TZZ'_site :
    IsPullback (E.mapTZ dT) ((rep_f (f := f)).fst' (E.TY dT).1.hom)
      ((rep_g (g := g)).fst' dT.V.1.hom) i := by
  have outer := (E.isPullback_TZ_site dT).paste_horiz (isPullback_TY_site (h := h) dT)
  rw [← E.mapTZ_snd, E.w] at outer
  exact IsPullback.of_right outer (E.mapTZ_fst dT) (isPullback_TZ'_site (g := g) dT)

omit E in
/-- The structure morphism of `T` over `Y'` is étale, hence flat. -/
theorem flat_tT : Flat ((BigFppfOver.toScheme B S hS).map (tT dT)) := by
  have h := dT.V.property
  change (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) dT.V.1.hom at h
  rw [← yoneda_map_tT] at h
  have : Etale ((BigFppfOver.toScheme B S hS).map (tT dT)) :=
    (presheaf_yoneda_map_iff B S hS (P := @Etale.{u}) inferInstance (tT dT)).1 h
  infer_instance

/-! ### The commutativity of the chart squares -/

/-- The composite `W_Z ⟶ W_{Z'} ⟶ W` is `W_Z ⟶ W_Y ⟶ W`. -/
theorem mapWZ_snd : E.mapWZ dT ≫ E.rep_b.snd dT.U.1.hom =
    E.rep_c.snd (E.WY dT).1.hom ≫ E.rep_a.snd dT.U.1.hom :=
  E.rep_b.lift_snd _ _ _

/-- The composite `W_Z ⟶ W_{Z'} ⟶ U'` is `W_Z ⟶ U ⟶ U'`. -/
theorem mapWZ_fst : yoneda.map (E.mapWZ dT) ≫ E.rep_b.fst dT.U.1.hom = (E.WZ dT).1.hom ≫ d.hom :=
  E.rep_b.lift_fst _ _ _

/-- The two composites `W_Z ⟶ T_{Z'}` agree. -/
theorem mapWZ_comp_dWZ'T :
    (E.dWZZ' dT).g ≫ (E.dWZ'T dT).g = (E.dWZT dT).g ≫ (E.dTZZ' dT).g := by
  let q := baseChangeChartSquareMap B S hS pU c _ pV (rep_f (f := f)) E.rep_c (E.dWYT dT)
    E.isPullback_c.w.symm
  have hq'f := baseChangeChartSquareMap_fst B S hS pU' b _ p (rep_g (g := g)) E.rep_b dT
    E.isPullback_b.w.symm
  have hqf := baseChangeChartSquareMap_fst B S hS pU c _ pV (rep_f (f := f)) E.rep_c (E.dWYT dT)
    E.isPullback_c.w.symm
  have hq's := baseChangeChartSquareMap_snd B S hS pU' b _ p (rep_g (g := g)) E.rep_b dT
    E.isPullback_b.w.symm
  have hqs := baseChangeChartSquareMap_snd B S hS pU c _ pV (rep_f (f := f)) E.rep_c (E.dWYT dT)
    E.isPullback_c.w.symm
  have hq₀s := baseChangeChartSquareMap_snd B S hS pV a _ p (rep_h (h := h)) E.rep_a dT
    E.isPullback_a.w.symm
  have hd : d.hom ≫ pU'.hom = pU.hom ≫ ((schemeSpaceFunctor B S hS).map i).hom :=
    congrArg (fun k => k.hom) E.comm_d
  refine (rep_g (g := g)).hom_ext ?_ ?_
  · exact ((congrArg (· ≫ (rep_g (g := g)).fst dT.V.1.hom) (yoneda.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (yoneda.map (E.mapWZ dT) ≫ ·) hq'f).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pU'.hom) (E.mapWZ_fst dT)).trans
      ((Category.assoc _ _ _).trans (congrArg ((E.WZ dT).1.hom ≫ ·) hd))))))).trans
      ((congrArg (· ≫ (rep_g (g := g)).fst dT.V.1.hom) (yoneda.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans
      ((congrArg (yoneda.map q ≫ ·) ((rep_g (g := g)).lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((schemeSpaceFunctor B S hS).map
        i).hom) hqf).trans (Category.assoc _ _ _)))))).symm
  · exact ((Category.assoc _ _ _).trans ((congrArg (E.mapWZ dT ≫ ·) hq's).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dT.g) (E.mapWZ_snd dT)).trans
      (Category.assoc _ _ _))))).trans
      ((Category.assoc _ _ _).trans ((congrArg (q ≫ ·) (E.mapTZ_snd dT)).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (rep_h (h := h)).snd dT.V.1.hom) hqs).trans
      ((Category.assoc _ _ _).trans (congrArg (E.rep_c.snd (E.WY dT).1.hom ≫ ·) hq₀s)))))).symm

/-! ### The relative Milnor square of a chart diagram -/

/-- **The rings of the eight charts above an affine chart diagram `W ⟶ T` of `P` over `Y'` form a
relative Milnor square** (the situation of Stacks 08KK): `Γ(T)` is the fibre product of `Γ(T_Y)`
and `Γ(T_{Z'})` over `Γ(T_Z)` with `Γ(T_{Z'}) ⟶ Γ(T_Z)` surjective, because `T` is flat over `Y'`
(`Stacks.Pushout.isFibreSquare_appTop_of_flat`), and the rings of the charts of `V`, `U'` and `U`
are the base changes of `Γ(W)` along it, because their squares of charts are cartesian with
affine corners (`AlgebraicGeometry.Space.isPushout_appTop_chartSquare_of_isAffineHom`). -/
theorem isRelativeSquare
    (hU : IsAffine ((SmallEtale.toOver B S hS P.1 ⋙ BigFppfOver.toScheme B S hS).obj dT.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj Y').1 ⋙
      BigFppfOver.toScheme B S hS).obj dT.V)) :
    MilnorPatching.IsRelativeSquare
      (chartDiagramRestrict B S hS ((schemeSpaceFunctor B S hS).map h) (E.dTY dT))
      (chartDiagramRestrict B S hS ((schemeSpaceFunctor B S hS).map g) (E.dTZ' dT))
      (chartDiagramRestrict B S hS ((schemeSpaceFunctor B S hS).map f) (E.dTZ dT))
      (chartDiagramRestrict B S hS ((schemeSpaceFunctor B S hS).map i) (E.dTZZ' dT))
      (chartDiagramRestrict B S hS p dT) (chartDiagramRestrict B S hS a (E.dWY dT))
      (chartDiagramRestrict B S hS pV (E.dWYT dT))
      (chartDiagramRestrict B S hS b (E.dWZ' dT))
      (chartDiagramRestrict B S hS pU' (E.dWZ'T dT))
      (chartDiagramRestrict B S hS c (E.dWZ dT))
      (chartDiagramRestrict B S hS d (E.dWZZ' dT))
      (chartDiagramRestrict B S hS pU (E.dWZT dT)) := by
  have hTZ' : IsAffine ((BigFppfOver.toScheme B S hS).obj (E.TZ' dT).1.left) :=
    isAffine_smallBaseChange_obj B S hS _ (rep_g (g := g)) E.isAffineHom_sp_g dT.V hV
  have hTY := isAffine_smallBaseChange_obj B S hS _ (rep_h (h := h)) E.isAffineHom_sp_h dT.V hV
  have hWY := isAffine_smallBaseChange_obj B S hS a E.rep_a E.isAffineHom_a dT.U hU
  have hcomm : (BigFppfOver.toScheme B S hS).map (E.mapTZ dT) ≫
      (BigFppfOver.toScheme B S hS).map ((rep_g (g := g)).snd dT.V.1.hom) =
      (BigFppfOver.toScheme B S hS).map ((rep_f (f := f)).snd (E.TY dT).1.hom) ≫
      (BigFppfOver.toScheme B S hS).map ((rep_h (h := h)).snd dT.V.1.hom) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg (BigFppfOver.toScheme B S hS).map
      (E.mapTZ_snd dT)).trans (Functor.map_comp _ _ _))
  have := E.isAffineHom
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Stacks.Pushout.isFibreSquare_appTop_of_flat E.isPushout E.isThickening (flat_tT dT)
      hcomm ((isPullback_TY_site (h := h) dT).map (BigFppfOver.toScheme B S hS))
      ((isPullback_TZ'_site (g := g) dT).map (BigFppfOver.toScheme B S hS))
      ((E.isPullback_TZ_site dT).map (BigFppfOver.toScheme B S hS))
      ((E.isPullback_TZZ'_site dT).map (BigFppfOver.toScheme B S hS)) hTZ'
  · exact isPushout_appTop_chartSquare_of_isAffineHom B S hS pV a _ p (rep_h (h := h)) E.rep_a
      dT E.isPullback_a.flip E.isAffineHom_sp_h hU hV
  · exact isPushout_appTop_chartSquare_of_isAffineHom B S hS pU' b _ p (rep_g (g := g)) E.rep_b
      dT E.isPullback_b.flip E.isAffineHom_sp_g hU hV
  · exact isPushout_appTop_chartSquare_of_isAffineHom B S hS pU c _ pV (rep_f (f := f)) E.rep_c
      (E.dWYT dT) E.isPullback_c.flip E.isAffineHom_sp_f hWY hTY
  · have e₀ : (E.dWZZ' dT).g ≫ (E.dWZ' dT).g = (E.dWZ dT).g ≫ (E.dWY dT).g := E.mapWZ_snd dT
    have e := congrArg (fun φ => ((BigFppfOver.toScheme B S hS).map φ).appTop.hom) e₀
    simp only at e
    exact e.symm
  · have e := congrArg (fun φ => ((BigFppfOver.toScheme B S hS).map φ).appTop.hom)
      (E.mapWZ_comp_dWZ'T dT)
    simp only at e
    exact e

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
