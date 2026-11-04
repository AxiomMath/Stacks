module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.PrincipalCenterHDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafCriterion

/-!
# Cartesianness on almost blowup squares over an arbitrary base

Condition (3) of Stacks 0EVF, `AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpSheaf`, asks a
presheaf `F` on the big h category over `S` to send an almost blowup square of the site to a
cartesian square of sets when the base of the square has affine underlying scheme. Together with
condition (1), the Zariski sheaf condition `AlgebraicGeometry.BigHOver.IsZariskiSheaf`, it
implies that `F` sends every almost blowup square of the site to a cartesian square of sets.

An almost blowup square is recorded as in `AlgebraicGeometry.BigHOver.IsAffineAlmostBlowUpSheaf`:
by its base `X`, its modification `b : X' ⟶ X`, a quasi-coherent ideal sheaf `I` on the
underlying scheme of `X` for which `b` is an almost blowup square with centre `I`, an
identification over `X` of the centre `z : Z ⟶ X` with the closed subscheme cut out by `I`, and
cartesianness of the square of schemes underlying `(z, b, e, p)`.

## Main results

* `AlgebraicGeometry.BigHOver.isPullback_of_isAffineAlmostBlowUpSheaf`: conditions (1) and (3) of
  Stacks 0EVF imply that the image of every almost blowup square of the site is cartesian.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EV6](https://stacks.math.columbia.edu/tag/0EV6)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace BigHOver

section Interlude

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}

/-! ### Restriction along commuting squares -/

/-- Restricting a section along the two sides of a commuting square gives the same result. -/
private theorem map_op_comm {X Y T V : BigHOver B S hS} {y : Y ⟶ X} {w : T ⟶ X}
    {a : V ⟶ Y} {f : V ⟶ T} (hc : a ≫ y = f ≫ w) (s : F.obj (op X)) :
    F.map a.op (F.map y.op s) = F.map f.op (F.map w.op s) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hc]

/-- Let `(e, p, z, b)` be a cartesian square and let a section over `Z` and a section over `X'`
have the same restriction to `E`.  Then they have the same restriction along any pair of
morphisms completing `(z, b)` to a commuting square. -/
private theorem map_op_eq_of_isPullback {X X' Z E V : BigHOver B S hS}
    {b : X' ⟶ X} {z : Z ⟶ X} {p : E ⟶ X'} {e : E ⟶ Z} (hsq : IsPullback e p z b)
    {t : F.obj (op Z)} {s : F.obj (op X')} (hc : F.map e.op t = F.map p.op s)
    {a : V ⟶ Z} {f : V ⟶ X'} (hcomm : a ≫ z = f ≫ b) :
    F.map a.op t = F.map f.op s := by
  rw [← hsq.lift_fst a f hcomm, op_comp, Functor.map_comp_apply, hc, ← Functor.map_comp_apply,
    ← op_comp, hsq.lift_snd]

/-- Sections over `Y₁` and `Y₂` which restrict to the same section over `C` on the fibre products
with `C` agree on `W` along the base change of `f₁` to `C`, for `gi ≫ f₁ = gj ≫ f₂`. -/
private theorem map_op_pullback_fst_comp_eq {X C W Y₁ Y₂ : BigHOver B S hS} (c : C ⟶ X)
    {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} {gi : W ⟶ Y₁} {gj : W ⟶ Y₂} (hgij : gi ≫ f₁ = gj ≫ f₂)
    {w₁ : F.obj (op Y₁)} {w₂ : F.obj (op Y₂)} {t : F.obj (op C)}
    (h₁ : F.map (pullback.fst f₁ c).op w₁ = F.map (pullback.snd f₁ c).op t)
    (h₂ : F.map (pullback.fst f₂ c).op w₂ = F.map (pullback.snd f₂ c).op t) :
    F.map (pullback.fst (gi ≫ f₁) c).op (F.map gi.op w₁) =
      F.map (pullback.fst (gi ≫ f₁) c).op (F.map gj.op w₂) := by
  have h₁' := map_op_eq_of_isPullback (IsPullback.of_hasPullback f₁ c) h₁
    (a := pullback.fst (gi ≫ f₁) c ≫ gi) (f := pullback.snd (gi ≫ f₁) c)
    (by rw [Category.assoc]; exact pullback.condition)
  have h₂' := map_op_eq_of_isPullback (IsPullback.of_hasPullback f₂ c) h₂
    (a := pullback.fst (gi ≫ f₁) c ≫ gj) (f := pullback.snd (gi ≫ f₁) c)
    (by rw [Category.assoc, ← hgij]; exact pullback.condition)
  simp only [op_comp, Functor.map_comp_apply] at h₁' h₂'
  rw [h₁', h₂']

/-! ### Base changing an almost blowup square of the site -/

/-- The base change in the site of the modification of an almost blowup square along an
arbitrary morphism of the site is again the modification of an almost blowup square, with centre
the inverse image of the original centre. -/
private theorem isAlmostBlowUpSquare_map_pullback_fst
    {X X' Y : BigHOver B S hS} (b : X' ⟶ X) (g : Y ⟶ X)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b)) :
    IsAlmostBlowUpSquare (I.comap ((BigHOver.toScheme B S hS).map g))
      ((BigHOver.toScheme B S hS).map (pullback.fst g b)) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
  have hiso : IsIso (pullbackComparison (BigHOver.toScheme B S hS) g b) := inferInstance
  rw [← pullbackComparison_comp_fst (BigHOver.toScheme B S hS) g b]
  exact isAlmostBlowUpSquare_isIso_comp _
    (isAlmostBlowUpSquare_baseChange I ((BigHOver.toScheme B S hS).map b)
      ((BigHOver.toScheme B S hS).map g) hb) _

/-- The base change in the site of the centre of an almost blowup square along an arbitrary
morphism of the site is the closed subscheme cut out by the inverse image of the original
centre. -/
private theorem nonempty_subschemeIso_map_pullback_fst
    {X Z Y : BigHOver B S hS} (z : Z ⟶ X) (g : Y ⟶ X)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hZiso : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι)) :
    Nonempty (Over.mk ((BigHOver.toScheme B S hS).map (pullback.fst g z)) ≅
      Over.mk (I.comap ((BigHOver.toScheme B S hS).map g)).subschemeι) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
  have hiso : IsIso (pullbackComparison (BigHOver.toScheme B S hS) g z) := inferInstance
  let K := BigHOver.toScheme B S hS
  let e₁ : Over.mk (K.map (pullback.fst g z)) ≅ Over.mk (pullback.fst (K.map g) (K.map z)) :=
    Over.isoMk (asIso (pullbackComparison K g z)) (pullbackComparison_comp_fst K g z)
  let e₂ : Over.mk (pullback.fst (K.map g) (K.map z)) ≅
      Over.mk (pullback.fst (K.map g) I.subschemeι) :=
    pullbackOverIso (K.map g) (K.map z) I.subschemeι hZiso.some
  let e₃ : Over.mk (pullback.fst (K.map g) I.subschemeι) ≅
      Over.mk (I.comap (K.map g)).subschemeι :=
    Over.isoMk (I.comapIso (K.map g)).symm
      (Scheme.IdealSheafData.comapIso_inv_subschemeι I (K.map g))
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃⟩

/-- Under condition (3) of Stacks 0EVF, the base change of an almost blowup square of the site
along a morphism whose source has affine underlying scheme, completed by the fibre product in the
site of the base changed centre and the base changed modification, is sent to a cartesian
square. -/
private theorem isPullback_map_pullback_of_isAffine
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F)
    {X X' Z Y : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (g : Y ⟶ X)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hZiso : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    (hY : IsAffine ((BigHOver.toScheme B S hS).obj Y)) :
    IsPullback (F.map (pullback.fst g z).op) (F.map (pullback.fst g b).op)
      (F.map (pullback.fst (pullback.fst g z) (pullback.fst g b)).op)
      (F.map (pullback.snd (pullback.fst g z) (pullback.fst g b)).op) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
  exact h3 Y (pullback g b) (pullback g z) (pullback (pullback.fst g z) (pullback.fst g b))
    (pullback.fst g b) (pullback.fst g z)
    (pullback.snd (pullback.fst g z) (pullback.fst g b))
    (pullback.fst (pullback.fst g z) (pullback.fst g b))
    (I.comap ((BigHOver.toScheme B S hS).map g)) hY
    (isAlmostBlowUpSquare_map_pullback_fst b g I hb)
    (nonempty_subschemeIso_map_pullback_fst z g I hZiso)
    ((IsPullback.of_hasPullback (pullback.fst g z) (pullback.fst g b)).map
      (BigHOver.toScheme B S hS))

/-! ### Injectivity over an arbitrary base -/

/-- Under conditions (1) and (3) of Stacks 0EVF, two sections over the base of an almost blowup
square of the site which restrict to the same section of the centre and to the same section of
the modification are equal. -/
private theorem eq_of_map_op_eq
    (hZsh : BigHOver.IsZariskiSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F)
    {X X' Z : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hZiso : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    {s t : F.obj (op X)} (hz : F.map z.op s = F.map z.op t)
    (hbb : F.map b.op s = F.map b.op t) : s = t := by
  let Xs := (BigHOver.toScheme B S hS).obj X
  let U₀ := (Scheme.affineOpenCover.{u} Xs).openCover
  let U : Scheme.OpenCover.{u + 1, u} Xs := U₀.reindex (Equiv.ulift.{u + 1, u})
  apply (preZeroHypercoverOfOpenCover_isSheafFor hZsh X U).isSeparatedFor.ext
  rintro V f ⟨i⟩
  have hA : IsAffine
      ((BigHOver.toScheme B S hS).obj ((preZeroHypercoverOfOpenCover U).X i)) :=
    Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
  refine Types.ext_of_isPullback
    (isPullback_map_pullback_of_isAffine h3 b z ((preZeroHypercoverOfOpenCover U).f i) I hb
      hZiso hA) ?_ ?_
  · rw [map_op_comm (pullback.condition
        (f := (preZeroHypercoverOfOpenCover U).f i) (g := z)) s,
      map_op_comm (pullback.condition
        (f := (preZeroHypercoverOfOpenCover U).f i) (g := z)) t, hz]
  · rw [map_op_comm (pullback.condition
        (f := (preZeroHypercoverOfOpenCover U).f i) (g := b)) s,
      map_op_comm (pullback.condition
        (f := (preZeroHypercoverOfOpenCover U).f i) (g := b)) t, hbb]

end Interlude

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- Let `F` be a presheaf of sets on the big h
category over `S` satisfying condition (1) of Stacks 0EVF, the sheaf condition for Zariski
coverings, and condition (3), cartesianness of the image of every almost blowup square of the
site whose base has affine underlying scheme. Then the image of *every* almost blowup square of
the site is cartesian: for a modification `b : X' ⟶ X` which is an almost blowup square with
centre the quasi-coherent ideal sheaf `I`, a centre `z : Z ⟶ X` identified over `X` with the
closed subscheme cut out by `I`, and an exceptional corner `p : E ⟶ X'`, `e : E ⟶ Z` completing
`(z, b)` to a cartesian square of schemes, the square `F(E) ← F(X')`, `F(Z) ← F(X)` is cartesian
in sets. -/
public theorem isPullback_of_isAffineAlmostBlowUpSheaf
    (hZ : BigHOver.IsZariskiSheaf B S hS F)
    (h3 : BigHOver.IsAffineAlmostBlowUpSheaf B S hS F)
    (X X' Z E : BigHOver B S hS) (b : X' ⟶ X) (z : Z ⟶ X) (p : E ⟶ X') (e : E ⟶ Z)
    (I : ((BigHOver.toScheme B S hS).obj X).IdealSheafData)
    (hb : IsAlmostBlowUpSquare I ((BigHOver.toScheme B S hS).map b))
    (hZiso : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk I.subschemeι))
    (hsq : IsPullback
      ((BigHOver.toScheme B S hS).map e)
      ((BigHOver.toScheme B S hS).map p)
      ((BigHOver.toScheme B S hS).map z)
      ((BigHOver.toScheme B S hS).map b)) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map p.op) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
  have hsq' : IsPullback e p z b := IsPullback.of_map_of_faithful (BigHOver.toScheme B S hS) hsq
  let Xs := (BigHOver.toScheme B S hS).obj X
  let U₀ := (Scheme.affineOpenCover.{u} Xs).openCover
  let U : Scheme.OpenCover.{u + 1, u} Xs := U₀.reindex (Equiv.ulift.{u + 1, u})
  let EX := preZeroHypercoverOfOpenCover U
  have hA : ∀ i, IsAffine ((BigHOver.toScheme B S hS).obj (EX.X i)) := fun i ↦
    Scheme.isAffine_affineOpenCover _ _ (Equiv.ulift.{u + 1, u} i)
  have hEX : Presieve.IsSheafFor F (Presieve.ofArrows EX.X EX.f) :=
    preZeroHypercoverOfOpenCover_isSheafFor hZ X U
  have hU : (EX.map (BigHOver.toScheme B S hS)).presieve₀ ∈ Scheme.zariskiPrecoverage Xs := by
    simpa [EX, preZeroHypercoverOfOpenCover, PreZeroHypercover.presieve₀,
      PreZeroHypercover.map] using U.mem₀
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hsq'.w]
  · exact fun x y hxy ↦ eq_of_map_op_eq hZ h3 b z I hb hZiso hxy.1 hxy.2
  · intro t s' hc
    have key : ∀ i, ∃ w : F.obj (op (EX.X i)),
        F.map (pullback.fst (EX.f i) z).op w = F.map (pullback.snd (EX.f i) z).op t ∧
          F.map (pullback.fst (EX.f i) b).op w = F.map (pullback.snd (EX.f i) b).op s' := by
      intro i
      refine Types.exists_of_isPullback
        (isPullback_map_pullback_of_isAffine h3 b z (EX.f i) I hb hZiso (hA i)) _ _ ?_
      have hcomm : (pullback.fst (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
            pullback.snd (EX.f i) z) ≫ z
          = (pullback.snd (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
            pullback.snd (EX.f i) b) ≫ b := by
        have c₁ : pullback.fst (EX.f i) z ≫ EX.f i = pullback.snd (EX.f i) z ≫ z :=
          pullback.condition
        have c₂ : pullback.fst (EX.f i) b ≫ EX.f i = pullback.snd (EX.f i) b ≫ b :=
          pullback.condition
        have c₃ : pullback.fst (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
              pullback.fst (EX.f i) z
            = pullback.snd (pullback.fst (EX.f i) z) (pullback.fst (EX.f i) b) ≫
              pullback.fst (EX.f i) b := pullback.condition
        rw [Category.assoc, ← c₁, ← Category.assoc, c₃, Category.assoc, c₂, ← Category.assoc]
      simpa only [op_comp, Functor.map_comp_apply] using
        map_op_eq_of_isPullback hsq' hc hcomm
    choose w hw₁ hw₂ using key
    have hcompat : Presieve.Arrows.Compatible F EX.f w := by
      intro i j W gi gj hgij
      refine eq_of_map_op_eq hZ h3 (pullback.fst (gi ≫ EX.f i) b)
        (pullback.fst (gi ≫ EX.f i) z)
        (I.comap ((BigHOver.toScheme B S hS).map (gi ≫ EX.f i)))
        (isAlmostBlowUpSquare_map_pullback_fst b (gi ≫ EX.f i) I hb)
        (nonempty_subschemeIso_map_pullback_fst z (gi ≫ EX.f i) I hZiso) ?_ ?_
      · exact map_op_pullback_fst_comp_eq z hgij (hw₁ i) (hw₁ j)
      · exact map_op_pullback_fst_comp_eq b hgij (hw₂ i) (hw₂ j)
    obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff F EX.f).mp hEX w hcompat
    have glue : ∀ {C : BigHOver B S hS} (c : C ⟶ X) (t : F.obj (op C)),
        (∀ i, F.map (pullback.fst (EX.f i) c).op (w i) = F.map (pullback.snd (EX.f i) c).op t) →
          F.map c.op s = t := by
      intro C c t hw
      apply (isSheafFor_pullback_of_zariskiCover hZ EX hU c).isSeparatedFor.ext
      rintro V f ⟨W, a, h, ⟨i⟩, hcomm⟩
      rw [← map_op_comm hcomm, hs i]
      exact map_op_eq_of_isPullback (IsPullback.of_hasPullback (EX.f i) c) (hw i) hcomm
    exact ⟨s, glue z t hw₁, glue b s' hw₂⟩

end BigHOver

end AlgebraicGeometry

end
