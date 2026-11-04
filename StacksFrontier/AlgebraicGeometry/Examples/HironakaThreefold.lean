module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaConicIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Gluing.TwoOpenRelativeGluing
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTowerOpen
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic

/-!
# Hironaka's threefold: the glued two-step blow-up of `ℙ³` in two conics

Let `k` be a field, `Y = ℙ³_k`, and let `C = {xy = z², w = 0}` and `D = {xy = w², z = 0}` be the
two conics of Hironaka's example, which meet in the two points `P = [1 : 0 : 0 : 0]` and
`Q = [0 : 1 : 0 : 0]` (see `StacksFrontier/AlgebraicGeometry/Examples/HironakaConicIdealSheaf.lean`).
This file builds the threefold `V` of [Stacks, Tag 08J1] and its morphism `f : V ⟶ Y`:

* over `Y - {Q}`, blow up `C` and then the strict transform of `D`
  (`AlgebraicGeometry.TwoStepTower.strictTower`);
* over `Y - {P}`, blow up `D` and then the strict transform of `C`;
* over `Y - {P, Q}` the conics are disjoint, so both towers are the blow-up of `C ∪ D`
  (`AlgebraicGeometry.TwoStepTower.strictTowerIso`), and the two towers glue
  (`Stacks.TwoOpenRelativeGluing.Datum`).

The glued morphism `f` is proper and Zariski-locally projective (over each of `Y - {Q}`,
`Y - {P}` it is a composite of two blow-ups in centres of finite type of a Noetherian scheme).
That `f` is not projective is the subject of later files.

## Main definitions

* `Stacks.Examples.HironakaThreefold.chartAwayQ`, `Stacks.Examples.HironakaThreefold.towerAwayQ`:
  the tower `C` then `D` over `Y - {Q}`.
* `Stacks.Examples.HironakaThreefold.chartAwayP`, `Stacks.Examples.HironakaThreefold.towerAwayP`:
  the tower `D` then `C` over `Y - {P}`.
* `Stacks.Examples.HironakaThreefold.overlapIso`: the identification of the two towers over
  `Y - {P, Q}`, as an isomorphism over `Y`.
* `Stacks.Examples.HironakaThreefold.gluingDatum`: the relative gluing datum.
* `Stacks.Examples.HironakaThreefold.hironakaThreefold`,
  `Stacks.Examples.HironakaThreefold.hironakaMorphism`: the glued scheme `V` and `f : V ⟶ Y`.
* `Stacks.Examples.HironakaThreefold.ιAwayQ`, `Stacks.Examples.HironakaThreefold.ιAwayP`: the two
  charts `Xᵢ ⟶ V`.

## Main results

* `Stacks.Examples.HironakaThreefold.isProper_hironakaMorphism`: `f` is proper.
* `Stacks.Examples.HironakaThreefold.isLocallyProjective_hironakaMorphism`: `f` is locally
  projective (Tag 01W8, third condition).
* `Stacks.Examples.HironakaThreefold.isPullback_awayQ`, `...isPullback_awayP`: the part of `V`
  over `Y - {Q}` (resp. `Y - {P}`) is the tower over it, as a cartesian square.
* `Stacks.Examples.HironakaThreefold.isPullback_fibre_awayQ_iff`, `...awayP_iff`: a fibre of the
  tower over a point of `Y - {Q}` (resp. `Y - {P}`) is a fibre of `f`, and conversely; this is
  the form in which the fibres of `f` over `P` and over `Q` are computed.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [H, Example B.3.4.1]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.TwoStepTower Stacks.Examples.HironakaConicIdealSheaf

universe u

namespace Stacks.Examples.HironakaThreefold

/-! ### Isomorphisms in `Over` -/

section OverIsos

variable {S Y : Scheme.{u}}

/-- An isomorphism of schemes over `S` is an isomorphism over `Y` after composing with
`g : S ⟶ Y`. -/
def overCompIso {A B : Scheme.{u}} {a : A ⟶ S} {b : B ⟶ S} (e : Over.mk a ≅ Over.mk b)
    (g : S ⟶ Y) : Over.mk (a ≫ g) ≅ Over.mk (b ≫ g) :=
  Over.isoMk ((Over.forget S).mapIso e) (by
    have h := Over.w e.hom
    simp only [Over.mk_hom] at h
    simp [reassoc_of% h])

/-- Equal structure morphisms give isomorphic objects of `Over Y`. -/
def overHomCongr {A : Scheme.{u}} {a a' : A ⟶ Y} (h : a = a') : Over.mk a ≅ Over.mk a' :=
  Over.isoMk (Iso.refl _) (by simp [h])

end OverIsos

/-! ### Towers over isomorphic bases -/

section Towers

variable {W : Scheme.{u}}

/-- The towers of equal centres are isomorphic over the base. -/
def towerEqIso {I₁ I₂ J₁ J₂ : W.IdealSheafData} (hI : I₁ = I₂) (hJ : J₁ = J₂) :
    Over.mk (strictTower I₁ J₁) ≅ Over.mk (strictTower I₂ J₂) :=
  eqToIso (by subst hI hJ; rfl)

/-- **The tower along an isomorphism of bases.** For an isomorphism `e : W' ≅ W`, the tower of
the pulled-back centres, composed with `e`, is isomorphic over `W` to the tower over `W`. -/
def towerIsoOfIso {W' : Scheme.{u}} (e : W' ≅ W) (I J : W.IdealSheafData) :
    Over.mk (strictTower (I.comap e.hom) (J.comap e.hom) ≫ e.hom) ≅ Over.mk (strictTower I J) :=
  haveI := (exists_isPullback_strictTower e.hom I J).choose_spec.isIso_snd_of_isIso
  Over.isoMk (asIso (exists_isPullback_strictTower e.hom I J).choose)
    (exists_isPullback_strictTower e.hom I J).choose_spec.w.symm

/-- The range of `V ⟶ U ⟶ Y` for `V` the inverse image in `U` of an open `U'` is `U ∩ U'`. -/
theorem range_ι_preimage_comp_ι {Y : Scheme.{u}} (U U' : Y.Opens) :
    Set.range ((U.ι ⁻¹ᵁ U').ι ≫ U.ι) = ((U ⊓ U' : Y.Opens) : Set Y) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1.2, y.2⟩
  · intro hx
    exact ⟨⟨⟨x, hx.1⟩, hx.2⟩, rfl⟩

/-- **The tower over an open, restricted to a smaller open, is the tower over that open.** Let
`U ⊆ Y` be open, `V ⊆ U` open, and `e : V ≅ W` an isomorphism with an open `W ⊆ Y` over `Y`.
Then the part over `V` of the tower of `I|U`, `J|U` is isomorphic over `Y` to the tower of
`I|W`, `J|W`. -/
def restrictTowerIso {Y : Scheme.{u}} (U : Y.Opens) (V : U.toScheme.Opens) (W : Y.Opens)
    (e : V.toScheme ≅ W.toScheme) (he : e.hom ≫ W.ι = V.ι ≫ U.ι) (I J : Y.IdealSheafData) :
    Over.mk ((strictTower (I.comap U.ι) (J.comap U.ι) ⁻¹ᵁ V).ι ≫
        strictTower (I.comap U.ι) (J.comap U.ι) ≫ U.ι) ≅
      Over.mk (strictTower (I.comap W.ι) (J.comap W.ι) ≫ W.ι) :=
  have hI : (I.comap U.ι).comap V.ι = (I.comap W.ι).comap e.hom := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, he]
  have hJ : (J.comap U.ι).comap V.ι = (J.comap W.ι).comap e.hom := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, he]
  overHomCongr (morphismRestrict_ι_assoc _ _ _).symm ≪≫
    overCompIso (nonempty_restrictIso (I.comap U.ι) (J.comap U.ι) V).some.symm (V.ι ≫ U.ι) ≪≫
    overCompIso (towerEqIso hI hJ) (V.ι ≫ U.ι) ≪≫
    overHomCongr (by simp only [Category.assoc, he]) ≪≫
    overCompIso (towerIsoOfIso e (I.comap W.ι) (J.comap W.ι)) W.ι

end Towers

/-! ### The two towers and their identification over `Y - {P, Q}` -/

variable (k : Type u) [Field k]

/-- The open subschemes of `ℙ³_k` are Noetherian. -/
instance isNoetherian_opens (U : (projectiveThreeSpace k).Opens) : IsNoetherian U.toScheme where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace U.ι

/-- **The tower over `Y - {Q}`**: its source, the blow-up of `C|_{Y - Q}` followed by the blow-up
of the strict transform of `D|_{Y - Q}`. -/
abbrev chartAwayQ : Scheme.{u} :=
  blowUp (strictCentre ((idealSheafC k).comap (opensAwayQ k).ι)
    ((idealSheafD k).comap (opensAwayQ k).ι))

/-- **The tower over `Y - {Q}`**: blow up `C`, then the strict transform of `D`. -/
abbrev towerAwayQ : chartAwayQ k ⟶ (opensAwayQ k).toScheme :=
  strictTower ((idealSheafC k).comap (opensAwayQ k).ι) ((idealSheafD k).comap (opensAwayQ k).ι)

/-- **The tower over `Y - {P}`**: its source, the blow-up of `D|_{Y - P}` followed by the blow-up
of the strict transform of `C|_{Y - P}`. -/
abbrev chartAwayP : Scheme.{u} :=
  blowUp (strictCentre ((idealSheafD k).comap (opensAwayP k).ι)
    ((idealSheafC k).comap (opensAwayP k).ι))

/-- **The tower over `Y - {P}`**: blow up `D`, then the strict transform of `C`. -/
abbrev towerAwayP : chartAwayP k ⟶ (opensAwayP k).toScheme :=
  strictTower ((idealSheafD k).comap (opensAwayP k).ι) ((idealSheafC k).comap (opensAwayP k).ι)

/-- The inverse image of `Y - {P}` in `Y - {Q}` is identified with `Y - {P, Q}`. -/
def overlapAwayQIso :
    ((opensAwayQ k).ι ⁻¹ᵁ opensAwayP k).toScheme ≅ (opensAwayPQ k).toScheme :=
  IsOpenImmersion.isoOfRangeEq (((opensAwayQ k).ι ⁻¹ᵁ opensAwayP k).ι ≫ (opensAwayQ k).ι)
    (opensAwayPQ k).ι (by
      rw [range_ι_preimage_comp_ι, Scheme.Opens.range_ι, opensAwayQ_inf_opensAwayP])

/-- The identification of the overlap inside `Y - {Q}` with `Y - {P, Q}` is over `Y`. -/
theorem overlapAwayQIso_hom_ι :
    (overlapAwayQIso k).hom ≫ (opensAwayPQ k).ι =
      ((opensAwayQ k).ι ⁻¹ᵁ opensAwayP k).ι ≫ (opensAwayQ k).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse image of `Y - {Q}` in `Y - {P}` is identified with `Y - {P, Q}`. -/
def overlapAwayPIso :
    ((opensAwayP k).ι ⁻¹ᵁ opensAwayQ k).toScheme ≅ (opensAwayPQ k).toScheme :=
  IsOpenImmersion.isoOfRangeEq (((opensAwayP k).ι ⁻¹ᵁ opensAwayQ k).ι ≫ (opensAwayP k).ι)
    (opensAwayPQ k).ι (by
      rw [range_ι_preimage_comp_ι, Scheme.Opens.range_ι, inf_comm, opensAwayQ_inf_opensAwayP])

/-- The identification of the overlap inside `Y - {P}` with `Y - {P, Q}` is over `Y`. -/
theorem overlapAwayPIso_hom_ι :
    (overlapAwayPIso k).hom ≫ (opensAwayPQ k).ι =
      ((opensAwayP k).ι ⁻¹ᵁ opensAwayQ k).ι ≫ (opensAwayP k).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Over `Y - {P, Q}` the two conics are disjoint. -/
theorem disjoint_supportSet_comap_opensAwayPQ :
    Disjoint ((idealSheafC k).comap (opensAwayPQ k).ι).supportSet
      ((idealSheafD k).comap (opensAwayPQ k).ι).supportSet :=
  disjoint_supportSet_of_sup_eq_top (comap_idealSheafC_sup_comap_idealSheafD_eq_top k)

/-- **The two towers agree over `Y - {P, Q}`**, as schemes over `Y`: the part of the tower over
`Y - {Q}` lying over `Y - {P}` is isomorphic over `Y` to the part of the tower over `Y - {P}`
lying over `Y - {Q}`. Both are the blow-up of the disjoint union of the conics there. -/
def overlapIso :
    Over.mk ((towerAwayQ k ⁻¹ᵁ ((opensAwayQ k).ι ⁻¹ᵁ opensAwayP k)).ι ≫ towerAwayQ k ≫
        (opensAwayQ k).ι) ≅
      Over.mk ((towerAwayP k ⁻¹ᵁ ((opensAwayP k).ι ⁻¹ᵁ opensAwayQ k)).ι ≫ towerAwayP k ≫
        (opensAwayP k).ι) :=
  restrictTowerIso (opensAwayQ k) _ (opensAwayPQ k) (overlapAwayQIso k) (overlapAwayQIso_hom_ι k)
      (idealSheafC k) (idealSheafD k) ≪≫
    overCompIso (strictTowerIso (disjoint_supportSet_comap_opensAwayPQ k)) (opensAwayPQ k).ι ≪≫
    (restrictTowerIso (opensAwayP k) _ (opensAwayPQ k) (overlapAwayPIso k)
      (overlapAwayPIso_hom_ι k) (idealSheafD k) (idealSheafC k)).symm

/-! ### The glued threefold -/

/-- **The relative gluing datum of Hironaka's example**: the tower `C` then `D` over `Y - {Q}`
and the tower `D` then `C` over `Y - {P}`, identified over `Y - {P, Q}` by `overlapIso`. -/
def gluingDatum : TwoOpenRelativeGluing.Datum (projectiveThreeSpace k) where
  U₁ := opensAwayQ k
  U₂ := opensAwayP k
  X₁ := chartAwayQ k
  X₂ := chartAwayP k
  f₁ := towerAwayQ k
  f₂ := towerAwayP k
  φ := (Over.forget _).mapIso (overlapIso k)
  comm := Over.w (overlapIso k).hom

/-- **Hironaka's threefold** `V`: the two towers glued over `Y - {P, Q}`. -/
abbrev hironakaThreefold : Scheme.{u} := (gluingDatum k).glued

/-- **Hironaka's morphism** `f : V ⟶ ℙ³_k`. -/
abbrev hironakaMorphism : hironakaThreefold k ⟶ projectiveThreeSpace k := (gluingDatum k).hom

/-- The chart of `V` over `Y - {Q}`. -/
abbrev ιAwayQ : chartAwayQ k ⟶ hironakaThreefold k := (gluingDatum k).ι₁

/-- The chart of `V` over `Y - {P}`. -/
abbrev ιAwayP : chartAwayP k ⟶ hironakaThreefold k := (gluingDatum k).ι₂

/-- On the chart over `Y - {Q}`, `f` is the tower. -/
@[reassoc]
theorem ιAwayQ_hironakaMorphism :
    ιAwayQ k ≫ hironakaMorphism k = towerAwayQ k ≫ (opensAwayQ k).ι :=
  (gluingDatum k).ι₁_hom

/-- On the chart over `Y - {P}`, `f` is the tower. -/
@[reassoc]
theorem ιAwayP_hironakaMorphism :
    ιAwayP k ≫ hironakaMorphism k = towerAwayP k ≫ (opensAwayP k).ι :=
  (gluingDatum k).ι₂_hom

/-- **The part of `V` over `Y - {Q}` is the tower `C` then `D`**, as a cartesian square. -/
theorem isPullback_awayQ :
    IsPullback (towerAwayQ k) (ιAwayQ k) (opensAwayQ k).ι (hironakaMorphism k) :=
  (gluingDatum k).isPullback₁

/-- **The part of `V` over `Y - {P}` is the tower `D` then `C`**, as a cartesian square. -/
theorem isPullback_awayP :
    IsPullback (towerAwayP k) (ιAwayP k) (opensAwayP k).ι (hironakaMorphism k) :=
  (gluingDatum k).isPullback₂

/-- The chart over `Y - {Q}` is an open immersion. -/
instance isOpenImmersion_ιAwayQ : IsOpenImmersion (ιAwayQ k) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_awayQ k) inferInstance

/-- The chart over `Y - {P}` is an open immersion. -/
instance isOpenImmersion_ιAwayP : IsOpenImmersion (ιAwayP k) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_awayP k) inferInstance

/-- The part of `V` over `Y - {Q}` is isomorphic to the source of the tower over `Y - {Q}`. -/
def isoAwayQ : (hironakaMorphism k ⁻¹ᵁ opensAwayQ k).toScheme ≅ chartAwayQ k :=
  (gluingDatum k).iso₁

/-- The part of `V` over `Y - {P}` is isomorphic to the source of the tower over `Y - {P}`. -/
def isoAwayP : (hironakaMorphism k ⁻¹ᵁ opensAwayP k).toScheme ≅ chartAwayP k :=
  (gluingDatum k).iso₂

/-- Under `isoAwayQ`, the restriction of `f` over `Y - {Q}` is the tower. -/
@[reassoc]
theorem isoAwayQ_hom_towerAwayQ :
    (isoAwayQ k).hom ≫ towerAwayQ k = hironakaMorphism k ∣_ opensAwayQ k :=
  (gluingDatum k).iso₁_hom_f₁

/-- Under `isoAwayP`, the restriction of `f` over `Y - {P}` is the tower. -/
@[reassoc]
theorem isoAwayP_hom_towerAwayP :
    (isoAwayP k).hom ≫ towerAwayP k = hironakaMorphism k ∣_ opensAwayP k :=
  (gluingDatum k).iso₂_hom_f₂

/-- Under `isoAwayQ`, the chart over `Y - {Q}` is the inclusion of the inverse image. -/
@[reassoc]
theorem isoAwayQ_hom_ιAwayQ :
    (isoAwayQ k).hom ≫ ιAwayQ k = (hironakaMorphism k ⁻¹ᵁ opensAwayQ k).ι :=
  (gluingDatum k).iso₁_hom_ι₁

/-- Under `isoAwayP`, the chart over `Y - {P}` is the inclusion of the inverse image. -/
@[reassoc]
theorem isoAwayP_hom_ιAwayP :
    (isoAwayP k).hom ≫ ιAwayP k = (hironakaMorphism k ⁻¹ᵁ opensAwayP k).ι :=
  (gluingDatum k).iso₂_hom_ι₂

/-- A square over a cartesian square `t, ι, j, f` with `j` monic is cartesian over `t` iff its
composite with `ι` is cartesian over `f`. -/
private theorem isPullback_fibre_iff_of_isPullback {X U V Y F K : Scheme.{u}} {t : X ⟶ U}
    {ι : X ⟶ V} {j : U ⟶ Y} {f : V ⟶ Y} [Mono j] (hp : IsPullback t ι j f) (q : F ⟶ X)
    (g : F ⟶ K) (y : K ⟶ U) : IsPullback q g t y ↔ IsPullback (q ≫ ι) g f (y ≫ j) := by
  refine ⟨fun h ↦ h.paste_horiz hp.flip, fun h ↦ IsPullback.of_right h ?_ hp.flip⟩
  refine (cancel_mono j).mp ?_
  simpa [hp.w] using h.w

/-- **Fibres of `f` over `Y - {Q}` are fibres of the tower.** For a morphism `y : K ⟶ Y - {Q}`
and `q : F ⟶ X₁`, `g : F ⟶ K`, the square of `q`, `g` over the tower is cartesian iff the
square of `q ≫ ι`, `g` over `f` and `y ≫ (Y - {Q} ⊆ Y)` is. -/
theorem isPullback_fibre_awayQ_iff {F K : Scheme.{u}} (q : F ⟶ chartAwayQ k) (g : F ⟶ K)
    (y : K ⟶ (opensAwayQ k).toScheme) :
    IsPullback q g (towerAwayQ k) y ↔
      IsPullback (q ≫ ιAwayQ k) g (hironakaMorphism k) (y ≫ (opensAwayQ k).ι) :=
  isPullback_fibre_iff_of_isPullback (isPullback_awayQ k) q g y

/-- **Fibres of `f` over `Y - {P}` are fibres of the tower.** For a morphism `y : K ⟶ Y - {P}`
and `q : F ⟶ X₂`, `g : F ⟶ K`, the square of `q`, `g` over the tower is cartesian iff the
square of `q ≫ ι`, `g` over `f` and `y ≫ (Y - {P} ⊆ Y)` is. -/
theorem isPullback_fibre_awayP_iff {F K : Scheme.{u}} (q : F ⟶ chartAwayP k) (g : F ⟶ K)
    (y : K ⟶ (opensAwayP k).toScheme) :
    IsPullback q g (towerAwayP k) y ↔
      IsPullback (q ≫ ιAwayP k) g (hironakaMorphism k) (y ≫ (opensAwayP k).ι) :=
  isPullback_fibre_iff_of_isPullback (isPullback_awayP k) q g y

/-! ### Properness and local projectivity -/

/-- The tower over `Y - {Q}` is projective. -/
theorem isProjective_towerAwayQ : IsProjective (towerAwayQ k) :=
  isProjective_strictTower ((isFiniteType_idealSheafC k).comap _) _

/-- The tower over `Y - {P}` is projective. -/
theorem isProjective_towerAwayP : IsProjective (towerAwayP k) :=
  isProjective_strictTower ((isFiniteType_idealSheafD k).comap _) _

/-- **Hironaka's morphism is proper.** -/
theorem isProper_hironakaMorphism : IsProper (hironakaMorphism k) :=
  (gluingDatum k).isProper_hom (opensAwayQ_sup_opensAwayP k) (isProjective_towerAwayQ k).isProper
    (isProjective_towerAwayP k).isProper

/-- **Hironaka's morphism is locally projective** (Tag 01W8, third condition): over `Y - {Q}`
and over `Y - {P}` it is a projective tower of blow-ups. -/
theorem isLocallyProjective_hironakaMorphism : IsLocallyProjective (hironakaMorphism k) :=
  (gluingDatum k).isLocallyProjective_hom (opensAwayQ_sup_opensAwayP k)
    (isProjective_towerAwayQ k) (isProjective_towerAwayP k)

end Stacks.Examples.HironakaThreefold

end
