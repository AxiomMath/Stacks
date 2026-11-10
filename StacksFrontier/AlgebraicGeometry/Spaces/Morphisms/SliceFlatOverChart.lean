module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GlobalSectionsSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Flatness of `V(f₁, …, f_r)` on the open subspace swept out by an affine étale chart

Let `g : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `f₁, …, f_r` be global
regular functions on `X`.  The last step of the proof of Stacks 06LW passes from the scheme-level
slicing lemma Stacks 06LI, applied on an étale chart `U` of `X`, back to the algebraic space: the
image of the chart is an open subspace `X' ⊆ X` (Stacks 06NF), and `V(f₁, …, f_r) ∩ X'` is
flat and locally of finite presentation over `Y` as soon as the zero scheme of the restricted
functions in `U` is so over an étale chart of `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_holdsOnEveryEtaleChart_vanishingSubfunctor`:
  for an affine étale chart `U` of `X` lying over an étale chart `V` of `Y`, if the zero scheme
  `V(f₁|_U, …, f_r|_U) ⊆ U` has a property `P` (étale local on source and target, stable under
  composition, and held by étale morphisms) over `V`, then `V(f₁, …, f_r) ∩ X'` has `P` over
  `Y` on every étale chart, where `X'` is the open image of `U`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor`: the case of
  flatness together with local finite presentation.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber`:
  the flatness half of Stacks 06LW with the regular sequence read in the local ring of the fibre
  of one étale chart `E ⟶ V` at a point `e`; the open subspace contains the image of `e`.

## References

* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`V(f₁, …, f_r)` restricted to the image of an affine étale chart.**  Let `g : X ⟶ Y` be a
morphism of algebraic spaces, `f₁, …, f_r` global functions on `X`, `U` an affine étale chart of
`X` and `q : V ⟶ Y` an étale chart of `Y` with a morphism `a : U ⟶ V` over `g`.  If the zero
scheme `V(f₁|_U, …, f_r|_U) ⊆ U` has `P` over `V`, then `V(f₁, …, f_r) ∩ X' ⟶ Y` has `P` on
every étale chart, where `X' ⊆ X` is an open subspace with the same points as the image of `U`
(Stacks 06NF), the same for every property `P` of morphisms of schemes which is étale local on
source and target, stable under composition and held by étale morphisms. -/
theorem exists_isOpenSubspace_holdsOnEveryEtaleChart_vanishingSubfunctor
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
    (hq : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf q)
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ V) (hcomm : U.1.hom ≫ g = yoneda.map a ≫ q) :
    ∃ (X' : Subfunctor X.1) (_ : IsOpenSubspace B S hS X'),
      Set.range (pointsMap B S hS X'.toFunctor X'.ι) =
        Set.range (pointsMap B S hS _ U.1.hom) ∧
      ∀ (P : MorphismProperty Scheme.{u}), IsEtaleLocalOnSourceAndTarget P →
        P.IsStableUnderComposition → (∀ {Z W : Scheme.{u}} (h : Z ⟶ W), Etale h → P h) →
        P ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => (f i).eval (op U)))).subschemeι ≫
            (BigFppfOver.toScheme B S hS).map a) →
        HoldsOnEveryEtaleChart B S hS P
          (((vanishingSubfunctor B S hS X f).preimage X'.ι).ι ≫ X'.ι ≫ g) := by
  obtain ⟨Z, hZeq, hiso⟩ := exists_closedSubspace_iso_zeroScheme_chartBaseChange B S hS X f
  obtain ⟨e, he⟩ := hiso U hU
  obtain ⟨X', ψ, hX', hψ, hψsurj, hψet, hrange⟩ :=
    exists_isOpenSubspace_etaleImage B S hS X.2 _ U.1.hom U.2
  refine ⟨X', hX', hrange, fun P hP hPcomp hPetale hslice => ?_⟩
  rw [hZeq]
  set T := BigFppfOver.toScheme B S hS
  have hZ' : IsAlgebraicSpace B S hS (Z.1.preimage X'.ι).toFunctor :=
    (isClosedSubspace_preimage B S hS X'.ι Z.1 X.2 hX'.1 Z.2).1
  have hsqR := Subfunctor.isPullback_preimage X'.ι Z.1
  have hbig := Z.2.2.rep.isPullback U.1.hom
  have hw : Z.2.2.rep.fst U.1.hom ≫ Z.1.ι = (yoneda.map (Z.2.2.rep.snd U.1.hom) ≫ ψ) ≫ X'.ι := by
    rw [Category.assoc, hψ]
    exact hbig.w
  let c := hsqR.lift (Z.2.2.rep.fst U.1.hom) (yoneda.map (Z.2.2.rep.snd U.1.hom) ≫ ψ) hw
  have hc₁ : c ≫ Z.1.fromPreimage X'.ι = Z.2.2.rep.fst U.1.hom := hsqR.lift_fst _ _ _
  have hc₂ : c ≫ (Z.1.preimage X'.ι).ι = yoneda.map (Z.2.2.rep.snd U.1.hom) ≫ ψ :=
    hsqR.lift_snd _ _ _
  have hleft : IsPullback c (yoneda.map (Z.2.2.rep.snd U.1.hom)) (Z.1.preimage X'.ι).ι ψ := by
    refine IsPullback.of_right ?_ hc₂ hsqR
    rw [hc₁, hψ]
    exact hbig
  refine holdsOnEveryEtaleChart_of_surjectiveEtale_source B S hS P hP hZ' Y.2 _ c
    (presheaf_of_isPullback B S hS hleft.flip hψsurj)
    (presheaf_of_isPullback B S hS hleft.flip hψet) ?_
  have hceq : c ≫ (Z.1.preimage X'.ι).ι ≫ X'.ι ≫ g =
      yoneda.map (Z.2.2.rep.snd U.1.hom ≫ a) ≫ q := by
    rw [reassoc_of% hc₂, reassoc_of% hψ, hcomm, Functor.map_comp, Category.assoc]
  rw [hceq]
  refine holdsOnEveryEtaleChart_comp B S hS P hP (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS V) Y.2 _ q ?_ ?_
  · refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS hP _).2 ?_
    have hmap : T.map (Z.2.2.rep.snd U.1.hom ≫ a) =
        e.hom ≫ ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => (f i).eval (op U)))).subschemeι ≫ T.map a) := by
      rw [T.map_comp, reassoc_of% he]
      rfl
    rw [hmap]
    exact hPcomp.comp_mem _ _ (hPetale _ inferInstance) hslice
  · exact holdsOnEveryEtaleChart_of_isEtale_hom B S hS P hPetale Y.2
      ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hq)

/-- **`V(f₁, …, f_r)` restricted to the image of an affine étale chart is flat and locally of
finite presentation** over `Y` when the zero scheme of the restricted functions is so over an
étale chart of `Y`. -/
theorem exists_isOpenSubspace_isFlat_vanishingSubfunctor
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
    (hq : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf q)
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ V) (hcomm : U.1.hom ≫ g = yoneda.map a ≫ q)
    (hflat : Flat ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.ofList (List.ofFn fun i => (f i).eval (op U)))).subschemeι ≫
        (BigFppfOver.toScheme B S hS).map a))
    (hlfp : LocallyOfFinitePresentation ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.ofList (List.ofFn fun i => (f i).eval (op U)))).subschemeι ≫
        (BigFppfOver.toScheme B S hS).map a)) :
    ∃ (X' : Subfunctor X.1) (_ : IsOpenSubspace B S hS X'),
      Set.range (pointsMap B S hS X'.toFunctor X'.ι) =
        Set.range (pointsMap B S hS _ U.1.hom) ∧
      IsFlat B S hS (((vanishingSubfunctor B S hS X f).preimage X'.ι).ι ≫ X'.ι ≫ g) ∧
      IsLocallyOfFinitePresentation B S hS
        (((vanishingSubfunctor B S hS X f).preimage X'.ι).ι ≫ X'.ι ≫ g) := by
  obtain ⟨X', hX', hrange, hP⟩ :=
    exists_isOpenSubspace_holdsOnEveryEtaleChart_vanishingSubfunctor B S hS X Y g f U hU V q hq a
      hcomm
  exact ⟨X', hX', hrange,
    hP _ Flat.isEtaleLocalOnSourceAndTarget inferInstance (fun _ _ => inferInstance) hflat,
    hP _ LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget inferInstance
      (fun _ _ => inferInstance) hlfp⟩

/-- **The flatness half of Stacks 06LW, read on one étale chart.**  Let `g : X ⟶ Y` be a morphism
of algebraic spaces, `f₁, …, f_r` global functions on `X`, `E` an étale chart of `X` over an
étale chart `q : V ⟶ Y` of `Y` through `a : E ⟶ V`, and `e` a point of `E` at which `a` is
locally of finite presentation and flat and at which the `f_i|_E` map to a regular sequence in the
local ring of the fibre of `a`.  Then there is an open subspace `X' ⊆ X` containing the image of
`e` such that `V(f₁, …, f_r) ∩ X' ⟶ Y` is flat and locally of finite presentation.

The slicing lemma Stacks 06LI, in the form
`Stacks.AlgebraicGeometry.exists_affine_openImmersion_flat_zeroScheme_of_isRegular_fiber`, gives
an affine open `D` of `E` through `e`, which is an étale chart of `X` on its own, and
`AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor` takes `X'` to be its
image. -/
theorem exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (E : SmallEtale B S hS X.1)
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
    (hq : (MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)).presheaf q)
    (a : (SmallEtale.toOver B S hS X.1).obj E ⟶ V) (hcomm : E.1.hom ≫ g = yoneda.map a ≫ q)
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map a)] (e : chartScheme E)
    (hflat : _root_.AlgebraicGeometry.IsFlatAt
      ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom e)
    (hregular : RingTheory.Sequence.IsRegular
      ((((BigFppfOver.toScheme B S hS).map a).fiber
        (((BigFppfOver.toScheme B S hS).map a) e)).presheaf.stalk
          (((BigFppfOver.toScheme B S hS).map a).asFiber e))
      (List.ofFn fun i : Fin r =>
        ((((BigFppfOver.toScheme B S hS).map a).fiberι
          (((BigFppfOver.toScheme B S hS).map a) e)).stalkMap
            (((BigFppfOver.toScheme B S hS).map a).asFiber e)).hom
          ((((BigFppfOver.toScheme B S hS).map a).fiberι_asFiber e).symm ▸
            (chartScheme E).presheaf.germ ⊤ e trivial ((f i).eval (op E))))) :
    ∃ (X' : Subfunctor X.1) (_ : IsOpenSubspace B S hS X'),
      chartPointsMap E e ∈ Set.range (pointsMap B S hS X'.toFunctor X'.ι) ∧
      IsFlat B S hS (((vanishingSubfunctor B S hS X f).preimage X'.ι).ι ≫ X'.ι ≫ g) ∧
      IsLocallyOfFinitePresentation B S hS
        (((vanishingSubfunctor B S hS X f).preimage X'.ι).ι ≫ X'.ι ≫ g) := by
  set T := BigFppfOver.toScheme B S hS
  obtain ⟨D, j, hj, hD, ⟨d, hd⟩, hfl, hfp⟩ :=
    Stacks.AlgebraicGeometry.exists_affine_openImmersion_flat_zeroScheme_of_isRegular_fiber
      (T.map a) e (fun i => (f i).eval (op E)) hflat hregular
  have hcont : B.Contains D :=
    B.contains_of_isOpenImmersion j ((SmallEtale.toOver B S hS X.1).obj E).left.2
  let Dobj : BigFppfOver B S hS :=
    BigFppfOver.mk B S hS hcont (j ≫ B.inclusion.map ((SmallEtale.toOver B S hS X.1).obj E).hom)
  let jm : Dobj ⟶ (SmallEtale.toOver B S hS X.1).obj E :=
    Over.homMk (ObjectProperty.homMk (X := B.obj hcont)
      (Y := ((SmallEtale.toOver B S hS X.1).obj E).left) j)
      (by apply ObjectProperty.hom_ext; rfl)
  have := hj
  have hjmet : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf (yoneda.map jm) :=
    (presheaf_yoneda_map_iff B S hS inferInstance jm).2 (inferInstanceAs (Etale j))
  have hmul := isMultiplicative_presheaf_etale B S hS
  let D' : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map jm ≫ E.1.hom),
      MorphismProperty.comp_mem _ _ _ hjmet E.2⟩
  let h : D' ⟶ E := ObjectProperty.homMk (CostructuredArrow.homMk jm rfl)
  have hcomm' : D'.1.hom ≫ g = yoneda.map (jm ≫ a) ≫ q := by
    change (yoneda.map jm ≫ E.1.hom) ≫ g = _
    rw [Category.assoc, hcomm, Functor.map_comp, Category.assoc]
  have hfun : (fun i => (f i).eval (op D') : Fin r → Γ(T.obj Dobj, ⊤)) =
      fun i => j.appTop ((f i).eval (op E)) :=
    funext fun i => (PresheafOfModules.sections_property (f i) h.op).symm
  have hmapa : T.map (jm ≫ a) = j ≫ T.map a := T.map_comp _ _
  obtain ⟨X', hX', hrange, hXflat, hXlfp⟩ :=
    exists_isOpenSubspace_isFlat_vanishingSubfunctor B S hS X Y g f D' hD V q hq (jm ≫ a) hcomm'
      (by rw [hfun, hmapa]; exact hfl) (by rw [hfun, hmapa]; exact hfp)
  refine ⟨X', hX', ?_, hXflat, hXlfp⟩
  rw [hrange, ← hd]
  have hpt := chartPointsMap_comp (B := B) (S := S) (hS := hS) (g := h) (x := d)
  have hmem : chartPointsMap D' d ∈ Set.range (pointsMap B S hS _ D'.1.hom) := ⟨_, rfl⟩
  exact hpt ▸ hmem

end AlgebraicGeometry.Space

end
