module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Base change of a relative effective Cartier divisor on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `D ⊆ X` be a
closed subspace which is an effective Cartier divisor and whose structure morphism `D ⟶ Y` is
flat — in the terminology of Stacks 0EPP, a *relative* effective Cartier divisor.  Then for
every morphism `g : Y' ⟶ Y` the inverse image of `D` in the fibre product `X' = Y' ×_Y X` is
again an effective Cartier divisor, that is, the pullback of `D` along the projection
`g' : X' ⟶ X` is defined in the sense of Stacks 083Y.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_comap_of_isPullback`: the scheme case Stacks
  056Q read on an arbitrary cartesian square rather than on the chosen fibre product.
* `AlgebraicGeometry.Space.isPullbackDefined_of_isPullback_of_isFlat`: **Stacks 0EPN**, the
  pullback of a relative effective Cartier divisor along an arbitrary base change is defined.
* `AlgebraicGeometry.Space.isPullbackDefined_fibreProduct_snd_of_isFlat`: the same for the
  chosen fibre product `Y' ×_Y X` and its projection to `X`.

## Implementation notes

Stacks 0EPN states the base change `g : Y' ⟶ Y` as a morphism of schemes; here `g` is an
arbitrary morphism of algebraic spaces. Likewise the fibre product `X' = Y' ×_Y X` and its
projection `g' : X' ⟶ X` are an arbitrary cartesian square; the chosen fibre product
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` with its square
`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_fiberProduct` is one instance.

## References

* [Stacks Project, Tag 0EPN](https://stacks.math.columbia.edu/tag/0EPN)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 0EPP](https://stacks.math.columbia.edu/tag/0EPP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The scheme case of base change of a relative effective Cartier divisor, on an arbitrary
cartesian square.**  If `I` is an effective Cartier ideal sheaf on `X` whose closed subscheme is
flat over `Y`, then its inverse image along the projection `p : W ⟶ X` of any fibre product of
`f : X ⟶ Y` and `g : Z ⟶ Y` is an effective Cartier ideal sheaf.  This is Stacks 056Q read on a
cartesian square instead of on `pullback g f`. -/
@[ega "IV 21.15.9" "partial"]
theorem isEffectiveCartierDivisor_comap_of_isPullback
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) {p : W ⟶ X} {q : W ⟶ Z}
    (hsq : IsPullback q p g f) (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    [Flat (I.subschemeι ≫ f)] :
    Stacks.Divisors.IsEffectiveCartierDivisor (I.comap p) := by
  have hJ : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (pullback.snd g f)) :=
    isEffectiveCartierDivisor_comap_pullback f g I hI
  have hcomap : (I.comap (pullback.snd g f)).comap hsq.isoPullback.hom = I.comap p := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq.isoPullback_hom_snd]
  rw [← hcomap]
  exact Stacks.Divisors.isPullbackDefined_of_flat hsq.isoPullback.hom _ hJ

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flatness of a closed subspace over the base, read on an étale chart.**  If `D ⟶ Y` is
flat and the ideal sheaf `I` on an étale chart `U` of `X` cuts out the inverse image of `D`,
then the closed subscheme of `I` is flat over the chart `V` of `Y` below `U`. -/
private theorem flat_chart_of_isFlat {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (D : ClosedSubspaces B S hS X.1) (hflat : IsFlat B S hS (D.1.ι ≫ f.hom))
    {U V : BigFppfOver B S hS} {b : yoneda.obj V ⟶ Y.1} {α : U ⟶ V}
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (I : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData)
    {R : BigFppfOver B S hS} {j : R ⟶ U}
    (e : (BigFppfOver.toScheme B S hS).obj R ≅ I.subscheme)
    (hsub : (BigFppfOver.toScheme B S hS).map j = e.hom ≫ I.subschemeι)
    {d : yoneda.obj R ⟶ D.1.toFunctor} (hd : d ≫ D.1.ι ≫ f.hom = yoneda.map (j ≫ α) ≫ b)
    (hdEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf d) :
    Flat (I.subschemeι ≫ (BigFppfOver.toScheme B S hS).map α) := by
  have hRflat : Flat ((BigFppfOver.toScheme B S hS).map (j ≫ α)) :=
    hflat R V d b (j ≫ α) hdEtale hb hd.symm
  rw [Functor.map_comp, hsub, Category.assoc] at hRflat
  have _ : Flat e.inv := inferInstance
  have _ : Flat (e.hom ≫ I.subschemeι ≫ (BigFppfOver.toScheme B S hS).map α) := hRflat
  have hfinal : Flat (e.inv ≫ e.hom ≫ I.subschemeι ≫
      (BigFppfOver.toScheme B S hS).map α) := inferInstance
  rwa [Iso.inv_hom_id_assoc] at hfinal

/-- **The range of a base change of a morphism of representables** is the preimage of its
range along the other projection. -/
private theorem range_yoneda_pullback_snd {C : Type*} [Category C] [HasPullbacks C]
    {R U W : C} (j : R ⟶ U) (p : W ⟶ U) :
    Subfunctor.range (yoneda.map (pullback.snd j p)) =
      (Subfunctor.range (yoneda.map j)).preimage (yoneda.map p) := by
  refine Subfunctor.ext (funext fun V => Set.ext fun x => ?_)
  show (∃ z : V.unop ⟶ pullback j p, z ≫ pullback.snd j p = x) ↔
    (∃ y : V.unop ⟶ R, y ≫ j = x ≫ p)
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z ≫ pullback.fst j p, ?_⟩
    simpa only [Category.assoc] using
      congrArg (fun t => z ≫ t) (pullback.condition (f := j) (g := p))
  · rintro ⟨y, hy⟩
    exact ⟨pullback.lift y x hy, pullback.lift_snd _ _ _⟩

/-- **A scheme-theoretic presentation of the inverse image of a closed subspace on an étale
chart is itself an étale chart of the subspace.**  If `j : R ⟶ U` has range the inverse image
of `D` on an étale chart `a : U ⟶ X`, the induced morphism `R ⟶ D` is étale. -/
private theorem presheafEtale_toClosedSubspace {X : AlgebraicSpaces B S hS}
    (D : ClosedSubspaces B S hS X.1) {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X.1)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {R : BigFppfOver B S hS} (j : R ⟶ U) [Mono (yoneda.map j)]
    (hpre : D.1.preimage a = Subfunctor.range (yoneda.map j)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (Subfunctor.lift (yoneda.map j) (G := D.1.preimage a) (by rw [hpre]) ≫
          D.1.fromPreimage a) := by
  set T := BigFppfOver.toScheme B S hS with hT
  set Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T with hQ
  have _ : Q.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have _ : Q.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have _ : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  have _ : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  have hle : Subfunctor.range (yoneda.map j) ≤ D.1.preimage a := by rw [hpre]
  have hEq := congrArg (fun Z : Subfunctor (yoneda.obj U) => Z.toFunctor) hpre.symm
  set eR : yoneda.obj R ≅ (D.1.preimage a).toFunctor :=
    (asIso (Subfunctor.toRange (yoneda.map j))).trans (eqToIso hEq) with heR
  have hrange : eR.hom ≫ (D.1.preimage a).ι = yoneda.map j := by
    simp only [heR, Iso.trans_hom, eqToIso.hom, asIso_hom, Category.assoc,
      subfunctor_eqToHom_ι hpre.symm, Subfunctor.toRange_ι]
  have hbase : Q.presheaf (D.1.fromPreimage a) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (Subfunctor.isPullback_preimage a D.1).flip ha
  have hiso : Q.presheaf eR.hom := by
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda eR.hom, ?_⟩
    intro A C _ fst snd sq
    have _ : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
    have _ : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
    have _ : IsIso (T.map snd) := inferInstance
    exact (inferInstance : Etale (T.map snd))
  have hlift : eR.hom = Subfunctor.lift (yoneda.map j) hle :=
    (cancel_mono (D.1.preimage a).ι).mp (by rw [hrange, Subfunctor.lift_ι])
  rw [← hlift]
  exact MorphismProperty.comp_mem Q.presheaf _ _ hiso hbase

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces and let `D ⊆ X` be an effective Cartier
divisor whose structure morphism `D ⟶ Y` is flat.  Then for every morphism `g : Y' ⟶ Y` and
every fibre product square exhibiting `X'` as `Y' ×_Y X`, the pullback of `D` along the
projection `g' : X' ⟶ X` is defined: the inverse image of `D` on `X'` is again an effective
Cartier divisor.

Stacks 0EPN asks `g` to be a morphism of schemes and `X'` to be the chosen fibre product; it is
stated here for an arbitrary morphism of algebraic spaces and an arbitrary cartesian square. -/
@[stacks 0EPN]
theorem isPullbackDefined_of_isPullback_of_isFlat {X Y Y' X' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) {f' : X' ⟶ Y'} {g' : X' ⟶ X} (hsq : IsPullback f' g' g f)
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
    (hflat : IsFlat B S hS (D.1.ι ≫ f.hom)) :
    IsPullbackDefined B S hS g' D := by
  classical
  set T := BigFppfOver.toScheme B S hS with hT
  set QEtale := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
    with hQE
  set QSurj := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u}) T
    with hQS
  have _ : QEtale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have _ : QSurj.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have _ : QEtale.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have _ : QSurj.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition
  have hDall : HasEffectiveCartierEtalePullbacks B S hS X D :=
    hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X D hD
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.property.exists_atlas
  obtain ⟨U, a, α, hcomm, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.property Y.property f.hom V b
      hbSurj hbEtale
  obtain ⟨I, R, j, e, hI, hsub, hpre⟩ :=
    hDall U a (isEtale_of_presheaf_etale B S hS haEtale)
  set d : yoneda.obj R ⟶ D.1.toFunctor :=
    Subfunctor.lift (yoneda.map j) (G := D.1.preimage a) (by rw [hpre]) ≫ D.1.fromPreimage a
    with hdDef
  have hjT : Mono (T.map j) := by rw [hsub]; infer_instance
  have hjSite : Mono j := T.mono_of_mono_map hjT
  have hjY : Mono (yoneda.map j) := inferInstance
  have hdEtale : QEtale.presheaf d :=
    presheafEtale_toClosedSubspace B S hS D a haEtale j hpre
  have hdι : d ≫ D.1.ι = yoneda.map j ≫ a := by
    rw [hdDef, Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc,
      Subfunctor.lift_ι]
  have hd : d ≫ D.1.ι ≫ f.hom = yoneda.map (j ≫ α) ≫ b := by
    rw [← Category.assoc, hdι, Functor.map_comp, Category.assoc, Category.assoc, hcomm]
  have hflatChart : Flat (I.subschemeι ≫ T.map α) :=
    flat_chart_of_isFlat B S hS f D hflat hbEtale I e hsub hd hdEtale
  set Vsp : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ with hVsp
  set bsp : Vsp ⟶ Y := ObjectProperty.homMk b with hbsp
  set Z := AlgebraicSpaces.fiberProduct B S hS g bsp with hZ
  set zY : Z ⟶ Y' := ObjectProperty.homMk (pullback.fst g.hom bsp.hom) with hzY
  set zV : Z ⟶ Vsp := ObjectProperty.homMk (pullback.snd g.hom bsp.hom) with hzV
  have hZpb : IsPullback zY zV g bsp := AlgebraicSpaces.isPullback_fiberProduct B S hS g bsp
  obtain ⟨V', r, hrSurj, hrEtale⟩ := Z.property.exists_atlas
  set rSp : AlgebraicSpaces B S hS := ⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩
    with hrSp
  set rFull : rSp ⟶ Z := ObjectProperty.homMk r with hrFull
  set β : V' ⟶ V := yoneda.preimage (r ≫ zV.hom) with hβdef
  have hmapβ : yoneda.map β = r ≫ zV.hom := by rw [hβdef, Functor.map_preimage]
  have hβ : (r ≫ zY.hom) ≫ g.hom = yoneda.map β ≫ b := by
    have h0 : rFull ≫ zY ≫ g = rFull ≫ zV ≫ bsp := by rw [hZpb.w]
    have h1 := congrArg (fun k : rSp ⟶ Y => k.hom) h0
    simp only [ObjectProperty.FullSubcategory.comp_hom, hrFull, hbsp,
      ObjectProperty.homMk_hom] at h1
    rw [Category.assoc, h1, hmapβ, Category.assoc]
  set W := pullback β α with hW
  set p := pullback.snd β α with hp
  set q := pullback.fst β α with hq
  have hsqSite : IsPullback q p β α := IsPullback.of_hasPullback β α
  have hWcartier : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap (T.map p)) := by
    have _ : Flat (I.subschemeι ≫ T.map α) := hflatChart
    exact isEffectiveCartierDivisor_comap_of_isPullback (T.map α) (T.map β)
      (hsqSite.map T) I hI
  set Usp : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ with hUsp
  set αsp : Usp ⟶ Vsp := ObjectProperty.homMk (yoneda.map α) with hαsp
  set aSp : Usp ⟶ X := ObjectProperty.homMk a with haSp
  set P := AlgebraicSpaces.fiberProduct B S hS zV αsp with hP
  set pZ : P ⟶ Z := ObjectProperty.homMk (pullback.fst zV.hom αsp.hom) with hpZ
  set pU : P ⟶ Usp := ObjectProperty.homMk (pullback.snd zV.hom αsp.hom) with hpU
  have hPpb : IsPullback pZ pU zV αsp := AlgebraicSpaces.isPullback_fiberProduct B S hS zV αsp
  have hrel : αsp ≫ bsp = aSp ≫ f := ObjectProperty.hom_ext _ hcomm.symm
  have hcompatP : pZ ≫ zY ≫ g = pU ≫ aSp ≫ f := by
    have h1 : pZ ≫ zY ≫ g = (pZ ≫ zV) ≫ bsp := by
      rw [hZpb.w, Category.assoc]
    have h2 : (pU ≫ αsp) ≫ bsp = pU ≫ aSp ≫ f := by rw [Category.assoc, hrel]
    rw [h1, hPpb.w, h2]
  set m : P ⟶ X' := hsq.lift (pZ ≫ zY) (pU ≫ aSp) hcompatP with hm
  have hmY : m ≫ f' = pZ ≫ zY := hsq.lift_fst _ _ _
  have hmX : m ≫ g' = pU ≫ aSp := hsq.lift_snd _ _ _
  have hPX : IsPullback m pU g' aSp := by
    have hPY : IsPullback (pZ ≫ zY) pU g (aSp ≫ f) := by
      rw [← hrel]; exact hPpb.paste_horiz hZpb
    set E := AlgebraicSpaces.fiberProduct B S hS g' aSp with hE
    set eX : E ⟶ X' := ObjectProperty.homMk (pullback.fst g'.hom aSp.hom) with heX
    set eU : E ⟶ Usp := ObjectProperty.homMk (pullback.snd g'.hom aSp.hom) with heU
    have hEpb : IsPullback eX eU g' aSp := AlgebraicSpaces.isPullback_fiberProduct B S hS g' aSp
    have hEcompat : eX ≫ f' ≫ g = eU ≫ αsp ≫ bsp := by
      have h1 : eX ≫ f' ≫ g = (eX ≫ g') ≫ f := by rw [hsq.w, Category.assoc]
      have h2 : (eU ≫ aSp) ≫ f = eU ≫ αsp ≫ bsp := by rw [Category.assoc, hrel]
      rw [h1, hEpb.w, h2]
    set eZ : E ⟶ Z := hZpb.lift (eX ≫ f') (eU ≫ αsp) hEcompat with heZ
    have heZV : eZ ≫ zV = eU ≫ αsp := hZpb.lift_snd _ _ _
    have heZY : eZ ≫ zY = eX ≫ f' := hZpb.lift_fst _ _ _
    set k : E ⟶ P := hPpb.lift eZ eU heZV with hk
    have hkZ : k ≫ pZ = eZ := hPpb.lift_fst _ _ _
    have hkU : k ≫ pU = eU := hPpb.lift_snd _ _ _
    have hk1 : k ≫ pZ ≫ zY = eX ≫ f' := by rw [← Category.assoc, hkZ, heZY]
    have hkM : k ≫ m = eX := by
      refine hsq.hom_ext ?_ ?_
      · rw [Category.assoc, hmY, hk1]
      · rw [Category.assoc, hmX, ← Category.assoc, hkU, hEpb.w]
    have hkpb : IsPullback k eU pU (𝟙 Usp) :=
      IsPullback.paste_twist_right hsq hPY aSp (𝟙 Usp) (by simp) eX eU hEpb
        (t := k) hk1 (by simpa using hkU)
    have _ : IsIso k := hkpb.isIso_fst_of_isIso
    exact hEpb.of_iso (asIso k) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simpa using hkM.symm) (by simpa using hkU.symm) (by simp) (by simp)
  set Wsp : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ with hWsp
  set qsp : Wsp ⟶ rSp := ObjectProperty.homMk (yoneda.map q) with hqsp
  set psp : Wsp ⟶ Usp := ObjectProperty.homMk (yoneda.map p) with hpsp
  set βsp : rSp ⟶ Vsp := ObjectProperty.homMk (yoneda.map β) with hβsp
  have hWsq : IsPullback psp qsp αsp βsp :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      (by simpa only [hpsp, hqsp, hαsp, hβsp, ObjectProperty.ι_map,
        ObjectProperty.homMk_hom] using (hsqSite.map yoneda).flip)
  have hβspEq : βsp = rFull ≫ zV := ObjectProperty.hom_ext _ (by
    simpa only [hβsp, hrFull, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom] using hmapβ)
  set wP : Wsp ⟶ P := hPpb.lift (qsp ≫ rFull) psp (by
    rw [Category.assoc, ← hβspEq]; exact hWsq.w.symm) with hwP
  have hwPZ : wP ≫ pZ = qsp ≫ rFull := hPpb.lift_fst _ _ _
  have hwPU : wP ≫ pU = psp := hPpb.lift_snd _ _ _
  have hWP : IsPullback wP qsp pZ rFull :=
    IsPullback.paste_twist_right hWsq hPpb.flip (𝟙 rSp) rFull
      (by rw [Category.id_comp, hβspEq]) (𝟙 Wsp) qsp IsPullback.of_id_fst (t := wP)
      (by simpa using hwPU) (by simpa using hwPZ)
  have hQ : ∀ (Q : MorphismProperty (BigFppfOver B S hS)) [Q.IsStableUnderBaseChange]
      [Q.IsStableUnderComposition], Q.presheaf a → Q.presheaf r → Q.presheaf (wP ≫ m).hom := by
    intro Q _ _ ha hr
    have _ : Q.presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange Q
    have _ : Q.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition Q
    exact MorphismProperty.comp_mem Q.presheaf _ _
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (by simpa only [hrFull, ObjectProperty.ι_map, ObjectProperty.homMk_hom] using
          hWP.flip.map (ObjectProperty.ι _)) hr)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (by simpa only [haSp, ObjectProperty.ι_map, ObjectProperty.homMk_hom] using
          hPX.flip.map (ObjectProperty.ι _)) ha)
  set t : yoneda.obj W ⟶ X'.1 := (wP ≫ m).hom with htDef
  have htEtale : QEtale.presheaf t := hQ QEtale haEtale hrEtale
  have htSurj : QSurj.presheaf t := hQ QSurj haSurj hrSurj
  set D' : ClosedSubspaces B S hS X'.1 :=
    ⟨D.1.preimage g'.hom,
      isClosedSubspace_preimage B S hS g'.hom D.1 X.2 X'.2 D.2⟩ with hD'
  have hRpb : IsPullback (T.map (pullback.fst j p) ≫ e.hom) (T.map (pullback.snd j p))
      I.subschemeι (T.map p) :=
    ((IsPullback.of_hasPullback j p).map T).of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)
      (by simp only [Iso.refl_hom, Category.comp_id]; exact hsub) (by simp)
  set eW : T.obj (pullback j p) ≅ (I.comap (T.map p)).subscheme :=
    hRpb.isoPullback ≪≫ pullbackSymmetry I.subschemeι (T.map p) ≪≫
      (I.comapIso (T.map p)).symm with heW
  have hsubW : T.map (pullback.snd j p) = eW.hom ≫ (I.comap (T.map p)).subschemeι := by
    rw [heW]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Scheme.IdealSheafData.comapIso_inv_subschemeι, pullbackSymmetry_hom_comp_fst]
    exact hRpb.isoPullback_hom_snd.symm
  have htX : t ≫ g'.hom = yoneda.map p ≫ a := by
    have h0 : (wP ≫ m) ≫ g' = psp ≫ aSp := by
      rw [Category.assoc, hmX, ← Category.assoc, hwPU]
    simpa only [htDef, ObjectProperty.FullSubcategory.comp_hom, hpsp, haSp,
      ObjectProperty.homMk_hom] using congrArg (fun k : Wsp ⟶ X => k.hom) h0
  have hpreW : D'.1.preimage t = Subfunctor.range (yoneda.map (pullback.snd j p)) := by
    rw [hD', ← Subfunctor.preimage_comp D.1 t g'.hom, htX, Subfunctor.preimage_comp, hpre,
      range_yoneda_pullback_snd]
  exact isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS X' D'
    ⟨W, t, isEtale_of_presheaf_etale B S hS htEtale,
      (presheafSurjective_iff_isSurjective_yoneda B S hS X'.1 X'.property W t).mp htSurj,
      ⟨I.comap (T.map p), pullback j p, pullback.snd j p, eW, hWcartier, hsubW, hpreW⟩⟩

/-- **Stacks 0EPN on the chosen fibre product.**  If `D ⊆ X` is an effective Cartier divisor
with `D ⟶ Y` flat, then for every `g : Y' ⟶ Y` the pullback of `D` along the projection
`Y' ×_Y X ⟶ X` is defined. -/
theorem isPullbackDefined_fibreProduct_snd_of_isFlat {X Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D)
    (hflat : IsFlat B S hS (D.1.ι ≫ f.hom)) :
    IsPullbackDefined B S hS
      (ObjectProperty.homMk (pullback.snd g.hom f.hom) :
        AlgebraicSpaces.fiberProduct B S hS g f ⟶ X) D :=
  isPullbackDefined_of_isPullback_of_isFlat B S hS f g
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g f) D hD hflat

end Space

end AlgebraicGeometry

end
