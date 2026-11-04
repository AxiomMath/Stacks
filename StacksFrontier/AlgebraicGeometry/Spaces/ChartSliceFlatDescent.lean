module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GivenSectionsSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceChartFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspaceOpenRestriction

/-!
# The last two steps of the flatness half of Stacks 06LW: slicing a chart and descending

Let `g : X ⟶ Y` be a flat, locally finitely presented morphism of algebraic spaces over a
scheme `S` contained in a big fppf site and let `f₁, …, f_r ∈ Γ(X, 𝒪_X)`.  The flatness half of
Stacks 06LW asserts that if the `f_i` have regular images in the étale local ring of a geometric
fibre of `g`, then after replacing `X` by an open subspace the closed subspace
`V(f₁, …, f_r) ⊆ X` is flat over `Y`.  The source proves it in five steps: enlarge the field of
the fibre point, choose charts, descend the regular sequence to the Zariski local ring of a chart
of the fibre, apply the scheme-level slicing lemma Stacks 06LI there, and descend flatness back
up along a surjective étale chart.

**This file performs the last two of those steps, and only them.**  It takes the regular sequence
already in the local ring of the scheme-theoretic fibre of a chart — which is where the source's
third step leaves it — and produces the open subspace of `X` and flatness of
`V(f₁, …, f_r) ∩ X' ⟶ Y`.  No `@[stacks 06LW]` attribute is claimed: the first three steps are
not performed here and the hypothesis consumed below is not the fibre hypothesis of Stacks 06LW
but its chartwise consequence; see the implementation notes.

## Main results

* `Stacks.AlgebraicGeometry.exists_affineOpens_flat_zeroScheme_of_isRegular_fiber`: Stacks 06LI
  for the given global functions with its neighbourhood returned as a *Zariski open* of the
  source rather than as an abstract scheme with an open immersion.
* `AlgebraicGeometry.Space.unitSection_eval_chartMap` and
  `AlgebraicGeometry.Space.unitSection_eval_chartOpen`: the value of a global regular function on
  a smaller étale chart is the pullback of its value on the larger one, and for a Zariski open of
  a chart that pullback is restriction of global sections along the open immersion.
* `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq'`: the unconditional form of
  `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_inf_of_flat_zeroScheme`
  : **the descent step**, that `V(f₁, …, f_r) ∩ X' ⟶ Y` is flat as soon as the zero scheme of the
  restricted functions on one affine étale chart `U₀` of `X` is flat over a chart of `Y`, where
  `X'` is the open subspace swept out by `U₀`.
* `Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_chartFiber`
  : **the slicing step followed by the descent step**, from the regular sequence in the local ring
  of the scheme-theoretic fibre of the chart.

## Implementation notes

The descent step is the one that needs a *surjective* étale chart of the open subspace, and that
is what replacing `X` by an open subspace buys: Stacks 06NF,
`AlgebraicGeometry.Space.exists_isOpenSubspace_etaleImage`, makes the chart `U₀ ⟶ X` a surjective
étale chart `U₀ ⟶ X'` of the open subspace it sweeps out.  Over that chart,
`AlgebraicGeometry.Space.isFlat_ι_vanishingSubfunctor_comp_of_zeroScheme` — condition (8) of
Stacks 03MM at the chart of the closed subspace base changed from `U₀` — reads flatness of
`V(f₁, …, f_r) ∩ X' ⟶ Y` off flatness of the scheme-theoretic zero scheme over the chart of `Y`.
Passing between `V(f₁, …, f_r) ∩ X'`, which is the inverse image of Stacks 083Q, and the zero
locus of the restricted functions computed inside `X'` is
`AlgebraicGeometry.Space.vanishingSubfunctor_restrict_eq_preimage`, whose chartwise hypothesis is
discharged from the surjectivity half of Stacks 03MB through
`AlgebraicGeometry.Space.exists_vanishingSubfunctor_eq`.

The slicing step applies Stacks 06LI to the morphism of schemes `U ⟶ V` underlying the chart
square.  Flatness and local finite presentation of that morphism are immediate: both properties
of a morphism of algebraic spaces *are* the every-chart conditions of Stacks 03ML and 03XP, so
the square itself supplies them.  Stacks 06LI then returns an affine open neighbourhood of the
chosen point over which the zero scheme is flat over `V`, and
`Stacks.AlgebraicGeometry.exists_affineOpens_flat_zeroScheme_of_isRegular_fiber` returns it as a
Zariski open `O` of the chart scheme, which is what makes it an object of the site again —
`AlgebraicGeometry.Space.chartOpenOver` — and hence an étale chart of `X` by
`AlgebraicGeometry.Space.chartOpen_isEtaleChart`.  The conversion from the open-immersion form is
along `AlgebraicGeometry.Scheme.Hom.isoOpensRange`, the zero scheme on the source being the
pullback of the zero scheme on the open along that isomorphism by
`Stacks.AlgebraicGeometry.comap_ofIdealTop`.

The restriction of the given functions to the smaller chart is the structure sheaf's own
restriction map, and that it is pullback of global sections along the underlying morphism of
schemes is `AlgebraicGeometry.Space.unitSection_eval_chartMap`; the ideal the zero scheme is cut
out by is therefore the one Stacks 06LI delivers.

## Where the earlier steps of Stacks 06LW are

The three earlier steps of the source's proof are not performed here, and all three are about the
*fibre*, which this file never mentions.  All three exist elsewhere.

The third step — the descent of the regular sequence from the étale local ring of the fibre to
the Zariski local ring `𝒪_{U_v, u}` of the chart of the fibre — is
`AlgebraicGeometry.Space.isRegular_chartFiber_of_isRegular_etaleLocalRing` in
`StacksFrontier/AlgebraicGeometry/Spaces/FibreChartRegularityDescent.lean`, which feeds
`AlgebraicGeometry.Space.isRegular_map_etaleLocalRing_iff_fiber_extendResidueField` with the
commuting square of local rings of Stacks 05VU,
`AlgebraicGeometry.Space.etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing`, at the chart
produced by `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_fiberBaseChange`.  That
lemma returns the chart up to an isomorphism of its scheme together with the morphism of the site
from the chart of the fibre to the chart `U` of `X`, its commuting square and the compatibility of
the isomorphism with it, which is exactly what the square of Stacks 05VU consumes.  Composing the
third step with the two steps proved here gives the flatness half of Stacks 06LW for a fibre over
a field *already* factoring through the chart of `Y`, which is
`Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_fiber_factorThroughChart` in
`StacksFrontier/AlgebraicGeometry/Spaces/FibreSliceFlatness.lean`.

The *first two* steps, which is why that factorisation is carried as a hypothesis there, are run
in `StacksFrontier/AlgebraicGeometry/Spaces/FibreSliceFlatnessEnlargement.lean`: the enlargement of
the field `k` of the point of `|F|` to one over which it becomes a section of `F ⟶ Spec k` whose
field spectrum factors through the chart `V ⟶ Y` (Stacks 0488 and
`AlgebraicGeometry.Space.exists_geometricPoint_factorThroughChart`), and the
transport of the regular sequence from `𝒪_{F, z̄}` to the étale local ring of the base-changed
fibre `F' = F ×_{Spec k} Spec k'` at a point above `z`
(`AlgebraicGeometry.Space.isRegular_map_etaleLocalRingMap_comp_iff_of_isFlatAt` against the flat
projection, together with
`AlgebraicGeometry.Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates` for the change
of geometric point).  The two pieces that assembly needs are the geometric point of `F'` above
the enlarged point of `F` (`AlgebraicGeometry.Space.exists_geometricPoint_pullback_fst_eq`) and
the rewriting of the regularity hypothesis as a statement about germs on one chart of `F`, through
the chart refinement `AlgebraicGeometry.Space.exists_compatible_chart_lift`, which is how that
last lemma is proved.  The flatness half of Stacks 06LW is
`Space.exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_geometricFiber`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06NF](https://stacks.math.columbia.edu/tag/06NF)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.AlgebraicGeometry

/-- **Stacks 06LI for the given global functions, with the neighbourhood as a Zariski open of
the source.**  Let `f : X ⟶ T` be locally of finite presentation and flat at `x`, and let
`b₁, …, b_r ∈ Γ(X, 𝒪_X)` have germs at `x` forming a regular sequence in the local ring of the
fibre through `x`.  Then `x` has an affine Zariski open neighbourhood `O ⊆ X` over which the
zero scheme of the restrictions `b_i|_O` is flat over `T`.

`Stacks.AlgebraicGeometry.exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber` returns
the neighbourhood as a scheme with an open immersion into `X`; its range is the open wanted here,
and the two zero schemes are identified by the comparison
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` for the pullback of the ideal sheaf along
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`, whose other projection is a base change of an
isomorphism and so cancels.

The open form is what makes the neighbourhood an object of the big fppf site again, which is what
a chart of an algebraic space has to be.  No `@[stacks]` attribute is claimed: Stacks 06LI is
registered on `Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_flat_of_isRegular_fiber`
and this is its conclusion re-expressed. -/
theorem exists_affineOpens_flat_zeroScheme_of_isRegular_fiber
    {X T : Scheme.{u}} (f : X ⟶ T) (x : X) {r : ℕ} (b : Fin r → Γ(X, ⊤))
    [LocallyOfFinitePresentation f]
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hregular : RingTheory.Sequence.IsRegular
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun i : Fin r =>
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((f.fiberι_asFiber x).symm ▸ (X.presheaf.germ ⊤ x trivial (b i))))) :
    ∃ O : X.Opens, IsAffine O.toScheme ∧ x ∈ O ∧
      Flat ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => O.ι.appTop (b i)))).subschemeι ≫ O.ι ≫ f) := by
  obtain ⟨W, j, hj, w, hWaff, hjw, hflatW⟩ :=
    exists_affineOpenImmersion_flat_zeroScheme_of_isRegular_fiber f x b hflat hregular
  have := hj
  have := hWaff
  set O : X.Opens := j.opensRange with hO
  set e : W ≅ O.toScheme := j.isoOpensRange with he
  have hje : e.hom ≫ O.ι = j := j.isoOpensRange_hom_ι
  have : IsAffine O.toScheme := IsAffine.of_isIso e.inv
  set J : O.toScheme.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop
      (Ideal.ofList (List.ofFn fun i => O.ι.appTop (b i))) with hJ
  have happ : ∀ i, j.appTop (b i) = e.hom.appTop.hom (O.ι.appTop (b i)) := fun i => by
    rw [← hje, Scheme.Hom.comp_appTop]
    rfl
  have hideal : Scheme.IdealSheafData.ofIdealTop
      (Ideal.ofList (List.ofFn fun i => j.appTop (b i))) = J.comap e.hom := by
    rw [hJ, comap_ofIdealTop e.hom _, Ideal.map_ofList]
    refine congrArg (Scheme.IdealSheafData.ofIdealTop ∘ Ideal.ofList) ?_
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => happ i)
  have hcomm : (J.comap e.hom).subschemeι ≫ j ≫ f =
      ((J.comapIso e.hom).hom ≫ pullback.snd e.hom J.subschemeι) ≫
        (J.subschemeι ≫ O.ι ≫ f) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst J e.hom, ← hje]
    simp only [Category.assoc]
    rw [← Category.assoc (pullback.fst e.hom J.subschemeι) e.hom, pullback.condition]
    simp only [Category.assoc]
  let : MorphismProperty.RespectsIso (@AlgebraicGeometry.Flat.{u}) :=
    AlgebraicGeometry.Flat.isStableUnderBaseChange.respectsIso
  rw [hideal, hcomm] at hflatW
  refine ⟨O, inferInstance, hjw ▸ ⟨w, rfl⟩, ?_⟩
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.Flat.{u})
    ((J.comapIso e.hom).hom ≫ pullback.snd e.hom J.subschemeι) _).1 hflatW.1

end Stacks.AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The value of a global regular function on a smaller étale chart is the pullback of its
value on the larger one.**  Restriction in the structure sheaf of the small étale site along a
morphism of charts is pullback of global sections along the underlying morphism of schemes. -/
theorem unitSection_eval_chartMap (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    {A U : SmallEtale B S hS X.1} (m : A ⟶ U) (i : Fin r) :
    (f i).eval (op A) =
      ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map m)).appTop
        ((f i).eval (op U)) := by
  refine ((f i).property m.op).symm.trans ?_
  change ((structureRingSheaf B S hS X).obj.map m.op).hom ((f i).eval (op U)) = _
  rfl

/-- **The defining ideal of `V(f₁, …, f_r)` on an affine étale chart is the ideal generated by
the restrictions of the functions**, with no hypothesis.  This is
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq` with its closed subspace supplied
by `AlgebraicGeometry.Space.exists_vanishingSubfunctor_eq`, that is by the surjectivity half of
Stacks 03MB. -/
theorem definingIdealAt_vanishingSubspace_eq' (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toSchemes B S hS X.1).obj W).1) :
    definingIdealAt B S hS X (vanishingSubspace B S hS X f) (op W) =
      vanishingIdealAt B S hS X f W := by
  obtain ⟨Z, -, hZid⟩ := exists_vanishingSubfunctor_eq B S hS X f
  refine definingIdealAt_vanishingSubspace_eq B S hS X f Z (fun W' hW' => ?_) W hW
  rw [← definingIdealSheaf_obj B S hS X Z (op W'), hZid,
    vanishingIdealSheaf_obj_of_isAffine B S hS X f W' hW']

/-- **The flatness half of the conclusion of Stacks 06LW, read off one affine étale chart.**
Let `g : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `f₁, …, f_r ∈ Γ(X, 𝒪_X)`, let
`φ : U₀ ⟶ X` be an étale chart of `X` whose scheme is affine, let `q : V ⟶ Y` be an étale chart
of the target and let `d : U₀ ⟶ V` be a morphism of the site over `g`.  If the scheme-theoretic
zero scheme of the restrictions `f₁|_{U₀}, …, f_r|_{U₀}` is flat over `V`, then the open
subspace `X' ⊆ X` swept out by `φ` has `V(f₁, …, f_r) ∩ X' ⟶ Y` flat.

This is the last step of the proof of the flatness half of Stacks 06LW: the open subspace is
Stacks 06NF, `AlgebraicGeometry.Space.exists_isOpenSubspace_etaleImage`, which turns `φ` into a
*surjective* étale chart of `X'`, and the descent of flatness along that chart is
`AlgebraicGeometry.Space.isFlat_ι_vanishingSubfunctor_comp_of_zeroScheme`, condition (8) of
Stacks 03MM at the chart of `V(f₁, …, f_r) ∩ X'` base changed from it. -/
theorem exists_isOpenSubspace_isFlat_vanishingSubfunctor_inf_of_flat_zeroScheme
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U₀ : BigFppfOver B S hS) (φ : yoneda.obj U₀ ⟶ X.1)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hU₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1) (hq : IsEtale B S hS q)
    (d : U₀ ⟶ V) (hcomm : φ ≫ g = yoneda.map d ≫ q)
    (L : List Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤))
    (hL : L = List.ofFn fun i =>
      (f i).eval (op (⟨CostructuredArrow.mk φ, hφ⟩ : SmallEtale B S hS X.1)))
    (hflat : AlgebraicGeometry.Flat
      ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList L)).subschemeι ≫
        (BigFppfOver.toScheme B S hS).map d)) :
    ∃ (W : Subfunctor X.1) (_ : IsOpenSubspace B S hS W),
      Set.range (pointsMap B S hS W.toFunctor W.ι) =
          Set.range (pointsMap B S hS (yoneda.obj U₀) φ) ∧
        IsFlat B S hS
          (((vanishingSubfunctor B S hS X f).preimage W.ι).ι ≫ W.ι ≫ g) := by
  obtain ⟨W, ψ, hWopen, hψφ, hψsurj, hψetale, hrange⟩ :=
    exists_isOpenSubspace_etaleImage B S hS X.2 U₀ φ hφ
  subst hL
  subst hψφ
  let W' : AlgebraicSpaces B S hS := ⟨W.toFunctor, hWopen.1⟩
  let ι : W' ⟶ X := ObjectProperty.homMk W.ι
  have hιetale : IsEtale B S hS ι.hom := isEtale_of_isOpenImmersion B S hS hWopen.2
  have hmain := isFlat_ι_vanishingSubfunctor_comp_of_zeroScheme B S hS W' Y (ι.hom ≫ g)
    (fun i => unitSectionsRestrict B S hS ι hιetale (f i))
    (⟨CostructuredArrow.mk ψ, hψetale⟩ : SmallEtale B S hS W.toFunctor)
    hU₀aff
    ((surjective_iff_surjective_pointsMap B S hS W.toFunctor hWopen.1 U₀ ψ).1 hψsurj)
    V q hq d (by simpa only [ι, ObjectProperty.homMk_hom, Category.assoc,
      CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self] using hcomm) hflat
  refine ⟨W, hWopen, hrange, ?_⟩
  rw [show (W.ι : W.toFunctor ⟶ X.1) = ι.hom from rfl,
    ← vanishingSubfunctor_restrict_eq_preimage B S hS ι hιetale f
      (definingIdealAt_vanishingSubspace_eq' B S hS X f)]
  exact hmain

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.chartOpensHom` is the inclusion
of the Zariski open. -/
theorem toScheme_map_chartOpensHom (X : AlgebraicSpaces B S hS) (A : SmallEtale B S hS X.1)
    (O : (etaleChartScheme B S hS A).Opens) :
    (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (chartOpensHom B S hS X A O)) = O.ι := rfl

/-- The morphism of schemes underlying the inclusion of a Zariski open of an étale chart is the
inclusion of the open subscheme. -/
theorem toScheme_map_chartOpenOverι {Xp : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A : SmallEtale B S hS Xp) (O : (etaleChartScheme B S hS A).Opens) :
    (BigFppfOver.toScheme B S hS).map (chartOpenOverι B S hS A O) = O.ι := rfl

/-- **The value of a global regular function on the chart cut out by a Zariski open of a chart
is its restriction to that open.** -/
theorem unitSection_eval_chartOpen (X : AlgebraicSpaces B S hS) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (A : SmallEtale B S hS X.1) (O : (etaleChartScheme B S hS A).Opens) (i : Fin r) :
    (f i).eval (op (⟨CostructuredArrow.mk (yoneda.map (chartOpenOverι B S hS A O) ≫ A.1.hom),
        chartOpen_isEtaleChart B S hS A O⟩ : SmallEtale B S hS X.1)) =
      O.ι.appTop ((f i).eval (op A)) := by
  have h := unitSection_eval_chartMap B S hS X f (chartOpensHom B S hS X A O) i
  rw [toScheme_map_chartOpensHom] at h
  exact h

/-- **The flatness half of the conclusion of Stacks 06LW.**  Let `g : X ⟶ Y` be a flat,
locally finitely presented morphism of algebraic spaces over `S`, let
`f₁, …, f_r ∈ Γ(X, 𝒪_X)`, let `U` be an étale chart of `X` lying over an étale chart `V` of `Y`
through a morphism `c` of the site, and let `u` be a point of the scheme of `U` at which the
germs of the `f_i` become a regular sequence in the local ring of the scheme-theoretic fibre of
`U ⟶ V` through `u`.  Then there is an open subspace `W ⊆ X` containing the image of `u` with
`V(f₁, …, f_r) ∩ W ⟶ Y` flat.

This is the final step of the proof of Stacks 06LW, the one it performs after descending the
regular sequence to the local ring of the fibre chart: the scheme-level slicing lemma
Stacks 06LI is applied to the morphism of schemes `U ⟶ V`, which is flat at `u` and locally of
finite presentation because `g` is, and the affine open of the chart it returns produces the
open subspace of `X` and the surjective étale chart of it along which flatness descends. -/
theorem exists_isOpenSubspace_isFlat_vanishingSubfunctor_of_isRegular_chartFiber
    (X Y : AlgebraicSpaces B S hS) (g : X.1 ⟶ Y.1)
    (hgflat : IsFlat B S hS g) (hglfp : IsLocallyOfFinitePresentation B S hS g)
    {r : ℕ} (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (U : SmallEtale B S hS X.1) (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
    (hq : IsEtale B S hS q) (c : (SmallEtale.toOver B S hS X.1).obj U ⟶ V)
    (hcomm : U.1.hom ≫ g = yoneda.map c ≫ q)
    (u : chartScheme U)
    (hreg : RingTheory.Sequence.IsRegular
      ((((BigFppfOver.toScheme B S hS).map c).fiber
        ((BigFppfOver.toScheme B S hS).map c u)).presheaf.stalk
          (((BigFppfOver.toScheme B S hS).map c).asFiber u))
      (List.ofFn fun i : Fin r =>
        ((((BigFppfOver.toScheme B S hS).map c).fiberι
            ((BigFppfOver.toScheme B S hS).map c u)).stalkMap
          (((BigFppfOver.toScheme B S hS).map c).asFiber u)).hom
          (((((BigFppfOver.toScheme B S hS).map c).fiberι_asFiber u).symm ▸
            ((chartScheme U).presheaf.germ ⊤ u trivial ((f i).eval (op U))))))) :
    ∃ (W : Subfunctor X.1) (_ : IsOpenSubspace B S hS W),
      chartSchemeToPoints B S hS X.1 U u ∈
          Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
        IsFlat B S hS
          (((vanishingSubfunctor B S hS X f).preimage W.ι).ι ≫ W.ι ≫ g) := by
  have hqp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q :=
    (isEtale_iff_presheaf_of_yoneda B S hS q).1 hq
  have hlfpc : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map c) :=
    hglfp ((SmallEtale.toOver B S hS X.1).obj U) V U.1.hom q c U.2 hqp hcomm.symm
  have hflatc : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map c) :=
    hgflat ((SmallEtale.toOver B S hS X.1).obj U) V U.1.hom q c U.2 hqp hcomm.symm
  obtain ⟨O, hOaff, hu, hflatO⟩ :=
    Stacks.AlgebraicGeometry.exists_affineOpens_flat_zeroScheme_of_isRegular_fiber
      ((BigFppfOver.toScheme B S hS).map c) u (fun i => (f i).eval (op U))
      ((AlgebraicGeometry.Flat.iff_flat_stalkMap _).mp inferInstance u) hreg
  obtain ⟨W, hWopen, hrange, hflatW⟩ :=
    exists_isOpenSubspace_isFlat_vanishingSubfunctor_inf_of_flat_zeroScheme B S hS X Y g f
      (chartOpenOver B S hS U O)
      (yoneda.map (chartOpenOverι B S hS U O) ≫ U.1.hom)
      (chartOpen_isEtaleChart B S hS U O) hOaff V q hq
      (chartOpenOverι B S hS U O ≫ c)
      (by simp only [Functor.map_comp, Category.assoc, ← hcomm])
      (List.ofFn fun i => O.ι.appTop ((f i).eval (op U)))
      (congrArg List.ofFn
        (funext fun i => (unitSection_eval_chartOpen B S hS X f U O i).symm))
      (by rw [Functor.map_comp, toScheme_map_chartOpenOverι]; exact hflatO)
  refine ⟨W, hWopen, ?_, hflatW⟩
  rw [hrange]
  refine ⟨_, ((chartSchemeToPoints_map B S hS X.1 (chartOpensHom B S hS X U O)
      (⟨u, hu⟩ : chartScheme ((chartOpens B S hS U).obj O))).trans
    (chartSchemeToPoints_eq_pointsMap B S hS X.1 ((chartOpens B S hS U).obj O)
      (⟨u, hu⟩ : chartScheme ((chartOpens B S hS U).obj O)))).symm⟩

end AlgebraicGeometry.Space

end
