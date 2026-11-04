module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiMainTheoremFiniteFactorization

/-!
# Compactifications from Zariski's main theorem

Let `p : P ⟶ Y` be a proper morphism of algebraic spaces over `S`, with `Y` quasi-compact and
quasi-separated, and let `m : U ⟶ P` be a quasi-compact monomorphism which is locally of finite
type. Then `m` is separated and quasi-finite (Stacks 0463), and Zariski's main theorem (Stacks
082K) factors it as a quasi-compact open immersion followed by a finite morphism `Y' ⟶ P`. A
finite morphism is proper (Stacks 04NZ), so `Y' ⟶ P ⟶ Y` is proper (Stacks 04XY) and `U ⊆ Y'`
is a compactification of `m ≫ p`.

Two cases of this are used in the proof of Nagata's compactification theorem for algebraic
spaces.

* If `u : U ⟶ Y` and `t : Y ⟶ T` are such that `u ≫ t` has a compactification `U ⊆ Ȳ`, and `t`
  is quasi-separated, then `U ⟶ Y ×_T Ȳ` is such an `m` for the projection `Y ×_T Ȳ ⟶ Y`, which
  is proper by Stacks 04WP. In the source this is applied with `U ⟶ X` étale, `X` separated of
  finite type over `Y`, and `T = Spec ℤ`.
* If `V` is an affine scheme locally of finite type over `S`, it immerses into a projective
  space `ℙⁿ_S`, and for any `v : V ⟶ Y` the morphism `V ⟶ Y ×_S ℙⁿ_S` is such an `m`.

## Main results

* `AlgebraicGeometry.Space.HasCompactification.of_mono_of_isProper`: the general statement.
* `AlgebraicGeometry.Space.HasCompactification.of_comp`: a compactification over `T` gives
  one over `Y`.
* `AlgebraicGeometry.Space.hasCompactification_yoneda_of_isAffine`: an affine scheme locally of
  finite type over `S` has a compactification over any quasi-compact quasi-separated algebraic
  space it maps to.

## Implementation notes

Zariski's main theorem for algebraic spaces, Stacks 082K, is
`AlgebraicGeometry.Space.exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite`, which
rests on Stacks 09YA: an integral morphism to a quasi-compact and quasi-separated algebraic
space is a directed limit of finite morphisms of finite presentation.
Quasi-separatedness of an algebraic space is the absolute notion of Stacks 03BS, part (3),
whence the containment `hZ` of `Spec ℤ` in the site.

The étale hypothesis of the source plays no role in the argument and is not assumed.

## References

* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
* [Stacks Project, Tag 082K](https://stacks.math.columbia.edu/tag/082K)
* [Stacks Project, Tag 09YA](https://stacks.math.columbia.edu/tag/09YA)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
* [Stacks Project, Tag 04XY](https://stacks.math.columbia.edu/tag/04XY)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If `m ≫ q` is an immersion then `m` is a monomorphism locally of finite type. -/
private theorem mono_and_isLocallyOfFiniteType_of_comp_isImmersion
    {U W P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hW : IsAlgebraicSpace B S hS W) (hP : IsAlgebraicSpace B S hS P)
    (m : U ⟶ W) (q : W ⟶ P) (h : IsImmersion B S hS (m ≫ q)) :
    Mono m ∧ IsLocallyOfFiniteType B S hS m :=
  have := mono_of_isImmersion B S hS h
  ⟨mono_of_mono m q,
    isLocallyOfFiniteType_of_comp B S hS hU hW hP m q
      (isLocallyOfFiniteType_of_isImmersion B S hS _ h)⟩

namespace HasCompactification

/-- **A quasi-compact monomorphism locally of finite type into a proper space is
compactifiable.** Let `p : P ⟶ Y` be proper, with `Y` quasi-compact and quasi-separated, and let
`m : U ⟶ P` be a quasi-compact monomorphism which is locally of finite type. Then `m` is
separated and quasi-finite (Stacks 0463), so by Zariski's main theorem (Stacks 082K) it factors
as a quasi-compact open immersion followed by a finite, hence proper, morphism to `P`; composing
with `p` gives a compactification of `m ≫ p`. -/
theorem of_mono_of_isProper (hZ : B.Contains (⊤_ Scheme.{u}))
    {U P Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hP : IsAlgebraicSpace B S hS P) (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (m : U ⟶ P) (p : P ⟶ Y) [Mono m] (hmlft : IsLocallyOfFiniteType B S hS m)
    (hmqc : IsQuasiCompact B S hS m) (hp : IsProper B S hS p) :
    HasCompactification B S hS (m ≫ p) := by
  have hPqc : IsQuasiCompactSpace B S hS P :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc hp.2.1.2
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hP hYqs
      (isQuasiSeparated_of_isSeparated B S hS hp.1)
  obtain ⟨T', j', π, hT', hj', hj'qc, hπ, hfac⟩ :=
    exists_isOpenImmersion_isFinite_comp_eq_of_isQuasiFinite m hU hP
      ⟨isLocallyQuasiFinite_of_mono B S hS hU hP m inferInstance hmlft, hmqc⟩
      (isSeparated_of_mono m inferInstance) hPqc hPqs
  have hπp : IsProper B S hS π := ((isFinite_iff_isAffineHom_and_isProper B S hS hT' hP π).mp hπ).2
  refine of_eq ?_ (of_isOpenImmersion_isProper j' (π ≫ p) hT' hj' hj'qc
    (isProper_comp' B S hS π p hP hY hπp hp))
  rw [← Category.assoc, hfac]

/-- **A compactification over a coarser base gives one over the finer base.** Let `u : U ⟶ Y`
and `t : Y ⟶ T` be morphisms of algebraic spaces over `S`, with `Y` quasi-compact and
quasi-separated and `t` quasi-separated. If `u ≫ t` has a compactification then so has `u`. -/
theorem of_comp (hZ : B.Contains (⊤_ Scheme.{u}))
    {U Y T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hY : IsAlgebraicSpace B S hS Y) (hT : IsAlgebraicSpace B S hS T)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (u : U ⟶ Y) (t : Y ⟶ T) (ht : IsQuasiSeparated B S hS t)
    (h : HasCompactification B S hS (u ≫ t)) : HasCompactification B S hS u := by
  obtain ⟨Yc, j, p, hYc, hj, hjqc, hp, hjp⟩ := h
  have hP : IsAlgebraicSpace B S hS (pullback t p) :=
    isAlgebraicSpace_pullback B S hS t p hY hYc hT
  let m : U ⟶ pullback t p := pullback.lift u j hjp.symm
  have hmfst : m ≫ pullback.fst t p = u := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd t p = j := pullback.lift_snd _ _ _
  obtain ⟨hmmono, hmlft⟩ := mono_and_isLocallyOfFiniteType_of_comp_isImmersion hU hP hYc m
    (pullback.snd t p) (hmsnd ▸ isImmersion_of_isOpenImmersion B S hS hj)
  have hmqc : IsQuasiCompact B S hS m :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS m (pullback.snd t p) hU hYc
      (hmsnd ▸ hjqc) (isQuasiSeparated_pullback_snd B S hS t p ht)
  have hfst : IsProper B S hS (pullback.fst t p) :=
    isProper_of_isPullback B S hS hP hYc hY hT (IsPullback.of_hasPullback t p).flip hp
  exact of_eq hmfst (of_mono_of_isProper hZ hU hP hY hYqc hYqs m _ hmlft hmqc hfst)

end HasCompactification

/-- **An affine scheme locally of finite type over `S` is compactifiable over any quasi-compact
quasi-separated algebraic space it maps to.** Let `V` be an object of the site with affine
underlying scheme whose structure morphism to `S` is locally of finite type, and let
`v : V ⟶ Y` be a morphism to a quasi-compact and quasi-separated algebraic space. Then `V`
immerses into a projective space `ℙⁿ_S`, and the morphism `V ⟶ Y ×_S ℙⁿ_S` is a quasi-compact
monomorphism locally of finite type into a space proper over `Y`, so
`AlgebraicGeometry.Space.HasCompactification.of_mono_of_isProper` applies. -/
theorem hasCompactification_yoneda_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hVft : LocallyOfFiniteType (B.inclusion.map V.hom)) (v : yoneda.obj V ⟶ Y) :
    HasCompactification B S hS v := by
  have : IsAffine (B.inclusion.obj V.left) := hV
  obtain ⟨n, ι, hι, hιf⟩ := exists_immersion_projectiveSpace (B.inclusion.map V.hom)
  have hPS : B.Contains (ProjectiveSpace n S) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (ProjectiveSpace n S ↘ S) hS
  let P : BigFppfOver B S hS := siteObject B S hS hPS (ProjectiveSpace n S ↘ S)
  let T : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  have hT : IsTerminal (yoneda.obj T) :=
    (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _
  let i : V ⟶ P := Over.homMk (ObjectProperty.homMk ι) (B.inclusion.map_injective hιf)
  let π : P ⟶ T := Over.homMk P.hom (Category.comp_id _)
  have hι' : IsImmersion B S hS (yoneda.map i) := by
    have := inverseImage_isStableUnderBaseChange B S hS
      (P := @AlgebraicGeometry.IsImmersion.{u}) inferInstance
    exact MorphismProperty.relative_map (F := yoneda) hι
  have hπ : IsProper B S hS (yoneda.map π) :=
    isProper_yoneda_map B S hS π (ProjectiveSpace.instIsProperOver n S)
  have hYP : IsAlgebraicSpace B S hS (pullback (hT.from Y) (yoneda.map π)) :=
    isAlgebraicSpace_pullback B S hS _ _ hY (isAlgebraicSpace_yoneda B S hS P)
      (isAlgebraicSpace_yoneda B S hS T)
  have hfst : IsProper B S hS (pullback.fst (hT.from Y) (yoneda.map π)) :=
    isProper_of_isPullback B S hS hYP (isAlgebraicSpace_yoneda B S hS P) hY
      (isAlgebraicSpace_yoneda B S hS T) (IsPullback.of_hasPullback _ _).flip hπ
  let m : yoneda.obj V ⟶ pullback (hT.from Y) (yoneda.map π) :=
    pullback.lift v (yoneda.map i) (hT.hom_ext _ _)
  have hmfst : m ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd _ _ = yoneda.map i := pullback.lift_snd _ _ _
  have hVa : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  obtain ⟨hmmono, hmlft⟩ := mono_and_isLocallyOfFiniteType_of_comp_isImmersion hVa hYP
    (isAlgebraicSpace_yoneda B S hS P) m _ (hmsnd ▸ hι')
  have hYPqs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback (hT.from Y) (yoneda.map π)) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hYP hYqs
      (isQuasiSeparated_of_isSeparated B S hS hfst.1)
  have hmqc : IsQuasiCompact B S hS m :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hYP hYPqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV) m
  exact HasCompactification.of_eq hmfst
    (HasCompactification.of_mono_of_isProper hZ hVa hYP hY hYqc hYqs m _ hmlft hmqc hfst)

end AlgebraicGeometry.Space

end
