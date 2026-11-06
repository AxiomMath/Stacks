module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Bootstrapping an algebraic space from a surjective étale cover

Let `S` be a scheme contained in a big fppf site `B` and let `F` be an fppf sheaf on the big
fppf site of `S`. If `F` admits a morphism from an algebraic space over `S` which is
representable by algebraic spaces, surjective and étale, then `F` is an algebraic space over
`S`; and the same conclusion holds if instead the diagonal of `F` is representable by algebraic
spaces and `F` admits a surjective étale morphism from an algebraic space. These are the two
sets of hypotheses of Stacks 03Y3, and the first follows from the second by Stacks 03Y2.

The passage from a chart of the covering algebraic space to a chart of `F` is unconditional:
a morphism `u : h_U ⟶ F` from an object of the site which is representable by algebraic spaces
and étale after every representable base change is representable by *objects of the site*,
because each of its base changes sits inside a product of representables as a monomorphism
which is locally of finite type, so Stacks 03XX applies. What is *not* unconditional is the
representability of the diagonal of `F`: the two components of a point of `F ×ₛ F` lift to `U`
only locally for the fppf topology, and glueing the resulting local descriptions of the
diagonal is effective fppf descent. That input is
`AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`, the
covering-sieve form of Stacks 02W8 at the monomorphisms locally of finite type, which holds
unconditionally; the size bound its glueing needs comes from the property lying below the
monomorphisms.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_of_isEtale_pullback_fst`: a morphism to a
  presheaf from an object of the site which is representable by algebraic spaces and étale
  after every representable base change is representable by objects of the site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale`:
  **Stacks 03Y3** under its conditions (a) and (b).
* `AlgebraicGeometry.Space.isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_diag`:
  **Stacks 03Y3** under its conditions (1), (2) and (3).

## Implementation notes

**The chart.** A chart `c : h_U ⟶ X` of the covering algebraic space is surjective and étale
after every representable base change, and the base change of `c` along the projection
`h_T ×_F X ⟶ X` keeps both properties, so the base change of `c ≫ f` along a point
`ξ : h_T ⟶ F` is the composite of two surjective étale morphisms of algebraic spaces; the
identification with that composite is `CategoryTheory.Limits.pullbackLeftPullbackSndIso`.
Surjectivity and étaleness of a morphism of algebraic spaces are transported across the
resulting isomorphism by the four private lemmas at the head of the file.

**The diagonal.** Over an arrow of the sieve along which both components of a point of
`F ⨯ F` lift to `U`, the base change of `Δ_F` is the base change of the kernel pair
`R ⟶ U ⨯ U` of the chart, whose underlying morphism of schemes is a monomorphism locally of
finite type by `AlgebraicGeometry.Space.locallyOfFiniteType_and_mono_toScheme_kernelPairToProd`;
the cartesian square exhibiting it is
`AlgebraicGeometry.Space.isPullback_kernelPairToProd`. The sieve is the intersection of the two
image sieves of the chart, covering because the chart is locally surjective — which is
Stacks 04S1 for this chart, `AlgebraicGeometry.isLocallySurjective_of_surjective_etale`.

**Why the source's second route is not taken.** Stacks finishes by exhibiting `F` as the
quotient `U/R` and appealing to Stacks 02WW. In this library Stacks 02WW itself carries the
same effective-descent hypothesis, so that route would prove no more than the direct argument
above; the direct argument is taken instead because it needs neither the étale
equivalence-relation structure on `R` nor the universal property of the quotient sheaf. The
source's other route, through Stacks 046K, is unavailable: the library's Stacks 046K carries
Stacks 0AMP as a hypothesis, and in the source Stacks 0AMP is a corollary of the bootstrap
theorem Stacks 04S6, which is downstream of the theorem proved here.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03Y1](https://stacks.math.columbia.edu/tag/03Y1)
* [Stacks Project, Tag 03Y2](https://stacks.math.columbia.edu/tag/03Y2)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_BootstrapEtaleSurjective :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Fibre products of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_BootstrapEtaleSurjective
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Small discrete limits of presheaves on the big fppf site over `S` (instance search times
out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_BootstrapEtaleSurjective
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-! ### Transport of surjectivity and étaleness across an isomorphism of the source -/

variable {B S hS}

/-- Precomposing an étale morphism of algebraic spaces over `S` with an isomorphism keeps it
étale. -/
private theorem isEtale_iso_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (k : G ⟶ H) (hk : IsEtale B S hS k) : IsEtale B S hS (e.hom ≫ k) :=
  have _hri : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf :=
    MorphismProperty.relative_respectsIso (F := yoneda) _
  isEtale_comp B S hS
    (fun _ φ hφ => MorphismProperty.RespectsIso.postcomp _ e.hom φ hφ) hk

/-- A morphism of algebraic spaces over `S` whose precomposition with an isomorphism is étale is
itself étale. -/
private theorem isEtale_of_iso_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (k : G ⟶ H) (hk : IsEtale B S hS (e.hom ≫ k)) : IsEtale B S hS k := by
  simpa using isEtale_iso_comp e.symm (e.hom ≫ k) hk

/-- Precomposing a surjective morphism of algebraic spaces over `S` with an isomorphism keeps it
surjective. -/
private theorem isSurjective_iso_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (k : G ⟶ H) (hk : IsSurjective B S hS k) : IsSurjective B S hS (e.hom ≫ k) :=
  isSurjective_comp B S hS (isSurjective_of_isIso B S hS e.hom) hk

/-- A morphism of algebraic spaces over `S` whose precomposition with an isomorphism is
surjective is itself surjective. -/
private theorem isSurjective_of_iso_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (k : G ⟶ H) (hk : IsSurjective B S hS (e.hom ≫ k)) : IsSurjective B S hS k := by
  simpa using isSurjective_iso_comp e.symm (e.hom ≫ k) hk

/-! ### Representability of a surjective étale chart by objects of the site -/

/-- **A morphism to a presheaf on the big fppf site of `S` from an object of the site which is
representable by algebraic spaces and étale after every representable base change is
representable by objects of the site.**

Let `u : h_U ⟶ F` be such a morphism and let `ξ : h_T ⟶ F` be a point of `F`. The fibre product
`h_T ×_F h_U` is an algebraic space over `S`, and its two projections are jointly
monomorphic, so it is a monomorphism over the product `h_T ⨯ h_U`, which is representable.
That monomorphism is separated by **Stacks 042N** and locally of finite type by **Stacks 0462**,
because its composite with the first projection is the base change of `u`, which is étale and
hence locally of finite type by **Stacks 06LT**; **Stacks 0463** then makes it locally
quasi-finite, and **Stacks 03XX** makes `h_T ×_F h_U` representable. -/
theorem relativelyRepresentable_of_isEtale_pullback_fst
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} (u : yoneda.obj U ⟶ F)
    (hu : IsRepresentableByAlgebraicSpaces B S hS u)
    (huE : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F),
      IsEtale B S hS (pullback.fst ξ u)) :
    yoneda.relativelyRepresentable u := by
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro T ξ
  have hP : IsAlgebraicSpace B S hS (pullback (yonedaEquiv.symm ξ) u) :=
    hu T (yonedaEquiv.symm ξ)
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hprod : IsAlgebraicSpace B S hS (yoneda.obj T ⨯ yoneda.obj U) :=
    isAlgebraicSpace_prod_yoneda B S hS T U
  have hmono : Mono (prod.lift (pullback.fst (yonedaEquiv.symm ξ) u)
      (pullback.snd (yonedaEquiv.symm ξ) u)) :=
    ⟨fun x y hxy => pullback.hom_ext
      (by simpa using congrArg (· ≫ (prod.fst : _ ⨯ _ ⟶ _)) hxy)
      (by simpa using congrArg (· ≫ (prod.snd : _ ⨯ _ ⟶ _)) hxy)⟩
  have hlftfst : IsLocallyOfFiniteType B S hS (pullback.fst (yonedaEquiv.symm ξ) u) :=
    isLocallyOfFiniteType_of_isEtale B S hS hT (huE T (yonedaEquiv.symm ξ))
  have hlft : IsLocallyOfFiniteType B S hS (prod.lift
      (pullback.fst (yonedaEquiv.symm ξ) u) (pullback.snd (yonedaEquiv.symm ξ) u)) :=
    isLocallyOfFiniteType_of_comp B S hS hP hprod hT _ prod.fst (by simpa using hlftfst)
  have hrepProd : (yoneda.obj T ⨯ yoneda.obj U).IsRepresentable :=
    isRepresentable_of_natIso (yoneda.obj (T ⨯ U)) (yonedaProdIso B S hS T U)
  exact isRepresentable_of_locallyQuasiFinite_separated B S hS _ _ hP hprod _ hrepProd
    (isLocallyQuasiFinite_of_mono B S hS hP hprod _ hmono hlft)
    (isSeparated_of_mono B S hS _ hmono)

/-! ### Stacks 03Y3 -/

/-- The base change along a point of `F` of the composite of a chart of the covering algebraic
space with the covering morphism is surjective and étale: it is the composite of the base change
of the covering morphism, which is surjective and étale by hypothesis, with a base change of the
chart. -/
private theorem isSurjective_isEtale_pullback_fst_comp
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ F}
    (hfS : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F),
      IsSurjective B S hS (pullback.fst ξ f))
    (hfE : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F),
      IsEtale B S hS (pullback.fst ξ f))
    {U : BigFppfOver B S hS} {c : yoneda.obj U ⟶ X}
    (hcS : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hcE : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F) :
    IsSurjective B S hS (pullback.fst ξ (c ≫ f)) ∧
      IsEtale B S hS (pullback.fst ξ (c ≫ f)) := by
  have hbcS := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hbcE := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hsq := (IsPullback.of_hasPullback (pullback.snd ξ f) c).flip
  have hcS' := MorphismProperty.of_isPullback hsq hcS
  have hcE' := MorphismProperty.of_isPullback hsq hcE
  have heq : (pullbackLeftPullbackSndIso ξ f c).hom ≫ pullback.fst ξ (c ≫ f) =
      pullback.fst (pullback.snd ξ f) c ≫ pullback.fst ξ f := by
    simp
  refine ⟨isSurjective_of_iso_comp (pullbackLeftPullbackSndIso ξ f c) _ ?_,
    isEtale_of_iso_comp (pullbackLeftPullbackSndIso ξ f c) _ ?_⟩
  · rw [heq]
    exact isSurjective_comp B S hS
      (isSurjective_of_presheafSurjective B S hS _ hcS') (hfS T ξ)
  · rw [heq]
    exact isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hcE') (hfE T ξ)

/-- **Stacks 03Y3, conditions (a) and (b).** Let `F` be an fppf sheaf on the big fppf site of
a scheme `S` admitting a morphism `f : X ⟶ F` from an algebraic space over `S` which is
representable by algebraic spaces, surjective and étale. Then `F` is an algebraic space over `S`.

The chart of `F` is the composite of a chart of `X` with `f`, which is representable by
algebraic spaces by **Stacks 03Y1** and therefore by objects of the site; the diagonal is the
only clause of **Stacks 025Y** needing effective fppf descent, which is supplied by
`isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`. -/
@[stacks 03Y3 "conditions (a) and (b)"]
theorem isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hfSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf)
    (hfEtale : HasProperty B S hS (etaleMorphisms B S hS) f hf) :
    IsAlgebraicSpace B S hS F := by
  classical
  obtain ⟨U, c, hcS, hcE⟩ := hX.exists_atlas
  have hfS : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F),
      IsSurjective B S hS (pullback.fst ξ f) := fun T ξ => hfSurj T ξ
  have hfE : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ F),
      IsEtale B S hS (pullback.fst ξ f) := fun T ξ => hfEtale T ξ
  have hbase := isSurjective_isEtale_pullback_fst_comp hfS hfE hcS hcE
  have huAlg : IsRepresentableByAlgebraicSpaces B S hS (c ≫ f) :=
    (IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable hcE.rep).comp hf
  have hurep : yoneda.relativelyRepresentable (c ≫ f) :=
    relativelyRepresentable_of_isEtale_pullback_fst (c ≫ f) huAlg fun T ξ => (hbase T ξ).2
  -- The chart of `F` is surjective and étale after every representable base change.
  have huS : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ f) := by
    refine ⟨hurep, ?_⟩
    intro a b g fst snd sq
    have h2 : (sq.isoPullback.hom ≫ (pullbackSymmetry (c ≫ f) g).hom) ≫
        pullback.fst g (c ≫ f) = yoneda.map snd := by
      rw [Category.assoc, pullbackSymmetry_hom_comp_fst, sq.isoPullback_hom_snd]
    have h3 : IsSurjective B S hS (yoneda.map snd) := by
      rw [← h2]
      exact isSurjective_iso_comp (sq.isoPullback ≪≫ pullbackSymmetry (c ≫ f) g) _
        (hbase a g).1
    exact MorphismProperty.of_relative_map
      ((surjective_yonedaMap_iff_surjective_pointsMap B S hS snd).2 h3)
  have huE : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ f) := by
    refine ⟨hurep, ?_⟩
    intro a b g fst snd sq
    have h2 : (sq.isoPullback.hom ≫ (pullbackSymmetry (c ≫ f) g).hom) ≫
        pullback.fst g (c ≫ f) = yoneda.map snd := by
      rw [Category.assoc, pullbackSymmetry_hom_comp_fst, sq.isoPullback_hom_snd]
    have h3 : IsEtale B S hS (yoneda.map snd) := by
      rw [← h2]
      exact isEtale_iso_comp (sq.isoPullback ≪≫ pullbackSymmetry (c ≫ f) g) _ (hbase a g).2
    exact (presheaf_yoneda_map_etale_iff B S hS snd).1
      ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map snd)).1 h3)
  -- The diagonal, by effective descent along the image sieves of the chart.
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (c ≫ f) :=
    _root_.AlgebraicGeometry.isLocallySurjective_of_surjective_etale B S hS (c ≫ f) huS huE
  have hbcP : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.monomorphisms Scheme.{u} ⊓
        @_root_.AlgebraicGeometry.LocallyOfFiniteType) := .inf
  have hriP : MorphismProperty.RespectsIso
      ((MorphismProperty.monomorphisms Scheme.{u} ⊓
        @_root_.AlgebraicGeometry.LocallyOfFiniteType).inverseImage
          (BigFppfOver.toScheme B S hS)) := MorphismProperty.RespectsIso.inverseImage _ _
  obtain ⟨hjlft, hjmono⟩ :=
    locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (c ≫ f) huE
  have hdiagF : yoneda.relativelyRepresentable (diag F) := by
    have key : ((MorphismProperty.monomorphisms Scheme.{u} ⊓
        @_root_.AlgebraicGeometry.LocallyOfFiniteType).inverseImage
          (BigFppfOver.toScheme B S hS)).presheaf (diag F) := by
      refine (MorphismProperty.presheaf_iff_forall_presheaf_pullback_snd _ _).2 ?_
      intro a h
      refine isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS
        (diag F) hF (isSheaf_prod_self B S hS hF) h
        (Presheaf.imageSieve (c ≫ f) (yonedaEquiv (h ≫ prod.fst)) ⊓
          Presheaf.imageSieve (c ≫ f) (yonedaEquiv (h ≫ prod.snd)))
        ((BigFppfOver.topology B S hS).intersection_covering
          (Presheaf.imageSieve_mem _ _ _) (Presheaf.imageSieve_mem _ _ _)) ?_
      intro b q hq
      obtain ⟨⟨xx, hxx⟩, ⟨yy, hyy⟩⟩ := hq
      have hfac : yoneda.map q ≫ h =
          yoneda.map (prod.lift xx yy) ≫ atlasProd B S hS (c ≫ f) := by
        refine prod.hom_ext ?_ ?_
        · rw [Category.assoc, Category.assoc, atlasProd, prod.lift_fst, ← Functor.map_comp_assoc,
            prod.lift_fst]
          apply yonedaEquiv.injective
          rw [yonedaEquiv_comp (yoneda.map xx) (c ≫ f), yonedaEquiv_yoneda_map,
            ← yonedaEquiv_naturality, hxx]
        · rw [Category.assoc, Category.assoc, atlasProd, prod.lift_snd, ← Functor.map_comp_assoc,
            prod.lift_snd]
          apply yonedaEquiv.injective
          rw [yonedaEquiv_comp (yoneda.map yy) (c ≫ f), yonedaEquiv_yoneda_map,
            ← yonedaEquiv_naturality, hyy]
      have hsq1 := (IsPullback.of_hasPullback (prod.lift xx yy)
        (kernelPairToProd B S hS huE.rep)).flip
      have hsq := (hsq1.map yoneda).paste_horiz (isPullback_kernelPairToProd B S hS huE.rep)
      rw [← hfac] at hsq
      refine presheaf_pullback_snd_of_isPullback hsq ?_
      exact (inverseImage_isStableUnderBaseChange B S hS hbcP).of_isPullback hsq1
        ⟨hjmono, hjlft⟩
    exact key.rep
  exact ⟨hF, hdiagF, U, c ≫ f, huS, huE⟩

/-- **Stacks 03Y3, conditions (1), (2) and (3).** Let `F` be an fppf sheaf on the big fppf
site of a scheme `S` whose diagonal is representable by algebraic spaces and which admits a
surjective étale morphism from an algebraic space over `S`. Then `F` is an algebraic space over
`S`.

Condition (2) makes the morphism of condition (3) representable by algebraic spaces by **Stacks
03Y2**, so the hypotheses (a) and (b) hold and the previous theorem applies. -/
@[stacks 03Y3 "conditions (1), (2) and (3)"]
theorem isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_diag
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diag F))
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F)
    (hfSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f))
    (hfEtale : HasProperty B S hS (etaleMorphisms B S hS) f
      (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f)) :
    IsAlgebraicSpace B S hS F :=
  isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale hF hX f
    (isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag hX f)
    hfSurj hfEtale

end AlgebraicGeometry.Space

end
