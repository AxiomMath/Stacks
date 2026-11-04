module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedShortExact

/-!
# Weakly associated points of a direct image on algebraic spaces

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over a scheme `S` of a big
fppf site `B`, let `F` be a quasi-coherent `𝒪_X`-module and let `y` be a point of `Y` outside
the image of `|f|`.  Stacks 0CUQ asserts that `y` is then not weakly associated to the direct
image `f_*F`.

The argument of the source is followed step by step, with its last citation — Stacks 0CU2, that
along an *affine* morphism `g` every weakly associated point of `g_*H` is the image of one of
`H` — carried as an explicit hypothesis.  Everything else is discharged here:

* an affine étale chart `V` of `Y` through `y` exists
  (`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`), which is the source's "we may
  and do assume `Y` is an affine scheme";
* weak association is detected by étale restriction (Stacks 0CUU), and étale restriction of a
  direct image is the direct image of the étale restriction along the base change
  (Stacks 03LX), so the question moves to the base change `f' : X ×_Y V ⟶ V`;
* that base change has quasi-compact source, so it admits an affine surjective étale chart
  `U` (Stacks 03H6), and `U ⟶ V` is a morphism of affine schemes of the site, hence an affine
  morphism of algebraic spaces (Stacks 03WF);
* restriction of modules along a *surjective* étale morphism is faithful, so the unit
  `F ⟶ i_*i^*F` of the Stacks 03LU adjunction is a monomorphism and, the direct image being a
  right adjoint, `f'_*F' ⟶ (U ⟶ V)_*(F'|_U)` is a monomorphism as well.  This is the source's
  inclusion `f_*F ⊂ g_*(F|_U)`;
* Stacks 0CTZ carries weakly associated points along that monomorphism.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardChartComparison` is the comparison
  `f_*F ⟶ (i ≫ f)_*(i^*F)` attached to a morphism `i` into the source of `f`.
* `AlgebraicGeometry.Space.AffinePushforwardWeaklyAssociatedImage` is Stacks 0CU2 as a
  proposition, the single hypothesis the main results carry.

## Main results

* `AlgebraicGeometry.Space.injective_val_map_of_etale_surjective`: restriction of sections of
  an `𝒪_X`-module along a surjective étale morphism of étale charts is injective.
* `AlgebraicGeometry.Space.faithful_etaleModulePullback` and
  `AlgebraicGeometry.Space.faithful_modulePullback`: étale restriction, and hence the pullback
  of modules of Stacks 03LU, along a surjective étale morphism from a scheme is faithful.
* `AlgebraicGeometry.Space.mono_modulePushforwardChartComparison`: the comparison above is a
  monomorphism when the pullback along `i` is faithful.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_of_mono`: **Stacks 0CTZ for a
  monomorphism** of `𝒪_X`-modules.
* `AlgebraicGeometry.Space.isAffineHom_yoneda_map`: a morphism of objects of the big fppf site
  with affine underlying schemes is an affine morphism of algebraic spaces.
* `AlgebraicGeometry.Space.not_isWeaklyAssociatedPoint_modulePushforward_of_isQuasiCompactSpace`:
  Stacks 0CUQ when the target is an affine scheme of the site and the source is quasi-compact,
  granting Stacks 0CU2.
* `AlgebraicGeometry.Space.not_isWeaklyAssociatedPoint_modulePushforward_of_notMem_range`:
  **Stacks 0CUQ**, granting Stacks 0CU2.

## Implementation notes

Stacks 0CU2 is not proved here, but it is carried in this development: it is
`AlgebraicGeometry.Space.affinePushforwardWeaklyAssociatedImage` in
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/SpaceAffinePushforward.lean`,
which proves the hypothesis `h0CU2` below from the case of a target represented by an affine
scheme of the site.  Its own proof reduces, along an étale scheme chart of the target, to the
case of an affine morphism of schemes (Stacks 05EX).  What that reduction still needs is not
the stalk comparison of Stacks 05VP, which is available —
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison` in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartStalkTensorIsomorphism.lean` — nor Stacks 03LZ,
which `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartQuasicoherentGlueing.lean` carries;
it is the comparison of the Zariski modules of a represented algebraic space with its
small-étale modules, the equivalence of Stacks 03LY, whose absence is recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartModuleGlueing.lean`.  Carrying Stacks 0CU2
as a hypothesis here is therefore the same idiom as the `h05VP` of
`AlgebraicGeometry.Space.supp_restrictToChart_eq_preimage_supportOfSheaf`.

Two hypotheses of the source are *not* assumed.  Quasi-separatedness of `f` is unused: the
source needs it only to know that `f_*F` is quasi-coherent (Stacks 03M9), and the argument
below never uses that — `AlgebraicGeometry.Space.IsWeaklyAssociatedPoint` is defined for an
arbitrary `𝒪_X`-module, so the statement is well posed without it.  **No `@[stacks 03M9]`
attribute is carried and no part of Stacks 03M9 is used.**  Quasi-coherence of `F` itself *is*
assumed, because Stacks 0CU2 assumes it; it is passed as an explicit argument rather than an
instance so that the quasi-coherence of the pullbacks of `F` produced along the way, which is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback`, can be handed over
explicitly too.

The module universe is the universe `u` of the structure rings.  That is forced twice over:
`AlgebraicGeometry.Space.modulePushforward` exists only there, and the abelian structure used
to turn a monomorphism into a short exact sequence is available only there.  Étale restriction
is faithful at every module universe, and
`AlgebraicGeometry.Space.injective_val_map_of_etale_surjective` and
`AlgebraicGeometry.Space.faithful_etaleModulePullback` are stated at a free one.

The base change of `f` along the chart is the presheaf fibre product of Stacks 02X2, which is
an honest algebraic space, so no localization of the spaces-étale site intervenes and the
obstruction recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentPushforwardReduction.lean` — that the
Stacks 04CF restriction of `f_*F` to a chart is a direct image on a *slice* of the
spaces-étale site rather than on the small étale site of an algebraic space — does not arise:
Stacks 03LX for the ordinary direct image,
`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`, already compares the two
functors `AlgebraicGeometry.Space.modulePushforward` of the two edges of the cartesian square.

## References

* [Stacks Project, Tag 0CUQ](https://stacks.math.columbia.edu/tag/0CUQ)
* [Stacks Project, Tag 0CU2](https://stacks.math.columbia.edu/tag/0CU2)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 0CTZ](https://stacks.math.columbia.edu/tag/0CTZ)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Faithfulness of étale restriction along a surjective étale morphism -/

/-- Restriction of sections of an `𝒪_X`-module along a morphism of étale charts whose
underlying morphism of schemes is surjective and étale is injective: such a morphism generates
a covering sieve of its target, and a sheaf is separated for a covering sieve. -/
theorem injective_val_map_of_etale_surjective (X : AlgebraicSpaces B S hS)
    (G : Modules.{u, m} B S hS X.1 X.2) {V W : SmallEtale B S hS X.1} (k : W ⟶ V)
    (hk : Etale ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map k))
    (hs : Surjective ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).map k)) :
    Function.Injective (G.val.map k.op) := by
  have hpre : Presieve.singleton k ∈ SmallEtale.precoverage B S hS X.1 V := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton]
    exact B.singleton_mem_etalePrecoverage _ hs hk
  have hcov : Sieve.generate (Presieve.singleton k) ∈ SmallEtale.topology B S hS X.1 V :=
    Precoverage.generate_mem_toGrothendieck hpre
  intro x y h
  refine G.isSheaf.isSeparated V _ hcov x y ?_
  rintro Z f hf
  obtain ⟨T, c, d, hd, rfl⟩ := hf
  cases hd
  have h2 : G.val.presheaf.map k.op x = G.val.presheaf.map k.op y := h
  have hmap : G.val.presheaf.map (c ≫ k).op
      = G.val.presheaf.map k.op ≫ G.val.presheaf.map c.op :=
    G.val.presheaf.map_comp k.op c.op
  have e : ∀ z, G.val.presheaf.map (c ≫ k).op z
      = G.val.presheaf.map c.op (G.val.presheaf.map k.op z) := fun z =>
    (ConcreteCategory.congr_hom hmap z).trans (CategoryTheory.comp_apply _ _ z)
  exact (e x).trans
    ((congrArg (fun z => G.val.presheaf.map c.op z) h2).trans (e y).symm)

/-- **Étale restriction along a surjective étale chart is faithful.**  Let `i : U ⟶ X` be a
surjective étale morphism of algebraic spaces whose source is the algebraic space of a scheme
of the site.  Then restricting `𝒪_X`-modules to the étale charts of `U` is a faithful functor.

Two morphisms with equal restrictions agree over every étale chart `V` of `X`, because the
projection of `U ×_X V` to `V` is a chart of `X` in the image of
`AlgebraicGeometry.Space.smallEtalePostcomp` whose underlying morphism of schemes is surjective
and étale, so `AlgebraicGeometry.Space.injective_val_map_of_etale_surjective` applies. -/
theorem faithful_etaleModulePullback {X : AlgebraicSpaces B S hS}
    (U : BigFppfOver B S hS) (i : schemeSpace U ⟶ X) (hi : IsEtale B S hS i.hom)
    (hs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) :
    (etaleModulePullback.{u, m} B S hS i hi).Faithful := by
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u}) T
  have hi' : P.presheaf i.hom := (isEtale_iff_presheaf_of_yoneda B S hS i.hom).1 hi
  constructor
  intro F G a b hab
  ext V s
  let r := hs.rep
  let p := r.fst' V.unop.1.hom
  let q := r.snd V.unop.1.hom
  have sq := r.isPullback' V.unop.1.hom
  have hp : P p := V.unop.2.property i.hom (yoneda.map q) p sq.flip
  have hq : Etale (T.map q) := hi'.property V.unop.1.hom (yoneda.map p) q sq
  have hqs : Surjective (T.map q) := hs.property V.unop.1.hom (yoneda.map p) q sq
  let W : SmallEtale B S hS (schemeSpace U).1 :=
    ⟨CostructuredArrow.mk (yoneda.map p), (presheaf_yoneda_map_etale_iff B S hS p).2 hp⟩
  let L := smallEtalePostcomp B S hS i hi
  let k : L.obj W ⟶ V.unop := ⟨CostructuredArrow.homMk q sq.w.symm⟩
  apply injective_val_map_of_etale_surjective B S hS X G k hq hqs
  refine (PresheafOfModules.naturality_apply a.val k.op s).symm.trans
    (Eq.trans ?_ (PresheafOfModules.naturality_apply b.val k.op s))
  exact congrArg (fun t => t.val.app (.op W) (F.val.map k.op s)) hab

/-! ### The inclusion of a direct image into the direct image over a chart -/

/-- **The pullback of modules along a surjective étale chart is faithful.**  This is
`AlgebraicGeometry.Space.faithful_etaleModulePullback` transported along Stacks Equation 03LW,
the identification of the pullback of Stacks 03LU with étale restriction. -/
theorem faithful_modulePullback {X : AlgebraicSpaces B S hS}
    (U : BigFppfOver B S hS) (i : schemeSpace U ⟶ X) (hi : IsEtale B S hS i.hom)
    (hs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i.hom) :
    (modulePullback B S hS i).Faithful :=
  have := faithful_etaleModulePullback.{u, u} B S hS U i hi hs
  Functor.Faithful.of_iso (modulePullbackIsoEtaleModulePullback B S hS i hi).symm

/-- The canonical map `f_*F ⟶ (i ≫ f)_*(i^*F)`. -/
def modulePushforwardChartComparison {X Y Z : AlgebraicSpaces B S hS} (i : Z ⟶ X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS f).obj F ⟶
      (modulePushforward B S hS (i ≫ f)).obj ((modulePullback B S hS i).obj F) :=
  (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS i).unit.app F) ≫
    (modulePushforwardCompIso B S hS i f).hom.app ((modulePullback B S hS i).obj F)

/-- `AlgebraicGeometry.Space.modulePushforwardChartComparison` is a monomorphism as soon as the
pullback along `i` is faithful: the unit of a faithful left adjoint is a monomorphism, and the
direct image preserves monomorphisms, being a right adjoint. -/
theorem mono_modulePushforwardChartComparison {X Y Z : AlgebraicSpaces B S hS}
    (i : Z ⟶ X) (f : X ⟶ Y) (hi : (modulePullback B S hS i).Faithful)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    Mono (modulePushforwardChartComparison B S hS i f F) := by
  have := hi
  have : Mono ((modulePullbackAdjunction B S hS i).unit.app F) :=
    (modulePullbackAdjunction B S hS i).unit_mono_of_L_faithful F
  exact inferInstanceAs (Mono (_ ≫ _))

/-! ### A morphism of affine objects of the site is an affine morphism of spaces -/

/-- **A morphism of affine objects of the site is an affine morphism of algebraic spaces.**
Every base change of it to an affine scheme of the site is the fibre product in the site, whose
underlying scheme is the fibre product of the underlying schemes and hence affine. -/
theorem isAffineHom_yoneda_map {U V : BigFppfOver B S hS} (f : U ⟶ V)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    IsAffineHom B S hS (yoneda.map f) := by
  let T := BigFppfOver.toScheme B S hS
  have hiso : ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} => X.size < B.cutoff) :=
    ⟨fun e h => (Scheme.size_congr e) ▸ h⟩
  have hlim : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} => X.size < B.cutoff) WalkingCospan := .mk' (by
    rintro _ ⟨D, hD⟩
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan D))]
    exact Scheme.size_pullback_lt _ _ (hD .left) (hD .right))
  let : HasPullbacks B.Schemes := inferInstance
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan T := by
    apply comp_preservesLimitsOfShape
  intro Z g
  let g' : Z.1 ⟶ V := yoneda.preimage g
  have hg : yoneda.map g' = g := yoneda.map_preimage g
  have hZ : IsAffine (T.obj Z.1) := Z.2
  have hW : IsAffineOver B S hS (pullback f g') :=
    IsAffine.of_isIso (PreservesPullback.iso T f g').hom
  refine ⟨⟨pullback f g', hW⟩, yoneda.map (pullback.fst f g'),
    pullback.snd f g', ?_⟩
  rw [← hg]
  exact (IsPullback.of_hasPullback f g').map yoneda

/-! ### Quasi-compactness of a representable algebraic space -/

/-- A scheme of the site with compact underlying space is a quasi-compact algebraic space:
the identity is a surjective étale chart. -/
theorem isQuasiCompactSpace_yoneda_of_compactSpace (V : BigFppfOver B S hS)
    (hV : CompactSpace ((BigFppfOver.toScheme B S hS).obj V)) :
    IsQuasiCompactSpace B S hS (yoneda.obj V) := by
  refine ⟨V, 𝟙 _, hV, ?_, ?_⟩
  · rw [show (𝟙 (yoneda.obj V)) = yoneda.map (𝟙 V) from (yoneda.map_id V).symm]
    exact (presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.Surjective.{u}) inferInstance (𝟙 V)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  · intro W c hc
    simpa using hc

/-! ### Weakly associated points of a monomorphism of modules -/

/-- The short exact sequence `0 → F → G → G/F → 0` attached to a monomorphism of
`𝒪_X`-modules. -/
def monoCokernelShortComplex {X : AlgebraicSpaces B S hS}
    {F G : Modules.{u, u} B S hS X.1 X.2} (α : F ⟶ G) :
    ShortComplex (Modules.{u, u} B S hS X.1 X.2) where
  X₁ := F
  X₂ := G
  X₃ := cokernel α
  f := α
  g := cokernel.π α
  zero := cokernel.condition α

/-- `AlgebraicGeometry.Space.monoCokernelShortComplex` of a monomorphism is short exact: the
`𝒪_X`-modules being an abelian category, a monomorphism is the kernel of its own cokernel. -/
theorem shortExact_monoCokernelShortComplex {X : AlgebraicSpaces B S hS}
    {F G : Modules.{u, u} B S hS X.1 X.2} (α : F ⟶ G) [Mono α] :
    (monoCokernelShortComplex B S hS α).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel (monoCokernelShortComplex B S hS α)
    (Abelian.monoIsKernelOfCokernel (f := α) _ (colimit.isColimit _))
  mono_f := inferInstanceAs (Mono α)
  epi_g := inferInstanceAs (Epi (cokernel.π α))

/-- **Stacks 0CTZ for a monomorphism.** Every weakly associated point of a submodule of an
`𝒪_X`-module is weakly associated to the ambient module. -/
theorem weaklyAssociatedPoints_subset_of_mono {X : AlgebraicSpaces B S hS}
    {F G : Modules.{u, u} B S hS X.1 X.2} (α : F ⟶ G) [Mono α] :
    weaklyAssociatedPoints B S hS X F ⊆ weaklyAssociatedPoints B S hS X G :=
  weaklyAssociatedPoints_subset_of_shortExact B S hS X (monoCokernelShortComplex B S hS α)
    (shortExact_monoCokernelShortComplex B S hS α)

/-! ### Stacks 0CU2 as a named hypothesis -/

/-- **Stacks 0CU2**, as a proposition: for every affine morphism `g : X ⟶ Y` of algebraic
spaces over `S` and every quasi-coherent `𝒪_X`-module `H`, each weakly associated point of
`g_*H` is the image of a weakly associated point of `H`.

It is carried as an explicit hypothesis by the results below, and it is the only input they
lack.  It is proved from the case of a target represented by an affine scheme of the site by
`AlgebraicGeometry.Space.affinePushforwardWeaklyAssociatedImage` in
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/SpaceAffinePushforward.lean`. -/
def AffinePushforwardWeaklyAssociatedImage : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y), IsAffineHom B S hS g.hom →
    ∀ H : Modules.{u, u} B S hS X.1 X.2, H.IsQuasicoherentOnSite →
      weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS g).obj H) ⊆
        pointsMap B S hS X.1 g.hom '' weaklyAssociatedPoints B S hS X H

/-! ### The case of an affine base and a quasi-compact source -/

/-- **Stacks 0CUQ when the target is an affine scheme and the source is quasi-compact**,
granting Stacks 0CU2.

This is steps 3 and 4 of the proof of the source: the quasi-compact algebraic space `X` has an
affine surjective étale chart `U`, the composite `U ⟶ V` is an affine morphism, the unit of the
pullback-pushforward adjunction along `U ⟶ X` is a monomorphism because the pullback is
faithful, so `f_*F` is a submodule of `(U ⟶ V)_*(F|_U)`; Stacks 0CTZ carries weakly associated
points along that inclusion and Stacks 0CU2 places them in the image of `|U| ⟶ |V|`, which is
contained in the image of `|X| ⟶ |V|`. -/
theorem not_isWeaklyAssociatedPoint_modulePushforward_of_isQuasiCompactSpace
    (h0CU2 : AffinePushforwardWeaklyAssociatedImage B S hS)
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)
    (hX : IsQuasiCompactSpace B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (y : points B S hS (schemeSpace V).1)
    (hy : y ∉ Set.range (pointsMap B S hS X.1 f.hom)) :
    ¬ IsWeaklyAssociatedPoint B S hS (schemeSpace V)
      ((modulePushforward B S hS f).obj F) y := by
  intro hw
  obtain ⟨U, i₀, hU, hsurj, hi⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).mp hX
  let i : schemeSpace U ⟶ X := ObjectProperty.homMk i₀
  have hiEt : IsEtale B S hS i.hom := hi
  have hfaith := faithful_modulePullback B S hS U i hiEt hsurj
  have hHqc : ((modulePullback B S hS i).obj F).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((modulePullbackIsoEtaleModulePullback B S hS i hiEt).app F).symm
      (isQuasicoherentOnSite_etaleModulePullback B S hS i hiEt F hF)
  have hmono := mono_modulePushforwardChartComparison B S hS i f hfaith F
  have haff : IsAffineHom B S hS (i ≫ f).hom := by
    have := hU
    have := hV
    rw [show (i ≫ f).hom = yoneda.map (yoneda.preimage (i ≫ f).hom) from
      (yoneda.map_preimage _).symm]
    exact isAffineHom_yoneda_map B S hS _
  have hw' : IsWeaklyAssociatedPoint B S hS (schemeSpace V)
      ((modulePushforward B S hS (i ≫ f)).obj ((modulePullback B S hS i).obj F)) y :=
    weaklyAssociatedPoints_subset_of_mono B S hS
      (modulePushforwardChartComparison B S hS i f F) hw
  obtain ⟨x, -, hx⟩ := h0CU2 (i ≫ f) haff _ hHqc hw'
  refine hy ⟨pointsMap B S hS (schemeSpace U).1 i.hom x, ?_⟩
  rw [← pointsMap_comp_apply]
  exact hx

/-! ### Stacks 0CUQ -/

/-- **Stacks 0CUQ**, granting Stacks 0CU2.

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over `S`, let `F` be a
quasi-coherent `𝒪_X`-module and let `y` be a point of `Y` outside the image of `|f|`. Then `y`
is not weakly associated to `f_*F`.

The hypothesis `h0CU2` is Stacks 0CU2, the inclusion `WeakAss(g_*H) ⊆ |g|(WeakAss(H))` for an
affine morphism `g`; it is the one step of the source's argument that this development does not
have. Quasi-separatedness of `f`, which the source assumes, is not needed: it enters the source
only through Stacks 03M9, and the argument below does not use quasi-coherence of the direct
image, so Stacks 03M9 is not needed either. -/
@[stacks 0CUQ "granting Stacks 0CU2"]
theorem not_isWeaklyAssociatedPoint_modulePushforward_of_notMem_range
    (h0CU2 : AffinePushforwardWeaklyAssociatedImage B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (y : points B S hS Y.1) (hy : y ∉ Set.range (pointsMap B S hS X.1 f.hom)) :
    ¬ IsWeaklyAssociatedPoint B S hS Y ((modulePushforward B S hS f).obj F) y := by
  intro hw
  obtain ⟨V, b, hV, hb, v, hv⟩ := exists_affine_etale_chart_at_point B S hS Y.1 Y.2 y
  let g : schemeSpace V ⟶ Y := ObjectProperty.homMk b
  have hg : IsEtale B S hS g.hom := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hb
  have hwV : IsWeaklyAssociatedPoint B S hS (schemeSpace V)
      ((etaleModulePullback B S hS g hg).obj ((modulePushforward B S hS f).obj F)) v :=
    (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS g hg _ v).2 (hv ▸ hw)
  let X' := AlgebraicSpaces.fiberProduct B S hS g f
  let f' : X' ⟶ schemeSpace V := ObjectProperty.homMk (pullback.fst g.hom f.hom)
  let i : X' ⟶ X := ObjectProperty.homMk (pullback.snd g.hom f.hom)
  have sq : IsPullback i f' f g := (AlgebraicSpaces.isPullback_fiberProduct B S hS g f).flip
  have hiEt : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  have hwX' : IsWeaklyAssociatedPoint B S hS (schemeSpace V)
      ((modulePushforward B S hS f').obj ((etaleModulePullback B S hS i hiEt).obj F)) v :=
    (isWeaklyAssociatedPoint_congr B S hS
      ((modulePushforwardEtaleBaseChangeIso B S hS i f' f g sq hg).app F) v).2 hwV
  have hVqc : IsQuasiCompactSpace B S hS (schemeSpace V).1 :=
    isQuasiCompactSpace_yoneda_of_compactSpace B S hS V (by have := hV; infer_instance)
  have hX'qc : IsQuasiCompactSpace B S hS X'.1 :=
    hfqc _ (schemeSpace V).2 hVqc g.hom
  have hnot : v ∉ Set.range (pointsMap B S hS X'.1 f'.hom) := by
    rintro ⟨x, hx⟩
    refine hy ⟨pointsMap B S hS X'.1 i.hom x, ?_⟩
    rw [← pointsMap_comp_apply,
      show i.hom ≫ f.hom = f'.hom ≫ g.hom from congrArg (fun k => k.hom) sq.w,
      pointsMap_comp_apply, hx]
    exact hv
  exact not_isWeaklyAssociatedPoint_modulePushforward_of_isQuasiCompactSpace B S hS h0CU2
    hV f' hX'qc _
    (isQuasicoherentOnSite_etaleModulePullback B S hS i hiEt F hF) v hnot hwX'

end AlgebraicGeometry.Space

end
