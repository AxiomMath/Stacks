module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforwardConjugation
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward

/-!
# The direct image along an affine open immersion as an open immersion of Quot functors

Let `B` be an algebraic space, let `π : X ⟶ Y` be an affine open immersion of algebraic spaces
which are separated and of finite presentation over `B`, and let `F` be a quasi-coherent
`𝒪_X`-module.  Stacks 0DP2 asserts that the morphism `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` of
Stacks 0DP1 is an open immersion.

Being an open immersion is a property of a morphism of presheaves of `Type u` on the schemes of
the site, while the Quot functor of Stacks 09TR takes values in `Type (u + 1)`, quotients being
recorded by subobjects.  The assertion is therefore made, as for the Hilbert functor in
`StacksFrontier/AlgebraicGeometry/Quot/HilbertFunctorOpenImmersion.lean`, about the morphism induced
on *given* models (`AlgebraicGeometry.Space.QuotSitePresheafModel`) of the two Quot presheaves of
the site; the existence of such models is the representability of the Quot functor, a separate
statement.

The morphism of models is a monomorphism because the direct image `π_{T,*}` along the base change
of an open immersion is fully faithful, which is Stacks 03LV, and a monomorphism of presheaves
whose range has open inverse image under every scheme-valued point of its target is an open
immersion.  The identification of those inverse images is where the source's omitted argument
lies: a member of `Quot_{π_*F/Y/B}(T)` is a direct image exactly when the support of the quotient
it names lies in `X_T`, and the source's hint is that this condition on `t ∈ T` holds in a
neighbourhood of every point at which it holds.

## Main definitions

* `AlgebraicGeometry.Space.QuotSitePresheafModel.familyEquiv` and
  `AlgebraicGeometry.Space.QuotSitePresheafModel.mapFrom`: a section of a model of the Quot
  presheaf is a quotient classified by the Quot functor, and a morphism into the Quot presheaf is
  read in a model.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.quotFamilyOverPushforward` and
  `AlgebraicGeometry.Space.QuotPushforwardSituation.quotSitePresheafPushforwardMap`: the morphism
  of Stacks 0DP1 read on the Quot presheaves of the site, and
  `AlgebraicGeometry.Space.QuotPushforwardSituation.quotModelMap` its reading in given models.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.SupportedInSource`: the condition
  `Supp(Q) ⊆ |X_T|` of the source's hint.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.AffineOpenImmersionQuotInputs`: the inputs of
  the source's omitted argument, each field naming what it stands for.

## Main results

* `AlgebraicGeometry.Space.QuotPushforwardSituation.isOpenImmersion_baseChangeOfMap`: the base
  change `π_T : X_T ⟶ Y_T` of an open immersion is an open immersion, by Stacks 02YW.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.quotFamilyOverPushforward_subobject`: the
  direct image of a quotient over a scheme of the site is the value of the morphism of Quot
  functors of Stacks 0DP1 at the test scheme the quotient lies over, so the morphism of models
  below is that morphism and not another.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.quotFamilyOverPushforward_injective` and
  `AlgebraicGeometry.Space.QuotPushforwardSituation.mono_quotModelMap`: the direct image of
  quotients over a scheme of the site is injective, so the morphism of models is a monomorphism.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.exists_quotFamilyOverPushforward_iff` and
  `AlgebraicGeometry.Space.QuotPushforwardSituation.mem_range_quotModelMap_iff`: a section of the
  model of `Quot_{π_*F/Y/B}` is in the range exactly when the quotient it names is the direct
  image of a quotient of `F`.
* **Stacks 0DP2**, the morphism of Quot functors induced by an affine open immersion is an open
  immersion, is
  `AlgebraicGeometry.Space.QuotPushforwardSituation.isOpenImmersion_pushforwardQuotModelMap`, in
  `StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionDirectImage`.

## Implementation notes

**The inputs of the source's omitted argument are carried as hypotheses.**  The source proves
Stacks 0DP2 only by the hint that the condition `Supp(Q_t) ⊆ |X_t|` on a member of
`Quot_{π_*F/Y/B}(T)` holds in a neighbourhood of every point at which it holds.  Two assertions
are needed to turn that into an open immersion, and they are the fields of
`AlgebraicGeometry.Space.QuotPushforwardSituation.AffineOpenImmersionQuotInputs`:

* that a member of `Quot_{π_*F/Y/B}(T)` is the direct image of a member of `Quot_{F/X/B}(T)`
  exactly when that support condition holds.  Its substance is the inverse construction — a
  quotient of `G_T` supported in `X_T` is the direct image of a quotient of `F_T` — which rests
  on the identification `π_T^*π_{T,*} ≅ 𝟭` for quotients, recorded as unavailable in
  `StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorOpenImmersionDirectImage.lean`, whose attribute
  on `AlgebraicGeometry.Space.QuotOpenImmersionSituation.quotFunctorMap` says that the companion
  tag Stacks 0DP3 is covered there only for the morphism and not for its being an open immersion;
* that the locus of the support condition is an open subspace of the test scheme.  This is the
  source's hint itself; no form of it is available in this development.

What is proved here is everything else: the morphism of Quot presheaves of the site and its
reading in models, its being a monomorphism — which is Stacks 03LV through
`AlgebraicGeometry.Space.fullyFaithfulModulePushforwardOfIsOpenImmersion`, and needs no
hypothesis — the identification of the range of its components, and the passage from those data
to an open immersion by
`AlgebraicGeometry.Space.isOpenImmersion_of_isOpenSubspace_range_preimage`.

**The affineness of the open immersion is a field of the standing data of Stacks 0DP1.**  That
standing data asks `π` to be affine and quasi-finite; the source's "affine open immersion" is
therefore the situation together with the hypothesis `hπ` that `π` is an open immersion.

**Quotients over a scheme of the site are compared field by field.**  A quotient over `T` is a
morphism `T ⟶ B` together with a subobject of `F_T` for the resulting test scheme, so the
subobject is typed through the morphism to `B` and equalities of quotients are heterogeneous in
it.  Every proof below therefore destructures the quotients and unfolds the direct image to a
structure literal before comparing, which is what
`AlgebraicGeometry.Space.QuotFamilyOver.baseChange_id` and its companions do in
`StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorPresheaf.lean`.

## References

* [Stacks Project, Tag 0DP2](https://stacks.math.columbia.edu/tag/0DP2)
* [Stacks Project, Tag 0DP1](https://stacks.math.columbia.edu/tag/0DP1)
* [Stacks Project, Tag 0DP3](https://stacks.math.columbia.edu/tag/0DP3)
* [Stacks Project, Tag 0DPE](https://stacks.math.columbia.edu/tag/0DPE)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Quotients over a scheme of the site -/

/-- Two quotients over a scheme of the site which agree have the same kernel; the kernel is typed
through the morphism to the base, so its equality is heterogeneous. -/
theorem QuotFamilyOver.subobject_heq {D : QuotSituation B S hS} {T : BigFppfOver B S hS}
    {a b : QuotFamilyOver D T} (hab : a = b) : a.subobject ≍ b.subobject := by
  subst hab
  rfl

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS} (M : QuotSitePresheafModel D)

/-- A section of a model of the Quot presheaf over a scheme of the site is the same thing as a
quotient classified by the Quot functor over that scheme. -/
def familyEquiv (T : BigFppfOver B S hS) :
    M.presheaf.obj (Opposite.op T) ≃ QuotFamilyOver D T :=
  Equiv.ulift.symm.trans (M.iso.app (Opposite.op T)).toEquiv

/-- The quotient a section of a model names is its image under the comparison of the model with
the Quot presheaf. -/
theorem familyEquiv_apply (T : BigFppfOver B S hS) (z : M.presheaf.obj (Opposite.op T)) :
    M.familyEquiv T z = M.iso.hom.app (Opposite.op T) (ULift.up z) := rfl

/-- The identification of the sections of a model with the quotients is compatible with
restriction. -/
theorem familyEquiv_map {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (z : M.presheaf.obj (Opposite.op T)) :
    M.familyEquiv T' (M.presheaf.map g.op z) = (M.familyEquiv T z).baseChange g := by
  have h := types_congr_hom (M.iso.hom.naturality g.op) (ULift.up.{u + 1} z)
  exact h

/-- Transport a morphism into the Quot presheaf from a universe-lifted small presheaf into a
model of the Quot presheaf. -/
def mapFrom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⋙ uliftFunctor.{u + 1, u} ⟶ D.quotSitePresheaf) : F ⟶ M.presheaf where
  app T := ↾fun z ↦ (M.iso.inv.app T (p.app T ⟨z⟩)).down
  naturality {T T'} g := by
    ext z
    have h := types_congr_hom ((p ≫ M.iso.inv).naturality g) (ULift.up.{u + 1} z)
    exact congrArg ULift.down h

end QuotSitePresheafModel

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-! ### The base change of the open immersion -/

/-- **The base change of an open immersion is an open immersion**, by Stacks 02YW, applied to the
base change `π_T : X_T ⟶ Y_T` of the morphism of the situation. -/
theorem isOpenImmersion_baseChangeOfMap (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) : IsOpenImmersion B S hS (D.baseChangeOfMap T).hom :=
  isOpenImmersion_of_isPullback B S hS (D.isPullback_baseChangeOfMap T).flip hπ

/-- **Stacks 03LV for the base change of the open immersion**: the direct image `π_{T,*}` of
`𝒪_{X_T}`-modules is fully faithful, restriction to the open subspace being a left inverse of
it. -/
def fullyFaithfulPushforwardOfIsOpenImmersion (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) :
    (modulePushforward B S hS (D.baseChangeOfMap T)).FullyFaithful :=
  fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS (D.baseChangeOfMap T)
    (D.isOpenImmersion_baseChangeOfMap hπ T)

/-! ### The morphism of Quot presheaves of the site -/

/-- The direct image of a quotient over a scheme of the site: the same morphism to the base, and
the direct image of its kernel.  This is the morphism of Stacks 0DP1 read on the quotients over
the schemes of the site. -/
def quotFamilyOverPushforward (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (T : BigFppfOver B S hS)
    (x : QuotFamilyOver D.sourceSituation T) : QuotFamilyOver (D.targetSituation h) T where
  toBase := x.toBase
  subobject := D.pushforwardQuotient h I.comparison (CostructuredArrow.mk x.toBase) x.subobject
  mem := D.pushforwardQuotient_mem h I (CostructuredArrow.mk x.toBase) x.subobject x.mem

/-- **The direct image of a quotient over a scheme of the site is the morphism of Quot functors
of Stacks 0DP1 at the test scheme the quotient lies over**: the kernel recording the image
quotient is the value there of
`AlgebraicGeometry.Space.QuotPushforwardSituation.quotFunctorMap`. -/
theorem quotFamilyOverPushforward_subobject
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (T : BigFppfOver B S hS)
    (x : QuotFamilyOver D.sourceSituation T) :
    (D.quotFamilyOverPushforward h I T x).subobject =
      (((D.quotFunctorMap h I).app (Opposite.op (CostructuredArrow.mk x.toBase)))
        ⟨x.subobject, x.mem⟩).1 :=
  rfl

/-- Taking the direct image of a quotient commutes with base change along a morphism of schemes
of the site; this is the compatibility of the direct image with pullback carried by
Stacks 0DP1. -/
theorem quotFamilyOverPushforward_baseChange
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D.sourceSituation T) :
    D.quotFamilyOverPushforward h I T' (x.baseChange g) =
      (D.quotFamilyOverPushforward h I T x).baseChange g := by
  obtain ⟨b, K, hK⟩ := x
  simp only [quotFamilyOverPushforward, QuotFamilyOver.baseChange]
  exact QuotFamilyOver.ext rfl
    (heq_of_eq (I.pushforwardQuotient_quotientPullback (QuotFamilyOver.restrict g b) K))

/-- The morphism of Quot presheaves of the site induced by the direct image: over a scheme of the
site it sends a quotient to its direct image.  This is the morphism of Stacks 0DP1, read on the
presheaves of the site rather than on the functors on the test schemes. -/
def quotSitePresheafPushforwardMap (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) :
    D.sourceSituation.quotSitePresheaf ⟶ (D.targetSituation h).quotSitePresheaf where
  app T := TypeCat.ofHom fun x => D.quotFamilyOverPushforward h I T.unop x
  naturality {T T'} g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact D.quotFamilyOverPushforward_baseChange h I g.unop x

/-- The direct image of quotients over a scheme of the site is injective, by full faithfulness of
the direct image along the base change of the open immersion (Stacks 03LV). -/
theorem quotFamilyOverPushforward_injective
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : BigFppfOver B S hS) :
    Function.Injective (D.quotFamilyOverPushforward h I T) := by
  rintro ⟨ab, aK, aM⟩ ⟨bb, bK, bM⟩ hab
  simp only [quotFamilyOverPushforward] at hab
  have hbase : ab = bb := congrArg QuotFamilyOver.toBase hab
  subst hbase
  have hK : aK = bK :=
    D.pushforwardQuotient_injective_of_fullyFaithful h I.comparison (CostructuredArrow.mk ab)
      (D.fullyFaithfulPushforwardOfIsOpenImmersion hπ (CostructuredArrow.mk ab))
      (eq_of_heq (QuotFamilyOver.subobject_heq hab))
  subst hK
  rfl

/-- A quotient over a scheme of the site is a direct image exactly when its kernel is the direct
image of a member of `Quot_{F/X/B}` over the test scheme it lies over. -/
theorem exists_quotFamilyOverPushforward_iff
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (T : BigFppfOver B S hS)
    (y : QuotFamilyOver (D.targetSituation h) T) :
    (∃ x, D.quotFamilyOverPushforward h I T x = y) ↔
      ∃ K ∈ D.sourceSituation.properlySupportedQuotients (CostructuredArrow.mk y.toBase),
        D.pushforwardQuotient h I.comparison (CostructuredArrow.mk y.toBase) K = y.subobject := by
  obtain ⟨b, K', hK'⟩ := y
  dsimp only
  constructor
  · rintro ⟨⟨b₂, K₂, hK₂⟩, hx⟩
    simp only [quotFamilyOverPushforward] at hx
    have hbase : b₂ = b := congrArg QuotFamilyOver.toBase hx
    subst hbase
    exact ⟨K₂, hK₂, eq_of_heq (QuotFamilyOver.subobject_heq hx)⟩
  · rintro ⟨K, hK, hKy⟩
    refine ⟨⟨b, K, hK⟩, ?_⟩
    simp only [quotFamilyOverPushforward]
    exact QuotFamilyOver.ext rfl (heq_of_eq hKy)

/-! ### The morphism read in models of the Quot presheaves -/

/-- The morphism of Quot presheaves induced by the direct image, read in given models of the two
Quot presheaves of the site. -/
def quotModelMap (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h)
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel (D.targetSituation h)) : MX.presheaf ⟶ MY.presheaf :=
  MY.mapFrom (MX.iso.hom ≫ D.quotSitePresheafPushforwardMap h I)

/-- The morphism of models is the morphism of Quot presheaves: on a section of the model of
`Quot_{F/X/B}` it takes the direct image of the corresponding quotient. -/
theorem familyEquiv_quotModelMap (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h)
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel (D.targetSituation h)) (T : BigFppfOver B S hS)
    (z : MX.presheaf.obj (Opposite.op T)) :
    MY.familyEquiv T ((D.quotModelMap h I MX MY).app (Opposite.op T) z) =
      D.quotFamilyOverPushforward h I T (MX.familyEquiv T z) :=
  types_congr_hom (MY.iso.inv_hom_id_app (Opposite.op T))
    ((MX.iso.hom ≫ D.quotSitePresheafPushforwardMap h I).app (Opposite.op T) (ULift.up z))

/-- The morphism of models is a monomorphism, the direct image of quotients being injective. -/
theorem mono_quotModelMap (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) (hπ : IsOpenImmersion B S hS D.π.hom)
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel (D.targetSituation h)) :
    Mono (D.quotModelMap h I MX MY) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro a b hab
  have hq := congrArg (MY.familyEquiv T.unop) hab
  rw [D.familyEquiv_quotModelMap, D.familyEquiv_quotModelMap] at hq
  exact (MX.familyEquiv T.unop).injective
    (D.quotFamilyOverPushforward_injective h I hπ T.unop hq)

/-- A section of the model of `Quot_{π_*F/Y/B}` is in the range of the induced morphism exactly
when the quotient it corresponds to is the direct image of a quotient of `F`. -/
theorem mem_range_quotModelMap_iff (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h)
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel (D.targetSituation h)) (T : BigFppfOver B S hS)
    (z : MY.presheaf.obj (Opposite.op T)) :
    z ∈ Set.range ((D.quotModelMap h I MX MY).app (Opposite.op T)) ↔
      ∃ x, D.quotFamilyOverPushforward h I T x = MY.familyEquiv T z := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨MX.familyEquiv T w, (D.familyEquiv_quotModelMap h I MX MY T w).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(MX.familyEquiv T).symm x, ?_⟩
    apply (MY.familyEquiv T).injective
    rw [D.familyEquiv_quotModelMap, Equiv.apply_symm_apply, hx]

/-! ### The support condition of the source's hint, and the inputs carried -/

/-- **The condition `Supp(Q) ⊆ |X_T|` of the source's hint**: the support of the quotient of
`G_T` by a submodule is contained in the image of the points of `X_T`. -/
def SupportedInSource (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (T : SchemesOver D.base) (K : Subobject ((D.targetSituation h).baseChangeModule T)) : Prop :=
  (D.targetSituation h).support T ((D.targetSituation h).quotientModule T K) ⊆
    Set.range (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom)

/-- The support condition on a quotient over a scheme of the site, read over the test scheme the
quotient lies over. -/
def SupportedInSourceOver (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    {T : BigFppfOver B S hS} (y : QuotFamilyOver (D.targetSituation h) T) : Prop :=
  D.SupportedInSource h (CostructuredArrow.mk y.toBase) y.subobject

/-- **The inputs of the omitted argument of Stacks 0DP2**, bundled.

The first field is the characterization of the direct images among the members of
`Quot_{π_*F/Y/B}(T)` by the support condition.  Its substance is the inverse construction: a
quotient of `G_T` whose support lies in `X_T` is the direct image of a quotient of `F_T`.  That
construction rests on the identification `π_T^*π_{T,*} ≅ 𝟭` for quotients, which this development
does not have; `StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorOpenImmersionDirectImage.lean`
records it as missing, and the attribute there on
`AlgebraicGeometry.Space.QuotOpenImmersionSituation.quotFunctorMap` says that the companion tag
Stacks 0DP3 is covered only for the morphism and not for its being an open immersion.

The remaining three fields are **the source's hint**, which is all the source gives for
Stacks 0DP2: the locus in a scheme of the site over which the support condition holds for the
base changes of a quotient is an open subspace of it.  No form of that assertion is available in
this development. -/
structure AffineOpenImmersionQuotInputs (D : QuotPushforwardSituation B S hS)
    (h : SchemeTargetAffinePushforwardQuasicoherent B S hS)
    (I : D.AffinePushforwardQuotInputs h) where
  /-- **The inverse construction**: a member of `Quot_{π_*F/Y/B}(T)` is a direct image exactly
  when the support of the quotient it names lies in `X_T`. -/
  exists_pushforwardQuotient_iff : ∀ (T : SchemesOver D.base)
      (K : Subobject ((D.targetSituation h).baseChangeModule T)),
    K ∈ (D.targetSituation h).properlySupportedQuotients T →
      ((∃ K' ∈ D.sourceSituation.properlySupportedQuotients T,
          D.pushforwardQuotient h I.comparison T K' = K) ↔ D.SupportedInSource h T K)
  /-- **The source's hint**: the locus of the support condition, as a subfunctor of a scheme of
  the site. -/
  locus : ∀ (T : BigFppfOver B S hS), QuotFamilyOver (D.targetSituation h) T →
    Subfunctor (yoneda.obj T)
  /-- **The source's hint**: that locus is cut out by the support condition on the base changes
  of the quotient. -/
  mem_locus_iff : ∀ (T : BigFppfOver B S hS) (y : QuotFamilyOver (D.targetSituation h) T)
      (U : (BigFppfOver B S hS)ᵒᵖ) (g : U.unop ⟶ T),
    g ∈ (locus T y).obj U ↔ D.SupportedInSourceOver h (y.baseChange g)
  /-- **The source's hint**: that locus is an open subspace. -/
  isOpenSubspace_locus : ∀ (T : BigFppfOver B S hS)
      (y : QuotFamilyOver (D.targetSituation h) T), IsOpenSubspace B S hS (locus T y)

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
