module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPushforwardSupplement

/-!
# Variants of pushforward of Quot families along affine open immersions

The declarations below extend
`StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionPushforward` and are kept in a
module of their own so that that module stays unchanged. A primed name `X'` is a variant of the
declaration `X` there.

## Main declarations

* `quotFamilyOverPushforward'`
* `quotFamilyOverPushforward_subobject'`
* `quotFamilyOverPushforward_baseChange'`
* `quotSitePresheafPushforwardMap'`
* `quotFamilyOverPushforward_injective'`
* `exists_quotFamilyOverPushforward_iff'`
* `quotModelMap'`
* `familyEquiv_quotModelMap'`
* `mono_quotModelMap'`
* `mem_range_quotModelMap_iff'`
* `SupportedInSource'`
* `SupportedInSourceOver'`
* `AffineOpenImmersionQuotInputs'`
* `isOpenImmersion_quotModelMap'`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS} (M : QuotSitePresheafModel D)

end QuotSitePresheafModel

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-- The direct image of a quotient over a scheme of the site: the same morphism to the base, and
the direct image of its kernel.  This is the morphism of Stacks 0DP1 read on the quotients over
the schemes of the site. -/
def quotFamilyOverPushforward' (I : D.AffinePushforwardQuotInputs') (T : BigFppfOver B S hS)
    (x : QuotFamilyOver D.sourceSituation T) : QuotFamilyOver D.targetSituation' T where
  toBase := x.toBase
  subobject := D.pushforwardQuotient' I.comparison (CostructuredArrow.mk x.toBase) x.subobject
  mem := D.pushforwardQuotient_mem' I (CostructuredArrow.mk x.toBase) x.subobject x.mem

/-- **The direct image of a quotient over a scheme of the site is the morphism of Quot functors
of Stacks 0DP1 at the test scheme the quotient lies over**: the kernel recording the image
quotient is the value there of
`AlgebraicGeometry.Space.QuotPushforwardSituation.quotFunctorMap'`. -/
theorem quotFamilyOverPushforward_subobject' (I : D.AffinePushforwardQuotInputs')
    (T : BigFppfOver B S hS)
    (x : QuotFamilyOver D.sourceSituation T) :
    (D.quotFamilyOverPushforward' I T x).subobject =
      (((D.quotFunctorMap' I).app (Opposite.op (CostructuredArrow.mk x.toBase)))
        ⟨x.subobject, x.mem⟩).1 :=
  rfl

/-- Taking the direct image of a quotient commutes with base change along a morphism of schemes
of the site; this is the compatibility of the direct image with pullback carried by
Stacks 0DP1. -/
theorem quotFamilyOverPushforward_baseChange' (I : D.AffinePushforwardQuotInputs')
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D.sourceSituation T) :
    D.quotFamilyOverPushforward' I T' (x.baseChange g) =
      (D.quotFamilyOverPushforward' I T x).baseChange g := by
  obtain ⟨b, K, hK⟩ := x
  simp only [quotFamilyOverPushforward', QuotFamilyOver.baseChange]
  exact QuotFamilyOver.ext rfl
    (heq_of_eq (I.pushforwardQuotient_quotientPullback (QuotFamilyOver.restrict g b) K))

/-- The morphism of Quot presheaves of the site induced by the direct image: over a scheme of the
site it sends a quotient to its direct image.  This is the morphism of Stacks 0DP1, read on the
presheaves of the site rather than on the functors on the test schemes. -/
def quotSitePresheafPushforwardMap' (I : D.AffinePushforwardQuotInputs') :
    D.sourceSituation.quotSitePresheaf ⟶ D.targetSituation'.quotSitePresheaf where
  app T := TypeCat.ofHom fun x => D.quotFamilyOverPushforward' I T.unop x
  naturality {T T'} g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact D.quotFamilyOverPushforward_baseChange' I g.unop x

/-- The direct image of quotients over a scheme of the site is injective, by full faithfulness of
the direct image along the base change of the open immersion (Stacks 03LV). -/
theorem quotFamilyOverPushforward_injective' (I : D.AffinePushforwardQuotInputs')
    (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : BigFppfOver B S hS) :
    Function.Injective (D.quotFamilyOverPushforward' I T) := by
  rintro ⟨ab, aK, aM⟩ ⟨bb, bK, bM⟩ hab
  simp only [quotFamilyOverPushforward'] at hab
  obtain rfl : ab = bb := congrArg QuotFamilyOver.toBase hab
  obtain rfl : aK = bK :=
    D.pushforwardQuotient_injective_of_fullyFaithful' I.comparison (CostructuredArrow.mk ab)
      (D.fullyFaithfulPushforwardOfIsOpenImmersion hπ (CostructuredArrow.mk ab))
      (eq_of_heq (QuotFamilyOver.subobject_heq hab))
  rfl

/-- A quotient over a scheme of the site is a direct image exactly when its kernel is the direct
image of a member of `Quot_{F/X/B}` over the test scheme it lies over. -/
theorem exists_quotFamilyOverPushforward_iff' (I : D.AffinePushforwardQuotInputs')
    (T : BigFppfOver B S hS)
    (y : QuotFamilyOver D.targetSituation' T) :
    (∃ x, D.quotFamilyOverPushforward' I T x = y) ↔
      ∃ K ∈ D.sourceSituation.properlySupportedQuotients (CostructuredArrow.mk y.toBase),
        D.pushforwardQuotient' I.comparison (CostructuredArrow.mk y.toBase) K = y.subobject := by
  obtain ⟨b, K', hK'⟩ := y
  dsimp only
  constructor
  · rintro ⟨⟨b₂, K₂, hK₂⟩, hx⟩
    simp only [quotFamilyOverPushforward'] at hx
    obtain rfl : b₂ = b := congrArg QuotFamilyOver.toBase hx
    exact ⟨K₂, hK₂, eq_of_heq (QuotFamilyOver.subobject_heq hx)⟩
  · rintro ⟨K, hK, hKy⟩
    refine ⟨⟨b, K, hK⟩, ?_⟩
    simp only [quotFamilyOverPushforward']
    exact QuotFamilyOver.ext rfl (heq_of_eq hKy)

/-- The morphism of Quot presheaves induced by the direct image, read in given models of the two
Quot presheaves of the site. -/
def quotModelMap' (I : D.AffinePushforwardQuotInputs')
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation') : MX.presheaf ⟶ MY.presheaf :=
  MY.mapFrom (MX.iso.hom ≫ D.quotSitePresheafPushforwardMap' I)

/-- The morphism of models is the morphism of Quot presheaves: on a section of the model of
`Quot_{F/X/B}` it takes the direct image of the corresponding quotient. -/
theorem familyEquiv_quotModelMap' (I : D.AffinePushforwardQuotInputs')
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation') (T : BigFppfOver B S hS)
    (z : MX.presheaf.obj (Opposite.op T)) :
    MY.familyEquiv T ((D.quotModelMap' I MX MY).app (Opposite.op T) z) =
      D.quotFamilyOverPushforward' I T (MX.familyEquiv T z) :=
  types_congr_hom (MY.iso.inv_hom_id_app (Opposite.op T))
    ((MX.iso.hom ≫ D.quotSitePresheafPushforwardMap' I).app (Opposite.op T) (ULift.up z))

/-- The morphism of models is a monomorphism, the direct image of quotients being injective. -/
theorem mono_quotModelMap' (I : D.AffinePushforwardQuotInputs')
    (hπ : IsOpenImmersion B S hS D.π.hom)
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation') :
    Mono (D.quotModelMap' I MX MY) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro a b hab
  have hq := congrArg (MY.familyEquiv T.unop) hab
  rw [D.familyEquiv_quotModelMap', D.familyEquiv_quotModelMap'] at hq
  exact (MX.familyEquiv T.unop).injective
    (D.quotFamilyOverPushforward_injective' I hπ T.unop hq)

/-- A section of the model of `Quot_{π_*F/Y/B}` is in the range of the induced morphism exactly
when the quotient it corresponds to is the direct image of a quotient of `F`. -/
theorem mem_range_quotModelMap_iff' (I : D.AffinePushforwardQuotInputs')
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation') (T : BigFppfOver B S hS)
    (z : MY.presheaf.obj (Opposite.op T)) :
    z ∈ Set.range ((D.quotModelMap' I MX MY).app (Opposite.op T)) ↔
      ∃ x, D.quotFamilyOverPushforward' I T x = MY.familyEquiv T z := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨MX.familyEquiv T w, (D.familyEquiv_quotModelMap' I MX MY T w).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(MX.familyEquiv T).symm x, ?_⟩
    apply (MY.familyEquiv T).injective
    rw [D.familyEquiv_quotModelMap', Equiv.apply_symm_apply, hx]

/-- **The condition `Supp(Q) ⊆ |X_T|` of the source's hint**: the support of the quotient of
`G_T` by a submodule is contained in the image of the points of `X_T`. -/
def SupportedInSource' (T : SchemesOver D.base)
    (K : Subobject (D.targetSituation'.baseChangeModule T)) : Prop :=
  D.targetSituation'.support T (D.targetSituation'.quotientModule T K) ⊆
    Set.range (pointsMap B S hS (D.sourceSituation.space T).1 (D.baseChangeOfMap T).hom)

/-- The support condition on a quotient over a scheme of the site, read over the test scheme the
quotient lies over. -/
def SupportedInSourceOver' {T : BigFppfOver B S hS}
    (y : QuotFamilyOver D.targetSituation' T) : Prop :=
  D.SupportedInSource' (CostructuredArrow.mk y.toBase) y.subobject

/-- **The inputs of the omitted argument of Stacks 0DP2**, bundled.

The first field is the characterization of the direct images among the members of
`Quot_{π_*F/Y/B}(T)` by the support condition.  Its substance is the inverse construction: a
quotient of `G_T` whose support lies in `X_T` is the direct image of a quotient of `F_T`.  That
construction rests on the identification `π_T^*π_{T,*} ≅ 𝟭` for quotients, which this development
does not have; `StacksFrontier/AlgebraicGeometry/Quot/QuotFunctorOpenImmersionDirectImage.lean`
records it as missing, and the attribute there on
`AlgebraicGeometry.Space.QuotOpenImmersionSituation.quotFunctorMap'` says that the companion tag
Stacks 0DP3 is covered only for the morphism and not for its being an open immersion.

The remaining three fields are **the source's hint**, which is all the source gives for
Stacks 0DP2: the locus in a scheme of the site over which the support condition holds for the
base changes of a quotient is an open subspace of it.  No form of that assertion is available in
this development. -/
structure AffineOpenImmersionQuotInputs' (D : QuotPushforwardSituation B S hS)
    (I : D.AffinePushforwardQuotInputs') where
  /-- **The inverse construction**: a member of `Quot_{π_*F/Y/B}(T)` is a direct image exactly
  when the support of the quotient it names lies in `X_T`. -/
  exists_pushforwardQuotient_iff : ∀ (T : SchemesOver D.base)
      (K : Subobject (D.targetSituation'.baseChangeModule T)),
    K ∈ D.targetSituation'.properlySupportedQuotients T →
      ((∃ K' ∈ D.sourceSituation.properlySupportedQuotients T,
          D.pushforwardQuotient' I.comparison T K' = K) ↔ D.SupportedInSource' T K)
  /-- **The source's hint**: the locus of the support condition, as a subfunctor of a scheme of
  the site. -/
  locus : ∀ (T : BigFppfOver B S hS), QuotFamilyOver D.targetSituation' T →
    Subfunctor (yoneda.obj T)
  /-- **The source's hint**: that locus is cut out by the support condition on the base changes
  of the quotient. -/
  mem_locus_iff : ∀ (T : BigFppfOver B S hS) (y : QuotFamilyOver D.targetSituation' T)
      (U : (BigFppfOver B S hS)ᵒᵖ) (g : U.unop ⟶ T),
    g ∈ (locus T y).obj U ↔ D.SupportedInSourceOver' (y.baseChange g)
  /-- **The source's hint**: that locus is an open subspace. -/
  isOpenSubspace_locus : ∀ (T : BigFppfOver B S hS)
      (y : QuotFamilyOver D.targetSituation' T), IsOpenSubspace B S hS (locus T y)

/-- **Stacks 0DP2.**  The morphism of Quot functors `Quot_{F/X/B} ⟶ Quot_{π_*F/Y/B}` induced by
the direct image along an affine open immersion is an open immersion, read in given models of the
two Quot presheaves of the site.

It is a monomorphism by full faithfulness of `π_{T,*}` (Stacks 03LV), so by
`AlgebraicGeometry.Space.isOpenImmersion_of_isOpenSubspace_range_preimage` it suffices that its
range have open inverse image under every scheme-valued point of the model of
`Quot_{π_*F/Y/B}`.  Such a point is a quotient `Q` of `G_T`, and a morphism `g : U ⟶ T` lies in
that inverse image exactly when the base change of `Q` to `U` is a direct image, that is — by the
first carried input — exactly when its support lies in `X_U`; that locus is open by the carried
form of the source's hint. -/
theorem isOpenImmersion_quotModelMap' (I : D.AffinePushforwardQuotInputs')
    (hπ : IsOpenImmersion B S hS D.π.hom)
    (J : D.AffineOpenImmersionQuotInputs' I)
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.targetSituation') :
    IsOpenImmersion B S hS (D.quotModelMap' I MX MY) := by
  have := D.mono_quotModelMap' I hπ MX MY
  apply isOpenImmersion_of_isOpenSubspace_range_preimage
  intro T q
  set y := MY.familyEquiv T (yonedaEquiv q)
  have heq : (Subfunctor.range (D.quotModelMap' I MX MY)).preimage q = J.locus T y := by
    ext U g
    have hqg : q.app U g = MY.presheaf.map (Quiver.Hom.op g) (yonedaEquiv q) := by
      have hnat := NatTrans.naturality_apply q (Quiver.Hom.op g) (𝟙 T)
      rw [yonedaEquiv_apply]
      simpa using hnat
    show q.app U g ∈ Set.range ((D.quotModelMap' I MX MY).app U) ↔
      g ∈ (J.locus T y).obj U
    rw [hqg, D.mem_range_quotModelMap_iff' I MX MY, QuotSitePresheafModel.familyEquiv_map,
      D.exists_quotFamilyOverPushforward_iff' I]
    exact (J.exists_pushforwardQuotient_iff _ _ (y.baseChange g).mem).trans
      (J.mem_locus_iff T y U g).symm
  rw [heq]
  exact J.isOpenSubspace_locus T y

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
