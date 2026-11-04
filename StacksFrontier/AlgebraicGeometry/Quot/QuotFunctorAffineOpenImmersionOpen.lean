module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionSupport
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSitePresheafCanonicalModel

/-!
# A direct image of Quot presheaves along an affine open immersion is an open immersion

Let `π : X ⟶ Y` be an affine open immersion of algebraic spaces which are separated and of finite
presentation over an algebraic space `B`, let `F` be a quasi-coherent `𝒪_X`-module and write
`G = π_*F`.  Granted that the direct image `G_T ⟶ π_{T,*}F_T ⟶ π_{T,*}Q'` of a member
`F_T ⟶ Q'` of `Quot_{F/X/B}(T)` is a member of `Quot_{G/Y/B}(T)`, the direct image of quotients
is a morphism of Quot presheaves of the site `Quot_{F/X/B} ⟶ Quot_{G/Y/B}`, and it is an open
immersion when read in models of the two presheaves in the universe of the site.

* It is a monomorphism: the quotient `F_T ⟶ Q'` is recovered from its direct image by
  restriction to `X_T`, restriction being exact and a left inverse of the direct image
  (Stacks 03LV).
* A quotient `G_T ⟶ Q` lies in its range exactly when `Supp(Q) ⊆ |X_T|`, and the locus of `T`
  over which this holds after base change is open
  (`AlgebraicGeometry.Space.QuotSituation.isOpenSubspace_supportLocus`).

## Main definitions

In the namespace `AlgebraicGeometry.Space`:

* `QuotPushforwardSituation.directImageQuotFamilyOver`: the direct image of a quotient over a
  scheme of the site.
* `QuotPushforwardSituation.directImageQuotSitePresheafMap`: the direct image of quotients as a
  morphism of Quot presheaves of the site.

## Main results

* `QuotPushforwardSituation.directImageQuotFamilyOver_injective`: the direct image of quotients
  over a scheme of the site is injective.
* `QuotPushforwardSituation.exists_directImageQuotFamilyOver_eq_iff`: its range is cut out by the
  support condition.
* `QuotPushforwardSituation.isOpenImmersion_mapFrom_directImageQuotSitePresheafMap`: the direct
  image of quotients is an open immersion in any models of the two presheaves.

## References

* [Stacks Project, Tag 0DP2](https://stacks.math.columbia.edu/tag/0DP2)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The modules here have their sections in the universe of the schemes, which the ambient-universe
-- abelian structure of `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` cannot describe; left
-- in place it is selected ahead of `SheafOfModules.instAbelian` and leaves the module universe
-- of the subobjects and cokernels below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-- The condition that the direct image of every member of `Quot_{F/X/B}(T)` is a member of
`Quot_{π_*F/Y/B}(T)`, which is Stacks 0DP1 on objects. -/
abbrev DirectImageQuotientMem : Prop :=
  ∀ (T : SchemesOver D.base) (K' : Subobject (D.sourceSituation.baseChangeModule T)),
    K' ∈ D.sourceSituation.properlySupportedQuotients T →
      D.directImageQuotient T K' ∈ D.directImageSituation.properlySupportedQuotients T

/-- **The direct image of a quotient over a scheme of the site**: a quotient `F_T ⟶ Q'` over the
test scheme `T ⟶ B` goes to the quotient `G_T ⟶ π_{T,*}Q'` over the same test scheme. -/
def directImageQuotFamilyOver (hmem : D.DirectImageQuotientMem) {T : BigFppfOver B S hS}
    (x : QuotFamilyOver D.sourceSituation T) : QuotFamilyOver D.directImageSituation T where
  toBase := x.toBase
  subobject := D.directImageQuotient (CostructuredArrow.mk x.toBase) x.subobject
  mem := hmem (CostructuredArrow.mk x.toBase) x.subobject x.mem

/-- Taking the direct image of a quotient over a scheme of the site commutes with base change
along a morphism of schemes of the site (part (b) of the proof of Stacks 0DN9). -/
theorem directImageQuotFamilyOver_baseChange (hmem : D.DirectImageQuotientMem)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : QuotFamilyOver D.sourceSituation T) :
    D.directImageQuotFamilyOver hmem (x.baseChange g) =
      (D.directImageQuotFamilyOver hmem x).baseChange g := by
  obtain ⟨b, K, hK⟩ := x
  simp only [directImageQuotFamilyOver, QuotFamilyOver.baseChange]
  have key := D.directImageQuotient_quotientPullback (QuotFamilyOver.restrict g b) K hK.1.1.1
  exact QuotFamilyOver.ext rfl (heq_of_eq key)

/-- **The direct image of quotients as a morphism of Quot presheaves of the site.**  Naturality is
the compatibility of the direct image with pullback along a morphism of test schemes. -/
def directImageQuotSitePresheafMap (hmem : D.DirectImageQuotientMem) :
    D.sourceSituation.quotSitePresheaf ⟶ D.directImageSituation.quotSitePresheaf where
  app T := TypeCat.ofHom fun x => D.directImageQuotFamilyOver hmem (T := T.unop) x
  naturality _ _ g :=
    ConcreteCategory.hom_ext _ _ fun x => D.directImageQuotFamilyOver_baseChange hmem g.unop x

/-- A family has a given direct image iff the direct image of its kernel is the given kernel. -/
private theorem directImageQuotFamilyOver_eq_mk_iff (hmem : D.DirectImageQuotientMem)
    {T : BigFppfOver B S hS} {b : (schemeSpaceFunctor B S hS).obj T ⟶ D.sourceSituation.Y}
    {K₂ : Subobject (D.sourceSituation.baseChangeModule (CostructuredArrow.mk b))}
    {h₂ : K₂ ∈ D.sourceSituation.properlySupportedQuotients (CostructuredArrow.mk b)}
    {K : Subobject (D.directImageSituation.baseChangeModule (CostructuredArrow.mk b))} {h} :
    D.directImageQuotFamilyOver hmem ⟨b, K₂, h₂⟩ = ⟨b, K, h⟩ ↔
      D.directImageQuotient (CostructuredArrow.mk b) K₂ = K := by
  exact ⟨fun hx => by injection hx, fun hx => QuotFamilyOver.ext rfl (heq_of_eq hx)⟩

/-- The direct image of quotients over a scheme of the site is injective. -/
theorem directImageQuotFamilyOver_injective (hπ : IsOpenImmersion B S hS D.π.hom)
    (hmem : D.DirectImageQuotientMem) {T : BigFppfOver B S hS} :
    Function.Injective (D.directImageQuotFamilyOver hmem (T := T)) := by
  rintro ⟨ab, aK, aM⟩ ⟨bb, bK, bM⟩ hab
  obtain rfl : ab = bb := congrArg QuotFamilyOver.toBase hab
  obtain rfl := D.directImageQuotient_injective hπ (CostructuredArrow.mk ab)
    ((D.directImageQuotFamilyOver_eq_mk_iff hmem).1 hab)
  rfl

/-- **The range of the direct image of quotients over a scheme of the site is cut out by the
support condition** `Supp(Q) ⊆ |X_T|`. -/
theorem exists_directImageQuotFamilyOver_eq_iff (hπ : IsOpenImmersion B S hS D.π.hom)
    (hmem : D.DirectImageQuotientMem) {T : BigFppfOver B S hS}
    (y : QuotFamilyOver D.directImageSituation T) :
    (∃ x, D.directImageQuotFamilyOver hmem x = y) ↔
      D.SupportedInSource (schemeTargetAffinePushforwardQuasicoherent B S hS)
        (CostructuredArrow.mk y.toBase) y.subobject := by
  obtain ⟨b, K, hK⟩ := y
  refine Iff.trans ?_
    (D.exists_directImageQuotient_iff_supportedInSource hπ (CostructuredArrow.mk b) K hK)
  constructor
  · rintro ⟨⟨b₂, K₂, hK₂⟩, hx⟩
    obtain rfl : b₂ = b := congrArg QuotFamilyOver.toBase hx
    exact ⟨K₂, hK₂, (D.directImageQuotFamilyOver_eq_mk_iff hmem).1 hx⟩
  · rintro ⟨K', hK', hKK⟩
    exact ⟨⟨b, K', hK'⟩, 
      (D.directImageQuotFamilyOver_eq_mk_iff hmem).2 hKK⟩

/-- **The direct image of quotients along an affine open immersion is an open immersion**, read in
any models of the two Quot presheaves in the universe of the site.

It is a monomorphism, the direct image of quotients being injective, so by
`AlgebraicGeometry.Space.isOpenImmersion_of_isOpenSubspace_range_preimage` it suffices that its
range have open inverse image under every scheme-valued point of the model of
`Quot_{π_*F/Y/B}`.  Such a point is a quotient `Q` of `G_T`, and a morphism `g : U ⟶ T` lies in
that inverse image exactly when the base change of `Q` to `U` is a direct image, that is exactly
when its support lies in `X_U`; that is the support locus of `Q`, which is open. -/
theorem isOpenImmersion_mapFrom_directImageQuotSitePresheafMap
    (hπ : IsOpenImmersion B S hS D.π.hom) (hmem : D.DirectImageQuotientMem)
    (MX : QuotSitePresheafModel D.sourceSituation)
    (MY : QuotSitePresheafModel D.directImageSituation) :
    IsOpenImmersion B S hS (MY.mapFrom (MX.iso.hom ≫ D.directImageQuotSitePresheafMap hmem)) := by
  set Φ := D.directImageQuotSitePresheafMap hmem
  have hfam : ∀ (T : BigFppfOver B S hS) (z : MX.presheaf.obj (Opposite.op T)),
      MY.familyEquiv T ((MY.mapFrom (MX.iso.hom ≫ Φ)).app (Opposite.op T) z) =
        D.directImageQuotFamilyOver hmem (MX.familyEquiv T z) := fun T z =>
    types_congr_hom (MY.iso.inv_hom_id_app (Opposite.op T))
      ((MX.iso.hom ≫ Φ).app (Opposite.op T) (ULift.up z))
  have hmono : Mono (MY.mapFrom (MX.iso.hom ≫ Φ)) := by
    refine (NatTrans.mono_iff_mono_app _).2 fun T => (mono_iff_injective _).2 fun a b hab => ?_
    have hq := congrArg (MY.familyEquiv T.unop) hab
    rw [hfam, hfam] at hq
    exact (MX.familyEquiv T.unop).injective (D.directImageQuotFamilyOver_injective hπ hmem hq)
  apply isOpenImmersion_of_isOpenSubspace_range_preimage
  intro T q
  set y := MY.familyEquiv T (yonedaEquiv q)
  have heq : (Subfunctor.range (MY.mapFrom (MX.iso.hom ≫ Φ))).preimage q =
      D.directImageSituation.supportLocus D.comp y := by
    ext U g
    have hqg : q.app U g = MY.presheaf.map (Quiver.Hom.op g) (yonedaEquiv q) := by
      have hnat := NatTrans.naturality_apply q (Quiver.Hom.op g) (𝟙 T)
      rw [yonedaEquiv_apply]
      simpa using hnat
    show q.app U g ∈ Set.range ((MY.mapFrom (MX.iso.hom ≫ Φ)).app U) ↔
      g ∈ (D.directImageSituation.supportLocus D.comp y).obj U
    have hmem' : ∀ z, z ∈ Set.range ((MY.mapFrom (MX.iso.hom ≫ Φ)).app U) ↔
        ∃ x, D.directImageQuotFamilyOver hmem x = MY.familyEquiv U.unop z := by
      intro z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨MX.familyEquiv U.unop w, (hfam U.unop w).symm⟩
      · rintro ⟨x, hx⟩
        exact ⟨(MX.familyEquiv U.unop).symm x, (MY.familyEquiv U.unop).injective <| by
          rw [hfam, Equiv.apply_symm_apply, hx]⟩
    rw [hqg, hmem', QuotSitePresheafModel.familyEquiv_map,
      D.exists_directImageQuotFamilyOver_eq_iff hπ hmem,
      D.directImageSituation.mem_supportLocus_iff D.comp hπ y g]
    rfl
  rw [heq]
  exact D.directImageSituation.isOpenSubspace_supportLocus D.comp hπ y

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
