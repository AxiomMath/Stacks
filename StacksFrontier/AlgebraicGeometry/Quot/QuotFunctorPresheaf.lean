module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback

/-!
# The Quot functor as a functor and as a presheaf on the site

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module. To a scheme `T` over `B` is
attached the set `Quot_{F/X/B}(T)` of quotients of `F_T` which are quasi-coherent, of finite
presentation, flat over `T` and with support proper over `T`; that set is
`AlgebraicGeometry.Space.QuotSituation.properlySupportedQuotients`. This file assembles those sets
into a functor on the test schemes over `B`, and reads that functor as a presheaf on the schemes
of the site together with a canonical morphism to `B`.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.quotFunctor`: the Quot functor
  `Quot_{F/X/B} : (Sch/B)ᵒᵖ ⥤ Sets`.
* `AlgebraicGeometry.Space.QuotFamilyOver`: a quotient classified by the Quot functor over a
  scheme of the site, together with the morphism to `B` it lies over.
* `AlgebraicGeometry.Space.QuotSituation.quotSitePresheaf`: the Quot functor read as a presheaf on
  the schemes of the site, and `AlgebraicGeometry.Space.QuotSituation.quotSitePresheafToBase` its
  canonical morphism to `B`.
* `AlgebraicGeometry.Space.QuotSitePresheafModel`: a model of that presheaf in the universe of the
  site.

## Main results

* `AlgebraicGeometry.Space.hasProperSupport_of_iso`: having support proper over the base is an
  invariant of the isomorphism class of a module.
* `AlgebraicGeometry.Space.QuotSituation.quotientPullback_mem_properlySupportedQuotients`: the
  four conditions defining `Quot_{F/X/B}` are stable under pullback of quotients.

## Implementation notes

Quotients are recorded by their kernels, so a section of the functor over `T` is a subobject of
`F_T` and lives one universe up: the Quot functor takes values in `Type (u + 1)` while an
algebraic space takes values in `Type u`. A model in `Type u` is recorded by the structure
`AlgebraicGeometry.Space.QuotSitePresheafModel`.

## References

* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Proper support is an invariant of the isomorphism class -/

/-- Having support proper over the base depends on the support only, so it transports along an
equality of supports. -/
theorem hasProperSupport_congr_support {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (g : X ⟶ Y)
    (hg : IsLocallyOfFiniteType B S hS g) {s t : Set (points B S hS X)} (hst : s = t)
    (h : ∃ hcl : IsClosed s, IsProperOver B S hS hX hY g hg s hcl) :
    ∃ hcl : IsClosed t, IsProperOver B S hS hX hY g hg t hcl :=
  hst ▸ h

/-- Having support proper over the base is an invariant of the isomorphism class of a
module. -/
theorem hasProperSupport_of_iso {X : AlgebraicSpaces B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (g : X.1 ⟶ Y)
    (hg : IsLocallyOfFiniteType B S hS g) {M N : Modules.{u, u} B S hS X.1 X.2} (e : M ≅ N)
    (h : HasProperSupport B S hS X.property hY g hg ((SheafOfModules.toSheaf _).obj M)) :
    HasProperSupport B S hS X.property hY g hg ((SheafOfModules.toSheaf _).obj N) :=
  hasProperSupport_congr_support X.property hY g hg (supportOfSheaf_eq_of_iso B S hS X e) h

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- The proper-support condition on a module over a test scheme is an invariant of its
isomorphism class. -/
theorem isProperlySupportedOver_of_iso {T : SchemesOver D.Y}
    {M N : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (e : M ≅ N)
    (h : D.IsProperlySupportedOver T M) : D.IsProperlySupportedOver T N :=
  hasProperSupport_of_iso ((schemeSpaceFunctor B S hS).obj T.left).property
    (D.projection T).hom (D.isLocallyOfFiniteType_projection T) e h

/-! ### Pullback of a quotient of the Quot functor -/

/-- The pullback of a quotient in `Quot_{F/X/B}(T)` along a morphism `T' ⟶ T` of test schemes
lies in `Quot_{F/X/B}(T')`. -/
@[stacks 09TR "stability of the four conditions under pullback of quotients"]
theorem quotientPullback_mem_properlySupportedQuotients
    {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.properlySupportedQuotients T) :
    D.quotientPullback h K ∈ D.properlySupportedQuotients T' :=
  ⟨⟨D.quotientPullback_mem_quotients' h K hK.1.1,
      SheafOfModules.IsFinitePresentationOnSite.of_iso (D.quotientPullbackCokernelIso h K).symm
        (D.pullbackPreservesFinitePresentation h (D.quotientModule T K) hK.1.2)⟩,
    D.isProperlySupportedOver_of_iso (D.quotientPullbackCokernelIso h K).symm
      (D.isProperlySupportedOver_modulePullback_quotientModule h hK)⟩

/-! ### The Quot functor -/

/-- The Quot functor `Quot_{F/X/B} : (Sch/B)ᵒᵖ ⥤ Sets` of `F/X/B`: its value at
a test scheme `T` over `B` is the set `Quot_{F/X/B}(T)` of quotients of `F_T` that are
quasi-coherent, of finite presentation, flat over `T` and with support proper over `T`, and its
action on a morphism of test schemes is pullback of quotients. -/
@[stacks 09TR "the Quot functor on the test schemes over the base"]
def quotFunctor : (SchemesOver D.Y)ᵒᵖ ⥤ Type (u + 1) where
  obj T := D.properlySupportedQuotients T.unop
  map {_ _} m := ↾fun K ↦
    ⟨D.quotientPullback m.unop K.1,
      D.quotientPullback_mem_properlySupportedQuotients m.unop K.1 K.2⟩
  map_id T := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_id (modulePushforwardCoherence B S hS) T.unop K.1))
  map_comp m n := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_comp (modulePushforwardCoherence B S hS)
      n.unop m.unop K.1))

/-- The value of the Quot functor at a test scheme over `B` is the set
`Quot_{F/X/B}(T)`. -/
theorem quotFunctor_obj (T : SchemesOver D.Y) :
    D.quotFunctor.obj (Opposite.op T) = D.properlySupportedQuotients T :=
  rfl

/-- The action of the Quot functor on a morphism of test schemes is pullback of
quotients. -/
theorem quotFunctor_map {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (hK : K ∈ D.properlySupportedQuotients T) :
    (D.quotFunctor.map (Opposite.op h)
      ⟨K, hK⟩ : D.properlySupportedQuotients T').1 = D.quotientPullback h K :=
  rfl

/-- The Quot functor is a subfunctor of the functor of finitely presented quotients: at every
test scheme its value is a subset of the value of
`AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsFunctor`, and the two
actions agree. -/
def quotFunctorToFinitePresentationQuotientsFunctor :
    D.quotFunctor ⟶ D.toQuotientSituation.finitePresentationQuotientsFunctor where
  app T := ↾fun K ↦ ⟨K.1, D.properlySupportedQuotients_subset_finitePresentation T.unop K.2⟩

end QuotSituation

/-! ### The Quot functor as a presheaf on the schemes of the site -/

/-- A quotient classified by the Quot functor over a scheme of the big fppf site
rather than over a test scheme of `B`: the morphism to `B` the quotient lies over, together with a
quotient over the resulting test scheme. -/
@[stacks 09TR "quotients over the schemes of the site"]
structure QuotFamilyOver (D : QuotSituation B S hS) (T : BigFppfOver B S hS) where
  /-- The morphism to `B` the quotient lies over. -/
  toBase : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y
  /-- The kernel of the quotient, over the resulting test scheme. -/
  subobject : Subobject (D.baseChangeModule (CostructuredArrow.mk toBase))
  /-- The quotient is quasi-coherent, of finite presentation, flat over the test scheme and has
  support proper over it. -/
  mem : subobject ∈ D.properlySupportedQuotients (CostructuredArrow.mk toBase)

namespace QuotFamilyOver

variable {D : QuotSituation B S hS}

/-- Two quotients over a scheme of the site agree as soon as the morphisms to `B` they lie over
agree and their kernels agree over that, heterogeneously. -/
theorem ext {T : BigFppfOver B S hS} {a b : QuotFamilyOver D T} (hbase : a.toBase = b.toBase)
    (hsub : a.subobject ≍ b.subobject) : a = b := by
  obtain ⟨ab, aK, aM⟩ := a
  obtain ⟨bb, bK, bM⟩ := b
  subst hbase
  cases eq_of_heq hsub
  rfl

/-- The morphism of test schemes over `B` induced by a morphism of schemes of the site and a
morphism from the target to `B`. -/
def restrict {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (h : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y) :
    (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ h) : SchemesOver D.Y) ⟶
      CostructuredArrow.mk h :=
  CostructuredArrow.homMk g rfl

/-- `restrict` sends the identity to the identity. -/
theorem restrict_id (T : BigFppfOver B S hS)
    (h : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y) :
    restrict (𝟙 T) h = 𝟙 (CostructuredArrow.mk h) :=
  CostructuredArrow.hom_ext _ _ rfl

/-- `restrict` is compatible with composition. -/
theorem restrict_comp {T T' T'' : BigFppfOver B S hS} (g : T' ⟶ T) (k : T'' ⟶ T')
    (h : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y) :
    restrict k ((schemeSpaceFunctor B S hS).map g ≫ h) ≫ restrict g h = restrict (k ≫ g) h :=
  CostructuredArrow.hom_ext _ _ rfl

/-- Base change of a quotient over a scheme of the site along a morphism of schemes of the
site. -/
def baseChange {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D T) : QuotFamilyOver D T' where
  toBase := (schemeSpaceFunctor B S hS).map g ≫ x.toBase
  subobject := D.quotientPullback (restrict g x.toBase) x.subobject
  mem := D.quotientPullback_mem_properlySupportedQuotients
    (restrict g x.toBase) x.subobject x.mem

/-- The base change along `g` lies over the composite of `g` with the original morphism to `B`. -/
@[simp]
theorem baseChange_toBase {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (x : QuotFamilyOver D T) :
    (x.baseChange g).toBase = (schemeSpaceFunctor B S hS).map g ≫ x.toBase :=
  rfl

/-- Base change along the identity is the identity. -/
theorem baseChange_id (T : BigFppfOver B S hS)
    (x : QuotFamilyOver D T) : x.baseChange (𝟙 T) = x := by
  refine QuotFamilyOver.ext (by simp) ?_
  simp only [baseChange, restrict_id]
  exact heq_of_eq (D.quotientPullback_id (modulePushforwardCoherence B S hS) _ x.subobject)

/-- Base change is compatible with composition. -/
theorem baseChange_comp {T T' T'' : BigFppfOver B S hS} (g : T' ⟶ T)
    (k : T'' ⟶ T') (x : QuotFamilyOver D T) :
    (x.baseChange g).baseChange k = x.baseChange (k ≫ g) := by
  refine QuotFamilyOver.ext (by simp) ?_
  simp only [baseChange, ← restrict_comp]
  exact heq_of_eq
    (D.quotientPullback_comp (modulePushforwardCoherence B S hS) _ _ x.subobject).symm

end QuotFamilyOver

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- The Quot functor read as a presheaf on the schemes of the big fppf site: a
section over `T` is a morphism `T ⟶ B` together with a quotient of `F_T` for the resulting test
scheme, and restriction pulls back both. -/
@[stacks 09TR "the presheaf on the schemes of the site"]
def quotSitePresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj T := QuotFamilyOver D T.unop
  map g := TypeCat.ofHom fun x => x.baseChange g.unop
  map_id T := ConcreteCategory.hom_ext _ _ fun x ↦ x.baseChange_id T.unop
  map_comp g h := ConcreteCategory.hom_ext _ _ fun x ↦ (x.baseChange_comp g.unop h.unop).symm

/-- The canonical morphism from the Quot presheaf to the universe lift of the base algebraic space
`B`, sending a quotient to the morphism to `B` it lies over. -/
@[stacks 09TR "the canonical morphism to the base"]
def quotSitePresheafToBase :
    D.quotSitePresheaf ⟶ D.Y.obj ⋙ uliftFunctor.{u + 1, u} where
  app T := TypeCat.ofHom fun x => ULift.up (yonedaEquiv x.toBase.hom)
  naturality T T' g := by
    ext x
    exact congrArg ULift.up (yonedaEquiv_naturality x.toBase.hom g.unop).symm

/-- The canonical morphism to the base takes a section of the Quot presheaf to the point of `B`
corresponding to the morphism it lies over. -/
@[simp]
theorem quotSitePresheafToBase_app_apply (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : D.quotSitePresheaf.obj T) :
    (D.quotSitePresheafToBase.app T x).down = yonedaEquiv x.toBase.hom :=
  rfl

end QuotSituation

/-- A model of the Quot presheaf of a situation in the universe of the big fppf site: a presheaf
of `Type u` whose universe lift is isomorphic to the Quot presheaf. -/
structure QuotSitePresheafModel (D : QuotSituation B S hS) where
  /-- The small presheaf. -/
  presheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Its universe lift is the Quot presheaf. -/
  iso : presheaf ⋙ uliftFunctor.{u + 1, u} ≅ D.quotSitePresheaf

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS} (M : QuotSitePresheafModel D)

/-- The canonical morphism from a model of the Quot presheaf to the base algebraic space. -/
def toBase : M.presheaf ⟶ D.Y.obj where
  app T := ↾fun z ↦ (D.quotSitePresheafToBase.app T (M.iso.hom.app T ⟨z⟩)).down
  naturality {T T'} g := by
    ext z
    exact congrArg ULift.down
      (types_congr_hom ((M.iso.hom ≫ D.quotSitePresheafToBase).naturality g) (ULift.up.{u + 1} z))

end QuotSitePresheafModel

end AlgebraicGeometry.Space

end
