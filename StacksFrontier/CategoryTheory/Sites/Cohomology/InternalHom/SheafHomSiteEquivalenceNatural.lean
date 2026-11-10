module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
import all StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects

/-!
# Internal Hom of complexes is invariant under an equivalence of ringed sites

Let `(C, O_C)` and `(D, O_D)` be ringed sites and let `e : C ≌ D` be an equivalence of the
underlying sites, continuous in both directions, together with structure maps
`φ : O_C ⟶ e_* O_D` and `ψ : O_D ⟶ (e^{-1})_* O_C` exhibiting the two pushforwards of sheaves
of modules as mutually inverse equivalences — exactly the data of Mathlib's
`SheafOfModules.pushforwardPushforwardEquivalence`. On sheaves of modules the transport of the
internal Hom sheaf of Stacks 03EM along such an equivalence is
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIso`. This file raises that statement two
levels, to complexes and then to derived categories:

```
φ_* SheafHom^•(A, B) ≅ SheafHom^•(φ_* A, φ_* B),
φ_* RSheafHom(K, L) ≅ RSheafHom(φ_* K, φ_* L).
```

Both are proved in the pattern of `AlgebraicGeometry.RingedSite.derivedHomRestriction`
([Stacks, Tag 08JB]), with an arbitrary equivalence of ringed sites in place of restriction to
a slice site. Neither statement is a Stacks tag — the tags are stated for restriction along a
localization, which is not an equivalence — so nothing here carries a `@[stacks]` attribute.

## Main definitions

* `AlgebraicGeometry.RingedSite.homComplexMapIso`: a fully faithful additive functor preserves
  the Hom complex of two cochain complexes.
* `AlgebraicGeometry.RingedSite.siteEquivSectionIso`: the identification of the complexes of
  sections, over an object `W` of `C`, of the two sides of the chain-level statement.
* `AlgebraicGeometry.RingedSite.siteEquivSectionLinearEquiv`: that identification in a fixed
  degree, as an `O_C(W)`-linear equivalence.
* `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso`: **the chain-level transport.**
* `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomNatIso`: **the derived-level transport.**

## Main results

* `AlgebraicGeometry.RingedSite.siteEquivSectionIso_apply` and
  `siteEquivSectionIso_apply_section`: the chain-level identification acts on a local
  homogeneous cochain by transporting it along the equivalence of slices. This pins the
  comparison down rather than merely asserting that some isomorphism exists.
* `AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso_natural`: the chain-level transport
  is natural in both variables, i.e. it intertwines the maps
  `AlgebraicGeometry.RingedSite.homMap` of internal Hom complexes.

## Implementation notes

The internal Hom complex is available only through the characterising data of
`AlgebraicGeometry.RingedSite.SheafHomComplex`, so the comparison is built on sections: over an
object `W` of `C` the sections of `φ_* SheafHom^•(A, B)` are the sections of `SheafHom^•(A, B)`
over `e(W)`, which are the cochains from `A|_{e(W)}` to `B|_{e(W)}` on `D/e(W)`; the equivalence
of slices `C/W ≌ D/e(W)` carries those to the cochains from `(φ_* A)|_W` to `(φ_* B)|_W`, which
are the sections of `SheafHom^•(φ_* A, φ_* B)` over `W`. The middle step is
`homComplexMapIso` applied to the slice-level equivalence
`Stacks.SheafOfModules.InternalHom.siteEquivModulesOver`, and no comparison of the two restricted
complexes is needed: the localized structure maps are `φ` and `ψ` whiskered along the slice
projections, which makes the transport of `A|_{e(W)}` *equal* to `(φ_* A)|_W`.

Two further compatibilities are what make the identification a map of sheaves of modules and not
merely of sheaves of abelian groups, and they are the only places the hypotheses on `φ` are
used. Linearity over `O_C(W)` — through which the sections of the transport are an
`O_C(W)`-module — is the `smul_natural` field of the two realizations together with the
naturality of `φ`, recorded as `phi_naturality_apply`. Compatibility with restriction along an
arrow of `C` is the `restrict_natural` field of the two realizations together with
`e(h ≫ g) = e(h) ≫ e(g)`; the two slice objects that identifies carry the element being
evaluated in their types, so the substitution is made by `subst` in
`siteEquivSectionIso_apply_section_of_eq` rather than by `congrArg`.

The derived statement needs no descent through a localization. A representative `N` of `K` and
the chosen K-injective resolution `I` of a representative of `L` are enough: there both sides
are the class of an ordinary internal Hom complex by
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, and the comparison is the class of the
chain-level transport. That the transport of `I` is still K-injective is [Stacks, Tag 08BJ] in
the form `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, applied to the adjunction
`ψ_* ⊣ φ_*` of the equivalence, whose left adjoint is exact.

The exactness of `φ_*` is an instance *hypothesis* of the derived section rather than an
instance: the witness is that `φ_*` is the functor of `modulesEquiv`, which needs `ψ`, `H₁` and
`H₂`, and typeclass synthesis cannot recover those from a statement mentioning only `φ`.
`pushforward_preservesFiniteLimits` and `pushforward_preservesFiniteColimits` discharge the
hypotheses; this is the device used for the same reason in
`Stacks.SheafOfModules.derivedOverFunctorEquiv`.

Several functors are made `implicit_reducible` locally, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomRestriction.lean`: the
sections of `φ_* M` over `W` and the sections of `M` over `e(W)` are the same object only after
the pushforward of presheaves of modules and its restriction of scalars are unfolded, which is
invisible at the transparency a rewrite uses.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u v

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

omit hlim hcolim in
include ψ H₁ H₂ in
/-- The K-injectivity of the transport of a K-injective complex, [Stacks, Tag 08BJ]: the inverse
of the equivalence is an exact left adjoint of the transport. -/
theorem pushComplex_isKInjective
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] : ((pushComplex eqv φ).obj I).IsKInjective :=
  let := pushforward_inverse_preservesFiniteLimits eqv φ ψ H₁ H₂
  let := pushforward_inverse_preservesFiniteColimits eqv φ ψ H₁ H₂
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (SheafOfModules.pushforward.{u} φ) (SheafOfModules.pushforward.{u} ψ)
    (modulesEquiv eqv φ ψ H₁ H₂).symm.toAdjunction I

/-- The source of the transport of the derived internal Hom, as a functor of both arguments:
`(K, L) ↦ φ_* RSheafHom(K, L)`. -/
abbrev siteEquivSourceFunctor :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  Functor.uncurry.obj (derivedSheafHomBifunctor X) ⋙
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory

/-- The target of the transport of the derived internal Hom, as a functor of both arguments:
`(K, L) ↦ RSheafHom(φ_* K, φ_* L)`. -/
abbrev siteEquivTargetFunctor :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.op.prod
      (SheafOfModules.pushforward.{u} φ).mapDerivedCategory) ⋙
    Functor.uncurry.obj (derivedSheafHomBifunctor Y)

/-- The transport of the class of a complex is the class of its transport. -/
abbrev siteEquivComparison
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj ((pushComplex eqv φ).obj A) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.app A

omit [eqv.inverse.IsContinuous X.J Y.J] in
/-- The comparison of `siteEquivComparison` is natural in the complex. -/
theorem siteEquivComparison_natural
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : A ⟶ B) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        (siteEquivComparison eqv φ B).hom =
      (siteEquivComparison eqv φ A).hom ≫ DerivedCategory.Q.map ((pushComplex eqv φ).map f) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.hom.naturality f

/-- The source of the transport on a K-injective model: the transport of the class of the
internal Hom complex. -/
def siteEquivSourceComparison
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (siteEquivSourceFunctor eqv φ).obj (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj ((pushComplex eqv φ).obj (sheafHomComplex X A B).obj) :=
  (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.mapIso
      (derivedSheafHomComparison X A B) ≪≫
    siteEquivComparison eqv φ (sheafHomComplex X A B).obj

/-- The transport of classes of complexes in both arguments of the derived internal Hom of the
target site, as an isomorphism of functors on pairs of complexes. -/
def siteEquivArgumentsComparison :
    ((DerivedCategory.Q ⋙ (SheafOfModules.pushforward.{u} φ).mapDerivedCategory).op.prod
      (DerivedCategory.Q ⋙ (SheafOfModules.pushforward.{u} φ).mapDerivedCategory)) ⋙
        Functor.uncurry.obj (derivedSheafHomBifunctor Y) ≅
    ((pushComplex eqv φ ⋙ DerivedCategory.Q).op.prod (pushComplex eqv φ ⋙ DerivedCategory.Q)) ⋙
        Functor.uncurry.obj (derivedSheafHomBifunctor Y) :=
  Functor.isoWhiskerRight (NatIso.prod
    (NatIso.op (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors.symm)
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategoryFactors) _

include ψ H₁ H₂ in
/-- The target of the transport on a K-injective model: the class of the internal Hom complex
of the transports. -/
def siteEquivTargetComparison
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (siteEquivTargetFunctor eqv φ).obj (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj
        (sheafHomComplex Y ((pushComplex eqv φ).obj A) ((pushComplex eqv φ).obj B)).obj :=
  haveI := pushComplex_isKInjective eqv φ ψ H₁ H₂ B
  (siteEquivArgumentsComparison eqv φ).app (op A, B) ≪≫
    derivedSheafHomComparison Y ((pushComplex eqv φ).obj A) ((pushComplex eqv φ).obj B)

omit [eqv.inverse.IsContinuous X.J Y.J] in
/-- The source model comparison is natural in both complexes. -/
theorem siteEquivSourceComparison_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [B.IsKInjective] [B'.IsKInjective] (f : A' ⟶ A) (g : B ⟶ B') :
    (siteEquivSourceFunctor eqv φ).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (siteEquivSourceComparison eqv φ A' B').hom =
    (siteEquivSourceComparison eqv φ A B).hom ≫
      DerivedCategory.Q.map ((pushComplex eqv φ).map (homMap X f g)) := by
  change (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
      (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map f).op).app
          (DerivedCategory.Q.obj B) ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
          (DerivedCategory.Q.map g)) ≫
      ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
          (derivedSheafHomComparison X A' B').hom ≫ _) =
    ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (derivedSheafHomComparison X A B).hom ≫ _) ≫ _
  rw [← Functor.map_comp_assoc, Category.assoc, derivedSheafHomComparison_naturality X f g,
    Functor.map_comp, Category.assoc, siteEquivComparison_natural, Category.assoc]

include ψ H₁ H₂ in
/-- The target model comparison is natural in both complexes. -/
theorem siteEquivTargetComparison_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [B.IsKInjective] [B'.IsKInjective] (f : A' ⟶ A) (g : B ⟶ B') :
    (siteEquivTargetFunctor eqv φ).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (siteEquivTargetComparison eqv φ ψ H₁ H₂ A' B').hom =
    (siteEquivTargetComparison eqv φ ψ H₁ H₂ A B).hom ≫
      DerivedCategory.Q.map (homMap Y ((pushComplex eqv φ).map f) ((pushComplex eqv φ).map g)) := by
  have := pushComplex_isKInjective eqv φ ψ H₁ H₂ B
  have := pushComplex_isKInjective eqv φ ψ H₁ H₂ B'
  simp only [siteEquivTargetComparison, Iso.trans_hom, Iso.app_hom]
  have h : (siteEquivTargetFunctor eqv φ).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (siteEquivArgumentsComparison eqv φ).hom.app (op A', B') = _ :=
    (siteEquivArgumentsComparison eqv φ).hom.naturality (Prod.mkHom f.op g)
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  congr 1
  simp only [Functor.comp_obj, Functor.prod_obj, Functor.op_obj, Functor.uncurry_obj_obj,
    Functor.comp_map, Functor.prod_map, Functor.op_map,
    Quiver.Hom.unop_op, Functor.uncurry_obj_map]
  simpa only [Category.assoc] using
    derivedSheafHomComparison_naturality Y ((pushComplex eqv φ).map f) ((pushComplex eqv φ).map g)
include ψ H₁ H₂ in
/-- The transport of the derived internal Hom on a pair of complexes with K-injective target. -/
def siteEquivModelIso
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (siteEquivSourceFunctor eqv φ).obj (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      (siteEquivTargetFunctor eqv φ).obj (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) :=
  siteEquivSourceComparison eqv φ A B ≪≫
    DerivedCategory.Q.mapIso (siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ A B) ≪≫
    (siteEquivTargetComparison eqv φ ψ H₁ H₂ A B).symm

/-- The model transport is natural in both complexes. -/
theorem siteEquivModelIso_natural
    {A A' B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [B.IsKInjective] [B'.IsKInjective] (f : A' ⟶ A) (g : B ⟶ B') :
    (siteEquivSourceFunctor eqv φ).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) ≫
      (siteEquivModelIso eqv φ ψ H₁ H₂ A' B').hom =
    (siteEquivModelIso eqv φ ψ H₁ H₂ A B).hom ≫
      (siteEquivTargetFunctor eqv φ).map
        (Prod.mkHom (DerivedCategory.Q.map f).op (DerivedCategory.Q.map g)) := by
  apply (cancel_mono (siteEquivTargetComparison eqv φ ψ H₁ H₂ A' B').hom).mp
  simp only [siteEquivModelIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, siteEquivSourceComparison_natural eqv φ f g, Category.assoc,
    siteEquivTargetComparison_natural eqv φ ψ H₁ H₂ f g]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, siteEquivSheafHomComplexIso_natural]

/-- **The derived internal Hom is invariant under an equivalence of ringed sites, naturally in
both arguments.** There is an isomorphism of functors of two variables
`φ_* RSheafHom(-, -) ≅ RSheafHom(φ_* -, φ_* -)` which on a pair of complexes with K-injective
target is the class of the chain-level transport `siteEquivSheafHomComplexIso`.

It is obtained, as in `AlgebraicGeometry.RingedSite.derivedHom_restriction_exists`, by extending
the model transport `siteEquivModelIso` along the functorial K-injective resolution. -/
theorem siteEquivDerivedSheafHom_exists :
    ∃ e : siteEquivSourceFunctor eqv φ ≅ siteEquivTargetFunctor eqv φ,
      ∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        [B.IsKInjective],
        e.hom.app (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) =
          (siteEquivModelIso eqv φ ψ H₁ H₂ A B).hom := by
  let C := CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ
  let Q : C ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    DerivedCategory.Q
  let W := HomologicalComplex.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
  let R := (𝟭 Cᵒᵖ).prod (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  let η : 𝟭 (Cᵒᵖ × C) ⟶ R :=
    { app := fun c => Prod.mkHom (𝟙 c.1)
        ((Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app c.2)
      naturality := by
        intro c c' f
        apply Prod.ext
        · simp [R]
        · exact (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).naturality f.2 }
  have (c : Cᵒᵖ × C) : IsIso ((Q.op.prod Q).map (η.app c)) := by
    dsimp [Q, η]
    exact (isIso_prod_iff _ _).2 ⟨(Q.mapIso (Iso.refl c.1.unop)).op.isIso_hom, inferInstance⟩
  obtain ⟨e, he⟩ := extendIsoFromResolution (Q.op.prod Q) (W.op.prod W) R η
    (fun c : Cᵒᵖ × C => c.2.IsKInjective)
    (fun c => Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) c.2)
    (siteEquivSourceFunctor eqv φ) (siteEquivTargetFunctor eqv φ)
    (fun c hc => by
      have := hc
      exact siteEquivModelIso eqv φ ψ H₁ H₂ c.1.unop c.2)
    (by
      intro c c' hc hc' f
      have := hc
      have := hc'
      exact siteEquivModelIso_natural eqv φ ψ H₁ H₂ f.1.unop f.2)
  exact ⟨e, fun A B hB => he (op A, B) hB⟩

/-- **The derived internal Hom is invariant under an equivalence of ringed sites.** The
transport along the equivalence of `RSheafHom_{O_X}(K, L)` is the derived internal Hom of the
transports of `K` and `L`, naturally in both (`siteEquivDerivedSheafHomNatIso_natural_left`,
`siteEquivDerivedSheafHomNatIso_natural_right`); on a pair of complexes with K-injective target it
is the class of the chain-level transport `siteEquivSheafHomComplexIso`
(`siteEquivDerivedSheafHomNatIso_model`). The transport of a K-injective complex stays K-injective
by [Stacks, Tag 08BJ], the inverse of the equivalence being exact. -/
def siteEquivDerivedSheafHomNatIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  (Classical.choose (siteEquivDerivedSheafHom_exists eqv φ ψ H₁ H₂)).app (op K, L)

/-- On a pair of complexes with K-injective target the transport is the model transport. -/
theorem siteEquivDerivedSheafHomNatIso_model
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (siteEquivDerivedSheafHomNatIso eqv φ ψ H₁ H₂ (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B)).hom = (siteEquivModelIso eqv φ ψ H₁ H₂ A B).hom :=
  Classical.choose_spec (siteEquivDerivedSheafHom_exists eqv φ ψ H₁ H₂) A B

/-- The transport of the derived internal Hom is natural in the first, contravariant argument. -/
theorem siteEquivDerivedSheafHomNatIso_natural_left
    {K K' L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K' ⟶ K) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).map f.op).app L) ≫
        (siteEquivDerivedSheafHomNatIso eqv φ ψ H₁ H₂ K' L).hom =
      (siteEquivDerivedSheafHomNatIso eqv φ ψ H₁ H₂ K L).hom ≫
        ((derivedSheafHomBifunctor Y).map
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map f).op).app
            ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) := by
  have h := (Classical.choose (siteEquivDerivedSheafHom_exists eqv φ ψ H₁ H₂)).hom.naturality
    (Prod.mkHom f.op (𝟙 L))
  simpa [siteEquivDerivedSheafHomNatIso] using h

/-- The transport of the derived internal Hom is natural in the second, covariant argument. -/
theorem siteEquivDerivedSheafHomNatIso_natural_right
    {K L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : L ⟶ L') :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).obj (op K)).map g) ≫
        (siteEquivDerivedSheafHomNatIso eqv φ ψ H₁ H₂ K L').hom =
      (siteEquivDerivedSheafHomNatIso eqv φ ψ H₁ H₂ K L).hom ≫
        ((derivedSheafHomBifunctor Y).obj
          (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).map
            ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map g) := by
  have h := (Classical.choose (siteEquivDerivedSheafHom_exists eqv φ ψ H₁ H₂)).hom.naturality
    (Prod.mkHom (𝟙 (op K)) g)
  simpa [siteEquivDerivedSheafHomNatIso] using h

end Derived

section OfIso

attribute [local instance] HasDerivedCategory.standard

variable [hφ : IsIso φ]

variable [hlim : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ)]
  [hcolim : PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ)]

/-- **The derived-level transport, for an invertible structure map.** See
`siteEquivSheafHomComplexIsoOfIso` for why the invertibility is a named instance argument. -/
def siteEquivDerivedSheafHomNatIsoOfIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  siteEquivDerivedSheafHomNatIso eqv φ (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) K L

/-- `siteEquivDerivedSheafHomNatIsoOfIso` is natural in the second, covariant argument. -/
theorem siteEquivDerivedSheafHomNatIsoOfIso_natural_right
    {K L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : L ⟶ L') :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).obj (op K)).map g) ≫
        (siteEquivDerivedSheafHomNatIsoOfIso eqv φ K L').hom =
      (siteEquivDerivedSheafHomNatIsoOfIso eqv φ K L).hom ≫
        ((derivedSheafHomBifunctor Y).obj
          (op ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj K))).map
            ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map g) :=
  siteEquivDerivedSheafHomNatIso_natural_right eqv φ _ _ _ g

/-- `siteEquivDerivedSheafHomNatIsoOfIso` is natural in the first, contravariant argument. -/
theorem siteEquivDerivedSheafHomNatIsoOfIso_natural_left
    {K K' L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K' ⟶ K) :
    (SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map
        (((derivedSheafHomBifunctor X).map f.op).app L) ≫
        (siteEquivDerivedSheafHomNatIsoOfIso eqv φ K' L).hom =
      (siteEquivDerivedSheafHomNatIsoOfIso eqv φ K L).hom ≫
        ((derivedSheafHomBifunctor Y).map
          ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.map f).op).app
            ((SheafOfModules.pushforward.{u} φ).mapDerivedCategory.obj L) :=
  siteEquivDerivedSheafHomNatIso_natural_left eqv φ _ _ _ f

end OfIso

end AlgebraicGeometry.RingedSite

end
