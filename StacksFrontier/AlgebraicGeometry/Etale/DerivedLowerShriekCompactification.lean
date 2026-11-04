module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

import StacksCore.Tactic.StacksAttribute

/-!
# The derived lower shriek of a quasi-finite separated morphism is the direct image with
compact support

Let `f : X ⟶ Y` be a quasi-finite separated morphism of a big étale site with `Y` quasi-compact
and quasi-separated. Zariski's main theorem, [Stacks, Tag 05K0], factors `f` as an open
immersion `j : X ⟶ X̄` followed by a finite morphism `f̄ : X̄ ⟶ Y`, and the big étale site
contains `X̄` because a finite morphism does not increase the size of a scheme. The derived
lower shriek of [Stacks, Tag 0F7H] is `Rf_! = R f̄_* ∘ j_!`; since `f̄` is finite its direct
image is exact, so `R f̄_* = f̄_*`, and `f̄_* ∘ j_! = f_!` by [Stacks, Tag 0F52]. Hence `Rf_!`
is the functor induced on unbounded derived categories by the direct image with compact support
`f_!` of [Stacks, Tag 0F6R], which is the functor [Stacks, Tag 0F5M] derives. This is
[Stacks, Tag 0GKM], and it is proved here both for abelian étale sheaves and for sheaves of
`Λ`-modules, that is in `D(X_étale, Λ)`, for a ring `Λ`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isOpenImmersion_isFinite_factorization` — the
  factorization of a quasi-finite separated morphism of a big étale site into an open immersion
  followed by a finite morphism, inside the site. This is [Stacks, Tag 05K0] transported along
  the inclusion of the site into schemes.
* `AlgebraicGeometry.SmallEtale.exists_compactification_derivedLowerShriekIso` —
  **[Stacks, Tag 0GKM]** for abelian étale sheaves.
* `AlgebraicGeometry.SmallEtale.exists_compactification_moduleDerivedLowerShriekIso` —
  **[Stacks, Tag 0GKM]** for sheaves of `Λ`-modules, that is in `D(X_étale, Λ)`.

## Implementation notes

The compactification is *produced*, not assumed: the hypotheses are the source's own, namely
that `f` is quasi-finite — [Stacks, Tag 02NG], that is `LocallyQuasiFinite`,
`LocallyOfFiniteType` and `QuasiCompact` together — and separated, with the target quasi-compact
and quasi-separated. Quasi-compactness and quasi-separatedness of the source are not assumed:
they follow, `f` being quasi-compact and separated.

The factorization is obtained from
`Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization`, Tag 05K0, applied
to the morphism of schemes underlying `f`. Its target `T` lies in the big étale site because it
is of finite type over the target of `f`, which lies in the site, and
`AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact` is Tag 000R (5). The
resulting object of the site is `AlgebraicGeometry.BigEtaleSite.objOfContains`, which does not
unfold to a pair: a reducible wrapper would reduce the projections `X̄.obj` and `X̄.property`
away, and every instance about a functor on `AbelianSheaf B X̄` is found by matching those
projections.

`j_!` is read as the direct image with compact support `f_!` of Tag 0F6R along the open
immersion `j`, which is extension by zero of Tag 03S3 by
`AlgebraicGeometry.SmallEtale.abelianExtensionByZeroIsoFShriek`, the comparison of Tag 0F6Q.
The underived identification `f_! ≅ j_! ⋙ f̄_*` in that form is
`AlgebraicGeometry.SmallEtale.fShriekFunctorIsoCompactificationHom`, and the derived one is
obtained from it by the universal property of the localization, as in
`AlgebraicGeometry.SmallEtale.derivedLowerShriekIso`.

Since the compactification is produced, the derived category of the abelian sheaves on `X̄`
cannot be fixed by an instance argument of the statement; the conclusion is therefore
universally quantified over the choice of such a derived category, which is what
`AlgebraicGeometry.SmallEtale.DerivedLowerShriekAgrees` records. That predicate also keeps the
two sides of the comparison from being re-elaborated at the produced morphisms, which is what
makes the final application a match of arguments rather than a comparison of two derived
functors built from different instance resolutions.

The coefficient ring `Λ` lives in the universe of the schemes. The identification of Tag 0F52
through a compactification is available at the coefficient universe `u + 1` of abelian étale
sheaves, that being where extension by zero of Tag 03S3 and the comparison of Tag 0F6Q are
constructed; sheaves of `Λ`-modules at that coefficient universe are
`AlgebraicGeometry.SmallEtale.ModuleSheaf.{u, u, u}`, whose coefficient universe
`max (u + 1) u u` is `u + 1` exactly when `Λ` is in `Type u`. The `Λ`-linear functors are the
lifts `Stacks.ModuleCatLift.moduleLift` of the abelian ones, so the `Λ`-linear `f_!` is the
`AlgebraicGeometry.SmallEtale.fShriekMod` of the repository, and the `Λ`-linear comparison is
the lift of the abelian one by `Stacks.ModuleCatLift.moduleLiftNatIso`.

## References

* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 0F52](https://stacks.math.columbia.edu/tag/0F52)
* [Stacks Project, Tag 0F6Q](https://stacks.math.columbia.edu/tag/0F6Q)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

/-- A scheme contained in a big étale site, as an object of that site.

This is `AlgebraicGeometry.BigEtaleSite.obj` as a definition rather than an abbreviation: the
projections of an object of the site appear in the index of every small étale topology, and
instance search finds the functors on sheaves for such a topology by matching those
projections, which a reducible wrapper would reduce away. -/
public def BigEtaleSite.objOfContains (B : BigEtaleSite.{u})
    (S : AlgebraicGeometry.Scheme.{u}) (hS : B.Contains S) : B.Scheme :=
  ⟨S, hS⟩

namespace SmallEtale

/-! ### The compactification inside the big étale site -/

section Factorization

variable (B : BigEtaleSite.{u})

/-- An open immersion of a big étale site, viewed as an object of the small étale site of its
target, has an open immersion for its structure morphism. This is the same statement as the
hypothesis, but in the shape in which instance search meets it. -/
public instance isOpenImmersion_ofEtaleHom_obj_hom {X T : B.Scheme} (j : X ⟶ T)
    [IsOpenImmersion (B.inclusion.map j)] :
    IsOpenImmersion (B.inclusion.map (SmallEtale.ofEtaleHom B j).obj.hom) :=
  inferInstanceAs (IsOpenImmersion (B.inclusion.map j))

/-- **Zariski's main theorem inside a big étale site.** A quasi-finite separated morphism
`f : X ⟶ Y` of a big étale site whose target is quasi-compact and quasi-separated factors as an
open immersion `j : X ⟶ X̄` followed by a finite morphism `f̄ : X̄ ⟶ Y`, with `X̄` again an
object of the site.

Quasi-finiteness is Stacks 02NG: locally quasi-finite, locally of finite type and quasi-compact
together. The factorization of schemes is Stacks 05K0,
`Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization`; the intermediate
scheme belongs to the site by Stacks 000R (5), being of finite type over the target. -/
@[ega "III 4.4.5" "special case",
  ega "IV 18.12.13" "special case",
  sga "3 VIB 5.6.0" "(ii), special case"]
public theorem exists_isOpenImmersion_isFinite_factorization {X Y : B.Scheme} (f : X ⟶ Y)
    [IsSeparated (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
    [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] :
    ∃ (Xbar : B.Scheme) (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
      (_ : IsOpenImmersion (B.inclusion.map j)) (_ : IsFinite (B.inclusion.map fbar)),
      f = j ≫ fbar := by
  have : CompactSpace ↥(B.inclusion.obj Y) := inferInstanceAs (CompactSpace ↥Y.obj)
  have : QuasiSeparatedSpace ↥(B.inclusion.obj Y) :=
    inferInstanceAs (QuasiSeparatedSpace ↥Y.obj)
  obtain ⟨T, jm, π, hjm, hjmqc, hπ, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization
      (B.inclusion.map f)
  have hjm' : IsOpenImmersion jm := hjm
  have hπ' : IsFinite π := hπ
  have hT : B.Contains T := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact π Y.property
  exact ⟨B.objOfContains T hT, ObjectProperty.homMk jm, ObjectProperty.homMk π, hjm, hπ,
    B.inclusion.map_injective hfac⟩

end Factorization

/-! ### `f_! = f̄_* ∘ j_!` for an open immersion, and its derived form -/

section Abelian

variable (B : BigEtaleSite.{u}) {X Xbar Y : B.Scheme} (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)

/-- **Stacks 0F52** for an open immersion `j : X ⟶ X̄` presented as a morphism. The direct image
with compact support along `f = j ≫ f̄`, for `f̄ : X̄ ⟶ Y` proper and locally quasi-finite, is
`f_!` along `j` followed by the ordinary direct image along `f̄`.

The first factor is extension by zero along `j` of Stacks 03S3, by Stacks 0F6Q in the form
`AlgebraicGeometry.SmallEtale.abelianExtensionByZeroIsoFShriek`. -/
public def fShriekFunctorIsoCompactificationHom
    [IsOpenImmersion (B.inclusion.map j)] [IsProper (B.inclusion.map fbar)]
    [LocallyQuasiFinite (B.inclusion.map fbar)] :
    fShriekFunctor.{u, u} B (j ≫ fbar) ≅
      fShriekFunctor.{u, u} B j ⋙ etalePushforward.{u, u + 1} B fbar :=
  fShriekFunctorIsoCompactification.{u} B fbar (SmallEtale.ofEtaleHom B j) ≪≫
    Functor.isoWhiskerRight
      (abelianExtensionByZeroIsoFShriek B Xbar.obj Xbar.property (SmallEtale.ofEtaleHom B j))
      (etalePushforward.{u, u + 1} B fbar)

/-- **Stacks 0GKM** for a given compactification, in the form in which `j_!` is the direct image
with compact support along the open immersion `j`: the derived lower shriek
`Rf_! = R f̄_* ∘ j_!` of Stacks 0F7H agrees with the functor induced on unbounded derived
categories of abelian étale sheaves by `f_!`. -/
public def derivedLowerShriekIsoOfOpenImmersion
    [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B X)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Xbar)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Y)] :
    (fShriekFunctor.{u, u} B (j ≫ fbar)).mapDerivedCategory ≅
      (fShriekFunctor.{u, u} B j).mapDerivedCategory ⋙
        (etalePushforward.{u, u + 1} B fbar).mapDerivedCategory :=
  Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
    (fShriekFunctorIsoCompactificationHom B j fbar)

/-- The assertion of Stacks 0GKM for a compactification `f = j ≫ f̄` and abelian coefficients:
for every choice of derived category of the abelian étale sheaves on `X̄`, the derived lower
shriek `R f̄_* ∘ j_!` agrees with the functor induced on unbounded derived categories by the
direct image with compact support along `j ≫ f̄`. -/
public def DerivedLowerShriekAgrees
    [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B X)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Y)] : Prop :=
  ∀ [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Xbar)],
    Nonempty ((fShriekFunctor.{u, u} B (j ≫ fbar)).mapDerivedCategory ≅
      (fShriekFunctor.{u, u} B j).mapDerivedCategory ⋙
        (etalePushforward.{u, u + 1} B fbar).mapDerivedCategory)

/-- Every compactification satisfies the assertion of Stacks 0GKM. -/
public theorem derivedLowerShriekAgrees
    [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B X)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Y)] :
    DerivedLowerShriekAgrees.{w} B j fbar :=
  fun [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Xbar)] =>
    ⟨derivedLowerShriekIsoOfOpenImmersion B j fbar⟩

end Abelian

/-! ### Stacks 0GKM for abelian coefficients -/

/-- **Stacks 0GKM** for abelian étale sheaves. Let `f : X ⟶ Y` be a quasi-finite separated
morphism of a big étale site with `Y` quasi-compact and quasi-separated. Then `f` factors as an
open immersion `j : X ⟶ X̄` followed by a finite morphism `f̄ : X̄ ⟶ Y`, and for that
compactification the derived lower shriek `Rf_! = R f̄_* ∘ j_!` of Stacks 0F7H agrees with the
functor induced on unbounded derived categories of abelian étale sheaves by the direct image
with compact support `f_!` of Stacks 0F6R, which is the functor Stacks 0F5M derives.

Quasi-finiteness is Stacks 02NG: locally quasi-finite, locally of finite type and quasi-compact
together. No compactification is assumed; one is produced, by Zariski's main theorem
Stacks 05K0. -/
@[stacks 0GKM "abelian coefficients", ega "IV 18.12.13" "special case"]
public theorem exists_compactification_derivedLowerShriekIso (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y)
    [IsSeparated (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
    [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B X)]
    [HasDerivedCategory.{w} (AbelianSheaf.{u, u} B Y)] :
    ∃ (Xbar : B.Scheme) (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
      (_ : IsOpenImmersion (B.inclusion.map j)) (_ : IsFinite (B.inclusion.map fbar)),
      f = j ≫ fbar ∧ DerivedLowerShriekAgrees.{w} B j fbar := by
  obtain ⟨Xbar, j, fbar, hoi, hfin, hfac⟩ :=
    exists_isOpenImmersion_isFinite_factorization B f
  exact ⟨Xbar, j, fbar, hoi, hfin, hfac, derivedLowerShriekAgrees B j fbar⟩

/-! ### Sheaves of `Λ`-modules -/

section Module

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

open Stacks.ModuleCatLift

/-- Sheafification of presheaves of `Λ`-modules on the small étale site at the coefficient
universe `u + 1` of abelian étale sheaves, which is where the identification of Stacks 0F52
through a compactification lives. -/
public instance hasSheafify_etaleModuleSheaf (S : B.Scheme) :
    HasSheafify (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleSheaf.{u, u, u} B S Λ

/-- The `Λ`-linear lift of an additive functor on abelian étale sheaves: a functor on sheaves of
`Λ`-modules whose underlying abelian sheaf is the one the functor produces. -/
public abbrev etaleModuleLift {X Y : B.Scheme}
    (G : AbelianSheaf.{u, u} B X ⥤ AbelianSheaf.{u, u} B Y) [G.Additive] :
    ModuleSheaf.{u, u, u} B X Λ ⥤ ModuleSheaf.{u, u, u} B Y Λ :=
  moduleLift.{u + 1, u, _, _, _, _} Λ (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Y.obj Y.property) G

/-- The `Λ`-linear lift of a left exact additive functor is left exact: forgetting the
`Λ`-module structure is left exact and conservative, and takes the lift to the functor it was
lifted from. -/
public instance preservesFiniteLimits_etaleModuleLift {X Y : B.Scheme}
    (G : AbelianSheaf.{u, u} B X ⥤ AbelianSheaf.{u, u} B Y) [G.Additive]
    [PreservesFiniteLimits G] :
    PreservesFiniteLimits (etaleModuleLift B Λ G) := by
  have := preservesFiniteLimits_forgetModuleSheaf.{u, u, u} B X Λ
  have := preservesFiniteLimits_forgetModuleSheaf.{u, u, u} B Y Λ
  have : ReflectsFiniteLimits (forgetModuleSheaf.{u, u, u} B Y Λ) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  have : PreservesFiniteLimits (etaleModuleLift B Λ G ⋙ forgetModuleSheaf.{u, u, u} B Y Λ) := by
    rw [moduleLift_comp_sheafCompose.{u + 1, u, _, _, _, _} Λ
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property) G]
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forgetModuleSheaf.{u, u, u} B Y Λ)

/-- The `Λ`-linear lift of a right exact additive functor is right exact: forgetting the
`Λ`-module structure preserves all colimits and is conservative. -/
public instance preservesFiniteColimits_etaleModuleLift {X Y : B.Scheme}
    (G : AbelianSheaf.{u, u} B X ⥤ AbelianSheaf.{u, u} B Y) [G.Additive]
    [PreservesFiniteColimits G] :
    PreservesFiniteColimits (etaleModuleLift B Λ G) := by
  have := preservesColimitsOfSize_forgetModuleSheaf.{u, u, u} B X Λ
  have := preservesColimitsOfSize_forgetModuleSheaf.{u, u, u} B Y Λ
  have : PreservesFiniteColimits (forgetModuleSheaf.{u, u, u} B X Λ) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteColimits (forgetModuleSheaf.{u, u, u} B Y Λ) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteColimits
      (etaleModuleLift B Λ G ⋙ forgetModuleSheaf.{u, u, u} B Y Λ) := by
    rw [moduleLift_comp_sheafCompose.{u + 1, u, _, _, _, _} Λ
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property) G]
    exact comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_reflects_of_preserves _ (forgetModuleSheaf.{u, u, u} B Y Λ)

/-- The `Λ`-linear direct image with compact support of the repository is the `Λ`-linear lift of
`f_!`. -/
public lemma fShriekMod_eq_etaleModuleLift {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] :
    fShriekMod.{u, u, u} B Λ f = etaleModuleLift B Λ (fShriekFunctor.{u, u} B f) :=
  rfl

/-- The `Λ`-linear direct image with compact support is right exact, `f_!` being exact by
Stacks 0F5F. -/
public instance preservesFiniteColimits_fShriekMod {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] :
    PreservesFiniteColimits (fShriekMod.{u, u, u} B Λ f) :=
  preservesFiniteColimits_etaleModuleLift B Λ (fShriekFunctor.{u, u} B f)

/-- A natural isomorphism of additive functors on abelian étale sheaves lifts to the sheaves of
`Λ`-modules. -/
public def etaleModuleLiftNatIso {X Y : B.Scheme}
    (G G' : AbelianSheaf.{u, u} B X ⥤ AbelianSheaf.{u, u} B Y) [G.Additive] [G'.Additive]
    (e : G ≅ G') : etaleModuleLift B Λ G ≅ etaleModuleLift B Λ G' :=
  moduleLiftNatIso.{u + 1, u, _, _, _, _} Λ (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Y.obj Y.property) G G' e

/-- The `Λ`-linear lift of a composite of additive functors on abelian étale sheaves is the
composite of their lifts. -/
public lemma etaleModuleLift_comp {X Xbar Y : B.Scheme}
    (G₁ : AbelianSheaf.{u, u} B X ⥤ AbelianSheaf.{u, u} B Xbar) [G₁.Additive]
    (G₂ : AbelianSheaf.{u, u} B Xbar ⥤ AbelianSheaf.{u, u} B Y) [G₂.Additive] :
    etaleModuleLift B Λ (G₁ ⋙ G₂) = etaleModuleLift B Λ G₁ ⋙ etaleModuleLift B Λ G₂ :=
  moduleLift_comp.{u + 1, u, _, _, _, _, _, _} Λ (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Xbar.obj Xbar.property) (SmallEtale.topology B Y.obj Y.property) G₁ G₂

/-- The direct image of sheaves of `Λ`-modules on the small étale sites: the `Λ`-linear lift of
the direct image of abelian étale sheaves. -/
public abbrev etalePushforwardMod {X Y : B.Scheme} (g : X ⟶ Y) :
    ModuleSheaf.{u, u, u} B X Λ ⥤ ModuleSheaf.{u, u, u} B Y Λ :=
  etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g)

variable {X Xbar Y : B.Scheme} (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)

/-- **Stacks 0F52 for coefficients in a ring `Λ`.** For `f = j ≫ f̄` with `j` an open immersion
and `f̄` proper and locally quasi-finite, the `Λ`-linear direct image with compact support along
`f` is the `Λ`-linear `j_!` followed by the `Λ`-linear direct image along `f̄`. This is the lift
of the identification of abelian sheaves. -/
public def fShriekModIsoCompactificationHom
    [IsOpenImmersion (B.inclusion.map j)] [IsProper (B.inclusion.map fbar)]
    [LocallyQuasiFinite (B.inclusion.map fbar)] :
    fShriekMod.{u, u, u} B Λ (j ≫ fbar) ≅
      fShriekMod.{u, u, u} B Λ j ⋙ etalePushforwardMod B Λ fbar :=
  etaleModuleLiftNatIso B Λ (fShriekFunctor.{u, u} B (j ≫ fbar))
      (fShriekFunctor.{u, u} B j ⋙ etalePushforward.{u, u + 1} B fbar)
      (fShriekFunctorIsoCompactificationHom B j fbar) ≪≫
    eqToIso (etaleModuleLift_comp B Λ (fShriekFunctor.{u, u} B j)
      (etalePushforward.{u, u + 1} B fbar))

/-- **Stacks 0GKM** for a given compactification and coefficients in a ring `Λ`: the derived
lower shriek `Rf_! = R f̄_* ∘ j_!` of Stacks 0F7H agrees with the functor induced on
`D(X_étale, Λ) ⥤ D(Y_étale, Λ)` by the `Λ`-linear direct image with compact support. -/
public def derivedLowerShriekModIsoOfOpenImmersion
    [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Xbar Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)] :
    (fShriekMod.{u, u, u} B Λ (j ≫ fbar)).mapDerivedCategory ≅
      (fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙
        (etalePushforwardMod B Λ fbar).mapDerivedCategory :=
  Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
    (fShriekModIsoCompactificationHom B Λ j fbar)

/-- The assertion of Stacks 0GKM for a compactification `f = j ≫ f̄` and coefficients in a ring
`Λ`: for every choice of derived category of the sheaves of `Λ`-modules on `X̄`, the derived
lower shriek `R f̄_* ∘ j_!` agrees with the functor `D(X_étale, Λ) ⥤ D(Y_étale, Λ)` induced by
the `Λ`-linear direct image with compact support along `j ≫ f̄`. -/
public def ModuleDerivedLowerShriekAgrees
    [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)] : Prop :=
  ∀ [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Xbar Λ)],
    Nonempty ((fShriekMod.{u, u, u} B Λ (j ≫ fbar)).mapDerivedCategory ≅
      (fShriekMod.{u, u, u} B Λ j).mapDerivedCategory ⋙
        (etalePushforwardMod B Λ fbar).mapDerivedCategory)

/-- Every compactification satisfies the assertion of Stacks 0GKM with coefficients in `Λ`. -/
public theorem moduleDerivedLowerShriekAgrees
    [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)] :
    ModuleDerivedLowerShriekAgrees.{w} B Λ j fbar :=
  fun [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Xbar Λ)] =>
    ⟨derivedLowerShriekModIsoOfOpenImmersion B Λ j fbar⟩

end Module

/-- **Stacks 0GKM** for coefficients in a ring `Λ`. Let `f : X ⟶ Y` be a quasi-finite separated
morphism of a big étale site with `Y` quasi-compact and quasi-separated, and let `Λ` be a ring.
Then `f` factors as an open immersion `j : X ⟶ X̄` followed by a finite morphism `f̄ : X̄ ⟶ Y`,
and for that compactification the derived lower shriek `Rf_! = R f̄_* ∘ j_!` of Stacks 0F7H
agrees with the functor `D(X_étale, Λ) ⥤ D(Y_étale, Λ)` induced by the `Λ`-linear direct image
with compact support `f_!`, which is the functor Stacks 0F5M derives.

Quasi-finiteness is Stacks 02NG: locally quasi-finite, locally of finite type and quasi-compact
together. No compactification is assumed; one is produced, by Zariski's main theorem
Stacks 05K0. -/
@[stacks 0GKM "coefficients in a ring Λ, i.e. in D(X_étale, Λ)", ega "IV 18.12.13" "special case"]
public theorem exists_compactification_moduleDerivedLowerShriekIso (B : BigEtaleSite.{u})
    (Λ : Type u) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
    [IsSeparated (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
    [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)] :
    ∃ (Xbar : B.Scheme) (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
      (_ : IsOpenImmersion (B.inclusion.map j)) (_ : IsFinite (B.inclusion.map fbar)),
      f = j ≫ fbar ∧ ModuleDerivedLowerShriekAgrees.{w} B Λ j fbar := by
  obtain ⟨Xbar, j, fbar, hoi, hfin, hfac⟩ :=
    exists_isOpenImmersion_isFinite_factorization B f
  exact ⟨Xbar, j, fbar, hoi, hfin, hfac, moduleDerivedLowerShriekAgrees B Λ j fbar⟩

end SmallEtale

end AlgebraicGeometry

end
