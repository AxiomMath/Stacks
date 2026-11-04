module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.LocalCohomologyExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonInDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianLocalCohomologyExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologySheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Forgetting the module structure commutes with excision, in degree zero

Let `X` be a scheme, `T ⊆ X` a subset and `U ⊆ X` an open subscheme.  Sections supported on `T`
restrict to sections supported on `U ∩ T`, twice over: for sheaves of `𝒪_X`-modules, as
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`, and for sheaves of
abelian groups, as
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictNatIso`.  Forgetting the
module structure carries the first to the second:

`H_T(ℱ)|_U → H_{U ∩ T}(ℱ|_U)`, read on abelian sheaves, **is** `H_T(ℱ_ab)|_U → H_{U ∩ T}(ℱ_ab|_U)`.

That is `forget_supportedSectionsRestrict_comm`, and it is the degree-zero case of the
coherence the square of [Stacks, Tag 0G87] needs: that [Stacks, Tag 0G74] part (2) commutes with
the module-level and the abelian excision.

## Main results

* `Stacks.Cohomology.SupportedComplexes.supportedSectionsSheafForgetIso_hom_app_ι`: the
  degree-zero comparison of [Stacks, Tag 0G6N] is compatible with the two inclusions into the
  ambient sheaf of sections.  It is the identity on sections, so this is a `rfl` after the
  sheaf, natural-transformation and group-homomorphism extensionality lemmas.
* `Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictNatIso_hom_app_ι` and
  `Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictNatIso_hom_app_ι`: the
  same for the two degree-zero excisions.  The module-level one is not provable by computation —
  `Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso` is assembled from
  `Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsRestrictIso`, so its
  components are an `Exists.choose` and the inclusion compatibility is the `choose_spec` that
  specifies them.
* `Stacks.Cohomology.SupportedComplexes.forget_supportedSectionsRestrict_comm`: **the
  degree-zero coherence**, at one module.
* `Stacks.Cohomology.SupportedComplexes.forgetRestrictCompIso`: forgetting the module structure
  and restricting to `U` is restricting to `U` and forgetting, as functors.  The identity.
* `Stacks.Cohomology.SupportedComplexes.excisionZero_hom_app`: **an excision built from the two
  derived-functor engines, in degree zero**, at arbitrary categories.
* `Stacks.Cohomology.SupportedComplexes.localCohomologyRestrictNatIso_zero_hom_app` and
  `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso_zero_hom_app`: that
  lemma applied to the module-level and to the abelian excision — each is the two engines
  composed, so each is one application.

## What is not proved here

**The coherence in a general degree `n` is not proved here.**  What it is *not* a consequence of
is the degree-zero **comparison**: the comparison of [Stacks, Tag 0G74] part (2) in degree `n` —
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorForgetIso` — is **not** the
derived functor of `Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedForgetIso`, and
cannot be: an injective resolution of `ℱ` by `𝒪_X`-modules is not an injective resolution of
`ℱ_ab`, the forgetful functor not preserving injectives.  That degreewise comparison is instead
descended from the unbounded derived category, where part (2) is proved by flasqueness
(`isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor` of this namespace).

It *is*, however, a formal consequence of the degree-zero **square**
`forget_supportedSectionsRestrict_comm` below.  On the unbounded derived category all four
comparisons are `CategoryTheory.Functor.rightDerivedDesc` of degree-zero data — the forgetful one
as `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`, pinned by
`abelianSupportedEndoForgetComparison_fac` — so two such composites agree as soon as they agree
after the derivation unit, which is what `CategoryTheory.Functor.rightDerived_ext` says and what
the degree-zero square supplies.  No new mathematics is needed in degree `n`; what is needed is a
derived-category form of each excision and the identification of each with its classical form.

Two routes to degree `n` are available: a derived-category excision for abelian sheaves matched
with `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso`, or a resolution
argument through sheaves that are acyclic for `H_T` rather than injective.

* The derived-category excision for abelian sheaves is
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsRestrictNatIso`, for
  arbitrary total right derived functors, with its defining factorization `..._fac`.  Its two
  presuppositions are
  `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose` and
  `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose_of_exact_leftAdjoint`, the latter
  because restriction of abelian sheaves to an open subset is right adjoint to the exact
  extension by zero and so preserves K-injectivity ([Stacks, Tag 08BJ]).
* The acyclic-resolution engine **is** in the library too:
  `Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic` splits `Rⁿ(G ∘ F)` as
  `F ⋙ Rⁿ G` for an exact `F` carrying injectives to `G`-acyclic objects, with no preservation of
  injectives assumed.  What is genuinely missing on that route is something else: the canonical
  comparison `Rⁿ(F ⋙ G) ⟶ F ⋙ Rⁿ G` for a merely exact `F`.
  `Stacks.Cohomology.RightDerivedEdge.edge` runs the other way and does require
  `F.PreservesInjectiveObjects`, so it is not that comparison; and without it the acyclic route
  cannot even state the degree-`n` comparison it would have to identify with
  `localCohomologySheafFunctorForgetIso`.  That is why the derived-category route is the one
  taken.

## Implementation notes

**Why the proof is a cancellation and not a computation.**  Three of the four comparisons in the
square are the identity on sections and could be checked sectionwise; the module-level excision
cannot, its components being a choice.  What specifies that choice is its compatibility with the
inclusion of the subsheaf of supported sections into the ambient sheaf, and that inclusion is a
monomorphism, so the square follows by cancelling it.  The four inclusion compatibilities are the
first three results above together with
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictIso_hom_ι`.

**Every chase is a helper at a variable category, applied with `exact`.**  The two sides of the
square compose in two spellings of one category — `AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules (structureSheafRing _)` for the modules on `U`, and
`↥U` and `(Opens.toTopCat X.carrier).obj U` for the space — and `rw` on
`CategoryTheory.Category.assoc` or on `CategoryTheory.Functor.map_comp` across either of them is
not type-correct at `implicit` transparency.  So each side is first proved in its *own* spelling,
where no crossing occurs, and the two are combined by `cancel_subobject`, which is stated at an
arbitrary category with all five objects implicit and all six morphisms explicit: every object is
then read off a given argument's type instead of being solved for, and the crossing is met by a
single definitional check rather than by unification against a metavariable.

For the same reason `Mono` for the abelian inclusion is taken from
`abelian_supportedSectionsSheafι_mono`, which states it at a *variable* abelian sheaf on the open
subset.  Instance search does not find it at the applied shape
`(abelianRestrictOpen U).obj (ℱ_ab)`: `AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι`
is `implicit_reducible` and `abelianRestrictOpen` is an abbreviation, so the instance's head
unfolds and the discrimination key no longer matches.

**No `@[stacks ...]` attribute is attached to any declaration here.**  Everything is a
compatibility between results that carry their own tags; this file states no numbered result of
the source.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

/-! ### Formal identities, each at an arbitrary category -/

/-- **A functor image followed by a comparison the inclusion turns back into a functor image.**
Given `g ≫ ι = Fn.map p` and `q ≫ p = r`, the composite `Fn.map q ≫ g ≫ ι` is `Fn.map r`.

Stated at arbitrary categories, every object implicit and every morphism explicit: this is the
step that would otherwise be a `rw` under the crossing of the two spellings of the category of
modules on the open subset, where the motive is not type-correct. -/
private theorem map_comp_tail {D E : Type*} [Category* D] [Category* E] (Fn : D ⥤ E)
    {a b c : D} {z : E} (q : a ⟶ b) (p : b ⟶ c) (r : a ⟶ c)
    (g : Fn.obj b ⟶ z) (ι : z ⟶ Fn.obj c)
    (hg : g ≫ ι = Fn.map p) (hqp : q ≫ p = r) :
    Fn.map q ≫ g ≫ ι = Fn.map r := by
  rw [hg, ← Fn.map_comp, hqp]

/-- **Two comparisons into a subobject agree when they agree after the inclusion.**  Given a
monomorphism `ι` out of the common target and two factorisations `f₁ ≫ g₁ ≫ ι = m` and
`f₂ ≫ g₂ ≫ ι = m` through one morphism `m`, the two two-factor composites are equal.

Stated at an arbitrary category, every object implicit and every morphism explicit, so that
applying it never asks the elaborator to solve an object metavariable across the two spellings of
the category of modules on the open subset. -/
private theorem cancel_subobject {D : Type*} [Category* D] {a b₁ b₂ c e : D}
    (f₁ : a ⟶ b₁) (g₁ : b₁ ⟶ c) (f₂ : a ⟶ b₂) (g₂ : b₂ ⟶ c) (ι : c ⟶ e) (m : a ⟶ e)
    (hι : Mono ι) (h₁ : f₁ ≫ g₁ ≫ ι = m) (h₂ : f₂ ≫ g₂ ≫ ι = m) :
    f₁ ≫ g₁ = f₂ ≫ g₂ :=
  have := hι
  (cancel_mono ι).1 (by rw [Category.assoc, Category.assoc, h₁, h₂])

/-! ### A two-engine excision in degree zero, at arbitrary categories -/

/-- **The degree-zero description of an excision built from the two derived-functor engines.**
Let `S` be an endofunctor of `A`, let `r : A ⥤ B` be exact and preserve injective objects, let
`S'` be an endofunctor of `B` and let `e : S ⋙ r ≅ r ⋙ S'` be a degree-zero excision.  The
degree-`n` excision is
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` followed by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, and in degree zero that
composite carries the canonical map of `S` to the canonical map of `S'`, through `e`.

This is `Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_zero` followed by
`Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_zero`, and it is stated
here at arbitrary categories so that the module-level and the abelian excision are two
applications of one lemma rather than two chases. -/
theorem excisionZero_hom_app {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [HasInjectiveResolutions B]
    (S : A ⥤ A) (r : A ⥤ B) (S' : B ⥤ B) [S.Additive] [r.Additive] [S'.Additive]
    [(r ⋙ S').Additive] [r.PreservesHomology]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r] [r.PreservesInjectiveObjects]
    (e : S ⋙ r ≅ r ⋙ S') (M : A) :
    r.map (S.toRightDerivedZero.app M) ≫
        (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S r (r ⋙ S') e 0 ≪≫
          Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso r S' 0).hom.app M =
      e.hom.app M ≫ S'.toRightDerivedZero.app (r.obj M) := by
  show r.map (S.toRightDerivedZero.app M) ≫
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso S r (r ⋙ S') e 0).hom.app M ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso r S' 0).hom.app M = _
  rw [← Category.assoc,
    Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app_zero S r (r ⋙ S') e M,
    Category.assoc,
    Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_zero r S' M]

/-! ### The degree-zero comparison is compatible with the inclusions -/

section ForgetIota

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier)

/-- **The degree-zero comparison of [Stacks, Tag 0G6N] is compatible with the two inclusions.**
Composing `H_Z(ℱ)_ab ≅ H_Z(ℱ_ab)` with the inclusion of the subsheaf of sections of `ℱ_ab`
supported on `Z` is the underlying morphism of abelian sheaves of the inclusion of the subsheaf
of sections of `ℱ` supported on `Z`.

Both inclusions are the identity on sections, and so is the comparison
`Stacks.Cohomology.SupportedComplexes.supportedSectionsSheafForgetIso`, whose components are
built from `Stacks.Cohomology.SupportedComplexes.supportedSectionsForgetAppIso`; so the identity
holds on a section of either side by `rfl`. -/
theorem supportedSectionsSheafForgetIso_hom_app_ι
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (supportedSectionsSheafForgetIso X Z).hom.app F ≫
        AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι Z
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj F) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).map
        (supportedSectionsSheafι Z F) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext s
  rfl

end ForgetIota

/-! ### The two degree-zero excisions are compatible with the inclusions -/

variable {X : Scheme.{u}} (T : Set X) (U : X.Opens)

/-- **The abelian inclusion of the subsheaf of supported sections is a monomorphism**, stated at
a variable space and a variable abelian sheaf on it.

This is the instance of `AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι`, restated
because instance search does not find it at an applied shape; see the implementation notes. -/
theorem abelian_supportedSectionsSheafι_mono {Y : TopCat.{u}} (Z : Set Y)
    (H : Y.Sheaf AddCommGrpCat.{u}) :
    Mono (AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι Z H) := inferInstance

/-- **The module-level degree-zero excision is compatible with the two inclusions.**  This is
the clause that *specifies* it:
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso` has as its components
the isomorphism produced by
`Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsRestrictIso`, which is
chosen, not constructed, and the only thing known about it is this compatibility. -/
theorem supportedSectionsRestrictNatIso_hom_app_ι (F : X.Modules) :
    (Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso T U).hom.app F ≫
        supportedSectionsSheafι (⇑U.ι ⁻¹' T) ((Scheme.Modules.restrictFunctor U.ι).obj F) =
      (Scheme.Modules.restrictFunctor U.ι).map (supportedSectionsSheafι T F) :=
  (Stacks.Perfect.SupportedSectionsRestriction.exists_supportedSectionsRestrictIso
    T U F).choose_spec

/-- **The abelian degree-zero excision is compatible with the two inclusions.**  This is
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictIso_hom_ι`, read at the
components of the natural isomorphism. -/
theorem abelianSupportedSectionsRestrictNatIso_hom_app_ι
    (G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :
    (abelianSupportedSectionsRestrictNatIso (X := X.carrier) T U).hom.app G ≫
        AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι (preimageSubset U T)
          ((abelianRestrictOpen U).obj G) =
      (abelianRestrictOpen U).map
        (AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι T G) :=
  abelianSupportedSectionsRestrictIso_hom_ι T U G

/-! ### Forgetting the module structure commutes with restriction -/

/-- **Forgetting the module structure and restricting to `U` is restricting to `U` and
forgetting.**  `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι` is a pushforward of sheaves
of modules along the functor of images of opens, and
`Stacks.Cohomology.SupportedComplexes.abelianRestrictOpen` is the pushforward of abelian sheaves
along that same functor, so the two composites are *definitionally* equal: the underlying abelian
sheaf of `ℱ|_U` is literally `V ↦ ℱ(j(V))`. -/
@[sga "4 IV 11.2.3" "special case"]
def forgetRestrictCompIso :
    Scheme.Modules.restrictFunctor U.ι ⋙
        _root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace) ≅
      _root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace) ⋙
        abelianRestrictOpen (X := X.carrier) U :=
  Iso.refl _

/-! ### The degree-zero coherence -/

/-- The module-level side of the square, composed with the abelian inclusion: it is the
restriction to `U` of the underlying morphism of the inclusion on `X`.

Written entirely in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling, so that no
crossing of the two spellings of the category of modules on `U` occurs inside the proof. -/
theorem forget_moduleExcision_comp_ι (F : X.Modules) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso
            T U).hom.app F) ≫
        (supportedSectionsSheafForgetIso U.toScheme.toRingedSpace (⇑U.ι ⁻¹' T)).hom.app
            ((Scheme.Modules.restrictFunctor U.ι).obj F) ≫
          AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι (⇑U.ι ⁻¹' T)
            ((_root_.SheafOfModules.toSheaf
              (structureSheafRing U.toScheme.toRingedSpace)).obj
                ((Scheme.Modules.restrictFunctor U.ι).obj F)) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
        ((Scheme.Modules.restrictFunctor U.ι).map (supportedSectionsSheafι T F)) :=
  map_comp_tail _ _ _ _ _ _
    (supportedSectionsSheafForgetIso_hom_app_ι U.toScheme.toRingedSpace (⇑U.ι ⁻¹' T)
      ((Scheme.Modules.restrictFunctor U.ι).obj F))
    (supportedSectionsRestrictNatIso_hom_app_ι T U F)

/-- The abelian side of the square, composed with the abelian inclusion: it is the restriction to
`U` of the underlying morphism of the inclusion on `X`, again.

Written entirely in the `Stacks.Cohomology.SupportedComplexes.abelianRestrictOpen` spelling. -/
theorem forget_abelianExcision_comp_ι (F : X.Modules) :
    (abelianRestrictOpen (X := X.carrier) U).map
          ((supportedSectionsSheafForgetIso X.toRingedSpace T).hom.app F) ≫
        (abelianSupportedSectionsRestrictNatIso (X := X.carrier) T U).hom.app
            ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) ≫
          AlgebraicGeometry.SheafOfModules.supportedSectionsSheafι (preimageSubset U T)
            ((abelianRestrictOpen U).obj
              ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F)) =
      (abelianRestrictOpen (X := X.carrier) U).map
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).map
          (supportedSectionsSheafι T F)) :=
  map_comp_tail _ _ _ _ _ _
    (abelianSupportedSectionsRestrictNatIso_hom_app_ι T U
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F))
    (supportedSectionsSheafForgetIso_hom_app_ι X.toRingedSpace T F)

/-- **Forgetting the module structure commutes with the two degree-zero excisions.**  For a
scheme `X`, a subset `T ⊆ X`, an open subscheme `U ⊆ X` and an `𝒪_X`-module `ℱ`, the square

`H_T(ℱ)|_U ⟶ H_{U ∩ T}(ℱ|_U)` read on abelian sheaves, versus
`H_T(ℱ_ab)|_U ⟶ H_{U ∩ T}(ℱ_ab|_U)`,

commutes: the module-level excision of
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`, read through the
comparison `Stacks.Cohomology.SupportedComplexes.supportedSectionsSheafForgetIso` of
[Stacks, Tag 0G6N] on `U`, is the abelian excision
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictNatIso` read through that
comparison on `X`.

That the equation is well-typed is `forgetRestrictCompIso`: the source of the left-hand side is
`(H_T(ℱ)|_U)_ab` and of the right-hand side `(H_T(ℱ)_ab)|_U`, which are definitionally equal.

This is the **degree-zero** case of the coherence between [Stacks, Tag 0G74] part (2) and the two
excisions, which is what the square of [Stacks, Tag 0G87] needs in every degree; the higher
degrees are not a formal consequence, both excisions being right derived functors of these
degree-zero ones and the comparison in higher degrees not being the derived functor of this
one. -/
theorem forget_supportedSectionsRestrict_comm (F : X.Modules) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing U.toScheme.toRingedSpace)).map
          ((Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso
            T U).hom.app F) ≫
        (supportedSectionsSheafForgetIso U.toScheme.toRingedSpace (⇑U.ι ⁻¹' T)).hom.app
          ((Scheme.Modules.restrictFunctor U.ι).obj F) =
      (abelianRestrictOpen (X := X.carrier) U).map
          ((supportedSectionsSheafForgetIso X.toRingedSpace T).hom.app F) ≫
        (abelianSupportedSectionsRestrictNatIso (X := X.carrier) T U).hom.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).obj F) :=
  cancel_subobject _ _ _ _ _ _
    (abelian_supportedSectionsSheafι_mono (⇑U.ι ⁻¹' T)
      ((_root_.SheafOfModules.toSheaf
        (structureSheafRing U.toScheme.toRingedSpace)).obj
          ((Scheme.Modules.restrictFunctor U.ι).obj F)))
    (forget_moduleExcision_comp_ι T U F) (forget_abelianExcision_comp_ι T U F)

/-! ### The two excisions in degree zero -/

/-- **The module-level excision in degree zero is the degree-zero excision.**
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso` in degree `0` carries the
canonical map `H_T ⟶ ℋ ⁰_T` to the canonical map on `U`, through
`Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso`.

One application of `excisionZero_hom_app`: that excision is by definition the two engines
composed, in exactly that order. -/
theorem localCohomologyRestrictNatIso_zero_hom_app (F : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
          ((Stacks.Perfect.LocalCohomologyExcision.supportedSectionsOn X
            T).toRightDerivedZero.app F) ≫
        (Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso
          T U 0).hom.app F =
      (Stacks.Perfect.LocalCohomologyExcision.supportedSectionsRestrictNatIso
          T U).hom.app F ≫
        (Stacks.Perfect.LocalCohomologyExcision.supportedSectionsOn U.toScheme
          (⇑U.ι ⁻¹' T)).toRightDerivedZero.app ((Scheme.Modules.restrictFunctor U.ι).obj F) :=
  excisionZero_hom_app _ _ _ _ _

/-- **The abelian excision in degree zero is the abelian degree-zero excision.**  The same
statement for `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso` and
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictNatIso`, and the same one
application of `excisionZero_hom_app`.

Together with the previous result and
`forget_supportedSectionsRestrict_comm` this is what a proof of the coherence in *every* degree
has to start from: the two excisions agree with their degree-zero data, and the degree-zero data
are matched by [Stacks, Tag 0G6N]. -/
theorem abelianLocalCohomologyRestrictNatIso_zero_hom_app
    (G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :
    (abelianRestrictOpen (X := X.carrier) U).map
          ((abelianSupportedSections T).toRightDerivedZero.app G) ≫
        (abelianLocalCohomologyRestrictNatIso (X := X.carrier) T U 0).hom.app G =
      (abelianSupportedSectionsRestrictNatIso (X := X.carrier) T U).hom.app G ≫
        (abelianSupportedSections (preimageSubset U T)).toRightDerivedZero.app
          ((abelianRestrictOpen U).obj G) :=
  excisionZero_hom_app _ _ _ _ _

end Stacks.Cohomology.SupportedComplexes

end
