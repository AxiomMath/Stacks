module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall

/-!
# Sections over an object of a site are surjective where the first cohomology vanishes

Let `J` be a Grothendieck topology on a category `C` whose objects may live one universe above
its morphisms, and let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of abelian sheaves for
`J`.  If `H¹(U, X₁)` vanishes then every section of `X₃` over `U` lifts to a section of `X₂`.

The two halves of this are in the library and nothing joined them.  The long exact sequence in
the object variable of a fixed left exact additive functor gives
`Stacks.Cohomology.epi_map_of_isZero_rightDerived_one`, and the identification of Mathlib's
`CategoryTheory.Sheaf.H'` with the right derived functors of sections over an object is
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections`.  Composing them is
this file.

## Main results

* `Stacks.Cohomology.ObjectSections.epi_sheafSections_map_of_isZero_sheafH'`: the map on sections
  over `U` is an epimorphism of abelian groups.
* `Stacks.Cohomology.ObjectSections.surjective_sections_of_isZero_sheafH'`: the same read as
  surjectivity of a function.

## Implementation notes

The `CategoryTheory.Ext` universe of `CategoryTheory.Sheaf.H'` is the *morphism* universe `v` of
the site, which is the universe at which the vanishing statements about the small étale and big
`τ`-sites of a scheme are stated — see
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`.  The sibling
`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation` is pinned at
`max u v` instead, which on a site whose objects live above its morphisms is one universe too
high to meet those statements, so it is not usable here.

No `@[stacks]` attribute: this is the mechanism behind [Stacks, Tag 01F1]/[Stacks, Tag 0157] and
not a delimited part of either.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Cohomology.ObjectSections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- **Sections over an object of a site are right exact where the first cohomology of the kernel
vanishes.**  For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of abelian sheaves with
`H¹(U, X₁) = 0`, the map `Γ(U, X₂) ⟶ Γ(U, X₃)` is an epimorphism. -/
public theorem epi_sheafSections_map_of_isZero_sheafH'
    {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact) (U : C)
    (h : IsZero (Sheaf.H'.{v} T.X₁ 1 U)) :
    Epi (((sheafSections J AddCommGrpCat.{v}).obj (op U)).map T.g) :=
  Stacks.Cohomology.epi_map_of_isZero_rightDerived_one _ hT
    (h.of_iso (FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{v} J T.X₁ 1 U).symm)

/-- **Sections over an object of a site are surjective where the first cohomology of the kernel
vanishes.**  This is `epi_sheafSections_map_of_isZero_sheafH'` read as surjectivity of the map of
sections itself. -/
public theorem surjective_sections_of_isZero_sheafH'
    {T : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hT : T.ShortExact) (U : C)
    (h : IsZero (Sheaf.H'.{v} T.X₁ 1 U)) :
    Function.Surjective
      (((sheafToPresheaf J AddCommGrpCat.{v}).map T.g).app (op U)) :=
  (AddCommGrpCat.epi_iff_surjective _).1 (epi_sheafSections_map_of_isZero_sheafH' J hT U h)

/-! ### Sheaves of modules -/

section Modules

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}] (R : Sheaf J RingCat.{v})

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] in
/-- **A short exact sequence of sheaves of modules has short exact underlying abelian
sheaves.**  The monomorphism and the exactness come from `SheafOfModules.toSheaf` preserving
finite limits, the epimorphism from
`Stacks.SheafOfModules.EpiMono.preservesEpimorphismsToSheaf`. -/
public theorem shortExact_map_toSheaf {T : ShortComplex (SheafOfModules.{v} R)}
    (hT : T.ShortExact) : (T.map (SheafOfModules.toSheaf.{v} R)).ShortExact :=
  have := hT.mono_f
  have := hT.epi_g
  { exact := hT.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
    mono_f := (SheafOfModules.toSheaf.{v} R).map_mono _
    epi_g := (SheafOfModules.toSheaf.{v} R).map_epi _ }

/-- **Sections of sheaves of modules over an object of a site are surjective where the first
cohomology of the kernel vanishes.**  For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
sheaves of `R`-modules whose underlying abelian sheaf `X₁` has `H¹(U, X₁) = 0`, every section of
`X₃` over `U` lifts to a section of `X₂` over `U`. -/
public theorem surjective_val_app_of_isZero_sheafH'
    {T : ShortComplex (SheafOfModules.{v} R)} (hT : T.ShortExact) (U : C)
    (h : IsZero (Sheaf.H'.{v} ((SheafOfModules.toSheaf.{v} R).obj T.X₁) 1 U)) :
    Function.Surjective (T.g.val.app (op U)) :=
  surjective_sections_of_isZero_sheafH' J (shortExact_map_toSheaf J R hT) U h

omit [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- **A morphism of sheaves of modules which is surjective on the sections over the members of a
generating presieve is an epimorphism.**  The presieve need not be a sieve, which is what makes
this applicable to the affine opens of a scheme: an open subset of an affine open need not be
affine. -/
public theorem epi_of_surjective_on_presieve
    {M N : SheafOfModules.{v} R} (f : M ⟶ N) (P : ∀ V : C, Presieve V)
    (hP : ∀ V : C, Sieve.generate (P V) ∈ J V)
    (hsurj : ∀ (V : C) ⦃W : C⦄ (g : W ⟶ V), P V g →
      Function.Surjective
        (((PresheafOfModules.toPresheaf R.obj).map f.val).app (op W))) :
    Epi f := by
  set φ := (PresheafOfModules.toPresheaf R.obj).map f.val with hφ
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective f ⟨fun {V} y ↦ ?_⟩
  refine J.superset_covering ?_ (hP V)
  rintro W g ⟨W', a, b, hb, rfl⟩
  obtain ⟨t, ht⟩ := hsurj V b hb
    (((PresheafOfModules.toPresheaf R.obj).obj N.val).map b.op y)
  refine ⟨((PresheafOfModules.toPresheaf R.obj).obj M.val).map a.op t, ?_⟩
  rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp]

end Modules

end Stacks.Cohomology.ObjectSections

end
