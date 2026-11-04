module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionTails
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes

/-!
# The derived stalk of an iterated derived pullback, unconditionally

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and `x` a point of `X`.
`AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat` reduced the coherence of the derived
stalk formula of Stacks 0098 with the composition formula of Tag 0D5S to a single equation at a
K-flat complex.  This file proves that equation — at *every* cochain complex, K-flat or not — and
so removes the hypothesis.

The equation is a composite of eight morphisms in the derived category of `𝒪_{X,x}`-modules, and
it closes by a chase through seven identities that the development already has:

1. the characterizing equation `AlgebraicGeometry.derivedPullbackStalkIso_comp_comparison` of the
   derived stalk formula, for `g` at `f x` and for `f` at `x`;
2. the naturality of `AlgebraicGeometry.derivedPullbackStalkIso` for `f` along the comparison on
   complexes for `g`, used forwards;
3. the naturality of `AlgebraicGeometry.derivedStalkExtensionCompIso` and of the comparison of
   derived against degreewise extension of scalars;
4. the merged extension-of-scalars tail
   `AlgebraicGeometry.derivedStalkExtensionCompIso_hom_app_comp_comparison`;
5. the composition formula on complexes
   `AlgebraicGeometry.pullbackComparisonOnComplex_comp`;
6. the compatibility of the *underived* stalk formula with composition,
   `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_inv_app`, applied degreewise;
7. `CategoryTheory.Iso.inv_hom_id_assoc` for the Tag 0D5S isomorphism.

No K-flatness and no inverse of a comparison is used anywhere.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.derivedStalkTail_comp`: **the degreewise content of the coherence.**  The
  stalk formula for `f` read backwards, then extension of scalars of the stalk formula for `g`
  read backwards, then the degreewise merge of the two extensions of scalars, is the stalk of the
  pullback-composition isomorphism followed by the stalk formula for `f ≫ g` read backwards.
  This is `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_inv_app` applied in each degree and
  localized.
* `AlgebraicGeometry.derivedPullbackStalkCompIso_hom_app_comp_comparison`: the two-step derived
  stalk computation, composed with the tail of the one-step computation for `f ≫ g`, is the Tag
  0D5S comparison followed by the right-hand side of the characterizing equation for `f ≫ g`.
* `AlgebraicGeometry.derivedPullbackStalkCompIso_comp_comparison`: **the hypothesis of
  `derivedPullbackStalkIso_comp_of_kFlat`, proved at every complex.**
* `AlgebraicGeometry.derivedPullbackStalkIso_comp`,
  `AlgebraicGeometry.derivedPullbackStalkCompIso_hom_eq` and
  `AlgebraicGeometry.derivedPullbackStalkCompIso_eq`: **the coherence itself.**  The two-step
  derived stalk computation of an iterated derived pullback *is* the Tag 0D5S composition
  isomorphism followed by the one-step computation, with no hypothesis.

## Implementation notes

*Why the chase is run at abstract objects and morphisms.*  Every composite occurring in the
equation is a morphism of the derived category of `𝒪_{X,x}`-modules, and the chase uses nothing
about its factors beyond the seven identities listed above.  It is therefore stated and proved as
`StacksDraft.DerivedStalkCompositionChase.stalkCompChase`, for free objects and free morphisms of
an arbitrary category, and applied by `exact`.  This is not a stylistic choice.  The equation
mixes the two spellings of the category of modules on a scheme — `AlgebraicGeometry.Scheme.Modules
X` and `CategoryTheory.SheafOfModules (structureSheafRing X.toSheafedSpace)`,
which carry definitionally but not *reducibly* equal `Category` instances — and likewise the two
spellings `(f ≫ g) x` and `g (f x)` of the image point.  A goal of that shape is not type-correct
at the transparency at which `rw`, `simp` and even `conv_lhs` check their motives, so every one of
them fails on it with "did not find an occurrence of the pattern" against a pattern that is
plainly there.  At free objects and morphisms there is nothing to unfold, the rewrites all fire,
and the single conversion is paid once by `exact`.

*Why the tail identity is assembled by `refine` rather than by `rw`.*  The same obstruction makes
`AlgebraicGeometry.derivedStalkTail_comp` unprovable by rewriting: its statement mixes the two
spellings of the image point, so no rewrite fires.  Instead the abstract lemma
`StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIso_hom_app_comp_eqToHom` is
applied to the goal by `refine ... .trans ?_`, which leaves a goal that the *elaborator* has
written; the remaining steps collect the factors into one `DerivedCategory.Q.map` and reduce to a
degreewise statement, and no term in that chain is one this file had to spell out.

*Why the transport along the equation of germ maps is stated for a free homomorphism.*  The merge
of the two degreewise extensions of scalars is `ModuleCat.extendScalarsComp` at the two germ maps,
transported along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`.  The germ map of `f ≫ g` is not
a variable, so that equation cannot be substituted away in place; stated for a free `φ` with
`h : φ = b.comp a` it can, and the `eqToHom` it carries becomes an identity.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.ModuleSkyscraper
open StacksDraft.DerivedExtensionScalarsComp

universe u

namespace StacksDraft.DerivedExtensionScalarsComp

attribute [local instance] HasDerivedCategory.standard

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- **The composition isomorphism for degreewise extension of scalars, transported along an
equation of ring homomorphisms.**  Let `a : R →+* S`, `b : S →+* T` and let `φ : R →+* T` be
*equal* to `b ∘ a` rather than that term.  Then `extensionScalarsComplexCompIso`, followed by the
transport of its target along the equation, is the localization of the degreewise merge of the two
extension-of-scalars functors, transported in the same way.

Proved by substituting the equation, after which both `eqToHom`s are identities. -/
theorem extensionScalarsComplexCompIso_hom_app_comp_eqToHom
    (a : R →+* S) (b : S →+* T) (φ : R →+* T) (h : φ = b.comp a)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extensionScalarsComplexCompIso a b).hom.app C ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj C) h.symm) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        ((ModuleCat.extendScalarsComp a b).symm ≪≫
          eqToIso (congrArg ModuleCat.extendScalars h.symm)) (ComplexShape.up ℤ)).hom.app C) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, eqToIso_refl, Iso.trans_refl]
  rfl

end StacksDraft.DerivedExtensionScalarsComp

namespace StacksDraft.DerivedStalkCompositionChase

section

variable {C D : Type*} [Category C] [Category D]

/-- A functor applied to a composite of two morphisms, as a composite. -/
theorem map_comp₂ (F : C ⥤ D) {W X Y : C} (α : W ⟶ X) (β : X ⟶ Y) :
    F.map (α ≫ β) = F.map α ≫ F.map β :=
  CategoryTheory.Functor.map_comp _ _ _

/-- A functor applied to a composite of three morphisms, as a composite. -/
theorem map_comp₃ (F : C ⥤ D) {W X Y Z : C} (α : W ⟶ X) (β : X ⟶ Y) (γ : Y ⟶ Z) :
    F.map (α ≫ β ≫ γ) = F.map α ≫ F.map β ≫ F.map γ := by
  rw [map_comp₂, map_comp₂]

end

section

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Two localized morphisms of cochain complexes, as one. -/
theorem Q_map_comp₂ {K L M : CochainComplex C ℤ} (α : K ⟶ L) (β : L ⟶ M) :
    DerivedCategory.Q.map α ≫ DerivedCategory.Q.map β = DerivedCategory.Q.map (α ≫ β) :=
  (CategoryTheory.Functor.map_comp _ _ _).symm

/-- Three localized morphisms of cochain complexes, as one. -/
theorem Q_map_comp₃ {K L M N : CochainComplex C ℤ} (α : K ⟶ L) (β : L ⟶ M) (γ : M ⟶ N) :
    DerivedCategory.Q.map α ≫ DerivedCategory.Q.map β ≫ DerivedCategory.Q.map γ =
      DerivedCategory.Q.map (α ≫ β ≫ γ) :=
  (congrArg (fun t => DerivedCategory.Q.map α ≫ t) (Q_map_comp₂ β γ)).trans
    (Q_map_comp₂ α (β ≫ γ))

end

section

variable {C : Type*} [Category C]
variable {O₀ O₁ O₂ O₃ O₄ P₁ P₂ A₁ A₂ A₃ A₄ A₅ A₆ B₁ B₂ B₃ B₄ B₅ B₆ : C}

/-- **The diagram chase behind the coherence of the derived stalk formula with the composition
formula of Tag 0D5S**, at free objects and free morphisms of an arbitrary category.

Read `ψ` as the two-step derived stalk computation, `tcm ≫ tcc` as the tail of the one-step
computation for `f ≫ g`, and `sa ≫ scfg ≫ mdfg ≫ nufg` as the Tag 0D5S comparison followed by the
right-hand side of the characterizing equation for `f ≫ g`.  The ten hypotheses are, in order:
the components of the two-step computation; the naturality of the merge of the two derived
extensions of scalars; the merged extension-of-scalars tail; the characterizing equation for `g`
at `f x`, carried by extension of scalars along the germ map of `f`; the naturality of the stalk
formula for `f`; the naturality of the comparison of derived against degreewise extension of
scalars; the characterizing equation for `f` at `x`; the composition formula on complexes; the
naturality of the factorization of the derived stalk functor; and the degreewise content.

Stated abstractly because the concrete equation is not type-correct at the transparency at which
`rw` and `simp` check their motives; see the implementation notes. -/
theorem stalkCompChase
    {ψ : O₀ ⟶ P₁} {tcm : P₁ ⟶ P₂} {tcc : P₂ ⟶ O₄}
    {φf : O₀ ⟶ A₁} {taφg : A₁ ⟶ A₂} {e : A₂ ⟶ P₁} {tatbm : A₂ ⟶ A₃} {e' : A₃ ⟶ P₂}
    {tatbc : A₃ ⟶ A₄} {tac : A₄ ⟶ A₅} {esc : A₅ ⟶ A₆} {eqh : A₆ ⟶ O₄}
    {tacg : A₁ ⟶ B₂} {slf : O₀ ⟶ B₁} {φf' : B₁ ⟶ B₂} {tam : B₂ ⟶ B₃} {tanu : B₃ ⟶ A₄}
    {tac' : B₃ ⟶ B₄} {qw : B₄ ⟶ A₅} {scf : B₁ ⟶ B₅} {mdf : B₅ ⟶ B₆} {nuf : B₆ ⟶ B₄}
    {sqm : B₅ ⟶ O₂} {qsm : B₆ ⟶ O₃} {mdfg : O₂ ⟶ O₃} {nufg : O₃ ⟶ O₄}
    {sa : O₀ ⟶ O₁} {scfg : O₁ ⟶ O₂}
    (h₁ : ψ = φf ≫ taφg ≫ e)
    (h₂ : e ≫ tcm = tatbm ≫ e')
    (h₃ : e' ≫ tcc = tatbc ≫ tac ≫ esc ≫ eqh)
    (h₄ : taφg ≫ tatbm ≫ tatbc = tacg ≫ tam ≫ tanu)
    (h₅ : φf ≫ tacg = slf ≫ φf')
    (h₆ : tanu ≫ tac = tac' ≫ qw)
    (h₇ : φf' ≫ tam ≫ tac' = scf ≫ mdf ≫ nuf)
    (h₈ : sa ≫ scfg = slf ≫ scf ≫ sqm)
    (h₉ : sqm ≫ mdfg = mdf ≫ qsm)
    (h₁₀ : nuf ≫ qw ≫ esc ≫ eqh = qsm ≫ nufg) :
    ψ ≫ tcm ≫ tcc = sa ≫ scfg ≫ mdfg ≫ nufg := by
  rw [h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, h₃, reassoc_of% h₄, reassoc_of% h₅, reassoc_of% h₆, reassoc_of% h₇,
    h₁₀, ← reassoc_of% h₉, reassoc_of% h₈]

end

end StacksDraft.DerivedStalkCompositionChase

namespace AlgebraicGeometry

open StacksDraft.DerivedStalkCompositionChase

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)

/-- The components of the two-step derived stalk computation of an iterated derived pullback: the
derived stalk formula for `f` at `x`, then extension of scalars along the germ map of `f` of the
derived stalk formula for `g` at `f x`, then the merge of the two extensions of scalars. -/
theorem derivedPullbackStalkCompIso_hom_app (K : DerivedCategory Z.Modules) :
    (derivedPullbackStalkCompIso f g x).hom.app K =
      (derivedPullbackStalkIso f x).hom.app ((derivedPullback g.toLRSHom.toShHom).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map
          ((derivedPullbackStalkIso g (f x)).hom.app K) ≫
        (derivedStalkExtensionCompIso f g x).hom.app ((derivedStalkFunctor (g (f x))).obj K) :=
  rfl

/-- **The degreewise content of the coherence.**  At a cochain complex `P` of `𝒪_Z`-modules, the
stalk formula of Stacks 0098 for `f` read backwards on the degreewise pullback of `P` along `g`,
then extension of scalars along the germ map of `f` of the stalk formula for `g` read backwards,
then the degreewise merge of the two extensions of scalars, is the stalk at `x` of the
pullback-composition isomorphism followed by the stalk formula for `f ≫ g` read backwards —
everything localized to the derived category.

This is `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_inv_app` in each degree, with the two
spellings of the pullback-composition isomorphism identified by
`Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp`. -/
theorem derivedStalkTail_comp (P : CochainComplex Z.Modules ℤ) :
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (pullbackStalkIso f x).symm
          (ComplexShape.up ℤ)).hom.app
        (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} (f.stalkMap x).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex (pullbackStalkIso g (f x)).symm
            (ComplexShape.up ℤ)).hom.app P)) ≫
      (extensionScalarsComplexCompIso (g.stalkMap (f x)).hom (f.stalkMap x).hom).hom.app
        (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
      eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj
        (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x).symm) =
    DerivedCategory.Q.map
        (((modulesStalkFunctor X x).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso
            (modulePullbackComp f.toLRSHom.toShHom g.toLRSHom.toShHom)
            (ComplexShape.up ℤ)).hom.app P)) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (pullbackStalkIso (f ≫ g) x).symm
        (ComplexShape.up ℤ)).hom.app P) := by
  refine (congrArg (fun t => _ ≫ _ ≫ t)
    (extensionScalarsComplexCompIso_hom_app_comp_eqToHom (g.stalkMap (f x)).hom
      (f.stalkMap x).hom ((f ≫ g).stalkMap x).hom (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x)
      (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))).trans ?_
  refine (Q_map_comp₃ _ _ _).trans ?_
  refine (congrArg DerivedCategory.Q.map ?_).trans (Q_map_comp₂ _ _).symm
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplex_map_f, Iso.symm_hom]
  have hmod := pullbackStalkIso_comp_inv_app f g x (P.X n)
  rw [extendScalarsStalkComp_eq,
    Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp] at hmod
  exact hmod.symm

/-- **The two-step derived stalk computation against the tail of the one-step computation.**  At
every cochain complex `P` of `𝒪_Z`-modules, the two-step computation `derivedPullbackStalkCompIso`
followed by the comparisons that the characterizing equation of
`AlgebraicGeometry.derivedPullbackStalkIso` for `f ≫ g` composes with is the Tag 0D5S comparison
followed by the right-hand side of that equation.

This is the chase `StacksDraft.DerivedStalkCompositionChase.stalkCompChase` at the ten identities
listed in its docstring; no K-flatness hypothesis and no inverse of a comparison occurs. -/
theorem derivedPullbackStalkCompIso_hom_app_comp_comparison (P : CochainComplex Z.Modules ℤ) :
    (derivedPullbackStalkCompIso f g x).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
          ((modulesStalkFunctor Z ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
          (((modulesStalkFunctor Z ((f ≫ g) x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (derivedStalkFunctor x).map ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
            g.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj P)) ≫
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
        (modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (pullbackStalkIso (f ≫ g) x).symm (ComplexShape.up ℤ)).hom.app P) := by
  have h₁ := derivedPullbackStalkCompIso_hom_app f g x (DerivedCategory.Q.obj P)
  have h₂ := ((derivedStalkExtensionCompIso f g x).hom.naturality
    ((modulesStalkFunctor Z (g (f x))).mapDerivedCategoryFactors.hom.app P)).symm
  have h₃ := derivedStalkExtensionCompIso_hom_app_comp_comparison f g x
    (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hcg := derivedPullbackStalkIso_comp_comparison g (f x) P
  have h₄ := ((map_comp₃ (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor
      _ _ _).symm.trans
    (congrArg (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map hcg)).trans
    (map_comp₃ (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor _ _ _)
  have h₅ := ((derivedPullbackStalkIso f x).hom.naturality
    (pullbackComparisonOnComplex g P)).symm
  have h₆ := (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).comparison.naturality
    ((NatIso.mapHomologicalComplex (pullbackStalkIso g (f x)).symm
      (ComplexShape.up ℤ)).hom.app P)
  have h₇ := derivedPullbackStalkIso_comp_comparison f x
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hcomp := pullbackComparisonOnComplex_comp f g P
  have h₈ := ((map_comp₂ (derivedStalkFunctor x) _ _).symm.trans
    (congrArg (derivedStalkFunctor x).map hcomp)).trans
    (map_comp₃ (derivedStalkFunctor x) _ _ _)
  have h₉ := (modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso
      (modulePullbackComp f.toLRSHom.toShHom g.toLRSHom.toShHom) (ComplexShape.up ℤ)).hom.app P)
  exact stalkCompChase h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ (derivedStalkTail_comp f g x P)

/-- **The hypothesis of `AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat`, at every
complex.**  The two-step derived stalk computation, read backwards along the Tag 0D5S composition
isomorphism and composed with the comparison of derived against degreewise extension of scalars
along the germ map of `f ≫ g`, satisfies the equation which characterizes
`AlgebraicGeometry.derivedPullbackStalkIso` for `f ≫ g`.

This is `derivedPullbackStalkCompIso_hom_app_comp_comparison` with the Tag 0D5S comparison
cancelled against its inverse. -/
theorem derivedPullbackStalkCompIso_comp_comparison (P : CochainComplex Z.Modules ℤ) :
    (derivedStalkFunctor x).map ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
            g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
        (derivedPullbackStalkCompIso f g x).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
          ((modulesStalkFunctor Z ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
          (((modulesStalkFunctor Z ((f ≫ g) x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
        (modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (pullbackStalkIso (f ≫ g) x).symm (ComplexShape.up ℤ)).hom.app P) :=
  (congrArg (fun t => (derivedStalkFunctor x).map
      ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
        g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫ t)
    (derivedPullbackStalkCompIso_hom_app_comp_comparison f g x P)).trans
    (Iso.inv_hom_id_assoc ((derivedStalkFunctor x).mapIso
      ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom).app
        (DerivedCategory.Q.obj P))) _)

/-- **The coherence of the derived stalk formula with the composition formula of Tag 0D5S.**  The
two-step derived stalk computation of an iterated derived pullback, read backwards along the Tag
0D5S composition isomorphism, is the one-step computation for `f ≫ g`.

This is `AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat` with its hypothesis discharged
by `derivedPullbackStalkCompIso_comp_comparison`. -/
theorem derivedPullbackStalkIso_comp :
    (Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x)).inv ≫ (derivedPullbackStalkCompIso f g x).hom =
      (derivedPullbackStalkIso (f ≫ g) x).hom :=
  derivedPullbackStalkIso_comp_of_kFlat f g x
    (fun P _ => derivedPullbackStalkCompIso_comp_comparison f g x P)

/-- **The coherence, as an equation of morphisms of functors.**  The two-step derived stalk
computation is the Tag 0D5S composition isomorphism followed by the one-step computation. -/
theorem derivedPullbackStalkCompIso_hom_eq :
    (derivedPullbackStalkCompIso f g x).hom =
      (Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x)).hom ≫ (derivedPullbackStalkIso (f ≫ g) x).hom :=
  derivedPullbackStalkCompIso_hom_eq_of_kFlat f g x
    (fun P _ => derivedPullbackStalkCompIso_comp_comparison f g x P)

/-- **The coherence, as an equality of isomorphisms.**  This is the form a consumer reasoning
about the derived base change map of Stacks 08HY applies: the composition isomorphism appears
there in the adjoint description of the map, and this says what the derived stalk does to it. -/
theorem derivedPullbackStalkCompIso_eq :
    derivedPullbackStalkCompIso f g x =
      Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x) ≪≫ derivedPullbackStalkIso (f ≫ g) x :=
  derivedPullbackStalkCompIso_eq_of_kFlat f g x
    (fun P _ => derivedPullbackStalkCompIso_comp_comparison f g x P)

end AlgebraicGeometry

end
