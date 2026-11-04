module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionGeneral
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionTails
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexesAnyModel

/-!
# The derived stalk formula of Stacks 0098 is coherent with the composition formula of Tag 0D5S

`AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat_general` reduces that coherence — that the
two-step derived stalk computation of `Lg^* ⋙ Lf^*` is the composition isomorphism of Tag 0D5S
followed by the one-step computation for `f ≫ g` — to a single equation at a K-flat complex, and
leaves the equation as a hypothesis. This module proves that equation, at *every* cochain complex,
and so makes the coherence unconditional.

The equation is a composite of eight morphisms between objects of a derived category, and its
content is degreewise: the compatibility of the *underived* stalk formula of Stacks 0098 with
composition. The proof separates the two.

* The chase is run in `StacksDraft.CompositionChase`, where every object and every morphism is a
  variable and the eight hypotheses are the naturality squares and characterizing equations the
  composite is built from. Nothing is rewritten inside a concrete term: the two spellings of the
  category of modules on a scheme carry two `Category` instances which are definitionally but not
  reducibly equal, and a `rewrite` keyed on a component of a composite of morphisms of functors
  between them is rejected as producing an ill-typed motive.
* The degreewise heart is `pullbackStalkIso_comp_inv_mapHomologicalComplex`: at each degree it is
  `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_inv_app` together with
  `Stacks.ModuleSkyscraper.extendScalarsStalkComp_hom_app`, which carries the transport along
  `Stacks.ModuleSkyscraper.stalkMap_hom_comp`.

## Main results

* `StacksDraft.CompositionChase.chase`: the eight-step diagram chase, for free categories and
  free morphisms.
* `AlgebraicGeometry.pullbackStalkIso_comp_inv_mapHomologicalComplex`: Stacks 0098's composition
  compatibility on complexes.
* `AlgebraicGeometry.pullbackStalkIso_comp_inv_mapDerived`: the same in the derived category.
* `AlgebraicGeometry.derivedPullbackStalkCompIso_hom_app_general`: the three factors of the
  two-step computation.
* `AlgebraicGeometry.derivedPullbackStalkCompIso_hcomp`: **the equation.** The hypothesis of
  `AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat_general`, at every cochain complex and
  with no K-flatness assumed.
* `AlgebraicGeometry.derivedPullbackStalkIso_comp_general` and
  `AlgebraicGeometry.derivedPullbackStalkCompIso_eq_general`: **the coherence, unconditionally.**

## Implementation notes

The chase takes the two-step computation as an opaque morphism `U` together with the equation
`U = u₁ ≫ u₂ ≫ u₃` naming its three factors, rather than the composite itself. Supplying the
composite would need that equation rewritten into the goal, and `rewrite` fails there for the
reason above; as a hypothesis it is discharged by
`derivedPullbackStalkCompIso_hom_app_general`, which is `rfl`.

Everything carries `HasDerivedCategory` binders. A consumer computing the derived stalk of a
chart's identification works at the locally small model of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, and a statement proved at the standard model
would say nothing there; that is why the four modules this one chains together were taken off
`HasDerivedCategory.standard`.

No tag attribute is placed here. Stacks 0098 is the stalk formula for one morphism and is carried
elsewhere; what is proved here is a coherence *between* two instances of it, which is not part of
what the tag asserts.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace StacksDraft.CompositionChase

variable {C : Type*} [Category* C]

/-- **The eight-step chase.** The composite `m ≫ U ≫ t₁ ≫ t₂` equals `r₁ ≫ r₂ ≫ r₃`
whenever the nine displayed equations hold: `h₀` names the three factors of `U`, `h₁`, `h₄`, `h₅`
and `h₈` are naturality squares, `h₂`, `h₃` and `h₆` are characterizing equations of derived
functor comparisons, `h₇` presents one factor through an inverse, and `h₉` is the degreewise
heart.

Every category, object and morphism is a variable, which is what makes the chase a sequence of
rewrites rather than a fight with transparency. -/
public theorem chase {O₀ O₁ O₂ O₃ O₄ O₅ O₆ R₁ R₂ Da Pa Pb Pc W₁ W₂ N₁ Q₁ X₁ X₂ : C}
    (m : O₀ ⟶ O₁) (U : O₁ ⟶ O₄)
    (u₁ : O₁ ⟶ O₂) (u₂ : O₂ ⟶ O₃) (u₃ : O₃ ⟶ O₄) (t₁ : O₄ ⟶ O₅) (t₂ : O₅ ⟶ O₆)
    (r₁ : O₀ ⟶ R₁) (r₂ : R₁ ⟶ R₂) (r₃ : R₂ ⟶ O₆)
    (a₁ : O₃ ⟶ Da) (d : Da ⟶ O₅) (a₂ : Da ⟶ Pa) (p : Pa ⟶ Pb) (e₁ : Pb ⟶ Pc) (e₂ : Pc ⟶ O₆)
    (v₁ : O₂ ⟶ W₁) (v₂ : W₁ ⟶ W₂) (v₃ : W₂ ⟶ Pa) (n : O₁ ⟶ N₁) (s : N₁ ⟶ W₁)
    (q : W₂ ⟶ Q₁) (k : Q₁ ⟶ Pb) (w₁ : N₁ ⟶ X₁) (w₂ : X₁ ⟶ X₂) (w₃ : X₂ ⟶ Q₁)
    (z : X₁ ⟶ R₁) (j : X₂ ⟶ R₂)
    (h₀ : U = u₁ ≫ u₂ ≫ u₃)
    (h₁ : u₃ ≫ t₁ = a₁ ≫ d) (h₂ : d ≫ t₂ = a₂ ≫ p ≫ e₁ ≫ e₂)
    (h₃ : u₂ ≫ a₁ ≫ a₂ = v₁ ≫ v₂ ≫ v₃) (h₄ : u₁ ≫ v₁ = n ≫ s) (h₅ : v₃ ≫ p = q ≫ k)
    (h₆ : s ≫ v₂ ≫ q = w₁ ≫ w₂ ≫ w₃) (h₇ : r₁ = m ≫ n ≫ w₁ ≫ z) (h₈ : z ≫ r₂ = w₂ ≫ j)
    (h₉ : w₃ ≫ k ≫ e₁ ≫ e₂ = j ≫ r₃) :
    m ≫ U ≫ t₁ ≫ t₂ = r₁ ≫ r₂ ≫ r₃ := by
  rw [h₀]
  have hl : m ≫ (u₁ ≫ u₂ ≫ u₃) ≫ t₁ ≫ t₂ = m ≫ n ≫ w₁ ≫ w₂ ≫ j ≫ r₃ := by
    simp only [Category.assoc]
    rw [reassoc_of% h₁, h₂, reassoc_of% h₃, reassoc_of% h₄, reassoc_of% h₅, reassoc_of% h₆, h₉]
  have hr : r₁ ≫ r₂ ≫ r₃ = m ≫ n ≫ w₁ ≫ w₂ ≫ j ≫ r₃ := by
    rw [h₇]
    simp only [Category.assoc]
    rw [reassoc_of% h₈]
  rw [hl, hr]

/-- A functor carries an equation between two three-fold composites to an equation between the
three-fold composites of the images. -/
public theorem map_comp_three {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A₁ A₂ A₃ A₄ B₂ B₃ : D} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄)
    (a' : A₁ ⟶ B₂) (b' : B₂ ⟶ B₃) (c' : B₃ ⟶ A₄) (h : a ≫ b ≫ c = a' ≫ b' ≫ c') :
    F.map a ≫ F.map b ≫ F.map c = F.map a' ≫ F.map b' ≫ F.map c' := by
  simpa only [Functor.map_comp] using F.congr_map h

/-- A morphism presented as `ih ≫ c = a ≫ b ≫ r` with `ih` invertible is, under a functor, the
image of `iv` followed by the images of `a`, `b` and `r`. -/
public theorem map_eq_of_comp {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A B B' E₁ E₂ : D} (ih : A ⟶ B) (iv : B ⟶ A) (hiv : iv ≫ ih = 𝟙 B) (c : B ⟶ B')
    (a : A ⟶ E₁) (b : E₁ ⟶ E₂) (r : E₂ ⟶ B') (h : ih ≫ c = a ≫ b ≫ r) :
    F.map c = F.map iv ≫ F.map a ≫ F.map b ≫ F.map r := by
  have hc : iv ≫ a ≫ b ≫ r = c := by
    rw [← h, ← Category.assoc, hiv, Category.id_comp]
  simpa only [Functor.map_comp] using F.congr_map hc.symm


/-- Replacing the third factor of a three-fold composite. -/
public theorem comp3_congr_third {D : Type*} [Category* D] {A B C' E₁ : D}
    (p : A ⟶ B) (q : B ⟶ C') (r r' : C' ⟶ E₁) (h : r = r') :
    p ≫ q ≫ r = p ≫ q ≫ r' := by rw [h]


/-- Replacing the fourth factor of a four-fold composite. -/
public theorem comp4_congr_fourth {D : Type*} [Category* D] {A B C' E₁ E₂ : D}
    (p : A ⟶ B) (q : B ⟶ C') (r : C' ⟶ E₁) (t t' : E₁ ⟶ E₂) (h : t = t') :
    p ≫ q ≫ r ≫ t = p ≫ q ≫ r ≫ t' := by rw [h]

/-- A functor carries an equation between a four-fold and a two-fold composite to the
corresponding equation between the images. -/
public theorem map_comp4_eq {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A B C' E₁ E₂ A' : D} (a : A ⟶ B) (b : B ⟶ C') (c : C' ⟶ E₁) (t : E₁ ⟶ E₂)
    (a' : A ⟶ A') (b' : A' ⟶ E₂) (h : a ≫ b ≫ c ≫ t = a' ≫ b') :
    F.map a ≫ F.map b ≫ F.map c ≫ F.map t = F.map a' ≫ F.map b' := by
  simpa only [Functor.map_comp] using F.congr_map h

/-- A functor carries a transport along an equality of objects to the transport along the
equality of their images. -/
public theorem map_eqToHom_eq {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A B : D} (h : A = B) (h' : F.obj A = F.obj B) : eqToHom h' = F.map (eqToHom h) := by
  subst h
  simp

end StacksDraft.CompositionChase

namespace AlgebraicGeometry

open Stacks.ModuleSkyscraper

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)

/-- **Stacks 0098's composition compatibility, on complexes.** Degreewise this is
`Stacks.ModuleSkyscraper.pullbackStalkIso_comp_inv_app`, whose last factor is expanded by
`Stacks.ModuleSkyscraper.extendScalarsStalkComp_hom_app` into the composition isomorphism for
extension of scalars and the transport along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`. -/
public theorem pullbackStalkIso_comp_inv_mapHomologicalComplex
    (P : CochainComplex Z.Modules ℤ) :
    (NatIso.mapHomologicalComplex (pullbackStalkIso f x).symm (ComplexShape.up ℤ)).hom.app
          (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.extendScalars (f.stalkMap x).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex (pullbackStalkIso g (f x)).symm
            (ComplexShape.up ℤ)).hom.app P) ≫
        (Functor.mapHomologicalComplexCompIso
            (ModuleCat.extendScalarsComp.{u} (g.stalkMap (f x)).hom (f.stalkMap x).hom).symm
            (ComplexShape.up ℤ)).hom.app
          (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        eqToHom (congrArg (fun ψ => ((ModuleCat.extendScalars.{u} ψ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (stalkMap_hom_comp f g x).symm) =
      ((modulesStalkFunctor X x).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp f g)
            (ComplexShape.up ℤ)).hom.app P) ≫
        (NatIso.mapHomologicalComplex (pullbackStalkIso (f ≫ g) x).symm
          (ComplexShape.up ℤ)).hom.app P := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    Functor.mapHomologicalComplex_map_f, NatIso.mapHomologicalComplex_hom_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  exact Eq.trans (StacksDraft.CompositionChase.comp3_congr_third _ _ _ _
      (extendScalarsStalkComp_hom_app f g x _).symm)
    (pullbackStalkIso_comp_inv_app f g x (P.X i)).symm

section Derived

open CochainComplex.DerivedExtensionScalars
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open StacksDraft.DerivedExtensionScalarsComp

attribute [local instance] hasDerivedCategory_ringedSpaceModules hasDerivedCategory_stalk_comp

variable [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  [HasDerivedCategory.{w} Z.Modules]
  [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
  [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
  [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))]

/-- The three factors of the two-step derived stalk computation of an iterated derived pullback:
the stalk formula for `f` at `x`, the stalk formula for `g` at `f x` with scalars extended along
the germ map of `f`, and the merge of the two extensions of scalars. -/
public theorem derivedPullbackStalkCompIso_hom_app_general
    (K : DerivedCategory Z.Modules) :
    (derivedPullbackStalkCompIsoGeneral f g x).hom.app K =
      (derivedPullbackStalkIso f x).hom.app
          ((derivedPullback g.toLRSHom.toShHom).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map
          ((derivedPullbackStalkIso g (f x)).hom.app K) ≫
        (derivedStalkExtensionCompIsoGeneral f g x).hom.app
          ((derivedStalkFunctor (g (f x))).obj K) :=
  rfl

/-- `pullbackStalkIso_comp_inv_mapHomologicalComplex` in the derived category: localization of the
equation of complexes, with the transport moved across `DerivedCategory.Q`. -/
public theorem pullbackStalkIso_comp_inv_mapDerived (P : CochainComplex Z.Modules ℤ) :
    DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pullbackStalkIso f x).symm (ComplexShape.up ℤ)).hom.app
            (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars (f.stalkMap x).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
            ((NatIso.mapHomologicalComplex (pullbackStalkIso g (f x)).symm
              (ComplexShape.up ℤ)).hom.app P)) ≫
        (extensionScalarsComplexCompIsoGeneral (g.stalkMap (f x)).hom (f.stalkMap x).hom).hom.app
          (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj
            (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P))
          (stalkMap_hom_comp f g x).symm) =
      DerivedCategory.Q.map
          (((modulesStalkFunctor X x).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp f g)
              (ComplexShape.up ℤ)).hom.app P)) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pullbackStalkIso (f ≫ g) x).symm
            (ComplexShape.up ℤ)).hom.app P) := by
  refine Eq.trans (StacksDraft.CompositionChase.comp4_congr_fourth _ _ _ _ _
    (StacksDraft.CompositionChase.map_eqToHom_eq DerivedCategory.Q
      (congrArg (fun ψ => ((ModuleCat.extendScalars.{u} ψ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((modulesStalkFunctor Z (g (f x))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        (stalkMap_hom_comp f g x).symm) _)) ?_
  exact StacksDraft.CompositionChase.map_comp4_eq DerivedCategory.Q _ _ _ _ _ _
    (pullbackStalkIso_comp_inv_mapHomologicalComplex f g x P)

/-- **The hypothesis of `AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat_general`,
discharged.** At every cochain complex of `𝒪_Z`-modules — no K-flatness needed — the two-step
derived stalk computation, read backwards along the composition isomorphism of Tag 0D5S and
composed with the comparison of derived against degreewise extension of scalars along the germ map
of `f ≫ g`, satisfies the equation that characterizes `AlgebraicGeometry.derivedPullbackStalkIso`
for `f ≫ g`. -/
public theorem derivedPullbackStalkCompIso_hcomp (P : CochainComplex Z.Modules ℤ) :
    (derivedStalkFunctor x).map
          ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
            g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
        (derivedPullbackStalkCompIsoGeneral f g x).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
          ((modulesStalkFunctor Z ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
          (((modulesStalkFunctor Z ((f ≫ g) x)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
        (modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (pullbackStalkIso (f ≫ g) x).symm
            (ComplexShape.up ℤ)).hom.app P) := by
  have h₁ := ((derivedStalkExtensionCompIsoGeneral f g x).hom.naturality
    ((modulesStalkFunctor Z ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P)).symm
  have h₂ := derivedStalkExtensionCompIsoGeneral_hom_app_comp_comparison f g x
    (((modulesStalkFunctor Z ((f ≫ g) x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have h₃ := StacksDraft.CompositionChase.map_comp_three
    (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor _ _ _ _ _ _
    (derivedPullbackStalkIso_comp_comparison g (f x) P)
  have h₄ := ((derivedPullbackStalkIso f x).hom.naturality
    (pullbackComparisonOnComplex g P)).symm
  have h₅ := (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).comparison.naturality
    ((NatIso.mapHomologicalComplex (pullbackStalkIso g (f x)).symm
      (ComplexShape.up ℤ)).hom.app P)
  have h₆ := derivedPullbackStalkIso_comp_comparison f x
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hcomp :
      (Stacks.DerivedPullback.Composition.derivedPullbackCompComparisonCanonical
            f.toLRSHom.toShHom g.toLRSHom.toShHom).app (DerivedCategory.Q.obj P) ≫
          pullbackComparisonOnComplex (f ≫ g) P =
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            f.toLRSHom.toShHom).map (pullbackComparisonOnComplex g P) ≫
          pullbackComparisonOnComplex f
              (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso
                (Stacks.DerivedPullback.Composition.modulePullbackComp f.toLRSHom.toShHom
                  g.toLRSHom.toShHom) (ComplexShape.up ℤ)).hom.app P) :=
    Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_comp_general
      f.toLRSHom.toShHom g.toLRSHom.toShHom P
  have h₇ := StacksDraft.CompositionChase.map_eq_of_comp (derivedStalkFunctor x)
    ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom).hom.app
      (DerivedCategory.Q.obj P))
    ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom).inv.app
      (DerivedCategory.Q.obj P))
    ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
      g.toLRSHom.toShHom).inv_hom_id_app (DerivedCategory.Q.obj P))
    _ _ _ _ hcomp
  have h₈ := (modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso (modulePullbackComp f.toLRSHom.toShHom
      g.toLRSHom.toShHom) (ComplexShape.up ℤ)).hom.app P)
  have h₉ := pullbackStalkIso_comp_inv_mapDerived f g x P
  exact StacksDraft.CompositionChase.chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedPullbackStalkCompIso_hom_app_general f g x (DerivedCategory.Q.obj P))
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉

/-- **The coherence of Stacks 0098 with Tag 0D5S, unconditionally.** The two-step derived stalk
computation of an iterated derived pullback, read backwards along the composition isomorphism of
Tag 0D5S, is the one-step computation for `f ≫ g`. -/
public theorem derivedPullbackStalkIso_comp_general :
    (Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x)).inv ≫ (derivedPullbackStalkCompIsoGeneral f g x).hom =
      (derivedPullbackStalkIso (f ≫ g) x).hom :=
  derivedPullbackStalkIso_comp_of_kFlat_general f g x fun P _ =>
    derivedPullbackStalkCompIso_hcomp f g x P

/-- **The coherence as an equality of isomorphisms.** The two-step derived stalk computation *is*
the Tag 0D5S composition isomorphism followed by the one-step computation. This is the form a
consumer who meets a composition isomorphism inside a derived stalk applies. -/
public theorem derivedPullbackStalkCompIso_eq_general :
    derivedPullbackStalkCompIsoGeneral f g x =
      Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x) ≪≫ derivedPullbackStalkIso (f ≫ g) x :=
  derivedPullbackStalkCompIsoGeneral_eq_of_kFlat f g x fun P _ =>
    derivedPullbackStalkCompIso_hcomp f g x P

end Derived

end AlgebraicGeometry

end
