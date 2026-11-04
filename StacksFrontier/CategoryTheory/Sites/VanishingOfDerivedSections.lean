module

public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsOnABigSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# A complex of abelian sheaves with no cohomology over a covering family is zero

Let `(C, J)` be a site and let `K` be an object of the unbounded derived category of abelian
sheaves on it. Suppose the derived sections `RΓ(y, K)` vanish for every `y` in a family of
objects covering every object of the site. Then `K = 0`.

This is the sheaf-theoretic half of the vanishing arguments of **Stacks 0H13** and **Stacks
0H14**: *"because every object of that site admits a covering by objects of this kind, the
cohomology sheaves vanish, hence the complex is zero"*. The hypothesis there is the vanishing of
cohomology **over objects**, i.e. of the right derived functors of sections, whereas
`StacksFrontier/CategoryTheory/Sites/VanishingOnCovering.lean` turns only the vanishing of the
*sections of the cohomology sheaves* into the vanishing of the complex. The step between the two
is what this file supplies.

## How the two are bridged

The passage is *not* through the hypercohomology edge morphism `H^q(y, K) ⟶ Γ(y, H^q(K))`, which
is not an epimorphism in general: its image is the bottom step of the filtration of `H^q(y, K)`
coming from the spectral sequence of Stacks 0BKV, so its vanishing says nothing about
`Γ(y, H^q(K))`. It goes through the projection from cycles instead.

Represent `K` by a K-injective complex `I`, which is possible because the abelian sheaves form a
Grothendieck abelian category (Stacks 079P, through
`Stacks.Cohomology.Localization.enoughKInjectives`). Then `RΓ(y, K)` is the complex of sections
`Γ(y, I)`, because the unit of an unbounded right derived functor is invertible on a K-injective
complex. So the hypothesis says that each complex of abelian groups `Γ(y, I)` is acyclic, i.e.
that over `y` every cycle of `I` is a boundary. Sections over an object are left exact, so they
commute with cycles, and the projection `Z^q(I) ⟶ H^q(I)` therefore becomes the zero morphism on
sections over `y`: it factors through the `q`-th homology of `Γ(y, I)`, which is zero. A
morphism of sheaves whose sections vanish on a covering family is zero, and the projection from
cycles is an epimorphism, so `H^q(I) = 0`.

## Main results

* `CategoryTheory.Sheaf.hom_eq_zero_of_isCoveringFamily`: a morphism of sheaves is zero as soon
  as its sections over the objects of a covering family are zero.
* `CategoryTheory.Sheaf.isZero_of_epi_of_isCoveringFamily`: the target of an epimorphism of
  sheaves is zero as soon as that epimorphism vanishes on sections over a covering family.
* `Stacks.Cohomology.DerivedSectionsVanishing.map_homologyπ_eq_zero`: a left exact additive
  functor annihilates the projection from cycles in the degrees where it kills the homology of
  the image complex.
* `Stacks.Cohomology.DerivedSectionsVanishing.isZero_of_isZero_derivedAbelianSections`: **the
  vanishing criterion** — a complex of abelian sheaves whose derived sections vanish over a
  covering family is zero.

## References

* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 0H13](https://stacks.math.columbia.edu/tag/0H13)
* [Stacks Project, Tag 0H14](https://stacks.math.columbia.edu/tag/0H14)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedLowerShriek

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A]

/-- A morphism of sheaves whose sections over the sources of one covering presieve of `X` vanish
has vanishing sections over `X` itself.

Two morphisms out of the sections over `X` that agree after restriction along every arrow of a
covering presieve are equal, because a sheaf is separated for that presieve; apply this to the
morphism in question and to the zero morphism, whose restrictions agree by naturality. -/
theorem hom_app_eq_zero_of_covering {F G : Sheaf J A} (φ : F ⟶ G) {X : C} (R : Presieve X)
    (hR : Sieve.generate R ∈ J X)
    (h : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, R f → φ.hom.app (op Y) = 0) :
    φ.hom.app (op X) = 0 := by
  have hsep : Presieve.IsSeparatedFor (G.obj ⋙ coyoneda.obj (op (F.obj.obj (op X)))) R := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact (G.property _ _ hR).isSeparatedFor
  refine hsep.ext fun {Y} {f} hf => ?_
  have hnat : F.obj.map f.op ≫ φ.hom.app (op Y) = φ.hom.app (op X) ≫ G.obj.map f.op :=
    φ.hom.naturality f.op
  have hcomp : φ.hom.app (op X) ≫ G.obj.map f.op = 0 := by
    rw [← hnat, h hf, comp_zero]
  simp [Functor.comp_map, hcomp]

/-- A morphism of sheaves whose sections over the objects of a covering family vanish is
zero. -/
theorem hom_eq_zero_of_isCoveringFamily {F G : Sheaf J A} (φ : F ⟶ G) {P : ObjectProperty C}
    (hP : J.IsCoveringFamily P) (h : ∀ Y : C, P Y → φ.hom.app (op Y) = 0) :
    φ = 0 := by
  rw [Sheaf.hom_ext_iff]
  ext X
  obtain ⟨R, hR, hRP⟩ := hP X.unop
  have hX : φ.hom.app (op X.unop) = 0 :=
    hom_app_eq_zero_of_covering φ R hR fun {Y} {_} hf => h Y (hRP hf)
  simpa using hX

/-- The target of an epimorphism of sheaves whose sections over the objects of a covering family
vanish is the zero sheaf. -/
theorem isZero_of_epi_of_isCoveringFamily {F G : Sheaf J A} (φ : F ⟶ G) (hφ : Epi φ)
    {P : ObjectProperty C} (hP : J.IsCoveringFamily P)
    (h : ∀ Y : C, P Y → φ.hom.app (op Y) = 0) :
    IsZero G := by
  have _ := hφ
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_epi φ).1 ?_
  rw [Category.comp_id, comp_zero, hom_eq_zero_of_isCoveringFamily φ hP h]

end CategoryTheory.Sheaf

namespace Stacks.Cohomology.DerivedSectionsVanishing

open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

section Comparison

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- **A left exact additive functor kills the projection from cycles in the degrees where it
kills the homology of the image complex.** If the `q`-th homology of the complex `F K` vanishes,
then `F` carries the projection `Z^q(K) ⟶ H^q(K)` to the zero morphism: that projection, read
through the comparison on cycles — invertible because `F` is left exact — is the projection from
the cycles of `F K` followed by the comparison on homology, and the first factor has a zero
target. -/
theorem map_homologyπ_eq_zero (K : CochainComplex A ℤ) (q : ℤ)
    (h : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology q)) :
    F.map (K.homologyπ q) = 0 := by
  have key : cyclesComparison F K q ≫ F.map (K.homologyπ q) =
      cyclesComparison F K q ≫ 0 := by
    rw [comp_zero, ← homologyπ_comp_homologyComparison F K q,
      h.eq_of_tgt (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q) 0,
      zero_comp]
  exact (cancel_epi (cyclesComparison F K q)).1 key

end Comparison

section Site

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u₁ v₁ w}]
  [IsGrothendieckAbelian.{max u₁ v₁ w} (Sheaf J AddCommGrpCat.{max u₁ v₁ w})]

attribute [local instance] HasDerivedCategory.standard

/-- **The derived sections of a K-injective complex are its sections.** If the derived sections
over `y` of the class of a K-injective complex `I` vanish, then the `q`-th homology of the
complex of sections of `I` over `y` vanishes, in every degree.

The unit of an unbounded right derived functor is invertible at a K-injective complex
(`Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective`), which identifies
`RΓ(y, I)` with the class of the complex `Γ(y, I)`. -/
theorem isZero_homology_sections_of_isZero_derivedAbelianSections (y : C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max u₁ v₁ w}) ℤ) [I.IsKInjective] (q : ℤ)
    (h : IsZero ((BigSite.derivedAbelianSections.{w} J y).obj (DerivedCategory.Q.obj I))) :
    IsZero ((((BigSite.abelianSections.{w} J y).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology q) := by
  have hunit : IsIso ((((BigSite.abelianSections.{w} J y).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u₁ v₁ w})
          (ComplexShape.up ℤ))).app
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max u₁ v₁ w})
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
      (BigSite.abelianSections.{w} J y) I
  have eQ : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max u₁ v₁ w})
        (ComplexShape.up ℤ)).obj I) ≅ DerivedCategory.Q.obj I :=
    (DerivedCategory.quotientCompQhIso (Sheaf J AddCommGrpCat.{max u₁ v₁ w})).app I
  have eSource : DerivedCategory.Q.obj (((BigSite.abelianSections.{w} J y).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) ≅
      DerivedCategory.Qh.obj (((BigSite.abelianSections.{w} J y).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient
          (Sheaf J AddCommGrpCat.{max u₁ v₁ w}) (ComplexShape.up ℤ)).obj I)) :=
    ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{max u₁ v₁ w}).app
        (((BigSite.abelianSections.{w} J y).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)).symm ≪≫
      DerivedCategory.Qh.mapIso
        (((BigSite.abelianSections.{w} J y).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app I).symm
  have hzero : IsZero (DerivedCategory.Q.obj
      (((BigSite.abelianSections.{w} J y).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) :=
    IsZero.of_iso h (eSource ≪≫ @asIso _ _ _ _ _ hunit ≪≫
      (BigSite.derivedAbelianSections.{w} J y).mapIso eQ)
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u₁ v₁ w} q).symm.app
      (((BigSite.abelianSections.{w} J y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  exact (DerivedCategory.isZero_iff_forall_isZero_homology _).1 hzero q

/-- **A complex of abelian sheaves whose derived sections vanish over a covering family is
zero.** This is the step *"since every object has a covering by such objects, the cohomology
sheaves vanish, hence the complex is zero"* of the vanishing arguments of **Stacks 0H13** and
**Stacks 0H14**, for an arbitrary site. -/
theorem isZero_of_isZero_derivedAbelianSections {P : ObjectProperty C}
    (hP : J.IsCoveringFamily P)
    (K : DerivedCategory (Sheaf J AddCommGrpCat.{max u₁ v₁ w}))
    (h : ∀ y : C, P y → IsZero ((BigSite.derivedAbelianSections.{w} J y).obj K)) :
    IsZero K := by
  obtain ⟨I, f, hI, hf⟩ := Stacks.Cohomology.Localization.enoughKInjectives
    (DerivedCategory.Q.objPreimage K)
  have _ := hI
  have _ := hf
  have e : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
  refine IsZero.of_iso ?_ e.symm
  refine (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun q => ?_
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctorFactors (Sheaf J AddCommGrpCat.{max u₁ v₁ w}) q).app I)
  have hepi₀ : Epi ((I.sc q).homologyπ) := inferInstance
  have hepi : Epi (I.homologyπ q) := hepi₀
  refine CategoryTheory.Sheaf.isZero_of_epi_of_isCoveringFamily (I.homologyπ q) hepi hP
    fun y hy => ?_
  refine map_homologyπ_eq_zero (BigSite.abelianSections.{w} J y) I q ?_
  exact isZero_homology_sections_of_isZero_derivedAbelianSections J y I q
    (IsZero.of_iso (h y hy) ((BigSite.derivedAbelianSections.{w} J y).mapIso e))

end Site

end Stacks.Cohomology.DerivedSectionsVanishing

end
