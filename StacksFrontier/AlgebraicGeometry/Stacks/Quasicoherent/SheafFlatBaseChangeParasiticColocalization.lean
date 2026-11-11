module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreQuotientColocalizationOfAdjunction
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedModuleLowerShriekSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedQuasicoherentRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSemiorthogonalDecompositionOfClass
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.CategoryTheory.Triangulated.LeftOrthogonalTriangleUniqueness

/-!
# Splitting off the parasitic part of a complex on an algebraic stack (Stacks 07BA)

Let `𝒳` be an algebraic stack and `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` the morphism of ringed
topoi of **Stacks 0788** (2). **Stacks 07BA**: every object `E` of `D_{LQCoh^fbc}(𝒪_𝒳)` sits in
a canonical distinguished triangle

`E' ⟶ E ⟶ P ⟶ E'[1]`

of `D_{LQCoh^fbc}(𝒪_𝒳)` with `P` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and
`Hom_{D(𝒪_𝒳)}(E', P') = 0` for every `P'` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.

`LQCoh^fbc(𝒪_𝒳)` is the class of **Stacks 0762** with the flat base change property read through
the sheaf pullback on the small étale sites, as in the source:
`AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`.

As in the source, `E' = Lg_! g^* E` and `E' ⟶ E` is the counit of `Lg_! ⊣ g^*`, with `Lg_!` the
derived lower shriek of **Stacks 07AS** (4),
`AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriek`.

That `Lg_! g^* E` lies in `D_{LQCoh^fbc}(𝒪_𝒳)` is **Stacks 07B9** (2)(a), (2)(c), which rests on
**Stacks 07B3** (2) in degree `0`; the latter is proved at the standard models
`HasDerivedCategory.standard` of the two derived categories, so the results using it are stated at
those models (named in their statements), the others for any models.

## Main results

All in the namespace `AlgebraicGeometry.Stack.FlatFppf`.

* `exists_sheafParasiticColocalizationTriangle_unique`: the whole lemma, the triangle together
  with its canonicity.
* `exists_sheafParasiticColocalizationTriangle`: the triangle, with `E'` left orthogonal to
  `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and `P` in it.
* `leftOrthogonal_sheafParasiticFreePart`: the orthogonality.
* `derivedParasitic_obj₃_of_distTriang_sheafParasiticFreePartHom`: every cone on
  `Lg_! g^* E ⟶ E` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`.
* `exists_iso_sheafParasiticColocalizationTriangle`: the canonicity ([Stacks, Tag 0CQP]): any
  distinguished triangle `E'' ⟶ E ⟶ P'' ⟶ E''[1]` with `E''` left orthogonal to
  `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and `P''` in it is isomorphic to the canonical one by an
  isomorphism which is the identity on `E`.
* `hasColocalizations_locallyQuasicoherentSheafFlatBaseChangeFppfModules`: the triangle as the
  colocalization hypothesis `DerivedCategoryB.HasColocalizations` of the Verdier quotient.

## References

* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07B9](https://stacks.math.columbia.edu/tag/07B9)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0CQP](https://stacks.math.columbia.edu/tag/0CQP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w t t'

attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

-- the abelian structure of the library on sheaves of modules whose sections contain the site
-- would be met first by instance search here, with a universe constraint it cannot solve
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

section AnyModels

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t'} (flatFppfModules B S hS 𝒳)]

/-- `E' = Lg_! g^* E`, the first term of the triangle of Stacks 07BA. -/
abbrev sheafParasiticFreePart (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    DerivedCategory (fppfModules B S hS 𝒳) :=
  parasiticFreePart B S hS 𝒳 (derivedModuleLowerShriek B S hS 𝒳) K

/-- The canonical morphism `Lg_! g^* E ⟶ E`, the counit of `Lg_! ⊣ g^*`. -/
abbrev sheafParasiticFreePartHom (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    sheafParasiticFreePart B S hS 𝒳 K ⟶ K :=
  parasiticFreePartHom B S hS 𝒳 (derivedModuleLowerShriek B S hS 𝒳)
    (derivedModuleLowerShriekAdjunction B S hS 𝒳) K

/-- **Stacks 07BA**, the orthogonality: `Hom(Lg_! g^* E, P') = Hom(g^* E, g^* P') = 0` for every
`P'` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
@[stacks 07BA "the orthogonality: Hom_D(𝒪_𝒳)(E', P') = 0 for every P' in \
D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳), at E' = Lg_! g^* E, for the faithful class LQCoh^fbc of Stacks \
0762 (flat base change read with the pullback of sheaves), the actual derived lower shriek Lg_! of \
Stacks 07AS (4) and any models of the derived categories, with no hypothesis"]
theorem leftOrthogonal_sheafParasiticFreePart (K : DerivedCategory (fppfModules B S hS 𝒳)) :
    (ParasiticQuotient.derivedParasitic B S hS 𝒳
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).leftOrthogonal
      (sheafParasiticFreePart B S hS 𝒳 K) :=
  ParasiticQuotient.leftOrthogonal_parasiticFreePart B S hS 𝒳 _
    (derivedModuleLowerShriek B S hS 𝒳) (derivedModuleLowerShriekAdjunction B S hS 𝒳) K

-- Stacks 07B3 (2) in degree 0, for the models at hand; it is proved below at the standard models
variable (h0 : ∀ M : flatFppfModules B S hS 𝒳, M.IsQuasicoherentOnSite →
    DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
      ((derivedModuleLowerShriek B S hS 𝒳).obj
        ((DerivedCategory.singleFunctor (flatFppfModules B S hS 𝒳) 0).obj M)))

include h0 in
/-- **Stacks 07BA**, the cone: for `E` in `D_{LQCoh^fbc}(𝒪_𝒳)`, every cone `P` on the canonical
morphism `Lg_! g^* E ⟶ E` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`: `Lg_! g^* E` lies in
`D_{LQCoh^fbc}(𝒪_𝒳)` by Stacks 07B9 (2)(a), (2)(c), and `g^* P = 0` because `g^* Lg_! = id`. -/
theorem derivedParasitic_obj₃_of_distTriang_sheafParasiticFreePartHom_of_single
    (K : DerivedCategory (fppfModules B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K)
    (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
    (c : P ⟶ (sheafParasiticFreePart B S hS 𝒳 K)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ∈
      distTriang (DerivedCategory (fppfModules B S hS 𝒳))) :
    ParasiticQuotient.derivedParasitic B S hS 𝒳
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P :=
  ParasiticQuotient.derivedParasitic_obj₃_of_distTriang B S hS 𝒳 _
    (derivedModuleLowerShriek B S hS 𝒳) (derivedModuleLowerShriekAdjunction B S hS 𝒳)
    (isIso_derivedModuleLowerShriekAdjunction_unit B S hS 𝒳) K hK
    (derivedSheafFlatBaseChange_parasiticFreePart_of_single B E h S hS 𝒳 h0 K hK) P b c hT

include h0 in
/-- **Stacks 07BA**: every `E` in `D_{LQCoh^fbc}(𝒪_𝒳)` sits in a distinguished triangle
`E' ⟶ E ⟶ P ⟶ E'[1]` of `D_{LQCoh^fbc}(𝒪_𝒳)`, `E' ⟶ E` the canonical morphism
`Lg_! g^* E ⟶ E`, with `P` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and `E'` left orthogonal to
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
theorem exists_sheafParasiticColocalizationTriangle_of_single
    (K : DerivedCategory (fppfModules B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K) :
    ∃ (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
      (c : P ⟶ (sheafParasiticFreePart B S hS 𝒳 K)⟦(1 : ℤ)⟧),
      Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ∈
          distTriang (DerivedCategory (fppfModules B S hS 𝒳)) ∧
        DerivedCategoryB.derivedCategoryB
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
          (sheafParasiticFreePart B S hS 𝒳 K) ∧
        DerivedCategoryB.derivedCategoryB
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P ∧
        ParasiticQuotient.derivedParasitic B S hS 𝒳
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P ∧
        (ParasiticQuotient.derivedParasitic B S hS 𝒳
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).leftOrthogonal
          (sheafParasiticFreePart B S hS 𝒳 K) := by
  obtain ⟨P, b, c, hT⟩ := distinguished_cocone_triangle (sheafParasiticFreePartHom B S hS 𝒳 K)
  have hP := derivedParasitic_obj₃_of_distTriang_sheafParasiticFreePartHom_of_single B E h S hS 𝒳
    h0 K hK P b c hT
  exact ⟨P, b, c, hT, derivedSheafFlatBaseChange_parasiticFreePart_of_single B E h S hS 𝒳 h0 K hK,
    DerivedCategory.KernelColocalization.derivedInter_le _ _ P hP, hP,
    leftOrthogonal_sheafParasiticFreePart B E h S hS 𝒳 K⟩

include h0 in
/-- **Stacks 07BA**, in the form of the colocalization hypothesis of the Verdier quotient
`D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` (`D_QCoh(𝒪_𝒳)` of **Stacks 07B6**): every
object of `D_{LQCoh^fbc}(𝒪_𝒳)` receives a morphism with cone in
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, namely `Lg_! g^* E ⟶ E`, out of an object left orthogonal to
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
theorem hasColocalizations_locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_single :
    DerivedCategoryB.HasColocalizations
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
      (ParasiticQuotient.parasitic B S hS 𝒳 ⊓
        lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) :=
  DerivedCategoryB.hasColocalizations_of_adjunction _ _
    (derivedModuleLowerShriekAdjunction B S hS 𝒳)
    (ParasiticQuotient.isZero_derivedModuleRestriction_iff B S hS 𝒳)
    (isIso_derivedModuleLowerShriekAdjunction_unit B S hS 𝒳)
    (derivedSheafFlatBaseChange_parasiticFreePart_of_single B E h S hS 𝒳 h0)

/-- **Stacks 07BA, canonicity** ([Stacks, Tag 0CQP]): a distinguished triangle
`E'' ⟶ E ⟶ P'' ⟶ E''[1]` with `E''` left orthogonal to `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and
`P''` in it is isomorphic to any distinguished triangle on the canonical morphism
`Lg_! g^* E ⟶ E` whose third term lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`, by an isomorphism of
triangles which is the identity on `E`. -/
@[stacks 07BA "the canonicity of the triangle: a distinguished triangle E'' ⟶ E ⟶ P'' ⟶ E''[1] \
with E'' left orthogonal to D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) and P'' in it is isomorphic to the \
triangle on Lg_! g^* E ⟶ E by an isomorphism which is the identity on E (Stacks 0CQP), for the \
faithful class LQCoh^fbc, any models of the derived categories, with no hypothesis"]
theorem exists_iso_sheafParasiticColocalizationTriangle
    (K : DerivedCategory (fppfModules B S hS 𝒳))
    (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
    (c : P ⟶ (sheafParasiticFreePart B S hS 𝒳 K)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ∈
      distTriang (DerivedCategory (fppfModules B S hS 𝒳)))
    (hP : ParasiticQuotient.derivedParasitic B S hS 𝒳
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P)
    {E'' P'' : DerivedCategory (fppfModules B S hS 𝒳)} (f'' : E'' ⟶ K) (g'' : K ⟶ P'')
    (h'' : P'' ⟶ E''⟦(1 : ℤ)⟧)
    (hT'' : Triangle.mk f'' g'' h'' ∈ distTriang (DerivedCategory (fppfModules B S hS 𝒳)))
    (hE'' : (ParasiticQuotient.derivedParasitic B S hS 𝒳
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).leftOrthogonal E'')
    (hP'' : ParasiticQuotient.derivedParasitic B S hS 𝒳
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P'') :
    ∃ e : Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ≅ Triangle.mk f'' g'' h'',
      e.hom.hom₂ = 𝟙 K :=
  exists_iso_of_leftOrthogonal _ _ _ _ _ _ _ hT hT''
    (leftOrthogonal_sheafParasiticFreePart B E h S hS 𝒳 K) hE'' hP hP''

end AnyModels

/-! ### At the standard models

`Lg_!` lies in `D_{LQCoh^fbc}(𝒪_𝒳)` on quasi-coherent modules in degree `0` (**Stacks 07B3** (2),
`locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek`), which is proved at
the standard models `HasDerivedCategory.standard` of the two derived categories; they are named
in the statements below. -/

section StandardModels

/-- **Stacks 07BA**, the cone: for `E` in `D_{LQCoh^fbc}(𝒪_𝒳)`, every cone `P` on the canonical
morphism `Lg_! g^* E ⟶ E` lies in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
@[stacks 07BA "the cone: for E' = Lg_! g^* E and E' ⟶ E the counit of Lg_! ⊣ g^*, every \
distinguished triangle E' ⟶ E ⟶ P ⟶ E'[1] with E in D_LQCoh^fbc(𝒪_𝒳) has P in \
D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳), for the faithful class LQCoh^fbc of Stacks 0762 and the actual \
derived lower shriek of Stacks 07AS (4) at the standard models of the derived categories, with no \
hypothesis (Stacks 07B9 (2)(a), (2)(c) and 07B3 (2) are proved, not assumed)"]
theorem derivedParasitic_obj₃_of_distTriang_sheafParasiticFreePartHom :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    ∀ (K : DerivedCategory (fppfModules B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K →
      ∀ (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
        (c : P ⟶ (sheafParasiticFreePart B S hS 𝒳 K)⟦(1 : ℤ)⟧),
        Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ∈
          distTriang (DerivedCategory (fppfModules B S hS 𝒳)) →
        ParasiticQuotient.derivedParasitic B S hS 𝒳
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P := by
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  exact derivedParasitic_obj₃_of_distTriang_sheafParasiticFreePartHom_of_single B E h S hS 𝒳
    (locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳)

/-- **Stacks 07BA**: every `E` in `D_{LQCoh^fbc}(𝒪_𝒳)` sits in a distinguished triangle
`E' ⟶ E ⟶ P ⟶ E'[1]` of `D_{LQCoh^fbc}(𝒪_𝒳)`, `E' ⟶ E` the canonical morphism
`Lg_! g^* E ⟶ E`, with `P` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and `E'` left orthogonal to
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`. -/
@[stacks 07BA "the existence of the triangle: every E in D_LQCoh^fbc(𝒪_𝒳) sits in a \
distinguished triangle E' ⟶ E ⟶ P ⟶ E'[1] with E' = Lg_! g^* E and E' ⟶ E the counit, E' and P \
in D_LQCoh^fbc(𝒪_𝒳), P in D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) and Hom(E', P') = 0 for every P' in \
D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳), for the faithful class LQCoh^fbc of Stacks 0762 and the actual \
derived lower shriek of Stacks 07AS (4) at the standard models of the derived categories, with no \
hypothesis"]
theorem exists_sheafParasiticColocalizationTriangle :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    ∀ (K : DerivedCategory (fppfModules B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K →
      ∃ (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
        (c : P ⟶ (sheafParasiticFreePart B S hS 𝒳 K)⟦(1 : ℤ)⟧),
        Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ∈
            distTriang (DerivedCategory (fppfModules B S hS 𝒳)) ∧
          DerivedCategoryB.derivedCategoryB
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
            (sheafParasiticFreePart B S hS 𝒳 K) ∧
          DerivedCategoryB.derivedCategoryB
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P ∧
          ParasiticQuotient.derivedParasitic B S hS 𝒳
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P ∧
          (ParasiticQuotient.derivedParasitic B S hS 𝒳
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).leftOrthogonal
            (sheafParasiticFreePart B S hS 𝒳 K) := by
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  exact exists_sheafParasiticColocalizationTriangle_of_single B E h S hS 𝒳
    (locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳)

/-- **Stacks 07BA**: every `E` in `D_{LQCoh^fbc}(𝒪_𝒳)` sits in a canonical distinguished triangle
`E' ⟶ E ⟶ P ⟶ E'[1]` of `D_{LQCoh^fbc}(𝒪_𝒳)`, `E' ⟶ E` the canonical morphism
`Lg_! g^* E ⟶ E`, with `P` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` and
`Hom_{D(𝒪_𝒳)}(E', P') = 0` for every `P'` in `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`; canonical in the
sense of the source: every distinguished triangle `E'' ⟶ E ⟶ P'' ⟶ E''[1]` with these two
properties is isomorphic to it by an isomorphism of triangles which is the identity on `E`
([Stacks, Tag 0CQP]). -/
@[stacks 07BA "the whole lemma: every E in D_LQCoh^fbc(𝒪_𝒳) sits in a distinguished triangle \
E' ⟶ E ⟶ P ⟶ E'[1] of D_LQCoh^fbc(𝒪_𝒳), E' = Lg_! g^* E and E' ⟶ E the counit, with P in \
D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) and Hom(E', P') = 0 for every P' in it, canonical: any other such \
triangle is isomorphic to it by an isomorphism which is the identity on E (Stacks 0CQP); for the \
faithful class LQCoh^fbc of Stacks 0762 and the derived lower shriek of Stacks 07AS (4), at the \
standard models of the derived categories"]
theorem exists_sheafParasiticColocalizationTriangle_unique :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    letI := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
    ∀ (K : DerivedCategory (fppfModules B S hS 𝒳)),
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) K →
      ∃ (P : DerivedCategory (fppfModules B S hS 𝒳)) (b : K ⟶ P)
        (c : P ⟶ (sheafParasiticFreePart B S hS 𝒳 K)⟦(1 : ℤ)⟧),
        Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ∈
            distTriang (DerivedCategory (fppfModules B S hS 𝒳)) ∧
          DerivedCategoryB.derivedCategoryB
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
            (sheafParasiticFreePart B S hS 𝒳 K) ∧
          DerivedCategoryB.derivedCategoryB
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P ∧
          ParasiticQuotient.derivedParasitic B S hS 𝒳
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P ∧
          (ParasiticQuotient.derivedParasitic B S hS 𝒳
            (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).leftOrthogonal
            (sheafParasiticFreePart B S hS 𝒳 K) ∧
          ∀ {E'' P'' : DerivedCategory (fppfModules B S hS 𝒳)} (f'' : E'' ⟶ K) (g'' : K ⟶ P'')
            (h'' : P'' ⟶ E''⟦(1 : ℤ)⟧),
            Triangle.mk f'' g'' h'' ∈ distTriang (DerivedCategory (fppfModules B S hS 𝒳)) →
            (ParasiticQuotient.derivedParasitic B S hS 𝒳
              (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).leftOrthogonal E'' →
            ParasiticQuotient.derivedParasitic B S hS 𝒳
              (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) P'' →
            ∃ e : Triangle.mk (sheafParasiticFreePartHom B S hS 𝒳 K) b c ≅
                Triangle.mk f'' g'' h'', e.hom.hom₂ = 𝟙 K := by
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  intro K hK
  obtain ⟨P, b, c, hT, hE', hPB, hP, hO⟩ :=
    exists_sheafParasiticColocalizationTriangle B E h S hS 𝒳 K hK
  exact ⟨P, b, c, hT, hE', hPB, hP, hO, fun f'' g'' h'' hT'' hE'' hP'' =>
    exists_iso_sheafParasiticColocalizationTriangle B E h S hS 𝒳 K P b c hT hP f'' g'' h''
      hT'' hE'' hP''⟩

/-- **Stacks 07BA**, in the form of the colocalization hypothesis of the Verdier quotient
`D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` (`D_QCoh(𝒪_𝒳)` of **Stacks 07B6**). -/
@[stacks 07BA "the triangle as the colocalization of D_LQCoh^fbc(𝒪_𝒳) by \
D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳): every object receives Lg_! g^* E ⟶ E, a morphism with cone in \
D_(Parasitic ∩ LQCoh^fbc)(𝒪_𝒳) out of an object left orthogonal to it, for the faithful class \
LQCoh^fbc and the actual Lg_! at the standard models of the derived categories, with no \
hypothesis"]
theorem hasColocalizations_locallyQuasicoherentSheafFlatBaseChangeFppfModules :
    letI := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
    DerivedCategoryB.HasColocalizations
      (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
      (ParasiticQuotient.parasitic B S hS 𝒳 ⊓
        lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) := by
  let := HasDerivedCategory.standard (fppfModules B S hS 𝒳)
  let := HasDerivedCategory.standard (flatFppfModules B S hS 𝒳)
  exact hasColocalizations_locallyQuasicoherentSheafFlatBaseChangeFppfModules_of_single
    B E h S hS 𝒳
    (locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳)

end StandardModels

end AlgebraicGeometry.Stack.FlatFppf

end
