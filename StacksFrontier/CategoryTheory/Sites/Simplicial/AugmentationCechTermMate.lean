module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechTermAdjunction
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationConeLawAb

/-!
# The mate of a cosimplicial transition is a structure map of the resolution

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
The degree-`k` term `F ↦ a_{k,*}F_k` of the complex of Stacks 0D79 is a right adjoint, and its
left adjoint `𝒢 ↦ g_{k!}(a_k^{-1}𝒢)` is the degree-`k` term of the resolution of Stacks 0D78:
that is `CategoryTheory.SimplicialSiteSituation.Augmentation.cechTermAdjunction`. This file
proves the comparison of the two complexes' *structure*: the conjugate, along those adjunctions,
of the cosimplicial transition of Stacks 0D79 at `φ : ⦋m⦌ ⟶ ⦋n⦌` is the simplicial structure map
of the resolution at `φ`, read through the identifications of its terms.

That is what makes `Hom(-, F)` applied to the resolution of Stacks 0D78 a complex isomorphic to
the complex of Stacks 0D79 tested against `𝒢`, and hence what the exactness of the latter above
degree `0` rests on.

The proof is the transposition the source performs, made explicit. By
`Stacks.CategoryTheory.homEquiv_conjugate` the identity is equivalent to one equation of
transposes, which splits along `cechTermAdjunction`'s two halves: the half for
`g_{n!} ⊣ g_n^{-1}` is the description of the resolution's structure maps through the direct-sum
formula of Stacks 09WG, which
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolutionFace.lean` supplies, and the
half for `a_n^{-1} ⊣ a_{n,*}` is the cone law of Stacks 0D70 on abelian sheaves, which
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationConeLawAb.lean` supplies. What is left
between them is `fiberTransitionAb_resolution_square`, and that is a chain of four naturalities.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.degIso`: the degree-`k` identification of
  the resolution of Stacks 0D78, with its source spelled as the degree-`k` term of the
  simplex-coefficient resolution.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentLowerShriekMap_comp_degIso_hom`:
  the comparison of Stacks 09WG followed by that identification is the lower shriek image of the
  restriction comparison of Stacks 0D70, compatibility (b).
* `CategoryTheory.SimplicialSiteSituation.Augmentation.fiberTransitionAb_resolution_square`: the
  abelian square the mate identity reduces to.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechTermAdjunction_homEquiv_apply`: the
  transposition along `cechTermAdjunction`, unfolded into its two halves and the Stacks 04DB
  correction.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.homEquiv_degIso_inv_comp_barSimplicial_map`: the transpose along `g_{n!} ⊣ g_n^{-1}` of the
  resolution's structure map at `φ`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.conjugateEquiv_abelianCosimplicialPushforward_map_app`: **the mate identity.**

## Implementation notes

`degIso` exists for a spelling reason, not a mathematical one. The source of
`Resolution.degreeIso` is `(resolution …).simplicial _⦋k⦌` while every comparison lemma of
Stacks 09WG is stated at `(barSimplicial …).obj (Opposite.op ⦋k⦌)`; the two are definitionally
equal, but a composite anchored at one of them does not admit a rewrite whose replacement is
anchored at the other, because the motive is rejected at `implicit` transparency. Naming the
isomorphism at the second spelling anchors every composite below consistently.

For the same reason the hom-set bijections below are applied with their object arguments written
out rather than left to unification: `componentInverseImageAb` and the inverse image of
Stacks 04JC it unfolds to are two spellings of one functor, and unification picks whichever it
reaches first, after which a rewrite stated in the other spelling does not fire.

## References

* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K) (G : Sheaf K Ab.{u})

/-- The degree-`k` identification of the resolution of Stacks 0D78, with its source spelled as
the degree-`k` term of the simplex-coefficient resolution. -/
def degIso (k : ℕ) :
    (barSimplicial S ((totalInverseImageAb S D K a).obj G)).obj (Opposite.op ⦋k⦌) ≅
      resolutionTerm S D K a G k :=
  (resolution S D K a G).degreeIso k

/-- The degree-`k` identification of the resolution of Stacks 0D78, with its source spelled as
the degree-`k` term of the simplex-coefficient resolution. -/
def degIso' (k : ℕ) :
    ((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G)).obj (Opposite.op ⦋k⦌) ≅
      resolutionTerm S D K a G k :=
  (resolution S D K a G).degreeIso k

/-- `degIso` is the degree-`k` identification `degreeIso` of the resolution. -/
theorem degIso_eq (k : ℕ) : degIso S D K a G k = (resolution S D K a G).degreeIso k := rfl

/-- `degIso'` is the degree-`k` identification `degreeIso` of the resolution. -/
theorem degIso_eq' (k : ℕ) : degIso' S D K a G k = (resolution S D K a G).degreeIso k := rfl

/-- The degree-`k` identification unfolded: the lower shriek image of the restriction comparison
of Stacks 0D70, compatibility (b), followed by the comparison of Stacks 09WG. -/
theorem degIso_inv (k : ℕ) :
    (degIso S D K a G k).inv =
      (componentLowerShriekAb S ⦋k⦌).map
          (componentRestrictionAbInverseImageIso S D K a G ⦋k⦌).inv ≫
        componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G) ⦋k⦌ :=
  rfl

/-- The degree-`k` identification unfolded: the lower shriek image of the restriction comparison
of Stacks 0D70, compatibility (b), followed by the comparison of Stacks 09WG. -/
theorem degIso_inv' (k : ℕ) :
    (degIso' S D K a G k).inv =
      (componentLowerShriekAb S ⦋k⦌).map
          (componentRestrictionAbInverseImageIso' S D K a G ⦋k⦌).inv ≫
        (componentLowerShriekMap' S ⦋k⦌).app ((totalInverseImageAb S D K a).obj G) :=
  rfl

/-- The comparison of Stacks 09WG in degree `m`, followed by the degree-`m` identification of the
resolution of Stacks 0D78, is the lower shriek image of the restriction comparison of
Stacks 0D70, compatibility (b). -/
theorem componentLowerShriekMap_comp_degIso_hom (m : ℕ) :
    componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G) ⦋m⦌ ≫
        (degIso S D K a G m).hom =
      (componentLowerShriekAb S ⦋m⦌).map
        (componentRestrictionAbInverseImageIso S D K a G ⦋m⦌).hom := by
  let := isIso_componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G)
    (isCartesianAbSheaf_totalInverseImageAb S D K a G) ⦋m⦌
  show componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G) ⦋m⦌ ≫
      CategoryTheory.inv (componentLowerShriekMap S
        ((totalInverseImageAb S D K a).obj G) ⦋m⦌) ≫
      (componentLowerShriekAb S ⦋m⦌).map
        (componentRestrictionAbInverseImageIso S D K a G ⦋m⦌).hom = _
  rw [IsIso.hom_inv_id_assoc]

/-- The comparison of Stacks 09WG in degree `m`, followed by the degree-`m` identification of the
resolution of Stacks 0D78, is the lower shriek image of the restriction comparison of
Stacks 0D70, compatibility (b). -/
theorem componentLowerShriekMap_comp_degIso_hom' (m : ℕ) :
    (componentLowerShriekMap' S ⦋m⦌).app ((totalInverseImageAb S D K a).obj G) ≫
        (degIso' S D K a G m).hom =
      (componentLowerShriekAb S ⦋m⦌).map
        (componentRestrictionAbInverseImageIso' S D K a G ⦋m⦌).hom := by
  exact componentLowerShriekMap_comp_degIso_hom S D K a G m

/-- The degree-`n` restriction of `componentLowerShriekMap_comp_degreeIso_hom`, stated as one
composite so that the cancellation happens at the objects the consumer's statement spells out. -/
theorem abelianComponent_map_componentLowerShriekMap_comp_degIso_hom (m : ℕ)
    (k : SimplexCategory) :
    (S.abelianComponent k).map
          (componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G) ⦋m⦌) ≫
        (S.abelianComponent k).map (degIso S D K a G m).hom =
      (S.abelianComponent k).map ((componentLowerShriekAb S ⦋m⦌).map
        (componentRestrictionAbInverseImageIso S D K a G ⦋m⦌).hom) :=
  ((S.abelianComponent k).map_comp _ _).symm.trans
    (congrArg (S.abelianComponent k).map
      (componentLowerShriekMap_comp_degIso_hom S D K a G m))

/-- The degree-`n` restriction of `componentLowerShriekMap_comp_degreeIso_hom`, stated as one
composite so that the cancellation happens at the objects the consumer's statement spells out. -/
theorem restrictAb_map_componentLowerShriekMap_comp_degIso_hom (m : ℕ)
    (k : SimplexCategory) :
    (S.restrictAb k).map
          ((componentLowerShriekMap' S ⦋m⦌).app ((totalInverseImageAb S D K a).obj G)) ≫
        (S.restrictAb k).map (degIso' S D K a G m).hom =
      (S.restrictAb k).map ((componentLowerShriekAb S ⦋m⦌).map
        (componentRestrictionAbInverseImageIso' S D K a G ⦋m⦌).hom) := by
  exact abelianComponent_map_componentLowerShriekMap_comp_degIso_hom S D K a G m k

/-- **The abelian square the mate identity reduces to.** -/
theorem fiberTransitionAb_resolution_square {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (S.transitionInverseImageAb φ).map
          ((componentRestrictionAbInverseImageIso S D K a G ⦋m⦌).hom ≫
            (S.componentLowerShriekAbAdjunction ⦋m⦌).unit.app
              ((componentInverseImageAb S D K a ⦋m⦌).obj G)) ≫
        (S.fiberTransitionAb φ).app (resolutionTerm S D K a G m) =
      (S.fiberTransitionAb φ).app ((totalInverseImageAb S D K a).obj G) ≫
        componentSheafSummand S ((totalInverseImageAb S D K a).obj G) φ ≫
        (S.abelianComponent ⦋n⦌).map (degIso S D K a G m).hom := by
  have hu := (S.componentLowerShriekAbAdjunction ⦋m⦌).unit.naturality
    (componentRestrictionAbInverseImageIso S D K a G ⦋m⦌).hom
  have hnat := (S.fiberTransitionAb φ).naturality
    ((componentLowerShriekAb S ⦋m⦌).map
      (componentRestrictionAbInverseImageIso S D K a G ⦋m⦌).hom)
  rw [← Category.assoc, ←
    componentSumFormulaLeg_comp_abelianComponent_map_componentLowerShriekMap,
    Category.assoc, abelianComponent_map_componentLowerShriekMap_comp_degIso_hom]
  simp only [CategoryTheory.Functor.id_map, Functor.comp_map] at hu
  simp only [Functor.comp_map] at hnat
  rw [hu, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hnat, ← Category.assoc, ← componentSumFormulaLeg_app]

/-- **The abelian square the mate identity reduces to.** -/
theorem fiberTransitionAb_resolution_square' {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (S.transitionInverseImageAb φ).map
          ((componentRestrictionAbInverseImageIso' S D K a G ⦋m⦌).hom ≫
            (S.componentLowerShriekAbAdjunction' ⦋m⦌).unit.app
              ((componentInverseImageAb S D K a ⦋m⦌).obj G)) ≫
        (S.fiberTransitionAb' φ).app (resolutionTerm S D K a G m) =
      (S.fiberTransitionAb' φ).app ((totalInverseImageAb S D K a).obj G) ≫
        componentSheafSummand' S ((totalInverseImageAb S D K a).obj G) φ ≫
        (S.restrictAb ⦋n⦌).map (degIso' S D K a G m).hom := by
  exact fiberTransitionAb_resolution_square S D K a G φ

variable [HasSheafify K Ab.{u}]

/-- The transposition along `cechTermAdjunction`, unfolded: transpose along `g_{k!} ⊣ g_k^{-1}`,
then along `a_k⁻¹ ⊣ a_{k,*}`, then correct by the comparison of Stacks 04DB. -/
theorem cechTermAdjunction_homEquiv_apply (k : SimplexCategory)
    (Y : Sheaf S.totalTopology Ab.{u}) (ξ : (cechTermLowerShriek S D K a k).obj G ⟶ Y) :
    (cechTermAdjunction S D K a k).homEquiv G Y ξ =
      (abelianInverseImageAdjPushforward (S.componentTopology k)
            (componentAugmentation S D K a k)).homEquiv G _
          ((S.componentLowerShriekAbAdjunction k).homEquiv
            ((componentInverseImageAb S D K a k).obj G) Y ξ) ≫
        (abelianComponentPushforwardIso S D K a k).inv.app Y := by
  refine Eq.trans (Adjunction.homEquiv_ofNatIsoRight_apply
    ((componentInverseImageAbAdjunction S D K a k).comp
      (S.componentLowerShriekAbAdjunction k))
    (abelianComponentPushforwardIso S D K a k).symm ξ) ?_
  rw [Adjunction.comp_homEquiv]
  rfl

/-- The transposition along `cechTermAdjunction`, unfolded: transpose along `g_{k!} ⊣ g_k^{-1}`,
then along `a_k⁻¹ ⊣ a_{k,*}`, then correct by the comparison of Stacks 04DB. -/
theorem cechTermAdjunction_homEquiv_apply' (k : SimplexCategory)
    (Y : Sheaf S.totalTopology Ab.{u}) (ξ : (cechTermLowerShriek S D K a k).obj G ⟶ Y) :
    (cechTermAdjunction S D K a k).homEquiv G Y ξ =
      (abelianInverseImageAdjPushforward (S.componentTopology k)
            (componentAugmentation S D K a k)).homEquiv G _
          ((S.componentLowerShriekAbAdjunction' k).homEquiv
            ((componentInverseImageAb S D K a k).obj G) Y ξ) ≫
        (abelianComponentPushforwardIso S D K a k).inv.app Y := by
  exact cechTermAdjunction_homEquiv_apply S D K a G k Y ξ

omit [HasSheafify K Ab.{u}] in
/-- The transpose along `g_{n!} ⊣ g_n^{-1}` of the degree-`φ` structure map of the resolution of
Stacks 0D78, read through the identifications of its terms: the restriction comparison of
Stacks 0D70, compatibility (b), followed by the `φ`-labelled summand of Stacks 09WG and the
degree-`m` identification. -/
theorem homEquiv_degIso_inv_comp_barSimplicial_map {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (S.componentLowerShriekAbAdjunction ⦋n⦌).homEquiv
        ((componentInverseImageAb S D K a ⦋n⦌).obj G) (resolutionTerm S D K a G m)
        ((degIso S D K a G n).inv ≫
          (barSimplicial S ((totalInverseImageAb S D K a).obj G)).map φ.op ≫
            (degIso S D K a G m).hom) =
      (componentRestrictionAbInverseImageIso S D K a G ⦋n⦌).inv ≫
        componentSheafSummand S ((totalInverseImageAb S D K a).obj G) φ ≫
          (S.abelianComponent ⦋n⦌).map (degIso S D K a G m).hom := by
  rw [degIso_inv, Category.assoc, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right,
    show (S.componentLowerShriekAbAdjunction ⦋n⦌).homEquiv
        ((S.abelianComponent ⦋n⦌).obj ((totalInverseImageAb S D K a).obj G))
        ((barSimplicial S ((totalInverseImageAb S D K a).obj G)).obj (Opposite.op ⦋n⦌))
        (componentLowerShriekMap S ((totalInverseImageAb S D K a).obj G) ⦋n⦌) =
      componentSheafInclusion S ((totalInverseImageAb S D K a).obj G) ⦋n⦌ from
      ((S.componentLowerShriekAbAdjunction ⦋n⦌).homEquiv _ _).apply_symm_apply _,
    CategoryTheory.Functor.map_comp,
    ← Category.assoc (componentSheafInclusion S ((totalInverseImageAb S D K a).obj G) ⦋n⦌),
    componentSheafInclusion_comp_barSimplicial_map]

omit [HasSheafify K Ab.{u}] in
/-- The transpose along `g_{n!} ⊣ g_n^{-1}` of the degree-`φ` structure map of the resolution of
Stacks 0D78, read through the identifications of its terms: the restriction comparison of
Stacks 0D70, compatibility (b), followed by the `φ`-labelled summand of Stacks 09WG and the
degree-`m` identification. -/
theorem homEquiv_degIso_inv_comp_barSimplicial_map' {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (S.componentLowerShriekAbAdjunction' ⦋n⦌).homEquiv
        ((componentInverseImageAb S D K a ⦋n⦌).obj G) (resolutionTerm S D K a G m)
        ((degIso' S D K a G n).inv ≫
          ((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G)).map φ.op ≫
            (degIso' S D K a G m).hom) =
      (componentRestrictionAbInverseImageIso' S D K a G ⦋n⦌).inv ≫
        componentSheafSummand' S ((totalInverseImageAb S D K a).obj G) φ ≫
          (S.restrictAb ⦋n⦌).map (degIso' S D K a G m).hom := by
  exact homEquiv_degIso_inv_comp_barSimplicial_map S D K a G φ

/-- **The mate of a cosimplicial transition of the complex of Stacks 0D79 is the corresponding
structure map of the resolution of Stacks 0D78.** The degree-`k` term of the complex is a right
adjoint whose left adjoint is the degree-`k` term of the resolution (`cechTermAdjunction`); this
says that the conjugate, along those adjunctions, of the cosimplicial transition at
`φ : ⦋m⦌ ⟶ ⦋n⦌` is the structure map of the resolution at `φ`, read through the identifications
of its terms. -/
theorem conjugateEquiv_abelianCosimplicialPushforward_map_app {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((conjugateEquiv (cechTermAdjunction S D K a ⦋m⦌)
          (cechTermAdjunction S D K a ⦋n⦌)).symm
        ((abelianCosimplicialPushforward S D K a).map φ :
          abelianComponentPushforward S D K a ⦋m⦌ ⟶
            abelianComponentPushforward S D K a ⦋n⦌)).app G =
      (degIso S D K a G n).inv ≫
        (barSimplicial S ((totalInverseImageAb S D K a).obj G)).map φ.op ≫
          (degIso S D K a G m).hom := by
  have hc := Stacks.CategoryTheory.homEquiv_conjugate (cechTermAdjunction S D K a ⦋m⦌)
    (cechTermAdjunction S D K a ⦋n⦌)
    ((abelianCosimplicialPushforward S D K a).map φ :
      abelianComponentPushforward S D K a ⦋m⦌ ⟶ abelianComponentPushforward S D K a ⦋n⦌)
    (X := G) (𝟙 (resolutionTerm S D K a G m))
  have hc' : (cechTermAdjunction S D K a ⦋n⦌).homEquiv G (resolutionTerm S D K a G m)
        (((conjugateEquiv (cechTermAdjunction S D K a ⦋m⦌)
              (cechTermAdjunction S D K a ⦋n⦌)).symm
            ((abelianCosimplicialPushforward S D K a).map φ :
              abelianComponentPushforward S D K a ⦋m⦌ ⟶
                abelianComponentPushforward S D K a ⦋n⦌)).app G) =
      (cechTermAdjunction S D K a ⦋m⦌).homEquiv G (resolutionTerm S D K a G m)
          (𝟙 (resolutionTerm S D K a G m)) ≫
        ((abelianCosimplicialPushforward S D K a).map φ).app (resolutionTerm S D K a G m) :=
    (congrArg ((cechTermAdjunction S D K a ⦋n⦌).homEquiv G (resolutionTerm S D K a G m))
      (Category.comp_id _).symm).trans hc
  have hid : (S.componentLowerShriekAbAdjunction ⦋m⦌).homEquiv
        ((componentInverseImageAb S D K a ⦋m⦌).obj G) (resolutionTerm S D K a G m)
        (𝟙 (resolutionTerm S D K a G m)) =
      (S.componentLowerShriekAbAdjunction ⦋m⦌).unit.app
        ((componentInverseImageAb S D K a ⦋m⦌).obj G) :=
    Adjunction.homEquiv_id _ _
  refine ((cechTermAdjunction S D K a ⦋n⦌).homEquiv G
    (resolutionTerm S D K a G m)).injective (hc'.trans ?_)
  rw [cechTermAdjunction_homEquiv_apply, cechTermAdjunction_homEquiv_apply, hid,
    homEquiv_degIso_inv_comp_barSimplicial_map,
    ← Iso.inv_hom_id_assoc (componentRestrictionAbInverseImageIso S D K a G ⦋m⦌)
      ((S.componentLowerShriekAbAdjunction ⦋m⦌).unit.app
        ((componentInverseImageAb S D K a ⦋m⦌).obj G))]
  exact (abelianHomEquiv_abelianCosimplicialPushforward_iff_fiberTransitionAb S D K a G
    (resolutionTerm S D K a G m) φ
    ((componentRestrictionAbInverseImageIso S D K a G ⦋m⦌).hom ≫
      (S.componentLowerShriekAbAdjunction ⦋m⦌).unit.app
        ((componentInverseImageAb S D K a ⦋m⦌).obj G))
    (componentSheafSummand S ((totalInverseImageAb S D K a).obj G) φ ≫
      (S.abelianComponent ⦋n⦌).map (degIso S D K a G m).hom)).mpr
    (fiberTransitionAb_resolution_square S D K a G φ)

/-- **The mate of a cosimplicial transition of the complex of Stacks 0D79 is the corresponding
structure map of the resolution of Stacks 0D78.** The degree-`k` term of the complex is a right
adjoint whose left adjoint is the degree-`k` term of the resolution (`cechTermAdjunction`); this
says that the conjugate, along those adjunctions, of the cosimplicial transition at
`φ : ⦋m⦌ ⟶ ⦋n⦌` is the structure map of the resolution at `φ`, read through the identifications
of its terms. -/
theorem conjugateEquiv_abelianCosimplicialPushforward_map_app' {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    ((conjugateEquiv (cechTermAdjunction S D K a ⦋m⦌)
          (cechTermAdjunction S D K a ⦋n⦌)).symm
        ((abelianCosimplicialPushforward S D K a).map φ :
          abelianComponentPushforward S D K a ⦋m⦌ ⟶
            abelianComponentPushforward S D K a ⦋n⦌)).app G =
      (degIso' S D K a G n).inv ≫
        ((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G)).map φ.op ≫
          (degIso' S D K a G m).hom := by
  exact conjugateEquiv_abelianCosimplicialPushforward_map_app S D K a G φ

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
