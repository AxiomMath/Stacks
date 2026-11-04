module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationIndependenceClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionClassCases
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.CompositeFactorization
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.Factorization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition

/-!
# The Gysin map of a composite of local complete intersection morphisms

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` and
`g : Y ⟶ Z` be local complete intersection morphisms of schemes locally of finite type over `S`.
**Stacks 0FF5** asserts that if the Gysin map of Stacks 0FF3 exists for `g ∘ f` and for `g`, then
it exists for `f` and

  `(g ∘ f)^! = f^! ∘ g^!`   in `A^*(X ⟶ Z)^∧`.

## Main results

* `Stacks.Chow.SmoothFactorization.gysinMap_composite_of_regularImmersionCompositionCase`: for
  factorizations `X ⟶ P ⟶ Z` of `g ∘ f` and `Y ⟶ P' ⟶ Z` of `g`, the Gysin map of the factorization
  `X ⟶ P ×_Z P' ⟶ Z` of `g ∘ f` is the composite of the Gysin maps of the factorization
  `X ⟶ P ×_Z Y ⟶ Y` of `f` and of the factorization of `g`.
* `Stacks.Chow.lciGysinMap_comp_of_regularImmersionCompositionCase`: the statement above.

Both are proved under the hypothesis `Stacks.Chow.RegularImmersionCompositionCase C`, the
composition formula of Stacks 0FF0 for regular immersions.

## References

* [Stacks Project, Tag 0FF5](https://stacks.math.columbia.edu/tag/0FF5)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 0FF0](https://stacks.math.columbia.edu/tag/0FF0)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 069J](https://stacks.math.columbia.edu/tag/069J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

section Composition

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] {f : X ⟶ Y} {g : Y ⟶ Z} [LocallyOfFiniteType f]
  [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)

/-- For a factorization `F` of `g ∘ f` and a factorization `G` of `g`, the Gysin map of the
factorization `X ⟶ P ×_Z P' ⟶ Z` of `g ∘ f` built from them is the composite of the Gysin maps of
the induced factorization `X ⟶ P ×_Z Y ⟶ Y` of `f` and of `G`, granted the composition formula
`hcomp` for regular immersions. -/
theorem SmoothFactorization.gysinMap_composite_of_regularImmersionCompositionCase
    (hcomp : RegularImmersionCompositionCase C) (F : SmoothFactorization (f ≫ g))
    (G : SmoothFactorization g) (hlf : IsLocalCompleteIntersectionMorphism f)
    (hlg : IsLocalCompleteIntersectionMorphism g) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    (F.composite G).gysinMap C sX sZ (comp_comp_structureMorphism_eq hf hg)
        (isLocalCompleteIntersectionMorphism_comp f g hlf hlg) =
      completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg
        (F.ofComp.gysinMap C sX sY hf hlf) (G.gysinMap C sY sZ hg hlg) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set q := pullback.snd F.proj G.proj with hq
  have sq := (F.isPullback_compositeImm G).flip
  set e := sq.isoPullback with he
  have he₁ : e.hom ≫ pullback.fst G.imm q = F.ofComp.proj := sq.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd G.imm q = F.compositeImm G := sq.isoPullback_hom_snd
  let F₁ : SmoothFactorization f :=
    { ambient := pullback G.imm q
      imm := F.ofComp.imm ≫ e.hom
      proj := pullback.fst G.imm q
      isImmersion := inferInstance
      isSmooth := inferInstance
      imm_proj := by rw [Category.assoc, he₁, F.ofComp.imm_proj] }
  have hF₁ := SmoothFactorization.gysinMap_eq_of_regularImmersionCompositionCase C sX sY hf hcomp
    F₁ F.ofComp hlf
  set sP' := G.proj ≫ sZ with hsP'
  set sW := pullback.fst G.imm q ≫ sY with hsW
  set sR := q ≫ sP' with hsR
  have : IsLocallyNoetherian G.ambient := LocallyOfFiniteType.isLocallyNoetherian sP'
  have : IsLocallyNoetherian (pullback F.proj G.proj) := LocallyOfFiniteType.isLocallyNoetherian sR
  have : IsLocallyNoetherian (pullback G.imm q) := LocallyOfFiniteType.isLocallyNoetherian sW
  have hb := G.imm_comp_structureMorphism C sY sZ hg
  have hjW := pullbackSnd_comp_structureMorphism_eq C sY sP' G.imm hb q
  have hsWX : (F.ofComp.imm ≫ e.hom) ≫ sW = sX := F₁.imm_comp_structureMorphism C sX sY hf
  have hR : (q ≫ G.proj) ≫ sZ = sR := Category.assoc _ _ _
  have hrb := G.isRegularImmersion hlg
  have hrj : IsRegularImmersion (pullback.snd G.imm q) :=
    (isRegularImmersion_iff_isKoszulRegularImmersion _).2
      (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_pullback_snd_of_flat G.imm q
        (G.isKoszulRegularImmersion_of_lci hlg))
  have hrs : IsRegularImmersion (F.ofComp.imm ≫ e.hom) := F₁.isRegularImmersion hlf
  have hcomposite : (F.ofComp.imm ≫ e.hom) ≫ pullback.snd G.imm q =
      F.ofComp.imm ≫ F.compositeImm G := by
    rw [Category.assoc, he₂]
  have : IsLocallyNoetherian (F.composite G).ambient :=
    LocallyOfFiniteType.isLocallyNoetherian ((F.composite G).proj ≫ sZ)
  have hrc : IsRegularImmersion (F.ofComp.imm ≫ F.compositeImm G) :=
    (F.composite G).isRegularImmersion (isLocalCompleteIntersectionMorphism_comp f g hlf hlg)
  have hrsj : IsRegularImmersion ((F.ofComp.imm ≫ e.hom) ≫ pullback.snd G.imm q) := by
    have key : ∀ {a b : X ⟶ pullback F.proj G.proj} [IsImmersion a] [IsImmersion b], a = b →
        IsRegularImmersion a → IsRegularImmersion b := by
      rintro a b _ _ rfl ha
      exact ha
    exact key hcomposite.symm hrc
  set bB := completedVirtualNormalGysinClassOfImmersion C sY sP' G.imm hb
    (VirtualNormalBundle.ofIsRegularImmersion G.imm hrb)
  set gB := completedFlatPullbackOfSmooth C sP' sZ G.proj rfl
  set qB := completedFlatPullbackOfSmooth C sR sP' q rfl
  have h0 := hcomp sX sW sR (F.ofComp.imm ≫ e.hom) (pullback.snd G.imm q) hsWX hjW hrs hrj hrsj
  have h1 := regularImmersionSmoothBaseChangeCase C sY sP' G.imm hb q hrb hrj
  have h2 := completedBivariantRestriction_composite_completedFlatPullbackOfSmooth C sY sP' G.imm
    hb q bB
  rw [h1] at h2
  have h4 := completedFlatPullbackOfSmooth_comp C sR sP' sZ q G.proj rfl rfl
  refine eq_of_heq ((completedBivariantGroup.copy_heq C _ _ _ _).trans ?_)
  have L1 : completedBivariantCompositeOfInvertible C sX ((q ≫ G.proj) ≫ sZ) sZ
      (F.ofComp.imm ≫ F.compositeImm G) (q ≫ G.proj)
      ((F.composite G).imm_comp_structureMorphism C sX sZ (comp_comp_structureMorphism_eq hf hg))
      rfl
      (completedVirtualNormalGysinClassOfImmersion C sX ((q ≫ G.proj) ≫ sZ)
        (F.ofComp.imm ≫ F.compositeImm G)
        ((F.composite G).imm_comp_structureMorphism C sX sZ (comp_comp_structureMorphism_eq hf hg))
        (VirtualNormalBundle.ofIsRegularImmersion _ hrc))
      (completedFlatPullbackOfSmooth C ((q ≫ G.proj) ≫ sZ) sZ (q ≫ G.proj) rfl) ≍
      completedBivariantCompositeOfInvertible C sX sR sZ
        ((F.ofComp.imm ≫ e.hom) ≫ pullback.snd G.imm q) (q ≫ G.proj)
        (comp_comp_structureMorphism_eq hsWX hjW) (comp_comp_structureMorphism_eq rfl rfl)
        (completedVirtualNormalGysinClassOfImmersion C sX sR
          ((F.ofComp.imm ≫ e.hom) ≫ pullback.snd G.imm q)
          (comp_comp_structureMorphism_eq hsWX hjW)
          (VirtualNormalBundle.ofIsRegularImmersion _ hrsj))
        (completedBivariantCompositeOfInvertible C sR sP' sZ q G.proj rfl rfl qB gB) :=
    completedBivariantCompositeOfInvertible_heq_congr C rfl hR rfl hcomposite.symm rfl
      (completedVirtualNormalGysinClassOfImmersion_ofIsRegularImmersion_heq_congr C hR
        hcomposite.symm hrc hrsj)
      ((completedFlatPullbackOfSmooth_heq_congr C hR rfl).trans (heq_of_eq h4.symm))
  refine L1.trans ?_
  rw [h0]
  refine (completedBivariantCompositeOfInvertible_assoc C ..).trans ?_
  have inner :=
    ((completedBivariantCompositeOfInvertible_assoc C ..).symm.trans
    (completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl
      (pullback.condition (f := G.imm) (g := q)).symm rfl h2 (HEq.rfl (a := gB)))).trans
    (completedBivariantCompositeOfInvertible_assoc C ..)
  refine (completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl rfl
    (by rw [← Category.assoc, ← pullback.condition, Category.assoc]) HEq.rfl
    inner).trans ?_
  refine (completedBivariantCompositeOfInvertible_assoc C ..).symm.trans ?_
  have hs1 : completedBivariantCompositeOfInvertible C sX sW sY (F.ofComp.imm ≫ e.hom)
      (pullback.fst G.imm q) hsWX rfl
      (completedVirtualNormalGysinClassOfImmersion C sX sW (F.ofComp.imm ≫ e.hom) hsWX
        (VirtualNormalBundle.ofIsRegularImmersion _ hrs))
      (completedFlatPullbackOfSmooth C sW sY (pullback.fst G.imm q) rfl) ≍
      F.ofComp.gysinMap C sX sY hf hlf := by
    rw [← hF₁]
    exact (completedBivariantGroup.copy_heq C _ _ _ _).symm
  exact completedBivariantCompositeOfInvertible_heq_congr C rfl rfl rfl F₁.imm_proj G.imm_proj
    hs1 (completedBivariantGroup.copy_heq C _ _ _ _).symm

/-- Let `f : X ⟶ Y` and `g : Y ⟶ Z` be local complete intersection morphisms of schemes locally of
finite type over the base, such that the Gysin map exists for `g ∘ f` and for `g`. Granted the
composition formula `hcomp` for regular immersions, the Gysin map exists for `f`, and
`(g ∘ f)^! = f^! ∘ g^!` in `A^*(X ⟶ Z)^∧`. -/
theorem lciGysinMap_comp_of_regularImmersionCompositionCase
    (hcomp : RegularImmersionCompositionCase C) (hlf : IsLocalCompleteIntersectionMorphism f)
    (hlg : IsLocalCompleteIntersectionMorphism g) (hgf : GysinMapExists (f ≫ g))
    (hG : GysinMapExists g) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    ∃ hF : GysinMapExists f,
      lciGysinMap C sX sZ (comp_comp_structureMorphism_eq hf hg)
          (isLocalCompleteIntersectionMorphism_comp f g hlf hlg) hgf =
        completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg
          (lciGysinMap C sX sY hf hlf hF) (lciGysinMap C sY sZ hg hlg hG) := by
  refine ⟨GysinMapExists.left_of_comp f g hgf, ?_⟩
  obtain ⟨F⟩ := (gysinMapExists_iff_nonempty _).1 hgf
  obtain ⟨G⟩ := (gysinMapExists_iff_nonempty _).1 hG
  rw [← SmoothFactorization.gysinMap_eq_lciGysinMap_of_regularImmersionCompositionCase C sX sZ _
      hcomp (F.composite G) _ hgf,
    ← SmoothFactorization.gysinMap_eq_lciGysinMap_of_regularImmersionCompositionCase C sX sY hf
      hcomp F.ofComp hlf,
    ← SmoothFactorization.gysinMap_eq_lciGysinMap_of_regularImmersionCompositionCase C sY sZ hg
      hcomp G hlg hG]
  exact SmoothFactorization.gysinMap_composite_of_regularImmersionCompositionCase C sX sY sZ hf hg
    hcomp F G hlf hlg

end Composition

end Stacks.Chow

end
