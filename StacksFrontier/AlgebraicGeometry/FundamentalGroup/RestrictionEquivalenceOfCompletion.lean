module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Unramified.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.AlgebraicGeometry.TensorFiniteness.RingedSpace
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FiniteLocallyFreeAdic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Thickening
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantSheaf
import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.BaseChangeIso
import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
import StacksFrontier.AlgebraicGeometry.PushforwardCoherent

/-!
# Restriction of finite étale covers when completion is an equivalence

Let `X` be a Noetherian scheme and `Y ⊆ X` a closed subscheme with ideal sheaf `I`. An object
`(ℱ_n)` of `Coh(X, I)` is finite locally free when each `ℱ_n` is a finite locally free
`𝒪_X / I^{n+1}`-module, i.e. the direct image of a finite locally free module on the closed
subscheme cut out by `I^{n+1}` (`Stacks.Algebraization.IsFiniteLocallyFreeAdic`). [Stacks, Tag
0EL9] asserts: if the completion functor `Coh(𝒪_X) ⥤ Coh(X, I)` is an equivalence on the full
subcategories of finite locally free objects, then restriction `FÉt_X ⥤ FÉt_Y` is an
equivalence.

## Main definitions

* `Stacks.FundamentalGroup.FiniteLocallyFreeCoherent` and
  `Stacks.FundamentalGroup.FiniteLocallyFreeAdic` — the two full subcategories of finite locally
  free objects.
* `Stacks.FundamentalGroup.finiteLocallyFreeCompletion` — the completion functor of Stacks 0880
  between them.

## Main results

* `Stacks.FundamentalGroup.finiteEtaleBaseChange_isEquivalence_of_completionEquivalence` —
  [Stacks, Tag 0EL9], for a closed immersion `i : Y ⟶ X` with ideal sheaf `ker i`.
* `Stacks.FundamentalGroup.finiteEtaleBaseChange_isEquivalence_of_completion` — the same for the
  closed subscheme cut out by a quasi-coherent ideal sheaf, from which the former is deduced.

## Implementation notes

Full faithfulness is [Stacks, Tag 0EL8]. Essential surjectivity follows the source. A finite
étale `U_0 ⟶ Y` lifts, by [Stacks, Tag 0BQB], to a tower of finite étale `U_n ⟶ Y_n` over the
infinitesimal neighbourhoods `Y_n`, each the base change of the next; the direct images of their
structure sheaves form a finite locally free object of `Coh(X, I)`, which is the completion of a
finite locally free coherent `ℱ`. The multiplications and units of the tower are maps of
completions, so they come from maps `ℱ ⊗ ℱ ⟶ ℱ` and `𝒪_X ⟶ ℱ`, and faithfulness of completion
gives the axioms of a sheaf of commutative algebras; `U` is its relative spectrum, finite
locally free over `X`, with `U ×_X Y_n ≅ U_n`.

Étaleness of `U ⟶ X` is checked through the separability idempotent rather than the discriminant
of [Stacks, Tag 0BJF]: the diagonal idempotents of the étale `U_n ⟶ Y_n` form a compatible system
of sections of the direct image of `𝒪_{U ×_X U}`, which is finite locally free; full
faithfulness of completion produces a global section `e` with `Δ^♯(e) = 1` and
`(x ⊗ 1 - 1 ⊗ x) e = 0`, a separability element. On every affine open of `X` it makes the ring of
sections of `U` formally unramified, and `U ⟶ X`, being flat and of finite presentation, is
étale.

## References

* [Stacks Project, Tag 0EL9](https://stacks.math.columbia.edu/tag/0EL9)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
* [Stacks Project, Tag 0BQB](https://stacks.math.columbia.edu/tag/0BQB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf
  Stacks.Algebraization.sectionsSMulCommClassΓ Stacks.Algebraization.monoSubmoduleι
  Stacks.Algebraization.sectionsModuleΓPresheaf Stacks.Algebraization.epi_cokernelπ_submodule

namespace Stacks.FundamentalGroup

/-- The finite locally free objects in the category of coherent sheaves. -/
public abbrev FiniteLocallyFreeCoherent (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (C := AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (fun F => AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F.obj)

/-- The finite locally free objects of `Coh(X, I)`: the coherent adic systems each of whose terms
is the direct image of a finite locally free module on the closed subscheme cut out by the
corresponding power of `I`. -/
public abbrev FiniteLocallyFreeAdic {X : Scheme.{u}} (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    (C := Stacks.Coherent.CoherentAdicSystems I) (Stacks.Algebraization.IsFiniteLocallyFreeAdic I)

/-- The completion functor `Coh(𝒪_X) ⥤ Coh(X, I)` of Stacks 0880 on the full subcategories of
finite locally free objects; it lands there by
`Stacks.Algebraization.isFiniteLocallyFreeAdic_completion`. -/
public noncomputable def finiteLocallyFreeCompletion (X : Scheme.{u})
    [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    FiniteLocallyFreeCoherent X ⥤ FiniteLocallyFreeAdic I :=
  ObjectProperty.lift (P := (Stacks.Algebraization.IsFiniteLocallyFreeAdic I :
      ObjectProperty (Stacks.Coherent.CoherentAdicSystems I)))
    ((ObjectProperty.ι (P := fun F : AlgebraicGeometry.SheafOfModules.CoherentModules
        X.ringCatSheaf => AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F.obj)) ⋙
      Stacks.Algebraization.completionFunctor X I)
    (fun F => Stacks.Algebraization.isFiniteLocallyFreeAdic_completion X I F.obj F.property)

private theorem completion_map_bijective_of_equivalence
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (E F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E.obj)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F.obj) :
    Function.Bijective (fun f : E ⟶ F =>
      (Stacks.Algebraization.completionFunctor X I).map f) := by
  let G := finiteLocallyFreeCompletion X I
  let : G.IsEquivalence := inferInstance
  let hFF := (G.asEquivalence.fullyFaithfulFunctor).comp
    (ObjectProperty.fullyFaithfulι (P := Stacks.Algebraization.IsFiniteLocallyFreeAdic I))
  let E' : FiniteLocallyFreeCoherent X := ⟨E, hE⟩
  let F' : FiniteLocallyFreeCoherent X := ⟨F, hF⟩
  let H := G ⋙ ObjectProperty.ι (P := Stacks.Algebraization.IsFiniteLocallyFreeAdic I)
  have hmap' (f : E' ⟶ F') :
      H.map f = (Stacks.Algebraization.completionFunctor X I).map f.hom := rfl
  have hb := hFF.map_bijective E' F'
  constructor
  · intro f g hfg
    have hfg' : ObjectProperty.homMk (X := E') (Y := F') f =
        ObjectProperty.homMk (X := E') (Y := F') g := by
      apply hb.1
      show H.map (ObjectProperty.homMk (X := E') (Y := F') f) =
        H.map (ObjectProperty.homMk (X := E') (Y := F') g)
      rw [hmap', hmap']
      exact hfg
    exact congrArg (fun k : E' ⟶ F' => k.hom) hfg'
  · intro f
    obtain ⟨g, hg⟩ := hb.2 f
    refine ⟨g.hom, ?_⟩
    show H.map g = f
    rw [hmap']
    exact hg

private theorem finiteLocallyFreeCompletion_essSurj
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (F : FiniteLocallyFreeAdic I) :
    ∃ E : FiniteLocallyFreeCoherent X,
      Nonempty ((Stacks.Algebraization.completionFunctor X I).obj E.obj ≅ F.obj) := by
  let G := finiteLocallyFreeCompletion X I
  let : G.IsEquivalence := inferInstance
  obtain ⟨E, e⟩ := Functor.EssSurj.mem_essImage G F
  exact ⟨E, ⟨Functor.mapIso (ObjectProperty.ι
    (P := Stacks.Algebraization.IsFiniteLocallyFreeAdic I)) (Classical.choice e)⟩⟩

private theorem finiteLocallyFreeCompletion_reflects_isIso
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    {E F : FiniteLocallyFreeCoherent X} (f : E ⟶ F)
    [IsIso ((finiteLocallyFreeCompletion X I).map f)] : IsIso f := by
  let G := finiteLocallyFreeCompletion X I
  let : G.IsEquivalence := inferInstance
  let : G.FullyFaithful := G.asEquivalence.fullyFaithfulFunctor
  exact isIso_of_reflects_iso f G

private theorem isIso_of_isIso_completion_app
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    {E F : FiniteLocallyFreeCoherent X} (f : E.obj ⟶ F.obj)
    (hf : ∀ n : ℕ, IsIso (((Stacks.Algebraization.completionFunctor X I).map f).hom.app (op n))) :
    IsIso f := by
  let G := finiteLocallyFreeCompletion X I
  let g : E ⟶ F := ObjectProperty.homMk f
  let α := ((Stacks.Algebraization.completionFunctor X I).map f).hom
  let (n : ℕᵒᵖ) : IsIso (α.app n) := hf n.unop
  let : IsIso α := NatIso.isIso_of_isIso_app _
  let H := ObjectProperty.ι (P := Stacks.Coherent.IsCoherentAdicSystem I)
  have : IsIso (H.map ((Stacks.Algebraization.completionFunctor X I).map f)) :=
    inferInstanceAs (IsIso α)
  have : IsIso ((Stacks.Algebraization.completionFunctor X I).map f) :=
    isIso_of_reflects_iso _ H
  let K := ObjectProperty.ι (P := Stacks.Algebraization.IsFiniteLocallyFreeAdic I)
  have : IsIso (K.map (G.map g)) :=
    inferInstanceAs (IsIso ((Stacks.Algebraization.completionFunctor X I).map f))
  have : IsIso (G.map g) := isIso_of_reflects_iso _ K
  have : IsIso g := finiteLocallyFreeCompletion_reflects_isIso X I g
  exact Functor.map_isIso (ObjectProperty.ι
    (P := fun M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf =>
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M.obj)) g

private theorem finiteEtale_isFiniteLocallyFree
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] : Stacks.Morphisms.IsFiniteLocallyFree f :=
  Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f |>.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

private theorem finiteEtaleBaseChange_essSurj_of_thickening
    {X Y : Scheme.{u}} (i : X ⟶ Y) (hi : Stacks.Thickenings.IsThickening i) :
    (AlgebraicGeometry.finiteEtaleBaseChange i).EssSurj :=
  (AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_isThickening i hi).essSurj

private theorem exists_finiteEtaleLift_nthOrder
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i] (n : ℕ)
    (A : AlgebraicGeometry.FiniteEtaleOver X) :
    ∃ B : AlgebraicGeometry.FiniteEtaleOver
        (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n),
      Nonempty ((AlgebraicGeometry.finiteEtaleBaseChange
        (Stacks.Thickenings.nthOrderInclusion i n)).obj B ≅ A) := by
  let j := Stacks.Thickenings.nthOrderInclusion i n
  have := finiteEtaleBaseChange_essSurj_of_thickening j
    (Stacks.Thickenings.nthOrderInclusion_isNthOrderThickening i n).isThickening
  exact Functor.EssSurj.mem_essImage _ A

private theorem finiteEtaleObject_isFiniteLocallyFree
    {X : Scheme.{u}}
    (A : AlgebraicGeometry.FiniteEtaleOver X) :
    Stacks.Morphisms.IsFiniteLocallyFree A.hom := by
  let : IsFinite A.hom := A.prop.1
  let : Etale A.hom := A.prop.2
  exact finiteEtale_isFiniteLocallyFree (X := X) (Y := A.left) (f := A.hom)

private theorem exists_finiteLocallyFreeEtaleLift_nthOrder
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i]
    (n : ℕ)
    [IsLocallyNoetherian (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n)]
    (A : AlgebraicGeometry.FiniteEtaleOver X) :
    ∃ B : AlgebraicGeometry.FiniteEtaleOver
        (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n),
      Stacks.Morphisms.IsFiniteLocallyFree B.hom ∧
        Nonempty ((AlgebraicGeometry.finiteEtaleBaseChange
          (Stacks.Thickenings.nthOrderInclusion i n)).obj B ≅ A) := by
  obtain ⟨B, hB⟩ := exists_finiteEtaleLift_nthOrder i n A
  exact ⟨B, finiteEtaleObject_isFiniteLocallyFree B, hB⟩

private def idealPowerInclusion {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) : (I ^ (n + 1)).subscheme ⟶ (I ^ (n + 2)).subscheme :=
  Scheme.IdealSheafData.inclusion
    (Scheme.IdealSheafData.le_def.mpr fun _ => Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

private lemma idealPowerInclusion_comp {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) :
    idealPowerInclusion I n ≫ (I ^ (n + 2)).subschemeι =
      (I ^ (n + 1)).subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

private lemma idealPowerInclusion_isThickening {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) :
    Stacks.Thickenings.IsThickening (idealPowerInclusion I n) := by
  have hc := idealPowerInclusion_comp I n
  have : IsClosedImmersion
      (idealPowerInclusion I n ≫ (I ^ (n + 2)).subschemeι) := by
    rw [hc]
    infer_instance
  refine ⟨IsClosedImmersion.of_comp_isClosedImmersion _
    (I ^ (n + 2)).subschemeι, ?_⟩
  intro y
  have hy : (I ^ (n + 2)).subschemeι y ∈
      Set.range (I ^ (n + 1)).subschemeι := by
    have hr : Set.range (I ^ (n + 1)).subschemeι =
        Set.range (I ^ (n + 2)).subschemeι := by
      simp only [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.support_pow_succ]
    rw [hr]
    exact ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, (I ^ (n + 2)).subschemeι.isClosedEmbedding.injective ?_⟩
  exact (Scheme.Hom.comp_apply (idealPowerInclusion I n)
    (I ^ (n + 2)).subschemeι x).symm.trans
      ((congrArg (fun f => f x) hc).trans hx)

private def liftFiniteEtale {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    (hj : Stacks.Thickenings.IsThickening j) (A : AlgebraicGeometry.FiniteEtaleOver Y) :
    AlgebraicGeometry.FiniteEtaleOver Z := by
  letI := AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_isThickening j hj
  exact (AlgebraicGeometry.finiteEtaleBaseChange j).asEquivalence.inverse.obj A

private def liftFiniteEtaleIso {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    (hj : Stacks.Thickenings.IsThickening j) (A : AlgebraicGeometry.FiniteEtaleOver Y) :
    (AlgebraicGeometry.finiteEtaleBaseChange j).obj (liftFiniteEtale j hj A) ≅ A := by
  letI := AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_isThickening j hj
  exact (AlgebraicGeometry.finiteEtaleBaseChange j).asEquivalence.counitIso.app A

private def finiteEtaleTower {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) : ∀ n, AlgebraicGeometry.FiniteEtaleOver (Y n)
  | 0 => A
  | n + 1 => liftFiniteEtale (j n) (hj n) (finiteEtaleTower j hj A n)

private def finiteEtaleTowerIso {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) (n : ℕ) :
    (AlgebraicGeometry.finiteEtaleBaseChange (j n)).obj (finiteEtaleTower j hj A (n + 1)) ≅
      finiteEtaleTower j hj A n :=
  liftFiniteEtaleIso (j n) (hj n) (finiteEtaleTower j hj A n)

private def finiteEtaleTowerStep {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) (n : ℕ) :
    (finiteEtaleTower j hj A n).left ⟶ (finiteEtaleTower j hj A (n + 1)).left :=
  (finiteEtaleTowerIso j hj A n).inv.left ≫
    Limits.pullback.fst (finiteEtaleTower j hj A (n + 1)).hom (j n)

private lemma finiteEtaleTowerStep_isPullback {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) (n : ℕ) :
    IsPullback (finiteEtaleTowerStep j hj A n) (finiteEtaleTower j hj A n).hom
      (finiteEtaleTower j hj A (n + 1)).hom (j n) := by
  let e := finiteEtaleTowerIso j hj A n
  let e' : (finiteEtaleTower j hj A n).left ≅
      Limits.pullback (finiteEtaleTower j hj A (n + 1)).hom (j n) :=
    { hom := e.inv.left
      inv := e.hom.left
      hom_inv_id := congrArg (fun f => f.left) e.inv_hom_id
      inv_hom_id := congrArg (fun f => f.left) e.hom_inv_id }
  apply (IsPullback.of_hasPullback (finiteEtaleTower j hj A (n + 1)).hom
    (j n)).of_iso' e' (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · dsimp only [e', Iso.refl_hom]
    rw [Category.comp_id]
    exact MorphismProperty.Over.w e.inv
  · simp
  · simp

private def finiteEtaleTowerOver {X : Scheme.{u}} {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (p : ∀ n, Y n ⟶ X) (hp : ∀ n, j n ≫ p (n + 1) = p n)
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) : ℕ ⥤ Over X :=
  Functor.ofSequence (X := fun n => Over.mk ((finiteEtaleTower j hj A n).hom ≫ p n))
    (fun n => Over.homMk (finiteEtaleTowerStep j hj A n) (by
      dsimp only [Over.mk_hom]
      rw [← Category.assoc, (finiteEtaleTowerStep_isPullback j hj A n).w,
        Category.assoc, hp n]))

private def pushforwardStructureSheafMap {X : Scheme.{u}} {Y Z : Over X}
    (f : Y ⟶ Z) : Stacks.Morphisms.pushforwardStructureSheaf Z.hom ⟶
      Stacks.Morphisms.pushforwardStructureSheaf Y.hom :=
  (Scheme.Modules.pushforward Z.hom).map
      (SheafOfModules.unitToPushforwardObjUnit f.left.toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp f.left Z.hom).hom.app
      (SheafOfModules.unit Y.left.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr (Over.w f)).hom.app
      (SheafOfModules.unit Y.left.ringCatSheaf)

private def finiteEtaleTowerModules {X : Scheme.{u}} {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (p : ∀ n, Y n ⟶ X) (hp : ∀ n, j n ≫ p (n + 1) = p n)
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n =>
    Stacks.Morphisms.pushforwardStructureSheaf ((finiteEtaleTowerOver j hj p hp A).obj n).hom)
      (fun n => pushforwardStructureSheafMap
        ((finiteEtaleTowerOver j hj p hp A).map (homOfLE (Nat.le_succ n))))

private def finiteEtaleTowerModulesObjIso {X : Scheme.{u}} {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (p : ∀ n, Y n ⟶ X) (hp : ∀ n, j n ≫ p (n + 1) = p n)
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) (n : ℕ) :
    (Scheme.Modules.pushforward (p n)).obj
      (Stacks.Morphisms.pushforwardStructureSheaf (finiteEtaleTower j hj A n).hom) ≅
        (finiteEtaleTowerModules j hj p hp A).obj (op n) :=
  (Scheme.Modules.pushforwardComp (finiteEtaleTower j hj A n).hom (p n)).app _

private lemma finiteEtaleTowerModules_finiteLocallyFree {X : Scheme.{u}}
    {Y : ℕ → Scheme.{u}} (j : ∀ n, Y n ⟶ Y (n + 1))
    (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (p : ∀ n, Y n ⟶ X) (hp : ∀ n, j n ≫ p (n + 1) = p n)
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) (n : ℕ) :
    ∃ M : (Y n).Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M ∧
      Nonempty ((Scheme.Modules.pushforward (p n)).obj M ≅
        (finiteEtaleTowerModules j hj p hp A).obj (op n)) := by
  refine ⟨Stacks.Morphisms.pushforwardStructureSheaf (finiteEtaleTower j hj A n).hom,
    ?_, ⟨finiteEtaleTowerModulesObjIso j hj p hp A n⟩⟩
  exact ((Stacks.Morphisms.isFiniteLocallyFree_iff _).mp
    (finiteEtaleObject_isFiniteLocallyFree (finiteEtaleTower j hj A n))).2

private lemma finiteEtaleTowerModules_isCoherent {X : Scheme.{u}}
    [IsLocallyNoetherian X] {Y : ℕ → Scheme.{u}}
    (j : ∀ n, Y n ⟶ Y (n + 1)) (hj : ∀ n, Stacks.Thickenings.IsThickening (j n))
    (p : ∀ n, Y n ⟶ X) [∀ n, IsFinite (p n)]
    (hp : ∀ n, j n ≫ p (n + 1) = p n)
    (A : AlgebraicGeometry.FiniteEtaleOver (Y 0)) (n : ℕ) :
    ((finiteEtaleTowerModules j hj p hp A).obj (op n)).IsCoherent := by
  let B := finiteEtaleTower j hj A n
  let : IsFinite B.hom := B.prop.1
  let f := B.hom ≫ p n
  let : IsFinite f := inferInstance
  let : IsLocallyNoetherian B.left :=
    LocallyOfFiniteType.isLocallyNoetherian f
  have hu : (SheafOfModules.unit B.left.ringCatSheaf).IsQuasicoherent ∧
      (SheafOfModules.unit B.left.ringCatSheaf).IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae B.left
      (SheafOfModules.unit _)).out 1 2).mp
      (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent B.left)
  let := hu.1
  exact @Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite
    B.left X f _ _
    (SheafOfModules.unit B.left.ringCatSheaf) hu.1
    (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent B.left)

private lemma idealPowerMultiple_pushforwardStructureSheaf_eq_bot
    {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ)
    (hI : I ^ n ≤ f.ker) :
    Stacks.Algebraization.idealPowerMultiple I n (Stacks.Morphisms.pushforwardStructureSheaf f) =
      ⊥ := by
  apply le_antisymm _ bot_le
  rw [Stacks.Algebraization.idealPowerMultiple_le_iff]
  intro U
  apply Submodule.smul_le.mpr
  intro r hr m _
  have hr' : r ∈ f.ker.ideal U := (Scheme.IdealSheafData.le_def.mp hI U) hr
  have hz : (f.app U.1).hom r = 0 := f.ideal_ker_le U hr'
  have hsmul : r • m = 0 := by
    change Γ(Y, f ⁻¹ᵁ U.1) at m
    show (f.app U.1).hom r * m = 0
    rw [hz, zero_mul]
  rw [hsmul]
  exact Submodule.zero_mem _

private def idealPowerTowerModules {X : Scheme.{u}} (I : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) : ℕᵒᵖ ⥤ X.Modules :=
  finiteEtaleTowerModules (idealPowerInclusion I) (idealPowerInclusion_isThickening I)
    (fun n => (I ^ (n + 1)).subschemeι) (idealPowerInclusion_comp I) A

private lemma idealPowerTowerModules_annihilated {X : Scheme.{u}}
    (I : X.IdealSheafData) (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) (n : ℕ) :
    Stacks.Algebraization.idealPowerMultiple I (n + 1)
      ((idealPowerTowerModules I A).obj (op n)) = ⊥ := by
  let B := finiteEtaleTower (idealPowerInclusion I)
    (idealPowerInclusion_isThickening I) A n
  exact idealPowerMultiple_pushforwardStructureSheaf_eq_bot
    (B.hom ≫ (I ^ (n + 1)).subschemeι) I (n + 1)
      (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using
        B.hom.le_ker_comp (I ^ (n + 1)).subschemeι)

private lemma idealPowerTowerModules_coherent {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) (n : ℕ) :
    ((idealPowerTowerModules I A).obj (op n)).IsCoherent :=
  finiteEtaleTowerModules_isCoherent (idealPowerInclusion I)
    (idealPowerInclusion_isThickening I) (fun n => (I ^ (n + 1)).subschemeι)
    (idealPowerInclusion_comp I) A n

private lemma idealPowerTowerModules_finiteLocallyFree {X : Scheme.{u}}
    (I : X.IdealSheafData) (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) (n : ℕ) :
    ∃ M : (I ^ (n + 1)).subscheme.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M ∧
        Nonempty ((Scheme.Modules.pushforward (I ^ (n + 1)).subschemeι).obj M ≅
          (idealPowerTowerModules I A).obj (op n)) :=
  finiteEtaleTowerModules_finiteLocallyFree (idealPowerInclusion I)
    (idealPowerInclusion_isThickening I) (fun n => (I ^ (n + 1)).subschemeι)
    (idealPowerInclusion_comp I) A n

section

open TopologicalSpace CategoryTheory.Limits

private lemma moduleSection_ext_affine {X : Scheme.{u}} (F : X.Modules)
    {U : X.Opens} {s t : F.val.obj (op U)}
    (h : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U),
      F.val.map (homOfLE hVU).op s = F.val.map (homOfLE hVU).op t) : s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  obtain ⟨V, hV, rfl⟩ := hV
  exact ⟨V, hVU, hxV, h ⟨V, hV⟩ hVU⟩

private lemma moduleHom_ext_affine {X : Scheme.{u}} {F G : X.Modules}
    {f g : F ⟶ G} (h : ∀ U : X.affineOpens, f.val.app (op U.1) = g.val.app (op U.1)) :
    f = g := by
  ext U s
  apply moduleSection_ext_affine G
  intro V hVU
  exact (PresheafOfModules.naturality_apply f.val (homOfLE hVU).op s).symm.trans
    ((congrArg (fun k => k (F.val.map (homOfLE hVU).op s)) (h V)).trans
      (PresheafOfModules.naturality_apply g.val (homOfLE hVU).op s))

private def moduleHomOfAffine {X : Scheme.{u}} {F G : X.Modules}
    (f : ∀ U : X.affineOpens, F.val.obj (op U.1) ⟶ G.val.obj (op U.1))
    (hf : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1) (s : F.val.obj (op U.1)),
      f V (F.val.map (homOfLE hVU).op s) = G.val.map (homOfLE hVU).op (f U s)) :
    F ⟶ G := by
  let α : (inducedFunctor (fun U : X.affineOpens => U.1)).op ⋙ F.val.presheaf ⟶
      (inducedFunctor (fun U : X.affineOpens => U.1)).op ⋙ G.val.presheaf :=
    { app := fun U => AddCommGrpCat.ofHom (f U.unop).hom.toAddMonoidHom
      naturality := by
        intro U V hUV
        ext s
        exact hf U.unop V.unop
          (leOfHom ((inducedFunctor (fun U : X.affineOpens => U.1)).map hUV.unop)) s }
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa using X.isBasis_affineOpens
  let β := TopCat.Sheaf.restrictHomEquivHom F.val.presheaf
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj G) hB α
  have hβ (U : X.affineOpens) : β.app (op U.1) = α.app (op U) :=
    TopCat.Sheaf.extend_hom_app _ _ _ _ _
  refine ⟨PresheafOfModules.homMk β ?_⟩
  intro U r s
  apply moduleSection_ext_affine G
  intro V hVU
  have hn (s : F.val.obj U) :
      G.val.map (homOfLE hVU).op (β.app U s) =
        f V (F.val.map (homOfLE hVU).op s) :=
    (CategoryTheory.congr_fun (β.naturality (homOfLE hVU).op) s).symm.trans
      (congrArg (fun k => k (F.val.map (homOfLE hVU).op s)) (hβ V))
  exact (hn (r • s)).trans ((congrArg (f V) (F.val.map_smul _ r s)).trans
    (((f V).hom.map_smul _ _).trans ((congrArg (fun z =>
      X.ringCatSheaf.obj.map (homOfLE hVU).op r • z) (hn s).symm).trans
        (G.val.map_smul _ r (β.app U s)).symm)))

private lemma moduleHomOfAffine_app {X : Scheme.{u}} {F G : X.Modules}
    (f : ∀ U : X.affineOpens, F.val.obj (op U.1) ⟶ G.val.obj (op U.1))
    (hf : ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1) (s : F.val.obj (op U.1)),
      f V (F.val.map (homOfLE hVU).op s) = G.val.map (homOfLE hVU).op (f U s))
    (U : X.affineOpens) : (moduleHomOfAffine f hf).val.app (op U.1) = f U := by
  ext s
  show ((TopCat.Sheaf.restrictHomEquivHom
    (B := fun V : X.affineOpens => V.1) F.val.presheaf
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj G) _ _).app (op U.1)).hom s = _
  exact congrArg (fun (k : F.val.presheaf.obj (op U.1) ⟶
    G.val.presheaf.obj (op U.1)) => k s)
      (TopCat.Sheaf.extend_hom_app (B := fun V : X.affineOpens => V.1)
        F.val.presheaf ((SheafOfModules.toSheaf X.ringCatSheaf).obj G) _ _ U)

private lemma module_epi_of_surjective_affine {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (hf : ∀ U : X.affineOpens, Function.Surjective (f.val.app (op U.1))) :
    Epi f := by
  constructor
  intro H g h hgh
  apply moduleHom_ext_affine
  intro U
  ext s
  obtain ⟨t, rfl⟩ := hf U s
  exact congrArg (fun k : F ⟶ H => k.val.app (op U.1) t) hgh

private lemma module_exists_desc_of_surjective_affine {X : Scheme.{u}}
    {F G H : X.Modules} (f : F ⟶ G) (g : F ⟶ H)
    (hf : ∀ U : X.affineOpens, Function.Surjective (f.val.app (op U.1)))
    (hker : ∀ U : X.affineOpens,
      LinearMap.ker (f.val.app (op U.1)).hom ≤ LinearMap.ker (g.val.app (op U.1)).hom) :
    ∃ k : G ⟶ H, f ≫ k = g := by
  let k (U : X.affineOpens) : G.val.obj (op U.1) ⟶ H.val.obj (op U.1) :=
    ModuleCat.ofHom (((LinearMap.ker (f.val.app (op U.1)).hom).liftQ
      (g.val.app (op U.1)).hom (hker U)).comp
        ((f.val.app (op U.1)).hom.quotKerEquivOfSurjective (hf U)).symm.toLinearMap)
  have hk (U : X.affineOpens) (s : F.val.obj (op U.1)) :
      k U (f.val.app (op U.1) s) = g.val.app (op U.1) s :=
    congrArg ((LinearMap.ker (f.val.app (op U.1)).hom).liftQ
      (g.val.app (op U.1)).hom (hker U))
        (LinearMap.quotKerEquivOfSurjective_symm_apply _ (hf U) s)
  have hn (U V : X.affineOpens) (hVU : V.1 ≤ U.1) (s : G.val.obj (op U.1)) :
      k V (G.val.map (homOfLE hVU).op s) = H.val.map (homOfLE hVU).op (k U s) := by
    obtain ⟨t, rfl⟩ := hf U s
    refine (congrArg (k V)
      (PresheafOfModules.naturality_apply f.val (homOfLE hVU).op t).symm).trans ?_
    refine (hk V _).trans ?_
    refine (PresheafOfModules.naturality_apply g.val (homOfLE hVU).op t).trans ?_
    exact congrArg (H.val.map (homOfLE hVU).op) (hk U t).symm
  refine ⟨moduleHomOfAffine k hn, ?_⟩
  apply moduleHom_ext_affine
  intro U
  ext s
  show (moduleHomOfAffine k hn).val.app (op U.1) (f.val.app (op U.1) s) = _
  rw [moduleHomOfAffine_app]
  exact hk U s

private def moduleIsCokernelOfAffine {X : Scheme.{u}} {F G : X.Modules}
    (N : F.Submodule) (f : F ⟶ G)
    (w : N.ι ≫ f = (0 : (N.toSheafOfModules : X.Modules) ⟶ _))
    (hf : ∀ U : X.affineOpens, Function.Surjective (f.val.app (op U.1)))
    (hker : ∀ U : X.affineOpens,
      LinearMap.ker (f.val.app (op U.1)).hom ≤ N.toSubmodule.obj (op U.1)) :
    IsColimit (CokernelCofork.ofπ f w) := by
  letI := module_epi_of_surjective_affine f hf
  apply CokernelCofork.IsColimit.ofπ' f w
  intro H g hg
  have hh (U : X.affineOpens) : LinearMap.ker (f.val.app (op U.1)).hom ≤
      LinearMap.ker (g.val.app (op U.1)).hom := by
    intro s hs
    exact congrArg (fun k : N.toSheafOfModules ⟶ H =>
      k.val.app (op U.1) ⟨s, hker U hs⟩) hg
  exact ⟨(module_exists_desc_of_surjective_affine f g hf hh).choose,
    (module_exists_desc_of_surjective_affine f g hf hh).choose_spec⟩

private def moduleKernelSubmodule {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) :
    F.Submodule where
  obj U := LinearMap.ker (f.val.app U).hom
  map {U V} g := by
    intro x hx
    change f.val.app V (F.val.map g x) = 0
    rw [PresheafOfModules.naturality_apply, show f.val.app U x = 0 from hx, map_zero]
    rfl
  isSheaf {U} x hx := by
    let H := G.val.presheaf ⋙ forget AddCommGrpCat.{u}
    have hs : Presheaf.IsSheaf (Opens.grothendieckTopology X) H :=
      GrothendieckTopology.HasSheafCompose.isSheaf _ G.isSheaf
    change f.val.app U x = 0
    have hs' := (isSheaf_iff_isSheaf_of_type _ H).mp hs
    apply (hs' _ hx).isSeparatedFor.ext
    intro V i hi
    change G.val.map i.op (f.val.app U x) = G.val.map i.op 0
    rw [← PresheafOfModules.naturality_apply, map_zero]
    exact hi

private lemma idealPowerQuotient_iso_of_affine {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {F G : X.Modules} (f : F ⟶ G)
    (hf : ∀ U : X.affineOpens, Function.Surjective (f.val.app (op U.1)))
    (hker : ∀ U : X.affineOpens, LinearMap.ker (f.val.app (op U.1)).hom =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) (F.val.obj (op U.1)))) :
    ∃ e : Stacks.Algebraization.idealPowerQuotient I n F ≅ G,
      cokernel.π (Stacks.Algebraization.idealPowerMultiple I n F).ι ≫ e.hom = f := by
  have hN : Stacks.Algebraization.idealPowerMultiple I n F ≤ moduleKernelSubmodule f := by
    rw [Stacks.Algebraization.idealPowerMultiple_le_iff]
    intro U
    exact (hker U).symm.le
  have w : (Stacks.Algebraization.idealPowerMultiple I n F).ι ≫ f =
      (0 :
        ((Stacks.Algebraization.idealPowerMultiple I n F).toSheafOfModules : X.Modules) ⟶ _) := by
    ext U s
    exact hN U s.property
  have hK (U : X.affineOpens) : LinearMap.ker (f.val.app (op U.1)).hom ≤
      (Stacks.Algebraization.idealPowerMultiple I n F).toSubmodule.obj (op U.1) := by
    rw [hker U]
    exact (Stacks.Algebraization.idealPowerMultiple_le_iff I n F _).mp le_rfl U
  let c := moduleIsCokernelOfAffine _ f w hf hK
  exact ⟨(cokernelIsCokernel _).coconePointUniqueUpToIso c,
    (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom c WalkingParallelPair.one⟩

private lemma ker_eq_map_of_isPushout
    {R A B P : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {a : A ⟶ P} {b : B ⟶ P} (h : IsPushout f g a b)
    (hf : Function.Surjective f.hom) :
    RingHom.ker b.hom = (RingHom.ker f.hom).map g.hom := by
  let K := (RingHom.ker f.hom).map g.hom
  let q := Ideal.Quotient.mk K
  let e := RingHom.quotientKerEquivOfSurjective hf
  have he (r : R) : e.symm (f.hom r) = Ideal.Quotient.mk _ r := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hf r).symm
  have hq : RingHom.ker f.hom ≤ RingHom.ker (q.comp g.hom) := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.hom hr)
  let k : A →+* B ⧸ K := (Ideal.Quotient.lift _ (q.comp g.hom) hq).comp e.symm.toRingHom
  have hk : f ≫ CommRingCat.ofHom k = g ≫ CommRingCat.ofHom q := by
    ext r
    show (Ideal.Quotient.lift _ (q.comp g.hom) hq) (e.symm (f.hom r)) = q (g.hom r)
    rw [he]
    rfl
  let d : P ⟶ CommRingCat.of (B ⧸ K) := h.desc (CommRingCat.ofHom k) (CommRingCat.ofHom q) hk
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hd := congrArg (fun z : B ⟶ CommRingCat.of (B ⧸ K) => z.hom x)
      (h.inr_desc (CommRingCat.ofHom k) (CommRingCat.ofHom q) hk)
    change d.hom (b.hom x) = q x at hd
    rw [show b.hom x = 0 from hx, map_zero] at hd
    exact hd.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    show b.hom (g.hom r) = 0
    have hw := congrArg (fun z : R ⟶ P => z.hom r) h.w
    change a.hom (f.hom r) = b.hom (g.hom r) at hw
    rw [show f.hom r = 0 from hr, map_zero] at hw
    exact hw.symm

private lemma pushforwardStructureSheafMap_app {X : Scheme.{u}} {Y Z : Over X}
    (f : Y ⟶ Z) (U : X.Opens) :
    (pushforwardStructureSheafMap f).app U =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (f.left.appLE (Z.hom ⁻¹ᵁ U) (Y.hom ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, Over.w f])) := by
  simp only [pushforwardStructureSheafMap, Scheme.Modules.Hom.comp_app]
  rfl


private lemma isPushout_appLE_of_isPullback
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    {US : S.Opens} {UT : T.Opens} {UX : X.Opens} {UY : Y.Opens}
    (hS : IsAffineOpen US) (hT : IsAffineOpen UT) (hX : IsAffineOpen UX)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
    (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :
    IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST)
      (g.appLE UX UY (by simp [hUY])) (iY.appLE UT UY (by simp [hUY])) := by
  let : IsAffine US.toScheme := hS
  let : IsAffine UT.toScheme := hT
  let : IsAffine UX.toScheme := hX
  have hp := isPushout_appTop_of_isPullback (Scheme.Hom.isPullback_resLE H hUST hUSX hUY)
  refine hp.of_iso US.topIso UX.topIso UT.topIso UY.topIso ?_ ?_ ?_ ?_
  all_goals simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma isPullback_comp_mono
    {C : Type*} [Category C] {P X Y Z T : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (i : Z ⟶ T) [Mono i] :
    IsPullback fst snd (f ≫ i) (g ≫ i) := by
  have w : fst ≫ (f ≫ i) = snd ≫ (g ≫ i) := by
    rw [← Category.assoc, ← Category.assoc, h.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst s.snd ((cancel_mono i).mp (by simpa using s.condition)))
    (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _) ?_⟩⟩
  intro s m hm₁ hm₂
  apply h.hom_ext
  · exact hm₁.trans (h.lift_fst _ _ _).symm
  · exact hm₂.trans (h.lift_snd _ _ _).symm

private lemma pushforwardStructureSheafMap_surjective_affine
    {X : Scheme.{u}} {Y Z : Over X} (f : Y ⟶ Z)
    [IsClosedImmersion f.left] [IsAffineHom Z.hom] (U : X.affineOpens) :
    Function.Surjective ((pushforwardStructureSheafMap f).val.app (op U.1)) := by
  have hU : Y.hom ⁻¹ᵁ U.1 = f.left ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, Over.w f]
  show Function.Surjective ((pushforwardStructureSheafMap f).app U.1)
  rw [pushforwardStructureSheafMap_app]
  show Function.Surjective (f.left.appLE (Z.hom ⁻¹ᵁ U.1) (Y.hom ⁻¹ᵁ U.1) _).hom
  have hs : ∀ (V : Y.left.Opens) (e : V = f.left ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1)),
      Function.Surjective (f.left.appLE (Z.hom ⁻¹ᵁ U.1) V e.le).hom := by
    intro V e
    subst V
    simpa only [Scheme.Hom.appLE_eq_app] using
      f.left.app_surjective (Z.hom ⁻¹ᵁ U.1) (U.2.preimage Z.hom)
  exact hs _ hU

private lemma pushforwardStructureSheafMap_ker_of_isPullback
    {X T : Scheme.{u}} {Y Z : Over X} (f : Y ⟶ Z)
    (i : T ⟶ X) [IsClosedImmersion i] [IsAffineHom Z.hom]
    (g : Y.left ⟶ T) (H : IsPullback f.left g Z.hom i)
    (U : X.affineOpens) :
    LinearMap.ker ((pushforwardStructureSheafMap f).val.app (op U.1)).hom =
      (RingHom.ker (i.app U.1).hom) •
        (⊤ : Submodule Γ(X, U.1)
          ((Stacks.Morphisms.pushforwardStructureSheaf Z.hom).val.obj (op U.1))) := by
  let : Algebra Γ(X, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1) := (Z.hom.app U.1).hom.toAlgebra
  have hUY : Y.hom ⁻¹ᵁ U.1 =
      f.left ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1) ⊓ g ⁻¹ᵁ (i ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← H.w, Over.w f, inf_idem]
  have hp := isPushout_appLE_of_isPullback H U.2
    (U.2.preimage i) (U.2.preimage Z.hom) le_rfl le_rfl hUY
  have hk := ker_eq_map_of_isPushout hp.flip (by
    simpa only [Scheme.Hom.appLE_eq_app] using i.app_surjective U.1 U.2)
  have hs := Ideal.smul_top_eq_map (S := Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (RingHom.ker (i.app U.1).hom)
  ext s
  show ((pushforwardStructureSheafMap f).app U.1) s = 0 ↔
    s ∈ (RingHom.ker (i.app U.1).hom) •
      (⊤ : Submodule Γ(X, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
  rw [hs]
  rw [pushforwardStructureSheafMap_app]
  show (f.left.appLE (Z.hom ⁻¹ᵁ U.1) (Y.hom ⁻¹ᵁ U.1) _).hom s = 0 ↔ _
  show s ∈ RingHom.ker (f.left.appLE _ _ _).hom ↔ _
  rw [hk]
  simp only [Scheme.Hom.appLE_eq_app]
  rfl

/-- The transition maps of `idealPowerTowerModules` are the maps induced on pushforwards. -/
private lemma pushforwardStructureSheafMap_tower_map {X : Scheme.{u}} (I : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) (n : ℕ) :
    pushforwardStructureSheafMap
      ((finiteEtaleTowerOver (idealPowerInclusion I) (idealPowerInclusion_isThickening I)
        (fun k => (I ^ (k + 1)).subschemeι) (idealPowerInclusion_comp I) A).map
          (homOfLE (Nat.le_succ n))) =
      (idealPowerTowerModules I A).map (homOfLE (Nat.le_succ n)).op :=
  by simp only [idealPowerTowerModules, finiteEtaleTowerModules,
    Functor.ofOpSequence_map_homOfLE_succ]

/-- The `n`th term of the tower of finite étale covers is finite over `X`. -/
private lemma isFinite_finiteEtaleTower_comp {X : Scheme.{u}} (I : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) (n : ℕ) :
    IsFinite ((finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A
      n).hom ≫ (I ^ (n + 1)).subschemeι) :=
  have := (finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A n).prop.1
  inferInstance

private lemma idealPowerTowerModules_quotient {X : Scheme.{u}}
    (I : X.IdealSheafData) (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) (n : ℕ) :
    ∃ e : Stacks.Algebraization.idealPowerQuotient I (n + 1)
        ((idealPowerTowerModules I A).obj (op (n + 1))) ≅
          (idealPowerTowerModules I A).obj (op n),
      cokernel.π (Stacks.Algebraization.idealPowerMultiple I (n + 1)
        ((idealPowerTowerModules I A).obj (op (n + 1)))).ι ≫ e.hom =
          (idealPowerTowerModules I A).map (homOfLE (Nat.le_succ n)).op := by
  let B := finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A
  let T := finiteEtaleTowerOver (idealPowerInclusion I)
    (idealPowerInclusion_isThickening I) (fun k => (I ^ (k + 1)).subschemeι)
    (idealPowerInclusion_comp I) A
  let α : T.obj n ⟶ T.obj (n + 1) := T.map (homOfLE (Nat.le_succ n))
  have hα : α.left = finiteEtaleTowerStep (idealPowerInclusion I)
      (idealPowerInclusion_isThickening I) A n := by
    simp only [α, T, finiteEtaleTowerOver, Functor.ofSequence_map_homOfLE_succ,
      Over.homMk_left]
    rfl
  have H : IsPullback α.left (B n).hom (T.obj (n + 1)).hom
      (I ^ (n + 1)).subschemeι := by
    have H := isPullback_comp_mono
      (finiteEtaleTowerStep_isPullback (idealPowerInclusion I)
        (idealPowerInclusion_isThickening I) A n) (I ^ (n + 2)).subschemeι
    rw [idealPowerInclusion_comp] at H
    rw [hα]
    exact H
  have : IsFinite (T.obj (n + 1)).hom := isFinite_finiteEtaleTower_comp I A (n + 1)
  let : IsClosedImmersion α.left := MorphismProperty.of_isPullback H.flip inferInstance
  have hq := idealPowerQuotient_iso_of_affine I (n + 1)
    (pushforwardStructureSheafMap α)
    (pushforwardStructureSheafMap_surjective_affine α) (fun U => by
      rw [pushforwardStructureSheafMap_ker_of_isPullback α _ (B n).hom H U,
        Scheme.IdealSheafData.ker_subschemeι_app]
      rfl)
  obtain ⟨e, he⟩ := hq
  refine ⟨e, ?_⟩
  exact he.trans (pushforwardStructureSheafMap_tower_map I A n)

private lemma idealPowerTowerModules_isCoherentAdicSystem {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) :
    Stacks.Coherent.IsCoherentAdicSystem I (idealPowerTowerModules I A) :=
  ⟨idealPowerTowerModules_coherent I A, idealPowerTowerModules_annihilated I A,
    idealPowerTowerModules_quotient I A⟩

private lemma finiteLocallyFree_of_iso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G := by
  obtain ⟨q, hq, hfin⟩ := hF.exists_isFiniteLocallyFreeData
  let := hq
  let := hfin
  let p : SheafOfModules.LocalGeneratorsData G :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom }
  refine { exists_isFiniteLocallyFreeData := ⟨p, ?_, ?_⟩ }
  · constructor
    intro i
    have hp : (p.generators i).π = (q.generators i).π ≫
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom :=
      SheafOfModules.GeneratingSections.ofEpi_π (q.generators i)
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom
    have h₀ : IsIso (q.generators i).π := hq.isIso i
    have hi : IsIso ((q.generators i).π ≫
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom) := inferInstance
    exact Eq.mp (congrArg (fun k => IsIso k) hp.symm) hi
  · constructor
    intro i
    exact ⟨(hfin.isFiniteType i).finite⟩

private lemma finiteLocallyFree_unit (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) := by
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff (𝟙 X)).mp
    (finiteEtale_isFiniteLocallyFree (𝟙 X))
  exact finiteLocallyFree_of_iso ((Scheme.Modules.pushforwardId X).app
    (SheafOfModules.unit X.ringCatSheaf)) h.2

private abbrev finiteLocallyFreeUnit (X : Scheme.{u}) [IsLocallyNoetherian X] :
    FiniteLocallyFreeCoherent X :=
  ⟨⟨SheafOfModules.unit X.ringCatSheaf,
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X⟩,
    finiteLocallyFree_unit X⟩

private lemma tensorSheaf_finiteLocallyFree {X : Scheme.{u}} (F G : X.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))) := by
  have hFl : _root_.SheafOfModules.IsLocallyFree.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) F := by
    obtain ⟨q, hq, -⟩ := hF.exists_isFiniteLocallyFreeData
    exact q.isLocallyFree
  have hGl : _root_.SheafOfModules.IsLocallyFree.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) G := by
    obtain ⟨q, hq, -⟩ := hG.exists_isFiniteLocallyFreeData
    exact q.isLocallyFree
  have hFt : _root_.SheafOfModules.IsFiniteType.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) F := by
    obtain ⟨q, _, hq⟩ := hF.exists_isFiniteLocallyFreeData
    exact { exists_localGeneratorsData := ⟨q, hq⟩ }
  have hGt : _root_.SheafOfModules.IsFiniteType.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) G := by
    obtain ⟨q, _, hq⟩ := hG.exists_isFiniteLocallyFreeData
    exact { exists_localGeneratorsData := ⟨q, hq⟩ }
  let T : X.Modules :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))
  have hTl : _root_.SheafOfModules.IsLocallyFree.{u, u, u} T :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isLocallyFree X.toRingedSpace F G hFl hGl
  have hTt : _root_.SheafOfModules.IsFiniteType.{u, u, u} T :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isFiniteType X.toRingedSpace F G hFt hGt
  have : T.IsQuasicoherent := by
    obtain ⟨q, hq⟩ := hTl.exists_isLocallyFreeData
    exact q.quasiCoherentData.isQuasicoherent
  have key := (Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae T).out 3 4
  exact key.mp ⟨hTl, hTt⟩

private abbrev finiteLocallyFreeTensor {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : FiniteLocallyFreeCoherent X) : FiniteLocallyFreeCoherent X := by
  let T : X.Modules :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F.obj.obj)).obj
        (G.obj.obj))
  let hT : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} T :=
    tensorSheaf_finiteLocallyFree F.obj.obj G.obj.obj F.property G.property
  letI := hT
  exact ⟨⟨T, Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X T⟩, hT⟩

private lemma exists_completionProjection_desc {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (E : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (n : ℕ)
    {F : X.Modules} (f : E.obj ⟶ F)
    (hF : Stacks.Algebraization.idealPowerMultiple I (n + 1) F = ⊥) :
    ∃ g : ((Stacks.Algebraization.completionFunctor X I).obj E).obj.obj (op n) ⟶ F,
      Stacks.Algebraization.completionProjection X I E n ≫ g = f := by
  let g := cokernel.desc (Stacks.Algebraization.idealPowerMultiple I (n + 1) E.obj).ι f
    (Stacks.Algebraization.comp_eq_zero_of_idealPowerMultiple_eq_bot I (n + 1) f hF)
  refine ⟨eqToHom (Stacks.Algebraization.completionFunctor_obj X I E n) ≫ g, ?_⟩
  have h1 : eqToHom (Stacks.Algebraization.completionFunctor_obj X I E n).symm ≫
      eqToHom (Stacks.Algebraization.completionFunctor_obj X I E n) ≫ g = g :=
    (eqToHom_trans_assoc _ _ g).trans
      ((congrArg (· ≫ g) (eqToHom_refl _ _)).trans (Category.id_comp g))
  exact (Category.assoc _ _ _).trans ((congrArg (fun k => cokernel.π
    (Stacks.Algebraization.idealPowerMultiple I (n + 1) E.obj).ι ≫ k) h1).trans
      (cokernel.π_desc _ _ _))

private lemma hom_ext_of_completionProjection_iso
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    {E G : FiniteLocallyFreeCoherent X} (F : Stacks.Coherent.CoherentAdicSystems I)
    (e : (Stacks.Algebraization.completionFunctor X I).obj G.obj ≅ F)
    {f g : E.obj.obj ⟶ G.obj.obj}
    (hfg : ∀ n,
      f ≫ Stacks.Algebraization.completionProjection X I G.obj n ≫ e.hom.hom.app (op n) =
        g ≫ Stacks.Algebraization.completionProjection X I G.obj n ≫ e.hom.hom.app (op n)) :
    f = g := by
  have heq : ObjectProperty.homMk (X := E.obj) (Y := G.obj) f =
      ObjectProperty.homMk (X := E.obj) (Y := G.obj) g := by
    apply (completion_map_bijective_of_equivalence X I E.obj G.obj
      E.property G.property).1
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    apply (@cancel_epi _ _ _ _ _ (Stacks.Algebraization.completionProjection X I E.obj n.unop)
        (Stacks.Algebraization.epi_completionProjection X I E.obj n.unop) _ _).mp
    rw [Stacks.Algebraization.completionFunctor_map_quotient,
      Stacks.Algebraization.completionFunctor_map_quotient]
    have : IsIso (e.hom.hom.app n) :=
      inferInstanceAs (IsIso ((Functor.mapIso
        (ObjectProperty.ι (P := Stacks.Coherent.IsCoherentAdicSystem I)) e).hom.app n))
    apply (cancel_mono (e.hom.hom.app n)).mp
    exact (Category.assoc _ _ _).trans ((hfg n.unop).trans (Category.assoc _ _ _).symm)
  exact congrArg (fun k : E.obj ⟶ G.obj => k.hom) heq

private theorem existsUnique_map_to_algebraizedSystem
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (E G : FiniteLocallyFreeCoherent X) (F : Stacks.Coherent.CoherentAdicSystems I)
    (e : (Stacks.Algebraization.completionFunctor X I).obj G.obj ≅ F)
    (q : ∀ n : ℕ, E.obj.obj ⟶ F.obj.obj (op n))
    (hq : ∀ n, q (n + 1) ≫ F.obj.map (homOfLE (Nat.le_succ n)).op = q n) :
    ∃! f : E.obj ⟶ G.obj, ∀ n,
      f.hom ≫ Stacks.Algebraization.completionProjection X I G.obj n ≫ e.hom.hom.app (op n) =
        q n := by
  choose d hd using fun n => exists_completionProjection_desc I E.obj n (q n) (F.property.2.1 n)
  have hn (n : ℕ) :
      ((Stacks.Algebraization.completionFunctor X I).obj E.obj).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ d n =
        d (n + 1) ≫ F.obj.map (homOfLE (Nat.le_succ n)).op := by
    apply (@cancel_epi _ _ _ _ _ (Stacks.Algebraization.completionProjection X I E.obj (n + 1))
        (Stacks.Algebraization.epi_completionProjection X I E.obj (n + 1)) _ _).mp
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ d n)
        (Stacks.Algebraization.completionProjection_transition X I E.obj n)).trans
        ((hd n).trans ((hq n).symm.trans
          ((congrArg (· ≫ F.obj.map (homOfLE (Nat.le_succ n)).op) (hd (n + 1))).symm.trans
            (Category.assoc _ _ _)))))
  let α : (Stacks.Algebraization.completionFunctor X I).obj E.obj ⟶ F :=
    ObjectProperty.homMk (NatTrans.ofOpSequence d hn)
  have hα (n : ℕ) :
      Stacks.Algebraization.completionProjection X I E.obj n ≫ α.hom.app (op n) = q n := hd n
  obtain ⟨f, hf⟩ := (completion_map_bijective_of_equivalence X I
    E.obj G.obj E.property G.property).2 (α ≫ e.inv)
  have hf' : ∀ n, f.hom ≫ Stacks.Algebraization.completionProjection X I G.obj n ≫
      e.hom.hom.app (op n) = q n := by
    intro n
    have h2 : Stacks.Algebraization.completionProjection X I E.obj n ≫
        ((Stacks.Algebraization.completionFunctor X I).map f ≫ e.hom).hom.app (op n) = q n :=
      (congrArg (fun k => Stacks.Algebraization.completionProjection X I E.obj n ≫
        k.hom.app (op n)) ((Iso.eq_comp_inv _).mp hf)).trans (hα n)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ e.hom.hom.app (op n))
        (Stacks.Algebraization.completionFunctor_map_quotient X I f n).symm).trans
          ((Category.assoc _ _ _).trans h2))
  refine ⟨f, hf', fun g hg => ?_⟩
  apply ObjectProperty.hom_ext
  exact hom_ext_of_completionProjection_iso X I F e fun n => (hg n).trans (hf' n).symm

private theorem existsUnique_completion_map
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (E F : FiniteLocallyFreeCoherent X)
    (φ : ∀ n : ℕ,
      ((Stacks.Algebraization.completionFunctor X I).obj E.obj).obj.obj (op n) ⟶
        ((Stacks.Algebraization.completionFunctor X I).obj F.obj).obj.obj (op n))
    (hφ : ∀ n : ℕ,
      ((Stacks.Algebraization.completionFunctor X I).obj E.obj).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ φ n =
        φ (n + 1) ≫ ((Stacks.Algebraization.completionFunctor X I).obj F.obj).obj.map
          (homOfLE (Nat.le_succ n)).op) :
    ∃! f : E.obj ⟶ F.obj, ∀ n : ℕ,
      Stacks.Algebraization.completionProjection X I E.obj n ≫ φ n =
        f.hom ≫ Stacks.Algebraization.completionProjection X I F.obj n := by
  have hq (n : ℕ) :
      (Stacks.Algebraization.completionProjection X I E.obj (n + 1) ≫ φ (n + 1)) ≫
        ((Stacks.Algebraization.completionFunctor X I).obj F.obj).obj.map
          (homOfLE (Nat.le_succ n)).op =
      Stacks.Algebraization.completionProjection X I E.obj n ≫ φ n := by
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hφ n).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ φ n)
        (Stacks.Algebraization.completionProjection_transition X I E.obj n))))
  obtain ⟨f, hf, hu⟩ := existsUnique_map_to_algebraizedSystem X I E F
    ((Stacks.Algebraization.completionFunctor X I).obj F.obj) (Iso.refl _)
    (fun n => Stacks.Algebraization.completionProjection X I E.obj n ≫ φ n) hq
  exact ⟨f, fun n => (hf n).symm.trans (congrArg (f.hom ≫ ·) (Category.comp_id _)),
    fun g hg => hu g fun n => (congrArg (g.hom ≫ ·) (Category.comp_id _)).trans (hg n).symm⟩


private lemma pushforwardStructureSheafMap_unit {X : Scheme.{u}} {Y Z : Over X}
    (f : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit Z.hom.toRingCatSheafHom ≫
      pushforwardStructureSheafMap f =
        SheafOfModules.unitToPushforwardObjUnit Y.hom.toRingCatSheafHom := by
  ext U
  show (pushforwardStructureSheafMap f).app U.unop ((Z.hom.app U.unop).hom 1) =
    (Y.hom.app U.unop).hom 1
  rw [pushforwardStructureSheafMap_app]
  show (f.left.appLE _ _ _).hom ((Z.hom.app U.unop).hom 1) =
    (Y.hom.app U.unop).hom 1
  simp only [map_one]

private lemma completionProjection_iso_transition
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (E : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : Stacks.Coherent.CoherentAdicSystems I)
    (e : (Stacks.Algebraization.completionFunctor X I).obj E ≅ F) (n : ℕ) :
    (Stacks.Algebraization.completionProjection X I E (n + 1) ≫ e.hom.hom.app (op (n + 1))) ≫
      F.obj.map (homOfLE (Nat.le_succ n)).op =
        Stacks.Algebraization.completionProjection X I E n ≫ e.hom.hom.app (op n) :=
  (Category.assoc _ _ _).trans ((congrArg
    (Stacks.Algebraization.completionProjection X I E (n + 1) ≫ ·)
      (e.hom.hom.naturality (homOfLE (Nat.le_succ n)).op).symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.hom.hom.app (op n))
      (Stacks.Algebraization.completionProjection_transition X I E n))))

private theorem existsUnique_algebraizedTowerUnit
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme)
    (E : FiniteLocallyFreeCoherent X)
    (e : (Stacks.Algebraization.completionFunctor X I).obj E.obj ≅
      ⟨idealPowerTowerModules I A, idealPowerTowerModules_isCoherentAdicSystem I A⟩) :
    ∃! η : (finiteLocallyFreeUnit X).obj ⟶ E.obj, ∀ n,
      η.hom ≫ Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n) =
        SheafOfModules.unitToPushforwardObjUnit
          ((finiteEtaleTowerOver (idealPowerInclusion I)
            (idealPowerInclusion_isThickening I) (fun k => (I ^ (k + 1)).subschemeι)
            (idealPowerInclusion_comp I) A).obj n).hom.toRingCatSheafHom := by
  let T := finiteEtaleTowerOver (idealPowerInclusion I)
    (idealPowerInclusion_isThickening I) (fun k => (I ^ (k + 1)).subschemeι)
    (idealPowerInclusion_comp I) A
  apply existsUnique_map_to_algebraizedSystem X I (finiteLocallyFreeUnit X) E _ e
  intro n
  exact (congrArg (_ ≫ ·) (pushforwardStructureSheafMap_tower_map I A n).symm).trans
    (pushforwardStructureSheafMap_unit (T.map (homOfLE (Nat.le_succ n))))

open scoped TensorProduct

private def sheafifyDesc {X : Scheme.{u}}
    {P : PresheafOfModules.{u} X.ringCatSheaf.obj} {E : X.Modules}
    (f : P ⟶ E.val) :
    (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace).obj P ⟶ E :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm f

private lemma sheafifyDesc_apply {X : Scheme.{u}}
    {P : PresheafOfModules.{u} X.ringCatSheaf.obj} {E : X.Modules}
    (f : P ⟶ E.val) (U : X.Opensᵒᵖ) (x : P.obj U) :
    (sheafifyDesc f).val.app U
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace P).app U x) =
        f.app U x :=
  congrArg (fun k => k.app U x)
    ((PresheafOfModules.sheafificationHomEquiv
      (𝟙 X.ringCatSheaf.obj)).apply_symm_apply f)

private def tensorMulPresheafMap {X Y : Scheme.{u}} (f : Y ⟶ X) (E : X.Modules)
    (p : E ⟶ Stacks.Morphisms.pushforwardStructureSheaf f) :
    (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (E.val) (E.val)) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf f).val where
  app U := by
    letI : Algebra Γ(X, U.unop) Γ(Y, f ⁻¹ᵁ U.unop) := (f.app U.unop).hom.toAlgebra
    let pU : E.val.obj U →ₗ[Γ(X, U.unop)] Γ(Y, f ⁻¹ᵁ U.unop) := (p.val.app U).hom
    change ModuleCat.of Γ(X, U.unop)
      (TensorProduct Γ(X, U.unop) (E.val.obj U) (E.val.obj U)) ⟶
        ModuleCat.of Γ(X, U.unop) Γ(Y, f ⁻¹ᵁ U.unop)
    exact ModuleCat.ofHom ((LinearMap.mul' Γ(X, U.unop) Γ(Y, f ⁻¹ᵁ U.unop)).comp
      (TensorProduct.map pU pU))
  naturality {U V} g := by
    letI : Algebra Γ(X, U.unop) Γ(Y, f ⁻¹ᵁ U.unop) := (f.app U.unop).hom.toAlgebra
    letI : Algebra Γ(X, V.unop) Γ(Y, f ⁻¹ᵁ V.unop) := (f.app V.unop).hom.toAlgebra
    ext t
    change TensorProduct Γ(X, U.unop) (E.val.obj U) (E.val.obj U) at t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul x y =>
      change Mul.mul (α := Γ(Y, f ⁻¹ᵁ V.unop))
        (p.val.app V (E.val.map g x)) (p.val.app V (E.val.map g y)) =
        (Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map g.unop).op).hom
          (Mul.mul (α := Γ(Y, f ⁻¹ᵁ U.unop)) (p.val.app U x) (p.val.app U y))
      exact (congrArg₂ (fun a b : Γ(Y, f ⁻¹ᵁ V.unop) => a * b)
        (PresheafOfModules.naturality_apply p.val g x)
        (PresheafOfModules.naturality_apply p.val g y)).trans
          (map_mul (Y.presheaf.map
            ((TopologicalSpace.Opens.map f.base).map g.unop).op).hom _ _).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

private def tensorMulSheafMap {X Y : Scheme.{u}} (f : Y ⟶ X) (E : X.Modules)
    (p : E ⟶ Stacks.Morphisms.pushforwardStructureSheaf f) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (E)) ⟶
      Stacks.Morphisms.pushforwardStructureSheaf f :=
  sheafifyDesc (tensorMulPresheafMap f E p)

private lemma tensorMulSheafMap_apply {X Y : Scheme.{u}} (f : Y ⟶ X) (E : X.Modules)
    (p : E ⟶ Stacks.Morphisms.pushforwardStructureSheaf f) (U : X.Opens)
    (x y : E.val.obj (op U)) :
    (tensorMulSheafMap f E p).val.app (op U)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace E E (op U)
        (x ⊗ₜ[Γ(X, U)] y)) =
        Mul.mul (α := Γ(Y, f ⁻¹ᵁ U)) (p.val.app (op U) x) (p.val.app (op U) y) :=
  sheafifyDesc_apply (tensorMulPresheafMap f E p) (op U) (x ⊗ₜ y)

private lemma tensorMulSheafMap_naturality {X : Scheme.{u}} {Y Z : Over X}
    (f : Y ⟶ Z) (E : X.Modules) (p : E ⟶ Stacks.Morphisms.pushforwardStructureSheaf Z.hom) :
    tensorMulSheafMap Z.hom E p ≫ pushforwardStructureSheafMap f =
      tensorMulSheafMap Y.hom E (p ≫ pushforwardStructureSheafMap f) := by
  apply Stacks.SheafOfModules.TensorStalkRingedSpace.hom_ext_toTensorSheafSection X.toRingedSpace
  intro U x y
  show (pushforwardStructureSheafMap f).app U.unop
    ((tensorMulSheafMap Z.hom E p).val.app U
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace E E U
        (x ⊗ₜ[Γ(X, U.unop)] y))) = _
  rw [tensorMulSheafMap_apply, tensorMulSheafMap_apply]
  show (pushforwardStructureSheafMap f).app U.unop
    (Mul.mul (α := Γ(Z.left, Z.hom ⁻¹ᵁ U.unop)) (p.val.app U x) (p.val.app U y)) =
      Mul.mul (α := Γ(Y.left, Y.hom ⁻¹ᵁ U.unop))
        ((pushforwardStructureSheafMap f).app U.unop (p.val.app U x))
        ((pushforwardStructureSheafMap f).app U.unop (p.val.app U y))
  rw [pushforwardStructureSheafMap_app]
  exact map_mul (f.left.appLE _ _ _).hom _ _

private theorem existsUnique_algebraizedTowerMul
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme)
    (E : FiniteLocallyFreeCoherent X)
    (e : (Stacks.Algebraization.completionFunctor X I).obj E.obj ≅
      ⟨idealPowerTowerModules I A, idealPowerTowerModules_isCoherentAdicSystem I A⟩) :
    ∃! μ : (finiteLocallyFreeTensor E E).obj ⟶ E.obj, ∀ n,
      μ.hom ≫ Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n) =
        tensorMulSheafMap
          ((finiteEtaleTowerOver (idealPowerInclusion I)
            (idealPowerInclusion_isThickening I) (fun k => (I ^ (k + 1)).subschemeι)
            (idealPowerInclusion_comp I) A).obj n).hom E.obj.obj
          (Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)) := by
  let T := finiteEtaleTowerOver (idealPowerInclusion I)
    (idealPowerInclusion_isThickening I) (fun k => (I ^ (k + 1)).subschemeι)
    (idealPowerInclusion_comp I) A
  apply existsUnique_map_to_algebraizedSystem X I (finiteLocallyFreeTensor E E) E _ e
  intro n
  have hp := completionProjection_iso_transition I E.obj _ e n
  change (Stacks.Algebraization.completionProjection X I E.obj (n + 1) ≫
    e.hom.hom.app (op (n + 1))) ≫
      (idealPowerTowerModules I A).map (homOfLE (Nat.le_succ n)).op = _ at hp
  rw [← pushforwardStructureSheafMap_tower_map] at hp
  exact (congrArg (_ ≫ ·) (pushforwardStructureSheafMap_tower_map I A n).symm).trans
    ((tensorMulSheafMap_naturality _ E.obj.obj _).trans
      (congrArg (tensorMulSheafMap _ E.obj.obj) hp))

open MonoidalCategory

/-- The monoidal structure on presheaves of modules over the structure sheaf of `X`, given by
the pointwise tensor product. -/
local instance (X : Scheme.{u}) :
    MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

/-- The symmetric monoidal structure on presheaves of modules over the structure sheaf of `X`,
given by the pointwise tensor product. -/
local instance (X : Scheme.{u}) :
    SymmetricCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  PresheafOfModules.symmetricCategory (R := X.presheaf)

private lemma presheafHom_ext_of_completion
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    {P : PresheafOfModules.{u} X.ringCatSheaf.obj}
    (hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace).obj P))
    (E : FiniteLocallyFreeCoherent X) (F : Stacks.Coherent.CoherentAdicSystems I)
    (e : (Stacks.Algebraization.completionFunctor X I).obj E.obj ≅ F)
    {f g : P ⟶ E.obj.obj.val}
    (hfg : ∀ n, f ≫ (Stacks.Algebraization.completionProjection X I E.obj n ≫
      e.hom.hom.app (op n)).val = g ≫
        (Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)).val) :
    f = g := by
  let := hP
  let D : FiniteLocallyFreeCoherent X :=
    ⟨⟨_, @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X _ _
      hP⟩, hP⟩
  have heq : sheafifyDesc f = sheafifyDesc g := by
    apply hom_ext_of_completionProjection_iso X I (E := D) F e
    intro n
    apply (PresheafOfModules.sheafificationHomEquiv
      (𝟙 X.ringCatSheaf.obj)).injective
    ext U x
    show (Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)).val.app U
        ((sheafifyDesc f).val.app U
          ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace P).app U x)) =
      (Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)).val.app U
        ((sheafifyDesc g).val.app U
          ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace P).app U x))
    let φ := ConcreteCategory.hom
      ((Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)).val.app U)
    exact (DFunLike.congr_arg φ (sheafifyDesc_apply f U x)).trans
      ((congrArg (fun k => k.app U x) (hfg n)).trans
        (DFunLike.congr_arg φ (sheafifyDesc_apply g U x)).symm)
  exact (PresheafOfModules.sheafificationHomEquiv
    (𝟙 X.ringCatSheaf.obj)).symm.injective heq

private lemma finiteLocallyFree_sheafify_triple {X : Scheme.{u}}
    (E F G : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace).obj
        ((E.val ⊗ F.val) ⊗ G.val)) := by
  let L := Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf X.ringCatSheaf.2
  let q := Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf X.ringCatSheaf.2
    (E.val ⊗ F.val)
  have : IsIso (L.map (q ▷ G.val)) :=
    Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight X.presheaf
      X.ringCatSheaf.2 q G.val
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify X.presheaf
        X.ringCatSheaf.2 _)
  exact finiteLocallyFree_of_iso (asIso (L.map (q ▷ G.val))).symm
    (tensorSheaf_finiteLocallyFree _ _ (tensorSheaf_finiteLocallyFree E F hE hF) hG)

private lemma finiteLocallyFree_sheafify_val {X : Scheme.{u}} (E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace).obj
        E.val) := by
  let a := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have : IsIso (a.counit.app E) := NatIso.isIso_app_of_isIso a.counit E
  exact finiteLocallyFree_of_iso (asIso (a.counit.app E)).symm hE

section algebraLaws

/-- The module structure on sections at the `X.presheaf ⋙ forget₂ _ _` spelling of the ring of
sections, which is how the monoidal structure on presheaves of modules writes it. -/
local instance sectionsModuleForgetPresheaf {X : Scheme.{u}} (M : X.Modules) (U : X.Opensᵒᵖ) :
    Module ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (M.val.obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))

private lemma algebraLaws_of_separating_homs {X : Scheme.{u}}
    (E : X.Modules) (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (T : ℕ → Over X) (p : ∀ n, E ⟶ Stacks.Morphisms.pushforwardStructureSheaf (T n).hom)
    (hext : ∀ (P : PresheafOfModules.{u} X.ringCatSheaf.obj),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace).obj P) →
      ∀ f g : P ⟶ E.val, (∀ n, f ≫ (p n).val = g ≫ (p n).val) → f = g)
    (η : SheafOfModules.unit X.ringCatSheaf ⟶ E)
    (m : E.val ⊗ E.val ⟶ E.val)
    (hη : ∀ n U, (p n).val.app U (η.val.app U (1 : Γ(X, U.unop))) =
      (1 : Γ((T n).left, (T n).hom ⁻¹ᵁ U.unop)))
    (hm : ∀ n U (x y : E.val.obj U),
      (p n).val.app U (m.app U (x ⊗ₜ[Γ(X, U.unop)] y)) =
        Mul.mul (α := Γ((T n).left, (T n).hom ⁻¹ᵁ U.unop))
          ((p n).val.app U x) ((p n).val.app U y)) :
    (∀ U (x y : E.val.obj U),
      m.app U (x ⊗ₜ[Γ(X, U.unop)] y) = m.app U (y ⊗ₜ[Γ(X, U.unop)] x)) ∧
    (∀ U (x y z : E.val.obj U),
      m.app U (m.app U (x ⊗ₜ[Γ(X, U.unop)] y) ⊗ₜ[Γ(X, U.unop)] z) =
        m.app U (x ⊗ₜ[Γ(X, U.unop)] m.app U (y ⊗ₜ[Γ(X, U.unop)] z))) ∧
    (∀ U (x : E.val.obj U), m.app U
      (η.val.app U (1 : Γ(X, U.unop)) ⊗ₜ[Γ(X, U.unop)] x) = x) := by
  have hc : m = (β_ E.val E.val).hom ≫ m := by
    apply hext (E.val ⊗ E.val) (tensorSheaf_finiteLocallyFree E E hE hE)
    intro n
    ext U t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    | tmul x y =>
      show (p n).val.app U (m.app U (x ⊗ₜ[Γ(X, U.unop)] y)) =
        (p n).val.app U (m.app U (y ⊗ₜ[Γ(X, U.unop)] x))
      rw [hm, hm]
      exact @mul_comm Γ((T n).left, (T n).hom ⁻¹ᵁ U.unop) inferInstance _ _
  have ha : (m ▷ E.val) ≫ m =
      (α_ E.val E.val E.val).hom ≫ (E.val ◁ m) ≫ m := by
    apply hext _ (finiteLocallyFree_sheafify_triple E E E hE hE hE)
    intro n
    ext U t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    | tmul t z =>
      induction t using TensorProduct.induction_on with
      | zero =>
        exact (DFunLike.congr_arg (((m ▷ E.val ≫ m) ≫ (p n).val).app U).hom
          (TensorProduct.zero_tmul _ z)).trans ((map_zero _).trans ((map_zero _).symm.trans
            (DFunLike.congr_arg ((((α_ E.val E.val E.val).hom ≫ E.val ◁ m ≫ m) ≫
              (p n).val).app U).hom (TensorProduct.zero_tmul _ z)).symm))
      | add x y hx hy =>
        let F := (((m ▷ E.val ≫ m) ≫ (p n).val).app U).hom
        let G := ((((α_ E.val E.val E.val).hom ≫ E.val ◁ m ≫ m) ≫ (p n).val).app U).hom
        have h1 := DFunLike.congr_arg F (TensorProduct.add_tmul x y z)
        have h2 := DFunLike.congr_arg G (TensorProduct.add_tmul x y z)
        exact h1.trans ((F.map_add _ _).trans ((congrArg₂ (· + ·) hx hy).trans
          ((G.map_add _ _).symm.trans h2.symm)))
      | tmul x y =>
        show (p n).val.app U (m.app U
          (m.app U (x ⊗ₜ[Γ(X, U.unop)] y) ⊗ₜ[Γ(X, U.unop)] z)) =
            (p n).val.app U (m.app U
              (x ⊗ₜ[Γ(X, U.unop)] m.app U (y ⊗ₜ[Γ(X, U.unop)] z)))
        rw [hm, hm, hm, hm]
        exact @mul_assoc Γ((T n).left, (T n).hom ⁻¹ᵁ U.unop) inferInstance _ _ _
  have hu : (λ_ E.val).inv ≫ (η.val ⊗ₘ 𝟙 E.val) ≫ m = 𝟙 E.val := by
    apply hext _ (finiteLocallyFree_sheafify_val E hE)
    intro n
    ext U x
    show (p n).val.app U (m.app U
      (η.val.app U (1 : Γ(X, U.unop)) ⊗ₜ[Γ(X, U.unop)] x)) = (p n).val.app U x
    rw [hm, hη]
    exact @one_mul Γ((T n).left, (T n).hom ⁻¹ᵁ U.unop) inferInstance _
  refine ⟨?_, ?_, ?_⟩
  · intro U x y
    exact congrArg (fun k => k.app U (x ⊗ₜ[Γ(X, U.unop)] y)) hc
  · intro U x y z
    exact congrArg (fun k => k.app U
      ((x ⊗ₜ[Γ(X, U.unop)] y) ⊗ₜ[Γ(X, U.unop)] z)) ha
  · intro U x
    exact congrArg (fun k => k.app U x) hu

end algebraLaws

private structure ModuleAlgebraData {X : Scheme.{u}} (E : X.Modules) where
  unit : SheafOfModules.unit X.ringCatSheaf ⟶ E
  mul : E.val ⊗ E.val ⟶ E.val
  mul_comm : ∀ U (x y : E.val.obj U),
      mul.app U (x ⊗ₜ[Γ(X, U.unop)] y) = mul.app U (y ⊗ₜ[Γ(X, U.unop)] x)
  mul_assoc : ∀ U (x y z : E.val.obj U),
      mul.app U (mul.app U (x ⊗ₜ[Γ(X, U.unop)] y) ⊗ₜ[Γ(X, U.unop)] z) =
        mul.app U (x ⊗ₜ[Γ(X, U.unop)] mul.app U (y ⊗ₜ[Γ(X, U.unop)] z))
  one_mul : ∀ U (x : E.val.obj U), mul.app U
      (unit.val.app U (1 : Γ(X, U.unop)) ⊗ₜ[Γ(X, U.unop)] x) = x

@[instance_reducible] private def moduleSectionCommRing {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E)
    (U : X.Opensᵒᵖ) : CommRing (E.val.obj U) where
  __ := (inferInstance : AddCommGroup (E.val.obj U))
  one := d.unit.val.app U (1 : Γ(X, U.unop))
  mul x y := d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] y)
  mul_assoc := d.mul_assoc U
  mul_comm := d.mul_comm U
  one_mul := d.one_mul U
  mul_one x := (d.mul_comm U _ _).trans (d.one_mul U x)
  left_distrib x y z := by
    change d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] (y + z)) = _
    exact (congrArg (fun t => d.mul.app U t)
      (TensorProduct.tmul_add (R := Γ(X, U.unop)) x y z)).trans
      ((d.mul.app U).hom.map_add _ _)
  right_distrib x y z := by
    change d.mul.app U ((x + y) ⊗ₜ[Γ(X, U.unop)] z) = _
    exact (congrArg (fun t => d.mul.app U t)
      (TensorProduct.add_tmul (R := Γ(X, U.unop)) x y z)).trans
      ((d.mul.app U).hom.map_add _ _)
  zero_mul x := by
    change d.mul.app U (0 ⊗ₜ[Γ(X, U.unop)] x) = _
    exact (congrArg (fun t => d.mul.app U t) (TensorProduct.zero_tmul _ _)).trans
      ((d.mul.app U).hom.map_zero)
  mul_zero x := by
    change d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] 0) = _
    exact (congrArg (fun t => d.mul.app U t) (TensorProduct.tmul_zero _ _)).trans
      ((d.mul.app U).hom.map_zero)
  natCast n := n • d.unit.val.app U (1 : Γ(X, U.unop))
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast z := z • d.unit.val.app U (1 : Γ(X, U.unop))
  intCast_ofNat n := natCast_zsmul _ _
  intCast_negSucc n := negSucc_zsmul _ _

private def algebraPresheafOfModule {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E) :
    X.Opensᵒᵖ ⥤ CommRingCat.{u} := by
  letI (U : X.Opensᵒᵖ) := moduleSectionCommRing E d U
  exact
    { obj U := CommRingCat.of (E.val.obj U)
      map f := CommRingCat.ofHom
        { __ := (E.val.map f).hom.toAddMonoidHom
          map_one' := by
            exact (PresheafOfModules.naturality_apply d.unit.val f
              (1 : Γ(X, _))).symm.trans (by
                change d.unit.val.app _ ((X.presheaf.map f).hom 1) =
                  d.unit.val.app _ (1 : Γ(X, _))
                exact congrArg (fun t => d.unit.val.app _ t)
                  ((X.presheaf.map f).hom.map_one))
          map_mul' x y := by
            exact (PresheafOfModules.naturality_apply d.mul f
              (x ⊗ₜ[Γ(X, _)] y)).symm }
      map_id U := by ext x; exact congrArg (fun f => f x) (E.val.map_id U)
      map_comp f g := by ext x; exact E.val.map_comp_apply f g x }

@[instance_reducible] private def moduleSectionAlgebra {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E) (U : X.Opensᵒᵖ) :
    letI := moduleSectionCommRing E d U
    Algebra Γ(X, U.unop) (E.val.obj U) := by
  letI := moduleSectionCommRing E d U
  exact Algebra.ofModule
    (fun r x y => by
      change d.mul.app U ((r • x) ⊗ₜ[Γ(X, U.unop)] y) =
        r • d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] y)
      exact (congrArg (fun t => d.mul.app U t)
        (TensorProduct.smul_tmul' (R := Γ(X, U.unop)) r x y).symm).trans
        ((d.mul.app U).hom.map_smul r _))
    (fun r x y => by
      change d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] (r • y)) =
        r • d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] y)
      exact (congrArg (fun t => d.mul.app U t)
        (TensorProduct.tmul_smul (R := Γ(X, U.unop)) r x y)).trans
        ((d.mul.app U).hom.map_smul r _))

private lemma moduleSectionAlgebra_map {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E) (U : X.Opensᵒᵖ) (r : Γ(X, U.unop)) :
    letI := moduleSectionCommRing E d U
    letI := moduleSectionAlgebra E d U
    algebraMap Γ(X, U.unop) (E.val.obj U) r = d.unit.val.app U r := by
  show r • d.unit.val.app U (1 : Γ(X, U.unop)) = d.unit.val.app U r
  exact ((d.unit.val.app U).hom.map_smul r (1 : Γ(X, U.unop))).symm.trans
    (congrArg (fun t => d.unit.val.app U t) (mul_one r))

private def algebraSheafOfModule {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E) : Stacks.RelativeSpec.AlgebraSheaf X := by
  letI (U : X.Opensᵒᵖ) := moduleSectionCommRing E d U
  letI (U : X.Opensᵒᵖ) := moduleSectionAlgebra E d U
  let A : TopCat.Sheaf CommRingCat X :=
    ⟨algebraPresheafOfModule E d,
      (Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X)
        (algebraPresheafOfModule E d)
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).mpr E.isSheaf⟩
  exact Under.mk (Y := A) ⟨
    { app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) (E.val.obj U))
      naturality {U V} f := by
        ext r
        change algebraMap Γ(X, V.unop) (E.val.obj V) ((X.presheaf.map f).hom r) =
          E.val.map f (algebraMap Γ(X, U.unop) (E.val.obj U) r)
        rw [moduleSectionAlgebra_map]
        exact (PresheafOfModules.naturality_apply d.unit.val f r).trans
          (congrArg (fun t => E.val.map f t) (moduleSectionAlgebra_map E d U r).symm) }⟩

private def algebraSheafOfModuleIso {X : Scheme.{u}} (E : X.Modules)
    (d : ModuleAlgebraData E) :
    (algebraSheafOfModule E d).underlyingModule ≅ E := by
  letI (U : X.Opensᵒᵖ) := moduleSectionCommRing E d U
  letI (U : X.Opensᵒᵖ) := moduleSectionAlgebra E d U
  let e (U : X.Opensᵒᵖ) :
      ((algebraSheafOfModule E d).underlyingModule.val.obj U) ≃ₗ[Γ(X, U.unop)]
        E.val.obj U :=
    { toFun := id
      invFun := id
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' r x := by
        change Mul.mul (α := E.val.obj U) (algebraMap Γ(X, U.unop) (E.val.obj U) r)
          x = @SMul.smul Γ(X, U.unop) (E.val.obj U)
            (E.val.obj U).isModule.toDistribMulAction.toSMul r x
        exact @Algebra.smul_def Γ(X, U.unop) (E.val.obj U) _ _ _ r x |>.symm }
  exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso (PresheafOfModules.isoMk
    (fun U => (e U).toModuleIso) (fun {_ _} f => by ext x; rfl))

private lemma algebraSheafOfModule_isQuasicoherent {X : Scheme.{u}}
    (E : X.Modules) [E.IsQuasicoherent] (d : ModuleAlgebraData E) :
    (algebraSheafOfModule E d).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (algebraSheafOfModuleIso E d).symm inferInstance

private abbrev idealPowerTowerOver {X : Scheme.{u}} (I : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) :=
  finiteEtaleTowerOver (idealPowerInclusion I) (idealPowerInclusion_isThickening I)
    (fun k => (I ^ (k + 1)).subschemeι) (idealPowerInclusion_comp I) A

private theorem exists_algebraizedTowerData
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme)
    (E : FiniteLocallyFreeCoherent X)
    (e : (Stacks.Algebraization.completionFunctor X I).obj E.obj ≅
      ⟨idealPowerTowerModules I A, idealPowerTowerModules_isCoherentAdicSystem I A⟩) :
    ∃ d : ModuleAlgebraData E.obj.obj, ∀ n,
      let p := Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)
      (∀ U, p.val.app U (d.unit.val.app U (1 : Γ(X, U.unop))) =
        (1 : Γ(((idealPowerTowerOver I A).obj n).left,
          ((idealPowerTowerOver I A).obj n).hom ⁻¹ᵁ U.unop))) ∧
      (∀ U (x y : E.obj.obj.val.obj U),
        p.val.app U (d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] y)) =
          Mul.mul (α := Γ(((idealPowerTowerOver I A).obj n).left,
            ((idealPowerTowerOver I A).obj n).hom ⁻¹ᵁ U.unop))
            (p.val.app U x) (p.val.app U y)) := by
  obtain ⟨η, hη, -⟩ := existsUnique_algebraizedTowerUnit X I A E e
  obtain ⟨μ, hμ, -⟩ := existsUnique_algebraizedTowerMul X I A E e
  let m : E.obj.obj.val ⊗ E.obj.obj.val ⟶ E.obj.obj.val :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)) μ.hom
  let T := idealPowerTowerOver I A
  let p (n : ℕ) : E.obj.obj ⟶ Stacks.Morphisms.pushforwardStructureSheaf (T.obj n).hom :=
    Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)
  have hunit (n : ℕ) (U : X.Opensᵒᵖ) :
      (p n).val.app U (η.hom.val.app U (1 : Γ(X, U.unop))) =
        (1 : Γ((T.obj n).left, (T.obj n).hom ⁻¹ᵁ U.unop)) := by
    have hh := congrArg (fun k => k.val.app U (1 : Γ(X, U.unop))) (hη n)
    exact hh.trans (map_one ((T.obj n).hom.app U.unop).hom)
  have hmul (n : ℕ) (U : X.Opensᵒᵖ) (x y : E.obj.obj.val.obj U) :
      (p n).val.app U (m.app U (x ⊗ₜ[Γ(X, U.unop)] y)) =
        Mul.mul (α := Γ((T.obj n).left, (T.obj n).hom ⁻¹ᵁ U.unop))
          ((p n).val.app U x) ((p n).val.app U y) := by
    have hh := congrArg (fun k => k.val.app U
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
        E.obj.obj E.obj.obj U
        (x ⊗ₜ[Γ(X, U.unop)] y))) (hμ n)
    exact hh.trans (tensorMulSheafMap_apply (T.obj n).hom E.obj.obj (p n) U.unop x y)
  obtain ⟨hc, ha, hu⟩ := algebraLaws_of_separating_homs E.obj.obj E.property T.obj p
    (fun P hP f g hh => presheafHom_ext_of_completion X I hP E _ e hh)
    η.hom m hunit hmul
  exact ⟨⟨η.hom, m, hc, ha, hu⟩, fun n => ⟨hunit n, hmul n⟩⟩

private def algebraUnderlyingFunctor (X : Scheme.{u}) :
    Stacks.RelativeSpec.AlgebraSheaf X ⥤ X.Modules where
  obj A := A.underlyingModule
  map {A B} f := ⟨
    { app U := ModuleCat.ofHom (R := X.ringCatSheaf.obj.obj U)
        (X := A.underlyingModule.val.obj U) (Y := B.underlyingModule.val.obj U)
        { toFun := fun x => (f.right.hom.app U).hom x
          map_add' := (f.right.hom.app U).hom.map_add
          map_smul' r x := by
            change (f.right.hom.app U).hom
                (Mul.mul (α := A.right.obj.obj U) ((A.hom.hom.app U).hom r) x) =
              Mul.mul (α := B.right.obj.obj U)
                ((B.hom.hom.app U).hom r) ((f.right.hom.app U).hom x)
            exact ((f.right.hom.app U).hom.map_mul _ _).trans
              (congrArg (fun a => Mul.mul (α := B.right.obj.obj U) a
                ((f.right.hom.app U).hom x))
                (congrArg (fun k => (k.hom.app U).hom r) (Under.w f))) }
      naturality {U V} g := by
        ext x
        exact congrArg (fun k => k.hom x) (f.right.hom.naturality g) }⟩
  map_id A := by ext U x; rfl
  map_comp f g := by ext U x; rfl

private def pushforwardAlgebraUnderlyingIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).underlyingModule ≅
      Stacks.Morphisms.pushforwardStructureSheaf f := Iso.refl _

private theorem exists_affineOver_algebraIso {X : Scheme.{u}}
    (A : Stacks.RelativeSpec.AlgebraSheaf X) (hA : A.IsQuasicoherent) :
    ∃ V : AlgebraicGeometry.AffineOver X,
      Nonempty (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra V.obj.hom ≅ A) := by
  let e := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.equivalence X
  let C : Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra X := ⟨A, hA⟩
  let V := (e.inverse.obj C).unop
  exact ⟨V, ⟨(Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X V).symm ≪≫
    (ObjectProperty.ι (P := Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebra X)).mapIso
      (e.counitIso.app C)⟩⟩

private def algebraSheafOfModuleToPushforward {X Y : Scheme.{u}}
    (E : X.Modules) (d : ModuleAlgebraData E) (f : Y ⟶ X)
    (p : E ⟶ Stacks.Morphisms.pushforwardStructureSheaf f)
    (hu : ∀ U, p.val.app U (d.unit.val.app U (1 : Γ(X, U.unop))) =
      (1 : Γ(Y, f ⁻¹ᵁ U.unop)))
    (hm : ∀ U (x y : E.val.obj U),
      p.val.app U (d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] y)) =
        Mul.mul (α := Γ(Y, f ⁻¹ᵁ U.unop)) (p.val.app U x) (p.val.app U y)) :
    algebraSheafOfModule E d ⟶ Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f := by
  letI (U : X.Opensᵒᵖ) := moduleSectionCommRing E d U
  letI (U : X.Opensᵒᵖ) := moduleSectionAlgebra E d U
  let q : (algebraSheafOfModule E d).right ⟶
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebra f).right := ⟨
    { app U := CommRingCat.ofHom (R := E.val.obj U) (S := Γ(Y, f ⁻¹ᵁ U.unop))
        { toFun := fun x => p.val.app U x
          map_zero' := (p.val.app U).hom.map_zero
          map_add' := (p.val.app U).hom.map_add
          map_one' := hu U
          map_mul' := hm U }
      naturality {U V} g := by
        ext x
        exact PresheafOfModules.naturality_apply p.val g x }⟩
  refine Under.homMk q ?_
  apply ObjectProperty.hom_ext
  ext U r
  change p.val.app U (algebraMap Γ(X, U.unop) (E.val.obj U) r) =
    (f.app U.unop).hom r
  obtain ⟨r, rfl⟩ : ∃ r' : Γ(X, U.unop), r' = r := ⟨r, rfl⟩
  refine (congrArg (fun t => p.val.app U t) (moduleSectionAlgebra_map E d U r)).trans ?_
  refine (congrArg (fun t => p.val.app U (d.unit.val.app U t)) (mul_one r).symm).trans ?_
  refine (congrArg (fun t => p.val.app U t)
    ((d.unit.val.app U).hom.map_smul r (1 : Γ(X, U.unop)))).trans ?_
  refine ((p.val.app U).hom.map_smul r _).trans ?_
  refine (congrArg (fun t => r • t) (hu U)).trans ?_
  exact mul_one ((f.app U.unop).hom r)

private lemma algebraSheafOfModuleToPushforward_underlying {X Y : Scheme.{u}}
    (E : X.Modules) (d : ModuleAlgebraData E) (f : Y ⟶ X)
    (p : E ⟶ Stacks.Morphisms.pushforwardStructureSheaf f)
    (hu : ∀ U, p.val.app U (d.unit.val.app U (1 : Γ(X, U.unop))) =
      (1 : Γ(Y, f ⁻¹ᵁ U.unop)))
    (hm : ∀ U (x y : E.val.obj U),
      p.val.app U (d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] y)) =
        Mul.mul (α := Γ(Y, f ⁻¹ᵁ U.unop)) (p.val.app U x) (p.val.app U y)) :
    (algebraUnderlyingFunctor X).map (algebraSheafOfModuleToPushforward E d f p hu hm) ≫
        (pushforwardAlgebraUnderlyingIso f).hom =
      (algebraSheafOfModuleIso E d).hom ≫ p := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  have h1 : ((algebraUnderlyingFunctor X).map
      (algebraSheafOfModuleToPushforward E d f p hu hm)).val.app U x = (p.val.app U).hom x := rfl
  have h2 : ((algebraSheafOfModuleIso E d).hom).val.app U x = x := by
    unfold algebraSheafOfModuleIso
    exact rfl
  show (pushforwardAlgebraUnderlyingIso f).hom.val.app U
      (((algebraUnderlyingFunctor X).map
        (algebraSheafOfModuleToPushforward E d f p hu hm)).val.app U x) =
    p.val.app U ((algebraSheafOfModuleIso E d).hom.val.app U x)
  rw [h2]
  exact h1

private theorem exists_affineHom_of_algebraHom {X : Scheme.{u}}
    (V W : AlgebraicGeometry.AffineOver X)
    (q : Stacks.AffineAlgebraEquivalence.pushforwardAlgebra W.obj.hom ⟶
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebra V.obj.hom) :
    ∃ f : V ⟶ W, Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f.hom = q := by
  let e := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.equivalence X
  let iV := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X V
  let iW := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X W
  let q' : e.functor.obj (op W) ⟶ e.functor.obj (op V) :=
    ObjectProperty.homMk (iW.hom ≫ q ≫ iV.inv)
  let f : V ⟶ W := (e.functor.preimage q').unop
  refine ⟨f, ?_⟩
  have hf := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso_naturality X f
  change (ObjectProperty.ι (P := Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebra X)).map
      (e.functor.map f.op) ≫ iV.hom =
    iW.hom ≫ Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f.hom at hf
  have hq : e.functor.map f.op = q' := e.functor.map_preimage q'
  rw [hq] at hf
  apply (cancel_epi iW.hom).mp
  simpa only [ObjectProperty.ι_map, q', ObjectProperty.homMk_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using hf.symm

private lemma pushforwardAlgebraMap_app {X : Scheme.{u}} {Y Z : Over X}
    (f : Y ⟶ Z) (U : X.Opens) :
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f).right.hom.app (op U) =
      f.left.appLE (Z.hom ⁻¹ᵁ U) (Y.hom ⁻¹ᵁ U)
        (by rw [← Scheme.Hom.comp_preimage, Over.w f]) := by
  obtain ⟨Y, a, rfl⟩ := Over.mk_surjective Y
  obtain ⟨Z, b, rfl⟩ := Over.mk_surjective Z
  obtain ⟨f, w, rfl⟩ := Over.homMk_surjective f
  change Y ⟶ Z at f
  change f ≫ b = a at w
  subst a
  simp only [Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap, Over.homMk_left, Over.mk_hom]
  show f.app (b ⁻¹ᵁ U) = f.appLE (b ⁻¹ᵁ U) ((f ≫ b) ⁻¹ᵁ U) _
  exact Scheme.Hom.app_eq_appLE f

private lemma pushforwardAlgebraMap_underlying {X : Scheme.{u}} {Y Z : Over X}
    (f : Y ⟶ Z) :
    (algebraUnderlyingFunctor X).map (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f) ≫
        (pushforwardAlgebraUnderlyingIso Y.hom).hom =
      (pushforwardAlgebraUnderlyingIso Z.hom).hom ≫ pushforwardStructureSheafMap f := by
  ext U x
  show ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f).right.hom.app (op U)).hom x =
    (pushforwardStructureSheafMap f).app U x
  rw [pushforwardAlgebraMap_app, pushforwardStructureSheafMap_app]
  rfl

private lemma algebraUnderlyingFunctor_reflects_isIso {X : Scheme.{u}}
    {A B : Stacks.RelativeSpec.AlgebraSheaf X} (f : A ⟶ B)
    [IsIso ((algebraUnderlyingFunctor X).map f)] : IsIso f := by
  have (U : X.Opensᵒᵖ) : IsIso (f.right.hom.app U) := by
    let L := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj U
    let i := asIso ((algebraUnderlyingFunctor X).map f)
    have : IsIso (L.map ((algebraUnderlyingFunctor X).map f)) := (L.mapIso i).isIso_hom
    apply (ConcreteCategory.isIso_iff_bijective (f.right.hom.app U)).mpr
    exact ConcreteCategory.bijective_of_isIso (L.map ((algebraUnderlyingFunctor X).map f))
  have : IsIso f.right.hom := NatIso.isIso_of_isIso_app _
  let e : A.right ≅ B.right := ObjectProperty.isoMk _ (asIso f.right.hom)
  have : IsIso f.right := inferInstanceAs (IsIso e.hom)
  have : IsIso ((Under.forget X.sheaf).map f) := inferInstanceAs (IsIso f.right)
  exact isIso_of_reflects_iso f (Under.forget X.sheaf)

private lemma affineHom_ext_of_pushforwardStructureSheafMap
    {X : Scheme.{u}} {A B : Over X} [IsAffineHom A.hom] [IsAffineHom B.hom]
    {f g : A ⟶ B} (hfg : pushforwardStructureSheafMap f = pushforwardStructureSheafMap g) :
    f = g := by
  have ha : Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f =
      Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap g := by
    apply (Under.forget _).map_injective
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    ext x
    have h := congrArg (fun k => (k.val.app U).hom x) hfg
    change (pushforwardStructureSheafMap f).app U.unop x =
      (pushforwardStructureSheafMap g).app U.unop x at h
    rw [pushforwardStructureSheafMap_app, pushforwardStructureSheafMap_app] at h
    show ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f).right.hom.app U).hom x =
      ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap g).right.hom.app U).hom x
    rw [pushforwardAlgebraMap_app, pushforwardAlgebraMap_app]
    exact h
  let A' : AlgebraicGeometry.AffineOver X := ⟨A, inferInstance⟩
  let B' : AlgebraicGeometry.AffineOver X := ⟨B, inferInstance⟩
  let f' : A' ⟶ B' := ObjectProperty.homMk f
  let g' : A' ⟶ B' := ObjectProperty.homMk g
  let e := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.equivalence X
  let iA := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X A'
  let L := ObjectProperty.ι (P := Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebra X)
  have he : f'.op = g'.op := by
    apply e.functor.map_injective
    apply L.map_injective
    apply (cancel_mono iA.hom).mp
    rw [Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso_naturality X f',
      Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso_naturality X g']
    exact congrArg (fun k =>
      (Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X B').hom ≫ k) ha
  exact congrArg (fun k : op B' ⟶ op A' => k.unop.hom) he

private theorem exists_towerMaps_of_algebraizedData
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme)
    (E : FiniteLocallyFreeCoherent X)
    (e : (Stacks.Algebraization.completionFunctor X I).obj E.obj ≅
      ⟨idealPowerTowerModules I A, idealPowerTowerModules_isCoherentAdicSystem I A⟩)
    (d : ModuleAlgebraData E.obj.obj)
    (hd : ∀ n,
      let p := Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)
      (∀ U, p.val.app U (d.unit.val.app U (1 : Γ(X, U.unop))) =
        (1 : Γ(((idealPowerTowerOver I A).obj n).left,
          ((idealPowerTowerOver I A).obj n).hom ⁻¹ᵁ U.unop))) ∧
      (∀ U (x y : E.obj.obj.val.obj U),
        p.val.app U (d.mul.app U (x ⊗ₜ[Γ(X, U.unop)] y)) =
          Mul.mul (α := Γ(((idealPowerTowerOver I A).obj n).left,
            ((idealPowerTowerOver I A).obj n).hom ⁻¹ᵁ U.unop))
            (p.val.app U x) (p.val.app U y)))
    (V : AlgebraicGeometry.AffineOver X)
    (eV : Stacks.AffineAlgebraEquivalence.pushforwardAlgebra V.obj.hom ≅
      algebraSheafOfModule E.obj.obj d) :
    let eM := (pushforwardAlgebraUnderlyingIso V.obj.hom).symm ≪≫
      (algebraUnderlyingFunctor X).mapIso eV ≪≫ algebraSheafOfModuleIso E.obj.obj d
    ∃ g : ∀ n, (idealPowerTowerOver I A).obj n ⟶ V.obj, ∀ n,
      pushforwardStructureSheafMap (g n) =
        eM.hom ≫ Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n) := by
  let T := idealPowerTowerOver I A
  have ha (n : ℕ) : IsAffineHom (T.obj n).hom :=
    have : IsFinite (T.obj n).hom := isFinite_finiteEtaleTower_comp I A n
    inferInstance
  let W (n : ℕ) : AlgebraicGeometry.AffineOver X := ⟨T.obj n, ha n⟩
  let p (n : ℕ) := Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom.hom.app (op n)
  let q (n : ℕ) := algebraSheafOfModuleToPushforward E.obj.obj d (T.obj n).hom
    (p n) (hd n).1 (hd n).2
  choose g hg using fun n => exists_affineHom_of_algebraHom (W n) V (eV.hom ≫ q n)
  refine ⟨fun n => (g n).hom, ?_⟩
  intro n
  apply (cancel_epi (pushforwardAlgebraUnderlyingIso V.obj.hom).hom).mp
  rw [← pushforwardAlgebraMap_underlying, hg, Functor.map_comp]
  let iV := pushforwardAlgebraUnderlyingIso V.obj.hom
  let w := (algebraUnderlyingFunctor X).map eV.hom ≫ (algebraSheafOfModuleIso E.obj.obj d).hom
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => (algebraUnderlyingFunctor X).map eV.hom ≫ k)
    (algebraSheafOfModuleToPushforward_underlying E.obj.obj d (T.obj n).hom (p n)
      (hd n).1 (hd n).2)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (Iso.hom_inv_id_assoc iV (w ≫ p n)).symm.trans ?_
  exact congrArg (fun k => iV.hom ≫ k) (Category.assoc iV.inv w (p n)).symm

private lemma quotientIso_of_completionIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (M E : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (eM : M ≅ E) (F : Stacks.Coherent.CoherentAdicSystems I)
    (e : (Stacks.Algebraization.completionFunctor X I).obj E ≅ F) (n : ℕ) :
    ∃ eQ : Stacks.Algebraization.idealPowerQuotient I (n + 1) M.obj ≅ F.obj.obj (op n),
      cokernel.π (Stacks.Algebraization.idealPowerMultiple I (n + 1) M.obj).ι ≫ eQ.hom =
        eM.hom.hom ≫ Stacks.Algebraization.completionProjection X I E n ≫ e.hom.hom.app (op n) := by
  let eC := (Stacks.Algebraization.completionFunctor X I).mapIso eM ≪≫ e
  let eQ := (eqToIso (Stacks.Algebraization.completionFunctor_obj X I M n)).symm ≪≫
    ((ObjectProperty.ι (P := Stacks.Coherent.IsCoherentAdicSystem I)).mapIso eC).app (op n)
  refine ⟨eQ, ?_⟩
  show Stacks.Algebraization.completionProjection X I M n ≫
    (((Stacks.Algebraization.completionFunctor X I).map eM.hom).hom.app (op n) ≫
      e.hom.hom.app (op n)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom.hom.app (op n))
      (Stacks.Algebraization.completionFunctor_map_quotient X I eM.hom n)).trans
      (Category.assoc _ _ _))

private lemma pushforwardStructureSheafMap_quotient_of_isPullback
    {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {Y Z : Over X} (f : Y ⟶ Z) [IsAffineHom Z.hom]
    (g : Y.left ⟶ (I ^ (n + 1)).subscheme)
    (H : IsPullback f.left g Z.hom (I ^ (n + 1)).subschemeι) :
    ∃ eQ : Stacks.Algebraization.idealPowerQuotient I (n + 1)
        (Stacks.Morphisms.pushforwardStructureSheaf Z.hom) ≅
          Stacks.Morphisms.pushforwardStructureSheaf Y.hom,
      cokernel.π (Stacks.Algebraization.idealPowerMultiple I (n + 1)
        (Stacks.Morphisms.pushforwardStructureSheaf Z.hom)).ι ≫ eQ.hom =
          pushforwardStructureSheafMap f := by
  let : IsClosedImmersion f.left := MorphismProperty.of_isPullback H.flip inferInstance
  apply idealPowerQuotient_iso_of_affine I (n + 1) (pushforwardStructureSheafMap f)
    (pushforwardStructureSheafMap_surjective_affine f)
  intro U
  rw [pushforwardStructureSheafMap_ker_of_isPullback f _ g H U,
    Scheme.IdealSheafData.ker_subschemeι_app]
  rfl

private lemma isIso_of_cokernel_comparison {C : Type*} [Category C]
    [HasZeroMorphisms C] {M N P Q : C} (a : M ⟶ N) [HasCokernel a]
    (f : N ⟶ P) (g : N ⟶ Q) (k : P ⟶ Q) (h : f ≫ k = g)
    (eP : cokernel a ≅ P) (heP : cokernel.π a ≫ eP.hom = f)
    (eQ : cokernel a ≅ Q) (heQ : cokernel.π a ≫ eQ.hom = g) : IsIso k := by
  have hk : eP.hom ≫ k = eQ.hom := by
    apply (cancel_epi (cokernel.π a)).mp
    rw [← Category.assoc, heP, heQ, h]
  have : k = eP.inv ≫ eQ.hom := by rw [← hk]; simp
  rw [this]
  infer_instance

private lemma pushforwardStructureSheafMap_comp {X : Scheme.{u}}
    {U V W : Over X} (f : U ⟶ V) (g : V ⟶ W) :
    pushforwardStructureSheafMap (f ≫ g) =
      pushforwardStructureSheafMap g ≫ pushforwardStructureSheafMap f := by
  ext O x
  show (pushforwardStructureSheafMap (f ≫ g)).app O x =
    (pushforwardStructureSheafMap f).app O ((pushforwardStructureSheafMap g).app O x)
  rw [pushforwardStructureSheafMap_app, pushforwardStructureSheafMap_app,
    pushforwardStructureSheafMap_app]
  show ((f.left ≫ g.left).appLE (W.hom ⁻¹ᵁ O) (U.hom ⁻¹ᵁ O) _).hom x =
    (f.left.appLE (V.hom ⁻¹ᵁ O) (U.hom ⁻¹ᵁ O) _).hom
      ((g.left.appLE (W.hom ⁻¹ᵁ O) (V.hom ⁻¹ᵁ O) _).hom x)
  exact congrArg (fun k => k.hom x)
    (Scheme.Hom.appLE_comp_appLE f.left g.left (W.hom ⁻¹ᵁ O) (V.hom ⁻¹ᵁ O)
      (U.hom ⁻¹ᵁ O) (by rw [← Scheme.Hom.comp_preimage, Over.w g])
        (by rw [← Scheme.Hom.comp_preimage, Over.w f])).symm

private lemma affineHom_isIso_of_pushforwardStructureSheafMap {X : Scheme.{u}}
    (U V : AlgebraicGeometry.AffineOver X) (f : U ⟶ V)
    [IsIso (pushforwardStructureSheafMap f.hom)] : IsIso f := by
  have : IsIso ((algebraUnderlyingFunctor X).map
      (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f.hom)) := by
    have hh := pushforwardAlgebraMap_underlying f.hom
    let iU := pushforwardAlgebraUnderlyingIso U.obj.hom
    let iV := pushforwardAlgebraUnderlyingIso V.obj.hom
    let e := iV ≪≫ asIso (pushforwardStructureSheafMap f.hom) ≪≫ iU.symm
    have he : (algebraUnderlyingFunctor X).map
        (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f.hom) = e.hom :=
      (Category.comp_id _).symm.trans
        ((congrArg (fun k => (algebraUnderlyingFunctor X).map
          (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f.hom) ≫ k)
            iU.hom_inv_id.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ iU.inv) hh).trans (Category.assoc _ _ _))))
    exact he ▸ e.isIso_hom
  have := algebraUnderlyingFunctor_reflects_isIso
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f.hom)
  let e := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.equivalence X
  let iU := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X U
  let iV := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X V
  let L := ObjectProperty.ι (P := Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebra X)
  have hh := Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso_naturality X f
  have : IsIso (L.map (e.functor.map f.op)) := by
    have : IsIso (L.map (e.functor.map f.op) ≫ iU.hom) := by
      show IsIso
        (_ ≫ (Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.pushforwardIso X U).hom)
      rw [hh]
      show IsIso (iV.hom ≫ Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f.hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ iU.hom
  have : IsIso (e.functor.map f.op) := isIso_of_reflects_iso _ L
  have : IsIso f.op := isIso_of_reflects_iso _ e.functor
  exact isIso_of_op f

private lemma isPullback_of_pushforward_quotient {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {W V : Over X}
    [IsAffineHom W.hom] [IsAffineHom V.hom]
    (a : W.left ⟶ (I ^ (n + 1)).subscheme)
    (ha : a ≫ (I ^ (n + 1)).subschemeι = W.hom) (g : W ⟶ V)
    (eW : Stacks.Algebraization.idealPowerQuotient I (n + 1)
        (Stacks.Morphisms.pushforwardStructureSheaf V.hom) ≅
          Stacks.Morphisms.pushforwardStructureSheaf W.hom)
    (heW : cokernel.π (Stacks.Algebraization.idealPowerMultiple I (n + 1)
      (Stacks.Morphisms.pushforwardStructureSheaf V.hom)).ι ≫ eW.hom =
        pushforwardStructureSheafMap g) :
    IsPullback g.left a V.hom (I ^ (n + 1)).subschemeι := by
  let i := (I ^ (n + 1)).subschemeι
  let : IsAffineHom i := inferInstanceAs (IsAffineHom (I ^ (n + 1)).subschemeι)
  let P : Over X := Over.mk (pullback.snd V.hom i ≫ i)
  let pr : P ⟶ V := Over.homMk (pullback.fst V.hom i) pullback.condition
  have hs : g.left ≫ V.hom = a ≫ i := (Over.w g).trans ha.symm
  let k : W ⟶ P := Over.homMk (pullback.lift g.left a hs) (by
    show pullback.lift g.left a hs ≫ (pullback.snd V.hom i ≫ i) = W.hom
    rw [← Category.assoc, pullback.lift_snd, ha])
  have hk : k ≫ pr = g := by
    ext
    exact pullback.lift_fst _ _ _
  obtain ⟨eP, heP⟩ := pushforwardStructureSheafMap_quotient_of_isPullback I n pr
    (pullback.snd V.hom i) (IsPullback.of_hasPullback V.hom i)
  have : IsIso (pushforwardStructureSheafMap k) :=
    isIso_of_cokernel_comparison _ (pushforwardStructureSheafMap pr)
      (pushforwardStructureSheafMap g) (pushforwardStructureSheafMap k)
      (by rw [← pushforwardStructureSheafMap_comp, hk]) eP heP eW heW
  have : IsAffineHom (pullback.snd V.hom i) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback V.hom i) (inferInstance : IsAffineHom V.hom)
  have : IsAffineHom P.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd V.hom i ≫ i))
  let W' : AlgebraicGeometry.AffineOver X := ⟨W, inferInstance⟩
  let P' : AlgebraicGeometry.AffineOver X := ⟨P, inferInstance⟩
  let k' : W' ⟶ P' := ObjectProperty.homMk k
  have : IsIso (pushforwardStructureSheafMap k'.hom) :=
    inferInstanceAs (IsIso (pushforwardStructureSheafMap k))
  have : IsIso k' := affineHom_isIso_of_pushforwardStructureSheafMap W' P' k'
  have : IsIso k := (ObjectProperty.ι (P := AlgebraicGeometry.IsAffineHomOver X)).map_isIso k'
  have : IsIso k.left := (Over.forget X).map_isIso k
  exact IsPullback.of_iso_pullback ⟨hs⟩ (asIso k.left)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

private theorem exists_finiteLocallyFree_lift_tower
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme) :
    ∃ (V : Over X) (_ : Stacks.Morphisms.IsFiniteLocallyFree V.hom)
      (g : ∀ n, (idealPowerTowerOver I A).obj n ⟶ V),
      (∀ n, IsPullback (g n).left
        (finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A n).hom
        V.hom (I ^ (n + 1)).subschemeι) ∧
      ∀ n, (idealPowerTowerOver I A).map (homOfLE (Nat.le_succ n)) ≫ g (n + 1) = g n := by
  let F : FiniteLocallyFreeAdic I :=
    ⟨⟨idealPowerTowerModules I A, idealPowerTowerModules_isCoherentAdicSystem I A⟩,
      fun n => by
        obtain ⟨M, hM, hiso⟩ := idealPowerTowerModules_finiteLocallyFree I A n
        exact ⟨M, (Scheme.Modules.isFiniteLocallyFree_iff M).2 hM, hiso⟩⟩
  obtain ⟨E, ⟨eE⟩⟩ := finiteLocallyFreeCompletion_essSurj X I F
  obtain ⟨d, hd⟩ := exists_algebraizedTowerData X I A E eE
  let B := algebraSheafOfModule E.obj.obj d
  let := E.property
  have hB : B.IsQuasicoherent := algebraSheafOfModule_isQuasicoherent E.obj.obj d
  obtain ⟨V, ⟨eV⟩⟩ := exists_affineOver_algebraIso B hB
  let eM : Stacks.Morphisms.pushforwardStructureSheaf V.obj.hom ≅ E.obj.obj :=
    (pushforwardAlgebraUnderlyingIso V.obj.hom).symm ≪≫
      (algebraUnderlyingFunctor X).mapIso eV ≪≫ algebraSheafOfModuleIso E.obj.obj d
  have hV : Stacks.Morphisms.IsFiniteLocallyFree V.obj.hom :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff V.obj.hom).mpr
      ⟨V.property, finiteLocallyFree_of_iso eM.symm E.property⟩
  obtain ⟨g, hg⟩ := exists_towerMaps_of_algebraizedData X I A E eE d hd V eV
  refine ⟨V.obj, hV, g, ?_, ?_⟩
  · intro n
    let C := finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A n
    have : IsFinite ((idealPowerTowerOver I A).obj n).hom := isFinite_finiteEtaleTower_comp I A n
    let : IsAffineHom V.obj.hom := V.property
    let := hV
    let M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
      ⟨Stacks.Morphisms.pushforwardStructureSheaf V.obj.hom,
        Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X _⟩
    let eMC : M ≅ E.obj := ObjectProperty.isoMk _ eM
    obtain ⟨eQ, heQ⟩ := quotientIso_of_completionIso I M E.obj eMC F.obj eE n
    apply isPullback_of_pushforward_quotient I n C.hom rfl (g n) eQ
    exact heQ.trans (hg n).symm
  · intro n
    let T := idealPowerTowerOver I A
    let C := finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A n
    have : IsFinite (T.obj n).hom := isFinite_finiteEtaleTower_comp I A n
    have : IsAffineHom V.obj.hom := V.property
    apply affineHom_ext_of_pushforwardStructureSheafMap
    rw [pushforwardStructureSheafMap_comp, hg (n + 1), hg n]
    have ht := completionProjection_iso_transition I E.obj F.obj eE n
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (fun k => eM.hom ≫ k) (Eq.trans ?_ ht)
    exact congrArg (fun k => (Stacks.Algebraization.completionProjection X I E.obj (n + 1) ≫
      eE.hom.hom.app (op (n + 1))) ≫ k)
      (pushforwardStructureSheafMap_tower_map I A n)


private lemma tensor_mul_of_separating
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {e : A ⊗[R] A}
    (he : ∀ a : A, (a ⊗ₜ[R] 1 - 1 ⊗ₜ[R] a) * e = 0)
    (t : A ⊗[R] A) :
    t * e = ((Algebra.TensorProduct.lmul' R t) ⊗ₜ[R] (1 : A)) * e := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [add_mul, TensorProduct.add_tmul, hx, hy]
  | tmul a b =>
    have hb : (1 ⊗ₜ[R] b) * e = (b ⊗ₜ[R] (1 : A)) * e :=
      (sub_eq_zero.mp (by simpa only [sub_mul] using he b)).symm
    calc
      (a ⊗ₜ[R] b) * e = (a ⊗ₜ[R] (1 : A)) * ((1 ⊗ₜ[R] b) * e) := by
        rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      _ = (a ⊗ₜ[R] (1 : A)) * ((b ⊗ₜ[R] (1 : A)) * e) := by rw [hb]
      _ = _ := by simp [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul]

private lemma separabilityElement_unique
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    {e t : A ⊗[R] A}
    (he : ∀ a : A, (a ⊗ₜ[R] 1 - 1 ⊗ₜ[R] a) * e = 0)
    (ht : ∀ a : A, (a ⊗ₜ[R] 1 - 1 ⊗ₜ[R] a) * t = 0)
    (he1 : Algebra.TensorProduct.lmul' R e = 1)
    (ht1 : Algebra.TensorProduct.lmul' R t = 1) : e = t := by
  have hte := tensor_mul_of_separating R A he t
  have het := tensor_mul_of_separating R A ht e
  rw [ht1] at hte
  rw [he1] at het
  change t * e = (1 : A ⊗[R] A) * e at hte
  change e * t = (1 : A ⊗[R] A) * t at het
  simpa only [one_mul] using hte.symm.trans ((mul_comm t e).trans het)

/-- For a pushout `A ⊗[R] A` of `a` along itself, the identification with `B` is compatible with
the two inclusions and with multiplication `d : B ⟶ A`. -/
private lemma exists_tensorRingEquiv_of_isPushout
    {R A B : CommRingCat.{u}} (a : R ⟶ A) (l r : A ⟶ B)
    (H : IsPushout a a l r) (d : B ⟶ A) (hl : l ≫ d = 𝟙 A) (hr : r ≫ d = 𝟙 A) :
    letI : Algebra R A := a.hom.toAlgebra
    ∃ E' : A ⊗[R] A ≃+* B, (∀ x : A, E' (x ⊗ₜ[R] (1 : A)) = l.hom x) ∧
      (∀ x : A, E' ((1 : A) ⊗ₜ[R] x) = r.hom x) ∧
      ∀ t : A ⊗[R] A, d.hom (E' t) = Algebra.TensorProduct.lmul' R t := by
  let : Algebra R A := a.hom.toAlgebra
  let H₀ := CommRingCat.isPushout_tensorProduct R A A
  let E := H₀.isoIsPushout A A H
  have hd : E.hom ≫ d = CommRingCat.ofHom (Algebra.TensorProduct.lmul' R).toRingHom := by
    apply H₀.hom_ext <;> simp only [← Category.assoc]
    · rw [H₀.inl_isoIsPushout_hom A A H, hl]
      ext x
      simp
    · rw [H₀.inr_isoIsPushout_hom A A H, hr]
      ext x
      simp
  exact ⟨E.commRingCatIsoToRingEquiv,
    fun x => congrArg (fun f : A ⟶ B => f.hom x) (H₀.inl_isoIsPushout_hom A A H),
    fun x => congrArg (fun f : A ⟶ B => f.hom x) (H₀.inr_isoIsPushout_hom A A H),
    fun t => congrArg (fun f : CommRingCat.of (A ⊗[R] A) ⟶ A => f.hom t) hd⟩

private lemma existsUnique_separabilityElement_of_isPushout
    {R A B : CommRingCat.{u}} (a : R ⟶ A) (l r : A ⟶ B)
    (H : IsPushout a a l r) (d : B ⟶ A)
    (hl : l ≫ d = 𝟙 A) (hr : r ≫ d = 𝟙 A)
    (ha : a.hom.FormallyUnramified) (hft : a.hom.EssFiniteType) :
    ∃! e : B, d.hom e = 1 ∧ ∀ x : A, (l.hom x - r.hom x) * e = 0 := by
  let : Algebra R A := a.hom.toAlgebra
  let : Algebra.FormallyUnramified R A := ha
  let : Algebra.EssFiniteType R A := hft
  obtain ⟨E', hEl, hEr, hd'⟩ := exists_tensorRingEquiv_of_isPushout a l r H d hl hr
  let t := Algebra.FormallyUnramified.elem R A
  have ht : ∀ x : A, (x ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x) * t = 0 := by
    intro x
    rw [sub_mul, sub_eq_zero]
    exact (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) x).symm
  refine ⟨E' t, ⟨?_, ?_⟩, ?_⟩
  · rw [hd']
    exact Algebra.FormallyUnramified.lmul_elem (R := R) (S := A)
  · intro x
    rw [← hEl, ← hEr, ← map_sub, ← map_mul, ht, map_zero]
  · intro b hb
    apply E'.symm.injective
    simp only [RingEquiv.symm_apply_apply]
    apply separabilityElement_unique R A
    · intro x
      apply E'.injective
      simp only [map_mul, map_sub, hEl, hEr, E'.apply_symm_apply, map_zero]
      exact hb.2 x
    · exact ht
    · rw [← hd', E'.apply_symm_apply, hb.1]
    · exact Algebra.FormallyUnramified.lmul_elem (R := R) (S := A)

private lemma mul_eq_mul_of_isPushout
    {R A C P B : CommRingCat.{u}} {a : R ⟶ A} {c : R ⟶ C}
    {l : A ⟶ P} {r : C ⟶ P} (H : IsPushout a c l r)
    (f g : P ⟶ B) (e : B)
    (hl : ∀ x : A, f.hom (l.hom x) * e = g.hom (l.hom x) * e)
    (hr : ∀ x : C, f.hom (r.hom x) * e = g.hom (r.hom x) * e)
    (x : P) : f.hom x * e = g.hom x * e := by
  let S : Subring P :=
    { carrier := { x | f.hom x * e = g.hom x * e }
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro x y hx hy; simpa only [Set.mem_ofPred_eq, map_add, add_mul] using
          congrArg₂ (· + ·) hx hy
      neg_mem' := by
        intro x hx; simpa only [Set.mem_ofPred_eq, map_neg, neg_mul] using congrArg Neg.neg hx
      mul_mem' := by
        intro x y hx hy
        show f.hom (x * y) * e = g.hom (x * y) * e
        rw [map_mul, map_mul, mul_assoc, hy]
        calc
          f.hom x * (g.hom y * e) = g.hom y * (f.hom x * e) := by ring
          _ = g.hom y * (g.hom x * e) := by rw [hx]
          _ = _ := by ring }
  have hS : Subring.closure (Set.range l ∪ Set.range r) ≤ S := by
    apply Subring.closure_le.mpr
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact hl y
    · exact hr y
  rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout H] at hS
  exact hS (Subring.mem_top x)

private lemma separabilityElement_map
    {R A C A' B B' : CommRingCat.{u}}
    {a : R ⟶ A} {c : R ⟶ C} {α : A ⟶ A'} {a' : C ⟶ A'}
    (H : IsPushout a c α a')
    (l r : A ⟶ B) (l' r' : A' ⟶ B') (φ : B ⟶ B')
    (d : B ⟶ A) (d' : B' ⟶ A')
    (hbase : a' ≫ l' = a' ≫ r')
    (hl : l ≫ φ = α ≫ l') (hr : r ≫ φ = α ≫ r')
    (hd : φ ≫ d' = d ≫ α)
    (e : B) (he : d.hom e = 1 ∧ ∀ x : A, (l.hom x - r.hom x) * e = 0) :
    d'.hom (φ.hom e) = 1 ∧
      ∀ x : A', (l'.hom x - r'.hom x) * φ.hom e = 0 := by
  constructor
  · have h := congrArg (fun k : B ⟶ A' => k.hom e) hd
    change d'.hom (φ.hom e) = α.hom (d.hom e) at h
    simpa only [he.1, map_one] using h
  · intro x
    rw [sub_mul, sub_eq_zero]
    apply mul_eq_mul_of_isPushout H l' r' (φ.hom e)
    · intro y
      have h₁ := congrArg (fun k : A ⟶ B' => k.hom y) hl
      have h₂ := congrArg (fun k : A ⟶ B' => k.hom y) hr
      change φ.hom (l.hom y) = l'.hom (α.hom y) at h₁
      change φ.hom (r.hom y) = r'.hom (α.hom y) at h₂
      rw [← h₁, ← h₂, ← map_mul, ← map_mul]
      exact congrArg φ.hom (sub_eq_zero.mp (by simpa only [sub_mul] using he.2 y))
    · intro y
      exact congrArg (fun k : C ⟶ B' => k.hom y * φ.hom e) hbase


private abbrev overRingMap {X : Scheme.{u}} {A B : Over X}
    (f : A ⟶ B) (U : X.Opens) :
    B.left.presheaf.obj (op (B.hom ⁻¹ᵁ U)) ⟶
      A.left.presheaf.obj (op (A.hom ⁻¹ᵁ U)) :=
  (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f).right.hom.app (op U)

private lemma overRingMap_comp {X : Scheme.{u}} {A B C : Over X}
    (f : A ⟶ B) (g : B ⟶ C) (U : X.Opens) :
    overRingMap g U ≫ overRingMap f U = overRingMap (f ≫ g) U := by
  simp only [overRingMap, pushforwardAlgebraMap_app]
  exact Scheme.Hom.appLE_comp_appLE f.left g.left _ _ _ _ _

private lemma overRingMap_id {X : Scheme.{u}} (A : Over X) (U : X.Opens) :
    overRingMap (𝟙 A) U = 𝟙 _ := by
  simp only [overRingMap, pushforwardAlgebraMap_app, Scheme.Hom.appLE,
    Over.id_left, Scheme.Hom.id_app]
  exact A.left.presheaf.map_id _

private lemma overRingMap_naturality {X : Scheme.{u}} {A B : Over X}
    (f : A ⟶ B) {U V : X.Opens} (hVU : V ≤ U) :
    overRingMap f U ≫ A.left.presheaf.map
        ((TopologicalSpace.Opens.map A.hom.base).map (homOfLE hVU)).op =
      B.left.presheaf.map
        ((TopologicalSpace.Opens.map B.hom.base).map (homOfLE hVU)).op ≫
          overRingMap f V :=
  ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f).right.hom.naturality
    (homOfLE hVU).op).symm

@[implicit_reducible]
private def overSelfProduct {X : Scheme.{u}} (A : Over X) : Over X :=
  Over.mk (pullback.fst A.hom A.hom ≫ A.hom)

private def overSelfProductFst {X : Scheme.{u}} (A : Over X) : overSelfProduct A ⟶ A :=
  Over.homMk (pullback.fst A.hom A.hom)

private def overSelfProductSnd {X : Scheme.{u}} (A : Over X) : overSelfProduct A ⟶ A :=
  Over.homMk (pullback.snd A.hom A.hom) (pullback.condition.symm)

private def overDiagonal {X : Scheme.{u}} (A : Over X) : A ⟶ overSelfProduct A :=
  Over.homMk (pullback.diagonal A.hom) (by simp [overSelfProduct])

private lemma overDiagonal_fst {X : Scheme.{u}} (A : Over X) :
    overDiagonal A ≫ overSelfProductFst A = 𝟙 A := by
  ext
  exact pullback.diagonal_fst A.hom

private lemma overDiagonal_snd {X : Scheme.{u}} (A : Over X) :
    overDiagonal A ≫ overSelfProductSnd A = 𝟙 A := by
  ext
  exact pullback.diagonal_snd A.hom

private lemma overSelfProduct_isPushout {X : Scheme.{u}} (A : Over X)
    [IsAffineHom A.hom] (U : X.affineOpens) :
    IsPushout (A.hom.app U.1) (A.hom.app U.1)
      (overRingMap (overSelfProductFst A) U.1)
      (overRingMap (overSelfProductSnd A) U.1) := by
  have h := isPushout_appLE_of_isPullback (IsPullback.of_hasPullback A.hom A.hom)
    U.2 (IsAffineHom.isAffine_preimage _ U.2) (IsAffineHom.isAffine_preimage _ U.2)
    le_rfl le_rfl
    (show (overSelfProduct A).hom ⁻¹ᵁ U.1 =
      pullback.fst A.hom A.hom ⁻¹ᵁ (A.hom ⁻¹ᵁ U.1) ⊓
      pullback.snd A.hom A.hom ⁻¹ᵁ (A.hom ⁻¹ᵁ U.1) by
        show (pullback.fst A.hom A.hom ≫ A.hom) ⁻¹ᵁ U.1 = _
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition, inf_idem])
  simp only [Scheme.Hom.appLE_eq_app] at h
  simp only [overRingMap, pushforwardAlgebraMap_app]
  exact h

private lemma existsUnique_overSeparabilityElement {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] (U : X.affineOpens) :
    ∃! e : Γ((overSelfProduct A).left, (overSelfProduct A).hom ⁻¹ᵁ U.1),
      (overRingMap (overDiagonal A) U.1).hom e = 1 ∧
        ∀ x : Γ(A.left, A.hom ⁻¹ᵁ U.1),
          ((overRingMap (overSelfProductFst A) U.1).hom x -
            (overRingMap (overSelfProductSnd A) U.1).hom x) * e = 0 := by
  apply existsUnique_separabilityElement_of_isPushout (A.hom.app U.1) _ _
    (overSelfProduct_isPushout A U) (overRingMap (overDiagonal A) U.1)
  · rw [overRingMap_comp, overDiagonal_fst, overRingMap_id]
  · rw [overRingMap_comp, overDiagonal_snd, overRingMap_id]
  · simpa only [Scheme.Hom.appLE_eq_app] using
      A.hom.formallyUnramified_appLE U.2 (IsAffineHom.isAffine_preimage _ U.2) le_rfl
  · exact (A.hom.finite_app U.1 U.2).finiteType.essFiniteType

private def overSeparabilityElement {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] (U : X.affineOpens) :
    Γ((overSelfProduct A).left, (overSelfProduct A).hom ⁻¹ᵁ U.1) :=
  (existsUnique_overSeparabilityElement A U).choose

private lemma overSeparabilityElement_spec {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] (U : X.affineOpens) :
    (overRingMap (overDiagonal A) U.1).hom (overSeparabilityElement A U) = 1 ∧
      ∀ x : Γ(A.left, A.hom ⁻¹ᵁ U.1),
        ((overRingMap (overSelfProductFst A) U.1).hom x -
          (overRingMap (overSelfProductSnd A) U.1).hom x) *
          overSeparabilityElement A U = 0 :=
  (existsUnique_overSeparabilityElement A U).choose_spec.1


private lemma isPushout_app_restriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (U V : X.affineOpens) (hVU : V.1 ≤ U.1) :
    IsPushout (f.app U.1) (X.presheaf.map (homOfLE hVU).op)
      (Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map (homOfLE hVU)).op)
      (f.app V.1) := by
  have h := isPushout_appLE_of_isPullback (IsPullback.id_horiz f)
    U.2 V.2 (IsAffineHom.isAffine_preimage _ U.2)
    (show V.1 ≤ (𝟙 X) ⁻¹ᵁ U.1 from hVU) le_rfl
    (show f ⁻¹ᵁ V.1 = (𝟙 Y) ⁻¹ᵁ (f ⁻¹ᵁ U.1) ⊓ f ⁻¹ᵁ V.1 by
      simpa only [Scheme.Hom.id_preimage] using
        (inf_eq_right.mpr ((TopologicalSpace.Opens.map f.base).monotone hVU)).symm)
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, homOfLE_refl, CategoryTheory.op_id,
    Y.presheaf.map_id, Category.comp_id] at h
  convert h using 1
  · congr 1
  · exact (Category.id_comp _).symm

private lemma overSeparabilityElement_naturality {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom]
    (U V : X.affineOpens) (hVU : V.1 ≤ U.1) :
    ((overSelfProduct A).left.presheaf.map
      ((TopologicalSpace.Opens.map (overSelfProduct A).hom.base).map
        (homOfLE hVU)).op).hom (overSeparabilityElement A U) =
      overSeparabilityElement A V := by
  apply (existsUnique_overSeparabilityElement A V).choose_spec.2
  apply separabilityElement_map (isPushout_app_restriction A.hom U V hVU)
    (overRingMap (overSelfProductFst A) U.1)
    (overRingMap (overSelfProductSnd A) U.1)
    (overRingMap (overSelfProductFst A) V.1)
    (overRingMap (overSelfProductSnd A) V.1) _
    (overRingMap (overDiagonal A) U.1) (overRingMap (overDiagonal A) V.1)
  · exact (overSelfProduct_isPushout A V).w
  · exact overRingMap_naturality (overSelfProductFst A) hVU
  · exact overRingMap_naturality (overSelfProductSnd A) hVU
  · exact (overRingMap_naturality (overDiagonal A) hVU).symm
  · exact overSeparabilityElement_spec A U

private def overSeparabilityMapApp {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] (U : X.affineOpens) :
    (SheafOfModules.unit X.ringCatSheaf).val.obj (op U.1) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (overSelfProduct A).hom).val.obj (op U.1) := by
  let P := overSelfProduct A
  letI : Algebra Γ(X, U.1) Γ(P.left, P.hom ⁻¹ᵁ U.1) := (P.hom.app U.1).hom.toAlgebra
  change ModuleCat.of Γ(X, U.1) Γ(X, U.1) ⟶
    ModuleCat.of Γ(X, U.1) Γ(P.left, P.hom ⁻¹ᵁ U.1)
  exact ModuleCat.ofHom ((LinearMap.id : Γ(X, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1)).smulRight
    (overSeparabilityElement A U))

private lemma overSeparabilityMapApp_one {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] (U : X.affineOpens) :
    overSeparabilityMapApp A U (1 : Γ(X, U.1)) = overSeparabilityElement A U := by
  let P := overSelfProduct A
  let : Algebra Γ(X, U.1) Γ(P.left, P.hom ⁻¹ᵁ U.1) := (P.hom.app U.1).hom.toAlgebra
  exact one_smul Γ(X, U.1) (overSeparabilityElement A U)

private def overSeparabilityMap {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] :
    SheafOfModules.unit X.ringCatSheaf ⟶
      Stacks.Morphisms.pushforwardStructureSheaf (overSelfProduct A).hom := by
  refine moduleHomOfAffine (overSeparabilityMapApp A) ?_
  intro U V hVU s
  change Γ(X, U.1) at s
  let P := overSelfProduct A
  letI : Algebra Γ(X, U.1) Γ(P.left, P.hom ⁻¹ᵁ U.1) := (P.hom.app U.1).hom.toAlgebra
  letI : Algebra Γ(X, V.1) Γ(P.left, P.hom ⁻¹ᵁ V.1) := (P.hom.app V.1).hom.toAlgebra
  change ((X.presheaf.map (homOfLE hVU).op).hom s) • overSeparabilityElement A V =
    ((overSelfProduct A).left.presheaf.map
      ((TopologicalSpace.Opens.map (overSelfProduct A).hom.base).map
        (homOfLE hVU)).op).hom (s • overSeparabilityElement A U)
  rw [← overSeparabilityElement_naturality A U V hVU]
  exact ((Stacks.Morphisms.pushforwardStructureSheaf (overSelfProduct A).hom).val.map_smul
    (homOfLE hVU).op s (overSeparabilityElement A U)).symm

private lemma overSeparabilityMap_apply_one {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] (U : X.affineOpens) :
    (overSeparabilityMap A).val.app (op U.1) (1 : Γ(X, U.1)) =
      overSeparabilityElement A U := by
  unfold overSeparabilityMap
  exact (ConcreteCategory.congr_hom (moduleHomOfAffine_app _ _ U) _).trans
    (overSeparabilityMapApp_one A U)


private def overSelfProductMap {X : Scheme.{u}} {A B : Over X} (f : A ⟶ B) :
    overSelfProduct A ⟶ overSelfProduct B :=
  Over.homMk (pullback.map A.hom A.hom B.hom B.hom f.left f.left (𝟙 X)
    (by simp) (by simp)) (by
      simp only [overSelfProduct, Over.mk_hom, pullback.map, pullback.lift_fst_assoc,
        Category.assoc, Over.w])

private lemma overSelfProductMap_left {X : Scheme.{u}} {A B : Over X} (f : A ⟶ B) :
    (overSelfProductMap f).left = pullback.map A.hom A.hom B.hom B.hom f.left f.left (𝟙 X)
      (by simp) (by simp) := rfl

private lemma overDiagonal_left {X : Scheme.{u}} (A : Over X) :
    (overDiagonal A).left = pullback.diagonal A.hom := rfl

private lemma overSelfProductMap_fst {X : Scheme.{u}} {A B : Over X} (f : A ⟶ B) :
    overSelfProductMap f ≫ overSelfProductFst B = overSelfProductFst A ≫ f := by
  ext
  exact pullback.lift_fst _ _ _

private lemma overSelfProductMap_snd {X : Scheme.{u}} {A B : Over X} (f : A ⟶ B) :
    overSelfProductMap f ≫ overSelfProductSnd B = overSelfProductSnd A ≫ f := by
  ext
  exact pullback.lift_snd _ _ _

private lemma overDiagonal_naturality {X : Scheme.{u}} {A B : Over X} (f : A ⟶ B) :
    overDiagonal A ≫ overSelfProductMap f = f ≫ overDiagonal B := by
  ext
  rw [Over.comp_left, Over.comp_left, overDiagonal_left, overDiagonal_left,
    overSelfProductMap_left]
  apply pullback.hom_ext
  · calc _ = pullback.diagonal A.hom ≫ (pullback.fst A.hom A.hom ≫ f.left) :=
          (Category.assoc _ _ _).trans
            (congrArg (pullback.diagonal A.hom ≫ ·) (pullback.lift_fst _ _ _))
      _ = f.left := by rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
      _ = (f.left ≫ pullback.diagonal B.hom) ≫ pullback.fst B.hom B.hom := by
          rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  · calc _ = pullback.diagonal A.hom ≫ (pullback.snd A.hom A.hom ≫ f.left) :=
          (Category.assoc _ _ _).trans
            (congrArg (pullback.diagonal A.hom ≫ ·) (pullback.lift_snd _ _ _))
      _ = f.left := by rw [← Category.assoc, pullback.diagonal_snd, Category.id_comp]
      _ = (f.left ≫ pullback.diagonal B.hom) ≫ pullback.snd B.hom B.hom := by
          rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]

private lemma overRingMap_apply {X : Scheme.{u}} {A B : Over X}
    (f : A ⟶ B) (U : X.Opens) (x : Γ(B.left, B.hom ⁻¹ᵁ U)) :
    (overRingMap f U).hom x = (pushforwardStructureSheafMap f).val.app (op U) x := by
  show ((Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap f).right.hom.app (op U)).hom x =
    (pushforwardStructureSheafMap f).app U x
  rw [pushforwardAlgebraMap_app, pushforwardStructureSheafMap_app]
  rfl

private lemma overSeparabilityElement_map {X : Scheme.{u}} {A B : Over X}
    [IsFinite A.hom] [FormallyUnramified A.hom]
    [IsFinite B.hom] [FormallyUnramified B.hom]
    (f : A ⟶ B) [IsClosedImmersion f.left] (U : X.affineOpens) :
    (overRingMap (overSelfProductMap f) U.1).hom (overSeparabilityElement B U) =
      overSeparabilityElement A U := by
  apply (existsUnique_overSeparabilityElement A U).choose_spec.2
  have hl := congrArg (fun k => overRingMap k U.1) (overSelfProductMap_fst f)
  have hr := congrArg (fun k => overRingMap k U.1) (overSelfProductMap_snd f)
  have hd := congrArg (fun k => overRingMap k U.1) (overDiagonal_naturality f)
  simp only [← overRingMap_comp] at hl hr hd
  constructor
  · have hh := congrArg (fun k => k.hom (overSeparabilityElement B U)) hd
    change (overRingMap (overDiagonal A) U.1).hom
        ((overRingMap (overSelfProductMap f) U.1).hom (overSeparabilityElement B U)) =
      (overRingMap f U.1).hom
        ((overRingMap (overDiagonal B) U.1).hom (overSeparabilityElement B U)) at hh
    simpa only [(overSeparabilityElement_spec B U).1, map_one] using hh
  · intro x
    obtain ⟨y, hy⟩ := pushforwardStructureSheafMap_surjective_affine f U x
    change Γ(B.left, B.hom ⁻¹ᵁ U.1) at y
    rw [← overRingMap_apply] at hy
    subst x
    have hl' := congrArg (fun k => k.hom y) hl
    have hr' := congrArg (fun k => k.hom y) hr
    change (overRingMap (overSelfProductMap f) U.1).hom
        ((overRingMap (overSelfProductFst B) U.1).hom y) =
      (overRingMap (overSelfProductFst A) U.1).hom ((overRingMap f U.1).hom y) at hl'
    change (overRingMap (overSelfProductMap f) U.1).hom
        ((overRingMap (overSelfProductSnd B) U.1).hom y) =
      (overRingMap (overSelfProductSnd A) U.1).hom ((overRingMap f U.1).hom y) at hr'
    rw [← hl', ← hr', ← map_sub, ← map_mul,
      (overSeparabilityElement_spec B U).2 y, map_zero]

private lemma overSeparabilityMap_naturality {X : Scheme.{u}} {A B : Over X}
    [IsFinite A.hom] [FormallyUnramified A.hom]
    [IsFinite B.hom] [FormallyUnramified B.hom]
    (f : A ⟶ B) [IsClosedImmersion f.left] :
    overSeparabilityMap B ≫ pushforwardStructureSheafMap (overSelfProductMap f) =
      overSeparabilityMap A := by
  apply moduleHom_ext_affine
  intro U
  ext
  show (pushforwardStructureSheafMap (overSelfProductMap f)).val.app (op U.1)
      ((overSeparabilityMap B).val.app (op U.1) (1 : Γ(X, U.1))) =
    (overSeparabilityMap A).val.app (op U.1) (1 : Γ(X, U.1))
  rw [overSeparabilityMap_apply_one, overSeparabilityMap_apply_one, ← overRingMap_apply]
  exact overSeparabilityElement_map f U


private lemma exists_map_of_quotientMaps
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (E G : FiniteLocallyFreeCoherent X) (Q : ℕ → X.Modules)
    (e : ∀ n, ((Stacks.Algebraization.completionFunctor X I).obj G.obj).obj.obj (op n) ≅ Q n)
    (t : ∀ n, Q (n + 1) ⟶ Q n)
    (ht : ∀ n, (Stacks.Algebraization.completionProjection X I G.obj (n + 1) ≫ (e (n + 1)).hom) ≫
      t n = Stacks.Algebraization.completionProjection X I G.obj n ≫ (e n).hom)
    (hQ : ∀ n, Stacks.Algebraization.idealPowerMultiple I (n + 1) (Q n) = ⊥)
    (q : ∀ n, E.obj.obj ⟶ Q n) (hq : ∀ n, q (n + 1) ≫ t n = q n) :
    ∃ f : E.obj.obj ⟶ G.obj.obj, ∀ n,
      f ≫ Stacks.Algebraization.completionProjection X I G.obj n ≫ (e n).hom = q n := by
  choose d hd using fun n => exists_completionProjection_desc I E.obj n (q n) (hQ n)
  let φ n := d n ≫ (e n).inv
  have hφ n :
      ((Stacks.Algebraization.completionFunctor X I).obj E.obj).obj.map
          (homOfLE (Nat.le_succ n)).op ≫ φ n =
        φ (n + 1) ≫ ((Stacks.Algebraization.completionFunctor X I).obj G.obj).obj.map
          (homOfLE (Nat.le_succ n)).op := by
    have htrans :
        ((Stacks.Algebraization.completionFunctor X I).obj G.obj).obj.map
            (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
          (e (n + 1)).hom ≫ t n := by
      apply (@cancel_epi _ _ _ _ _ (Stacks.Algebraization.completionProjection X I G.obj (n + 1))
        (Stacks.Algebraization.epi_completionProjection X I G.obj (n + 1)) _ _).mp
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (e n).hom)
          (Stacks.Algebraization.completionProjection_transition X I G.obj n)).trans
          ((ht n).symm.trans (Category.assoc _ _ _)))
    have htrans' : (e (n + 1)).inv ≫
        ((Stacks.Algebraization.completionFunctor X I).obj G.obj).obj.map
            (homOfLE (Nat.le_succ n)).op = t n ≫ (e n).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← htrans, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    apply (@cancel_epi _ _ _ _ _ (Stacks.Algebraization.completionProjection X I E.obj (n + 1))
        (Stacks.Algebraization.epi_completionProjection X I E.obj (n + 1)) _ _).mp
    calc _ = (Stacks.Algebraization.completionProjection X I E.obj (n + 1) ≫
            ((Stacks.Algebraization.completionFunctor X I).obj E.obj).obj.map
              (homOfLE (Nat.le_succ n)).op) ≫ φ n := (Category.assoc _ _ _).symm
      _ = Stacks.Algebraization.completionProjection X I E.obj n ≫ φ n :=
          congrArg (· ≫ φ n) (Stacks.Algebraization.completionProjection_transition X I E.obj n)
      _ = (Stacks.Algebraization.completionProjection X I E.obj n ≫ d n) ≫ (e n).inv :=
          (Category.assoc _ _ _).symm
      _ = (q (n + 1) ≫ t n) ≫ (e n).inv :=
          congrArg (· ≫ (e n).inv) ((hd n).trans (hq n).symm)
      _ = q (n + 1) ≫ ((e (n + 1)).inv ≫
            ((Stacks.Algebraization.completionFunctor X I).obj G.obj).obj.map
              (homOfLE (Nat.le_succ n)).op) :=
          (Category.assoc _ _ _).trans (congrArg (q (n + 1) ≫ ·) htrans'.symm)
      _ = (Stacks.Algebraization.completionProjection X I E.obj (n + 1) ≫ d (n + 1)) ≫
            ((e (n + 1)).inv ≫
              ((Stacks.Algebraization.completionFunctor X I).obj G.obj).obj.map
                (homOfLE (Nat.le_succ n)).op) :=
          congrArg (· ≫ _) (hd (n + 1)).symm
      _ = _ := (Category.assoc _ _ _).trans
          (congrArg (Stacks.Algebraization.completionProjection X I E.obj (n + 1) ≫ ·)
            (Category.assoc _ _ _).symm)
  obtain ⟨f, hf, -⟩ := existsUnique_completion_map X I E G φ hφ
  refine ⟨f.hom, fun n => ?_⟩
  have hde : φ n ≫ (e n).hom = d n := by
    simp only [φ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc _ = (f.hom ≫ Stacks.Algebraization.completionProjection X I G.obj n) ≫ (e n).hom :=
        (Category.assoc _ _ _).symm
    _ = (Stacks.Algebraization.completionProjection X I E.obj n ≫ φ n) ≫ (e n).hom :=
        congrArg (· ≫ (e n).hom) (hf n).symm
    _ = Stacks.Algebraization.completionProjection X I E.obj n ≫ d n :=
        (Category.assoc _ _ _).trans
          (congrArg (Stacks.Algebraization.completionProjection X I E.obj n ≫ ·) hde)
    _ = q n := hd n

private lemma hom_ext_of_quotientMaps
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (E G : FiniteLocallyFreeCoherent X) (Q : ℕ → X.Modules)
    (e : ∀ n, ((Stacks.Algebraization.completionFunctor X I).obj G.obj).obj.obj (op n) ≅ Q n)
    {f g : E.obj.obj ⟶ G.obj.obj}
    (hfg : ∀ n, f ≫ Stacks.Algebraization.completionProjection X I G.obj n ≫ (e n).hom =
      g ≫ Stacks.Algebraization.completionProjection X I G.obj n ≫ (e n).hom) : f = g := by
  apply hom_ext_of_completionProjection_iso X I
    ((Stacks.Algebraization.completionFunctor X I).obj G.obj) (Iso.refl _)
  intro n
  have h1 : (f ≫ Stacks.Algebraization.completionProjection X I G.obj n) ≫ (e n).hom =
      (g ≫ Stacks.Algebraization.completionProjection X I G.obj n) ≫ (e n).hom :=
    (Category.assoc _ _ _).trans ((hfg n).trans (Category.assoc _ _ _).symm)
  have h2 := (cancel_mono (e n).hom).mp h1
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ 𝟙 _) h2).trans (Category.assoc _ _ _))

private lemma isPullback_pullbackMap_self
    {X Y A B : Scheme.{u}} (i : Y ⟶ X) [Mono i] (pA : A ⟶ X) (pB : B ⟶ X)
    (a : A ⟶ Y) (ha : a ≫ i = pA) (f : A ⟶ B) (hf : f ≫ pB = pA)
    (H : IsPullback f a pB i) :
    IsPullback (pullback.map pA pA pB pB f f (𝟙 X) (by simp [hf]) (by simp [hf]))
      (pullback.fst pA pA ≫ a) (pullback.fst pB pB ≫ pB) i := by
  have hpa : pullback.fst pA pA ≫ a = pullback.snd pA pA ≫ a := by
    apply (cancel_mono i).mp
    simpa only [Category.assoc, ha] using pullback.condition (f := pA) (g := pA)
  have hw : pullback.map pA pA pB pB f f (𝟙 X) (by simp [hf]) (by simp [hf]) ≫
      pullback.fst pB pB ≫ pB = (pullback.fst pA pA ≫ a) ≫ i := by
    simp [pullback.map, hf, ha, pullback.lift_fst_assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => ?_) ?_ ?_ ?_⟩⟩
  · let l : s.pt ⟶ A := H.lift (s.fst ≫ pullback.fst pB pB) s.snd
      (by simpa only [Category.assoc] using s.condition)
    let r : s.pt ⟶ A := H.lift (s.fst ≫ pullback.snd pB pB) s.snd
      (by simpa only [Category.assoc, pullback.condition] using s.condition)
    exact pullback.lift l r (by
      rw [← ha, ← Category.assoc, ← Category.assoc, H.lift_snd, H.lift_snd])
  · intro s
    apply pullback.hom_ext <;>
      simp [pullback.map, Category.assoc, H.lift_fst, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro s
    simp only [pullback.lift_fst_assoc, H.lift_snd]
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · apply H.hom_ext
      · have hm := congrArg (fun k => k ≫ pullback.fst pB pB) hm₁
        simpa [pullback.map, Category.assoc, H.lift_fst, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hm
      · simpa [H.lift_snd, pullback.lift_fst_assoc] using hm₂
    · apply H.hom_ext
      · have hm := congrArg (fun k => k ≫ pullback.snd pB pB) hm₁
        simpa [pullback.map, Category.assoc, H.lift_fst, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hm
      · simp only [Category.assoc, pullback.lift_fst_assoc, H.lift_snd, ← hpa]
        exact hm₂

private lemma isPullback_overSelfProductMap
    {X Y : Scheme.{u}} (i : Y ⟶ X) [Mono i]
    {A B : Over X} (a : A.left ⟶ Y) (ha : a ≫ i = A.hom) (f : A ⟶ B)
    (H : IsPullback f.left a B.hom i) :
    IsPullback (overSelfProductMap f).left
      (pullback.fst A.hom A.hom ≫ a) (overSelfProduct B).hom i :=
  isPullback_pullbackMap_self i A.hom B.hom a ha f.left (Over.w f) H


private def multiplyBySection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (η : SheafOfModules.unit X.ringCatSheaf ⟶ Stacks.Morphisms.pushforwardStructureSheaf f) :
    Stacks.Morphisms.pushforwardStructureSheaf f ⟶
      Stacks.Morphisms.pushforwardStructureSheaf f where
  val :=
    { app U := by
        letI : Algebra Γ(X, U.unop) Γ(Y, f ⁻¹ᵁ U.unop) := (f.app U.unop).hom.toAlgebra
        change ModuleCat.of Γ(X, U.unop) Γ(Y, f ⁻¹ᵁ U.unop) ⟶
          ModuleCat.of Γ(X, U.unop) Γ(Y, f ⁻¹ᵁ U.unop)
        exact ModuleCat.ofHom (LinearMap.mulRight Γ(X, U.unop)
          (η.val.app U (1 : Γ(X, U.unop))))
      naturality {U V} g := by
        ext x
        change Mul.mul (α := Γ(Y, f ⁻¹ᵁ V.unop))
            ((Stacks.Morphisms.pushforwardStructureSheaf f).val.map g x)
            (η.val.app V (1 : Γ(X, V.unop))) =
          ((Stacks.Morphisms.pushforwardStructureSheaf f).val.map g)
            (Mul.mul (α := Γ(Y, f ⁻¹ᵁ U.unop)) x (η.val.app U (1 : Γ(X, U.unop))))
        have hn := PresheafOfModules.naturality_apply η.val g (1 : Γ(X, U.unop))
        change η.val.app V ((X.presheaf.map g).hom 1) = _ at hn
        rw [map_one] at hn
        rw [hn]
        exact (map_mul (Y.presheaf.map
          ((TopologicalSpace.Opens.map f.base).map g.unop).op).hom _ _).symm }

private lemma multiplyBySection_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    (η : SheafOfModules.unit X.ringCatSheaf ⟶ Stacks.Morphisms.pushforwardStructureSheaf f)
    (U : X.Opens) (x : Γ(Y, f ⁻¹ᵁ U)) :
    (multiplyBySection f η).val.app (op U) x =
      Mul.mul (α := Γ(Y, f ⁻¹ᵁ U)) x (η.val.app (op U) (1 : Γ(X, U))) := rfl

private lemma multiplyBySection_naturality {X : Scheme.{u}} {A B : Over X}
    (f : A ⟶ B)
    (η : SheafOfModules.unit X.ringCatSheaf ⟶ Stacks.Morphisms.pushforwardStructureSheaf B.hom) :
    multiplyBySection B.hom η ≫ pushforwardStructureSheafMap f =
      pushforwardStructureSheafMap f ≫
        multiplyBySection A.hom (η ≫ pushforwardStructureSheafMap f) := by
  ext U x
  show (pushforwardStructureSheafMap f).val.app (op U)
      ((multiplyBySection B.hom η).val.app (op U) x) =
    (multiplyBySection A.hom (η ≫ pushforwardStructureSheafMap f)).val.app (op U)
      ((pushforwardStructureSheafMap f).val.app (op U) x)
  show (pushforwardStructureSheafMap f).val.app (op U)
      (Mul.mul (α := Γ(B.left, B.hom ⁻¹ᵁ U)) x (η.val.app (op U) (1 : Γ(X, U)))) =
    Mul.mul (α := Γ(A.left, A.hom ⁻¹ᵁ U))
      ((pushforwardStructureSheafMap f).val.app (op U) x)
      ((pushforwardStructureSheafMap f).val.app (op U) (η.val.app (op U) (1 : Γ(X, U))))
  exact ((overRingMap_apply f U _).symm.trans (map_mul (overRingMap f U).hom _ _)).trans
    (congrArg₂ (· * ·) (overRingMap_apply f U _) (overRingMap_apply f U _))

private lemma overSeparabilityMap_diagonal {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] :
    overSeparabilityMap A ≫ pushforwardStructureSheafMap (overDiagonal A) =
      SheafOfModules.unitToPushforwardObjUnit A.hom.toRingCatSheafHom := by
  apply moduleHom_ext_affine
  intro U
  ext
  show (pushforwardStructureSheafMap (overDiagonal A)).val.app (op U.1)
      ((overSeparabilityMap A).val.app (op U.1) (1 : Γ(X, U.1))) =
    (A.hom.app U.1).hom 1
  rw [overSeparabilityMap_apply_one, ← overRingMap_apply, map_one]
  exact (overSeparabilityElement_spec A U).1

private lemma overSeparabilityMap_annihilates {X : Scheme.{u}} (A : Over X)
    [IsFinite A.hom] [FormallyUnramified A.hom] :
    (pushforwardStructureSheafMap (overSelfProductFst A) -
      pushforwardStructureSheafMap (overSelfProductSnd A)) ≫
      multiplyBySection (overSelfProduct A).hom (overSeparabilityMap A) = 0 := by
  apply moduleHom_ext_affine
  intro U
  ext x
  show (multiplyBySection (overSelfProduct A).hom (overSeparabilityMap A)).val.app (op U.1)
      ((pushforwardStructureSheafMap (overSelfProductFst A)).val.app (op U.1) x -
        (pushforwardStructureSheafMap (overSelfProductSnd A)).val.app (op U.1) x) = 0
  exact (congrArg₂ (fun (a b : Γ((overSelfProduct A).left, (overSelfProduct A).hom ⁻¹ᵁ U.1)) =>
      (a - b) * (show Γ((overSelfProduct A).left, (overSelfProduct A).hom ⁻¹ᵁ U.1) from
        (overSeparabilityMap A).val.app (op U.1) (1 : Γ(X, U.1))))
      (overRingMap_apply _ _ x).symm (overRingMap_apply _ _ x).symm).trans
    ((congrArg (fun z : Γ((overSelfProduct A).left, (overSelfProduct A).hom ⁻¹ᵁ U.1) =>
      ((overRingMap (overSelfProductFst A) U.1).hom x -
        (overRingMap (overSelfProductSnd A) U.1).hom x) * z)
      (overSeparabilityMap_apply_one A U)).trans ((overSeparabilityElement_spec A U).2 x))

private lemma formallyUnramified_of_separabilityElement_of_isPushout
    {R A B : CommRingCat.{u}} (a : R ⟶ A) (l r : A ⟶ B)
    (H : IsPushout a a l r) (d : B ⟶ A)
    (hl : l ≫ d = 𝟙 A) (hr : r ≫ d = 𝟙 A)
    (hft : a.hom.EssFiniteType) (e : B)
    (he : d.hom e = 1 ∧ ∀ x : A, (l.hom x - r.hom x) * e = 0) :
    a.hom.FormallyUnramified := by
  let : Algebra R A := a.hom.toAlgebra
  let : Algebra.EssFiniteType R A := hft
  obtain ⟨E', hEl, hEr, hd'⟩ := exists_tensorRingEquiv_of_isPushout a l r H d hl hr
  show Algebra.FormallyUnramified R A
  apply Algebra.FormallyUnramified.iff_exists_tensorProduct.mpr
  refine ⟨E'.symm e, ?_, ?_⟩
  · intro x
    apply E'.injective
    simp only [map_mul, map_sub, hEl, hEr, E'.apply_symm_apply, map_zero]
    rw [sub_mul, sub_eq_zero]
    exact (sub_eq_zero.mp (by simpa only [sub_mul] using he.2 x)).symm
  · simpa only [E'.apply_symm_apply, he.1] using (hd' (E'.symm e)).symm


private lemma finiteLocallyFree_overSelfProduct {X : Scheme.{u}} (A : Over X)
    [Stacks.Morphisms.IsFiniteLocallyFree A.hom] :
    Stacks.Morphisms.IsFiniteLocallyFree (overSelfProduct A).hom := by
  obtain ⟨hfin, hflat, hpres⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation A.hom).mp
      inferInstance
  let := hfin
  let := hflat
  let := hpres
  apply (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
  show IsFinite (pullback.fst A.hom A.hom ≫ A.hom) ∧
    Flat (pullback.fst A.hom A.hom ≫ A.hom) ∧
      LocallyOfFinitePresentation (pullback.fst A.hom A.hom ≫ A.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private lemma etale_of_separabilityMap {X : Scheme.{u}} (A : Over X)
    [Stacks.Morphisms.IsFiniteLocallyFree A.hom]
    (η : SheafOfModules.unit X.ringCatSheaf ⟶
      Stacks.Morphisms.pushforwardStructureSheaf (overSelfProduct A).hom)
    (hη : η ≫ pushforwardStructureSheafMap (overDiagonal A) =
      SheafOfModules.unitToPushforwardObjUnit A.hom.toRingCatSheafHom)
    (hsep : (pushforwardStructureSheafMap (overSelfProductFst A) -
      pushforwardStructureSheafMap (overSelfProductSnd A)) ≫
        multiplyBySection (overSelfProduct A).hom η = 0) : Etale A.hom := by
  obtain ⟨hfin, hflat, hpres⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation A.hom).mp
      inferInstance
  let := hfin
  let := hflat
  let := hpres
  have hU (U : X.affineOpens) : (A.hom.app U.1).hom.FormallyUnramified := by
    refine formallyUnramified_of_separabilityElement_of_isPushout (A.hom.app U.1) _ _
      (overSelfProduct_isPushout A U) (overRingMap (overDiagonal A) U.1) ?_ ?_
      ((A.hom.finite_app U.1 U.2).finiteType.essFiniteType)
      (η.val.app (op U.1) (1 : Γ(X, U.1))) ?_
    · rw [overRingMap_comp, overDiagonal_fst, overRingMap_id]
    · rw [overRingMap_comp, overDiagonal_snd, overRingMap_id]
    · constructor
      · have hh := congrArg (fun k => (k.val.app (op U.1)).hom (1 : Γ(X, U.1))) hη
        change (pushforwardStructureSheafMap (overDiagonal A)).val.app (op U.1)
          (η.val.app (op U.1) (1 : Γ(X, U.1))) = (A.hom.app U.1).hom 1 at hh
        have hh' : (A.hom.app U.1).hom (1 : Γ(X, U.1)) = 1 := map_one _
        exact (overRingMap_apply _ _ _).trans (hh.trans hh')
      · intro x
        have hh := congrArg (fun k => (k.val.app (op U.1)).hom x) hsep
        change (multiplyBySection (overSelfProduct A).hom η).val.app (op U.1)
          ((pushforwardStructureSheafMap (overSelfProductFst A)).val.app (op U.1) x -
            (pushforwardStructureSheafMap (overSelfProductSnd A)).val.app (op U.1) x) = 0 at hh
        exact (congrArg₂ (fun (a b : Γ((overSelfProduct A).left,
            (overSelfProduct A).hom ⁻¹ᵁ U.1)) =>
          (a - b) * (show Γ((overSelfProduct A).left, (overSelfProduct A).hom ⁻¹ᵁ U.1) from
            η.val.app (op U.1) (1 : Γ(X, U.1))))
          (overRingMap_apply _ _ x) (overRingMap_apply _ _ x)).trans hh
  have : FormallyUnramified A.hom := by
    constructor
    intro U hUaff V hVaff hVU
    have hres := (𝟙 A.left : A.left ⟶ A.left).formallyUnramified_appLE
      (IsAffineHom.isAffine_preimage U hUaff) hVaff hVU
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at hres
    exact (hU ⟨U, hUaff⟩).comp hres
  exact Etale.of_formallyUnramified_of_flat A.hom

private lemma exists_completionPushforwardIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) {A B : Over X} [IsAffineHom B.hom]
    (E : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hE : E.obj = Stacks.Morphisms.pushforwardStructureSheaf B.hom)
    (g : A ⟶ B) (a : A.left ⟶ (I ^ (n + 1)).subscheme)
    (H : IsPullback g.left a B.hom (I ^ (n + 1)).subschemeι) :
    ∃ e : ((Stacks.Algebraization.completionFunctor X I).obj E).obj.obj (op n) ≅
        Stacks.Morphisms.pushforwardStructureSheaf A.hom,
      Stacks.Algebraization.completionProjection X I E n ≫ e.hom =
        eqToHom hE ≫ pushforwardStructureSheafMap g := by
  obtain ⟨Q, hQ⟩ := pushforwardStructureSheafMap_quotient_of_isPullback I n g a H
  let e := eqToIso (Stacks.Algebraization.completionFunctor_obj X I E n) ≪≫
    eqToIso (congrArg (Stacks.Algebraization.idealPowerQuotient I (n + 1)) hE) ≪≫ Q
  refine ⟨e, ?_⟩
  cases E with
  | mk E hcoh =>
    dsimp only at hE
    subst E
    have hinner : eqToHom (Stacks.Algebraization.completionFunctor_obj X I
        ⟨Stacks.Morphisms.pushforwardStructureSheaf B.hom, hcoh⟩ n).symm ≫ e.hom = Q.hom := by
      simp only [e, Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hinner).trans
      (hQ.trans (Category.id_comp _).symm))


private lemma etale_of_finiteLocallyFree_lift_tower
    (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence]
    (A : AlgebraicGeometry.FiniteEtaleOver (I ^ 1).subscheme)
    (V : Over X) [Stacks.Morphisms.IsFiniteLocallyFree V.hom]
    (g : ∀ n, (idealPowerTowerOver I A).obj n ⟶ V)
    (hg : ∀ n, IsPullback (g n).left
      (finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A n).hom
      V.hom (I ^ (n + 1)).subschemeι)
    (hgnat : ∀ n, (idealPowerTowerOver I A).map (homOfLE (Nat.le_succ n)) ≫
      g (n + 1) = g n) : Etale V.hom := by
  let T := idealPowerTowerOver I A
  let C := finiteEtaleTower (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A
  have (n : ℕ) : IsFinite (T.obj n).hom := isFinite_finiteEtaleTower_comp I A n
  have (n : ℕ) : FormallyUnramified (T.obj n).hom := by
    have : Etale (C n).hom := (C n).prop.2
    exact MorphismProperty.comp_mem (@FormallyUnramified) (C n).hom
      (I ^ (n + 1)).subschemeι inferInstance inferInstance
  have (n : ℕ) : IsClosedImmersion (T.map (homOfLE (Nat.le_succ n))).left := by
    have : IsClosedImmersion (idealPowerInclusion I n) :=
      (idealPowerInclusion_isThickening I n).1
    have ht := MorphismProperty.of_isPullback
      (finiteEtaleTowerStep_isPullback (idealPowerInclusion I)
        (idealPowerInclusion_isThickening I) A n).flip
        (inferInstance : IsClosedImmersion (idealPowerInclusion I n))
    have hl : (T.map (homOfLE (Nat.le_succ n))).left = finiteEtaleTowerStep
        (idealPowerInclusion I) (idealPowerInclusion_isThickening I) A n := by
      simp only [T, idealPowerTowerOver, finiteEtaleTowerOver,
        Functor.ofSequence_map_homOfLE_succ, Over.homMk_left]
      rfl
    rw [hl]
    exact ht
  let P := overSelfProduct V
  have : Stacks.Morphisms.IsFiniteLocallyFree P.hom := finiteLocallyFree_overSelfProduct V
  let E : FiniteLocallyFreeCoherent X :=
    ⟨⟨Stacks.Morphisms.pushforwardStructureSheaf V.hom,
      Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X _⟩,
      inferInstance⟩
  let F : FiniteLocallyFreeCoherent X :=
    ⟨⟨Stacks.Morphisms.pushforwardStructureSheaf P.hom,
      Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X _⟩,
      inferInstance⟩
  let Q n := Stacks.Morphisms.pushforwardStructureSheaf (overSelfProduct (T.obj n)).hom
  let q n := pushforwardStructureSheafMap (overSelfProductMap (g n))
  have hP n := isPullback_overSelfProductMap (I ^ (n + 1)).subschemeι
    (C n).hom rfl (g n) (hg n)
  have heE n : ∃ e : ((Stacks.Algebraization.completionFunctor X I).obj E.obj).obj.obj (op n) ≅
      Stacks.Morphisms.pushforwardStructureSheaf (T.obj n).hom,
      Stacks.Algebraization.completionProjection X I E.obj n ≫ e.hom =
        pushforwardStructureSheafMap (g n) := by
    obtain ⟨e, he⟩ := exists_completionPushforwardIso I n E.obj rfl (g n) (C n).hom (hg n)
    exact ⟨e, he.trans (Category.id_comp _)⟩
  have heF n : ∃ e : ((Stacks.Algebraization.completionFunctor X I).obj F.obj).obj.obj (op n) ≅ Q n,
      Stacks.Algebraization.completionProjection X I F.obj n ≫ e.hom = q n := by
    obtain ⟨e, he⟩ := exists_completionPushforwardIso I n F.obj rfl
      (overSelfProductMap (g n)) (pullback.fst (T.obj n).hom (T.obj n).hom ≫ (C n).hom) (hP n)
    exact ⟨e, he.trans (Category.id_comp _)⟩
  choose eE heE using heE
  choose eF heF using heF
  let t n := pushforwardStructureSheafMap
    (overSelfProductMap (T.map (homOfLE (Nat.le_succ n))))
  have ht n : q (n + 1) ≫ t n = q n := by
    have hcomp : overSelfProductMap ((idealPowerTowerOver I A).map (homOfLE (Nat.le_succ n)) ≫
          g (n + 1)) =
        overSelfProductMap ((idealPowerTowerOver I A).map (homOfLE (Nat.le_succ n))) ≫
          overSelfProductMap (g (n + 1)) := by
      ext
      rw [Over.comp_left, overSelfProductMap_left, overSelfProductMap_left,
        overSelfProductMap_left]
      exact (pullback.map_comp ..).symm
    rw [← pushforwardStructureSheafMap_comp, ← hcomp, hgnat]
  have hQ n : Stacks.Algebraization.idealPowerMultiple I (n + 1) (Q n) = ⊥ := by
    show Stacks.Algebraization.idealPowerMultiple I (n + 1)
      (Stacks.Morphisms.pushforwardStructureSheaf
        (pullback.fst (T.obj n).hom (T.obj n).hom ≫ ((C n).hom ≫ (I ^ (n + 1)).subschemeι))) = ⊥
    have hk := (pullback.fst (T.obj n).hom (T.obj n).hom ≫ (C n).hom).le_ker_comp
      (I ^ (n + 1)).subschemeι
    rw [Scheme.IdealSheafData.ker_subschemeι] at hk
    have hb := idealPowerMultiple_pushforwardStructureSheaf_eq_bot
      ((pullback.fst (T.obj n).hom (T.obj n).hom ≫ (C n).hom) ≫ (I ^ (n + 1)).subschemeι)
      I (n + 1) hk
    have e2 : pullback.fst (T.obj n).hom (T.obj n).hom ≫ ((C n).hom ≫ (I ^ (n + 1)).subschemeι) =
        (pullback.fst (T.obj n).hom (T.obj n).hom ≫ (C n).hom) ≫ (I ^ (n + 1)).subschemeι :=
      (Category.assoc _ _ _).symm
    rw [e2]
    exact hb
  obtain ⟨η, hη⟩ := exists_map_of_quotientMaps X I (finiteLocallyFreeUnit X) F Q eF t
    (fun n => by rw [heF, heF]; exact ht n) hQ
    (fun n => overSeparabilityMap (T.obj n))
    (fun n => overSeparabilityMap_naturality (T.map (homOfLE (Nat.le_succ n))))
  have hηq n : η ≫ q n = overSeparabilityMap (T.obj n) := by
    rw [← heF]
    exact hη n
  apply etale_of_separabilityMap V η
  · apply hom_ext_of_quotientMaps X I (finiteLocallyFreeUnit X) E _ eE
    intro n
    rw [heE]
    have hd : pushforwardStructureSheafMap (overDiagonal V) ≫
        pushforwardStructureSheafMap (g n) =
      q n ≫ pushforwardStructureSheafMap (overDiagonal (T.obj n)) := by
      rw [← pushforwardStructureSheafMap_comp, ← pushforwardStructureSheafMap_comp,
        overDiagonal_naturality]
    calc _ = η ≫ (pushforwardStructureSheafMap (overDiagonal V) ≫
          pushforwardStructureSheafMap (g n)) := Category.assoc _ _ _
      _ = η ≫ (q n ≫ pushforwardStructureSheafMap (overDiagonal (T.obj n))) :=
          congrArg (η ≫ ·) hd
      _ = (η ≫ q n) ≫ pushforwardStructureSheafMap (overDiagonal (T.obj n)) :=
          (Category.assoc _ _ _).symm
      _ = overSeparabilityMap (T.obj n) ≫ pushforwardStructureSheafMap (overDiagonal (T.obj n)) :=
          congrArg (· ≫ pushforwardStructureSheafMap (overDiagonal (T.obj n))) (hηq n)
      _ = _ := (overSeparabilityMap_diagonal (T.obj n)).trans
          (pushforwardStructureSheafMap_unit (g n)).symm
  · apply hom_ext_of_quotientMaps X I E F Q eF
    intro n
    rw [heF]
    refine Eq.trans ?_ (zero_comp (C := X.Modules)).symm
    have hnat := multiplyBySection_naturality (overSelfProductMap (g n)) η
    rw [hηq n] at hnat
    have hf : pushforwardStructureSheafMap (overSelfProductFst V) ≫ q n =
        pushforwardStructureSheafMap (g n) ≫
          pushforwardStructureSheafMap (overSelfProductFst (T.obj n)) := by
      rw [← pushforwardStructureSheafMap_comp, ← pushforwardStructureSheafMap_comp,
        overSelfProductMap_fst]
    have hs : pushforwardStructureSheafMap (overSelfProductSnd V) ≫ q n =
        pushforwardStructureSheafMap (g n) ≫
          pushforwardStructureSheafMap (overSelfProductSnd (T.obj n)) := by
      rw [← pushforwardStructureSheafMap_comp, ← pushforwardStructureSheafMap_comp,
        overSelfProductMap_snd]
    calc _ = (pushforwardStructureSheafMap (overSelfProductFst V) -
          pushforwardStructureSheafMap (overSelfProductSnd V)) ≫
            (multiplyBySection (overSelfProduct V).hom η ≫ q n) := Category.assoc _ _ _
      _ = (pushforwardStructureSheafMap (overSelfProductFst V) -
          pushforwardStructureSheafMap (overSelfProductSnd V)) ≫
            (q n ≫ multiplyBySection (overSelfProduct (T.obj n)).hom
              (overSeparabilityMap (T.obj n))) := congrArg (_ ≫ ·) hnat
      _ = (pushforwardStructureSheafMap (overSelfProductFst V) ≫ q n -
          pushforwardStructureSheafMap (overSelfProductSnd V) ≫ q n) ≫
            multiplyBySection (overSelfProduct (T.obj n)).hom
              (overSeparabilityMap (T.obj n)) :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (Preadditive.sub_comp _ _ _))
      _ = (pushforwardStructureSheafMap (g n) ≫
            (pushforwardStructureSheafMap (overSelfProductFst (T.obj n)) -
              pushforwardStructureSheafMap (overSelfProductSnd (T.obj n)))) ≫
            multiplyBySection (overSelfProduct (T.obj n)).hom
              (overSeparabilityMap (T.obj n)) := by
          rw [hf, hs, Preadditive.comp_sub]
      _ = 0 := (Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (overSeparabilityMap_annihilates (T.obj n))).trans comp_zero)

private lemma subschemeι_eqToHom {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    I.subschemeι = eqToHom (congrArg (fun K : X.IdealSheafData => K.subscheme) h) ≫
      J.subschemeι := by
  subst J
  simp only [eqToHom_refl, Category.id_comp]

end

/-- Restriction of finite étale covers to the closed subscheme cut out by `I` is essentially
surjective when completion is an equivalence on finite locally free objects. -/
private theorem essSurj_finiteEtaleBaseChange_subschemeι_of_completion
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence] :
    (AlgebraicGeometry.finiteEtaleBaseChange I.subschemeι).EssSurj := by
  constructor
  intro A
  let e : (I ^ 1).subscheme ≅ I.subscheme := eqToIso (by rw [pow_one])
  let A₀ := (AlgebraicGeometry.finiteEtaleBaseChange e.hom).obj A
  obtain ⟨V, hV, g, hg, hgnat⟩ := exists_finiteLocallyFree_lift_tower X I A₀
  let := hV
  have : Etale V.hom := etale_of_finiteLocallyFree_lift_tower X I A₀ V g hg hgnat
  have : IsFinite V.hom :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      V.hom).mp hV).1
  let W : AlgebraicGeometry.FiniteEtaleOver X :=
    MorphismProperty.Over.mk ⊤ V.hom ⟨inferInstance, inferInstance⟩
  let p : A₀.left ⟶ A.left := CategoryTheory.Limits.pullback.fst A.hom e.hom
  have : IsIso p := inferInstanceAs (IsIso (CategoryTheory.Limits.pullback.fst A.hom e.hom))
  let j : A₀.left ≅ A.left := asIso p
  let a : A.left ⟶ V.left := j.inv ≫ (g 0).left
  have H₀ : IsPullback (g 0).left A₀.hom V.hom (I ^ 1).subschemeι := hg 0
  have H : IsPullback a A.hom V.hom I.subschemeι := by
    apply H₀.of_iso j (Iso.refl _) e (Iso.refl _)
    · exact (j.hom_inv_id_assoc (g 0).left).symm
    · exact CategoryTheory.Limits.pullback.condition.symm
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id, e, eqToIso.hom] using
        (subschemeι_eqToHom (I := I ^ 1) (J := I) (pow_one I))
  exact ⟨W, ⟨(MorphismProperty.Over.isoMk (A := A)
    (B := (AlgebraicGeometry.finiteEtaleBaseChange I.subschemeι).obj W)
    H.isoPullback H.isoPullback_hom_snd).symm⟩⟩

/-- **[Stacks, Tag 0EL9], for the closed subscheme cut out by an ideal sheaf.** Let `X` be a
Noetherian scheme and `I` a quasi-coherent ideal sheaf. If the completion functor
`Coh(𝒪_X) ⥤ Coh(X, I)` is an equivalence on the full subcategories of finite locally free
objects, then restriction of finite étale covers to the closed subscheme cut out by `I` is an
equivalence. The tag is carried by the form for an arbitrary closed immersion,
`Stacks.FundamentalGroup.finiteEtaleBaseChange_isEquivalence_of_completionEquivalence`. -/
public theorem finiteEtaleBaseChange_isEquivalence_of_completion
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [(finiteLocallyFreeCompletion X I).IsEquivalence] :
    (AlgebraicGeometry.finiteEtaleBaseChange I.subschemeι).IsEquivalence := by
  obtain ⟨hFF⟩ :=
    fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFiniteLocallyFree
      I.subschemeι (fun E F hE hF => by
        rw [I.ker_subschemeι]
        exact completion_map_bijective_of_equivalence X I E F hE hF)
  exact { faithful := hFF.faithful, full := hFF.full,
          essSurj := essSurj_finiteEtaleBaseChange_subschemeι_of_completion X I }

/-- **[Stacks, Tag 0EL9].** Let `X` be a Noetherian scheme and `Y ⊆ X` a closed subscheme with
ideal sheaf `I`. If the completion functor `Coh(𝒪_X) ⥤ Coh(X, I)`, `ℱ ↦ ℱ^∧`, is an equivalence
on the full subcategories of finite locally free objects, then the restriction functor
`FÉt_X ⥤ FÉt_Y`, `U ↦ U ×_X Y`, is an equivalence.

The closed subscheme is given by a closed immersion `i : Y ⟶ X` with ideal sheaf `I = ker i`.
Restriction factors as restriction to the closed subscheme cut out by `I` followed by base change
along the isomorphism from `Y` onto it, and the second is an equivalence because an isomorphism is
a thickening ([Stacks, Tag 0BQB]); the first is
`Stacks.FundamentalGroup.finiteEtaleBaseChange_isEquivalence_of_completion`. -/
@[stacks 0EL9 "completion an equivalence on finite locally free objects implies restriction \
FEt_X to FEt_Y an equivalence"]
public theorem finiteEtaleBaseChange_isEquivalence_of_completionEquivalence
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    [(finiteLocallyFreeCompletion X i.ker).IsEquivalence] :
    (AlgebraicGeometry.finiteEtaleBaseChange i).IsEquivalence := by
  have h₁ : (AlgebraicGeometry.finiteEtaleBaseChange i.ker.subschemeι).IsEquivalence :=
    finiteEtaleBaseChange_isEquivalence_of_completion X i.ker
  have h₂ : (AlgebraicGeometry.finiteEtaleBaseChange i.toImage).IsEquivalence :=
    AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_isThickening i.toImage
      ⟨inferInstance, (asIso i.toImage).hom.surjective⟩
  have e : AlgebraicGeometry.finiteEtaleBaseChange i ≅
      AlgebraicGeometry.finiteEtaleBaseChange i.ker.subschemeι ⋙
        AlgebraicGeometry.finiteEtaleBaseChange i.toImage :=
    MorphismProperty.Over.pullbackComp i.toImage i.ker.subschemeι i
      (Scheme.Hom.toImage_imageι i).symm
  exact Functor.isEquivalence_of_iso e.symm

end Stacks.FundamentalGroup

end
