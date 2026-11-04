module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationDerivedMap
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedDerivedBaseChange
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.SingleUnitComposition

/-!
# The lower horizontal arrow of the derived base-change diagram of Stacks 0G7U

Let `g : X' ⟶ X` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)`, put `f'ᵢ = g^♯(fᵢ)`,
and for an `𝒪_X`-module `ℱ` write `ℱ' = g^*ℱ`.  Let `ℱ^•`, resp. `(ℱ')^•`, be the extended
alternating Čech complex of [Stacks, Tag 0G7I] of `ℱ, f₁, …, f_c`, resp. `ℱ', f'₁, …, f'_c`.

`Stacks.Perfect.SupportedDerivedBaseChange.derivedBaseChangeSquare` proves that the derived
diagram of [Stacks, Tag 0G7U] commutes for *any* lower horizontal arrow `Lg^*(ℱ^•) ⟶ (ℱ')^•`
and *any* down arrow `Lg^*ℱ ⟶ ℱ'` compatible with the augmentations of [Stacks, Tag 0G7L].
This file builds the pair the remark itself writes down, proves that compatibility for it, and
instantiates the diagram — which finishes it.

The lower horizontal arrow is the composite `Lg^*(ℱ^•) ⟶ g^*(ℱ^•) ⟶ (ℱ')^•` of the canonical
comparison of [Stacks, Tag 06YJ] read at a cochain complex
(`Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex`) with the comparison
`Stacks.Perfect.CechBaseChange.extendBaseChange` of the two Čech complexes.  The down arrow is
that same comparison at the complex concentrated in degree `0`, which the library already has as
`AlgebraicGeometry.RingedSpaceThickening.derivedPullbackSingleObj`.

The compatibility is an identity in the derived category, but all its content is the chain-level
identity between `extendBaseChange` followed by the augmentation of `(ℱ')^•` and the degreewise
inverse image of the augmentation of `ℱ^•`; and that in turn is a statement in degree `0`, where
both Čech complexes carry the coefficient module itself and both augmentations are the identity.

## Which of the remark's two diagrams this is

[Stacks, Tag 0G7U] displays two diagrams.  The one finished here is the SECOND one, the derived
diagram, which the remark states "without assuming `ℱ` is quasi-coherent"; it is the one the
source proves first.  The FIRST diagram — the quasi-coherent one, on the cohomology sheaves in
degree `c`, with the class maps `c_{f₁,…,f_c}` of [Stacks, Tag 0G7Q] as its vertical arrows — is
NOT in this file and is still outstanding.  The source obtains it from the derived diagram "by
looking at this diagram on cohomology sheaves in degree `c`" together with the compatibility of
the construction of [Stacks, Tag 0G7Q] with pullbacks, so `derivedBaseChangeSquare_cech` below is
its input.

## Main definitions

* `Stacks.Perfect.CechDerivedBaseChange.cechDerivedBaseChange`: **the lower horizontal arrow
  `Lg^*(ℱ^•) ⟶ (ℱ')^•` of [Stacks, Tag 0G7U]**.

## Main results

* `Stacks.Perfect.CechDerivedBaseChange.cechDerivedBaseChange_comp_augmentation`: **the
  augmentation compatibility.**  The lower horizontal arrow followed by the augmentation of
  `(ℱ')^•` is `Lg^*` of the augmentation of `ℱ^•` followed by the down arrow.  This is the
  hypothesis `derivedBaseChangeSquare` is stated against.
* `Stacks.Perfect.CechDerivedBaseChange.derivedBaseChangeSquare_cech`: **the derived diagram of
  [Stacks, Tag 0G7U] commutes for the remark's own two arrows.**
* `Stacks.Perfect.CechDerivedBaseChange.cplxBaseChange_comp_augmentationComplex`: the
  `ℕ`-graded chain-level identity the compatibility rests on — the comparison of the two Čech
  complexes commutes with their projections onto the coefficient module in degree `0`.
* `Stacks.Perfect.CechDerivedBaseChange.extendBaseChange_comp_augmentationExtend`: the same
  identity in the `ℤ`-grading, for the maps `augmentation` is the localization of.
* `Stacks.Perfect.CechDerivedBaseChange.derivedPullbackSingleObj_eq`: the down arrow is the
  comparison of [Stacks, Tag 06YJ] at the complex concentrated in degree `0`.
* `Stacks.Perfect.CechDerivedBaseChange.mapHomologicalComplexExtendIso_inv_comp_extendSingleIso`:
  the two ways of identifying the degreewise image of an extended single complex with a single
  complex agree.

## Implementation notes

The `ℕ`-graded identity is checked degreewise.  In a positive degree both composites land in a
zero object.  In degree `0` the projection of the Čech complex onto its coefficient module is
the identity — `(data e G).zeroIso` is `Iso.refl` and
`HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0` is too — so both composites are the
identity of `g^*ℱ`; the only step that is not formal is `Functor.map_id` for `g^*`.

`rw` and `simp only` check their results at `implicit` transparency, and the types met here are
spelled in two definitionally but not reducibly equal ways: the Čech complex is `cplx e G` on one
side and `(extendedAlternatingCech e G).complex` on the other, and the two spellings carry two
`Quiver` instance paths, so even `HomologicalComplex.comp_f` and `CategoryTheory.Category.id_comp`
are rejected on the composites.  Every such step is therefore taken in term mode, against a
`have` in which all the objects are universally quantified in one ambient category — `comp0`,
`cancel`, `glue`, `glue3` below — which is the recipe
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedDerivedBaseChange.lean`
already uses.  For the same reason the two `ℤ`-graded statements are phrased with
`ComplexShape.embeddingUpNat_f_zero` rather than `rfl`: a proof of
`ComplexShape.embeddingUpNat.f 0 = 0` that is literally `rfl` makes the surrounding
`HomologicalComplex.extendSingleIso` ill-typed at `implicit` transparency and every rewrite on
it fails.

`derivedPullbackSingleObj` and `derivedPullbackComparisonOnComplex` are the same composite
except that the latter carries one more factor,
`DerivedCategory.Qh` of a component of `CategoryTheory.Functor.mapHomotopyCategoryFactors`.  That
component is an identity, but only definitionally: its source and target are
`(quotient ⋙ F.mapHomotopyCategory c).obj K` and `(F.mapHomologicalComplex c ⋙ quotient).obj K`,
equal after `CategoryTheory.Quotient.lift` is unfolded, so the fact is available as a `rfl` `have`
and not to `rw`.  `derivedPullbackSingleObj_eq` records it, then kills the factor with
`CategoryTheory.Functor.map_id` — spelled out, because `Functor.map_id` resolves to the monadic
`Functor` of the core library.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.ExtendedAlternatingCech (cplx)
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation (augmentation augmentationComplex)
open Stacks.Perfect.CechBaseChange (cplxBaseChange cplxBaseChange_f_zero extendBaseChange)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)
open StacksDraft.UnitPullbackComposition (derivedPullbackComparisonOnComplex_naturality)
open AlgebraicGeometry.RingedSpaceThickening (derivedPullbackSingleObj)
open Stacks.Perfect.SupportedFraction (supportPush cechToDerivedSupport)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.SupportedDerivedBaseChange (derivedBaseChangeSquare supportedPullbackRoute
  isClosed_equationsClosedSet_pullback equationsClosedSet_pullback_subset)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechDerivedBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The degreewise image of an extended single complex is a single complex, in one way.**
Extending the complex with `A` in degree `i` along `e`, then applying `P` degreewise, then
identifying with the complex with `P(A)` in degree `i'`, can be read either by commuting `P` past
the extension (`HomologicalComplex.mapHomologicalComplexExtendIso`) and extending the
degree-`i` identification, or by identifying before extending; the two agree. -/
public theorem mapHomologicalComplexExtendIso_inv_comp_extendSingleIso {ι ι' : Type*}
    [DecidableEq ι] [DecidableEq ι'] {s : ComplexShape ι} {s' : ComplexShape ι'}
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasZeroObject C] [HasZeroObject D] (P : C ⥤ D) [P.PreservesZeroMorphisms]
    (e : s.Embedding s') (A : C) (i : ι) (i' : ι') (h : e.f i = i') :
    (HomologicalComplex.mapHomologicalComplexExtendIso P
          ((HomologicalComplex.single C s i).obj A) e).inv ≫
        HomologicalComplex.extendMap
          ((HomologicalComplex.singleMapHomologicalComplex P s i).hom.app A) e ≫
        (HomologicalComplex.extendSingleIso e (P.obj A) i i' h).hom =
      (P.mapHomologicalComplex s').map
          (HomologicalComplex.extendSingleIso e A i i' h).hom ≫
        (HomologicalComplex.singleMapHomologicalComplex P s' i').hom.app A := by
  rw [Iso.inv_comp_eq]
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = i'
  · subst hn
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      HomologicalComplex.extendMap_f _ e h,
      HomologicalComplex.extendSingleIso_hom_f e (P.obj A) i n h,
      HomologicalComplex.mapHomologicalComplexExtendIso_hom_f P _ e h,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.extendSingleIso_hom_f e A i n h,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    simp only [Functor.comp_obj, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.map_inv_hom_id_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X s' i' (P.obj A) n hn).eq_of_tgt _ _

/-- **The comparison `Lp^*(ℱ[0]) ⟶ (p^*ℱ)[0]` is the comparison of [Stacks, Tag 06YJ] at the
complex concentrated in degree `0`.**  Both sides are the same composite; the comparison on
complexes carries one further factor, the image under `DerivedCategory.Qh` of a component of
`CategoryTheory.Functor.mapHomotopyCategoryFactors`, which is an identity morphism. -/
public theorem derivedPullbackSingleObj_eq {Y Y' : RingedSpace.{u, u}} (p : Y' ⟶ Y)
    (G : ModuleSheaves Y) :
    derivedPullbackSingleObj p G =
      derivedPullbackComparisonOnComplex p
          ((HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj G) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback p) (ComplexShape.up ℤ) 0).hom.app G) := by
  have hfac : ((modulePullback p).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj G) =
      𝟙 ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ) ⋙
        (modulePullback p).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj G)) := rfl
  have hu := Eq.trans (congrArg DerivedCategory.Qh.map hfac)
    (CategoryTheory.Functor.map_id DerivedCategory.Qh _)
  have hA := congrArg (derivedPullback p).map
    (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app (C := ModuleSheaves Y) 0 G)
  have glue3 : ∀ {Z₀ Z₁ Z₂ Z₃ Z₄ : DerivedCategory (ModuleSheaves Y')}
      (a a' : Z₀ ⟶ Z₁) (b : Z₁ ⟶ Z₂) (u : Z₂ ⟶ Z₂) (v : Z₂ ⟶ Z₃) (w : Z₃ ⟶ Z₄),
      a = a' → u = 𝟙 Z₂ → a ≫ b ≫ v ≫ w = (a' ≫ b ≫ u ≫ v) ≫ w := by
    intro Z₀ Z₁ Z₂ Z₃ Z₄ a a' b u v w ha hu'
    rw [ha, hu', Category.id_comp]
    simp only [Category.assoc]
  exact glue3 _ _ _ _ _ _ hA hu

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-- **The comparison of the two extended alternating Čech complexes commutes with their
projections onto the coefficient module**, in the `ℕ`-grading the complexes are built in.

Both composites are concentrated in degree `0`, the target being zero in every positive degree,
and there both are the identity of `g^*ℱ`: the projection of
[Stacks, Tag 0G7L] is the canonical identification of the degree-`0` term with the coefficient
module, which for these complexes is the identity, and the comparison of
[Stacks, Tag 0G7U] is the identity in degree `0` by
`Stacks.Perfect.CechBaseChange.cplxBaseChange_f_zero`. -/
public theorem cplxBaseChange_comp_augmentationComplex :
    cplxBaseChange g f F ≫
        augmentationComplex (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) =
      ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (augmentationComplex f F) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pullback g)
          (ComplexShape.up ℕ) 0).hom.app F := by
  have comp0 : ∀ {A B C : HomologicalComplex X'.Modules (ComplexShape.up ℕ)}
      (a : A ⟶ B) (b : B ⟶ C), (a ≫ b).f 0 = a.f 0 ≫ b.f 0 :=
    fun a b => HomologicalComplex.comp_f a b 0
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero =>
    have hz : ∀ {Y : Scheme.{u}} {d : ℕ} (e : Fin d → Γ(Y, ⊤)) (G : Y.Modules),
        (Stacks.Perfect.ExtendedAlternatingCech.extendedAlternatingCech e G).zeroIso.hom =
          𝟙 G := fun _ _ => rfl
    have hts : ∀ {Y : Scheme.{u}} (K : CochainComplex Y.Modules ℕ) (G : Y.Modules)
        (k : K.X 0 ⟶ G), ((K.toSingle₀Equiv G).symm k).f 0 = k :=
      fun _ _ k => CochainComplex.toSingle₀Equiv_symm_apply_f_zero k
    have hA : ∀ {Y : Scheme.{u}} {d : ℕ} (e : Fin d → Γ(Y, ⊤)) (G : Y.Modules),
        (augmentationComplex e G).f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 G).inv := by
      intro Y d e G
      simp only [augmentationComplex, hz]
      exact Eq.trans (hts _ _ _) rfl
    have cancel : ∀ {A B : X.Modules} (i : A ≅ B) {T : X'.Modules}
        (w : (Scheme.Modules.pullback g).obj B ⟶ T),
        (Scheme.Modules.pullback g).map i.inv ≫
            (Scheme.Modules.pullback g).map i.hom ≫ w = w := by
      intro A B i T w
      rw [← Category.assoc, ← Functor.map_comp, i.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have hl : (cplxBaseChange g f F).f 0 ≫
          (augmentationComplex (fun j => g.appTop (f j))
            ((Scheme.Modules.pullback g).obj F)).f 0 =
        (augmentationComplex (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F)).f 0 := by
      rw [cplxBaseChange_f_zero]
      exact Category.id_comp _
    refine Eq.trans (comp0 _ _) (Eq.trans hl (Eq.trans ?_ (comp0 _ _).symm))
    rw [Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    exact Eq.trans (hA _ _) (Eq.trans
      (cancel (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((Scheme.Modules.pullback g).obj F)).inv).symm
      (congrArg (fun t => (Scheme.Modules.pullback g).map t ≫
        (Scheme.Modules.pullback g).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 F).hom ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            ((Scheme.Modules.pullback g).obj F)).inv) (hA f F).symm))
  | succ p =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
      ((Scheme.Modules.pullback g).obj F) (p + 1) (by omega)).eq_of_tgt _ _

/-- **`cplxBaseChange_comp_augmentationComplex` in the `ℤ`-grading**: the comparison of the two
Čech complexes extended by zero commutes with the two maps of complexes that
`Stacks.Perfect.ExtendedAlternatingCech.Augmentation.augmentation` is the localization of.

Extending is functorial (`HomologicalComplex.extendMap_comp`), so the `ℕ`-graded identity can be
extended as it stands; moving the comparison isomorphism of
`HomologicalComplex.mapHomologicalComplexExtendIso` across it is its naturality in the complex,
and the leftover factor on single complexes is
`mapHomologicalComplexExtendIso_inv_comp_extendSingleIso`. -/
public theorem extendBaseChange_comp_augmentationExtend :
    extendBaseChange g f F ≫
        (HomologicalComplex.extendMap
            (augmentationComplex (fun j => g.appTop (f j))
              ((Scheme.Modules.pullback g).obj F)) ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
            ((Scheme.Modules.pullback g).obj F) 0 0
            ComplexShape.embeddingUpNat_f_zero).hom) =
      ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap (augmentationComplex f F)
              ComplexShape.embeddingUpNat ≫
            (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0
              ComplexShape.embeddingUpNat_f_zero).hom) ≫
        (HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pullback g)
          (ComplexShape.up ℤ) 0).hom.app F := by
  have glue : ∀ {V₀ V₁ V₂ V₃ V₄ V₅ V₆ : HomologicalComplex X'.Modules (ComplexShape.up ℤ)}
      (u : V₀ ⟶ V₁) (a₁ : V₁ ⟶ V₂) (a₂ : V₂ ⟶ V₃) (t : V₃ ⟶ V₄)
      (m₁ : V₁ ⟶ V₅) (m₂ : V₅ ⟶ V₃) (p : V₀ ⟶ V₆) (v : V₆ ⟶ V₅) (w : V₆ ⟶ V₄),
      a₁ ≫ a₂ = m₁ ≫ m₂ → u ≫ m₁ = p ≫ v → v ≫ m₂ ≫ t = w →
      u ≫ a₁ ≫ a₂ ≫ t = p ≫ w := by
    intro V₀ V₁ V₂ V₃ V₄ V₅ V₆ u a₁ a₂ t m₁ m₂ p v w h₀ h₁ h₂
    rw [← h₂, ← Category.assoc a₁, h₀]
    simp only [Category.assoc]
    rw [← Category.assoc u, h₁]
    simp only [Category.assoc]
  have hsplit := Eq.trans
    (HomologicalComplex.extendMap_comp (cplxBaseChange g f F)
      (augmentationComplex (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F))
      ComplexShape.embeddingUpNat).symm
    (Eq.trans
      (congrArg (fun φ => HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
        (cplxBaseChange_comp_augmentationComplex g f F))
      (HomologicalComplex.extendMap_comp
        (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (augmentationComplex f F))
        ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pullback g)
          (ComplexShape.up ℕ) 0).hom.app F) ComplexShape.embeddingUpNat))
  simp only [extendBaseChange, Functor.map_comp, Category.assoc]
  exact glue _ _ _ _ _ _ _ _ _ hsplit
    (HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
      (Scheme.Modules.pullback g) (cplx f F) (augmentationComplex f F)
      ComplexShape.embeddingUpNat).symm
    (mapHomologicalComplexExtendIso_inv_comp_extendSingleIso (Scheme.Modules.pullback g)
      ComplexShape.embeddingUpNat F 0 0 ComplexShape.embeddingUpNat_f_zero)

/-- **The lower horizontal arrow `Lg^*(ℱ^•) ⟶ g^*(ℱ^•) ⟶ (ℱ')^•` of the diagram of
[Stacks, Tag 0G7U]**: the canonical comparison of [Stacks, Tag 06YJ] of the derived with the
degreewise inverse image, read at the extended alternating Čech complex, followed by the
comparison `Stacks.Perfect.CechBaseChange.extendBaseChange` of the two Čech complexes. -/
public def cechDerivedBaseChange :
    (derivedPullback g.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat)) ⟶
      DerivedCategory.Q.obj ((cplx (fun j => g.appTop (f j))
        ((Scheme.Modules.pullback g).obj F)).extend ComplexShape.embeddingUpNat) :=
  derivedPullbackComparisonOnComplex g.toLRSHom.toShHom
      ((cplx f F).extend ComplexShape.embeddingUpNat) ≫
    DerivedCategory.Q.map (extendBaseChange g f F)

/-- **The lower horizontal arrow of [Stacks, Tag 0G7U] is compatible with the augmentations of
[Stacks, Tag 0G7L].**  Followed by the augmentation of `(ℱ')^•` it is `Lg^*` of the augmentation
of `ℱ^•` followed by the canonical arrow `Lg^*ℱ ⟶ g^*ℱ = ℱ'` in degree `0`.

This is the hypothesis `Stacks.Perfect.SupportedDerivedBaseChange.derivedBaseChangeSquare` is
stated against, so it is all that the remark's diagram still needed.  Both sides are the
comparison of [Stacks, Tag 06YJ] at the extended Čech complex followed by the image of a map of
complexes — the right-hand side by naturality of that comparison — so the identity reduces to
`extendBaseChange_comp_augmentationExtend`. -/
public theorem cechDerivedBaseChange_comp_augmentation :
    cechDerivedBaseChange g f F ≫
        augmentation (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) =
      (derivedPullback g.toLRSHom.toShHom).map (augmentation f F) ≫
        derivedPullbackSingleObj g.toLRSHom.toShHom F := by
  have qmap : ∀ {A B C : CochainComplex X'.Modules ℤ} (a : A ⟶ B) (b : B ⟶ C),
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map b = DerivedCategory.Q.map (a ≫ b) :=
    fun a b => (DerivedCategory.Q.map_comp a b).symm
  have glue : ∀ {W₀ W₁ W₂ W₃ W₄ W₅ : DerivedCategory X'.Modules}
      (cm : W₀ ⟶ W₁) (a : W₁ ⟶ W₂) (b : W₂ ⟶ W₃) (m : W₁ ⟶ W₄) (t : W₄ ⟶ W₃)
      (d : W₀ ⟶ W₅) (cm' : W₅ ⟶ W₄),
      a ≫ b = m ≫ t → d ≫ cm' = cm ≫ m → (cm ≫ a) ≫ b = d ≫ cm' ≫ t := by
    intro W₀ W₁ W₂ W₃ W₄ W₅ cm a b m t d cm' h₁ h₂
    rw [Category.assoc, h₁, ← Category.assoc, ← h₂, Category.assoc]
  exact Eq.trans
    (glue _ _ _ _ _ _ _
      (Eq.trans (qmap _ _) (Eq.trans
        (congrArg DerivedCategory.Q.map (extendBaseChange_comp_augmentationExtend g f F))
        (qmap _ _).symm))
      (derivedPullbackComparisonOnComplex_naturality g.toLRSHom.toShHom
        (HomologicalComplex.extendMap (augmentationComplex f F) ComplexShape.embeddingUpNat ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat F 0 0
            ComplexShape.embeddingUpNat_f_zero).hom)))
    (congrArg (fun t => (derivedPullback g.toLRSHom.toShHom).map (augmentation f F) ≫ t)
      (derivedPullbackSingleObj_eq g.toLRSHom.toShHom F).symm)

/-- **The derived diagram of [Stacks, Tag 0G7U] commutes**, for the lower horizontal arrow and
the down arrow the remark itself writes down.  This is
`Stacks.Perfect.SupportedDerivedBaseChange.derivedBaseChangeSquare` instantiated at
`cechDerivedBaseChange` and `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackSingleObj`,
whose compatibility with the augmentations of [Stacks, Tag 0G7L] is
`cechDerivedBaseChange_comp_augmentation`. -/
@[stacks 0G7U "the derived diagram of the remark, with the remark's own lower horizontal arrow \
  Lg^*F^bullet -> g^*F^bullet -> (F')^bullet and its own down arrow induced by Lg^*F -> g^*F = \
  F', for an arbitrary O_X-module F"]
public theorem derivedBaseChangeSquare_cech :
    (derivedPullback g.toLRSHom.toShHom).map
          (cechToDerivedSupport f F (isClosed_equationsClosedSet f) le_rfl) ≫
        supportedPullbackRoute g.toLRSHom.toShHom (equationsClosedSet f)
            (isClosed_equationsClosedSet f)
            ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≫
        (supportPush (isClosed_equationsClosedSet_pullback g f)).map
          (derivedPullbackSingleObj g.toLRSHom.toShHom F) =
      cechDerivedBaseChange g f F ≫
        cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
          (isClosed_equationsClosedSet_pullback g f) (equationsClosedSet_pullback_subset g f) :=
  derivedBaseChangeSquare g f F (cechDerivedBaseChange_comp_augmentation g f F)

end Stacks.Perfect.CechDerivedBaseChange

end
