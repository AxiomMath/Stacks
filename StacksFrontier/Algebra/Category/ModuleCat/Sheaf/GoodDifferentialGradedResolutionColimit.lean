module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# The colimit step in the construction of a flat resolution

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `M` be a right differential graded `A`-module. The source constructs a quasi-isomorphism
`P → M` with `P` good by building a tower

`P₀ → P₁ → P₂ → ⋯ → M`

in which every `Pᵢ` is good, every `Hⁿ(Pᵢ) → Hⁿ(M)` is surjective, and the kernel of
`Hⁿ(Pᵢ) → Hⁿ(M)` is annihilated by `Hⁿ(Pᵢ) → Hⁿ(Pᵢ₊₁)`, and then setting `P = colim Pᵢ`.

This file proves the last step, for a tower taken as a hypothesis: the colimit of such a tower
maps to `M` by a quasi-isomorphism, and inherits flatness.

## Main definitions

* `Stacks.SequentialColimit.constColimitDesc` is the canonical map out of the colimit of a
  constant diagram over `ℕ`, and `Stacks.SequentialColimit.isIso_constColimitDesc` says it is an
  isomorphism.
* `SheafOfModules.DifferentialGradedModule.isColimit_toCochainComplex_mapCocone`: forgetting the
  module structure of a right differential graded module, keeping its complex, carries a colimit
  cocone over `ℕ` to a colimit cocone.

## Main results

* `Stacks.SequentialColimit.preservesColimitsOfShape_homologyFunctor`: **in an abelian category
  whose colimits of a given shape are exact, cohomology commutes with those colimits.**
* `Stacks.SequentialColimit.isIso_colimit_desc_of_epi_of_killsKernels` and
  `Stacks.SequentialColimit.isIso_desc_of_epi_of_killsKernels`: **the map to the target of a
  cocone out of the colimit of a sequence is an isomorphism** as soon as the cocone is an
  epimorphism at stage `0` and, at every stage, every map killed by the cocone is killed by the
  transition to the next stage, in an abelian category with exact colimits over `ℕ`.
* `SheafOfModules.DifferentialGradedModule.isColimit_homology_mapCocone`: **`Hⁿ(colim Pᵢ) =
  colim Hⁿ(Pᵢ)`** for a sequence of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_of_isColimit_nat`: flatness
  of the underlying graded module and K-flatness pass to a colimit over `ℕ`.
* `SheafOfModules.DifferentialGradedModule.quasiIso_desc_of_tower`: **the map from a chosen
  colimit of a tower with the two cohomological properties above to `M` is a
  quasi-isomorphism.**
* `SheafOfModules.DifferentialGradedModule.exists_quasiIso_of_tower`: **Tag 0FSH, the colimit
  step.** The colimit of a tower with the two cohomological properties above maps to `M` by a
  quasi-isomorphism and is flat as a graded module and K-flat.

## References

* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w x t m v u

namespace Stacks.SequentialColimit

/-! ### Cohomology commutes with exact colimits -/

section HomologyColimit

variable {B : Type u} [Category.{v} B] [Abelian B]

/-- The comparison natural isomorphism between applying homology pointwise to a diagram of short
complexes and taking the homology of the short complex of functors it corresponds to under
`CategoryTheory.ShortComplex.FunctorEquivalence`. -/
noncomputable def shortComplexHomologyCompIso {J : Type w} [Category.{x} J]
    (E : J ⥤ ShortComplex B) :
    E ⋙ ShortComplex.homologyFunctor B ≅
      ((ShortComplex.FunctorEquivalence.inverse J B).obj E).homology :=
  NatIso.ofComponents
    (fun j ↦ ((ShortComplex.FunctorEquivalence.inverse J B).obj E).mapHomologyIso
      ((evaluation J B).obj j))
    (fun {j j'} φ ↦ by
      change ShortComplex.homologyMap
            (((ShortComplex.FunctorEquivalence.inverse J B).obj E).mapNatTrans
              ((evaluation J B).map φ)) ≫
          (((ShortComplex.FunctorEquivalence.inverse J B).obj E).mapHomologyIso
            ((evaluation J B).obj j')).hom
        = (((ShortComplex.FunctorEquivalence.inverse J B).obj E).mapHomologyIso
            ((evaluation J B).obj j)).hom ≫
          ((evaluation J B).map φ).app
            ((ShortComplex.FunctorEquivalence.inverse J B).obj E).homology
      rw [NatTrans.app_homology, Iso.hom_inv_id_assoc])

/-- The homology of a short complex commutes with colimits of a shape whose colimits are
exact. -/
lemma preservesColimitsOfShape_shortComplexHomologyFunctor {J : Type w} [Category.{x} J]
    [HasColimitsOfShape J B] [HasExactColimitsOfShape J B] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor B) := by
  refine ⟨fun {E} ↦ preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone E) ?_⟩
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (shortComplexHomologyCompIso E)
      (colimit.cocone ((ShortComplex.FunctorEquivalence.inverse J B).obj E).homology)).symm
      (colimit.isColimit _))
    (Cocone.ext (((ShortComplex.FunctorEquivalence.inverse J B).obj E).mapHomologyIso
      (colim : (J ⥤ B) ⥤ B)).symm (fun j ↦ ?_))
  set T := (ShortComplex.FunctorEquivalence.inverse J B).obj E with hT
  let i : (evaluation J B).obj j ⟶ (colim : (J ⥤ B) ⥤ B) :=
    { app := fun X ↦ colimit.ι X j
      naturality := fun X Y f ↦ by simp }
  have key : i.app T.homology = (T.mapHomologyIso ((evaluation J B).obj j)).inv ≫
      ShortComplex.homologyMap (T.mapNatTrans i) ≫ (T.mapHomologyIso colim).hom :=
    NatTrans.app_homology i T
  change ((T.mapHomologyIso ((evaluation J B).obj j)).hom ≫ i.app T.homology) ≫
      (T.mapHomologyIso (colim : (J ⥤ B) ⥤ B)).inv
    = ShortComplex.homologyMap (T.mapNatTrans i)
  rw [key]
  simp

/-- The short complex attached to a homological complex in a fixed degree commutes with
colimits. -/
lemma preservesColimitsOfShape_homologicalComplexShortComplexFunctor {J : Type w} [Category.{x} J]
    [HasColimitsOfShape J B] {I : Type*} (cs : ComplexShape I) (i : I) :
    PreservesColimitsOfShape J (HomologicalComplex.shortComplexFunctor B cs i) :=
  ⟨fun {_} ↦ ⟨fun hs ↦ ⟨ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves (HomologicalComplex.eval B cs _) hs)
    (isColimitOfPreserves (HomologicalComplex.eval B cs _) hs)
    (isColimitOfPreserves (HomologicalComplex.eval B cs _) hs)⟩⟩⟩

/-- **In an abelian category whose colimits of a given shape are exact, cohomology in a fixed
degree commutes with those colimits.** -/
lemma preservesColimitsOfShape_homologyFunctor {J : Type w} [Category.{x} J]
    [HasColimitsOfShape J B] [HasExactColimitsOfShape J B] {I : Type*} (cs : ComplexShape I)
    (i : I) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor B cs i) :=
  have := preservesColimitsOfShape_homologicalComplexShortComplexFunctor (B := B) (J := J) cs i
  have := preservesColimitsOfShape_shortComplexHomologyFunctor (B := B) (J := J)
  preservesColimitsOfShape_of_natIso (HomologicalComplex.homologyFunctorIso B cs i).symm

end HomologyColimit

/-! ### The colimit of a constant diagram over `ℕ` -/

section Const

variable {B : Type u} [Category.{v} B] [HasColimitsOfShape ℕ B]

/-- The canonical map from the colimit of the constant diagram on `X` over `ℕ` to `X`. -/
noncomputable def constColimitDesc (X : B) : colimit ((Functor.const ℕ).obj X) ⟶ X :=
  colimit.desc _ (Cocone.mk X { app := fun _ ↦ 𝟙 X, naturality := by intros; simp })

/-- Each coprojection of the colimit of the constant diagram on `X` over `ℕ`, followed by
`constColimitDesc X`, is the identity of `X`. -/
@[simp]
lemma colimit_ι_constColimitDesc (X : B) (m : ℕ) :
    colimit.ι ((Functor.const ℕ).obj X) m ≫ constColimitDesc X = 𝟙 X :=
  colimit.ι_desc _ m

/-- **The colimit of a constant diagram over `ℕ` is its value**:
`Stacks.SequentialColimit.constColimitDesc` is an isomorphism. -/
lemma isIso_constColimitDesc (X : B) : IsIso (constColimitDesc X) := by
  refine ⟨colimit.ι ((Functor.const ℕ).obj X) 0, ?_, ?_⟩
  · refine colimit.hom_ext fun m ↦ ?_
    have hw : colimit.ι ((Functor.const ℕ).obj X) m
        = colimit.ι ((Functor.const ℕ).obj X) 0 := by
      simpa using colimit.w ((Functor.const ℕ).obj X) (homOfLE (Nat.zero_le m))
    rw [hw, ← Category.assoc, colimit_ι_constColimitDesc]
    simp
  · simp

end Const

/-! ### The colimit of a sequence with vanishing transition maps -/

section Zero

variable {B : Type u} [Category.{v} B] [HasZeroMorphisms B] [HasColimitsOfShape ℕ B]

/-- **The colimit of a sequence all of whose transition maps vanish is zero.** -/
lemma isZero_colimit_of_map_succ_eq_zero (K : ℕ ⥤ B)
    (h : ∀ m : ℕ, K.map (homOfLE m.le_succ) = 0) : IsZero (colimit K) := by
  have hi : ∀ m : ℕ, colimit.ι K m = 0 := by
    intro m
    rw [← colimit.w K (homOfLE m.le_succ), h m, zero_comp]
  rw [IsZero.iff_id_eq_zero]
  exact colimit.hom_ext fun m ↦ by rw [Category.comp_id, comp_zero, hi]

end Zero

/-! ### The map out of a sequential colimit -/

section Main

variable {B : Type u} [Category.{v} B] [Abelian B] [HasColimitsOfShape ℕ B]
  [HasExactColimitsOfShape ℕ B]

/-- **The map out of the colimit of a sequence induced by a cocone is an isomorphism** when the
cocone is an epimorphism at stage `0` and, at every stage, a morphism killed by the cocone is
killed by the transition to the next stage. -/
lemma isIso_colimit_desc_of_epi_of_killsKernels (G : ℕ ⥤ B) (c : Cocone G)
    (hepi : Epi (c.ι.app 0))
    (hkill : ∀ (j : ℕ) {Z : B} (g : Z ⟶ G.obj j), g ≫ c.ι.app j = 0 →
      g ≫ G.map (homOfLE j.le_succ) = 0) :
    IsIso (colimit.desc G c) := by
  have hcolim : PreservesFiniteLimits (colim : (ℕ ⥤ B) ⥤ B) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  have hcond : ∀ j : ℕ, (kernel.ι c.ι).app j ≫ c.ι.app j = 0 := by
    intro j
    simpa only [NatTrans.comp_app, Limits.zero_app] using
      NatTrans.congr_app (kernel.condition c.ι) j
  have hk : ∀ j : ℕ, (kernel c.ι).map (homOfLE j.le_succ) = 0 := by
    intro j
    rw [← cancel_mono ((kernel.ι c.ι).app (j + 1)), zero_comp,
      (kernel.ι c.ι).naturality (homOfLE j.le_succ)]
    exact hkill j _ (hcond j)
  have hker : IsZero (kernel (colim.map c.ι)) :=
    (isZero_colimit_of_map_succ_eq_zero (kernel c.ι) hk).of_iso
      (PreservesKernel.iso (colim : (ℕ ⥤ B) ⥤ B) c.ι).symm
  have hmono : Mono (colim.map c.ι) := by
    refine (Preadditive.mono_iff_cancel_zero _).mpr fun Z g hg ↦ ?_
    calc g = kernel.lift (colim.map c.ι) g hg ≫ kernel.ι (colim.map c.ι) :=
          (kernel.lift_ι _ _ _).symm
      _ = 0 := by rw [hker.eq_zero_of_tgt (kernel.lift (colim.map c.ι) g hg), zero_comp]
  have hiso : IsIso (constColimitDesc c.pt) := isIso_constColimitDesc c.pt
  have hfac : colimit.desc G c = colim.map c.ι ≫ constColimitDesc c.pt := by
    refine colimit.hom_ext fun j ↦ ?_
    rw [colimit.ι_desc, ← Category.assoc, colimit.ι_map, Category.assoc,
      colimit_ι_constColimitDesc]
    simp
  have hepi' : Epi (colimit.desc G c) := by
    have h0 : Epi (colimit.ι G 0 ≫ colimit.desc G c) := by rwa [colimit.ι_desc]
    exact epi_of_epi (colimit.ι G 0) (colimit.desc G c)
  have hmono' : Mono (colimit.desc G c) := by rw [hfac]; infer_instance
  exact isIso_of_mono_of_epi _

/-- `Stacks.SequentialColimit.isIso_colimit_desc_of_epi_of_killsKernels` for an arbitrary colimit
cocone rather than the one of the colimit API: the morphism induced by a cocone out of the point
of a colimit cocone over a sequence is an isomorphism under the same two hypotheses. -/
lemma isIso_desc_of_epi_of_killsKernels (G : ℕ ⥤ B) {s : Cocone G} (hs : IsColimit s)
    (c : Cocone G) (hepi : Epi (c.ι.app 0))
    (hkill : ∀ (j : ℕ) {Z : B} (g : Z ⟶ G.obj j), g ≫ c.ι.app j = 0 →
      g ≫ G.map (homOfLE j.le_succ) = 0) :
    IsIso (hs.desc c) := by
  have h := isIso_colimit_desc_of_epi_of_killsKernels G c hepi hkill
  have hi : ∀ j : ℕ, colimit.ι G j ≫
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit G) hs).hom = s.ι.app j := fun j ↦
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G) hs j
  have hfac : colimit.desc G c
      = (IsColimit.coconePointUniqueUpToIso (colimit.isColimit G) hs).hom ≫ hs.desc c := by
    refine colimit.hom_ext fun j ↦ ?_
    rw [colimit.ι_desc, ← Category.assoc, hi, hs.fac]
  rw [hfac] at h
  exact IsIso.of_isIso_comp_left
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit G) hs).hom (hs.desc c)

end Main

end Stacks.SequentialColimit

namespace SheafOfModules

namespace DifferentialGradedModule

section Exact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The equivalence between `AsSmall.{m} ℕ`, a shape in the module universe, and `ℕ`. -/
noncomputable def asSmallNatEquiv : (AsSmall.{m} ℕ) ≌ ℕ := AsSmall.equiv.symm

/-- **Colimits over `ℕ` of sheaves of modules are exact.** -/
theorem hasExactColimitsOfShape_nat (R : Sheaf J RingCat.{t})
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    HasExactColimitsOfShape ℕ (SheafOfModules.{m} R) :=
  HasExactColimitsOfShape.of_domain_equivalence _ asSmallNatEquiv.{m}

end Exact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-! ### Colimits over `ℕ` -/

/-- **Right differential graded modules have colimits over `ℕ`.** -/
theorem hasColimitsOfShape_nat :
    HasColimitsOfShape ℕ (DifferentialGradedModule.{t, m, m} A) :=
  have : HasColimitsOfSize.{m, m} (DifferentialGradedModule.{t, m, m} A) := hasColimitsOfSize
  hasColimitsOfShape_of_equivalence asSmallNatEquiv.{m}

/-- **Forgetting the module structure of a right differential graded module, keeping its complex,
carries a colimit cocone over `ℕ` to a colimit cocone.** -/
noncomputable def isColimit_toCochainComplex_mapCocone
    {G : ℕ ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone G} (hc : IsColimit c) :
    IsColimit ((toCochainComplex A).mapCocone c) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n ↦ ?_
  have h2 : PreservesColimitsOfShape ℕ
      (GradedModule.pieceFunctor A.toGradedAlgebra n :
        GradedModule.{t, m, m} A.toGradedAlgebra ⥤ SheafOfModules.{m} (toRingCat J Osharp)) :=
    have h1 : PreservesColimitsOfSize.{m, m}
        (GradedModule.pieceFunctor A.toGradedAlgebra n :
          GradedModule.{t, m, m} A.toGradedAlgebra ⥤ SheafOfModules.{m} (toRingCat J Osharp)) :=
      GradedModule.pieceFunctor_preservesColimitsOfSize' n
    (preservesSmallestColimits_of_preservesColimits _).preservesColimitsOfShape
  have h4 : PreservesColimitsOfShape ℕ
      (forgetToGradedModule A ⋙ GradedModule.pieceFunctor A.toGradedAlgebra n :
        DifferentialGradedModule.{t, m, m} A ⥤ SheafOfModules.{m} (toRingCat J Osharp)) :=
    comp_preservesColimitsOfShape _ _
  exact isColimitOfPreserves
    (forgetToGradedModule A ⋙ GradedModule.pieceFunctor A.toGradedAlgebra n) hc

/-- **`Hⁿ(colim Pᵢ) = colim Hⁿ(Pᵢ)`** for a sequence of right differential graded modules. -/
noncomputable def isColimit_homology_mapCocone
    {G : ℕ ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone G} (hc : IsColimit c) (n : ℤ) :
    IsColimit ((HomologicalComplex.homologyFunctor (SheafOfModules.{m} (toRingCat J Osharp))
      (ComplexShape.up ℤ) n).mapCocone ((toCochainComplex A).mapCocone c)) :=
  have := hasExactColimitsOfShape_nat.{t, m} (toRingCat J Osharp)
  have := Stacks.SequentialColimit.preservesColimitsOfShape_homologyFunctor
    (B := SheafOfModules.{m} (toRingCat J Osharp)) (J := ℕ) (ComplexShape.up ℤ) n
  isColimitOfPreserves _ (isColimit_toCochainComplex_mapCocone hc)

/-- **Flatness of the underlying graded module and K-flatness pass to a colimit over `ℕ` of right
differential graded modules.** -/
theorem isGradedFlat_and_isKFlat_of_isColimit_nat
    {G : ℕ ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone G} (hc : IsColimit c)
    (hG : ∀ i : ℕ, RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded (G.obj i)) ∧ RelativeTensor.IsKFlat (G.obj i)) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded c.pt) ∧
      RelativeTensor.IsKFlat c.pt :=
  isGradedFlat_and_isKFlat_of_isColimit
    (K := asSmallNatEquiv.{m}.functor ⋙ G)
    (c := c.whisker asSmallNatEquiv.{m}.functor)
    (hc.whiskerEquivalence asSmallNatEquiv.{m}) fun _ ↦ hG _

/-! ### Tag 0FSH, the colimit step -/

/-- **The map from a colimit of a tower to a compatible cocone is a quasi-isomorphism.** Let
`P₀ → P₁ → ⋯` be a sequence of right differential graded `A`-modules, let `d` be a colimit
cocone on it and let `c` be any cocone on it, say with point `M`. If `Hⁿ(P₀) → Hⁿ(M)` is an
epimorphism for every `n` and every morphism into `Hⁿ(Pᵢ)` killed by the map to `Hⁿ(M)` is killed
by the map to `Hⁿ(Pᵢ₊₁)`, then the induced map `d.pt ⟶ M` is a quasi-isomorphism. -/
theorem quasiIso_desc_of_tower (P : ℕ ⥤ DifferentialGradedModule.{t, m, m} A)
    {d : Cocone P} (hd : IsColimit d) (c : Cocone P)
    (hepi : ∀ n : ℤ,
      Epi (HomologicalComplex.homologyMap (c.ι.app 0).toHomologicalComplex n))
    (hkill : ∀ (n : ℤ) (i : ℕ) {Z : SheafOfModules.{m} (toRingCat J Osharp)}
      (g : Z ⟶ (P.obj i).complex.homology n),
      g ≫ HomologicalComplex.homologyMap (c.ι.app i).toHomologicalComplex n = 0 →
        g ≫ HomologicalComplex.homologyMap
          (P.map (homOfLE i.le_succ)).toHomologicalComplex n = 0) :
    QuasiIso (hd.desc c).toHomologicalComplex := by
  rw [quasiIso_iff_isIso_homologyMap]
  intro n
  have hHc := isColimit_homology_mapCocone hd n
  have hdesc : hHc.desc ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{m} (toRingCat J Osharp)) (ComplexShape.up ℤ) n).mapCocone
        ((toCochainComplex A).mapCocone c))
      = HomologicalComplex.homologyMap (hd.desc c).toHomologicalComplex n := by
    refine (hHc.uniq _ _ fun j ↦ ?_).symm
    change HomologicalComplex.homologyMap ((toCochainComplex A).map (d.ι.app j)) n ≫
      HomologicalComplex.homologyMap ((toCochainComplex A).map (hd.desc c)) n = _
    rw [← HomologicalComplex.homologyMap_comp, ← (toCochainComplex A).map_comp, hd.fac]
    rfl
  rw [← hdesc]
  have := hasExactColimitsOfShape_nat.{t, m} (toRingCat J Osharp)
  exact Stacks.SequentialColimit.isIso_desc_of_epi_of_killsKernels
    (P ⋙ toCochainComplex A ⋙ HomologicalComplex.homologyFunctor
      (SheafOfModules.{m} (toRingCat J Osharp)) (ComplexShape.up ℤ) n)
    hHc _ (hepi n) fun i _ g hg ↦ hkill n i g hg

/-- **Tag 0FSH, the colimit step.** *"Let `(C, O)` be a ringed site. Let `A` be a sheaf of
differential graded algebras on `(C, O)`. Let `M` be a differential graded `A`-module. There
exists a homomorphism `P → M` of differential graded `A`-modules which is a quasi-isomorphism
and with `P` good."*

Given a sequence `P₀ → P₁ → ⋯` of right differential graded `A`-modules with a compatible family
of maps to `M = c.pt` such that

* every `Pᵢ` is flat as a graded module and K-flat,
* `Hⁿ(P₀) → Hⁿ(M)` is an epimorphism for every `n`, and
* every morphism into `Hⁿ(Pᵢ)` which the map to `Hⁿ(M)` kills is killed by the map to
  `Hⁿ(Pᵢ₊₁)`,

the colimit `P = colim Pᵢ` with its induced map to `M` is a quasi-isomorphism, and `P` is flat as
a graded module and K-flat. The flatness conclusion is conditions (1) and (2) of the definition
of good (Tag 0FSA). -/
theorem exists_quasiIso_of_tower (P : ℕ ⥤ DifferentialGradedModule.{t, m, m} A) (c : Cocone P)
    (hflat : ∀ i : ℕ, RelativeTensor.IsGradedFlat
      (GradedModule.ofDifferentialGraded (P.obj i)) ∧ RelativeTensor.IsKFlat (P.obj i))
    (hepi : ∀ n : ℤ,
      Epi (HomologicalComplex.homologyMap (c.ι.app 0).toHomologicalComplex n))
    (hkill : ∀ (n : ℤ) (i : ℕ) {Z : SheafOfModules.{m} (toRingCat J Osharp)}
      (g : Z ⟶ (P.obj i).complex.homology n),
      g ≫ HomologicalComplex.homologyMap (c.ι.app i).toHomologicalComplex n = 0 →
        g ≫ HomologicalComplex.homologyMap
          (P.map (homOfLE i.le_succ)).toHomologicalComplex n = 0) :
    ∃ (Q : DifferentialGradedModule.{t, m, m} A) (f : Q ⟶ c.pt),
      QuasiIso f.toHomologicalComplex ∧
        RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
          RelativeTensor.IsKFlat Q := by
  have hcol : HasColimitsOfShape ℕ (DifferentialGradedModule.{t, m, m} A) :=
    hasColimitsOfShape_nat (A := A)
  exact ⟨colimit P, (colimit.isColimit P).desc c,
    quasiIso_desc_of_tower P (colimit.isColimit P) c hepi hkill,
    isGradedFlat_and_isKFlat_of_isColimit_nat (colimit.isColimit P) hflat⟩

end DifferentialGradedModule

end SheafOfModules

end
