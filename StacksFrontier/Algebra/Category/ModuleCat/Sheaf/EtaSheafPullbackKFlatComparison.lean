module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackComposition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentDerivedFlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.SingleUnitComposition

/-!
# The derived comparison of décalages under a pullback, at a complex of torsion-free modules

Let `f : X ⟶ Y` be a morphism of ringed spaces, `I ⊆ 𝒪_Y` and `J ⊆ 𝒪_X` invertible ideal sheaves
with a compatible identification `f^*I ≅ J`, and let `P^•` be a complex of `I`-torsion-free
`𝒪_Y`-modules whose termwise pullback is `J`-torsion free.  This file builds the comparison

`Lf^*[η_I P^•] ⟶ [f^*(η_I P^•)] ⟶ [η_J(f^* P^•)]`

in `D(𝒪_X)` — the comparison of Stacks 06YJ between the derived and the degreewise pullback,
followed by the class of the chain-level comparison
`Stacks.IdealTorsion.Eta.transportedPullbackEtaMap` — and proves the two facts about it that the
proof of Stacks 0F9X rests on:

* it is an isomorphism exactly when, for one (equivalently every) quasi-isomorphism
  `r : R^• ⟶ η_I P^•` out of a K-flat complex, the map of complexes
  `f^*R^• ⟶ f^*(η_I P^•) ⟶ η_J(f^* P^•)` is a quasi-isomorphism; and
* it is natural in `P^•`, so that being an isomorphism transfers along quasi-isomorphisms between
  K-flat complexes.

No flatness of `f` is assumed.

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackEtaKFlatComparison`: the comparison in `D(𝒪_X)`.

## Main results

* `Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_naturality`: the chain-level comparison is
  natural in the complex.
* `Stacks.IdealTorsion.Eta.isIso_pullbackEtaKFlatComparison_iff`: the comparison is an
  isomorphism iff the chain-level comparison precomposed with a K-flat resolution is a
  quasi-isomorphism.
* `Stacks.IdealTorsion.Eta.isIso_pullbackEtaKFlatComparison_iff_of_quasiIso`: the property of
  being an isomorphism transfers along a quasi-isomorphism of K-flat complexes.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.IdealTorsion.Eta

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  (J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
  (κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
  [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property J]
  (e : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    ((pullbackFunctor f).obj I) J)
  [Mono ι] [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)] [Mono κ]
  (he : e.hom ≫ κ = pullbackIdealIncl f I ι)

/-! ### Naturality of the chain-level comparison -/

section Naturality

variable {C : Type*} [Category C]

/-- Two pastings of two squares along a common first projection agree when the bottom
composites do. -/
private theorem comp_chain₂_eq {A₀ A₁ A₂ A₁' P₀ P₁ P₂ P₁' : C} {m₁ : A₀ ⟶ A₁} {m₂ : A₁ ⟶ A₂}
    {m₁' : A₀ ⟶ A₁'} {m₂' : A₁' ⟶ A₂} {p₀ : A₀ ⟶ P₀} {p₁ : A₁ ⟶ P₁} {p₂ : A₂ ⟶ P₂}
    {p₁' : A₁' ⟶ P₁'} {q₁ : P₀ ⟶ P₁} {q₂ : P₁ ⟶ P₂} {q₁' : P₀ ⟶ P₁'} {q₂' : P₁' ⟶ P₂}
    (h₁ : m₁ ≫ p₁ = p₀ ≫ q₁) (h₂ : m₂ ≫ p₂ = p₁ ≫ q₂)
    (h₁' : m₁' ≫ p₁' = p₀ ≫ q₁') (h₂' : m₂' ≫ p₂ = p₁' ≫ q₂') (h : q₁ ≫ q₂ = q₁' ≫ q₂') :
    (m₁ ≫ m₂) ≫ p₂ = (m₁' ≫ m₂') ≫ p₂ := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, h, ← Category.assoc, ← h₁',
    Category.assoc, ← h₂', Category.assoc]

end Naturality

variable {F G : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
  (u : F ⟶ G)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
  (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
  (hF'' : ∀ n : ℤ, IsIdealTorsionFree X κ ((pullbackComplex f F).X n))
  (hG : ∀ n : ℤ, IsIdealTorsionFree Y ι (G.X n))
  (hG' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f G).X n))
  (hG'' : ∀ n : ℤ, IsIdealTorsionFree X κ ((pullbackComplex f G).X n))

/-- **The chain-level comparison of décalages is natural in the complex.**  Both composites are
maps into the fibre products defining the terms of `η_J(f^* G^•)`, and their projections agree by
the naturality of the interchange of the pullback with the ideal powers. -/
theorem transportedPullbackEtaMap_naturality :
    pullbackComplexMap f (etaMap Y I ι u hF hG) ≫
        transportedPullbackEtaMap f I ι J κ e he G hG hG' hG'' =
      transportedPullbackEtaMap f I ι J κ e he F hF hF' hF'' ≫
        etaMap X J κ (pullbackComplexMap f u)
          hF'' hG'' := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine pullback.hom_ext
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ?_ ?_
  · exact comp_chain₂_eq (functor_square (pullbackFunctor f) (etaMap_fst Y I ι u hF hG n))
      (transportedPullbackEtaMap_f_fst f I ι J κ e he G hG hG' hG'' n)
      (transportedPullbackEtaMap_f_fst f I ι J κ e he F hF hF' hF'' n)
      (etaMap_fst X J κ (pullbackComplexMap f u) hF'' hG'' n)
      (pullbackIdealPowerTransportIso_natural f I J e n (u.f n))
  · exact comp_chain₂_eq (functor_square (pullbackFunctor f) (etaMap_snd Y I ι u hF hG n))
      (transportedPullbackEtaMap_f_snd f I ι J κ e he G hG hG' hG'' n)
      (transportedPullbackEtaMap_f_snd f I ι J κ e he F hF hF' hF'' n)
      (etaMap_snd X J κ (pullbackComplexMap f u) hF'' hG'' n)
      (pullbackIdealPowerTransportIso_natural f I J e (n + 1) (u.f (n + 1)))

/-! ### The comparison in the derived category

The derived pullback and its comparison with the degreewise pullback are typed over the
`structureSheafRing` spelling of the structure sheaf, while the décalage and all the facts about
it (in particular Stacks 0F8P) are typed over `Stacks.SheafOfModules.Tensor.ringSheaf _.sheaf`.
The two are the same category, but instance search and `rw` do not cross between them, so the
derived pullback and the comparison are first restated at the décalage spelling, once, by
ascription. -/

section Derived

/-- The derived pullback, at the spelling of the structure sheaf used by the décalage files. -/
abbrev etaDerivedPullback (f : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  derivedPullback f

/-- The comparison of Stacks 06YJ between the derived and the degreewise pullback, at the
spelling of the structure sheaf used by the décalage files. -/
def etaPullbackComparisonOnComplex (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ) :
    (etaDerivedPullback f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj (pullbackComplex f K) :=
  derivedPullbackComparisonOnComplex f K

/-- Naturality of the comparison of Stacks 06YJ. -/
theorem etaPullbackComparisonOnComplex_naturality (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (φ : K ⟶ L) :
    (etaDerivedPullback f).map (DerivedCategory.Q.map φ) ≫ etaPullbackComparisonOnComplex f L =
      etaPullbackComparisonOnComplex f K ≫
        DerivedCategory.Q.map (pullbackComplexMap f φ) :=
  StacksDraft.UnitPullbackComposition.derivedPullbackComparisonOnComplex_naturality f φ

/-- The comparison of Stacks 06YJ is invertible at a K-flat complex. -/
theorem isIso_etaPullbackComparisonOnComplex (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K) :
    IsIso (etaPullbackComparisonOnComplex f K) :=
  Stacks.NaiveCotangentDerivedFlatBaseChange.isIso_derivedPullbackComparisonOnComplex_of_kFlat f K
    hK

/-- **The degreewise pullback of a quasi-isomorphism of K-flat complexes is a
quasi-isomorphism.**  In the naturality square of the comparison of Stacks 06YJ the comparisons
at the two K-flat complexes are invertible, and so is `Lf^*[u]`. -/
theorem quasiIso_pullbackComplex_map_of_kFlat (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (φ : K ⟶ L) [QuasiIso φ]
    (hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y K)
    (hL : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y L) :
    QuasiIso (pullbackComplexMap f φ) := by
  have := isIso_etaPullbackComparisonOnComplex f K hK
  have := isIso_etaPullbackComparisonOnComplex f L hL
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso,
    ← isIso_comp_left_iff (etaPullbackComparisonOnComplex f K),
    ← etaPullbackComparisonOnComplex_naturality]
  infer_instance

end Derived

/-- **The comparison of décalages under a pullback, in the derived category**:
`Lf^*[η_I P^•] ⟶ [f^*(η_I P^•)] ⟶ [η_J(f^* P^•)]`, the comparison of Stacks 06YJ followed by the
class of the chain-level comparison. -/
def pullbackEtaKFlatComparison :
    (etaDerivedPullback f).obj (DerivedCategory.Q.obj (etaObj Y I ι F hF)) ⟶
      DerivedCategory.Q.obj (etaObj X J κ (pullbackComplex f F) hF'') :=
  etaPullbackComparisonOnComplex f (etaObj Y I ι F hF) ≫
    DerivedCategory.Q.map (transportedPullbackEtaMap f I ι J κ e he F hF hF' hF'')

/-- **The comparison is an isomorphism iff the chain-level comparison, precomposed with a K-flat
resolution of the décalage, is a quasi-isomorphism.**  By the naturality of the comparison of
Stacks 06YJ, the derived comparison precomposed with `Lf^*[r]` is the comparison at the K-flat
complex `R^•`, which is invertible, followed by the class of `f^*r` and of the chain-level
comparison; and `Lf^*[r]` is invertible since `r` is a quasi-isomorphism. -/
theorem isIso_pullbackEtaKFlatComparison_iff
    {R : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (r : R ⟶ etaObj Y I ι F hF) [QuasiIso r]
    (hR : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y R) :
    IsIso (pullbackEtaKFlatComparison f I ι J κ e he hF hF' hF'') ↔
      QuasiIso (pullbackComplexMap f r ≫
        transportedPullbackEtaMap f I ι J κ e he F hF hF' hF'') := by
  have hcR := isIso_etaPullbackComparisonOnComplex f R hR
  have key : (etaDerivedPullback f).map (DerivedCategory.Q.map r) ≫
      pullbackEtaKFlatComparison f I ι J κ e he hF hF' hF'' =
      etaPullbackComparisonOnComplex f R ≫
        DerivedCategory.Q.map (pullbackComplexMap f r ≫
          transportedPullbackEtaMap f I ι J κ e he F hF hF' hF'') := by
    rw [pullbackEtaKFlatComparison, ← Category.assoc, etaPullbackComparisonOnComplex_naturality,
      Category.assoc, Functor.map_comp]
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso,
    ← isIso_comp_left_iff ((etaDerivedPullback f).map (DerivedCategory.Q.map r)), key,
    isIso_comp_left_iff]

/-- **The comparison is natural in the complex.** -/
theorem pullbackEtaKFlatComparison_naturality :
    (etaDerivedPullback f).map (DerivedCategory.Q.map (etaMap Y I ι u hF hG)) ≫
        pullbackEtaKFlatComparison f I ι J κ e he hG hG' hG'' =
      pullbackEtaKFlatComparison f I ι J κ e he hF hF' hF'' ≫
        DerivedCategory.Q.map (etaMap X J κ (pullbackComplexMap f u) hF'' hG'') := by
  rw [pullbackEtaKFlatComparison, pullbackEtaKFlatComparison, ← Category.assoc,
    etaPullbackComparisonOnComplex_naturality, Category.assoc, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp,
    transportedPullbackEtaMap_naturality f I ι J κ e he u hF hF' hF'' hG hG' hG'']

/-- **Being an isomorphism transfers along a quasi-isomorphism of K-flat complexes.**  The two
vertical maps in the naturality square are invertible: `η_I u` is a quasi-isomorphism by
Stacks 0F8P, and `f^* u` is one because `u` is a quasi-isomorphism of K-flat complexes; then
`η_J(f^* u)` is a quasi-isomorphism by Stacks 0F8P again. -/
theorem isIso_pullbackEtaKFlatComparison_iff_of_quasiIso [QuasiIso u]
    (hFk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y F)
    (hGk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y G) :
    IsIso (pullbackEtaKFlatComparison f I ι J κ e he hF hF' hF'') ↔
      IsIso (pullbackEtaKFlatComparison f I ι J κ e he hG hG' hG'') := by
  have : IsIso (DerivedCategory.Q.map (etaMap Y I ι u hF hG)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_etaMap Y I ι u hF hG inferInstance)
  have : IsIso (DerivedCategory.Q.map (etaMap X J κ (pullbackComplexMap f u) hF'' hG'')) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (quasiIso_etaMap X J κ _ hF'' hG'' (quasiIso_pullbackComplex_map_of_kFlat f u hFk hGk))
  rw [← isIso_comp_right_iff _
      (DerivedCategory.Q.map (etaMap X J κ (pullbackComplexMap f u) hF'' hG'')),
    ← pullbackEtaKFlatComparison_naturality f I ι J κ e he u hF hF' hF'' hG hG' hG'',
    isIso_comp_left_iff]

end Stacks.IdealTorsion.Eta

end
