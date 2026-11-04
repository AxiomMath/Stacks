module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafIdealTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafTwistAutomorphism

/-!
# The comparison of décalages under a pullback, for an arbitrary presentation of the pulled-back
ideal

Let `f : X ⟶ Y` be a morphism of ringed spaces, `I ⊆ 𝒪_Y` an invertible ideal sheaf, and
`J ⊆ 𝒪_X` an invertible ideal sheaf identified with the pulled-back ideal `f^*I ⟶ 𝒪_X` by an
isomorphism `e : f^*I ≅ J` compatible with the two inclusions.  For a complex `F^•` of
`I`-torsion-free `𝒪_Y`-modules whose termwise pullback is `J`-torsion free, this file names the
chain-level comparison

`f^*(η_I F^•) ⟶ η_J(f^* F^•)`,

the canonical comparison `Stacks.IdealTorsion.Eta.pullbackEtaMap` into `η_{f^*I}` followed by the
transport `Stacks.IdealTorsion.Eta.IdealCongr.etaMap` along `e`, and records how it acts on the
two projections of the fibre products defining the terms of the décalage, and that it is natural
in the complex.

No flatness is assumed anywhere in this file.

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackIdealPowerTransportIso`: the interchange
  `f^*(I^{⊗ n} ⊗ M) ≅ J^{⊗ n} ⊗ f^*M` of a pullback with an integer ideal power, followed by the
  transport along `e`.
* `Stacks.IdealTorsion.Eta.transportedPullbackEtaMap`: the comparison of complexes
  `f^*(η_I F^•) ⟶ η_J(f^* F^•)`.

## Main results

* `Stacks.IdealTorsion.Eta.pullbackIdealPowerTransportIso_natural` and
  `pullbackIdealPowerTransportIso_idealPowerIncl`: the interchange is natural in the module and
  respects the inclusion of consecutive ideal powers.
* `Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_f_fst` and `_f_snd`: the comparison acts on
  the two projections by the interchange.
* `Stacks.IdealTorsion.Eta.transportedPullbackEtaMap_naturality`: the comparison is natural in
  the complex.

## Implementation notes

The pullback functor is typed over a different spelling of the structure sheaf of rings from the
décalage files, so composites mixing the two carry different `Category` instance terms and `rw`
cannot match `Category.assoc` in them; such squares are assembled by `Eq.trans`.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

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

/-- The termwise pullback of a map of complexes, typed at the spelling of the structure sheaf used
by the décalage files.  It is a definition rather than an abbreviation so that `rw` does not see
the `structureRingSheaf` spelling of `Stacks.RingedSpace.pullbackFunctor` underneath. -/
def pullbackComplexMap {K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ} (φ : K ⟶ L) :
    pullbackComplex f K ⟶ pullbackComplex f L :=
  ((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ

/-- In degree `n`, the termwise pullback of `φ` is the pullback of `φ.f n`. -/
theorem pullbackComplexMap_f {K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ} (φ : K ⟶ L)
    (n : ℤ) : (pullbackComplexMap f φ).f n = (pullbackFunctor f).map (φ.f n) := rfl

/-- **The interchange of a pullback with an integer ideal power, transported to `J`**:
`f^*(I^{⊗ n} ⊗ M) ≅ J^{⊗ n} ⊗ f^*M`.  It is `Stacks.IdealTorsion.Eta.pullbackIdealPowerIso`
followed by `Stacks.IdealTorsion.Eta.IdealCongr.powerIso` along `e`. -/
def pullbackIdealPowerTransportIso (n : ℤ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    (pullbackFunctor f).obj (idealPowerTerm Y I n M) ≅
      idealPowerTerm X J n ((pullbackFunctor f).obj M) :=
  pullbackIdealPowerIso f I n M ≪≫
    IdealCongr.powerIso X ((pullbackFunctor f).obj I) J e n ((pullbackFunctor f).obj M)

/-- Two commuting squares placed side by side compose to a commuting square. -/
private theorem comp_comp_eq_of_squares {C : Type*} [Category C] {a b c d a' d' : C}
    {x : a ⟶ b} {A : b ⟶ c} {B : c ⟶ d} {A' : a ⟶ a'} {P : a' ⟶ c} {B' : a' ⟶ d'}
    {y : d' ⟶ d} (h₁ : x ≫ A = A' ≫ P) (h₂ : P ≫ B = B' ≫ y) :
    x ≫ (A ≫ B) = (A' ≫ B') ≫ y := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Two commuting squares placed one above the other compose to a commuting square. -/
private theorem comp_comp_eq_of_squares_stacked {C : Type*} [Category C] {a b c d e g : C}
    {x : a ⟶ b} {T : b ⟶ c} {z : c ⟶ d} {z' : b ⟶ e} {B : e ⟶ d} {w : a ⟶ g} {A : g ⟶ e}
    (h₁ : T ≫ z = z' ≫ B) (h₂ : x ≫ z' = w ≫ A) :
    (x ≫ T) ≫ z = w ≫ (A ≫ B) := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]

/-- The transported interchange is natural in the module. -/
theorem pullbackIdealPowerTransportIso_natural (n : ℤ)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)} (a : M ⟶ N) :
    (pullbackFunctor f).map (idealPowerMap Y I n a) ≫
        (pullbackIdealPowerTransportIso f I J e n N).hom =
      (pullbackIdealPowerTransportIso f I J e n M).hom ≫
        idealPowerMap X J n ((pullbackFunctor f).map a) :=
  comp_comp_eq_of_squares (pullbackIdealPowerIso_natural f I n a)
    (IdealCongr.powerIso_natural X ((pullbackFunctor f).obj I) J e n ((pullbackFunctor f).map a))

/-- The transported interchange respects the inclusion of consecutive ideal powers. -/
theorem pullbackIdealPowerTransportIso_idealPowerIncl
    (he : e.hom ≫ κ = pullbackIdealIncl f I ι) (n : ℤ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    (pullbackFunctor f).map (idealPowerIncl Y I ι n M) ≫
        (pullbackIdealPowerTransportIso f I J e n M).hom =
      (pullbackIdealPowerTransportIso f I J e (n + 1) M).hom ≫
        idealPowerIncl X J κ n ((pullbackFunctor f).obj M) :=
  comp_comp_eq_of_squares (map_idealPowerIncl f I ι n M)
    (IdealCongr.powerIso_idealPowerIncl X ((pullbackFunctor f).obj I) J
      (pullbackIdealIncl f I ι) κ e he n ((pullbackFunctor f).obj M))

variable [Mono ι] [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)] [Mono κ]
  (he : e.hom ≫ κ = pullbackIdealIncl f I ι)

/-- **The comparison of décalages under a pullback, transported to `J`**:
`f^*(η_I F^•) ⟶ η_J(f^* F^•)`.  It is `Stacks.IdealTorsion.Eta.pullbackEtaMap` followed by the
transport `Stacks.IdealTorsion.Eta.IdealCongr.etaMap` along `e`. -/
def transportedPullbackEtaMap
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hF'' : ∀ n : ℤ, IsIdealTorsionFree X κ ((pullbackComplex f F).X n)) :
    pullbackComplex f (etaObj Y I ι F hF) ⟶ etaObj X J κ (pullbackComplex f F) hF'' :=
  pullbackEtaMap f I ι F hF hF' ≫
    IdealCongr.etaMap X ((pullbackFunctor f).obj I) J (pullbackIdealIncl f I ι) κ e he
      (pullbackComplex f F) hF' hF''

variable (F : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
  (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
  (hF'' : ∀ n : ℤ, IsIdealTorsionFree X κ ((pullbackComplex f F).X n))

/-- The transported comparison on the first projection. -/
theorem transportedPullbackEtaMap_f_fst (n : ℤ) :
    (transportedPullbackEtaMap f I ι J κ e he F hF hF' hF'').f n ≫
        etaFst X J κ (pullbackComplex f F) n =
      (pullbackFunctor f).map (etaFst Y I ι F n) ≫
        (pullbackIdealPowerTransportIso f I J e n (F.X n)).hom :=
  comp_comp_eq_of_squares_stacked
    (IdealCongr.etaTermMap_fst X ((pullbackFunctor f).obj I) J (pullbackIdealIncl f I ι) κ e
      he (pullbackComplex f F) n) (pullbackEtaTermMap_fst f I ι F n)

/-- The transported comparison on the second projection. -/
theorem transportedPullbackEtaMap_f_snd (n : ℤ) :
    (transportedPullbackEtaMap f I ι J κ e he F hF hF' hF'').f n ≫
        etaSnd X J κ (pullbackComplex f F) n =
      (pullbackFunctor f).map (etaSnd Y I ι F n) ≫
        (pullbackIdealPowerTransportIso f I J e (n + 1) (F.X (n + 1))).hom :=
  comp_comp_eq_of_squares_stacked
    (IdealCongr.etaTermMap_snd X ((pullbackFunctor f).obj I) J (pullbackIdealIncl f I ι) κ e
      he (pullbackComplex f F) n) (pullbackEtaTermMap_snd f I ι F n)

/-- The transported comparison depends on the identification of ideals only through its value. -/
theorem transportedPullbackEtaMap_congr_iso
    {e₁ e₂ : Iso (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
      ((pullbackFunctor f).obj I) J} (h : e₁ = e₂) (he₁ : e₁.hom ≫ κ = pullbackIdealIncl f I ι)
    (he₂ : e₂.hom ≫ κ = pullbackIdealIncl f I ι) :
    transportedPullbackEtaMap f I ι J κ e₁ he₁ F hF hF' hF'' =
      transportedPullbackEtaMap f I ι J κ e₂ he₂ F hF hF' hF'' := by
  subst h; rfl

end Stacks.IdealTorsion.Eta

end
