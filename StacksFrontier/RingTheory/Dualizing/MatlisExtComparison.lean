module

public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
public import StacksFrontier.RingTheory.Dualizing.MaximalIdealPowerTorsion
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison

import all StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds

/-!
# The Ext-level Matlis comparison on finite-length modules

Let `(A, 𝔪, κ)` be a Noetherian local ring with a normalized dualizing complex `ω`, and let
`E` be an injective hull of `κ`. On finite-length modules the derived Hom into `ω` is Matlis
duality into `E`, and taking degree-zero cohomology turns that identification into a natural
isomorphism `Ext^0_A(N, ω) ≅ Hom_A(N, E)` of `A`-modules. This file packages that comparison as
`Dualizing.NaturalMatlisExtComparison` and records the one place the dualizing complex is used
below degree zero: the comparison map induced by removing `𝔪`-power torsion is bijective in
every negative degree, because the torsion submodule has finite length and so contributes
nothing outside degree zero.

## Main results

* `Dualizing.exists_naturalMatlisExtComparison` — the natural degree-zero Matlis comparison
  exists for a normalized dualizing complex and an injective hull of the residue field.
* `Dualizing.bijective_extComparison_quotientMaximalIdealPowerTorsion` — below degree zero the
  canonical `Ext` comparison for the quotient by `𝔪`-power torsion is bijective.

## Implementation notes

The comparison is assembled from `Dualizing.derivedHomFiniteLengthIsoMatlisDual` by taking
degree-zero cohomology and composing with `Dualizing.extIntoOmegaAtLinearEquiv`; naturality is
checked against `Dualizing.extPrecomp`, which is precomposition on `Ext`. The negative-degree
bijectivity reuses the torsion-vanishing comparison already proved for the degree bounds.

## References

* [Stacks Project, proof of Lemma 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Lemma 0AW0](https://stacks.math.columbia.edu/tag/0AW0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing


/-- Precomposition on `Ext` is composition with the single-complex image of the map; this is
the named form of `Dualizing.extPrecomp`, used so that no proof below has to unfold it. -/
private lemma extPrecomp_apply_comp {A : Type u} [CommRing A]
    {N N' : Type (max v u)} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (f : N →ₗ[A] N')
    (ω : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ)
    (x : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A N')) ω i) :
    extPrecomp f ω i x =
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map (ModuleCat.ofHom f) ≫ x := by
  change (ShiftedHom.mk₀ 0 rfl _).comp x (add_zero i) = _
  exact ShiftedHom.mk₀_comp _ _ _ _

/-- The degree-zero comparison induced by a derived-Hom Matlis isomorphism. -/
private noncomputable def finiteLengthExtMatlisEquiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (E : Type (max v u)) [AddCommGroup E] [Module A E]
    (e : derivedHomFiniteLengthFunctor A ω ≅
      matlisDualFiniteLengthFunctor A (ModuleCat.of A E))
    (N : Type (max v u)) [AddCommGroup N] [Module A N]
    (hN : IsFiniteLength A N) :
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
        (ModuleCat.of A N)) ω 0 ≃ₗ[A] (N →ₗ[A] E) := by
  let Ncat : FiniteLengthModules.{u, v} A := ⟨ModuleCat.of A N, hN⟩
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A N)
  let D := (dualizingDerivedHomFunctor A ω).obj (.op X)
  let Ecat : ModuleCat.{max v u} A := ModuleCat.of A E
  let H : ModuleCat.{max v u} A :=
    (MonoidalClosed.internalHom.obj (Opposite.op (ModuleCat.of A N))).obj Ecat
  let eD : D ≅ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj H :=
    e.app (Opposite.op Ncat)
  let h0 := DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0
  let e0 := h0.mapIso eD ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max v u} A) 0).app H
  let eH : (H : Type (max v u)) ≃ₗ[A] (N →ₗ[A] E) :=
    ModuleCat.homLinearEquiv (M := ModuleCat.of A N) (N := Ecat) (S := A)
  exact (extIntoOmegaAtLinearEquiv A ω 0 (ModuleCat.of A N)).trans
    (e0.toLinearEquiv.trans eH)

/-- For a normalized dualizing complex and an injective hull of the residue field, the
degree-zero Matlis comparison exists naturally on finite-length modules. -/
public lemma exists_naturalMatlisExtComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (hω : IsNormalizedDualizingComplex ω)
    (E : Type (max v u)) [AddCommGroup E] [Module A E]
    (j : (ModuleCat.uliftFunctor.{v} A).obj
      (ModuleCat.of A (ResidueField A)) ⟶ ModuleCat.of A E) [Mono j]
    (hj : Module.IsInjectiveHull j) :
    Nonempty (NaturalMatlisExtComparison A ω E) := by
  obtain ⟨e⟩ := derivedHomFiniteLengthIsoMatlisDual A ω hω (ModuleCat.of A E) j hj
  exact ⟨{
    equiv := fun N _ _ hN => (finiteLengthExtMatlisEquiv A ω E e N hN).toAddEquiv
    naturality := fun N N' _ _ _ _ hN hN' f x => by
      let Ncat : FiniteLengthModules.{u, v} A := ⟨ModuleCat.of A N, hN⟩
      let N'cat : FiniteLengthModules.{u, v} A := ⟨ModuleCat.of A N', hN'⟩
      let fcat : Ncat ⟶ N'cat := ObjectProperty.homMk (ModuleCat.ofHom f)
      let H := (MonoidalClosed.internalHom.obj (.op (ModuleCat.of A N))).obj
        (ModuleCat.of A E)
      let H' := (MonoidalClosed.internalHom.obj (.op (ModuleCat.of A N'))).obj
        (ModuleCat.of A E)
      let p : H' ⟶ H := (MonoidalClosed.internalHom.map
        (ModuleCat.ofHom f).op).app (ModuleCat.of A E)
      let h0 := DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0
      let s0 := DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
      let a := (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max v u} A) 0).hom
      change ModuleCat.homLinearEquiv (S := A)
          (a.app H (h0.map (e.hom.app (.op Ncat))
            (extIntoOmegaAtLinearEquiv A ω 0 (ModuleCat.of A N)
              (extPrecomp f ω 0 x)))) =
        (ModuleCat.homLinearEquiv (S := A)
          (a.app H' (h0.map (e.hom.app (.op N'cat))
            (extIntoOmegaAtLinearEquiv A ω 0 (ModuleCat.of A N') x)))).comp f
      rw [extPrecomp_apply_comp, extIntoOmegaAtLinearEquiv_naturality]
      have hn := congrArg h0.map (e.hom.naturality fcat.op)
      simp only [Functor.map_comp] at hn
      have hn' := ConcreteCategory.congr_hom hn
        (extIntoOmegaAtLinearEquiv A ω 0 (ModuleCat.of A N') x)
      change h0.map (e.hom.app (.op Ncat))
          (h0.map ((dualizingDerivedHomFunctor A ω).map
            (s0.map (ModuleCat.ofHom f)).op)
            (extIntoOmegaAtLinearEquiv A ω 0 (ModuleCat.of A N') x)) =
        h0.map (s0.map p) (h0.map (e.hom.app (.op N'cat))
          (extIntoOmegaAtLinearEquiv A ω 0 (ModuleCat.of A N') x)) at hn'
      rw [hn']
      have ha := ConcreteCategory.congr_hom (a.naturality p)
        (h0.map (e.hom.app (.op N'cat))
          (extIntoOmegaAtLinearEquiv A ω 0 (ModuleCat.of A N') x))
      change a.app H (h0.map (s0.map p) _) = p (a.app H' _) at ha
      rw [ha]
      rfl
  }⟩

/-- Below degree zero, the canonical Ext comparison after removing maximal-ideal-power torsion
is an isomorphism. -/
public lemma bijective_extComparison_quotientMaximalIdealPowerTorsion
    (A : Type u) (M : Type (max v u)) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (ω : DerivedCategory (ModuleCat.{max v u} A))
    (hω : IsNormalizedDualizingComplex ω)
    (i : ℤ) (hi : i < 0) :
    Function.Bijective (extComparison M ω i) :=
  extComparison_bijective_of_torsion_vanishing ω i
    (finiteLength_ext_subsingleton_of_ne_zero ω hω
      (isFiniteLength_maximalIdealPowerTorsion A M) (by lia))
    (finiteLength_ext_subsingleton_of_ne_zero ω hω
      (isFiniteLength_maximalIdealPowerTorsion A M) (by lia))

end Dualizing
