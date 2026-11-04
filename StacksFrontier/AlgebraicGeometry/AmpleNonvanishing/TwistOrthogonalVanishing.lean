module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleMapNonzero
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.AmpleAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.ColimitClose.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback

/-!
# An object of `D_QCoh` orthogonal to enough modules is zero

Let `X` be a quasi-compact and quasi-separated scheme carrying an ample invertible module, and
let `𝒯` be a class of `𝒪_X`-modules large enough that every quasi-coherent `𝒪_X`-module of
finite type is a quotient of a finite direct sum of members of `𝒯`. This file proves that an
object `K` of `D_QCoh(𝒪_X)` receiving only the zero morphism from `M[-p]`, for `M` in `𝒯` and
every `p`, is itself zero.

This is the vanishing step of the proof of [Stacks, Tag 0A9V]: there `X = P^n_A` and `𝒯` is the
class of the twists `𝒪_X(d)` with `d ≤ 0`.

## The argument

By [Stacks, Tag 08DB] — in the form
`Stacks.AmpleNonvanishing.exists_quasicoherentComplex_iso_of_isAmple`, whose two hypotheses
ampleness supplies — `K` is the class of a cochain complex `H` of quasi-coherent modules. It is
enough to see that every `H^p` vanishes, and for that it is enough that the projection
`Z^p(H) ⟶ H^p(H)` is zero, since it is an epimorphism.

The cycles `Z^p(H)` are quasi-coherent (a kernel of a map of quasi-coherent modules), so by
[Stacks, Tag 01PG] they are the filtered colimit of their quasi-coherent submodules of finite
type; a morphism out of `Z^p(H)` vanishes as soon as it vanishes on each of those. Each of them
is a quotient of a finite direct sum of members of `𝒯`, so the question is whether a map
`g : M ⟶ Z^p(H)` with `M` in `𝒯` can have nonzero class in `H^p(H)`. If it did, the cochain map
`M[-p] ⟶ H` it induces would be nonzero in the derived category
(`HomologicalComplex.derivedMap_mkHomFromSingle_ne_zero`), contradicting the hypothesis.

## Main results

* `Stacks.AmpleNonvanishing.isZero_of_hom_single_eq_zero` — the statement above.

## References

* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample
open Stacks.AlgebraicGeometry.Tag01PGColimitClose
  (isColimit_finiteTypeQuasicoherentSubobjectCocone)

universe u

namespace Stacks.AmpleNonvanishing

/-- An object is zero exactly when its zero endomorphism is invertible. -/
theorem isZero_iff_isIso_zero {C : Type*} [Category C] [Limits.HasZeroMorphisms C] (Z : C) :
    IsZero Z ↔ IsIso (0 : Z ⟶ Z) :=
  ⟨fun h => (isIsoZeroSelfEquiv Z).symm ((IsZero.iff_id_eq_zero Z).1 h),
    fun h => (IsZero.iff_id_eq_zero Z).2 (isIsoZeroSelfEquiv Z h)⟩

/-- A morphism flanked by isomorphisms is zero as soon as the composite is. Stated so that
neither flank has to be known to be a monomorphism or an epimorphism, which instance search does
not supply for the component of an isomorphism. -/
theorem eq_zero_of_iso_comp_comp_iso {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {W X Y Z : C} (e : W ≅ X) {g : X ⟶ Y} (e' : Y ≅ Z) (h : e.hom ≫ g ≫ e'.hom = 0) : g = 0 := by
  have hg : g = e.inv ≫ (e.hom ≫ g ≫ e'.hom) ≫ e'.inv := by simp
  rw [hg, h, zero_comp, comp_zero]

/-- **A morphism of `D(𝒪_X)` out of an object of `D_QCoh(𝒪_X)` into a shift of another one is
zero as soon as every morphism of `D_QCoh(𝒪_X)` into that shift is.** The inclusion of
`D_QCoh(𝒪_X)` is fully faithful and commutes with the shift, so the two groups of morphisms
agree. -/
theorem hom_obj_eq_zero_of_hom_eq_zero {X : Scheme.{u}}
    (E K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (h : ∀ (p : ℤ)
      (g : E ⟶ (shiftFunctor (Stacks.Duality.quasiCoherentDerivedCategory X) p).obj K), g = 0)
    (p : ℤ) (f : E.obj ⟶ (shiftFunctor (DerivedCategory X.Modules) p).obj K.obj) : f = 0 := by
  have e := ((DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.commShiftIso p).app K
  have hg := congrArg (fun t => t.hom) (h p (ObjectProperty.homMk (f ≫ e.inv)))
  simp only [ObjectProperty.homMk_hom, ObjectProperty.zero_hom] at hg
  simpa using hg =≫ e.hom

/-- **An object of `D_QCoh(𝒪_X)` orthogonal to enough modules is zero.** Let `X` be a
quasi-compact and quasi-separated scheme carrying an ample invertible module `L`, and let `𝒯` be
a class of `𝒪_X`-modules such that every quasi-coherent `𝒪_X`-module of finite type is the
target of an epimorphism from a finite direct sum of members of `𝒯`. If the only morphism
`M[-p] ⟶ K` is zero, for every `M` in `𝒯` and every degree `p`, then `K` is zero. -/
theorem isZero_of_hom_single_eq_zero (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (𝒯 : X.Modules → Prop)
    (hgen : ∀ F : X.Modules, F.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} F →
      ∃ (r : ℕ) (M : Fin r → X.Modules), (∀ j, 𝒯 (M j)) ∧ ∃ φ : (∐ M) ⟶ F, Epi φ)
    (K : Stacks.Duality.quasiCoherentDerivedCategory X)
    (hkill : ∀ M : X.Modules, 𝒯 M → ∀ (p : ℤ)
      (f : (DerivedCategory.singleFunctor X.Modules p).obj M ⟶ K.obj), f = 0) :
    IsZero K := by
  classical
  obtain ⟨G, ⟨eK⟩⟩ := exists_quasicoherentComplex_iso_of_isAmple X L hL K
  set H : CochainComplex X.Modules ℤ :=
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G
  have hH : ∀ i : ℤ, (H.X i).IsQuasicoherent := fun i => (G.X i).property
  have hz : ∀ p : ℤ, IsZero (H.homology p) := by
    intro p
    have : (H.cycles p).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
        (H.cyclesIsKernel p (p + 1) (by simp)) (hH p) (hH (p + 1))
    have hπ : H.homologyπ p = 0 := by
      refine (isColimit_finiteTypeQuasicoherentSubobjectCocone
        (H.cycles p)).hom_ext fun Gsub => ?_
      obtain ⟨r, M, h𝒯, φ, hφ⟩ :=
        hgen (Gsub.obj : X.Modules) Gsub.property.1 Gsub.property.2
      have hterm : ∀ j : Fin r,
          (Sigma.ι M j ≫ φ ≫ Gsub.obj.arrow) ≫ H.homologyπ p = 0 := by
        intro j
        by_contra hg
        refine HomologicalComplex.derivedMap_mkHomFromSingle_ne_zero H p
          (Sigma.ι M j ≫ φ ≫ Gsub.obj.arrow) hg ?_
        have h0 := hkill (M j) (h𝒯 j) p
          (((DerivedCategory.singleFunctorIsoCompQ X.Modules p).app (M j)).hom ≫
            DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle
              ((Sigma.ι M j ≫ φ ≫ Gsub.obj.arrow) ≫ H.iCycles p) (fun k _ => by simp)) ≫
            eK.inv)
        exact eq_zero_of_iso_comp_comp_iso
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules p).app (M j)) eK.symm h0
      have hker : Gsub.obj.arrow ≫ H.homologyπ p = 0 := by
        refine (cancel_epi φ).1 (Sigma.hom_ext _ _ fun j => ?_)
        simpa only [Category.assoc, comp_zero] using hterm j
      exact hker.trans comp_zero.symm
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    refine (cancel_epi (H.homologyπ p)).mp ?_
    simp [hπ]
  have hzero : IsZero K.obj := by
    refine (isZero_iff_isIso_zero K.obj).mpr ?_
    rw [DerivedCategory.isIso_iff]
    intro p
    rw [Functor.map_zero, ← isZero_iff_isIso_zero]
    exact (hz p).of_iso
      (((DerivedCategory.homologyFunctorFactors X.Modules p).app H).symm ≪≫
        (DerivedCategory.homologyFunctor X.Modules p).mapIso eK.symm).symm
  refine (IsZero.iff_id_eq_zero K).mpr ?_
  refine (ObjectProperty.ι _).map_injective ?_
  exact (IsZero.iff_id_eq_zero K.obj).mp hzero

end Stacks.AmpleNonvanishing

end
