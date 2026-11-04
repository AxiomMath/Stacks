module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TwistOrthogonalVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularAnyModel

/-!
# Degreewise vanishing of cohomology sheaves in `D_QCoh` from orthogonality

Let `X` be a quasi-compact and quasi-separated scheme carrying an ample invertible module, and
let `𝒯` be a class of `𝒪_X`-modules such that every quasi-coherent `𝒪_X`-module of finite type
is a quotient of a finite direct sum of members of `𝒯`. For `K ∈ D_QCoh(𝒪_X)` and a degree `p`,
if the only morphism `M[-p] ⟶ K` is zero for every `M` in `𝒯`, then `Hᵖ(K) = 0`.

This is the degreewise form of the vanishing step of [Stacks, Tag 0BQR]: the cocycle argument
of `Stacks.AmpleNonvanishing.isZero_of_hom_single_eq_zero` only ever uses the hypothesis in the
degree whose cohomology it kills. Everything is stated for an arbitrary model of the derived
category; [Stacks, Tag 08DB] is moved to that model along the comparison equivalence.

## Main results

* `Stacks.AmpleNonvanishing.exists_iso_Q_obj_quasicoherentComplex_of_isAmple`: [Stacks, Tag 08DB]
  on a scheme with an ample invertible module, in any model of `D(𝒪_X)`.
* `Stacks.AmpleNonvanishing.isZero_homology_of_hom_singleFunctor_eq_zero`: the degreewise
  vanishing above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample
open Stacks.AlgebraicGeometry.Tag01PGColimitClose
  (isColimit_finiteTypeQuasicoherentSubobjectCocone)

universe w u

namespace Stacks.AmpleNonvanishing

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)

include hL in
/-- **[Stacks, Tag 08DB] in any model of `D(𝒪_X)`.** On a scheme carrying an ample invertible
module, every object of `D_QCoh(𝒪_X)` is isomorphic to the class of a cochain complex of
quasi-coherent `𝒪_X`-modules. -/
theorem exists_iso_Q_obj_quasicoherentComplex_of_isAmple (h : HasDerivedCategory.{w} X.Modules)
    (K : @DerivedCategory X.Modules _ _ h)
    (hK : ∀ i : ℤ, (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((@DerivedCategory.homologyFunctor X.Modules _ _ h i).obj K)) :
    ∃ G : CochainComplex (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ℤ,
      Nonempty (K ≅ (@DerivedCategory.Q X.Modules _ _ h).obj
        (((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)) := by
  let h₁ : HasDerivedCategory.{u} X.Modules := Scheme.Modules.hasDerivedCategory X
  let E := StacksDraft.DerivedModel.modelEquiv h₁ h
  let K₁ : @DerivedCategory X.Modules _ _ h₁ := E.inverse.obj K
  have hK₁ : ∀ i : ℤ, (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((@DerivedCategory.homologyFunctor X.Modules _ _ h₁ i).obj K₁) := fun i =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((@DerivedCategory.homologyFunctor X.Modules _ _ h i).mapIso (E.counitIso.app K)).symm ≪≫
        (StacksDraft.DerivedModel.modelEquivCompHomologyFunctorIso h₁ h i).app K₁)
      (hK i)
  obtain ⟨G, ⟨e⟩⟩ := exists_quasicoherentComplex_iso_of_isAmple X L hL ⟨K₁, hK₁⟩
  exact ⟨G, ⟨E.counitIso.symm.app K ≪≫ E.functor.mapIso e ≪≫
    (StacksDraft.DerivedModel.modelCompQIso h₁ h).app _⟩⟩

variable [CompactSpace X] [QuasiSeparatedSpace X] (𝒯 : X.Modules → Prop)
  (hgen : ∀ F : X.Modules, F.IsQuasicoherent → SheafOfModules.IsFiniteType.{u, u, u} F →
    ∃ (r : ℕ) (M : Fin r → X.Modules), (∀ j, 𝒯 (M j)) ∧ ∃ φ : (∐ M) ⟶ F, Epi φ)

include hL hgen in
/-- **Degreewise vanishing from orthogonality.** Let `X` be a quasi-compact and quasi-separated
scheme carrying an ample invertible module, and `𝒯` a class of `𝒪_X`-modules of which every
quasi-coherent module of finite type is a quotient of a finite direct sum. If `K ∈ D_QCoh(𝒪_X)`
receives only the zero morphism from `M[-p]` for every `M` in `𝒯`, then `Hᵖ(K) = 0`. -/
theorem isZero_homology_of_hom_singleFunctor_eq_zero [HasDerivedCategory.{w} X.Modules]
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor X.Modules i).obj K))
    (p : ℤ) (hkill : ∀ M : X.Modules, 𝒯 M →
      ∀ f : (DerivedCategory.singleFunctor X.Modules p).obj M ⟶ K, f = 0) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules p).obj K) := by
  classical
  obtain ⟨G, ⟨eK⟩⟩ := exists_iso_Q_obj_quasicoherentComplex_of_isAmple X L hL inferInstance K hK
  set H : CochainComplex X.Modules ℤ :=
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj G
  have hH : ∀ i : ℤ, (H.X i).IsQuasicoherent := fun i => (G.X i).property
  have hz : IsZero (H.homology p) := by
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
        exact eq_zero_of_iso_comp_comp_iso
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules p).app (M j)) eK.symm
          (hkill (M j) (h𝒯 j)
            (((DerivedCategory.singleFunctorIsoCompQ X.Modules p).app (M j)).hom ≫
              DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle
                ((Sigma.ι M j ≫ φ ≫ Gsub.obj.arrow) ≫ H.iCycles p) (fun k _ => by simp)) ≫
              eK.inv))
      have hker : Gsub.obj.arrow ≫ H.homologyπ p = 0 := by
        refine (cancel_epi φ).1 ?_
        refine Sigma.hom_ext _ _ fun j => ?_
        simpa using hterm j
      exact hker.trans comp_zero.symm
    refine (IsZero.iff_id_eq_zero _).mpr ?_
    refine (cancel_epi (H.homologyπ p)).mp ?_
    simp [hπ]
  exact hz.of_iso (((DerivedCategory.homologyFunctorFactors X.Modules p).app H).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules p).mapIso eK.symm).symm

end Stacks.AmpleNonvanishing

end
