module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.Finiteness
public import StacksFrontier.RingTheory.Flat.EqualizerTensorExactDVR

/-!
# Global functions of a proper flat algebraic space over a discrete valuation ring

Let `V` be a discrete valuation ring and `X` an algebraic space over `Spec V` whose structure
morphism is proper, flat and of finite presentation. If the closed fibre `X_k` has only constant
global functions, `k = H⁰(X_k, 𝒪)`, then so does every flat base change of `X`: for every flat
`V`-algebra `A'`, `A' = H⁰(X_{A'}, 𝒪)`. In particular this holds for the generic fibre and for
its base changes to extensions of the fraction field.

## Main results

* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_relocalizeRestrict_of_dvr`: the
  statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {hV : B.Contains (Spec (.of V))} {X : (BigFppfOver B (Spec (.of V)) hV)ᵒᵖ ⥤ Type u}

omit [IsDomain V] [IsDiscreteValuationRing V] in
/-- The equalizer of the two pullbacks of functions from an affine étale atlas to its kernel pair
is a finitely generated `V`-module when the global functions are. -/
private theorem fg_ker_siteObjectAlgHom (hX : IsAlgebraicSpace B (Spec (.of V)) hV X)
    {U R : BigFppfOver B (Spec (.of V)) hV} (p : yoneda.obj U ⟶ X)
    (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of V)) hV)).presheaf p)
    (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of V)) hV)).presheaf p)
    (r₁ r₂ : R ⟶ U) (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) p p)
    (hfin : Module.Finite V (globalFunctions B (Spec (.of V)) hV X)) :
    letI := siteObjectAlgebra B V U
    letI := siteObjectAlgebra B V R
    (LinearMap.ker ((siteObjectAlgHom B r₁).toLinearMap -
      (siteObjectAlgHom B r₂).toLinearMap)).FG := by
  let := siteObjectAlgebra B V U
  let := siteObjectAlgebra B V R
  let ψ := globalFunctionsToChart B (Spec (.of V)) hV ⟨X, hX⟩ p
  let ψl : globalFunctions B (Spec (.of V)) hV X →ₗ[V]
      Γ((BigFppfOver.toScheme B (Spec (.of V)) hV).obj U, ⊤) :=
    { toFun := ψ
      map_add' := map_add ψ
      map_smul' := fun a s => by
        rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def]
        congr 1
        exact globalFunctionsToChart_algebraMap V B hV X hX p a }
  have hrange : LinearMap.ker ((siteObjectAlgHom B r₁).toLinearMap -
      (siteObjectAlgHom B r₂).toLinearMap) = LinearMap.range ψl := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.sub_apply, sub_eq_zero]
    exact (exists_globalFunctionsToChart_eq_iff B _ hV X hX p hps hpe r₁ r₂ hR c).symm
  rw [hrange, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map ψl

/-- **Constant global functions spread from the closed fibre over a discrete valuation ring.**
Let `V` be a discrete valuation ring and `X` an algebraic space over `Spec V` whose structure
morphism is proper, flat and of finite presentation. If the closed fibre `X_k` satisfies
`k = H⁰(X_k, 𝒪)`, then `A' = H⁰(X_{A'}, 𝒪)` for every flat `V`-algebra `A'` whose spectrum lies
in the site. -/
theorem bijective_algebraMap_globalFunctions_relocalizeRestrict_of_dvr
    (hX : IsAlgebraicSpace B (Spec (.of V)) hV X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hV)))) (hf : IsProper B (Spec (.of V)) hV f)
    (hflat : IsFlat B (Spec (.of V)) hV f) (hfp : IsFinitePresentation B (Spec (.of V)) hV f)
    (hs : ∀ (hP : B.Contains (Spec (.of (maximalIdeal V).ResidueField)))
      (gP : B.obj hP ⟶ B.obj hV),
      B.inclusion.map gP =
        Spec.map (CommRingCat.ofHom (algebraMap V (maximalIdeal V).ResidueField)) →
      Function.Bijective (algebraMap (maximalIdeal V).ResidueField (globalFunctions B
        (Spec (.of (maximalIdeal V).ResidueField)) hP ((OverShriek.relocalizeRestrict gP).obj X))))
    (A' : Type u) [CommRing A'] [Algebra V A'] [Module.Flat V A']
    (hA' : B.Contains (Spec (.of A'))) (g : B.obj hA' ⟶ B.obj hV)
    (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap V A'))) :
    Function.Bijective (algebraMap A'
      (globalFunctions B (Spec (.of A')) hA' ((OverShriek.relocalizeRestrict g).obj X))) := by
  obtain ⟨W, R, p, r₁, r₂, hps, hpe, hR, hW, hRa, hWf, hWp, hRf, hRp⟩ :=
    exists_affine_atlas_flat_finitePresentation B hX f hf.1 hflat hfp
  let := siteObjectAlgebra B V W
  let := siteObjectAlgebra B V R
  have := flat_siteObjectAlgebra B hW hWf
  have := flat_siteObjectAlgebra B hRa hRf
  have hfin : Module.Finite V (globalFunctions B (Spec (.of V)) hV X) := by
    have hf' : f = (isTerminal_yoneda_obj_base B _ hV).from X :=
      (isTerminal_yoneda_obj_base B _ hV).hom_ext _ _
    exact moduleFinite_globalFunctions_of_isProper V ⟨X, hX⟩ (hf' ▸ hf)
  have hker := fg_ker_siteObjectAlgHom B hX p hps hpe r₁ r₂ hR hfin
  let P := maximalIdeal V
  have hP : B.Contains (Spec (.of P.ResidueField)) :=
    BigFppfSite.contains_spec_residueField_atPrime B hV P
  have hk := (bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X hX p hps hpe r₁ r₂
    hR hW hRa (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap V P.ResidueField))))
    rfl).mp (hs hP _ rfl)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  have : Module.Free (V ⧸ maximalIdeal V) P.ResidueField := Module.Free.of_divisionRing _ _
  have : Module.FaithfullyFlat (V ⧸ maximalIdeal V) P.ResidueField := inferInstance
  have hk' : AlgHom.EqualizerTensorExact (siteObjectAlgHom B r₁) (siteObjectAlgHom B r₂)
      (V ⧸ maximalIdeal V) := hk.of_faithfullyFlat
  have hV' := AlgHom.EqualizerTensorExact.self_of_residueField_of_isDiscreteValuationRing hker hk'
  exact (bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X hX p hps hpe r₁ r₂ hR
    hW hRa g hg).mpr (hV'.of_flat (N := A'))

end AlgebraicGeometry.Space
