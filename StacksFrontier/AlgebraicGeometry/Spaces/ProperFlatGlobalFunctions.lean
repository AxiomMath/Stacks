module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.StructureMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections
public import StacksFrontier.RingTheory.Flat.EqualizerTensorExactBaseChange

/-!
# Global functions of a flat, finitely presented, separated algebraic space over an affine base

Let `X` be an algebraic space over `Spec A` whose structure morphism is separated, flat and of
finite presentation. If `κ(𝔭) = H⁰(X_{κ(𝔭)}, 𝒪)` for every prime `𝔭` of `A`, then
`A' = H⁰(X_{A'}, 𝒪)` for every `A`-algebra `A'`, in particular `A = H⁰(X, 𝒪)`.

`X` has a surjective étale atlas `W` with `W` and `R = W ×_X W` affine (`X` is quasi-compact and
separated over an affine base), and `C = Γ(W)`, `D = Γ(R)` are flat and finitely presented
over `A`. Global functions are the equalizer of `C ⇉ D`, also after base change, so the claim is
exactness of `0 → A' → A' ⊗_A C → A' ⊗_A D`, which holds on the fibres by hypothesis and
therefore everywhere (`AlgHom.EqualizerTensorExact.of_residueField_of_algebra`).

## Main results

* `AlgebraicGeometry.Space.exists_affine_atlas_flat_finitePresentation`: the atlas.
* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_relocalizeRestrict_of_residueField`
  and `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_of_residueField`: the
  statement above.
* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_congr`: `A = H⁰(X, 𝒪)` is
  invariant under isomorphism.

## Implementation notes

The base change to `Spec A'` is restriction along a morphism `g` of the big fppf site lying over
`Spec A' → Spec A`, given with that property as `hg`; such a `g` is unique, so quantifying over it
in the hypothesis on the fibres asks nothing more than the fibre over the canonical morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}

/-- A property of morphisms of schemes holding on every étale chart of the structure morphism of
`X` holds for the structure morphism of the scheme of every étale chart of `X`. -/
theorem holdsOnEveryEtaleChart_structure_chart (P : MorphismProperty Scheme.{u})
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    (hf : HoldsOnEveryEtaleChart B (Spec (.of A)) hA P f) {U : BigFppfOver B (Spec (.of A)) hA}
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf a) :
    P (B.inclusion.map U.hom) :=
  hf U (Over.mk (𝟙 (B.obj hA))) a (𝟙 _) (Over.homMk U.hom (by simp)) ha
    (presheaf_inverseImage_id_yoneda B (Spec (.of A)) hA _ (fun q _ => by
      have : IsIso q := ‹_›
      exact (inferInstance : Etale q)) _)
    ((isTerminal_yoneda_obj_base B _ hA).hom_ext _ _)

/-- The scheme of an affine object of the site over `Spec A` has affine image under the
inclusion. -/
private instance {U : BigFppfOver B (Spec (.of A)) hA}
    [hU : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)] :
    IsAffine (B.inclusion.obj U.left) := hU

private instance : IsAffine (B.inclusion.obj (B.obj hA)) :=
  inferInstanceAs (IsAffine (Spec (.of A)))

/-- For an object `U` of the site over `Spec A` with affine scheme, flatness of its structure
morphism makes `Γ(U)` a flat `A`-algebra. -/
theorem flat_siteObjectAlgebra {U : BigFppfOver B (Spec (.of A)) hA}
    (hU : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U))
    (h : Flat (B.inclusion.map U.hom)) :
    letI := siteObjectAlgebra B A U
    Module.Flat A Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) := by
  let := siteObjectAlgebra B A U
  rw [← RingHom.flat_algebraMap_iff]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv))
    (HasRingHomProperty.appTop @Flat _ h)

/-- For an object `U` of the site over `Spec A` with affine scheme, local finite presentation of
its structure morphism makes `Γ(U)` a finitely presented `A`-algebra. -/
theorem finitePresentation_siteObjectAlgebra {U : BigFppfOver B (Spec (.of A)) hA}
    (hU : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U))
    (h : LocallyOfFinitePresentation (B.inclusion.map U.hom)) :
    letI := siteObjectAlgebra B A U
    Algebra.FinitePresentation A Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) := by
  let := siteObjectAlgebra B A U
  rw [← RingHom.finitePresentation_algebraMap]
  exact RingHom.FinitePresentation.comp
    (HasRingHomProperty.appTop @LocallyOfFinitePresentation _ h)
    (RingHom.FinitePresentation.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv))

/-! ### Invariance under isomorphism -/

/-- `H⁰(X, 𝒪) = A` is invariant under isomorphism of algebraic spaces over `Spec A`. -/
theorem bijective_algebraMap_globalFunctions_congr
    {F G : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B (Spec (.of A)) hA F) (hG : IsAlgebraicSpace B (Spec (.of A)) hA G)
    (e : F ≅ G) :
    Function.Bijective (algebraMap A (globalFunctions B (Spec (.of A)) hA F)) ↔
      Function.Bijective (algebraMap A (globalFunctions B (Spec (.of A)) hA G)) := by
  let F' : AlgebraicSpaces B (Spec (.of A)) hA := ⟨F, hF⟩
  let G' : AlgebraicSpaces B (Spec (.of A)) hA := ⟨G, hG⟩
  let φ : F' ⟶ G' := ObjectProperty.homMk e.hom
  let ψ : G' ⟶ F' := ObjectProperty.homMk e.inv
  have h₁ : (globalFunctionsMap B _ hA φ).comp (globalFunctionsMap B _ hA ψ) = RingHom.id _ := by
    rw [← globalFunctionsMap_comp, ← globalFunctionsMap_id]
    congr 1
    exact ObjectProperty.hom_ext _ e.hom_inv_id
  have h₂ : (globalFunctionsMap B _ hA ψ).comp (globalFunctionsMap B _ hA φ) = RingHom.id _ := by
    rw [← globalFunctionsMap_comp, ← globalFunctionsMap_id]
    congr 1
    exact ObjectProperty.hom_ext _ e.inv_hom_id
  have hbij : Function.Bijective (globalFunctionsMap B _ hA φ) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨globalFunctionsMap B _ hA ψ, RingHom.congr_fun h₂, RingHom.congr_fun h₁⟩
  have hcomp : ⇑(algebraMap A (globalFunctions B (Spec (.of A)) hA F)) =
      globalFunctionsMap B _ hA φ ∘ algebraMap A (globalFunctions B (Spec (.of A)) hA G) :=
    funext fun a => (globalFunctionsMap_algebraMap _ B _ φ a).symm
  rw [hcomp]
  exact hbij.of_comp_iff' _

variable (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

include hX in
/-- **An affine atlas with affine kernel pair, flat and finitely presented over the base.** A
separated algebraic space over `Spec A` whose structure morphism is flat and of finite
presentation has a surjective étale atlas `p : W ⟶ X` with `W` affine whose kernel pair
`R = W ×_X W` is affine, and both `Γ(W)` and `Γ(R)` are flat and finitely presented over `A`. -/
theorem exists_affine_atlas_flat_finitePresentation
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hsep : IsSeparated B (Spec (.of A)) hA f)
    (hflat : IsFlat B (Spec (.of A)) hA f) (hfp : IsFinitePresentation B (Spec (.of A)) hA f) :
    ∃ (W R : BigFppfOver B (Spec (.of A)) hA) (p : yoneda.obj W ⟶ X) (r₁ r₂ : R ⟶ W),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p ∧
      IsPullback (yoneda.map r₁) (yoneda.map r₂) p p ∧
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj W) ∧
      IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj R) ∧
      Flat (B.inclusion.map W.hom) ∧ LocallyOfFinitePresentation (B.inclusion.map W.hom) ∧
      Flat (B.inclusion.map R.hom) ∧ LocallyOfFinitePresentation (B.inclusion.map R.hom) := by
  obtain ⟨W, c, hW, hcs, hce⟩ :=
    exists_isAffine_isEtale_isSurjective_chart_of_isQuasiCompact B (Spec (.of A)) hA hX f hfp.2.1
  have hpe := presheaf_etale_of_isEtale B (Spec (.of A)) hA hce
  obtain ⟨R, β, r, hR⟩ := hpe.1 c
  obtain ⟨rHom, rfl⟩ : ∃ rHom, yoneda.map rHom = r := ⟨_, Yoneda.fullyFaithful.map_preimage r⟩
  have hsepAbs := isAbsolutelySeparated_of_isSeparated_to_affine B (Spec (.of A)) hA
    (BigFppfSite.contains_terminal B) (Over.mk (𝟙 (B.obj hA)))
    (inferInstanceAs (IsAffine (Spec (.of A)))) f hsep
  have hRaff := ((isAbsolutelySeparated_iff_hasAffineIntersections B (Spec (.of A)) hA
    (BigFppfSite.contains_terminal B) X hX).mp hsepAbs W W R c c rHom β hW hW hR).1
  have hRe := etale_comp_of_scheme B (Spec (.of A)) hA β c (hpe.2 c _ β hR) hpe
  exact ⟨W, R, c, rHom, β, hcs, hpe, hR, hW, hRaff,
    holdsOnEveryEtaleChart_structure_chart B _ f hflat c hpe,
    holdsOnEveryEtaleChart_structure_chart B _ f hfp.1 c hpe,
    holdsOnEveryEtaleChart_structure_chart B _ f hflat _ hRe,
    holdsOnEveryEtaleChart_structure_chart B _ f hfp.1 _ hRe⟩

include hX in
/-- **Global functions are constant after every base change once they are on the fibres.** Let
`X` be a separated algebraic space over `Spec A` whose structure morphism is flat and of finite
presentation. If `κ(𝔭) = H⁰(X_{κ(𝔭)}, 𝒪)` for every prime `𝔭` of `A`, then
`A' = H⁰(X_{A'}, 𝒪)` for every `A`-algebra `A'` whose spectrum lies in the site. -/
theorem bijective_algebraMap_globalFunctions_relocalizeRestrict_of_residueField
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hsep : IsSeparated B (Spec (.of A)) hA f)
    (hflat : IsFlat B (Spec (.of A)) hA f) (hfp : IsFinitePresentation B (Spec (.of A)) hA f)
    (hfib : ∀ (P : Ideal A) [P.IsPrime] (hP : B.Contains (Spec (.of P.ResidueField)))
      (gP : B.obj hP ⟶ B.obj hA),
      B.inclusion.map gP = Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField)) →
      Function.Bijective (algebraMap P.ResidueField (globalFunctions B
        (Spec (.of P.ResidueField)) hP ((OverShriek.relocalizeRestrict gP).obj X))))
    (A' : Type u) [CommRing A'] [Algebra A A'] (hA' : B.Contains (Spec (.of A')))
    (g : B.obj hA' ⟶ B.obj hA)
    (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A A'))) :
    Function.Bijective (algebraMap A'
      (globalFunctions B (Spec (.of A')) hA' ((OverShriek.relocalizeRestrict g).obj X))) := by
  obtain ⟨W, R, p, r₁, r₂, hps, hpe, hR, hW, hRa, hWf, hWp, hRf, hRp⟩ :=
    exists_affine_atlas_flat_finitePresentation B hX f hsep hflat hfp
  let := siteObjectAlgebra B A W
  let := siteObjectAlgebra B A R
  have := flat_siteObjectAlgebra B hW hWf
  have := flat_siteObjectAlgebra B hRa hRf
  have := finitePresentation_siteObjectAlgebra B hW hWp
  have := finitePresentation_siteObjectAlgebra B hRa hRp
  refine (bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X hX p hps hpe r₁ r₂ hR
    hW hRa g hg).mpr ?_
  refine AlgHom.EqualizerTensorExact.of_residueField_of_algebra (fun P _ => ?_) A'
  exact (bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X hX p hps hpe r₁ r₂ hR
    hW hRa (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField))))
    rfl).mp (hfib P (BigFppfSite.contains_spec_residueField_atPrime B hA P) _ rfl)

include hX in
/-- **`A = H⁰(X, 𝒪)` once it holds on the fibres.** Let `X` be a separated algebraic space over
`Spec A` whose structure morphism is flat and of finite presentation. If
`κ(𝔭) = H⁰(X_{κ(𝔭)}, 𝒪)` for every prime `𝔭` of `A`, then `A = H⁰(X, 𝒪)`. -/
theorem bijective_algebraMap_globalFunctions_of_residueField
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA)))) (hsep : IsSeparated B (Spec (.of A)) hA f)
    (hflat : IsFlat B (Spec (.of A)) hA f) (hfp : IsFinitePresentation B (Spec (.of A)) hA f)
    (hfib : ∀ (P : Ideal A) [P.IsPrime] (hP : B.Contains (Spec (.of P.ResidueField)))
      (gP : B.obj hP ⟶ B.obj hA),
      B.inclusion.map gP = Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField)) →
      Function.Bijective (algebraMap P.ResidueField (globalFunctions B
        (Spec (.of P.ResidueField)) hP ((OverShriek.relocalizeRestrict gP).obj X)))) :
    Function.Bijective (algebraMap A (globalFunctions B (Spec (.of A)) hA X)) := by
  obtain ⟨W, R, p, r₁, r₂, hps, hpe, hR, hW, hRa, hWf, hWp, hRf, hRp⟩ :=
    exists_affine_atlas_flat_finitePresentation B hX f hsep hflat hfp
  let := siteObjectAlgebra B A W
  let := siteObjectAlgebra B A R
  have := flat_siteObjectAlgebra B hW hWf
  have := flat_siteObjectAlgebra B hRa hRf
  have := finitePresentation_siteObjectAlgebra B hW hWp
  have := finitePresentation_siteObjectAlgebra B hRa hRp
  refine (bijective_algebraMap_globalFunctions_iff B X hX p hps hpe r₁ r₂ hR).mpr ?_
  refine AlgHom.EqualizerTensorExact.of_residueField fun P _ => ?_
  exact (bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X hX p hps hpe r₁ r₂ hR
    hW hRa (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A P.ResidueField))))
    rfl).mp (hfib P (BigFppfSite.contains_spec_residueField_atPrime B hA P) _ rfl)

end AlgebraicGeometry.Space

end
