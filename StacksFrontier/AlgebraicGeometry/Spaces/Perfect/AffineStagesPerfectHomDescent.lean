module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.RingSystemHomotopy
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DescentSituationAffinePerfectDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePointTensorFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTensorCocycle

/-!
# Descent of morphisms between perfect objects over affine stages

In Situation 09RH with charts bounded in size and the chosen stage `X₀` affine, every stage
`Xᵢ` (`i ≥ 0`) and the limit `X` are affine, and the morphisms between perfect objects descend:
for perfect `Eᵢ`, `Kᵢ` on a stage `Xᵢ`,
`colim_{j ≥ i} Hom(Lf_{ji}^*Eᵢ, Lf_{ji}^*Kᵢ) ⟶ Hom(Lfᵢ^*Eᵢ, Lfᵢ^*Kᵢ)` is bijective. This is the
affine case of the full faithfulness half of Stacks 09RI–09RJ.

The proof follows the source: on an affine stage `Xᵢ ≅ Spec Aᵢ` a perfect object is
`𝒪 ⊗_{Aᵢ} C` for a bounded complex `C` of finite projective `Aᵢ`-modules
(`AlgebraicGeometry.Space.exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso`), derived
pullback along `X_j ⟶ Xᵢ` is `𝒪 ⊗_{Γ(X_j)} (Γ(X_j) ⊗_{Aᵢ} C)`
(`AlgebraicGeometry.Space.derivedPullbackPointTensorIso`, natural and compatible with
composition), the functor `𝒪 ⊗_A -` out of `D(A)` is fully faithful over an affine space, and
`Γ(X) = colim Γ(X_j)` (Stacks 07SI, under the bound on the charts) reduces the claim to the
ring-level statement `Stacks.LimitHomDescent.Affine.RingSystem.exists_Qh_map_ext_eq`,
`Stacks.LimitHomDescent.Affine.RingSystem.exists_le_Qh_map_ext_eq` (Stacks 09RE over rings).

## Main results

* `AlgebraicGeometry.Space.DescentSituation.stageProjectionDerivedPullbackIso_hom_naturality`.
* `AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_isAffineSpace`.
* `AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_restrictTo_of_isAffineSpace`: the
  affine case of the induction of Stacks 08GP for the full faithfulness half.

## Implementation notes

The goals of the descent statements are large: every derived pullback in them carries the models
of its source and target derived categories. `obtain pat := e` with `e` not a local hypothesis
abstracts `e` in the goal first, which traverses the goal without sharing; the proofs therefore
name such an `e` with `have` and destructure the hypothesis.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace CochainComplex.IsKProjective

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- Two maps out of a K-projective complex which agree in the derived category agree in the
homotopy category. -/
theorem quotient_map_eq_of_Q_map_eq {K L : CochainComplex 𝒜 ℤ} [K.IsKProjective] (a b : K ⟶ L)
    (h : DerivedCategory.Q.map a = DerivedCategory.Q.map b) :
    (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map a =
      (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map b := by
  apply (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj L)).injective
  rwa [← Stacks.LimitHomDescent.Affine.quotientCompQhIso_conj a,
    ← Stacks.LimitHomDescent.Affine.quotientCompQhIso_conj b, cancel_epi, cancel_mono] at h

end CochainComplex.IsKProjective

namespace CochainComplex

variable {A A' : Type u} [CommRing A] [CommRing A'] (α : A →+* A')
  (C : CochainComplex (ModuleCat.{u} A) ℤ)

/-- Extension of scalars along `α` of a complex which is strictly `≤ b` is strictly `≤ b`. -/
instance (b : ℤ) [C.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  exact (ModuleCat.extendScalars.{u, u, u} α).map_isZero (C.isZero_of_isStrictlyLE b n hn)

/-- Extension of scalars of a complex with finitely many nonzero terms has finitely many nonzero
terms. -/
theorem finite_support_extendScalars (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite) :
    {i : ℤ | ¬ IsZero ((((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C).X i)}.Finite :=
  hbd.subset fun _ hi h => hi ((ModuleCat.extendScalars.{u, u, u} α).map_isZero h)

end CochainComplex

namespace CategoryTheory.Functor

variable {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (F : 𝒞 ⥤ 𝒟) {E K E' K' : 𝒞}
  (eE : E ≅ E') (eK : K ≅ K') (φ ψ : E ⟶ K)

/-- If `F` identifies `φ` and `ψ`, it identifies their conjugates `eE⁻¹ ≫ φ ≫ eK` and
`eE⁻¹ ≫ ψ ≫ eK`. -/
theorem map_conj_eq_of_map_eq (h : F.map φ = F.map ψ) :
    F.map (eE.inv ≫ φ ≫ eK.hom) = F.map (eE.inv ≫ ψ ≫ eK.hom) := by
  rw [F.map_comp, F.map_comp, F.map_comp, F.map_comp, h]

/-- If `F` identifies the conjugates `eE⁻¹ ≫ φ ≫ eK` and `eE⁻¹ ≫ ψ ≫ eK`, it identifies `φ`
and `ψ`. -/
theorem map_eq_of_map_conj_eq (h : F.map (eE.inv ≫ φ ≫ eK.hom) = F.map (eE.inv ≫ ψ ≫ eK.hom)) :
    F.map φ = F.map ψ := by
  have e : ∀ χ : E ⟶ K, F.map χ =
      F.map eE.hom ≫ F.map (eE.inv ≫ χ ≫ eK.hom) ≫ F.map eK.inv := fun χ => by
    rw [← F.map_comp, ← F.map_comp]
    simp
  rw [e φ, e ψ, h]

end CategoryTheory.Functor

namespace CategoryTheory.Iso

variable {𝒟 : Type*} [Category* 𝒟] {P P' Y Y' Z Z' W W' V V' : 𝒟}

/-- **A morphism determined by three commuting squares.** Given isomorphisms
`c : P ≅ Y`, `Γ : Y ≅ Z`, `ρ : W ≅ Z`, `Λ : P ≅ V`, `Ξ : V ≅ W` (and primed copies) with
`c ≫ Γ ≫ ρ⁻¹ = Λ ≫ Ξ`, a morphism `φ : Y ⟶ Y'` with `Γ⁻¹ ≫ φ ≫ Γ' = ρ⁻¹ ≫ r ≫ ρ'` for some
`r : W ⟶ W'`, and `s : V ⟶ V'` with `s ≫ Ξ' = Ξ ≫ r`, the morphism `φ` is
`c⁻¹ ≫ Λ ≫ s ≫ Λ'⁻¹ ≫ c'`. -/
theorem eq_inv_comp_comp_hom_of_comm (c : P ≅ Y) (c' : P' ≅ Y') (Γ : Y ≅ Z) (Γ' : Y' ≅ Z')
    (ρ : W ≅ Z) (ρ' : W' ≅ Z') (Λ : P ≅ V) (Λ' : P' ≅ V') (Ξ : V ≅ W) (Ξ' : V' ≅ W')
    (φ : Y ⟶ Y') (s : V ⟶ V') (r : W ⟶ W') (fv : Z ⟶ Z')
    (hC : c.hom ≫ Γ.hom ≫ ρ.inv = Λ.hom ≫ Ξ.hom) (hC' : c'.hom ≫ Γ'.hom ≫ ρ'.inv = Λ'.hom ≫ Ξ'.hom)
    (hnt : s ≫ Ξ'.hom = Ξ.hom ≫ r) (hv : fv = Γ.inv ≫ φ ≫ Γ'.hom) (ht : ρ.inv ≫ r ≫ ρ'.hom = fv) :
    φ = c.inv ≫ (Λ.hom ≫ s ≫ Λ'.inv) ≫ c'.hom := by
  have hΛ : Λ.hom = c.hom ≫ Γ.hom ≫ ρ.inv ≫ Ξ.inv := by
    have h := hC =≫ Ξ.inv
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact h.symm
  have hΛ' : Λ'.inv = Ξ'.hom ≫ ρ'.hom ≫ Γ'.inv ≫ c'.inv := by
    refine Iso.inv_ext ?_
    have h := hC' =≫ Ξ'.inv
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    rw [← h]
    simp
  have hφ : φ = Γ.hom ≫ fv ≫ Γ'.inv := by
    rw [hv]
    simp
  rw [hφ, hΛ, hΛ', ← ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hnt]
  simp

/-- **Transport of a factorisation along isomorphisms of the source and target.** If
`eE⁻¹ ≫ φ ≫ eK = c'⁻¹ ≫ x ≫ d'` and the squares `n ≫ c' = c ≫ eE`, `m ≫ d = d' ≫ eK⁻¹` commute,
then `φ = c⁻¹ ≫ (n ≫ x ≫ m) ≫ d`. -/
theorem eq_inv_comp_comp_hom_of_naturality {A₁ A₁' B₁ B₁' A₂ A₂' B₂ B₂' : 𝒟}
    (c : A₁ ≅ B₁) (c' : A₁' ≅ B₁') (d : A₂ ≅ B₂) (d' : A₂' ≅ B₂') (eE : B₁ ≅ B₁') (eK : B₂ ≅ B₂')
    (n : A₁ ⟶ A₁') (m : A₂' ⟶ A₂) (x : A₁' ⟶ A₂') (φ : B₁ ⟶ B₂)
    (hn : n ≫ c'.hom = c.hom ≫ eE.hom) (hm : m ≫ d.hom = d'.hom ≫ eK.inv)
    (h : eE.inv ≫ φ ≫ eK.hom = c'.inv ≫ x ≫ d'.hom) :
    φ = c.inv ≫ (n ≫ x ≫ m) ≫ d.hom := by
  have hφ : φ = eE.hom ≫ (eE.inv ≫ φ ≫ eK.hom) ≫ eK.inv := by simp
  rw [hφ, h, Iso.eq_inv_comp]
  simp only [Category.assoc]
  rw [hm, ← reassoc_of% hn]
  simp

end CategoryTheory.Iso

namespace AlgebraicGeometry.Space

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Congr

variable {X X' : AlgebraicSpaces B S hS} {A A' : Type u} [CommRing A] [CommRing A']
  (ψ : A →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)))
  (ψ' : A' →+* (SpacesEtale.structurePresheaf B S hS X').obj (op (SpacesEtale.idObj B S hS X')))

/-- **`Lg^* T_ψ(C) ≅ T_{ψ'}(A' ⊗_A C)` depends on `g` and `α` only through their values**: for
`g₁ = g₂` and `α₁ = α₂` the two isomorphisms agree up to the identifications of their sources
and targets. -/
theorem derivedPullbackPointTensorIso_congr (g₁ g₂ : X' ⟶ X) (hg : g₁ = g₂) (α₁ α₂ : A →+* A')
    (hα : α₁ = α₂) (hψ₁ : ∀ a, globalFunctionsMap B S hS g₁ (ψ a) = ψ' (α₁ a))
    (hψ₂ : ∀ a, globalFunctionsMap B S hS g₂ (ψ a) = ψ' (α₂ a))
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    (hb : C.IsStrictlyLE b) (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite A (C.X i)) (hproj : ∀ i : ℤ, Module.Projective A (C.X i)) :
    (derivedPullbackPointTensorIso B S hS ψ g₁ ψ' α₁ hψ₁ C b hb hbd hfin hproj).hom =
      eqToHom (by rw [hg]) ≫
        (derivedPullbackPointTensorIso B S hS ψ g₂ ψ' α₂ hψ₂ C b hb hbd hfin hproj).hom ≫
        eqToHom (by rw [hα]) := by
  subst hg hα
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end Congr

section Surjectivity

open Stacks.LimitHomDescent.Affine in
/-- **The morphism at the limit given by a chain map at a stage.** Let `p : X ⟶ Xⱼ`,
`f : Xⱼ ⟶ X₀` with `p ≫ f = g`, ring maps `αⱼ : R₀ ⟶ Rⱼ`, `γ : Rⱼ ⟶ R` with `αⱼ ≫ γ = α`
compatible with `R₀ ⟶ Γ(X₀)`, `Rⱼ ⟶ Γ(Xⱼ)`, `R ⟶ Γ(X)`, and bounded complexes `C`, `C'` of
finite projective `R₀`-modules. If a morphism `φ : Lg^* T(C) ⟶ Lg^* T(C')` corresponds to the
chain map `v : R ⊗ C ⟶ R ⊗ C'`, and `v` is, up to homotopy, `R ⊗_{Rⱼ} t` for a chain map
`t : Rⱼ ⊗ C ⟶ Rⱼ ⊗ C'`, then `φ` is `Lp^*` of the morphism `Lf^* T(C) ⟶ Lf^* T(C')`
corresponding to `t`, read through `Lp^* Lf^* ≅ Lg^*`. -/
theorem eq_derivedPullback_map_of_pointTensor {X Xj X₀ : AlgebraicSpaces B S hS} (p : X ⟶ Xj)
    (f : Xj ⟶ X₀) (g : X ⟶ X₀) (hg : p ≫ f = g) {R₀ Rj R : CommRingCat.{u}} (αj : R₀ ⟶ Rj)
    (γ : Rj ⟶ R) (α : R₀ ⟶ R) (hα : αj ≫ γ = α)
    (ψ₀ : R₀ →+* (SpacesEtale.structurePresheaf B S hS X₀).obj (op (SpacesEtale.idObj B S hS X₀)))
    (ψj : Rj →+* (SpacesEtale.structurePresheaf B S hS Xj).obj (op (SpacesEtale.idObj B S hS Xj)))
    (ψ : R →+* (SpacesEtale.structurePresheaf B S hS X).obj (op (SpacesEtale.idObj B S hS X)))
    (hψj : ∀ a, globalFunctionsMap B S hS f (ψ₀ a) = ψj (αj.hom a))
    (hψp : ∀ a, globalFunctionsMap B S hS p (ψj a) = ψ (γ.hom a))
    (hψ : ∀ a, globalFunctionsMap B S hS g (ψ₀ a) = ψ (α.hom a))
    (C C' : CochainComplex (ModuleCat.{u} R₀) ℤ) (b b' : ℤ) (hCb : C.IsStrictlyLE b)
    (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite) (hfin : ∀ i : ℤ, Module.Finite R₀ (C.X i))
    (hproj : ∀ i : ℤ, Module.Projective R₀ (C.X i)) (hCb' : C'.IsStrictlyLE b')
    (hbd' : {i : ℤ | ¬ IsZero (C'.X i)}.Finite) (hfin' : ∀ i : ℤ, Module.Finite R₀ (C'.X i))
    (hproj' : ∀ i : ℤ, Module.Projective R₀ (C'.X i))
    (φ : (derivedPullback (spacesEtaleModelHom B S hS g)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C)) ⟶
      (derivedPullback (spacesEtaleModelHom B S hS g)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C')))
    (t : (ext αj).obj C ⟶ (ext αj).obj C') (v : (ext α).obj C ⟶ (ext α).obj C')
    (hv : DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex
        (ComplexShape.up ℤ)).map v) =
      (derivedPullbackPointTensorIso B S hS ψ₀ g ψ α.hom hψ C b hCb hbd hfin hproj).inv ≫ φ ≫
        (derivedPullbackPointTensorIso B S hS ψ₀ g ψ α.hom hψ C' b' hCb' hbd' hfin' hproj').hom)
    (ht : (Stacks.FilteredColimitHom.Qh R).map ((extCompIsoOf αj γ α hα C).inv ≫ (ext γ).map t ≫
        (extCompIsoOf αj γ α hα C').hom) = (Stacks.FilteredColimitHom.Qh R).map v) :
    ∃ ψt : (derivedPullback (spacesEtaleModelHom B S hS f)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C)) ⟶
      (derivedPullback (spacesEtaleModelHom B S hS f)).obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS ψ₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          C')),
      φ = ((spacesEtaleModelDerivedPullbackCompIso B S hS p f).app _ ≪≫
          eqToIso (congrArg (fun k => (derivedPullback (spacesEtaleModelHom B S hS k)).obj
            (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS ψ₀).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C))) hg)).inv ≫
        (derivedPullback (spacesEtaleModelHom B S hS p)).map ψt ≫
        ((spacesEtaleModelDerivedPullbackCompIso B S hS p f).app _ ≪≫
          eqToIso (congrArg (fun k => (derivedPullback (spacesEtaleModelHom B S hS k)).obj
            (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS ψ₀).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C'))) hg)).hom := by
  subst hg hα
  have hC := hCb
  have hC' := hCb'
  have hfinj := fun n => (have := hfin n; have := hproj n;
    StacksDraft.Perfect.finite_projective_extendScalars_obj αj.hom (C.X n))
  have hfinj' := fun n => (have := hfin' n; have := hproj' n;
    StacksDraft.Perfect.finite_projective_extendScalars_obj αj.hom (C'.X n))
  have hbdj := CochainComplex.finite_support_extendScalars αj.hom C hbd
  have hbdj' := CochainComplex.finite_support_extendScalars αj.hom C' hbd'
  have cC := derivedPullbackPointTensorIso_comp B S hS f p ψ₀ ψj ψ αj.hom γ.hom hψj hψp hψ C b
    hCb hbd hfin hproj inferInstance hbdj (fun n => (hfinj n).1) (fun n => (hfinj n).2)
  have cC' := derivedPullbackPointTensorIso_comp B S hS f p ψ₀ ψj ψ αj.hom γ.hom hψj hψp hψ C' b'
    hCb' hbd' hfin' hproj' inferInstance hbdj' (fun n => (hfinj' n).1) (fun n => (hfinj' n).2)
  have nt := derivedPullbackPointTensorIso_hom_naturality B S hS p ψj ψ γ.hom hψp t b b'
    inferInstance hbdj (fun n => (hfinj n).1) (fun n => (hfinj n).2)
    inferInstance hbdj' (fun n => (hfinj' n).1) (fun n => (hfinj' n).2)
  let T := (spacesEtaleModelPointTensor B S hS ψ).mapHomologicalComplex (ComplexShape.up ℤ)
  have hρ : ∀ M : CochainComplex (ModuleCat.{u} R₀) ℤ, (extCompIsoOf αj γ (αj ≫ γ) rfl M).inv =
      (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp αj.hom γ.hom).hom
        (ComplexShape.up ℤ)).app M := fun M => by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    simp [extCompIsoOf, extComp]
  have ht' := DerivedCategory.Q_map_eq_of_homotopy _
    ((spacesEtaleModelPointTensor B S hS ψ).mapHomotopy (HomotopyCategory.homotopyOfEq _ _ ht))
  simp only [Functor.map_comp] at ht'
  refine ⟨(derivedPullbackPointTensorIso B S hS ψ₀ f ψj αj.hom hψj C b hCb hbd hfin hproj).hom ≫
    DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS ψj).mapHomologicalComplex
      (ComplexShape.up ℤ)).map t) ≫
    (derivedPullbackPointTensorIso B S hS ψ₀ f ψj αj.hom hψj C' b' hCb' hbd' hfin' hproj').inv, ?_⟩
  have key := Iso.eq_inv_comp_comp_hom_of_comm
    ((spacesEtaleModelDerivedPullbackCompIso B S hS p f).app _)
    ((spacesEtaleModelDerivedPullbackCompIso B S hS p f).app _)
    (derivedPullbackPointTensorIso B S hS ψ₀ (p ≫ f) ψ (αj ≫ γ).hom hψ C b hCb hbd hfin hproj)
    (derivedPullbackPointTensorIso B S hS ψ₀ (p ≫ f) ψ (αj ≫ γ).hom hψ C' b' hCb' hbd' hfin' hproj')
    (DerivedCategory.Q.mapIso (T.mapIso (extCompIsoOf αj γ (αj ≫ γ) rfl C)))
    (DerivedCategory.Q.mapIso (T.mapIso (extCompIsoOf αj γ (αj ≫ γ) rfl C')))
    ((derivedPullback (spacesEtaleModelHom B S hS p)).mapIso
      (derivedPullbackPointTensorIso B S hS ψ₀ f ψj αj.hom hψj C b hCb hbd hfin hproj))
    ((derivedPullback (spacesEtaleModelHom B S hS p)).mapIso
      (derivedPullbackPointTensorIso B S hS ψ₀ f ψj αj.hom hψj C' b' hCb' hbd' hfin' hproj'))
    (derivedPullbackPointTensorIso B S hS ψj p ψ γ.hom hψp _ b inferInstance hbdj
      (fun n => (hfinj n).1) (fun n => (hfinj n).2))
    (derivedPullbackPointTensorIso B S hS ψj p ψ γ.hom hψp _ b' inferInstance hbdj'
      (fun n => (hfinj' n).1) (fun n => (hfinj' n).2))
    φ _ _ _ (by rw [Functor.mapIso_inv, Functor.mapIso_inv, hρ]; exact cC)
    (by rw [Functor.mapIso_inv, Functor.mapIso_inv, hρ]; exact cC') nt hv ht'
  refine key.trans ?_
  simp only [Iso.trans_inv, Iso.trans_hom, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]

end Surjectivity

/-- Extension of scalars of a complex of finite projective modules which is strictly `≤ b` is
K-projective. -/
private theorem isKProjective_extendScalars_of_finite_projective {A₀ A : Type u} [CommRing A₀]
    [CommRing A] (α : A₀ →+* A) (C : CochainComplex (ModuleCat.{u} A₀) ℤ) (b : ℤ)
    [C.IsStrictlyLE b] (hfin : ∀ i : ℤ, Module.Finite A₀ (C.X i))
    (hproj : ∀ i : ℤ, Module.Projective A₀ (C.X i)) :
    CochainComplex.IsKProjective (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C) := by
  have : ∀ n, Projective ((((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C).X n) := fun n =>
    have := hfin n
    have := hproj n
    (IsProjective.iff_projective (R := A) (P := (ModuleCat.extendScalars.{u, u, u} α).obj
      (C.X n))).1 (StacksDraft.Perfect.finite_projective_extendScalars_obj α (C.X n)).2
  exact CochainComplex.isKProjective_of_projective _ b

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **`Lf_j^* ∘ Lf_{ji}^* ≅ Lfᵢ^*` is natural.** -/
theorem stageProjectionDerivedPullbackIso_hom_naturality {i j : I} (h : i ≤ j)
    {E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).O))}
    (e : E ⟶ E') :
    (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op j)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op j), D.algebraicSpace j⟩))).map
        ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map e) ≫
        (D.stageProjectionDerivedPullbackIso h E').hom =
      (D.stageProjectionDerivedPullbackIso h E).hom ≫
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map e := by
  have key : ∀ (k₁ k₂ : (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨D.system.obj (op i), D.algebraicSpace i⟩) (hk : k₁ = k₂),
      (derivedPullback (spacesEtaleModelHom B S hS k₁)).map e ≫
        eqToHom (congrArg (fun k => (derivedPullback (spacesEtaleModelHom B S hS k)).obj E') hk) =
      eqToHom (congrArg (fun k => (derivedPullback (spacesEtaleModelHom B S hS k)).obj E) hk) ≫
        (derivedPullback (spacesEtaleModelHom B S hS k₂)).map e := by
    intro k₁ k₂ hk
    subst hk
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  simp only [stageProjectionDerivedPullbackIso, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    Category.assoc]
  rw [← key ((ObjectProperty.homMk (D.limitCone.π.app (op j)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op j), D.algebraicSpace j⟩) ≫
      ObjectProperty.homMk (D.system.map (homOfLE h).op))
    (ObjectProperty.homMk (D.limitCone.π.app (op i)))
    (ObjectProperty.hom_ext _ (D.limitCone.w (homOfLE h).op)), ← Category.assoc,
    ← Category.assoc]
  congr 1
  exact (spacesEtaleModelDerivedPullbackCompIso B S hS _ _).hom.naturality e

section RingSystem

variable {A₀ : Type u} [CommRing A₀]
  (ψ₀ : A₀ →+* (SpacesEtale.structurePresheaf B S hS
    (D.toLimitSituation.stage D.toLimitSituation.base)).obj
    (op (SpacesEtale.idObj B S hS (D.toLimitSituation.stage D.toLimitSituation.base))))
  {A : Type u} [CommRing A]
  (σ : A ≃+* (SpacesEtale.structurePresheaf B S hS
    (D.toLimitSituation.limitSpace D.limitAlgebraicSpace)).obj
      (op (SpacesEtale.idObj B S hS (D.toLimitSituation.limitSpace D.limitAlgebraicSpace))))

/-- **The rings of the stages `j ≥ 0` as algebras over a ring `A₀ ⟶ Γ(X₀)`**, with vertex a ring
`A ≅ Γ(X)`: the stage rings are the shrunk rings `Γ(X_j)`, with structure maps
`A₀ ⟶ Γ(X₀) ⟶ Γ(X_j)`, and the maps to the vertex are `Γ(X_j) ⟶ Γ(X) ≅ A`. -/
def stageRingSystem :
    Stacks.LimitHomDescent.Affine.RingSystem.{u, u} (CommRingCat.of A₀)
      D.toLimitSituation.Stages where
  A j := D.toLimitSituation.stagesGlobalFunctions.obj j
  φ j := CommRingCat.ofHom ((Shrink.ringEquiv _).symm.toRingHom.comp
    ((globalFunctionsMap B S hS (D.toLimitSituation.transition j.2)).comp ψ₀))
  β h := D.toLimitSituation.stagesGlobalFunctions.map (homOfLE h)
  φ_β {i j} h := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
        (D.toLimitSituation.transition (leOfHom (homOfLE h)))
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
          (D.toLimitSituation.transition i.2) (ψ₀ x))))) =
      (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS (D.toLimitSituation.transition j.2)
        (ψ₀ x))
    rw [RingEquiv.apply_symm_apply,
      ← D.toLimitSituation.transition_comp i.2 (leOfHom (homOfLE h)) j.2,
      globalFunctionsMap_comp]
    rfl
  β_β h h' := (D.toLimitSituation.stagesGlobalFunctions.map_comp (homOfLE h) (homOfLE h')).symm
  β_refl i := D.toLimitSituation.stagesGlobalFunctions.map_id i
  lim := CommRingCat.of A
  φlim := CommRingCat.ofHom (σ.symm.toRingHom.comp
    ((globalFunctionsMap B S hS (D.toLimitSituation.projection D.limitAlgebraicSpace
      D.toLimitSituation.base)).comp
      ψ₀))
  γ j := CommRingCat.ofHom (σ.symm.toRingHom.comp
    ((globalFunctionsMap B S hS (D.toLimitSituation.projection D.limitAlgebraicSpace j.1)).comp
      (Shrink.ringEquiv _).toRingHom))
  φ_γ j := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change σ.symm (globalFunctionsMap B S hS
        (D.toLimitSituation.projection D.limitAlgebraicSpace j.1)
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
          (D.toLimitSituation.transition j.2) (ψ₀ x))))) =
      σ.symm (globalFunctionsMap B S hS
        (D.toLimitSituation.projection D.limitAlgebraicSpace D.toLimitSituation.base) (ψ₀ x))
    rw [RingEquiv.apply_symm_apply,
      ← D.toLimitSituation.projection_comp_transition D.limitAlgebraicSpace j.2,
      globalFunctionsMap_comp]
    rfl
  β_γ {i j} h := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change σ.symm (globalFunctionsMap B S hS
        (D.toLimitSituation.projection D.limitAlgebraicSpace j.1)
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
          (D.toLimitSituation.transition (leOfHom (homOfLE h))) (Shrink.ringEquiv _ x))))) =
      σ.symm (globalFunctionsMap B S hS
        (D.toLimitSituation.projection D.limitAlgebraicSpace i.1) (Shrink.ringEquiv _ x))
    rw [RingEquiv.apply_symm_apply,
      ← D.toLimitSituation.projection_comp_transition D.limitAlgebraicSpace (leOfHom (homOfLE h)),
      globalFunctionsMap_comp]
    rfl

/-- The ring of a stage of `AlgebraicGeometry.Space.DescentSituation.stageRingSystem` is the ring
of global functions of the stage. -/
def stageRingEquiv (j : D.toLimitSituation.Stages) :
    (D.stageRingSystem ψ₀ σ).A j ≃+*
      (SpacesEtale.structurePresheaf B S hS ⟨D.system.obj (op j.1), D.algebraicSpace j.1⟩).obj
        (op (SpacesEtale.idObj B S hS ⟨D.system.obj (op j.1), D.algebraicSpace j.1⟩)) :=
  Shrink.ringEquiv (globalFunctions' B S hS (D.toLimitSituation.stage j.1).1)

/-- The map on global functions of the transition `X_j ⟶ X₀` sends `ψ₀ a` to the image under
`AlgebraicGeometry.Space.DescentSituation.stageRingEquiv` of the structure map `φ j` of
`AlgebraicGeometry.Space.DescentSituation.stageRingSystem` applied to `a`. -/
theorem globalFunctionsMap_transition_apply (j : D.toLimitSituation.Stages) (a : A₀) :
    globalFunctionsMap B S hS (ObjectProperty.homMk (D.system.map (homOfLE j.2).op) :
        (⟨D.system.obj (op j.1), D.algebraicSpace j.1⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩) (ψ₀ a) =
      D.stageRingEquiv ψ₀ σ j (((D.stageRingSystem ψ₀ σ).φ j).hom a) :=
  ((Shrink.ringEquiv (globalFunctions' B S hS
    (D.toLimitSituation.stage j.1).1)).apply_symm_apply _).symm

/-- The map on global functions of the projection `X ⟶ X₀` sends `ψ₀ a` to `σ (φlim a)`, where
`φlim : A₀ ⟶ A` is the structure map of the vertex of
`AlgebraicGeometry.Space.DescentSituation.stageRingSystem`. -/
theorem globalFunctionsMap_projection_apply (a : A₀) :
    globalFunctionsMap B S hS (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩) (ψ₀ a) =
      σ ((D.stageRingSystem ψ₀ σ).φlim.hom a) :=
  (σ.apply_symm_apply _).symm

/-- Under `AlgebraicGeometry.Space.DescentSituation.stageRingEquiv` and `σ`, the map on global
functions of the projection `X ⟶ X_j` is the map `γ j` of
`AlgebraicGeometry.Space.DescentSituation.stageRingSystem` from the ring of the stage `j` to the
vertex. -/
theorem globalFunctionsMap_stageProjection_apply (j : D.toLimitSituation.Stages)
    (x : (D.stageRingSystem ψ₀ σ).A j) :
    globalFunctionsMap B S hS (ObjectProperty.homMk (D.limitCone.π.app (op j.1)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op j.1), D.algebraicSpace j.1⟩) (D.stageRingEquiv ψ₀ σ j x) =
      σ (((D.stageRingSystem ψ₀ σ).γ j).hom x) :=
  (σ.apply_symm_apply _).symm

/-- **`Γ(X) = colim_{j ≥ 0} Γ(X_j)`** for the ring system of
`AlgebraicGeometry.Space.DescentSituation.stageRingSystem`, when the charts are bounded and the
chosen stage is affine (Stacks 07SI). -/
theorem isStagesColimit_stageRingSystem (hb : ChartsBounded B S hS D.system)
    (hbase : IsAffineSpace B S hS (D.system.obj (op D.base))) :
    Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : (D.stageRingSystem ψ₀ σ).A i) =>
        (D.stageRingSystem ψ₀ σ).β h x)
      (fun j (x : (D.stageRingSystem ψ₀ σ).A j) => (D.stageRingSystem ψ₀ σ).γ j x) := by
  let L := D.toLimitSituation
  obtain ⟨T₀, hT₀, ⟨e₀⟩⟩ := hbase
  let U₀ : BigAffineFppf B S hS := ⟨T₀, hT₀⟩
  let f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ L.system.obj (op L.base) :=
    e₀.inv
  have : IsIso f₀ := Iso.isIso_inv e₀
  have hf₀ : IsEtaleChart B S hS (L.system.obj (op L.base)) (CostructuredArrow.mk f₀) :=
    isEtaleChart_of_isIso (B := B) (S := S) (hS := hS) (f := f₀)
  have hpb : IsPullback (𝟙 _) (yoneda.map (𝟙 ((BigAffineFppf.inclusion B S hS).obj U₀))) f₀ f₀ := by
    rw [yoneda.map_id]
    exact IsKernelPair.id_of_mono f₀
  have hcol := L.isStagesColimit_globalFunctions_of_chartsBounded (U₀ := U₀) (R₀ := U₀)
    D.limitAlgebraicSpace hb hf₀ (isSurjective_of_isIso B S hS f₀) hpb
  exact Stacks.IsStagesColimit.ofEquiv _ _ (fun i => (Shrink.ringEquiv _).toEquiv) σ.toEquiv
    (fun i j h s => by
      change Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
        (L.transition (leOfHom (homOfLE h))) (Shrink.ringEquiv _ s))) = _
      rw [RingEquiv.apply_symm_apply]
      rfl)
    (fun i s => by
      change σ (σ.symm _) = _
      rw [RingEquiv.apply_symm_apply]
      rfl) hcol

end RingSystem

section Injectivity

variable {A₀ : Type u} [CommRing A₀] (hA₀ : B.Contains (Spec (CommRingCat.of A₀)))
  (p₀ : Spec (CommRingCat.of A₀) ⟶ S)
  (g₀ : (⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩ : AlgebraicSpaces B S hS) ≅
    ⟨yoneda.obj (BigFppfOver.mk B S hS hA₀ p₀), isAlgebraicSpace_yoneda B S hS _⟩)
  (C C' : CochainComplex (ModuleCat.{u} A₀) ℤ) (b b' : ℤ) (hCb : C.IsStrictlyLE b)
  (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite) (hfin : ∀ i : ℤ, Module.Finite A₀ (C.X i))
  (hproj : ∀ i : ℤ, Module.Projective A₀ (C.X i)) (hCb' : C'.IsStrictlyLE b')
  (hbd' : {i : ℤ | ¬ IsZero (C'.X i)}.Finite) (hfin' : ∀ i : ℤ, Module.Finite A₀ (C'.X i))
  (hproj' : ∀ i : ℤ, Module.Projective A₀ (C'.X i))

include hCb hbd hfin hproj hCb' hbd' hfin' hproj' in
/-- **Eventual injectivity over an affine chosen stage**, for objects `𝒪 ⊗_{A₀} C` and
`𝒪 ⊗_{A₀} C'` with `X₀ ≅ Spec A₀` and `C`, `C'` bounded complexes of finite projective
`A₀`-modules: two morphisms with the same derived pullback to the limit have the same derived
pullback to some stage. -/
theorem exists_derivedPullback_map_eq_of_pointTensor (hb : ChartsBounded B S hS D.system)
    (hbase : IsAffineSpace B S hS (D.system.obj (op D.base)))
    (φ ψ : DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) ⟶
      DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C'))
    (h : (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map φ =
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map ψ) :
    ∃ (j : I) (hj : D.base ≤ j),
      (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE hj).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map φ =
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE hj).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map ψ := by
  let hX := D.limitAlgebraicSpace
  let ψ₀ := representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀
  have := hCb
  have : ∀ n, Projective (C.X n) := fun n =>
    (IsProjective.iff_projective (R := A₀) (P := C.X n)).1 (hproj n)
  have : C.IsKProjective := CochainComplex.isKProjective_of_projective C b
  obtain ⟨u, rfl⟩ := exists_pointTensor_Q_map_eq B S hS hA₀ p₀ g₀ φ
  obtain ⟨w, rfl⟩ := exists_pointTensor_Q_map_eq B S hS hA₀ p₀ g₀ ψ
  have hXaff : IsAffineSpace B S hS D.limitCone.pt :=
    (D.isAffineHom_limitCone_π_of_chartsBounded hb (op D.base)).isAffineSpace_source hbase
  obtain ⟨T, hT, ⟨eT⟩⟩ := hXaff
  obtain ⟨A, _, hA, p, ⟨eA⟩⟩ := exists_iso_mk_spec B S hS T hT
  let g : (⟨D.limitCone.pt, hX⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ (eT ≪≫ yoneda.mapIso eA)
  let ψL := representedTildeOfIsoPointRingHom B S hS hA p g
  have hψL : Function.Bijective ψL := bijective_pointRingHomOfModel B S hS _
    (bijective_representedTildeOfIsoBaseRingHom B S hS hA p g)
  let σ := RingEquiv.ofBijective ψL hψL
  let RS := D.stageRingSystem ψ₀ σ
  have hcol := D.isStagesColimit_stageRingSystem ψ₀ σ hb hbase
  let α : A₀ →+* A := RS.φlim.hom
  have hψ : ∀ a, globalFunctionsMap B S hS (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
      (⟨D.limitCone.pt, hX⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩) (ψ₀ a) = ψL (α a) :=
    D.globalFunctionsMap_projection_apply ψ₀ σ
  have hnat := fun v => derivedPullbackPointTensorIso_hom_naturality (B := B) (S := S) (hS := hS)
    (g := _) (ψ := ψ₀) (ψ' := ψL) (α := α) (hψ := hψ) v b b' hCb hbd hfin hproj hCb' hbd' hfin'
      hproj'
  have h1 : DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS ψL).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
        (ComplexShape.up ℤ)).map u)) =
      DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS ψL).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (((ModuleCat.extendScalars.{u, u, u} α).mapHomologicalComplex
        (ComplexShape.up ℤ)).map w)) := by
    have hu := hnat u
    rw [h, hnat w] at hu
    exact ((cancel_epi _).1 hu).symm
  have h2 := (pointTensor_Q_map_eq_iff B S hS hA p g _ _).1 h1
  have := isKProjective_extendScalars_of_finite_projective α C b hfin hproj
  have h3 := CochainComplex.IsKProjective.quotient_map_eq_of_Q_map_eq _ _ h2
  have hfp : ∀ n, Module.FinitePresentation (CommRingCat.of A₀) (C.X n) := fun n =>
    have := hfin n
    have := hproj n
    Module.finitePresentation_of_projective _ _
  obtain ⟨j, hj⟩ := RS.exists_le_Qh_map_ext_eq hcol hbd hfp u w h3
  let ψj := (D.stageRingEquiv ψ₀ σ j).toRingHom
  have hnatj := fun v => derivedPullbackPointTensorIso_hom_naturality (B := B) (S := S) (hS := hS)
    (g := (ObjectProperty.homMk (D.system.map (homOfLE j.2).op) :
        (⟨D.system.obj (op j.1), D.algebraicSpace j.1⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))
    (ψ := ψ₀) (ψ' := ψj) (α := (RS.φ j).hom) (hψ := D.globalFunctionsMap_transition_apply ψ₀ σ j)
      v b b' hCb hbd hfin hproj hCb' hbd' hfin' hproj'
  refine ⟨j.1, j.2, (Iso.cancel_iso_hom_right _ _ _).1
    ((hnatj u).trans (Eq.trans ?_ (hnatj w).symm))⟩
  congr 1
  exact DerivedCategory.Q_map_eq_of_homotopy _
    ((spacesEtaleModelPointTensor B S hS ψj).mapHomotopy (HomotopyCategory.homotopyOfEq _ _ hj))

include hCb hbd hfin hproj hCb' hbd' hfin' hproj' in
/-- **Every morphism at the limit comes from a stage, over an affine chosen stage**, for objects
`𝒪 ⊗_{A₀} C` and `𝒪 ⊗_{A₀} C'` with `X₀ ≅ Spec A₀` and `C`, `C'` bounded complexes of finite
projective `A₀`-modules: a morphism `Lf₀^*(𝒪 ⊗ C) ⟶ Lf₀^*(𝒪 ⊗ C')` is `Lf_j^*ψ` for a morphism
`ψ : Lf_{j0}^*(𝒪 ⊗ C) ⟶ Lf_{j0}^*(𝒪 ⊗ C')` at some stage `j`, read through
`AlgebraicGeometry.Space.DescentSituation.stageProjectionDerivedPullbackIso`. -/
theorem exists_derivedPullback_map_eq_comp_of_pointTensor (hb : ChartsBounded B S hS D.system)
    (hbase : IsAffineSpace B S hS (D.system.obj (op D.base)))
    (φ : (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj
        (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C)) ⟶
      (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj
        (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C'))) :
    ∃ (j : I) (hj : D.base ≤ j) (ψ : (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE hj).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj
        (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C)) ⟶
      (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE hj).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj
        (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C'))),
      φ = (D.stageProjectionDerivedPullbackIso hj _).inv ≫
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op j)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op j), D.algebraicSpace j⟩))).map ψ ≫
        (D.stageProjectionDerivedPullbackIso hj _).hom := by
  let hX := D.limitAlgebraicSpace
  let ψ₀ := representedTildeOfIsoPointRingHom B S hS hA₀ p₀ g₀
  have hXaff : IsAffineSpace B S hS D.limitCone.pt :=
    (D.isAffineHom_limitCone_π_of_chartsBounded hb (op D.base)).isAffineSpace_source hbase
  obtain ⟨T, hT, ⟨eT⟩⟩ := hXaff
  have hspec := exists_iso_mk_spec B S hS T hT
  obtain ⟨A, _, hA, p, ⟨eA⟩⟩ := hspec
  let g : (⟨D.limitCone.pt, hX⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ (eT ≪≫ yoneda.mapIso eA)
  let ψL := representedTildeOfIsoPointRingHom B S hS hA p g
  have hψL : Function.Bijective ψL := bijective_pointRingHomOfModel B S hS _
    (bijective_representedTildeOfIsoBaseRingHom B S hS hA p g)
  let σ := RingEquiv.ofBijective ψL hψL
  let RS := D.stageRingSystem ψ₀ σ
  have hcol := D.isStagesColimit_stageRingSystem ψ₀ σ hb hbase
  have hψ := D.globalFunctionsMap_projection_apply ψ₀ σ
  let α : A₀ →+* A := RS.φlim.hom
  have := hCb
  have := isKProjective_extendScalars_of_finite_projective α C b hfin hproj
  have hfp : ∀ n, Module.FinitePresentation (CommRingCat.of A₀) (C.X n) := fun n =>
    have := hfin n
    have := hproj n
    Module.finitePresentation_of_projective _ _
  have hv := exists_pointTensor_Q_map_eq B S hS hA p g
    ((derivedPullbackPointTensorIso B S hS ψ₀ _ ψL α hψ C b hCb hbd hfin hproj).inv ≫ φ ≫
      (derivedPullbackPointTensorIso B S hS ψ₀ _ ψL α hψ C' b' hCb' hbd' hfin' hproj').hom)
  obtain ⟨v, hv⟩ := hv
  have ht := RS.exists_Qh_map_ext_eq hcol hbd hfp v
  obtain ⟨j, t, ht⟩ := ht
  have hψt := eq_derivedPullback_map_of_pointTensor
    (ObjectProperty.homMk (D.limitCone.π.app (op j.1)) :
      (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.system.obj (op j.1), D.algebraicSpace j.1⟩)
    (ObjectProperty.homMk (D.system.map (homOfLE j.2).op) :
      (⟨D.system.obj (op j.1), D.algebraicSpace j.1⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
    (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
      (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
    (ObjectProperty.hom_ext _ (D.limitCone.w (homOfLE j.2).op)) (RS.φ j) (RS.γ j) RS.φlim
    (RS.φ_γ j) ψ₀ (D.stageRingEquiv ψ₀ σ j).toRingHom ψL
    (D.globalFunctionsMap_transition_apply ψ₀ σ j)
    (D.globalFunctionsMap_stageProjection_apply ψ₀ σ j) hψ C C' b b' hCb hbd hfin hproj hCb' hbd'
    hfin' hproj' φ t v hv ht
  exact ⟨j.1, j.2, hψt⟩

end Injectivity

/-- **The full faithfulness half of Stacks 09RI–09RJ at the chosen stage, when it is affine**:
the clauses of `AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend` at `i = 0`, for
perfect `E`, `K` on `X₀ ≅ Spec A₀`, from their presentations `𝒪 ⊗_{A₀} C`, `𝒪 ⊗_{A₀} C'`. -/
theorem perfectHomsDescend_base_of_isAffineSpace (hb : ChartsBounded B S hS D.system)
    (hbase : IsAffineSpace B S hS (D.system.obj (op D.base)))
    (E K : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS ⟨D.system.obj (op D.base),
          D.algebraicSpace D.base⟩).O)))
    (hE : (spacesEtaleModelRingedSite B S hS ⟨D.system.obj (op D.base),
      D.algebraicSpace D.base⟩).IsPerfect E)
    (hK : (spacesEtaleModelRingedSite B S hS ⟨D.system.obj (op D.base),
      D.algebraicSpace D.base⟩).IsPerfect K) :
    (∀ φ : (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj E ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj K,
      ∃ (j : I) (h : D.base ≤ j) (ψ : (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj E ⟶
          (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).obj K),
        φ = (D.stageProjectionDerivedPullbackIso h E).inv ≫
          (derivedPullback (spacesEtaleModelHom B S hS
            (ObjectProperty.homMk (D.limitCone.π.app (op j)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
                ⟨D.system.obj (op j), D.algebraicSpace j⟩))).map ψ ≫
          (D.stageProjectionDerivedPullbackIso h K).hom) ∧
    (∀ φ ψ : E ⟶ K,
      (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map φ =
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map ψ →
      ∃ (j : I) (h : D.base ≤ j),
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map φ =
          (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map ψ)
 := by
  have hbase' := hbase
  obtain ⟨T, hT, ⟨eT⟩⟩ := hbase'
  have hspec := exists_iso_mk_spec B S hS T hT
  obtain ⟨A₀, _, hA₀, p₀, ⟨eA⟩⟩ := hspec
  let g₀ : (⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj (BigFppfOver.mk B S hS hA₀ p₀), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ (eT ≪≫ yoneda.mapIso eA)
  have hE' := exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso B S hS hA₀ p₀ g₀ E hE
  obtain ⟨C, hbd, hfin, hproj, ⟨eE⟩⟩ := hE'
  have hK' := exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso B S hS hA₀ p₀ g₀ K hK
  obtain ⟨C', hbd', hfin', hproj', ⟨eK⟩⟩ := hK'
  have hle : ∀ M : CochainComplex (ModuleCat.{u} A₀) ℤ, {i : ℤ | ¬ IsZero (M.X i)}.Finite →
      ∃ b, M.IsStrictlyLE b := fun M hM => by
    obtain ⟨b, hb₁⟩ := hM.bddAbove
    exact ⟨b, (CochainComplex.isStrictlyLE_iff _ _).2 fun _ hn =>
      not_not.1 fun hz => not_lt.2 (hb₁ hz) hn⟩
  have hb₁ := hle C hbd
  obtain ⟨b, hCb⟩ := hb₁
  have hb₁' := hle C' hbd'
  obtain ⟨b', hCb'⟩ := hb₁'
  refine ⟨fun φ => ?_, fun φ ψ h => ?_⟩
  · obtain ⟨j, hj, ψ', hψ'⟩ := D.exists_derivedPullback_map_eq_comp_of_pointTensor hA₀ p₀ g₀ C C'
      b b' hCb hbd hfin hproj hCb' hbd' hfin' hproj' hb hbase
      ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map eE.inv ≫ φ ≫
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op D.base)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map eK.hom)
    refine ⟨j, hj, (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hj).op) :
          (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map eE.hom ≫ ψ' ≫
      (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.system.map (homOfLE hj).op) :
          (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩))).map eK.inv, ?_⟩
    have n1 := D.stageProjectionDerivedPullbackIso_hom_naturality hj eE.hom
    have n2 := D.stageProjectionDerivedPullbackIso_hom_naturality hj eK.inv
    simp only [Functor.map_comp]
    exact Iso.eq_inv_comp_comp_hom_of_naturality _ _ _ _ (Functor.mapIso _ eE) (Functor.mapIso _ eK)
      _ _ _ φ n1 n2 hψ'
  · obtain ⟨j, hj, hj'⟩ := D.exists_derivedPullback_map_eq_of_pointTensor hA₀ p₀ g₀ C C' b b' hCb
      hbd hfin hproj hCb' hbd' hfin' hproj' hb hbase _ _
      (Functor.map_conj_eq_of_map_eq _ eE eK φ ψ h)
    exact ⟨j, hj, Functor.map_eq_of_map_conj_eq _ eE eK φ ψ hj'⟩


/-- **Stacks 09RI–09RJ, full faithfulness for perfect objects, over an affine chosen stage.** In
Situation 09RH with charts bounded in size and `X₀` affine, for perfect `Eᵢ`, `Kᵢ` on a stage
`Xᵢ` (`i ≥ 0`) every morphism `Lfᵢ^*Eᵢ ⟶ Lfᵢ^*Kᵢ` comes from a stage `j ≥ i`, and two morphisms
`Eᵢ ⟶ Kᵢ` with the same image at the limit have the same image at a stage `j ≥ i`: the stage
`Xᵢ` is affine over the affine `X₀`, so the case `i = 0` applies to the situation with chosen
stage `i`. -/
theorem perfectHomsDescend_of_isAffineSpace (hb : ChartsBounded B S hS D.system)
    (hbase : IsAffineSpace B S hS (D.system.obj (op D.base))) : D.PerfectHomsDescend :=
  fun i hi E K hE hK =>
    ({ D with base := i } : DescentSituation B S hS hZ I).perfectHomsDescend_base_of_isAffineSpace
      hb ((D.transition_affine (homOfLE hi).op).isAffineSpace_source hbase) E K hE hK

variable {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAlgebraicSpace B S hS U₀)
  (hU₀qc : IsQuasiCompactSpace B S hS U₀) (hU₀qs : IsAbsolutelyQuasiSeparated B S hS hZ U₀)
  (u : U₀ ⟶ D.system.obj (op D.base))

/-- **Stacks 09RI–09RJ, full faithfulness, for an affine `U₀`**: morphisms between perfect objects
on the stages `U_i = X_i ×_{X₀} U₀` descend, when the charts of the situation are bounded and
`U₀` is affine. With
`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_restrictTo_of_isAffineSpace`
this is the affine case of the induction of Stacks 08GP in the source's proof. -/
theorem perfectHomsDescend_restrictTo_of_isAffineSpace (hb : ChartsBounded B S hS D.system)
    (hU₀aff : IsAffineSpace B S hS U₀) :
    (D.restrictTo hU₀ hU₀qc hU₀qs u).PerfectHomsDescend :=
  (D.restrictTo hU₀ hU₀qc hU₀qs u).perfectHomsDescend_of_isAffineSpace
    (D.chartsBounded_restrictTo hU₀ hU₀qc hU₀qs u hb)
    (D.isAffineSpace_restrictTo_base hU₀ hU₀qc hU₀qs u hU₀aff)

end DescentSituation



end AlgebraicGeometry.Space

end
