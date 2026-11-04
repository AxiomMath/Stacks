module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.TransportRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIdentityRigidity

/-!
# Automorphisms of a flat deformation are automorphisms of its solution

For a flat deformation `D = (f' : X' ⟶ Y', i : X ⟶ X')` of `f : X ⟶ Y` over the first order
thickening `Y ⊂ Y'`, an isomorphism `e : D ⟶ E` of deformations induces an isomorphism of the
solutions `0 → f^*𝒞_{Y/Y'} → i⁻¹𝒪_{X'} → 𝒪_X → 0` of the extension problem of
[Stacks Project, Tag 0D17] (`Deformation.ambientSolutionIso`, through `e^♯`), compatibly with
composition. This assignment is bijective on isomorphisms `D ⟶ E`:

* it is injective because a morphism of algebraic spaces is determined by its morphism of small
  étale ringed topoi (Stacks 04KL), and the transported morphism of ringed topoi of
  `ambientSolutionIso e` is 2-isomorphic to the one of `e`;
* it is surjective because, by Stacks 04KL over `Y'`, the transported morphism of ringed topoi of
  an isomorphism `σ` of solutions is induced by an isomorphism `e` of deformations; the two
  isomorphisms `ambientSolutionIso e` and `σ` of solutions then give 2-isomorphic morphisms of
  ringed topoi `(Sh(X_étale), i⁻¹𝒪_{X'}) ⟶ X'_étale` with the same underlying morphism of topoi,
  and they agree by the rigidity of the identity of `Sh(X_étale)` fixing `𝒪_X`
  (`AlgebraicGeometry.Space.smallEtale_identityEnd_eq_id`).

In particular the automorphism group of a flat deformation `(f', a)` — the automorphisms
`φ : X' ⟶ X'` over `Y'` reducing to the identity on `X' ×_{Y'} Y` — is the automorphism group of
its solution (`Deformation.autMulEquivAmbientSolution`).

## Main definitions
* `AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation.ambientSolutionIso`.
* `AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation.autMulEquivAmbientSolution`.

## References
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

open _root_.Deformation.ToposThickening.RingedToposExtensionProblem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Generic

variable {X X₁ X₂ X₃ : AlgebraicSpaces B S hS}

/-- The composition law of the maps `(u ≫ h)⁻¹𝒪 ⟶ u⁻¹𝒪` along chains of equalities
`i ≫ k₁ = j₂`, `j₂ ≫ k₂ = j₃`. -/
theorem eqToHom_inverseImageStructureSheafMap_comp (i : X ⟶ X₁) (k₁ : X₁ ⟶ X₂) (k₂ : X₂ ⟶ X₃)
    {j₂ : X ⟶ X₂} {j₃ : X ⟶ X₃} (h₂ : i ≫ k₁ = j₂) (h₃ : j₂ ≫ k₂ = j₃)
    (h : i ≫ k₁ ≫ k₂ = j₃) :
    (eqToHom (congrArg (inverseImageStructureSheaf B S hS) h₃.symm) ≫
        inverseImageStructureSheafMap B S hS j₂ k₂) ≫
      (eqToHom (congrArg (inverseImageStructureSheaf B S hS) h₂.symm) ≫
        inverseImageStructureSheafMap B S hS i k₁) =
    eqToHom (congrArg (inverseImageStructureSheaf B S hS) h.symm) ≫
      inverseImageStructureSheafMap B S hS i (k₁ ≫ k₂) := by
  subst h₂ h₃
  have he : eqToHom (congrArg (inverseImageStructureSheaf B S hS) h.symm) = 𝟙 _ :=
    eqToHom_refl _ _
  rw [he]
  simp only [eqToHom_refl, Category.id_comp]
  have hc := inverseImageStructureSheafMap_comp_comp i k₁ k₂
  simp only [inverseImageStructureSheafMap] at hc ⊢
  exact hc

end Generic

section LocallySurjective

universe v₃ u₃ w₃

/-- The underlying map of sheaves of sets of a locally surjective map of sheaves of rings is an
epimorphism. -/
theorem epi_forget_map_of_isLocallySurjective {𝒞 : Type u₃} [Category.{v₃} 𝒞]
    {J : GrothendieckTopology 𝒞} [J.HasSheafCompose (forget CommRingCat.{w₃})]
    {F G : Sheaf J CommRingCat.{w₃}} (φ : F ⟶ G) (h : Presheaf.IsLocallySurjective J φ.hom) :
    Epi ((sheafCompose J (forget CommRingCat.{w₃})).map φ) := by
  have : Sheaf.IsLocallySurjective φ := h
  infer_instance

end LocallySurjective

section Universal

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {X₀ : RingedTopos.{v₁, u₁, w₁}} {B₀ : RingedTopos.{v₂, u₂, w₂}}
  [X₀.J.HasSheafCompose (forget RingCat.{w₁})] [B₀.J.HasSheafCompose (forget RingCat.{w₂})]
  [X₀.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B₀.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  {P₀ : _root_.Deformation.ToposThickening.RingedToposExtensionProblem X₀ B₀}

/-- **A map of thickened structure sheaves over `𝒪_X` and under the thickened base is a morphism
of solutions** when `c` is universal: the identity on `𝒢` is automatic
(`kernel_comm_of_universal`). -/
def solutionHomOfUniversal (hc : P₀.CIsUniversal) {P Q : P₀.CompatibleFirstOrderThickening}
    (φ : P.extension ⟶ Q.extension) (hr : φ ≫ Q.reduction = P.reduction)
    (hb : P.baseMap ≫ φ = Q.baseMap) : CompatibleFirstOrderThickening.Hom P Q where
  hom := φ
  reduction_comm := hr
  baseMap_comm := hb
  kernel_comm := kernel_comm_of_universal hc φ hr hb

end Universal

variable {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)}

namespace Deformation

/-- The map `e^♯ : i_E⁻¹𝒪_{X'_E} = i_D⁻¹e⁻¹𝒪_{X'_E} ⟶ i_D⁻¹𝒪_{X'_D}` of an isomorphism
`e : D ⟶ E` of deformations. -/
def ambientSolutionMap {D E : Deformation f} (e : D ⟶ E) :
    inverseImageStructureSheaf B S hS E.i ⟶ inverseImageStructureSheaf B S hS D.i :=
  eqToHom (congrArg (inverseImageStructureSheaf B S hS) e.compat.symm) ≫
    inverseImageStructureSheafMap B S hS D.i e.hom.hom

/-- The map `e^♯` commutes with the reductions of the solutions of `E` and `D` to `𝒪_X`. -/
theorem ambientSolutionMap_reduction {D E : Deformation f} (e : D ⟶ E) :
    ambientSolutionMap e ≫ (D.ambientSolution hZ).reduction = (E.ambientSolution hZ).reduction := by
  rw [ambientSolution_reduction, ambientSolution_reduction]
  exact (Category.assoc _ _ _).trans ((congrArg _
    (inverseImageStructureSheafMap_comp_structureSharpInverseImage B S hS D.i e.hom.hom)).trans
    (structureSharpInverseImage_eqToHom B S hS e.compat.symm))

/-- The map `e^♯` commutes with the maps from the thickened base into the solutions of `E` and
`D`. -/
theorem ambientSolutionMap_baseMap {D E : Deformation f} (e : D ⟶ E) :
    (E.ambientSolution hZ).baseMap ≫ ambientSolutionMap e = (D.ambientSolution hZ).baseMap := by
  rw [ambientSolution_baseMap, ambientSolution_baseMap]
  exact ambientBaseMap_transport D.i e.hom.hom E.f' f (subspaceInclusion B S hS Y' Z)
    e.compat e.hom_f' E.isPullback.w.symm D.isPullback.w.symm

/-- `e^♯` as a morphism of solutions `E.ambientSolution ⟶ D.ambientSolution`. -/
def ambientSolutionHom {D E : Deformation f} (e : D ⟶ E) :
    CompatibleFirstOrderThickening.Hom.{u, u + 1, u, u, u + 1, u}
      (E.ambientSolution hZ) (D.ambientSolution hZ) :=
  solutionHomOfUniversal (cIsUniversal_problem hZ f) (ambientSolutionMap e)
    (ambientSolutionMap_reduction hZ e) (ambientSolutionMap_baseMap hZ e)

/-- **The isomorphism of solutions of an isomorphism of deformations**, `(e^♯)⁻¹`. -/
def ambientSolutionIso {D E : Deformation f} (e : D ⟶ E) :
    CompatibleFirstOrderThickening.Iso.{u, u + 1, u, u, u + 1, u}
      (D.ambientSolution hZ) (E.ambientSolution hZ) :=
  (CompatibleFirstOrderThickening.Hom.toIso (ambientSolutionHom hZ e)).symm

/-- The inverse of the underlying isomorphism of `ambientSolutionIso e` is `e^♯`. -/
theorem ambientSolutionIso_hom_inv {D E : Deformation f} (e : D ⟶ E) :
    (ambientSolutionIso hZ e).hom.inv = ambientSolutionMap e :=
  rfl

/-- Two isomorphisms of solutions are equal when their underlying inverses are. -/
private theorem solution_iso_eq_of_hom_inv_eq {D E : Deformation f}
    {σ τ : CompatibleFirstOrderThickening.Iso.{u, u + 1, u, u, u + 1, u}
      (D.ambientSolution hZ) (E.ambientSolution hZ)}
    (h : σ.hom.inv = τ.hom.inv) : σ = τ := by
  apply CompatibleFirstOrderThickening.Iso.ext
  exact CategoryTheory.Iso.ext ((CategoryTheory.Iso.inv_eq_inv _ _).1 h)

/-- `ambientSolutionIso` is compatible with composition. -/
theorem ambientSolutionIso_comp {D E F : Deformation f} (e₁ : D ⟶ E) (e₂ : E ⟶ F) :
    ambientSolutionIso hZ (e₁ ≫ e₂) =
      (ambientSolutionIso hZ e₁).trans (ambientSolutionIso hZ e₂) :=
  solution_iso_eq_of_hom_inv_eq hZ
    (eqToHom_inverseImageStructureSheafMap_comp D.i e₁.hom.hom e₂.hom.hom e₁.compat e₂.compat
    (e₁ ≫ e₂).compat).symm

/-! ### Bijectivity on isomorphisms -/

/-- **The transported morphism of ringed topoi of `ambientSolutionIso e` is induced by `e`**:
`e_small ∘ (i_D, 𝟙) ≅ (i_E, e^♯)` (Stacks 03G8), hence `e_small ≅ (i_E, e^♯) ∘ (i_D, 𝟙)⁻¹`. -/
def smallEtaleTwoIsoTransportHom {D E : Deformation f} (e : D ⟶ E) :
    SmallEtaleTwoIso B S hS (smallEtaleRingedToposHom B S hS e.hom.hom)
      (transportHom hZ (ambientSolutionIso hZ e)) :=
  letI := D.isEquivalence_i hZ
  twoIsoTransportOfCompWithRings.{u, u + 1, u} (smallEtaleRingedToposHom B S hS D.i)
    (smallEtaleRingedToposHom B S hS E.i) (ambientSolutionMap e)
    (smallEtaleRingedToposHom B S hS e.hom.hom)
    ((smallCompWithRingsTwoIso D.i e.hom.hom (𝟙 _)).trans
      (withRingsHomEqTwoIso e.compat _ _ (by
        simp only [Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctor_obj,
          ambientSolutionMap, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        exact Category.comp_id _)))

/-- **`ambientSolutionIso` is injective**: a morphism of algebraic spaces is determined by its
morphism of small étale ringed topoi (Stacks 04KL), and that of `e` is the transported morphism
of `ambientSolutionIso e`. -/
theorem ambientSolutionIso_injective {D E : Deformation f} :
    Function.Injective (ambientSolutionIso hZ (D := D) (E := E)) := by
  intro e e' h
  have hk : e.hom.hom = e'.hom.hom := eq_of_inducesSmallEtaleRingedToposHom B S hS
    (isRecoveredFromSmallEtale_holds B S hS) _ _
    ⟨(smallEtaleTwoIsoTransportHom hZ e).trans
      (h ▸ (smallEtaleTwoIsoTransportHom hZ e').symm)⟩
  exact Deformation.Iso.ext (CategoryTheory.Iso.ext hk)

/-- `ambientSolutionIso e` is determined by `e^♯`. -/
theorem ambientSolutionIso_eq_of_map_eq {D E : Deformation f} (e : D ⟶ E)
    (σ : CompatibleFirstOrderThickening.Iso.{u, u + 1, u, u, u + 1, u}
      (D.ambientSolution hZ) (E.ambientSolution hZ))
    (h : ambientSolutionMap e = σ.hom.inv) : ambientSolutionIso hZ e = σ :=
  solution_iso_eq_of_hom_inv_eq hZ h

/-- **Rigidity**: an isomorphism `e` of deformations whose morphism of small étale ringed topoi is
2-isomorphic to the transported morphism of an isomorphism `σ` of solutions has
`ambientSolutionIso e = σ`: `(i_E, e^♯)` and `(i_E, σ⁻¹)` are then 2-isomorphic, and they agree by
the rigidity of the identity of `Sh(X_étale)` fixing `𝒪_X`. -/
theorem ambientSolutionIso_eq_of_twoIso {D E : Deformation f} (e : D ⟶ E)
    (σ : CompatibleFirstOrderThickening.Iso.{u, u + 1, u, u, u + 1, u}
      (D.ambientSolution hZ) (E.ambientSolution hZ))
    (t : SmallEtaleTwoIso B S hS (smallEtaleRingedToposHom B S hS e.hom.hom)
      (transportHom hZ σ)) :
    ambientSolutionIso hZ e = σ := by
  let := D.isEquivalence_i hZ
  have := E.isEquivalence_i hZ
  have θ₁ : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (A := withRings (smallEtaleRingedTopos B S hS X) (inverseImageStructureSheaf B S hS D.i))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (X := withRings (smallEtaleRingedTopos B S hS X) (inverseImageStructureSheaf B S hS D.i))
        (transport.{u, u + 1, u} (smallEtaleRingedToposHom B S hS D.i)
          (smallEtaleRingedToposHom B S hS E.i) (ambientSolutionMap e))
        (withRingsHom (smallEtaleRingedToposHom B S hS D.i) (𝟙 _)))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (X := withRings (smallEtaleRingedTopos B S hS X) (inverseImageStructureSheaf B S hS D.i))
        (transport.{u, u + 1, u} (smallEtaleRingedToposHom B S hS D.i)
          (smallEtaleRingedToposHom B S hS E.i) σ.hom.symm.hom)
        (withRingsHom (smallEtaleRingedToposHom B S hS D.i) (𝟙 _))) :=
    RingedToposHom.TwoIso.whiskerLeft
      (A := withRings (smallEtaleRingedTopos B S hS X) (inverseImageStructureSheaf B S hS D.i))
      (B := smallEtaleRingedTopos B S hS D.X') (C := smallEtaleRingedTopos B S hS E.X')
      (withRingsHom (smallEtaleRingedToposHom B S hS D.i) (𝟙 _))
      ((smallEtaleTwoIsoTransportHom hZ e).symm.trans t)
  have θ := (transportCompWithRingsTwoIso.{u, u + 1, u} (smallEtaleRingedToposHom B S hS D.i)
      (smallEtaleRingedToposHom B S hS E.i) (ambientSolutionMap e)).symm.trans
    (θ₁.trans (transportCompWithRingsTwoIso.{u, u + 1, u} (smallEtaleRingedToposHom B S hS D.i)
        (smallEtaleRingedToposHom B S hS E.i) σ.hom.symm.hom))
  have hr : ambientSolutionMap e ≫ (D.ambientSolution hZ).reduction =
      σ.hom.symm.hom ≫ (D.ambientSolution hZ).reduction :=
    (ambientSolutionMap_reduction hZ e).trans σ.symm.reduction_comm.symm
  have hepi : Epi ((smallEtaleRingedTopos B S hS X).forgetRing.map
      (ambientSolutionMap e ≫ (D.ambientSolution hZ).reduction)) :=
    epi_forget_map_of_isLocallySurjective _
      ((ambientSolutionMap_reduction hZ e).symm ▸ (E.ambientSolution hZ).locallySurjective)
  exact ambientSolutionIso_eq_of_map_eq hZ e σ <|
    eq_of_withRingsHom_twoIso.{u, u + 1, u} (smallEtaleRingedToposHom B S hS E.i)
      (ambientSolutionMap e) σ.hom.symm.hom (D.ambientSolution hZ).reduction hr hepi
      (smallEtale_identityEnd_eq_id B S hS X) θ

/-- **`ambientSolutionIso` is surjective**: by Stacks 04KL over `Y'` the transported morphism of
ringed topoi of an isomorphism `σ` of solutions is induced by an isomorphism `e` of deformations
(as in `nonempty_hom_of_iso`); then `(i_E, e^♯)` and `(i_E, σ⁻¹)` are 2-isomorphic, so they agree
by the rigidity of the identity of `Sh(X_étale)` fixing `𝒪_X`. -/
theorem exists_ambientSolutionIso_eq {D E : Deformation f}
    (σ : CompatibleFirstOrderThickening.Iso.{u, u + 1, u, u, u + 1, u}
      (D.ambientSolution hZ) (E.ambientSolution hZ)) :
    ∃ e : D ⟶ E, ambientSolutionIso hZ e = σ := by
  have hKL : IsRecoveredFromSmallEtale B S hS := isRecoveredFromSmallEtale_holds B S hS
  obtain ⟨k, ⟨t⟩, -⟩ := hKL D.f' E.f' (transportHom hZ σ) (isLocallyRinged_transportHom hZ σ)
    ⟨transportBaseTwoIso hZ σ⟩
  have hi : D.i ≫ k = E.i := eq_of_inducesSmallEtaleRingedToposHom B S hS hKL _ _
    ⟨(smallEtaleRingedToposHomCompTwoIso B S hS D.i k).symm.trans
      ((RingedToposHom.TwoIso.whiskerLeft (smallEtaleRingedToposHom B S hS D.i) t).trans
        (transportSquareTwoIso hZ σ))⟩
  have hf : k ≫ E.f' = D.f' := eq_of_inducesSmallEtaleRingedToposHom B S hS hKL _ _
    ⟨(smallEtaleRingedToposHomCompTwoIso B S hS k E.f').symm.trans
      ((RingedToposHom.TwoIso.whiskerRight t (smallEtaleRingedToposHom B S hS E.f')).trans
        (transportBaseTwoIso hZ σ))⟩
  have := (isIso_transportHom hZ σ).1
  have := (isIso_transportHom hZ σ).2
  have : (smallEtaleRingedToposHom B S hS k).toToposHom.pushforward.IsEquivalence :=
    Functor.isEquivalence_of_iso t.e.symm
  have : IsIso (smallEtaleRingedToposHom B S hS k).fSharp := by
    have hc : RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS k) =
        RingedToposHom.forgetFSharp (transportHom hZ σ) ≫ t.e.inv.app _ := by
      rw [← t.commutes, Category.assoc, CategoryTheory.Iso.hom_inv_id_app, Category.comp_id]
    have : IsIso (RingedToposHom.forgetFSharp (transportHom hZ σ)) :=
      Functor.map_isIso _ (transportHom hZ σ).fSharp
    have : IsIso ((smallEtaleRingedTopos B S hS E.X').forgetRing.map
        (smallEtaleRingedToposHom B S hS k).fSharp) := by
      show IsIso (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS k))
      rw [hc]
      infer_instance
    exact isIso_of_reflects_iso _ (smallEtaleRingedTopos B S hS E.X').forgetRing
  have := isIso_of_isIso_smallEtaleRingedToposHom k
  exact ⟨_, ambientSolutionIso_eq_of_twoIso hZ { hom := asIso k, hom_f' := hf, compat := hi } σ t⟩

/-- **The automorphism group of a flat deformation is the automorphism group of its solution**:
an automorphism `φ : X' ⟶ X'` over `Y'` reducing to the identity on `X' ×_{Y'} Y` (an element
of `Aut D`) is sent to `(φ^♯)⁻¹`. -/
def autMulEquivAmbientSolution (D : Deformation f) :
    Aut D ≃* (D.ambientSolution hZ).AutomorphismGroup :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (M := Aut D) (G := Aut (D.ambientSolution hZ)) (fun a : Aut D =>
        (Groupoid.isoEquivHom (D.ambientSolution hZ) (D.ambientSolution hZ)).symm
          (ambientSolutionIso hZ a.hom))
      fun a b => CategoryTheory.Iso.ext (ambientSolutionIso_comp hZ b.hom a.hom))
    ⟨fun a b h => CategoryTheory.Iso.ext (ambientSolutionIso_injective hZ
        (congrArg CategoryTheory.Iso.hom h)),
      fun x => by
        obtain ⟨e, he⟩ := exists_ambientSolutionIso_eq hZ x.hom
        exact ⟨(Groupoid.isoEquivHom D D).symm e, CategoryTheory.Iso.ext he⟩⟩

/-- The image of an automorphism `a` of `D` under `autMulEquivAmbientSolution` has underlying
isomorphism `ambientSolutionIso a.hom`. -/
theorem autMulEquivAmbientSolution_apply_hom (D : Deformation f) (a : Aut D) :
    (autMulEquivAmbientSolution hZ D a).hom = ambientSolutionIso hZ a.hom :=
  rfl

end Deformation

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
