module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsAssociatedSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedGlobalPairing

/-!
# Global sections of a chain-level tensor pairing of finite free summands, on a ringed site

Let `(C, O)` be a ringed site, `R = Γ(C, O)`, and let `E`, `F` be complexes of `O`-modules whose
terms are direct summands of finite free modules, `E` bounded. If `Tot(E ⊗ F)` is homotopy
equivalent to `O[0]`, then `Tot(Γ(E) ⊗_R Γ(F))` is homotopy equivalent to `R[0]`.

This is the step of the proof of `(1) ⟹ (2)` of Stacks 0FPY which passes, by Stacks 0FPX, from
the sheaves to the global sections: "`α` and `β` correspond to maps of complexes
`a : R → Tot(M ⊗_R N)` and `b : Tot(M ⊗_R N) → R`, … `b ∘ a = 1` and `b ∘ a - 1 = dh + hd`".

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0FPX](https://stacks.math.columbia.edu/tag/0FPX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

variable (X : RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Global sections of a direct summand of a finite free module form a finite projective module
over the global sections. -/
theorem gamma_finite_projective
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hG : _root_.IsDirectSummandOfFiniteFree _ G) :
    Module.Finite (GammaRing X) ((gammaF X).obj G) ∧
      Module.Projective (GammaRing X) ((gammaF X).obj G) := by
  obtain ⟨n, i, r, h⟩ := (_root_.isDirectSummandOfFiniteFree_iff_free _ G).mp hG
  have := isIso_assocAdj_unit_free X n
  let e : (assocF X).obj (freeG X n) ≅ SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (ULift.{u} (Fin n)) :=
    sectionTensorFreeIso.{u, u, u} X.O (ULift.{u} (Fin n))
  let ρ' : Retract G ((assocF X).obj (freeG X n)) :=
    (⟨i, r, h⟩ : Retract G _).trans (Retract.ofIso e.symm)
  let σ : Retract ((gammaF X).obj G) (freeG X n) :=
    (ρ'.map (gammaF X)).trans (Retract.ofIso (asIso ((assocAdj X).unit.app (freeG X n))).symm)
  have hσ : σ.r.hom.comp σ.i.hom = LinearMap.id := congrArg ModuleCat.Hom.hom σ.retract
  have : Module.Finite (GammaRing X) (freeG X n) :=
    inferInstanceAs (Module.Finite _ (ULift.{u} (Fin n) →₀ GammaRing X))
  have : Module.Projective (GammaRing X) (freeG X n) :=
    inferInstanceAs (Module.Projective _ (ULift.{u} (Fin n) →₀ GammaRing X))
  exact ⟨Module.Finite.of_surjective σ.r.hom
      (Function.LeftInverse.surjective (fun m => LinearMap.congr_fun hσ m)),
    Module.Projective.of_split σ.i.hom σ.r.hom hσ⟩

/-- A complex of finite projective modules over the global sections is the complex of global
sections of its associated complex of sheaves. -/
def unitIsoComplex (P : CochainComplex (ModuleCat.{u} (GammaRing X)) ℤ)
    (hP : ∀ i, Module.Finite (GammaRing X) (P.X i) ∧ Module.Projective (GammaRing X) (P.X i)) :
    P ≅ ((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((assocF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => haveI := (hP i).1; haveI := (hP i).2
      haveI := isIso_assocAdj_unit X (P.X i)
      asIso ((assocAdj X).unit.app (P.X i)))
    (fun i j _ => ((assocAdj X).unit.naturality (P.d i j)).symm)

/-- A complex of direct summands of finite free modules is the complex associated to its complex
of global sections. -/
def assocGammaIso
    (E : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (E.X i)) :
    ((assocF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) ≅ E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => haveI := isIso_assocAdj_counit X (E.X i) (hE i)
      asIso ((assocAdj X).counit.app (E.X i)))
    (fun i j _ => ((assocAdj X).counit.naturality (E.d i j)).symm)

/-- Global sections of the structure sheaf, as a module over the global sections. -/
def gammaUnitIso :
    (gammaF X).obj (SheafOfModules.unit _) ≅ 𝟙_ (ModuleCat.{u} (GammaRing X)) :=
  (globalSectionsUnitIso.{u, u, u} X.O).symm

/-- **Global sections of a chain-level tensor pairing of finite free summands.** If `E` and `F`
are complexes of direct summands of finite free `O`-modules, `E` bounded, and `Tot(E ⊗ F)` is
homotopy equivalent to `O[0]`, then `Tot(Γ(E) ⊗_R Γ(F))` is homotopy equivalent to `R[0]`. -/
def gammaTensorHomotopyEquiv
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (E.X i))
    (hF : ∀ i, _root_.IsDirectSummandOfFiniteFree _ (F.X i))
    (a b : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero (E.X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor E F
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    HomotopyEquiv (((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⊗
        ((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
      (𝟙_ (CochainComplex (ModuleCat.{u} (GammaRing X)) ℤ)) := by
  let P := ((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  let P' := ((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have hP : ∀ i, Module.Finite (GammaRing X) (P.X i) ∧ Module.Projective (GammaRing X) (P.X i) :=
    fun i => gamma_finite_projective X (E.X i) (hE i)
  have hP' : ∀ i, Module.Finite (GammaRing X) (P'.X i) ∧
      Module.Projective (GammaRing X) (P'.X i) :=
    fun i => gamma_finite_projective X (F.X i) (hF i)
  have hPz : ∀ i, (i < a ∨ b < i) → IsZero (P.X i) := fun i hi =>
    (gammaF X).map_isZero (hEz i hi)
  let h1 := HomotopyEquiv.ofIso (unitIsoComplex X (P ⊗ P')
    (Stacks.Cohomology.InvertibleDerived.tensor_finite_projective P P' a b hPz hP hP'))
  let h2 := HomotopyEquiv.ofIso (((gammaF X).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (assocTotIso P P'))
  let h3 : HomotopyEquiv (HomologicalComplex.mapBifunctor
      (((assocF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (((assocF X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P')
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))
      (HomologicalComplex.mapBifunctor E F
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) :=
    HomologicalComplex.mapBifunctorHomotopyEquiv _ _
      (HomotopyEquiv.ofIso (assocGammaIso X E hE)) (HomotopyEquiv.ofIso (assocGammaIso X F hF))
  let h4 := (gammaF X).mapHomotopyEquiv (h3.trans h)
  let h5 := HomotopyEquiv.ofIso (((HomologicalComplex.singleMapHomologicalComplex (gammaF X)
    (ComplexShape.up ℤ) 0).app (SheafOfModules.unit _)) ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso (gammaUnitIso X))
  exact h1.trans (h2.trans (h4.trans h5))

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
