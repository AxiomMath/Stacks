module

public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedAssocTot
public import StacksFrontier.Homology.DerivedCategory.Monoidal.InvertibleChainInverse
public import StacksFrontier.Algebra.Homology.MapBifunctorHomotopyEquiv

/-!
# Global sections of a chain-level tensor pairing of finite free summands

Let `(Y, 𝒪_Y)` be a ringed space, `R = Γ(Y, 𝒪_Y)`, and let `E`, `F` be bounded complexes of
`𝒪_Y`-modules whose terms are direct summands of finite free modules. If `Tot(E ⊗ F)` is
homotopy equivalent to `𝒪_Y[0]`, then `Tot(Γ(Y, E) ⊗_R Γ(Y, F))` is homotopy equivalent to
`R[0]`.

## References

* [Stacks Project, Tag 0FPF](https://stacks.math.columbia.edu/tag/0FPF)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Opposite TopologicalSpace Stacks.SheafOfModules.DerivedMonoidal Stacks.AssociatedSheaf
open StrictlyPerfect

universe u

namespace Stacks.Cohomology.InvertibleDerived

variable (Y : RingedSpace.{u, u})

/-- Global sections of a direct summand of a finite free module form a finite projective module
over the global sections. -/
public theorem gamma_finite_projective (G : OXMod.{u, u} Y) (hG : IsDirectSummandOfFiniteFree G) :
    Module.Finite (GlobalRing Y) ((gammaF Y).obj G) ∧
      Module.Projective (GlobalRing Y) ((gammaF Y).obj G) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract G).mp hG
  have := isIso_unit_free Y (ULift.{u} (Fin n))
  let ρ' : Retract G ((assocF Y).obj ((ModuleCat.free (GlobalRing Y)).obj (ULift.{u} (Fin n)))) :=
    ρ.trans (Retract.ofIso (StrictlyPerfect.finiteFreeIsoFree Y n ≪≫
      freeIsoAssociatedSheaf Y (RingHom.id (GlobalRing Y)) (ULift.{u} (Fin n))))
  let σ : Retract ((gammaF Y).obj G)
      ((ModuleCat.free (GlobalRing Y)).obj (ULift.{u} (Fin n))) :=
    (ρ'.map (gammaF Y)).trans (Retract.ofIso
      (asIso ((assocAdj Y).unit.app
        ((ModuleCat.free (GlobalRing Y)).obj (ULift.{u} (Fin n))))).symm)
  have hσ : σ.r.hom.comp σ.i.hom = LinearMap.id :=
    congrArg ModuleCat.Hom.hom σ.retract
  have : Module.Finite (GlobalRing Y)
      ((ModuleCat.free (GlobalRing Y)).obj (ULift.{u} (Fin n))) :=
    inferInstanceAs (Module.Finite _ (ULift.{u} (Fin n) →₀ GlobalRing Y))
  have : Module.Projective (GlobalRing Y)
      ((ModuleCat.free (GlobalRing Y)).obj (ULift.{u} (Fin n))) :=
    inferInstanceAs (Module.Projective _ (ULift.{u} (Fin n) →₀ GlobalRing Y))
  exact ⟨Module.Finite.of_surjective σ.r.hom
      (Function.LeftInverse.surjective (LinearMap.congr_fun hσ)),
    Module.Projective.of_split σ.i.hom σ.r.hom hσ⟩

/-- A coproduct of finite modules all but finitely many of which vanish is finite. -/
public theorem finite_coproduct_of_isZero {R : Type u} [CommRing R] {ι : Type}
    (F : ι → ModuleCat.{u} R) [∀ j, Module.Finite R (F j)] [HasCoproduct F] (s : Finset ι)
    (hs : ∀ j, j ∉ s → IsZero (F j)) : Module.Finite R (∐ F : ModuleCat R) := by
  classical
  let G : s → ModuleCat.{u} R := fun j => F j
  have : Module.Finite R (∐ G : ModuleCat R) :=
    Module.Finite.equiv (ModuleCat.coprodIsoDirectSum G).symm.toLinearEquiv
  let f : (∐ G : ModuleCat R) ⟶ ∐ F := Sigma.desc (fun j => Sigma.ι F j)
  have : Epi f := ⟨fun g h heq => Sigma.hom_ext _ _ fun j => by
    by_cases hj : j ∈ s
    · simpa only [f, Category.assoc, Sigma.ι_desc_assoc] using
        congrArg (fun k => Sigma.ι G ⟨j, hj⟩ ≫ k) heq
    · exact (hs j hj).eq_of_src _ _⟩
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)

/-- The total tensor complex of two bounded complexes of finite projective modules has finite
projective terms when one of them is bounded. -/
public theorem tensor_finite_projective {R : Type u} [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hPz : ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hP : ∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i))
    (hQ : ∀ i, Module.Finite R (Q.X i) ∧ Module.Projective R (Q.X i)) (i : ℤ) :
    Module.Finite R ((P ⊗ Q).X i) ∧ Module.Projective R ((P ⊗ Q).X i) := by
  classical
  let F : {pq : ℤ × ℤ // pq.1 + pq.2 = i} → ModuleCat.{u} R :=
    fun pq => P.X pq.1.1 ⊗ Q.X pq.1.2
  have : ∀ j, Module.Finite R (F j) := fun j => by
    have := (hP j.1.1).1
    have := (hQ j.1.2).1
    exact Module.Finite.tensorProduct R _ _
  have : ∀ j, Module.Projective R (F j) := fun j => by
    have := (hP j.1.1).2
    have := (hQ j.1.2).2
    change Module.Projective R (TensorProduct R (P.X j.1.1) (Q.X j.1.2))
    infer_instance
  change Module.Finite R (∐ F : ModuleCat R) ∧ Module.Projective R (∐ F : ModuleCat R)
  refine ⟨?_, Module.Projective.of_equiv (ModuleCat.coprodIsoDirectSum F).symm.toLinearEquiv⟩
  let s : Finset {pq : ℤ × ℤ // pq.1 + pq.2 = i} :=
    (Finset.Icc a b).map
      ⟨fun p => ⟨(p, i - p), by omega⟩, fun p q h => congrArg (fun z => z.1.1) h⟩
  refine finite_coproduct_of_isZero F s fun j hj => ?_
  have hj' : ¬(a ≤ j.1.1 ∧ j.1.1 ≤ b) := fun h => hj (Finset.mem_map.mpr
    ⟨j.1.1, Finset.mem_Icc.mpr h, Subtype.ext (Prod.ext rfl (show i - j.1.1 = j.1.2 by
      have := j.2; omega))⟩)
  exact (MonoidalCategory.tensorRight (Q.X j.1.2)).map_isZero (hPz j.1.1 (by omega))

/-- A complex of finite projective modules over the global sections is the complex of global
sections of its associated complex of sheaves. -/
public def unitIsoComplex (P : CochainComplex (ModuleCat.{u} (GlobalRing Y)) ℤ)
    (hP : ∀ i, Module.Finite (GlobalRing Y) (P.X i) ∧ Module.Projective (GlobalRing Y) (P.X i)) :
    P ≅ ((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((assocF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      haveI := (hP i).1
      haveI := (hP i).2
      haveI := isIso_assocAdj_unit Y (P.X i)
      asIso ((assocAdj Y).unit.app (P.X i)))
    (fun i j _ => ((assocAdj Y).unit.naturality (P.d i j)).symm)

/-- Global sections of the structure sheaf, as a module over the global sections. -/
public def gammaUnitIso :
    (gammaF Y).obj (SheafOfModules.unit _) ≅ 𝟙_ (ModuleCat.{u} (GlobalRing Y)) :=
  (gammaF Y).mapIso (Stacks.AssociatedSheaf.associatedSheafUnitIso Y
      (RingHom.id (GlobalRing Y))).symm ≪≫
    (haveI := isIso_assocAdj_unit Y (ModuleCat.of (GlobalRing Y) (GlobalRing Y));
      asIso ((assocAdj Y).unit.app (ModuleCat.of (GlobalRing Y) (GlobalRing Y)))).symm

/-- **Global sections of a chain-level tensor pairing of finite free summands.** If `E` and `F`
are complexes of direct summands of finite free `𝒪_Y`-modules and `Tot(E ⊗ F)` is homotopy
equivalent to `𝒪_Y[0]`, then `Tot(Γ(Y, E) ⊗_R Γ(Y, F))` is homotopy equivalent to `R[0]`, provided
`E` is bounded. -/
public def gammaTensorHomotopyEquiv
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hE : ∀ i, IsDirectSummandOfFiniteFree (E.X i)) (hF : ∀ i, IsDirectSummandOfFiniteFree (F.X i))
    (a b : ℤ) (hEz : ∀ i, (i < a ∨ b < i) → IsZero (E.X i))
    (h : HomotopyEquiv (HomologicalComplex.mapBifunctor E F
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _))) :
    HomotopyEquiv (((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ⊗
        ((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
      (𝟙_ (CochainComplex (ModuleCat.{u} (GlobalRing Y)) ℤ)) := by
  let P := ((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  let P' := ((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  have hP : ∀ i, Module.Finite (GlobalRing Y) (P.X i) ∧ Module.Projective (GlobalRing Y) (P.X i) :=
    fun i => gamma_finite_projective Y (E.X i) (hE i)
  have hP' : ∀ i, Module.Finite (GlobalRing Y) (P'.X i) ∧
      Module.Projective (GlobalRing Y) (P'.X i) :=
    fun i => gamma_finite_projective Y (F.X i) (hF i)
  have hPz : ∀ i, (i < a ∨ b < i) → IsZero (P.X i) := fun i hi =>
    (gammaF Y).map_isZero (hEz i hi)
  let h1 := HomotopyEquiv.ofIso (unitIsoComplex Y (P ⊗ P')
    (tensor_finite_projective P P' a b hPz hP hP'))
  let h2 := HomotopyEquiv.ofIso (((gammaF Y).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (assocTotIso Y P P'))
  let h3 : HomotopyEquiv (HomologicalComplex.mapBifunctor
      (((assocR Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (((assocR Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj P')
      (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf) (ComplexShape.up ℤ))
      (HomologicalComplex.mapBifunctor E
      F (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
      (ComplexShape.up ℤ)) :=
    HomologicalComplex.mapBifunctorHomotopyEquiv _ _
      (HomotopyEquiv.ofIso (assocGammaIso Y E hE)) (HomotopyEquiv.ofIso (assocGammaIso Y F hF))
  let h4 := (gammaF Y).mapHomotopyEquiv (h3.trans h)
  let h5 := HomotopyEquiv.ofIso (((HomologicalComplex.singleMapHomologicalComplex (gammaF Y)
    (ComplexShape.up ℤ) 0).app (SheafOfModules.unit _)) ≪≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso (gammaUnitIso Y))
  exact h1.trans (h2.trans (h4.trans h5))

end Stacks.Cohomology.InvertibleDerived

end
