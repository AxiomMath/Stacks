module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionFullyFaithfulProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionExact

/-!
# Stacks 08B9 on compatible families of maps to the quotients

Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `X` be an algebraic
space locally of finite type over `Spec A`.  For coherent `𝒪_X`-modules `F`, `G` with support
proper over `Spec A`, a family of maps `a_n : F ⟶ G / I^{n+1} G` compatible with the projections
`G / I^{n+2} G ⟶ G / I^{n+1} G` comes from a unique map `F ⟶ G`
(`AlgebraicGeometry.Space.existsUnique_hom_of_compatible_idealPowerQuotient`).  This is the form
of Stacks 08B9 (`AlgebraicGeometry.Space.C1573.bijective_completionFunctorProperOver_map`) in which
a morphism of adic systems out of the completion of `F` is given by its composites with the
projections from `F`.

## References

* [Stacks Project, Tag 08B9](https://stacks.math.columbia.edu/tag/08B9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- The map `M / 𝓘 ^ k M ⟶ N` induced by a morphism `M ⟶ N` into a module annihilated by
`𝓘 ^ k`. -/
def idealPowerQuotientDesc (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (a : M ⟶ N)
    (hN : idealPowerMultiple B S hS F hF 𝓘 k N = ⊥) :
    idealPowerQuotient B S hS F hF 𝓘 k M ⟶ N :=
  cokernel.desc _ a (idealPowerMultiple_ι_comp_eq_zero_of_eq_bot B S hS F hF 𝓘 k a hN)

/-- The projection `M ⟶ M / 𝓘 ^ k M` followed by `idealPowerQuotientDesc` is the original map
`M ⟶ N`. -/
@[reassoc (attr := simp)]
theorem π_idealPowerQuotientDesc (k : ℕ) {M N : Modules.{u, u} B S hS F hF} (a : M ⟶ N)
    (hN : idealPowerMultiple B S hS F hF 𝓘 k N = ⊥) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι ≫
        idealPowerQuotientDesc B S hS F hF 𝓘 k a hN = a :=
  cokernel.π_desc _ _ _

/-- A family of maps into the quotients `N / 𝓘 ^ (n + 1) N` compatible with the successive
projections is compatible with all the projections. -/
theorem comp_idealPowerQuotientMapOfLE_of_succ {M N : Modules.{u, u} B S hS F hF}
    (a : ∀ n : ℕ, M ⟶ idealPowerQuotient B S hS F hF 𝓘 (n + 1) N)
    (ha : ∀ n, a (n + 1) ≫ idealPowerQuotientMapOfLE B S hS F hF 𝓘
      (Nat.le_succ (n + 1)) N = a n) {j i : ℕ} (hji : j ≤ i) :
    a i ≫ idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right hji 1) N = a j := by
  induction i, hji using Nat.le_induction with
  | base => rw [idealPowerQuotientMapOfLE_refl, Category.comp_id]
  | succ i hji ih =>
    rw [← idealPowerQuotientMapOfLE_comp B S hS F hF 𝓘 (Nat.add_le_add_right hji 1)
      (Nat.le_succ (i + 1)), reassoc_of% (ha i), ih]

/-- The maps out of the quotients induced by a compatible family commute with the projections. -/
theorem idealPowerQuotientMapOfLE_comp_idealPowerQuotientDesc {M N : Modules.{u, u} B S hS F hF}
    (a : ∀ n : ℕ, M ⟶ idealPowerQuotient B S hS F hF 𝓘 (n + 1) N)
    (ha : ∀ n, a (n + 1) ≫ idealPowerQuotientMapOfLE B S hS F hF 𝓘
      (Nat.le_succ (n + 1)) N = a n)
    (hbot : ∀ n, idealPowerMultiple B S hS F hF 𝓘 (n + 1)
      (idealPowerQuotient B S hS F hF 𝓘 (n + 1) N) = ⊥) {j i : ℕ} (hji : j ≤ i) :
    idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right hji 1) M ≫
        idealPowerQuotientDesc B S hS F hF 𝓘 (j + 1) (a j) (hbot j) =
      idealPowerQuotientDesc B S hS F hF 𝓘 (i + 1) (a i) (hbot i) ≫
        idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right hji 1) N := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (i + 1) M).ι)).1 ?_
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE, π_idealPowerQuotientDesc,
    π_idealPowerQuotientDesc_assoc]
  exact (comp_idealPowerQuotientMapOfLE_of_succ B S hS F hF 𝓘 a ha hji).symm

section Completion

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)

/-- **Stacks 08B9, on compatible families of maps to the quotients.**  Let `A` be a Noetherian
ring complete with respect to `I` and `X ⟶ Spec A` locally of finite type.  For coherent modules
`M`, `N` with support proper over `Spec A`, a family of maps `a_n : M ⟶ N / I^{n+1} N` compatible
with the projections comes from a unique map `M ⟶ N`. -/
theorem existsUnique_hom_of_compatible_idealPowerQuotient [IsNoetherianRing A] [IsAdicComplete I A]
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (M N : CoherentModulesProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf)
    (a : ∀ n : ℕ, M.obj.obj ⟶
      idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 (C1573.baseIdealSubmodule X.1 X.2 I) (n + 1)
        N.obj.obj)
    (ha : ∀ n, a (n + 1) ≫ idealPowerQuotientMapOfLE B (Spec (.of A)) hA X.1 X.2
      (C1573.baseIdealSubmodule X.1 X.2 I) (Nat.le_succ (n + 1)) N.obj.obj = a n) :
    ∃! b : M.obj.obj ⟶ N.obj.obj, ∀ n, b ≫ cokernel.π (idealPowerMultiple B (Spec (.of A)) hA
      X.1 X.2 (C1573.baseIdealSubmodule X.1 X.2 I) (n + 1) N.obj.obj).ι = a n := by
  let := C1573.fact_isLocallyNoetherian_of_baseObject X f hf
  let 𝓘 := C1573.baseIdealSubmodule X.1 X.2 I
  let hI := C1573.isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I
  let Φ := completionFunctorProperOver B (Spec (.of A)) hA X.1
    (schemeSpace (baseObject A B hA)).1 X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf 𝓘 hI
  have hbot : ∀ n, idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1)
      (idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) N.obj.obj) = ⊥ := fun n =>
    idealPowerMultiple_idealPowerQuotient_eq_bot B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) N.obj.obj
  let β : adicQuotientSystem B (Spec (.of A)) hA X.1 X.2 𝓘 M.obj.obj ⟶
      adicQuotientSystem B (Spec (.of A)) hA X.1 X.2 𝓘 N.obj.obj :=
    { app := fun n => idealPowerQuotientDesc B (Spec (.of A)) hA X.1 X.2 𝓘 (n.unop + 1)
        (a n.unop) (hbot n.unop)
      naturality := fun i j g =>
        idealPowerQuotientMapOfLE_comp_idealPowerQuotientDesc B (Spec (.of A)) hA X.1 X.2 𝓘 a ha
          hbot (leOfHom g.unop) }
  let β' : Φ.obj M ⟶ Φ.obj N := ObjectProperty.homMk (ObjectProperty.homMk β)
  have hb := C1573.bijective_completionFunctorProperOver_map X I f hf M N
  have hspec : ∀ b : M ⟶ N, Φ.map b = β' ↔ ∀ n, b.hom.hom ≫ cokernel.π (idealPowerMultiple B
      (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) N.obj.obj).ι = a n := by
    refine fun b => ⟨fun h n => ?_, fun h => ?_⟩
    · have h' := congrArg (fun c : Φ.obj M ⟶ Φ.obj N => c.hom.hom.app (op n)) h
      change idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) b.hom.hom =
        idealPowerQuotientDesc B (Spec (.of A)) hA X.1 X.2 𝓘 (n + 1) (a n) (hbot n) at h'
      rw [← π_comp_idealPowerQuotientMapOfHom, h', π_idealPowerQuotientDesc]
    · refine ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_)))
      refine (cancel_epi (cokernel.π (idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 𝓘
        (n.unop + 1) M.obj.obj).ι)).1 ?_
      change cokernel.π _ ≫ idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 𝓘
          (n.unop + 1) b.hom.hom =
        cokernel.π _ ≫ idealPowerQuotientDesc B (Spec (.of A)) hA X.1 X.2 𝓘 (n.unop + 1)
          (a n.unop) (hbot n.unop)
      rw [π_comp_idealPowerQuotientMapOfHom, π_idealPowerQuotientDesc]
      exact h n.unop
  obtain ⟨b, hb'⟩ := hb.2 β'
  exact ⟨b.hom.hom, (hspec b).1 hb', fun c hc => congrArg (fun d : M ⟶ N => d.hom.hom)
    (hb.1 (((hspec (ObjectProperty.homMk (ObjectProperty.homMk c))).2 hc).trans hb'.symm))⟩

end Completion

end AlgebraicGeometry.Space

end
