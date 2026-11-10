module

public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.CategoryTheory.Sites.Stack.SquareCocone
public import StacksFrontier.RingTheory.CompleteLocalRing.FiniteEtaleResidueExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Base change of a formal object along a local homomorphism

Let `ξ = (R, ξ_n, f_n)` be a formal object of a category `p` fibred in groupoids over the big fppf
site of `S` (**Stacks 07X4**), and let `R → R'` be a local homomorphism of Noetherian complete
local `S`-algebras with finite type residue fields. A local homomorphism maps `𝔪_R ^ (n + 1)` into
`𝔪_{R'} ^ (n + 1)`, so it induces maps `Spec (R' / 𝔪_{R'} ^ (n + 1)) ⟶ Spec (R / 𝔪_R ^ (n + 1))`
of infinitesimal thickenings, compatible with their inclusions into one another. Pulling `ξ_n`
back along them gives a formal object `ξ'` over `R'`, together with morphisms `ξ'_n ⟶ ξ_n` over
the maps of thickenings commuting with the transition morphisms.

## Main definitions

* `Deformation.Artin.truncationOverMap`: the map of infinitesimal thickenings induced by a local
  homomorphism of complete local bases.
* `Deformation.Artin.FormalObject.baseChange`: the base change of a formal object.
* `Deformation.Artin.FormalObject.baseChangeπ`: its morphisms to the levels of the original
  formal object.

## Main results

* `Deformation.Artin.FormalObject.transition_baseChangeπ`: the morphisms to the original levels
  commute with the transition morphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The maps of infinitesimal thickenings -/

section Truncation

variable (A A' : FormalBase S) (φ : A.R →+* A'.R) [IsLocalHom φ]
  (hφ : Spec.map (CommRingCat.ofHom φ) ≫ A.toS = A'.toS)
  (c : ∀ n, B.Contains (A.truncation n)) (c' : ∀ n, B.Contains (A'.truncation n))

/-- The map of `n`-th infinitesimal thickenings induced by a local homomorphism `φ` of complete
local bases over `S`, as a morphism of the big fppf site of `S`. -/
def truncationOverMap (n : ℕ) :
    truncationOver B S hS A' c' n ⟶ truncationOver B S hS A c n :=
  Over.homMk (ObjectProperty.homMk (X := ⟨A'.truncation n, c' n⟩) (Y := ⟨A.truncation n, c n⟩)
    (Spec.map (CommRingCat.ofHom (localQuotientMap φ n)))) (by
    apply ObjectProperty.hom_ext
    change Spec.map (CommRingCat.ofHom (localQuotientMap φ n)) ≫
        (adicThickeningι A.R (maximalIdeal A.R) n ≫ A.toS) =
      adicThickeningι A'.R (maximalIdeal A'.R) n ≫ A'.toS
    rw [← hφ, ← Category.assoc, adicThickeningι, adicThickeningι, ← Spec.map_comp,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      localQuotientMap_comp_mk])

/-- The map of thickenings, read on schemes, is the spectrum of `localQuotientMap`. -/
theorem toScheme_map_truncationOverMap (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map (truncationOverMap A A' φ hφ c c' n) =
      Spec.map (CommRingCat.ofHom (localQuotientMap φ n)) :=
  rfl

/-- The maps of thickenings commute with the inclusions of consecutive thickenings. -/
theorem truncationOverSucc_truncationOverMap (n : ℕ) :
    truncationOverSucc B S hS A' c' n ≫ truncationOverMap A A' φ hφ c c' (n + 1) =
      truncationOverMap A A' φ hφ c c' n ≫ truncationOverSucc B S hS A c n := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  simp only [Functor.map_comp, toScheme_map_truncationOverMap]
  change A'.truncationSucc n ≫ _ = _ ≫ A.truncationSucc n
  simp only [FormalBase.truncationSucc, adicThickeningSucc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [localQuotientMap, Ideal.quotientMap_mk]

end Truncation

/-! ### The base change of a formal object -/

section BaseChange

variable {F : Type v} [Category.{w} F] {p : F ⥤ BigFppfOver B S hS}
  (hp : p.IsFiberedInGroupoids) (ξ : FormalObject B S hS p)
  (A' : FormalBase S) (φ : ξ.base.R →+* A'.R) [IsLocalHom φ]
  (hφ : Spec.map (CommRingCat.ofHom φ) ≫ ξ.base.toS = A'.toS)
  (c' : ∀ n, B.Contains (A'.truncation n))

/-- The levels of the base change: the pullbacks of the levels of `ξ` along the maps of
thickenings. -/
def FormalObject.baseChangeLevel (n : ℕ) : F :=
  letI : p.IsFibered := hp.isFibered
  Functor.IsPreFibered.pullbackObj (ξ.level_eq n)
    (truncationOverMap ξ.base A' φ hφ ξ.contains c' n)

/-- The `n`-th level of the base change lies over the `n`-th thickening of `R'`. -/
theorem FormalObject.baseChangeLevel_eq (n : ℕ) :
    p.obj (ξ.baseChangeLevel hp A' φ hφ c' n) = truncationOver B S hS A' c' n := by
  let : p.IsFibered := hp.isFibered
  exact Functor.IsPreFibered.pullbackObj_proj _ _

/-- The morphism from a level of the base change to the corresponding level of `ξ`. -/
def FormalObject.baseChangeπ (n : ℕ) : ξ.baseChangeLevel hp A' φ hφ c' n ⟶ ξ.level n :=
  letI : p.IsFibered := hp.isFibered
  Functor.IsPreFibered.pullbackMap (ξ.level_eq n)
    (truncationOverMap ξ.base A' φ hφ ξ.contains c' n)

/-- The morphism `baseChangeπ` lies over the map of `n`-th thickenings. -/
instance FormalObject.isHomLift_baseChangeπ (n : ℕ) :
    p.IsHomLift (truncationOverMap ξ.base A' φ hφ ξ.contains c' n)
      (ξ.baseChangeπ hp A' φ hφ c' n) := by
  let : p.IsFibered := hp.isFibered
  exact (Functor.IsPreFibered.pullbackMap.IsCartesian (ξ.level_eq n)
    (truncationOverMap ξ.base A' φ hφ ξ.contains c' n)).toIsHomLift

/-- The composite of `baseChangeπ` at level `n` with the transition morphism of `ξ` lies over the
composite of the inclusion of thickenings of `R'` with the map of `(n + 1)`-st thickenings. -/
theorem FormalObject.isHomLift_baseChangeπ_transition (n : ℕ) : p.IsHomLift
    (truncationOverSucc B S hS A' c' n ≫ truncationOverMap ξ.base A' φ hφ ξ.contains c' (n + 1))
    (ξ.baseChangeπ hp A' φ hφ c' n ≫ ξ.transition n) := by
  rw [truncationOverSucc_truncationOverMap]
  have := ξ.transition_lift n
  have := FormalObject.isHomLift_baseChangeπ hp ξ A' φ hφ c' n
  infer_instance

/-- The transition morphisms of the base change, lifted through the cartesian morphisms to the
levels of `ξ`. -/
def FormalObject.baseChangeTransition (n : ℕ) :
    ξ.baseChangeLevel hp A' φ hφ c' n ⟶ ξ.baseChangeLevel hp A' φ hφ c' (n + 1) :=
  haveI := ξ.isHomLift_baseChangeπ_transition hp A' φ hφ c' n
  hp.fill (f := truncationOverMap ξ.base A' φ hφ ξ.contains c' (n + 1))
    (g := truncationOverSucc B S hS A' c' n) rfl (ξ.baseChangeπ hp A' φ hφ c' (n + 1))
    (ξ.baseChangeπ hp A' φ hφ c' n ≫ ξ.transition n)

/-- The transition morphisms of the base change lie over the inclusions of consecutive
thickenings of `R'`. -/
theorem FormalObject.baseChangeTransition_isHomLift (n : ℕ) :
    p.IsHomLift (truncationOverSucc B S hS A' c' n) (ξ.baseChangeTransition hp A' φ hφ c' n) :=
  have := ξ.isHomLift_baseChangeπ_transition hp A' φ hφ c' n
  hp.fill_isHomLift _ _ _

/-- The transition morphisms of the base change commute with the morphisms `baseChangeπ` to the
levels of `ξ`. -/
@[reassoc]
theorem FormalObject.baseChangeTransition_fac (n : ℕ) :
    ξ.baseChangeTransition hp A' φ hφ c' n ≫ ξ.baseChangeπ hp A' φ hφ c' (n + 1) =
      ξ.baseChangeπ hp A' φ hφ c' n ≫ ξ.transition n :=
  have := ξ.isHomLift_baseChangeπ_transition hp A' φ hφ c' n
  hp.fill_fac _ _ _

/-- **The base change of a formal object along a local homomorphism of complete local bases**:
the levels are the pullbacks of the levels of `ξ` along the maps of infinitesimal
thickenings, with the transition morphisms they inherit. -/
def FormalObject.baseChange : FormalObject B S hS p where
  base := A'
  contains := c'
  level := ξ.baseChangeLevel hp A' φ hφ c'
  level_eq := ξ.baseChangeLevel_eq hp A' φ hφ c'
  transition := ξ.baseChangeTransition hp A' φ hφ c'
  transition_lift := ξ.baseChangeTransition_isHomLift hp A' φ hφ c'

/-- The levels of the base change are the `baseChangeLevel`s. -/
@[simp]
theorem FormalObject.baseChange_level (n : ℕ) :
    (ξ.baseChange hp A' φ hφ c').level n = ξ.baseChangeLevel hp A' φ hφ c' n := rfl

/-- The morphisms to the levels of `ξ` commute with the transition morphisms. -/
@[reassoc]
theorem FormalObject.transition_baseChangeπ (n : ℕ) :
    (ξ.baseChange hp A' φ hφ c').transition n ≫ ξ.baseChangeπ hp A' φ hφ c' (n + 1) =
      ξ.baseChangeπ hp A' φ hφ c' n ≫ ξ.transition n :=
  ξ.baseChangeTransition_fac hp A' φ hφ c' n

end BaseChange

/-! ### Finite local extensions of complete local bases -/

section Finite

variable (A : FormalBase S) (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra A.R R']
  [IsLocalHom (algebraMap A.R R')] [Module.Finite A.R R']

/-- The map induced on the quotients by the powers of the maximal ideals by a finite local
homomorphism is finite. -/
theorem finite_localQuotientMap (n : ℕ) :
    (localQuotientMap (algebraMap A.R R') n).Finite := by
  refine RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1))) ?_
  rw [localQuotientMap_comp_mk]
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
    (RingHom.finite_algebraMap.2 inferInstance)

/-- **A finite local extension of a complete local base.** A local ring `R'` which is a finite
algebra over the ring `R` of a complete local base, with the induced local homomorphism, is again
a complete local base: it is Noetherian and complete (**Stacks 0325**), and its residue field is
finite over that of `R`, hence of finite type over `S`. -/
def FormalBase.ofFinite : FormalBase S where
  R := R'
  noetherian := (IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing (S := R')
    ⟨A.noetherian, inferInstance, A.complete⟩).isNoetherian
  complete := (IsNoetherianCompleteLocalRing.of_finite_of_isLocalRing (S := R')
    ⟨A.noetherian, inferInstance, A.complete⟩).isComplete
  toS := Spec.map (CommRingCat.ofHom (algebraMap A.R R')) ≫ A.toS
  residueLocallyFiniteType := by
    have hfin : IsFinite (Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap A.R R') 0))) :=
      (IsFinite.SpecMap_iff _).2 (finite_localQuotientMap A R' 0)
    have h : adicThickeningι R' (maximalIdeal R') 0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap A.R R')) ≫ A.toS =
        Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap A.R R') 0)) ≫
          (adicThickeningι A.R (maximalIdeal A.R) 0 ≫ A.toS) := by
      simp only [adicThickeningι, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        localQuotientMap_comp_mk]
    rw [h]
    have := A.residueLocallyFiniteType
    infer_instance
  residueQuasiCompact := by
    have hfin : IsFinite (Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap A.R R') 0))) :=
      (IsFinite.SpecMap_iff _).2 (finite_localQuotientMap A R' 0)
    have h : adicThickeningι R' (maximalIdeal R') 0 ≫
        Spec.map (CommRingCat.ofHom (algebraMap A.R R')) ≫ A.toS =
        Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap A.R R') 0)) ≫
          (adicThickeningι A.R (maximalIdeal A.R) 0 ≫ A.toS) := by
      simp only [adicThickeningι, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        localQuotientMap_comp_mk]
    rw [h]
    have := A.residueQuasiCompact
    infer_instance

/-- The ring of `FormalBase.ofFinite A R'` is `R'`. -/
@[simp]
theorem FormalBase.ofFinite_R : (A.ofFinite R').R = R' := rfl

/-- The structure morphism of `FormalBase.ofFinite A R'` is the composite of `Spec R' ⟶ Spec R`
with the structure morphism of `A`. -/
theorem FormalBase.ofFinite_toS :
    (A.ofFinite R').toS = Spec.map (CommRingCat.ofHom (algebraMap A.R R')) ≫ A.toS := rfl

omit [IsLocalRing R'] [IsLocalHom (algebraMap A.R R')] in
/-- The spectrum of a finite local extension of a complete local base in the site lies in the
site. -/
theorem FormalBase.contains_spec_ofFinite (hA : B.Contains (Spec (.of A.R))) :
    B.Contains (Spec (.of R')) :=
  Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit A.R R' hA

end Finite

end Deformation.Artin

end
