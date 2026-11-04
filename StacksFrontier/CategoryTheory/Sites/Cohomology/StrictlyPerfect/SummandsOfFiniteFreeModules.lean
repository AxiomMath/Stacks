module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Projective
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Modules on a ringed site which are summands of finite free modules

Let `(C, O)` be a ringed site and `R = Γ(C, O)` the ring of global sections of its structure
sheaf. A sheaf of `O`-modules is a *summand of a finite free module* when it is a retract of a
finite product `O ⊕ ⋯ ⊕ O` of copies of the structure sheaf. This file shows that global
sections identify the category of such modules with the category of finite projective
`R`-modules.

The argument is the one in the source, carried out by hand rather than through the morphism of
topoi to a point. A finite free module `O^n` represents `n`-tuples of global sections: a map
out of it is determined by its `n` coordinates, which are maps out of `O`, and these in turn
are global sections. So on finite free modules the global sections functor is fully faithful
and sends `O^n` to the free module `R^n`; both properties pass to retracts, which gives
fullness and faithfulness on summands of finite free modules and finiteness and projectivity
of their global sections. Essential surjectivity goes the other way: a finite projective
`R`-module is a retract of some `R^n`, hence is cut out by an idempotent of `R^n`; that
idempotent comes from a unique idempotent of `O^n`, and its equalizer with the identity is a
summand of a finite free module with the prescribed global sections.

## Main definitions

* `AlgebraicGeometry.RingedSite.globalSectionRing`: the ring `Γ(C, O)` of global sections of
  the structure sheaf.
* `AlgebraicGeometry.RingedSite.globalSectionsFunctor`: global sections of sheaves of modules
  on a ringed site, as modules over `Γ(C, O)`.
* `AlgebraicGeometry.RingedSite.finiteFree`: the finite free module `O^n`.
* `AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree`: being a retract of some `O^n`.

## Main results

* `AlgebraicGeometry.RingedSite.finiteFreeHomEquiv`: maps out of `O^n` are `n`-tuples of
  global sections.
* `AlgebraicGeometry.RingedSite.finiteFreeSectionsEquiv`: the global sections of `O^n` are the
  free module `R^n`.
* `AlgebraicGeometry.RingedSite.finiteProjective_of_isDirectSummandOfFiniteFree`: global
  sections of a summand of a finite free module are a finite projective `R`-module.
* `AlgebraicGeometry.RingedSite.finiteFreeSummandEquivalenceFiniteProjective`: the resulting
  equivalence of categories, and
  `finiteFreeSummandEquivalenceFiniteProjective_iso_globalSections`, which records that it is
  given by global sections.

## Implementation notes

The structure sheaf of a ringed site is `CommRingCat`-valued while sheaves of modules are
indexed by a sheaf of rings, so everything below is stated for
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`, the structure sheaf with commutativity
forgotten.

Finiteness and projectivity are recorded as an `ObjectProperty` on `ModuleCat R` so that the
target of the equivalence is a full subcategory in the sense of
`CategoryTheory.ObjectProperty.FullSubcategory`, matching the source's "category of finite
projective `R`-modules".

## References

* [Stacks Project, Tag 0FPX](https://stacks.math.columbia.edu/tag/0FPX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible] Stacks.Cohomology.SiteModules.globalSectionsFunctor

variable (X : RingedSite.{u, v, w})

/-- The ring `R = Γ(C, O)` of global sections of the structure sheaf of a ringed site. -/
abbrev globalSectionRing :=
  Stacks.Cohomology.SiteModules.GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- Global sections of sheaves of modules on a ringed site, as modules over the ring of global
sections of the structure sheaf. -/
abbrev globalSectionsFunctor : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
    ModuleCat.{max u w} X.globalSectionRing :=
  Stacks.Cohomology.SiteModules.globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- Global sections of a sheaf of modules are the maps out of the structure sheaf. -/
def globalSectionsIsoCoyoneda :
    (X.globalSectionsFunctor ⋙ forget _) ≅
      coyoneda.obj (Opposite.op (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  refine NatIso.ofComponents (fun M => Equiv.toIso M.unitHomEquiv.symm) ?_
  intro M N f
  ext s
  exact (SheafOfModules.unitHomEquiv_symm_comp s f).symm

/-- The global sections of the structure sheaf are the ring of global sections itself. -/
lemma globalSectionsFunctor_obj_unit :
    X.globalSectionsFunctor.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =
      ModuleCat.of X.globalSectionRing X.globalSectionRing := rfl

/-- The unit global section of the structure sheaf. -/
def globalUnitOne : X.globalSectionsFunctor.obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  X.globalSectionsIsoCoyoneda.inv.app
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (𝟙 _)

/-- Under `globalSectionsIsoCoyoneda`, the image of a global section `s` of `M` under a map
`f : M ⟶ N` corresponds to the composite of the map `O ⟶ M` given by `s` with `f`. -/
lemma globalSectionsIsoCoyoneda_map_apply
    (M N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (f : M ⟶ N) (s : X.globalSectionsFunctor.obj M) :
    X.globalSectionsIsoCoyoneda.hom.app N (X.globalSectionsFunctor.map f s) =
      X.globalSectionsIsoCoyoneda.hom.app M s ≫ f := by
  show N.unitHomEquiv.symm (SheafOfModules.sectionsMap f s) = _
  exact (SheafOfModules.unitHomEquiv_symm_comp s f).symm

/-- Under `globalSectionsIsoCoyoneda`, the unit global section of `O` corresponds to the identity
of `O`. -/
lemma globalSectionsIsoCoyoneda_globalUnitOne :
    X.globalSectionsIsoCoyoneda.hom.app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) X.globalUnitOne =
      𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := by
  simp [globalUnitOne, globalSectionsIsoCoyoneda]

/-- Under `globalSectionsIsoCoyoneda`, the image of the unit global section under a map
`f : O ⟶ M` corresponds to `f` itself. -/
lemma globalSectionsIsoCoyoneda_map_globalUnitOne
    (M : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (f : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ M) :
    X.globalSectionsIsoCoyoneda.hom.app M
      (X.globalSectionsFunctor.map f X.globalUnitOne) = f := by
  rw [globalSectionsIsoCoyoneda_map_apply, globalSectionsIsoCoyoneda_globalUnitOne]
  simp

/-- The finite free module `O^n` on a ringed site. -/
abbrev finiteFree (n : ℕ) : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- A sheaf of modules is a summand of a finite free module if it is a retract of a finite
power of the structure sheaf. -/
def IsDirectSummandOfFiniteFree
    (E : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  ∃ n : ℕ, Nonempty (Retract E (X.finiteFree n))

/-- The `i`-th coordinate inclusion `O ⟶ O^n`. -/
def finiteFreeι (n : ℕ) (i : Fin n) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ X.finiteFree n :=
  Pi.lift (fun j => if i = j then 𝟙 _ else 0)

/-- The sum over `i` of the `i`-th projection followed by the `i`-th inclusion is the identity
of `O^n`. -/
lemma sum_π_comp_finiteFreeι (n : ℕ) :
    (∑ i : Fin n, Pi.π (fun _ : Fin n =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
      X.finiteFreeι n i) = 𝟙 (X.finiteFree n) := by
  show (∑ i : Fin n, Pi.π (fun _ : Fin n =>
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
    Pi.lift (fun j => if i = j then 𝟙 _ else 0)) =
      𝟙 (∏ᶜ fun _ : Fin n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  apply Pi.hom_ext
  intro j
  classical
  simp only [Preadditive.sum_comp, Category.assoc, Pi.lift_π]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

/-- A map out of `O^n` is the same thing as its `n` coordinates, each a global section. -/
def finiteFreeHomEquiv (n : ℕ)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (X.finiteFree n ⟶ M) ≃ (Fin n → M.sections) where
  toFun f i := M.unitHomEquiv (X.finiteFreeι n i ≫ f)
  invFun s := ∑ i : Fin n, Pi.π (fun _ : Fin n =>
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
      M.unitHomEquiv.symm (s i)
  left_inv f := by
    change (∑ i : Fin n, Pi.π (fun _ : Fin n =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
      M.unitHomEquiv.symm (M.unitHomEquiv (X.finiteFreeι n i ≫ f))) = f
    simp only [M.unitHomEquiv.symm_apply_apply]
    rw [show (∑ i : Fin n, Pi.π (fun _ : Fin n =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
      X.finiteFreeι n i ≫ f) =
        (∑ i : Fin n, Pi.π (fun _ : Fin n =>
          SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i ≫
      X.finiteFreeι n i) ≫ f by rw [Preadditive.sum_comp]; simp [Category.assoc]]
    rw [sum_π_comp_finiteFreeι]
    simp
  right_inv s := by
    funext i
    change M.unitHomEquiv (X.finiteFreeι n i ≫
      (∑ j : Fin n, Pi.π (fun _ : Fin n =>
          SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j ≫
        M.unitHomEquiv.symm (s j))) = s i
    rw [Preadditive.comp_sum]
    have hproj (j : Fin n) : X.finiteFreeι n i ≫
        Pi.π (fun _ : Fin n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j =
          if i = j then 𝟙 _ else 0 := by
      simp [finiteFreeι]
    have hs : (∑ j : Fin n, X.finiteFreeι n i ≫
        Pi.π (fun _ : Fin n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j ≫
        M.unitHomEquiv.symm (s j)) =
        ∑ j : Fin n, (if i = j then M.unitHomEquiv.symm (s i) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Category.assoc, hproj j]
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    rw [hs, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Ne.symm hji]
    · simp

/-- Taking the `n` coordinates of a global section of `O^n`. -/
def finiteFreeSectionsCoords (n : ℕ) :
    X.globalSectionsFunctor.obj (X.finiteFree n) →ₗ[X.globalSectionRing]
      (Fin n → X.globalSectionsFunctor.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  LinearMap.pi fun i =>
    (X.globalSectionsFunctor.map
      (Pi.π (fun _ : Fin n =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i)).hom

/-- The `i`-th coordinate of a global section of `O^n` is the global section of `O` given by the
composite of the corresponding map `O ⟶ O^n` with the `i`-th projection. -/
lemma finiteFreeSectionsCoords_apply (n : ℕ)
    (x : X.globalSectionsFunctor.obj (X.finiteFree n)) (i : Fin n) :
    X.finiteFreeSectionsCoords n x i =
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv
        ((X.finiteFree n).unitHomEquiv.symm x ≫
          Pi.π (fun _ : Fin n =>
            SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) := by
  change (X.finiteFree n).sections at x
  show SheafOfModules.sectionsMap
      (Pi.π (fun _ : Fin n =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) x = _
  rw [SheafOfModules.unitHomEquiv_comp_apply]
  simp

/-- The coordinates of a global section of `O^n` determine it. -/
def finiteFreeSectionsCoordsEquiv (n : ℕ) :
    X.globalSectionsFunctor.obj (X.finiteFree n) ≃ₗ[X.globalSectionRing]
      (Fin n → X.globalSectionsFunctor.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  refine LinearEquiv.ofBijective (X.finiteFreeSectionsCoords n) ⟨?_, ?_⟩
  · intro x y hxy
    change (X.finiteFree n).sections at x
    change (X.finiteFree n).sections at y
    have hm : (X.finiteFree n).unitHomEquiv.symm x =
        (X.finiteFree n).unitHomEquiv.symm y := by
      apply Pi.hom_ext
      intro i
      apply (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv.injective
      calc
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv
            ((X.finiteFree n).unitHomEquiv.symm x ≫
              Pi.π (fun _ : Fin n =>
                SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) =
          X.finiteFreeSectionsCoords n x i :=
            (X.finiteFreeSectionsCoords_apply n x i).symm
        _ = X.finiteFreeSectionsCoords n y i := congrFun hxy i
        _ = (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv
            ((X.finiteFree n).unitHomEquiv.symm y ≫
              Pi.π (fun _ : Fin n =>
                SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) :=
          X.finiteFreeSectionsCoords_apply n y i
    exact (X.finiteFree n).unitHomEquiv.symm.injective hm
  · intro f
    refine ⟨(X.finiteFree n).unitHomEquiv
      (Pi.lift fun i => (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv.symm (f i)), ?_⟩
    funext i
    change SheafOfModules.sectionsMap
      (Pi.π (fun _ : Fin n => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i)
      ((X.finiteFree n).unitHomEquiv
        (Pi.lift fun j =>
          (SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv.symm (f j))) = f i
    calc
      _ = (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv
          ((Pi.lift fun j =>
              (SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv.symm (f j)) ≫
            Pi.π (fun _ : Fin n =>
              SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i) := by
            rw [← SheafOfModules.unitHomEquiv_comp_apply]
      _ = f i := by simp

/-- Global sections of the structure sheaf are the ring of global sections. -/
def unitSectionsLinearEquiv :
    X.globalSectionsFunctor.obj (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≃ₗ[X.globalSectionRing]
      X.globalSectionRing :=
  (eqToIso X.globalSectionsFunctor_obj_unit).toLinearEquiv

/-- Coordinatewise form of `unitSectionsLinearEquiv`. -/
def piUnitSectionsLinearEquiv (n : ℕ) :
    (Fin n → X.globalSectionsFunctor.obj (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≃ₗ[X.globalSectionRing]
      (Fin n → X.globalSectionRing) where
  toFun f i := X.unitSectionsLinearEquiv (f i)
  invFun f i := X.unitSectionsLinearEquiv.symm (f i)
  left_inv f := by funext i; exact X.unitSectionsLinearEquiv.left_inv (f i)
  right_inv f := by funext i; exact X.unitSectionsLinearEquiv.right_inv (f i)
  map_add' f g := by funext i; exact X.unitSectionsLinearEquiv.map_add (f i) (g i)
  map_smul' r f := by funext i; exact X.unitSectionsLinearEquiv.map_smul r (f i)

/-- The global sections of the finite free module `O^n` are the free module `R^n`. -/
def finiteFreeSectionsEquiv (n : ℕ) :
    X.globalSectionsFunctor.obj (X.finiteFree n) ≃ₗ[X.globalSectionRing]
      (Fin n → X.globalSectionRing) :=
  X.finiteFreeSectionsCoordsEquiv n ≪≫ₗ X.piUnitSectionsLinearEquiv n

/-- An endomorphism of the structure sheaf is multiplication by a global scalar. -/
def unitEndScalar
    (f : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    X.globalSectionRing :=
  (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv f

/-- Viewed as an element of the ring of global sections, the global section of `O` given by an
endomorphism `f` of `O` is the scalar `unitEndScalar f`. -/
lemma unitSectionsLinearEquiv_unitHomEquiv
    (f : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    X.unitSectionsLinearEquiv ((SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv f) =
      X.unitEndScalar f := rfl

/-- The identity of the structure sheaf is multiplication by `1`. -/
@[simp]
lemma unitEndScalar_id :
    X.unitEndScalar
      (𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) = 1 := by
  apply Subtype.ext
  funext Y
  rfl

/-- The zero endomorphism of the structure sheaf is multiplication by `0`. -/
@[simp]
lemma unitEndScalar_zero :
    X.unitEndScalar (0 : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = 0 := by
  apply Subtype.ext
  funext Y
  rfl

/-- The `i`-th coordinate inclusion sends the unit global section to the `i`-th basis vector
of `R^n`. -/
lemma finiteFreeSectionsEquiv_finiteFreeι (n : ℕ) (i : Fin n) :
    X.finiteFreeSectionsEquiv n
      (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne) =
      Pi.single i (1 : X.globalSectionRing) := by
  classical
  funext j
  show X.unitSectionsLinearEquiv
      (X.finiteFreeSectionsCoords n
        (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne) j) = _
  rw [finiteFreeSectionsCoords_apply]
  have hsec : X.globalSectionsIsoCoyoneda.hom.app (X.finiteFree n)
      (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne) =
      X.finiteFreeι n i :=
    X.globalSectionsIsoCoyoneda_map_globalUnitOne (X.finiteFree n) (X.finiteFreeι n i)
  show X.unitSectionsLinearEquiv
      ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).unitHomEquiv
        (X.globalSectionsIsoCoyoneda.hom.app (X.finiteFree n)
          (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne) ≫
          Pi.π (fun _ : Fin n =>
            SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j)) = _
  rw [hsec, unitSectionsLinearEquiv_unitHomEquiv]
  have hcomp : X.unitEndScalar
      (X.finiteFreeι n i ≫ Pi.π (fun _ : Fin n =>
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j) =
        if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp [finiteFreeι]
    · have hz : X.finiteFreeι n i ≫
          Pi.π (fun _ : Fin n =>
            SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j = 0 := by
        simp [finiteFreeι, hij]
      rw [hz, unitEndScalar_zero]
      simp [hij]
  rw [hcomp]
  simp [Pi.single_apply, eq_comm]

/-- The global sections of the finite free module `O^n` are a finite projective module over the
ring of global sections. -/
lemma finiteProjective_finiteFree (n : ℕ) :
    Module.Finite X.globalSectionRing (X.globalSectionsFunctor.obj (X.finiteFree n)) ∧
      Module.Projective X.globalSectionRing
        (X.globalSectionsFunctor.obj (X.finiteFree n)) := by
  let e := X.finiteFreeSectionsEquiv n
  refine ⟨?_, ?_⟩
  · have : Module.Finite X.globalSectionRing (Fin n → X.globalSectionRing) := inferInstance
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  · exact Module.Projective.of_basis ((Pi.basisFun X.globalSectionRing (Fin n)).map e.symm)

/-- Under `globalSectionsIsoCoyoneda`, the image of the `i`-th basis section of `O^n` under a map
`k : O^n ⟶ M` corresponds to `finiteFreeι n i ≫ k`. -/
private lemma globalSectionsIsoCoyoneda_map_finiteFreeι_globalUnitOne (n : ℕ)
    (M : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (k : X.finiteFree n ⟶ M)
    (i : Fin n) :
    X.globalSectionsIsoCoyoneda.hom.app M
      (X.globalSectionsFunctor.map k
        (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne)) =
      X.finiteFreeι n i ≫ k := by
  rw [globalSectionsIsoCoyoneda_map_apply, globalSectionsIsoCoyoneda_map_globalUnitOne]

/-- The map of finite free modules with prescribed global sections. -/
def finiteFreeHomOfSectionsHom (n m : ℕ)
    (f : X.globalSectionsFunctor.obj (X.finiteFree n) ⟶
      X.globalSectionsFunctor.obj (X.finiteFree m)) :
    X.finiteFree n ⟶ X.finiteFree m :=
  (X.finiteFreeHomEquiv n (X.finiteFree m)).symm fun i =>
    f (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne)

/-- The map `finiteFreeHomOfSectionsHom n m f` of finite free modules induces `f` on global
sections. -/
@[simp]
lemma globalSectionsFunctor_map_finiteFreeHomOfSectionsHom (n m : ℕ)
    (f : X.globalSectionsFunctor.obj (X.finiteFree n) ⟶
      X.globalSectionsFunctor.obj (X.finiteFree m)) :
    X.globalSectionsFunctor.map (X.finiteFreeHomOfSectionsHom n m f) = f := by
  let en := X.finiteFreeSectionsEquiv n
  let em := X.finiteFreeSectionsEquiv m
  let g₁ : (Fin n → X.globalSectionRing) →ₗ[X.globalSectionRing]
      (Fin m → X.globalSectionRing) :=
    em.toLinearMap.comp
      ((X.globalSectionsFunctor.map (X.finiteFreeHomOfSectionsHom n m f)).hom.comp
        en.symm.toLinearMap)
  let g₂ : (Fin n → X.globalSectionRing) →ₗ[X.globalSectionRing]
      (Fin m → X.globalSectionRing) :=
    em.toLinearMap.comp (f.hom.comp en.symm.toLinearMap)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (X.finiteFree n).sections at x
  have hg : g₁ = g₂ := by
    apply (Pi.basisFun X.globalSectionRing (Fin n)).ext
    intro i
    have hb : en.symm (Pi.single i (1 : X.globalSectionRing)) =
        X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne := by
      apply en.injective
      rw [finiteFreeSectionsEquiv_finiteFreeι]
      simp
    have hbase : X.globalSectionsFunctor.map (X.finiteFreeHomOfSectionsHom n m f)
        (en.symm (Pi.single i (1 : X.globalSectionRing))) =
        f (en.symm (Pi.single i (1 : X.globalSectionRing))) := by
      rw [hb]
      apply (Iso.toEquiv (X.globalSectionsIsoCoyoneda.app (X.finiteFree m))).injective
      have hcoord := congrFun
        ((X.finiteFreeHomEquiv n (X.finiteFree m)).right_inv
          (fun j => f (X.globalSectionsFunctor.map (X.finiteFreeι n j) X.globalUnitOne))) i
      calc
        X.globalSectionsIsoCoyoneda.hom.app (X.finiteFree m)
            (X.globalSectionsFunctor.map (X.finiteFreeHomOfSectionsHom n m f)
              (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne)) =
            X.finiteFreeι n i ≫ X.finiteFreeHomOfSectionsHom n m f :=
          X.globalSectionsIsoCoyoneda_map_finiteFreeι_globalUnitOne n (X.finiteFree m) _ i
        _ = (X.finiteFree m).unitHomEquiv.symm
            (f (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne)) := by
          change (X.finiteFree m).unitHomEquiv
              (X.finiteFreeι n i ≫ X.finiteFreeHomOfSectionsHom n m f) =
            f (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne) at hcoord
          rw [← hcoord]
          simp
        _ = X.globalSectionsIsoCoyoneda.hom.app (X.finiteFree m)
            (f (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne)) := rfl
    rw [Pi.basisFun_apply]
    show g₁ (Pi.single i (1 : X.globalSectionRing)) =
      g₂ (Pi.single i (1 : X.globalSectionRing))
    calc
      g₁ (Pi.single i (1 : X.globalSectionRing)) =
          em (X.globalSectionsFunctor.map (X.finiteFreeHomOfSectionsHom n m f)
            (en.symm (Pi.single i (1 : X.globalSectionRing)))) := rfl
      _ = em (f (en.symm (Pi.single i (1 : X.globalSectionRing)))) := congrArg em hbase
      _ = g₂ (Pi.single i (1 : X.globalSectionRing)) := rfl
  apply em.injective
  have h := congrArg (fun q => q (en x)) hg
  change em (X.globalSectionsFunctor.map (X.finiteFreeHomOfSectionsHom n m f)
      (en.symm (en x))) = em (f (en.symm (en x))) at h
  rw [en.symm_apply_apply] at h
  exact h

/-- **Stacks 0FPX.** Global sections of a summand of a finite free module are a finite
projective module over the ring of global sections. -/
lemma finiteProjective_of_isDirectSummandOfFiniteFree
    (M : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : X.IsDirectSummandOfFiniteFree M) :
    Module.Finite X.globalSectionRing (X.globalSectionsFunctor.obj M) ∧
      Module.Projective X.globalSectionRing (X.globalSectionsFunctor.obj M) := by
  obtain ⟨n, ⟨r⟩⟩ := hM
  let r' := r.map X.globalSectionsFunctor
  have hf := X.finiteProjective_finiteFree n
  let := hf.1
  let := hf.2
  have hri (x : X.globalSectionsFunctor.obj M) : r'.r.hom (r'.i.hom x) = x := by
    show (r'.i ≫ r'.r) x = x
    rw [r'.retract]
    rfl
  refine ⟨?_, ?_⟩
  · exact Module.Finite.of_surjective r'.r.hom fun x => ⟨r'.i.hom x, hri x⟩
  · exact Module.Projective.of_split r'.i.hom r'.r.hom (LinearMap.ext hri)

/-- Global sections are faithful on finite free modules. -/
lemma finiteFreeHom_injective (n m : ℕ) {f g : X.finiteFree n ⟶ X.finiteFree m}
    (h : X.globalSectionsFunctor.map f = X.globalSectionsFunctor.map g) : f = g := by
  apply (X.finiteFreeHomEquiv n (X.finiteFree m)).injective
  funext i
  have hval := congrArg
    (fun k => k (X.globalSectionsFunctor.map (X.finiteFreeι n i) X.globalUnitOne)) h
  have hsec := congrArg (X.globalSectionsIsoCoyoneda.hom.app (X.finiteFree m)) hval
  exact congrArg (X.finiteFree m).unitHomEquiv
    ((X.globalSectionsIsoCoyoneda_map_finiteFreeι_globalUnitOne n _ f i).symm.trans
      (hsec.trans (X.globalSectionsIsoCoyoneda_map_finiteFreeι_globalUnitOne n _ g i)))

/-- Global sections are faithful on summands of finite free modules. -/
lemma globalSectionsFunctor_map_injective
    (M N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : X.IsDirectSummandOfFiniteFree M) (hN : X.IsDirectSummandOfFiniteFree N)
    {f g : M ⟶ N} (h : X.globalSectionsFunctor.map f = X.globalSectionsFunctor.map g) :
    f = g := by
  obtain ⟨n, ⟨rM⟩⟩ := hM
  obtain ⟨m, ⟨rN⟩⟩ := hN
  have hcomp : X.globalSectionsFunctor.map (rM.r ≫ f ≫ rN.i) =
      X.globalSectionsFunctor.map (rM.r ≫ g ≫ rN.i) := by
    simp only [Functor.map_comp, h]
  calc
    f = rM.i ≫ (rM.r ≫ f ≫ rN.i) ≫ rN.r := by simp [Category.assoc, rN.retract]
    _ = rM.i ≫ (rM.r ≫ g ≫ rN.i) ≫ rN.r := by rw [X.finiteFreeHom_injective n m hcomp]
    _ = g := by simp [Category.assoc, rN.retract]

/-- Global sections are full on summands of finite free modules. -/
lemma globalSectionsFunctor_map_surjective
    (M N : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : X.IsDirectSummandOfFiniteFree M) (hN : X.IsDirectSummandOfFiniteFree N)
    (f : X.globalSectionsFunctor.obj M ⟶ X.globalSectionsFunctor.obj N) :
    ∃ g : M ⟶ N, X.globalSectionsFunctor.map g = f := by
  obtain ⟨n, ⟨rM⟩⟩ := hM
  obtain ⟨m, ⟨rN⟩⟩ := hN
  let hfree : X.globalSectionsFunctor.obj (X.finiteFree n) ⟶
      X.globalSectionsFunctor.obj (X.finiteFree m) :=
    X.globalSectionsFunctor.map rM.r ≫ f ≫ X.globalSectionsFunctor.map rN.i
  let gfree := X.finiteFreeHomOfSectionsHom n m hfree
  refine ⟨rM.i ≫ gfree ≫ rN.r, ?_⟩
  simp only [Functor.map_comp]
  rw [globalSectionsFunctor_map_finiteFreeHomOfSectionsHom]
  have hleft : X.globalSectionsFunctor.map rM.i ≫ X.globalSectionsFunctor.map rM.r =
      𝟙 (X.globalSectionsFunctor.obj M) := (rM.map X.globalSectionsFunctor).retract
  have hright : X.globalSectionsFunctor.map rN.i ≫ X.globalSectionsFunctor.map rN.r =
      𝟙 (X.globalSectionsFunctor.obj N) := (rN.map X.globalSectionsFunctor).retract
  dsimp only [hfree]
  simp only [Category.assoc]
  rw [reassoc_of% hleft, hright, Category.comp_id]

/-- Being a finite projective module over the ring of global sections. -/
abbrev FiniteProjective : ObjectProperty (ModuleCat.{max u w} X.globalSectionRing) :=
  fun M => Module.Finite X.globalSectionRing M ∧ Module.Projective X.globalSectionRing M

/-- The global sections of a summand of a finite free module satisfy `FiniteProjective`. -/
lemma finiteProjective_globalSectionsFunctor_obj
    (M : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : X.IsDirectSummandOfFiniteFree M) :
    X.FiniteProjective (X.globalSectionsFunctor.obj M) :=
  X.finiteProjective_of_isDirectSummandOfFiniteFree M hM

/-- On a ringed site `(C, O)` with `R = Γ(C, O)`, the category of `O`-modules which are summands
of finite free modules is equivalent to the category of finite projective `R`-modules. -/
@[stacks 0FPX "the equivalence"]
def finiteFreeSummandEquivalenceFiniteProjective :
    ObjectProperty.FullSubcategory X.IsDirectSummandOfFiniteFree ≌
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{max u w}
            (Stacks.Cohomology.SiteModules.GlobalSectionRing
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) =>
          Module.Finite
              (Stacks.Cohomology.SiteModules.GlobalSectionRing
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M ∧
            Module.Projective
              (Stacks.Cohomology.SiteModules.GlobalSectionRing
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M) := by
  let P : ObjectProperty (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    X.IsDirectSummandOfFiniteFree
  let Q : ObjectProperty (ModuleCat.{max u w} X.globalSectionRing) := X.FiniteProjective
  let H := ObjectProperty.ι P ⋙ X.globalSectionsFunctor
  let F := Q.lift H
    (fun M => X.finiteProjective_globalSectionsFunctor_obj M.obj M.property)
  haveI : H.Full := ⟨fun {M N} f => by
    obtain ⟨g, hg⟩ := X.globalSectionsFunctor_map_surjective M.obj N.obj M.property N.property f
    exact ⟨P.homMk g, hg⟩⟩
  haveI : H.Faithful := ⟨fun {M N} {_ _} h =>
    P.ι.map_injective (X.globalSectionsFunctor_map_injective M.obj N.obj M.property N.property h)⟩
  haveI : F.EssSurj := by
    refine ⟨?_⟩
    intro T
    let M := T.obj
    have hfinite : Module.Finite X.globalSectionRing M := T.property.1
    have hprojective : Module.Projective X.globalSectionRing M := T.property.2
    let := hfinite
    let := hprojective
    obtain ⟨n, f, g, -, -, hfg⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective X.globalSectionRing M
    let Aₙ := X.finiteFree n
    let e := X.finiteFreeSectionsEquiv n
    let iMap := e.symm.toLinearMap.comp g
    let rMap := f.comp e.toLinearMap
    have hsplit : rMap.comp iMap = LinearMap.id := by
      ext x
      simpa [iMap, rMap, LinearMap.comp_apply] using
        congrArg (fun k : M →ₗ[X.globalSectionRing] M => k x) hfg
    let iM : M ⟶ X.globalSectionsFunctor.obj Aₙ :=
      ModuleCat.ofHom (X := M) (Y := X.globalSectionsFunctor.obj Aₙ) iMap
    let rM : X.globalSectionsFunctor.obj Aₙ ⟶ M :=
      ModuleCat.ofHom (X := X.globalSectionsFunctor.obj Aₙ) (Y := M) rMap
    have hsplitCat : iM ≫ rM = 𝟙 M := by
      ext x
      change rMap (iMap x) = x
      exact congrArg (fun k : M →ₗ[X.globalSectionRing] M => k x) hsplit
    let pM : X.globalSectionsFunctor.obj Aₙ ⟶ X.globalSectionsFunctor.obj Aₙ := rM ≫ iM
    have hpM : pM ≫ pM = pM := by
      change (rM ≫ iM) ≫ (rM ≫ iM) = rM ≫ iM
      calc
        (rM ≫ iM) ≫ (rM ≫ iM) = rM ≫ (iM ≫ rM) ≫ iM := by cat_disch
        _ = rM ≫ 𝟙 M ≫ iM := by rw [hsplitCat]
        _ = rM ≫ iM := by simp
    let pS := X.finiteFreeHomOfSectionsHom n n pM
    have hpSmap : X.globalSectionsFunctor.map pS = pM :=
      X.globalSectionsFunctor_map_finiteFreeHomOfSectionsHom n n pM
    have hpS : pS ≫ pS = pS := by
      apply X.finiteFreeHom_injective n n
      calc
        X.globalSectionsFunctor.map (pS ≫ pS) =
            X.globalSectionsFunctor.map pS ≫ X.globalSectionsFunctor.map pS := by
          rw [Functor.map_comp]
        _ = pM ≫ pM := by rw [hpSmap]
        _ = pM := hpM
        _ = X.globalSectionsFunctor.map pS := hpSmap.symm
    let : HasEqualizer (𝟙 Aₙ) pS := inferInstance
    let Y := equalizer (𝟙 Aₙ) pS
    let iY : Y ⟶ Aₙ := equalizer.ι (𝟙 Aₙ) pS
    let rY : Aₙ ⟶ Y := equalizer.lift pS (by simp [hpS])
    have hiY : iY ≫ rY = 𝟙 Y :=
      (splitMonoOfIdempotentEqualizer
        (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) hpS).id
    have hpY : rY ≫ iY = pS := by
      dsimp only [rY, iY]
      exact equalizer.lift_ι _ _
    have hY : X.IsDirectSummandOfFiniteFree Y := ⟨n, ⟨⟨iY, rY, hiY⟩⟩⟩
    have hsplitMap : X.globalSectionsFunctor.map rY ≫ X.globalSectionsFunctor.map iY = pM := by
      rw [← Functor.map_comp, hpY, hpSmap]
    have hsplitMap' : X.globalSectionsFunctor.map iY ≫ X.globalSectionsFunctor.map rY =
        𝟙 (X.globalSectionsFunctor.obj Y) := by
      rw [← Functor.map_comp, hiY, X.globalSectionsFunctor.map_id]
    let eYM : X.globalSectionsFunctor.obj Y ≅ M :=
      { hom := X.globalSectionsFunctor.map iY ≫ rM
        inv := iM ≫ X.globalSectionsFunctor.map rY
        hom_inv_id := by
          calc
            X.globalSectionsFunctor.map iY ≫ rM ≫ iM ≫ X.globalSectionsFunctor.map rY =
                (X.globalSectionsFunctor.map iY ≫ (rM ≫ iM)) ≫
                  X.globalSectionsFunctor.map rY := by cat_disch
            _ = (X.globalSectionsFunctor.map iY ≫ (X.globalSectionsFunctor.map rY ≫
                X.globalSectionsFunctor.map iY)) ≫ X.globalSectionsFunctor.map rY := by
              rw [hsplitMap]
            _ = (X.globalSectionsFunctor.map iY ≫ X.globalSectionsFunctor.map rY) ≫
                (X.globalSectionsFunctor.map iY ≫
                  X.globalSectionsFunctor.map rY) := by cat_disch
            _ = 𝟙 (X.globalSectionsFunctor.obj Y) := by rw [hsplitMap']; simp
        inv_hom_id := by
          calc
            iM ≫ X.globalSectionsFunctor.map rY ≫ X.globalSectionsFunctor.map iY ≫ rM =
                (iM ≫ (X.globalSectionsFunctor.map rY ≫
                  X.globalSectionsFunctor.map iY)) ≫ rM := by cat_disch
            _ = (iM ≫ (rM ≫ iM)) ≫ rM := by rw [hsplitMap]
            _ = (iM ≫ rM) ≫ (iM ≫ rM) := by cat_disch
            _ = 𝟙 M := by rw [hsplitCat]; simp }
    exact ⟨⟨Y, hY⟩, ⟨Q.isoMk eYM⟩⟩
  letI : F.IsEquivalence := { }
  exact F.asEquivalence

/-- The equivalence `finiteFreeSummandEquivalenceFiniteProjective` is given by taking global
sections. -/
@[stacks 0FPX "identification with global sections"]
def finiteFreeSummandEquivalenceFiniteProjective_iso_globalSections :
    X.finiteFreeSummandEquivalenceFiniteProjective.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := by
  let P : ObjectProperty (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    X.IsDirectSummandOfFiniteFree
  let Q : ObjectProperty (ModuleCat.{max u w}
      (Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := fun M =>
    Module.Finite (Stacks.Cohomology.SiteModules.GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M ∧
      Module.Projective (Stacks.Cohomology.SiteModules.GlobalSectionRing
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) M
  let H := ObjectProperty.ι P ⋙
    Stacks.Cohomology.SiteModules.globalSectionsFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hobj : ∀ M : P.FullSubcategory,
      Q ((Stacks.Cohomology.SiteModules.globalSectionsFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj M.obj) :=
    fun M => X.finiteProjective_globalSectionsFunctor_obj M.obj M.property
  exact ObjectProperty.liftCompιIso Q H hobj

end AlgebraicGeometry.RingedSite
