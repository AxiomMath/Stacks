module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCohomologySequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDirectSums
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedFilteredColimits

/-!
# Functorial attachment along a set of acyclic monomorphisms

Let `X` be a ringed site and `A` a sheaf of differential graded algebras on it, and let
`i r : M r ⟶ M' r` be a family of monomorphisms of right differential graded `A`-modules whose
sources and targets all have acyclic underlying complexes. This file constructs, functorially in
the module `N`, a monomorphism `N ⟶ F N` which is a quasi-isomorphism and through which every
morphism `M r ⟶ N` extends to `M' r ⟶ F N`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.SetOfMonosExtension`: the functor, its natural
  inclusion, and the three properties above, packaged as data so that a later transfinite
  construction can iterate the functor.

## Main results

* `SheafOfModules.DifferentialGradedModule.functorSetOfMonos`: the construction exists.

## Implementation notes

The functor attaches, in one step, all the maps out of all the sources at once: `F N` is the
pushout of `∐ M' ← ∐ M → N`, the coproducts being indexed by the pairs `(r, φ : M r ⟶ N)`. The
inclusion `N ⟶ F N` is the pushout inclusion, which is a monomorphism because `∐ M → ∐ M'` is
one and monomorphisms are stable under pushout in an abelian category, and a quasi-isomorphism
because its cokernel is the cokernel of `∐ M → ∐ M'`, which is acyclic: coproducts of acyclic
differential graded modules are acyclic, since the underlying complex of a coproduct is the
degreewise coproduct and filtered colimits in the category of sheaves of modules are exact
(AB5), and the cokernel of a monomorphism of acyclic complexes is acyclic by the long exact
cohomology sequence.

The index type of the family lives in its own universe `t`, so the pairs `(r, φ)` indexing the
coproducts need not lie in the module universe. The module universe is therefore taken to be
`max u w t`, which contains both the site universe and the index universe, and the construction
is carried out in `CategoryTheory.ULiftHom` of the category of differential graded modules, whose
hom universe is large enough for diagrams indexed by those pairs. Colimits, abelianness and AB5
are transported to `ULiftHom` along the canonical equivalence.

## References

* [Stacks Project, Tag 0FSZ](https://stacks.math.columbia.edu/tag/0FSZ)
-/

public section

open CategoryTheory
open CategoryTheory.Limits

namespace SheafOfModules.DifferentialGradedModule

universe u v w t

section

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [HasSheafify X.J AddCommGrpCat.{max u w t}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u w t}]

private theorem liftedModuleColimits :
    HasColimitsOfSize.{max u w t, max u w t}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) := by
  let C := DifferentialGradedModule.{u, v, max u w t} A
  let : Category.{max u (max u w t)} C :=
    inferInstance
  let : HasColimitsOfSize.{max u w t, max u w t} C :=
    DifferentialGradedModule.hasColimitsOfSize.{u, v, max u w t, u, u}
  let e := ULiftHom.equiv (C := C)
  exact Adjunction.has_colimits_of_equivalence.{max u w t, max u w t}
    (C := ULiftHom.{max t u} C) (D := C) e.inverse

/-- The universe-lifted category of differential graded `A`-modules has all colimits of size
`max u w t`. -/
local instance liftedModuleColimitsInstance :
    HasColimitsOfSize.{max u w t, max u w t}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  liftedModuleColimits.{u, v, w, t} (X := X) (A := A)

/-- The universe-lifted category of differential graded `A`-modules has all coproducts indexed
by a type `I` in universe `max u w t`.

Searching for a coproduct through `HasColimitsOfSize` has to unify the universes of the
shape category against the two levels of `liftedModuleColimitsInstance`, and the resulting
search exceeds the instance budget at every use below. Naming the shapes actually used -- the
discrete ones -- makes each of those searches a single step. -/
local instance liftedModuleColimitsOfDiscreteShape (I : Type (max u w t)) :
    HasColimitsOfShape (Discrete I)
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  (liftedModuleColimits.{u, v, w, t} (X := X) (A := A)).has_colimits_of_shape (Discrete I)

@[instance_reducible] private noncomputable def liftedModuleAbelian :
    Abelian (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) := by
  let C := DifferentialGradedModule.{u, v, max u w t} A
  letI : Category.{max u (max u w t)} C := inferInstance
  letI : Abelian C := DifferentialGradedModule.abelian.{u, v, max u w t, u, u}
  let D := ULiftHom.{max t u} C
  letI : Category.{max (max t u) (max u (max u w t))} D := ULiftHom.category
  letI : Preadditive D :=
    Preadditive.ofFullyFaithful (ULiftHom.equiv (C := C)).symm.fullyFaithfulFunctor
  letI : HasFiniteProducts D := by
    refine ⟨fun n => ?_⟩
    let : HasLimitsOfShape (Discrete (Fin n)) C := inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence (ULiftHom.equiv (C := C)).inverse
  exact abelianOfEquivalence (ULiftHom.equiv (C := C)).inverse

private theorem liftedModuleAB5 :
    AB5OfSize.{max u w t, max u w t}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) := by
  let C := DifferentialGradedModule.{u, v, max u w t} A
  let : Category.{max u (max u w t)} C := inferInstance
  let : HasColimitsOfSize.{max u w t, max u w t} C :=
    DifferentialGradedModule.hasColimitsOfSize.{u, v, max u w t, u, u}
  let : Abelian C := DifferentialGradedModule.abelian.{u, v, max u w t, u, u}
  let : AB5OfSize.{max u w t, max u w t} C :=
    DifferentialGradedModule.filteredColimits_exact.{max u w t, max u w t, max w t, v, u, u, u} A
  let E := ULiftHom.equiv (C := C)
  let : Category.{max (max t u) w} (ULiftHom.{max t u} C) := ULiftHom.category
  let : HasColimitsOfSize.{max u w t, max u w t} (ULiftHom.{max t u} C) := by
    exact Adjunction.has_colimits_of_equivalence.{max u w t, max u w t}
      (C := ULiftHom.{max t u} C) (D := C) E.inverse
  constructor
  intro J _ _
  exact HasExactColimitsOfShape.of_codomain_equivalence J E

variable {Idx : Type t}
variable (M M' : Idx → ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))
    (i : ∀ r, M r ⟶ M' r)

private abbrev AttachIndex
    (N : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  Σ r : Idx, (M r ⟶ N)

private noncomputable abbrev sourceCoproduct
    (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) :
    (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  ∐ fun j : AttachIndex M N => M j.1

private noncomputable abbrev targetCoproduct
    (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) :
    (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  ∐ fun j : AttachIndex M N => M' j.1

private noncomputable abbrev sourceToObject
    (N : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :
    sourceCoproduct M N ⟶ N :=
  show (∐ fun j : AttachIndex M N => M j.1) ⟶ N from
    Limits.Sigma.desc fun j => j.2

private noncomputable abbrev attachMap
    (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) :
  sourceCoproduct M N ⟶ targetCoproduct M M' N :=
  show (∐ fun j : AttachIndex M N => M j.1) ⟶
      (∐ fun j : AttachIndex M N => M' j.1) from
    Limits.Sigma.desc fun j => i j.1 ≫
      Limits.Sigma.ι (fun k : AttachIndex M N => M' k.1) j

private noncomputable abbrev targetCoproductMap
    {N P : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))} (f : N ⟶ P) :
  targetCoproduct M M' N ⟶ targetCoproduct M M' P :=
  Limits.Sigma.desc fun j => by
    exact Limits.Sigma.ι (fun k : AttachIndex M P => M' k.1) ⟨j.1, j.2 ≫ f⟩

private noncomputable abbrev sourceCoproductMap
    {N P : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))} (f : N ⟶ P) :
  sourceCoproduct M N ⟶ sourceCoproduct M P :=
  Limits.Sigma.desc fun j => by
    exact Limits.Sigma.ι (fun k : AttachIndex M P => M k.1) ⟨j.1, j.2 ≫ f⟩

private lemma targetCoproductMap_id
    (N : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :
  targetCoproductMap M M' (𝟙 N) = 𝟙 (targetCoproduct M M' N) := by
  apply Limits.Sigma.hom_ext
  intro j
  cases j with
  | mk r φ =>
      simp only [targetCoproductMap, Limits.Sigma.ι_comp_desc, Category.comp_id]
      have hidx : (⟨r, φ ≫ 𝟙 N⟩ : AttachIndex M N) = ⟨r, φ⟩ := by simp
      cases hidx
      rfl

private lemma targetCoproductMap_comp
    {N P Q : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)}
    (f : N ⟶ P) (g : P ⟶ Q) :
    targetCoproductMap M M' (f ≫ g) =
      targetCoproductMap M M' f ≫ targetCoproductMap M M' g := by
  apply Limits.Sigma.hom_ext
  intro j
  cases j with
  | mk r φ =>
      simp [targetCoproductMap]
      have hidx : (⟨r, φ ≫ (f ≫ g)⟩ : AttachIndex M Q) =
          ⟨r, (φ ≫ f) ≫ g⟩ := by
        congr 1
      cases hidx
      rfl

private theorem attachedHasPushout
  (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) :
    @HasPushout (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))
      ULiftHom.category _ _ _ (sourceToObject M N) (attachMap M M' i N) := by
  let : HasColimitsOfShape WalkingSpan
      ((ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) :=
    HasColimitsOfShape.of_small _ WalkingSpan
  infer_instance

private noncomputable abbrev attachedObject
    (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) :
    (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  letI := attachedHasPushout M M' i N
  pushout (sourceToObject M N) (attachMap M M' i N)

private noncomputable abbrev attachedInclusion
    (N : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :
    N ⟶ attachedObject M M' i N :=
  letI := attachedHasPushout M M' i N
  pushout.inl (sourceToObject M N) (attachMap M M' i N)

private theorem attachedInclusion_eq_pushoutInl
    (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) :
    attachedInclusion M M' i N =
      pushout.inl (sourceToObject M N) (attachMap M M' i N) := by
  let : HasPushout (sourceToObject M N) (attachMap M M' i N) :=
    attachedHasPushout M M' i N
  rfl

private noncomputable def attachedMap
    {N P : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))} (f : N ⟶ P) :
    attachedObject M M' i N ⟶ attachedObject M M' i P :=
  letI := attachedHasPushout M M' i N
  letI := attachedHasPushout M M' i P
  pushout.desc
    (f ≫ pushout.inl (sourceToObject M P) (attachMap M M' i P))
    (targetCoproductMap M M' f ≫
      pushout.inr (sourceToObject M P) (attachMap M M' i P))
    (by
      have hs : sourceToObject M N ≫ f =
          sourceCoproductMap M f ≫ sourceToObject M P := by
        apply Limits.Sigma.hom_ext
        intro j
        simp [sourceToObject, sourceCoproductMap, sourceCoproduct]
      have ht : attachMap M M' i N ≫ targetCoproductMap M M' f =
          sourceCoproductMap M f ≫ attachMap M M' i P := by
        apply Limits.Sigma.hom_ext
        intro j
        simp [attachMap, sourceCoproductMap, targetCoproductMap,
          sourceCoproduct, targetCoproduct, Category.assoc]
      change (sourceToObject M N ≫ f) ≫
        pushout.inl (sourceToObject M P) (attachMap M M' i P) =
        (attachMap M M' i N ≫ targetCoproductMap M M' f) ≫
          pushout.inr (sourceToObject M P) (attachMap M M' i P)
      rw [hs, Category.assoc, pushout.condition, ← Category.assoc, ht, Category.assoc])

private lemma attachedMap_inl
    {N P : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)}
    (f : N ⟶ P) :
    pushout.inl (sourceToObject M N) (attachMap M M' i N) ≫
        attachedMap M M' i f =
      f ≫ pushout.inl (sourceToObject M P) (attachMap M M' i P) := by
  let := attachedHasPushout M M' i N
  let := attachedHasPushout M M' i P
  dsimp [attachedMap]
  rw [pushout.inl_desc]

private lemma attachedMap_inr
    {N P : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)}
    (f : N ⟶ P) :
    pushout.inr (sourceToObject M N) (attachMap M M' i N) ≫
        attachedMap M M' i f =
      targetCoproductMap M M' f ≫
        pushout.inr (sourceToObject M P) (attachMap M M' i P) := by
  let := attachedHasPushout M M' i N
  let := attachedHasPushout M M' i P
  dsimp [attachedMap]
  rw [pushout.inr_desc]

private noncomputable def attachmentFunctor
    (M₀ M₀' : Idx → (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)))
    (i₀ : ∀ r, M₀ r ⟶ M₀' r) :
    (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) ⥤
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) where
  obj N := attachedObject M₀ M₀' i₀ N
  map f := attachedMap M₀ M₀' i₀ f
  map_id N := by
    let := attachedHasPushout M₀ M₀' i₀ N
    apply pushout.hom_ext
    · dsimp [attachedMap]
      simp
    · apply Limits.Sigma.hom_ext
      intro j
      dsimp [attachedMap]
      simp [targetCoproductMap_id]
  map_comp := by
    intro N P Q f g
    let := attachedHasPushout M₀ M₀' i₀ N
    let := attachedHasPushout M₀ M₀' i₀ P
    let := attachedHasPushout M₀ M₀' i₀ Q
    apply pushout.hom_ext
    · calc
        pushout.inl (sourceToObject M₀ N) (attachMap M₀ M₀' i₀ N) ≫
            attachedMap M₀ M₀' i₀ (f ≫ g) =
            (f ≫ g) ≫ pushout.inl (sourceToObject M₀ Q)
              (attachMap M₀ M₀' i₀ Q) := by
                rw [attachedMap_inl]
        _ = f ≫ (g ≫ pushout.inl (sourceToObject M₀ Q)
              (attachMap M₀ M₀' i₀ Q)) := by simp [Category.assoc]
        _ = (pushout.inl (sourceToObject M₀ N) (attachMap M₀ M₀' i₀ N) ≫
              attachedMap M₀ M₀' i₀ f) ≫ attachedMap M₀ M₀' i₀ g := by
                simp [attachedMap_inl, Category.assoc]
    · calc
        pushout.inr (sourceToObject M₀ N) (attachMap M₀ M₀' i₀ N) ≫
            attachedMap M₀ M₀' i₀ (f ≫ g) =
            targetCoproductMap M₀ M₀' (f ≫ g) ≫
              pushout.inr (sourceToObject M₀ Q) (attachMap M₀ M₀' i₀ Q) := by
                rw [attachedMap_inr]
        _ = (targetCoproductMap M₀ M₀' f ≫ targetCoproductMap M₀ M₀' g) ≫
              pushout.inr (sourceToObject M₀ Q) (attachMap M₀ M₀' i₀ Q) := by
                rw [targetCoproductMap_comp]
        _ = targetCoproductMap M₀ M₀' f ≫
              (targetCoproductMap M₀ M₀' g ≫
                pushout.inr (sourceToObject M₀ Q) (attachMap M₀ M₀' i₀ Q)) := by
                simp [Category.assoc]
        _ = (pushout.inr (sourceToObject M₀ N) (attachMap M₀ M₀' i₀ N) ≫
              attachedMap M₀ M₀' i₀ f) ≫ attachedMap M₀ M₀' i₀ g := by
                simp [attachedMap_inr]

private noncomputable def attachmentInclusion :
    𝟭 ((ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) ⟶
      attachmentFunctor M M' i where
  app N := attachedInclusion M M' i N
  naturality N P f := by
    let := attachedHasPushout M M' i N
    let := attachedHasPushout M M' i P
    dsimp [attachmentFunctor, attachedMap, attachedInclusion, attachedObject,
      attachMap, sourceToObject, sourceCoproduct, targetCoproduct]
    simp

private lemma attachMap_mono
    (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)))
    (hi : ∀ r, Mono (i r)) :
    Mono (attachMap M M' i N) := by
  let (j : AttachIndex M N) : Mono (i j.1) := hi j.1
  let C := DifferentialGradedModule.{u, v, max u w t} A
  let : Category.{max u (max u w t)} C := inferInstance
  let : Abelian C :=
    DifferentialGradedModule.abelian.{u, v, max u w t, u, u}
  let : HasFiniteProducts C := inferInstance
  let : Category.{max (max t u) w}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) := ULiftHom.category
  let : Preadditive (ULiftHom.{max t u} C) :=
    Preadditive.ofFullyFaithful (ULiftHom.equiv (C := C)).symm.fullyFaithfulFunctor
  let : HasFiniteProducts (ULiftHom.{max t u} C) := by
    refine ⟨fun n => ?_⟩
    let : HasLimitsOfShape (Discrete (Fin n)) C := inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence (ULiftHom.equiv (C := C)).inverse
  let : Abelian (ULiftHom.{max t u} C) :=
    abelianOfEquivalence (ULiftHom.equiv (C := C)).inverse
  let : HasFiniteBiproducts (ULiftHom.{max t u} C) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : AB5OfSize.{max u w t, max u w t}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
    liftedModuleAB5.{u, v, w, t} (X := X) (A := A)
  let : UnivLE.{max (max t u) w, max u w t} := inferInstance
  let : AB5OfSize.{max (max t u) w, max (max t u) w}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
    AB5OfSize_of_univLE _
  let : AB4OfSize.{max (max t u) w, max (max t u) w,
      max (max (max (t + 1) (u + 1)) v) (w + 1)}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
    AB4.of_AB5.{max (max t u) w, max (max t u) w,
      max (max (max (t + 1) (u + 1)) v) (w + 1)} _
  let : AB4OfSize.{max u w t}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
    AB4OfSize_shrink.{max u w t, max (max t u) w} _
  let : HasCoproducts.{max u w t}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) := inferInstance
  let : MorphismProperty.IsStableUnderCoproducts.{max u w t}
      (MorphismProperty.monomorphisms
        (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A))) := inferInstance
  let : MorphismProperty.IsStableUnderCoproductsOfShape
      (MorphismProperty.monomorphisms
        (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)))
      (AttachIndex M N) := inferInstance
  change Mono (Limits.Sigma.map fun j : AttachIndex M N => i j.1)
  infer_instance

private lemma attachedInclusion_mono
    (N : (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)))
    (hi : ∀ r, Mono (i r)) :
    Mono (attachedInclusion M M' i N) := by
  let : Mono (attachMap M M' i N) := attachMap_mono M M' i N hi
  let C := DifferentialGradedModule.{u, v, max u w t} A
  let : Category.{max u (max u w t)} C := inferInstance
  let : Abelian C :=
    DifferentialGradedModule.abelian.{u, v, max u w t, u, u}
  let : HasZeroMorphisms C := Preadditive.preadditiveHasZeroMorphisms
  let : Category.{max (max t u) w}
      (ULiftHom.{max t u} C) := ULiftHom.category
  let : Abelian (ULiftHom.{max t u} C) := liftedModuleAbelian (X := X) (A := A)
  exact inferInstance

end

section AcyclicCokernel

private lemma coproductAcyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    {I : Type w}
    [HasColimitsOfShape (Discrete I) C]
    [HasExactColimitsOfShape (Discrete I) C]
    (F : I → CochainComplex C ℤ) (K : CochainComplex C ℤ)
    (ι : ∀ i, F i ⟶ K)
    (hcF : IsColimit (Cofan.mk K ι))
    (hF : ∀ i, (F i).Acyclic) : K.Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff' K (n - 1) n (n + 1)
    (by simp [CochainComplex.prev]) (by simp [CochainComplex.next])]
  let G : Discrete I ⥤ CochainComplex C ℤ := Discrete.functor F
  let F₁ := HomologicalComplex.eval C (ComplexShape.up ℤ) (n - 1)
  let F₂ := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let F₃ := HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)
  let D₁ := G ⋙ F₁
  let D₂ := G ⋙ F₂
  let D₃ := G ⋙ F₃
  let f : D₁ ⟶ D₂ := {
    app := fun i => (F i.as).d (n - 1) n
    naturality := by intro i j q; cat_disch }
  let g : D₂ ⟶ D₃ := {
    app := fun i => (F i.as).d n (n + 1)
    naturality := by intro i j q; cat_disch }
  let S : ShortComplex (Discrete I ⥤ C) :=
    ShortComplex.mk f g (by
      ext i
      exact HomologicalComplex.d_comp_d (F i.as) (n - 1) n (n + 1))
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
    ext i
    let E := (CategoryTheory.evaluation (Discrete I) C).obj i
    have hi : (S.map E).Exact := by
      have hs : ((F i.as).sc' (n - 1) n (n + 1)).Exact :=
        (HomologicalComplex.exactAt_iff' (F i.as) (n - 1) n (n + 1)
          (by simp [CochainComplex.prev]) (by simp [CochainComplex.next])).mp (hF i.as n)
      change (ShortComplex.mk (E.map S.f) (E.map S.g) _).Exact
      simpa [E, S, f, g, D₁, D₂, D₃, F₁, F₂, F₃,
        HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
        HomologicalComplex.shortComplexFunctor'_obj_X₁,
        HomologicalComplex.shortComplexFunctor'_obj_X₂,
        HomologicalComplex.shortComplexFunctor'_obj_X₃,
        HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g] using hs
    have hieq := (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero (S.map E)).mp hi
    have hz : kernel.ι (E.map S.g) ≫ cokernel.π (E.map S.f) = 0 := by
      change kernel.ι (S.map E).g ≫ cokernel.π (S.map E).f = 0
      exact hieq
    change E.map (kernel.ι S.g) ≫ E.map (cokernel.π S.f) = 0
    rw [← kernelComparison_comp_ι S.g E, ← π_comp_cokernelComparison S.f E]
    calc
      (kernelComparison S.g E ≫ kernel.ι (E.map S.g)) ≫
          cokernel.π (E.map S.f) ≫ cokernelComparison S.f E =
        kernelComparison S.g E ≫
          (kernel.ι (E.map S.g) ≫ cokernel.π (E.map S.f)) ≫ cokernelComparison S.f E := by
            simp [Category.assoc]
      _ = 0 := by rw [hz]; simp
  let cF : Cofan F := Cofan.mk K ι
  let c₁ : Cocone S.X₁ := F₁.mapCocone cF
  let c₂ : Cocone S.X₂ := F₂.mapCocone cF
  let c₃ : Cocone S.X₃ := F₃.mapCocone cF
  have hp₁ : PreservesColimit G F₁ := by dsimp [G, F₁]; infer_instance
  have hp₂ : PreservesColimit G F₂ := by dsimp [G, F₂]; infer_instance
  have hp₃ : PreservesColimit G F₃ := by dsimp [G, F₃]; infer_instance
  have hc₁ : IsColimit c₁ := isColimitOfPreserves F₁ hcF
  have hc₂ : IsColimit c₂ := isColimitOfPreserves F₂ hcF
  have hc₃ : IsColimit c₃ := isColimitOfPreserves F₃ hcF
  let d₁ := K.d (n - 1) n
  let d₂ := K.d n (n + 1)
  let hf : ∀ i, c₁.ι.app i ≫ d₁ = S.f.app i ≫ c₂.ι.app i := by
    intro i
    change (ι i.as).f (n - 1) ≫ K.d (n - 1) n =
      (F i.as).d (n - 1) n ≫ (ι i.as).f n
    exact (ι i.as).comm (n - 1) n
  let hg : ∀ i, c₂.ι.app i ≫ d₂ = S.g.app i ≫ c₃.ι.app i := by
    intro i
    change (ι i.as).f n ≫ K.d n (n + 1) =
      (F i.as).d n (n + 1) ≫ (ι i.as).f (n + 1)
    exact (ι i.as).comm n (n + 1)
  let T := Limits.colim.mapShortComplex S hc₁ c₂ c₃ d₁ d₂ hf hg
  have hT := Limits.colim.exact_mapShortComplex hS hc₁ hc₂ hc₃ d₁ d₂ hf hg
  simpa [T, d₁, d₂, c₁, c₂, c₃, cF, F₁, F₂, F₃, D₁, D₂, D₃,
    Limits.colim.mapShortComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor'] using hT

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
variable {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
variable [HasSheafify X.J AddCommGrpCat.{max u w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u w}]

private lemma quasiIsoOfShortExactAcyclicCokernel
    {B : Type*} [Category* B] [Abelian B]
    {S : ShortComplex (CochainComplex B ℤ)} (hS : S.ShortExact)
    (hX₃ : S.X₃.Acyclic) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (HomologicalComplex.homologyMap S.f n) := by
    have hRel : (ComplexShape.up ℤ).Rel (n - 1) n := by simp
    have hExact := hS.homology_exact₁ (n - 1) n hRel
    have hzero := (hX₃ (n - 1)).isZero_homology
    have hδ : hS.δ (n - 1) n hRel = 0 := hzero.eq_of_src _ _
    exact hExact.mono_g hδ
  have hepi : Epi (HomologicalComplex.homologyMap S.f n) := by
    have hExact := hS.homology_exact₂ n
    have hzero := (hX₃ n).isZero_homology
    have hg : HomologicalComplex.homologyMap S.g n = 0 := hzero.eq_of_tgt _ _
    exact hExact.epi_f hg
  exact isIso_of_mono_of_epi _

private theorem cokernelAcyclic
    {P Q : DifferentialGradedModule.{u, v, max u w} A}
    (f : P ⟶ Q) [Mono f]
    (hP : P.complex.Acyclic) (hQ : Q.complex.Acyclic) :
    (@cokernel (DifferentialGradedModule.{u, v, max u w} A)
      inferInstance Preadditive.preadditiveHasZeroMorphisms
      P Q f).complex.Acyclic := by
  let : Abelian (DifferentialGradedModule.{u, v, max u w} A) :=
    DifferentialGradedModule.abelian (A := A)
  let : HasZeroMorphisms (DifferentialGradedModule.{u, v, max u w} A) :=
    Preadditive.preadditiveHasZeroMorphisms
  let : HasCokernels (DifferentialGradedModule.{u, v, max u w} A) := inferInstance
  let S : @ShortComplex (DifferentialGradedModule.{u, v, max u w} A) _
      (Preadditive.preadditiveHasZeroMorphisms) :=
    @ShortComplex.mk _ _ (Preadditive.preadditiveHasZeroMorphisms)
      P Q (cokernel f) f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := by simpa [S] using ShortComplex.exact_cokernel f }
  have hf : QuasiIso f.toHomologicalComplex := by
    constructor
    intro n
    exact (quasiIsoAt_iff_exactAt f.toHomologicalComplex n (hP n)).2 (hQ n)
  have hh := (toCochainComplex_shortExact A S hS).acyclic_X₃ hf
  simpa [S, toCochainComplex] using hh

end AcyclicCokernel

section LiftedAcyclicity

universe q

private lemma differentialGradedModuleCoproductAcyclic
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [HasSheafify X.J AddCommGrpCat.{q}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{q}]
    {I : Type q}
    (F : I → DifferentialGradedModule.{u, v, q} A)
    (K : DifferentialGradedModule.{u, v, q} A)
    (ι : ∀ i, F i ⟶ K)
    (hcDGM : IsColimit (Cofan.mk K ι))
    (hF : ∀ i, (F i).complex.Acyclic) :
    K.complex.Acyclic := by
  let C := SheafOfModules.{q} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : Category C := SheafOfModules.instCategory
  let : Preadditive C := SheafOfModules.instPreadditive (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : Abelian C := inferInstance
  let : AB5OfSize.{q, q} C := inferInstance
  let : HasFiniteProducts C := inferInstance
  let : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  let _ : ∀ J : Type q, HasColimitsOfShape (Discrete J)
      (PresheafOfModules.{q} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) := fun J =>
    PresheafOfModules.hasColimitsOfShape _ _
  let : HasCoproducts.{q} C := fun J =>
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Discrete J)
  let : AB4OfSize.{q} C :=
    AB4.of_AB5.{q, max u q, max u (q + 1)} C
  let : HasColimitsOfShape (Discrete I) C := inferInstance
  let : HasExactColimitsOfShape (Discrete I) C := inferInstance
  let G : I → CochainComplex C ℤ := fun i => (F i).complex
  let cStdDGM : Cofan F := Cofan.mk (∐ F) (Sigma.ι F)
  have hcStdDGM : IsColimit cStdDGM := coproductIsCoproduct F
  let eDGM := IsColimit.coconePointUniqueUpToIso hcStdDGM hcDGM
  let U : DifferentialGradedModule.{u, v, q} A ⥤ CochainComplex C ℤ :=
    { obj := fun M => M.complex
      map := fun f => f.toHomologicalComplex
      map_id := fun M => by ext n; rfl
      map_comp := fun f g => by ext n; rfl }
  let eComplex := U.mapIso eDGM
  let cStdComplex : Cofan G := Cofan.mk (∐ F).complex
    (fun i => (Sigma.ι F i).toHomologicalComplex)
  let cTargetComplex : Cofan G := Cofan.mk K.complex
    (fun i => (ι i).toHomologicalComplex)
  let eCocone : cStdComplex ≅ cTargetComplex := by
    exact Cocone.ext eComplex (fun j => by
      cases j with
      | mk i =>
        change (Sigma.ι F i).toHomologicalComplex ≫
          eDGM.hom.toHomologicalComplex = (ι i).toHomologicalComplex
        exact congrArg (fun f => f.toHomologicalComplex)
          (IsColimit.comp_coconePointUniqueUpToIso_hom hcStdDGM hcDGM
            (Discrete.mk i)))
  have hcStdComplex : IsColimit cStdComplex := by
    apply HomologicalComplex.isColimitOfEval
    intro n
    let E := HomologicalComplex.eval C (ComplexShape.up ℤ) n
    let c₁ : Cofan (fun i => (F i).complex.X n) :=
      Cofan.mk ((∐ F).complex.X n)
        (fun i => (Sigma.ι F i).toHomologicalComplex.f n)
    let c₂ := E.mapCocone cStdComplex
    let eD := Discrete.compNatIsoDiscrete G E
    let c₂' := (Cocone.precompose eD.inv).obj c₂
    have e : c₁ ≅ c₂' := by
      apply Cocone.ext (Iso.refl _)
    have h₂' : IsColimit c₂' := IsColimit.ofIsoColimit
      (DifferentialGradedModule.coproductIsColimit_degree A F n) e
    exact (IsColimit.precomposeHomEquiv eD.symm c₂) h₂'
  have hc : IsColimit cTargetComplex := IsColimit.ofIsoColimit hcStdComplex eCocone
  exact coproductAcyclic (C := C) (F := G) (K := K.complex)
    (ι := fun i => (ι i).toHomologicalComplex) hc hF

private lemma liftedCoproductAcyclic
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [HasSheafify X.J AddCommGrpCat.{q}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{q}]
    {I : Type q}
    (F : I → ULiftHom.{max t u}
      (DifferentialGradedModule.{u, v, q} A))
    (K : ULiftHom.{max t u}
      (DifferentialGradedModule.{u, v, q} A))
    (ι : ∀ i, F i ⟶ K)
    (hcLift : IsColimit (Cofan.mk K ι))
    (hF : ∀ i, (F i).complex.Acyclic) : K.complex.Acyclic := by
  let C := DifferentialGradedModule.{u, v, q} A
  let : Category.{max u q} C := inferInstance
  let D := ULiftHom.{max t u} C
  let : Category.{max (max t u) (max u q)} D := ULiftHom.category
  let E : C ≌ D := ULiftHom.equiv (C := C)
  let F' : I → C := fun i => E.inverse.obj (F i)
  let K' : C := E.inverse.obj K
  let ι' : ∀ i, F' i ⟶ K' := fun i => E.inverse.map (ι i)
  have hc0 := isColimitOfPreserves E.inverse hcLift
  let eD := Discrete.compNatIsoDiscrete F E.inverse
  let hc0' := (Cocone.precompose eD.inv).obj
    (E.inverse.mapCocone (Cofan.mk K ι))
  have hcIso : hc0' ≅ Cofan.mk K' ι' := by
    apply Cocone.ext (Iso.refl _)
  have hc0'lim : IsColimit hc0' :=
    (IsColimit.precomposeHomEquiv eD.symm
      (E.inverse.mapCocone (Cofan.mk K ι))).symm hc0
  have hc : IsColimit (Cofan.mk K' ι') := IsColimit.ofIsoColimit hc0'lim hcIso
  let U : D ⥤ CochainComplex (SheafOfModules.{q} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    { obj := fun M => M.complex
      map := fun f => (E.inverse.map f).toHomologicalComplex
      map_id := fun M => by ext n; rfl
      map_comp := fun f g => by ext n; rfl }
  have hF' : ∀ i, (F' i).complex.Acyclic := by
    intro i
    let e := U.mapIso (E.counitIso.app (F i))
    intro n
    simpa [F', U, E, ULiftHom.equiv, ULiftHom.up, ULiftHom.down,
      ULiftHom.objDown, ULiftHom.objUp] using
      (hF i n).of_iso e.symm
  have hK' : K'.complex.Acyclic :=
    differentialGradedModuleCoproductAcyclic F' K' ι' hc hF'
  let eComplex := U.mapIso (E.counitIso.app K)
  intro n
  simpa [U, E, ULiftHom.equiv, ULiftHom.up, ULiftHom.down,
    ULiftHom.objDown, ULiftHom.objUp] using
    (hK' n).of_iso eComplex

private lemma liftedCokernelAcyclic
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [HasSheafify X.J AddCommGrpCat.{max u w t}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u w t}]
    {P Q : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)}
    [Abelian (ULiftHom.{max t u}
      (DifferentialGradedModule.{u, v, max u w t} A))]
    (f : P ⟶ Q) [Mono f]
    (hP : P.complex.Acyclic) (hQ : Q.complex.Acyclic) :
    (cokernel f).complex.Acyclic := by
  let C := DifferentialGradedModule.{u, v, max u w t} A
  let : Category.{max u (max u w t)} C :=
    inferInstance
  let D := ULiftHom.{max t u} C
  let : Category.{max (max t u) (max u (max u w t))} D := ULiftHom.category
  let : HasColimitsOfSize.{max u w t, max u w t} C :=
    DifferentialGradedModule.hasColimitsOfSize.{u, v, max u w t, u, u}
  let : HasColimitsOfSize.{max u w t, max u w t} D :=
    liftedModuleColimits.{u, v, w, t} (X := X) (A := A)
  let : Abelian C :=
    DifferentialGradedModule.abelian.{u, v, max u w t, u, u}
  let : HasZeroMorphisms C := Preadditive.preadditiveHasZeroMorphisms
  let E : C ≌ D := ULiftHom.equiv (C := C)
  let f' : E.inverse.obj P ⟶ E.inverse.obj Q := E.inverse.map f
  let : Mono f' := by dsimp [f']; infer_instance
  let V : C ⥤
      CochainComplex (SheafOfModules.{max u w t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    { obj := fun M => M.complex
      map := fun g => g.toHomologicalComplex
      map_id := fun M => by ext n; rfl
      map_comp := fun g h => by ext n; rfl }
  let U : D ⥤
      CochainComplex (SheafOfModules.{max u w t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    { obj := fun M => M.complex
      map := fun g => (E.inverse.map g).toHomologicalComplex
      map_id := fun M => by ext n; rfl
      map_comp := fun g h => by ext n; rfl }
  have hP' : (E.inverse.obj P).complex.Acyclic := by
    let e := U.mapIso (E.counitIso.app P)
    intro n
    simpa [U, E, ULiftHom.equiv, ULiftHom.up, ULiftHom.down,
      ULiftHom.objDown, ULiftHom.objUp] using (hP n).of_iso e.symm
  have hQ' : (E.inverse.obj Q).complex.Acyclic := by
    let e := U.mapIso (E.counitIso.app Q)
    intro n
    simpa [U, E, ULiftHom.equiv, ULiftHom.up, ULiftHom.down,
      ULiftHom.objDown, ULiftHom.objUp] using (hQ n).of_iso e.symm
  let cD : CokernelCofork f := CokernelCofork.ofπ (cokernel.π f)
    (cokernel.condition f)
  let cC : CokernelCofork f' := CokernelCofork.ofπ (cokernel.π f')
    (cokernel.condition f')
  have hcD : IsColimit cD := cokernelIsCokernel f
  have hcC : IsColimit cC := cokernelIsCokernel f'
  let cMapped := cD.map E.inverse
  have hcMapped : IsColimit cMapped := cD.mapIsColimit hcD E.inverse
  let eCoker := hcC.coconePointUniqueUpToIso hcMapped
  let eComplex := V.mapIso eCoker
  let eComplex' : (cokernel f').complex ≅
      (E.inverse.obj (cokernel f)).complex := by
    simpa [V, E, cMapped, cD, cC, f', CokernelCofork.map] using eComplex
  have hCoker' : (E.inverse.obj (cokernel f)).complex.Acyclic := by
    intro n
    exact ((cokernelAcyclic.{u, v, max w t} f' hP' hQ') n).of_iso eComplex'
  let eLift := U.mapIso (E.counitIso.app (cokernel f))
  intro n
  simpa [U, E, ULiftHom.equiv, ULiftHom.up, ULiftHom.down,
    ULiftHom.objDown, ULiftHom.objUp] using (hCoker' n).of_iso eLift

end LiftedAcyclicity

section AttachedQuasiIso

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
variable {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
variable [HasSheafify X.J AddCommGrpCat.{max u w t}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u w t}]
variable {Idx : Type t}
variable (M M' : Idx → ULiftHom.{max t u}
  (DifferentialGradedModule.{u, v, max u w t} A))
variable (i : ∀ r, M r ⟶ M' r)

/-- The universe-lifted category of differential graded `A`-modules has all colimits of size
`max u w t`.

This and the following instances of the first section are named here for two reasons: the
statement of `attachedCokernelAcyclic` below mentions a cokernel, so the abelian structure has to
be fixed before it rather than inside a proof; and the searches that find them have to unify the
two levels of a `HasColimitsOfSize` against a shape category, which is expensive enough that doing
it inside each proof exhausts the heartbeat budget. -/
local instance liftedColimits :
    HasColimitsOfSize.{max u w t, max u w t}
      (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  liftedModuleColimits.{u, v, w, t} (X := X) (A := A)

@[instance_reducible] private noncomputable local instance liftedAbelian :
    Abelian (ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)) :=
  liftedModuleAbelian.{u, v, w, t} (X := X) (A := A)

/-- The cokernel of the attachment inclusion is acyclic. The inclusion is the pushout of
`∐ M ⟶ ∐ M'` along `∐ M ⟶ N`, so the two have the same cokernel, and that of `∐ M ⟶ ∐ M'` is
acyclic because both coproducts are. -/
private lemma attachedCokernelAcyclic
    (N : ULiftHom.{max t u}
      (DifferentialGradedModule.{u, v, max u w t} A))
    (hi : ∀ r, Mono (i r))
    (hM : ∀ r, (M r).complex.Acyclic)
    (hM' : ∀ r, (M' r).complex.Acyclic) :
    (cokernel (attachedInclusion M M' i N)).complex.Acyclic := by
  let C := DifferentialGradedModule.{u, v, max u w t} A
  let D := ULiftHom.{max t u} C
  let : HasCoproduct (fun j : AttachIndex M N => M j.1) :=
    (liftedColimits.has_colimits_of_shape (Discrete (AttachIndex M N))).has_colimit _
  let : HasCoproduct (fun j : AttachIndex M N => M' j.1) :=
    (liftedColimits.has_colimits_of_shape (Discrete (AttachIndex M N))).has_colimit _
  let : Mono (attachMap M M' i N) := attachMap_mono M M' i N hi
  have hSource : (sourceCoproduct M N).complex.Acyclic := by
    apply liftedCoproductAcyclic (X := X) (A := A)
      (F := fun j : AttachIndex M N => M j.1)
      (K := sourceCoproduct M N)
      (ι := Sigma.ι fun j : AttachIndex M N => M j.1)
      (hcLift := coproductIsCoproduct (fun j : AttachIndex M N => M j.1))
    exact fun j => hM j.1
  have hTarget : (targetCoproduct M M' N).complex.Acyclic := by
    apply liftedCoproductAcyclic (X := X) (A := A)
      (F := fun j : AttachIndex M N => M' j.1)
      (K := targetCoproduct M M' N)
      (ι := Sigma.ι fun j : AttachIndex M N => M' j.1)
      (hcLift := coproductIsCoproduct (fun j : AttachIndex M N => M' j.1))
    exact fun j => hM' j.1
  have hCokerAttach : (cokernel (attachMap M M' i N)).complex.Acyclic :=
    liftedCokernelAcyclic (attachMap M M' i N) hSource hTarget
  let : HasPushout (sourceToObject M N) (attachMap M M' i N) :=
    attachedHasPushout M M' i N
  have hpo0 : IsPushout (sourceToObject M N) (attachMap M M' i N)
      (pushout.inl (sourceToObject M N) (attachMap M M' i N))
      (pushout.inr (sourceToObject M N) (attachMap M M' i N)) := by
    refine ⟨⟨pushout.condition⟩, ?_⟩
    exact ⟨pushoutIsPushout (sourceToObject M N) (attachMap M M' i N)⟩
  let hpo := hpo0.flip
  let cokerMap := cokernel.map (attachMap M M' i N)
    (pushout.inl (sourceToObject M N) (attachMap M M' i N))
    (sourceToObject M N) (pushout.inr (sourceToObject M N) (attachMap M M' i N)) hpo.w
  have hcokerMap : IsIso cokerMap := isIso_cokernel_map_of_isPushout hpo
  let cokerIso : cokernel (attachMap M M' i N) ≅
      cokernel (attachedInclusion M M' i N) := by
    rw [attachedInclusion_eq_pushoutInl]
    exact asIso cokerMap
  let E : C ≌ D := ULiftHom.equiv (C := C)
  let V : C ⥤
      CochainComplex (SheafOfModules.{max u w t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    toCochainComplex.{u, v, max u w t, u, u} A
  let : HasZeroMorphisms C := Preadditive.preadditiveHasZeroMorphisms
  let U : D ⥤
      CochainComplex (SheafOfModules.{max u w t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    E.inverse ⋙ V
  intro n
  simpa [U, V, toCochainComplex, E,
    ULiftHom.equiv, ULiftHom.up, ULiftHom.down,
    ULiftHom.objDown, ULiftHom.objUp] using
    (hCokerAttach n).of_iso (U.mapIso cokerIso)

/-- In the `ULiftHom` category of right differential graded modules, a monomorphism with acyclic
cokernel is a quasi-isomorphism: forgetting the action takes the short exact sequence
`N ⟶ P ⟶ coker f` to a short exact sequence of complexes (Tag 0FRK), whose long exact cohomology
sequence has vanishing third term. -/
private lemma quasiIso_of_mono_of_cokernelAcyclic
    {N P : ULiftHom.{max t u} (DifferentialGradedModule.{u, v, max u w t} A)}
    (f : N ⟶ P) [Mono f] (hcoker : (cokernel f).complex.Acyclic) :
    QuasiIso f.down.toHomologicalComplex := by
  let C := DifferentialGradedModule.{u, v, max u w t} A
  let D := ULiftHom.{max t u} C
  let E : C ≌ D := ULiftHom.equiv (C := C)
  let V : C ⥤
      CochainComplex (SheafOfModules.{max u w t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    toCochainComplex.{u, v, max u w t, u, u} A
  let U : D ⥤
      CochainComplex (SheafOfModules.{max u w t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    E.inverse ⋙ V
  let S : ShortComplex D := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := by
    refine ⟨?_⟩
    exact ShortComplex.exact_cokernel f
  let : E.inverse.Additive := E.symm.fullyFaithfulFunctor.additive_ofFullyFaithful
  let : V.PreservesZeroMorphisms := inferInstance
  let : U.PreservesZeroMorphisms := inferInstance
  have hS' : (S.map E.inverse).ShortExact := hS.map_of_exact E.inverse
  have hUnderlying : (S.map U).ShortExact := by
    have hh := toCochainComplex_shortExact A (S.map E.inverse) hS'
    simpa [S, U, V, ShortComplex.map_comp] using hh
  have hCoker : (S.map U).X₃.Acyclic := hcoker
  exact quasiIsoOfShortExactAcyclicCokernel hUnderlying hCoker

/-- The attachment inclusion is a quasi-isomorphism: it is a monomorphism and its cokernel is
acyclic. -/
private lemma attachedInclusion_quasiIso
    (N : ULiftHom.{max t u}
      (DifferentialGradedModule.{u, v, max u w t} A))
    (hi : ∀ r, Mono (i r))
    (hM : ∀ r, (M r).complex.Acyclic)
    (hM' : ∀ r, (M' r).complex.Acyclic) :
    QuasiIso (attachedInclusion M M' i N).down.toHomologicalComplex :=
  let : Mono (attachedInclusion M M' i N) := attachedInclusion_mono M M' i N hi
  quasiIso_of_mono_of_cokernelAcyclic (attachedInclusion M M' i N)
    (attachedCokernelAcyclic M M' i N hi hM hM')

end AttachedQuasiIso

/-- A functorial extension along a family of monomorphisms of differential
graded modules, with quasi-isomorphic monomorphic unit. -/
structure SetOfMonosExtension {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [HasSheafify X.J AddCommGrpCat.{max u w t}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u w t}]
    {Idx : Type t} (M M' : Idx → DifferentialGradedModule.{u, v, max u w t} A)
    (i : ∀ r, M r ⟶ M' r) where
  /-- The endofunctor obtained by attaching all prescribed extensions. -/
  functor : DifferentialGradedModule.{u, v, max u w t} A ⥤
    DifferentialGradedModule.{u, v, max u w t} A
  /-- The natural inclusion into the extension. -/
  inclusion : 𝟭 (DifferentialGradedModule.{u, v, max u w t} A) ⟶ functor
  /-- Each component of the inclusion is injective. -/
  mono (N : DifferentialGradedModule.{u, v, max u w t} A) : Mono (inclusion.app N)
  /-- Each component of the inclusion is a quasi-isomorphism. -/
  quasiIso (N : DifferentialGradedModule.{u, v, max u w t} A) :
    QuasiIso (inclusion.app N).toHomologicalComplex
  /-- Every map from a prescribed source extends after the inclusion. -/
  extension (N : DifferentialGradedModule.{u, v, max u w t} A)
      (r : Idx) (f : M r ⟶ N) :
    ∃ g : M' r ⟶ functor.obj N, i r ≫ g = f ≫ inclusion.app N

/-- Functorially attach all maps from the sources of a set of acyclic
monomorphisms. -/
@[stacks 0FSZ]
noncomputable def functorSetOfMonos {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [HasSheafify X.J AddCommGrpCat.{max u w t}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u w t}]
    {Idx : Type t} (M M' : Idx → DifferentialGradedModule.{u, v, max u w t} A)
    (i : ∀ r, M r ⟶ M' r)
    (hi : ∀ r, Mono (i r))
    (hM : ∀ r, (M r).complex.Acyclic)
    (hM' : ∀ r, (M' r).complex.Acyclic) :
    SetOfMonosExtension M M' i := by
  let C := DifferentialGradedModule.{u, v, max u w t} A
  letI : Category.{max u (max u w t)} C :=
    inferInstance
  letI : HasColimitsOfSize.{max u w t, max u w t} C :=
    DifferentialGradedModule.hasColimitsOfSize.{u, v, max u w t, u, u}
  letI : Abelian C :=
    DifferentialGradedModule.abelian.{u, v, max u w t, u, u}
  letI : HasZeroMorphisms C := Preadditive.preadditiveHasZeroMorphisms
  let D := ULiftHom.{max t u} C
  letI : Category.{max (max t u) (max u (max u w t))} D := ULiftHom.category
  letI : HasColimitsOfSize.{max u w t, max u w t} D :=
    liftedModuleColimits.{u, v, w, t} (X := X) (A := A)
  let E : C ≌ D := ULiftHom.equiv (C := C)
  let ML : Idx → D := fun r => E.functor.obj (M r)
  let ML' : Idx → D := fun r => E.functor.obj (M' r)
  let iL : ∀ r, ML r ⟶ ML' r := fun r => E.functor.map (i r)
  let Fd := attachmentFunctor ML ML' iL
  let F : C ⥤ C := E.functor ⋙ Fd ⋙ E.inverse
  let η : 𝟭 C ⟶ F :=
    E.unitIso.hom ≫ Functor.whiskerRight
      (Functor.whiskerLeft E.functor (attachmentInclusion ML ML' iL)) E.inverse
  refine ⟨F, η, ?_, ?_, ?_⟩
  · intro N
    change Mono (E.unitIso.hom.app N ≫
      E.inverse.map (attachedInclusion ML ML' iL (E.functor.obj N)))
    constructor
    intro Z a b hab
    let f₀ := attachedInclusion ML ML' iL (E.functor.obj N)
    let : Mono f₀ :=
      attachedInclusion_mono ML ML' iL (E.functor.obj N) (fun r => by
        let : Mono (i r) := hi r
        infer_instance)
    have hMapped : Mono (E.inverse.map f₀) := by
      constructor
      intro W g h hgh
      apply E.functor.map_injective
      have hmap := congrArg (fun k => E.functor.map k) hgh
      have hmap' : E.functor.map g ≫ f₀ = E.functor.map h ≫ f₀ := by
        convert hmap using 1 <;> rfl
      exact (cancel_mono f₀).1 hmap'
    let : Mono (E.inverse.map f₀) := hMapped
    have h1 := (cancel_mono (E.inverse.map f₀)).1 hab
    exact (cancel_mono (E.unitIso.hom.app N)).1 h1
  · intro N
    have hUnit : QuasiIso (E.unitIso.hom.app N).toHomologicalComplex := by
      let : IsIso (E.unitIso.hom.app N) := inferInstance
      let : IsIso (E.unitIso.hom.app N).toHomologicalComplex := by
        change IsIso
          ((toCochainComplex.{u, v, max u w t, u, u} A).map
            (E.unitIso.hom.app N))
        infer_instance
      infer_instance
    have hAttach : QuasiIso
        (E.inverse.map (attachedInclusion ML ML' iL (E.functor.obj N))).toHomologicalComplex := by
      simpa [E, ULiftHom.equiv, ULiftHom.down, ULiftHom.objDown,
        toCochainComplex] using
        (attachedInclusion_quasiIso ML ML' iL (E.functor.obj N)
          (fun r => by let : Mono (i r) := hi r; infer_instance)
          (fun r => by change (M r).complex.Acyclic; exact hM r)
          (fun r => by change (M' r).complex.Acyclic; exact hM' r))
    have hComp := quasiIso_comp
      (φ := (E.unitIso.hom.app N).toHomologicalComplex)
      (φ' := (E.inverse.map (attachedInclusion ML ML' iL (E.functor.obj N))).toHomologicalComplex)
      (hφ := hUnit) (hφ' := hAttach)
    change QuasiIso
      ((E.unitIso.hom.app N).toHomologicalComplex ≫
        (E.inverse.map (attachedInclusion ML ML' iL (E.functor.obj N))).toHomologicalComplex)
    exact hComp
  · intro N r f
    let nD := E.functor.obj N
    let j : AttachIndex ML nD := ⟨r, E.functor.map f⟩
    let d : ML' r ⟶ attachedObject ML ML' iL nD :=
      Limits.Sigma.ι (fun k : AttachIndex ML nD => ML' k.1) j ≫
        pushout.inr (sourceToObject ML nD) (attachMap ML ML' iL nD)
    let g : M' r ⟶ F.obj N :=
      E.unitIso.hom.app (M' r) ≫ E.inverse.map d
    refine ⟨g, ?_⟩
    have hd : E.functor.map (i r) ≫ d =
        E.functor.map f ≫ attachedInclusion ML ML' iL nD := by
      let : HasPushout (sourceToObject ML nD) (attachMap ML ML' iL nD) :=
        attachedHasPushout ML ML' iL nD
      dsimp [d, attachedInclusion]
      calc
        E.functor.map (i r) ≫
            Limits.Sigma.ι (fun k : AttachIndex ML nD => ML' k.1) j ≫
                pushout.inr (sourceToObject ML nD) (attachMap ML ML' iL nD) =
            Limits.Sigma.ι (fun k : AttachIndex ML nD => ML k.1) j ≫
              attachMap ML ML' iL nD ≫
                pushout.inr (sourceToObject ML nD) (attachMap ML ML' iL nD) := by
                  have hι : E.functor.map (i r) ≫
                      Limits.Sigma.ι (fun k : AttachIndex ML nD => ML' k.1) j =
                    Limits.Sigma.ι (fun k : AttachIndex ML nD => ML k.1) j ≫
                      attachMap ML ML' iL nD := by
                    dsimp [j, iL]
                    rw [attachMap, Limits.Sigma.ι_comp_desc]
                  rw [← Category.assoc, ← Category.assoc]
                  exact congrArg
                    (fun k => k ≫ pushout.inr (sourceToObject ML nD)
                      (attachMap ML ML' iL nD)) hι
        _ = Limits.Sigma.ι (fun k : AttachIndex ML nD => ML k.1) j ≫
              sourceToObject ML nD ≫
                pushout.inl (sourceToObject ML nD) (attachMap ML ML' iL nD) := by
                  rw [pushout.condition]
        _ = E.functor.map f ≫
              pushout.inl (sourceToObject ML nD) (attachMap ML ML' iL nD) := by
                  simp [j, sourceToObject]
    change i r ≫ E.unit.app (M' r) ≫ E.inverse.map d =
      f ≫ E.unit.app N ≫
        E.inverse.map (attachedInclusion ML ML' iL nD)
    have hmap := congrArg (fun k => E.inverse.map k) hd
    exact hmap

end SheafOfModules.DifferentialGradedModule
