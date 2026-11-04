module

public import StacksFrontier.RingTheory.MilnorPatching.ProjectiveModules
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback

open ModuleGlueing
/-!
# Compatible pairs of finite projective modules over a ring fibre product

Let `B' = B ×_A A'` with `A' → A` surjective. Milnor patching says extension of scalars is an
equivalence from `B'`-modules onto compatible pairs, and restricts to an equivalence between the
finite projective objects on both sides. This file records the two consequences a deformation
problem uses: the module of compatible pairs attached to a pair of finite projective modules is
itself finite projective over `B'`, and its two extensions of scalars are canonically the two
given modules, by an identification computing the image of `1 ⊗ p` as the two components of `p`.

## Main definitions

* `Deformation.Examples.ringFibreProductFst` and `Deformation.Examples.ringFibreProductSnd`:
  the two projections of the fibre product, at the type of the fibre product.

## Main results

* `Deformation.Examples.ringFibreProduct_comm`: the fibre-product square commutes.
* `Deformation.Examples.exists_finiteProjectivePatch_iso`: a compatible pair of finite
  projective modules is, up to isomorphism, the image of a finite projective module over the
  fibre product.
* `Deformation.Examples.compatiblePairsModule_finiteProjective`: the module of compatible pairs
  is finite projective over the fibre product.
* `Deformation.Examples.exists_compatiblePairsModule_baseChangeEquiv`: its two extensions of
  scalars are the two components of the pair, with `1 ⊗ p` going to the two components of `p`.

## Implementation notes

The point of `ringFibreProductFst` and `ringFibreProductSnd` is the *type* they are stated at.
The projections of the canonical cone have domain `↑s.pullbackCone.pt`, which is the fibre product
only after `CommRingCat.pullbackCone` unfolds; so a module structure over the fibre product is
not found for a construction whose base ring was inferred from the cone. Naming the two
projections at the ascribed type `s.fibreProduct →+* _` fixes the base ring once, and every
construction below is formed from them.

## References

* [Stacks Project, Tag 07RU](https://stacks.math.columbia.edu/tag/07RU)
* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

namespace Deformation.Examples

universe u

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
  {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}

/-- The first projection of a ring fibre product, at the type of the fibre product. -/
public abbrev ringFibreProductFst (s : RingFibreProduct.Situation toBase surjection I) :
    s.fibreProduct →+* B :=
  s.pullbackCone.fst.hom

/-- The second projection of a ring fibre product, at the type of the fibre product. -/
public abbrev ringFibreProductSnd (s : RingFibreProduct.Situation toBase surjection I) :
    s.fibreProduct →+* A' :=
  s.pullbackCone.snd.hom

/-- The defining square of a ring fibre product commutes. -/
public theorem ringFibreProduct_comm (s : RingFibreProduct.Situation toBase surjection I) :
    toBase.comp (ringFibreProductFst s) = surjection.comp (ringFibreProductSnd s) :=
  congrArg CommRingCat.Hom.hom s.pullbackCone.condition

variable (toBase surjection I)

/-- A compatible pair whose two components are finite projective is isomorphic to the image
under extension of scalars of a finite projective module over the fibre product. -/
public theorem exists_finiteProjectivePatch_iso
    (s : RingFibreProduct.Situation toBase surjection I)
    (X : CategoricalPullback
      (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection))
    (hX : (Module.Finite B X.fst ∧ Module.Projective B X.fst) ∧
      (Module.Finite A' X.snd ∧ Module.Projective A' X.snd)) :
    ∃ L : ModuleCat.{u} s.fibreProduct,
      Module.Finite s.fibreProduct L ∧ Module.Projective s.fibreProduct L ∧
        Nonempty
          ((ModuleGlueing.extensionOfScalarsToPullback (ringFibreProductFst s)
            (ringFibreProductSnd s) toBase surjection (ringFibreProduct_comm s)).obj L ≅ X) := by
  classical
  let P : ObjectProperty (ModuleCat.{u} s.fibreProduct) := fun L ↦
    Module.Finite s.fibreProduct L ∧ Module.Projective s.fibreProduct L
  let Q : ObjectProperty
      (CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
        (ModuleCat.extendScalars.{u, u, u} surjection)) := fun Y ↦
    (Module.Finite B Y.fst ∧ Module.Projective B Y.fst) ∧
      (Module.Finite A' Y.snd ∧ Module.Projective A' Y.snd)
  obtain ⟨q, ⟨hNat⟩⟩ :=
    MilnorPatching.finiteProjectiveModulesEquivalenceOverFibreProduct toBase surjection I s
  let X' : Q.FullSubcategory := ⟨X, hX⟩
  let L' : P.FullSubcategory := q.inverse.obj X'
  exact ⟨L'.obj, L'.property.1, L'.property.2,
    ⟨hNat.app L' ≪≫ Q.ι.mapIso (q.counitIso.app X')⟩⟩

/-- The module of compatible pairs attached to a pair of finite projective modules is finite
projective over the fibre product. -/
public theorem compatiblePairsModule_finiteProjective
    (s : RingFibreProduct.Situation toBase surjection I)
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection))
    (hX : (Module.Finite B X.fst ∧ Module.Projective B X.fst) ∧
      (Module.Finite A' X.snd ∧ Module.Projective A' X.snd)) :
    Module.Finite s.fibreProduct
      (MilnorPatching.compatiblePairsModule (ringFibreProductFst s) (ringFibreProductSnd s)
        toBase surjection (ringFibreProduct_comm s) X) ∧
    Module.Projective s.fibreProduct
      (MilnorPatching.compatiblePairsModule (ringFibreProductFst s) (ringFibreProductSnd s)
        toBase surjection (ringFibreProduct_comm s) X) := by
  classical
  obtain ⟨L, hLf, hLp, ⟨i⟩⟩ :=
    exists_finiteProjectivePatch_iso toBase surjection I s X hX
  have : Module.Flat s.fibreProduct L := Module.Flat.of_projective
  obtain ⟨F, e, adj, _, _⟩ :=
    MilnorPatching.exists_rightAdjoint_extensionOfScalarsToPullback
      (ringFibreProductFst s) (ringFibreProductSnd s) toBase surjection (ringFibreProduct_comm s)
  obtain ⟨F₀, _, adj₀, _, _, _, hunit, _⟩ :=
    MilnorPatching.flatModulesEquivalenceOverFibreProduct toBase surjection I s
  have := hunit L inferInstance
  let j : L ≅ F.obj X := asIso (adj₀.unit.app L) ≪≫
    F₀.mapIso i ≪≫ (adj₀.rightAdjointUniq adj).app X
  let j' : L ≃ₗ[s.fibreProduct] _ :=
    (j.toLinearEquiv : L ≃ₗ[s.fibreProduct] F.obj X).trans (e X)
  exact ⟨Module.Finite.equiv j', Module.Projective.of_equiv j'⟩

/-- The two extensions of scalars of the module of compatible pairs are the two components of
the pair, by identifications sending `1 ⊗ p` to `p.1` and to `p.2`. -/
public theorem exists_compatiblePairsModule_baseChangeEquiv
    (s : RingFibreProduct.Situation toBase surjection I)
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection)) :
    let R := s.fibreProduct
    let P := MilnorPatching.compatiblePairsModule (ringFibreProductFst s) (ringFibreProductSnd s)
      toBase surjection (ringFibreProduct_comm s) X
    letI : Algebra R B := (ringFibreProductFst s).toAlgebra
    letI : Algebra R A' := (ringFibreProductSnd s).toAlgebra
    ∃ (e₁ : TensorProduct R B P ≃ₗ[B] X.fst)
      (e₂ : TensorProduct R A' P ≃ₗ[A'] X.snd),
      ∀ p : P, e₁ (1 ⊗ₜ[R] p) = p.1.1 ∧ e₂ (1 ⊗ₜ[R] p) = p.1.2 := by
  let R := s.fibreProduct
  let P := MilnorPatching.compatiblePairsModule (ringFibreProductFst s) (ringFibreProductSnd s)
    toBase surjection (ringFibreProduct_comm s) X
  let : Algebra R B := (ringFibreProductFst s).toAlgebra
  let : Algebra R A' := (ringFibreProductSnd s).toAlgebra
  obtain ⟨F, e, adj, _, he⟩ :=
    MilnorPatching.exists_rightAdjoint_extensionOfScalarsToPullback
      (ringFibreProductFst s) (ringFibreProductSnd s) toBase surjection (ringFibreProduct_comm s)
  obtain ⟨F₀, _, adj₀, _, hc⟩ :=
    MilnorPatching.compatiblePairsRightAdjoint_counit_isIso toBase surjection I s
  have : IsIso adj₀.counit := hc
  let E := ModuleGlueing.extensionOfScalarsToPullback (ringFibreProductFst s)
    (ringFibreProductSnd s) toBase surjection (ringFibreProduct_comm s)
  have : IsIso (adj.counit.app X) := by
    apply (isIso_comp_left_iff (E.map ((adj₀.rightAdjointUniq adj).hom.app X))
      (adj.counit.app X)).mp
    rw [adj₀.rightAdjointUniq_hom_app_counit adj X]
    infer_instance
  let c₁ := ((CategoricalPullback.π₁ _ _).mapIso (asIso (adj.counit.app X))).toLinearEquiv
  let c₂ := ((CategoricalPullback.π₂ _ _).mapIso (asIso (adj.counit.app X))).toLinearEquiv
  refine ⟨(LinearEquiv.baseChange R B P (F.obj X) (e X).symm).trans c₁,
    (LinearEquiv.baseChange R A' P (F.obj X) (e X).symm).trans c₂, fun p ↦ ?_⟩
  have hh := he (F.obj X) X (𝟙 (F.obj X)) ((e X).symm p)
  have hi : (adj.homEquiv (F.obj X) X).symm (𝟙 (F.obj X)) = adj.counit.app X := by
    simp [adj.homEquiv_counit]
  simp only [hi, ModuleCat.id_apply, LinearEquiv.apply_symm_apply] at hh
  exact ⟨hh.1.symm, hh.2.symm⟩

end Deformation.Examples
