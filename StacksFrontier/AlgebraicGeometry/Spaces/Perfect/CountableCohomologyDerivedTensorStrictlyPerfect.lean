module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableCohomologyQcqsEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes

/-!
# Countable cohomology after tensoring with a strictly perfect complex

Let `X` be a quasi-compact quasi-separated algebraic space and let `K` be an object of `D(𝒪_X)`
whose cohomology sheaves are quasi-coherent with countable sets of sections over the affine
schemes étale over `X`.  Then for every quasi-compact quasi-separated `U` étale over `X` and
every strictly perfect complex `P` of `𝒪_X`-modules the groups `H^i(U, (K ⊗^𝐋 P)|_U)` are
countable.  The dévissage is on the stupid truncations of `P`: tensoring with `K` and taking
derived sections over `U` are exact, and countability of cohomology in `D(Ab)` is stable under
the resulting triangles, shifts, retracts and finite direct sums.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AddCommGrpCat (HasCountableCohomology)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-! ### Countable cohomology in the derived category of abelian groups -/

section DerivedAb

/-- **Countable cohomology is inherited by the shifts.**  `H^i(E⟦n⟧)` is `H^{n+i}(E)`. -/
theorem hasCountableCohomology_shift {E : DerivedCategory AddCommGrpCat.{u + 1}}
    (h : HasCountableCohomology E) (n : ℤ) : HasCountableCohomology (E⟦n⟧) := fun i =>
  have := h (n + i)
  Countable.of_equiv _ ((Functor.ShiftSequence.shiftIso
    (F := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0) n i (n + i) rfl).app
      E |>.addCommGroupIsoToAddEquiv.toEquiv.symm)

/-- **A zero object of `D(Ab)` has countable cohomology.** -/
theorem hasCountableCohomology_of_isZero {E : DerivedCategory AddCommGrpCat.{u + 1}}
    (h : IsZero E) : HasCountableCohomology E := fun _q =>
  AddCommGrpCat.isCountable.prop_of_isZero (Functor.map_isZero _ h)

/-- **Countable cohomology passes to retracts**: a retract of `H^q(F)` is a subobject of it. -/
theorem hasCountableCohomology_of_retract {E F : DerivedCategory AddCommGrpCat.{u + 1}}
    (r : Retract E F) (hF : HasCountableCohomology F) : HasCountableCohomology E := fun q => by
  have hr := r.map (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q)
  have : IsSplitMono hr.i := ⟨⟨hr.r, hr.retract⟩⟩
  exact AddCommGrpCat.isCountable.prop_of_mono hr.i (hF q)

/-- **Countable cohomology is inherited by a finite direct sum**: `H^q` commutes with finite
biproducts, and a finite product of countable abelian groups is countable. -/
theorem hasCountableCohomology_biproduct {J : Type} [Finite J]
    (E : J → DerivedCategory AddCommGrpCat.{u + 1})
    (h : ∀ j, HasCountableCohomology (E j)) : HasCountableCohomology (⨁ E) := fun q => by
  let F := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q
  have : ∀ j, Countable ((F.obj ∘ E) j) := fun j => h j q
  exact Countable.of_equiv (∀ j, (F.obj ∘ E) j)
    ((F.mapBiproduct E ≪≫
      AddCommGrpCat.biproductIsoPi _).addCommGroupIsoToAddEquiv.toEquiv.symm)

end DerivedAb

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] isGrothendieckAbelian_modules

/-- **Derived global sections of an algebraic space are exact.**  They are a right derived
functor of the degreewise global sections followed by localization, and the `𝒪_Y`-modules admit
K-injective resolutions. -/
local instance isTriangulatedDerivedGlobalSectionsAb (Y : AlgebraicSpaces B S hS) :
    (derivedGlobalSectionsAb B S hS Y).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2) _ _
    (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit (globalSectionsAb B S hS Y))

variable {X : AlgebraicSpaces B S hS}

/-- **`RΓ(U, (-)|_U)`**: restriction to an algebraic space `U` étale over `X`, followed by
derived global sections there, read in abelian groups. -/
abbrev derivedGlobalSectionsAbRestrict (U : SpacesEtale B S hS X) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory ⋙
    derivedGlobalSectionsAb B S hS U.1.left

/-- **Countable cohomology over every quasi-compact quasi-separated étale object.**  The
property of an object `L` of `D(𝒪_X)` that `H^i(U, L|_U)` is countable for every quasi-compact
quasi-separated `U` étale over `X` and every `i`.  This is the conclusion of Stacks 0CRU, read
as a property of `L`. -/
def HasCountableQcqsEtaleCohomology (hZ : B.Contains (⊤_ Scheme.{u}))
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  ∀ U : SpacesEtale B S hS X, IsQuasiCompactSpace B S hS U.1.left.1 →
    IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1 →
      HasCountableCohomology ((derivedGlobalSectionsAbRestrict B S hS U).obj L)

namespace HasCountableQcqsEtaleCohomology

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})}
  {L L' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}

/-- Countable cohomology over the quasi-compact quasi-separated étale objects is invariant under
isomorphism in `D(𝒪_X)`. -/
theorem of_iso (e : L ≅ L') (h : HasCountableQcqsEtaleCohomology B S hS hZ L) :
    HasCountableQcqsEtaleCohomology B S hS hZ L' := fun U hqc hqs =>
  (h U hqc hqs).of_iso ((derivedGlobalSectionsAbRestrict B S hS U).mapIso e)

/-- A zero object of `D(𝒪_X)` has countable cohomology over every object. -/
theorem of_isZero (h : IsZero L) : HasCountableQcqsEtaleCohomology B S hS hZ L :=
  fun _ _ _ => hasCountableCohomology_of_isZero (Functor.map_isZero _ h)

/-- Countable cohomology over the quasi-compact quasi-separated étale objects is inherited by the
shifts, restriction and derived global sections both commuting with the shift. -/
theorem shift (h : HasCountableQcqsEtaleCohomology B S hS hZ L) (n : ℤ) :
    HasCountableQcqsEtaleCohomology B S hS hZ (L⟦n⟧) := fun U hqc hqs =>
  (hasCountableCohomology_shift (h U hqc hqs) n).of_iso
    (((derivedGlobalSectionsAbRestrict B S hS U).commShiftIso n).app L).symm

/-- Countable cohomology over the quasi-compact quasi-separated étale objects passes to
retracts. -/
theorem of_retract (r : Retract L L') (h : HasCountableQcqsEtaleCohomology B S hS hZ L') :
    HasCountableQcqsEtaleCohomology B S hS hZ L := fun U hqc hqs =>
  hasCountableCohomology_of_retract (r.map (derivedGlobalSectionsAbRestrict B S hS U))
    (h U hqc hqs)

/-- Countable cohomology over the quasi-compact quasi-separated étale objects is inherited by a
finite direct sum. -/
theorem biproduct {J : Type} [Finite J]
    (G : J → DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (h : ∀ j, HasCountableQcqsEtaleCohomology B S hS hZ (G j)) :
    HasCountableQcqsEtaleCohomology B S hS hZ (⨁ G) := fun U hqc hqs =>
  (hasCountableCohomology_biproduct _ fun j => h j U hqc hqs).of_iso
    ((derivedGlobalSectionsAbRestrict B S hS U).mapBiproduct G).symm

/-- **The two out of three property.**  For a distinguished triangle of `D(𝒪_X)`, countable
cohomology over the quasi-compact quasi-separated étale objects at the outer two vertices gives
it at the middle one: restriction and derived global sections are exact, and countability in
`D(Ab)` is two out of three along a distinguished triangle. -/
theorem obj₂ (Δ : Triangle (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)))
    (hΔ : Δ ∈ distTriang _) (h₁ : HasCountableQcqsEtaleCohomology B S hS hZ Δ.obj₁)
    (h₃ : HasCountableQcqsEtaleCohomology B S hS hZ Δ.obj₃) :
    HasCountableQcqsEtaleCohomology B S hS hZ Δ.obj₂ := fun U hqc hqs =>
  AddCommGrpCat.HasCountableCohomology.obj₂ _
    ((derivedGlobalSectionsAbRestrict B S hS U).map_distinguished Δ hΔ)
    (h₁ U hqc hqs) (h₃ U hqc hqs)

end HasCountableQcqsEtaleCohomology

/-! ### The dévissage -/

section Tensor

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).Additive]
  [∀ K L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ,
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O) (ComplexShape.up ℤ)]

/-- **An `𝒪_X`-module placed in a degree is a shift of it placed in degree zero**:
`M[0]⟦-i⟧ ≅ M[i]`.  This is the shift datum of `DerivedCategory.singleFunctors`. -/
def singleShiftIso (M : Modules.{u, u} B S hS X.1 X.2) (i : ℤ) :
    ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M)⟦-i⟧ ≅
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj M :=
  ((DerivedCategory.singleFunctors (Modules.{u, u} B S hS X.1 X.2)).shiftIso
    (-i) i 0 (by omega)).app M

/-- **`K ⊗^𝐋 𝒪_X[i]` is `K⟦-i⟧`.**  The structure sheaf in degree zero is a unit for the derived
tensor product, and tensoring with `K` commutes with the shift. -/
def derivedTensorSingleUnitIso
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (i : ℤ) :
    (T.tensor.obj K).obj ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≅
      K⟦-i⟧ :=
  (T.tensor.obj K).mapIso (singleShiftIso B S hS _ i).symm ≪≫
    ((T.tensor.obj K).commShiftIso (-i)).app _ ≪≫
    (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (-i)).mapIso (T.unitIso K)

/-- **The dévissage of the cohomology clause of Stacks 0CRU to the structure sheaf.**  If
`H^i(U, K|_U)` is countable for every quasi-compact quasi-separated `U` étale over `X`, then so
is `H^i(U, (K ⊗^𝐋 P)|_U)` for every strictly perfect complex `P` of `𝒪_X`-modules.

The induction is on the stupid truncations of `P`: it is bounded, each of its terms is a retract
of a finite direct sum of copies of `𝒪_X`, and the extension step is the distinguished triangle
of a short exact sequence of complexes, carried along by the exactness of `K ⊗^𝐋 -` and of
derived sections. -/
theorem hasCountableQcqsEtaleCohomology_derivedTensor_of_isStrictlyPerfect
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : HasCountableQcqsEtaleCohomology B S hS hZ K)
    (P : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hP : IsStrictlyPerfect
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) P) :
    HasCountableQcqsEtaleCohomology B S hS hZ
      ((T.tensor.obj K).obj (DerivedCategory.Q.obj P)) := by
  classical
  refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex
    (fun A => HasCountableQcqsEtaleCohomology B S hS hZ ((T.tensor.obj K).obj A))
    (fun e h => h.of_iso ((T.tensor.obj K).mapIso e))
    (fun A hA => .of_isZero (Functor.map_isZero _ hA)) ?_ P hP.bounded ?_
  · intro Sc hSc h₁ h₃
    exact HasCountableQcqsEtaleCohomology.obj₂ _
      ((T.tensor.obj K).map_distinguished _
        (DerivedCategory.triangleOfSES_distinguished hSc)) h₁ h₃
  · intro i
    obtain ⟨m, ⟨r⟩⟩ :=
      (Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_iff_retract_biproduct
        (smallEtaleRingedSite B S hS X.1 X.2).O (P.X i)).mp (hP.termDirectSummand i)
    let Ψ := DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) i ⋙
      T.tensor.obj K
    refine HasCountableQcqsEtaleCohomology.of_retract (r.map Ψ) ?_
    refine HasCountableQcqsEtaleCohomology.of_iso (Ψ.mapBiproduct _).symm ?_
    exact HasCountableQcqsEtaleCohomology.biproduct _ fun _ =>
      HasCountableQcqsEtaleCohomology.of_iso
        (derivedTensorSingleUnitIso B S hS T K i).symm (hK.shift (-i))

/-- **The cohomology clause of Stacks 0CRU for a strictly perfect complex.**  Let `X` be an
algebraic space and `K` an object of `D(𝒪_X)` whose cohomology
sheaves are quasi-coherent and have countable sets of sections over the affine schemes étale
over `X`.  Then `H^i(U, (K ⊗^𝐋 P)|_U)` is countable for every quasi-compact quasi-separated `U`
étale over `X`, every `i`, and every strictly perfect complex `P` of `𝒪_X`-modules.

The hypothesis on `K` is carried to `K ⊗^𝐋 P` by
`AlgebraicGeometry.Space.hasCountableQcqsEtaleCohomology_derivedTensor_of_isStrictlyPerfect`,
whose base case is
`AlgebraicGeometry.Space.hasCountableCohomology_derivedGlobalSectionsAb_restrict`. -/
theorem hasCountableCohomology_derivedTensor_restrict_of_isStrictlyPerfect
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj K).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj K).val.obj (Opposite.op v)))
    (P : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hP : IsStrictlyPerfect
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) P)
    (U : SpacesEtale B S hS X) (hUqc : IsQuasiCompactSpace B S hS U.1.left.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1) :
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS U.1.left).obj
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj
        ((T.tensor.obj K).obj (DerivedCategory.Q.obj P)))) :=
  hasCountableQcqsEtaleCohomology_derivedTensor_of_isStrictlyPerfect B S hS hZ T K
    (fun V hVqc hVqs => hasCountableCohomology_derivedGlobalSectionsAb_restrict B S hS hZ X
      K hqc hcount V hVqc hVqs) P hP U hUqc hUqs

/-- **The cohomology clause of Stacks 0CRU for an object of `D(𝒪_X)` with a global strictly
perfect model.**  Same statement as
`AlgebraicGeometry.Space.hasCountableCohomology_derivedTensor_restrict_of_isStrictlyPerfect`,
read at an object `E` of `D(𝒪_X)` isomorphic to a strictly perfect complex rather than at the
complex itself. -/
theorem hasCountableCohomology_derivedTensor_restrict_of_exists_strictlyPerfectModel
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj K).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj K).val.obj (Opposite.op v)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∃ P : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ,
      IsStrictlyPerfect
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ E))
    (U : SpacesEtale B S hS X) (hUqc : IsQuasiCompactSpace B S hS U.1.left.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1) :
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS U.1.left).obj
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj
        ((T.tensor.obj K).obj E))) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  exact HasCountableQcqsEtaleCohomology.of_iso ((T.tensor.obj K).mapIso e)
    (fun V hVqc hVqs => hasCountableCohomology_derivedTensor_restrict_of_isStrictlyPerfect B S hS
      hZ T K hqc hcount P hP V hVqc hVqs) U hUqc hUqs

end Tensor

end AlgebraicGeometry.Space

end
