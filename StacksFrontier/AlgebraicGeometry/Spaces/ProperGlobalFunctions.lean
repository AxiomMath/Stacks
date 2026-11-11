module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase

/-!
# Global functions of a proper algebraic space over a field

Let `k` be a field and let `X` be a proper algebraic space over `k`.  Tag 0DMY describes the
ring `A = H⁰(X, 𝒪_X)` of global regular functions of `X`: it is a finite dimensional
`k`-algebra, it splits as a finite product of Artinian local `k`-algebras indexed by the
connected components of `|X|`, and when `X` is reduced each factor is a field finite over `k`.

The splitting itself is `AlgebraicGeometry.Space.ComponentwiseArtinianFactorization`, built in
`StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra` from finiteness of the set of
connected components and artinianness of the whole ring of global functions, and restated in
`StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPointSpace` with the first of those two
discharged.  What this file adds is the reduction of the second, finite dimensionality of `A`,
to finiteness of the cohomology of coherent modules ([Stacks, Tag 08AS], used in degree zero for
the structure sheaf), and the three consequences of it.  The complete statement of
Tag 0DMY, with finite dimensionality of `A` proved outright, is registered in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFinite` (parts (1) to (3)) and
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsGeometric` (parts (4) to (8)).

Four things are needed to run [Stacks, Tag 08AS] at the structure sheaf and are provided here.
The structure sheaf has to be presented as an `𝒪_X`-module in the module universe of
`AlgebraicGeometry.Space.cohomologyOverBase`, which is
`AlgebraicGeometry.Space.structureModuleLarge`; it has to be coherent there, which it is because it
is finite locally free; its degree-zero cohomology over the base ring has to be identified
`k`-linearly with `AlgebraicGeometry.Space.globalFunctions`, which is
`AlgebraicGeometry.Space.cohomologyZeroStructureModuleLinearEquiv`; and `X` has to be
quasi-compact and locally Noetherian, which properness over an affine base supplies.

## Main definitions

* `AlgebraicGeometry.Space.structureModuleLarge` is the structure sheaf of an algebraic space as an
  `𝒪_X`-module in the module universe of `AlgebraicGeometry.Space.cohomologyOverBase`.
* `AlgebraicGeometry.Space.cohomologyZeroStructureModuleLinearEquiv` identifies its degree-zero
  cohomology over the base ring with the ring of global functions, as base-ring modules.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_structureModuleLarge` and
  `AlgebraicGeometry.Space.isCoherent_structureModuleLarge`: the structure sheaf is finite locally
  free, hence coherent on a locally Noetherian algebraic space.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isProper_baseObject` and
  `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isProper`: a proper
  algebraic space over an affine base is quasi-compact, and is locally Noetherian when the base
  ring is Noetherian.
* `AlgebraicGeometry.Space.finiteDimensional_globalFunctions_of_isProper`: the global functions
  of a proper algebraic space over a field are finite dimensional once the cohomology of coherent
  modules is finite over `k`.
* `AlgebraicGeometry.Space.isArtinianRing_globalFunctions_of_isProper`: that ring is therefore
  Artinian.
* `AlgebraicGeometry.Space.finite_connectedComponents_points_of_isProper`: **Tag 0DMY,
  part (2)**, `|X|` has finitely many connected components.
* `AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization_of_isProper`: the global
  functions split as the product, over those components, of the rings of functions on the charts
  of each, each factor Artinian and local.
* `AlgebraicGeometry.Space.isReduced_componentFunctions` and
  `AlgebraicGeometry.Space.isField_componentFunctions`: **Tag 0DMY, part (3)**, for a reduced
  `X` each factor is reduced, hence a field.
* `AlgebraicGeometry.Space.finiteDimensional_componentFunctions_of_isProper`: each factor is
  finite dimensional over `k`, under the same finiteness hypothesis.

## Implementation notes

**The finiteness hypothesis.**
`AlgebraicGeometry.Space.finiteDimensional_globalFunctions_of_isProper` and the results downstream
of it take as a hypothesis `hcoh` that the cohomology over `k` of
every coherent `𝒪_X`-module, in the module universe of
`AlgebraicGeometry.Space.cohomologyOverBase`, is a finite `k`-module in every degree.  The
hypothesis is not needed for their conclusions: finite dimensionality of `A` is proved
outright, over any Noetherian base ring, as
`AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper` in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.Finiteness` (via finiteness of the
global sections of coherent modules,
`AlgebraicGeometry.Space.moduleFinite_sectionsOverBase_of_isProper`), and
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsFinite` derives parts (1) to (3)
of Tag 0DMY from it.  Tags 04ZK, 04ZF, 04ZL, 00J6, 00KJ and 0BGS, also used here, are all in
the library.

**Universes.**  `AlgebraicGeometry.Space.cohomologyOverBase.{u, w}` is valued in
`ModuleCat.{max (u + 1) w}`, while `AlgebraicGeometry.Space.globalFunctions` lies in
`Type (u + 1)`;  the two meet at `w := u`, and that is the instantiation used throughout.  The
module universe of `AlgebraicGeometry.Space.structureModuleLarge` is correspondingly `u + 1`, which
is why `CategoryTheory.SheafOfModules.unit` — whose sections lie in the universe `u` of the
structure rings — cannot serve as the structure sheaf here and
`Stacks.Cohomology.SiteModules.unitULift` is used instead.  For the same reason
`AlgebraicGeometry.Space.isCoherent_structureSheaf`, which is Tag 07UB for
`CategoryTheory.SheafOfModules.unit`, does not apply, and coherence is obtained afresh from
finite local freeness.

**Finite dimensionality.**  "Finite dimensional over `k`" is written `Module.Finite k`, which is
the definition of `FiniteDimensional k`, rather than `FiniteDimensional k` itself.  The reason is
syntactic: `FiniteDimensional` takes its `AddCommGroup` instance before its `Module` instance,
and on the ring of global functions — a subring of a product of rings of sections — instance
search picks for the former a path that does not match the `AddCommMonoid` underlying the
`Module` that `AlgebraicGeometry.Space.globalFunctionsAlgebra` supplies, so the elaborated
statement has no instance.  `Module.Finite` takes the `AddCommMonoid` from the `Module`, and
elaborates.

**The product decomposition.**  Part (2) is asserted as nonemptiness of
`AlgebraicGeometry.Space.ComponentwiseArtinianFactorization`, the structure that pins the
equivalence to be simultaneous restriction to the components;  part (3) takes such a
factorization as an argument where its statement has to mention the base-field algebra
structure of a factor, which is the one restriction induces and which that structure carries.
Reducedness of a factor is read off the product through `Pi.single`: a nilpotent element of one
factor is a nilpotent element of the product, which is reduced because the global functions
are, by Tag 0BGS.

**Parts (4) to (8).**  Parts (4) to (8) of Tag 0DMY — separability of the factors for a
geometrically reduced `X`, geometric irreducibility of `A` for a geometrically connected or
geometrically irreducible `X`, and `A = k` for a geometrically reduced and geometrically
connected, or geometrically integral, `X` — are not stated here; they are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsGeometric`.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 00KJ](https://stacks.math.columbia.edu/tag/00KJ)
* [Stacks Project, Tag 0BGS](https://stacks.math.columbia.edu/tag/0BGS)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The structure sheaf in the module universe of cohomology -/

section StructureModule

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- The structure sheaf `𝒪_X` of an algebraic space over `Spec A`, as an `𝒪_X`-module in the
module universe `u + 1` of `AlgebraicGeometry.Space.cohomologyOverBase.{u, u}`.

`CategoryTheory.SheafOfModules.unit` puts the module sections in the universe `u` of the
structure rings, which is not the module universe of cohomology on the small étale site of an
algebraic space over a `Scheme.{u}`;  this is `Stacks.Cohomology.SiteModules.unitULift`, the
same module with its sections lifted. -/
abbrev structureModuleLarge : Modules.{u, u + 1} B (Spec (.of A)) hA X hX :=
  Stacks.Cohomology.SiteModules.unitULift.{u + 1, u, u, u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))

/-- **The structure sheaf is finite locally free.**  Every étale chart is covered by itself, and
over a chart the structure sheaf is free of rank one on itself — the lift of its sections being
undone by `ULift.moduleEquiv`.

Free of rank one is the colimit of the one-object cofan on the restricted structure sheaf,
whose universal property is checked by case analysis on `Fin 1`. -/
theorem isFiniteLocallyFreeOnSite_structureModuleLarge :
    SheafOfModules.IsFiniteLocallyFreeOnSite (structureModuleLarge A B hA X hX) := by
  intro U
  refine ⟨PUnit, (fun _ => U), (fun _ => 𝟙 U), ?_, ?_⟩
  · apply (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J.superset_covering (S := ⊤)
    · intro V g _
      exact (Sieve.ofArrows (fun _ : PUnit => U) (fun _ => 𝟙 U)).downward_closed
        (Sieve.ofArrows_mk (fun _ : PUnit => U) (fun _ => 𝟙 U) PUnit.unit) g
    · exact (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J.top_mem U
  · intro _
    let N := SheafOfModules.unit
      (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X
          hX).O)).over U)
    have hN : IsColimit (Cofan.mk N (fun _ : Fin 1 => 𝟙 N)) := by
      refine Cofan.IsColimit.mk _ (fun s => s.inj 0) ?_ ?_
      · intro s j
        exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
      · intro s m hm
        simpa using hm 0
    exact ⟨1, N, (fun _ => 𝟙 N), ⟨hN⟩, (fun _ => ULift.moduleEquiv.symm), fun _ _ => rfl⟩

/-- **The structure sheaf of a locally Noetherian algebraic space is coherent**, in the module
universe of cohomology.  This is Tag 07UB for a finite locally free module, applied to
`AlgebraicGeometry.Space.structureModuleLarge`.

`AlgebraicGeometry.Space.isCoherent_structureSheaf` is the same assertion for
`CategoryTheory.SheafOfModules.unit`, at module universe `u`, and does not apply here. -/
theorem isCoherent_structureModuleLarge
    (hN : HasEtaleLocalProperty B (Spec (.of A)) hA X
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsCoherent B (Spec (.of A)) hA X hX (structureModuleLarge A B hA X hX) :=
  have : Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X
    (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hN⟩
  isCoherent_of_isFiniteLocallyFreeOnSite _
    (isFiniteLocallyFreeOnSite_structureModuleLarge A B hA X hX)

/-- **Degree-zero cohomology of the structure sheaf over the base ring is the ring of global
functions.**  For an algebraic space `X` over `Spec A` the `A`-module
`H⁰(X, 𝒪_X) = AlgebraicGeometry.Space.cohomologyOverBase ... 0` is the ring
`AlgebraicGeometry.Space.globalFunctions` of compatible families of regular functions on the
étale charts, with its `A`-algebra structure.

This is `Stacks.Cohomology.SiteModules.cohomologyZeroUnitLinearEquiv` for the small étale
ringed site of `X`, read `A`-linearly:  the two carriers agree because
`AlgebraicGeometry.Space.globalFunctions` and
`Stacks.Cohomology.SiteModules.GlobalSectionRing` of the ring sheaf of that site are the same
subring of `∀ U, Γ(U, 𝒪_U)`, and the `A`-action is in both cases the one of
`AlgebraicGeometry.Space.baseRingHom`, which is
`AlgebraicGeometry.Space.baseToGlobalFunctions`. -/
def cohomologyZeroStructureModuleLinearEquiv :
    cohomologyOverBase.{u, u} A B hA X hX (structureModuleLarge A B hA X hX) 0 ≃ₗ[A]
      globalFunctions B (Spec (.of A)) hA X :=
  let E := Stacks.Cohomology.SiteModules.cohomologyZeroUnitLinearEquiv.{u + 1, u, u, u + 1}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
  { toFun := E
    invFun := E.symm
    left_inv := E.left_inv
    right_inv := E.right_inv
    map_add' := E.map_add
    map_smul' := fun a x => E.map_smul (baseRingHom A B hA X hX a) x }

end StructureModule

/-! ### Quasi-compactness and local Noetherianity of a proper algebraic space -/

section ProperOverAffine

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseObject A B hA))

/-- The base `Spec A` of a Noetherian ring, read as an algebraic space over itself, is locally
Noetherian:  it is representable, so Tag 03E6 reduces the question to the scheme `Spec A`. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_baseObject [IsNoetherianRing A] :
    HasEtaleLocalProperty B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  (exists_atlas_iff_of_representable B (Spec (.of A)) hA
    (yoneda.obj (baseObject A B hA)) (fun T : Scheme.{u} => IsLocallyNoetherian T)
    (baseObject A B hA) (Iso.refl _)).2
    ((AlgebraicGeometry.isLocallyNoetherian_Spec (R := .of A)).2 inferInstance)

include hX

/-- **A proper algebraic space over an affine base is quasi-compact.**  Properness contains
universal closedness, and the base `Spec A`, read as the terminal object of the big fppf
category over itself, is affine, so this is
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_universallyClosed_of_isAffine`. -/
theorem isQuasiCompactSpace_of_isProper_baseObject (hf : IsProper B (Spec (.of A)) hA f) :
    IsQuasiCompactSpace B (Spec (.of A)) hA X :=
  isQuasiCompactSpace_of_universallyClosed_of_isAffine B (Spec (.of A)) hA
    (baseObject A B hA) (inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))) hX
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) f
    hf.universallyClosed

/-- **A proper algebraic space over the spectrum of a Noetherian ring is locally Noetherian.**
This is Tag 04ZK, the base being locally Noetherian by
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_baseObject` and the
morphism being locally of finite type because it is proper. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isProper [IsNoetherianRing A]
    (hf : IsProper B (Spec (.of A)) hA f) :
    HasEtaleLocalProperty B (Spec (.of A)) hA X
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of A)) hA hX
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) f
    hf.isFiniteType.1
    (hasEtaleLocalProperty_isLocallyNoetherian_baseObject A B hA)

end ProperOverAffine

/-! ### Tag 0DMY -/

section Field

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- The global regular functions of a proper algebraic space `X` over a field `k` form a finite
dimensional `k`-algebra, given that the cohomology over `k` of every coherent `𝒪_X`-module is a
finite `k`-module in every degree (the hypothesis `hcoh`).  The conclusion holds without `hcoh`:
it is `AlgebraicGeometry.Space.moduleFinite_globalFunctions_of_isProper`, part (1) of Tag 0DMY.

Properness makes `X` locally Noetherian over `k`, so the structure sheaf is a coherent
`𝒪_X`-module by `AlgebraicGeometry.Space.isCoherent_structureModuleLarge`, and its degree-zero
cohomology over `k` is the ring of global functions by
`AlgebraicGeometry.Space.cohomologyZeroStructureModuleLinearEquiv`. -/
theorem finiteDimensional_globalFunctions_of_isProper (hf : IsProper B (Spec (.of k)) hS f)
    (hcoh : ∀ M : Modules.{u, u + 1} B (Spec (.of k)) hS X hX,
      IsCoherent B (Spec (.of k)) hS X hX M → ∀ i : ℕ,
        Module.Finite k (cohomologyOverBase.{u, u} k B hS X hX M i)) :
    Module.Finite k (globalFunctions B (Spec (.of k)) hS X) :=
  have := hcoh (structureModuleLarge k B hS X hX)
    (isCoherent_structureModuleLarge k B hS X hX
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hS X hX f hf)) 0
  Module.Finite.equiv (cohomologyZeroStructureModuleLinearEquiv k B hS X hX)

/-- The ring of global regular functions of a proper algebraic space over a field is Artinian:
it is a finite dimensional `k`-algebra by
`AlgebraicGeometry.Space.finiteDimensional_globalFunctions_of_isProper`, hence Artinian as a
module over `k`, hence over itself.  The same holds without `hcoh`:
`AlgebraicGeometry.Space.isArtinianRing_globalFunctions_of_isProper_of_field`. -/
theorem isArtinianRing_globalFunctions_of_isProper (hf : IsProper B (Spec (.of k)) hS f)
    (hcoh : ∀ M : Modules.{u, u + 1} B (Spec (.of k)) hS X hX,
      IsCoherent B (Spec (.of k)) hS X hX M → ∀ i : ℕ,
        Module.Finite k (cohomologyOverBase.{u, u} k B hS X hX M i)) :
    IsArtinianRing (globalFunctions B (Spec (.of k)) hS X) :=
  have := finiteDimensional_globalFunctions_of_isProper k B hS X hX f hf hcoh
  IsArtinianRing.of_finite k (globalFunctions B (Spec (.of k)) hS X)

/-- **Stacks 0DMY, part (2), the number of factors.**  The point space of a proper algebraic
space over a field has finitely many connected components, so that the product decomposition of
its global regular functions is a finite product.

Properness makes `X` quasi-compact and locally Noetherian through Tags 04ZL and 04ZK, and
Tag 04ZF then makes `|X|` a Noetherian topological space;  a Noetherian space has finitely many
connected components. -/
@[stacks 0DMY "part (2): the product is finite, there being one factor for each of the finitely \
many connected components of the point space"]
theorem finite_connectedComponents_points_of_isProper (hf : IsProper B (Spec (.of k)) hS f) :
    Finite (ConnectedComponents (points B (Spec (.of k)) hS X)) :=
  finite_connectedComponents_points B (Spec (.of k)) hS hX
    (isQuasiCompactSpace_of_isProper_baseObject k B hS X hX f hf)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hS X hX f hf)

/-- The global regular functions of a proper algebraic space over a field split as the product,
over the connected components of its point space, of the rings of functions on the étale charts
lying in each component;  each factor is an Artinian local ring,
and the splitting is simultaneous restriction to the components.  The set of components is
finite by `AlgebraicGeometry.Space.finite_connectedComponents_points_of_isProper`, so the
product is finite.

This is `AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace`
with its remaining hypothesis discharged:  artinianness of the whole ring of global functions
is `AlgebraicGeometry.Space.isArtinianRing_globalFunctions_of_isProper`, which uses `hcoh`.
Without `hcoh` this is
`AlgebraicGeometry.Space.nonempty_componentwiseArtinianFactorization_of_isProper_of_field`,
part (2) of Tag 0DMY.  Quasi-compactness and local Noetherianity of `X` come from properness
through Tags 04ZL and 04ZK, and Tag 04ZF then makes the point space Noetherian, so that the set of
connected components is finite. -/
theorem nonempty_componentwiseArtinianFactorization_of_isProper
    (hf : IsProper B (Spec (.of k)) hS f)
    (hcoh : ∀ M : Modules.{u, u + 1} B (Spec (.of k)) hS X hX,
      IsCoherent B (Spec (.of k)) hS X hX M → ∀ i : ℕ,
        Module.Finite k (cohomologyOverBase.{u, u} k B hS X hX M i)) :
    Nonempty (ComponentwiseArtinianFactorization k B hS X) :=
  nonempty_componentwiseArtinianFactorization_of_isQuasiCompactSpace k B hS X hX
    (isQuasiCompactSpace_of_isProper_baseObject k B hS X hX f hf)
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hS X hX f hf)
    (isArtinianRing_globalFunctions_of_isProper k B hS X hX f hf hcoh)

/-- Each factor of a componentwise factorization of the global functions of a reduced algebraic
space is a reduced ring.

The global functions are reduced by Tag 0BGS, hence so is the product of the factors, and a
nilpotent element of one factor is a nilpotent element of the product through `Pi.single`. -/
theorem isReduced_componentFunctions
    (hred : HasEtaleLocalProperty B (Spec (.of k)) hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    _root_.IsReduced (componentFunctions B (Spec (.of k)) hS X c) := by
  classical
  let (d : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X d) := fac.factorAlgebra d
  have : _root_.IsReduced (globalFunctions B (Spec (.of k)) hS X) :=
    isReduced_globalFunctions B (Spec (.of k)) hS X hX hred
  have hprod : _root_.IsReduced
      (∀ d : ConnectedComponents (points B (Spec (.of k)) hS X),
        componentFunctions B (Spec (.of k)) hS X d) :=
    isReduced_of_injective fac.equivalence.symm.toRingHom fac.equivalence.symm.injective
  refine ⟨fun x ⟨n, hn⟩ => ?_⟩
  have hy : IsNilpotent (Pi.single c x) := by
    refine ⟨n + 1, ?_⟩
    funext d
    by_cases h : d = c
    · subst h
      change (Pi.single d x d) ^ (n + 1) = 0
      rw [Pi.single_eq_same, pow_succ, hn, zero_mul]
    · change (Pi.single c x d) ^ (n + 1) = 0
      rw [Pi.single_eq_of_ne h]
      exact zero_pow (Nat.succ_ne_zero n)
  simpa using congrFun (IsReduced.eq_zero _ hy) c

/-- **Stacks 0DMY, part (3).**  For a reduced algebraic space, each factor of a componentwise
factorization of its global regular functions is a field:  the factor is an Artinian local ring
by the factorization and reduced by
`AlgebraicGeometry.Space.isReduced_componentFunctions`, and a reduced Artinian local ring is a
field. -/
@[stacks 0DMY "part (3): the factors of a reduced space are fields"]
theorem isField_componentFunctions
    (hred : HasEtaleLocalProperty B (Spec (.of k)) hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T))
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    IsField (componentFunctions B (Spec (.of k)) hS X c) :=
  have := fac.isArtinian c
  have := fac.isLocal c
  have := isReduced_componentFunctions k B hS X hX hred fac c
  IsArtinianRing.isField_of_isReduced_of_isLocalRing _

/-- Each factor of a componentwise factorization of the global regular functions of a proper
algebraic space over a field is finite dimensional over that field, given `hcoh` — so that, `X`
being reduced, each factor is a finite field extension of `k`
by `AlgebraicGeometry.Space.isField_componentFunctions`.

The global functions are finite dimensional by
`AlgebraicGeometry.Space.finiteDimensional_globalFunctions_of_isProper`, the factorization makes
the product of the factors `k`-linearly isomorphic to them, and projection onto a factor is a
surjective `k`-linear map.  Reducedness is not used.  Without `hcoh` this is
`AlgebraicGeometry.Space.moduleFinite_componentFunctions_of_isProper`, part (3) of Tag 0DMY. -/
theorem finiteDimensional_componentFunctions_of_isProper (hf : IsProper B (Spec (.of k)) hS f)
    (hcoh : ∀ M : Modules.{u, u + 1} B (Spec (.of k)) hS X hX,
      IsCoherent B (Spec (.of k)) hS X hX M → ∀ i : ℕ,
        Module.Finite k (cohomologyOverBase.{u, u} k B hS X hX M i))
    (fac : ComponentwiseArtinianFactorization k B hS X)
    (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
    @Module.Finite k (componentFunctions B (Spec (.of k)) hS X c) _ _
      (@Algebra.toModule k (componentFunctions B (Spec (.of k)) hS X c) _ _
        (fac.factorAlgebra c)) := by
  let (d : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X d) := fac.factorAlgebra d
  have := finiteDimensional_globalFunctions_of_isProper k B hS X hX f hf hcoh
  have : Module.Finite k
      (∀ d : ConnectedComponents (points B (Spec (.of k)) hS X),
        componentFunctions B (Spec (.of k)) hS X d) :=
    Module.Finite.equiv fac.equivalence.toLinearEquiv
  exact Module.Finite.of_surjective (LinearMap.proj c) (LinearMap.proj_surjective c)

end Field

end AlgebraicGeometry.Space

end
