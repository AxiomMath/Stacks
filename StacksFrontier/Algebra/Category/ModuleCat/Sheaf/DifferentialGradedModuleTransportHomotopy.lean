module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransport

/-!
# An additive lax monoidal functor transports a homotopy

Let `L : SheafOfModules R ⥤ SheafOfModules S` be an additive lax monoidal functor for the
tensor product of Tag 01CA, let `A` be a sheaf of differential graded `R`-algebras and let
`h` be a homotopy between two morphisms `ψ, χ : M ⟶ M₂` of right differential graded
`A`-modules. Then `L` applied degreewise to the components of `h` is a homotopy between the
transported morphisms `L(ψ)` and `L(χ)`, so the transport functor
`SheafOfModules.DifferentialGradedModule.transportFunctor` carries homotopic morphisms to
homotopic morphisms.

The two axioms transport for different reasons. Compatibility with the action of the algebra is
a morphism-level identity once it is read through
`SheafOfModules.DifferentialGradedModule.smulSheaf_comp_heq_iff`, and a lax monoidal functor
transports such an identity by `Stacks.MonoidalGraded.mapMul_naturality`. The homotopy equation
is a sum of composites of morphisms of complexes, and an additive functor preserves sums,
composites and the degree transports `eqToHom`.

For `L = f⁻¹` this is the missing half of the pullback `f^*M = f⁻¹M ⊗_{f⁻¹B} A` of a right
differential graded module: the tensor product with a bimodule already carries homotopies by
`SheafOfModules.TensorFunctorData.mapHomotopy`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.transportHomotopy` is the transported homotopy.

## Main results

* `SheafOfModules.DifferentialGradedModule.preservesHomotopic_transportFunctor`: the transport
  functor carries homotopic morphisms to homotopic morphisms.

## References

* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf

universe v₁ v₂ u₁ u₂ w

namespace SheafOfModules.DifferentialGradedModule

section TransportHomotopy

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (L : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [L.LaxMonoidal] [L.Additive] {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO hP

/-- **The transport of a homotopy along an additive lax monoidal functor**: the functor applied
to the degree `-1` components of the homotopy. -/
noncomputable def transportHomotopy {M M₂ : DifferentialGradedModule.{w, w, w} A}
    {ψ χ : M ⟶ M₂} (h : Homotopy ψ χ) :
    Homotopy (transportHom L hO hP ψ) (transportHom L hO hP χ) where
  app n := L.map (h.app n)
  map_mul n i := by
    refine (smulSheaf_comp_heq_iff (transport L M hO hP) hP (transport L M₂ hO hP)
      (fun q ↦ L.map (h.app q)) n i).mp ?_
    have hsrc : smulSheaf M n i ≫ h.app (n + i) ≫
          eqToHom (congrArg M₂.complex.X (show n + i - 1 = n - 1 + i by omega)) =
        (h.app n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf M₂ (n - 1) i :=
      (smulSheaf_comp_heq_iff M hO M₂ h.app n i).mpr fun U x y ↦ h.map_mul n i U x y
    have hnat := Stacks.MonoidalGraded.mapMul_naturality L (smulSheaf M n i)
      (smulSheaf M₂ (n - 1) i) (h.app n) (𝟙 (A.complex.X i))
      (h.app (n + i) ≫ eqToHom (congrArg M₂.complex.X (show n + i - 1 = n - 1 + i by omega)))
      hsrc
    rw [L.map_comp, L.map_id, eqToHom_map] at hnat
    rw [smulSheaf_transport, smulSheaf_transport]
    exact hnat
  comm n := by
    have hsub : L.map (ψ.toHomologicalComplex.f n - χ.toHomologicalComplex.f n) =
        L.map (ψ.toHomologicalComplex.f n) - L.map (χ.toHomologicalComplex.f n) := L.map_sub
    refine Eq.trans hsub.symm ?_
    refine Eq.trans (congrArg (fun z : M.complex.X n ⟶ M₂.complex.X n ↦ L.map z)
      (h.comm n)) ?_
    rw [L.map_add, L.map_comp, L.map_comp, L.map_comp, eqToHom_map]
    rfl

/-- **The transport functor carries homotopic morphisms to homotopic morphisms.** -/
theorem preservesHomotopic_transportFunctor :
    PreservesHomotopic (transportFunctor L hO hP (A := A)) :=
  fun _ _ ⟨h⟩ ↦ ⟨transportHomotopy L hO hP h⟩

end TransportHomotopy

end SheafOfModules.DifferentialGradedModule

end
