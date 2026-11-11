module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.Products
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct

/-!
# The global cup product

Let `(S, 𝒪_S)` be a ringed space, let `K, M ∈ D(𝒪_S)` and set `A = Γ(S, 𝒪_S)`. The global cup
product is a map `μ : RΓ(S, K) ⊗^𝐋_A RΓ(S, M) ⟶ RΓ(S, K ⊗^𝐋_{𝒪_S} M)` in `D(A)`, and it induces
pairings `∪ : Hⁱ(S, K) × Hʲ(S, M) ⟶ Hⁱ⁺ʲ(S, K ⊗^𝐋_{𝒪_S} M)` by tensoring two classes to a class
in `Hⁱ⁺ʲ(RΓ(S, K) ⊗^𝐋_A RΓ(S, M))` and applying `μ`.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison`: a left adjoint `L` of
  `RΓ(S, -) : D(𝒪_S) ⥤ D(A)` together with a comparison of bifunctors
  `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct`: the global cup product `μ`, as a
  morphism of bifunctors.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyModule`: `Hⁱ(S, K)`, the `i`-th
  cohomology of `RΓ(S, K)` as an `A`-module.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing`: the induced pairings
  `Hⁱ(S, K) ⊗_A Hʲ(S, M) ⟶ Hⁱ⁺ʲ(S, K ⊗^𝐋_{𝒪_S} M)`.
* `RingTheory.TorProducts.IsCocycleProduct`: a map `Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)` is
  induced by tensoring cocycles on a given choice of K-flat representatives.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct_app`: on objects the global cup
  product is the adjoint transpose of the tensor comparison followed by the counit of
  `L ⊣ RΓ(S, -)` in both tensor factors.
* `Stacks.Cohomology.DerivedGlobalCupProduct.isIso_globalCupProduct_app`: `μ` is invertible at
  a pair where the unit of the adjunction, the tensor comparison and the two counits are.
* `Stacks.Cohomology.DerivedGlobalCupProduct.globalCupProduct_naturality`: `μ` is natural in
  both complexes jointly.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_eq`: the pairing is the tensoring of
  classes followed by `Hⁱ⁺ʲ(μ)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_tensorStep`: the tensoring step sends
  the classes of two cocycles to the class of their tensor, on K-flat representatives.
* `RingTheory.TorProducts.IsCocycleProduct.eq`: two maps which are cocycle products at the same
  choice of K-flat representatives are equal.
* `RingTheory.TorProducts.eq_cohomologyTensorProduct_of_forall`: a map which is a cocycle
  product at every choice of K-flat representatives is `cohomologyTensorProduct`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_eq_of_isCocycleProduct`: the pairings
  are computed by any such map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

/-! ### Cocycle products of cohomology classes -/

section CocycleProduct

namespace RingTheory.TorProducts

open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- The type of maps `Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)` over a commutative ring `R`. -/
abbrev CohomologyProductMap (K L : DObj R) (i j : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K ⊗
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L ⟶
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).obj
      (((canonicalDerivedTensorProductFunctor R).obj K).obj L)

/-- For `K` and `L` in `D(R)`, K-flat complexes `P` and `Q` and isomorphisms `P ≅ K` and
`Q ≅ L` in `D(R)`, a map `f : Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)` is a cocycle product at that
choice when, read through those representatives and through the comparison of `⊗^𝐋_R` with the
tensor product of K-flat complexes, it is induced by a tensoring of cocycles
`Zⁱ(P) ⊗_R Zʲ(Q) ⟶ Zⁱ⁺ʲ(P ⊗ Q)`. -/
def IsCocycleProduct (K L : DObj R) (i j : ℤ)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (hQ : Q.KFlat)
    (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L)
    (f : CohomologyProductMap K L i j) : Prop :=
  ∃ z : P.cycles i ⊗ Q.cycles j ⟶ (P ⊗ Q).cycles (i + j),
    z ≫ (P ⊗ Q).iCycles (i + j) =
        (P.iCycles i ⊗ₘ Q.iCycles j) ≫
          HomologicalComplex.ιTensorObj P Q i j (i + j) rfl ∧
      (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫
            ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app P ⊗ₘ
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).inv.app Q) ≫
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map eP.hom ⊗ₘ
              (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map eQ.hom) ≫
            f ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
              (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
                ((canonicalDerivedTensorProductFunctor R).obj
                  (DerivedCategory.Q.obj P)).map eQ.inv ≫
                ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (i + j)).hom.app (P ⊗ Q) =
          z ≫ (P ⊗ Q).homologyπ (i + j)

/-- Every cohomology tensor product is a cocycle product at some choice of K-flat
representatives. -/
theorem CohomologyTensorProduct.isCocycleProduct {K L : DObj R} {i j : ℤ}
    (p : CohomologyTensorProduct K L i j) :
    ∃ (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (hQ : Q.KFlat)
      (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L),
      IsCocycleProduct K L i j P Q hP hQ eP eQ p.map :=
  p.maps_cocycles

/-- Two maps which are cocycle products at the same choice of K-flat representatives are
equal. -/
theorem IsCocycleProduct.eq {K L : DObj R} {i j : ℤ}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} {hP : P.KFlat} {hQ : Q.KFlat}
    {eP : DerivedCategory.Q.obj P ≅ K} {eQ : DerivedCategory.Q.obj Q ≅ L}
    {f g : CohomologyProductMap K L i j}
    (hf : IsCocycleProduct K L i j P Q hP hQ eP eQ f)
    (hg : IsCocycleProduct K L i j P Q hP hQ eP eQ g) : f = g := by
  obtain ⟨z, hz, hzf⟩ := hf
  obtain ⟨z', hz', hzg⟩ := hg
  obtain rfl : z = z' := by
    rw [← cancel_mono ((P ⊗ Q).iCycles (i + j)), hz, hz']
  have h₁ : Epi (P.homologyπ i ⊗ₘ Q.homologyπ j) := epi_tensorHom _ _
  obtain ⟨α, hα⟩ :
      ∃ α : P.homology i ⊗ Q.homology j ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K ⊗
            (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L,
        α.hom =
          ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app P ⊗ₘ
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).inv.app Q) ≫
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map eP.hom ⊗ₘ
              (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map eQ.hom) :=
    ⟨((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).symm.app P ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso eP) ⊗ᵢ
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) j).symm.app Q ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).mapIso eQ),
      by simp only [tensorIso_hom, tensorHom_comp_tensorHom]; rfl⟩
  obtain ⟨β, hβ⟩ :
      ∃ β : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).obj
            (((canonicalDerivedTensorProductFunctor R).obj K).obj L) ≅
          (P ⊗ Q).homology (i + j),
        β.hom =
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
              (((canonicalDerivedTensorProductFunctor R).map eP.inv).app L ≫
                ((canonicalDerivedTensorProductFunctor R).obj
                  (DerivedCategory.Q.obj P)).map eQ.inv ≫
                ((canonicalDerivedTensorProduct R).comparison P Q hP hQ).hom) ≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (i + j)).hom.app (P ⊗ Q) :=
    ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).mapIso
          (((canonicalDerivedTensorProductFunctor R).mapIso eP.symm).app L ≪≫
            ((canonicalDerivedTensorProductFunctor R).obj
                (DerivedCategory.Q.obj P)).mapIso eQ.symm ≪≫
              (canonicalDerivedTensorProduct R).comparison P Q hP hQ) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (i + j)).app (P ⊗ Q), rfl⟩
  have e : (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ α.hom ≫ f ≫ β.hom =
      (P.homologyπ i ⊗ₘ Q.homologyπ j) ≫ α.hom ≫ g ≫ β.hom := by
    rw [hα, hβ]
    exact hzf.trans hzg.symm
  exact (Iso.cancel_iso_hom_right f g β).1 ((Iso.cancel_iso_hom_left α _ _).1 ((cancel_epi _).1 e))

/-- A map which is a cocycle product at every choice of K-flat representatives is the map of
`RingTheory.TorProducts.cohomologyTensorProduct`. -/
theorem eq_cohomologyTensorProduct_of_forall {K L : DObj R} {i j : ℤ}
    (f : CohomologyProductMap K L i j)
    (hf : ∀ (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (hQ : Q.KFlat)
      (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L),
      IsCocycleProduct K L i j P Q hP hQ eP eQ f) :
    f = (cohomologyTensorProduct K L i j).map := by
  obtain ⟨P, Q, hP, hQ, eP, eQ, h⟩ := (cohomologyTensorProduct K L i j).isCocycleProduct
  exact (hf P Q hP hQ eP eQ).eq h

end RingTheory.TorProducts

end CocycleProduct

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable (S : RingedSpace.{u, u})

/-! ### The one-point comparison -/

/-- A one-point comparison for derived global sections: a functor `L : D(A) ⥤ D(𝒪_S)` for
`A = Γ(S, 𝒪_S)`, an adjunction `L ⊣ RΓ(S, -)`, and a morphism of bifunctors
`L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`. -/
structure OnePointComparison where
  /-- The left adjoint `L` of derived global sections. -/
  pullback : DerivedCategory (ModuleCat.{u} (baseRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))
  /-- `L` is left adjoint to `RΓ(S, -) : D(𝒪_S) ⥤ D(A)`. -/
  adjunction : pullback ⊣ baseSections S
  /-- The comparison `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`, as a morphism of bifunctors. -/
  tensorComparison :
    Functor.uncurry.obj (tensorBase S) ⋙ pullback ⟶
      pullback.prod pullback ⋙ Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)

/-! ### The global cup product -/

variable {S}

/-- The global cup product `μ : RΓ(S, K) ⊗^𝐋_A RΓ(S, M) ⟶ RΓ(S, K ⊗^𝐋_{𝒪_S} M)` in `D(A)` for
`A = Γ(S, 𝒪_S)`, as a morphism of bifunctors on `D(𝒪_S) × D(𝒪_S)`: the relative cup product
construction for the adjunction `L ⊣ RΓ(S, -)` and the tensor comparison of `c`.

The tensor comparison of an arbitrary `c` is unconstrained (it may be zero, and then so is the
result), so this is the recipe of Cohomology, Section 0FKU for an arbitrary datum, not the cup
product of the source. The source's `μ` is
`globalCupProduct (canonicalOnePointComparison S)`, for which Section 0FKU is stated in
`Stacks.Cohomology.DerivedGlobalCupProduct.section_cupProduct_canonical`. -/
def globalCupProduct (c : OnePointComparison S) : GlobalCupProduct S where
  app KM :=
    adjunctionBitensorMap c.adjunction (Functor.uncurry.obj (tensorBase S))
      (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)) c.tensorComparison KM.1 KM.2
  naturality _ _ km :=
    adjunctionBitensorMap_natural c.adjunction (Functor.uncurry.obj (tensorBase S))
      (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)) c.tensorComparison km.1 km.2

/-- On objects the global cup product is the adjoint transpose of the tensor comparison followed
by the counit of `L ⊣ RΓ(S, -)` in both tensor factors. -/
theorem globalCupProduct_app (c : OnePointComparison S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (globalCupProduct c).app (K, M) =
      adjunctionBitensorMap c.adjunction (Functor.uncurry.obj (tensorBase S))
        (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)) c.tensorComparison K M :=
  rfl

/-- The global cup product is natural in both complexes jointly. -/
theorem globalCupProduct_naturality (κ : GlobalCupProduct S)
    {K K' M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
    (k : K ⟶ K') (m : M ⟶ M') :
    (Functor.uncurry.obj (tensorBase S)).map
          ((baseSections S).map k ×ₘ (baseSections S).map m) ≫ κ.app (K', M') =
      κ.app (K, M) ≫
        (baseSections S).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)).map (k ×ₘ m)) :=
  κ.naturality (X := (K, M)) (Y := (K', M')) (k, m)

/-- The global cup product `μ` at `(K, M)` is an isomorphism as soon as the unit of
`L ⊣ RΓ(S, -)` is invertible at `RΓ(S, K) ⊗^𝐋_A RΓ(S, M)`, the tensor comparison of `c` is
invertible at `(RΓ(S, K), RΓ(S, M))`, and the counit of `L ⊣ RΓ(S, -)` is invertible at `K` and
at `M`. -/
theorem isIso_globalCupProduct_app (c : OnePointComparison S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (hunit : IsIso (c.adjunction.unit.app
      ((Functor.uncurry.obj (tensorBase S)).obj
        ((baseSections S).obj K, (baseSections S).obj M))))
    (hcmp : IsIso (c.tensorComparison.app
      ((baseSections S).obj K, (baseSections S).obj M)))
    (hK : IsIso (c.adjunction.counit.app K)) (hM : IsIso (c.adjunction.counit.app M)) :
    IsIso ((globalCupProduct c).app (K, M)) :=
  isIso_adjunctionBitensorMap_of_isIso c.adjunction (Functor.uncurry.obj (tensorBase S))
    (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)) c.tensorComparison K M
    hunit hcmp hK hM

/-! ### The induced pairings on cohomology -/

/-- `Hⁱ(S, K)`, the `i`-th cohomology of `RΓ(S, K)`, as a module over `A = Γ(S, 𝒪_S)`. -/
abbrev cohomologyModule (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i : ℤ) :
    ModuleCat.{u} (baseRing S) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).obj ((baseSections S).obj K)

/-- The pairings `∪ : Hⁱ(S, K) ⊗_A Hʲ(S, M) ⟶ Hⁱ⁺ʲ(S, K ⊗^𝐋_{𝒪_S} M)` induced by a global cup
product `κ`: a class `ξ ∈ Hⁱ(S, K)` and a class `η ∈ Hʲ(S, M)` are tensored to a class `ξ ⊗ η` in
`Hⁱ⁺ʲ(RΓ(S, K) ⊗^𝐋_A RΓ(S, M))`, and `ξ ∪ η = κ(ξ ⊗ η)`.

For an arbitrary `κ` this is the second display of Cohomology, Section 0FKU applied to that
morphism; the source's pairings are `cupPairing (globalCupProduct (canonicalOnePointComparison S))`,
stated in `Stacks.Cohomology.DerivedGlobalCupProduct.section_cupProduct_canonical`. -/
def cupPairing (κ : GlobalCupProduct S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ) :
    cohomologyModule K i ⊗ cohomologyModule M j ⟶
      cohomologyModule (((derivedTensorProductFunctor S.sheaf).obj K).obj M) (i + j) :=
  (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections S).obj K)
        ((baseSections S).obj M) i j).map ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map (κ.app (K, M))

/-- The pairing is the tensoring of the two classes followed by `Hⁱ⁺ʲ` of the global cup
product. -/
theorem cupPairing_eq (κ : GlobalCupProduct S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ) :
    cupPairing κ K M i j =
      (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections S).obj K)
            ((baseSections S).obj M) i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          (κ.app (K, M)) :=
  rfl

/-- The tensoring step of `cupPairing` is a `RingTheory.TorProducts.CohomologyTensorProduct`:
on K-flat representatives of `RΓ(S, K)` and `RΓ(S, M)` it sends the tensor of the classes of two
cocycles `k` and `l` to the class of `k ⊗ l`. -/
theorem cupPairing_tensorStep (κ : GlobalCupProduct S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ) :
    ∃ p : RingTheory.TorProducts.CohomologyTensorProduct ((baseSections S).obj K)
        ((baseSections S).obj M) i j,
      cupPairing κ K M i j =
        p.map ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          (κ.app (K, M)) :=
  ⟨RingTheory.TorProducts.cohomologyTensorProduct ((baseSections S).obj K)
    ((baseSections S).obj M) i j, rfl⟩

/-- The pairings induced by `globalCupProduct c` are the tensoring of classes followed by
`Hⁱ⁺ʲ` of the relative cup product construction for `c`. -/
theorem cupPairing_globalCupProduct (c : OnePointComparison S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ) :
    cupPairing (globalCupProduct c) K M i j =
      (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections S).obj K)
            ((baseSections S).obj M) i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
          (adjunctionBitensorMap c.adjunction (Functor.uncurry.obj (tensorBase S))
            (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf)) c.tensorComparison K M) :=
  rfl

/-- The pairings are computed by any tensoring of classes which is induced by tensoring cocycles
at every choice of K-flat representatives of `RΓ(S, K)` and `RΓ(S, M)`. -/
theorem cupPairing_eq_of_isCocycleProduct (κ : GlobalCupProduct S)
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ)
    (f : RingTheory.TorProducts.CohomologyProductMap ((baseSections S).obj K)
      ((baseSections S).obj M) i j)
    (hf : ∀ (P Q : CochainComplex (ModuleCat.{u} (baseRing S)) ℤ) (hP : P.KFlat) (hQ : Q.KFlat)
      (eP : DerivedCategory.Q.obj P ≅ (baseSections S).obj K)
      (eQ : DerivedCategory.Q.obj Q ≅ (baseSections S).obj M),
      RingTheory.TorProducts.IsCocycleProduct ((baseSections S).obj K) ((baseSections S).obj M)
        i j P Q hP hQ eP eQ f) :
    cupPairing κ K M i j =
      f ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
        (κ.app (K, M)) := by
  rw [cupPairing_eq, RingTheory.TorProducts.eq_cohomologyTensorProduct_of_forall f hf]

end Stacks.Cohomology.DerivedGlobalCupProduct

end
