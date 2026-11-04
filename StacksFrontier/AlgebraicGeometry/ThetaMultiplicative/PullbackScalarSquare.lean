module

public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.ScalarAction

/-!
# The twist comparison intertwines the homogeneous scalar actions

Let `ψ : 𝒜 →+*ᵍ ℬ` be a map of graded rings and `a ∈ 𝒜 i` homogeneous of degree `i`. This file
proves that the comparison
`Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso`,
`e_n : (Proj ψ)^*𝒪_{Proj 𝒜}(n) ≅ 𝒪_{Proj ℬ}(n)`, intertwines multiplication by `a` with
multiplication by `ψ a` in every integer degree `n`:

`(Proj ψ)^*(a ·) ≫ e_{i + n} = e_n ≫ ((ψ a) ·)`.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.ThetaMultiplicative`.

* `twistPushforwardMap_twistScalarSheafMap_comp`: the square for the adjoint comparison
  `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`, as an identity of morphisms
  of sheaves of modules.
* `twistMap_twistScalarSheafMap_comp`: the square for the pullback comparison
  `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`.
* `head_twistScalarSheafMap`, `tail_twistScalarSheafMap`, `composite_twistScalarSheafMap`: the
  square for the three leading, the three trailing, and all six factors of
  `pullbackTwistCompositeIso`.
* `pullbackTwistCompositeIso_twistScalarSheafMap`, `pullbackTwistIso_twistScalarSheafMap`: the
  square for the comparison isomorphisms `pullbackTwistCompositeIso` and `pullbackTwistIso`.

## Implementation notes

The graded rings and their carriers are all taken in a single universe `Type u`, since
`AlgebraicGeometry.Proj.map` is stated in Mathlib for a single universe.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap)
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection

namespace Stacks.AlgebraicGeometry.ThetaMultiplicative

universe u

variable {A B σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The square for the adjoint form, as an identity of morphisms -/

/-- The adjoint comparison `twistPushforwardMap` intertwines multiplication by a homogeneous
element `a` of degree `i` with multiplication by `ψ a`, as an identity of morphisms of sheaves of
modules. -/
public theorem twistPushforwardMap_twistScalarSheafMap_comp (ψ : 𝒜 →+*ᵍ ℬ) (i : ℕ) (n : ℤ)
    (a : 𝒜 i) :
    twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a ≫ twistPushforwardMap 𝒜 ℬ ψ ((i : ℤ) + n) =
      twistPushforwardMap 𝒜 ℬ ψ n ≫
        (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
          ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).map
            (twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩)) := by
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.hom_ext ?_
  intro U
  refine ModuleCat.hom_ext ?_
  ext s
  exact twistPushforwardMap_twistScalarSheafMap 𝒜 ℬ ψ i n a U.unop s

/-! ### The square for the pullback form -/

/-- The pullback comparison `twistMap` intertwines the pullback of multiplication by a
homogeneous element `a` of degree `i` with multiplication by `ψ a`. -/
public theorem twistMap_twistScalarSheafMap_comp (ψ : 𝒜 →+*ᵍ ℬ) (i : ℕ) (n : ℤ) (a : 𝒜 i) :
    (Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).map
          (twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a) ≫
        twistMap 𝒜 ℬ ψ ((i : ℤ) + n) =
      twistMap 𝒜 ℬ ψ n ≫
        (Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).map
          (twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩) := by
  have key := (Scheme.Modules.pullbackPushforwardAdjunction
    (mapHom 𝒜 ℬ ψ)).homEquiv_naturality_right_square
    (twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a) (twistPushforwardMap 𝒜 ℬ ψ ((i : ℤ) + n))
    (twistPushforwardMap 𝒜 ℬ ψ n) ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).map
      (twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩))
    (twistPushforwardMap_twistScalarSheafMap_comp 𝒜 ℬ ψ i n a)
  rw [twistMap, twistMap, ← Category.assoc, key, Category.assoc, Category.assoc]
  exact congrArg _ ((Scheme.Modules.restrictFunctorIsoPullback
    (mapDomain 𝒜 ℬ ψ).ι).hom.naturality
      (twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩))

/-! ### The square for the six structural factors -/

/-- The three leading factors of `pullbackTwistCompositeIso` — the congruence along
`baseChange_comp_mapHom`, the pseudofunctoriality isomorphism for the factorisation through
`baseChange`, and the pullback of `twistMap` along `baseChange` — intertwine the pullback of
multiplication by `a` with the pullback of multiplication by `ψ a`. -/
public theorem head_twistScalarSheafMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤) (i : ℕ) (n : ℤ) (a : 𝒜 i) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a) ≫
        ((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒜 ℬ ψ hψ hdom)).inv.app
            (twistingSheaf 𝒜 ((i : ℤ) + n)) ≫
          (Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapHom 𝒜 ℬ ψ)).inv.app
            (twistingSheaf 𝒜 ((i : ℤ) + n)) ≫
          (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
            (twistMap 𝒜 ℬ ψ ((i : ℤ) + n))) =
      ((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒜 ℬ ψ hψ hdom)).inv.app
            (twistingSheaf 𝒜 n) ≫
          (Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapHom 𝒜 ℬ ψ)).inv.app
            (twistingSheaf 𝒜 n) ≫
          (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map (twistMap 𝒜 ℬ ψ n)) ≫
        (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
          ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).map
            (twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩)) := by
  have hmid : (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
        ((Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).map
          (twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a)) ≫
          (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
            (twistMap 𝒜 ℬ ψ ((i : ℤ) + n)) =
      (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map (twistMap 𝒜 ℬ ψ n) ≫
        (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
          ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).map
            (twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩)) :=
    ((Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
        (twistMap_twistScalarSheafMap_comp 𝒜 ℬ ψ i n a)).trans
        ((Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map_comp _ _))
  exact (CommSq.vert_comp ⟨(Scheme.Modules.pullbackCongr
    (baseChange_comp_mapHom 𝒜 ℬ ψ hψ hdom)).inv.naturality _⟩ (.vert_comp
      ⟨(Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapHom 𝒜 ℬ ψ)).inv.naturality _⟩
      ⟨hmid⟩)).w

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The three trailing factors of `pullbackTwistCompositeIso` — the pseudofunctoriality
isomorphism for `baseChange_comp_ι`, the congruence along it, and the pullback along the
identity — intertwine the pullback of multiplication by `ψ a` with multiplication by `ψ a`. -/
public theorem tail_twistScalarSheafMap (ψ : 𝒜 →+*ᵍ ℬ) (hdom : mapDomain 𝒜 ℬ ψ = ⊤)
    (i : ℕ) (n : ℤ) (a : 𝒜 i) :
    (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
          ((Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).map
            (twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩)) ≫
        ((Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapDomain 𝒜 ℬ ψ).ι).hom.app
            (twistingSheaf ℬ ((i : ℤ) + n)) ≫
          (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒜 ℬ ψ hdom)).hom.app
            (twistingSheaf ℬ ((i : ℤ) + n)) ≫
          (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app
            (twistingSheaf ℬ ((i : ℤ) + n))) =
      ((Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapDomain 𝒜 ℬ ψ).ι).hom.app
            (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒜 ℬ ψ hdom)).hom.app
            (twistingSheaf ℬ n) ≫
          (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app
            (twistingSheaf ℬ n)) ≫
        twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩ := by
  exact (CommSq.vert_comp ⟨(Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom)
    (mapDomain 𝒜 ℬ ψ).ι).hom.naturality _⟩ (.vert_comp
      ⟨(Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒜 ℬ ψ hdom)).hom.naturality _⟩
      ⟨(Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.naturality _⟩)).w

/-- The six factors of `pullbackTwistCompositeIso`, composed, intertwine the pullback of
multiplication by `a` with multiplication by `ψ a`. -/
public theorem composite_twistScalarSheafMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤) (i : ℕ) (n : ℤ) (a : 𝒜 i) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a) ≫
        (((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒜 ℬ ψ hψ hdom)).inv.app
              (twistingSheaf 𝒜 ((i : ℤ) + n)) ≫
            (Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapHom 𝒜 ℬ ψ)).inv.app
              (twistingSheaf 𝒜 ((i : ℤ) + n)) ≫
            (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map
              (twistMap 𝒜 ℬ ψ ((i : ℤ) + n))) ≫
          ((Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapDomain 𝒜 ℬ ψ).ι).hom.app
              (twistingSheaf ℬ ((i : ℤ) + n)) ≫
            (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒜 ℬ ψ hdom)).hom.app
              (twistingSheaf ℬ ((i : ℤ) + n)) ≫
            (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app
              (twistingSheaf ℬ ((i : ℤ) + n)))) =
      (((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒜 ℬ ψ hψ hdom)).inv.app
              (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapHom 𝒜 ℬ ψ)).inv.app
              (twistingSheaf 𝒜 n) ≫
            (Scheme.Modules.pullback (baseChange 𝒜 ℬ ψ hdom)).map (twistMap 𝒜 ℬ ψ n)) ≫
          ((Scheme.Modules.pullbackComp (baseChange 𝒜 ℬ ψ hdom) (mapDomain 𝒜 ℬ ψ).ι).hom.app
              (twistingSheaf ℬ n) ≫
            (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒜 ℬ ψ hdom)).hom.app
              (twistingSheaf ℬ n) ≫
            (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app
              (twistingSheaf ℬ n))) ≫
        twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩ := by
  exact (CommSq.vert_comp ⟨head_twistScalarSheafMap 𝒜 ℬ ψ hψ hdom i n a⟩
    ⟨tail_twistScalarSheafMap 𝒜 ℬ ψ hdom i n a⟩).w

/-- The comparison `e_n := pullbackTwistCompositeIso` intertwines multiplication by a
homogeneous element `a` of degree `i` with multiplication by `ψ a`:
`(Proj ψ)^*(a ·) ≫ e_{i + n} = e_n ≫ ((ψ a) ·)`, in every integer degree `n`. -/
public theorem pullbackTwistCompositeIso_twistScalarSheafMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hdom : mapDomain 𝒜 ℬ ψ = ⊤) (i : ℕ) (n : ℤ) (a : 𝒜 i)
    (htwn : IsIso (twistMap 𝒜 ℬ ψ n)) (htwk : IsIso (twistMap 𝒜 ℬ ψ ((i : ℤ) + n))) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a) ≫
        (pullbackTwistCompositeIso ψ hψ hdom ((i : ℤ) + n) htwk).hom =
      (pullbackTwistCompositeIso ψ hψ hdom n htwn).hom ≫
        twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩ :=
  composite_twistScalarSheafMap 𝒜 ℬ ψ hψ hdom i n a

/-- The comparison `e_n := pullbackTwistIso` intertwines multiplication by a homogeneous
element `a` of degree `i` with multiplication by `ψ a`:
`(Proj ψ)^*(a ·) ≫ e_{i + n} = e_n ≫ ((ψ a) ·)`, in every integer degree `n`. -/
public theorem pullbackTwistIso_twistScalarSheafMap (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hsurj : Function.Surjective (ψ : A → B))
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (i : ℕ) (n : ℤ) (a : 𝒜 i) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistScalarSheafMap 𝒜 i n ((i : ℤ) + n) rfl a) ≫
        (pullbackTwistIso ψ hψ hsurj hgen ((i : ℤ) + n)).hom =
      (pullbackTwistIso ψ hψ hsurj hgen n).hom ≫
        twistScalarSheafMap ℬ i n ((i : ℤ) + n) rfl ⟨ψ a, ψ.map_mem a.2⟩ :=
  pullbackTwistCompositeIso_twistScalarSheafMap 𝒜 ℬ ψ hψ _ i n a _ _

end Stacks.AlgebraicGeometry.ThetaMultiplicative

end
