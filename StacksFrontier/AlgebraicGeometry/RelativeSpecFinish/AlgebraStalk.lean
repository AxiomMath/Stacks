module

public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic

/-!
# Stalks of the pullback of an algebra sheaf

Let `g : T ⟶ S` be a morphism of schemes and `A` a sheaf of commutative `𝒪_S`-algebras.  The
pullback `Stacks.AffineAlgebraEquivalence.algebraPullback` of `A` along `g` is by construction
the pushout `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` in the category of sheaves of commutative rings on `T`.

The `algebraPullback_isQuasicoherent` clause of Stacks Tag 01SA asks for the underlying
`𝒪_T`-module of that pushout to be the extension of scalars of the underlying `𝒪_S`-module,
after which the clause follows from
`Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback` (Stacks Tag 01BG) and
closure of quasi-coherence under isomorphism.  That identification can be checked on stalks,
since `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk` reduces invertibility of a
morphism of sheaves of modules to invertibility on every stalk.

This file supplies the half of that argument which concerns the pushout: **taking stalks on
sheaves of commutative rings preserves it**.  Concretely, for every `t : T` the stalk at `t` of
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is the pushout of the stalks, i.e. the tensor product
`(g⁻¹A)_t ⊗_{(g⁻¹𝒪_S)_t} 𝒪_{T,t}`.

## Main results

* `preservesColimitsOfShape_stalkOnSheaf`: the stalk functor on sheaves of commutative rings
  preserves pushouts.
* `isPushout_stalk_algebraPullback`: the stalk at `t` of the square exhibiting
  `algebraPullback` as an extension of scalars is again a pushout square, now of commutative
  rings.
* `stalkAlgebraPullbackIso`: that pushout written as a tensor product, so the stalk of the
  pullback algebra is `(g⁻¹A)_t ⊗_{(g⁻¹𝒪_S)_t} 𝒪_{T,t}`.

## Implementation notes

`TopCat.Presheaf.stalkFunctor` composed with `TopCat.Sheaf.forget` is a left adjoint, by
Mathlib's `stalkSkyscraperSheafAdjunction`, hence preserves all colimits; applying
`CategoryTheory.IsPushout.map` to
`Stacks.AffineAlgebraEquivalence.algebraPullback_isPushout` gives the square, and
`CommRingCat.isPushout_tensorProduct` together with
`CategoryTheory.IsPushout.isoIsPushout` turns it into the tensor product.

The `IsLeftAdjoint` instance for the stalk functor on sheaves does **not** synthesize: the
ambient section in Mathlib carries a `∀ U, Decidable (p₀ ∈ U)` hypothesis which is not
available, so `stalkSkyscraperSheafAdjunction` has to be invoked under `classical`.  The
resulting `PreservesColimitsOfSize` must then be instantiated at universe `0` (the shape
`CategoryTheory.Limits.WalkingSpan` lives there) and handed to
`CategoryTheory.IsPushout.map` **positionally**: a `have` of the instance is not picked up by
instance search.  The two `Algebra` instances on the stalks are repeated in the statement and
in the proof of `stalkAlgebraPullbackIso`, since a `letI` in a statement does not survive into
the proof.

## What is not done

**This file does not prove the `algebraPullback_isQuasicoherent` clause of [Stacks, Tag 01SA]**.
Two pieces of the stalk argument are still missing, and both are on the *source* side of the
comparison:

* the stalk of the sheaf-theoretic inverse image, `(g⁻¹A)_t ≅ A_{g(t)}`.  Mathlib has
  `TopCat.Presheaf.stalkPullbackIso` for the **presheaf** inverse image only, and
  `TopCat.Sheaf.pullback` is that followed by sheafification; the identification of the stalk
  of a `CommRingCat`-valued categorical sheafification with the stalk of the presheaf is itself
  absent from Mathlib (`TopCat.Presheaf.sheafifyStalkIso` is about the concrete, `Type`-valued
  sheafification).
* the stalk of `AlgebraicGeometry.Scheme.Modules.pullback`, that is
  `(g^*M)_t ≅ M_{g(t)} ⊗_{𝒪_{S,g(t)}} 𝒪_{T,t}`, and the comparison morphism from it to the
  underlying module of the pushout.  Nothing in
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/` computes a stalk.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.AffineAlgebraEquivalence

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- The stalk at a point, as a functor on sheaves of commutative rings. -/
public abbrev stalkOnSheaf (t : T) :
    TopCat.Sheaf CommRingCat.{u} T.toTopCat ⥤ CommRingCat.{u} :=
  TopCat.Sheaf.forget CommRingCat.{u} T.toTopCat ⋙
    TopCat.Presheaf.stalkFunctor CommRingCat.{u} t

/-- The stalk functor on sheaves of commutative rings preserves pushouts. -/
public theorem preservesColimitsOfShape_stalkOnSheaf (t : T) :
    PreservesColimitsOfShape WalkingSpan (stalkOnSheaf (T := T) t) := by
  classical
  exact (show PreservesColimitsOfSize.{0, 0} (stalkOnSheaf (T := T) t) from
    (stalkSkyscraperSheafAdjunction t).leftAdjoint_preservesColimits).preservesColimitsOfShape

/-- **The stalk of the pullback of an algebra sheaf is the pushout of the stalks.**  The square
exhibiting `Stacks.AffineAlgebraEquivalence.algebraPullback` as an extension of scalars stays a
pushout square after taking the stalk at any point of `T`. -/
public theorem isPushout_stalk_algebraPullback (A : Stacks.RelativeSpec.AlgebraSheaf S) (t : T) :
    IsPushout
      ((stalkOnSheaf t).map ((TopCat.Sheaf.pullback CommRingCat g.base).map A.hom))
      ((stalkOnSheaf t).map (inverseImageStructureMap g))
      ((stalkOnSheaf t).map ((algebraPullbackMap g).app A))
      ((stalkOnSheaf t).map ((algebraPullback g).obj A).hom) :=
  @IsPushout.map _ _ _ _ (stalkOnSheaf t) _ _ _ _ _ _ _ _
    (preservesColimitsOfShape_stalkOnSheaf t).preservesColimit
    (algebraPullback_isPushout g A)

section Tensor

variable (A : Stacks.RelativeSpec.AlgebraSheaf S) (t : T)

/-- The stalk at `t` of the inverse image `g⁻¹𝒪_S`, the ring the two stalks are tensored
over. -/
public abbrev inverseImageBaseStalk : CommRingCat.{u} :=
  (stalkOnSheaf t).obj ((TopCat.Sheaf.pullback CommRingCat g.base).obj S.sheaf)

/-- The stalk at `t` of the inverse image `g⁻¹A`. -/
public abbrev inverseImageAlgebraStalk : CommRingCat.{u} :=
  (stalkOnSheaf t).obj ((TopCat.Sheaf.pullback CommRingCat g.base).obj A.right)

/-- The `(g⁻¹𝒪_S)_t`-algebra structure on `(g⁻¹A)_t`, given by the stalk of the structure
morphism of `A`. -/
@[instance_reducible]
public def algebraInverseImageAlgebraStalk :
    Algebra (inverseImageBaseStalk g t) (inverseImageAlgebraStalk g A t) :=
  ((stalkOnSheaf t).map ((TopCat.Sheaf.pullback CommRingCat g.base).map A.hom)).hom.toAlgebra

/-- The `(g⁻¹𝒪_S)_t`-algebra structure on `𝒪_{T,t}`, given by the stalk of `g⁻¹𝒪_S ⟶ 𝒪_T`. -/
@[instance_reducible]
public def algebraStructureStalk :
    Algebra (inverseImageBaseStalk g t) ((stalkOnSheaf t).obj T.sheaf) :=
  ((stalkOnSheaf t).map (inverseImageStructureMap g)).hom.toAlgebra

/-- **The stalk of the pullback algebra is a tensor product of stalks**:
`(g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T)_t ≅ (g⁻¹A)_t ⊗_{(g⁻¹𝒪_S)_t} 𝒪_{T,t}`. -/
public def stalkAlgebraPullbackIso :
    letI := algebraInverseImageAlgebraStalk g A t
    letI := algebraStructureStalk g t
    CommRingCat.of (inverseImageAlgebraStalk g A t ⊗[inverseImageBaseStalk g t]
        (stalkOnSheaf t).obj T.sheaf) ≅
      (stalkOnSheaf t).obj ((algebraPullback g).obj A).right :=
  letI := algebraInverseImageAlgebraStalk g A t
  letI := algebraStructureStalk g t
  (CommRingCat.isPushout_tensorProduct _ _ _).isoIsPushout _ _
    (isPushout_stalk_algebraPullback g A t)

end Tensor

end Stacks.AffineAlgebraEquivalence

end

end
