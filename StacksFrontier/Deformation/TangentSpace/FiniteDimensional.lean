module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksFrontier.Deformation.TangentSpace.DifferentialLinear
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite-dimensionality of the tangent space of a predeformation category

Let `𝓕` be a predeformation category over `𝒞_Λ` whose associated functor of fibrewise
isomorphism classes satisfies Schlessinger's condition (S2). Stacks 06IH then equips the
tangent space `T𝓕 = 𝓕(k[ε])` with a canonical `k`-vector-space structure. That structure is
not given by a formula: it is transported along an equality of carriers from the value at the
rank-one module of the *linear lift* `LinearFunctorLift k U` of the set-valued functor
`U : V ↦ 𝓕(k[V])` produced by Stacks 06IA. Consequently a concrete map out of `T𝓕` is not
visibly linear, and the only handle on linearity is the one used for Stacks 06IJ: a family of
maps out of `U` which is natural in `V` is automatically `k`-linear at `V = k`, because
addition on the value of an additive `k`-linear functor at `k` is computed from the two
projections `k × k → k` and their sum, and scalar multiplication by `r` from `r • 𝟙`.

This file packages that observation into the criterion one needs in order to prove a tangent
space finite-dimensional: it suffices to exhibit an additive, `k`-linear, module-valued
functor `G` on finitely generated `k`-modules whose value at `k` is finite-dimensional,
together with a natural family of maps `U ⟶ G` which is injective at `V = k`. All of the
transport along the carrier equality of Stacks 06IH is discharged here, so the remaining
obligation is purely mathematical.

## Main results

* `Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`: a natural
  injection of the tangent-space set functor into an additive `k`-linear functor with
  finite-dimensional value at the rank-one module makes the canonical tangent space of
  Stacks 06IH finite-dimensional.

## Implementation notes

`Deformation.associatedTangentSpaceSetFunctor` is an abbreviation for the set-valued functor
`V ↦ 𝓕(k[V])` in the form Stacks 06IA and 06IH use it, namely through the Artinian square-zero
extensions of Stacks 06IB. Its value at `FGModuleCat.of k k` is *definitionally* the tangent
space `Deformation.artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)`, so the
injectivity hypothesis and the conclusion speak about the same type with no comparison map.

As in Stacks 06IJ the (S2) and predeformation hypotheses appear in the conclusion as `Fact`
instances, because that is how Stacks 06IH exposes the vector-space structure to instance
search; this is why the conclusion is stated under a `letI` prefix.
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u w u₁ v₁ u₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The set-valued functor `V ↦ 𝓕(k[V])` on finitely generated `k`-modules, whose linear lift
of Stacks 06IA carries the canonical vector-space structure of Stacks 06IH on the tangent
space. Its value at the rank-one module is the tangent space itself. -/
@[sga "7 VI 1.18" "partial"]
noncomputable abbrev associatedTangentSpaceSetFunctor
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) : FGModuleCat.{w} k ⥤ Type u₁ :=
  tangentSpaceSetFunctor Λ k (artinianLocalOver Λ k)
    (squareZeroExtension_mem_artinianLocalOver Λ k)
    (artinianLocalOverToArtinian Λ k ⋙ isomorphismClasses 𝓕 h𝓕)

/-- Transport along an equality of types is injective. -/
theorem cast_inj_of_eq {α β : Type u₁} (h : α = β) {x y : α}
    (hxy : cast h x = cast h y) : x = y := by
  cases h
  exact hxy

/-- Transporting bundled module data along an equality of types carries finite-dimensionality
to finite-dimensionality. -/
private theorem finiteDimensional_rec {R : Type w} [Field R] {α β : Type u₁}
    (h : α = β) (D : AddModuleData R α) :
    letI : AddCommGroup α := D.1
    letI : Module R α := D.2
    let Dβ : AddModuleData R β := h.rec D
    letI : AddCommGroup β := Dβ.1
    letI : Module R β := Dβ.2
    FiniteDimensional R α → FiniteDimensional R β := by
  cases h
  exact id

/-- The tangent space of a predeformation category whose isomorphism-class functor satisfies
(S2) is finite-dimensional for its canonical structure of Stacks 06IH as soon as the
set-valued functor `V ↦ 𝓕(k[V])` has a family of maps to an additive `k`-linear
module-valued functor `G`, natural in `V`, which is injective at the rank-one module and whose
value there is finite-dimensional.

Naturality is what supplies linearity: it is not available from the injection at `V = k`
alone, because the vector-space structure of Stacks 06IH is defined through the whole functor
`V ↦ 𝓕(k[V])` and not through its value at `k`. -/
theorem finiteDimensional_artinianTangentSpace_of_natural_injection
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (G : FGModuleCat.{w} k ⥤ ModuleCat.{u₂} k) [G.Additive] [G.Linear k]
    [FiniteDimensional k (G.obj (FGModuleCat.of k k))]
    (t : ∀ V : FGModuleCat.{w} k,
      (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V → G.obj V)
    (ht : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V')
        (x : (associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).obj V),
      t V' ((associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered).map f x) = (G.map f) (t V x))
    (hinj : Function.Injective (t (FGModuleCat.of k k))) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
    FiniteDimensional k (artinianTangentSpace Λ k (isomorphismClasses 𝓕 h𝓕.cofibered)) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕.cofibered))) := ⟨hS2⟩
  let A : FGModuleCat.{w} k := FGModuleCat.of k k
  let U := associatedTangentSpaceSetFunctor 𝓕 h𝓕.cofibered
  let LF := associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2
  let eF (V : FGModuleCat.{w} k) : (LF.functor.obj V : Type u₁) = U.obj V :=
    congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ ↦ H.obj V) LF.forget_comp
  let tmod : ∀ V : FGModuleCat.{w} k, LF.functor.obj V → G.obj V :=
    fun V x ↦ t V (cast (eF V) x)
  have htmod : ∀ {V V' : FGModuleCat.{w} k} (f : V ⟶ V') (x : LF.functor.obj V),
      tmod V' ((LF.functor.map f) x) = (G.map f) (tmod V x) := by
    intro V V' f x
    dsimp [tmod]
    rw [moduleFunctor_map_cast k LF.functor U LF.forget_comp f x]
    exact ht f _
  have hinjmod : Function.Injective (tmod A) := fun _ _ hxy ↦
    cast_inj_of_eq (eF A) (hinj hxy)
  have hfd : FiniteDimensional k (LF.functor.obj A) :=
    FiniteDimensional.of_injective
      (IsLinearMap.mk' _ (isLinearMap_of_natural_on_fgModules k LF.functor G tmod htmod)) hinjmod
  have hcarrier := associatedTangentSpaceModuleStructure_carrierUnlifted 𝓕 h𝓕 hS2
  let DF : AddModuleData k (LF.functor.obj A) := ⟨inferInstance, inferInstance⟩
  have hDF : associatedTangentSpaceModuleDataUnlifted 𝓕 = hcarrier.rec DF := rfl
  unfold associatedTangentSpaceAddCommGroupUnlifted associatedTangentSpaceModuleUnlifted
  rw [hDF]
  exact finiteDimensional_rec hcarrier DF hfd

end Deformation

end
