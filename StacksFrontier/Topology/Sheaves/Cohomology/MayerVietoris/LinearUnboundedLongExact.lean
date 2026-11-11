module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.LinearUnboundedTriangle

/-!
# The Mayer--Vietoris long exact cohomology sequence over the ring of global functions

Let `(X, 𝒪_X)` be a ringed space, let `A = Γ(X, 𝒪_X)`, and let `X = U ∪ V` be a union of two
open subsets. For `E` in `D(𝒪_X)` write `H^n(W, E)` for the `A`-module `H^n(RΓ(W, E))`.
Applying the cohomology functors of `D(A)` to the functorial Mayer--Vietoris triangle
`Stacks.Cohomology.LinearMayerVietoris.linearUnboundedMayerVietoris` gives the long exact
sequence

`⋯ ⟶ H^n(X, E) ⟶ H^n(U, E) ⊕ H^n(V, E) ⟶ H^n(U ∩ V, E) ⟶ H^{n+1}(X, E) ⟶ ⋯`

functorially in `E`.

## Main definitions

* `Stacks.Cohomology.LinearMayerVietoris.linearCohomology`: the functor `H^n(W, -)`.
* `Stacks.Cohomology.LinearMayerVietoris.cohomologyToBiprod`,
  `Stacks.Cohomology.LinearMayerVietoris.cohomologyFromBiprod`,
  `Stacks.Cohomology.LinearMayerVietoris.cohomologyConnecting`: the three maps of the sequence.

## Main results

* `Stacks.Cohomology.LinearMayerVietoris.linearUnboundedMayerVietoris_longExact`: the triangle,
  exactness of the long exact sequence at every term, and naturality of its maps in `E`.

## Implementation notes

The cohomology of the middle term `RΓ(U, E) ⊕ RΓ(V, E)` of the triangle is identified with
`H^n(U, E) ⊕ H^n(V, E)` through `CategoryTheory.Functor.mapBiprod`, the cohomology functors being
additive; exactness is then transported from the homology sequence of the triangle
(`DerivedCategory.HomologySequence`).

## References

* [Stacks Project, Tag 08BX](https://stacks.math.columbia.edu/tag/08BX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.LinearDerivedSections

universe u

namespace Stacks.Cohomology.LinearMayerVietoris

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.isGrothendieckAbelianU

variable (X : RingedSpace.{u, u}) (U V : Opens X.carrier)

/-- The cohomology `H^n(W, E) = H^n(RΓ(W, E))` of the `A`-linear derived sections over an
open `W`, as a functor of `E ∈ D(𝒪_X)` with values in `A`-modules, `A = Γ(X, 𝒪_X)`. -/
abbrev linearCohomology (W : Opens X.carrier) (n : ℤ) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤ ModuleCat.{u} (baseRing X) :=
  derivedLinearSections X W ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n

/-- The restriction map `H^n(W, E) ⟶ H^n(Z, E)` for `Z ⊆ W`, natural in `E`: the map induced
on cohomology by the derived restriction `RΓ(W, -) ⟶ RΓ(Z, -)`. -/
abbrev linearCohomologyRestriction {Z W : Opens X.carrier} (h : Z ≤ W) (n : ℤ) :
    linearCohomology X W n ⟶ linearCohomology X Z n :=
  Functor.whiskerRight (derivedLinearRestriction X h)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n)

/-- The first map `H^n(X, E) ⟶ H^n(U, E) ⊕ H^n(V, E)` of the Mayer--Vietoris long exact
sequence, the two restriction maps. -/
def cohomologyToBiprod (n : ℤ) (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (linearCohomology X ⊤ n).obj E ⟶
      (linearCohomology X U n).obj E ⊞ (linearCohomology X V n).obj E :=
  biprod.lift ((linearCohomologyRestriction X (le_top : U ≤ ⊤) n).app E)
    ((linearCohomologyRestriction X (le_top : V ≤ ⊤) n).app E)

/-- The second map `H^n(U, E) ⊕ H^n(V, E) ⟶ H^n(U ∩ V, E)` of the Mayer--Vietoris long exact
sequence, the difference of the two restriction maps. -/
def cohomologyFromBiprod (n : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (linearCohomology X U n).obj E ⊞ (linearCohomology X V n).obj E ⟶
      (linearCohomology X (U ⊓ V) n).obj E :=
  biprod.desc ((linearCohomologyRestriction X (inf_le_left : U ⊓ V ≤ U) n).app E)
    (-((linearCohomologyRestriction X (inf_le_right : U ⊓ V ≤ V) n).app E))

/-- The connecting map `H^{n₀}(U ∩ V, E) ⟶ H^{n₁}(X, E)`, `n₁ = n₀ + 1`, of the long exact
cohomology sequence attached to a map `δ : RΓ(U ∩ V, -) ⟶ RΓ(X, -)[1]`: the map induced by
`δ` on cohomology, i.e. the connecting map of the homology sequence of the Mayer--Vietoris
triangle when `δ` is its third map. -/
def cohomologyConnecting
    (δ : derivedLinearSections X (U ⊓ V) ⟶ derivedLinearSections X ⊤ ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (linearCohomology X (U ⊓ V) n₀).obj E ⟶ (linearCohomology X ⊤ n₁).obj E :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).shiftMap (δ.app E) n₀ n₁
    (by rw [add_comm 1, h])

/-- The first map of the Mayer--Vietoris long exact sequence is natural in `E`. -/
lemma cohomologyToBiprod_naturality (n : ℤ)
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : E ⟶ E') :
    cohomologyToBiprod X U V n E ≫
        biprod.map ((linearCohomology X U n).map φ) ((linearCohomology X V n).map φ) =
      (linearCohomology X ⊤ n).map φ ≫ cohomologyToBiprod X U V n E' := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, cohomologyToBiprod, biprod.lift_fst_assoc,
      cohomologyToBiprod, Category.assoc, biprod.lift_fst]
    exact ((linearCohomologyRestriction X (le_top : U ≤ ⊤) n).naturality φ).symm
  · rw [Category.assoc, biprod.map_snd, cohomologyToBiprod, biprod.lift_snd_assoc,
      cohomologyToBiprod, Category.assoc, biprod.lift_snd]
    exact ((linearCohomologyRestriction X (le_top : V ≤ ⊤) n).naturality φ).symm

/-- The second map of the Mayer--Vietoris long exact sequence is natural in `E`. -/
lemma cohomologyFromBiprod_naturality (n : ℤ)
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : E ⟶ E') :
    cohomologyFromBiprod X U V n E ≫ (linearCohomology X (U ⊓ V) n).map φ =
      biprod.map ((linearCohomology X U n).map φ) ((linearCohomology X V n).map φ) ≫
        cohomologyFromBiprod X U V n E' := by
  apply biprod.hom_ext'
  · rw [cohomologyFromBiprod, biprod.inl_desc_assoc, biprod.inl_map_assoc,
      cohomologyFromBiprod, biprod.inl_desc]
    exact ((linearCohomologyRestriction X (inf_le_left : U ⊓ V ≤ U) n).naturality φ).symm
  · rw [cohomologyFromBiprod, biprod.inr_desc_assoc, biprod.inr_map_assoc,
      cohomologyFromBiprod, biprod.inr_desc, Preadditive.neg_comp, Preadditive.comp_neg]
    exact congrArg Neg.neg
      ((linearCohomologyRestriction X (inf_le_right : U ⊓ V ≤ V) n).naturality φ).symm

/-- The connecting map of the Mayer--Vietoris long exact sequence is natural in `E`. -/
lemma cohomologyConnecting_naturality
    (δ : derivedLinearSections X (U ⊓ V) ⟶ derivedLinearSections X ⊤ ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : E ⟶ E') :
    cohomologyConnecting X U V δ n₀ n₁ h E ≫ (linearCohomology X ⊤ n₁).map φ =
      (linearCohomology X (U ⊓ V) n₀).map φ ≫ cohomologyConnecting X U V δ n₀ n₁ h E' := by
  have hφ : (derivedLinearSections X (U ⊓ V)).map φ ≫ δ.app E' =
      δ.app E ≫ ((derivedLinearSections X ⊤).map φ)⟦(1 : ℤ)⟧' := δ.naturality φ
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).shiftMap (δ.app E)
      n₀ n₁ _ ≫ ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).shift n₁).map
        ((derivedLinearSections X ⊤).map φ) =
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).shift n₀).map
        ((derivedLinearSections X (U ⊓ V)).map φ) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) 0).shiftMap (δ.app E')
        n₀ n₁ _
  rw [← Functor.shiftMap_comp, ← Functor.shiftMap_comp', hφ]

/-- **Stacks 08BX, the long exact cohomology sequence.** Let `X` be a ringed space covered by
two open subsets `U` and `V`, and let `A = Γ(X, 𝒪_X)`.  There is a natural transformation
`δ : RΓ(U ∩ V, -) ⟶ RΓ(X, -)[1]` such that, for every object `E` of `D(𝒪_X)`,

* `RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ∩ V, E) ⟶ RΓ(X, E)[1]` is a distinguished
  triangle in `D(A)`, the first two maps being the restrictions with the usual sign;
* writing `H^n(W, E) = H^n(RΓ(W, E))`, the sequence
  `H^n(X, E) ⟶ H^n(U, E) ⊕ H^n(V, E) ⟶ H^n(U ∩ V, E) ⟶ H^{n+1}(X, E) ⟶
    H^{n+1}(U, E) ⊕ H^{n+1}(V, E)`
  is exact for every `n ∈ ℤ`, the connecting map being the one induced by `δ`; as `n` varies
  these windows make up the whole long exact Mayer--Vietoris sequence;
* every map of the long exact sequence is natural in `E`. -/
@[stacks 08BX "the triangle and the long exact cohomology sequence, functorial in E, in D(A)"]
theorem linearUnboundedMayerVietoris_longExact (hUV : U ⊔ V = ⊤) :
    ∃ δ : derivedLinearSections X (U ⊓ V) ⟶ derivedLinearSections X ⊤ ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} (baseRing X))) (1 : ℤ),
      (∀ E, Triangle.mk
        (biprod.lift ((derivedLinearRestriction X (le_top : U ≤ ⊤)).app E)
          ((derivedLinearRestriction X (le_top : V ≤ ⊤)).app E))
        (biprod.desc ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app E)
          (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app E)))
        (δ.app E) ∈ distTriang (DerivedCategory (ModuleCat.{u} (baseRing X)))) ∧
      (∀ E (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁),
        (ComposableArrows.mk₄ (cohomologyToBiprod X U V n₀ E) (cohomologyFromBiprod X U V n₀ E)
          (cohomologyConnecting X U V δ n₀ n₁ h E) (cohomologyToBiprod X U V n₁ E)).Exact) ∧
      (∀ (n : ℤ) {E E'} (φ : E ⟶ E'),
        cohomologyToBiprod X U V n E ≫
            biprod.map ((linearCohomology X U n).map φ) ((linearCohomology X V n).map φ) =
          (linearCohomology X ⊤ n).map φ ≫ cohomologyToBiprod X U V n E' ∧
        cohomologyFromBiprod X U V n E ≫ (linearCohomology X (U ⊓ V) n).map φ =
          biprod.map ((linearCohomology X U n).map φ) ((linearCohomology X V n).map φ) ≫
            cohomologyFromBiprod X U V n E') ∧
      (∀ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) {E E'} (φ : E ⟶ E'),
        cohomologyConnecting X U V δ n₀ n₁ h E ≫ (linearCohomology X ⊤ n₁).map φ =
          (linearCohomology X (U ⊓ V) n₀).map φ ≫ cohomologyConnecting X U V δ n₀ n₁ h E') := by
  obtain ⟨δ, hδ⟩ := linearUnboundedMayerVietoris X U V hUV
  refine ⟨δ, hδ, fun E n₀ n₁ h => ?_,
    fun n _ _ φ => ⟨cohomologyToBiprod_naturality X U V n φ,
      cohomologyFromBiprod_naturality X U V n φ⟩,
    fun n₀ n₁ h _ _ φ => cohomologyConnecting_naturality X U V δ n₀ n₁ h φ⟩
  let T := Triangle.mk
    (biprod.lift ((derivedLinearRestriction X (le_top : U ≤ ⊤)).app E)
      ((derivedLinearRestriction X (le_top : V ≤ ⊤)).app E))
    (biprod.desc ((derivedLinearRestriction X (inf_le_left : U ⊓ V ≤ U)).app E)
      (-((derivedLinearRestriction X (inf_le_right : U ⊓ V ≤ V)).app E)))
    (δ.app E)
  have hT : T ∈ distTriang _ := hδ E
  have hpres (n : ℤ) :
      PreservesBinaryBiproducts (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have := hpres n₀
  have := hpres n₁
  have hS : (ComposableArrows.mk₄
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n₀).map T.mor₁)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n₀).map T.mor₂)
      (DerivedCategory.HomologySequence.δ T n₀ n₁ h)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n₁).map T.mor₁)).Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₂ T hT n₀).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (DerivedCategory.HomologySequence.exact₃ T hT n₀ n₁ h).exact_toComposableArrows
        (DerivedCategory.HomologySequence.exact₁ T hT n₀ n₁ h).exact_toComposableArrows)
  refine ComposableArrows.exact_of_iso ?_ hS
  refine ComposableArrows.isoMk₄ (Iso.refl _)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n₀).mapBiprod
      ((derivedLinearSections X U).obj E) ((derivedLinearSections X V).obj E))
    (Iso.refl _) (Iso.refl _)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) n₁).mapBiprod
      ((derivedLinearSections X U).obj E) ((derivedLinearSections X V).obj E))
    ?_ ?_ ?_ ?_
  · exact (biprod.map_lift_mapBiprod _ _ _ _ _).trans (Category.id_comp _).symm
  · refine (Category.comp_id _).trans ?_
    refine (biprod.mapBiprod_hom_desc _ _ _ _ _).symm.trans ?_
    rw [Functor.map_neg]
    rfl
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (biprod.map_lift_mapBiprod _ _ _ _ _).trans (Category.id_comp _).symm

end Stacks.Cohomology.LinearMayerVietoris

end
