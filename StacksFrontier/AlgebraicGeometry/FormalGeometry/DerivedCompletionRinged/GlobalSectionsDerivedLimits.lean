module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedLimits
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.UnboundedGlobalSections
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.Complete

/-!
# `A`-linear derived global sections commute with derived limits

Let `(𝒞, 𝒪)` be a ringed site, `A` a commutative ring and `ρ : A ⟶ Γ(𝒞, 𝒪)` a ring map, so that
`𝒪` is a sheaf of `A`-algebras. `AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded`
of `UnboundedGlobalSections.lean` is `RΓ(𝒞, -) : D(𝒪) ⥤ D(A)`, the total right derived functor of
`A`-linear global sections on the whole unbounded derived category.

This file proves that this functor carries derived limits of countable inverse systems to derived
limits, and the consequence for derived completeness: if multiplication by the global section
`ρ a` of `𝒪` satisfies the Milnor condition `T(K, ρ a) = 0` on `K ∈ D(𝒪)`, then multiplication by
`a` satisfies it on `RΓ(𝒞, K)`, so that `RΓ(𝒞, K)` is derived complete along `I ⊂ A` as soon as
`T(K, ρ a) = 0` for every `a ∈ I`.

## Main results

* `AlgebraicGeometry.RingedSite.preservesLimitsOfShape_moduleGlobalSectionsOver`: `A`-linear
  global sections preserve countable products.
* `AlgebraicGeometry.RingedSite.preservesLimit_derivedGlobalSectionsOverUnbounded`: so does
  `RΓ(𝒞, -)` on the derived category, by [Stacks, Tag 08U1].
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_derivedGlobalSectionsOverUnbounded`: the
  Milnor condition transports from the global section `ρ a` of `𝒪` to the scalar `a` of `A`.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_derivedGlobalSectionsOverUnbounded_of_forall`:
  `RΓ(𝒞, K)` is derived complete along `I` when `T(K, ρ a) = 0` for every `a ∈ I`.

## Implementation notes

*Why this is a prerequisite of [Stacks, Tag 0BLX].* The source's proof of the identity
`RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)` is [Stacks, Tag 0A0G] applied to the morphism of ringed topoi
`(𝒞, 𝒪) ⟶ (pt, A)`, and the proof of that tag rewrites both sides with the Koszul formula
`K^∧ = R lim (K ⊗^𝐋 Kₙ)` of [Stacks, Tag 0A0E] and then **exchanges the direct image with
`R lim`** before finishing with the projection formula. At the morphism to the punctual site the
direct image is `RΓ(𝒞, -)`, so that exchange step is
`AlgebraicGeometry.RingedSite.isDerivedLimit_map_derivedGlobalSectionsOverUnbounded` of
`UnboundedGlobalSections.lean`, **`RΓ(𝒞, R lim Kₙ) = R lim RΓ(𝒞, Kₙ)`**. It holds at the full
generality of Tag 0BLX: no nilpotence, no finiteness and no boundedness hypothesis of any kind.
The other steps of that proof are not available; see the "What remains for Tag 0BLX" section of
`GlobalSectionsCompletion.lean` and the discussion in `UnboundedGlobalSections.lean`.

*The route to product preservation.* [Stacks, Tag 08U1] in the shape
`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor` asks that the source be Grothendieck
abelian, that countable products be exact in the *target* abelian category, and that the
underived functor preserve them. All three hold here: sheaves of modules on a site are
Grothendieck abelian by `SheafOfModules.isGrothendieckAbelianU`; countable products of
`A`-modules are exact; and `Γ(𝒞, -) = Hom_𝒪(𝒪, -)` preserves all limits, being a `Hom`-functor,
as does restriction of scalars. This is what fails for a general direct image, whose target is
again a category of sheaves of modules, where countable products are not exact — there the
preservation has to come from an adjunction instead, which is why
`AlgebraicGeometry.RingedSite.derivedPushforward_isDerivedComplete` of `Pushforward.lean` is
argued the way it is.

Preservation of countable products by `Hom_𝒪(𝒪, -)` is proved by forgetting to types, where it
is `CategoryTheory.coyoneda`'s preservation of limits; the forgetful functor of `ModuleCat`
reflects limits, which brings the conclusion back.

*The two scalars.* `Γ(𝒞, -)` is semilinear rather than linear: a scalar `a` of `A` acts on
`D(𝒪)` as multiplication by the global section `ρ a`, which is the central element
`Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (ρ a)` of
`Mod(𝒪)`, and on `D(A)` as `a` itself. The transport of the Milnor condition is therefore
`isDerivedCompleteAt_map_of_center` of `Pushforward.lean`, between two different rings of
scalars, and not the linear `isDerivedCompleteAt_map`. That the functor intertwines the two
multiplications is `map_globalSectionScalar_moduleGlobalSectionsOver` below, which is the
naturality of `globalSectionToEnd (ρ a)`: it acts on `Hom_𝒪(𝒪, M)` by postcomposition on the
target and by precomposition on the source `𝒪`, and those agree.

*What this does and does not give for Tag 0BLX.* It discharges the hypothesis `hρnil` of
`AlgebraicGeometry.RingedSite.isDerivedComplete_derivedGlobalSectionsOverUnbounded` — that each
`ρ a` be *nilpotent* — replacing it by the Milnor condition on the object, which nilpotence
implies. It does **not** discharge it from `AlgebraicGeometry.RingedSite.IsDerivedComplete`, the
predicate of [Stacks, Tag 0999]: that predicate is slicewise, asking the Milnor condition of
`K|_U` on the slice site over every object `U` and every section of `ℐ` over `U`, and the passage
from it to the Milnor condition for `K` on `𝒞` itself at a *global* section needs restriction to
a slice site to commute with countable products in `D(𝒪)` — i.e. exactly the exactness of
countable products of sheaves of modules that Tag 08U1 cannot be fed here. So "`RΓ(𝒞, ℱ^∧)` is
derived complete along `I`" is still not available, and no part of Tag 0BLX is registered here.

## References

* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped IsMulCommutative

universe u v w

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section Products

/-- **`Hom(P, -)` preserves products.** Forgetting the module structure turns it into
`CategoryTheory.coyoneda`, which preserves all limits; the forgetful functor of `ModuleCat`
reflects limits, so the preservation comes back. -/
theorem preservesLimitsOfShape_preadditiveCoyonedaObj
    {C : Type w} [Category.{v} C] [Preadditive C] [HasProductsOfShape ℕ C] (P : C) :
    PreservesLimitsOfShape (Discrete ℕ) (preadditiveCoyonedaObj P) := by
  have hpres : PreservesLimitsOfShape (Discrete ℕ)
      (preadditiveCoyonedaObj P ⋙ forget (ModuleCat.{v} (End P)ᵐᵒᵖ)) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (coyoneda.obj (op P)))
  have hrefl : ReflectsLimitsOfShape (Discrete ℕ) (forget (ModuleCat.{v} (End P)ᵐᵒᵖ)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves (preadditiveCoyonedaObj P) (forget _)

/-- Restriction of scalars preserves countable products: a product of modules is computed on the
underlying additive groups, which restriction of scalars does not change. -/
instance preservesLimitsOfShape_restrictScalars {R S : Type v} [Ring R] [Ring S]
    (r : R →+* S) : PreservesLimitsOfShape (Discrete ℕ) (ModuleCat.restrictScalars.{v} r) :=
  ⟨fun {_} ↦ inferInstance⟩

variable (X : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- **`A`-linear global sections preserve countable products.** `Γ(𝒞, -) = Hom_𝒪(𝒪, -)` is a
`Hom`-functor, and restriction of scalars changes no limit. -/
instance preservesLimitsOfShape_moduleGlobalSectionsOver :
    PreservesLimitsOfShape (Discrete ℕ) (moduleGlobalSectionsOver X A ρ) := by
  have h₁ : PreservesLimitsOfShape (Discrete ℕ)
      (preadditiveCoyonedaObj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
    preservesLimitsOfShape_preadditiveCoyonedaObj _
  exact Limits.comp_preservesLimitsOfShape
    (preadditiveCoyonedaObj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (ModuleCat.restrictScalars ((globalSectionMulEnd X).comp ρ))

end Products

section DerivedLimits

-- Countable products exist in the derived category of a module category. The global instance is
-- deliberately not registered, so `Dualizing.hasProductsOfShape_nat_derivedCategory` — the one
-- declaration of this fact — is made a local instance here.
attribute [local instance] Dualizing.hasProductsOfShape_nat_derivedCategory

variable (X : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- **`RΓ(𝒞, -)` preserves countable products**, by [Stacks, Tag 08U1]: `Mod(𝒪)` is Grothendieck
abelian, countable products of `A`-modules are exact, and `Γ(𝒞, -)` preserves them. -/
theorem preservesLimit_derivedGlobalSectionsOverUnbounded
    (G : Functor (Discrete ℕ)
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))) :
    PreservesLimit G (derivedGlobalSectionsOverUnbounded X A ρ) := by
  have _ :=
    SheafOfModules.isGrothendieckAbelianU.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  exact Stacks.Injectives.preservesLimit_discrete_of_isRightDerivedFunctor
    (moduleGlobalSectionsOver X A ρ) (derivedGlobalSectionsOverUnbounded X A ρ)
    (derivedGlobalSectionsOverUnboundedUnit X A ρ) G

end DerivedLimits

section Completeness

-- Countable products in the derived category of the base ring, as in the previous section.
attribute [local instance] Dualizing.hasProductsOfShape_nat_derivedCategory

/-- Countable products in `D(𝒪)`, from K-injective resolutions. -/
local instance hasProductsOfShape_nat_derivedCategory_sheaves (X : RingedSite.{u, u, u}) :
    HasProductsOfShape ℕ
      (DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  hasProductsOfShape_nat_derivedCategory_ringSheaf.{u, u, u} X

/-- Sheaves of modules are linear over the centre of their own category, which is the linear
structure the derived-completeness predicate of [Stacks, Tag 0999] uses. Named apart from the
`linearCatCenterRingSheaf` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomAdditive.lean`, which states the
same thing in a closure disjoint from this one: a `local instance` still occupies a global name, so
two modules declaring it under one name cannot both be imported. -/
local instance linearCatCenterRingSheafGlobalSections (X : RingedSite.{u, u, u}) :
    Linear (CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Linear.ofRingMorphism (RingHom.id _)

variable (X : RingedSite.{u, u, u}) (A : Type u) [CommRing A]
  (ρ : A →+* RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- **Multiplication by the global section `ρ x` of `𝒪`**, as a central endomorphism of the
sheaves of `𝒪`-modules. This is the scalar at which the Milnor condition on `D(𝒪)` is taken, the
`A`-action on `D(𝒪)` factoring through it. -/
abbrev globalSectionScalar (x : A) :
    CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ⟨(ρ x).1, (ρ x).2⟩

/-- **`Γ(𝒞, -)` intertwines multiplication by `ρ x` with multiplication by `x`.** The `A`-action
on `Γ(𝒞, M) = Hom_𝒪(𝒪, M)` is precomposition with multiplication by `ρ x` on the source `𝒪`,
while the functor carries multiplication by `ρ x` on `M` to postcomposition with it; the two
agree because multiplication by a global section is natural. -/
theorem map_globalSectionScalar_moduleGlobalSectionsOver (x : A)
    (P : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (moduleGlobalSectionsOver X A ρ).map ((globalSectionScalar X A ρ x).app P) =
      x • 𝟙 ((moduleGlobalSectionsOver X A ρ).obj P) :=
  ModuleCat.hom_ext <| LinearMap.ext fun g ↦ by
    let g' : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶ P := g
    have h1 : ((moduleGlobalSectionsOver X A ρ).map ((globalSectionScalar X A ρ x).app P)).hom g =
        g' ≫ (globalSectionScalar X A ρ x).app P := rfl
    have h2 : (x • 𝟙 ((moduleGlobalSectionsOver X A ρ).obj P)).hom g =
        (globalSectionScalar X A ρ x).app _ ≫ g' := by
      rw [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply]
      exact smul_moduleGlobalSectionsOver X A ρ P x g
    rw [h1, h2]
    exact (globalSectionScalar X A ρ x).naturality g'

/-- **The Milnor condition transports from the global section `ρ x` to the scalar `x`.** If
`T(K, ρ x) = 0` in `D(𝒪)` then `T(RΓ(𝒞, K), x) = 0` in `D(A)`.

`RΓ(𝒞, -)` is additive, preserves the countable power of `K` by
`preservesLimit_derivedGlobalSectionsOverUnbounded`, and carries multiplication by `ρ x` to
multiplication by `x` — on complexes, on the homotopy category and after right derivation, by
`Stacks.SemilinearFunctor.map_smul_id_rightDerived`. So `isDerivedCompleteAt_map_of_center`
applies. -/
theorem isDerivedCompleteAt_derivedGlobalSectionsOverUnbounded (x : A)
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : IsDerivedCompleteAt K (globalSectionScalar X A ρ x)) :
    IsDerivedCompleteAt ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) x := by
  have hpres := preservesLimit_derivedGlobalSectionsOverUnbounded X A ρ
    (Discrete.functor fun _ : ℕ ↦ K)
  have _ :=
    SheafOfModules.isGrothendieckAbelianU.{u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
  let := Functor.IsRightDerivedFunctor.commShift
    (derivedGlobalSectionsOverUnbounded X A ρ) (derivedGlobalSectionsOverUnboundedUnit X A ρ) W ℤ
  have : (derivedGlobalSectionsOverUnbounded X A ρ).IsTriangulated :=
    Stacks.Injectives.rightDerivedFunctor_isTriangulated (moduleGlobalSectionsOver X A ρ)
      (derivedGlobalSectionsOverUnbounded X A ρ)
      (derivedGlobalSectionsOverUnboundedUnit X A ρ)
  refine isDerivedCompleteAt_map_of_center (derivedGlobalSectionsOverUnbounded X A ρ) K
    (globalSectionScalar X A ρ x) x (fun L ↦ ?_) hK
  refine Stacks.SemilinearFunctor.map_smul_id_rightDerived
    (derivedGlobalSectionsOverUnbounded X A ρ)
    (derivedGlobalSectionsOverUnboundedUnit X A ρ) W
    (globalSectionScalar X A ρ x) x
    (fun M ↦ Stacks.SemilinearFunctor.map_smul_id_comp _ DerivedCategory.Qh _ _
      (fun N ↦ Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory
        (moduleGlobalSectionsOver X A ρ) _ _ (fun P ↦ ?_) (ComplexShape.up ℤ) N) M) L
  exact Eq.trans
    (congrArg (fun h ↦ (moduleGlobalSectionsOver X A ρ).map h)
      (Category.comp_id ((globalSectionScalar X A ρ x).app P)))
    (map_globalSectionScalar_moduleGlobalSectionsOver X A ρ x P)

/-- **`RΓ(𝒞, K)` is derived complete along `I` as soon as `T(K, ρ a) = 0` for every `a ∈ I`.**

This is the "right hand side" half of the identity of [Stacks, Tag 0BLX] — that the derived
completion of `RΓ(𝒞, K)` along `I` is `RΓ(𝒞, K)` itself — under a hypothesis on `K` rather than
on the ring map: it strictly generalizes
`AlgebraicGeometry.RingedSite.isDerivedComplete_derivedGlobalSectionsOverUnbounded`, whose
hypothesis is that every `ρ a` be nilpotent, and a nilpotent scalar satisfies the Milnor
condition at once by `isDerivedCompleteAt_of_isNilpotent`.

It is *not* the same as asking that `K` be derived complete along `I𝒪` in the sense of
[Stacks, Tag 0999]: that predicate is slicewise, and the module documentation of this file says
what the passage from it to the hypothesis here would need. -/
theorem isDerivedComplete_derivedGlobalSectionsOverUnbounded_of_forall (I : Ideal A)
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hK : ∀ a ∈ I, IsDerivedCompleteAt K (globalSectionScalar X A ρ a)) :
    _root_.IsDerivedComplete I ((derivedGlobalSectionsOverUnbounded X A ρ).obj K) :=
  fun a ha ↦ isDerivedCompleteAt_derivedGlobalSectionsOverUnbounded X A ρ a K (hK a ha)

end Completeness

end AlgebraicGeometry.RingedSite

end
