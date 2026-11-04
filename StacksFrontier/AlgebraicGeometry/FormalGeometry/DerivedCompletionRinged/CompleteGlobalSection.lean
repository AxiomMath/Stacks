module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafCondition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingFromComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LeftAdjoint

/-!
# Derived completeness at a global section, globally and at the subproducts of a family

Let `(𝒞, 𝒪)` be a ringed site, let `K ∈ D(𝒪)` and let `h` be a global section of `𝒪`.
Multiplication by `h` is a central endomorphism
`Stacks.SheafOfModules.globalSectionToEnd 𝒪 (awayFamily h)` of the category of sheaves of
`𝒪`-modules, and `AlgebraicGeometry.RingedSite.memVanishingIdeal_iff_isDerivedCompleteAt` --
the equivalence of conditions (1) and (3) of [Stacks, Tag 0997] -- reads the vanishing of
`R𝑆heafHom_𝒪(𝒪_h, K)` as derived completeness of `K` at that *global* scalar. The predicate of
[Stacks, Tag 0999], on the other hand, is stated *per slice*: it tests `T(K|_U, g) = 0` at the
local sections `g` of a sheaf of ideals. This file supplies the two passages between those two
shapes which the construction of a completion functor out of a finite family of global sections
needs.

## Main results

* `Stacks.SheafOfModules.overFunctor_map_globalSectionToEnd`: restriction from the site to the
  slice site over `U` carries multiplication by a compatible family of local sections to
  multiplication by the member of that family at `U`.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_of_forall_isDerivedCompleteAtSection`:
  **per-slice gives global.** If `T(K|_U, h|_U) = 0` for every object `U` of `𝒞`, then `K` is
  derived complete at the global scalar given by `h`.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_awayFamily_of_isDerivedComplete`: the same
  passage with the hypothesis in the form of [Stacks, Tag 0999], for a global section all of
  whose restrictions are sections of the given sheaf of ideals.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_prodGlobalSection_of_mem`: **generators give
  subproducts.** For a finite family `f_1, …, f_r` of global sections and `S` a subset containing
  an index `i` at which `K` is derived complete, `K` is derived complete at
  `f_S = ∏_{j ∈ S} f_j`.
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_prodGlobalSection_of_isDerivedComplete`: the
  two passages composed with [Stacks, Tag 0997], giving the vanishing of
  `R𝑆heafHom_𝒪(𝒪_{f_S}, K)` for every non-empty `S` from derived completeness of `K` along a
  sheaf of ideals containing the restrictions of the generators.

## Implementation notes

The local-to-global passage is locality of invertibility in `D(𝒪)`,
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`, applied to the family of *all*
objects of `𝒞`, which covers the final object because the identity of each object already lies
in the sieve that family generates there. At the member `U` the image of the Milnor difference is
invertible because `T(K|_U, h|_U) = 0`; the two scalars are matched by
`Stacks.SheafOfModules.overFunctor_map_globalSectionToEnd` below, and the matching is carried to
the derived category exactly as in the proof of
`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve`, which is the same locality
step for a covering of a single object rather than of the top.

The passage from the generators to the subproducts is closure of the global condition under
multiplication, `isDerivedCompleteAt_smul`, together with multiplicativity of
`Stacks.SheafOfModules.globalSectionToEnd` in the section, which is
`Stacks.SheafOfModules.globalSectionToEnd_mul_of_val`: the sections of a sheaf of rings carry no
`Mul` instance, so that lemma takes the product pointwise as a hypothesis, and
`AlgebraicGeometry.RingedSite.globalSectionVal_prodGlobalSection` with `Finset.prod_erase_mul`
supplies it. No multiplicativity of a sheaf of ideals is involved: `f_S` is itself a *global*
section, and it is reached from the single generator `f_i` for any one `i ∈ S`.

## References

* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe v u w m

namespace Stacks.SheafOfModules

/-- **Restriction to a slice site matches the global and the local multiplication operator.**
For `R` a sheaf of rings on `𝒞` and `s` a compatible family of local sections of `R`, the
restriction `SheafOfModules.overFunctor R U` carries multiplication by `s` to multiplication by
the section `s_U` of `R` over `U`, read on `𝒞/U`.

This is the companion at the base of
`Stacks.SheafOfModules.overFunctor_map_terminalSectionToEnd`, which is the same statement one
slice further up; both are `Stacks.SheafOfModules.map_globalSectionToEnd` for the restriction
functor, whose hypothesis here is the compatibility of the family `s` itself. -/
theorem overFunctor_map_globalSectionToEnd {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [∀ T : Cᵒᵖ, IsMulCommutative (R.obj.obj T)] (U : C)
    (s : (R.obj ⋙ forget RingCat).sections) (M : _root_.SheafOfModules.{m} R) :
    (_root_.SheafOfModules.overFunctor.{m} R U).map ((globalSectionToEnd R s).app M) =
      (terminalSectionToEnd (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal (s.val (op U))).app
        ((_root_.SheafOfModules.overFunctor.{m} R U).obj M) :=
  map_globalSectionToEnd (F := Over.forget U) (S := R.over U) (R := R) (𝟙 (R.over U)) s
    (terminalSection (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal (s.val (op U)))
    (fun T ↦ (terminalSection_over_val R U (s.val (op U)) T).trans
      (s.property ((unop T).hom).op))
    M

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

attribute [local instance] linearCatCenterRingSheaf
  isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- **Every object of a site covers the final object.** The sieve which the family of all objects
generates at an object already contains that object's identity, so it is the maximal sieve. This
is the covering of the top at which the locality of invertibility in `D(𝒪)` turns a condition
holding on every slice into one holding on `𝒞`. -/
theorem coversTop_id : X.J.CoversTop (id : X.C → X.C) := fun W ↦
  X.J.superset_covering (fun Z _ _ ↦ ⟨Z, ⟨𝟙 Z⟩⟩) (X.J.top_mem W)

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] hasProductsOfShape_nat_derivedCategory

section Global

variable (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Derived restriction to a slice site matches the global and the local multiplication
operator.** The functor induced on derived categories by restriction to `𝒞/U` carries
multiplication by the global section `h` to multiplication by its value `h|_U`, read on the
slice as a section over the terminal object `U ⟶ U`.

This is `Stacks.SheafOfModules.overFunctor_map_globalSectionToEnd` transported to derived
categories, and it is the single input both passages between the global and the per-slice shape
of the Milnor condition consume: `isDerivedCompleteAt_of_forall_isDerivedCompleteAtSection`
below reads it through `isIso_map_oneSubSmulShift_of_isDerivedCompleteAt`, and
`isDerivedCompleteAtSection_of_isDerivedCompleteAt` through
`isDerivedCompleteAt_map_of_smul_id`. -/
theorem overFunctor_mapDerivedCategory_map_smul_id (U : X.C)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.map
        ((Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (awayFamily X h) :
          CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) • 𝟙 L) =
      (overTerminalRingHom X U (globalSectionVal h (op U)) :
          CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))) •
        𝟙 ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj L) := by
  let G := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let a : CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (awayFamily X h)
  let aU : CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    overTerminalRingHom X U (globalSectionVal h (op U))
  have hmap : ∀ M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      G.map (a.app M) = aU.app (G.obj M) :=
    Stacks.SheafOfModules.overFunctor_map_globalSectionToEnd
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U (awayFamily X h)
  exact Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id
    G a aU
    (fun Z ↦ Stacks.SemilinearFunctor.map_smul_id_mapHomologicalComplex G a aU
      (fun M ↦ (congrArg G.map (Category.comp_id (a.app M))).trans
        ((hmap M).trans (Category.comp_id (aU.app (G.obj M))).symm))
      (ComplexShape.up ℤ) Z) L

/-- **Derived completeness at a global section is detected slice by slice.** If the restriction
of `K` to the slice site over `U` is derived complete at the restriction of the global section
`h` there, for every object `U` of `𝒞`, then `K` itself is derived complete at the central
endomorphism given by multiplication by `h`.

Derived completeness at a scalar is invertibility of the Milnor difference `1 - h·shift`, and
invertibility in `D(𝒪)` is local on the site
(`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`, the locality step of
[Stacks, Tag 08JJ]); the family of all objects of `𝒞` covers the final object, and at the member
`U` the image of the Milnor difference is invertible because `T(K|_U, h|_U) = 0`. -/
theorem isDerivedCompleteAt_of_forall_isDerivedCompleteAtSection
    (hh : ∀ U : X.C, IsDerivedCompleteAtSection X K U (globalSectionVal h (op U))) :
    IsDerivedCompleteAt K
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) :
        CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  show IsIso (oneSubSmulShift K
    (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (awayFamily X h) :
      CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
  exact Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory (coversTop_id X) _ fun U ↦ by
    have := preservesProducts_mapDerivedCategory_overFunctor X U
    exact isIso_map_oneSubSmulShift_of_isDerivedCompleteAt
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory
      (overFunctor_mapDerivedCategory_map_smul_id X h U K) (hh U)

/-- **Derived completeness at a global section passes to every slice**, which is the converse of
`isDerivedCompleteAt_of_forall_isDerivedCompleteAtSection` and the direction that needs no
locality: if `K` is derived complete at multiplication by the global section `h`, then the
restriction `K|_U` is derived complete at `h|_U` for every object `U` of `𝒞`, that is
`T(K|_U, h|_U) = 0`.

Derived restriction to the slice is additive, preserves the countable products of the derived
categories (`preservesProducts_mapDerivedCategory_overFunctor`) and carries multiplication by
`h` to multiplication by `h|_U` (`overFunctor_mapDerivedCategory_map_smul_id`); such a functor
transports the Milnor condition by `isDerivedCompleteAt_map_of_smul_id`. -/
theorem isDerivedCompleteAtSection_of_isDerivedCompleteAt
    (hK : IsDerivedCompleteAt K
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) :
        CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (U : X.C) :
    IsDerivedCompleteAtSection X K U (globalSectionVal h (op U)) := by
  have := preservesProducts_mapDerivedCategory_overFunctor X U
  exact isDerivedCompleteAt_map_of_smul_id
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U).mapDerivedCategory
    (overFunctor_mapDerivedCategory_map_smul_id X h U K) hK

/-- **[Stacks, Tag 0999] gives derived completeness at a global section of the ideal sheaf.** If
`K` is derived complete along `ℐ` and every restriction of the global section `h` is a section of
`ℐ`, then `K` is derived complete at multiplication by `h`. -/
theorem isDerivedCompleteAt_awayFamily_of_isDerivedComplete
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ U : X.C, globalSectionVal h (op U) ∈ I.toSubmodule.obj (op U))
    (hK : IsDerivedComplete.{u, u, u, u} X I K) :
    IsDerivedCompleteAt K
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X h) :
        CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  isDerivedCompleteAt_of_forall_isDerivedCompleteAtSection X K h
    fun U ↦ (isDerivedComplete_iff_forall_isDerivedCompleteAtSection X K I).1 hK U
      (globalSectionVal h (op U)) (hI U)

end Global

section Prod

variable {r : ℕ} (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **Multiplication by `f_S` splits off multiplication by one generator.** For `i ∈ S` the
central endomorphism given by `f_S = ∏_{j ∈ S} f_j` is the product of the one given by
`f_{S \ {i}}` and the one given by `f_i`. -/
theorem globalSectionToEnd_awayFamily_prodGlobalSection_erase
    {S : Finset (Fin r)} {i : Fin r} (hi : i ∈ S) :
    (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (awayFamily X (prodGlobalSection f S)) :
          CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) =
      Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X (prodGlobalSection f (S.erase i))) *
        Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X (f i)) :=
  Stacks.SheafOfModules.globalSectionToEnd_mul_of_val (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      _ _ _ fun U ↦ by
    show globalSectionVal (prodGlobalSection f S) U =
      globalSectionVal (prodGlobalSection f (S.erase i)) U * globalSectionVal (f i) U
    rw [globalSectionVal_prodGlobalSection, globalSectionVal_prodGlobalSection]
    exact (Finset.prod_erase_mul S (fun j ↦ globalSectionVal (f j) U) hi).symm

/-- **Derived completeness at one generator gives it at every subproduct containing that
generator.** If `K` is derived complete at multiplication by `f_i` and `i ∈ S`, then `K` is
derived complete at multiplication by `f_S = ∏_{j ∈ S} f_j`.

In particular every non-empty `S` is reached from any one of its elements. The condition is
closed under multiplication by an arbitrary central endomorphism (`isDerivedCompleteAt_smul`),
and `f_S` is itself a *global* section, so no multiplicativity of a sheaf of ideals is needed. -/
theorem isDerivedCompleteAt_prodGlobalSection_of_mem
    {S : Finset (Fin r)} {i : Fin r} (hi : i ∈ S)
    (hfi : IsDerivedCompleteAt K
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (awayFamily X (f i)) :
        CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedCompleteAt K
      (Stacks.SheafOfModules.globalSectionToEnd (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (awayFamily X (prodGlobalSection f S)) :
          CatCenter (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) := by
  rw [globalSectionToEnd_awayFamily_prodGlobalSection_erase X f hi]
  exact isDerivedCompleteAt_smul _ hfi

/-- **A derived-complete `K` is right orthogonal to every non-empty subproduct.** If `K` is
derived complete along a sheaf of ideals `ℐ` all of whose slices contain the restrictions of the
generators `f_1, …, f_r`, then `R𝑆heafHom_𝒪(𝒪_{f_S}, K) = 0` for every non-empty `S`.

This is the vanishing which the stupid filtration of the extended alternating Čech complex
`Č(f)` consumes, assembled from three inputs: the per-slice-to-global passage
`isDerivedCompleteAt_awayFamily_of_isDerivedComplete` at a single generator `f_i` with `i ∈ S`,
the generator-to-subproduct passage `isDerivedCompleteAt_prodGlobalSection_of_mem`, and the
equivalence of conditions (1) and (3) of [Stacks, Tag 0997],
`memVanishingIdeal_iff_isDerivedCompleteAt`. Emptiness of `S` is excluded because `f_∅ = 1` is a
unit, for which the vanishing is false; `S` non-empty supplies the index `i`. -/
theorem memVanishingIdeal_prodGlobalSection_of_isDerivedComplete
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hI : ∀ (i : Fin r) (U : X.C),
      globalSectionVal (f i) (op U) ∈ I.toSubmodule.obj (op U))
    (hK : IsDerivedComplete.{u, u, u, u} X I K)
    {S : Finset (Fin r)} (hS : S.Nonempty) :
    MemVanishingIdeal X K (prodGlobalSection f S) := by
  obtain ⟨i, hi⟩ := hS
  exact (memVanishingIdeal_iff_isDerivedCompleteAt X (prodGlobalSection f S) K).2 <|
    isDerivedCompleteAt_prodGlobalSection_of_mem X K f hi
      (isDerivedCompleteAt_awayFamily_of_isDerivedComplete X K (f i) I (hI i) hK)

end Prod

end AlgebraicGeometry.RingedSite

end
