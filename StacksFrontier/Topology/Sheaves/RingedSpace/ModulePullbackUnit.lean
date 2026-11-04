module

public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.Modules.ClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The pullback of the structure sheaf, and the adjunction unit at the structure sheaf

Let `f : X ⟶ Y` be a morphism of ringed spaces. The transpose
`RingedSpaceModuleAdjunction.modulePullbackUnitToUnit f : f^* 𝒪_Y ⟶ 𝒪_X` of the
structure-sheaf map is *always* an isomorphism, for every morphism of ringed spaces and in
every universe. This file proves that and draws the consequence for the unit of `f^* ⊣ f_*` at
the structure sheaf:

`𝒪_Y ⟶ f_* f^* 𝒪_Y` **is** the structure-sheaf map `f^♯ : 𝒪_Y ⟶ f_* 𝒪_X`,

read through the isomorphism. This is the tensor description
`f_* f^* M ≅ M ⊗_{𝒪_Y} f_* 𝒪_X` of [Stacks Project, Tag 01R3] part (1) in the one case
`M = 𝒪_Y`, where the tensor product is the right-hand factor and the comparison is pinned on
generators: the unit sends a section `a` of `𝒪_Y` to `f^♯(a)`, that is, to `a ⊗ 1`.

Only `AlgebraicGeometry.RingedSpace.isIso_modulePullbackUnitToUnit_ofRestrict` — the same
statement for the open immersion `ι_U : X|_U ⟶ X` — was available before, and it was proved
there from the explicit description of restriction. The proof here is independent of that and
applies to every `f`: Mathlib's `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` is an
isomorphism as soon as the functor of sites is final, and `TopologicalSpace.Opens.map g` is
final for a trivial reason — the top open is a terminal object of every structured-arrow
category over it.

## Main results

* `TopologicalSpace.Opens.map_final`: `TopologicalSpace.Opens.map g` is a final functor.
* `RingedSpaceModuleAdjunction.isIso_modulePullbackUnitToUnit`: `f^* 𝒪_Y ≅ 𝒪_X` for
  every morphism of ringed spaces, as an instance.
* `RingedSpaceModuleAdjunction.modulePullbackUnitIso` is that isomorphism, pinned by
  `RingedSpaceModuleAdjunction.modulePullbackUnitIso_hom` and, through the hom-set
  bijection, by
  `RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit`.
* `RingedSpaceModuleAdjunction.modulePullbackFreeIso`: `f^* (𝒪_Y^I) ≅ 𝒪_X^I` for every index
  type, from the same finality.
* `RingedSpaceModuleAdjunction.unit_app_unit`: **the generator formula.** The unit of
  `f^* ⊣ f_*` at `𝒪_Y` is the structure-sheaf map followed by `f_*` of the inverse of
  `modulePullbackUnitIso`. Equivalently
  `RingedSpaceModuleAdjunction.unit_app_unit_comp_modulePushforward_map`, which has no
  inverse in it.
* `RingedSpaceModuleAdjunction.modulePushforwardPullbackUnitIso` is
  `f_* f^* 𝒪_Y ≅ f_* 𝒪_X`, the tensor description at `M = 𝒪_Y`.
* `RingedSpaceModuleAdjunction.epi_unit_app_unit_iff`: the unit at `𝒪_Y` is an
  epimorphism exactly when the structure-sheaf map is. For a closed immersion the right-hand
  side is a hypothesis, so the left-hand side holds.
* `RingedSpaceModuleAdjunction.epi_unit_app_unit_of_isClosedImmersion`: for a closed
  immersion of ringed spaces the unit at the structure sheaf is an epimorphism, which is the
  second assertion of [Stacks Project, Tag 01R3] part (1) at `M = 𝒪_Y`.
* `RingedSpaceModuleAdjunction.epi_unit_app_of_epi`: the naturality step that transports
  epimorphy of the unit along an epimorphism `N ⟶ M`. Its second hypothesis — that `f_* f^*`
  takes that epimorphism to an epimorphism — is exactly the exactness of pushforward along a
  closed immersion, and is left as a hypothesis because nothing in the library yet supplies it
  for sheaves of modules.

## Implementation notes

The finality of `TopologicalSpace.Opens.map g` is *not* an instance of
`CategoryTheory.Functor.final_of_isRightAdjoint`: `TopologicalSpace.Opens.map g` has a right
adjoint, not a left one, so that route would prove it initial. What makes it final is that
`V = ⊤` is a terminal object of `CategoryTheory.StructuredArrow U (Opens.map g)`, since
`U ≤ g⁻¹ ⊤` always and the morphisms of a poset are unique.

No tensor product of sheaves of modules is used, or needed, for the case `M = 𝒪_Y`: the
right-hand side of the tensor formula is then `𝒪_Y ⊗_{𝒪_Y} f_* 𝒪_X = f_* 𝒪_X`, and the
content is the identification of the unit with `f^♯`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace TopologicalSpace.Opens

/-- **The inverse-image functor on opens is final.** For a continuous map `g : X ⟶ Y` and an
open `U` of `X`, the category of opens `V` of `Y` with `U ≤ g⁻¹ V` has the terminal object
`V = ⊤`, so it is connected. -/
instance map_final {X Y : TopCat.{u}} (g : X ⟶ Y) : (Opens.map g).Final where
  out U := by
    let t : StructuredArrow U (Opens.map g) := StructuredArrow.mk (Y := ⊤) (homOfLE le_top)
    have h : ∀ A : StructuredArrow U (Opens.map g), A ⟶ t := fun _ =>
      StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)
    have : Nonempty (StructuredArrow U (Opens.map g)) := ⟨t⟩
    exact zigzag_isConnected fun A B => (Zigzag.of_hom (h A)).trans (Zigzag.of_inv (h B))

end TopologicalSpace.Opens

namespace RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **`f^* 𝒪_Y ≅ 𝒪_X` for every morphism of ringed spaces.** The transpose of the
structure-sheaf map is an isomorphism.

This generalises `AlgebraicGeometry.RingedSpace.isIso_modulePullbackUnitToUnit_ofRestrict`,
which is the case of the open immersion `ι_U`, to an arbitrary morphism; the proof is
different, and uses no description of the sections of a pullback. By
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` it suffices that the functor of sites
`TopologicalSpace.Opens.map f.hom.base` be final, which is
`TopologicalSpace.Opens.map_final`. -/
@[sga "4 IV 13.4" "special case"]
instance isIso_modulePullbackUnitToUnit : IsIso (modulePullbackUnitToUnit f) :=
  inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f)))

/-- **`f^* 𝒪_Y ≅ 𝒪_X`**, as an isomorphism. Pinned by
`RingedSpaceModuleAdjunction.modulePullbackUnitIso_hom`, and through the hom-set
bijection of `f^* ⊣ f_*` by
`RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit`: its transpose is the
structure-sheaf map. -/
noncomputable def modulePullbackUnitIso :
    (modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)) ≅
      SheafOfModules.unit (structureSheafRing X) :=
  asIso (modulePullbackUnitToUnit f)

/-- The forward direction of `RingedSpaceModuleAdjunction.modulePullbackUnitIso` is the
transpose of the structure-sheaf map. -/
@[simp]
theorem modulePullbackUnitIso_hom :
    (modulePullbackUnitIso f).hom = modulePullbackUnitToUnit f :=
  rfl

/-- **`f^* (𝒪_Y^I) ≅ 𝒪_X^I` for every morphism of ringed spaces and every index type.** The
pullback of a free sheaf of modules is free on the same index type.

Like `RingedSpaceModuleAdjunction.modulePullbackUnitIso` this needs nothing of `f` beyond
finality of the functor of sites, `TopologicalSpace.Opens.map_final`: it is Mathlib's
`CategoryTheory.SheafOfModules.pullbackObjFreeIso` read for `f^* ⊣ f_*`. -/
noncomputable def modulePullbackFreeIso (I : Type u) :
    (modulePullback f).obj (SheafOfModules.free (R := structureSheafRing Y) I) ≅
      SheafOfModules.free (R := structureSheafRing X) I :=
  SheafOfModules.pullbackObjFreeIso (structureSheafHom f) I

/-- **The generator formula for the unit at the structure sheaf, without an inverse.** The unit
of `f^* ⊣ f_*` at `𝒪_Y`, followed by `f_*` of the identification `f^* 𝒪_Y ≅ 𝒪_X`, is the
structure-sheaf map `f^♯`.

On sections this says that the unit sends `a ∈ 𝒪_Y(V)` to `f^♯(a)`, which is the image of
`a ⊗ 1` under the tensor description `f_* f^* 𝒪_Y ≅ 𝒪_Y ⊗_{𝒪_Y} f_* 𝒪_X = f_* 𝒪_X`. It is
`RingedSpaceModuleAdjunction.homEquiv_modulePullbackUnitToUnit` with the hom-set
bijection written out. -/
theorem unit_app_unit_comp_modulePushforward_map :
    (modulePullbackPushforwardAdjunction f).unit.app (SheafOfModules.unit (structureSheafRing Y)) ≫
        (modulePushforward f).map (modulePullbackUnitToUnit f) =
      structureSheafModuleHom f :=
  homEquiv_modulePullbackUnitToUnit f

/-- **The generator formula for the unit at the structure sheaf.** The unit of `f^* ⊣ f_*` at
`𝒪_Y` is the structure-sheaf map read through `f_*` of the inverse of
`RingedSpaceModuleAdjunction.modulePullbackUnitIso`. -/
theorem unit_app_unit :
    (modulePullbackPushforwardAdjunction f).unit.app (SheafOfModules.unit (structureSheafRing Y)) =
      structureSheafModuleHom f ≫
        (modulePushforward f).map (modulePullbackUnitIso f).inv := by
  rw [← unit_app_unit_comp_modulePushforward_map f, Category.assoc, ← Functor.map_comp,
    modulePullbackUnitIso, asIso_inv, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- **The tensor description of `f_* f^* M` at `M = 𝒪_Y`**: `f_* f^* 𝒪_Y ≅ f_* 𝒪_X`, the
right-hand side being `𝒪_Y ⊗_{𝒪_Y} f_* 𝒪_X`. The comparison is pinned on generators by
`RingedSpaceModuleAdjunction.unit_app_unit`: precomposing it with the unit gives the
structure-sheaf map, so a section `a` goes to `a ⊗ 1 = f^♯(a)`. -/
noncomputable def modulePushforwardPullbackUnitIso :
    (modulePushforward f).obj
        ((modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y))) ≅
      (modulePushforward f).obj (SheafOfModules.unit (structureSheafRing X)) :=
  (modulePushforward f).mapIso (modulePullbackUnitIso f)

/-- The unit of `f^* ⊣ f_*` at `𝒪_Y` is an epimorphism exactly when the structure-sheaf map
`f^♯ : 𝒪_Y ⟶ f_* 𝒪_X` is one. For a closed immersion of ringed spaces the right-hand side is a
defining hypothesis (`AlgebraicGeometry.SheafOfModules.IsClosedImmersion`), so the unit at the
structure sheaf is an epimorphism. -/
theorem epi_unit_app_unit_iff :
    Epi ((modulePullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit (structureSheafRing Y))) ↔
      Epi (structureSheafModuleHom f) := by
  rw [unit_app_unit f]
  exact epi_comp_iff_of_isIso _ _

/-- **For a closed immersion of ringed spaces the unit at the structure sheaf is an
epimorphism.** By `RingedSpaceModuleAdjunction.epi_unit_app_unit_iff` this is exactly
the surjectivity of `f^♯`, which is one of the three defining conditions of
`AlgebraicGeometry.SheafOfModules.IsClosedImmersion`.

Together with `RingedSpaceModuleAdjunction.unit_app_unit` this is the second assertion of
[Stacks Project, Tag 01R3] part (1) in the case `M = 𝒪_Y`: the unit is the epimorphism
`𝒪_Y ⟶ f_* 𝒪_X = 𝒪_Y ⊗_{𝒪_Y} f_* 𝒪_X`. -/
instance epi_unit_app_unit_of_isClosedImmersion
    [AlgebraicGeometry.SheafOfModules.IsClosedImmersion f] :
    Epi ((modulePullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit (structureSheafRing Y))) :=
  (epi_unit_app_unit_iff f).mpr
    AlgebraicGeometry.SheafOfModules.IsClosedImmersion.structureSheafMap_epi

/-- **The naturality step of the generator argument.** If `p : N ⟶ M` is an epimorphism, if the
unit of `f^* ⊣ f_*` is an epimorphism at `N`, and if `f_* f^*` takes `p` to an epimorphism,
then the unit is an epimorphism at `M`.

The last hypothesis is where the geometry enters: `f^*` is a left adjoint, so it always
preserves epimorphisms, but `f_*` does so only under a hypothesis on `f` — for a closed
immersion it is the exactness of pushforward, [Stacks Project, Tag 01AX]. -/
theorem epi_unit_app_of_epi {M N : SheafOfModules.{u} (structureSheafRing Y)} (p : N ⟶ M) [Epi p]
    (hN : Epi ((modulePullbackPushforwardAdjunction f).unit.app N))
    (hp : Epi ((modulePushforward f).map ((modulePullback f).map p))) :
    Epi ((modulePullbackPushforwardAdjunction f).unit.app M) := by
  have := hN
  have := hp
  have h : p ≫ (modulePullbackPushforwardAdjunction f).unit.app M =
      (modulePullbackPushforwardAdjunction f).unit.app N ≫
        (modulePushforward f).map ((modulePullback f).map p) := by
    simp
  have : Epi (p ≫ (modulePullbackPushforwardAdjunction f).unit.app M) := by
    rw [h]; exact epi_comp _ _
  exact epi_of_epi p _

end RingedSpaceModuleAdjunction

end
