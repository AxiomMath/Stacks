module

import StacksFrontier.Topology.Sheaves.AlgebraicStructure.FactorThroughInjective
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Monoidal.Mon


/-!
# Checking that a map of sheaves of sets is a homomorphism on stalks

Stacks 007W: let `X` be a topological space, let `(C, F)` be a type of algebraic structure
(Stacks 007M, formalized as `AlgebraicStructureType`), let `𝓕`, `𝓖` be sheaves on `X` with
values in `C`, and let `φ : 𝓕 → 𝓖` be a map of the *underlying sheaves of sets*. If for every
`x ∈ X` the induced map on stalks `𝓕_x → 𝓖_x` is a morphism of algebraic structures, then `φ`
is a morphism of sheaves with values in `C`.

## Modelling

A `C`-valued presheaf on `X` is a `TopCat.Presheaf S.C X`, and its underlying presheaf of sets
is `𝓕 ⋙ S.F`; a map of the underlying sheaves of sets is therefore a natural transformation
`φ : 𝓕 ⋙ S.F ⟶ 𝓖 ⋙ S.F`, and the conclusion "`φ` is a morphism of sheaves with values in `C`"
is `∃! α : 𝓕 ⟶ 𝓖, CategoryTheory.whiskerRight α S.F = φ`.

Stalks are taken in `C`. A type of algebraic structure only provides *filtered* colimits, so
`TopCat.Presheaf.stalk` (which asks for all colimits) does not apply and the stalk is built here
as `stalkC`, the colimit of `(OpenNhds.inclusion x).op ⋙ 𝓕` — literally the same diagram, whose
colimit exists because `(OpenNhds x)ᵒᵖ` is filtered. `germC` is the corresponding germ map.

The hypothesis "the stalk map is a morphism of algebraic structures" is
`stalkHom S 𝓕 𝓖 φ`: a family of `C`-morphisms `ψ x : 𝓕_x ⟶ 𝓖_x` whose underlying functions
agree with `φ` on germs. Because `F` preserves the filtered colimit computing the stalk, germs
are jointly surjective onto `F (𝓕_x)`, so such a `ψ x` is unique and is exactly the stalk map of
`φ` regarded as a `C`-morphism.

## Proof

Following the source: for an open `U`, form in `C` the product `∏_{x ∈ U} 𝓕_x` and the germ map
`germPi`, giving the square

```
𝓕(U) ---germPi---> ∏_{x ∈ U} 𝓕_x
                        |
                     ∏ ψ x
                        v
𝓖(U) ---germPi---> ∏_{x ∈ U} 𝓖_x
```

whose bottom arrow is injective on underlying sets (Stacks 0079, via
`TopCat.Presheaf.section_ext` for the sheaf of sets `𝓖 ⋙ S.F`) and which commutes on underlying
sets by the hypothesis on stalks. Stacks 007P
(`factor_through_injective_image_subset`) then produces the `C`-morphism `𝓕(U) ⟶ 𝓖(U)`, whose
underlying function must be `φ.app (op U)` by that same injectivity. Naturality of the resulting
family follows from naturality of `φ` because `F` is faithful.

Only the sheaf condition on `𝓖` enters the argument; the hypothesis that `𝓕` is a sheaf is
recorded as in the source but is not needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace ExactnessPoints

variable (S : AlgebraicStructureType.{v, u}) {X : TopCat.{v}}

/-- The diagram over the (filtered) poset of open neighbourhoods of `x` whose colimit is the
stalk of `𝓕` at `x`. -/
abbrev stalkDiagram (𝓕 : X.Presheaf S.C) (x : X) : (OpenNhds x)ᵒᵖ ⥤ S.C :=
  (OpenNhds.inclusion x).op ⋙ 𝓕

/-- The stalk diagram has a colimit: its shape `(OpenNhds x)ᵒᵖ` is filtered, and a type of
algebraic structure supplies colimits of filtered shapes. -/
instance hasColimitStalkDiagram (𝓕 : X.Presheaf S.C) (x : X) :
    HasColimit (stalkDiagram S 𝓕 x) :=
  have : HasColimitsOfShape (OpenNhds x)ᵒᵖ S.C :=
    HasFilteredColimitsOfSize.HasColimitsOfShape _
  inferInstance

/-- The stalk at `x` of a presheaf with values in a type of algebraic structure `(C, F)`.

This is `TopCat.Presheaf.stalk`'s diagram, but `TopCat.Presheaf.stalk` requires all colimits in
`C` whereas a type of algebraic structure only supplies filtered ones — and the shape
`(OpenNhds x)ᵒᵖ` is filtered. -/
noncomputable def stalkC (𝓕 : X.Presheaf S.C) (x : X) : S.C :=
  colimit (stalkDiagram S 𝓕 x)

/-- The germ map `𝓕(U) ⟶ 𝓕_x` for `x ∈ U`, in `C`. -/
noncomputable def germC (𝓕 : X.Presheaf S.C) (U : Opens X) (x : X) (hx : x ∈ U) :
    𝓕.obj (op U) ⟶ stalkC S 𝓕 x :=
  colimit.ι (stalkDiagram S 𝓕 x) (op ⟨U, hx⟩)

/-- `F` preserves the filtered colimit computing `stalkC`, so it identifies the underlying set of
the `C`-valued stalk with the stalk of the underlying sheaf of sets. -/
noncomputable def stalkCIso (𝓕 : X.Presheaf S.C) (x : X) :
    S.F.obj (stalkC S 𝓕 x) ≅ TopCat.Presheaf.stalk (𝓕 ⋙ S.F) x :=
  have : PreservesColimitsOfShape (OpenNhds x)ᵒᵖ S.F :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
  preservesColimitIso S.F (stalkDiagram S 𝓕 x)

/-- `stalkCIso` matches the germ maps: the underlying function of the `C`-valued germ map,
followed by the identification of stalks, is the germ map of the underlying sheaf of sets. -/
@[simp]
lemma map_germC_stalkCIso_hom (𝓕 : X.Presheaf S.C) (U : Opens X) (x : X) (hx : x ∈ U) :
    S.F.map (germC S 𝓕 U x hx) ≫ (stalkCIso S 𝓕 x).hom =
      TopCat.Presheaf.germ (𝓕 ⋙ S.F) U x hx :=
  have : PreservesColimitsOfShape (OpenNhds x)ᵒᵖ S.F :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
  ι_preservesColimitIso_hom S.F (stalkDiagram S 𝓕 x) (op ⟨U, hx⟩)

/-- The elementwise form of `map_germC_stalkCIso_hom`: `stalkCIso` sends the `C`-valued germ of
a section to its germ in the stalk of the underlying sheaf of sets. -/
lemma map_germC_apply_stalkCIso_hom (𝓕 : X.Presheaf S.C) (U : Opens X) (x : X) (hx : x ∈ U)
    (s : S.F.obj (𝓕.obj (op U))) :
    (stalkCIso S 𝓕 x).hom (S.F.map (germC S 𝓕 U x hx) s) =
      TopCat.Presheaf.germ (𝓕 ⋙ S.F) U x hx s :=
  ConcreteCategory.congr_hom (map_germC_stalkCIso_hom S 𝓕 U x hx) s

/-- The hypothesis of Stacks 007W: a family of `C`-morphisms on stalks whose underlying functions
are the ones induced by `φ`.

Concretely, `ψ x : 𝓕_x ⟶ 𝓖_x` is a morphism of algebraic structures which on underlying sets
sends the germ at `x` of a section `s` over `U` to the germ at `x` of `φ_U s`. Since `F`
preserves the filtered colimit computing the stalk, germs cover `F (𝓕_x)`, so `ψ x` is forced to
be the stalk map of `φ`. -/
structure StalkHom (𝓕 𝓖 : X.Presheaf S.C) (φ : 𝓕 ⋙ S.F ⟶ 𝓖 ⋙ S.F) where
  /-- The morphism of algebraic structures on the stalk at `x`. -/
  ψ (x : X) : stalkC S 𝓕 x ⟶ stalkC S 𝓖 x
  /-- Its underlying function is the map induced by `φ` on stalks. -/
  germ_ψ (x : X) (U : Opens X) (hx : x ∈ U) (s : S.F.obj (𝓕.obj (op U))) :
    S.F.map (ψ x) (S.F.map (germC S 𝓕 U x hx) s) =
      S.F.map (germC S 𝓖 U x hx) (φ.app (op U) s)

namespace Aux

variable {S} {𝓕 𝓖 : X.Presheaf S.C} {φ : 𝓕 ⋙ S.F ⟶ 𝓖 ⋙ S.F}

/-- Elements of the underlying set of a product in `C` are determined by their components: `F`
preserves the product, so `F` of the product cone is a limit cone in `Type v`, and a limit cone
in `Type v` is jointly monic (test with maps out of `PUnit`). -/
lemma map_pi_ext {ι : Type v} (g : ι → S.C) (a b : S.F.obj (∏ᶜ g))
    (h : ∀ i, S.F.map (Limits.Pi.π g i) a = S.F.map (Limits.Pi.π g i) b) : a = b := by
  have hc : IsLimit (S.F.mapCone (limit.cone (Discrete.functor g))) :=
    isLimitOfPreserves S.F (limit.isLimit _)
  have key : TypeCat.ofHom (fun _ : PUnit.{v + 1} => a) =
      TypeCat.ofHom (fun _ : PUnit.{v + 1} => b) := by
    refine hc.hom_ext ?_
    rintro ⟨i⟩
    refine ConcreteCategory.hom_ext _ _ fun _ => ?_
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    simpa using h i
  simpa using ConcreteCategory.congr_hom key PUnit.unit

/-- `∏_{x ∈ U} 𝓕_x`, formed in `C`. -/
noncomputable abbrev stalkPi (𝓕 : X.Presheaf S.C) (U : Opens X) : S.C :=
  ∏ᶜ fun x : U => stalkC S 𝓕 x

/-- The map `𝓕(U) ⟶ ∏_{x ∈ U} 𝓕_x` assembling all germs. -/
noncomputable def germPi (𝓕 : X.Presheaf S.C) (U : Opens X) :
    𝓕.obj (op U) ⟶ stalkPi 𝓕 U :=
  Limits.Pi.lift fun x : U => germC S 𝓕 U x.1 x.2

/-- The component of `germPi` at a point `x` of `U` is the germ map at `x`. -/
@[reassoc (attr := simp)]
lemma germPi_π (𝓕 : X.Presheaf S.C) (U : Opens X) (x : U) :
    germPi 𝓕 U ≫ Limits.Pi.π _ x = germC S 𝓕 U x.1 x.2 :=
  Limits.Pi.lift_comp_π _ _

/-- The component at `x` of the underlying function of `germPi` is the underlying function of the
germ map at `x`. -/
private lemma map_π_map_germPi_apply (𝓕 : X.Presheaf S.C) (U : Opens X) (x : U)
    (s : S.F.obj (𝓕.obj (op U))) :
    S.F.map (Limits.Pi.π _ x) (S.F.map (germPi 𝓕 U) s) = S.F.map (germC S 𝓕 U x.1 x.2) s := by
  rw [← S.F.map_comp_apply, germPi_π]

/-- The underlying function of `germPi` is injective when `𝓖 ⋙ S.F` is a sheaf: this is
Stacks 0079 transported through `stalkCIso`. -/
lemma injective_map_germPi (h𝓖 : TopCat.Presheaf.IsSheaf (𝓖 ⋙ S.F)) (U : Opens X) :
    Function.Injective (S.F.map (germPi 𝓖 U)) := by
  intro s t hst
  -- Two sections of the sheaf of sets `𝓖 ⋙ S.F` with the same germs everywhere are equal.
  refine TopCat.Presheaf.section_ext ⟨_, h𝓖⟩ U s t fun x hx => ?_
  -- Read off the germ at `x` from `germPi` by composing with the projection and `stalkCIso`.
  have key : S.F.map (germC S 𝓖 U x hx) s = S.F.map (germC S 𝓖 U x hx) t := by
    have h := congrArg (S.F.map (Limits.Pi.π (fun x : U => stalkC S 𝓖 x) ⟨x, hx⟩)) hst
    rwa [map_π_map_germPi_apply, map_π_map_germPi_apply] at h
  rw [← map_germC_apply_stalkCIso_hom S 𝓖 U x hx s,
    ← map_germC_apply_stalkCIso_hom S 𝓖 U x hx t, key]

/-- The `C`-morphism `∏_{x ∈ U} 𝓕_x ⟶ ∏_{x ∈ U} 𝓖_x` induced by a family of stalk maps. -/
noncomputable def stalkPiMap (T : StalkHom S 𝓕 𝓖 φ) (U : Opens X) :
    stalkPi 𝓕 U ⟶ stalkPi 𝓖 U :=
  Limits.Pi.map fun x : U => T.ψ x.1

/-- The component of `stalkPiMap` at a point `x` of `U` is the given stalk map `ψ x`. -/
@[reassoc (attr := simp)]
lemma stalkPiMap_π (T : StalkHom S 𝓕 𝓖 φ) (U : Opens X) (x : U) :
    stalkPiMap T U ≫ Limits.Pi.π _ x = Limits.Pi.π _ x ≫ T.ψ x.1 :=
  Limits.Pi.map_π _ _

/-- The square of the source commutes on underlying sets: the germ family of `φ_U s` is the image
under the stalk maps of the germ family of `s`. -/
lemma germPi_comp_apply (T : StalkHom S 𝓕 𝓖 φ) (U : Opens X)
    (s : S.F.obj (𝓕.obj (op U))) :
    S.F.map (germPi 𝓕 U ≫ stalkPiMap T U) s =
      S.F.map (germPi 𝓖 U) (φ.app (op U) s) := by
  -- It suffices to compare the two elements componentwise.
  refine map_pi_ext _ _ _ fun x => ?_
  rw [S.F.map_comp_apply, ← S.F.map_comp_apply _ (Limits.Pi.π _ x), stalkPiMap_π,
    S.F.map_comp_apply, map_π_map_germPi_apply, map_π_map_germPi_apply]
  exact T.germ_ψ x.1 U x.2 s

end Aux

open Aux in
/-- **Stacks 007W (Lemma 6.15.6).** Let `X` be a topological space, let `(C, F)` be a type of
algebraic structure, let `𝓕` and `𝓖` be sheaves on `X` with values in `C`, and let
`φ : 𝓕 ⋙ F ⟶ 𝓖 ⋙ F` be a map of the underlying sheaves of sets. If for every `x ∈ X` the
induced map `𝓕_x ⟶ 𝓖_x` is a morphism of algebraic structures, then `φ` is (uniquely) a
morphism of sheaves with values in `C`.

The hypothesis on stalks is `StalkHom S 𝓕 𝓖 φ`, and "is a morphism of sheaves with values in
`C`" is: there is a unique `α : 𝓕 ⟶ 𝓖` in `C`-valued presheaves with
`Functor.whiskerRight α S.F = φ`.

Only the sheaf condition on `𝓖` is used. -/
@[stacks 007W]
theorem exists_unique_hom_of_stalkHom {𝓕 𝓖 : X.Presheaf S.C}
    (_h𝓕 : TopCat.Presheaf.IsSheaf (𝓕 ⋙ S.F))
    (h𝓖 : TopCat.Presheaf.IsSheaf (𝓖 ⋙ S.F))
    (φ : 𝓕 ⋙ S.F ⟶ 𝓖 ⋙ S.F) (T : StalkHom S 𝓕 𝓖 φ) :
    ∃! α : 𝓕 ⟶ 𝓖, Functor.whiskerRight α S.F = φ := by
  -- For each open `U`, produce the unique `C`-morphism over `U` with underlying function `φ_U`.
  have step : ∀ U : Opens X, ∃ t : 𝓕.obj (op U) ⟶ 𝓖.obj (op U),
      S.F.map t = φ.app (op U) := by
    intro U
    have hinj : Function.Injective (S.F.map (germPi 𝓖 U)) := injective_map_germPi h𝓖 U
    -- Stacks 007P: factor `germPi 𝓕 U ≫ stalkPiMap` through the injective `germPi 𝓖 U`.
    -- The image containment: the witness over `s` is `φ_U s`.
    have hsub : Set.range (S.F.map (germPi 𝓕 U ≫ stalkPiMap T U)) ⊆
        Set.range (S.F.map (germPi 𝓖 U)) := by
      rintro _ ⟨s, rfl⟩
      exact ⟨φ.app (op U) s, (germPi_comp_apply T U s).symm⟩
    obtain ⟨t, ht⟩ := factor_through_injective_image_subset S _ _ _
      (germPi 𝓕 U ≫ stalkPiMap T U) (germPi 𝓖 U) hinj hsub
    refine ⟨t, ConcreteCategory.hom_ext _ _ fun s => ?_⟩
    -- `F t` and `φ_U` have the same germs everywhere, hence agree.
    refine hinj ?_
    have h₁ : S.F.map (t ≫ germPi 𝓖 U) s = S.F.map (germPi 𝓖 U) (φ.app (op U) s) := by
      rw [← ht]; exact germPi_comp_apply T U s
    simpa [S.F.map_comp, ConcreteCategory.comp_apply] using h₁
  choose t ht using step
  refine ⟨{ app := fun U => t U.unop, naturality := ?_ }, ?_, ?_⟩
  · -- Naturality: apply the faithful `F` and use naturality of `φ`.
    intro U V i
    refine S.F.map_injective ?_
    have := φ.naturality i
    simpa [S.F.map_comp, ht] using this
  · refine NatTrans.ext (funext fun U => ?_)
    exact ht U.unop
  · -- Uniqueness: `F` is faithful.
    intro α hα
    refine NatTrans.ext (funext fun U => S.F.map_injective ?_)
    rw [ht U.unop]
    simpa using NatTrans.congr_app hα U

end ExactnessPoints
