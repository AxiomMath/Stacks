module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a sheaf of modules preserves surjections

Let `Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)` be a finite-product-preserving functor between
categories of sheaves of sets on two sites, let `O` be a sheaf of rings on `(D, K)`, and let
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor J Φ O` be the inverse-image functor on
sheaves of modules of Stacks 03D2. This file proves that this functor carries epimorphisms to
epimorphisms as soon as `Φ` carries locally surjective morphisms to locally surjective
morphisms — in particular whenever `Φ` is the inverse image of a morphism of topoi.

This is the step that every "the inverse image preserves property `P`" statement of Stacks
03DO rests on: finite type, local generation by `r` sections and finite presentation are each
the existence, locally, of a surjection from a finite free module, and transporting such a
surjection is exactly this lemma together with the finite-free comparison.

## Main results

* `Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMap`: the underlying
  morphism of sheaves of sets of an inverse-image morphism of modules is `Φ` applied to the
  underlying morphism of sheaves of sets — on the nose.
* `Stacks.Sheaves.ToposPullback.isLocallySurjective_pullbackModuleMap`: the inverse image of a
  locally surjective morphism is locally surjective.
* `Stacks.Sheaves.ToposPullback.epi_pullbackModuleMap` and
  `Stacks.Sheaves.ToposPullback.preservesEpimorphisms_pullbackModuleFunctor`: the inverse-image
  functor on sheaves of modules preserves epimorphisms.
* `Stacks.SheafOfModules.Presentation.isFinite_map`: Mathlib's `Presentation.map` preserves
  finiteness of a presentation, at general universes.

## Implementation notes

The whole proof rests on one `rfl`: by construction of Stacks 03D2 in `ToposPullback.lean`, the
underlying presheaf of abelian groups of `pullbackModuleObj J Φ O G` has as its sections over
`X` the sections over `X` of `Φ` applied to the underlying sheaf of *sets* of `G`, and the
inverse image of a morphism acts as `Φ` applied to that morphism. That is the content of
`pullbackRingSheafIso` and of the `moduleIso` field of `PullbackModuleData` both being
`Iso.refl`. So `moduleSheafFunctor_map_pullbackModuleMap` holds by `hom_ext_sections` and
`rfl`, and no comparison isomorphism has to be transported anywhere.

Local surjectivity is used as the pivot rather than epimorphy, because local surjectivity is a
condition on underlying *functions* — it is the same statement for a morphism of sheaves of
modules, of sheaves of abelian groups, and of sheaves of sets, and the two transfers are
`Presheaf.IsLocallySurjective.imageSieve_mem` in either direction with no hypotheses at all.
Epimorphy, by contrast, is not: the direction `Epi → locally surjective` for sheaves of modules
is `Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi`, which needs the abelian structure
and hence `HasSheafify K AddCommGrpCat.{ww'}`; the direction back is
`epi_of_isLocallySurjective`, which needs nothing. The hypotheses below are therefore
asymmetric on purpose: `HasSheafify` and `WEqualsLocallyBijective` are required for the *source*
site `K` only.

The hypothesis on `Φ` is stated as preservation of local surjectivity rather than as
`Φ.PreservesEpimorphisms`, for the same reason. Converting the latter into the former needs
`Epi → locally surjective` for `Type`-valued sheaves, i.e. `HasSheafify J (Type ww)`, which
forces `ww = max uu vv` and so would silently narrow a universe that the statement otherwise
leaves free. `isLocallySurjective_map_of_preservesEpimorphisms` records that conversion
separately, under exactly that extra hypothesis, so that a caller who is at those universes can
use it and a caller who is not is not forced into them.

`Presentation.isFinite_map` is included here because it is the other half of the same
machine and has the same universe story; see its own docstring for why the repository's
existing copy, pinned to `Type 0`, cannot serve.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (O : Sheaf K RingCat.{ww'}) {G G' : SheafOfModules.{ww'} O}

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The underlying morphism of sheaves of sets of the inverse image of a morphism of sheaves of
modules is `Φ` applied to its underlying morphism of sheaves of sets. This is an equality, not
an isomorphism: the inverse-image module is built so that its sections *are* the sections of
`Φ` applied to the underlying sheaf of sets. -/
lemma moduleSheafFunctor_map_pullbackModuleMap (φ : G ⟶ G') :
    (moduleSheafFunctor (pullbackRingSheaf J Φ O)).map (pullbackModuleMap J Φ O φ) =
      Φ.map ((moduleSheafFunctor O).map φ) :=
  hom_ext_sections fun _ _ => rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The inverse image of a locally surjective morphism of sheaves of modules is locally
surjective, provided `Φ` carries locally surjective morphisms of sheaves of sets to locally
surjective morphisms. -/
theorem isLocallySurjective_pullbackModuleMap
    (hΦ : ∀ {A B : Sheaf K (Type ww')} (ψ : A ⟶ B), Sheaf.IsLocallySurjective ψ →
      Sheaf.IsLocallySurjective (Φ.map ψ))
    (φ : G ⟶ G') (hφ : Sheaf.IsLocallySurjective ((moduleSheafFunctor O).map φ)) :
    Sheaf.IsLocallySurjective
      ((moduleSheafFunctor (pullbackRingSheaf J Φ O)).map (pullbackModuleMap J Φ O φ)) := by
  rw [moduleSheafFunctor_map_pullbackModuleMap]
  exact hΦ _ hφ

variable [HasSheafify K AddCommGrpCat.{ww'}] [K.WEqualsLocallyBijective AddCommGrpCat.{ww'}]

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- **Stacks 03DO**, the surjectivity step: the inverse image of an epimorphism of sheaves of
modules is an epimorphism, provided `Φ` preserves local surjectivity. -/
theorem epi_pullbackModuleMap
    (hΦ : ∀ {A B : Sheaf K (Type ww')} (ψ : A ⟶ B), Sheaf.IsLocallySurjective ψ →
      Sheaf.IsLocallySurjective (Φ.map ψ))
    (φ : G ⟶ G') [Epi φ] : Epi (pullbackModuleMap J Φ O φ) :=
  have h := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi φ
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ⟨(isLocallySurjective_pullbackModuleMap J Φ O hΦ φ ⟨h.imageSieve_mem⟩).imageSieve_mem⟩

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The inverse-image functor on sheaves of modules preserves epimorphisms, provided `Φ`
preserves local surjectivity. -/
theorem preservesEpimorphisms_pullbackModuleFunctor
    (hΦ : ∀ {A B : Sheaf K (Type ww')} (ψ : A ⟶ B), Sheaf.IsLocallySurjective ψ →
      Sheaf.IsLocallySurjective (Φ.map ψ)) :
    (pullbackModuleFunctor J Φ O).PreservesEpimorphisms where
  preserves φ _hφ := epi_pullbackModuleMap J Φ O hΦ φ

end Stacks.Sheaves.ToposPullback

/-! ## Deriving the hypothesis on `Φ` from preservation of epimorphisms -/

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [Φ.PreservesEpimorphisms]
  [HasSheafify J (Type ww)] [HasSheafify K (Type ww)]

/-- A functor between categories of sheaves of sets that preserves epimorphisms preserves local
surjectivity, once both categories have sheafification — for `Type`-valued sheaves local
surjectivity and epimorphy agree. The sheafification hypotheses are the price of the
conversion, and are why the results above take preservation of local surjectivity as their
hypothesis instead. -/
theorem isLocallySurjective_map_of_preservesEpimorphisms
    {A B : Sheaf K (Type ww)} (ψ : A ⟶ B) (hψ : Sheaf.IsLocallySurjective ψ) :
    Sheaf.IsLocallySurjective (Φ.map ψ) := by
  rw [Sheaf.isLocallySurjective_iff_epi] at hψ ⊢
  exact Φ.map_epi ψ

end Stacks.Sheaves.ToposPullback

/-! ## Finiteness of a transported presentation -/

namespace Stacks.SheafOfModules

open CategoryTheory CategoryTheory.Limits

universe u v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transporting a presentation of a sheaf of modules along a colimit-preserving functor that
carries the structure sheaf to the structure sheaf preserves finiteness of the presentation: the
index types of the generators and of the relations are literally unchanged.

The repository already has this as `SheafOfModules.Presentation.IsFinite.map`, but
with **every universe pinned to `0`** — both sites `Type` with `Category.{0}`, both sheaves of
rings in `RingCat.{0}`, and `PreservesColimitsOfSize.{0, 0}`. That is sound for its consumers,
whose sites are all `Opens X` for `X : Type`, and is useless for a statement about a morphism
of ringed topoi or ringed sites, where the two sites carry four independent universes. Nothing
is pinned here. That `R` and `S` share the universe `u` is forced, not chosen:
`SheafOfModules.Presentation.map`, and behind it `SheafOfModules.free`, are stated that way,
because `free I` requires its index type to live in the ring universe. -/
@[ega "0 5.2.5" "special case"]
instance Presentation.isFinite_map {M : _root_.SheafOfModules.{u} R}
    (P : M.Presentation) (F : _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : _root_.SheafOfModules.unit S ≅ F.obj (_root_.SheafOfModules.unit R)) [P.IsFinite] :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by
    rw [_root_.SheafOfModules.Presentation.map_generators_I]
    exact (_root_.SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := P)).finite⟩
  isFiniteType_relations := ⟨by
    rw [_root_.SheafOfModules.Presentation.map_relations_I]
    exact (_root_.SheafOfModules.Presentation.IsFinite.isFiniteType_relations (p := P)).finite⟩

end Stacks.SheafOfModules

end
