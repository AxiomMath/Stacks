module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDual
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.MorphismGluing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AffineBaseAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageRestrictOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 088B with `α` characterized, and the locality of that characterization on the base

Let `π : X' ⟶ X` be a proper morphism of Noetherian schemes, let `𝒥, 𝒦 ⊆ 𝒪_X` be quasi-coherent
sheaves of ideals and set `ℐ = π^{-1}𝒥 𝒪_{X'}`. [Stacks, Tag 088B] produces, from an object
`(𝒢_n)` of `Coh(X, 𝒥)`, a coherent `𝒪_{X'}`-module `𝓕` and an isomorphism
`β : π^*(𝒢_n) ≅ 𝓕 ^∧`, a morphism

`α : (𝒢_n) ⟶ (π_*𝓕) ^∧`

whose levelwise kernels and cokernels are annihilated by a power of `𝒦`. Stacks characterizes
`α` by the requirement that each composite

`𝒢_n --α_n--> (π_*𝓕) / 𝒥 ⁿ⁺¹ (π_*𝓕) --δ_n--> π_*(𝓕 / ℐ ⁿ⁺¹ 𝓕)`

be the map `γ_n` of `Stacks.Coherent.directImageComparison`; that predicate is
`Stacks.Coherent.IsDirectImageCharacterized`. This file proves, at a general base, that such an
`α` exists for an algebraizable `(𝒢_n)`, that it is unique once `δ` is a monomorphism after
passing to the inverse limit, and that the characterization is local on the base.

## Main definitions

* `Stacks.Coherent.directImageQuotientComparisonApp`,
  `Stacks.Coherent.directImageQuotientComparisonSystem`: `δ` as a morphism of inverse systems
  `(π_*𝓕) ^∧ ⟶ π_*(𝓕 ^∧)`.

## Main results

* `Stacks.Coherent.isDirectImageCharacterized_iff_comp_directImageQuotientComparisonSystem`: the
  characterization of `α` is the single equation `α ≫ δ = γ`.
* `Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq`: two morphisms out of a
  completion with the same composite with `δ` are equal, provided the inverse limit of `δ` is a
  monomorphism.
* `Stacks.Coherent.directImageComparison_app_of_systemIso` and
  `Stacks.Coherent.isDirectImageCharacterized_of_systemIso`: `γ` and the characterization of `α`
  transported along an isomorphism of the system `(𝒢_n)`.
* `Stacks.Coherent.pullbackCompletionDescent_completionProjection`: the descent `b : π^*𝒢 ≅ 𝓕`
  of [Stacks, Tag 0883], followed by the `n`-th projection of `𝓕 ^∧`, is the pullback of the
  `n`-th projection of `𝒢 ^∧` followed by `β_n`.
* `Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_algebraization` and
  `Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_essImage`: for an
  algebraizable `(𝒢_n)` there is an `α` which is characterized and has its levelwise kernels and
  cokernels annihilated by a power of `𝒦`.
* `Stacks.Coherent.isDirectImageCharacterized_iff_restrictCover`: the characterization of `α` is
  local on the base.
* `Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover`: a characterized `α` is glued
  from characterized morphisms of the restricted systems over an open cover of the base which
  agree on overlaps.
* `Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine`:
  [Stacks, Tag 088B] over an affine base, with `α` characterized.

## Implementation notes

The map `Stacks.Coherent.properDirectImageCompletionMap` is the completion of
`c : 𝒢 ⟶ π_*π^*𝒢 ⟶ π_*𝓕` read through an algebraization `(𝒢_n) ≅ 𝒢 ^∧`. A map presented this
way cannot be restricted to an open of `X`, which inherits no algebraization; the
characterization can, by `Stacks.Coherent.isDirectImageCharacterized_iff_restrictCover`.

A monomorphism of inverse systems in `X.Modules` is a levelwise monomorphism, and the kernel of

`δ_m : (π_*𝓕) / 𝒥 ᵐ (π_*𝓕) ⟶ π_*(𝓕 / ℐ ᵐ 𝓕)`

is `π_*(ℐ ᵐ 𝓕) / 𝒥 ᵐ (π_*𝓕)`, which the uniform Artin–Rees bounds of [Stacks, Tag 02OB] squeeze
between powers of `𝒥` but do not kill. So `δ` is not a monomorphism; only its inverse limit is,
being an isomorphism by the theorem on formal functions [Stacks, Tag 02OC]. That theorem is
available here for global sections over a complete affine base
(`Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper`) but not in the relative form
`lim ((π_*𝓕) ^∧) ≅ lim (π_*(𝓕 ^∧))`, so
`Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq` takes the monomorphism as
the hypothesis `hmono`.

Over an affine open `U = Spec B` of the base, the local data of
`Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover` come from the affine case only
when `B` is complete along `𝒥(U)`: in general Grothendieck existence fails over `Spec B`, by
`Stacks.Coherent.essImage_completionFunctor_iff_essImage_fgModuleCat` at the local ring of a
node, and Stacks instead base changes along the flat map `Spec B ^∧ ⟶ Spec B`.

The annihilation half of the conclusion is not glued over a cover:
`Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` asks for one exponent working at every
level, which needs a finite cover.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization

/-! ### Transport of the characterization along an isomorphism of systems -/

section Transport

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData) (G G' : CoherentAdicSystems J)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

omit [IsProper f] in
/-- `γ` transported along an isomorphism of systems. Let `d : (𝒢_n) ≅ (𝒢'_n)` be an
isomorphism of inverse systems over the base, and let the two isomorphisms `β`, `β'` of
[Stacks, Tag 088B] correspond under it in the sense `hd`: that `π^*d_n` followed by `β'_n` is
`β_n`. Then `d_n` followed by the map `γ_n` of `(𝒢'_n)` is the map `γ_n` of `(𝒢_n)`. -/
public theorem directImageComparison_app_of_systemIso
    (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)
    (β' : (coherentAdicPullback f J).obj G' ≅ (completionFunctor X (J.comap f)).obj F)
    (d : G.obj ≅ G'.obj)
    (hd : ∀ n : ℕᵒᵖ, (Scheme.Modules.pullback f).map (d.hom.app n) ≫ β'.hom.hom.app n =
      β.hom.hom.app n) (n : ℕᵒᵖ) :
    d.hom.app n ≫ (directImageComparison f J G' F β').app n =
      (directImageComparison f J G F β).app n := by
  have hnat : d.hom.app n ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G'.obj.obj n) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj n) ≫
        (Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).map (d.hom.app n) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (d.hom.app n)
  rw [directImageComparison_app, directImageComparison_app, ← Category.assoc, hnat,
    Category.assoc, Functor.comp_map]
  exact congrArg (fun z =>
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (G.obj.obj n) ≫ z)
    (((Scheme.Modules.pushforward f).map_comp ((Scheme.Modules.pullback f).map (d.hom.app n))
      (β'.hom.hom.app n)).symm.trans (congrArg (Scheme.Modules.pushforward f).map (hd n)))

/-- The characterization of `α` transported along an isomorphism of systems. With `d`, `β` and
`β'` as in `Stacks.Coherent.directImageComparison_app_of_systemIso`, if `α'` is a characterized
map out of `(𝒢'_n)` then `d ≫ α'` is a characterized map out of `(𝒢_n)`. -/
public theorem isDirectImageCharacterized_of_systemIso
    (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)
    (β' : (coherentAdicPullback f J).obj G' ≅ (completionFunctor X (J.comap f)).obj F)
    (d : G.obj ≅ G'.obj)
    (hd : ∀ n : ℕᵒᵖ, (Scheme.Modules.pullback f).map (d.hom.app n) ≫ β'.hom.hom.app n =
      β.hom.hom.app n)
    (α' : G'.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj)
    (h : IsDirectImageCharacterized f J G' F β' α') :
    IsDirectImageCharacterized f J G F β (d.hom ≫ α') := by
  intro n
  rw [NatTrans.comp_app, Category.assoc, h n, ← Category.assoc,
    directImageComparison_app_of_systemIso f J G G' F β β' d hd (op n)]

end Transport

/-! ### The normalization of the descent of `β` -/

section Descent

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
  (J : Y.IdealSheafData) (𝒢 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)

/-- The descent
`b : f^*𝒢 ≅ 𝓕` of an isomorphism `β : f^*(𝒢 ^∧) ≅ 𝓕 ^∧`, followed by the projection of `𝓕` onto
the `n`-th term of its completion, is the pullback of the projection of `𝒢` onto the `n`-th term
of `𝒢 ^∧` followed by `β_n`. -/
public theorem pullbackCompletionDescent_completionProjection
    (hff : Nonempty (completionFunctor X (J.comap f)).FullyFaithful)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (β : (coherentAdicPullback f J).obj ((completionFunctor Y J).obj 𝒢) ≅
      (completionFunctor X (J.comap f)).obj F) (n : ℕ) :
    (pullbackCompletionDescent f J 𝒢 hff F β).hom ≫ completionProjection X (J.comap f) F n =
      (Scheme.Modules.pullback f).map (completionProjection Y J 𝒢 n) ≫
        β.hom.hom.app (op n) := by
  set ei := hff.some.preimageIso (completionPullbackIso f J 𝒢 ≪≫ β) with hei
  have hmap : (completionFunctor X (J.comap f)).map ei.hom =
      (completionPullbackIso f J 𝒢 ≪≫ β).hom :=
    hff.some.map_preimage _
  have hq := completionFunctor_map_quotient X (J.comap f) ei.hom n
  rw [hmap] at hq
  refine hq.symm.trans ?_
  rw [Iso.trans_hom, completionPullbackIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ β.hom.hom.app (op n))
      (completionProjection_completionPullbackComparison f J 𝒢 (op n)))

end Descent

/-! ### `δ` as a morphism of inverse systems, and uniqueness of `α` -/

section DeltaSystem

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The level-`n` component of `δ`, between the terms of the two systems: the comparison
`δ_{n+1} : (f_*𝓕)/𝒥 ⁿ⁺¹(f_*𝓕) ⟶ f_*(𝓕/ℐ ⁿ⁺¹𝓕)` of
`Stacks.Coherent.directImageQuotientComparison`, read between the `n`-th term of `(f_*𝓕) ^∧` and
the `n`-th term of `f_*(𝓕 ^∧)` through the two object formulas of [Stacks, Tag 0880]. -/
public def directImageQuotientComparisonApp (n : ℕ) :
    ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj.obj (op n) ⟶
      (((completionFunctor X (J.comap f)).obj F).obj ⋙
        Scheme.Modules.pushforward f).obj (op n) :=
  eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) ≫
    directImageQuotientComparison f J (n + 1) F.obj ≫
      eqToHom (pushforward_completion_obj f J F n).symm

/-- Read out of `f_*𝓕` along the projection onto the `n`-th term of its completion,
`Stacks.Coherent.directImageQuotientComparisonApp` is the direct image of the projection of `𝓕`
onto the `n`-th term of its completion. The projection being an epimorphism, this determines the
component. -/
public theorem completionProjection_directImageQuotientComparisonApp (n : ℕ) :
    completionProjection Y J (properPushforwardCoherent f F) n ≫
        directImageQuotientComparisonApp f J F n =
      (Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F n) := by
  have hπJ : completionProjection Y J (properPushforwardCoherent f F) n ≫
      eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) =
      cokernel.π (C := Y.Modules)
        (idealPowerMultiple J (n + 1) (properPushforwardCoherent f F).obj).ι :=
    (Category.assoc (cokernel.π (C := Y.Modules)
          (idealPowerMultiple J (n + 1) (properPushforwardCoherent f F).obj).ι)
        (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n).symm)
        (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n))).trans
      ((congrArg (fun k => cokernel.π (C := Y.Modules)
            (idealPowerMultiple J (n + 1) (properPushforwardCoherent f F).obj).ι ≫ k)
          ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))
  have heP : eqToHom (pushforward_completion_obj f J F n).symm =
      (Scheme.Modules.pushforward f).map
        (eqToHom (completionFunctor_obj X (J.comap f) F n).symm) :=
    (eqToHom_map (Scheme.Modules.pushforward f)
      (completionFunctor_obj X (J.comap f) F n).symm).symm
  exact (Category.assoc (obj := Y.Modules) _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (directImageQuotientComparison f J (n + 1) F.obj ≫
          eqToHom (pushforward_completion_obj f J F n).symm)) hπJ).trans
      ((Category.assoc (obj := Y.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ eqToHom (pushforward_completion_obj f J F n).symm)
            (directImageQuotientComparison_π f J (n + 1) F.obj)).trans
          ((congrArg (fun z => (Scheme.Modules.pushforward f).map
                (cokernel.π (C := X.Modules)
                  (idealPowerMultiple (J.comap f) (n + 1) F.obj).ι) ≫ z) heP).trans
            ((Scheme.Modules.pushforward f).map_comp _ _).symm))))

/-- `δ` as a morphism of inverse systems `(f_*𝓕) ^∧ ⟶ f_*(𝓕 ^∧)`, with components
`Stacks.Coherent.directImageQuotientComparisonApp`. -/
public def directImageQuotientComparisonSystem :
    ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj ⟶
      ((completionFunctor X (J.comap f)).obj F).obj ⋙ Scheme.Modules.pushforward f where
  app n := directImageQuotientComparisonApp f J F n.unop
  naturality m n g := by
    have hepi :=
      Stacks.Algebraization.epi_completionProjection Y J (properPushforwardCoherent f F) m.unop
    refine (@cancel_epi _ _ _ _ _
      (completionProjection Y J (properPushforwardCoherent f F) m.unop) hepi _ _).mp ?_
    have hL : completionProjection Y J (properPushforwardCoherent f F) m.unop ≫
        ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj.map g ≫
          directImageQuotientComparisonApp f J F n.unop =
        (Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F n.unop) :=
      (Category.assoc (obj := Y.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ directImageQuotientComparisonApp f J F n.unop)
            (Stacks.Algebraization.completionProjection_map Y J
              (properPushforwardCoherent f F) g)).trans
          (completionProjection_directImageQuotientComparisonApp f J F n.unop))
    have hR : completionProjection Y J (properPushforwardCoherent f F) m.unop ≫
        directImageQuotientComparisonApp f J F m.unop ≫
          (((completionFunctor X (J.comap f)).obj F).obj ⋙
            Scheme.Modules.pushforward f).map g =
        (Scheme.Modules.pushforward f).map (completionProjection X (J.comap f) F n.unop) :=
      (Category.assoc (obj := Y.Modules) _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (((completionFunctor X (J.comap f)).obj F).obj ⋙
              Scheme.Modules.pushforward f).map g)
            (completionProjection_directImageQuotientComparisonApp f J F m.unop)).trans
          (((Scheme.Modules.pushforward f).map_comp _ _).symm.trans
            (congrArg (Scheme.Modules.pushforward f).map
              (Stacks.Algebraization.completionProjection_map X (J.comap f) F g))))
    exact hL.trans hR.symm

/-- The components of `Stacks.Coherent.directImageQuotientComparisonSystem`. -/
public theorem directImageQuotientComparisonSystem_app (n : ℕᵒᵖ) :
    (directImageQuotientComparisonSystem f J F).app n =
      directImageQuotientComparisonApp f J F n.unop :=
  rfl

/-- The characterization of `α` in [Stacks, Tag 088B] as one equation: a morphism
`α : (𝒢_n) ⟶ (f_*𝓕) ^∧` satisfies `Stacks.Coherent.IsDirectImageCharacterized` exactly when its
composite with `Stacks.Coherent.directImageQuotientComparisonSystem` is the comparison `γ` of
`Stacks.Coherent.directImageComparison`. -/
public theorem isDirectImageCharacterized_iff_comp_directImageQuotientComparisonSystem
    (G : CoherentAdicSystems J)
    (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)
    (α : G.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj) :
    IsDirectImageCharacterized f J G F β α ↔
      α ≫ directImageQuotientComparisonSystem f J F = directImageComparison f J G F β := by
  have hpt : ∀ n : ℕ,
      (α.app (op n) ≫ directImageQuotientComparisonApp f J F n =
        (directImageComparison f J G F β).app (op n)) ↔
      (α.app (op n) ≫ eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) ≫
          directImageQuotientComparison f J (n + 1) F.obj =
        (directImageComparison f J G F β).app (op n) ≫
          eqToHom (pushforward_completion_obj f J F n)) := by
    intro n
    have hre : α.app (op n) ≫ directImageQuotientComparisonApp f J F n =
        (α.app (op n) ≫ eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n) ≫
            directImageQuotientComparison f J (n + 1) F.obj) ≫
          eqToHom (pushforward_completion_obj f J F n).symm :=
      (congrArg (fun z => α.app (op n) ≫ z)
          (Category.assoc (obj := Y.Modules)
            (eqToHom (completionFunctor_obj Y J (properPushforwardCoherent f F) n))
            (directImageQuotientComparison f J (n + 1) F.obj)
            (eqToHom (pushforward_completion_obj f J F n).symm))).trans
        (Category.assoc (obj := Y.Modules) _ _ _).symm
    refine Iff.trans (iff_of_eq (congrArg
      (fun z => z = (directImageComparison f J G F β).app (op n)) hre)) ?_
    exact comp_eqToHom_iff _ _ _
  exact ⟨fun h => NatTrans.ext (funext fun n => (hpt n.unop).2 (h n.unop)),
    fun h n => (hpt n).1 (congrArg (fun z => NatTrans.app z (op n)) h)⟩

/-- Uniqueness of the characterized `α` out of a completion: two morphisms out of the completion
`𝒜 ^∧` with the same composite with `Stacks.Coherent.directImageQuotientComparisonSystem` are
equal, as soon as the inverse limit of that morphism of systems is a monomorphism.

The hypothesis `hmono` cannot be replaced by `δ` being a monomorphism: a monomorphism of inverse
systems in `Y.Modules` is one levelwise, and the kernel of `δ_m` is `f_*(ℐ ᵐ 𝓕) / 𝒥 ᵐ (f_*𝓕)`,
which the uniform Artin–Rees bounds of [Stacks, Tag 02OB] squeeze between powers of `𝒥` but do
not kill. Only the inverse limit of `δ` is injective, being an isomorphism by the theorem on
formal functions [Stacks, Tag 02OC].

A morphism `w` out of `𝒜 ^∧` is determined by the single map `𝒜 ⟶ lim ((f_*𝓕) ^∧)` its
composites with the projections assemble into, and post-composing `w` with `δ` post-composes that
map with `lim δ`. -/
public theorem eq_of_comp_directImageQuotientComparisonSystem_eq
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (hmono : Mono (limMap (C := Y.Modules) (directImageQuotientComparisonSystem f J F)))
    {u v : ((completionFunctor Y J).obj 𝒜).obj ⟶
      ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj}
    (h : u ≫ directImageQuotientComparisonSystem f J F =
      v ≫ directImageQuotientComparisonSystem f J F) : u = v := by
  have hcomp : ∀ w : ((completionFunctor Y J).obj 𝒜).obj ⟶
      ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj,
      limMap (C := Y.Modules) w ≫ limMap (C := Y.Modules)
          (directImageQuotientComparisonSystem f J F) =
        limMap (C := Y.Modules) (w ≫ directImageQuotientComparisonSystem f J F) := by
    intro w
    simp only [limMap_eq, Functor.map_comp]
  have := hmono
  have hlim : completionToLimit Y J 𝒜 ≫ limMap (C := Y.Modules) u =
      completionToLimit Y J 𝒜 ≫ limMap (C := Y.Modules) v := by
    refine (cancel_mono (limMap (C := Y.Modules)
      (directImageQuotientComparisonSystem f J F))).1 ?_
    erw [Category.assoc, Category.assoc, hcomp, hcomp, h]
  refine Stacks.Algebraization.completionSystemHom_ext Y J 𝒜 u v fun n => ?_
  have key : ∀ w : ((completionFunctor Y J).obj 𝒜).obj ⟶
      ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj,
      completionProjection Y J 𝒜 n ≫ w.app (op n) =
        (completionToLimit Y J 𝒜 ≫ limMap (C := Y.Modules) w) ≫
          limit.π (C := Y.Modules)
            ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj (op n) := by
    intro w
    erw [Category.assoc (obj := Y.Modules) (completionToLimit Y J 𝒜)
      (limMap (C := Y.Modules) w), limMap_π (C := Y.Modules),
      ← Category.assoc (obj := Y.Modules) (completionToLimit Y J 𝒜),
      completionToLimit_projection]
    rfl
  rw [key u, key v, hlim]

end DeltaSystem

/-! ### Stacks 088B with `α` characterized -/

section Characterized

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
  (J K : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (G : CoherentAdicSystems J)

omit [IsProper f] in
/-- Pulling back the inverse of an algebraization `e` and composing with `β` undoes the pullback
of `e`, levelwise. -/
private theorem pullback_map_mapIso_hom_comp_coherentAdicPullback_mapIso_symm_trans
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (e : G ≅ (completionFunctor Y J).obj 𝒜)
    (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)
    (n : ℕᵒᵖ) :
    (Scheme.Modules.pullback f).map
        (((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e).hom.app n) ≫
      ((((coherentAdicPullback f J).mapIso e).symm ≪≫ β).hom.hom.app n) =
    β.hom.hom.app n := by
  have hinv : ((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e).hom.app n ≫
      ((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e).inv.app n = 𝟙 _ :=
    congrArg (fun z => NatTrans.app z n)
      ((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e).hom_inv_id
  have h1 : (((coherentAdicPullback f J).mapIso e).symm ≪≫ β).hom.hom.app n =
      (Scheme.Modules.pullback f).map
          (((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e).inv.app n) ≫
        β.hom.hom.app n :=
    congrArg (fun z => z ≫ β.hom.hom.app n)
      (coherentAdicPullback_map_hom_app f J e.inv n)
  have h2 : (Scheme.Modules.pullback f).map
        (((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e).hom.app n) ≫
      (Scheme.Modules.pullback f).map
        (((ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e).inv.app n) = 𝟙 _ :=
    (((Scheme.Modules.pullback f).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.pullback f).map hinv)).trans
      ((Scheme.Modules.pullback f).map_id _)
  rw [h1]
  exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
    ((congrArg (fun z => z ≫ β.hom.hom.app n) h2).trans (Category.id_comp _))

/-- [Stacks, Tag 088B] with `α` characterized, for an algebraizable system, at a general base.
Let
`f : X ⟶ Y` be a proper morphism of Noetherian schemes, let `𝒥, 𝒦 ⊆ 𝒪_Y` be quasi-coherent sheaves
of ideals, let `(𝒢_n)` be an object of `Coh(Y, 𝒥)` algebraized by a coherent `𝒪_Y`-module `𝒜`,
let `𝓕` be a coherent `𝒪_X`-module and let `β : f^*(𝒢_n) ≅ 𝓕 ^∧`. Granted full faithfulness of
completion on `X` ([Stacks, Tag 0883]) and the condition `hc` expressing that `f` is an
isomorphism away from `V(𝒦)`, there is a morphism

`α : (𝒢_n) ⟶ (f_*𝓕) ^∧`

which is both characterized in the sense of `Stacks.Coherent.IsDirectImageCharacterized` and
has its levelwise kernels and cokernels annihilated by a power of `𝒦`.

The map is `Stacks.Coherent.properDirectImageCompletionMap` at the algebraization and at the
descent of `β` through `Stacks.Coherent.pullbackCompletionDescent`; the annihilation is
`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_properDirectImageCompletionMap`, and the
characterization is
`Stacks.Coherent.isDirectImageCharacterized_properDirectImageCompletionMap`, whose hypothesis
`hb` is `Stacks.Coherent.pullbackCompletionDescent_completionProjection`, transported to `(𝒢_n)`
by `Stacks.Coherent.isDirectImageCharacterized_of_systemIso`. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_algebraization
    (𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (e : G ≅ (completionFunctor Y J).obj 𝒜)
    (hff : Nonempty (completionFunctor X (J.comap f)).FullyFaithful)
    (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)
    (hc : IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj,
      IsDirectImageCharacterized f J G F β α ∧
        IsKernelCokernelAnnihilatedByPower K α := by
  set β' := ((coherentAdicPullback f J).mapIso e).symm ≪≫ β
  set ι := (ObjectProperty.ι (IsCoherentAdicSystem J)).mapIso e
  set b := pullbackCompletionDescent f J 𝒜 hff F β'
  refine ⟨properDirectImageCompletionMap f J 𝒜 F b G ι, ?_,
    isKernelCokernelAnnihilatedByPower_properDirectImageCompletionMap f J K 𝒜 F _ G _ hc⟩
  have hchar := isDirectImageCharacterized_of_systemIso f J G ((completionFunctor Y J).obj 𝒜) F
    β β' ι (pullback_map_mapIso_hom_comp_coherentAdicPullback_mapIso_symm_trans f J F G 𝒜 e β) _
    (isDirectImageCharacterized_properDirectImageCompletionMap f J 𝒜 F b β'
      (pullbackCompletionDescent_completionProjection f J 𝒜 hff F β'))
  have hEq : ι.hom ≫ properDirectImageCompletionMap f J 𝒜 F b
      ((completionFunctor Y J).obj 𝒜) (Iso.refl _) =
      properDirectImageCompletionMap f J 𝒜 F b G ι :=
    congrArg (ι.hom ≫ ·) (Category.id_comp _)
  exact hEq ▸ hchar

/-- [Stacks, Tag 088B] with `α` characterized, at a system in the essential image of completion:
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_algebraization` with the
algebraization given by the hypothesis `halg`. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_essImage
    (halg : (completionFunctor Y J).essImage G)
    (hff : Nonempty (completionFunctor X (J.comap f)).FullyFaithful)
    (β : (coherentAdicPullback f J).obj G ≅ (completionFunctor X (J.comap f)).obj F)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
      (G ≅ (completionFunctor Y J).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι K.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor Y J).obj (properPushforwardCoherent f F)).obj,
      IsDirectImageCharacterized f J G F β α ∧
        IsKernelCokernelAnnihilatedByPower K α := by
  obtain ⟨𝒜, ⟨ealg⟩⟩ := halg
  exact exists_isDirectImageCharacterized_isKernelCokernel_of_algebraization f J K F G 𝒜
    ealg.symm hff β (hc 𝒜 ealg.symm)

end Characterized

/-! ### Locality of the characterization on the base -/

section Locality

variable {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] (π : X' ⟶ X) [IsProper π]
  (J : X.IdealSheafData) (G : CoherentAdicSystems J)
  (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
  (β : (coherentAdicPullback π J).obj G ≅ (completionFunctor X' (J.comap π)).obj 𝓕)

/-- The characterization of `α` is local on the base: a morphism
`α : (𝒢_n) ⟶ (π_*𝓕) ^∧` of inverse systems of `𝒪_X`-modules satisfies
`Stacks.Coherent.IsDirectImageCharacterized` exactly when, over each member of an open cover of
the base, the restriction of its composite with `δ` is the restriction of `γ`.

Both sides of the characterization are morphisms of sheaves of modules on `X`, one at every
level, so this is `Stacks.Coherent.hom_ext_of_restrictCover` levelwise in one direction and
functoriality of restriction in the other. -/
public theorem isDirectImageCharacterized_iff_restrictCover
    {Jx : Type u} (U : Jx → X.Opens) (hU : IsOpenCover U)
    (α : G.obj ⟶ ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj) :
    IsDirectImageCharacterized π J G 𝓕 β α ↔
      ∀ (j : Jx) (n : ℕ),
        (Scheme.Modules.restrictFunctor (U j).ι).map (α.app (op n)) ≫
            (Scheme.Modules.restrictFunctor (U j).ι).map
              (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
                directImageQuotientComparison π J (n + 1) 𝓕.obj) =
          (Scheme.Modules.restrictFunctor (U j).ι).map
            ((directImageComparison π J G 𝓕 β).app (op n) ≫
              eqToHom (pushforward_completion_obj π J 𝓕 n)) := by
  have hg : ⨆ j, (U j).ι ''ᵁ (⊤ : (U j).toScheme.Opens) = ⊤ := by
    simp only [Scheme.Opens.ι_image_top]
    exact hU
  refine ⟨fun h j n => ?_, fun h n => ?_⟩
  · exact ((Scheme.Modules.restrictFunctor (U j).ι).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.restrictFunctor (U j).ι).map (h n))
  · refine hom_ext_of_restrictCover (fun j => (U j).ι) hg _ _ fun j => ?_
    rw [Functor.map_comp]
    exact h j n

/-- The `α` of [Stacks, Tag 088B] is constructed over an open cover of the base and glued. Let
`π : X' ⟶ X` be a proper morphism of Noetherian schemes, `𝒥 ⊆ 𝒪_X` a quasi-coherent sheaf of
ideals, `(𝒢_n)` an object of `Coh(X, 𝒥)`, `𝓕` a coherent `𝒪_{X'}`-module and
`β : π^*(𝒢_n) ≅ 𝓕 ^∧`. Given an open cover `U` of `X` and, over each member, a morphism `ψ j` of
the restricted systems

* satisfying the restricted characterization `hchar` — its composite with the restriction of `δ`
  is the restriction of `γ` — and
* agreeing with the others on the sections over every open contained in two members, `hψ`,

there is a morphism `α : (𝒢_n) ⟶ (π_*𝓕) ^∧` which satisfies
`Stacks.Coherent.IsDirectImageCharacterized` and restricts to each `ψ j`.

The members of the cover need not be affine, and nothing is assumed to be algebraizable. -/
public theorem exists_isDirectImageCharacterized_of_openCover
    {Jx : Type u} (U : Jx → X.Opens) (hU : IsOpenCover U)
    (ψ : ∀ j, G.obj ⋙ Scheme.Modules.restrictFunctor (U j).ι ⟶
      ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj ⋙
        Scheme.Modules.restrictFunctor (U j).ι)
    (hψ : ∀ (i j : Jx) (n : ℕᵒᵖ) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
      localAppOpen (U i) ((ψ i).app n) hVi = localAppOpen (U j) ((ψ j).app n) hVj)
    (hchar : ∀ (j : Jx) (n : ℕ), (ψ j).app (op n) ≫
          (Scheme.Modules.restrictFunctor (U j).ι).map
            (eqToHom (completionFunctor_obj X J (properPushforwardCoherent π 𝓕) n) ≫
              directImageQuotientComparison π J (n + 1) 𝓕.obj) =
        (Scheme.Modules.restrictFunctor (U j).ι).map
          ((directImageComparison π J G 𝓕 β).app (op n) ≫
            eqToHom (pushforward_completion_obj π J 𝓕 n))) :
    ∃ α : G.obj ⟶ ((completionFunctor X J).obj (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π J G 𝓕 β α ∧
        ∀ j, Functor.whiskerRight α (Scheme.Modules.restrictFunctor (U j).ι) = ψ j := by
  obtain ⟨α, hα, -⟩ := existsUnique_systemHom_of_openCover U hU ψ hψ
  refine ⟨α, (isDirectImageCharacterized_iff_restrictCover π J G 𝓕 β U hU α).2
    fun j n => ?_, hα⟩
  have hres : (Scheme.Modules.restrictFunctor (U j).ι).map (α.app (op n)) =
      (ψ j).app (op n) :=
    congrArg (fun z => NatTrans.app z (op n)) (hα j)
  rw [hres]
  exact hchar j n

end Locality

end Stacks.Coherent

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### Stacks 088B with `α` characterized, over an affine base -/

/-- [Stacks, Tag 088B] with `α` characterized, over an affine base. Let `A` be a Noetherian ring
complete with respect to `I`, let `f : X ⟶ Spec A` be proper with `X` affine, set
`𝓘 = I · 𝒪_X`, let `π : X' ⟶ X` be proper and let `𝒦 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals.
For a coherent `𝒪_{X'}`-module `𝓕`, an object `G` of `Coh(X, 𝓘)`, an isomorphism
`β : π^*G ≅ 𝓕 ^∧` and the condition `hc` expressing that `π` is an isomorphism away from `V(𝒦)`,
there is a morphism

`α : G ⟶ (π_*𝓕) ^∧`

which is characterized in the sense of `Stacks.Coherent.IsDirectImageCharacterized` and has its
levelwise kernels and cokernels annihilated by a power of `𝒦`.

This is
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`
with the characterization added to the conclusion. The hypotheses of
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_essImage` hold here:
`halg` by `Stacks.Algebraization.essImage_completionFunctor_baseIdealSheaf_of_isAffine` and `hff`
by `Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper`. -/
public theorem exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) (π : X' ⟶ X) [IsProper π] [IsProper f] [IsAffine X]
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : CoherentAdicSystems (baseIdealSheaf A I f))
    (β : (coherentAdicPullback π (baseIdealSheaf A I f)).obj G ≅
      (completionFunctor X' ((baseIdealSheaf A I f).comap π)).obj 𝓕)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      (G ≅ (completionFunctor X (baseIdealSheaf A I f)).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsDirectImageCharacterized π (baseIdealSheaf A I f) G 𝓕 β α ∧
        IsKernelCokernelAnnihilatedByPower 𝒦 α :=
  exists_isDirectImageCharacterized_isKernelCokernel_of_essImage π (baseIdealSheaf A I f) 𝒦 𝓕 G
    (essImage_completionFunctor_baseIdealSheaf_of_isAffine A I f G)
    (fullyFaithful_completionFunctor_comap_of_isProper A I f π) β hc

end Stacks.Algebraization

end
