module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Units

/-!
# Affine base change for quasi-coherent modules is compatible with composition

Let `φ : R ⟶ S` and `ψ : S ⟶ T` be morphisms of commutative rings.  There are two ways of
identifying the inverse image of `M^~` along `Spec.map (φ ≫ ψ)` with `(T ⊗_S (S ⊗_R M))^~`:
either pull back in two steps, using
`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` for `φ` and then for `ψ`, or pull
back in one step along `φ ≫ ψ` and then split the extension of scalars with
`ModuleCat.extendScalarsComp`.  This file proves that the two agree.

This is the coherence that was missing from
`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso`: that comparison is produced by
uniqueness of left adjoints, so nothing about it is computable by unfolding, and consumers could
previously only use its naturality in the module argument.

## Main results

* `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso_comp_app`: the coherence, one
  module at a time.
* `Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso_comp`: the coherence as an equality
  of natural isomorphisms.

## Implementation notes

The proof is by the universal property, read on global sections.  A morphism out of
`(Spec.map ξ)^* (M^~)` is determined by its transpose along the pullback--pushforward
adjunction (`pullback_hom_ext`), and a morphism out of `M^~` is determined by what it does to
global sections (`tilde_hom_ext`); so the coherence follows from the single computation
`moduleSpecΓ_map_tildePullbackIso_comp_unit`, which evaluates both composites on the canonical
global section of `M^~` attached to `m : M`.  Both answers are `1 ⊗ 1 ⊗ m`: for the two-step
composite this uses `Stacks.AlgebraicGeometry.AffineBaseChange.tildePullbackIso_unit` twice,
together with the fact that the unit of the pullback--pushforward adjunction along a composite
is, through `AlgebraicGeometry.Scheme.Modules.pullbackComp`, the composite of the two units
(`moduleSpecΓ_map_pullbackComp_inv_unit_apply`, an instance of
`CategoryTheory.unit_conjugateEquiv` and
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`); for the one-step composite
it uses `tildePullbackIso_unit` once and
`ModuleCat.extendScalarsComp_hom_app_one_tmul`.

Every passage between the various descriptions of a module of global sections is definitional:
direct image does not change sections over the whole space, and neither does the comparison of
iterated direct images.  The lemmas `moduleSpecΓ_map_unit_comp_apply₂` and
`moduleSpecΓ_map_unit_comp_apply₄` package those definitional unfoldings once and for all, on
variables, so that the kernel never has to perform them on the large terms occurring in the
coherence itself.

The statement of `tildePullbackIso_comp` carries no associators: `(F ⋙ G) ⋙ H` and
`F ⋙ (G ⋙ H)` are definitionally equal, so the whiskered isomorphisms compose directly.

## References

* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.SectionsColimit

/-! ### Two extensionality principles -/

/-- A morphism out of an inverse image is determined by its transpose: by the composite of the
unit of the pullback--pushforward adjunction with its own direct image. -/
theorem pullback_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Y.Modules} {P : X.Modules}
    {u v : (Scheme.Modules.pullback f).obj N ⟶ P}
    (h : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N ≫
          (Scheme.Modules.pushforward f).map u =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N ≫
          (Scheme.Modules.pushforward f).map v) :
    u = v :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv N P).injective <| by
    rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]

/-- A morphism out of `M^~` is determined by what it does to the global sections attached to the
elements of `M`. -/
theorem tilde_hom_ext {A : CommRingCat.{u}} {M : ModuleCat.{u} A} {Q : (Spec A).Modules}
    {p q : (tilde.functor A).obj M ⟶ Q}
    (h : ∀ m : M, (moduleSpecΓFunctor.map p).hom ((tilde.toTildeΓNatIso.hom.app M).hom m) =
      (moduleSpecΓFunctor.map q).hom ((tilde.toTildeΓNatIso.hom.app M).hom m)) :
    p = q :=
  (tilde.adjunction.homEquiv M Q).injective <| by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact ModuleCat.hom_ext (LinearMap.ext h)

/-! ### Global sections of the units -/

section Sections

variable {A B C : CommRingCat.{u}}

/-- Transporting the unit of the pullback--pushforward adjunction along an equality of morphisms
of schemes gives the unit of the adjunction for the other morphism. -/
theorem moduleSpecΓ_map_pullbackCongr_unit_apply {f g : Spec C ⟶ Spec A} (e : f = g)
    (N : (Spec A).Modules) (x : Γ(N, ⊤)) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr e).hom.app N)).hom
        ((moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)).hom x) =
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)).hom x := by
  subst e
  rfl

/-- On global sections, the unit of the pullback--pushforward adjunction along a composite,
followed by the comparison of iterated inverse images, is the composite of the two units. -/
theorem moduleSpecΓ_map_pullbackComp_inv_unit_apply (f : Spec C ⟶ Spec B) (g : Spec B ⟶ Spec A)
    (N : (Spec A).Modules) (x : Γ(N, ⊤)) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).inv.app N)).hom
        ((moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app N)).hom x) =
      (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            ((Scheme.Modules.pullback g).obj N))).hom
        ((moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N)).hom x) := by
  have key := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at key
  exact (congr(ModuleCat.Hom.hom (moduleSpecΓFunctor.map $(key)) x)).symm

/-- Naturality of the unit of the pullback--pushforward adjunction, on global sections. -/
theorem moduleSpecΓ_map_pullback_map_unit_apply (f : Spec C ⟶ Spec B)
    {N₁ N₂ : (Spec B).Modules} (k : N₁ ⟶ N₂) (y : Γ(N₁, ⊤)) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map k)).hom
        ((moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N₁)).hom y) =
      (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N₂)).hom
        ((moduleSpecΓFunctor.map k).hom y) :=
  (congr(ModuleCat.Hom.hom (moduleSpecΓFunctor.map
    $((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality k)) y)).symm

/-- Naturality of the identification of a module with the global sections of its associated
quasi-coherent module. -/
theorem moduleSpecΓ_map_tilde_map_apply {M₁ M₂ : ModuleCat.{u} A} (k : M₁ ⟶ M₂) (z : M₁) :
    (moduleSpecΓFunctor.map ((tilde.functor A).map k)).hom
        ((tilde.toTildeΓNatIso.hom.app M₁).hom z) =
      (tilde.toTildeΓNatIso.hom.app M₂).hom (k.hom z) :=
  (congr(ModuleCat.Hom.hom $(tilde.toTildeΓNatIso.hom.naturality k) z)).symm

/-- Reading a transpose of a two-fold composite on global sections.  This is one definitional
unfolding, isolated on variables: direct image along `Spec.map ξ` does not change sections over
the whole space. -/
theorem moduleSpecΓ_map_unit_comp_apply₂ (ξ : A ⟶ C) (M : ModuleCat.{u} A)
    {N₂ N₃ : (Spec C).Modules}
    (a : (Scheme.Modules.pullback (Spec.map ξ)).obj ((tilde.functor A).obj M) ⟶ N₂)
    (b : N₂ ⟶ N₃) (y : (tilde.functor A ⋙ moduleSpecΓFunctor).obj M) :
    (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ξ)).unit.app
              ((tilde.functor A).obj M) ≫
            (Scheme.Modules.pushforward (Spec.map ξ)).map (a ≫ b))).hom y =
      (moduleSpecΓFunctor.map b).hom ((moduleSpecΓFunctor.map a).hom
        ((moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ξ)).unit.app
            ((tilde.functor A).obj M))).hom y)) := rfl

/-- Reading a transpose of a four-fold composite on global sections; see
`moduleSpecΓ_map_unit_comp_apply₂`. -/
theorem moduleSpecΓ_map_unit_comp_apply₄ (ξ : A ⟶ C) (M : ModuleCat.{u} A)
    {N₂ N₃ N₄ N₅ : (Spec C).Modules}
    (a : (Scheme.Modules.pullback (Spec.map ξ)).obj ((tilde.functor A).obj M) ⟶ N₂)
    (b : N₂ ⟶ N₃) (c : N₃ ⟶ N₄) (d : N₄ ⟶ N₅)
    (y : (tilde.functor A ⋙ moduleSpecΓFunctor).obj M) :
    (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ξ)).unit.app
              ((tilde.functor A).obj M) ≫
            (Scheme.Modules.pushforward (Spec.map ξ)).map ((a ≫ b) ≫ c ≫ d))).hom y =
      (moduleSpecΓFunctor.map d).hom ((moduleSpecΓFunctor.map c).hom
        ((moduleSpecΓFunctor.map b).hom ((moduleSpecΓFunctor.map a).hom
          ((moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map ξ)).unit.app
              ((tilde.functor A).obj M))).hom y)))) := rfl

end Sections

/-! ### The coherence -/

section Comp

variable {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T)

/-- Both ways of comparing the inverse image of `M^~` along `Spec.map (φ ≫ ψ)` with
`(T ⊗_S (S ⊗_R M))^~` send the global section of `M^~` attached to `m` to `1 ⊗ 1 ⊗ m`. -/
theorem moduleSpecΓ_map_tildePullbackIso_comp_unit (M : ModuleCat.{u} R) (m : M) :
    (moduleSpecΓFunctor.map
        ((tildePullbackIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M))).hom
      ((moduleSpecΓFunctor.map
          ((Scheme.Modules.pullback (Spec.map ψ)).map ((tildePullbackIso φ).hom.app M))).hom
        ((moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app
              ((tilde.functor R).obj M))).hom
          ((moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ)).hom.app
                ((tilde.functor R).obj M))).hom
            ((moduleSpecΓFunctor.map
                ((Scheme.Modules.pullbackPushforwardAdjunction
                    (Spec.map (φ ≫ ψ))).unit.app ((tilde.functor R).obj M))).hom
              ((tilde.toTildeΓNatIso.hom.app M).hom m))))) =
      (moduleSpecΓFunctor.map
            ((tilde.functor T).map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M))).hom
        ((moduleSpecΓFunctor.map ((tildePullbackIso (φ ≫ ψ)).hom.app M)).hom
          ((moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                  (Spec.map (φ ≫ ψ))).unit.app ((tilde.functor R).obj M))).hom
            ((tilde.toTildeΓNatIso.hom.app M).hom m))) := by
  rw [moduleSpecΓ_map_pullbackCongr_unit_apply (Spec.map_comp φ ψ) ((tilde.functor R).obj M)
      ((tilde.toTildeΓNatIso.hom.app M).hom m),
    moduleSpecΓ_map_pullbackComp_inv_unit_apply (Spec.map ψ) (Spec.map φ)
      ((tilde.functor R).obj M) ((tilde.toTildeΓNatIso.hom.app M).hom m),
    moduleSpecΓ_map_pullback_map_unit_apply (Spec.map ψ)
      (N₁ := (Scheme.Modules.pullback (Spec.map φ)).obj ((tilde.functor R).obj M))
      (N₂ := (tilde.functor S).obj ((ModuleCat.extendScalars φ.hom).obj M))
      ((tildePullbackIso φ).hom.app M)
      ((moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map φ)).unit.app ((tilde.functor R).obj M))).hom
        ((tilde.toTildeΓNatIso.hom.app M).hom m)),
    AffineBaseChange.tildePullbackIso_unit φ M m,
    AffineBaseChange.tildePullbackIso_unit ψ ((ModuleCat.extendScalars φ.hom).obj M)
      ((1 : S) ⊗ₜ[R, φ.hom] m),
    AffineBaseChange.tildePullbackIso_unit (φ ≫ ψ) M m,
    moduleSpecΓ_map_tilde_map_apply
      (M₁ := (ModuleCat.extendScalars (φ ≫ ψ).hom).obj M)
      (M₂ := (ModuleCat.extendScalars ψ.hom).obj ((ModuleCat.extendScalars φ.hom).obj M))
      ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M)
      ((1 : T) ⊗ₜ[R, (φ ≫ ψ).hom] m)]
  exact congrArg _ (ModuleCat.extendScalarsComp_hom_app_one_tmul φ.hom ψ.hom M m).symm

/-- **The affine base-change isomorphism is compatible with composition of ring maps**, one
module at a time: pulling `M^~` back along `Spec.map φ` and then along `Spec.map ψ` and
comparing with `(T ⊗_S (S ⊗_R M))^~` in two steps is the same as pulling back along
`Spec.map (φ ≫ ψ)` in one step and splitting `T ⊗_R M` as `T ⊗_S (S ⊗_R M)`. -/
theorem tildePullbackIso_comp_app (M : ModuleCat.{u} R) :
    ((Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ)).hom.app ((tilde.functor R).obj M) ≫
          (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app
            ((tilde.functor R).obj M)) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map ((tildePullbackIso φ).hom.app M) ≫
          (tildePullbackIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) =
      (tildePullbackIso (φ ≫ ψ)).hom.app M ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) := by
  refine pullback_hom_ext (Spec.map (φ ≫ ψ)) (tilde_hom_ext fun m => ?_)
  rw [moduleSpecΓ_map_unit_comp_apply₄ (φ ≫ ψ) M, moduleSpecΓ_map_unit_comp_apply₂ (φ ≫ ψ) M]
  exact moduleSpecΓ_map_tildePullbackIso_comp_unit φ ψ M m

/-- **The affine base-change isomorphism is compatible with composition of ring maps.**  The two
natural identifications of `tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map (φ ≫ ψ))` with
`ModuleCat.extendScalars φ.hom ⋙ ModuleCat.extendScalars ψ.hom ⋙ tilde.functor T` agree. -/
theorem tildePullbackIso_comp :
    Functor.isoWhiskerLeft (tilde.functor R)
        (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ) ≪≫
          (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).symm) ≪≫
      Functor.isoWhiskerRight (tildePullbackIso φ) (Scheme.Modules.pullback (Spec.map ψ)) ≪≫
        Functor.isoWhiskerLeft (ModuleCat.extendScalars φ.hom) (tildePullbackIso ψ) =
      tildePullbackIso (φ ≫ ψ) ≪≫
        Functor.isoWhiskerRight (ModuleCat.extendScalarsComp φ.hom ψ.hom) (tilde.functor T) := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact tildePullbackIso_comp_app φ ψ M

end Comp

end Stacks.AlgebraicGeometry.SectionsColimit

end
