module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.Restriction
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal

/-!
# Crystals in modules on the big crystalline site, at sheaf level

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation.  Over every object `(U, T, δ)` it restricts to a module `F_T` on the ambient scheme
`T`, and that restriction is again a sheaf, because the restrictions of `(U, T, δ)` to the opens
of `T` form a continuous functor.  A morphism `f : (U, T, δ) ⟶ (U', T', δ')` gives an `f`-map
`F_{T'} ⟶ f_* F_T`, and the adjunction between pullback and pushforward of *sheaves* of modules
turns it into the comparison map `c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules.  The
module `F` is a *crystal in `𝒪_{X/S}`-modules* when every one of these comparison maps is an
isomorphism.

The pullback used here is `SheafOfModules.pullback`: the left adjoint of the pushforward of
sheaves of modules along the continuous functor `Opens T' ⥤ Opens T` of Zariski sites induced by
the map of ambient schemes, which is the sheafification of the pullback of presheaves of modules.

## The correction

The literal reading of [Stacks, Tag 07IT] — a sheaf of `𝒪_{X/S}`-modules is quasi-coherent if and
only if it is locally quasi-coherent and a crystal — is false when the crystal condition is read
with the comparison maps of *presheaves* of modules, that is, with
`Crystalline.GlobalCrystallineSituation.IsCrystal`.  The pullback of presheaves of modules is not
the pullback of sheaves of modules: the latter sheafifies the former, and sheafification is not
the identity on the relevant presheaves because an infinite coproduct of sheaves of modules is
not computed section by section.  Concretely, let `T_A` be a countable disjoint union of copies
of `Spec 𝔽_p`; the coproduct of countably many copies of `𝒪_{X/S}` is quasi-coherent, while its
presheaf-level comparison maps over `T_A` are not isomorphisms, because a section of the
coproduct over `T_A` may use a different summand on each component and so is not in the image of
the presheaf-level coproduct.  The crystal condition of [Stacks, Tag 07IS] is therefore read here
at sheaf level, which is `Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, and it is the
weaker of the two: `Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafFMap` — the `f`-map of
  the restricted structure sheaves of a morphism of the big crystalline site, as a morphism of
  sheaves of rings over the continuous functor of Zariski sites induced by the map of ambient
  schemes.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleRestrictionSheaf` — the restriction
  `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme of an object, as a sheaf of
  modules.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheaf` — the `f`-map
  `F_{T'} ⟶ f_* F_T` of sheaves of modules.
* `Crystalline.GlobalCrystallineSituation.Thickening.moduleComparisonSheaf` — the comparison map
  `c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules, [Stacks, Tag 07IQ] at sheaf level.
* `Crystalline.GlobalCrystallineSituation.IsSheafCrystal` — the crystal condition of
  [Stacks, Tag 07IS], read with the comparison maps of sheaves of modules.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.moduleFMapSheaf_eq_moduleComparisonSheaf` —
  the `f`-map is recovered from the comparison map by the unit of the adjunction.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleComparisonSheaf` — the
  comparison map of sheaves of modules is an isomorphism as soon as the comparison map of
  presheaves of modules is.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleComparisonSheaf_of_isCartesian` —
  the comparison map of sheaves of modules of a Cartesian open immersion is an isomorphism.
* `Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal` — a crystal for the
  comparison maps of presheaves of modules is a crystal for the comparison maps of sheaves of
  modules.

## Implementation notes

The pullback of sheaves of modules along a continuous functor exists once the pullback of
presheaves of modules does and the target site has a sheafification for abelian groups which is
locally bijective.  Both hold here: the opens of a scheme over `Scheme.{u}` form a small category
in `Type u`, the same universe as the rings and the module sections, so Mathlib's instance for
the pullback of presheaves of modules applies.  It applies only to a morphism of presheaves of
rings written in the shape `S ⟶ F.op ⋙ R`, whereas the morphism underlying a morphism of sheaves
of rings is written with `Functor.sheafPushforwardContinuous`; the two are the same presheaf
morphism, so the instance for the sheaf-level `f`-map is obtained from the presheaf-level one by
`inferInstanceAs` on the first shape, and no weakening of definitional transparency is needed to
see through the difference.

The comparison map of sheaves of modules is not compared with the comparison map of presheaves of
modules through the identification of the sheaf pullback with the sheafification of the presheaf
pullback; that identification is stated with the morphism underlying the sheaf-level `f`-map and
rewriting along it does not typecheck without lowering the transparency of definitional
unfolding.  Instead both comparison maps are characterised by the same universal property — the
`f`-map is their common transpose — and the implication between them is proved by transporting
bijectivity of postcomposition across the fully faithful forgetful functor from sheaves of
modules to presheaves of modules, under which the `f`-map and the pushforward of a morphism are
preserved on the nose.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation

/-- A morphism all of whose postcompositions are bijective is an isomorphism. -/
private theorem isIso_of_bijective_comp_right {C₁ : Type*} [Category C₁] {P Y : C₁} (u : P ⟶ Y)
    (h : ∀ Z : C₁, Function.Bijective fun k : Y ⟶ Z ↦ u ≫ k) : IsIso u := by
  obtain ⟨k, hk⟩ := (h P).surjective (𝟙 P)
  have hk' : u ≫ k = 𝟙 P := hk
  refine ⟨k, hk', (h Y).injective ?_⟩
  show u ≫ k ≫ u = u ≫ 𝟙 Y
  rw [← Category.assoc, hk', Category.id_comp, Category.comp_id]

/-- Postcomposition with an isomorphism is bijective. -/
private theorem bijective_comp_right_of_isIso {C₁ : Type*} [Category C₁] {P Y : C₁} (u : P ⟶ Y)
    (hu : IsIso u) (Z : C₁) : Function.Bijective fun k : Y ⟶ Z ↦ u ≫ k := by
  have := hu
  refine ⟨fun a b hab ↦ ?_, fun c ↦ ⟨inv u ≫ c, by simp⟩⟩
  simpa using congrArg (fun t ↦ inv u ≫ t) hab

/-- A morphism of sheaves of modules is its underlying morphism of presheaves of modules. -/
private theorem bijective_hom_val {C₁ : Type*} [Category C₁] {J : GrothendieckTopology C₁}
    {R : Sheaf J RingCat.{u}} (X Y : SheafOfModules.{u} R) :
    Function.Bijective fun k : X ⟶ Y ↦ k.val :=
  ⟨fun _ _ hab ↦ SheafOfModules.Hom.ext hab, fun v ↦ ⟨⟨v⟩, rfl⟩⟩

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}} {A B : Thickening S}

/-- **The `f`-map of the restricted structure sheaves of a morphism of `CRIS(X/S)`.**  Over an
open `W` of the ambient scheme of the target it is the restriction map along the restriction of
the morphism over `W`; it is a morphism of sheaves of rings over the continuous functor of
Zariski sites induced by the map of ambient schemes. -/
noncomputable def ringRestrictionSheafFMap (g : A ⟶ B) :
    B.ringRestrictionSheaf ⟶
      ((Opens.map g.targetHom.hom.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology ↥B.thickening.target.scheme)
          (Opens.grothendieckTopology ↥A.thickening.target.scheme)).obj
        A.ringRestrictionSheaf :=
  ⟨restrictionFMap (crisRing S) g⟩

/-- The pushforward of presheaves of modules along the `f`-map of the restricted structure
sheaves has a left adjoint: the opens of the ambient schemes are small categories in the
universe of the rings and of the module sections. -/
instance isRightAdjoint_pushforward_ringRestrictionSheafFMap (g : A ⟶ B) :
    (PresheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g).hom).IsRightAdjoint :=
  inferInstanceAs (PresheafOfModules.pushforward.{u}
    (show ringRestriction B ⟶
        (Opens.map g.targetHom.hom.base).op ⋙ ringRestriction A from
      restrictionFMap (crisRing S) g)).IsRightAdjoint

/-- **Stacks Project, Tag 07IQ.**  The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the
ambient scheme of an object, as a sheaf of modules over the restricted structure sheaf: its
sections over an open `W` are the sections of `F` over the restriction of the object to `W`.  The
sheaf condition holds because the restrictions to the opens of the ambient scheme form a
continuous functor. -/
noncomputable def moduleRestrictionSheaf (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : Thickening S) : SheafOfModules.{u} A.ringRestrictionSheaf where
  val := moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) A
  isSheaf := isSheaf_restriction _ M.isSheaf A

/-- The underlying presheaf of modules of `moduleRestrictionSheaf M A` is the restriction
`moduleRestriction M.val A` of the underlying presheaf of `M`. -/
@[simp]
theorem moduleRestrictionSheaf_val (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : Thickening S) :
    (moduleRestrictionSheaf M A).val =
      moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) A := rfl

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- **Stacks Project, Tag 07IQ.**  The `f`-map `F_{T'} ⟶ f_* F_T` of a sheaf of
`𝒪_{X/S}`-modules along a morphism `f` of `CRIS(X/S)`, as a morphism of sheaves of modules: it is
the `f`-map of the underlying presheaves of modules, the pushforward of a sheaf along a
continuous functor being computed by restriction. -/
noncomputable def moduleFMapSheaf (g : A ⟶ B) :
    moduleRestrictionSheaf M B ⟶
      (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g)).obj
        (moduleRestrictionSheaf M A) :=
  ⟨moduleFMap (M.val : PresheafOfModules.{u} (crisRing S)) g⟩

/-- **Stacks Project, Tag 07IQ.**  The comparison map `c_f : f^* F_{T'} ⟶ F_T` of a morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `CRIS(X/S)` and a sheaf of `𝒪_{X/S}`-modules `F`, a map of
sheaves of `𝒪_T`-modules obtained from the `f`-map `F_{T'} ⟶ f_* F_T` by the adjunction between
pullback and pushforward of *sheaves* of modules.  The pullback is the sheafification of the
pullback of presheaves of modules, so this map is in general not the comparison map
`Crystalline.GlobalCrystallineSituation.Thickening.moduleComparison` of the underlying presheaves
of modules. -/
@[stacks 07IQ "the comparison map for modules on the big crystalline site, for sheaves"]
noncomputable def moduleComparisonSheaf (g : A ⟶ B) :
    (SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).obj
        (moduleRestrictionSheaf M B) ⟶ moduleRestrictionSheaf M A :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u} (ringRestrictionSheafFMap g)).homEquiv
    (moduleRestrictionSheaf M B) (moduleRestrictionSheaf M A)).symm (moduleFMapSheaf M g)

/-- The `f`-map of a sheaf of `𝒪_{X/S}`-modules is recovered from the comparison map of sheaves
of modules by the unit of the adjunction between pullback and pushforward. -/
theorem moduleFMapSheaf_eq_moduleComparisonSheaf (g : A ⟶ B) :
    moduleFMapSheaf M g =
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (ringRestrictionSheafFMap g)).homEquiv
        (moduleRestrictionSheaf M B) (moduleRestrictionSheaf M A) (moduleComparisonSheaf M g) :=
  (Equiv.apply_symm_apply _ _).symm

/-- Postcomposing the comparison map of presheaves of modules and transposing gives the `f`-map
of presheaves of modules followed by the pushforward of the postcomposed morphism. -/
private theorem homEquiv_moduleComparison_comp (N : PresheafOfModules.{u} (crisRing S))
    (g : A ⟶ B) (W : PresheafOfModules.{u} (ringRestriction A))
    (k : moduleRestriction N A ⟶ W) :
    (PresheafOfModules.pullbackPushforwardAdjunction (F := Opens.map g.targetHom.hom.base)
          (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction N B) W
        (moduleComparison N g ≫ k) =
      moduleFMap N g ≫
        (PresheafOfModules.pushforward (F := Opens.map g.targetHom.hom.base)
          (restrictionFMap (crisRing S) g)).map k := by
  rw [Adjunction.homEquiv_naturality_right, moduleComparison, Equiv.apply_symm_apply]

/-- **The comparison map of sheaves of modules is an isomorphism as soon as the comparison map of
presheaves of modules is.**  Both maps transpose to the same `f`-map, so postcomposition with
either is, after transposing, the map sending a morphism out of `F_T` to the `f`-map followed by
its pushforward; the forgetful functor from sheaves of modules to presheaves of modules is fully
faithful and carries the `f`-map and the pushforward of a morphism to the presheaf-level ones, so
bijectivity of postcomposition transfers from the presheaf level to the sheaf level. -/
theorem isIso_moduleComparisonSheaf (g : A ⟶ B)
    (h : IsIso (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g)) :
    IsIso (moduleComparisonSheaf M g) := by
  refine isIso_of_bijective_comp_right _ fun Z ↦ ?_
  have key : (fun (k : moduleRestrictionSheaf M A ⟶ Z) ↦
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z
          (moduleComparisonSheaf M g ≫ k)).val) =
      fun k ↦ (PresheafOfModules.pullbackPushforwardAdjunction
            (F := Opens.map g.targetHom.hom.base) (restrictionFMap (crisRing S) g)).homEquiv
          (moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) B) Z.val
          (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g ≫ k.val) := by
    funext k
    have h1 : ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z
            (moduleComparisonSheaf M g ≫ k)) =
        moduleFMapSheaf M g ≫
          (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g)).map k := by
      rw [Adjunction.homEquiv_naturality_right, moduleComparisonSheaf, Equiv.apply_symm_apply]
    rw [h1]
    exact (homEquiv_moduleComparison_comp (M.val : PresheafOfModules.{u} (crisRing S)) g
      Z.val k.val).symm
  have hr : Function.Bijective (fun (k : moduleRestrictionSheaf M A ⟶ Z) ↦
      (PresheafOfModules.pullbackPushforwardAdjunction
            (F := Opens.map g.targetHom.hom.base) (restrictionFMap (crisRing S) g)).homEquiv
          (moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) B) Z.val
          (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g ≫ k.val)) :=
    (Equiv.bijective _).comp ((bijective_comp_right_of_isIso _ h _).comp
      (bijective_hom_val _ _))
  have hT : Function.Bijective
      (fun w : (SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).obj
          (moduleRestrictionSheaf M B) ⟶ Z ↦
        (((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z) w).val) :=
    (bijective_hom_val _ _).comp (Equiv.bijective _)
  refine (hT.of_comp_iff'
    (fun k : moduleRestrictionSheaf M A ⟶ Z ↦ moduleComparisonSheaf M g ≫ k)).1 ?_
  change Function.Bijective (fun (k : moduleRestrictionSheaf M A ⟶ Z) ↦
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z
      (moduleComparisonSheaf M g ≫ k)).val)
  rw [key]
  exact hr

/-- **Stacks Project, Tag 07IQ.**  The comparison map of sheaves of modules of a Cartesian open
immersion of `CRIS(X/S)` is an isomorphism: the restriction `F_T` is then the restriction of
`F_{T'}` to the open `T` of `T'` already at the level of presheaves of modules. -/
@[stacks 07IQ "the comparison map for sheaves of modules is an isomorphism for an open immersion"]
theorem isIso_moduleComparisonSheaf_of_isCartesian (g : A ⟶ B)
    [IsOpenImmersion g.targetHom.hom] (hg : IsCartesian g) :
    IsIso (moduleComparisonSheaf M g) :=
  isIso_moduleComparisonSheaf M g
    (isIso_moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g hg)

end Thickening

/-- **Stacks Project, Tag 07IS.**  A sheaf of `𝒪_{X/S}`-modules on the big crystalline site is a
*crystal in `𝒪_{X/S}`-modules* when for every morphism `f : (U, T, δ) ⟶ (U', T', δ')` of the site
the comparison map `c_f : f^* F_{T'} ⟶ F_T` of *sheaves* of `𝒪_T`-modules is an isomorphism.

This is the sheaf-level reading of the condition, the pullback being the pullback of sheaves of
modules, that is, the sheafification of the pullback of presheaves of modules.  It is the reading
the source intends and it is weaker than the presheaf-level condition
`Crystalline.GlobalCrystallineSituation.IsCrystal`; see the correction described in the module
documentation. -/
@[stacks 07IS "part (3): crystal in modules on the big site CRIS(X/S), with the comparison maps
  of sheaves of modules"]
def IsSheafCrystal {S : GlobalCrystallineSituation.{u}}
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) : Prop :=
  ∀ (A B : Thickening S) (k : A ⟶ B), IsIso (Thickening.moduleComparisonSheaf M k)

/-- **A crystal for the comparison maps of presheaves of modules is a crystal for the comparison
maps of sheaves of modules.**  The converse fails: the pullback of sheaves of modules sheafifies
the pullback of presheaves of modules, and an infinite coproduct of sheaves of modules is not
computed section by section. -/
theorem isSheafCrystal_of_isCrystal {S : GlobalCrystallineSituation.{u}}
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (h : IsCrystal M) :
    IsSheafCrystal M :=
  fun A B k ↦ Thickening.isIso_moduleComparisonSheaf M k (h A B k)

end Crystalline.GlobalCrystallineSituation

end
