module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image along a surjective morphism is faithful on étale sheaves of sets

For a surjective morphism of schemes `f : X ⟶ Y` the unit `𝒢 ⟶ f_* f^{-1}𝒢` of the
inverse-image/direct-image adjunction on sheaves of sets on the small étale sites is a
monomorphism, so the inverse image `f^{-1}` is a faithful functor and the comparison
`Γ(Y, 𝒢) ⟶ Γ(X, f^{-1}𝒢)` on global sections is injective.

The stalk of the unit at a geometric point of `Y` which lifts to `X` is a split monomorphism:
the stalk of `f^{-1}𝒢` at a lift is the stalk of `𝒢` at the point
([Stacks, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)), and the stalk of the unit
followed by that identification and by the stalk of the counit is that identification again, by
the triangle identity. If `f` is surjective the geometric points of `Y` obtained from the points
of `X` cover `Y`, and stalks at a covering family of geometric points detect local injectivity
and hence monomorphisms.

For a finite surjective `f` these are the injectivity statements contained in
[Stacks, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3): the zeroth level of the Čech
nerve of `f` is `X` itself, so the augmentation is the unit and the fork map of the displayed
equalizer is the comparison on global sections.

## Main results

* `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mono_of_injective_sheafFiber_map`
  — a `w`-small conservative family of points detects monomorphisms of sheaves of
  `Type (max w v)`.
* `Stacks.Sites.mono_globalSectionsPullbackComparison_app` — the comparison on global sections
  induced by an adjunction is a monomorphism as soon as the unit is one over the terminal object.
* `Stacks.EtaleCohomology.injective_sheafFiber_map_smallEtaleUnit` — the stalk of the unit at a
  geometric point of `Y` factoring through `f` is injective.
* `Stacks.EtaleCohomology.mono_smallEtaleUnit_of_surjective` — for surjective `f` the unit is a
  monomorphism.
* `Stacks.EtaleCohomology.injective_smallEtaleGlobalSectionsComparison_of_surjective` — the
  comparison on global sections is injective.
* `Stacks.EtaleCohomology.faithful_smallEtaleInverseImage_of_surjective` — `f^{-1}` is faithful.

## References

* [Stacks Project, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' v' u' v u

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

/-- A `w`-small conservative family of points of a site, relative to the universe `w`, detects
local injectivity of a morphism of sheaves of `Type (max w v)` for an arbitrary `v`.

Local injectivity is a condition on germs, so the `Type w`-valued fibre functors see it even at
these coefficients, where the conclusion of
`ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms` is unavailable. -/
public lemma isLocallyInjective_of_injective_sheafFiber_map
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    (P : ObjectProperty (GrothendieckTopology.Point.{w} J))
    [LocallySmall.{w} C] [ObjectProperty.Small.{w} P]
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (hP : P.IsConservativeFamilyOfPoints)
    {F G : Sheaf J (Type (max w v))} (f : F ⟶ G)
    (hf : ∀ Φ : P.FullSubcategory, Function.Injective (Φ.obj.sheafFiber.map f)) :
    Sheaf.IsLocallyInjective f := by
  classical
  have cover {X : C} (R : Sieve X)
      (hR : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
        ∃ (Y : C) (g : Y ⟶ X) (_ : R g) (y : Φ.obj.fiber.obj Y),
          Φ.obj.fiber.map g y = x) : R ∈ J X := by
    obtain ⟨α, Y, g, rfl⟩ := R.exists_eq_ofArrows
    refine (hP.jointly_reflect_ofArrows_mem_of_small g).2 fun Φ x => ?_
    obtain ⟨W, a, ha, w, hw⟩ := hR Φ x
    obtain ⟨i, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ha
    exact ⟨i, Φ.obj.fiber.map b w, by simpa using hw⟩
  refine ⟨?_⟩
  intro X x y h
  apply cover
  intro Φ t
  have ht : Φ.obj.toPresheafFiber X.unop t F.obj x =
      Φ.obj.toPresheafFiber X.unop t F.obj y := by
    apply hf Φ
    show Φ.obj.presheafFiber.map f.hom (Φ.obj.toPresheafFiber X.unop t F.obj x) =
      Φ.obj.presheafFiber.map f.hom (Φ.obj.toPresheafFiber X.unop t F.obj y)
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
      GrothendieckTopology.Point.toPresheafFiber_naturality_apply, h]
  obtain ⟨Y, g, z, hz, heq⟩ := (Φ.obj.toPresheafFiber_eq_iff' _ _ _ _).1 ht
  exact ⟨Y, g, heq, z, hz⟩

/-- A `w`-small conservative family of points of a site detects monomorphisms of sheaves of
`Type (max w v)`, a locally injective morphism of sheaves being a monomorphism. -/
@[sga "4 IV 6.4.3" "Monomorphism clause"]
public lemma mono_of_injective_sheafFiber_map
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    (P : ObjectProperty (GrothendieckTopology.Point.{w} J))
    [LocallySmall.{w} C] [ObjectProperty.Small.{w} P]
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (hP : P.IsConservativeFamilyOfPoints)
    {F G : Sheaf J (Type (max w v))} (f : F ⟶ G)
    (hf : ∀ Φ : P.FullSubcategory, Function.Injective (Φ.obj.sheafFiber.map f)) : Mono f :=
  have := isLocallyInjective_of_injective_sheafFiber_map P hP f hf
  Sheaf.mono_of_isLocallyInjective f

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

namespace Stacks.Sites

variable {C : Type*} [Category C] {D : Type*} [Category D] (G : C ⥤ D)
  (A : Type*) [Category A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] {P : Sheaf J A ⥤ Sheaf K A}
  [HasWeakSheafify J A] [HasWeakSheafify K A] [HasTerminal C] [HasTerminal D]

/-- The comparison map on global sections induced by an adjunction is a monomorphism as soon as
the unit is one over the chosen terminal object and the chosen morphism of terminal objects is
an isomorphism: the comparison is that unit component, restricted along that morphism and read
through the two identifications of global sections with sections over a terminal object. -/
public theorem mono_globalSectionsPullbackComparison_app
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) {U : C} {V : D}
    (hU : IsTerminal U) (hV : IsTerminal V) (g : V ⟶ G.obj U) (F : Sheaf J A)
    [Mono ((adj.unit.app F).hom.app (op U))] [IsIso g] :
    Mono ((globalSectionsPullbackComparison G A J K adj hU hV g).app F) := by
  have key {W₁ W₂ W₃ : A} {p : W₁ ⟶ W₂} {q : W₂ ⟶ W₃} (_ : Mono p) (_ : Mono q) :
      Mono (p ≫ q) := mono_comp p q
  rw [globalSectionsPullbackComparison_app, sectionsPullbackComparison_app]
  have h₁ : Mono ((Sheaf.ΓNatIsoSheafSections J A hU).hom.app F) := inferInstance
  have h₂ : Mono ((P.obj F).obj.map g.op) := inferInstance
  have h₃ : Mono ((Sheaf.ΓNatIsoSheafSections K A hV).inv.app (P.obj F)) := inferInstance
  exact key h₁ (key (key inferInstance h₂) h₃)

end Stacks.Sites

namespace Stacks.EtaleCohomology

open CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The stalk of the unit at a geometric point of `Y` which factors through `f` is
injective.** The stalk of `f^{-1}𝒢` at `s` is the stalk of `𝒢` at `s ≫ f`, and composing the
stalk of the unit with that identification and with the stalk of the counit returns the
identification, by the triangle identity of the adjunction. -/
public theorem injective_sheafFiber_map_smallEtaleUnit
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    Function.Injective ((pointSmallEtale (s ≫ f)).sheafFiber.map
      ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app G)) := by
  set adj := smallEtaleInverseImageAdjunction.{u, v} f
  set e := smallEtaleInverseImageStalkIso.{v, u} f s
  have htri : (smallEtaleInverseImage.{u, v} f ⋙
        (pointSmallEtale s).sheafFiber).map (adj.unit.app G) ≫
      (pointSmallEtale s).sheafFiber.map
        (adj.counit.app ((smallEtaleInverseImage.{u, v} f).obj G)) =
      𝟙 ((smallEtaleInverseImage.{u, v} f ⋙ (pointSmallEtale s).sheafFiber).obj G) := by
    rw [Functor.comp_map, ← Functor.map_comp, adj.left_triangle_components G]
    exact CategoryTheory.Functor.map_id _ _
  have hfac : (pointSmallEtale (s ≫ f)).sheafFiber.map (adj.unit.app G) ≫
      (e.inv.app ((smallEtaleInverseImage.{u, v} f ⋙
          (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
            (smallEtaleTopology Y) (smallEtaleTopology X)).obj G) ≫
        (pointSmallEtale s).sheafFiber.map
          (adj.counit.app ((smallEtaleInverseImage.{u, v} f).obj G))) = e.inv.app G := by
    rw [← Category.assoc, e.inv.naturality (adj.unit.app G), Category.assoc, htri]
    exact Category.comp_id _
  exact (mono_iff_injective _).1 (mono_of_mono_fac hfac)

/-- For a surjective morphism the unit `𝒢 ⟶ f_* f^{-1}𝒢` is locally injective: the geometric
points of `Y` coming from the points of `X` cover `Y`, and the stalk of the unit at each of them
is injective. -/
public theorem isLocallyInjective_smallEtaleUnit_of_surjective [Surjective f]
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    Sheaf.IsLocallyInjective ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app G) := by
  refine isLocallyInjective_of_injective_sheafFiber_map.{u, u, u + 1, max (u + 1) v}
    (ObjectProperty.ofObj fun x : X => pointSmallEtale (residueGeometricPoint X x ≫ f))
    (Scheme.isConservative_pointSmallEtale _ ?_) _ ?_
  · ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := f.surjective y
    refine ⟨x, default, ?_⟩
    rwa [Scheme.Hom.comp_apply, residueGeometricPoint_apply]
  · rintro ⟨_, ⟨x⟩⟩
    exact injective_sheafFiber_map_smallEtaleUnit f _ G

/-- **The augmentation is a monomorphism.** For a surjective morphism of schemes the unit
`𝒢 ⟶ f_* f^{-1}𝒢` of the inverse-image/direct-image adjunction on sheaves of sets on the small
étale sites is a monomorphism. For a finite surjective `f` this is injectivity of the
augmentation `𝒢 ⟶ f_{0,*}f_0^{-1}𝒢`, the zeroth level of the Čech nerve being `X` itself; the
equalizer presentation of [Stacks, Tag 09Z3] is
`Stacks.EtaleCohomology.globalSectionsPullback_isEqualizer_of_isFinite_surjective`. -/
@[sga "4 VIII 9.1"]
public theorem mono_smallEtaleUnit_of_surjective [Surjective f]
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    Mono ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app G) :=
  have := isLocallyInjective_smallEtaleUnit_of_surjective f G
  Sheaf.mono_of_isLocallyInjective _

/-- For a surjective morphism the unit `𝒢 ⟶ f_* f^{-1}𝒢` is injective on the sections over
every object of the small étale site of `Y`. -/
public theorem injective_smallEtaleUnit_app_of_surjective [Surjective f]
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : Y.Etaleᵒᵖ) :
    Function.Injective
      (((smallEtaleInverseImageAdjunction.{u, v} f).unit.app G).hom.app V) :=
  (Sheaf.isLocallyInjective_iff_injective _).1
    (isLocallyInjective_smallEtaleUnit_of_surjective f G) V

/-- For a surjective morphism the comparison `Γ(Y, 𝒢) ⟶ Γ(X, f^{-1}𝒢)` on global sections of
sheaves of sets on the small étale sites is a monomorphism. Base change carries a terminal
object to a terminal object, so the restriction appearing in the comparison is along an
isomorphism and the comparison is the unit over the terminal object up to isomorphisms. -/
public theorem mono_smallEtaleGlobalSectionsComparison_of_surjective [Surjective f]
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    Mono ((smallEtaleGlobalSectionsComparison.{u, v} f).app G) :=
  have : Mono (((smallEtaleInverseImageAdjunction.{u, v} f).unit.app G).hom.app
      (op (terminal Y.Etale))) :=
    (mono_iff_injective _).2 (injective_smallEtaleUnit_app_of_surjective f G _)
  have : IsIso ((isTerminalSmallEtaleBaseChangeObjTerminal f).from (terminal X.Etale)) :=
    ⟨⟨terminalIsTerminal.from _, terminalIsTerminal.hom_ext _ _,
      (isTerminalSmallEtaleBaseChangeObjTerminal f).hom_ext _ _⟩⟩
  Stacks.Sites.mono_globalSectionsPullbackComparison_app (smallEtaleBaseChange f)
    (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X)
    (smallEtaleInverseImageAdjunction.{u, v} f) terminalIsTerminal terminalIsTerminal
    ((isTerminalSmallEtaleBaseChangeObjTerminal f).from (terminal X.Etale)) G

/-- **The comparison on global sections is injective** for a surjective morphism of schemes:
`Γ(Y, 𝒢) ⟶ Γ(X, f^{-1}𝒢)` is injective. For a finite surjective `f` this is injectivity of the
fork map of the equalizer presentation of [Stacks, Tag 09Z3], which is proved in full as
`Stacks.EtaleCohomology.globalSectionsPullback_isEqualizer_of_isFinite_surjective`;  surjectivity
of the morphism alone, with no finiteness, already gives the injectivity. -/
public theorem injective_smallEtaleGlobalSectionsComparison_of_surjective [Surjective f]
    (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    Function.Injective ((smallEtaleGlobalSectionsComparison.{u, v} f).app G) :=
  (mono_iff_injective _).1 (mono_smallEtaleGlobalSectionsComparison_of_surjective f G)

/-- **Inverse image along a surjective morphism is faithful** on sheaves of sets on the small
étale sites: the unit of the adjunction is a monomorphism. -/
public theorem faithful_smallEtaleInverseImage_of_surjective [Surjective f] :
    (smallEtaleInverseImage.{u, v} f).Faithful :=
  have (G : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
      Mono ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app G) :=
    mono_smallEtaleUnit_of_surjective f G
  (smallEtaleInverseImageAdjunction.{u, v} f).faithful_L_of_mono_unit_app

end Stacks.EtaleCohomology

end
