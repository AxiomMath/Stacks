module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Functoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of relative differentials of schemes

A commutative square of schemes induces a canonical morphism from the pullback of the sheaf
of relative differentials of its right edge to the sheaf of relative differentials of its
left edge. It is uniquely determined by compatibility with the universal derivations.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsRelativeDifferentialsMap` expresses compatibility of a
  morphism of relative differentials with the universal derivations on every open set.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap` is the canonical morphism induced
  by a commutative square of schemes.
* `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials` is the canonical morphism
  `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair `X ⟶ Y ⟶ S`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.existsUnique_relativeDifferentialsMap` gives existence and
  uniqueness of the morphism compatible with the universal derivations.
* `AlgebraicGeometry.Scheme.Hom.isRelativeDifferentialsMap_iff_eq` characterizes the
  canonical morphism by that compatibility.
* `AlgebraicGeometry.Scheme.Hom.isRelativeDifferentialsMap_comp` and
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp`: the canonical morphisms of two
  squares stacked horizontally compose to the canonical morphism of the outer square.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp_toRelativeDifferentials`: the
  special case in which the second square is the one computing `Ω_{X/S} ⟶ Ω_{X/Y}`.

## Implementation notes

Compatibility is stated on sections, after transposing the morphism across the
pullback-pushforward adjunction on sheaves of modules; so existence and uniqueness
simultaneously record that the composite with the pushed-forward universal derivation is a
derivation and that its adjoint is uniquely characterized. `relativeDifferentialsMap` chooses
that unique morphism, and `isRelativeDifferentialsMap_iff_eq` exposes its defining property
without unfolding the choice.

Horizontal composition of squares is stated at the level of the defining compatibility rather
than of the chosen morphisms, so that no compatibility of choices has to be checked by hand: the
composite of two compatible morphisms is compatible, and the equation of chosen morphisms then
follows from uniqueness. The intermediate structure morphism of the stacked square is an
arbitrary `q : X' ⟶ S` together with `f ≫ p = q`, not the composite `f ≫ p` itself, so that
no transport along that equation is needed.

Everything is transported from the corresponding statements for a square of ringed spaces,
along the underlying ringed space of a scheme: the structural map of a morphism of schemes
and the structural map of the induced morphism of ringed spaces are the same transpose.

## References

* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism from the pullback of `Ω_{X/S}` to `Ω_{X'/S'}` is a map of relative
differentials when its adjoint sends the universal differential of every local section to the
universal differential of its pullback. -/
def IsRelativeDifferentialsMap {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S')
    (c : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶
      relativeDifferentials p') : Prop :=
  ∀ (U : X.Opens) (h : Γ(X, U)),
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
        (relativeDifferentials p) (relativeDifferentials p') c).val.app (.op U)).hom
          ((universalRelativeDerivation p).d h) =
      (universalRelativeDerivation p').d ((f.app U).hom h)

/-- Being a map of relative differentials of a square of schemes is being one for the induced
square of ringed spaces. -/
private lemma isRelativeDifferentialsMap_iff_ringedSpace {X' X S' S : Scheme.{u}}
    (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S')
    (c : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶
      relativeDifferentials p') :
    IsRelativeDifferentialsMap f p p' c ↔
      SheafOfModules.IsDifferentialMap f.toLRSHom.toShHom p.toLRSHom.toShHom
        p'.toLRSHom.toShHom c :=
  Iff.rfl

/-- The square of ringed spaces underlying a commutative square of schemes commutes. -/
lemma toShHom_comm {X' X S' S : Scheme.{u}} {f : X' ⟶ X} {p : X ⟶ S} {p' : X' ⟶ S'}
    {g : S' ⟶ S} (hcomm : f ≫ p = p' ≫ g) :
    f.toLRSHom.toShHom ≫ p.toLRSHom.toShHom =
      p'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom := by
  have hL : f.toLRSHom ≫ p.toLRSHom = p'.toLRSHom ≫ g.toLRSHom := by
    simpa only [Scheme.Hom.comp_toLRSHom] using congrArg Scheme.Hom.toLRSHom hcomm
  simpa only [LocallyRingedSpace.comp_toShHom] using
    congrArg LocallyRingedSpace.Hom.toShHom hL

/-- A commutative square of schemes induces a unique morphism `f^* Ω_{X/S} ⟶ Ω_{X'/S'}`
carrying the universal differential of every local section to the universal differential of
its pullback. -/
@[stacks 01UV,
  ega "IV 16.5.13" "more general",
  ega "IV 17.3.6" "more general",
  sga "3 III 0.1.7" "partial"]
theorem existsUnique_relativeDifferentialsMap {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    ∃! c : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶
      relativeDifferentials p', IsRelativeDifferentialsMap f p p' c := by
  obtain ⟨c, hc, hu⟩ := SheafOfModules.existsUnique_differentialMap
    f.toLRSHom.toShHom p.toLRSHom.toShHom p'.toLRSHom.toShHom g.toLRSHom.toShHom
    (toShHom_comm hcomm)
  exact ⟨c, (isRelativeDifferentialsMap_iff_ringedSpace f p p' c).mpr hc,
    fun d hd => hu d ((isRelativeDifferentialsMap_iff_ringedSpace f p p' d).mp hd)⟩

/-- The canonical morphism `f^* Ω_{X/S} ⟶ Ω_{X'/S'}` associated to a commutative square of
schemes. -/
noncomputable def relativeDifferentialsMap {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶ relativeDifferentials p' :=
  Classical.choose (existsUnique_relativeDifferentialsMap f p p' g hcomm)

/-- The canonical morphism of a commutative square is compatible with the universal
derivations. -/
private lemma isRelativeDifferentialsMap_relativeDifferentialsMap {X' X S' S : Scheme.{u}}
    (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) :
    IsRelativeDifferentialsMap f p p' (relativeDifferentialsMap f p p' g hcomm) :=
  (Classical.choose_spec (existsUnique_relativeDifferentialsMap f p p' g hcomm)).1

/-- Compatibility with the universal derivations characterizes the canonical morphism on
relative differentials associated to a commutative square of schemes. -/
@[stacks 01UV "characterization of the canonical map"]
theorem isRelativeDifferentialsMap_iff_eq {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g)
    (c : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶
      relativeDifferentials p') :
    IsRelativeDifferentialsMap f p p' c ↔ c = relativeDifferentialsMap f p p' g hcomm := by
  refine ⟨fun hc => (Classical.choose_spec
    (existsUnique_relativeDifferentialsMap f p p' g hcomm)).2 c hc, fun hc => ?_⟩
  rw [hc]
  exact isRelativeDifferentialsMap_relativeDifferentialsMap f p p' g hcomm

/-- The canonical morphism `Ω_{X/S} ⟶ Ω_{X/Y}` of a composable pair `X ⟶ Y ⟶ S`, obtained
from the canonical morphism of the square whose horizontal edges are the identity of `X` and
`g`. -/
noncomputable def toRelativeDifferentials {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) :
    relativeDifferentials (f ≫ g) ⟶ relativeDifferentials f :=
  ((Scheme.Modules.pullbackId X).inv.app (relativeDifferentials (f ≫ g))) ≫
    relativeDifferentialsMap (𝟙 X) (f ≫ g) f g (by simp)

/-- The transpose of a morphism out of the pullback along an identity is its action on sections,
read through the component of the isomorphism identifying that pullback with the identity
functor. -/
theorem pullbackId_adjoint_apply {X : Scheme.{u}} (M N : X.Modules)
    (b : (Scheme.Modules.pullback (𝟙 X)).obj M ⟶ N) (U : X.Opens)
    (s : M.presheaf.obj (.op U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv M N b).val.app
      (.op U)).hom s =
      (b.app U).hom ((((Scheme.Modules.pullbackId X).inv.app M).app U).hom s) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)
  let i := (Scheme.Modules.pullbackId X).inv.app M
  have hu := unit_conjugateEquiv Adjunction.id adj (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at hu
  have hpid : (Scheme.Modules.pushforwardId X).inv.app M =
      adj.unit.app M ≫ (Scheme.Modules.pushforward (𝟙 X)).map
        ((Scheme.Modules.pullbackId X).hom.app M) := by simpa using hu
  have hunit : adj.unit.app M = (Scheme.Modules.pushforwardId X).inv.app M ≫
      (Scheme.Modules.pushforward (𝟙 X)).map i := by
    have hc := congrArg (fun t => t ≫ (Scheme.Modules.pushforward (𝟙 X)).map i) hpid
    simpa [Functor.map_comp, Category.assoc] using hc.symm
  rw [Adjunction.homEquiv_apply, hunit]
  show (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward (𝟙 X)).map b) U)
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pushforward (𝟙 X)).map i) U)
        ((Scheme.Modules.Hom.app ((Scheme.Modules.pushforwardId X).inv.app M) U) s)) = _
  rw [Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardId_inv_app_app]
  rfl

/-- **The canonical morphisms of two squares stacked horizontally compose to the canonical
morphism of the outer square**, in the form of the defining compatibility: if `a` is compatible
with the universal derivations for the square with structure morphisms `p` and `q`, and `b` is
compatible for the square with structure morphisms `q` and `p'` whose source morphism is the
identity, then their composite is compatible for the square with structure morphisms `p` and
`p'`. The composite is read through the component of the isomorphism identifying the pullback
along an identity with the identity functor. -/
theorem isRelativeDifferentialsMap_comp {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S)
    (q : X' ⟶ S) (p' : X' ⟶ S')
    (a : (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶ relativeDifferentials q)
    (b : (Scheme.Modules.pullback (𝟙 X')).obj (relativeDifferentials q) ⟶
      relativeDifferentials p')
    (ha : IsRelativeDifferentialsMap f p q a)
    (hb : IsRelativeDifferentialsMap (𝟙 X') q p' b) :
    IsRelativeDifferentialsMap f p p'
      (a ≫ ((Scheme.Modules.pullbackId X').inv.app (relativeDifferentials q) ≫ b)) := by
  intro U s
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let Ωq : X'.Modules := relativeDifferentials q
  let Ωp' : X'.Modules := relativeDifferentials p'
  let i := (Scheme.Modules.pullbackId X').inv.app Ωq
  have hn := adj.homEquiv_naturality_right a (i ≫ b)
  have hnval := congrArg (fun e => (e.val.app (.op U)).hom
    ((universalRelativeDerivation p).d s)) hn
  rw [hnval]
  show (((Scheme.Modules.pushforward f).map (i ≫ b)).app U).hom
      (((adj.homEquiv (relativeDifferentials p) Ωq a).val.app (.op U)).hom
        ((universalRelativeDerivation p).d s)) = _
  rw [ha U s]
  have hmap : (((Scheme.Modules.pushforward f).map (i ≫ b)).app U).hom
      ((universalRelativeDerivation q).d ((f.app U).hom s)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X')).homEquiv Ωq Ωp' b).val.app
        (.op (f ⁻¹ᵁ U))).hom ((universalRelativeDerivation q).d ((f.app U).hom s)) := by
    show ((i ≫ b).app (f ⁻¹ᵁ U)).hom
        ((universalRelativeDerivation q).d ((f.app U).hom s)) = _
    show (b.app (f ⁻¹ᵁ U)).hom ((i.app (f ⁻¹ᵁ U)).hom
        ((universalRelativeDerivation q).d ((f.app U).hom s))) = _
    exact (pullbackId_adjoint_apply Ωq Ωp' b (f ⁻¹ᵁ U) _).symm
  rw [hmap]
  exact hb (f ⁻¹ᵁ U) ((f.app U).hom s)

/-- **The canonical morphisms of two squares stacked horizontally compose to the canonical
morphism of the outer square.** The intermediate structure morphism `q` is only required to
satisfy `f ≫ p = q`. -/
theorem relativeDifferentialsMap_comp {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S)
    (q : X' ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hq : f ≫ p = q) (hcomm : q = p' ≫ g) :
    relativeDifferentialsMap f p q (𝟙 S) (hq.trans (Category.comp_id q).symm) ≫
        ((Scheme.Modules.pullbackId X').inv.app (relativeDifferentials q) ≫
          relativeDifferentialsMap (𝟙 X') q p' g ((Category.id_comp q).trans hcomm)) =
      relativeDifferentialsMap f p p' g (hq.trans hcomm) :=
  (isRelativeDifferentialsMap_iff_eq f p p' g (hq.trans hcomm) _).mp
    (isRelativeDifferentialsMap_comp f p q p' _ _
      (isRelativeDifferentialsMap_relativeDifferentialsMap f p q (𝟙 S) _)
      (isRelativeDifferentialsMap_relativeDifferentialsMap (𝟙 X') q p' g _))

/-- **The canonical morphism of a commutative square factors through the canonical morphism of
the composable pair formed by its two right-hand edges.** This is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp` in the case where the second square
is the one defining `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials`. -/
theorem relativeDifferentialsMap_comp_toRelativeDifferentials {X' X Y S : Scheme.{u}}
    (r : X' ⟶ X) (p : X ⟶ S) (s : X' ⟶ Y) (f : Y ⟶ S) (hcomm : r ≫ p = s ≫ f) :
    relativeDifferentialsMap r p (s ≫ f) (𝟙 S) (hcomm.trans (Category.comp_id (s ≫ f)).symm) ≫
        s.toRelativeDifferentials f =
      relativeDifferentialsMap r p s f hcomm :=
  relativeDifferentialsMap_comp r p (s ≫ f) s f hcomm rfl

end AlgebraicGeometry.Scheme.Hom
