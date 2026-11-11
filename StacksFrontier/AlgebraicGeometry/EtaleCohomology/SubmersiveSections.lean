module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Maps.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkSectionsTransitivity
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections under a universally submersive morphism with connected fibres

Let `f : X ⟶ S` be universally submersive with geometrically connected fibres. Pulling back a
sheaf of sets on the small étale site of `S` to the small étale site of `X` does not change its
global sections: `Γ(S, F) = Γ(X, f^{-1} F)`.

## The shape of the argument

The comparison map `Γ(S, F) ⟶ Γ(X, f^{-1} F)` is the one induced by the unit of the
inverse-image/direct-image adjunction, using that base change `S.Etale ⥤ X.Etale` is a final
functor, so that global sections upstairs are the limit of the sections over base changes of
objects downstairs.

Injectivity comes from the surjectivity of `f`: for two global sections the locus where their
germs agree is an open `W` of the base, and `W` pulls back to the corresponding locus upstairs,
so a section agreeing everywhere upstairs agrees everywhere downstairs.

Surjectivity is local. The stalk of `f^{-1} F` at a geometric point `x` of `X` is the stalk of
`F` at `x ≫ f`, so a germ of `f^{-1} F` is represented by an étale neighbourhood `V` of `S` and
a section `s` of `F` over `V`. The agreement locus of the pullback of `s` with the given global
section `t` of `f^{-1} F` is open, and over a geometric fibre of `f` the sheaf `f^{-1} F` becomes
constant, so that locus is also closed; connectedness of the fibres makes it saturated for the
base change of `f` along `V`, and submersivity of that base change then descends it to an open
of `V`. This produces an étale covering of `S` over which `t` comes from sections of `F`, which
glue by the injectivity already proved.

## Stacks erratum

Only the base changes of `f` along étale morphisms are ever asked to be submersive, and plain
submersivity of `f` does not give that. The source states the tag with `f` merely submersive,
and in that form it is FALSE; the hypothesis of universal submersivity carried here is the
corrected one, not a convenience.

The counterexample is in characteristic `2`. Let `k` be a field of characteristic `2`, let
`A = {g ∈ k[t] ∣ g(0) = g(1)}` be the node — the affine line with `t = 0` and `t = 1` glued —
and let `B = k[t, 1/t]` be the affine line with `t = 0` removed. The morphism
`f : Spec B ⟶ Spec A` is the homeomorphism described in the Stacks proof: it is bijective
because the node has already glued the removed point `t = 0` to the surviving point `t = 1`,
and it is submersive with geometrically connected fibres, while being neither integral nor
universally submersive. Let `a = t² + t`, which lies in `A` because `a(0) = 0 = a(1)` in
characteristic `2`, and let `T = Spec A[z]/(z² + z + a)`, the connected étale double cover of
`Spec A` — étale because the derivative of `z² + z + a` in `z` is the unit `1`. Take
`F = h_T`, the functor of points of `T`. Then `Γ(S, F)` is EMPTY: a root of `z² + z + a` in
`k[t]` is `t` or `t + 1`, and neither takes the same value at `0` and at `1`, so neither lies
in `A`. But `Γ(X, f⁻¹F)` has TWO elements, `t` and `t + 1`, both of which lie in `B`. So the
claimed equality `Γ(S, F) = Γ(X, f⁻¹F)` fails, and the base change `X ×_S T ⟶ T` is a
disjoint union of two copies of `X` mapping bijectively but not homeomorphically onto `T`,
which is exactly the step of the source proof that submersivity alone does not license.

## Main results

* `Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage` — the canonical comparison
  from global sections downstairs to global sections of the inverse image upstairs is an
  isomorphism. This is the tag in the form the source asserts it.
* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso` — the same statement packaged
  as an isomorphism of global-sections functors, natural in the sheaf.
* `Stacks.EtaleCohomology.isIso_smallEtaleInverseImageSections` — the localized form: for a
  morphism `a : U ⟶ V ×_S X` of the small étale site of `X` whose induced morphism `U ⟶ V` is
  universally submersive with geometrically connected fibres, the comparison `G(V) ⟶ (f⁻¹G)(U)`
  is an isomorphism.

## Implementation notes

The equality of section sets of the source is expressed as a natural isomorphism of
global-sections functors, which records both that the comparison is the canonical one and that
it is natural in the sheaf. Geometric connectedness of the fibres is Mathlib's morphism property
`GeometricallyConnected`, and submersivity is `(topologically Topology.IsQuotientMap).universally`.

Geometric points of a scheme are morphisms from the spectrum of a separably closed field, and
the stalk of a sheaf at such a point is `CategoryTheory.GrothendieckTopology.Point.sheafFiber`
for the point of the small étale site that the geometric point determines.

## References

* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MorphismProperty
open AlgebraicGeometry.Scheme

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

universe u v

namespace Stacks.EtaleCohomology

/-- The Mathlib instance `Scheme.instHasSheafifyEtaleSmallEtaleTopology` (for `Category.{u}`
coefficients) is tried first and its universe constraint fails hard while a universe level is
still a metavariable; this instance for sheaves of types answers first. -/
private instance (priority := high) hasSheafifySmallEtaleType (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (Type (max (u + 1) v)) := inferInstance

/-- The final object of the small étale site of `S`: the identity of `S`, viewed as an étale
`S`-scheme. -/
private abbrev smallEtaleFinal (S : Scheme.{u}) : S.Etale := Scheme.Etale.mk (𝟙 S)

/-- The final object of the small étale site is final. -/
private def isTerminalSmallEtaleFinal (S : Scheme.{u}) : IsTerminal (smallEtaleFinal S) :=
  let : IsIso (smallEtaleFinal S).hom := inferInstanceAs (IsIso (𝟙 S))
  isTerminalOfIsIsoHom (smallEtaleFinal S)

/-- The unique morphism from an étale `S`-scheme to the final object of the small étale site. -/
private def smallEtaleToFinal {S : Scheme.{u}} (U : S.Etale) : U ⟶ smallEtaleFinal S :=
  MorphismProperty.Over.homMk U.hom (by
    change U.hom ≫ 𝟙 S = U.hom
    simp)

/-- A geometric point of `S`, viewed as a point of the final object of the small étale site. -/
private def smallEtaleFinalPoint {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ S) : (pointSmallEtale x).fiber.obj (smallEtaleFinal S) :=
  CategoryTheory.Over.homMk x (by
    change x ≫ 𝟙 S = x
    simp)

private def baseChangeTerminal {T S : Scheme.{u}} (f : T ⟶ S) :
    IsTerminal ((smallEtaleBaseChange f).obj (smallEtaleFinal S)) :=
  isTerminalSmallEtaleBaseChangeObj f (isTerminalSmallEtaleFinal S)

private instance smallEtaleBaseChange_final {T S : Scheme.{u}} (f : T ⟶ S) :
    (smallEtaleBaseChange f).Final := by
  let terminal : S.Etale := smallEtaleFinal S
  have : (Functor.fromPUnit.{u} terminal).Final := Functor.final_fromPUnit_of_isTerminal
    (isTerminalSmallEtaleFinal S)
  have : (Functor.fromPUnit.{u} ((smallEtaleBaseChange f).obj terminal)).Final :=
    Functor.final_fromPUnit_of_isTerminal (baseChangeTerminal f)
  have : (Functor.fromPUnit.{u} terminal ⋙ smallEtaleBaseChange f).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{u}
      ((smallEtaleBaseChange f).obj terminal)) (Discrete.natIso (fun _ ↦ Iso.refl _))
  exact Functor.final_of_final_comp (Functor.fromPUnit.{u} terminal) _

private def smallEtaleBaseChangeGlobalSectionsIsLimit {T S : Scheme.{u}} (f : T ⟶ S)
    (H : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    IsLimit (H.coneΓ.whisker (smallEtaleBaseChange f).op) :=
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm H.isLimitConeΓ

private def globalSectionsComparisonApp {T S : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) :
    (Sheaf.Γ _ _).obj G ⟶ (Sheaf.Γ _ _).obj ((smallEtaleInverseImage f).obj G) :=
  (smallEtaleBaseChangeGlobalSectionsIsLimit f _).lift
    ⟨_, G.coneΓ.π ≫ ((smallEtaleInverseImageAdjunction f).unit.app G).hom⟩

/-- The unit of the inverse-image/direct-image adjunction at an étale `S`-scheme `V`, read as a
map from the sections of `G` over `V` to the sections of the inverse image over the base
change of `V`. -/
@[expose] public def smallEtaleUnitApp {T S : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) (V : S.Etale) :
    G.obj.obj (Opposite.op V) ⟶
      ((smallEtaleInverseImage f).obj G).obj.obj
        (Opposite.op ((smallEtaleBaseChange f).obj V)) :=
  ((smallEtaleInverseImageAdjunction f).unit.app G).hom.app (Opposite.op V)

private lemma smallEtaleUnitApp_naturality {T S : Scheme.{u}} (f : T ⟶ S)
    {G H : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))} (a : G ⟶ H) (V : S.Etale) :
    a.hom.app (Opposite.op V) ≫ smallEtaleUnitApp f H V =
      smallEtaleUnitApp f G V ≫ ((smallEtaleInverseImage f).map a).hom.app
        (Opposite.op ((smallEtaleBaseChange f).obj V)) :=
  congrArg (fun morphism ↦ morphism.hom.app (Opposite.op V))
    ((smallEtaleInverseImageAdjunction f).unit.naturality a)

private lemma globalSectionsComparisonApp_ΓRes {T S : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) (V : S.Etale) :
    globalSectionsComparisonApp f G ≫ ((smallEtaleInverseImage f).obj G).ΓRes
        (Opposite.op ((smallEtaleBaseChange f).obj V)) =
      G.ΓRes (Opposite.op V) ≫ smallEtaleUnitApp f G V :=
  (smallEtaleBaseChangeGlobalSectionsIsLimit f _).fac _ (Opposite.op V)

/-- The canonical comparison `Γ(S, F) ⟶ Γ(X, f⁻¹F)`, natural in the sheaf `F`: on a sheaf it is
the map induced by the unit of the inverse-image/direct-image adjunction, read through the
identification of global sections upstairs with the limit of the sections over base changes of
étale `S`-schemes. Tag 0EZK asserts that this transformation is an isomorphism, which is
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage`. -/
public def globalSectionsSmallEtaleInverseImage {T S : Scheme.{u}} (f : T ⟶ S) :
    Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ⟶
      smallEtaleInverseImage f ⋙
        Sheaf.Γ (smallEtaleTopology T) (Type (max (u + 1) v)) where
  app G := globalSectionsComparisonApp f G
  naturality G H a := by
    apply (smallEtaleBaseChangeGlobalSectionsIsLimit f _).hom_ext
    intro V
    have key : ((Sheaf.Γ _ _).map a ≫ globalSectionsComparisonApp f H) ≫
        ((smallEtaleInverseImage f).obj H).ΓRes
          (Opposite.op ((smallEtaleBaseChange f).obj V.unop)) =
      (globalSectionsComparisonApp f G ≫
        (Sheaf.Γ _ _).map ((smallEtaleInverseImage f).map a)) ≫
        ((smallEtaleInverseImage f).obj H).ΓRes
          (Opposite.op ((smallEtaleBaseChange f).obj V.unop)) := by
      rw [Category.assoc, globalSectionsComparisonApp_ΓRes, ← Category.assoc,
        Sheaf.ΓRes_naturality]
      conv_rhs =>
        rw [Category.assoc, Sheaf.ΓRes_naturality, ← Category.assoc,
          globalSectionsComparisonApp_ΓRes]
      rw [Category.assoc, Category.assoc, smallEtaleUnitApp_naturality]
    exact key

/-- The canonical comparison from the sections of `G` over an étale `S`-scheme `V` to the
sections of `f⁻¹G` over an étale `T`-scheme `U` given over `V`: the unit of the inverse-image
adjunction at `V`, followed by restriction along `a : U ⟶ V ×_S T`. -/
@[expose] public def smallEtaleInverseImageSections {T S : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)))
    {U : T.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V) :
    G.obj.obj (Opposite.op V) ⟶
      ((smallEtaleInverseImage f).obj G).obj.obj (Opposite.op U) :=
  smallEtaleUnitApp f G V ≫ ((smallEtaleInverseImage f).obj G).obj.map a.op

private lemma globalSectionsComparison_ΓRes
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale) :
    (globalSectionsSmallEtaleInverseImage f).app F ≫
      ((smallEtaleInverseImage f).obj F).ΓRes
        (Opposite.op ((smallEtaleBaseChange f).obj U)) =
    F.ΓRes (Opposite.op U) ≫ smallEtaleUnitApp f F U :=
  globalSectionsComparisonApp_ΓRes f F U

private lemma globalSectionsSmallEtaleInverseImage_app_ΓRes {T S : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)))
    {U : T.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V) :
    (globalSectionsSmallEtaleInverseImage f).app G ≫
        ((smallEtaleInverseImage f).obj G).ΓRes (Opposite.op U) =
      G.ΓRes (Opposite.op V) ≫ smallEtaleInverseImageSections f G a := by
  dsimp [smallEtaleInverseImageSections, globalSectionsSmallEtaleInverseImage]
  rw [← Category.assoc, ← globalSectionsComparisonApp_ΓRes, Category.assoc, Sheaf.ΓRes_map]

/-- If `a : T ⟶ V ×_S X` is a morphism over `X`, lying over `x : T ⟶ X`, then its first
projection lies over `x ≫ f`. -/
private lemma pullback_fst_comp_eq {X S T W : Scheme.{u}} (f : X ⟶ S) (x : T ⟶ X) (g : W ⟶ S)
    (a : T ⟶ pullback g f) (ha : a ≫ pullback.snd g f = x) :
    (a ≫ pullback.fst g f) ≫ g = x ≫ f := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, ha]

/-- A morphism to a fibre product is recovered from its two projections. -/
private lemma pullback_lift_fst_eq {X S T W : Scheme.{u}} (f : X ⟶ S) (x : T ⟶ X) (g : W ⟶ S)
    (a : T ⟶ pullback g f) (ha : a ≫ pullback.snd g f = x)
    (h : (a ≫ pullback.fst g f) ≫ g = x ≫ f) :
    pullback.lift (a ≫ pullback.fst g f) x h = a := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst]
  · rw [pullback.lift_snd, ha]

/-- Base change along `f` of a morphism of schemes over `S`, read on the first projections. -/
private lemma overPullback_map_left_fst {X S T : Scheme.{u}} (f : X ⟶ S)
    {V W : CategoryTheory.Over S} (a : V ⟶ W) (g : T ⟶ pullback V.hom f) :
    (g ≫ ((CategoryTheory.Over.pullback f).map a).left) ≫ pullback.fst W.hom f =
      (g ≫ pullback.fst V.hom f) ≫ a.left := by
  have h : ((CategoryTheory.Over.pullback f).map a).left ≫ pullback.fst W.hom f =
      pullback.fst V.hom f ≫ a.left := pullback.lift_fst _ _ _
  rw [Category.assoc, Category.assoc, h]

/-- Lifting `x : T ⟶ X` to the base change along `f` of a scheme `V` over `S` is the same thing
as lifting `x ≫ f` to `V`. This is the hom-set bijection of `Over.mapPullbackAdj f`. -/
private def overPullbackFiberEquiv {X S T : Scheme.{u}} (f : X ⟶ S) (x : T ⟶ X)
    (V : CategoryTheory.Over S) :
    (CategoryTheory.Over.mk x ⟶ (CategoryTheory.Over.pullback f).obj V) ≃
      (CategoryTheory.Over.mk (x ≫ f) ⟶ V) where
  toFun a := CategoryTheory.Over.homMk (a.left ≫ pullback.fst V.hom f)
    (pullback_fst_comp_eq f x V.hom a.left (CategoryTheory.Over.w a))
  invFun a := CategoryTheory.Over.homMk (pullback.lift a.left x (CategoryTheory.Over.w a))
    (pullback.lift_snd _ _ _)
  left_inv a := CategoryTheory.Over.OverMorphism.ext
    (pullback_lift_fst_eq f x V.hom a.left (CategoryTheory.Over.w a) _)
  right_inv _a := CategoryTheory.Over.OverMorphism.ext (pullback.lift_fst _ _ _)

private def smallEtaleBaseChangeFiberIso
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    smallEtaleBaseChange f ⋙ (pointSmallEtale x).fiber ≅
      (pointSmallEtale (x ≫ f)).fiber := by
  refine NatIso.ofComponents (fun V ↦ (show
    ((pointSmallEtale x).fiber.obj ((smallEtaleBaseChange f).obj V)) ≃
      ((pointSmallEtale (x ≫ f)).fiber.obj V) from
    overPullbackFiberEquiv f x ((Etale.forget S).obj V)).toIso) ?_
  intro V W a
  ext b
  refine CategoryTheory.Over.OverMorphism.ext ?_
  exact overPullback_map_left_fst f ((Etale.forget S).map a) b.left

private def smallEtaleSkyscraperIso
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (pointSmallEtale x).skyscraperSheafFunctor (A := Type (max (u + 1) v)) ⋙
        (smallEtaleBaseChange f).sheafPushforwardContinuous
          (Type (max (u + 1) v)) S.smallEtaleTopology X.smallEtaleTopology ≅
      (pointSmallEtale (x ≫ f)).skyscraperSheafFunctor := by
  let A := Type (max (u + 1) v)
  let G := smallEtaleBaseChange f
  let Φ := pointSmallEtale x
  let Ψ := pointSmallEtale (x ≫ f)
  let e := smallEtaleBaseChangeFiberIso f x
  let ep : Φ.skyscraperPresheafFunctor (A := A) ⋙
      (Functor.whiskeringLeft _ _ A).obj G.op ≅
      Ψ.skyscraperPresheafFunctor :=
    (Iso.refl _) ≪≫
      (flipFunctor _ _ _).mapIso
        (Functor.isoWhiskerRight (NatIso.op e.symm) piConst.flip)
  exact (show Φ.skyscraperSheafFunctor (A := A) ⋙
      G.sheafPushforwardContinuous A S.smallEtaleTopology X.smallEtaleTopology ≅
      Ψ.skyscraperSheafFunctor from
    NatIso.ofComponents (fun M ↦
      (fullyFaithfulSheafToPresheaf S.smallEtaleTopology A).preimageIso
        (ep.app M)) (by
          intro M N a
          apply (sheafToPresheaf S.smallEtaleTopology A).map_injective
          exact ep.hom.naturality a))

private def smallEtalePullbackStalkIso
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    smallEtaleInverseImage.{u, v} f ⋙
        (pointSmallEtale x).sheafFiber ≅
      (pointSmallEtale (x ≫ f)).sheafFiber :=
  ((conjugateIsoEquiv
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange f) (Type (max (u + 1) v))
      S.smallEtaleTopology X.smallEtaleTopology).comp
      (pointSmallEtale x).skyscraperSheafAdjunction)
      (pointSmallEtale (x ≫ f)).skyscraperSheafAdjunction).symm
        (smallEtaleSkyscraperIso f x)).symm

private lemma smallEtaleSkyscraperIso_hom_π
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (M : Type (max (u + 1) v)) (V : S.Etale)
    (a : (pointSmallEtale x).fiber.obj ((smallEtaleBaseChange f).obj V)) :
    ((smallEtaleSkyscraperIso f x).hom.app M).hom.app (Opposite.op V) ≫
      Pi.π _ ((smallEtaleBaseChangeFiberIso f x).hom.app V a) = Pi.π _ a := by
  have key : ((smallEtaleSkyscraperIso f x).hom.app M).hom.app (Opposite.op V) =
      Pi.map' (f := fun _ ↦ M) (g := fun _ ↦ M)
        (fun b ↦ (smallEtaleBaseChangeFiberIso f x).inv.app V b) (fun _ ↦ 𝟙 M) := rfl
  have hinv : (smallEtaleBaseChangeFiberIso f x).inv.app V
      ((smallEtaleBaseChangeFiberIso f x).hom.app V a) = a :=
    congrArg (fun b ↦ b a) (congrArg ConcreteCategory.hom
      ((smallEtaleBaseChangeFiberIso f x).hom_inv_id_app V))
  have main : Pi.map' (f := fun _ ↦ M) (g := fun _ ↦ M)
        (fun b ↦ (smallEtaleBaseChangeFiberIso f x).inv.app V b) (fun _ ↦ 𝟙 M) ≫
      Pi.π (fun _ ↦ M) ((smallEtaleBaseChangeFiberIso f x).hom.app V a) =
      Pi.π (fun _ ↦ M) a := by
    rw [Pi.map'_comp_π, Category.comp_id]
    exact congrArg (Pi.π (fun _ ↦ M)) hinv
  rw [key]
  exact main

private lemma skyscraperSheafUnit_π
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (Φ : J.Point.{u}) (H : Sheaf J (Type (max (u + 1) v)))
    (W : C) (b : Φ.fiber.obj W) :
    (((Φ.skyscraperSheafAdjunction (A := Type (max (u + 1) v))).unit.app H).hom.app
      (Opposite.op W)) ≫ Pi.π _ b = Φ.toPresheafFiber W b H.obj := by
  rw [← Adjunction.homEquiv_id]
  have h := Φ.skyscraperSheafAdjunction_homEquiv_apply_hom
    (A := Type (max (u + 1) v)) (F := H) (𝟙 (Φ.presheafFiber.obj H.obj))
  exact (congrArg (fun morphism ↦ morphism.app (Opposite.op W) ≫ Pi.π _ b) h).trans
    ((Φ.skyscraperPresheafHomEquiv_app_π (𝟙 _) W b).trans
      (Category.comp_id _))

/-- Cancelling a natural isomorphism: if `p ≫ m = n ≫ e.hom.app Z`, then
`p ≫ m ≫ e.inv.app Z = n`. -/
private lemma comp_inv_app_of_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F ≅ G) {Z : C} {W W' : D} (p : W' ⟶ W) (m : W ⟶ G.obj Z) (n : W' ⟶ F.obj Z)
    (h : p ≫ m = n ≫ e.hom.app Z) : p ≫ m ≫ e.inv.app Z = n := by
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Rewriting the last two factors of a composite. -/
private lemma comp_comp_comp_eq {C : Type*} [Category C] {W₁ W₂ W₃ W₄ W₅ : C}
    (p : W₁ ⟶ W₂) (q : W₂ ⟶ W₃) {r : W₃ ⟶ W₄} {s : W₄ ⟶ W₅} {t : W₃ ⟶ W₅}
    (ht : r ≫ s = t) : (p ≫ q ≫ r) ≫ s = p ≫ q ≫ t := by
  rw [← ht, Category.assoc, Category.assoc]

/-- Moving a factor past a composite. -/
private lemma comp_comp_eq_comp_comp {C : Type*} [Category C] {W₁ W₂ W₃ W₄ W₅ : C}
    (p : W₁ ⟶ W₂) {q : W₂ ⟶ W₃} {r : W₃ ⟶ W₄} {r' : W₂ ⟶ W₅} {z : W₅ ⟶ W₄}
    (h : q ≫ r = r' ≫ z) : (p ≫ q) ≫ r = (p ≫ r') ≫ z := by
  rw [Category.assoc, h, Category.assoc]

private lemma smallEtalePullbackStalkIso_germ
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale)
    (a : (pointSmallEtale x).fiber.obj ((smallEtaleBaseChange f).obj V)) :
    (((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
      (Opposite.op V)) ≫
      (pointSmallEtale x).toPresheafFiber _ a
        ((smallEtaleInverseImage f).obj F).obj ≫
      (smallEtalePullbackStalkIso f x).hom.app F =
    (pointSmallEtale (x ≫ f)).toPresheafFiber V
      ((smallEtaleBaseChangeFiberIso f x).hom.app V a) F.obj := by
  let adj := (smallEtaleInverseImageAdjunction.{u, v} f).comp
    ((pointSmallEtale x).skyscraperSheafAdjunction (A := Type (max (u + 1) v)))
  let adj' := (pointSmallEtale (x ≫ f)).skyscraperSheafAdjunction
    (A := Type (max (u + 1) v))
  let e := (conjugateIsoEquiv adj adj').symm (smallEtaleSkyscraperIso.{u, v} f x)
  change (((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
    (Opposite.op V)) ≫ ((pointSmallEtale x).toPresheafFiber _ a
      ((smallEtaleInverseImage f).obj F).obj ≫ e.inv.app F) = _
  have h := unit_conjugateEquiv_symm adj adj' (smallEtaleSkyscraperIso f x).hom F
  have h' := congrArg (fun t ↦ t.hom.app (Opposite.op V) ≫
    Pi.π _ ((smallEtaleBaseChangeFiberIso f x).hom.app V a)) h
  simp only [adj, Adjunction.comp_unit_app] at h'
  change (((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
    (Opposite.op V) ≫
    ((((pointSmallEtale x).skyscraperSheafAdjunction
      (A := Type (max (u + 1) v))).unit.app
      ((smallEtaleInverseImage f).obj F)).hom.app
        (Opposite.op ((smallEtaleBaseChange f).obj V))) ≫
    (((smallEtaleSkyscraperIso f x).hom.app _).hom.app (Opposite.op V))) ≫
      Pi.π _ ((smallEtaleBaseChangeFiberIso f x).hom.app V a) = _ at h'
  have hsky := smallEtaleSkyscraperIso_hom_π f x
    ((pointSmallEtale x).sheafFiber.obj ((smallEtaleInverseImage f).obj F)) V a
  have h2 := (comp_comp_comp_eq _ _ hsky).symm.trans h'
  have hh := skyscraperSheafUnit_π (pointSmallEtale x)
    ((smallEtaleInverseImage f).obj F)
    ((smallEtaleBaseChange f).obj V) a
  have hh' := congrArg (fun b ↦
    (((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
      (Opposite.op V)) ≫ b) hh
  have h'' := hh'.symm.trans h2
  change _ = ((((pointSmallEtale (x ≫ f)).skyscraperSheafAdjunction
    (A := Type (max (u + 1) v))).unit.app F).hom.app
    (Opposite.op V) ≫ ((pointSmallEtale (x ≫ f)).skyscraperPresheafFunctor.map
      (((conjugateEquiv adj adj').symm (smallEtaleSkyscraperIso f x).hom).app F)).app
        (Opposite.op V)) ≫ Pi.π _ _ at h''
  change _ = ((((pointSmallEtale (x ≫ f)).skyscraperSheafAdjunction
    (A := Type (max (u + 1) v))).unit.app F).hom.app (Opposite.op V) ≫
      Limits.Pi.map (fun _ ↦ (((conjugateEquiv adj adj').symm
        (smallEtaleSkyscraperIso f x).hom).app F))) ≫ Pi.π _ _ at h''
  have hh₂ := skyscraperSheafUnit_π (pointSmallEtale (x ≫ f)) F V
    ((smallEtaleBaseChangeFiberIso f x).hom.app V a)
  exact comp_inv_app_of_eq e _ _ _ (h''.trans
    ((comp_comp_eq_comp_comp _ (Pi.map_π _ _)).trans
      (congrArg (· ≫ (((conjugateEquiv adj adj').symm
        (smallEtaleSkyscraperIso f x).hom).app F)) hh₂)))

/-- The base change of `f` along every étale morphism to `S` is a quotient map of underlying
topological spaces. -/
private def IsQuotientMapEtaleBaseChange {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ V : S.Etale, Topology.IsQuotientMap (pullback.fst V.hom f)

private theorem isQuotientMapEtaleBaseChange_of_universallySubmersive
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsub : (topologically @Topology.IsQuotientMap :
      MorphismProperty Scheme.{u}).universally f) :
    IsQuotientMapEtaleBaseChange f := fun V ↦
  hsub (pullback.snd V.hom f) V.hom (pullback.fst V.hom f)
    (IsPullback.of_hasPullback V.hom f)

private theorem exists_open_factor_of_quotientMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Topology.IsQuotientMap f) {U : Set X}
    (hU : IsOpen U) (hsat : f ⁻¹' (f '' U) = U) :
    ∃ V : Set Y, IsOpen V ∧ f ⁻¹' V = U := by
  refine ⟨f '' U, ?_, hsat⟩
  exact hf.isCoinducing.isOpen_preimage.mp (by rwa [hsat])

private def globalSectionGerm {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    (Sheaf.Γ _ _).obj F ⟶ (pointSmallEtale x).sheafFiber.obj F :=
  F.ΓRes (Opposite.op (smallEtaleFinal S)) ≫
    (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) (smallEtaleFinalPoint x) F.obj

private lemma globalSectionGerm_eq {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale)
    (a : (pointSmallEtale x).fiber.obj U) :
    globalSectionGerm x F = F.ΓRes (Opposite.op U) ≫
      (pointSmallEtale x).toPresheafFiber U a F.obj := by
  have h := (pointSmallEtale x).toPresheafFiber_w (smallEtaleToFinal U) a F.obj
  have ha : (pointSmallEtale x).fiber.map (smallEtaleToFinal U) a =
      smallEtaleFinalPoint x := by
    apply Over.OverMorphism.ext
    exact CategoryTheory.Over.w a
  rw [ha] at h
  have key : F.ΓRes (Opposite.op (smallEtaleFinal S)) ≫
      (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) (smallEtaleFinalPoint x) F.obj =
        F.ΓRes (Opposite.op U) ≫
          (pointSmallEtale x).toPresheafFiber U a F.obj := by
    rw [← h, ← Category.assoc, Sheaf.ΓRes_map]
  exact key

private def globalSectionsEqOpen {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : (Sheaf.Γ _ _).obj F) : S.Opens :=
  ⨆ U : { U : S.Etale // F.ΓRes (Opposite.op U) s = F.ΓRes (Opposite.op U) t },
    ⟨Set.range U.1.hom, U.1.hom.isOpenMap.isOpen_range⟩

private lemma mem_globalSectionsEqOpen_iff {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : (Sheaf.Γ _ _).obj F) :
    x default ∈ globalSectionsEqOpen F s t ↔
      globalSectionGerm x F s = globalSectionGerm x F t := by
  constructor
  · intro hx
    obtain ⟨⟨U, hU⟩, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨a, ha, _⟩ := exists_fac_of_etale_of_isSepClosed U.hom x y hy
    rw [globalSectionGerm_eq x F U (Over.homMk a ha)]
    exact congrArg ((pointSmallEtale x).toPresheafFiber U (Over.homMk a ha) F.obj) hU
  · intro hx
    let a := smallEtaleFinalPoint x
    change (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) a F.obj
      (F.ΓRes (Opposite.op (smallEtaleFinal S)) s) =
      (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) a F.obj
        (F.ΓRes (Opposite.op (smallEtaleFinal S)) t) at hx
    obtain ⟨U, morphism, b, hb, heq⟩ :=
      ((pointSmallEtale x).toPresheafFiber_eq_iff' (P := F.obj)
        (smallEtaleFinal S) a
        (F.ΓRes (Opposite.op (smallEtaleFinal S)) s)
        (F.ΓRes (Opposite.op (smallEtaleFinal S)) t)).mp hx
    have hU : F.ΓRes (Opposite.op U) s = F.ΓRes (Opposite.op U) t := by
      have hres := F.ΓRes_map morphism.op
      exact (ConcreteCategory.congr_hom hres s).symm.trans
        (heq.trans (ConcreteCategory.congr_hom hres t))
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨⟨U, hU⟩, b.left (default : Spec (.of Ω)), ?_⟩
    exact congrArg (fun morphism : Spec (.of Ω) ⟶ S ↦
      morphism (default : Spec (.of Ω))) (CategoryTheory.Over.w b)

/-- Restriction of global sections to a terminal object of the small étale site is invertible. -/
private lemma globalSections_res_isIso_of_isTerminal
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) {T : S.Etale}
    (hT : IsTerminal T) : IsIso (F.ΓRes (Opposite.op T)) := by
  let iso := F.isLimitConeΓ.conePointUniqueUpToIso (limitOfDiagramInitial hT.op F.obj)
  change IsIso iso.hom
  infer_instance

private lemma globalSections_res_final_isIso
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    IsIso (F.ΓRes (Opposite.op (smallEtaleFinal S))) :=
  globalSections_res_isIso_of_isTerminal F (isTerminalSmallEtaleFinal S)

private lemma globalSectionsEqOpen_eq_top_iff {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : (Sheaf.Γ _ _).obj F) :
    globalSectionsEqOpen F s t = ⊤ ↔ s = t := by
  constructor
  · intro h
    let index := { U : S.Etale // F.ΓRes (Opposite.op U) s = F.ΓRes (Opposite.op U) t }
    let objects : index → S.Etale := fun U ↦ U.1
    let maps : ∀ U : index, objects U ⟶ smallEtaleFinal S := fun U ↦ smallEtaleToFinal U.1
    have hcover : Sieve.ofArrows objects maps ∈ S.smallEtaleTopology (smallEtaleFinal S) := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      ext x
      have hx : x ∈ globalSectionsEqOpen F s t := by rw [h]; trivial
      obtain ⟨U, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨fun _ ↦ trivial, fun _ ↦ Set.mem_iUnion.mpr ⟨U, y, hy⟩⟩
    have heq : F.ΓRes (Opposite.op (smallEtaleFinal S)) s =
        F.ΓRes (Opposite.op (smallEtaleFinal S)) t := by
      apply ((isSheaf_iff_isSheaf_of_type _ F.obj).mp F.property).isSeparated _ hcover |>.ext
      intro U morphism hmorphism
      obtain ⟨V, a, rfl⟩ := Sieve.ofArrows.exists hmorphism
      simp only [op_comp, Functor.map_comp, types_comp_apply]
      apply congrArg (F.obj.map a.op)
      have hs := ConcreteCategory.congr_hom (F.ΓRes_map (maps V).op) s
      have ht := ConcreteCategory.congr_hom (F.ΓRes_map (maps V).op) t
      exact hs.trans (V.2.trans ht.symm)
    exact ((isIso_iff_bijective _).mp (globalSections_res_final_isIso F)).injective heq
  · rintro rfl
    exact top_unique fun x _ ↦
      TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨smallEtaleFinal S, rfl⟩, x, rfl⟩

/-- In a category, if `germ = B ≫ C`, `germ' = E ≫ N`, `A ≫ B = E ≫ G` and `G ≫ C ≫ D = N`, then
`A ≫ germ ≫ D = germ'`. -/
private lemma assoc_eq_of_fac {𝒞 : Type*} [Category 𝒞] {W X Y Z T P : 𝒞}
    {A : W ⟶ X} {B : X ⟶ P} {C : P ⟶ Y} {D : Y ⟶ Z} {E : W ⟶ T} {G : T ⟶ P}
    {N : T ⟶ Z} {germ : X ⟶ Y} {germ' : W ⟶ Z}
    (hgerm : germ = B ≫ C) (hgerm' : germ' = E ≫ N)
    (hfac : A ≫ B = E ≫ G) (hstalk : G ≫ C ≫ D = N) :
    A ≫ germ ≫ D = germ' := by
  rw [hgerm, hgerm', Category.assoc B C D, ← Category.assoc A B (C ≫ D), hfac,
    Category.assoc E G (C ≫ D), hstalk]

private lemma globalSectionGerm_pullback
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    (globalSectionsSmallEtaleInverseImage f).app F ≫
      globalSectionGerm x ((smallEtaleInverseImage f).obj F) ≫
        (smallEtalePullbackStalkIso f x).hom.app F =
      globalSectionGerm (x ≫ f) F := by
  let V := smallEtaleFinal S
  let a : (pointSmallEtale x).fiber.obj ((smallEtaleBaseChange f).obj V) :=
    CategoryTheory.Over.homMk
      (pullback.lift (x ≫ f) x (by
        change (x ≫ f) ≫ 𝟙 S = x ≫ f
        simp)) (by
        change pullback.lift (x ≫ f) x _ ≫ pullback.snd (𝟙 S) f = x
        exact pullback.lift_snd _ _ _)
  exact assoc_eq_of_fac
    (globalSectionGerm_eq x ((smallEtaleInverseImage f).obj F)
      ((smallEtaleBaseChange f).obj V) a)
    (globalSectionGerm_eq (x ≫ f) F V
      ((smallEtaleBaseChangeFiberIso f x).hom.app V a))
    (globalSectionsComparison_ΓRes f F V) (smallEtalePullbackStalkIso_germ f x F V a)

private lemma mem_globalSectionsEqOpen_pullback_iff
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : (Sheaf.Γ _ _).obj F) :
    x default ∈ globalSectionsEqOpen ((smallEtaleInverseImage f).obj F)
      ((globalSectionsSmallEtaleInverseImage f).app F s)
      ((globalSectionsSmallEtaleInverseImage f).app F t) ↔
        (x ≫ f) default ∈ globalSectionsEqOpen F s t := by
  rw [mem_globalSectionsEqOpen_iff, mem_globalSectionsEqOpen_iff]
  have hs := ConcreteCategory.congr_hom (globalSectionGerm_pullback f x F) s
  have ht := ConcreteCategory.congr_hom (globalSectionGerm_pullback f x F) t
  refine ⟨fun h ↦ hs.symm.trans
    ((congrArg ((smallEtalePullbackStalkIso f x).hom.app F) h).trans ht), fun h ↦ ?_⟩
  apply (smallEtalePullbackStalkIso f x).app F |>.toEquiv.injective
  exact hs.trans (h.trans ht.symm)

private def geometricPointAt {S : Scheme.{u}} (s : S) :
    Spec (.of (SeparableClosure (S.residueField s))) ⟶ S :=
  (S.SpecToEquivOfField (SeparableClosure (S.residueField s))).symm
    ⟨s, CommRingCat.ofHom (algebraMap (S.residueField s) _)⟩

private lemma geometricPointAt_apply {S : Scheme.{u}} (s : S) :
    geometricPointAt s default = s := by
  simp [geometricPointAt, Scheme.SpecToEquivOfField]

private def pointSmallEtaleIdentityInitial
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    IsInitial (show (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.Elements from
      Functor.elementsMk _ (smallEtaleFinal (Spec (.of Ω))) (CategoryTheory.Over.homMk (𝟙 _) (by
        change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
        simp))) := by
  apply IsInitial.ofUniqueHom
    (fun U : (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber.Elements ↦
      Functor.Elements.homMk
      (MorphismProperty.Over.homMk U.val.left (CategoryTheory.Over.w U.val)) ?_)
    (fun U morphism ↦ ?_)
  · apply Over.OverMorphism.ext
    change (𝟙 _) ≫ U.val.left = U.val.left
    exact Category.id_comp _
  · apply Functor.Elements.hom_ext
    apply MorphismProperty.Over.Hom.ext
    have h : 𝟙 _ ≫ morphism.hom.left = U.val.left :=
      congrArg (fun b ↦ b.left) morphism.map_val
    exact (Category.id_comp morphism.hom.left).symm.trans h

/-- If the final object with its point is initial among the elements of the fibre functor, the
germ of a global section is bijective. -/
private lemma globalSectionGerm_bijective_of_isInitial {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (h : IsInitial (show (pointSmallEtale x).fiber.Elements from
      Functor.elementsMk _ (smallEtaleFinal S) (smallEtaleFinalPoint x))) :
    Function.Bijective (globalSectionGerm x F) := by
  have := globalSections_res_final_isIso F
  have : IsIso ((pointSmallEtale x).toPresheafFiber (smallEtaleFinal S)
      (smallEtaleFinalPoint x) F.obj) :=
    ((pointSmallEtale x).isColimitPresheafFiberCocone F.obj).isIso_ι_app_of_isTerminal
      (Opposite.op (Functor.elementsMk _ (smallEtaleFinal S) (smallEtaleFinalPoint x))) h.op
  exact (isIso_iff_bijective _).mp (inferInstanceAs (IsIso (F.ΓRes _ ≫
    (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) (smallEtaleFinalPoint x) F.obj)))

private lemma globalSectionGerm_identity_bijective
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology (Type (max (u + 1) v))) :
    Function.Bijective (globalSectionGerm (𝟙 (Spec (.of Ω))) F) :=
  globalSectionGerm_bijective_of_isInitial _ F (pointSmallEtaleIdentityInitial Ω)

private lemma exists_etale_field_section
    (k : Type u) [Field k] [IsSepClosed k]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of k))
    (U : (Spec (.of k)).Etale) (a : (pointSmallEtale x).fiber.obj U) :
    ∃ b : Spec (.of k) ⟶ U.left, b ≫ U.hom = 𝟙 _ ∧ x ≫ b = a.left := by
  obtain ⟨b, hb, hy⟩ := exists_fac_of_etale_of_isSepClosed U.hom (𝟙 _)
    (a.left (default : Spec (.of Ω))) (by
      change U.hom (a.left (default : Spec (.of Ω))) = (default : Spec (.of k))
      exact Subsingleton.elim (α := Spec (.of k)) _ _)
  have : IsOpenImmersion b := AlgebraicGeometry.Unramified.section_isOpenImmersion U.hom b hb
  have hrange : Set.range a.left ⊆ Set.range b := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(default : Spec (.of k)), ?_⟩
    change b (default : Spec (.of k)) = a.left z
    have hz : z = (default : Spec (.of Ω)) :=
      Subsingleton.elim (α := Spec (.of Ω)) _ _
    exact hz ▸ hy
  let lift := IsOpenImmersion.lift b a.left hrange
  have hlift : lift = x := by
    have h := congrArg (· ≫ U.hom) (IsOpenImmersion.lift_fac b a.left hrange)
    have ha : a.left ≫ U.hom = x := CategoryTheory.Over.w a
    simpa only [Category.assoc, hb, Category.comp_id] using h.trans ha
  exact ⟨b, hb, (congrArg (· ≫ b) hlift).symm.trans (IsOpenImmersion.lift_fac b a.left hrange)⟩

private def pointSmallEtaleFieldInitial
    (k : Type u) [Field k] [IsSepClosed k]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of k)) :
    IsInitial (show (pointSmallEtale x).fiber.Elements from
      Functor.elementsMk _ (smallEtaleFinal (Spec (.of k))) (CategoryTheory.Over.homMk x (by
        change x ≫ 𝟙 _ = x
        simp))) := by
  classical
  let sectionOf (U : (pointSmallEtale x).fiber.Elements) :=
    (exists_etale_field_section k x U.obj U.val).choose
  have hsection (U : (pointSmallEtale x).fiber.Elements) :
      sectionOf U ≫ U.obj.hom = 𝟙 _ ∧ x ≫ sectionOf U = U.val.left :=
    (exists_etale_field_section k x U.obj U.val).choose_spec
  apply IsInitial.ofUniqueHom
    (fun U : (pointSmallEtale x).fiber.Elements ↦ Functor.Elements.homMk
      (MorphismProperty.Over.homMk (sectionOf U) (hsection U).1) (by
        apply Over.OverMorphism.ext
        exact (hsection U).2))
    (fun U morphism ↦ ?_)
  apply Functor.Elements.hom_ext
  apply MorphismProperty.Over.Hom.ext
  have : IsOpenImmersion (sectionOf U) :=
    AlgebraicGeometry.Unramified.section_isOpenImmersion U.obj.hom (sectionOf U) (hsection U).1
  have hpoint := congrArg (fun a ↦ a.left (default : Spec (.of Ω))) morphism.map_val
  change (x ≫ morphism.hom.left) (default : Spec (.of Ω)) =
    U.val.left (default : Spec (.of Ω)) at hpoint
  have hrange : Set.range morphism.hom.left ⊆ Set.range (sectionOf U) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨(default : Spec (.of k)), ?_⟩
    have hx : x (default : Spec (.of Ω)) = (default : Spec (.of k)) :=
      Subsingleton.elim _ _
    have hpoint' : morphism.hom.left (default : Spec (.of k)) =
        U.val.left (default : Spec (.of Ω)) :=
      (congrArg (fun p ↦ morphism.hom.left p) hx).symm.trans
        ((Scheme.Hom.comp_apply x morphism.hom.left
          (default : Spec (.of Ω))).symm.trans hpoint)
    have hsectionPoint := congrArg (fun a ↦ a (default : Spec (.of Ω))) (hsection U).2
    change sectionOf U (default : Spec (.of k)) = morphism.hom.left z
    have hz : z = (default : Spec (.of k)) :=
      Subsingleton.elim (α := Spec (.of k)) _ _
    rw [hz]
    simpa only [Scheme.Hom.comp_apply, hx] using hsectionPoint.trans hpoint'.symm
  let lift := IsOpenImmersion.lift (sectionOf U) morphism.hom.left hrange
  have hlift : lift = 𝟙 (Spec (.of k)) := by
    have h := congrArg (· ≫ U.obj.hom)
      (IsOpenImmersion.lift_fac (sectionOf U) morphism.hom.left hrange)
    have hm : morphism.hom.left ≫ U.obj.hom = 𝟙 (Spec (.of k)) :=
      MorphismProperty.Over.w morphism.hom
    have h' := h.trans hm
    exact (Category.comp_id lift).symm.trans
      ((congrArg (lift ≫ ·) (hsection U).1).symm.trans
        ((Category.assoc lift (sectionOf U) U.obj.hom).symm.trans h'))
  change morphism.hom.left = sectionOf U
  exact (IsOpenImmersion.lift_fac (sectionOf U) morphism.hom.left hrange).symm.trans
    ((congrArg (· ≫ sectionOf U) hlift).trans (Category.id_comp (sectionOf U)))

private lemma sieve_mem_smallEtaleTopology_of_geometricPoints
    {S : Scheme.{u}} (U : S.Etale) (R : Sieve U)
    (hR : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ S) (a : (pointSmallEtale x).fiber.obj U),
      ∃ (V : S.Etale) (morphism : V ⟶ U), R morphism ∧
        ∃ b : (pointSmallEtale x).fiber.obj V,
          (pointSmallEtale x).fiber.map morphism b = a) :
    R ∈ S.smallEtaleTopology U := by
  obtain ⟨index, objects, maps, rfl⟩ := R.exists_eq_ofArrows
  rw [ofArrows_mem_smallEtaleTopology_iff]
  apply Set.eq_univ_of_forall
  intro y
  let x := geometricPointAt y ≫ U.hom
  let a : (pointSmallEtale x).fiber.obj U := Over.homMk (geometricPointAt y) rfl
  obtain ⟨V, morphism, hmorphism, b, hb⟩ := hR _ x a
  obtain ⟨i, factor, rfl⟩ := Sieve.ofArrows.exists hmorphism
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  refine ⟨factor.left (b.left (default : Spec (.of (SeparableClosure
    (U.left.residueField y))))), ?_⟩
  have h : (b.left ≫ factor.left ≫ (maps i).left)
      (default : Spec (.of (SeparableClosure (U.left.residueField y)))) =
      geometricPointAt y default :=
    congrArg (fun m ↦ m.left
      (default : Spec (.of (SeparableClosure (U.left.residueField y))))) hb
  have h1 : (factor.left ≫ (maps i).left)
      (b.left (default : Spec (.of (SeparableClosure (U.left.residueField y))))) =
      geometricPointAt y default :=
    (Scheme.Hom.comp_apply b.left (factor.left ≫ (maps i).left) _).symm.trans h
  have h2 : (maps i).left (factor.left
      (b.left (default : Spec (.of (SeparableClosure (U.left.residueField y)))))) =
      geometricPointAt y default :=
    (Scheme.Hom.comp_apply factor.left (maps i).left _).symm.trans h1
  exact h2.trans (geometricPointAt_apply y)

private lemma smallEtaleSheaf_isLocallySurjective_of_stalk_surjective
    {S : Scheme.{u}}
    {F G : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))} (morphism : F ⟶ G)
    (hsurj : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ S),
      Function.Surjective ((pointSmallEtale x).sheafFiber.map morphism)) :
    Sheaf.IsLocallySurjective morphism := by
  constructor
  intro U s
  apply sieve_mem_smallEtaleTopology_of_geometricPoints U _
  intro Ω _ _ x a
  let Φ := pointSmallEtale x
  obtain ⟨t, ht⟩ := hsurj Ω x (Φ.toPresheafFiber U a G.obj s)
  change Φ.presheafFiber.obj F.obj at t
  change Φ.presheafFiber.map morphism.hom t = _ at ht
  obtain ⟨V, b, t, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) t
  let W := IsCofiltered.min (Φ.fiber.elementsMk U a) (Φ.fiber.elementsMk V b)
  let leftMap := IsCofiltered.minToLeft (Φ.fiber.elementsMk U a) (Φ.fiber.elementsMk V b)
  let rightMap := IsCofiltered.minToRight (Φ.fiber.elementsMk U a) (Φ.fiber.elementsMk V b)
  have heq : Φ.toPresheafFiber W.obj W.val G.obj
      (morphism.hom.app (Opposite.op W.obj) (F.obj.map rightMap.hom.op t)) =
      Φ.toPresheafFiber W.obj W.val G.obj (G.obj.map leftMap.hom.op s) := by
    rw [← GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
      GrothendieckTopology.Point.toPresheafFiber_w_apply,
      GrothendieckTopology.Point.toPresheafFiber_w_apply,
      leftMap.map_val, rightMap.map_val]
    exact ht
  obtain ⟨Z, restriction, c, hc, heq⟩ :=
    (Φ.toPresheafFiber_eq_iff' W.obj W.val _ _).mp heq
  refine ⟨Z, restriction ≫ leftMap.hom, ?_, c, ?_⟩
  · refine ⟨F.obj.map restriction.op (F.obj.map rightMap.hom.op t), ?_⟩
    have hnat := ConcreteCategory.congr_hom (morphism.hom.naturality restriction.op)
      (F.obj.map rightMap.hom.op t)
    change morphism.hom.app (Opposite.op Z) (F.obj.map restriction.op
      (F.obj.map rightMap.hom.op t)) = G.obj.map restriction.op
        (morphism.hom.app (Opposite.op W.obj) (F.obj.map rightMap.hom.op t)) at hnat
    exact (hnat.trans heq).trans
      (ConcreteCategory.congr_hom (G.obj.map_comp leftMap.hom.op restriction.op) s).symm
  · rw [Functor.map_comp, types_comp_apply, hc]
    exact leftMap.map_val

private lemma smallEtaleSheaf_isLocallyInjective_of_stalk_injective
    {S : Scheme.{u}}
    {F G : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))} (morphism : F ⟶ G)
    (hinj : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ S),
      Function.Injective ((pointSmallEtale x).sheafFiber.map morphism)) :
    Sheaf.IsLocallyInjective morphism := by
  constructor
  intro U s t hst
  apply sieve_mem_smallEtaleTopology_of_geometricPoints U.unop _
  intro Ω _ _ x a
  have heq : (pointSmallEtale x).toPresheafFiber U.unop a F.obj s =
      (pointSmallEtale x).toPresheafFiber U.unop a F.obj t := by
    apply hinj Ω x
    change (pointSmallEtale x).presheafFiber.map morphism.hom _ =
      (pointSmallEtale x).presheafFiber.map morphism.hom _
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply,
      GrothendieckTopology.Point.toPresheafFiber_naturality_apply, hst]
  obtain ⟨V, restriction, b, hb, heq⟩ :=
    ((pointSmallEtale x).toPresheafFiber_eq_iff' U.unop a s t).mp heq
  exact ⟨V, restriction, heq, b, hb⟩

private lemma smallEtaleSheaf_isIso_of_stalk_bijective
    {S : Scheme.{u}}
    {F G : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))} (morphism : F ⟶ G)
    (hbij : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ S),
      Function.Bijective ((pointSmallEtale x).sheafFiber.map morphism)) :
    IsIso morphism :=
  (Sheaf.isLocallyBijective_iff_isIso morphism).mp
    ⟨smallEtaleSheaf_isLocallyInjective_of_stalk_injective morphism
        (fun Ω _ _ x ↦ (hbij Ω x).injective),
      smallEtaleSheaf_isLocallySurjective_of_stalk_surjective morphism
        (fun Ω _ _ x ↦ (hbij Ω x).surjective)⟩

private lemma globalSectionGerm_field_bijective
    (k : Type u) [Field k] [IsSepClosed k]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of k))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (Type (max (u + 1) v))) :
    Function.Bijective (globalSectionGerm x F) :=
  globalSectionGerm_bijective_of_isInitial x F (pointSmallEtaleFieldInitial k x)

private def constantSheafCounit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    (constantSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj
      ((Sheaf.Γ _ _).obj F) ⟶ F :=
  { hom := sheafifyLift S.smallEtaleTopology F.coneΓ.π F.property }

private lemma constantSheafCounit_ΓRes {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale) :
    (toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj
      ((Sheaf.Γ _ _).obj F))).app (Opposite.op U) ≫
        (constantSheafCounit F).hom.app (Opposite.op U) = F.ΓRes (Opposite.op U) :=
  NatTrans.congr_app (toSheafify_sheafifyLift S.smallEtaleTopology F.coneΓ.π
    F.property) (Opposite.op U)

private lemma globalSectionsComparison_injective
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : Function.Surjective f)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Function.Injective ((globalSectionsSmallEtaleInverseImage f).app F) := by
  intro s t hst
  apply (globalSectionsEqOpen_eq_top_iff F s t).mp
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx := (mem_globalSectionsEqOpen_pullback_iff f (geometricPointAt x) F s t).mp
    (show geometricPointAt x default ∈ globalSectionsEqOpen
      ((smallEtaleInverseImage f).obj F)
      ((globalSectionsSmallEtaleInverseImage f).app F s)
      ((globalSectionsSmallEtaleInverseImage f).app F t) from by
        rw [(globalSectionsEqOpen_eq_top_iff _ _ _).mpr hst]
        trivial)
  simpa [Scheme.Hom.comp_apply, geometricPointAt_apply] using hx

private lemma constantPresheaf_germ_bijective
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [LocallySmall.{u} C] (Φ : J.Point.{u})
    (M : Type (max (u + 1) v)) (W : C) (a : Φ.fiber.obj W) :
    Function.Bijective (Φ.toPresheafFiber W a ((Functor.const Cᵒᵖ).obj M)) := by
  let P := (Functor.const Cᵒᵖ).obj M
  let e := (Φ.isColimitPresheafFiberCocone P).coconePointUniqueUpToIso
    (isColimitConstCocone Φ.fiber.Elementsᵒᵖ M)
  have he : Φ.toPresheafFiber W a P ≫ e.hom = 𝟙 M :=
    (Φ.isColimitPresheafFiberCocone P).comp_coconePointUniqueUpToIso_hom
      (isColimitConstCocone Φ.fiber.Elementsᵒᵖ M) (Opposite.op (Φ.fiber.elementsMk W a))
  have he' : Φ.toPresheafFiber W a P = e.inv :=
    (cancel_mono e.hom).mp (he.trans e.inv_hom_id.symm)
  rw [he']
  exact e.symm.toEquiv.bijective

private lemma constantSheaf_germ_bijective
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [LocallySmall.{u} C] (Φ : J.Point.{u})
    [HasSheafify J (Type (max (u + 1) v))]
    (M : Type (max (u + 1) v)) (W : C) (a : Φ.fiber.obj W) :
    Function.Bijective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app
      (Opposite.op W) ≫
        Φ.toPresheafFiber W a ((constantSheaf J (Type (max (u + 1) v))).obj M).obj) := by
  change Function.Bijective ((toSheafify J ((Functor.const Cᵒᵖ).obj M)).app
    (Opposite.op W) ≫ Φ.toPresheafFiber W a (sheafify J _))
  rw [← Φ.toPresheafFiber_naturality]
  change Function.Bijective ((Φ.presheafFiber.map
    (toSheafify J ((Functor.const Cᵒᵖ).obj M))) ∘
      (Φ.toPresheafFiber W a ((Functor.const Cᵒᵖ).obj M)))
  exact ((asIso (Φ.presheafFiber.map
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)))).toEquiv.bijective).comp
    (constantPresheaf_germ_bijective Φ M W a)

private def constantGlobalSection (S : Scheme.{u})
    (M : Type (max (u + 1) v)) :
    M ⟶ (Sheaf.Γ _ _).obj ((constantSheaf S.smallEtaleTopology
      (Type (max (u + 1) v))).obj M) :=
  Sheaf.ΓHomEquiv (toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M))

private lemma constantGlobalSection_ΓRes (S : Scheme.{u})
    (M : Type (max (u + 1) v)) (U : S.Etale) :
    constantGlobalSection S M ≫
      ((constantSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj M).ΓRes
        (Opposite.op U) =
      (toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M)).app
        (Opposite.op U) :=
  ((constantSheaf S.smallEtaleTopology
    (Type (max (u + 1) v))).obj M).isLimitConeΓ.fac
      ⟨M, toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M)⟩
        (Opposite.op U)

private lemma constantGlobalSection_germ_bijective {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (M : Type (max (u + 1) v)) :
    Function.Bijective (constantGlobalSection S M ≫
      globalSectionGerm x ((constantSheaf S.smallEtaleTopology
        (Type (max (u + 1) v))).obj M)) := by
  have hbase := constantGlobalSection_ΓRes S M (smallEtaleFinal S)
  have hb := constantSheaf_germ_bijective.{u, v} (pointSmallEtale x) M (smallEtaleFinal S)
    (smallEtaleFinalPoint x)
  have hpt : ∀ m, (constantGlobalSection S M ≫
      globalSectionGerm x ((constantSheaf S.smallEtaleTopology
        (Type (max (u + 1) v))).obj M)) m =
      ((toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj M)).app
          (Opposite.op (smallEtaleFinal S)) ≫
        (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) (smallEtaleFinalPoint x)
          ((constantSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj M).obj) m := by
    intro m
    exact congrArg (ConcreteCategory.hom
      ((pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) (smallEtaleFinalPoint x)
        ((constantSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj M).obj))
      (ConcreteCategory.congr_hom hbase m)
  refine ⟨fun m₁ m₂ h ↦ hb.1 (((hpt m₁).symm.trans h).trans (hpt m₂)), fun y ↦ ?_⟩
  obtain ⟨m, hm⟩ := hb.2 y
  exact ⟨m, (hpt m).trans hm⟩

private lemma constantSheafCounit_germ {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    (constantGlobalSection S ((Sheaf.Γ _ _).obj F) ≫
      globalSectionGerm x ((constantSheaf S.smallEtaleTopology
        (Type (max (u + 1) v))).obj ((Sheaf.Γ _ _).obj F))) ≫
      (pointSmallEtale x).sheafFiber.map (constantSheafCounit F) =
        globalSectionGerm x F := by
  have key : (constantGlobalSection S ((Sheaf.Γ _ _).obj F) ≫
        (((constantSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj
              ((Sheaf.Γ _ _).obj F)).ΓRes (Opposite.op (smallEtaleFinal S)) ≫
          (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) (smallEtaleFinalPoint x)
            ((constantSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj
              ((Sheaf.Γ _ _).obj F)).obj)) ≫
      (pointSmallEtale x).presheafFiber.map (constantSheafCounit F).hom =
      F.ΓRes (Opposite.op (smallEtaleFinal S)) ≫
        (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S)
          (smallEtaleFinalPoint x) F.obj := by
    rw [← Category.assoc, Category.assoc,
      (pointSmallEtale x).toPresheafFiber_naturality (constantSheafCounit F).hom
        (smallEtaleFinal S) (smallEtaleFinalPoint x)]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ (z ≫ (constantSheafCounit F).hom.app
              (Opposite.op (smallEtaleFinal S))) ≫
            (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S)
              (smallEtaleFinalPoint x) F.obj)
          (constantGlobalSection_ΓRes S ((Sheaf.Γ _ _).obj F) (smallEtaleFinal S))).trans
        (congrArg (· ≫ (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S)
            (smallEtaleFinalPoint x) F.obj)
          (constantSheafCounit_ΓRes F (smallEtaleFinal S))))
  exact key

private lemma constantSheafCounit_isIso_over_sepClosedField
    (k : Type u) [Field k] [IsSepClosed k]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (Type (max (u + 1) v))) :
    IsIso (constantSheafCounit F) := by
  apply smallEtaleSheaf_isIso_of_stalk_bijective
  intro Ω _ _ x
  apply (Function.Bijective.of_comp_iff _
    (constantGlobalSection_germ_bijective x ((Sheaf.Γ _ _).obj F))).mp
  change Function.Bijective ((constantGlobalSection (Spec (.of k))
    ((Sheaf.Γ _ _).obj F) ≫ globalSectionGerm x
      ((constantSheaf (Spec (.of k)).smallEtaleTopology
        (Type (max (u + 1) v))).obj ((Sheaf.Γ _ _).obj F))) ≫
      (pointSmallEtale x).sheafFiber.map (constantSheafCounit F))
  rw [constantSheafCounit_germ]
  exact globalSectionGerm_field_bijective k x F

private def smallEtaleInverseImageCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleInverseImage.{u, v} g ⋙
      smallEtaleInverseImage f ≅
        smallEtaleInverseImage (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (smallEtaleInverseImageAdjunction g)
    (smallEtaleInverseImageAdjunction f)
    (smallEtaleInverseImageAdjunction (f ≫ g))
    (smallEtalePushforwardCompIso f g)

private def smallEtaleConstantPullbackIso
    {X S : Scheme.{u}} (f : X ⟶ S) :
    constantSheaf S.smallEtaleTopology (Type (max (u + 1) v)) ⋙
      smallEtaleInverseImage f ≅
        constantSheaf X.smallEtaleTopology (Type (max (u + 1) v)) := by
  let A := Type (max (u + 1) v)
  let P := (smallEtaleBaseChange f).sheafPushforwardContinuous
    A S.smallEtaleTopology X.smallEtaleTopology
  let e : P ⋙ Sheaf.Γ S.smallEtaleTopology A ≅ Sheaf.Γ X.smallEtaleTopology A :=
    NatIso.ofComponents (fun F ↦
      (P.obj F).isLimitConeΓ.conePointUniqueUpToIso
        (smallEtaleBaseChangeGlobalSectionsIsLimit f F)) (by
          intro F G morphism
          apply (smallEtaleBaseChangeGlobalSectionsIsLimit f G).hom_ext
          intro U
          let eF := (P.obj F).isLimitConeΓ.conePointUniqueUpToIso
            (smallEtaleBaseChangeGlobalSectionsIsLimit f F)
          let eG := (P.obj G).isLimitConeΓ.conePointUniqueUpToIso
            (smallEtaleBaseChangeGlobalSectionsIsLimit f G)
          let V := Opposite.op ((smallEtaleBaseChange f).obj U.unop)
          have hF : eF.hom ≫ F.ΓRes V = (P.obj F).ΓRes U :=
            (P.obj F).isLimitConeΓ.conePointUniqueUpToIso_hom_comp
              (smallEtaleBaseChangeGlobalSectionsIsLimit f F) U
          have hG : eG.hom ≫ G.ΓRes V = (P.obj G).ΓRes U :=
            (P.obj G).isLimitConeΓ.conePointUniqueUpToIso_hom_comp
              (smallEtaleBaseChangeGlobalSectionsIsLimit f G) U
          change ((Sheaf.Γ S.smallEtaleTopology A).map (P.map morphism) ≫ eG.hom) ≫
            G.ΓRes V = (eF.hom ≫ (Sheaf.Γ X.smallEtaleTopology A).map morphism) ≫
              G.ΓRes V
          exact (Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) hG).trans
              ((Sheaf.ΓRes_naturality (P.map morphism) U).trans
                ((congrArg (· ≫ morphism.hom.app V) hF).symm.trans
                  ((Category.assoc _ _ _).trans
                    ((congrArg (eF.hom ≫ ·) (Sheaf.ΓRes_naturality morphism V).symm).trans
                      (Category.assoc _ _ _).symm))))))
  exact Adjunction.leftAdjointCompIso
    (constantSheafΓAdj S.smallEtaleTopology A)
    (smallEtaleInverseImageAdjunction f)
    (constantSheafΓAdj X.smallEtaleTopology A) e

private lemma globalSectionsEqOpen_constant_disjoint {S : Scheme.{u}}
    (M : Type (max (u + 1) v))
    (s : (Sheaf.Γ _ _).obj ((constantSheaf S.smallEtaleTopology
      (Type (max (u + 1) v))).obj M)) (a b : M) (hab : a ≠ b) :
    Disjoint (globalSectionsEqOpen _ s (constantGlobalSection S M a))
      (globalSectionsEqOpen _ s (constantGlobalSection S M b)) := by
  rw [disjoint_iff_inf_le]
  intro y hy
  have ha := (mem_globalSectionsEqOpen_iff (geometricPointAt y) _ _ _).mp
    (by simpa [geometricPointAt_apply] using hy.1)
  have hb := (mem_globalSectionsEqOpen_iff (geometricPointAt y) _ _ _).mp
    (by simpa [geometricPointAt_apply] using hy.2)
  exact hab ((constantGlobalSection_germ_bijective (geometricPointAt y) M).injective
    (ha.symm.trans hb))

private lemma globalSectionsEqOpen_constant_cover {S : Scheme.{u}}
    (M : Type (max (u + 1) v))
    (s : (Sheaf.Γ _ _).obj ((constantSheaf S.smallEtaleTopology
      (Type (max (u + 1) v))).obj M)) :
    (⨆ a : M, globalSectionsEqOpen _ s (constantGlobalSection S M a)) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨a, ha⟩ := (constantGlobalSection_germ_bijective (geometricPointAt y) M).surjective
    (globalSectionGerm (geometricPointAt y) _ s)
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨a, ?_⟩
  have := (mem_globalSectionsEqOpen_iff (geometricPointAt y) _ _ _).mpr ha.symm
  change (geometricPointAt y) default ∈ globalSectionsEqOpen _ s
    (constantGlobalSection S M a) at this
  rwa [geometricPointAt_apply] at this

private lemma globalSectionsEqOpen_constant_isClopen {S : Scheme.{u}}
    (M : Type (max (u + 1) v))
    (s : (Sheaf.Γ _ _).obj ((constantSheaf S.smallEtaleTopology
      (Type (max (u + 1) v))).obj M)) (a : M) :
    IsClopen (globalSectionsEqOpen _ s (constantGlobalSection S M a) : Set S) := by
  classical
  let other : S.Opens := ⨆ b : {b : M // b ≠ a},
    globalSectionsEqOpen _ s (constantGlobalSection S M b.1)
  apply isClopen_of_disjoint_cover_open (b := (other : Set S))
  · intro y _
    have hy : y ∈ (⨆ b : M, globalSectionsEqOpen _ s
        (constantGlobalSection S M b)) := by
      rw [globalSectionsEqOpen_constant_cover]
      trivial
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    by_cases hba : b = a
    · exact Or.inl (hba ▸ hb)
    · exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hba⟩, hb⟩)
  · exact (globalSectionsEqOpen _ s (constantGlobalSection S M a)).isOpen
  · exact other.isOpen
  · rw [Set.disjoint_left]
    intro y ha hb
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hb
    exact disjoint_iff_inf_le.mp (globalSectionsEqOpen_constant_disjoint M s a b.1 (Ne.symm b.2))
      ⟨ha, hb⟩

private lemma constantGlobalSection_bijective_of_connectedSpace
    (S : Scheme.{u}) [ConnectedSpace S] (M : Type (max (u + 1) v)) :
    Function.Bijective (constantGlobalSection S M) := by
  let y : S := Classical.choice inferInstance
  constructor
  · exact fun a b hab ↦ (constantGlobalSection_germ_bijective (geometricPointAt y) M).injective
      (congrArg (globalSectionGerm (geometricPointAt y) _) hab)
  · intro s
    obtain ⟨a, ha⟩ := (constantGlobalSection_germ_bijective (geometricPointAt y) M).surjective
      (globalSectionGerm (geometricPointAt y) _ s)
    refine ⟨a, ((globalSectionsEqOpen_eq_top_iff _ _ _).mp ?_).symm⟩
    apply TopologicalSpace.Opens.ext
    exact (globalSectionsEqOpen_constant_isClopen M s a).eq_univ ⟨y, by
      have hy := (mem_globalSectionsEqOpen_iff (geometricPointAt y) _ s
        (constantGlobalSection S M a)).mpr ha.symm
      simpa [geometricPointAt_apply] using hy⟩

private lemma globalSectionGerm_naturality {S : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    {F G : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))} (morphism : F ⟶ G) :
    (Sheaf.Γ _ _).map morphism ≫ globalSectionGerm x G =
      globalSectionGerm x F ≫ (pointSmallEtale x).sheafFiber.map morphism := by
  have key : (Sheaf.Γ _ _).map morphism ≫
      (G.ΓRes (Opposite.op (smallEtaleFinal S)) ≫
        (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S) (smallEtaleFinalPoint x) G.obj) =
      (F.ΓRes (Opposite.op (smallEtaleFinal S)) ≫
          (pointSmallEtale x).toPresheafFiber (smallEtaleFinal S)
            (smallEtaleFinalPoint x) F.obj) ≫
        (pointSmallEtale x).presheafFiber.map morphism.hom := by
    rw [← Category.assoc, Sheaf.ΓRes_naturality, Category.assoc, Category.assoc,
      (pointSmallEtale x).toPresheafFiber_naturality morphism.hom (smallEtaleFinal S)
        (smallEtaleFinalPoint x)]
  exact key

private lemma globalSectionGerm_constant_bijective
    {S : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (M : Type (max (u + 1) v)) :
    Function.Bijective (globalSectionGerm x
      ((constantSheaf S.smallEtaleTopology (Type (max (u + 1) v))).obj M)) :=
  (Function.Bijective.of_comp_iff _
    (constantGlobalSection_bijective_of_connectedSpace S M)).mp
      (constantGlobalSection_germ_bijective x M)

private lemma globalSectionGerm_bijective_of_isConstant
    {S : Scheme.{u}} [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    [Sheaf.IsConstant S.smallEtaleTopology F] :
    Function.Bijective (globalSectionGerm x F) := by
  obtain ⟨M, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant S.smallEtaleTopology F
  apply (Function.Bijective.of_comp_iff _
    ((Sheaf.Γ _ _).mapIso e).toEquiv.bijective).mp
  change Function.Bijective ((Sheaf.Γ _ _).map e.hom ≫ globalSectionGerm x F)
  rw [globalSectionGerm_naturality]
  exact (((pointSmallEtale x).sheafFiber.mapIso e).toEquiv.bijective).comp
    (globalSectionGerm_constant_bijective x M)

private def smallEtalePullbackFieldConstantIso
    {X : Scheme.{u}} (k : Type u) [Field k] [IsSepClosed k]
    (f : X ⟶ Spec (.of k))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (Type (max (u + 1) v))) :
    (constantSheaf X.smallEtaleTopology (Type (max (u + 1) v))).obj
      ((Sheaf.Γ _ _).obj F) ≅ (smallEtaleInverseImage f).obj F := by
  have := constantSheafCounit_isIso_over_sepClosedField k F
  exact ((smallEtaleConstantPullbackIso f).app ((Sheaf.Γ _ _).obj F)).symm ≪≫
    (smallEtaleInverseImage f).mapIso (asIso (constantSheafCounit F))

private lemma globalSectionsEqOpen_eq_top_of_isConstant_of_nonempty
    {S : Scheme.{u}} [ConnectedSpace S]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    [Sheaf.IsConstant S.smallEtaleTopology F]
    (s t : (Sheaf.Γ _ _).obj F) (hne : (globalSectionsEqOpen F s t : Set S).Nonempty) :
    globalSectionsEqOpen F s t = ⊤ := by
  obtain ⟨y, hy⟩ := hne
  apply (globalSectionsEqOpen_eq_top_iff F s t).mpr
  apply (globalSectionGerm_bijective_of_isConstant (geometricPointAt y) F).injective
  exact (mem_globalSectionsEqOpen_iff (geometricPointAt y) F s t).mp
    (by simpa [geometricPointAt_apply] using hy)

private lemma smallEtaleInverseImage_isConstant_over_geometricFiber
    {X S Y : Scheme.{u}} (f : X ⟶ S)
    (k : Type u) [Field k] [IsSepClosed k] (g : Spec (.of k) ⟶ S)
    (i : Y ⟶ X) (q : Y ⟶ Spec (.of k)) (h : i ≫ f = q ≫ g)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Sheaf.IsConstant Y.smallEtaleTopology
      ((smallEtaleInverseImage i).obj
        ((smallEtaleInverseImage f).obj F)) := by
  let e := (smallEtaleInverseImageCompIso i f).app F ≪≫
    eqToIso (congrArg (fun p : Y ⟶ S ↦
      (smallEtaleInverseImage.{u, v} p).obj F) h) ≪≫
    ((smallEtaleInverseImageCompIso q g).app F).symm ≪≫
    (smallEtalePullbackFieldConstantIso k q
      ((smallEtaleInverseImage g).obj F)).symm
  exact Sheaf.isConstant_of_iso Y.smallEtaleTopology e

private lemma globalSectionsEqOpen_pullback
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : (Sheaf.Γ _ _).obj F) :
    (globalSectionsEqOpen ((smallEtaleInverseImage f).obj F)
      ((globalSectionsSmallEtaleInverseImage f).app F s)
      ((globalSectionsSmallEtaleInverseImage f).app F t) : Set X) =
        f ⁻¹' (globalSectionsEqOpen F s t : Set S) := by
  ext x
  simpa [Scheme.Hom.comp_apply, geometricPointAt_apply] using
    mem_globalSectionsEqOpen_pullback_iff f (geometricPointAt x) F s t

private lemma globalSectionsEqOpen_inverseImage_saturated
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyConnected f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : (Sheaf.Γ _ _).obj ((smallEtaleInverseImage f).obj F)) :
    f ⁻¹' (f '' (globalSectionsEqOpen _ s t : Set X)) =
      (globalSectionsEqOpen _ s t : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    let g := geometricPointAt (f x)
    let i := pullback.fst f g
    let q := pullback.snd f g
    let H := (smallEtaleInverseImage f).obj F
    let H' := (smallEtaleInverseImage i).obj H
    let s' := (globalSectionsSmallEtaleInverseImage i).app H s
    let t' := (globalSectionsSmallEtaleInverseImage i).app H t
    have : ConnectedSpace (pullback f g : Scheme.{u}) :=
      pullback_of_geometrically
        (GeometricallyConnected.geometrically_connectedSpace (f := f)) _ g
    have : Sheaf.IsConstant (pullback f g : Scheme.{u}).smallEtaleTopology H' :=
      smallEtaleInverseImage_isConstant_over_geometricFiber f _ g i q
        pullback.condition F
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := g) y (default : Spec (.of (SeparableClosure
        (S.residueField (f x))))) (by
          simpa only [g, geometricPointAt_apply] using hxy)
    have hne : (globalSectionsEqOpen H' s' t' : Set (pullback f g : Scheme.{u})).Nonempty := by
      refine ⟨z, ?_⟩
      rw [globalSectionsEqOpen_pullback]
      change (pullback.fst f g) z ∈ (globalSectionsEqOpen H s t : Set X)
      rwa [hz]
    have heq := globalSectionsEqOpen_eq_top_of_isConstant_of_nonempty H' s' t' hne
    obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := g) x (default : Spec (.of (SeparableClosure
        (S.residueField (f x))))) (by simp only [g, geometricPointAt_apply])
    have hwmem : w ∈ (globalSectionsEqOpen H' s' t' : Set (pullback f g : Scheme.{u})) := by
      rw [heq]
      trivial
    rw [globalSectionsEqOpen_pullback] at hwmem
    change (pullback.fst f g) w ∈ (globalSectionsEqOpen H s t : Set X) at hwmem
    rwa [hw] at hwmem
  · exact fun hx ↦ ⟨x, hx, rfl⟩

private lemma globalSectionsEqOpen_inverseImage_descends
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hquot : Topology.IsQuotientMap f) [GeometricallyConnected f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (s t : (Sheaf.Γ _ _).obj ((smallEtaleInverseImage f).obj F)) :
    ∃ U : S.Opens, f ⁻¹' (U : Set S) = (globalSectionsEqOpen _ s t : Set X) := by
  obtain ⟨U, hU, heq⟩ := exists_open_factor_of_quotientMap f hquot
    (globalSectionsEqOpen _ s t).isOpen
    (globalSectionsEqOpen_inverseImage_saturated f F s t)
  exact ⟨⟨U, hU⟩, heq⟩

private lemma smallEtaleInverseImageSections_germ
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (b : (pointSmallEtale x).fiber.obj U) :
    smallEtaleInverseImageSections f F a ≫
      (pointSmallEtale x).toPresheafFiber U b
        ((smallEtaleInverseImage f).obj F).obj ≫
      (smallEtalePullbackStalkIso f x).hom.app F =
    (pointSmallEtale (x ≫ f)).toPresheafFiber V
      ((smallEtaleBaseChangeFiberIso f x).hom.app V
        ((pointSmallEtale x).fiber.map a b)) F.obj := by
  let unitMap := ((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
    (Opposite.op V)
  let stalkMap := (smallEtalePullbackStalkIso f x).hom.app F
  let germMap := (pointSmallEtale x).toPresheafFiber U b
    ((smallEtaleInverseImage f).obj F).obj
  let restriction := ((smallEtaleInverseImage f).obj F).obj.map a.op
  have hw := (pointSmallEtale x).toPresheafFiber_w a b
    ((smallEtaleInverseImage f).obj F).obj
  exact (Category.assoc unitMap restriction (germMap ≫ stalkMap)).trans
    ((congrArg (unitMap ≫ ·) ((Category.assoc restriction germMap stalkMap).symm.trans
      (congrArg (· ≫ stalkMap) hw))).trans
        (smallEtalePullbackStalkIso_germ f x F V _))

private lemma exists_smallEtaleInverseImage_germ_representative
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (t : (Sheaf.Γ _ _).obj ((smallEtaleInverseImage f).obj F)) :
    ∃ (V : S.Etale) (a : (pointSmallEtale (x ≫ f)).fiber.obj V)
      (s : F.obj.obj (Opposite.op V)),
      globalSectionGerm x ((smallEtaleInverseImage f).obj F) t =
        (pointSmallEtale x).toPresheafFiber
          ((smallEtaleBaseChange f).obj V)
          ((smallEtaleBaseChangeFiberIso f x).inv.app V a)
          ((smallEtaleInverseImage f).obj F).obj
          ((((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
            (Opposite.op V)) s) := by
  let H := (smallEtaleInverseImage f).obj F
  let e := smallEtalePullbackStalkIso f x
  obtain ⟨V, a, s, hs⟩ := (pointSmallEtale (x ≫ f)).toPresheafFiber_jointly_surjective
    (P := F.obj) (e.hom.app F (globalSectionGerm x H t))
  refine ⟨V, a, s, ?_⟩
  apply e.app F |>.toEquiv.injective
  have h := ConcreteCategory.congr_hom
    (smallEtalePullbackStalkIso_germ f x F V
      ((smallEtaleBaseChangeFiberIso f x).inv.app V a)) s
  have ha := ConcreteCategory.congr_hom
    ((smallEtaleBaseChangeFiberIso f x).inv_hom_id_app V) a
  change (smallEtaleBaseChangeFiberIso f x).hom.app V
    ((smallEtaleBaseChangeFiberIso f x).inv.app V a) = a at ha
  change _ = (pointSmallEtale (x ≫ f)).toPresheafFiber V _ F.obj s at h
  rw [ha] at h
  exact hs.symm.trans h.symm

/-- For an étale `f : X ⟶ S`, the inverse image on sheaves of sets is the direct image along
composition with `f`: both are left adjoint to the direct image along base change. -/
private def smallEtaleRestrictionIso
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] :
    smallEtaleInverseImage.{u, v} f ≅
      (Scheme.Etale.smallEtaleCompose f).sheafPushforwardContinuous (Type (max (u + 1) v))
        X.smallEtaleTopology S.smallEtaleTopology :=
  (smallEtaleInverseImageAdjunction f).leftAdjointUniq
    ((Scheme.Etale.smallEtaleComposeBaseChangeAdj f).sheafPushforwardContinuous
      X.smallEtaleTopology S.smallEtaleTopology)

/- `CategoryTheory.MorphismProperty C` is the type of families `⦃X Y : C⦄ → (X ⟶ Y) → Prop`, and
the small étale site `AlgebraicGeometry.Scheme.Etale` is `MorphismProperty.Over @Etale ⊤ X`.
Recognizing `@Etale` at that type, and an object of the site as an object of the comma category,
needs those definitions unfolded, so they are made `implicit_reducible` from here on. -/
attribute [local implicit_reducible] CategoryTheory.MorphismProperty
  AlgebraicGeometry.Scheme.Etale

/-- For an étale `f : X ⟶ S` and an isomorphism `e` from `X`, viewed as an object of the small
étale site of `S`, to `U`, the sections of `F` over `U` are in bijection with the global sections
of `f^{-1} F`. -/
private def etaleSectionLiftAux {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale)
    (e : (Scheme.Etale.smallEtaleCompose f).obj (smallEtaleFinal X) ≅ U) :
    F.obj.obj (Opposite.op U) ≃
      (Sheaf.Γ _ _).obj ((smallEtaleInverseImage f).obj F) := by
  let R := (smallEtaleRestrictionIso f).app F
  let G := ((Scheme.Etale.smallEtaleCompose f).sheafPushforwardContinuous
    (Type (max (u + 1) v)) X.smallEtaleTopology S.smallEtaleTopology).obj F
  let terminalLimit := limitOfDiagramInitial
    (isTerminalSmallEtaleFinal X).op G.obj
  exact ((Sheaf.Γ _ _).mapIso R ≪≫
    (G.isLimitConeΓ.conePointUniqueUpToIso terminalLimit) ≪≫
    (F.obj.mapIso e.op).symm).toEquiv.symm

private def etaleSectionLift {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale) :
    F.obj.obj (Opposite.op U) ≃
      (Sheaf.Γ _ _).obj ((smallEtaleInverseImage U.hom).obj F) :=
  etaleSectionLiftAux U.hom F U (MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 U.left ≫ U.hom = 𝟙 U.left ≫ U.hom
    rfl))

private def etaleDiagonal {S : Scheme.{u}} (U : S.Etale) :
    smallEtaleFinal U.left ⟶ (smallEtaleBaseChange U.hom).obj U :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) (𝟙 _) (by simp)) (by
    change pullback.lift (𝟙 _) (𝟙 _) _ ≫ pullback.snd U.hom U.hom = 𝟙 _
    exact pullback.lift_snd _ _ _)

private lemma smallEtaleRestrictionIso_unit
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale) :
    ((smallEtaleInverseImageAdjunction f).unit.app F).hom.app (Opposite.op U) ≫
      ((smallEtaleRestrictionIso f).hom.app F).hom.app
        (Opposite.op ((smallEtaleBaseChange f).obj U)) =
      F.obj.map (MorphismProperty.Over.homMk (pullback.fst U.hom f)
        pullback.condition :
          (Scheme.Etale.smallEtaleCompose f).obj ((smallEtaleBaseChange f).obj U) ⟶ U).op := by
  let adj := Scheme.Etale.smallEtaleComposeBaseChangeAdj f
  have h := (smallEtaleInverseImageAdjunction f).unit_leftAdjointUniq_hom_app
    (adj.sheafPushforwardContinuous X.smallEtaleTopology S.smallEtaleTopology) F
  have h' := congrArg (fun morphism ↦ morphism.hom.app (Opposite.op U)) h
  exact h'.trans (adj.sheafPushforwardContinuous_unit_app_hom_app _ _ F _)

/-- `smallEtaleRestrictionIso_unit`, stated through `smallEtaleUnitApp`. -/
private lemma smallEtaleUnitApp_restrictionIso
    {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale) :
    smallEtaleUnitApp f F U ≫
      ((smallEtaleRestrictionIso f).hom.app F).hom.app
        (Opposite.op ((smallEtaleBaseChange f).obj U)) =
      F.obj.map (MorphismProperty.Over.homMk (pullback.fst U.hom f)
        pullback.condition :
          (Scheme.Etale.smallEtaleCompose f).obj ((smallEtaleBaseChange f).obj U) ⟶ U).op :=
  smallEtaleRestrictionIso_unit f F U

/-- Two successive restrictions of a section compose to the restriction along the composite. -/
private lemma map_op_comp_eq {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*)
    {A B D : C} (p : B ⟶ A) (q : D ⟶ B) {r : D ⟶ A} (hr : q ≫ p = r) :
    P.map p.op ≫ P.map q.op = P.map r.op := by
  subst hr
  rw [op_comp, P.map_comp]

private lemma etaleSectionLiftAux_ΓRes {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale)
    (e : (Scheme.Etale.smallEtaleCompose f).obj (smallEtaleFinal X) ≅ U)
    (s : F.obj.obj (Opposite.op U)) :
    ((smallEtaleRestrictionIso f).hom.app F).hom.app
        (Opposite.op (smallEtaleFinal X))
      (((smallEtaleInverseImage f).obj F).ΓRes
        (Opposite.op (smallEtaleFinal X)) (etaleSectionLiftAux f F U e s)) =
      F.obj.map e.hom.op s := by
  let H := (smallEtaleInverseImage f).obj F
  let R := (smallEtaleRestrictionIso f).app F
  let G := ((Scheme.Etale.smallEtaleCompose f).sheafPushforwardContinuous
    (Type (max (u + 1) v)) X.smallEtaleTopology S.smallEtaleTopology).obj F
  let L := limitOfDiagramInitial
    (isTerminalSmallEtaleFinal X).op G.obj
  have h := G.isLimitConeΓ.conePointUniqueUpToIso_inv_comp L
    (Opposite.op (smallEtaleFinal X))
  change R.hom.hom.app (Opposite.op (smallEtaleFinal X))
    (H.ΓRes (Opposite.op (smallEtaleFinal X))
      (((Sheaf.Γ _ _).map R.inv)
        ((G.isLimitConeΓ.conePointUniqueUpToIso L).inv (F.obj.map e.hom.op s)))) = _
  rw [← types_comp_apply, ← Sheaf.ΓRes_naturality]
  change (((Sheaf.Γ _ _).map R.inv ≫ (Sheaf.Γ _ _).map R.hom ≫ G.ΓRes _)
    ((G.isLimitConeΓ.conePointUniqueUpToIso L).inv (F.obj.map e.hom.op s))) = _
  rw [← Category.assoc, ← Functor.map_comp, R.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  have hid : (coneOfDiagramInitial
      (isTerminalSmallEtaleFinal X).op
      G.obj).π.app (Opposite.op (smallEtaleFinal X)) = 𝟙 _ := by
    change G.obj.map _ = 𝟙 _
    have hid : (isTerminalSmallEtaleFinal X).op.to
          (Opposite.op (smallEtaleFinal X)) = 𝟙 _ :=
      (isTerminalSmallEtaleFinal X).op.hom_ext _ _
    rw [hid, CategoryTheory.Functor.map_id]
  have h' : (G.isLimitConeΓ.conePointUniqueUpToIso L).inv ≫ G.ΓRes _ = 𝟙 _ :=
    h.trans hid
  exact ConcreteCategory.congr_hom h' (F.obj.map e.hom.op s)

private lemma etaleSectionLift_ΓRes
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (U : S.Etale) (s : F.obj.obj (Opposite.op U)) :
    ((smallEtaleRestrictionIso U.hom).hom.app F).hom.app
        (Opposite.op (smallEtaleFinal U.left))
      (((smallEtaleInverseImage U.hom).obj F).ΓRes
        (Opposite.op (smallEtaleFinal U.left)) (etaleSectionLift F U s)) =
      F.obj.map (MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 U.left ≫ U.hom = 𝟙 U.left ≫ U.hom
        rfl)).hom.op s :=
  etaleSectionLiftAux_ΓRes U.hom F U _ s

private lemma etaleSectionLift_diagonal
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (U : S.Etale) (s : F.obj.obj (Opposite.op U)) :
    ((smallEtaleInverseImage U.hom).obj F).ΓRes
      (Opposite.op (smallEtaleFinal U.left)) (etaleSectionLift F U s) =
      smallEtaleInverseImageSections U.hom F (etaleDiagonal U) s := by
  apply (CategoryTheory.mono_iff_injective
    (((smallEtaleRestrictionIso U.hom).hom.app F).hom.app
      (Opposite.op (smallEtaleFinal U.left)))).mp inferInstance
  have hkey : smallEtaleUnitApp U.hom F U ≫
      ((smallEtaleInverseImage U.hom).obj F).obj.map (etaleDiagonal U).op ≫
        ((smallEtaleRestrictionIso U.hom).hom.app F).hom.app
          (Opposite.op (smallEtaleFinal U.left)) =
      F.obj.map (MorphismProperty.Over.homMk (pullback.fst U.hom U.hom)
          pullback.condition :
        (Scheme.Etale.smallEtaleCompose U.hom).obj
          ((smallEtaleBaseChange U.hom).obj U) ⟶ U).op ≫
        F.obj.map ((Scheme.Etale.smallEtaleCompose U.hom).map (etaleDiagonal U)).op := by
    rw [((smallEtaleRestrictionIso U.hom).hom.app F).hom.naturality (etaleDiagonal U).op,
      ← Category.assoc, smallEtaleUnitApp_restrictionIso]
    rfl
  have hmor : (Scheme.Etale.smallEtaleCompose U.hom).map (etaleDiagonal U) ≫
      (MorphismProperty.Over.homMk (pullback.fst U.hom U.hom) pullback.condition :
        (Scheme.Etale.smallEtaleCompose U.hom).obj
          ((smallEtaleBaseChange U.hom).obj U) ⟶ U) =
      (MorphismProperty.Over.isoMk (Iso.refl U.left) (by
        change 𝟙 U.left ≫ U.hom = 𝟙 U.left ≫ U.hom
        rfl) : (Scheme.Etale.smallEtaleCompose U.hom).obj
          (smallEtaleFinal U.left) ≅ U).hom := by
    refine MorphismProperty.Over.Hom.ext ?_
    have hleft : pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp) ≫
        pullback.fst U.hom U.hom = 𝟙 U.left := pullback.lift_fst _ _ _
    exact hleft
  have hR := ConcreteCategory.congr_hom (hkey.trans (map_op_comp_eq F.obj _ _ hmor)) s
  exact (etaleSectionLift_ΓRes F U s).trans hR.symm

private lemma etaleSectionLift_germ
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale)
    (a : Spec (.of Ω) ⟶ U.left) (s : F.obj.obj (Opposite.op U)) :
    (smallEtalePullbackStalkIso U.hom a).hom.app F
      (globalSectionGerm a ((smallEtaleInverseImage U.hom).obj F)
        (etaleSectionLift F U s)) =
      (pointSmallEtale (a ≫ U.hom)).toPresheafFiber U
        (Over.homMk a rfl) F.obj s := by
  change (smallEtalePullbackStalkIso U.hom a).hom.app F
    ((pointSmallEtale a).toPresheafFiber (smallEtaleFinal U.left) (smallEtaleFinalPoint a)
      ((smallEtaleInverseImage U.hom).obj F).obj
      (((smallEtaleInverseImage U.hom).obj F).ΓRes _ (etaleSectionLift F U s))) = _
  rw [etaleSectionLift_diagonal]
  have h := ConcreteCategory.congr_hom
    (smallEtaleInverseImageSections_germ U.hom a F (etaleDiagonal U) (smallEtaleFinalPoint a)) s
  refine h.trans (congrArg
    (fun b ↦ (pointSmallEtale (a ≫ U.hom)).toPresheafFiber U b F.obj s) ?_)
  apply Over.OverMorphism.ext
  have hfst : (a ≫ pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp)) ≫
      pullback.fst U.hom U.hom = a := by
    rw [Category.assoc, pullback.lift_fst, Category.comp_id]
  exact hfst

private lemma smallEtaleInverseImageCompIso_unit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology (Type (max (u + 1) v))) (U : Z.Etale) :
    ((smallEtaleInverseImageAdjunction g).unit.app F).hom.app
        (Opposite.op U) ≫
      ((smallEtaleInverseImageAdjunction f).unit.app
        ((smallEtaleInverseImage g).obj F)).hom.app
          (Opposite.op ((smallEtaleBaseChange g).obj U)) ≫
      ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
        (Opposite.op ((smallEtaleBaseChange f).obj
          ((smallEtaleBaseChange g).obj U))) =
    ((smallEtaleInverseImageAdjunction (f ≫ g)).unit.app F).hom.app
        (Opposite.op U) ≫
      ((smallEtaleInverseImage (f ≫ g)).obj F).obj.map
        ((smallEtaleBaseChangeComp f g).inv.app U).op := by
  have h := unit_conjugateEquiv_symm
    (smallEtaleInverseImageAdjunction (f ≫ g))
    ((smallEtaleInverseImageAdjunction g).comp
      (smallEtaleInverseImageAdjunction f))
    (smallEtalePushforwardCompIso f g).inv F
  have h' := congrArg (fun morphism ↦ morphism.hom.app (Opposite.op U)) h
  change ((smallEtaleInverseImageAdjunction (f ≫ g)).unit.app F).hom.app
      (Opposite.op U) ≫
    ((smallEtalePushforwardCompIso f g).inv.app
      ((smallEtaleInverseImage (f ≫ g)).obj F)).hom.app (Opposite.op U) =
    (((smallEtaleInverseImageAdjunction g).comp
      (smallEtaleInverseImageAdjunction f)).unit.app F).hom.app
        (Opposite.op U) ≫
      ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
        (Opposite.op ((smallEtaleBaseChange f).obj
          ((smallEtaleBaseChange g).obj U))) at h'
  rw [Adjunction.comp_unit_app] at h'
  change ((smallEtaleInverseImageAdjunction (f ≫ g)).unit.app F).hom.app
      (Opposite.op U) ≫
    ((smallEtalePushforwardCompIso f g).inv.app
      ((smallEtaleInverseImage (f ≫ g)).obj F)).hom.app (Opposite.op U) =
    (((smallEtaleInverseImageAdjunction g).unit.app F).hom.app (Opposite.op U) ≫
      ((smallEtaleInverseImageAdjunction f).unit.app
        ((smallEtaleInverseImage g).obj F)).hom.app
          (Opposite.op ((smallEtaleBaseChange g).obj U))) ≫
      ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
        (Opposite.op ((smallEtaleBaseChange f).obj
          ((smallEtaleBaseChange g).obj U))) at h'
  rw [smallEtalePushforwardCompIso,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app] at h'
  exact (Category.assoc _ _ _).symm.trans h'.symm

/-- `smallEtaleInverseImageCompIso_unit`, stated through `smallEtaleUnitApp`. -/
private lemma smallEtaleUnitApp_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology (Type (max (u + 1) v))) (U : Z.Etale) :
    smallEtaleUnitApp g F U ≫
      smallEtaleUnitApp f ((smallEtaleInverseImage g).obj F)
          ((smallEtaleBaseChange g).obj U) ≫
        ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
          (Opposite.op ((smallEtaleBaseChange f).obj
            ((smallEtaleBaseChange g).obj U))) =
    smallEtaleUnitApp (f ≫ g) F U ≫
      ((smallEtaleInverseImage (f ≫ g)).obj F).obj.map
        ((smallEtaleBaseChangeComp f g).inv.app U).op :=
  smallEtaleInverseImageCompIso_unit f g F U

/-- Naturality of `smallEtaleUnitApp` in the étale `S`-scheme. -/
private lemma smallEtaleUnitApp_naturality_obj {T S : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) {V W : S.Etale} (a : V ⟶ W) :
    G.obj.map a.op ≫ smallEtaleUnitApp f G V =
      smallEtaleUnitApp f G W ≫ ((smallEtaleInverseImage f).obj G).obj.map
        ((smallEtaleBaseChange f).map a).op :=
  ((smallEtaleInverseImageAdjunction f).unit.app G).hom.naturality a.op

private lemma globalSectionsSmallEtaleInverseImage_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology (Type (max (u + 1) v))) :
    (globalSectionsSmallEtaleInverseImage g).app F ≫
      (globalSectionsSmallEtaleInverseImage f).app
        ((smallEtaleInverseImage g).obj F) ≫
      (Sheaf.Γ _ _).map ((smallEtaleInverseImageCompIso f g).hom.app F) =
    (globalSectionsSmallEtaleInverseImage (f ≫ g)).app F := by
  apply ((Functor.Initial.isLimitWhiskerEquiv
    (smallEtaleBaseChange g).op _).symm
      (smallEtaleBaseChangeGlobalSectionsIsLimit f
        ((smallEtaleInverseImage (f ≫ g)).obj F))).hom_ext
  intro U
  change (_ ≫ _ ≫ _) ≫
      ((smallEtaleInverseImage (f ≫ g)).obj F).ΓRes
        (Opposite.op ((smallEtaleBaseChange f).obj
          ((smallEtaleBaseChange g).obj U.unop))) =
    (globalSectionsSmallEtaleInverseImage (f ≫ g)).app F ≫
      ((smallEtaleInverseImage (f ≫ g)).obj F).ΓRes
        (Opposite.op ((smallEtaleBaseChange f).obj
          ((smallEtaleBaseChange g).obj U.unop)))
  have hf := globalSectionsComparison_ΓRes f
    ((smallEtaleInverseImage g).obj F)
      ((smallEtaleBaseChange g).obj U.unop)
  have hg := globalSectionsComparison_ΓRes g F U.unop
  have hfg := globalSectionsComparison_ΓRes (f ≫ g) F U.unop
  simp only [Category.assoc]
  rw [Sheaf.ΓRes_naturality, ← Category.assoc _ _
    (((smallEtaleInverseImageCompIso f g).hom.app F).hom.app _), hf]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (_ ≫ _), hg]
  simp only [Category.assoc]
  rw [smallEtaleUnitApp_comp, ← Category.assoc, ← hfg]
  simp only [Category.assoc, Sheaf.ΓRes_map]
  rfl

private lemma smallEtaleInverseImageSections_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology (Type (max (u + 1) v)))
    {U : Z.Etale} {V : Y.Etale} {W : X.Etale}
    (a : V ⟶ (smallEtaleBaseChange g).obj U)
    (b : W ⟶ (smallEtaleBaseChange f).obj V) :
    smallEtaleInverseImageSections g F a ≫
      smallEtaleInverseImageSections f
        ((smallEtaleInverseImage g).obj F) b ≫
      ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app (Opposite.op W) =
    smallEtaleInverseImageSections (f ≫ g) F
      (b ≫ (smallEtaleBaseChange f).map a ≫
        (smallEtaleBaseChangeComp f g).inv.app U) := by
  let H := (smallEtaleInverseImage g).obj F
  let L := (smallEtaleInverseImage f).obj H
  let M := (smallEtaleInverseImage (f ≫ g)).obj F
  have hunit : H.obj.map a.op ≫
      smallEtaleUnitApp f ((smallEtaleInverseImage g).obj F) V =
    smallEtaleUnitApp f ((smallEtaleInverseImage g).obj F)
        ((smallEtaleBaseChange g).obj U) ≫
      L.obj.map ((smallEtaleBaseChange f).map a).op :=
    smallEtaleUnitApp_naturality_obj f H a
  have hcomp := ((smallEtaleInverseImageCompIso f g).hom.app F).hom.naturality b.op
  change L.obj.map b.op ≫ ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
      (Opposite.op W) =
    ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
      (Opposite.op ((smallEtaleBaseChange f).obj V)) ≫ M.obj.map b.op at hcomp
  have hcomp' := ((smallEtaleInverseImageCompIso f g).hom.app F).hom.naturality
    ((smallEtaleBaseChange f).map a).op
  change L.obj.map ((smallEtaleBaseChange f).map a).op ≫
    ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
      (Opposite.op ((smallEtaleBaseChange f).obj V)) =
    ((smallEtaleInverseImageCompIso f g).hom.app F).hom.app
      (Opposite.op ((smallEtaleBaseChange f).obj
        ((smallEtaleBaseChange g).obj U))) ≫
      M.obj.map ((smallEtaleBaseChange f).map a).op at hcomp'
  dsimp only [smallEtaleInverseImageSections]
  simp only [Category.assoc]
  rw [hcomp]
  rw [← Category.assoc (H.obj.map a.op) _ (_ ≫ _), hunit]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (M.obj.map b.op), hcomp']
  simp only [Category.assoc]
  rw [← Category.assoc
    (smallEtaleUnitApp f ((smallEtaleInverseImage g).obj F)
      ((smallEtaleBaseChange g).obj U)) _ (_ ≫ _)]
  have h := smallEtaleUnitApp_comp f g F U
  rw [← Category.assoc _ _ (_ ≫ _), h]
  simp only [op_comp, Functor.map_comp, Category.assoc]
  rfl

private lemma smallEtaleInverseImageSections_congr
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale}
    (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (b : U ⟶ (smallEtaleBaseChange g).obj V)
    (hab : a ≫ (eqToIso (congrArg (fun morphism ↦
      (smallEtaleBaseChange morphism).obj V) h)).hom = b) :
    smallEtaleInverseImageSections f F a ≫
      ((eqToIso (congrArg (fun morphism ↦
        (smallEtaleInverseImage.{u, v} morphism).obj F) h)).hom).hom.app
          (Opposite.op U) =
      smallEtaleInverseImageSections g F b := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id] at hab
  subst b
  simp

private lemma smallEtaleBaseChange_congr_fst
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g) (V : S.Etale) :
    ((eqToIso (congrArg (fun morphism ↦
      (smallEtaleBaseChange morphism).obj V) h)).hom).left ≫
        pullback.fst V.hom g = pullback.fst V.hom f := by
  cases h
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Cancellation of a one-sided inverse in a composite of morphisms of schemes. -/
private lemma comp_eq_of_inv_comp {A B D : Scheme.{u}} (ι : A ⟶ B) (κ : B ⟶ A)
    (π : B ⟶ D) (ρ : A ⟶ D) (hκ : κ ≫ ρ = π) (hid : ι ≫ κ = 𝟙 A) :
    ι ≫ π = ρ := by
  rw [← hκ, ← Category.assoc, hid, Category.id_comp]

/-- Rearrangement of a fourfold composite of morphisms of schemes. -/
private lemma comp_rearrange_of_comp_eq {A B D E J K L : Scheme.{u}}
    (β : A ⟶ B) (μ : B ⟶ D) (ι : D ⟶ E) (π : E ⟶ J) (σ : D ⟶ K) (τ : K ⟶ J)
    (φ : B ⟶ L) (ψ : L ⟶ K) (hι : ι ≫ π = σ ≫ τ) (hμ : μ ≫ σ = φ ≫ ψ) :
    (β ≫ μ ≫ ι) ≫ π = β ≫ φ ≫ ψ ≫ τ := by
  rw [Category.assoc, Category.assoc, hι, ← Category.assoc μ σ τ, hμ, Category.assoc]

/-- Reassociation absorbing the inner factor of a composite of morphisms of schemes. -/
private lemma comp_comp_eq {A B C D : Scheme.{u}} (ι : A ⟶ B) (κ : B ⟶ C) (π : C ⟶ D)
    (ρ : B ⟶ D) (h : κ ≫ π = ρ) : (ι ≫ κ) ≫ π = ι ≫ ρ := by
  rw [Category.assoc, h]

/-- A fourfold composite whose first two factors cancel and whose third factor is an identity. -/
private lemma comp_four_eq_of_comp_id_left {A B C : Scheme.{u}} (α : A ⟶ B) (β : B ⟶ A)
    (δ : A ⟶ C) (h : α ≫ β = 𝟙 A) : α ≫ β ≫ 𝟙 A ≫ δ = δ := by
  rw [← Category.assoc, h, Category.id_comp, Category.id_comp]

/-- A fourfold composite whose last two factors cancel. -/
private lemma comp_four_eq_of_comp_id_right {A B C D : Scheme.{u}} (α : A ⟶ B) (β : B ⟶ C)
    (γ : C ⟶ D) (δ : D ⟶ C) (ρ : A ⟶ C) (hαβ : α ≫ β = ρ) (hγδ : γ ≫ δ = 𝟙 C) :
    α ≫ β ≫ γ ≫ δ = ρ := by
  rw [← Category.assoc, hαβ, hγδ, Category.comp_id]

private lemma smallEtaleBaseChangeComp_inv_fst
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).inv.app U).left ≫ pullback.fst U.hom (f ≫ g) =
      pullback.fst (pullback.snd U.hom g) f ≫ pullback.fst U.hom g := by
  have : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  refine comp_eq_of_inv_comp _ ((smallEtaleBaseChangeComp f g).hom.app U).left _ _
    (MorphismProperty.Over.pullbackComp_left_fst_fst f g U) ?_
  exact congrArg (fun morphism ↦ morphism.left)
    ((smallEtaleBaseChangeComp f g).inv_hom_id_app U)

private lemma smallEtaleBaseChange_map_fst
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (a : U ⟶ V) :
    ((smallEtaleBaseChange f).map a).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

private lemma smallEtaleBaseChangeComposite_fst
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {U : Z.Etale} {V : Y.Etale} {W : X.Etale}
    (a : V ⟶ (smallEtaleBaseChange g).obj U)
    (b : W ⟶ (smallEtaleBaseChange f).obj V) :
    (b ≫ (smallEtaleBaseChange f).map a ≫
      (smallEtaleBaseChangeComp f g).inv.app U).left ≫
        pullback.fst U.hom (f ≫ g) =
      b.left ≫ pullback.fst V.hom f ≫ a.left ≫ pullback.fst U.hom g := by
  have hmap : ((smallEtaleBaseChange f).map a).left ≫
      pullback.fst (pullback.snd U.hom g) f = pullback.fst V.hom f ≫ a.left :=
    smallEtaleBaseChange_map_fst f a
  exact comp_rearrange_of_comp_eq b.left ((smallEtaleBaseChange f).map a).left
    ((smallEtaleBaseChangeComp f g).inv.app U).left (pullback.fst U.hom (f ≫ g))
    (pullback.fst (pullback.snd U.hom g) f) (pullback.fst U.hom g)
    (pullback.fst V.hom f) a.left (smallEtaleBaseChangeComp_inv_fst f g U) hmap

private lemma globalSectionsComparison_congr
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    (globalSectionsSmallEtaleInverseImage f).app F ≫
      (Sheaf.Γ _ _).map (eqToIso (congrArg (fun morphism ↦
        (smallEtaleInverseImage.{u, v} morphism).obj F) h)).hom =
      (globalSectionsSmallEtaleInverseImage g).app F := by
  cases h
  simp

private lemma globalSections_map_ΓRes
    {S : Scheme.{u}} {F G : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))}
    (a : F ⟶ G) (U : S.Etale) (t : (Sheaf.Γ _ _).obj F) :
    G.ΓRes (Opposite.op U) ((Sheaf.Γ _ _).map a t) =
      a.hom.app (Opposite.op U) (F.ΓRes (Opposite.op U) t) :=
  ConcreteCategory.congr_hom (Sheaf.ΓRes_naturality a (Opposite.op U)) t

/-- `globalSections_map_ΓRes` for the transport isomorphism attached to an equality `f = g`
of morphisms. -/
private lemma globalSections_map_eqToIso_ΓRes
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : X.Etale)
    (t : (Sheaf.Γ _ _).obj ((smallEtaleInverseImage.{u, v} f).obj F)) :
    ((smallEtaleInverseImage.{u, v} g).obj F).ΓRes (Opposite.op U)
      ((Sheaf.Γ _ _).map (eqToIso (congrArg (fun morphism ↦
        (smallEtaleInverseImage.{u, v} morphism).obj F) h)).hom t) =
      (eqToIso (congrArg (fun morphism ↦
        (smallEtaleInverseImage.{u, v} morphism).obj F) h)).hom.hom.app
          (Opposite.op U)
          (((smallEtaleInverseImage.{u, v} f).obj F).ΓRes (Opposite.op U) t) :=
  globalSections_map_ΓRes _ U t

/-- `smallEtaleInverseImageSections_congr` evaluated at a section. -/
private lemma smallEtaleInverseImageSections_congr_apply
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale}
    (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (b : U ⟶ (smallEtaleBaseChange g).obj V)
    (hab : a ≫ (eqToIso (congrArg (fun morphism ↦
      (smallEtaleBaseChange morphism).obj V) h)).hom = b)
    (s : F.obj.obj (Opposite.op V)) :
    (eqToIso (congrArg (fun morphism ↦
      (smallEtaleInverseImage.{u, v} morphism).obj F) h)).hom.hom.app
        (Opposite.op U) (smallEtaleInverseImageSections f F a s) =
      smallEtaleInverseImageSections g F b s := by
  simpa only [CategoryTheory.comp_apply] using
    ConcreteCategory.congr_hom (smallEtaleInverseImageSections_congr h F a b hab) s

/-- If the restriction to `U` of a global section `t` of `f⁻¹F` is
`smallEtaleInverseImageSections f F a s`, then the restriction of its transport along `f = g` is
`smallEtaleInverseImageSections g F b s`. -/
private lemma globalSections_map_eqToIso_ΓRes_sections
    {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale}
    (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (b : U ⟶ (smallEtaleBaseChange g).obj V)
    (hab : a ≫ (eqToIso (congrArg (fun morphism ↦
      (smallEtaleBaseChange morphism).obj V) h)).hom = b)
    (s : F.obj.obj (Opposite.op V))
    (t : (Sheaf.Γ _ _).obj ((smallEtaleInverseImage.{u, v} f).obj F))
    (ht : ((smallEtaleInverseImage.{u, v} f).obj F).ΓRes (Opposite.op U) t =
      smallEtaleInverseImageSections f F a s) :
    ((smallEtaleInverseImage.{u, v} g).obj F).ΓRes (Opposite.op U)
      ((Sheaf.Γ _ _).map (eqToIso (congrArg (fun morphism ↦
        (smallEtaleInverseImage.{u, v} morphism).obj F) h)).hom t) =
      smallEtaleInverseImageSections g F b s :=
  ((globalSections_map_eqToIso_ΓRes h F U t).trans
    (congrArg (fun z ↦ (eqToIso (congrArg (fun morphism ↦
      (smallEtaleInverseImage.{u, v} morphism).obj F) h)).hom.hom.app
        (Opposite.op U) z) ht)).trans
    (smallEtaleInverseImageSections_congr_apply h F a b hab s)

/-- The lift of `pullback.fst V.hom f` to the base change, along that same projection, of the
final object of the small étale site of `V`. -/
private def smallEtalePullbackFinalLift {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Etale) :
    smallEtaleFinal ((smallEtaleBaseChange f).obj V).left ⟶
      (smallEtaleBaseChange (pullback.fst V.hom f)).obj (smallEtaleFinal V.left) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst V.hom f) (𝟙 _)
      ((Category.comp_id (pullback.fst V.hom f)).trans
        (Category.id_comp (pullback.fst V.hom f)).symm))
    (pullback.lift_snd _ _ _)

/-- The diagonal section of the base change of `V` to `V ×_S X`, read through base change along
`pullback.snd V.hom f` followed by `f`. -/
private def smallEtalePullbackDiagonalSnd {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Etale) :
    smallEtaleFinal ((smallEtaleBaseChange f).obj V).left ⟶
      (smallEtaleBaseChange (pullback.snd V.hom f ≫ f)).obj V :=
  etaleDiagonal ((smallEtaleBaseChange f).obj V) ≫
    (smallEtaleBaseChange (pullback.snd V.hom f)).map
      (𝟙 ((smallEtaleBaseChange f).obj V)) ≫
    (smallEtaleBaseChangeComp (pullback.snd V.hom f) f).inv.app V

/-- The same diagonal section, read through base change along `pullback.fst V.hom f` followed
by `V.hom`. -/
private def smallEtalePullbackDiagonalFst {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Etale) :
    smallEtaleFinal ((smallEtaleBaseChange f).obj V).left ⟶
      (smallEtaleBaseChange (pullback.fst V.hom f ≫ V.hom)).obj V :=
  smallEtalePullbackFinalLift f V ≫
    (smallEtaleBaseChange (pullback.fst V.hom f)).map (etaleDiagonal V) ≫
    (smallEtaleBaseChangeComp (pullback.fst V.hom f) V.hom).inv.app V

private lemma smallEtalePullbackDiagonal_congr
    {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Etale) :
    smallEtalePullbackDiagonalSnd f V ≫ (eqToIso (congrArg (fun morphism ↦
      (smallEtaleBaseChange morphism).obj V)
        (pullback.condition (f := V.hom) (g := f)).symm)).hom =
      smallEtalePullbackDiagonalFst f V := by
  let W := (smallEtaleBaseChange f).obj V
  let p := pullback.snd V.hom f
  let q := pullback.fst V.hom f
  let b := smallEtalePullbackFinalLift f V
  let c := smallEtalePullbackDiagonalSnd f V
  let d := smallEtalePullbackDiagonalFst f V
  let κ := (eqToIso (congrArg (fun morphism ↦
    (smallEtaleBaseChange morphism).obj V)
      (pullback.condition (f := V.hom) (g := f)).symm)).hom
  change c ≫ κ = d
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · have hκ : κ.left ≫ pullback.fst V.hom (q ≫ V.hom) =
        pullback.fst V.hom (p ≫ f) :=
      smallEtaleBaseChange_congr_fst
        (pullback.condition (f := V.hom) (g := f)).symm V
    have hc : c.left ≫ pullback.fst V.hom (p ≫ f) =
        (etaleDiagonal W).left ≫ pullback.fst W.hom p ≫
          𝟙 W.left ≫ pullback.fst V.hom f :=
      smallEtaleBaseChangeComposite_fst p f (𝟙 W) (etaleDiagonal W)
    have hd : d.left ≫ pullback.fst V.hom (q ≫ V.hom) =
        b.left ≫ pullback.fst (smallEtaleFinal V.left).hom q ≫
          (etaleDiagonal V).left ≫ pullback.fst V.hom V.hom :=
      smallEtaleBaseChangeComposite_fst q V.hom (etaleDiagonal V) b
    have hw : (etaleDiagonal W).left ≫ pullback.fst W.hom p = 𝟙 W.left :=
      pullback.lift_fst _ _ _
    have hv : (etaleDiagonal V).left ≫ pullback.fst V.hom V.hom = 𝟙 V.left :=
      pullback.lift_fst _ _ _
    have hb : b.left ≫ pullback.fst (smallEtaleFinal V.left).hom q = q :=
      pullback.lift_fst _ _ _
    have step : (etaleDiagonal W).left ≫ pullback.fst W.hom p ≫
          𝟙 W.left ≫ pullback.fst V.hom f =
        b.left ≫ pullback.fst (smallEtaleFinal V.left).hom q ≫
          (etaleDiagonal V).left ≫ pullback.fst V.hom V.hom :=
      (comp_four_eq_of_comp_id_left _ _ _ hw).trans
        (comp_four_eq_of_comp_id_right _ _ _ _ _ hb hv).symm
    exact ((comp_comp_eq c.left _ _ _ hκ).trans hc).trans (step.trans hd.symm)
  · have hκ : κ.left ≫ pullback.snd V.hom (q ≫ V.hom) =
        pullback.snd V.hom (p ≫ f) := MorphismProperty.Over.w κ
    have hc : c.left ≫ pullback.snd V.hom (p ≫ f) = 𝟙 W.left :=
      MorphismProperty.Over.w c
    have hd : d.left ≫ pullback.snd V.hom (q ≫ V.hom) = 𝟙 W.left :=
      MorphismProperty.Over.w d
    exact ((comp_comp_eq c.left _ _ _ hκ).trans hc).trans hd.symm

private lemma etaleSectionLift_pullback_unit
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale)
    (s : F.obj.obj (Opposite.op V)) :
    ((smallEtaleInverseImageCompIso (pullback.snd V.hom f) f).app F).hom.hom.app
        (Opposite.op (smallEtaleFinal ((smallEtaleBaseChange f).obj V).left))
      (smallEtaleInverseImageSections (pullback.snd V.hom f)
        ((smallEtaleInverseImage f).obj F)
        (etaleDiagonal ((smallEtaleBaseChange f).obj V))
        (smallEtaleUnitApp f F V s)) =
      smallEtaleInverseImageSections (pullback.snd V.hom f ≫ f) F
        (smallEtalePullbackDiagonalSnd f V) s := by
  let W := (smallEtaleBaseChange f).obj V
  let p := pullback.snd V.hom f
  let H := (smallEtaleInverseImage f).obj F
  have hid : smallEtaleInverseImageSections f F (𝟙 W) =
      smallEtaleUnitApp f F V := by
    change _ ≫ H.obj.map (𝟙 W).op = _
    rw [op_id, H.obj.map_id, Category.comp_id]
  have h := ConcreteCategory.congr_hom
    (smallEtaleInverseImageSections_comp p f F (𝟙 W) (etaleDiagonal W)) s
  rw [hid] at h
  simp only [CategoryTheory.comp_apply] at h
  exact h

private lemma etaleSectionLift_pullback_mid
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale)
    (s : F.obj.obj (Opposite.op V)) :
    ((smallEtaleInverseImage (pullback.snd V.hom f ≫ f)).obj F).ΓRes
        (Opposite.op (smallEtaleFinal ((smallEtaleBaseChange f).obj V).left))
      ((Sheaf.Γ _ _).map
        ((smallEtaleInverseImageCompIso (pullback.snd V.hom f) f).app F).hom
        (etaleSectionLift ((smallEtaleInverseImage f).obj F)
          ((smallEtaleBaseChange f).obj V) (smallEtaleUnitApp f F V s))) =
      smallEtaleInverseImageSections (pullback.snd V.hom f ≫ f) F
        (smallEtalePullbackDiagonalSnd f V) s := by
  let W := (smallEtaleBaseChange f).obj V
  let p := pullback.snd V.hom f
  let H := (smallEtaleInverseImage f).obj F
  let T := Opposite.op (smallEtaleFinal W.left)
  let ep := (smallEtaleInverseImageCompIso p f).app F
  let x := etaleSectionLift H W (smallEtaleUnitApp f F V s)
  have h2 : ((smallEtaleInverseImage (p ≫ f)).obj F).ΓRes T
      ((Sheaf.Γ _ _).map ep.hom x) =
      ep.hom.hom.app T (((smallEtaleInverseImage p).obj H).ΓRes T x) :=
    globalSections_map_ΓRes ep.hom (smallEtaleFinal W.left) x
  have h3 : ((smallEtaleInverseImage p).obj H).ΓRes T x =
      smallEtaleInverseImageSections p H (etaleDiagonal W)
        (smallEtaleUnitApp f F V s) :=
    etaleSectionLift_diagonal H W (smallEtaleUnitApp f F V s)
  exact (h2.trans (congrArg (fun z ↦ ep.hom.hom.app T z) h3)).trans
    (etaleSectionLift_pullback_unit f F V s)

private lemma etaleSectionLift_pullback_left
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale)
    (s : F.obj.obj (Opposite.op V))
    (t : (Sheaf.Γ _ _).obj
      ((smallEtaleInverseImage (pullback.snd V.hom f ≫ f)).obj F))
    (ht : ((smallEtaleInverseImage (pullback.snd V.hom f ≫ f)).obj F).ΓRes
        (Opposite.op (smallEtaleFinal ((smallEtaleBaseChange f).obj V).left)) t =
      smallEtaleInverseImageSections (pullback.snd V.hom f ≫ f) F
        (smallEtalePullbackDiagonalSnd f V) s) :
    ((smallEtaleInverseImage (pullback.fst V.hom f ≫ V.hom)).obj F).ΓRes
        (Opposite.op (smallEtaleFinal ((smallEtaleBaseChange f).obj V).left))
      ((Sheaf.Γ _ _).map (eqToIso (congrArg (fun morphism ↦
          (smallEtaleInverseImage.{u, v} morphism).obj F)
            (pullback.condition (f := V.hom) (g := f)).symm)).hom t) =
      smallEtaleInverseImageSections (pullback.fst V.hom f ≫ V.hom) F
        (smallEtalePullbackDiagonalFst f V) s :=
  globalSections_map_eqToIso_ΓRes_sections
    (pullback.condition (f := V.hom) (g := f)).symm F
    (smallEtalePullbackDiagonalSnd f V) (smallEtalePullbackDiagonalFst f V)
    (smallEtalePullbackDiagonal_congr f V) s t ht

private lemma etaleSectionLift_pullback_right
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale)
    (s : F.obj.obj (Opposite.op V)) :
    ((smallEtaleInverseImage (pullback.fst V.hom f ≫ V.hom)).obj F).ΓRes
        (Opposite.op (smallEtaleFinal ((smallEtaleBaseChange f).obj V).left))
      ((Sheaf.Γ _ _).map
        ((smallEtaleInverseImageCompIso (pullback.fst V.hom f) V.hom).app F).hom
        ((globalSectionsSmallEtaleInverseImage (pullback.fst V.hom f)).app
          ((smallEtaleInverseImage V.hom).obj F) (etaleSectionLift F V s))) =
      smallEtaleInverseImageSections (pullback.fst V.hom f ≫ V.hom) F
        (smallEtalePullbackDiagonalFst f V) s := by
  let W := (smallEtaleBaseChange f).obj V
  let q := pullback.fst V.hom f
  let G := (smallEtaleInverseImage V.hom).obj F
  let M := (smallEtaleInverseImage (q ≫ V.hom)).obj F
  let T := Opposite.op (smallEtaleFinal W.left)
  let eQ := (smallEtaleInverseImageCompIso q V.hom).app F
  let y := etaleSectionLift F V s
  let b := smallEtalePullbackFinalLift f V
  let d := smallEtalePullbackDiagonalFst f V
  have h6 : eQ.hom.hom.app T (smallEtaleInverseImageSections q G b
      (smallEtaleInverseImageSections V.hom F (etaleDiagonal V) s)) =
      smallEtaleInverseImageSections (q ≫ V.hom) F d s := by
    have h := ConcreteCategory.congr_hom
      (smallEtaleInverseImageSections_comp q V.hom F (etaleDiagonal V) b) s
    simp only [CategoryTheory.comp_apply] at h
    exact h
  have h7 : G.ΓRes (Opposite.op (smallEtaleFinal V.left)) y =
      smallEtaleInverseImageSections V.hom F (etaleDiagonal V) s :=
    etaleSectionLift_diagonal F V s
  have h8 : ((smallEtaleInverseImage q).obj G).ΓRes T
      ((globalSectionsSmallEtaleInverseImage q).app G y) =
      smallEtaleInverseImageSections q G b
        (G.ΓRes (Opposite.op (smallEtaleFinal V.left)) y) := by
    have h := ConcreteCategory.congr_hom
      (globalSectionsSmallEtaleInverseImage_app_ΓRes q G b) y
    simp only [CategoryTheory.comp_apply] at h
    exact h
  have h9 : M.ΓRes T ((Sheaf.Γ _ _).map eQ.hom
      ((globalSectionsSmallEtaleInverseImage q).app G y)) =
      eQ.hom.hom.app T (((smallEtaleInverseImage q).obj G).ΓRes T
        ((globalSectionsSmallEtaleInverseImage q).app G y)) :=
    globalSections_map_ΓRes eQ.hom (smallEtaleFinal W.left)
      ((globalSectionsSmallEtaleInverseImage q).app G y)
  have hC : smallEtaleInverseImageSections q G b
        (G.ΓRes (Opposite.op (smallEtaleFinal V.left)) y) =
      smallEtaleInverseImageSections q G b
        (smallEtaleInverseImageSections V.hom F (etaleDiagonal V) s) :=
    congrArg (fun z ↦ smallEtaleInverseImageSections q G b z) h7
  have hD : eQ.hom.hom.app T (((smallEtaleInverseImage q).obj G).ΓRes T
        ((globalSectionsSmallEtaleInverseImage q).app G y)) =
      smallEtaleInverseImageSections (q ≫ V.hom) F d s :=
    (congrArg (fun z ↦ eQ.hom.hom.app T z) (h8.trans hC)).trans h6
  exact h9.trans hD

private lemma etaleSectionLift_pullback_aux
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale)
    (s : F.obj.obj (Opposite.op V)) :
    (Sheaf.Γ _ _).map (eqToIso (congrArg (fun morphism ↦
        (smallEtaleInverseImage.{u, v} morphism).obj F)
          (pullback.condition (f := V.hom) (g := f)).symm)).hom
      ((Sheaf.Γ _ _).map
        ((smallEtaleInverseImageCompIso (pullback.snd V.hom f) f).app F).hom
        (etaleSectionLift ((smallEtaleInverseImage f).obj F)
          ((smallEtaleBaseChange f).obj V) (smallEtaleUnitApp f F V s))) =
      (Sheaf.Γ _ _).map
        ((smallEtaleInverseImageCompIso (pullback.fst V.hom f) V.hom).app F).hom
        ((globalSectionsSmallEtaleInverseImage (pullback.fst V.hom f)).app
          ((smallEtaleInverseImage V.hom).obj F) (etaleSectionLift F V s)) := by
  let W := (smallEtaleBaseChange f).obj V
  let q := pullback.fst V.hom f
  let M := (smallEtaleInverseImage (q ≫ V.hom)).obj F
  let T := Opposite.op (smallEtaleFinal W.left)
  have : IsIso (M.ΓRes T) := globalSections_res_final_isIso M
  apply (CategoryTheory.mono_iff_injective (M.ΓRes T)).mp inferInstance
  exact (etaleSectionLift_pullback_left f F V s _
      (etaleSectionLift_pullback_mid f F V s)).trans
    (etaleSectionLift_pullback_right f F V s).symm

private lemma etaleSectionLift_pullback
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale)
    (s : F.obj.obj (Opposite.op V)) :
    let W := (smallEtaleBaseChange f).obj V
    let p := pullback.snd V.hom f
    let q := pullback.fst V.hom f
    let H := (smallEtaleInverseImage f).obj F
    let e := (smallEtaleInverseImageCompIso p f).app F ≪≫
      eqToIso (congrArg (fun morphism ↦
        (smallEtaleInverseImage.{u, v} morphism).obj F)
          pullback.condition.symm) ≪≫
      ((smallEtaleInverseImageCompIso q V.hom).app F).symm
    (Sheaf.Γ _ _).map e.hom
      (etaleSectionLift H W
        ((((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
          (Opposite.op V)) s)) =
      (globalSectionsSmallEtaleInverseImage q).app
        ((smallEtaleInverseImage V.hom).obj F) (etaleSectionLift F V s) := by
  dsimp only
  let W := (smallEtaleBaseChange f).obj V
  let p := pullback.snd V.hom f
  let q := pullback.fst V.hom f
  let H := (smallEtaleInverseImage f).obj F
  let G := (smallEtaleInverseImage V.hom).obj F
  let ep := (smallEtaleInverseImageCompIso p f).app F
  let ec := eqToIso (congrArg (fun morphism ↦
    (smallEtaleInverseImage.{u, v} morphism).obj F)
      (pullback.condition (f := V.hom) (g := f)).symm)
  let eQ := (smallEtaleInverseImageCompIso q V.hom).app F
  let e := ep ≪≫ ec ≪≫ eQ.symm
  let x := etaleSectionLift H W (smallEtaleUnitApp f F V s)
  let y := etaleSectionLift F V s
  have key : (Sheaf.Γ _ _).map ec.hom ((Sheaf.Γ _ _).map ep.hom x) =
      (Sheaf.Γ _ _).map eQ.hom
        ((globalSectionsSmallEtaleInverseImage q).app G y) :=
    etaleSectionLift_pullback_aux f F V s
  have hcomp : e.hom ≫ eQ.hom = ep.hom ≫ ec.hom := by
    change (ep.hom ≫ ec.hom ≫ eQ.inv) ≫ eQ.hom = ep.hom ≫ ec.hom
    rw [Category.assoc, Category.assoc, eQ.inv_hom_id, Category.comp_id]
  have hmapcomp : (Sheaf.Γ _ _).map e.hom ≫ (Sheaf.Γ _ _).map eQ.hom =
      (Sheaf.Γ _ _).map ep.hom ≫ (Sheaf.Γ _ _).map ec.hom := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomp]
  have hcancel : (Sheaf.Γ _ _).map eQ.hom ((Sheaf.Γ _ _).map e.hom x) =
      (Sheaf.Γ _ _).map ec.hom ((Sheaf.Γ _ _).map ep.hom x) :=
    ((CategoryTheory.comp_apply ((Sheaf.Γ _ _).map e.hom)
          ((Sheaf.Γ _ _).map eQ.hom) x).symm.trans
        (ConcreteCategory.congr_hom hmapcomp x)).trans
      (CategoryTheory.comp_apply ((Sheaf.Γ _ _).map ep.hom)
        ((Sheaf.Γ _ _).map ec.hom) x)
  apply (CategoryTheory.mono_iff_injective
    ((Sheaf.Γ _ _).map eQ.hom)).mp inferInstance
  exact hcancel.trans key

private lemma smallEtaleSection_eq_of_germs
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (U : S.Etale) (s t : F.obj.obj (Opposite.op U))
    (heq : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ S) (a : (pointSmallEtale x).fiber.obj U),
      (pointSmallEtale x).toPresheafFiber U a F.obj s =
        (pointSmallEtale x).toPresheafFiber U a F.obj t) : s = t := by
  have hcover : Presheaf.equalizerSieve (F := F.obj) s t ∈ S.smallEtaleTopology U := by
    apply sieve_mem_smallEtaleTopology_of_geometricPoints U _
    intro Ω _ _ x a
    obtain ⟨V, morphism, b, hb, hst⟩ :=
      ((pointSmallEtale x).toPresheafFiber_eq_iff' (P := F.obj) U a s t).mp (heq Ω x a)
    exact ⟨V, morphism, hst, b, hb⟩
  exact ((isSheaf_iff_isSheaf_of_type _ F.obj).mp F.property).isSeparated
    _ hcover |>.ext (fun _ _ h ↦ h)

private lemma globalSectionsEqOpen_map_iso
    {S : Scheme.{u}} {F G : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))}
    (e : F ≅ G) (s t : (Sheaf.Γ _ _).obj F) :
    globalSectionsEqOpen G ((Sheaf.Γ _ _).map e.hom s)
      ((Sheaf.Γ _ _).map e.hom t) = globalSectionsEqOpen F s t := by
  ext y
  rw [← geometricPointAt_apply y]
  refine (mem_globalSectionsEqOpen_iff (geometricPointAt y) G _ _).trans
    (Iff.trans ?_ (mem_globalSectionsEqOpen_iff (geometricPointAt y) F s t).symm)
  have hs := ConcreteCategory.congr_hom
    (globalSectionGerm_naturality (geometricPointAt y) e.hom) s
  have ht := ConcreteCategory.congr_hom
    (globalSectionGerm_naturality (geometricPointAt y) e.hom) t
  simp only [types_comp_apply] at hs ht
  rw [hs, ht]
  exact ((pointSmallEtale (geometricPointAt y)).sheafFiber.mapIso e).toEquiv.injective.eq_iff

/-- A germ of a section along `homMk point hover` equals the germ of a global section at `base`
exactly when the same holds with `base` replaced by `point ≫ U.hom`. -/
private lemma toPresheafFiber_homMk_eq_germ_iff
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale)
    (s : F.obj.obj (Opposite.op U)) (t : (Sheaf.Γ _ _).obj F)
    (point : Spec (.of Ω) ⟶ U.left) (base : Spec (.of Ω) ⟶ S) (hover : point ≫ U.hom = base) :
    (pointSmallEtale base).toPresheafFiber U (Over.homMk point hover) F.obj s =
        globalSectionGerm base F t ↔
      (pointSmallEtale (point ≫ U.hom)).toPresheafFiber U
        (Over.homMk point rfl) F.obj s = globalSectionGerm (point ≫ U.hom) F t := by
  cases hover
  exact Iff.rfl

private lemma smallEtaleSection_restrict_eq_of_image_subset_eqOpen
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    {U V : S.Etale} (morphism : V ⟶ U)
    (s : F.obj.obj (Opposite.op U)) (t : (Sheaf.Γ _ _).obj F)
    (himage : ∀ y : V.left, morphism.left y ∈ globalSectionsEqOpen
      ((smallEtaleInverseImage U.hom).obj F)
      (etaleSectionLift F U s)
      ((globalSectionsSmallEtaleInverseImage U.hom).app F t)) :
    F.obj.map morphism.op s = F.ΓRes (Opposite.op V) t := by
  apply smallEtaleSection_eq_of_germs F V
  intro Ω _ _ x a
  have hmem := himage (a.left (default : Spec (.of Ω)))
  have hg := (mem_globalSectionsEqOpen_iff (a.left ≫ morphism.left)
    ((smallEtaleInverseImage U.hom).obj F)
      (etaleSectionLift F U s)
      ((globalSectionsSmallEtaleInverseImage U.hom).app F t)).mp
        (by exact hmem)
  have h := congrArg ((smallEtalePullbackStalkIso U.hom
    (a.left ≫ morphism.left)).hom.app F) hg
  rw [etaleSectionLift_germ] at h
  have hp := ConcreteCategory.congr_hom
    (globalSectionGerm_pullback U.hom (a.left ≫ morphism.left) F) t
  simp only [types_comp_apply] at hp
  have h := h.trans hp
  have hover : (a.left ≫ morphism.left) ≫ U.hom = x :=
    (Category.assoc a.left morphism.left U.hom).trans
      ((congrArg (a.left ≫ ·) (MorphismProperty.Over.w morphism)).trans (Over.w a))
  let b : (pointSmallEtale x).fiber.obj U := Over.homMk
    (a.left ≫ morphism.left) hover
  have hleft : (pointSmallEtale x).toPresheafFiber V a F.obj
      (F.obj.map morphism.op s) =
        (pointSmallEtale x).toPresheafFiber U b F.obj s := by
    have hw := (pointSmallEtale x).toPresheafFiber_w_apply morphism a F.obj s
    have hb : (pointSmallEtale x).fiber.map morphism a = b := by
      apply Over.OverMorphism.ext
      rfl
    rwa [hb] at hw
  rw [hleft]
  have hright : globalSectionGerm x F t =
      (pointSmallEtale x).toPresheafFiber V a F.obj (F.ΓRes (Opposite.op V) t) :=
    ConcreteCategory.congr_hom (globalSectionGerm_eq x F V a) t
  apply Eq.trans (b := globalSectionGerm x F t) ?_ hright
  exact (toPresheafFiber_homMk_eq_germ_iff F U s t _ x hover).mpr h

private lemma smallEtaleInverseImageUnit_injective
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyConnected f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (V : S.Etale) :
    Function.Injective
      ((((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
        (Opposite.op V))) := by
  intro first second equality
  let q := pullback.fst V.hom f
  apply (etaleSectionLift F V).injective
  apply globalSectionsComparison_injective q (pullback.fst V.hom f).surjective
    ((smallEtaleInverseImage V.hom).obj F)
  rw [← etaleSectionLift_pullback f F V first,
    ← etaleSectionLift_pullback f F V second, equality]

private lemma mem_globalSectionsEqOpen_etaleSectionLift
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (U : S.Etale) (s : F.obj.obj (Opposite.op U)) (t : (Sheaf.Γ _ _).obj F)
    (x : Spec (.of Ω) ⟶ S) (a : (pointSmallEtale x).fiber.obj U)
    (heq : (pointSmallEtale x).toPresheafFiber U a F.obj s = globalSectionGerm x F t) :
    a.left (default : Spec (.of Ω)) ∈ globalSectionsEqOpen
      ((smallEtaleInverseImage U.hom).obj F) (etaleSectionLift F U s)
      ((globalSectionsSmallEtaleInverseImage U.hom).app F t) := by
  apply (mem_globalSectionsEqOpen_iff a.left _ _ _).mpr
  apply ((smallEtalePullbackStalkIso U.hom a.left).app F).toEquiv.injective
  change (smallEtalePullbackStalkIso U.hom a.left).hom.app F
      (globalSectionGerm a.left ((smallEtaleInverseImage U.hom).obj F)
        (etaleSectionLift F U s)) =
    (smallEtalePullbackStalkIso U.hom a.left).hom.app F
      (globalSectionGerm a.left ((smallEtaleInverseImage U.hom).obj F)
        ((globalSectionsSmallEtaleInverseImage U.hom).app F t))
  have hp := ConcreteCategory.congr_hom (globalSectionGerm_pullback U.hom a.left F) t
  simp only [types_comp_apply] at hp
  exact (etaleSectionLift_germ F U a.left s).trans
    (((toPresheafFiber_homMk_eq_germ_iff F U s t a.left x (Over.w a)).mp heq).trans hp.symm)

private lemma exists_smallEtaleInverseImage_local_lift
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsub : IsQuotientMapEtaleBaseChange f) [GeometricallyConnected f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (t : (Sheaf.Γ _ _).obj ((smallEtaleInverseImage f).obj F))
    (x : X) :
    ∃ (V : S.Etale) (s : F.obj.obj (Opposite.op V)),
      f x ∈ Set.range V.hom ∧
      (((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
        (Opposite.op V)) s =
        ((smallEtaleInverseImage f).obj F).ΓRes
          (Opposite.op ((smallEtaleBaseChange f).obj V)) t := by
  let point := geometricPointAt x
  let H := (smallEtaleInverseImage f).obj F
  obtain ⟨V, a, s, hs⟩ := exists_smallEtaleInverseImage_germ_representative f point F t
  let W := (smallEtaleBaseChange f).obj V
  let p := pullback.snd V.hom f
  let q := pullback.fst V.hom f
  let G := (smallEtaleInverseImage V.hom).obj F
  let e := (smallEtaleInverseImageCompIso p f).app F ≪≫
    eqToIso (congrArg (fun morphism ↦
      (smallEtaleInverseImage.{u, v} morphism).obj F)
        pullback.condition.symm) ≪≫
    ((smallEtaleInverseImageCompIso q V.hom).app F).symm
  let first := etaleSectionLift H W
    ((((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
      (Opposite.op V)) s)
  let second := (globalSectionsSmallEtaleInverseImage p).app H t
  let second' := (Sheaf.Γ _ _).map e.hom second
  have hfirst : (Sheaf.Γ _ _).map e.hom first =
      (globalSectionsSmallEtaleInverseImage q).app G
        (etaleSectionLift F V s) := etaleSectionLift_pullback f F V s
  obtain ⟨A, hA⟩ := globalSectionsEqOpen_inverseImage_descends q (hsub V) G
    ((globalSectionsSmallEtaleInverseImage q).app G
      (etaleSectionLift F V s)) second'
  have hA' : q ⁻¹' A.1 =
      (globalSectionsEqOpen ((smallEtaleInverseImage p).obj H)
        first second).1 := by
    have hopen : globalSectionsEqOpen ((smallEtaleInverseImage q).obj G)
          ((globalSectionsSmallEtaleInverseImage q).app G (etaleSectionLift F V s)) second' =
        globalSectionsEqOpen ((smallEtaleInverseImage p).obj H) first second := by
      rw [← hfirst]
      exact globalSectionsEqOpen_map_iso e first second
    rwa [hopen] at hA
  let b := (smallEtaleBaseChangeFiberIso f point).inv.app V a
  have hmem : b.left (default : Spec (.of (SeparableClosure (X.residueField x)))) ∈
      globalSectionsEqOpen ((smallEtaleInverseImage p).obj H) first second :=
    mem_globalSectionsEqOpen_etaleSectionLift H W _ t point b hs.symm
  have hbA : q (b.left (default : Spec (.of (SeparableClosure (X.residueField x))))) ∈ A := by
    change b.left (default : Spec (.of (SeparableClosure (X.residueField x)))) ∈
      q ⁻¹' A.1
    rwa [hA']
  let V' : S.Etale := MorphismProperty.Over.mk ⊤ (A.ι ≫ V.hom) inferInstance
  let restriction : V' ⟶ V := MorphismProperty.Over.homMk A.ι rfl
  let W' := (smallEtaleBaseChange f).obj V'
  let restriction' : W' ⟶ W := (smallEtaleBaseChange f).map restriction
  refine ⟨V', F.obj.map restriction.op s, ?_, ?_⟩
  · refine ⟨⟨q (b.left (default : Spec (.of (SeparableClosure (X.residueField x))))), hbA⟩, ?_⟩
    change V.hom (q (b.left (default : Spec (.of (SeparableClosure
      (X.residueField x)))))) = f x
    have hover : b.left ≫ q ≫ V.hom = point ≫ f :=
      (Category.assoc b.left (pullback.fst V.hom f) V.hom).symm.trans
        (pullback_fst_comp_eq f point V.hom b.left (Over.w b))
    have heq := congrArg (fun morphism : Spec (.of (SeparableClosure
        (X.residueField x))) ⟶ S ↦ morphism default) hover
    simp only [Functor.fromPUnit, Functor.const_obj_obj, Scheme.Hom.comp_apply, point,
      geometricPointAt_apply] at heq ⊢
    exact heq
  · have heq := smallEtaleSection_restrict_eq_of_image_subset_eqOpen H
        restriction'
        ((((smallEtaleInverseImageAdjunction f).unit.app F).hom.app
          (Opposite.op V)) s) t (fun y ↦ ?_)
    · refine Eq.trans ?_ heq
      exact ConcreteCategory.congr_hom (smallEtaleUnitApp_naturality_obj f F restriction) s
    · change restriction'.left y ∈ globalSectionsEqOpen
        ((smallEtaleInverseImage p).obj H) first second
      apply (Set.ext_iff.mp hA' (restriction'.left y)).mp
      have hq := smallEtaleBaseChange_map_fst f restriction
      have hq' := congrArg (fun morphism : W'.left ⟶ V.left ↦ morphism y) hq
      change q (restriction'.left y) =
        A.ι ((pullback.fst V'.hom f) y) at hq'
      exact (congrArg (fun point : V.left ↦ point ∈ A.1) hq').mpr
        ((pullback.fst V'.hom f) y).property

private lemma exists_preimage_of_imageSieve_mem
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type v)} (morphism : F ⟶ G)
    (hinj : ∀ U, Function.Injective (morphism.hom.app U))
    (U : C) (target : G.obj.obj (Opposite.op U))
    (hcover : Presheaf.imageSieve morphism.hom target ∈ J U) :
    ∃ preimage, morphism.hom.app (Opposite.op U) preimage = target := by
  let covering := Presheaf.imageSieve morphism.hom target
  let family : Presieve.FamilyOfElements F.obj covering.arrows :=
    fun _ _ witness ↦ witness.choose
  have hfamily : family.Compatible := by
    apply (Presieve.compatible_iff_sieveCompatible family).mpr
    intro V W restriction further witness
    apply hinj (Opposite.op W)
    change morphism.hom.app _ (covering.downward_closed witness further).choose = _
    rw [(covering.downward_closed witness further).choose_spec, NatTrans.naturality_apply,
      witness.choose_spec]
    simp only [op_comp, Functor.map_comp, types_comp_apply]
  let sheaf := ((isSheaf_iff_isSheaf_of_type _ F.obj).mp F.property) covering hcover
  obtain ⟨preimage, hpreimage, _⟩ := sheaf family hfamily
  refine ⟨preimage, ?_⟩
  apply (((isSheaf_iff_isSheaf_of_type _ G.obj).mp G.property).isSeparated
    covering hcover).ext
  intro V restriction witness
  rw [← NatTrans.naturality_apply, hpreimage restriction witness]
  exact witness.choose_spec

private lemma globalSectionsComparison_surjective
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsub : IsQuotientMapEtaleBaseChange f) [GeometricallyConnected f]
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
    Function.Surjective ((globalSectionsSmallEtaleInverseImage f).app F) := by
  intro t
  let H := (smallEtaleInverseImage f).obj F
  let unit := (smallEtaleInverseImageAdjunction f).unit.app F
  let U := smallEtaleFinal S
  let target := H.ΓRes (Opposite.op ((smallEtaleBaseChange f).obj U)) t
  have hcover : Presheaf.imageSieve unit.hom target ∈ S.smallEtaleTopology U := by
    apply sieve_mem_smallEtaleTopology_of_geometricPoints U _
    intro Ω _ _ point a
    obtain ⟨x, hx⟩ := f.surjective (point default)
    obtain ⟨V, s, hpoint, hs⟩ := exists_smallEtaleInverseImage_local_lift f hsub F t x
    rw [hx] at hpoint
    obtain ⟨y, hy⟩ := hpoint
    obtain ⟨lift, hlift, _⟩ := exists_fac_of_etale_of_isSepClosed V.hom point y hy
    let restriction := smallEtaleToFinal V
    let b : (pointSmallEtale point).fiber.obj V := Over.homMk lift hlift
    refine ⟨V, restriction, ?_, b, ?_⟩
    · refine ⟨s, ?_⟩
      change unit.hom.app (Opposite.op V) s = H.obj.map
        ((smallEtaleBaseChange f).map restriction).op
          (H.ΓRes (Opposite.op ((smallEtaleBaseChange f).obj U)) t)
      rw [hs]
      exact (ConcreteCategory.congr_hom
        (H.ΓRes_map ((smallEtaleBaseChange f).map restriction).op) t).symm
    · apply Over.OverMorphism.ext
      change lift ≫ V.hom = a.left
      exact hlift.trans (by simpa [U, smallEtaleFinal] using (Over.w a).symm)
  obtain ⟨s, hs⟩ := exists_preimage_of_imageSieve_mem unit
    (fun V ↦ smallEtaleInverseImageUnit_injective f F V.unop) U target hcover
  have := globalSections_res_final_isIso F
  let global := inv (F.ΓRes (Opposite.op U)) s
  have hglobal : F.ΓRes (Opposite.op U) global = s :=
    ConcreteCategory.congr_hom (IsIso.inv_hom_id (F.ΓRes (Opposite.op U))) s
  refine ⟨global, ?_⟩
  have : IsIso (H.ΓRes (Opposite.op ((smallEtaleBaseChange f).obj U))) :=
    globalSections_res_isIso_of_isTerminal H (baseChangeTerminal f)
  apply (CategoryTheory.mono_iff_injective
    (H.ΓRes (Opposite.op ((smallEtaleBaseChange f).obj U)))).mp inferInstance
  have hcomparison := ConcreteCategory.congr_hom (globalSectionsComparison_ΓRes f F U) global
  simp only [types_comp_apply] at hcomparison
  refine hcomparison.trans ?_
  rwa [hglobal]

/-- **Stacks Project, Tag 0EZK.** For `f` universally submersive with geometrically connected
fibres, the *canonical* comparison `Γ(S, F) ⟶ Γ(X, f⁻¹F)` is an isomorphism, naturally in the
sheaf `F`. This is the form in which the source asserts the tag — it says "there is a canonical
map `Γ(S, F) → Γ(X, f⁻¹F)`" and then that it is injective and surjective — and it is strictly
stronger than the bare existence of an isomorphism of global-sections functors, which would not
say that the isomorphism is restriction of sections.

**Stacks erratum.** The hypothesis stated here is the corrected one;
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso` carries the characteristic-`2`
counterexample to the tag as the source writes it. -/
@[stacks 0EZK "corrected: Stacks erratum. The tag in the form the \
source asserts it, about the canonical comparison rather than a bare isomorphism of \
global-sections functors. The tag is false with only `f` submersive; see the counterexample in \
the docstring of globalSectionsSmallEtaleInverseImageIso"]
public theorem isIso_globalSectionsSmallEtaleInverseImage
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsub : (topologically @Topology.IsQuotientMap :
      MorphismProperty Scheme.{u}).universally f)
    [GeometricallyConnected f] :
    IsIso (globalSectionsSmallEtaleInverseImage.{u, v} f) := by
  have hbij (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
      Function.Bijective ((globalSectionsSmallEtaleInverseImage f).app F) :=
    ⟨globalSectionsComparison_injective f f.surjective F,
      globalSectionsComparison_surjective f
        (isQuotientMapEtaleBaseChange_of_universallySubmersive f hsub) F⟩
  let (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) :
      IsIso ((globalSectionsSmallEtaleInverseImage f).app F) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij F)
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks Project, Tag 0EZK.** Pullback along a universally submersive morphism with
geometrically connected fibres preserves global sections of every sheaf of sets on the small
étale site, naturally in the sheaf. The isomorphism is the canonical comparison, which
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage` inverts.

**Stacks erratum.** The hypothesis stated here is the corrected
one. As the source writes the tag it asks only that `f` be submersive, and in that form the
statement is false: the proof reduces along an étale base change, and submersivity does not
survive one. The counterexample lives in characteristic `2`. Let `k` be a field of
characteristic `2`, let `A = {g ∈ k[t] ∣ g(0) = g(1)}` be the node — the affine line with the
two points `t = 0` and `t = 1` glued — let `B = k[t, 1/t]` be the affine line with `t = 0`
removed, and let `f : Spec B ⟶ Spec A` be the homeomorphism described in the Stacks proof: it
is bijective because the node has already glued the removed point `t = 0` to the surviving
point `t = 1`. Take `F = h_T`, the functor of points of `T = Spec A[z]/(z² + z + a)` with
`a = t² + t`, which is the connected étale double cover of `Spec A` — étale because the
derivative of `z² + z + a` in `z` is the unit `1` in characteristic `2`. Then `Γ(S, F)` is
EMPTY: a root of `z² + z + a` in `k[t]` is `t` or `t + 1`, and neither takes the same value at
`0` and at `1`, so neither lies in `A`. But `Γ(X, f⁻¹F)` has TWO elements, `t` and `t + 1`,
both of which lie in `B`. So the claimed bijection `Γ(S, F) = Γ(X, f⁻¹F)` cannot hold, and the
submersive hypothesis alone does not suffice. Universal submersivity — equivalently,
submersivity after every étale base change — is what the argument uses and what is assumed
here; it is part of the corrected statement, not a strengthening of it. -/
@[stacks 0EZK "corrected: Stacks erratum. The tag is false with \
only `f` submersive, since the proof's reduction is an etale base change and submersivity \
does not survive one; universal submersivity is assumed instead. Counterexample in \
characteristic 2: the homeomorphism Spec k[t,1/t] -> Spec {g : g(0) = g(1)} and the double \
cover T = Spec A[z]/(z^2 + z + a) with a = t^2 + t, for which the sections downstairs are \
empty while there are two upstairs; see this declaration's docstring"]
public def globalSectionsSmallEtaleInverseImageIso
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsub : (topologically @Topology.IsQuotientMap :
      MorphismProperty Scheme.{u}).universally f)
    [GeometricallyConnected f] :
    Sheaf.Γ (smallEtaleTopology S) (Type (max (u + 1) v)) ≅
      smallEtaleInverseImage f ⋙
        Sheaf.Γ (smallEtaleTopology X) (Type (max (u + 1) v)) :=
  let := isIso_globalSectionsSmallEtaleInverseImage.{u, v} f hsub
  asIso (globalSectionsSmallEtaleInverseImage f)

/-! ### Localizing the comparison to the small étale site of an object

Everything above compares *global* sections.  This section localizes that comparison: for a
morphism `a : U ⟶ V ×_S X` of the small étale site of `X` whose induced morphism `k : U ⟶ V` is
universally submersive with geometrically connected fibres, the canonical comparison
`G(V) ⟶ (f⁻¹G)(U)` of `Stacks.EtaleCohomology.smallEtaleInverseImageSections` is bijective.

The reduction to the global statement is the small-étale instance of the compatibility of inverse
image with localization, and it is carried out through the sections comparison itself rather than
through an equivalence of the small étale site of `U.left` with a slice of `X_étale`.  Three facts
do the work, and all three are about `smallEtaleInverseImageSections`:

* it *composes*, which is `smallEtaleInverseImageSections_comp` above: the comparison attached to
  a composite `U.left ⟶ X ⟶ S` is the composite of the two comparisons, read through
  `smallEtaleInverseImageCompIso`;
* at the *diagonal of an étale object* it is invertible,
  `isIso_smallEtaleInverseImageSections_etaleDiagonal`, because inverse image along an étale
  morphism is restriction, so the comparison there is `etaleSectionLift`;
* at the *final objects* it is invertible as soon as the global comparison is,
  `isIso_smallEtaleInverseImageSections_final`, because global sections are the sections at the
  final object.

The two factorizations `U.left ⟶ X ⟶ S` and `U.left ⟶ V.left ⟶ S` of the structure morphism of
`U` then give two decompositions of one and the same comparison, the one over the final object of
the small étale site of `U.left`.  In the second all three factors are invertible, by the last two
facts applied to `k`; in the first every factor except the wanted one is.  That the two
decompositions compute the same comparison is `hom_ext_baseChange` below: a morphism of the small
étale site into a base change `V ×_S U.left` is determined by its projection to `V`, and both
decompositions project to `k`.
-/

section LocalizedSections

/-- A component of an isomorphism of sheaves is invertible. -/
private lemma isIso_hom_app_of_sheafIso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {A : Type*} [Category* A] {F G : Sheaf J A} (e : F ≅ G) (X : Cᵒᵖ) :
    IsIso (e.hom.hom.app X) :=
  let : IsIso e.hom.hom := (ObjectProperty.isIso_hom_iff _).mpr inferInstance
  inferInstance

/-- A morphism equal to a composite of two isomorphisms is an isomorphism. -/
private lemma isIso_of_eq_comp {C : Type*} [Category* C] {A B D : C}
    (x : A ⟶ B) (y : B ⟶ D) (z : A ⟶ D) [IsIso x] [IsIso y] (h : x ≫ y = z) : IsIso z :=
  h ▸ inferInstance

/-- Transport of invertibility of the sections comparison along an equality of the morphisms it
is taken along. -/
private lemma isIso_sections_transport {X S : Scheme.{u}} {m m' : X ⟶ S} (h : m = m')
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale}
    (x : U ⟶ (smallEtaleBaseChange m).obj V)
    (y : U ⟶ (smallEtaleBaseChange m').obj V)
    (hxy : x ≫ (eqToIso (congrArg (fun morphism ↦
      (smallEtaleBaseChange morphism).obj V) h)).hom = y)
    (hx : IsIso (smallEtaleInverseImageSections.{u, v} m F x)) :
    IsIso (smallEtaleInverseImageSections.{u, v} m' F y) := by
  cases h
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id] at hxy
  subst hxy
  exact hx

/-- Cancellation of an invertible right factor: if `x ≫ y = z` with `y` and `z` invertible, then
`x` is invertible. -/
private lemma isIso_of_comp_eq_of_isIso {C : Type*} [Category* C] {A B D : C}
    (x : A ⟶ B) (y : B ⟶ D) (z : A ⟶ D) [IsIso y] [IsIso z] (h : x ≫ y = z) : IsIso x :=
  let : IsIso (x ≫ y) := h ▸ ‹IsIso z›
  (isIso_comp_right_iff x y).mp inferInstance

/-- A threefold composite of morphisms of schemes whose first two factors compose to `ρ` and whose
last factor is an identity is `ρ`. -/
private lemma comp_comp_eq_of_comp_eq_id {A B D : Scheme.{u}} (ι : A ⟶ B) (κ : B ⟶ D)
    (μ : D ⟶ D) (ρ : A ⟶ D) (hμ : μ = 𝟙 D) (h : ι ≫ κ = ρ) : ι ≫ κ ≫ μ = ρ := by
  rw [hμ, Category.comp_id, h]

/-- A projection that factors through a one-sided inverse, for bare morphisms of schemes. -/
private lemma comp_eq_of_comp_eq_id {A B D : Scheme.{u}} (ι : A ⟶ B) (σ : B ⟶ A) (κ : A ⟶ D)
    (π : B ⟶ D) (hπ : π = σ ≫ κ) (hσ : ι ≫ σ = 𝟙 A) : ι ≫ π = κ := by
  rw [hπ, ← Category.assoc, hσ, Category.id_comp]

/-- A morphism of the small étale site into a base change `V ×_S X` is determined by the
projection of its underlying morphism of schemes to `V`: the projection to `X` is forced, being
the structure morphism of the source. -/
private lemma hom_ext_baseChange {X S : Scheme.{u}} (m : X ⟶ S) {U : X.Etale} {V : S.Etale}
    (x y : U ⟶ (smallEtaleBaseChange m).obj V)
    (h : x.left ≫ pullback.fst V.hom m = y.left ≫ pullback.fst V.hom m) : x = y := by
  refine MorphismProperty.Over.Hom.ext (pullback.hom_ext h ?_)
  have hx : x.left ≫ pullback.snd V.hom m = U.hom := MorphismProperty.Over.w x
  have hy : y.left ≫ pullback.snd V.hom m = U.hom := MorphismProperty.Over.w y
  exact hx.trans hy.symm

/-- The inverse of the composition isomorphism for base change, followed by the projection to the
base.  The isomorphism is Mathlib's `CategoryTheory.MorphismProperty.Over.pullbackComp`, of which
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp` is the instance at the étale morphisms. -/
private alias baseChangeComp_inv_app_left_fst :=
  Stacks.EtaleCohomology.smallEtaleBaseChangeComp_inv_app_left_fst

/-- The morphism of the small étale site produced by `smallEtaleInverseImageSections_comp`, read
on the projection to the base: it projects to the composite of the projections of its two
factors. -/
private alias sectionsCompMor_left_fst := smallEtaleBaseChangeComposite_fst

/-- The diagonal of an étale object projects to the identity. -/
private lemma etaleDiagonal_left_fst {S : Scheme.{u}} (U : S.Etale) :
    (etaleDiagonal U).left ≫ pullback.fst U.hom U.hom = 𝟙 U.left :=
  pullback.lift_fst _ _ _

/-- A morphism of the small étale site of `U'` from the final object to the base change along
`k : U' ⟶ V'` of the final object of the small étale site of `V'` projects to `k` itself. -/
private lemma finalToBaseChange_left_fst {U' V' : Scheme.{u}} (k : U' ⟶ V')
    (c : smallEtaleFinal U' ⟶ (smallEtaleBaseChange k).obj (smallEtaleFinal V')) :
    c.left ≫ pullback.fst (smallEtaleFinal V').hom k = k := by
  have hc : c.left ≫ pullback.snd (smallEtaleFinal V').hom k = 𝟙 U' :=
    MorphismProperty.Over.w c
  have hcond : pullback.fst (smallEtaleFinal V').hom k ≫ (smallEtaleFinal V').hom =
      pullback.snd (smallEtaleFinal V').hom k ≫ k := pullback.condition
  have hpi : pullback.fst (smallEtaleFinal V').hom k =
      pullback.snd (smallEtaleFinal V').hom k ≫ k :=
    (Category.comp_id (pullback.fst (smallEtaleFinal V').hom k)).symm.trans hcond
  exact comp_eq_of_comp_eq_id c.left _ k _ hpi hc

/-- **At the diagonal of an étale object the sections comparison is invertible.**  For
`U : S.Etale` the canonical morphism of the small étale site of `U.left` from the final object to
`U ×_S U` makes the comparison `F(U) ⟶ (U.hom⁻¹F)(U.left)` the identification of the sections of
`F` over `U` with the global sections of its restriction to the small étale site of `U.left`,
which is `Stacks.EtaleCohomology.etaleSectionLift`. -/
private lemma isIso_smallEtaleInverseImageSections_etaleDiagonal
    {S : Scheme.{u}} (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v))) (U : S.Etale) :
    IsIso (smallEtaleInverseImageSections.{u, v} U.hom F (etaleDiagonal U)) := by
  rw [CategoryTheory.isIso_iff_bijective]
  have hres : Function.Bijective (((smallEtaleInverseImage U.hom).obj F).ΓRes
      (Opposite.op (smallEtaleFinal U.left))) :=
    (CategoryTheory.isIso_iff_bijective _).mp (globalSections_res_final_isIso _)
  have heq : smallEtaleInverseImageSections.{u, v} U.hom F (etaleDiagonal U) =
      ((smallEtaleInverseImage U.hom).obj F).ΓRes
        (Opposite.op (smallEtaleFinal U.left)) ∘ (etaleSectionLift F U) :=
    funext fun s ↦ (etaleSectionLift_diagonal F U s).symm
  rw [heq]
  exact hres.comp (etaleSectionLift F U).bijective

/-- **At the final objects the sections comparison is invertible as soon as the global comparison
is.**  Global sections of a sheaf on a small étale site are its sections at the final object, so
the comparison at a morphism between the final objects is the global comparison read through those
two identifications. -/
private lemma isIso_smallEtaleInverseImageSections_final
    {U' V' : Scheme.{u}} (k : U' ⟶ V')
    (hk : IsIso (globalSectionsSmallEtaleInverseImage.{u, v} k))
    (H : Sheaf V'.smallEtaleTopology (Type (max (u + 1) v)))
    (c : smallEtaleFinal U' ⟶ (smallEtaleBaseChange k).obj (smallEtaleFinal V')) :
    IsIso (smallEtaleInverseImageSections.{u, v} k H c) := by
  let := hk
  let := globalSections_res_final_isIso ((smallEtaleInverseImage.{u, v} k).obj H)
  let := globalSections_res_final_isIso H
  have hcomp : IsIso (H.ΓRes (Opposite.op (smallEtaleFinal V')) ≫
      smallEtaleInverseImageSections.{u, v} k H c) := by
    rw [← globalSectionsSmallEtaleInverseImage_app_ΓRes k H c]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hcomp

/-- **The two readings agree.** The morphism of the small étale site of `U.left` obtained by
reading the comparison over `U` through `X` is the one obtained by reading it through `V.left`,
transported along the equality of the two factorizations.  Both project to `k`, and a morphism
into a base change is determined by its projection. -/
private lemma routeMor_eq {X S : Scheme.{u}} (f : X ⟶ S)
    {U : X.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (k : U.left ⟶ V.left) (hkeq : a.left ≫ pullback.fst V.hom f = k)
    (hfac : k ≫ V.hom = U.hom ≫ f) :
    (etaleDiagonal U ≫ (smallEtaleBaseChange U.hom).map a ≫
        (smallEtaleBaseChangeComp U.hom f).inv.app V) =
      ((baseChangeTerminal k).from (smallEtaleFinal U.left) ≫
          (smallEtaleBaseChange k).map (etaleDiagonal V) ≫
          (smallEtaleBaseChangeComp k V.hom).inv.app V) ≫
        (eqToIso (congrArg (fun morphism ↦
          (smallEtaleBaseChange morphism).obj V) hfac)).hom := by
  have hLHS : (etaleDiagonal U ≫ (smallEtaleBaseChange U.hom).map a ≫
      (smallEtaleBaseChangeComp U.hom f).inv.app V).left ≫
        pullback.fst V.hom (U.hom ≫ f) = k := by
    rw [sectionsCompMor_left_fst U.hom f a (etaleDiagonal U), hkeq]
    exact comp_eq_of_inv_comp (etaleDiagonal U).left (pullback.fst U.hom U.hom) _ k rfl
      (etaleDiagonal_left_fst U)
  have hRHS : (((baseChangeTerminal k).from (smallEtaleFinal U.left) ≫
        (smallEtaleBaseChange k).map (etaleDiagonal V) ≫
        (smallEtaleBaseChangeComp k V.hom).inv.app V) ≫
      (eqToIso (congrArg (fun morphism ↦
        (smallEtaleBaseChange morphism).obj V) hfac)).hom).left ≫
        pullback.fst V.hom (U.hom ≫ f) = k := by
    refine Eq.trans (comp_comp_eq
      ((baseChangeTerminal k).from (smallEtaleFinal U.left) ≫
        (smallEtaleBaseChange k).map (etaleDiagonal V) ≫
        (smallEtaleBaseChangeComp k V.hom).inv.app V).left
      (eqToIso (congrArg (fun morphism ↦
        (smallEtaleBaseChange morphism).obj V) hfac)).hom.left
      (pullback.fst V.hom (U.hom ≫ f)) (pullback.fst V.hom (k ≫ V.hom))
      (smallEtaleBaseChange_congr_fst hfac V)) ?_
    rw [sectionsCompMor_left_fst k V.hom (etaleDiagonal V)
      ((baseChangeTerminal k).from (smallEtaleFinal U.left))]
    exact comp_comp_eq_of_comp_eq_id
      ((baseChangeTerminal k).from (smallEtaleFinal U.left)).left _ _ k
      (etaleDiagonal_left_fst V) (finalToBaseChange_left_fst k _)
  exact hom_ext_baseChange (U.hom ≫ f) _ _ (hLHS.trans hRHS.symm)

/-- **The reading through `V.left` is invertible.** All three of its factors are: the two outer
ones by `isIso_smallEtaleInverseImageSections_etaleDiagonal` and
`isIso_smallEtaleInverseImageSections_final`, the inner one being a component of
`smallEtaleInverseImageCompIso`. -/
private lemma isIso_routeVMor_sections {S U' : Scheme.{u}}
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) {V : S.Etale} (k : U' ⟶ V.left)
    (hk : IsIso (globalSectionsSmallEtaleInverseImage.{u, v} k)) :
    IsIso (smallEtaleInverseImageSections.{u, v} (k ≫ V.hom) G
      ((baseChangeTerminal k).from (smallEtaleFinal U') ≫
        (smallEtaleBaseChange k).map (etaleDiagonal V) ≫
        (smallEtaleBaseChangeComp k V.hom).inv.app V)) := by
  let := isIso_smallEtaleInverseImageSections_etaleDiagonal.{u, v} G V
  let := isIso_smallEtaleInverseImageSections_final.{u, v} k hk
    ((smallEtaleInverseImage.{u, v} V.hom).obj G)
    ((baseChangeTerminal k).from (smallEtaleFinal U'))
  let := isIso_hom_app_of_sheafIso ((smallEtaleInverseImageCompIso.{u, v} k V.hom).app G)
    (Opposite.op (smallEtaleFinal U'))
  rw [← smallEtaleInverseImageSections_comp.{u, v} k V.hom G (etaleDiagonal V)
    ((baseChangeTerminal k).from (smallEtaleFinal U'))]
  infer_instance

/-- **The reading through `X` is invertible**, being the reading through `V.left` transported
along the equality of the two factorizations. -/
private lemma isIso_routeXMor_sections {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (k : U.left ⟶ V.left) (hkeq : a.left ≫ pullback.fst V.hom f = k)
    (hfac : k ≫ V.hom = U.hom ≫ f)
    (hk : IsIso (globalSectionsSmallEtaleInverseImage.{u, v} k)) :
    IsIso (smallEtaleInverseImageSections.{u, v} (U.hom ≫ f) G
      (etaleDiagonal U ≫ (smallEtaleBaseChange U.hom).map a ≫
        (smallEtaleBaseChangeComp U.hom f).inv.app V)) :=
  isIso_sections_transport hfac G _ _ (routeMor_eq f a k hkeq hfac).symm
    (isIso_routeVMor_sections.{u, v} G k hk)

/-- The localized comparison is invertible as soon as the *global* comparison along the induced
morphism `k : U.left ⟶ V.left` is. -/
private lemma isIso_smallEtaleInverseImageSections_of_isIso_globalSections
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (k : U.left ⟶ V.left) (hkeq : a.left ≫ pullback.fst V.hom f = k)
    (hk : IsIso (globalSectionsSmallEtaleInverseImage.{u, v} k)) :
    IsIso (smallEtaleInverseImageSections.{u, v} f G a) := by
  have hfac : k ≫ V.hom = U.hom ≫ f :=
    hkeq ▸ pullback_fst_comp_eq f U.hom V.hom a.left (MorphismProperty.Over.w a)
  let := isIso_smallEtaleInverseImageSections_etaleDiagonal.{u, v}
    ((smallEtaleInverseImage.{u, v} f).obj G) U
  let := isIso_hom_app_of_sheafIso ((smallEtaleInverseImageCompIso.{u, v} U.hom f).app G)
    (Opposite.op (smallEtaleFinal U.left))
  let := isIso_routeXMor_sections.{u, v} f G a k hkeq hfac hk
  exact isIso_of_comp_eq_of_isIso _ _ _
    (smallEtaleInverseImageSections_comp.{u, v} U.hom f G a (etaleDiagonal U))

/-- **Tag 0A3H, in the localized form in which the base change results of Tags 0EYR, 0EZX, 0EYS
and 0EZZ use it.**  For every sheaf of sets `G` on the small étale site of `S` and every morphism
`a : U ⟶ V ×_S X` of the small étale site of `X` whose induced morphism `k : U ⟶ V` is universally
submersive with geometrically connected fibres, the canonical comparison `G(V) ⟶ (f⁻¹G)(U)` is
bijective.

The hypotheses are the ones Tag 0EZK is carried with, imposed on `k`, and nothing else: no
hypothesis on `f` itself is needed, all the geometry happening at `k`.  For `k` flat,
quasi-compact and with geometrically connected fibres they are supplied by
`Stacks.EtaleCohomology.universally_isQuotientMap_of_flat_quasiCompact`.

No tag attribute is placed here.  The carriers of Tag 0A3H in this library are
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage_of_flat_quasiCompact` and
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImageIso_of_flat_of_quasiCompact`, which
state the tag's own global form. -/
public theorem isIso_smallEtaleInverseImageSections
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)))
    {U : X.Etale} {V : S.Etale} (a : U ⟶ (smallEtaleBaseChange f).obj V)
    (hsub : (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally
      (a.left ≫ pullback.fst V.hom f))
    (hconn : GeometricallyConnected (a.left ≫ pullback.fst V.hom f)) :
    IsIso (smallEtaleInverseImageSections.{u, v} f G a) :=
  let := hconn
  isIso_smallEtaleInverseImageSections_of_isIso_globalSections.{u, v} f G a _ rfl
    (isIso_globalSectionsSmallEtaleInverseImage.{u, v} _ hsub)

end LocalizedSections

end Stacks.EtaleCohomology

end
