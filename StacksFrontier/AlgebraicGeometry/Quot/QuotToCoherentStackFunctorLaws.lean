module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStack

/-!
# The functor laws for the module comparisons of Stacks 0DP6

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
of finite presentation and let `F` be a quasi-coherent `𝒪_X`-module — the standing data
`AlgebraicGeometry.Space.QuotSituation` of Stacks 09TR.  Stacks 0DP6 records the morphism

`Quot_{F/X/B} ⟶ Coh_{X/B}`

which carries a quotient `F_T ⟶ 𝒬` of `Quot_{F/X/B}(T)` to the object `𝒬` of `Coh_{X/B}` over
`T`.  Its object and morphism assignments are
`AlgebraicGeometry.Space.QuotSituation.cohObject` and
`AlgebraicGeometry.Space.QuotSituation.cohHom` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotToCoherentStack.lean`; the module comparison a morphism
of `Coh_{X/B}` carries is the inverse of
`AlgebraicGeometry.Space.QuotientSituation.quotientPullbackCokernelIso`, the identification of
the quotient of `F_{T'}` by the pulled-back kernel with the inverse image of `F_T/K`.

This file proves the two functor laws for those module comparisons, against the unit and
composition comparisons out of which the identity and the composition of `Coh_{X/B}` are built
(`AlgebraicGeometry.Space.CoherentSituation.idComparison` and
`AlgebraicGeometry.Space.CoherentSituation.compComparison`).

## Main results

* `AlgebraicGeometry.Space.QuotSituation.quotientPullbackCokernelIso_hom_id`: **the unit law for
  the module comparison** — the comparison for the identity of a test scheme is the unit
  comparison of `Coh_{X/B}`, read through the identification of the quotient pulled back along
  the identity with the quotient itself.
* `AlgebraicGeometry.Space.QuotSituation.quotientPullbackCokernelIso_hom_comp`: **the
  composition law for the module comparison** — the comparison for a composite of morphisms of
  test schemes is the composite of the two comparisons along the composition comparison of
  `Coh_{X/B}`, read through the identification of the quotient pulled back along a composite
  with the iterated pullback.  This is the composite that
  `AlgebraicGeometry.Space.CoherentHom.comp` forms, so the two laws together say that the
  assignments of Stacks 0DP6 respect identities and composition.
* `AlgebraicGeometry.Space.QuotSituation.baseChangeComparison_id_idComparison` and
  `AlgebraicGeometry.Space.QuotSituation.baseChangeComparison_comp_compComparison`: the two
  coherences of `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison` re-expressed
  through the comparisons of `Coh_{X/B}`, which is what makes the two laws statable at them.
* `AlgebraicGeometry.Space.QuotSituation.quotientPullbackProjection_comp`: the cocycle identity
  for the projections `F_{T''} ⟶ (X_{T''} ⟶ X_T)^*(F_T/K)` onto the pulled-back quotients, which
  is the content of the composition law before the kernels are read off.
* `CategoryTheory.comp_assoc_of_eq` and
  `CategoryTheory.Functor.hom_app_of_eq_compWhisker`: the two pieces of general category theory
  the laws are factored through.

## Implementation notes

**Every statement is made either at the level of isomorphisms of functors or at a spelling the
proof produces verbatim.**  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCoherence.lean` record that the
kernel does not finish checking a proof of a statement that projects the underlying morphism of
a comparison of inverse images: those comparisons contain
`eqToIso (congrArg (AlgebraicGeometry.Space.modulePullback B S hS ·) h)` factors, and reducing
them forces `AlgebraicGeometry.Space.modulePullback` to be unfolded.  The same obstruction is
met here from a third side, and the two devices that avoid it are:

* the two coherences are transported to the comparisons of `Coh_{X/B}` as equalities of
  *isomorphisms of functors*, where the transport is immediate;
* each law is first proved with the comparison of `Coh_{X/B}` abstracted as a variable
  (`quotientPullbackCokernelIso_hom_id_of_factorization`,
  `quotientPullbackCokernelIso_hom_comp_of_factorization`) and then instantiated, so that the
  only comparison of two spellings is between the type of a variable and the type of the
  argument supplied for it.

For the same reason the composition law is proved by cancelling the projection
`F_{T''} ⟶ F_{T''}/(K pulled back along h ≫ k)`, which is an epimorphism, rather than by
specializing `CategoryTheory.Functor.conjSubobjectCokernelIso_comp`: that specialization does
not elaborate at `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison`, whereas every
step of the projection calculation is either an equality of morphisms out of `F_{T''}` or an
application of a general lemma about an abstract comparison.  The calculation is split across
`quotientPullbackProjection_comp`,
`quotientProjection_comp_quotientPullbackCokernelIso_hom_comp` and
`quotientPullbackCokernelIso_hom_comp_of_factorization` so that each declaration stays inside
the elaborator's budget.

The same discipline dictates which of the two spellings of a base-change map each statement
uses.  The Quot side speaks `AlgebraicGeometry.Space.QuotientSituation` and the `Coh_{X/B}` side
speaks `AlgebraicGeometry.Space.CoherentSituation`, so `(X_h)^*` has two names here; a statement
that mixes them in the argument of `CategoryTheory.Functor.map` is not checkable, while one that
mixes them only in the type of an isomorphism of functors is.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Reassociating a composite whose first two factors have a known composite. -/
theorem comp_assoc_of_eq {C : Type*} [Category* C] {A A' A'' A''' : C} {p : A ⟶ A'}
    {q : A' ⟶ A''} {p' : A ⟶ A''} (hp : p ≫ q = p') (r : A'' ⟶ A''') :
    p' ≫ r = p ≫ (q ≫ r) := by
  subst hp
  simp

end CategoryTheory

namespace CategoryTheory.Functor

/-- The component at `M` of a comparison which factors through two comparisons and an
identification `L ≅ L₁ ⋙ L₂`. -/
theorem hom_app_of_eq_compWhisker {C : Type*} {D₀ : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category* C] [Category* D₀] [Category* D₁] [Category* D₂]
    {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L₁ : D₀ ⥤ D₁} {L₂ : D₁ ⥤ D₂} {L : D₀ ⥤ D₂}
    (c₁ : P₁ ≅ P₀ ⋙ L₁) (c₂ : P₂ ≅ P₁ ⋙ L₂) (c : P₂ ≅ P₀ ⋙ L) (τ : L ≅ L₁ ⋙ L₂)
    (hfac : c = (c₂ ≪≫ isoWhiskerRight c₁ L₂ ≪≫ associator P₀ L₁ L₂) ≪≫
      (isoWhiskerLeft P₀ τ).symm) (M : C) :
    c.hom.app M = c₂.hom.app M ≫ L₂.map (c₁.hom.app M) ≫ τ.inv.app (P₀.obj M) := by
  subst hfac
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **The base-change comparison for the identity of a test scheme is the unit comparison of
`Coh_{X/B}`.**  `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison_id` writes that
comparison as whiskering `F_T`'s inverse image with the unit law `(X_{𝟙 T})^* ≅ 𝟭` of
Stacks 03LU; the unit comparison
`AlgebraicGeometry.Space.CoherentSituation.idComparison` of `Coh_{X/B}` is the inverse of that
unit law, so the two sides differ only by the direction in which the transport along
`X_{𝟙 T} = 𝟙 X_T` is written.

This is an equality of isomorphisms of functors, which is the only level at which such a
statement is tractable; see the implementation notes. -/
theorem baseChangeComparison_id_idComparison (hc : ModulePushforwardCoherence B S hS)
    (T : SchemesOver D.Y) :
    D.baseChangeComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (D.sourceProjection T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T))
          (D.toCoherentSituation.idComparison hc T).symm :=
  (D.baseChangeComparison_id hc T).trans (by rfl)

/-- **The unit law for the module comparison, for an abstract unit comparison.**  If the
base-change comparison for the identity of `T` is whiskering `F_T`'s inverse image with the
inverse of an identification `γ : (X_{𝟙 T})^* ≅ 𝟭`, then the identification of the quotient of
`F_T` by the kernel pulled back along the identity with the inverse image of `F_T/K` is the
component of `γ` at that quotient, read through the equality of the two kernels.

The identification is taken as a variable so that the instantiation in
`AlgebraicGeometry.Space.QuotSituation.quotientPullbackCokernelIso_hom_id` compares only the
type of that variable with the type of the argument supplied for it. -/
theorem quotientPullbackCokernelIso_hom_id_of_factorization {T : SchemesOver D.Y}
    (K : Subobject (D.baseChangeModule T))
    (γ : modulePullback B S hS (D.toCoherentSituation.relativeMap (𝟙 T)) ≅
      𝟭 (Modules.{u, u} B S hS (D.toCoherentSituation.space T).1
        (D.toCoherentSituation.space T).2))
    (hγ : D.baseChangeComparison (𝟙 T) =
      (Functor.rightUnitor (modulePullback B S hS (D.sourceProjection T))).symm ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) γ.symm) :
    (D.quotientPullbackCokernelIso (𝟙 T) K).hom =
      eqToHom (congrArg (fun J : Subobject (D.baseChangeModule T) => Limits.cokernel J.arrow)
          (Functor.conjSubobject_id γ.symm (D.baseChangeComparison (𝟙 T)) hγ K)) ≫
        γ.inv.app (Limits.cokernel K.arrow) :=
  Functor.conjSubobjectCokernelIso_id γ.symm (D.baseChangeComparison (𝟙 T)) hγ K

/-- **Stacks 0DP6, the unit law for the module comparison.**  The module comparison the morphism
`Quot_{F/X/B} ⟶ Coh_{X/B}` attaches to the identity of a test scheme is the unit comparison out
of which `AlgebraicGeometry.Space.CoherentHom.id` is built, read through the identification of
the quotient pulled back along the identity with the quotient itself.

Together with
`AlgebraicGeometry.Space.QuotSituation.quotientPullbackCokernelIso_hom_comp` this says that the
module comparisons of `AlgebraicGeometry.Space.QuotSituation.cohHom` satisfy the two functor
laws. -/
theorem quotientPullbackCokernelIso_hom_id (hc : ModulePushforwardCoherence B S hS)
    {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T)) :
    (D.quotientPullbackCokernelIso (𝟙 T) K).hom =
      eqToHom (congrArg (fun J : Subobject (D.baseChangeModule T) => Limits.cokernel J.arrow)
          (Functor.conjSubobject_id (D.toCoherentSituation.idComparison hc T).symm
            (D.baseChangeComparison (𝟙 T)) (D.baseChangeComparison_id_idComparison hc T) K)) ≫
        (D.toCoherentSituation.idComparison hc T).inv.app (Limits.cokernel K.arrow) :=
  D.quotientPullbackCokernelIso_hom_id_of_factorization K
    (D.toCoherentSituation.idComparison hc T) (D.baseChangeComparison_id_idComparison hc T)

/-- **The projection onto a quotient transports along an equality of kernels.**  This is
`CategoryTheory.Limits.cokernel_π_arrow_eqToHom` in the spelling the quotient situation uses for
its projections and its quotients, which is what makes it composable with the rest of the
calculation. -/
theorem quotientProjection_comp_eqToHom {T : SchemesOver D.Y}
    {K K' : Subobject (D.baseChangeModule T)} (e : K = K') :
    D.quotientProjection T K ≫
        eqToHom (congrArg (fun J : Subobject (D.baseChangeModule T) =>
          D.quotientModule T J) e) =
      D.quotientProjection T K' := by
  subst e
  exact Category.comp_id _

/-- **The naturality of a comparison of iterated inverse images, at a morphism out of `F_T`.**
The source of the morphism is written out rather than named `F_T`, so that the statement is the
one the naturality field produces verbatim. -/
theorem comparison_inv_naturality {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T)
    (τ : modulePullback B S hS (D.relativeMap (h ≫ k)) ≅
      modulePullback B S hS (D.relativeMap k) ⋙ modulePullback B S hS (D.relativeMap h))
    {Y : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    (f : (modulePullback B S hS (D.sourceProjection T)).obj D.F ⟶ Y) :
    (modulePullback B S hS (D.relativeMap h)).map
          ((modulePullback B S hS (D.relativeMap k)).map f) ≫ τ.inv.app Y =
      τ.inv.app ((modulePullback B S hS (D.sourceProjection T)).obj D.F) ≫
        (modulePullback B S hS (D.relativeMap (h ≫ k))).map f :=
  τ.inv.naturality f

/-- **The cocycle identity for the projections onto the pulled-back quotients.**  The projection
of `F_{T''}` onto the inverse image of `F_T/K` along `X_{T''} ⟶ X_T` is the projection onto the
inverse image along `X_{T''} ⟶ X_{T'}` of `F_{T'}/(K pulled back along k)`, followed by the
inverse image of the identification of that quotient with the inverse image of `F_T/K` and by
the comparison of the two iterated inverse images.

This is the whole content of the composition law: both sides of that law become these two
composites once the projection onto the quotient by the pulled-back kernel, an epimorphism, is
cancelled. -/
theorem quotientPullbackProjection_comp {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T')
    (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T))
    (τ : modulePullback B S hS (D.relativeMap (h ≫ k)) ≅
      modulePullback B S hS (D.relativeMap k) ⋙ modulePullback B S hS (D.relativeMap h))
    (hτ : D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) τ).symm) :
    D.quotientPullbackProjection (h ≫ k) K =
      D.quotientPullbackProjection h (D.quotientPullback k K) ≫
        ((modulePullback B S hS (D.relativeMap h)).map
            (D.quotientPullbackCokernelIso k K).hom ≫
          τ.inv.app (D.quotientModule T K)) :=
  calc D.quotientPullbackProjection (h ≫ k) K
      = (D.baseChangeComparison (h ≫ k)).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap (h ≫ k))).map
            (D.quotientProjection T K) := rfl
    _ = ((D.baseChangeComparison h).hom.app D.F ≫
            (modulePullback B S hS (D.relativeMap h)).map
                ((D.baseChangeComparison k).hom.app D.F) ≫
              τ.inv.app ((modulePullback B S hS (D.sourceProjection T)).obj D.F)) ≫
          (modulePullback B S hS (D.relativeMap (h ≫ k))).map (D.quotientProjection T K) :=
        congrArg (fun x => x ≫ (modulePullback B S hS (D.relativeMap (h ≫ k))).map
            (D.quotientProjection T K))
          (Functor.hom_app_of_eq_compWhisker (D.baseChangeComparison k)
            (D.baseChangeComparison h) (D.baseChangeComparison (h ≫ k)) τ hτ D.F)
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          ((modulePullback B S hS (D.relativeMap h)).map
                ((D.baseChangeComparison k).hom.app D.F) ≫
              τ.inv.app ((modulePullback B S hS (D.sourceProjection T)).obj D.F)) ≫
            (modulePullback B S hS (D.relativeMap (h ≫ k))).map (D.quotientProjection T K) :=
        Category.assoc _ _ _
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap h)).map
              ((D.baseChangeComparison k).hom.app D.F) ≫
            (τ.inv.app ((modulePullback B S hS (D.sourceProjection T)).obj D.F) ≫
              (modulePullback B S hS (D.relativeMap (h ≫ k))).map
                (D.quotientProjection T K)) :=
        congrArg (fun x => (D.baseChangeComparison h).hom.app D.F ≫ x)
          (Category.assoc _ _ _)
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap h)).map
              ((D.baseChangeComparison k).hom.app D.F) ≫
            ((modulePullback B S hS (D.relativeMap h)).map
                ((modulePullback B S hS (D.relativeMap k)).map (D.quotientProjection T K)) ≫
              τ.inv.app (D.quotientModule T K)) :=
        congrArg (fun x => (D.baseChangeComparison h).hom.app D.F ≫
            (modulePullback B S hS (D.relativeMap h)).map
              ((D.baseChangeComparison k).hom.app D.F) ≫ x)
          (D.comparison_inv_naturality h k τ (D.quotientProjection T K)).symm
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          ((modulePullback B S hS (D.relativeMap h)).map
                ((D.baseChangeComparison k).hom.app D.F) ≫
              (modulePullback B S hS (D.relativeMap h)).map
                ((modulePullback B S hS (D.relativeMap k)).map (D.quotientProjection T K))) ≫
            τ.inv.app (D.quotientModule T K) :=
        congrArg (fun x => (D.baseChangeComparison h).hom.app D.F ≫ x)
          (Category.assoc _ _ _).symm
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap h)).map
              ((D.baseChangeComparison k).hom.app D.F ≫
                (modulePullback B S hS (D.relativeMap k)).map (D.quotientProjection T K)) ≫
            τ.inv.app (D.quotientModule T K) :=
        congrArg (fun x => (D.baseChangeComparison h).hom.app D.F ≫
            x ≫ τ.inv.app (D.quotientModule T K))
          (Functor.map_comp (modulePullback B S hS (D.relativeMap h)) _ _).symm
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap h)).map
              (D.quotientProjection T' (D.quotientPullback k K) ≫
                (D.quotientPullbackCokernelIso k K).hom) ≫
            τ.inv.app (D.quotientModule T K) :=
        congrArg (fun x => (D.baseChangeComparison h).hom.app D.F ≫
            (modulePullback B S hS (D.relativeMap h)).map x ≫
              τ.inv.app (D.quotientModule T K))
          (D.quotientProjection_comp_quotientPullbackCokernelIso_hom k K).symm
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          ((modulePullback B S hS (D.relativeMap h)).map
                (D.quotientProjection T' (D.quotientPullback k K)) ≫
              (modulePullback B S hS (D.relativeMap h)).map
                (D.quotientPullbackCokernelIso k K).hom) ≫
            τ.inv.app (D.quotientModule T K) :=
        congrArg (fun x => (D.baseChangeComparison h).hom.app D.F ≫
            x ≫ τ.inv.app (D.quotientModule T K))
          (Functor.map_comp (modulePullback B S hS (D.relativeMap h)) _ _)
    _ = (D.baseChangeComparison h).hom.app D.F ≫
          (modulePullback B S hS (D.relativeMap h)).map
              (D.quotientProjection T' (D.quotientPullback k K)) ≫
            ((modulePullback B S hS (D.relativeMap h)).map
                (D.quotientPullbackCokernelIso k K).hom ≫
              τ.inv.app (D.quotientModule T K)) :=
        congrArg (fun x => (D.baseChangeComparison h).hom.app D.F ≫ x)
          (Category.assoc _ _ _)
    _ = _ := (Category.assoc _ _ _).symm

/-- **The composition law for the module comparison, composed with the projection onto the
quotient by the pulled-back kernel.**  This is the cocycle identity
`AlgebraicGeometry.Space.QuotSituation.quotientPullbackProjection_comp` with both projections
onto pulled-back quotients replaced by the projections onto the quotients by the pulled-back
kernels. -/
theorem quotientProjection_comp_quotientPullbackCokernelIso_hom_comp
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T))
    (τ : modulePullback B S hS (D.relativeMap (h ≫ k)) ≅
      modulePullback B S hS (D.relativeMap k) ⋙ modulePullback B S hS (D.relativeMap h))
    (hτ : D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) τ).symm) :
    D.quotientProjection T'' (D.quotientPullback (h ≫ k) K) ≫
        (D.quotientPullbackCokernelIso (h ≫ k) K).hom =
      D.quotientProjection T'' (D.quotientPullback h (D.quotientPullback k K)) ≫
        ((D.quotientPullbackCokernelIso h (D.quotientPullback k K)).hom ≫
          ((modulePullback B S hS (D.relativeMap h)).map
              (D.quotientPullbackCokernelIso k K).hom ≫
            τ.inv.app (D.quotientModule T K))) :=
  ((D.quotientProjection_comp_quotientPullbackCokernelIso_hom (h ≫ k) K).trans
      (D.quotientPullbackProjection_comp h k K τ hτ)).trans
    (comp_assoc_of_eq (D.quotientProjection_comp_quotientPullbackCokernelIso_hom h
      (D.quotientPullback k K)) _)

/-- **The composition law for the module comparison, for an abstract comparison of iterated
inverse images.**  The comparison is taken as a variable, and the equality of the kernel pulled
back along a composite with the iterated pullback as a hypothesis, for the reason recorded in
the implementation notes. -/
theorem quotientPullbackCokernelIso_hom_comp_of_factorization {T'' T' T : SchemesOver D.Y}
    (h : T'' ⟶ T') (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T))
    (τ : modulePullback B S hS (D.relativeMap (h ≫ k)) ≅
      modulePullback B S hS (D.relativeMap k) ⋙ modulePullback B S hS (D.relativeMap h))
    (hτ : D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T)) τ).symm)
    (he : D.quotientPullback (h ≫ k) K = D.quotientPullback h (D.quotientPullback k K)) :
    (D.quotientPullbackCokernelIso (h ≫ k) K).hom =
      eqToHom (congrArg (fun J : Subobject (D.baseChangeModule T'') =>
          D.quotientModule T'' J) he) ≫
        ((D.quotientPullbackCokernelIso h (D.quotientPullback k K)).hom ≫
          ((modulePullback B S hS (D.relativeMap h)).map
              (D.quotientPullbackCokernelIso k K).hom ≫
            τ.inv.app (D.quotientModule T K))) :=
  (cancel_epi (D.quotientProjection T'' (D.quotientPullback (h ≫ k) K))).1
    ((D.quotientProjection_comp_quotientPullbackCokernelIso_hom_comp h k K τ hτ).trans
      (comp_assoc_of_eq (D.quotientProjection_comp_eqToHom he) _))

/-- **The base-change comparison for a composite of morphisms of test schemes factors through
the composition comparison of `Coh_{X/B}`.**  This is
`AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison_comp` with the comparison of
Stacks 03LU for the two base-change maps named as
`AlgebraicGeometry.Space.CoherentSituation.compComparison`, which is the comparison out of which
`AlgebraicGeometry.Space.CoherentHom.comp` is built.

As for the unit law, this is an equality of isomorphisms of functors. -/
theorem baseChangeComparison_comp_compComparison (hc : ModulePushforwardCoherence B S hS)
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T) :
    D.baseChangeComparison (h ≫ k) =
      (D.baseChangeComparison h ≪≫
          Functor.isoWhiskerRight (D.baseChangeComparison k)
            (modulePullback B S hS (D.relativeMap h)) ≪≫
          Functor.associator (modulePullback B S hS (D.sourceProjection T))
            (modulePullback B S hS (D.relativeMap k))
            (modulePullback B S hS (D.relativeMap h))) ≪≫
        (Functor.isoWhiskerLeft (modulePullback B S hS (D.sourceProjection T))
          (D.toCoherentSituation.compComparison h k)).symm :=
  (D.baseChangeComparison_comp hc h k).trans (by rfl)

/-- **Stacks 0DP6, the composition law for the module comparison.**  The module comparison the
morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` attaches to a composite `h ≫ k` of morphisms of test schemes
is the composite of the comparisons attached to `k` and to `h` along the composition comparison
out of which `AlgebraicGeometry.Space.CoherentHom.comp` is built, read through the
identification of the kernel pulled back along `h ≫ k` with the iterated pullback.

Together with `AlgebraicGeometry.Space.QuotSituation.quotientPullbackCokernelIso_hom_id` this
says that the module comparisons of `AlgebraicGeometry.Space.QuotSituation.cohHom` satisfy the
two functor laws. -/
theorem quotientPullbackCokernelIso_hom_comp (hc : ModulePushforwardCoherence B S hS)
    {T'' T' T : SchemesOver D.Y} (h : T'' ⟶ T') (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    (D.quotientPullbackCokernelIso (h ≫ k) K).hom =
      eqToHom (congrArg (fun J : Subobject (D.baseChangeModule T'') =>
          D.quotientModule T'' J) (D.quotientPullback_comp hc h k K)) ≫
        ((D.quotientPullbackCokernelIso h (D.quotientPullback k K)).hom ≫
          ((modulePullback B S hS (D.relativeMap h)).map
              (D.quotientPullbackCokernelIso k K).hom ≫
            (D.toCoherentSituation.compComparison h k).inv.app (D.quotientModule T K))) :=
  D.quotientPullbackCokernelIso_hom_comp_of_factorization h k K
    (D.toCoherentSituation.compComparison h k)
    (D.baseChangeComparison_comp_compComparison hc h k) (D.quotientPullback_comp hc h k K)

end QuotSituation

end AlgebraicGeometry.Space

end
