module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeIdentity

/-!
# The derived identity law for the base change map of abelian small étale sheaves

For a morphism `g : X ⟶ S` of schemes and morphisms `u : S ⟶ S`, `v : X ⟶ X` which are the
identity, the square

```
X --v--> X
|g        |g
v         v
S --u--> S
```

commutes, and the *derived* base change comparison of that square is the identity, modulo the
comparisons `R(u^{-1}) ≅ 𝟭` and `R(v^{-1}) ≅ 𝟭`. Together with the derived pasting law
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedPaste` this is what makes the
derived base change comparisons of a morphism of inverse systems of schemes a *functor* on the
index category, which is what the colimit diagram of [Stacks, Tag 0DV2] is a diagram over.

The hypotheses are that `u` and `v` are identities, and the commutativity of the square. Nothing
else: no finiteness, separatedness or torsion condition enters, inverse image of abelian sheaves
being exact for every morphism of schemes.

## How it is proved

Three layers, each the identity analogue of a layer of the pasting law.

On the small étale sites, base change along a morphism known to be the identity is the identity
(`Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf`), and the comparison for a composite one of
whose factors is such a morphism is the corresponding unitor. One of the two unit laws is
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_id_hom_app`; the other, where the
*first* factor is the identity, is proved here by the same argument — a morphism into a base
change is determined by its first projection.

On direct images these two unit laws give the comparison `g_* v_* ≅ g_* ≅ u_* g_*` of the two
composite direct images around the square, and
`Stacks.Cohomology.BaseChange.mate_id_app` turns that into the underived base change map,
through `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_mate`.

On derived categories the descent is generic, and is
`Stacks.Cohomology.BaseChange.derived_id`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePushforwardAbIdOf` — direct image of abelian sheaves along a
  morphism known to be the identity is the identity functor.
* `Stacks.EtaleCohomology.smallEtalePullbackAbIdOf` — the same for inverse image, as the left
  adjoint of the former.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_id_left_hom_app` — **the unit law for the
  base-change comparison with the first factor an identity**, dual to
  `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_id_hom_app`.
* `Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_id_left_hom_app` and
  `Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_id_right_hom_app` — the two unit laws for
  the comparison of direct images along a composite.
* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso_id_hom_app` — the comparison of the two
  composite direct images around the identity square is the one the two unitors force.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_id_app` — **the underived identity law** for
  the base change map of abelian small étale sheaves.
* `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_id` and
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_id_app` — **the derived identity law**,
  as an identity of natural transformations and evaluated at a bounded below complex.

## Implementation notes

*No tag is placed.* The identity law is not a source-delimited result: it is not part of
[Stacks, Tag 0E47], which states the pasting law, nor of the statement of [Stacks, Tag 0F02]
which constructs the base change map. It is one of the inputs that the colimit diagram of
[Stacks, Tag 0DV2] needs, and it is the derived half of it — the half concerning the underlying
sheaves being
`Stacks.EtaleCohomology.directImageSystem_map_id`.

*Why every computation on the small étale site is term-mode.* In the presence of an object of a
small étale site the rewriting tactics cannot see through `CategoryTheory.MorphismProperty`, so
every rearrangement is isolated in a statement about morphisms in an abstract category and
applied as a term; see the same note on
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity`.

*Why the comparison for a composite is renamed.*
`Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso` names the common diagonal of the square
`g ≫ u`, while the two unit laws are stated with it named `g` — the naming at which no
transport along an equality of morphisms appears in them. The two namings differ by an
`CategoryTheory.eqToIso`, and the two transports that enter cancel, which is
`Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_congr` together with the generic
cancellation of a common second factor.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Morphisms into an iterated base change -/

section SiteUnitLaw

/-- A morphism into an iterated base change is determined by its composite projection onto the
original object. -/
private lemma smallEtaleBaseChange_double_hom_ext {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    {A : W.Etale} {V : Y.Etale}
    {p q : A ⟶ (smallEtaleBaseChange f).obj ((smallEtaleBaseChange g).obj V)}
    (hpq : p.left ≫ pullback.fst ((smallEtaleBaseChange g).obj V).hom f ≫
        pullback.fst V.hom g =
      q.left ≫ pullback.fst ((smallEtaleBaseChange g).obj V).hom f ≫ pullback.fst V.hom g) :
    p = q :=
  smallEtaleBaseChange_hom_ext f (pullback.hom_ext hpq
    ((smallEtaleBaseChange_fst_snd f g p).trans
      (smallEtaleBaseChange_fst_snd f g q).symm))

/-- The rearrangement that proves the left unit law, on variables in an abstract category. -/
private theorem idUnitRearrange {C : Type*} [Category* C] {O₁ O₂ O₃ : C}
    {p q : O₁ ⟶ O₂} {x : O₂ ⟶ O₁} {y : O₁ ⟶ O₃}
    (hp : p ≫ x ≫ y = y) (hq : q ≫ x = 𝟙 O₁) :
    p ≫ x ≫ y = q ≫ x ≫ y := by
  rw [hp, ← Category.assoc, hq, Category.id_comp]

variable {X Y : Scheme.{u}} (v : X ⟶ X) (hv : v = 𝟙 X) (g : X ⟶ Y) (hvg : g = v ≫ g)

include hv in
/-- **The unit law for `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` with the first factor
an identity.** With the composite named `g`, the comparison between base change along `g` and
the composite of the base changes along `g` and along `v` is the identity comparison for `v`:
both sides are morphisms into an iterated base change, and their composite projections onto the
original object agree.

This is dual to `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_id_hom_app`, where it is the
second factor that is an identity. -/
public theorem smallEtaleBaseChangeComp'_id_left_hom_app (U : Y.Etale) :
    (smallEtaleBaseChangeComp' v g g hvg).hom.app U =
      (smallEtaleBaseChangeIdOf v hv).inv.app ((smallEtaleBaseChange g).obj U) :=
  smallEtaleBaseChange_double_hom_ext v g
    (idUnitRearrange (smallEtaleBaseChangeComp'_fst_fst v g g hvg U)
      (smallEtaleBaseChangeIdOf_inv_app_left v hv ((smallEtaleBaseChange g).obj U)))

end SiteUnitLaw

/-! ### Direct image along an identity -/

section PushforwardId

/-- **Direct image of abelian sheaves along a morphism known to be the identity is the identity
functor.** -/
public def smallEtalePushforwardAbIdOf {X : Scheme.{u}} (v : X ⟶ X) (hv : v = 𝟙 X) :
    smallEtalePushforwardAb v ≅ 𝟭 (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeIdOf v hv) Ab.{u + 1}
    (smallEtaleTopology X)

/-- The component of `Stacks.EtaleCohomology.smallEtalePushforwardAbIdOf`. -/
public lemma smallEtalePushforwardAbIdOf_hom_app_hom_app {X : Scheme.{u}} (v : X ⟶ X)
    (hv : v = 𝟙 X) (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (U : (X.Etale)ᵒᵖ) :
    ((smallEtalePushforwardAbIdOf v hv).hom.app G).hom.app U =
      G.obj.map (Opposite.op ((smallEtaleBaseChangeIdOf v hv).inv.app U.unop)) :=
  Category.comp_id _

/-- The component of the comparison for a composite direct image of abelian sheaves. -/
public lemma smallEtalePushforwardAbComp'_hom_app_hom_app {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (U : (Z.Etale)ᵒᵖ) :
    ((smallEtalePushforwardAbComp' f g fg hfg).hom.app F).hom.app U =
      F.obj.map (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) :=
  smallEtalePushforwardComp'_hom_app_hom_app f g fg hfg Ab.{u + 1} F U

/-- A component of the comparison of direct images along a composite is determined by its
components, which are the sections of `F` along the components of the site-level comparison. -/
private theorem smallEtalePushforwardAbComp'_hom_app_ext {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (T : (smallEtalePushforwardAb f ⋙ smallEtalePushforwardAb g).obj F ⟶
      (smallEtalePushforwardAb fg).obj F)
    (h : ∀ U : (Z.Etale)ᵒᵖ,
      F.obj.map (Opposite.op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) =
        T.hom.app U) :
    (smallEtalePushforwardAbComp' f g fg hfg).hom.app F = T :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U =>
    (smallEtalePushforwardAbComp'_hom_app_hom_app f g fg hfg F U).trans (h U)))

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The unit law for the comparison of direct images along a composite, with the first factor
an identity.** -/
public theorem smallEtalePushforwardAbComp'_id_left_hom_app (v : X ⟶ X) (hv : v = 𝟙 X)
    (hvg : g = v ≫ g) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtalePushforwardAbComp' v g g hvg).hom.app F =
      (smallEtalePushforwardAb g).map ((smallEtalePushforwardAbIdOf v hv).hom.app F) := by
  refine smallEtalePushforwardAbComp'_hom_app_ext v g g hvg F _ fun U => ?_
  rw [smallEtaleBaseChangeComp'_id_left_hom_app v hv g hvg U.unop]
  exact (smallEtalePushforwardAbIdOf_hom_app_hom_app v hv F
    (Opposite.op ((smallEtaleBaseChange g).obj U.unop))).symm

/-- **The unit law for the comparison of direct images along a composite, with the second factor
an identity.** -/
public theorem smallEtalePushforwardAbComp'_id_right_hom_app (u : Y ⟶ Y) (hu : u = 𝟙 Y)
    (hgu : g = g ≫ u) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtalePushforwardAbComp' g u g hgu).hom.app F =
      (smallEtalePushforwardAbIdOf u hu).hom.app ((smallEtalePushforwardAb g).obj F) := by
  refine smallEtalePushforwardAbComp'_hom_app_ext g u g hgu F _ fun U => ?_
  rw [smallEtaleBaseChangeComp'_id_hom_app g u hu hgu U.unop]
  exact (smallEtalePushforwardAbIdOf_hom_app_hom_app u hu
    ((smallEtalePushforwardAb g).obj F) U).symm

/-- The inverse half of `smallEtalePushforwardAbComp'_id_right_hom_app`. -/
public theorem smallEtalePushforwardAbComp'_id_right_inv_app (u : Y ⟶ Y) (hu : u = 𝟙 Y)
    (hgu : g = g ≫ u) (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtalePushforwardAbComp' g u g hgu).inv.app F =
      (smallEtalePushforwardAbIdOf u hu).inv.app ((smallEtalePushforwardAb g).obj F) :=
  congrArg Iso.inv
    (Iso.ext (smallEtalePushforwardAbComp'_id_right_hom_app g u hu hgu F) :
      Iso.app (smallEtalePushforwardAbComp' g u g hgu) F =
        Iso.app (smallEtalePushforwardAbIdOf u hu) ((smallEtalePushforwardAb g).obj F))

end PushforwardId

/-! ### The square comparison at the identity square -/

section SquareId

/-- Renaming the composite in the comparison of direct images along a composite: the dependence
on the name is a single transport along the equality of the two names. -/
private theorem smallEtalePushforwardAbComp'_congr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg₁ fg₂ : X ⟶ Z) (h₁ : fg₁ = f ≫ g) (h₂ : fg₂ = f ≫ g) (h₃ : fg₂ = fg₁) :
    smallEtalePushforwardAbComp' f g fg₁ h₁ =
      smallEtalePushforwardAbComp' f g fg₂ h₂ ≪≫
        eqToIso (congrArg smallEtalePushforwardAb h₃) := by
  subst h₂
  subst h₃
  exact (Iso.trans_refl _).symm

/-- A common second factor cancels out of two composites of isomorphisms, one of them
inverted. -/
private theorem isoTransCancel {D : Type*} [Category* D] {P Q R S : D} (A : P ≅ Q) (E : Q ≅ R)
    (B : S ≅ Q) :
    (A ≪≫ E) ≪≫ (B ≪≫ E).symm = A ≪≫ B.symm := by
  refine Iso.ext ?_
  simp

variable {X S : Scheme.{u}} (g : X ⟶ S) (u : S ⟶ S) (v : X ⟶ X) (hu : u = 𝟙 S) (hv : v = 𝟙 X)
  (w : g ≫ u = v ≫ g)

include hu hv w in
/-- **The comparison of the two composite direct images around the identity square is the one
the two unitors force.** -/
public theorem smallEtaleSquarePushforwardIso_id_hom_app
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtaleSquarePushforwardIso u g g v w).hom.app F =
      (smallEtalePushforwardAb g).map ((smallEtalePushforwardAbIdOf v hv).hom.app F) ≫
        (smallEtalePushforwardAbIdOf u hu).inv.app ((smallEtalePushforwardAb g).obj F) := by
  have hvg : g = v ≫ g := by rw [hv, Category.id_comp]
  have hgu : g = g ≫ u := by rw [hu, Category.comp_id]
  have h0 : smallEtaleSquarePushforwardIso u g g v w =
      smallEtalePushforwardAbComp' v g (g ≫ u) w ≪≫
        (smallEtalePushforwardAbComp' g u (g ≫ u) rfl).symm := rfl
  have hsq : smallEtaleSquarePushforwardIso u g g v w =
      smallEtalePushforwardAbComp' v g g hvg ≪≫
        (smallEtalePushforwardAbComp' g u g hgu).symm := by
    rw [h0, smallEtalePushforwardAbComp'_congr v g (g ≫ u) g w hvg hgu,
      smallEtalePushforwardAbComp'_congr g u (g ≫ u) g rfl hgu hgu]
    exact isoTransCancel _ _ _
  rw [hsq, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    smallEtalePushforwardAbComp'_id_left_hom_app g v hv hvg F,
    smallEtalePushforwardAbComp'_id_right_inv_app g u hu hgu F]

end SquareId

/-! ### The identity law -/

section IdentityLaw

variable {X S : Scheme.{u}} (g : X ⟶ S) (u : S ⟶ S) (v : X ⟶ X) (hu : u = 𝟙 S) (hv : v = 𝟙 X)
  (w : g ≫ u = v ≫ g)

/-- **Inverse image of abelian sheaves along a morphism known to be the identity is the identity
functor**, as the left adjoint of `Stacks.EtaleCohomology.smallEtalePushforwardAbIdOf`. -/
public def smallEtalePullbackAbIdOf {Y : Scheme.{u}} (u : Y ⟶ Y) (hu : u = 𝟙 Y) :
    smallEtalePullbackAb u ≅ 𝟭 (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :=
  (smallEtaleAdjunctionAb u).leftAdjointIdIso (smallEtalePushforwardAbIdOf u hu)

include hu hv w in
/-- **The underived identity law for the base change map of abelian small étale sheaves.** The
base change map of the identity square is the identity, modulo the identifications of the two
inverse images with the identity functor. -/
public theorem smallEtaleBaseChangeAb_id_app
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtaleBaseChangeAb u g g v w).app F =
      (smallEtalePullbackAbIdOf u hu).hom.app ((smallEtalePushforwardAb g).obj F) ≫
        (smallEtalePushforwardAb g).map ((smallEtalePullbackAbIdOf v hv).inv.app F) := by
  rw [smallEtaleBaseChangeAb_eq_mate]
  exact Stacks.Cohomology.BaseChange.mate_id_app (smallEtaleAdjunctionAb u)
    (smallEtaleAdjunctionAb v) (smallEtalePushforwardAb g)
    (smallEtaleSquarePushforwardIso u g g v w) (smallEtalePushforwardAbIdOf u hu)
    (smallEtalePushforwardAbIdOf v hv)
    (smallEtaleSquarePushforwardIso_id_hom_app g u v hu hv w) F

include hu hv w in
/-- **The derived identity law for the base change map of abelian small étale sheaves.** The
derived base change comparison of the identity square is the comparison the two derived
identity isomorphisms force. -/
public theorem smallEtaleDerivedBaseChangeAb_id :
    smallEtaleDerivedBaseChangeAb u g g v w =
      Stacks.Cohomology.BaseChange.derivedId (smallEtalePushforwardAb g)
        (smallEtalePullbackAb u) (smallEtalePullbackAb v)
        (smallEtalePullbackAbIdOf u hu) (smallEtalePullbackAbIdOf v hv) :=
  Stacks.Cohomology.BaseChange.derived_id (smallEtalePushforwardAb g)
    (smallEtalePullbackAb u) (smallEtalePullbackAb v)
    (smallEtalePullbackAbIdOf u hu) (smallEtalePullbackAbIdOf v hv) _
    (smallEtaleBaseChangeAb_id_app g u v hu hv w)

include hu hv w in
/-- **The derived identity law, evaluated at a bounded below complex.** -/
public theorem smallEtaleDerivedBaseChangeAb_id_app
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) Ab.{u + 1})) :
    (smallEtaleDerivedBaseChangeAb u g g v w).app M =
      (Functor.rightDerivedFunctorPlusIdIsoOf (smallEtalePullbackAb u)
            (smallEtalePullbackAbIdOf u hu)).hom.app
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj M) ≫
        (smallEtalePushforwardAb g).rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusIdIsoOf (smallEtalePullbackAb v)
            (smallEtalePullbackAbIdOf v hv)).inv.app M) :=
  Stacks.Cohomology.BaseChange.derived_id_app (smallEtalePushforwardAb g)
    (smallEtalePullbackAb u) (smallEtalePullbackAb v)
    (smallEtalePullbackAbIdOf u hu) (smallEtalePullbackAbIdOf v hv) _
    (smallEtaleBaseChangeAb_id_app g u v hu hv w) M

end IdentityLaw

end Stacks.EtaleCohomology

end
