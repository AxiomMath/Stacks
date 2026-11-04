module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRule
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InverseIsoGysin

/-!
# The operation of a Chow cohomology class on the test schemes is natural

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `c ∈ A^p(X) = A^p(X ⟶ X)` be a bivariant class (Stacks 0B76,
0B7E). On a test scheme `g : T ⟶ X` the class operates on `A_*(T)` by capping into
`A_*(X ×_X T)` and pushing forward along the isomorphism `X ×_X T ≅ T`; this is
`Stacks.Chow.BivariantClass.idRule`. The three axioms of Stacks 0B76 for `c` translate into the
three corresponding identities for that operation, read directly on the test schemes:

* commutation with proper pushforward is `Stacks.Chow.BivariantClass.idRule_properNaturality`;
* commutation with flat pullback of fixed relative dimension is
  `Stacks.Chow.BivariantClass.idRule_flatNaturality` (this file);
* commutation with the Gysin map of a section of an invertible module is
  `Stacks.Chow.BivariantClass.idRule_gysinNaturality` (this file), for the Gysin system of the
  first Chern class of an invertible module.

## Main results

* `Stacks.Chow.BivariantClass.idRule_flatNaturality`
* `Stacks.Chow.BivariantClass.idRule_gysinNaturality`

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

variable (G : GysinSystem C) {p : ℤ}

/-- **Axiom (2) of Stacks 0B76, read on the test schemes.** The operation of a Chow cohomology
class commutes with flat pullback of fixed relative dimension along a morphism of test schemes
over `X`. -/
theorem BivariantClass.idRule_flatNaturality
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    IdentityCapRule.FlatNaturality C sX p (c.idRule C sX G) := by
  intro T T' g _ h _ _ r hr k hfac hfacp α
  set h' : pullback (𝟙 X) (h ≫ g) ⟶ pullback (𝟙 X) g := bivariantBaseChangeMap (𝟙 X) g h
  have sq : IsPullback (pullback.snd (𝟙 X) (h ≫ g)) h' h (pullback.snd (𝟙 X) g) :=
    isPullback_bivariantBaseChangeMap (𝟙 X) g h
  have hfst : h' ≫ pullback.fst (𝟙 X) g = pullback.fst (𝟙 X) (h ≫ g) :=
    bivariantBaseChangeMap_fst (𝟙 X) g h
  have : LocallyOfFiniteType h' :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hr' : AlgebraicGeometry.RelativeDimension h' r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
  have hm : h' ≫ pullback.fst (𝟙 X) g ≫ sX = pullback.fst (𝟙 X) (h ≫ g) ≫ sX := by
    rw [← Category.assoc, hfst]
  have hh : h ≫ g ≫ sX = (h ≫ g) ≫ sX := by simp [Category.assoc]
  have hbg : (identityBaseChangeIso g).hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX g
  have hbg' : (identityBaseChangeIso (h ≫ g)).hom ≫ (h ≫ g) ≫ sX =
      pullback.fst (𝟙 X) (h ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX (h ≫ g)
  have hsq : h' ≫ (identityBaseChangeIso g).hom = (identityBaseChangeIso (h ≫ g)).hom ≫ h :=
    sq.w.symm
  have hfach' : FlatPullbackFactorsThroughRationalEquivalence C
      (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) h' hm r hr' (k - p) :=
    flatPullbackFactorsThroughRationalEquivalence_of_isIso_square C
      (pullback.fst (𝟙 X) g ≫ sX) (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (g ≫ sX) ((h ≫ g) ≫ sX)
      (identityBaseChangeIso g).hom hbg (identityBaseChangeIso (h ≫ g)).hom hbg' h' hm h hh
      hsq r hr' hr (k - p) hfacp
  refine HEq.trans (chowPushforwardOfIso_heq (identityBaseChangeIso (h ≫ g)).hom hbg' hbg' rfl
      rfl (show k + (r : ℤ) - p = k - p + (r : ℤ) by omega)
      (c.flat_naturality g h r hr h' sq hfst k hr' hfac hfach' α)) ?_
  exact heq_of_eq (flatPullbackChow_chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX)
    (pullback.fst (𝟙 X) (h ≫ g) ≫ sX) (g ≫ sX) ((h ≫ g) ≫ sX)
    (identityBaseChangeIso g).hom hbg (identityBaseChangeIso (h ≫ g)).hom hbg' h' hm h hh
    hsq r hr' hr (k - p) hfach' hfacp (c.cap g k α)).symm

/-- **Axiom (3) of Stacks 0B76, read on the test schemes.** The operation of a Chow cohomology
class commutes with the Gysin map of the zero scheme of a section of an invertible module on a
test scheme, for the Gysin system of the first Chern class of an invertible module. -/
theorem BivariantClass.idRule_gysinNaturality
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p) :
    IdentityCapRule.GysinNaturality C sX p (c.idRule C sX (gysinSystemOfInvertible C))
      (gysinSystemOfInvertible C) := by
  intro T g _ N _ s k α
  set D := Stacks.Divisors.zeroScheme T N s with hD
  set N' := (Scheme.Modules.pullback (pullback.snd (𝟙 X) g)).obj N with hN'
  set s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd (𝟙 X) g) N s with hs'
  set E := Stacks.Divisors.zeroScheme (pullback (𝟙 X) g) N' s' with hE
  set e : pullback (𝟙 X) (D.subschemeι ≫ g) ≅ E.subscheme :=
    bivariantDivisorBaseChangeIso (𝟙 X) g N s with hee
  set eD : pullback (𝟙 X) (D.subschemeι ≫ g) ≅ D.subscheme :=
    identityBaseChangeIso (D.subschemeι ≫ g) with heD
  set eg : pullback (𝟙 X) g ≅ T := identityBaseChangeIso g with heg
  have hbgD : eD.hom ≫ (D.subschemeι ≫ g) ≫ sX =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX (D.subschemeι ≫ g)
  have hbgDinv : eD.inv ≫ pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX =
      (D.subschemeι ≫ g) ≫ sX :=
    identityBaseChangeIso_hom_comp C sX (D.subschemeι ≫ g)
  have hbg : eg.hom ≫ g ≫ sX = pullback.fst (𝟙 X) g ≫ sX :=
    identityBaseChangeIso_hom_comp_base C sX g
  have hbginv : eg.inv ≫ pullback.fst (𝟙 X) g ≫ sX = g ≫ sX :=
    identityBaseChangeIso_hom_comp C sX g
  have hfstD : bivariantBaseChangeMap (𝟙 X) g D.subschemeι ≫ pullback.fst (𝟙 X) g =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) :=
    bivariantBaseChangeMap_fst (𝟙 X) g D.subschemeι
  have he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap (𝟙 X) g D.subschemeι :=
    bivariantDivisorBaseChangeIso_hom_subschemeι (𝟙 X) g N s
  have hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX := by
    rw [← Category.assoc, he, ← Category.assoc, hfstD]
  have hj : (eD.inv ≫ e.hom) ≫ (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) =
      D.subschemeι ≫ g ≫ sX := by
    rw [Category.assoc, hbase, hbgDinv, Category.assoc]
  have hinvj : (e.hom ≫ (inv (eD.inv ≫ e.hom))) = eD.hom := by
    rw [IsIso.comp_inv_eq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hidx : k + 1 - p = k - p + 1 := by omega
  have hinvjb : (inv (eD.inv ≫ e.hom)) ≫ (D.subschemeι ≫ g ≫ sX) =
      E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX := by
    rw [IsIso.inv_comp_eq, hj]
  have hfe := properPushforwardFactorsThroughRationalEquivalence_of_isIso C
    (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
    (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) e.hom hbase (k - p)
  have hfi := properPushforwardFactorsThroughRationalEquivalence_of_isIso C
    (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (D.subschemeι ≫ g ≫ sX)
    (inv (eD.inv ≫ e.hom)) hinvjb (k - p)
  have hgys := c.gysin_naturality g N s k e he hbase
    hfe α
  have hnat := GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C (g ≫ sX)
    (pullback.fst (𝟙 X) g ≫ sX) eg.inv (pullback.snd (𝟙 X) g)
    eg.inv_hom_id hbginv N s (k - p) (eD.inv ≫ e.hom) hj
    (by
      rw [Category.assoc, he]
      exact identityBaseChangeIso_inv_bivariantBaseChangeMap g D.subschemeι)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
      (D.subschemeι ≫ g ≫ sX) (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (eD.inv ≫ e.hom) hj
      (k - p))
    (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hidx)
      (chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) eg.hom hbg (k + 1 - p)
        (c.cap g (k + 1) α)))
  have harg : chowPushforwardOfIso C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) eg.inv hbginv
        (k - p + 1)
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hidx)
          (chowPushforwardOfIso C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) eg.hom hbg (k + 1 - p)
            (c.cap g (k + 1) α))) =
      Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X) g ≫ sX)) hidx) (c.cap g (k + 1) α) := by
    rw [← chowPushforwardOfIso_cast C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX) eg.inv hbginv hidx]
    exact congrArg (Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X) g ≫ sX)) hidx))
      (chowPushforwardOfIso_inv_comp C (pullback.fst (𝟙 X) g ≫ sX) (g ≫ sX) eg.hom hbg
        (k + 1 - p) (c.cap g (k + 1) α))
  rw [harg, ← hgys] at hnat
  have hbgD' : eD.hom ≫ D.subschemeι ≫ g ≫ sX =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX := by
    rw [← Category.assoc D.subschemeι g sX]
    exact hbgD
  have hsplit := congrFun (congrArg DFunLike.coe
    (properChowPushforward_comp C (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
      (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (D.subschemeι ≫ g ≫ sX) e.hom
      (inv (eD.inv ≫ e.hom)) hbase hinvjb (k - p)
      hfe hfi))
    (c.cap (D.subschemeι ≫ g) k ((gysinSystemOfInvertible C).onChow (g ≫ sX) N s k α))
  rw [AddMonoidHom.coe_comp, Function.comp_apply] at hsplit
  have hcompb : (e.hom ≫ (inv (eD.inv ≫ e.hom))) ≫ (D.subschemeι ≫ g ≫ sX) =
      pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX := by
    rw [Category.assoc, hinvjb]; exact hbase
  have hfacComp : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX) (D.subschemeι ≫ g ≫ sX)
      (e.hom ≫ (inv (eD.inv ≫ e.hom))) hcompb (k - p) :=
    properPushforwardFactorsThroughRationalEquivalence_comp C
      (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
      (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (D.subschemeι ≫ g ≫ sX) e.hom
      (inv (eD.inv ≫ e.hom)) hbase hinvjb (k - p)
      hfe hfi
  have hcongr := congrFun (congrArg DFunLike.coe
    (properChowPushforward_congr C (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX)
      (D.subschemeι ≫ g ≫ sX) (e.hom ≫ (inv (eD.inv ≫ e.hom))) eD.hom hinvj
      hcompb hbgD' (k - p) hfacComp
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C
        (pullback.fst (𝟙 X) (D.subschemeι ≫ g) ≫ sX) (D.subschemeι ≫ g ≫ sX) eD.hom hbgD'
        (k - p))))
    (c.cap (D.subschemeι ≫ g) k ((gysinSystemOfInvertible C).onChow (g ≫ sX) N s k α))
  exact ((hsplit.trans hcongr).symm.trans
    (DFunLike.congr_arg (chowPushforwardOfIso C (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX)
      (D.subschemeι ≫ g ≫ sX) (inv (eD.inv ≫ e.hom)) hinvjb (k - p)) hnat)).trans
    (chowPushforwardOfIso_inv_comp C (D.subschemeι ≫ g ≫ sX)
      (E.subschemeι ≫ pullback.fst (𝟙 X) g ≫ sX) (eD.inv ≫ e.hom) hj (k - p) _)

end Stacks.Chow

end
