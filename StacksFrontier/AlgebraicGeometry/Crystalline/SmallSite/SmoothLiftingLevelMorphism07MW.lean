module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.EnvelopeCosimplicialComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothLiftingComparison

/-!
# Morphisms into the levels `T_e` respect the maps to `C = Γ(X, ⊤)`

Let `(p, (S, I, γ), X)` be a global crystalline situation with `X` and `S` affine and `p`
nilpotent on `Γ(X, ⊤)`, and let `T_e = T(0)_e` be the degree-zero levels of the cosimplicial
system of thickenings `...SmallSite.wholeSpaceSystem` of [Stacks, Tag 07JN], built from the
default presentation `A[x_c : c ∈ C] → C`.  The ring `Γ(T_e, 𝒪)` is the reduction of the divided
power envelope `E(0)` of that presentation, through `...SmallSite.envLevelMap`.

For an object `(U, T, δ)` of `Cris(X/S)` whose map `U ⟶ X` is an isomorphism, the ring
`Γ(T, ⊤)` maps to `Γ(X, ⊤)`: restrict to `U` along the thickening and transport to `X` along the
inverse of `U ≅ X`.  This is `thickeningAugmentation`.  This module proves:

* `thickeningAugmentation_crysRingMap` — the augmentation is natural: restricting along a
  morphism `B ⟶ B'` of `Cris(X/S)` and then augmenting is augmenting on `B'`;
* `thickeningAugmentation_envLevelMap` — on the level `T_e` the augmentation sends the reduction
  of the image of a polynomial `q` of the presentation algebra to its image `g(q) ∈ C`.  This is
  the compatibility of the counit of the equivalence
  `Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine` with the structural maps
  `C → B/J`, together with the fact that the structural map of the completed envelope sends
  `g(q)` to the class of `q`;
* `thickeningAugmentation_crysRingMap_envLevelMap` — the two together: for every morphism
  `k : B ⟶ T_e` with `B` over the whole of `X`, augmenting the restriction along `k` of the
  reduction of `q` gives `g(q)`;
* `Situation07MW.toY_appTop_crysRingMap_envLevelMap` — the case of the smooth lifting
  `(X, Y, γ)` of Remark [Stacks, Tag 07MW], where the augmentation is restriction along `X ⟶ Y`
  (`Situation07MW.thickeningAugmentation_crystallineThickening`).

Everything stated is proved; nothing is assumed.  No tag attribute is placed: these are
auxiliary compatibilities for part (3) of [Stacks, Tag 07MW], which is not proved here.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u v w

noncomputable section

namespace Crystalline.DividedPowerThickening

variable {s : AffineCrystallineSituation.{u, v}}

/-- **A morphism of divided power thickenings preserves the elements lifting a given element of
`C`**: if the class of `x` modulo `J` is the image of `c ∈ C`, so is the class of the image of
`x`. -/
theorem mk_hom_of_mk_eq_toQuotient {X Y : DividedPowerThickening.{u, v, w} s} (f : X ⟶ Y)
    {x : (X.ring : Type w)} {c : s.C}
    (h : Ideal.Quotient.mk X.ring.ideal x = X.toQuotient c) :
    Ideal.Quotient.mk Y.ring.ideal (f.hom x) = Y.toQuotient c := by
  rw [← f.toQuotient_comp, RingHom.comp_apply, ← h, DividedPowerRing.quotientRingHom_mk]

end Crystalline.DividedPowerThickening

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The augmentation of an object over the whole of `X` -/

/-- **The augmentation `Γ(T, ⊤) → Γ(X, ⊤)` of an object `(U, T, δ)` of `Cris(X/S)` over the whole
of `X`**: restriction to `U` along the thickening `U ↪ T`, followed by the transport to `X` along
the inverse of the isomorphism `U ≅ X`. -/
def thickeningAugmentation (B : CrystallineThickening S) [IsIso B.obj.toX] :
    Γ(B.obj.thickening.target.scheme, ⊤) →+* Γ(S.X, ⊤) :=
  (inv B.obj.toX).appTop.hom.comp B.obj.thickening.immersion.appTop.hom

/-- The augmentation is restriction along the thickening followed by restriction along the
inverse of `U ≅ X`. -/
theorem thickeningAugmentation_apply (B : CrystallineThickening S) [IsIso B.obj.toX]
    (a : Γ(B.obj.thickening.target.scheme, ⊤)) :
    thickeningAugmentation B a =
      (inv B.obj.toX).appTop.hom (B.obj.thickening.immersion.appTop.hom a) := rfl

variable [IsAffine S.X]

/-- **The augmentation is the inverse of the structural map `Γ(X, ⊤) → Γ(T, ⊤)/I_T(⊤)` on
classes**: the structural map sends the augmentation of `a` to the class of `a`. -/
theorem wholeSectionsToQuotient_thickeningAugmentation (B : CrystallineThickening S)
    [IsIso B.obj.toX] (a : Γ(B.obj.thickening.target.scheme, ⊤)) :
    wholeSectionsToQuotient B.obj (thickeningAugmentation B a) =
      Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B.obj.thickening) a := by
  refine B.obj.thickening.sectionsQuotientEquiv.injective ?_
  rw [sectionsQuotientEquiv_wholeSectionsToQuotient, SchemeThickening.sectionsQuotientEquiv_mk,
    thickeningAugmentation_apply, toX_appTop_inv_appTop]

/-- **The augmentation of `a` is the element of `Γ(X, ⊤)` which the structural map sends to the
class of `a`.** -/
theorem thickeningAugmentation_eq_of_wholeSectionsToQuotient (B : CrystallineThickening S)
    [IsIso B.obj.toX] {a : Γ(B.obj.thickening.target.scheme, ⊤)} {c : Γ(S.X, ⊤)}
    (h : wholeSectionsToQuotient B.obj c =
      Ideal.Quotient.mk (SchemeThickening.sectionsIdeal B.obj.thickening) a) :
    thickeningAugmentation B a = c := by
  have h' := congrArg B.obj.thickening.sectionsQuotientEquiv h
  rw [sectionsQuotientEquiv_wholeSectionsToQuotient,
    SchemeThickening.sectionsQuotientEquiv_mk] at h'
  rw [thickeningAugmentation_apply, ← h', Stacks.Thickenings.appTop_comp_apply,
    IsIso.inv_hom_id, Scheme.Hom.id_appTop]
  rfl

/-- **The augmentation is natural**: for a morphism `k : B ⟶ B'` of `Cris(X/S)` between objects
over the whole of `X`, augmenting the restriction of `b` along `k` is augmenting `b`. -/
theorem thickeningAugmentation_crysRingMap {B B' : CrystallineThickening S} [IsIso B.obj.toX]
    [IsIso B'.obj.toX] (k : B ⟶ B') (b : Γ(B'.obj.thickening.target.scheme, ⊤)) :
    thickeningAugmentation B (crysRingMap S k.hom b) = thickeningAugmentation B' b := by
  refine thickeningAugmentation_eq_of_wholeSectionsToQuotient B ?_
  rw [← wholeQuotientMap_comp_wholeSectionsToQuotient k.hom, RingHom.comp_apply,
    wholeSectionsToQuotient_thickeningAugmentation, wholeQuotientMap, Ideal.quotientMap_mk]
  rfl

/-- The augmentation is unchanged by restriction along the identity, the case `k = 𝟙` of
`thickeningAugmentation_crysRingMap`. -/
theorem thickeningAugmentation_crysRingMap_id (B : CrystallineThickening S) [IsIso B.obj.toX]
    (b : Γ(B.obj.thickening.target.scheme, ⊤)) :
    thickeningAugmentation B (crysRingMap S (𝟙 B : B ⟶ B).hom b) = thickeningAugmentation B b :=
  thickeningAugmentation_crysRingMap (𝟙 B) b

/-! ### The levels `T_e` -/

variable [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- The objects `T(n)_e` of the system of [Stacks, Tag 07JN] are thickenings of the whole of
`X`. -/
instance isIso_levelObj_toX (n e : ℕ) : IsIso (levelObj hp n e).obj.toX :=
  isWholeSpaceSystem_wholeSpaceSystem S hp n e

/-- **On the level `T_e`, the augmentation of the reduction of a polynomial `q` of the presentation
algebra is its image `g(q)` in `C = Γ(X, ⊤)`.** -/
theorem thickeningAugmentation_envLevelMap (e : ℕ)
    (q : MvPolynomial (Fin 1 × wholeSpaceIndex S hp) (affineSituation S hp).A) :
    thickeningAugmentation (levelObj hp 0 e) (envLevelMap hp 0 e
        ((tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
          0).algebraMap.toRingHom q)) =
      tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0 q := by
  set Y := wholeSpaceSystemLevel hp 0 e
  set ε := (affineIsCrystalline hp).ι.mapIso ((wholeSiteEquivLittleAffine hp).counitIso.app Y)
  set r := envLevelMap hp 0 e
    ((tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
      0).algebraMap.toRingHom q)
  refine thickeningAugmentation_eq_of_wholeSectionsToQuotient _ ?_
  have h1 : wholeSpaceSystemLevelRingEquiv hp 0 e r = Ideal.Quotient.mk _
      ((tensorPowerEnvelopeThickening (affineSituation S hp) (wholeSpacePresentation S hp)
        (wholeSpacePresentation_surjective S hp) 0).presentationMap q) := by
    apply (Ideal.quotientEquiv _ _ (wholeSpaceSystemEnvelopeRingEquiv hp 0)
      (wholeSpaceSystemEnvelope_pAdicIdeal_pow_map hp 0 _)).injective
    refine (wholeSpaceEnvelopeRingLevelEquiv_apply hp 0 e r).symm.trans ?_
    rw [Ideal.quotientEquiv_mk, wholeSpaceSystemEnvelopeRingEquiv_presentationMap]
    exact (wholeSpaceEnvelopeRingLevelEquiv hp 0 e).apply_symm_apply _
  have h2 : Ideal.Quotient.mk Y.obj.ring.ideal (ε.hom.hom r) =
      Y.obj.toQuotient (tensorPowerPresentation (affineSituation S hp)
        (wholeSpacePresentation S hp) 0 q) := by
    change _ = levelQuotientMap _ _ _ _ ((wholeSpaceSystemEnvelope hp 0).toQuotient _)
    rw [CompletedEnvelopeThickening.toQuotient_apply, levelQuotientMap_mk]
    exact congrArg _ h1
  have h3 := DividedPowerThickening.mk_hom_of_mk_eq_toQuotient ε.inv h2
  rw [show ε.inv.hom (ε.hom.hom r) = r from
    (DividedPowerThickening.ringEquivOfIso ε).symm_apply_apply r] at h3
  exact h3.symm

/-- **A morphism `k : B ⟶ T_e` from an object over the whole of `X` respects the maps from the
presentation algebra to `C`**: augmenting the restriction along `k` of the reduction of a
polynomial `q` gives its image `g(q)` in `C = Γ(X, ⊤)`. -/
theorem thickeningAugmentation_crysRingMap_envLevelMap {B : CrystallineThickening S}
    [IsIso B.obj.toX] (e : ℕ) (k : B ⟶ levelObj hp 0 e)
    (q : MvPolynomial (Fin 1 × wholeSpaceIndex S hp) (affineSituation S hp).A) :
    thickeningAugmentation B (crysRingMap S k.hom (envLevelMap hp 0 e
        ((tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
          0).algebraMap.toRingHom q))) =
      tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0 q :=
  (thickeningAugmentation_crysRingMap k _).trans (thickeningAugmentation_envLevelMap hp e q)

/-! ### The smooth lifting of Remark [Stacks, Tag 07MW] -/

namespace Situation07MW

variable (T : Situation07MW S)

/-- The map to `X` of the smooth lifting `(X, Y, γ)` is the identity, an isomorphism. -/
instance isIso_crystallineThickening_toX : IsIso T.crystallineThickening.obj.toX := by
  change IsIso (𝟙 S.X)
  infer_instance

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The augmentation of the smooth lifting `(X, Y, γ)` is restriction along `X ⟶ Y`.** -/
theorem thickeningAugmentation_crystallineThickening
    (b : Γ(T.crystallineThickening.obj.thickening.target.scheme, ⊤)) :
    thickeningAugmentation T.crystallineThickening b = T.toY.appTop.hom b := by
  rw [thickeningAugmentation_apply]
  change (inv (𝟙 S.X)).appTop.hom (T.toY.appTop.hom b) = _
  rw [IsIso.inv_id, Scheme.Hom.id_appTop]
  rfl

/-- **A morphism `k : (X, Y, γ) ⟶ T_e` from the smooth lifting respects the maps to `C`**: the
restriction to `X` of the restriction along `k` of the reduction of a polynomial `q` is its image
`g(q)` in `C = Γ(X, ⊤)`. -/
theorem toY_appTop_crysRingMap_envLevelMap (e : ℕ)
    (k : T.crystallineThickening ⟶ levelObj hp 0 e)
    (q : MvPolynomial (Fin 1 × wholeSpaceIndex S hp) (affineSituation S hp).A) :
    T.toY.appTop.hom (crysRingMap S k.hom (envLevelMap hp 0 e
        ((tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
          0).algebraMap.toRingHom q))) =
      tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) 0 q :=
  (thickeningAugmentation_crystallineThickening T _).symm.trans
    (thickeningAugmentation_crysRingMap_envLevelMap hp e k q)

end Situation07MW

end Crystalline.GlobalCrystallineSituation.SmallSite

end
