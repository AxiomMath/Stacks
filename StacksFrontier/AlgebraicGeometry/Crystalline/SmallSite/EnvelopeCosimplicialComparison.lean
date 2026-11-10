module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDividedPowerForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceEnvelopeRingBridge

/-!
# The two cosimplicial structures on `D(•)` agree

There are two cosimplicial structures on the completed divided power envelopes `D(n)` of the
`(n + 1)`-fold tensor power presentations:

* `Crystalline.envelopeCosimplicial` is the cosimplicial object of the completed affine
  crystalline site `Cris^∧(C/A)` whose structure map along `φ : ⦋n⦌ ⟶ ⦋m⦌` is the map out of the
  coproduct of [Stacks, Tag 07L4] whose `j`-th component is the `φ(j)`-th coprojection.
* `Crystalline.cosimplicialEnvelopeRing` is the cosimplicial ring whose structure map is the
  completion `Crystalline.adicCompletionRingMap` of the reindexing `Crystalline.envelopeReindex`
  of the variables.

The degreewise isomorphism `Crystalline.tensorPowerEnvelopeThickeningRingEquiv` intertwines the
two.

## Main definitions

* `Crystalline.envelopeCosimplicialRingMapThickening`: the structure map of
  `Crystalline.cosimplicialEnvelopeRing`, as a morphism `D(n) ⟶ D(m)` of the site-theoretic
  realisations.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceEnvelopeRingLevelEquiv`: the
  section ring of the level `(n, e)` of the system of [Stacks, Tag 07JN] is the finite level
  `N + e` of the degree `n` of `...SmallSite.wholeSpaceEnvelopeRing`.

## Main results

* `Crystalline.envelopeCosimplicial_map_eq`: the structure map of
  `Crystalline.envelopeCosimplicial` is the transported structure map of
  `Crystalline.cosimplicialEnvelopeRing`.
* `Crystalline.tensorPowerEnvelopeThickeningRingEquiv_envelopeCosimplicial_map`: the
  identification of the two realisations of `D(n)` intertwines the two cosimplicial structures.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystemEnvelopeRingEquiv_map`: the
  same statement for the system of [Stacks, Tag 07JN] and the cosimplicial ring
  `...SmallSite.wholeSpaceEnvelopeRing`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceEnvelopeRingLevelEquiv_map`: the
  identification of the section rings of the levels with the finite levels of `D(*)` is natural
  in the cosimplicial direction.

## References

* [Stacks Project, Tag 07L4](https://stacks.math.columbia.edu/tag/07L4)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u v w r

noncomputable section

namespace DividedPowerRing

/-- The divided power morphism `R' → S'` obtained from a divided power morphism `R → S` by
transport along equalities `R' = R` and `S' = S` of divided power rings. -/
def dpMorphismCongr {R R' S S' : DividedPowerRing.{r}} (hR : R' = R) (hS : S' = S)
    (q : DividedPowers.DPMorphism R.dividedPowers S.dividedPowers) :
    DividedPowers.DPMorphism R'.dividedPowers S'.dividedPowers := by
  cases hR
  cases hS
  exact q

/-- The transported morphism `DividedPowerRing.dpMorphismCongr hR hS q` is `q` read through the
two isomorphisms of carriers. -/
theorem ringEquivOfEq_dpMorphismCongr {R R' S S' : DividedPowerRing.{r}}
    (hR : R' = R) (hS : S' = S)
    (q : DividedPowers.DPMorphism R.dividedPowers S.dividedPowers) (x : (R' : Type r)) :
    ringEquivOfEq hS (dpMorphismCongr hR hS q x) = q (ringEquivOfEq hR x) := by
  cases hR
  cases hS
  rfl

end DividedPowerRing

namespace Crystalline

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (hg : Function.Surjective g)

/-! ### The map from the presentation algebra, on constants and on the quotient -/

/-- **The map from the presentation algebra agrees with the structure map from the base on the
constants.** -/
theorem CompletedEnvelopeThickening.presentationMap_C (X : CompletedEnvelopeThickening s g hg)
    (a : s.A) :
    X.presentationMap (MvPolynomial.C a) = X.thickening.fromBase.toRingHom a := by
  rcases X with ⟨hp, ⟨R, b, hc, t, ht, hbij⟩, hr, m, hm, ha, hq⟩
  dsimp only at hr hm ha ⊢
  subst R
  change m (algebraMap s.A (MvPolynomial ι s.A) a) = b.toRingHom a
  rw [eq_of_heq hm, eq_of_heq ha]
  exact congrArg
    (algebraMap (polynomialDividedPowerEnvelope s g).object
      (pAdicCompletedDividedPowerEnvelope s g hg))
    (RingHom.congr_fun (polynomialDividedPowerEnvelope s g).algebraMap_comp a)

/-- **The structural identification of `C` with `D / J̄` sends the image of a polynomial to the
class of its image under the map from the presentation algebra.** -/
theorem CompletedEnvelopeThickening.toQuotient_apply (X : CompletedEnvelopeThickening s g hg)
    (q : MvPolynomial ι s.A) :
    X.thickening.toQuotient (g q) =
      Ideal.Quotient.mk X.thickening.ring.ideal (X.presentationMap q) := by
  rcases X with ⟨hp, ⟨R, b, hc, t, ht, hbij⟩, hr, m, hm, ha, hq⟩
  dsimp only at hr hm hq ⊢
  subst R
  change t (g q) = Ideal.Quotient.mk (completedEnvelopeDPRing s g hg hp).ideal (m q)
  rw [eq_of_heq hm]
  exact eq_of_heq (hq q)

/-! ### The reindexing of the variables -/

/-- The reindexing of the variables commutes with the two surjections onto `C`, read
pointwise. -/
theorem tensorPowerPresentation_rename_simplexVariableMap {n m : SimplexCategory} (φ : n ⟶ m)
    (q : MvPolynomial (Fin (n.len + 1) × ι) s.A) :
    tensorPowerPresentation s g m.len
        (MvPolynomial.rename (simplexVariableMap (ι := ι) φ) q) =
      tensorPowerPresentation s g n.len q := by
  have h : (tensorPowerPresentation s g m.len).comp
      (MvPolynomial.rename (simplexVariableMap (ι := ι) φ)) =
      tensorPowerPresentation s g n.len := by
    ext x
    simp [tensorPowerPresentation, simplexVariableMap]
  exact DFunLike.congr_fun h q

/-- **The reindexing of the variables carries the `j`-th polynomial coprojection to the
`φ(j)`-th one.**  Both are renamings of the variables of `P`, and the two renamings agree
because `x_i ↦ x_i(j) ↦ x_i(φ(j))`. -/
theorem rename_simplexVariableMap_mvPolynomialCoprojection {n m : SimplexCategory} (φ : n ⟶ m)
    (j : Fin (n.len + 1)) (p : MvPolynomial ι s.A) :
    MvPolynomial.rename (simplexVariableMap (ι := ι) φ)
        (mvPolynomialCoprojection (s.A : Type u) (n := n.len) j p) =
      mvPolynomialCoprojection (s.A : Type u) (n := m.len) (φ.toOrderHom j) p := by
  simp [mvPolynomialCoprojection, simplexVariableMap, MvPolynomial.rename_rename,
    Function.comp_def]

/-! ### The structure map of `D(*)` as a morphism of the realisations -/

/-- The ring of the site-theoretic `D(n)` is the divided power ring
`Crystalline.completedTensorPowerDividedPowerRing s g hg n`. -/
theorem tensorPowerEnvelopeThickening_ring_eq (n : ℕ) :
    (tensorPowerEnvelopeThickening s g hg n).thickening.ring =
      completedTensorPowerDividedPowerRing s g hg n :=
  (tensorPowerEnvelopeThickening s g hg n).ring_eq

/-- The ring isomorphism `tensorPowerEnvelopeThickeningRingEquiv` is the one induced by the
equality `tensorPowerEnvelopeThickening_ring_eq` of the two divided power rings. -/
theorem tensorPowerEnvelopeThickeningRingEquiv_eq (n : ℕ) :
    tensorPowerEnvelopeThickeningRingEquiv s g hg n =
      DividedPowerRing.ringEquivOfEq (tensorPowerEnvelopeThickening_ring_eq s g hg n) := rfl

/-- **The structure map `D(n) → D(m)` of `Crystalline.cosimplicialEnvelopeRing`, read as a
divided power morphism of the rings of the site-theoretic realisations of `D(n)` and `D(m)`.** -/
def envelopeCosimplicialRingMapHom {n m : SimplexCategory} (φ : n ⟶ m) :
    (tensorPowerEnvelopeThickening s g hg n.len).thickening.ring ⟶
      (tensorPowerEnvelopeThickening s g hg m.len).thickening.ring :=
  DividedPowerRing.dpMorphismCongr (tensorPowerEnvelopeThickening_ring_eq s g hg n.len)
    (tensorPowerEnvelopeThickening_ring_eq s g hg m.len)
    (DividedPowers.DPMorphism.mk' (cosimplicialEnvelopeRing_isDPMorphism s g hg φ))

/-- **The transported map is the structure map of `D(*)` read through the identifications.** -/
theorem ringEquiv_envelopeCosimplicialRingMapHom {n m : SimplexCategory} (φ : n ⟶ m)
    (x : ((tensorPowerEnvelopeThickening s g hg n.len).thickening.ring : Type (max u w))) :
    tensorPowerEnvelopeThickeningRingEquiv s g hg m.len
        (envelopeCosimplicialRingMapHom s g hg φ x) =
      (cosimplicialEnvelopeRing s g hg).map φ
        (tensorPowerEnvelopeThickeningRingEquiv s g hg n.len x) :=
  DividedPowerRing.ringEquivOfEq_dpMorphismCongr _ _ _ x

/-- **The transported map renames the variables on the image of the presentation algebra.** -/
theorem envelopeCosimplicialRingMapHom_presentationMap {n m : SimplexCategory} (φ : n ⟶ m)
    (q : MvPolynomial (Fin (n.len + 1) × ι) s.A) :
    envelopeCosimplicialRingMapHom s g hg φ
        ((tensorPowerEnvelopeThickening s g hg n.len).presentationMap q) =
      (tensorPowerEnvelopeThickening s g hg m.len).presentationMap
        (MvPolynomial.rename (simplexVariableMap (ι := ι) φ) q) := by
  apply (tensorPowerEnvelopeThickeningRingEquiv s g hg m.len).injective
  rw [ringEquiv_envelopeCosimplicialRingMapHom,
    tensorPowerEnvelopeThickeningRingEquiv_presentationMap,
    tensorPowerEnvelopeThickeningRingEquiv_presentationMap,
    cosimplicialEnvelopeRing_map_polynomial]

/-- **The structure map of `Crystalline.cosimplicialEnvelopeRing` as a morphism
`D(n) ⟶ D(m)` of the site-theoretic realisations in `Cris^∧(C/A)`.** -/
def envelopeCosimplicialRingMapThickening {n m : SimplexCategory} (φ : n ⟶ m) :
    (tensorPowerEnvelopeThickening s g hg n.len).thickening ⟶
      (tensorPowerEnvelopeThickening s g hg m.len).thickening where
  hom := envelopeCosimplicialRingMapHom s g hg φ
  fromBase_comp := by
    apply DividedPowers.DPMorphism.ext
    funext a
    change envelopeCosimplicialRingMapHom s g hg φ
        ((tensorPowerEnvelopeThickening s g hg n.len).thickening.fromBase.toRingHom a) =
      (tensorPowerEnvelopeThickening s g hg m.len).thickening.fromBase.toRingHom a
    rw [← CompletedEnvelopeThickening.presentationMap_C,
      envelopeCosimplicialRingMapHom_presentationMap, MvPolynomial.rename_C,
      CompletedEnvelopeThickening.presentationMap_C]
  toQuotient_comp := by
    apply RingHom.ext
    intro c
    obtain ⟨q, rfl⟩ := tensorPowerPresentation_surjective s g hg n.len c
    change DividedPowerRing.quotientRingHom (envelopeCosimplicialRingMapHom s g hg φ)
        ((tensorPowerEnvelopeThickening s g hg n.len).thickening.toQuotient
          (tensorPowerPresentation s g n.len q)) = _
    rw [CompletedEnvelopeThickening.toQuotient_apply, DividedPowerRing.quotientRingHom_mk,
      envelopeCosimplicialRingMapHom_presentationMap,
      ← CompletedEnvelopeThickening.toQuotient_apply,
      tensorPowerPresentation_rename_simplexVariableMap]

/-! ### The comparison -/

/-- **The transported structure map has the coprojections of `Crystalline.envelopeCosimplicial`
as its restrictions**: the `j`-th coprojection `D ⟶ D(n)` followed by it is the `φ(j)`-th
coprojection `D ⟶ D(m)`. -/
theorem envelopeCosimplicialRingMapThickening_coprojection {n m : SimplexCategory} (φ : n ⟶ m)
    (j : Fin (n.len + 1)) :
    completedEnvelopeCoprojection s g hg n.len j ≫
        envelopeCosimplicialRingMapThickening s g hg φ =
      completedEnvelopeCoprojection s g hg m.len (φ.toOrderHom j) := by
  apply completedEnvelope_hom_ext s g hg (completedEnvelopeThickening s g hg)
  apply RingHom.ext
  intro p
  change envelopeCosimplicialRingMapHom s g hg φ
      ((completedEnvelopeCoprojection s g hg n.len j).hom.toRingHom
        ((completedEnvelopeThickening s g hg).presentationMap p)) =
    (completedEnvelopeCoprojection s g hg m.len (φ.toOrderHom j)).hom.toRingHom
      ((completedEnvelopeThickening s g hg).presentationMap p)
  rw [(completedEnvelopeCoprojections s g hg n.len).2 j p,
    envelopeCosimplicialRingMapHom_presentationMap,
    (completedEnvelopeCoprojections s g hg m.len).2 (φ.toOrderHom j) p,
    rename_simplexVariableMap_mvPolynomialCoprojection]

/-- **The structure map of `Crystalline.envelopeCosimplicial` is the transported structure map of
`Crystalline.cosimplicialEnvelopeRing`.** -/
theorem envelopeCosimplicial_map_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    ((envelopeCosimplicial s g hg).map φ :
        (tensorPowerEnvelopeThickening s g hg n.len).thickening ⟶
          (tensorPowerEnvelopeThickening s g hg m.len).thickening) =
      envelopeCosimplicialRingMapThickening s g hg φ := by
  refine envelopeCoproduct_hom_ext s g hg _ _ fun j => ?_
  exact (envelopeCosimplicial_coprojection_comp_map s g hg φ j).trans
    (envelopeCosimplicialRingMapThickening_coprojection s g hg φ j).symm

/-- **The two cosimplicial structures on `D(•)` agree.**

The degreewise identification `Crystalline.tensorPowerEnvelopeThickeningRingEquiv` of the ring of
the object `D(n)` of `Cris^∧(C/A)` with the degree `n` of the cosimplicial ring
`Crystalline.cosimplicialEnvelopeRing` intertwines the structure map of
`Crystalline.envelopeCosimplicial` with the structure map of
`Crystalline.cosimplicialEnvelopeRing`. -/
theorem tensorPowerEnvelopeThickeningRingEquiv_envelopeCosimplicial_map
    {n m : SimplexCategory} (φ : n ⟶ m)
    (x : ((tensorPowerEnvelopeThickening s g hg n.len).thickening.ring : Type (max u w))) :
    tensorPowerEnvelopeThickeningRingEquiv s g hg m.len
        (((envelopeCosimplicial s g hg).map φ).hom.toRingHom x) =
      (cosimplicialEnvelopeRing s g hg).map φ
        (tensorPowerEnvelopeThickeningRingEquiv s g hg n.len x) :=
  by
  rw [envelopeCosimplicial_map_eq]
  exact ringEquiv_envelopeCosimplicialRingMapHom s g hg φ x

/-- **The structure map of `Crystalline.envelopeCosimplicial` renames the variables on the image
of the presentation algebra.** -/
theorem envelopeCosimplicial_map_presentationMap {n m : SimplexCategory} (φ : n ⟶ m)
    (q : MvPolynomial (Fin (n.len + 1) × ι) s.A) :
    ((envelopeCosimplicial s g hg).map φ).hom.toRingHom
        ((tensorPowerEnvelopeThickening s g hg n.len).presentationMap q) =
      (tensorPowerEnvelopeThickening s g hg m.len).presentationMap
        (MvPolynomial.rename (simplexVariableMap (ι := ι) φ) q) :=
  by
  rw [envelopeCosimplicial_map_eq]
  exact envelopeCosimplicialRingMapHom_presentationMap s g hg φ q

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The identification of the two `D(n)` intertwines the cosimplicial structure the system of
[Stacks, Tag 07JN] is built from with the cosimplicial structure of
`...SmallSite.wholeSpaceEnvelopeRing`.** -/
theorem wholeSpaceSystemEnvelopeRingEquiv_map {n m : SimplexCategory} (φ : n ⟶ m)
    (x : ((wholeSpaceSystemEnvelope hp n.len).ring : Type u)) :
    wholeSpaceSystemEnvelopeRingEquiv hp m.len
        (((_root_.Crystalline.envelopeCosimplicial (affineSituation S hp)
          (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp)).map φ).hom.toRingHom x) =
      (wholeSpaceEnvelopeRing hp).map φ (wholeSpaceSystemEnvelopeRingEquiv hp n.len x) :=
  _root_.Crystalline.tensorPowerEnvelopeThickeningRingEquiv_envelopeCosimplicial_map
    (affineSituation S hp) (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp) φ x

/-! ### The identification at the finite levels -/

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The identification `...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` of the rings of the two
realisations of `D(n)` maps the `k`-th power of the `p`-adic ideal of one onto that of the
other. -/
theorem wholeSpaceSystemEnvelope_pAdicIdeal_pow_map (n k : ℕ) :
    DividedPowers.pAdicIdeal
        (A := ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u))
        (affineSituation S hp).p ^ k =
      (DividedPowers.pAdicIdeal (A := ((wholeSpaceSystemEnvelope hp n).ring : Type u))
          (affineSituation S hp).p ^ k).map
        (wholeSpaceSystemEnvelopeRingEquiv hp n : _ →+* _) := by
  rw [Ideal.map_pow, _root_.Crystalline.pAdicIdeal_map_ringHom]

/-- **The section ring of the level `(n, e)` of the system of [Stacks, Tag 07JN] is the finite
level `N + e` of the degree `n` of the cosimplicial ring `...SmallSite.wholeSpaceEnvelopeRing`.**

`...SmallSite.wholeSpaceSystemLevelRingEquiv` identifies it with the level of the ring of the
object `D(n)` the system is built from, and `...SmallSite.wholeSpaceSystemEnvelopeRingEquiv`
identifies that ring with the degree `n` of `D(*)`; this is their composite. -/
def wholeSpaceEnvelopeRingLevelEquiv (n e : ℕ) :
    ((structureSheaf S).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e)) : Type u) ≃+*
      (((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u) ⧸
        DividedPowers.pAdicIdeal
            (A := ((wholeSpaceEnvelopeRing hp).obj (SimplexCategory.mk n) : Type u))
            (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) :=
  (wholeSpaceSystemLevelRingEquiv hp n e).trans
    (Ideal.quotientEquiv _ _ (wholeSpaceSystemEnvelopeRingEquiv hp n)
      (wholeSpaceSystemEnvelope_pAdicIdeal_pow_map hp n _))

/-- `wholeSpaceEnvelopeRingLevelEquiv` sends a section to its image under
`wholeSpaceSystemLevelRingEquiv` followed by the map of quotients induced by
`wholeSpaceSystemEnvelopeRingEquiv`. -/
theorem wholeSpaceEnvelopeRingLevelEquiv_apply (n e : ℕ)
    (x : (structureSheaf S).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e))) :
    wholeSpaceEnvelopeRingLevelEquiv hp n e x =
      Ideal.quotientEquiv _ _ (wholeSpaceSystemEnvelopeRingEquiv hp n)
        (wholeSpaceSystemEnvelope_pAdicIdeal_pow_map hp n _)
        (wholeSpaceSystemLevelRingEquiv hp n e x) :=
  rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The structure map of `D(*)` carries the `k`-th power of the `p`-adic ideal into the `k`-th
power of the `p`-adic ideal. -/
theorem wholeSpaceEnvelopeRing_map_pAdicIdeal_pow_le {n m : SimplexCategory} (φ : n ⟶ m)
    (k : ℕ) :
    DividedPowers.pAdicIdeal (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u))
        (affineSituation S hp).p ^ k ≤
      (DividedPowers.pAdicIdeal (A := ((wholeSpaceEnvelopeRing hp).obj m : Type u))
          (affineSituation S hp).p ^ k).comap ((wholeSpaceEnvelopeRing hp).map φ).hom := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, _root_.Crystalline.pAdicIdeal_map_ringHom]

/-- **The identification of the section rings of the levels with the finite levels of `D(*)` is
natural in the cosimplicial direction.**

Restricting a section of `𝒪_{X/S}` along the transition map `T(m)_e ⟶ T(n)_e` of the system of
[Stacks, Tag 07JN] becomes, through `...SmallSite.wholeSpaceEnvelopeRingLevelEquiv`, the
reduction to the level `N + e` of the structure map `D(n) ⟶ D(m)` of
`...SmallSite.wholeSpaceEnvelopeRing`. -/
theorem wholeSpaceEnvelopeRingLevelEquiv_map {n m : ℕ}
    (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (e : ℕ)
    (x : (structureSheaf S).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))).obj e))) :
    wholeSpaceEnvelopeRingLevelEquiv hp m e
        (((structureSheaf S).obj.map
          (((wholeSpaceSystem S hp).map φ.op).app e).op).hom x) =
      Ideal.quotientMap _ ((wholeSpaceEnvelopeRing hp).map φ).hom
          (wholeSpaceEnvelopeRing_map_pAdicIdeal_pow_le hp φ _)
        (wholeSpaceEnvelopeRingLevelEquiv hp n e x) := by
  obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (wholeSpaceSystemLevelRingEquiv hp n e x)
  rw [wholeSpaceEnvelopeRingLevelEquiv_apply, wholeSpaceEnvelopeRingLevelEquiv_apply,
    wholeSpaceSystemLevelRingEquiv_map, ← hd, Ideal.quotientEquiv_mk, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (wholeSpaceSystemEnvelopeRingEquiv_map hp φ d)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
