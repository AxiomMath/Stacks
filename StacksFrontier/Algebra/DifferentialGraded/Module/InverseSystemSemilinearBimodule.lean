module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorRestrictLeft
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorPlainIsoNatural
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemStrictModule

/-!
# Inverse systems of differential graded bimodules from semilinear transition homomorphisms

An inverse system of differential graded bimodules in the sense of
`DifferentialGraded.BimoduleSystem` carries, as data, the comparison maps
`M_m ⊗^𝐋_{A_m} X|_{A_m} ⟶ M_n ⊗^𝐋_{A_n} X` of the derived tensor functors, subject to the one
compatibility `DifferentialGraded.BimoduleSystem.cmp_trans` that says they compose. This file
constructs such a system from the datum one actually has in practice — bimodules `M_n` over a
strict inverse system of differential graded algebras together with *semilinear* transition
homomorphisms `M_m ⟶ M_n|_{τ_{m,n}}` composing on the nose — by taking for the comparison maps
the derived comparisons `DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of the plain
ones.

The compatibility is then not assumed but proved, and the comparison maps of the resulting system
are the derived comparisons *by definition*. That is exactly the hypothesis `hcmp` of
`Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance` (Tag 0GZJ) and of
`DifferentialGraded.BimoduleSystem.towerMap_ofSemilinear_towerMap`, so those results apply to
every system built here, by `rfl`.

## Main definitions

* `DifferentialGraded.StrictBimoduleSystem`: a strict inverse system of differential graded
  bimodules — a bimodule `M_n` over `A_n` for every `n` and a semilinear homomorphism
  `M_m ⟶ M_n|_{τ_{m,n}}` for every `n ≤ m`, whose underlying maps compose.
* `DifferentialGraded.StrictBimoduleSystem.cmp`: its comparison of the derived tensor functors,
  the derived comparison of the plain comparison attached to the semilinear transition.
* `DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem`: the inverse system of differential
  graded bimodules it gives.
* `DifferentialGraded.Bimodule.regularRestrictedBimodule` and
  `DifferentialGraded.Bimodule.regularRestrictedIdHom`: a differential graded algebra `B` as a
  bimodule over an algebra mapping to it, and the identity of `B` as a semilinear homomorphism
  between two such readings.
* `DifferentialGraded.StrictBimoduleSystem.ofRegularId`: a strict inverse system of bimodules
  from a compatible family of homomorphisms `ψ_n : A_n → B`, namely `B` with `A_n` acting on the
  left through `ψ_n` and the identity of `B` for every transition.

## Main results

* `DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear_comp_app`: the plain comparison
  attached to a composite of semilinear homomorphisms is the composite of the plain comparisons.
  This is the whole mathematical content of the compatibility below; everything else is
  bookkeeping in a localized category.
* `DifferentialGraded.Bimodule.restrictTensorHomotopyTrans_comp_app` and
  `DifferentialGraded.Bimodule.derivedTensorRestrictTrans_comp_app`: the same statement on the
  homotopy categories and on the derived categories.
* `DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem_cmp`: the comparison maps of the
  system built here are the derived comparisons of the plain ones, by `rfl`.

## Implementation notes

*Why the composite is characterised and not computed.* A comparison of the derived tensor
functors over two different algebras is a lift through the universal property of a left derived
functor (Tag 09LS), so two such comparisons are equal as soon as their composites with the
comparison of Tag 0BZ2 agree; that is
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_unique`, and
`CategoryTheory.Functor.leftDerived_ext` is the form of it used below. The identity on the derived
categories is therefore reduced to one on the homotopy categories, and that one to the plain
identity on pure tensors, which is where the semilinear homomorphisms actually compose.

*Abstract diagram lemmas.* The reduced identity is a composite in a localized category, where
`CategoryTheory.Category.assoc` does not rewrite — the two sides present
`CategoryTheory.Quiver.Hom` at different instance paths. It is therefore proved for abstract
categories and functors in
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_comp_aux` and instantiated by `exact`,
which is the device of `DifferentialGradedModule.derivedTrans_comp_aux`.

*The transitions are indexed by all pairs.* `DifferentialGraded.BimoduleSystem.cmp_trans` is
asked for every triple `n ≤ m ≤ k` of indices, including the degenerate ones, so the semilinear
transitions are likewise given for every pair `n ≤ m` and asked to compose, exactly as in
`DifferentialGraded.StrictModuleSystem`. The composition is asked of the underlying maps rather
than as an equation of homomorphisms of bimodules, which is what keeps it free of any transport
along an equality of objects: the underlying right `B`-module of a restricted bimodule is the
original one, so all three underlying maps already have the same source and target.

## References

* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) is the derived tensor
  product and its universal property, [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) the
  comparison with the plain tensor product, [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM)
  the plain tensor product, [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) restriction of
  scalars and [Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ) differential graded
  bimodules.
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI) and
  [Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) are where such a system is used.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra

namespace Bimodule

variable {R : Type u} [CommRing R] {Ak Am An B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The plain comparison of a composite of semilinear homomorphisms -/

/-- **The plain comparison attached to a composite of semilinear homomorphisms is the composite
of the plain comparisons.** Let `χ : A_k → A_m` and `σ : A_m → A_n` be homomorphisms of
differential graded algebras, let `P`, `Q` and `S` be bimodules over `A_k`, `A_m` and `A_n`, let
`g : P ⟶ Q|_χ` and `f : Q ⟶ S|_σ` be semilinear homomorphisms and let `gf : P ⟶ S|_{σ ∘ χ}` have
for underlying map the composite of theirs. Then the comparison
`DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear` of `gf` is the comparison of `g`
followed by the comparison of `f`.

Both sides send the pure tensor `y ⊗ p` to `y ⊗ f(g(p))`, and a homomorphism out of a tensor
product is determined by its values on pure tensors. -/
theorem tensorCompNatTransOfSemilinear_comp_app (χ : Ak.Hom Am) (σ : Am.Hom An)
    (P : Bimodule Ak B) (Q : Bimodule Am B) (S : Bimodule An B)
    (g : P ⟶ Bimodule.restrictLeft χ Q) (f : Q ⟶ Bimodule.restrictLeft σ S)
    (gf : P ⟶ Bimodule.restrictLeft (σ.comp χ) S)
    (hgf : ∀ y : P.rightModule.M, gf.rightHom.toFun y = f.rightHom.toFun (g.rightHom.toFun y))
    (Y : DifferentialGradedModule.{u, u, u} An) :
    (tensorCompNatTransOfSemilinear (σ.comp χ) P S gf).app Y =
      (tensorCompNatTransOfSemilinear χ P Q g).app ((restrictScalarsFunctor σ).obj Y) ≫
        (tensorCompNatTransOfSemilinear σ Q S f).app Y := by
  refine tensorObj_hom_ext' P ((restrictScalarsFunctor (σ.comp χ)).obj Y) _ _ fun x y => ?_
  refine (tensorCompNatTransOfSemilinear_app_pure (σ.comp χ) P S gf Y x y).trans ?_
  refine (congrArg (((tensorDGFunctor S).pure Y).toLinearMap x) (hgf y)).trans ?_
  exact ((congrArg (fun w => ((tensorCompNatTransOfSemilinear σ Q S f).app Y).toFun w)
      (tensorCompNatTransOfSemilinear_app_pure χ P Q g
        ((restrictScalarsFunctor σ).obj Y) x y)).trans
    (tensorCompNatTransOfSemilinear_app_pure σ Q S f Y x (g.rightHom.toFun y))).symm

/-! ### The comparison of a composite on the homotopy categories -/

/-- **Splitting a composite across a cancelling pair.** Stated for an abstract category: in a
quotient or localized category the two sides present `CategoryTheory.Quiver.Hom` at different
instance paths, and `CategoryTheory.Category.assoc` then refuses to rewrite. -/
theorem comp_insert_aux {C : Type*} [Category C] {a b c d u v : C} (i : a ⟶ b) (m₁ : b ⟶ c)
    (q : c ⟶ u) (qi : u ⟶ c) (m₂ : c ⟶ d) (s : d ⟶ v) (hq : q ≫ qi = 𝟙 c) :
    i ≫ (m₁ ≫ m₂) ≫ s = (i ≫ m₁ ≫ q) ≫ (qi ≫ m₂ ≫ s) := by
  have hcancel : q ≫ qi ≫ m₂ ≫ s = m₂ ≫ s := by
    rw [← Category.assoc q qi, hq, Category.id_comp]
  simp only [Category.assoc, hcancel]

/-- **The comparison on the homotopy categories of a composite of semilinear homomorphisms is the
composite of the comparisons.** The homotopy-category comparison
`DifferentialGraded.Bimodule.restrictTensorHomotopyTrans` of a plain comparison which is a
composite of two plain comparisons is the composite of their homotopy-category comparisons.

Every object of the homotopy category is the class of a differential graded module, where the
three comparisons are computed by
`DifferentialGraded.Bimodule.restrictTensorHomotopyTrans_app`; the two inner copies of the
comparison of Tag 09LM for `Q` then cancel. -/
theorem restrictTensorHomotopyTrans_comp_app (χ : Ak.Hom Am) (σ : Am.Hom An)
    (P : Bimodule Ak B) (Q : Bimodule Am B) (S : Bimodule An B)
    (τχ : restrictScalarsFunctor χ ⋙ tensorCompFunctor P ⟶ tensorCompFunctor Q)
    (τσ : restrictScalarsFunctor σ ⋙ tensorCompFunctor Q ⟶ tensorCompFunctor S)
    (τν : restrictScalarsFunctor (σ.comp χ) ⋙ tensorCompFunctor P ⟶ tensorCompFunctor S)
    (hτ : ∀ Y : DifferentialGradedModule.{u, u, u} An,
      τν.app Y = τχ.app ((restrictScalarsFunctor σ).obj Y) ≫ τσ.app Y)
    (Z : HomotopyCategory An) :
    (restrictTensorHomotopyTrans (σ.comp χ) P S τν).app Z =
      (restrictTensorHomotopyTrans χ P Q τχ).app ((restrictScalarsHomotopyFunctor σ).obj Z) ≫
        (restrictTensorHomotopyTrans σ Q S τσ).app Z := by
  obtain ⟨Y⟩ := Z
  show (restrictTensorHomotopyTrans (σ.comp χ) P S τν).app ((toHomotopyCategory An).obj Y) =
    (restrictTensorHomotopyTrans χ P Q τχ).app
        ((toHomotopyCategory Am).obj ((restrictScalarsFunctor σ).obj Y)) ≫
      (restrictTensorHomotopyTrans σ Q S τσ).app ((toHomotopyCategory An).obj Y)
  have hmap : (toHomotopyCategory B).map (τν.app Y) =
      (toHomotopyCategory B).map (τχ.app ((restrictScalarsFunctor σ).obj Y)) ≫
        (toHomotopyCategory B).map (τσ.app Y) :=
    (congrArg (fun w => (toHomotopyCategory B).map w) (hτ Y)).trans
      ((toHomotopyCategory B).map_comp _ _)
  rw [restrictTensorHomotopyTrans_app, restrictTensorHomotopyTrans_app,
    restrictTensorHomotopyTrans_app, hmap]
  exact comp_insert_aux _ _ _ _ _ _
    ((tensorCompFunctor_quotient Q).hom_inv_id_app ((restrictScalarsFunctor σ).obj Y))

/-! ### The comparison of a composite on the derived categories -/

/-- A transport along an equality of an object, composed on the left with a morphism out of that
object, drops out. Stated so that the equality is an argument, since in a localized category the
two names of one object are not recognised by `CategoryTheory.eqToHom_refl` without it. -/
theorem eqToHom_comp_left_eq {C : Type*} [Category C] {X Y : C} (h : X = X) (u : X ⟶ Y) :
    eqToHom h ≫ u = u := by
  rw [eqToHom_refl, Category.id_comp]

/-- **The comparison of the derived tensor functors attached to a composite, for abstract
categories.** The hypotheses are the defining property of the three comparisons (`Hχ`, `Hσ`,
`Hν`), the formula for the comparison of the two restrictions with the restriction along the
composite (`Hrc`) and the composition law on the homotopy categories (`Hs`); the conclusion is
the composition law on the derived categories, evaluated at the image of an object of the
homotopy category, which is where the universal property of a left derived functor leaves it.

It is stated for abstract categories and functors because in a localized category the two sides
of a composition present `CategoryTheory.Quiver.Hom` at different instance paths, so
`CategoryTheory.Category.assoc` refuses to rewrite; it is instantiated at the derived categories
of differential graded modules in
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_comp_app`. -/
theorem derivedTensorRestrictTrans_comp_aux
    {Hn Hm Hk HB Dn Dm Dk E : Type*} [Category Hn] [Category Hm] [Category Hk] [Category HB]
    [Category Dn] [Category Dm] [Category Dk] [Category E]
    {Qn : Hn ⥤ Dn} {Qm : Hm ⥤ Dm} {Qk : Hk ⥤ Dk} {QB : HB ⥤ E}
    {Rσ : Dn ⥤ Dm} {Rχ : Dm ⥤ Dk} {Rν : Dn ⥤ Dk}
    {rσ : Hn ⥤ Hm} {rχ : Hm ⥤ Hk} {rν : Hn ⥤ Hk}
    {Tn : Dn ⥤ E} {Tm : Dm ⥤ E} {Tk : Dk ⥤ E}
    {tn : Hn ⥤ HB} {tm : Hm ⥤ HB} {tk : Hk ⥤ HB}
    (factσ : Qn ⋙ Rσ ≅ rσ ⋙ Qm) (factχ : Qm ⋙ Rχ ≅ rχ ⋙ Qk) (factν : Qn ⋙ Rν ≅ rν ⋙ Qk)
    (e : rσ ⋙ rχ = rν)
    (cun : Qn ⋙ Tn ⟶ tn ⋙ QB) (cum : Qm ⋙ Tm ⟶ tm ⋙ QB) (cuk : Qk ⋙ Tk ⟶ tk ⋙ QB)
    (cχ : Rχ ⋙ Tk ⟶ Tm) (cσ : Rσ ⋙ Tm ⟶ Tn) (cν : Rν ⋙ Tk ⟶ Tn)
    (sχ : rχ ⋙ tk ⟶ tm) (sσ : rσ ⋙ tm ⟶ tn) (sν : rν ⋙ tk ⟶ tn)
    (rc : Rσ ⋙ Rχ ⟶ Rν) (Z : Hn)
    (hfun : (rσ ⋙ rχ) ⋙ Qk = rν ⋙ Qk) (hobj : tk.obj (rν.obj Z) = tk.obj (rχ.obj (rσ.obj Z)))
    (Hχ : cχ.app (Qm.obj (rσ.obj Z)) ≫ cum.app (rσ.obj Z) =
      Tk.map (factχ.hom.app (rσ.obj Z)) ≫
        cuk.app (rχ.obj (rσ.obj Z)) ≫ QB.map (sχ.app (rσ.obj Z)))
    (Hσ : cσ.app (Qn.obj Z) ≫ cun.app Z =
      Tm.map (factσ.hom.app Z) ≫ cum.app (rσ.obj Z) ≫ QB.map (sσ.app Z))
    (Hν : cν.app (Qn.obj Z) ≫ cun.app Z =
      Tk.map (factν.hom.app Z) ≫ cuk.app (rν.obj Z) ≫ QB.map (sν.app Z))
    (Hrc : rc.app (Qn.obj Z) =
      Rχ.map (factσ.hom.app Z) ≫ factχ.hom.app (rσ.obj Z) ≫
        (eqToIso hfun).hom.app Z ≫ factν.inv.app Z)
    (Hs : sν.app Z = eqToHom hobj ≫ sχ.app (rσ.obj Z) ≫ sσ.app Z) :
    (Tk.map (rc.app (Qn.obj Z)) ≫ cν.app (Qn.obj Z)) ≫ cun.app Z =
      (cχ.app (Rσ.obj (Qn.obj Z)) ≫ cσ.app (Qn.obj Z)) ≫ cun.app Z := by
  subst e
  simp only [Functor.comp_obj, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    eqToHom_refl] at Hrc Hs
  have hL : (Tk.map (rc.app (Qn.obj Z)) ≫ cν.app (Qn.obj Z)) ≫ cun.app Z =
      Tk.map (Rχ.map (factσ.hom.app Z) ≫ factχ.hom.app (rσ.obj Z)) ≫
        cuk.app (rχ.obj (rσ.obj Z)) ≫
          QB.map (sχ.app (rσ.obj Z)) ≫ QB.map (sσ.app Z) := by
    rw [Category.assoc, Hν, Hrc, Hs, QB.map_comp, ← Functor.map_comp_assoc, Category.assoc,
      Category.assoc, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, Category.comp_id]
  have hR : (cχ.app (Rσ.obj (Qn.obj Z)) ≫ cσ.app (Qn.obj Z)) ≫ cun.app Z =
      Tk.map (Rχ.map (factσ.hom.app Z) ≫ factχ.hom.app (rσ.obj Z)) ≫
        cuk.app (rχ.obj (rσ.obj Z)) ≫
          QB.map (sχ.app (rσ.obj Z)) ≫ QB.map (sσ.app Z) := by
    have hnat : Tk.map (Rχ.map (factσ.hom.app Z)) ≫ cχ.app (Qm.obj (rσ.obj Z)) =
        cχ.app (Rσ.obj (Qn.obj Z)) ≫ Tm.map (factσ.hom.app Z) :=
      cχ.naturality (factσ.hom.app Z)
    rw [Category.assoc, Hσ, ← Category.assoc (cχ.app (Rσ.obj (Qn.obj Z))), ← hnat,
      Category.assoc, ← Category.assoc (cχ.app (Qm.obj (rσ.obj Z))) (cum.app (rσ.obj Z)), Hχ]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc]
  exact hL.trans hR.symm

/-- **The comparison of the derived tensor functors attached to a composite of semilinear
homomorphisms is the composite of the comparisons.** Let `χ : A_k → A_m`, `σ : A_m → A_n` and
`ν : A_k → A_n` be homomorphisms of differential graded algebras with `σ ∘ χ = ν`, let `P`, `Q`
and `S` be bimodules over them and let `g : P ⟶ Q|_χ`, `f : Q ⟶ S|_σ` and `gf : P ⟶ S|_ν` be
semilinear homomorphisms with `gf` the composite of `g` and `f` on underlying maps. Then the
derived comparison `DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of `gf`, precomposed
with the identification of a two-step restriction of scalars with the one-step one, is the
derived comparison of `g` followed by the derived comparison of `f`.

This is the compatibility `DifferentialGraded.BimoduleSystem.cmp_trans` that an inverse system of
bimodules asks for, so it is what makes
`DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem` possible. -/
theorem derivedTensorRestrictTrans_comp_app (χ : Ak.Hom Am) (σ : Am.Hom An) (ν : Ak.Hom An)
    (hν : σ.comp χ = ν) (P : Bimodule Ak B) (Q : Bimodule Am B) (S : Bimodule An B)
    (g : P ⟶ Bimodule.restrictLeft χ Q) (f : Q ⟶ Bimodule.restrictLeft σ S)
    (gf : P ⟶ Bimodule.restrictLeft ν S)
    (hgf : ∀ y : P.rightModule.M, gf.rightHom.toFun y = f.rightHom.toFun (g.rightHom.toFun y))
    (X : derivedCategory' An) :
    (derivedTensorFunctor P).map
        ((derivedRestrictionComp χ σ ≪≫
            eqToIso (congrArg (fun α : Ak.Hom An => derivedRestriction α) hν)).hom.app X) ≫
        (derivedTensorRestrictTrans ν P S (tensorCompNatTransOfSemilinear ν P S gf)).app X =
      (derivedTensorRestrictTrans χ P Q (tensorCompNatTransOfSemilinear χ P Q g)).app
          ((derivedRestriction σ).obj X) ≫
        (derivedTensorRestrictTrans σ Q S (tensorCompNatTransOfSemilinear σ Q S f)).app X := by
  subst hν
  have key : Functor.whiskerRight (derivedRestrictionComp χ σ).hom (derivedTensorFunctor P) ≫
        derivedTensorRestrictTrans (σ.comp χ) P S
          (tensorCompNatTransOfSemilinear (σ.comp χ) P S gf) =
      Functor.whiskerLeft (derivedRestriction σ)
          (derivedTensorRestrictTrans χ P Q (tensorCompNatTransOfSemilinear χ P Q g)) ≫
        derivedTensorRestrictTrans σ Q S (tensorCompNatTransOfSemilinear σ Q S f) := by
    refine Functor.leftDerived_ext (derivedTensorFunctor S) (derivedTensorFunctorCounit S)
      (quasiIsomorphisms' An) _ _ _ ?_
    ext Z
    exact derivedTensorRestrictTrans_comp_aux (derivedRestrictionFactorization σ)
      (derivedRestrictionFactorization χ) (derivedRestrictionFactorization (σ.comp χ))
      (restrictScalarsHomotopyFunctor_comp χ σ) (derivedTensorFunctorCounit S)
      (derivedTensorFunctorCounit Q) (derivedTensorFunctorCounit P)
      (derivedTensorRestrictTrans χ P Q (tensorCompNatTransOfSemilinear χ P Q g))
      (derivedTensorRestrictTrans σ Q S (tensorCompNatTransOfSemilinear σ Q S f))
      (derivedTensorRestrictTrans (σ.comp χ) P S (tensorCompNatTransOfSemilinear (σ.comp χ) P S gf))
      (restrictTensorHomotopyTrans χ P Q (tensorCompNatTransOfSemilinear χ P Q g))
      (restrictTensorHomotopyTrans σ Q S (tensorCompNatTransOfSemilinear σ Q S f))
      (restrictTensorHomotopyTrans (σ.comp χ) P S
        (tensorCompNatTransOfSemilinear (σ.comp χ) P S gf))
      (derivedRestrictionComp χ σ).hom Z
      (congrArg (fun F : HomotopyCategory An ⥤ HomotopyCategory Ak => F ⋙ (quasiIsomorphisms' Ak).Q)
        (restrictScalarsHomotopyFunctor_comp χ σ)) rfl
      ((derivedTensorRestrictTrans_app_comp_counit χ P Q _ _).trans
        (derivedTensorRestrictTransQuotient_app χ P Q _ _))
      ((derivedTensorRestrictTrans_app_comp_counit σ Q S _ Z).trans
        (derivedTensorRestrictTransQuotient_app σ Q S _ Z))
      ((derivedTensorRestrictTrans_app_comp_counit (σ.comp χ) P S _ Z).trans
        (derivedTensorRestrictTransQuotient_app (σ.comp χ) P S _ Z))
      (by rw [derivedRestrictionComp_hom_app]; rfl)
      ((restrictTensorHomotopyTrans_comp_app χ σ P Q S _ _ _
        (tensorCompNatTransOfSemilinear_comp_app χ σ P Q S g f gf hgf) Z).trans
          (eqToHom_comp_left_eq _ _).symm)
  have happ := congrArg
    (fun α : (derivedRestriction σ ⋙ derivedRestriction χ) ⋙ derivedTensorFunctor P ⟶
      derivedTensorFunctor S => α.app X) key
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at happ
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Functor.map_comp, Category.assoc] using happ

/-! ### A differential graded algebra as a bimodule over an algebra mapping to it -/

/-- **A differential graded algebra as a bimodule over an algebra mapping to it.** The regular
right differential graded `B`-module, with `A` acting on the left by multiplication through
`ψ : A → B`. This is the bimodule half of `DifferentialGradedModule.restrictScalars` of a regular
module. -/
def regularRestrictedBimodule {A B : DifferentialGradedAlgebra.{u, u} R} (ψ : A.Hom B) :
    Bimodule A B where
  rightModule := regularModule B
  leftAction := regularBimoduleStructure ψ

/-- **The identity of `B` as a semilinear homomorphism of regular bimodules.** If `ψ : A → B`,
`φ' : A → C` and `ψ' : C → B` satisfy `ψ' ∘ φ' = ψ`, then the identity of `B` is a
`φ'`-semilinear homomorphism of differential graded bimodules from `B` read over `A` through `ψ`
to the restriction along `φ'` of `B` read over `C` through `ψ'`.

This is the bimodule counterpart of `DifferentialGradedModule.restrictedRegularIdHom`; the
hypothesis is an equality of homomorphisms of algebras, so the identity of `B` is never evaluated
on an element. -/
def regularRestrictedIdHom {A C B : DifferentialGradedAlgebra.{u, u} R} (ψ : A.Hom B)
    (φ' : A.Hom C) (ψ' : C.Hom B) (hcomp : ψ'.comp φ' = ψ) :
    regularRestrictedBimodule ψ ⟶ Bimodule.restrictLeft φ' (regularRestrictedBimodule ψ') where
  rightHom := DifferentialGradedModule.Hom.id (regularModule B)
  map_left := by
    subst hcomp
    exact fun n p a x => (regularBimoduleStructure_action (ψ'.comp φ') n p a x).trans
      (regularBimoduleStructure_action ψ' n p (φ'.gradingMap n a) x).symm

end Bimodule

/-! ### Strict inverse systems of differential graded bimodules -/

/-- **A strict inverse system of differential graded bimodules** over a strict inverse system of
differential graded algebras: a differential graded `(A_n, B)`-bimodule `M_n` for every `n`
together with a semilinear homomorphism `M_m ⟶ M_n|_{τ_{m,n}}` for every `n ≤ m`, whose
underlying maps compose.

This is the source's system `(M_n)` of right differential graded `A_n`-modules with a commuting
action of `B` and semilinear transition homomorphisms, as it is actually given; the comparison
maps of the derived tensor functors that
`DifferentialGraded.BimoduleSystem` asks for are constructed from it by
`DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem`. -/
structure StrictBimoduleSystem {R : Type u} [CommRing R] (T : StrictAlgebraSystem R)
    (B : DifferentialGradedAlgebra.{u, u} R) where
  /-- The differential graded `(A_n, B)`-bimodule `M_n` of the system. -/
  bimod : ∀ n : ℕ, Bimodule (T.alg n) B
  /-- The semilinear transition homomorphism `M_m ⟶ M_n|_{τ_{m,n}}` of the system, for
  `n ≤ m`. -/
  trans : ∀ {n m : ℕ} (h : n ≤ m), bimod m ⟶ Bimodule.restrictLeft (T.trans h) (bimod n)
  /-- The underlying maps of the transition homomorphisms compose. Stated on underlying maps
  because restricting a bimodule on the left leaves its underlying right `B`-module unchanged, so
  no transport along an equality of objects is involved. -/
  trans_comp : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (y : (bimod k).rightModule.M),
    (trans (h.trans h')).rightHom.toFun y =
      (trans h).rightHom.toFun ((trans h').rightHom.toFun y)

namespace StrictBimoduleSystem

variable {R : Type u} [CommRing R] {T : StrictAlgebraSystem R}
  {B : DifferentialGradedAlgebra.{u, u} R}

/-- **The comparison of the derived tensor functors of a strict inverse system of bimodules:**
the derived comparison `DifferentialGraded.Bimodule.derivedTensorRestrictTrans` of the plain
comparison `DifferentialGraded.Bimodule.tensorCompNatTransOfSemilinear` attached to the
semilinear transition homomorphism. -/
def cmp (M : StrictBimoduleSystem T B) {n m : ℕ} (h : n ≤ m) :
    T.toAlgebraSystem.restr h ⋙ Bimodule.derivedTensorFunctor (M.bimod m) ⟶
      Bimodule.derivedTensorFunctor (M.bimod n) :=
  Bimodule.derivedTensorRestrictTrans (T.trans h) (M.bimod m) (M.bimod n)
    (Bimodule.tensorCompNatTransOfSemilinear (T.trans h) (M.bimod m) (M.bimod n) (M.trans h))

/-- **The comparison maps of a strict inverse system of bimodules compose**, with the
identification of a two-step restriction of scalars with a one-step one spelled out as the one
`DifferentialGraded.StrictAlgebraSystem.toAlgebraSystem` provides. This is
`DifferentialGraded.Bimodule.derivedTensorRestrictTrans_comp_app` at the transition homomorphisms
of the system; it is stated separately from
`DifferentialGraded.StrictBimoduleSystem.cmp_cmp` because recognising the identification inside
the whole identity, rather than on its own, is beyond the kernel. -/
theorem cmp_cmp' (M : StrictBimoduleSystem T B) {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k)
    (X : derivedCategory' (T.alg n)) :
    (Bimodule.derivedTensorFunctor (M.bimod k)).map
        ((derivedRestrictionComp (T.trans h') (T.trans h) ≪≫
          eqToIso (congrArg (fun α : (T.alg k).Hom (T.alg n) => derivedRestriction α)
            (T.trans_comp h h'))).hom.app X) ≫ (M.cmp (h.trans h')).app X =
      (M.cmp h').app ((derivedRestriction (T.trans h)).obj X) ≫ (M.cmp h).app X :=
  Bimodule.derivedTensorRestrictTrans_comp_app (T.trans h') (T.trans h)
    (T.trans (h.trans h')) (T.trans_comp h h') (M.bimod k) (M.bimod m) (M.bimod n)
    (M.trans h') (M.trans h) (M.trans (h.trans h')) (M.trans_comp h h') X

/-- **The comparison maps of a strict inverse system of bimodules compose**, over the
identification `DifferentialGraded.AlgebraSystem.restrComp` of a two-step restriction of scalars
with a one-step one. This is the one compatibility that `DifferentialGraded.BimoduleSystem` asks
for, and it is `DifferentialGraded.StrictBimoduleSystem.cmp_cmp'` once the identification is
recognised as the one a strict system provides. -/
theorem cmp_cmp (M : StrictBimoduleSystem T B) {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k)
    (X : derivedCategory' (T.alg n)) :
    (Bimodule.derivedTensorFunctor (M.bimod k)).map
        ((T.toAlgebraSystem.restrComp h h').hom.app X) ≫ (M.cmp (h.trans h')).app X =
      (M.cmp h').app ((T.toAlgebraSystem.restr h).obj X) ≫ (M.cmp h).app X := by
  rw [show T.toAlgebraSystem.restrComp h h' =
      derivedRestrictionComp (T.trans h') (T.trans h) ≪≫
        eqToIso (congrArg (fun α : (T.alg k).Hom (T.alg n) => derivedRestriction α)
          (T.trans_comp h h')) from rfl]
  exact M.cmp_cmp' h h' X

/-- **The inverse system of differential graded bimodules underlying a strict one.** Its
comparison maps are the derived comparisons of the plain comparisons attached to the semilinear
transition homomorphisms, and their compatibility is
`DifferentialGraded.StrictBimoduleSystem.cmp_cmp` rather than an assumption. -/
def toBimoduleSystem (M : StrictBimoduleSystem T B) : BimoduleSystem T.toAlgebraSystem B where
  obj := M.bimod
  cmp := M.cmp
  cmp_trans := M.cmp_cmp

/-- The bimodules of the system underlying a strict one are the given ones. -/
@[simp] theorem toBimoduleSystem_obj (M : StrictBimoduleSystem T B) (n : ℕ) :
    M.toBimoduleSystem.obj n = M.bimod n := rfl

/-- **The comparison maps of the system underlying a strict one are the derived comparisons of
the plain ones.** This is the hypothesis `hcmp` of
`DifferentialGraded.BimoduleSystem.towerMap_ofSemilinear_towerMap` and of Tag 0GZJ, and it holds
here by `rfl`. -/
theorem toBimoduleSystem_cmp (M : StrictBimoduleSystem T B) {n m : ℕ} (h : n ≤ m) :
    M.toBimoduleSystem.cmp h =
      Bimodule.derivedTensorRestrictTrans (T.trans h) (M.bimod m) (M.bimod n)
        (Bimodule.tensorCompNatTransOfSemilinear (T.trans h) (M.bimod m) (M.bimod n)
          (M.trans h)) :=
  rfl

/-- **A strict inverse system of regular bimodules read through a fixed algebra.** Let `(A_n)` be
a strict inverse system of differential graded algebras, let `B` be a differential graded algebra
and let `ψ_n : A_n → B` be homomorphisms compatible with the transitions, `ψ_n ∘ τ_{m,n} = ψ_m`.
Then `B`, read as an `(A_n, B)`-bimodule through `ψ_n`, is a strict inverse system of
differential graded bimodules whose transition homomorphisms are the identity of `B`.

This is the bimodule counterpart of
`DifferentialGraded.StrictModuleSystem.ofRestrictedRegularId`, and with
`DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem` it provides inverse systems of
bimodules in the sense of `DifferentialGraded.BimoduleSystem` whose comparison maps are the
derived comparisons of the plain ones. -/
def ofRegularId (T : StrictAlgebraSystem R) (B : DifferentialGradedAlgebra.{u, u} R)
    (ψ : ∀ n : ℕ, (T.alg n).Hom B)
    (hsq : ∀ {n m : ℕ} (h : n ≤ m), (ψ n).comp (T.trans h) = ψ m) :
    StrictBimoduleSystem T B where
  bimod n := Bimodule.regularRestrictedBimodule (ψ n)
  trans h := Bimodule.regularRestrictedIdHom (ψ _) (T.trans h) (ψ _) (hsq h)
  trans_comp _ _ _ := rfl

/-- The bimodules of `DifferentialGraded.StrictBimoduleSystem.ofRegularId` are `B` read over
`A_n` through `ψ_n`. -/
@[simp] theorem ofRegularId_bimod (T : StrictAlgebraSystem R)
    (B : DifferentialGradedAlgebra.{u, u} R) (ψ : ∀ n : ℕ, (T.alg n).Hom B)
    (hsq : ∀ {n m : ℕ} (h : n ≤ m), (ψ n).comp (T.trans h) = ψ m) (n : ℕ) :
    (ofRegularId T B ψ hsq).bimod n = Bimodule.regularRestrictedBimodule (ψ n) := rfl

end StrictBimoduleSystem

end DifferentialGraded

end
