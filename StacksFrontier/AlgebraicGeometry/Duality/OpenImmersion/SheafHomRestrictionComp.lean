module

public import StacksFrontier.AlgebraicGeometry.Duality.NewShriekOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualityCompactification
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorIsoCompositionLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# The canonical map `Lg^* R𝓗om(P, Z) ⟶ R𝓗om(Lg^*P, Lg^*Z)` along a composite

For morphisms of schemes `a : A ⟶ B` and `b : B ⟶ C`, the comparison
`L(a ≫ b)^*(P ⊗ᴸ Q) ≅ L(a ≫ b)^*P ⊗ᴸ L(a ≫ b)^*Q` of [Stacks, Tag 079U] is the one of `b`
followed by the one of `a`, through `La^* ∘ Lb^* = L(a ≫ b)^*` ([Stacks, Tag 0D5S]). By the
currying bijection of [Stacks, Tag 08J8] the same holds for the canonical map of
[Stacks, Tag 08I3]. For open immersions this gives the transitivity of the restriction of
`f_new^! = D_X ∘ Lf^* ∘ D_Y` to opens.

## Main results

* `Stacks.Duality.TwistedInverseImageDuality.pullTensorIso_comp`: [Stacks, Tag 079U] along a
  composite, at the standard model.
* `Stacks.Duality.TwistedInverseImageDuality.pullSheafHomMap_comp'`: the canonical map of a
  composite.
* `Stacks.Duality.TwistedInverseImageDuality.pullCompIso_assoc`: the cocycle identity of
  [Stacks, Tag 0D5S] for `Stacks.Duality.UpperShriekDuality.pullCompIso`.
* `Stacks.Duality.fNewShriekRestrictIso_comp`: restricting `f_new^!` to `W ⊆ V ⊆ X` in two
  steps is restricting it to `W`.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Duality.UpperShriekDuality (pullCompIso)

variable {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)

/-- `pullCompIso` along `a ≫ b = a ≫ b` is the canonical composition isomorphism. -/
theorem pullCompIso_hom_app_rfl (K : Std C) :
    (pullCompIso a b (a ≫ b) rfl).hom.app K =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
        b.toLRSHom.toShHom).hom.app K := by
  simp only [pullCompIso]
  exact Category.comp_id _

/-- `pullTensorIso`, unfolded. -/
theorem pullTensorIso_hom_eq (g : A ⟶ B) (P Q : Std B) :
    (pullTensorIso g P Q).hom =
      (pull g).map (((ProjectionFormulaLocallySmall.standardTensorIso B).inv.app P).app Q) ≫
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
          g.toLRSHom.toShHom).hom.app (P, Q) ≫
        (((ProjectionFormulaLocallySmall.standardTensorIso A).hom.app ((pull g).obj P)).app
          ((pull g).obj Q)) := by
  simp [pullTensorIso, pullTensorNatIso]
  rfl

/-- [Stacks, Tag 079U] along a composite, at a pair of objects. -/
theorem derivedPullbackTensorIso_comp_app (P Q : Std C) :
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
        b.toLRSHom.toShHom).hom.app
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor C.sheaf).obj P).obj Q) ≫
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom)).hom.app (P, Q) =
    (pull a).map ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        b.toLRSHom.toShHom).hom.app (P, Q)) ≫
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        a.toLRSHom.toShHom).hom.app ((pull b).obj P, (pull b).obj Q) ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor A.sheaf).map
        ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
          b.toLRSHom.toShHom).hom.app P)).app _ ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor A.sheaf).obj _).map
        ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
          b.toLRSHom.toShHom).hom.app Q) :=
  NatTrans.congr_app
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_comp a.toLRSHom.toShHom
      b.toLRSHom.toShHom) (P, Q)

/-- The chase behind `pullTensorIso_comp`. -/
theorem pullTensor_comp_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (La : 𝒟 ⥤ 𝒞)
    {d0 d1 d2 d3 : 𝒟} (u : d0 ⟶ d1) (v : d1 ⟶ d2) (w : d2 ⟶ d3) (w' : d3 ⟶ d2)
    (hw : w ≫ w' = 𝟙 _) {c1 c2 c3 c4 c5 c6 : 𝒞} (κ1 : La.obj d0 ⟶ c1) (Ls : c1 ⟶ c2)
    (κ2 : La.obj d1 ⟶ c2) (T : c2 ⟶ c3) (tA : c3 ⟶ c4) (Ta : La.obj d2 ⟶ c5) (m' : c5 ⟶ c3)
    (tA' : c5 ⟶ c6) (mA : c6 ⟶ c4) (nat : La.map u ≫ κ2 = κ1 ≫ Ls)
    (h : κ2 ≫ T = La.map v ≫ Ta ≫ m') (nA : m' ≫ tA = tA' ≫ mA) :
    κ1 ≫ Ls ≫ T ≫ tA = La.map (u ≫ v ≫ w) ≫ (La.map w' ≫ Ta ≫ tA') ≫ mA := by
  rw [← reassoc_of% nat, reassoc_of% h, nA]
  simp only [Functor.map_comp, Category.assoc]
  rw [← La.map_comp_assoc w w', hw, La.map_id, Category.id_comp]

/-- Naturality of `standardTensorIso` in both variables. -/
theorem standardTensorIso_hom_naturality_pair {X : Scheme.{u}} {P P' Q Q' : Std X} (p : P ⟶ P')
    (q : Q ⟶ Q') :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map p).app Q ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj P').map q ≫
        ((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app P').app Q' =
      ((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app P).app Q ≫
        ((tensor X).map p).app Q ≫ ((tensor X).obj P').map q := by
  rw [((ProjectionFormulaLocallySmall.standardTensorIso X).hom.app P').naturality q,
    ← Category.assoc, ← NatTrans.comp_app,
    (ProjectionFormulaLocallySmall.standardTensorIso X).hom.naturality p, NatTrans.comp_app,
    Category.assoc]

/-- **`Lk^*(P ⊗ᴸ Q) ≅ Lk^*P ⊗ᴸ Lk^*Q` for `k = a ≫ b`** is the one of `b`, followed by the one
of `a`, through `La^* ∘ Lb^* = Lk^*` ([Stacks, Tag 079U] and [Stacks, Tag 0D5S]). -/
theorem pullTensorIso_comp (P Q : Std C) :
    (pullCompIso a b (a ≫ b) rfl).hom.app (((tensor C).obj P).obj Q) ≫
        (pullTensorIso (a ≫ b) P Q).hom =
      (pull a).map (pullTensorIso b P Q).hom ≫
        (pullTensorIso a ((pull b).obj P) ((pull b).obj Q)).hom ≫
        ((tensor A).map ((pullCompIso a b (a ≫ b) rfl).hom.app P)).app _ ≫
        ((tensor A).obj _).map ((pullCompIso a b (a ≫ b) rfl).hom.app Q) := by
  rw [pullCompIso_hom_app_rfl, pullCompIso_hom_app_rfl, pullCompIso_hom_app_rfl,
    pullTensorIso_hom_eq, pullTensorIso_hom_eq, pullTensorIso_hom_eq]
  exact pullTensor_comp_chase (pull a) _ _ _ _
    (by simp; rfl)
    _ _ _ _ _ _ _ _ _
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      a.toLRSHom.toShHom b.toLRSHom.toShHom).hom.naturality
        (((ProjectionFormulaLocallySmall.standardTensorIso C).inv.app P).app Q))
    (derivedPullbackTensorIso_comp_app a b P Q)
    (by
      have := standardTensorIso_hom_naturality_pair (X := A)
        ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
          b.toLRSHom.toShHom).hom.app P)
        ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
          b.toLRSHom.toShHom).hom.app Q)
      rw [← Category.assoc] at this
      exact this)

/-- The chase behind `pullSheafHomMap_comp`. -/
theorem sheafHom_comp_chase {𝒞 : Type*} [Category 𝒞] {x0 x1 x2 x3 x5 z0 z1 : 𝒞}
    (p : x0 ≅ x1) (M : x1 ≅ x5) (N : x0 ≅ x2) (Aa : x2 ≅ x3) (Xs : x3 ≅ x5) (E : x1 ⟶ z1)
    (LLev : x0 ⟶ z0) (v : z0 ⟶ z1) (h : p.hom ≫ M.hom = N.hom ≫ Aa.hom ≫ Xs.hom)
    (nat : LLev ≫ v = p.hom ≫ E) :
    M.inv ≫ E = Xs.inv ≫ Aa.inv ≫ N.inv ≫ LLev ≫ v := by
  have hM : M.inv = Xs.inv ≫ Aa.inv ≫ N.inv ≫ p.hom := by
    rw [← cancel_mono M.hom, Iso.inv_hom_id, Category.assoc, Category.assoc, Category.assoc, h]
    simp
  rw [hM, nat]
  simp only [Category.assoc]

/-- **The canonical map of [Stacks, Tag 08I3] for a composite `a ≫ b`** is the one of `b`
pulled back along `a`, followed by the one of `a`, through `La^* ∘ Lb^* = L(a ≫ b)^*`. -/
theorem pullSheafHomMap_comp (P Z : Std C) :
    pullSheafHomMap (a ≫ b) P Z =
      (pullCompIso a b (a ≫ b) rfl).inv.app _ ≫ (pull a).map (pullSheafHomMap b P Z) ≫
        pullSheafHomMap a ((pull b).obj P) ((pull b).obj Z) ≫
        ((sheafHom A).map ((pullCompIso a b (a ≫ b) rfl).inv.app P).op).app _ ≫
        ((sheafHom A).obj _).map ((pullCompIso a b (a ≫ b) rfl).hom.app Z) := by
  apply (curry A _ _ _).injective
  rw [curry_pullSheafHomMap, curry_naturality_left, ← Category.assoc, ← Category.assoc,
    curry_naturality_right, curry_naturality_middle, Category.assoc]
  simp only [Functor.comp_obj]
  rw [curry_pull_map_comp_pullSheafHomMap, curry_pullSheafHomMap]
  have h := pullTensorIso_comp a b (((sheafHom C).obj (op P)).obj Z) P
  have hX := ((tensor A).map ((pullCompIso a b (a ≫ b) rfl).hom.app
    (((sheafHom C).obj (op P)).obj Z))).naturality ((pullCompIso a b (a ≫ b) rfl).hom.app P)
  simp only [Functor.comp_obj] at hX
  rw [← hX] at h
  have nat := (pullCompIso a b (a ≫ b) rfl).hom.naturality (evaluation P Z)
  simp only [Functor.map_comp, Category.assoc]
  refine (sheafHom_comp_chase ((pullCompIso a b (a ≫ b) rfl).app _)
    (pullTensorIso (a ≫ b) (((sheafHom C).obj (op P)).obj Z) P)
    ((pull a).mapIso (pullTensorIso b (((sheafHom C).obj (op P)).obj Z) P))
    (pullTensorIso a ((pull b).obj (((sheafHom C).obj (op P)).obj Z)) ((pull b).obj P))
    (((tensor A).obj _).mapIso ((pullCompIso a b (a ≫ b) rfl).app P) ≪≫
      ((tensor A).mapIso ((pullCompIso a b (a ≫ b) rfl).app _)).app _)
    _ _ _ h nat).trans ?_
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.comp_map, Category.assoc]

/-- **The cocycle identity of [Stacks, Tag 0D5S] for `pullCompIso`.** -/
theorem pullCompIso_assoc {D : Scheme.{u}} (c : C ⟶ D) {ab : A ⟶ C} {bc : B ⟶ D}
    {abc : A ⟶ D} (wab : a ≫ b = ab) (wbc : b ≫ c = bc) (w₁ : ab ≫ c = abc)
    (w₂ : a ≫ bc = abc) (K : Std D) :
    (pullCompIso a b ab wab).hom.app ((pull c).obj K) ≫ (pullCompIso ab c abc w₁).hom.app K =
      (pull a).map ((pullCompIso b c bc wbc).hom.app K) ≫ (pullCompIso a bc abc w₂).hom.app K := by
  subst wab wbc w₁
  rw [pullCompIso_hom_app_rfl, pullCompIso_hom_app_rfl, pullCompIso_hom_app_rfl]
  refine
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc_app
      a.toLRSHom.toShHom b.toLRSHom.toShHom c.toLRSHom.toShHom K).trans ?_
  congr 1
  simp only [pullCompIso]
  exact (Category.comp_id _).symm

/-- `pullSheafHomMap_comp` along any `a ≫ b = k`. -/
theorem pullSheafHomMap_comp' {k : A ⟶ C} (w : a ≫ b = k) (P Z : Std C) :
    pullSheafHomMap k P Z =
      (pullCompIso a b k w).inv.app _ ≫ (pull a).map (pullSheafHomMap b P Z) ≫
        pullSheafHomMap a ((pull b).obj P) ((pull b).obj Z) ≫
        ((sheafHom A).map ((pullCompIso a b k w).inv.app P).op).app _ ≫
        ((sheafHom A).obj _).map ((pullCompIso a b k w).hom.app Z) := by
  subst w
  exact pullSheafHomMap_comp a b P Z

/-- `pullCompIso_assoc`, inverted. -/
theorem pullCompIso_assoc_inv {D : Scheme.{u}} (c : C ⟶ D) {ab : A ⟶ C} {bc : B ⟶ D}
    {abc : A ⟶ D} (wab : a ≫ b = ab) (wbc : b ≫ c = bc) (w₁ : ab ≫ c = abc)
    (w₂ : a ≫ bc = abc) (K : Std D) :
    (pullCompIso ab c abc w₁).inv.app K ≫ (pullCompIso a b ab wab).inv.app ((pull c).obj K) =
      (pullCompIso a bc abc w₂).inv.app K ≫ (pull a).map ((pullCompIso b c bc wbc).inv.app K) := by
  have h' := congrArg Iso.inv (Iso.ext (pullCompIso_assoc a b c wab wbc w₁ w₂ K) :
    (pullCompIso a b ab wab).app ((pull c).obj K) ≪≫ (pullCompIso ab c abc w₁).app K =
      (pull a).mapIso ((pullCompIso b c bc wbc).app K) ≪≫ (pullCompIso a bc abc w₂).app K)
  simpa using h'

/-- `R𝓗om(-, ω)` of two equal composites. -/
theorem sheafHom_map_comp_app_eq {X : Scheme.{u}} {P Q R Q' : Std X} (a₁ : Q ⟶ R) (a₂ : P ⟶ Q)
    (b₁ : Q' ⟶ R) (b₂ : P ⟶ Q') (E : a₂ ≫ a₁ = b₂ ≫ b₁) (ω : Std X) :
    ((sheafHom X).map a₁.op).app ω ≫ ((sheafHom X).map a₂.op).app ω =
      ((sheafHom X).map b₁.op).app ω ≫ ((sheafHom X).map b₂.op).app ω := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp, E]

end Stacks.Duality.TwistedInverseImageDuality

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Duality.UpperShriekDuality (pullCompIso)
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

variable {V X Y : Scheme.{u}} (ι : V ⟶ X) [IsOpenImmersion ι]

/-- The components of `pullDualIso` are the canonical maps. -/
theorem pullDualIso_hom_app (ωX P : Std X) :
    (pullDualIso ι ωX).hom.app (op P) = pullSheafHomMap ι P ωX := by
  simp only [pullDualIso, relativeDualIsoSheafHom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    UpperShriekDuality.pullSheafHomIso_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom]
  exact (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans ((Category.id_comp _).trans
    (Category.comp_id _))

/-- The components of `fNewShriekRestrictIso`. -/
theorem fNewShriekRestrictIso_hom_app (f : X ⟶ Y) (k : V ⟶ Y) (e : ι ≫ f = k) (ωX : Std X)
    (ωY : Std Y) (M : Std Y) :
    (fNewShriekRestrictIso ι f k e ωX ωY).hom.app M =
      (pullDualIso ι ωX).hom.app ((pull f).op.obj ((dualInto ωY).rightOp.obj M)) ≫
        (dualInto ((pull ι).obj ωX)).map
          ((NatIso.op (pullCompIso ι f k e)).inv.app ((dualInto ωY).rightOp.obj M)) := by
  simp only [fNewShriekRestrictIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app, Category.id_comp]

/-- `D_ω` on the opposite of a natural isomorphism, through `R𝓗om`. -/
theorem dualInto_map_natIsoOp_inv_app {Z T : Scheme.{u}} {F G : Std T ⥤ Std Z} (ω : Std Z)
    (e : F ≅ G) (D : (Std T)ᵒᵖ) :
    (dualInto ω).map ((NatIso.op e).inv.app D) =
      ((sheafHom Z).map (e.inv.app D.unop).op).app ω :=
  pre_app_std Z _ ω

/-- The components of `dualIntoMapIso`. -/
theorem relativeDualMapIso_inv_app_eq {Z : Scheme.{u}} {ω ω' : Std Z} (e : ω ≅ ω') (P : (Std Z)ᵒᵖ) :
    (dualIntoMapIso e).inv.app P = ((sheafHom Z).obj P).map e.inv :=
  rfl

/-- The chase behind `fNewShriekRestrictIso_comp`. -/
theorem fNewShriekRestrictIso_comp_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (L : 𝒟 ⥤ 𝒞)
    {d0 d1 d2 : 𝒟} (m1 : d0 ⟶ d1) (m2 : d1 ⟶ d2) {c0 c1 c2 c3 c4 c5 c6 : 𝒞}
    (p : c0 ⟶ L.obj d0) (q : L.obj d1 ⟶ c1) (x1 : c1 ⟶ c2) (y1 : c2 ⟶ c3) (x2 : c3 ⟶ c4)
    (y2 : c4 ⟶ c5) (q' : L.obj d2 ⟶ c6) (x3 : c6 ⟶ c5) (s : c1 ⟶ c6) (x2' : c2 ⟶ c5)
    (y1' : c5 ⟶ c4) (N1 : L.map m2 ≫ q' = q ≫ s) (N2 : y1 ≫ x2 = x2' ≫ y1')
    (C1 : y1' ≫ y2 = 𝟙 _) (C2 : x1 ≫ x2' = s ≫ x3) :
    ((p ≫ L.map m1 ≫ q ≫ x1 ≫ y1) ≫ x2) ≫ y2 = p ≫ L.map (m1 ≫ m2) ≫ q' ≫ x3 := by
  simp only [Category.assoc]
  rw [reassoc_of% N2, C1, Category.comp_id, C2, ← reassoc_of% N1, L.map_comp, Category.assoc]

variable {W : Scheme.{u}}

/-- **Restricting `f_new^!` in two steps.** For open immersions `ι : W ⟶ V`, `uV : V ⟶ X` with
`ι ≫ uV = uW`, the isomorphism `uW^* ∘ f_new^! ≅ (uW ≫ f)_new^!` is `ι^*` of the one for `uV`
followed by the one for `ι`, the dualizing complexes being identified by `Lι^* ∘ LuV^* = LuW^*`. -/
theorem fNewShriekRestrictIso_comp (ι : W ⟶ V) (uV : V ⟶ X) (uW : W ⟶ X) [IsOpenImmersion ι]
    [IsOpenImmersion uV] [IsOpenImmersion uW] (h : ι ≫ uV = uW) (f : X ⟶ Y) (gV : V ⟶ Y)
    (gW : W ⟶ Y) (eV : uV ≫ f = gV) (eW : uW ≫ f = gW) (eι : ι ≫ gV = gW) (ωX : Std X) (ωY : Std Y)
    (M : Std Y) :
    (fNewShriekRestrictIso uW f gW eW ωX ωY).hom.app M ≫
        (dualIntoMapIso ((pullCompIso ι uV uW h).app ωX)).inv.app _ =
      (pullCompIso ι uV uW h).inv.app _ ≫
        (pull ι).map ((fNewShriekRestrictIso uV f gV eV ωX ωY).hom.app M) ≫
        (fNewShriekRestrictIso ι gV gW eι ((pull uV).obj ωX) ωY).hom.app M := by
  rw [fNewShriekRestrictIso_hom_app, fNewShriekRestrictIso_hom_app, fNewShriekRestrictIso_hom_app,
    pullDualIso_hom_app, pullDualIso_hom_app, pullDualIso_hom_app,
    pullSheafHomMap_comp' ι uV h, dualInto_map_natIsoOp_inv_app, dualInto_map_natIsoOp_inv_app,
    dualInto_map_natIsoOp_inv_app, relativeDualMapIso_inv_app_eq]
  refine fNewShriekRestrictIso_comp_chase (pull ι) _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullSheafHomMap_naturality ι ((pullCompIso uV f gV eV).inv.app
      (unop ((dualInto ωY).rightOp.obj M))) ((pull uV).obj ωX))
    (((TwistedInverseImageDuality.sheafHom W).map ((pullCompIso uW f gW eW).inv.app
      (unop ((dualInto ωY).rightOp.obj M))).op).naturality ((pullCompIso ι uV uW h).hom.app ωX))
    (((TwistedInverseImageDuality.sheafHom W).obj
      (op ((pull gW).obj (unop ((dualInto ωY).rightOp.obj M))))).mapIso
        ((pullCompIso ι uV uW h).app ωX)).hom_inv_id
    (sheafHom_map_comp_app_eq _ _ _ _ (pullCompIso_assoc_inv ι uV f h eV eW eι _) _)

end Stacks.Duality
