module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupBoundedSiteVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantExtensionByZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnitySupplement

/-!
# The cohomology of `Z/n` on the size-bounded small étale site and on Mathlib's

Tags 03RQ and 03RR are proved on the small étale site `SmallEtale.topology B X hX` of
Stacks 021B cut out of a big étale site `B`, at coefficients `AddCommGrpCat.{u}`, while the eight
assertions of Tag 03SC live on Mathlib's small étale site `X.smallEtaleTopology` at coefficients
`AddCommGrpCat.{u + 1}`. This file identifies the cohomology of the constant sheaf `Z/n` on the two
(as sets, in every degree), which is what moves vanishing, finiteness and cardinalities across:

* raising the coefficient universe on the size-bounded site does not change cohomology
  (`Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`), and carries the constant sheaf to the
  constant sheaf;
* the size-bounded site is a dense subsite of Mathlib's, with the same final object, so restriction
  is an equivalence of sheaf categories carrying constant sheaves to constant sheaves.

## Main results

* `Stacks.EtaleCohomology.ConstantTransport.sheafHConstantEquivOfIsDenseSubsite`.
* `Stacks.EtaleCohomology.ConstantTransport.sheafHConstantZModEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open _root_.AlgebraicGeometry

universe w w' a v₁ u₁ v₂ u₂ t u

namespace Stacks.EtaleCohomology.ConstantTransport

/-- `Ext` groups along isomorphisms in both variables. -/
def extCongr {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] {A A' B B' : C} (e₁ : A ≅ A')
    (e₂ : B ≅ B') (n : ℕ) : Ext.{w} A B n ≃ Ext.{w} A' B' n :=
  ((((extFunctor.{w} n).mapIso e₁.op).app B).addCommGroupIsoToAddEquiv.toEquiv.symm).trans
    (((extFunctor.{w} n).obj (op A')).mapIso e₂).addCommGroupIsoToAddEquiv.toEquiv

/-- **The cohomology of a constant abelian sheaf does not change on a dense subsite**, as a
bijection of cohomology groups, the two `Ext` universes being unrelated. -/
def sheafHConstantEquivOfIsDenseSubsite
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
    [G.IsDenseSubsite J K]
    [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
    [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]
    {TC : C} (hTC : IsTerminal TC) (hTD : IsTerminal (G.obj TC))
    (M : AddCommGrpCat.{a}) (q : ℕ) :
    Sheaf.H.{w} ((constantSheaf J AddCommGrpCat.{a}).obj M) q ≃
      Sheaf.H.{w'} ((constantSheaf K AddCommGrpCat.{a}).obj M) q :=
  let E := Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}
  have : HasLimitsOfShape (Discrete WalkingPair) (Cᵒᵖ ⥤ AddCommGrpCat.{a}) := inferInstance
  have : HasBinaryProducts (Sheaf J AddCommGrpCat.{a}) := inferInstance
  have : PreservesLimitsOfSize.{0, 0} E.functor := E.symm.toAdjunction.rightAdjoint_preservesLimits
  have : E.functor.IsLeftAdjoint := E.isLeftAdjoint_functor
  have : E.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  (Stacks.CohomologyVanishing.extEquivOfEquivalence E _ _ q).trans
    (extCongr ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app _)
      ((equivCommuteConstant J AddCommGrpCat.{a} K G hTC hTD).app M) q)

section Bounded

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **The cohomology of a constant sheaf on the size-bounded small étale site and on Mathlib's**,
at coefficients `AddCommGrpCat.{u + 1}`. -/
def sheafHBoundedConstantEquiv
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})]
    (M : AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H.{w} ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj M) q ≃
      Sheaf.H.{u + 1} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) q :=
  have : ∀ T : (X.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B X hX).op) AddCommGrpCat.{u + 1} :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have hT : IsTerminal ((SmallEtale.toEtaleSite B X hX).obj (SmallEtale.final B X hX)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  sheafHConstantEquivOfIsDenseSubsite _ _ (SmallEtale.toEtaleSite B X hX)
    (SmallEtale.finalIsTerminal B X hX) hT M q

/-- The universe lift of the constant sheaf `Z/n` on the size-bounded small étale site is the
constant sheaf `Z/n` at the larger coefficient universe. -/
def sheafComposeUliftConstantZModIso (n : ℕ)
    [(SmallEtale.topology B X hX).PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u}] :
    (sheafCompose (SmallEtale.topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (smallEtaleConstantZModSheaf B X hX n) ≅
      (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) :=
  let e : AddCommGrpCat.uliftFunctor.{u + 1, u}.obj (AddCommGrpCat.of (ULift.{u} (ZMod n))) ≅
      AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) :=
    AddEquiv.toAddCommGrpIso
      { toFun := fun x => ⟨x.down.down⟩
        invFun := fun x => ⟨⟨x.down⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
  ((sheafComposeNatIso (SmallEtale.topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}
      (sheafificationAdjunction (SmallEtale.topology B X hX) AddCommGrpCat.{u})
      (sheafificationAdjunction (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})).app
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u} (ZMod n))))).symm ≪≫
    (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).mapIso e

/-- **The cohomology of `Z/n` on the size-bounded small étale site at coefficients
`AddCommGrpCat.{u}`, in which Tags 03RQ and 03RR are stated, is the cohomology of `Z/n` on
Mathlib's small étale site at coefficients `AddCommGrpCat.{u + 1}`, in which Tag 03SC is
stated**, in every degree. -/
def sheafHConstantZModEquiv (n : ℕ)
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] (q : ℕ) :
    Sheaf.H.{t} (smallEtaleConstantZModSheaf B X hX n) q ≃
      Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb X n) q :=
  have := (boundedSmallEtaleUlift_properties.{u + 1, u} B X hX).1
  have := (boundedSmallEtaleUlift_properties.{u + 1, u} B X hX).2
  have : HasExt.{u + 1} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
    smallEtaleSheaf_hasExt B X hX
  ((Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv.{u, t, u + 1, u + 1}
      (SmallEtale.topology B X hX)
      (smallEtaleConstantZModSheaf B X hX n) q).toEquiv.trans
    (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr
      (sheafComposeUliftConstantZModIso B X hX n) q).toEquiv).trans
    (sheafHBoundedConstantEquiv B X hX _ q)

/-- **Plug-in for Tag 03RQ.** An identification of `H^q(X, Z/n)` on the size-bounded site with a
group `G` gives the order of `H^q(X, Z/n)` on Mathlib's site. -/
theorem natCard_sheafH_constantZModAb_of_addEquiv (n : ℕ)
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] (q : ℕ) {G : Type*}
    [AddCommGroup G] (h : Nonempty (Sheaf.H.{t} (smallEtaleConstantZModSheaf B X hX n) q ≃+ G)) :
    Nat.card (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb X n) q) = Nat.card G :=
  let ⟨e⟩ := h
  Nat.card_congr ((sheafHConstantZModEquiv B X hX n q).symm.trans e.toEquiv)

/-- **Plug-in for Tag 03RQ, vanishing.** -/
theorem subsingleton_sheafH_constantZModAb_of_boundedSite (n : ℕ)
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] (q : ℕ)
    (h : Subsingleton (Sheaf.H.{t} (smallEtaleConstantZModSheaf B X hX n) q)) :
    Subsingleton (Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb X n) q) :=
  (sheafHConstantZModEquiv B X hX n q).symm.injective.subsingleton

/-- **The passage from `μ_n` to `Z/n`, transported.** For `n` invertible in the algebraically
closed field `k`, the cohomology of `μ_n` on the size-bounded site (in which Tag 03RR is stated)
is the cohomology of `Z/n` on Mathlib's site. -/
def sheafHRootsOfUnityEquiv {k : Type u} [Field k] [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hnk : IsUnit (n : k))
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] (q : ℕ) :
    Sheaf.H.{t} (smallEtaleRootsOfUnitySheaf B X hX n) q ≃
      Sheaf.H.{u + 1} (StrongTorsionCurveAssertions.constantZModAb X n) q :=
  (sheafHAddEquivOfIso (SmallEtale.topology B X hX)
    (constantZModSheafIsoRootsOfUnitySheaf B k f hX n hn hnk) q).toEquiv.symm.trans
    (sheafHConstantZModEquiv B X hX n q)

end Bounded

end Stacks.EtaleCohomology.ConstantTransport

end
