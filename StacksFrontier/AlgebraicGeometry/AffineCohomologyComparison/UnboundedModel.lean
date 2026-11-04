module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionViaPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleCollapseViaPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleRightDerivedViaPlus
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# The collapse at an acyclic object: the two models agree

`Stacks.Cohomology.AffineComparison.rightDerivedFunctorPlusObjSingleIso` is the collapse of
`R⁺F` at an object right acyclic for `F`, on the bounded below derived category, and it is one of
the two factors of [Stacks, Tag 089W]. `CategoryTheory.Functor.singleCollapseIso` is the same
collapse for an unbounded right derived functor. **This file proves that
`CategoryTheory.Functor.boundedDerivedIso` carries one to the other.**

With that and the two matchings proved upstream — the crossing between the two models at a single
complex, and the composition comparison — **this file closes [Stacks, Tag 089W] against the
unbounded model**, which is the comparison the route of conclusion (c) of [Stacks, Tag 0EX3]
needs.

## Main results

* `map_rightDerivedFunctorPlusObjSingleIso_inv`: the collapse at an acyclic object matches, the
  third of the three matchings.
* `boundedDerivedIso_hom_app_comp_singleCollapse`: **the three matchings assembled**, before
  cohomology is taken. This is the mathematical content.
* `singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom`: the same with `Hⁿ` taken, which
  cancels the two model crossings.
* `cohomologyIsoPushforward_hom_eq`: **[Stacks, Tag 089W] read at the unbounded model.**

## Implementation notes

*Why the inverse direction.* The two single-functor coherences this needs already exist, and
their directions decide the shape: `Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app`
(`Homology/DerivedIndexing/Composite.lean:915`) is available for `inv` and has no `hom`
counterpart, and `Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app`
(`StacksFrontier/Homology/DerivedIndexing/Composite.lean`) likewise. Inverting the statement is free —
both sides are isomorphisms — and it lets both apply as they stand, rather than forcing a `hom`
sibling that belongs beside them and not here.

*The third factor is the only one proved anywhere new.* `Stacks.DerivedFunctor`'s
`comp_boundedDerivedIso_inv_app` supplies the middle factor, the unit of `R⁺F` read through the
crossing; the first and last are the two coherences above. What this file adds is the chase, and
the bridge `Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app` between the two
spellings of the inner coherence — `StacksFrontier/Homology/DerivedIndexing/Composite.lean` writes its
right-hand side through `HomologicalComplex.singleMapHomologicalComplex`, while
`CategoryTheory.Functor.singleCollapse` is built on
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor`.

*Nothing here was found by a name search.* Every ingredient was located by grepping the
**constants the statement is about** — `rightDerivedFunctorPlusObjSingleIso`,
`mapSingleFunctorCompQhIso`, `singleFunctorPlusIsoCompQh` — and not the names a new lemma would
have been given; a name search for these had already missed four of them in this tree, which is
recorded in `StacksFrontier/Algebra/Homology/DerivedCategory/SingleCollapseViaPlus.lean`.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.AffineBase
open scoped AlgebraicGeometry

namespace Stacks.Cohomology.AffineComparison

universe v u vB uB vC uC wA wB wC

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The chase that compares the two collapses, at variables of an abstract category. Its three
hypotheses are the two single-functor coherences and the unit of `R⁺F` read through the
crossing, the last composed with the naturality of the crossing. -/
private lemma chase_collapse {C : Type*} [Category* C] {P₀ P₂ P₃ P₄ P₅ P₆ P₇ : C}
    {c' : P₀ ⟶ P₅} {b' : P₅ ⟶ P₂} {a' : P₂ ⟶ P₃}
    {p : P₀ ⟶ P₄} {q : P₄ ⟶ P₅} (f2 : c' = p ≫ q)
    {r : P₅ ⟶ P₆} {t : P₆ ⟶ P₂} (f3 : b' = r ≫ t)
    {s : P₆ ⟶ P₇} {z : P₇ ⟶ P₃} (f4 : t ≫ a' = s ≫ z) :
    (c' ≫ b') ≫ a' = (((p ≫ q) ≫ r) ≫ s) ≫ z := by
  rw [f2, f3]
  simp only [Category.assoc]
  rw [f4]

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{wB} B]
  {C' : Type uC} [Category.{vC} C'] [Abelian C'] [HasDerivedCategory.{wC} C']
  (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

omit [EnoughInjectives B] in
/-- **The two collapses correspond under the `D⁺`-to-`D` crossing.** For `X` right acyclic for
`F`, the inverse of the bounded below collapse
`rightDerivedFunctorPlusObjSingleIso`, read in `D(B)`, is the inverse of the unbounded collapse
`CategoryTheory.Functor.singleCollapseIso` followed by the crossing.

Its three factors are `Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app` with the
bridge `Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app`,
`Stacks.DerivedFunctor.comp_boundedDerivedIso_inv_app`, and
`Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app` together with the naturality
of the crossing. -/
theorem map_rightDerivedFunctorPlusObjSingleIso_inv
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (X : A) (hX : F.rightAcyclic X) :
    DerivedCategory.Plus.ι.map (rightDerivedFunctorPlusObjSingleIso F X hX).inv =
      (Functor.singleCollapseIso F RF αF hres X hX).inv ≫
        (Functor.boundedDerivedIso F RF αF hres).inv.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X) := by
  refine (Functor.map_comp _ _ _).trans ?_
  erw [Functor.map_comp]
  exact chase_collapse
      ((Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app (P := F) X).trans
        (congrArg (fun z => (DerivedCategory.singleFunctorIsoCompQh B 0).hom.app (F.obj X) ≫
            DerivedCategory.Qh.map z)
          (Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app (P := F) X).symm))
      (Stacks.DerivedFunctor.comp_boundedDerivedIso_inv_app F RF αF hres
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X)).symm
      (((Functor.boundedDerivedIso F RF αF hres).inv.naturality
          ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).inv.app X)).symm.trans
        (congrArg (fun z => RF.map z ≫
            (Functor.boundedDerivedIso F RF αF hres).inv.app
              ((DerivedCategory.Plus.singleFunctor A 0).obj X))
          (Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_inv_app (C := A) X)))

/-- An isomorphism known through its inverse, read forwards. At variables. -/
private lemma map_hom_eq {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {X Y : C}
    (e : X ≅ Y) {Z : D} (a : H.obj X ≅ Z) (b : Z ≅ H.obj Y)
    (h : H.map e.inv = b.inv ≫ a.inv) : H.map e.hom = a.hom ≫ b.hom := by
  have h2 : H.map e.hom ≫ b.inv ≫ a.inv = 𝟙 _ := by
    rw [← h, ← H.map_comp, e.hom_inv_id, H.map_id]
  have h3 : (a.hom ≫ b.hom) ≫ b.inv ≫ a.inv = 𝟙 _ := by simp
  exact (cancel_mono (b.inv ≫ a.inv)).1 (h2.trans h3.symm)

/-- The chase that assembles the three matchings, at variables of an abstract category. Its three
hypotheses are the composition matching, the collapse carried through the outer derived functor,
and the naturality of the outer crossing at the collapse. -/
private lemma chase_assembly {C : Type*} [Category* C] {Q R S S' T U V : C}
    {bfg : Q ⟶ R} {th : R ⟶ S} {ci : Q ⟶ U} {bg : U ⟶ S'} {bf : S' ⟶ S}
    (g1 : ci ≫ bg ≫ bf = bfg ≫ th)
    {sc : S ⟶ T} {m : S' ⟶ T} (g2 : bf ≫ sc = m)
    {gm : U ⟶ V} {bg' : V ⟶ T} (g3 : gm ≫ bg' = bg ≫ m) :
    bfg ≫ th ≫ sc = ci ≫ gm ≫ bg' := by
  rw [← Category.assoc bfg, ← g1, g3, ← g2]
  simp only [Category.assoc]

variable (G : B ⥤ C') [G.Additive]
  (RG : DerivedCategory B ⥤ DerivedCategory C')
  (αG : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
  (RFG : DerivedCategory A ⥤ DerivedCategory C')
  (αFG : (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RFG)
  [RFG.IsRightDerivedFunctor αFG (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (θ : RFG ⟶ RF ⋙ RG)

/-- **The three matchings assembled, before cohomology is taken.** For `X` right acyclic for `F`,
the comparison of the two iterated derived functors followed by `RG` of the unbounded collapse is
the `D⁺` comparison followed by `R⁺G` of the `D⁺` collapse, read in `D(C')` through the crossings.

This is the whole content of the comparison of [Stacks, Tag 089W] with the unbounded route: what
remains after it is the two model crossings at either end, which
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_boundedDerivedIso`
supplies. -/
theorem boundedDerivedIso_hom_app_comp_singleCollapse
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hresB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hθ : ∀ L : HomotopyCategory A (ComplexShape.up ℤ),
      αFG.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
              (ComplexShape.up ℤ)).inv.app L) ≫
          αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          RG.map (αF.app L))
    (X : A) (hX : F.rightAcyclic X) :
    (Functor.boundedDerivedIso (F ⋙ G) RFG αFG hresA).hom.app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
        θ.app (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
          RG.map (Functor.singleCollapse F RF αF hresA X hX) =
      DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusComp F G).app
            ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
        DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map
            (rightDerivedFunctorPlusObjSingleIso F X hX).hom) ≫
          (Functor.boundedDerivedIso G RG αG hresB).hom.app
            ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X)) :=
  chase_assembly
    (Functor.boundedDerivedIso_hom_app_comp_rightDerivedFunctorPlusComp F G RF αF RG αG RFG αFG
      hresA hresB θ hθ ((DerivedCategory.Plus.singleFunctor A 0).obj X))
    ((RG.map_comp _ _).symm.trans (congrArg RG.map
      (map_hom_eq DerivedCategory.Plus.ι (rightDerivedFunctorPlusObjSingleIso F X hX)
        ((Functor.boundedDerivedIso F RF αF hresA).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X))
        (Functor.singleCollapseIso F RF αF hresA X hX)
        (map_rightDerivedFunctorPlusObjSingleIso_inv F RF αF hresA X hX)).symm))
    ((Functor.boundedDerivedIso G RG αG hresB).hom.naturality
      (rightDerivedFunctorPlusObjSingleIso F X hX).hom)

/-- The chase that takes cohomology of the assembly, at variables of an abstract category: the
two model crossings at either end are cancelled against the two crossings of the models of the
derived functors. -/
private lemma chase_final {C : Type*} [Category* C] {P Q R S T U V : C}
    {cr₁ : P ⟶ Q} {a : Q ⟶ R} {m : R ⟶ S} {c : S ⟶ T}
    {hb : P ⟶ R} (p1 : cr₁ ≫ a = hb)
    {hbg : S ⟶ U} {cr₂ : U ⟶ T} (p2 : c = hbg ≫ cr₂)
    {h1 : P ⟶ V} {h2 : V ⟶ U} (q : hb ≫ m ≫ hbg = h1 ≫ h2) :
    cr₁ ≫ a ≫ m ≫ c = h1 ≫ h2 ≫ cr₂ := by
  rw [← Category.assoc cr₁, p1, p2, ← Category.assoc m, ← Category.assoc hb, q, Category.assoc]

/-- A four-fold composite under one functor image, with the value of the composite known. At
variables. -/
private lemma map_comp_four {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {P Q R S T U : C} {f₁ : P ⟶ Q} {f₂ : Q ⟶ R} {f₃ : R ⟶ S} {f₄ : S ⟶ T}
    {g₁ : P ⟶ U} {g₂ : U ⟶ T} (h : f₁ ≫ f₂ ≫ f₃ ≫ f₄ = g₁ ≫ g₂) :
    H.map f₁ ≫ (H.map f₂ ≫ H.map f₃) ≫ H.map f₄ = H.map g₁ ≫ H.map g₂ := by
  simp only [← H.map_comp, Category.assoc, h]

/-- **[Stacks, Tag 089W]'s collapse factor read at the unbounded model.** For `X` right acyclic
for `F`, the crossing of the two models at `X` followed by
`rightDerivedCollapseIso` is the degree-`n` cohomology of the comparison of the two iterated
derived functors and of `RG` of the unbounded collapse, followed by the crossing of the two
models at `F X`.

The crossing stands on the **left** so that it is never inverted. The left-hand side opens by
`rfl`: `rightDerivedCollapseIso` is an `Iso.trans` of
`Stacks.DerivedIndexing.rightDerivedIso` at either end with `rightDerivedPlusCollapseIso`
between, and that middle factor is `Hⁿ(Plus.ι.map _)` on the nose,
`CategoryTheory.DerivedCategory.Plus.homologyFunctor` being `Plus.ι ⋙ homologyFunctor`. -/
theorem singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I))
    (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hresB : ∀ K : CochainComplex B ℤ, ∃ (I : CochainComplex B ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (hθ : ∀ L : HomotopyCategory A (ComplexShape.up ℤ),
      αFG.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
              (ComplexShape.up ℤ)).inv.app L) ≫
          αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          RG.map (αF.app L))
    (X : A) (hX : F.rightAcyclic X) (n : ℕ) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (F ⋙ G) RFG αFG
            hresA n).hom.app X ≫
        (rightDerivedCollapseIso F G hFG X hX n).hom =
      (DerivedCategory.homologyFunctor C' (n : ℤ)).map
          (θ.app ((DerivedCategory.singleFunctor A 0).obj X)) ≫
        (DerivedCategory.homologyFunctor C' (n : ℤ)).map
            (RG.map (Functor.singleCollapse F RF αF hresA X hX)) ≫
          (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived G RG αG
            hresB n).hom.app (F.obj X) := by
  have hci : (Stacks.Cohomology.DerivedPushforwardSections.compIso F G hFG).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) =
      (Functor.rightDerivedFunctorPlusComp F G).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) :=
    congr_app (Stacks.Cohomology.DerivedPushforwardSections.compIso_hom F G hFG) _
  refine chase_final
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_comp_rightDerivedIso
      (F ⋙ G) RFG αFG hresA n X)
    ((Iso.inv_comp_eq
      ((DerivedCategory.homologyFunctor C' (n : ℤ)).mapIso
        (((Functor.boundedDerivedIso G RG αG hresB).app
          ((DerivedCategory.Plus.singleFunctor B 0).obj (F.obj X))).symm))).2
      (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app_boundedDerivedIso
        G RG αG hresB n (F.obj X))).symm ?_
  rw [show (rightDerivedPlusCollapseIso F G hFG X hX (n : ℤ)).hom =
      (DerivedCategory.homologyFunctor C' (n : ℤ)).map (DerivedCategory.Plus.ι.map
          ((Functor.rightDerivedFunctorPlusComp F G).app
            ((DerivedCategory.Plus.singleFunctor A 0).obj X))) ≫
        (DerivedCategory.homologyFunctor C' (n : ℤ)).map (DerivedCategory.Plus.ι.map
          (G.rightDerivedFunctorPlus.map
            (rightDerivedFunctorPlusObjSingleIso F X hX).hom)) from
    (congrArg (fun z => (DerivedCategory.homologyFunctor C' (n : ℤ)).map
        (DerivedCategory.Plus.ι.map (z ≫ G.rightDerivedFunctorPlus.map
          (rightDerivedFunctorPlusObjSingleIso F X hX).hom))) hci).trans
      ((congrArg (DerivedCategory.homologyFunctor C' (n : ℤ)).map
          (DerivedCategory.Plus.ι.map_comp _ _)).trans
        ((DerivedCategory.homologyFunctor C' (n : ℤ)).map_comp _ _))]
  exact map_comp_four (DerivedCategory.homologyFunctor C' (n : ℤ))
    ((Iso.inv_comp_eq
      ((Functor.boundedDerivedIso (F ⋙ G) RFG αFG hresA).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X))).2
      (boundedDerivedIso_hom_app_comp_singleCollapse F RF αF G RG αG RFG αFG θ hresA hresB hθ
        X hX).symm)

section Tag089W

attribute [local instance] HasDerivedCategory.standard

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsAffineHom f]
  (Ff : X.Modules) [Ff.IsQuasicoherent]
  (RF : DerivedCategory X.Modules ⥤ DerivedCategory S.Modules)
  (αF : (AlgebraicGeometry.Scheme.Modules.pushforward f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  (RG : DerivedCategory S.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
  (αG : (moduleGlobalSections S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)
  [RG.IsRightDerivedFunctor αG (HomotopyCategory.quasiIso S.Modules (ComplexShape.up ℤ))]
  (RFG : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
  (αFG : Functor.mapHomotopyCategory
        (AlgebraicGeometry.Scheme.Modules.pushforward f ⋙ moduleGlobalSections S)
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RFG)
  [RFG.IsRightDerivedFunctor αFG (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  (θ : RFG ⟶ RF ⋙ RG)

/-- **[Stacks, Tag 089W] read at the unbounded model.** For an affine morphism of schemes
`f : X ⟶ S` and a quasi-coherent `F`, the comparison
`H^n(X, F) ≅ H^n(S, f_* F)` of [Stacks, Tag 089W] is

> restriction of scalars pulled inside the right derived functor, the crossing of the two models
> at `F` inverted, the comparison of the two iterated derived functors, `RG` of the collapse of
> `Rf_*` at `F`, and the crossing of the two models at `f_* F`,

for **any** unbounded right derived functors of the two degreewise functors and any comparison
`θ` between the iterated ones satisfying the usual factorisation `hθ`.

Keeping the derived data as parameters is deliberate: the unbounded derived functors this
development uses are stated at `SheafOfModules (structureSheafRing _)` while 089W is stated at
`AlgebraicGeometry.Scheme.Modules`, and those two carry different `Preadditive` instances. The
statement below crosses that divide **not at all**; a consumer crosses it once, in argument
position, when it supplies `RF`, `RG`, `RFG` and `θ`. -/
theorem cohomologyIsoPushforward_hom_eq
    (hresA : ∀ K : CochainComplex X.Modules ℤ, ∃ (I : CochainComplex X.Modules ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g)
    (hresB : ∀ K : CochainComplex S.Modules ℤ, ∃ (I : CochainComplex S.Modules ℤ) (g : K ⟶ I),
      I.IsKInjective ∧ QuasiIso g)
    (hθ : ∀ L : HomotopyCategory X.Modules (ComplexShape.up ℤ),
      αFG.app L ≫ θ.app (DerivedCategory.Qh.obj L) =
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso
              (Iso.refl (AlgebraicGeometry.Scheme.Modules.pushforward f ⋙
                moduleGlobalSections S)) (ComplexShape.up ℤ)).inv.app L) ≫
          αG.app (((AlgebraicGeometry.Scheme.Modules.pushforward f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj L) ≫
          RG.map (αF.app L))
    (n : ℕ) :
    (cohomologyIsoPushforward f Ff n).hom =
      (restrictScalarsRightDerivedIso f Ff n).hom ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (AlgebraicGeometry.Scheme.Modules.pushforward f ⋙ moduleGlobalSections S)
            RFG αFG hresA n).inv.app Ff ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) (n : ℤ)).map
              (θ.app ((DerivedCategory.singleFunctor X.Modules 0).obj Ff)) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) (n : ℤ)).map
                (RG.map (Functor.singleCollapse
                  (AlgebraicGeometry.Scheme.Modules.pushforward f) RF αF hresA Ff
                  (rightAcyclic_pushforward_of_isAffineHom f Ff))) ≫
              (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                  (moduleGlobalSections S) RG αG hresB n).hom.app
                ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj Ff) :=
  congrArg (fun z => (restrictScalarsRightDerivedIso f Ff n).hom ≫ z)
    ((Iso.inv_comp_eq
        ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (AlgebraicGeometry.Scheme.Modules.pushforward f ⋙ moduleGlobalSections S)
          RFG αFG hresA n).app Ff)).2
        (singleCompDerived_hom_app_comp_rightDerivedCollapseIso_hom
          (AlgebraicGeometry.Scheme.Modules.pushforward f) RF αF (moduleGlobalSections S) RG αG
          RFG αFG θ (rightAcyclic_moduleGlobalSections_pushforward_obj f) hresA hresB hθ Ff
          (rightAcyclic_pushforward_of_isAffineHom f Ff) n).symm).symm

end Tag089W

end Stacks.Cohomology.AffineComparison

end
