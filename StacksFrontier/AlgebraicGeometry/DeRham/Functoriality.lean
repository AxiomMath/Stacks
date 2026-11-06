module

public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Topology.Sheaves.Modules.DeRhamUniqueness
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of relative de Rham cohomology

Let

```
X' --f--> X
|         |
S' -----> S
```

be a commutative square of schemes. The canonical map on relative differentials of the square
extends uniquely to a homomorphism of sheaves of graded algebras
`⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})`; it commutes with the de Rham differential, hence is a map of
complexes `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}`. Composing derived global sections of that map with the
identification `RΓ(X, Rf_*-) ≅ RΓ(X', -)` gives the **pullback maps**

`f^* : RΓ(X, Ω^•_{X/S}) ⟶ RΓ(X', Ω^•_{X'/S'})` and `f^* : H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom`: the canonical homomorphism of
  sheaves of graded algebras `⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})`.
* `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` and
  `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus`: **the canonical map of de Rham
  complexes** `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of abelian sheaves, and the same map read as a
  morphism of bounded-below complexes.
* `AlgebraicGeometry.Scheme.Hom.deRhamCohomology`: **relative de Rham cohomology**
  `H^i_{dR}(X/S)` of a morphism of schemes.
* `AlgebraicGeometry.Scheme.Hom.deRhamDerivedSectionsPullback` and
  `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback`: **the pullback maps** on derived
  global sections of the de Rham complex and on de Rham cohomology.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_comm`: **the canonical homomorphism
  commutes with the de Rham differential.** This is what makes the degreewise maps a map of
  complexes; it is checked on the multiples of the exact wedges, which generate the sheaves of
  differential forms locally.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPushforwardIso`: derived global sections on `X'`
  are derived global sections on `X` of the derived direct image, for abelian sheaves.
* `AlgebraicGeometry.SheafOfModules.eq_of_exactWedges`: two additive natural families out of
  `⋀ᵖ Ω` agreeing on the multiples of the exact wedges are equal.

## Implementation notes

The canonical homomorphism is obtained from the universal property of the exterior algebra of
`Ω_{X/S}`, applied to the pushforward `f_*(⋀ Ω_{X'/S'})` with its square-zero degree-one
generator. Multiplication in that pushforward is the multiplication of `⋀ Ω_{X'/S'}` over the
inverse-image open, so products of local sections are computed on `X'`; this is what makes the
de Rham rule checkable on both sides of the square.

The map of complexes is stated in **abelian** sheaves rather than in sheaves of modules. The
de Rham differential is only `p^{-1}𝒪_S`-linear, so a map of complexes of modules would need
the base-change morphism `p^{-1}𝒪_S ⟶ f_*(p'^{-1}𝒪_{S'})` of the square; the abelian form needs
no ring datum, and it is the form relative de Rham cohomology is computed in
(`AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelian`).

`AlgebraicGeometry.Scheme.Hom.deRhamPushforwardToDerived` carries no type ascription: ascribing
its type leaves the universe of `HasDerivedCategory` undetermined, since that universe is a
parameter of the class and is only fixed by the instance found while elaborating the body.

## References

* [Stacks Project, Section 50.3](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Section 50.2](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace SheafOfModules.GradedAlgebra
open RingedSpaceModuleAdjunction

universe u

namespace SheafOfModules.GradedAlgebra.UnitalHom

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {A B : SheafOfModules.GradedAlgebra.{u, u} R}

/-- A homomorphism of sheaves of graded algebras commutes with transport along an equality
of degrees. -/
theorem val_app_degCast (ψ : UnitalHom A B) (U : Cᵒᵖ) {i j : ℤ} (h : i = j)
    (x : (A.piece i).val.obj U) :
    (ψ.app j).val.app U
        (Stacks.degCast (F := fun k : ℤ => ((A.piece k).val.obj U : Type u)) h x) =
      Stacks.degCast (F := fun k : ℤ => ((B.piece k).val.obj U : Type u)) h
        ((ψ.app i).val.app U x) := by
  subst h
  rfl

end SheafOfModules.GradedAlgebra.UnitalHom

namespace Stacks.DeRham

open HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- A functor preserving zero morphisms preserves being strictly supported on an embedding. -/
instance isStrictlySupported_mapHomologicalComplex (K : HomologicalComplex C c')
    [K.IsStrictlySupported e] :
    (((F.mapHomologicalComplex c').obj K).IsStrictlySupported e) where
  isZero i' hi' := F.map_isZero (K.isZero_X_of_isStrictlySupported e i' hi')


end Stacks.DeRham

namespace AlgebraicGeometry.SheafOfModules

open Opposite

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- **The de Rham rule, transport-free.** On a multiple of an ordered product of exact
differentials the differential is the ordered product of one more exact differential. -/
theorem DeRhamDifferential.differential_smul_homogeneousProdLeft (D : DeRhamDifferential B)
    (n : ℕ) (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U)
    (c : Fin n → X.sheaf.obj.obj U) :
    (D.differential n).val.app U
        (b • B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
          fun i => exactOne B U (c i)) =
      B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U (n + 1)
        fun i => exactOne B U ((Fin.cons b c : Fin (n + 1) → X.sheaf.obj.obj U) i) := by
  have hdef : (B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U (n + 1)
        fun i => exactOne B U ((Fin.cons b c : Fin (n + 1) → X.sheaf.obj.obj U) i)) =
      Stacks.degCast
        (F := fun k : ℤ => ((B.exterior.piece k).val.obj U : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
        ((B.exterior.mul 1 (n : ℤ)).app U (exactOne B U b)
          (B.exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
            fun i => exactOne B U (c i))) := rfl
  rw [hdef]
  exact eq_of_heq
    ((D.generator n U b _ (isExactWedge_homogeneousProdLeft B U n c)).trans
      (Stacks.heq_degCast
        (F := fun k : ℤ => ((B.exterior.piece k).val.obj U : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega) _).symm)

/-- **Two additive natural families out of `⋀ᵖ Ω` that agree on the multiples of the exact
wedges agree**, since those generate `⋀ᵖ Ω` locally and the target is a sheaf. -/
theorem eq_of_exactWedges (p : ℕ)
    {N : _root_.SheafOfModules.{u} (underlyingRingSheaf X.sheaf)}
    (α β : ∀ U : (Opens X.carrier)ᵒᵖ, (B.exteriorPower p).val.obj U →+ N.val.obj U)
    (hα : ∀ {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (x : (B.exteriorPower p).val.obj U),
      α V ((B.exteriorPower p).val.map i x) = N.val.map i (α U x))
    (hβ : ∀ {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (x : (B.exteriorPower p).val.obj U),
      β V ((B.exteriorPower p).val.map i x) = N.val.map i (β U x))
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (b : X.sheaf.obj.obj U)
      (ω : (B.exteriorPower p).val.obj U), IsExactWedge B U p ω →
        α U (b • ω) = β U (b • ω))
    (U : (Opens X.carrier)ᵒᵖ) (x : (B.exteriorPower p).val.obj U) : α U x = β U x := by
  have key : ∀ (V : (Opens X.carrier)ᵒᵖ) (η : (B.exteriorPower p).val.obj V),
      η ∈ exactWedgeSubgroup B V p → α V η = β V η := by
    intro V
    have hsub : exactWedgeSubgroup B V p ≤ AddMonoidHom.eqLocus (α V) (β V) := by
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro η ⟨b, ω, hω, rfl⟩
      exact h V b ω hω
    exact fun η hη => hsub hη
  obtain ⟨S, hS, hcov⟩ := locallyGeneratedByExactWedges B p U x
  refine N.isSheaf.isSeparated (unop U) S hS _ _ fun V i hi => ?_
  exact (hα i.op x).symm.trans ((key (op V) _ (hcov i hi)).trans (hβ i.op x))

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)

/-- The degree-one generator of `⋀ Ω_{X'/S'}` read on `f^*Ω_{X/S}`: the canonical map on
relative differentials of the square of Tag 01UV followed by the generator. -/
noncomputable def pushforwardFormsGenerator (hcomm : f ≫ p = p' ≫ g) :
    (Scheme.Modules.pullback f).obj (relativeDifferentials p) ⟶
      (relativeDifferentialFormsAlgebra p').piece 1 :=
  relativeDifferentialsMap f p p' g hcomm ≫
    Scheme.Modules.exteriorGenerator (relativeDifferentials p')

/-- The degree-one generator read on `f^*Ω_{X/S}` has square zero. -/
theorem squareZero_pushforwardFormsGenerator (hcomm : f ≫ p = p' ≫ g) :
    SquareZero (pushforwardFormsGenerator f p p' g hcomm) :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p')).1.comp _

/-- **Stacks Project, Tag 07HX.** The canonical homomorphism of sheaves of graded algebras
`⋀ Ω_{X/S} ⟶ f_*(⋀ Ω_{X'/S'})` of a commutative square of schemes: the unique unital
homomorphism extending the canonical map on relative differentials. -/
noncomputable def deRhamFormsPushforwardHom (hcomm : f ≫ p = p' ≫ g) :
    UnitalHom (relativeDifferentialFormsAlgebra p)
      (pushforwardRingedSpace f.toLRSHom.toShHom (relativeDifferentialFormsAlgebra p')) :=
  pushforwardDesc f.toLRSHom.toShHom
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p))
    (squareZero_pushforwardFormsGenerator f p p' g hcomm)

/-- In degree one the canonical homomorphism carries the exact differential of a local section
to the exact differential of its pullback. -/
theorem deRhamFormsPushforwardHom_exactOne (hcomm : f ≫ p = p' ≫ g) (U : (X.Opens)ᵒᵖ)
    (x : X.sheaf.obj.obj U) :
    ((deRhamFormsPushforwardHom f p p' g hcomm).app 1).val.app U
        (SheafOfModules.exactOne (deRhamAlgebras p) U x) =
      SheafOfModules.exactOne (deRhamAlgebras p')
        ((opensMap f.toLRSHom.toShHom).op.obj U) ((f.app U.unop).hom x) := by
  have hext := IsExteriorAlgebra.desc_extends
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials p))
      (pushforwardRingedSpace f.toLRSHom.toShHom (relativeDifferentialFormsAlgebra p'))
      (pushforwardGenerator f.toLRSHom.toShHom (pushforwardFormsGenerator f p p' g hcomm))
      (squareZero_pushforwardGenerator _ (squareZero_pushforwardFormsGenerator f p p' g hcomm))
  have hd := relativeDifferentialsMap_app_d (f := f) (p := p) (p' := p') g hcomm U.unop x
  have h2 := homEquiv_val_app f.toLRSHom.toShHom (relativeDifferentialsMap f p p' g hcomm)
    U ((universalRelativeDerivation p).d x)
  have h3 : (relativeDifferentialsMap f p p' g hcomm).val.app
      ((opensMap f.toLRSHom.toShHom).op.obj U)
      (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app
        (relativeDifferentials p)).val.app U
          ((universalRelativeDerivation p).d x)) =
      (universalRelativeDerivation p').d ((f.app U.unop).hom x) := h2.symm.trans hd
  have h1 := congrArg (fun h : relativeDifferentials p ⟶
      (pushforwardRingedSpace f.toLRSHom.toShHom
        (relativeDifferentialFormsAlgebra p')).piece 1 =>
    h.val.app U ((universalRelativeDerivation p).d x)) hext
  refine h1.trans ?_
  refine (pushforwardGenerator_val_app f.toLRSHom.toShHom
    (pushforwardFormsGenerator f p p' g hcomm) U _).trans ?_
  exact congrArg
    ((Scheme.Modules.exteriorGenerator (relativeDifferentials p')).val.app
      ((opensMap f.toLRSHom.toShHom).op.obj U)) h3

/-- The canonical homomorphism carries an ordered product of exact differentials to the ordered
product of the exact differentials of the pullbacks. -/
theorem deRhamFormsPushforwardHom_homogeneousProdLeft (hcomm : f ≫ p = p' ≫ g)
    (U : (X.Opens)ᵒᵖ) (n : ℕ) (c : Fin n → X.sheaf.obj.obj U) :
    ((deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app U
        ((deRhamAlgebras p).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
          fun i => SheafOfModules.exactOne (deRhamAlgebras p) U (c i)) =
      (deRhamAlgebras p').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        ((opensMap f.toLRSHom.toShHom).op.obj U) n
        fun i => SheafOfModules.exactOne (deRhamAlgebras p')
          ((opensMap f.toLRSHom.toShHom).op.obj U) ((f.app U.unop).hom (c i)) := by
  induction n with
  | zero => exact (deRhamFormsPushforwardHom f p p' g hcomm).map_one U
  | succ n ih =>
      have hA : (deRhamAlgebras p).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U
            (n + 1) (fun i => SheafOfModules.exactOne (deRhamAlgebras p) U (c i)) =
          Stacks.degCast
            (F := fun k : ℤ =>
              (((relativeDifferentialFormsAlgebra p).piece k).val.obj U : Type u))
            (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
            (((relativeDifferentialFormsAlgebra p).mul 1 (n : ℤ)).app U
              (SheafOfModules.exactOne (deRhamAlgebras p) U (c 0))
              ((deRhamAlgebras p).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
                fun i => SheafOfModules.exactOne (deRhamAlgebras p) U (c i.succ))) := rfl
      have hB : (deRhamAlgebras p').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            ((opensMap f.toLRSHom.toShHom).op.obj U) (n + 1)
            (fun i => SheafOfModules.exactOne (deRhamAlgebras p')
              ((opensMap f.toLRSHom.toShHom).op.obj U) ((f.app U.unop).hom (c i))) =
          Stacks.degCast
            (F := fun k : ℤ =>
              (((pushforwardRingedSpace f.toLRSHom.toShHom
                (relativeDifferentialFormsAlgebra p')).piece k).val.obj U : Type u))
            (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
            (((pushforwardRingedSpace f.toLRSHom.toShHom
                (relativeDifferentialFormsAlgebra p')).mul 1 (n : ℤ)).app U
              (SheafOfModules.exactOne (deRhamAlgebras p')
                ((opensMap f.toLRSHom.toShHom).op.obj U) ((f.app U.unop).hom (c 0)))
              ((deRhamAlgebras p').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
                ((opensMap f.toLRSHom.toShHom).op.obj U) n
                fun i => SheafOfModules.exactOne (deRhamAlgebras p')
                  ((opensMap f.toLRSHom.toShHom).op.obj U)
                  ((f.app U.unop).hom (c i.succ)))) := rfl
      rw [hA, hB]
      refine (SheafOfModules.GradedAlgebra.UnitalHom.val_app_degCast
        (deRhamFormsPushforwardHom f p p' g hcomm) U
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega) _).trans ?_
      refine congrArg (Stacks.degCast
        (F := fun k : ℤ =>
          (((pushforwardRingedSpace f.toLRSHom.toShHom
            (relativeDifferentialFormsAlgebra p')).piece k).val.obj U : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)) ?_
      refine ((deRhamFormsPushforwardHom f p p' g hcomm).map_mul 1 (n : ℤ) U _ _).trans ?_
      rw [deRhamFormsPushforwardHom_exactOne, ih fun i => c i.succ]

/-- The canonical homomorphism is semilinear for `f^♯ : 𝒪_X ⟶ f_*𝒪_{X'}`. -/
theorem deRhamFormsPushforwardHom_smul (hcomm : f ≫ p = p' ≫ g) (n : ℤ)
    (U : (X.Opens)ᵒᵖ) (b : X.sheaf.obj.obj U)
    (ω : ((relativeDifferentialFormsAlgebra p).piece n).val.obj U) :
    ((deRhamFormsPushforwardHom f p p' g hcomm).app n).val.app U (b • ω) =
      @SMul.smul (X'.sheaf.obj.obj ((opensMap f.toLRSHom.toShHom).op.obj U))
        (((relativeDifferentialFormsAlgebra p').piece n).val.obj
          ((opensMap f.toLRSHom.toShHom).op.obj U)) _
        ((f.app U.unop).hom b)
        (((deRhamFormsPushforwardHom f p p' g hcomm).app n).val.app U ω) :=
  PresheafOfModules.app_smul ((deRhamFormsPushforwardHom f p p' g hcomm).app n).val b ω

/-- **The canonical homomorphism commutes with the de Rham differential.** -/
theorem deRhamFormsPushforwardHom_comm (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (U : (X.Opens)ᵒᵖ) (ω : ((deRhamAlgebras p).exteriorPower n).val.obj U) :
    ((SheafOfModules.deRhamDifferential (deRhamAlgebras p')).differential n).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj U)
        (((deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app U ω) =
      ((deRhamFormsPushforwardHom f p p' g hcomm).app ((n + 1 : ℕ) : ℤ)).val.app U
        (((SheafOfModules.deRhamDifferential (deRhamAlgebras p)).differential n).val.app U
          ω) := by
  refine SheafOfModules.eq_of_exactWedges (deRhamAlgebras p) n
    (N := (modulePushforward f.toLRSHom.toShHom).obj
      ((deRhamAlgebras p').exteriorPower (n + 1)))
    (fun V => AddMonoidHom.comp
      (((SheafOfModules.deRhamDifferential (deRhamAlgebras p')).differential n).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj V)).hom.toAddMonoidHom
      (((deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app V).hom.toAddMonoidHom)
    (fun V => AddMonoidHom.comp
      (((deRhamFormsPushforwardHom f p p' g hcomm).app
        ((n + 1 : ℕ) : ℤ)).val.app V).hom.toAddMonoidHom
      (((SheafOfModules.deRhamDifferential (deRhamAlgebras p)).differential n).val.app
        V).hom.toAddMonoidHom)
    ?_ ?_ ?_ U ω
  · intro V W i x
    refine Eq.trans (congrArg (fun y =>
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras p')).differential n).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj W) y)
      (PresheafOfModules.naturality_apply
        ((deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val i x)) ?_
    exact PresheafOfModules.naturality_apply
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras p')).differential n).val
      ((opensMap f.toLRSHom.toShHom).op.map i) _
  · intro V W i x
    refine Eq.trans (congrArg (fun y =>
      ((deRhamFormsPushforwardHom f p p' g hcomm).app ((n + 1 : ℕ) : ℤ)).val.app W y)
      (PresheafOfModules.naturality_apply
        ((SheafOfModules.deRhamDifferential (deRhamAlgebras p)).differential n).val i x)) ?_
    exact PresheafOfModules.naturality_apply
      ((deRhamFormsPushforwardHom f p p' g hcomm).app ((n + 1 : ℕ) : ℤ)).val i _
  · intro V b η hη
    obtain ⟨c, rfl⟩ :=
      SheafOfModules.exists_eq_homogeneousProdLeft (deRhamAlgebras p) V n η hη
    have hcons : (fun i => (f.app V.unop).hom
          ((Fin.cons b c : Fin (n + 1) → X.sheaf.obj.obj V) i)) =
        (Fin.cons ((f.app V.unop).hom b)
          (fun i => (f.app V.unop).hom (c i)) :
            Fin (n + 1) → X'.sheaf.obj.obj ((opensMap f.toLRSHom.toShHom).op.obj V)) := by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => rfl
    refine Eq.trans (congrArg (fun y =>
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras p')).differential n).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj V) y)
      (deRhamFormsPushforwardHom_smul f p p' g hcomm (n : ℤ) V b
        ((deRhamAlgebras p).exterior.toPresheafGradedAlgebra.homogeneousProdLeft V n
          fun i => SheafOfModules.exactOne (deRhamAlgebras p) V (c i)))) ?_
    refine Eq.trans (congrArg (fun y : ((relativeDifferentialFormsAlgebra p').piece
        (n : ℤ)).val.obj ((opensMap f.toLRSHom.toShHom).op.obj V) =>
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras p')).differential n).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj V)
        (@SMul.smul (X'.sheaf.obj.obj ((opensMap f.toLRSHom.toShHom).op.obj V))
          (((relativeDifferentialFormsAlgebra p').piece (n : ℤ)).val.obj
            ((opensMap f.toLRSHom.toShHom).op.obj V)) _ ((f.app V.unop).hom b) y))
      (deRhamFormsPushforwardHom_homogeneousProdLeft f p p' g hcomm V n c)) ?_
    refine Eq.trans (SheafOfModules.DeRhamDifferential.differential_smul_homogeneousProdLeft
      (deRhamAlgebras p') (SheafOfModules.deRhamDifferential (deRhamAlgebras p')) n
      ((opensMap f.toLRSHom.toShHom).op.obj V) ((f.app V.unop).hom b)
      (fun i => (f.app V.unop).hom (c i))) ?_
    refine Eq.symm (Eq.trans (congrArg (fun y =>
      ((deRhamFormsPushforwardHom f p p' g hcomm).app ((n + 1 : ℕ) : ℤ)).val.app V y)
      (SheafOfModules.DeRhamDifferential.differential_smul_homogeneousProdLeft
        (deRhamAlgebras p) (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) n V b c)) ?_)
    refine Eq.trans (deRhamFormsPushforwardHom_homogeneousProdLeft f p p' g hcomm V (n + 1)
      (Fin.cons b c : Fin (n + 1) → X.sheaf.obj.obj V)) ?_
    exact congrArg (fun w : Fin (n + 1) →
        X'.sheaf.obj.obj ((opensMap f.toLRSHom.toShHom).op.obj V) =>
      (deRhamAlgebras p').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        ((opensMap f.toLRSHom.toShHom).op.obj V) (n + 1)
        fun i => SheafOfModules.exactOne (deRhamAlgebras p')
          ((opensMap f.toLRSHom.toShHom).op.obj V) (w i)) hcons

/-- The commutation of the canonical map with the arrows of the de Rham complex. -/
theorem deRhamFormsPushforwardHom_comm_d (hcomm : f ≫ p = p' ≫ g) (n : ℕ)
    (U : (X.Opens)ᵒᵖ) (ω : ((deRhamAlgebras p).exteriorPower n).val.obj U) :
    ((SheafOfModules.deRhamComplex (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))).d n (n + 1)).val.app
        ((opensMap f.toLRSHom.toShHom).op.obj U)
        (((deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ)).val.app U ω) =
      ((deRhamFormsPushforwardHom f p p' g hcomm).app ((n + 1 : ℕ) : ℤ)).val.app U
        (((SheafOfModules.deRhamComplex (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p))).d n (n + 1)).val.app U ω) := by
  rw [SheafOfModules.deRhamComplex_d, SheafOfModules.deRhamComplex_d]
  exact deRhamFormsPushforwardHom_comm f p p' g hcomm n U ω

/-- **Stacks Project, Tag 07HX.** The canonical map of de Rham complexes
`Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of a commutative square of schemes, read in abelian sheaves. -/
@[stacks 07HX "the canonical map of complexes `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}`"]
noncomputable def deRhamAbelianPushforwardMap (hcomm : f ≫ p = p' ≫ g) :
    SheafOfModules.deRhamAbelianComplex (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ⟶
      ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u}
          f.base).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SheafOfModules.deRhamAbelianComplex (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))) :=
  { f := fun n => (_root_.SheafOfModules.toSheaf (structureSheafRing X.toRingedSpace)).map
      ((deRhamFormsPushforwardHom f p p' g hcomm).app (n : ℤ))
    comm' := by
      rintro n m rfl
      ext U x
      exact deRhamFormsPushforwardHom_comm_d f p p' g hcomm n U x }

/-! ### Derived global sections -/

section Derived

open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree
open Stacks.Cohomology.DerivedPushforwardSections

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- On bounded-below complexes of abelian sheaves the localization functor to the derived
category factors through the homotopy category. -/
noncomputable def plusQIsoOn (Y : Scheme.{u})
    (L : CochainComplex.Plus (AbelianSheaf Y.toRingedSpace.carrier)) :
    DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient (AbelianSheaf Y.toRingedSpace.carrier)).obj L) ≅
      DerivedCategory.Plus.Q.obj L :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.quotientCompQhIso (AbelianSheaf Y.toRingedSpace.carrier)).app L.obj)

/-- The direct image of an injective abelian sheaf has right acyclic global sections. -/
theorem rightAcyclic_abelianPushforward_obj
    (I : AbelianSheaf X'.toRingedSpace.carrier) (hI : Injective I) :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightAcyclic
      ((abelianPushforward.{u, u} f.base).obj I) :=
  have : Injective ((abelianPushforward.{u, u} f.base).obj I) :=
    (abelianPushforward.{u, u} f.base).injective_obj_of_injective hI
  Functor.rightAcyclic_of_injective _ _

/-- **Stacks Project, Tag 01EZ, for abelian sheaves.** Derived global sections on `X'` are
derived global sections on `X` of the derived direct image. -/
noncomputable def derivedSectionsPushforwardIso :
    (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus ≅
      (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlus ⋙
        (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus :=
  compIso (abelianPushforward.{u, u} f.base) (sectionsFunctor X.toRingedSpace.carrier ⊤)
    (rightAcyclic_abelianPushforward_obj f)

/-- `f_*Ω^•_{X'/S'}`, as a bounded-below complex of abelian sheaves on `X`. -/
noncomputable def deRhamPushforwardPlus :
    CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier) :=
  ⟨((abelianPushforward.{u, u} f.base).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (SheafOfModules.deRhamAbelianComplexInt (deRhamAlgebras p')
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))), 0, inferInstance⟩

/-- The canonical map `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of bounded-below complexes of abelian
sheaves on `X`. -/
noncomputable def deRhamAbelianPushforwardMapPlus (hcomm : f ≫ p = p' ≫ g) :
    SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ⟶
      deRhamPushforwardPlus f p' :=
  ⟨(ComplexShape.embeddingUpNat.extendFunctor _).map
      (deRhamAbelianPushforwardMap f p p' g hcomm) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso
      (abelianPushforward.{u, u} f.base) _ ComplexShape.embeddingUpNat).hom⟩

/-- The homotopy-category identification of the pushforward of the de Rham complex. -/
noncomputable def quotDeRhamPushforwardIso :
    (abelianPushforward.{u, u} f.base).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj
          (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
            (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))) ≅
      (HomotopyCategory.Plus.quotient
        (AbelianSheaf X.toRingedSpace.carrier)).obj (deRhamPushforwardPlus f p') :=
  (HomotopyCategory.Plus.ι (AbelianSheaf X.toRingedSpace.carrier)).preimageIso
    (((abelianPushforward.{u, u} f.base).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app
        (SheafOfModules.deRhamAbelianComplexInt (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))))

/-- The derived-functor unit, read on the pushforward of the de Rham complex:
`f_*Ω^•_{X'/S'} ⟶ Rf_*Ω^•_{X'/S'}` in `D⁺`. -/
noncomputable def deRhamPushforwardToDerived :=
  (plusQIsoOn X (deRhamPushforwardPlus f p')).inv ≫
    DerivedCategory.Plus.Qh.map (quotDeRhamPushforwardIso f p').inv ≫
    (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient (AbelianSheaf X'.toRingedSpace.carrier)).obj
        (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))) ≫
    (abelianPushforward.{u, u} f.base).rightDerivedFunctorPlus.map
      (plusQIsoOn X' (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))).hom

/-- **Relative de Rham cohomology** `H^i_{dR}(X/S)` of a morphism of schemes: the `i`-th
cohomology of the derived global sections of the relative de Rham complex. -/
@[stacks 0FL6 "the definition `H^i_dR(X/S) = H^i(RΓ(X, Ω^•_{X/S}))`"]
noncomputable abbrev deRhamCohomology (p : X ⟶ S) (i : ℤ) : AddCommGrpCat.{u} :=
  SheafOfModules.deRhamCohomologyAbelian (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) i

/-- The canonical ring map `H^0(S, 𝒪_S) ⟶ Γ(X, p^{-1}𝒪_S)` on global sections, the unit of the
inverse-image adjunction over the whole space. -/
noncomputable def inverseImageGlobalSections (p : X ⟶ S) :
    S.sheaf.obj.obj (Opposite.op ⊤) ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf).obj.obj (Opposite.op ⊤) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.base).unit.app
    S.sheaf).hom.app (Opposite.op ⊤)

/-- **Relative de Rham cohomology is a module over `H^0(S, 𝒪_S)`**: the de Rham complex is a
complex of `p^{-1}𝒪_S`-modules, so its hypercohomology is a module over `Γ(X, p^{-1}𝒪_S)`, and
hence over `H^0(S, 𝒪_S)` along the unit of the inverse-image adjunction. -/
@[stacks 0FL6 "the `H^0(S, 𝒪_S)`-module structure on `H^i_dR(X/S)`"]
noncomputable def deRhamCohomologyBaseModule (p : X ⟶ S) (i : ℤ) :
    ModuleCat.{u} (S.sheaf.obj.obj (Opposite.op ⊤)) :=
  (ModuleCat.restrictScalars (inverseImageGlobalSections p).hom).obj
    (SheafOfModules.deRhamCohomology (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) i)

/-- **The pullback map `f^* : RΓ(X, Ω^•_{X/S}) ⟶ RΓ(X', Ω^•_{X'/S'})`** of a commutative square
of schemes: derived global sections of the canonical map of de Rham complexes, followed by the
identification of derived global sections on `X'` with derived global sections of the derived
direct image. -/
@[stacks 0FL6 "the pullback map `f^* : RΓ(X, Ω^•_{X/S}) ⟶ RΓ(X', Ω^•_{X'/S'})`"]
noncomputable def deRhamDerivedSectionsPullback (hcomm : f ≫ p = p' ≫ g) :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p)
            (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))) ⟶
      (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj
          (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
            (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))) :=
  (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map (deRhamAbelianPushforwardMapPlus f p p' g hcomm)) ≫
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (deRhamPushforwardToDerived f p') ≫
    (derivedSectionsPushforwardIso f).inv.app
      (DerivedCategory.Plus.Q.obj
        (SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p'))))

/-- **The pullback map `f^* : H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')`** of a commutative square of
schemes: the map induced on cohomology by the pullback map on derived global sections. -/
@[stacks 0FL6 "the pullback map `f^* : H^i_dR(X/S) ⟶ H^i_dR(X'/S')`"]
noncomputable def deRhamCohomologyPullback (hcomm : f ≫ p = p' ≫ g) (i : ℤ) :
    deRhamCohomology p i ⟶ deRhamCohomology p' i :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
    (deRhamDerivedSectionsPullback f p p' g hcomm)

end Derived

end AlgebraicGeometry.Scheme.Hom

end
