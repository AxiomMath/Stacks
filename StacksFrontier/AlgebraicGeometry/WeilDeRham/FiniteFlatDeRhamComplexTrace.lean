module

public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.AlgebraicGeometry.FormsTrace.Proposition
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenFormsMapSections
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteFlatDeRhamTraceOne

/-!
# The trace map of de Rham complexes of a finite syntomic morphism

Let `f : X ⟶ P` be a finite syntomic morphism of schemes and `sP : P ⟶ S` a morphism. By Stacks,
Proposition 0FLC (3), the trace maps of Lemma 0FLB induce a map of complexes
`Θ_f : f_*Ω^•_{X/S} ⟶ Ω^•_{P/S}`. This file records it as a map of complexes of abelian sheaves
(`Stacks.WeilDeRham.deRhamAbelianTraceMap`) and proves the statement used in the proof of
Axiom (A6) for de Rham cohomology (Stacks, Section 0FWC): **if `f_*𝒪_X` is finite locally free of
constant rank `e`, the composite of `Θ_f` with the canonical map `Ω^•_{P/S} ⟶ f_*Ω^•_{X/S}` is
multiplication by `e`.**

## Main definitions

* `Stacks.WeilDeRham.deRhamAbelianTraceMap`: the trace map `f_*Ω^•_{X/S} ⟶ Ω^•_{P/S}` of
  abelian de Rham complexes.

## Main results

* `Stacks.WeilDeRham.absoluteToRelativeFormsMap_homogeneousProdLeft` and
  `Stacks.WeilDeRham.relativeDifferentialFormsPullback_homogeneousProdLeft`: the
  absolute-to-relative comparison and the pullback of forms on exact wedges.
* `Stacks.WeilDeRham.relativeFormsTrace_deRhamFormsPushforwardHom`: `Θ_S(f^*ω) = e · ω` on local
  relative forms.
* `Stacks.WeilDeRham.deRhamAbelianPushforwardMap_comp_deRhamAbelianTraceMap`: the composite
  `Ω^•_{P/S} ⟶ f_*Ω^•_{X/S} ⟶ Ω^•_{P/S}` is `e • 𝟙`.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.WeilDeRham

open Stacks.AlgebraicGeometry.AffineOpenDifferentialForms
  (isExteriorAlgebra_relativeDifferentialFormsAlgebra)

/-! ### The absolute-to-relative comparison on exact wedges -/

/-- The exact wedge `d c₀ ∧ ⋯ ∧ d cₙ` is `d c₀` wedged with the exact wedge of the remaining
terms, up to transport along `1 + n = n + 1`. -/
private theorem homogeneousProdLeft_exactOne_succ {X S : Scheme.{u}} (a : X ⟶ S)
    (U : (X.Opens)ᵒᵖ) (n : ℕ) (c : Fin (n + 1) → X.sheaf.obj.obj U) :
    (deRhamAlgebras a).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U (n + 1)
        (fun i => SheafOfModules.exactOne (deRhamAlgebras a) U (c i)) =
      Stacks.degCast
        (F := fun k : ℤ => (((relativeDifferentialFormsAlgebra a).piece k).val.obj U : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
        (((relativeDifferentialFormsAlgebra a).mul 1 (n : ℤ)).app U
          (SheafOfModules.exactOne (deRhamAlgebras a) U (c 0))
          ((deRhamAlgebras a).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
            fun i => SheafOfModules.exactOne (deRhamAlgebras a) U (c i.succ))) := rfl

section AbsoluteToRelative

variable {X S : Scheme.{u}} (g : X ⟶ S)

/-- **The comparison `Ω^1_{X/ℤ} ⟶ Ω^1_{X/S}` carries the absolute exact differential `d x` to the
relative one.** -/
theorem absoluteToRelativeFormsMap_exactOne (U : (X.Opens)ᵒᵖ) (x : X.sheaf.obj.obj U) :
    (g.absoluteToRelativeFormsMap 1).val.app U
        (SheafOfModules.exactOne (deRhamAlgebras X.toSpecZ) U x) =
      SheafOfModules.exactOne (deRhamAlgebras g) U x := by
  have hext := (isExteriorAlgebra_relativeDifferentialFormsAlgebra X.toSpecZ).map_app_one
    (isExteriorAlgebra_relativeDifferentialFormsAlgebra g) (absoluteToRelativeDifferentials g)
  have h1 := congrArg (fun t : relativeDifferentials X.toSpecZ ⟶
      (relativeDifferentialFormsAlgebra g).piece 1 =>
    t.val.app U ((universalRelativeDerivation X.toSpecZ).d x)) hext
  exact h1.trans (congrArg ((Scheme.Modules.exteriorGenerator
    (relativeDifferentials g)).val.app U) (absoluteToRelativeDifferentials_app_d g U.unop x))

/-- **The comparison `Ω^n_{X/ℤ} ⟶ Ω^n_{X/S}` carries the absolute exact wedge
`d c₁ ∧ ⋯ ∧ d cₙ` to the relative exact wedge `d c₁ ∧ ⋯ ∧ d cₙ`.** -/
theorem absoluteToRelativeFormsMap_homogeneousProdLeft (U : (X.Opens)ᵒᵖ) (n : ℕ)
    (c : Fin n → X.sheaf.obj.obj U) :
    (g.absoluteToRelativeFormsMap (n : ℤ)).val.app U
        ((deRhamAlgebras X.toSpecZ).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
          fun i => SheafOfModules.exactOne (deRhamAlgebras X.toSpecZ) U (c i)) =
      (deRhamAlgebras g).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
        fun i => SheafOfModules.exactOne (deRhamAlgebras g) U (c i) := by
  induction n with
  | zero => exact ((isExteriorAlgebra_relativeDifferentialFormsAlgebra X.toSpecZ).map
      (isExteriorAlgebra_relativeDifferentialFormsAlgebra g)
      (absoluteToRelativeDifferentials g)).map_one U
  | succ n ih =>
      rw [homogeneousProdLeft_exactOne_succ, homogeneousProdLeft_exactOne_succ]
      refine (SheafOfModules.GradedAlgebra.UnitalHom.val_app_degCast
        ((isExteriorAlgebra_relativeDifferentialFormsAlgebra X.toSpecZ).map
          (isExteriorAlgebra_relativeDifferentialFormsAlgebra g)
          (absoluteToRelativeDifferentials g)) U
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega) _).trans ?_
      refine congrArg (Stacks.degCast
        (F := fun k : ℤ =>
          (((relativeDifferentialFormsAlgebra g).piece k).val.obj U : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)) ?_
      refine (((isExteriorAlgebra_relativeDifferentialFormsAlgebra X.toSpecZ).map
          (isExteriorAlgebra_relativeDifferentialFormsAlgebra g)
          (absoluteToRelativeDifferentials g)).map_mul 1 (n : ℤ) U _ _).trans ?_
      exact congrArg₂ (fun x y => ((relativeDifferentialFormsAlgebra g).mul 1 (n : ℤ)).app U x y)
        (absoluteToRelativeFormsMap_exactOne g U (c 0)) (ih fun i => c i.succ)

end AbsoluteToRelative

/-! ### Pulling back exact wedges along a commutative square -/

section Pullback

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (a : X ⟶ S) (a' : X' ⟶ S') (g : S' ⟶ S)
  (hcomm : f ≫ a = a' ≫ g)

/-- Pulling back a local differential form commutes with transport along an equality of
degrees. -/
theorem relativeDifferentialFormsPullback_degCast (U : X.Opens) {i j : ℤ} (h : i = j)
    (x : Γ(relativeDifferentialForms a i, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm j U
        (Stacks.degCast (F := fun k : ℤ =>
          (((relativeDifferentialFormsAlgebra a).piece k).val.obj (op U) : Type u)) h x) =
      Stacks.degCast (F := fun k : ℤ =>
          (((relativeDifferentialFormsAlgebra a').piece k).val.obj (op (f ⁻¹ᵁ U)) : Type u)) h
        (relativeDifferentialFormsPullback f a a' g hcomm i U x) := by
  subst h
  rfl

/-- **Pulling back a local differential form along a commutative square carries the exact wedge
`d c₁ ∧ ⋯ ∧ d cₙ` to the exact wedge `d f^♯c₁ ∧ ⋯ ∧ d f^♯cₙ`.** -/
theorem relativeDifferentialFormsPullback_homogeneousProdLeft (U : X.Opens) (n : ℕ)
    (c : Fin n → Γ(X, U)) :
    relativeDifferentialFormsPullback f a a' g hcomm (n : ℤ) U
        ((deRhamAlgebras a).exterior.toPresheafGradedAlgebra.homogeneousProdLeft (op U) n
          fun i => SheafOfModules.exactOne (deRhamAlgebras a) (op U) (c i)) =
      (deRhamAlgebras a').exterior.toPresheafGradedAlgebra.homogeneousProdLeft
        (op (f ⁻¹ᵁ U)) n fun i => SheafOfModules.exactOne (deRhamAlgebras a')
          (op (f ⁻¹ᵁ U)) ((f.app U).hom (c i)) := by
  induction n with
  | zero => exact relativeDifferentialFormsPullback_one f a a' g hcomm U
  | succ n ih =>
      refine (relativeDifferentialFormsPullback_degCast f a a' g hcomm U
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega) _).trans ?_
      refine congrArg (Stacks.degCast
        (F := fun k : ℤ =>
          (((relativeDifferentialFormsAlgebra a').piece k).val.obj (op (f ⁻¹ᵁ U)) : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)) ?_
      refine (relativeDifferentialFormsPullback_mul f a a' g hcomm 1 (n : ℤ) U _ _).trans ?_
      exact congrArg₂ (fun x y => ((relativeDifferentialFormsAlgebra a').mul 1 (n : ℤ)).app
        (op (f ⁻¹ᵁ U)) x y) (relativeDifferentialFormsPullback_exteriorGenerator_d f a a' g hcomm U
          (c 0)) (ih fun i => c i.succ)

end Pullback

/-! ### The trace composed with the canonical map is multiplication by the rank -/

section Degree

variable {X P S : Scheme.{u}} (f : X ⟶ P) (sP : P ⟶ S) [IsFinite f] (hf : Syntomic f) (e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e]

/-- **`Θ_S ∘ f^* = e` on relative differential forms.** Let `f : X ⟶ P` be finite syntomic with
`f_*𝒪_X` finite locally free of rank `e`, and let `sP : P ⟶ S`. The canonical map
`Ω^n_{P/S} ⟶ f_*Ω^n_{X/S}` of the square `f ≫ sP = (f ≫ sP) ≫ 𝟙 S` (Tag 07HX), followed by the
trace on relative forms `Θ^n_{X/P, S} : f_*Ω^n_{X/S} ⟶ Ω^n_{P/S}` of Proposition 0FLC (3), is
multiplication by `e`. -/
theorem relativeFormsTrace_deRhamFormsPushforwardHom
    (n : ℕ) (U : (P.Opens)ᵒᵖ) (x : ((relativeDifferentialFormsAlgebra sP).piece n).val.obj U) :
    (f.relativeFormsTrace sP hf n).val.app U
        (((deRhamFormsPushforwardHom f sP (f ≫ sP) (𝟙 S) (Category.comp_id _).symm).app
          (n : ℤ)).val.app U x) = e • x := by
  refine SheafOfModules.eq_of_exactWedges (deRhamAlgebras sP) n
    (N := (deRhamAlgebras sP).exteriorPower n)
    (fun V => AddMonoidHom.comp ((f.relativeFormsTrace sP hf n).val.app V).hom.toAddMonoidHom
      (((deRhamFormsPushforwardHom f sP (f ≫ sP) (𝟙 S)
        (Category.comp_id _).symm).app (n : ℤ)).val.app V).hom.toAddMonoidHom)
    (fun V => e • AddMonoidHom.id _) ?_ ?_ ?_ U x
  · intro V W i y
    refine Eq.trans (congrArg (fun z => (f.relativeFormsTrace sP hf n).val.app W z)
      (PresheafOfModules.naturality_apply ((deRhamFormsPushforwardHom f sP (f ≫ sP) (𝟙 S)
        (Category.comp_id _).symm).app (n : ℤ)).val i y)) ?_
    exact PresheafOfModules.naturality_apply (f.relativeFormsTrace sP hf n).val i _
  · intro V W i y
    exact (map_nsmul (((deRhamAlgebras sP).exteriorPower n).val.map i).hom e y).symm
  · intro V b ω hω
    obtain ⟨c, rfl⟩ :=
      SheafOfModules.exists_eq_homogeneousProdLeft (deRhamAlgebras sP) V n ω hω
    induction V with | op V => ?_
    have := AlgebraicGeometry.flat hf
    have := AlgebraicGeometry.locallyOfFinitePresentation hf
    have hcomm : f ≫ sP = (f ≫ sP) ≫ 𝟙 S := (Category.comp_id _).symm
    have hcommZ : f ≫ P.toSpecZ = X.toSpecZ ≫ 𝟙 _ := Scheme.comp_toSpecZ f
    have step1 : id (α := Γ(relativeDifferentialForms (f ≫ sP) n, f ⁻¹ᵁ V))
        ((((deRhamFormsPushforwardHom f sP (f ≫ sP) (𝟙 S) hcomm).app (n : ℤ)).val.app (op V))
          (id (α := P.sheaf.obj.obj (op V)) b •
            (deRhamAlgebras sP).exterior.toPresheafGradedAlgebra.homogeneousProdLeft (op V) n
              fun i => SheafOfModules.exactOne (deRhamAlgebras sP) (op V) (c i))) =
        (f.app V).hom b • id (α := Γ(relativeDifferentialForms (f ≫ sP) n, f ⁻¹ᵁ V))
          ((deRhamAlgebras (f ≫ sP)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft
            (op (f ⁻¹ᵁ V)) n fun i =>
              SheafOfModules.exactOne (deRhamAlgebras (f ≫ sP)) _ ((f.app V).hom (c i))) :=
      (deRhamFormsPushforwardHom_smul f sP (f ≫ sP) (𝟙 S) hcomm (n : ℤ) (op V) b _).trans
        (congrArg (fun z => (f.app V).hom b •
            id (α := Γ(relativeDifferentialForms (f ≫ sP) n, f ⁻¹ᵁ V)) z)
          (deRhamFormsPushforwardHom_homogeneousProdLeft f sP (f ≫ sP) (𝟙 S) hcomm (op V) n c))
    have step2 := absoluteToRelativeFormsMap_homogeneousProdLeft (f ≫ sP) (op (f ⁻¹ᵁ V)) n
      fun i => (f.app V).hom (c i)
    have step3 := (relativeDifferentialFormsPullback_smul f P.toSpecZ X.toSpecZ (𝟙 _) hcommZ
      (n : ℤ) V b _).trans (congrArg (fun z => (f.app V).hom b •
          id (α := Γ(Scheme.absoluteDifferentialForms X n, f ⁻¹ᵁ V)) z)
        (relativeDifferentialFormsPullback_homogeneousProdLeft f P.toSpecZ X.toSpecZ (𝟙 _)
          hcommZ V n c))
    have step4 := congr($(relativeFormsTrace_comp_formsTrace (f := f) sP (p := n) hf).val.app
      (op V))
    have step5 := f.formsTrace_smul_absoluteFormsPullback hf n V 1
    have step6 := absoluteToRelativeFormsMap_homogeneousProdLeft sP (op V) n c
    have e1 := step1.trans ((congrArg (fun z => (f.app V).hom b •
        id (α := Γ(relativeDifferentialForms (f ≫ sP) n, f ⁻¹ᵁ V)) z) step2.symm).trans
      ((Scheme.Modules.Hom.app_smul (U := f ⁻¹ᵁ V) ((f ≫ sP).absoluteToRelativeFormsMap n)
        ((f.app V).hom b) _).symm.trans
      (congrArg (((f ≫ sP).absoluteToRelativeFormsMap n).val.app (op (f ⁻¹ᵁ V))).hom
        step3.symm)))
    refine (congrArg ((f.relativeFormsTrace sP hf n).val.app (op V)).hom e1).trans ?_
    refine (ConcreteCategory.congr_hom step4 _).trans ?_
    have e2 : ∀ w : Γ(Scheme.absoluteDifferentialForms P n, V),
        (f.formsTrace hf n).app V (f.absoluteFormsPullback n V w) = e • w := by
      intro w
      have h5 := step5 w
      rw [one_smul] at h5
      exact h5.trans ((congrArg (fun r : Γ(P, V) => r • w) (finiteTrace_app_one f e V)).trans
        (Nat.cast_smul_eq_nsmul _ _ _))
    refine (congrArg ((sP.absoluteToRelativeFormsMap n).val.app (op V)).hom (e2 _)).trans ?_
    refine (map_nsmul _ _ _).trans ?_
    refine congrArg (fun z => e • z)
      ((Scheme.Modules.Hom.app_smul (U := V) (sP.absoluteToRelativeFormsMap n)
        (show Γ(P, V) from b) _).trans ?_)
    exact congrArg (fun z => (show Γ(P, V) from b) • z) step6

end Degree

/-! ### The trace map of de Rham complexes -/

section Complex

open Stacks.Cohomology.LerayLowDegree

variable {X P S : Scheme.{u}} (f : X ⟶ P) (sP : P ⟶ S) [IsFinite f] (hf : Syntomic f) (e : ℕ)

/-- **The trace map of relative de Rham complexes** `f_*Ω^•_{X/S} ⟶ Ω^•_{P/S}` of a finite
syntomic morphism `f : X ⟶ P` over `sP : P ⟶ S` (Proposition 0FLC (3)), read in abelian sheaves:
in degree `n` it is the trace on relative forms
`AlgebraicGeometry.Scheme.Hom.relativeFormsTrace`. -/
def deRhamAbelianTraceMap :
    ((abelianPushforward.{u, u} f.base).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (SheafOfModules.deRhamAbelianComplex (deRhamAlgebras (f ≫ sP))
          (SheafOfModules.deRhamDifferential (deRhamAlgebras (f ≫ sP)))) ⟶
      SheafOfModules.deRhamAbelianComplex (deRhamAlgebras sP)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras sP)) where
  f n := (_root_.SheafOfModules.toSheaf.{u, u, u, u} P.ringCatSheaf).map
    (f.relativeFormsTrace sP hf n)
  comm' := by
    rintro n m rfl
    ext U x
    exact (relativeFormsTrace_deRhamComplex_d sP n hf U.unop x).symm

/-- **The canonical map `Ω^•_{P/S} ⟶ f_*Ω^•_{X/S}` followed by the trace map is multiplication by
the rank `e` of `f_*𝒪_X`**, as a map of complexes of abelian sheaves. -/
theorem deRhamAbelianPushforwardMap_comp_deRhamAbelianTraceMap
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) e] :
    deRhamAbelianPushforwardMap f sP (f ≫ sP) (𝟙 S) (Category.comp_id _).symm ≫
        deRhamAbelianTraceMap f sP hf = e • 𝟙 _ := by
  ext n U x
  exact relativeFormsTrace_deRhamFormsPushforwardHom f sP hf e n U x

end Complex

end Stacks.WeilDeRham

end
