module

public import StacksFrontier.AlgebraicGeometry.DeRham.Functoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial

/-!
# The canonical map of differential forms of a composable pair, and the de Rham differential

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes. The canonical surjection
`Ω_{X/S} ⟶ Ω_{X/Y}` of [Stacks, Tag 01UX] is
`AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials`. This file extends it to **all degrees**,
as a homomorphism of sheaves of graded algebras `⋀ Ω_{X/S} ⟶ ⋀ Ω_{X/Y}`, and proves that the
resulting degreewise maps **commute with the de Rham differential**:

`d_{X/Y} ∘ ⋀ᵏ(Ω_{X/S} ⟶ Ω_{X/Y}) = ⋀^{k+1}(Ω_{X/S} ⟶ Ω_{X/Y}) ∘ d_{X/S}`.

This is the statement that `d_{X/Y}` is *induced* by `d_{X/S}`. It is what identifies the two
readings of the differential of a graded piece of the filtration of Section 0FMK: the Leibniz
rule produces `d_{X/S}` on the tensor side formed over `(f ∘ g)^{-1}𝒪_S`, while the differential
of the target complex is `d_{X/Y}` on the tensor side formed over `f^{-1}𝒪_Y`, and `d_{X/Y}` is
`f^{-1}𝒪_Y`-linear rather than `𝒪_X`-linear, so it cannot be moved across the tensor.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom`: **the canonical homomorphism of
  sheaves of graded algebras `⋀ Ω_{X/S} ⟶ ⋀ Ω_{X/Y}`** of a composable pair of morphisms of
  schemes, the unique unital homomorphism extending
  `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials`. Its degree-`n` component is the map
  `Ω^n_{X/S} ⟶ Ω^n_{X/Y}` on relative differential forms.

## Main results

* `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_app_d`: the canonical surjection
  `Ω_{X/S} ⟶ Ω_{X/Y}` carries `d_{X/S} a` to `d_{X/Y} a` on every local section `a` of `𝒪_X`.
* `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_exactOne` and
  `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_homogeneousProdLeft`: the canonical
  homomorphism carries the exact differential of a local section to the exact differential of
  the same section, and an ordered product of exact differentials to the ordered product of the
  same exact differentials read on `Ω_{X/Y}`.
* `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_comm`: **the canonical homomorphism
  commutes with the de Rham differential**, checked on the multiples of the exact wedges, which
  generate the sheaves of differential forms locally.
* `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_comm_d`: the same commutation read on
  the arrows of the two relative de Rham complexes.

## Implementation notes

**The route.** The homomorphism is `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map` of
`AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials`, i.e. it comes from the universal
property of the exterior algebra of `Ω_{X/S}` applied to the exterior algebra of `Ω_{X/Y}` with
its own degree-one generator composed with the canonical surjection. The alternative route is
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` ([Stacks, Tag 07HX]) at the
commutative square `(𝟙 X, f ≫ g, f, g)`; that route is dearer twice over, since its target
carries a direct image along `𝟙 X` which has to be identified with the identity functor, and
since it is built in abelian sheaves, which is one spelling further from the sheaves of modules
the graded pieces of Section 0FMK live in. Taking the universal property directly needs neither
identification, and the generic functoriality of the exterior algebra
(`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_id`,
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.map_comp`) comes with it.

**The commutation is checked sectionwise.** The de Rham differential is characterised on the
multiples of the exact wedges, and those generate the sheaf of `n`-forms locally
(`AlgebraicGeometry.SheafOfModules.locallyGeneratedByExactWedges`), so two additive natural
families out of `Ω^n_{X/S}` agreeing there agree
(`AlgebraicGeometry.SheafOfModules.eq_of_exactWedges`). Both generic lemmas are consumed inside
the proof rather than restated at these binders, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceCut`: a restatement of a generic lemma
about the de Rham differential at the binders of a morphism of schemes elaborates but exceeds
the kernel's budget for the definitional checks against degree normalisation.

## References

* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX)
* [Stacks Project, Section 50.2](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite SheafOfModules.GradedAlgebra

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The canonical map `Ω_{X/S} ⟶ Ω_{X/Y}` carries `d_{X/S} a` to `d_{X/Y} a`.** This is the
defining property of the canonical map of the square with horizontal edges `𝟙 X` and `g`
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d`), with the transpose along
`(𝟙 X)^* ⊣ (𝟙 X)_*` computed by
`AlgebraicGeometry.Scheme.Hom.pullbackId_adjoint_apply`. -/
theorem toRelativeDifferentials_app_d (U : X.Opens) (x : Γ(X, U)) :
    ((toRelativeDifferentials f g).app U).hom ((universalRelativeDerivation (f ≫ g)).d x) =
      (universalRelativeDerivation f).d x :=
  (pullbackId_adjoint_apply (relativeDifferentials (f ≫ g)) (relativeDifferentials f)
      (relativeDifferentialsMap (𝟙 X) (f ≫ g) f g (Category.id_comp (f ≫ g))) U
      ((universalRelativeDerivation (f ≫ g)).d x)).symm.trans
    (relativeDifferentialsMap_app_d (f := 𝟙 X) (p := f ≫ g) (p' := f) g
      (Category.id_comp (f ≫ g)) U x)

/-- **The canonical homomorphism of sheaves of graded algebras `⋀ Ω_{X/S} ⟶ ⋀ Ω_{X/Y}`** of a
composable pair `X ⟶ Y ⟶ S`: the unique unital homomorphism extending the canonical surjection
`AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials` on relative differentials. Its degree-`n`
component is the canonical map `Ω^n_{X/S} ⟶ Ω^n_{X/Y}` of relative differential forms. -/
noncomputable def deRhamFormsToRelativeHom :
    UnitalHom (relativeDifferentialFormsAlgebra (f ≫ g)) (relativeDifferentialFormsAlgebra f) :=
  (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials (f ≫ g))).map
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials f))
    (toRelativeDifferentials f g)

/-- In degree one the canonical homomorphism carries the exact differential of a local section
of `𝒪_X` to the exact differential of the same section, read on `Ω_{X/Y}`. -/
theorem deRhamFormsToRelativeHom_exactOne (U : (X.Opens)ᵒᵖ) (x : X.sheaf.obj.obj U) :
    ((deRhamFormsToRelativeHom f g).app 1).val.app U
        (SheafOfModules.exactOne (deRhamAlgebras (f ≫ g)) U x) =
      SheafOfModules.exactOne (deRhamAlgebras f) U x := by
  have hext := (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (relativeDifferentials (f ≫ g))).map_app_one
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (relativeDifferentials f))
    (toRelativeDifferentials f g)
  have h1 := congrArg (fun t : relativeDifferentials (f ≫ g) ⟶
      (relativeDifferentialFormsAlgebra f).piece 1 =>
    t.val.app U ((universalRelativeDerivation (f ≫ g)).d x)) hext
  exact h1.trans (congrArg ((Scheme.Modules.exteriorGenerator
    (relativeDifferentials f)).val.app U) (toRelativeDifferentials_app_d f g U.unop x))

/-- The canonical homomorphism carries an ordered product of exact differentials to the ordered
product of the same exact differentials, read on `Ω_{X/Y}`. -/
theorem deRhamFormsToRelativeHom_homogeneousProdLeft (U : (X.Opens)ᵒᵖ) (n : ℕ)
    (c : Fin n → X.sheaf.obj.obj U) :
    ((deRhamFormsToRelativeHom f g).app (n : ℤ)).val.app U
        ((deRhamAlgebras (f ≫ g)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
          fun i => SheafOfModules.exactOne (deRhamAlgebras (f ≫ g)) U (c i)) =
      (deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
        fun i => SheafOfModules.exactOne (deRhamAlgebras f) U (c i) := by
  induction n with
  | zero => exact (deRhamFormsToRelativeHom f g).map_one U
  | succ n ih =>
      have hA : (deRhamAlgebras (f ≫ g)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U
            (n + 1) (fun i => SheafOfModules.exactOne (deRhamAlgebras (f ≫ g)) U (c i)) =
          Stacks.degCast
            (F := fun k : ℤ =>
              (((relativeDifferentialFormsAlgebra (f ≫ g)).piece k).val.obj U : Type u))
            (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
            (((relativeDifferentialFormsAlgebra (f ≫ g)).mul 1 (n : ℤ)).app U
              (SheafOfModules.exactOne (deRhamAlgebras (f ≫ g)) U (c 0))
              ((deRhamAlgebras (f ≫ g)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
                fun i => SheafOfModules.exactOne (deRhamAlgebras (f ≫ g)) U (c i.succ))) := rfl
      have hB : (deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U
            (n + 1) (fun i => SheafOfModules.exactOne (deRhamAlgebras f) U (c i)) =
          Stacks.degCast
            (F := fun k : ℤ =>
              (((relativeDifferentialFormsAlgebra f).piece k).val.obj U : Type u))
            (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)
            (((relativeDifferentialFormsAlgebra f).mul 1 (n : ℤ)).app U
              (SheafOfModules.exactOne (deRhamAlgebras f) U (c 0))
              ((deRhamAlgebras f).exterior.toPresheafGradedAlgebra.homogeneousProdLeft U n
                fun i => SheafOfModules.exactOne (deRhamAlgebras f) U (c i.succ))) := rfl
      rw [hA, hB]
      refine (SheafOfModules.GradedAlgebra.UnitalHom.val_app_degCast
        (deRhamFormsToRelativeHom f g) U
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega) _).trans ?_
      refine congrArg (Stacks.degCast
        (F := fun k : ℤ =>
          (((relativeDifferentialFormsAlgebra f).piece k).val.obj U : Type u))
        (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)) ?_
      refine ((deRhamFormsToRelativeHom f g).map_mul 1 (n : ℤ) U _ _).trans ?_
      rw [deRhamFormsToRelativeHom_exactOne, ih fun i => c i.succ]

/-- **The canonical homomorphism commutes with the de Rham differential**: the differential
`d_{X/Y}` is induced by `d_{X/S}` along the canonical surjection `Ω_{X/S} ⟶ Ω_{X/Y}`, in every
degree. Checked on the multiples of the exact wedges, which generate the sheaves of relative
differential forms locally. -/
theorem deRhamFormsToRelativeHom_comm (n : ℕ) (U : (X.Opens)ᵒᵖ)
    (ω : ((deRhamAlgebras (f ≫ g)).exteriorPower n).val.obj U) :
    ((SheafOfModules.deRhamDifferential (deRhamAlgebras f)).differential n).val.app U
        (((deRhamFormsToRelativeHom f g).app (n : ℤ)).val.app U ω) =
      ((deRhamFormsToRelativeHom f g).app ((n + 1 : ℕ) : ℤ)).val.app U
        (((SheafOfModules.deRhamDifferential (deRhamAlgebras (f ≫ g))).differential n).val.app U
          ω) := by
  refine SheafOfModules.eq_of_exactWedges (deRhamAlgebras (f ≫ g)) n
    (N := (deRhamAlgebras f).exteriorPower (n + 1))
    (fun V => AddMonoidHom.comp
      (((SheafOfModules.deRhamDifferential (deRhamAlgebras f)).differential n).val.app
        V).hom.toAddMonoidHom
      (((deRhamFormsToRelativeHom f g).app (n : ℤ)).val.app V).hom.toAddMonoidHom)
    (fun V => AddMonoidHom.comp
      (((deRhamFormsToRelativeHom f g).app ((n + 1 : ℕ) : ℤ)).val.app V).hom.toAddMonoidHom
      (((SheafOfModules.deRhamDifferential (deRhamAlgebras (f ≫ g))).differential n).val.app
        V).hom.toAddMonoidHom)
    ?_ ?_ ?_ U ω
  · intro V W i x
    refine Eq.trans (congrArg (fun y =>
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras f)).differential n).val.app W y)
      (PresheafOfModules.naturality_apply
        ((deRhamFormsToRelativeHom f g).app (n : ℤ)).val i x)) ?_
    exact PresheafOfModules.naturality_apply
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras f)).differential n).val i _
  · intro V W i x
    refine Eq.trans (congrArg (fun y =>
      ((deRhamFormsToRelativeHom f g).app ((n + 1 : ℕ) : ℤ)).val.app W y)
      (PresheafOfModules.naturality_apply
        ((SheafOfModules.deRhamDifferential (deRhamAlgebras (f ≫ g))).differential n).val i x)) ?_
    exact PresheafOfModules.naturality_apply
      ((deRhamFormsToRelativeHom f g).app ((n + 1 : ℕ) : ℤ)).val i _
  · intro V b η hη
    obtain ⟨c, rfl⟩ :=
      SheafOfModules.exists_eq_homogeneousProdLeft (deRhamAlgebras (f ≫ g)) V n η hη
    refine Eq.trans (congrArg (fun y =>
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras f)).differential n).val.app V y)
      (PresheafOfModules.app_smul ((deRhamFormsToRelativeHom f g).app (n : ℤ)).val b
        ((deRhamAlgebras (f ≫ g)).exterior.toPresheafGradedAlgebra.homogeneousProdLeft V n
          fun i => SheafOfModules.exactOne (deRhamAlgebras (f ≫ g)) V (c i)))) ?_
    refine Eq.trans (congrArg (fun y : ((relativeDifferentialFormsAlgebra f).piece
        (n : ℤ)).val.obj V =>
      ((SheafOfModules.deRhamDifferential (deRhamAlgebras f)).differential n).val.app V
        (b • y)) (deRhamFormsToRelativeHom_homogeneousProdLeft f g V n c)) ?_
    refine Eq.trans (SheafOfModules.DeRhamDifferential.differential_smul_homogeneousProdLeft
      (deRhamAlgebras f) (SheafOfModules.deRhamDifferential (deRhamAlgebras f)) n V b c) ?_
    refine Eq.symm (Eq.trans (congrArg (fun y =>
      ((deRhamFormsToRelativeHom f g).app ((n + 1 : ℕ) : ℤ)).val.app V y)
      (SheafOfModules.DeRhamDifferential.differential_smul_homogeneousProdLeft
        (deRhamAlgebras (f ≫ g))
        (SheafOfModules.deRhamDifferential (deRhamAlgebras (f ≫ g))) n V b c)) ?_)
    exact deRhamFormsToRelativeHom_homogeneousProdLeft f g V (n + 1)
      (Fin.cons b c : Fin (n + 1) → X.sheaf.obj.obj V)

/-- The commutation of the canonical homomorphism with the arrows of the two relative de Rham
complexes: the degreewise maps `Ω^n_{X/S} ⟶ Ω^n_{X/Y}` are a map of complexes on sections. -/
theorem deRhamFormsToRelativeHom_comm_d (n : ℕ) (U : (X.Opens)ᵒᵖ)
    (ω : ((deRhamAlgebras (f ≫ g)).exteriorPower n).val.obj U) :
    ((deRhamComplex f).d n (n + 1)).val.app U
        (((deRhamFormsToRelativeHom f g).app (n : ℤ)).val.app U ω) =
      ((deRhamFormsToRelativeHom f g).app ((n + 1 : ℕ) : ℤ)).val.app U
        (((deRhamComplex (f ≫ g)).d n (n + 1)).val.app U ω) := by
  rw [deRhamComplex_d, deRhamComplex_d]
  exact deRhamFormsToRelativeHom_comm f g n U ω

end AlgebraicGeometry.Scheme.Hom

end
