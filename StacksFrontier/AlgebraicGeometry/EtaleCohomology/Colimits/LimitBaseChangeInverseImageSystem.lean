module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison

/-!
# The inverse image of a presented system along a morphism of inverse systems

Let `e : D' ⟶ D` be a morphism of inverse systems of schemes over `Iᵒᵖ` and let `(ℱ_i, φ_{i'i})`
be a system of abelian sheaves on `D` in the sense of [Stacks, Tag 0EZL]. The inverse images
`e_i^{-1}ℱ_i` form a system of sheaves on `D'`: the transition at `i' ≥ i` is the comparison of
the inverse images along the two sides of the naturality square `D'(a) ≫ e_j = e_i ≫ D(a)`,
followed by `e_i^{-1}φ_{i'i}`. If `c'` and `c` are cones over `D'` and `D` and `e_∞ : c'.pt ⟶ c.pt`
is compatible with the projections, then for a sheaf `ℱ` presented as `colim f_i^{-1}ℱ_i` the
inverse image `e_∞^{-1}ℱ` is presented as `colim f'_i^{-1}e_i^{-1}ℱ_i`: inverse image is a left
adjoint.

This is the first step of the proof of [Stacks, Tag 0EZT]: `e^{-1}ℱ = colim e^{-1}p_i^{-1}ℱ_i =
colim q_i^{-1}e_i^{-1}ℱ_i`, which is the system to which [Stacks, Tag 0EYM] is applied for the
base changed morphisms `h_i`.

Everything here is in the vocabulary of `Stacks.EtaleCohomology.smallEtalePullbackAb`, the
abstract left adjoint, which is the one of the base change map
`Stacks.EtaleCohomology.higherBaseChangeMapAb` and of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`, and every
comparison is built from `Stacks.EtaleCohomology.smallEtalePullbackAbComp'`, which is also the one
of the pasting law `Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app_named`.
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemBaseChange` is the same construction for
the constructed inverse image `Stacks.EtaleCohomology.etaleAbelianInverseImage`.)

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackAbSquareIso` — the comparison
  `f'^{-1}e^{-1} ≅ e'^{-1}f^{-1}` of the two composite inverse images of a commutative square.
* `Stacks.EtaleCohomology.smallEtalePullbackAbSquareMap` — that comparison followed by the inverse
  image of a map `f^{-1}A ⟶ B`.
* `Stacks.EtaleCohomology.LimitBaseChange.inverseImageSystem` — the system `e_i^{-1}ℱ_i` on `D'`.
* `Stacks.EtaleCohomology.LimitBaseChange.inverseImageSystemLeg` — the legs
  `f'_i^{-1}e_i^{-1}ℱ_i ⟶ e_∞^{-1}ℱ`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbComp'_hom_app_comp` — the associativity pentagon
  of the comparison of inverse images, at a sheaf.
* `Stacks.EtaleCohomology.smallEtalePullbackAbSquareIso_hcomp`,
  `Stacks.EtaleCohomology.smallEtalePullbackAbSquareIso_vcomp` — the comparison of a pasted
  square is the composite of the comparisons of its two halves, for horizontal and for vertical
  pasting.
* `Stacks.EtaleCohomology.LimitBaseChange.isPullbackColimitPresentation_inverseImageSystem` —
  the inverse image of a colimit presentation is a colimit presentation of the inverse image of
  the system.

## Implementation notes

The comparisons and the maps built from them are defined for an arbitrary commutative square of
schemes and only then applied to the squares of an inverse system. A morphism defined directly at
the squares of an inverse system and compared, by unfolding, with the composite it abbreviates
is checked by the kernel only after unfolding the inverse image functors, which does not
terminate in reasonable time; the generic definitions do not have this problem.

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-! ### The associativity pentagon -/

/-- The associativity pentagon of `Stacks.EtaleCohomology.smallEtalePullbackAbComp'`, at a sheaf:
the two ways of comparing `j^{-1}i^{-1}f^{-1}G` with `p^{-1}G` agree. -/
theorem smallEtalePullbackAbComp'_hom_app_comp {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀)
    (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁)
    (hq : q = j ≫ i) (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a)
    (G : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (smallEtalePullbackAbComp' j i q hq).hom.app ((smallEtalePullbackAb f).obj G) ≫
        (smallEtalePullbackAbComp' q f p hp₁).hom.app G =
      (smallEtalePullbackAb j).map ((smallEtalePullbackAbComp' i f a ha).hom.app G) ≫
        (smallEtalePullbackAbComp' j a p hp₂).hom.app G := by
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] using
    congrArg (fun z => z.hom.app G) (smallEtalePullbackAbComp'_assoc j i f q hq a ha p hp₁ hp₂)

/-! ### The comparison attached to a commutative square -/

section Square

variable {X' X Y' Y : Scheme.{u}} (f' : X' ⟶ Y') (e' : X' ⟶ X) (e : Y' ⟶ Y) (f : X ⟶ Y)
  (P : X' ⟶ Y) (h₁ : P = f' ≫ e) (h₂ : P = e' ≫ f)

/-- **The comparison of the two composite inverse images of a commutative square**
`f' ≫ e = e' ≫ f`, with the common composite named `P`:
`f'^{-1}e^{-1} ≅ P^{-1} ≅ e'^{-1}f^{-1}`. -/
def smallEtalePullbackAbSquareIso :
    smallEtalePullbackAb e ⋙ smallEtalePullbackAb f' ≅
      smallEtalePullbackAb f ⋙ smallEtalePullbackAb e' :=
  smallEtalePullbackAbComp' f' e P h₁ ≪≫ (smallEtalePullbackAbComp' e' f P h₂).symm

/-- The component at `A` of `Stacks.EtaleCohomology.smallEtalePullbackAbSquareIso` is the
comparison `f'^{-1}e^{-1}A ≅ P^{-1}A` followed by the inverse of `e'^{-1}f^{-1}A ≅ P^{-1}A`. -/
theorem smallEtalePullbackAbSquareIso_hom_app (A : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).hom.app A =
      (smallEtalePullbackAbComp' f' e P h₁).hom.app A ≫
        (smallEtalePullbackAbComp' e' f P h₂).inv.app A :=
  rfl

/-- The comparison of the two composite inverse images of a commutative square, followed by the
inverse image along `e'` of a map `f^{-1}A ⟶ B`. -/
def smallEtalePullbackAbSquareMap (A : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (B : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (φ : (smallEtalePullbackAb f).obj A ⟶ B) :
    (smallEtalePullbackAb f').obj ((smallEtalePullbackAb e).obj A) ⟶
      (smallEtalePullbackAb e').obj B :=
  (smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).hom.app A ≫ (smallEtalePullbackAb e').map φ

/-- `Stacks.EtaleCohomology.smallEtalePullbackAbSquareMap` is the component at `A` of the
comparison of the square followed by `e'^{-1}φ`. -/
theorem smallEtalePullbackAbSquareMap_eq (A : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (B : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (φ : (smallEtalePullbackAb f).obj A ⟶ B) :
    smallEtalePullbackAbSquareMap f' e' e f P h₁ h₂ A B φ =
      (smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).hom.app A ≫
        (smallEtalePullbackAb e').map φ :=
  rfl

/-- `Stacks.EtaleCohomology.smallEtalePullbackAbSquareMap` into a direct image, followed by the
counit, is the comparison followed by the transpose. -/
theorem smallEtalePullbackAbSquareMap_comp_counit (A : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (G : Sheaf (smallEtaleTopology X') Ab.{u + 1})
    (φ : (smallEtalePullbackAb f).obj A ⟶ (smallEtalePushforwardAb e').obj G) :
    smallEtalePullbackAbSquareMap f' e' e f P h₁ h₂ A _ φ ≫
        (smallEtaleAdjunctionAb e').counit.app G =
      (smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).hom.app A ≫
        ((smallEtaleAdjunctionAb e').homEquiv _ _).symm φ := by
  rw [smallEtalePullbackAbSquareMap_eq, Category.assoc, Adjunction.homEquiv_counit]

end Square

/-! ### Pasting -/

/-- **The comparison of a horizontally pasted square** is the composite of the comparisons of its
two halves, read through the comparisons of the inverse images along the two composites: three
associativity pentagons. -/
theorem smallEtalePullbackAbSquareIso_hcomp {X'₀ X'₁ X'₂ X₀ X₁ X₂ : Scheme.{u}}
    (f'₁ : X'₀ ⟶ X'₁) (f'₂ : X'₁ ⟶ X'₂) (f'₁₂ : X'₀ ⟶ X'₂) (h' : f'₁₂ = f'₁ ≫ f'₂)
    (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₁₂ : X₀ ⟶ X₂) (h : f₁₂ = f₁ ≫ f₂)
    (e₀ : X'₀ ⟶ X₀) (e₁ : X'₁ ⟶ X₁) (e₂ : X'₂ ⟶ X₂)
    (P₁ : X'₀ ⟶ X₁) (hP₁ : P₁ = f'₁ ≫ e₁) (hP₁' : P₁ = e₀ ≫ f₁)
    (P₂ : X'₁ ⟶ X₂) (hP₂ : P₂ = f'₂ ≫ e₂) (hP₂' : P₂ = e₁ ≫ f₂)
    (P : X'₀ ⟶ X₂) (hP : P = f'₁₂ ≫ e₂) (hP' : P = e₀ ≫ f₁₂)
    (A : Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) :
    (smallEtalePullbackAbComp' f'₁ f'₂ f'₁₂ h').inv.app ((smallEtalePullbackAb e₂).obj A) ≫
        (smallEtalePullbackAb f'₁).map
          ((smallEtalePullbackAbSquareIso f'₂ e₁ e₂ f₂ P₂ hP₂ hP₂').hom.app A) ≫
        (smallEtalePullbackAbSquareIso f'₁ e₀ e₁ f₁ P₁ hP₁ hP₁').hom.app
          ((smallEtalePullbackAb f₂).obj A) ≫
        (smallEtalePullbackAb e₀).map ((smallEtalePullbackAbComp' f₁ f₂ f₁₂ h).hom.app A) =
      (smallEtalePullbackAbSquareIso f'₁₂ e₀ e₂ f₁₂ P hP hP').hom.app A := by
  have hW₁ : P = P₁ ≫ f₂ := by rw [hP', h, hP₁', Category.assoc]
  have hW₂ : P = f'₁ ≫ P₂ := by rw [hP, h', hP₂, Category.assoc]
  have Q₁ := smallEtalePullbackAbComp'_hom_app_comp f₂ f₁ e₀ f₁₂ h P₁ hP₁' P hW₁ hP' A
  have Q₂ := smallEtalePullbackAbComp'_hom_app_comp f₂ e₁ f'₁ P₂ hP₂' P₁ hP₁ P hW₁ hW₂ A
  have Q₃ := smallEtalePullbackAbComp'_hom_app_comp e₂ f'₂ f'₁ P₂ hP₂ f'₁₂ h' P hP hW₂ A
  simp only [smallEtalePullbackAbSquareIso_hom_app, (smallEtalePullbackAb f'₁).map_comp]
  rw [← cancel_mono ((smallEtalePullbackAbComp' e₀ f₁₂ P hP').hom.app A)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← Q₁, Iso.inv_hom_id_app_assoc, Q₂, ← Functor.map_comp_assoc (smallEtalePullbackAb f'₁)
    ((smallEtalePullbackAbComp' e₁ f₂ P₂ hP₂').inv.app A), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, ← Q₃, Iso.inv_hom_id_app_assoc]

/-- **The comparison of a vertically pasted square** is the composite of the comparisons of its
two halves, read through the comparisons of the inverse images along the two composites: three
associativity pentagons. -/
theorem smallEtalePullbackAbSquareIso_vcomp {X' Y' X Y X₀ Y₀ : Scheme.{u}}
    (f' : X' ⟶ Y') (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀)
    (e'₁ : X' ⟶ X) (e'₂ : X ⟶ X₀) (e'₁₂ : X' ⟶ X₀) (hE' : e'₁₂ = e'₁ ≫ e'₂)
    (e₁ : Y' ⟶ Y) (e₂ : Y ⟶ Y₀) (e₁₂ : Y' ⟶ Y₀) (hE : e₁₂ = e₁ ≫ e₂)
    (PU : X' ⟶ Y) (hPU : PU = f' ≫ e₁) (hPU' : PU = e'₁ ≫ f)
    (PW : X ⟶ Y₀) (hPW : PW = f ≫ e₂) (hPW' : PW = e'₂ ≫ f₀)
    (P : X' ⟶ Y₀) (hP : P = f' ≫ e₁₂) (hP' : P = e'₁₂ ≫ f₀)
    (A : Sheaf (smallEtaleTopology Y₀) Ab.{u + 1}) :
    (smallEtalePullbackAb f').map ((smallEtalePullbackAbComp' e₁ e₂ e₁₂ hE).inv.app A) ≫
        (smallEtalePullbackAbSquareIso f' e'₁ e₁ f PU hPU hPU').hom.app
          ((smallEtalePullbackAb e₂).obj A) ≫
        (smallEtalePullbackAb e'₁).map
          ((smallEtalePullbackAbSquareIso f e'₂ e₂ f₀ PW hPW hPW').hom.app A) ≫
        (smallEtalePullbackAbComp' e'₁ e'₂ e'₁₂ hE').hom.app ((smallEtalePullbackAb f₀).obj A) =
      (smallEtalePullbackAbSquareIso f' e'₁₂ e₁₂ f₀ P hP hP').hom.app A := by
  have hV₁ : P = e'₁ ≫ PW := by rw [hP', hE', hPW', Category.assoc]
  have hV₂ : P = PU ≫ e₂ := by rw [hP, hE, hPU, Category.assoc]
  have V₁ := smallEtalePullbackAbComp'_hom_app_comp f₀ e'₂ e'₁ PW hPW' e'₁₂ hE' P hP' hV₁ A
  have V₂ := smallEtalePullbackAbComp'_hom_app_comp e₂ f e'₁ PW hPW PU hPU' P hV₂ hV₁ A
  have V₃ := smallEtalePullbackAbComp'_hom_app_comp e₂ e₁ f' e₁₂ hE PU hPU P hV₂ hP A
  simp only [smallEtalePullbackAbSquareIso_hom_app, (smallEtalePullbackAb e'₁).map_comp]
  rw [← cancel_mono ((smallEtalePullbackAbComp' e'₁₂ f₀ P hP').hom.app A)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [V₁, ← Functor.map_comp_assoc (smallEtalePullbackAb e'₁)
    ((smallEtalePullbackAbComp' e'₂ f₀ PW hPW').inv.app A), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, ← V₂, Iso.inv_hom_id_app_assoc, V₃,
    ← Functor.map_comp_assoc (smallEtalePullbackAb f'), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The rearrangement behind `smallEtalePullbackAbSquareMap_hcomp`, in an abstract category. -/
theorem squareMap_hcomp_algebra {C : Type*} [Category* C]
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ o₇ : C} {x : o₀ ⟶ o₁} {M : o₁ ⟶ o₃} {n : o₁ ⟶ o₂}
    {E : o₂ ⟶ o₃} {S₁ : o₃ ⟶ o₄} {Φ₁ : o₄ ⟶ o₅} {S₁' : o₂ ⟶ o₆} {Q : o₆ ⟶ o₄}
    {c : o₆ ⟶ o₇} {Φ₁₂ : o₇ ⟶ o₅} {S : o₀ ⟶ o₇} {L₁ : o₃ ⟶ o₅} {L : o₀ ⟶ o₅}
    (hM : M = n ≫ E) (hL₁ : L₁ = S₁ ≫ Φ₁) (hL : L = S ≫ Φ₁₂) (hN : E ≫ S₁ = S₁' ≫ Q)
    (hT : Q ≫ Φ₁ = c ≫ Φ₁₂) (hK : x ≫ n ≫ S₁' ≫ c = S) :
    x ≫ M ≫ L₁ = L := by
  rw [hM, hL₁, hL, ← hK]
  simp only [Category.assoc]
  rw [reassoc_of% hN, hT]

/-- **The maps attached to a horizontally pasted square compose.** If `φ₁₂` is the composite of
`f_1^{-1}φ₂` and `φ₁` read through the comparison along `f₁₂ = f₁ ≫ f₂`, then the map of the
pasted square at `φ₁₂` is the composite of the maps of the two halves. -/
theorem smallEtalePullbackAbSquareMap_hcomp {X'₀ X'₁ X'₂ X₀ X₁ X₂ : Scheme.{u}}
    (f'₁ : X'₀ ⟶ X'₁) (f'₂ : X'₁ ⟶ X'₂) (f'₁₂ : X'₀ ⟶ X'₂) (h' : f'₁₂ = f'₁ ≫ f'₂)
    (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₁₂ : X₀ ⟶ X₂) (h : f₁₂ = f₁ ≫ f₂)
    (e₀ : X'₀ ⟶ X₀) (e₁ : X'₁ ⟶ X₁) (e₂ : X'₂ ⟶ X₂)
    (P₁ : X'₀ ⟶ X₁) (hP₁ : P₁ = f'₁ ≫ e₁) (hP₁' : P₁ = e₀ ≫ f₁)
    (P₂ : X'₁ ⟶ X₂) (hP₂ : P₂ = f'₂ ≫ e₂) (hP₂' : P₂ = e₁ ≫ f₂)
    (P : X'₀ ⟶ X₂) (hP : P = f'₁₂ ≫ e₂) (hP' : P = e₀ ≫ f₁₂)
    (A₂ : Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) (A₁ : Sheaf (smallEtaleTopology X₁) Ab.{u + 1})
    (A₀ : Sheaf (smallEtaleTopology X₀) Ab.{u + 1})
    (φ₂ : (smallEtalePullbackAb f₂).obj A₂ ⟶ A₁) (φ₁ : (smallEtalePullbackAb f₁).obj A₁ ⟶ A₀)
    (φ₁₂ : (smallEtalePullbackAb f₁₂).obj A₂ ⟶ A₀)
    (hφ : (smallEtalePullbackAb f₁).map φ₂ ≫ φ₁ =
      (smallEtalePullbackAbComp' f₁ f₂ f₁₂ h).hom.app A₂ ≫ φ₁₂) :
    (smallEtalePullbackAbComp' f'₁ f'₂ f'₁₂ h').inv.app ((smallEtalePullbackAb e₂).obj A₂) ≫
        (smallEtalePullbackAb f'₁).map
          (smallEtalePullbackAbSquareMap f'₂ e₁ e₂ f₂ P₂ hP₂ hP₂' A₂ A₁ φ₂) ≫
        smallEtalePullbackAbSquareMap f'₁ e₀ e₁ f₁ P₁ hP₁ hP₁' A₁ A₀ φ₁ =
      smallEtalePullbackAbSquareMap f'₁₂ e₀ e₂ f₁₂ P hP hP' A₂ A₀ φ₁₂ := by
  exact squareMap_hcomp_algebra (Functor.map_comp _ _ _)
    (smallEtalePullbackAbSquareMap_eq _ _ _ _ _ _ _ _ _ _)
    (smallEtalePullbackAbSquareMap_eq _ _ _ _ _ _ _ _ _ _)
    ((smallEtalePullbackAbSquareIso f'₁ e₀ e₁ f₁ P₁ hP₁ hP₁').hom.naturality φ₂)
    (((smallEtalePullbackAb e₀).map_comp _ _).symm.trans
      ((congrArg _ hφ).trans ((smallEtalePullbackAb e₀).map_comp _ _)))
    (smallEtalePullbackAbSquareIso_hcomp f'₁ f'₂ f'₁₂ h' f₁ f₂ f₁₂ h e₀ e₁ e₂ P₁ hP₁ hP₁' P₂ hP₂
      hP₂' P hP hP' A₂)

/-! ### Colimit presentations along a left adjoint -/

/-- **A left adjoint carries a colimit presentation to a colimit presentation**, in the
universal-property form of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`: if the `ι_i`
present `N` as the colimit of a diagram with maps `d`, and the objects `M'_i` with maps `d'` are
identified with the `L(M_i)` compatibly with the diagram maps, then the
`M'_i ≅ L(M_i) ⟶ L(N)` present `L(N)`. -/
theorem existsUnique_desc_of_leftAdjoint {C C' : Type*} [Category* C] [Category* C']
    {L : C ⥤ C'} {R : C' ⥤ C} (adj : L ⊣ R) {J : Type*} [Category* J] {M : J → C}
    {M' : J → C'} {N : C} (ι : ∀ i, M i ⟶ N) (d : ∀ ⦃i j : J⦄, (i ⟶ j) → (M j ⟶ M i))
    (d' : ∀ ⦃i j : J⦄, (i ⟶ j) → (M' j ⟶ M' i)) (κ : ∀ i, M' i ≅ L.obj (M i))
    (hκ : ∀ ⦃i j : J⦄ (a : i ⟶ j), d' a ≫ (κ i).hom = (κ j).hom ≫ L.map (d a))
    (hN : ∀ (Z : C) (τ : ∀ i, M i ⟶ Z), (∀ ⦃i j : J⦄ (a : i ⟶ j), d a ≫ τ i = τ j) →
      ∃! χ : N ⟶ Z, ∀ i, ι i ≫ χ = τ i)
    (ι' : ∀ i, M' i ⟶ L.obj N) (hι' : ∀ i, ι' i = (κ i).hom ≫ L.map (ι i))
    (Z' : C') (τ' : ∀ i, M' i ⟶ Z') (hτ' : ∀ ⦃i j : J⦄ (a : i ⟶ j), d' a ≫ τ' i = τ' j) :
    ∃! χ : L.obj N ⟶ Z', ∀ i, ι' i ≫ χ = τ' i := by
  let τ : ∀ i, M i ⟶ R.obj Z' := fun i => adj.homEquiv _ _ ((κ i).inv ≫ τ' i)
  have hτ : ∀ ⦃i j : J⦄ (a : i ⟶ j), d a ≫ τ i = τ j := by
    intro i j a
    apply (adj.homEquiv _ _).symm.injective
    have hd : L.map (d a) = (κ j).inv ≫ d' a ≫ (κ i).hom := by
      rw [hκ a, Iso.inv_hom_id_assoc]
    rw [Adjunction.homEquiv_naturality_left_symm]
    simp only [τ, Equiv.symm_apply_apply]
    rw [hd, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hτ' a]
  obtain ⟨χ, hχ, hχu⟩ := hN _ τ hτ
  refine ⟨(adj.homEquiv _ _).symm χ, fun i => ?_, fun y hy => ?_⟩
  · rw [hι', Category.assoc, ← Adjunction.homEquiv_naturality_left_symm, hχ i,
      Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  · refine (Equiv.symm_apply_apply (adj.homEquiv _ _) y).symm.trans
      (congrArg _ (hχu _ fun i => ?_))
    rw [← Adjunction.homEquiv_naturality_left]
    change _ = adj.homEquiv _ _ ((κ i).inv ≫ τ' i)
    rw [← hy i, hι', Category.assoc, Iso.inv_hom_id_assoc]

/-- The rearrangement behind `smallEtalePullbackAbSquareIso_hcomp_map`, in an abstract
category. -/
theorem squareIso_hcomp_map_algebra {C : Type*} [Category* C]
    {o₀ o₁ o₂ o₃ o₄ o₅ o₆ : C} {x : o₀ ⟶ o₁} {M : o₁ ⟶ o₃} {n : o₁ ⟶ o₂}
    {E : o₂ ⟶ o₃} {S₁ : o₃ ⟶ o₄} {S₁' : o₂ ⟶ o₅} {Q : o₅ ⟶ o₄} {c : o₅ ⟶ o₆}
    {c' : o₆ ⟶ o₅} {S : o₀ ⟶ o₆} {D : o₆ ⟶ o₄}
    (hM : M = n ≫ E) (hN : E ≫ S₁ = S₁' ≫ Q) (hD : D = c' ≫ Q) (hK : x ≫ n ≫ S₁' ≫ c = S)
    (hcc : c ≫ c' ≫ Q = Q) :
    (x ≫ M) ≫ S₁ = S ≫ D := by
  rw [hM, hD, ← hK]
  simp only [Category.assoc]
  rw [hN, hcc]

/-- The comparisons of the squares of a horizontally pasted square commute with the maps of the
two halves. -/
theorem smallEtalePullbackAbSquareIso_hcomp_map {X'₀ X'₁ X'₂ X₀ X₁ X₂ : Scheme.{u}}
    (f'₁ : X'₀ ⟶ X'₁) (f'₂ : X'₁ ⟶ X'₂) (f'₁₂ : X'₀ ⟶ X'₂) (h' : f'₁₂ = f'₁ ≫ f'₂)
    (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₁₂ : X₀ ⟶ X₂) (h : f₁₂ = f₁ ≫ f₂)
    (e₀ : X'₀ ⟶ X₀) (e₁ : X'₁ ⟶ X₁) (e₂ : X'₂ ⟶ X₂)
    (P₁ : X'₀ ⟶ X₁) (hP₁ : P₁ = f'₁ ≫ e₁) (hP₁' : P₁ = e₀ ≫ f₁)
    (P₂ : X'₁ ⟶ X₂) (hP₂ : P₂ = f'₂ ≫ e₂) (hP₂' : P₂ = e₁ ≫ f₂)
    (P : X'₀ ⟶ X₂) (hP : P = f'₁₂ ≫ e₂) (hP' : P = e₀ ≫ f₁₂)
    (A₂ : Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) (A₁ : Sheaf (smallEtaleTopology X₁) Ab.{u + 1})
    (φ₂ : (smallEtalePullbackAb f₂).obj A₂ ⟶ A₁) :
    ((smallEtalePullbackAbComp' f'₁ f'₂ f'₁₂ h').inv.app ((smallEtalePullbackAb e₂).obj A₂) ≫
        (smallEtalePullbackAb f'₁).map
          (smallEtalePullbackAbSquareMap f'₂ e₁ e₂ f₂ P₂ hP₂ hP₂' A₂ A₁ φ₂)) ≫
        ((smallEtalePullbackAbSquareIso f'₁ e₀ e₁ f₁ P₁ hP₁ hP₁').app A₁).hom =
      ((smallEtalePullbackAbSquareIso f'₁₂ e₀ e₂ f₁₂ P hP hP').app A₂).hom ≫
        (smallEtalePullbackAb e₀).map ((smallEtalePullbackAbComp' f₁ f₂ f₁₂ h).inv.app A₂ ≫
          (smallEtalePullbackAb f₁).map φ₂) := by
  exact squareIso_hcomp_map_algebra (Functor.map_comp _ _ _)
    ((smallEtalePullbackAbSquareIso f'₁ e₀ e₁ f₁ P₁ hP₁ hP₁').hom.naturality φ₂)
    ((smallEtalePullbackAb e₀).map_comp _ _)
    (smallEtalePullbackAbSquareIso_hcomp f'₁ f'₂ f'₁₂ h' f₁ f₂ f₁₂ h e₀ e₁ e₂ P₁ hP₁ hP₁' P₂ hP₂
      hP₂' P hP hP' A₂)
    (((smallEtalePullbackAb e₀).mapIso
      ((smallEtalePullbackAbComp' f₁ f₂ f₁₂ h).app A₂)).hom_inv_id_assoc
      ((smallEtalePullbackAb e₀).map ((smallEtalePullbackAb f₁).map φ₂)))

/-- `Stacks.EtaleCohomology.smallEtalePullbackAbSquareMap`, with the comparison written as the
component of the isomorphism at the sheaf. -/
theorem smallEtalePullbackAbSquareMap_eq_app {X' X Y' Y : Scheme.{u}} (f' : X' ⟶ Y')
    (e' : X' ⟶ X) (e : Y' ⟶ Y) (f : X ⟶ Y) (P : X' ⟶ Y) (h₁ : P = f' ≫ e) (h₂ : P = e' ≫ f)
    (A : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (B : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (φ : (smallEtalePullbackAb f).obj A ⟶ B) :
    smallEtalePullbackAbSquareMap f' e' e f P h₁ h₂ A B φ =
      ((smallEtalePullbackAbSquareIso f' e' e f P h₁ h₂).app A).hom ≫
        (smallEtalePullbackAb e').map φ :=
  rfl

namespace LimitBaseChange

/-! ### The system of inverse images -/

section System

variable {I : Type v} [Preorder I] {D D' : Iᵒᵖ ⥤ Scheme.{u}} (e : D' ⟶ D)

/-- The cocycle condition of a system of sheaves, with the comparison written as
`Stacks.EtaleCohomology.smallEtalePullbackAbComp'` and moved to the other side. -/
theorem systemMap_comp_eq {D : Iᵒᵖ ⥤ Scheme.{u}} (F : EtaleSheafSystem D Ab.{u + 1})
    {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (smallEtalePullbackAb (D.map a)).map (F.map b) ≫ F.map a =
      (smallEtalePullbackAbComp' (D.map a) (D.map b) (D.map (a ≫ b))
          (D.map_comp a b)).hom.app (F.obj k) ≫ F.map (a ≫ b) := by
  rw [← systemPullbackComp_eq, ← F.map_comp a b, Iso.hom_inv_id_app_assoc]

/-- **The inverse image of a system along `e`**: the sheaves `e_i^{-1}ℱ_i` on the levels of `D'`.
The transition map at `a : i ⟶ j` is the comparison of the inverse images along the two sides of
the naturality square `D'(a) ≫ e_j = e_i ≫ D(a)`, followed by `e_i^{-1}` of the transition map of
`ℱ`; the cocycle condition is the pasting of the naturality squares at `a` and `b`. -/
def inverseImageSystem (F : EtaleSheafSystem D Ab.{u + 1}) : EtaleSheafSystem D' Ab.{u + 1} where
  obj i := (smallEtalePullbackAb (e.app i)).obj (F.obj i)
  map {i j} a := smallEtalePullbackAbSquareMap (D'.map a) (e.app i) (e.app j) (D.map a)
    (D'.map a ≫ e.app j) rfl (e.naturality a) (F.obj j) (F.obj i) (F.map a)
  map_comp {i j k} a b := by
    rw [systemPullbackComp_eq]
    exact smallEtalePullbackAbSquareMap_hcomp (D'.map a) (D'.map b) (D'.map (a ≫ b))
      (D'.map_comp a b) (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) (e.app i)
      (e.app j) (e.app k) _ rfl (e.naturality a) _ rfl (e.naturality b) _ rfl
      (e.naturality (a ≫ b)) (F.obj k) (F.obj j) (F.obj i) (F.map b) (F.map a) (F.map (a ≫ b))
      (systemMap_comp_eq F a b)

/-- The sheaf of the inverse image of a system at level `i` is `e_i^{-1}ℱ_i`. -/
theorem inverseImageSystem_obj (F : EtaleSheafSystem D Ab.{u + 1}) (i : Iᵒᵖ) :
    (inverseImageSystem e F).obj i = (smallEtalePullbackAb (e.app i)).obj (F.obj i) :=
  rfl

/-- The transition map of the inverse image of a system at `a : i ⟶ j` is
`Stacks.EtaleCohomology.smallEtalePullbackAbSquareMap` of the naturality square at `a` and the
transition map `F.map a`. -/
theorem inverseImageSystem_map (F : EtaleSheafSystem D Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (inverseImageSystem e F).map a =
      smallEtalePullbackAbSquareMap (D'.map a) (e.app i) (e.app j) (D.map a)
        (D'.map a ≫ e.app j) rfl (e.naturality a) (F.obj j) (F.obj i) (F.map a) :=
  rfl

/-- The transition maps of the inverse image of a system, as the comparison of the naturality
square followed by the inverse image of the transition map of the system. -/
theorem inverseImageSystem_map_eq (F : EtaleSheafSystem D Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (inverseImageSystem e F).map a =
      ((smallEtalePullbackAbSquareIso (D'.map a) (e.app i) (e.app j) (D.map a)
          (D'.map a ≫ e.app j) rfl (e.naturality a)).app (F.obj j)).hom ≫
        (smallEtalePullbackAb (e.app i)).map (F.map a) :=
  smallEtalePullbackAbSquareMap_eq_app _ _ _ _ _ _ _ _ _ _

/-! ### The presentation on the limit -/

variable {c' : Cone D'} {c : Cone D} (eL : c'.pt ⟶ c.pt)
  (he : ∀ i : Iᵒᵖ, eL ≫ c.π.app i = c'.π.app i ≫ e.app i)

/-- **The legs of the inverse image of a presented system**: the comparison
`f'_i^{-1}e_i^{-1}ℱ_i ≅ e_∞^{-1}f_i^{-1}ℱ_i` of the square `f'_i ≫ e_i = e_∞ ≫ f_i`, followed by
the inverse image along `e_∞` of the leg `f_i^{-1}ℱ_i ⟶ ℱ`. -/
def inverseImageSystemLeg (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (F : EtaleSheafSystem D Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    (smallEtalePullbackAb (c'.π.app i)).obj ((inverseImageSystem e F).obj i) ⟶
      (smallEtalePullbackAb eL).obj 𝓕 :=
  smallEtalePullbackAbSquareMap (X' := c'.pt) (c'.π.app i) eL (e.app i) (c.π.app i)
    (c'.π.app i ≫ e.app i) rfl (he i).symm (F.obj i) 𝓕 (ι i)

/-- The compatibility of a family out of the inverse images of a system with its transitions,
written as `Stacks.EtaleCohomology.smallEtalePullbackAbComp'` and moved to the other side. -/
theorem legCompatible_eq {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}
    {𝒢 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}} (F : EtaleSheafSystem D Ab.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝒢) {i j : Iᵒᵖ}
    (a : i ⟶ j)
    (hτ : (conePullbackComp c a).inv.app (F.obj j) ≫
      (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ τ i = τ j) :
    (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ τ i =
      (smallEtalePullbackAbComp' (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm).hom.app
        (F.obj j) ≫ τ j := by
  rw [← hτ, ← conePullbackComp_eq, Iso.hom_inv_id_app_assoc]

/-- **The legs of the inverse image of a presented system are compatible** with the transitions
of the inverse image of the system, if the legs of the presentation are compatible with those of
the system: the pasting of the square of the legs at `i` with the naturality square at `a`. -/
theorem inverseImageSystemLeg_compatible (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (F : EtaleSheafSystem D Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    {i j : Iᵒᵖ} (a : i ⟶ j)
    (hι : (conePullbackComp c a).inv.app (F.obj j) ≫
      (smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j) :
    (conePullbackComp c' a).inv.app ((inverseImageSystem e F).obj j) ≫
        (smallEtalePullbackAb (c'.π.app i)).map ((inverseImageSystem e F).map a) ≫
          inverseImageSystemLeg e eL he 𝓕 F ι i =
      inverseImageSystemLeg e eL he 𝓕 F ι j := by
  rw [conePullbackComp_eq]
  exact smallEtalePullbackAbSquareMap_hcomp (X'₀ := c'.pt) (c'.π.app i) (D'.map a) (c'.π.app j)
    (c'.w a).symm (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm eL (e.app i) (e.app j) _ rfl
    (he i).symm _
    rfl (e.naturality a) _ rfl (he j).symm (F.obj j) (F.obj i) 𝓕 (F.map a) (ι i) (ι j)
    (legCompatible_eq F ι a hι)

/-- The comparisons of the squares of the legs commute with the diagram maps of the two systems:
the pasting of the square of the legs at `i` with the naturality square at `a`, at the identity. -/
theorem inverseImageSystemLeg_comparison_comm (F : EtaleSheafSystem D Ab.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    ((conePullbackComp c' a).inv.app ((inverseImageSystem e F).obj j) ≫
        (smallEtalePullbackAb (c'.π.app i)).map ((inverseImageSystem e F).map a)) ≫
      ((smallEtalePullbackAbSquareIso (X' := c'.pt) (c'.π.app i) eL (e.app i) (c.π.app i)
        (c'.π.app i ≫ e.app i) rfl (he i).symm).app (F.obj i)).hom =
    ((smallEtalePullbackAbSquareIso (X' := c'.pt) (c'.π.app j) eL (e.app j) (c.π.app j)
        (c'.π.app j ≫ e.app j) rfl (he j).symm).app (F.obj j)).hom ≫
      (smallEtalePullbackAb eL).map ((conePullbackComp c a).inv.app (F.obj j) ≫
        (smallEtalePullbackAb (c.π.app i)).map (F.map a)) := by
  rw [conePullbackComp_eq, conePullbackComp_eq]
  exact smallEtalePullbackAbSquareIso_hcomp_map (X'₀ := c'.pt) (c'.π.app i) (D'.map a) (c'.π.app j)
    (c'.w a).symm (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm eL (e.app i) (e.app j) _ rfl
    (he i).symm _ rfl (e.naturality a) _ rfl (he j).symm (F.obj j) (F.obj i) (F.map a)

/-- The legs of the inverse image of a presented system, as the comparison of the square of the
legs followed by the inverse image of the leg of the presentation. -/
theorem inverseImageSystemLeg_eq (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (F : EtaleSheafSystem D Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕) (i : Iᵒᵖ) :
    inverseImageSystemLeg e eL he 𝓕 F ι i =
      @CategoryStruct.comp (Sheaf (smallEtaleTopology c'.pt) Ab.{u + 1}) _
        ((smallEtalePullbackAb (c'.π.app i)).obj ((inverseImageSystem e F).obj i))
        ((smallEtalePullbackAb eL).obj ((smallEtalePullbackAb (c.π.app i)).obj (F.obj i)))
        ((smallEtalePullbackAb eL).obj 𝓕)
        ((smallEtalePullbackAbSquareIso (X' := c'.pt) (c'.π.app i) eL (e.app i) (c.π.app i)
          (c'.π.app i ≫ e.app i) rfl (he i).symm).app (F.obj i)).hom
        ((smallEtalePullbackAb eL).map (ι i)) :=
  smallEtalePullbackAbSquareMap_eq_app _ _ _ _ _ _ _ _ _ _

/-- **The inverse image of a colimit presentation is a colimit presentation** of the inverse image
of the system. Inverse image is a left adjoint: a compatible family of maps out of the
`f'_i^{-1}e_i^{-1}ℱ_i` is, through the comparisons of the squares of the legs and the adjunction,
a compatible family of maps out of the `f_i^{-1}ℱ_i`. -/
theorem isPullbackColimitPresentation_inverseImageSystem
    (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) (F : EtaleSheafSystem D Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι) :
    LimitHigherDirectImage.IsPullbackColimitPresentation c' ((smallEtalePullbackAb eL).obj 𝓕)
      (inverseImageSystem e F) (inverseImageSystemLeg e eL he 𝓕 F ι) := by
  intro 𝒢 τ' hτ'
  exact existsUnique_desc_of_leftAdjoint (C := Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (C' := Sheaf (smallEtaleTopology c'.pt) Ab.{u + 1}) (L := smallEtalePullbackAb eL)
    (R := smallEtalePushforwardAb eL) (J := Iᵒᵖ)
    (M := fun i => (smallEtalePullbackAb (c.π.app i)).obj (F.obj i))
    (M' := fun i => (smallEtalePullbackAb (c'.π.app i)).obj ((inverseImageSystem e F).obj i))
    (N := 𝓕) (smallEtaleAdjunctionAb eL) ι
    (fun i j a => (conePullbackComp c a).inv.app (F.obj j) ≫
      (smallEtalePullbackAb (c.π.app i)).map (F.map a))
    (fun i j a => (conePullbackComp c' a).inv.app ((inverseImageSystem e F).obj j) ≫
      (smallEtalePullbackAb (c'.π.app i)).map ((inverseImageSystem e F).map a))
    (fun i => (smallEtalePullbackAbSquareIso (X' := c'.pt) (c'.π.app i) eL (e.app i) (c.π.app i)
      (c'.π.app i ≫ e.app i) rfl (he i).symm).app (F.obj i))
    (fun i j a => inverseImageSystemLeg_comparison_comm e eL he F a)
    (fun Z τ hτ => hpres Z τ fun a => (Category.assoc _ _ _).symm.trans (hτ a))
    (inverseImageSystemLeg e eL he 𝓕 F ι)
    (fun i => inverseImageSystemLeg_eq e eL he 𝓕 F ι i) 𝒢 τ'
    (fun i j a => (Category.assoc _ _ _).trans (hτ' a))

end System

end LimitBaseChange

end Stacks.EtaleCohomology

end
