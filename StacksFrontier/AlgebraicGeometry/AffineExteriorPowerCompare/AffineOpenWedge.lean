module

public import StacksFrontier.AlgebraicGeometry.AffineExteriorPowerCompare.AffineOpen
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorComparison
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge

/-!
# The exterior-power comparison on an affine open, on wedges and products

`Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso` identifies, for an exterior algebra `E`
of a quasi-coherent module `F` on a scheme `X` and an affine open `U`,

`Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)`.

**This file evaluates that identification.** It carries the ordered product in `E` of the
degree-one generators at sections `s₁, …, sₙ` of `F` over `U` to the wedge `s₁ ∧ ⋯ ∧ sₙ`, and it
carries the product of `E` to the wedge product of exterior powers. Together these say that the
comparison is the canonical one, and that it is an isomorphism of graded algebras.

## Main results

* `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_inv_ιMulti`: **the comparison on a
  wedge**: its inverse carries `s₁ ∧ ⋯ ∧ sₙ` to the ordered product of the degree-one generators
  at the `sᵢ`; `affineOpenExteriorPowerΓIso_hom_homogeneousProd` is the same equation read
  forwards, and `affineOpenExteriorPowerΓIso_hom_one` its degree-zero case.
* `Stacks.AffineExteriorPower.affineOpenExteriorPowerΓIso_hom_mul`: **the comparison is
  multiplicative**: it carries the product of `E` to `exteriorPower.wedgeMul`.

## Implementation notes

The comparison is a composite of four steps, and the equation on a wedge is carried through each
of them in turn.

1. `Stacks.AffineExteriorPower.pullbackFromSpecΓIso_inv_apply`: the comparison of sections is the
   pullback of a section along `Spec Γ(X, U) ⟶ X`, by
   `AlgebraicGeometry.restrictFunctorIsoPullback_hom_app_pullbackSection`.
2. `Stacks.PullbackExteriorAlgebra.comparisonHom_homogeneousProd`: the comparison of Tag 01CI
   carries the pullback of an ordered product of generators to the ordered product of the
   generators at the pulled-back sections; it is multiplicative and matches the generators
   (`Stacks.PullbackExteriorAlgebra.comparisonHom_mul`, `comparisonHom_generator`).
3. `Stacks.AffineExteriorPower.quasicoherentExteriorPowerΓIso_inv_ιMulti`: Tag 01I8 on `Spec R`
   on a wedge, from `Stacks.AffineExteriorPower.exteriorPowerΓIso_inv_ιMulti` through the
   factorisation `quasicoherentExteriorPowerΓIso_inv_eq`.
4. The exterior power of the comparison of sections, which is `exteriorPower.map`.

Multiplicativity then follows because the wedges span the exterior powers: both sides are
bilinear, and on two wedges they agree by `Stacks.GradedAlgebra.mul_homogeneousProd` and
`exteriorPower.wedgeMul_ιMulti`. The degree of the product is `(p : ℤ) + q`, which is
definitionally `((p + q : ℕ) : ℤ)`; the statement carries the transport as an `eqToHom`, the
spelling of `AlgebraicGeometry.Scheme.Hom.absoluteFormsAction_tmul`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.PullbackExteriorAlgebra

open RingedSpaceModuleAdjunction Stacks.RingedSpace SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))
  {M : SheafOfModules.{u} (structureRingSheaf Y)} {ι : M ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj M ⟶ B.piece 1}
  (hA : IsExteriorAlgebra A ι) (hκ : SquareZero κ)

/-- The comparison morphism `f^*(A_n) ⟶ B_n` carries the pullback of an ordered product of
degree-one generators to the ordered product of the degree-one generators of `B` at the pulled
back sections. -/
theorem comparisonHom_homogeneousProd (U : (Opens Y.carrier)ᵒᵖ) (n : ℕ)
    (s : Fin n → M.val.obj U) :
    (comparisonHom f A hA hκ n).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece n) U
          (A.toPresheafGradedAlgebra.homogeneousProd U n fun i => ι.val.app U (s i))) =
      B.toPresheafGradedAlgebra.homogeneousProd ((opensMap f).op.obj U) n
        fun i => κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U (s i)) := by
  induction n with
  | zero => exact comparisonHom_one f A hA hκ U
  | succ n ih =>
    refine (comparisonHom_mul f A hA hκ (n : ℤ) 1 U _ _).trans ?_
    rw [ih fun i => s i.castSucc, comparisonHom_generator]
    rfl

end Stacks.PullbackExteriorAlgebra

namespace Stacks.AffineExteriorPower

open SheafOfModules.GradedAlgebra (IsExteriorAlgebra UnitalHom)
open Stacks.AlgebraicGeometry.AffineBaseChangeLocality (tildeΓIso)

section Quasicoherent

variable {R : CommRingCat.{u}} (F : (Spec R).Modules) [F.IsQuasicoherent]

/-- **The quasi-coherent comparison on a wedge of global sections.** The inverse of
`Γ(Spec R, ⋀ⁿ F) ≅ ⋀ⁿ_R Γ(Spec R, F)` carries `t₁ ∧ ⋯ ∧ tₙ` to the ordered product of the
degree-one generators at the `tᵢ`. -/
theorem quasicoherentExteriorPowerΓIso_inv_ιMulti
    {E : SheafOfModules.GradedAlgebra.{u} (Spec R).ringCatSheaf} {gen : F ⟶ E.piece 1}
    (hE : E.IsExteriorAlgebra gen) (n : ℕ) (t : Fin n → ↥(moduleSpecΓFunctor.obj F)) :
    (quasicoherentExteriorPowerΓIso F hE n).inv.hom (exteriorPower.ιMulti ↥R n t) =
      E.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n
        (fun i => gen.val.app (specGlobalOpen R) (t i)) := by
  rw [quasicoherentExteriorPowerΓIso_inv_eq, ModuleCat.hom_comp, LinearMap.comp_apply,
    exteriorPowerΓIso_inv_ιMulti]
  refine (UnitalHom.app_homogeneousProd
    ((specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.isUniversal.desc
      E ((tildeΓIso F).hom ≫ gen) (isExteriorAlgebra_tildeΓ hE).1) (specGlobalOpen R) n _).trans ?_
  refine congrArg (E.toPresheafGradedAlgebra.homogeneousProd (specGlobalOpen R) n)
    (funext fun i => ?_)
  have h := congrArg (fun k : (tilde (moduleSpecΓFunctor.obj F) : (Spec R).Modules) ⟶ E.piece 1 =>
      k.val.app (specGlobalOpen R) ((tilde.toOpen (moduleSpecΓFunctor.obj F) ⊤).hom (t i)))
    (SheafOfModules.GradedAlgebra.IsUniversal.desc_extends
      (specTildeAlgebras R (moduleSpecΓFunctor.obj F)).exterior_isExteriorAlgebra.isUniversal
      E ((tildeΓIso F).hom ≫ gen) (isExteriorAlgebra_tildeΓ hE).1)
  refine h.trans ?_
  exact congrArg (gen.val.app (specGlobalOpen R)) (TildeTensor.toOpen_fromTildeΓ_app_top F (t i))

end Quasicoherent

section AffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (F : X.Modules) (hU : IsAffineOpen U)

/-- The inverse of the comparison of sections of `Stacks.AffineExteriorPower.pullbackFromSpecΓIso`
is the pullback of a section along `Spec Γ(X, U) ⟶ X`. -/
theorem pullbackFromSpecΓIso_inv_apply
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) (s : Γ(F, U)) :
    (pullbackFromSpecΓIso F hU).inv.hom s =
      Scheme.Modules.pullbackSection hU.fromSpec F U ⊤ h s := by
  change ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).hom.app F).val.app (op ⊤)
    ((Stacks.Modules.restrictFromSpecSectionsEquiv F hU).symm s) = _
  rw [restrictFunctorIsoPullback_hom_app_pullbackSection F hU h]
  congr 1
  rw [affineSectionsLinearEquiv_eq_map F hU (Stacks.Modules.image_top_fromSpec hU)]
  exact (Stacks.Modules.restrictFromSpecSectionsEquiv F hU).apply_symm_apply s

variable {E : SheafOfModules.GradedAlgebra.{u, u}
    (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace)} {gen : F ⟶ E.piece 1}
  (hE : IsExteriorAlgebra E gen)

/-- Tag 01CI on an affine open, on the pullback of an ordered product of degree-one generators:
it is the ordered product of the degree-one generators of the exterior algebra of the inverse
image at the pulled-back sections. -/
theorem exteriorPowerFromSpecIso_hom_pullbackSection (n : ℕ)
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) (s : Fin n → Γ(F, U)) :
    (exteriorPowerFromSpecIso F hU hE (n : ℤ)).hom.val.app (op ⊤)
        (Scheme.Modules.pullbackSection hU.fromSpec (pieceModules E (n : ℤ)) U ⊤ h
          (E.toPresheafGradedAlgebra.homogeneousProd (op U) n
            fun i => gen.val.app (op U) (s i))) =
      (Scheme.Modules.exteriorAlgebra
          ((Scheme.Modules.pullback hU.fromSpec).obj F)).toPresheafGradedAlgebra.homogeneousProd
        (op ⊤) n fun i => (Scheme.Modules.exteriorGenerator
          ((Scheme.Modules.pullback hU.fromSpec).obj F)).val.app (op ⊤)
            (Scheme.Modules.pullbackSection hU.fromSpec F U ⊤ h (s i)) := by
  refine (PresheafOfModules.naturality_apply (exteriorPowerFromSpecIso F hU hE (n : ℤ)).hom.val
    (homOfLE h).op _).trans ?_
  refine (congrArg _ (Stacks.PullbackExteriorAlgebra.comparisonHom_homogeneousProd
    hU.fromSpec.toLRSHom.toShHom E hE _ (op U) n s)).trans ?_
  refine ((Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback hU.fromSpec).obj
    F)).toPresheafGradedAlgebra.homogeneousProd_naturality (homOfLE h).op n _).trans ?_
  refine congrArg ((Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback hU.fromSpec).obj
    F)).toPresheafGradedAlgebra.homogeneousProd (op ⊤) n) (funext fun i => ?_)
  exact (PresheafOfModules.naturality_apply (Scheme.Modules.exteriorGenerator
    ((Scheme.Modules.pullback hU.fromSpec).obj F)).val (homOfLE h).op _).symm

variable [F.IsQuasicoherent]

/-- **The comparison `Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)` on an ordered product of degree-one
generators**: it is the wedge of the sections. -/
theorem affineOpenExteriorPowerΓIso_hom_homogeneousProd (n : ℕ) (s : Fin n → Γ(F, U)) :
    (affineOpenExteriorPowerΓIso F hU hE n).hom.hom
        (E.toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i => gen.val.app (op U) (s i)) =
      exteriorPower.ιMulti Γ(X, U) n s := by
  have h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h12 := (congrArg ((exteriorPowerFromSpecIso F hU hE (n : ℤ)).hom.val.app (op ⊤))
    (pullbackFromSpecΓIso_inv_apply (pieceModules E (n : ℤ)) hU h
      (E.toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i => gen.val.app (op U) (s i)))).trans
    (exteriorPowerFromSpecIso_hom_pullbackSection F hU hE n h s)
  have h3 := quasicoherentExteriorPowerΓIso_inv_ιMulti ((Scheme.Modules.pullback hU.fromSpec).obj F)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n
    (fun i => Scheme.Modules.pullbackSection hU.fromSpec F U ⊤ h (s i))
  refine (congrArg (fun y => exteriorPowerCongr (pullbackFromSpecΓIso F hU).toLinearEquiv n
    ((quasicoherentExteriorPowerΓIso ((Scheme.Modules.pullback hU.fromSpec).obj F)
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n).hom.hom y))
    (h12.trans h3.symm)).trans ?_
  refine (congrArg (exteriorPowerCongr (pullbackFromSpecΓIso F hU).toLinearEquiv n)
    (congrArg (fun k => ModuleCat.Hom.hom k _)
      (quasicoherentExteriorPowerΓIso ((Scheme.Modules.pullback hU.fromSpec).obj F)
        (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _) n).inv_hom_id)).trans ?_
  refine (exteriorPower.map_apply_ιMulti _ _).trans
    (congrArg (exteriorPower.ιMulti Γ(X, U) n) (funext fun i => ?_))
  refine (congrArg (pullbackFromSpecΓIso F hU).hom.hom
    (pullbackFromSpecΓIso_inv_apply F hU h (s i)).symm).trans ?_
  exact congrArg (fun k => ModuleCat.Hom.hom k (s i)) (pullbackFromSpecΓIso F hU).inv_hom_id

/-- **The comparison `Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)` on a wedge**: its inverse carries
`s₁ ∧ ⋯ ∧ sₙ` to the ordered product, in `E`, of the degree-one generators at the `sᵢ`. -/
theorem affineOpenExteriorPowerΓIso_inv_ιMulti (n : ℕ) (s : Fin n → Γ(F, U)) :
    (affineOpenExteriorPowerΓIso F hU hE n).inv.hom (exteriorPower.ιMulti Γ(X, U) n s) =
      E.toPresheafGradedAlgebra.homogeneousProd (op U) n
        fun i => gen.val.app (op U) (s i) := by
  rw [← affineOpenExteriorPowerΓIso_hom_homogeneousProd F hU hE n s]
  exact congrArg (fun k => ModuleCat.Hom.hom k _)
    (affineOpenExteriorPowerΓIso F hU hE n).hom_inv_id

/-- The comparison in degree zero carries the unit section of `E` to the empty wedge. -/
theorem affineOpenExteriorPowerΓIso_hom_one :
    (affineOpenExteriorPowerΓIso F hU hE 0).hom.hom (E.one.eval (op U)) =
      exteriorPower.ιMulti Γ(X, U) 0 Fin.elim0 :=
  affineOpenExteriorPowerΓIso_hom_homogeneousProd F hU hE 0 Fin.elim0

/-- The product of `E` on sections over `U`, as a `Γ(X, U)`-bilinear map. -/
def pieceSectionsMul (p q : ℕ) :
    Γ(pieceModules E (p : ℤ), U) →ₗ[Γ(X, U)] Γ(pieceModules E (q : ℤ), U) →ₗ[Γ(X, U)]
      Γ(pieceModules E ((p + q : ℕ) : ℤ), U) :=
  LinearMap.mk₂ Γ(X, U) (fun x y => (E.mul p q).app (op U) x y)
    (fun x x' y => (congrArg (fun k => k y) (map_add ((E.mul p q).app (op U)) x x')).trans
      (AddMonoidHom.add_apply _ _ y))
    (fun c x y => by exact (E.mul p q).map_smul_left (op U) c x y)
    (fun x y y' => map_add (((E.mul p q).app (op U)) x) y y')
    (fun c x y => by exact (E.mul p q).map_smul_right (op U) c x y)

/-- **The comparison `Γ(⋀ⁿ F, U) ≅ ⋀ⁿ_{Γ(X, U)} Γ(F, U)` is multiplicative**: it carries the
product of `E` to the wedge product. -/
theorem affineOpenExteriorPowerΓIso_hom_mul (p q : ℕ) (α : Γ(pieceModules E (p : ℤ), U))
    (β : Γ(pieceModules E (q : ℤ), U)) :
    (affineOpenExteriorPowerΓIso F hU hE (p + q)).hom.hom
        ((eqToHom (congrArg (pieceModules E) (Nat.cast_add p q).symm)).val.app (op U)
          ((E.mul p q).app (op U) α β)) =
      exteriorPower.wedgeMul p q ((affineOpenExteriorPowerΓIso F hU hE p).hom.hom α)
        ((affineOpenExteriorPowerΓIso F hU hE q).hom.hom β) := by
  have key : ((pieceSectionsMul (E := E) (U := U) p q).compl₁₂
      (affineOpenExteriorPowerΓIso F hU hE p).inv.hom
      (affineOpenExteriorPowerΓIso F hU hE q).inv.hom).compr₂
        (affineOpenExteriorPowerΓIso F hU hE (p + q)).hom.hom =
      exteriorPower.wedgeMul p q := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun u =>
      exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_))
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, exteriorPower.wedgeMul_ιMulti]
    rw [affineOpenExteriorPowerΓIso_inv_ιMulti, affineOpenExteriorPowerΓIso_inv_ιMulti]
    have hfin : Fin.append (fun i => gen.val.app (op U) (u i))
        (fun i => gen.val.app (op U) (v i)) = fun i => gen.val.app (op U) (Fin.append u v i) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact congrArg (gen.val.app (op U)) (Fin.append_left u v j).symm
      · rw [Fin.append_right]
        exact congrArg (gen.val.app (op U)) (Fin.append_right u v j).symm
    refine (congrArg (affineOpenExteriorPowerΓIso F hU hE (p + q)).hom.hom
      ((E.toPresheafGradedAlgebra.mul_homogeneousProd (op U) p q _ _).trans
        (congrArg (E.toPresheafGradedAlgebra.homogeneousProd (op U) (p + q)) hfin))).trans ?_
    exact affineOpenExteriorPowerΓIso_hom_homogeneousProd F hU hE (p + q) (Fin.append u v)
  have h := LinearMap.congr_fun₂ key ((affineOpenExteriorPowerΓIso F hU hE p).hom.hom α)
    ((affineOpenExteriorPowerΓIso F hU hE q).hom.hom β)
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply] at h
  refine Eq.trans ?_ h
  refine congrArg (affineOpenExteriorPowerΓIso F hU hE (p + q)).hom.hom ?_
  rw [eqToHom_refl]
  exact congrArg₂ (fun x y => pieceSectionsMul (E := E) (U := U) p q x y)
    (congrArg (fun k => ModuleCat.Hom.hom k α)
      (affineOpenExteriorPowerΓIso F hU hE p).hom_inv_id).symm
    (congrArg (fun k => ModuleCat.Hom.hom k β)
      (affineOpenExteriorPowerΓIso F hU hE q).hom_inv_id).symm

end AffineOpen

end Stacks.AffineExteriorPower

end
