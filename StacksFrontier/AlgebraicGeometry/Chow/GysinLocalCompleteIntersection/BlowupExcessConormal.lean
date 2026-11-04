module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BaseChangeConormal
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreExceptionalSmooth
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSequence
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassOpenFactor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The excess conormal sheaf of the blow up formula

Let `i : Z ⟶ X` be a regular closed immersion, `b : X' ⟶ X` the blowing up of `X` with centre
`Z`, and `E = X' ×_X Z` the exceptional divisor, with `j : E ⟶ X'` and `π : E ⟶ Z`. The sheaf
`𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})` of Stacks 0FVA is the excess conormal sheaf of any
factorization `X' ⟶ P ⟶ X` of `b` through a smooth `P`, the kernel of `j^*𝒞_{X'/P} ⟶ 𝒞_{E/P'}`
with `P' = P ×_X Z` (`Stacks.Chow.SmoothFactorization.baseChangeExcessConormal`). Both are the
intersection of the two subsheaves `j^*𝒞_{X'/P}` and `π^*𝒞_{Z/X}` of `𝒞_{E/P}` cut out by the
two short exact conormal sequences of Stacks 063N

```
0 ⟶ j^*𝒞_{X'/P} ⟶ 𝒞_{E/P} ⟶ 𝒞_{E/X'} ⟶ 0        (E ⟶ X' ⟶ P, E ⟶ X' an effective Cartier divisor)
0 ⟶ (E ⟶ P')^*𝒞_{P'/P} ⟶ 𝒞_{E/P} ⟶ 𝒞_{E/P'} ⟶ 0  (E ⟶ P' ⟶ P, E ⟶ P' Koszul-regular)
```

with `𝒞_{P'/P}` the pullback of `𝒞_{Z/X}` by flat base change (Stacks 0473).

## Main definitions

* `Stacks.Chow.kernelCompIsoKernelComp`: for two short exact sequences `A ⟶ M ⟶ Q₁` and
  `B ⟶ M ⟶ Q₂` with the same middle term, `Ker(A ⟶ Q₂) ≅ Ker(B ⟶ Q₁)`; both are `A ∩ B`.
* `Stacks.Chow.baseChangeExcessConormalIsoKernel`: the excess conormal sheaf of a factorization
  along a closed immersion `i` is the kernel of `π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}`.
* `Stacks.Chow.blowupExcessConormal`: the sheaf `𝓕` of Stacks 0FVA.
* `Stacks.Chow.baseChangeExcessConormalIsoBlowupExcessConormal`: the excess conormal sheaf of a
  factorization of the blowing up is `𝓕`.

## Main results

* `Stacks.Chow.isFiniteLocallyFree_blowupExcessConormal`: `𝓕` is finite locally free when the
  Gysin map exists for `b`.

## References

* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 063N](https://stacks.math.columbia.edu/tag/063N)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### Two subobjects of one object -/

section Abstract

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] {A B M Q₁ Q₂ : 𝒞}
  (a : A ⟶ M) (q₁ : M ⟶ Q₁) (b : B ⟶ M) (q₂ : M ⟶ Q₂) (w₁ : a ≫ q₁ = 0) (w₂ : b ≫ q₂ = 0)
  (h₁ : (ShortComplex.mk a q₁ w₁).Exact) (h₂ : (ShortComplex.mk b q₂ w₂).Exact) [Mono a] [Mono b]

/-- The map `Ker(A ⟶ Q₂) ⟶ B` through which `Ker(A ⟶ Q₂) ⟶ A ⟶ M` factors. -/
noncomputable def kernelCompLift : kernel (a ≫ q₂) ⟶ B :=
  h₂.lift (kernel.ι (a ≫ q₂) ≫ a) (by rw [Category.assoc]; exact kernel.condition _)

omit [Mono a] in
/-- The composite `Ker(A ⟶ Q₂) ⟶ B ⟶ M` equals `Ker(A ⟶ Q₂) ⟶ A ⟶ M`. -/
@[reassoc]
theorem kernelCompLift_comp : kernelCompLift a b q₂ w₂ h₂ ≫ b = kernel.ι (a ≫ q₂) ≫ a :=
  h₂.lift_f _ _

/-- **Two subobjects with the same ambient object meet in one kernel.** For short exact
sequences `A ⟶ M ⟶ Q₁` and `B ⟶ M ⟶ Q₂` with the same middle term, the kernels of
`A ⟶ M ⟶ Q₂` and `B ⟶ M ⟶ Q₁` are isomorphic: both are the intersection `A ∩ B` in `M`. -/
noncomputable def kernelCompIsoKernelComp : kernel (a ≫ q₂) ≅ kernel (b ≫ q₁) where
  hom := kernel.lift (b ≫ q₁) (kernelCompLift a b q₂ w₂ h₂) (by
    rw [← Category.assoc, kernelCompLift_comp, Category.assoc, w₁, comp_zero])
  inv := kernel.lift (a ≫ q₂) (kernelCompLift b a q₁ w₁ h₁) (by
    rw [← Category.assoc, kernelCompLift_comp, Category.assoc, w₂, comp_zero])
  hom_inv_id := by
    rw [← cancel_mono (kernel.ι (a ≫ q₂) ≫ a)]
    simp [kernelCompLift_comp]
  inv_hom_id := by
    rw [← cancel_mono (kernel.ι (b ≫ q₁) ≫ b)]
    simp [kernelCompLift_comp]

/-- The isomorphism `Ker(A ⟶ Q₂) ≅ Ker(B ⟶ Q₁)` is compatible with the two inclusions into `M`. -/
theorem kernelCompIsoKernelComp_hom_ι :
    (kernelCompIsoKernelComp a q₁ b q₂ w₁ w₂ h₁ h₂).hom ≫ kernel.ι (b ≫ q₁) ≫ b =
      kernel.ι (a ≫ q₂) ≫ a := by
  rw [kernelCompIsoKernelComp, ← Category.assoc, kernel.lift_ι, kernelCompLift_comp]

end Abstract

/-! ### Conormal maps: transports and the two conormal sequences through a common middle term -/

section ConormalMaps

open Stacks.Immersion

/-- The conormal map of a square changes by a transport when the morphisms of the square are
replaced by equal ones. -/
theorem immersionConormalSheafMap_eq_eqToHom_comp {Z Z' W W' : Scheme.{u}} (i : Z ⟶ Z')
    (k : W ⟶ W') [IsImmersion i] [IsImmersion k] {f f' : Z ⟶ W} {g g' : Z' ⟶ W'}
    (hf : f = f') (hg : g = g')
    (c : i.toLRSHom.toShHom ≫ g.toLRSHom.toShHom = f.toLRSHom.toShHom ≫ k.toLRSHom.toShHom)
    (c' : i.toLRSHom.toShHom ≫ g'.toLRSHom.toShHom = f'.toLRSHom.toShHom ≫ k.toLRSHom.toShHom) :
    immersionConormalSheafMap i k f g c =
      eqToHom (by rw [hf]) ≫ immersionConormalSheafMap i k f' g' c' := by
  subst hf hg
  simp

/-- **The conormal sequence of `Z ⟶ Y ⟶ X`, read with any morphism `k` equal to the composite as
middle term**, is short exact when `Z ⟶ Y` is `H₁`-regular (Stacks 063N). -/
@[sga "6 VII 1.7" "more general"]
theorem shortExact_conormalSequence_of_eq {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (k : Z ⟶ X) [IsImmersion k] (e : i ≫ j = k)
    (hi : IsH1RegularImmersion i)
    (w : immersionConormalSheafMap k j i (𝟙 X) (toShHom_square (by rw [Category.comp_id, e])) ≫
      (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv.app _ ≫
        immersionConormalSheafMap i k (𝟙 Z) j (toShHom_square (by rw [Category.id_comp, e])) = 0) :
    (ShortComplex.mk _ _ w).ShortExact := by
  subst e
  exact conormalSequence_shortExact i j hi

/-- The conormal sequence of `Z ⟶ Y ⟶ X`, read with a morphism `k` equal to the composite, is a
complex (Stacks 062S). -/
theorem conormalSequence_comp_zero_of_eq {Z Y X : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (k : Z ⟶ X) [IsImmersion k] (e : i ≫ j = k) :
    immersionConormalSheafMap k j i (𝟙 X) (toShHom_square (by rw [Category.comp_id, e])) ≫
      (modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).inv.app _ ≫
        immersionConormalSheafMap i k (𝟙 Z) j (toShHom_square (by rw [Category.id_comp, e])) =
      0 := by
  subst e
  exact conormalSequence_comp_zero i j

/-- A conormal map of a square whose top edge is an identity, after a conormal map, is the
conormal map of the pasted square. -/
theorem immersionConormalSheafMap_comp_id {Z₁ Z₂ X₁ X₂ X₃ : Scheme.{u}} (i₁ : Z₁ ⟶ X₁)
    (i₂ : Z₁ ⟶ X₂) (i₃ : Z₂ ⟶ X₃) [IsImmersion i₁] [IsImmersion i₂] [IsImmersion i₃]
    (g₁ : X₁ ⟶ X₂) (comm₁ : i₁ ≫ g₁ = 𝟙 Z₁ ≫ i₂) (f₂ : Z₁ ⟶ Z₂) (g₂ : X₂ ⟶ X₃)
    (comm₂ : i₂ ≫ g₂ = f₂ ≫ i₃) :
    immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂) ≫
        (modulePullbackId Z₁.toLocallyRingedSpace.toRingedSpace).inv.app _ ≫
          immersionConormalSheafMap i₁ i₂ (𝟙 Z₁) g₁ (toShHom_square comm₁) =
      immersionConormalSheafMap i₁ i₃ f₂ (g₁ ≫ g₂) (toShHom_square (square_comp comm₁ comm₂)) := by
  have hc := immersionConormalSheafMap_comp i₁ i₂ i₃ (𝟙 Z₁) g₁ comm₁ f₂ g₂ comm₂
  have hic : (modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 Z₁)).toShHom f₂.toLRSHom.toShHom).hom.app
      (Stacks.ClosedImmersion.conormalSheaf i₃.liftCoborder.toLRSHom.toShHom) =
      (modulePullbackId Z₁.toLocallyRingedSpace.toRingedSpace).inv.app _ :=
    (Iso.hom_eq_inv ((modulePullbackComp (Scheme.Hom.toLRSHom (𝟙 Z₁)).toShHom
      f₂.toLRSHom.toShHom).app _)
      ((modulePullbackId Z₁.toLocallyRingedSpace.toRingedSpace).app _)).2
      (modulePullbackComp_id_inv_app f₂.toLRSHom.toShHom _).symm
  rw [hic] at hc
  refine Eq.trans ?_ hc.symm
  have hn := (modulePullbackId Z₁.toLocallyRingedSpace.toRingedSpace).inv.naturality
    (immersionConormalSheafMap i₂ i₃ f₂ g₂ (toShHom_square comm₂))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans (Category.assoc _ _ _))

/-- `Stacks.Chow.immersionConormalSheafMap_comp_id` when the second square has an identity as its
bottom edge. -/
theorem immersionConormalSheafMap_comp_id_id {Z₁ Z₂ X₁ X₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X₁)
    (i₂ : Z₁ ⟶ X₂) (i₃ : Z₂ ⟶ X₂) [IsImmersion i₁] [IsImmersion i₂] [IsImmersion i₃]
    (g₁ : X₁ ⟶ X₂) (comm₁ : i₁ ≫ g₁ = 𝟙 Z₁ ≫ i₂) (f₂ : Z₁ ⟶ Z₂)
    (comm₂ : i₂ ≫ 𝟙 X₂ = f₂ ≫ i₃) (comm : i₁ ≫ g₁ = f₂ ≫ i₃) :
    immersionConormalSheafMap i₂ i₃ f₂ (𝟙 X₂) (toShHom_square comm₂) ≫
        (modulePullbackId Z₁.toLocallyRingedSpace.toRingedSpace).inv.app _ ≫
          immersionConormalSheafMap i₁ i₂ (𝟙 Z₁) g₁ (toShHom_square comm₁) =
      immersionConormalSheafMap i₁ i₃ f₂ g₁ (toShHom_square comm) := by
  rw [immersionConormalSheafMap_comp_id i₁ i₂ i₃ g₁ comm₁ f₂ (𝟙 X₂) comm₂,
    immersionConormalSheafMap_eq_eqToHom_comp i₁ i₃ (rfl : f₂ = f₂) (Category.comp_id g₁) _
      (toShHom_square comm), eqToHom_refl, Category.id_comp]

/-- **The excess conormal sheaf of a factorization, read on the target of the base change.**
Let `j ≫ f = π ≫ i` be a cartesian square with `i : Z ⟶ X` a closed immersion, `j : E ⟶ X'` an
`H₁`-regular immersion and `π : E ⟶ Z` a local complete intersection morphism, and let
`X' ⟶ P ⟶ X` be a factorization of `f` through a smooth `P`. Then the excess conormal sheaf of
the factorization along `i`, the kernel of `j^*𝒞_{X'/P} ⟶ 𝒞_{E/P'}` with `P' = P ×_X Z`, is the
kernel of the canonical map `π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}`: both are the intersection of
`j^*𝒞_{X'/P}` and `π^*𝒞_{Z/X}` inside `𝒞_{E/P}`. -/
noncomputable def baseChangeExcessConormalIsoKernel {E X' Z X : Scheme.{u}} {j : E ⟶ X'}
    {π : E ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X} [IsClosedImmersion i] [IsImmersion j]
    (hsq : IsPullback j π f i) (hj : IsH1RegularImmersion j)
    (hπ : IsLocalCompleteIntersectionMorphism π) (Fb : SmoothFactorization f) :
    Fb.baseChangeExcessConormal hsq ≅
      kernel (immersionConormalSheafMap j i π f (toShHom_square hsq.w)) := by
  haveI := Fb.isImmersion
  haveI := Fb.isSmooth
  haveI : IsImmersion (Fb.baseChangeImm hsq.w) := Fb.isImmersion_baseChangeImm hsq
  have hi'p : Fb.baseChangeImm hsq.w ≫ pullback.fst Fb.proj i = j ≫ Fb.imm :=
    Fb.baseChangeImm_fst hsq.w
  have hi'h : Fb.baseChangeImm hsq.w ≫ pullback.snd Fb.proj i = π := Fb.baseChangeImm_snd hsq.w
  have hi' : IsH1RegularImmersion (Fb.baseChangeImm hsq.w) :=
    isH1RegularImmersion_of_isKoszulRegularImmersion _
      (Fb.isKoszulRegularImmersion_baseChange hsq hπ)
  have w₁ := conormalSequence_comp_zero_of_eq j Fb.imm (j ≫ Fb.imm) rfl
  have w₂ := conormalSequence_comp_zero_of_eq (Fb.baseChangeImm hsq.w) (pullback.fst Fb.proj i)
    (j ≫ Fb.imm) hi'p
  have ses₁ := shortExact_conormalSequence_of_eq j Fb.imm (j ≫ Fb.imm) rfl hj w₁
  have ses₂ := shortExact_conormalSequence_of_eq _ _ (j ≫ Fb.imm) hi'p hi' w₂
  haveI : Mono (immersionConormalSheafMap (j ≫ Fb.imm) Fb.imm j (𝟙 _)
      (toShHom_square (by rw [Category.comp_id]))) := ses₁.mono_f
  haveI : Mono (immersionConormalSheafMap (j ≫ Fb.imm) (pullback.fst Fb.proj i)
      (Fb.baseChangeImm hsq.w) (𝟙 _) (toShHom_square (by rw [Category.comp_id, hi'p]))) :=
    ses₂.mono_f
  have e₁ := immersionConormalSheafMap_comp_id_id (Fb.baseChangeImm hsq.w) (j ≫ Fb.imm) Fb.imm
    (pullback.fst Fb.proj i) (by rw [Category.id_comp, hi'p]) j (by rw [Category.comp_id])
    (Fb.isPullback_baseChange hsq).flip.w
  have e₂ := immersionConormalSheafMap_comp_id_id j (j ≫ Fb.imm) (pullback.fst Fb.proj i) Fb.imm
    (by rw [Category.id_comp]) (Fb.baseChangeImm hsq.w) (by rw [Category.comp_id, hi'p])
    hi'p.symm
  have e₃ := immersionConormalSheafMap_comp j (pullback.fst Fb.proj i) i
    (Fb.baseChangeImm hsq.w) Fb.imm hi'p.symm (pullback.snd Fb.proj i) Fb.proj pullback.condition
  have e₄ := immersionConormalSheafMap_eq_eqToHom_comp j i hi'h.symm Fb.imm_proj.symm
    (toShHom_square hsq.w) (toShHom_square (square_comp hi'p.symm pullback.condition))
  haveI := isIso_immersionConormalSheafMap_of_flat (pullback.fst Fb.proj i) i
    (pullback.snd Fb.proj i) Fb.proj (IsPullback.of_hasPullback Fb.proj i)
  refine kernelIsoOfEq e₁.symm ≪≫ @kernelCompIsoKernelComp _ _ _ _ _ _ _ _ _ _ _ _ w₁ w₂
      ses₁.exact ses₂.exact ses₁.mono_f ses₂.mono_f ≪≫ kernelIsoOfEq e₂ ≪≫
    (kernelIsIsoComp ((modulePullbackComp (Fb.baseChangeImm hsq.w).toLRSHom.toShHom
        (pullback.snd Fb.proj i).toLRSHom.toShHom).hom.app _ ≫
      (modulePullback (Fb.baseChangeImm hsq.w).toLRSHom.toShHom).map
        (immersionConormalSheafMap (pullback.fst Fb.proj i) i (pullback.snd Fb.proj i) Fb.proj
          (toShHom_square pullback.condition))) _).symm ≪≫
    (kernelIsIsoComp (eqToHom (congrArg (fun t : E ⟶ Z => (modulePullback t.toLRSHom.toShHom).obj
      (Stacks.ClosedImmersion.conormalSheaf i.liftCoborder.toLRSHom.toShHom)) hi'h.symm)) _).symm ≪≫
    kernelIsoOfEq ?_
  rw [e₄, e₃]
  simp only [Category.assoc]
  congr 1

end ConormalMaps

/-! ### The sheaf `𝓕` of the blow up formula -/

section Blowup

open Stacks.Immersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The sheaf `𝓕` of Stacks 0FVA**: for the blowing up `b : X' ⟶ X` along a closed immersion
`i : Z ⟶ X`, with exceptional divisor `E = X' ×_X Z`, `j : E ⟶ X'` and `π : E ⟶ Z`, the kernel of
the canonical map `π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}` (Stacks 01R4). -/
noncomputable def blowupExcessConormal : (pullback (Stacks.Blowup.blowUpToBase i.ker) i).Modules :=
  kernel (immersionConormalSheafMap (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i) i
    (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) (Stacks.Blowup.blowUpToBase i.ker)
    (toShHom_square pullback.condition))

/-- The projection `E = X' ×_X Z ⟶ Z` of the exceptional divisor of the blowing up along a
regular closed immersion is a local complete intersection morphism, being smooth. -/
theorem isLocalCompleteIntersectionMorphism_pullbackSnd_blowUpToBase (hi : IsRegularImmersion i) :
    IsLocalCompleteIntersectionMorphism (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) := by
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  have h := isLocalCompleteIntersectionMorphism_comp_of_smooth
    (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) (𝟙 Z)
    (isLocalCompleteIntersectionMorphism_of_isOpenImmersion (𝟙 Z))
  rwa [Category.comp_id] at h

/-- **The excess conormal sheaf of a factorization of the blowing up is `𝓕`.** Let `i : Z ⟶ X`
be a regular closed immersion and `X' ⟶ P ⟶ X` a factorization of the blowing up `b : X' ⟶ X`
along `Z` through a smooth `P`. Its excess conormal sheaf along `i`, the kernel of
`j^*𝒞_{X'/P} ⟶ 𝒞_{E/P'}` with `P' = P ×_X Z` (the sheaf `𝒞` of Stacks 0FV9, by its clause 1), is
the sheaf `𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})` of Stacks 0FVA. -/
noncomputable def baseChangeExcessConormalIsoBlowupExcessConormal (hi : IsRegularImmersion i)
    (Fb : SmoothFactorization (Stacks.Blowup.blowUpToBase i.ker)) :
    Fb.baseChangeExcessConormal (IsPullback.of_hasPullback (Stacks.Blowup.blowUpToBase i.ker) i) ≅
      blowupExcessConormal i :=
  baseChangeExcessConormalIsoKernel (IsPullback.of_hasPullback _ i)
    (isH1RegularImmersion_of_isKoszulRegularImmersion _
      (isKoszulRegularImmersion_of_isRegularImmersion _
        (Stacks.Blowup.isRegularImmersion_pullbackFst_blowUpToBase i)))
    (isLocalCompleteIntersectionMorphism_pullbackSnd_blowUpToBase i hi) Fb

/-- **The sheaf `𝓕` of Stacks 0FVA is finite locally free** when the Gysin map exists for the
blowing up `b` along a regular closed immersion into a locally Noetherian scheme. -/
theorem isFiniteLocallyFree_blowupExcessConormal [IsLocallyNoetherian X] (hi : IsRegularImmersion i)
    (hG : GysinMapExists (Stacks.Blowup.blowUpToBase i.ker)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (blowupExcessConormal i) := by
  obtain ⟨Fb⟩ := (gysinMapExists_iff_nonempty _).1 hG
  have := Fb.isFiniteLocallyFree_baseChangeExcessConormal
    (IsPullback.of_hasPullback (Stacks.Blowup.blowUpToBase i.ker) i)
    (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi)
    (isLocalCompleteIntersectionMorphism_pullbackSnd_blowUpToBase i hi)
  exact SheafOfModules.IsFiniteLocallyFree.of_iso
    (baseChangeExcessConormalIsoBlowupExcessConormal i hi Fb)

end Blowup

end Stacks.Chow

end
