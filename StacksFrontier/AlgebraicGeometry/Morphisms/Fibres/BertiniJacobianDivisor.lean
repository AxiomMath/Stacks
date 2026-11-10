module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFlatOpenJacobian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.ZeroSchemeStalkRegular
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Jacobian criterion in the Bertini situation, and [Stacks, Tag 0FD6]

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) with `X` smooth and
of finite type over an algebraically closed field `k`, and write `q : H_univ → 𝔸^r_k` for the
universal family. Everything in the proof of [Stacks, Tag 0FD6] except the Jacobian criterion
itself is discharged in the modules this one imports; what is left is
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor`, the assertion that for a closed point `w` of
`q⁻¹(W)` over a closed point `x` of `X`, at which some linear form `∑ᵢ Mᵢⱼxᵢ` of the evaluation
matrix does not vanish, the divisor of the residue coordinates of `q(w)` is smooth over
`κ(q(w))` at the point `z` of it that `w` comes from. This module proves that, and reads off the
tag.

The proof is the source's. The residue field at `q(w)` is the base field: `w` is a closed point
of a scheme of finite type over `k` and `k → κ(q(w)) → κ(w)` composes to a bijection, so
`κ(q(w)) ≅ k`. Hence the coordinate tuple of `q(w)` comes from a tuple `c` of `k`, and the base
change `X_{κ(q(w))} → X` along which the divisor is taken is an isomorphism — so the divisor is
the zero scheme `Z(∑ᵢ cᵢψ(vᵢ))` on `X` itself, read through that isomorphism. Non-vanishing of
a form of `M` at `w` says `∑ᵢ Mᵢⱼcᵢ ≠ 0`, that is, by the defining property of the evaluation
matrix, that `ev_x` does not kill `c`: the germ of `∑ᵢ cᵢψ(vᵢ)` at `x` avoids `𝔪_x²ℒ_x`. Since
`X` is smooth over `k`, `𝒪_{X,x}` is regular, so
`AlgebraicGeometry.isRegularLocalRing_stalk_zeroScheme_of_notMem_maximalSqSmul` makes the local
ring of the divisor at `z` regular — and that is smoothness over `κ(q(w))`, a perfect field.

## Main results

* `Stacks.Bertini.FamilyDivisors.surjective_algebraMap_residueFieldParameterBase` and
  `Stacks.Bertini.FamilyDivisors.perfectField_residueFieldParameterBase`: the residue field at
  the image of a closed point of `q⁻¹(W)` is the base field, hence perfect.
* `Stacks.Bertini.FamilyDivisors.coeffMap_ne_zero_of_mem_basicOpen`: non-vanishing of a form of
  the evaluation matrix at a point of `𝔸^r_X` is non-vanishing of `M` on the coordinate tuple of
  its image, read in the base field.
* `Stacks.Bertini.FamilyDivisors.notMem_maximalSqSmul_constCoeffSection`: the germ ↔ evaluation
  bridge — `ev_x(c) ≠ 0` exactly when the germ of `∑ᵢ cᵢψ(vᵢ)` at `x` avoids `𝔪_x²ℒ_x`.
* `AlgebraicGeometry.isRegularLocalRing_stalk_subscheme_of_eq_comap_zeroScheme`: the Jacobian
  criterion transported along an isomorphism of ambient schemes.
* `Stacks.Bertini.FamilyDivisors.jacobianAtDivisor`: **the Jacobian criterion in the Bertini
  situation**, `Stacks.Bertini.FamilyDivisors.JacobianAtDivisor` for the standing basis of the
  linear system.
* `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates`:
  **[Stacks, Tag 0FD6]** from hypotheses (1), (2) and (3) of the tag, with no input assumed, and
  `…forGeneral_smooth_specializedDivisor_of_generates_of_basis`: the same with hypothesis (3) at
  an arbitrary basis of the linear system rather than at the standing one.
* `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise`:
  **the same with no dimension data assumed either.** The dimension count is run at each closed
  point `x` of `X` with the local dimension of `X` at `x`, which exists because the local ring
  of a smooth scheme at a closed point is regular; so the equidimensionality of `X`, the bound
  `dim X ≤ n` and the inequality `n + 1 ≤ dim V` that the previous statement assumes are all
  discharged, the last one off the surjectivity of `ev_x` as in the source.
* `…forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_basis`:
  **the same with hypothesis (3) at an arbitrary basis of the linear system**, as the source
  states it. The only hypothesis left that the source does not make is that `k` is algebraically
  closed.

## Implementation notes

`JacobianAtDivisor` is stated at a basis `b` of the linear system indexed by `Fin (m + 1)`,
while the coordinates of the parameter space are those of the standing basis `D.basis`. The two
are compared only by the index bijection `Stacks.Bertini.FamilyDivisors.basisIndexEquiv`, not by
a change of basis, so the coordinate tuple of a point of `𝔸^r_k` is a tuple of coefficients
against `D.basis` while the kernel condition on the matrix `M` is one on coefficients against
`b`. The two agree exactly when `b` is `D.basis` read through that bijection, which is the
hypothesis `hb0` of `Stacks.Bertini.FamilyDivisors.jacobianAtDivisor`; it is satisfied by
`D.basis.reindex (finCongr hm)`, which is the basis the tag is read off at. At an unrelated
basis the two kernel conditions differ by a change of basis, and the criterion as spelled is
then not the Jacobian criterion.

So the criterion stays at the standing basis — but hypothesis (3) need not, and the chain
through `Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis` keeps the two as separate
parameters. That is what lets
`FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_basis` take
hypothesis (3) at an arbitrary basis while instantiating the criterion at
`D.basis.reindex (finCongr …)` all the same.

The divisor is spelled `(D.universalDivisor.comap (D.fibreParameterMap …)).subscheme`, the
spelling of the cartesian square; `Stacks.Bertini.FamilyDivisors.specializedDivisor_eq_comap`
turns it into a zero scheme, and
`AlgebraicGeometry.isRegularLocalRing_stalk_subscheme_of_eq_comap_zeroScheme` takes that
equality of ideal sheaves as a hypothesis, so that no term of the subscheme has to be
transported along it.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ImmersionEvaluationSurjective

universe u

namespace AlgebraicGeometry

/-- **The stalk of a closed subscheme which is the inverse image along an isomorphism of the
zero scheme of a section of an invertible module is a regular local ring**, at a point over
which the section does not vanish to second order. -/
theorem isRegularLocalRing_stalk_subscheme_of_eq_comap_zeroScheme
    {X X' : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (t : Γ(L, ⊤)) (f : X' ⟶ X) [IsIso f] {I : X'.IdealSheafData}
    (hI : I = (zeroScheme X L t).comap f) (z : I.subscheme)
    (hreg : ∀ y : X, IsRegularLocalRing (X.presheaf.stalk y))
    (ht : (L.presheaf.Γgerm (f.base (I.subschemeι.base z))).hom t ∉
      Stacks.ImmersionEvaluationSurjective.maximalSqSmul L
        (f.base (I.subschemeι.base z))) :
    IsRegularLocalRing (I.subscheme.presheaf.stalk z) := by
  obtain ⟨s, hs⟩ : ∃ s : L.sections, s.eval (op ⊤) = t :=
    ⟨Stacks.SheafOfModules.sectionsOfTopOfRingSheaf L t,
      Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top L t⟩
  subst hs
  set Z := zeroScheme X L (s.eval (op ⊤))
  subst hI
  have : IsIso (CategoryTheory.Limits.pullback.snd f Z.subschemeι) :=
    (CategoryTheory.IsPullback.of_hasPullback f Z.subschemeι).isIso_snd_of_isIso
  let e : (Z.comap f).subscheme ≅ Z.subscheme :=
    Z.comapIso f ≪≫ asIso (CategoryTheory.Limits.pullback.snd f Z.subschemeι)
  have hcomp : e.hom ≫ Z.subschemeι = (Z.comap f).subschemeι ≫ f := by
    change ((Z.comapIso f).hom ≫ CategoryTheory.Limits.pullback.snd f Z.subschemeι) ≫ _ = _
    rw [Scheme.IdealSheafData.comapIso_hom_snd,
      Scheme.IdealSheafData.subschemeMap_subschemeι]
  have hpt : Z.subschemeι.base (e.hom.base z) = f.base ((Z.comap f).subschemeι.base z) := by
    rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
  have := hreg (Z.subschemeι.base (e.hom.base z))
  have : IsRegularLocalRing (Z.subscheme.presheaf.stalk (e.hom.base z)) :=
    isRegularLocalRing_stalk_zeroScheme_of_notMem_maximalSqSmul L s (e.hom.base z)
      (by rw [hpt]; exact ht)
  have hfin := isRegularLocalRing_stalk_of_iso e.symm (e.hom.base z)
  have hz : e.symm.hom.base (e.hom.base z) = z := by
    rw [Iso.symm_hom, ← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  rwa [hz] at hfin

end AlgebraicGeometry

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u}) (W : D.parameterBase.Opens)

/-- **The structure morphism of `q⁻¹(W)` factors the one of the parameter space.** -/
theorem appTop_universalDivisorToBaseOver (t : Γ(Spec (.of D.k), ⊤)) :
    (D.universalFamilyMapOver W).appTop
        ((𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)).appTop t) =
      (D.universalDivisorToBaseOver W).appTop t := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    D.universalFamilyMapOver_comp_over W]

/-- The residue field map at `x` carries the value at `f x` of the pullback of `t` along `g` to
the value at `x` of its pullback along `h`, whenever `f ≫ g = h`. -/
private theorem residueFieldMap_Γevaluation_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hfg : f ≫ g = h) (x : X) (t : Γ(Z, ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f.base x) (g.appTop t)) = X.Γevaluation x (h.appTop t) := by
  rw [Scheme.Γevaluation_naturality_apply, ← hfg, Scheme.Hom.comp_appTop]
  rfl

/-- **The residue field at the image of a closed point of `q⁻¹(W)` is the base field.** -/
theorem surjective_algebraMap_residueFieldParameterBase [IsAlgClosed D.k]
    [LocallyOfFiniteType D.toBase]
    (w : (D.universalDivisorSchemeOver W).toScheme)
    (hw : IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme)) :
    Function.Surjective (algebraMap D.k
      ↥(D.parameterBase.residueField ((D.universalFamilyMapOver W).base w))) := by
  let : Algebra D.k ↥((D.universalDivisorSchemeOver W).toScheme.residueField w) :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (D.universalDivisorToBaseOver W).appTop ≫
      (D.universalDivisorSchemeOver W).toScheme.Γevaluation w).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap D.k
      ↥((D.universalDivisorSchemeOver W).toScheme.residueField w)) :=
    AlgebraicGeometry.bijective_algebraMap_residueField_of_isClosed
      (D.universalDivisorToBaseOver W) w hw
  have hcomp : ∀ c : D.k,
      ((D.universalFamilyMapOver W).residueFieldMap w).hom
          (algebraMap D.k
            ↥(D.parameterBase.residueField ((D.universalFamilyMapOver W).base w)) c) =
        algebraMap D.k ↥((D.universalDivisorSchemeOver W).toScheme.residueField w) c := by
    intro c
    change (D.universalFamilyMapOver W).residueFieldMap w
        (D.parameterBase.Γevaluation ((D.universalFamilyMapOver W).base w)
          ((𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)).appTop
            ((Scheme.ΓSpecIso (.of D.k)).inv c))) = _
    exact residueFieldMap_Γevaluation_appTop _ _ _ (D.universalFamilyMapOver_comp_over W) _ _
  intro t
  obtain ⟨c, hc⟩ := hbij.2 (((D.universalFamilyMapOver W).residueFieldMap w).hom t)
  exact ⟨c, RingHom.injective ((D.universalFamilyMapOver W).residueFieldMap w).hom
    (by rw [hcomp c, hc])⟩

/-- **`κ(s)` is perfect** at the image of a closed point of `q⁻¹(W)`, being the base field. -/
theorem perfectField_residueFieldParameterBase [IsAlgClosed D.k] [LocallyOfFiniteType D.toBase]
    (w : (D.universalDivisorSchemeOver W).toScheme)
    (hw : IsClosed ({w} : Set (D.universalDivisorSchemeOver W).toScheme)) :
    PerfectField ↥(D.parameterBase.residueField ((D.universalFamilyMapOver W).base w)) :=
  PerfectField.of_ringEquiv (RingEquiv.ofBijective
    (algebraMap D.k ↥(D.parameterBase.residueField ((D.universalFamilyMapOver W).base w)))
    ⟨RingHom.injective _, D.surjective_algebraMap_residueFieldParameterBase W w hw⟩)

section Coordinates

open Stacks.LinearSubspace

variable {n : ℕ}

/-- **The value of a linear form of the matrix at a point of `𝔸^r_X`.** Read in the residue
field of the image `s` of the point in `𝔸^r_k`, it is the value of `∑ᵢ Mᵢⱼ cᵢ` where `c` is a
tuple of the base field whose image in `κ(s)` is the coordinate tuple of `s`. -/
theorem Γevaluation_evalCoordForm (M : D.basisIndex → Fin (n + 1) → D.k) (j : Fin (n + 1))
    (p : D.parameterSpace) (c : D.basisIndex → D.k)
    (hc : ∀ i : D.basisIndex,
      algebraMap D.k ↥(D.parameterBase.residueField
          ((AffineSpace.map D.basisIndex D.toBase).base p)) (c i) =
        D.residueCoord ((AffineSpace.map D.basisIndex D.toBase).base p) i.down) :
    D.parameterSpace.Γevaluation p (D.evalCoordForm M j) =
      (AffineSpace.map D.basisIndex D.toBase).residueFieldMap p
        (algebraMap D.k ↥(D.parameterBase.residueField
          ((AffineSpace.map D.basisIndex D.toBase).base p)) (coeffMap M c j)) := by
  have hconst : ∀ t : D.k,
      (AffineSpace.map D.basisIndex D.toBase).residueFieldMap p
          (algebraMap D.k ↥(D.parameterBase.residueField
            ((AffineSpace.map D.basisIndex D.toBase).base p)) t) =
        D.parameterSpace.Γevaluation p
          ((𝔸(D.basisIndex; D.X) ↘ D.X).appTop (D.constSection t)) := by
    intro t
    change (AffineSpace.map D.basisIndex D.toBase).residueFieldMap p
        (D.parameterBase.Γevaluation ((AffineSpace.map D.basisIndex D.toBase).base p)
          ((𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)).appTop
            ((Scheme.ΓSpecIso (.of D.k)).inv t))) = _
    exact residueFieldMap_Γevaluation_appTop _ _ _ (AffineSpace.map_over D.toBase) _ _
  have hcoord : ∀ i : D.basisIndex,
      (AffineSpace.map D.basisIndex D.toBase).residueFieldMap p
          (D.residueCoord ((AffineSpace.map D.basisIndex D.toBase).base p) i.down) =
        D.parameterSpace.Γevaluation p (AffineSpace.coord D.X i) := by
    intro i
    change (AffineSpace.map D.basisIndex D.toBase).residueFieldMap p
        (D.parameterBase.Γevaluation ((AffineSpace.map D.basisIndex D.toBase).base p)
          (AffineSpace.coord (Spec (.of D.k)) (ULift.up i.down))) = _
    rw [Scheme.Γevaluation_naturality_apply, AffineSpace.map_appTop_coord]
  rw [evalCoordForm, AffineSpace.coordForm, map_sum, coeffMap_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_mul, hconst, hc i, hcoord i]

/-- **Non-vanishing of a linear form of the matrix at a point of `𝔸^r_X`** says that the
coordinate tuple of its image in `𝔸^r_k`, read in the base field, is not killed by `M`. -/
theorem coeffMap_ne_zero_of_mem_basicOpen (M : D.basisIndex → Fin (n + 1) → D.k)
    (j : Fin (n + 1)) (p : D.parameterSpace) (c : D.basisIndex → D.k)
    (hc : ∀ i : D.basisIndex,
      algebraMap D.k ↥(D.parameterBase.residueField
          ((AffineSpace.map D.basisIndex D.toBase).base p)) (c i) =
        D.residueCoord ((AffineSpace.map D.basisIndex D.toBase).base p) i.down)
    (hp : p ∈ D.parameterSpace.basicOpen (D.evalCoordForm M j)) :
    coeffMap M c ≠ 0 := by
  have hne : D.parameterSpace.Γevaluation p (D.evalCoordForm M j) ≠ 0 :=
    (Scheme.evaluation_ne_zero_iff_mem_basicOpen D.parameterSpace (U := ⊤) p trivial
      (D.evalCoordForm M j)).mpr hp
  rw [D.Γevaluation_evalCoordForm M j p c hc] at hne
  intro h0
  rw [show coeffMap M c j = 0 from by rw [h0]; rfl, map_zero, map_zero] at hne
  exact hne rfl

end Coordinates

section Germ

open Stacks.LinearSubspace

/-- **The section `∑ᵢ cᵢ ψ(vᵢ)` of `L` attached to a coordinate tuple of the base field.** -/
def constCoeffSection (c : Fin (Module.finrank D.k D.V) → D.k) : Γ(D.L, ⊤) :=
  ∑ i, D.constSection (c i) • D.sectionOf (D.basis i)

/-- The germ at `x` of the constant global section `t` of the structure sheaf is the image of `t`
under `baseGerm D.toBase x`. -/
theorem germ_constSection (x : D.X) (t : D.k) :
    (D.X.presheaf.Γgerm x).hom (D.constSection t) = baseGerm D.toBase x t := rfl

/-- **The germ of `∑ᵢ cᵢ ψ(vᵢ)`** is the corresponding combination of the germs of the sections
of the standing basis. -/
theorem Γgerm_constCoeffSection (x : D.X) (c : Fin (Module.finrank D.k D.V) → D.k) :
    (D.L.presheaf.Γgerm x).hom (D.constCoeffSection c) =
      ∑ i, baseGerm D.toBase x (c i) •
        (D.L.presheaf.Γgerm x).hom (D.sectionOf (D.basis i)) := by
  rw [constCoeffSection, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Stacks.ModuleStalk.Γgerm_smul, D.germ_constSection x (c i)]

/-- **Non-vanishing of the evaluation at a coordinate tuple is non-vanishing of the germ of the
corresponding section to second order.** The basis `b` is the standing basis of the linear
system, read through the comparison of the two index sets. -/
theorem notMem_maximalSqSmul_constCoeffSection {m : ℕ}
    (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hb0 : ∀ l, b l = D.basis (D.basisIndexEquiv b l).down)
    (x : D.X) (c : D.basisIndex → D.k)
    (hne : evalCoord (fun l => D.sectionOf (b l)) D.toBase x
      (fun l => c (D.basisIndexEquiv b l)) ≠ 0) :
    (D.L.presheaf.Γgerm x).hom (D.constCoeffSection fun i => c (ULift.up i)) ∉
      maximalSqSmul D.L x := by
  intro hmem
  refine hne ?_
  have hsum : (∑ l, baseGerm D.toBase x (c (D.basisIndexEquiv b l)) •
        (D.L.presheaf.Γgerm x).hom (D.sectionOf (b l))) =
      (D.L.presheaf.Γgerm x).hom (D.constCoeffSection fun i => c (ULift.up i)) := by
    rw [D.Γgerm_constCoeffSection x]
    refine Eq.trans (Finset.sum_congr rfl fun l _ => by rw [hb0 l]) ?_
    refine Eq.trans (Equiv.sum_comp (D.basisIndexEquiv b)
      (fun i : D.basisIndex => baseGerm D.toBase x (c i) •
        (D.L.presheaf.Γgerm x).hom (D.sectionOf (D.basis i.down)))) ?_
    exact (Equiv.sum_comp (Equiv.ulift.symm : Fin (Module.finrank D.k D.V) ≃ D.basisIndex)
      (fun i : D.basisIndex => baseGerm D.toBase x (c i) •
        (D.L.presheaf.Γgerm x).hom (D.sectionOf (D.basis i.down)))).symm
  rw [evalCoord_apply]
  change Submodule.Quotient.mk (p := maximalSqSmul D.L x) _ = 0
  rw [Submodule.Quotient.mk_eq_zero, hsum]
  exact hmem

end Germ

section BaseChange

variable (K : Type u) [Field K] [Algebra D.k K]

/-- **A global function on `Spec k` pulled back to `X_{k'}` through `X` or through `Spec k'`.**
The two legs of the cartesian square presenting `X_{k'}` agree on global sections. -/
theorem appTop_baseChangeToX_comp (u : Γ(Spec (.of D.k), ⊤)) :
    (D.baseChangeToX K).appTop (D.toBase.appTop u) =
      (D.baseChangeToSpec K).appTop
        ((Spec.map (CommRingCat.ofHom (algebraMap D.k K))).appTop u) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, (D.isPullback_baseChange K).w,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- **A scalar of `k` read on `Spec k'` is its image under the structure map.** -/
theorem appTop_SpecMap_algebraMap (t : D.k) :
    (Spec.map (CommRingCat.ofHom (algebraMap D.k K))).appTop
        ((Scheme.ΓSpecIso (.of D.k)).inv t) =
      (Scheme.ΓSpecIso (.of K)).inv (algebraMap D.k K t) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

/-- **A constant function on `X` pulls back to the corresponding constant on `X_{k'}`.** -/
theorem appTop_baseChangeToX_constSection (t : D.k) :
    (D.baseChangeToX K).appTop (D.constSection t) =
      D.baseChangeScalar K (algebraMap D.k K t) := by
  rw [constSection, D.appTop_baseChangeToX_comp K ((Scheme.ΓSpecIso (.of D.k)).inv t),
    D.appTop_SpecMap_algebraMap K t]
  rfl

/-- **The section `∑ᵢ aᵢ ψ(vᵢ)` of a tuple coming from the base field is the pullback of the
corresponding section of `L` on `X`.** -/
theorem specializedSection_eq_pullbackGlobalSections
    (c : Fin (Module.finrank D.k D.V) → D.k) :
    D.specializedSection K (fun i => algebraMap D.k K (c i)) =
      pullbackGlobalSections (D.baseChangeToX K) D.L (D.constCoeffSection c) := by
  rw [specializedSection, constCoeffSection, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    D.appTop_baseChangeToX_constSection K (c i)]

/-- **The base change along a bijective extension of the base field is an isomorphism.** -/
theorem isIso_baseChangeToX (hbij : Function.Bijective (algebraMap D.k K)) :
    IsIso (D.baseChangeToX K) := by
  have : IsIso (CommRingCat.ofHom (algebraMap D.k K)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact ((D.isPullback_baseChange K).flip).isIso_snd_of_isIso

end BaseChange

/-- **Every local ring of a smooth `X` over an algebraically closed field is regular.** -/
@[ega "IV 17.5.8" "(iii), special case", sga "1 II 3.1" "special case"]
theorem isRegularLocalRing_stalk_of_smooth [IsAlgClosed D.k] [Smooth D.toBase] (y : D.X) :
    IsRegularLocalRing (D.X.presheaf.stalk y) := by
  have : LocallyOfFiniteType D.toBase := inferInstance
  let : Algebra D.k ↑(D.X.residueField y) :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ D.toBase.appTop ≫ D.X.Γevaluation y).hom.toAlgebra
  refine (smoothAt_iff_isRegularLocalRing_stalk D.toBase y
    (Algebra.isSeparableExtension_of_perfectField D.k _)).mp ?_
  refine (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus D.toBase y).mpr ?_
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

section Divisor

open Stacks.LinearSubspace

/-- **The local ring of the divisor of a coordinate tuple at a point where the corresponding
section of `L` does not vanish to second order is regular.** The coordinate tuple is that of a
point `s` of `𝔸^r_k` whose residue field is the base field, so the divisor lives on a base
change of `X` along an isomorphism and the Jacobian criterion can be read on `X` itself. -/
theorem isRegularLocalRing_stalk_residueCoordDivisor [IsAlgClosed D.k] [Smooth D.toBase]
    (s : D.parameterBase)
    (hsurj : Function.Surjective (algebraMap D.k ↥(D.parameterBase.residueField s)))
    (c : D.basisIndex → D.k)
    (hc : ∀ i : D.basisIndex,
      algebraMap D.k ↥(D.parameterBase.residueField s) (c i) = D.residueCoord s i.down)
    (z : D.residueCoordDivisor s) {x : D.X}
    (hzx : (D.baseChangeToX ↥(D.parameterBase.residueField s)).base
        ((D.universalDivisor.comap
          (D.fibreParameterMap ↥(D.parameterBase.residueField s)
            (D.residueCoord s))).subschemeι.base z) = x)
    (hgerm : (D.L.presheaf.Γgerm x).hom
      (D.constCoeffSection fun i => c (ULift.up i)) ∉ maximalSqSmul D.L x) :
    IsRegularLocalRing ((D.residueCoordDivisor s).presheaf.stalk z) := by
  have : IsIso (D.baseChangeToX ↥(D.parameterBase.residueField s)) :=
    D.isIso_baseChangeToX _ ⟨RingHom.injective _, hsurj⟩
  have ha : (fun i => algebraMap D.k ↥(D.parameterBase.residueField s)
      ((fun i' => c (ULift.up i')) i)) = D.residueCoord s :=
    funext fun i => hc (ULift.up i)
  have hI : D.universalDivisor.comap
        (D.fibreParameterMap ↥(D.parameterBase.residueField s) (D.residueCoord s)) =
      (zeroScheme D.X D.L (D.constCoeffSection fun i => c (ULift.up i))).comap
        (D.baseChangeToX ↥(D.parameterBase.residueField s)) := by
    rw [← D.specializedDivisor_eq_comap _ (D.residueCoord s),
      ← Stacks.Divisors.zeroScheme_pullback,
      ← D.specializedSection_eq_pullbackGlobalSections _ (fun i => c (ULift.up i)), ← ha]
    rfl
  refine AlgebraicGeometry.isRegularLocalRing_stalk_subscheme_of_eq_comap_zeroScheme
    D.L _ (D.baseChangeToX ↥(D.parameterBase.residueField s)) hI z
    D.isRegularLocalRing_stalk_of_smooth ?_
  rw [hzx]
  exact hgerm

/-- **The Jacobian criterion in the Bertini situation**, for a basis of the linear system which
is the standing one read through the comparison of the two index sets.

Given an open `W` of the parameter space over which `q⁻¹(W) → 𝔸^r_k` is flat, a closed point `x`
of `X`, the matrix `M` of the evaluation `ev_x`, a closed point `w` of `q⁻¹(W)` lying over `x` at
which some form `∑ᵢ Mᵢⱼxᵢ` does not vanish, and the point `z` of the divisor of the residue
coordinates of `q(w)` which `w` comes from, the divisor is smooth over `κ(q(w))` at `z`.

The residue field at `q(w)` is the base field, because `w` is a closed point of a scheme of
finite type over an algebraically closed field and `q(w)` lies under it; so the divisor is the
base change of a divisor `Z(∑ᵢ cᵢψ(vᵢ))` on `X` itself along an isomorphism. The non-vanishing
of a form of `M` at `w` says that `M` does not kill the tuple `c`, which by the defining
property of `M` says that `ev_x` does not kill it, that is, that the germ of `∑ᵢ cᵢψ(vᵢ)` at `x`
avoids `𝔪_x²ℒ_x`; and the local ring of `X` at `x` is regular because `X` is smooth over `k`.
`AlgebraicGeometry.isRegularLocalRing_stalk_zeroScheme_of_notMem_maximalSqSmul` then gives
regularity of the local ring of the divisor at `z`, which is its smoothness over the residue
field because that field is perfect. -/
theorem jacobianAtDivisor [IsAlgClosed D.k] [Smooth D.toBase] {n m : ℕ}
    (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hb0 : ∀ l, b l = D.basis (D.basisIndexEquiv b l).down) :
    D.JacobianAtDivisor (n := n) b := by
  intro W hflat x hx M hM w hw hwx hform z hz
  obtain ⟨j, hj⟩ := hform
  have : LocallyOfFiniteType D.toBase := inferInstance
  have hsurj := D.surjective_algebraMap_residueFieldParameterBase W w hw
  choose c hc using fun i : D.basisIndex =>
    hsurj (D.residueCoord ((D.universalFamilyMapOver W).base w) i.down)
  have hcoeff : coeffMap M c ≠ 0 :=
    D.coeffMap_ne_zero_of_mem_basicOpen M j
      (D.universalDivisor.subschemeι.base ((D.universalDivisorSchemeOver W).ι.base w)) c
      (fun i => hc i) hj
  have hne : evalCoord (fun l => D.sectionOf (b l)) D.toBase x
      (fun l => c (D.basisIndexEquiv b l)) ≠ 0 := fun h => hcoeff ((hM c).mpr h)
  have hgerm := D.notMem_maximalSqSmul_constCoeffSection b hb0 x c hne
  have : PerfectField ↥(D.parameterBase.residueField ((D.universalFamilyMapOver W).base w)) :=
    D.perfectField_residueFieldParameterBase W w hw
  refine (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus
    (D.residueCoordDivisorToBase ((D.universalFamilyMapOver W).base w)) z).mp ?_
  let : Algebra ↥(D.parameterBase.residueField ((D.universalFamilyMapOver W).base w))
      ↥((D.residueCoordDivisor ((D.universalFamilyMapOver W).base w)).residueField z) :=
    ((Scheme.ΓSpecIso _).inv ≫
      (D.residueCoordDivisorToBase ((D.universalFamilyMapOver W).base w)).appTop ≫
        (D.residueCoordDivisor
          ((D.universalFamilyMapOver W).base w)).Γevaluation z).hom.toAlgebra
  refine (smoothAt_iff_isRegularLocalRing_stalk
    (D.residueCoordDivisorToBase ((D.universalFamilyMapOver W).base w)) z
    (Algebra.isSeparableExtension_of_perfectField _ _)).mpr ?_
  refine D.isRegularLocalRing_stalk_residueCoordDivisor _ hsurj c hc z ?_ hgerm
  have h1 : (D.universalDivisor.comap (D.fibreParameterMap
          ↥(D.parameterBase.residueField ((D.universalFamilyMapOver W).base w))
          (D.residueCoord ((D.universalFamilyMapOver W).base w)))).subschemeι ≫
        D.baseChangeToX ↥(D.parameterBase.residueField
          ((D.universalFamilyMapOver W).base w)) =
      D.specializedToUniversal _ (D.residueCoord ((D.universalFamilyMapOver W).base w)) ≫
        D.universalDivisor.subschemeι ≫ D.parameterProjection := by
    rw [← D.fibreParameterMap_comp_parameterProjection _
        (D.residueCoord ((D.universalFamilyMapOver W).base w)), ← Category.assoc,
      (D.universalDivisor.isPullback_comap (D.fibreParameterMap _
        (D.residueCoord ((D.universalFamilyMapOver W).base w)))).w, Category.assoc]
    rfl
  refine (congrArg (fun φ : _ ⟶ D.X => φ.base z) h1).trans ?_
  change D.parameterProjection.base (D.universalDivisor.subschemeι.base
    ((D.specializedToUniversal _
      (D.residueCoord ((D.universalFamilyMapOver W).base w))).base z)) = x
  rw [hz]
  exact hwx

/-- **The standing basis of the linear system, read through `Fin (m + 1)`**, is the standing
basis read through the comparison of the two index sets. -/
theorem basisIndexEquiv_reindex_basis {m : ℕ} (hm : Module.finrank D.k D.V = m + 1)
    (l : Fin (m + 1)) :
    (D.basis.reindex (finCongr hm)) l =
      D.basis (D.basisIndexEquiv (D.basis.reindex (finCongr hm)) l).down := by
  rw [Module.Basis.reindex_apply]
  rfl

/-- **[Stacks, Tag 0FD6].** In the standing situation of [Stacks, Tag 0G47] with `X` smooth and
of finite type over an algebraically closed field `k`, if the image of `ψ` generates `L` and the
morphism `φ_{L,ψ} : X → 𝐏(V)` it determines is an immersion, then the divisor `H_v` is smooth
over `k'` for general `v ∈ V ⊗_k k'`.

Nothing is assumed in place of a missing input. Hypothesis (1) of the tag is
`[Smooth D.toBase]`, hypothesis (2) is `Stacks.Bertini.FamilyDivisors.Generates` and hypothesis
(3) is `Stacks.Bertini.FamilyDivisors.IsImmersive`, taken at the standing basis of the linear
system read through `Fin (m + 1)`. The whole of the source's proof is proved: the generic
flatness of `q` (`exists_nonempty_opens_flat_universalFamilyMapOver`), the surjectivity of the
evaluation at a closed point (`surjective_evalQuotient_of_isClosed`), the dimension count of
[Stacks, Tag 0B2L], the identification of the fibre of `q` with the divisor of a coordinate
tuple (`parameterPoint_residueCoord`), and the Jacobian criterion itself
(`Stacks.Bertini.FamilyDivisors.jacobianAtDivisor`).

What remains in the signature and is **not** a hypothesis of the source. `[QuasiCompact
D.toBase]` together with `[Smooth D.toBase]` is the source's standing hypothesis that `X` is of
finite type over `k`, in the shape clause (1) of `Stacks.Bertini.FamilyDivisors.Hypotheses` uses;
`[NoetherianSpace D.universalDivisorScheme]` is that finiteness read on `H_univ`. `hX`, `hdim`
and `hnr` are the dimension data the count is run with: `X` of dimension at most `n`, of
dimension exactly `n` at each of its closed points, and `n + 1 ≤ dim V`. The source assumes none
of these — it runs the count on one irreducible component at a time and reads `n + 1 ≤ dim V`
off the surjectivity of `ev_x` — so `hdim` is an equidimensionality assumption added here and
`hnr` a numerical one. `[IsAlgClosed D.k]` is the case the source reduces to by
[Stacks, Tag 02FY], a reduction not formalized here. -/
-- The `@[stacks 0FD6]` registration is deliberately absent here: this statement assumes its
-- own input, and the pointwise carriers (:612, :673) and
-- forGeneral_smooth_specializedDivisor_of_basis (BertiniFieldBaseChangeDescent.lean:276) assume
-- no dimension data.
theorem forGeneral_smooth_specializedDivisor_of_generates [IsAlgClosed D.k] [Smooth D.toBase]
    [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    (hgen : D.Generates) {m n : ℕ} (hm : Module.finrank D.k D.V = m + 1)
    (himm : D.IsImmersive (D.basis.reindex (finCongr hm))
      (D.generatesBy_basis hgen (D.basis.reindex (finCongr hm))))
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor himm hnr hX hdim
    (D.jacobianAtDivisor _ (D.basisIndexEquiv_reindex_basis hm))

/-- **[Stacks, Tag 0FD6], with hypothesis (3) at an arbitrary basis of the linear system.** This
is `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates` with the
immersion hypothesis taken at any basis `b` of `V`, at any index type, rather than at the
standing basis read through `Fin (m + 1)`: the hypothesis does not depend on the basis
(`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'`), while the Jacobian criterion is
applied at the standing basis, where `Stacks.Bertini.FamilyDivisors.jacobianAtDivisor` proves it.
No relation between `b` and the standing basis is assumed, and the equality `dim V = m + 1` the
unprimed statement takes as an argument is read off `b` instead.

**No `@[stacks]` attribute is attached, deliberately.** This statement is strictly weaker than
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_`
`basis` below, which carries hypothesis (3) at an arbitrary basis with the dimension data `hnr`,
`hX`, `hdim` and `[NoetherianSpace D.universalDivisorScheme]` all discharged rather than assumed;
registering it would add nothing the registration there does not already carry. It exists so that
the dimension-data form of the carrier, too, can be used with hypothesis (3) at whichever basis a
caller holds it. -/
theorem forGeneral_smooth_specializedDivisor_of_generates_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] [NoetherianSpace D.universalDivisorScheme]
    (hgen : D.Generates) {m n : ℕ} (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (himm : D.IsImmersive b (D.generatesBy_basis hgen b))
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hdim : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDimAt D.X x = (n : WithBot ℕ∞)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_of_basis himm
    (D.basis.reindex (finCongr (D.finrank_eq_of_basis b))) hnr hX hdim
    (D.jacobianAtDivisor _
      (D.basisIndexEquiv_reindex_basis (D.finrank_eq_of_basis b)))

/-- **[Stacks, Tag 0FD6].** In the standing situation of [Stacks, Tag 0G47] with `X` smooth and
of finite type over an algebraically closed field `k`, if the image of `ψ` generates `L` and the
morphism `φ_{L,ψ} : X → 𝐏(V)` it determines is an immersion, then the divisor `H_v` is smooth
over `k'` for general `v ∈ V ⊗_k k'`.

This is `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates` with
its three non-source numerical and finiteness hypotheses removed. Hypothesis (1) of the tag is
`[Smooth D.toBase]` together with `[QuasiCompact D.toBase]`, which is `X` of finite type over
`k` in the shape clause (1) of `Stacks.Bertini.FamilyDivisors.Hypotheses` uses; hypothesis (2) is
`Stacks.Bertini.FamilyDivisors.Generates` and hypothesis (3) is
`Stacks.Bertini.FamilyDivisors.IsImmersive`. The whole of the source's proof is proved, as for
that theorem, and in addition:

* the Noetherianness of `H_univ`, which is derived from `X` being of finite type over `k`
  (`Stacks.Bertini.FamilyDivisors.noetherianSpace_universalDivisorScheme`) rather than assumed;
* the dimension data. The count is run at each closed point `x` of `X` with the local dimension
  `n_x` of `X` at `x` in place of one global `n`: `n_x` exists because the local ring of a
  smooth scheme at a closed point is regular
  (`Stacks.Bertini.FamilyDivisors.exists_natCast_eq_topologicalKrullDimAt_of_isClosed`), the
  inequality `n_x + 1 ≤ dim V` is read off the surjectivity of `ev_x`
  (`Stacks.Bertini.FamilyDivisors.succ_le_of_smooth`) as it is in the source, and the fibre bound
  `dim V - (n_x + 1)` is combined with `n_x` itself rather than with a global bound, by
  `AlgebraicGeometry.topologicalKrullDim_le_of_isClosed_singleton_fiber_add_target`. So no
  equidimensionality, no bound on `dim X`, and no numerical hypothesis `n + 1 ≤ dim V` remain.

What remains in the signature and is **not** a hypothesis of the source: `[IsAlgClosed D.k]`,
the case the source reduces to by [Stacks, Tag 02FY], a reduction not formalized here; and that
hypothesis (3) is taken at the standing basis of the linear system read through `Fin (m + 1)`
rather than at an arbitrary basis. -/
@[stacks 0FD6 "the conclusion from hypotheses (2) and (3) with no proof obligation assumed and \
no dimension data assumed -- the whole of the source's proof is discharged, the count being run \
at each closed point with the local dimension of X there -- but over an algebraically closed \
field, and with (3) taken at the standing basis; the source assumes neither of those two"]
theorem forGeneral_smooth_specializedDivisor_of_generates_pointwise [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] (hgen : D.Generates) {m : ℕ}
    (hm : Module.finrank D.k D.V = m + 1)
    (himm : D.IsImmersive (D.basis.reindex (finCongr hm))
      (D.generatesBy_basis hgen (D.basis.reindex (finCongr hm)))) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_pointwise himm
    fun _ => D.jacobianAtDivisor _ (D.basisIndexEquiv_reindex_basis hm)

/-- **[Stacks, Tag 0FD6].** In the standing situation of [Stacks, Tag 0G47] with `X` smooth and
of finite type over an algebraically closed field `k`, if the image of `ψ` generates `L` and the
morphism `φ_{L,ψ} : X → 𝐏(V)` it determines is an immersion, then the divisor `H_v` is smooth
over `k'` for general `v ∈ V ⊗_k k'`.

This is
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise` with
**hypothesis (3) taken at an arbitrary basis of the linear system** rather than at the standing
basis: the basis `b` is any basis of `V`, and the generation hypothesis at it is hypothesis (2)
of the tag, which is basis free (`Stacks.Bertini.FamilyDivisors.generates_iff_generatesBy_basis`).
No relation between `b` and the standing basis `D.basis` is assumed, and no bound on `dim V` is
needed: `b` itself exhibits one.

The basis enters the proof in two roles, which this statement separates. Hypothesis (3) feeds
only the surjectivity of the evaluation `ev_x`, a property of the basis-free map
`Stacks.Bertini.FamilyDivisors.evalVector` and so of no basis at all
(`Stacks.Bertini.FamilyDivisors.surjective_evalCoord_sectionOf_iff`); the Jacobian criterion
`Stacks.Bertini.FamilyDivisors.JacobianAtDivisor`, on the other hand, can only be stated against
the standing basis, since the coordinates of the parameter space are coefficients against it.
The chain
`Stacks.Bertini.FamilyDivisors.exists_evalMatrix_of_basis` →
`…smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_pointwise_of_basis` carries the two
as separate parameters, and this statement instantiates the second at
`D.basis.reindex (finCongr …)`, which is where
`Stacks.Bertini.FamilyDivisors.jacobianAtDivisor` applies.

What remains in the signature and is **not** a hypothesis of the source: `[IsAlgClosed D.k]` and
`[QuasiCompact D.toBase]`. `[Smooth D.toBase]` is hypothesis (1); it gives `X` locally of finite
presentation, hence locally of finite type, but not quasi-compact, so `[QuasiCompact D.toBase]`
is an addition — [Stacks, Tag 0G47] assumes of `X` only that it is a scheme over `k`, and
clause (1) of `Stacks.Bertini.FamilyDivisors.Hypotheses`, which does assume finite type, is
[Stacks, Tag 0G4F]'s hypothesis rather than 0G47's standing situation. It is however not needed:
hypothesis (3) implies it, since `𝐏(V)` has a Noetherian underlying space and an immersion
embeds `X` in it. The sibling
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_`
`basis'` is this statement with the binder discharged that way; see
`Stacks.Bertini.FamilyDivisors.quasiCompact_of_isImmersive`. Every proof obligation of the
source's argument is discharged, and so is all the dimension data: no equidimensionality of `X`,
no bound on `dim X`, no inequality `n + 1 ≤ dim V`, and no Noetherianness of `H_univ` is
assumed, the count being run at each closed point of `X` with the local dimension of `X` there.
`[IsAlgClosed D.k]` is the case the source reduces to by [Stacks, Tag 02FY]; that reduction is
**not** formalized here, and it is not a loose end but a development of its own — it needs the
base change of the standing situation along `k → k̄`, which nothing in the library constructs,
and above all the transfer of hypothesis (3) itself, for which the base-change compatibility of
`AlgebraicGeometry.toProjectiveSpaceOfModule` is missing. -/
@[stacks 0FD6 "the conclusion from hypotheses (2) and (3) with no proof obligation and no \
dimension data assumed, and with (3) at an arbitrary basis of the linear system -- the whole of \
the source's proof is discharged, the count being run at each closed point with the local \
dimension of X there. TWO hypotheses here are not the source's: that k is algebraically closed, \
the case Tag 02FY reduces to, and [QuasiCompact D.toBase]. Situation 0G47 assumes only that X \
is a scheme over k and Tag 0FD6 adds only smoothness, so quasi-compactness is an addition; it \
is NOT clause (1) of this project's Hypotheses bundle, which is Tag 0G4F's hypothesis, not \
0G47's standing situation. (3) is also still spelled at a basis rather than on the intrinsic \
morphism phi_(L, psi), but that is now only a spelling: the two agree by \
Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis, so the hypothesis does not depend on \
which basis it is read at"]
theorem forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_basis [IsAlgClosed D.k]
    [Smooth D.toBase] [QuasiCompact D.toBase] (hgen : D.Generates) {m : ℕ}
    (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (himm : D.IsImmersive b (D.generatesBy_basis hgen b)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  D.smooth_specializedDivisor_forGeneral_of_jacobianAtDivisor_pointwise_of_basis himm
    (D.basis.reindex (finCongr (D.finrank_eq_of_basis b)))
    fun _ => D.jacobianAtDivisor _
      (D.basisIndexEquiv_reindex_basis (D.finrank_eq_of_basis b))

end Divisor

end Stacks.Bertini.FamilyDivisors

end
