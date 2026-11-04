module

public import StacksFrontier.AlgebraicGeometry.CoveringResolution.Augmentation
public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic

/-!
# The contracting homotopy of the Čech resolution (towards Tag 02FU)

`StacksDraft.AlgebraicGeometry.F3.CoveringResolution.Augmentation` assembles eight of the nine
fields of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`, leaving the
  quasi-isomorphism property of the
augmentation. This file proves the local half of that property: over an open set `V`
contained in a member `U i₀` of the covering, the augmented Čech complex of sections is
contractible, by the explicit homotopy of the source's own proof,

`h(s)_{i₀ … i_{p-1}} = s_{i₀ i₀ … i_{p-1}}`,  `dh + hd = id`.

## Main definitions

* `factorRestr X R F V h` is restriction between two factors of a Čech term over a fixed
  open set `V`, for an inclusion `V ⊓ A ≤ V ⊓ B` of the *intersections with `V`* rather than
  of the index open sets. `factorDown` and `factorBack` are the corresponding maps to and
  from the sections of the enlargement of `F` over `V`.
* `diff X R U F p` is the Čech differential on sections over `V`, and `aug0 X R U F` the
  augmentation on sections over `V`.
* `homotopy X R U i₀ F hV p` is the contracting homotopy in degree `p + 1`, and
  `homotopyZero` its degree `-1` component into the sections of `F` itself. Both are built
  from the product coordinates `Stacks.CechTotalComplex.CoveringResolution.cechSections`, by
    prepending the index `i₀`.

## Main results

* `homotopy_id`: `dh + hd = id` in positive degrees, and `homotopy_zero_id` in degree zero.
* `aug0_comp_homotopyZero`: the augmentation is *split* injective on sections over `V`.
* `exists_preimage_succ`, `exists_preimage_zero` and `aug0_injective` are the elementwise
  consequences, in exactly the form the locality criterion
  `Stacks.SheafOfModules.ComplexLocality.exact_of_isOpenCover` consumes.

## Implementation notes

`Stacks.CechTotalComplex.CoveringResolution.cechIntersection X U (p+1) (Fin.cons i₀ s)` is `U i₀ ⊓
  ⨅ k, U (s k)`, which is
*not* below `⨅ k, U (s k)`; only its intersection with `V` is, by `V ≤ U i₀`. So the
restriction the homotopy needs is not `coordFactorMap`, which is induced by an inclusion of
the index open sets, and `factorRestr` is the required generalisation. It is a one-off
`ModuleCat` morphism, built with `ConcreteCategory.ofHom` — `ModuleCat.ofHom` does not apply,
because its source and target must be unified with `ModuleCat.of`, which a Čech factor is not
syntactically; its `map_smul'` is the same computation as
`Stacks.CechTotalComplex.CoveringResolution.infPushforwardRestriction`'s, namely that two
  restrictions of ring sections
between the same pair of open sets agree.

`factorRestr` depends on its inequality only as a *proposition*, so two restrictions with the
same endpoints are the same term. That is what makes `coordπ_factorRestr_canon` a `rfl` after
`subst`, and it is how the two alternating sums of the homotopy identity are matched term by
term: each side is normalised to `coordπ … r ≫ factorRestr …`, and then only the index tuples
have to be compared. No `eqToHom` occurs in this file, and no rewrite ever moves an index
inside a dependent type.

Three spellings have to be pinned down to keep `rw` usable, all for the reason recorded for
the `@[expose]` boundary: the vertex of the Čech product cone is spelled through
`Limits.getLimitCone`, which is not exposed, so a goal mentioning it is not type-correct at
the `implicit` transparency at which `rw` builds its motive and at which instance search for
`+` runs. Hence `coordPt_hom_ext` (the cone's universal property with the vertex spelled
`coordPt`), `aug0` (the augmentation with its target spelled `coordPt`) and `factorDown`
(`Stacks.CechTotalComplex.CoveringResolution.infUnit` with its target spelled `coordFactor`). With
  those three names in place
every step of the homotopy identity is an ordinary `rw` in `ModuleCat`, and the sign algebra
is `abel`.

## References

* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Equation 01EE](https://stacks.math.columbia.edu/tag/01EE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open Stacks.CategoryTheory.CechComplex

universe u v w t y

namespace Stacks.AlgebraicGeometry.CoveringResolutionQuasiIso

open Stacks.CechTotalComplex.CoveringResolution Stacks.AlgebraicGeometry.CoveringResolution

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})

section Factors

variable (F : SheafOfModules.{w} R) (V : Opens X)

/-- Restriction between the factors of a Čech term over a fixed open set `V`, for an
inclusion of the index open sets that holds only after intersecting with `V`. -/
noncomputable def factorRestr {A B : Opens X} (h : V ⊓ A ≤ V ⊓ B) :
    coordFactor.{u, v, w, t} X R F V B ⟶ coordFactor.{u, v, w, t} X R F V A :=
  ConcreteCategory.ofHom
    { toFun := fun x => (uliftSheaf.{u, v, w, t} X R F).val.map (homOfLE h).op x
      map_add' := fun x y =>
        ((uliftSheaf.{u, v, w, t} X R F).val.map (homOfLE h).op).hom.map_add x y
      map_smul' := fun r x => by
        refine ((uliftSheaf.{u, v, w, t} X R F).val.map_smul (homOfLE h).op _ x).trans ?_
        refine congrArg (fun ρ => ρ • (uliftSheaf.{u, v, w, t} X R F).val.map
          (homOfLE h).op x) ?_
        have key : R.obj.map (homOfLE (inf_le_left : V ⊓ B ≤ V)).op ≫
              R.obj.map (homOfLE h).op =
            R.obj.map (homOfLE (inf_le_left : V ⊓ A ≤ V)).op :=
          (R.obj.map_comp _ _).symm.trans (congrArg R.obj.map (Subsingleton.elim _ _))
        exact ConcreteCategory.congr_hom key r }

/-- `factorRestr` is restriction of sections of `F`. -/
theorem factorRestr_apply {A B : Opens X} (h : V ⊓ A ≤ V ⊓ B)
    (x : coordFactor.{u, v, w, t} X R F V B) :
    factorRestr.{u, v, w, t} X R F V h x =
      ULift.up (F.val.map (homOfLE h).op x.down) := rfl

/-- Restriction along the identity inclusion is the identity. -/
theorem factorRestr_refl {A : Opens X} (h : V ⊓ A ≤ V ⊓ A) :
    factorRestr.{u, v, w, t} X R F V h = 𝟙 _ := by
  ext x
  refine ((uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply
    (Subsingleton.elim _ (𝟙 (op (V ⊓ A)))) x).trans ?_
  exact map_id_apply X R (uliftSheaf.{u, v, w, t} X R F).val (op (V ⊓ A)) x

/-- Restrictions between factors compose. -/
theorem factorRestr_trans {A B C : Opens X} (h : V ⊓ A ≤ V ⊓ B) (h' : V ⊓ B ≤ V ⊓ C) :
    factorRestr.{u, v, w, t} X R F V h' ≫ factorRestr.{u, v, w, t} X R F V h =
      factorRestr.{u, v, w, t} X R F V (h.trans h') := by
  ext x
  exact ((uliftSheaf.{u, v, w, t} X R F).val.map_comp_apply _ _ x).symm.trans
    ((uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply (Subsingleton.elim _ _) x)

/-- The restriction induced by an inclusion of the index open sets is a `factorRestr`. -/
theorem coordFactorMap_eq_factorRestr {A B : Opens X} (h : A ≤ B) :
    coordFactorMap.{u, v, w, t} X R F V h =
      factorRestr.{u, v, w, t} X R F V (inf_le_inf_left V h) := by
  ext x
  exact (coordFactorMap_apply.{u, v, w, t} X R F V h x).trans
    (factorRestr_apply.{u, v, w, t} X R F V (inf_le_inf_left V h) x).symm

/-- Restriction *back* from a factor whose index open set contains `V`: since
`V ⊓ A = V` there, the sections of `F` over `V ⊓ A` are the sections over `V`. -/
noncomputable def factorBack {A : Opens X} (h : V ≤ A) :
    coordFactor.{u, v, w, t} X R F V A ⟶
      ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V) :=
  ConcreteCategory.ofHom
    { toFun := fun x => (uliftSheaf.{u, v, w, t} X R F).val.map
        (homOfLE (le_inf le_rfl h : V ≤ V ⊓ A)).op x
      map_add' := fun x y =>
        ((uliftSheaf.{u, v, w, t} X R F).val.map
          (homOfLE (le_inf le_rfl h : V ≤ V ⊓ A)).op).hom.map_add x y
      map_smul' := fun r x => by
        refine ((uliftSheaf.{u, v, w, t} X R F).val.map_smul
          (homOfLE (le_inf le_rfl h : V ≤ V ⊓ A)).op _ x).trans ?_
        refine congrArg (fun ρ => ρ • (uliftSheaf.{u, v, w, t} X R F).val.map
          (homOfLE (le_inf le_rfl h : V ≤ V ⊓ A)).op x) ?_
        have key : R.obj.map (homOfLE (inf_le_left : V ⊓ A ≤ V)).op ≫
              R.obj.map (homOfLE (le_inf le_rfl h : V ≤ V ⊓ A)).op = 𝟙 _ :=
          (R.obj.map_comp _ _).symm.trans
            ((congrArg R.obj.map (Subsingleton.elim _ (𝟙 (op V)))).trans (R.obj.map_id _))
        exact ConcreteCategory.congr_hom key r }

/-- `factorBack` is restriction of sections of `F`. -/
theorem factorBack_apply {A : Opens X} (h : V ≤ A)
    (x : coordFactor.{u, v, w, t} X R F V A) :
    factorBack.{u, v, w, t} X R F V h x =
      ULift.up (F.val.map (homOfLE (le_inf le_rfl h : V ≤ V ⊓ A)).op x.down) := rfl

/-- Restriction of sections to the intersection with the index open set, with its target
spelled `coordFactor`. This is `infUnit` evaluated at `V`; the spelling is what makes it
composable with `factorRestr` and `factorBack` at the transparency `rw` works at. -/
noncomputable def factorDown (A : Opens X) :
    ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V) ⟶
      coordFactor.{u, v, w, t} X R F V A :=
  (infUnit.{u, v, w, t} X R F A).val.app (op V)

/-- `factorDown` is `infUnit` on sections over `V`. -/
theorem factorDown_eq (A : Opens X) :
    factorDown.{u, v, w, t} X R F V A = (infUnit.{u, v, w, t} X R F A).val.app (op V) := rfl

/-- `factorDown` is restriction of sections of `F`. -/
theorem factorDown_apply (A : Opens X)
    (x : ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V)) :
    factorDown.{u, v, w, t} X R F V A x =
      ULift.up (F.val.map (homOfLE (inf_le_left : V ⊓ A ≤ V)).op x.down) := rfl

/-- Restricting to a factor and then further is restricting to the further factor. -/
theorem factorDown_comp_factorRestr {A B : Opens X} (h : V ⊓ A ≤ V ⊓ B) :
    factorDown.{u, v, w, t} X R F V B ≫ factorRestr.{u, v, w, t} X R F V h =
      factorDown.{u, v, w, t} X R F V A := by
  ext x
  refine ((uliftSheaf.{u, v, w, t} X R F).val.map_comp_apply _ _ x).symm.trans ?_
  exact (uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply (Subsingleton.elim _ _) x

/-- Restricting to a factor whose index open set contains `V` and coming back is the
identity. -/
theorem factorDown_comp_factorBack {A : Opens X} (h : V ≤ A) :
    factorDown.{u, v, w, t} X R F V A ≫ factorBack.{u, v, w, t} X R F V h = 𝟙 _ := by
  ext x
  refine ((uliftSheaf.{u, v, w, t} X R F).val.map_comp_apply _ _ x).symm.trans ?_
  refine ((uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply
    (Subsingleton.elim _ (𝟙 (op V))) x).trans ?_
  exact map_id_apply X R (uliftSheaf.{u, v, w, t} X R F).val (op V) x

/-- Coming back from a factor whose index open set contains `V` and restricting again is a
single restriction. -/
theorem factorBack_comp_factorDown {A B : Opens X} (h : V ≤ A) :
    factorBack.{u, v, w, t} X R F V h ≫ factorDown.{u, v, w, t} X R F V B =
      factorRestr.{u, v, w, t} X R F V (inf_le_left.trans (le_inf le_rfl h)) := by
  ext x
  refine ((uliftSheaf.{u, v, w, t} X R F).val.map_comp_apply _ _ x).symm.trans ?_
  exact (uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply (Subsingleton.elim _ _) x

end Factors

/-! ### The contracting homotopy -/

section Homotopy

variable {ι : Type t} (U : ι → Opens X) (i₀ : ι) {V : Opens X} (F : SheafOfModules.{w} R)

/-- Prepending the index of a member of the covering that contains `V` does not change the
intersection with `V`. -/
theorem inf_cechIntersection_cons (hV : V ≤ U i₀) (p : ℕ) (s : Fin (p + 1) → ι) :
    V ⊓ cechIntersection X U (p + 1) (Fin.cons i₀ s) = V ⊓ cechIntersection X U p s := by
  obtain ⟨c, hc⟩ : ∃ c : Fin (p + 2) → ι, c = Fin.cons i₀ s := ⟨_, rfl⟩
  have key : ∀ m : Fin (p + 1), U (c m.succ) = U (s m) := fun m => by rw [hc]; simp
  have key0 : U (c 0) = U i₀ := by rw [hc]; simp
  rw [← hc]
  have h1 : cechIntersection X U (p + 1) c = ⨅ k : Fin (p + 2), U (c k) := rfl
  have h2 : cechIntersection X U p s = ⨅ m : Fin (p + 1), U (s m) := rfl
  rw [h1, h2]
  refine le_antisymm (inf_le_inf_left V (le_iInf fun m => ?_))
    (le_inf inf_le_left (le_iInf fun k => ?_))
  · exact (iInf_le (fun k => U (c k)) m.succ).trans (le_of_eq (key m))
  · induction k using Fin.cases with
    | zero => exact inf_le_left.trans (hV.trans (le_of_eq key0.symm))
    | succ m =>
      exact inf_le_right.trans
        ((iInf_le (fun a => U (s a)) m).trans (le_of_eq (key m).symm))

/-- The inequality along which the contracting homotopy restricts. -/
theorem consLe (hV : V ≤ U i₀) (p : ℕ) (s : Fin (p + 1) → ι) :
    V ⊓ cechIntersection X U p s ≤ V ⊓ cechIntersection X U (p + 1) (Fin.cons i₀ s) :=
  (inf_cechIntersection_cons X U i₀ hV p s).ge

/-- Two morphisms into the sections over `V` of a Čech term agree as soon as they agree in
every product coordinate. This is `coordFanIsLimit` with the vertex spelled `coordPt`: the
cone's own vertex is spelled through `Limits.getLimitCone`, which is not exposed, so a goal
stated with it is not rewritable. -/
theorem coordPt_hom_ext {p : ℕ} {M : ModuleCat.{max u v w t} (R.obj.obj (op V))}
    {f g : M ⟶ coordPt.{u, v, w, t} X R U F p V}
    (h : ∀ s : Fin (p + 1) → ι, f ≫ coordπ.{u, v, w, t} X R U F p V s =
      g ≫ coordπ.{u, v, w, t} X R U F p V s) : f = g := by
  refine (coordFanIsLimit.{u, v, w, t} X R U F p V).hom_ext fun j => ?_
  obtain ⟨s⟩ := j
  exact h s

/-- The differential of the Čech complex, on sections over `V`. -/
noncomputable def diff (p : ℕ) :
    coordPt.{u, v, w, t} X R U F p V ⟶ coordPt.{u, v, w, t} X R U F (p + 1) V :=
  (SheafOfModules.evaluation.{max u v w t} R (op V)).map
    (((cechComplexFunctor U).obj (infPushforwardOpens.{u, v, w, t} X R F)).d p (p + 1))

/-- Equation 01EE in the product coordinates, for `diff`. -/
theorem diff_comp_coordπ (p : ℕ) (s : Fin (p + 2) → ι) :
    diff.{u, v, w, t} X R U F p ≫ coordπ.{u, v, w, t} X R U F (p + 1) V s =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (coordπ.{u, v, w, t} X R U F p V (s ∘ j.succAbove) ≫
          coordFactorMap.{u, v, w, t} X R F V
            (cechIntersection_le_succAbove X U p s j)) :=
  coordπ_d.{u, v, w, t} X R U F p V s

/-- Two coordinates with equal index tuples, followed by restrictions with the same
endpoints, agree. The restriction maps depend on their inequality only as a proposition, so
once the index tuples are identified the two composites are the same term. -/
theorem coordπ_factorRestr_canon (p : ℕ) {r r' : Fin (p + 1) → ι} (hr : r = r')
    {B C : Opens X} (h₁ : V ⊓ B ≤ V ⊓ cechIntersection X U p r) (h₂ : V ⊓ C ≤ V ⊓ B)
    (h₃ : V ⊓ C ≤ V ⊓ cechIntersection X U p r') :
    coordπ.{u, v, w, t} X R U F p V r ≫
        factorRestr.{u, v, w, t} X R F V h₁ ≫ factorRestr.{u, v, w, t} X R F V h₂ =
      coordπ.{u, v, w, t} X R U F p V r' ≫ factorRestr.{u, v, w, t} X R F V h₃ := by
  subst hr
  rw [factorRestr_trans]

/-- The contracting homotopy of the source's proof: in the product coordinates it prepends
the index `i₀` of a member of the covering containing `V`. -/
noncomputable def homotopy (hV : V ≤ U i₀) (p : ℕ) :
    coordPt.{u, v, w, t} X R U F (p + 1) V ⟶ coordPt.{u, v, w, t} X R U F p V :=
  (coordFanIsLimit.{u, v, w, t} X R U F p V).lift
    (Fan.mk (coordPt.{u, v, w, t} X R U F (p + 1) V) fun s =>
      coordπ.{u, v, w, t} X R U F (p + 1) V (Fin.cons i₀ s) ≫
        factorRestr.{u, v, w, t} X R F V (consLe X U i₀ hV p s))

/-- The coordinates of the contracting homotopy. -/
theorem homotopy_comp_coordπ (hV : V ≤ U i₀) (p : ℕ) (s : Fin (p + 1) → ι) :
    homotopy.{u, v, w, t} X R U i₀ F hV p ≫ coordπ.{u, v, w, t} X R U F p V s =
      coordπ.{u, v, w, t} X R U F (p + 1) V (Fin.cons i₀ s) ≫
        factorRestr.{u, v, w, t} X R F V (consLe X U i₀ hV p s) := by
  have h := (coordFanIsLimit.{u, v, w, t} X R U F p V).fac
    (Fan.mk (coordPt.{u, v, w, t} X R U F (p + 1) V) fun s' =>
      coordπ.{u, v, w, t} X R U F (p + 1) V (Fin.cons i₀ s') ≫
        factorRestr.{u, v, w, t} X R F V (consLe X U i₀ hV p s')) ⟨s⟩
  rwa [coordFan_π] at h

/-- The terms of the homotopy identity: the coordinate at the tuple obtained from `t` by
deleting its `j`-th index and prepending `i₀`, restricted to the `t`-intersection. -/
noncomputable def hterm (hV : V ≤ U i₀) (p : ℕ) (t : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    coordPt.{u, v, w, t} X R U F (p + 1) V ⟶
      coordFactor.{u, v, w, t} X R F V (cechIntersection X U (p + 1) t) :=
  coordπ.{u, v, w, t} X R U F (p + 1) V (Fin.cons i₀ (t ∘ j.succAbove)) ≫
    factorRestr.{u, v, w, t} X R F V
      ((inf_le_inf_left V (cechIntersection_le_succAbove X U p t j)).trans
        (consLe X U i₀ hV p (t ∘ j.succAbove)))

/-- **`dh` coordinatewise**: the differential of a homotopy value is the alternating sum of
the terms `hterm`. -/
theorem homotopy_comp_diff_comp_coordπ (hV : V ≤ U i₀) (p : ℕ) (t : Fin (p + 2) → ι) :
    homotopy.{u, v, w, t} X R U i₀ F hV p ≫
        diff.{u, v, w, t} X R U F p ≫ coordπ.{u, v, w, t} X R U F (p + 1) V t =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • hterm.{u, v, w, t} X R U i₀ F hV p t j := by
  rw [diff_comp_coordπ, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Preadditive.comp_zsmul, ← Category.assoc, homotopy_comp_coordπ, Category.assoc,
    coordFactorMap_eq_factorRestr, factorRestr_trans]
  rfl

/-- **`hd` coordinatewise**: the homotopy value of a differential is the coordinate itself
minus the same alternating sum. The `j = 0` term of the Čech differential of the tuple
`i₀ :: t` is the coordinate at `t`, because `V` is contained in `U i₀`. -/
theorem diff_comp_homotopy_comp_coordπ (hV : V ≤ U i₀) (p : ℕ) (t : Fin (p + 2) → ι) :
    diff.{u, v, w, t} X R U F (p + 1) ≫ homotopy.{u, v, w, t} X R U i₀ F hV (p + 1) ≫
        coordπ.{u, v, w, t} X R U F (p + 1) V t =
      coordπ.{u, v, w, t} X R U F (p + 1) V t -
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • hterm.{u, v, w, t} X R U i₀ F hV p t j := by
  rw [homotopy_comp_coordπ, ← Category.assoc, diff_comp_coordπ, Preadditive.sum_comp,
    Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · have e0 : (Fin.cons i₀ t : Fin (p + 3) → ι) ∘ (0 : Fin (p + 3)).succAbove = t := by
      funext m; simp
    rw [Preadditive.zsmul_comp, Category.assoc, coordFactorMap_eq_factorRestr,
      coordπ_factorRestr_canon X R U F (p + 1) e0 _ _ le_rfl, factorRestr_refl,
      Category.comp_id]
    simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    have e : (Fin.cons i₀ t : Fin (p + 3) → ι) ∘ (j.succ).succAbove =
        Fin.cons i₀ (t ∘ j.succAbove) := by
      funext k
      induction k using Fin.cases with
      | zero => simp
      | succ m => simp
    rw [Preadditive.zsmul_comp, Category.assoc, coordFactorMap_eq_factorRestr,
      coordπ_factorRestr_canon X R U F (p + 1) e _ _
        ((inf_le_inf_left V (cechIntersection_le_succAbove X U p t j)).trans
          (consLe X U i₀ hV p (t ∘ j.succAbove))), Fin.val_succ, pow_succ, mul_neg_one,
      neg_zsmul]
    rfl

/-- **The contracting homotopy identity in positive degrees** (the source's `dh + hd = id`,
on sections over an open set contained in a member of the covering). -/
theorem homotopy_id (hV : V ≤ U i₀) (p : ℕ) :
    homotopy.{u, v, w, t} X R U i₀ F hV p ≫ diff.{u, v, w, t} X R U F p +
        diff.{u, v, w, t} X R U F (p + 1) ≫ homotopy.{u, v, w, t} X R U i₀ F hV (p + 1) =
      𝟙 (coordPt.{u, v, w, t} X R U F (p + 1) V) := by
  refine coordPt_hom_ext.{u, v, w, t} X R U F fun t => ?_
  rw [Preadditive.add_comp, Category.assoc, Category.assoc,
    homotopy_comp_diff_comp_coordπ, diff_comp_homotopy_comp_coordπ, Category.id_comp]
  abel

/-! ### Degree zero -/

/-- The augmentation on sections over `V`, with its target spelled `coordPt`.

The spelling matters: the target of `augZero` is
`(((coveringComplex X R U).obj F).X 0).val.obj (op V)`, which is definitionally `coordPt` but
not syntactically, and the two cannot be identified at the `implicit` transparency at which
`rw` builds its motive and at which instance search for `+` runs, because
`Limits.getLimitCone` is not exposed. So the morphism is named once here with a clean type,
as in the `@[expose]`-boundary recipe. -/
noncomputable def aug0 :
    ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V) ⟶
      coordPt.{u, v, w, t} X R U F 0 V :=
  (augZero.{u, v, w, t} X R U F).val.app (op V)

/-- `aug0` is the augmentation. -/
theorem aug0_eq :
    aug0.{u, v, w, t} X R U F = (augZero.{u, v, w, t} X R U F).val.app (op V) := rfl

/-- `aug0` on a section. -/
theorem aug0_apply (x : ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V)) :
    aug0.{u, v, w, t} X R U F x = (augZero.{u, v, w, t} X R U F).val.app (op V) x := rfl

/-- The coordinates of the augmentation: its `s`-th coordinate is restriction of sections of
`F` to the intersection with `cechIntersection X U 0 s`. -/
theorem aug0_comp_coordπ (s : Fin 1 → ι) :
    aug0.{u, v, w, t} X R U F ≫ coordπ.{u, v, w, t} X R U F 0 V s =
      factorDown.{u, v, w, t} X R F V (cechIntersection X U 0 s) := by
  ext x
  exact ((termIso_hom_apply.{u, v, w, t} X R U F 0 V _ s).symm.trans
      (augZero_coord.{u, v, w, t} X R U F V s x)).trans
    (factorDown_apply.{u, v, w, t} X R F V (cechIntersection X U 0 s) x).symm

/-- A member of the covering containing `V` contains the degree-zero intersection it
indexes. -/
theorem le_cechIntersection_const (hV : V ≤ U i₀) :
    V ≤ cechIntersection X U 0 (fun _ : Fin 1 => i₀) := by
  have h1 : cechIntersection X U 0 (fun _ : Fin 1 => i₀) = ⨅ _ : Fin 1, U i₀ := rfl
  rw [h1]
  exact le_iInf fun _ => hV

/-- The degree `-1` component of the contracting homotopy: the coordinate at the constant
tuple `i₀`, whose intersection with `V` is `V` itself. -/
noncomputable def homotopyZero (hV : V ≤ U i₀) :
    coordPt.{u, v, w, t} X R U F 0 V ⟶
      ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V) :=
  coordπ.{u, v, w, t} X R U F 0 V (fun _ => i₀) ≫
    factorBack.{u, v, w, t} X R F V (le_cechIntersection_const X U i₀ hV)

/-- `homotopyZero` unfolded. -/
theorem homotopyZero_eq (hV : V ≤ U i₀) :
    homotopyZero.{u, v, w, t} X R U i₀ F hV =
      coordπ.{u, v, w, t} X R U F 0 V (fun _ => i₀) ≫
        factorBack.{u, v, w, t} X R F V (le_cechIntersection_const X U i₀ hV) := rfl

/-- **The augmentation is split injective on sections over `V`.** -/
theorem aug0_comp_homotopyZero (hV : V ≤ U i₀) :
    aug0.{u, v, w, t} X R U F ≫ homotopyZero.{u, v, w, t} X R U i₀ F hV = 𝟙 _ := by
  rw [homotopyZero_eq, ← Category.assoc, aug0_comp_coordπ, factorDown_comp_factorBack]

/-- The term of the degree-zero homotopy identity. -/
noncomputable def hterm0 (hV : V ≤ U i₀) (t : Fin 1 → ι) :
    coordPt.{u, v, w, t} X R U F 0 V ⟶
      coordFactor.{u, v, w, t} X R F V (cechIntersection X U 0 t) :=
  coordπ.{u, v, w, t} X R U F 0 V (fun _ => i₀) ≫
    factorRestr.{u, v, w, t} X R F V
      (inf_le_left.trans (le_inf le_rfl (le_cechIntersection_const X U i₀ hV)))

/-- The augmented homotopy term, coordinatewise. -/
theorem homotopyZero_comp_aug0_comp_coordπ (hV : V ≤ U i₀) (t : Fin 1 → ι) :
    homotopyZero.{u, v, w, t} X R U i₀ F hV ≫
        aug0.{u, v, w, t} X R U F ≫ coordπ.{u, v, w, t} X R U F 0 V t =
      hterm0.{u, v, w, t} X R U i₀ F hV t := by
  rw [aug0_comp_coordπ, homotopyZero_eq, Category.assoc, factorBack_comp_factorDown]
  rfl

/-- `hd` in degree zero. -/
theorem diff_comp_homotopy_comp_coordπ_zero (hV : V ≤ U i₀) (t : Fin 1 → ι) :
    diff.{u, v, w, t} X R U F 0 ≫ homotopy.{u, v, w, t} X R U i₀ F hV 0 ≫
        coordπ.{u, v, w, t} X R U F 0 V t =
      coordπ.{u, v, w, t} X R U F 0 V t - hterm0.{u, v, w, t} X R U i₀ F hV t := by
  have hsucc : (1 : Fin 2).succAbove = fun _ : Fin 1 => (0 : Fin 2) :=
    funext (Fin.forall_fin_one.2 rfl)
  have e0 : (Fin.cons i₀ t : Fin 2 → ι) ∘ (0 : Fin 2).succAbove = t := by
    funext m; simp
  have e1 : (Fin.cons i₀ t : Fin 2 → ι) ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 => i₀ := by
    rw [hsucc]; funext m; simp
  rw [homotopy_comp_coordπ, ← Category.assoc, diff_comp_coordπ, Preadditive.sum_comp,
    Fin.sum_univ_two]
  rw [Preadditive.zsmul_comp, Category.assoc, coordFactorMap_eq_factorRestr,
    coordπ_factorRestr_canon X R U F 0 e0 _ _ le_rfl, factorRestr_refl, Category.comp_id]
  rw [Preadditive.zsmul_comp, Category.assoc, coordFactorMap_eq_factorRestr,
    coordπ_factorRestr_canon X R U F 0 e1 _ _
      (inf_le_left.trans (le_inf le_rfl (le_cechIntersection_const X U i₀ hV)))]
  have h0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  rw [h0, h1, pow_zero, pow_one, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]
  rfl

/-- **The contracting homotopy identity in degree zero.** -/
theorem homotopy_zero_id (hV : V ≤ U i₀) :
    homotopyZero.{u, v, w, t} X R U i₀ F hV ≫ aug0.{u, v, w, t} X R U F +
        diff.{u, v, w, t} X R U F 0 ≫ homotopy.{u, v, w, t} X R U i₀ F hV 0 =
      𝟙 (coordPt.{u, v, w, t} X R U F 0 V) := by
  refine coordPt_hom_ext.{u, v, w, t} X R U F fun t => ?_
  rw [Preadditive.add_comp, Category.assoc, Category.assoc,
    homotopyZero_comp_aug0_comp_coordπ, diff_comp_homotopy_comp_coordπ_zero,
    Category.id_comp]
  abel

/-! ### Local exactness of the augmented complex -/

/-- The sum of two morphisms of modules, on an element. -/
theorem moduleCat_add_apply {S : Type*} [Ring S] {M N : ModuleCat.{y} S}
    (f g : M ⟶ N) (m : M) : (f + g) m = f m + g m := rfl

/-- If `b ≫ a + c ≫ d = 𝟙 M` and `c z = 0`, then `z` is the image under `a` of `b z`. -/
private theorem apply_eq_of_add_eq_id {S : Type*} [Ring S] {M N P : ModuleCat.{y} S}
    {a : N ⟶ M} {b : M ⟶ N} {c : M ⟶ P} {d : P ⟶ M} (h : b ≫ a + c ≫ d = 𝟙 M) (z : M)
    (hz : c z = 0) : a (b z) = z := by
  have e1 : a (b z) + d (c z) = z := ConcreteCategory.congr_hom h z
  rwa [hz, map_zero, add_zero] at e1

/-- **Every cycle of positive degree is a boundary on sections over `V`.** -/
theorem exists_preimage_succ (hV : V ≤ U i₀) (p : ℕ)
    (z : coordPt.{u, v, w, t} X R U F (p + 1) V)
    (hz : diff.{u, v, w, t} X R U F (p + 1) z = 0) :
    ∃ x : coordPt.{u, v, w, t} X R U F p V, diff.{u, v, w, t} X R U F p x = z :=
  ⟨_, apply_eq_of_add_eq_id (homotopy_id.{u, v, w, t} X R U i₀ F hV p) z hz⟩

/-- **Every cycle of degree zero comes from a section of `F` over `V`.** -/
theorem exists_preimage_zero (hV : V ≤ U i₀) (z : coordPt.{u, v, w, t} X R U F 0 V)
    (hz : diff.{u, v, w, t} X R U F 0 z = 0) :
    ∃ x : ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V),
      aug0.{u, v, w, t} X R U F x = z :=
  ⟨_, apply_eq_of_add_eq_id (homotopy_zero_id.{u, v, w, t} X R U i₀ F hV) z hz⟩

/-- **The augmentation is injective on sections over `V`.** -/
theorem aug0_injective (hV : V ≤ U i₀)
    {x : ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V)}
    (hx : aug0.{u, v, w, t} X R U F x = 0) : x = 0 := by
  have h := ConcreteCategory.congr_hom (aug0_comp_homotopyZero.{u, v, w, t} X R U i₀ F hV) x
  have e1 : homotopyZero.{u, v, w, t} X R U i₀ F hV (aug0.{u, v, w, t} X R U F x) = x := h
  rw [hx, map_zero] at e1
  exact e1.symm

end Homotopy

end Stacks.AlgebraicGeometry.CoveringResolutionQuasiIso
