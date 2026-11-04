module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecChartEval
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# Morphisms of algebras into the direct image of a point, read at an affine chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `𝒜` a quasi-coherent sheaf of
commutative `𝒪_X`-algebras, `V` an affine étale chart of `X`, `T` an object of the site and
`v : T ⟶ V` a morphism, so that `x := v ≫ (V ⟶ X)` is a point of `X` with values in `T`.  A
morphism of `𝒪_X`-algebras `α : 𝒜 ⟶ x_* 𝒪_T` has a reading at `V`,
`AlgebraicGeometry.Space.chartEval`, a ring map `𝒜(V) ⟶ Γ(T, 𝒪_T)`.  This file proves that
**`α` is determined by that reading**.

## Main results

* `AlgebraicGeometry.Space.algebraHom_ext_of_chartEval`: two morphisms `𝒜 ⟶ x_* 𝒪_T` with the
  same reading at the affine chart `V` are equal.

## Implementation notes

**One argument for every chart, and the covering is in the big fppf site.**  Let `W` be any
étale chart of `X` and `s ∈ 𝒜(W)`.  The section `α(s)` of `x_* 𝒪_T` over `W` is a regular
function on `T ×_X W` (`AlgebraicGeometry.Space.pointSectionsIso`), and regular functions are a
sheaf on the big fppf site (`AlgebraicGeometry.Space.isSheaf_gammaBigFppfOver`).  The two maps
`T ×_X W ⟶ T ⟶ V` and `T ×_X W ⟶ W` factor through one chart `V₀` mapping to `V` and to `W`
(`AlgebraicGeometry.Space.exists_chart_pair_factor`), and on a covering sieve of `T ×_X W` the
map to `V₀` factors through an *affine* chart `Vⱼ` of `X` mapping to `V₀`
(`AlgebraicGeometry.Space.exists_covering_affineChart_factor`).  So, on a member `k` of that
sieve, `k^* α(s)` is the pullback of `α(s|_{Vⱼ})` along a point `c` of `T ×_X Vⱼ`, and since `Vⱼ`
and `V` are affine and `𝒜` is quasi-coherent, `s|_{Vⱼ}` is a sum of products `b · a|_{Vⱼ}` with
`b ∈ 𝒪(Vⱼ)` and `a ∈ 𝒜(V)`
(`AlgebraicGeometry.Space.AlgebraSheaf.bijective_sectionsBaseChange_of_isQuasicoherent`).  On
such a product `α` is `b` times the restriction of `α(a)`, and the point `c` was chosen so that
pulling the restriction of `α(a)` back along it is pulling back the reading of `α` at `a`
(`AlgebraicGeometry.Space.appTop_pointSectionsIso_algebraMap_mul_map`).  No covering of `W` in
the small étale site and no open subscheme of `T ×_X W` is ever used: the only covering is the
fppf sieve, on which the separatedness of regular functions does all the work.

## References

* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Regular functions are separated for the big fppf topology**: two global regular functions
on an object `Q` of the site which agree after pullback along every arrow of a covering sieve are
equal. -/
theorem eq_of_appTop_eq_of_mem_topology {Q : BigFppfOver B S hS} {R : Sieve Q}
    (hR : R ∈ BigFppfOver.topology B S hS Q)
    {f g : Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤)}
    (h : ∀ ⦃T' : BigFppfOver B S hS⦄ (k : T' ⟶ Q), R.arrows k →
      ((BigFppfOver.toScheme B S hS).map k).appTop f =
        ((BigFppfOver.toScheme B S hS).map k).appTop g) :
    f = g :=
  (isSheaf_gammaBigFppfOver B S hS R hR).isSeparatedFor.ext fun _ k hk => h k hk

variable {X : AlgebraicSpaces B S hS} {A : AlgebraSheaf.{u, u} B S hS X.1 X.2}

/-- A morphism `α` of `𝒪_X`-algebras commutes with restriction along `κ : Vⱼ ⟶ V`. -/
private theorem hom_app_map_restrict {Y : AlgebraSheaf.{u, u} B S hS X.1 X.2}
    {V Vj : SmallEtale B S hS X.1} (κ : Vj ⟶ V) (α : A ⟶ Y) (a : A.right.obj.obj (op V)) :
    α.right.hom.app (op Vj) (A.right.obj.map κ.op a) =
      Y.right.obj.map κ.op (α.right.hom.app (op V) a) := by
  have h := ConcreteCategory.congr_hom (α.right.hom.naturality κ.op) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- The projections of `T ×_X Vⱼ` satisfy the square condition for any `κ : Vⱼ ⟶ V`. -/
private theorem fst_comp_eq_snd_comp_chart {V Vj : SmallEtale B S hS X.1} (κ : Vj ⟶ V)
    {T : BigFppfOver B S hS} (x : X.1.obj (op T)) :
    (relativelyRepresentable_specPointOver B S hS T x).fst Vj.obj.hom ≫
      (specPointOver B S hS T x).hom.hom =
      yoneda.map ((relativelyRepresentable_specPointOver B S hS T x).snd Vj.obj.hom ≫
        κ.hom.left) ≫ V.obj.hom := by
  refine ((relativelyRepresentable_specPointOver B S hS T x).isPullback Vj.obj.hom).w.trans ?_
  rw [Functor.map_comp, Category.assoc, CostructuredArrow.w κ.hom]

/-- **The local formula.**  Let `κ : Vⱼ ⟶ V` be a morphism of étale charts of `X`, and let
`c : T' ⟶ T ×_X Vⱼ` be a point lying over `e : T' ⟶ T` and over `e ≫ v` in `V`.  Then pulling
back along `c` the value of `α` at `Vⱼ` on a product `b · a|_{Vⱼ}`, with `b ∈ 𝒪(Vⱼ)` and
`a ∈ 𝒜(V)`, gives the pullback of `b` times the pullback along `e` of the reading of `α` at
`a`. -/
theorem appTop_pointSectionsIso_algebraMap_mul_map {V Vj : SmallEtale B S hS X.1} (κ : Vj ⟶ V)
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    (α : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)) {T' : BigFppfOver B S hS}
    (c : T' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback Vj.obj.hom) (e : T' ⟶ T)
    (hc₁ : yoneda.map c ≫ (relativelyRepresentable_specPointOver B S hS T x).fst Vj.obj.hom =
      yoneda.map e)
    (hc₂ : c ≫ (relativelyRepresentable_specPointOver B S hS T x).snd Vj.obj.hom ≫ κ.hom.left =
      e ≫ v)
    (b : (structureSheaf B S hS X.1 X.2).obj.obj (op Vj)) (a : A.right.obj.obj (op V)) :
    ((BigFppfOver.toScheme B S hS).map c).appTop ((pointSectionsIso B S hS T x Vj).hom
        (α.right.hom.app (op Vj) (A.algebraMap (op Vj) b * A.right.obj.map κ.op a))) =
      ((BigFppfOver.toScheme B S hS).map
          (c ≫ (relativelyRepresentable_specPointOver B S hS T x).snd Vj.obj.hom)).appTop b *
        ((BigFppfOver.toScheme B S hS).map e).appTop (chartEval B S hS A V v x hxv α a) := by
  have hcond := fst_comp_eq_snd_comp_chart B S hS κ x
  have hca : c ≫ (relativelyRepresentable_specPointOver B S hS T x).lift _ _ hcond =
      e ≫ chartGraph B S hS V v x hxv := by
    refine (relativelyRepresentable_specPointOver B S hS T x).hom_ext ?_ ?_
    · rw [Functor.map_comp, Category.assoc, Functor.relativelyRepresentable.lift_fst, hc₁,
        Functor.map_comp, Category.assoc, chartGraph_fst, Category.comp_id]
    · rw [Category.assoc, Functor.relativelyRepresentable.lift_snd, hc₂, Category.assoc,
        chartGraph_snd]
  have h₁ : (pointSectionsIso B S hS T x Vj).hom
      (α.right.hom.app (op Vj) (A.algebraMap (op Vj) b)) =
      ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_specPointOver B S hS T x).snd Vj.obj.hom)).appTop b := by
    rw [α.comm (op Vj) b]
    exact ConcreteCategory.congr_hom (fSharp_app_comp_pointSectionsIso B S hS T x Vj) b
  have h₃ := ConcreteCategory.congr_hom (map_comp_pointSectionsIso B S hS x κ
    ((relativelyRepresentable_specPointOver B S hS T x).lift _ _ hcond)
    (Functor.relativelyRepresentable.lift_fst _ _ _ _)
    (Functor.relativelyRepresentable.lift_snd _ _ _ _)) (α.right.hom.app (op V) a)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h₃
  rw [map_mul, map_mul, map_mul, h₁, hom_app_map_restrict B S hS κ α a, h₃]
  refine congrArg _ ?_
  refine (ConcreteCategory.congr_hom (appTop_map_comp_appTop_map B S hS c _) _).trans ?_
  rw [hca]
  exact (ConcreteCategory.congr_hom (appTop_map_comp_appTop_map B S hS e _) _).symm

/-- **Two morphisms with the same reading agree locally at an affine chart over `V`.**  Let
`κ : Vⱼ ⟶ V` be a morphism of affine étale charts of `X` and let `c : T' ⟶ T ×_X Vⱼ` lie over
`e : T' ⟶ T` and over `e ≫ v` in `V`.  If `α` and `α'` have the same reading at `V`, then the
values of `α` and `α'` at `Vⱼ` on any section of `𝒜`, pulled back along `c`, agree.

By quasi-coherence of `𝒜` every section over `Vⱼ` is a sum of products `b · a|_{Vⱼ}`
(`AlgebraicGeometry.Space.AlgebraSheaf.bijective_sectionsBaseChange_of_isQuasicoherent`), on
which `AlgebraicGeometry.Space.appTop_pointSectionsIso_algebraMap_mul_map` computes both sides
from the readings. -/
theorem appTop_pointSectionsIso_eq_of_chartEval_eq (hA : A.IsQuasicoherent)
    {V Vj : SmallEtale B S hS X.1} (hV : IsAffineChart B S hS X.1 V)
    (hVj : IsAffineChart B S hS X.1 Vj) (κ : Vj ⟶ V) {T : BigFppfOver B S hS}
    (v : T ⟶ V.obj.left) (x : X.1.obj (op T))
    (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    {α α' : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)}
    (h : chartEval B S hS A V v x hxv α = chartEval B S hS A V v x hxv α')
    {T' : BigFppfOver B S hS}
    (c : T' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback Vj.obj.hom) (e : T' ⟶ T)
    (hc₁ : yoneda.map c ≫ (relativelyRepresentable_specPointOver B S hS T x).fst Vj.obj.hom =
      yoneda.map e)
    (hc₂ : c ≫ (relativelyRepresentable_specPointOver B S hS T x).snd Vj.obj.hom ≫ κ.hom.left =
      e ≫ v)
    (s : A.right.obj.obj (op Vj)) :
    ((BigFppfOver.toScheme B S hS).map c).appTop
        ((pointSectionsIso B S hS T x Vj).hom (α.right.hom.app (op Vj) s)) =
      ((BigFppfOver.toScheme B S hS).map c).appTop
        ((pointSectionsIso B S hS T x Vj).hom (α'.right.hom.app (op Vj) s)) := by
  obtain ⟨t, rfl⟩ :=
    (AlgebraSheaf.bijective_sectionsBaseChange_of_isQuasicoherent A hA hV hVj κ).2 s
  induction t using TensorProduct.induction_on with
  | zero =>
    have e : sectionsBaseChange A.underlyingModule κ 0 = (0 : A.right.obj.obj (op Vj)) :=
      map_zero _
    rw [e, map_zero, map_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul b a =>
    rw [← AlgebraSheaf.sectionsBaseChange_tmul_eq A κ b a,
      appTop_pointSectionsIso_algebraMap_mul_map B S hS κ v x hxv α c e hc₁ hc₂ b a,
      appTop_pointSectionsIso_algebraMap_mul_map B S hS κ v x hxv α' c e hc₁ hc₂ b a, h]
  | add t₁ t₂ h₁ h₂ =>
    have e : sectionsBaseChange A.underlyingModule κ (t₁ + t₂) =
        (show A.right.obj.obj (op Vj) from sectionsBaseChange A.underlyingModule κ t₁) +
          (show A.right.obj.obj (op Vj) from sectionsBaseChange A.underlyingModule κ t₂) :=
      map_add _ _ _
    rw [e, map_add, map_add, map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) h₁ h₂

/-- **A morphism of `𝒪_X`-algebras into the direct image of a point is determined by its reading
at an affine chart.**  Let `𝒜` be quasi-coherent, `V` an affine étale chart of `X` and
`v : T ⟶ V` a morphism through which the point `x` of `X` factors.  Two morphisms
`α α' : 𝒜 ⟶ x_* 𝒪_T` with the same reading `AlgebraicGeometry.Space.chartEval` at `V` are equal.

At an arbitrary chart `W` the two values on a section are regular functions on `T ×_X W`; they are
compared after pullback along the members of a covering sieve of the big fppf site on which the
map `T ×_X W ⟶ V ×_X W` factors through affine charts, where
`AlgebraicGeometry.Space.appTop_pointSectionsIso_eq_of_chartEval_eq` applies.  See the
implementation notes. -/
theorem algebraHom_ext_of_chartEval (hA : A.IsQuasicoherent) {V : SmallEtale B S hS X.1}
    (hV : IsAffineChart B S hS X.1 V) {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left)
    (x : X.1.obj (op T)) (hxv : yonedaEquiv.symm x = yoneda.map v ≫ V.obj.hom)
    {α α' : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x)}
    (h : chartEval B S hS A V v x hxv α = chartEval B S hS A V v x hxv α') :
    α = α' := by
  refine AlgebraSheaf.Hom.ext (Sheaf.hom_ext (NatTrans.ext (funext fun Wop => ?_)))
  obtain ⟨W⟩ := Wop
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  have hcond : yoneda.map ((relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom ≫ v) ≫
      V.obj.hom =
      yoneda.map ((relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom) ≫
        W.obj.hom := by
    rw [Functor.map_comp, Functor.relativelyRepresentable.map_fst', Category.assoc, ← hxv]
    exact (relativelyRepresentable_specPointOver B S hS T x).w W.obj.hom
  obtain ⟨V₀, p₁, p₂, τ, hτ₁, hτ₂⟩ := exists_chart_pair_factor B S hS V W _ _ hcond
  obtain ⟨R, hR, hRf⟩ := exists_covering_affineChart_factor B S hS V₀ τ
  suffices key : (pointSectionsIso B S hS T x W).hom (α.right.hom.app (op W) s) =
      (pointSectionsIso B S hS T x W).hom (α'.right.hom.app (op W) s) by
    rw [← Iso.hom_inv_id_apply (pointSectionsIso B S hS T x W) (α.right.hom.app (op W) s), key,
      Iso.hom_inv_id_apply]
  refine eq_of_appTop_eq_of_mem_topology B S hS hR fun T'' k hk => ?_
  obtain ⟨Vj, κ, hVj, kk, hkk⟩ := hRf k hk
  have hk₂ : kk ≫ κ.hom.left ≫ p₂.hom.left =
      k ≫ (relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom := by
    rw [← Category.assoc, ← hkk, Category.assoc, hτ₂]
  have hk₁ : kk ≫ κ.hom.left ≫ p₁.hom.left =
      k ≫ (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom ≫ v := by
    rw [← Category.assoc, ← hkk, Category.assoc, hτ₁]
  have hc : (yoneda.map k ≫ (relativelyRepresentable_specPointOver B S hS T x).fst W.obj.hom) ≫
      (specPointOver B S hS T x).hom.hom = yoneda.map kk ≫ Vj.obj.hom := by
    rw [Category.assoc, (relativelyRepresentable_specPointOver B S hS T x).w W.obj.hom,
      ← Functor.map_comp_assoc, ← hk₂, Functor.map_comp_assoc, Functor.map_comp_assoc,
      CostructuredArrow.w p₂.hom, CostructuredArrow.w κ.hom]
  obtain ⟨c, hc₁, hc₂⟩ : ∃ c : T'' ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback
      Vj.obj.hom, yoneda.map c ≫ (relativelyRepresentable_specPointOver B S hS T x).fst Vj.obj.hom =
        yoneda.map k ≫ (relativelyRepresentable_specPointOver B S hS T x).fst W.obj.hom ∧
      c ≫ (relativelyRepresentable_specPointOver B S hS T x).snd Vj.obj.hom = kk :=
    ⟨_, Functor.relativelyRepresentable.lift_fst _ _ _ hc,
      Functor.relativelyRepresentable.lift_snd _ _ _ hc⟩
  have hcond₂ := fst_comp_eq_snd_comp_chart B S hS (κ ≫ p₂) x
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a : (relativelyRepresentable_specPointOver B S hS T x).pullback
      Vj.obj.hom ⟶ (relativelyRepresentable_specPointOver B S hS T x).pullback W.obj.hom,
      yoneda.map a ≫ (relativelyRepresentable_specPointOver B S hS T x).fst W.obj.hom =
        (relativelyRepresentable_specPointOver B S hS T x).fst Vj.obj.hom ∧
      a ≫ (relativelyRepresentable_specPointOver B S hS T x).snd W.obj.hom =
        (relativelyRepresentable_specPointOver B S hS T x).snd Vj.obj.hom ≫ (κ ≫ p₂).hom.left :=
    ⟨_, Functor.relativelyRepresentable.lift_fst _ _ _ hcond₂,
      Functor.relativelyRepresentable.lift_snd _ _ _ hcond₂⟩
  have hca : c ≫ a = k := by
    refine (relativelyRepresentable_specPointOver B S hS T x).hom_ext ?_ ?_
    · rw [Functor.map_comp, Category.assoc, ha₁, hc₁]
    · rw [Category.assoc, ha₂, ← Category.assoc, hc₂]
      exact hk₂
  have step : ∀ β : A ⟶ pushforwardAlgebra B S hS (specPointOver B S hS T x),
      ((BigFppfOver.toScheme B S hS).map k).appTop
          ((pointSectionsIso B S hS T x W).hom (β.right.hom.app (op W) s)) =
        ((BigFppfOver.toScheme B S hS).map c).appTop ((pointSectionsIso B S hS T x Vj).hom
          (β.right.hom.app (op Vj) (A.right.obj.map (κ ≫ p₂).op s))) := by
    intro β
    have e₁ := ConcreteCategory.congr_hom (appTop_map_comp_appTop_map B S hS c a)
      ((pointSectionsIso B S hS T x W).hom (β.right.hom.app (op W) s))
    rw [hca, ConcreteCategory.comp_apply] at e₁
    rw [← e₁]
    refine congrArg _ ?_
    have e₂ := ConcreteCategory.congr_hom (map_comp_pointSectionsIso B S hS x (κ ≫ p₂) a ha₁ ha₂)
      (β.right.hom.app (op W) s)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e₂
    rw [← e₂]
    refine congrArg _ ?_
    exact (hom_app_map_restrict B S hS (κ ≫ p₂) β s).symm
  rw [step α, step α']
  refine appTop_pointSectionsIso_eq_of_chartEval_eq B S hS hA hV hVj (κ ≫ p₁) v x hxv h c
    (k ≫ (relativelyRepresentable_specPointOver B S hS T x).fst' W.obj.hom) ?_ ?_ _
  · rw [hc₁, Functor.map_comp, Functor.relativelyRepresentable.map_fst']
  · rw [← Category.assoc, hc₂, Category.assoc]
    exact hk₁

end AlgebraicGeometry.Space

end
