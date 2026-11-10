module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalPushforwardRational
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# Functoriality of the equidimensional pushforward

For smooth projective schemes `X`, `Y` over `k` equidimensional of dimensions `d` and `e`, the
pushforward `f_* : CH^p(X) ⟶ CH^q(Y)`, `q = p + e - d`
(`Stacks.WeilCohomology.equidimensionalPushforward`), is proper pushforward
`CH_{d-p}(X) ⟶ CH_{d-p}(Y)` read through `CH^p(X) = CH_{d-p}(X_d)` and `CH^q(Y) = CH_{e-q}(Y_e)`.

## Main results

* `Stacks.WeilCohomology.equidimensionalPushforward_comp`: `(f ≫ g)_* = g_* ∘ f_*`.
* `Stacks.WeilCohomology.equidimensionalPushforward_surjective`: `f_*` is surjective as soon as
  proper pushforward `CH_{d-p}(X) ⟶ CH_{d-p}(Y)` along `f` is.

## References

* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### Restriction along an isomorphism -/

section Restriction

variable (C : ChowSituation.{u}) {A B U : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]

/-- **Restriction along an isomorphism after a proper pushforward is a proper pushforward.** For
a proper `φ : A ⟶ B` and an isomorphism `j : U ⟶ B` over the base, restricting `φ_*a` along `j`
is pushing `a` forward along `φ ≫ j⁻¹`. -/
theorem chowGroupRestrict_properChowPushforward_of_isIso (φ : A ⟶ B) [IsProper φ]
    (hφ : φ ≫ sB = sA) (j : U ⟶ B) [IsIso j] (hj : j ≫ sB = sU) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB φ hφ k)
    (a : chowGroup C sA k) :
    chowGroupRestrict C sB sU j hj k (properChowPushforward C sA sB φ hφ k hfac a) =
      properChowPushforward C sA sU (φ ≫ inv j)
        (by rw [Category.assoc, ← hj, IsIso.inv_hom_id_assoc, hφ]) k
        (properPushforwardDescends C _ _ _ _ k) a := by
  rw [chowGroupRestrict_of_isIso]
  exact (properChowPushforward_comp_apply C sA sB sU φ (inv j) (φ ≫ inv j) rfl hφ _ _ k hfac
    (properPushforwardDescends C _ _ _ _ k) _ a).symm

/-- **Pushing forward along an isomorphism undoes restriction along it.** For an isomorphism
`j : U ⟶ B` over the base, `j_*(x|_U) = x`. -/
theorem properChowPushforward_chowGroupRestrict_of_isIso (j : U ⟶ B) [IsIso j]
    (hj : j ≫ sB = sU) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sU sB j hj k)
    (x : chowGroup C sB k) :
    properChowPushforward C sU sB j hj k hfac (chowGroupRestrict C sB sU j hj k x) = x := by
  rw [chowGroupRestrict_of_isIso, properChowPushforward_eq_chowPushforwardOfIso,
    chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C sB sB _ (𝟙 B) (IsIso.inv_hom_id j) _
      (Category.id_comp sB), chowPushforwardOfIso_id]

end Restriction

variable {k : Type u} [Field k]

/-- The inclusion of the part of a given dimension of a smooth morphism is proper. -/
private instance isProper_dimPart_ι {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX] (d : ℕ) :
    IsProper (dimPart sX d).ι :=
  (isClopenDecomposition_dimPart sX).isProper_ι d

/-! ### Functoriality -/

/-- **Functoriality of the equidimensional pushforward, `(f ≫ g)_* = g_* ∘ f_*`.** For
`f : X ⟶ Y` and `g : Y ⟶ Z` of smooth projective schemes over `k`, with `Y` of relative
dimension `e`, pushing forward `CH^p(X) ⟶ CH^q(Y) ⟶ CH^r(Z)` is pushing forward along
`f ≫ g`. -/
theorem equidimensionalPushforward_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) {d e c : ℕ} (hY : RelativeDimension Y.obj.hom e) (p q r : ℤ)
    (hq : q = p + e - d) (hr : r = q + c - e) (α : codimensionChowGroup k X.obj.hom p) :
    equidimensionalPushforward g e c q r hr (equidimensionalPushforward f d e p q hq α) =
      equidimensionalPushforward (f ≫ g) d c p r (by omega) α := by
  funext c'
  by_cases hc : c' = c
  · subst hc
    have := isIso_dimPart_self_ι Y.obj.hom hY
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply]
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm))
    refine chowGroupRestrict_heq_of_eq _ _ _ rfl rfl rfl _ _ (by omega) _ _ ?_
    simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, AddMonoidHom.pi_apply]
    refine (properChowPushforward_heq_congr _ _ _ _ _ (by omega) _
      (properPushforwardDescends _ _ _ _ _ _) _ _ (chowGroupDegreeEquiv_heq _ _ _ _)).trans
      (heq_of_eq ?_)
    refine (DFunLike.congr_arg (properChowPushforward (fieldChowSituation k) (partBase Y.obj.hom e)
      Z.obj.hom ((dimPart Y.obj.hom e).ι ≫ g.hom.left) (by rw [Category.assoc, Over.w g.hom])
      ((d : ℤ) - p) (properPushforwardDescends _ _ _ _ _ _))
      (chowGroupRestrict_properChowPushforward_of_isIso (fieldChowSituation k)
        (partBase X.obj.hom d) Y.obj.hom (partBase Y.obj.hom e)
        ((dimPart X.obj.hom d).ι ≫ f.hom.left) (by rw [Category.assoc, Over.w f.hom])
        (dimPart Y.obj.hom e).ι rfl ((d : ℤ) - p) (properPushforwardDescends _ _ _ _ _ _)
        (α d))).trans ?_
    exact (properChowPushforward_comp_apply (fieldChowSituation k) (partBase X.obj.hom d)
      (partBase Y.obj.hom e) Z.obj.hom
      (((dimPart X.obj.hom d).ι ≫ f.hom.left) ≫ inv (dimPart Y.obj.hom e).ι)
      ((dimPart Y.obj.hom e).ι ≫ g.hom.left) ((dimPart X.obj.hom d).ι ≫ (f ≫ g).hom.left)
      (by simp) _ _ _ _ _ _ _ _).symm
  · simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, dite_eq_right hc,
      AddMonoidHom.zero_apply]

/-! ### Surjectivity -/

/-- **Surjectivity of the equidimensional pushforward.** For `X`, `Y` of relative dimensions `d`
and `e` and `q = p + e - d`, if proper pushforward `CH_{d-p}(X) ⟶ CH_{d-p}(Y)` along `f` is
surjective, so is `f_* : CH^p(X) ⟶ CH^q(Y)`. -/
theorem equidimensionalPushforward_surjective {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y)
    {d e : ℕ} (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)
    (p q : ℤ) (h : q = p + e - d)
    (hf : Function.Surjective (properChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom
      f.hom.left (Over.w f.hom) ((d : ℤ) - p)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _))) :
    Function.Surjective (equidimensionalPushforward f d e p q h) := by
  have := isIso_dimPart_self_ι X.obj.hom hX
  have := isIso_dimPart_self_ι Y.obj.hom hY
  intro β
  obtain ⟨x, hx⟩ := hf (properChowPushforward (fieldChowSituation k) (partBase Y.obj.hom e)
    Y.obj.hom (dimPart Y.obj.hom e).ι rfl ((d : ℤ) - p) (properPushforwardDescends _ _ _ _ _ _)
    (chowGroupDegreeEquiv _ _ (by omega : (e : ℤ) - q = d - p) (β e)))
  refine ⟨Pi.single d (chowGroupRestrict (fieldChowSituation k) X.obj.hom (partBase X.obj.hom d)
    (dimPart X.obj.hom d).ι rfl ((d : ℤ) - p) x), funext fun e' ↦ ?_⟩
  by_cases he : e' = e
  · subst he
    have key : chowGroupRestrict (fieldChowSituation k) Y.obj.hom (partBase Y.obj.hom e')
        (dimPart Y.obj.hom e').ι rfl ((d : ℤ) - p)
        (properChowPushforward (fieldChowSituation k) (partBase X.obj.hom d) Y.obj.hom
          ((dimPart X.obj.hom d).ι ≫ f.hom.left) (by rw [Category.assoc, Over.w f.hom])
          ((d : ℤ) - p) (properPushforwardDescends _ _ _ _ _ _)
          (Pi.single (M := fun d' : ℕ ↦ chowGroup (fieldChowSituation k) (partBase X.obj.hom d')
            (d' - p)) d (chowGroupRestrict (fieldChowSituation k) X.obj.hom (partBase X.obj.hom d)
            (dimPart X.obj.hom d).ι rfl ((d : ℤ) - p) x) d)) =
        chowGroupDegreeEquiv _ _ (by omega : (e' : ℤ) - q = d - p) (β e') := by
      rw [Pi.single_eq_same,
        properChowPushforward_comp_apply (fieldChowSituation k) (partBase X.obj.hom d)
          X.obj.hom Y.obj.hom (dimPart X.obj.hom d).ι f.hom.left _ rfl rfl (Over.w f.hom) _
          ((d : ℤ) - p) (properPushforwardDescends _ _ _ _ _ _)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _),
        properChowPushforward_chowGroupRestrict_of_isIso, hx,
        chowGroupRestrict_properChowPushforward_self]
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply]
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      ((heq_of_eq key).trans (chowGroupDegreeEquiv_heq _ _ _ _)))
  · have := isEmpty_dimPart_of_ne Y.obj.hom hY he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

end Stacks.WeilCohomology

end
