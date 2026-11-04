module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectOpenPart

/-!
# Formal objects of Artin's contraction functor: the reduction to two inputs

In the situation of Stacks 0GH8 let `F` be Artin's contraction functor of Stacks 0GHA and
`ξ = (R, ξ_n)` a formal object of `F`. By
`AlgebraicGeometry.Artin.ContractionSituation.formalObject_Z_eq_empty_or_eq_univ` it is a formal
object of `U'` or of `W`, and in the first case it is effective
(`AlgebraicGeometry.Artin.ContractionSituation.exists_effective_of_Z_eq_empty`). The proof of
Stacks 0GI8 treats the second case in two steps, and this file splits it accordingly.

1. *Algebraization along the reduction.* The elements `ξ_n` are morphisms
   `Spec(R/𝔪ⁿ⁺¹) ⟶ W`, that is a morphism `Spf R ⟶ W`, which need not be adic. With `I ⊆ R` the
   ideal of `Spf R ×_W W_red` and `Z = V(I)`, the restrictions to `Spf(R/Iᵏ)` algebraize to
   morphisms `Spec(R/Iᵏ) ⟶ W`, giving an adic `x̂ : V_{/Z} ⟶ W` for `V = Spec R`. This step
   concerns `W` only; its statement is
   `AlgebraicGeometry.FormalSpace.HasAdicAlgebraizationOfFormalObjects`.
2. *Compatibility.* For an adic `x̂ : V_{/Z} ⟶ W` with `Z` containing the closed point, the base
   change of `g` along `x̂` is a formal modification (Stacks 0GDN), hence by Stacks 0GDU the
   completion of a proper `V' ⟶ V` that is an isomorphism over `V ∖ Z`; Grothendieck's
   algebraization theorem (Stacks 0A4Z, using that `X'` is separated) gives `x' : V' ⟶ X'`, and
   its restriction to `V ∖ Z` is `u'`. Its statement is
   `AlgebraicGeometry.Artin.ContractionSituation.HasCompatibilityOverCompleteLocalBase`.

The triple `(Z, u', x̂)` then restricts to `ξ_n` on every thickening, since on the one-point
scheme `Spec(R/𝔪ⁿ⁺¹)` a triple with `Z = |Spec(R/𝔪ⁿ⁺¹)|` is determined by `x̂`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAdicAlgebraizationOfFormalObjects`: step 1.
* `AlgebraicGeometry.Artin.ContractionSituation.HasCompatibilityOverCompleteLocalBase`: step 2.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.hasEffectiveFormalObjects_of`: the two steps
  give Artin's axiom `[4]` for `F`.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

open LocallyNoetherianOver Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- The section of the completion `V_{/Z}` over the `n`-th thickening of a complete local base
`V = Spec R` given by the closed immersion `Spec(R/𝔪ⁿ⁺¹) ⟶ Spec R`, when `Z` contains its
image. -/
def FormalSpace.thickeningSection (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (Z : Set (Space.points B S hS
      (yoneda.obj (baseOver B S hS A (A.contains_spec_of_contains_truncation hA)))))
    (n : ℕ) (hZ : Space.HasImageIn B S hS _ Z (truncationOver B S hS A hA n)
      (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA n)) :
    (Space.completionSheaf B S hS _ Z).obj.obj (op (truncationOver B S hS A hA n)) :=
  ((BigFppfOver.topology B S hS).toSheafify
    (Space.completionSubfunctor B S hS _ Z).toFunctor).app (op _)
      ⟨ULift.up (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA n), hZ⟩

/-- **Algebraization of a formal object along the reduction** (the first step of the proof of
Stacks 0GI8). For every Noetherian complete local `S`-algebra `R` with residue field of finite
type over `S` and every compatible family `w_n ∈ W(Spec(R/𝔪ⁿ⁺¹))`, there are a closed subset
`Z ⊆ |Spec R|` containing the images of all thickenings and an adic morphism
`x̂ : (Spec R)_{/Z} ⟶ W` restricting to `w_n` on the `n`-th thickening. -/
def FormalSpace.HasAdicAlgebraizationOfFormalObjects (W : FormalSpace.FppfSheaf B S hS) :
    Prop :=
  ∀ (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (w : ∀ n, W.obj.obj (op (truncationOver B S hS A hA n))),
    (∀ n, W.obj.map (truncationOverSucc B S hS A hA n).op (w (n + 1)) = w n) →
    ∃ (Z : Set (Space.points B S hS
        (yoneda.obj (baseOver B S hS A (A.contains_spec_of_contains_truncation hA)))))
      (_ : IsClosed Z)
      (hZ : ∀ n, Space.HasImageIn B S hS _ Z (truncationOver B S hS A hA n)
        (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA n))
      (x : Space.completionSheaf B S hS _ Z ⟶ W),
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS x.hom ∧
        ∀ n, x.hom.app (op _) (FormalSpace.thickeningSection A hA Z n (hZ n)) = w n

namespace Artin.ContractionSituation

variable (c : ContractionSituation B S hS)

/-- **Compatibility over a complete local base** (the second step of the proof of Stacks 0GI8).
For every Noetherian complete local `S`-algebra `R` with residue field of finite type over `S`,
every closed `Z ⊆ |Spec R|` containing the closed point and every adic `x̂ : (Spec R)_{/Z} ⟶ W`
there is `u' : Spec R ∖ Z ⟶ U'` compatible with `x̂`. -/
def HasCompatibilityOverCompleteLocalBase : Prop :=
  ∀ (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (Z : Set (Space.points B S hS
      (yoneda.obj (baseOver B S hS A (A.contains_spec_of_contains_truncation hA))))),
    IsClosed Z →
    Space.HasImageIn B S hS _ Z (truncationOver B S hS A hA 0)
      (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA 0) →
    ∀ x : Space.completionSheaf B S hS _ Z ⟶ c.W,
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS x.hom →
      ∃ u, Nonempty (CompatibilityWitness c _ Z u x)

/-- The third component of a triple with closed subset everything is invariant under equality
of triples. -/
theorem Triple.xhatValue_congr {V : BigFppfOver B S hS} {t t' : Triple c V} (e : t = t')
    (h : t.Z = Set.univ) (h' : t'.Z = Set.univ) : t.xhatValue h = t'.xhatValue h' := by
  subst e
  rfl

/-- The restriction of a triple `(Z, u', x̂)` over `V` along `φ : V₂ ⟶ V₁` whose image lies in
`Z` has third component the value of `x̂` on the section `φ` of `V_{/Z}`. -/
theorem Triple.xhatValue_mapTriple_of_hasImageIn {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁)
    (t : Triple c V₁) (hφ : Space.HasImageIn B S hS _ t.Z V₂ φ)
    (h' : (mapTriple c φ t).Z = Set.univ) :
    (mapTriple c φ t).xhatValue h' = t.xhat.hom.app (op V₂)
      (((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS _ t.Z).toFunctor).app (op V₂) ⟨ULift.up φ, hφ⟩) := by
  let G₁ := (Space.completionSubfunctor B S hS (yoneda.obj V₁) t.Z).toFunctor
  let G₂ := (Space.completionSubfunctor B S hS (yoneda.obj V₂) (mapTriple c φ t).Z).toFunctor
  let e₂ : G₂.obj (op V₂) := ⟨ULift.up (𝟙 V₂), (mapTriple c φ t).hasImageIn_id h'⟩
  let ρ : G₂ ⟶ G₁ := Space.completionSubfunctorRestrict B S hS (yoneda.map φ) _ t.Z
    (fun _ hz => hz)
  have e : ρ.app (op V₂) e₂ = ⟨ULift.up φ, hφ⟩ := by
    apply Subtype.ext
    apply ULift.ext
    show 𝟙 V₂ ≫ φ = φ
    rw [Category.id_comp]
  let ι₁ : G₁ ⟶ (Space.completionSheaf B S hS (yoneda.obj V₁) t.Z).obj :=
    (BigFppfOver.topology B S hS).toSheafify G₁
  let ι₂ : G₂ ⟶ (Space.completionSheaf B S hS (yoneda.obj V₂) (mapTriple c φ t).Z).obj :=
    (BigFppfOver.topology B S hS).toSheafify G₂
  let r : Space.completionSheaf B S hS (yoneda.obj V₂) (mapTriple c φ t).Z ⟶
      Space.completionSheaf B S hS (yoneda.obj V₁) t.Z :=
    Space.completionSheafRestrict B S hS (yoneda.map φ) _ t.Z (fun _ hz => hz)
  have hr : ι₂ ≫ r.hom = ρ ≫ ι₁ := (GrothendieckTopology.toSheafify_naturality _ ρ).symm
  have h1 : ι₂ ≫ (r ≫ t.xhat).hom = ρ ≫ ι₁ ≫ t.xhat.hom := by
    show ι₂ ≫ r.hom ≫ t.xhat.hom = _
    rw [← Category.assoc, hr, Category.assoc]
  refine (congrArg (fun η : G₂ ⟶ c.W.obj => η.app (op V₂) e₂) h1).trans ?_
  show t.xhat.hom.app (op V₂) (ι₁.app (op V₂) (ρ.app (op V₂) e₂)) = _
  rw [e]
  rfl

/-- **Stacks 0GI8, assembled from its two steps.** If formal objects of `W` algebraize along
the reduction and compatibility holds over complete local bases, then every formal object of
Artin's functor `F` is effective. -/
theorem hasEffectiveFormalObjects_of
    (h₁ : FormalSpace.HasAdicAlgebraizationOfFormalObjects c.W)
    (h₂ : c.HasCompatibilityOverCompleteLocalBase) :
    HasEffectiveFormalObjects B S hS (contractionFunctor c) := by
  intro A hA ξ hξ
  rcases c.formalObject_Z_eq_empty_or_eq_univ A hA ξ hξ with h | h
  · exact c.exists_effective_of_Z_eq_empty A hA ξ hξ h
  set hRS := A.contains_spec_of_contains_truncation hA
  let w : ∀ n, c.W.obj.obj (op (truncationOver B S hS A hA n)) := fun n => (ξ n).xhatValue (h n)
  have hw : ∀ n, c.W.obj.map (truncationOverSucc B S hS A hA n).op (w (n + 1)) = w n := by
    intro n
    have h' : (mapTriple c (truncationOverSucc B S hS A hA n) (ξ (n + 1))).Z = Set.univ :=
      (congrArg Triple.Z (hξ n)).trans (h n)
    exact (Triple.xhatValue_mapTriple _ (ξ (n + 1)) (h (n + 1)) h').symm.trans
      (Triple.xhatValue_congr c (hξ n) h' (h n))
  obtain ⟨Z, hZc, hZ, x, hx, hxw⟩ := h₁ A hA w hw
  obtain ⟨u, hu⟩ := h₂ A hA Z hZc (hZ 0) x hx
  let t : Triple c (baseOver B S hS A hRS) := ⟨Z, hZc, u, x, hx, hu⟩
  refine ⟨t, fun n => ?_⟩
  show mapTriple c (restrictionToBase B S hS A hRS hA n) t = ξ n
  have h' : (mapTriple c (restrictionToBase B S hS A hRS hA n) t).Z = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨p, rfl⟩ := Quot.exists_rep q
    exact hZ n p
  exact Triple.ext_of_Z_eq_univ h' (h n)
    ((Triple.xhatValue_mapTriple_of_hasImageIn c _ t (hZ n) h').trans (hxw n))

end Artin.ContractionSituation

end AlgebraicGeometry

end
