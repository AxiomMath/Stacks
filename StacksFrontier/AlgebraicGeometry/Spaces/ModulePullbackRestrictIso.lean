module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Restricting an isomorphism of inverse images along a further morphism

Let `M` be a module on an algebraic space `A`, `N` a module on an algebraic space `A'`, and
`u : Z ⟶ A`, `v : Z ⟶ A'` two morphisms out of one algebraic space.  An isomorphism
`γ : u^*M ≅ v^*N` of inverse images can be pulled back along a morphism `t : Z₂ ⟶ Z`, and read
through the comparisons `(t ≫ u)^* ≅ t^* ∘ u^*` of Stacks 03LU it becomes an isomorphism
`(t ≫ u)^*M ≅ (t ≫ v)^*N`.  This file records that restriction and its calculus.

The point of the construction is that it only ever produces inverse images along *single*
morphisms: the iterated inverse images, and the comparisons between them, are confined to its
definition.  Every coherence a consumer needs then follows from the three laws proved here —
restriction is compatible with composition and inversion of isomorphisms, and restricting twice
is restricting along the composite — the last being the associativity coherence of the
comparisons of Stacks 03LU, which is unconditional.

The target morphisms `t ≫ u` and `t ≫ v` are taken as arbitrary morphisms `u₂`, `v₂` together
with equations `t ≫ u = u₂`, `t ≫ v = v₂`, so that a restriction can be taken at a morphism that
merely *equals* a composite without first rewriting.

## Main definitions

* `AlgebraicGeometry.Space.restrictPullbackIso`: the restriction of `γ : u^*M ≅ v^*N` along
  `t : Z₂ ⟶ Z`.

## Main results

* `AlgebraicGeometry.Space.restrictPullbackIso_trans` and
  `AlgebraicGeometry.Space.restrictPullbackIso_symm`: restriction is compatible with composition
  and inversion of isomorphisms.
* `AlgebraicGeometry.Space.restrictPullbackIso_restrictPullbackIso`: restricting along `t` and
  then along `t₂` is restricting along `t₂ ≫ t`.
* `AlgebraicGeometry.Space.restrictPullbackIso_eqToIso`: the restriction of the identification
  of the inverse images along two equal morphisms is the identification of the restrictions.
* `AlgebraicGeometry.Space.restrictPullbackIso_mapIso`: restricting the inverse image of an
  isomorphism of modules is taking the inverse image along the composite.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A A' A'' Z Z₂ Z₃ : AlgebraicSpaces B S hS}

/-- **The restriction of an isomorphism of inverse images along a further morphism.**  For
`γ : u^*M ≅ v^*N` and `t : Z₂ ⟶ Z` with `t ≫ u = u₂` and `t ≫ v = v₂`, the inverse image of `γ`
along `t`, read through the comparisons of Stacks 03LU, as an isomorphism `u₂^*M ≅ v₂^*N`. -/
def restrictPullbackIso {M : Modules.{u, u} B S hS A.1 A.2} {N : Modules.{u, u} B S hS A'.1 A'.2}
    {u : Z ⟶ A} {v : Z ⟶ A'} (t : Z₂ ⟶ Z) {u₂ : Z₂ ⟶ A} {v₂ : Z₂ ⟶ A'} (hu : t ≫ u = u₂)
    (hv : t ≫ v = v₂)
    (γ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N) :
    (modulePullback B S hS u₂).obj M ≅ (modulePullback B S hS v₂).obj N :=
  (modulePullbackTriangle B S hS hu).app M ≪≫ (modulePullback B S hS t).mapIso γ ≪≫
    ((modulePullbackTriangle B S hS hv).app N).symm

/-- The forward map of `restrictPullbackIso t hu hv γ` is the comparison `u₂^*M ≅ t^*(u^*M)`,
followed by `t^*γ`, followed by the inverse comparison `t^*(v^*N) ≅ v₂^*N`. -/
theorem restrictPullbackIso_hom {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS A'.1 A'.2} {u : Z ⟶ A} {v : Z ⟶ A'} (t : Z₂ ⟶ Z)
    {u₂ : Z₂ ⟶ A} {v₂ : Z₂ ⟶ A'} (hu : t ≫ u = u₂) (hv : t ≫ v = v₂)
    (γ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N) :
    (restrictPullbackIso t hu hv γ).hom =
      (modulePullbackTriangle B S hS hu).hom.app M ≫ (modulePullback B S hS t).map γ.hom ≫
        (modulePullbackTriangle B S hS hv).inv.app N :=
  rfl

/-- **Restriction is compatible with composition of isomorphisms.** -/
theorem restrictPullbackIso_trans {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS A'.1 A'.2} {P : Modules.{u, u} B S hS A''.1 A''.2}
    {u : Z ⟶ A} {v : Z ⟶ A'} {w : Z ⟶ A''} (t : Z₂ ⟶ Z) {u₂ : Z₂ ⟶ A} {v₂ : Z₂ ⟶ A'}
    {w₂ : Z₂ ⟶ A''} (hu : t ≫ u = u₂) (hv : t ≫ v = v₂) (hw : t ≫ w = w₂)
    (γ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N)
    (δ : (modulePullback B S hS v).obj N ≅ (modulePullback B S hS w).obj P) :
    restrictPullbackIso t hu hw (γ ≪≫ δ) =
      restrictPullbackIso t hu hv γ ≪≫ restrictPullbackIso t hv hw δ := by
  simp only [restrictPullbackIso, Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- **Restriction is compatible with inversion of isomorphisms.** -/
theorem restrictPullbackIso_symm {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS A'.1 A'.2} {u : Z ⟶ A} {v : Z ⟶ A'} (t : Z₂ ⟶ Z)
    {u₂ : Z₂ ⟶ A} {v₂ : Z₂ ⟶ A'} (hu : t ≫ u = u₂) (hv : t ≫ v = v₂)
    (γ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N) :
    restrictPullbackIso t hv hu γ.symm = (restrictPullbackIso t hu hv γ).symm := by
  simp only [restrictPullbackIso, Functor.mapIso_symm, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc]

/-- The restriction of the identity is the identity. -/
@[simp]
theorem restrictPullbackIso_refl {M : Modules.{u, u} B S hS A.1 A.2} {u : Z ⟶ A}
    (t : Z₂ ⟶ Z) {u₂ : Z₂ ⟶ A} (hu : t ≫ u = u₂) :
    restrictPullbackIso t hu hu (Iso.refl ((modulePullback B S hS u).obj M)) = Iso.refl _ := by
  ext
  simp [restrictPullbackIso_hom]

/-- The restriction does not depend on the proofs of the two equations, nor on the
presentation of the restricting morphism. -/
theorem restrictPullbackIso_congr {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS A'.1 A'.2} {u : Z ⟶ A} {v : Z ⟶ A'} {t t' : Z₂ ⟶ Z}
    (htt : t = t') {u₂ : Z₂ ⟶ A} {v₂ : Z₂ ⟶ A'} (hu : t ≫ u = u₂) (hv : t ≫ v = v₂)
    (hu' : t' ≫ u = u₂) (hv' : t' ≫ v = v₂)
    (γ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N) :
    restrictPullbackIso t hu hv γ = restrictPullbackIso t' hu' hv' γ := by
  subst htt
  rfl

/-- The associativity coherence of the comparisons of Stacks 03LU, as an equation of isomorphisms
of modules. -/
private theorem modulePullbackTriangle_app_trans_mapIso {Y : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A.1 A.2} {b : Y ⟶ A} {a : Z ⟶ Y} {c : Z ⟶ A} (h : a ≫ b = c)
    (t : Z₂ ⟶ Z) {c₂ : Z₂ ⟶ A} {a₂ : Z₂ ⟶ Y} (hc : t ≫ c = c₂) (ha : t ≫ a = a₂)
    (h₂ : a₂ ≫ b = c₂) :
    (modulePullbackTriangle B S hS hc).app M ≪≫
      (modulePullback B S hS t).mapIso ((modulePullbackTriangle B S hS h).app M) =
      (modulePullbackTriangle B S hS h₂).app M ≪≫
        (modulePullbackTriangle B S hS ha).app ((modulePullback B S hS b).obj M) := by
  rw [← Iso.symm_eq_iff]
  exact Iso.ext (modulePullbackTriangle_inv_app_assoc B S hS ha h hc h₂ M)

/-- **Restricting twice is restricting along the composite.**  This is the associativity
coherence of the comparisons of Stacks 03LU. -/
theorem restrictPullbackIso_restrictPullbackIso {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS A'.1 A'.2} {u : Z ⟶ A} {v : Z ⟶ A'} (t : Z₂ ⟶ Z)
    {u₂ : Z₂ ⟶ A} {v₂ : Z₂ ⟶ A'} (hu : t ≫ u = u₂) (hv : t ≫ v = v₂) (t₂ : Z₃ ⟶ Z₂)
    {u₃ : Z₃ ⟶ A} {v₃ : Z₃ ⟶ A'} (hu₂ : t₂ ≫ u₂ = u₃) (hv₂ : t₂ ≫ v₂ = v₃)
    (γ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N) :
    restrictPullbackIso t₂ hu₂ hv₂ (restrictPullbackIso t hu hv γ) =
      restrictPullbackIso (t₂ ≫ t) (by rw [Category.assoc, hu, hu₂])
        (by rw [Category.assoc, hv, hv₂]) γ := by
  have hu₃ : (t₂ ≫ t) ≫ u = u₃ := by rw [Category.assoc, hu, hu₂]
  have hv₃ : (t₂ ≫ t) ≫ v = v₃ := by rw [Category.assoc, hv, hv₂]
  have hM := modulePullbackTriangle_app_trans_mapIso (M := M) hu (t₂) hu₂
    (rfl : t₂ ≫ t = t₂ ≫ t) hu₃
  have hN : (modulePullback B S hS t₂).mapIso ((modulePullbackTriangle B S hS hv).app N).symm ≪≫
      ((modulePullbackTriangle B S hS hv₂).app N).symm =
      ((modulePullbackTriangle B S hS (rfl : t₂ ≫ t = t₂ ≫ t)).app
          ((modulePullback B S hS v).obj N)).symm ≪≫
        ((modulePullbackTriangle B S hS hv₃).app N).symm :=
    Iso.ext (modulePullbackTriangle_inv_app_assoc B S hS rfl hv hv₂ hv₃ N)
  have hnat : (modulePullbackTriangle B S hS (rfl : t₂ ≫ t = t₂ ≫ t)).app
        ((modulePullback B S hS u).obj M) ≪≫
      (modulePullback B S hS t₂).mapIso ((modulePullback B S hS t).mapIso γ) ≪≫
      ((modulePullbackTriangle B S hS (rfl : t₂ ≫ t = t₂ ≫ t)).app
          ((modulePullback B S hS v).obj N)).symm =
      (modulePullback B S hS (t₂ ≫ t)).mapIso γ :=
    Iso.ext (NatIso.naturality_2 (modulePullbackTriangle B S hS (rfl : t₂ ≫ t = t₂ ≫ t)) γ.hom)
  simp only [restrictPullbackIso, Functor.mapIso_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc, hM, Iso.trans_assoc, hN]
  rw [← Iso.trans_assoc ((modulePullback B S hS t₂).mapIso ((modulePullback B S hS t).mapIso γ)),
    ← Iso.trans_assoc ((modulePullbackTriangle B S hS (rfl : t₂ ≫ t = t₂ ≫ t)).app
        ((modulePullback B S hS u).obj M)), hnat]

/-- **Restrictions along two factorisations of one morphism agree.**  If `t ≫ o = w ≫ k`, then
restricting along `o` and then `t` is restricting along `k` and then `w`. -/
theorem restrictPullbackIso_restrictPullbackIso_eq {Q W : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A.1 A.2} {N : Modules.{u, u} B S hS A'.1 A'.2}
    {u : Q ⟶ A} {v : Q ⟶ A'} (o : Z ⟶ Q) {u₂ : Z ⟶ A} {v₂ : Z ⟶ A'} (ho₀ : o ≫ u = u₂)
    (ho₁ : o ≫ v = v₂) (t : Z₂ ⟶ Z) {u₃ : Z₂ ⟶ A} {v₃ : Z₂ ⟶ A'} (ht₀ : t ≫ u₂ = u₃)
    (ht₁ : t ≫ v₂ = v₃) (w : Z₂ ⟶ W) (k : W ⟶ Q) (e : t ≫ o = w ≫ k) {u₄ : W ⟶ A}
    {v₄ : W ⟶ A'} (hk₀ : k ≫ u = u₄) (hk₁ : k ≫ v = v₄) (hw₀ : w ≫ u₄ = u₃)
    (hw₁ : w ≫ v₄ = v₃)
    (γ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N) :
    restrictPullbackIso t ht₀ ht₁ (restrictPullbackIso o ho₀ ho₁ γ) =
      restrictPullbackIso w hw₀ hw₁ (restrictPullbackIso k hk₀ hk₁ γ) := by
  rw [restrictPullbackIso_restrictPullbackIso, restrictPullbackIso_restrictPullbackIso]
  exact restrictPullbackIso_congr e _ _ _ _ γ

/-- The restriction of the identification of the inverse images of one module along two equal
morphisms is the identification of the inverse images along their restrictions. -/
theorem restrictPullbackIso_eqToIso {M : Modules.{u, u} B S hS A.1 A.2} {u v : Z ⟶ A}
    (e : u = v) (t : Z₂ ⟶ Z) {u₂ v₂ : Z₂ ⟶ A} (hu : t ≫ u = u₂) (hv : t ≫ v = v₂) :
    restrictPullbackIso t hu hv
        (eqToIso (congrArg (fun w : Z ⟶ A ↦ (modulePullback B S hS w).obj M) e)) =
      eqToIso (congrArg (fun w : Z₂ ⟶ A ↦ (modulePullback B S hS w).obj M)
        (hu.symm.trans ((congrArg (t ≫ ·) e).trans hv))) := by
  subst e hu hv
  ext
  simp

/-- Restricting the inverse image of an isomorphism of modules is taking its inverse image along
the composite. -/
theorem restrictPullbackIso_mapIso {M N : Modules.{u, u} B S hS A.1 A.2} {u : Z ⟶ A}
    (t : Z₂ ⟶ Z) {u₂ : Z₂ ⟶ A} (hu : t ≫ u = u₂) (ε : M ≅ N) :
    restrictPullbackIso t hu hu ((modulePullback B S hS u).mapIso ε) =
      (modulePullback B S hS u₂).mapIso ε :=
  Iso.ext (NatIso.naturality_2 (modulePullbackTriangle B S hS hu) ε.hom)

/-- **The restriction of a comparison of Stacks 03LU is a comparison.**  For `a ≫ b = c` the
comparison `c^*M ≅ a^*(b^*M)`, restricted along `t`, is the comparison for `(t ≫ a) ≫ b = t ≫ c`.
This is the associativity coherence of Stacks 03LU. -/
theorem restrictPullbackIso_triangle {Y : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS A.1 A.2} {b : Y ⟶ A} {a : Z ⟶ Y} {c : Z ⟶ A} (h : a ≫ b = c)
    (t : Z₂ ⟶ Z) {c₂ : Z₂ ⟶ A} {a₂ : Z₂ ⟶ Y} (hc : t ≫ c = c₂) (ha : t ≫ a = a₂) :
    restrictPullbackIso t hc ha ((modulePullbackTriangle B S hS h).app M) =
      (modulePullbackTriangle B S hS
        (by rw [← ha, Category.assoc, h, hc] : a₂ ≫ b = c₂)).app M := by
  rw [restrictPullbackIso, ← Iso.trans_assoc,
    modulePullbackTriangle_app_trans_mapIso h t hc ha (by rw [← ha, Category.assoc, h, hc]),
    Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

/-- Restriction is injective as soon as the inverse image along the restricting morphism is
faithful on the homomorphisms concerned. -/
theorem restrictPullbackIso_injective {M : Modules.{u, u} B S hS A.1 A.2}
    {N : Modules.{u, u} B S hS A'.1 A'.2} {u : Z ⟶ A} {v : Z ⟶ A'} (t : Z₂ ⟶ Z)
    {u₂ : Z₂ ⟶ A} {v₂ : Z₂ ⟶ A'} (hu : t ≫ u = u₂) (hv : t ≫ v = v₂)
    (ht : Function.Injective (fun φ : (modulePullback B S hS u).obj M ⟶
      (modulePullback B S hS v).obj N ↦ (modulePullback B S hS t).map φ))
    {γ δ : (modulePullback B S hS u).obj M ≅ (modulePullback B S hS v).obj N}
    (h : restrictPullbackIso t hu hv γ = restrictPullbackIso t hu hv δ) : γ = δ := by
  have h' := congrArg Iso.hom h
  simp only [restrictPullbackIso_hom, cancel_epi, cancel_mono] at h'
  exact Iso.ext (ht h')

end AlgebraicGeometry.Space

end
