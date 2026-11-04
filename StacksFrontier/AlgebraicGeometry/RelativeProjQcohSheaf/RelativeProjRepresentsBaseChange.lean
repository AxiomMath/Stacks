module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartBaseChangeAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjRepresents
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoRepresenting
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionBaseChangeTransport

/-!
# The base-change morphism of Tag 01O3 and the representation of Tag 01NZ

Let `g : S' ⟶ S` be a morphism of schemes and `𝒜` a quasi-coherent graded `𝒪_S`-algebra.  The
relative homogeneous spectra `Proj_S(𝒜)` and `Proj_{S'}(g^*𝒜)` represent the functors `F` and `F'`
of the display 01NX (Tags 01NY, 01NZ), and Tag 01NT identifies `F'` with `h_{S'} ×_{h_S} F`,
sending a quadruple `(d, f', ℒ, ψ')` to `(d, g ∘ f', ℒ, ψ)`.  This file proves that the
base-change morphism `Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)` of Tag 01O3,
`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom`, which is defined chart by
chart, is the morphism these identifications induce: a morphism `k : T ⟶ Proj_{S'}(g^*𝒜)`
followed by it is the morphism representing the base change of the point of `F'` that `k`
represents (`...RelativeProjQcohSheaf.homEquiv_comp_baseChangeHom_val`).

It also constructs the isomorphism of relative homogeneous spectra induced by an isomorphism of
graded algebras, through the representations
(`...RelativeProjQcohSheaf.relativeProjCongr`).

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.homDegreeOpen_baseChangeUp`: the base-change
  morphism on the degree-`d` opens.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.classifyingMorphism_baseChangeUp`: the morphism
  attached to the base change of a point of `F'` is the morphism attached to the point followed
  by the base-change morphism.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.homEquiv_comp_baseChangeHom_val`: the same for
  the representation of the extended functor.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.relativeProjCongr` and
  `...RelativeProjQcohSheaf.homEquiv_comp_relativeProjCongr_val`.

## References

* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-! ### The canonical isomorphism of a relative homogeneous spectrum with itself -/

/-- The canonical isomorphism of Tag 01NZ between the relative homogeneous spectrum and itself is
the identity: both are compatible with the charts and with the structure morphism, and there is
only one such isomorphism. -/
theorem canonicalIso_relativeProj : canonicalIso A (relativeProj A) = Iso.refl _ :=
  (existsUnique_isoOver A (relativeProj A)).unique
    ⟨fun U => chart_comp_canonicalIso_hom A (relativeProj A) U,
      canonicalIso_hom_comp_toBase A (relativeProj A)⟩
    ⟨fun _ => Category.comp_id _, Category.id_comp _⟩

/-! ### The degree-`d` opens -/

/-- **The base-change morphism on the degree-`d` opens.** The morphism into `Proj_S(𝒜)` attached
to the base change of a point `ξ'` of `F'_d(W)` is the morphism into `Proj_{S'}(g^*𝒜)` attached to
`ξ'`, followed by the base-change morphism. Over the preimage of an affine open `U' ⊆ g⁻¹U` both
are chart-wise morphisms, which `Fd.chartHom_comp_baseChangeHom` compares, and such preimages
cover `W`. -/
theorem Fd.homDegreeOpen_baseChangeUp {k : ℕ} (hk : 0 < k) {W : Scheme.{u}}
    (ξ' : Fd (situationAlgebra (A.pullback g)) (k : ℤ) W) :
    Fd.homDegreeOpen A (relativeProj A) hk (Fd.baseChangeUp g (situationAlgebra A) (k : ℤ) ξ')
        ≫ ((relativeProj A).degreeOpen k).ι
      = Fd.homDegreeOpen (A.pullback g) (relativeProj (A.pullback g)) hk ξ'
          ≫ ((relativeProj (A.pullback g)).degreeOpen k).ι
          ≫ RelativeProjBaseChangeTwist.baseChangeHom A g := by
  set f' := ξ'.1
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.base (f'.base x)))
      isOpen_univ
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open (show f'.base x ∈ g ⁻¹ᵁ U from hxU)
      (g ⁻¹ᵁ U).isOpen
  have hle : U' ≤ g ⁻¹ᵁ U := hU'U
  set ξ := Fd.baseChangeUp g (situationAlgebra A) (k : ℤ) ξ'
  refine ⟨f' ⁻¹ᵁ U', hxU', ?_⟩
  set j := (f' ⁻¹ᵁ U').ι
  have hle' : f' ⁻¹ᵁ U' ≤ ξ.1 ⁻¹ᵁ U := fun y hy => hle hy
  set j₁ := W.homOfLE hle'
  have hjj : j₁ ≫ (ξ.1 ⁻¹ᵁ U).ι = j := Scheme.homOfLE_ι _ _
  -- the chart-wise classes
  obtain ⟨η', hη'⟩ := Fd.exists_chartClassInv_eq (A.pullback g) U'
    (Fd.pullback j ξ') (f' ∣_ U') (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ U')
  obtain ⟨η, hη⟩ := Fd.exists_chartClassInv_eq A U
    (Fd.pullback (ξ.1 ⁻¹ᵁ U).ι ξ) (ξ.1 ∣_ U) (by rw [Fd.pullback_fst]; exact morphismRestrict_ι _ U)
  have hcl : Fd.baseChangeUp g (situationAlgebra A) (k : ℤ)
      (Fd.chartClassInv (A.pullback g) U' η') = Fd.chartClassInv A U (Fd.pullback j₁ η) := by
    rw [hη', Fd.chartClassInv_pullback, hη, ← Fd.pullback_comp, hjj]
    exact Fd.baseChangeUp_pullback g (situationAlgebra A) (k : ℤ) j ξ'
  calc j ≫ Fd.homDegreeOpen A (relativeProj A) hk ξ ≫ ((relativeProj A).degreeOpen k).ι
      = j₁ ≫ (ξ.1 ⁻¹ᵁ U).ι ≫ Fd.homDegreeOpen A (relativeProj A) hk ξ
          ≫ ((relativeProj A).degreeOpen k).ι := by rw [← hjj, Category.assoc]
    _ = j₁ ≫ Fd.chartHom A U (relativeProj A) hU hk _ η := by
        rw [Fd.ι_homDegreeOpen A (relativeProj A) hk ξ U hU η hη]
    _ = Fd.chartHom A U (relativeProj A) hU hk _ (Fd.pullback j₁ η) :=
        (Fd.chartHom_pullback A U (relativeProj A) hU hk j₁ η).symm
    _ = Fd.chartHom (A.pullback g) U' (relativeProj (A.pullback g)) hU' hk _ η'
          ≫ RelativeProjBaseChangeTwist.baseChangeHom A g :=
        (Fd.chartHom_comp_baseChangeHom A g ⟨U, hU⟩ ⟨U', hU'⟩ hle hk η' (Fd.pullback j₁ η)
          hcl).symm
    _ = j ≫ Fd.homDegreeOpen (A.pullback g) (relativeProj (A.pullback g)) hk ξ'
          ≫ ((relativeProj (A.pullback g)).degreeOpen k).ι
          ≫ RelativeProjBaseChangeTwist.baseChangeHom A g := by
        rw [← Fd.ι_homDegreeOpen (A.pullback g) (relativeProj (A.pullback g)) hk ξ' U' hU' η' hη']
        rfl

/-! ### The classifying morphisms -/

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism in
/-- **The morphism attached to the base change of a point of `F'` is the morphism attached to the
point followed by the base-change morphism of Tag 01O3.** -/
theorem classifyingMorphism_baseChangeUp {W : Scheme.{u}}
    (ξ' : F (situationAlgebra (A.pullback g)) W) :
    F.classifyingMorphism A (F.baseChangeUp g (situationAlgebra A) ξ') =
      F.classifyingMorphism (A.pullback g) ξ' ≫ RelativeProjBaseChangeTwist.baseChangeHom A g := by
  obtain ⟨d, hd, Q, hQ⟩ := F.exists_quadruple ξ'
  rw [← hQ]
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
  have hk : 0 < k := by exact_mod_cast hd
  have e1 := F.classifyingMorphism_mk A hk
    (Q.baseChangeUp g ξ'.1 (situationAlgebra A) (k : ℤ))
  have e2 := F.classifyingMorphism_mk (A.pullback g) hk Q
  rw [canonicalIso_relativeProj, Iso.refl_inv] at e1 e2
  refine e1.trans ?_
  rw [e2]
  simp only [Category.comp_id, Category.assoc]
  exact Fd.homDegreeOpen_baseChangeUp A g hk (Fd.mk ξ'.1 Q)

/-! ### The representation of the extended functor -/

section Represent

variable {Y : Scheme.{u}} (B : SheafGradedAlgebra Y)

/-- The value at a quasi-compact test scheme of the point represented by a morphism is read off
at the identity of the test scheme. -/
theorem homEquiv_val_eq {T : Scheme.{u}} (m : T ⟶ (relativeProj B).scheme) (W : Scheme.{u})
    (hW : CompactSpace W) (w : W ⟶ T) :
    ((relativeProjRepresentableByFunctorUnconditional B).homEquiv m).val W hW w =
      ((relativeProjRepresentableByFunctorUnconditional B).homEquiv (w ≫ m)).val W hW (𝟙 W) := by
  rw [Functor.RepresentableBy.homEquiv_comp]
  rfl

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism in
/-- On a quasi-compact test scheme, the point represented by a morphism classifies it. -/
theorem classifyingMorphism_homEquiv_val {W : Scheme.{u}} (hW : CompactSpace W)
    (m : W ⟶ (relativeProj B).scheme) :
    F.classifyingMorphism B
        (((relativeProjRepresentableByFunctorUnconditional B).homEquiv m).val W hW (𝟙 W)) = m := by
  have h : F.toLim B (((relativeProjRepresentableByFunctorUnconditional B).homEquiv m).val W hW
      (𝟙 W)) = (relativeProjRepresentableByFunctorUnconditional B).homEquiv m :=
    (F.limEquiv (situationAlgebra B) W hW).symm_apply_apply
      ((relativeProjRepresentableByFunctorUnconditional B).homEquiv m)
  exact (congrArg (relativeProjRepresentableByFunctorUnconditional B).homEquiv.symm h).trans
    (Equiv.symm_apply_apply _ m)

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism in
/-- The point represented by the morphism a point classifies is the point. -/
theorem homEquiv_classifyingMorphism {W : Scheme.{u}} (ζ : F (situationAlgebra B) W) :
    (relativeProjRepresentableByFunctorUnconditional B).homEquiv (F.classifyingMorphism B ζ) =
      F.toLim B ζ :=
  Equiv.apply_symm_apply _ _

end Represent

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism in
/-- **The base-change morphism of Tag 01O3 and the representations of Tags 01NY and 01NZ.** For
`k : T ⟶ Proj_{S'}(g^*𝒜)` the point of the functor `F` of `𝒜` represented by `k` followed by the
base-change morphism is, at every quasi-compact test scheme, the base change of Tag 01NT of the
point of the functor `F'` of `g^*𝒜` represented by `k`. -/
theorem homEquiv_comp_baseChangeHom_val {T : Scheme.{u}}
    (k : T ⟶ (relativeProj (A.pullback g)).scheme) (W : Scheme.{u}) (hW : CompactSpace W)
    (w : W ⟶ T) :
    ((relativeProjRepresentableByFunctorUnconditional A).homEquiv
        (k ≫ RelativeProjBaseChangeTwist.baseChangeHom A g)).val W hW w =
      F.baseChangeUp g (situationAlgebra A)
        (((relativeProjRepresentableByFunctorUnconditional (A.pullback g)).homEquiv k).val W hW w)
    := by
  rw [homEquiv_val_eq, homEquiv_val_eq (A.pullback g)]
  set ζ' := ((relativeProjRepresentableByFunctorUnconditional (A.pullback g)).homEquiv
    (w ≫ k)).val W hW (𝟙 W)
  have hcl : F.classifyingMorphism A (F.baseChangeUp g (situationAlgebra A) ζ') =
      w ≫ k ≫ RelativeProjBaseChangeTwist.baseChangeHom A g :=
    (classifyingMorphism_baseChangeUp A g ζ').trans (by
      rw [classifyingMorphism_homEquiv_val (A.pullback g) hW (w ≫ k), Category.assoc])
  rw [← hcl, homEquiv_classifyingMorphism]
  exact F.pullback_id _

/-! ### The isomorphism of relative homogeneous spectra induced by an isomorphism of algebras -/

/-- **The extension over the quasi-compact test schemes of an isomorphism of functors.** -/
def _root_.AlgebraicGeometry.Scheme.QcExtension.mapIso {Φ Ψ : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)}
    (e : Φ ≅ Ψ) : Scheme.QcExtension.functor Φ ≅ Scheme.QcExtension.functor Ψ :=
  NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun s =>
        { val := fun W hW w => e.hom.app (op W) (s.val W hW w)
          compat := fun W W' hW hW' h w => by
            rw [← s.compat W W' hW hW' h w]
            exact (NatTrans.naturality_apply e.hom h.op _).symm }
      invFun := fun s =>
        { val := fun W hW w => e.inv.app (op W) (s.val W hW w)
          compat := fun W W' hW hW' h w => by
            rw [← s.compat W W' hW hW' h w]
            exact (NatTrans.naturality_apply e.inv h.op _).symm }
      left_inv := fun s => Scheme.QcExtension.ext (funext fun W => funext fun hW => funext fun w =>
        congrArg (fun α => α.app (op W) (s.val W hW w)) e.hom_inv_id)
      right_inv := fun s => Scheme.QcExtension.ext (funext fun W => funext fun hW => funext fun w =>
        congrArg (fun α => α.app (op W) (s.val W hW w)) e.inv_hom_id) })
    (fun {_ _} _ => rfl)

/-- The value of `Scheme.QcExtension.mapIso e` at a quasi-compact test scheme `W` is given by the
component of `e.hom` at `W`. -/
theorem _root_.AlgebraicGeometry.Scheme.QcExtension.mapIso_hom_app_val
    {Φ Ψ : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} (e : Φ ≅ Ψ) (T : Scheme.{u}ᵒᵖ)
    (s : Scheme.QcExtension Φ T.unop) (W : Scheme.{u}) (hW : CompactSpace W) (w : W ⟶ T.unop) :
    ((Scheme.QcExtension.mapIso e).hom.app T s).val W hW w = e.hom.app (op W) (s.val W hW w) :=
  rfl

section Congr

variable {Y : Scheme.{u}} {A₁ A₂ : SheafGradedAlgebra Y}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁) (situationAlgebra A₂))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))

/-- The isomorphism of the extended functors of the display 01NX of two isomorphic graded
algebras: the transport along the inverse of the isomorphism, at every quasi-compact test
scheme. -/
def limFunctorIso : F.limFunctor (situationAlgebra A₁) ≅ F.limFunctor (situationAlgebra A₂) :=
  Scheme.QcExtension.mapIso
    (F.algebraTransportIso (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ))

/-- **The isomorphism of relative homogeneous spectra induced by an isomorphism of graded
algebras**: the two relative homogeneous spectra represent isomorphic functors, by Tags 01NY and
01NZ, so they are isomorphic. -/
def relativeProjCongr : (relativeProj A₁).scheme ≅ (relativeProj A₂).scheme :=
  ((relativeProjRepresentableByFunctorUnconditional A₁).ofIso
    (limFunctorIso Φ hΦ)).uniqueUpToIso (relativeProjRepresentableByFunctorUnconditional A₂)

/-- **The isomorphism of relative homogeneous spectra induced by an isomorphism of graded
algebras, on points**: a morphism `k` into `Proj(𝒜₁)` followed by it represents the transport of
the point `k` represents. -/
theorem homEquiv_comp_relativeProjCongr {T : Scheme.{u}} (k : T ⟶ (relativeProj A₁).scheme) :
    (relativeProjRepresentableByFunctorUnconditional A₂).homEquiv
        (k ≫ (relativeProjCongr Φ hΦ).hom) =
      (limFunctorIso Φ hΦ).hom.app (op T)
        ((relativeProjRepresentableByFunctorUnconditional A₁).homEquiv k) := by
  have hhom : (relativeProjCongr Φ hΦ).hom =
      (relativeProjRepresentableByFunctorUnconditional A₂).homEquiv.symm
        ((limFunctorIso Φ hΦ).hom.app _
          ((relativeProjRepresentableByFunctorUnconditional A₁).homEquiv (𝟙 _))) := rfl
  rw [Functor.RepresentableBy.homEquiv_comp, hhom, Equiv.apply_symm_apply,
    ← NatTrans.naturality_apply, ← Functor.RepresentableBy.homEquiv_comp, Category.comp_id]

/-- The point represented by `k ≫ (relativeProjCongr Φ hΦ).hom`, evaluated at a quasi-compact test
scheme `W`, is the algebra transport, along the inverse of `Φ`, of the point represented by `k`. -/
theorem homEquiv_comp_relativeProjCongr_val {T : Scheme.{u}} (k : T ⟶ (relativeProj A₁).scheme)
    (W : Scheme.{u}) (hW : CompactSpace W) (w : W ⟶ T) :
    ((relativeProjRepresentableByFunctorUnconditional A₂).homEquiv
        (k ≫ (relativeProjCongr Φ hΦ).hom)).val W hW w =
      F.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ)
        (((relativeProjRepresentableByFunctorUnconditional A₁).homEquiv k).val W hW w) := by
  rw [homEquiv_comp_relativeProjCongr]
  rfl

end Congr

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
