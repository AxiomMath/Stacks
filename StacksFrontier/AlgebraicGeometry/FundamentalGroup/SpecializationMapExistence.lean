module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapHelpers
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData
public import StacksFrontier.RingTheory.Valuation.StrictlyHenselian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Existence of specialization maps

Let `f : X ⟶ S` be a proper morphism with geometrically connected fibres, let `s' ⇝ s` be a
specialization of points of `S` and let `s̄'` and `s̄` be geometric points over `s'` and `s`. Then
there is a specialization map `π₁(X_{s̄'}) ⟶ π₁(X_{s̄})`.

The construction is the one of the source. Let `A` be the strict henselization of `𝒪_{S,s}` with
respect to a separable closure of `κ(s)`, and let `g : Spec A ⟶ S` be the resulting morphism.

* The geometric point `s̄` factors through the *closed* point of `Spec A`: the local homomorphism
  `𝒪_{S,s} → κ(s̄)` attached to `s̄` extends to a local `𝒪_{S,s}`-algebra map `A → κ(s̄)` because
  `κ(s̄)` is a henselian local ring with separably closed residue field and `κ(s)^{sep}` embeds
  separably into it; this is the functoriality of the strict henselization, Stacks 04GU.
* The geometric point `s̄'` factors through `Spec A` as well, but not through its closed point.
  Here the specialization `s' ⇝ s` enters: it gives a homomorphism `𝒪_{S,s} → κ(s̄')`, namely
  `S.presheaf.stalkSpecializes` followed by `Scheme.stalkClosedPointTo`, which is *not* local.
  Dominating the image by a valuation subring `V ⊆ κ(s̄')` makes it local, and `V` may be chosen
  strictly henselian with algebraically closed residue field, so Stacks 04GU applies again and
  gives `A → V ⊆ κ(s̄')`. This replaces the source's choice of a point of `Spec A` over `s'` with
  separably algebraic residue field followed by an embedding of that residue field into `κ(s̄')`.
* `X_A` is connected, because `X_A ⟶ Spec A` is proper with geometrically connected fibres and
  `Spec A` is connected.
* The two geometric fibre functors on the finite étale covers of `X_A` attached to the images of
  the two chosen base points are isomorphic, because `X_A` is connected (Stacks 0BND).

The specialization map is then the composite `π₁(X_{s̄'}) → π₁(X_A) = π₁(X_{s̄})`, the equality
being base change along `X_{s̄} ⟶ X_A` (Stacks 0BQA). That this base change is an equivalence on
finite étale covers is
`AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap`, which combines Stacks 0A48, 0BTW and
0A49 exactly as the source does.

## Main results

* `AlgebraicGeometry.exists_isSpecializationMap` — the construction, with the closed-fibre
  equivalence taken as the argument `hclosedFibre`.
  `AlgebraicGeometry.exists_continuousMonoidHom_isSpecializationMap`
  (`StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapConstruction`, Stacks 0BUP)
  supplies that argument.

## Implementation notes

Base change along the inclusion `X_{s̄} ⟶ X_A` of the closed geometric fibre being an equivalence
on finite étale covers is Stacks 0A48 for the proper `X_A` over the henselian local ring `A`,
followed by the passage from the closed fibre over the separably closed `κ(s)^{sep}` to the fibre
over the algebraically closed `κ(s̄)`: with `L` the algebraic closure of `κ(s)^{sep}` in `κ(s̄)`,
this is Stacks 0BTW for the purely inseparable `L / κ(s)^{sep}` and Stacks 0A49 for `L ⊆ κ(s̄)`.
All three are proved in this library and combined in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianClosedGeometricFibre`.

The specialization map produced depends on the factorization of `s̄'` through `Spec A`, as the
source points out; the statement is therefore an existence statement and not the definition of a
function of the specialization.

## References

* [Stacks Project, Tag 0BUP](https://stacks.math.columbia.edu/tag/0BUP)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 0C0M](https://stacks.math.columbia.edu/tag/0C0M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Points of the strict henselization -/

/-- **Functoriality of the strict henselization** (Stacks 04GU) into an arbitrary henselian local
algebra with separably closed residue field. A local homomorphism `φ : R → B` from a local ring
to a henselian local ring whose residue field is separably closed extends to a local
`R`-algebra map `R^{sh} → B` on the strict henselization of `R`: the residue field of `R^{sh}` is
a separable closure of `κ(R)`, hence embeds into the separably closed `κ(B)` over `κ(R)`, and
`HenselianLocalRing.indEtaleAlgHomOfResidue` turns that embedding into the required map. -/
@[ega "IV 18.8.8" "(ii)"]
private theorem exists_ringHom_isLocalHom_of_isStrictHenselization
    {R Rsh B : Type u} [CommRing R] [CommRing Rsh] [CommRing B]
    [IsLocalRing R] [IsLocalRing Rsh] [HenselianLocalRing B]
    [Algebra R Rsh] [IsSepClosed (ResidueField B)]
    (φ : R →+* B) (hφ : IsLocalHom φ)
    (hR : Stacks.StrictHenselization.IsStrictHenselization R
      (SeparableClosure (maximalIdeal R).ResidueField) Rsh) :
    ∃ ψ : Rsh →+* B, IsLocalHom ψ ∧ ψ.comp (algebraMap R Rsh) = φ := by
  classical
  let κR := (maximalIdeal R).ResidueField
  let KR := SeparableClosure κR
  let _ : IsLocalHom (algebraMap R Rsh) := hR.isLocalHom
  let _ : Algebra R B := φ.toAlgebra
  have halg : (algebraMap R B) = φ := RingHom.algebraMap_toAlgebra φ
  let _ : IsLocalHom (algebraMap R B) := halg ▸ hφ
  let up := residueFieldEquivMaximalIdealResidueField R
  let upRsh := residueFieldEquivMaximalIdealResidueField Rsh
  let ρ : κR →+* ResidueField B :=
    (IsLocalRing.ResidueField.map (algebraMap R B)).comp up.symm.toRingHom
  let _ : Algebra κR (ResidueField B) := ρ.toAlgebra
  let _ : IsSepClosed KR := IsSepClosure.sep_closed κR
  let χ : KR →ₐ[κR] ResidueField B := IsSepClosed.lift
  let eR : ResidueField Rsh ≃+* KR := upRsh.trans hR.residueFieldEquiv.symm
  let δ : ResidueField Rsh →+* ResidueField B := χ.toRingHom.comp eR.toRingHom
  have hResR (r : R) : algebraMap (ResidueField R) κR (residue R r) = algebraMap R κR r := by
    simpa only [IsLocalRing.ResidueField.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply R (ResidueField R) κR r).symm
  have hRbase (r : R) : eR (residue Rsh (algebraMap R Rsh r))
      = algebraMap κR KR (algebraMap (ResidueField R) κR (residue R r)) := by
    have hcompat := DFunLike.congr_fun hR.residueFieldEquiv_comp
      (algebraMap (ResidueField R) κR (residue R r))
    rw [hResR] at hcompat
    apply hR.residueFieldEquiv.injective
    calc hR.residueFieldEquiv (eR (residue Rsh (algebraMap R Rsh r)))
        = upRsh (residue Rsh (algebraMap R Rsh r)) := by
          change hR.residueFieldEquiv (hR.residueFieldEquiv.symm
            (upRsh (residue Rsh (algebraMap R Rsh r)))) = _
          exact RingEquiv.apply_symm_apply _ _
      _ = Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm
              (algebraMap R κR r) := by
          change algebraMap (ResidueField Rsh) (maximalIdeal Rsh).ResidueField
            (residue Rsh (algebraMap R Rsh r)) = _
          rw [← IsLocalRing.ResidueField.algebraMap_eq (R := Rsh),
            ← IsScalarTower.algebraMap_apply Rsh (ResidueField Rsh)
              (maximalIdeal Rsh).ResidueField (algebraMap R Rsh r)]
          exact (Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal Rsh)
            (algebraMap R Rsh) (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm r).symm
      _ = hR.residueFieldEquiv (algebraMap κR KR
            (algebraMap (ResidueField R) κR (residue R r))) := hcompat.symm
  have hδ : δ.comp ((residue Rsh).comp (algebraMap R Rsh))
      = (residue B).comp (algebraMap R B) := by
    ext r
    change χ (eR (residue Rsh (algebraMap R Rsh r))) = residue B (algebraMap R B r)
    rw [hRbase, χ.commutes]
    have hup : algebraMap (ResidueField R) κR (residue R r) = up (residue R r) := rfl
    rw [RingHom.algebraMap_toAlgebra, hup]
    change IsLocalRing.ResidueField.map (algebraMap R B) (up.symm (up (residue R r)))
      = residue B (algebraMap R B r)
    rw [up.symm_apply_apply, IsLocalRing.ResidueField.map_residue]
  let ν := HenselianLocalRing.indEtaleAlgHomOfResidue hR.isFilteredColimitEtale δ hδ
  have hνloc : IsLocalHom ν :=
    HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hR.isFilteredColimitEtale δ hδ
  refine ⟨(ν : Rsh →+* B), ⟨IsLocalHom.map_nonunit (f := ν)⟩, ?_⟩
  ext r
  exact (ν.commutes r).trans (RingHom.congr_fun halg r)

variable {X S : Scheme.{u}}

/-- Spec of a ring map `A → K` lying over `ψ : 𝒪_{S,z} → K` composes with `Spec A → S` to the
map `Spec K → S` induced by `ψ`. -/
private theorem spec_map_comp_fromSpecStalk_eq {z : S} {A K : Type u} [CommRing A] [CommRing K]
    [Algebra (S.presheaf.stalk z) A] (ψ : S.presheaf.stalk z ⟶ CommRingCat.of K) (u : A →+* K)
    (hu : u.comp (algebraMap (S.presheaf.stalk z) A) = ψ.hom) :
    Spec.map (CommRingCat.ofHom u) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫ S.fromSpecStalk z =
        Spec.map ψ ≫ S.fromSpecStalk z := by
  rw [← Spec.map_comp_assoc]
  exact congr_arg (Spec.map · ≫ S.fromSpecStalk z) (CommRingCat.hom_ext hu)

/-- The geometric point `s̄` factors through the closed point of `Spec A`, for `A` a strict
henselization of the stalk of `S` at the image of `s̄`. The factorization is `Spec` of the local
`𝒪_{S,s}`-algebra map `A → κ(s̄)` of Stacks 04GU, available because `κ(s̄)` is a field, hence a
henselian local ring whose residue field is separably closed. -/
private theorem exists_factorization_closedPoint (s : GeometricPoint S) (z : S)
    (hz : s.hom (closedPoint s.residueField) = z) (A : Type u) [CommRing A]
    [IsLocalRing A] [Algebra (S.presheaf.stalk z) A]
    (hA : Stacks.StrictHenselization.IsStrictHenselization (S.presheaf.stalk z)
      (SeparableClosure (maximalIdeal (S.presheaf.stalk z)).ResidueField) A) :
    ∃ (p : s.source ⟶ Spec (.of A)),
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫
          S.fromSpecStalk z = s.hom ∧
        p (closedPoint s.residueField) = closedPoint A := by
  subst hz
  let _ : IsSepClosed (ResidueField s.residueField) :=
    have : IsAlgClosed (ResidueField s.residueField) :=
      IsAlgClosed.of_ringEquiv s.residueField _
        ((RingEquiv.quotientBot s.residueField).symm.trans
          (Ideal.quotEquivOfEq maximalIdeal_eq_bot.symm))
    inferInstance
  obtain ⟨u, huloc, hucomp⟩ := exists_ringHom_isLocalHom_of_isStrictHenselization
    (Scheme.stalkClosedPointTo s.hom).hom
    (Scheme.isLocalHom_stalkClosedPointTo s.hom) hA
  let _ : IsLocalHom u := huloc
  refine ⟨Spec.map (CommRingCat.ofHom u), ?_, ?_⟩
  · rw [spec_map_comp_fromSpecStalk_eq _ u hucomp]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk s.hom
  · exact comap_closedPoint u

/-- The geometric point `s̄'` factors through `Spec A`, for `A` a strict henselization of the
stalk of `S` at the image `s` of a second geometric point to which `s'` specializes. The
specialization gives a homomorphism `𝒪_{S,s} → κ(s̄')`, which is not local; a valuation subring
`V ⊆ κ(s̄')` dominating its image is strictly henselian with algebraically closed residue field
(Stacks 0C0M), so Stacks 04GU extends the resulting local homomorphism `𝒪_{S,s} → V` to
`A → V`, and the factorization is `Spec` of `A → V ⊆ κ(s̄')`. -/
private theorem exists_factorization_of_specializes (s' : GeometricPoint S) (z : S)
    (hspec : s'.hom (closedPoint s'.residueField) ⤳ z)
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra (S.presheaf.stalk z) A]
    (hA : Stacks.StrictHenselization.IsStrictHenselization (S.presheaf.stalk z)
      (SeparableClosure (maximalIdeal (S.presheaf.stalk z)).ResidueField) A) :
    ∃ p' : s'.source ⟶ Spec (.of A),
      p' ≫ Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫
          S.fromSpecStalk z = s'.hom := by
  let ψ : S.presheaf.stalk z ⟶ CommRingCat.of s'.residueField :=
    S.presheaf.stalkSpecializes hspec ≫ Scheme.stalkClosedPointTo s'.hom
  have hψ : Spec.map ψ ≫ S.fromSpecStalk z = s'.hom := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk s'.hom
  obtain ⟨V, hmem, hVloc, hVsh, -⟩ :=
    IsLocalRing.exists_factor_valuationRing_strictlyHenselian ψ.hom
  let _ : StrictlyHenselianLocalRing V := hVsh
  obtain ⟨u, -, hucomp⟩ := exists_ringHom_isLocalHom_of_isStrictHenselization
    (ψ.hom.codRestrict V.toSubring hmem) hVloc hA
  refine ⟨Spec.map (CommRingCat.ofHom ((algebraMap V s'.residueField).comp u)), ?_⟩
  rw [spec_map_comp_fromSpecStalk_eq ψ _ ?_]
  · exact hψ
  · ext x
    change algebraMap V s'.residueField (u (algebraMap (S.presheaf.stalk z) A x)) = ψ.hom x
    have hx : u (algebraMap (S.presheaf.stalk z) A x)
        = ψ.hom.codRestrict V.toSubring hmem x := RingHom.congr_fun hucomp x
    rw [hx]
    rfl

/-! ### Specialization maps exist -/

/-- The construction of a specialization map `π₁(X_{s̄'}) ⟶ π₁(X_{s̄})` for a proper `f : X ⟶ S`
with geometrically connected fibres and a specialization `s' ⇝ s`, taking as the argument
`hclosedFibre` that base change along the closed geometric fibre `X_{s̄} ⟶ X ×_S Spec C` is an
equivalence on finite étale covers for every henselian local ring `C` with separably closed
residue field through whose closed point `s̄` factors. That argument always holds
(`isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap`), and
`exists_continuousMonoidHom_isSpecializationMap` is this theorem with it supplied. -/
theorem exists_isSpecializationMap (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (s' s : GeometricPoint S)
    (hspec : s'.hom (closedPoint s'.residueField) ⤳ s.hom (closedPoint s.residueField))
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (hclosedFibre : ∀ (C : Type u) (_ : CommRing C) (_ : HenselianLocalRing C),
      ∀ (_ : IsSepClosed (ResidueField C)) (r : Spec (.of C) ⟶ S)
        (q : s.source ⟶ Spec (.of C)) (hq : q ≫ r = s.hom),
      q (closedPoint s.residueField) = closedPoint C →
      (finiteEtaleBaseChange (fiberOverGeometricPointMap f s r q hq)).IsEquivalence) :
    ∃ sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint f s) x,
      IsSpecializationMap f s' s x' x sp := by
  classical
  obtain ⟨A, hAring, hAloc, hAalg, hAsh⟩ := Stacks.StrictHenselization.exists_isStrictHenselization
    (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
    (SeparableClosure (maximalIdeal
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))).ResidueField)
  let _ : CommRing A := hAring
  let _ : IsLocalRing A := hAloc
  let _ : Algebra (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A := hAalg
  obtain ⟨hAsh⟩ := hAsh
  let _ : HenselianLocalRing A := hAsh.henselian
  let _ : IsSepClosed (maximalIdeal A).ResidueField := hAsh.sepClosed
  let _ : IsSepClosed (ResidueField A) := isSepClosed_residueField_of_maximalIdeal A
  let g : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap
        (S.presheaf.stalk (s.hom (closedPoint s.residueField))) A)) ≫
      S.fromSpecStalk (s.hom (closedPoint s.residueField))
  obtain ⟨p, hp, hpclosed⟩ := exists_factorization_closedPoint s _ rfl A hAsh
  obtain ⟨p', hp'⟩ := exists_factorization_of_specializes s' _ hspec A hAsh
  let i' : fiberOverGeometricPoint f s' ⟶ pullback f g := fiberOverGeometricPointMap f s' g p' hp'
  let i : fiberOverGeometricPoint f s ⟶ pullback f g := fiberOverGeometricPointMap f s g p hp
  have hXAconn : ConnectedSpace (pullback f g : Scheme.{u}) :=
      connectedSpace_pullback_spec_of_isProper f A g
  let _ : ConnectedSpace (pullback f g : Scheme.{u}) := hXAconn
  have hi : (finiteEtaleBaseChange i).IsEquivalence :=
    hclosedFibre A hAring inferInstance inferInstance g p hp hpclosed
  let _ := hi
  let t : finiteEtaleFiberFunctor (x'.map i') ≅ finiteEtaleFiberFunctor (x.map i) :=
    (nonempty_finiteEtaleFiberFunctorIso (pullback f g) (x'.map i') (x.map i)).some
  refine ⟨(ContinuousMonoidHom.toContinuousMonoidHom
      (etaleFundamentalGroupContinuousMulEquivOfIsEquivalence i x).symm).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom
      (etaleFundamentalGroupContinuousMulEquiv t)).comp
        (etaleFundamentalGroupMap i' x')), ?_⟩
  simp only [IsSpecializationMap]
  refine ⟨A, hAring, hAloc, hAalg, ⟨hAsh⟩, p', hp', p, hp, hpclosed, hXAconn, hi, t, fun γ ↦ ?_⟩
  change etaleFundamentalGroupMap i x
      ((etaleFundamentalGroupMulEquivOfIsEquivalence i x).symm
        (etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupMap i' x' γ))) = _
  rw [← etaleFundamentalGroupMulEquivOfIsEquivalence_apply]
  exact (etaleFundamentalGroupMulEquivOfIsEquivalence i x).apply_symm_apply _

end AlgebraicGeometry

end
