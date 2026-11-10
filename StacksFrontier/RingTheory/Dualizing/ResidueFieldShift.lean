module

public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.RingTheory.Dualizing.OverField
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing

/-!
# Derived Hom of a residue field into a dualizing complex

Let `A` be a Noetherian ring, `ω` a dualizing complex over `A` and `m ⊆ A` a maximal ideal with
residue field `κ = A/m`. Then `RHom_A(κ, ω)` is a shift of `κ`.

The argument has two halves. The first is that `RHom_A(κ, ω)` is a *simple* object of `D(κ)`:
by [Stacks, Tag 0AX0] it is a dualizing complex over `κ`, and over any Noetherian ring the
homothety condition in the definition of a dualizing complex says exactly that the degree-zero
endomorphisms of the complex in the derived category are the scalars. Over a field every nonzero
scalar is invertible, so every endomorphism is zero or invertible, and
`DerivedCategory.Invertible.simple_of_endomorphism_eq_zero_or_isIso` turns that into
simplicity. The second half is
`Dualizing.simple_bounded_iso_shift_field`, which says that a cohomologically bounded simple
object of the derived category of a field is a shift of the one-dimensional module in degree
zero.

## Main results

* `Dualizing.simple_of_isDualizingComplex_field` — a dualizing complex over a field is a simple
  object of its derived category.
* `Dualizing.derivedHom_residueField_iso_shift` — **[Stacks, Tag 0A7L]**: derived Hom from the
  residue field at a maximal ideal into a dualizing complex is a shift of that residue field.
* `Dualizing.derivedHom_localResidueField_iso_shift` — the same statement over a Noetherian local
  ring, phrased with `IsLocalRing.residue`, which is the form
  `Dualizing.IsNormalizedDualizingComplex` is stated against.

## Implementation notes

Extracting the scalars from the homothety condition is where the work is. The condition is
`QuasiIso (Dualizing.homothety I)` for a bounded injective representative `I`, i.e. that a chain
map of complexes of *additive groups* out of `ULift A` in degree zero is a quasi-isomorphism;
`Dualizing.homComplex_represents_derivedHom` identifies the degree-zero cohomology of its target
with `End_{D(κ)}(ω)`. So the composite `scalarToEnd` below, from `ULift κ` to those
endomorphisms, is a bijection because it is built from three bijections, and it is `a ↦ a • 𝟙`
because `Dualizing.homothety` is defined by that formula. The one square needed to transport the
formula through the universe lift of the Hom complex is
`CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom`.

The residue field of a maximal ideal is built here as a `Field (A ⧸ m)` instance whose ring
structure is the one already present on the quotient, rather than the one `Ideal.Quotient.field`
carries: the two are definitionally equal but not syntactically, and the derived category of
`ModuleCat (A ⧸ m)` must be formed from the ring structure the quotient already has for the
statement to be about `RHom_A(A/m, ω)`.

## References

* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- **A dualizing complex over a field is simple.** The homothety condition identifies the
endomorphisms of the complex in the derived category with the scalars, and over a field every
nonzero scalar is invertible. -/
theorem simple_of_isDualizingComplex_field
    {k : Type u} [Field k]
    (M : DerivedCategory (ModuleCat.{max v u} k))
    (hM : IsDualizingComplex M) : Simple M := by
  obtain ⟨a, b, I, hge, hle, hInj, ⟨eI⟩⟩ := hM.finiteInjectiveDimension
  have hq : QuasiIso (homothety I) :=
    hM.homothetyQuasiIso I ⟨eI.symm⟩ hInj ⟨a, b, hge, hle⟩
  have hb := ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap (homothety I) 0)
  let H := CochainComplex.HomComplex I I
  let F := AddCommGrpCat.uliftFunctor.{u, max v u}
  let uiso : (liftedEndomorphismComplex I).homology 0 ≅
      F.obj (H.homology 0) := (H.sc 0).mapHomologyIso F
  let D := DerivedCategory (ModuleCat.{max v u} k)
  let qI := DerivedCategory.Q.obj I
  let q0 :
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} k) (ComplexShape.up ℤ)).obj I)
        ≅ M :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} k)).app I ≪≫ eI.symm
  let q1 :
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{max v u} k) (ComplexShape.up ℤ)).obj
          (I⟦(0 : ℤ)⟧)) ≅ M :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} k)).app (I⟦(0 : ℤ)⟧) ≪≫
      (DerivedCategory.Q.commShiftIso 0).app I ≪≫
      (shiftFunctorZero D ℤ).app qI ≪≫ eI.symm
  let classToEnd : CochainComplex.HomComplex.CohomologyClass I I 0 → (M ⟶ M) :=
    fun c => q0.inv ≫
      DerivedCategory.Qh.map
        (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c) ≫ q1.hom
  have hrep := homComplex_represents_derivedHom I a 0
  have hclassSurj : Function.Surjective classToEnd := by
    intro f
    let g := q0.hom ≫ f ≫ q1.inv
    obtain ⟨c, hc⟩ := hrep.2 g
    refine ⟨c, ?_⟩
    change DerivedCategory.Qh.map
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c) = g at hc
    change q0.inv ≫
      DerivedCategory.Qh.map
        (CochainComplex.HomComplex.CohomologyClass.homAddEquiv c) ≫
      q1.hom = f
    rw [hc]
    simp [g, Category.assoc]
  let sIso := HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℤ) 0 (AddCommGrpCat.of (ULift.{max v u} k))
  let scalarToEnd (x : ULift.{max v u} k) : M ⟶ M :=
    classToEnd
      (CochainComplex.HomComplex.homologyAddEquiv I I 0
        ((uiso.hom
          ((HomologicalComplex.homologyMap (homothety I) 0).hom
            (sIso.inv x))).down))
  have hScalarSurj : Function.Surjective scalarToEnd := by
    intro f
    obtain ⟨c, hc⟩ := hclassSurj f
    obtain ⟨x, hx⟩ := (CochainComplex.HomComplex.homologyAddEquiv I I 0).surjective c
    obtain ⟨z, hz⟩ := hb.2 (uiso.inv (ULift.up x))
    refine ⟨sIso.hom z, ?_⟩
    dsimp [scalarToEnd]
    rw [sIso.hom_inv_id_apply, hz]
    have he := uiso.inv_hom_id_apply (ULift.up x)
    have he' := congrArg (fun t : F.obj (H.homology 0) => t.down) he
    rw [he', hx, hc]
  have hScalar (x : ULift.{max v u} k) :
      scalarToEnd x = x.down • (𝟙 M) := by
    have hclass :
        (CochainComplex.HomComplex.homologyAddEquiv I I 0)
          ((uiso.hom
            ((HomologicalComplex.homologyMap (homothety I) 0).hom
              (sIso.inv x))).down) =
        CochainComplex.HomComplex.CohomologyClass.mk
          (CochainComplex.HomComplex.Cocycle.ofHom (x.down • (𝟙 I))) := by
      let S := H.sc 0
      let h := CochainComplex.HomComplex.leftHomologyData I I 0
      let B := AddCommGrpCat.of (ULift.{max v u} k)
      let g : B ⟶ F.obj S.cycles :=
        (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 B).inv ≫
          HomologicalComplex.cyclesMap (homothety I) 0 ≫
          (S.mapCyclesIso F).hom
      have hsq : (liftedEndomorphismComplex I).homologyπ 0 ≫ uiso.hom =
          (S.mapCyclesIso F).hom ≫ F.map (H.homologyπ 0) :=
        ShortComplex.homologyπ_comp_mapHomologyIso_hom S F
      have hsi : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 B).inv ≫
          ((CochainComplex.singleFunctor AddCommGrpCat 0).obj B).homologyπ 0 = sIso.inv :=
        HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ (ComplexShape.up ℤ) 0 B
      have hassoc : ∀ {Z : AddCommGrpCat.{max u v}} (w : F.obj S.cycles ⟶ Z),
          g ≫ w = (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 B).inv ≫
            HomologicalComplex.cyclesMap (homothety I) 0 ≫ (S.mapCyclesIso F).hom ≫ w :=
        fun w => (Category.assoc _ _ _).trans
          (congrArg (fun z => (HomologicalComplex.singleObjCyclesSelfIso
            (ComplexShape.up ℤ) 0 B).inv ≫ z) (Category.assoc _ _ _))
      have hcat : sIso.inv ≫
          HomologicalComplex.homologyMap (homothety I) 0 ≫ uiso.hom =
          g ≫ F.map (H.homologyπ 0) := by
        rw [hassoc, ← hsi, Category.assoc,
          HomologicalComplex.homologyπ_naturality_assoc, hsq]
        rfl
      let c : CochainComplex.HomComplex.Cocycle I I 0 :=
        CochainComplex.HomComplex.Cocycle.ofHom (x.down • (𝟙 I))
      have hmc : (S.mapCyclesIso F).hom ≫ F.map S.iCycles =
          (liftedEndomorphismComplex I).iCycles 0 :=
        ShortComplex.mapCyclesIso_hom_iCycles S F
      have hgmap' : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 B).inv ≫
          HomologicalComplex.cyclesMap (homothety I) 0 ≫
            (liftedEndomorphismComplex I).iCycles 0 = (homothety I).f 0 := by
        have hiC : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 B).inv ≫
            ((CochainComplex.singleFunctor AddCommGrpCat 0).obj B).iCycles 0 =
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv :=
          HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles (ComplexShape.up ℤ) 0 B
        have hself : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 B).inv
            = 𝟙 B := rfl
        rw [HomologicalComplex.cyclesMap_i, ← Category.assoc, hiC]
        exact (congrArg (fun z : B ⟶ B => z ≫ (homothety I).f 0) hself).trans
          (Category.id_comp _)
      have hgmap : g ≫ F.map S.iCycles =
          (homothety I).f 0 :=
        (hassoc _).trans
          ((congrArg (fun z => (HomologicalComplex.singleObjCyclesSelfIso
            (ComplexShape.up ℤ) 0 B).inv ≫
              HomologicalComplex.cyclesMap (homothety I) 0 ≫ z) hmc).trans hgmap')
      have hhom : (homothety I).f 0 x =
          ULift.up (x.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)) := by
        simp only [homothety]
        rfl
      have hg : g x = ULift.up (h.cyclesIso.inv c) := by
        apply ULift.ext
        apply (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance
        have hp := congrArg (fun f : B ⟶ F.obj S.X₂ => f x) hgmap
        have hpdown := congrArg ULift.down hp
        have hleft : S.iCycles (g x).down =
            x.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I) :=
          hpdown.trans (congrArg ULift.down hhom)
        have hright : S.iCycles (h.cyclesIso.inv c) =
            CochainComplex.HomComplex.Cochain.ofHom (x.down • (𝟙 I)) :=
          congrArg (fun f : h.K ⟶ S.X₂ => f c) h.cyclesIso_inv_comp_iCycles
        rw [hleft, hright]
        apply CochainComplex.HomComplex.Cochain.ext₀
        intro p
        simp
      have hc := congrArg (fun f : B ⟶ F.obj (H.homology 0) => f x) hcat
      have hc' :
          (uiso.hom
            ((HomologicalComplex.homologyMap (homothety I) 0).hom
              (sIso.inv x))).down =
          (H.homologyπ 0) (h.cyclesIso.inv c) := by
        have hp0 := congrArg ULift.down hc
        simp only [ConcreteCategory.comp_apply] at hp0
        rw [hg] at hp0
        exact hp0.trans (by rfl)
      have hcoh :
          (CochainComplex.HomComplex.homologyAddEquiv I I 0)
            ((H.homologyπ 0) (h.cyclesIso.inv c)) =
          CochainComplex.HomComplex.CohomologyClass.mk c := by
        calc
          _ = h.homologyIso.hom (S.homologyπ (h.cyclesIso.inv c)) := rfl
          _ = h.π c := by
            have hh := congrArg (fun f : S.cycles ⟶ h.H => f (h.cyclesIso.inv c))
              h.homologyπ_comp_homologyIso_hom
            have hh' :
                h.homologyIso.hom (S.homologyπ (h.cyclesIso.inv c)) =
                h.π (h.cyclesIso.hom (h.cyclesIso.inv c)) := hh
            exact hh'.trans (congrArg (fun z => (ConcreteCategory.hom h.π) z)
              (h.cyclesIso.inv_hom_id_apply c))
          _ = _ := rfl
      rw [hc', hcoh]
    have hshift (f : I ⟶ I) :
        CochainComplex.HomComplex.Cocycle.equivHomShift.symm
          (CochainComplex.HomComplex.Cocycle.ofHom f) =
        f ≫ (shiftFunctorZero (CochainComplex (ModuleCat.{max v u} k) ℤ) ℤ).inv.app I := by
      rfl
    simp [scalarToEnd, classToEnd, hclass,
      CochainComplex.HomComplex.CohomologyClass.toHom_mk, hshift,
      q0, q1, Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    simp [D, qI]
  have hclassInj : Function.Injective classToEnd := by
    intro c d h
    apply hrep.1
    have h' := congrArg (fun f : M ⟶ M => q0.hom ≫ f ≫ q1.inv) h
    simpa [classToEnd, Category.assoc] using h'
  have hScalarInj : Function.Injective scalarToEnd := by
    intro x y h
    have hs := ConcreteCategory.bijective_of_isIso sIso.inv
    have hu := ConcreteCategory.bijective_of_isIso uiso.hom
    exact hs.1 <| hb.1 <| hu.1 <| ULift.down_injective <|
      (CochainComplex.HomComplex.homologyAddEquiv I I 0).injective (hclassInj h)
  have hId : (𝟙 M) ≠ 0 := by
    intro hz
    have h := hScalarInj (show scalarToEnd (ULift.up (1 : k)) =
      scalarToEnd (ULift.up (0 : k)) by simp [hScalar, hz])
    exact one_ne_zero (congrArg ULift.down h)
  apply DerivedCategory.Invertible.simple_of_endomorphism_eq_zero_or_isIso M hId
  intro f
  obtain ⟨x, rfl⟩ := hScalarSurj f
  rw [hScalar]
  by_cases hx : x.down = 0
  · exact Or.inl (by simp [hx])
  · right
    let e : M ≅ M :=
      { hom := x.down • (𝟙 M)
        inv := x.down⁻¹ • (𝟙 M)
        hom_inv_id := by simp [hx]
        inv_hom_id := by simp [hx] }
    exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- **Stacks Project, Tag 0A7L.** Derived Hom from the residue field at a maximal ideal into a
dualizing complex is isomorphic to an integral shift of the residue field. -/
@[stacks 0A7L]
theorem derivedHom_residueField_iso_shift
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K)
    (m : Ideal A) (hm : m.IsMaximal) :
    ∃ n : ℤ, Nonempty
      ((derivedHom.{u, v, u} (Ideal.Quotient.mk m)).obj K ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} (A ⧸ m)) 0).obj
          ((ModuleCat.uliftFunctor.{v} (A ⧸ m)).obj
            (ModuleCat.of (A ⧸ m) (A ⧸ m))))⟦n⟧) := by
  let quotientRing : Ring (A ⧸ m) := inferInstance
  let _ : Field (A ⧸ m) :=
    { Ideal.Quotient.field m with
      toDivisionRing :=
        { (Ideal.Quotient.field m).toDivisionRing with toRing := quotientRing } }
  have hfinite : (Ideal.Quotient.mk m).Finite :=
    RingHom.Finite.of_surjective _ (Ideal.Quotient.mk_surjective)
  have hdual : IsDualizingComplex
      ((derivedHom.{u, v, u} (Ideal.Quotient.mk m)).obj K) :=
    isDualizingComplex_derivedHom_of_finite.{u, v}
      (Ideal.Quotient.mk m) hfinite K hK
  let D := (derivedHom.{u, v, u} (Ideal.Quotient.mk m)).obj K
  have : Simple D := simple_of_isDualizingComplex_field.{u, v} D hdual
  obtain ⟨a, b, I, hge, hle, _, ⟨eI⟩⟩ := hdual.finiteInjectiveDimension
  have := hge
  have := hle
  have : D.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eI.symm a
  have : D.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso eI.symm b
  exact simple_bounded_iso_shift_field D a b

/-- For a Noetherian local ring, derived Hom from its canonical residue field into a dualizing
complex is a shift of the residue field. This is the form the normalization condition
`Dualizing.IsNormalizedDualizingComplex` is stated against. -/
theorem derivedHom_localResidueField_iso_shift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K) :
    ∃ n : ℤ, Nonempty
      ((derivedHom.{u, v, u} (IsLocalRing.residue A)).obj K ≅
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max v u} (IsLocalRing.ResidueField A)) 0).obj
            ((ModuleCat.uliftFunctor.{v} (IsLocalRing.ResidueField A)).obj
              (ModuleCat.of (IsLocalRing.ResidueField A)
                (IsLocalRing.ResidueField A))))⟦n⟧) :=
  derivedHom_residueField_iso_shift.{u, v} K hK (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal.isMaximal A)

end Dualizing

end
