module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall

/-!
# Schemes below a cardinal cutoff in an unrelated universe

The cutoff category `Sch_κ = AlgebraicGeometry.SchemeBelow κ` is essentially small at the
universe `u` of its schemes (`AlgebraicGeometry.essentiallySmall_schemeBelow`). This file
records the same fact at an *unrelated* universe `w`, under the only hypothesis that can make
it true: that the cutoff itself is `w`-small, in the form `Small.{w} κ.out`.

A size bound `X.size < κ` bounds the affine opens of a scheme and their rings of sections. So
once `κ.out` is `w`-small, the points of such a scheme, its stalks, the morphisms between two of
them, and the isomorphism classes of all of them are `w`-small.

## Main results

* `small_of_mk_le`, `small_out_cardinalMk`, `small_mvPolynomial`: transfer of `Small.{w}`
  along a cardinal bound, to the chosen representative of a cardinal, and to a polynomial
  ring.
* `AlgebraicGeometry.Scheme.small_of_small_affineOpens`,
  `AlgebraicGeometry.Scheme.small_stalk`, `AlgebraicGeometry.Scheme.small_hom`,
  `AlgebraicGeometry.Scheme.small_of_size_le`: the underlying type, the stalks and the
  morphisms of a scheme of bounded size are `w`-small.
* `AlgebraicGeometry.locallySmall_schemeBelow`: the cutoff category is locally `w`-small.
* `AlgebraicGeometry.essentiallySmall_schemeBelow_of_small_out`: the cutoff category is
  essentially small at `w`.

## Implementation notes

Essential smallness at `w` is not deduced from essential smallness at `u`, which would need
`UnivLE.{u, w}`.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w u

/-- A type whose cardinality is bounded by a cardinal embeds into the representative of it. -/
private theorem nonempty_embedding_out_of_mk_le {α : Type u} {bound : Cardinal.{u}}
    (h : Cardinal.mk α ≤ bound) : Nonempty (α ↪ bound.out) :=
  (Cardinal.le_def _ _).mp (by rwa [Cardinal.mk_out])

/-- A type whose cardinality is bounded by a cardinal with a `w`-small representative is
itself `w`-small. -/
theorem small_of_mk_le {α : Type u} (bound : Cardinal.{u}) [Small.{w} bound.out]
    (h : Cardinal.mk α ≤ bound) : Small.{w} α :=
  small_of_injective (nonempty_embedding_out_of_mk_le h).some.injective

/-- The chosen representative of the cardinality of a `w`-small type is `w`-small. -/
theorem small_out_cardinalMk (α : Type u) [Small.{w} α] : Small.{w} (Cardinal.mk α).out :=
  small_of_injective ((Cardinal.le_def _ α).mp (Cardinal.mk_out (Cardinal.mk α)).le).some.injective

/-- A polynomial ring over the integers in `w`-small many variables is `w`-small. -/
theorem small_mvPolynomial {α : Type u} [Small.{w} α] : Small.{w} (MvPolynomial α ℤ) :=
  small_of_injective (MvPolynomial.renameEquiv ℤ (equivShrink.{w} α)).injective

namespace AlgebraicGeometry

namespace Scheme

/-- A scheme with `w`-small many affine opens has a `w`-small underlying type. -/
theorem small_of_small_affineOpens (X : Scheme.{u}) [Small.{w} X.affineOpens] :
    Small.{w} X := by
  apply small_of_injective (f := fun x : X => {U : X.affineOpens | x ∈ U.1})
  intro x y hxy
  apply Inseparable.eq
  apply X.isBasis_affineOpens.inseparable_iff.mpr
  rintro _ ⟨U, hU, rfl⟩
  exact Iff.of_eq (congrArg (fun S => (⟨U, hU⟩ : X.affineOpens) ∈ S) hxy)

/-- A stalk of a scheme with `w`-small rings of sections on affine opens is `w`-small. -/
theorem small_stalk (X : Scheme.{u})
    (hsections : ∀ U : X.affineOpens, Small.{w} Γ(X, U.1)) (x : X) :
    Small.{w} (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  let _ : Small.{w} Γ(X, U) := hsections ⟨U, hU⟩
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact small_of_surjective (IsLocalization.mk'_surjective p.asIdeal.primeCompl)

/-- The morphisms between two `w`-small schemes with `w`-small stalks form a `w`-small type. -/
theorem small_hom (X Y : Scheme.{u}) [Small.{w} X] [Small.{w} Y]
    (hX : ∀ x : X, Small.{w} (X.presheaf.stalk x))
    (hY : ∀ y : Y, Small.{w} (Y.presheaf.stalk y)) :
    Small.{w} (X ⟶ Y) := by
  let _ : ∀ x : X, Small.{w} (X.presheaf.stalk x) := hX
  let _ : ∀ y : Y, Small.{w} (Y.presheaf.stalk y) := hY
  let _ : Small.{w} X.toTopCat := ‹Small.{w} X›
  let _ : Small.{w} Y.toTopCat := ‹Small.{w} Y›
  let _ : ∀ (x : X) (y : Y), Small.{w} (Y.presheaf.stalk y ⟶ X.presheaf.stalk x) :=
    fun _ _ => small_of_injective (f := fun φ => φ.hom.toFun)
      (fun _ _ h => CommRingCat.hom_ext (RingHom.ext (congrFun h)))
  let _ : Small.{w} (X.toTopCat ⟶ Y.toTopCat) :=
    small_of_injective (f := fun φ => ⇑φ)
      (fun _ _ h => ConcreteCategory.hom_ext _ _ (congrFun h))
  let data : Type u := Σ base : X.toTopCat ⟶ Y.toTopCat,
    ∀ x : X, Y.presheaf.stalk (base x) ⟶ X.presheaf.stalk x
  let _ : Small.{w} data := inferInstance
  apply small_of_injective
    (f := fun φ : X ⟶ Y => (⟨φ.base, fun x => φ.stalkMap x⟩ : data))
  intro φ ψ hφψ
  have hbase : φ.base = ψ.base := congrArg Sigma.fst hφψ
  apply Scheme.Hom.ext'
  apply (LocallyRingedSpace.forgetToSheafedSpace).map_injective
  apply SheafedSpace.hom_stalk_ext _ _ hbase
  intro x
  have transport (b b' : X.toTopCat ⟶ Y.toTopCat)
      (m : ∀ x : X, Y.presheaf.stalk (b x) ⟶ X.presheaf.stalk x)
      (m' : ∀ x : X, Y.presheaf.stalk (b' x) ⟶ X.presheaf.stalk x)
      (hb : b = b') (hm : HEq m m') :
      m x = (Y.presheaf.stalkCongr
        ((congrArg (fun c : X.toTopCat ⟶ Y.toTopCat => c x) hb).symm ▸
          Inseparable.rfl)).hom ≫ m' x := by
    cases hb
    cases hm
    simp
  exact transport _ _ _ _ hbase (Sigma.mk.inj_iff.mp hφψ).2

/-- A scheme of size at most a cardinal with a `w`-small representative is `w`-small. -/
theorem small_of_size_le (X : Scheme.{u}) (bound : Cardinal.{u}) [Small.{w} bound.out]
    (h : X.size ≤ bound) : Small.{w} X :=
  have : Small.{w} X.affineOpens :=
    small_of_mk_le bound (X.mk_affineOpens_le_size.trans h)
  X.small_of_small_affineOpens

end Scheme

/-- The rings of sections on affine opens of a scheme of bounded size are `w`-small. -/
private theorem small_sections_of_size_le (X : Scheme.{u}) (bound : Cardinal.{u})
    [Small.{w} bound.out] (h : X.size ≤ bound) (U : X.affineOpens) : Small.{w} Γ(X, U.1) :=
  small_of_mk_le bound ((X.mk_sections_le_size U).trans h)

/-- The cutoff category of schemes is locally small at `w` as soon as the cutoff has a `w`-small
representative. -/
theorem locallySmall_schemeBelow (bound : Cardinal.{u}) [Small.{w} bound.out] :
    LocallySmall.{w} (SchemeBelow bound) := by
  refine ⟨fun X Y => ?_⟩
  let _ : Small.{w} X.obj := X.obj.small_of_size_le bound X.property.le
  let _ : Small.{w} Y.obj := Y.obj.small_of_size_le bound Y.property.le
  let _ : Small.{w} (X.obj ⟶ Y.obj) := Scheme.small_hom X.obj Y.obj
    (X.obj.small_stalk (small_sections_of_size_le _ bound X.property.le))
    (Y.obj.small_stalk (small_sections_of_size_le _ bound Y.property.le))
  exact small_of_injective (f := fun φ : X ⟶ Y => φ.hom)
    (fun _ _ h => ObjectProperty.hom_ext _ h)

/-- The cutoff category `Sch_κ` of schemes of size below `κ` is essentially small at any
universe `w` for which the cutoff has a `w`-small representative. -/
theorem essentiallySmall_schemeBelow_of_small_out (bound : Cardinal.{u})
    [Small.{w} bound.out] : EssentiallySmall.{w} (SchemeBelow bound) := by
  classical
  let carrier := Set (ULift.{u} ℕ ⊕ bound.out)
  let enlarged := Cardinal.mk carrier
  let _ : Small.{w} (ULift.{u} ℕ) := small_map Equiv.ulift
  let _ : Small.{w} carrier := inferInstance
  let _ : Small.{w} enlarged.out := small_out_cardinalMk carrier
  have bound_lt : max bound Cardinal.aleph0 < enlarged := by
    show max bound Cardinal.aleph0 < Cardinal.mk (Set (ULift.{u} ℕ ⊕ bound.out))
    rw [Cardinal.mk_set, Cardinal.mk_sum]
    simp only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.mk_out, Cardinal.lift_id]
    simpa only [Cardinal.lift_aleph0] using
      (max_le (self_le_add_left bound Cardinal.aleph0)
        (self_le_add_right Cardinal.aleph0 bound)).trans_lt
          (Cardinal.cantor (Cardinal.aleph0 + bound))
  let category := SchemeBelow enlarged
  let inclusion := schemeBelowInclusion enlarged
  let _ : LocallySmall.{w} category := locallySmall_schemeBelow enlarged
  let polynomial := MvPolynomial bound.out ℤ
  let _ : Small.{w} polynomial := small_mvPolynomial
  have quotient_size (I : Ideal polynomial) :
      (Spec (CommRingCat.of (polynomial ⧸ I))).size < enlarged := by
    rw [Scheme.size_Spec]
    refine lt_of_le_of_lt (max_le (le_max_right _ _) ?_) bound_lt
    have hpoly : Cardinal.mk polynomial ≤ max bound Cardinal.aleph0 := by
      simpa [polynomial, max_comm, max_left_comm] using
        (MvPolynomial.cardinalMk_le_max_lift (R := ℤ) (σ := bound.out))
    exact (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans hpoly
  let quotients : ObjectProperty category := ObjectProperty.ofObj
    (fun I : Ideal polynomial =>
      ⟨Spec (CommRingCat.of (polynomial ⧸ I)), quotient_size I⟩)
  let affines : ObjectProperty category := fun X =>
    ∃ R : CommRingCat.{u}, Cardinal.mk R ≤ bound ∧ Nonempty (X.obj ≅ Spec R)
  have small_affines : ObjectProperty.EssentiallySmall.{w} affines := by
    let _ : Small.{w} (Ideal polynomial) := small_of_injective
      (f := fun I : Ideal polynomial => (I : Set polynomial))
      (fun _ _ h => SetLike.coe_injective h)
    refine ⟨quotients, inferInstance, ?_⟩
    rintro X ⟨R, hR, ⟨e⟩⟩
    let embedding : R ↪ bound.out := (nonempty_embedding_out_of_mk_le hR).some
    let evaluation : polynomial →+* R :=
      MvPolynomial.eval₂Hom (Int.castRingHom R) (Function.invFun embedding)
    have hsurj : Function.Surjective evaluation := fun r =>
      ⟨MvPolynomial.X (embedding r), (MvPolynomial.eval₂Hom_X' _ _ _).trans
        (Function.leftInverse_invFun embedding.injective r)⟩
    refine ⟨_, ⟨RingHom.ker evaluation⟩, ?_⟩
    apply Nonempty.intro
    apply ObjectProperty.isoMk
    exact e ≪≫ (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (RingHom.quotientKerEquivOfSurjective hsurj)).op)
  let _ : ObjectProperty.EssentiallySmall.{w} affines := small_affines
  let closure := Order.succ (Cardinal.mk (ULift.{w} ℕ ⊕ Shrink.{w} bound.out))
  let generated := affines.colimitsCardinalClosure closure
  let bounded : ObjectProperty category := fun X => X.obj.size < bound
  have bounded_le : bounded ≤ generated := by
    intro X hX
    have hinf : Cardinal.aleph0 ≤ closure := by
      simp only [closure, Cardinal.mk_sum, Cardinal.mk_uLift, Cardinal.mk_nat,
        Cardinal.lift_id, Cardinal.lift_aleph0]
      exact (self_le_add_right _ _).trans (Order.le_succ _)
    have hopens := X.obj.mk_affineOpens_le_size.trans hX.le
    let _ : Small.{w} X.obj.AffineZariskiSite := small_of_mk_le bound hopens
    have hindex : HasCardinalLT X.obj.AffineZariskiSite closure := by
      have hbound : HasCardinalLT bound.out closure := by
        apply (hasCardinalLT_iff_of_equiv (equivShrink.{w} bound.out) closure).mpr
        rw [hasCardinalLT_iff_cardinal_mk_lt]
        exact (Cardinal.mk_le_of_injective
          (Sum.inr_injective (α := ULift.{w} ℕ))).trans_lt (Order.lt_succ _)
      let embedding : X.obj.affineOpens ↪ bound.out :=
        (nonempty_embedding_out_of_mk_le hopens).some
      exact hbound.of_injective (fun U => embedding ⟨U.1, U.2⟩)
        (fun _ _ h => Subtype.ext (congrArg Subtype.val (embedding.injective h)))
    let _ : generated.IsClosedUnderColimitsOfShape X.obj.AffineZariskiSite :=
      affines.isClosedUnderColimitsOfShape_colimitsCardinalClosure closure _
        ((hasCardinalLT_arrow_iff_of_isThin _ _ hinf).mpr hindex)
    let diagram := (schemeSizeBelow enlarged).lift
      (Scheme.AffineZariskiSite.toOpensFunctor X.obj ⋙
        X.obj.presheaf.rightOp ⋙ Scheme.Spec)
      (fun U => by
        show (Spec Γ(X.obj, U.1)).size < enlarged
        rw [Scheme.size_Spec]
        exact (max_le X.obj.aleph0_le_size
          (X.obj.mk_sections_le_size ⟨U.1, U.2⟩)).trans_lt X.property)
    let cocone : Cocone diagram :=
      { pt := X
        ι :=
          { app := fun U => ObjectProperty.homMk U.2.fromSpec
            naturality := fun U V f => by
              apply ObjectProperty.hom_ext
              exact (Scheme.AffineZariskiSite.cocone X.obj).ι.naturality f } }
    have hcolimit : IsColimit cocone := isColimitOfReflects inclusion
      (Scheme.AffineZariskiSite.isColimitCocone X.obj)
    apply generated.prop_of_isColimit hcolimit
    intro U
    apply affines.le_colimitsCardinalClosure closure
    exact ⟨_, (X.obj.mk_sections_le_size ⟨U.1, U.2⟩).trans hX.le, ⟨Iso.refl _⟩⟩
  let _ : ObjectProperty.EssentiallySmall.{w} bounded :=
    ObjectProperty.EssentiallySmall.of_le bounded_le
  let _ : EssentiallySmall.{w} bounded.FullSubcategory := inferInstance
  let comparison : SchemeBelow bound ⥤ bounded.FullSubcategory :=
    { obj := fun X => ⟨⟨X.obj, X.property.trans ((le_max_left _ _).trans_lt bound_lt)⟩,
        X.property⟩
      map := fun f => ObjectProperty.homMk (ObjectProperty.homMk f.hom) }
  let _ : comparison.Full := ⟨fun f => ⟨ObjectProperty.homMk f.hom.hom, rfl⟩⟩
  let _ : comparison.Faithful :=
    ⟨fun h => ObjectProperty.hom_ext _ (congrArg (fun k => k.hom.hom) h)⟩
  exact essentiallySmall_of_fully_faithful comparison

end AlgebraicGeometry

end
