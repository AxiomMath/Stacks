module

public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbsolutelyIntegrallyClosed.MonogenicPresentation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.MultiplicativeDeformation.CoordinateRing
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.MultiplicativeDeformation.Exactness

/-!
# A deformation of the multiplicative group: the short exact sequence of group schemes

This file packages `G^{(π)}` as a group object in schemes over `Spec A` and assembles the short
exact sequence `0 → ℤ/ℓℤ → G^{(π)} → G^{(π ^ ℓ)} → 0` over `Spec A`, for `π = ζ - 1` and `ℓ`
prime.

## Main definitions

* `AlgebraicGeometry.MultiplicativeDeformation.groupScheme` is `G^{(π)}` as a group object in
  schemes over `Spec A`, and `AlgebraicGeometry.MultiplicativeDeformation.coordinateCounit` the
  counit `x ↦ 0` of its coordinate ring.

## Main results

* `AlgebraicGeometry.MultiplicativeDeformation.exists_shortExactSequence_of_groupSchemes`
  assembles the group schemes and their canonical maps into the displayed short exact sequence
  over `Spec A`.

## Implementation notes

The final theorem explicitly packages `G^{(π)}` and `G^{(π ^ ℓ)}` as group objects over
`Spec A`, identifies their multiplication maps with the two comultiplications, identifies `f`
with the dual of `isogeny`, and identifies the map from the constant group scheme by its values
`σ_i` on every indexed component. Its pullback square is the scheme-theoretic kernel, while
flatness and surjectivity give exactness at `G^{(π ^ ℓ)}`.

## References

* [Stacks Project, Tag 0GY4](https://stacks.math.columbia.edu/tag/0GY4)
-/

@[expose] public section

open Polynomial TensorProduct CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v

namespace AlgebraicGeometry.MultiplicativeDeformation

variable {A : Type u} [CommRing A]

variable (ℓ : ℕ) [NeZero ℓ] (ζ : A) (hζ : ζ ^ ℓ = 1)
  (hsplit : ∏ i : ZMod ℓ, (X - C (ζ ^ i.val)) = X ^ ℓ - 1)

/-! ### The group schemes over `Spec A` -/

/-- Functoriality of points: an `A`-algebra map `R → S` carries `R`-points of `G^{(π)}` to
`S`-points, additively. -/
noncomputable def pointMap {π : A} {R S : Type u}
    [CommRing R] [CommRing S] [Algebra A R] [Algebra A S] (f : R →ₐ[A] S) :
    DeformedPoint π R →+ DeformedPoint π S where
  toFun x := ⟨f x.coord, by simpa using x.isUnit_one_add.map f⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The group-valued functor of points of `G^{(π)}` on `A`-algebras, written multiplicatively
so that it takes values in groups. -/
noncomputable def pointFunctor (π : A) :
    (CommAlgCat.{u} A)ᵒᵖᵒᵖ ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Multiplicative (DeformedPoint π R.unop.unop))
  map f := GrpCat.ofHom (pointMap f.unop.unop.hom).toMultiplicative
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Multiplicative.toAdd.injective
    apply DeformedPoint.ext
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Multiplicative.toAdd.injective
    apply DeformedPoint.ext
    rfl

/-- The functor of points of `G^{(π)}` is represented by its coordinate ring. -/
noncomputable def pointRepresentableBy (π : A) :
    (pointFunctor π ⋙ forget GrpCat).RepresentableBy
      (Opposite.op (CommAlgCat.of A (coordinateRing π))) where
  homEquiv {R} :=
    (Quiver.Hom.opEquiv.symm.trans ConcreteCategory.homEquiv).trans
      ((Equiv.ofBijective (pointOfAlgHom π) (pointOfAlgHom_bijective π R.unop)).trans
        Multiplicative.ofAdd)
  homEquiv_comp f g := by
    apply Multiplicative.toAdd.injective
    apply DeformedPoint.ext
    rfl

/-- The Hopf-algebra structure on the coordinate ring of `G^{(π)}`, as a group object in the
opposite category of `A`-algebras, obtained from representability of the functor of points. -/
@[instance_reducible]
noncomputable def coordinateGrpObj (π : A) :
    GrpObj (Opposite.op (CommAlgCat.of A (coordinateRing π))) :=
  GrpObj.ofRepresentableBy _ (pointFunctor π) (pointRepresentableBy π)

private lemma coordinateGrpObj_mul (π : A) :
    letI := coordinateGrpObj π
    (MonObj.mul (X := Opposite.op (CommAlgCat.of A (coordinateRing π)))).unop.hom =
      comultiplication π := by
  let := coordinateGrpObj π
  apply (pointOfAlgHom_bijective π _).injective
  show pointOfAlgHom π
    (((pointRepresentableBy π).homEquiv'.symm
      ((pointRepresentableBy π).homEquiv' (fst _ _) *
        (pointRepresentableBy π).homEquiv' (snd _ _))).unop.hom) = _
  have he := (pointRepresentableBy π).homEquiv'.apply_symm_apply
    ((pointRepresentableBy π).homEquiv' (fst _ _) *
      (pointRepresentableBy π).homEquiv' (snd _ _))
  change pointOfAlgHom π _ =
    pointOfAlgHom π (Algebra.TensorProduct.includeLeft (S := A)) +
      pointOfAlgHom π (Algebra.TensorProduct.includeRight (A := coordinateRing π)) at he
  refine he.trans ?_
  symm
  ext
  simp [coord_pointOfAlgHom, comultiplication_coordinateGenerator]

private lemma coordinateMap_isMonHom (π ρ : A)
    (f : coordinateRing ρ →ₐ[A] coordinateRing π)
    (hf : ∀ (R : CommAlgCat.{u} A) (g h : coordinateRing π →ₐ[A] R),
      pointOfAlgHom ρ
        (((Algebra.TensorProduct.lift g h (fun _ _ => Commute.all _ _)).comp
          (comultiplication π)).comp f) =
        pointOfAlgHom ρ (g.comp f) + pointOfAlgHom ρ (h.comp f)) :
    letI := coordinateGrpObj π
    letI := coordinateGrpObj ρ
    IsMonHom (CommAlgCat.ofHom f).op := by
  let := coordinateGrpObj π
  let := coordinateGrpObj ρ
  let G : Grp ((CommAlgCat.{u} A)ᵒᵖ) := ⟨Opposite.op (CommAlgCat.of A (coordinateRing π))⟩
  let H : Grp ((CommAlgCat.{u} A)ᵒᵖ) := ⟨Opposite.op (CommAlgCat.of A (coordinateRing ρ))⟩
  let eG := yonedaGrpObjIsoOfRepresentableBy G.X
    (pointFunctor π) (pointRepresentableBy π)
  let eH := yonedaGrpObjIsoOfRepresentableBy H.X
    (pointFunctor ρ) (pointRepresentableBy ρ)
  have hsymm (R : CommAlgCat.{u} A) (g : coordinateRing π →ₐ[A] R) :
      (Equiv.ofBijective (pointOfAlgHom π) (pointOfAlgHom_bijective π R)).symm
        (pointOfAlgHom π g) = g :=
    (Equiv.ofBijective (pointOfAlgHom π) (pointOfAlgHom_bijective π R)).symm_apply_apply g
  let τ : pointFunctor π ⟶ pointFunctor ρ :=
    { app R := GrpCat.ofHom (AddMonoidHom.toMultiplicative
        (AddMonoidHom.mk'
          (fun x => pointOfAlgHom ρ
            (((Equiv.ofBijective (pointOfAlgHom π)
              (pointOfAlgHom_bijective π R.unop.unop)).symm x).comp f)) (by
            intro x y
            obtain ⟨g, rfl⟩ := (pointOfAlgHom_bijective π R.unop.unop).surjective x
            obtain ⟨h, rfl⟩ := (pointOfAlgHom_bijective π R.unop.unop).surjective y
            rw [hsymm, hsymm, ← pointOfAlgHom_comp_comultiplication, hsymm]
            exact hf R.unop.unop g h)))
      naturality := by
        intro R S g
        apply GrpCat.hom_ext
        apply MonoidHom.ext
        intro x
        apply Multiplicative.toAdd.injective
        obtain ⟨x, rfl⟩ := (pointOfAlgHom_bijective π R.unop.unop).surjective x.toAdd
        show pointOfAlgHom ρ
            (((Equiv.ofBijective (pointOfAlgHom π)
              (pointOfAlgHom_bijective π S.unop.unop)).symm
                (pointOfAlgHom π (g.unop.unop.hom.comp x))).comp f) = _
        rw [hsymm]
        show pointOfAlgHom ρ ((g.unop.unop.hom.comp x).comp f) =
          pointOfAlgHom ρ (g.unop.unop.hom.comp
            (((Equiv.ofBijective (pointOfAlgHom π)
              (pointOfAlgHom_bijective π R.unop.unop)).symm (pointOfAlgHom π x)).comp f))
        rw [hsymm]
        rfl }
  let ψ : G ⟶ H := yonedaGrpFullyFaithful.preimage (eG.hom ≫ τ ≫ eH.inv)
  have hψ : ψ.hom.hom = (CommAlgCat.ofHom f).op := by
    have he := congrArg (fun t => (t.app (Opposite.op G.X)) (𝟙 G.X))
      (yonedaGrpFullyFaithful.map_preimage (eG.hom ≫ τ ≫ eH.inv))
    change ψ.hom.hom = _ at he
    refine he.trans ?_
    apply (pointRepresentableBy ρ).homEquiv'.injective
    show (pointRepresentableBy ρ).homEquiv'
      ((pointRepresentableBy ρ).homEquiv'.symm _) = _
    rw [Equiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    show pointOfAlgHom ρ
      (((Equiv.ofBijective (pointOfAlgHom π)
        (pointOfAlgHom_bijective π (coordinateRing π))).symm
          (pointOfAlgHom π (AlgHom.id A _))).comp f) = pointOfAlgHom ρ f
    have hi := (Equiv.ofBijective (pointOfAlgHom π)
      (pointOfAlgHom_bijective π (coordinateRing π))).symm_apply_apply (AlgHom.id A _)
    change (Equiv.ofBijective (pointOfAlgHom π)
      (pointOfAlgHom_bijective π (coordinateRing π))).symm
        (pointOfAlgHom π (AlgHom.id A _)) = AlgHom.id A _ at hi
    rw [hi, AlgHom.id_comp]
  rw [← hψ]
  infer_instance

/-- The map `isogeny` of coordinate rings is a homomorphism of Hopf algebras, that is its dual
is a homomorphism of group objects. -/
lemma isogeny_isMonHom :
    letI := coordinateGrpObj (ζ - 1)
    letI := coordinateGrpObj ((ζ - 1) ^ ℓ)
    IsMonHom (CommAlgCat.ofHom (isogeny ℓ ζ hsplit)).op := by
  apply coordinateMap_isMonHom
  intro R g h
  rw [pointOfAlgHom_comp_isogeny, pointOfAlgHom_comp_comultiplication,
    isogenyOnPoints_add, pointOfAlgHom_comp_isogeny, pointOfAlgHom_comp_isogeny]

/-- `Spec` as a functor from `A`-algebras to schemes over `Spec A` is monoidal. Mathlib proves
this as `AlgebraicGeometry.braidedAlgSpec`, but instance search does not find that instance for
the ring `CommRingCat.of A`, so it is recorded here in the form the construction below needs. -/
@[instance_reducible]
noncomputable def algSpecMonoidal : (algSpec (CommRingCat.of A)).Monoidal :=
  (braidedAlgSpec (R := CommRingCat.of A)).toMonoidal

attribute [local instance] algSpecMonoidal

/-- The group scheme `G^{(π)} = Spec A[x, 1/(πx + 1)]` over `Spec A`, with the group law
`x + y = πxy + x + y` on points. -/
noncomputable def groupScheme (π : A) : Grp (Over (Spec (.of A))) :=
  letI := coordinateGrpObj π
  { X := (Spec (.of (coordinateRing π))).asOver (Spec (.of A))
    grp := by
      change GrpObj ((algSpec (.of A)).obj (Opposite.op (CommAlgCat.of A (coordinateRing π))))
      exact ((algSpec (.of A)).mapGrp.obj
        ⟨Opposite.op (CommAlgCat.of A (coordinateRing π))⟩).grp }

/-- The multiplication of `G^{(π)}` is, under the canonical affine fibre-product isomorphism,
the morphism dual to the comultiplication. -/
lemma groupScheme_mul (π : A) :
    (MonObj.mul (X := (groupScheme π).X)).left =
      (pullbackSpecIso A (coordinateRing π) (coordinateRing π)).hom ≫
        Spec.map (CommRingCat.ofHom (comultiplication π).toRingHom) := by
  let := coordinateGrpObj π
  show (Functor.LaxMonoidal.μ (algSpec (.of A)) _ _ ≫
    (algSpec (.of A)).map (MonObj.mul (X := Opposite.op
      (CommAlgCat.of A (coordinateRing π))))).left = _
  rw [Over.comp_left, μ_algSpec_left, algSpec_map_left]
  congr 2
  exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom (coordinateGrpObj_mul π))

/-- The counit `x ↦ 0` of the coordinate ring of `G^{(π)}`, dual to the origin. -/
noncomputable def coordinateCounit (π : A) : coordinateRing π →ₐ[A] A :=
  IsLocalization.Away.liftAlgHom (C π * X + 1) (f := aeval (0 : A)) (by simp)

/-- The counit sends the generator to zero. -/
lemma coordinateCounit_generator (π : A) :
    coordinateCounit π (coordinateGenerator π) = 0 := by
  simp [coordinateCounit, coordinateGenerator, IsLocalization.Away.liftAlgHom,
    IsLocalization.Away.lift]

private lemma coordinateGrpObj_one (π : A) :
    letI := coordinateGrpObj π
    (MonObj.one (X := Opposite.op (CommAlgCat.of A (coordinateRing π)))).unop.hom =
      coordinateCounit π := by
  let := coordinateGrpObj π
  apply (pointOfAlgHom_bijective π A).injective
  have he := (pointRepresentableBy π).homEquiv'.apply_symm_apply
    (1 : (pointFunctor π).obj (Opposite.op (𝟙_ (CommAlgCat.{u} A)ᵒᵖ)))
  change pointOfAlgHom π _ = 0 at he
  exact he.trans (DeformedPoint.ext (coordinateCounit_generator π).symm)

/-- The point of `algSpec` given by a morphism out of the unit is the spectrum of its dual. -/
private lemma ε_comp_algSpec_map_left {B : Type u} [CommRing B] [Algebra A B]
    (f : 𝟙_ (CommAlgCat.{u} A)ᵒᵖ ⟶ Opposite.op (CommAlgCat.of A B)) :
    (Functor.LaxMonoidal.ε (algSpec (.of A)) ≫ (algSpec (.of A)).map f).left =
      Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) := by
  rw [Over.comp_left, ε_algSpec_left]
  refine (Category.id_comp _).trans ?_
  rw [algSpec_map_left]
  rfl

/-- The unit of `G^{(π)}` is the morphism dual to the counit. -/
lemma groupScheme_one (π : A) :
    (MonObj.one (X := (groupScheme π).X)).left =
      Spec.map (CommRingCat.ofHom (coordinateCounit π).toRingHom) := by
  let := coordinateGrpObj π
  refine (ε_comp_algSpec_map_left
    (MonObj.one (X := Opposite.op (CommAlgCat.of A (coordinateRing π))))).trans ?_
  congr 1
  exact congrArg CommRingCat.ofHom (congrArg AlgHom.toRingHom (coordinateGrpObj_one π))

private lemma coordinateAlgHom_ext {π : A} {R : Type v} [CommRing R] [Algebra A R]
    {f g : coordinateRing π →ₐ[A] R}
    (h : f (coordinateGenerator π) = g (coordinateGenerator π)) : f = g :=
  IsLocalization.algHom_ext (Submonoid.powers (C π * X + 1)) (Polynomial.algHom_ext h)

private lemma comp_isogeny_eq_counit_iff {R : Type v} [CommRing R] [Algebra A R]
    (g : coordinateRing (ζ - 1) →ₐ[A] R) :
    g.comp (isogeny ℓ ζ hsplit) = (Algebra.ofId A R).comp (coordinateCounit ((ζ - 1) ^ ℓ)) ↔
      g (isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))) = 0 := by
  refine ⟨fun h => ?_, fun h => coordinateAlgHom_ext ?_⟩
  · simpa only [AlgHom.comp_apply, coordinateCounit_generator, map_zero] using
      AlgHom.congr_fun h (coordinateGenerator ((ζ - 1) ^ ℓ))
  · simpa only [AlgHom.comp_apply, coordinateCounit_generator, map_zero] using h

private noncomputable def kernelAlgHomEquiv (R : Type v) [CommRing R] [Algebra A R] :
    (kernelCoordinateRing ℓ ζ hsplit →ₐ[A] R) ≃
      {g : coordinateRing (ζ - 1) →ₐ[A] R //
        g.comp (isogeny ℓ ζ hsplit) =
          (Algebra.ofId A R).comp (coordinateCounit ((ζ - 1) ^ ℓ))} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ A _), by
    rw [comp_isogeny_eq_counit_iff]
    change g ((Ideal.Quotient.mk _)
      (isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ)))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)),
      map_zero]⟩
  invFun g := Ideal.Quotient.liftₐ _ g.val (by
    change Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))} ≤
      RingHom.ker g.val.toRingHom
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      ((comp_isogeny_eq_counit_iff ℓ ζ hsplit g.val).mp g.property))
  left_inv g := by
    apply Ideal.Quotient.algHom_ext
    exact Ideal.Quotient.liftₐ_comp _ _ _
  right_inv g := Subtype.ext (Ideal.Quotient.liftₐ_comp _ _ _)

private lemma kernel_isPullback :
    IsPullback
      (CommAlgCat.ofHom (Ideal.Quotient.mkₐ A
        (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))}))).op
      (toUnit _) (CommAlgCat.ofHom (isogeny ℓ ζ hsplit)).op
      (CommAlgCat.ofHom (coordinateCounit ((ζ - 1) ^ ℓ))).op := by
  let i := (CommAlgCat.ofHom (Ideal.Quotient.mkₐ A
    (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))}))).op
  let f := (CommAlgCat.ofHom (isogeny ℓ ζ hsplit)).op
  let o := (CommAlgCat.ofHom (coordinateCounit ((ζ - 1) ^ ℓ))).op
  have comm : i ≫ f = toUnit _ ≫ o := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact (kernelAlgHomEquiv ℓ ζ hsplit (kernelCoordinateRing ℓ ζ hsplit)
      (AlgHom.id A _)).property
  have compat (s : PullbackCone f o) :
      s.fst.unop.hom.comp (isogeny ℓ ζ hsplit) =
        (Algebra.ofId A s.pt.unop).comp (coordinateCounit ((ζ - 1) ^ ℓ)) := by
    have he := congrArg (fun g => g.unop.hom) s.condition
    change s.fst.unop.hom.comp (isogeny ℓ ζ hsplit) =
      s.snd.unop.hom.comp (coordinateCounit ((ζ - 1) ^ ℓ)) at he
    rwa [show s.snd.unop.hom = Algebra.ofId A s.pt.unop from Subsingleton.elim _ _] at he
  let lift (s : PullbackCone f o) :=
    (CommAlgCat.ofHom ((kernelAlgHomEquiv ℓ ζ hsplit s.pt.unop).symm
      ⟨s.fst.unop.hom, compat s⟩)).op
  have fac (s : PullbackCone f o) : lift s ≫ i = s.fst := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact congrArg Subtype.val ((kernelAlgHomEquiv ℓ ζ hsplit s.pt.unop).apply_symm_apply
      ⟨s.fst.unop.hom, compat s⟩)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm lift fac
    (fun _ => Subsingleton.elim _ _) (by
      intro s m hm _
      apply Quiver.Hom.unop_inj
      apply CommAlgCat.hom_ext
      apply (kernelAlgHomEquiv ℓ ζ hsplit s.pt.unop).injective
      apply Subtype.ext
      show m.unop.hom.comp (Ideal.Quotient.mkₐ A _) = _
      exact congrArg (fun g => g.unop.hom) (hm.trans (fac s).symm)))

/-- The morphism of group schemes `f : G^{(ζ - 1)} → G^{((ζ - 1) ^ ℓ)}` over `Spec A`. -/
noncomputable def isogenyGroupSchemeHom :
    groupScheme (ζ - 1) ⟶ groupScheme ((ζ - 1) ^ ℓ) := by
  letI := coordinateGrpObj (ζ - 1)
  letI := coordinateGrpObj ((ζ - 1) ^ ℓ)
  letI := isogeny_isMonHom ℓ ζ hsplit
  exact (algSpec (.of A)).mapGrp.map
    (Grp.ofHom (CommAlgCat.ofHom (isogeny ℓ ζ hsplit)).op)

/-- The morphism `f` of group schemes is dual to the map `isogeny` of coordinate rings. -/
lemma isogenyGroupSchemeHom_left :
    (isogenyGroupSchemeHom ℓ ζ hsplit).hom.hom.left =
      Spec.map (CommRingCat.ofHom (isogeny ℓ ζ hsplit).toRingHom) := rfl

private lemma isogenyGroupSchemeHom_flat_surjective :
    Flat (isogenyGroupSchemeHom ℓ ζ hsplit).hom.hom.left ∧
      Surjective (isogenyGroupSchemeHom ℓ ζ hsplit).hom.hom.left :=
  (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (isogeny ℓ ζ hsplit).toRingHom)).mpr
    (isogeny_faithfullyFlat ℓ ζ hsplit)

omit [NeZero ℓ] in
private lemma constantComponentOver_left (j : Multiplicative (ZMod ℓ)) :
    (constantComponentOver (A := A) ℓ j).left =
      pullback.lift
        (f := terminal.from
          (constantSchemeOverIntegers.{u, 0} (Multiplicative (ZMod ℓ))))
        (g := terminal.from (Spec (.of A)))
        (terminal.from (Spec (.of A)) ≫ Sigma.ι (fun _ : Multiplicative (ZMod ℓ) =>
          ⊤_ Scheme.{u}) j) (𝟙 _) (by simp) := by
  apply pullback.hom_ext <;> simp [constantComponentOver, Over.mapPullbackAdj]

section

/-! The constant group scheme over `Spec A` is the fibre product
`(∐ Spec ℤ) ×_{Spec ℤ} Spec A`, and the statements below present that fibre product both
through the group object it carries and through the pullback cone itself. Identifying the two
presentations is a matter of unfolding definitions, which the elaborator does only with the
transparency check switched off; the same option is used for the same reason in Mathlib's own
`AlgebraicGeometry.Limits` and `CategoryTheory.Comma.Over.Pullback`. -/
set_option backward.isDefEq.respectTransparency false

private noncomputable def constantComponentsIsColimit :
    IsColimit (Cofan.mk _ (fun j : Multiplicative (ZMod ℓ) =>
      (constantComponentOver (A := A) ℓ j).left)) := by
  let S := Spec (CommRingCat.of A)
  let T := ⊤_ Scheme.{u}
  let C := constantSchemeOverIntegersObj.{u, 0} (Multiplicative (ZMod ℓ))
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun _ : Multiplicative (ZMod ℓ) => T))
  apply Nonempty.some
  refine hu.nonempty_isColimit_of_isPullback_right
    (fun _ => 𝟙 T) C.hom (terminal.from S)
    (fun _ => terminal.from S) (fun _ => 𝟙 S)
    (fun _ => IsPullback.of_vert_isIso ⟨by simp⟩)
    (IsPullback.of_hasPullback C.hom (terminal.from S)) _ (Iso.refl _) ?_ ?_ ?_
  · exact fun j => terminal.hom_ext _ _
  · intro j
    simp [constantComponentOver_left, C, S, T]
  · intro j
    simp [constantComponentOver_left, C, S]

private lemma constantComponents_hom_ext {Y : Over (Spec (.of A))}
    {f g : (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X ⟶ Y}
    (h : ∀ j, constantComponentOver ℓ j ≫ f = constantComponentOver ℓ j ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply Cofan.IsColimit.hom_ext (constantComponentsIsColimit (A := A) ℓ)
  intro j
  exact congrArg Over.Hom.left (h j)

omit [NeZero ℓ] in
private lemma constantComponentOver_eq (j : Multiplicative (ZMod ℓ)) :
    constantComponentOver (A := A) ℓ j =
      Functor.LaxMonoidal.ε (Over.pullback (terminal.from (Spec (.of A)))) ≫
        (Over.pullback (terminal.from (Spec (.of A)))).map
          (constantComponent.{u, 0} (Multiplicative (ZMod ℓ)) j) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp [constantComponentOver_left, Over.ε_pullback_left, Over.pullback_map_left]

/-- Multiplying two points pushed forward along a monoidal functor is pushing forward the
product. -/
private lemma lift_ε_map_comp_mul {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {M : C} [MonObj M] (a b : 𝟙_ C ⟶ M) :
    lift (Functor.LaxMonoidal.ε F ≫ F.map a) (Functor.LaxMonoidal.ε F ≫ F.map b) ≫
        (Functor.LaxMonoidal.μ F M M ≫ F.map MonObj.mul) =
      Functor.LaxMonoidal.ε F ≫ F.map (lift a b ≫ MonObj.mul) := by
  rw [← comp_lift, Category.assoc, ← Functor.OplaxMonoidal.lift_δ, Category.assoc,
    Functor.Monoidal.δ_μ_assoc, ← F.map_comp]

omit [NeZero ℓ] in
private lemma constantComponentOver_mul (i j : Multiplicative (ZMod ℓ)) :
    lift (constantComponentOver (A := A) ℓ i) (constantComponentOver ℓ j) ≫
      MonObj.mul = constantComponentOver ℓ (i * j) := by
  let F := Over.pullback (terminal.from (Spec (.of A)))
  let C := constantSchemeOverIntegersObj.{u, 0} (Multiplicative (ZMod ℓ))
  let c := constantComponent.{u, 0} (Multiplicative (ZMod ℓ))
  have hc : lift (c i) (c j) ≫ MonObj.mul = c (i * j) :=
    (constantGroupSchemeStructure.{u, 0} (Multiplicative (ZMod ℓ))).property i j
  rw [constantComponentOver_eq, constantComponentOver_eq, constantComponentOver_eq]
  show lift (Functor.LaxMonoidal.ε F ≫ F.map (c i))
    (Functor.LaxMonoidal.ε F ≫ F.map (c j)) ≫
      (Functor.LaxMonoidal.μ F C C ≫ F.map MonObj.mul) = _
  rw [lift_ε_map_comp_mul, hc]

private noncomputable def constantComponentPairsIsColimit :
    IsColimit (Cofan.mk _ (fun p : Multiplicative (ZMod ℓ) × Multiplicative (ZMod ℓ) =>
      (lift (constantComponentOver (A := A) ℓ p.1) (constantComponentOver ℓ p.2)).left)) := by
  let C := (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (constantComponentsIsColimit (A := A) ℓ)
  have hP : ∀ (_ _ : Multiplicative (ZMod ℓ)),
      IsPullback (𝟙 (Spec (.of A))) (𝟙 (Spec (.of A)))
        (𝟙 (Spec (.of A))) (𝟙 (Spec (.of A))) :=
    fun _ _ => IsPullback.of_vert_isIso ⟨rfl⟩
  apply Nonempty.some
  refine hu.nonempty_isColimit_prod_of_isPullback hu
    (fun _ => 𝟙 _) (fun _ => 𝟙 _) C.hom C.hom
    (q₁ := fun _ _ => 𝟙 (Spec (.of A))) (q₂ := fun _ _ => 𝟙 (Spec (.of A)))
    hP
    (IsPullback.of_hasPullback C.hom C.hom) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact fun i => Over.w (constantComponentOver ℓ i)
  · exact fun i => Over.w (constantComponentOver ℓ i)
  all_goals
    intro i j
    simp [C]

/-- The canonical map from a finite coproduct of spectra to the spectrum of the product is an
isomorphism. This is the Mathlib instance `AlgebraicGeometry.instIsIsoSigmaSpec` with the index
type allowed to live in a universe of its own. -/
private lemma sigmaSpec_isIso {ι : Type} [Finite ι] (R : ι → CommRingCat.{u}) :
    IsIso (sigmaSpec R) := by
  let c := Fan.mk (CommRingCat.of (∀ i, R i))
    (fun i => CommRingCat.ofHom (Pi.evalRingHom (fun i => R i) i))
  have hc : IsLimit c := Fan.IsLimit.mk _
    (fun s => CommRingCat.ofHom (RingHom.pi (fun i => (s.proj i).hom)))
    (fun s i => by ext x; rfl)
    (fun s m hm => by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      funext i
      exact congrArg (fun f : s.pt ⟶ R i => f.hom x) (hm i))
  have he : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm (isColimitOfPreserves
          Scheme.Spec (Fan.IsLimit.op hc))⟩).hom := by
    ext1
    simp
    rfl
  rw [he]
  exact Iso.isIso_hom _

omit hζ hsplit in
private lemma exists_constantSchemeIsoSpecPi :
    ∃ σ : (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X ≅
        (Spec (.of (ZMod ℓ → A))).asOver (Spec (.of A)),
      ∀ j : Multiplicative (ZMod ℓ),
        (constantComponentOver (A := A) ℓ j).left ≫
            (σ.hom.left :
              (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X.left ⟶
                Spec (CommRingCat.of (ZMod ℓ → A))) =
          Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ZMod ℓ => A) j.toAdd)) := by
  let e := (constantComponentsIsColimit (A := A) ℓ).coconePointUniqueUpToIso
    (coproductIsCoproduct (fun _ : Multiplicative (ZMod ℓ) => Spec (.of A)))
  obtain ⟨g, hg⟩ : ∃ g : (∐ fun _ : Multiplicative (ZMod ℓ) => Spec (CommRingCat.of A)) ≅
      Spec (CommRingCat.of (ZMod ℓ → A)),
      g.hom = sigmaSpec (fun _ : Multiplicative (ZMod ℓ) => CommRingCat.of A) :=
    ⟨@asIso _ _ _ _ (sigmaSpec (fun _ : Multiplicative (ZMod ℓ) => CommRingCat.of A))
      (sigmaSpec_isIso _), rfl⟩
  have hcomp : ∀ j : Multiplicative (ZMod ℓ),
      (constantComponentOver (A := A) ℓ j).left ≫ (e ≪≫ g).hom =
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ZMod ℓ => A) j.toAdd)) := by
    intro j
    have he : (constantComponentOver (A := A) ℓ j).left ≫ e.hom =
        Sigma.ι (fun _ : Multiplicative (ZMod ℓ) => Spec (.of A)) j :=
      (constantComponentsIsColimit (A := A) ℓ).comp_coconePointUniqueUpToIso_hom _ ⟨j⟩
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    rw [he, hg]
    exact ι_sigmaSpec (fun _ : Multiplicative (ZMod ℓ) => CommRingCat.of A) j
  refine ⟨Over.isoMk (e ≪≫ g) ?_, ?_⟩
  · apply Cofan.IsColimit.hom_ext (constantComponentsIsColimit (A := A) ℓ)
    intro j
    have hw : (constantComponentOver (A := A) ℓ j).left ≫
        ((e ≪≫ g).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (ZMod ℓ → A)))) =
        (constantComponentOver (A := A) ℓ j).left ≫
          (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X.hom := by
      rw [← Category.assoc, hcomp j, ← Spec.map_comp]
      have hc : (CommRingCat.ofHom (algebraMap A (ZMod ℓ → A))) ≫
          CommRingCat.ofHom (Pi.evalRingHom (fun _ : ZMod ℓ => A) j.toAdd) =
          𝟙 (CommRingCat.of A) := rfl
      rw [hc, Spec.map_id]
      exact (Over.w (constantComponentOver (A := A) ℓ j)).symm
    exact hw
  · exact hcomp

open scoped CategoryTheory.MonObj

/-- A point `f` of a group object with `f * f = f` is the unit. -/
private lemma eq_one_of_lift_mul_eq {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {M : C} [GrpObj M] (f : 𝟙_ C ⟶ M) (h : lift f f ≫ MonObj.mul = f) : f = MonObj.one := by
  have he : f = 1 := mul_left_cancel ((by simpa only [Hom.mul_def] using h : f * f = f).trans
    (mul_one _).symm)
  simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using he

private noncomputable def pointAlgHom (π : A) (x : DeformedPoint π A) :
    coordinateRing π →ₐ[A] A :=
  (Equiv.ofBijective (pointOfAlgHom π) (pointOfAlgHom_bijective π A)).symm x

private lemma pointAlgHom_spec (π : A) (x : DeformedPoint π A) :
    pointOfAlgHom π (pointAlgHom π x) = x :=
  (Equiv.ofBijective (pointOfAlgHom π) (pointOfAlgHom_bijective π A)).apply_symm_apply x

private lemma pointAlgHom_generator (π : A) (x : DeformedPoint π A) :
    pointAlgHom π x (coordinateGenerator π) = x.coord :=
  congrArg DeformedPoint.coord (pointAlgHom_spec π x)

private noncomputable def pointSection (π : A) (x : DeformedPoint π A) :
    𝟙_ (Over (Spec (.of A))) ⟶ (groupScheme π).X :=
  Functor.LaxMonoidal.ε (algSpec (.of A)) ≫
    (algSpec (.of A)).map (CommAlgCat.ofHom (pointAlgHom π x)).op

private lemma pointSection_mul (π : A) (x y : DeformedPoint π A) :
    lift (pointSection π x) (pointSection π y) ≫ MonObj.mul = pointSection π (x + y) := by
  let := coordinateGrpObj π
  let sx := (CommAlgCat.ofHom (pointAlgHom π x)).op
  let sy := (CommAlgCat.ofHom (pointAlgHom π y)).op
  have hxy : lift sx sy ≫ MonObj.mul = (CommAlgCat.ofHom (pointAlgHom π (x + y))).op := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply (pointOfAlgHom_bijective π A).injective
    show pointOfAlgHom π
      ((Algebra.TensorProduct.lift (pointAlgHom π x) (pointAlgHom π y)
        (fun _ _ => Commute.all _ _)).comp
          (MonObj.mul (X := Opposite.op (CommAlgCat.of A (coordinateRing π)))).unop.hom) =
            pointOfAlgHom π (pointAlgHom π (x + y))
    rw [coordinateGrpObj_mul, pointOfAlgHom_comp_comultiplication,
      pointAlgHom_spec, pointAlgHom_spec, pointAlgHom_spec]
  let F := algSpec (CommRingCat.of A)
  show lift (Functor.LaxMonoidal.ε F ≫ F.map sx)
    (Functor.LaxMonoidal.ε F ≫ F.map sy) ≫
    (Functor.LaxMonoidal.μ F _ _ ≫ F.map MonObj.mul) = _
  rw [lift_ε_map_comp_mul, hxy]
  rfl

private lemma pointSection_zero (π : A) :
    pointSection π 0 = (MonObj.one : 𝟙_ (Over (Spec (.of A))) ⟶ (groupScheme π).X) := by
  exact eq_one_of_lift_mul_eq _ (by simpa only [zero_add] using pointSection_mul π 0 0)

omit [NeZero ℓ] in
private lemma constantComponentOver_one :
    constantComponentOver (A := A) ℓ 1 = MonObj.one := by
  exact eq_one_of_lift_mul_eq _
    (by simpa only [one_mul] using constantComponentOver_mul (A := A) ℓ 1 1)

private noncomputable def constantPointsMap :
    (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X ⟶
      (groupScheme (ζ - 1)).X :=
  Over.homMk ((constantComponentsIsColimit (A := A) ℓ).desc (Cofan.mk _
    (fun j => (pointSection (ζ - 1) (constantPoint ℓ ζ hζ j.toAdd)).left))) (by
      apply Cofan.IsColimit.hom_ext (constantComponentsIsColimit (A := A) ℓ)
      intro j
      rw [← Category.assoc]
      dsimp only [Cofan.inj]
      rw [IsColimit.fac]
      exact (Over.w (pointSection (ζ - 1) (constantPoint ℓ ζ hζ j.toAdd))).trans
        (Over.w (constantComponentOver (A := A) ℓ j)).symm)

private lemma constantComponentOver_pointsMap (j : Multiplicative (ZMod ℓ)) :
    constantComponentOver (A := A) ℓ j ≫ constantPointsMap ℓ ζ hζ =
      pointSection (ζ - 1) (constantPoint ℓ ζ hζ j.toAdd) :=
  Over.OverMorphism.ext ((constantComponentsIsColimit (A := A) ℓ).fac _ ⟨j⟩)

/-- The closed immersion of the constant group scheme of `ℤ/ℓℤ` over `Spec A` into
`G^{(ζ - 1)}` which sends the component indexed by `i` to the point `σ_i`. -/
private noncomputable def constantPointsGroupHom :
    constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A)) ⟶ groupScheme (ζ - 1) := by
  refine Grp.homMk'' (constantPointsMap ℓ ζ hζ) ?_ ?_
  · rw [← constantComponentOver_one, constantComponentOver_pointsMap]
    have hz : constantPoint ℓ ζ hζ (0 : ZMod ℓ) = 0 := by ext; simp [sigmaPoint]
    change pointSection (ζ - 1) (constantPoint ℓ ζ hζ 0) = _
    rw [hz, pointSection_zero]
  · apply Over.OverMorphism.ext
    apply Cofan.IsColimit.hom_ext (constantComponentPairsIsColimit (A := A) ℓ)
    rintro ⟨i, j⟩
    change (CartesianMonoidalCategory.lift (constantComponentOver (A := A) ℓ i)
        (constantComponentOver ℓ j) ≫ MonObj.mul ≫ constantPointsMap ℓ ζ hζ).left =
      (CartesianMonoidalCategory.lift (constantComponentOver (A := A) ℓ i)
        (constantComponentOver ℓ j) ≫
          (constantPointsMap ℓ ζ hζ ⊗ₘ constantPointsMap ℓ ζ hζ) ≫ MonObj.mul).left
    congr 1
    rw [← Category.assoc, constantComponentOver_mul, constantComponentOver_pointsMap,
      ← Category.assoc, lift_map, constantComponentOver_pointsMap,
      constantComponentOver_pointsMap, pointSection_mul]
    rw [← constantPoint_add ℓ ζ hζ hsplit]
    rfl

private lemma constantPointsGroupHom_hom :
    (constantPointsGroupHom ℓ ζ hζ hsplit).hom.hom = constantPointsMap ℓ ζ hζ := rfl

private lemma pointSection_left (π : A) (x : DeformedPoint π A) :
    (pointSection π x).left = Spec.map (CommRingCat.ofHom (pointAlgHom π x).toRingHom) := by
  exact ε_comp_algSpec_map_left (CommAlgCat.ofHom (pointAlgHom π x)).op

private lemma exists_constantKernelIso
    (e : kernelCoordinateRing ℓ ζ hsplit ≃ₐ[A] (ZMod ℓ → A))
    (he : ∀ j : ZMod ℓ,
      e (Ideal.Quotient.mk _ (coordinateGenerator (ζ - 1))) j = sigmaPoint ℓ ζ j) :
    ∃ κ : (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X ≅
        (algSpec (.of A)).obj
          (Opposite.op (CommAlgCat.of A (kernelCoordinateRing ℓ ζ hsplit))),
      κ.hom ≫ (algSpec (.of A)).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ A
          (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))}))).op =
        constantPointsMap ℓ ζ hζ := by
  obtain ⟨σ, hσ⟩ := exists_constantSchemeIsoSpecPi (A := A) ℓ
  refine ⟨σ ≪≫ (algSpec (.of A)).mapIso (CommAlgCat.isoMk e).op, ?_⟩
  apply constantComponents_hom_ext ℓ
  intro j
  refine Eq.trans ?_ (constantComponentOver_pointsMap ℓ ζ hζ j).symm
  apply Over.OverMorphism.ext
  have hh : ((Pi.evalAlgHom A (fun _ : ZMod ℓ => A) j.toAdd).comp e.toAlgHom).comp
      (Ideal.Quotient.mkₐ A
        (Ideal.span {isogeny ℓ ζ hsplit (coordinateGenerator ((ζ - 1) ^ ℓ))})) =
      pointAlgHom (ζ - 1) (constantPoint ℓ ζ hζ j.toAdd) := by
    apply coordinateAlgHom_ext
    show e (Ideal.Quotient.mk _ (coordinateGenerator (ζ - 1))) j.toAdd = _
    rw [he, pointAlgHom_generator, coord_constantPoint]
  have key : (constantComponentOver (A := A) ℓ j).left ≫
      ((σ.hom.left :
            (constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A))).X.left ⟶
              Spec (CommRingCat.of (ZMod ℓ → A))) ≫
          Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ A
          (Ideal.span {isogeny ℓ ζ hsplit
            (coordinateGenerator ((ζ - 1) ^ ℓ))})).toRingHom) =
      (pointSection (ζ - 1) (constantPoint ℓ ζ hζ j.toAdd)).left := by
    rw [Category.assoc, ← Category.assoc, hσ j, pointSection_left,
      ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (congrArg AlgHom.toRingHom hh))
  exact key

end

private lemma constantPoints_isPullback (hℓ : ℓ.Prime) :
    IsPullback (constantPointsGroupHom ℓ ζ hζ hsplit).hom.hom (toUnit _)
      (isogenyGroupSchemeHom ℓ ζ hsplit).hom.hom
      (MonObj.one : 𝟙_ (Over (Spec (.of A))) ⟶ (groupScheme ((ζ - 1) ^ ℓ)).X) := by
  obtain ⟨e, he⟩ := kernelCoordinateRing_algEquiv_pi ℓ ζ hsplit hℓ
  obtain ⟨κ, hκ⟩ := exists_constantKernelIso ℓ ζ hζ hsplit e he
  let : PreservesLimitsOfSize.{0, 0} (algSpec (.of A)) := preservesLimitsOfSize_algSpec
  have hpb := (kernel_isPullback ℓ ζ hsplit).map (algSpec (.of A))
  refine hpb.of_iso' κ (Iso.refl _)
    (asIso (Functor.LaxMonoidal.ε (algSpec (.of A)))) (Iso.refl _) ?_ ?_ ?_ ?_
  · refine Eq.trans ?_ (Category.comp_id _).symm
    rw [constantPointsGroupHom_hom]
    exact hκ
  · apply (cancel_mono (inv (Functor.LaxMonoidal.ε (algSpec (.of A))))).mp
    exact Subsingleton.elim _ _
  · simp only [Iso.refl_hom]
    rfl
  · apply Over.OverMorphism.ext
    refine Eq.trans ?_ (congrArg Over.Hom.left (Category.comp_id _)).symm
    rw [Over.comp_left, asIso_hom, ε_algSpec_left]
    refine (Category.id_comp _).trans ?_
    rw [algSpec_map_left]
    exact (groupScheme_one ((ζ - 1) ^ ℓ)).symm

/-- The short exact sequence `0 → ℤ/ℓℤ → G^{(ζ - 1)} → G^{((ζ - 1) ^ ℓ)} → 0` is a sequence of
group schemes over `Spec A`, not merely a sequence of groups of `A`-points. The left-hand group
scheme is the constant group scheme of `ℤ/ℓℤ`; the right-hand map is the scheme morphism dual
to the explicitly specified algebra homomorphism `isogeny`. The coordinate of the left-hand map
is pinned to the points `σ_i`, and the pullback square says that it identifies the constant
group scheme with the kernel. -/
@[stacks 0GY4]
theorem exists_shortExactSequence_of_groupSchemes (hℓ : ℓ.Prime) :
    ∃ (g : Grp (Over (Spec (.of A)))) (h : Grp (Over (Spec (.of A))))
      (i : constantGroupScheme (Multiplicative (ZMod ℓ)) (Spec (.of A)) ⟶ g) (f : g ⟶ h),
      ∃ (eg : g.X ≅ (Spec (.of (coordinateRing (ζ - 1)))).asOver (Spec (.of A)))
        (eh : h.X ≅ (Spec (.of (coordinateRing ((ζ - 1) ^ ℓ)))).asOver (Spec (.of A))),
        (((eg.inv ⊗ₘ eg.inv) ≫ MonObj.mul (X := g.X) ≫ eg.hom).left =
          (pullbackSpecIso A (coordinateRing (ζ - 1)) (coordinateRing (ζ - 1))).hom ≫
            Spec.map (CommRingCat.ofHom (comultiplication (ζ - 1)).toRingHom)) ∧
        (((eh.inv ⊗ₘ eh.inv) ≫ MonObj.mul (X := h.X) ≫ eh.hom).left =
          (pullbackSpecIso A (coordinateRing ((ζ - 1) ^ ℓ))
            (coordinateRing ((ζ - 1) ^ ℓ))).hom ≫
            Spec.map (CommRingCat.ofHom (comultiplication ((ζ - 1) ^ ℓ)).toRingHom)) ∧
        (CategoryTheory.IsPullback i.hom.hom (toUnit _)
          f.hom.hom (MonObj.one : (𝟙_ (Over (Spec (.of A)))) ⟶ h.X)) ∧
        (Flat f.hom.hom.left ∧ Surjective f.hom.hom.left) ∧
        (eg.inv ≫ f.hom.hom ≫ eh.hom).left =
          Spec.map (CommRingCat.ofHom (isogeny ℓ ζ hsplit).toRingHom) ∧
        (∀ j : ZMod ℓ,
          (Spec.preimage
            (constantComponentOver (A := A) ℓ (Multiplicative.ofAdd j) ≫
              i.hom.hom ≫ eg.hom).left).hom
            (coordinateGenerator (ζ - 1)) = sigmaPoint ℓ ζ j) := by
  have hζ := pow_eq_one_of_split ℓ ζ hℓ.one_lt hsplit
  have hmul (π : A) : (𝟙 (groupScheme π).X ⊗ₘ 𝟙 (groupScheme π).X) ≫
      MonObj.mul ≫ 𝟙 (groupScheme π).X = MonObj.mul (X := (groupScheme π).X) := by
    simp
  refine ⟨groupScheme (ζ - 1), groupScheme ((ζ - 1) ^ ℓ),
    constantPointsGroupHom ℓ ζ hζ hsplit, isogenyGroupSchemeHom ℓ ζ hsplit,
    Iso.refl _, Iso.refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg Over.Hom.left (hmul _)).trans (groupScheme_mul _)
  · exact (congrArg Over.Hom.left (hmul _)).trans (groupScheme_mul _)
  · exact constantPoints_isPullback ℓ ζ hζ hsplit hℓ
  · exact isogenyGroupSchemeHom_flat_surjective ℓ ζ hsplit
  · have h : 𝟙 (groupScheme (ζ - 1)).X ≫ (isogenyGroupSchemeHom ℓ ζ hsplit).hom.hom ≫
        𝟙 (groupScheme ((ζ - 1) ^ ℓ)).X = (isogenyGroupSchemeHom ℓ ζ hsplit).hom.hom := by
      simp
    exact (congrArg Over.Hom.left h).trans (isogenyGroupSchemeHom_left ℓ ζ hsplit)
  · intro j
    show (Spec.preimage
      (constantComponentOver ℓ (Multiplicative.ofAdd j) ≫
        constantPointsMap ℓ ζ hζ ≫ 𝟙 _).left).hom
        (coordinateGenerator (ζ - 1)) = _
    rw [Category.comp_id, constantComponentOver_pointsMap, pointSection_left,
      Spec.preimage_map]
    exact pointAlgHom_generator (ζ - 1) (constantPoint ℓ ζ hζ j)

end AlgebraicGeometry.MultiplicativeDeformation

end
