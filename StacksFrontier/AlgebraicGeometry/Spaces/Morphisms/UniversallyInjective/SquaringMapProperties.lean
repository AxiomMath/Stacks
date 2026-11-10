module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteLocalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective.SquaringMap

/-!
# Properties of the squaring map on the involution quotient of the affine line

Parts (2) to (4) of the remark Stacks 05VS: the squaring map on the involution quotient of
Stacks 02Z1 is an isomorphism away from the origin, exactly one point lies over the origin,
and the squaring map is universally injective.

See `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AffineLineInvolution

variable (k : Type u) [Field k]

/-! ### Lifting a point of the affine line to the punctured line -/

/-- Two morphisms to the affine line agree as soon as they agree on the coordinate. -/
private theorem affineLine_hom_ext {T : Over (Spec (.of k))} {a b : T ⟶ affineLine k}
    (h : a.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      b.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) : a = b := by
  refine Over.OverMorphism.ext (AffineSpace.hom_ext (a.w.trans b.w.symm) ?_)
  intro i
  cases i
  exact h

/-- The coordinate of a point of the affine line precomposed with a morphism is the
restriction of its coordinate. -/
private theorem comp_appTop_coord {T T' : Over (Spec (.of k))} (h : T' ⟶ T)
    (d : T ⟶ affineLine k) :
    (h ≫ d).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      h.left.appTop (d.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The coordinate of the square of a point of the affine line is the square of its
coordinate. -/
private theorem affineLineSquare_appTop_coord {T : Over (Spec (.of k))}
    (d : T ⟶ affineLine k) :
    (d ≫ affineLineSquare k).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      d.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) ^ 2 := by
  rw [comp_appTop_coord, affineLineSquare_left, AffineSpace.homOfVector_appTop_coord, map_pow]

/-- The coordinate of the negative of a point of the affine line is the negative of its
coordinate. -/
private theorem affineLineNeg_appTop_coord {T : Over (Spec (.of k))} (d : T ⟶ affineLine k) :
    (d ≫ affineLineNeg k).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      -d.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) := by
  rw [comp_appTop_coord, affineLineNeg_left, AffineSpace.homOfVector_appTop_coord, map_neg]

/-- Squaring the coordinate pulls the punctured affine line back to itself. -/
private theorem affineLineSquare_preimage_puncture :
    (affineLineSquare k).left ⁻¹ᵁ puncturedAffineLineOpen k = puncturedAffineLineOpen k := by
  rw [Scheme.preimage_basicOpen_top, affineLineSquare_left,
    AffineSpace.homOfVector_appTop_coord]
  exact Scheme.basicOpen_pow (affineLine k).left
    (AffineSpace.coord (Spec (.of k)) PUnit.unit) (by norm_num)

/-- A point of the affine line whose square lies in the punctured line already lies in the
punctured line. -/
private theorem affineLine_preimage_puncture_eq_top {T : Over (Spec (.of k))}
    (a : T ⟶ affineLine k) (c : T ⟶ puncturedAffineLine k)
    (h : a ≫ affineLineSquare k = c ≫ puncturedAffineLineInclusion k) :
    a.left ⁻¹ᵁ puncturedAffineLineOpen k = ⊤ := by
  have hι : (puncturedAffineLineOpen k).ι ⁻¹ᵁ puncturedAffineLineOpen k = ⊤ := by
    ext x
    exact iff_of_true x.property trivial
  have hcomp : (a ≫ affineLineSquare k).left ⁻¹ᵁ puncturedAffineLineOpen k = ⊤ := by
    rw [h, Over.comp_left, puncturedAffineLineInclusion_left, Scheme.Hom.comp_preimage, hι,
      Scheme.Hom.preimage_top]
  rw [Over.comp_left, Scheme.Hom.comp_preimage, affineLineSquare_preimage_puncture] at hcomp
  exact hcomp

/-- A morphism to the affine line which lands in the punctured line factors through it. -/
private theorem exists_lift_puncture {T : Over (Spec (.of k))}
    (a : T ⟶ affineLine k) (h : a.left ⁻¹ᵁ puncturedAffineLineOpen k = ⊤) :
    ∃ a' : T ⟶ puncturedAffineLine k, a' ≫ puncturedAffineLineInclusion k = a := by
  have hr : Set.range a.left ⊆ Set.range (puncturedAffineLineOpen k).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ a.left ⁻¹ᵁ puncturedAffineLineOpen k := by rw [h]; trivial
    exact hx
  have ha' : IsOpenImmersion.lift (puncturedAffineLineOpen k).ι a.left hr ≫
      (puncturedAffineLineOpen k).ι = a.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk _ ?_, Over.OverMorphism.ext ha'⟩
  change IsOpenImmersion.lift (puncturedAffineLineOpen k).ι a.left hr ≫
    (puncturedAffineLineOpen k).ι ≫ (affineLine k).hom = T.hom
  rw [← Category.assoc, ha', Over.w]

/-- A morphism to the affine line whose coordinate is a unit factors through the punctured
line. -/
private theorem exists_lift_puncture_of_isUnit {T : Over (Spec (.of k))}
    (a : T ⟶ affineLine k)
    (hu : IsUnit (a.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))) :
    ∃ a' : T ⟶ puncturedAffineLine k, a' ≫ puncturedAffineLineInclusion k = a :=
  exists_lift_puncture k a (by
    rw [Scheme.preimage_basicOpen_top]
    exact Scheme.basicOpen_of_isUnit _ hu)

/-! ### Adjoining a square root -/

/-- Adjoining a square root of an element of a commutative ring is a faithfully flat, finitely
presented ring extension: `X ^ 2 - C a` is monic, so the extension is free of rank two, and it
is integral and injective, hence surjective on spectra. -/
private theorem squareRoot_cover (R : Type u) [CommRing R] (a : R) :
    Flat (Spec.map (CommRingCat.ofHom
        (algebraMap R (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a))))) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
        (algebraMap R (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a))))) ∧
      Surjective (Spec.map (CommRingCat.ofHom
        (algebraMap R (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C a))))) := by
  set p : Polynomial R := Polynomial.X ^ 2 - Polynomial.C a with hp_def
  have hp : p.Monic := Polynomial.monic_X_pow_sub_C a (by norm_num)
  let A := AdjoinRoot p
  let _ : Module.Free R A := hp.free_adjoinRoot
  let _ : Module.Finite R A := hp.finite_adjoinRoot
  refine ⟨?_, ?_, ?_⟩
  · rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), CommRingCat.hom_ofHom,
      RingHom.finitePresentation_algebraMap]
    infer_instance
  · by_cases hR : Subsingleton R
    · let _ := hR
      exact ⟨fun x => (x.isPrime.ne_top (Subsingleton.elim _ _)).elim⟩
    · let _ : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
      let _ : Algebra.IsIntegral R A := AdjoinRoot.isIntegral_of_monic hp
      exact ⟨RingHom.IsIntegral.comap_surjective
        (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R A))
        (AdjoinRoot.of.injective_of_monic_of_degree_pos hp
          (by rw [hp_def, Polynomial.degree_X_pow_sub_C] <;> norm_num))⟩

/-- Every global section of an affine scheme acquires a square root on a faithfully flat,
finitely presented affine cover. -/
private theorem exists_squareRoot_affine (T : Scheme.{u}) [IsAffine T] (a : Γ(T, ⊤)) :
    ∃ (W : Scheme.{u}) (f : W ⟶ T) (b : Γ(W, ⊤)), IsAffine W ∧ Flat f ∧
      LocallyOfFinitePresentation f ∧ Surjective f ∧ f.appTop a = b ^ 2 := by
  let R : Type u := Γ(T, ⊤)
  let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.C a
  let A := AdjoinRoot p
  let W := Spec (.of A)
  obtain ⟨_, _, _⟩ := squareRoot_cover R a
  refine ⟨W, Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ T.isoSpec.inv,
    (Scheme.ΓSpecIso (.of A)).inv (AdjoinRoot.root p),
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hroot : AdjoinRoot.root p ^ 2 = algebraMap R A a := by
    have h : AdjoinRoot.mk p (Polynomial.X ^ 2 - Polynomial.C a) = 0 := AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
    exact sub_eq_zero.mp h
  have he : T.isoSpec.hom.appTop = (Scheme.ΓSpecIso (.of R)).hom := Scheme.toSpecΓ_appTop T
  have hi : T.isoSpec.inv.appTop = (Scheme.ΓSpecIso (.of R)).inv := by
    have hcomp := congrArg Scheme.Hom.appTop T.isoSpec.hom_inv_id
    rw [Scheme.Hom.comp_appTop, he] at hcomp
    exact (Iso.comp_hom_eq_id _).mp hcomp
  have key : (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop
      ((Scheme.ΓSpecIso (.of R)).inv a) =
      (Scheme.ΓSpecIso (.of A)).inv (algebraMap R A a) :=
    (congrArg (fun φ : CommRingCat.of R ⟶ Γ(W, ⊤) => φ a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R A)))).symm
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hi, key, ← hroot, map_pow]

/-! ### Points of the chart with the same square -/

/-- The quotient projection identifies a point of the punctured line with its negative: the
two are the two legs of the involution relation at the second summand of `R`. -/
private theorem toQuotientSheaf_neg_eq (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]
    (T : BigFppfOver B (Spec (.of k)) hk)
    (a : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ puncturedAffineLine k) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
        (Opposite.op T) (a ≫ puncturedAffineLineInclusion k ≫ affineLineNeg k) =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
        (Opposite.op T) (a ≫ puncturedAffineLineInclusion k) := by
  let q := Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
    (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)
  have h := congrArg (fun e => e.app (Opposite.op T) (a ≫ coprod.inr (X := affineLine k)))
    (Stacks.Groupoids.sourceMap_toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
      (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k))
  change q.app (Opposite.op T) ((a ≫ coprod.inr) ≫ (involutionRelation k).source) =
    q.app (Opposite.op T) ((a ≫ coprod.inr) ≫ (involutionRelation k).target) at h
  simpa only [involutionRelation_source, involutionRelation_target, Category.assoc,
    coprod.inr_desc] using h

/-- Two points of the chart with the same square, one of which lands in the punctured line,
have the same image in the quotient.

Since `2` is invertible, the two agree up to sign on a neighbourhood of any point of the test
object: those neighbourhoods are flat and locally of finite presentation, so they generate a
covering sieve on which the two images of the quotient projection agree, by
`AlgebraicGeometry.AffineLineInvolution.toQuotientSheaf_neg_eq` in the case where they differ
by a sign. The quotient is a sheaf, hence separated, so the two images agree. -/
private theorem quotient_eq_of_square_eq (hchar : (2 : k) ≠ 0) (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]
    (T : BigFppfOver B (Spec (.of k)) hk)
    (a b : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ affineLine k)
    (c : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ puncturedAffineLine k)
    (ha : a ≫ affineLineSquare k = c ≫ puncturedAffineLineInclusion k)
    (hb : b ≫ affineLineSquare k = c ≫ puncturedAffineLineInclusion k) :
    (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
        (Opposite.op T) a =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
          (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
        (Opposite.op T) b := by
  classical
  let J := BigFppfOver.topology B (Spec (.of k)) hk
  let F := Over.post (X := B.obj hk) B.inclusion
  let Q := involutionQuotient k B hk
  let q := Stacks.Groupoids.toQuotientSheaf J F (involutionRelation k)
  have hab : a.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) ^ 2 =
      b.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) ^ 2 := by
    rw [← affineLineSquare_appTop_coord k a, ← affineLineSquare_appTop_coord k b, ha, hb]
  have hpa := affineLine_preimage_puncture_eq_top k a c ha
  have hpb := affineLine_preimage_puncture_eq_top k b c hb
  obtain ⟨b', hb'⟩ := exists_lift_puncture k b hpb
  have h2 : IsUnit (2 : Γ((F.obj T).left, ⊤)) := by
    have h := (isUnit_iff_ne_zero.mpr hchar).map
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (F.obj T).hom.appTop).hom
    simpa only [CommRingCat.comp_apply, map_ofNat] using h
  have heq : Presheaf.equalizerSieve (F := Q.obj) (q.app (Opposite.op T) a)
      (q.app (Opposite.op T) b) ∈ J T := by
    apply sieve_mem_of_fppf_neighborhoods B (Spec (.of k)) hk
    intro x
    obtain ⟨U, hx, hU⟩ := exists_open_square_eq_or_neg (F.obj T).left
      (a.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
      (b.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) hab
      (by rwa [← Scheme.preimage_basicOpen_top]) h2 x
    have hsite : B.Contains U.toScheme :=
      Scheme.size_lt_of_isOpenImmersion U.ι T.left.property
    let m : B.obj hsite ⟶ T.left := ObjectProperty.homMk U.ι
    refine ⟨B.obj hsite, m, ?_, ?_, ?_, ?_⟩
    · exact (inferInstance : Flat U.ι)
    · exact (inferInstance : LocallyOfFinitePresentation U.ι)
    · exact ⟨⟨x, hx⟩, rfl⟩
    · let g : (Over.mk (m ≫ T.hom) : BigFppfOver B (Spec (.of k)) hk) ⟶ T := Over.homMk m
      have hres (d : F.obj T ⟶ affineLine k) :
          (F.map g ≫ d).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
            U.ι.appTop (d.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) :=
        comp_appTop_coord k (F.map g) d
      change Q.obj.map g.op (q.app (Opposite.op T) a) = Q.obj.map g.op (q.app (Opposite.op T) b)
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      change q.app (Opposite.op _) (F.map g ≫ a) = q.app (Opposite.op _) (F.map g ≫ b)
      rcases hU with hU | hU
      · congr 1
        refine affineLine_hom_ext k ?_
        rw [hres a, hres b]
        exact hU
      · have hneg : F.map g ≫ a =
            (F.map g ≫ b') ≫ puncturedAffineLineInclusion k ≫ affineLineNeg k := by
          refine affineLine_hom_ext k ?_
          rw [← Category.assoc, affineLineNeg_appTop_coord, Category.assoc, hb', hres a, hres b]
          exact hU
        have hpos : F.map g ≫ b = (F.map g ≫ b') ≫ puncturedAffineLineInclusion k := by
          rw [Category.assoc, hb']
        rw [hneg, hpos]
        exact toQuotientSheaf_neg_eq k B hk _ (F.map g ≫ b')
  exact (((isSheaf_iff_isSheaf_of_type J Q.obj).mp Q.property).isSeparated _ heq).ext
    (fun _ _ h => h)

/-! ### The quotient is the affine line away from the origin -/

/-- Squaring the coordinate is locally surjective on the restricted functors of points.

Over an affine piece of the affine cover of a test object, adjoining a square root of the
coordinate of the given point gives a flat, locally finitely presented, surjective affine
cover on which the point acquires a square root; those covers are jointly surjective, so they
generate a covering sieve. -/
theorem affineLineSquare_points_locallySurjective (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of k)) hk)
      ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
        (yoneda.map (affineLineSquare k))) := by
  classical
  let F := Over.post (X := B.obj hk) B.inclusion
  refine ⟨?_⟩
  intro T a
  apply sieve_mem_of_fppf_neighborhoods B (Spec (.of k)) hk
  intro x
  let e : (F.obj T).left.affineCover.X ((F.obj T).left.affineCover.idx x) ⟶ (F.obj T).left :=
    (F.obj T).left.affineCover.f ((F.obj T).left.affineCover.idx x)
  have hV : B.Contains ((F.obj T).left.affineCover.X ((F.obj T).left.affineCover.idx x)) :=
    Scheme.size_lt_of_isOpenImmersion e T.left.property
  obtain ⟨W, f, b, hWaff, hf, hfp, hsurj, hb⟩ := exists_squareRoot_affine
    ((F.obj T).left.affineCover.X ((F.obj T).left.affineCover.idx x))
    (e.appTop (a.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)))
  have _ := hWaff
  have _ := hf
  have _ := hfp
  have _ := hsurj
  have hW : B.Contains W := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hV
  let m : B.obj hW ⟶ T.left := ObjectProperty.homMk (f ≫ e)
  refine ⟨B.obj hW, m, ?_, ?_, ?_, ?_⟩
  · exact (inferInstance : Flat (f ≫ e))
  · exact (inferInstance : LocallyOfFinitePresentation (f ≫ e))
  · obtain ⟨z, hz⟩ := (F.obj T).left.affineCover.covers x
    obtain ⟨w, hw⟩ := f.surjective z
    refine ⟨w, ?_⟩
    change (f ≫ e) w = x
    rw [Scheme.Hom.comp_apply, hw]
    exact hz
  · let g : (Over.mk (m ≫ T.hom) : BigFppfOver B (Spec (.of k)) hk) ⟶ T := Over.homMk m
    let r : F.obj (Over.mk (m ≫ T.hom)) ⟶ affineLine k :=
      Over.homMk (AffineSpace.homOfVector (F.obj (Over.mk (m ≫ T.hom))).hom
        (fun _ : PUnit.{u + 1} => b)) (AffineSpace.homOfVector_over _ _)
    have hcomp : ∀ Z, (f ≫ e).appTop Z = f.appTop (e.appTop Z) := fun Z => by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    refine ⟨r, ?_⟩
    change r ≫ affineLineSquare k = F.map g ≫ a
    refine affineLine_hom_ext k ?_
    rw [affineLineSquare_appTop_coord, comp_appTop_coord,
      show r.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = b from
        AffineSpace.homOfVector_appTop_coord _ _ _]
    exact ((hcomp _).trans hb).symm

/-- The squaring map sends the class of a point of the affine line to its square. -/
private theorem squaringMap_app_toQuotientSheaf_app (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)]
    (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ affineLine k) :
    (squaringMap k B hk).app (Opposite.op T)
      ((Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
          (Opposite.op T) t) = t ≫ affineLineSquare k := by
  simpa using congrArg (fun α ↦ α.app (Opposite.op T) t)
    (toQuotientSheaf_comp_squaringMap k B hk)

/-- **Stacks 05VS, part (2).** Over a field in which `2` is invertible, the squaring map from
the involution quotient to the affine line is an isomorphism away from the origin: its base
change along the inclusion of the punctured affine line is an isomorphism. -/
@[stacks 05VS "part (2): an isomorphism away from the origin"]
theorem isIso_squaringMap_pullback_puncturedAffineLine (hchar : (2 : k) ≠ 0)
    (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    IsIso (pullback.snd (squaringMap k B hk)
      ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
        (yoneda.map (puncturedAffineLineInclusion k)))) := by
  let J := BigFppfOver.topology B (Spec (.of k)) hk
  let F := Over.post (X := B.obj hk) B.inclusion
  let A : Sheaf J (Type u) := affineLinePointsSheaf k B hk
  let V : Sheaf J (Type u) := ⟨Stacks.Groupoids.points F (puncturedAffineLine k),
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B (Spec (.of k)) hk
      (puncturedAffineLine k)⟩
  let f : involutionQuotient k B hk ⟶ A := ⟨squaringMap k B hk⟩
  let g : V ⟶ A := ⟨F.op.whiskerLeft (yoneda.map (puncturedAffineLineInclusion k))⟩
  let q := Stacks.Groupoids.toQuotientSheaf J F (involutionRelation k)
  have hq : Presheaf.IsLocallySurjective J q :=
    Stacks.Groupoids.toQuotientSheaf_isLocallySurjective J F (involutionRelation k)
  have hsq : Presheaf.IsLocallySurjective J (q ≫ f.hom) := by
    have hfac : q ≫ f.hom =
        F.op.whiskerLeft (yoneda.map (affineLineSquare k)) :=
      toQuotientSheaf_comp_squaringMap k B hk
    rw [hfac]
    exact affineLineSquare_points_locallySurjective k B hk
  have hrel : ∀ (T : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ)
      (a b : (Stacks.Groupoids.points F (affineLine k)).obj T)
      (c : (Stacks.Groupoids.points F (puncturedAffineLine k)).obj T),
      f.hom.app T (q.app T a) = g.hom.app T c →
      f.hom.app T (q.app T b) = g.hom.app T c → q.app T a = q.app T b := by
    intro T a b c ha hb
    refine quotient_eq_of_square_eq k hchar B hk T.unop a b c ?_ ?_
    · exact (squaringMap_app_toQuotientSheaf_app k B hk T.unop a).symm.trans ha
    · exact (squaringMap_app_toQuotientSheaf_app k B hk T.unop b).symm.trans hb
  have ht : IsIso (pullback.snd f g) :=
    isIso_of_local_roots J q f g (pullback.fst f g) (pullback.snd f g)
      (IsPullback.of_hasPullback f g) hrel
  have hpres : IsIso ((sheafToPresheaf J (Type u)).map (pullback.snd f g)) :=
    Functor.map_isIso _ _
  have he : (PreservesPullback.iso (sheafToPresheaf J (Type u)) f g).inv ≫
      (sheafToPresheaf J (Type u)).map (pullback.snd f g) = pullback.snd f.hom g.hom :=
    PreservesPullback.iso_inv_snd _ _ _
  have hfinal : IsIso (pullback.snd f.hom g.hom) := by
    rw [← he]
    infer_instance
  exact hfinal

/-! ### The unique point over the origin -/

/-- The origin of the affine line over an object over `Spec k`: the section whose coordinate
is `0`. This is the point `0` of the example of Stacks 05VS. -/
noncomputable def affineLineZero (T : Over (Spec (.of k))) : T ⟶ affineLine k :=
  Over.homMk (AffineSpace.homOfVector T.hom fun _ : PUnit.{u + 1} => 0)
    (AffineSpace.homOfVector_over _ _)

/-- The coordinate of the origin is `0`. -/
@[simp]
theorem affineLineZero_appTop_coord (T : Over (Spec (.of k))) :
    (affineLineZero k T).left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = 0 :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- A point of the affine line whose coordinate is `0` is the origin. -/
private theorem eq_affineLineZero_of_coord_eq_zero {T : Over (Spec (.of k))}
    {a : T ⟶ affineLine k}
    (h : a.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = 0) :
    a = affineLineZero k T :=
  affineLine_hom_ext k (h.trans (affineLineZero_appTop_coord k T).symm)

/-- The origin restricts to the origin. -/
@[simp]
theorem comp_affineLineZero {T T' : Over (Spec (.of k))} (h : T' ⟶ T) :
    h ≫ affineLineZero k T = affineLineZero k T' :=
  affineLine_hom_ext k (by
    rw [comp_appTop_coord, affineLineZero_appTop_coord, affineLineZero_appTop_coord, map_zero])

/-- Squaring the coordinate fixes the origin. -/
@[simp]
theorem affineLineZero_comp_affineLineSquare (T : Over (Spec (.of k))) :
    affineLineZero k T ≫ affineLineSquare k = affineLineZero k T :=
  affineLine_hom_ext k (by
    rw [affineLineSquare_appTop_coord, affineLineZero_appTop_coord, zero_pow (by norm_num)])

/-- Over a reduced scheme a point of the affine line whose square is the origin is already the
origin: its coordinate is nilpotent, hence zero. -/
private theorem eq_affineLineZero_of_square_eq {T : Over (Spec (.of k))} [IsReduced T.left]
    (a : T ⟶ affineLine k) (h : a ≫ affineLineSquare k = affineLineZero k T) :
    a = affineLineZero k T :=
  eq_affineLineZero_of_coord_eq_zero k <| IsNilpotent.eq_zero ⟨2, by
    rw [← affineLineSquare_appTop_coord, h, affineLineZero_appTop_coord]⟩

/-- The origin of the affine line, as a point of its restricted functor of points in the sense
of Stacks 03BU: the class of the zero section over the ground field itself. -/
noncomputable def originPoint (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k))) :
    Space.points B (Spec (.of k)) hk
      (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)) :=
  Space.FieldValuedPoint.class B (Spec (.of k)) hk _
    { carrier := k
      contained := hk
      toBase := 𝟙 (Spec (.of k))
      value := affineLineZero k _ }

/-- Squaring the coordinate fixes the origin on points. -/
private theorem pointsMap_affineLineSquare_originPoint (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) :
    Space.pointsMap B (Spec (.of k)) hk _
        ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (affineLineSquare k)))
        (originPoint k B hk) = originPoint k B hk := by
  set z : Space.FieldValuedPoint B (Spec (.of k)) hk
      (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)) :=
    { carrier := k
      contained := hk
      toBase := 𝟙 (Spec (.of k))
      value := affineLineZero k _ } with hz
  have hdom : Space.FieldValuedPoint.Dominates B (Spec (.of k)) hk _ z
      (Space.FieldValuedPoint.map B (Spec (.of k)) hk _
        ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (affineLineSquare k))) z) := by
    refine ⟨𝟙 _, ?_⟩
    change (Over.post (X := B.obj hk) B.inclusion).map (𝟙 _) ≫
      (z.value ≫ affineLineSquare k) = z.value
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact affineLineZero_comp_affineLineSquare k _
  exact Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of k)) hk _
    ⟨z, hdom, Space.FieldValuedPoint.dominates_refl B (Spec (.of k)) hk _ z⟩

/-- A point of the affine line whose square is the origin is the origin.

A representative of such a point and the zero section have a common field-valued extension on
which the representative's square is the zero section; the extension is the spectrum of a
field, hence reduced, so the representative is itself the zero section there. -/
private theorem eq_originPoint_of_pointsMap_affineLineSquare_eq (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (y : Space.points B (Spec (.of k)) hk
      (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k)))
    (hy : Space.pointsMap B (Spec (.of k)) hk _
      ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
        (yoneda.map (affineLineSquare k))) y = originPoint k B hk) :
    y = originPoint k B hk := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    (Space.FieldValuedPoint.class_eq_class_iff B (Spec (.of k)) hk _ _ _).mp hy
  change (Over.post (X := B.obj hk) B.inclusion).map a ≫
    (p.value ≫ affineLineSquare k) = r.value at ha
  have hb' : (Over.post (X := B.obj hk) B.inclusion).map b ≫ affineLineZero k _ = r.value := hb
  rw [comp_affineLineZero] at hb'
  have hred : IsReduced ((Over.post (X := B.obj hk) B.inclusion).obj
      (Space.FieldValuedPoint.siteObject B (Spec (.of k)) hk
        (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion)
          (affineLine k)) r)).left := by
    change IsReduced (Spec (.of r.carrier))
    infer_instance
  have _ := hred
  have hzero : (Over.post (X := B.obj hk) B.inclusion).map a ≫ p.value =
      affineLineZero k ((Over.post (X := B.obj hk) B.inclusion).obj
        (Space.FieldValuedPoint.siteObject B (Spec (.of k)) hk
          (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion)
            (affineLine k)) r)) := by
    refine eq_affineLineZero_of_square_eq k _ ?_
    calc ((Over.post (X := B.obj hk) B.inclusion).map a ≫ p.value) ≫ affineLineSquare k
        = (Over.post (X := B.obj hk) B.inclusion).map a ≫ (p.value ≫ affineLineSquare k) :=
          Category.assoc _ _ _
      _ = r.value := ha
      _ = _ := hb'.symm
  refine Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of k)) hk _
    ⟨r, ⟨a, ?_⟩, ⟨b, hb⟩⟩
  change (Over.post (X := B.obj hk) B.inclusion).map a ≫ p.value = r.value
  rw [hzero, hb']

/-- **Stacks 05VS, part (3).** Exactly one point of the involution quotient lies over the
origin of the affine line under the morphism descended from squaring the coordinate.

The quotient projection is locally surjective, hence surjective on the points of Stacks 03BU,
so every point of the quotient over the origin comes from a point of the affine line whose
square is the origin; such a point is the origin by
`AlgebraicGeometry.AffineLineInvolution.eq_affineLineZero_of_square_eq`, and the image of the
origin is the point sought. No assumption on the characteristic is needed: in characteristic
two the relation is the diagonal and the statement is that squaring is injective on
field-valued points. -/
@[stacks 05VS "part (3): exactly one point above the origin"]
theorem existsUnique_pointsMap_squaringMap_eq_originPoint (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    ∃! x : Space.points B (Spec (.of k)) hk (involutionQuotient k B hk).obj,
      Space.pointsMap B (Spec (.of k)) hk _ (squaringMap k B hk) x = originPoint k B hk := by
  set q := Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
    (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k) with hq
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of k)) hk) q :=
    Stacks.Groupoids.toQuotientSheaf_isLocallySurjective _ _ _
  have hsurj := Space.surjective_pointsMap_of_isLocallySurjective B (Spec (.of k)) hk q hls
  have hfac : ∀ z, Space.pointsMap B (Spec (.of k)) hk _ (squaringMap k B hk)
      (Space.pointsMap B (Spec (.of k)) hk _ q z) =
      Space.pointsMap B (Spec (.of k)) hk _
        ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (affineLineSquare k))) z := by
    intro z
    rw [← Function.comp_apply (f := Space.pointsMap B (Spec (.of k)) hk _ (squaringMap k B hk)),
      ← Space.pointsMap_comp, toQuotientSheaf_comp_squaringMap]
  refine ⟨Space.pointsMap B (Spec (.of k)) hk _ q (originPoint k B hk), ?_, ?_⟩
  · change Space.pointsMap B (Spec (.of k)) hk _ (squaringMap k B hk)
      (Space.pointsMap B (Spec (.of k)) hk _ q (originPoint k B hk)) = originPoint k B hk
    rw [hfac, pointsMap_affineLineSquare_originPoint]
  · intro x hx
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hfac] at hx
    rw [eq_originPoint_of_pointsMap_affineLineSquare_eq k B hk z hx]

/-! ### Universal injectivity of the squaring map -/

/-- Over the spectrum of a field every global section is zero or a unit. -/
private theorem eq_zero_or_isUnit_of_fieldSpec (K : Type u) [Field K]
    (x : Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))) : x = 0 ∨ IsUnit x := by
  rcases eq_or_ne x 0 with hx | hx
  · exact Or.inl hx
  · refine Or.inr ?_
    have hne : (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv x ≠ 0 := fun hz ↦
      hx ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
        (hz.trans (map_zero _).symm))
    simpa using (isUnit_iff_ne_zero.mpr hne).map
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm

/-- **Stacks 05VS, part (4).** Away from characteristic two the morphism descended from
squaring the coordinate is universally injective.

Universal injectivity is tested on field-valued points by
`AlgebraicGeometry.Space.universallyInjective_of_fieldPoints`, so it suffices to make two
sections of the quotient over the spectrum of a field with the same square agree over a further
field spectrum. The quotient projection is locally surjective, so after two successive
restrictions both sections are classes of points `t₁`, `t₂` of the affine line with the same
square. Over a field the coordinate of `t₁` is zero or a unit: in the first case the common
square is the origin and both points are the origin, the test object being reduced; in the
second the common square lies in the punctured line, and
`AlgebraicGeometry.AffineLineInvolution.quotient_eq_of_square_eq` identifies the two classes. -/
@[stacks 05VS "part (4): universally injective"]
theorem universallyInjective_squaringMap (hchar : (2 : k) ≠ 0) (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hk) (Type u)] :
    Space.UniversallyInjective B (Spec (.of k)) hk (squaringMap k B hk) := by
  refine Space.universallyInjective_of_fieldPoints B (Spec (.of k)) hk _ ?_
  intro p y h
  change (squaringMap k B hk).app
      (Opposite.op (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hk))) p.value =
    (squaringMap k B hk).app
      (Opposite.op (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hk))) y at h
  obtain ⟨L₁, hL₁f, hL₁, s₁, c₁, v₁, hv₁⟩ :=
    Space.exists_fieldSpec_lift_of_isLocallySurjective B (Spec (.of k)) hk _
      (Stacks.Groupoids.toQuotientSheaf_isLocallySurjective
        (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k))
      p.carrier p.contained p.toBase p.value
  obtain ⟨L₂, hL₂f, hL₂, s₂, c₂, v₂, hv₂⟩ :=
    Space.exists_fieldSpec_lift_of_isLocallySurjective B (Spec (.of k)) hk _
      (Stacks.Groupoids.toQuotientSheaf_isLocallySurjective
        (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k))
      L₁ hL₁ s₁ ((involutionQuotient k B hk).obj.map c₁.op y)
  have hred : IsReduced ((Over.post (X := B.obj hk) B.inclusion).obj
      (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))).left := by
    change IsReduced (Spec (.of L₂))
    infer_instance
  have _ := hred
  set t₁ : (Over.post (X := B.obj hk) B.inclusion).obj
      (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk)) ⟶ affineLine k :=
    (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion)
      (affineLine k)).map c₂.op v₁ with ht₁
  have hp : (involutionQuotient k B hk).obj.map (c₂ ≫ c₁).op p.value =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
          (Opposite.op (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))) t₁ := by
    rw [ht₁, NatTrans.naturality_apply
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)) c₂.op v₁, hv₁,
      op_comp, CategoryTheory.Functor.map_comp]
    rfl
  have hy : (involutionQuotient k B hk).obj.map (c₂ ≫ c₁).op y =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
          (Opposite.op (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))) v₂ := by
    rw [hv₂, op_comp, CategoryTheory.Functor.map_comp]
    rfl
  have hsq : t₁ ≫ affineLineSquare k = v₂ ≫ affineLineSquare k := by
    rw [← squaringMap_app_toQuotientSheaf_app k B hk
        (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk)) t₁,
      ← squaringMap_app_toQuotientSheaf_app k B hk
        (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk)) v₂, ← hp, ← hy,
      NatTrans.naturality_apply (squaringMap k B hk) (c₂ ≫ c₁).op p.value,
      NatTrans.naturality_apply (squaringMap k B hk) (c₂ ≫ c₁).op y, h]
  have hclass : (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
          (Opposite.op (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))) t₁ =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
        (Over.post (X := B.obj hk) B.inclusion) (involutionRelation k)).app
          (Opposite.op (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))) v₂ := by
    rcases eq_zero_or_isUnit_of_fieldSpec L₂
        (t₁.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) with hzero | hunit
    · have h₁ : t₁ = affineLineZero k ((Over.post (X := B.obj hk) B.inclusion).obj
          (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))) :=
        eq_affineLineZero_of_coord_eq_zero k hzero
      have h₂ : v₂ = affineLineZero k ((Over.post (X := B.obj hk) B.inclusion).obj
          (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))) := by
        refine eq_affineLineZero_of_square_eq k
          (T := (Over.post (X := B.obj hk) B.inclusion).obj
            (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))) _ ?_
        rw [← hsq, h₁, affineLineZero_comp_affineLineSquare]
      rw [h₁, h₂]
    · obtain ⟨w, hw⟩ := exists_lift_puncture_of_isUnit k (t₁ ≫ affineLineSquare k) (by
        rw [affineLineSquare_appTop_coord]
        exact hunit.pow 2)
      exact quotient_eq_of_square_eq k hchar B hk (Over.mk (⟨s₂⟩ : B.obj hL₂ ⟶ B.obj hk))
        t₁ v₂ w hw.symm (hsq.symm.trans hw.symm)
  exact ⟨{ carrier := L₂
           field := hL₂f
           contained := hL₂
           toBase := s₂
           value := (involutionQuotient k B hk).obj.map (c₂ ≫ c₁).op p.value }, c₂ ≫ c₁, rfl,
    hy.trans (hclass.symm.trans hp.symm)⟩

/-- **The origin is the only point of the affine line whose square is the origin**, and it is
one: squaring the coordinate fixes the origin. -/
theorem pointsMap_affineLineSquare_eq_originPoint_iff (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (y : Space.points B (Spec (.of k)) hk
      (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k))) :
    Space.pointsMap B (Spec (.of k)) hk _
        ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (affineLineSquare k))) y = originPoint k B hk ↔
      y = originPoint k B hk :=
  ⟨eq_originPoint_of_pointsMap_affineLineSquare_eq k B hk y,
    fun h => h ▸ pointsMap_affineLineSquare_originPoint k B hk⟩

/-- The coordinate of a morphism into the affine line through the punctured line is a unit. -/
private theorem isUnit_comp_puncturedAffineLineInclusion_appTop_coord {T : Over (Spec (.of k))}
    (v : T ⟶ puncturedAffineLine k) :
    IsUnit ((v ≫ puncturedAffineLineInclusion k).left.appTop
      (AffineSpace.coord (Spec (.of k)) PUnit.unit)) := by
  rw [comp_appTop_coord, puncturedAffineLineInclusion_left]
  exact (isUnit_basicOpen_appTop _ _).map _

/-- **The punctured affine line consists of the points of the affine line other than the
origin.** A field-valued point of the affine line has coordinate either zero, and is then the
origin, or a unit, and then factors through the punctured line; conversely the coordinate of a
point of the punctured line is a unit, so no such point is the origin. -/
theorem mem_range_pointsMap_puncturedAffineLineInclusion_iff (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k)))
    (y : Space.points B (Spec (.of k)) hk
      (Stacks.Groupoids.points (Over.post (X := B.obj hk) B.inclusion) (affineLine k))) :
    y ∈ Set.range (Space.pointsMap B (Spec (.of k)) hk _
        ((Over.post (X := B.obj hk) B.inclusion).op.whiskerLeft
          (yoneda.map (puncturedAffineLineInclusion k)))) ↔
      y ≠ originPoint k B hk := by
  have hnt : ∀ (K : Type u) [Field K], (0 : Γ(Spec (.of K), ⊤)) ≠ 1 := fun K _ h => by
    have := congrArg (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv h
    simp at this
  constructor
  · rintro ⟨z, rfl⟩ h
    obtain ⟨p, rfl⟩ := Quot.exists_rep z
    obtain ⟨r, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
      (Space.FieldValuedPoint.class_eq_class_iff B (Spec (.of k)) hk _ _ _).mp h
    change (Over.post (X := B.obj hk) B.inclusion).map a ≫
      (p.value ≫ puncturedAffineLineInclusion k) = r.value at ha
    have hb' : (Over.post (X := B.obj hk) B.inclusion).map b ≫ affineLineZero k _ = r.value := hb
    rw [comp_affineLineZero] at hb'
    have hu : IsUnit (((Over.post (X := B.obj hk) B.inclusion).map a ≫
        (p.value ≫ puncturedAffineLineInclusion k)).left.appTop
          (AffineSpace.coord (Spec (.of k)) PUnit.unit)) := by
      rw [comp_appTop_coord]
      exact (isUnit_comp_puncturedAffineLineInclusion_appTop_coord k p.value).map _
    rw [ha, ← hb', affineLineZero_appTop_coord, isUnit_zero_iff] at hu
    exact hnt r.carrier hu
  · intro hy
    obtain ⟨p, rfl⟩ := Quot.exists_rep y
    rcases eq_zero_or_isUnit_of_fieldSpec p.carrier
        (p.value.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) with h0 | hu
    · refine (hy ?_).elim
      have hval : p.value = affineLineZero k _ :=
        eq_affineLineZero_of_coord_eq_zero k h0
      refine Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of k)) hk _
        ⟨p, Space.FieldValuedPoint.dominates_refl B (Spec (.of k)) hk _ p,
          ⟨Over.homMk ⟨p.toBase⟩ (by
            apply ObjectProperty.hom_ext
            exact Category.comp_id p.toBase), ?_⟩⟩
      change (Over.post (X := B.obj hk) B.inclusion).map _ ≫ affineLineZero k _ = p.value
      rw [comp_affineLineZero, hval]
      rfl
    · obtain ⟨a', ha'⟩ := exists_lift_puncture_of_isUnit k p.value hu
      refine ⟨Space.FieldValuedPoint.class B (Spec (.of k)) hk _
        { carrier := p.carrier
          contained := p.contained
          toBase := p.toBase
          value := a' }, ?_⟩
      rw [Space.pointsMap_class]
      congr 1
      change Space.FieldValuedPoint.mk p.carrier p.contained p.toBase
        (a' ≫ puncturedAffineLineInclusion k) = p
      rw [ha']

end AlgebraicGeometry.AffineLineInvolution

end
