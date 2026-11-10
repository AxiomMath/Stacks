module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPrime
public import StacksFrontier.RingTheory.Length.PrimeResidueDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ResidueFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.ResidueField

/-!
# Points and residue degrees over an elementary étale chart

Let `g : Z ⟶ Y` be a morphism of decent algebraic spaces over `S`, and let `d` be a cartesian
square of étale scheme charts over it: a chart `V` of `Y`, the chart `U = Z ×_Y V` of `Z`, and
the morphism of schemes `r : U ⟶ V`. Let `e` be the only point of `V` above a point `η` of `|Y|`,
with `Spec κ(e) ⟶ Y` a monomorphism. This file shows that the fibre of `r` over `e` is the
fibre of `|g|` over `η`, and that the residue degrees along `g` at those points are the residue
degrees along `r`.

## Main results

* `AlgebraicGeometry.Space.bijOn_chartSchemeToPoints_fibre`: the map from points of `U` to
  `|Z|` is a bijection from `r⁻¹(e)` onto `g⁻¹(η)`.
* `AlgebraicGeometry.Space.primeResidueDegree_chartPrime_eq_finrank`: for affine charts, the
  residue degree of the prime of `Γ(U)` at `x ∈ r⁻¹(e)` over the prime of `Γ(V)` at `e` is the
  degree `[κ(z) : κ(g z)]` of the residue fields of the decent spaces at `z = |x|`.
* `AlgebraicGeometry.Space.finrank_residueFieldHom_eq_of_mono`: the degree of the residue
  field extension of a morphism of decent spaces can be read off any monomorphic field-valued
  representatives of the two points.
* `AlgebraicGeometry.Scheme.primeResidueDegree_comap_germ_eq_residueDegree`: for a morphism of
  affine schemes, the residue degree of the primes of global sections at `x` and `f x` is the
  degree of `κ(x) / κ(f x)`.

## Implementation notes

Injectivity on `r⁻¹(e)` goes through the base change `Z ×_Y Spec κ(e)`: by pasting with the
cartesian square it is also `U ×_V Spec κ(e)`, so every point of `U` above `e` lifts to it,
and its projection to `Z` is a monomorphism, hence injective on points. Surjectivity is the
surjectivity of points of a fibre product onto pairs of points with a common image.

For the degrees, `Spec κ(x) ⟶ U ⟶ Z` is a monomorphism: two maps into `Spec κ(x)` which agree in
`Z` agree in `Y`, hence after `Spec κ(x) ⟶ Spec κ(e)` because `Spec κ(e) ⟶ Y` is a monomorphism,
hence in `U = Z ×_Y V`, and `Spec κ(x) ⟶ U` is a monomorphism of schemes. So `κ(x)` and `κ(e)`
are residue fields of `Z` and `Y` in the sense of Stacks 0EMW, compatibly with `g` and `r`.

The comparison with the primes of the rings of sections needs the charts to be affine: for the
projective line over a field, mapping to the point, the ring of global sections does not see
the residue fields of the points of the line.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- On an affine scheme, the prime of the ring of global sections cut out by a point `x`, as the
preimage of the maximal ideal of the stalk under the germ map, is the prime of `Spec Γ(X, ⊤)`
corresponding to `x`. -/
theorem comap_germ_maximalIdeal_eq_primeIdealOf [IsAffine X] (x : X) :
    Ideal.comap (X.presheaf.germ ⊤ x trivial).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) =
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  rfl

/-- On an affine scheme, the residue field of the prime of the ring of global sections at a
point `x` is identified with `κ(x)`, compatibly with evaluation of global sections at `x`. -/
theorem exists_residueFieldEquiv_of_eq_primeIdealOf [IsAffine X] (x : X)
    (P : Ideal Γ(X, ⊤)) [P.IsPrime]
    (hP : P = ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal) :
    ∃ i : P.ResidueField ≃+* X.residueField x,
      ∀ a, i (algebraMap Γ(X, ⊤) P.ResidueField a) = X.Γevaluation x a := by
  subst hP
  exact ⟨(isAffineOpen_top X).residueFieldEquiv x trivial,
    (isAffineOpen_top X).residueFieldEquiv_algebraMap x trivial⟩

/-- The prime of global sections of `Y` cut out by `f x` is the preimage, under pullback of
global sections along `f`, of the prime of global sections of `X` cut out by `x`. -/
theorem comap_germ_maximalIdeal_eq_comap_appTop (f : X ⟶ Y) (x : X) :
    Ideal.comap (Y.presheaf.germ ⊤ (f x) trivial).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) =
      (Ideal.comap (X.presheaf.germ ⊤ x trivial).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).comap f.appTop.hom := by
  ext a
  simp only [Ideal.mem_comap]
  rw [← IsLocalRing.residue_eq_zero_iff, ← IsLocalRing.residue_eq_zero_iff]
  change Y.Γevaluation (f x) a = 0 ↔ X.Γevaluation x (f.appTop a) = 0
  rw [← Γevaluation_naturality_apply, map_eq_zero_iff _ (f.residueFieldMap x).hom.injective]

/-- For a morphism of affine schemes, the residue degree of the prime of global sections cut
out by `x` over the prime cut out by `f x` is the degree of the residue field extension
`κ(x) / κ(f x)`. -/
theorem primeResidueDegree_comap_germ_eq_residueDegree [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (x : X) :
    Stacks.Length.primeResidueDegree f.appTop.hom
        (Ideal.comap (Y.presheaf.germ ⊤ (f x) trivial).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))))
        (Ideal.comap (X.presheaf.germ ⊤ x trivial).hom
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) =
      f.residueDegree x := by
  rw [Stacks.Length.primeResidueDegree_of_eq _ _ _ (comap_germ_maximalIdeal_eq_comap_appTop f x)]
  obtain ⟨i, hi⟩ := exists_residueFieldEquiv_of_eq_primeIdealOf (f x) _
    (comap_germ_maximalIdeal_eq_primeIdealOf (f x))
  obtain ⟨j, hj⟩ := exists_residueFieldEquiv_of_eq_primeIdealOf x _
    (comap_germ_maximalIdeal_eq_primeIdealOf x)
  let := (Ideal.ResidueField.map _ _ f.appTop.hom
    (comap_germ_maximalIdeal_eq_comap_appTop f x)).toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv i j (Ideal.ResidueField.ringHom_ext ?_)
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, hi, RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
    hj]
  exact Γevaluation_naturality_apply f x a

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; enable the functor-category instances of `FibreDegreeStratification`. -/
/-- Pullbacks of presheaves on the big fppf site over `S`, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ElementaryChartFibre :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_ElementaryChartFibre
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Points

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}

/-- Over a point `e` of the target chart whose field-valued point is a monomorphism into `G`,
the points of a cartesian source chart lying over `e` are determined by the points of `F`
they define. -/
theorem injOn_chartSchemeToPoints_fibre (d : ChartDiagram B S hS F G f)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f d.V.1.hom) (e : chartScheme d.V)
    (hmono : Mono (fieldMorphism B S hS G (chartSchemeFieldValuedPoint B S hS G d.V e))) :
    Set.InjOn (chartSchemeToPoints B S hS F d.U)
      {x : chartScheme d.U | ((BigFppfOver.toScheme B S hS).map d.g).base x = e} := by
  let c := canonicalSiteFieldPoint B S hS ((SmallEtale.toOver B S hS G).obj d.V) e
  let t := fieldMorphism B S hS _ c
  have hmono' : Mono (t ≫ d.V.1.hom) := fieldMorphism_map B S hS _ _ c ▸ hmono
  have hfst : Mono (pullback.fst f (t ≫ d.V.1.hom)) :=
    (IsPullback.of_hasPullback f (t ≫ d.V.1.hom)).mono_fst_of_mono hmono'
  have hinj := pointsMap_injective_of_mono B S hS (pullback.fst f (t ≫ d.V.1.hom))
  let k := hd.lift (pullback.fst f (t ≫ d.V.1.hom)) (pullback.snd f (t ≫ d.V.1.hom) ≫ t)
    (by rw [(IsPullback.of_hasPullback f (t ≫ d.V.1.hom)).w, Category.assoc])
  have hsq : IsPullback k (pullback.snd f (t ≫ d.V.1.hom)) (yoneda.map d.g) t :=
    IsPullback.of_right' (IsPullback.of_hasPullback f (t ≫ d.V.1.hom)) hd
  have hlift : ∀ x : chartScheme d.U, ((BigFppfOver.toScheme B S hS).map d.g).base x = e →
      ∃ w, pointsMap B S hS _ k w = (canonicalSiteFieldPoint B S hS _ x).class B S hS _ := by
    intro x hx
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hsq _
      ((c.tautologicalPoint B S hS _).class B S hS _) (by
        rw [pointsMap_yoneda_map_class_canonicalSiteFieldPoint]
        exact (congrArg _ (congrArg _ hx)).trans
          (pointsMap_fieldMorphism_tautologicalPoint B S hS _ c).symm)
    exact ⟨w, hw⟩
  intro x₁ hx₁ x₂ hx₂ h
  obtain ⟨w₁, hw₁⟩ := hlift x₁ hx₁
  obtain ⟨w₂, hw₂⟩ := hlift x₂ hx₂
  have key : ∀ (x : chartScheme d.U) w, pointsMap B S hS _ k w =
        (canonicalSiteFieldPoint B S hS _ x).class B S hS _ →
      pointsMap B S hS _ (pullback.fst f (t ≫ d.V.1.hom)) w =
        chartSchemeToPoints B S hS F d.U x := by
    intro x w hw
    have hk : k ≫ d.U.1.hom = pullback.fst f (t ≫ d.V.1.hom) := hd.lift_fst _ _ _
    rw [← hk, pointsMap_comp_apply, hw]
    rfl
  have hw : w₁ = w₂ := hinj ((key x₁ w₁ hw₁).trans (h.trans (key x₂ w₂ hw₂).symm))
  rw [← pointsToScheme_class_canonicalSiteFieldPoint B S hS _ x₁,
    ← pointsToScheme_class_canonicalSiteFieldPoint B S hS _ x₂, ← hw₁, ← hw₂, hw]

/-- A morphism `σ : A ⟶ A'` of the site carries the spectrum of the residue field at a point `a`
of `A` to the spectrum of the residue field at its image, by the spectrum of the residue field
map of `σ` at `a`, compatibly with the canonical morphisms to `A` and `A'`. -/
theorem exists_siteHom_canonicalSiteFieldPoint {A A' : BigFppfOver B S hS} (σ : A ⟶ A')
    (a : (BigFppfOver.toScheme B S hS).obj A) :
    ∃ h : (canonicalSiteFieldPoint B S hS A a).siteObject B S hS (yoneda.obj A) ⟶
        (canonicalSiteFieldPoint B S hS A'
          ((BigFppfOver.toScheme B S hS).map σ a)).siteObject B S hS (yoneda.obj A'),
      B.inclusion.map h.left =
          Spec.map (((BigFppfOver.toScheme B S hS).map σ).residueFieldMap a) ∧
        h ≫ (canonicalSiteFieldPoint B S hS A'
            ((BigFppfOver.toScheme B S hS).map σ a)).siteHom B S hS =
          (canonicalSiteFieldPoint B S hS A a).siteHom B S hS ≫ σ := by
  have hρ : ∀ (A : BigFppfOver B S hS) (a : (BigFppfOver.toScheme B S hS).obj A),
      B.inclusion.map ((canonicalSiteFieldPoint B S hS A a).siteHom B S hS).left =
        ((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField a :=
    fun A a ↦ map_siteFieldPointOfSchemeMap_value_left B S hS A _ _
  have hb : ∀ (A : BigFppfOver B S hS) (a : (BigFppfOver.toScheme B S hS).obj A),
      B.inclusion.map ((canonicalSiteFieldPoint B S hS A a).siteObject B S hS
        (yoneda.obj A)).hom =
        ((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField a ≫ B.inclusion.map A.hom :=
    fun A a ↦ (B.inclusion.map_comp (siteMapOfSchemeMap B S hS A
        (B.residueField_spec_contains A.left.property a)
        (((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField a)) A.hom).trans
      (congrArg (· ≫ B.inclusion.map A.hom) (map_siteMapOfSchemeMap B S hS A _ _))
  have key := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
    ((BigFppfOver.toScheme B S hS).map σ) a
  have key' : Spec.map (((BigFppfOver.toScheme B S hS).map σ).residueFieldMap a) ≫
      ((BigFppfOver.toScheme B S hS).obj A').fromSpecResidueField
        ((BigFppfOver.toScheme B S hS).map σ a) ≫ B.inclusion.map A'.hom =
      ((BigFppfOver.toScheme B S hS).obj A).fromSpecResidueField a ≫ B.inclusion.map A.hom := by
    rw [← Category.assoc, key, Category.assoc]
    exact congrArg (_ ≫ ·) ((B.inclusion.map_comp σ.left A'.hom).symm.trans
      (congrArg B.inclusion.map (Over.w σ)))
  refine ⟨Over.homMk (B.inclusion.preimage
    (Spec.map (((BigFppfOver.toScheme B S hS).map σ).residueFieldMap a))) ?_,
    B.inclusion.map_preimage _, ?_⟩
  · apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage, hb, hb]
    exact key'
  · apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    refine (B.inclusion.map_comp _ _).trans (Eq.trans ?_ (B.inclusion.map_comp _ _).symm)
    refine (congrArg₂ (· ≫ ·) (B.inclusion.map_preimage _) (hρ A' _)).trans (key.trans ?_)
    exact congrArg (· ≫ _) (hρ A a).symm

/-- A chart diagram carries the spectrum of the residue field at a point `x` of the source chart
to the spectrum of the residue field at its image in the target chart, by the spectrum of the
residue field map at `x`, compatibly with the field-valued points of the source and target. -/
theorem exists_siteHom_chartSchemeFieldValuedPoint (d : ChartDiagram B S hS F G f)
    (x : chartScheme d.U) :
    ∃ h : (chartSchemeFieldValuedPoint B S hS F d.U x).siteObject B S hS F ⟶
        (chartSchemeFieldValuedPoint B S hS G d.V
          (((BigFppfOver.toScheme B S hS).map d.g).base x)).siteObject B S hS G,
      B.inclusion.map h.left = Spec.map (CommRingCat.ofHom
          (((BigFppfOver.toScheme B S hS).map d.g).residueFieldMap x).hom) ∧
        yoneda.map h ≫ yoneda.map (canonicalSiteFieldPoint B S hS _
            (((BigFppfOver.toScheme B S hS).map d.g).base x)).siteHom =
          yoneda.map (canonicalSiteFieldPoint B S hS _ x).siteHom ≫ yoneda.map d.g ∧
        yoneda.map h ≫ fieldMorphism B S hS G (chartSchemeFieldValuedPoint B S hS G d.V
            (((BigFppfOver.toScheme B S hS).map d.g).base x)) =
          fieldMorphism B S hS F (chartSchemeFieldValuedPoint B S hS F d.U x) ≫ f := by
  obtain ⟨h, h₁, h₂⟩ := exists_siteHom_canonicalSiteFieldPoint B S hS d.g x
  have e₁ : fieldMorphism B S hS F (chartSchemeFieldValuedPoint B S hS F d.U x) =
      yoneda.map (canonicalSiteFieldPoint B S hS _ x).siteHom ≫ d.U.1.hom :=
    fieldMorphism_map_yoneda B S hS F _ _
  have e₂ : fieldMorphism B S hS G (chartSchemeFieldValuedPoint B S hS G d.V
      (((BigFppfOver.toScheme B S hS).map d.g).base x)) =
      yoneda.map (canonicalSiteFieldPoint B S hS _
        (((BigFppfOver.toScheme B S hS).map d.g).base x)).siteHom ≫ d.V.1.hom :=
    fieldMorphism_map_yoneda B S hS G _ _
  have h₃ : yoneda.map h ≫ yoneda.map (canonicalSiteFieldPoint B S hS _
      (((BigFppfOver.toScheme B S hS).map d.g).base x)).siteHom =
        yoneda.map (canonicalSiteFieldPoint B S hS _ x).siteHom ≫ yoneda.map d.g := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg yoneda.map h₂
  refine ⟨h, h₁, h₃, ?_⟩
  rw [e₁, e₂]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d.V.1.hom) h₃).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) d.comm.symm).trans
      (Category.assoc _ _ _).symm)))

/-- Over a point of the target chart whose field-valued point is a monomorphism into `G`, the
field-valued point of a cartesian source chart at every point above it is a monomorphism into
`F`. -/
theorem mono_fieldMorphism_chartSchemeFieldValuedPoint (d : ChartDiagram B S hS F G f)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) f d.V.1.hom) (x : chartScheme d.U)
    (hmono : Mono (fieldMorphism B S hS G (chartSchemeFieldValuedPoint B S hS G d.V
      (((BigFppfOver.toScheme B S hS).map d.g).base x)))) :
    Mono (fieldMorphism B S hS F (chartSchemeFieldValuedPoint B S hS F d.U x)) := by
  obtain ⟨h, -, h₂, h₃⟩ := exists_siteHom_chartSchemeFieldValuedPoint B S hS d x
  have e₁ : fieldMorphism B S hS F (chartSchemeFieldValuedPoint B S hS F d.U x) =
      yoneda.map (canonicalSiteFieldPoint B S hS _ x).siteHom ≫ d.U.1.hom :=
    fieldMorphism_map_yoneda B S hS F _ _
  have hc : Mono (yoneda.map (canonicalSiteFieldPoint B S hS _ x).siteHom) := by
    have : Mono ((BigFppfOver.toScheme B S hS).map
        (canonicalSiteFieldPoint B S hS _ x).siteHom) := by
      change Mono (B.inclusion.map ((canonicalSiteFieldPoint B S hS _ x).siteHom B S hS).left)
      have h₀ : Mono (((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj d.U)).fromSpecResidueField x) := inferInstance
      have h₁ : B.inclusion.map ((canonicalSiteFieldPoint B S hS _ x).siteHom B S hS).left =
          ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj d.U)).fromSpecResidueField x :=
        map_siteFieldPointOfSchemeMap_value_left B S hS _ _ _
      rw [h₁]
      exact h₀
    have := (BigFppfOver.toScheme B S hS).mono_of_mono_map this
    infer_instance
  refine ⟨fun {W} a b hab ↦ ?_⟩
  have h₄ : a ≫ yoneda.map h = b ≫ yoneda.map h :=
    (cancel_mono (fieldMorphism B S hS G _)).1 ((Category.assoc _ _ _).trans
      ((congrArg (a ≫ ·) h₃).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f) hab).trans ((Category.assoc _ _ _).trans
          ((congrArg (b ≫ ·) h₃).symm.trans (Category.assoc _ _ _).symm))))))
  refine (cancel_mono (yoneda.map (canonicalSiteFieldPoint B S hS _ x).siteHom)).1
    (hd.hom_ext ?_ ?_)
  · exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) e₁.symm).trans
      (hab.trans ((congrArg (b ≫ ·) e₁).trans (Category.assoc _ _ _).symm)))
  · exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) h₂.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₄).trans
        ((Category.assoc _ _ _).trans ((congrArg (b ≫ ·) h₂).trans
          (Category.assoc _ _ _).symm)))))

end Points

section ResidueField

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The residue degree of a morphism of decent spaces at monomorphic representatives.** Let
`f : X ⟶ Y` be a morphism of decent algebraic spaces and `x` a point of `X`. If `q` and `q'`
are monomorphic field-valued representatives of `x` and of `f x`, related by a morphism of field
spectra over `f` which is the spectrum of `ψ : q'.carrier →+* q.carrier`, then the degree of
the residue field extension `κ(x) / κ(f x)` is the degree of `ψ`. -/
theorem finrank_residueFieldHom_eq_of_mono (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXdec : IsDecentSpace B S hS X)
    (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X)
    (q : FieldValuedPoint B S hS X) (hq : q.class B S hS X = x)
    (hqm : Mono (fieldMorphism B S hS X q)) (q' : FieldValuedPoint B S hS Y)
    (hq' : q'.class B S hS Y = pointsMap B S hS X f x) (hqm' : Mono (fieldMorphism B S hS Y q'))
    (ψ : q'.carrier →+* q.carrier) (h : q.siteObject B S hS X ⟶ q'.siteObject B S hS Y)
    (hψ : B.inclusion.map h.left = Spec.map (CommRingCat.ofHom ψ))
    (hsq : yoneda.map h ≫ fieldMorphism B S hS Y q' = fieldMorphism B S hS X q ≫ f) :
    (letI := (residueFieldHom B S hS X Y hY hXdec hYdec f x).toAlgebra;
      Module.finrank (residueField B S hS Y hYdec (pointsMap B S hS X f x))
        (residueField B S hS X hXdec x)) =
      letI := ψ.toAlgebra
      Module.finrank q'.carrier q.carrier := by
  obtain ⟨φ, k, hφ, hk⟩ := exists_ringEquiv_residueField_of_mono B S hS hX hXdec x q hq hqm
  obtain ⟨φ', k', hφ', hk'⟩ :=
    exists_ringEquiv_residueField_of_mono B S hS hY hYdec _ q' hq' hqm'
  have hspec := residueFieldHom_spec B S hS X Y hY hXdec hYdec f x
  change ∃ l : _, _ ∧ _ at hspec
  obtain ⟨l, hl, hlsq⟩ := hspec
  have hmY : Mono (residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x)) :=
    (residueFieldRepresentative B S hS Y hYdec (pointsMap B S hS X f x)).2.2
  have e₁ : yoneda.map (k ≫ l) ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x) =
      fieldMorphism B S hS X q ≫ f :=
    (congrArg (· ≫ _) (yoneda.map_comp k l)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hlsq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) hk))))
  have e₂ : yoneda.map (h ≫ k') ≫ residueFieldMorphism B S hS Y hYdec (pointsMap B S hS X f x) =
      fieldMorphism B S hS X q ≫ f :=
    (congrArg (· ≫ _) (yoneda.map_comp h k')).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) hk').trans hsq))
  have heq : k ≫ l = h ≫ k' := yoneda.map_injective ((cancel_mono _).1 (e₁.trans e₂.symm))
  have hring : CommRingCat.ofHom (residueFieldHom B S hS X Y hY hXdec hYdec f x) ≫
      CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom φ'.toRingHom ≫ CommRingCat.ofHom ψ :=
    Spec.map_injective ((Spec.map_comp _ _).trans ((congrArg₂ (· ≫ ·) hφ hl).symm.trans
      ((B.inclusion.map_comp _ _).symm.trans
        ((congrArg (fun m ↦ B.inclusion.map m.left) heq).trans
          ((B.inclusion.map_comp _ _).trans ((congrArg₂ (· ≫ ·) hψ hφ').trans
            (Spec.map_comp _ _).symm))))))
  let := (residueFieldHom B S hS X Y hY hXdec hYdec f x).toAlgebra
  let := ψ.toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv φ' φ (congrArg CommRingCat.Hom.hom hring.symm)

end ResidueField

/-- **The fibre of an elementary étale chart.** Let `d` be a cartesian square of étale scheme
charts over `g : Z ⟶ Y`, with scheme morphism `r : U ⟶ V`, and let `e` be the only point of `V`
above `η ∈ |Y|`, with `Spec κ(e) ⟶ Y` a monomorphism. Then the points of `U` above `e` map
bijectively onto the points of `|Z|` above `η`. -/
theorem bijOn_chartSchemeToPoints_fibre {Z Y : AlgebraicSpaces B S hS}
    (g : Z ⟶ Y) (d : ChartDiagram B S hS Z.1 Y.1 g.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) g.hom d.V.1.hom) (η : points B S hS Y.1)
    (e : chartScheme d.V) (he : chartSchemeToPoints B S hS Y.1 d.V e = η)
    (huniq : ∀ e' : chartScheme d.V, chartSchemeToPoints B S hS Y.1 d.V e' = η → e' = e)
    (hmono : Mono (fieldMorphism B S hS Y.1 (chartSchemeFieldValuedPoint B S hS Y.1 d.V e))) :
    Set.BijOn (chartSchemeToPoints B S hS Z.1 d.U)
      {x : chartScheme d.U | ((BigFppfOver.toScheme B S hS).map d.g).base x = e}
      {z : points B S hS Z.1 | pointsMap B S hS Z.1 g.hom z = η} := by
  refine ⟨fun x hx ↦ ?_, injOn_chartSchemeToPoints_fibre B S hS d hd e hmono, fun z hz ↦ ?_⟩
  · change pointsMap B S hS Z.1 g.hom _ = η
    rw [← chartSchemeToPoints_map_chartDiagram, Set.mem_ofPred_eq.mp hx, he]
  · obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS hd z
      ((canonicalSiteFieldPoint B S hS _ e).class B S hS _)
      ((Set.mem_ofPred_eq.mp hz).trans he.symm)
    have hx : chartSchemeToPoints B S hS Z.1 d.U
        (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS Z.1).obj d.U) w) = z := by
      rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm, Equiv.symm_apply_apply]
      exact hw
    refine ⟨_, huniq _ ?_, hx⟩
    rw [chartSchemeToPoints_map_chartDiagram, hx]
    exact hz

/-- **Residue degrees over an elementary étale chart.** In the situation of
`AlgebraicGeometry.Space.bijOn_chartSchemeToPoints_fibre`, with affine charts, the residue degree
of the prime of `Γ(U)` at a point `x` above `e` over the prime of `Γ(V)` at `e` is the degree of
the residue field extension of the decent spaces at the point `z` of `|Z|` defined by `x`. -/
theorem primeResidueDegree_chartPrime_eq_finrank {Z Y : AlgebraicSpaces B S hS}
    (hZdec : IsDecentSpace B S hS Z.1) (hYdec : IsDecentSpace B S hS Y.1)
    (g : Z ⟶ Y) (d : ChartDiagram B S hS Z.1 Y.1 g.hom)
    (hd : IsPullback d.U.1.hom (yoneda.map d.g) g.hom d.V.1.hom) (η : points B S hS Y.1)
    (e : chartScheme d.V) (he : chartSchemeToPoints B S hS Y.1 d.V e = η)
    (huniq : ∀ e' : chartScheme d.V, chartSchemeToPoints B S hS Y.1 d.V e' = η → e' = e)
    (hmono : Mono (fieldMorphism B S hS Y.1 (chartSchemeFieldValuedPoint B S hS Y.1 d.V e)))
    (x : chartScheme d.U) (hx : ((BigFppfOver.toScheme B S hS).map d.g).base x = e)
    [IsAffine (chartScheme d.U)] [IsAffine (chartScheme d.V)] :
    Stacks.Length.primeResidueDegree (chartDiagramPullback B S hS g d).hom
        (chartPrimeAt B S hS Y.2 d.V e) (chartPrimeAt B S hS Z.2 d.U x) =
      letI := (residueFieldHom B S hS Z.1 Y.1 Y.2 hZdec hYdec g.hom
        (chartSchemeToPoints B S hS Z.1 d.U x)).toAlgebra
      Module.finrank (residueField B S hS Y.1 hYdec
          (pointsMap B S hS Z.1 g.hom (chartSchemeToPoints B S hS Z.1 d.U x)))
        (residueField B S hS Z.1 hZdec (chartSchemeToPoints B S hS Z.1 d.U x)) := by
  subst hx
  have hq' : (chartSchemeFieldValuedPoint B S hS Y.1 d.V
      (((BigFppfOver.toScheme B S hS).map d.g).base x)).class B S hS Y.1 =
        pointsMap B S hS Z.1 g.hom (chartSchemeToPoints B S hS Z.1 d.U x) :=
    chartSchemeToPoints_map_chartDiagram B S hS d x
  obtain ⟨h, hψ, -, hsq⟩ := exists_siteHom_chartSchemeFieldValuedPoint B S hS d x
  refine (Scheme.primeResidueDegree_comap_germ_eq_residueDegree
    ((BigFppfOver.toScheme B S hS).map d.g) x).trans ?_
  exact (finrank_residueFieldHom_eq_of_mono B S hS Z.2 Y.2 hZdec hYdec g.hom _ _ rfl
    (mono_fieldMorphism_chartSchemeFieldValuedPoint B S hS d hd x hmono) _ hq' hmono _ h hψ
    hsq).symm

end AlgebraicGeometry.Space

end
