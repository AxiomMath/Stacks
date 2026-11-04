module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.CountableOpens
public import StacksCore.Tactic.StacksAttribute

/-!
# Countability of the finite-type schemes over a countable Noetherian ring

Over a countable Noetherian ring there are only countably many isomorphism classes of schemes of
finite type. Each such scheme is glued from finitely many affine charts, each chart is the
spectrum of one of the countably many polynomial-quotient models of a finite-type algebra, and the
gluing is recorded by countably many opens and transition morphisms; the resulting gluing code
determines the scheme up to isomorphism over the base.

## Main results

* `AlgebraicGeometry.countable_isomorphismClasses_of_finiteType`: finite-type schemes over a
  countable Noetherian ring have countably many isomorphism classes.

## Implementation notes

A scheme over `R` is an object of `Over (Spec (.of R))`. The finite-type schemes form the full
subcategory cut out by `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact`, and isomorphism classes are the quotient by
`CategoryTheory.isIsomorphicSetoid`.

## References

* [Stacks Project, Tag 0G0U](https://stacks.math.columbia.edu/tag/0G0U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open pullback

universe u

namespace AlgebraicGeometry

/-- A finite-presentation code over a countable ring consists of finitely many variables and
a finitely generated ideal of the corresponding polynomial ring. These codes form a countable
type. -/
private theorem countable_affinePresentationCodes
    (R : Type u) [CommRing R] [Countable R] :
    Countable (Σ n : ℕ, {I : Ideal (MvPolynomial (Fin n) R) // I.FG}) := by
  classical
  have hR : Cardinal.mk R ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  have hpoly (n : ℕ) : Cardinal.mk (MvPolynomial (Fin n) R) ≤ Cardinal.aleph0 := by
    have hbound : Cardinal.mk (MvPolynomial (Fin n) R) ≤
        max Cardinal.aleph0 (Cardinal.mk R) := by
      obtain ⟨e⟩ : Nonempty (Fin n ≃ ULift.{u} (Fin n)) := ⟨Equiv.ulift.symm⟩
      rw [Cardinal.mk_congr (MvPolynomial.renameEquiv R e).toEquiv]
      refine (MvPolynomial.cardinalMk_le_max (σ := ULift.{u} (Fin n)) (R := R)).trans ?_
      refine max_le (max_le (le_max_right _ _) (le_trans ?_ (le_max_left _ _)))
        (le_max_left _ _)
      rw [Cardinal.mk_uLift, Cardinal.mk_fin]
      simp
    exact hbound.trans (max_le le_rfl hR)
  have (n : ℕ) : Countable (MvPolynomial (Fin n) R) :=
    Cardinal.mk_le_aleph0_iff.mp (hpoly n)
  have (n : ℕ) : Countable {I : Ideal (MvPolynomial (Fin n) R) // I.FG} :=
    (show Function.Surjective (fun s : Finset (MvPolynomial (Fin n) R) =>
      (⟨Ideal.span (s : Set (MvPolynomial (Fin n) R)),
        Submodule.fg_span s.finite_toSet⟩ :
        {I : Ideal (MvPolynomial (Fin n) R) // I.FG})) from by
      rintro ⟨I, ⟨s, hs⟩⟩
      exact ⟨s, Subtype.ext hs⟩).countable
  infer_instance

/-- Over a countable Noetherian base, the polynomial quotient presentations used for finite type
algebras form a countable family. -/
private theorem countable_fgAlgCatSkeleton
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (FGAlgCatSkeleton R) := by
  classical
  have : Countable (Σ n : ℕ, {I : Ideal (MvPolynomial (Fin n) R) // I.FG}) :=
    countable_affinePresentationCodes R
  let enc (P : FGAlgCatSkeleton R) :
      Σ n : ℕ, {I : Ideal (MvPolynomial (Fin n) R) // I.FG} :=
    ⟨P.n, ⟨P.I, P.I.fg_of_isNoetherianRing⟩⟩
  have hinj : Function.Injective enc := by
    rintro ⟨n, I⟩ ⟨m, J⟩ h
    dsimp [enc] at h
    cases h
    rfl
  exact hinj.countable

/-- The coordinate ring of an affine chart mapping locally finitely to `Spec R` is a finite
type `R`-algebra. -/
private theorem affineChart_sections_finiteType
    (R : Type u) [CommRing R] (U : Scheme) (g : U ⟶ Spec (.of R))
    [IsAffine U] [LocallyOfFiniteType g] :
    RingHom.FiniteType
      (g.appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.toRingHom) :=
  (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) g inferInstance).comp
    (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The structure map of an affine chart, read as a ring homomorphism from the base ring to the
global sections of the chart. -/
private noncomputable def affineChartAlgebraMap
    (R : Type u) [CommRing R] {U : Scheme} (g : U ⟶ Spec (.of R)) :
    R →+* Γ(U, ⊤) :=
  (g.appTop).hom.comp
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.toRingHom

/-- Every affine chart of finite type over the base is the spectrum of one of the countably many
polynomial-quotient models. -/
private theorem affineChart_has_model
    (R : Type u) [CommRing R] (U : Scheme) (g : U ⟶ Spec (.of R))
    [IsAffine U] [LocallyOfFiniteType g] :
    ∃ P : FGAlgCatSkeleton R, ∃ e : Γ(U, ⊤) ≃+* P.eval.obj,
      ∀ r, e (affineChartAlgebraMap R g r) = algebraMap R (P.eval.obj : Type u) r := by
  let : Algebra R Γ(U, ⊤) := (affineChartAlgebraMap R g).toAlgebra
  have : Algebra.FiniteType R Γ(U, ⊤) :=
    RingHom.finiteType_algebraMap.mp (affineChart_sections_finiteType R U g)
  obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R Γ(U, ⊤)
  exact ⟨P, e.toRingEquiv, e.commutes⟩

/-- The affine scheme attached to a polynomial-quotient code, equipped with its structure map
to the base. -/
private noncomputable abbrev affineModelOver (R : Type u) [CommRing R]
    (P : FGAlgCatSkeleton R) :
    Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (P.eval.obj : Type u))))

/-- The underlying affine scheme of a polynomial-quotient code. -/
private noncomputable abbrev affineModelScheme (R : Type u) [CommRing R]
    (P : FGAlgCatSkeleton R) : Scheme := Spec (.of (P.eval.obj : Type u))

/-- An affine chart is isomorphic over the base to the model matching its ring of sections. -/
private noncomputable def affineChartOverIso
    (R : Type u) [CommRing R] (U : Scheme) (g : U ⟶ Spec (.of R))
    [IsAffine U] (P : FGAlgCatSkeleton R)
    (e : Γ(U, ⊤) ≃+* P.eval.obj)
    (he : ∀ r, e (affineChartAlgebraMap R g r) = algebraMap R (P.eval.obj : Type u) r) :
    affineModelOver R P ≅ Over.mk g := by
  let f : R →+* Γ(U, ⊤) := affineChartAlgebraMap R g
  letI : Algebra R Γ(U, ⊤) := f.toAlgebra
  letI : Algebra R P.eval.obj := algebraMap R (P.eval.obj : Type u) |>.toAlgebra
  let eAlg : Γ(U, ⊤) ≃ₐ[R] P.eval.obj :=
    { e with commutes' := he }
  haveI : IsAffine U := inferInstance
  letI : U.Over (Spec (.of R)) := ⟨g⟩
  let V : Over (Spec (.of R)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(U, ⊤))))
  let W : Over (Spec (.of R)) := Over.mk g
  let hVW : V ≅ W := Over.isoMk U.isoSpec.symm (by
    change U.isoSpec.inv ≫ W.hom = V.hom
    calc
      U.isoSpec.inv ≫ g = Spec.map (g.appTop) ≫ (Spec (.of R)).isoSpec.inv :=
        (Scheme.isoSpec_inv_naturality g).symm
      _ = Spec.map (CommRingCat.ofHom (algebraMap R Γ(U, ⊤))) := by
        rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
        congr 1)
  let hPV : affineModelOver R P ≅ V :=
    (AlgebraicGeometry.algSpec (.of R)).mapIso (CommAlgCat.isoMk eAlg).op
  exact hPV ≪≫ hVW

/-- The scheme underlying an affine model is affine. -/
private theorem affineModelOver_isAffine (R : Type u) [CommRing R] (P : FGAlgCatSkeleton R) :
    IsAffine (affineModelOver R P).left :=
  inferInstanceAs (IsAffine (Spec (.of (P.eval.obj : Type u))))

/-- The structure map of an affine model is locally of finite type. -/
private theorem affineModelOver_locallyOfFiniteType
    (R : Type u) [CommRing R] (P : FGAlgCatSkeleton R) :
    LocallyOfFiniteType (affineModelOver R P).hom := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap R (P.eval.obj : Type u))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr
    (inferInstance : Algebra.FiniteType R (P.eval.obj : Type u))

/-- The basic affine charts occurring in the gluing code have countably many opens. -/
private theorem countable_affineModel_opens
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R]
    (P : FGAlgCatSkeleton R) : Countable ((Spec (.of (P.eval.obj : Type u))).Opens) := by
  have := affineModelOver_isAffine R P
  have := affineModelOver_locallyOfFiniteType R P
  have : QuasiCompact (affineModelOver R P).hom := inferInstance
  exact countable_opens_of_affine_finiteType (affineModelOver R P)

/-- An open subscheme of an affine model, with its structure map to the base. -/
private noncomputable def affineModelOpenOver (R : Type u) [CommRing R]
    (P : FGAlgCatSkeleton R) (U : ((affineModelOver R P).left).Opens) :
    Over (Spec (.of R)) :=
  Over.mk (U.ι ≫ (affineModelOver R P).hom)

/-- Between opens of two affine models there are only countably many morphisms over the base. -/
private theorem countable_affineModelOpen_hom
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R]
    (P Q : FGAlgCatSkeleton R) (U : ((affineModelOver R P).left).Opens)
    (V : ((affineModelOver R Q).left).Opens) :
    Countable (affineModelOpenOver R P U ⟶ affineModelOpenOver R Q V) := by
  have := affineModelOver_isAffine R P
  have := affineModelOver_isAffine R Q
  have := affineModelOver_locallyOfFiniteType R P
  have := affineModelOver_locallyOfFiniteType R Q
  have : QuasiCompact (affineModelOver R P).hom := inferInstance
  have : QuasiCompact (affineModelOver R Q).hom := inferInstance
  exact countable_open_hom_of_affine_finiteType (affineModelOver R P) (affineModelOver R Q) U V

/-- Raw overlap and transition data on a finite list of the affine presentation models. -/
private noncomputable def finiteGluingRaw
    (R : Type u) [CommRing R] (n : ℕ)
    (P : Fin n → FGAlgCatSkeleton R) :=
  Σ W : ∀ i _j, (affineModelScheme R (P i)).Opens,
    (∀ i j,
      affineModelOpenOver R (P i) (W i j) ⟶
        affineModelOpenOver R (P j) (W j i))

/-- The overlap and transition data on a fixed finite list of models form a countable type. -/
private theorem countable_finiteGluingRaw
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R]
    (n : ℕ) (P : Fin n → FGAlgCatSkeleton R) : Countable (finiteGluingRaw R n P) := by
  classical
  have (i : Fin n) : Countable (affineModelScheme R (P i)).Opens :=
    countable_affineModel_opens R (P i)
  have (W : ∀ i j : Fin n, (affineModelScheme R (P i)).Opens) (i j : Fin n) :
      Countable (affineModelOpenOver R (P i) (W i j) ⟶
        affineModelOpenOver R (P j) (W j i)) :=
    countable_affineModelOpen_hom R (P i) (P j) (W i j) (W j i)
  unfold finiteGluingRaw
  infer_instance

/-- All overlap and transition data, over all finite lists of models. -/
private noncomputable def finiteGluingAll (R : Type u) [CommRing R] :=
  Σ n : ℕ, Σ P : Fin n → FGAlgCatSkeleton R, finiteGluingRaw R n P

/-- The whole gluing-code type is countable. -/
private theorem countable_finiteGluingAll
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (finiteGluingAll R) := by
  classical
  have : Countable (FGAlgCatSkeleton R) := countable_fgAlgCatSkeleton R
  have (n : ℕ) : Countable (Fin n → FGAlgCatSkeleton R) := inferInstance
  have (n : ℕ) (P : Fin n → FGAlgCatSkeleton R) : Countable (finiteGluingRaw R n P) :=
    countable_finiteGluingRaw R n P
  change Countable (Σ n : ℕ, Σ P : Fin n → FGAlgCatSkeleton R,
    finiteGluingRaw R n P)
  infer_instance

/-- An affine atlas of a finite type scheme, recorded on the countable affine models. -/
private structure finiteModelAtlas
    (R : Type u) [CommRing R] (X : Over (Spec (.of R)))
    (n : ℕ) (P : Fin n → FGAlgCatSkeleton R) where
  f : ∀ i, affineModelOver R (P i) ⟶ X
  f_open : ∀ i, IsOpenImmersion (f i).left
  covers : ∀ x : X.left, ∃ i y, (f i).left y = x
  W : ∀ i _j, (affineModelScheme R (P i)).Opens
  transitions : ∀ i j,
    affineModelOpenOver R (P i) (W i j) ⟶ affineModelOpenOver R (P j) (W j i)
  transition_fac : ∀ i j,
    (W i j).ι ≫ (f i).left = (transitions i j).left ≫ (W j i).ι ≫ (f j).left
  overlap : ∀ i j,
    Set.range (pullback.fst (f i).left (f j).left).base ⊆
      Set.range (W i j).ι.base

/-- The charts of a finite model atlas form an open cover of the scheme. -/
private noncomputable def finiteModelAtlas.openCover
    {R : Type u} [CommRing R] {X : Over (Spec (.of R))} {n : ℕ}
    {P : Fin n → FGAlgCatSkeleton R} (A : finiteModelAtlas R X n P) :
    Scheme.OpenCover X.left where
  I₀ := Fin n
  X i := affineModelScheme R (P i)
  f i := (A.f i).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨A.covers, A.f_open⟩

/-- The gluing code of a finite model atlas: its overlaps and transitions. -/
private noncomputable def finiteModelAtlas.code
    {R : Type u} [CommRing R] {X : Over (Spec (.of R))} {n : ℕ}
    {P : Fin n → FGAlgCatSkeleton R} (A : finiteModelAtlas R X n P) :
  finiteGluingRaw R n P :=
  ⟨A.W, A.transitions⟩

/-- Two atlases with the same overlap code give compatible maps on the pullbacks of their
charts. -/
private theorem finiteModelAtlas.compatible_of_code_eq
    {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))} {n : ℕ}
    {P : Fin n → FGAlgCatSkeleton R}
    (A : finiteModelAtlas R X n P) (B : finiteModelAtlas R Y n P)
    (h : A.code = B.code) (i j : Fin n) :
    pullback.fst (A.f i).left (A.f j).left ≫ (B.f i).left =
      pullback.snd (A.f i).left (A.f j).left ≫ (B.f j).left := by
  cases B with
  | mk fB fB_open B_covers W_B transitions_B transition_fac_B =>
  change (⟨A.W, A.transitions⟩ : finiteGluingRaw R n P) =
    ⟨W_B, transitions_B⟩ at h
  have hW : A.W = W_B := (Sigma.ext_iff.mp h).1
  cases hW
  change (⟨A.W, A.transitions⟩ : finiteGluingRaw R n P) =
    ⟨A.W, transitions_B⟩ at h
  cases h
  let p := pullback (A.f i).left (A.f j).left
  have : IsOpenImmersion (A.f j).left := A.f_open j
  have hrange := A.overlap i j
  let q : p ⟶ A.W i j := IsOpenImmersion.lift (A.W i j).ι
    (pullback.fst (A.f i).left (A.f j).left) hrange
  have hq : q ≫ (A.W i j).ι = pullback.fst (A.f i).left (A.f j).left :=
    IsOpenImmersion.lift_fac _ _ _
  have hqt : q ≫ (A.transitions i j).left ≫ (A.W j i).ι =
      pullback.snd (A.f i).left (A.f j).left := by
    apply (cancel_mono (A.f j).left).1
    calc
      q ≫ (A.transitions i j).left ≫ (A.W j i).ι ≫ (A.f j).left =
          q ≫ ((A.transitions i j).left ≫ (A.W j i).ι ≫ (A.f j).left) := by
            simp
      _ = q ≫ ((A.W i j).ι ≫ (A.f i).left) :=
        congrArg (fun k => q ≫ k) (A.transition_fac i j).symm
      _ = (q ≫ (A.W i j).ι) ≫ (A.f i).left := by simp [Category.assoc]
      _ = pullback.fst (A.f i).left (A.f j).left ≫ (A.f i).left := by rw [hq]
      _ = pullback.snd (A.f i).left (A.f j).left ≫ (A.f j).left :=
        pullback.condition
  calc
    pullback.fst (A.f i).left (A.f j).left ≫ (fB i).left =
        q ≫ (A.W i j).ι ≫ (fB i).left := by
          rw [← Category.assoc, hq]
    _ = q ≫ ((A.W i j).ι ≫ (fB i).left) := by simp
    _ = q ≫ ((A.transitions i j).left ≫ (A.W j i).ι ≫ (fB j).left) :=
      congrArg (fun k => q ≫ k) (transition_fac_B i j)
    _ = pullback.snd (A.f i).left (A.f j).left ≫ (fB j).left :=
      congrArg (fun k => k ≫ (fB j).left) hqt

/-- A morphism of underlying schemes that restricts to the charts of another atlas commutes with
the structure maps. -/
private theorem finiteModelAtlas.comp_hom_eq
    {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))} {n : ℕ}
    {P : Fin n → FGAlgCatSkeleton R}
    (A : finiteModelAtlas R X n P) (B : finiteModelAtlas R Y n P) (g : X.left ⟶ Y.left)
    (hg : ∀ i, (A.f i).left ≫ g = (B.f i).left) : g ≫ Y.hom = X.hom := by
  refine A.openCover.hom_ext _ _ fun i => ?_
  change (A.f i).left ≫ g ≫ Y.hom = (A.f i).left ≫ X.hom
  rw [← Category.assoc, hg i, (B.f i).w, (A.f i).w]

/-- Two morphisms of underlying schemes that send the charts of one atlas to those of the other
and back compose to the identity. -/
private theorem finiteModelAtlas.comp_eq_id
    {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))} {n : ℕ}
    {P : Fin n → FGAlgCatSkeleton R}
    (A : finiteModelAtlas R X n P) (B : finiteModelAtlas R Y n P) (g : X.left ⟶ Y.left)
    (g' : Y.left ⟶ X.left) (hg : ∀ i, (A.f i).left ≫ g = (B.f i).left)
    (hg' : ∀ i, (B.f i).left ≫ g' = (A.f i).left) : g ≫ g' = 𝟙 X.left := by
  refine A.openCover.hom_ext _ _ fun i => ?_
  change (A.f i).left ≫ g ≫ g' = (A.f i).left ≫ 𝟙 X.left
  rw [← Category.assoc, hg i, hg' i, Category.comp_id]

/-- Equal finite atlas codes determine isomorphic objects over the base. -/
private noncomputable def finiteModelAtlas.iso_of_code_eq
    {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))} {n : ℕ}
    {P : Fin n → FGAlgCatSkeleton R}
    (A : finiteModelAtlas R X n P) (B : finiteModelAtlas R Y n P)
    (h : A.code = B.code) : X ≅ Y := by
  let fwd : X.left ⟶ Y.left := A.openCover.glueMorphisms
    (fun i => (B.f i).left) (A.compatible_of_code_eq B h)
  let bwd : Y.left ⟶ X.left := B.openCover.glueMorphisms
    (fun i => (A.f i).left) (B.compatible_of_code_eq A h.symm)
  have hfwd (i : Fin n) : (A.f i).left ≫ fwd = (B.f i).left :=
    A.openCover.ι_glueMorphisms _ _ i
  have hbwd (i : Fin n) : (B.f i).left ≫ bwd = (A.f i).left :=
    B.openCover.ι_glueMorphisms _ _ i
  exact Over.isoMk ⟨fwd, bwd, A.comp_eq_id B fwd bwd hfwd hbwd, B.comp_eq_id A bwd fwd hbwd hfwd⟩
    (A.comp_hom_eq B fwd hfwd)

/-- Every scheme of finite type over a countable Noetherian base admits a finite model atlas. -/
private theorem exists_finiteModelAtlas
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R]
    (X : Over (Spec (.of R))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    ∃ n : ℕ, ∃ P : Fin n → FGAlgCatSkeleton R,
      Nonempty (finiteModelAtlas R X n P) := by
  classical
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let C := X.left.affineCover.finiteSubcover
  let n := Fintype.card C.I₀
  let eFin : C.I₀ ≃ Fin n := Fintype.equivFin C.I₀
  let chartObj (i : Fin n) := C.X (eFin.symm i)
  let chartMap (i : Fin n) : chartObj i ⟶ Spec (.of R) :=
    C.f (eFin.symm i) ≫ X.hom
  have hmodels (i : Fin n) :
      ∃ P : FGAlgCatSkeleton R,
        ∃ e : Γ(chartObj i, ⊤) ≃+* P.eval.obj,
          ∀ r, e (affineChartAlgebraMap R (chartMap i) r) =
            algebraMap R (P.eval.obj : Type u) r :=
    affineChart_has_model R (chartObj i) (chartMap i)
  let P : Fin n → FGAlgCatSkeleton R := fun i => Classical.choose (hmodels i)
  have heqs (i : Fin n) :
      ∃ e : Γ(chartObj i, ⊤) ≃+* (P i).eval.obj,
        ∀ r, e (affineChartAlgebraMap R (chartMap i) r) =
          algebraMap R ((P i).eval.obj : Type u) r :=
    Classical.choose_spec (hmodels i)
  let e (i : Fin n) := Classical.choose (heqs i)
  have he (i : Fin n) := Classical.choose_spec (heqs i)
  let chartIso (i : Fin n) :=
    affineChartOverIso R (chartObj i) (chartMap i) (P i) (e i) (he i)
  let post (i : Fin n) :
      Over.mk (C.f (eFin.symm i) ≫ X.hom) ⟶ X :=
    Over.homMk (C.f (eFin.symm i)) rfl
  let f (i : Fin n) : affineModelOver R (P i) ⟶ X := (chartIso i).hom ≫ post i
  have hfopen (i : Fin n) : IsOpenImmersion (f i).left := by
    have : IsIso (chartIso i).hom := (chartIso i).isIso_hom
    have : IsIso (chartIso i).hom.left := by
      simpa [Over.forget_map] using
        (Functor.map_isIso (Over.forget (Spec (.of R))) (chartIso i).hom)
    have h₁ : IsOpenImmersion (chartIso i).hom.left := IsOpenImmersion.of_isIso _
    have h₂ : IsOpenImmersion (C.f (eFin.symm i)) := C.map_prop (eFin.symm i)
    change IsOpenImmersion ((chartIso i).hom.left ≫ C.f (eFin.symm i))
    exact @IsOpenImmersion.comp _ _ _ _ _ h₁ h₂
  have (i : Fin n) : IsOpenImmersion (f i).left := hfopen i
  let W (i j : Fin n) : (affineModelScheme R (P i)).Opens :=
    (f i).left ⁻¹ᵁ (f j).left.opensRange
  have hRange (i j : Fin n) :
      Set.range (fun z => ((W i j).ι ≫ (f i).left).base z) ⊆
        Set.range (fun z => ((W j i).ι ≫ (f j).left).base z) := by
    rintro y ⟨z, rfl⟩
    have hz := z.property
    change (f i).left z.val ∈ Set.range (f j).left.base at hz
    obtain ⟨w, hw⟩ := hz
    have hw' : (f j).left w ∈ Set.range (f i).left.base := by
      rw [hw]
      exact ⟨z.val, rfl⟩
    refine ⟨⟨w, hw'⟩, ?_⟩
    change (f j).left w = (f i).left z.val
    exact hw
  let trans (i j : Fin n) :
      Scheme.Hom (W i j) (W j i) := by
    have h₁ : IsOpenImmersion ((W j i).ι ≫ (f j).left) :=
      @IsOpenImmersion.comp _ _ _ _ _ (by infer_instance) (hfopen j)
    exact @IsOpenImmersion.lift _ _ _ ((W j i).ι ≫ (f j).left)
      ((W i j).ι ≫ (f i).left) h₁ (hRange i j)
  have hfac (i j : Fin n) :
      (W i j).ι ≫ (f i).left = trans i j ≫ (W j i).ι ≫ (f j).left := by
    have h₁ : IsOpenImmersion ((W j i).ι ≫ (f j).left) :=
      @IsOpenImmersion.comp _ _ _ _ _ (by infer_instance) (hfopen j)
    exact (@IsOpenImmersion.lift_fac _ _ _ ((W j i).ι ≫ (f j).left)
      ((W i j).ι ≫ (f i).left) h₁ (hRange i j)).symm
  have hbase (i j : Fin n) :
      trans i j ≫ (W j i).ι ≫ (affineModelOver R (P j)).hom =
        (W i j).ι ≫ (affineModelOver R (P i)).hom := by
    calc
      trans i j ≫ (W j i).ι ≫ (affineModelOver R (P j)).hom =
          trans i j ≫ (W j i).ι ≫ (f j).left ≫ X.hom := by rw [← (f j).w]
      _ = (W i j).ι ≫ (f i).left ≫ X.hom :=
        congrArg (fun k => k ≫ X.hom) (hfac i j).symm
      _ = (W i j).ι ≫ (affineModelOver R (P i)).hom := by rw [(f i).w]
  let transition (i j : Fin n) :
      affineModelOpenOver R (P i) (W i j) ⟶ affineModelOpenOver R (P j) (W j i) :=
    Over.homMk (trans i j) (hbase i j)
  have hcover (x : X.left) : ∃ i y, (f i).left y = x := by
    obtain ⟨c, y, hy⟩ := C.exists_eq x
    let i := eFin c
    have hi0 : i = eFin c := rfl
    clear_value i
    have hi : eFin.symm i = c := by
      rw [hi0]
      exact eFin.symm_apply_apply c
    cases hi
    refine ⟨i, (chartIso i).inv.left y, ?_⟩
    dsimp [f, post]
    have hcancel : (chartIso i).hom.left ((chartIso i).inv.left y) = y := by
      have hiso : (chartIso i).inv.left ≫ (chartIso i).hom.left = 𝟙 (chartObj i) :=
        congrArg (fun q => q.left) (Iso.inv_hom_id (chartIso i))
      exact ConcreteCategory.congr_hom (congrArg (fun q => q.base) hiso) y
    rw [hcancel]
    exact hy
  refine ⟨n, P, ⟨?_⟩⟩
  refine ⟨f, hfopen, hcover, W, transition, hfac, fun i j => ?_⟩
  rintro x ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (f i).left.base ((pullback.fst (f i).left (f j).left).base z) ∈
    Set.range (f j).left.base
  exact ⟨(pullback.snd (f i).left (f j).left).base z,
    (congrArg (fun k : pullback (f i).left (f j).left ⟶ X.left => k.base z)
      pullback.condition).symm⟩

/-- The full subcategory of schemes of finite type over the base. -/
private abbrev finiteTypeOver (R : Type u) [CommRing R] :=
  ObjectProperty.FullSubcategory (fun X : Over (Spec (.of R)) =>
    LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)

/-- The codes that arise from an actual finite atlas. -/
private def realizableFiniteGluing (R : Type u) [CommRing R] :=
  {c : finiteGluingAll R //
    ∃ X : finiteTypeOver R, ∃ A : finiteModelAtlas R X.1 c.1 c.2.1,
      A.code = c.2.2}

/-- A scheme realising a given realizable gluing code. -/
private noncomputable def realizableFiniteGluing.target
    (R : Type u) [CommRing R] (c : realizableFiniteGluing R) : finiteTypeOver R :=
  Classical.choose c.2

/-- The chosen realising scheme carries an atlas with the given code. -/
private theorem realizableFiniteGluing.exists_atlas
    (R : Type u) [CommRing R] (c : realizableFiniteGluing R) :
    ∃ A : finiteModelAtlas R (c.target R).1 c.1.1 c.1.2.1,
      A.code = c.1.2.2 :=
  Classical.choose_spec c.2

/-- The isomorphism class of the scheme realising a gluing code. -/
private noncomputable def realizableFiniteGluing.toIsoClass
    (R : Type u) [CommRing R] (c : realizableFiniteGluing R) :
    Quotient (isIsomorphicSetoid (finiteTypeOver R)) :=
  Quotient.mk _ (c.target R)

/-- Every isomorphism class of a finite-type scheme is realised by a gluing code. -/
private theorem surjective_toIsoClass
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Function.Surjective (realizableFiniteGluing.toIsoClass R) := by
  classical
  intro q
  refine Quotient.inductionOn q fun X => ?_
  have : LocallyOfFiniteType X.1.hom := X.2.1
  have : QuasiCompact X.1.hom := X.2.2
  obtain ⟨n, P, ⟨A⟩⟩ := exists_finiteModelAtlas R X.1
  let code : finiteGluingAll R := ⟨n, P, A.code⟩
  let c : realizableFiniteGluing R := ⟨code, X, A, rfl⟩
  refine ⟨c, ?_⟩
  obtain ⟨A', hA'⟩ := c.exists_atlas R
  exact Quotient.sound
    ⟨ObjectProperty.isoMk _ (A'.iso_of_code_eq A (by simpa [c, code] using hA'))⟩

/-- There are countably many isomorphism classes of schemes of finite type over a countable
Noetherian ring. -/
@[stacks 0G0U "countable_iso_classes"]
public theorem countable_isomorphismClasses_of_finiteType
    (R : Type u) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable
      (Quotient (isIsomorphicSetoid
        (ObjectProperty.FullSubcategory (fun X : Over (Spec (.of R)) =>
          LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)))) := by
  classical
  have : Countable (finiteGluingAll R) := countable_finiteGluingAll R
  have : Countable (realizableFiniteGluing R) := Subtype.countable
  exact (surjective_toIsoClass R).countable

end AlgebraicGeometry
