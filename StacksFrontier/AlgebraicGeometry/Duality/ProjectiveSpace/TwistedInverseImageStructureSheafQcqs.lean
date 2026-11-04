module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperFlatRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTraceRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.SheafHom
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.PseudoCoherentByPseudoCoherentTwists
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic

/-!
# The twisted inverse image of the structure sheaf on projective space over a qcqs base

Let `Y` be a quasi-compact and quasi-separated scheme, `n ≥ 0`, `f : X = ℙⁿ_Y ⟶ Y` the structure
morphism and `a` the right adjoint of `R f_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E].
Then `a(𝒪_Y) ≅ 𝒪(-n-1)[n]`: the case `ℰ = 𝒪_Y^{⊕ n+1}` of [Stacks, Tag 0A9W].

The proof is the source's. The trace `R f_*(𝒪(-n-1)[n]) ≅ 𝒪_Y` determines
`c : 𝒪(-n-1)[n] ⟶ a(𝒪_Y)` by adjunction. Whether `c` is invertible is local on `X`, and the
inverse images `ℙⁿ_V` of the affine opens `V ⊆ Y` cover `X`. Over `V`, the map
`(j')^* a ⟶ a_V j^*` of [Stacks, Tag 0A9L] is invertible at `𝒪_Y` ([Stacks, Tag 0A9P] (1):
`f` is proper, flat and of finite presentation), and it carries `(j')^* c` to a morphism
`𝒪(-n-1)[n] ⟶ a_V(𝒪_V)` whose transpose is the restriction of the trace, followed by the base
change isomorphism `j^* R f_* ≅ R f'_* (j')^*`. A morphism `𝒪(-n-1)[n] ⟶ a_V(𝒪_V)` with
invertible transpose differs from the comparison map of the affine case by an automorphism of
`𝒪_V`, so it is invertible by the affine case.

## Main results

* `Stacks.Duality.ProjectiveSpace.qcqsDualizingTwistComparison` — the comparison map `c`.
* `Stacks.Duality.ProjectiveSpace.isIso_qcqsDualizingTwistComparison` — `c` is an isomorphism.
* `Stacks.Duality.ProjectiveSpace.nonempty_twistedInverseImage_derivedStructureSheaf_iso_of_qcqs`
  — `a(𝒪_Y) ≅ 𝒪(-n-1)[n]`.

## References

* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace Stacks.Duality.ProjectiveSpace

/-! ### Transposes through the map of Tag 0A9L -/

section Formal

variable {Ct Ct₁ Cx Cx' : Type*} [Category Ct] [Category Ct₁] [Category Cx] [Category Cx']
  {Li : Ct ⥤ Cx} {Ri : Cx ⥤ Ct} {Lj : Ct₁ ⥤ Cx'} {Rj : Cx' ⥤ Ct₁} {Rh : Ct ⥤ Ct₁}
  {a : Ct₁ ⥤ Ct} {Rf : Cx ⥤ Cx'} {a' : Cx' ⥤ Cx}
  (adjI : Li ⊣ Ri) (adjJ : Lj ⊣ Rj) (adjH : Rh ⊣ a) (adjF : Rf ⊣ a')
  (σ : Ri ⋙ Rh ⟶ Rf ⋙ Rj)

/-- The base change map `Lj ∘ Rh ⟶ Rf ∘ Li` built from the unit of `Li ⊣ Ri`, the square `σ` and
the counit of `Lj ⊣ Rj` is natural. -/
theorem baseChange_naturality {P Q : Ct} (c : P ⟶ Q) :
    Lj.map (Rh.map (adjI.unit.app P)) ≫ Lj.map (σ.app (Li.obj P)) ≫
        adjJ.counit.app (Rf.obj (Li.obj P)) ≫ Rf.map (Li.map c) =
      Lj.map (Rh.map c) ≫ Lj.map (Rh.map (adjI.unit.app Q)) ≫ Lj.map (σ.app (Li.obj Q)) ≫
        adjJ.counit.app (Rf.obj (Li.obj Q)) := by
  have h1 := adjJ.counit.naturality (Rf.map (Li.map c))
  have h2 := σ.naturality (Li.map c)
  have h3 := adjI.unit.naturality c
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h1 h2 h3
  have key : Rh.map (adjI.unit.app P) ≫ σ.app (Li.obj P) ≫ Rj.map (Rf.map (Li.map c)) =
      Rh.map c ≫ Rh.map (adjI.unit.app Q) ≫ σ.app (Li.obj Q) := by
    rw [← h2, ← Rh.map_comp_assoc, ← h3, Rh.map_comp_assoc]
  rw [← h1]
  simpa only [Lj.map_comp, Category.assoc] using
    congrArg (fun g => Lj.map g ≫ adjJ.counit.app (Rf.obj (Li.obj Q))) key

/-- **The transpose of `γ ∘ Li(c)`.** Let `γ : Li ∘ a ⟶ a' ∘ Lj` be the map of [Stacks, Tag 0A9L]
attached to the adjunctions and the mate `ξ` of `σ`. For `c : P ⟶ a(K)`, the transpose of
`γ_K ∘ Li(c)` across `Rf ⊣ a'`, preceded by the base change map at `P`, is `Lj` of the transpose
of `c` across `Rh ⊣ a`. -/
theorem baseChange_comp_homEquiv_symm_restrictionMap (ξ : a' ⋙ Ri ⟶ Rj ⋙ a) [IsIso ξ]
    (hξ : ∀ N, Rh.map (ξ.app N) ≫ adjH.counit.app (Rj.obj N) =
      σ.app (a'.obj N) ≫ Rj.map (adjF.counit.app N))
    (K : Ct₁) (γK : Li.obj (a.obj K) ⟶ a'.obj (Lj.obj K))
    (hγ : γK = Li.map (a.map (adjJ.unit.app K)) ≫ Li.map ((inv ξ).app (Lj.obj K)) ≫
      adjI.counit.app (a'.obj (Lj.obj K)))
    {P : Ct} (c : P ⟶ a.obj K) :
    Lj.map (Rh.map (adjI.unit.app P)) ≫ Lj.map (σ.app (Li.obj P)) ≫
        adjJ.counit.app (Rf.obj (Li.obj P)) ≫ (adjF.homEquiv _ _).symm (Li.map c ≫ γK) =
      Lj.map ((adjH.homEquiv _ _).symm c) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Lj.map_comp,
    Stacks.Duality.map_counit_eq_restrictionMap adjI adjJ adjH adjF σ ξ hξ K γK hγ]
  simp only [Category.assoc]
  rw [reassoc_of% (baseChange_naturality adjI adjJ σ c)]

end Formal

/-! ### The comparison map over a quasi-compact quasi-separated base -/

section Comparison

variable (n : ℕ) (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The trace `R f_*(𝒪(-n-1)[n]) ≅ 𝒪_Y` of the proof of [Stacks, Tag 0A9W], as an isomorphism in
`D_QCoh(𝒪_Y)`, for `Y` quasi-compact and quasi-separated. -/
noncomputable def qcqsDualizingTwistTraceIso :
    (quasiCoherentDerivedPushforward (projectiveSpaceOver n Y ↘ Y)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n Y ↘ Y))).obj
        (dualizingTwist n Y) ≅ DerivedPushforward.derivedStructureSheaf Y :=
  ObjectProperty.isoMk _ (dualizingTwistTrace n Y)

/-- **The comparison map `c : 𝒪(-n-1)[n] ⟶ a(𝒪_Y)`** of the proof of [Stacks, Tag 0A9W] on
`ℙⁿ_Y`, for `Y` quasi-compact and quasi-separated: the morphism adjoint to the trace
`R f_*(𝒪(-n-1)[n]) ≅ 𝒪_Y` under `R f_* ⊣ a`. -/
noncomputable def qcqsDualizingTwistComparison :
    dualizingTwist n Y ⟶ (twistedInverseImage (projectiveSpaceOver n Y ↘ Y)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n Y ↘ Y))).obj
        (DerivedPushforward.derivedStructureSheaf Y) :=
  (twistedInverseImageAdjunction (projectiveSpaceOver n Y ↘ Y)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n Y ↘ Y))).homEquiv
    _ _ (qcqsDualizingTwistTraceIso n Y).hom

end Comparison

/-! ### Over an affine base: morphisms with invertible transpose -/

section TransposeCriterion

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- Let `t : F(K) ≅ O` be an isomorphism whose transpose `K ⟶ G(O)` is invertible. Then every
`g : K ⟶ G(M)` with invertible transpose is invertible: it is the transpose of `t` followed by
`G` of the isomorphism `t⁻¹ ≫ ĝ : O ≅ M`. -/
theorem isIso_of_isIso_homEquiv_symm_of_isIso {K : C} {O M : D} (t : F.obj K ≅ O)
    (ht : IsIso (adj.homEquiv _ _ t.hom)) (g : K ⟶ G.obj M)
    (hg : IsIso ((adj.homEquiv _ _).symm g)) : IsIso g := by
  have e : g = adj.homEquiv _ _ t.hom ≫ G.map (t.inv ≫ (adj.homEquiv _ _).symm g) := by
    rw [← Adjunction.homEquiv_naturality_right, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  rw [e]
  infer_instance

end TransposeCriterion

section AffineCriterion

variable (n : ℕ) (S : Scheme.{u}) [IsAffine S]

/-- On `ℙⁿ_S`, `S` affine, a morphism `g : 𝒪(-n-1)[n] ⟶ a(M)` whose transpose
`R f_*(𝒪(-n-1)[n]) ⟶ M` is invertible is invertible: it is the comparison map of the affine case
followed by `a` of an isomorphism `𝒪_S ≅ M`. -/
theorem isIso_of_isIso_homEquiv_symm {M : quasiCoherentDerivedCategory S}
    (g : dualizingTwist n S ⟶ (twistedInverseImage (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n S ↘ S))).obj M)
    (hg : IsIso (((twistedInverseImageAdjunction (projectiveSpaceOver n S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        (projectiveSpaceOver n S ↘ S))).homEquiv _ _).symm g)) :
    IsIso g :=
  isIso_of_isIso_homEquiv_symm_of_isIso _ (dualizingTwistTraceIso n S)
    (isIso_dualizingTwistComparison n S) g hg

/-- On `P^n_A = Proj A[T₀, …, Tₙ]`, a morphism `g : 𝒪(-n-1)[n] ⟶ a(M)` whose transpose
`R f_*(𝒪(-n-1)[n]) ⟶ M` is invertible is invertible, by the invertibility of the trace map. -/
theorem isIso_of_isIso_pushTwistedAdj_homEquiv_symm (A : Type u) [CommRing A]
    {M : quasiCoherentDerivedCategory (Spec (CommRingCat.of A))}
    (g : topTwist A n ⟶ (twistedQ A n).obj M)
    (hg : IsIso (((pushTwistedAdj A n).homEquiv _ _).symm g)) :
    IsIso g :=
  isIso_of_isIso_homEquiv_symm_of_isIso _ (pushTopTwistIso A n) (isIso_traceMap A n) g hg

end AffineCriterion

/-! ### Restriction of `𝒪(-n-1)[n]` to the projective space over an open -/

section Restrict

variable (n : ℕ) {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]

/-- The morphism `ℙⁿ_V ⟶ ℙⁿ_Y` induced by an open immersion `V ⟶ Y` is an open immersion, being
a base change of it. -/
instance isOpenImmersion_projectiveSpaceOverMap : IsOpenImmersion (projectiveSpaceOverMap n j) :=
  MorphismProperty.of_isPullback (isPullback_projectiveSpaceOverMap n j).flip inferInstance

/-- The restriction of `𝒪(d)` on `ℙⁿ_Y` to `ℙⁿ_V` is `𝒪(d)`. -/
def restrictTwistOverIso (d : ℤ) :
    (Scheme.Modules.restrictFunctor (projectiveSpaceOverMap n j)).obj (twistOver n Y d) ≅
      twistOver n V d :=
  (Scheme.Modules.restrictFunctorIsoPullback _).app _ ≪≫
    Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso n j d

/-- The restriction of `𝒪(-n-1)[n]` on `ℙⁿ_Y` to `ℙⁿ_V` is `𝒪(-n-1)[n]`. -/
def restrictDualizingTwistIso :
    (OpenImmersion.restrictedDerivedRestrict (projectiveSpaceOverMap n j)).obj
        (dualizingTwist n Y) ≅ dualizingTwist n V :=
  ObjectProperty.isoMk _
    (((Scheme.Modules.restrictFunctor (projectiveSpaceOverMap n j)).mapDerivedCategory.commShiftIso
        (n : ℤ)).app _ ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso
        (((Scheme.Modules.restrictFunctor
            (projectiveSpaceOverMap n j)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso (restrictTwistOverIso n j _)))

end Restrict

/-! ### The comparison map over an affine open -/

section Locality

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [AlgebraicGeometry.QuasiCompact j]
  [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace U] [QuasiSeparatedSpace U] [AlgebraicGeometry.QuasiCompact f']
  [QuasiSeparated f']

/-- **Restricting a morphism into `a(N)` along a cartesian square of opens.** Let `f` be proper,
flat and of finite presentation over a quasi-compact quasi-separated `Y`, `j : V ⟶ Y` a
quasi-compact open immersion with base change `j' : U ⟶ X`, and `N ∈ D^+_QCoh(𝒪_Y)`. Let
`c : K ⟶ a(N)` have invertible transpose `R f_* K ⟶ N`. If every morphism `K' ⟶ a'(j^* N)` with
invertible transpose is invertible, for some `K' ≅ (j')^* K`, then `(j')^* c` is invertible.

The map `θ : (j')^* a ⟶ a' j^*` of [Stacks, Tag 0A9L] is invertible at `N`
([Stacks, Tag 0A9P] (1)), and the transpose of `θ ∘ (j')^* c`, preceded by the base change
isomorphism `j^* R f_* ≅ R f'_* (j')^*`, is `j^*` of the transpose of `c`. -/
theorem isIso_restrict_of_isIso_homEquiv_symm (sq : IsPullback j' f' f j)
    (N : quasiCoherentDerivedCategory Y)
    (hN : DerivedCategoryB.IsBoundedBelow N.obj) {K : quasiCoherentDerivedCategory X}
    (c : K ⟶ (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj N)
    (hc : IsIso (((twistedInverseImageAdjunction f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).homEquiv _ _).symm c))
    {K' : quasiCoherentDerivedCategory U}
    (e : K' ≅ (OpenImmersion.restrictedDerivedRestrict j').obj K)
    (crit : ∀ g : K' ⟶ (twistedInverseImage f'
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).obj
          ((OpenImmersion.restrictedDerivedRestrict j).obj N),
      IsIso (((twistedInverseImageAdjunction f'
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).homEquiv _ _).symm g) → IsIso g) :
    IsIso ((OpenImmersion.restrictedDerivedRestrict j').map c) := by
  let hpushj' := isQuasicoherent_homology_derivedPushforward_of_qcqs j'
  let hpushf := isQuasicoherent_homology_derivedPushforward_of_qcqs f
  let hpushf' := isQuasicoherent_homology_derivedPushforward_of_qcqs f'
  let hpushj := isQuasicoherent_homology_derivedPushforward_of_qcqs j
  let hres := OpenImmersion.isQuasicoherent_homology_derivedRestrict j
  let hres' := OpenImmersion.isQuasicoherent_homology_derivedRestrict j'
  let θ := OpenImmersion.twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj
    hres hres' sq
  have hθ : IsIso (θ.app N) := isIso_twistedInverseImageRestrictionMap_app_of_flat j' f' f j sq N hN
  let adjI := OpenImmersion.quasiCoherentDerivedRestrictAdjunction j' hres' hpushj'
  let adjJ := OpenImmersion.quasiCoherentDerivedRestrictAdjunction j hres hpushj
  let adjH := twistedInverseImageAdjunction f hpushf
  let adjF := twistedInverseImageAdjunction f' hpushf'
  let σ := (quasiCoherentDerivedPushforwardSquareIso j' f' f j hpushj' hpushf hpushf' hpushj
    sq.w).hom
  let ξ := twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf hpushf' hpushj sq
  let g := (OpenImmersion.restrictedDerivedRestrict j').map c ≫ θ.app N
  -- the base change map is invertible
  have hu : IsIso ((OpenImmersion.quasiCoherentDerivedRestrict j hres).map
      ((quasiCoherentDerivedPushforward f hpushf).map (adjI.unit.app K))) := by
    have : IsIso ((OpenImmersion.derivedRestrict j).map ((derivedPushforward f).map
        ((ObjectProperty.ι _).map (adjI.unit.app K)))) := by
      rw [map_liftDerivedRestrictPushforwardAdjunction_unit_app j' _ _ hres' hpushj' K]
      exact isIso_derivedRestrict_map_derivedPushforward_map_unit j' f' f j sq K.obj
    exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (ObjectProperty.ι _) this _
  have : IsIso adjJ.counit := isIso_liftDerivedRestrictPushforwardAdjunction_counit j _ _ _ _
  have hĝ : IsIso ((adjF.homEquiv _ _).symm g) := by
    let β := (OpenImmersion.quasiCoherentDerivedRestrict j hres).map
        ((quasiCoherentDerivedPushforward f hpushf).map (adjI.unit.app K)) ≫
      (OpenImmersion.quasiCoherentDerivedRestrict j hres).map (σ.app
        ((OpenImmersion.quasiCoherentDerivedRestrict j' hres').obj K)) ≫
      adjJ.counit.app ((quasiCoherentDerivedPushforward f' hpushf').obj
        ((OpenImmersion.quasiCoherentDerivedRestrict j' hres').obj K))
    -- the transpose of `g`, preceded by the base change map, is the restricted transpose of `c`
    have hβ : β ≫ (adjF.homEquiv _ _).symm g =
        (OpenImmersion.quasiCoherentDerivedRestrict j hres).map ((adjH.homEquiv _ _).symm c) := by
      simpa only [β, Category.assoc] using
        baseChange_comp_homEquiv_symm_restrictionMap adjI adjJ adjH adjF σ ξ
          (fun N => mateEquiv_counit _ _ _ N) N (θ.app N)
          (by simp [θ, adjI, adjJ, ξ, OpenImmersion.twistedInverseImageRestrictionMap]) c
    have : IsIso (β ≫ (adjF.homEquiv _ _).symm g) := by
      rw [hβ]
      infer_instance
    exact IsIso.of_isIso_comp_left β _
  have : IsIso (e.hom ≫ g) := crit _ (by
    rw [Adjunction.homEquiv_naturality_left_symm]
    infer_instance)
  have := IsIso.of_isIso_comp_left e.hom g
  exact IsIso.of_isIso_comp_right _ (θ.app N)

end Locality

section Local

variable (n : ℕ) {V Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] (j : V ⟶ Y)
  [IsOpenImmersion j] [IsAffine V]

/-- **The comparison map restricted to `ℙⁿ_V`, `V ⊆ Y` an affine open, is invertible**, by
`isIso_restrict_of_isIso_homEquiv_symm` and the affine case. -/
theorem isIso_restrict_qcqsDualizingTwistComparison :
    IsIso ((OpenImmersion.restrictedDerivedRestrict (projectiveSpaceOverMap n j)).map
      (qcqsDualizingTwistComparison n Y)) :=
  isIso_restrict_of_isIso_homEquiv_symm (projectiveSpaceOverMap n j)
    (projectiveSpaceOver n V ↘ V) (projectiveSpaceOver n Y ↘ Y) j
    (isPullback_projectiveSpaceOverMap n j) _
    (KoszulRegular.isBoundedBelow_singleFunctor_obj _) _
    (by
      rw [qcqsDualizingTwistComparison, Equiv.symm_apply_apply]
      infer_instance)
    (restrictDualizingTwistIso n j).symm
    (isIso_of_isIso_homEquiv_symm n V)

end Local

/-! ### Tag 0A9W for projective space over a quasi-compact quasi-separated base -/

section Main

variable (n : ℕ) (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **The comparison map `c : 𝒪(-n-1)[n] ⟶ a(𝒪_Y)` is an isomorphism**, for `Y` quasi-compact and
quasi-separated and `n ≥ 0`: whether a morphism of `D(𝒪_{ℙⁿ_Y})` is invertible is local, the
projective spaces `ℙⁿ_V` over the affine opens `V ⊆ Y` cover `ℙⁿ_Y`, and over each of them the
restriction of `c` is invertible. -/
instance isIso_qcqsDualizingTwistComparison : IsIso (qcqsDualizingTwistComparison n Y) := by
  let P := DerivedCategoryB.derivedCategoryB (A := (projectiveSpaceOver n Y).Modules)
    (SheafOfModules.isQuasicoherent (projectiveSpaceOver n Y).ringCatSheaf)
  suffices h : IsIso (qcqsDualizingTwistComparison n Y).hom by
    have : IsIso ((ObjectProperty.ι P).map (qcqsDualizingTwistComparison n Y)) := h
    exact (ObjectProperty.fullyFaithfulι P).isIso_of_isIso_map _
  refine QcqsGeneration.isIso_of_isIso_derivedRestrict _
    (fun V : Y.affineOpens => projectiveSpaceOverMap n (V : Y.Opens).ι) (fun x => ?_)
    (fun V => ?_)
  · obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := (projectiveSpaceOver n Y ↘ Y) x) (U := ⊤) trivial
    have sq : IsPullback (projectiveSpaceOverMap n V.ι) (projectiveSpaceOver n V ↘ V)
        (projectiveSpaceOver n Y ↘ Y) V.ι := isPullback_projectiveSpaceOverMap n V.ι
    obtain ⟨w, rfl⟩ : x ∈ Set.range (pullback.fst (projectiveSpaceOver n Y ↘ Y) V.ι) := by
      rwa [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    refine ⟨⟨V, hV⟩, sq.isoPullback.inv w, ?_⟩
    rw [← sq.isoPullback_inv_fst, Scheme.Hom.comp_apply]
  · have : IsAffine (V : Y.Opens) := V.2
    have := isIso_restrict_qcqsDualizingTwistComparison n (V : Y.Opens).ι (Y := Y)
    exact Functor.map_isIso (ObjectProperty.ι _)
      ((OpenImmersion.restrictedDerivedRestrict _).map (qcqsDualizingTwistComparison n Y))

/-- **[Stacks, Tag 0A9W] for `ℰ = 𝒪_Y^{⊕ n+1}`.** Let `Y` be a quasi-compact and quasi-separated
scheme, `n ≥ 0`, `f : ℙⁿ_Y ⟶ Y` the structure morphism and `a` the right adjoint of
`R f_* : D_QCoh(𝒪_{ℙⁿ_Y}) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. Then `a(𝒪_Y) ≅ 𝒪(-n-1)[n]`. -/
theorem nonempty_twistedInverseImage_derivedStructureSheaf_iso_of_qcqs :
    Nonempty ((twistedInverseImage (projectiveSpaceOver n Y ↘ Y)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (projectiveSpaceOver n Y ↘ Y))).obj
        (DerivedPushforward.derivedStructureSheaf Y) ≅ dualizingTwist n Y) :=
  ⟨(asIso (qcqsDualizingTwistComparison n Y)).symm⟩

end Main

end Stacks.Duality.ProjectiveSpace

end
