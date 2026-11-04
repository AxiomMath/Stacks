module

public import StacksFrontier.AlgebraicGeometry.Scheme.AutomorphismFunctorSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineMobius
public import StacksFrontier.AlgebraicGeometry.Scheme.ProjectiveGeneralLinearTwo

/-!
# The automorphism functor of the projective line is `PGL₂`

Let `k` be a commutative ring and `ℙ¹_k` the projective line over `k`. Its automorphism functor
`T ↦ Aut_T(ℙ¹_T)` on `k`-schemes (`AlgebraicGeometry.Scheme.autFunctor`) is represented by the
scheme `PGL₂ = Spec k[e_{p q}]` of `AlgebraicGeometry.projectiveGeneralLinearTwoScheme`, and the
universal automorphism is the Möbius map of the universal matrix: the composite
`GL₂(T) ⟶ PGL₂(T) ≅ Aut_T(ℙ¹_T)` sends an invertible matrix `M` to `μ_M`.

## The argument

* Over an affine `k`-scheme `T = Spec A`, the base change `ℙ¹_T` is the projective line over `A`
  (`AlgebraicGeometry.projectiveLineBaseChangeIso`), so an invertible matrix `M` over `A` gives an
  element `AlgebraicGeometry.mobiusAutFunctor` of `Aut_T(ℙ¹_T)`, natural in `A`.
* On the chart `D(g_p)` of `PGL₂` the chart matrix `N^p` gives such an element; on overlaps the
  chart matrices are proportional, so these glue to the universal element
  `AlgebraicGeometry.projectiveLineUniversalAut` over `PGL₂`
  (`AlgebraicGeometry.Scheme.exists_autFunctor_map_eq_of_openCover`). Its pull-back along the
  morphism `Spec A ⟶ PGL₂` given by `ev_M` is the Möbius map of `M`.
* **Injectivity.** Two morphisms `T ⟶ PGL₂` are, on a fine enough affine cover of `T`, of the form
  `ev_M` and `ev_N`; if they pull the universal element back to the same automorphism then
  `μ_M = μ_N`, so `N` is a scalar multiple of `M` and `ev_M = ev_N`.
* **Surjectivity.** An automorphism `ψ` of `ℙ¹_T` sends the section `∞` into one of the two charts
  locally on `T`; on such an affine piece `ψ` is a Möbius map
  (`AlgebraicGeometry.exists_eq_projectiveLineMobius`), and the morphisms `ev_M` of the pieces
  agree on overlaps by injectivity, so they glue.

## Main definitions

* `AlgebraicGeometry.projectiveLineOver`: `ℙ¹_k` as a `k`-scheme.
* `AlgebraicGeometry.mobiusAutFunctor`: the Möbius automorphism of `ℙ¹_T` for `T = Spec A`.
* `AlgebraicGeometry.projectiveLineUniversalAut`: the universal automorphism over `PGL₂`.
* `AlgebraicGeometry.evaluationOver`: the morphism `Spec A ⟶ PGL₂` of an invertible matrix.
* `AlgebraicGeometry.projectiveLineAutFunctorRepresentableBy`: **`PGL₂` represents the
  automorphism functor of `ℙ¹_k`.**

## Main results

* `AlgebraicGeometry.autFunctor_map_mobiusAutFunctor`: naturality of Möbius automorphisms.
* `AlgebraicGeometry.exists_eq_mobiusAutFunctor_of_range`: an automorphism of `ℙ¹_{Spec A}`
  sending `∞` into a chart is a Möbius automorphism.
* `AlgebraicGeometry.autFunctor_map_evaluationOver_universalAut`: the universal automorphism
  pulls back along `ev_M` to `μ_M`.
* `AlgebraicGeometry.eq_of_autFunctor_map_universalAut_eq` and
  `AlgebraicGeometry.exists_autFunctor_map_universalAut_eq`: injectivity and surjectivity.
* `AlgebraicGeometry.projectiveLineAutFunctorRepresentableBy_homEquiv_quotient`: the quotient
  morphism `GL₂ ⟶ PGL₂` corresponds to the Möbius automorphism of the universal matrix.

## References

* [Stacks Project, Tag 0DSV](https://stacks.math.columbia.edu/tag/0DSV)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Polynomial

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- The projective line over `k`, as a `k`-scheme. -/
abbrev projectiveLineOver : Over (Spec (.of k)) := Over.mk (projectiveLine k ↘ Spec (.of k))

/-- The projective line over `A`, as an `A`-scheme. -/
abbrev projectiveLineOverRing (A : Type u) [CommRing A] : Over (Spec (.of A)) :=
  Over.mk (projectiveLine A ↘ Spec (.of A))

/-! ### Base change of morphisms of projective lines -/

variable {k}

/-- Base change of projective lines is functorial. -/
theorem projectiveLineMap_comp_projectiveLineMap {S T : Type u} [CommRing S] [CommRing T]
    (g : k →+* S) (f : S →+* T) :
    projectiveLineMap f ≫ projectiveLineMap g = projectiveLineMap (f.comp g) := by
  refine projectiveLine_hom_ext_point ?_ ?_ <;>
  · rw [projectiveLineHomogeneousPoint_comp_projectiveLineMap_assoc,
      projectiveLineHomogeneousPoint_comp_projectiveLineMap,
      projectiveLineHomogeneousPoint_comp_projectiveLineMap]
    rfl

/-- The section `∞` is compatible with base change. -/
theorem projectiveLineInfinitySection_comp_projectiveLineMap {A : Type u} [CommRing A]
    (σ : k →+* A) :
    projectiveLineInfinitySection A ≫ projectiveLineMap σ =
      Spec.map (CommRingCat.ofHom σ) ≫ projectiveLineInfinitySection k := by
  rw [projectiveLineInfinitySection_eq_projectiveLineHomogeneousPoint,
    projectiveLineInfinitySection_eq_projectiveLineHomogeneousPoint,
        projectiveLineHomogeneousPoint_comp_projectiveLineMap,
    Spec_map_comp_projectiveLineHomogeneousPoint]
  exact projectiveLineHomogeneousPoint_congr _ _ _ (by simp) (by simp)

/-! ### Affine bases -/

section Transport

variable {A : Type u} [CommRing A] (h : Spec (.of A) ⟶ Spec (.of k))

/-- The ring map `k ⟶ A` underlying a morphism `Spec A ⟶ Spec k`. -/
abbrev ringHomOfSpec : k →+* A := (Spec.preimage h).hom

/-- The spectrum of `ringHomOfSpec h` is `h`. -/
theorem Spec_map_ringHomOfSpec : Spec.map (CommRingCat.ofHom (ringHomOfSpec h)) = h := by
  rw [ringHomOfSpec, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- `ringHomOfSpec` of `Spec φ ≫ h` is `φ` composed with `ringHomOfSpec h`. -/
theorem ringHomOfSpec_comp {B : Type u} [CommRing B] (φ : A →+* B) :
    ringHomOfSpec (Spec.map (CommRingCat.ofHom φ) ≫ h) = φ.comp (ringHomOfSpec h) := by
  rw [ringHomOfSpec, Spec.preimage_comp, Spec.preimage_map]
  rfl

/-- **`ℙ¹_A` is the base change of `ℙ¹_k` along `Spec A ⟶ Spec k`.** -/
theorem isPullback_projectiveLineMap_spec :
    IsPullback (projectiveLineMap (ringHomOfSpec h)) (projectiveLine A ↘ Spec (.of A))
      (projectiveLine k ↘ Spec (.of k)) h := by
  have := isPullback_projectiveLineMap (ringHomOfSpec h)
  rwa [Spec_map_ringHomOfSpec] at this

/-- The same pullback square, with the corners written as structure morphisms of `S`-schemes. -/
theorem isPullback_projectiveLineMap_over :
    IsPullback (projectiveLineMap (ringHomOfSpec h)) (projectiveLine A ↘ Spec (.of A))
      (projectiveLineOver k).hom (Over.mk h).hom :=
  isPullback_projectiveLineMap_spec h

/-- The comparison `ℙ¹_A ⟶ ℙ¹_k ×_k Spec A`. -/
abbrev projectiveLineBaseChangeHom :
    projectiveLine A ⟶ pullback (projectiveLineOver k).hom (Over.mk h).hom :=
  (isPullback_projectiveLineMap_over h).isoPullback.hom

/-- The comparison of `ℙ¹_A` with the base change of `ℙ¹_k`, as `A`-schemes. -/
def projectiveLineBaseChangeIso :
    projectiveLineOverRing A ≅ (Over.pullback (Over.mk h).hom).obj (projectiveLineOver k) :=
  Over.isoMk (isPullback_projectiveLineMap_over h).isoPullback (by simp)

/-- The underlying morphism of `projectiveLineBaseChangeIso h` is
`projectiveLineBaseChangeHom h`. -/
theorem projectiveLineBaseChangeIso_hom_left :
    (projectiveLineBaseChangeIso h).hom.left = projectiveLineBaseChangeHom h :=
  rfl

/-- The underlying morphism of the inverse of `projectiveLineBaseChangeIso h` is the inverse of
the pullback comparison isomorphism. -/
theorem projectiveLineBaseChangeIso_inv_left :
    (projectiveLineBaseChangeIso h).inv.left =
        (isPullback_projectiveLineMap_over h).isoPullback.inv :=
  rfl

/-- The Möbius automorphism `μ_M` of `ℙ¹_A`, as an automorphism of `A`-schemes. -/
def projectiveLineMobiusOver (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    Aut (projectiveLineOverRing A) :=
  Over.isoMk (projectiveLineMobiusIso hM) (projectiveLineMobius_comp_structureMorphism hM)

/-- **The Möbius automorphism of `ℙ¹_T` for `T = Spec A`**, as an element of the automorphism
functor of `ℙ¹_k`. -/
def mobiusAutFunctor (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    (Scheme.autFunctor (projectiveLineOver k)).obj (op (Over.mk h)) :=
  (projectiveLineBaseChangeIso h).conjAut (projectiveLineMobiusOver M hM)

/-- The underlying morphism of `mobiusAutFunctor h M hM` is `μ_M` conjugated by the comparison of
`ℙ¹_A` with the base change of `ℙ¹_k`. -/
theorem mobiusAutFunctor_hom_left (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    (mobiusAutFunctor h M hM).hom.left =
      (isPullback_projectiveLineMap_over h).isoPullback.inv ≫ projectiveLineMobius hM ≫
        projectiveLineBaseChangeHom h :=
  rfl

/-- The underlying morphism of `mobiusAutFunctor h M hM` followed by the projection to `ℙ¹_k` is
`μ_M` followed by the base change map `ℙ¹_A ⟶ ℙ¹_k`. -/
theorem mobiusAutFunctor_hom_left_fst (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    (mobiusAutFunctor h M hM).hom.left ≫ pullback.fst _ _ =
      (isPullback_projectiveLineMap_over h).isoPullback.inv ≫ projectiveLineMobius hM ≫
        projectiveLineMap (ringHomOfSpec h) := by
  rw [mobiusAutFunctor_hom_left, Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst]

/-- **Naturality of Möbius automorphisms**: the base change of `μ_M` along `Spec B ⟶ Spec A` is
`μ` of the image of `M`. -/
theorem autFunctor_map_mobiusAutFunctor {B : Type u} [CommRing B] (h' : Spec (.of B) ⟶ Spec (.of k))
    (q : Over.mk h' ⟶ Over.mk h) (φ : A →+* B) (hq : q.left = Spec.map (CommRingCat.ofHom φ))
    (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) (hφM : IsUnit (M.map φ).det) :
    (Scheme.autFunctor (projectiveLineOver k)).map q.op (mobiusAutFunctor h M hM) =
      mobiusAutFunctor h' (M.map φ) hφM := by
  have hh' : h' = Spec.map (CommRingCat.ofHom φ) ≫ h := by
    rw [← hq]
    exact (Over.w q).symm
  have hσ : ringHomOfSpec h' = φ.comp (ringHomOfSpec h) := by
    have := ringHomOfSpec_comp h φ
    rwa [← hh'] at this
  apply Iso.ext
  apply Scheme.endo_ext
  show (Scheme.endBaseChange _ q (mobiusAutFunctor h M hM).hom).left ≫ pullback.fst _ _ =
    (mobiusAutFunctor h' _ hφM).hom.left ≫ pullback.fst _ _
  rw [Scheme.endBaseChange_left_fst, mobiusAutFunctor_hom_left_fst, mobiusAutFunctor_hom_left_fst]
  have L1 : projectiveLineBaseChangeHom h' ≫ Scheme.baseChangeMap _ q =
      projectiveLineMap φ ≫ projectiveLineBaseChangeHom h := by
    apply pullback.hom_ext
    · rw [Category.assoc, Scheme.baseChangeMap_fst, IsPullback.isoPullback_hom_fst, Category.assoc,
        IsPullback.isoPullback_hom_fst, projectiveLineMap_comp_projectiveLineMap, hσ]
    · rw [Category.assoc, Scheme.baseChangeMap_snd, ← Category.assoc,
        IsPullback.isoPullback_hom_snd, Category.assoc, IsPullback.isoPullback_hom_snd,
        projectiveLineMap_comp_structureMorphism, hq]
  rw [← cancel_epi (projectiveLineBaseChangeHom h'), Iso.hom_inv_id_assoc, reassoc_of% L1,
    Iso.hom_inv_id_assoc, ← Category.assoc, projectiveLineMap_comp_projectiveLineMobius _ _ hφM,
    Category.assoc, projectiveLineMap_comp_projectiveLineMap, hσ]

/-- **Scalar multiples of a matrix give the same automorphism.** -/
theorem mobiusAutFunctor_smul (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) {w : A}
    (hw : IsUnit w) (hwM : IsUnit (w • M).det) :
    mobiusAutFunctor h (w • M) hwM = mobiusAutFunctor h M hM := by
  apply Iso.ext
  apply Over.OverMorphism.ext
  rw [mobiusAutFunctor_hom_left, mobiusAutFunctor_hom_left, projectiveLineMobius_smul hM hw hwM]

/-- **Möbius automorphisms determine the matrix up to a scalar.** -/
theorem exists_eq_smul_of_mobiusAutFunctor_eq {M N : Matrix (Fin 2) (Fin 2) A} (hM : IsUnit M.det)
    (hN : IsUnit N.det) (e : mobiusAutFunctor h M hM = mobiusAutFunctor h N hN) :
    ∃ w : A, IsUnit w ∧ N = w • M := by
  have e' := congrArg (fun ψ : (Scheme.autFunctor (projectiveLineOver k)).obj (op (Over.mk h)) ↦
    (isPullback_projectiveLineMap_over h).isoPullback.hom ≫ ψ.hom.left ≫
      (isPullback_projectiveLineMap_over h).isoPullback.inv) e
  simp only [mobiusAutFunctor_hom_left, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc] at e'
  exact (projectiveLineMobius_eq_iff hM hN).1 e'

/-- The automorphism of `ℙ¹_A` over `A` corresponding to an element of the automorphism functor
at `Spec A`. -/
def autFunctorToProjectiveLineAut
    (ψ : Aut ((Over.pullback (Over.mk h).hom).obj (projectiveLineOver k))) :
    Aut (projectiveLineOverRing A) :=
  (projectiveLineBaseChangeIso h).symm.conjAut ψ

/-- Conjugating `autFunctorToProjectiveLineAut h ψ` back by `projectiveLineBaseChangeIso h`
recovers `ψ`. -/
theorem conjAut_autFunctorToProjectiveLineAut
    (ψ : Aut ((Over.pullback (Over.mk h).hom).obj (projectiveLineOver k))) :
    (projectiveLineBaseChangeIso h).conjAut (autFunctorToProjectiveLineAut h ψ) = ψ := by
  apply Iso.ext
  rw [Iso.conjAut_hom, autFunctorToProjectiveLineAut, Iso.conjAut_hom, Iso.self_symm_conj]

/-- The underlying automorphism of `ℙ¹_A`. -/
abbrev autFunctorToProjectiveLineIso
    (ψ : Aut ((Over.pullback (Over.mk h).hom).obj (projectiveLineOver k))) :
    projectiveLine A ≅ projectiveLine A :=
  (Over.forget _).mapIso (autFunctorToProjectiveLineAut h ψ)

/-- The underlying morphism of `autFunctorToProjectiveLineIso h ψ` is `ψ` conjugated by the
comparison of `ℙ¹_A` with the base change of `ℙ¹_k`. -/
theorem autFunctorToProjectiveLineIso_hom
    (ψ : Aut ((Over.pullback (Over.mk h).hom).obj (projectiveLineOver k))) :
    (autFunctorToProjectiveLineIso h ψ).hom =
      projectiveLineBaseChangeHom h ≫ ψ.hom.left ≫
        (isPullback_projectiveLineMap_over h).isoPullback.inv :=
  rfl

/-- **An element of the automorphism functor over `Spec A` sending `∞` to a point `[a : c]` with
`a, c ∈ A` is a Möbius automorphism.** -/
theorem exists_eq_mobiusAutFunctor
    (ψ : Aut ((Over.pullback (Over.mk h).hom).obj (projectiveLineOver k))) {a c : A}
    (hac : IsCoprime a c)
    (hinf : projectiveLineInfinitySection A ≫ (autFunctorToProjectiveLineIso h ψ).hom =
      projectiveLineHomogeneousPoint (RingHom.id A) a c hac) :
    ∃ (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det), ψ = mobiusAutFunctor h M hM := by
  obtain ⟨M, hM, hχ⟩ := exists_eq_projectiveLineMobius (autFunctorToProjectiveLineIso h ψ)
    (Over.w (autFunctorToProjectiveLineAut h ψ).hom) hac hinf
  refine ⟨M, hM, ?_⟩
  rw [← conjAut_autFunctorToProjectiveLineAut h ψ, mobiusAutFunctor]
  congr 1
  exact Iso.ext (Over.OverMorphism.ext hχ)

end Transport

/-! ### The section `∞` -/

section Infinity

/-- The section `∞` of the base change of `ℙ¹_k` to a `k`-scheme `T`. -/
def projectiveLineInfinityOver (T : Over (Spec (.of k))) :
    T.left ⟶ pullback (projectiveLineOver k).hom T.hom :=
  pullback.lift (T.hom ≫ projectiveLineInfinitySection k) (𝟙 _) (by
    rw [Category.assoc, show projectiveLineInfinitySection k ≫ (projectiveLineOver k).hom = 𝟙 _ from
      projectiveLineInfinitySection_comp_structureMorphism k, Category.comp_id, Category.id_comp])

/-- The section `∞` of the base change, followed by the projection to `ℙ¹_k`, is the structure
morphism of `T` followed by the section `∞` of `ℙ¹_k`. -/
@[reassoc (attr := simp)]
theorem projectiveLineInfinityOver_fst (T : Over (Spec (.of k))) :
    projectiveLineInfinityOver T ≫ pullback.fst _ _ = T.hom ≫ projectiveLineInfinitySection k :=
  pullback.lift_fst _ _ _

/-- The section `∞` of the base change is a section of the projection to `T`. -/
@[reassoc (attr := simp)]
theorem projectiveLineInfinityOver_snd (T : Over (Spec (.of k))) :
    projectiveLineInfinityOver T ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The section `∞` is compatible with the base change map along a morphism `T' ⟶ T` of
`k`-schemes. -/
@[reassoc]
theorem projectiveLineInfinityOver_comp_baseChangeMap {T T' : Over (Spec (.of k))} (q : T' ⟶ T) :
    projectiveLineInfinityOver T' ≫ Scheme.baseChangeMap _ q =
      q.left ≫ projectiveLineInfinityOver T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Scheme.baseChangeMap_fst, projectiveLineInfinityOver_fst]
    rw [← Over.w q, Category.assoc]
  · simp only [Category.assoc, Scheme.baseChangeMap_snd, projectiveLineInfinityOver_snd_assoc,
      projectiveLineInfinityOver_snd, Category.comp_id]

variable {A : Type u} [CommRing A] (h : Spec (.of A) ⟶ Spec (.of k))

/-- The comparison `ℙ¹_A ⟶ ℙ¹_k ×_k Spec A` sends the section `∞` of `ℙ¹_A` to the section `∞`
of the base change. -/
theorem projectiveLineInfinitySection_comp_baseChangeHom :
    projectiveLineInfinitySection A ≫ projectiveLineBaseChangeHom h =
      projectiveLineInfinityOver (Over.mk h) := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, projectiveLineInfinityOver_fst,
      projectiveLineInfinitySection_comp_projectiveLineMap, Spec_map_ringHomOfSpec]
    rfl
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, projectiveLineInfinityOver_snd,
      projectiveLineInfinitySection_comp_structureMorphism]
    rfl

/-- `projectiveLineInfinitySection_comp_baseChangeHom`, followed by a morphism `f`. -/
theorem projectiveLineInfinitySection_comp_baseChangeHom_comp {Z : Scheme.{u}}
    (f : pullback (projectiveLineOver k).hom (Over.mk h).hom ⟶ Z) :
    projectiveLineInfinitySection A ≫ projectiveLineBaseChangeHom h ≫ f =
      projectiveLineInfinityOver (Over.mk h) ≫ f := by
  rw [← Category.assoc, projectiveLineInfinitySection_comp_baseChangeHom]

/-- **Where a restricted endomorphism sends `∞`**: for `q : Spec A ⟶ T` over `k` and `φ` an
endomorphism of `ℙ¹_T` over `T`, the image of `∞` under the restriction of `φ` to `Spec A`, read
in `ℙ¹_k`, is the restriction of the image of `∞` under `φ`. -/
theorem projectiveLineInfinitySection_comp_endBaseChange
    {T : Over (Spec (.of k))} (q : Over.mk h ⟶ T)
    (φ : (Over.pullback T.hom).obj (projectiveLineOver k) ⟶
      (Over.pullback T.hom).obj (projectiveLineOver k)) :
    projectiveLineInfinitySection A ≫ projectiveLineBaseChangeHom h ≫
        (Scheme.endBaseChange _ q φ).left ≫ (isPullback_projectiveLineMap_over h).isoPullback.inv ≫
          projectiveLineMap (ringHomOfSpec h) =
      q.left ≫ projectiveLineInfinityOver T ≫ φ.left ≫ pullback.fst _ _ := by
  rw [(isPullback_projectiveLineMap_over h).isoPullback_inv_fst,
    projectiveLineInfinitySection_comp_baseChangeHom_comp, Scheme.endBaseChange_left_fst,
    projectiveLineInfinityOver_comp_baseChangeMap_assoc]

/-- A section of `ℙ¹_A` over `A` landing in the range of an affine-line chart `χ` is the
composite of `χ` with `Spec` of an evaluation map `A[X] → A`. -/
private theorem exists_eq_spec_map_eval₂RingHom_comp_of_range_subset
    (χ : Spec (.of A[X]) ⟶ projectiveLine A) [IsOpenImmersion χ]
    (hχ : χ ≫ (projectiveLine A ↘ Spec (.of A)) = projectiveLineAffineStructureMorphism A)
    (s : Spec (.of A) ⟶ projectiveLine A) (hs : s ≫ (projectiveLine A ↘ Spec (.of A)) = 𝟙 _)
    (hr : Set.range s.base ⊆ Set.range χ.base) :
    ∃ t : A, s = Spec.map (CommRingCat.ofHom (eval₂RingHom (RingHom.id A) t)) ≫ χ := by
  set l := IsOpenImmersion.lift χ s hr
  have hl : l ≫ χ = s := IsOpenImmersion.lift_fac _ _ _
  have hρC : CommRingCat.ofHom (C : A →+* A[X]) ≫ Spec.preimage l = 𝟙 _ := by
    rw [← Spec.map_eq_id, Spec.map_comp, Spec.map_preimage]
    change l ≫ projectiveLineAffineStructureMorphism A = _
    rw [← hχ, reassoc_of% hl, hs]
  set t := (Spec.preimage l).hom X
  refine ⟨t, ?_⟩
  have hρ : Spec.preimage l = CommRingCat.ofHom (eval₂RingHom (RingHom.id A) t) := by
    ext1
    refine Polynomial.ringHom_ext (fun a ↦ ?_) (by simp [t])
    simpa using congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of A ↦ φ.hom a) hρC
  rw [← hρ, Spec.map_preimage, hl]

/-- A section of `ℙ¹_A` over `A` landing in the first chart is a point `[t : 1]`. -/
theorem exists_eq_projectiveLineHomogeneousPoint_of_range_subset_XChart
    (s : Spec (.of A) ⟶ projectiveLine A)
    (hs : s ≫ (projectiveLine A ↘ Spec (.of A)) = 𝟙 _)
    (hr : Set.range s.base ⊆ Set.range (projectiveLineXChart A).base) :
    ∃ t : A, s = projectiveLineHomogeneousPoint (RingHom.id A) t 1 isCoprime_one_right := by
  obtain ⟨t, ht⟩ := exists_eq_spec_map_eval₂RingHom_comp_of_range_subset _
    (projectiveLineXChart_comp_structureMorphism A) s hs hr
  refine ⟨t, ht.trans ?_⟩
  rw [← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
    Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_right (u := t) (v := 1) _
      (RingHom.id _) isUnit_one t (by simp), RingHom.comp_id]

/-- A section of `ℙ¹_A` over `A` landing in the second chart is a point `[1 : t]`. -/
theorem exists_eq_projectiveLineHomogeneousPoint_of_range_subset_YChart
    (s : Spec (.of A) ⟶ projectiveLine A)
    (hs : s ≫ (projectiveLine A ↘ Spec (.of A)) = 𝟙 _)
    (hr : Set.range s.base ⊆ Set.range (projectiveLineYChart A).base) :
    ∃ t : A, s = projectiveLineHomogeneousPoint (RingHom.id A) 1 t isCoprime_one_left := by
  obtain ⟨t, ht⟩ := exists_eq_spec_map_eval₂RingHom_comp_of_range_subset _
    (projectiveLineYChart_comp_structureMorphism A) s hs hr
  refine ⟨t, ht.trans ?_⟩
  rw [← Spec_map_id_comp (projectiveLineHomogeneousPoint _ _ _ _),
    Spec_map_comp_projectiveLineHomogeneousPoint_of_isUnit_left (u := 1) (v := t) _
      (RingHom.id _) isUnit_one t (by simp), RingHom.comp_id]

/-- **An automorphism of `ℙ¹_{Spec A}` sending `∞` into one of the two charts of `ℙ¹_k` is a
Möbius automorphism.** -/
theorem exists_eq_mobiusAutFunctor_of_range
    (ψ : Aut ((Over.pullback (Over.mk h).hom).obj (projectiveLineOver k)))
    (hr : Set.range (projectiveLineInfinitySection A ≫ projectiveLineBaseChangeHom h ≫
        ψ.hom.left ≫ (isPullback_projectiveLineMap_over h).isoPullback.inv ≫
          projectiveLineMap (ringHomOfSpec h)).base ⊆ Set.range (projectiveLineXChart k).base ∨
      Set.range (projectiveLineInfinitySection A ≫ projectiveLineBaseChangeHom h ≫
        ψ.hom.left ≫ (isPullback_projectiveLineMap_over h).isoPullback.inv ≫
          projectiveLineMap (ringHomOfSpec h)).base ⊆ Set.range (projectiveLineYChart k).base) :
    ∃ (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det), ψ = mobiusAutFunctor h M hM := by
  set s := projectiveLineInfinitySection A ≫ (autFunctorToProjectiveLineIso h ψ).hom
  have hs : s ≫ (projectiveLine A ↘ Spec (.of A)) = 𝟙 _ := by
    rw [Category.assoc, show (autFunctorToProjectiveLineIso h ψ).hom ≫
      (projectiveLine A ↘ Spec (.of A)) = _ from Over.w (autFunctorToProjectiveLineAut h ψ).hom]
    exact projectiveLineInfinitySection_comp_structureMorphism _
  have hX := preimage_range_projectiveLineXChart (ringHomOfSpec h) X X
    toLaurent_X_mul_overlapInverseCoordinate_X (dvd_refl X)
  have hY := preimage_range_projectiveLineYChart (ringHomOfSpec h) X X
    toLaurent_X_mul_overlapInverseCoordinate_X (dvd_refl X)
  change (projectiveLineMap (ringHomOfSpec h)).base ⁻¹' _ = _ at hX hY
  rcases hr with hr | hr
  · obtain ⟨t, ht⟩ := exists_eq_projectiveLineHomogeneousPoint_of_range_subset_XChart s hs (by
      rintro _ ⟨x, rfl⟩
      rw [← hX]
      exact hr ⟨x, rfl⟩)
    exact exists_eq_mobiusAutFunctor h ψ isCoprime_one_right ht
  · obtain ⟨t, ht⟩ := exists_eq_projectiveLineHomogeneousPoint_of_range_subset_YChart s hs (by
      rintro _ ⟨x, rfl⟩
      rw [← hY]
      exact hr ⟨x, rfl⟩)
    exact exists_eq_mobiusAutFunctor h ψ isCoprime_one_left ht

end Infinity


/-! ### The universal automorphism over `PGL₂` -/

section Universal

/-- `ringHomOfSpec` of `Spec σ` is `σ`. -/
theorem ringHomOfSpec_Spec_map {A : Type u} [CommRing A] (σ : k →+* A) :
    ringHomOfSpec (Spec.map (CommRingCat.ofHom σ)) = σ := by
  rw [ringHomOfSpec, Spec.preimage_map]
  rfl

variable (k)

/-- The cover of `PGL₂` by the charts `D(g_p)`. -/
abbrev projectiveGeneralLinearTwoCover : (projectiveGeneralLinearTwoScheme k).left.OpenCover where
  I₀ := Fin 2 × Fin 2
  X p := Spec (.of (projectiveGeneralLinearTwoChartRing k p))
  f _ := Spec.map (CommRingCat.ofHom (algebraMap _ _))
  mem₀ := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of (projectiveGeneralLinearTwoRing k))
    (projectiveGeneralLinearTwoChartElement k)
    (span_projectiveGeneralLinearTwoChartElement_eq_top k)).openCover.mem₀

/-- The structure morphism of the chart `D(g_p)` to `Spec k`. -/
abbrev projectiveGeneralLinearTwoChartHom (p : Fin 2 × Fin 2) :
    Spec (.of (projectiveGeneralLinearTwoChartRing k p)) ⟶ Spec (.of k) :=
  (projectiveGeneralLinearTwoCover k).f p ≫ (projectiveGeneralLinearTwoScheme k).hom

/-- The ring map underlying the structure morphism of the chart `D(g_p)` is
`projectiveGeneralLinearTwoChartStructure k p`. -/
theorem ringHomOfSpec_projectiveGeneralLinearTwoChartHom (p : Fin 2 × Fin 2) :
    ringHomOfSpec (projectiveGeneralLinearTwoChartHom k p) =
      projectiveGeneralLinearTwoChartStructure k p := by
  rw [projectiveGeneralLinearTwoChartHom]
  show ringHomOfSpec (Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (projectiveGeneralLinearTwoRing k)))) = _
  rw [ringHomOfSpec_comp, ringHomOfSpec_Spec_map]

/-- The Möbius automorphism of the chart matrix over the chart `D(g_p)`. -/
abbrev projectiveLineChartAut (p : Fin 2 × Fin 2) :
    (Scheme.autFunctor (projectiveLineOver k)).obj
      (op (Scheme.coverOverObj (projectiveGeneralLinearTwoCover k) p)) :=
  mobiusAutFunctor (projectiveGeneralLinearTwoChartHom k p)
    (projectiveGeneralLinearTwoChartMatrix k p)
        (isUnit_projectiveGeneralLinearTwoChartMatrix_det k p)

variable {k}

/-- A matrix with unit determinant keeps a unit determinant under a ring map. -/
private theorem isUnit_det_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {M : Matrix (Fin 2) (Fin 2) A} (hM : IsUnit M.det) : IsUnit (M.map φ).det := by
  rw [show (M.map φ).det = φ M.det from (RingHom.map_det _ _).symm]
  exact hM.map _

/-- If two composites of spectra of ring maps agree, so do the composites of the ring maps. -/
private theorem comp_eq_of_spec_map_comp_eq {R S₁ S₂ T : Type u} [CommRing R] [CommRing S₁]
    [CommRing S₂] [CommRing T] {α : R →+* S₁} {β : R →+* S₂} {φ₁ : S₁ →+* T} {φ₂ : S₂ →+* T}
    (hw : Spec.map (CommRingCat.ofHom φ₁) ≫ Spec.map (CommRingCat.ofHom α) =
      Spec.map (CommRingCat.ofHom φ₂) ≫ Spec.map (CommRingCat.ofHom β)) :
    φ₁.comp α = φ₂.comp β := by
  rw [← Spec.map_comp, ← Spec.map_comp] at hw
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hw)

/-- Two matrices over `A` with the same `ev` and with the entry `x` of the first one a unit give
the same Möbius automorphism. -/
theorem mobiusAutFunctor_eq_of_projectiveGeneralLinearTwoEval_eq {A : Type u} [CommRing A]
    (h : Spec (.of A) ⟶ Spec (.of k)) {σ : k →+* A} {M N : Matrix (Fin 2) (Fin 2) A}
    (hM : IsUnit M.det) (hN : IsUnit N.det)
    (e : projectiveGeneralLinearTwoEval σ M hM = projectiveGeneralLinearTwoEval σ N hN)
    (x : Fin 2 × Fin 2) (hx : IsUnit (M x.1 x.2)) :
    mobiusAutFunctor h M hM = mobiusAutFunctor h N hN := by
  obtain ⟨w, hw, rfl⟩ := eq_smul_of_projectiveGeneralLinearTwoEval_eq σ M hM hN e x hx
  exact (mobiusAutFunctor_smul h M hM hw hN).symm

/-- The same, for evaluations along two equal structure maps. -/
theorem mobiusAutFunctor_eq_of_projectiveGeneralLinearTwoEval_eq_of_eq {A : Type u} [CommRing A]
    (h : Spec (.of A) ⟶ Spec (.of k)) {σ σ' : k →+* A} (hσ : σ = σ')
    {M N : Matrix (Fin 2) (Fin 2) A} (hM : IsUnit M.det) (hN : IsUnit N.det)
    (e : projectiveGeneralLinearTwoEval σ M hM = projectiveGeneralLinearTwoEval σ' N hN)
    (x : Fin 2 × Fin 2) (hx : IsUnit (M x.1 x.2)) :
    mobiusAutFunctor h M hM = mobiusAutFunctor h N hN := by
  subst hσ
  exact mobiusAutFunctor_eq_of_projectiveGeneralLinearTwoEval_eq h hM hN e x hx

variable (k) in
/-- The overlap `D(g_p) ∩ D(g_{p'})`: the localization of `D(g_{p'})` at `g_p`. -/
abbrev projectiveGeneralLinearTwoOverlapRing (p p' : Fin 2 × Fin 2) :=
  Localization.Away (algebraMap (projectiveGeneralLinearTwoRing k)
    (projectiveGeneralLinearTwoChartRing k p') (projectiveGeneralLinearTwoChartElement k p))

variable (k) in
/-- The map from `D(g_p)` to the overlap. -/
def projectiveGeneralLinearTwoOverlapLeft (p p' : Fin 2 × Fin 2) :
    projectiveGeneralLinearTwoChartRing k p →+* projectiveGeneralLinearTwoOverlapRing k p p' :=
  IsLocalization.Away.lift (S := projectiveGeneralLinearTwoChartRing k p)
    (projectiveGeneralLinearTwoChartElement k p)
    (g := (algebraMap (projectiveGeneralLinearTwoChartRing k p')
      (projectiveGeneralLinearTwoOverlapRing k p p')).comp (algebraMap _ _))
    (IsLocalization.Away.algebraMap_isUnit (S := projectiveGeneralLinearTwoOverlapRing k p p')
      (algebraMap (projectiveGeneralLinearTwoRing k) (projectiveGeneralLinearTwoChartRing k p')
        (projectiveGeneralLinearTwoChartElement k p)))

variable (k) in
/-- The overlap of two charts of `PGL₂` is the spectrum of the overlap ring. -/
theorem isPullback_projectiveGeneralLinearTwoCover (p p' : Fin 2 × Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (projectiveGeneralLinearTwoOverlapLeft k p p')))
      (Spec.map (CommRingCat.ofHom (algebraMap (projectiveGeneralLinearTwoChartRing k p')
        (projectiveGeneralLinearTwoOverlapRing k p p'))))
      ((projectiveGeneralLinearTwoCover k).f p) ((projectiveGeneralLinearTwoCover k).f p') := by
  have : IsLocalization ((Submonoid.powers (projectiveGeneralLinearTwoChartElement k p)).map
      (algebraMap (projectiveGeneralLinearTwoRing k) (projectiveGeneralLinearTwoChartRing k p')))
      (projectiveGeneralLinearTwoOverlapRing k p p') := by
    rw [Submonoid.map_powers]
    infer_instance
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization
      (algebraMap (projectiveGeneralLinearTwoRing k) (projectiveGeneralLinearTwoChartRing k p'))
      (projectiveGeneralLinearTwoOverlapLeft k p p') (IsLocalization.Away.lift_comp _ _)
      (Submonoid.powers (projectiveGeneralLinearTwoChartElement k p)))).flip

/-- The Möbius automorphisms of the chart matrices of `D(g_p)` and `D(g_{p'})` agree on the
overlap `D(g_p) ∩ D(g_{p'})`. -/
theorem projectiveLineChartAut_compat (p p' : Fin 2 × Fin 2) :
    (Scheme.autFunctor (projectiveLineOver k)).map
        (Scheme.coverOverPairFst (projectiveGeneralLinearTwoCover k) p p').op
        (projectiveLineChartAut k p) =
      (Scheme.autFunctor (projectiveLineOver k)).map
        (Scheme.coverOverPairSnd (projectiveGeneralLinearTwoCover k) p p').op
        (projectiveLineChartAut k p') := by
  have hpb := isPullback_projectiveGeneralLinearTwoCover k p p'
  let 𝒱 : (Scheme.coverOverPairObj (projectiveGeneralLinearTwoCover k) p p').left.OpenCover :=
    { I₀ := Unit
      X _ := Spec (.of (projectiveGeneralLinearTwoOverlapRing k p p'))
      f _ := hpb.isoPullback.hom
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨⟨⟩, hpb.isoPullback.inv x, ?_⟩, fun _ ↦ inferInstance⟩
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
        rfl }
  refine Scheme.aut_ext_of_openCover _ 𝒱 fun i ↦ ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : projectiveGeneralLinearTwoChartRing k p →+*
      projectiveGeneralLinearTwoOverlapRing k p p',
      Spec.map (CommRingCat.ofHom φ₁) = (Scheme.coverOverι 𝒱 i ≫
        Scheme.coverOverPairFst (projectiveGeneralLinearTwoCover k) p p').left :=
    ⟨_, hpb.isoPullback_hom_fst.symm⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : projectiveGeneralLinearTwoChartRing k p' →+*
      projectiveGeneralLinearTwoOverlapRing k p p',
      Spec.map (CommRingCat.ofHom φ₂) = (Scheme.coverOverι 𝒱 i ≫
        Scheme.coverOverPairSnd (projectiveGeneralLinearTwoCover k) p p').left :=
    ⟨_, hpb.isoPullback_hom_snd.symm⟩
  have hφ₁₂ : φ₁.comp (algebraMap (projectiveGeneralLinearTwoRing k)
      (projectiveGeneralLinearTwoChartRing k p)) =
      φ₂.comp (algebraMap (projectiveGeneralLinearTwoRing k)
        (projectiveGeneralLinearTwoChartRing k p')) := by
    have hw : Spec.map (CommRingCat.ofHom φ₁) ≫ (projectiveGeneralLinearTwoCover k).f p =
        Spec.map (CommRingCat.ofHom φ₂) ≫ (projectiveGeneralLinearTwoCover k).f p' := by
      rw [hφ₁, hφ₂]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
        (Category.assoc _ _ _).symm)
    exact comp_eq_of_spec_map_comp_eq hw
  have hdet₁ := isUnit_det_map φ₁ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k p)
  have hdet₂ := isUnit_det_map φ₂ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k p')
  refine (autFunctor_map_mobiusAutFunctor (projectiveGeneralLinearTwoChartHom k p)
    (𝒱.f i ≫ (Scheme.coverOverPairObj (projectiveGeneralLinearTwoCover k) p p').hom)
    (Scheme.coverOverι 𝒱 i ≫ Scheme.coverOverPairFst (projectiveGeneralLinearTwoCover k) p p')
    φ₁ hφ₁.symm _ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k p) hdet₁).trans
    (Eq.trans ?_ (autFunctor_map_mobiusAutFunctor (projectiveGeneralLinearTwoChartHom k p')
    (𝒱.f i ≫ (Scheme.coverOverPairObj (projectiveGeneralLinearTwoCover k) p p').hom)
    (Scheme.coverOverι 𝒱 i ≫ Scheme.coverOverPairSnd (projectiveGeneralLinearTwoCover k) p p')
    φ₂ hφ₂.symm _ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k p') hdet₂).symm)
  have e₁ := projectiveGeneralLinearTwoEval_naturality
      (projectiveGeneralLinearTwoChartStructure k p)
    _ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k p) φ₁ hdet₁
  have e₂ := projectiveGeneralLinearTwoEval_naturality
      (projectiveGeneralLinearTwoChartStructure k p')
    _ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k p') φ₂ hdet₂
  rw [projectiveGeneralLinearTwoEval_chartMatrix] at e₁
  rw [projectiveGeneralLinearTwoEval_chartMatrix] at e₂
  have hσ : φ₁.comp (projectiveGeneralLinearTwoChartStructure k p) =
      φ₂.comp (projectiveGeneralLinearTwoChartStructure k p') :=
    RingHom.ext fun r ↦ congrArg (fun f ↦ f (algebraMap k _ r)) hφ₁₂
  exact mobiusAutFunctor_eq_of_projectiveGeneralLinearTwoEval_eq_of_eq _ hσ hdet₁ hdet₂
    (e₁.symm.trans (hφ₁₂.trans e₂)) p (by
      simp only [Matrix.map_apply, projectiveGeneralLinearTwoChartMatrix_self, map_one]
      exact isUnit_one)

variable (k) in
/-- **The universal automorphism over `PGL₂`**: glued from the Möbius automorphisms of the chart
matrices. -/
def projectiveLineUniversalAut :
    (Scheme.autFunctor (projectiveLineOver k)).obj (op (projectiveGeneralLinearTwoScheme k)) :=
  (Scheme.exists_autFunctor_map_eq_of_openCover (𝒰 := projectiveGeneralLinearTwoCover k)
    (fun p ↦ projectiveLineChartAut k p) projectiveLineChartAut_compat).choose

variable (k) in
/-- The universal automorphism restricts on the chart `D(g_p)` to the Möbius automorphism of the
chart matrix. -/
theorem autFunctor_map_coverOverι_universalAut (p : Fin 2 × Fin 2) :
    (Scheme.autFunctor (projectiveLineOver k)).map
        (Scheme.coverOverι (projectiveGeneralLinearTwoCover k) p).op
        (projectiveLineUniversalAut k) =
      projectiveLineChartAut k p :=
  (Scheme.exists_autFunctor_map_eq_of_openCover (𝒰 := projectiveGeneralLinearTwoCover k)
    (fun p ↦ projectiveLineChartAut k p) projectiveLineChartAut_compat).choose_spec p

/-- **The morphism `Spec A ⟶ PGL₂` of an invertible matrix**, given by `ev_M`. -/
def evaluationOver {A : Type u} [CommRing A] (h : Spec (.of A) ⟶ Spec (.of k))
    (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    Over.mk h ⟶ projectiveGeneralLinearTwoScheme k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (projectiveGeneralLinearTwoEval (ringHomOfSpec h) M hM)))
    (by
      change _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k _)) = h
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
        projectiveGeneralLinearTwoEval_comp_algebraMap, Spec_map_ringHomOfSpec])

/-- The entries of an invertible matrix generate the unit ideal. -/
theorem span_entries_eq_top {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A}
    (hM : IsUnit M.det) : Ideal.span (Set.range fun x : Fin 2 × Fin 2 ↦ M x.1 x.2) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ ?_ hM
  rw [Matrix.det_fin_two]
  have mem : ∀ x : Fin 2 × Fin 2,
      M x.1 x.2 ∈ Ideal.span (Set.range fun x : Fin 2 × Fin 2 ↦ M x.1 x.2) :=
    fun x ↦ Ideal.subset_span ⟨x, rfl⟩
  exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (mem (0, 0)))
      (Ideal.mul_mem_right _ _ (mem (0, 1)))

/-- The cover of `Spec A` by the basic opens of the entries of an invertible matrix. -/
abbrev entriesCover {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} (hM : IsUnit M.det) :
    (Spec (.of A)).OpenCover where
  I₀ := Fin 2 × Fin 2
  X x := Spec (.of (Localization.Away (M x.1 x.2)))
  f _ := Spec.map (CommRingCat.ofHom (algebraMap A _))
  mem₀ := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of A) (fun x : Fin 2 × Fin 2 ↦ M x.1 x.2)
    (span_entries_eq_top hM)).openCover.mem₀

/-- **The universal automorphism pulls back along `ev_M` to the Möbius automorphism of `M`.** -/
theorem autFunctor_map_evaluationOver_universalAut {A : Type u} [CommRing A]
    (h : Spec (.of A) ⟶ Spec (.of k)) (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    (Scheme.autFunctor (projectiveLineOver k)).map (evaluationOver h M hM).op
        (projectiveLineUniversalAut k) =
      mobiusAutFunctor h M hM := by
  refine Scheme.aut_ext_of_openCover _ (entriesCover hM) fun x ↦ ?_
  rw [← Functor.map_comp_apply, ← op_comp]
  set ν := algebraMap A (Localization.Away (M x.1 x.2))
  set ev := projectiveGeneralLinearTwoEval (ringHomOfSpec h) M hM
  have hunit : IsUnit (ν (ev (projectiveGeneralLinearTwoChartElement k x))) := by
    have h1 := congrArg ν
        (projectiveGeneralLinearTwoEval_element_mul_det (ringHomOfSpec h) M hM x x)
    rw [map_mul, map_mul] at h1
    have hx : IsUnit (ν (M x.1 x.2)) := IsLocalization.Away.algebraMap_isUnit _
    exact isUnit_of_mul_isUnit_left (h1 ▸ hx.mul hx)
  have hrange : Set.range ((entriesCover hM).f x ≫ (evaluationOver h M hM).left).base ⊆
      Set.range ((projectiveGeneralLinearTwoCover k).f x).base := by
    rintro _ ⟨y, rfl⟩
    show PrimeSpectrum.comap ev (PrimeSpectrum.comap ν y) ∈
      Set.range (PrimeSpectrum.comap (algebraMap (projectiveGeneralLinearTwoRing k)
        (projectiveGeneralLinearTwoChartRing k x)))
    rw [PrimeSpectrum.localization_away_comap_range (projectiveGeneralLinearTwoChartRing k x)
      (projectiveGeneralLinearTwoChartElement k x)]
    intro hmem
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
  set l := IsOpenImmersion.lift ((projectiveGeneralLinearTwoCover k).f x)
    ((entriesCover hM).f x ≫ (evaluationOver h M hM).left) hrange
  have hl : l ≫ (projectiveGeneralLinearTwoCover k).f x =
      (entriesCover hM).f x ≫ (evaluationOver h M hM).left := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : projectiveGeneralLinearTwoChartRing k x →+* Localization.Away (M x.1 x.2),
      Spec.map (CommRingCat.ofHom φ) = l :=
    ⟨(Spec.preimage l).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  let q : Scheme.coverOverObj (T := Over.mk h) (entriesCover hM) x ⟶
      Scheme.coverOverObj (projectiveGeneralLinearTwoCover k) x :=
    Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
      show Spec.map (CommRingCat.ofHom φ) ≫ (projectiveGeneralLinearTwoCover k).f x ≫
        (projectiveGeneralLinearTwoScheme k).hom = (entriesCover hM).f x ≫ h
      rw [hφ, ← Category.assoc, hl, Category.assoc]
      exact congrArg (_ ≫ ·) (Over.w (evaluationOver h M hM)))
  have hq : Scheme.coverOverι (T := Over.mk h) (entriesCover hM) x ≫ evaluationOver h M hM =
      q ≫ Scheme.coverOverι (projectiveGeneralLinearTwoCover k) x := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    exact hl.symm.trans (congrArg (· ≫ _) hφ.symm)
  rw [hq, op_comp, Functor.map_comp_apply, autFunctor_map_coverOverι_universalAut]
  have hdetφ := isUnit_det_map φ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k x)
  have hdetν := isUnit_det_map ν hM
  refine (autFunctor_map_mobiusAutFunctor (projectiveGeneralLinearTwoChartHom k x)
    ((entriesCover hM).f x ≫ h) q φ rfl _
      (isUnit_projectiveGeneralLinearTwoChartMatrix_det k x) hdetφ).trans
    (Eq.trans ?_ (autFunctor_map_mobiusAutFunctor h ((entriesCover hM).f x ≫ h)
      (Scheme.coverOverι (T := Over.mk h) (entriesCover hM) x) ν rfl M hM hdetν).symm)
  have hφν : φ.comp (algebraMap (projectiveGeneralLinearTwoRing k)
      (projectiveGeneralLinearTwoChartRing k x)) = ν.comp ev := by
    have hw := hl
    rw [← hφ] at hw
    exact comp_eq_of_spec_map_comp_eq hw
  have e₁ := projectiveGeneralLinearTwoEval_naturality
      (projectiveGeneralLinearTwoChartStructure k x)
    _ (isUnit_projectiveGeneralLinearTwoChartMatrix_det k x) φ hdetφ
  rw [projectiveGeneralLinearTwoEval_chartMatrix] at e₁
  have e₂ := projectiveGeneralLinearTwoEval_naturality (ringHomOfSpec h) M hM ν hdetν
  have hσ : φ.comp (projectiveGeneralLinearTwoChartStructure k x) = ν.comp (ringHomOfSpec h) := by
    refine RingHom.ext fun r ↦ ?_
    have := congrArg (fun f ↦ f (algebraMap k _ r)) hφν
    simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
    rw [show ev (algebraMap k _ r) = ringHomOfSpec h r from
      congrArg (fun f ↦ f r) (projectiveGeneralLinearTwoEval_comp_algebraMap _ M hM)] at this
    exact this
  exact mobiusAutFunctor_eq_of_projectiveGeneralLinearTwoEval_eq_of_eq _ hσ hdetφ hdetν
    (e₁.symm.trans (hφν.trans e₂)) x (by
      simp only [Matrix.map_apply, projectiveGeneralLinearTwoChartMatrix_self, map_one]
      exact isUnit_one)

end Universal

/-! ### Affine covers subordinate to given neighbourhoods -/

section Subordinate

/-- An affine open neighbourhood of `y` inside `U y`, given by an open immersion from the
spectrum of a ring. -/
theorem exists_spec_subordinate {Y : Scheme.{u}} (U : Y → Y.Opens) (hU : ∀ y, y ∈ U y) (y : Y) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ Y), IsOpenImmersion f ∧ y ∈ Set.range f ∧
      Set.range f ⊆ U y :=
  Scheme.exists_affine_mem_range_and_range_subset (hU y)

/-- **The open cover of `Y` by affine opens `Spec A_y ∋ y` contained in prescribed neighbourhoods
`U y`.** Each member is the spectrum of a ring written as `Spec (.of A)`. -/
abbrev subordinateAffineCover {Y : Scheme.{u}} (U : Y → Y.Opens) (hU : ∀ y, y ∈ U y) :
    Y.OpenCover where
  I₀ := Y
  X y := Spec (.of ↑(exists_spec_subordinate U hU y).choose)
  f y := (exists_spec_subordinate U hU y).choose_spec.choose
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y ↦ ⟨y, (exists_spec_subordinate U hU y).choose_spec.choose_spec.2.1⟩,
      fun y ↦ (exists_spec_subordinate U hU y).choose_spec.choose_spec.1⟩

/-- The member of `subordinateAffineCover U hU` at `y` lands in `U y`. -/
theorem range_subordinateAffineCover_subset {Y : Scheme.{u}} (U : Y → Y.Opens)
    (hU : ∀ y, y ∈ U y) (y : Y) :
    Set.range ((subordinateAffineCover U hU).f y) ⊆ U y :=
  (exists_spec_subordinate U hU y).choose_spec.choose_spec.2.2

end Subordinate

/-! ### Morphisms to `PGL₂` from affine schemes -/

/-- A ring map whose spectrum lands in a basic open inverts the element. -/
theorem isUnit_of_range_subset {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (r : R)
    (h : Set.range (Spec.map (CommRingCat.ofHom φ)) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))) :
    IsUnit (φ r) := by
  by_contra hr
  obtain ⟨m, hm, hrm⟩ := Ideal.exists_le_maximal (Ideal.span {φ r})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hP := h ⟨⟨m, hm.isPrime⟩, rfl⟩
  change PrimeSpectrum.comap φ ⟨m, hm.isPrime⟩ ∈
    Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) at hP
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at hP
  exact hP (hrm (Ideal.mem_span_singleton_self _))

/-- **A morphism `Spec A ⟶ PGL₂` over `k` landing in a chart `D(g_p)` is `ev_M` for an invertible
matrix `M` over `A`.** -/
theorem exists_eq_evaluationOver {A : Type u} [CommRing A] (h : Spec (.of A) ⟶ Spec (.of k))
    (c : Over.mk h ⟶ projectiveGeneralLinearTwoScheme k) (p : Fin 2 × Fin 2)
    (hc : Set.range c.left ⊆ Set.range ((projectiveGeneralLinearTwoCover k).f p)) :
    ∃ (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det), c = evaluationOver h M hM := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : projectiveGeneralLinearTwoRing k →+* A,
      Spec.map (CommRingCat.ofHom ρ) = c.left :=
    ⟨(Spec.preimage c.left).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have hσ : ρ.comp (algebraMap k _) = ringHomOfSpec h := by
    have hw : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap k _)) =
        h := by
      rw [hρ]
      exact Over.w c
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hw
    rw [← hw, ringHomOfSpec_Spec_map]
  have hunit : IsUnit (ρ (projectiveGeneralLinearTwoChartElement k p)) :=
    isUnit_of_range_subset ρ _ (by rw [hρ]; exact hc)
  obtain ⟨M, hM, -, hρM⟩ := exists_eq_projectiveGeneralLinearTwoEval_of_isUnit _ ρ hσ p hunit
  refine ⟨M, hM, Over.OverMorphism.ext ?_⟩
  rw [← hρ, hρM]
  rfl

/-! ### Representability -/

/-- **Injectivity**: two morphisms to `PGL₂` pulling the universal automorphism back to the same
automorphism are equal. -/
theorem eq_of_autFunctor_map_universalAut_eq {T : Over (Spec (.of k))}
    (a b : T ⟶ projectiveGeneralLinearTwoScheme k)
    (hab : (Scheme.autFunctor (projectiveLineOver k)).map a.op (projectiveLineUniversalAut k) =
      (Scheme.autFunctor (projectiveLineOver k)).map b.op (projectiveLineUniversalAut k)) :
    a = b := by
  let 𝒢 := projectiveGeneralLinearTwoCover k
  let U : T.left → T.left.Opens := fun y ↦
    a.left ⁻¹ᵁ (𝒢.f (𝒢.idx (a.left y))).opensRange ⊓ b.left ⁻¹ᵁ (𝒢.f (𝒢.idx (b.left y))).opensRange
  have hU : ∀ y, y ∈ U y := fun y ↦ ⟨𝒢.covers (a.left y), 𝒢.covers (b.left y)⟩
  let 𝒲 := subordinateAffineCover U hU
  apply Over.OverMorphism.ext
  refine 𝒲.hom_ext _ _ fun y ↦ ?_
  have hsub := range_subordinateAffineCover_subset U hU y
  obtain ⟨Ma, hMa, ha⟩ := exists_eq_evaluationOver (𝒲.f y ≫ T.hom)
    (Scheme.coverOverι 𝒲 y ≫ a) (𝒢.idx (a.left y)) (by
      rintro _ ⟨z, rfl⟩
      exact (hsub ⟨z, rfl⟩).1)
  obtain ⟨Mb, hMb, hb⟩ := exists_eq_evaluationOver (𝒲.f y ≫ T.hom)
    (Scheme.coverOverι 𝒲 y ≫ b) (𝒢.idx (b.left y)) (by
      rintro _ ⟨z, rfl⟩
      exact (hsub ⟨z, rfl⟩).2)
  have e : mobiusAutFunctor (𝒲.f y ≫ T.hom) Ma hMa = mobiusAutFunctor (𝒲.f y ≫ T.hom) Mb hMb := by
    rw [← autFunctor_map_evaluationOver_universalAut, ← autFunctor_map_evaluationOver_universalAut,
      ← ha, ← hb, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      hab]
  obtain ⟨w, hw, hwM⟩ := exists_eq_smul_of_mobiusAutFunctor_eq _ hMa hMb e
  have : Scheme.coverOverι 𝒲 y ≫ a = Scheme.coverOverι 𝒲 y ≫ b := by
    rw [ha, hb]
    subst hwM
    apply Over.OverMorphism.ext
    simp only [evaluationOver, Over.homMk_left]
    rw [projectiveGeneralLinearTwoEval_smul _ Ma hMa hw hMb]
  exact congrArg Over.Hom.left this

/-- **Surjectivity**: every automorphism of `ℙ¹_T` is pulled back from the universal one. -/
theorem exists_autFunctor_map_universalAut_eq {T : Over (Spec (.of k))}
    (ψ : (Scheme.autFunctor (projectiveLineOver k)).obj (op T)) :
    ∃ a : T ⟶ projectiveGeneralLinearTwoScheme k,
      (Scheme.autFunctor (projectiveLineOver k)).map a.op (projectiveLineUniversalAut k) = ψ := by
  let τ := projectiveLineInfinityOver T ≫ ψ.hom.left ≫ pullback.fst _ _
  let PC := (projectiveLineGluingData k).openCover
  let U : T.left → T.left.Opens := fun y ↦ τ ⁻¹ᵁ (PC.f (PC.idx (τ y))).opensRange
  have hU : ∀ y, y ∈ U y := fun y ↦ PC.covers (τ y)
  let 𝒲 := subordinateAffineCover U hU
  have hmob : ∀ y, ∃ (M : Matrix (Fin 2) (Fin 2) _) (hM : IsUnit M.det),
      (Scheme.autFunctor (projectiveLineOver k)).map (Scheme.coverOverι 𝒲 y).op ψ =
        mobiusAutFunctor (𝒲.f y ≫ T.hom) M hM := by
    intro y
    refine exists_eq_mobiusAutFunctor_of_range (𝒲.f y ≫ T.hom) _ ?_
    have key := projectiveLineInfinitySection_comp_endBaseChange (𝒲.f y ≫ T.hom)
      (Scheme.coverOverι 𝒲 y) ψ.hom
    have hsub : Set.range (𝒲.f y ≫ τ) ⊆ Set.range (PC.f (PC.idx (τ y))) := by
      rintro _ ⟨z, rfl⟩
      exact range_subordinateAffineCover_subset U hU y ⟨z, rfl⟩
    have hr : Set.range (projectiveLineInfinitySection _ ≫ projectiveLineBaseChangeHom _ ≫
        (Scheme.endBaseChange _ (Scheme.coverOverι 𝒲 y) ψ.hom).left ≫
          (isPullback_projectiveLineMap_over (𝒲.f y ≫ T.hom)).isoPullback.inv ≫
            projectiveLineMap (ringHomOfSpec (𝒲.f y ≫ T.hom))) ⊆
        Set.range (PC.f (PC.idx (τ y))) := by
      rw [key]
      exact hsub
    rcases hPC : PC.idx (τ y) with ⟨_ | _⟩
    · left
      rw [hPC] at hr
      exact hr
    · right
      rw [hPC] at hr
      exact hr
  choose M hM hMψ using hmob
  let a : ∀ y, Scheme.coverOverObj 𝒲 y ⟶ projectiveGeneralLinearTwoScheme k := fun y ↦
    evaluationOver (𝒲.f y ≫ T.hom) (M y) (hM y)
  have ha : ∀ y, (Scheme.autFunctor (projectiveLineOver k)).map (a y).op
      (projectiveLineUniversalAut k) =
        (Scheme.autFunctor (projectiveLineOver k)).map (Scheme.coverOverι 𝒲 y).op ψ := fun y ↦
    (autFunctor_map_evaluationOver_universalAut _ _ _).trans (hMψ y).symm
  have compat : ∀ y z, pullback.fst (𝒲.f y) (𝒲.f z) ≫ (a y).left =
      pullback.snd (𝒲.f y) (𝒲.f z) ≫ (a z).left := by
    intro y z
    have hι : Scheme.coverOverPairFst 𝒲 y z ≫ Scheme.coverOverι 𝒲 y =
        Scheme.coverOverPairSnd 𝒲 y z ≫ Scheme.coverOverι 𝒲 z :=
      Over.OverMorphism.ext pullback.condition
    have := eq_of_autFunctor_map_universalAut_eq (Scheme.coverOverPairFst 𝒲 y z ≫ a y)
      (Scheme.coverOverPairSnd 𝒲 y z ≫ a z) (by
        rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ha, ha,
          ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
          hι])
    exact congrArg Over.Hom.left this
  let g := 𝒲.glueMorphisms (fun y ↦ (a y).left) compat
  have hg : ∀ y, 𝒲.f y ≫ g = (a y).left := fun y ↦ 𝒲.ι_glueMorphisms _ _ y
  let a₀ : T ⟶ projectiveGeneralLinearTwoScheme k := Over.homMk g (by
    refine 𝒲.hom_ext _ _ fun y ↦ ?_
    rw [← Category.assoc, hg]
    exact Over.w (a y))
  refine ⟨a₀, Scheme.aut_ext_of_openCover _ 𝒲 fun y ↦ ?_⟩
  rw [← Functor.map_comp_apply, ← op_comp]
  have hy : Scheme.coverOverι 𝒲 y ≫ a₀ = a y := Over.OverMorphism.ext (hg y)
  rw [hy, ha]

variable (k) in
/-- **`PGL₂` represents the automorphism functor of `ℙ¹_k`**, with universal element the universal
Möbius automorphism. -/
def projectiveLineAutFunctorRepresentableBy :
    (Scheme.autFunctor (projectiveLineOver k)).RepresentableBy
      (projectiveGeneralLinearTwoScheme k) where
  homEquiv := Equiv.ofBijective
    (fun a ↦ (Scheme.autFunctor (projectiveLineOver k)).map a.op (projectiveLineUniversalAut k))
    ⟨fun a b hab ↦ eq_of_autFunctor_map_universalAut_eq a b hab,
      fun ψ ↦ exists_autFunctor_map_universalAut_eq ψ⟩
  homEquiv_comp f g := by
    change (Scheme.autFunctor (projectiveLineOver k)).map (f ≫ g).op
      (projectiveLineUniversalAut k) = (Scheme.autFunctor (projectiveLineOver k)).map f.op
        ((Scheme.autFunctor (projectiveLineOver k)).map g.op (projectiveLineUniversalAut k))
    rw [op_comp, Functor.map_comp_apply]

/-- **The quotient morphism `GL₂ ⟶ PGL₂` corresponds to the Möbius automorphism of the universal
matrix**: under the identification of `PGL₂` with the automorphism functor of `ℙ¹_k`, a point
`M ∈ GL₂(A)` goes to `μ_M`. -/
theorem projectiveLineAutFunctorRepresentableBy_homEquiv_evaluationOver {A : Type u} [CommRing A]
    (h : Spec (.of A) ⟶ Spec (.of k)) (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    (projectiveLineAutFunctorRepresentableBy k).homEquiv (evaluationOver h M hM) =
      mobiusAutFunctor h M hM :=
  autFunctor_map_evaluationOver_universalAut h M hM


variable (k) in
/-- `GL₂` as a `k`-scheme. -/
abbrev generalLinearTwoOver : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (generalLinearTwoCoordinateRing k))))

variable (k) in
/-- The quotient morphism `GL₂ ⟶ PGL₂` of `k`-schemes. -/
def generalLinearTwoToProjectiveOver :
    generalLinearTwoOver k ⟶ projectiveGeneralLinearTwoScheme k :=
  Over.homMk (generalLinearTwoToProjective k) (by
    change Spec.map (CommRingCat.ofHom (projectiveGeneralLinearTwoRing k).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (projectiveGeneralLinearTwoRing k))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (generalLinearTwoCoordinateRing k)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ))
      (AlgHom.comp_algebraMap (projectiveGeneralLinearTwoRing k).val))

variable (k) in
/-- **`Aut(ℙ¹_k) = PGL₂` as functors, with the Möbius action**: under the identification of the
automorphism functor of `ℙ¹_k` with `PGL₂`, the quotient morphism `GL₂ ⟶ PGL₂` is the Möbius
automorphism of the universal invertible matrix. -/
theorem projectiveLineAutFunctorRepresentableBy_homEquiv_quotient :
    (projectiveLineAutFunctorRepresentableBy k).homEquiv (generalLinearTwoToProjectiveOver k) =
      mobiusAutFunctor _ (generalLinearTwoUniversalMatrix k)
        (isUnit_generalLinearTwoUniversalMatrix_det k) := by
  have e₂ := projectiveGeneralLinearTwoEval_universalMatrix_of_eq k
    (ringHomOfSpec_Spec_map (algebraMap k (generalLinearTwoCoordinateRing k)))
  have : evaluationOver (Spec.map (CommRingCat.ofHom
      (algebraMap k (generalLinearTwoCoordinateRing k)))) (generalLinearTwoUniversalMatrix k)
      (isUnit_generalLinearTwoUniversalMatrix_det k) = generalLinearTwoToProjectiveOver k :=
    Over.OverMorphism.ext (congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) e₂)
  rw [← this, projectiveLineAutFunctorRepresentableBy_homEquiv_evaluationOver]

end AlgebraicGeometry
