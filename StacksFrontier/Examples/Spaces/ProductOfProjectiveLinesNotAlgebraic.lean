module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.Algebra.Polynomial.Laurent
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Spaces.ProductOfProjectiveLinesFlatCover
public import StacksFrontier.RingTheory.FinitePresentation.PolynomialLift
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveLinePoints
public import StacksFrontier.AlgebraicGeometry.Size.Affine

/-!
# The functor `(ℙ¹)^∞` is not an algebraic space

The functor `(ℙ¹)^∞` of sequences of morphisms to the projective line is an fpqc sheaf with
representable diagonal (`StacksFrontier/Examples/Spaces/ProductOfProjectiveLines.lean`). Restricted
to the big fppf site of `Spec ℤ` of any big fppf site, it is not an algebraic space.

Suppose `f : U ⟶ (ℙ¹)^∞` is a surjective étale atlas. Choose a point `u₀` of `U`, defined over a
field `K`, over the point all of whose coordinates are `[1 : 1]`, and an affine open `U₁` of `U`
containing it.

* The base change of `U` along the chart `Spec ℤ[tᵢ : i ∈ ℕ] ⟶ (ℙ¹)^∞`, `(tᵢ) ↦ ([1 : tᵢ])`, is
  étale over `Spec ℤ[tᵢ]`, so an affine open neighbourhood of the point given by `u₀` is of finite
  presentation over `ℤ[tᵢ]`. Its equations involve finitely many of the variables, so for all but
  finitely many `j` the line `t ↦ ([1 : 1], …, [1 : t], …)` moving only the `j`-th coordinate lifts
  to `U₁` through `u₀`. The same holds for the lines `t ↦ [t : 1]` in the other chart.
* For such a `j` the two lifts agree on `𝔾ₘ = Spec K[t, t⁻¹]`, where the two lines coincide: lifts
  along an étale morphism with affine source agreeing at a point agree on a dense open, by the
  open diagonal of an étale morphism, and hence everywhere, the target being separated.
* The ring maps `Γ(U₁) ⟶ K[t]` and `Γ(U₁) ⟶ K[t⁻¹]` of the two lifts therefore agree in
  `K[t, t⁻¹]`, so they take constant values. The first lift is then constant, while its `j`-th
  coordinate is the nonconstant line `t ↦ [1 : t]`.

This replaces the cohomological argument of the source (vanishing of quasi-coherent cohomology
above a bound on a quasi-compact separated algebraic space, against the nonvanishing of the
cohomology of `𝒪(-2, …, -2)` in every degree): it uses only that `ℙ¹` is not affine.

## Main definitions

* `AlgebraicGeometry.ProjectiveLinePow.siteRestrict`: the restriction of a functor on schemes to
  the big fppf site of `Spec ℤ`.

## Main results

* `AlgebraicGeometry.ProjectiveLinePow.eq_of_etale_of_comp_eq`: uniqueness of lifts along an étale
  morphism to `(ℙ¹)^∞` into an affine open.
* `AlgebraicGeometry.ProjectiveLinePow.exists_finset_forall_exists_lift`: lines through a point of
  an étale chart.
* `AlgebraicGeometry.ProjectiveLinePow.not_isAlgebraicSpace_siteRestrict_projectiveLinePow`:
  `(ℙ¹)^∞` is not an algebraic space.

## References

* [Stacks Project, Tag 078F](https://stacks.math.columbia.edu/tag/078F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProjectiveLinePow

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (.of (ULift.{u} ℤ))))

/-- The restriction of a functor on all schemes to the big fppf site of `Spec ℤ`. -/
abbrev siteRestrict (F : Scheme.{u}ᵒᵖ ⥤ Type u) :
    (BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ)ᵒᵖ ⥤ Type u :=
  (BigFppfOver.toScheme B _ hZ).op ⋙ F

/-- A scheme of the big fppf site, regarded as an object over `Spec ℤ`. -/
abbrev siteObj {Y : Scheme.{u}} (hY : B.Contains Y) : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ :=
  BigFppfOver.mk B _ hZ hY (specULiftZIsTerminal.from Y)

/-- Every morphism of schemes between objects of the big fppf site of `Spec ℤ` is a morphism of
the site, `Spec ℤ` being terminal. -/
def siteHom {T T' : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    (h : (BigFppfOver.toScheme B _ hZ).obj T ⟶ (BigFppfOver.toScheme B _ hZ).obj T') :
    T ⟶ T' :=
  Over.homMk (ObjectProperty.homMk h) (by
    apply ObjectProperty.hom_ext
    exact specULiftZIsTerminal.hom_ext _ _)

/-- The underlying morphism of schemes of `siteHom B hZ h` is `h`. -/
@[simp]
lemma toScheme_map_siteHom {T T' : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    (h : (BigFppfOver.toScheme B _ hZ).obj T ⟶ (BigFppfOver.toScheme B _ hZ).obj T') :
    (BigFppfOver.toScheme B _ hZ).map (siteHom B hZ h) = h :=
  rfl

variable {B hZ}

/-- The components of a morphism of presheaves into the restriction of `(ℙ¹)^∞`, composed with a
morphism of the site. -/
lemma yonedaEquiv_yoneda_map_comp {U Z : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    (f : yoneda.obj U ⟶ siteRestrict B hZ projectiveLinePow.{u}) (a : Z ⟶ U) :
    yonedaEquiv (yoneda.map a ≫ f) =
      fun i ↦ (BigFppfOver.toScheme B _ hZ).map a ≫ yonedaEquiv f i := by
  have h := f.naturality_apply a.op (𝟙 U)
  simp only [yoneda_obj_map, Quiver.Hom.unop_op] at h
  simp only [yonedaEquiv_apply, NatTrans.comp_app, CategoryTheory.comp_apply, yoneda_map_app]
  exact h.trans rfl

/-- Two morphisms of the site into a scheme-valued point of the restriction of `(ℙ¹)^∞` make
the square commute exactly when their components agree. -/
lemma yoneda_map_comp_eq_iff {U Y Z : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    (f : yoneda.obj U ⟶ siteRestrict B hZ projectiveLinePow.{u})
    (g : yoneda.obj Y ⟶ siteRestrict B hZ projectiveLinePow.{u}) (a : Z ⟶ U) (b : Z ⟶ Y) :
    yoneda.map a ≫ f = yoneda.map b ≫ g ↔
      ∀ i, (BigFppfOver.toScheme B _ hZ).map a ≫ yonedaEquiv f i =
        (BigFppfOver.toScheme B _ hZ).map b ≫ yonedaEquiv g i := by
  rw [← yonedaEquiv.apply_eq_iff_eq, yonedaEquiv_yoneda_map_comp, yonedaEquiv_yoneda_map_comp]
  exact funext_iff

/-- The two legs of a represented base change of a morphism `f` into the restriction of
`(ℙ¹)^∞` along a scheme-valued point `y` have the same components. -/
lemma fst'_comp_eq_snd_comp {U Y : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    {f : yoneda.obj U ⟶ siteRestrict B hZ projectiveLinePow.{u}}
    (hr : yoneda.relativelyRepresentable f)
    (y : (siteRestrict B hZ projectiveLinePow.{u}).obj (op Y)) (i : ULift.{u} ℕ) :
    (BigFppfOver.toScheme B _ hZ).map (hr.fst' (yonedaEquiv.symm y)) ≫ yonedaEquiv f i =
      (BigFppfOver.toScheme B _ hZ).map (hr.snd (yonedaEquiv.symm y)) ≫ y i := by
  have h := hr.w (yonedaEquiv.symm y)
  rw [← hr.map_fst', yoneda_map_comp_eq_iff, Equiv.apply_symm_apply] at h
  exact h i

/-- A pair of morphisms of schemes with the same components factors through the represented
base change of a morphism `f` into the restriction of `(ℙ¹)^∞` along a scheme-valued point. -/
lemma exists_lift_pullback {U Y Z : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    {f : yoneda.obj U ⟶ siteRestrict B hZ projectiveLinePow.{u}}
    (hr : yoneda.relativelyRepresentable f)
    (y : (siteRestrict B hZ projectiveLinePow.{u}).obj (op Y))
    (a : (BigFppfOver.toScheme B _ hZ).obj Z ⟶ (BigFppfOver.toScheme B _ hZ).obj U)
    (b : (BigFppfOver.toScheme B _ hZ).obj Z ⟶ (BigFppfOver.toScheme B _ hZ).obj Y)
    (h : ∀ i, a ≫ yonedaEquiv f i = b ≫ y i) :
    ∃ w : Z ⟶ hr.pullback (yonedaEquiv.symm y),
      (BigFppfOver.toScheme B _ hZ).map w ≫
          (BigFppfOver.toScheme B _ hZ).map (hr.fst' (yonedaEquiv.symm y)) = a ∧
        (BigFppfOver.toScheme B _ hZ).map w ≫
          (BigFppfOver.toScheme B _ hZ).map (hr.snd (yonedaEquiv.symm y)) = b := by
  have hc : yoneda.map (siteHom B hZ a) ≫ f = yoneda.map (siteHom B hZ b) ≫ yonedaEquiv.symm y := by
    rw [yoneda_map_comp_eq_iff, Equiv.apply_symm_apply]
    exact h
  refine ⟨hr.lift' _ _ hc, ?_, ?_⟩
  · rw [← Functor.map_comp, hr.lift'_fst]
    rfl
  · rw [← Functor.map_comp, hr.lift'_snd]
    rfl

/-- **Uniqueness of lifts along an étale atlas.** Let `f` be an étale morphism from a
representable presheaf `U` to the restriction of `(ℙ¹)^∞`, and let `U₁` be an affine open of `U`.
Two morphisms `l`, `m` from a reduced irreducible scheme `G` of the site into `U₁` with the same
image in `(ℙ¹)^∞` agree as soon as they agree after composing with a morphism `E ⟶ G` from a
nonempty scheme of the site. -/
theorem eq_of_etale_of_comp_eq {U G E : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    {f : yoneda.obj U ⟶ siteRestrict B hZ projectiveLinePow.{u}}
    (het : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf f)
    {U₁ : ((BigFppfOver.toScheme B _ hZ).obj U).Opens} (hU₁ : IsAffineOpen U₁)
    [IsReduced ((BigFppfOver.toScheme B _ hZ).obj G)]
    [IrreducibleSpace ((BigFppfOver.toScheme B _ hZ).obj G)]
    [Nonempty ((BigFppfOver.toScheme B _ hZ).obj E)]
    (l m : (BigFppfOver.toScheme B _ hZ).obj G ⟶ U₁)
    (hlm : ∀ i, l ≫ U₁.ι ≫ yonedaEquiv f i = m ≫ U₁.ι ≫ yonedaEquiv f i)
    (e : (BigFppfOver.toScheme B _ hZ).obj E ⟶ (BigFppfOver.toScheme B _ hZ).obj G)
    (he : e ≫ l = e ≫ m) :
    l = m := by
  let y : (siteRestrict B hZ projectiveLinePow.{u}).obj (op G) :=
    fun i ↦ l ≫ U₁.ι ≫ yonedaEquiv f i
  let hr := het.rep
  let π := (BigFppfOver.toScheme B _ hZ).map (hr.snd (yonedaEquiv.symm y))
  let ρ := (BigFppfOver.toScheme B _ hZ).map (hr.fst' (yonedaEquiv.symm y))
  have hπ : Etale π := het.property_snd _
  obtain ⟨s, hs₁, hs₂⟩ := exists_lift_pullback hr y (l ≫ U₁.ι) (𝟙 _) fun i ↦ by
    rw [Category.assoc, Category.id_comp]
  obtain ⟨s', hs'₁, hs'₂⟩ := exists_lift_pullback hr y (m ≫ U₁.ι) (𝟙 _) fun i ↦ by
    rw [Category.assoc, Category.id_comp]
    exact (hlm i).symm
  obtain ⟨e', -, he'⟩ := exists_lift_pullback (Y := G) (Z := E) hr y (e ≫ l ≫ U₁.ι) e fun i ↦ by
    simp only [Category.assoc, y]
  have hee : e ≫ (BigFppfOver.toScheme B _ hZ).map s =
      e ≫ (BigFppfOver.toScheme B _ hZ).map s' := by
    have key : ∀ t : (BigFppfOver.toScheme B _ hZ).obj E ⟶
        (BigFppfOver.toScheme B _ hZ).obj (hr.pullback (yonedaEquiv.symm y)),
        t ≫ ρ = e ≫ l ≫ U₁.ι → t ≫ π = e →
          (BigFppfOver.toScheme B _ hZ).map (siteHom B hZ t) =
            (BigFppfOver.toScheme B _ hZ).map (siteHom B hZ
              (e ≫ (BigFppfOver.toScheme B _ hZ).map s)) := by
      intro t ht₁ ht₂
      congr 1
      apply hr.hom_ext'
      · apply (BigFppfOver.toScheme B _ hZ).map_injective
        rw [Functor.map_comp, Functor.map_comp]
        exact (show t ≫ ρ = (e ≫ (BigFppfOver.toScheme B _ hZ).map s) ≫ ρ by
          rw [ht₁, Category.assoc, hs₁])
      · apply (BigFppfOver.toScheme B _ hZ).map_injective
        rw [Functor.map_comp, Functor.map_comp]
        exact (show t ≫ π = (e ≫ (BigFppfOver.toScheme B _ hZ).map s) ≫ π by
          rw [ht₂, Category.assoc, hs₂, Category.comp_id])
    have := key (e ≫ (BigFppfOver.toScheme B _ hZ).map s')
      (by rw [Category.assoc, hs'₁, ← Category.assoc, ← he, Category.assoc])
      (by rw [Category.assoc, hs'₂, Category.comp_id])
    exact this.symm
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : (BigFppfOver.toScheme B _ hZ).obj G ⟶ pullback π π,
      t ≫ pullback.fst π π = (BigFppfOver.toScheme B _ hZ).map s ∧
        t ≫ pullback.snd π π = (BigFppfOver.toScheme B _ hZ).map s' :=
    ⟨pullback.lift _ _ (hs₂.trans hs'₂.symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  let O : ((BigFppfOver.toScheme B _ hZ).obj G).Opens := t ⁻¹ᵁ (pullback.diagonal π).opensRange
  obtain ⟨x₀⟩ := ‹Nonempty ((BigFppfOver.toScheme B _ hZ).obj E)›
  have hx₀ : e x₀ ∈ O := by
    have ht : e ≫ t = (e ≫ (BigFppfOver.toScheme B _ hZ).map s) ≫ pullback.diagonal π := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, ht₁, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, ht₂, pullback.diagonal_snd, Category.comp_id, hee]
    refine ⟨(e ≫ (BigFppfOver.toScheme B _ hZ).map s) x₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← ht, Scheme.Hom.comp_apply]
  have hO : IsDominant O.ι := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Opens.range_ι]
    exact O.isOpen.dense ⟨_, hx₀⟩
  let ℓ : (O : Scheme.{u}) ⟶ (BigFppfOver.toScheme B _ hZ).obj (hr.pullback (yonedaEquiv.symm y)) :=
    IsOpenImmersion.lift (pullback.diagonal π) (O.ι ≫ t) (by
      rintro _ ⟨x, rfl⟩
      exact x.2)
  have hℓ : ℓ ≫ pullback.diagonal π = O.ι ≫ t := IsOpenImmersion.lift_fac _ _ _
  have h₁ : O.ι ≫ (BigFppfOver.toScheme B _ hZ).map s = ℓ := by
    have := congrArg (· ≫ pullback.fst π π) hℓ
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, ht₁] at this
    exact this.symm
  have h₂ : O.ι ≫ (BigFppfOver.toScheme B _ hZ).map s' = ℓ := by
    have := congrArg (· ≫ pullback.snd π π) hℓ
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, ht₂] at this
    exact this.symm
  have hO' : O.ι ≫ l = O.ι ≫ m := by
    rw [← cancel_mono U₁.ι, Category.assoc, Category.assoc, ← hs₁, ← hs'₁, ← Category.assoc,
      ← Category.assoc, h₁, h₂]
  have : IsAffine U₁ := hU₁
  exact ext_of_isDominant_of_isSeparated (specULiftZIsTerminal.from (U₁ : Scheme.{u}))
    (specULiftZIsTerminal.hom_ext _ _) O.ι hO'

/-- **Lines through a point of an étale atlas.** Let `f` be an étale morphism from a
representable presheaf `U` to the restriction of `(ℙ¹)^∞` to the big fppf site, `U₁` an affine
open of `U`, and `pt` a natural family of ring-valued points of `ℙ¹` (an affine chart). If a
`K`-point `u₀` of `U₁` lies over the point all of whose coordinates are `pt K 1`, then for all but
finitely many indices `j` the line of `(ℙ¹)^∞` moving only the `j`-th coordinate along the chart
lifts to `U₁` through `u₀`.

The fibre product of `U` with the chart `Spec ℤ[tᵢ] ⟶ (ℙ¹)^∞` is étale over `Spec ℤ[tᵢ]`, so an
affine open neighbourhood of the point given by `u₀` is of finite presentation over it, and its
equations involve only finitely many of the variables `tᵢ`. -/
theorem exists_finset_forall_exists_lift {U : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    {f : yoneda.obj U ⟶ siteRestrict B hZ projectiveLinePow.{u}}
    (het : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf f)
    {U₁ : ((BigFppfOver.toScheme B _ hZ).obj U).Opens}
    (pt : ∀ (R : Type u) [CommRing R], R → (Spec (.of R) ⟶ projectiveSpaceAtUniverse.{u} 1))
    (hpt : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (g : R →+* R') (a : R),
      Spec.map (CommRingCat.ofHom g) ≫ pt R a = pt R' (g a))
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    (u₀ : Spec (.of K) ⟶ U₁) (hu₀ : ∀ i, u₀ ≫ U₁.ι ≫ yonedaEquiv f i = pt K 1) :
    ∃ s : Finset (ULift.{u} ℕ), ∀ j ∉ s, ∃ l : Spec (.of (Polynomial K)) ⟶ U₁,
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 1)) ≫ l = u₀ ∧
      ∀ i, l ≫ U₁.ι ≫ yonedaEquiv f i =
        pt (Polynomial K) (if i = j then Polynomial.X else 1) := by
  classical
  let A := MvPolynomial (ULift.{u} ℕ) (ULift.{u} ℤ)
  have hV : B.Contains (Spec (.of A)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hZ
      (MvPolynomial.cardinalMk_le_max.trans (by simp))
  let yV : ULift.{u} ℕ → (Spec (.of A) ⟶ projectiveSpaceAtUniverse.{u} 1) :=
    fun i ↦ pt A (MvPolynomial.X i)
  let y : (siteRestrict B hZ projectiveLinePow.{u}).obj (op (siteObj B hZ hV)) := yV
  let hr := het.rep
  let W := hr.pullback (yonedaEquiv.symm y)
  let π : (BigFppfOver.toScheme B _ hZ).obj W ⟶ Spec (.of A) :=
    (BigFppfOver.toScheme B _ hZ).map (hr.snd (yonedaEquiv.symm y))
  let ρ := (BigFppfOver.toScheme B _ hZ).map (hr.fst' (yonedaEquiv.symm y))
  have hπ : Etale π := het.property_snd _
  have hw : ∀ i, ρ ≫ yonedaEquiv f i = π ≫ yV i := fst'_comp_eq_snd_comp hr y
  let ε : A →+* K :=
    MvPolynomial.eval₂Hom ((Int.castRingHom K).comp ULift.ringEquiv.toRingHom) fun _ ↦ 1
  let v₀ : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom ε)
  have hv₀ : ∀ i, v₀ ≫ yV i = pt K 1 := fun i ↦ by
    change Spec.map (CommRingCat.ofHom ε) ≫ pt A (MvPolynomial.X i) = pt K 1
    rw [hpt]
    congr 1
    exact MvPolynomial.eval₂Hom_X' _ _ i
  obtain ⟨w₀, hw₀f, hw₀s⟩ := exists_lift_pullback (Z := siteObj B hZ hK) hr y (u₀ ≫ U₁.ι) v₀
    fun i ↦ (Category.assoc _ _ _).trans ((hu₀ i).trans (hv₀ i).symm)
  let wbar : Spec (.of K) ⟶ (BigFppfOver.toScheme B _ hZ).obj W :=
    (BigFppfOver.toScheme B _ hZ).map w₀
  obtain ⟨x₀⟩ : Nonempty (Spec (.of K)) := inferInstance
  have hx₀ : wbar x₀ ∈ ρ ⁻¹ᵁ U₁ := by
    have key : (wbar ≫ ρ) x₀ ∈ U₁ := by
      rw [show wbar ≫ ρ = u₀ ≫ U₁.ι from hw₀f, Scheme.Hom.comp_apply]
      exact (u₀ x₀).2
    exact key
  obtain ⟨W₁, hW₁, hxW₁, hW₁N⟩ := exists_isAffineOpen_mem_and_subset hx₀
  have : IsAffine W₁ := hW₁
  let w₁ : Spec (.of K) ⟶ W₁ := IsOpenImmersion.lift W₁.ι wbar (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim x x₀]
    exact hxW₁)
  have hw₁ : w₁ ≫ W₁.ι = wbar := IsOpenImmersion.lift_fac _ _ _
  have : LocallyOfFinitePresentation π := inferInstance
  let h₁ : (W₁ : Scheme.{u}) ⟶ Spec (.of A) := W₁.ι ≫ π
  let ψ := (W₁ : Scheme.{u}).isoSpec
  let φ₀ : CommRingCat.of A ⟶ Γ(W₁, ⊤) := Spec.preimage (ψ.inv ≫ h₁)
  have hφ₀ : Spec.map φ₀ = ψ.inv ≫ W₁.ι ≫ π := Spec.map_preimage _
  have hfp : φ₀.hom.FinitePresentation := by
    have : LocallyOfFinitePresentation (Spec.map φ₀) := by
      rw [hφ₀]
      infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  let χ : Γ(W₁, ⊤) ⟶ CommRingCat.of K := Spec.preimage (w₁ ≫ ψ.hom)
  have hχ : Spec.map χ = w₁ ≫ ψ.hom := Spec.map_preimage _
  have hφχ : φ₀ ≫ χ = CommRingCat.ofHom ε := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ, hφ₀]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hw₁]
    exact hw₀s
  have hχX : ∀ i, χ.hom (φ₀.hom (MvPolynomial.X i)) = 1 := fun i ↦ by
    have := congrArg (fun φ ↦ φ.hom (MvPolynomial.X i)) hφχ
    exact this.trans (MvPolynomial.eval₂Hom_X' _ _ i)
  obtain ⟨s, hs⟩ := MvPolynomial.exists_finset_forall_exists_polynomial_lift φ₀.hom hfp χ.hom
  refine ⟨s, fun j hj ↦ ?_⟩
  obtain ⟨σ, hσX, -, hσev⟩ := hs j hj
  rw [hχX] at hσev
  let l' : Spec (.of (Polynomial K)) ⟶ W₁ := Spec.map (CommRingCat.ofHom σ) ≫ ψ.inv
  let l : Spec (.of (Polynomial K)) ⟶ U₁ :=
    IsOpenImmersion.lift U₁.ι (l' ≫ W₁.ι ≫ ρ) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hW₁N (l' x).2)
  have hl : l ≫ U₁.ι = l' ≫ W₁.ι ≫ ρ := IsOpenImmersion.lift_fac _ _ _
  have hev : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : K))) ≫
      Spec.map (CommRingCat.ofHom σ) = Spec.map χ := by
    rw [← Spec.map_comp]
    congr 1
    ext1
    exact hσev
  refine ⟨l, ?_, fun i ↦ ?_⟩
  · rw [← cancel_mono U₁.ι, Category.assoc, hl]
    change (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : K))) ≫
      Spec.map (CommRingCat.ofHom σ)) ≫ ψ.inv ≫ W₁.ι ≫ ρ = _
    rw [hev, hχ, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hw₁]
    exact hw₀f
  · rw [← Category.assoc, hl]
    simp only [Category.assoc]
    rw [hw i]
    change Spec.map (CommRingCat.ofHom σ) ≫ (ψ.inv ≫ W₁.ι ≫ π) ≫ pt A (MvPolynomial.X i) = _
    rw [← hφ₀, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (σ.comp φ₀.hom)) ≫ pt A (MvPolynomial.X i) = _
    rw [hpt]
    congr 1
    change σ (φ₀.hom (MvPolynomial.X i)) = _
    rw [hσX, hχX]
    split_ifs <;> simp

/-- Evaluation at `1` of a polynomial in `X⁻¹`, read in the Laurent polynomial ring, is evaluation
at `1`. -/
lemma eval₂_one_invert_toLaurent {K : Type u} [CommRing K] (q : Polynomial K) :
    LaurentPolynomial.eval₂ (RingHom.id K) 1 (LaurentPolynomial.invert (Polynomial.toLaurent q)) =
      Polynomial.eval 1 q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp

/-- **No point of an étale chart lies over `[1 : 1]^∞`.** Let `f` be an étale morphism from a
representable presheaf `U` to the restriction of `(ℙ¹)^∞` and `U₁` an affine open of `U`. Then
no point of `U₁`, defined over a field of the site, lies over the point of `(ℙ¹)^∞` all of
whose coordinates are `[1 : 1]`.

For some index `j` the lines `t ↦ [1 : t]` and `t ↦ [t : 1]` in the `j`-th coordinate both
lift to `U₁` through the point (`exists_finset_forall_exists_lift`). On `𝔾ₘ` they are the same
line of `(ℙ¹)^∞`, so the two lifts agree there (`eq_of_etale_of_comp_eq`). Their ring maps
`Γ(U₁) ⟶ K[t]` and `Γ(U₁) ⟶ K[t⁻¹]` then agree in `K[t, t⁻¹]`, so they take constant values:
the first lift is constant, while its `j`-th coordinate is the nonconstant line `t ↦ [1 : t]`. -/
theorem false_of_etale_of_point {U : BigFppfOver B (Spec (.of (ULift.{u} ℤ))) hZ}
    {f : yoneda.obj U ⟶ siteRestrict B hZ projectiveLinePow.{u}}
    (het : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hZ)).presheaf f)
    {U₁ : ((BigFppfOver.toScheme B _ hZ).obj U).Opens} (hU₁ : IsAffineOpen U₁)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    (u₀ : Spec (.of K) ⟶ U₁)
    (hu₀ : ∀ i, u₀ ≫ U₁.ι ≫ yonedaEquiv f i = ProjectiveLine.pointOne K 1) : False := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_finset_forall_exists_lift het ProjectiveLine.pointOne
    (fun _ _ _ _ g a ↦ ProjectiveLine.SpecMap_comp_pointOne _ g a) K hK u₀ hu₀
  obtain ⟨s₁, hs₁⟩ := exists_finset_forall_exists_lift het ProjectiveLine.pointInf
    (fun _ _ _ _ g a ↦ ProjectiveLine.SpecMap_comp_pointInf _ g a) K hK u₀
    (fun i ↦ by rw [hu₀ i, ProjectiveLine.pointOne_one])
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset (s₀ ∪ s₁)
  obtain ⟨l, hl₁, hl⟩ := hs₀ j fun h ↦ hj (Finset.mem_union_left _ h)
  obtain ⟨m, hm₁, hm⟩ := hs₁ j fun h ↦ hj (Finset.mem_union_right _ h)
  -- The two lifts agree on `𝔾ₘ`.
  let L := LaurentPolynomial K
  let a₀ : Polynomial K →+* L := Polynomial.toLaurent
  let a₁ : Polynomial K →+* L := LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent
  have hG : B.Contains (Spec (.of L)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hK
      ((Cardinal.mk_le_of_isLocalization_powers (Polynomial.X : Polynomial K) L).trans
        (max_le (le_max_left _ _)
          (Polynomial.cardinalMk_le_max.trans_eq (max_comm _ _))))
  let ev : L →+* K := LaurentPolynomial.eval₂ (RingHom.id K) 1
  have hlm : ∀ i, (Spec.map (CommRingCat.ofHom a₀) ≫ l) ≫ U₁.ι ≫ yonedaEquiv f i =
      (Spec.map (CommRingCat.ofHom a₁) ≫ m) ≫ U₁.ι ≫ yonedaEquiv f i := by
    intro i
    rw [Category.assoc, Category.assoc, hl i, hm i, ProjectiveLine.SpecMap_comp_pointOne,
      ProjectiveLine.SpecMap_comp_pointInf]
    split_ifs
    · have hT : a₀ Polynomial.X = (((LaurentPolynomial.isUnit_T (R := K) 1).unit : Lˣ) : L) := by
        rw [IsUnit.unit_spec]
        exact Polynomial.toLaurent_X
      rw [hT, ProjectiveLine.pointOne_eq_pointInf]
      congr 1
      rw [show a₁ Polynomial.X = LaurentPolynomial.T (-1) by simp [a₁]]
      exact Units.inv_eq_of_mul_eq_one_right (by
        rw [IsUnit.unit_spec, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero])
    · simp only [map_one]
      exact ProjectiveLine.pointOne_one
  have hev₀ : CommRingCat.ofHom a₀ ≫ CommRingCat.ofHom ev =
      CommRingCat.ofHom (Polynomial.evalRingHom 1) := by
    refine CommRingCat.hom_ext (RingHom.ext fun q ↦ ?_)
    exact LaurentPolynomial.eval₂_toLaurent (RingHom.id K) 1 q
  have hev₁ : CommRingCat.ofHom a₁ ≫ CommRingCat.ofHom ev =
      CommRingCat.ofHom (Polynomial.evalRingHom 1) := by
    refine CommRingCat.hom_ext (RingHom.ext fun q ↦ ?_)
    exact eval₂_one_invert_toLaurent q
  have : IsReduced ((BigFppfOver.toScheme B _ hZ).obj (siteObj B hZ hG)) :=
    inferInstanceAs (IsReduced (Spec (.of L)))
  have : IrreducibleSpace ((BigFppfOver.toScheme B _ hZ).obj (siteObj B hZ hG)) :=
    inferInstanceAs (IrreducibleSpace (Spec (.of L)))
  have : Nonempty ((BigFppfOver.toScheme B _ hZ).obj (siteObj B hZ hK)) :=
    inferInstanceAs (Nonempty (Spec (.of K)))
  have hglue : Spec.map (CommRingCat.ofHom a₀) ≫ l = Spec.map (CommRingCat.ofHom a₁) ≫ m :=
    eq_of_etale_of_comp_eq het hU₁ (G := siteObj B hZ hG) (E := siteObj B hZ hK) _ _ hlm
      (Spec.map (CommRingCat.ofHom ev)) (by
        change Spec.map (CommRingCat.ofHom ev) ≫ Spec.map (CommRingCat.ofHom a₀) ≫ l =
          Spec.map (CommRingCat.ofHom ev) ≫ Spec.map (CommRingCat.ofHom a₁) ≫ m
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hev₀, hev₁,
          hl₁, hm₁])
  -- So the first lift is constant, which its `j`-th coordinate is not.
  have : IsAffine U₁ := hU₁
  let ψ := (U₁ : Scheme.{u}).isoSpec
  let α : Γ(U₁, ⊤) ⟶ CommRingCat.of (Polynomial K) := Spec.preimage (l ≫ ψ.hom)
  let β : Γ(U₁, ⊤) ⟶ CommRingCat.of (Polynomial K) := Spec.preimage (m ≫ ψ.hom)
  have hα : Spec.map α = l ≫ ψ.hom := Spec.map_preimage _
  have hβ : Spec.map β = m ≫ ψ.hom := Spec.map_preimage _
  have hαβ : α ≫ CommRingCat.ofHom a₀ = β ≫ CommRingCat.ofHom a₁ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hα, hβ, ← Category.assoc, hglue, Category.assoc]
  have hconst : ∀ c, α.hom c = Polynomial.C (Polynomial.eval 1 (α.hom c)) := by
    intro c
    have h : Polynomial.toLaurent (α.hom c) =
        LaurentPolynomial.invert (Polynomial.toLaurent (β.hom c)) :=
      congrArg (fun φ ↦ φ.hom c) hαβ
    have h' := Polynomial.eq_C_coeff_zero_of_toLaurent_eq_invert h
    rw [h', Polynomial.eval_C]
  have hα' : α = (α ≫ CommRingCat.ofHom (Polynomial.evalRingHom 1)) ≫
      CommRingCat.ofHom Polynomial.C := by
    exact CommRingCat.hom_ext (RingHom.ext fun c ↦ hconst c)
  have hlconst : l = Spec.map (CommRingCat.ofHom Polynomial.C) ≫ u₀ := by
    rw [← cancel_mono ψ.hom, ← hα, Category.assoc, ← hl₁, Category.assoc, ← hα,
      ← Spec.map_comp, ← Spec.map_comp, ← hα']
  have hj' := hl j
  simp only [↓reduceIte] at hj'
  rw [hlconst, Category.assoc, hu₀ j, ProjectiveLine.SpecMap_comp_pointOne,
    map_one] at hj'
  exact Polynomial.X_ne_C (1 : K) (ProjectiveLine.pointOne_injective hj').symm

variable (B hZ) in
/-- **`(ℙ¹)^∞` is not an algebraic space.** For every big fppf site `B`, the restriction to the
big fppf site of `Spec ℤ` of the functor `(ℙ¹)^∞` of sequences of morphisms to `ℙ¹` is not an
algebraic space: a surjective étale atlas would have a point over the point all of whose
coordinates are `[1 : 1]`, which `false_of_etale_of_point` rules out. -/
theorem not_isAlgebraicSpace_siteRestrict_projectiveLinePow :
    ¬ IsAlgebraicSpace B (Spec (.of (ULift.{u} ℤ))) hZ
      (siteRestrict B hZ projectiveLinePow.{u}) := by
  intro h
  obtain ⟨U, f, hsurj, het⟩ := h.exists_atlas
  let y : (siteRestrict B hZ projectiveLinePow.{u}).obj (op (siteObj B hZ hZ)) :=
    fun _ ↦ ProjectiveLine.pointOne _ 1
  let hr := hsurj.rep
  have hπ₀ : Surjective ((BigFppfOver.toScheme B _ hZ).map (hr.snd (yonedaEquiv.symm y))) :=
    hsurj.property_snd _
  obtain ⟨z⟩ : Nonempty (Spec (.of (ULift.{u} ℤ))) := inferInstance
  obtain ⟨w, -⟩ := hπ₀.surj z
  let W₀ := (BigFppfOver.toScheme B _ hZ).obj (hr.pullback (yonedaEquiv.symm y))
  have hW₀ : B.Contains W₀ := (hr.pullback (yonedaEquiv.symm y)).left.property
  have hK : B.Contains (Spec (.of (W₀.residueField w))) := B.residueField_spec_contains hW₀ w
  let u₀' : Spec (.of (W₀.residueField w)) ⟶ (BigFppfOver.toScheme B _ hZ).obj U :=
    W₀.fromSpecResidueField w ≫ (BigFppfOver.toScheme B _ hZ).map (hr.fst' (yonedaEquiv.symm y))
  have hu₀' : ∀ i, u₀' ≫ yonedaEquiv f i = ProjectiveLine.pointOne (W₀.residueField w) 1 := by
    intro i
    change W₀.fromSpecResidueField w ≫ _ ≫ _ = _
    rw [fst'_comp_eq_snd_comp hr y i, ← Category.assoc,
      show W₀.fromSpecResidueField w ≫
          (BigFppfOver.toScheme B _ hZ).map (hr.snd (yonedaEquiv.symm y)) =
        Spec.map (CommRingCat.ofHom ((Int.castRingHom (W₀.residueField w)).comp
          ULift.ringEquiv.toRingHom)) from specULiftZIsTerminal.hom_ext _ _]
    change _ ≫ ProjectiveLine.pointOne _ 1 = _
    rw [ProjectiveLine.SpecMap_comp_pointOne, map_one]
  obtain ⟨x₀⟩ : Nonempty (Spec (.of (W₀.residueField w))) := inferInstance
  obtain ⟨U₁, hU₁, hxU₁, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (u₀' x₀))
  let u₀ : Spec (.of (W₀.residueField w)) ⟶ U₁ := IsOpenImmersion.lift U₁.ι u₀' (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim x x₀]
    exact hxU₁)
  have hu₀ : u₀ ≫ U₁.ι = u₀' := IsOpenImmersion.lift_fac _ _ _
  exact false_of_etale_of_point het hU₁ (W₀.residueField w) hK u₀
    (fun i ↦ by rw [← Category.assoc, hu₀, hu₀' i])

/-- Every big fppf site contains `Spec ℤ`, its cutoff being uncountable. -/
theorem _root_.AlgebraicGeometry.BigFppfSite.contains_spec_ulift_int (B : BigFppfSite.{u}) :
    B.Contains (Spec (.of (ULift.{u} ℤ))) := by
  rw [BigFppfSite.Contains, Scheme.size_Spec]
  refine max_lt B.aleph0_lt_cutoff ?_
  have hℤ : Cardinal.mk (CommRingCat.of (ULift.{u} ℤ)) = Cardinal.aleph0 := by simp
  rw [hℤ]
  exact B.aleph0_lt_cutoff

/-- **Stacks 078F.** There is a functor `F : Sch^{opp} ⥤ Sets` which satisfies the sheaf
condition for the fpqc topology, has representable diagonal `F ⟶ F × F`, and receives a
surjective, flat, universally open, quasi-compact morphism `U ⟶ F` from a scheme `U`, but which
is not an algebraic space: for every big fppf site `B`, its restriction to the big fppf site of
`Spec ℤ` in `B` is not an algebraic space over `Spec ℤ`.

The functor is `(ℙ¹)^∞`, sending a scheme `T` to the set of sequences of morphisms `T ⟶ ℙ¹`.
Its sheaf property and representable diagonal are
`AlgebraicGeometry.isSheaf_fpqc_projectiveLinePow` and
`AlgebraicGeometry.relativelyRepresentable_diag_projectiveLinePow`. The morphism `U ⟶ F` is
`projectiveLinePowFlatCover`, from the product of countably many copies of the disjoint union of
the two standard charts of `ℙ¹`, an affine scheme. That `F` is not an algebraic space is
`not_isAlgebraicSpace_siteRestrict_projectiveLinePow`. A morphism from a scheme to `F` is
surjective, flat, universally open or quasi-compact when every base change of it along a morphism
from a scheme is, in the sense of `CategoryTheory.MorphismProperty.presheaf`. -/
@[stacks 078F]
theorem exists_fpqc_sheaf_not_isAlgebraicSpace :
    ∃ F : Scheme.{u}ᵒᵖ ⥤ Type u,
      Presheaf.IsSheaf Scheme.fpqcTopology.{u} F ∧
      yoneda.relativelyRepresentable (diag F) ∧
      (∃ (U : Scheme.{u}) (p : yoneda.obj U ⟶ F),
        MorphismProperty.presheaf (C := Scheme.{u}) @Surjective p ∧
        MorphismProperty.presheaf (C := Scheme.{u}) @Flat p ∧
        MorphismProperty.presheaf (C := Scheme.{u}) @UniversallyOpen p ∧
        MorphismProperty.presheaf (C := Scheme.{u}) @QuasiCompact p) ∧
      ∀ B : BigFppfSite.{u}, ¬ IsAlgebraicSpace B (Spec (.of (ULift.{u} ℤ)))
        B.contains_spec_ulift_int (siteRestrict B B.contains_spec_ulift_int F) := by
  obtain ⟨U, -, p, hs, hf, ho, hq⟩ :=
    exists_surjective_flat_universallyOpen_quasiCompact_projectiveLinePow.{u}
  exact ⟨projectiveLinePow.{u}, isSheaf_fpqc_projectiveLinePow,
    relativelyRepresentable_diag_projectiveLinePow, ⟨U, p, hs, hf, ho, hq⟩,
    fun B ↦ not_isAlgebraicSpace_siteRestrict_projectiveLinePow B B.contains_spec_ulift_int⟩

end AlgebraicGeometry.ProjectiveLinePow

end
