module

import StacksFrontier.AlgebraicGeometry.Size.OpenCover
import StacksFrontier.AlgebraicGeometry.Size.FiniteType
import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Basic
import StacksFrontier.Algebra.Category.Ring.Epi.Cardinality
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Cardinal
import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.Monomorphism

/-!
# Size of the source of a monomorphism of schemes

A monomorphism of schemes `f : X ⟶ Y` does not increase size, provided it is quasi-compact or
locally of finite presentation: in either case `size X ≤ size Y` (Stacks 04VA).

The analogous statement for monomorphisms locally of finite type is false: for
`B = ∏_{n ∈ ℕ} 𝔽₂`, the coproduct `X = ∐_𝒰 Spec 𝔽₂` over the ultrafilters `𝒰` on `ℕ` maps to
`Spec B` by a monomorphism locally of finite type, and `X` has `2 ^ (2 ^ ℵ₀)` affine opens,
whereas `size (Spec B) = 2 ^ ℵ₀`. With no hypothesis beyond `Mono f` there is still the bound
`size X ≤ max (2 ^ #Y) (size Y)`, which lies below every cardinal closed under powersets that
exceeds `size Y`.

## Main results

* `AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact`: a quasi-compact monomorphism
  `X ⟶ Y` satisfies `size X ≤ size Y`.
* `AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation`: a monomorphism
  `X ⟶ Y` locally of finite presentation satisfies `size X ≤ size Y`.
* `AlgebraicGeometry.Scheme.mk_le_two_pow_size`: `#X ≤ 2 ^ size X`.
* `AlgebraicGeometry.Scheme.size_le_of_mono`: every monomorphism `X ⟶ Y` satisfies
  `size X ≤ max (2 ^ #Y) (size Y)`.
* `AlgebraicGeometry.Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit`,
  `AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit`: for a cardinal `κ` closed
  under powersets with `size Y < κ`, `max (2 ^ #Y) (size Y) < κ`, and hence the source of every
  monomorphism into `Y` has size below `κ`.
-/

@[expose] public section

open Cardinal CategoryTheory TopologicalSpace

universe u

namespace Cardinal

/-- If `φ : B → A` is a ring epimorphism, then `#A ≤ max ℵ₀ #B`. -/
theorem mk_le_of_epi_ofHom {B A : Type u} [CommRing B] [CommRing A] (φ : B →+* A)
    (hφ : Epi (CommRingCat.ofHom φ)) :
    #A ≤ max ℵ₀ #B :=
  (epi_card_le B A φ hφ).trans (le_max_right _ _)

/-- A polynomial ring in finitely many variables over `B` has cardinality at most `max ℵ₀ #B`. -/
theorem mk_mvPolynomial_fin_le (B : Type u) [CommRing B] (n : ℕ) :
    #(MvPolynomial (Fin n) B) ≤ max ℵ₀ #B := by
  obtain ⟨e⟩ : Nonempty (Fin n ≃ ULift.{u} (Fin n)) := ⟨Equiv.ulift.symm⟩
  rw [mk_congr (MvPolynomial.renameEquiv B e).toEquiv]
  refine (MvPolynomial.cardinalMk_le_max (σ := ULift.{u} (Fin n)) (R := B)).trans
    (max_le (max_le (le_max_right _ _) (le_trans ?_ (le_max_left _ _))) (le_max_left _ _))
  simp

/-- `#(Finset α) ≤ max ℵ₀ #α`. -/
private theorem mk_finset_le (α : Type u) : #(Finset α) ≤ max ℵ₀ #α := by
  rcases finite_or_infinite α with h | h
  · exact (lt_aleph0_of_finite (Finset α)).le.trans (le_max_left _ _)
  · rw [mk_finset_of_infinite]; exact le_max_right _ _

/-- The pairs `(n, I)` of a natural number `n` and a finitely generated ideal `I` of
`B[x_1, …, x_n]` number at most `max ℵ₀ #B`. -/
private theorem mk_sigma_fg_ideal_le (B : Type u) [CommRing B] :
    #(Σ n : ℕ, {I : Ideal (MvPolynomial (Fin n) B) // I.FG}) ≤ max ℵ₀ #B := by
  have hsummand (n : ℕ) : #{I : Ideal (MvPolynomial (Fin n) B) // I.FG} ≤ max ℵ₀ #B := by
    have hinj : #{I : Ideal (MvPolynomial (Fin n) B) // I.FG} ≤
        #(Finset (MvPolynomial (Fin n) B)) := by
      refine mk_le_of_surjective (f := fun s : Finset (MvPolynomial (Fin n) B) =>
        (⟨Ideal.span ↑s, Submodule.fg_span s.finite_toSet⟩ :
          {I : Ideal (MvPolynomial (Fin n) B) // I.FG})) ?_
      rintro ⟨I, s, hs⟩
      exact ⟨s, Subtype.ext hs⟩
    exact hinj.trans
      ((mk_finset_le _).trans (max_le (le_max_left _ _) (mk_mvPolynomial_fin_le B n)))
  rw [mk_sigma]
  refine (sum_le_sum _ (fun _ => max ℵ₀ #B) hsummand).trans ?_
  rw [sum_const, show Cardinal.lift.{u, 0} #ℕ = ℵ₀ by simp,
    show Cardinal.lift.{0, u} (max ℵ₀ #B) = max ℵ₀ #B by simp]
  exact (mul_le_mul' (le_max_left _ _) le_rfl).trans (mul_eq_self (le_max_left _ _)).le

end Cardinal

namespace AlgebraicGeometry

/-! ### The quasi-compact case over an affine target -/

/-- A quasi-compact scheme admits a finite cover by affine opens, indexed by `Fin n`. -/
private theorem exists_finite_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.affineOpens), ⨆ k, (U k : X.Opens) = ⊤ := by
  classical
  have hcov : (Set.univ : Set X) ⊆ ⋃ i : X.affineOpens, (↑(i : X.Opens) : Set X) := by
    rw [← Opens.coe_iSup, iSup_affineOpens_eq_top X]
    simp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => (↑(i : X.Opens) : Set X)) (fun i => (i : X.Opens).isOpen) hcov
  refine ⟨Fintype.card t, fun k => ((Fintype.equivFin t).symm k : X.affineOpens),
    eq_top_iff.mpr fun x _ => ?_⟩
  rw [Opens.mem_iSup]
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨Fintype.equivFin t ⟨i, hi⟩, by simpa using hxi⟩

/-- For any morphism `g : X ⟶ Y` from a quasi-compact scheme, `X` has a finite cover by affine
opens each of which `g` maps into an affine open of `Y`. -/
private theorem exists_finite_subordinate_affine_cover {X Y : Scheme.{u}} (g : X ⟶ Y)
    [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.affineOpens) (V : Fin n → Y.affineOpens),
      (⨆ k, (U k).1) = ⊤ ∧ ∀ k, (U k).1 ≤ g ⁻¹ᵁ (V k).1 := by
  classical
  have hpt : ∀ x : X, ∃ (U : X.affineOpens) (V : Y.affineOpens),
      x ∈ U.1 ∧ U.1 ≤ g ⁻¹ᵁ V.1 := fun x => by
    obtain ⟨V₀, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Y) (x := g.base x) (U := (⊤ : Y.Opens)) trivial
    obtain ⟨U₀, hU, hxU, hsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := g ⁻¹ᵁ V₀) hxV
    exact ⟨⟨U₀, hU⟩, ⟨V₀, hV⟩, hxU, hsub⟩
  choose U V hmem hsub using hpt
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    (fun x : X => ((U x).1.carrier : Set X)) (fun x => (U x).1.isOpen)
    fun x _ => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  refine ⟨t.card, fun k => U (t.equivFin.symm k).1, fun k => V (t.equivFin.symm k).1,
    eq_top_iff.mpr fun x _ => ?_, fun k => hsub _⟩
  obtain ⟨y, hyt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hyt⟩, by simpa using hxU⟩

/-- For a monomorphism `f : X ⟶ Y` and an affine open `W ⊆ X`, `#Γ(X, W) ≤ size Y`. -/
private theorem mk_sections_le_size_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (W : X.affineOpens) : #Γ(X, W.1) ≤ Y.size := by
  have : IsAffine (↑W.1 : Scheme.{u}) := W.2
  have : Mono (W.1.ι ≫ f) := mono_comp _ _
  obtain ⟨n, U, V, hcov, hsub⟩ := exists_finite_subordinate_affine_cover (W.1.ι ≫ f)
  have hsize : (↑W.1 : Scheme.{u}).size ≤ Y.size := by
    refine Scheme.size_le_of_finite_affine_cover U hcov Y.size (Scheme.aleph0_le_size Y)
      fun k => ?_
    have : IsAffine (↑(U k).1 : Scheme.{u}) := (U k).2
    have : IsAffine (↑(V k).1 : Scheme.{u}) := (V k).2
    have : Mono ((W.1.ι ≫ f).resLE (V k).1 (U k).1 (hsub k)) := by
      have : Mono ((W.1.ι ≫ f).resLE (V k).1 (U k).1 (hsub k) ≫ (V k).1.ι) := by
        rw [Scheme.Hom.resLE_comp_ι]; exact mono_comp _ _
      exact mono_of_mono _ (V k).1.ι
    rw [← Scheme.mk_sections_coe_opens (↑W.1 : Scheme.{u}) (U k).1]
    refine (mk_le_of_epi_ofHom _ (epi_appTop_of_mono
      ((W.1.ι ≫ f).resLE (V k).1 (U k).1 (hsub k)))).trans
      (max_le (Scheme.aleph0_le_size Y) ?_)
    rw [Scheme.mk_sections_coe_opens Y (V k).1]
    exact Scheme.mk_sections_le_size Y (V k)
  rw [← Scheme.mk_sections_coe_opens X W.1]
  exact (Scheme.mk_sections_le_size (↑W.1 : Scheme.{u})
    ⟨⊤, isAffineOpen_top (↑W.1 : Scheme.{u})⟩).trans hsize

/-- A quasi-compact monomorphism into an affine scheme does not increase size. -/
private theorem size_le_of_mono_quasiCompact_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Mono f] [QuasiCompact f] :
    X.size ≤ Y.size := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨n, U, -, hU, -⟩ := exists_finite_subordinate_affine_cover f
  exact Scheme.size_le_of_finite_affine_cover U hU Y.size (Scheme.aleph0_le_size Y) fun k =>
    mk_sections_le_size_of_mono f (U k)

/-! ### The locally-of-finite-presentation case over an affine target -/

/-- Two opens of `X` whose open subschemes are isomorphic over `Y`, along a monomorphism
`f : X ⟶ Y`, are equal. -/
private theorem opens_eq_of_iso_over {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (V W : X.Opens) (α : (↑W : Scheme.{u}) ≅ (↑V : Scheme.{u}))
    (hcomp : α.hom ≫ (V.ι ≫ f) = W.ι ≫ f) : V = W := by
  have h1 : α.hom ≫ V.ι = W.ι := by rw [← cancel_mono f]; simpa using hcomp
  have e2 : (α.hom ≫ V.ι).opensRange = V := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  exact e2.symm.trans <| Opens.ext <| by
    change Set.range (α.hom ≫ V.ι).base = _
    rw [h1]; exact Scheme.Opens.range_ι W

/-- Affine opens of `X` whose section rings are isomorphic *over* `Γ(Y, ⊤)` coincide, when
`f : X ⟶ Y` is a monomorphism into an affine scheme. -/
private theorem affineOpens_eq_of_appTop_iso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    [Mono f] (V W : X.affineOpens)
    (θ : Γ((↑V.1 : Scheme.{u}), ⊤) ≅ Γ((↑W.1 : Scheme.{u}), ⊤))
    (hθ : (V.1.ι ≫ f).appTop ≫ θ.hom = (W.1.ι ≫ f).appTop) :
    V.1 = W.1 := by
  have : IsAffine (↑V.1 : Scheme.{u}) := V.2
  have : IsAffine (↑W.1 : Scheme.{u}) := W.2
  set gV : (↑V.1 : Scheme.{u}) ⟶ Y := V.1.ι ≫ f
  set gW : (↑W.1 : Scheme.{u}) ⟶ Y := W.1.ι ≫ f
  let α : (↑W.1 : Scheme.{u}) ≅ (↑V.1 : Scheme.{u}) :=
    (↑W.1 : Scheme.{u}).isoSpec ≪≫ asIso (Spec.map θ.hom) ≪≫
      (↑V.1 : Scheme.{u}).isoSpec.symm
  have hαhom : α.hom = (↑W.1 : Scheme.{u}).isoSpec.hom ≫
      Spec.map θ.hom ≫ (↑V.1 : Scheme.{u}).isoSpec.inv := by simp [α]
  refine opens_eq_of_iso_over f V.1 W.1 α ?_
  change α.hom ≫ gV = gW
  rw [hαhom, ← cancel_mono Y.isoSpec.hom, Category.assoc, Category.assoc, Category.assoc,
    ← Scheme.isoSpec_hom_naturality gV, Iso.inv_hom_id_assoc, ← Spec.map_comp, hθ,
    Scheme.isoSpec_hom_naturality gW]

/-- The map on global sections is the `appLE` map for `⊤ ≤ ⊤`. -/
private theorem appTop_eq_appLE {X Y : Scheme.{u}} (gV : X ⟶ Y) :
    gV.appTop = Scheme.Hom.appLE gV ⊤ ⊤ le_top := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; congr 1

/-- For `f : X ⟶ Y` locally of finite presentation into an affine `Y`, every affine open `V` of `X`
comes with a presentation of `Γ(X, V)` as a quotient of a polynomial ring over `Γ(Y, ⊤)` in
finitely many variables by a finitely generated ideal. -/
private theorem exists_mvPolynomial_presentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [Mono f] [LocallyOfFinitePresentation f] (V : X.affineOpens) :
    ∃ (n : ℕ) (π : MvPolynomial (Fin n) Γ(Y, ⊤) →+* Γ((↑V.1 : Scheme.{u}), ⊤)),
      Function.Surjective π ∧
      π.comp (MvPolynomial.C) = (V.1.ι ≫ f).appTop.hom ∧
      (RingHom.ker π).FG := by
  have : IsAffine (↑V.1 : Scheme.{u}) := V.2
  set gV : (↑V.1 : Scheme.{u}) ⟶ Y := V.1.ι ≫ f
  have hlfp : LocallyOfFinitePresentation gV := locallyOfFinitePresentation_comp _ _
  have hfp : gV.appTop.hom.FinitePresentation := by
    rw [appTop_eq_appLE]
    exact LocallyOfFinitePresentation.finitePresentation_appLE gV (U := ⊤)
      (isAffineOpen_top Y) (V := ⊤) (isAffineOpen_top (↑V.1 : Scheme.{u})) le_top
  let := gV.appTop.hom.toAlgebra
  have hAFP : Algebra.FinitePresentation (Γ(Y, ⊤) : Type u)
      (Γ((↑V.1 : Scheme.{u}), ⊤) : Type u) := hfp
  obtain ⟨n, π, hsurj, hker⟩ := hAFP.out
  refine ⟨n, π.toRingHom, hsurj, ?_, hker⟩
  ext b
  change π (MvPolynomial.C b) = gV.appTop.hom b
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, RingHom.algebraMap_toAlgebra]

/-- Two affine opens of `X` presented over `Γ(Y, ⊤)` by the same number of variables and the same
kernel are equal, when `f : X ⟶ Y` is a monomorphism into an affine scheme. -/
private theorem affineOpens_eq_of_ker_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    [Mono f] (V W : X.affineOpens) (n : ℕ)
    (πV : MvPolynomial (Fin n) Γ(Y, ⊤) →+* Γ((↑V.1 : Scheme.{u}), ⊤))
    (πW : MvPolynomial (Fin n) Γ(Y, ⊤) →+* Γ((↑W.1 : Scheme.{u}), ⊤))
    (hsV : Function.Surjective πV) (hsW : Function.Surjective πW)
    (hcV : πV.comp MvPolynomial.C = (V.1.ι ≫ f).appTop.hom)
    (hcW : πW.comp MvPolynomial.C = (W.1.ι ≫ f).appTop.hom)
    (hker : RingHom.ker πV = RingHom.ker πW) : V.1 = W.1 := by
  set B : Type u := (Γ(Y, ⊤) : Type u)
  let : Algebra B (Γ((↑V.1 : Scheme.{u}), ⊤) : Type u) := (V.1.ι ≫ f).appTop.hom.toAlgebra
  let : Algebra B (Γ((↑W.1 : Scheme.{u}), ⊤) : Type u) := (W.1.ι ≫ f).appTop.hom.toAlgebra
  have hcommV (b : B) : πV (algebraMap B (MvPolynomial (Fin n) B) b) =
      algebraMap B (Γ((↑V.1 : Scheme.{u}), ⊤) : Type u) b := by
    rw [MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
    exact DFunLike.congr_fun hcV b
  have hcommW (b : B) : πW (algebraMap B (MvPolynomial (Fin n) B) b) =
      algebraMap B (Γ((↑W.1 : Scheme.{u}), ⊤) : Type u) b := by
    rw [MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
    exact DFunLike.congr_fun hcW b
  let πVa : MvPolynomial (Fin n) B →ₐ[B] (Γ((↑V.1 : Scheme.{u}), ⊤) : Type u) :=
    { πV with commutes' := hcommV }
  let πWa : MvPolynomial (Fin n) B →ₐ[B] (Γ((↑W.1 : Scheme.{u}), ⊤) : Type u) :=
    { πW with commutes' := hcommW }
  have hkerA : RingHom.ker πVa.toRingHom = RingHom.ker πWa.toRingHom := hker
  let Θ : (Γ((↑V.1 : Scheme.{u}), ⊤) : Type u) ≃ₐ[B]
      (Γ((↑W.1 : Scheme.{u}), ⊤) : Type u) :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := πVa) hsV).symm.trans
      ((Ideal.quotientEquivAlgOfEq B hkerA).trans
        (Ideal.quotientKerAlgEquivOfSurjective (f := πWa) hsW))
  refine affineOpens_eq_of_appTop_iso f V W Θ.toRingEquiv.toCommRingCatIso ?_
  ext x
  change Θ (algebraMap B _ x) = (W.1.ι ≫ f).appTop.hom x
  rw [AlgEquiv.commutes, RingHom.algebraMap_toAlgebra]

/-- Two affine opens of `X` presented over `Γ(Y, ⊤)` by equal numbers of variables and
heterogeneously equal kernels are equal, when `f : X ⟶ Y` is a monomorphism into an affine
scheme. -/
private theorem affineOpens_eq_of_ker_heq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    [Mono f] (V W : X.affineOpens) (nV nW : ℕ)
    (πV : MvPolynomial (Fin nV) Γ(Y, ⊤) →+* Γ((↑V.1 : Scheme.{u}), ⊤))
    (πW : MvPolynomial (Fin nW) Γ(Y, ⊤) →+* Γ((↑W.1 : Scheme.{u}), ⊤))
    (hsV : Function.Surjective πV) (hsW : Function.Surjective πW)
    (hcV : πV.comp MvPolynomial.C = (V.1.ι ≫ f).appTop.hom)
    (hcW : πW.comp MvPolynomial.C = (W.1.ι ≫ f).appTop.hom)
    (hn : nV = nW) (hker : HEq (RingHom.ker πV) (RingHom.ker πW)) : V.1 = W.1 := by
  subst hn
  exact affineOpens_eq_of_ker_eq f V W nV πV πW hsV hsW hcV hcW (eq_of_heq hker)

/-- For a monomorphism `f : X ⟶ Y` locally of finite presentation into an affine `Y`,
`#X.affineOpens ≤ size Y`. -/
private theorem mk_affineOpens_le_size_of_mono_lfp {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [Mono f] [LocallyOfFinitePresentation f] :
    #X.affineOpens ≤ Y.size := by
  classical
  choose n π hsurj hcomp hfg using (exists_mvPolynomial_presentation f)
  set Ξ : X.affineOpens →
      Σ m : ℕ, {I : Ideal (MvPolynomial (Fin m) (Γ(Y, ⊤) : CommRingCat)) // I.FG} :=
    fun V => ⟨n V, ⟨RingHom.ker (π V), hfg V⟩⟩
  have hinj : Function.Injective Ξ := by
    intro V W hVW
    obtain ⟨hn, hk⟩ := Sigma.mk.inj_iff.mp hVW
    refine Subtype.ext (affineOpens_eq_of_ker_heq f V W (n V) (n W) (π V) (π W) (hsurj V)
      (hsurj W) (hcomp V) (hcomp W) hn ?_)
    exact (Subtype.heq_iff_coe_heq (by rw [hn]) (by rw [hn])).mp hk
  refine (mk_le_of_injective hinj).trans ?_
  rw [Scheme.size_of_isAffine Y]
  exact Cardinal.mk_sigma_fg_ideal_le _

/-- A monomorphism locally of finite presentation into an affine scheme does not increase size. -/
private theorem size_le_of_mono_locallyOfFinitePresentation_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [Mono f]
    [LocallyOfFinitePresentation f] :
    X.size ≤ Y.size := by
  refine Scheme.size_le_of_bounds (Scheme.aleph0_le_size Y)
    (mk_affineOpens_le_size_of_mono_lfp f) fun U => ?_
  rw [Scheme.size_of_isAffine Y]
  let := (Scheme.Hom.appLE f ⊤ ↑U le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, ⊤) Γ(X, ↑U) :=
    RingHom.FiniteType.of_finitePresentation
      (LocallyOfFinitePresentation.finitePresentation_appLE f (U := ⊤) (isAffineOpen_top Y)
        U.2 le_top)
  exact mk_le_of_algebra_finiteType Γ(Y, ⊤) Γ(X, ↑U)

/-! ### Reduction from an affine target to a general target -/

/-- If `size (f ⁻¹ᵁ V) ≤ size V` for every affine open `V` of `Y`, then `size X ≤ size Y`. -/
private theorem size_le_of_affine_target_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ V : Y.affineOpens,
      (↑((Opens.map f.base).obj V.1) : Scheme.{u}).size ≤ (V.1 : Scheme.{u}).size) :
    X.size ≤ Y.size := by
  have : Nonempty Y.affineOpens := ⟨⟨⊥, isAffineOpen_bot Y⟩⟩
  set S : Y.affineOpens → X.Opens := fun i => (Opens.map f.base).obj i.1
  have hcov : ⨆ i, S i = ⊤ := f.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y)
  exact (Scheme.size_le_of_iSup_eq_top S hcov).trans
    (max_le (Scheme.mk_affineOpens_le_size Y)
      (ciSup_le' fun i => (H i).trans (Scheme.size_coe_opens_le Y i.1)))

/-- The restriction of a monomorphism to an open of the target is a monomorphism. -/
private theorem mono_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] (V : Y.Opens) :
    Mono (f ∣_ V) :=
  (MorphismProperty.monomorphisms.iff _).mp
    (IsZariskiLocalAtTarget.restrict ((MorphismProperty.monomorphisms.iff f).mpr ‹Mono f›) V)

/-! ### The two cases of Stacks 04VA -/

/-- If `f : X ⟶ Y` is a quasi-compact monomorphism of schemes, then `size X ≤ size Y`. -/
@[stacks 04VA]
theorem Scheme.size_le_of_mono_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] [QuasiCompact f] :
    X.size ≤ Y.size := by
  refine size_le_of_affine_target_reduction f fun V => ?_
  have : IsAffine (↑V.1 : Scheme.{u}) := V.2
  have := mono_restrict f V.1
  exact size_le_of_mono_quasiCompact_of_isAffine (f ∣_ V.1)

/-- If `f : X ⟶ Y` is a monomorphism of schemes which is locally of finite presentation, then
`size X ≤ size Y`. -/
@[stacks 04VA]
theorem Scheme.size_le_of_mono_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] [LocallyOfFinitePresentation f] :
    X.size ≤ Y.size := by
  refine size_le_of_affine_target_reduction f fun V => ?_
  have : IsAffine (↑V.1 : Scheme.{u}) := V.2
  have := mono_restrict f V.1
  exact size_le_of_mono_locallyOfFinitePresentation_of_isAffine (f ∣_ V.1)

/-! ### Counting the points of a scheme -/

/-- The affine opens of `X` number at most `2 ^ #X`. -/
theorem Scheme.mk_affineOpens_le_two_pow (X : Scheme.{u}) :
    #X.affineOpens ≤ 2 ^ #(X : Type u) :=
  (mk_le_of_injective (f := fun U : X.affineOpens => ((U.1 : X.Opens) : Set X))
    fun _ _ h => Subtype.ext (Opens.ext h)).trans_eq mk_set

/-- An affine open `U` of `X` has at most `2 ^ #Γ(X, U)` points. -/
private theorem mk_coe_affineOpen_le {X : Scheme.{u}} (U : X.affineOpens) :
    #(↑U.1 : Scheme.{u}) ≤ 2 ^ #Γ(X, U.1) :=
  (mk_le_of_injective U.2.isoSpec.hom.injective).trans
    ((mk_le_of_injective (f := fun p : PrimeSpectrum Γ(X, U.1) => (p.asIdeal : Set Γ(X, U.1)))
      fun _ _ h => PrimeSpectrum.ext (SetLike.coe_injective h)).trans_eq mk_set)

/-- A scheme `X` has at most `2 ^ size X` points. -/
theorem Scheme.mk_le_two_pow_size (X : Scheme.{u}) : #(X : Type u) ≤ 2 ^ X.size := by
  classical
  have hex : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 := fun x =>
    Opens.mem_iSup.mp (by rw [iSup_affineOpens_eq_top X]; trivial)
  choose A hA using hex
  have hinj : Function.Injective
      (fun x : X => (⟨A x, ⟨x, hA x⟩⟩ : Σ U : X.affineOpens, (↑U.1 : Scheme.{u}))) :=
    fun _ _ h => by
      simpa using congrArg (fun p : Σ U : X.affineOpens, (↑U.1 : Scheme.{u}) => p.2.1) h
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_sigma]
  refine (sum_le_sum _ (fun _ => 2 ^ X.size) fun U =>
    (mk_coe_affineOpen_le U).trans
      (power_le_power_left two_ne_zero (Scheme.mk_sections_le_size X U))).trans ?_
  rw [sum_const']
  exact (mul_le_max_of_aleph0_le_right ((Scheme.aleph0_le_size X).trans (cantor _).le)).trans
    (max_le ((Scheme.mk_affineOpens_le_size X).trans (cantor _).le) le_rfl)

/-! ### A monomorphism with no further hypothesis -/

/-- Every monomorphism of schemes `f : X ⟶ Y` satisfies `size X ≤ max (2 ^ #Y) (size Y)`. -/
theorem Scheme.size_le_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] :
    X.size ≤ max (2 ^ #(Y : Type u)) Y.size :=
  Scheme.size_le_of_bounds (le_max_of_le_right (Scheme.aleph0_le_size Y))
    (le_max_of_le_left (X.mk_affineOpens_le_two_pow.trans
      (power_le_power_left two_ne_zero (mk_le_of_injective f.injective))))
    fun W => le_max_of_le_right (mk_sections_le_size_of_mono f W)

/-- For a cardinal `κ` closed under powersets with `size Y < κ`, `max (2 ^ #Y) (size Y) < κ`. -/
theorem Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit {κ : Cardinal.{u}}
    (hsl : Cardinal.IsStrongPrelimit κ) {Y : Scheme.{u}} (hY : Y.size < κ) :
    max (2 ^ #(Y : Type u)) Y.size < κ :=
  max_lt (hsl (Y.mk_le_two_pow_size.trans_lt (hsl hY))) hY

/-- The source of any monomorphism into a scheme of size below a cardinal closed under powersets
again has size below that cardinal. -/
theorem Scheme.size_lt_of_mono_of_isStrongPrelimit {κ : Cardinal.{u}}
    (hsl : Cardinal.IsStrongPrelimit κ) {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f]
    (hY : Y.size < κ) : X.size < κ :=
  (Scheme.size_le_of_mono f).trans_lt (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit hsl hY)

end AlgebraicGeometry
