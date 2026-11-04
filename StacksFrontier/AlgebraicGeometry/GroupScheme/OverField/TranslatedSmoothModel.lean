module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GenericQuotientFlat
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityAscent

/-!
# Lifting to a smooth affine scheme through a nil-thickening

Let `S` be an affine scheme, `X` an affine scheme smooth over `S`, and `i : Z ⟶ W` a surjective
closed immersion of `S`-schemes with `W` affine (a nil-thickening of affine schemes). **Every
`S`-morphism `Z ⟶ X` extends along `i` to an `S`-morphism `W ⟶ X`.** On rings this is the lifting
property of a formally smooth algebra of finite presentation along a quotient by a nil ideal
(an ideal all of whose elements are nilpotent, not necessarily nilpotent itself).

Applied to a closed subgroup scheme `L ⊆ G` of a group scheme over a field with the same
underlying space, this extends a `k`-morphism `π : V ⟶ X` defined on an open `V ⊆ L` to an affine
open `U ⊆ G` with `L ∩ U ⊆ V`, which is the hypothesis `π'` of
`AlgebraicGeometry.exists_isAffineOpen_locallyOfFinitePresentation`.

The smooth affine target is produced by generic smoothness: if `π : V ⟶ X` is a `k`-morphism to
an integral `k`-scheme locally of finite type over a perfect field, flat at the points of a
nonempty open `V' ⊆ V`, then `π` restricts to a flat quasi-compact `k`-morphism from a nonempty
affine open `W ⊆ V'` to an affine open `X₀ ⊆ X` smooth over `k`.

## Main results

* `Algebra.FormallySmooth.exists_lift_of_le_nilradical`: a formally smooth algebra of finite
  presentation lifts along `B → B ⧸ I` for `I ≤ nilradical B`.
* `AlgebraicGeometry.exists_comp_eq_of_isClosedImmersion_of_surjective`: the geometric form,
  over an affine base.
* `AlgebraicGeometry.exists_extend_of_closedSubgroupScheme`: the form used for a closed subgroup
  scheme with the same underlying space.
* `AlgebraicGeometry.exists_smooth_affine_model`: shrinking a morphism flat on a nonempty open to
  a flat quasi-compact morphism between affine opens, with target smooth over `k`.

## Implementation notes

Mathlib's `Algebra.FormallySmooth.exists_lift` needs a nilpotent ideal. Writing
`A = R[x₁, …, xₙ] ⧸ J` with `J` finitely generated and choosing lifts `bᵢ ∈ B` of `g (xᵢ)`, the
image `J'` of `J` in `B` is finitely generated, contained in `I`, hence nilpotent
(`Ideal.FG.isNilpotent_iff_le_nilradical`); `g` factors through `B ⧸ J'`, and the lift to `B` is
given by `exists_lift` for `J'`.

In the geometric form the kernel of `Γ(W) → Γ(Z)` is a nil ideal because its elements have empty
basic opens (their preimages under the surjection `i` are empty), and morphisms into the affine
scheme `X` are determined by, and exist for, every map on global sections.

For the smooth affine model, `X₀` is an affine neighbourhood of the generic point of `X` inside the
dense smooth open of `geometricallyReduced_iff_exists_dense_open_smooth` (a reduced scheme over a
perfect field is geometrically reduced). No dominance of `π` is needed: `π` is generalizing at a
point `v ∈ V'` where it is flat (`exists_specializes_of_isFlatAt`), so some generalization of `v`,
which still lies in the open `V'`, maps to the generic point of `X`, hence into `X₀`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Algebra.FormallySmooth

/-- **Lifting along a nil ideal.** Let `A` be a formally smooth `R`-algebra of finite
presentation, `B` an `R`-algebra and `I` an ideal of `B` contained in the nilradical. Every
`R`-algebra map `A → B ⧸ I` lifts to an `R`-algebra map `A → B`. -/
theorem exists_lift_of_le_nilradical {R : Type u} {A : Type v} {B : Type w} [CommRing R]
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [FormallySmooth R A]
    [FinitePresentation R A] (I : Ideal B) (hI : I ≤ nilradical B) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  obtain ⟨n, π, hπ, hJ⟩ := FinitePresentation.out (R := R) (A := A)
  choose b hb using fun i : Fin n => Ideal.Quotient.mk_surjective (g (π (MvPolynomial.X i)))
  let h : MvPolynomial (Fin n) R →ₐ[R] B := MvPolynomial.aeval b
  have hh : (Ideal.Quotient.mkₐ R I).comp h = g.comp π :=
    MvPolynomial.algHom_ext fun i => by simp [h, hb]
  let J := RingHom.ker π
  replace hJ : J.FG := hJ
  let J' := J.map h.toRingHom
  have hJ'I : J' ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have := congr($hh x)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    exact this.trans (by rw [show π x = 0 from hx, map_zero])
  have hJ' : IsNilpotent J' := (hJ.map _).isNilpotent_iff_le_nilradical.mpr (hJ'I.trans hI)
  let φ₀ : MvPolynomial (Fin n) R ⧸ J →ₐ[R] B ⧸ J' :=
    Ideal.quotientMapₐ J' h (Ideal.le_comap_map)
  let φ : A →ₐ[R] B ⧸ J' := φ₀.comp (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  obtain ⟨f, hf⟩ := exists_lift J' hJ' φ
  refine ⟨f, ?_⟩
  ext a
  obtain ⟨x, rfl⟩ := hπ a
  have e1 := congr($hf (π x))
  have e2 := congr($hh x)
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at e1 e2 ⊢
  have e3 : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π x) = Ideal.Quotient.mk J x := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  have e4 : φ (π x) = Ideal.Quotient.mk J' (h x) := by
    show φ₀ ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π x)) = _
    rw [e3]
    rfl
  rw [e4, Ideal.Quotient.eq] at e1
  rw [← e2, Ideal.Quotient.eq]
  exact hJ'I e1

end Algebra.FormallySmooth

namespace AlgebraicGeometry

/-- Every ring map `Γ(X, ⊤) ⟶ Γ(W, ⊤)` into the global sections of a scheme `W` is induced by
a morphism `W ⟶ X` when `X` is affine. -/
lemma exists_appTop_eq_of_isAffine {W X : Scheme.{u}} [IsAffine X] (ψ : Γ(X, ⊤) ⟶ Γ(W, ⊤)) :
    ∃ p : W ⟶ X, p.appTop = ψ := by
  refine ⟨W.toSpecΓ ≫ Spec.map ψ ≫ X.isoSpec.inv, ?_⟩
  have h : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
      Scheme.Hom.id_appTop]
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, reassoc_of% h]

/-- A morphism `h : Z ⟶ T` over `S` induces an algebra map `Γ(T, ⊤) ⟶ Γ(Z, ⊤)` over `Γ(S, ⊤)`. -/
private def appTopAlgHom {S T Z : Scheme.{u}} (fT : T ⟶ S) (fZ : Z ⟶ S) (h : Z ⟶ T)
    (hh : h ≫ fT = fZ) :
    letI := fT.appTop.hom.toAlgebra
    letI := fZ.appTop.hom.toAlgebra
    Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z, ⊤) :=
  letI := fT.appTop.hom.toAlgebra
  letI := fZ.appTop.hom.toAlgebra
  { h.appTop.hom with
    commutes' := fun r => by
      show h.appTop (fT.appTop r) = fZ.appTop r
      rw [← hh, Scheme.Hom.comp_appTop]
      rfl }

/-- **Extension through a nil-thickening into a smooth affine scheme.** Let `S` be affine, `X`
an affine scheme smooth over `S`, and `i : Z ⟶ W` a surjective closed immersion of `S`-schemes
with `W` affine. Every `S`-morphism `p : Z ⟶ X` extends to an `S`-morphism `p' : W ⟶ X` with
`i ≫ p' = p`. -/
theorem exists_comp_eq_of_isClosedImmersion_of_surjective {S X Z W : Scheme.{u}} [IsAffine S]
    [IsAffine X] [IsAffine W] (fX : X ⟶ S) (fZ : Z ⟶ S) (fW : W ⟶ S) [Smooth fX]
    (i : Z ⟶ W) [IsClosedImmersion i] [Surjective i] (hi : i ≫ fW = fZ) (p : Z ⟶ X)
    (hp : p ≫ fX = fZ) : ∃ p' : W ⟶ X, p' ≫ fX = fW ∧ i ≫ p' = p := by
  obtain ⟨-, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  let := fX.appTop.hom.toAlgebra
  let := fW.appTop.hom.toAlgebra
  let := fZ.appTop.hom.toAlgebra
  have : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp ‹_›
  let iA := appTopAlgHom fW fZ i hi
  let pA := appTopAlgHom fX fZ p hp
  have hiA : Function.Surjective iA := hsurj
  have hI : RingHom.ker iA ≤ nilradical Γ(W, ⊤) := by
    intro x hx
    rw [mem_nilradical, Scheme.isNilpotent_iff_basicOpen_eq_bot, eq_bot_iff]
    intro w hw
    obtain ⟨z, rfl⟩ := i.surjective w
    have hz : z ∈ i ⁻¹ᵁ W.basicOpen x := hw
    rw [Scheme.preimage_basicOpen_top, show i.appTop x = 0 from hx, Scheme.basicOpen_zero] at hz
    exact hz.elim
  let e := Ideal.quotientKerAlgEquivOfSurjective hiA
  obtain ⟨f, hf⟩ := Algebra.FormallySmooth.exists_lift_of_le_nilradical _ hI
    (e.symm.toAlgHom.comp pA)
  obtain ⟨p', hp'⟩ := exists_appTop_eq_of_isAffine (CommRingCat.ofHom f.toRingHom)
  refine ⟨p', ext_of_isAffine ?_, ext_of_isAffine ?_⟩ <;> rw [Scheme.Hom.comp_appTop, hp']
  · ext r
    exact f.commutes r
  · ext a
    have := congr(e $(congr($hf a)))
    simp only [e, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at this
    exact this

/-- **Extending a smooth affine model from `L ∩ U` to `U`.** Let `G` be a group scheme over a
field `k` and `L ⊆ G` a closed subgroup scheme whose inclusion is surjective. Let
`π : V ⟶ X` be a `k`-morphism from an open `V ⊆ L` to an affine `k`-scheme `X` smooth over `k`,
and `U ⊆ G` an affine open with `L ∩ U ⊆ V`. Then `π` restricted to `L ∩ U` extends to a
`k`-morphism `π' : U ⟶ X`. -/
theorem exists_extend_of_closedSubgroupScheme (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (L : ClosedSubgroupScheme G) [Surjective L.ι.hom.hom.left]
    (V : L.carrier.X.left.Opens) (X : Over (Spec (.of k))) [IsAffine X.left] [Smooth X.hom]
    (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ L.carrier.X.hom)
    (U : G.X.left.Opens) (hU : IsAffineOpen U) (hUV : L.ι.hom.hom.left ⁻¹ᵁ U ≤ V) :
    ∃ π' : U.toScheme ⟶ X.left, π' ≫ X.hom = U.ι ≫ G.X.hom ∧
      (L.ι.hom.hom.left ∣_ U) ≫ π' = L.carrier.X.left.homOfLE hUV ≫ π := by
  have : IsClosedImmersion L.ι.hom.hom.left := L.isClosedImmersion
  have : IsAffine U.toScheme := hU
  have : Surjective (L.ι.hom.hom.left ∣_ U) :=
    IsZariskiLocalAtTarget.restrict ‹Surjective L.ι.hom.hom.left› U
  refine exists_comp_eq_of_isClosedImmersion_of_surjective X.hom
    ((L.ι.hom.hom.left ∣_ U) ≫ U.ι ≫ G.X.hom) (U.ι ≫ G.X.hom) (L.ι.hom.hom.left ∣_ U) rfl
    (L.carrier.X.left.homOfLE hUV ≫ π) ?_
  rw [Category.assoc, hπ, morphismRestrict_ι_assoc, Over.w L.ι.hom.hom,
    Scheme.homOfLE_ι_assoc]

open GenericQuotientFlat in
/-- **A smooth affine model.** Let `k` be a perfect field, `Y` a `k`-scheme, `X` an integral
`k`-scheme locally of finite type, and `π : V ⟶ X` a `k`-morphism on an open `V ⊆ Y` which is
flat at every point of a nonempty open `V' ⊆ V`. Then there are an affine open `X₀ ⊆ X` smooth
over `k` (given as a `k`-scheme `X₀` with an open immersion `j : X₀ ⟶ X` over `k`) and a nonempty
affine open `W ⊆ V'` such that `π` restricts to a flat, quasi-compact `k`-morphism
`π₀ : W ⟶ X₀`. -/
theorem exists_smooth_affine_model {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    (y : Y ⟶ Spec (.of k)) (V : Y.Opens) (X : Over (Spec (.of k))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ y)
    (V' : Y.Opens) (hV'V : V' ≤ V) (hV' : (V' : Set Y).Nonempty)
    (hflat : ∀ v (hv : v ∈ V'), FlatAt π ⟨v, hV'V hv⟩) :
    ∃ (X₀ : Over (Spec (.of k))) (_ : IsAffine X₀.left) (_ : Smooth X₀.hom)
      (j : X₀.left ⟶ X.left) (_ : IsOpenImmersion j) (_ : j ≫ X.hom = X₀.hom)
      (W : Y.Opens) (hW : W ≤ V'), (W : Set Y).Nonempty ∧ IsAffineOpen W ∧
      ∃ π₀ : W.toScheme ⟶ X₀.left, π₀ ≫ X₀.hom = W.ι ≫ y ∧
        π₀ ≫ j = Y.homOfLE (hW.trans hV'V) ≫ π ∧ Flat π₀ ∧ QuasiCompact π₀ := by
  have : GeometricallyReduced X.hom := geometricallyReduced_of_isReduced X.hom
  obtain ⟨U, hUd, hUs⟩ := (geometricallyReduced_iff_exists_dense_open_smooth X.hom).mp this
  have hξU : genericPoint X.left ∈ U :=
    ((genericPoint_spec X.left).mem_open_set_iff U.2).mpr (by simpa using hUd.nonempty)
  obtain ⟨X₀, hX₀, hξX₀, hX₀U⟩ := exists_isAffineOpen_mem_and_subset hξU
  obtain ⟨v, hv⟩ := hV'
  obtain ⟨v', hv'v, hv'ξ⟩ := exists_specializes_of_isFlatAt π ⟨v, hV'V hv⟩ (hflat v hv)
    (genericPoint_specializes _)
  have hv'V' : v'.1 ∈ V' := (hv'v.map continuous_subtype_val).mem_open V'.2 hv
  have hv'X₀ : v'.1 ∈ V.ι ''ᵁ (π ⁻¹ᵁ X₀) := ⟨v', show π v' ∈ X₀ by rw [hv'ξ]; exact hξX₀, rfl⟩
  obtain ⟨W, hW, hvW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := V' ⊓ V.ι ''ᵁ (π ⁻¹ᵁ X₀)) ⟨hv'V', hv'X₀⟩
  have hWV' : W ≤ V' := fun w hw => (hWsub hw).1
  have hWV : W ≤ V := hWV'.trans hV'V
  have hrange : Set.range (Y.homOfLE hWV ≫ π) ⊆ Set.range X₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨u, hu, huw⟩ := (hWsub w.2).2
    have he : u = Y.homOfLE hWV w := Subtype.ext (huw.trans (Scheme.homOfLE_apply hWV w).symm)
    rw [Scheme.Hom.comp_apply, ← he]
    exact hu
  let π₀ : W.toScheme ⟶ X₀.toScheme := IsOpenImmersion.lift X₀.ι (Y.homOfLE hWV ≫ π) hrange
  have hπ₀ : π₀ ≫ X₀.ι = Y.homOfLE hWV ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hX₀a : IsAffine X₀.toScheme := hX₀
  have : IsAffine W.toScheme := hW
  have hsm : Smooth (X₀.ι ≫ X.hom) := by
    rw [← Scheme.homOfLE_ι X.left (show X₀ ≤ U from hX₀U), Category.assoc]
    infer_instance
  have hqc : QuasiCompact π₀ := inferInstance
  have hfl : Flat π₀ := by
    refine Flat.of_stalkMap π₀ fun w => ?_
    have hf : FlatAt (Y.homOfLE hWV ≫ π) w := by
      refine flatAt_comp _ _ w (flatAt_of_flat _ w) ?_
      have he : Y.homOfLE hWV w = ⟨w.1, hWV w.2⟩ := Subtype.ext (Scheme.homOfLE_apply hWV w)
      rw [he]
      exact hflat w.1 (hWV' w.2)
    rw [← hπ₀, FlatAt, Scheme.Hom.stalkMap_comp] at hf
    change ((π₀.stalkMap w).hom.comp (X₀.ι.stalkMap (π₀ w)).hom).Flat at hf
    exact (RingHom.Flat.comp_iff_of_bijective_right
      (ConcreteCategory.bijective_of_isIso _)).mp hf
  refine ⟨Over.mk (X₀.ι ≫ X.hom), hX₀a, hsm, X₀.ι, inferInstance, rfl, W, hWV', ⟨_, hvW⟩, hW,
    π₀, ?_, hπ₀, hfl, hqc⟩
  show π₀ ≫ X₀.ι ≫ X.hom = W.ι ≫ y
  rw [reassoc_of% hπ₀, hπ, Scheme.homOfLE_ι_assoc]

end AlgebraicGeometry

end
