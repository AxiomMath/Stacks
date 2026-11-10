module

public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalSequence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalToolkit
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.StalkGenerators
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Generators
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.ImmersionStalk
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence
public import StacksFrontier.RingTheory.Koszul.Concatenation
public import StacksFrontier.RingTheory.Koszul.Homotopy
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Koszul-regularity of the first of two immersions with split conormal sequence

Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions with `j` locally of finite presentation whose
conormal sequence is exact and locally split.  If both `j` and `i ≫ j` are Koszul-regular, then so
is `i`.  This is part (3) of [Stacks Project, Tag 068Z].

The argument is local at a point `z` of `Z`.  Near `x = j (i z)` the ideal `I` of `Y` is generated
by sections `f₁, …, f_n` whose classes are a basis of `I_x / 𝔪_x I_x`, and these extend to a basis
of `J_x / 𝔪_x J_x` for the ideal `J` of `Z` by sections `g₁, …, g_m`.  Applying
[Stacks Project, Tag 067N] to `I` and to `J` turns both families into Koszul-regular generating
sequences on one neighbourhood of `x`, and the images of the `g_b` in `O_Y` then form a
Koszul-regular sequence generating the ideal of `i`.

`Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_retraction` is the same conclusion
when `j` admits a retraction `ρ : X ⟶ Y` instead of a split conormal sequence: the map
`u ↦ u - ρ^♯ (j^♯ u)` retracts the stalk of the ideal of `j` off that of the ideal of `i ≫ j`,
which is all the splitting is used for, and it needs no finite presentation.

`Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_mem_smul_stalkIdeal` is the common
generalisation of the two: its hypothesis is exactly what the splitting and the retraction are
each used to produce, namely that an element of `I_x` lying in `𝔪_x J_x` already lies in
`𝔪_x I_x`, i.e. injectivity of the map of cotangent fibres `I_x / 𝔪_x I_x ⟶ J_x / 𝔪_x J_x`.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 068Z)](https://stacks.math.columbia.edu/tag/068Z)
* [Stacks Project, Lemma 31.20.5 (Tag 067N)](https://stacks.math.columbia.edu/tag/067N)
* [Stacks Project, Lemma 15.30.14 (Tag 068M)](https://stacks.math.columbia.edu/tag/068M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RingTheory.QuasiRegular
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.AlgebraicGeometry

variable {Z Y X : Scheme.{u}}

/-! ### Commutative algebra of Koszul-regular sequences -/

section Algebra

open scoped TensorProduct

/-- Koszul-regularity only depends on the sequence. -/
private lemma koszulRegular_congr {R : Type*} [CommRing R] {r : ℕ} {f g : Fin r → R} (h : f = g)
    (hf : Koszul.IsKoszulRegular f) : Koszul.IsKoszulRegular g := h ▸ hf

/-- Koszul-regularity of a sequence transports along a ring isomorphism, which is a flat ring
map. -/
private theorem koszulRegular_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {r : ℕ} {f : Fin r → R} (hf : Koszul.IsKoszulRegular f) :
    Koszul.IsKoszulRegular fun k => e (f k) := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  have : Module.Flat R S := RingHom.Flat.of_bijective e.bijective
  have h := KoszulC.isKoszulRegular_baseChange (S := S) f R
    ((Koszul.isKoszulRegularOn_self_iff f).mpr hf)
  have h' := Koszul.isKoszulRegularOn_of_linearEquiv (R := S) _
    (TensorProduct.AlgebraTensorModule.rid R S S) h
  have hae : (fun k => algebraMap R S (f k)) = fun k => e (f k) := by
    funext k
    rw [RingHom.algebraMap_toAlgebra]
    rfl
  exact hae ▸ (Koszul.isKoszulRegularOn_self_iff _).mp h'

/-- A sequence generating the unit ideal is Koszul-regular: it annihilates its own Koszul
homology. -/
private theorem koszulRegular_of_jid_eq_top {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (h : Jid f = ⊤) : Koszul.IsKoszulRegular f := by
  intro n _
  refine ModuleCat.isZero_iff_subsingleton.mpr ?_
  refine (Module.annihilator_eq_top_iff (R := R)).mp ?_
  exact top_unique (h ▸ (Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator f).2 n)

/-- **Stacks Project, Tag 068M, read through a surjection.** If `f` generates the kernel of a
surjective ring map `φ` and the image of `g` in the quotient by that kernel is Koszul-regular,
then `φ ∘ g` is Koszul-regular. -/
private theorem koszulRegular_map_of_ker_eq_jid {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) {n m : ℕ} (f : Fin n → R) (g : Fin m → R)
    (hker : Jid f = RingHom.ker φ)
    (hg : Koszul.IsKoszulRegular fun b : Fin m => Ideal.Quotient.mk (Jid f) (g b)) :
    Koszul.IsKoszulRegular fun b => φ (g b) := by
  have he : (fun b : Fin m => (Ideal.quotEquivOfEq hker).trans
      (RingHom.quotientKerEquivOfSurjective hφ)
      (Ideal.Quotient.mk (Jid f) (g b))) = fun b => φ (g b) := by
    funext b
    change (RingHom.quotientKerEquivOfSurjective hφ)
      ((Ideal.quotEquivOfEq hker) (Ideal.Quotient.mk (Jid f) (g b))) = φ (g b)
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hφ (g b)
  exact koszulRegular_congr he (koszulRegular_of_ringEquiv _ hg)

end Algebra

/-! ### Stalks of the defining ideal sheaf of an immersion -/

section Stalk

/-- **The tail of a Koszul-regular generating family is Koszul-regular downstairs.** If `f`
generates the defining ideal sheaf of `j` over `U` and `f` followed by `g` is Koszul-regular at
`j z`, then the germs of the images of the `g_b` in `O_{Z, z}` form a Koszul-regular sequence. -/
private theorem koszulRegular_stalkMap_tail (j : Z ⟶ X) [IsImmersion j] (U : X.Opens) {n m : ℕ}
    (f : Fin n → Γ(X, U)) (g : Fin m → Γ(X, U))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom j) U f) (z : Z) (hz : j z ∈ U)
    (hf : Koszul.IsKoszulRegular (germFamily X.toRingedSpace U f (j z) hz))
    (hfg : Koszul.IsKoszulRegular (Fin.append (germFamily X.toRingedSpace U f (j z) hz)
      (germFamily X.toRingedSpace U g (j z) hz))) :
    Koszul.IsKoszulRegular fun b => (j.stalkMap z).hom (X.presheaf.germ U (j z) hz (g b)) :=
  koszulRegular_map_of_ker_eq_jid (j.stalkMap z).hom (j.stalkMap_surjective z) _ _
    (ker_stalkMap_eq_jid j U f hgen z hz).symm
    (Koszul.koszulRegular_quotient_of_koszulRegular_append _ _ hf hfg)

end Stalk

/-! ### Moving generating families along an open immersion -/

section OpenImmersion

/-- Koszul exactness of a family of sections is preserved by transport to the image of an open
immersion. -/
private theorem isKoszulSequenceExactOn_image {W : Scheme.{u}} (f : W ⟶ X) [IsOpenImmersion f]
    (U : W.Opens) {r : ℕ} (s : Fin r → Γ(W, U))
    (h : IsKoszulSequenceExactOn W.toRingedSpace U s fun k => 0 < k) :
    IsKoszulSequenceExactOn X.toRingedSpace (f ''ᵁ U) (fun b => (f.appIso U).inv (s b))
      fun k => 0 < k := by
  refine (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular X.toRingedSpace (f ''ᵁ U)
    _).mpr fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := id hy
  have hW := (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular W.toRingedSpace U s).mp h
    x hx
  refine koszulRegular_congr
    (f := fun b => (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm
      (germFamily W.toRingedSpace U s x hx b)) ?_
    (koszulRegular_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm hW)
  funext b
  exact ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm_apply_eq).mpr
    (germ_appIso_inv f U x hx hy (s b)).symm

/-- Koszul exactness of a family of sections is preserved by pullback along an open immersion. -/
private theorem isKoszulSequenceExactOn_preimage {W : Scheme.{u}} (f : W ⟶ X)
    [IsOpenImmersion f] (U : X.Opens) {r : ℕ} (s : Fin r → Γ(X, U))
    (h : IsKoszulSequenceExactOn X.toRingedSpace U s fun k => 0 < k) :
    IsKoszulSequenceExactOn W.toRingedSpace (f ⁻¹ᵁ U) (fun b => f.app U (s b))
      fun k => 0 < k := by
  refine (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular W.toRingedSpace (f ⁻¹ᵁ U)
    _).mpr fun x hx => ?_
  have hfx : f x ∈ U := hx
  have hX := (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular X.toRingedSpace U s).mp h
    (f x) hfx
  refine koszulRegular_congr
    (f := fun b => (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
      (germFamily X.toRingedSpace U s (f x) hfx b)) ?_
    (koszulRegular_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv hX)
  funext b
  exact Scheme.Hom.germ_stalkMap_apply f U x hfx (s b)

/-- **Local Koszul-regular generators of the defining ideal sheaf of an immersion.** A
Koszul-regular immersion has, near every point of its image, a Koszul-regular family of sections
generating its defining ideal sheaf on the target. -/
private theorem exists_koszulRegular_generators_near_image (j : Z ⟶ X) [IsImmersion j]
    (hK : IsKoszulRegularImmersion j) (z : Z) :
    ∃ (V : X.Opens) (_ : j z ∈ V) (n : ℕ) (t : Fin n → Γ(X, V)),
      IsKoszulSequenceExactOn X.toRingedSpace V t (fun k => 0 < k) ∧
        IsGeneratedByOn X.toRingedSpace (definingIdealOfHom j) V t := by
  have hcomp : idealRestriction j.coborderRange.ι (definingIdealOfHom j) =
      definingIdealOfHom j.liftCoborder := by
    rw [show definingIdealOfHom j =
      definingIdealOfHom (j.liftCoborder ≫ j.coborderRange.ι) from
        (congrArg definingIdealOfHom j.liftCoborder_ι).symm]
    exact definingIdealOfHom_comp_open j.liftCoborder j.coborderRange.ι
  have hzU : j.liftCoborder z ∈ idealQuotientSupport
      j.coborderRange.toScheme.toRingedSpace (definingIdealOfHom j.liftCoborder) := by
    rw [definingIdealQuotient_support_eq_range]
    exact ⟨z, rfl⟩
  have hpt : j.coborderRange.ι (j.liftCoborder z) = j z := by
    rw [← Scheme.Hom.comp_apply, j.liftCoborder_ι]
  obtain ⟨V, hzV, n, s, hs, hgen⟩ := hK (j.liftCoborder z) hzU
  exact ⟨j.coborderRange.ι ''ᵁ V, ⟨j.liftCoborder z, hzV, hpt⟩, n,
    fun b => (j.coborderRange.ι.appIso V).inv (s b),
    isKoszulSequenceExactOn_image j.coborderRange.ι V s hs,
    (isGeneratedByOn_image_iff j.coborderRange.ι (definingIdealOfHom j) V s).mpr (hcomp ▸ hgen)⟩

/-- The stalk of the defining ideal sheaf of a Koszul-regular immersion is finitely generated. -/
private theorem koszulRegularImmersion_stalkIdeal_fg (j : Z ⟶ X) [IsImmersion j]
    (hK : IsKoszulRegularImmersion j) (z : Z) :
    (Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
      (definingIdealOfHom j) (j z)).FG := by
  obtain ⟨V, hzV, n, t, _, hgen⟩ := exists_koszulRegular_generators_near_image j hK z
  exact stalkIdeal_fg_of_isGeneratedByOn (definingIdealOfHom j) V t hgen (j z) hzV

end OpenImmersion

/-! ### Realising a basis of the cotangent fibre by Koszul-regular generators -/

section Local067N

/-- **Stacks Project, Tag 067N, part (3), from a local witness.** Let `J` be an ideal subsheaf
generated on a neighbourhood `V` of `x` by a Koszul-regular family, and let `f₁, …, f_r ∈ J_x` lift
a basis of `J_x / 𝔪_x J_x`.  Then on a smaller neighbourhood the `f_i` are the germs of sections of
`J` forming a Koszul-regular family which generates `J` there. -/
private theorem exists_koszulRegular_generators_of_basis_local {W : LocallyRingedSpace.{u}}
    (J : (Stacks.RingedSpace.structureSheafModule W.toRingedSpace).Submodule) (x : W) {r s : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal J x)
    (b : Module.Basis (Fin r) (W.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (W.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber J x))
    (hf : ∀ i, b i = Submodule.Quotient.mk (f i))
    (hne : Stacks.RingedSpace.stalkIdeal J x ≠ ⊤)
    (V : Opens W) (hxV : x ∈ V) (g : Fin s → W.presheaf.obj (op V))
    (hK : IsKoszulSequenceExactOn W.toRingedSpace V g fun k => 0 < k)
    (hgen : IsGeneratedByOn W.toRingedSpace J V g) :
    ∃ (U : Opens W) (hxU : x ∈ U) (fU : Fin r → J.obj (op U)),
      (∀ i, W.presheaf.germ U x hxU (fU i).1 = (f i).1) ∧
        IsKoszulSequenceExactOn W.toRingedSpace U (fun i => (fU i).1) (fun k => 0 < k) ∧
        IsGeneratedByOn W.toRingedSpace J U fun i => (fU i).1 := by
  classical
  have hKgerm :=
    (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular W.toRingedSpace V g).mp hK
  have hqr : ∀ (y : W) (hy : y ∈ V), RingTheory.Sequence.IsQuasiRegular (W.presheaf.stalk y)
      (List.ofFn (germFamily W.toRingedSpace V g y hy)) := fun y hy =>
    Koszul.isQuasiRegular_of_isH1RegularOn
      ((Koszul.isH1RegularOn_self_iff _).mpr (hKgerm y hy 1 one_ne_zero))
  obtain ⟨hrs, U, hxU, iUV, fU, A, hA, hfU, hchange⟩ :=
    Stacks.RingedSpace.exists_invertible_change_of_local_generators J x f b hf hne V hxV g
      (fun y hy => stalkIdeal_eq_jid_of_isGeneratedByOn J g hgen y hy) hqr
  subst hrs
  simp only [Fin.cast_refl, id_eq] at hchange
  have hUV : U ≤ V := leOfHom iUV
  have hchange' : ∀ i, (fU i).1 = ∑ j, A i j * W.presheaf.map (homOfLE hUV).op (g j) := by
    intro i
    simpa only [show iUV = homOfLE hUV from Subsingleton.elim _ _] using hchange i
  have hspan : ∀ (y : W) (hy : y ∈ U),
      Jid (germFamily W.toRingedSpace U (fun i => (fU i).1) y hy) =
        Jid (germFamily W.toRingedSpace V g y (hUV hy)) := by
    intro y hy
    refine jid_eq_of_isUnit_matrix _ _ ((W.presheaf.germ U y hy).hom.mapMatrix A)
      (hA.map (W.presheaf.germ U y hy).hom.mapMatrix) fun i => ?_
    have h := congrArg (W.presheaf.germ U y hy) (hchange' i)
    simpa only [map_sum, map_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
      W.presheaf.germ_res_apply, germFamily] using h
  refine ⟨U, hxU, fU, hfU, ?_, ?_⟩
  · refine (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular W.toRingedSpace U _).mpr
      fun y hy => ?_
    exact (Koszul.regularity_of_generators_of_eq_span_range
      (Jid (germFamily W.toRingedSpace U (fun i => (fU i).1) y hy)) _ rfl).2.2
      ⟨germFamily W.toRingedSpace V g y (hUV hy), (hspan y hy).symm, hKgerm y (hUV hy)⟩
  · refine isGeneratedByOn_of_forall_stalkIdeal_eq J _ fun y hy => ?_
    rw [hspan y hy]
    exact stalkIdeal_eq_jid_of_isGeneratedByOn J g hgen y (hUV hy)

end Local067N

/-! ### The tail of an adapted generating family -/

section Tail

/-- The tail of a Koszul-regular generating family of the ideal of `Z` is a Koszul-regular family
on `Y`. -/
private theorem isKoszulSequenceExactOn_tail (j : Z ⟶ X) [IsImmersion j] (U : X.Opens) {n m : ℕ}
    (f : Fin n → Γ(X, U)) (g : Fin m → Γ(X, U))
    (hgen : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom j) U f)
    (hf : IsKoszulSequenceExactOn X.toRingedSpace U f fun k => 0 < k)
    (hfg : IsKoszulSequenceExactOn X.toRingedSpace U (Fin.append f g) fun k => 0 < k) :
    IsKoszulSequenceExactOn Z.toRingedSpace (j ⁻¹ᵁ U) (fun b => j.app U (g b))
      fun k => 0 < k := by
  refine (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular Z.toRingedSpace (j ⁻¹ᵁ U)
    _).mpr fun z hz => ?_
  have hzU : j z ∈ U := hz
  have hKf := (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular X.toRingedSpace U f).mp hf
    (j z) hzU
  have hKfg := (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular X.toRingedSpace U
    (Fin.append f g)).mp hfg (j z) hzU
  rw [germFamily_append] at hKfg
  refine koszulRegular_congr
    (f := fun b => (j.stalkMap z).hom (X.presheaf.germ U (j z) hzU (g b))) ?_
    (koszulRegular_stalkMap_tail j U f g hgen z hzU hKf hKfg)
  funext b
  exact Scheme.Hom.germ_stalkMap_apply j U z hzU (g b)

/-- **Stacks Project, Tag 067N, part (3), at a Koszul-regular immersion.** Elements of the stalk
at `g z` of the defining ideal sheaf of a Koszul-regular immersion `g` whose classes form a basis
of the cotangent fibre are the germs of sections generating that ideal sheaf Koszul-regularly on a
neighbourhood. -/
private theorem exists_koszulRegular_generators_of_koszulRegularImmersion (g : Z ⟶ X)
    [IsImmersion g] (hg : IsKoszulRegularImmersion g) (z : Z) {x : X} (hx : g z = x) {r : ℕ}
    (f : Fin r → Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
      (definingIdealOfHom g) x)
    (b : Module.Basis (Fin r) (X.toLocallyRingedSpace.presheaf.stalk x ⧸
        IsLocalRing.maximalIdeal (X.toLocallyRingedSpace.presheaf.stalk x))
      (Stacks.RingedSpace.idealCotangentFiber (X := X.toLocallyRingedSpace)
        (definingIdealOfHom g) x))
    (hf : ∀ a, b a = Submodule.Quotient.mk (f a)) :
    ∃ (U : X.Opens) (hxU : x ∈ U)
      (fU : Fin r → (definingIdealOfHom g).obj (op U)),
      (∀ a, X.toLocallyRingedSpace.presheaf.germ U x hxU (fU a).1 = (f a).1) ∧
        IsKoszulSequenceExactOn X.toRingedSpace U (fun a => (fU a).1) (fun k => 0 < k) ∧
          IsGeneratedByOn X.toRingedSpace (definingIdealOfHom g) U fun a => (fU a).1 := by
  subst hx
  obtain ⟨V, hxV, n, q, hK, hgen⟩ := exists_koszulRegular_generators_near_image g hg z
  exact exists_koszulRegular_generators_of_basis_local (definingIdealOfHom g) (g z) f b hf
    (stalkIdeal_definingIdealOfHom_ne_top g z) V hxV q hK hgen

/-- The stalk of the defining ideal sheaf of a Koszul-regular immersion is finitely generated, at
a point presented as the image of a point of the source. -/
private theorem koszulRegularImmersion_stalkIdeal_fg_of_eq (g : Z ⟶ X) [IsImmersion g]
    (hg : IsKoszulRegularImmersion g) (z : Z) {x : X} (hx : g z = x) :
    (Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
      (definingIdealOfHom g) x).FG := by
  subst hx
  exact koszulRegularImmersion_stalkIdeal_fg g hg z

/-- **The tail of two adapted Koszul-regular generating families generates the ideal of `i`.**
Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions, let `x = j (i z)`, and let the ideal of `j` be
generated Koszul-regularly near `x` by `f₁, …, f_n` and the ideal of `i ≫ j` by a family whose
first `n` members have the same germs at `x` as the `f_a`. Then the images in `O_Y` of the
remaining members generate the ideal of `i` Koszul-regularly near `i z`. -/
private theorem exists_koszulRegular_tail_of_koszulRegular_families (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion j] (z : Z) {n m : ℕ} (Vf Vt : X.Opens)
    (hxVf : j (i z) ∈ Vf) (hxVt : j (i z) ∈ Vt)
    (fU : Fin n → Γ(X, Vf)) (t : Fin (n + m) → Γ(X, Vt))
    (hgerm : ∀ a : Fin n, X.toLocallyRingedSpace.presheaf.germ Vf (j (i z)) hxVf (fU a)
      = X.toLocallyRingedSpace.presheaf.germ Vt (j (i z)) hxVt (t (Fin.castAdd m a)))
    (hKf : IsKoszulSequenceExactOn X.toRingedSpace Vf fU (fun k => 0 < k))
    (hgenf : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom j) Vf fU)
    (hKt : IsKoszulSequenceExactOn X.toRingedSpace Vt t (fun k => 0 < k))
    (hgent : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom (i ≫ j)) Vt t) :
    ∃ (T : Y.Opens) (_ : i z ∈ T) (m : ℕ) (tail : Fin m → Γ(Y, T)),
      IsKoszulSequenceExactOn Y.toRingedSpace T tail (fun k => 0 < k) ∧
        IsGeneratedByOn Y.toRingedSpace (definingIdealOfHom i) T tail := by
  classical
  obtain ⟨O, hxO, hOf, hOt, hsections⟩ :=
    exists_open_map_eq_of_germ_eq (W := X.toLocallyRingedSpace) (j (i z)) Vf Vt hxVf hxVt
      fU (fun a => t (Fin.castAdd m a)) hgerm
  have hsplit : (fun k => X.presheaf.map (homOfLE hOt).op (t k)) =
      Fin.append (fun a => X.presheaf.map (homOfLE hOf).op (fU a))
        fun b => X.presheaf.map (homOfLE hOt).op (t (Fin.natAdd n b)) := by
    funext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · rw [Fin.append_left]
      exact (hsections a).symm
    · rw [Fin.append_right]
  have hKfO : IsKoszulSequenceExactOn X.toRingedSpace O
      (fun a => X.presheaf.map (homOfLE hOf).op (fU a)) fun k => 0 < k :=
    hKf.of_le O hOf
  have hgenfO : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom j) O
      fun a => X.presheaf.map (homOfLE hOf).op (fU a) :=
    isGeneratedByOn_of_le _ _ hgenf O hOf
  have hKtO : IsKoszulSequenceExactOn X.toRingedSpace O
      (fun k => X.presheaf.map (homOfLE hOt).op (t k)) fun k => 0 < k :=
    hKt.of_le O hOt
  have hgentO : IsGeneratedByOn X.toRingedSpace (definingIdealOfHom (i ≫ j)) O
      fun k => X.presheaf.map (homOfLE hOt).op (t k) :=
    isGeneratedByOn_of_le _ _ hgent O hOt
  rw [hsplit] at hKtO hgentO
  exact ⟨j ⁻¹ᵁ O, hxO, m, _,
    isKoszulSequenceExactOn_tail j O _ _ hgenfO hKfO hKtO,
    isGeneratedByOn_tail_of_comp i j O _ _ hgenfO hgentO⟩

/-- **A Koszul-regular family generating the ideal of `i` near a point.** For immersions whose
conormal sequence is exact and locally split, with `j` and `i ≫ j` Koszul-regular, the ideal of `i`
is generated near every point of `Z` by a Koszul-regular family of sections of `O_Y`. -/
private theorem exists_koszulRegular_tail_near_image (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i]
    [IsImmersion j] [LocallyOfFinitePresentation j] (hS : IsSplitExactConormalSequence i j)
    (hj : IsKoszulRegularImmersion j) (hij : IsKoszulRegularImmersion (i ≫ j)) (z : Z) :
    ∃ (T : Y.Opens) (_ : i z ∈ T) (m : ℕ) (tail : Fin m → Γ(Y, T)),
      IsKoszulSequenceExactOn Y.toRingedSpace T tail (fun k => 0 < k) ∧
        IsGeneratedByOn Y.toRingedSpace (definingIdealOfHom i) T tail := by
  classical
  obtain ⟨U, hxU, n, m, f, g, -, -, -, hgenI, hfI, hfJ, hgJ, bI, bJ, hbI, hbJl, hbJr⟩ :=
    exists_adapted_local_generators i j hS z (koszulRegularImmersion_stalkIdeal_fg (i ≫ j) hij z)
  obtain ⟨Vf, hxVf, fU, hfU, hKf, hgenf⟩ :=
    exists_koszulRegular_generators_of_koszulRegularImmersion j hj (i z) rfl
      (fun a => ⟨X.presheaf.germ U (j (i z)) hxU (f a), hfI a⟩) bI hbI
  have hbJ' : ∀ k, (bJ.reindex (finSumFinEquiv (m := n) (n := m))) k =
      Submodule.Quotient.mk ((Sum.elim
        (fun a => (⟨X.presheaf.germ U (j (i z)) hxU (f a), hfJ a⟩ :
          Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
            (definingIdealOfHom (i ≫ j)) (j (i z))))
        fun b => ⟨X.presheaf.germ U (j (i z)) hxU (g b), hgJ b⟩)
          (finSumFinEquiv.symm k)) := by
    intro k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd]
      exact hbJl a
    · rw [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd]
      exact hbJr b
  obtain ⟨Vt, hxVt, t, ht, hKt, hgent⟩ :=
    exists_koszulRegular_generators_of_koszulRegularImmersion (i ≫ j) hij z (x := j (i z)) rfl
      (fun k => Sum.elim
        (fun a => (⟨X.presheaf.germ U (j (i z)) hxU (f a), hfJ a⟩ :
          Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
            (definingIdealOfHom (i ≫ j)) (j (i z))))
        (fun b => ⟨X.presheaf.germ U (j (i z)) hxU (g b), hgJ b⟩) (finSumFinEquiv.symm k))
      (bJ.reindex (finSumFinEquiv (m := n) (n := m))) hbJ'
  refine exists_koszulRegular_tail_of_koszulRegular_families i j z Vf Vt hxVf hxVt
    (fun a => (fU a).1) (fun k => (t k).1) (fun a => ?_) hKf hgenf hKt hgent
  rw [hfU a, ht (Fin.castAdd m a), finSumFinEquiv_symm_apply_castAdd]
  rfl

end Tail

/-- **Koszul-regular generating families near every point make an immersion Koszul-regular.**
This is the assembly step shared by the three forms of part (3) of [Stacks Project, Tag 068Z]:
off the closed range of the closed factor of `i` the ideal is the unit ideal, so the one-member
family `1` works there. -/
private theorem isKoszulRegularImmersion_of_exists_tail (i : Z ⟶ Y) [IsImmersion i]
    (htail : ∀ z : Z, ∃ (T : Y.Opens) (_ : i z ∈ T) (m : ℕ) (tail : Fin m → Γ(Y, T)),
      IsKoszulSequenceExactOn Y.toRingedSpace T tail (fun k => 0 < k) ∧
        IsGeneratedByOn Y.toRingedSpace (definingIdealOfHom i) T tail) :
    IsKoszulRegularImmersion i := by
  classical
  have hJ : idealRestriction i.coborderRange.ι (definingIdealOfHom i) =
      definingIdealOfHom i.liftCoborder := by
    rw [show definingIdealOfHom i =
      definingIdealOfHom (i.liftCoborder ≫ i.coborderRange.ι) from
        (congrArg definingIdealOfHom i.liftCoborder_ι).symm]
    exact definingIdealOfHom_comp_open i.liftCoborder i.coborderRange.ι
  intro x _
  by_cases hrange : x ∈ Set.range i.liftCoborder.base
  · obtain ⟨z, rfl⟩ := hrange
    obtain ⟨T, hyT, m, tail, hK, hgen⟩ := htail z
    have hpt : i.coborderRange.ι (i.liftCoborder z) = i z := by
      rw [← Scheme.Hom.comp_apply, i.liftCoborder_ι]
    have hxO : i.liftCoborder z ∈ i.coborderRange.ι ⁻¹ᵁ T := by
      change i.coborderRange.ι (i.liftCoborder z) ∈ T
      rw [hpt]
      exact hyT
    have hgenO := isGeneratedByOn_restriction i.coborderRange.ι (definingIdealOfHom i) T tail hgen
    rw [hJ] at hgenO
    exact ⟨i.coborderRange.ι ⁻¹ᵁ T, hxO, m, fun b => i.coborderRange.ι.app T (tail b),
      isKoszulSequenceExactOn_preimage i.coborderRange.ι T tail hK, hgenO⟩
  · have hspan : ∀ (y : i.coborderRange.toScheme) (hy : y ∈ (⟨(Set.range i.liftCoborder.base)ᶜ,
        i.liftCoborder.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
          i.coborderRange.toScheme.Opens)),
        Jid (germFamily i.coborderRange.toScheme.toRingedSpace _
          (fun _ : Fin 1 => (1 : Γ(i.coborderRange.toScheme, _))) y hy) = ⊤ :=
      fun y hy => (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨0, by simp [germFamily]⟩)
    refine ⟨⟨(Set.range i.liftCoborder.base)ᶜ,
      i.liftCoborder.isClosedEmbedding.isClosed_range.isOpen_compl⟩, hrange, 1, fun _ => 1, ?_, ?_⟩
    · refine (isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular
        i.coborderRange.toScheme.toRingedSpace _ _).mpr fun y hy => ?_
      exact koszulRegular_of_jid_eq_top _ (hspan y hy)
    · refine isGeneratedByOn_of_forall_stalkIdeal_eq (definingIdealOfHom i.liftCoborder) _
        fun y hy => ?_
      rw [hspan y hy]
      exact stalkIdeal_definingIdealOfHom_eq_top_of_notMem_range i.liftCoborder y hy

/-! ### Part (3) of Stacks tag 068Z -/

/-- **[Stacks Project, Tag 068Z], part (3).** For immersions `i : Z ⟶ Y` and `j : Y ⟶ X` with `j`
locally of finite presentation whose conormal sequence is exact and locally split, `i` is
Koszul-regular as soon as both `j` and `i ≫ j` are. -/
@[stacks 068Z "(3) Koszul-regularity of the first immersion"]
theorem isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] [LocallyOfFinitePresentation j]
    (hS : IsSplitExactConormalSequence i j) (hj : IsKoszulRegularImmersion j)
    (hij : IsKoszulRegularImmersion (i ≫ j)) :
    IsKoszulRegularImmersion i := by
  exact isKoszulRegularImmersion_of_exists_tail i fun z =>
    exists_koszulRegular_tail_near_image i j hS hj hij z

/-! ### Koszul-regularity of the first of two immersions with the second retracted -/

section Retraction

/-- **A Koszul-regular family generating the ideal of `i` near a point, for a retracted `j`.**
For immersions `i : Z ⟶ Y` and `j : Y ⟶ X` with `j` admitting a retraction and both `j` and
`i ≫ j` Koszul-regular, the ideal of `i` is generated near every point of `Z` by a Koszul-regular
family of sections of `O_Y`. -/
private theorem exists_koszulRegular_tail_of_retraction (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (ρ : X ⟶ Y) (hρ : j ≫ ρ = 𝟙 Y)
    (hj : IsKoszulRegularImmersion j) (hij : IsKoszulRegularImmersion (i ≫ j)) (z : Z) :
    ∃ (T : Y.Opens) (_ : i z ∈ T) (m : ℕ) (tail : Fin m → Γ(Y, T)),
      IsKoszulSequenceExactOn Y.toRingedSpace T tail (fun k => 0 < k) ∧
        IsGeneratedByOn Y.toRingedSpace (definingIdealOfHom i) T tail := by
  have hIJ : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
      (definingIdealOfHom j) (j (i z)) ≤
      Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z)) :=
    stalkIdeal_mono (definingIdealOfHom_le_comp i j) _
  obtain ⟨n, m, v, c, bI, bJ, hbI, hbJ, hcv⟩ :=
    exists_adapted_cotangent_bases (definingIdealOfHom j) (definingIdealOfHom (i ≫ j)) hIJ
      (koszulRegularImmersion_stalkIdeal_fg_of_eq j hj (i z) rfl)
      (koszulRegularImmersion_stalkIdeal_fg_of_eq (i ≫ j) hij z
        (x := j (i z)) rfl)
      (mk_eq_zero_of_mk_eq_zero_of_retraction i j ρ hρ z hIJ)
  obtain ⟨Vf, hxVf, fU, hfU, hKf, hgenf⟩ :=
    exists_koszulRegular_generators_of_koszulRegularImmersion j hj (i z) rfl v bI hbI
  obtain ⟨Vt, hxVt, t, ht, hKt, hgent⟩ :=
    exists_koszulRegular_generators_of_koszulRegularImmersion (i ≫ j) hij z
      (x := j (i z)) rfl c bJ hbJ
  refine exists_koszulRegular_tail_of_koszulRegular_families i j z Vf Vt hxVf hxVt
    (fun a => (fU a).1) (fun k => (t k).1) (fun a => ?_) hKf hgenf hKt hgent
  rw [hfU a, ht (Fin.castAdd m a), hcv a]

/-- **Koszul-regularity of the first of two immersions with the second retracted.** Let
`i : Z ⟶ Y` and `j : Y ⟶ X` be immersions and let `ρ : X ⟶ Y` be a retraction of `j`. If both `j`
and `i ≫ j` are Koszul-regular immersions, then so is `i`.

This is [Stacks Project, Tag 068Z] part (3) for a retracted second immersion: the retraction
`u ↦ u - ρ^♯ (j^♯ u)` of the stalk of the ideal of `j` takes the place of the splitting of the
conormal sequence, so neither exactness nor finite presentation is needed. -/
theorem isKoszulRegularImmersion_of_comp_of_retraction (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] (ρ : X ⟶ Y) (hρ : j ≫ ρ = 𝟙 Y)
    (hj : IsKoszulRegularImmersion j) (hij : IsKoszulRegularImmersion (i ≫ j)) :
    IsKoszulRegularImmersion i := by
  exact isKoszulRegularImmersion_of_exists_tail i fun z =>
    exists_koszulRegular_tail_of_retraction i j ρ hρ hj hij z

end Retraction

/-! ### Koszul-regularity of the first of two immersions from the cotangent fibres -/

section CotangentFibre

/-- **Koszul-regularity of the first of two immersions, from the cotangent fibres alone.** Let
`i : Z ⟶ Y` and `j : Y ⟶ X` be immersions, write `x = j (i z)` and let `I_x ⊆ J_x` be the stalks
at `x` of the defining ideals of `j` and of `i ≫ j`. If every element of `I_x` lying in
`𝔪_x J_x` already lies in `𝔪_x I_x`, and both `j` and `i ≫ j` are Koszul-regular, then so is `i`.

This is [Stacks Project, Tag 068Z] part (3) with its conormal hypothesis replaced by the one
consequence of it that the proof uses, namely injectivity of the map of cotangent fibres
`I_x / 𝔪_x I_x ⟶ J_x / 𝔪_x J_x`; in exchange neither exactness nor finite presentation is needed.
`Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_isSplitExactConormalSequence`
obtains the hypothesis from an exact and locally split conormal sequence and
`Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_comp_of_retraction` from a retraction of
`j`. -/
theorem isKoszulRegularImmersion_of_comp_of_mem_smul_stalkIdeal (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j]
    (hmk : ∀ z : Z, ∀ a ∈ Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom j) (j (i z)),
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (i z))) •
          Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
            (definingIdealOfHom (i ≫ j)) (j (i z)) →
        a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (j (i z))) •
          Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
            (definingIdealOfHom j) (j (i z)))
    (hj : IsKoszulRegularImmersion j) (hij : IsKoszulRegularImmersion (i ≫ j)) :
    IsKoszulRegularImmersion i := by
  refine isKoszulRegularImmersion_of_exists_tail i fun z => ?_
  have hIJ : Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
      (definingIdealOfHom j) (j (i z)) ≤
      Stacks.RingedSpace.stalkIdeal (X := X.toLocallyRingedSpace)
        (definingIdealOfHom (i ≫ j)) (j (i z)) :=
    stalkIdeal_mono (definingIdealOfHom_le_comp i j) _
  obtain ⟨n, m, v, c, bI, bJ, hbI, hbJ, hcv⟩ :=
    exists_adapted_cotangent_bases (definingIdealOfHom j) (definingIdealOfHom (i ≫ j)) hIJ
      (koszulRegularImmersion_stalkIdeal_fg_of_eq j hj (i z) rfl)
      (koszulRegularImmersion_stalkIdeal_fg_of_eq (i ≫ j) hij z (x := j (i z)) rfl)
      (fun a h0 => by
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff] at h0 ⊢
        exact hmk z _ a.2 h0)
  obtain ⟨Vf, hxVf, fU, hfU, hKf, hgenf⟩ :=
    exists_koszulRegular_generators_of_koszulRegularImmersion j hj (i z) rfl v bI hbI
  obtain ⟨Vt, hxVt, t, ht, hKt, hgent⟩ :=
    exists_koszulRegular_generators_of_koszulRegularImmersion (i ≫ j) hij z
      (x := j (i z)) rfl c bJ hbJ
  refine exists_koszulRegular_tail_of_koszulRegular_families i j z Vf Vt hxVf hxVt
    (fun a => (fU a).1) (fun k => (t k).1) (fun a => ?_) hKf hgenf hKt hgent
  rw [hfU a, ht (Fin.castAdd m a), hcv a]

end CotangentFibre

end Stacks.AlgebraicGeometry

end
