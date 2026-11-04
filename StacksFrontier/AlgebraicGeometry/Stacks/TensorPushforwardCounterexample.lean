module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Sheaves.CommRingCat
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Basic

/-!
# Stacks 0GRN fails as printed: the scheme-level counterexample

**Stacks 0GRN** asserts that for `a : 𝒴 → 𝒳` and `b : 𝒵 → 𝒳` representable by schemes,
quasi-compact, quasi-separated and flat, the canonical map

`a_{QCoh,*}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh,*}𝒪_𝒵 → f_{QCoh,*}𝒪_{𝒴 ×_𝒳 𝒵}`

is an isomorphism. This is false already for schemes. Let `k` be a field,

`A = k[x, y, z, w] / (xy - zw)`, `X = Spec A`, `V = D(x) ∪ D(z) ⊆ X`,

and let `a = b : V → X` be the open immersion; it is representable, quasi-compact,
quasi-separated and flat. Since `V ×_X V = V` and `X` is affine, the canonical map is the
multiplication `Γ(V, 𝒪) ⊗_A Γ(V, 𝒪) → Γ(V, 𝒪)`, and this is not injective.

The reason: on `V` the function `t = w / x = y / z` is regular, and
`V ≅ 𝔸³ ∖ {x = z = 0}` with coordinates `x, z, t` (`y = zt`, `w = xt`), so
`Γ(V, 𝒪) = k[x, z, t]`, of depth `2` along the line removed, while `A → k[x, z, t]` is not
flat: `k[x, z, t] ⊗_A k[x, z, t] = k[x, z, t, t'] / (x(t - t'), z(t - t'))`, and `t ⊗ 1 - 1 ⊗ t`
is a nonzero element of the kernel of the multiplication. In the source's proof the Künneth
formula (**Lemma 0FLQ**) gives `Rf_*𝒪 = Ra_*𝒪 ⊗^𝐋 Rb_*𝒪`, and the last step reads off `H⁰` of
the right hand side as `a_*𝒪 ⊗ b_*𝒪`; that fails because `H¹(V, 𝒪) ≠ 0` and `Γ(V, 𝒪)` is not
flat over `A`.

The nonzero kernel element is detected by two `A`-algebra maps `Γ(V, 𝒪) → k` which take
different values on `t`: both lie over the origin of `X`, which is not in `V`, and they are
evaluation at the points `(0, 0, 0)` and `(0, 0, 1)` of the line `x = z = 0` of `𝔸³`, which is
not in `V` either, of the pullback along `𝔸³ → Spec A`. They exist because every function on
`𝔸³ ∖ {x = z = 0}` is a polynomial (`Stacks.PicardUFD.algebraMap_bijective_two_basicOpens`).
The identification `Γ(V, 𝒪) = k[x, z, t]` itself (that `𝔸³ → Spec A` is an isomorphism over `V`)
is not needed for the counterexample and is not proved here.

## Main definitions

* `AlgebraicGeometry.TensorPushforwardCounterexample.coneRing`: the ring `A`.
* `AlgebraicGeometry.TensorPushforwardCounterexample.coneOpen`: the open `V = D(x) ∪ D(z)` of
  `Spec A`.
* `AlgebraicGeometry.TensorPushforwardCounterexample.ratioSection`: the section `t` of `𝒪` over
  `V`, equal to `w / x` on `D(x)` and to `y / z` on `D(z)`.

## Main results

* `AlgebraicGeometry.TensorPushforwardCounterexample.lmul'_ratioSection_tmul_sub`: the element
  `t ⊗ 1 - 1 ⊗ t` of `Γ(V, 𝒪) ⊗_A Γ(V, 𝒪)` is killed by the multiplication.
* `AlgebraicGeometry.TensorPushforwardCounterexample.ratioSection_tmul_sub_ne_zero`: it is
  nonzero.
* `AlgebraicGeometry.TensorPushforwardCounterexample.not_injective_lmul'_coneSections`: hence the
  multiplication `Γ(V, 𝒪) ⊗_A Γ(V, 𝒪) → Γ(V, 𝒪)` is not injective.

General lemmas used on the way:

* `AlgebraicGeometry.TensorPushforwardCounterexample.SpecMap_appLE_algebraMap`: `Spec.map φ` on
  sections carries `algebraMap R` to `algebraMap S ∘ φ`.
* `AlgebraicGeometry.TensorPushforwardCounterexample.sectionsMap`: `Spec.map φ` on sections,
  typed with the sections of `Spec.structureSheaf`, with `sectionsMap_algebraMap` and
  `sectionsMap_restrict`.
* `AlgebraicGeometry.TensorPushforwardCounterexample.exists_section_basicOpen_sup`: a pair of
  fractions `a / f` on `D(f)` and `b / g` on `D(g)` with `ga = fb` glues to a section over
  `D(f) ∪ D(g)`.

## References

* [Stacks Project, Tag 0GRN](https://stacks.math.columbia.edu/tag/0GRN)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial TopologicalSpace Opposite TensorProduct

universe u

namespace AlgebraicGeometry.TensorPushforwardCounterexample

/-! ### Two general facts about sections of the structure sheaf of a spectrum -/

/-- For a ring map `φ : R ⟶ S`, the map `Spec.map φ` on sections carries `algebraMap R` to
`algebraMap S ∘ φ`. -/
lemma SpecMap_appLE_algebraMap {R S : CommRingCat.{u}} (φ : R ⟶ S) (U : (Spec R).Opens)
    (V : (Spec S).Opens) (e : V ≤ Spec.map φ ⁻¹ᵁ U) (r : R) :
    (Spec.map φ).appLE U V e (algebraMap R Γ(Spec R, U) r) =
      algebraMap S Γ(Spec S, V) (φ r) := by
  have h : (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map (homOfLE le_top).op ≫
      (Spec.map φ).appLE U V e =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫ (Spec S).presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE, Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  exact congr(($h).hom r)

/-- The map `Spec.map φ` on sections of the structure sheaves, from `U ⊆ Spec R` to
`V ⊆ Spec S` with `V ⊆ (Spec φ)⁻¹ U`, typed with the sections of `Spec.structureSheaf`. -/
def sectionsMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (U : Opens (PrimeSpectrum R)) (V : Opens (PrimeSpectrum S))
    (e : V ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U) :
    (Spec.structureSheaf R).obj.obj (op U) →+* (Spec.structureSheaf S).obj.obj (op V) :=
  ((Spec.map (CommRingCat.ofHom φ)).appLE U V e).hom

/-- `sectionsMap φ` carries `algebraMap R r` to `algebraMap S (φ r)`. -/
lemma sectionsMap_algebraMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (U : Opens (PrimeSpectrum R)) (V : Opens (PrimeSpectrum S))
    (e : V ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U) (r : R) :
    sectionsMap φ U V e (algebraMap R _ r) = algebraMap S _ (φ r) :=
  SpecMap_appLE_algebraMap (CommRingCat.ofHom φ) U V e r

/-- `sectionsMap` commutes with restriction. -/
lemma sectionsMap_restrict {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {U U' : Opens (PrimeSpectrum R)} {V V' : Opens (PrimeSpectrum S)}
    (e : V ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U)
    (e' : V' ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U') (hU : U' ≤ U) (hV : V' ≤ V)
    (s : (Spec.structureSheaf R).obj.obj (op U)) :
    (Spec.structureSheaf S).obj.map (homOfLE hV).op (sectionsMap φ U V e s) =
      sectionsMap φ U' V' e' ((Spec.structureSheaf R).obj.map (homOfLE hU).op s) :=
  congr(($((Scheme.Hom.appLE_map (Spec.map (CommRingCat.ofHom φ)) e (homOfLE hV).op).trans
    (Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom φ)) e' (homOfLE hU).op).symm)).hom s)

/-- A pair of fractions `a / f` on `D(f)` and `b / g` on `D(g)` with `g a = f b` glues to a
section of the structure sheaf of `Spec R` over `D(f) ∪ D(g)`. -/
lemma exists_section_basicOpen_sup {R : Type u} [CommRing R] (f g a b : R) (h : g * a = f * b) :
    ∃ s : (Spec.structureSheaf R).obj.obj
        (op (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g)),
      (Spec.structureSheaf R).obj.map (homOfLE le_sup_left).op s *
          algebraMap R ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))) f =
        algebraMap R ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))) a ∧
      (Spec.structureSheaf R).obj.map (homOfLE le_sup_right).op s *
          algebraMap R ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen g))) g =
        algebraMap R ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen g))) b := by
  have hsf := IsLocalization.mk'_spec ((Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen f))) a (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)
  have hsg := IsLocalization.mk'_spec ((Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen g))) b (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)
  set sf := IsLocalization.mk' ((Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen f))) a (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)
  set sg := IsLocalization.mk' ((Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen g))) b (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)
  have hf := IsLocalization.Away.algebraMap_isUnit (S := (Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen f))) f
  have hg := IsLocalization.Away.algebraMap_isUnit (S := (Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen g))) g
  set ρf := (Spec.structureSheaf R).obj.map
    (homOfLE inf_le_left : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g ⟶ _).op
  set ρg := (Spec.structureSheaf R).obj.map
    (homOfLE inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g ⟶ _).op
  have huf := hf.map ρf.hom
  have hug := hg.map ρg.hom
  have h1 := congrArg ρf.hom hsf
  have h2 := congrArg ρg.hom hsg
  rw [map_mul] at h1 h2
  change ρf sf * algebraMap R _ f = algebraMap R _ a at h1
  change ρg sg * algebraMap R _ g = algebraMap R _ b at h2
  change IsUnit (algebraMap R ((Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g))) f) at huf
  change IsUnit (algebraMap R ((Spec.structureSheaf R).obj.obj
    (op (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g))) g) at hug
  have heq : ρf sf = ρg sg := by
    refine ((huf.mul hug).mul_left_inj).mp ?_
    calc ρf sf * (algebraMap R _ f * algebraMap R _ g)
        = (ρf sf * algebraMap R _ f) * algebraMap R _ g := by ring
      _ = algebraMap R _ (g * a) := by rw [h1, ← map_mul, mul_comm]
      _ = algebraMap R _ (f * b) := by rw [h]
      _ = (ρg sg * algebraMap R _ g) * algebraMap R _ f := by rw [h2, ← map_mul, mul_comm]
      _ = ρg sg * (algebraMap R _ f * algebraMap R _ g) := by ring
  refine ⟨((Spec.structureSheaf R).objSupIsoProdEqLocus _ _).inv ⟨(sf, sg), heq⟩, ?_, ?_⟩
  · rwa [TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst]
  · rwa [TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd]

/-! ### The ring `A = k[x, y, z, w] / (xy - zw)` and the open `V = D(x) ∪ D(z)` -/

variable (k : Type u) [Field k]

/-- The relation `xy - zw` in `k[x, y, z, w]`, the variables indexed `0, 1, 2, 3`. -/
def coneRelation : MvPolynomial (Fin 4) k := X 0 * X 1 - X 2 * X 3

/-- The ring `A = k[x, y, z, w] / (xy - zw)`. -/
abbrev coneRing : Type u := MvPolynomial (Fin 4) k ⧸ Ideal.span {coneRelation k}

/-- The coordinate function `x` of `A`. -/
abbrev coneX : coneRing k := Ideal.Quotient.mk _ (X 0)

/-- The coordinate function `y` of `A`. -/
abbrev coneY : coneRing k := Ideal.Quotient.mk _ (X 1)

/-- The coordinate function `z` of `A`. -/
abbrev coneZ : coneRing k := Ideal.Quotient.mk _ (X 2)

/-- The coordinate function `w` of `A`. -/
abbrev coneW : coneRing k := Ideal.Quotient.mk _ (X 3)

/-- In `A`, `zw = xy`. -/
lemma coneZ_mul_coneW : coneZ k * coneW k = coneX k * coneY k := by
  rw [← map_mul, ← map_mul, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- The open `V = D(x) ∪ D(z)` of `Spec A`. -/
def coneOpen : Opens (PrimeSpectrum (coneRing k)) :=
  PrimeSpectrum.basicOpen (coneX k) ⊔ PrimeSpectrum.basicOpen (coneZ k)

/-- The ring `Γ(V, 𝒪)` of functions on `V = D(x) ∪ D(z) ⊆ Spec A`, an `A`-algebra. -/
abbrev coneSections : Type u := (Spec.structureSheaf (coneRing k)).obj.obj (op (coneOpen k))

/-- The section `t` of `𝒪` over `V`, equal to `w / x` on `D(x)` and to `y / z` on `D(z)`. -/
def ratioSection : coneSections k :=
  (exists_section_basicOpen_sup (coneX k) (coneZ k) (coneW k) (coneY k)
    (coneZ_mul_coneW k)).choose

/-- On `D(x)` the section `t` satisfies `t x = w`, and on `D(z)` it satisfies `t z = y`. -/
lemma ratioSection_spec :
    (Spec.structureSheaf (coneRing k)).obj.map (homOfLE le_sup_left).op (ratioSection k) *
          algebraMap (coneRing k) ((Spec.structureSheaf (coneRing k)).obj.obj
            (op (PrimeSpectrum.basicOpen (coneX k)))) (coneX k) =
        algebraMap (coneRing k) ((Spec.structureSheaf (coneRing k)).obj.obj
            (op (PrimeSpectrum.basicOpen (coneX k)))) (coneW k) ∧
      (Spec.structureSheaf (coneRing k)).obj.map (homOfLE le_sup_right).op (ratioSection k) *
          algebraMap (coneRing k) ((Spec.structureSheaf (coneRing k)).obj.obj
            (op (PrimeSpectrum.basicOpen (coneZ k)))) (coneZ k) =
        algebraMap (coneRing k) ((Spec.structureSheaf (coneRing k)).obj.obj
            (op (PrimeSpectrum.basicOpen (coneZ k)))) (coneY k) :=
  (exists_section_basicOpen_sup (coneX k) (coneZ k) (coneW k) (coneY k)
    (coneZ_mul_coneW k)).choose_spec

/-! ### The comparison with `𝔸³` -/

/-- The ring map `A → k[x, z, t]`, `x ↦ x`, `y ↦ zt`, `z ↦ z`, `w ↦ xt`; the variables of
`k[x, z, t]` are indexed `0, 1, 2`. -/
def toAffineSpace : coneRing k →+* MvPolynomial (Fin 3) k :=
  Ideal.Quotient.lift _ (aeval ![X 0, X 1 * X 2, X 1, X 0 * X 2]).toRingHom (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hrel : aeval ![(X 0 : MvPolynomial (Fin 3) k), X 1 * X 2, X 1, X 0 * X 2]
        (coneRelation k) = 0 := by
      simp [coneRelation]
      ring
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, hrel, mul_zero])

/-- `toAffineSpace` sends `x` to `x`. -/
@[simp] lemma toAffineSpace_coneX : toAffineSpace k (coneX k) = X 0 := by
  simp [toAffineSpace]

/-- `toAffineSpace` sends `y` to `zt`. -/
@[simp] lemma toAffineSpace_coneY : toAffineSpace k (coneY k) = X 1 * X 2 := by
  simp [toAffineSpace]

/-- `toAffineSpace` sends `z` to `z`. -/
@[simp] lemma toAffineSpace_coneZ : toAffineSpace k (coneZ k) = X 1 := by
  simp [toAffineSpace]

/-- `toAffineSpace` sends `w` to `xt`. -/
@[simp] lemma toAffineSpace_coneW : toAffineSpace k (coneW k) = X 0 * X 2 := by
  simp [toAffineSpace]

/-- The open `D(x) ∪ D(z)` of `𝔸³ = Spec k[x, z, t]`, the complement of the line `x = z = 0`. -/
def affineOpen : Opens (PrimeSpectrum (MvPolynomial (Fin 3) k)) :=
  PrimeSpectrum.basicOpen (X 0) ⊔ PrimeSpectrum.basicOpen (X 1)

/-- The morphism `𝔸³ → Spec A` of `toAffineSpace`. -/
abbrev affineSpaceMap : Spec (.of (MvPolynomial (Fin 3) k)) ⟶ Spec (.of (coneRing k)) :=
  Spec.map (CommRingCat.ofHom (toAffineSpace k))

/-- The open `D(x)` of `𝔸³` lies in the preimage of `D(x) ⊆ Spec A` under `affineSpaceMap`. -/
lemma basicOpen_X_zero_le :
    PrimeSpectrum.basicOpen (X 0 : MvPolynomial (Fin 3) k) ≤
      affineSpaceMap k ⁻¹ᵁ PrimeSpectrum.basicOpen (coneX k) := by
  rw [SpecMap_preimage_basicOpen]
  simp only [CommRingCat.hom_ofHom, toAffineSpace_coneX, le_refl]

/-- The open `D(z)` of `𝔸³` lies in the preimage of `D(z) ⊆ Spec A` under `affineSpaceMap`. -/
lemma basicOpen_X_one_le :
    PrimeSpectrum.basicOpen (X 1 : MvPolynomial (Fin 3) k) ≤
      affineSpaceMap k ⁻¹ᵁ PrimeSpectrum.basicOpen (coneZ k) := by
  rw [SpecMap_preimage_basicOpen]
  simp only [CommRingCat.hom_ofHom, toAffineSpace_coneZ, le_refl]

/-- The open `affineOpen` of `𝔸³` lies in the preimage of `V` under `affineSpaceMap`. -/
lemma affineOpen_le : affineOpen k ≤ affineSpaceMap k ⁻¹ᵁ coneOpen k :=
  sup_le ((basicOpen_X_zero_le k).trans (Scheme.Hom.preimage_mono _ le_sup_left))
    ((basicOpen_X_one_le k).trans (Scheme.Hom.preimage_mono _ le_sup_right))

/-- In `k[x, z, t]`, `x` does not divide `z`. -/
lemma not_X_zero_dvd_X_one : ¬ (X 0 : MvPolynomial (Fin 3) k) ∣ X 1 := by
  rintro ⟨c, hc⟩
  simpa using congrArg (eval ![0, 1, 0]) hc

/-- Every function on `𝔸³ ∖ {x = z = 0}` is a polynomial. -/
lemma algebraMap_affineOpen_bijective :
    Function.Bijective (algebraMap (MvPolynomial (Fin 3) k)
      ((Spec.structureSheaf (MvPolynomial (Fin 3) k)).obj.obj (op (affineOpen k)))) := by
  let := UniqueFactorizationMonoid.normalizationMonoid (α := MvPolynomial (Fin 3) k)
  refine Stacks.PicardUFD.algebraMap_bijective_two_basicOpens _ (X 0) (X 1)
    (X_ne_zero (R := k) (σ := Fin 3) 0) (X_ne_zero (R := k) (σ := Fin 3) 1) ?_
  intro p hp hp'
  have hassoc : Associated p (X 0) :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor p hp).associated_of_dvd
      (X_prime (σ := Fin 3) (R := k) (i := 0))
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  exact not_X_zero_dvd_X_one k
    (hassoc.symm.dvd.trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp'))

/-- The identification `k[x, z, t] ≅ Γ(𝔸³ ∖ {x = z = 0}, 𝒪)`. -/
def affineOpenEquiv : MvPolynomial (Fin 3) k ≃+*
    (Spec.structureSheaf (MvPolynomial (Fin 3) k)).obj.obj (op (affineOpen k)) :=
  RingEquiv.ofBijective (algebraMap (MvPolynomial (Fin 3) k) _)
    (algebraMap_affineOpen_bijective k)

/-- If `s * f = g` on `U'`, `f` becomes a unit on `V'`, and `c * φ f = φ g`, then the
pullback of `s` restricted to `V'` is `c`. -/
private lemma sectionsMap_restrict_eq_of_mul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {U U' : Opens (PrimeSpectrum R)} {V V' : Opens (PrimeSpectrum S)}
    (e : V ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U)
    (e' : V' ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ U') (hU : U' ≤ U) (hV : V' ≤ V)
    (s : (Spec.structureSheaf R).obj.obj (op U)) (f g : R)
    (c : S)
    (hu : IsUnit (algebraMap S ((Spec.structureSheaf S).obj.obj (op V')) (φ f)))
    (hs : (Spec.structureSheaf R).obj.map (homOfLE hU).op s *
      algebraMap R ((Spec.structureSheaf R).obj.obj (op U')) f =
        algebraMap R ((Spec.structureSheaf R).obj.obj (op U')) g)
    (hc : c * φ f = φ g) :
    (Spec.structureSheaf S).obj.map (homOfLE hV).op (sectionsMap φ U V e s) =
      algebraMap S _ c := by
  rw [sectionsMap_restrict φ e e' hU hV]
  refine hu.mul_left_inj.mp ?_
  rw [← sectionsMap_algebraMap φ U' V' e' f, ← map_mul, hs, sectionsMap_algebraMap, ← hc,
    map_mul, sectionsMap_algebraMap]

/-- The pullback of `t` to `𝔸³ ∖ {x = z = 0}` is the coordinate `t`. -/
lemma sectionsMap_ratioSection :
    sectionsMap (toAffineSpace k) (coneOpen k) (affineOpen k) (affineOpen_le k)
        (ratioSection k) =
      algebraMap (MvPolynomial (Fin 3) k) _ (X 2) := by
  obtain ⟨hx, hz⟩ := ratioSection_spec k
  refine (Spec.structureSheaf (MvPolynomial (Fin 3) k)).eq_of_locally_eq₂
    (homOfLE le_sup_left : PrimeSpectrum.basicOpen (X 0) ⟶ affineOpen k)
    (homOfLE le_sup_right : PrimeSpectrum.basicOpen (X 1) ⟶ affineOpen k) le_rfl _ _ ?_ ?_
  · refine sectionsMap_restrict_eq_of_mul _ _ (basicOpen_X_zero_le k) _ _ _ (coneX k) (coneW k) _
      (by simpa using IsLocalization.Away.algebraMap_isUnit (X 0)) hx ?_
    rw [toAffineSpace_coneX, toAffineSpace_coneW, mul_comm]
  · refine sectionsMap_restrict_eq_of_mul _ _ (basicOpen_X_one_le k) _ _ _ (coneZ k) (coneY k) _
      (by simpa using IsLocalization.Away.algebraMap_isUnit (X 1)) hz ?_
    rw [toAffineSpace_coneZ, toAffineSpace_coneY, mul_comm]

/-! ### Two points over the origin -/

/-- The `A`-algebra structure on `k` of the origin `x = y = z = w = 0`. -/
@[instance_reducible]
def originAlgebra : Algebra (coneRing k) k :=
  ((eval ![0, 0, 0]).comp (toAffineSpace k)).toAlgebra

/-- For `a ∈ A`, the polynomial `toAffineSpace a` takes the same value at `(0, 0, c)` and at
`(0, 0, 0)`. -/
lemma eval_toAffineSpace (c : k) (a : coneRing k) :
    eval ![0, 0, c] (toAffineSpace k a) = eval ![0, 0, 0] (toAffineSpace k a) := by
  suffices h : (eval ![0, 0, c]).comp (toAffineSpace k) =
      (eval ![(0 : k), 0, 0]).comp (toAffineSpace k) from congrArg (· a) h
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · simp [toAffineSpace]
  · fin_cases i <;> simp [toAffineSpace]

/-- The `A`-algebra map `Γ(V, 𝒪) → k`, evaluation of the pullback to `𝔸³ ∖ {x = z = 0}` at the
point `(0, 0, c)` of the line removed. -/
def evalOnLine (c : k) :
    letI := originAlgebra k
    coneSections k →ₐ[coneRing k] k :=
  letI := originAlgebra k
  { toRingHom := (eval ![0, 0, c]).comp ((affineOpenEquiv k).symm.toRingHom.comp
      (sectionsMap (toAffineSpace k) (coneOpen k) (affineOpen k) (affineOpen_le k)))
    commutes' := fun a => by
      change eval ![0, 0, c] ((affineOpenEquiv k).symm
        (sectionsMap (toAffineSpace k) (coneOpen k) (affineOpen k) (affineOpen_le k)
          (algebraMap _ (coneSections k) a))) = eval ![0, 0, 0] (toAffineSpace k a)
      rw [sectionsMap_algebraMap,
        show algebraMap _ _ (toAffineSpace k a) = affineOpenEquiv k (toAffineSpace k a) from rfl,
        RingEquiv.symm_apply_apply]
      exact eval_toAffineSpace k c a }

/-- `evalOnLine c` takes the value `c` on the section `t`. -/
lemma evalOnLine_ratioSection (c : k) : evalOnLine k c (ratioSection k) = c := by
  show eval ![0, 0, c] ((affineOpenEquiv k).symm
    (sectionsMap (toAffineSpace k) (coneOpen k) (affineOpen k) (affineOpen_le k)
      (ratioSection k))) = c
  rw [sectionsMap_ratioSection,
    show algebraMap _ _ (X 2 : MvPolynomial (Fin 3) k) = affineOpenEquiv k (X 2) from rfl,
    RingEquiv.symm_apply_apply]
  simp

/-! ### The multiplication `Γ(V, 𝒪) ⊗_A Γ(V, 𝒪) → Γ(V, 𝒪)` is not injective -/

/-- `t ⊗ 1 - 1 ⊗ t` is killed by the multiplication `Γ(V, 𝒪) ⊗_A Γ(V, 𝒪) → Γ(V, 𝒪)`. -/
lemma lmul'_ratioSection_tmul_sub :
    Algebra.TensorProduct.lmul' (coneRing k)
        (ratioSection k ⊗ₜ[coneRing k] (1 : coneSections k) - 1 ⊗ₜ ratioSection k) = 0 := by
  rw [map_sub, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    mul_one, one_mul, sub_self]

/-- `t ⊗ 1 - 1 ⊗ t` is a nonzero element of `Γ(V, 𝒪) ⊗_A Γ(V, 𝒪)`: the evaluations at
`(0, 0, 0)` and `(0, 0, 1)` give it the value `-1`. -/
lemma ratioSection_tmul_sub_ne_zero :
    ratioSection k ⊗ₜ[coneRing k] (1 : coneSections k) - 1 ⊗ₜ ratioSection k ≠ 0 := by
  let := originAlgebra k
  intro h
  let L := Algebra.TensorProduct.lift (evalOnLine k 0) (evalOnLine k 1)
    (fun _ _ => mul_comm _ _)
  have h1 : L (ratioSection k ⊗ₜ[coneRing k] (1 : coneSections k)) = 0 :=
    (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans (by
      rw [evalOnLine_ratioSection, zero_mul])
  have h2 : L ((1 : coneSections k) ⊗ₜ[coneRing k] ratioSection k) = 1 :=
    (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans (by
      rw [evalOnLine_ratioSection, map_one, one_mul])
  simpa [h1, h2] using congrArg L h

/-- **Stacks 0GRN fails as printed**, at the level of schemes. For `A = k[x, y, z, w] / (xy - zw)`
and the open immersion `V = D(x) ∪ D(z) → Spec A` (representable, quasi-compact,
quasi-separated and flat), `V ×_{Spec A} V = V` and the canonical map of the tag is the
multiplication `Γ(V, 𝒪) ⊗_A Γ(V, 𝒪) → Γ(V, 𝒪)`; it is not injective. The step of the source's
proof that fails is reading `H⁰(Ra_*𝒪 ⊗^𝐋 Rb_*𝒪)` as `a_*𝒪 ⊗ b_*𝒪`: here `H¹(V, 𝒪) ≠ 0` and
`Γ(V, 𝒪) = k[x, z, t]` is not flat over `A`. -/
theorem not_injective_lmul'_coneSections :
    ¬ Function.Injective (Algebra.TensorProduct.lmul' (coneRing k) (S := coneSections k)) :=
  fun hinj => ratioSection_tmul_sub_ne_zero k (hinj (by rw [lmul'_ratioSection_tmul_sub, map_zero]))

end AlgebraicGeometry.TensorPushforwardCounterexample

end
