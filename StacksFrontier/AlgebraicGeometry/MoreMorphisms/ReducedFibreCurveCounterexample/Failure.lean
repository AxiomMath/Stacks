module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurveCounterexample.Points
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurveCounterexample.Ramification
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReplacement
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GenericFibrePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointGeneralizing
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.PuncturedFreeness

/-!
# The normalized base change of the counterexample is never smooth at all generic points

Let `S` be the line with infinitely many origins over a field `k` and `f : X ⟶ S` the total
space of the counterexample. For every finite extension `L` of the function field `K` of `S`,
with `T` the normalization of `S` in `Spec L`, `Y` the normalization of `X ×_S T` and
`g : Y ⟶ T` the projection, `g` fails to be smooth at some generic point of some fibre.

Take `n = [L : K]`. Over the `n`-th origin `p` the fibre of `X` contains the line `x = 0`, with
generic point `ξ` at which `t = x ^ (n + 1) y`, `y` a unit. Choose a point `b` of `T` over `p` and
a point `η` of `Y` over `ξ` and `b`; since `T ⟶ S` and `Y ⟶ X ×_S T` are integral, `η` is a generic
point of its fibre. If `g` were smooth at `η`, the local homomorphism `𝒪_{T,b} → 𝒪_{Y,η}` would be
flat with `𝔪_b 𝒪_{Y,η} = 𝔪_η` (on a chart of `Y` that is of finite type over a Noetherian base), so
`t = x ^ (n + 1) y` would force the germ of `t` into `𝔪_b ^ (n + 1)`. But the ramification of `b`
over `p` is at most `[L : K] = n`.

## Main results

* `AlgebraicGeometry.ReducedFibreCurveCounterexample.exists_not_smoothAt`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Polynomial

universe u

namespace AlgebraicGeometry.ReducedFibreCurveCounterexample

section General

/-- **The normalization of a Nagata regular curve in a finite extension of its function field is
locally Noetherian**: over an affine open with Nagata ring of sections `A` it is the spectrum of
the integral closure of the Dedekind domain `A`, a Dedekind domain. -/
theorem isLocallyNoetherian_normalization_genericExtensionHom {S : Scheme.{u}} [IsIntegral S]
    {L : Type u} [Field L] [Algebra S.functionField L] [FiniteDimensional S.functionField L]
    (hN : IsNagataScheme S) (hR : IsRegular S) (hdim : topologicalKrullDim S ≤ 1) :
    IsLocallyNoetherian (S.genericExtensionHom L).normalization := by
  classical
  choose V₀ hxV hVN using hN
  set V : S → S.Opens := fun x ↦ (V₀ x).1 with hVdef
  have hVa : ∀ x, IsAffineOpen (V x) := fun x ↦ (V₀ x).2
  have hne : ∀ x : S, Nonempty (V x) := fun x ↦ ⟨⟨x, hxV x⟩⟩
  have hded : ∀ x : S, IsDedekindDomain Γ(S, V x) := fun x ↦
    isDedekindDomain_sections_of_isRegular hR hdim _ (hVa x)
  have hψ : ∀ x : S, let : Algebra Γ(S, V x) L :=
      ((algebraMap S.functionField L).comp (algebraMap Γ(S, V x) S.functionField)).toAlgebra
      ∃ ψ : Spec (.of ↥(integralClosure Γ(S, V x) L)) ⟶ (S.genericExtensionHom L).normalization,
        IsPullback ψ (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, V x) ↥(integralClosure Γ(S, V x) L))))
          (S.genericExtensionHom L).fromNormalization (hVa x).fromSpec := fun x ↦
    Scheme.exists_isPullback_genericExtensionHom_fromNormalization (L := L) (V x) (hVa x)
  choose ψ hψ using hψ
  have : ∀ x : S, IsOpenImmersion (ψ x) := fun x ↦
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hψ x).flip inferInstance
  refine (isLocallyNoetherian_iff_openCover (Scheme.Cover.mkOfCovers S _ ψ fun b ↦ ?_)).mpr
    fun x ↦ ?_
  · obtain ⟨a, ha⟩ : (S.genericExtensionHom L).fromNormalization.base b ∈
        Set.range (hVa ((S.genericExtensionHom L).fromNormalization.base b)).fromSpec.base := by
      rw [IsAffineOpen.range_fromSpec]
      exact hxV _
    obtain ⟨c, hc, -⟩ := Scheme.exists_preimage_of_isPullback (hψ _) b a ha.symm
    exact ⟨_, c, hc⟩
  · have := hne x
    let : Algebra Γ(S, V x) L :=
      ((algebraMap S.functionField L).comp (algebraMap Γ(S, V x) S.functionField)).toAlgebra
    have := functionField_isFractionRing_of_isAffineOpen S (V x) (hVa x)
    have : IsScalarTower Γ(S, V x) S.functionField L :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have := hded x
    have : IsDedekindDomain ↥(integralClosure Γ(S, V x) L) :=
      isDedekindDomain_integralClosure_of_isNagataRing S.functionField L (hVN x)
    change IsLocallyNoetherian (Spec (.of ↥(integralClosure Γ(S, V x) L)))
    infer_instance

/-- Every point of `S` over a nonempty affine open has a point of the normalization of `S` in
`Spec L` above it. -/
theorem exists_fromNormalization_genericExtensionHom_eq {S : Scheme.{u}} [IsIntegral S]
    {L : Type u} [Field L] [Algebra S.functionField L] (U : S.Opens) (hU : IsAffineOpen U)
    [Nonempty U] (s : S) (hs : s ∈ U) :
    ∃ b : (S.genericExtensionHom L).normalization,
      (S.genericExtensionHom L).fromNormalization b = s := by
  let : Algebra Γ(S, U) L :=
    ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
  obtain ⟨ψ, hψ⟩ := Scheme.exists_isPullback_genericExtensionHom_fromNormalization (L := L) U hU
  obtain ⟨a, rfl⟩ : s ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  have hinj : Function.Injective (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L)) := by
    intro x y hxy
    have h : algebraMap S.functionField L (algebraMap Γ(S, U) S.functionField x) =
        algebraMap S.functionField L (algebraMap Γ(S, U) S.functionField y) :=
      congrArg (fun z : ↥(integralClosure Γ(S, U) L) ↦ (z : L)) hxy
    have := functionField_isFractionRing_of_isAffineOpen S U hU
    exact IsFractionRing.injective Γ(S, U) S.functionField ((algebraMap _ L).injective h)
  obtain ⟨Q, -, hQ, hQa⟩ := Ideal.exists_ideal_over_prime_of_isIntegral a.asIdeal
    (⊥ : Ideal ↥(integralClosure Γ(S, U) L)) (by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le)
  let q : Spec (.of ↥(integralClosure Γ(S, U) L)) := ⟨Q, hQ⟩
  refine ⟨ψ q, (congrArg (fun φ : Spec (.of ↥(integralClosure Γ(S, U) L)) ⟶ S ↦ φ q)
    hψ.w).trans ?_⟩
  change hU.fromSpec (Spec.map _ q) = _
  congr 1
  exact PrimeSpectrum.ext hQa

/-- A point of a scheme which is a generic point of its fibre, read in the local ring: every prime
of `𝒪_{V,x}` containing the maximal ideal of the base is the maximal ideal. -/
theorem eq_maximalIdeal_of_forall_specializes {V T : Scheme.{u}} (h : V ⟶ T) (x : V)
    (hx : ∀ a : V, a ⤳ x → h a = h x → a = x) (P : Ideal (V.presheaf.stalk x)) (hP : P.IsPrime)
    (hle : (maximalIdeal (T.presheaf.stalk (h x))).map (h.stalkMap x).hom ≤ P) :
    P = maximalIdeal (V.presheaf.stalk x) := by
  set p : Spec (V.presheaf.stalk x) := ⟨P, hP⟩
  have ha : V.fromSpecStalk x p ⤳ x := by
    have : V.fromSpecStalk x p ∈ Set.range (V.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hz : Spec.map (h.stalkMap x) p = closedPoint _ :=
    PrimeSpectrum.ext ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_isPrime _ P).ne_top
      (Ideal.map_le_iff_le_comap.mp hle)).symm
  have hha : h (V.fromSpecStalk x p) = h x := by
    have := congrArg (fun φ : Spec (V.presheaf.stalk x) ⟶ T ↦ φ p)
      (Scheme.SpecMap_stalkMap_fromSpecStalk h (x := x))
    simp only [Scheme.Hom.comp_apply] at this
    rw [← this, hz, Scheme.fromSpecStalk_closedPoint]
  have hp : p = closedPoint _ := (V.fromSpecStalk x).isEmbedding.injective
    ((hx _ ha hha).trans Scheme.fromSpecStalk_closedPoint.symm)
  exact congrArg PrimeSpectrum.asIdeal hp

/-- A point over a generic point of the fibre of `f`, along integral morphisms `p` and `q`, is a
generic point of the fibre of `p ≫ q ≫ f`. -/
theorem eq_of_specializes_of_isIntegralHom_comp {Y P X S : Scheme.{u}} (p : Y ⟶ P) (q : P ⟶ X)
    (f : X ⟶ S) [IsIntegralHom p] [IsIntegralHom q] {η a : Y}
    (hξ : ∀ w, w ⤳ q (p η) → f w = f (q (p η)) → w = q (p η)) (ha : a ⤳ η)
    (hfa : f (q (p a)) = f (q (p η))) : a = η :=
  eq_of_specializes_of_base_eq_of_isIntegralHom p ha
    (eq_of_specializes_of_base_eq_of_isIntegralHom q (ha.map p.continuous)
      (hξ _ ((ha.map p.continuous).map q.continuous) hfa))

/-- A morphism whose restriction `f.resLE ⊤ V le_top` to an open `V` is smooth gives a smooth
`V.ι ≫ f`. -/
theorem smooth_ι_comp_of_smooth_resLE {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens)
    (hV : Smooth (f.resLE ⊤ V le_top)) : Smooth (V.ι ≫ f) := by
  have hres : f.resLE ⊤ V le_top ≫ (Scheme.topIso _).hom = V.ι ≫ f := by
    simpa using Scheme.Hom.resLE_comp_ι f (U := ⊤) (V := V) le_top
  rw [← hres]
  exact MorphismProperty.comp_mem _ _ _ hV inferInstance

/-- At a generic point `x` of its fibre, a smooth morphism `h` to a locally Noetherian scheme has
`𝔪_{h x} 𝒪_{V,x} = 𝔪_x`, so an element of `𝔪_{h x}` mapping to `a ^ n * c` with `c` a unit lies in
`𝔪_{h x} ^ n`. -/
theorem mem_maximalIdeal_pow_of_smooth_of_forall_specializes {V T : Scheme.{u}} (h : V ⟶ T)
    [Smooth h] [IsLocallyNoetherian T] (x : V) (hx : ∀ a : V, a ⤳ x → h a = h x → a = x)
    {t : T.presheaf.stalk (h x)} (ht : t ∈ maximalIdeal _) (n : ℕ) {a c : V.presheaf.stalk x}
    (hac : h.stalkMap x t = a ^ n * c) (hc : IsUnit c) :
    t ∈ maximalIdeal (T.presheaf.stalk (h x)) ^ n := by
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian h
  let : Algebra (T.presheaf.stalk (h x)) (V.presheaf.stalk x) := (h.stalkMap x).hom.toAlgebra
  have : Algebra.FormallySmooth (T.presheaf.stalk (h x)) (V.presheaf.stalk x) :=
    InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap h x
      (InfinitesimalLifting.smoothAt_of_smooth h x)
  have : IsLocalHom (algebraMap (T.presheaf.stalk (h x)) (V.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap x).hom)
  have : Module.Flat (T.presheaf.stalk (h x)) (V.presheaf.stalk x) := Flat.stalkMap h x
  exact mem_maximalIdeal_pow_of_map_maximalIdeal_eq (map_maximalIdeal_eq_of_formallySmooth
    fun P hP hle ↦ eq_maximalIdeal_of_forall_specializes h x hx P hP hle) ht hc n hac

end General

variable (k : Type u) [Field k]

/-- The `n`-th origin is the point of the `n`-th chart where its coordinate vanishes. -/
theorem primeIdealOf_origin (n : ℕ) :
    ((isAffineOpen_baseChart k n).primeIdealOf ⟨baseι k n (origin k), mem_baseChart k n _⟩) =
      ⟨Ideal.span {baseCoord k n}, (isMaximal_span_baseCoord k n).isPrime⟩ := by
  apply PrimeSpectrum.ext
  have hτ : baseCoord k n ∈ ((isAffineOpen_baseChart k n).primeIdealOf
      ⟨baseι k n (origin k), mem_baseChart k n _⟩).asIdeal := by
    by_contra h
    exact origin_notMem_basicOpen_baseCoord k n
      (((isAffineOpen_baseChart k n).notMem_primeIdealOf_iff_mem_basicOpen _ _).mp h)
  exact ((isMaximal_span_baseCoord k n).eq_of_le (PrimeSpectrum.isPrime _).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hτ)).symm

/-- The coordinate of the `n`-th chart vanishes at the `n`-th origin, stated at any point equal to
it. -/
theorem germ_baseCoord_mem_maximalIdeal (n : ℕ) (s : base k) (hs : s = baseι k n (origin k))
    (hsU : s ∈ baseChart k n) :
    (base k).presheaf.germ _ s hsU (baseCoord k n) ∈ maximalIdeal _ := by
  subst hs
  rw [mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen _ _ _ hsU]
  exact origin_notMem_basicOpen_baseCoord k n

/-- The pullback of the coordinate of the `n`-th chart vanishes at any point over the `n`-th
origin. -/
theorem germ_app_baseCoord_mem_maximalIdeal {T : Scheme.{u}} (ν : T ⟶ base k) (n : ℕ) (b : T)
    (hb : ν b = baseι k n (origin k)) (hbU : b ∈ ν ⁻¹ᵁ baseChart k n) :
    T.presheaf.germ _ b hbU (ν.app _ (baseCoord k n)) ∈ maximalIdeal _ := by
  have hbU' : ν b ∈ baseChart k n := hbU
  have h₁ : ν.stalkMap b ((base k).presheaf.germ _ (ν b) hbU' (baseCoord k n)) ∈
      maximalIdeal _ := map_nonunit (ν.stalkMap b).hom _
    (germ_baseCoord_mem_maximalIdeal k n _ hb hbU')
  rwa [Scheme.Hom.germ_stalkMap_apply] at h₁

/-- A point over the `n`-th origin lies in the preimage of the `n`-th chart. -/
private theorem mem_preimage_baseChart_of_eq_origin {T : Scheme.{u}} (ν : T ⟶ base k) (n : ℕ)
    (b : T) (hb : ν b = baseι k n (origin k)) : b ∈ ν ⁻¹ᵁ baseChart k n := by
  change ν b ∈ baseChart k n
  rw [hb]
  exact mem_baseChart k n _

/-- Two factorizations `h ≫ ν = m ≫ totalMap k` carry the coordinate of the `n`-th chart to the
same germ. -/
theorem stalkMap_germ_app_baseCoord_eq {V T : Scheme.{u}} (h : V ⟶ T) (ν : T ⟶ base k)
    (m : V ⟶ total k) (hsq : h ≫ ν = m ≫ totalMap k) (n : ℕ) (x : V)
    (hbU : h x ∈ ν ⁻¹ᵁ baseChart k n) (hmU : m x ∈ totalMap k ⁻¹ᵁ baseChart k n) :
    h.stalkMap x (T.presheaf.germ _ (h x) hbU (ν.app _ (baseCoord k n))) =
      m.stalkMap x ((total k).presheaf.germ _ (m x) hmU ((totalMap k).app _ (baseCoord k n))) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
  have key : ∀ (F G : V ⟶ base k) (_ : F = G) (hF : x ∈ F ⁻¹ᵁ baseChart k n)
      (hG : x ∈ G ⁻¹ᵁ baseChart k n), V.presheaf.germ _ x hF (F.app _ (baseCoord k n)) =
        V.presheaf.germ _ x hG (G.app _ (baseCoord k n)) := by
    rintro F G rfl hF hG
    rfl
  exact key (h ≫ ν) (m ≫ totalMap k) hsq _ _

/-- If `h ≫ ν = m ≫ totalMap k` with `h` smooth over a locally Noetherian base and `x` a generic
point of its fibre with `m x` the generic point of the line `x = 0` over the `n`-th origin, then
the germ of the `n`-th coordinate at `h x` lies in `𝔪 ^ (n + 1)`. -/
theorem germ_app_baseCoord_mem_maximalIdeal_pow {V T : Scheme.{u}} (h : V ⟶ T) [Smooth h]
    [IsLocallyNoetherian T] (ν : T ⟶ base k) (m : V ⟶ total k) (hsq : h ≫ ν = m ≫ totalMap k)
    (n : ℕ) (x : V) (hx : ∀ a : V, a ⤳ x → h a = h x → a = x)
    (hmx : m x = totalι k n (specialPoint0 k)) (hνx : ν (h x) = baseι k n (origin k))
    (hbU : h x ∈ ν ⁻¹ᵁ baseChart k n) :
    T.presheaf.germ _ (h x) hbU (ν.app _ (baseCoord k n)) ∈ maximalIdeal _ ^ (n + 1) := by
  have hmU := mem_preimage_baseChart_of_eq_origin k (totalMap k) n (m x)
    (by rw [hmx, totalMap_specialPoint])
  obtain ⟨a, c, -, hc, hac⟩ := exists_germ_totalMap_baseCoord k n (m x) hmx hmU
  refine mem_maximalIdeal_pow_of_smooth_of_forall_specializes h x hx
    (germ_app_baseCoord_mem_maximalIdeal k ν n (h x) hνx hbU) (n + 1) (a := m.stalkMap x a)
    (c := m.stalkMap x c) ?_ (hc.map _)
  rw [stalkMap_germ_app_baseCoord_eq k h ν m hsq n x hbU hmU, hac, map_mul, map_pow]

/-- **The counterexample fails the conclusion of Tag 0BRQ for every finite extension.** For every
finite extension `L` of the function field of the line with infinitely many origins, the
normalization of the base change of the total space to the normalization of the base in `Spec L`
fails to be smooth at some generic point of some fibre. -/
theorem exists_not_smoothAt (L : Type u) [Field L] [Algebra (base k).functionField L]
    [FiniteDimensional (base k).functionField L]
    (hW : ∀ V : (pullback (totalMap k) ((base k).genericExtensionHom L).fromNormalization :
        Scheme.{u}).Opens,
      IsCompact (V : Set (pullback (totalMap k) ((base k).genericExtensionHom L).fromNormalization :
        Scheme.{u})) → (irreducibleComponents V).Finite) :
    ∃ (b : ((base k).genericExtensionHom L).normalization)
      (y : (Scheme.normalization _ hW ≫
        pullback.snd (totalMap k) ((base k).genericExtensionHom L).fromNormalization).fiber b),
      y ∈ genericPoints ↥((Scheme.normalization _ hW ≫
        pullback.snd (totalMap k) ((base k).genericExtensionHom L).fromNormalization).fiber b) ∧
      ¬ InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫
          pullback.snd (totalMap k) ((base k).genericExtensionHom L).fromNormalization)
        ((Scheme.normalization _ hW ≫
          pullback.snd (totalMap k) ((base k).genericExtensionHom L).fromNormalization).fiberι b
            y) := by
  classical
  set n := Module.finrank (base k).functionField L
  set ν := ((base k).genericExtensionHom L).fromNormalization
  set g := Scheme.normalization _ hW ≫ pullback.snd (totalMap k) ν with hg
  have hU := isAffineOpen_baseChart k n
  have : Nonempty (baseChart k n) := ⟨⟨_, mem_baseChart k n (origin k)⟩⟩
  obtain ⟨b, hb⟩ := exists_fromNormalization_genericExtensionHom_eq (L := L) (baseChart k n) hU
    (baseι k n (origin k)) (mem_baseChart k n _)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := totalMap k) (g := ν)
    (totalι k n (specialPoint0 k)) b (by rw [totalMap_specialPoint, hb])
  obtain ⟨η, hη⟩ := (Scheme.normalization _ hW).surjective z
  have hgη : g η = b := by rw [hg, Scheme.Hom.comp_apply, hη, hz2]
  have hfst : pullback.fst (totalMap k) ν (Scheme.normalization _ hW η) =
      totalι k n (specialPoint0 k) := by rw [hη, hz1]
  have hgen : ∀ a, a ⤳ η → g a = g η → a = η := fun a ha hga ↦
    eq_of_specializes_of_isIntegralHom_comp (Scheme.normalization _ hW)
      (pullback.fst (totalMap k) ν) (totalMap k)
      (by rw [hfst]; exact eq_specialPoint_of_specializes k n) ha (by
        have hsnd : pullback.snd (totalMap k) ν (Scheme.normalization _ hW a) = b := by
          rw [← Scheme.Hom.comp_apply, ← hg, hga, hgη]
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hsnd, hfst, hb,
          totalMap_specialPoint])
  refine ⟨g η, g.asFiber η, (mem_genericPoints_asFiber_iff g η).mpr hgen, ?_⟩
  rw [g.fiberι_asFiber]
  rintro ⟨V, hηV, hVsm⟩
  have hsm : Smooth (V.ι ≫ g) := smooth_ι_comp_of_smooth_resLE g V hVsm
  set Vs : Scheme.{u} := Scheme.Opens.toScheme V
  set h : Vs ⟶ _ := V.ι ≫ g with hh
  set x : Vs := ⟨η, hηV⟩
  have : IsLocallyNoetherian ((base k).genericExtensionHom L).normalization :=
    isLocallyNoetherian_normalization_genericExtensionHom (isNagataScheme_base k)
      (isRegular_base k) (topologicalKrullDim_base k).le
  have hνx : ν (h x) = baseι k n (origin k) := by rw [show h x = b from hgη, hb]
  have hbU := mem_preimage_baseChart_of_eq_origin k ν n (h x) hνx
  set m : Vs ⟶ total k := V.ι ≫ Scheme.normalization _ hW ≫ pullback.fst (totalMap k) ν
    with hmdef
  have hmx : m x = totalι k n (specialPoint0 k) := hfst
  have hsq : h ≫ ν = m ≫ totalMap k := by
    simp only [hh, hmdef, hg, Category.assoc, pullback.condition]
  exact germ_notMem_maximalIdeal_pow (L := L) (baseChart k n) hU
    (isDedekindDomain_sections_of_isRegular (isRegular_base k) (topologicalKrullDim_base k).le _ hU)
    (isNagataRing_baseChart k n) (baseCoord_ne_zero k n) (isMaximal_span_baseCoord k n) (h x) hbU
    (germ_app_baseCoord_mem_maximalIdeal k ν n (h x) hνx hbU)
    (germ_app_baseCoord_mem_maximalIdeal_pow k h ν m hsq n x
      (fun a ha hha ↦ Subtype.ext (hgen a.1 (ha.map V.ι.continuous) hha)) hmx hνx hbU)

end AlgebraicGeometry.ReducedFibreCurveCounterexample
