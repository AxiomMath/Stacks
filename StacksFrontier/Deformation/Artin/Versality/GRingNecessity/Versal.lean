module

public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.FormalObject
public import StacksFrontier.Deformation.FormalObject.VersalLifting

/-!
# Versality of the formal object of Stacks Example 98.12.8

Let `Λ` be a Noetherian ring, `𝔪 ⊂ Λ` a maximal ideal, `R = Λ_𝔪^∧`, `Λ → C → R` a
factorization with `C` of finite type, and `𝒳 = 𝒮_F` the category fibred in sets of Stacks
Example 98.12.8. This file proves that every formal object of `𝒳` whose base is `R` over
`S = Spec Λ` is versal, in particular the effective formal object `ξ` of the Example.

The mathematics is that of the Example. Every Artinian local `𝒪_{S,s}`-algebra `B` with
residue field `κ(𝔪)` receives a unique local map from `R`, because `𝔪^N B = 0` and
`R / 𝔪^N R = Λ_𝔪 / 𝔪^N`. Since `F` takes values in subsingletons, morphisms of `𝒳` are
determined by, and exist over, every morphism of their images, so a morphism out of a level of
`ξ` in the predeformation category is determined by its map of Artinian rings, and those maps
are unique. Hence every lifting problem for `ξ` is solved by the unique map `R → B'`.

## Main definitions

* `Deformation.Artin.GRingNecessity.toStalkHom`: the localization map `Λ → 𝒪_{S,s}`.
* `Deformation.Artin.GRingNecessity.formalObjectPoint`: the image `s ∈ S` of the closed point of
  the base of `ξ`.
* `Deformation.Artin.GRingNecessity.formalObjectStalkAlgebra`: the canonical `𝒪_{S,s}`-algebra
  structure on the base of `ξ`, for which `formalObjectStalkAlgebra_spec` is the compatibility
  hypothesis of Stacks 07XH.

## Main results

* `Deformation.Artin.GRingNecessity.isVersal_of_isCompletionBase`: a formal object of `𝒳` whose
  base is isomorphic over `S` to `Spec R` is versal.
* `Deformation.Artin.GRingNecessity.formalObject_isVersal`: **Stacks Example 98.12.8**, the
  formal object `ξ` is versal.

## Implementation notes

Versality is tested by the intrinsic lifting criterion of Stacks 06HS
(`Deformation.isVersal_iff_lifts_artinian`). The local ring `𝒪_{S,s}` of `S = Spec Λ` is the
stalk of the structure sheaf, a localization of `Λ`; its algebra structure on the base of the
formal object is any one compatible with the structure morphism to `S`, as in the hypothesis
of Stacks 07XH, and it is pinned down by that compatibility.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 06HS](https://stacks.math.columbia.edu/tag/06HS)
* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingNecessity

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

variable {Λ : Type u} [CommRing Λ]

/-! ### The local rings of `Spec Λ` -/

section Stalk

/-- The localization map `Λ → 𝒪_{S,s}` for `S = Spec Λ`. -/
def toStalkHom (s : Spec (.of Λ)) : Λ →+* (Spec (.of Λ)).presheaf.stalk s :=
  (StructureSheaf.toStalk Λ s).hom

/-- The canonical morphism `Spec 𝒪_{S,s} → S` is the spectrum of `Λ → 𝒪_{S,s}`. -/
theorem fromSpecStalk_eq_toStalkHom (s : Spec (.of Λ)) :
    (Spec (.of Λ)).fromSpecStalk s = Spec.map (CommRingCat.ofHom (toStalkHom s)) :=
  Spec.fromSpecStalk_eq' _ _

/-- `stalk_ringHom_ext`, stated for a point of the prime spectrum. -/
private theorem stalk_ringHom_ext_aux (s : PrimeSpectrum Λ) {X : Type*} [CommRing X]
    {f g : (Spec (.of Λ)).presheaf.stalk s →+* X}
    (h : f.comp (toStalkHom s) = g.comp (toStalkHom s)) : f = g := by
  let := (toStalkHom s).toAlgebra
  have : IsLocalization.AtPrime ((Spec (.of Λ)).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk Λ s
  exact IsLocalization.ringHom_ext s.asIdeal.primeCompl h

/-- Ring maps out of a local ring of `Spec Λ` are determined by their restriction to `Λ`. -/
theorem stalk_ringHom_ext (s : Spec (.of Λ)) {X : Type*} [CommRing X]
    {f g : (Spec (.of Λ)).presheaf.stalk s →+* X}
    (h : f.comp (toStalkHom s) = g.comp (toStalkHom s)) : f = g :=
  stalk_ringHom_ext_aux s h

end Stalk

/-! ### Complete local bases isomorphic to `Λ_𝔪^∧` over a local ring of `Spec Λ` -/

section Base

variable [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal]
  {A : FormalBase (Spec (.of Λ))} (s : Spec (.of Λ))
  [Algebra ((Spec (.of Λ)).presheaf.stalk s) A.R]

/-- A ring isomorphism is a local ring homomorphism. -/
theorem ringEquiv_map_maximalIdeal_le {R T : Type*} [CommRing R] [IsLocalRing R] [CommRing T]
    [IsLocalRing T] (σ : R ≃+* T) : (maximalIdeal R).map (σ : R →+* T) ≤ maximalIdeal T :=
  IsLocalRing.map_maximalIdeal_le (σ : R →+* T)

omit [IsNoetherianRing Λ] in
/-- The `𝒪_{S,s}`-algebra structure of a complete local base isomorphic to `Λ_𝔪^∧` restricts
to `σ ∘ (Λ → Λ_𝔪^∧)` on `Λ`. -/
theorem algebraMap_comp_toStalkHom (σ : Completion 𝔪 ≃+* A.R)
    (hσ : Spec.map (CommRingCat.ofHom ((σ : Completion 𝔪 →+* A.R).comp
      (algebraMap Λ (Completion 𝔪)))) = A.toS)
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R)) ≫
      (Spec (.of Λ)).fromSpecStalk s = A.toS) :
    (algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R).comp (toStalkHom s) =
      (σ : Completion 𝔪 →+* A.R).comp (algebraMap Λ (Completion 𝔪)) := by
  have h : Spec.map (CommRingCat.ofHom ((algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R).comp
      (toStalkHom s))) = Spec.map (CommRingCat.ofHom ((σ : Completion 𝔪 →+* A.R).comp
      (algebraMap Λ (Completion 𝔪)))) := by
    rw [hσ, ← hΛ, fromSpecStalk_eq_toStalkHom, CommRingCat.ofHom_comp, Spec.map_comp]
  simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective h)

variable {𝔪 s}

/-- Every element of a base isomorphic to `Λ_𝔪^∧` is congruent to an element of `𝒪_{S,s}`
modulo every power of the maximal ideal. -/
theorem exists_sub_mem_pow_of_completionBase (σ : Completion 𝔪 ≃+* A.R)
    (hK : (algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R).comp (toStalkHom s) =
      (σ : Completion 𝔪 →+* A.R).comp (algebraMap Λ (Completion 𝔪)))
    (n : ℕ) (r : A.R) :
    ∃ o : (Spec (.of Λ)).presheaf.stalk s,
      r - algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R o ∈ maximalIdeal A.R ^ n := by
  obtain ⟨l, hl⟩ := exists_sub_mem_pow_completion 𝔪 n (σ.symm r)
  refine ⟨toStalkHom s l, ?_⟩
  have h1 : algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R (toStalkHom s l) =
      σ (algebraMap Λ (Completion 𝔪) l) := RingHom.congr_fun hK l
  rw [h1]
  have h2 : σ (σ.symm r - algebraMap Λ (Completion 𝔪) l) ∈ maximalIdeal A.R ^ n :=
    Ideal.pow_right_mono (ringEquiv_map_maximalIdeal_le σ) n
      (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hl)
  rwa [map_sub, RingEquiv.apply_symm_apply] at h2

/-- A local ring map sends the `N`-th power of the maximal ideal into the `N`-th power of the
maximal ideal. -/
theorem map_mem_pow_of_isLocalHom {R T : Type*} [CommRing R] [IsLocalRing R] [CommRing T]
    [IsLocalRing T] (f : R →+* T) [IsLocalHom f] {x : R} {N : ℕ}
    (hx : x ∈ maximalIdeal R ^ N) : f x ∈ maximalIdeal T ^ N :=
  Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le f) N
    (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f hx)

variable (A s) in
/-- A complete local base as an object of `\widehat{𝒞}` over the local ring `𝒪_{S,s}`, with the
identity identification of its residue field. -/
abbrev baseAlgCat :
    CompleteLocalAlgCat.{u, u, u} ((Spec (.of Λ)).presheaf.stalk s) (ResidueField A.R) where
  carrier := A.R
  completeLocal := ⟨A.noetherian, A.localRing, A.complete⟩
  residueEquiv := AlgEquiv.refl

/-- The structure map of an adic truncation of a complete local algebra is surjective as soon as
every element is congruent to an element of the base ring. -/
theorem truncation_algebraMap_surjective {O k : Type u} [CommRing O] [Field k] [Algebra O k]
    (R : CompleteLocalAlgCat.{u, u, u} O k) (n : ℕ)
    (h : ∀ r : R, ∃ o : O, r - algebraMap O R o ∈ maximalIdeal R ^ (n + 1)) :
    Function.Surjective (algebraMap O ((Deformation.AdicTruncation.functor n).obj R)) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal R ^ (n + 1)) z
  obtain ⟨o, ho⟩ := h r
  refine ⟨o, ?_⟩
  change Ideal.Quotient.mk _ (algebraMap O R o) = Ideal.Quotient.mk _ r
  rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← neg_mem_iff, neg_sub]

variable (σ : Completion 𝔪 ≃+* A.R)
  (hK : (algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R).comp (toStalkHom s) =
    (σ : Completion 𝔪 →+* A.R).comp (algebraMap Λ (Completion 𝔪)))

include hK in
/-- Maps out of an adic truncation of a base isomorphic to `Λ_𝔪^∧` are unique. -/
theorem subsingleton_truncation_hom (n : ℕ)
    (D : ArtinianLocalAlgCat.{u, u, u} ((Spec (.of Λ)).presheaf.stalk s) (ResidueField A.R)) :
    Subsingleton ((Deformation.AdicTruncation.functor n).obj (baseAlgCat A s) ⟶ D) := by
  refine ⟨fun u v => ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun z => ?_)⟩
  obtain ⟨o, rfl⟩ := truncation_algebraMap_surjective (baseAlgCat A s) n
    (fun r => exists_sub_mem_pow_of_completionBase σ hK (n + 1) r) z
  rw [AlgHom.commutes, AlgHom.commutes]

include hK in
/-- Maps from a base isomorphic to `Λ_𝔪^∧` to an Artinian algebra are unique. -/
theorem subsingleton_hom_artinian
    (D : ArtinianLocalAlgCat.{u, u, u} ((Spec (.of Λ)).presheaf.stalk s) (ResidueField A.R)) :
    Subsingleton (baseAlgCat A s ⟶ Deformation.artinianToComplete.obj D) := by
  obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_eq_bot (X := D)
  refine ⟨fun u v => CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun r => ?_)⟩
  obtain ⟨o, ho⟩ := exists_sub_mem_pow_of_completionBase σ hK N r
  have key (w : baseAlgCat A s ⟶ Deformation.artinianToComplete.obj D) :
      w.hom r = w.hom (algebraMap _ A.R o) := by
    have : IsLocalHom w.hom.toRingHom := w.isLocal
    have h := map_mem_pow_of_isLocalHom w.hom.toRingHom ho
    change w.hom (r - algebraMap _ A.R o) ∈ maximalIdeal D ^ N at h
    rwa [hN, Ideal.mem_bot, map_sub, sub_eq_zero] at h
  rw [key u, key v, AlgHom.commutes, AlgHom.commutes]

include hK in
/-- The maximal ideal of an Artinian local `𝒪_{S,s}`-algebra with residue field that of a base
isomorphic to `Λ_𝔪^∧` lies over `𝔪` in `Λ`. -/
theorem comap_maximalIdeal_artinian
    (D : ArtinianLocalAlgCat.{u, u, u} ((Spec (.of Λ)).presheaf.stalk s) (ResidueField A.R)) :
    (maximalIdeal D).comap ((algebraMap ((Spec (.of Λ)).presheaf.stalk s) D).comp
      (toStalkHom s)) = 𝔪 := by
  ext l
  rw [Ideal.mem_comap, RingHom.comp_apply, ← residue_eq_zero_iff]
  have h1 : D.residueEquiv (residue D (algebraMap ((Spec (.of Λ)).presheaf.stalk s) D
      (toStalkHom s l))) = residue A.R (σ (algebraMap Λ (Completion 𝔪) l)) := by
    have h2 : residue D (algebraMap ((Spec (.of Λ)).presheaf.stalk s) D (toStalkHom s l)) =
        algebraMap ((Spec (.of Λ)).presheaf.stalk s) (ResidueField D) (toStalkHom s l) := rfl
    have h3 : σ (algebraMap Λ (Completion 𝔪) l) =
        algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R (toStalkHom s l) :=
      (RingHom.congr_fun hK l).symm
    rw [h2, AlgEquiv.commutes, h3]
    rfl
  rw [← EmbeddingLike.map_eq_zero_iff (f := D.residueEquiv), h1, residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal, ← Ideal.mem_comap, comap_maximalIdeal_completion]

include hK in
/-- **Maps from `Λ_𝔪^∧` to Artinian algebras.** A base isomorphic to `Λ_𝔪^∧` maps to every
Artinian local `𝒪_{S,s}`-algebra with the same residue field. -/
theorem nonempty_hom_artinian
    (D : ArtinianLocalAlgCat.{u, u, u} ((Spec (.of Λ)).presheaf.stalk s) (ResidueField A.R)) :
    Nonempty (baseAlgCat A s ⟶ Deformation.artinianToComplete.obj D) := by
  let : Algebra Λ D := ((algebraMap ((Spec (.of Λ)).presheaf.stalk s) D).comp
    (toStalkHom s)).toAlgebra
  obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_eq_bot (X := D)
  have hD := comap_maximalIdeal_artinian σ hK D
  let L : Completion 𝔪 →ₐ[Λ] D := completionLift 𝔪 hD N hN
  let ψ : A.R →+* D := (L : Completion 𝔪 →+* D).comp (σ.symm : A.R →+* Completion 𝔪)
  have hψ : ψ.comp (algebraMap ((Spec (.of Λ)).presheaf.stalk s) A.R) =
      algebraMap ((Spec (.of Λ)).presheaf.stalk s) D := by
    apply stalk_ringHom_ext s
    rw [RingHom.comp_assoc, hK]
    ext l
    simp only [ψ, RingHom.comp_apply, RingHom.coe_coe, RingEquiv.symm_apply_apply,
      AlgHom.commutes]
    rfl
  have hψm : ∀ x ∈ maximalIdeal A.R, ψ x ∈ maximalIdeal D := fun x hx =>
    map_maximalIdeal_completion_le 𝔪 hD L (Ideal.mem_map_of_mem L
      (ringEquiv_map_maximalIdeal_le σ.symm (Ideal.mem_map_of_mem _ hx)))
  have hloc : IsLocalHom ψ := ((IsLocalRing.local_hom_TFAE ψ).out 4 1).mp
    (show maximalIdeal A.R ≤ (maximalIdeal D).comap ψ from hψm)
  refine ⟨⟨{ ψ with commutes' := fun o => RingHom.congr_fun hψ o }, hloc, fun r => ?_⟩⟩
  obtain ⟨o, ho⟩ := exists_sub_mem_pow_of_completionBase σ hK 1 r
  rw [pow_one] at ho
  change D.residueEquiv (residue D (ψ r)) = residue A.R r
  have e1 : residue D (ψ r) = residue D (algebraMap _ D o) := by
    have h3 : algebraMap _ D o = ψ (algebraMap _ A.R o) := (RingHom.congr_fun hψ o).symm
    rw [h3]
    refine Ideal.Quotient.eq.mpr ?_
    rw [← map_sub]
    exact hψm _ ho
  have e2 : residue A.R r = residue A.R (algebraMap _ A.R o) := Ideal.Quotient.eq.mpr ho
  rw [e1, e2]
  exact D.residueEquiv.commutes o

end Base

/-! ### The predeformation categories of `𝒳` are thin -/

section Thin

variable (𝔪 : Ideal Λ) [𝔪.IsMaximal] (C : Type u) [CommRing C] [Algebra Λ C]
  (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))
  {Λ' k : Type u} [CommRing Λ'] [Field k] [Algebra Λ' k] (iΛ : Spec (.of Λ') ⟶ Spec (.of Λ))
  {x₀ : (factorizationCategory 𝔪 C B hS).val.obj}
  {hx₀ : ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ)}

/-- Solving an equation `eqToHom e₁⁻¹ ≫ X ≫ eqToHom e₂ = Y` for `X`. -/
theorem eq_of_eqToHom_comp_comp_eqToHom {𝒞 : Type*} [Category 𝒞] {a a' b b' : 𝒞}
    (e₁ : a = a') (e₂ : b = b') {X : a ⟶ b} {Y : a' ⟶ b'}
    (h : eqToHom e₁.symm ≫ X ≫ eqToHom e₂ = Y) : X = eqToHom e₁ ≫ Y ≫ eqToHom e₂.symm := by
  subst e₁ e₂
  simpa using h

/-- The morphism of schemes over `S` underlying an arrow of Artinian algebras between two
deformations. -/
def specHomOfRingHom (a b : DeformationObject iΛ
    ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) x₀ hx₀)
    (r : a.algebra ⟶ b.algebra) :
    ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).obj b.point ⟶
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).obj a.point :=
  eqToHom b.base ≫
    Over.homMk (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' b.algebra)) ≫ iΛ))
      (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' a.algebra)) ≫ iΛ))
      (Spec.map (CommRingCat.ofHom r.hom.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom r.hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ' a.algebra)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ' b.algebra)) ≫ iΛ
      have hc : (r.hom.toRingHom).comp (algebraMap Λ' a.algebra) = algebraMap Λ' b.algebra :=
        r.hom.comp_algebraMap
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]) ≫
    eqToHom a.base.symm

/-- The underlying morphism of schemes of `specHomOfRingHom` is the spectrum of the ring
map, up to the identifications of the points of the deformations. -/
theorem specHomOfRingHom_left (a b : DeformationObject iΛ
    ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) x₀ hx₀)
    (r : a.algebra ⟶ b.algebra) :
    (specHomOfRingHom 𝔪 C B hS iΛ a b r).left =
      eqToHom (congrArg Over.left b.base) ≫ Spec.map (CommRingCat.ofHom r.hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm := by
  simp [specHomOfRingHom, Over.comp_left, Over.eqToHom_left]

/-- In the predeformation category of `𝒳` there is a morphism over every map of Artinian
algebras. -/
theorem exists_deformationMorphism (a b : DeformationObject iΛ
    ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) x₀ hx₀)
    (r : a.algebra ⟶ b.algebra) :
    ∃ m : DeformationMorphism iΛ
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) x₀ hx₀ a b,
      m.ringHom = r := by
  obtain ⟨arrow, harrow, -⟩ := existsUnique_hom_of_map (specHomOfRingHom 𝔪 C B hS iΛ a b r)
  have hleft : (((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion).map
      arrow).left = eqToHom (congrArg Over.left b.base) ≫
        Spec.map (CommRingCat.ofHom r.hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm := by
    rw [harrow, specHomOfRingHom_left]
  refine ⟨⟨r, arrow, ?_, ?_⟩, rfl⟩
  · apply hom_ext_of_post
    apply Over.OverMorphism.ext
    rw [Functor.map_comp, Over.comp_left, hleft,
      eq_of_eqToHom_comp_comp_eqToHom (congrArg Over.left hx₀) (congrArg Over.left b.base)
        b.arrow_base,
      eq_of_eqToHom_comp_comp_eqToHom (congrArg Over.left hx₀) (congrArg Over.left a.base)
        a.arrow_base]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    congr 1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext z
    exact r.residue_comm z
  · rw [hleft]
    simp

/-- In the predeformation category of `𝒳` a morphism is determined by its map of Artinian
algebras. -/
theorem deformationMorphism_ext {a b : DeformationObject iΛ
    ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) x₀ hx₀}
    {m₁ m₂ : DeformationMorphism iΛ
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) x₀ hx₀ a b}
    (h : m₁.ringHom = m₂.ringHom) : m₁ = m₂ := by
  refine DeformationMorphism.ext_of_components iΛ _ x₀ hx₀ h ?_
  apply hom_ext_of_post
  apply Over.OverMorphism.ext
  rw [eq_of_eqToHom_comp_comp_eqToHom (congrArg Over.left b.base) (congrArg Over.left a.base)
      m₁.arrow_base,
    eq_of_eqToHom_comp_comp_eqToHom (congrArg Over.left b.base) (congrArg Over.left a.base)
      m₂.arrow_base, h]

attribute [local instance] PredeformationConstruction.category in
/-- **The predeformation categories of `𝒳` are thin.** The projection of a predeformation
category of `𝒳` to the category of Artinian algebras is bijective on morphisms. -/
theorem predeformation_existsUnique_map
    (𝓕 : PredeformationConstruction iΛ
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) x₀ hx₀)
    {a b : 𝓕.carrier} (r : 𝓕.projection.obj a ⟶ 𝓕.projection.obj b) :
    ∃! m : a ⟶ b, 𝓕.projection.map m = r := by
  let r' : (𝓕.objects a).algebra ⟶ (𝓕.objects b).algebra :=
    eqToHom (𝓕.object_projection a).symm ≫ r ≫ eqToHom (𝓕.object_projection b)
  obtain ⟨dm, hdm⟩ := exists_deformationMorphism 𝔪 C B hS iΛ (𝓕.objects a) (𝓕.objects b) r'
  have key (m : a ⟶ b) : 𝓕.projection.map m = r ↔ (𝓕.morphisms a b m).ringHom = r' := by
    rw [← 𝓕.morphism_projection m]
    refine ⟨fun h => by rw [h], fun h => ?_⟩
    simpa [r'] using congrArg (fun t => eqToHom (𝓕.object_projection a) ≫ t ≫
      eqToHom (𝓕.object_projection b).symm) h
  exact ⟨(𝓕.morphisms a b).symm dm,
    (key _).mpr ((congrArg DeformationMorphism.ringHom
      ((𝓕.morphisms a b).apply_symm_apply dm)).trans hdm),
    fun m hm => (𝓕.morphisms a b).injective
      ((deformationMorphism_ext 𝔪 C B hS iΛ (((key m).mp hm).trans hdm.symm)).trans
        ((𝓕.morphisms a b).apply_symm_apply dm).symm)⟩

end Thin

/-! ### Formal objects over a category whose projection is bijective on morphisms -/

section FormalObjects

universe v w uF vF

variable {Λ' : Type u} {k : Type w} [CommRing Λ'] [Field k] [Algebra Λ' k]
  {F : Type uF} [Category.{vF} F] {P : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ' k}

/-- If the projection `P` is bijective on morphisms, a morphism of formal objects is the same as
a morphism of their complete local bases. -/
theorem formalObject_existsUnique_hom
    (hP : ∀ {a b : F} (r : P.obj a ⟶ P.obj b), ∃! m : a ⟶ b, P.map m = r)
    (X Y : Deformation.FormalObject P) (β : X.base ⟶ Y.base) :
    ∃! h : X ⟶ Y, h.base = β := by
  let r : ∀ n, P.obj (X.level n) ⟶ P.obj (Y.level n) := fun n =>
    eqToHom (X.level_eq n) ≫ (Deformation.AdicTruncation.functor n).map β ≫
      eqToHom (Y.level_eq n).symm
  choose m hm hmu using fun n => hP (r n)
  have hm' : ∀ n, P.map (m n) = r n := hm
  have hlift : ∀ n, P.IsHomLift ((Deformation.AdicTruncation.functor n).map β) (m n) :=
    fun n => IsHomLift.of_fac' P _ _ (X.level_eq n) (Y.level_eq n) (hm' n)
  have htrans : ∀ (Z : Deformation.FormalObject P) (n : ℕ), P.map (Z.transition n) =
      eqToHom (Z.level_eq (n + 1)) ≫ (Deformation.AdicTruncation.transitionNat n).app Z.base ≫
        eqToHom (Z.level_eq n).symm := fun Z n => by
    have := Z.transition_lift n
    exact IsHomLift.fac' P _ _
  let h : X ⟶ Y :=
    { base := β
      app := m
      app_lift := hlift
      naturality := fun n => by
        obtain ⟨_, -, hu⟩ := hP (P.map (m (n + 1) ≫ Y.transition n))
        refine (hu _ ?_).trans (hu _ rfl).symm
        change P.map (X.transition n ≫ m n) = P.map (m (n + 1) ≫ Y.transition n)
        rw [Functor.map_comp, Functor.map_comp, htrans X n, htrans Y n, hm' n, hm' (n + 1)]
        simp only [r, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc ((Deformation.AdicTruncation.transitionNat n).app X.base),
          ← (Deformation.AdicTruncation.transitionNat n).naturality β]
        simp }
  refine ⟨h, rfl, fun h' hh' => ?_⟩
  subst hh'
  refine Deformation.FormalObject.Hom.ext (f := h') (g := h) rfl (fun n => ?_)
  apply hmu n
  have := h'.app_lift n
  exact IsHomLift.fac' P ((Deformation.AdicTruncation.functor n).map h'.base) (h'.app n)

end FormalObjects

/-! ### Versality -/

section Versality

variable [IsNoetherianRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal] (C : Type u) [CommRing C]
  [Algebra Λ C] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))

/-- Morphisms into an object equal to `Y` form a subsingleton when those into `Y` do. -/
theorem subsingleton_hom_of_eq {𝒞 : Type*} [Category 𝒞] {X Y Y' : 𝒞} (h : Y' = Y)
    [Subsingleton (X ⟶ Y)] : Subsingleton (X ⟶ Y') := by
  subst h
  infer_instance

attribute [local instance] PredeformationConstruction.category in
/-- **Versality.** A formal object of `𝒳` whose base is isomorphic over `S` to `Spec Λ_𝔪^∧` is
versal, for every algebra structure of the local ring `𝒪_{S,s}` on its base compatible with
the structure morphism. -/
theorem isVersal_of_isCompletionBase
    (ξ : FormalObject B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p)
    (hξ : IsCompletionBase 𝔪 ξ.base) (s : Spec (.of Λ))
    [Algebra ((Spec (.of Λ)).presheaf.stalk s : Type u) ξ.base.R]
    (iΛ : Spec (.of ((Spec (.of Λ)).presheaf.stalk s : Type u)) ⟶ Spec (.of Λ))
    (hiΛ : iΛ = (Spec (.of Λ)).fromSpecStalk s)
    (hΛ : Spec.map (CommRingCat.ofHom
        (algebraMap ((Spec (.of Λ)).presheaf.stalk s : Type u) ξ.base.R)) ≫ iΛ = ξ.base.toS) :
    FormalObject.IsVersal B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
      (factorizationCategory 𝔪 C B hS).property ξ ((Spec (.of Λ)).presheaf.stalk s : Type u)
      iΛ hΛ := by
  obtain ⟨σ, hσ⟩ := hξ
  have hK := algebraMap_comp_toStalkHom 𝔪 s σ hσ (by rwa [← hiΛ])
  have hP := fun {a b} (r) => predeformation_existsUnique_map 𝔪 C B hS
    (Λ' := ((Spec (.of Λ)).presheaf.stalk s : Type u)) (k := ResidueField ξ.base.R) iΛ
    (predeformationCategory iΛ
      ((factorizationCategory 𝔪 C B hS).val.p ⋙ Over.post B.inclusion) (ξ.level 0)
      (ξ.basePoint ((Spec (.of Λ)).presheaf.stalk s : Type u) iΛ hΛ))
    (a := a) (b := b) r
  rw [FormalObject.isVersal_iff, Deformation.isVersal_iff_lifts_artinian]
  intro Bt At f _ y x g hg a
  have hyb : y.base = Deformation.artinianToComplete.obj Bt :=
    IsHomLift.domain_eq Deformation.FormalObject.projection (Deformation.artinianToComplete.map f) g
  have hxb : x.base = Deformation.artinianToComplete.obj At :=
    IsHomLift.codomain_eq Deformation.FormalObject.projection
      (Deformation.artinianToComplete.map f) g
  have hom := formalObject_existsUnique_hom hP
    (ξ.predeformationFormalObject ((Spec (.of Λ)).presheaf.stalk s : Type u) iΛ hΛ)
  obtain ⟨β₀⟩ := nonempty_hom_artinian σ hK Bt
  obtain ⟨b, -, -⟩ := hom y (β₀ ≫ eqToHom hyb.symm)
  refine ⟨b, ?_⟩
  have : Subsingleton (baseAlgCat ξ.base s ⟶ Deformation.artinianToComplete.obj At) :=
    subsingleton_hom_artinian σ hK At
  have hsub : Subsingleton (baseAlgCat ξ.base s ⟶ x.base) := subsingleton_hom_of_eq hxb
  obtain ⟨_, -, huniq⟩ := hom x a.base
  exact (huniq _ (@Subsingleton.elim _ hsub _ _)).trans (huniq a rfl).symm

variable (φ : C →ₐ[Λ] Completion 𝔪)

/-- **Stacks Example 98.12.8: the formal object `ξ` is versal**, for the local ring `𝒪_{S,s}`
of `S = Spec Λ` at any point `s` and any algebra structure of `𝒪_{S,s}` on the base of `ξ`
compatible with the structure morphism, in the form of the hypothesis of Stacks 07XH. -/
theorem formalObject_isVersal (s : Spec (.of Λ))
    [Algebra ((Spec (.of Λ)).presheaf.stalk s : Type u) (formalObject 𝔪 C φ B hS).base.R]
    (iΛ : Spec (.of ((Spec (.of Λ)).presheaf.stalk s : Type u)) ⟶ Spec (.of Λ))
    (hiΛ : iΛ = (Spec (.of Λ)).fromSpecStalk s)
    (hΛ : Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of Λ)).presheaf.stalk s : Type u)
        (formalObject 𝔪 C φ B hS).base.R)) ≫ iΛ = (formalObject 𝔪 C φ B hS).base.toS) :
    FormalObject.IsVersal B (Spec (.of Λ)) hS (factorizationCategory 𝔪 C B hS).val.p
      (factorizationCategory 𝔪 C B hS).property (formalObject 𝔪 C φ B hS)
      ((Spec (.of Λ)).presheaf.stalk s : Type u) iΛ hΛ :=
  isVersal_of_isCompletionBase 𝔪 C B hS _ (isCompletionBase_formalObject 𝔪 C φ B hS) s iΛ hiΛ
    hΛ

/-- The image in `S` of the closed point of the base of `ξ`. -/
abbrev formalObjectPoint : Spec (.of Λ) :=
  (formalObject 𝔪 C φ B hS).base.toS (closedPoint (formalObject 𝔪 C φ B hS).base.R)

/-- The canonical algebra structure of the local ring of `S` at the image of the closed point on
the base of `ξ`: the map on local rings induced by the structure morphism. -/
@[instance_reducible]
def formalObjectStalkAlgebra :
    Algebra ((Spec (.of Λ)).presheaf.stalk (formalObjectPoint 𝔪 C B hS φ) : Type u)
      (formalObject 𝔪 C φ B hS).base.R :=
  (Scheme.stalkClosedPointTo (formalObject 𝔪 C φ B hS).base.toS).hom.toAlgebra

/-- The canonical algebra structure is compatible with the structure morphism. -/
theorem formalObjectStalkAlgebra_spec :
    letI := formalObjectStalkAlgebra 𝔪 C B hS φ
    Spec.map (CommRingCat.ofHom (algebraMap
        ((Spec (.of Λ)).presheaf.stalk (formalObjectPoint 𝔪 C B hS φ) : Type u)
        (formalObject 𝔪 C φ B hS).base.R)) ≫
      (Spec (.of Λ)).fromSpecStalk (formalObjectPoint 𝔪 C B hS φ) =
      (formalObject 𝔪 C φ B hS).base.toS :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

end Versality

end Deformation.Artin.GRingNecessity

end
