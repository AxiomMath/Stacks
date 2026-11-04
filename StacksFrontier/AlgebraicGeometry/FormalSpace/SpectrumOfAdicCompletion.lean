module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfAdicCompletion

/-!
# The spectrum of an adic completion as an object of the big fppf site

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an object of the big fppf site
of `S` whose underlying scheme `X` is affine with ring of global sections `A`, let `I ⊆ A` be an
ideal and let `T ⊆ |X|` be the closed subset `V(I)`. This file constructs the spectrum of the
`I`-adic completion `Â` of `A` as an object of the site, with its canonical morphism `κ` to `V`,
and shows that a morphism `ŵ₀ : X_{/T} ⟶ W₀` from the completion of `X` along `T` to an affine
object `W₀` of the site extends to a morphism `h₀ : Spec Â ⟶ W₀` agreeing with `ŵ₀` on every
morphism into `Spec Â` with image in `V(I)`, as soon as `A` is Noetherian and `X` and `W₀` lie
over a common affine open of `S`. This is step F1 of the existence half of Stacks 0GI3.

## Main definitions

* `AlgebraicGeometry.Space.adicCompletionObj`: the spectrum of the `I`-adic completion of the
  ring of global sections of `X`, as an object of the big fppf site of `S`.
* `AlgebraicGeometry.Space.adicCompletionObjHom`: its canonical morphism to `V`.
* `AlgebraicGeometry.Space.adicCompletionObjLift`: the morphism `Spec Â ⟶ W₀` induced by a
  morphism from the completion `X_{/T}` to an affine object `W₀`.

## Main results

* `AlgebraicGeometry.Space.adicCompletionObjLift_spec`: `z ≫ h₀ = ŵ₀(κ ∘ z)` for every
  morphism `z` into `Spec Â` with image in `V(I)`.
* `AlgebraicGeometry.Space.exists_adicCompletionObj_hom_app_eq`: the same for the composite with
  any morphism `W₀ ⟶ W`.

## Implementation notes

*Size.* `size (Spec Â) = max ℵ₀ #Â` and `#Â ≤ #A ^ ℵ₀`, which is below the cutoff because the
cutoff is a strong prelimit cardinal (Stacks 000R (9)); this is
`AlgebraicGeometry.BigFppfSite.contains_spec_adicCompletion`.

*The construction.* For every `n` the closed subscheme `Spec (A / Iⁿ)` of `X` has image in
`V(I)`, so `ŵ₀` sends its inclusion to a morphism `gₙ : Spec (A / Iⁿ) ⟶ W₀`. As `W₀` is affine,
`gₙ` is the spectrum of a ring map `φₙ : Γ(W₀) ⟶ A / Iⁿ`, and naturality of `ŵ₀` along the
transition maps makes the `φₙ` compatible. Their limit `Γ(W₀) ⟶ Â` (Mathlib's
`AdicCompletion.liftRingHom`) gives `h₀`. That `h₀` lies over `S` is tested on the common affine
open of `S`: two morphisms from `Spec Â` to an affine scheme are equal once they agree on every
`Spec (A / Iⁿ)`, because the maps `Â ⟶ A / Iⁿ` are jointly injective.

*The property.* Equality of two morphisms of schemes is local on the source, so it suffices to
treat an affine source `Z`. A morphism `Z ⟶ Spec Â` with image in `V(I)` corresponds to a ring
map `Â ⟶ Γ(Z)` sending `I` into the nilradical; as `I` is finitely generated it kills some
`Iⁿ`, hence the kernel `Iⁿ Â` of `Â ⟶ A / Iⁿ` (Mathlib's `pow_smul_top_eq_ker_eval`), so the
morphism factors through `Spec (A / Iⁿ)`, where `h₀` is `gₙ` by construction, and naturality of
`ŵ₀` concludes.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-! ### Two auxiliary facts -/

/-- Two morphisms from the spectrum of an adic completion to a scheme, with image in a common
affine open, are equal once they agree on the spectrum of every `R / Iⁿ`. -/
private theorem eq_of_specMap_evalₐ_comp_eq {R : Type u} [CommRing R] (I : Ideal R)
    {Y : Scheme.{u}} (O : Y.Opens) (hO : IsAffineOpen O)
    (a b : Spec (.of (AdicCompletion I R)) ⟶ Y) (ha : Set.range a ⊆ (O : Set Y))
    (hb : Set.range b ⊆ (O : Set Y))
    (h : ∀ n : ℕ, Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom) ≫ a =
      Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom) ≫ b) :
    a = b := by
  have : IsAffine O := hO
  obtain ⟨a', rfl⟩ : ∃ a', a' ≫ O.ι = a :=
    ⟨_, IsOpenImmersion.lift_fac O.ι a (by rwa [Scheme.Opens.range_ι])⟩
  obtain ⟨b', rfl⟩ : ∃ b', b' ≫ O.ι = b :=
    ⟨_, IsOpenImmersion.lift_fac O.ι b (by rwa [Scheme.Opens.range_ι])⟩
  congr 1
  refine (cancel_mono O.toScheme.isoSpec.hom).mp ?_
  rw [← Spec.map_preimage (a' ≫ O.toScheme.isoSpec.hom),
    ← Spec.map_preimage (b' ≫ O.toScheme.isoSpec.hom)]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
  refine AdicCompletion.ext_evalₐ fun n => ?_
  have h2 := congrArg (fun g => Spec.preimage (g ≫ O.toScheme.isoSpec.hom))
    (show _ ≫ a' = _ ≫ b' from (cancel_mono O.ι).mp (by simpa using h n))
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map] at h2
  exact congrArg (fun φ => φ.hom x) h2

/-- A point of an affine scheme lies in `V(I)` exactly when its prime contains `I`. -/
private theorem isoSpec_inv_mem_zeroLocus_iff {X : Scheme.{u}} [IsAffine X] (I : Ideal Γ(X, ⊤))
    (p : PrimeSpectrum Γ(X, ⊤)) : X.isoSpec.inv p ∈ X.zeroLocus (I : Set Γ(X, ⊤)) ↔ I ≤ p.asIdeal :=
  Set.ext_iff.mp (Scheme.isoSpec_inv_preimage_zeroLocus X _) p

/-- A morphism into an affine spectrum is the spectrum of the ring map it induces on global
sections. -/
private theorem eq_toSpecΓ_comp_specMap {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Naturality of a morphism out of a completion subfunctor, read on representable sections. -/
private theorem app_comp_down {V W₀ : BigFppfOver B S hS}
    {T : Set (points B S hS (yoneda.obj V))}
    (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶
      yoneda.obj W₀ ⋙ uliftFunctor.{u + 1})
    {Zo Zo' : BigFppfOver B S hS} (v : Zo' ⟶ Zo) (x : Zo ⟶ V)
    (hx : HasImageIn B S hS (yoneda.obj V) T Zo x) (x' : Zo' ⟶ V)
    (hx' : HasImageIn B S hS (yoneda.obj V) T Zo' x') (hxx : v ≫ x = x') :
    (ŵ₀.app (op Zo') ⟨ULift.up x', hx'⟩).down =
      v ≫ (ŵ₀.app (op Zo) ⟨ULift.up x, hx⟩).down := by
  subst hxx
  exact congrArg ULift.down (NatTrans.naturality_apply ŵ₀ v.op ⟨ULift.up x, hx⟩)

/-! ### The spectrum of the adic completion -/

section

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (W₀ : BigFppfOver B S hS)

/-- The spectrum of the ring of global sections of an affine object of the site lies in the
site. -/
theorem contains_spec_globalSections :
    B.Contains (Spec (.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :=
  (Scheme.size_congr ((BigFppfOver.toScheme B S hS).obj V).isoSpec).symm.trans_lt V.left.2

/-- The spectrum of the `I`-adic completion `Â` of the ring of global sections `A` of an affine
object `V` of the big fppf site of `S`, as an object of that site, structured over `S` through
`Spec Â ⟶ Spec A ≅ V`. Its underlying scheme is `Spec Â` by definition. -/
def adicCompletionObj (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (B.contains_spec_adicCompletion (contains_spec_globalSections B S hS V) I)
    (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map V.hom)

/-- The canonical morphism `κ : Spec Â ⟶ V`. -/
def adicCompletionObjHom (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    adicCompletionObj B S hS V I ⟶ V :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The underlying morphism of schemes of `κ : Spec Â ⟶ V` is the composite
`Spec Â ⟶ Spec A ≅ V`. -/
lemma toScheme_map_adicCompletionObjHom (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (BigFppfOver.toScheme B S hS).map (adicCompletionObjHom B S hS V I) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv :=
  rfl

/-- A closed subset of the points of an affine object of the site is the zero locus of an ideal
of its ring of global sections. -/
theorem exists_ideal_mem_iff_mem_zeroLocus {T : Set (points B S hS (yoneda.obj V))}
    (hT : IsClosed T) :
    ∃ I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤), ∀ x, x ∈ T ↔
      pointsToScheme B S hS V x ∈ ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) := by
  have hcl := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V T).mp hT
  obtain ⟨I, hI⟩ := (Scheme.eq_zeroLocus_of_isClosed_of_isAffine _ _).mp hcl
  refine ⟨I, fun x => ?_⟩
  rw [← hI]
  exact (injective_pointsToScheme B S hS V).mem_set_image.symm

variable (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  {T : Set (points B S hS (yoneda.obj V))}

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- For `T` the zero locus of `I`, a morphism into `V` has image in `T` exactly when the
underlying morphism of schemes has image in `V(I)`. -/
private theorem hasImageIn_iff_forall_mem_zeroLocus
    (hTI : ∀ x, x ∈ T ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (Zo : BigFppfOver B S hS) (z : Zo ⟶ V) :
    HasImageIn B S hS (yoneda.obj V) T Zo z ↔
      ∀ x, (BigFppfOver.toScheme B S hS).map z x ∈
        ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
          (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) := by
  have hz : yonedaEquiv.symm z = yoneda.map z := by
    rw [Equiv.symm_apply_eq, yonedaEquiv_yoneda_map]
  rw [hasImageIn_iff_range_subset, hz]
  constructor
  · intro h x
    obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS Zo x
    rw [← pointsToScheme_pointsMap_yoneda]
    exact (hTI _).mp (h ⟨w, rfl⟩)
  · rintro h _ ⟨w, rfl⟩
    rw [hTI, pointsToScheme_pointsMap_yoneda]
    exact h _

/-! #### The closed subschemes `Spec (A / Iⁿ)` -/

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The composite `Spec (A / Iⁿ) ⟶ Spec Â ⟶ Spec A` is the closed immersion
`Spec (A / Iⁿ) ⟶ Spec A` induced by the quotient map. -/
@[reassoc]
theorem specMap_evalₐ_comp_specMap_algebraMap (n : ℕ) :
    Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) := by
  rw [← Spec.map_comp]
  congr 1

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- For `m ≤ n`, the composite `Spec (A / Iᵐ) ⟶ Spec (A / Iⁿ) ⟶ Spec A` is the closed
immersion `Spec (A / Iᵐ) ⟶ Spec A` induced by the quotient map. -/
@[reassoc]
theorem specMap_factorPow_comp_specMap_mk {m n : ℕ} (hmn : m ≤ n) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I hmn)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ m))) := by
  rw [← Spec.map_comp]
  congr 1

/-- `Spec (A / Iⁿ)` as an object of the site, structured over `S` through `V`. -/
def adicCompletionQuotientObj (n : ℕ) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS
    (Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      (contains_spec_globalSections B S hS V)
      ((mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (le_max_right _ _)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map V.hom)

/-- The closed immersion `Spec (A / Iⁿ) ⟶ V`. -/
def adicCompletionQuotientObjHom (n : ℕ) : adicCompletionQuotientObj B S hS V I n ⟶ V :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv))
    (by apply ObjectProperty.hom_ext; rfl)

private theorem specMap_evalₐ_comp_toScheme_map_adicCompletionObjHom (n : ℕ) :
    Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom) ≫
        (BigFppfOver.toScheme B S hS).map (adicCompletionObjHom B S hS V I) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv := by
  rw [toScheme_map_adicCompletionObjHom, specMap_evalₐ_comp_specMap_algebraMap_assoc]

/-- The closed immersion `Spec (A / Iⁿ) ⟶ Spec Â`. -/
private def adicCompletionQuotientObjToAdic (n : ℕ) :
    adicCompletionQuotientObj B S hS V I n ⟶ adicCompletionObj B S hS V I :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom)))
    (by
      apply ObjectProperty.hom_ext
      exact specMap_evalₐ_comp_specMap_algebraMap_assoc B S hS V I n _)

private theorem adicCompletionQuotientObjToAdic_comp (n : ℕ) :
    adicCompletionQuotientObjToAdic B S hS V I n ≫ adicCompletionObjHom B S hS V I =
      adicCompletionQuotientObjHom B S hS V I n :=
  (BigFppfOver.toScheme B S hS).map_injective
    ((Functor.map_comp _ _ _).trans
      (specMap_evalₐ_comp_toScheme_map_adicCompletionObjHom B S hS V I n))

/-- The transition map `Spec (A / Iᵐ) ⟶ Spec (A / Iⁿ)` for `m ≤ n`. -/
def adicCompletionQuotientObjTransition {m n : ℕ} (hmn : m ≤ n) :
    adicCompletionQuotientObj B S hS V I m ⟶ adicCompletionQuotientObj B S hS V I n :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPow I hmn))))
    (by
      apply ObjectProperty.hom_ext
      exact specMap_factorPow_comp_specMap_mk_assoc B S hS V I hmn _)

private theorem adicCompletionQuotientObjTransition_comp {m n : ℕ} (hmn : m ≤ n) :
    adicCompletionQuotientObjTransition B S hS V I hmn ≫ adicCompletionQuotientObjHom B S hS V I n =
      adicCompletionQuotientObjHom B S hS V I m :=
  (BigFppfOver.toScheme B S hS).map_injective
    ((Functor.map_comp _ _ _).trans (specMap_factorPow_comp_specMap_mk_assoc B S hS V I hmn _))

/-- For `T` the zero locus of `I`, the closed immersion `Spec (A / Iⁿ) ⟶ V` has image
within `T`. -/
theorem hasImageIn_adicCompletionQuotientObjHom
    (hTI : ∀ x, x ∈ T ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (n : ℕ) :
    HasImageIn B S hS (yoneda.obj V) T (adicCompletionQuotientObj B S hS V I n)
      (adicCompletionQuotientObjHom B S hS V I n) := by
  rw [hasImageIn_iff_forall_mem_zeroLocus B S hS V I hTI]
  intro (p : PrimeSpectrum (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ I ^ n))
  have key : I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n)) p).asIdeal := by
    refine Ideal.IsPrime.le_of_pow_le (n := n) ?_
    intro a ha
    show Ideal.Quotient.mk (I ^ n) a ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact p.asIdeal.zero_mem
  exact (isoSpec_inv_mem_zeroLocus_iff I _).mpr key

/-! #### The morphism `h₀ : Spec Â ⟶ W₀` -/

variable (hTI : ∀ x, x ∈ T ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  (O : S.Opens) (hO : IsAffineOpen O)
  (hVO : Set.range (B.inclusion.map V.hom).base ⊆ (O : Set S))
  (hWO : Set.range (B.inclusion.map W₀.hom).base ⊆ (O : Set S))
  (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶
      yoneda.obj W₀ ⋙ uliftFunctor.{u + 1})

/-- The morphism `gₙ : Spec (A / Iⁿ) ⟶ W₀` obtained by evaluating `ŵ₀` on the closed
subscheme `Spec (A / Iⁿ)`. -/
def adicCompletionQuotientLift (n : ℕ) : adicCompletionQuotientObj B S hS V I n ⟶ W₀ :=
  (ŵ₀.app (op (adicCompletionQuotientObj B S hS V I n))
    ⟨ULift.up (adicCompletionQuotientObjHom B S hS V I n),
      hasImageIn_adicCompletionQuotientObjHom B S hS V I hTI n⟩).down

private theorem adicCompletionQuotientObjTransition_comp_lift {m n : ℕ} (hmn : m ≤ n) :
    adicCompletionQuotientObjTransition B S hS V I hmn ≫
        adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n =
      adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ m :=
  (app_comp_down B S hS ŵ₀ (adicCompletionQuotientObjTransition B S hS V I hmn)
    (adicCompletionQuotientObjHom B S hS V I n)
    (hasImageIn_adicCompletionQuotientObjHom B S hS V I hTI n)
    (adicCompletionQuotientObjHom B S hS V I m)
    (hasImageIn_adicCompletionQuotientObjHom B S hS V I hTI m)
    (adicCompletionQuotientObjTransition_comp B S hS V I hmn)).symm

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]

/-- The ring map `φₙ : Γ(W₀) ⟶ A / Iⁿ` of which `gₙ` is the spectrum. -/
def adicCompletionQuotientRingHom (n : ℕ) :
    Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) ⟶
      CommRingCat.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ I ^ n) :=
  Spec.preimage
    ((BigFppfOver.toScheme B S hS).map (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n) ≫
    ((BigFppfOver.toScheme B S hS).obj W₀).isoSpec.hom)

private theorem specMap_adicCompletionQuotientRingHom (n : ℕ) :
    Spec.map (adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ n) =
      (BigFppfOver.toScheme B S hS).map (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n) ≫
        ((BigFppfOver.toScheme B S hS).obj W₀).isoSpec.hom :=
  Spec.map_preimage _

/-- For `m ≤ n`, the ring maps `φₙ : Γ(W₀) ⟶ A / Iⁿ` and `φₘ` are compatible with the
transition map `A / Iⁿ ⟶ A / Iᵐ`. -/
theorem factorPow_comp_adicCompletionQuotientRingHom {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp
        (adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ n).hom =
      (adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ m).hom := by
  have h : adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ n ≫
      CommRingCat.ofHom (Ideal.Quotient.factorPow I hmn) =
        adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ m := by
    apply Spec.map_injective
    have e : (BigFppfOver.toScheme B S hS).map
          (adicCompletionQuotientObjTransition B S hS V I hmn) ≫
        (BigFppfOver.toScheme B S hS).map (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n) ≫
          ((BigFppfOver.toScheme B S hS).obj W₀).isoSpec.hom =
        (BigFppfOver.toScheme B S hS).map (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ m) ≫
          ((BigFppfOver.toScheme B S hS).obj W₀).isoSpec.hom := by
      rw [← Category.assoc, ← Functor.map_comp,
        adicCompletionQuotientObjTransition_comp_lift B S hS V W₀ I hTI ŵ₀ hmn]
    rw [Spec.map_comp, specMap_adicCompletionQuotientRingHom,
      specMap_adicCompletionQuotientRingHom]
    exact e
  exact congrArg CommRingCat.Hom.hom h

/-- The ring map `Γ(W₀) ⟶ Â`, the limit of the `φₙ`. -/
def adicCompletionObjLiftRingHom :
    Γ((BigFppfOver.toScheme B S hS).obj W₀, ⊤) →+*
      AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  AdicCompletion.liftRingHom I (fun n => (adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ n).hom)
    (fun hmn => factorPow_comp_adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ hmn)

/-- The morphism of schemes `h₀ : Spec Â ⟶ W₀`. -/
def adicCompletionObjLiftScheme :
    Spec (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) ⟶
      (BigFppfOver.toScheme B S hS).obj W₀ :=
  Spec.map (CommRingCat.ofHom (adicCompletionObjLiftRingHom B S hS V W₀ I hTI ŵ₀)) ≫
    ((BigFppfOver.toScheme B S hS).obj W₀).isoSpec.inv

private theorem specMap_evalₐ_comp_adicCompletionObjLiftScheme (n : ℕ) :
    Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom) ≫
        adicCompletionObjLiftScheme B S hS V W₀ I hTI ŵ₀ =
      (BigFppfOver.toScheme B S hS).map (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n) := by
  have h : CommRingCat.ofHom (adicCompletionObjLiftRingHom B S hS V W₀ I hTI ŵ₀) ≫
      CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom =
        adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ n := by
    ext x
    exact AdicCompletion.evalₐ_liftRingHom I
      (fun n => (adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ n).hom)
      (fun hmn => factorPow_comp_adicCompletionQuotientRingHom B S hS V W₀ I hTI ŵ₀ hmn) n x
  have e : ((BigFppfOver.toScheme B S hS).map (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n) ≫
      ((BigFppfOver.toScheme B S hS).obj W₀).isoSpec.hom) ≫
        ((BigFppfOver.toScheme B S hS).obj W₀).isoSpec.inv =
      (BigFppfOver.toScheme B S hS).map (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n) := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [adicCompletionObjLiftScheme, ← Category.assoc, ← Spec.map_comp, h,
    specMap_adicCompletionQuotientRingHom]
  exact e

include O hO hVO hWO in
/-- The morphism of schemes `h₀ : Spec Â ⟶ W₀` lies over `S`. -/
theorem adicCompletionObjLiftScheme_comp :
    adicCompletionObjLiftScheme B S hS V W₀ I hTI ŵ₀ ≫ B.inclusion.map W₀.hom =
      B.inclusion.map (adicCompletionObj B S hS V I).hom := by
  refine eq_of_specMap_evalₐ_comp_eq I O hO _ _ ?_ ?_ fun n => ?_
  · rintro _ ⟨x, rfl⟩
    exact hWO ⟨adicCompletionObjLiftScheme B S hS V W₀ I hTI ŵ₀ x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact hVO ⟨(BigFppfOver.toScheme B S hS).map (adicCompletionObjHom B S hS V I) x, rfl⟩
  · rw [← Category.assoc, specMap_evalₐ_comp_adicCompletionObjLiftScheme]
    exact (congrArg (fun k => k.hom)
      (Over.w (adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n))).trans
      (specMap_evalₐ_comp_specMap_algebraMap_assoc B S hS V I n _).symm

/-- **Step F1 of Stacks 0GI3.** The morphism `h₀ : Spec Â ⟶ W₀` induced by a morphism
`ŵ₀ : X_{/T} ⟶ W₀` from the completion of `X` along `T = V(I)` to an affine object `W₀`, when
`X` and `W₀` lie over a common affine open of `S`: it is the spectrum of the limit of the ring
maps `Γ(W₀) ⟶ A / Iⁿ` corresponding to the values of `ŵ₀` on the closed subschemes
`Spec (A / Iⁿ)`. -/
def adicCompletionObjLift : adicCompletionObj B S hS V I ⟶ W₀ :=
  Over.homMk (ObjectProperty.homMk (adicCompletionObjLiftScheme B S hS V W₀ I hTI ŵ₀))
    (by
      apply ObjectProperty.hom_ext
      exact adicCompletionObjLiftScheme_comp B S hS V W₀ I hTI O hO hVO hWO ŵ₀)

private theorem adicCompletionQuotientObjToAdic_comp_lift (n : ℕ) :
    adicCompletionQuotientObjToAdic B S hS V I n ≫
        adicCompletionObjLift B S hS V W₀ I hTI O hO hVO hWO ŵ₀ =
      adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n :=
  (BigFppfOver.toScheme B S hS).map_injective
    ((Functor.map_comp _ _ _).trans
      (specMap_evalₐ_comp_adicCompletionObjLiftScheme B S hS V W₀ I hTI ŵ₀ n))

/-- The property of `h₀` over an affine source. -/
private theorem adicCompletionObjLift_spec_of_isAffine
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (Zo : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj Zo)]
    (z : Zo ⟶ adicCompletionObj B S hS V I)
    (hz : HasImageIn B S hS (yoneda.obj V) T Zo (z ≫ adicCompletionObjHom B S hS V I)) :
    z ≫ adicCompletionObjLift B S hS V W₀ I hTI O hO hVO hWO ŵ₀ =
      (ŵ₀.app (op Zo) ⟨ULift.up (z ≫ adicCompletionObjHom B S hS V I), hz⟩).down := by
  have hzs := (hasImageIn_iff_forall_mem_zeroLocus B S hS V I hTI Zo _).mp hz
  -- the ring map `ψ : Â ⟶ Γ(Z)` of which `z` is the spectrum
  obtain ⟨ψ, hzψ⟩ : ∃ ψ : CommRingCat.of (AdicCompletion I
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ⟶
        Γ((BigFppfOver.toScheme B S hS).obj Zo, ⊤),
      (BigFppfOver.toScheme B S hS).map z =
        ((BigFppfOver.toScheme B S hS).obj Zo).toSpecΓ ≫ Spec.map ψ :=
    ⟨_, eq_toSpecΓ_comp_specMap ((BigFppfOver.toScheme B S hS).map z)⟩
  -- `ψ` sends `I` into the nilradical
  have hnil : I.map (ψ.hom.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) ≤
      nilradical Γ((BigFppfOver.toScheme B S hS).obj Zo, ⊤) := by
    have huniv : PrimeSpectrum.zeroLocus
        ((I.map (ψ.hom.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) :
          Ideal Γ((BigFppfOver.toScheme B S hS).obj Zo, ⊤)) :
          Set Γ((BigFppfOver.toScheme B S hS).obj Zo, ⊤)) = Set.univ := by
      refine Set.eq_univ_of_forall fun P => ?_
      obtain ⟨x, hxP⟩ := (ConcreteCategory.bijective_of_isIso
        ((BigFppfOver.toScheme B S hS).obj Zo).isoSpec.hom.base).surjective P
      have hpt : (BigFppfOver.toScheme B S hS).map (z ≫ adicCompletionObjHom B S hS V I) x =
          ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv
            (Spec.map (CommRingCat.ofHom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
              (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) (Spec.map ψ P)) := by
        rw [← hxP]
        exact congrArg
          (fun g => (BigFppfOver.toScheme B S hS).map (adicCompletionObjHom B S hS V I) (g x)) hzψ
      have hmem' : I ≤ Ideal.comap (ψ.hom.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) P.asIdeal :=
        (isoSpec_inv_mem_zeroLocus_iff I _).mp (hpt ▸ hzs x)
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
      exact hmem'
    rwa [PrimeSpectrum.zeroLocus_eq_univ_iff, SetLike.coe_subset_coe] at huniv
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (J := (0 : Ideal Γ((BigFppfOver.toScheme B S hS).obj Zo, ⊤))) hnil
    ((Ideal.fg_of_isNoetherianRing I).map _)
  rw [← Ideal.map_pow, Submodule.zero_eq_bot, le_bot_iff, Ideal.map_eq_bot_iff_le_ker] at hn
  -- `ψ` kills the kernel of `Â ⟶ A / Iⁿ`
  have hker : ∀ x : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      AdicCompletion.evalₐ I n x = 0 → ψ.hom x = 0 := by
    intro x hx
    have hx' : x ∈ (I ^ n • ⊤ : Submodule Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing I),
        LinearMap.mem_ker, ← AdicCompletion.factor_evalₐ_eq_eval I x
          (le_of_eq (Ideal.mul_top _).symm), hx, map_zero]
    refine Submodule.smul_induction_on (p := fun y => ψ.hom y = 0) hx'
      (fun r hr m _ => ?_) (fun y y' hy hy' => ?_)
    · show ψ.hom (r • m) = 0
      rw [Algebra.smul_def, map_mul]
      have hr' : ψ.hom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) r) = 0 := hn hr
      rw [hr', zero_mul]
    · show ψ.hom (y + y') = 0
      rw [map_add, hy, hy', add_zero]
  -- the factorization `ψ = ψ' ∘ evalₐ`
  let ψ' : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ I ^ n →+*
      Γ((BigFppfOver.toScheme B S hS).obj Zo, ⊤) :=
    Ideal.Quotient.lift (I ^ n) (ψ.hom.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) (fun a ha => hn ha)
  have hψ' : CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom ≫ CommRingCat.ofHom ψ' =
      ψ := by
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    show ψ' (AdicCompletion.evalₐ I n x) = ψ.hom x
    rw [← ha]
    show ψ.hom (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) a) = ψ.hom x
    rw [← sub_eq_zero, ← map_sub]
    refine hker _ ?_
    rw [map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha, sub_self]
  -- the morphism `t : Z ⟶ Spec (A / Iⁿ)`
  obtain ⟨ts, hts⟩ : ∃ ts : (BigFppfOver.toScheme B S hS).obj Zo ⟶
      Spec (.of (Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) ⧸ I ^ n)),
      ts ≫ Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I n).toRingHom) =
        (BigFppfOver.toScheme B S hS).map z :=
    ⟨((BigFppfOver.toScheme B S hS).obj Zo).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ'), by
      rw [Category.assoc, ← Spec.map_comp, hψ', hzψ]⟩
  let t : Zo ⟶ adicCompletionQuotientObj B S hS V I n :=
    Over.homMk (ObjectProperty.homMk ts)
      (by
        apply ObjectProperty.hom_ext
        show ts ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) ≫ _ = _
        rw [← specMap_evalₐ_comp_specMap_algebraMap_assoc, ← Category.assoc ts, hts]
        exact congrArg (fun k => k.hom) (Over.w z))
  have hzt : z = t ≫ adicCompletionQuotientObjToAdic B S hS V I n :=
    (BigFppfOver.toScheme B S hS).map_injective
      (hts.symm.trans ((BigFppfOver.toScheme B S hS).map_comp t
        (adicCompletionQuotientObjToAdic B S hS V I n)).symm)
  have hxx : t ≫ adicCompletionQuotientObjHom B S hS V I n =
      z ≫ adicCompletionObjHom B S hS V I := by
    rw [hzt, Category.assoc, adicCompletionQuotientObjToAdic_comp]
  calc z ≫ adicCompletionObjLift B S hS V W₀ I hTI O hO hVO hWO ŵ₀
      = (t ≫ adicCompletionQuotientObjToAdic B S hS V I n) ≫
          adicCompletionObjLift B S hS V W₀ I hTI O hO hVO hWO ŵ₀ := by rw [← hzt]
    _ = t ≫ adicCompletionQuotientLift B S hS V W₀ I hTI ŵ₀ n := by
        rw [Category.assoc, adicCompletionQuotientObjToAdic_comp_lift]
    _ = _ := (app_comp_down B S hS ŵ₀ t (adicCompletionQuotientObjHom B S hS V I n)
        (hasImageIn_adicCompletionQuotientObjHom B S hS V I hTI n) _ hz hxx).symm

/-- **Step F1 of Stacks 0GI3, the property of `h₀`.** For every morphism `z` into `Spec Â`
whose composite with `κ : Spec Â ⟶ V` has image in `T = V(I)`, the composite `z ≫ h₀` is the
value of `ŵ₀` on `κ ∘ z`. -/
theorem adicCompletionObjLift_spec [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (Zo : BigFppfOver B S hS) (z : Zo ⟶ adicCompletionObj B S hS V I)
    (hz : HasImageIn B S hS (yoneda.obj V) T Zo (z ≫ adicCompletionObjHom B S hS V I)) :
    z ≫ adicCompletionObjLift B S hS V W₀ I hTI O hO hVO hWO ŵ₀ =
      (ŵ₀.app (op Zo) ⟨ULift.up (z ≫ adicCompletionObjHom B S hS V I), hz⟩).down := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  refine Scheme.Cover.hom_ext ((BigFppfOver.toScheme B S hS).obj Zo).affineCover _ _
    fun j => ?_
  let Uj : BigFppfOver B S hS := BigFppfOver.mk B S hS
    (B.contains_of_mono (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f j) Zo.left.2)
    (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f j ≫ B.inclusion.map Zo.hom)
  let uj : Uj ⟶ Zo :=
    Over.homMk (ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.f j))
      (by apply ObjectProperty.hom_ext; rfl)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Uj) :=
    inferInstanceAs (IsAffine (((BigFppfOver.toScheme B S hS).obj Zo).affineCover.X j))
  have hz' : HasImageIn B S hS (yoneda.obj V) T Uj
      ((uj ≫ z) ≫ adicCompletionObjHom B S hS V I) := by
    rw [Category.assoc]
    exact ((completionSubfunctor B S hS (yoneda.obj V) T).toFunctor.map uj.op
      ⟨ULift.up (z ≫ adicCompletionObjHom B S hS V I), hz⟩).2
  have h1 := adicCompletionObjLift_spec_of_isAffine B S hS V W₀ I hTI O hO hVO hWO ŵ₀ Uj
    (uj ≫ z) hz'
  have h2 := app_comp_down B S hS ŵ₀ uj _ hz _ hz' (Category.assoc _ _ _).symm
  show (BigFppfOver.toScheme B S hS).map uj ≫ _ = (BigFppfOver.toScheme B S hS).map uj ≫ _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, h1, h2]

end

/-- **Step F1 of Stacks 0GI3, in the form used for glueing.** Let `V` be an affine object of the
site with Noetherian ring of global sections `A`, let `T = V(I)` for an ideal `I ⊆ A`, and let
`ŵ = ŵ₀ ≫ π` be a morphism from the completion `X_{/T}` to `W` factoring through an affine
object `W₀` lying, like `V`, over an affine open of `S`. Then there is a morphism
`h : Spec Â ⟶ W` agreeing with `ŵ` on every morphism into `Spec Â` with image in `V(I)`. -/
theorem exists_adicCompletionObj_hom_app_eq {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V W₀ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
    {T : Set (points B S hS (yoneda.obj V))}
    (hTI : ∀ x, x ∈ T ↔ pointsToScheme B S hS V x ∈
      ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
        (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
    (O : S.Opens) (hO : IsAffineOpen O)
    (hVO : Set.range (B.inclusion.map V.hom).base ⊆ (O : Set S))
    (hWO : Set.range (B.inclusion.map W₀.hom).base ⊆ (O : Set S))
    (π : yoneda.obj W₀ ⟶ W)
    (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj V) T).toFunctor ⟶
      yoneda.obj W₀ ⋙ uliftFunctor.{u + 1}) :
    ∃ h : yoneda.obj (adicCompletionObj B S hS V I) ⟶ W,
      ∀ (Zo : BigFppfOver B S hS) (z : Zo ⟶ adicCompletionObj B S hS V I)
        (hz : HasImageIn B S hS (yoneda.obj V) T Zo (z ≫ adicCompletionObjHom B S hS V I)),
        h.app (op Zo) z = ((ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1}).app (op Zo)
          ⟨ULift.up (z ≫ adicCompletionObjHom B S hS V I), hz⟩).down := by
  refine ⟨yoneda.map (adicCompletionObjLift B S hS V W₀ I hTI O hO hVO hWO ŵ₀) ≫ π,
    fun Zo z hz => ?_⟩
  show π.app (op Zo) (z ≫ adicCompletionObjLift B S hS V W₀ I hTI O hO hVO hWO ŵ₀) =
    π.app (op Zo) (ŵ₀.app (op Zo) ⟨ULift.up (z ≫ adicCompletionObjHom B S hS V I), hz⟩).down
  rw [adicCompletionObjLift_spec]

end Space

end AlgebraicGeometry

end
