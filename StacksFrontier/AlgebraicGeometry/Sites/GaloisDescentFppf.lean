module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Galois descent of sections of an fppf sheaf along a finite Galois algebra

Let `R → A` be a ring map making `A` a faithfully flat, finitely presented `R`-algebra, and let a
finite group `G` act on `A` by `R`-algebra automorphisms, `ρ : G →* (A ≃ₐ[R] A)`.  Suppose the
action is *Galois*: the canonical map

`A ⊗[R] A → (G → A)`,  `a ⊗ b ↦ (σ ↦ a · σ(b))`

(`AlgebraicGeometry.galoisTensorPi`) is bijective.  Then for every sheaf `F` on the big fppf site
of a scheme `S` — a presheaf `(BigFppfOver B S hS)ᵒᵖ ⥤ Type w` satisfying
`Presheaf.IsSheaf (BigFppfOver.topology B S hS)`, the spelling of the sheaf condition of
`AlgebraicGeometry.IsAlgebraicSpace` — restriction along `Spec A → Spec R` identifies `F(Spec R)`
with the sections of `F(Spec A)` fixed by the pullbacks along the automorphisms `Spec σ`.

The argument is the usual one.  `Spec A → Spec R` is an fppf covering, so `F(Spec R)` is the
equalizer of the two restrictions `F(Spec A) ⇉ F(Spec A ×_{Spec R} Spec A)`.  The Galois
condition says that the graphs `(id, Spec σ) : Spec A → Spec A ×_{Spec R} Spec A` are the summand
inclusions of a decomposition `∐_{σ : G} Spec A ≅ Spec A ×_{Spec R} Spec A`; so they are open
immersions covering the fibre product, and a section of `F(Spec A)` lies in the equalizer exactly
when it is fixed by every `Spec σ`.

## Main definitions

* `AlgebraicGeometry.galoisTensorPi`: the canonical map `A ⊗[R] A → (G → A)`.
* `AlgebraicGeometry.specGraph`: the graph `(id, Spec σ)` of an automorphism, into the fibre
  product of schemes `Spec A ×_{Spec R} Spec A`.
* `AlgebraicGeometry.galoisBaseObj`, `AlgebraicGeometry.galoisCoverObj`,
  `AlgebraicGeometry.galoisCoverMap`, `AlgebraicGeometry.galoisCoverAut` and
  `AlgebraicGeometry.galoisGraph`: `Spec R`, `Spec A`, the covering `Spec A → Spec R`, the
  automorphisms `Spec σ` and the graphs, as objects and morphisms of the big fppf site over `S`.
* `AlgebraicGeometry.galoisRestriction`: restriction `F(Spec R) → F(Spec A)^G`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_specGraph`, `AlgebraicGeometry.isClosedImmersion_specGraph`,
  `AlgebraicGeometry.etale_specGraph` and `AlgebraicGeometry.exists_specGraph_eq`: under the
  Galois condition the graphs are open and closed immersions, étale, and jointly surjective.
* `AlgebraicGeometry.galoisCoverMap_mem_topology`: `Spec A → Spec R` is an fppf covering.
* `AlgebraicGeometry.galoisGraph_mem_topology`: under the Galois condition the graphs generate a
  covering sieve of the fibre product in the big fppf site.
* `AlgebraicGeometry.existsUnique_map_galoisCoverMap`: the sheaf-equalizer step, with no Galois
  condition — a section of `F(Spec A)` whose two pullbacks to every `Z` with two maps to `Spec A`
  agreeing over `Spec R` agree descends uniquely to `F(Spec R)`.
* `AlgebraicGeometry.bijective_galoisRestriction`: **Galois descent of sections**,
  `F(Spec R) ≅ F(Spec A)^G`.

## Implementation notes

`Spec R` and `Spec A` enter the big fppf site through `AlgebraicGeometry.siteObject`, so the
statements carry the two size conditions `B.Contains (Spec R)` and `B.Contains (Spec A)` and a
structure morphism `s : Spec R ⟶ S`; the structure morphism of `Spec A` is the composite.

The site's fibre product `Spec A ×_{Spec R} Spec A` is compared with the fibre product of schemes
by `CategoryTheory.Limits.PreservesPullback.iso` at `AlgebraicGeometry.BigFppfOver.toScheme`, which
preserves fibre products (Stacks 021U), and the fibre product of schemes with
`Spec (A ⊗[R] A)` by `AlgebraicGeometry.pullbackSpecIso`.  `∐_{σ : G} Spec A ≅ Spec (G → A)` is
`AlgebraicGeometry.sigmaSpec`, invertible because `G` is finite.

The open-immersion property of the graph inside the site is obtained by cancelling the comparison
isomorphism with `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`: the two spellings
of the fibre product of schemes are equal only up to unfolding the functor, and instance search
does not see an open immersion through that unfolding.

## References

* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe w u

namespace AlgebraicGeometry

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {G : Type u} [Group G]
  (ρ : G →* (A ≃ₐ[R] A))

/-! ### The Galois condition on rings and on spectra -/

/-- The canonical map `A ⊗[R] A → (G → A)`, `a ⊗ b ↦ (σ ↦ a · σ(b))`, attached to an action of
`G` on `A` by `R`-algebra automorphisms.  The action is *Galois* when it is bijective. -/
def galoisTensorPi : A ⊗[R] A →ₐ[A] (G → A) :=
  AlgHom.pi fun σ ↦ Algebra.TensorProduct.lift (AlgHom.id A A) (ρ σ).toAlgHom
    fun _ _ ↦ Commute.all _ _

/-- The coordinate at `σ` of the image of `a ⊗ b` under `AlgebraicGeometry.galoisTensorPi` is
`a · σ(b)`. -/
@[simp]
lemma galoisTensorPi_tmul (a b : A) (σ : G) :
    galoisTensorPi ρ (a ⊗ₜ[R] b) σ = a * ρ σ b := by
  simp [galoisTensorPi, Algebra.TensorProduct.lift_tmul]

/-- The automorphism `Spec σ` of `Spec A` lies over `Spec R`, `σ` being an `R`-algebra map. -/
lemma specMap_aut_comp_specMap_algebraMap (σ : G) :
    Spec.map (CommRingCat.ofHom (ρ σ).toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (ρ σ).commutes x

/-- The graph `(id, Spec σ) : Spec A → Spec A ×_{Spec R} Spec A` of the automorphism `Spec σ`. -/
def specGraph (σ : G) : Spec (.of A) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom (ρ σ).toRingEquiv.toRingHom)) (by
    rw [Category.id_comp, specMap_aut_comp_specMap_algebraMap])

/-- Read on `Spec (A ⊗[R] A)`, the graph of `Spec σ` is the spectrum of the coordinate of
`AlgebraicGeometry.galoisTensorPi` at `σ`. -/
lemma specGraph_comp_pullbackSpecIso (σ : G) :
    specGraph ρ σ ≫ (pullbackSpecIso R A A).hom =
      Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : G ↦ A) σ).comp
        (galoisTensorPi ρ).toRingHom)) := by
  rw [← Iso.eq_comp_inv]
  apply pullback.hom_ext
  · rw [specGraph, pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    have : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) ≫
        CommRingCat.ofHom ((Pi.evalRingHom (fun _ : G ↦ A) σ).comp
          (galoisTensorPi ρ).toRingHom) = 𝟙 _ := by
      ext x
      simp
    rw [this, Spec.map_id]
  · rw [specGraph, pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    congr 1
    ext x
    simp

section Galois

variable [Finite G] (h : Function.Bijective (galoisTensorPi ρ))
include h

/-- **The Galois decomposition of `Spec A ×_{Spec R} Spec A`.**  Under the Galois condition the
fibre product is the disjoint union of copies of `Spec A` indexed by `G`: it is
`Spec (A ⊗[R] A) ≅ Spec (G → A) ≅ ∐_{σ : G} Spec A`. -/
def galoisSigmaIso : (∐ fun _ : G ↦ Spec (.of A)) ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
  asIso (sigmaSpec (fun _ : G ↦ CommRingCat.of A)) ≪≫
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (RingEquiv.ofBijective (galoisTensorPi ρ).toRingHom h)).op ≪≫
    (pullbackSpecIso R A A).symm

/-- The summand of the Galois decomposition indexed by `σ` is the graph of `Spec σ`. -/
lemma ι_galoisSigmaIso_hom (σ : G) :
    Sigma.ι (fun _ : G ↦ Spec (.of A)) σ ≫ (galoisSigmaIso ρ h).hom = specGraph ρ σ := by
  rw [← cancel_mono (pullbackSpecIso R A A).hom, specGraph_comp_pullbackSpecIso]
  simp only [galoisSigmaIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.op_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, ι_sigmaSpec_assoc]
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- **Under the Galois condition the graph of `Spec σ` is an open immersion**, being a summand
inclusion of the Galois decomposition; in particular it is étale. -/
theorem isOpenImmersion_specGraph (σ : G) : IsOpenImmersion (specGraph ρ σ) := by
  rw [← ι_galoisSigmaIso_hom ρ h]
  infer_instance

/-- Under the Galois condition the graph of `Spec σ` is étale. -/
theorem etale_specGraph (σ : G) : Etale (specGraph ρ σ) := by
  have := isOpenImmersion_specGraph ρ h σ
  infer_instance

omit [Finite G] in
/-- **Under the Galois condition the graph of `Spec σ` is a closed immersion**: on
`Spec (A ⊗[R] A)` it is the spectrum of the coordinate of `AlgebraicGeometry.galoisTensorPi` at
`σ`, which is surjective. -/
theorem isClosedImmersion_specGraph (σ : G) : IsClosedImmersion (specGraph ρ σ) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullbackSpecIso R A A).hom, specGraph_comp_pullbackSpecIso]
  refine IsClosedImmersion.spec_of_surjective _ fun a ↦ ?_
  obtain ⟨t, ht⟩ := h.2 fun _ ↦ a
  exact ⟨t, congrFun ht σ⟩

/-- **Under the Galois condition the graphs jointly cover `Spec A ×_{Spec R} Spec A`.** -/
theorem exists_specGraph_eq (x : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    ∃ σ y, specGraph ρ σ y = x := by
  obtain ⟨⟨σ, z⟩, hz⟩ := (sigmaMk (fun _ : G ↦ Spec (.of A))).surjective
    ((galoisSigmaIso ρ h).inv x)
  refine ⟨σ, z, ?_⟩
  rw [sigmaMk_mk] at hz
  rw [← ι_galoisSigmaIso_hom ρ h, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply,
    Iso.inv_hom_id]
  rfl

end Galois

/-! ### The Galois situation in the big fppf site -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hR : B.Contains (Spec (.of R))) (hA : B.Contains (Spec (.of A))) (s : Spec (.of R) ⟶ S)

/-- `Spec R`, as an object of the big fppf site over `S` through the structure morphism `s`. -/
abbrev galoisBaseObj : BigFppfOver B S hS := siteObject B S hS hR s

/-- `Spec A`, as an object of the big fppf site over `S` through `Spec A → Spec R → S`. -/
abbrev galoisCoverObj : BigFppfOver B S hS :=
  siteObject B S hS hA (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ s)

/-- The morphism `Spec A → Spec R` of the big fppf site over `S`. -/
def galoisCoverMap : galoisCoverObj (R := R) B S hS hA s ⟶ galoisBaseObj B S hS hR s :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (by ext : 1; rfl)

/-- The automorphism `Spec σ` of `Spec A`, as a morphism of the big fppf site over `S`. -/
def galoisCoverAut (σ : G) : galoisCoverObj (R := R) B S hS hA s ⟶ galoisCoverObj B S hS hA s :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (ρ σ).toRingEquiv.toRingHom)))
    (by
      ext : 1
      change Spec.map (CommRingCat.ofHom (ρ σ).toRingEquiv.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ s =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ s
      rw [← Category.assoc, specMap_aut_comp_specMap_algebraMap])

/-- In the big fppf site over `S`, the automorphism `Spec σ` of `Spec A` lies over `Spec R`. -/
lemma galoisCoverAut_comp_galoisCoverMap (σ : G) :
    galoisCoverAut ρ B S hS hA s σ ≫ galoisCoverMap B S hS hR hA s =
      galoisCoverMap B S hS hR hA s := by
  ext : 2
  exact specMap_aut_comp_specMap_algebraMap ρ σ

/-- **`Spec A → Spec R` is an fppf covering** of the big fppf site over `S`: it is flat and
surjective because `A` is faithfully flat over `R`, and locally of finite presentation because
`A` is finitely presented over `R`. -/
theorem galoisCoverMap_mem_topology [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A] :
    Sieve.generate (Presieve.singleton (galoisCoverMap B S hS hR hA s)) ∈
      BigFppfOver.topology B S hS (galoisBaseObj B S hS hR s) := by
  have hff : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    (flat_and_surjective_SpecMap_iff _).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance)
  exact Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS _ hff.2 hff.1
    ((LocallyOfFinitePresentation.SpecMap_iff _).2
      (RingHom.finitePresentation_algebraMap.2 inferInstance))

/-- The graph `(id, Spec σ) : Spec A → Spec A ×_{Spec R} Spec A`, in the big fppf site over
`S`. -/
def galoisGraph (σ : G) : galoisCoverObj (R := R) B S hS hA s ⟶
    pullback (galoisCoverMap B S hS hR hA s) (galoisCoverMap B S hS hR hA s) :=
  pullback.lift (𝟙 _) (galoisCoverAut ρ B S hS hA s σ) (by
    rw [Category.id_comp, galoisCoverAut_comp_galoisCoverMap])

/-- On underlying schemes, the graph in the site is the graph of schemes, across the comparison
of the two fibre products. -/
lemma toScheme_map_galoisGraph (σ : G) :
    (BigFppfOver.toScheme B S hS).map (galoisGraph ρ B S hS hR hA s σ) ≫
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) (galoisCoverMap B S hS hR hA s)
        (galoisCoverMap B S hS hR hA s)).hom = specGraph ρ σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp, galoisGraph,
      pullback.lift_fst, CategoryTheory.Functor.map_id]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp, galoisGraph,
      pullback.lift_snd]
    exact (pullback.lift_snd _ _ _).symm

/-- **Under the Galois condition the graphs cover `Spec A ×_{Spec R} Spec A`** in the big fppf
site over `S`: they are open immersions, hence flat and locally of finite presentation, and they
are jointly surjective. -/
theorem galoisGraph_mem_topology [Finite G] (h : Function.Bijective (galoisTensorPi ρ)) :
    Sieve.generate (Presieve.ofArrows (fun _ : G ↦ galoisCoverObj B S hS hA s)
        (galoisGraph ρ B S hS hR hA s)) ∈
      BigFppfOver.topology B S hS
        (pullback (galoisCoverMap B S hS hR hA s) (galoisCoverMap B S hS hR hA s)) := by
  let e := PreservesPullback.iso (BigFppfOver.toScheme B S hS) (galoisCoverMap B S hS hR hA s)
    (galoisCoverMap B S hS hR hA s)
  have hj : ∀ σ, (BigFppfOver.toScheme B S hS).map (galoisGraph ρ B S hS hR hA s σ) =
      specGraph ρ σ ≫ e.inv := fun σ ↦
    (Iso.eq_comp_inv e).2 (toScheme_map_galoisGraph ρ B S hS hR hA s σ)
  refine BigFppfOver.sieve_generate_ofArrows_mem_topology _ _ ?_
  refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x ↦ ?_, fun σ ↦ ?_⟩
  · obtain ⟨σ, y, hy⟩ := exists_specGraph_eq ρ h (e.hom x)
    refine ⟨σ, y, ?_⟩
    rw [hj]
    show e.inv (specGraph ρ σ y) = x
    rw [hy]
    show (e.hom ≫ e.inv) x = x
    rw [Iso.hom_inv_id]
    rfl
  · have hoi : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
        (galoisGraph ρ B S hS hR hA s σ)) := by
      rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ e.hom,
        toScheme_map_galoisGraph]
      exact isOpenImmersion_specGraph ρ h σ
    exact ⟨inferInstance, inferInstance⟩

/-! ### Descent of sections -/

/-- Restriction of a section over `Spec R` to `Spec A`, which is fixed by every `Spec σ`. -/
def galoisRestriction (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w) :
    F.obj (op (galoisBaseObj B S hS hR s)) →
      {y : F.obj (op (galoisCoverObj B S hS hA s)) //
        ∀ σ : G, F.map (galoisCoverAut ρ B S hS hA s σ).op y = y} :=
  fun x ↦ ⟨F.map (galoisCoverMap B S hS hR hA s).op x, fun σ ↦ by
    rw [← Functor.map_comp_apply, ← op_comp, galoisCoverAut_comp_galoisCoverMap]⟩

/-- The underlying section of `AlgebraicGeometry.galoisRestriction` of `x` is the pullback of `x`
along `Spec A → Spec R`. -/
@[simp]
theorem galoisRestriction_coe (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w)
    (x : F.obj (op (galoisBaseObj B S hS hR s))) :
    (galoisRestriction ρ B S hS hR hA s F x : F.obj (op (galoisCoverObj B S hS hA s))) =
      F.map (galoisCoverMap B S hS hR hA s).op x :=
  rfl

/-- **The sheaf-equalizer step**, with no Galois condition: since `Spec A → Spec R` is an fppf
covering, a section of `F(Spec A)` whose pullbacks along any two maps `Z ⟶ Spec A` agreeing over
`Spec R` agree comes from a unique section of `F(Spec R)`. -/
theorem existsUnique_map_galoisCoverMap [Module.FaithfullyFlat R A]
    [Algebra.FinitePresentation R A] {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (y : F.obj (op (galoisCoverObj B S hS hA s)))
    (hy : ∀ {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ galoisCoverObj B S hS hA s),
      p₁ ≫ galoisCoverMap B S hS hR hA s = p₂ ≫ galoisCoverMap B S hS hR hA s →
        F.map p₁.op y = F.map p₂.op y) :
    ∃! x, F.map (galoisCoverMap B S hS hR hA s).op x = y :=
  Presieve.isSheafFor_singleton.1 ((Presieve.isSheafFor_iff_generate _).2
    ((isSheaf_iff_isSheaf_of_type _ _).1 hF _ (galoisCoverMap_mem_topology B S hS hR hA s))) y hy

/-- **Under the Galois condition a fixed section satisfies the equalizer condition**: its
pullbacks along any two maps `Z ⟶ Spec A` agreeing over `Spec R` agree.  The pair factors
through `Spec A ×_{Spec R} Spec A`, which the graphs of the `Spec σ` cover, and on the graph of
`Spec σ` the two pullbacks are the section and its pullback by `Spec σ`. -/
theorem map_galoisCover_eq_of_forall_fixed [Finite G]
    (h : Function.Bijective (galoisTensorPi ρ)) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (y : F.obj (op (galoisCoverObj B S hS hA s)))
    (hy : ∀ σ : G, F.map (galoisCoverAut ρ B S hS hA s σ).op y = y)
    {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ galoisCoverObj B S hS hA s)
    (hp : p₁ ≫ galoisCoverMap B S hS hR hA s = p₂ ≫ galoisCoverMap B S hS hR hA s) :
    F.map p₁.op y = F.map p₂.op y := by
  rw [isSheaf_iff_isSheaf_of_type] at hF
  have hT := (BigFppfOver.topology B S hS).pullback_stable (pullback.lift p₁ p₂ hp)
    (galoisGraph_mem_topology ρ B S hS hR hA s h)
  refine (hF _ hT).isSeparatedFor.ext fun V f hf ↦ ?_
  obtain ⟨V', g, k, hk, hfac⟩ := hf
  obtain ⟨σ⟩ := hk
  have h₁ : f ≫ p₁ = g := by
    simpa [galoisGraph, pullback.lift_fst] using (hfac =≫ pullback.fst _ _).symm
  have h₂ : f ≫ p₂ = g ≫ galoisCoverAut ρ B S hS hA s σ := by
    simpa [galoisGraph, pullback.lift_snd] using (hfac =≫ pullback.snd _ _).symm
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    h₁, h₂, op_comp, Functor.map_comp_apply, hy σ]

/-- **Galois descent of sections of an fppf sheaf.**  Let `A` be a faithfully flat, finitely
presented `R`-algebra with an action of a finite group `G` by `R`-algebra automorphisms for which
`A ⊗[R] A → (G → A)` is bijective.  For every sheaf `F` on the big fppf site over `S`, restriction
along `Spec A → Spec R` is a bijection from `F(Spec R)` onto the sections of `F(Spec A)` fixed by
every `Spec σ`. -/
theorem bijective_galoisRestriction [Module.FaithfullyFlat R A] [Algebra.FinitePresentation R A]
    [Finite G] (h : Function.Bijective (galoisTensorPi ρ))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    Function.Bijective (galoisRestriction ρ B S hS hR hA s F) := by
  refine ⟨fun x₁ x₂ hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := existsUnique_map_galoisCoverMap B S hS hR hA s hF
      (F.map (galoisCoverMap B S hS hR hA s).op x₁) fun p₁ p₂ hp ↦ by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
          ← op_comp, hp]
    exact (ht x₁ rfl).trans (ht x₂ (congrArg Subtype.val hx).symm).symm
  · obtain ⟨t, ht, -⟩ := existsUnique_map_galoisCoverMap B S hS hR hA s hF y.1
      fun p₁ p₂ hp ↦ map_galoisCover_eq_of_forall_fixed ρ B S hS hR hA s h hF y.1 y.2 p₁ p₂ hp
    exact ⟨t, Subtype.ext ht⟩

end AlgebraicGeometry

end
