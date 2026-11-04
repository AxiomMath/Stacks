module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.RingHomPi
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski

/-!
# Separatedness of quasi-coherent descent along a standard fpqc covering of an affine scheme

Stacks 023S asserts, for a standard fpqc covering `{Spec Aₖ ⟶ T}` of an affine scheme `T`, both
that every quasi-coherent descent datum is effective and that the canonical descent functor of
Stacks 023D is fully faithful.  This file proves the *separatedness* half of the second
assertion: the canonical descent functor is **faithful**, equivalently a morphism of
quasi-coherent modules on `T` is determined by its pullbacks along the members of the covering.

The argument is the reduction of Stacks 023S to the case of a single morphism, carried out at
the level of morphisms only, where it needs no gluing.  A finite family of ring maps
`ρ k : R ⟶ A k` factors through its product `π : R ⟶ ∏ₖ A k`, and:

* `π` is faithfully flat as soon as each `ρ k` is flat and the images of the `Spec (A k)` cover
  `Spec R` (`RingHom.FaithfullyFlat.pi`), so pullback along `Spec.map π` is faithful on
  quasi-coherent modules by `Stacks.Descent.faithful_pullbackQcoh`;
* the components `Spec (A k) ⟶ Spec (∏ₖ A k)` are open immersions with covering images, so a
  morphism on `Spec (∏ₖ A k)` is determined by its pullbacks along them, by the Zariski
  separatedness `Stacks.Descent.hom_ext_of_pullback_map_eq`.

## Main results

* `Stacks.Descent.faithful_pullback_of_isIso`: pullback of sheaves of modules along an
  isomorphism of schemes is faithful.
* `Stacks.Descent.iSup_opensRange_specMap_piComponent`: the spectra of the factors of a finite
  product of rings cover the spectrum of the product.
* `Stacks.Descent.hom_ext_of_pullback_specMap_map_eq`: faithfully flat descent of morphisms of
  quasi-coherent modules on affine schemes, in the one-morphism case.
* `Stacks.Descent.hom_ext_of_pullback_map_eq_standard` and
  `Stacks.Descent.hom_ext_of_pullback_map_eq_of_isAffine`: a morphism of quasi-coherent modules
  on an affine scheme is determined by its pullbacks along a finite jointly surjective family of
  flat morphisms from affine schemes.
* `Stacks.Descent.faithful_qcohToDescentData_of_isAffine` and
  `Stacks.Descent.faithful_canonicalDescentFunctor_of_isAffine`: the faithfulness half of
  Stacks 023S, for `Stacks.Descent.qcohPseudofunctor` and for the canonical descent functor of
  Stacks 023D respectively.
* `Stacks.Descent.faithful_qcohToDescentData_of_mem_fpqcPrecoverage`: the same, with the
  hypotheses packaged as membership of `AlgebraicGeometry.Scheme.fpqcPrecoverage`.

## Implementation notes

The index type of the family is taken in `Type u` for the main statements because the coproduct
`∐ fun k ↦ Spec (A k)`, through which `AlgebraicGeometry.sigmaSpec` identifies the spectrum of
the product ring, is only formed for index types in `Type u`.  The versions with a free index
universe are obtained by reindexing along an equivalence with an index type in `Type u`, which is
why they carry no smallness hypothesis beyond finiteness.

`AlgebraicGeometry.sigmaSpec` is used only through its surjectivity on points; the open-immersion
instance for the component maps `Spec.map (Pi.evalRingHom _ k)` is Mathlib's.

## References

* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe v u

namespace Stacks.Descent

/-- Pullback of sheaves of modules along an isomorphism of schemes is faithful: it is one half of
an equivalence, the other half being pullback along the inverse. -/
lemma faithful_pullback_of_isIso {Y Z : Scheme.{u}} (b : Y ⟶ Z) [IsIso b] :
    (Scheme.Modules.pullback b).Faithful :=
  Functor.Faithful.of_comp_iso (G := Scheme.Modules.pullback (inv b)) (H := 𝟭 Z.Modules)
    (Scheme.Modules.pullbackComp (inv b) b ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id b) ≪≫ Scheme.Modules.pullbackId Z)

/-- **Faithfully flat descent of morphisms of quasi-coherent modules on affine schemes.**  A
morphism of quasi-coherent modules on `Spec R` is determined by its pullback along `Spec.map π`
for a faithfully flat ring map `π`.  This is the one-morphism case of the faithfulness half of
Stacks 023S, and is the comonadicity of `Stacks.Descent.pullbackQcoh` read on morphisms. -/
lemma hom_ext_of_pullback_specMap_map_eq {R B : CommRingCat.{u}} (π : R ⟶ B)
    (hπ : π.hom.FaithfullyFlat) {M N : (Spec R).Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] {φ ψ : M ⟶ N}
    (h : (Scheme.Modules.pullback (Spec.map π)).map φ =
      (Scheme.Modules.pullback (Spec.map π)).map ψ) : φ = ψ := by
  have := faithful_pullbackQcoh π hπ
  have key : (ObjectProperty.homMk φ : (⟨M, ‹M.IsQuasicoherent›⟩ :
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory) ⟶
        ⟨N, ‹N.IsQuasicoherent›⟩) = ObjectProperty.homMk ψ :=
    (pullbackQcoh π).map_injective (ObjectProperty.hom_ext _ h)
  exact congrArg InducedCategory.Hom.hom key

section Pi

variable {K : Type u} (A : K → CommRingCat.{u})

/-- The projection onto the `k`-th factor of a product of rings. -/
abbrev piComponent (k : K) : CommRingCat.of (∀ k, (A k : Type u)) ⟶ A k :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k ↦ (A k : Type u)) k)

variable [Finite K]

/-- Every point of the spectrum of a finite product of rings lies in the image of the spectrum of
one of the factors. -/
theorem exists_base_specMap_piComponent_eq (p : Spec (CommRingCat.of (∀ k, (A k : Type u)))) :
    ∃ (k : K) (y : Spec (A k)), (Spec.map (piComponent A k)).base y = p := by
  have hp : (sigmaSpec A).base ((inv (sigmaSpec A)).base p) = p := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  obtain ⟨⟨k, y⟩, hy⟩ := (sigmaMk (fun k ↦ Spec (A k))).surjective ((inv (sigmaSpec A)).base p)
  refine ⟨k, y, ?_⟩
  rw [← hp, ← hy, sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec]

/-- The spectra of the factors of a finite product of rings form an open covering of the spectrum
of the product. -/
theorem iSup_opensRange_specMap_piComponent :
    ⨆ k, (Spec.map (piComponent A k)).opensRange = ⊤ := by
  rw [eq_top_iff]
  intro p _
  obtain ⟨k, y, hy⟩ := exists_base_specMap_piComponent_eq A p
  exact Opens.mem_iSup.2 ⟨k, y, hy⟩

end Pi

/-- The product of a family of ring maps, followed by the projection onto one factor, is that
member of the family. -/
theorem piComponent_comp {R : CommRingCat.{u}} {K : Type u} {A : K → CommRingCat.{u}}
    (ρ : ∀ k, R ⟶ A k) (k : K) :
    CommRingCat.ofHom (RingHom.pi fun k ↦ (ρ k).hom) ≫ piComponent A k = ρ k := rfl

/-- If `f ≫ g = h`, equal pullbacks along `h` of two morphisms give equal pullbacks along `f`
of their pullbacks along `g`. -/
private theorem pullback_map_pullback_map_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (hfg : f ≫ g = h) {M N : Z.Modules} {φ ψ : M ⟶ N}
    (e : (Scheme.Modules.pullback h).map φ = (Scheme.Modules.pullback h).map ψ) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map ψ) := by
  set ε := Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr hfg with hε
  have key : ∀ θ : M ⟶ N, (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map θ) =
      ε.hom.app M ≫ (Scheme.Modules.pullback h).map θ ≫ ε.inv.app N := fun θ ↦ by
    rw [← NatTrans.naturality_assoc]
    simp
  rw [key φ, key ψ, e]

/-- **The faithfulness half of Stacks 023S, in terms of ring maps.**  A morphism of
quasi-coherent modules on `Spec R` is determined by its pullbacks along a finite family of flat
ring maps `ρ k : R ⟶ A k` whose spectra cover `Spec R`. -/
theorem hom_ext_of_pullback_map_eq_standard {R : CommRingCat.{u}} {K : Type u} [Finite K]
    {A : K → CommRingCat.{u}} (ρ : ∀ k, R ⟶ A k) (hflat : ∀ k, (ρ k).hom.Flat)
    (hsurj : ∀ p : PrimeSpectrum R, ∃ k q, PrimeSpectrum.comap (ρ k).hom q = p)
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] {φ ψ : M ⟶ N}
    (h : ∀ k, (Scheme.Modules.pullback (Spec.map (ρ k))).map φ =
      (Scheme.Modules.pullback (Spec.map (ρ k))).map ψ) : φ = ψ := by
  refine hom_ext_of_pullback_specMap_map_eq
    (CommRingCat.ofHom (RingHom.pi fun k ↦ (ρ k).hom))
    (RingHom.FaithfullyFlat.pi _ hflat hsurj) ?_
  refine hom_ext_of_pullback_map_eq (fun k ↦ Spec.map (piComponent A k))
    (iSup_opensRange_specMap_piComponent A) fun k ↦ ?_
  have hk : Spec.map (piComponent A k) ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi fun k ↦ (ρ k).hom)) = Spec.map (ρ k) := by
    rw [← Spec.map_comp, piComponent_comp]
  exact pullback_map_pullback_map_eq _ _ _ hk (h k)

/-- **The faithfulness half of Stacks 023S.**  A morphism of quasi-coherent modules on an affine
scheme `T` is determined by its pullbacks along a finite jointly surjective family of flat
morphisms out of spectra of rings. -/
theorem hom_ext_of_pullback_map_eq_of_isAffine {T : Scheme.{u}} [IsAffine T] {K : Type u}
    [Finite K] {A : K → CommRingCat.{u}} (g : ∀ k, Spec (A k) ⟶ T) [∀ k, Flat (g k)]
    (hsurj : ∀ t : T, ∃ k, t ∈ Set.range (g k).base)
    {M N : T.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] {φ ψ : M ⟶ N}
    (h : ∀ k, (Scheme.Modules.pullback (g k)).map φ = (Scheme.Modules.pullback (g k)).map ψ) :
    φ = ψ := by
  have := faithful_pullback_of_isIso T.isoSpec.inv
  refine (Scheme.Modules.pullback T.isoSpec.inv).map_injective (a₁ := φ) (a₂ := ψ) ?_
  set ρ : ∀ k, Γ(T, ⊤) ⟶ A k := fun k ↦ Spec.preimage (g k ≫ T.isoSpec.hom) with hρdef
  have hρ : ∀ k, Spec.map (ρ k) = g k ≫ T.isoSpec.hom := fun k ↦ Spec.map_preimage _
  have hρ' : ∀ k, Spec.map (ρ k) ≫ T.isoSpec.inv = g k := fun k ↦ by
    rw [hρ k, Category.assoc, T.isoSpec.hom_inv_id, Category.comp_id]
  have hflat : ∀ k, (ρ k).hom.Flat := fun k ↦ by
    have : Flat (Spec.map (ρ k)) := by rw [hρ k]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this
  have hid : ∀ p : PrimeSpectrum Γ(T, ⊤), T.isoSpec.hom.base (T.isoSpec.inv.base p) = p := by
    intro p
    show (T.isoSpec.inv ≫ T.isoSpec.hom).base p = p
    rw [T.isoSpec.inv_hom_id]
    rfl
  have hsurj' : ∀ p : PrimeSpectrum Γ(T, ⊤), ∃ k q, PrimeSpectrum.comap (ρ k).hom q = p := by
    intro p
    obtain ⟨k, z, hz⟩ := hsurj (T.isoSpec.inv.base p)
    refine ⟨k, z, ?_⟩
    have hbase : (Spec.map (ρ k)).base z = T.isoSpec.hom.base ((g k).base z) := by
      rw [hρ k, Scheme.Hom.comp_apply]
    rwa [hz, hid p] at hbase
  have hqc : ∀ P : T.Modules, P.IsQuasicoherent →
      ((Scheme.Modules.pullback T.isoSpec.inv).obj P).IsQuasicoherent := fun P hP ↦
    Stacks.Modules.isQuasicoherent_pullback T.isoSpec.inv P hP
  have := hqc M ‹_›
  have := hqc N ‹_›
  refine hom_ext_of_pullback_map_eq_standard ρ hflat hsurj' fun k ↦ ?_
  exact pullback_map_pullback_map_eq _ _ _ (hρ' k) (h k)

/-- **The faithfulness half of Stacks 023S**, with a free index universe for the covering
family.  A morphism of quasi-coherent modules on an affine scheme `T` is determined by its
pullbacks along a finite jointly surjective family of flat morphisms out of spectra of rings. -/
theorem hom_ext_of_pullback_map_eq_of_isAffine' {T : Scheme.{u}} [IsAffine T] {K : Type v}
    [Finite K] {A : K → CommRingCat.{u}} (g : ∀ k, Spec (A k) ⟶ T) [∀ k, Flat (g k)]
    (hsurj : ∀ t : T, ∃ k, t ∈ Set.range (g k).base)
    {M N : T.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] {φ ψ : M ⟶ N}
    (h : ∀ k, (Scheme.Modules.pullback (g k)).map φ = (Scheme.Modules.pullback (g k)).map ψ) :
    φ = ψ := by
  obtain ⟨K', ⟨e⟩⟩ := Small.equiv_small.{u} (α := K)
  have : Finite K' := e.finite_iff.mp ‹_›
  have : ∀ k : K', Flat (g (e.symm k)) := fun k ↦ inferInstance
  exact hom_ext_of_pullback_map_eq_of_isAffine (A := fun k : K' ↦ A (e.symm k))
    (fun k ↦ g (e.symm k))
    (fun t ↦ (hsurj t).imp' e fun k ht ↦ by rw [e.symm_apply_apply]; exact ht)
    fun k ↦ h (e.symm k)

/-- **The faithfulness half of Stacks 023S for `Stacks.Descent.qcohPseudofunctor`.**  For a
finite jointly surjective family of flat morphisms out of spectra of rings over an affine base,
`CategoryTheory.Pseudofunctor.toDescentData` is faithful. -/
theorem faithful_qcohToDescentData_of_isAffine {T : Scheme.{u}} [IsAffine T] {K : Type v}
    [Finite K] {A : K → CommRingCat.{u}} (g : ∀ k, Spec (A k) ⟶ T) [∀ k, Flat (g k)]
    (hsurj : ∀ t : T, ∃ k, t ∈ Set.range (g k).base) :
    (qcohPseudofunctor.toDescentData g).Faithful where
  map_injective {M N _ _} h := by
    have hM : M.obj.IsQuasicoherent := M.property
    have hN : N.obj.IsQuasicoherent := N.property
    apply ObjectProperty.hom_ext
    refine hom_ext_of_pullback_map_eq_of_isAffine' (M := M.obj) (N := N.obj) g hsurj fun k ↦ ?_
    exact congrArg
      (fun θ ↦ InducedCategory.Hom.hom (Pseudofunctor.DescentData.Hom.hom θ k)) h

/-- **The faithfulness half of Stacks 023S for the canonical descent functor of Stacks 023D.**
For a finite jointly surjective family of flat morphisms out of spectra of rings over an affine
base, `AlgebraicGeometry.canonicalDescentFunctor` is faithful. -/
theorem faithful_canonicalDescentFunctor_of_isAffine {T : Scheme.{u}} [IsAffine T] {K : Type v}
    [Finite K] {A : K → CommRingCat.{u}} (g : ∀ k, Spec (A k) ⟶ T) [∀ k, Flat (g k)]
    (hsurj : ∀ t : T, ∃ k, t ∈ Set.range (g k).base) :
    (canonicalDescentFunctor g).Faithful where
  map_injective {M N φ ψ} h := by
    apply ObjectProperty.hom_ext
    refine hom_ext_of_pullback_map_eq_of_isAffine' g hsurj fun k ↦ ?_
    exact (canonicalDescentFunctor_map_hom_hom g φ k).symm.trans
      ((congrArg (fun θ ↦ θ.hom.hom k) h).trans (canonicalDescentFunctor_map_hom_hom g ψ k))

/-- **The faithfulness half of Stacks 023S**, with the covering hypotheses packaged as
membership of `AlgebraicGeometry.Scheme.fpqcPrecoverage`. -/
theorem faithful_qcohToDescentData_of_mem_fpqcPrecoverage {T : Scheme.{u}} [IsAffine T]
    {K : Type v} [Finite K] {A : K → CommRingCat.{u}} (g : ∀ k, Spec (A k) ⟶ T)
    (hg : Presieve.ofArrows (fun k ↦ Spec (A k)) g ∈ Scheme.fpqcPrecoverage.{u} T) :
    (qcohPseudofunctor.toDescentData g).Faithful := by
  have hg' := (Scheme.ofArrows_mem_precoverage_iff _).1
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hg)
  have : ∀ k, Flat (g k) := hg'.2
  exact faithful_qcohToDescentData_of_isAffine g fun t ↦ (hg'.1 t).imp fun _ h ↦ h

end Stacks.Descent

end

end
