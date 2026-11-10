module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Morphisms from the spectrum of a limit of thickenings to a coproduct of affine schemes

Let `(Aₙ)` be an inverse system of rings whose transition maps are surjective with nilpotent
kernels and let `A = lim Aₙ`. The spectra `Spec Aₙ` all have the same points as `Spec A₀`. A
compatible family of morphisms `Spec Aₙ ⟶ V` into a coproduct `V = ∐ Wⱼ` of affine schemes
therefore lands, for every `n`, in the finite sub-coproduct of the summands met by the
quasi-compact `Spec A₀`, which is affine; on an affine target such a family is a compatible
family of ring maps, which factors through `A`. So the family comes from a morphism
`Spec A ⟶ V`.

## Main results

* `AlgebraicGeometry.exists_spec_limit_hom_of_isColimit_cofan`: the extension.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The spectrum of a surjective ring map whose kernel is nil is surjective on points. -/
theorem Spec_map_base_surjective_of_ker_le_nilradical {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : Function.Surjective f.hom) (hk : RingHom.ker f.hom ≤ nilradical R) :
    Function.Surjective (Spec.map f).base := by
  intro x
  have h : x ∈ Set.range (PrimeSpectrum.comap f.hom) := by
    rw [range_comap_of_surjective _ _ hf]
    exact PrimeSpectrum.zeroLocus_anti_mono (Set.Subset.trans hk le_rfl) (by
      rw [PrimeSpectrum.zeroLocus_nilradical]; trivial)
  exact h


section Cofan

variable {J : Type u} {W : J → Scheme.{u}} {V : Scheme.{u}} (cW : ∀ j, W j ⟶ V)
  (hV : IsColimit (Cofan.mk V cW))

/-- The comparison of a coproduct of schemes with the chosen one. -/
abbrev cofanIso : ∐ W ≅ V :=
  (colimit.isColimit (Discrete.functor W)).coconePointUniqueUpToIso hV

include hV in
/-- The comparison `cofanIso` carries the coprojection `Sigma.ι W j` to the injection `cW j`. -/
theorem sigmaι_cofanIso_hom (j : J) : Sigma.ι W j ≫ (cofanIso cW hV).hom = cW j :=
  (colimit.isColimit (Discrete.functor W)).comp_coconePointUniqueUpToIso_hom hV ⟨j⟩

include hV in
/-- Each injection `cW j` into a coproduct of schemes is an open immersion. -/
theorem isOpenImmersion_cofan_inj (j : J) : IsOpenImmersion (cW j) := by
  rw [← sigmaι_cofanIso_hom cW hV j]
  have : IsOpenImmersion (Sigma.ι W j) := (sigmaOpenCover W).map_prop j
  infer_instance

include hV in
/-- Every point of a coproduct of schemes lies in the image of some injection `cW j`. -/
theorem exists_mem_range_cofan_inj (v : V) : ∃ j, v ∈ Set.range (cW j) := by
  obtain ⟨w, rfl⟩ := (cofanIso cW hV).hom.homeomorph.surjective v
  obtain ⟨⟨j, x⟩, rfl⟩ := (sigmaMk W).surjective w
  refine ⟨j, x, ?_⟩
  rw [sigmaMk_mk, ← sigmaι_cofanIso_hom cW hV j]
  rfl

include hV in
/-- The images of distinct injections into a coproduct of schemes are disjoint. -/
theorem disjoint_range_cofan_inj {i j : J} (h : i ≠ j) :
    Disjoint (Set.range (cW i)) (Set.range (cW j)) := by
  rw [Set.disjoint_iff]
  rintro v ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
  rw [← sigmaι_cofanIso_hom cW hV i, ← sigmaι_cofanIso_hom cW hV j, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at hy
  have hy' := (cofanIso cW hV).hom.homeomorph.injective hy
  have := (sigmaι_eq_iff W j i y x).1 hy'
  exact h (congrArg Sigma.fst this).symm

include hV in
/-- **A quasi-compact scheme mapping to a coproduct of schemes meets finitely many summands.** -/
theorem exists_finset_range_subset {X : Scheme.{u}} [CompactSpace X] (t : X ⟶ V) :
    ∃ F : Finset J, Set.range t ⊆ ⋃ j ∈ F, Set.range (cW j) := by
  have := isOpenImmersion_cofan_inj cW hV
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun j => t ⁻¹' Set.range (cW j))
    (fun j => (cW j).isOpenEmbedding.isOpen_range.preimage t.continuous) fun x _ => by
      obtain ⟨j, hj⟩ := exists_mem_range_cofan_inj cW hV (t x)
      exact Set.mem_iUnion.2 ⟨j, hj⟩
  refine ⟨F, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  exact Set.mem_iUnion₂.2 ⟨j, hj, hx⟩


include hV in
/-- **A compatible family of morphisms from the spectra of an inverse system of thickenings to a
coproduct of affine schemes comes from the spectrum of the limit.** -/
theorem exists_spec_limit_hom_of_isColimit_cofan [∀ j, IsAffine (W j)]
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (cA : Cone A) (hcA : IsLimit cA)
    (hsurj : ∀ n, Function.Surjective (A.map (homOfLE (Nat.zero_le n)).op).hom)
    (hnil : ∀ n, RingHom.ker (A.map (homOfLE (Nat.zero_le n)).op).hom ≤
      nilradical (A.obj (op n)))
    (t : ∀ n, Spec (A.obj (op n)) ⟶ V)
    (ht : ∀ {i j : ℕ} (f : i ⟶ j), Spec.map (A.map f.op) ≫ t j = t i) :
    ∃ τ : Spec cA.pt ⟶ V, ∀ n, Spec.map (cA.π.app (op n)) ≫ τ = t n := by
  classical
  have := isOpenImmersion_cofan_inj cW hV
  obtain ⟨F, hF⟩ := exists_finset_range_subset cW hV (t 0)
  let G : ∐ (fun j : F => W j.1) ⟶ V := Sigma.desc fun j => cW j.1
  have : ∀ j : F, IsOpenImmersion (cW j.1) := fun j => inferInstance
  have : IsOpenImmersion G := isOpenImmersion_sigmaDesc (fun j : F => W j.1)
    (fun j => cW j.1) fun i j h => disjoint_range_cofan_inj cW hV fun e => h (Subtype.ext e)
  have hrange : ∀ n, Set.range (t n) ⊆ Set.range G := by
    intro n
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := Spec_map_base_surjective_of_ker_le_nilradical _ (hsurj n) (hnil n) x
    have e : t 0 z = t n ((Spec.map (A.map (homOfLE (Nat.zero_le n)).op)).base z) := by
      rw [← ht (homOfLE (Nat.zero_le n))]
      rfl
    obtain ⟨j, hj, y, hy⟩ := Set.mem_iUnion₂.1 (hF ⟨z, rfl⟩)
    refine ⟨Sigma.ι (fun j : F => W j.1) ⟨j, hj⟩ y, ?_⟩
    rw [← e, ← hy, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  let lift : ∀ n, Spec (A.obj (op n)) ⟶ ∐ (fun j : F => W j.1) := fun n =>
    IsOpenImmersion.lift G (t n) (hrange n)
  let ψ : ∀ n, Γ(∐ (fun j : F => W j.1), ⊤) ⟶ A.obj (op n) := fun n =>
    Spec.preimage (lift n ≫ (Scheme.isoSpec _).hom)
  have hψ : ∀ n, Spec.map (ψ n) = lift n ≫ (Scheme.isoSpec _).hom := fun n => Spec.map_preimage _
  have hlift : ∀ {i j : ℕ} (f : i ⟶ j), Spec.map (A.map f.op) ≫ lift j = lift i := fun f =>
    IsOpenImmersion.lift_uniq G _ (hrange _) _ (by
      rw [Category.assoc, IsOpenImmersion.lift_fac, ht])
  have hnat : ∀ {i j : ℕ} (f : i ⟶ j), ψ j ≫ A.map f.op = ψ i := fun f =>
    Spec.map_injective (by rw [Spec.map_comp, hψ, hψ, ← Category.assoc, hlift])
  let cone : Cone A :=
    { pt := Γ(∐ (fun j : F => W j.1), ⊤)
      π := { app := fun n => ψ n.unop
             naturality := fun i j g => by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
               exact (hnat g.unop).symm } }
  refine ⟨Spec.map (hcA.lift cone) ≫ (Scheme.isoSpec _).inv ≫ G, fun n => ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hcA.fac cone (op n)]
  change Spec.map (ψ n) ≫ _ ≫ G = t n
  rw [hψ, Category.assoc, Iso.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

end Cofan

end AlgebraicGeometry

end
