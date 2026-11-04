module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.RingTheory.Henselian.Pair.Nilpotent

/-!
# Monomorphisms locally of finite type

A monomorphism of schemes is separated, because its diagonal is an isomorphism, and it is
injective on points; together with local finite type the latter forces every point to be
isolated in its fibre, so such a morphism is locally quasi-finite.

Over the spectrum of a limit of a sequence of rings with surjective transition maps having
locally nilpotent kernels, a monomorphism locally of finite type through which every stage of
the sequence factors is an isomorphism.

## Main results

* `AlgebraicGeometry.isSeparated_and_locallyQuasiFinite_of_mono`: a monomorphism locally of
  finite type is separated and locally quasi-finite.
* `AlgebraicGeometry.isIso_of_forall_spec_factors_of_isLimit`: over the spectrum of the limit of
  a sequence of rings with surjective transition maps having locally nilpotent kernels, a
  monomorphism locally of finite type through which every stage factors is an isomorphism.

## Implementation notes

As in `AlgebraicGeometry.QuasiFinite.Defs`, local quasi-finiteness is the conjunction of the
typeclasses `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`,
so with local finite type assumed the conclusion records separatedness together with the fibre
condition. Mathlib supplies both halves as instances: `AlgebraicGeometry.isSeparated_of_mono`,
and the chain from `CategoryTheory.Mono` through `AlgebraicGeometry.UniversallyInjective` to
`AlgebraicGeometry.LocallyQuasiFinite`.

## References

* [Stacks Project, Tag 0CT8](https://stacks.math.columbia.edu/tag/0CT8)
* [Stacks Project, Tag 0CTJ](https://stacks.math.columbia.edu/tag/0CTJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A monomorphism of schemes which is locally of finite type is separated and locally
quasi-finite. -/
@[stacks 0CT8]
theorem isSeparated_and_locallyQuasiFinite_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] :
    IsSeparated f ∧ LocallyQuasiFinite f :=
  ⟨inferInstance, inferInstance⟩

section Limit

open CategoryTheory.Limits

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone F)

/-- For `A` the limit of a sequence of surjections with locally nilpotent kernels, an open subset
of `Spec A` containing the image of `Spec A₀ → Spec A` is all of `Spec A`. -/
private lemma eq_top_of_range_spec_π_subset (hc : IsLimit c)
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
      RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom ≤ nilradical (F.obj (.op (n + 1))))
    (U : (Spec c.pt).Opens)
    (hU : Set.range (Spec.map (c.π.app (.op 0))).base ⊆ (U : Set (Spec c.pt))) :
    U = ⊤ := by
  classical
  have hsurj : Function.Surjective (c.π.app (.op 0)).hom :=
    Concrete.surjective_π_app_zero_of_surjective_map hc fun k => (hF k).1
  have hker : RingHom.ker (c.π.app (.op 0)).hom ≤ Ideal.jacobson (⊥ : Ideal c.pt) :=
    (henselianRing_ker_limit_π_of_surjective_of_ker_le_nilradical F c hc hF 0).jac
  apply top_unique
  intro q _
  by_contra hq
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp U.2.isClosed_compl
  have hItop : I ≠ ⊤ := fun htop =>
    Set.nonempty_iff_ne_empty.mp ⟨q, hq⟩
      (hI.trans (PrimeSpectrum.zeroLocus_empty_iff_eq_top.2 htop))
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hItop
  have hMK : RingHom.ker (c.π.app (.op 0)).hom ≤ M := fun x hx =>
    Ring.jacobson_le_of_isMaximal M (by simpa only [Ideal.jacobson_bot] using hker hx)
  have hmem : (⟨M, hM.isPrime⟩ : Spec c.pt) ∈
      Set.range (PrimeSpectrum.comap (c.π.app (.op 0)).hom) := by
    rw [_root_.range_comap_of_surjective _ _ hsurj]
    exact hMK
  have hcompl : (⟨M, hM.isPrime⟩ : Spec c.pt) ∈ (U.carrier)ᶜ := by rw [hI]; exact hIM
  exact hcompl (hU hmem)

/-- Let `A` be the limit of a sequence of rings whose transition maps are surjective with locally
nilpotent kernels. A monomorphism `f : T ⟶ Spec A` locally of finite type through which every
`Spec Aₙ ⟶ Spec A` factors is an isomorphism. -/
@[stacks 0CTJ]
theorem isIso_of_forall_spec_factors_of_isLimit (hc : IsLimit c)
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
      RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom ≤ nilradical (F.obj (.op (n + 1))))
    {T : Scheme.{u}} (f : T ⟶ Spec c.pt) [Mono f] [LocallyOfFiniteType f]
    (hfac : ∀ n : ℕ, ∃ g : Spec (F.obj (.op n)) ⟶ T, g ≫ f = Spec.map (c.π.app (.op n))) :
    IsIso f := by
  classical
  choose g hg using hfac
  have hcompat : ∀ {T : Scheme.{u}} (f : T ⟶ Spec c.pt) [Mono f]
      (g : ∀ n : ℕ, Spec (F.obj (.op n)) ⟶ T),
      (∀ n, g n ≫ f = Spec.map (c.π.app (.op n))) →
      ∀ {i k : ℕᵒᵖ} (a : i ⟶ k), Spec.map (F.map a) ≫ g i.unop = g k.unop := by
    intro T f _ g hg i k a
    apply (cancel_mono f).1
    rw [Category.assoc, hg, hg, ← Spec.map_comp, c.w a]
  have hstepHomeo (n : ℕ) :
      IsHomeomorph (Spec.map (F.map (homOfLE (Nat.le_succ n)).op)).base := by
    refine PrimeSpectrum.isHomeomorph_comap _ (fun x => ?_) (hF n).2
    obtain ⟨y, rfl⟩ := (hF n).1 x
    exact ⟨1, by omega, y, by simp⟩
  have hrangeAll (n : ℕ) : Set.range (g n).base = Set.range (g 0).base := by
    induction n with
    | zero => rfl
    | succ n ih =>
      refine Eq.trans ?_ ih
      rw [← (hstepHomeo n).surjective.range_comp (g (n + 1)).base]
      exact congrArg (fun k : Spec (F.obj (.op n)) ⟶ T => Set.range k.base)
        (hcompat f g hg (homOfLE (Nat.le_succ n)).op)
  obtain ⟨W₀, hW₀c, hW₀o, hW₀r, -⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (isCompact_range (g 0).continuous) isOpen_univ (by simp)
  let V : T.Opens := ⟨W₀, hW₀o⟩
  have hliftRange (n : ℕ) : Set.range (g n).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι, hrangeAll n]
    exact hW₀r
  let g' (n : ℕ) : Spec (F.obj (.op n)) ⟶ V.toScheme :=
    IsOpenImmersion.lift V.ι (g n) (hliftRange n)
  have hg'fac (n : ℕ) : g' n ≫ V.ι = g n := IsOpenImmersion.lift_fac V.ι (g n) (hliftRange n)
  let f' : V.toScheme ⟶ Spec c.pt := V.ι ≫ f
  have hstage (n : ℕ) : g' n ≫ f' = Spec.map (c.π.app (.op n)) := by
    rw [← hg, ← hg'fac, Category.assoc]
  have : Mono f' := inferInstanceAs (Mono (V.ι ≫ f))
  have : LocallyOfFiniteType f' := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ f))
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hW₀c
  obtain ⟨W, j, p, hj, -, hp, hf'⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization f'
  have : IsAffine W := isAffine_of_isAffineHom p
  have hstageW (n : ℕ) : g' n ≫ j ≫ p = Spec.map (c.π.app (.op n)) := by
    rw [← hf', hstage]
  let χ (n : ℕ) : Γ(W, ⊤) ⟶ F.obj (.op n) := Spec.preimage (g' n ≫ j ≫ W.isoSpec.hom)
  have hχmap (n : ℕ) : Spec.map (χ n) = g' n ≫ j ≫ W.isoSpec.hom := Spec.map_preimage _
  let d : Cone F :=
    { pt := Γ(W, ⊤)
      π :=
        { app := fun i => χ i.unop
          naturality := fun i k a => by
            apply Spec.map_injective
            simpa [hχmap] using
              congrArg (fun q => q ≫ j ≫ W.isoSpec.hom) (hcompat f' g' hstage a) |>.symm } }
  let φ : Γ(W, ⊤) ⟶ c.pt := hc.lift d
  have hφ (n : ℕ) : φ ≫ c.π.app (.op n) = χ n := hc.fac d (.op n)
  let ψ : c.pt ⟶ Γ(W, ⊤) := Spec.preimage (W.isoSpec.inv ≫ p)
  have hψmap : Spec.map ψ = W.isoSpec.inv ≫ p := Spec.map_preimage _
  have hψφ : ψ ≫ φ = 𝟙 c.pt := by
    refine hc.hom_ext fun i => ?_
    obtain ⟨n⟩ := i
    have hχ : ψ ≫ χ n = c.π.app (.op n) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hχmap, hψmap]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hstageW n
    rw [Category.assoc, Category.id_comp, hφ n, hχ]
  let h : Spec c.pt ⟶ W := Spec.map φ ≫ W.isoSpec.inv
  have hhp : h ≫ p = 𝟙 (Spec c.pt) := by
    simp only [h]
    rw [Category.assoc, ← hψmap, ← Spec.map_comp, hψφ, Spec.map_id]
  have hstageH (n : ℕ) : Spec.map (c.π.app (.op n)) ≫ h = g' n ≫ j := by
    apply (cancel_mono W.isoSpec.hom).1
    simp only [Category.assoc, h, Iso.inv_hom_id, Category.comp_id]
    rw [← Spec.map_comp, hφ n, hχmap n]
  have hopen : h ⁻¹ᵁ j.opensRange = ⊤ := by
    refine eq_top_of_range_spec_π_subset F c hc hF _ ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨(g' 0).base x,
      (congrArg (fun q : Spec (F.obj (.op 0)) ⟶ W => q.base x) (hstageH 0)).symm⟩
  have hrange : Set.range h.base ⊆ Set.range j.base := by
    rintro _ ⟨y, rfl⟩
    show y ∈ h ⁻¹ᵁ j.opensRange
    simp [hopen]
  have : IsSplitEpi f :=
    IsSplitEpi.mk'
      { section_ := IsOpenImmersion.lift j h hrange ≫ V.ι
        id := by
          calc (IsOpenImmersion.lift j h hrange ≫ V.ι) ≫ f
              = IsOpenImmersion.lift j h hrange ≫ f' := by rw [Category.assoc]
            _ = (IsOpenImmersion.lift j h hrange ≫ j) ≫ p := by rw [hf', Category.assoc]
            _ = h ≫ p := by rw [IsOpenImmersion.lift_fac]
            _ = 𝟙 _ := hhp }
  exact isIso_of_mono_of_isSplitEpi f

end Limit

end AlgebraicGeometry

end
