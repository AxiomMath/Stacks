module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TorAmplitude.Module
public import StacksFrontier.RingTheory.WeaklyEtale.Defs
public import StacksFrontier.RingTheory.WeaklyEtale.WeakDimension

@[expose] public section

/-!
# Rings of weak dimension at most one

For a commutative ring `A` the following are equivalent: `A` has weak dimension at most one;
every ideal of `A` is flat; every finitely generated ideal of `A` is flat; every submodule of a
flat `A`-module is flat; and every localization of `A` at a prime ideal is a valuation ring.

## Main results

* `weakDimensionLE_one_tfae`: the five characterizations above are equivalent.

## Implementation notes

Weak dimension is `HasWeakDimensionLE`, which carries the derived tensor product, its
comparison with termwise tensor product, and the universal property certifying that the
comparison exhibits the derived tensor product as a total left derived functor. Those data are
part of the statement, exactly as in the source.

The two implications that involve the derived category are handled by the Tor-dimension
machinery of `StacksDraft.Homology.TorAmplitude`: a module has Tor dimension at most `d`
precisely when it is represented by a complex of flat modules concentrated in degrees `[-d, 0]`.
Going into weak dimension one, a length-one flat resolution is produced by truncating a
projective resolution, whose first cocycle module embeds into a projective module and is
therefore flat. Coming out of weak dimension one, a length-one flat resolution
`0 → C → F → A/I → 0` is compared with the tautological presentation `0 → I → A → A/I → 0`;
since `A` is free the comparison splits, giving a short exact sequence
`0 → I → A × C → F → 0` whose middle and right terms are flat.

A valuation ring in Mathlib is by definition a domain, so the last condition asserts the
existence of a domain structure on each localization together with the valuation-ring property,
as in the source.

## References

* [The Stacks Project, Tag 092S](https://stacks.math.columbia.edu/tag/092S)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-! ### Flatness lemmas -/

/-- A product of two flat modules is flat. -/
private theorem flat_prod {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [Module.Flat A X] [Module.Flat A Y] : Module.Flat A (X × Y) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := X) f hf
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := Y) f hf
  have hsq : (TensorProduct.prodRight A A N' X Y).toLinearMap ∘ₗ
        LinearMap.rTensor (X × Y) f =
      ((LinearMap.rTensor X f).prodMap (LinearMap.rTensor Y f)) ∘ₗ
        (TensorProduct.prodRight A A N X Y).toLinearMap := by
    ext n x <;> simp
  intro z w hzw
  apply (TensorProduct.prodRight A A N X Y).injective
  have key : ((LinearMap.rTensor X f).prodMap (LinearMap.rTensor Y f))
        ((TensorProduct.prodRight A A N X Y) z) =
      ((LinearMap.rTensor X f).prodMap (LinearMap.rTensor Y f))
        ((TensorProduct.prodRight A A N X Y) w) := by
    have hz := LinearMap.congr_fun hsq z
    have hw := LinearMap.congr_fun hsq w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hz hw
    rw [← hz, ← hw, hzw]
  exact Prod.ext (h1 (congrArg Prod.fst key)) (h2 (congrArg Prod.snd key))

/-- The kernel of a surjection between flat modules is flat. -/
@[ega "0 20.6.21" "more general"]
private theorem flat_ker {X Y : Type u} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [Module.Flat A X] [Module.Flat A Y] (g : X →ₗ[A] Y)
    (hg : Function.Surjective g) : Module.Flat A (LinearMap.ker g) :=
  StacksDraft.TorAmplitude.flat_of_shortExact_left _
    (ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero (R := A) (LinearMap.ker g).subtype g
        (LinearMap.ext fun x => x.2))
      (LinearMap.exact_subtype_ker_map g) Subtype.val_injective hg)

/-- If every submodule of a flat module is flat, then any module admitting a monomorphism into
a flat module is flat. -/
private theorem flat_of_mono
    (h : ∀ (M : Type u) [AddCommGroup M] [Module A M],
      Module.Flat A M → ∀ N : Submodule A M, Module.Flat A N)
    {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (hf : Mono f) (hY : Module.Flat A Y) :
    Module.Flat A X := by
  have := h Y hY (LinearMap.range f.hom)
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofInjective f.hom ((ModuleCat.mono_iff_injective f).1 hf))

/-! ### Valuation rings -/

/-- A free ideal of a commutative ring is principal: a basis with two distinct members `b i`,
`b j` would satisfy `b j • b i - b i • b j = 0`, a relation whose coefficients are not both
zero. -/
private theorem ideal_isPrincipal_of_free {R : Type*} [CommSemiring R] (I : Ideal R)
    [Module.Free R I] : I.IsPrincipal := by
  classical
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI
  let b := Module.Free.chooseBasis R I
  obtain ⟨i⟩ := b.index_nonempty
  refine ⟨⟨(b i).val, le_antisymm ?_ ?_⟩⟩
  · intro x hx
    rw [Submodule.mem_span_singleton]
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h : (b i).val • (⟨x, hx⟩ : I) = x • b i := Subtype.ext (mul_comm _ _)
    simpa only [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, mul_comm] using congrArg (fun y : I => b.repr y i) h
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (b i).property)

/-- A local ring all of whose finitely generated ideals are flat is a domain. -/
private theorem isDomain_of_flat_fg_ideals {R : Type*} [CommRing R] [IsLocalRing R]
    (h : ∀ I : Ideal R, I.FG → Module.Flat R I) : IsDomain R := by
  have : NoZeroDivisors R := ⟨by
    intro x y hxy
    by_cases hy : y = 0
    · exact Or.inr hy
    left
    let I := Ideal.span ({y} : Set R)
    have : Module.Flat R I := h I (Submodule.fg_span_singleton y)
    have : Module.Free R I := Module.free_of_flat_of_isLocalRing
    have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr (by
      intro hI
      have : y ∈ I := Ideal.subset_span (Set.mem_singleton y)
      exact hy (by simpa [hI] using this))
    apply eq_of_smul_eq_smul (α := I)
    intro z
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp z.property
    apply Subtype.ext
    change x * z.val = 0 * z.val
    rw [ha, ← mul_assoc, hxy, zero_mul, zero_mul]⟩
  exact NoZeroDivisors.to_isDomain R

/-- A local ring all of whose finitely generated ideals are flat is a valuation ring: such an
ideal is finite and flat, hence free, hence principal, so the ring is Bézout. -/
private theorem valuationRing_of_flat_fg_ideals {R : Type*} [CommRing R] [IsLocalRing R]
    (h : ∀ I : Ideal R, I.FG → Module.Flat R I) :
    ∃ _ : IsDomain R, ValuationRing R := by
  have := isDomain_of_flat_fg_ideals h
  refine ⟨inferInstance, ?_⟩
  have : IsBezout R := ⟨fun I hI => by
    have : Module.Finite R I := Module.Finite.of_fg hI
    have : Module.Flat R I := h I hI
    have : Module.Free R I := Module.free_of_flat_of_isLocalRing
    exact ideal_isPrincipal_of_free I⟩
  infer_instance

/-- If every localization at a prime ideal is a valuation ring, then every ideal is flat:
flatness is local at the maximal ideals, and over a Bézout domain a torsion-free module is
flat. -/
private theorem flat_ideal_of_valuation_localizations {R : Type*} [CommRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime], ∃ _ : IsDomain (Localization.AtPrime p),
      ValuationRing (Localization.AtPrime p)) (I : Ideal R) : Module.Flat R I := by
  apply Module.flat_of_isLocalized_maximal R I
    (fun p _ => I.localized' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p)))
    (fun p _ => I.toLocalized' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p)))
  intro p hp
  obtain ⟨_, _⟩ := h p
  have : Module.Flat (Localization.AtPrime p)
      (I.localized' (Localization.AtPrime p) p.primeCompl
        (Algebra.linearMap R (Localization.AtPrime p))) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  exact Module.Flat.trans R (Localization.AtPrime p) _

/-- If every submodule of a flat module is flat, then every localization at a prime ideal is a
valuation ring: an ideal of the localization is the localization of its restriction, which is a
submodule of the flat module `Localization.AtPrime p`. -/
private theorem valuation_localizations_of_flat_submodules {R : Type u} [CommRing R]
    (h : ∀ (M : Type u) [AddCommGroup M] [Module R M],
      Module.Flat R M → ∀ N : Submodule R M, Module.Flat R N)
    (p : Ideal R) [p.IsPrime] :
    ∃ _ : IsDomain (Localization.AtPrime p), ValuationRing (Localization.AtPrime p) := by
  apply valuationRing_of_flat_fg_ideals
  intro I _
  have : Module.Flat R I := h (Localization.AtPrime p)
    (IsLocalization.flat (Localization.AtPrime p) p.primeCompl) (I.restrictScalars R)
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl I).mpr
    inferInstance

/-! ### Length-one flat resolutions -/

section Derived

variable {derivedTensor : DerivedCategory (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A)}
  (comparison : ∀ N : ModuleCat.{u} A,
    DerivedCategory.Q ⋙
        derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
      ((tensoringRight (ModuleCat.{u} A)).obj N).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ N : ModuleCat.{u} A,
    (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
      (comparison N)
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))

/-- A module of Tor dimension at most one sits in a short exact sequence `0 → C → F → M → 0`
with `C` and `F` flat.

A flat representative of `M[0]` concentrated in degrees `[-1, 0]` is a two-term complex
`C → F`; the first cohomology of the representative vanishes, which makes the differential a
monomorphism, and the zeroth cohomology is `M`, which identifies `M` with the cokernel of the
differential. -/
@[sga "6 I 5.4" "special case"]
private theorem exists_flat_presentation (M : ModuleCat.{u} A)
    (hM : HasTorDimensionLE derivedTensor comparison isLeftDerived M 1) :
    ∃ (C F : ModuleCat.{u} A) (ι : C ⟶ F) (φ : F ⟶ M),
      Module.Flat A C ∧ Module.Flat A F ∧ Function.Injective ι.hom ∧
        Function.Surjective φ.hom ∧
        LinearMap.range ι.hom = LinearMap.ker φ.hom := by
  obtain ⟨E, hEflat, hEGE, hELE, ⟨e⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorDimensionLE_iff_hasFlatRepresentative
      comparison isLeftDerived M 1).1.mp hM
  have hz2 : IsZero (E.X (-2)) := CochainComplex.isZero_of_isStrictlyGE E (-1) (-2) (by omega)
  have hz1 : IsZero (E.X 1) := CochainComplex.isZero_of_isStrictlyLE E 0 1 (by omega)
  have hd2 : E.d (-2) (-1) = 0 := hz2.eq_of_src _ _
  have hd0 : E.d 0 1 = 0 := hz1.eq_of_tgt _ _
  -- compare the cohomology of `E` with that of the single complex on `M`
  have hiso : ∀ i : ℤ,
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M).homology i ≅ E.homology i :=
    fun i =>
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app _).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
          (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).symm ≪≫ e) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app E
  have hHm1 : IsZero (E.homology (-1)) :=
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M (-1)
      (by omega)).of_iso (hiso (-1)).symm
  have hop : E.opcycles 0 ≅ M :=
    (E.isoHomologyι 0 1 (by simp) hd0).symm ≪≫ (hiso 0).symm ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M
  -- the differential `E^{-1} ⟶ E^0` is a monomorphism
  have hmono : Mono (E.d (-1) 0) := by
    have h1 : IsIso (E.pOpcycles (-1)) := E.isIso_pOpcycles (-2) (-1) (by simp) hd2
    have h2 : Mono (E.fromOpcycles (-1) 0) :=
      Preadditive.mono_of_isZero_kernel' _ (E.homologyIsKernel (-1) 0 (by simp)) hHm1
    rw [← E.p_fromOpcycles (-1) 0]
    exact mono_comp _ _
  -- the induced short exact sequence
  have hT : (ShortComplex.mk (E.d (-1) 0) (E.pOpcycles 0)
      (E.d_pOpcycles (-1) 0)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (E.opcyclesIsCokernel (-1) 0 (by simp))
      mono_f := hmono
      epi_g := inferInstance }
  refine ⟨E.X (-1), E.X 0, E.d (-1) 0, E.pOpcycles 0 ≫ hop.hom, hEflat _, hEflat _,
    (ModuleCat.mono_iff_injective _).1 hmono, ?_, ?_⟩
  · exact (ModuleCat.epi_iff_surjective _).1 (epi_comp _ _)
  · have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hT.exact
    rw [LinearMap.exact_iff] at hex
    rw [ModuleCat.hom_comp, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot_of_injective
        ((ModuleCat.mono_iff_injective hop.hom).1 inferInstance))]
    exact hex.symm

/-- If every submodule of a flat module is flat, then every module has Tor dimension at most
one.

A projective resolution `P` of `M` is truncated at degree `-1`. Its degree `-1` opcycles embed
into the projective module `P^0`, because `P` is exact in degree `-1`, and are therefore flat;
so the truncation is a complex of flat modules concentrated in degrees `[-1, 0]` representing
`M[0]`. -/
private theorem hasTorDimensionLE_one_of_flat_submodules
    (h : ∀ (M : Type u) [AddCommGroup M] [Module A M],
      Module.Flat A M → ∀ N : Submodule A M, Module.Flat A N)
    (M : ModuleCat.{u} A) :
    HasTorDimensionLE derivedTensor comparison isLeftDerived M 1 := by
  refine (StacksDraft.TorAmplitude.hasTorDimensionLE_iff_hasFlatRepresentative
    comparison isLeftDerived M 1).1.mpr ?_
  set R := ProjectiveResolution.of M
  set P := R.cochainComplex
  have hLE : P.IsStrictlyLE 0 := inferInstance
  have hGE : P.IsGE 0 := inferInstance
  have hflat : ∀ i, Module.Flat A (P.X i) := fun i => inferInstance
  have hex : P.ExactAt (-1) := (CochainComplex.isGE_iff P 0).1 hGE (-1) (by omega)
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hex
  have hopc : Module.Flat A (P.opcycles (-1)) :=
    flat_of_mono h (P.fromOpcycles (-1) 0)
      (Preadditive.mono_of_isZero_kernel' _ (P.homologyIsKernel (-1) 0 (by simp)) hex)
      (hflat 0)
  have hGE' : P.IsGE (-1) := P.isGE_of_ge (-1) 0 (by omega)
  have eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M :=
    asIso (DerivedCategory.Q.map R.π') ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).symm
  have hqi : QuasiIso (P.πTruncGE (-1)) := inferInstance
  refine ⟨P.truncGE (-1), StacksDraft.TorAmplitude.flat_truncGE P (-1), ?_,
    StacksDraft.TorAmplitude.truncGE_isStrictlyLE P (-1) 0 hLE,
    ⟨eP.symm ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE (-1)))⟩⟩
  · simpa using (inferInstance : (P.truncGE (-1)).IsStrictlyGE (-1))

end Derived

/-- If the cyclic module `A ⧸ I` admits a short exact sequence `0 → C → F → A ⧸ I → 0` with `C`
and `F` flat, then the ideal `I` itself is flat.

This compares the given presentation with the tautological one, `0 → I → A → A ⧸ I → 0`. Lift
the generator: choose `f₀ : F` above `1 ∈ A ⧸ I`. Then `ψ (a, c) = a • f₀ - ι c` is a surjection
`A × C → F`, its source and target are flat, so its kernel is flat, and the first projection
identifies that kernel with `I`. -/
private theorem flat_ideal_of_flat_presentation (I : Ideal A) {C F : ModuleCat.{u} A}
    (ι : C ⟶ F) (φ : F ⟶ ModuleCat.of A (A ⧸ I)) (hC : Module.Flat A C)
    (hF : Module.Flat A F) (hι : Function.Injective ι.hom) (hφ : Function.Surjective φ.hom)
    (hrange : LinearMap.range ι.hom = LinearMap.ker φ.hom) :
    Module.Flat A I := by
  obtain ⟨f₀, hf₀⟩ := hφ (Submodule.mkQ I 1)
  set ψ : A × C →ₗ[A] F :=
    (LinearMap.toSpanSingleton A F f₀).comp (LinearMap.fst A A C) -
      ι.hom.comp (LinearMap.snd A A C)
  -- `φ` sends `a • f₀` to the class of `a`
  have hφsmul : ∀ a : A, φ.hom (a • f₀) = Submodule.mkQ I a := fun a => by
    rw [map_smul, hf₀, ← map_smul, smul_eq_mul, mul_one]
  have hψsurj : Function.Surjective ψ := by
    intro f
    obtain ⟨a, ha⟩ := (Submodule.mkQ_surjective I) (φ.hom f)
    have : a • f₀ - f ∈ LinearMap.ker φ.hom := by
      simp only [LinearMap.mem_ker, map_sub, hφsmul, ha, sub_self]
    obtain ⟨c, hc⟩ := hrange ▸ this
    exact ⟨(a, c), by simp [ψ, hc]⟩
  -- the first projection identifies `ker ψ` with `I`
  set θ : LinearMap.ker ψ →ₗ[A] A :=
    (LinearMap.fst A A C).comp (Submodule.subtype (LinearMap.ker ψ))
  have hker : ∀ p : A × C, p ∈ LinearMap.ker ψ ↔ p.1 • f₀ = ι.hom p.2 := fun p => by
    simp [ψ, sub_eq_zero]
  have hmem : ∀ a : A, a • f₀ ∈ LinearMap.range ι.hom ↔ a ∈ I := fun a => by
    rw [hrange, LinearMap.mem_ker, hφsmul, ← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hθinj : Function.Injective θ := by
    intro x y hxy
    have hx := (hker x).1 x.2
    have hy := (hker y).1 y.2
    refine Subtype.ext (Prod.ext hxy (hι ?_))
    rw [← hx, ← hy, show (x : A × C).1 = (y : A × C).1 from hxy]
  have hθrange : LinearMap.range θ = I := by
    apply le_antisymm
    · rintro a ⟨x, rfl⟩
      exact (hmem _).1 ⟨(x : A × C).2, ((hker x).1 x.2).symm⟩
    · intro a ha
      obtain ⟨c, hc⟩ := (hmem a).2 ha
      exact ⟨⟨(a, c), (hker _).2 hc.symm⟩, rfl⟩
  have : Module.Flat A (A × C) := flat_prod
  have := flat_ker ψ hψsurj
  exact Module.Flat.of_linearEquiv
    ((LinearEquiv.ofEq _ _ hθrange.symm).trans (LinearEquiv.ofInjective θ hθinj).symm)

/-! ### Stacks 092S -/

/-- **Stacks Tag 092S.** For a commutative ring, weak dimension at most one, flatness of all
ideals, flatness of all finitely generated ideals, flatness of submodules of flat modules, and
the valuation-ring property for all localizations at prime ideals are equivalent. -/
@[stacks 092S]
theorem weakDimensionLE_one_tfae
    (A : Type u) [CommRing A]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        ((tensoringRight (ModuleCat.{u} A)).obj N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    List.TFAE
      [ HasWeakDimensionLE derivedTensor comparison isLeftDerived 1,
        ∀ I : Ideal A, Module.Flat A I,
        ∀ I : Ideal A, I.FG → Module.Flat A I,
        ∀ (M : Type u) [AddCommGroup M] [Module A M],
          Module.Flat A M → ∀ N : Submodule A M, Module.Flat A N,
        ∀ (p : Ideal A) [p.IsPrime],
          ∃ _ : IsDomain (Localization.AtPrime p),
            ValuationRing (Localization.AtPrime p) ] := by
  tfae_have 1 → 2 := by
    intro h1 I
    obtain ⟨C, F, ι, φ, hC, hF, hι, hφ, hrange⟩ :=
      exists_flat_presentation comparison isLeftDerived (ModuleCat.of A (A ⧸ I))
        (h1 (ModuleCat.of A (A ⧸ I)))
    exact flat_ideal_of_flat_presentation I ι φ hC hF hι hφ hrange
  tfae_have 2 → 3 := fun h I _ => h I
  tfae_have 3 → 4 := by
    intro h M _ _ _ N
    exact flat_submodule_of_flat_of_weakDimensionLE_one h N
  tfae_have 4 → 5 := valuation_localizations_of_flat_submodules
  tfae_have 5 → 2 := flat_ideal_of_valuation_localizations
  tfae_have 4 → 1 := fun h M =>
    hasTorDimensionLE_one_of_flat_submodules comparison isLeftDerived h M
  tfae_finish

end
