module

public import StacksFrontier.RingTheory.Tor.LongExactSequence
public import StacksFrontier.RingTheory.Tor.Vanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness is the vanishing of `Tor₁`

Let `R` be a commutative ring and let `M` be an `R`-module. The following are equivalent:

1. `M` is flat over `R`;
2. for every `i > 0` the functor `Tor_i(M, -)` is zero;
3. the functor `Tor₁(M, -)` is zero;
4. `Tor₁(M, R/I) = 0` for every ideal `I ⊆ R`;
5. `Tor₁(M, R/I) = 0` for every finitely generated ideal `I ⊆ R`.

Here `Tor_i(M, N)` is the `i`-th homology of `P_• ⊗ N` for a projective resolution `P_•` of `M`,
that is `((CategoryTheory.Tor' (ModuleCat R) i).obj M).obj N`.

Flatness of `M` gives `Tor₁(M, N) = 0` for every `N`: writing `N` as a quotient of a projective
`F` with kernel `K`, the six term exact sequence reads `Tor₁(M, F) → Tor₁(M, N) → M ⊗ K → M ⊗ F`,
where the first term vanishes because `F` is flat and the last map is injective because `M` is
flat. Vanishing in higher degrees follows by induction on the degree, from the homology sequence
of the short exact sequence of complexes obtained by tensoring a projective resolution of `M` with
`0 → K → F → N → 0`. Conversely, for an ideal `I` the six term exact sequence of
`0 → I → R → R/I → 0` reads `Tor₁(M, R/I) → M ⊗ I → M ⊗ R`, so `Tor₁(M, R/I) = 0` makes
`M ⊗ I → M ⊗ R` injective, and a module for which this holds for every finitely generated ideal
is flat.

## Main results

* `Stacks.Tor.FlatnessCriterion.solution`: the five conditions are equivalent.
* `Module.Flat.tfae_isZero_Tor'`: the five conditions are equivalent.

## Implementation notes

The functor used is `CategoryTheory.Tor'`, which left derives the first variable of the tensor
product, rather than `CategoryTheory.Tor`, which left derives the second. Conditions (2) and (3)
are the vanishing of an object of `ModuleCat R ⥤ ModuleCat R`, which
`CategoryTheory.Functor.isZero_iff` turns into the vanishing of `Tor_i(M, N)` for every `N`.

## References

* [Stacks Project, Tag 00M5](https://stacks.math.columbia.edu/tag/00M5)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace Stacks.Tor.FlatnessCriterion

section LeftDerived

variable {C : Type*} [Category* C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]

/-- Let `T : 0 → G₁ → G₂ → G₃ → 0` be a short complex of additive functors `C ⥤ D` which is short
exact after evaluation at each term of a projective resolution `P` of `M`. If the `i`-th left
derived functor of `G₂` and the `j`-th left derived functor of `G₁` vanish at `M`, where
`i = j + 1`, then so does the `i`-th left derived functor of `G₃`. -/
private lemma isZero_leftDerived_obj_X₃ (T : ShortComplex (C ⥤ D))
    [T.X₁.Additive] [T.X₂.Additive] [T.X₃.Additive]
    {M : C} (P : ProjectiveResolution M)
    (hT : ∀ n : ℕ, (T.map ((evaluation C D).obj (P.complex.X n))).ShortExact)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (h₂ : IsZero ((T.X₂.leftDerived i).obj M)) (h₁ : IsZero ((T.X₁.leftDerived j).obj M)) :
    IsZero ((T.X₃.leftDerived i).obj M) := by
  have hzero : (NatTrans.mapHomologicalComplex T.f (ComplexShape.down ℕ)).app P.complex ≫
      (NatTrans.mapHomologicalComplex T.g (ComplexShape.down ℕ)).app P.complex = 0 := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, T.zero]
    ext n
    simp
  set U : ShortComplex (HomologicalComplex D (ComplexShape.down ℕ)) := ShortComplex.mk _ _ hzero
  have hU : U.ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact U (fun n => hT n)
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj T.X₃ i)
  refine (hU.homology_exact₃ i j hij).isZero_X₂ ?_ ?_
  · exact IsZero.eq_of_src (h₂.of_iso (P.isoLeftDerivedObj T.X₂ i).symm) _ _
  · exact IsZero.eq_of_tgt (h₁.of_iso (P.isoLeftDerivedObj T.X₁ j).symm) _ _

end LeftDerived

section Tor

variable {R : Type u} [CommRing R]

/-- The short exact sequence `0 → ker f → X → Y → 0` attached to an epimorphism `f : X ⟶ Y`. -/
private lemma shortExact_kernelSequence {C : Type*} [Category* C] [Abelian C] {X Y : C}
    (f : X ⟶ Y) [hf : Epi f] : (ShortComplex.kernelSequence f).ShortExact :=
  { exact := ShortComplex.kernelSequence_exact f
    mono_f := inferInstance
    epi_g := hf }

/-- If `f : F ⟶ N` is an epimorphism of `R`-modules, `Tor_i(M, F) = 0` and
`Tor_j(M, ker f) = 0`, where `i = j + 1`, then `Tor_i(M, N) = 0`. -/
private lemma isZero_Tor'_obj_of_epi (M : ModuleCat.{u} R) {F N : ModuleCat.{u} R} (f : F ⟶ N)
    [Epi f] (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (h₂ : IsZero (((Tor' (ModuleCat.{u} R) i).obj M).obj F))
    (h₁ : IsZero (((Tor' (ModuleCat.{u} R) j).obj M).obj (kernel f))) :
    IsZero (((Tor' (ModuleCat.{u} R) i).obj M).obj N) := by
  have hzero : (tensoringRight (ModuleCat.{u} R)).map (ShortComplex.kernelSequence f).f ≫
      (tensoringRight (ModuleCat.{u} R)).map (ShortComplex.kernelSequence f).g = 0 := by
    rw [← Functor.map_comp, ShortComplex.zero]
    ext Y
    simp
  refine isZero_leftDerived_obj_X₃ (ShortComplex.mk _ _ hzero) (projectiveResolution M)
    (fun n => ?_) i j hij h₂ h₁
  have : Module.Projective R ((projectiveResolution M).complex.X n) := inferInstance
  exact (shortExact_kernelSequence f).map_of_exact
    (tensorLeft ((projectiveResolution M).complex.X n))

/-- For a short exact sequence `S` of `R`-modules with `Tor₁(M, S.X₂) = 0`, `Tor₁(M, S.X₃) = 0` iff
`M ◁ S.f` is a monomorphism. -/
private lemma isZero_Tor'_one_obj_X₃_iff_mono {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (M : ModuleCat.{u} R)
    (h : IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj S.X₂)) :
    IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj S.X₃) ↔ Mono (M ◁ S.f) := by
  obtain ⟨δ, hex⟩ := (hS.exists_Tor'_one_composableArrows_exact_and_epi M).1
  refine ⟨fun h₃ => (hex.exact' 2 3 4).mono_g (h₃.eq_of_src _ _), fun hm => ?_⟩
  exact (hex.exact' 1 2 3).isZero_X₂ (h.eq_of_src _ _)
    (zero_of_comp_mono (M ◁ S.f) (hex.toIsComplex.zero 2))

/-- If `M` is flat then `Tor_i(M, N) = 0` for every `i > 0` and every `N`. -/
private lemma isZero_Tor'_succ_obj_of_flat_left (M : ModuleCat.{u} R) [Module.Flat R M] (n : ℕ) :
    ∀ N : ModuleCat.{u} R, IsZero (((Tor' (ModuleCat.{u} R) (n + 1)).obj M).obj N) := by
  induction n with
  | zero =>
    intro N
    refine (isZero_Tor'_one_obj_X₃_iff_mono (shortExact_kernelSequence (Projective.π N)) M
      (isZero_Tor'_succ_obj_of_flat M (Projective.over N) 0)).mpr ?_
    exact preserves_mono_of_preservesLimit (tensorLeft M) _
  | succ n ih =>
    intro N
    exact isZero_Tor'_obj_of_epi M (Projective.π N) (n + 2) (n + 1) rfl
      (isZero_Tor'_succ_obj_of_flat M (Projective.over N) (n + 1)) (ih _)

end Tor

/-- For an `R`-module `M`, the following are equivalent: `M` is flat; `Tor_i(M, -)` is zero for
every `i > 0`; `Tor₁(M, -)` is zero; `Tor₁(M, R/I) = 0` for every ideal `I`; and
`Tor₁(M, R/I) = 0` for every finitely generated ideal `I`. -/
public theorem solution {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    List.TFAE
      [Module.Flat R M,
        ∀ i, 0 < i → IsZero ((Tor' (ModuleCat.{u} R) i).obj M),
        IsZero ((Tor' (ModuleCat.{u} R) 1).obj M),
        ∀ I : Ideal R,
          IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))),
        ∀ I : Ideal R, I.FG →
          IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I)))] := by
  tfae_have 1 → 2 := by
    intro hM i hi
    have : Module.Flat R M := hM
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    exact (Functor.isZero_iff _).mpr (isZero_Tor'_succ_obj_of_flat_left M n)
  tfae_have 2 → 3 := fun h => h 1 one_pos
  tfae_have 3 → 4 := fun h I => h.obj _
  tfae_have 4 → 5 := fun h I _ => h I
  tfae_have 5 → 1 := by
    intro h
    rw [Module.Flat.iff_lTensor_injective]
    intro I hI
    have hzero : ModuleCat.ofHom I.subtype ≫ ModuleCat.ofHom I.mkQ = 0 := by
      ext x
      simp [Ideal.Quotient.eq_zero_iff_mem]
    have hS := ModuleCat.shortComplex_shortExact
      (ShortComplex.mk (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom I.mkQ) hzero)
      (LinearMap.exact_subtype_mkQ I) I.injective_subtype (Submodule.mkQ_surjective I)
    have hmono : Mono (M ◁ ModuleCat.ofHom I.subtype) :=
      (isZero_Tor'_one_obj_X₃_iff_mono hS M
        (isZero_Tor'_succ_obj_of_flat M (ModuleCat.of R R) 0)).mp (h I hI)
    rw [ModuleCat.mono_iff_injective] at hmono
    simpa [ModuleCat.hom_whiskerLeft] using hmono
  tfae_finish

end Stacks.Tor.FlatnessCriterion

open CategoryTheory Limits

namespace Module.Flat

/-- Let `R` be a commutative ring and let `M` be an `R`-module. The following are equivalent:
(1) `M` is flat over `R`; (2) for all `i > 0` the functor `Tor_i(M, -)` is zero; (3) the functor
`Tor₁(M, -)` is zero; (4) `Tor₁(M, R/I) = 0` for all ideals `I ⊆ R`; (5) `Tor₁(M, R/I) = 0` for
all finitely generated ideals `I ⊆ R`. Here `Tor_i(M, -)` is `(Tor' (ModuleCat R) i).obj M`, the
`i`-th left derived functor of `- ⊗ N` evaluated at `M`. -/
@[stacks 00M5, ega "0 6.1.1"]
public theorem tfae_isZero_Tor' {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    List.TFAE
      [Module.Flat R M,
        ∀ i, 0 < i → IsZero ((Tor' (ModuleCat.{u} R) i).obj M),
        IsZero ((Tor' (ModuleCat.{u} R) 1).obj M),
        ∀ I : Ideal R,
          IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I))),
        ∀ I : Ideal R, I.FG →
          IsZero (((Tor' (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ I)))] :=
  Stacks.Tor.FlatnessCriterion.solution M

end Module.Flat
