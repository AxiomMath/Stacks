module

public import StacksFrontier.Homology.Perfect.ProjectiveAmplitude
public import StacksFrontier.Homology.PseudoCoherent.Characterization

@[expose] public section

/-!
# Perfectness passes to retracts over an arbitrary ring

Let `R` be a ring, not assumed commutative, and let `D(R)` be the derived category of `R`-modules.
A retract in `D(R)` of a perfect object is again perfect. Together with the two-out-of-three
property of perfectness in a distinguished triangle this is the last of the closure properties
needed to identify the perfect objects with the triangulated envelope of the regular module, and
hence with the compact objects.

The argument runs through projective amplitude rather than Tor amplitude, and that is the whole
point: `StacksDraft.Perfect.isPerfect_of_biproduct` ([stacks 066S]) reaches the same conclusion
by descending a flat representative to a small commutative coefficient ring, and
`Module.Flat` — hence every notion of Tor amplitude in this tree — is available only over a
commutative base. Projective amplitude is detected by vanishing of `Ext` groups
([stacks 0A5P], `StacksDraft.ProjectiveAmplitude`), and `Ext` out of a retract is a quotient of
`Ext` out of the ambient object, so the detection transports with no commutativity anywhere.

## Main results

* `StacksDraft.Perfect.isPseudoCoherent_of_isPerfect`: a perfect object is pseudo-coherent.
* `StacksDraft.Perfect.isPerfect_of_pseudoCoherent_of_ext_endpoint_vanishing`: a pseudo-coherent
  object living in degrees `≥ a` whose `Ext^{-a + 1}` vanishes against every module is perfect.
* `StacksDraft.Perfect.isPerfect_of_retract`: a retract of a perfect object is perfect.

## Implementation notes

The ring lives in `Type u` and the modules in `Type (max u v)`, the convention of
`StacksDraft.Perfect.isPerfect_iff_isCompactObject_max`; taking `v := u` specialises every result
below to modules in the universe of the ring. The one place the convention is forced is
`StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective`,
whose recognition of pseudo-coherence from a bounded above finite projective representative is
stated there, and which needs a copy of the ring inside the module universe.

The second result above is the noncommutative part of [stacks 0G9A] (1) ⟸ (5): it recognises a
perfect object among the pseudo-coherent ones from a single `Ext` degree. Only the direction
producing perfectness is proved here, since that is what the retract argument consumes, and only
the finiteness bookkeeping distinguishes it from
`StacksDraft.ProjectiveAmplitude.hasProjectiveAmplitude_of_endpointVanishing`: the truncation of a
finite projective representative has finitely generated terms, the one in degree `a` because the
opcycles there are a quotient of a finitely generated module.

## References

* [Stacks Project, Tag 066S](https://stacks.math.columbia.edu/tag/066S)
* [Stacks Project, Tag 0A5P](https://stacks.math.columbia.edu/tag/0A5P)
* [Stacks Project, Tag 0G9A](https://stacks.math.columbia.edu/tag/0G9A)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

variable {R : Type u} [Ring R]

/-- A perfect object is pseudo-coherent: a bounded complex of finite projective modules is in
particular a bounded above one. -/
theorem isPseudoCoherent_of_isPerfect (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsPerfect K) : PseudoCoherence.IsPseudoCoherent K := by
  obtain ⟨P, a, b, hPge, hPle, hPfin, hPproj, ⟨eP⟩⟩ := hK
  exact (PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
    K 0).2.1.mpr ⟨P, ⟨b, hPle⟩, fun n => ⟨hPfin n, hPproj n⟩, ⟨eP.symm⟩⟩

/-- A pseudo-coherent object of `D(R)` whose cohomology vanishes below `a` and whose
`Ext^{-a + 1}(K, N)` vanishes for every module `N` is perfect.

A bounded above finite projective representative `E` of `K` has projective degree-`a` opcycles by
the `Ext` criterion of [stacks 0A5P], and those opcycles are finitely generated because they are a
quotient of `E^a`; so the truncation `σ_{≥ a} E`, which represents `K` since `K` lives in degrees
`≥ a`, is a bounded complex of finite projective modules. -/
theorem isPerfect_of_pseudoCoherent_of_ext_endpoint_vanishing
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ)
    (hK : PseudoCoherence.IsPseudoCoherent K) (hGE : K.IsGE a)
    (hext : ∀ N : ModuleCat.{max u v} R, Subsingleton (DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) (-a + 1))) :
    IsPerfect K := by
  have : Small.{max u v} R := small_max R
  obtain ⟨E, ⟨bE, hEle⟩, hEfinproj, ⟨eE⟩⟩ :=
    PseudoCoherence.finiteProjectiveRepresentative_of_pseudoCoherent hK
  have : E.IsStrictlyLE bE := hEle
  have : ∀ i, CategoryTheory.Projective (E.X i) := by
    intro i
    let : Module.Projective R (E.X i) := (hEfinproj i).2
    exact (E.X i).projective_of_categoryTheory_projective
  have hEGE : E.IsGE a := (DerivedCategory.isGE_Q_obj_iff E a).mp
    (DerivedCategory.TStructure.t.isGE_of_iso eE.symm a)
  have : QuasiIso (E.πTruncGE a) := (E.quasiIso_πTruncGE_iff a).2 hEGE
  have hopproj : CategoryTheory.Projective (E.opcycles a) :=
    StacksDraft.ProjectiveDimension.opcycles_projective_of_ext_subsingleton E K eE a bE hext
  let hopfin : Module.Finite R (E.opcycles a) :=
    let : Module.Finite R (E.X a) := (hEfinproj a).1
    Module.Finite.of_surjective (ModuleCat.Hom.hom (E.pOpcycles a))
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have hsub : ∀ i < a, Subsingleton ((E.truncGE a).X i) := fun i hi =>
    ModuleCat.isZero_iff_subsingleton.mp ((E.truncGE a).isZero_of_isStrictlyGE a i hi)
  refine ⟨E.truncGE a, a, bE, inferInstance, inferInstance, ?_, ?_,
    ⟨eE.symm ≪≫ asIso (DerivedCategory.Q.map (E.πTruncGE a))⟩⟩
  · intro i
    rcases lt_trichotomy i a with hi | hi | hi
    · have := hsub i hi
      infer_instance
    · subst i
      exact Module.Finite.equiv (E.truncGEXIsoOpcycles a).toLinearEquiv.symm
    · let : Module.Finite R (E.X i) := (hEfinproj i).1
      exact Module.Finite.equiv (E.truncGEXIso a i hi).toLinearEquiv.symm
  · intro i
    rcases lt_trichotomy i a with hi | hi | hi
    · have := hsub i hi
      infer_instance
    · subst i
      exact (IsProjective.iff_projective ((E.truncGE a).X a)).mpr
        (CategoryTheory.Projective.of_iso (E.truncGEXIsoOpcycles a).symm hopproj)
    · let : Module.Projective R (E.X i) := (hEfinproj i).2
      exact Module.Projective.of_equiv (E.truncGEXIso a i hi).toLinearEquiv.symm

/-- A retract of a perfect object of `D(R)` is perfect, with no commutativity assumption on `R`.

The retract `X` of a perfect `Y` inherits the cohomology vanishing of `Y` below the lower end `a`
of a bounded finite projective representative, and inherits the vanishing of `Ext^{-a + 1}`
because precomposition with `X ⟶ Y` surjects `Ext` out of `Y` onto `Ext` out of `X`. It is
pseudo-coherent because the retract splits `Y` as a biproduct `X ⊞ Z` and pseudo-coherence passes
to biproduct summands ([stacks 064X]). -/
theorem isPerfect_of_retract {X Y : DerivedCategory (ModuleCat.{max u v} R)}
    (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) (hY : IsPerfect Y) : IsPerfect X := by
  obtain ⟨P, a, b, hPge, hPle, hPfin, hPproj, ⟨eP⟩⟩ := hY
  have : P.IsStrictlyGE a := hPge
  have : P.IsStrictlyLE b := hPle
  have hYamp : ProjectiveAmplitude.HasProjectiveAmplitude Y a b :=
    ⟨P, ⟨eP.symm⟩, hPproj, hPge, hPle⟩
  have hYGE : Y.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eP.symm a
  have hXGE : X.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro n hn
    have : IsSplitMono f := ⟨⟨⟨g, hfg⟩⟩⟩
    exact ((DerivedCategory.isGE_iff Y a).mp hYGE n hn).of_mono
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map f)
  have hext : ∀ N : ModuleCat.{max u v} R, Subsingleton (DerivedCategory.Ext X
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) (-a + 1)) := by
    intro N
    have : Subsingleton (Y ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N)⟦-a + 1⟧) :=
      StacksDraft.ProjectiveDimension.ext_vanishes_of_hasProjectiveAmplitude hYamp N (-a + 1)
        (by simp only [Set.mem_Icc, not_and_or, not_le]; right; omega)
    exact Function.Surjective.subsingleton (f := (f ≫ ·))
      fun u => ⟨g ≫ u, by simp [← Category.assoc, hfg]⟩
  obtain ⟨Z, q, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  have : IsSplitMono (f⟦(1 : ℤ)⟧') :=
    ⟨⟨⟨g⟦(1 : ℤ)⟧', by simp [← CategoryTheory.Functor.map_comp, hfg]⟩⟩⟩
  have hzero : h = 0 := by
    have hz := Pretriangulated.comp_distTriang_mor_zero₃₁ _ hT
    simp only [Pretriangulated.Triangle.mk_mor₃, Pretriangulated.Triangle.mk_mor₁,
      Pretriangulated.Triangle.mk_obj₁] at hz
    exact (cancel_mono (f⟦(1 : ℤ)⟧')).1 (by simpa using hz)
  obtain ⟨e, -, -⟩ := Pretriangulated.exists_iso_binaryBiproduct_of_distTriang _ hT hzero
  have hXZ : IsPerfect (X ⊞ Z) := ⟨P, a, b, hPge, hPle, hPfin, hPproj, ⟨e.symm ≪≫ eP⟩⟩
  have hXpc : PseudoCoherence.IsPseudoCoherent X :=
    ((_root_.PseudoCoherence.isPseudoCoherentFrom_and_pseudoCoherent_of_biproduct X Z 0).2
      (isPseudoCoherent_of_isPerfect _ hXZ)).1
  exact isPerfect_of_pseudoCoherent_of_ext_endpoint_vanishing X a hXpc hXGE hext

end StacksDraft.Perfect

end
