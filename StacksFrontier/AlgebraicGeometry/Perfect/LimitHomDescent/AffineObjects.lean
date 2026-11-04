module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineCore
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate

/-!
# Stacks 09RE over a directed system of spectra, for objects of `D(𝒪_{Spec R})`

Let `R ⟶ A_i` be a directed system of `R`-algebras with colimit `A`, and consider the system of
spectra `Spec A_i` over `Spec R` with vertex `Spec A`. For objects `E` and `K` of
`D(𝒪_{Spec R})`, `Hom(L(Spec A)^*E, L(Spec A)^*K)` is the filtered colimit of the
`Hom(L(Spec A_i)^*E, L(Spec A_i)^*K)` if either `E` is perfect and `K` lies in
`D_QCoh(𝒪_{Spec R})`, or `E` is pseudo-coherent and `K` lies in `D_QCoh(𝒪_{Spec R})` and has
finite Tor dimension.

## Main results

* `Stacks.LimitHomDescent.Affine.RingSystem.isColim_of_isPerfect`: the first case.
* `Stacks.LimitHomDescent.Affine.RingSystem.isColim_of_isPseudoCoherent`: the second case.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

universe d v u

namespace Stacks.LimitHomDescent.Affine

/-- Pseudo-coherence is invariant under isomorphism in the derived category. -/
theorem isPseudoCoherent_of_iso {X : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u} X)]
    {E E' : DerivedCategory (StrictlyPerfect.OXMod.{u} X)} (e : E ≅ E')
    (h : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E' := by
  obtain ⟨L, hL, ⟨f⟩⟩ := h
  exact ⟨L, hL, ⟨f ≪≫ e⟩⟩

/-- Tor amplitude is invariant under isomorphism in the derived category. -/
theorem hasFiniteTorDimension_of_iso {X : RingedSpace.{u, u}}
    {E E' : DerivedCategory (StrictlyPerfect.OXMod.{u} X)} (e : E ≅ E')
    (h : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension X E) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension X E' := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, fun F i hi => (h F i hi).of_iso
    ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u} X) i).mapIso
      (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.mapIso e).app _)).symm⟩

variable {R A : CommRingCat.{u}}

/-- Extending scalars along `f : R ⟶ A` degreewise sends a complex of projective `R`-modules to a
complex of projective `A`-modules. -/
theorem projective_ext (f : R ⟶ A) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ n : ℤ, Module.Projective R (P.X n)) (n : ℤ) :
    Projective (((ext f).obj P).X n) := by
  have := hP n
  exact (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).map_projective (P.X n) inferInstance

/-- Extending scalars along `f : R ⟶ A` degreewise sends a bounded above complex of projective
`R`-modules to a K-projective complex of `A`-modules. -/
theorem isKProjective_ext (f : R ⟶ A) (P : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [P.IsStrictlyLE d] (hP : ∀ n : ℤ, Module.Projective R (P.X n)) :
    ((ext f).obj P).IsKProjective := by
  have : ∀ n : ℤ, Projective (((ext f).obj P).X n) := projective_ext f P hP
  exact CochainComplex.isKProjective_of_projective _ d

namespace RingSystem

variable {J : Type v} [Preorder J] (S : RingSystem R J) [IsDirected J (· ≤ ·)] [Nonempty J]
  (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
    (fun j (x : S.A j) => S.γ j x))

/-- The affine case at a bounded above complex `P` of finite projective modules and a K-flat
complex `N`, given a finite set `W` of degrees outside of which the vanishing condition holds. -/
private theorem isColim_dT_of_projective
    (hcol : Stacks.IsStagesColimit (fun i j (h : i ≤ j) (x : S.A i) => S.β h x)
      (fun j (x : S.A j) => S.γ j x)) (P N : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (hfin : ∀ n : ℤ, Module.Finite R (P.X n))
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n)) (hN : N.KFlat) (W : Finset ℤ)
    (hW : ∀ n : ℤ, n ∉ W → IsZero (P.X n) ∨
      (IsZero ((S.limCx N).X n) ∧ IsZero ((S.limCx N).X (n - 1)) ∧
        ∀ j, IsZero ((S.stageCx N j).X n) ∧ IsZero ((S.stageCx N j).X (n + 1)))) :
    S.toSchemeSystem.IsColim ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))
      ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj N)) := by
  have : ∀ n : ℤ, Module.Flat R (P.X n) := fun n => by
    have := hproj n
    infer_instance
  have hP : P.KFlat := CochainComplex.KFlat.kFlat_of_flat.{u, u} P b
  have : ∀ j, ((ext (S.φ j)).obj P).IsKProjective := fun j => isKProjective_ext _ P b hproj
  have : ((ext S.φlim).obj P).IsKProjective := isKProjective_ext _ P b hproj
  exact isColim_toSchemeSystem (S := S) (N := N) (hcol := hcol) (P := P) (hP := hP) (hN := hN)
    (W := W) hW fun n => by
      have := hproj n
      have := hfin n
      exact Module.finitePresentation_of_projective R (P.X n)

include hcol in
/-- The affine case at a bounded complex of finite projective modules and a K-flat complex. -/
theorem isColim_dT_of_bounded (P N : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] (hfin : ∀ n : ℤ, Module.Finite R (P.X n))
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n)) (hN : N.KFlat) :
    S.toSchemeSystem.IsColim ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))
      ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj N)) :=
  S.isColim_dT_of_projective hcol P N b hfin hproj hN (Finset.Icc a b) fun n hn => Or.inl <| by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · exact P.isZero_of_isStrictlyGE a n hn
    · exact P.isZero_of_isStrictlyLE b n hn

include hcol in
/-- The affine case at a bounded above complex of finite free modules and a bounded complex of
flat modules. -/
theorem isColim_dT_of_boundedAbove (P N : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] (hfin : ∀ n : ℤ, Module.Finite R (P.X n))
    (hfree : ∀ n : ℤ, Module.Free R (P.X n)) (a' b' : ℤ) [N.IsStrictlyGE a'] [N.IsStrictlyLE b']
    (hNflat : ∀ n : ℤ, Module.Flat R (N.X n)) :
    S.toSchemeSystem.IsColim ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj P))
      ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj N)) := by
  have hproj : ∀ n : ℤ, Module.Projective R (P.X n) := fun n => by
    have := hfree n
    infer_instance
  have : ∀ n : ℤ, Module.Flat R (N.X n) := hNflat
  have hN : N.KFlat := CochainComplex.KFlat.kFlat_of_flat.{u, u} N b'
  have hz : ∀ m : ℤ, (m < a' ∨ b' < m) → IsZero (N.X m) := fun m hm => by
    rcases hm with hm | hm
    · exact N.isZero_of_isStrictlyGE a' m hm
    · exact N.isZero_of_isStrictlyLE b' m hm
  refine S.isColim_dT_of_projective hcol P N b hfin hproj hN (Finset.Icc (a' - 1) (b' + 1))
    fun n hn => Or.inr ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  exact ⟨(resExt S.φlim).map_isZero (hz n (by omega)),
    (resExt S.φlim).map_isZero (hz (n - 1) (by omega)), fun j =>
      ⟨(resExt (S.φ j)).map_isZero (hz n (by omega)),
        (resExt (S.φ j)).map_isZero (hz (n + 1) (by omega))⟩⟩

/-- A K-flat representative of an object of `D(R)`. -/
theorem exists_kFlat_iso (M : DerivedCategory (ModuleCat.{u} R)) :
    ∃ N : CochainComplex (ModuleCat.{u} R) ℤ, N.KFlat ∧
      Nonempty (DerivedCategory.Q.obj N ≅ M) := by
  obtain ⟨N, g, hN, -, hqis, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage M)
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := g)).2 hqis
  exact ⟨N, hN, ⟨asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

include hcol in
/-- **Stacks 09RE over a directed system of spectra, the perfect case.** If `E` is a perfect object
of `D(𝒪_{Spec R})` and `K` has quasi-coherent cohomology sheaves, then
`Hom(L(Spec A)^*E, L(Spec A)^*K)` is the filtered colimit of the
`Hom(L(Spec A_i)^*E, L(Spec A_i)^*K)`. -/
theorem isColim_of_isPerfect (E K : DMod (Spec R))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E)
    (hK : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj K).IsQuasicoherent) :
    S.toSchemeSystem.IsColim E K := by
  obtain ⟨M, ⟨eE⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect (Spec R) E hE)
  have hM : StacksDraft.Perfect.IsPerfect M := (isPerfect_tilde_iff M).1
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (Spec R).toRingedSpace) eE.symm hE)
  obtain ⟨P, a, b, hGE, hLE, hfin, hproj, ⟨eM⟩⟩ := hM
  obtain ⟨M', ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R K hK
  obtain ⟨N, hN, ⟨eN⟩⟩ := exists_kFlat_iso M'
  exact SchemeSystem.IsColim.of_iso_snd E ((tilde.functor R).mapDerivedCategory.mapIso eN ≪≫ eK)
    (SchemeSystem.IsColim.of_iso_fst ((tilde.functor R).mapDerivedCategory.mapIso eM.symm ≪≫ eE)
      (S.isColim_dT_of_bounded hcol P N a b hfin hproj hN))

include hcol in
/-- **Stacks 09RE over a directed system of spectra, the pseudo-coherent case.** If `E` is a
pseudo-coherent object of `D(𝒪_{Spec R})` and `K` has quasi-coherent cohomology sheaves and finite
Tor dimension, then `Hom(L(Spec A)^*E, L(Spec A)^*K)` is the filtered colimit of the
`Hom(L(Spec A_i)^*E, L(Spec A_i)^*K)`. -/
theorem isColim_of_isPseudoCoherent (E K : DMod (Spec R))
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent
      (X := (Spec R).toRingedSpace) E)
    (hK : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj K).IsQuasicoherent)
    (hKt : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension (Spec R).toRingedSpace K) :
    S.toSchemeSystem.IsColim E K := by
  obtain ⟨M, ⟨eE⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R E
    (isQuasicoherentDerived_of_isPseudoCoherent (Spec R) E
      ((Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
        (X := (Spec R).toRingedSpace) E).1 hE))
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M :=
    (isPseudoCoherent_mapDerivedCategory_tilde_iff M).1
      (isPseudoCoherent_of_iso (X := (Spec R).toRingedSpace) eE.symm hE)
  obtain ⟨P, hPff, ⟨eM⟩⟩ := hM
  obtain ⟨b, hb⟩ := hPff.upperBound
  obtain ⟨M', ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R K hK
  have hM' : StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical R M' :=
    (hasFiniteTorDimension_tilde_iff M').1
      (hasFiniteTorDimension_of_iso (X := (Spec R).toRingedSpace) eK.symm hKt)
  obtain ⟨a', b', hab⟩ :=
    (StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
      R M').1 hM'
  obtain ⟨N, hNflat, hNGE, hNLE, ⟨eN⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative R M' a' b').1 hab
  exact SchemeSystem.IsColim.of_iso_snd E
    ((tilde.functor R).mapDerivedCategory.mapIso eN.symm ≪≫ eK)
    (SchemeSystem.IsColim.of_iso_fst ((tilde.functor R).mapDerivedCategory.mapIso eM ≪≫ eE)
      (S.isColim_dT_of_boundedAbove hcol P N b (fun n => (hPff.finiteFree n).1)
        (fun n => (hPff.finiteFree n).2) a' b' hNflat))

end RingSystem

end Stacks.LimitHomDescent.Affine

end
