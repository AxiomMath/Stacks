module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonCoherentCharacterization
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.QuasicoherentRepresentative
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.TwistCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CoherentQuotientOfTwists
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentBiproduct
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeDevissage
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Homology.PseudoCoherent.Triangle

/-!
# Derived global sections of a pseudo-coherent complex on projective space

Let `A` be a commutative ring, `n` a natural number and `π : ℙⁿ_A ⟶ Spec A` the structure
morphism. If `F` is a pseudo-coherent object of `D(𝒪_{ℙⁿ_A})`, then `RΓ_A(F)` is a
pseudo-coherent object of `D(A)`. This is the pseudo-coherence half of [Stacks, Tag 0CSD] for the
flat proper morphism of finite presentation `π`.

## Main results

All in the namespace `AlgebraicGeometry.ProjectiveSpaceDirectImage`.

* `exists_singleFunctor_twists_epi`: the top cohomology sheaf of a pseudo-coherent object is hit,
  in the derived category, by a finite sum of twists of the structure sheaf placed in the top
  degree.
* `isPseudoCoherent_derivedGlobalSectionsOver_of_isPseudoCoherent`: `RΓ_A(F)` is pseudo-coherent
  for every pseudo-coherent `F`.

## The proof

`F` is bounded above, its top cohomology sheaf `H^j(F)` is of finite type ([Stacks, Tag 08DN]
part (1)), and `F` is represented by a complex of quasi-coherent modules ([Stacks, Tag 08DB]).
A quasi-coherent submodule of finite type of the cycles in degree `j` maps onto `H^j(F)`
([Stacks, Tag 01PG]), and is a quotient of a finite sum `S` of twists `𝒪(d)` ([Stacks, Tag 01YS]
part (1)), which gives a morphism `S[-j] ⟶ F` surjective on `H^j`. Its cone is again
pseudo-coherent ([Stacks, Tag 08CD]) and has no cohomology from degree `j` on. Since `RΓ_A(S[-j])`
is pseudo-coherent ([Stacks, Tag 01XT]) and `RΓ_A` has cohomological dimension `n` on
`D_QCoh(𝒪_{ℙⁿ_A})` ([Stacks, Tag 08D4]), induction on the number of steps shows that `RΓ_A(F)` is
`m`-pseudo-coherent for every `m`.

The derived categories are the standard model `HasDerivedCategory.standard`, at a raised
priority. The locally small model enters only through
`AlgebraicGeometry.exists_quasicoherent_representative`, which is stated at an arbitrary model.

## References

* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 08DB](https://stacks.math.columbia.edu/tag/08DB)
* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.ProjectiveSpaceDirectImage

attribute [local instance 100000] HasDerivedCategory.standard

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver tensorPowModuleProjectiveTwistIso)

variable {A : Type u} [CommRing A] (n : ℕ)

/-! ### Twists placed in one degree -/

/-- A twist `𝒪(d)` placed in degree `j` is `m`-pseudo-coherent for every `m`: it is perfect. -/
theorem isPseudoCoherentFrom_singleFunctor_twistOver (d j m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace)
      ((DerivedCategory.singleFunctor
        (StrictlyPerfect.OXMod (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) j).obj
        (twistOver n (Spec (.of A)) d)) m :=
  @RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero
    (projectiveSpaceOver n (Spec (.of A))).toRingedSpace _ (twistOver n (Spec (.of A)) d) m j
    ((RingedSpace.IsPerfect.isPseudoCoherent
      (Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.isPerfect_singleFunctor_twistOver
        n (Spec (.of A)) d)).isPseudoCoherentFrom (m - j))

/-- A twist `𝒪(d)` placed in degree `j`, as an object of the derived category of
`Scheme.Modules`, is `m`-pseudo-coherent for every `m`. -/
theorem isPseudoCoherentFrom_singleFunctor_twistOver' (d j m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace)
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules j).obj
        (twistOver n (Spec (.of A)) d)) m :=
  isPseudoCoherentFrom_singleFunctor_twistOver n d j m

/-! ### Finite sums of twists placed in degree zero -/

/-- The two properties of a module `M` on `ℙⁿ_A` that the induction needs of the module the top
cohomology is killed by: `M[0]` is `m`-pseudo-coherent for every `m`, and `RΓ_A(M[0])` is a
pseudo-coherent object of `D(A)`. -/
def IsTwistLike (M : (projectiveSpaceOver n (Spec (.of A))).Modules) : Prop :=
  (∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace)
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules 0).obj M) m) ∧
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedGlobalSectionsOver (proj (A := A) n)).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules 0).obj M))

variable {n}

/-- `IsTwistLike` is invariant under isomorphism of modules. -/
theorem IsTwistLike.of_iso {M N : (projectiveSpaceOver n (Spec (.of A))).Modules}
    (hM : IsTwistLike n M) (e : M ≅ N) : IsTwistLike n N := by
  let e' :=
    (DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules 0).mapIso e
  exact ⟨fun m => @RingedSpace.IsPseudoCoherentFrom.ofIso
    (projectiveSpaceOver n (Spec (.of A))).toRingedSpace _ _ _ m (hM.1 m) e',
    StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso hM.2
      ((derivedGlobalSectionsOver (proj (A := A) n)).mapIso e')⟩

/-- A zero module is `IsTwistLike`. -/
theorem isTwistLike_of_isZero {M : (projectiveSpaceOver n (Spec (.of A))).Modules}
    (hM : IsZero M) : IsTwistLike n M := by
  have hz : IsZero
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules 0).obj M) :=
    Functor.map_isZero _ hM
  exact ⟨fun m => (@RingedSpace.isPseudoCoherent_of_isZero
    (projectiveSpaceOver n (Spec (.of A))).toRingedSpace _ _ hz).isPseudoCoherentFrom m,
    (StacksDraft.PseudoCoherence.pseudoCoherent_of_isZero _ (Functor.map_isZero _ hz)).1⟩

/-- The biproduct of two `IsTwistLike` modules is `IsTwistLike`. -/
theorem IsTwistLike.biprod {M N : (projectiveSpaceOver n (Spec (.of A))).Modules}
    (hM : IsTwistLike n M) (hN : IsTwistLike n N) : IsTwistLike n (M ⊞ N) := by
  have hS := (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact
  have hT := hS.singleTriangle_distinguished
  exact ⟨fun m => @RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished
      (projectiveSpaceOver n (Spec (.of A))).toRingedSpace _ m hS.singleTriangle hT
      (hM.1 m) (hN.1 m),
    (StacksDraft.PseudoCoherence.isPseudoCoherent_of_distinguished _
      ((derivedGlobalSectionsOver (proj (A := A) n)).map_distinguished _ hT)).2.1 hM.2 hN.2⟩

/-- Every twist `𝒪(d)` of the structure sheaf of `ℙⁿ_A` is `IsTwistLike`. -/
theorem isTwistLike_twistOver (d : ℤ) : IsTwistLike n (twistOver n (Spec (.of A)) d) :=
  ⟨fun m => isPseudoCoherentFrom_singleFunctor_twistOver' n d 0 m,
    isPseudoCoherent_derivedGlobalSectionsOver_twist n d⟩

/-- The `d`-th tensor power of the twisting sheaf `𝒪(1)` of `ℙⁿ_A` is `IsTwistLike`. -/
theorem isTwistLike_tensorPowModule (d : ℤ) :
    IsTwistLike n (Stacks.Ample.tensorPowModule (projectiveSpaceOver n (Spec (.of A)))
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of A))) d) :=
  (isTwistLike_twistOver d).of_iso (tensorPowModuleProjectiveTwistIso n (Spec (.of A)) d).symm

/-- A finite biproduct of `IsTwistLike` modules is `IsTwistLike`. -/
theorem isTwistLike_biproduct :
    ∀ (r : ℕ) (f : Fin r → (projectiveSpaceOver n (Spec (.of A))).Modules),
      (∀ i, IsTwistLike n (f i)) → IsTwistLike n (⨁ f) := by
  intro r
  induction r with
  | zero => exact fun f _ => isTwistLike_of_isZero (isZero_biproduct_of_isEmpty f)
  | succ r ih =>
    exact fun f hf =>
      ((hf 0).biprod (ih _ fun i => hf i.succ)).of_iso (biproductFinSuccIso r f).symm

variable (n)

/-! ### Killing the top cohomology sheaf with a finite sum of twists -/

/-- An object of `D(𝒪_{ℙⁿ_A})` which is `m`-pseudo-coherent for every `m` has quasi-coherent
cohomology sheaves. -/
theorem isQuasicoherent_homology_of_forall_isPseudoCoherentFrom
    (C : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules)
    (hC : ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) C m) (i : ℤ) :
    ((DerivedCategory.homologyFunctor
      (projectiveSpaceOver n (Spec (.of A))).Modules i).obj C).IsQuasicoherent :=
  isQuasicoherent_homology_of_isPseudoCoherentFrom
    (projectiveSpaceOver n (Spec (.of A))) C (i - 1) i (hC (i - 1)) (by omega)

/-- A morphism from a single module out of a complex, built from a map into the cycles, induces
an epimorphism on cohomology in that degree as soon as the composite to the cohomology is an
epimorphism. -/
theorem epi_homologyMap_mkHomFromSingle {C : Type*} [Category C] [Abelian C]
    {K : CochainComplex C ℤ} {j : ℤ} {M : C} (φ : M ⟶ K.cycles j)
    (hφ : Epi (φ ≫ K.homologyπ j)) :
    Epi (HomologicalComplex.homologyMap
      (HomologicalComplex.mkHomFromSingle (φ ≫ K.iCycles j) (fun k _ => by simp)) j) := by
  set ψ := HomologicalComplex.mkHomFromSingle (φ ≫ K.iCycles j) (fun k _ => by simp)
  have hc : HomologicalComplex.cyclesMap ψ j =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) j M).hom ≫ φ := by
    rw [← cancel_mono (K.iCycles j), HomologicalComplex.cyclesMap_i, Category.assoc,
      HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc,
      HomologicalComplex.mkHomFromSingle_f]
  have h := HomologicalComplex.homologyπ_naturality ψ j
  rw [hc, Category.assoc] at h
  exact epi_of_epi_fac h

/-- **The top cohomology sheaf of a pseudo-coherent object is hit by a finite sum of twists.**
Let `C` be an object of `D(𝒪_{ℙⁿ_A})` which is `m`-pseudo-coherent for every `m` and has no
cohomology above degree `j`. Then there are a module `M` with `M[0]` pseudo-coherent and
`RΓ_A(M[0])` pseudo-coherent — a finite direct sum of twists of the structure sheaf — and a
morphism `M[-j] ⟶ C` which is surjective on `H^j`. -/
theorem exists_singleFunctor_twists_epi
    (C : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules) (j : ℤ)
    (hC : ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) C m)
    (hj : C.IsLE j) :
    ∃ (M : (projectiveSpaceOver n (Spec (.of A))).Modules)
      (β : (DerivedCategory.singleFunctor _ j).obj M ⟶ C),
      IsTwistLike n M ∧
        Epi ((DerivedCategory.homologyFunctor (projectiveSpaceOver n (Spec (.of A))).Modules j).map
          β) := by
  have hft : SheafOfModules.IsFiniteType ((DerivedCategory.homologyFunctor
      (projectiveSpaceOver n (Spec (.of A))).Modules j).obj C) :=
    RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) C j (hC j)
      (fun i hi => C.isZero_of_isLE j i hi)
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_quasicoherent_representative' (projectiveSpaceOver n (Spec (.of A)))
    (HasDerivedCategory.standard _) C
    (isQuasicoherent_homology_of_forall_isPseudoCoherentFrom n C hC)
  have : (K.X j).IsQuasicoherent := hK j
  have : (K.X (j + 1)).IsQuasicoherent := hK (j + 1)
  have : (K.cycles j).IsQuasicoherent := Stacks.Chow.isQuasicoherent_cycles K j
  let eH : K.homology j ≅
      (DerivedCategory.homologyFunctor (projectiveSpaceOver n (Spec (.of A))).Modules j).obj C :=
    ((DerivedCategory.homologyFunctorFactors
      (projectiveSpaceOver n (Spec (.of A))).Modules j).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (projectiveSpaceOver n (Spec (.of A))).Modules j).mapIso e
  obtain ⟨S, hS⟩ := exists_finiteTypeQuasicoherentSubobject_epi_comp_of_qcqs hft
    (K.homologyπ j ≫ eH.hom)
  obtain ⟨r, d, b, hb, p, hp, -⟩ := Stacks.ProjectiveSpace.exists_epi_biproduct_tensorPowModule
    n (Spec (.of A)) 0 (S.obj : (projectiveSpaceOver n (Spec (.of A))).Modules) S.2.1 S.2.2
  have hM : IsTwistLike n b.pt :=
    (isTwistLike_biproduct r _ fun i => isTwistLike_tensorPowModule (d i)).of_iso
      (biproduct.uniqueUpToIso _ hb).symm
  let φ : b.pt ⟶ K.cycles j := p ≫ S.obj.arrow
  have hφ : Epi (φ ≫ K.homologyπ j) := by
    rw [show φ ≫ K.homologyπ j =
        (p ≫ S.obj.arrow ≫ K.homologyπ j ≫ eH.hom) ≫ eH.inv by simp [φ]]
    infer_instance
  let ψ := HomologicalComplex.mkHomFromSingle (φ ≫ K.iCycles j) (fun k _ => by simp)
  refine ⟨b.pt, ((DerivedCategory.singleFunctorIsoCompQ
    (projectiveSpaceOver n (Spec (.of A))).Modules j).app b.pt).hom ≫
    DerivedCategory.Q.map ψ ≫ e.hom, hM, ?_⟩
  have hQ : Epi ((DerivedCategory.homologyFunctor
      (projectiveSpaceOver n (Spec (.of A))).Modules j).map (DerivedCategory.Q.map ψ)) :=
    (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso
      (DerivedCategory.homologyFunctorFactors (projectiveSpaceOver n (Spec (.of A))).Modules j)
      ψ).2 (epi_homologyMap_mkHomFromSingle φ hφ)
  rw [Functor.map_comp, Functor.map_comp]
  exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _ (@epi_comp _ _ _ _ _ _ hQ _ (IsIso.epi_of_iso _))

/-! ### The induction -/

/-- A module `M` with `IsTwistLike` placed in degree `j` is `m`-pseudo-coherent for every `m`, and
its `RΓ_A` is pseudo-coherent. -/
theorem IsTwistLike.singleFunctor {M : (projectiveSpaceOver n (Spec (.of A))).Modules}
    (hM : IsTwistLike n M) (j : ℤ) :
    (∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace)
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules j).obj M) m) ∧
    StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedGlobalSectionsOver (proj (A := A) n)).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n (Spec (.of A))).Modules j).obj
        M)) :=
  ⟨fun m => @RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero
    (projectiveSpaceOver n (Spec (.of A))).toRingedSpace _ M m j (hM.1 (m - j)),
    StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso (hM.2.shift (-j))
      (((derivedGlobalSectionsOver (proj (A := A) n)).commShiftIso (-j)).symm.app _ ≪≫
        (derivedGlobalSectionsOver (proj (A := A) n)).mapIso
          (((DerivedCategory.singleFunctors _).shiftIso (-j) j 0 (by omega)).app M))⟩

/-- **The induction.** If `C` is `m`-pseudo-coherent for every `m` and has no cohomology above
degree `b`, then `RΓ_A(C)` is `(b + n + 1 - N)`-pseudo-coherent, for every `N`. -/
theorem isPseudoCoherentFrom_derivedGlobalSectionsOver_of_isLE (N : ℕ) :
    ∀ (C : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules) (b : ℤ),
      (∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
        (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) C m) → C.IsLE b →
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((derivedGlobalSectionsOver (proj (A := A) n)).obj C) (b + n + 1 - N) := by
  induction N with
  | zero =>
    intro C b hC hb
    have hle := isLE_derivedGlobalSectionsOver_obj n C b hb
      (isQuasicoherent_homology_of_forall_isPseudoCoherentFrom n C hC)
    exact StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_homology_isZero _ _
      fun i hi => ((derivedGlobalSectionsOver (proj (A := A) n)).obj C).isZero_of_isLE (b + n) i
        (by omega)
  | succ N ih =>
    intro C b hC hb
    obtain ⟨M, β, hM, hβ⟩ := exists_singleFunctor_twists_epi n C b hC hb
    obtain ⟨C', g, h, hT⟩ := distinguished_cocone_triangle β
    have hS := IsTwistLike.singleFunctor n hM b
    have hC' : ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
        (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) C' m := fun m =>
      @RingedSpace.isPseudoCoherentFrom_obj₃_of_distinguished
        (projectiveSpaceOver n (Spec (.of A))).toRingedSpace _ m _ hT (hS.1 (m + 1)) (hC m)
    have hz : ∀ i : ℤ, b ≤ i → IsZero ((DerivedCategory.homologyFunctor
        (projectiveSpaceOver n (Spec (.of A))).Modules i).obj C') := by
      refine CategoryTheory.isZero_homology_obj₃_of_distinguished b (Triangle.mk β g h) hT
        (fun i hi => ?_) hβ
      exact ⟨⟨0, (((DerivedCategory.singleFunctor _ b).obj M).isZero_of_isLE b i hi).eq_of_src _ _,
        (C.isZero_of_isLE b i hi).eq_of_src _ _⟩⟩
    have hb' : C'.IsLE (b - 1) := by
      rw [DerivedCategory.isLE_iff]
      exact fun i hi => hz i (by omega)
    refine _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two _ _
      ((derivedGlobalSectionsOver (proj (A := A) n)).map_distinguished _ hT)
      ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1 hS.2 _) ?_
    rw [show b + (n : ℤ) + 1 - ((N + 1 : ℕ) : ℤ) = b - 1 + n + 1 - N by omega]
    exact ih C' (b - 1) hC' hb'

/-- **[Stacks, Tag 0CSD], the pseudo-coherence half, for `ℙⁿ_A ⟶ Spec A`.** For every
pseudo-coherent object `F` of `D(𝒪_{ℙⁿ_A})`, the derived global sections `RΓ_A(F)` are a
pseudo-coherent object of `D(A)`. -/
theorem isPseudoCoherent_derivedGlobalSectionsOver_of_isPseudoCoherent
    (F : DerivedCategory (projectiveSpaceOver n (Spec (.of A))).Modules)
    (hF : RingedSpace.IsPseudoCoherent (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace)
      F) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedGlobalSectionsOver (proj (A := A) n)).obj F) := by
  have hF' : ∀ m : ℤ, RingedSpace.IsPseudoCoherentFrom
      (X := (projectiveSpaceOver n (Spec (.of A))).toRingedSpace) F m :=
    hF.isPseudoCoherentFrom
  obtain ⟨b, hb⟩ := exists_isLE_of_isPseudoCoherentFrom F 0 (hF' 0)
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m =>
    (isPseudoCoherentFrom_derivedGlobalSectionsOver_of_isLE n (b + n + 1 - m).toNat F b hF'
      hb).mono (by omega)

end AlgebraicGeometry.ProjectiveSpaceDirectImage

end
