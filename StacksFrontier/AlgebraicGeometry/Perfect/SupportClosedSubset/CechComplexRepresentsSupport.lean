module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportedSectionsValue
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.ExtendedCechComplexComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedSectionsComplexInclusion
public import StacksFrontier.Homology.CochainComplexDegreeZeroHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction

/-!
# The extended alternating Čech complex is its own derived sections with support

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions, let `Z` be a closed
subset whose complement is `U = ⋃ᵢ X.basicOpen fᵢ`.  The extended alternating Čech complex
`𝓕^•` of Stacks 0G7I is acyclic over `U` (Stacks 0G7K), and therefore

`i_* Rℋ_Z(𝓕^•) ≅ 𝓕^•`

in the unbounded derived category of `𝒪_X`-modules.  The proof is the one the source attributes
to Stacks 0AEF, carried out on resolutions: a K-injective resolution `ℐ^•` of `𝓕^•` by injective
modules has `ℐ^•|_U` K-injective and acyclic, hence null-homotopic, so the short exact sequence
`0 ⟶ ℋ_Z(ℐ^•) ⟶ ℐ^• ⟶ j_*(ℐ^•|_U) ⟶ 0` of Stacks 0G72 exhibits the inclusion of the supported
sections as a quasi-isomorphism, while `ℋ_Z(ℐ^•)` computes `i_* Rℋ_Z` by Stacks 0G6N.

The complex also vanishes above degree `c`: there is no strictly increasing `(p + 1)`-tuple in
`{1, …, c}` once `p ≥ c`.  At `c = 0` that leaves only degree zero, where the complex is `𝓕`
itself.

## Main results

* `nonempty_pushforwardDerivedSupportCechIso`: the isomorphism `i_* Rℋ_Z(𝓕^•) ≅ 𝓕^•`.

* `jStar_preservesHomology`: restriction to an open subspace is exact.
* `acyclic_jStar_of_acyclic_modulePullback`, `acyclic_jStar_extend_of_acyclic` and
  `acyclic_jStar_of_quasiIso`: acyclicity of a restriction passes between the two spellings of
  restriction, from the `ℕ`-indexed complex to its `ℤ`-indexed extension, and along a
  quasi-isomorphism.
* `exactAt_extend_of_gt` and `isZero_homology_extend_of_gt`: the extended complex is exact, and
  so has vanishing cohomology sheaves, in degrees above `c`.
* `dataHomologyZeroIso`: for the **empty** family of equations the degree-zero cohomology sheaf
  of the complex is the coefficient module itself.

## Implementation notes

The acyclicity of Stacks 0G7K is proved for the `ℕ`-indexed complex with restriction written as
`AlgebraicGeometry.Scheme.Modules.pullback`, whereas the derived category needs the `ℤ`-indexed
extension and the short exact sequence of Stacks 0G72 is written with the extension-by-zero
spelling `ExtensionByZeroModules.jStar` of restriction.  The two restriction functors are
compared by `Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso`, and the change of
grading is made on cohomology sheaves rather than on complexes: restriction is exact, so it
commutes with the formation of cohomology sheaves (`CategoryTheory.ShortComplex.mapHomologyIso`),
and the cohomology sheaves of an extension are those of the original complex in the embedded
degrees and zero elsewhere (`HomologicalComplex.extendHomologyIso` and
`HomologicalComplex.extend_exactAt`).

The closed subset enters as a parameter together with the identification of its complement with
the union of the principal opens, rather than as the zero locus of the equations: that keeps
this file independent of the module in which the zero locus is named, and the identification is
one application of `TopologicalSpace.Opens.ext`.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7K](https://stacks.math.columbia.edu/tag/0G7K)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.SheafOfModules.SupportedSections
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechSupportRepresentation

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction to an open subspace is exact -/

section Restriction

variable (Y : RingedSpace.{u, u}) (U : Opens Y.carrier)

/-- Restriction of sheaves of modules to an open subspace is additive, being a right adjoint. -/
public instance jStar_additive : (jStar U (structureSheafRing Y)).Additive := by
  let _ : (jStar U (structureSheafRing Y)).IsRightAdjoint :=
    (jShriekAdjunction U (structureSheafRing Y)).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-- Restriction of sheaves of modules to an open subspace preserves cohomology: it is a right
adjoint of extension by zero and a left adjoint of pushforward, hence exact. -/
public instance jStar_preservesHomology : (jStar U (structureSheafRing Y)).PreservesHomology := by
  let _ : PreservesLimits (jStar U (structureSheafRing Y)) :=
    (jShriekAdjunction U (structureSheafRing Y)).rightAdjoint_preservesLimits
  let _ : PreservesColimits (jStar U (structureSheafRing Y)) :=
    (jStarAdjunction U (structureSheafRing Y)).leftAdjoint_preservesColimits
  infer_instance

end Restriction

/-- An exact functor commutes with the formation of cohomology sheaves of a complex. -/
public def mapHomologyIso {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (G : A ⥤ B) [G.Additive] [G.PreservesHomology] {ι : Type*} {cs : ComplexShape ι}
    (K : HomologicalComplex A cs) (n : ι) :
    ((G.mapHomologicalComplex cs).obj K).homology n ≅ G.obj (K.homology n) :=
  ShortComplex.mapHomologyIso (K.sc n) G

/-! ### The terms of the complex vanish above the number of equations -/

/-- There is no strictly increasing `(p + 1)`-tuple in `Fin c` once `c ≤ p`. -/
public theorem isEmpty_ordIndex_of_le {c p : ℕ} (h : c ≤ p) :
    IsEmpty (CechCochains.OrdIndex (I := Fin c) p) := by
  refine ⟨fun s => ?_⟩
  have hc := Fintype.card_le_of_injective s.1 s.2.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- A product over an empty index is a zero object. -/
public theorem isZero_pi_of_isEmpty {A : Type*} [Category* A] [Abelian A] {J : Type*}
    [IsEmpty J] (M : J → A) : IsZero (∏ᶜ M) := by
  have ht : IsTerminal (∏ᶜ M) :=
    IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => isEmptyElim i)
      (fun _ _ => Pi.hom_ext _ _ fun i => isEmptyElim i)
  exact IsZero.of_iso (isZero_zero _) (ht.uniqueUpToIso (isZero_zero _).isTerminal)

variable {X : Scheme.{u}} {c : ℕ} {f : Fin c → Γ(X, ⊤)} {F : X.Modules}
  (D : ExtendedAlternatingCechData f F)

/-- The terms of the extended alternating Čech complex vanish in degrees above the number of
equations. -/
public theorem isZero_complex_X_of_le {p : ℕ} (h : c ≤ p) : IsZero (D.complex.X (p + 1)) :=
  have : IsEmpty (CechCochains.OrdIndex (I := Fin c) p) := isEmpty_ordIndex_of_le h
  IsZero.of_iso (isZero_pi_of_isEmpty _) (D.termIso p)

/-- The extended alternating Čech complex is exact in degrees above the number of equations. -/
public theorem exactAt_of_lt {p : ℕ} (h : c < p) : D.complex.ExactAt p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact ShortComplex.exact_of_isZero_X₂ _ (isZero_complex_X_of_le D (by omega))

/-- No term of an `ℕ`-indexed complex is placed in a negative degree of its `ℤ`-indexed
extension. -/
private theorem embeddingUpNat_f_ne_of_neg {n : ℤ} (hn : n < 0) (p : ℕ) :
    ComplexShape.embeddingUpNat.f p ≠ n := by
  have hp : ComplexShape.embeddingUpNat.f p = (p : ℤ) := rfl
  omega

/-- The `ℤ`-indexed extension of the extended alternating Čech complex is exact in degrees above
the number of equations. -/
public theorem exactAt_extend_of_gt {n : ℤ} (h : (c : ℤ) < n) :
    (D.complex.extend ComplexShape.embeddingUpNat).ExactAt n := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
  exact (HomologicalComplex.extend_exactAt_iff D.complex ComplexShape.embeddingUpNat
    (j := p) rfl).2 (exactAt_of_lt D (by exact_mod_cast h))

/-- The `ℤ`-indexed extension of the extended alternating Čech complex is bounded below by
degree `0`. -/
public theorem isStrictlyGE_extend :
    CochainComplex.IsStrictlyGE (D.complex.extend ComplexShape.embeddingUpNat) 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact HomologicalComplex.isZero_extend_X _ _ n (embeddingUpNat_f_ne_of_neg hn)

/-- The `ℤ`-indexed extension of the extended alternating Čech complex has vanishing cohomology
sheaves in degrees above the number of equations. -/
public theorem isZero_homology_extend_of_gt {n : ℤ} (h : (c : ℤ) < n) :
    IsZero ((D.complex.extend ComplexShape.embeddingUpNat).homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (exactAt_extend_of_gt D h)

/-! ### Degree zero with no equations -/

section EmptyEquations

variable {g : Fin 0 → Γ(X, ⊤)} {G : X.Modules}
  (E : AlgebraicGeometry.ExtendedAlternatingCech.Data g G)

/-- **With no equations the degree-one term of the extended alternating Čech complex vanishes.**
There is no strictly increasing map `Fin 1 → Fin 0`, so the product that
`AlgebraicGeometry.ExtendedAlternatingCech.Data.termIso` presents that term as is a product over
an empty index.  This is `isZero_complex_X_of_le` at `c = p = 0`, read on the other of the two
constructions of the complex. -/
public theorem isZero_data_complex_X_one : IsZero (E.complex.X 1) :=
  have : IsEmpty (CechCochains.OrdIndex (I := Fin 0) 0) := isEmpty_ordIndex_of_le le_rfl
  IsZero.of_iso (isZero_pi_of_isEmpty _) (E.termIso 0)

/-- **With no equations the augmentation of the extended alternating Čech complex vanishes**, its
target being a zero object by `isZero_data_complex_X_one`.  It is the empty product of the
canonical restrictions to the principal opens of the equations. -/
public theorem data_complex_d_zero_eq_zero : E.complex.d 0 1 = 0 :=
  (isZero_data_complex_X_one E).eq_of_tgt _ 0

/-- **Degree zero of the extended alternating Čech complex of an empty family of equations is the
coefficient module itself.**

With no equations nothing leaves degree zero, by `data_complex_d_zero_eq_zero`, so
`CochainComplex.homologyZeroIso` applies and
`AlgebraicGeometry.ExtendedAlternatingCech.Data.zeroIso` identifies the degree-zero term with the
coefficient module.

This is the degree-zero end of the vanishing `isZero_complex_X_of_le`: for an empty family the
complex is concentrated in degree zero, where it is `ℱ`.  It is what the degree-`c` statements
attached to the complex — the fraction class of [Stacks, Tag 0G7Q] and the local cohomology
identification of [Stacks, Tag 0G7M] — read as at `c = 0`, and it needs no identification of the
common zero locus of the equations: the reason is the emptiness of the index of the degree-one
term, not that the zero locus is everything. -/
public def dataHomologyZeroIso : E.complex.homology 0 ≅ G :=
  CochainComplex.homologyZeroIso E.complex (data_complex_d_zero_eq_zero E) ≪≫ E.zeroIso

/-- `dataHomologyZeroIso` is the canonical identification: on the class of a degree-zero cycle it
is the cycle itself, read in the coefficient module. -/
public theorem homologyπ_comp_dataHomologyZeroIso_hom :
    E.complex.homologyπ 0 ≫ (dataHomologyZeroIso E).hom =
      E.complex.iCycles 0 ≫ E.zeroIso.hom := by
  rw [dataHomologyZeroIso, Iso.trans_hom, ← Category.assoc,
    CochainComplex.homologyπ_comp_homologyZeroIso_hom]

end EmptyEquations

/-! ### Acyclicity of the restriction to the complement -/

section RingedSpace

variable {Y : RingedSpace.{u, u}} (V : Opens Y.carrier)

/-- The two spellings of restriction to an open subspace — pullback along the inclusion and the
right adjoint of extension by zero — agree, so acyclicity of one restriction is acyclicity of
the other. -/
public theorem acyclic_jStar_of_acyclic_modulePullback
    {K : HomologicalComplex (_root_.SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℕ)}
    (h : (((modulePullback (Y.ofRestrict V.isOpenEmbedding)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).Acyclic) :
    (((jStar V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      K).Acyclic := by
  have _ := Functor.preservesZeroMorphisms_of_iso
    (Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso Y V)
  rw [HomologicalComplex.acyclic_iff] at h ⊢
  exact fun n => (h n).of_iso ((NatIso.mapHomologicalComplex
    (Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso Y V)
    (ComplexShape.up ℕ)).app K)

/-- An acyclic complex stays acyclic after restriction and extension of the grading from `ℕ` to
`ℤ`: restriction is exact, and the cohomology sheaves of an extension are those of the original
complex in the embedded degrees and zero elsewhere. -/
public theorem acyclic_jStar_extend_of_acyclic
    {K : HomologicalComplex (_root_.SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℕ)}
    (h : (((jStar V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      K).Acyclic) :
    (((jStar V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K.extend ComplexShape.embeddingUpNat)).Acyclic := by
  rw [HomologicalComplex.acyclic_iff] at h ⊢
  intro n
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ n).2 ?_
  refine IsZero.of_iso ?_ (mapHomologyIso (jStar V (structureSheafRing Y)) _ n)
  rcases lt_or_ge n 0 with hn | hn
  · refine Functor.map_isZero _ ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 ?_)
    exact HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat n
      (embeddingUpNat_f_ne_of_neg hn)
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ p).1 (h p)) ?_
    exact Functor.mapIso _ (HomologicalComplex.extendHomologyIso K
        ComplexShape.embeddingUpNat (j := p) rfl) ≪≫
      (mapHomologyIso (jStar V (structureSheafRing Y)) K p).symm

/-- Acyclicity of a restriction is invariant under quasi-isomorphism of the complex restricted:
restriction is exact, so it carries a quasi-isomorphism to a quasi-isomorphism. -/
public theorem acyclic_jStar_of_quasiIso
    {C I : HomologicalComplex (_root_.SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)}
    (r : C ⟶ I) (hr : QuasiIso r)
    (h : (((jStar V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      C).Acyclic) :
    (((jStar V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      I).Acyclic := by
  rw [HomologicalComplex.acyclic_iff] at h ⊢
  intro n
  have hqi : QuasiIso (((jStar V (structureSheafRing Y)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map r) := inferInstance
  have _ := (quasiIsoAt_iff_isIso_homologyMap _ n).1 (hqi.quasiIsoAt n)
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ n).2 ?_
  refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap
    (((jStar V (structureSheafRing Y)).mapHomologicalComplex (ComplexShape.up ℤ)).map r) n)).symm
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).1 (h n)

end RingedSpace

/-! ### The complex is its own derived sections with support -/

variable {Z : Set X} (hZ : IsClosed Z) (hZU : openComplement Z hZ = ⨆ i, X.basicOpen (f i))

include hZU in
/-- **Stacks Project, Tag 0G7M**, the step that uses the acyclicity of Stacks 0G7K: the derived
sections with support on `Z` do not change the extended alternating Čech complex,

`i_* Rℋ_Z(𝓕^•) ≅ 𝓕^•`.

The isomorphism is produced on a K-injective resolution of `𝓕^•` by injective modules, where it
is the inclusion of the subsheaf of sections supported on `Z`; that inclusion is a
quasi-isomorphism because its cokernel is the pushforward of a null-homotopic complex.  The
resolution is not canonical, which is why the statement asserts the existence of the
isomorphism, as the neighbouring statements of Stacks 0A3B do. -/
public theorem nonempty_pushforwardDerivedSupportCechIso :
    letI := pushforward_preservesFiniteLimits X.toRingedSpace Z
    letI := pushforward_preservesFiniteColimits X.toRingedSpace Z hZ
    Nonempty
      ((modulePushforward (closedSubsetInclusion X.toRingedSpace Z)).mapDerivedCategory.obj
          ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).obj
            (DerivedCategory.Q.obj (D.complex.extend ComplexShape.embeddingUpNat))) ≅
        DerivedCategory.Q.obj (D.complex.extend ComplexShape.embeddingUpNat)) := by
  have _ := pushforward_preservesFiniteLimits X.toRingedSpace Z
  have _ := pushforward_preservesFiniteColimits X.toRingedSpace Z hZ
  have := isStrictlyGE_extend D
  obtain ⟨I, r, hr, hinj, hIGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (D.complex.extend ComplexShape.embeddingUpNat) 0
  have hKI : I.IsKInjective :=
    @CochainComplex.isKInjective_of_injective _ _ _ I 0 hIGE hinj
  have hQr : IsIso (DerivedCategory.Q.map r) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ r).2 hr
  have hUI :
      (((jStar (openComplement Z hZ) (structureSheafRing X.toRingedSpace)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).Acyclic := by
    rw [hZU]
    refine acyclic_jStar_of_quasiIso _ r hr (acyclic_jStar_extend_of_acyclic _ ?_)
    exact acyclic_jStar_of_acyclic_modulePullback _
      (Stacks.Perfect.CechComplexComparison.acyclic_restrict D)
  have hincl := @Stacks.Perfect.SupportedSectionsComplex.isIso_Q_map_supportedSectionsComplexι
    X.toRingedSpace Z hZ I hinj hKI hUI
  exact ⟨(modulePushforward (closedSubsetInclusion X.toRingedSpace Z)).mapDerivedCategory.mapIso
        ((derivedSupportedSectionsOnClosed X.toRingedSpace Z hZ).mapIso
          (@asIso _ _ _ _ (DerivedCategory.Q.map r) hQr)) ≪≫
      Stacks.Perfect.DerivedSupportedSectionsValue.pushforwardDerivedSupportedSectionsIso
        X.toRingedSpace Z hZ I hKI ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map
        (Stacks.Perfect.SupportedSectionsComplex.supportedSectionsComplexι
          X.toRingedSpace Z I)) hincl ≪≫
      (@asIso _ _ _ _ (DerivedCategory.Q.map r) hQr).symm⟩

end Stacks.Perfect.CechSupportRepresentation

end
