module

public import
  StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.NoetherianModelClauses
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.PicardComplement
public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.TwistSectionsKernel
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularProjectiveSpace
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# The Picard group of the projective line with a closed point removed

Let `k` be a field, let `f ∈ k[T₀, T₁]` be homogeneous and let `X = D₊(f)` be the complement of
its vanishing locus in `ℙ¹_k = Proj k[T₀, T₁]`. For `f` homogeneous and irreducible of degree `d`
the vanishing locus is a single closed point `t = V₊(f)` with residue degree `d`, so
`X = ℙ¹_k ∖ {t}` is the curve of [Stacks, Tag 0CDP]. The surjection `ℤ = Pic(ℙ¹_k) ↠ Pic(X)` has
kernel exactly `dℤ`, so `Pic(X) = ℤ/dℤ`, and in particular `Pic(X) ≠ 0` when `t` is not a
`k`-rational point. The open `X` is `Proj.basicOpen (grading k) f`.

## Main definitions

* `Stacks.ProjectiveLine.complementTwistClass` and
  `Stacks.ProjectiveLine.complementTwistHom`: the class of `𝒪(m)|_X` in `Pic(X)`, and the
  homomorphism `ℤ → Pic(X)` it defines.
* `Stacks.ProjectiveLine.complementRestrictHom`: the restriction homomorphism
  `Pic(ℙ¹_k) → Pic(X)`, obtained from `ℤ → Pic(X)` through the isomorphism `ℤ ≃ Pic(ℙ¹_k)` of
  Tag 0BXJ.
* `Stacks.ProjectiveLine.complementZModHom` and
  `Stacks.ProjectiveLine.complementZModEquiv`: the induced homomorphism `ℤ/dℤ → Pic(X)`, and
  **the isomorphism `ℤ/dℤ ≃+ Pic(X)`** it induces.

## Main results

* `Stacks.ProjectiveLine.uniqueFactorizationMonoid_stalk`: the local rings of `ℙ¹_k` are unique
  factorization domains.
* `Stacks.ProjectiveLine.exists_iso_pullback_twistingSheaf`: every invertible module on `X` is
  the restriction of a twist.
* `Stacks.ProjectiveLine.complementRestrictHom_picardClass`: `complementRestrictHom` is
  restriction of invertible modules.
* `Stacks.ProjectiveLine.surjective_complementRestrictHom`: **the surjection
  `ℤ = Pic(ℙ¹_k) ↠ Pic(X)`.**
* `Stacks.ProjectiveLine.complementTwistClass_mul_degree`: `𝒪(nd)` is trivial on `X`.
* `Stacks.ProjectiveLine.surjective_complementZModHom` and
  `Stacks.ProjectiveLine.nsmul_finrank_residueField_eq_zero`: `Pic(X)` is a quotient of
  `ℤ/dℤ`, for `d = [κ(t) : k]`.
* `Stacks.ProjectiveLine.dvd_of_complementTwistClass_eq_zero`: **the kernel** — `𝒪(m)` is
  trivial on `X` only when `d ∣ m`.
* `Stacks.ProjectiveLine.injective_complementZModHom` and
  `Stacks.ProjectiveLine.complementZModEquiv`: **`Pic(X) = ℤ/dℤ`.**
* `Stacks.ProjectiveLine.nontrivial_picardGroup_basicOpen`: **`Pic(X) ≠ 0` when `t` is not a
  `k`-rational point**, so this example is a counterexample to [Stacks, Tag 0CC5].
* `Stacks.ProjectiveLine.card_eq_finrank_residueField`: the same isomorphism with `d` read as
  the residue degree `[κ(t) : k]`.

## References

* [Stacks Project, Tag 0CDP](https://stacks.math.columbia.edu/tag/0CDP)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 0BD9](https://stacks.math.columbia.edu/tag/0BD9)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjectiveLine

universe u

variable {k : Type u} [Field k]

/-- The local rings of `ℙ¹_k` are unique factorization domains. -/
theorem uniqueFactorizationMonoid_stalk (x : AlgebraicGeometry.Proj (grading k)) :
    UniqueFactorizationMonoid ((AlgebraicGeometry.Proj (grading k)).presheaf.stalk x) :=
  have := Stacks.AlgebraicGeometry.ProjPolyChart.isRegularLocalRing_stalk_proj k 1 x
  IsRegularLocalRing.uniqueFactorizationMonoid _

/-- `ℙ¹_k` is locally Noetherian. -/
theorem isLocallyNoetherian_proj (k : Type u) [Field k] :
    IsLocallyNoetherian (AlgebraicGeometry.Proj (grading k)) :=
  Stacks.AlgebraicGeometry.Proj.isLocallyNoetherian_proj _

variable (f : MvPolynomial (Fin 2) k)

/-- Every invertible module on `X = ℙ¹_k ∖ V₊(f)` is the restriction of a twist `𝒪(m)`. -/
theorem exists_iso_pullback_twistingSheaf
    (L : (Proj.basicOpen (grading k) f).toScheme.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible
      (Proj.basicOpen (grading k) f).toScheme.presheaf
      (Proj.basicOpen (grading k) f).toScheme.ringCatIsSheaf L) :
    ∃ m : ℤ, Nonempty (L ≅ (Scheme.Modules.pullback (Proj.basicOpen (grading k) f).ι).obj
      (twistingSheaf (grading k) m)) := by
  have := isLocallyNoetherian_proj k
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Proj.basicOpen (grading k) f).toScheme.sheaf.obj
      (Proj.basicOpen (grading k) f).toScheme.ringCatSheaf.property L := hL
  obtain ⟨L', hL', ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_isInvertible_pullback_iso_of_isLocallyNoetherian
      (Proj.basicOpen (grading k) f) L fun x _ => uniqueFactorizationMonoid_stalk x
  obtain ⟨m, ⟨e'⟩⟩ := Stacks.PicardUFD.exists_iso_twistingSheaf_general k 1 L' hL'
  exact ⟨m, ⟨e ≪≫ (Scheme.Modules.pullback _).mapIso e'⟩⟩

/-- The class in `Pic(ℙ¹_k ∖ V₊(f))` of the twist `𝒪(m)`. -/
def complementTwistClass (m : ℤ) : (Proj.basicOpen (grading k) f).toScheme.picardGroup :=
  Stacks.SheafOfModules.pullbackPicardClass (Proj.basicOpen (grading k) f).ι
    (twistingSheaf (grading k) m) (Stacks.PicardUFD.isInvertible_twistingSheaf k 1 m)

/-- **The map `ℤ → Pic(ℙ¹_k ∖ V₊(f))` is surjective.** -/
theorem surjective_complementTwistClass : Function.Surjective (complementTwistClass f) := by
  intro c
  obtain ⟨L, hL, hLc⟩ := Stacks.SheafOfModules.exists_picardClass_eq
    (Proj.basicOpen (grading k) f).toScheme.presheaf
    (Proj.basicOpen (grading k) f).toScheme.ringCatIsSheaf c
  obtain ⟨m, ⟨e⟩⟩ := exists_iso_pullback_twistingSheaf f L hL
  refine ⟨m, ?_⟩
  rw [← hLc]
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mpr ⟨e.symm⟩

/-- **The map `ℤ → Pic(ℙ¹_k ∖ V₊(f))` is additive.** -/
theorem complementTwistClass_add (m m' : ℤ) :
    complementTwistClass f (m + m') = complementTwistClass f m + complementTwistClass f m' := by
  have hm := Stacks.PicardUFD.isInvertible_twistingSheaf k 1 m
  have hm' := Stacks.PicardUFD.isInvertible_twistingSheaf k 1 m'
  have htens := Stacks.SheafOfModules.isInvertible_schemeTensor
    (AlgebraicGeometry.Proj (grading k)) (twistingSheaf (grading k) m)
    (twistingSheaf (grading k) m') hm hm'
  have h1 : complementTwistClass f m + complementTwistClass f m' =
      Stacks.SheafOfModules.pullbackPicardClass (Proj.basicOpen (grading k) f).ι
        (Stacks.SheafOfModules.schemeTensor (AlgebraicGeometry.Proj (grading k))
          (twistingSheaf (grading k) m) (twistingSheaf (grading k) m')) htens :=
    (Stacks.SheafOfModules.pullbackPicardClass_tensorSheaf _ _ _ hm hm' htens).symm
  rw [h1]
  exact Stacks.SheafOfModules.pullbackPicardClass_congr _ _ _ _ htens
    (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso (grading k)
      (Stacks.PicardUFD.degreeOneCover k 1) m m').symm

/-- **The twist `𝒪(nd)` becomes trivial on `X = ℙ¹_k ∖ V₊(f)`** when `f` is homogeneous of
degree `d`. -/
theorem complementTwistClass_mul_degree {d : ℕ} (hf : f ∈ grading k d) (n : ℤ) :
    complementTwistClass f (n * d) = 0 :=
  (Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff _ _ _).mpr
    ⟨((Scheme.Modules.restrictFunctorIsoPullback
        (Proj.basicOpen (grading k) f).ι).app (twistingSheaf (grading k) (n * d))).symm ≪≫
      Stacks.AlgebraicGeometry.ProjInvertibleLocus.restrictIsoUnitOfOverIsoUnit _ _
        (Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit
          (grading k) hf n)⟩

/-- **The homomorphism `ℤ → Pic(ℙ¹_k ∖ V₊(f))`**, `m ↦ 𝒪(m)|_X`. -/
def complementTwistHom : ℤ →+ (Proj.basicOpen (grading k) f).toScheme.picardGroup :=
  AddMonoidHom.mk' (complementTwistClass f) (complementTwistClass_add f)

/-- The homomorphism `ℤ → Pic(X)` sends `m` to the class of `𝒪(m)|_X`. -/
@[simp]
theorem complementTwistHom_apply (m : ℤ) :
    complementTwistHom f m = complementTwistClass f m := rfl

/-- **The restriction homomorphism `Pic(ℙ¹_k) → Pic(X)`** for `X = ℙ¹_k ∖ V₊(f)`, defined
through the isomorphism `ℤ ≃ Pic(ℙ¹_k)` of [Stacks, Tag 0BXJ]. -/
def complementRestrictHom : (AlgebraicGeometry.Proj (grading k)).picardGroup →+
    (Proj.basicOpen (grading k) f).toScheme.picardGroup :=
  (complementTwistHom f).comp
    (Stacks.PicardUFD.twistPicardAddEquiv k 1 Nat.one_pos).symm.toAddMonoidHom

/-- The restriction homomorphism sends the class of `𝒪(m)` to the class of `𝒪(m)|_X`. -/
theorem complementRestrictHom_twistPicardHom (m : ℤ) :
    complementRestrictHom f (Stacks.PicardUFD.twistPicardHom k 1 m) =
      complementTwistClass f m := by
  show complementTwistHom f ((Stacks.PicardUFD.twistPicardAddEquiv k 1 Nat.one_pos).symm
    (Stacks.PicardUFD.twistPicardHom k 1 m)) = _
  rw [← Stacks.PicardUFD.twistPicardAddEquiv_apply k 1 Nat.one_pos m, AddEquiv.symm_apply_apply]
  rfl

/-- **`complementRestrictHom` is the restriction map**: it sends the class of an invertible
`𝒪_{ℙ¹}`-module to the class of its restriction to `X = ℙ¹_k ∖ V₊(f)`. -/
theorem complementRestrictHom_picardClass (L : (AlgebraicGeometry.Proj (grading k)).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (grading k)).presheaf
      (AlgebraicGeometry.Proj (grading k)).ringCatIsSheaf L) :
    complementRestrictHom f ((AlgebraicGeometry.Proj (grading k)).picardClass L hL) =
      Stacks.SheafOfModules.pullbackPicardClass (Proj.basicOpen (grading k) f).ι L hL := by
  obtain ⟨m, ⟨e⟩⟩ := Stacks.PicardUFD.exists_iso_twistingSheaf_general k 1 L hL
  have hm := Stacks.PicardUFD.isInvertible_twistingSheaf k 1 m
  have h1 : (AlgebraicGeometry.Proj (grading k)).picardClass L hL =
      Stacks.PicardUFD.twistPicardHom k 1 m :=
    (AlgebraicGeometry.Scheme.picardClass_eq_iff _ _ _ hL hm).mpr ⟨e⟩
  rw [h1, complementRestrictHom_twistPicardHom]
  exact (Stacks.SheafOfModules.pullbackPicardClass_congr _ _ _ hL hm e).symm

/-- **The restriction map `ℤ = Pic(ℙ¹_k) → Pic(X)` is surjective**, for
`X = ℙ¹_k ∖ V₊(f)`. -/
@[stacks 0CDP "the displayed surjection `ℤ = Pic(ℙ¹_k) → Pic(X)` for `X = ℙ¹_k ∖ {t}`, by \
Tag 0BD9 for the surjectivity and Tag 0BXJ for the identification of `Pic(ℙ¹_k)` with `ℤ`"]
theorem surjective_complementRestrictHom : Function.Surjective (complementRestrictHom f) := by
  intro c
  obtain ⟨m, hm⟩ := surjective_complementTwistClass f c
  exact ⟨Stacks.PicardUFD.twistPicardHom k 1 m,
    (complementRestrictHom_twistPicardHom f m).trans hm⟩

/-- **`Pic(X)` is killed by `d = deg f`.** -/
theorem nsmul_degree_eq_zero {d : ℕ} (hf : f ∈ grading k d)
    (c : (Proj.basicOpen (grading k) f).toScheme.picardGroup) : d • c = 0 := by
  obtain ⟨m, rfl⟩ := surjective_complementTwistClass f c
  have h2 : d • complementTwistClass f m = complementTwistClass f (m * d) := by
    show d • complementTwistHom f m = complementTwistHom f (m * d)
    rw [← map_nsmul]
    congr 1
    ring
  rw [h2, complementTwistClass_mul_degree f hf m]

/-- **The homomorphism `ℤ/dℤ → Pic(X)`** induced by `ℤ → Pic(X)`, for `X = ℙ¹_k ∖ V₊(f)` and
`d = deg f`. -/
def complementZModHom {d : ℕ} (hf : f ∈ grading k d) :
    ZMod d →+ (Proj.basicOpen (grading k) f).toScheme.picardGroup :=
  ZMod.lift d ⟨complementTwistHom f, by simpa using complementTwistClass_mul_degree f hf 1⟩

/-- The homomorphism `ℤ/dℤ → Pic(X)` sends the class of `m` to the class of `𝒪(m)|_X`. -/
@[simp]
theorem complementZModHom_intCast {d : ℕ} (hf : f ∈ grading k d) (m : ℤ) :
    complementZModHom f hf (m : ZMod d) = complementTwistClass f m :=
  ZMod.lift_coe _ _ m

/-- **The map `ℤ/dℤ → Pic(X)` is surjective**, for `X = ℙ¹_k ∖ V₊(f)` and `d = deg f`. -/
@[stacks 0CDP "the computation `Pic(X) = ℤ/dℤ` for `X = ℙ¹_k ∖ {t}`, surjectivity half: the \
displayed map factors through `ℤ/dℤ` by a surjection, `d = deg f = [κ(t) : k]`"]
theorem surjective_complementZModHom {d : ℕ} (hf : f ∈ grading k d) :
    Function.Surjective (complementZModHom f hf) := by
  intro c
  obtain ⟨m, hm⟩ := surjective_complementTwistClass f c
  exact ⟨(m : ZMod d), (complementZModHom_intCast f hf m).trans hm⟩

/-- **`Pic(X)` is killed by `d = [κ(t) : k]`**, the residue degree of the removed closed point
`t = V₊(f)` of `ℙ¹_k`. -/
@[stacks 0CDP "`Pic(X)` is killed by `d = [κ(t) : k]` for `X = ℙ¹_k ∖ {t}`, the residue degree \
read in the standard chart"]
theorem nsmul_finrank_residueField_eq_zero {d : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f)
    (hX : ¬ MvPolynomial.X (1 : Fin 2) ∣ f)
    [(Ideal.span {dehomogenize k f}).IsPrime]
    (c : (Proj.basicOpen (grading k) f).toScheme.picardGroup) :
    Module.finrank k (Ideal.span {dehomogenize k f}).ResidueField • c = 0 := by
  rw [finrank_residueField_span_dehomogenize hf hirr hX]
  exact nsmul_degree_eq_zero f (mem_grading hf) c

/-! ### The kernel: `𝒪(m)` is trivial on `X` only for `d ∣ m` -/

/-- **The kernel computation of [Stacks, Tag 0CDP], for a non-negative twist.** If `𝒪(m)` is
trivial on `X = ℙ¹_k ∖ {t}`, with `t = V₊(f)` a closed point of degree `d`, then `d ∣ m`. -/
theorem dvd_of_complementTwistClass_natCast_eq_zero {d m : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f)
    (hzero : complementTwistClass f (m : ℤ) = 0) : d ∣ m := by
  have hdpos := pos_of_irreducible hf hirr
  rcases le_or_gt 2 d with hd | hd
  · obtain ⟨e0⟩ := (Stacks.SheafOfModules.pullbackPicardClass_eq_zero_iff _ _ _).mp hzero
    have erest : Scheme.Modules.restrict
          (show (AlgebraicGeometry.Proj (grading k)).Modules from
            twistingSheaf (grading k) (m : ℤ))
          (Proj.basicOpen (grading k) f).ι ≅
        SheafOfModules.unit (Proj.basicOpen (grading k) f).toScheme.ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback (Proj.basicOpen (grading k) f).ι).app _ ≪≫ e0
    have s := Stacks.SheafOfModules.generatorOfOverIso _
      (Stacks.AlgebraicGeometry.TwistMapsInvertible.overIsoUnitOfRestrictIsoUnit
        (show (AlgebraicGeometry.Proj (grading k)).Modules from
          twistingSheaf (grading k) (m : ℤ))
        (Proj.basicOpen (grading k) f) erest)
    obtain ⟨n, hh, hhmem, hdvd⟩ :=
      exists_dvd_of_generatorSections (mem_grading hf) hdpos (m : ℤ) s
    have hcast : ∀ y : MvPolynomial (Fin 2) k, y.IsHomogeneous m →
        y ∈ AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading
          (S := MvPolynomial (Fin 2) k) (grading k) (((0 * d : ℕ) : ℤ) + (m : ℤ)) := by
      intro y hy
      rw [show (((0 * d : ℕ) : ℤ) + (m : ℤ)) = ((m : ℕ) : ℤ) by push_cast; ring,
        AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast]
      exact (MvPolynomial.mem_homogeneousSubmodule _ _).mpr hy
    obtain ⟨N0, hN0⟩ := hdvd 0 (MvPolynomial.X 0 ^ m)
      (hcast _ (by simpa using (MvPolynomial.isHomogeneous_X k (0 : Fin 2)).pow m))
    obtain ⟨N1, hN1⟩ := hdvd 0 (MvPolynomial.X 1 ^ m)
      (hcast _ (by simpa using (MvPolynomial.isHomogeneous_X k (1 : Fin 2)).pow m))
    have hhne : hh ≠ 0 := by
      rintro rfl
      exact mul_ne_zero (pow_ne_zero m
        (MvPolynomial.X_prime (R := k) (i := (0 : Fin 2))).irreducible.ne_zero)
        (pow_ne_zero N0 hirr.ne_zero) (zero_dvd_iff.mp hN0)
    have hhhom : hh.IsHomogeneous (n * d + m) := by
      rwa [show (((n * d : ℕ) : ℤ) + (m : ℤ)) = ((n * d + m : ℕ) : ℤ) by push_cast; ring,
        AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast] at hhmem
    exact (Nat.dvd_add_right (dvd_mul_left d n)).mp
      (dvd_of_isHomogeneous_dvd_mul_pow hf hirr hd hhhom hhne hN0 hN1)
  · exact (show d = 1 by lia) ▸ one_dvd m

/-- **The kernel computation of [Stacks, Tag 0CDP].** `𝒪(m)` is trivial on `X = ℙ¹_k ∖ {t}`
only when `d ∣ m`, for every integer `m`. -/
theorem dvd_of_complementTwistClass_eq_zero {d : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) {m : ℤ}
    (hzero : complementTwistClass f m = 0) : (d : ℤ) ∣ m := by
  have hnat : d ∣ m.natAbs := by
    rcases Int.natAbs_eq m with he | he
    · exact dvd_of_complementTwistClass_natCast_eq_zero hf hirr (he ▸ hzero)
    · refine dvd_of_complementTwistClass_natCast_eq_zero hf hirr ?_
      have h2 : complementTwistHom f (-m) = -complementTwistHom f m := map_neg _ _
      rw [complementTwistHom_apply, complementTwistHom_apply, hzero, neg_zero] at h2
      rw [show ((m.natAbs : ℤ)) = -m by lia]
      exact h2
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hnat)

/-- **`ℤ/dℤ → Pic(X)` is injective.** -/
theorem injective_complementZModHom {d : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    Function.Injective (complementZModHom f (mem_grading hf)) := by
  refine (ZMod.lift_injective (n := d)).mpr fun m hm => ?_
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m d).mpr
    (dvd_of_complementTwistClass_eq_zero hf hirr hm)

/-- **`Pic(X) = ℤ/dℤ`.** Let `t = V₊(f)` be the closed point of `ℙ¹_k` cut out by a homogeneous
irreducible form `f` of degree `d`, and let `X = ℙ¹_k ∖ {t}`. The surjection
`ℤ = Pic(ℙ¹_k) ↠ Pic(X)` has kernel `dℤ`, so it induces an isomorphism `ℤ/dℤ ≃ Pic(X)`. -/
@[stacks 0CDP "the computation `Pic(X) = ℤ/dℤ` for `X = ℙ¹_k ∖ {t}`, as the isomorphism \
`ℤ/dℤ ≃+ Pic(X)` induced by the displayed surjection, `d = deg f = [κ(t) : k]`"]
def complementZModEquiv {d : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    ZMod d ≃+ (Proj.basicOpen (grading k) f).toScheme.picardGroup :=
  AddEquiv.ofBijective (complementZModHom f (mem_grading hf))
    ⟨injective_complementZModHom hf hirr, surjective_complementZModHom f (mem_grading hf)⟩

/-- **`Pic(X) ≠ 0` for a non-rational point.** If the closed point `t = V₊(f)` of `ℙ¹_k` has
degree `d > 1`, equivalently is not a `k`-rational point, then the Picard group of
`X = ℙ¹_k ∖ {t}` is nonzero. -/
@[stacks 0CDP "`Pic(X) ≠ 0` for `X = ℙ¹_k ∖ {t}` when `t` is not a `k`-rational point, i.e. \
when `d = [κ(t) : k] > 1`; this is what makes the example a counterexample to Tag 0CC5"]
theorem nontrivial_picardGroup_basicOpen {d : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f) (hd : 2 ≤ d) :
    Nontrivial (Proj.basicOpen (grading k) f).toScheme.picardGroup := by
  refine ⟨⟨complementTwistClass f 1, 0, fun hcon => ?_⟩⟩
  have hdvd : (d : ℤ) ∣ 1 := dvd_of_complementTwistClass_eq_zero hf hirr hcon
  have := Int.le_of_dvd one_pos hdvd
  lia

/-- **`Pic(X) = ℤ/dℤ` with `d = [κ(t) : k]`**, the residue degree of the removed point read in
the standard chart. -/
theorem card_eq_finrank_residueField {d : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous d) (hirr : Irreducible f)
    (hX : ¬ MvPolynomial.X (1 : Fin 2) ∣ f)
    [(Ideal.span {dehomogenize k f}).IsPrime] :
    Nonempty (ZMod (Module.finrank k (Ideal.span {dehomogenize k f}).ResidueField) ≃+
      (Proj.basicOpen (grading k) f).toScheme.picardGroup) :=
  ⟨finrank_residueField_span_dehomogenize hf hirr hX ▸ complementZModEquiv hf hirr⟩

end Stacks.ProjectiveLine

end
