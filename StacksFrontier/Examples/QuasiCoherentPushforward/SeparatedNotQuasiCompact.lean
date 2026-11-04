module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent

/-!
# A separated non-quasi-compact morphism with non-quasi-coherent pushforward

Let `X = ∐_{n ∈ ℕ} Spec ℤ` and let `f : X ⟶ Spec ℤ` be the morphism which is the identity on
each summand. It is separated, since it factors as the open immersion
`∐ₙ Spec ℤ ⟶ Spec (∏ₙ ℤ)` followed by a morphism of affine schemes, and it is not
quasi-compact, since `X` itself is not compact. The structure sheaf of `X` is quasi-coherent,
but `f_* 𝒪_X` is not: the section of `f_* 𝒪_X` over `D(2) ⊆ Spec ℤ` whose `n`-th component is
`2⁻ⁿ` admits no uniform denominator, so the sections of `f_* 𝒪_X` over `D(2)` are not the
localization at `2` of its global sections.

Hence the quasi-compactness hypothesis in the theorem that pushforward preserves
quasi-coherence cannot be dropped.

## Main results

* `exists_isSeparated_not_quasiCompact_pushforward_not_isQuasicoherent`, in the namespace
  `Stacks.Examples.QcohPushforward`: such a morphism exists over the spectrum of the integers.

## Implementation notes

The structure sheaf is taken as the unit object `SheafOfModules.unit` of the category of
modules over itself, and quasi-coherence of the pushforward is tested through Mathlib's
criterion `AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`, which turns it into the
statement that sections over each standard open are the corresponding localization.

## References

* [Stacks Project, Tag 078D](https://stacks.math.columbia.edu/tag/078D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Examples.QcohPushforward

/-- The disjoint union of countably many copies of `Spec ℤ`. -/
private noncomputable abbrev countableSpecUnion : Scheme :=
  ∐ fun _ : ℕ => Spec (.of ℤ)

/-- The morphism `∐ₙ Spec ℤ ⟶ Spec ℤ` which is the identity on every summand. -/
private noncomputable abbrev countableSpecUnionMap :
    countableSpecUnion ⟶ Spec (.of ℤ) :=
  Sigma.desc fun _ : ℕ => (𝟙 (Spec (.of ℤ)))

/-- The structure sheaf of `∐ₙ Spec ℤ`, as a module over itself. -/
private noncomputable abbrev countableSpecUnionUnit : countableSpecUnion.Modules :=
  SheafOfModules.unit countableSpecUnion.ringCatSheaf

/-- Each summand inclusion followed by the structure morphism is the identity. -/
private theorem countableSpecUnionMap_comp_component (n : ℕ) :
    Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) n ≫ countableSpecUnionMap =
      𝟙 (Spec (.of ℤ)) := by simp [countableSpecUnionMap]

/-- The structure morphism is separated: over the terminal object `Spec ℤ` it agrees with the
composite of the open immersion `∐ₙ Spec ℤ ⟶ Spec (∏ₙ ℤ)` and a morphism of affines. -/
private theorem countableSpecUnionMap_separated :
    IsSeparated countableSpecUnionMap := by
  have h : countableSpecUnionMap =
      sigmaSpec (fun _ : ℕ => CommRingCat.of ℤ) ≫
        Scheme.Spec.map (CommRingCat.ofHom (Pi.constRingHom ℕ ℤ)).op :=
    specZIsTerminal.hom_ext _ _
  rw [h]
  apply (IsSeparated.comp_iff
    (f := sigmaSpec (fun _ : ℕ => CommRingCat.of ℤ))
    (g := Scheme.Spec.map (CommRingCat.ofHom (Pi.constRingHom ℕ ℤ)).op)).2
  infer_instance

/-- The structure morphism is not quasi-compact: the preimage of the affine open `Spec ℤ` is
the whole of `∐ₙ Spec ℤ`, which is not compact. -/
private theorem countableSpecUnionMap_not_quasiCompact :
    ¬ QuasiCompact countableSpecUnionMap := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro h
  have ht := h ⊤ (isAffineOpen_top _)
  change IsCompact (Set.univ : Set countableSpecUnion) at ht
  have hs : IsCompact (Set.univ : Set (Σ _ : ℕ, Spec (.of ℤ))) := by
    rw [← Set.image_univ_of_surjective (sigmaMk (fun _ : ℕ => Spec (.of ℤ))).symm.surjective]
    exact ht.image (sigmaMk (fun _ : ℕ => Spec (.of ℤ))).symm.continuous
  obtain ⟨s, t, hsfin, -, heq⟩ := hs.sigma_exists_finite_sigma_eq
  have hsub : (Set.univ : Set ℕ) ⊆ s := by
    intro n hn
    obtain ⟨p⟩ : Nonempty (Spec (.of ℤ)) := inferInstance
    have hm : ((⟨n, p⟩ : Σ _ : ℕ, Spec (.of ℤ))) ∈ Set.univ := Set.mem_univ _
    rw [← heq] at hm
    exact (Set.mem_sigma_iff.mp hm).1
  exact Set.infinite_univ.not_finite (hsfin.subset hsub)

/-- A module over a scheme has only the zero section over the empty open, since the ring of
functions there is the zero ring. -/
private lemma subsingleton_sections_bot (X : Scheme) (M : X.Modules) :
    Subsingleton Γ(M, ⊥) :=
  Module.subsingleton Γ(X, ⊥) _

/-- Sections of a module over an open subset of a disjoint union of schemes are exactly
families of sections over the parts cut out by the summands: the parts are pairwise disjoint,
so the compatibility condition is vacuous. -/
private lemma sigma_sections_bijective_on {ι : Type} (B : ι → Scheme)
    (U : (∐ B).Opens) (M : (∐ B).Modules) :
    Function.Bijective (fun (s : Γ(M, U)) (i : ι) =>
      M.presheaf.map (homOfLE (inf_le_left : U ⊓ (Sigma.ι B i ''ᵁ ⊤) ≤ U)).op s) := by
  classical
  let O (i : ι) : (∐ B).Opens := Sigma.ι B i ''ᵁ ⊤
  let P (i : ι) : (∐ B).Opens := U ⊓ O i
  have hO : ⨆ i, O i = ⊤ := by
    simp only [O, Scheme.Hom.image_top_eq_opensRange]
    exact (sigmaOpenCover B).iSup_opensRange
  have hP : ⨆ i, P i = U := by simp only [P, ← inf_iSup_eq, hO, inf_top_eq]
  let G : TopCat.Sheaf Ab (∐ B).toTopCat := ⟨M.presheaf, M.isSheaf⟩
  have hcompat (sf : ∀ i, Γ(M, P i)) :
      TopCat.Presheaf.IsCompatible G.1 P sf := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hd : P i ⊓ P j = ⊥ := by
        simp only [P, O, inf_assoc, inf_left_comm]
        rw [show O i ⊓ O j = ⊥ by
          simpa only [O, Scheme.Hom.image_top_eq_opensRange] using
            (disjoint_iff.mp (disjoint_opensRange_sigmaι B i j hij))]
        simp
      have : Subsingleton (G.obj.obj (Opposite.op (P i ⊓ P j))) := by
        rw [hd]
        exact subsingleton_sections_bot _ M
      exact Subsingleton.elim _ _
  rw [Function.bijective_iff_existsUnique]
  intro sf
  obtain ⟨gl, hgl, huniq⟩ := G.existsUnique_gluing' P U
    (fun i => homOfLE (inf_le_left : P i ≤ U)) (by rw [hP]) sf (hcompat sf)
  exact ⟨gl, funext hgl, fun s hs => huniq s (congrFun hs)⟩

/-- No single power of `2` is a common numerator for the family `2⁻ⁿ`: if `2ⁿ xₙ = 2ᵏ` for all
`n`, then taking `n = k + 1` makes `2` a unit in `ℤ`. -/
private theorem no_uniform_two_denominator (k : ℕ) (x : ℕ → ℤ)
    (h : ∀ n, (2 : ℤ) ^ n * x n = (2 : ℤ) ^ k) : False := by
  have hmul : (2 : ℤ) ^ k * ((2 : ℤ) * x (k + 1)) = (2 : ℤ) ^ k * 1 := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h (k + 1)
  have hbad : (2 : ℤ) * x (k + 1) = 1 := mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hmul
  omega

/-- The standard open `D(2) ⊆ Spec ℤ`. -/
private noncomputable abbrev twoBasicOpen : (Spec (.of ℤ)).Opens :=
  PrimeSpectrum.basicOpen (2 : ℤ)

/-- The algebra structure of the sections of the structure sheaf over a standard open. -/
private noncomputable instance (priority := 2000) specBasicOpenAlgebra
    (R : CommRingCat) (r : R) :
    Algebra R Γ(Spec R, PrimeSpectrum.basicOpen r) :=
  inferInstanceAs (Algebra R
    ((Spec.structureSheaf R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen r))))

/-- The sections of the structure sheaf over a standard open `D(r)` are the localization of
the ring at `r`. -/
private noncomputable instance (priority := 2000) specBasicOpenIsLocalization
    (R : CommRingCat) (r : R) :
    IsLocalization.Away r Γ(Spec R, PrimeSpectrum.basicOpen r) :=
  inferInstanceAs (IsLocalization.Away r
    ((Spec.structureSheaf R).obj.obj (Opposite.op (PrimeSpectrum.basicOpen r))))

/-- The section `r⁻ⁿ` of the structure sheaf over the standard open `D(r)`. -/
private noncomputable def inversePowerSection (R : CommRingCat) (r : R) (n : ℕ) :
    Γ(Spec R, PrimeSpectrum.basicOpen r) :=
  IsLocalization.mk' (M := Submonoid.powers r) Γ(Spec R, PrimeSpectrum.basicOpen r) (1 : R)
    ⟨r ^ n, ⟨n, rfl⟩⟩

/-- The section `r⁻ⁿ` is inverse to `rⁿ` on `D(r)`. -/
private lemma pow_mul_inversePowerSection (R : CommRingCat) (r : R) (n : ℕ) :
    (algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r)) r ^ n *
      inversePowerSection R r n = 1 := by
  simpa only [inversePowerSection, ← map_pow, map_one] using
    IsLocalization.mk'_spec' (M := Submonoid.powers r)
      Γ(Spec R, PrimeSpectrum.basicOpen r) (1 : R) ⟨r ^ n, ⟨n, rfl⟩⟩

/-- Over a domain, restriction of a global constant to a nonempty standard open is injective,
since the powers of a nonzero element are nonzerodivisors. -/
private lemma basicOpen_constants_injective (R : CommRingCat) [NoZeroDivisors R]
    (r : R) (hr : r ≠ 0) :
    Function.Injective (fun x : R => (Spec R).presheaf.map
      (PrimeSpectrum.basicOpen r).leTop.op ((Scheme.ΓSpecIso R).inv x)) :=
  IsLocalization.injective Γ(Spec R, PrimeSpectrum.basicOpen r)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hr)

/-- The preimage of `D(2)` in `∐ₙ Spec ℤ`. -/
private noncomputable abbrev sourceTwoOpen : countableSpecUnion.Opens :=
  countableSpecUnionMap ⁻¹ᵁ twoBasicOpen

/-- The part of the preimage of `D(2)` lying in the `i`-th summand. -/
private noncomputable abbrev sourceTwoPart (i : ℕ) : countableSpecUnion.Opens :=
  sourceTwoOpen ⊓ Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i ''ᵁ ⊤

/-- The preimage of `D(2)` meets the `i`-th summand in `D(2)` again. -/
private theorem sourceTwoOpen_preimage_component (i : ℕ) :
    (Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i) ⁻¹ᵁ sourceTwoOpen = twoBasicOpen := by
  change (Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i) ⁻¹ᵁ
    (countableSpecUnionMap ⁻¹ᵁ twoBasicOpen) = twoBasicOpen
  rw [← Scheme.Hom.comp_preimage, countableSpecUnionMap_comp_component]
  simp

/-- The `i`-th part of the preimage of `D(2)` is the image of `D(2)` under the `i`-th summand
inclusion. -/
private theorem sourceTwoPart_eq (i : ℕ) :
    sourceTwoPart i = Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i ''ᵁ twoBasicOpen := by
  change (sourceTwoOpen ⊓ Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i ''ᵁ ⊤) = _
  rw [inf_comm, Scheme.Hom.image_top_eq_opensRange,
    ← Scheme.Hom.image_preimage_eq_opensRange_inf, sourceTwoOpen_preimage_component]

/-- The section `2⁻ⁱ` on the `i`-th part of the preimage of `D(2)`. -/
private noncomputable def componentBadSection (i : ℕ) :
    Γ(countableSpecUnionUnit, sourceTwoPart i) :=
  countableSpecUnion.presheaf.map (eqToHom (sourceTwoPart_eq i)).op
    (((Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i).appIso twoBasicOpen).inv
      (inversePowerSection (.of ℤ) 2 i))

/-- The sections `2⁻ⁱ` glue to a single section of the structure sheaf over the preimage
of `D(2)`. -/
private lemma exists_badLocalSection :
    ∃ s : Γ(countableSpecUnionUnit, sourceTwoOpen),
      ∀ i : ℕ,
        countableSpecUnionUnit.presheaf.map
          (homOfLE (inf_le_left : sourceTwoPart i ≤ sourceTwoOpen)).op s =
            componentBadSection i := by
  obtain ⟨s, hs⟩ := (sigma_sections_bijective_on
    (fun _ : ℕ => Spec (.of ℤ)) sourceTwoOpen countableSpecUnionUnit).2 componentBadSection
  exact ⟨s, congrFun hs⟩

/-- The glued section of the structure sheaf over the preimage of `D(2)` whose `i`-th
component is `2⁻ⁱ`. -/
private noncomputable def badLocalSection : Γ(countableSpecUnion, sourceTwoOpen) :=
  Classical.choose exists_badLocalSection

/-- The `i`-th component of the glued section is `2⁻ⁱ`. -/
private lemma badLocalSection_component (i : ℕ) :
    (Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i).appLE sourceTwoOpen twoBasicOpen
      (sourceTwoOpen_preimage_component i).ge badLocalSection =
        inversePowerSection (.of ℤ) 2 i := by
  apply (ConcreteCategory.bijective_of_isIso
    ((Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i).appIso twoBasicOpen).inv).1
  rw [Scheme.Hom.appLE_appIso_inv_apply]
  have h := Classical.choose_spec exists_badLocalSection i
  change countableSpecUnion.presheaf.map
    (homOfLE (inf_le_left : sourceTwoPart i ≤ sourceTwoOpen)).op badLocalSection =
      componentBadSection i at h
  have h' := congrArg
    (countableSpecUnion.presheaf.map (eqToHom (sourceTwoPart_eq i).symm).op) h
  simp only [componentBadSection, ← CommRingCat.comp_apply, Category.assoc,
    ← Functor.map_comp, ← op_comp] at h'
  simpa using h'

/-- **Stacks Project, Tag 078D (non-quasi-compact case).** Over `Spec ℤ`, a separated,
non-quasi-compact morphism can push a quasi-coherent structure sheaf to a sheaf which is not
quasi-coherent. -/
@[stacks 078D "non_quasi_compact"]
theorem exists_isSeparated_not_quasiCompact_pushforward_not_isQuasicoherent :
    ∃ (X : Scheme) (f : X ⟶ Spec (.of ℤ)),
      IsSeparated f ∧ ¬ QuasiCompact f ∧
        (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent ∧
          ¬ ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent := by
  refine ⟨countableSpecUnion, countableSpecUnionMap,
    countableSpecUnionMap_separated, countableSpecUnionMap_not_quasiCompact,
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _, ?_⟩
  let M := (Scheme.Modules.pushforward countableSpecUnionMap).obj
    (SheafOfModules.unit countableSpecUnion.ringCatSheaf)
  intro hqc
  have hAway : IsLocalizedModule.Away (2 : ℤ)
      (((AlgebraicGeometry.modulesSpecToSheaf (R := CommRingCat.of ℤ)).obj M).obj.map
        (twoBasicOpen.leTop).op).hom :=
    (AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing M).mp
      ((AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ M).mp hqc) (2 : ℤ)
  obtain ⟨k, x, hx⟩ := IsLocalizedModule.Away.surj
    (((AlgebraicGeometry.modulesSpecToSheaf (R := CommRingCat.of ℤ)).obj M).obj.map
      (twoBasicOpen.leTop).op).hom (2 : ℤ) badLocalSection
  change countableSpecUnionMap.app twoBasicOpen
      ((Spec (.of ℤ)).presheaf.map twoBasicOpen.leTop.op
        ((Scheme.ΓSpecIso (.of ℤ)).inv ((2 : ℤ) ^ k))) * badLocalSection =
    countableSpecUnion.presheaf.map
      ((TopologicalSpace.Opens.map countableSpecUnionMap.base).map
        twoBasicOpen.leTop).op x at hx
  simp only [map_pow, map_ofNat] at hx
  let value (i : ℕ) : Γ(Spec (.of ℤ), ⊤) :=
    (Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i).appLE
      (countableSpecUnionMap ⁻¹ᵁ ⊤) ⊤ (by simp) x
  apply no_uniform_two_denominator k
    (fun i => (Scheme.ΓSpecIso (.of ℤ)).hom (value i))
  intro i
  let si := Sigma.ι (fun _ : ℕ => Spec (.of ℤ)) i
  have hi := congrArg
    (si.appLE sourceTwoOpen twoBasicOpen (sourceTwoOpen_preimage_component i).ge) hx
  simp only [si, map_mul, map_pow, map_ofNat, badLocalSection_component] at hi
  have hres :
      si.appLE sourceTwoOpen twoBasicOpen (sourceTwoOpen_preimage_component i).ge
        (countableSpecUnion.presheaf.map
          ((TopologicalSpace.Opens.map countableSpecUnionMap.base).map
            twoBasicOpen.leTop).op x) =
      (Spec (.of ℤ)).presheaf.map twoBasicOpen.leTop.op (value i) := by
    have hleft := Scheme.Hom.map_appLE (f := si) (U := sourceTwoOpen) (V := twoBasicOpen)
      (sourceTwoOpen_preimage_component i).ge
      ((TopologicalSpace.Opens.map countableSpecUnionMap.base).map twoBasicOpen.leTop).op
    have hright := Scheme.Hom.appLE_map (f := si) (U := countableSpecUnionMap ⁻¹ᵁ ⊤)
      (V := (⊤ : (Spec (.of ℤ)).Opens)) (V' := twoBasicOpen) (by simp)
      twoBasicOpen.leTop.op
    calc
      _ = (countableSpecUnion.presheaf.map
            ((TopologicalSpace.Opens.map countableSpecUnionMap.base).map
              twoBasicOpen.leTop).op ≫
          si.appLE sourceTwoOpen twoBasicOpen
            (sourceTwoOpen_preimage_component i).ge) x := rfl
      _ = (si.appLE (countableSpecUnionMap ⁻¹ᵁ ⊤) twoBasicOpen _) x := by rw [hleft]
      _ = (si.appLE (countableSpecUnionMap ⁻¹ᵁ ⊤) (⊤ : (Spec (.of ℤ)).Opens) (by simp) ≫
          (Spec (.of ℤ)).presheaf.map twoBasicOpen.leTop.op) x := by rw [hright]
      _ = _ := rfl
  rw [hres] at hi
  have hinv : (2 : Γ(Spec (.of ℤ), twoBasicOpen)) ^ i *
      inversePowerSection (.of ℤ) 2 i = 1 := by
    simpa only [map_ofNat] using pow_mul_inversePowerSection (.of ℤ) 2 i
  have heq :
      (Spec (.of ℤ)).presheaf.map twoBasicOpen.leTop.op
        ((2 : Γ(Spec (.of ℤ), ⊤)) ^ i * value i) =
      (Spec (.of ℤ)).presheaf.map twoBasicOpen.leTop.op
        ((2 : Γ(Spec (.of ℤ), ⊤)) ^ k) := by
    simp only [map_mul, map_pow, map_ofNat]
    rw [← hi, mul_left_comm, hinv, mul_one]
  have hglobal : (2 : Γ(Spec (.of ℤ), ⊤)) ^ i * value i = 2 ^ k :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of ℤ)).hom).1
      (basicOpen_constants_injective (.of ℤ) 2 (by norm_num)
        (a₁ := (Scheme.ΓSpecIso (.of ℤ)).hom ((2 : Γ(Spec (.of ℤ), ⊤)) ^ i * value i))
        (a₂ := (Scheme.ΓSpecIso (.of ℤ)).hom ((2 : Γ(Spec (.of ℤ), ⊤)) ^ k))
        (by simpa only [Iso.hom_inv_id_apply] using heq))
  simpa only [map_mul, map_pow, map_ofNat] using
    congrArg (Scheme.ΓSpecIso (.of ℤ)).hom hglobal

end Stacks.Examples.QcohPushforward
