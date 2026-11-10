module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurveProper
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothBadPoint
public import StacksFrontier.AlgebraicGeometry.NodalContraction.DvrStalk
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.NormalizedPointBlowupSequence

/-!
# Contracting a component of the special fibre of a regular proper model

In the situation of [Stacks, Tag 0C61] let `C_n ⊆ X_k` be an irreducible component of the
special fibre and let `f : X ⟶ X'` be a contraction of `C_n`: the blowup of a regular closed point
`x ∈ X'` of dimension two, with exceptional divisor `C_n`. This file shows that `X'` is again a
regular proper model of the same curve, which is the first assertion of [Stacks, Tag 0C6C].

The structure morphism `X ⟶ Spec R` carries `C_n` into the closed point, so it factors uniquely
through `f` ([Stacks, Tag 0C5J]); the factorisation is proper ([Stacks, Tag 0C2M] (2)). The
scheme `X'` is regular: at `x` by definition of a contraction, elsewhere because `f` is an
isomorphism over `X' ∖ {x}`. It is flat over `R`, because its local rings are domains and the
stalk maps of `X' ⟶ Spec R` are injective, `f` being surjective and `X` flat over `R`. Finally `x`
lies over the closed point of `Spec R`, so `f` is an isomorphism over the generic point and the
generic fibre of `X'` is that of `X`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.contractionToBase` — the structure morphism
  `X' ⟶ Spec R` of the contracted model.
* `Stacks.Models.RegularProperModelSituation.contractedSituation` — the regular proper model
  `X' ⟶ Spec R` of the same curve, over the same discrete valuation ring.

## Main results

* `AlgebraicGeometry.IsContractionOfExceptionalCurve.exists_centre` — a contraction contracts its
  curve to a regular closed point of dimension two and is an isomorphism over the complement.
* `AlgebraicGeometry.IsContractionOfExceptionalCurve.isRegular` — the target of a contraction of
  a regular scheme is regular.
* `Stacks.Models.RegularProperModelSituation.contraction_comp_contractionToBase` — the contraction
  is a morphism over `Spec R`.

## Implementation notes

The contracted situation is built as `{ S with X := X', X_to_R := … }`, so the discrete valuation
ring, its fraction and residue fields, the uniformizer and the curve `C` of the contracted
situation are those of `S` definitionally. The statement holds for every contraction `f` of
`C_n`; that `C_n` is an exceptional curve of the first kind is what makes one exist
([Stacks, Tag 0C2M]), and is not otherwise used.

## References

* [Stacks Project, Tag 0C6C](https://stacks.math.columbia.edu/tag/0C6C)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### The centre of a contraction -/

/-- **The centre of a contraction.** A contraction `b : X ⟶ X'` of an ideal sheaf `D` carries the
support of `D` onto a closed point `z` of `X'` whose local ring is regular of dimension two, the
support of `D` is exactly the fibre over `z`, and `b` is an isomorphism over `X' ∖ {z}`. -/
public theorem IsContractionOfExceptionalCurve.exists_centre {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) :
    ∃ (z : X') (hz : IsClosed ({z} : Set X')),
      IsRegularLocalRing (X'.presheaf.stalk z) ∧ ringKrullDim (X'.presheaf.stalk z) = 2 ∧
        (∀ x : X, x ∈ (D.support : Set X) ↔ b x = z) ∧
        IsIso (b ∣_ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens)) := by
  obtain ⟨z, hz, hreg, hdim, hD, e, he⟩ := hb.exists_blowUp_iso
  refine ⟨z, hz, hreg, hdim, fun x => ?_,
    isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) e he⟩
  rw [hD, Scheme.IdealSheafData.support_comap]
  change b x ∈ ((Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).support :
    Set X') ↔ b x = z
  simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk,
    Set.mem_singleton_iff]

/-- A point of the target over which a morphism restricts to an isomorphism has a preimage. -/
public theorem exists_eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)] (y : Y) (hy : y ∈ U) : ∃ x : X, f x = y := by
  obtain ⟨x, hx⟩ := (asIso (f ∣_ U)).hom.homeomorph.surjective ⟨y, hy⟩
  refine ⟨(f ⁻¹ᵁ U).ι x, ?_⟩
  have h : ((f ∣_ U) ≫ U.ι) x = y := congrArg (fun t : U => (t : Y)) hx
  rwa [morphismRestrict_ι] at h

/-- A point other than the centre has a preimage when the contraction is an isomorphism over the
complement of the centre. -/
private theorem exists_eq_of_ne_of_isIso_morphismRestrict_compl {X Y : Scheme.{u}} (f : X ⟶ Y)
    {z : Y} (hz : IsClosed ({z} : Set Y))
    (hiso : IsIso (f ∣_ (⟨({z} : Set Y)ᶜ, hz.isOpen_compl⟩ : Y.Opens))) {y : Y} (hy : y ≠ z) :
    ∃ x : X, f x = y :=
  exists_eq_of_isIso_morphismRestrict f (⟨({z} : Set Y)ᶜ, hz.isOpen_compl⟩ : Y.Opens) y hy

/-- A contraction is an isomorphism on local rings at every point off the contracted curve. -/
public theorem IsContractionOfExceptionalCurve.isIso_stalkMap {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) {x : X}
    (hx : x ∉ (D.support : Set X)) : IsIso (b.stalkMap x) := by
  obtain ⟨z, hz, -, -, hsupp, hiso⟩ := hb.exists_centre
  exact isIso_stalkMap_of_isIso_morphismRestrict b hiso fun h => hx ((hsupp x).2 h)

/-- **The target of a contraction of a regular scheme is regular.** At the centre this is part of
the definition of a contraction; elsewhere the contraction is an isomorphism. -/
public theorem IsContractionOfExceptionalCurve.isRegular {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b)
    (hX : IsRegular X) : IsRegular X' := by
  obtain ⟨z, hz, hzreg, -, hsupp, hiso⟩ := hb.exists_centre
  have hX12 := (isRegular_tfae X).out 1 2
  have hX'12 := (isRegular_tfae X').out 1 2
  have hXstalk : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := (hX12.mp hX).2
  have : IsNoetherian X' := hb.isNoetherian
  refine hX'12.mpr ⟨inferInstance, fun y => ?_⟩
  by_cases hy : y = z
  · subst hy
    exact hzreg
  · obtain ⟨x, rfl⟩ := exists_eq_of_ne_of_isIso_morphismRestrict_compl b hz hiso hy
    have : IsIso (b.stalkMap x) := hb.isIso_stalkMap fun h => hy ((hsupp x).1 h)
    have : IsRegularLocalRing (X.presheaf.stalk x) := hXstalk x
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (b.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-- **A contraction with nonempty curve is surjective.** Away from the centre it is an
isomorphism, and the centre is the image of any point of the contracted curve. -/
public theorem IsContractionOfExceptionalCurve.surjective {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b)
    (hD : (D.support : Set X).Nonempty) : Function.Surjective b.base := by
  obtain ⟨z, hz, -, -, hsupp, hiso⟩ := hb.exists_centre
  intro y
  by_cases hy : y = z
  · obtain ⟨x, hx⟩ := hD
    exact ⟨x, ((hsupp x).1 hx).trans hy.symm⟩
  · exact exists_eq_of_ne_of_isIso_morphismRestrict_compl b hz hiso hy

/-- **Properness over an affine Noetherian base descends along a surjective contraction.** If
`b : X ⟶ X'` contracts an ideal sheaf with nonempty support and `b ≫ f'` is proper over `Spec R`
with `R` Noetherian, then `f'` is proper: universal closedness and separatedness descend along
the proper surjection `b`, and finite type descends by
`AlgebraicGeometry.locallyOfFiniteType_of_isContractionOfExceptionalCurve`. -/
public theorem IsContractionOfExceptionalCurve.isProper_of_isProper_comp
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b)
    (hD : (D.support : Set X).Nonempty) (f' : X' ⟶ Spec (.of R)) (hf : IsProper (b ≫ f')) :
    IsProper f' := by
  have := hf
  have := hb.isProper
  have : Surjective b := ⟨hb.surjective hD⟩
  have hUC : UniversallyClosed f' := UniversallyClosed.of_comp_surjective b f'
  have hsep : IsSeparated f' := by
    let g : (Over.mk (b ≫ f') : Over (Spec (.of R))) ⟶ Over.mk f' := Over.homMk b rfl
    have : Surjective g.left := show Surjective b from inferInstance
    have : UniversallyClosed g.left := show UniversallyClosed b from inferInstance
    have : IsSeparated (Over.mk (b ≫ f') : Over (Spec (.of R))).hom :=
      show IsSeparated (b ≫ f') from inferInstance
    exact isSeparated_of_surjective_universallyClosed g
  have : LocallyOfFiniteType f' :=
    locallyOfFiniteType_of_isContractionOfExceptionalCurve hb f'
  exact (isProper_iff f').2 ⟨hsep, hUC, inferInstance⟩

/-! ### Flatness over a principal ideal domain -/

/-- **Flatness over a principal ideal domain descends along a surjection to a scheme with
integral local rings.** Let `R` be a principal ideal domain, `b : X ⟶ Y` surjective and
`f : Y ⟶ Spec R` such that `b ≫ f` is flat. If every local ring of `Y` is a domain, `f` is flat:
its stalk maps are injective, and an injective map from a Bézout domain to a domain is flat. -/
public theorem flat_of_surjective_of_flat_comp {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {X Y : Scheme.{u}} (b : X ⟶ Y) (f : Y ⟶ Spec (.of R))
    [Flat (b ≫ f)] (hb : Function.Surjective b.base)
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) : Flat f := by
  refine Flat.of_stalkMap _ fun y => ?_
  have := hY y
  have : IsDomain ((Spec (.of R)).presheaf.stalk (f y)) := isDomain_stalk_spec (f y)
  have : IsPrincipalIdealRing ((Spec (.of R)).presheaf.stalk (f y)) :=
    isPrincipalIdealRing_stalk_spec (f y)
  let := (f.stalkMap y).hom.toAlgebra
  change Module.Flat _ _
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
  -- the stalk map is a right factor of an injective stalk map of `b ≫ f`
  obtain ⟨x, rfl⟩ := hb y
  have key : ∀ w : (Spec (.of R)).presheaf.stalk (f (b x)),
      (b.stalkMap x).hom ((f.stalkMap (b x)).hom w) = ((b ≫ f).stalkMap x).hom w := by
    intro w
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hinj : Function.Injective ((b ≫ f).stalkMap x).hom := by
    let := ((b ≫ f).stalkMap x).hom.toAlgebra
    have : Module.Flat ((Spec (.of R)).presheaf.stalk ((b ≫ f) x)) (X.presheaf.stalk x) :=
      Flat.stalkMap (b ≫ f) x
    have : IsLocalHom (algebraMap ((Spec (.of R)).presheaf.stalk ((b ≫ f) x))
        (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom ((b ≫ f).stalkMap x).hom)
    exact RingHom.FaithfullyFlat.injective (Module.FaithfullyFlat.of_flat_of_isLocalHom)
  intro a a' ha
  refine hinj ?_
  rw [← key a, ← key a']
  exact congrArg (b.stalkMap x).hom ha

end AlgebraicGeometry

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-! ### The structure morphism of the contracted model -/

/-- The model morphism carries every irreducible component of the special fibre to a single
point of `Spec R`, the closed point: the component lies over `Spec k`. -/
public theorem exists_X_to_R_eq_of_specialFiberComponent
    (Z : irreducibleComponents S.specialFiber) :
    ∃ y : Spec (.of S.R), ∀ z : (S.specialFiberComponentIdeal Z).subscheme,
      S.X_to_R ((S.specialFiberComponentIdeal Z).subschemeι z) = y := by
  rcases isEmpty_or_nonempty (S.specialFiberComponentIdeal Z).subscheme with hemp | hne
  · exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S.R), fun z => (hemp.false z).elim⟩
  · obtain ⟨z₀⟩ := hne
    refine ⟨S.X_to_R ((S.specialFiberComponentIdeal Z).subschemeι z₀), fun z => ?_⟩
    have h := S.specialFiberComponentToSpec_comp Z
    have hz := congrArg (fun g => g z) h
    have hz₀ := congrArg (fun g => g z₀) h
    simp only [Scheme.Hom.comp_apply] at hz hz₀
    rw [← hz, ← hz₀, Subsingleton.elim (S.specialFiberComponentToSpec Z z)
      (S.specialFiberComponentToSpec Z z₀)]

/-- The support of the ideal sheaf of an irreducible component of the special fibre is
nonempty. -/
public theorem nonempty_support_specialFiberComponentIdeal
    (Z : irreducibleComponents S.specialFiber) :
    (((S.specialFiberComponentIdeal Z).support : Closeds S.X) : Set S.X).Nonempty := by
  rw [S.coe_support_specialFiberComponentIdeal Z]
  exact Z.2.1.1.image _

/-- No point of the special fibre lies over the generic point of `Spec R`: the uniformizer
vanishes in `k` and not in `K`. -/
public theorem specMap_residueField_ne_specMap_fractionField (x : Spec (.of S.k))
    (y : Spec (.of S.K)) :
    Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) x ≠
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) y := by
  have hπk : algebraMap S.R S.k S.π = 0 := by
    rw [← S.residueEquiv.commutes]
    change S.residueEquiv (IsLocalRing.residue S.R S.π) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr
      (show S.π ∈ IsLocalRing.maximalIdeal S.R from S.uniformizer.not_isUnit), map_zero]
  intro h
  have hmem : S.π ∈ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) x).asIdeal := by
    change algebraMap S.R S.k S.π ∈ x.asIdeal
    rw [hπk]
    exact Ideal.zero_mem _
  rw [h] at hmem
  have hy : y = genericPoint (Spec (.of S.K)) := Subsingleton.elim _ _
  rw [hy, genericPoint_eq_bot_of_affine] at hmem
  change algebraMap S.R S.K S.π = 0 at hmem
  exact S.uniformizer.ne_zero ((IsFractionRing.injective S.R S.K) (by simpa using hmem))

variable {N : irreducibleComponents S.specialFiber} {X' : Scheme.{u}} {f : S.X ⟶ X'}

/-- The model morphism factors uniquely through a contraction of a component of the special
fibre ([Stacks, Tag 0C5J]): the component is carried to the closed point of `Spec R`. -/
public theorem existsUnique_comp_eq_X_to_R
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    ∃! p : X' ⟶ Spec (.of S.R), f ≫ p = S.X_to_R :=
  existsUnique_comp_eq_of_isContractionOfExceptionalCurve _ f hf S.X_to_R
    (S.exists_X_to_R_eq_of_specialFiberComponent N)

/-- **The structure morphism of the contracted model**: the unique `p : X' ⟶ Spec R` with
`f ≫ p = (X ⟶ Spec R)`. -/
public def contractionToBase
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    X' ⟶ Spec (.of S.R) :=
  (S.existsUnique_comp_eq_X_to_R hf).exists.choose

/-- The contraction is a morphism over `Spec R`. -/
@[reassoc (attr := simp)]
public theorem contraction_comp_contractionToBase
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    f ≫ S.contractionToBase hf = S.X_to_R :=
  (S.existsUnique_comp_eq_X_to_R hf).exists.choose_spec

/-- The structure morphism of the contracted model is proper ([Stacks, Tag 0C2M] (2)). -/
public theorem isProper_contractionToBase
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    IsProper (S.contractionToBase hf) :=
  hf.isProper_of_isProper_comp (S.nonempty_support_specialFiberComponentIdeal N) _
    (by rw [S.contraction_comp_contractionToBase hf]; infer_instance)

/-- The contraction is surjective. -/
public theorem surjective_contraction
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    Function.Surjective f.base :=
  hf.surjective (S.nonempty_support_specialFiberComponentIdeal N)

/-- The structure morphism of the contracted model is flat: the local rings of `X'` are regular,
hence domains, and `f` is surjective with `X` flat over `R`. -/
public theorem flat_contractionToBase
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    Flat (S.contractionToBase hf) := by
  have : Flat (f ≫ S.contractionToBase hf) := by
    rw [S.contraction_comp_contractionToBase hf]; infer_instance
  have hreg := hf.isRegular S.regular
  have h12 := (isRegular_tfae X').out 1 2
  have hstalk := (h12.mp hreg).2
  exact flat_of_surjective_of_flat_comp f _ (S.surjective_contraction hf)
    fun y => have := hstalk y; IsRegularLocalRing.isDomain _

/-- The centre of the contraction lies over the closed point of `Spec R`, so the generic fibre of
`X'` misses it. -/
theorem range_pullbackFst_contractionToBase_subset
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) {z : X'}
    (hz : ∀ x : S.X, x ∈ ((S.specialFiberComponentIdeal N).support : Set S.X) ↔ f x = z) :
    Set.range (pullback.fst (S.contractionToBase hf)
        (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))) ⊆ ({z} : Set X')ᶜ := by
  rintro _ ⟨y, rfl⟩ hy
  obtain ⟨x, hx⟩ := S.nonempty_support_specialFiberComponentIdeal N
  have hx' := hx
  rw [S.coe_support_specialFiberComponentIdeal N] at hx'
  obtain ⟨w, -, rfl⟩ := hx'
  let jk := Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))
  let jK := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))
  apply S.specMap_residueField_ne_specMap_fractionField (pullback.snd S.X_to_R jk w)
    (pullback.snd (S.contractionToBase hf) jK y)
  calc jk (pullback.snd S.X_to_R jk w)
      = S.X_to_R (S.specialFiberι w) :=
        (congrArg (fun g => g w) (pullback.condition (f := S.X_to_R) (g := jk))).symm
    _ = S.contractionToBase hf (f (S.specialFiberι w)) := by
        rw [← S.contraction_comp_contractionToBase hf]; rfl
    _ = S.contractionToBase hf (pullback.fst (S.contractionToBase hf) jK y) := by
        rw [(hz _).1 hx, hy]
    _ = _ := congrArg (fun g => g y) (pullback.condition (f := S.contractionToBase hf)
          (g := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))

/-- The contraction is an isomorphism over the generic fibre of the contracted model. -/
public instance isIso_pullbackSnd_contraction_genericFiber
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    IsIso (pullback.snd f (pullback.fst (S.contractionToBase hf)
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))) := by
  obtain ⟨z, hz, -, -, hsupp, hiso⟩ := hf.exists_centre
  exact isIso_pullback_snd_of_isIso_morphismRestrict f _
    (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens) hiso
    fun y => S.range_pullbackFst_contractionToBase_subset hf hsupp ⟨y, rfl⟩

/-- **The generic fibre of the contracted model is the curve.** It is the generic fibre of `X`,
the contraction being an isomorphism over it. -/
public def contractedGenericFiberIso
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    S.C ≅ pullback (S.contractionToBase hf) (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) :=
  S.genericFiberIso ≪≫ pullback.congrHom (S.contraction_comp_contractionToBase hf).symm rfl ≪≫
    (pullbackRightPullbackFstIso _ _ f).symm ≪≫ asIso (pullback.snd f _)

/-- The generic fibre isomorphism of the contracted model lies over `Spec K`. -/
public theorem contractedGenericFiberIso_hom_snd
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    (S.contractedGenericFiberIso hf).hom ≫ pullback.snd (S.contractionToBase hf)
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) = S.C_to_K := by
  simp only [contractedGenericFiberIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd]
  rw [← S.genericFiberIso_over_K]
  congr 1
  simp only [pullback.congrHom, pullback.map, Category.comp_id]
  exact pullback.lift_snd _ _ _

/-- The contraction carries the generic fibre isomorphism of `X` to that of the contracted
model: on the curve, `f` followed by the inclusion of the generic fibre is the inclusion of the
generic fibre of `X`. -/
public theorem contractedGenericFiberIso_hom_fst
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    (S.contractedGenericFiberIso hf).hom ≫ pullback.fst (S.contractionToBase hf)
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) =
      S.genericFiberIso.hom ≫ pullback.fst S.X_to_R _ ≫ f := by
  simp only [contractedGenericFiberIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc]
  simp only [pullback.congrHom, pullback.map, Category.comp_id, asIso_hom]
  rw [pullback.lift_fst_assoc]

/-- **Stacks Project, Tag 0C6C, the contracted model.** Let `f : X ⟶ X'` contract an
irreducible component `C_n` of the special fibre of a regular proper model `X` of `C`. Then `X'`,
with the structure morphism through which `X ⟶ Spec R` factors, is again a regular proper model
of `C` over the same discrete valuation ring: it is the standing situation of
[Stacks, Tag 0C61] with `X'` in place of `X`. -/
@[stacks 0C6C "X' is as in Situation 0C61: a regular proper model of the same curve"]
public abbrev contractedSituation
    (hf : IsContractionOfExceptionalCurve (S.specialFiberComponentIdeal N) f) :
    RegularProperModelSituation.{u} :=
  { S with
    X := X'
    X_to_R := S.contractionToBase hf
    flat := S.flat_contractionToBase hf
    locallyOfFiniteType := haveI := S.isProper_contractionToBase hf; inferInstance
    quasiCompact := haveI := S.isProper_contractionToBase hf; inferInstance
    regular := hf.isRegular S.regular
    genericFiberIso := S.contractedGenericFiberIso hf
    genericFiberIso_over_K := S.contractedGenericFiberIso_hom_snd hf
    modelProper := S.isProper_contractionToBase hf }

end RegularProperModelSituation

end Stacks.Models

end
