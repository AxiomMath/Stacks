module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreMorphismRestrict
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatCartierFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleBlowupGlue

/-!
# A divisor which is ample on a closed fibre is relatively ample near it

Let `f : Z ⟶ S` be a proper, flat morphism of schemes, locally of finite presentation, and let
`D ⊆ Z` be a closed subscheme, flat over `S` and of finite presentation over `Z`. Suppose that
at a point `s` of `S` the fibre `D_s ⊆ Z_s` is an effective Cartier divisor and that `𝒪_{Z_s}(D_s)`
is ample. Then over an open neighbourhood `U` of `s` the divisor `D` is an effective Cartier
divisor of `f⁻¹(U)` and `𝒪(D)` is ample relative to `f⁻¹(U) ⟶ U`.

This is the scheme-theoretic heart of the polarization step of the route to Stacks 0E6F and 0DQ0:
a lifted good divisor of a closed fibre of a family of curves, once the
family is a scheme, polarizes it near the fibre.

## Main results

* `AlgebraicGeometry.C1590Private.exists_iso_fromSpecResidueField`: a closed immersion from the
  spectrum of a field is the residue field of its image point, up to isomorphism.
* `AlgebraicGeometry.C1590Private.exists_iso_fiber_of_isPullback`: the base change of a morphism
  along a closed immersion from the spectrum of a field is the fibre at the image point.
* `AlgebraicGeometry.C1590Private.exists_isRelativelyAmple_divisorSheaf_near_fiber`: the statement
  above, with the fibre `Z_s` of Mathlib.
* `AlgebraicGeometry.C1590Private.exists_isRelativelyAmple_near_closedPoint`: the same, with the
  fibre presented by any cartesian square over a closed immersion from the spectrum of a field,
  and the conclusion read on every cartesian square over the open neighbourhood.

## The argument

At a point `x` of `D` over `s`, Stacks 062Y (2) makes `D` a relative effective Cartier divisor
on an affine open neighbourhood of `x`; off `D` the divisor is empty. The union `W` of the opens
on which `D` restricts to an effective Cartier divisor therefore contains the fibre `f⁻¹(s)`, and,
`f` being closed, `U = S ∖ f(Z ∖ W)` is an open neighbourhood of `s` with `f⁻¹(U) ⊆ W`. Over `U`
the divisor is effective Cartier, being so on an open cover (Stacks 01WS), and its invertible
sheaf restricts on the fibre to `𝒪_{Z_s}(D_s)` (Stacks 0C4U), which is ample. Stacks 0D2S
shrinks `U` to an open over which `𝒪(D)` is ample relative to `f`.

## References

* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.Divisors (IsEffectiveCartierDivisor divisorSheaf)

namespace AlgebraicGeometry.C1590Private

universe u

/-! ### Closed points as residue fields, and fibres -/

/-- **A closed immersion from the spectrum of a field is the residue field of its image point.**
It factors as `Spec K ⟶ Spec κ(s) ⟶ S` through the residue field of its image point `s`; the
first factor is a closed immersion, surjective onto the reduced scheme `Spec κ(s)`, hence an
isomorphism. -/
theorem exists_iso_fromSpecResidueField {S : Scheme.{u}} {K : Type u} [Field K]
    (pt : Spec (.of K) ⟶ S) [IsClosedImmersion pt] :
    ∃ e : Spec (.of K) ≅ Spec (S.residueField (pt (IsLocalRing.closedPoint K))),
      e.hom ≫ S.fromSpecResidueField _ = pt := by
  set s := pt (IsLocalRing.closedPoint K)
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S pt
  have hrange : Set.range pt = {s} := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨z, rfl⟩
      rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  have hcl : IsClosed ({s} : Set S) := hrange ▸ pt.isClosedEmbedding.isClosed_range
  have := isClosed_singleton_iff_isClosedImmersion.mp hcl
  have : IsClosedImmersion
      (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo pt)) ≫
        S.fromSpecResidueField s) := by
    rw [hfac]
    infer_instance
  have := IsClosedImmersion.of_comp_isClosedImmersion
    (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo pt))) (S.fromSpecResidueField s)
  have : Surjective (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo pt))) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective
    (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo pt)))
  exact ⟨asIso (Spec.map (S.descResidueField (Scheme.stalkClosedPointTo pt))), hfac⟩

/-- **The base change along a closed immersion from the spectrum of a field is the fibre.** A
cartesian square over `pt : Spec K ⟶ S` presents the fibre of `f` at the image point of `pt`. -/
theorem exists_iso_fiber_of_isPullback {Z S V : Scheme.{u}} (f : Z ⟶ S) {K : Type u} [Field K]
    (pt : Spec (.of K) ⟶ S) [IsClosedImmersion pt] {qV : V ⟶ Z} {v : V ⟶ Spec (.of K)}
    (hsq : IsPullback qV v f pt) :
    ∃ e : V ≅ f.fiber (pt (IsLocalRing.closedPoint K)), e.hom ≫ f.fiberι _ = qV := by
  obtain ⟨e, he⟩ := exists_iso_fromSpecResidueField pt
  have h₁ : IsPullback (f.fiberι (pt (IsLocalRing.closedPoint K)))
      (f.fiberToSpecResidueField _ ≫ e.inv) f pt :=
    (IsPullback.of_hasPullback f _).of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
      (by simp only [Iso.refl_hom, Iso.symm_hom]; rfl) (by simp)
      (by simp [← he])
  exact ⟨hsq.isoIsPullback _ _ h₁, hsq.isoIsPullback_hom_fst _ _ h₁⟩

/-! ### Ample divisors along isomorphisms -/

/-- **An ample effective Cartier divisor pulls back to one along an isomorphism.** -/
theorem isAmple_divisorSheaf_comap_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (E : Y.IdealSheafData) [hE : IsEffectiveCartierDivisor E]
    (hA : haveI := Stacks.Divisors.isInvertible_divisorSheaf E; IsAmple Y (divisorSheaf E)) :
    ∃ _ : IsEffectiveCartierDivisor (E.comap e),
      haveI := Stacks.Divisors.isInvertible_divisorSheaf (E.comap e)
      IsAmple X (divisorSheaf (E.comap e)) := by
  have hE' : IsEffectiveCartierDivisor (E.comap e) :=
    Stacks.Divisors.isPullbackDefined_of_flat e E hE
  have := Stacks.Divisors.isInvertible_divisorSheaf E
  have := Stacks.Divisors.isInvertible_divisorSheaf (E.comap e)
  refine ⟨hE', ?_⟩
  have : Stacks.Divisors.IsPullbackDefined e E := hE'
  exact (Stacks.RelativeVeryAmple.isAmple_congr (pullbackModule e (divisorSheaf E))
    (divisorSheaf (E.comap e)) (Stacks.Divisors.invertibleSheafPullbackIso e E)).mp
    (Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso e (divisorSheaf E) hA)

/-- Ampleness of the invertible sheaf of an effective Cartier divisor depends only on the
divisor. -/
theorem isAmple_divisorSheaf_of_eq {X : Scheme.{u}} {E E' : X.IdealSheafData} (h : E = E')
    [IsEffectiveCartierDivisor E] [IsEffectiveCartierDivisor E']
    (hA : haveI := Stacks.Divisors.isInvertible_divisorSheaf E; IsAmple X (divisorSheaf E)) :
    haveI := Stacks.Divisors.isInvertible_divisorSheaf E'; IsAmple X (divisorSheaf E') := by
  subst h
  exact hA

/-! ### The Cartier locus contains the fibre -/

/-- The empty closed subscheme of the complement of the support is an effective Cartier
divisor. -/
theorem isEffectiveCartierDivisor_comap_compl_support {Z : Scheme.{u}} (I : Z.IdealSheafData) :
    IsEffectiveCartierDivisor (I.comap (Scheme.Opens.ι (X := Z) I.support.compl)) := by
  refine (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal _).2 fun x hx => ?_
  rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
    Scheme.IdealSheafData.support_comap] at hx
  exact (x.2 hx).elim

/-- **Stacks 062Y (2), at the points of a fibre.** Every point of the fibre of `f` at `s` has an
open neighbourhood on which `D` restricts to an effective Cartier divisor. -/
theorem exists_isEffectiveCartierDivisor_comap_of_fiber {Z S : Scheme.{u}} (f : Z ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (I : Z.IdealSheafData)
    [LocallyOfFinitePresentation I.subschemeι] [Flat (I.subschemeι ≫ f)] (s : S)
    (hE : IsEffectiveCartierDivisor (I.comap (f.fiberι s))) (x : Z) (hx : f x = s) :
    ∃ V : Z.Opens, x ∈ V ∧ IsEffectiveCartierDivisor (I.comap V.ι) := by
  subst hx
  by_cases hxI : x ∈ I.support
  · have hfib : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧
        IsEffectiveCartierDivisor ((I.comap (f.fiberι (f x))).comap V.ι) :=
      ⟨⊤, trivial, Stacks.Divisors.isPullbackDefined_of_flat (⊤ : (f.fiber (f x)).Opens).ι _ hE⟩
    obtain ⟨V, hxV, -, hV⟩ :=
      Stacks.Divisors.exists_isRelativeEffectiveCartierDivisor_of_flat_of_finitePresentation f I x
        hxI hfib (Flat.stalkMap (I.subschemeι ≫ f) (⟨x, hxI⟩ : I.subscheme))
    exact ⟨V, hxV, hV.1⟩
  · exact ⟨I.support.compl, hxI, isEffectiveCartierDivisor_comap_compl_support I⟩

/-! ### The neighbourhood -/

section Neighbourhood

variable {Z S : Scheme.{u}} (f : Z ⟶ S) (I : Z.IdealSheafData)

/-- The union of the opens of `Z` on which `D` restricts to an effective Cartier divisor. -/
def cartierLocus : Z.Opens :=
  sSup {V : Z.Opens | IsEffectiveCartierDivisor (I.comap V.ι)}

/-- `D` restricts to an effective Cartier divisor over every open inside its Cartier locus. -/
theorem isEffectiveCartierDivisor_comap_of_le_cartierLocus (W : Z.Opens)
    (hW : W ≤ cartierLocus I) : IsEffectiveCartierDivisor (I.comap W.ι) := by
  let 𝒱 := {V : Z.Opens | IsEffectiveCartierDivisor (I.comap V.ι)}
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_comap (I.comap W.ι)
    (Y := fun V : 𝒱 => pullback W.ι V.1.ι) (fun V => pullback.fst W.ι V.1.ι) (fun x => ?_)
    fun V => ?_
  · obtain ⟨V, hV, hxV⟩ := (TopologicalSpace.Opens.mem_sSup (Us := 𝒱)).mp (hW x.2)
    refine ⟨⟨V, hV⟩, ?_⟩
    rwa [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  · rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
      Scheme.IdealSheafData.comap_comp]
    exact Stacks.Divisors.isPullbackDefined_of_flat _ _ V.2

variable [IsProper f]

/-- The open of the base above which `D` is effective Cartier: the complement of the image of
the complement of the Cartier locus, which is closed because `f` is proper. -/
def cartierBase : S.Opens :=
  ⟨(f.base '' ((cartierLocus I : Set Z)ᶜ))ᶜ,
    (f.isClosedMap _ (cartierLocus I).isOpen.isClosed_compl).isOpen_compl⟩

/-- The preimage under `f` of `cartierBase f I` is contained in `cartierLocus I`. -/
theorem preimage_cartierBase_le : f ⁻¹ᵁ cartierBase f I ≤ cartierLocus I := by
  intro z hz
  by_contra h
  exact hz ⟨z, h, rfl⟩

/-- If `f` is flat and locally of finite presentation, `D` is of finite presentation over `Z` and
flat over `S`, and the fibre of `D` at `s` is an effective Cartier divisor, then `s` lies in
`cartierBase f I`. -/
theorem mem_cartierBase [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation I.subschemeι] [Flat (I.subschemeι ≫ f)] (s : S)
    (hE : IsEffectiveCartierDivisor (I.comap (f.fiberι s))) : s ∈ cartierBase f I := by
  rintro ⟨z, hz, hzs⟩
  obtain ⟨V, hzV, hV⟩ := exists_isEffectiveCartierDivisor_comap_of_fiber f I s hE z hzs
  exact hz (TopologicalSpace.Opens.mem_sSup.mpr ⟨V, hV, hzV⟩)

end Neighbourhood

/-! ### The main statement -/

/-- **A divisor ample on a fibre is relatively ample near it** (Stacks 062Y, 0C4U and 0D2S). Let
`f : Z ⟶ S` be proper, flat and locally of finite presentation, and `D ⊆ Z` a closed subscheme
of finite presentation over `Z` and flat over `S`, whose fibre `D_s` at `s` is an effective
Cartier divisor of `Z_s` with `𝒪(D_s)` ample. Then there is an open `U ∋ s` of `S` over which `D`
is an effective Cartier divisor and its invertible sheaf is ample relative to `f⁻¹(U) ⟶ U`,
read on every cartesian square over `U`. -/
theorem exists_isRelativelyAmple_divisorSheaf_near_fiber {Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (I : Z.IdealSheafData)
    [LocallyOfFinitePresentation I.subschemeι] [Flat (I.subschemeι ≫ f)] (s : S)
    [hE : IsEffectiveCartierDivisor (I.comap (f.fiberι s))]
    (hA : haveI := Stacks.Divisors.isInvertible_divisorSheaf (I.comap (f.fiberι s))
      IsAmple (f.fiber s) (divisorSheaf (I.comap (f.fiberι s)))) :
    ∃ (T : Scheme.{u}) (j : T ⟶ S), IsOpenImmersion j ∧ s ∈ Set.range j ∧
      ∀ (Zt : Scheme.{u}) (p : Zt ⟶ Z) (g : Zt ⟶ T), IsPullback p g f j →
        ∃ (L : Zt.Modules) (_ : IsInvertibleModule Zt L),
          Stacks.RelativeAmple.IsRelativelyAmple g L := by
  set U := cartierBase f I
  have hsU : s ∈ U := mem_cartierBase f I s hE
  -- the divisor over `U`
  have hEU : IsEffectiveCartierDivisor (I.comap (f ⁻¹ᵁ U).ι) :=
    isEffectiveCartierDivisor_comap_of_le_cartierLocus I _ (preimage_cartierBase_le f I)
  have := Stacks.Divisors.isInvertible_divisorSheaf (I.comap (f ⁻¹ᵁ U).ι)
  set L := divisorSheaf (I.comap (f ⁻¹ᵁ U).ι)
  -- its restriction to the fibre
  set s' : U.toScheme := ⟨s, hsU⟩
  let k := Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso f U s hsU
  obtain ⟨hEk, hAk⟩ := isAmple_divisorSheaf_comap_of_isIso k.hom _ hA
  have hcomap : (I.comap (f ⁻¹ᵁ U).ι).comap ((f ∣_ U).fiberι s') =
      (I.comap (f.fiberι s)).comap k.hom := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Stacks.AmpleFibreNeighbourhood.fiberMorphismRestrictIso_hom_comp_fiberι f U s hsU]
  have hpd : IsEffectiveCartierDivisor
      ((I.comap (f ⁻¹ᵁ U).ι).comap ((f ∣_ U).fiberι s')) :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_eq hcomap
  have : Stacks.Divisors.IsPullbackDefined ((f ∣_ U).fiberι s') (I.comap (f ⁻¹ᵁ U).ι) := hpd
  have hAfib : IsAmple ((f ∣_ U).fiber s') (pullbackModule ((f ∣_ U).fiberι s') L) := by
    have := Stacks.Divisors.isInvertible_divisorSheaf
      ((I.comap (f ⁻¹ᵁ U).ι).comap ((f ∣_ U).fiberι s'))
    exact (Stacks.RelativeVeryAmple.isAmple_congr (pullbackModule ((f ∣_ U).fiberι s') L)
      (divisorSheaf ((I.comap (f ⁻¹ᵁ U).ι).comap ((f ∣_ U).fiberι s')))
      (Stacks.Divisors.invertibleSheafPullbackIso ((f ∣_ U).fiberι s')
        (I.comap (f ⁻¹ᵁ U).ι))).mpr (isAmple_divisorSheaf_of_eq hcomap.symm hAk)
  -- Stacks 0D2S
  obtain ⟨V, hsV, hrel⟩ :=
    Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre (f ∣_ U) L s' hAfib
  refine ⟨V.toScheme, V.ι ≫ U.ι, inferInstance, ⟨⟨s', hsV⟩, rfl⟩, fun Zt p g hsq => ?_⟩
  -- the chosen cartesian square over `V`
  have hcan : IsPullback (((f ∣_ U) ⁻¹ᵁ V).ι ≫ (f ⁻¹ᵁ U).ι) ((f ∣_ U) ∣_ V) f (V.ι ≫ U.ι) :=
    ((isPullback_morphismRestrict (f ∣_ U) V).paste_vert (isPullback_morphismRestrict f U)).flip
  have h := Stacks.AmpleBridge.isRelativelyAmple_comp_of_isIso
    (hsq.isoIsPullback _ _ hcan).hom ((f ∣_ U) ∣_ V) _ hrel
  rw [hsq.isoIsPullback_hom_snd _ _ hcan] at h
  exact ⟨_, inferInstance, h⟩

/-- **A divisor ample on a closed fibre is relatively ample near it**, with the fibre presented
by a cartesian square over a closed immersion `pt : Spec K ⟶ S` from the spectrum of a field:
`exists_isRelativelyAmple_divisorSheaf_near_fiber` read through
`exists_iso_fiber_of_isPullback`. -/
theorem exists_isRelativelyAmple_near_closedPoint {Z S V : Scheme.{u}} (f : Z ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] (I : Z.IdealSheafData)
    [LocallyOfFinitePresentation I.subschemeι] [Flat (I.subschemeι ≫ f)] {K : Type u} [Field K]
    (pt : Spec (.of K) ⟶ S) [IsClosedImmersion pt] (qV : V ⟶ Z) (v : V ⟶ Spec (.of K))
    (hsq : IsPullback qV v f pt) [hE : IsEffectiveCartierDivisor (I.comap qV)]
    (hA : haveI := Stacks.Divisors.isInvertible_divisorSheaf (I.comap qV)
      IsAmple V (divisorSheaf (I.comap qV))) :
    ∃ (T : Scheme.{u}) (j : T ⟶ S), IsOpenImmersion j ∧
      pt (IsLocalRing.closedPoint K) ∈ Set.range j ∧
      ∀ (Zt : Scheme.{u}) (p : Zt ⟶ Z) (g : Zt ⟶ T), IsPullback p g f j →
        ∃ (L : Zt.Modules) (_ : IsInvertibleModule Zt L),
          Stacks.RelativeAmple.IsRelativelyAmple g L := by
  obtain ⟨e, he⟩ := exists_iso_fiber_of_isPullback f pt hsq
  have hc : (I.comap qV).comap e.inv = I.comap (f.fiberι (pt (IsLocalRing.closedPoint K))) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← he, Iso.inv_hom_id_assoc]
  obtain ⟨hE', hA'⟩ := isAmple_divisorSheaf_comap_of_isIso e.inv _ hA
  have : IsEffectiveCartierDivisor (I.comap (f.fiberι (pt (IsLocalRing.closedPoint K)))) :=
    Stacks.Divisors.isEffectiveCartierDivisor_of_eq hc.symm
  exact exists_isRelativelyAmple_divisorSheaf_near_fiber f I _ (isAmple_divisorSheaf_of_eq hc hA')

end AlgebraicGeometry.C1590Private

end
