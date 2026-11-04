module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort

/-!
# A resolution of a normal surface with one singular point, centred at that point

Let `V` be a normal Noetherian scheme whose only singular point is the closed point `v`, and
assume that the spectrum of the local ring `𝒪_{V,v}` has a resolution of singularities by
normalized blowups (Stacks 0BGL). Then `V` has a resolution by a finite sequence of proper
normalized blowups all of whose centres lie over `v`: the local sequence over `Spec 𝒪_{V,v}` is
spread out over `V`, and the result is regular because regularity is checked on the flat cover
of `V` by `V ∖ {v}` and `Spec 𝒪_{V,v}`.

Unlike the conclusion of Stacks 0BGL, which allows a centre anywhere, the sequence produced here
is centred over `v`. That is what makes it an object of the category `𝒞_{V, v}` of Stacks 0BHA,
over which it can be transported from an elementary étale neighbourhood of a singular point of
an algebraic space to the whole space (Stacks 0BHL).

## Main results

* `AlgebraicGeometry.exists_reflTransGen_isProperNormalizedBlowUpOutside_of_singularLocus`: the
  statement above.

## References

* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A resolution by proper normalized blowups centred over the only singular point.** If `V`
is a normal Noetherian scheme whose singular locus is the closed point `v` and the spectrum of
`𝒪_{V,v}` has a resolution by normalized blowups, then there is a sequence of proper normalized
blowups of `V` at closed points lying over `v`, ending in a regular scheme proper over `V`. -/
theorem exists_reflTransGen_isProperNormalizedBlowUpOutside_of_singularLocus (V : Scheme.{u})
    [IsNoetherian V] [IsNormal V] (v : V) (hv : IsClosed ({v} : Set V))
    (hsing : singularLocus V = {v})
    (hres : HasResolutionByNormalizedBlowUps (Spec (.of (V.presheaf.stalk v)))) :
    ∃ (U : V.Opens) (Z : Over V), (∀ y, y ∉ U → y = v) ∧
      Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U) (Over.mk (𝟙 V)) Z ∧
        AlgebraicGeometry.IsProper Z.hom ∧ IsRegular Z.left := by
  classical
  let Dsit : FinitePresentationAwayPointsSituation.{u} :=
    { S := V
      n := 1
      points := fun _ => v
      points_injective := fun i j _ => Subsingleton.elim i j
      points_closed := fun _ => hv
      complement_quasiCompact := inferInstance }
  let : IsLocallyNoetherian Dsit.S := by show IsLocallyNoetherian V; infer_instance
  let : IsNormal Dsit.S := by show IsNormal V; infer_instance
  have hcomponents : ∀ W : Dsit.S.Opens, IsCompact (W : Set Dsit.S) →
      (irreducibleComponents W).Finite := finite_irreducibleComponents_of_isCompact Dsit.S
  have hcompl : ∀ y : V, y ∉ (Dsit.complement : Set V) → y = v := by
    intro y hy
    change ¬ y ∉ Set.range (fun _ : Fin 1 => v) at hy
    obtain ⟨_, h⟩ := not_not.mp hy
    exact h.symm
  have hnoeth : ∀ i, IsLocallyNoetherian (Dsit.localScheme i) := fun i => by
    show IsLocallyNoetherian (Spec (.of (Dsit.S.presheaf.stalk (Dsit.points i))))
    exact isLocallyNoetherian_Spec.mpr inferInstance
  have hlocal : ∀ i : Fin Dsit.n, ∃ Z : Over (Dsit.localScheme i),
      Relation.ReflTransGen (IsProperNormalizedBlowUpOutside (Dsit.puncturedLocalScheme i))
        (Over.mk (𝟙 (Dsit.localScheme i))) Z ∧ AlgebraicGeometry.IsProper Z.hom ∧
          IsRegular Z.left := by
    intro i
    let : Flat (Dsit.S.fromSpecStalk (Dsit.points i)) := flat_fromSpecStalk Dsit.S (Dsit.points i)
    let : IsNormal (Dsit.localScheme i) :=
      isNormal_of_flat_preimmersion (Dsit.S.fromSpecStalk (Dsit.points i))
    have := hnoeth i
    refine exists_reflTransGen_of_hasResolutionByNormalizedBlowUps _ (fun z hz hzU => ?_) hres
    exact hzU (Set.mem_singleton_iff.mpr (eq_closedPoint_of_isClosed_singleton _ z hz))
  choose Z hZ hZproper hZreg using hlocal
  obtain ⟨A, hA, hAproper, hAlocal, ⟨eAU⟩⟩ :=
    Dsit.exists_properNormalizedBlowUpSequence_of_local hcomponents Z hZ
  let : AlgebraicGeometry.IsProper A.hom := hAproper
  let : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hregU : IsRegular ((Over.pullback Dsit.complement.ι).obj A).left := by
    let : IsLocallyNoetherian ((Over.pullback Dsit.complement.ι).obj A).left :=
      isLocallyNoetherian_of_isOpenImmersion
        (Limits.pullback.fst A.hom Dsit.complement.ι)
    let : IsLocallyNoetherian Dsit.complement.toScheme :=
      isLocallyNoetherian_of_isOpenImmersion Dsit.complement.ι
    have hiff : IsRegular Dsit.complement.toScheme ↔
        IsLocallyNoetherian Dsit.complement.toScheme ∧
          ∀ x : Dsit.complement.toScheme,
            IsRegularLocalRing (Dsit.complement.toScheme.presheaf.stalk x) := by
      simpa using (isRegular_tfae Dsit.complement.toScheme).out 1 2 (by simp) (by simp)
    have hreg : IsRegular Dsit.complement.toScheme := by
      refine hiff.mpr ⟨inferInstance, fun x => ?_⟩
      have hx : Dsit.complement.ι x ∉ singularLocus V := by
        rw [hsing]
        intro h
        exact x.2 ⟨0, (Set.mem_singleton_iff.mp h).symm⟩
      let : IsRegularLocalRing (Dsit.S.presheaf.stalk (Dsit.complement.ι x)) := not_not.mp hx
      exact IsRegularLocalRing.of_ringEquiv
        (asIso (Dsit.complement.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact isRegular_of_iso ((Over.forget _).mapIso eAU) hreg
  have hregLocal : ∀ i, IsRegular
      ((Over.pullback (Dsit.S.fromSpecStalk (Dsit.points i))).obj A).left := by
    intro i
    let : AlgebraicGeometry.IsProper
        ((Over.pullback (Dsit.S.fromSpecStalk (Dsit.points i))).obj A).hom := by
      show AlgebraicGeometry.IsProper
        (Limits.pullback.snd A.hom (Dsit.S.fromSpecStalk (Dsit.points i)))
      infer_instance
    have := hnoeth i
    let : IsLocallyNoetherian
        ((Over.pullback (Dsit.S.fromSpecStalk (Dsit.points i))).obj A).left :=
      LocallyOfFiniteType.isLocallyNoetherian
        ((Over.pullback (Dsit.S.fromSpecStalk (Dsit.points i))).obj A).hom
    exact isRegular_of_iso ((Over.forget _).mapIso (hAlocal i).some) (hZreg i)
  exact ⟨Dsit.complement, A, hcompl, hA, hAproper,
    Dsit.isRegular_of_localizations A hregU hregLocal⟩

end AlgebraicGeometry
