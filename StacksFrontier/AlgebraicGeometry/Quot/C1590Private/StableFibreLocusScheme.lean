module

public import StacksFrontier.AlgebraicGeometry.AmpleFibreLimit.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegree
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableCurveOverAmple

/-!
# The stable fibre locus of a proper morphism of schemes is open (towards Stacks 0E76)

Let `q : Z ⟶ U` be a proper morphism of schemes whose fibres are proper nodal curves of dimension
one with `H⁰ = κ(u)`, and let `ω` be an invertible `𝒪_Z`-module restricting on every fibre `Z_u`
to its dualizing sheaf `ω_{Z_u}`. Then the points `u` with `Z_u` a stable curve form an open
subset of `U`. This is the scheme case of the proof of Stacks 0E76 from Stacks 0E74: the fibre
`Z_u` is stable exactly when `ω_{Z_u}` is ample
(`AlgebraicGeometry.C1590Private.isStableCurveOver_iff_isAmple`), and by Stacks 0D2S an
invertible module ample on one fibre of a proper morphism is relatively ample over an open
neighbourhood of that point, hence ample on the nearby fibres (Stacks 0893, 01VK). For the
relative dualizing sheaf of a family of curves this replaces Stacks 0D3D, which the source uses
for algebraic spaces: étale locally on the base a family of curves is a scheme (Stacks 0E6F).

## Main results

* `AlgebraicGeometry.C1590Private.exists_isOpen_isStableCurveOver_fiber`.

## Implementation notes

An unregistered helper. Unconditional: the module `ω` and the comparison of its
restrictions with the dualizing sheaves of the fibres are data of the statement.

## References

* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E74](https://stacks.math.columbia.edu/tag/0E74)
* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

open Stacks.AmpleLocallyClosed (pullbackModule) in
/-- An invertible module relatively ample over an open neighbourhood `V` of `y` is ample on the
fibre over `y`. -/
theorem isAmple_pullbackModule_fiberι_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {V : S.Opens}
    {y : S} (hy : y ∈ V)
    [Stacks.Ample.IsInvertibleModule (f.fiber y) (pullbackModule (f.fiberι y) L)]
    (hV : Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L)) :
    Stacks.Ample.IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L) := by
  -- the fibre over `y` is a base change of `f ∣_ V`
  have hrange : Set.range (S.fromSpecResidueField y) ⊆ Set.range V.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.2 hy
  let g : Spec (S.residueField y) ⟶ V :=
    IsOpenImmersion.lift V.ι (S.fromSpecResidueField y) hrange
  have hg : g ≫ V.ι = S.fromSpecResidueField y := IsOpenImmersion.lift_fac _ _ _
  have ht : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι := (isPullback_morphismRestrict f V).flip
  let l : f.fiber y ⟶ f ⁻¹ᵁ V := ht.lift (f.fiberι y) (f.fiberToSpecResidueField y ≫ g)
    (by rw [Category.assoc, hg]; exact (IsPullback.of_hasPullback f _).w)
  have hl : l ≫ (f ⁻¹ᵁ V).ι = f.fiberι y := ht.lift_fst _ _ _
  have hsq : IsPullback l (f.fiberToSpecResidueField y) (f ∣_ V) g := by
    refine IsPullback.of_right ?_ (ht.lift_snd _ _ _) ht
    rw [hl, hg]
    exact IsPullback.of_hasPullback f _
  -- Stacks 0893 along `Spec κ(y) ⟶ V`, then Stacks 01VK over the field
  have hrel' : Stacks.RelativeAmple.IsRelativelyAmple (f.fiberToSpecResidueField y)
      (pullbackModule (f.fiberι y) L) :=
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
      ((Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso l (f ⁻¹ᵁ V).ι L).symm ≪≫
        Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hl L)).mp
      (Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsq _ hV)
  rw [Stacks.AmpleBridge.isAmple_iff_isAmple]
  exact (Scheme.Modules.isRelativelyAmple_iff_isAmple _ _).mp hrel'

open Stacks.AmpleLocallyClosed (pullbackModule) in
/-- **The stable fibre locus of a proper morphism of schemes is open.** Let `q : Z ⟶ U` be
proper, with every fibre `Z_u` of dimension one, `H⁰(Z_u, 𝒪) = κ(u)` and at-worst-nodal
singularities, and let `ω` be invertible on `Z` with `ω|_{Z_u} ≅ ω_{Z_u}` for every `u`. If the
fibre over `u₀` is a stable curve, so is the fibre over every point of an open neighbourhood of
`u₀`. -/
theorem exists_isOpen_isStableCurveOver_fiber {Z U : Scheme.{u}} (q : Z ⟶ U) [IsProper q]
    (ω : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 ω]
    (hω : ∀ u : U, Nonempty ((Scheme.Modules.pullback (q.fiberι u)).obj ω ≅
      Stacks.Duality.dualizingSheafOverField (k := U.residueField u) (q.fiberToSpecResidueField u)))
    (hfib : ∀ u : U, topologicalKrullDim (q.fiber u) = 1 ∧
      IsIso ((Scheme.ΓSpecIso (U.residueField u)).inv ≫ (q.fiberToSpecResidueField u).appTop) ∧
      (letI : (q.fiber u).Over (Spec (U.residueField u)) := ⟨q.fiberToSpecResidueField u⟩;
        Stacks.Curves.HasAtWorstNodalSingularities (U.residueField u) (q.fiber u)))
    (u₀ : U) (h₀ : IsStableCurveOver (U.residueField u₀) (q.fiberToSpecResidueField u₀)) :
    ∃ N : U.Opens, u₀ ∈ N ∧
      ∀ u ∈ N, IsStableCurveOver (U.residueField u) (q.fiberToSpecResidueField u) := by
  -- the restriction of `ω` to a fibre, in the two spellings of the pullback
  have hres : ∀ u : U, ∃ _ : Stacks.Ample.IsInvertibleModule (q.fiber u)
      (pullbackModule (q.fiberι u) ω),
      (Stacks.Ample.IsAmple (q.fiber u) (pullbackModule (q.fiberι u) ω) ↔
        IsStableCurveOver (U.residueField u) (q.fiberToSpecResidueField u)) := by
    intro u
    obtain ⟨hdim, hH0, hnodal⟩ := hfib u
    obtain ⟨e⟩ := hω u
    let e' : pullbackModule (q.fiberι u) ω ≅
        Stacks.Duality.dualizingSheafOverField (k := U.residueField u)
          (q.fiberToSpecResidueField u) :=
      ((Stacks.ProjectiveBundleQuotients.pullbackIso (q.fiberι u)).app ω).symm ≪≫ e
    have : SheafOfModules.IsInvertible (q.fiber u).presheaf (q.fiber u).ringCatSheaf.2
        ((Scheme.Modules.pullback (q.fiberι u)).obj ω) :=
      Stacks.Modules.isInvertible_pullback _ _
    have hinv : SheafOfModules.IsInvertible (q.fiber u).presheaf (q.fiber u).ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (k := U.residueField u)
          (q.fiberToSpecResidueField u)) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
    have hinv' : Stacks.Ample.IsInvertibleModule (q.fiber u) (pullbackModule (q.fiberι u) ω) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e'.symm
    have := hH0
    refine ⟨hinv', ?_⟩
    rw [isStableCurveOver_iff_isAmple _ _ hdim hnodal, Stacks.AmpleBridge.isAmple_iff_isAmple]
    exact ⟨fun h => ⟨hinv, Scheme.Modules.isAmple_of_iso e' h⟩,
      fun ⟨_, h⟩ => Scheme.Modules.isAmple_of_iso e'.symm h⟩
  obtain ⟨hinv₀, hamp₀⟩ := hres u₀
  have := hinv₀
  -- Stacks 0D2S
  obtain ⟨V, hu₀, hV⟩ := Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre q ω u₀
    (hamp₀.2 h₀)
  refine ⟨V, hu₀, fun u hu => ?_⟩
  obtain ⟨hinv, hamp⟩ := hres u
  have := hinv
  exact hamp.1 (isAmple_pullbackModule_fiberι_of_isRelativelyAmple q ω hu hV)

end AlgebraicGeometry.C1590Private

end
