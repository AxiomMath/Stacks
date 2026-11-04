module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentFactorization
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentFactorization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Further results on `ComponentFactorization`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentFactorization` that need
imports beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace VanishingSituation

/-- **Stacks Project, Tag 0AX9.** A nonzero element of the maximal ideal which, along every
irreducible component of the special fibre, admits at some closed point of that component and of
no other a factorization one factor of which lies in the local maximal ideal and restricts to a
nonzero function on the component.

`hfib` is the standing exclusion of Section 54.7 (Situation 0AX8), transcribed. The section states
it in these words:

> If $X_s$ has dimension $0$, then $f$ is finite and hence an isomorphism. We will discard this
> uninteresting case.

So `hfib : 1 ≤ topologicalKrullDim V.specialFiber` is that sentence, and every later lemma of the
section is read under it. It appears as a binder here only because
`AlgebraicGeometry.VanishingSituation` transcribes Situation 0AX8 itself, which states the
situation without the section's subsequent exclusion.

Nothing else is carried. The source passes that exclusion from the fibre to each of its
components through the geometric connectedness of `X_s`, which it has from the Stein
factorization — More on Morphisms, Lemma 37.53.6, [Stacks, Tag 0AY8], whose second conclusion is
not available unconditionally in this library (see
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/SteinFactorization/NormalBase.lean`, where the
first conclusion `f_*𝒪_X = 𝒪_S` is tagged and the second is given only over [Stacks, Tag 0G7X]).
That input is not needed: a zero-dimensional component is a point lying on no other component,
hence open in the special fibre and so a quasi-finite point of `f`, and a modification of the
spectrum of a normal local domain with such a point in its closed fibre is an isomorphism
(`AlgebraicGeometry.IsModification.isIso_of_isOpen_singleton_fiber`), whence the special fibre is
a single point of dimension zero, which `hfib` forbids. So `hfib` alone gives the observation
following Situation 54.7.1, that every component has dimension one, as
`AlgebraicGeometry.VanishingSituation.topologicalKrullDim_component_eq_one`. -/
@[stacks 0AX9 "the lemma under the standing exclusion of Section 54.7 (Situation 0AX8): the case \
dim X_s = 0, discarded by the source, which notes there that f is then finite and hence an \
isomorphism. The geometric connectedness of the special fibre that the source reads off the \
Stein factorization is proved here where it is used: a zero-dimensional component is a point \
open in the special fibre, so Zariski's main theorem over the local base makes the modification \
an isomorphism and the special fibre a single point, which the exclusion rules out"]
theorem exists_ne_zero_mem_maximalIdeal_factorization_of_le_topologicalKrullDim_specialFiber
    (V : VanishingSituation.{u})
    (hfib : 1 ≤ topologicalKrullDim V.specialFiber) :
    ∃ a : V.A, a ≠ 0 ∧ a ∈ V.maximalIdeal ∧
      ∀ i : Fin V.numberOfComponents,
        ∃ y : componentScheme V i,
          IsClosed
              ({(Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι y} : Set V.X) ∧
          (Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι y ∈ componentInSource V i ∧
          (∀ j : Fin V.numberOfComponents, j ≠ i →
            (Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι y ∉ componentInSource V j) ∧
          ∃ g h : V.X.presheaf.stalk
              ((Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι y),
            g ∈ IsLocalRing.maximalIdeal _ ∧
            (Scheme.IdealSheafData.vanishingIdeal
                (componentClosed V i)).subschemeι.stalkMap y g ≠ 0 ∧
            ((StructureSheaf.toStalk V.A (V.f _) ≫ V.f.stalkMap _) a = g * h) := by
  classical
  have hnotfield : ¬ IsField V.A := by
    intro hfield
    have hdim0 : ringKrullDim V.A = 0 := ringKrullDim_eq_zero_of_isField hfield
    rw [V.dimension_two] at hdim0
    norm_num at hdim0
  obtain ⟨c, hc, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot fun hm =>
    hnotfield (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm)
  have hdata : ∀ i : Fin V.numberOfComponents,
      ∃ y : componentScheme V i,
        IsClosed ({(Scheme.IdealSheafData.vanishingIdeal
          (componentClosed V i)).subschemeι y} : Set V.X) ∧
        (Scheme.IdealSheafData.vanishingIdeal
          (componentClosed V i)).subschemeι y ∈ componentInSource V i ∧
        (∀ j : Fin V.numberOfComponents, j ≠ i →
          (Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι y ∉ componentInSource V j) ∧
        ∃ g : V.X.presheaf.stalk
            ((Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι y),
          g ∈ IsLocalRing.maximalIdeal _ ∧
          (Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι.stalkMap y g ≠ 0 := by
    intro i
    obtain ⟨y, hyclosed, hysource, hynot⟩ := exists_componentScheme_point V i
    obtain ⟨g, hgmax, hgne⟩ :=
      exists_nonzero_maximalIdeal_element_at_component_point V
        (V.topologicalKrullDim_component_eq_one hfib) i y hyclosed
    exact ⟨y, hyclosed, hysource, hynot, g, hgmax, hgne⟩
  choose y hyclosed hysource hynot g hgmax hgne using hdata
  have hfractions : ∀ i : Fin V.numberOfComponents,
      ∃ a b : V.A, a ≠ 0 ∧ b ≠ 0 ∧
        (StructureSheaf.toStalk V.A
          (V.f ((Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι (y i))) ≫
          V.f.stalkMap ((Scheme.IdealSheafData.vanishingIdeal
            (componentClosed V i)).subschemeι (y i))) a =
          g i * (StructureSheaf.toStalk V.A
            (V.f ((Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι (y i))) ≫
            V.f.stalkMap ((Scheme.IdealSheafData.vanishingIdeal
              (componentClosed V i)).subschemeι (y i))) b := by
    intro i
    exact exists_fraction_for_stalk_element V
      ((Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι (y i)) (g i) fun hg0 => hgne i (by simp [hg0])
  choose a₀ b₀ ha₀ hb₀ hfactor using hfractions
  let a := c * ∏ i : Fin V.numberOfComponents, a₀ i
  let ρ (i : Fin V.numberOfComponents) : V.A →+*
      V.X.presheaf.stalk
        ((Scheme.IdealSheafData.vanishingIdeal
          (componentClosed V i)).subschemeι (y i)) :=
    (StructureSheaf.toStalk V.A
      (V.f ((Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι (y i))) ≫
      V.f.stalkMap ((Scheme.IdealSheafData.vanishingIdeal
        (componentClosed V i)).subschemeι (y i))).hom
  let hi (i : Fin V.numberOfComponents) :=
    ρ i c * (ρ i (b₀ i) * ∏ j ∈ Finset.univ.erase i, ρ i (a₀ j))
  have hamem : a ∈ V.maximalIdeal := by
    dsimp [a]
    simpa [mul_comm] using
      (Ideal.mul_mem_left V.maximalIdeal (∏ i : Fin V.numberOfComponents, a₀ i) hc)
  refine ⟨a, mul_ne_zero hcne (Finset.prod_ne_zero_iff.mpr fun i _ => ha₀ i), hamem,
    fun i => ⟨y i, hyclosed i, hysource i, hynot i, g i, hi i, hgmax i, hgne i, ?_⟩⟩
  have hprod : ρ i (∏ j : Fin V.numberOfComponents, a₀ j) =
      ρ i (a₀ i) * ∏ j ∈ Finset.univ.erase i, ρ i (a₀ j) := by
    rw [map_prod]
    exact (Finset.mul_prod_erase Finset.univ (fun j => ρ i (a₀ j))
      (Finset.mem_univ i)).symm
  show ρ i a = g i * hi i
  calc
    ρ i a = ρ i c * ρ i (∏ j : Fin V.numberOfComponents, a₀ j) := by
      simp [a]
    _ = ρ i c * (ρ i (a₀ i) * ∏ j ∈ Finset.univ.erase i, ρ i (a₀ j)) := by
      rw [hprod]
    _ = g i * hi i := by
      rw [hfactor i]
      simp only [hi]
      ring

end VanishingSituation

end AlgebraicGeometry

end
