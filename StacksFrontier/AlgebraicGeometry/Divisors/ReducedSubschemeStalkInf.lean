module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# The ideal sheaf of a reduced closed subscheme as a finite infimum of stalk ideals

Let `I` be an ideal sheaf on a scheme `X` whose closed subscheme `I.subscheme` is reduced, and
let `g : Y ⟶ I.subscheme` be a surjective morphism.  Then `I` is recovered as the kernel of the
composite `g ≫ I.subschemeι`, and if `Y` is covered by finitely many open immersions `ε j`, the
ideal that `I` induces in each local ring of `X` is the infimum of the ideals induced by the
kernels of the morphisms `ε j ≫ g ≫ I.subschemeι`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.eq_ker_comp_subschemeι_of_surjective`: a reduced closed
  subscheme is cut out by the kernel of any surjection onto it.
* `AlgebraicGeometry.Scheme.Hom.ker_eq_iInf_of_opensRange_cover`: the kernel of a morphism is the
  infimum of the kernels of its restrictions to the members of an open cover of the source.
* `AlgebraicGeometry.IdealSheafData.stalk_iInf_fin`: the ideal induced in a local ring by a finite
  infimum of ideal sheaves is the infimum of the induced ideals.
* `AlgebraicGeometry.Scheme.IdealSheafData.stalk_eq_iInf_of_finite_cover`: the combination of the
  three statements above.

## Implementation notes

For the first statement the inequality `I ≤ (g ≫ I.subschemeι).ker` is formal, from
`AlgebraicGeometry.Scheme.Hom.le_ker_comp` and
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`.  The reverse inequality uses that a
reduced closed subscheme is determined by its support: `I` is the vanishing ideal of `I.support`,
and the support of the kernel contains the range of `g ≫ I.subschemeι`, which is the range of
`I.subschemeι` because `g` is surjective.

The second statement is proved sectionwise.  A section of `𝒪_Y` whose restriction along each
`ε i` vanishes has vanishing germ at every point, because the stalk maps of an open immersion are
isomorphisms, hence the section is zero.

The stalk computation reduces, on an affine open neighbourhood of the point, to the statement that
localization commutes with finite infima of ideals, `IsLocalization.map_inf`.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Localization commutes with the infimum of a finite family of ideals indexed by a `Finset`. -/
private theorem Ideal.map_finsetInf_algebraMap_of_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) [Algebra R S]
    [IsLocalization M S] {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    (s.inf I).map (algebraMap R S) = s.inf fun i ↦ (I i).map (algebraMap R S) := by
  classical
  refine Finset.induction_on s (by simp [_root_.Ideal.map_top]) ?_
  intro a s _ ih
  rw [Finset.inf_insert, Finset.inf_insert, IsLocalization.map_inf M S, ih]

/-- Localization commutes with the infimum of a family of ideals indexed by `Fin m`. -/
private theorem Ideal.map_iInf_fin_algebraMap_of_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) [Algebra R S]
    [IsLocalization M S] {m : ℕ} (I : Fin m → Ideal R) :
    (⨅ j, I j).map (algebraMap R S) = ⨅ j, (I j).map (algebraMap R S) := by
  rw [← Finset.inf_univ_eq_iInf I,
    ← Finset.inf_univ_eq_iInf fun j ↦ (I j).map (algebraMap R S),
    Ideal.map_finsetInf_algebraMap_of_isLocalization M]

/-- **A reduced closed subscheme is cut out by the kernel of any surjection onto it.**

If the closed subscheme attached to an ideal sheaf `I` is reduced and `g` is a surjective
morphism onto it, then the kernel of `g ≫ I.subschemeι` is `I` itself. -/
theorem Scheme.IdealSheafData.eq_ker_comp_subschemeι_of_surjective
    {X Y : Scheme.{u}} (I : X.IdealSheafData) [IsReduced I.subscheme]
    (g : Y ⟶ I.subscheme) [Surjective g] :
    (g ≫ I.subschemeι).ker = I := by
  have hge : I ≤ (g ≫ I.subschemeι).ker :=
    (Scheme.IdealSheafData.ker_subschemeι I).ge.trans (Scheme.Hom.le_ker_comp g I.subschemeι)
  have hIv : I = Scheme.IdealSheafData.vanishingIdeal I.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme I I.support rfl
  refine le_antisymm (le_trans ?_ hIv.ge) hge
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  have hrange : Set.range (g ≫ I.subschemeι).base = (I.support : Set X) := by
    rw [AlgebraicGeometry.range_eq_range_of_surjective (g ≫ I.subschemeι) I.subschemeι g rfl]
    exact Scheme.IdealSheafData.range_subschemeι I
  exact fun z hz ↦ Scheme.Hom.range_subset_ker_support (g ≫ I.subschemeι) (hrange ▸ hz)

/-- **The kernel of a morphism is the infimum of the kernels of its restrictions to an open
cover.**

If the open immersions `ε i` cover `Y`, then the kernel of `g : Y ⟶ X` is the infimum of the
kernels of the composites `ε i ≫ g`. -/
theorem Scheme.Hom.ker_eq_iInf_of_opensRange_cover
    {X Y : Scheme.{u}} (g : Y ⟶ X) {ι : Type*} {A : ι → Scheme.{u}}
    (ε : ∀ i, A i ⟶ Y) [∀ i, IsOpenImmersion (ε i)]
    (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (ε i).base) :
    g.ker = ⨅ i, (ε i ≫ g).ker := by
  refine le_antisymm (le_iInf fun i ↦ Scheme.Hom.le_ker_comp (ε i) g) ?_
  have hker : g.ker = Scheme.IdealSheafData.ofIdeals fun U ↦ RingHom.ker (g.app U).hom := rfl
  rw [hker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  rw [RingHom.mem_ker]
  have hres : ∀ i, ((ε i).app (g ⁻¹ᵁ (U : X.Opens))).hom ((g.app U).hom s) = 0 := fun i ↦
    Scheme.Hom.ideal_ker_le (ε i ≫ g) U (Scheme.IdealSheafData.ideal_mono (iInf_le _ i) U hs)
  refine TopCat.Presheaf.section_ext Y.sheaf (g ⁻¹ᵁ (U : X.Opens)) _ 0 ?_
  intro y hy
  obtain ⟨i, a, ha⟩ := hcover y
  subst ha
  show Y.presheaf.germ (g ⁻¹ᵁ (U : X.Opens)) _ hy ((g.app U).hom s) =
    Y.presheaf.germ (g ⁻¹ᵁ (U : X.Opens)) _ hy 0
  have hinj : Function.Injective ((ε i).stalkMap a) :=
    (ConcreteCategory.bijective_of_isIso ((ε i).stalkMap a)).1
  apply hinj
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]
  simpa using congrArg ((A i).presheaf.germ ((ε i) ⁻¹ᵁ (g ⁻¹ᵁ (U : X.Opens))) a hy) (hres i)

/-- **The ideal induced in a local ring by a finite infimum of ideal sheaves is the infimum of
the induced ideals.** -/
theorem IdealSheafData.stalk_iInf_fin
    {X : Scheme.{u}} [IsLocallyNoetherian X] {m : ℕ} (F : Fin m → X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (⨅ j, F j) x = ⨅ j, IdealSheafData.stalk (F j) x := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  simp_rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU]
  rw [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  exact @Ideal.map_iInf_fin_algebraMap_of_isLocalization _ _ _ _
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.algebra_section_stalk ⟨x, hxU⟩)
    (hU.isLocalization_stalk ⟨x, hxU⟩) m _

/-- **The ideal induced by a reduced closed subscheme in a local ring is a finite infimum.**

If `I.subscheme` is reduced, `g : Y ⟶ I.subscheme` is surjective and `Y` is covered by finitely
many open immersions `ε j`, then the ideal `I` induces at a point `x` of `X` is the infimum of
the ideals induced there by the kernels of the morphisms `ε j ≫ g ≫ I.subschemeι`. -/
theorem Scheme.IdealSheafData.stalk_eq_iInf_of_finite_cover
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) [IsReduced I.subscheme]
    (g : Y ⟶ I.subscheme) [Surjective g] {m : ℕ} {A : Fin m → Scheme.{u}}
    (ε : ∀ j, A j ⟶ Y) [∀ j, IsOpenImmersion (ε j)]
    (hcover : ∀ y : Y, ∃ j, y ∈ Set.range (ε j).base) (x : X) :
    AlgebraicGeometry.IdealSheafData.stalk I x
      = ⨅ j, AlgebraicGeometry.IdealSheafData.stalk ((ε j ≫ g ≫ I.subschemeι).ker) x :=
  (congrArg (AlgebraicGeometry.IdealSheafData.stalk · x)
      ((Scheme.IdealSheafData.eq_ker_comp_subschemeι_of_surjective I g).symm.trans
        (Scheme.Hom.ker_eq_iInf_of_opensRange_cover (g ≫ I.subschemeι) ε hcover))).trans
    (IdealSheafData.stalk_iInf_fin _ x)

end AlgebraicGeometry

end
