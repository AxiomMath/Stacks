module

public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Components
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Finite
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTensorPower.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affineness of the nonvanishing locus of a glued section

The fourth step of the proof of [Stacks, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
observes that `X_s` is set-theoretically the union of the affine closed subschemes `(Z_i)_{s_i}`
and concludes that it is affine by [Tag 09NL](https://stacks.math.columbia.edu/tag/09NL).  This
file supplies both halves.

The identification of `(Z_i)_{s_i}` with the preimage of `X_s` is
`preimage_nonvanishingOpen_eq_of_iso`: for a closed immersion `f` and an isomorphism
`f^* M ≅ N` carrying the pulled-back section to a given one, the preimage of the nonvanishing
locus of the section of `M` is the nonvanishing locus of the section of `N`.  That is exactly the
data the glueing step of Tag 09NE delivers, and with it the affineness is the reduced case of
Tag 09NL, proved as `Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion`.

## Main results

* `Stacks.AmpleReducedDimensionOne.sections_eq_of_eval_top`: a global section of a sheaf of
  modules is determined by its value over `⊤`.
* `Stacks.AmpleReducedDimensionOne.preimage_nonvanishingOpen_eq_of_iso`: the nonvanishing locus
  pulls back to the nonvanishing locus of the transported section.
* `Stacks.AmpleReducedDimensionOne.isAffineOpen_of_isAffineOpen_preimage`: **an open subset of a
  reduced scheme covered by finitely many closed subschemes in which its preimage is affine is
  affine.**
* `Stacks.AmpleReducedDimensionOne.isAffineOpen_of_isAffineOpen_preimage_of_subset_range`: the
  one-piece case.
* `Stacks.AmpleReducedDimensionOne.isAffineOpen_of_isAffineOpen_preimage_components`: the case of
  the irreducible components, which is the step the proof of Tag 09NX takes.

## Implementation notes

**The one-piece case is used twice, and the second use is a gap in the source's prose.**  The last
step of the proof of Tag 09NX concludes "`X_t` is affine" from "`(Z_1)_t` is affine" with no
argument.  The reason it is legitimate is that the open in question is contained in `Z_1`, so the
one-piece case of the same lemma applies — the cover consists of the single closed immersion
`Z_1 ⟶ X`.  It is the same lemma as the four-sentences-earlier appeal to Tag 09NL, a reuse the
source does not signpost, and `isAffineOpen_of_isAffineOpen_preimage_of_subset_range` is it.

**Why the preimage identification needs the declared intermediate type.**  The pulled-back section
is `Stacks.SheafOfModules.modulePullbackSection`, whose value over `⊤` is stated in terms of
`Stacks.RingedSpace.pullbackUnit`, while Tag 09NE states its compatibility in terms of the unit of
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`.  The two are the same term, but
`rw` with `modulePullbackSection_eval_top` fails across the `X.Modules` spelling of the module;
binding the equation locally *with its type written out* goes through.

## References

* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Topology.Irreducible
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AmpleReducedDimensionOne

/-! ### Global sections are determined over `⊤` -/

/-- **A global section of a sheaf of modules is determined by its value over `⊤`.**  Every other
value is the restriction of that one, so `Stacks.SheafOfModules.sectionsOfTop` is a retraction. -/
theorem sections_eq_of_eval_top {Y : RingedSpace.{u, u}}
    {A : _root_.SheafOfModules.{u} (structureSheafRing Y)} {u v : A.sections}
    (h : u.eval (op ⊤) = v.eval (op ⊤)) : u = v := by
  rw [← sectionsOfTop_eval_top_self A u, ← sectionsOfTop_eval_top_self A v, h]

/-! ### The preimage of a nonvanishing locus -/

variable {X : Scheme.{u}}

/-- **The preimage of `X_t` under a morphism is the nonvanishing locus of the transported
section.**  The hypothesis is the conclusion of the glueing step of Tag 09NE: an isomorphism
`f^* M ≅ N` taking the image of `t` under the unit of `f^* ⊣ f_*` to `v`, over `⊤`.

Tag 0H78 identifies the preimage with the nonvanishing locus of the pulled-back section, and the
isomorphism moves that to `v` because a nonvanishing locus depends on a section only through its
value over `⊤`. -/
theorem preimage_nonvanishingOpen_eq_of_iso
    {Z : Scheme.{u}} (f : Z ⟶ X) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    (t : M.sections) (N : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 N]
    (v : N.sections)
    (e : (modulePullback f.toLRSHom.toShHom).obj M ≅ N)
    (hev : e.hom.val.app (op ⊤)
        (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app M).val.app (op ⊤)
          (t.eval (op ⊤))) = v.eval (op ⊤)) :
    f ⁻¹ᵁ nonvanishingOpen (X := X.toRingedSpace) M t
      = nonvanishingOpen (X := Z.toRingedSpace) N v := by
  have hMs : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr ‹_›
  have hpull : Stacks.SheafOfModules.IsInvertible Z.presheaf
      (structureSheafRing Z.toRingedSpace).property
      ((modulePullback f.toLRSHom.toShHom).obj M) :=
    @Stacks.RingedSpace.isInvertible_modulePullback Z.toRingedSpace X.toRingedSpace
      f.toLRSHom.toShHom M hMs
  have h1 : (modulePullbackSection f.toLRSHom M t).eval (op ⊤) =
      ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app M).val.app (op ⊤)
        (t.eval (op ⊤)) :=
    modulePullbackSection_eval_top f.toLRSHom M t
  have hsec : _root_.SheafOfModules.sectionsMap e.hom
      (modulePullbackSection f.toLRSHom M t) = v :=
    sections_eq_of_eval_top (by
      rw [show (_root_.SheafOfModules.sectionsMap e.hom
            (modulePullbackSection f.toLRSHom M t)).eval (op ⊤)
          = e.hom.val.app (op ⊤)
            ((modulePullbackSection f.toLRSHom M t).eval (op ⊤)) from rfl, h1]
      exact hev)
  rw [Stacks.SheafOfModules.preimage_nonvanishingOpen f M t, ← hsec]
  exact (nonvanishingOpen_sectionsMap (X := Z.toRingedSpace) e _).symm

/-! ### Affineness from a closed cover of the open -/

/-- **An open subset of a reduced scheme is affine once finitely many closed subschemes cover it
and its preimage in each of them is affine.**  This is the reduced case of Tag 09NL applied inside
the open subscheme: the preimages are closed subschemes of it by restriction, they are affine by
hypothesis, they cover it, and it is reduced because the ambient scheme is. -/
theorem isAffineOpen_of_isAffineOpen_preimage [AlgebraicGeometry.IsReduced X]
    {ι : Type*} [Finite ι] {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (f i)] (U : X.Opens)
    (hcov : (U : Set X) ⊆ ⋃ i, Set.range (f i).base)
    (haff : ∀ i, IsAffineOpen (f i ⁻¹ᵁ U)) : IsAffineOpen U := by
  have haff' : ∀ i, IsAffine (f i ⁻¹ᵁ U).toScheme := haff
  refine Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion
    (X := U.toScheme) (fun i => f i ∣_ U) ?_
  refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ?_
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp (hcov y.2)
  refine ⟨i, ⟨z, ?_⟩, Subtype.ext ?_⟩
  · change (f i) z ∈ U
    rw [hz]; exact y.2
  · exact (morphismRestrict_base_coe (f i) U _).trans hz

/-- **The one-piece case: an open contained in the range of a single closed immersion is affine
once its preimage there is.**  This is the step the last paragraph of the proof of Tag 09NX takes
without comment when it concludes that `X_t` is affine from the affineness of `(Z_1)_t`. -/
theorem isAffineOpen_of_isAffineOpen_preimage_of_subset_range [AlgebraicGeometry.IsReduced X]
    {Z : Scheme.{u}} (f : Z ⟶ X) [IsClosedImmersion f] (U : X.Opens)
    (hU : (U : Set X) ⊆ Set.range f.base) (haff : IsAffineOpen (f ⁻¹ᵁ U)) : IsAffineOpen U :=
  isAffineOpen_of_isAffineOpen_preimage (ι := Unit) (fun _ => f) U
    (hU.trans (Set.subset_iUnion (fun _ : Unit => Set.range f.base) ())) fun _ => haff

variable (X) in
/-- **The case of the irreducible components, which is the fourth step of the proof of
Tag 09NX.**  On a Noetherian reduced scheme an open subset whose preimage in every irreducible
component is affine is affine: the components cover, and there are finitely many of them. -/
@[ega "II 6.7.3" "Sufficiency direction"]
theorem isAffineOpen_of_isAffineOpen_preimage_components [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsReduced X] (U : X.Opens)
    (haff : ∀ C : irreducibleComponents (X : Type u), IsAffineOpen (componentι X C ⁻¹ᵁ U)) :
    IsAffineOpen U := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  refine isAffineOpen_of_isAffineOpen_preimage (componentι X) U (fun x _ => ?_) haff
  obtain ⟨C, z, hz⟩ := exists_componentι_eq X x
  exact Set.mem_iUnion.mpr ⟨C, z, hz⟩

end Stacks.AmpleReducedDimensionOne

end
