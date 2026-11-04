module

public import StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison

/-!
# Three apparent universe obstructions, and the one that remains

Three statements might appear unstatable for universe reasons.  Each is elaborated here at its
own exact spelling, with every piece of vocabulary spelled as the source spells it, rather than
as a sibling file spells it.  All three statements elaborate.  What remains is a single
genuine gap, in the proof rather than the statement of the first, and this file closes the
statement verbatim up to that one gap and names it.

## Main results

* `EventualFinitenessUniverse.exists_isAffineOpen_map_preimage_of_initiallySmall`
  recovers the eventual affineness of the preimage of a quasi-compact open at an index universe
  independent of the scheme universe, from Stacks 01Z4 rather than from the inner machinery of
  Stacks 01Z6.
* `EventualFinitenessUniverse.exists_isAffineOpen_and_isIntegral_app_of_initiallySmall`
  is the affine-base step of Stacks 09ZN at an independent index universe, for a *thin* index
  category.
* `AlgebraicGeometry.Scheme.structureSheaf_sheaf_obj_property` records that a scheme's sheaf of
  rings, read through the site-level structure sheaf of Stacks 05NA, is its own
  `AlgebraicGeometry.Scheme.ringCatSheaf`.

## The universe situation

`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral` in
`StacksFrontier/AlgebraicGeometry/EventualFiniteness/Basic.lean` proves Stacks 09ZN with the
index type and the schemes in *one* universe.  The statement does not force that coupling: written
with `Type*` for the index and a bare `Scheme` for the schemes, the statement elaborates with two
independent universe parameters, `u_1` for the index and `u_2` for the schemes, the latter
reaching the former nowhere.  The coupling is forced only in the *proof*, and only through
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`, every declaration of which is stated for
`{I : Type u} [Category.{u} I]` with `D : I ⥤ Scheme.{u}`.

`StacksFrontier/AlgebraicGeometry/LimitUniverse/AffineTransitionLimit.lean` already frees that
coupling, under `CategoryTheory.LocallySmall.{u} I` and `CategoryTheory.InitiallySmall.{u} I`.
For the index category of Stacks 09ZN, which is the opposite of a directed preorder, the first
of the two is automatic: the opposite of a preorder is thin, so
`CategoryTheory.locallySmall_of_thin` supplies it by instance search.  The second is a genuine
cofinality condition — a `u`-small weakly initial set of objects — and is the whole residue of
the recorded obstruction.  It is not derivable from the source's hypotheses: the ordinals form a
directed preorder no small subset of which is cofinal.  So Stacks 09ZN at a free index universe
carries exactly one hypothesis the source statement does not, and `Small.{u} I` discharges it.

Stacks 09ZN itself, in that form, is
`AlgebraicGeometry.Scheme.exists_isFinite_app_of_isLimit_of_initiallySmall` together with
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_initiallySmall` and
`AlgebraicGeometry.eventually_isFinite_of_isLimit_of_isIntegral_of_small`, in
`StacksFrontier/AlgebraicGeometry/EventualFiniteness/Basic.lean`, which proves the cofiltered
form without assuming the index category thin.  What this file contributes is the affine-base
step at an independent index universe, taken from Stacks 01Z4 rather than from the inner
machinery of Stacks 01Z6.

Two other measurements are recorded here rather than formalized, since what blocks them is not
the universes.

Stacks 0B8W, descent of an invertible module through an inverse limit, had been recorded as
needing both index universes tied and a private reproduction of the invertibility predicate.
Neither holds.  Its statement elaborates verbatim with the index object universe, the index
morphism universe and the scheme universe all independent, over `Scheme.{u}` and with no
weakening to `Scheme.{max u w}`; and the predicate it needs is the library
`AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`, applied to a scheme's own
`AlgebraicGeometry.Scheme.sheaf` and the sheaf condition carried by its
`AlgebraicGeometry.Scheme.ringCatSheaf`, with nothing private reproduced.  What blocks 0B8W is
that neither Mathlib nor this repository has any descent theory for sheaves of modules through
an inverse limit of schemes: `Mathlib.AlgebraicGeometry.AffineTransitionLimit` mentions sheaves
of modules nowhere, and Stacks 01ZR, which 0B8W consumes, is for the same reason open.

Stacks 01YB, extension of morphisms of coherent sheaves across the complement of a closed
subscheme, had been recorded as needing a compiler option to elaborate.  It does not.  All four
of its declarations, together with the ideal-power vocabulary they stand on, elaborate with no
option set at all, and at a free scheme universe.  What remains for 01YB is only its
mathematics.

## Transparency notes

`((Functor.const I).obj S).obj i` is not syntactically `S`, so instance search does not see
`QuasiSeparatedSpace S` at that spelling and `QuasiCompact (t.app i)` is not found.  A local
hypothesis of the form `∀ j, QuasiSeparatedSpace ((Functor.const I).obj S).obj j)`, proved by
`inferInstanceAs`, restores it; a bare `have` of the unquantified instance does not.

`AlgebraicGeometry.Scheme.Modules` is a `def` carrying its own `Category` instance, and
`AlgebraicGeometry.Scheme.ringCatSheaf` is a `TopCat.Sheaf`, so the identification recorded by
`AlgebraicGeometry.Scheme.structureSheaf_sheaf_obj_property` holds by `rfl` at default
transparency but is not available to instance search, which is keyed syntactically.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [The Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [The Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [The Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)

## What is not done

Stacks 09ZN is *not* proved at a fully free index universe: the cofinality hypothesis
`CategoryTheory.InitiallySmall.{u} Iᵒᵖ` is carried, not discharged, and discharging it is a
mathematical question about inverse limits over large directed systems, not a spelling question.
No part of Stacks 0B8W or of Stacks 01YB is proved here; for each, this file records a
statability measurement and the reason the remaining obstruction is not about universes.  No
project tag attribute is attached to anything below.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace EventualFinitenessUniverse

variable {I : Type w} [Category.{v} I] {S : Scheme.{u}} (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S) (c : Cone D)

/-- Preimages along the legs of a natural transformation to a constant functor compose. -/
private theorem map_preimage_app_preimage {i j : I} (g : j ⟶ i) (V : S.Opens) :
    D.map g ⁻¹ᵁ (t.app i ⁻¹ᵁ V) = t.app j ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, EventualFiniteness.map_comp_app]

variable [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]

include c in
/-- The eventual affineness of the preimage of a quasi-compact open, at an index universe
independent of the scheme universe. -/
lemma exists_isAffineOpen_map_preimage_of_initiallySmall (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    {i : I} (U : (D.obj i).Opens) (hU : IsCompact (U : Set (D.obj i)))
    (h : IsAffineOpen (c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (g : j ⟶ i), IsAffineOpen (D.map g ⁻¹ᵁ U) := by
  obtain ⟨i', V, hV, hVU⟩ :=
    exists_isAffineOpen_preimage_eq_of_initiallySmall D c hc (c.π.app i ⁻¹ᵁ U) h
  set m := IsCofiltered.min i i' with hm
  set a : m ⟶ i := IsCofiltered.minToLeft i i' with ha
  set b : m ⟶ i' := IsCofiltered.minToRight i i' with hb
  have hcone : ∀ {k : I} (e : m ⟶ k) (W : (D.obj k).Opens),
      c.π.app m ⁻¹ᵁ (D.map e ⁻¹ᵁ W) = c.π.app k ⁻¹ᵁ W := fun e W ↦ by
    rw [← Scheme.Hom.comp_preimage, c.w e]
  obtain ⟨j, g, hg⟩ := exists_map_preimage_eq_map_preimage_of_initiallySmall D c hc
    (QuasiCompact.isCompact_preimage (f := D.map a) _ U.isOpen hU)
    (QuasiCompact.isCompact_preimage (f := D.map b) _ V.isOpen hV.isCompact)
    ((hcone a U).trans (hVU.symm.trans (hcone b V).symm))
  refine ⟨j, g ≫ a, ?_⟩
  rw [D.map_comp, Scheme.Hom.comp_preimage, hg]
  exact hV.preimage (D.map g ≫ D.map b)

open Stacks.RingTheory.EventualFiniteness AlgebraicGeometry.EventualFiniteness in
include c in
/-- The affine-base case of [Stacks, Tag 09ZN], at an index universe independent of the scheme
universe.  Over a fixed affine open `V` of the base, the preimage of `V` is affine and the ring
map `Γ(S, V) → Γ(Dⱼ, tⱼ⁻¹V)` is integral at some stage `j` below any prescribed index. -/
lemma exists_isAffineOpen_and_isIntegral_app_of_initiallySmall
    [Quiver.IsThin I] [QuasiSeparatedSpace S] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (hc : IsLimit c) (f : c.pt ⟶ S) [IsIntegralHom f]
    (hf : ∀ i, f = c.π.app i ≫ t.app i)
    [∀ {i j : I} (g : i ⟶ j), IsFinite (D.map g)]
    [∀ i, LocallyOfFiniteType (t.app i)]
    (i : I) (V : S.Opens) (hV : IsAffineOpen V) :
    ∃ (j : I) (_ : j ⟶ i), IsAffineOpen (t.app j ⁻¹ᵁ V) ∧
      RingHom.IsIntegral (((t.app j).app V).hom) := by
  classical
  have : ∀ j : I, QuasiSeparatedSpace ↥(((Functor.const I).obj S).obj j) :=
    fun _ ↦ inferInstanceAs (QuasiSeparatedSpace ↥S)
  have hUcpt : IsCompact ((t.app i ⁻¹ᵁ V : (D.obj i).Opens) : Set (D.obj i)) :=
    QuasiCompact.isCompact_preimage (f := t.app i) _ V.2 hV.isCompact
  have hlim : IsAffineOpen (c.π.app i ⁻¹ᵁ (t.app i ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage, ← hf i]; exact hV.preimage f
  obtain ⟨j₀, g₀, haff₀⟩ :=
    exists_isAffineOpen_map_preimage_of_initiallySmall D c hc (t.app i ⁻¹ᵁ V) hUcpt hlim
  have haff : IsAffineOpen (t.app j₀ ⁻¹ᵁ V) := by
    rwa [← map_preimage_app_preimage D t g₀]
  obtain rfl := hf j₀
  have hintlim : RingHom.IsIntegral ((((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
      (((t.app j₀).app V).hom)) := by
    rw [← Scheme.Hom.comp_app_hom]
    exact IsIntegralHom.isIntegral_app _ V hV
  have hftype : RingHom.FiniteType (((t.app j₀).app V).hom) := by
    have h := HasRingHomProperty.appLE @LocallyOfFiniteType (t.app j₀) inferInstance ⟨V, hV⟩
      ⟨t.app j₀ ⁻¹ᵁ V, haff⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at h
  obtain ⟨s, hs⟩ := exists_finset_gens _ hftype
  have key : ∀ x : Γ(D.obj j₀, t.app j₀ ⁻¹ᵁ V), ∃ (j : I) (g : j ⟶ j₀)
      (P : Polynomial Γ(S, V)), P.Monic ∧
      (((D.map g).app (t.app j₀ ⁻¹ᵁ V)).hom)
        (Polynomial.eval₂ (((t.app j₀).app V).hom) x P) = 0 := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hintlim (((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom x)
    have h0 : (((c.π.app j₀).app (t.app j₀ ⁻¹ᵁ V)).hom)
        (Polynomial.eval₂ (((t.app j₀).app V).hom) x P) = 0 := by
      rw [Polynomial.hom_eval₂]; exact hPx
    obtain ⟨j, g, hg⟩ := exists_app_map_eq_zero_of_isLimit_of_initiallySmall D c hc
      (U := t.app j₀ ⁻¹ᵁ V) haff.isCompact _ h0
    exact ⟨j, g, P, hP, hg⟩
  choose jx gx Px hPxmonic hPxzero using key
  obtain ⟨k, T⟩ := IsCofiltered.inf_objs_exists (insert j₀ (s.image jx))
  obtain ⟨g₁⟩ := T (Finset.mem_insert_self _ _)
  refine ⟨k, g₁ ≫ g₀, ?_⟩
  have hphi : RingHom.Finite (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) :=
    IsFinite.finite_app (D.map g₁) (t.app j₀ ⁻¹ᵁ V) haff
  have hintim : ∀ a : Γ(D.obj j₀, t.app j₀ ⁻¹ᵁ V),
      ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
        (((t.app j₀).app V).hom)).IsIntegralElem
          ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) a) := by
    refine isIntegralElem_image_of_gens (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) _ hs ?_
    intro x hx
    refine ⟨Px x, hPxmonic x, ?_⟩
    refine (Polynomial.hom_eval₂ (Px x) (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) x).symm.trans ?_
    have hmem : jx x ∈ insert j₀ (s.image jx) :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
    rw [show g₁ = (T hmem).some ≫ gx x from Subsingleton.elim _ _]
    exact app_map_eq_zero_of_comp D (gx x) _ _ _ (hPxzero x)
  have hint2 : RingHom.IsIntegral ((((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom).comp
      (((t.app j₀).app V).hom)) :=
    isIntegral_comp_of_isIntegralElem_image (((t.app j₀).app V).hom)
      (((D.map g₁).app (t.app j₀ ⁻¹ᵁ V)).hom) hphi.to_isIntegral hintim
  have hintring : RingHom.IsIntegral (((D.map g₁ ≫ t.app j₀).app V).hom) := by
    rw [Scheme.Hom.comp_app_hom]; exact hint2
  refine ⟨?_, ?_⟩
  · rw [← map_preimage_app_preimage D t g₁]
    exact haff.preimage (D.map g₁)
  · rw [← map_comp_app D t g₁]
    exact hintring

end EventualFinitenessUniverse

/-- A scheme's sheaf of rings, read through the site-level structure sheaf of Stacks 05NA on the
site of its opens, is its own `AlgebraicGeometry.Scheme.ringCatSheaf`.  This identification is
what lets a module over the latter be the subject of the invertibility predicate of Stacks 01CS,
which is stated over the former; it holds by `rfl` at default transparency, and instance search,
being keyed syntactically, does not see it. -/
lemma Scheme.structureSheaf_sheaf_obj_property (X : Scheme.{u}) :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj X.ringCatSheaf.property =
      X.ringCatSheaf := rfl

end AlgebraicGeometry

end
