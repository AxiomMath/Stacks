module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.WeaklyContractibleHypercovering
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQcqs
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSiteCoverings

/-!
# The quasi-compact quasi-separated pro-étale site

Stacks 09A1 (2) singles out inside a pro-étale site the full subcategory `X_{qcqs, proétale}` of
its quasi-compact and quasi-separated objects, whose coverings are the *finite* pro-étale
coverings. This file constructs that category inside a chosen big pro-étale site, with its
coverings and topology, verifies the site axioms for it, and shows that the inclusion into the
big site is continuous and preserves fibre products.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsQcqs`: the object property cutting out the quasi-compact
  quasi-separated objects of a chosen big pro-étale site.
* `AlgebraicGeometry.ProEtale.QcqsProetale`: the resulting full subcategory, with its inclusion
  `AlgebraicGeometry.ProEtale.QcqsProetale.inclusion` into the big site and the functor
  `AlgebraicGeometry.ProEtale.QcqsProetale.toScheme` to underlying schemes.
* `AlgebraicGeometry.ProEtale.QcqsProetale.IsCovering`,
  `AlgebraicGeometry.ProEtale.QcqsProetale.precoverage` and
  `AlgebraicGeometry.ProEtale.QcqsProetale.topology`: the finite pro-étale covering families, the
  precoverage they present and the topology they generate.

## Main results

* `AlgebraicGeometry.ProEtale.IsQcqs.pullback` and `AlgebraicGeometry.ProEtale.IsQcqs.coproduct`:
  the property passes to a fibre product and to a finite disjoint union, so that
  `QcqsProetale B` has fibre products and finite coproducts.
* `AlgebraicGeometry.ProEtale.QcqsProetale.isSite_isCovering`: the finite pro-étale covering
  families satisfy the site axioms.
* `AlgebraicGeometry.ProEtale.QcqsProetale.mapsCoveringsToCoverings`: the inclusion into the big
  pro-étale site takes covering families to covering families. Together with the instance that it
  preserves fibre products, this is the continuity of Stacks 00WV.

## Implementation notes

The covering families are the finite families whose image in schemes is a pro-étale covering,
not the chosen bounded covering families of the big site, and finiteness of the index type is
imposed on the covering families rather than on the generated topology.

## References

* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

universe u

/-- The object property cutting out the quasi-compact quasi-separated objects of a chosen big
pro-étale site. -/
abbrev IsQcqs (B : BigProetaleSite.{u}) : ObjectProperty B.Scheme :=
  fun X ↦ CompactSpace X.obj ∧ QuasiSeparatedSpace X.obj

variable {B : BigProetaleSite.{u}}

/-- An object whose underlying scheme is isomorphic to a quasi-compact quasi-separated scheme is
quasi-compact and quasi-separated. -/
private theorem isQcqs_of_iso_inclusion {X : B.Scheme} {S : Scheme.{u}} (e : B.inclusion.obj X ≅ S)
    (hc : CompactSpace S) (hq : QuasiSeparatedSpace S) : IsQcqs B X :=
  ⟨(Scheme.homeoOfIso e).symm.compactSpace,
    (quasiSeparatedSpace_congr (Scheme.homeoOfIso e)).mpr hq⟩

/-- Quasi-compactness and quasi-separatedness of an object of a chosen big pro-étale site are
transported along an isomorphism. -/
theorem IsQcqs.of_iso {X Y : B.Scheme} (e : X ≅ Y) (h : IsQcqs B X) : IsQcqs B Y :=
  isQcqs_of_iso_inclusion (B.inclusion.mapIso e).symm h.1 h.2

/-- Being quasi-compact and quasi-separated is invariant under isomorphism. -/
instance : (IsQcqs B).IsClosedUnderIsomorphisms where
  of_iso e h := IsQcqs.of_iso e h

/-- **A fibre product of quasi-compact quasi-separated objects is quasi-compact and
quasi-separated.** -/
theorem IsQcqs.pullback {X Y Z : B.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : IsQcqs B X) (hY : IsQcqs B Y) (hZ : IsQcqs B Z) :
    IsQcqs B (Limits.pullback f g) := by
  have _ : CompactSpace (B.inclusion.obj X) := hX.1
  have _ : QuasiSeparatedSpace (B.inclusion.obj X) := hX.2
  have _ : CompactSpace (B.inclusion.obj Y) := hY.1
  have _ : QuasiSeparatedSpace (B.inclusion.obj Y) := hY.2
  have _ : CompactSpace (B.inclusion.obj Z) := hZ.1
  have _ : QuasiSeparatedSpace (B.inclusion.obj Z) := hZ.2
  exact isQcqs_of_iso_inclusion (PreservesPullback.iso B.inclusion f g) inferInstance
    (quasiSeparatedSpace_of_quasiSeparated
      (Limits.pullback.snd (B.inclusion.map f) (B.inclusion.map g)))

/-- Quasi-compact quasi-separated objects are closed under fibre products. -/
instance : (IsQcqs B).IsClosedUnderLimitsOfShape WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact IsQcqs.of_iso (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm
      (IsQcqs.pullback _ _ (hF .left) (hF .right) (hF .one)))

/-- **A finite disjoint union of quasi-compact quasi-separated objects is quasi-compact and
quasi-separated.** -/
theorem IsQcqs.coproduct {I : Type*} [Finite I] (A : I → B.Scheme)
    (hA : ∀ i, IsQcqs B (A i)) : IsQcqs B (∐ A) := by
  have _ (i : I) : CompactSpace (B.inclusion.obj (A i)) := (hA i).1
  have _ (i : I) : QuasiSeparatedSpace (B.inclusion.obj (A i)) := (hA i).2
  exact isQcqs_of_iso_inclusion (PreservesCoproduct.iso B.inclusion A)
    (compactSpace_sigmaObj _) (quasiSeparatedSpace_sigmaObj _)

/-- Quasi-compact quasi-separated objects are closed under finite coproducts. -/
instance : (IsQcqs B).IsClosedUnderFiniteCoproducts where
  isClosedUnderColimitsOfShape J _ := .mk' (by
    rintro _ ⟨F, hF⟩
    exact IsQcqs.of_iso (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))).symm
      (IsQcqs.coproduct _ fun j ↦ hF ⟨j⟩))

/-- The category `X_{qcqs, proétale}` of Stacks 09A1 (2): the full subcategory of a chosen big
pro-étale site on its quasi-compact quasi-separated objects. -/
abbrev QcqsProetale (B : BigProetaleSite.{u}) := (IsQcqs B).FullSubcategory

namespace QcqsProetale

variable (B)

/-- The canonical full inclusion into the chosen big pro-étale site. -/
abbrev inclusion : QcqsProetale B ⥤ B.Scheme := (IsQcqs B).ι

/-- The underlying scheme of a quasi-compact quasi-separated object. -/
abbrev toScheme : QcqsProetale B ⥤ Scheme.{u} := inclusion B ⋙ B.inclusion

/-- The quasi-compact quasi-separated pro-étale site has fibre products. -/
instance hasPullbacks : HasPullbacks (QcqsProetale B) := inferInstance

/-- The quasi-compact quasi-separated pro-étale site has finite coproducts. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (QcqsProetale B) := inferInstance

/-- Fibre products in the quasi-compact quasi-separated pro-étale site are those of the big
site. -/
noncomputable instance createsPullbacks :
    CreatesLimitsOfShape WalkingCospan (inclusion B) := inferInstance

/-- The inclusion into the big pro-étale site preserves fibre products. -/
noncomputable instance preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (inclusion B) := inferInstance

variable {B}

/-- The underlying scheme of an object of `QcqsProetale B` is quasi-compact. -/
instance compactSpace (U : QcqsProetale B) : CompactSpace U.obj.obj := U.property.1

/-- The underlying scheme of an object of `QcqsProetale B` is quasi-separated. -/
instance quasiSeparatedSpace (U : QcqsProetale B) : QuasiSeparatedSpace U.obj.obj :=
  U.property.2

variable (B)

/-- **The coverings of `X_{qcqs, proétale}`:** the finite pro-étale coverings, that is the finite
families whose image in schemes is a pro-étale covering. -/
abbrev IsCovering (E : Covering.{u + 1, u, u + 1} (QcqsProetale B)) : Prop :=
  (E.2.map (toScheme B)).presieve₀ ∈
      Scheme.proetalePrecoverage.coverings ((toScheme B).obj E.1) ∧
    Finite E.2.I₀

/-- The precoverage presented by the finite pro-étale covering families. -/
def precoverage : Precoverage (QcqsProetale B) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B ⟨X, E⟩}

/-- A presieve on `X_{qcqs, proétale}` is covering precisely when a finite pro-étale covering
family presents it. -/
theorem mem_precoverage_iff {X : QcqsProetale B} (R : Presieve X) :
    R ∈ precoverage B X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsCovering B ⟨X, E⟩ := Iff.rfl

/-- The topology of `X_{qcqs, proétale}`. -/
abbrev topology : GrothendieckTopology (QcqsProetale B) := (precoverage B).toGrothendieck

/-- **The finite pro-étale covering families of `X_{qcqs, proétale}` satisfy the isomorphism,
composition and base change axioms**, so they present a site. -/
theorem isSite_isCovering : IsSite (IsCovering B) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    refine ⟨?_, inferInstance⟩
    have _ : IsIso ((toScheme B).map f) := inferInstance
    have h : Presieve.singleton ((toScheme B).map f) ∈
        Scheme.proetalePrecoverage.coverings ((toScheme B).obj U) :=
      Precoverage.mem_coverings_of_isIso _
    rwa [← Presieve.ofArrows_pUnit] at h
  · intro 𝒰 h𝒰 𝒱 h𝒱 h
    have key : ∀ (i : 𝒰.2.I₀) (W : QcqsProetale B) (F : PreZeroHypercover.{u + 1} W)
        (hW : W = 𝒰.2.X i), IsCovering B ⟨W, F⟩ →
        Presieve.ofArrows (fun j ↦ (toScheme B).obj (F.X j))
            (fun j ↦ (toScheme B).map (F.f j ≫ eqToHom hW)) ∈
          Scheme.proetalePrecoverage.coverings ((toScheme B).obj (𝒰.2.X i)) := by
      intro i W F hW hF
      subst hW
      simp only [eqToHom_refl, Category.comp_id]
      exact hF.1
    refine ⟨?_, ?_⟩
    · have hcomp := Precoverage.comp_mem_coverings
        (J := Scheme.proetalePrecoverage.{u})
        (f := fun i ↦ (toScheme B).map (𝒰.2.f i)) h𝒰.1
        (g := fun i j ↦ (toScheme B).map ((𝒱 i).2.f j ≫ eqToHom (h i)))
        (fun i ↦ key i (𝒱 i).1 (𝒱 i).2 (h i) (h𝒱 i))
      have hcomp' : Presieve.ofArrows
            (fun p : Σ i : 𝒰.2.I₀, (𝒱 i).2.I₀ ↦ (toScheme B).obj ((𝒱 p.1).2.X p.2))
            (fun p ↦ (toScheme B).map (((𝒱 p.1).2.f p.2 ≫ eqToHom (h p.1)) ≫ 𝒰.2.f p.1)) ∈
          Scheme.proetalePrecoverage.coverings ((toScheme B).obj 𝒰.1) := by
        simpa only [← Functor.map_comp] using hcomp
      exact hcomp'
    · have _ : Finite 𝒰.2.I₀ := h𝒰.2
      have _ : ∀ i, Finite (𝒱 i).2.I₀ := fun i ↦ (h𝒱 i).2
      change Finite (Σ i, (𝒱 i).2.I₀)
      infer_instance
  · intro 𝒰 h𝒰 V g
    have _ : Finite 𝒰.2.I₀ := h𝒰.2
    refine ⟨fun i ↦ Limits.pullback (𝒰.2.f i) g, fun i ↦ Limits.pullback.fst _ _,
      fun i ↦ Limits.pullback.snd _ _, fun i ↦ IsPullback.of_hasPullback _ _, ?_, inferInstance⟩
    exact Precoverage.mem_coverings_of_isPullback
      (J := Scheme.proetalePrecoverage.{u})
      (fun i ↦ (toScheme B).map (𝒰.2.f i)) h𝒰.1 ((toScheme B).map g) _ _
      (fun i ↦ ((IsPullback.of_hasPullback (𝒰.2.f i) g).flip).map (toScheme B))

/-- **The inclusion of `X_{qcqs, proétale}` into the big pro-étale site takes covering families
to covering families.** -/
theorem mapsCoveringsToCoverings :
    Stacks.CategoryTheory.Hypercovering.MapsCoveringsToCoverings.{u + 1} (inclusion B)
      (topology B).toPretopology B.topology.toPretopology := by
  intro V ι A g hg
  rw [GrothendieckTopology.mem_toPretopology] at hg ⊢
  obtain ⟨E, hE, hle⟩ := exists_covering_le_of_isSite (IsCovering B) (isSite_isCovering B)
    (precoverage B) (fun _ _ ↦ Iff.rfl) _ hg
  have hcov : Sieve.generate ((E.map (inclusion B)).presieve₀) ∈
      B.topology ((inclusion B).obj V) := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
    exact hE.1
  refine B.topology.superset_covering ?_ hcov
  rw [Sieve.generate_le_iff]
  intro Y f hf
  obtain ⟨i⟩ := hf
  obtain ⟨Z, a, b, ⟨j⟩, hfac⟩ := hle _ (E.f i) (Presieve.ofArrows.mk i)
  refine ⟨_, (inclusion B).map a, (inclusion B).map (g j), Presieve.ofArrows.mk j, ?_⟩
  change (inclusion B).map a ≫ (inclusion B).map (g j) = (inclusion B).map (E.f i)
  rw [← (inclusion B).map_comp, hfac]

end QcqsProetale

end AlgebraicGeometry.ProEtale

end
