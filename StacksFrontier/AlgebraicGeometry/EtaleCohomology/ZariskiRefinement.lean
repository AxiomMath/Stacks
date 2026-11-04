module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ZariskiRestrictionSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.SpreadingOutFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs

/-!
# Étale coverings are Zariski coverings when the local rings are strictly henselian

Let `X` be a scheme and `x` a point whose local ring `𝒪_{X,x}` is strictly henselian. An étale
morphism `f : W ⟶ X` whose image contains `x` then admits a *section over a Zariski
neighbourhood* of `x`: there is an open subscheme `V ∋ x` of `X` and a morphism `g : V ⟶ W`
with `g ≫ f = V.ι`.

As a consequence, if *every* local ring of `X` is strictly henselian then the inclusion
`AlgebraicGeometry.opensToEtale` of the open subschemes into the small étale site is
**cocontinuous**: an étale covering sieve of an open subscheme pulls back to a Zariski covering
sieve. Concretely, every étale covering of such a scheme is refined by a Zariski open covering,
and the restriction of étale abelian sheaves to the Zariski site is right exact.

## Main results

* `AlgebraicGeometry.exists_opens_section_of_etale` — an étale morphism has a section over a
  Zariski neighbourhood of any point of its image whose local ring is strictly henselian.
* `AlgebraicGeometry.isCocontinuous_opensToEtale` — the open subschemes of a scheme with
  strictly henselian local rings are a cocontinuous subsite of its small étale site.
* `AlgebraicGeometry.isAlmostCocontinuous_opensToEtale` — the same subsite is almost
  cocontinuous.
* `AlgebraicGeometry.zariskiRestrictionFunctor_preservesFiniteColimits_of_strictlyHenselian` —
  the Zariski restriction of étale abelian sheaves is right exact, given two sheafification
  hypotheses on the small étale site.
* `AlgebraicGeometry.zariskiRestrictionFunctor_preservesFiniteColimits_of_strictlyHenselian'` —
  the same at the coefficient universe `u + 1`, where those hypotheses hold automatically.

## References

* [Stacks Project, Tag 09AX](https://stacks.math.columbia.edu/tag/09AX)
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- **An étale morphism has a Zariski-local section at a strictly henselian point.** If
`f : W ⟶ X` is étale, `w` is a point of `W`, and the local ring of `X` at `f w` is strictly
henselian, then `f` has a section over some open neighbourhood of `f w`. -/
public theorem exists_opens_section_of_etale {X W : Scheme.{u}} (f : W ⟶ X) [Etale f] (w : W)
    (hsh : StrictlyHenselianLocalRing ↥(X.presheaf.stalk (f.base w))) :
    ∃ (V : X.Opens) (_ : f.base w ∈ V) (g : V.toScheme ⟶ W), g ≫ f = V.ι := by
  let alg : W.residueField w ⟶ CommRingCat.of (AlgebraicClosure ↥(W.residueField w)) :=
    CommRingCat.ofHom (algebraMap ↥(W.residueField w) (AlgebraicClosure ↥(W.residueField w)))
  have hp : Spec.map (X.residue (f.base w) ≫ f.residueFieldMap w ≫ alg) ≫
      X.fromSpecStalk (f.base w) = Spec.map alg ≫ W.fromSpecResidueField w ≫ f := by
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ← Scheme.fromSpecResidueField, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hcl : (Spec.map (X.residue (f.base w) ≫ f.residueFieldMap w ≫ alg))
      (default : Spec (CommRingCat.of (AlgebraicClosure ↥(W.residueField w)))) =
      IsLocalRing.closedPoint ↥(X.presheaf.stalk (f.base w)) := by
    rw [Spec.map_comp, Scheme.Hom.comp_apply, Spec.map_apply]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  obtain ⟨t, ht, -⟩ := @exists_hom_of_strictlyHenselian X
    { residueField := AlgebraicClosure ↥(W.residueField w)
      hom := Spec.map alg ≫ W.fromSpecResidueField w ≫ f }
    ↥(X.presheaf.stalk (f.base w)) _ hsh
    (X.fromSpecStalk (f.base w))
    (Spec.map (X.residue (f.base w) ≫ f.residueFieldMap w ≫ alg)) hp hcl
    W f _ (Spec.map alg ≫ W.fromSpecResidueField w) (by simp)
  obtain ⟨V, hxV, g, -, hg⟩ :=
    spread_out_of_locallyOfFinitePresentation' (𝟙 X) f (x := f.base w) t (by simpa using ht)
  exact ⟨V, hxV, g, by simpa using hg⟩

/-- **Étale coverings of a scheme with strictly henselian local rings are Zariski-refinable.**
The inclusion of the open subschemes of `X` into its small étale site is cocontinuous: an étale
covering sieve of an open subscheme `V` pulls back to a Zariski covering sieve of `V`. -/
public theorem isCocontinuous_opensToEtale (X : Scheme.{u})
    (hlocal : ∀ x : X, StrictlyHenselianLocalRing ↥(X.presheaf.stalk x)) :
    (opensToEtale X).IsCocontinuous (Opens.grothendieckTopology ↑X)
      (Scheme.smallEtaleTopology X) where
  cover_lift {V T} hT := by
    rw [Opens.mem_grothendieckTopology]
    intro x hxV
    obtain ⟨ι, Z, fam, rfl⟩ := T.exists_eq_ofArrows
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hT
    have hmem : (⟨x, hxV⟩ : V.toScheme) ∈ ⋃ i, Set.range (fam i).left := by rw [hT]; trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hmem
    have hTg : (Sieve.ofArrows Z fam).arrows (fam i) := Sieve.ofArrows_mk Z fam i
    have hw : ((Z i).hom : (Z i).left ⟶ X) = (fam i).left ≫ V.ι :=
      (MorphismProperty.Over.w (fam i)).symm
    have hyx : ((Z i).hom : (Z i).left ⟶ X).base y = x := by
      rw [hw, Scheme.Hom.comp_apply (fam i).left V.ι y, hy]
      exact Scheme.Opens.ι_apply _ _
    obtain ⟨V₀, hxV₀, s, hs⟩ :=
      exists_opens_section_of_etale ((Z i).hom : (Z i).left ⟶ X) y (hlocal _)
    rw [hyx] at hxV₀
    refine ⟨V₀ ⊓ V, homOfLE inf_le_right, ?_, ⟨hxV₀, hxV⟩⟩
    have m : (opensToEtale X).obj (V₀ ⊓ V) ⟶ Z i :=
      MorphismProperty.Over.homMk (X.homOfLE (inf_le_left : V₀ ⊓ V ≤ V₀) ≫ s)
        (by
          show (X.homOfLE (inf_le_left : V₀ ⊓ V ≤ V₀) ≫ s) ≫ ((Z i).hom : (Z i).left ⟶ X) =
            (V₀ ⊓ V).ι
          rw [Category.assoc, hs, X.homOfLE_ι]) trivial
    show (Sieve.ofArrows Z fam).arrows
      ((opensToEtale X).map (homOfLE (inf_le_right : V₀ ⊓ V ≤ V)))
    have key : (opensToEtale X).map (homOfLE (inf_le_right : V₀ ⊓ V ≤ V)) = m ≫ fam i :=
      Subsingleton.elim _ _
    rw [key]
    exact (Sieve.ofArrows Z fam).downward_closed hTg _

/-- **The open subschemes are an almost cocontinuous subsite of the small étale site**, for a
scheme all of whose local rings are strictly henselian. -/
public theorem isAlmostCocontinuous_opensToEtale (X : Scheme.{u})
    (hlocal : ∀ x : X, StrictlyHenselianLocalRing ↥(X.presheaf.stalk x)) :
    IsAlmostCocontinuous (opensToEtale X) (Opens.grothendieckTopology ↑X)
      (Scheme.smallEtaleTopology X) :=
  have := isCocontinuous_opensToEtale X hlocal
  isAlmostCocontinuous_of_isCocontinuous _ _ _

/-- **The Zariski restriction of étale abelian sheaves is right exact** when every local ring of
`X` is strictly henselian, provided `AddCommGrpCat.{v}`-valued presheaves on the small étale site
are sheafifiable and their sheafification inverts exactly the locally bijective morphisms. -/
public theorem zariskiRestrictionFunctor_preservesFiniteColimits_of_strictlyHenselian
    (X : Scheme.{u})
    (hlocal : ∀ x : X, StrictlyHenselianLocalRing ↥(X.presheaf.stalk x))
    [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat.{v}]
    [HasSheafify (Scheme.smallEtaleTopology X) AddCommGrpCat.{v}]
    [(Scheme.smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{v}] :
    PreservesFiniteColimits (zariskiRestrictionFunctor.{u, v} X) := by
  have h := Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous
    (opensToEtale X) (Opens.grothendieckTopology ↑X) (Scheme.smallEtaleTopology X)
    (isAlmostCocontinuous_opensToEtale X hlocal)
  have e : zariskiRestrictionFunctor.{u, v} X ≅
      (opensToEtale X).sheafPushforwardContinuous AddCommGrpCat.{v}
        (Opens.grothendieckTopology ↑X) (Scheme.smallEtaleTopology X) :=
    (Functor.isoWhiskerLeft
      ((opensToEtale X).sheafPushforwardContinuous AddCommGrpCat.{v}
        (Opens.grothendieckTopology ↑X) (Scheme.smallEtaleTopology X))
      (asIso (sheafificationAdjunction (Opens.grothendieckTopology ↑X)
        AddCommGrpCat.{v}).counit)).trans (Functor.rightUnitor _)
  exact preservesFiniteColimits_of_natIso e.symm

/-- **The Zariski restriction of étale abelian sheaves is right exact** when every local ring of
`X` is strictly henselian, at the coefficient universe `u + 1` of the small étale site. -/
public theorem zariskiRestrictionFunctor_preservesFiniteColimits_of_strictlyHenselian'
    (X : Scheme.{u})
    (hlocal : ∀ x : X, StrictlyHenselianLocalRing ↥(X.presheaf.stalk x))
    [HasSheafify (Opens.grothendieckTopology ↑X) AddCommGrpCat.{u + 1}] :
    PreservesFiniteColimits (zariskiRestrictionFunctor.{u, u + 1} X) :=
  zariskiRestrictionFunctor_preservesFiniteColimits_of_strictlyHenselian X hlocal

end AlgebraicGeometry

end
