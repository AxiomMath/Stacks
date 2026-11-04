module

public import StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteAssociatedModuleUnique
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsiteReflect

/-!
# Quasi-coherence reflects from the affine subsites of Stacks 0GZV and 0GZX

For each of the seven affine sites of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines` — the two small ones of
Stacks 0GZX and the five big ones of Stacks 0GZV — that file proves that the restriction of a
quasi-coherent module on the ambient ringed site is quasi-coherent on the affine subsite. **This
file proves the converse at all seven**, so that at each of them a module on the ambient site is
quasi-coherent exactly when its restriction to the affine objects is.

Both halves are instances of the general statements of
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsiteReflect`: quasi-coherence is
intrinsic to the ringed topos and does not depend on which of the two sites presents it, the
content of Stacks 03DG for clause (6) of Stacks 03DL.

## Main results

* `AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect`: **a sheaf of modules on
  `((Sch/S)_fppf, 𝒪)` whose restriction to `(Aff/S)_fppf` is quasi-coherent is quasi-coherent**,
  and `AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_restriction_iff` the resulting
  equivalence; with their Zariski, étale, smooth and syntomic counterparts, and the two small
  counterparts of Stacks 0GZX.
* `AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_iff_isQuasicoherentOnSite`:
  **condition (7) of Stacks 0GZV at `τ = fppf` is the conjunction of condition (6) with the bare
  existence of an ambient lift.** The quasi-coherence of the lift is no longer an extra demand.

## What this settles about condition (7) of Stacks 0GZV

The implication **(1) ⇒ (7)** has two inputs: a sheaf of modules `𝓜` on `(Sch/S)_τ` restricting
to the given cartesian `𝓕`, and the quasi-coherence of that `𝓜`. **The second is what this file
supplies**, through `AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect`: once `𝓕` is
quasi-coherent on the affine subsite — which is condition (6), available from condition (1) by
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_of_canonicalMap_isIso` — any ambient lift
of it is automatically quasi-coherent.

The first input is the *essential surjectivity* of restriction to the affine objects at the
universe `u` of the module sections, i.e. the Comparison Lemma for sheaves of modules,
`Stacks.DenseSubsiteModules.essSurj_moduleRestriction`, whose hypothesis is that
`(BigAffineFppf.inclusion B S hS).sheafPushforwardContinuous AddCommGrpCat.{u} _ _` be an
equivalence. It is supplied in
`StacksFrontier.AlgebraicGeometry.Descent.BigAffineSiteModuleComparisonLemma`, as
`AlgebraicGeometry.bigAffineFppf_exists_moduleLift`:

  for `𝓕 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (bigAffineFppfRingedSite B S hS).O)`,
    `∃ 𝓜 : SheafOfModules.{u} (BigFppfOver.structureSheaf B S hS),
       Nonempty (𝓕 ≅ (bigAffineFppfModuleRestriction B S hS).obj 𝓜)`,

so that `AlgebraicGeometry.bigAffineFppf_isRestrictionOfQuasicoherent_of_canonicalMap_isIso`
closes (1) ⇒ (7), and (1) ⇒ (8) follows from the equivalence of (7) and (8).

(The obstruction does not lie in the quasi-coherence half: the reflection of quasi-coherence
needs only *full faithfulness* at the raised universe, which holds unconditionally — see
`Stacks.SheafOfModules.hasGlobalPresentation_of_restriction`. It lies on the existence side,
where Mathlib supplies the equivalence from
`∀ X, HasLimitsOfShape (StructuredArrow X (BigAffineFppf.inclusion B S hS).op) AddCommGrpCat.{u}`.
Those structured-arrow categories have their objects in `Type (u + 1)`, but this does not
prevent the limits from existing:
`CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` asks for the index category to be
*essentially* `u`-small, not `u`-small, and it is — the affine objects over `S` are essentially
`u`-small by `AlgebraicGeometry.essentiallySmall_bigAffineFppf` and `(Sch/S)_fppf` is locally
`u`-small. So no descent from `u + 1` to `u` is needed, and the sections raised by
`AlgebraicGeometry.uliftRingSheaf` for Stacks 0GZU in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence` are there to
keep a free section universe `w`, not because `u` is out of reach.)

No `stacks` attribute is claimed here: the two halves proved in this file — (7) ⇒ (6) and its
converse for an ambient module — are registered where they belong, on
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_restriction` and its counterparts, and
(1) ⇒ (7) is registered on the statement that proves it.

## References

* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 0GZU](https://stacks.math.columbia.edu/tag/0GZU)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### The five big affine sites of Stacks 0GZV -/

/-- **Quasi-coherence reflects along restriction to `(Aff/S)_fppf`.** A sheaf of modules on the
ringed site `((Sch/S)_fppf, 𝒪)` whose restriction to the big affine fppf site of `S` is
quasi-coherent there is quasi-coherent on `((Sch/S)_fppf, 𝒪)`.

This is the converse of
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_restriction`, and it is the
quasi-coherence half of the implication (1) ⇒ (7) of Stacks 0GZV; the existence half is
`AlgebraicGeometry.bigAffineFppf_exists_moduleLift`. -/
public theorem bigAffineFppf_isQuasicoherentOnSite_reflect
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u} (BigFppfOver.structureSheaf B S hS))
    (hM : ((bigAffineFppfModuleRestriction B S hS).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (BigAffineFppf.inclusion B S hS) (BigFppfOver.structureSheaf B S hS) M hM

/-- **A sheaf of modules on `((Sch/S)_fppf, 𝒪)` is quasi-coherent exactly when its restriction
to `(Aff/S)_fppf` is**, which is the precise sense in which quasi-coherence is intrinsic to the
ringed topos presented by either of the two sites. -/
public theorem bigAffineFppf_isQuasicoherentOnSite_restriction_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u} (BigFppfOver.structureSheaf B S hS)) :
    ((bigAffineFppfModuleRestriction B S hS).obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  ⟨bigAffineFppf_isQuasicoherentOnSite_reflect B S hS M,
    bigAffineFppf_isQuasicoherentOnSite_restriction B S hS M⟩

/-- **Condition (7) of Stacks 0GZV at `τ = fppf` is condition (6) together with the bare
existence of an ambient lift.** The forward direction is
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_restriction`; the converse is
`AlgebraicGeometry.bigAffineFppf_isQuasicoherentOnSite_reflect`, which upgrades an arbitrary
lift of a quasi-coherent `𝓕` to a quasi-coherent one. -/
public theorem bigAffineFppf_isRestrictionOfQuasicoherent_iff_isQuasicoherentOnSite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineFppfRingedSite B S hS).O)) :
    BigAffineFppf.IsRestrictionOfQuasicoherent B S hS F ↔
      (F.IsQuasicoherentOnSite ∧
        ∃ M : SheafOfModules.{u} (BigFppfOver.structureSheaf B S hS),
          Nonempty (F ≅ (bigAffineFppfModuleRestriction B S hS).obj M)) := by
  constructor
  · rintro ⟨M, hM, ⟨e⟩⟩
    exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm
      (bigAffineFppf_isQuasicoherentOnSite_restriction B S hS M hM), M, ⟨e⟩⟩
  · rintro ⟨hF, M, ⟨e⟩⟩
    exact ⟨M, bigAffineFppf_isQuasicoherentOnSite_reflect B S hS M
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e hF), ⟨e⟩⟩

/-- **Quasi-coherence reflects along restriction to `(Aff/S)_Zar`**, the converse of
`AlgebraicGeometry.bigAffineZariski_isQuasicoherentOnSite_restriction`. -/
public theorem bigAffineZariski_isQuasicoherentOnSite_reflect
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O))
    (hM : ((SheafOfModules.pushforward.{u} (F := BigAffineZariski.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineZariskiRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  have := (BigAffineZariski.inclusion_isSpecialCocontinuous B S hS).1
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (BigAffineZariski.inclusion B S hS) _ M hM

/-- **Quasi-coherence reflects along restriction to `(Aff/S)_étale`**, the converse of
`AlgebraicGeometry.bigAffineEtale_isQuasicoherentOnSite_restriction`. -/
public theorem bigAffineEtale_isQuasicoherentOnSite_reflect
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O))
    (hM : ((SheafOfModules.pushforward.{u} (F := BigAffineEtale.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineEtaleRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  have := (BigAffineEtale.inclusion_isSpecialCocontinuous B S hS).1
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (BigAffineEtale.inclusion B S hS) _ M hM

/-- **Quasi-coherence reflects along restriction to `(Aff/S)_smooth`**, the converse of
`AlgebraicGeometry.bigAffineSmooth_isQuasicoherentOnSite_restriction`. -/
public theorem bigAffineSmooth_isQuasicoherentOnSite_reflect
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O))
    (hM : ((SheafOfModules.pushforward.{u} (F := BigAffineSmooth.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSmoothRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  have := (BigAffineSmooth.inclusion_isSpecialCocontinuous B S hS).1
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (BigAffineSmooth.inclusion B S hS) _ M hM

/-- **Quasi-coherence reflects along restriction to `(Aff/S)_syntomic`**, the converse of
`AlgebraicGeometry.bigAffineSyntomic_isQuasicoherentOnSite_restriction`. -/
public theorem bigAffineSyntomic_isQuasicoherentOnSite_reflect
    (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O))
    (hM : ((SheafOfModules.pushforward.{u} (F := BigAffineSyntomic.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (bigAffineSyntomicRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  have := (BigAffineSyntomic.inclusion_isSpecialCocontinuous B S hS).1
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (BigAffineSyntomic.inclusion B S hS) _ M hM

/-! ### The two small affine sites of Stacks 0GZX -/

/-- **Quasi-coherence reflects along restriction to the small affine Zariski site**, the
converse of `AlgebraicGeometry.smallAffineZariski_isQuasicoherentOnSite_restriction`. -/
public theorem smallAffineZariski_isQuasicoherentOnSite_reflect
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallZariskiRingedSite B S hS).O))
    (hM : ((SheafOfModules.pushforward.{u} (F := SmallAffineZariski.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallZariskiRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineZariskiRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  have := (SmallAffineZariski.inclusion_isSpecialCocontinuous B S hS).1
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (SmallAffineZariski.inclusion B S hS) _ M hM

/-- **Quasi-coherence reflects along restriction to the small affine étale site**, the converse
of `AlgebraicGeometry.smallAffineEtale_isQuasicoherentOnSite_restriction`.

In particular the hypothesis of
`AlgebraicGeometry.SmallEtale.bijective_restrictionBaseChange_of_affineRestriction` and of the
other statements of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounitFromAffine` is now
equivalent to quasi-coherence of the module on `S_étale` itself, rather than strictly weaker as
that file's header says. -/
public theorem smallAffineEtale_isQuasicoherentOnSite_reflect
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
    (hM : ((SheafOfModules.pushforward.{u} (F := SmallAffineEtale.inclusion B S hS)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (smallAffineEtaleRingedSite B S hS).O))
        (𝟙 _)).obj
        M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite :=
  have := (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).1
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_restriction
    (SmallAffineEtale.inclusion B S hS) _ M hM

end AlgebraicGeometry

end
