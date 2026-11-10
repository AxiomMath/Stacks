module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcAffineOpenBase

/-!
# The affine-open refinement of an fpqc covering, and what the gluing of Stacks 023T still needs

`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcAffineOpenBase.lean` leaves the
effectivity half of Stacks 023T resting on the Zariski locality of effectivity,
`AlgebraicGeometry.QuasicoherentDescentData.EffectiveGluesOverAffineOpens`: a quasi-coherent
descent datum whose restriction to each member of the affine open covering of the base is
effective is effective.  Its fpqc input is discharged unconditionally there, so what is left is
the gluing, and the gluing has two halves — produce the quasi-coherent sheaves over the affine
opens, and glue them.  **The first half is already a theorem**
(`…isEffective_pullFunctor_homOverPullback₁`), so only the second can be missing.

This file isolates the second half as a statement about the *affine-open refinement*

`𝒲 = {X i ×_S U a ⟶ S}`,

the family obtained by binding the affine open covering of `S` with the base changes of the given
family `𝒰` along its members.  Three facts about it are proved here, all unconditional:

* `𝒲` is itself an fpqc covering of `S`, and it refines both `𝒰` and the affine open covering;
* consequently a quasi-coherent descent datum `D` for `𝒰` is effective **if and only if** there
  is a quasi-coherent descent datum `E` for the affine open covering of `S` whose restriction to
  `𝒲` is isomorphic to the restriction of `D` to `𝒲`;
* the components of such an `E`, and the components of such an isomorphism, are *already
  available*: they are the quasi-coherent sheaves and the isomorphisms that
  `…isEffective_pullFunctor_homOverPullback₁` produces over the affine opens.

So nothing remains to be constructed over the affine opens, and nothing remains of the fpqc
descent: what the gluing of Stacks 023T still needs is exactly the *transition isomorphisms* of a
Zariski descent datum on the affine open covering, together with their cocycle condition.

Along the way the coproduct collapse is generalized off the affine base.  `Stacks 022F`'s
collapse `…presieve₀_sigmaFamily_mem_fpqcPrecoverage` asks the base to be affine and the family
to be finite and affine; `presieve₀_sigmaFamily_mem_fpqcPrecoverage_of_mem` below asks only that
the family be an fpqc covering, because the fpqc quasi-compactness condition is a condition on
the *family* — `AlgebraicGeometry.QuasiCompactCover` — which passes from a family to the
one-element family of its coproduct along `AlgebraicGeometry.QuasiCompactCover.of_hom`.  That
yields the first effective descent along a single faithfully flat morphism over a base which is
not assumed affine: `isEquivalence_canonicalDescentFunctor_sigmaFamily_openCover`.

## Main definitions

* `AlgebraicGeometry.QuasicoherentDescentData.affineOpenRefinement`: the affine-open refinement
  `{X i ×_S U a ⟶ S}` of an fpqc covering family, as an fpqc `0`-hypercover.
* `AlgebraicGeometry.QuasicoherentDescentData.affineOpenRefinementToFamily` and
  `…affineOpenRefinementToAffineCover`: its two refinement morphisms, to the given family and to
  the affine open covering of the base.
* `AlgebraicGeometry.QuasicoherentDescentData.affineOpenRefinementSummand`: the inclusion of the
  base change of `𝒰` to the affine open `U a` as the part of the affine-open refinement above
  `a`, over `U a ⟶ S`.
* `AlgebraicGeometry.QuasicoherentDescentData.ZariskiDescentDatumOverAffineCover`: the existence,
  for every fpqc covering family of every scheme and every quasi-coherent descent datum for it,
  of a quasi-coherent descent datum on the affine open covering of the base restricting to it.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.pullFunctorCompIso`: **restriction along a
  composite of morphisms of families is the composite of the restrictions**, over composable
  morphisms of the bases.  This is the cross-base coherence; `…pullFunctorIsoOfEq` covers only
  a fixed base.
* `AlgebraicGeometry.QuasicoherentDescentData.affineOpenRefinementSummandIso`: **restricting a
  datum to the affine-open refinement and then to the part above `a` is restricting it to the
  affine open `U a`.**
* `AlgebraicGeometry.QuasicoherentDescentData.presieve₀_sigmaFamily_mem_fpqcPrecoverage_of_mem`:
  **the one-element family of the coproduct of an fpqc covering family is an fpqc covering
  family**, over an arbitrary base and at an arbitrary index.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_sigmaFamily_openCover` and
  `…isEquivalence_canonicalDescentFunctor_sigmaFamily_openCover`: **descent along the single
  morphism `∐ U a ⟶ S` out of the coproduct of a Zariski open covering is effective over an
  arbitrary base**, and the canonical descent functor for it is an equivalence.
* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_of_iso_pullFunctor_affineOpenRefinement`
  and `…isEffective_iff_exists_iso_pullFunctor_affineOpenRefinement`: **a quasi-coherent descent
  datum is effective exactly when it comes, over the affine-open refinement, from a quasi-coherent
  descent datum on the affine open covering of the base.**
* `AlgebraicGeometry.QuasicoherentDescentData.exists_iso_canonicalDescentFunctor_affineOpen`:
  **the components of that datum, and of that isomorphism, exist unconditionally.**
* `AlgebraicGeometry.QuasicoherentDescentData.effectiveGluesOverAffineOpens_of_zariskiDatum`,
  `…effectiveSigmaFamilyOverAnyBase_of_zariskiDatum` and
  `…isEffective_fpqcPrecoverage_of_zariskiDatum`: the chain from the remaining statement to the
  effectivity half of Stacks 023T, and
  `…zariskiDescentDatumOverAffineCover_iff`, which shows that statement is *equivalent* to it, so
  nothing has been strengthened.

## Implementation notes

The affine-open refinement is `CategoryTheory.Precoverage.ZeroHypercover.bind` of
`AlgebraicGeometry.affineZeroHypercover` with the base changes
`CategoryTheory.Precoverage.ZeroHypercover.pullback₁`, so its fpqc covering condition is
`bind`'s.  Its member above `(a, i)` is `pullback (U a ⟶ S) (X i ⟶ S)`, and the two refinement
morphisms are the two projections of that pullback; that is why the components of a datum
restricted along them are *equal*, not merely isomorphic, to the components of the datum
restricted to the affine open `U a` in the sense of `…homOverPullback₁`, and why the isomorphisms
of `…isEffective_pullFunctor_homOverPullback₁` are componentwise exactly what the missing
isomorphism needs.

Both directions of the main equivalence are refinement transport.  Forward: the affine open
covering is a Zariski covering, so a datum on it is effective by Stacks 023E
(`Stacks.Descent.isEffective_openCover`), effectivity passes to the refinement
(`…isEffective_pullFunctor_obj`), and it descends back along the refinement because the
refinement is an fpqc covering
(`…isEffective_of_isEffective_pullFunctor_obj_of_mem_fpqcPrecoverage`).  Backward: the canonical
datum of the module witnessing effectivity restricts to the canonical datum on each of the three
families, by `…canonicalDescentFunctorCompPullFunctorIso`.

No `stacks` attribute is placed: the unconditional results here are about one particular
covering family, which is less than Stacks 023T asserts, and the general statements carry a
hypothesis.

## References

* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w'' w' w v u

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

/-! ### Restriction along a composite of morphisms of families -/

section Comp

variable {U V W : Scheme.{u}} {𝒳 : PreZeroHypercover.{w} U} {𝒴 : PreZeroHypercover.{w'} V}
  {𝒵 : PreZeroHypercover.{w''} W} {g : U ⟶ V} {h : V ⟶ W} {k : U ⟶ W}

/-- **Restriction along a composite of morphisms of families is the composite of the
restrictions.**  For `Φ : 𝒳 ⟶ 𝒴` over `g : U ⟶ V` and `Ψ : 𝒴 ⟶ 𝒵` over `h : V ⟶ W`, restricting
a quasi-coherent descent datum for `𝒵` along `Ψ` and then along `Φ` gives its restriction along
the composite `CategoryTheory.PreZeroHypercover.HomOver.comp`, naturally in the datum.

For a *fixed* base this is `…pullFunctorIsoOfEq`.  At the level of the
pullback pseudofunctor the cross-base statement is Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.pullFunctorCompIso`, already general; what is done here
is the transfer across the inclusion of the quasi-coherent descent data, exactly as
`…pullFunctorIsoOfEq` transfers `…pullFunctorIso`.  The index map and the component morphisms of
`HomOver.comp` are *on the nose* the `α ∘ β` and `r'` of Mathlib's statement, which is why no
transport appears. -/
public noncomputable def pullFunctorCompIso (Φ : 𝒳.HomOver 𝒴 g) (Ψ : 𝒴.HomOver 𝒵 h)
    (hk : g ≫ h = k) :
    pullFunctor Ψ ⋙ pullFunctor Φ ≅ pullFunctor (Φ.comp Ψ hk) := by
  let e := Pseudofunctor.DescentData.pullFunctorCompIso modulePullbackPseudofunctor
    (f := 𝒵.f) (p := h) (f' := 𝒴.f) (α := Ψ.s₀) (p' := Ψ.h₀) Ψ.w₀
    (f'' := 𝒳.f) (q := g) (β := Φ.s₀) (q' := Φ.h₀) Φ.w₀ k
    (r' := fun i ↦ Φ.h₀ i ≫ Ψ.h₀ (Φ.s₀ i)) hk (fun _ ↦ rfl)
  let ι𝒵 := ObjectProperty.ι (fun D : modulePullbackPseudofunctor.DescentData 𝒵.f ↦
    ∀ i, (D.obj i).IsQuasicoherent)
  exact NatIso.ofComponents
    (fun D ↦ (ObjectProperty.isoMk
      (P := fun D : modulePullbackPseudofunctor.DescentData 𝒳.f ↦
        ∀ i, (D.obj i).IsQuasicoherent)
      (e.app (ι𝒵.obj D)) :
        (pullFunctor Ψ ⋙ pullFunctor Φ).obj D ≅ (pullFunctor (Φ.comp Ψ hk)).obj D))
    fun φ ↦ by
      apply ObjectProperty.hom_ext
      exact e.hom.naturality (ι𝒵.map φ)

end Comp

/-! ### The coproduct collapse off the affine base -/

/-- **The one-element family of the coproduct of an fpqc covering family is an fpqc covering
family**, over an arbitrary base and at an arbitrary index type.

`AlgebraicGeometry.QuasicoherentDescentData.presieve₀_sigmaFamily_mem_fpqcPrecoverage` asks the
base to be affine and the family to be finite with affine members, which is what Stacks 022F
delivers; none of that is needed.  The fpqc precoverage is the quasi-compact precoverage on flat
morphisms, and its quasi-compactness condition is `AlgebraicGeometry.QuasiCompactCover`, a
condition on the *family*: the family refines the one-element family of its coproduct, so
`AlgebraicGeometry.QuasiCompactCover.of_hom` carries that condition across.  The coproduct
morphism is flat because flatness is Zariski-local at the source, and surjective because the
family is jointly surjective. -/
public theorem presieve₀_sigmaFamily_mem_fpqcPrecoverage_of_mem {T : Scheme.{u}}
    (𝒱 : PreZeroHypercover.{w} T) [Small.{u} 𝒱.I₀]
    (h𝒱 : 𝒱.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T) :
    (sigmaFamily 𝒱).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T := by
  obtain ⟨hqc, hflat⟩ : 𝒱.presieve₀ ∈ Scheme.qcPrecoverage T ∧
      𝒱.presieve₀ ∈ Scheme.precoverage (@Flat.{u}) T := h𝒱
  replace hflat := (Scheme.presieve₀_mem_precoverage_iff _).mp hflat
  have hQC : QuasiCompactCover 𝒱 := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hqc
  have hQCs : QuasiCompactCover (sigmaFamily 𝒱) :=
    QuasiCompactCover.of_hom (PreZeroHypercover.homOverIdEquivHom 𝒱 _ (toSigmaFamily 𝒱))
  change _ ∈ Scheme.qcPrecoverage T ∧ _ ∈ Scheme.precoverage (@Flat.{u}) T
  have hFlat : ∀ i, Flat (𝒱.f i) := fun i ↦ hflat.2 i
  have hdesc : Flat (Sigma.desc 𝒱.f) := inferInstance
  have hs : ∀ x : T, x ∈ Set.range (Sigma.desc 𝒱.f) := by
    intro x
    obtain ⟨i, y, hy⟩ := hflat.1 x
    refine ⟨Sigma.ι 𝒱.X i y, ?_⟩
    rwa [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hQCs,
    (Scheme.presieve₀_mem_precoverage_iff _).mpr
      ⟨fun x ↦ ⟨PUnit.unit, hs x⟩, fun _ ↦ hdesc⟩⟩

/-- **Descent along the single morphism out of the coproduct of a Zariski open covering is
effective over an arbitrary base.**  Every quasi-coherent descent datum for the one-element family
`∐ U a ⟶ S` of an open covering of an arbitrary scheme `S` is effective.

The open covering refines that one-element family and is an fpqc covering, so
`…isEffective_of_forall_isEffective_of_mem_fpqcPrecoverage` carries effectivity from it to the
coproduct; over the open covering itself effectivity is the Zariski half of Stacks 023E,
`Stacks.Descent.isEffective_openCover`. -/
public theorem isEffective_sigmaFamily_openCover {S : Scheme.{u}} (𝒜 : Scheme.OpenCover.{w} S)
    [Small.{u} 𝒜.I₀]
    (D : QuasicoherentDescentData (sigmaFamily 𝒜.toPreZeroHypercover).f) : D.IsEffective :=
  isEffective_of_forall_isEffective_of_mem_fpqcPrecoverage (toSigmaFamily _)
    (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ 𝒜.mem₀)
    (Stacks.Descent.isEffective_openCover 𝒜) D

/-- **The canonical descent functor for the single morphism out of the coproduct of a Zariski
open covering is an equivalence**, over an arbitrary base: quasi-coherent modules on `S` are the
same as quasi-coherent descent data along `∐ U a ⟶ S`.

Full faithfulness is the full faithfulness half of Stacks 023T, available because that
one-element family is an fpqc covering by `presieve₀_sigmaFamily_mem_fpqcPrecoverage_of_mem`;
essential surjectivity is `isEffective_sigmaFamily_openCover`.  This is descent along a single
faithfully flat morphism over a base which is **not** assumed affine. -/
public theorem isEquivalence_canonicalDescentFunctor_sigmaFamily_openCover {S : Scheme.{u}}
    (𝒜 : Scheme.OpenCover.{w} S) [Small.{u} 𝒜.I₀] :
    (canonicalDescentFunctor (sigmaFamily 𝒜.toPreZeroHypercover).f).IsEquivalence := by
  obtain ⟨hff⟩ := nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage
    (sigmaFamily 𝒜.toPreZeroHypercover)
    (presieve₀_sigmaFamily_mem_fpqcPrecoverage_of_mem 𝒜.toPreZeroHypercover
      (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ 𝒜.mem₀))
  have := hff.full
  have := hff.faithful
  have : (canonicalDescentFunctor (sigmaFamily 𝒜.toPreZeroHypercover).f).EssSurj :=
    ⟨isEffective_sigmaFamily_openCover 𝒜⟩
  exact { }

/-! ### The affine-open refinement -/

variable {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
  (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)

/-- **The affine-open refinement of an fpqc covering family**: the family
`{X i ×_S U a ⟶ S}` indexed by pairs of a member `U a` of the affine open covering of `S` and a
member `X i` of the given family, as an fpqc `0`-hypercover of `S`.

It is the bind of `AlgebraicGeometry.affineZeroHypercover` with the base changes of `𝒰` along its
members, so its fpqc covering condition is supplied by
`CategoryTheory.Precoverage.ZeroHypercover.bind`. -/
public noncomputable def affineOpenRefinement :
    Scheme.fpqcPrecoverage.ZeroHypercover.{max u v} S :=
  (affineZeroHypercover S).bind
    fun a ↦ (⟨𝒰, h𝒰⟩ : Scheme.fpqcPrecoverage.ZeroHypercover.{v} S).pullback₁ (S.affineCover.f a)

/-- **The affine-open refinement refines the given family**, by the second projection of the
pullback. -/
public noncomputable def affineOpenRefinementToFamily :
    (affineOpenRefinement 𝒰 h𝒰).toPreZeroHypercover.HomOver 𝒰 (𝟙 S) where
  s₀ p := p.2
  h₀ p := pullback.snd (S.affineCover.f p.1) (𝒰.f p.2)
  w₀ p := by
    rw [Category.comp_id]
    exact pullback.condition.symm

/-- **The affine-open refinement refines the affine open covering of the base**, by the first
projection of the pullback. -/
public noncomputable def affineOpenRefinementToAffineCover :
    (affineOpenRefinement 𝒰 h𝒰).toPreZeroHypercover.HomOver
      (affineZeroHypercover S).toPreZeroHypercover (𝟙 S) where
  s₀ p := p.1
  h₀ p := pullback.fst (S.affineCover.f p.1) (𝒰.f p.2)
  w₀ _ := (Category.comp_id _).symm

/-- **The part of the affine-open refinement above a member of the affine open covering**: the
base change of `𝒰` to the affine open `U a`, mapped into the affine-open refinement over
`U a ⟶ S` by the identity on each member.

The members agree on the nose — both are `pullback (U a ⟶ S) (X i ⟶ S)` — only their structure
morphisms differ, one going to `U a` and the other to `S`. -/
public noncomputable def affineOpenRefinementSummand (a : S.affineCover.I₀) :
    (𝒰.pullback₁ (S.affineCover.f a)).HomOver
      (affineOpenRefinement 𝒰 h𝒰).toPreZeroHypercover (S.affineCover.f a) where
  s₀ i := ⟨a, i⟩
  h₀ _ := 𝟙 _
  w₀ _ := Category.id_comp _

/-- **Restricting a datum to the affine-open refinement and then to the part above `a` is
restricting it to the affine open `U a`.**  So the restriction of `D` to the affine-open
refinement already carries, above each `a`, exactly the datum
`…isEffective_pullFunctor_homOverPullback₁` proves effective.

This is `pullFunctorCompIso` followed by `…pullFunctorIsoOfEq`: the composite morphism of
families has index map the identity and component morphisms `𝟙 ≫ pullback.snd`, which is the
same morphism of families as `…homOverPullback₁` with a unit inserted, and both lie over
`U a ⟶ S`. -/
public noncomputable def affineOpenRefinementSummandIso (a : S.affineCover.I₀) :
    pullFunctor (affineOpenRefinementToFamily 𝒰 h𝒰) ⋙
        pullFunctor (affineOpenRefinementSummand 𝒰 h𝒰 a) ≅
      pullFunctor (homOverPullback₁ 𝒰 (S.affineCover.f a)) :=
  pullFunctorCompIso (affineOpenRefinementSummand 𝒰 h𝒰 a)
      (affineOpenRefinementToFamily 𝒰 h𝒰) (Category.comp_id _) ≪≫
    pullFunctorIsoOfEq _ (homOverPullback₁ 𝒰 (S.affineCover.f a)) rfl

/-! ### What the gluing still needs -/

/-- **A quasi-coherent descent datum is effective as soon as it comes, over the affine-open
refinement, from a quasi-coherent descent datum on the affine open covering of the base.**

The datum `E` on the affine open covering is effective by the Zariski half of Stacks 023E, so its
restriction to the affine-open refinement is effective; the given isomorphism transports that to
the restriction of `D`; and the restriction functor along the affine-open refinement is fully
faithful, that refinement being an fpqc covering, so effectivity descends back to `D`.

No hypothesis on `D` and none on `E`: the whole of the remaining gluing is the production of `E`
and of the isomorphism. -/
public theorem isEffective_of_iso_pullFunctor_affineOpenRefinement
    (D : QuasicoherentDescentData 𝒰.f)
    (E : QuasicoherentDescentData (affineZeroHypercover S).f)
    (e : (pullFunctor (affineOpenRefinementToAffineCover 𝒰 h𝒰)).obj E ≅
      (pullFunctor (affineOpenRefinementToFamily 𝒰 h𝒰)).obj D) :
    D.IsEffective :=
  isEffective_of_isEffective_pullFunctor_obj_of_mem_fpqcPrecoverage
    (affineOpenRefinementToFamily 𝒰 h𝒰) (affineOpenRefinement 𝒰 h𝒰).mem₀
    (isEffective_of_iso_pullFunctor_obj (affineOpenRefinementToAffineCover 𝒰 h𝒰)
      (Stacks.Descent.isEffective_openCover S.affineCover E) e)

/-- **An effective quasi-coherent descent datum does come from a quasi-coherent descent datum on
the affine open covering of the base**, namely from the canonical datum of the module witnessing
its effectivity.

Both restrictions of that canonical datum are the canonical datum of the same module relative to
the affine-open refinement, by `…canonicalDescentFunctorCompPullFunctorIso`.  So the hypothesis of
`isEffective_of_iso_pullFunctor_affineOpenRefinement` is not a strengthening of its
conclusion. -/
public theorem exists_iso_pullFunctor_affineOpenRefinement_of_isEffective
    {D : QuasicoherentDescentData 𝒰.f} (hD : D.IsEffective) :
    ∃ E : QuasicoherentDescentData (affineZeroHypercover S).f,
      Nonempty ((pullFunctor (affineOpenRefinementToAffineCover 𝒰 h𝒰)).obj E ≅
        (pullFunctor (affineOpenRefinementToFamily 𝒰 h𝒰)).obj D) := by
  obtain ⟨M, ⟨eM⟩⟩ := hD
  exact ⟨(canonicalDescentFunctor (affineZeroHypercover S).f).obj M,
    ⟨(canonicalDescentFunctorCompPullFunctorIso (affineOpenRefinementToAffineCover 𝒰 h𝒰)).app M ≪≫
      ((canonicalDescentFunctorCompPullFunctorIso
        (affineOpenRefinementToFamily 𝒰 h𝒰)).app M).symm ≪≫
      (pullFunctor (affineOpenRefinementToFamily 𝒰 h𝒰)).mapIso eM⟩⟩

/-- **Effectivity *is* descending from the affine open covering of the base.**  A quasi-coherent
descent datum for an fpqc covering family is effective if and only if there is a quasi-coherent
descent datum on the affine open covering of the base whose restriction to the affine-open
refinement is isomorphic to its own.

So the remaining content of the gluing of Stacks 023T is exactly the production of that datum:
neither more nor less. -/
public theorem isEffective_iff_exists_iso_pullFunctor_affineOpenRefinement
    (D : QuasicoherentDescentData 𝒰.f) :
    D.IsEffective ↔ ∃ E : QuasicoherentDescentData (affineZeroHypercover S).f,
      Nonempty ((pullFunctor (affineOpenRefinementToAffineCover 𝒰 h𝒰)).obj E ≅
        (pullFunctor (affineOpenRefinementToFamily 𝒰 h𝒰)).obj D) :=
  ⟨exists_iso_pullFunctor_affineOpenRefinement_of_isEffective 𝒰 h𝒰,
    fun ⟨E, ⟨e⟩⟩ ↦ isEffective_of_iso_pullFunctor_affineOpenRefinement 𝒰 h𝒰 D E e⟩

include h𝒰 in
/-- **The components of the missing datum, and of the missing isomorphism, exist
unconditionally.**  For every member `U a` of the affine open covering of the base there is a
quasi-coherent module on `U a` whose canonical descent datum relative to the base change of `𝒰`
to `U a` is isomorphic to the restriction of `D` there.

This is `…isEffective_pullFunctor_homOverPullback₁` read as an existence statement.  The members
of the base-changed family are the members `pullback (U a ⟶ S) (X i ⟶ S)` of the affine-open
refinement above `a`, so these modules are the components of the datum `E` that
`isEffective_iff_exists_iso_pullFunctor_affineOpenRefinement` asks for, and the components of
these isomorphisms are the components of the isomorphism it asks for.  What is missing is
therefore neither a sheaf nor a componentwise comparison, but the transition isomorphisms of `E`
and their cocycle condition. -/
public theorem exists_iso_canonicalDescentFunctor_affineOpen
    (D : QuasicoherentDescentData 𝒰.f) (a : S.affineCover.I₀) :
    ∃ M : (SheafOfModules.isQuasicoherent (S.affineCover.X a).ringCatSheaf).FullSubcategory,
      Nonempty ((canonicalDescentFunctor (𝒰.pullback₁ (S.affineCover.f a)).f).obj M ≅
        (pullFunctor (homOverPullback₁ 𝒰 (S.affineCover.f a))).obj D) :=
  isEffective_pullFunctor_homOverPullback₁ 𝒰 h𝒰 (S.affineCover.f a) D

/-! ### The chain to the effectivity half of Stacks 023T -/

/-- **What the gluing of Stacks 023T still needs**: for every fpqc covering family of every
scheme and every quasi-coherent descent datum for it, a quasi-coherent descent datum on the
affine open covering of the base whose restriction to the affine-open refinement is isomorphic to
its own.

Its components are supplied by `exists_iso_canonicalDescentFunctor_affineOpen`, and
`zariskiDescentDatumOverAffineCover_iff` shows it is equivalent to the effectivity half of Stacks
023T, so nothing is being smuggled in. -/
public abbrev ZariskiDescentDatumOverAffineCover : Prop :=
  ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) (D : QuasicoherentDescentData 𝒰.f),
      ∃ E : QuasicoherentDescentData (affineZeroHypercover S).f,
        Nonempty ((pullFunctor (affineOpenRefinementToAffineCover 𝒰 h𝒰)).obj E ≅
          (pullFunctor (affineOpenRefinementToFamily 𝒰 h𝒰)).obj D)

/-- **The effectivity half of [Stacks, Tag 023T] over the Zariski descent datum alone**, for an
arbitrary fpqc covering family of an arbitrary scheme at an arbitrary index universe. -/
public theorem isEffective_fpqcPrecoverage_of_zariskiDatum
    (h : ZariskiDescentDatumOverAffineCover.{v, u}) {S : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{v} S) (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  (isEffective_iff_exists_iso_pullFunctor_affineOpenRefinement 𝒰 h𝒰 D).2 (h 𝒰 h𝒰 D)

/-- **The Zariski locality `EffectiveGluesOverAffineOpens`, over the Zariski descent datum
alone.** -/
public theorem effectiveGluesOverAffineOpens_of_zariskiDatum
    (h : ZariskiDescentDatumOverAffineCover.{v, u}) : EffectiveGluesOverAffineOpens.{v, u} :=
  effectiveGluesOverAffineOpens_of_forall
    fun 𝒰 h𝒰 D ↦ isEffective_fpqcPrecoverage_of_zariskiDatum h 𝒰 h𝒰 D

/-- **`EffectiveSigmaFamilyOverAnyBase`, over the Zariski descent datum alone.** -/
public theorem effectiveSigmaFamilyOverAnyBase_of_zariskiDatum
    (h : ZariskiDescentDatumOverAffineCover.{u, u}) : EffectiveSigmaFamilyOverAnyBase.{u} :=
  effectiveSigmaFamilyOverAnyBase_of_glues (effectiveGluesOverAffineOpens_of_zariskiDatum h)

/-- **The remaining statement is exactly the effectivity half of [Stacks, Tag 023T]**, so it is a
reformulation of what is missing and neither a weakening nor a strengthening of it.

The forward implication is `isEffective_fpqcPrecoverage_of_zariskiDatum`; the backward one is
`exists_iso_pullFunctor_affineOpenRefinement_of_isEffective`, which needs no hypothesis. -/
public theorem zariskiDescentDatumOverAffineCover_iff :
    ZariskiDescentDatumOverAffineCover.{v, u} ↔
      ∀ {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S),
        𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
          ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective := by
  constructor
  · intro h S 𝒱 h𝒱 D
    exact isEffective_fpqcPrecoverage_of_zariskiDatum h 𝒱 h𝒱 D
  · intro h S 𝒱 h𝒱 D
    exact exists_iso_pullFunctor_affineOpenRefinement_of_isEffective 𝒱 h𝒱 (h 𝒱 h𝒱 D)

end QuasicoherentDescentData

end AlgebraicGeometry

end
