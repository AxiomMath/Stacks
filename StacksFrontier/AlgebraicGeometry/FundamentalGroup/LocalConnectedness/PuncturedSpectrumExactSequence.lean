module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrum
import all StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrum

/-!
# The local exact sequence of a punctured spectrum

Let `(A, 𝔪)` be a local ring, let `X = Spec A` and let `U = X ∖ {𝔪}` be the punctured spectrum.
Let `Aˢʰ` be a strict henselization of `A` and let `Uˢʰ` be its punctured spectrum, which is the
preimage of `U` under `Spec Aˢʰ ⟶ Spec A`. Assuming `Uˢʰ` connected, this file proves two of the
three assertions of Stacks Tag 0BSB about

```
π₁(Uˢʰ, ū) → π₁(U, ū) → π₁(X, ū) → 1
```

namely the surjectivity of `π₁(U) → π₁(X)` and the triviality of the composite. The third
assertion — that the kernel of `π₁(U) → π₁(X)` is the smallest closed normal subgroup containing
the image of `π₁(Uˢʰ)` — is reduced here to one statement about descent, which is *not* proved in
this module; see "The descent half". It is proved downstream, so the tag is covered.

## Main results

* `AlgebraicGeometry.connectedSpace_puncturedSpectrum_of_isStrictHenselization` — the
  connectedness of `U` implicit in the statement of Stacks 0BSB, since `π₁(U, ū)` appears in it.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_puncturedSpectrum` — **the surjectivity
  `π₁(U) → π₁(X) → 1` of Stacks 0BSB.**
* `AlgebraicGeometry.etaleFundamentalGroupMap_comp_eq_one_puncturedSpectrum` — **the triviality
  of the composite `π₁(Uˢʰ) → π₁(U) → π₁(X)` of Stacks 0BSB.**
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum` — the full
  exactness, conditional on the descent statement that is the remaining content of the tag.

## How the two proved assertions go

Surjectivity is Stacks 0BN6: it is equivalent to full faithfulness of
`FÉt_X ⥤ FÉt_U`, which is Stacks 0BLQ, available here as
`AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum` under exactly the
connectedness hypothesis on `Uˢʰ` that Stacks 0BSB assumes.

Triviality of the composite is Stacks 0BS8: it is equivalent to the composite functor
`FÉt_X ⥤ FÉt_U ⥤ FÉt_{Uˢʰ}` landing in finite coproducts of copies of `Uˢʰ`. Since
`Uˢʰ ⟶ U ⟶ X` and `Uˢʰ ⟶ Spec Aˢʰ ⟶ X` are the same morphism, that composite is also base
change along `Spec Aˢʰ ⟶ X` followed by base change along `Uˢʰ ⟶ Spec Aˢʰ`; the first step
already lands in finite coproducts of copies of `Spec Aˢʰ` because `Aˢʰ` is strictly henselian,
and the second is exact, hence preserves them.

## The descent half

Exactness at `π₁(U)` is reduced by
`AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum` to a single
obligation: a finite étale cover of `U` whose base change to `Uˢʰ` is a finite coproduct of
copies of `Uˢʰ` lies in the essential image of `FÉt_X ⥤ FÉt_U`. That is the descent half of the
source's proof, and it is the place where the quasi-compactness of `U` is used: the source
builds the cover over `X` by fpqc descent along `Spec Aˢʰ ⟶ X` (Stacks 0245, 02W0, 02VN, 02LA),
and the descent datum is transported from `Uˢʰ` to `Spec Aˢʰ` by applying Stacks 0BSA to the
quasi-compact open immersions `Uˢʰ ×_U Uˢʰ ⊆ Spec Aˢʰ ×_X Spec Aˢʰ` and its triple analogue.

That obligation is a hypothesis of every declaration **in this module**, which needs none of the
fpqc descent machinery and therefore imports none of it. It is **proved**, from exactly the
hypotheses of the tag, in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent`,
which imports this module: the descent half itself is
`AlgebraicGeometry.essImage_finiteEtaleBaseChange_puncturedSpectrum` and the resulting
unconditional exact sequence, which is where the `@[stacks 0BSB]` attribute for the whole tag
sits, is
`AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum_of_quasiCompact`.
So the "no `@[stacks 0BSB]`" notes below are statements about the declarations they are attached
to, not about the state of the tag.

## Implementation notes

The punctured spectrum of `Aˢʰ` is presented as
`Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ Stacks.Divisors.puncturedSpectrum A`, the
preimage of the punctured spectrum of `A`, rather than as
`Stacks.Divisors.puncturedSpectrum Ash`. The two are equal
(`AlgebraicGeometry.preimage_puncturedSpectrum_of_isStrictHenselization`), but the preimage form
is the one that comes with the morphism `Uˢʰ ⟶ U` of the source, namely the restriction
`Spec.map _ ∣_ Stacks.Divisors.puncturedSpectrum A`; the morphism out of
`Stacks.Divisors.puncturedSpectrum Ash` would only exist after transporting along that equality.

The connectedness hypothesis is `IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash))`, the
form in which the siblings in this directory state it.

**No declaration below assumes `QuasiCompact (Stacks.Divisors.puncturedSpectrum A).ι`**, the
retrocompactness of `U` that Stacks 0BSB assumes. The two assertions proved here do not need it,
so they are stated without it and hold in that greater generality; in the conditional statement
it is subsumed by the hypothesis `hdescent`, which is the only step of the source's proof that
uses it.

`AlgebraicGeometry.preimage_puncturedSpectrum` is `private` in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/LocalConnectedness/PuncturedSpectrum.lean`, so
that module is also imported with `import all` rather than having its proof repeated here.

Every geometric point below is a geometric point of `Uˢʰ`; its images in `U` and in `X` are the
compatible base points `ū` of the source.

## References

* [Stacks Project, Tag 0BSB](https://stacks.math.columbia.edu/tag/0BSB)
* [Stacks Project, Tag 0BLQ](https://stacks.math.columbia.edu/tag/0BLQ)
* [Stacks Project, Tag 0BN6](https://stacks.math.columbia.edu/tag/0BN6)
* [Stacks Project, Tag 0BS8](https://stacks.math.columbia.edu/tag/0BS8)
* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
* [Stacks Project, Tag 0BSA](https://stacks.math.columbia.edu/tag/0BSA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.Divisors
open Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] [IsLocalRing A]
  (κsep : Type u) [Field κsep] [Algebra (maximalIdeal A).ResidueField κsep]
  [IsSepClosure (maximalIdeal A).ResidueField κsep]
  (Ash : Type u) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]

/-- **A strict henselization is faithfully flat, so its spectrum covers.** Flatness is property
(2) of `Stacks.StrictHenselization.IsStrictHenselization`, and a flat local homomorphism of local
rings is faithfully flat. -/
@[ega "IV 18.8.8", sga "4 VIII 4.4"]
theorem flat_and_surjective_specMap_algebraMap_of_isStrictHenselization
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap A Ash))) := by
  let : Module.Flat A Ash := hAsh.flat
  let : IsLocalHom (algebraMap A Ash) := hAsh.isLocalHom
  let : Module.FaithfullyFlat A Ash := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

/-- **The punctured spectrum of a strict henselization is the preimage of the punctured
spectrum.** The structure map `A → Aˢʰ` is local and generates the maximal ideal of `Aˢʰ` from
that of `A`, so a point of `Spec Aˢʰ` is the closed point exactly when its image is. -/
theorem preimage_puncturedSpectrum_of_isStrictHenselization
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash) :
    Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A =
      puncturedSpectrum Ash := by
  let : IsLocalHom (algebraMap A Ash) := hAsh.isLocalHom
  exact preimage_puncturedSpectrum (algebraMap A Ash) hAsh.maximalIdeal_map

/-- **The punctured spectrum of a strict henselization is connected**, as an open subscheme of
`Spec Aˢʰ` presented as the preimage of the punctured spectrum of `A`. This is the hypothesis of
Stacks 0BSB on `Uˢʰ`, read through
`AlgebraicGeometry.preimage_puncturedSpectrum_of_isStrictHenselization`. -/
theorem connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash))) :
    ConnectedSpace
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A) := by
  rw [preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh]
  exact isConnected_iff_connectedSpace.mp hconnected

/-- **Connectedness of `U` in Stacks Project, Tag 0BSB.** The punctured spectrum of `A` is
connected as soon as the punctured spectrum of a strict henselization `Aˢʰ` is: the latter is the
preimage of the former under the faithfully flat `Spec Aˢʰ ⟶ Spec A`, so the restriction
`Uˢʰ ⟶ U` is surjective and connectedness transfers along it. This is implicit in the statement
of the tag, since `π₁(U, ū)` appears in it. -/
@[stacks 0BSB "connectedness of `U`, implicit since `π₁(U, ū)` appears in the statement"]
theorem connectedSpace_puncturedSpectrum_of_isStrictHenselization
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash))) :
    ConnectedSpace (puncturedSpectrum A).toScheme := by
  obtain ⟨hflat, hsurj⟩ :=
    flat_and_surjective_specMap_algebraMap_of_isStrictHenselization A κsep Ash hAsh
  let f := Spec.map (CommRingCat.ofHom (algebraMap A Ash))
  let : Flat f := hflat
  let : Surjective f := hsurj
  let : ConnectedSpace (f ⁻¹ᵁ puncturedSpectrum A) :=
    connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
  let : Surjective (f ∣_ puncturedSpectrum A) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f (puncturedSpectrum A)).flip
      inferInstance
  exact (f ∣_ puncturedSpectrum A).surjective.connectedSpace
    (f ∣_ puncturedSpectrum A).continuous

/-- The three connectedness facts about `X`, `U` and `Uˢʰ` used by the fundamental group maps. -/
private theorem connectedSpace_triple_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash))) :
    ConnectedSpace (Spec (.of A)) ∧ ConnectedSpace (puncturedSpectrum A).toScheme ∧
      ConnectedSpace
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A) :=
  ⟨connectedSpace_spec_of_isLocalRing A,
    connectedSpace_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected,
    connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected⟩

/-- **A finite étale cover of `Spec A` splits over the punctured spectrum of a strict
henselization.** The two factorisations `Uˢʰ ⟶ U ⟶ X` and `Uˢʰ ⟶ Spec Aˢʰ ⟶ X` of the same
morphism identify the composite base change with base change along `Spec Aˢʰ ⟶ X` followed by
base change along the open immersion `Uˢʰ ⟶ Spec Aˢʰ`. The first step lands in finite coproducts
of copies of `Spec Aˢʰ` because `Aˢʰ` is strictly henselian, and the second preserves them
because base change along a morphism of connected schemes is exact. -/
theorem isFiniteCoproductOfTerminal_finiteEtaleBaseChange_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (w : GeometricPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).toScheme)
    (Y : FiniteEtaleOver (Spec (.of A))) :
    IsFiniteCoproductOfTerminal
      ((finiteEtaleBaseChange
          (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)).obj
        ((finiteEtaleBaseChange (puncturedSpectrum A).ι).obj Y)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A Ash))
  let U := puncturedSpectrum A
  let V := f ⁻¹ᵁ U
  let : ConnectedSpace (Spec (.of Ash)) := connectedSpace_spec_of_isLocalRing Ash
  obtain ⟨_, _, _⟩ := connectedSpace_triple_puncturedSpectrum A κsep Ash hAsh hconnected
  let e₁ : finiteEtaleBaseChange ((f ∣_ U) ≫ U.ι) ≅
      finiteEtaleBaseChange U.ι ⋙ finiteEtaleBaseChange (f ∣_ U) :=
    MorphismProperty.Over.pullbackComp (f ∣_ U) U.ι
  let e₂ : finiteEtaleBaseChange ((f ∣_ U) ≫ U.ι) ≅
      finiteEtaleBaseChange f ⋙ finiteEtaleBaseChange V.ι :=
    MorphismProperty.Over.pullbackComp V.ι f ((f ∣_ U) ≫ U.ι) (morphismRestrict_ι f U)
  let : HenselianLocalRing Ash := hAsh.henselian
  let : IsSepClosed (maximalIdeal Ash).ResidueField := hAsh.sepClosed
  let : IsSepClosed (ResidueField Ash) := isSepClosed_residueField_of_maximalIdeal Ash
  have hsplit : IsFiniteCoproductOfTerminal ((finiteEtaleBaseChange f).obj Y) :=
    isFiniteCoproductOfTerminal_of_henselian_isSepClosed Ash _
  have : PreservesFiniteLimits (finiteEtaleBaseChange V.ι) :=
    (exactFunctor_finiteEtaleBaseChange V.ι w).1
  have : PreservesFiniteColimits (finiteEtaleBaseChange V.ι) :=
    (exactFunctor_finiteEtaleBaseChange V.ι w).2
  exact isFiniteCoproductOfTerminal_of_iso ((e₂.symm ≪≫ e₁).app Y)
    (isFiniteCoproductOfTerminal_map (finiteEtaleBaseChange V.ι) hsplit)

/-- **Triviality of the composite in Stacks Project, Tag 0BSB.** Let `(A, 𝔪)` be a local ring,
`X = Spec A`, `U = X ∖ {𝔪}` the punctured spectrum, `Aˢʰ` a strict henselization of `A` and
`Uˢʰ` its punctured spectrum, presented as the preimage of `U`. If `Uˢʰ` is connected then the
composite

```
π₁(Uˢʰ, ū) ⟶ π₁(U, ū) ⟶ π₁(X, ū)
```

is the trivial homomorphism. This is the complex condition of the exact sequence asserted by the
tag; it is Stacks 0BS8 applied to the composite base-change functor, which lands in finite
coproducts of copies of `Uˢʰ` by
`AlgebraicGeometry.isFiniteCoproductOfTerminal_finiteEtaleBaseChange_puncturedSpectrum`.

The quasi-compactness of `U` assumed by the tag is not needed for this assertion; it enters only
the descent half of the source's proof, which is the remaining obligation of
`AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum`. -/
@[stacks 0BSB "triviality of the composite `π₁(Uˢʰ) → π₁(U) → π₁(X)` only"]
theorem etaleFundamentalGroupMap_comp_eq_one_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (w : GeometricPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).toScheme) :
    letI : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
    letI : ConnectedSpace (puncturedSpectrum A).toScheme :=
      connectedSpace_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
    letI : ConnectedSpace
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A) :=
      connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh
        hconnected
    (etaleFundamentalGroupMap (puncturedSpectrum A).ι
          (w.map (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_
            puncturedSpectrum A))).toMonoidHom.comp
        (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)
          w).toMonoidHom = 1 := by
  obtain ⟨_, _, _⟩ := connectedSpace_triple_puncturedSpectrum A κsep Ash hAsh hconnected
  exact etaleFundamentalGroupMap_comp_eq_one_of_isFiniteCoproductOfTerminal _
    (puncturedSpectrum A).ι w
    (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_puncturedSpectrum A κsep Ash hAsh
      hconnected w)

/-- **Surjectivity in Stacks Project, Tag 0BSB.** Let `(A, 𝔪)` be a local ring, `X = Spec A`,
`U = X ∖ {𝔪}` the punctured spectrum, and `Aˢʰ` a strict henselization of `A` whose punctured
spectrum is connected. Then for every geometric point `ū` of `U` the induced homomorphism

```
π₁(U, ū) ⟶ π₁(X, ū)
```

is surjective. This is the criterion of Stacks 0BN6, whose second condition is full faithfulness
of `FÉt_X ⥤ FÉt_U`, which is Stacks 0BLQ
(`AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum`); the transport
between the abstract automorphism groups of that criterion and the étale fundamental groups is
`AlgebraicGeometry.autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom`.

The quasi-compactness of `U` assumed by the tag is not needed for this assertion; it enters only
the descent half of the source's proof, which is the remaining obligation of
`AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum`. -/
@[stacks 0BSB "surjectivity of `π₁(U) → π₁(X)`, the `→ 1` of the sequence, only"]
theorem surjective_etaleFundamentalGroupMap_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (u : GeometricPoint (puncturedSpectrum A).toScheme) :
    letI : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
    letI : ConnectedSpace (puncturedSpectrum A).toScheme :=
      connectedSpace_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
    Function.Surjective (etaleFundamentalGroupMap (puncturedSpectrum A).ι u) := by
  obtain ⟨_, _, _⟩ := connectedSpace_triple_puncturedSpectrum A κsep Ash hAsh hconnected
  let B := Spec (CommRingCat.of A)
  let H := finiteEtaleBaseChange (puncturedSpectrum A).ι
  let F := finiteEtaleFiberFintypeFunctor B (u.map (puncturedSpectrum A).ι)
  let F' := finiteEtaleFiberFintypeFunctor (puncturedSpectrum A).toScheme u
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso (puncturedSpectrum A).ι u
  let d := galoisFunctorDataOfFiberIso F F' H t
  let _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  let _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor _ _
  let star := finiteEtaleOverTerminal B
  let star' := finiteEtaleOverTerminal (puncturedSpectrum A).toScheme
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange (puncturedSpectrum A).ι u
  have : PreservesFiniteLimits H := hH.1
  have hHs : IsTerminal (H.obj star) := hs.isTerminalObj H star
  have hdsurj : Function.Surjective d.hom :=
    ((surjective_inducedHom_tfae F F' H hH t d star star' hs hs' hHs).out 2 1).mp
      (fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum A κsep Ash hAsh hconnected)
  intro ρ
  obtain ⟨σ, hσ⟩ := hdsurj
    ((autMulEquivEtaleFundamentalGroup B (u.map (puncturedSpectrum A).ι)).symm ρ)
  refine ⟨autMulEquivEtaleFundamentalGroup (puncturedSpectrum A).toScheme u σ, ?_⟩
  rw [← autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom (puncturedSpectrum A).ι u d σ, hσ]
  exact (autMulEquivEtaleFundamentalGroup B
    (u.map (puncturedSpectrum A).ι)).apply_symm_apply ρ

/-- **The local exact sequence of a punctured spectrum, conditionally on descent.** Let `(A, 𝔪)`
be a local ring, `X = Spec A`, `U = X ∖ {𝔪}` the punctured spectrum, `Aˢʰ` a strict henselization
of `A` with connected punctured spectrum `Uˢʰ`, and `ū` a geometric point of `Uˢʰ`. If every
finite étale cover of `U` whose base change to `Uˢʰ` is a finite coproduct of copies of `Uˢʰ` is
the restriction of a finite étale cover of `X`, then

```
π₁(Uˢʰ, ū) → π₁(U, ū) → π₁(X, ū) → 1
```

is exact in the sense of Stacks 0BS9 part (1), i.e. `Stacks.FundamentalGroup.IsExactSequence`.

This is Stacks 0BS9 for the two base-change functors: its second condition is full faithfulness
of `FÉt_X ⥤ FÉt_U`, which is Stacks 0BLQ, together with the description of the essential image of
that functor, whose easy half is
`AlgebraicGeometry.isFiniteCoproductOfTerminal_finiteEtaleBaseChange_puncturedSpectrum` and whose
other half is the hypothesis `hdescent`. **No `@[stacks 0BSB]` attribute is placed on this
declaration**: `hdescent` is the descent half of the source's proof, and it is also where the
quasi-compactness of `U` assumed by the tag is used, so a declaration assuming it does not
discharge the tag. -/
theorem isExactSequence_etaleFundamentalGroupMap_puncturedSpectrum
    (hAsh : Stacks.StrictHenselization.IsStrictHenselization A κsep Ash)
    (hconnected : _root_.IsConnected ({closedPoint Ash}ᶜ : Set (PrimeSpectrum Ash)))
    (w : GeometricPoint
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A).toScheme)
    (hdescent : ∀ V : FiniteEtaleOver (puncturedSpectrum A).toScheme,
      IsFiniteCoproductOfTerminal
          ((finiteEtaleBaseChange
            (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)).obj V) →
        (finiteEtaleBaseChange (puncturedSpectrum A).ι).essImage V) :
    letI : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
    letI : ConnectedSpace (puncturedSpectrum A).toScheme :=
      connectedSpace_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh hconnected
    letI : ConnectedSpace
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ⁻¹ᵁ puncturedSpectrum A) :=
      connectedSpace_preimage_puncturedSpectrum_of_isStrictHenselization A κsep Ash hAsh
        hconnected
    IsExactSequence
      (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A) w)
      (etaleFundamentalGroupMap (puncturedSpectrum A).ι
        (w.map (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A))) := by
  obtain ⟨_, _, _⟩ := connectedSpace_triple_puncturedSpectrum A κsep Ash hAsh hconnected
  refine isExactSequence_etaleFundamentalGroupMap _ (puncturedSpectrum A).ι w
    (fullyFaithful_finiteEtaleBaseChange_to_puncturedSpectrum A κsep Ash hAsh hconnected)
    (fun V ↦ ⟨fun hV ↦ ?_, hdescent V⟩)
  obtain ⟨Y, ⟨e⟩⟩ := hV
  exact isFiniteCoproductOfTerminal_of_iso
    ((finiteEtaleBaseChange
      (Spec.map (CommRingCat.ofHom (algebraMap A Ash)) ∣_ puncturedSpectrum A)).mapIso e)
    (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_puncturedSpectrum A κsep Ash hAsh
      hconnected w Y)

end AlgebraicGeometry

end
