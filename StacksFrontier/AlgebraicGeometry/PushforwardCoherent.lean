module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent.Affine

/-!
# The direct image of a coherent module along a finite morphism is coherent

Let `f : X ⟶ Y` be a finite morphism of schemes with `Y` locally Noetherian, and let `F` be a
coherent `𝒪_X`-module. This file proves that `f_* F` is a coherent `𝒪_Y`-module, which is the
second assertion of [Stacks, Tag 01Y6]. The first assertion, vanishing of the higher direct
images, is proved separately as
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite`
(`@[stacks 01Y6 "the higher direct images vanish"]`).

By [Stacks, Tag 01XZ] — proved as
`Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType` —
coherence on a locally Noetherian scheme is quasi-coherence together with finite type, so the
statement splits into two halves:

* *quasi-coherence* of `f_* F`, which holds for an arbitrary **affine** morphism and is already
  proved as
  `Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`
  ([Stacks, Tag 02KG]); a finite morphism is affine by definition, so nothing is needed here;
* *finite type* of `f_* F`, which is proved here and which genuinely needs `f` finite rather
  than merely affine. For `f : 𝔸¹_k ⟶ Spec k` the module `f_* 𝒪_{𝔸¹}` is the `k`-module `k[x]`,
  which is quasi-coherent but not of finite type.

The proof of the finite-type half is the source's. Finite type is local on `Y`, and over an
affine open `V = Spec A` of `Y` the preimage is an affine `Spec B` with `A → B` finite; there
`F` is `M^~` for a finite `B`-module `M`, the direct image is the same module read over `A`, and
a finite module over a finite `A`-algebra is a finite `A`-module ([Stacks, Tag 00GJ]). The
affine-open step is `StacksFrontier/AlgebraicGeometry/PushforwardCoherent/Affine.lean`; this file
is the local-to-global glue.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteType_pushforward_of_isFinite`: **the
  direct image of a quasi-coherent module of finite type along a finite morphism is of finite
  type.** No Noetherian hypothesis.
* `Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite`:
  the coherence assertion of [Stacks, Tag 01Y6], for the coherence predicate of
  Stacks Tag 01BW, and `stacksPushforward_isCoherent_of_isFinite` for the
  other coherence predicate of this branch. The tag itself is carried on
  `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`.
* `Stacks.AlgebraicGeometry.PushforwardCoherent.isCoherent_higherDirectImage_of_isFinite`:
  **[Stacks, Tag 02O5] for a finite morphism with locally Noetherian target**, with every
  hypothesis of
  `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_higherDirectImage_of_isAffineHom`
  discharged.
* `Stacks.AlgebraicGeometry.PushforwardCoherent.isFiniteTildeOn_of_isFiniteType_restrict`: a
  quasi-coherent module whose restriction to an affine open is of finite type satisfies
  condition (4) of [Stacks, Tag 01XZ] at that open. This is the local criterion the main proof
  feeds its affine computation into.

## Implementation notes

**No `@[stacks 01Y6]` tag is placed here.** The vanishing half of the tag is tagged elsewhere.

**The predicate is written `_root_.SheafOfModules.IsCoherent` throughout, and that is not
cosmetic**: the library carries two distinct coherence constants with identical fields, and
inside the `Stacks.` namespace both the unqualified name and the dot notation resolve to the
other one, with no error anywhere. The statement proved for the second constant goes through the
bridge `Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent`. See the implementation
notes of `StacksFrontier/AlgebraicGeometry/ProperMapping/CoherenceClosure.lean`.

Finite type of `f_* F` is first established after restriction to an affine open `V` of `Y`,
using that restriction to `V` commutes with the direct image
(`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`), and is then returned to a
statement about `f_* F` itself through condition (4) of [Stacks, Tag 01XZ]: on `V` the module is
the `tilde` of its global sections, so a *global* finite generating family is available, which
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn` glues. Going
through condition (4) rather than directly through a locality statement for finite type is what
makes the gluing possible: finite type of the restrictions alone provides generators only after
passing to a further cover.

`HasDerivedCategory.standard` is made a local instance, as it is in
`StacksFrontier/AlgebraicGeometry/CoherentOfFiniteType.lean`: the statement of
`isCoherent_higherDirectImage_of_isFinite` must name the same derived category as the theorem
whose hypotheses it discharges. Nothing else in this file mentions a derived category.

Several instance arguments are passed positionally. The reason is the one recorded in
`StacksFrontier/AlgebraicGeometry/CoherentOfFiniteType.lean`: `AlgebraicGeometry.Scheme.Modules` is
a `def` for `SheafOfModules _`, so a lemma stated for a general site, applied to `X.Modules`,
asks for its `IsFiniteType` instance at the `SheafOfModules _` spelling while the hypothesis in
context carries the `X.Modules` one. The two are definitionally equal, so passing the term
works; synthesis does not see through the `def`.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 00GJ](https://stacks.math.columbia.edu/tag/00GJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.PushforwardCoherent

variable {X Y : Scheme.{u}}

/-! ### The local criterion -/

/-- **A quasi-coherent module whose restriction to an affine open `V` is of finite type satisfies
condition (4) of [Stacks, Tag 01XZ] at `V`**: it is there the `tilde` of a finite module. Read on
`Spec Γ(Y, V)` the module is the `tilde` of its global sections, and finite type of a `tilde` is
finiteness of the module. -/
theorem isFiniteTildeOn_of_isFiniteType_restrict (G : Y.Modules) [G.IsQuasicoherent]
    (V : Y.Opens) (hV : IsAffineOpen V) (h : (G.restrict V.ι).IsFiniteType) :
    CoherentTFAE.IsFiniteTildeOn G V hV :=
  have : (CoherentTFAE.specRestrict G hV).IsFiniteType :=
    CoherentTFAE.isFiniteType_restrict hV.isoSpec.inv (G.restrict V.ι)
  have : (CoherentTFAE.specRestrict G hV).IsQuasicoherent := inferInstance
  CoherentTFAE.isFiniteTildeOn_of_finite_specModule G V hV
    (finite_moduleSpecΓ (CoherentTFAE.specRestrict G hV))

/-! ### Finite type of the direct image -/

/-- **The direct image of a quasi-coherent module of finite type along a finite morphism is of
finite type.** This is the half of [Stacks, Tag 01Y6] that is not already covered by
quasi-coherence of the direct image along an affine morphism. No Noetherian hypothesis is
needed, and the hypothesis that `f` is finite rather than merely affine is essential. -/
theorem isFiniteType_pushforward_of_isFinite (f : X ⟶ Y) [IsFinite f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj F).IsFiniteType := by
  refine CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn _
    (fun V : Y.affineOpens ↦ (V : Y.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top Y))
    (fun V ↦ V.2) fun V ↦ ?_
  obtain ⟨V, hV⟩ := V
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := IsAffineHom.isAffine_preimage V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hW
  have : IsAffine V.toScheme := hV
  -- Over the affine open `V` the morphism `f ∣_ V` is a finite morphism of affine schemes.
  have hfin : ((f ∣_ V).appTop).hom.Finite :=
    IsFinite.finite_app (f ∣_ V) ⊤ (isAffineOpen_top V.toScheme)
  have hFr : (F.restrict (f ⁻¹ᵁ V).ι).IsFiniteType :=
    CoherentTFAE.isFiniteType_restrict (f ⁻¹ᵁ V).ι F
  have hpush :=
    isFiniteType_pushforward_of_isAffine (f ∣_ V) hfin (F.restrict (f ⁻¹ᵁ V).ι)
  -- Restriction to `V` commutes with the direct image.
  have hres : (((Scheme.Modules.pushforward f).obj F).restrict V.ι).IsFiniteType :=
    @Stacks.SheafOfModules.isFiniteType_of_iso.{u} _ _ _ _ _ _ _ _ _
      ((AffinePushforward.restrictPushforwardIso f V).app F).symm hpush
  exact isFiniteTildeOn_of_isFiniteType_restrict _ V hV hres

/-! ### Coherence of the direct image: Stacks 01Y6 -/

/-- **[Stacks, Tag 01Y6], coherence of the direct image.** The direct image of a coherent
quasi-coherent module along a finite morphism to a locally Noetherian scheme is coherent.

The source states two assertions — `R^p f_* F = 0` for `p > 0`, and `f_* F` coherent when `F` is
(coherent.tex:2502). Both halves of the tag are carried on
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite` and
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite`; this
instance is the same coherence statement, kept for its many consumers but not tagged. -/
instance pushforward_isCoherent_of_isFinite (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (F : X.Modules) [F.IsQuasicoherent] [hF : _root_.SheafOfModules.IsCoherent F] :
    _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F) :=
  have : F.IsFiniteType := @_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ F hF
  have : ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
    isFiniteType_pushforward_of_isFinite f F
  CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **[Stacks, Tag 01Y6], coherence of the direct image** for the second coherence predicate of
the library, through the bridge
`Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent`. -/
theorem stacksPushforward_isCoherent_of_isFinite [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [IsFinite f] (F : X.Modules) [F.IsQuasicoherent]
    (hF : _root_.SheafOfModules.IsCoherent F) :
    Stacks.SheafOfModules.IsCoherent ((Scheme.Modules.pushforward f).obj F) :=
  ProperMapping.stacksIsCoherent (pushforward_isCoherent_of_isFinite f F)

/-! ### The finite case of the proper mapping theorem -/

/-- **[Stacks, Tag 02O5] for a finite morphism with locally Noetherian target.** Every
hypothesis of
`Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_higherDirectImage_of_isAffineHom` is
discharged: a finite morphism is affine, and the direct image of a coherent module along it is
quasi-coherent and of finite type. -/
theorem isCoherent_higherDirectImage_of_isFinite [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [IsFinite f] (F : X.Modules) [F.IsQuasicoherent]
    (hF : _root_.SheafOfModules.IsCoherent F) (p : ℤ) :
    _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  have : ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
    @_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ _ (pushforward_isCoherent_of_isFinite f F)
  CoherentOfFiniteType.isCoherent_higherDirectImage_of_isAffineHom f F hF p

end Stacks.AlgebraicGeometry.PushforwardCoherent

end
