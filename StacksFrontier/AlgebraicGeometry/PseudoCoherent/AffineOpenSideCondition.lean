module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StandardOpenSideCondition
public import StacksFrontier.Homology.RelativePseudoCoherentPolynomial

/-!
# The side condition of Stacks 09VA at an affine space over an arbitrary affine open

`StacksFrontier/AlgebraicGeometry/PseudoCoherent/StandardOpenSideCondition.lean` discharges the
side condition of Stacks 09VA at an affine space `𝔸ⁿ_V` over an affine base `S` only when `V` is
a *standard* open `S_b`, because there `Γ(𝔸ⁿ_V, ⊤) = Γ(S, ⊤)[y₁, …, yₙ]_b` is a localization away
of a polynomial ring. That is why Stacks 09VD,
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict`, carries the
hypothesis that `V` is a standard open.

The hypothesis is removable, and the reason is not a localization: for *any* affine open `V` of
an affine `S` the ring map `Γ(S, ⊤) ⟶ Γ(V, ⊤)` is pseudo-coherent, because an open immersion is,
and Stacks 067D then says that adjoining variables to a relatively pseudo-coherent algebra keeps
it relatively pseudo-coherent. So `Γ(𝔸ⁿ_V, ⊤) = Γ(V, ⊤)[y₁, …, yₙ]` is pseudo-coherent relative
to `Γ(S, ⊤)` even though it is no localization of `Γ(S, ⊤)[y₁, …, yₙ]`. Nothing about standard
opens is needed, and the same argument runs with the open immersion `V ⟶ S` replaced by any
pseudo-coherent morphism, which is the form Stacks 09UT consumes.

## Main results

* `AlgebraicGeometry.pseudoCoherent_of_isOpenImmersion`: an open immersion is pseudo-coherent.
* `pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative` (in the namespace
  `AlgebraicGeometry.Scheme.Modules`): the side condition of Stacks 09VA at `𝔸ⁿ_V ⟶ W` for affine
  `V` and `W`, granted that `Γ(V, ⊤)` is pseudo-coherent relative to `Γ(W, ⊤)` as a module over
  itself.
* `pushforwardStructureSheafPseudoCoherentOver_affineSpace_affineOpen`: that side condition at an
  arbitrary affine open `V` of an affine `S`, with nothing assumed. This is the hypothesis `hOS`
  of
  `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen_over`
  that `StandardOpenSideCondition.lean` could discharge only for a standard open.
* `pushforwardStructureSheafPseudoCoherentOver_affineSpace_resLE`: the same side condition over a
  compatible pair of affine opens of a pseudo-coherent morphism.
* `isPseudoCoherentFromAfterPushforward_restrict_affineOpen`:
  **Stacks 09VD with its standard-open hypothesis dropped**, that is, base enlargement of the
  local condition of Stacks 09UI across an arbitrary affine open of the base.

## Implementation notes

**Pseudo-coherence of an open immersion.** `AlgebraicGeometry.PseudoCoherent` is the morphism
property attached to `RingHom.PseudoCoherent`, so Mathlib's
`AlgebraicGeometry.HasRingHomProperty.of_isOpenImmersion` applies as soon as the identity ring
map is pseudo-coherent. That is `Algebra.PseudoCoherent.of_ringEquiv` at the identity
equivalence, so `RingHom.pseudoCoherent_containsIdentities` costs one line and is the whole input.
The accompanying restriction and `resLE` instances are the ones Mathlib declares for
`AlgebraicGeometry.LocallyOfFiniteType`, with the same proofs. The composition instances,
`AlgebraicGeometry.pseudoCoherent_isStableUnderComposition` and
`AlgebraicGeometry.pseudoCoherent_comp` (Stacks 0681), are imported from
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PseudoCoherentMorphism/Composition.lean`.

**Why this unblocks a tagged statement.** The three hypotheses of
`exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen_over` are `hOb`, `hOV` and
`hOS`. The first two are discharged at any affine base by
`AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_basicOpen`; only
`hOS` needed the base to be a standard open. With `hOS` supplied here, the proof of Stacks 09VD
goes through verbatim at an arbitrary affine open, which is
`isPseudoCoherentFromAfterPushforward_restrict_affineOpen` below. That statement, together with
Stacks 09VE
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_standardCover`) and both
halves of Stacks 09VA, is what the outstanding Stacks 09UJ at a general object of the derived
category asks for; see `StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairs.lean`.

**Universe bookkeeping.** `AffineSpace.algEquivMvPolynomialFin` indexes the variables by `Fin n`
while the affine space is indexed by `ULift (Fin n)`, and the transport of relative
pseudo-coherence along it is through `AlgEquiv.restrictScalars`, so the scalar tower
`Γ(W, ⊤) → Γ(V, ⊤) → Γ(𝔸ⁿ_V, ⊤)` has to be exhibited; `halg` is what identifies its lower step
with the map on sections.

## References

* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.3 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 36.57.5 (067D)](https://stacks.math.columbia.edu/tag/067D)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace RingHom

/-- The identity ring map is pseudo-coherent, being an isomorphism. -/
public theorem pseudoCoherent_containsIdentities : ContainsIdentities @PseudoCoherent :=
  fun R _ ↦ pseudoCoherent_algebraMap.mpr (Algebra.PseudoCoherent.of_ringEquiv (RingEquiv.refl R))

end RingHom

namespace AlgebraicGeometry

/-- An open immersion of schemes is pseudo-coherent: `AlgebraicGeometry.PseudoCoherent` is the
morphism property attached to `RingHom.PseudoCoherent`, which holds for identities. -/
public instance (priority := 900) pseudoCoherent_of_isOpenImmersion {X S : Scheme.{u}}
    (f : X ⟶ S) [IsOpenImmersion f] : PseudoCoherent f :=
  HasRingHomProperty.of_isOpenImmersion (Q := @RingHom.PseudoCoherent)
    RingHom.pseudoCoherent_containsIdentities

/-- The restriction of a pseudo-coherent morphism over an open of the target is pseudo-coherent. -/
public instance pseudoCoherent_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    [PseudoCoherent f] : PseudoCoherent (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

/-- The restriction of a pseudo-coherent morphism to a compatible pair of opens is
pseudo-coherent. -/
public instance pseudoCoherent_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [PseudoCoherent f] : PseudoCoherent (f.resLE V U e) := by
  delta Scheme.Hom.resLE
  infer_instance

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-- **The side condition of Stacks 09VA at an affine space over an affine scheme, from relative
pseudo-coherence of the sections.** Let `q : V ⟶ W` be a morphism of affine schemes and suppose
`Γ(V, ⊤)` is pseudo-coherent relative to `Γ(W, ⊤)` as a module over itself. Then for every closed
immersion `p : 𝔸ⁿ_V ⟶ 𝔸ᴺ_W` over `W` the sheaf `p_*𝒪` is pseudo-coherent.

`Γ(𝔸ⁿ_V, ⊤)` is the polynomial ring `Γ(V, ⊤)[y₁, …, yₙ]`
(`AlgebraicGeometry.AffineSpace.algEquivMvPolynomialFin`), which is pseudo-coherent relative to
`Γ(W, ⊤)` by Stacks 067D in the form
`PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_of_relative`; the conclusion is then
`AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_of_relative`. -/
public theorem pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative (n : ℕ)
    {W V : Scheme.{u}} [IsAffine W] [IsAffine V] (q : V ⟶ W) [Algebra Γ(W, ⊤) Γ(V, ⊤)]
    (halg : algebraMap Γ(W, ⊤) Γ(V, ⊤) = q.appTop.hom)
    [Algebra.FiniteType Γ(W, ⊤) Γ(V, ⊤)]
    (hV : PseudoCoherence.IsModuleRelativelyPseudoCoherent (R := Γ(W, ⊤)) (A := Γ(V, ⊤))
      Γ(V, ⊤)) :
    PushforwardStructureSheafPseudoCoherentOver W (AffineSpace (ULift.{u} (Fin n)) V)
      ((AffineSpace.over (ULift.{u} (Fin n)) V).hom ≫ q) := by
  let algVC : Algebra Γ(V, ⊤) Γ(AffineSpace (ULift.{u} (Fin n)) V, ⊤) :=
    ((AffineSpace.over (ULift.{u} (Fin n)) V).hom.appTop).hom.toAlgebra
  have halgVC : algebraMap Γ(V, ⊤) Γ(AffineSpace (ULift.{u} (Fin n)) V, ⊤) =
      ((AffineSpace.over (ULift.{u} (Fin n)) V).hom.appTop).hom := rfl
  let algWC : Algebra Γ(W, ⊤) Γ(AffineSpace (ULift.{u} (Fin n)) V, ⊤) :=
    (((AffineSpace.over (ULift.{u} (Fin n)) V).hom ≫ q).appTop).hom.toAlgebra
  have htow : IsScalarTower Γ(W, ⊤) Γ(V, ⊤) Γ(AffineSpace (ULift.{u} (Fin n)) V, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    show (((AffineSpace.over (ULift.{u} (Fin n)) V).hom ≫ q).appTop).hom = _
    rw [Scheme.Hom.comp_appTop, halg]
    rfl
  have hFTP : Algebra.FiniteType Γ(W, ⊤) (MvPolynomial (Fin n) Γ(V, ⊤)) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType Γ(W, ⊤) Γ(V, ⊤))
      (inferInstance : Algebra.FiniteType Γ(V, ⊤) (MvPolynomial (Fin n) Γ(V, ⊤)))
  have e' := (AffineSpace.algEquivMvPolynomialFin n V halgVC).restrictScalars Γ(W, ⊤)
  have hFTC : Algebra.FiniteType Γ(W, ⊤) Γ(AffineSpace (ULift.{u} (Fin n)) V, ⊤) :=
    Algebra.FiniteType.of_surjective e'.toAlgHom e'.surjective
  exact pushforwardStructureSheafPseudoCoherentOver_of_relative _ rfl
    (PseudoCoherence.isModuleRelativelyPseudoCoherent_of_algEquiv e'
      (PseudoCoherence.isModuleRelativelyPseudoCoherent_mvPolynomial_of_relative n hV))

/-- **The side condition of Stacks 09VA at an affine space over an arbitrary affine open of an
affine base, with nothing assumed.** This is the hypothesis `hOS` of
`AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen_over`,
which `StacksFrontier/AlgebraicGeometry/PseudoCoherent/StandardOpenSideCondition.lean` discharges only
for `V` a standard open of `S`.

The open immersion `V ⟶ S` is pseudo-coherent, so its map on sections `Γ(S, ⊤) ⟶ Γ(V, ⊤)` is a
pseudo-coherent ring map by `AlgebraicGeometry.HasRingHomProperty.appTop`, which is exactly the
hypothesis of `pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative`. -/
public theorem pushforwardStructureSheafPseudoCoherentOver_affineSpace_affineOpen (n : ℕ)
    {S : Scheme.{u}} [IsAffine S] (V : S.affineOpens) :
    PushforwardStructureSheafPseudoCoherentOver S
      (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}))
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι) := by
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have hpc : RingHom.PseudoCoherent (V.1.ι.appTop).hom :=
    HasRingHomProperty.appTop (P := @PseudoCoherent) _ inferInstance
  let alg : Algebra Γ(S, ⊤) Γ((V.1 : Scheme.{u}), ⊤) := (V.1.ι.appTop).hom.toAlgebra
  obtain ⟨hFT, hrel⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp
      (RingHom.pseudoCoherent_algebraMap.mp hpc)
  let _ := hFT
  exact pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative n _ rfl hrel

/-- **The side condition of Stacks 09VA at an affine space over a compatible pair of affine opens
of a pseudo-coherent morphism.** For `g : Y ⟶ S` pseudo-coherent, `V` an affine open of `Y` and
`W` an affine open of `S` with `V ⊆ g ⁻¹ᵁ W`, the sheaf `p_*𝒪` is pseudo-coherent for every closed
immersion `p : 𝔸ⁿ_V ⟶ 𝔸ᴺ_W` over `W`.

Pseudo-coherence of `g` restricts to `g.resLE W V`, whose map on sections is therefore a
pseudo-coherent ring map, and that is the hypothesis of
`pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative`. This is the form the base
change of Stacks 09UT asks for. -/
public theorem pushforwardStructureSheafPseudoCoherentOver_affineSpace_resLE (n : ℕ)
    {Y S : Scheme.{u}} (g : Y ⟶ S) [PseudoCoherent g] (V : Y.affineOpens) (W : S.affineOpens)
    (h : V.1 ≤ g ⁻¹ᵁ W.1) :
    PushforwardStructureSheafPseudoCoherentOver (W.1 : Scheme.{u})
      (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}))
      ((AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ g.resLE W.1 V.1 h) := by
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have hpc : RingHom.PseudoCoherent ((g.resLE W.1 V.1 h).appTop).hom :=
    HasRingHomProperty.appTop (P := @PseudoCoherent) _ inferInstance
  let alg : Algebra Γ((W.1 : Scheme.{u}), ⊤) Γ((V.1 : Scheme.{u}), ⊤) :=
    ((g.resLE W.1 V.1 h).appTop).hom.toAlgebra
  obtain ⟨hFT, hrel⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp
      (RingHom.pseudoCoherent_algebraMap.mp hpc)
  let _ := hFT
  exact pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative n _ rfl hrel

/-- **Stacks 09VD without its standard-open hypothesis.** Let `S` be affine, let `V` be an
arbitrary affine open of `S`, let `X` be affine with `f : X ⟶ V` locally of finite type, let `E`
be an object of `D(𝒪_X)` and let `U` be an affine open of `X`. If the equivalent conditions of
Stacks 09VC hold for the pair `(X ⟶ V, E)`, then they hold for `(U ⟶ S, E|_U)`.

This is `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict` with the
hypothesis `hV` removed: the proof is the same, with the one appeal to
`AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_affineSpace` — the
only step that used `V = S_b` — replaced by
`pushforwardStructureSheafPseudoCoherentOver_affineSpace_affineOpen`. -/
public theorem isPseudoCoherentFromAfterPushforward_restrict_affineOpen {S X : Scheme.{u}}
    [IsAffine S] [IsAffine X] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
    [LocallyOfFiniteType f] [QuasiCompact f] (U : X.affineOpens)
    (E : DerivedCategory X.Modules) (m : ℤ) :
    (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) →
      (∃ (n : ℕ) (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = U.1.ι ≫ f ≫ V.1.ι ∧
            IsPseudoCoherentFromAfterPushforward i
              ((restrictFunctor U.1.ι).mapDerivedCategory.obj E) m) := by
  intro h
  have hUaff : IsAffine (U.1 : Scheme.{u}) := U.2
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  obtain ⟨N, c, hcU, hccov⟩ := exists_fin_basicOpen_le_cover U.1
  have hpre : ∀ j, U.1.ι ⁻¹ᵁ X.basicOpen (c j) =
      (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (c j)) :=
    fun j => Scheme.preimage_basicOpen_top U.1.ι (c j)
  have hcov : (⨆ j, (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (c j))) = ⊤ :=
    (iSup_congr fun j => hpre j).symm.trans hccov
  refine exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen_over
    (U.1.ι ≫ f ≫ V.1.ι)
    (fun K a => pushforwardStructureSheafPseudoCoherentOver_basicOpen K S a) _ m
    (fun j => U.1.ι.appTop (c j))
    ((Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top _).mpr hcov) fun j => ?_
  obtain ⟨k, l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen_over V f
      (fun K a => pushforwardStructureSheafPseudoCoherentOver_basicOpen K _ a)
      (fun k => pushforwardStructureSheafPseudoCoherentOver_affineSpace_affineOpen k V) E m
      (c j) h
  rw [← hpre j]
  refine ⟨k, (Scheme.Opens.isoOfLE (hcU j)).hom ≫ l, inferInstance, ?_,
    isPseudoCoherentFromAfterPushforward_isoOfLE (hcU j) l E m hlpc⟩
  rw [Category.assoc, hlo, ← Category.assoc, ← Category.assoc,
    Scheme.Opens.isoOfLE_hom_ι (hcU j), Category.assoc, Category.assoc]

end Scheme.Modules

end AlgebraicGeometry

end
