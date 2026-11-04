module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineOpenSideCondition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairs

/-!
# Stacks 09UJ, the implication (1) ⟹ (2)

Stacks 09UI defines relative `m`-pseudo-coherence of an object `E` of `D(𝒪_X)` for a morphism
`f : X ⟶ S` locally of finite type by the *existence* of an affine open cover `V` of `S` and, over
each member, an affine open cover `U` of `f ⁻¹ᵁ V i` on which the local condition holds. Stacks
09UJ says that the condition then holds on *every* compatible pair of affine opens
`U ⊆ f ⁻¹ᵁ V`. This file proves that implication, and with the converse
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair` it discharges
`AlgebraicGeometry.AffinePairComparison`.

The argument is the source's. Given a pair `(U, V)` it suffices, by Stacks 09VE, to exhibit a
standard affine open cover of `U` on which the condition holds, hence to find around each point
`u ∈ U` one standard open `U' ⊆ U` with the condition for `(U' ⟶ V, E|_{U'})`. Choose a member
`V i` of the cover of `S` containing `f(u)` and a member `U_{ij}` of the cover of `f ⁻¹ᵁ V i`
containing `u`; shrink `V i` to an affine open `V'' ⊆ V ⊓ V i` around `f(u)` and `U_{ij}` to an
affine open `U' ⊆ U ⊓ U_{ij} ⊓ f ⁻¹ᵁ V''` around `u`. Three moves on the pair condition then carry
the hypothesis at `(U_{ij}, V i)` to the conclusion at `(U', V)`: shrink the source, shrink the
base, enlarge the base.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterSomeImmersion`: the local condition
  of Stacks 09UI for a bare morphism of schemes `g : A ⟶ B` — the existence of a closed immersion
  of `A` into a finite-dimensional affine space over `B` factoring `g` along which the derived
  pushforward is `m`-pseudo-coherent. This is the first of the equivalent conditions of
  Stacks 09VC, named so that the moves below can be stated without the bookkeeping of
  `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_comp` and
  `isPseudoCoherentFromAfterSomeImmersion_of_comp`: the condition is carried **both ways** along a
  pseudo-coherent morphism `p : T' ⟶ T` of affine schemes. The forward direction is the first
  paragraph of Stacks 09VD; the backward direction is Stacks 09VC together with the reverse half
  of Stacks 09VA.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_restrict`: the
  condition passes to an arbitrary affine open of the source. This is Stacks 09VD with the base
  taken to be the whole of the affine scheme it is stated over.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.of_le_source`, `.of_le_base` and
  `.of_base_le`: the three moves on the pair condition.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_forall_mem`: the condition at
  a pair follows from the condition at a standard open around each point of `U`. This is
  Stacks 09VE plus quasi-compactness of `U`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom`:
  **Stacks 09UJ, the implication (1) ⟹ (2).**
* `AlgebraicGeometry.affinePairComparison`: **the equivalence of Stacks 09UJ**, that is,
  `AlgebraicGeometry.AffinePairComparison`, both of whose directions are now proved.

## Implementation notes

**Why shrinking the base is available.** The two directions along `p : T' ⟶ T` share one side
condition: the pushforward of the structure sheaf along a closed immersion `𝔸ⁿ_{T'} ⟶ 𝔸ᴺ_T` over
`T` must be pseudo-coherent. That is
`Scheme.Modules.pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative`,
whose hypothesis is relative pseudo-coherence of `Γ(T', ⊤)` over `Γ(T, ⊤)` — exactly what
pseudo-coherence of `p` provides, through
`AlgebraicGeometry.HasRingHomProperty.appTop` and `RingHom.pseudoCoherent_algebraMap`. For the
inclusion of one affine open of a scheme in another, `AlgebraicGeometry.Scheme.homOfLE`, that
hypothesis holds because an open immersion is pseudo-coherent
(`AlgebraicGeometry.pseudoCoherent_of_isOpenImmersion`); no localization and no standard open is
involved. The side condition carries the compatibility `p ≫ 𝔸ᴺ_T ↘ T = 𝔸ⁿ_{T'} ↘ T' ≫ p`, without
which it is false — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SideCondition.lean`.

**The two spellings of a small open.** The source's `U'` is simultaneously an open of `X`, where
the hypothesis at `U_{ij}` lives, and a standard open of `U`, which is what Stacks 09VE consumes.
Both are needed, and the comparison between restricting `E` to it in one step and in two is
`AlgebraicGeometry.Scheme.Modules.derivedRestrictOfLEObjIso`; the local condition is carried
across by `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE` and by
its converse `isPseudoCoherentFromAfterPushforward_isoOfLE_iff` below. That `U'` can be taken to
be a standard open of `U` and an affine open of `X` at once is
`AlgebraicGeometry.Scheme.Opens.ι_image_basicOpen_topIso_inv`: the basic open of `U` cut out by
`U.topIso.inv r` for `r : Γ(X, U)` has image `X_r` in `X`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-! ### The local condition of Stacks 09UI for a bare morphism -/

/-- The local condition of Stacks 09UI for a morphism `g : A ⟶ B` of schemes: there are a closed
immersion `i` of `A` into a finite-dimensional affine space over `B` with `i` followed by the
structure morphism equal to `g`, and the derived pushforward of `F` along `i` is
`m`-pseudo-coherent.

This is the first of the equivalent conditions of Stacks 09VC for the pair `(g, F)`, written for a
bare morphism rather than for a compatible pair of affine opens as in
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair`. -/
public abbrev IsPseudoCoherentFromAfterSomeImmersion {A B : Scheme.{u}} (g : A ⟶ B)
    (F : DerivedCategory A.Modules) (m : ℤ) : Prop :=
  ∃ (n : ℕ) (i : A ⟶ AffineSpace (ULift.{u} (Fin n)) B),
    IsClosedImmersion i ∧
      i ≫ (AffineSpace.over (ULift.{u} (Fin n)) B).hom = g ∧
        IsPseudoCoherentFromAfterPushforward i F m

/-- **The side condition of Stacks 09VA at an affine space over a pseudo-coherent morphism of
affine schemes.** For `p : T' ⟶ T` pseudo-coherent with `T` and `T'` affine, the pushforward of
the structure sheaf along any closed immersion `𝔸ⁿ_{T'} ⟶ 𝔸ᴺ_T` over `T` is pseudo-coherent.

Pseudo-coherence of `p` says that `Γ(T', ⊤)` is a pseudo-coherent `Γ(T, ⊤)`-algebra
(`AlgebraicGeometry.HasRingHomProperty.appTop` and `RingHom.pseudoCoherent_algebraMap`), which is
the hypothesis of
`pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative`. -/
public theorem pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_pseudoCoherent
    {T' T : Scheme.{u}} [IsAffine T'] [IsAffine T] (p : T' ⟶ T) [PseudoCoherent p] (n : ℕ) :
    PushforwardStructureSheafPseudoCoherentOver T (AffineSpace (ULift.{u} (Fin n)) T')
      ((AffineSpace.over (ULift.{u} (Fin n)) T').hom ≫ p) := by
  have hpc : RingHom.PseudoCoherent (p.appTop).hom :=
    HasRingHomProperty.appTop (P := @PseudoCoherent) _ inferInstance
  let alg : Algebra Γ(T, ⊤) Γ(T', ⊤) := (p.appTop).hom.toAlgebra
  obtain ⟨hFT, hrel⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp
      (RingHom.pseudoCoherent_algebraMap.mp hpc)
  let _ := hFT
  exact pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_relative n p rfl hrel

/-- The structure morphism of an affine space over `T'`, followed by a morphism `p : T' ⟶ T`
locally of finite type, is locally of finite type. -/
private theorem locallyOfFiniteType_affineSpace_over_comp {T' T : Scheme.{u}} (p : T' ⟶ T)
    [LocallyOfFiniteType p] (n : ℕ) :
    LocallyOfFiniteType ((AffineSpace.over (ULift.{u} (Fin n)) T').hom ≫ p) := by
  have : LocallyOfFiniteType ((AffineSpace.over (ULift.{u} (Fin n)) T').hom) := by
    rw [AffineSpace.over_hom_eq]
    infer_instance
  infer_instance

/-- **Enlarging the base of the local condition of Stacks 09UI along a pseudo-coherent morphism of
affine schemes.** This is the first paragraph of the proof of Stacks 09VD: compose the given
closed immersion `A ⟶ 𝔸ⁿ_{T'}` with a closed immersion of `𝔸ⁿ_{T'}` into an affine space over
`T`, which exists because `𝔸ⁿ_{T'} ⟶ T` is a morphism of affine schemes locally of finite type,
and transport `m`-pseudo-coherence along it by the forward half of Stacks 09VA. -/
public theorem isPseudoCoherentFromAfterSomeImmersion_comp {A T' T : Scheme.{u}} [IsAffine T']
    [IsAffine T] (g : A ⟶ T') (p : T' ⟶ T) [PseudoCoherent p] [LocallyOfFiniteType p]
    (F : DerivedCategory A.Modules) (m : ℤ) (h : IsPseudoCoherentFromAfterSomeImmersion g F m) :
    IsPseudoCoherentFromAfterSomeImmersion (g ≫ p) F m := by
  obtain ⟨n, i, hi, hio, hpc⟩ := h
  have := hi
  have := locallyOfFiniteType_affineSpace_over_comp p n
  obtain ⟨N, j, hj, hjo, hjpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_of_comp_over i
      ((AffineSpace.over (ULift.{u} (Fin n)) T').hom ≫ p)
      (pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_pseudoCoherent p n) F m hpc
  exact ⟨N, j, hj, by rw [hjo, ← Category.assoc, hio], hjpc⟩

/-- **Shrinking the base of the local condition of Stacks 09UI along a pseudo-coherent morphism of
affine schemes.** This is the move the proof of Stacks 09UJ needs and that no composition of
forward implications provides.

Choose any closed immersion `d : A ⟶ 𝔸ⁿ_{T'}` over `T'` and any closed immersion
`q : 𝔸ⁿ_{T'} ⟶ 𝔸ᴷ_T` over `T`; both exist because the morphisms in question are morphisms of
affine schemes locally of finite type. Stacks 09VC applied to `g ≫ p` turns the hypothesis into
`m`-pseudo-coherence of the pushforward along the composite `d ≫ q`, and the reverse half of
Stacks 09VA at `q` — whose side condition is
`pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_pseudoCoherent` — strips `q` off
again. -/
public theorem isPseudoCoherentFromAfterSomeImmersion_of_comp {A T' T : Scheme.{u}} [IsAffine A]
    [IsAffine T'] [IsAffine T] (g : A ⟶ T') [LocallyOfFiniteType g] (p : T' ⟶ T)
    [PseudoCoherent p] [LocallyOfFiniteType p] (F : DerivedCategory A.Modules) (m : ℤ)
    (h : IsPseudoCoherentFromAfterSomeImmersion (g ≫ p) F m) :
    IsPseudoCoherentFromAfterSomeImmersion g F m := by
  obtain ⟨n, d, hd, hdo⟩ := exists_isClosedImmersion_affineSpace g
  have := hd
  have := locallyOfFiniteType_affineSpace_over_comp p n
  obtain ⟨K, q, hq, hqo⟩ :=
    exists_isClosedImmersion_affineSpace ((AffineSpace.over (ULift.{u} (Fin n)) T').hom ≫ p)
  have := hq
  have key : IsPseudoCoherentFromAfterPushforward (d ≫ q) F m :=
    (isPseudoCoherentFrom_some_iff_forall_fin (g ≫ p) F m).mp h K _ inferInstance
      (by rw [Category.assoc, hqo, ← Category.assoc, hdo])
  rw [isPseudoCoherentFromAfterPushforward_comp_iff] at key
  refine ⟨n, d, hd, hdo, ?_⟩
  rw [isPseudoCoherentFromAfterPushforward_iff]
  exact isPseudoCoherentFrom_of_pushforward_mapDerivedCategory q
    (pushforwardStructureSheafPseudoCoherentOver_affineSpace_of_pseudoCoherent p n K q hq hqo) m _
    key

/-- Precomposing with `isoOfLE` turns a factorisation through `U.ι` into one through `V.ι`. -/
private theorem isoOfLE_hom_comp_comp_eq {X Y Z : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (i : U.toScheme ⟶ Y) (k : Y ⟶ Z) (g : X ⟶ Z) (hi : i ≫ k = U.ι ≫ g) :
    (Scheme.Opens.isoOfLE h).hom ≫ i ≫ k = (V.ι ⁻¹ᵁ U).ι ≫ V.ι ≫ g := by
  rw [hi, ← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, Category.assoc]

/-- **Stacks 09VD at an arbitrary affine open of the source, over the whole base.** Let `A` and
`T` be affine, let `g : A ⟶ T` be locally of finite type, let `F` be an object of `D(𝒪_A)` and let
`W` be an affine open of `A`. If the equivalent conditions of Stacks 09VC hold for `(g, F)` then
they hold for `(W ⟶ T, F|_W)`.

This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict_affineOpen` with
the affine open of the base taken to be the whole of `T`, proved directly so that no isomorphism
`(⊤ : T.Opens).toScheme ≅ T` has to be carried: cover `W` by the finitely many standard opens
`A_{cⱼ}` of `A` contained in it, apply the standard-open case
`exists_isPseudoCoherentFromAfterPushforward_basicOpen_over` to each, move the conclusion onto the
corresponding standard open of `W` by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE`, and glue with
Stacks 09VE in the form `exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen_over`. -/
public theorem isPseudoCoherentFromAfterSomeImmersion_restrict {T A : Scheme.{u}} [IsAffine T]
    [IsAffine A] (g : A ⟶ T) [LocallyOfFiniteType g] (W : A.affineOpens)
    (F : DerivedCategory A.Modules) (m : ℤ)
    (h : IsPseudoCoherentFromAfterSomeImmersion g F m) :
    IsPseudoCoherentFromAfterSomeImmersion (W.1.ι ≫ g)
      ((restrictFunctor W.1.ι).mapDerivedCategory.obj F) m := by
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  obtain ⟨N, c, hcW, hccov⟩ := exists_fin_basicOpen_le_cover W.1
  have hpre : ∀ j, W.1.ι ⁻¹ᵁ A.basicOpen (c j) =
      (W.1 : Scheme.{u}).basicOpen (W.1.ι.appTop (c j)) :=
    fun j => Scheme.preimage_basicOpen_top W.1.ι (c j)
  have hcov : (⨆ j, (W.1 : Scheme.{u}).basicOpen (W.1.ι.appTop (c j))) = ⊤ :=
    (iSup_congr fun j => hpre j).symm.trans hccov
  refine exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen_over (W.1.ι ≫ g)
    (fun K a => pushforwardStructureSheafPseudoCoherentOver_basicOpen K T a) _ m
    (fun j => W.1.ι.appTop (c j))
    ((Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top _).mpr hcov) fun j => ?_
  obtain ⟨k, l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_basicOpen_over g
      (fun K a => pushforwardStructureSheafPseudoCoherentOver_basicOpen K T a) F m (c j) h
  have := hl
  rw [← hpre j]
  refine ⟨k, (Scheme.Opens.isoOfLE (hcW j)).hom ≫ l, inferInstance, ?_,
    isPseudoCoherentFromAfterPushforward_isoOfLE (hcW j) l F m hlpc⟩
  exact isoOfLE_hom_comp_comp_eq (hcW j) l _ g hlo

/-- **The local condition of Stacks 09UI transported between `W` and `ι_A⁻¹W`, as an `Iff`.** This
is `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE` with its
converse: both directions come from the `Iff`
`isPseudoCoherentFromAfterPushforward_precomp_isIso_iff` together with the comparison
`AlgebraicGeometry.Scheme.Modules.derivedRestrictOfLEObjIso` of the two restrictions. -/
public theorem isPseudoCoherentFromAfterPushforward_isoOfLE_iff {X Y : Scheme.{u}}
    {A W : X.Opens} (h : W ≤ A) (l : W.toScheme ⟶ Y) [IsClosedImmersion l]
    (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward ((Scheme.Opens.isoOfLE h).hom ≫ l)
        ((restrictFunctor (A.ι ⁻¹ᵁ W).ι).mapDerivedCategory.obj
          ((restrictFunctor A.ι).mapDerivedCategory.obj E)) m ↔
      IsPseudoCoherentFromAfterPushforward l
        ((restrictFunctor W.ι).mapDerivedCategory.obj E) m := by
  rw [isPseudoCoherentFromAfterPushforward_precomp_isIso_iff]
  exact isPseudoCoherentFromAfterPushforward_iff_of_iso l (derivedRestrictOfLEObjIso h E) m

end Scheme.Modules

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

/-! ### The three moves on the pair condition -/

/-- **The pair condition of Stacks 09UI passes to a smaller affine open of the source.** This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_restrict` at the affine
open `ι_W⁻¹W'` of `W`, followed by the transport
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE_iff` of the
restricted object from `ι_W⁻¹W'` to `W'`. -/
public theorem IsPseudoCoherentFromOnAffinePair.of_le_source {E : DerivedCategory X.Modules}
    {m : ℤ} {W W' : X.affineOpens} {T : S.affineOpens} (hW : W'.1 ≤ W.1)
    (hWT : W.1 ≤ f ⁻¹ᵁ T.1) (hW'T : W'.1 ≤ f ⁻¹ᵁ T.1)
    (h : f.IsPseudoCoherentFromOnAffinePair E m W T hWT) :
    f.IsPseudoCoherentFromOnAffinePair E m W' T hW'T := by
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have hW'aff : IsAffine (W'.1 : Scheme.{u}) := W'.2
  have hTaff : IsAffine (T.1 : Scheme.{u}) := T.2
  have := locallyOfFiniteType_resLE f T.1 W.1 hWT
  have hpreaff : IsAffine ((W.1.ι ⁻¹ᵁ W'.1 : (W.1 : Scheme.{u}).Opens) : Scheme.{u}) :=
    IsAffine.of_isIso (Scheme.Opens.isoOfLE hW).hom
  obtain ⟨n, i, hi, hio, hpc⟩ :=
    Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_restrict (f.resLE T.1 W.1 hWT)
      ⟨W.1.ι ⁻¹ᵁ W'.1, hpreaff⟩ _ m h
  have := hi
  have hio' : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (T.1 : Scheme.{u})).hom ≫ T.1.ι =
      (W.1.ι ⁻¹ᵁ W'.1).ι ≫ W.1.ι ≫ f := by
    rw [← Category.assoc, hio, Category.assoc, Scheme.Hom.resLE_comp_ι]
  have hkey : (Scheme.Opens.isoOfLE hW).inv ≫ (W.1.ι ⁻¹ᵁ W'.1).ι ≫ W.1.ι = W'.1.ι := by
    rw [← Scheme.Opens.isoOfLE_hom_ι hW, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hid : (Scheme.Opens.isoOfLE hW).hom ≫ ((Scheme.Opens.isoOfLE hW).inv ≫ i) = i := by
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  refine ⟨n, (Scheme.Opens.isoOfLE hW).inv ≫ i, inferInstance, ?_,
    (Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE_iff hW
      ((Scheme.Opens.isoOfLE hW).inv ≫ i) E m).mp
      ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_congr hid.symm _ m).mp hpc)⟩
  rw [← cancel_mono T.1.ι, Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, hio',
    ← hkey, Category.assoc, Category.assoc]

/-- **The pair condition of Stacks 09UI passes to a smaller affine open of the base**, provided
the source still maps into it. This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_of_comp` along the open
immersion `T' ⟶ T`, which is pseudo-coherent by
`AlgebraicGeometry.pseudoCoherent_of_isOpenImmersion`. -/
public theorem IsPseudoCoherentFromOnAffinePair.of_le_base {E : DerivedCategory X.Modules}
    {m : ℤ} {W : X.affineOpens} {T T' : S.affineOpens} (hT : T'.1 ≤ T.1)
    (hWT : W.1 ≤ f ⁻¹ᵁ T.1) (hWT' : W.1 ≤ f ⁻¹ᵁ T'.1)
    (h : f.IsPseudoCoherentFromOnAffinePair E m W T hWT) :
    f.IsPseudoCoherentFromOnAffinePair E m W T' hWT' := by
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have hTaff : IsAffine (T.1 : Scheme.{u}) := T.2
  have hT'aff : IsAffine (T'.1 : Scheme.{u}) := T'.2
  have := locallyOfFiniteType_resLE f T'.1 W.1 hWT'
  have heq : f.resLE T'.1 W.1 hWT' ≫ S.homOfLE hT = f.resLE T.1 W.1 hWT := by
    rw [← cancel_mono T.1.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι]
  refine Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_of_comp
    (f.resLE T'.1 W.1 hWT') (S.homOfLE hT) _ m ?_
  rwa [heq]

/-- **The pair condition of Stacks 09UI passes to a larger affine open of the base.** This is
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_comp` along the open
immersion `T ⟶ T'`, which is pseudo-coherent by
`AlgebraicGeometry.pseudoCoherent_of_isOpenImmersion`; it is the first paragraph of the proof of
Stacks 09VD, with no hypothesis that `T` be a standard open of `T'`. -/
public theorem IsPseudoCoherentFromOnAffinePair.of_base_le {E : DerivedCategory X.Modules}
    {m : ℤ} {W : X.affineOpens} {T T' : S.affineOpens} (hT : T.1 ≤ T'.1)
    (hWT : W.1 ≤ f ⁻¹ᵁ T.1) (hWT' : W.1 ≤ f ⁻¹ᵁ T'.1)
    (h : f.IsPseudoCoherentFromOnAffinePair E m W T hWT) :
    f.IsPseudoCoherentFromOnAffinePair E m W T' hWT' := by
  have hWaff : IsAffine (W.1 : Scheme.{u}) := W.2
  have hTaff : IsAffine (T.1 : Scheme.{u}) := T.2
  have hT'aff : IsAffine (T'.1 : Scheme.{u}) := T'.2
  have heq : f.resLE T.1 W.1 hWT ≫ S.homOfLE hT = f.resLE T'.1 W.1 hWT' := by
    rw [← cancel_mono T'.1.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι]
  have hres := Scheme.Modules.isPseudoCoherentFromAfterSomeImmersion_comp
    (f.resLE T.1 W.1 hWT) (S.homOfLE hT) _ m h
  rwa [heq] at hres

/-! ### Gluing the pair condition from a neighbourhood of each point -/

/-- **The pair condition of Stacks 09UI is local on the source.** If around every point of an
affine open `U` with `U ⊆ f ⁻¹ᵁ V` there is a standard open of `U` on which the local condition of
Stacks 09UI holds over `V`, then it holds on `U` itself.

`U` is a compact space because it is affine, so finitely many of the standard opens already cover
it, and Stacks 09VE
(`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_standardCover`) glues the
conditions at the members of a standard affine open cover into the condition at `U`. -/
public theorem isPseudoCoherentFromOnAffinePair_of_forall_mem {E : DerivedCategory X.Modules}
    {m : ℤ} (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (h : ∀ x : (U.1 : Scheme.{u}), ∃ a : Γ((U.1 : Scheme.{u}), ⊤),
      x ∈ (U.1 : Scheme.{u}).basicOpen a ∧
        Scheme.Modules.IsPseudoCoherentFromAfterSomeImmersion
          (((U.1 : Scheme.{u}).basicOpen a).ι ≫ f.resLE V.1 U.1 hUV)
          ((Scheme.Modules.restrictFunctor
              ((U.1 : Scheme.{u}).basicOpen a).ι).mapDerivedCategory.obj
            ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E)) m) :
    f.IsPseudoCoherentFromOnAffinePair E m U V hUV := by
  classical
  have hUaff : IsAffine (U.1 : Scheme.{u}) := U.2
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  have := locallyOfFiniteType_resLE f V.1 U.1 hUV
  choose a hxa ha using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((U.1 : Scheme.{u}).basicOpen (a x)).1)
    (fun x => ((U.1 : Scheme.{u}).basicOpen (a x)).2)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxa x⟩)
  have hcov : (⨆ j : Fin t.card, (U.1 : Scheme.{u}).basicOpen (a (t.equivFin.symm j).1)) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨i, hi⟩, by simpa using hx⟩
  exact (Scheme.Modules.isPseudoCoherentFrom_some_iff_forall_standardCover
    (f.resLE V.1 U.1 hUV) _ m (fun j => a (t.equivFin.symm j).1)
    ((Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top _).mpr hcov)).mp
    fun j => ha _

/-! ### Stacks 09UJ -/

/-- **Stacks 09UJ, the implication (1) ⟹ (2).** If `E` is relatively `m`-pseudo-coherent for
`f : X ⟶ S` locally of finite type, then the local condition of Stacks 09UI holds at every
compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`.

Given the pair, `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_forall_mem`
reduces the claim to finding, around each point `x` of `U`, a standard open of `U` carrying the
condition over `V`. Pick a member `V i` of the cover of `S` with `f(x) ∈ V i` and a member
`U_{ij}` of the cover of `f ⁻¹ᵁ V i` with `x ∈ U_{ij}`, both supplied by relative
`m`-pseudo-coherence. `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` applied in `V` gives an
affine open `V'' ⊆ V ⊓ V i` containing `f(x)`, and applied in `U` gives an affine open
`U' ⊆ U_{ij} ⊓ f ⁻¹ᵁ V''` of `X` which is a standard open of `U` containing `x`. The three moves
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.of_le_source`, `.of_le_base` and
`.of_base_le` carry the condition from `(U_{ij}, V i)` to `(U', V i)` to `(U', V'')` to
`(U', V)`. -/
public theorem isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom
    {E : DerivedCategory X.Modules} {m : ℤ} (h : f.IsPseudoCoherentFrom E m)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    f.IsPseudoCoherentFromOnAffinePair E m U V hUV := by
  obtain ⟨ι, Vc, hVcov, hVc⟩ := h
  refine isPseudoCoherentFromOnAffinePair_of_forall_mem f U V hUV fun x => ?_
  obtain ⟨i, hi⟩ : ∃ i, f.base x.1 ∈ ((Vc i).1 : S.Opens) :=
    Opens.mem_iSup.mp (hVcov ▸ Opens.mem_top (f.base x.1))
  obtain ⟨κ, Uc, hUcov, hUc⟩ := hVc i
  obtain ⟨j, hj⟩ : ∃ j, x.1 ∈ ((Uc j).1 : X.Opens) :=
    Opens.mem_iSup.mp (hUcov ▸ (hi : x.1 ∈ f ⁻¹ᵁ (Vc i).1))
  obtain ⟨hle, hij⟩ := hUc j
  obtain ⟨b, hbVi, hbx⟩ := V.2.exists_basicOpen_le (V := ((Vc i).1 : S.Opens))
    ⟨f.base x.1, hi⟩ (hUV x.2)
  obtain ⟨r, hrU, hrx⟩ := U.2.exists_basicOpen_le
    (V := ((Uc j).1 : X.Opens) ⊓ f ⁻¹ᵁ S.basicOpen b) ⟨x.1, hj, hbx⟩ x.2
  have hrUj : X.basicOpen r ≤ ((Uc j).1 : X.Opens) := fun _ hz => (hrU hz).1
  have hrVpp : X.basicOpen r ≤ f ⁻¹ᵁ S.basicOpen b := fun _ hz => (hrU hz).2
  have hrUle : X.basicOpen r ≤ (U.1 : X.Opens) := Scheme.basicOpen_le X r
  have hrV : X.basicOpen r ≤ f ⁻¹ᵁ (V.1 : S.Opens) := hrUle.trans hUV
  have hrVi : X.basicOpen r ≤ f ⁻¹ᵁ ((Vc i).1 : S.Opens) := hrUj.trans hle
  have hpair : f.IsPseudoCoherentFromOnAffinePair E m ⟨X.basicOpen r, U.2.basicOpen r⟩ V hrV := by
    refine IsPseudoCoherentFromOnAffinePair.of_base_le f
      (T := ⟨S.basicOpen b, V.2.basicOpen b⟩) (Scheme.basicOpen_le S b) hrVpp hrV ?_
    refine IsPseudoCoherentFromOnAffinePair.of_le_base f (T := Vc i) hbVi hrVi hrVpp ?_
    exact IsPseudoCoherentFromOnAffinePair.of_le_source f (W := Uc j) hrUj hle hrVi hij
  obtain ⟨n, i0, hi0, hi0o, hi0pc⟩ := hpair
  have := hi0
  have hbasic : U.1.ι ⁻¹ᵁ X.basicOpen r =
      (U.1 : Scheme.{u}).basicOpen (U.1.topIso.inv r) := by
    rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv U.1 r,
      U.1.ι.preimage_image_eq ((U.1 : Scheme.{u}).basicOpen (U.1.topIso.inv r))]
  have hi0o' : i0 ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom ≫ V.1.ι =
      (X.basicOpen r).ι ≫ f := by
    rw [← Category.assoc, hi0o, Scheme.Hom.resLE_comp_ι]
  refine ⟨U.1.topIso.inv r, ?_, ?_⟩
  · rwa [← hbasic]
  · rw [← hbasic]
    refine ⟨n, (Scheme.Opens.isoOfLE hrUle).hom ≫ i0, inferInstance, ?_,
      Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE hrUle i0 E m hi0pc⟩
    rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, Category.assoc,
      Scheme.Hom.resLE_comp_ι]
    exact Scheme.Modules.isoOfLE_hom_comp_comp_eq hrUle i0 _ f hi0o'

end Scheme.Hom

/-- **Stacks 09UJ.** For `f : X ⟶ S` locally of finite type, `E` an object of `D(𝒪_X)` and `m` an
integer, `E` is relatively `m`-pseudo-coherent if and only if the local condition of Stacks 09UI
holds at every compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`.

The implication (1) ⟹ (2) is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom` and the
implication (2) ⟹ (1) is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair`. This discharges the
condition `AlgebraicGeometry.AffinePairComparison`. -/
public theorem affinePairComparison {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) : AffinePairComparison f E m :=
  ⟨fun h U V hUV => Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f h U V hUV,
    Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair f E m⟩

end AlgebraicGeometry

end
