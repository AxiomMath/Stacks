module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StandardCoverGluing

/-!
# Localizing relative pseudo-coherence to an arbitrary affine open, Stacks 09VD

Let `S` be an affine scheme, `V ⊆ S` an affine open, `f : X ⟶ V` a morphism of affine schemes
locally of finite type and `E` an object of `D(𝒪_X)`. Stacks 09VD says that if the equivalent
conditions of Stacks 09VC hold for the pair `(X ⟶ V, E)`, then they hold for `(U ⟶ S, E|_U)` for
*every affine open* `U ⊆ X`.

The source's own proof produces the conclusion only for a *standard* open of `X`; that case is
`Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen`
(in the `AlgebraicGeometry` namespace), and passing from it to an arbitrary affine open is
Stacks 09VE. This file takes that step: an affine open `U` of an affine scheme `X` is covered by
the standard opens of `X` that it contains
(`AlgebraicGeometry.exists_fin_basicOpen_le_cover`), those are standard opens of `U` as well, and
Stacks 09VE glues the conditions at them into the condition at `U`.

## Main results

* `AlgebraicGeometry.exists_fin_basicOpen_le_cover`: an affine open of an affine scheme is covered
  by finitely many standard opens of the ambient scheme contained in it.
* `AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrictInv` and
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompPushforwardIso`: pushforward along an
  isomorphism of schemes is restriction along its inverse.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorOfLEIso` and
  `AlgebraicGeometry.Scheme.Modules.derivedRestrictOfLEObjIso`: restricting to `W ≤ A` in one step
  and restricting to `A` and then to `A ∩ W` differ by the canonical isomorphism
  `A ∩ W ≅ W`, at the level of modules and of derived categories.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE`: the local
  condition of Stacks 09UI transported along that isomorphism.
* `AlgebraicGeometry.Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_affineOpen`:
  **Stacks 09VD at an arbitrary affine open of `X`**, granted the side condition of Stacks 09VA.

## Implementation notes

**Why a comparison of restrictions is needed at all.** Stacks 09VD restricts `E` to `U` in a single
step, while its proof restricts twice: first to `U`, then to a member of a cover of `U`. The
members of the cover used here are the standard opens `X_b` of `X` contained in `U`, for which the
standard-open case supplies the condition at the *single* restriction
`(restrictFunctor (X_b).ι).mapDerivedCategory.obj E` on the scheme `(X_b).toScheme`, whereas Stacks
09VE asks for it at the *double* restriction on the scheme `(ι_U⁻¹X_b).toScheme`, an open subscheme
of `U`. The two schemes are isomorphic by `AlgebraicGeometry.Scheme.Opens.isoOfLE`, and the two
objects correspond under that isomorphism; supplying the correspondence is the content of this file
beyond the gluing.

It is assembled from Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`,
`restrictFunctorCongr` and `restrictFunctorId` at the level of functors, and carried to derived
categories by `CategoryTheory.Functor.mapDerivedCategoryCompIso`. One fact about restriction along
an isomorphism `k` is needed that Mathlib does not state: that `k_*` is restriction along `k⁻¹`,
equivalently that `restrictFunctor k ⋙ pushforward k ≅ 𝟭`. Mathlib has the *other* composite,
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`, for any open immersion; whiskering
it with `AlgebraicGeometry.Scheme.Modules.restrictFunctorCompInvIso` turns it into this one, with
no equivalence of categories and no coherence obligation.

**The cover.** `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` gives, for each point of `U`, a
standard open of `X` between the point and `U`; `U` is a compact space because it is affine, so
finitely many suffice. Their preimages in `U` are the standard opens of `U` cut out by the
restrictions of the same global sections, by
`AlgebraicGeometry.Scheme.preimage_basicOpen_top`, which is what makes them a standard affine open
cover of `U` in the sense Stacks 09VE consumes.

**What is conditional.** Four instances of the side condition of Stacks 09VA are carried as
hypotheses, in exactly the shapes the cited results consume them: `hOV` and `hOS` for the
standard-open case over `V`
(`Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen`),
and `hO` and `hOb` for the gluing over `S`
(`Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen`).
Stacks 09VD carries none of them, so no `stacks` attribute is placed here; discharging the side
condition of Stacks 09VA discharges all four with no restatement.

**`V` need not be a standard open.** Stacks 09VD assumes that `V` is a standard open of `S`, and
the hypothesis is *not* taken here: it is used nowhere. Neither the standard-open case over `V`
nor the gluing over `S` needs it — the first because `𝔸ⁿ_V ⟶ S` is locally of finite type for any
open `V`, as `Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_affineOpen` already
records, and the second because it is a statement about `U` and `S` alone. Omitting it makes the
result strictly stronger than Stacks 09VD, which therefore follows from it by discarding the
hypothesis.

**An expected linter finding.** The instance `[QuasiCompact f]`, which Stacks 09VD's hypotheses
include, is kept and is not used — it is automatic for a morphism of affine schemes — so
`lake lint` reports one `unusedArguments` finding on this file, as it does for several of the
neighbouring ones.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`, which
is made a local instance; there is no global instance, so a user of these results makes the same
declaration.

## References

* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### An affine open is covered by standard opens of the ambient affine scheme -/

/-- **An affine open of an affine scheme is covered by finitely many standard opens of the ambient
scheme contained in it.** Each point of `A` lies in a standard open `X_b ≤ A` by
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`, and `A` is a compact space because it is
affine, so a finite subfamily already covers it.

The conclusion is phrased with the preimages `ι_A⁻¹X_b`, which are the opens of `A` the cover
consists of; `AlgebraicGeometry.Scheme.preimage_basicOpen_top` identifies them with the standard
opens of `A` cut out by the restrictions of the `b`, which is the form Stacks 09VE consumes. -/
public theorem exists_fin_basicOpen_le_cover {X : Scheme.{u}} [IsAffine X] (A : X.Opens)
    [IsAffine A.toScheme] :
    ∃ (N : ℕ) (b : Fin N → Γ(X, ⊤)), (∀ j, X.basicOpen (b j) ≤ A) ∧
      (⨆ j, A.ι ⁻¹ᵁ X.basicOpen (b j)) = ⊤ := by
  classical
  have hcover : (Set.univ : Set A.toScheme) ⊆
      ⋃ b : {b : Γ(X, ⊤) // X.basicOpen b ≤ A}, (A.ι ⁻¹ᵁ X.basicOpen b.1).1 := by
    intro x _
    obtain ⟨b, hbA, hxb⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := A) x (Opens.mem_top _)
    exact Set.mem_iUnion.2 ⟨⟨b, hbA⟩, hxb⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : {b : Γ(X, ⊤) // X.basicOpen b ≤ A} => (A.ι ⁻¹ᵁ X.basicOpen b.1).1)
    (fun b => (A.ι ⁻¹ᵁ X.basicOpen b.1).2) hcover
  refine ⟨t.card, fun j => (t.equivFin.symm j).1.1, fun j => (t.equivFin.symm j).1.2, ?_⟩
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨i, hi⟩, by simpa using hx⟩

namespace Scheme.Modules

/-! ### Restricting in one step and in two -/

/-- **Pushforward along an isomorphism of schemes is restriction along its inverse.** Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` identifies `k^*k_*` with the
identity for any open immersion `k`; restricting further along `k⁻¹`, which undoes `k^*` by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCompInvIso`, turns that into the statement here.
No equivalence of categories is produced and no coherence condition arises. -/
public def pushforwardIsoRestrictInv {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] :
    pushforward k ≅ restrictFunctor (inv k) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (pushforward k) (restrictFunctorCompInvIso k).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictFunctorAdjCounitIso k) (restrictFunctor (inv k)) ≪≫
    Functor.leftUnitor _

/-- Restricting along an isomorphism `k` of schemes and then pushing forward along `k` is the
identity. This is the composite Mathlib does not state —
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` is the other one — and it follows
from `AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrictInv`. -/
public def restrictFunctorCompPushforwardIso {Y Z : Scheme.{u}} (k : Y ⟶ Z) [IsIso k] :
    restrictFunctor k ⋙ pushforward k ≅ 𝟭 Z.Modules :=
  Functor.isoWhiskerLeft (restrictFunctor k) (pushforwardIsoRestrictInv k) ≪≫
    restrictFunctorCompInvIso k

/-- **Restricting to `W ≤ A` in one step and in two.** Restricting a sheaf of `𝒪_X`-modules to `A`
and then to `ι_A⁻¹W`, and then pushing forward along the canonical isomorphism
`ι_A⁻¹W ≅ W` of `AlgebraicGeometry.Scheme.Opens.isoOfLE`, is restricting to `W` directly.

The two restrictions compose to a single one along `ι_{ι_A⁻¹W} ≫ ι_A` by Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`, that morphism is
`isoOfLE ≫ ι_W` by `AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_ι`, and splitting *that* composite
again leaves a restriction along the isomorphism, which
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCompPushforwardIso` cancels against the
pushforward. -/
public def restrictFunctorOfLEIso {X : Scheme.{u}} {A W : X.Opens} (h : W ≤ A) :
    restrictFunctor A.ι ⋙
        (restrictFunctor (A.ι ⁻¹ᵁ W).ι ⋙ pushforward (Scheme.Opens.isoOfLE h).hom) ≅
      restrictFunctor W.ι :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((restrictFunctorComp (A.ι ⁻¹ᵁ W).ι A.ι).symm ≪≫
      restrictFunctorCongr (Scheme.Opens.isoOfLE_hom_ι h).symm ≪≫
      restrictFunctorComp (Scheme.Opens.isoOfLE h).hom W.ι)
      (pushforward (Scheme.Opens.isoOfLE h).hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictFunctor W.ι)
      (restrictFunctorCompPushforwardIso (Scheme.Opens.isoOfLE h).hom) ≪≫
    Functor.rightUnitor _

/-- `AlgebraicGeometry.Scheme.Modules.restrictFunctorOfLEIso` at an object of the derived
category. The functor isomorphism is carried across by
`CategoryTheory.Functor.mapDerivedCategoryCompIso`, used twice: once at the identity isomorphism,
to split the induced functor of a composite, and once at the comparison itself. -/
public def derivedRestrictOfLEObjIso {X : Scheme.{u}} {A W : X.Opens} (h : W ≤ A)
    (E : DerivedCategory X.Modules) :
    (pushforward (Scheme.Opens.isoOfLE h).hom).mapDerivedCategory.obj
        ((restrictFunctor (A.ι ⁻¹ᵁ W).ι).mapDerivedCategory.obj
          ((restrictFunctor A.ι).mapDerivedCategory.obj E)) ≅
      (restrictFunctor W.ι).mapDerivedCategory.obj E :=
  (Functor.mapDerivedCategoryCompIso (Iso.refl (restrictFunctor (A.ι ⁻¹ᵁ W).ι ⋙
      pushforward (Scheme.Opens.isoOfLE h).hom))).app
      ((restrictFunctor A.ι).mapDerivedCategory.obj E) ≪≫
    (Functor.mapDerivedCategoryCompIso (restrictFunctorOfLEIso h)).app E

/-- **The local condition of Stacks 09UI transported from `W` to `ι_A⁻¹W`.** Let `W ≤ A` be opens
of `X` and let `l : W ⟶ Y` be a closed immersion. If the derived pushforward of `E|_W` along `l`
is `m`-pseudo-coherent, then so is the derived pushforward of `(E|_A)|_{ι_A⁻¹W}` along
`isoOfLE ≫ l`.

Precomposition with an isomorphism is handled by
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_isIso_iff`, and the
object it leaves is identified by
`AlgebraicGeometry.Scheme.Modules.derivedRestrictOfLEObjIso`. -/
public theorem isPseudoCoherentFromAfterPushforward_isoOfLE {X Y : Scheme.{u}} {A W : X.Opens}
    (h : W ≤ A) (l : W.toScheme ⟶ Y) [IsClosedImmersion l] (E : DerivedCategory X.Modules)
    (m : ℤ)
    (hl : IsPseudoCoherentFromAfterPushforward l
      ((restrictFunctor W.ι).mapDerivedCategory.obj E) m) :
    IsPseudoCoherentFromAfterPushforward ((Scheme.Opens.isoOfLE h).hom ≫ l)
      ((restrictFunctor (A.ι ⁻¹ᵁ W).ι).mapDerivedCategory.obj
        ((restrictFunctor A.ι).mapDerivedCategory.obj E)) m := by
  rw [isPseudoCoherentFromAfterPushforward_precomp_isIso_iff]
  exact IsPseudoCoherentFromAfterPushforward.of_iso l hl (derivedRestrictOfLEObjIso h E).symm

/-! ### Stacks 09VD at an arbitrary affine open -/

/-- **Stacks 09VD at an arbitrary affine open of `X`**, granted the side condition of Stacks 09VA.
Let `S` be affine, let `V` be an affine open of `S`, let `f : X ⟶ V` be a morphism of affine
schemes locally of finite type, let `U` be an affine open of `X` and let `E` be an object of
`D(𝒪_X)`. If the equivalent conditions of Stacks 09VC hold for the pair `(X ⟶ V, E)` then they
hold for the pair `(U ⟶ S, E|_U)`.

Stacks 09VD assumes in addition that `V` is a *standard* open of `S`; that hypothesis is not
needed and is not taken, so this is the stronger statement.

Cover `U` by the finitely many standard opens `X_{bⱼ}` of `X` contained in it
(`AlgebraicGeometry.exists_fin_basicOpen_le_cover`). Their preimages in `U` are the standard opens
of `U` cut out by the restrictions of the `bⱼ`, so they are a standard affine open cover of `U`.
The standard-open case of Stacks 09VD
(`Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen`)
gives the conditions of Stacks 09VC for each `(X_{bⱼ} ⟶ S, E|_{X_{bⱼ}})`;
`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_isoOfLE` moves each one onto
the corresponding open of `U`; and Stacks 09VE
(`Scheme.Modules.exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen`)
glues them. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_affineOpen {S X : Scheme.{u}}
    [IsAffine S] [IsAffine X] (V : S.affineOpens) (f : X ⟶ (V.1 : Scheme.{u}))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hOV : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) (V.1 : Scheme.{u}), ⊤)),
      PushforwardStructureSheafPseudoCoherent (V.1 : Scheme.{u})
        ((AffineSpace (ULift.{u} (Fin N)) (V.1 : Scheme.{u})).basicOpen a).toScheme)
    (hOS : ∀ (n N : ℕ) (p : AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u}) ⟶
        AffineSpace (ULift.{u} (Fin N)) S), IsClosedImmersion p →
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin N)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin N)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit
              (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).ringCatSheaf))))
    (hO : ∀ {a b : ℕ}
      (p : AffineSpace (ULift.{u} (Fin a)) S ⟶ AffineSpace (ULift.{u} (Fin b)) S)
      [IsClosedImmersion p],
      RingedSpace.IsPseudoCoherent (X := (AffineSpace (ULift.{u} (Fin b)) S).toRingedSpace)
        ((DerivedCategory.singleFunctor (AffineSpace (ULift.{u} (Fin b)) S).Modules 0).obj
          ((pushforward p).obj
            (SheafOfModules.unit (AffineSpace (ULift.{u} (Fin a)) S).ringCatSheaf))))
    (hOb : ∀ (N : ℕ) (a : Γ(AffineSpace (ULift.{u} (Fin N)) S, ⊤)),
      PushforwardStructureSheafPseudoCoherent S
        ((AffineSpace (ULift.{u} (Fin N)) S).basicOpen a).toScheme)
    (U : X.affineOpens) (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom = f ∧
          IsPseudoCoherentFromAfterPushforward i E m) :
    ∃ (n : ℕ) (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = U.1.ι ≫ f ≫ V.1.ι ∧
          IsPseudoCoherentFromAfterPushforward i
            ((restrictFunctor U.1.ι).mapDerivedCategory.obj E) m := by
  have hUaff : IsAffine (U.1 : Scheme.{u}) := U.2
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  obtain ⟨N, b, hbU, hbcov⟩ := exists_fin_basicOpen_le_cover U.1
  have hpre : ∀ j, U.1.ι ⁻¹ᵁ X.basicOpen (b j) =
      (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (b j)) :=
    fun j => Scheme.preimage_basicOpen_top U.1.ι (b j)
  have hcov : (⨆ j, (U.1 : Scheme.{u}).basicOpen (U.1.ι.appTop (b j))) = ⊤ :=
    (iSup_congr fun j => hpre j).symm.trans hbcov
  refine exists_isPseudoCoherentFromAfterPushforward_of_forall_basicOpen
    (U.1.ι ≫ f ≫ V.1.ι) hO hOb _ m (fun j => U.1.ι.appTop (b j))
    ((Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top _).mpr hcov) fun j => ?_
  obtain ⟨k, l, hl, hlo, hlpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_basicOpen_of_affineOpen V f hOV hOS E m (b j) h
  have := hl
  rw [← hpre j]
  refine ⟨k, (Scheme.Opens.isoOfLE (hbU j)).hom ≫ l, inferInstance, ?_,
    isPseudoCoherentFromAfterPushforward_isoOfLE (hbU j) l E m hlpc⟩
  rw [Category.assoc, hlo, ← Category.assoc, ← Category.assoc,
    Scheme.Opens.isoOfLE_hom_ι (hbU j), Category.assoc, Category.assoc]

end Scheme.Modules

end AlgebraicGeometry

end
