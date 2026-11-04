module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk

/-!
# Descending a vector bundle that is free over the local schemes in codimension one

Let `f : X ⟶ S` be flat and proper with `𝒪_S = f_*𝒪_X`, let `S` be a normal Noetherian scheme,
and let `ℰ` be a finite locally free `𝒪_X`-module whose pullback to `X ×_S Spec 𝒪_{S,s}` is free
for every point `s` of codimension one. Then `ℰ` is isomorphic to the pullback of a finite
locally free `𝒪_S`-module, provided the same freeness holds at the generic points of the
irreducible components of `S` that contain no point of codimension one. This is
[Stacks, Tag 0EXG] with a hypothesis the source omits, without which the statement is false.

## Main results

* `AlgebraicGeometry.VectorBundleCodimensionOne.exists_isFiniteLocallyFree_pullback_iso`: a finite
  locally free module which is free over the local schemes of `S` in codimension at most one is
  the pullback of a finite locally free module on `S`.

## References

* [Stacks Project, Tag 0EXG](https://stacks.math.columbia.edu/tag/0EXG)
* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0AVM](https://stacks.math.columbia.edu/tag/0AVM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.VectorBundleCodimensionOne

/-- Let `f : X ⟶ S` be flat and proper with `𝒪_S = f_*𝒪_X`, let `S` be a normal Noetherian
scheme, and let `ℰ` be a finite locally free `𝒪_X`-module whose pullback to `X ×_S Spec 𝒪_{S,s}`
is free for every point `s ∈ S` of codimension one, and also for every point `s` of codimension
zero that does not specialize to a point of codimension one. Then `ℰ` is isomorphic to the
pullback of a finite locally free `𝒪_S`-module.

The two conditions `hfree` and `hfree₀` together are equivalent to freeness over the local scheme
at every point of codimension at most one. The condition `hfree₀` is not in the source, and the
statement is false without it (`not_forall_exists_isFiniteLocallyFree_pullback_iso_of_codimOne`):
for a field `k`, take `S = Spec k`, `X = ℙ¹_k` and `ℰ = 𝒪(1)`; then `S` has no point of
codimension one, but `𝒪(1)` is not the pullback of a `k`-vector space. When every irreducible
component of `S` has a point of codimension one, `hfree₀` is vacuous.

Codimension of a point is the Krull dimension of its local ring, and freeness after base change
to the local scheme at `s` means an isomorphism with some free module `𝒪^{(I)}`, the index set
being arbitrary. The hypothesis `𝒪_S = f_*𝒪_X` is invertibility of the comparison map
`f.toLRSHom.toHom.c`. -/
@[stacks 0EXG "corrected: freeness is also required at generic points of S with no \
codimension-1 specialization; as stated the lemma fails for X = ℙ¹_k over Spec k with ℰ = 𝒪(1)"]
public theorem exists_isFiniteLocallyFree_pullback_iso {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [IsProper f] [IsNoetherian S] [IsNormal S] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (hO : IsIso f.toLRSHom.toHom.c)
    (hfree : ∀ s : S, ringKrullDim (S.presheaf.stalk s) = 1 →
      ∃ I : Type u, Nonempty
        ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E ≅
          SheafOfModules.free I))
    (hfree₀ : ∀ s : S, ringKrullDim (S.presheaf.stalk s) = 0 →
      (∀ t : S, s ⤳ t → ringKrullDim (S.presheaf.stalk t) ≠ 1) →
      ∃ I : Type u, Nonempty
        ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E ≅
          SheafOfModules.free I)) :
    ∃ M : S.Modules, SheafOfModules.IsFiniteLocallyFree.{u, u, u} M ∧
      Nonempty ((Scheme.Modules.pullback f).obj M ≅ E) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let M := (Scheme.Modules.pushforward f).obj E
  have : M.IsCoherent := ProperCoherenceWitness.isCoherent_pushforward f E
  have hMqc : M.IsQuasicoherent := AlgebraicGeometry.pushforward_isQuasicoherent f E
  have : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E).IsCoherent :=
    isCoherent_pullback f M
  have : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj E).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom M hMqc
  have : ((𝟭 X.Modules).obj E).IsQuasicoherent := inferInstanceAs E.IsQuasicoherent
  have : M.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hstalkFinite : ∀ s : S, Module.Finite (S.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf s) :=
    SheafOfModules.finite_stalk S.sheaf M
  have hlocal : ∀ (x : X) (s : S), f x ⤳ s →
      (∃ I : Type u, Nonempty
        ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E ≅
          SheafOfModules.free I)) →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E).val)) := by
    rintro x s hxs ⟨I, ⟨e⟩⟩
    have : IsLocallyNoetherian (pullback f (S.fromSpecStalk s)) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f _)
    exact isIso_stalk_counit_of_iso_free f hO E s I e
      (isCoherent_pullback (pullback.fst f (S.fromSpecStalk s)) E).isFiniteType x hxs
  have hcodim : ∀ x : X, ringKrullDim (S.presheaf.stalk (f x)) ≤ 1 →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app E).val)) := by
    intro x hx
    by_cases h1 : ringKrullDim (S.presheaf.stalk (f x)) = 1
    · exact hlocal x (f x) specializes_rfl (hfree (f x) h1)
    have hlt : ringKrullDim (S.presheaf.stalk (f x)) < ((0 : ℕ) : WithBot ℕ∞) + 1 := by
      simpa using lt_of_le_of_ne hx h1
    have h0 : ringKrullDim (S.presheaf.stalk (f x)) = 0 :=
      le_antisymm (by simpa using ENat.WithBot.lt_add_one_iff.mp hlt)
        ringKrullDim_nonneg_of_nontrivial
    by_cases hspec : ∃ t : S, f x ⤳ t ∧ ringKrullDim (S.presheaf.stalk t) = 1
    · obtain ⟨t, hxt, ht⟩ := hspec
      exact hlocal x t hxt (hfree t ht)
    · exact hlocal x (f x) specializes_rfl
        (hfree₀ (f x) h0 fun t hxt ht => hspec ⟨t, hxt, ht⟩)
  have : Surjective f := surjective_of_isIso_cMap f hO
  exact exists_isFiniteLocallyFree_pullback_iso_of_isIso_counit f E
    (isIso_counit_of_isIso_stalk_of_codim_le_one f E hstalkFinite hcodim)

end AlgebraicGeometry.VectorBundleCodimensionOne

end
