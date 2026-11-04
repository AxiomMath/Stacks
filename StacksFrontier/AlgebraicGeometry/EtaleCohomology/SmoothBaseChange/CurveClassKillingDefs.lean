module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveHigherDegreeClasses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.GaloisCover
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint

/-!
# The objects of Lemma 0EYT

Let `X` be a scheme over a field `k` with a rational point `x`. This file sets up the objects in
which [Stacks, Tag 0EYT] is stated: base changes are written `X_{k'} = Spec k' ×_{Spec k} X`;
`basePoint` is the base change `x_{k'}` of the rational point; `IsSplitOver p y` says that the
fibre of `p` over `y` is a finite disjoint union of copies of the source of `y`; and for a cover
`Z ⟶ X_{k'}` and a tower `k ⊆ k' ⊆ K'` with `K/k` and `K ⊆ K'`, `coverBaseChangeMap` is the
morphism `Z_{K'} = Spec K' ×_{Spec k'} Z ⟶ X_K` along which a class on `X_K` is restricted.

It also treats the case `q > 1` of the lemma, where the trivial cover `Z = X_k` does.

## Main definitions

* `Stacks.EtaleCohomology.basePoint`, `Stacks.EtaleCohomology.IsSplitOver`.
* `Stacks.EtaleCohomology.coverBaseChangeMap`, `Stacks.EtaleCohomology.coverBaseChangeClass`.

## Main results

* `Stacks.EtaleCohomology.isGaloisCover_id`, `Stacks.EtaleCohomology.isSplitOver_id`.
* `Stacks.EtaleCohomology.exists_galoisCover_of_one_lt` — the case `q > 1` of Tag 0EYT.

## References

* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The base change `x_{k'} : Spec k' ⟶ X_{k'}` of a rational point** `x` of `X`, where
`X_{k'} = Spec k' ×_{Spec k} X`. -/
def basePoint (k' : Type u) [Field k'] [Algebra k k'] (x : Spec (.of k) ⟶ X)
    (hx : x ≫ f = 𝟙 _) : Spec (.of k') ⟶ pullback (spectrumMap k k') f :=
  pullback.lift (𝟙 _) (spectrumMap k k' ≫ x) (by rw [Category.assoc, hx, Category.comp_id,
    Category.id_comp])

/-- **A finite étale `p : Z ⟶ Y` is split over `y : S ⟶ Y`** when the fibre `Z ×_Y S` is,
over `S`, a finite disjoint union of copies of `S`. -/
def IsSplitOver {S Z Y : Scheme.{u}} (p : Z ⟶ Y) (y : S ⟶ Y) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (e : ∐ (fun _ : ι => S) ≅ pullback p y),
    e.hom ≫ pullback.snd p y = Limits.Sigma.desc fun _ => 𝟙 S

section CoverBaseChange

variable (K k' K' : Type u) [Field K] [Field k'] [Field K'] [Algebra k K] [Algebra k k']
  [Algebra K K'] [Algebra k' K'] [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
  {Z : Scheme.{u}} (p : Z ⟶ pullback (spectrumMap k k') f)

/-- For a tower of fields `A ⊆ B ⊆ C`, the composite `Spec C ⟶ Spec B ⟶ Spec A` is the morphism
`Spec C ⟶ Spec A`. -/
theorem spectrumMap_comp_spectrumMap (A B C : Type u) [Field A] [Field B] [Field C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    spectrumMap B C ≫ spectrumMap A B = spectrumMap A C := by
  rw [spectrumMap, spectrumMap, spectrumMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- **The base change map `Z_{K'} ⟶ X_K`.** For a cover `p : Z ⟶ X_{k'}` and field extensions
`k ⊆ k' ⊆ K'` and `k ⊆ K ⊆ K'`, the morphism from `Z_{K'} = Spec K' ×_{Spec k'} Z` to
`X_K = Spec K ×_{Spec k} X` whose components are `Z_{K'} ⟶ Spec K' ⟶ Spec K` and
`Z_{K'} ⟶ Z ⟶ X_{k'} ⟶ X`. -/
def coverBaseChangeMap :
    pullback (spectrumMap k' K') (p ≫ pullback.fst (spectrumMap k k') f) ⟶
      pullback (spectrumMap k K) f :=
  pullback.lift (pullback.fst _ _ ≫ spectrumMap K K')
    (pullback.snd _ _ ≫ p ≫ pullback.snd _ _) (by
      rw [Category.assoc, spectrumMap_comp_spectrumMap, ← spectrumMap_comp_spectrumMap k k' K',
        ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, Category.assoc,
        pullback.condition, Category.assoc])

/-- The composite of `coverBaseChangeMap` with the projection `X_K ⟶ Spec K` is the composite
`Z_{K'} ⟶ Spec K' ⟶ Spec K`. -/
theorem coverBaseChangeMap_fst :
    coverBaseChangeMap f K k' K' p ≫ pullback.fst (spectrumMap k K) f =
      pullback.fst _ _ ≫ spectrumMap K K' :=
  pullback.lift_fst _ _ _

/-- **Restriction of a class on `X_K` to `Z_{K'}`**: the restriction along
`coverBaseChangeMap` followed by the identification of the two inverse images of a sheaf on
`Spec K`, along `Z_{K'} ⟶ X_K ⟶ Spec K` and along `Z_{K'} ⟶ Spec K' ⟶ Spec K`. -/
def coverBaseChangeClass (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) :
    Sheaf.H.{u + 1, u + 1}
        ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q →+
      Sheaf.H.{u + 1, u + 1} ((etaleAbelianInverseImage.{u, u + 1}
        (pullback.fst (spectrumMap k' K') (p ≫ pullback.fst (spectrumMap k k') f) ≫
          spectrumMap K K')).obj F) q :=
  etaleCohomologyMapTo (coverBaseChangeMap f K k' K' p)
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (coverBaseChangeMap f K k' K' p)
      (pullback.fst (spectrumMap k K) f) _ (coverBaseChangeMap_fst f K k' K' p).symm).inv.app F)
    q

end CoverBaseChange

/-! ### The trivial cover -/

section Trivial

/-- The identity of a connected scheme is a Galois cover, with trivial group. -/
theorem isGaloisCover_id {Z : Scheme.{u}} [ConnectedSpace Z] : IsGaloisCover (𝟙 Z) :=
  ⟨inferInstance, inferInstance, ‹_›, fun y a b => ⟨1, by
    have ha := a.2
    have hb := b.2
    rw [Category.comp_id] at ha hb
    change a.1 ≫ 𝟙 Z = b.1
    rw [Category.comp_id, ha, hb]⟩⟩

/-- The identity of a scheme, as an object over that scheme, has exactly one automorphism. -/
theorem natCard_aut_id (Z : Scheme.{u}) : Nat.card (Aut (Over.mk (𝟙 Z))) = 1 := by
  have : Subsingleton (Aut (Over.mk (𝟙 Z))) :=
    ⟨fun σ τ => Iso.ext ((Over.mkIdTerminal (X := Z)).hom_ext _ _)⟩
  have : Unique (Aut (Over.mk (𝟙 Z))) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  exact Nat.card_unique

/-- The identity is split over every point. -/
theorem isSplitOver_id {S Z : Scheme.{u}} (y : S ⟶ Z) : IsSplitOver (𝟙 Z) y := by
  refine ⟨PUnit, inferInstance, coproductUniqueIso (fun _ : PUnit => S) ≪≫
    (asIso (pullback.snd (𝟙 Z) y)).symm, ?_⟩
  refine Sigma.hom_ext _ _ fun i => ?_
  simp

/-- The base change of a geometrically connected scheme to a field is connected. -/
theorem connectedSpace_pullback_spectrumMap [GeometricallyConnected f] (K : Type u) [Field K]
    [Algebra k K] : ConnectedSpace ↥(pullback (spectrumMap k K) f) :=
  GeometricallyConnected.geometrically_connectedSpace (f := f) (spectrumMap k K)
    (pullback.snd _ _) (pullback.fst _ _) (IsPullback.of_hasPullback _ _).flip

end Trivial

/-! ### The case `q > 1` -/

variable {K : Type u} [Field K] [Algebra k K]

/-- **[Stacks, Tag 0EYT], the case `q > 1`, in the form of the lemma.** For `q > 1` one can take
`k' = k`, the trivial cover `Z = X_k` and a finite extension `K'/K`. -/
theorem exists_galoisCover_of_one_lt [IsCurve k f] [IsAffine X] (x : Spec (.of k) ⟶ X)
    (hx : x ≫ f = 𝟙 _) (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {n : ℕ} (hn : 0 < n) (hF : n • 𝟙 F = 0) {q : ℕ} (hq : 1 < q)
    (ξ : Sheaf.H.{u + 1, u + 1}
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.fst (spectrumMap k K) f)).obj F) q) :
    ∃ (k' K' : Type u) (_ : Field k') (_ : Field K') (_ : Algebra k k') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : Algebra k K') (_ : IsScalarTower k k' K')
      (_ : IsScalarTower k K K') (_ : FiniteDimensional k k') (_ : FiniteDimensional K K')
      (Z : Scheme.{u}) (p : Z ⟶ pullback (spectrumMap k k') f),
      IsGaloisCover p ∧ (∃ m : ℕ, Nat.card (Aut (Over.mk p)) ∣ n ^ m) ∧
        IsSplitOver p (basePoint f k' x hx) ∧ coverBaseChangeClass f K k' K' p F q ξ = 0 := by
  obtain ⟨E, hE, hξ⟩ := exists_finiteDimensional_restriction_eq_zero_of_one_lt f F hn hF hq ξ
  let : Algebra k E := ((algebraMap K E).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k k E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IrreducibleSpace X := inferInstance
  have : ConnectedSpace X :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ X).isConnected
  have : GeometricallyConnected f := geometricallyConnected_of_connectedSpace_of_section f x hx
  have := connectedSpace_pullback_spectrumMap f k
  refine ⟨k, E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hE, _, 𝟙 _, isGaloisCover_id,
    ⟨0, by rw [natCard_aut_id, pow_zero]⟩, isSplitOver_id _, ?_⟩
  let g : pullback (spectrumMap k E) (𝟙 _ ≫ pullback.fst (spectrumMap k k) f) ⟶
      pullback (spectrumMap K E) (pullback.fst (spectrumMap k K) f) :=
    pullback.lift (pullback.fst _ _) (coverBaseChangeMap f K k E (𝟙 _))
      (coverBaseChangeMap_fst f K k E (𝟙 _)).symm
  have hg : g ≫ pullback.snd _ _ = coverBaseChangeMap f K k E (𝟙 _) := pullback.lift_snd _ _ _
  rw [coverBaseChangeClass, ← etaleCohomologyMapTo_comp g (pullback.snd _ _) _ hg.symm
    (𝟙 _) ((etaleAbelianInverseImageCompIso'.{u, u + 1} g (pullback.snd _ _) _ hg.symm).inv.app _ ≫
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (coverBaseChangeMap f K k E (𝟙 _))
        (pullback.fst (spectrumMap k K) f) _ (coverBaseChangeMap_fst f K k E (𝟙 _)).symm).inv.app F)
    _ (by simp), etaleCohomologyMapTo_id, hξ, map_zero]

end Stacks.EtaleCohomology

end
