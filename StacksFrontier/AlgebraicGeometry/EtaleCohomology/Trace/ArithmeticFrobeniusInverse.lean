module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FrobeniusRestrictionCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionEndomorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BafflingTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion

/-!
# The arithmetic Frobenius acts as the inverse of the geometric Frobenius

Let `k` be a finite field with `q = p ^ f` elements, let `X` be a scheme over `k` and let `K`
be an extension field of `k`. Write `X_K = X ×_{Spec k} Spec K` for the base change. Two
endomorphisms of `X_K` are in play:

* `galoisBaseChange X K σ`, the base change `id_X × Spec(σ)` of a `k`-automorphism `σ` of `K`;
* `geometricFrobeniusBaseChange X K p f hcard`, the base change `π_X × id` of the geometric
  Frobenius `π_X` of `X`.

When `σ` is the arithmetic Frobenius `frob_k : x ↦ x ^ q` these two commute, their composite is
the `f`-fold absolute Frobenius of `X_K`, and each acts on étale cohomology as the inverse of the
other.

## Main definitions

* `Stacks.Frobenius.galoisBaseChange`: the automorphism `id_X × Spec(σ)` of `X_K`.
* `Stacks.Frobenius.geometricFrobeniusBaseChange`: the endomorphism `π_X × id` of `X_K`.
* `Stacks.Frobenius.galoisBaseChangeEtaleEquivalence`: base change along
  `id_X × Spec(frob_k)` as an equivalence of the small étale site of `X_K`, with quasi-inverse
  base change along `π_X × id`.

## Main results

* `Stacks.Frobenius.galoisBaseChange_comp_geometricFrobeniusBaseChange` and
  `Stacks.Frobenius.geometricFrobeniusBaseChange_comp_galoisBaseChange`: both composites equal
  the `f`-fold absolute Frobenius of `X_K`, so the two endomorphisms commute
  (`Stacks.Frobenius.galoisBaseChange_comm_geometricFrobeniusBaseChange`).
* `Stacks.Frobenius.galoisCompGeometricFrobeniusCohomologyIso`: on étale cohomology in every
  degree and for arbitrary abelian coefficients, inverse image along `π_X × id` followed by
  inverse image along `id_X × Spec(frob_k)` is canonically isomorphic to the identity.
* `Stacks.Frobenius.galoisCompGeometricFrobeniusCohomologyAddEquiv`: the same at a single
  abelian sheaf, as an isomorphism of cohomology groups.
* `Stacks.Frobenius.galoisRestrictionEndo_comp_geometricFrobeniusRestrictionEndo` and
  `Stacks.Frobenius.geometricFrobeniusRestrictionEndo_comp_galoisRestrictionEndo`: for an
  abelian sheaf `ℱ` on `X_étale` and every degree `j`, the two endomorphisms of
  `H^j(X_K, ℱ|_{X_K})` induced by `id_X × Spec(frob_k)` and by `π_X × id` are mutually inverse.

## Implementation notes

The arithmetic Frobenius enters as a `k`-automorphism `σ` of `K` together with the hypothesis
`∀ x, σ x = x ^ p ^ f`; by `Stacks.Frobenius.eq_arithmeticFrobenius` this hypothesis determines
`σ` uniquely, and `arithmeticFrobenius_comp_geometricFrobeniusBaseChange` is the specialisation
to `Stacks.Frobenius.arithmeticFrobenius`. No algebraicity, separability or algebraic
closedness of `K/k` is assumed, so `K = k̄` is a special case.

## References

* [Stacks Project, Tag 03SV](https://stacks.math.columbia.edu/tag/03SV)
-/


@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology
open Stacks.Frobenius

namespace Stacks.Frobenius

/-- A finite field with `p ^ f` elements has `f ≠ 0`. -/
public lemma ne_zero_of_card_eq_pow {k : Type u} [Field k] [Fintype k] {p f : ℕ}
    (hcard : Fintype.card k = p ^ f) : f ≠ 0 := by
  rintro rfl
  exact Fintype.one_lt_card.ne' (hcard.trans (pow_zero p))

/-- The structure morphism `Spec K ⟶ Spec k` of an extension field `K` of `k`. -/
public abbrev specAlgebraMap (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K] :
    Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- `Spec K` is in characteristic `p` when the base field `k` is. -/
public lemma isInCharacteristic_specAlgebraMap (k : Type u) [Field k] (K : Type u) [Field K]
    [Algebra k K] (p : ℕ) [CharP k p] : IsInCharacteristic (Spec (.of K)) p :=
  isInCharacteristic_of_over (p := p) (Over.mk (specAlgebraMap k K))

section BaseChange

variable {k : Type u} [Field k] (X : Over (Spec (.of k)))
  (K : Type u) [Field K] [Algebra k K]

/-- The base change `X_K = X ×_{Spec k} Spec K` of a scheme `X` over `k` to an extension
field `K`. -/
@[ega "IV 6.7.7"]
public abbrev fieldBaseChange : Scheme.{u} :=
  pullback X.hom (specAlgebraMap k K)

/-- **The `G_k`-action on `X_K`.** The automorphism `id_X × Spec(σ)` of `X_K` attached to a
`k`-automorphism `σ` of `K`. -/
public def galoisBaseChange (σ : K ≃ₐ[k] K) : fieldBaseChange X K ⟶ fieldBaseChange X K :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom))
    (by
      have h : CommRingCat.ofHom (algebraMap k K) ≫
          CommRingCat.ofHom σ.toAlgHom.toRingHom =
            CommRingCat.ofHom (algebraMap k K) := by
        ext x
        exact σ.commutes x
      rw [Category.assoc, ← Spec.map_comp, h]
      exact pullback.condition)

/-- `id_X × Spec(σ)` is a morphism over `X`. -/
@[reassoc (attr := simp)]
public lemma galoisBaseChange_comp_fst (σ : K ≃ₐ[k] K) :
    galoisBaseChange X K σ ≫ pullback.fst X.hom (specAlgebraMap k K) =
      pullback.fst X.hom (specAlgebraMap k K) :=
  pullback.lift_fst _ _ _

/-- `id_X × Spec(σ)` is `Spec(σ)` on the second factor. -/
@[reassoc (attr := simp)]
public lemma galoisBaseChange_comp_snd (σ : K ≃ₐ[k] K) :
    galoisBaseChange X K σ ≫ pullback.snd X.hom (specAlgebraMap k K) =
      pullback.snd X.hom (specAlgebraMap k K) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) :=
  pullback.lift_snd _ _ _

variable (p : ℕ) [CharP k p]

/-- `X_K` is in characteristic `p` when the base field `k` is. -/
public lemma isInCharacteristic_fieldBaseChange :
    IsInCharacteristic (fieldBaseChange X K) p :=
  isInCharacteristic_of_hom (pullback.fst X.hom (specAlgebraMap k K)) p
    (isInCharacteristic_of_over X)

variable [Fintype k] (f : ℕ) [Fact p.Prime] (hcard : Fintype.card k = p ^ f)

/-- The base change `π_X × id` to `K` of the geometric Frobenius `π_X` of `X`. -/
public def geometricFrobeniusBaseChange :
    fieldBaseChange X K ⟶ fieldBaseChange X K :=
  pullback.lift (pullback.fst _ _ ≫ (geometricFrobenius X p f hcard).left)
    (pullback.snd _ _)
    (by rw [Category.assoc, Over.w]; exact pullback.condition)

/-- `π_X × id` lies over `π_X`. -/
@[reassoc (attr := simp)]
public lemma geometricFrobeniusBaseChange_comp_fst :
    geometricFrobeniusBaseChange X K p f hcard ≫ pullback.fst X.hom (specAlgebraMap k K) =
      pullback.fst X.hom (specAlgebraMap k K) ≫ (geometricFrobenius X p f hcard).left :=
  pullback.lift_fst _ _ _

/-- `π_X × id` is the identity on the second factor. -/
@[reassoc (attr := simp)]
public lemma geometricFrobeniusBaseChange_comp_snd :
    geometricFrobeniusBaseChange X K p f hcard ≫ pullback.snd X.hom (specAlgebraMap k K) =
      pullback.snd X.hom (specAlgebraMap k K) :=
  pullback.lift_snd _ _ _

/-- With `σ` the arithmetic Frobenius `x ↦ x ^ q` of `K`, both composites of `id_X × Spec(σ)` and
`π_X × id` are the `f`-fold absolute Frobenius of `X_K`. -/
private theorem comp_eq_absoluteFrobeniusPow_and (σ : K ≃ₐ[k] K)
    (hσ : ∀ x : K, σ x = x ^ p ^ f) :
    galoisBaseChange X K σ ≫ geometricFrobeniusBaseChange X K p f hcard =
        absoluteFrobeniusPow (fieldBaseChange X K) p
          (isInCharacteristic_fieldBaseChange X K p) f ∧
      geometricFrobeniusBaseChange X K p f hcard ≫ galoisBaseChange X K σ =
        absoluteFrobeniusPow (fieldBaseChange X K) p
          (isInCharacteristic_fieldBaseChange X K p) f := by
  have hspec := specMap_eq_absoluteFrobeniusPow (σ : K →+* K) p f
    (isInCharacteristic_specAlgebraMap k K p) hσ
  constructor <;> refine pullback.hom_ext ?_ ?_ <;> first
    | simpa [hspec] using
        (absoluteFrobeniusPow_naturality _ p _ (isInCharacteristic_of_over X) f).symm
    | simpa [hspec] using
        (absoluteFrobeniusPow_naturality _ p _ (isInCharacteristic_specAlgebraMap k K p) f).symm

/-- With `σ` the arithmetic Frobenius `x ↦ x ^ q` of `K`, the composite
`(π_X × id) ∘ (id_X × Spec(σ))` is the `f`-fold absolute Frobenius of `X_K`. -/
public theorem galoisBaseChange_comp_geometricFrobeniusBaseChange (σ : K ≃ₐ[k] K)
    (hσ : ∀ x : K, σ x = x ^ p ^ f) :
    galoisBaseChange X K σ ≫ geometricFrobeniusBaseChange X K p f hcard =
      absoluteFrobeniusPow (fieldBaseChange X K) p
        (isInCharacteristic_fieldBaseChange X K p) f :=
  (comp_eq_absoluteFrobeniusPow_and X K p f hcard σ hσ).1

/-- With `σ` the arithmetic Frobenius `x ↦ x ^ q` of `K`, the composite
`(id_X × Spec(σ)) ∘ (π_X × id)` is the `f`-fold absolute Frobenius of `X_K`. -/
public theorem geometricFrobeniusBaseChange_comp_galoisBaseChange (σ : K ≃ₐ[k] K)
    (hσ : ∀ x : K, σ x = x ^ p ^ f) :
    geometricFrobeniusBaseChange X K p f hcard ≫ galoisBaseChange X K σ =
      absoluteFrobeniusPow (fieldBaseChange X K) p
        (isInCharacteristic_fieldBaseChange X K p) f :=
  (comp_eq_absoluteFrobeniusPow_and X K p f hcard σ hσ).2

/-- The base change of the geometric Frobenius and the action of the arithmetic Frobenius
commute. -/
public theorem galoisBaseChange_comm_geometricFrobeniusBaseChange (σ : K ≃ₐ[k] K)
    (hσ : ∀ x : K, σ x = x ^ p ^ f) :
    galoisBaseChange X K σ ≫ geometricFrobeniusBaseChange X K p f hcard =
      geometricFrobeniusBaseChange X K p f hcard ≫ galoisBaseChange X K σ := by
  rw [galoisBaseChange_comp_geometricFrobeniusBaseChange X K p f hcard σ hσ,
    geometricFrobeniusBaseChange_comp_galoisBaseChange X K p f hcard σ hσ]

end BaseChange

section EtaleSite

variable {k : Type u} [Field k] [Fintype k] (X : Over (Spec (.of k)))
  (K : Type u) [Field K] [Algebra k K] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f) (σ : K ≃ₐ[k] K) (hσ : ∀ x : K, σ x = x ^ p ^ f)

/-- Base change along the composite `(π_X × id) ∘ (id_X × Spec(frob_k))` is isomorphic to the
identity functor of the small étale site of `X_K`. -/
public def compEtaleSiteIso :
    𝟭 (fieldBaseChange X K).Etale ≅
      smallEtaleBaseChange
        (galoisBaseChange X K σ ≫ geometricFrobeniusBaseChange X K p f hcard) :=
  absoluteFrobeniusPowEtaleSiteIso (fieldBaseChange X K) p
      (isInCharacteristic_fieldBaseChange X K p) (ne_zero_of_card_eq_pow hcard) ≪≫
    eqToIso (show smallEtaleBaseChange (absoluteFrobeniusPow (fieldBaseChange X K) p
          (isInCharacteristic_fieldBaseChange X K p) f) =
        smallEtaleBaseChange
          (galoisBaseChange X K σ ≫ geometricFrobeniusBaseChange X K p f hcard) from by
      rw [galoisBaseChange_comp_geometricFrobeniusBaseChange X K p f hcard σ hσ])

/-- Base change along `π_X × id` followed by base change along `id_X × Spec(frob_k)` is
isomorphic to the identity functor of the small étale site of `X_K`. -/
public def galoisCompGeometricFrobeniusEtaleSiteIso :
    𝟭 (fieldBaseChange X K).Etale ≅
      smallEtaleBaseChange (geometricFrobeniusBaseChange X K p f hcard) ⋙
        smallEtaleBaseChange (galoisBaseChange X K σ) :=
  compEtaleSiteIso X K p f hcard σ hσ ≪≫
    smallEtaleBaseChangeComp (galoisBaseChange X K σ)
      (geometricFrobeniusBaseChange X K p f hcard)

/-- Base change along `id_X × Spec(frob_k)` followed by base change along `π_X × id` is
isomorphic to the identity functor of the small étale site of `X_K`. -/
public def geometricFrobeniusCompGaloisEtaleSiteIso :
    𝟭 (fieldBaseChange X K).Etale ≅
      smallEtaleBaseChange (galoisBaseChange X K σ) ⋙
        smallEtaleBaseChange (geometricFrobeniusBaseChange X K p f hcard) :=
  absoluteFrobeniusPowEtaleSiteIso (fieldBaseChange X K) p
      (isInCharacteristic_fieldBaseChange X K p) (ne_zero_of_card_eq_pow hcard) ≪≫
    eqToIso (show smallEtaleBaseChange (absoluteFrobeniusPow (fieldBaseChange X K) p
          (isInCharacteristic_fieldBaseChange X K p) f) =
        smallEtaleBaseChange
          (geometricFrobeniusBaseChange X K p f hcard ≫ galoisBaseChange X K σ) from by
      rw [geometricFrobeniusBaseChange_comp_galoisBaseChange X K p f hcard σ hσ]) ≪≫
    smallEtaleBaseChangeComp (geometricFrobeniusBaseChange X K p f hcard)
      (galoisBaseChange X K σ)

/-- Base change along the Galois action `id_X × Spec(frob_k)` of the arithmetic Frobenius is an
equivalence of the small étale site of `X_K`, and base change along `π_X × id` is a
quasi-inverse for it. -/
public def galoisBaseChangeEtaleEquivalence :
    (fieldBaseChange X K).Etale ≌ (fieldBaseChange X K).Etale :=
  CategoryTheory.Equivalence.mk (smallEtaleBaseChange (galoisBaseChange X K σ))
    (smallEtaleBaseChange (geometricFrobeniusBaseChange X K p f hcard))
    (geometricFrobeniusCompGaloisEtaleSiteIso X K p f hcard σ hσ)
    (galoisCompGeometricFrobeniusEtaleSiteIso X K p f hcard σ hσ).symm

/-- The equivalence of the small étale site induced by the Galois action of the arithmetic
Frobenius is base change along `id_X × Spec(frob_k)`. -/
@[simp]
public lemma galoisBaseChangeEtaleEquivalence_functor :
    (galoisBaseChangeEtaleEquivalence X K p f hcard σ hσ).functor =
      smallEtaleBaseChange (galoisBaseChange X K σ) :=
  rfl

/-- Its quasi-inverse is base change along the base-changed geometric Frobenius. -/
@[simp]
public lemma galoisBaseChangeEtaleEquivalence_inverse :
    (galoisBaseChangeEtaleEquivalence X K p f hcard σ hσ).inverse =
      smallEtaleBaseChange (geometricFrobeniusBaseChange X K p f hcard) :=
  rfl

end EtaleSite

section Cohomology

variable {k : Type u} [Field k] [Fintype k] (X : Over (Spec (.of k)))
  (K : Type u) [Field K] [Algebra k K] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f) (σ : K ≃ₐ[k] K) (hσ : ∀ x : K, σ x = x ^ p ^ f)
  [HasWeakSheafify (smallEtaleTopology (fieldBaseChange X K))
    AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (smallEtaleTopology (fieldBaseChange X K)) AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf (smallEtaleTopology (fieldBaseChange X K))
    AddCommGrpCat.{max (u + 1) v})]
  [∀ F : (fieldBaseChange X K).Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange (galoisBaseChange X K σ ≫
      geometricFrobeniusBaseChange X K p f hcard)).op.HasLeftKanExtension F]

/-- In every degree `n` and for arbitrary abelian coefficients, inverse image along `π_X × id`,
then inverse image along the Galois action `id_X × Spec(frob_k)` of the arithmetic Frobenius,
then étale cohomology, is canonically isomorphic to étale cohomology. -/
public def galoisCompGeometricFrobeniusCohomologyIso (n : ℕ) :
    (etaleAbelianInverseImage.{u, v} (geometricFrobeniusBaseChange X K p f hcard) ⋙
        etaleAbelianInverseImage.{u, v} (galoisBaseChange X K σ)) ⋙
      Sheaf.functorH (smallEtaleTopology (fieldBaseChange X K)) n ≅
      Sheaf.functorH (smallEtaleTopology (fieldBaseChange X K)) n :=
  Functor.isoWhiskerRight
      (etaleAbelianInverseImageCompIso.{u, v} (galoisBaseChange X K σ)
          (geometricFrobeniusBaseChange X K p f hcard)).symm
      (Sheaf.functorH (smallEtaleTopology (fieldBaseChange X K)) n) ≪≫
    etaleCohomologyFunctorIsoOfBaseChangeIso.{u, v, w} (fieldBaseChange X K)
      (galoisBaseChange X K σ ≫ geometricFrobeniusBaseChange X K p f hcard)
      (compEtaleSiteIso X K p f hcard σ hσ) n

/-- For an abelian sheaf `F` on the small étale site of `X_K` and every degree `n`, the
cohomology of the inverse image of `F` along `π_X × id` and then along the Galois action of the
arithmetic Frobenius is canonically isomorphic to the cohomology of `F`. -/
public def galoisCompGeometricFrobeniusCohomologyAddEquiv (n : ℕ)
    (F : Sheaf (smallEtaleTopology (fieldBaseChange X K)) AddCommGrpCat.{max (u + 1) v}) :
    Sheaf.H.{w}
        ((etaleAbelianInverseImage.{u, v} (galoisBaseChange X K σ)).obj
          ((etaleAbelianInverseImage.{u, v}
            (geometricFrobeniusBaseChange X K p f hcard)).obj F)) n ≃+
      Sheaf.H.{w} F n :=
  ((galoisCompGeometricFrobeniusCohomologyIso.{u, v, w} X K p f hcard σ hσ n).app
    F).addCommGroupIsoToAddEquiv

end Cohomology

section ArithmeticFrobenius

variable {k : Type u} [Field k] [Fintype k] (X : Over (Spec (.of k)))
  (K : Type u) [Field K] [Algebra k K] (p f : ℕ) [Fact p.Prime] [CharP k p]
  [ExpChar K p] [PerfectRing K p] (hcard : Fintype.card k = p ^ f)

/-- For the arithmetic Frobenius `frob_k` of `K`, the composite
`(π_X × id) ∘ (id_X × Spec(frob_k))` is the `f`-fold absolute Frobenius of `X_K`. -/
public theorem arithmeticFrobenius_comp_geometricFrobeniusBaseChange :
    galoisBaseChange X K (arithmeticFrobenius k K p f hcard) ≫
        geometricFrobeniusBaseChange X K p f hcard =
      absoluteFrobeniusPow (fieldBaseChange X K) p
        (isInCharacteristic_fieldBaseChange X K p) f :=
  galoisBaseChange_comp_geometricFrobeniusBaseChange X K p f hcard
    (arithmeticFrobenius k K p f hcard) fun x ↦ by
      rw [arithmeticFrobenius_apply, hcard]

/-- For the arithmetic Frobenius `frob_k` of `K`, the composite
`(id_X × Spec(frob_k)) ∘ (π_X × id)` is the `f`-fold absolute Frobenius of `X_K`. -/
public theorem geometricFrobeniusBaseChange_comp_arithmeticFrobenius :
    geometricFrobeniusBaseChange X K p f hcard ≫
        galoisBaseChange X K (arithmeticFrobenius k K p f hcard) =
      absoluteFrobeniusPow (fieldBaseChange X K) p
        (isInCharacteristic_fieldBaseChange X K p) f :=
  geometricFrobeniusBaseChange_comp_galoisBaseChange X K p f hcard
    (arithmeticFrobenius k K p f hcard) fun x ↦ by
      rw [arithmeticFrobenius_apply, hcard]

end ArithmeticFrobenius

section CohomologyEndo

variable {k : Type u} [Field k] [Fintype k] (X : Over (Spec (.of k)))
  (K : Type u) [Field K] [Algebra k K] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f) (σ : K ≃ₐ[k] K) (hσ : ∀ x : K, σ x = x ^ p ^ f)

/-- The projection `X_K ⟶ X` of the base change of `X` to the extension field `K`. -/
@[ega "IV 6.7.7"]
public abbrev fieldBaseChangeProj : fieldBaseChange X K ⟶ X.left :=
  pullback.fst X.hom (specAlgebraMap k K)

/-- `π_X × id` lies over the `f`-fold absolute Frobenius of `X`. -/
public lemma fieldBaseChangeProj_comp_absoluteFrobeniusPow :
    fieldBaseChangeProj X K ≫
        absoluteFrobeniusPow X.left p (isInCharacteristic_of_over X) f =
      geometricFrobeniusBaseChange X K p f hcard ≫ fieldBaseChangeProj X K :=
  (geometricFrobeniusBaseChange_comp_fst X K p f hcard).symm

section Coefficients

variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (fieldBaseChange X K).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange
      (absoluteFrobeniusPow X.left p (isInCharacteristic_of_over X) f)).op.HasLeftKanExtension G]

/-- **The coefficient identification along the Galois action.** Since `id_X × Spec(σ)` is a
morphism over `X`, the restriction to `X_K` of a sheaf on `X_étale` is canonically identified
with its inverse image along that morphism. -/
public def galoisRestrictionCoeff
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImage.{u, v} (galoisBaseChange X K σ)).obj
        ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F) ⟶
      (etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F :=
  (etaleAbelianInverseImageCompIso'.{u, v} (galoisBaseChange X K σ) (fieldBaseChangeProj X K)
    (fieldBaseChangeProj X K) (galoisBaseChange_comp_fst X K σ).symm).inv.app F

/-- **The coefficient identification along the base-changed geometric Frobenius.** Since
`π_X × id` lies over the geometric Frobenius `π_X` of `X`, the restriction to `X_K` of a sheaf
on `X_étale` is identified with its inverse image along that morphism, through the Frobenius
descent of Tag 03SR on `X`. -/
public def geometricFrobeniusRestrictionCoeff
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImage.{u, v} (geometricFrobeniusBaseChange X K p f hcard)).obj
        ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F) ⟶
      (etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F :=
  (frobeniusRestrictionCoeffFrob.{u, v} (fieldBaseChangeProj X K) p
    (isInCharacteristic_of_over X) (ne_zero_of_card_eq_pow hcard)
    (geometricFrobeniusBaseChange X K p f hcard)
    (fieldBaseChangeProj X K ≫
      absoluteFrobeniusPow X.left p (isInCharacteristic_of_over X) f)
    (fieldBaseChangeProj_comp_absoluteFrobeniusPow X K p f hcard) rfl).app F

end Coefficients

variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (fieldBaseChange X K).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf (fieldBaseChange X K).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange
      (absoluteFrobeniusPow X.left p (isInCharacteristic_of_over X) f)).op.HasLeftKanExtension G]
  [∀ G : (fieldBaseChange X K).Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange (absoluteFrobeniusPow (fieldBaseChange X K) p
      (isInCharacteristic_fieldBaseChange X K p) f)).op.HasLeftKanExtension G]

include hσ in
/-- Let `k` be a finite field with `q = p ^ f` elements, let `X` be a scheme over `k`, let
`K/k` be an extension and let `σ` be the arithmetic Frobenius `x ↦ x ^ q` of `K`. For an
abelian sheaf `ℱ` on `X_étale` and every degree `j`, the endomorphism of `H^j(X_K, ℱ|_{X_K})`
induced by the Galois action `id_X × Spec(σ)` undoes the one induced by `π_X × id`: the
arithmetic Frobenius acts as the inverse of `π_X^*`.

Each endomorphism restricts along the morphism of `X_K` and then identifies the coefficients
again: along `X` for the Galois action (`galoisRestrictionCoeff`), and through the Frobenius
descent on `X` for the geometric Frobenius (`geometricFrobeniusRestrictionCoeff`). -/
@[stacks 03SV "the Galois action of frob_k after the map induced by the geometric Frobenius \
is the identity"]
public theorem galoisRestrictionEndo_comp_geometricFrobeniusRestrictionEndo (n : ℕ)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleCohomologyEndo.{u, v, w} (galoisBaseChange X K σ)
          ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F)
          (galoisRestrictionCoeff.{u, v} X K σ F) n).comp
        (etaleCohomologyEndo.{u, v, w} (geometricFrobeniusBaseChange X K p f hcard)
          ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F)
          (geometricFrobeniusRestrictionCoeff.{u, v} X K p f hcard F) n) =
      AddMonoidHom.id (Sheaf.H.{w}
        ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F) n) :=
  etaleCohomologyEndo_comp.{u, v, w} (galoisBaseChange X K σ)
    (geometricFrobeniusBaseChange X K p f hcard)
    (frobeniusRestrictionUnit.{u, v} p (isInCharacteristic_fieldBaseChange X K p)
      (ne_zero_of_card_eq_pow hcard) (galoisBaseChange X K σ)
      (geometricFrobeniusBaseChange X K p f hcard)
      (galoisBaseChange_comp_geometricFrobeniusBaseChange X K p f hcard σ hσ).symm)
    _ _ _
    (frobeniusRestrictionConstantCoherence.{u, v} p
      (isInCharacteristic_fieldBaseChange X K p) (ne_zero_of_card_eq_pow hcard)
      (galoisBaseChange X K σ) (geometricFrobeniusBaseChange X K p f hcard)
      (galoisBaseChange_comp_geometricFrobeniusBaseChange X K p f hcard σ hσ).symm
      (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)))
    (frobeniusRestrictionCoeffCoherence.{u, v} (fieldBaseChangeProj X K) p
      (isInCharacteristic_of_over X) (isInCharacteristic_fieldBaseChange X K p)
      (ne_zero_of_card_eq_pow hcard) (galoisBaseChange X K σ)
      (geometricFrobeniusBaseChange X K p f hcard) (galoisBaseChange_comp_fst X K σ).symm
      (fieldBaseChangeProj X K ≫
        absoluteFrobeniusPow X.left p (isInCharacteristic_of_over X) f)
      (fieldBaseChangeProj_comp_absoluteFrobeniusPow X K p f hcard) rfl
      (galoisBaseChange_comp_geometricFrobeniusBaseChange X K p f hcard σ hσ).symm F) n

include hσ in
/-- With the data of `galoisRestrictionEndo_comp_geometricFrobeniusRestrictionEndo`, the
endomorphism of `H^j(X_K, ℱ|_{X_K})` induced by `π_X × id` undoes the one induced by the Galois
action `id_X × Spec(σ)`; so the two endomorphisms are mutually inverse. -/
@[stacks 03SV "the map induced by the geometric Frobenius after the Galois action of frob_k \
is the identity"]
public theorem geometricFrobeniusRestrictionEndo_comp_galoisRestrictionEndo (n : ℕ)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleCohomologyEndo.{u, v, w} (geometricFrobeniusBaseChange X K p f hcard)
          ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F)
          (geometricFrobeniusRestrictionCoeff.{u, v} X K p f hcard F) n).comp
        (etaleCohomologyEndo.{u, v, w} (galoisBaseChange X K σ)
          ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F)
          (galoisRestrictionCoeff.{u, v} X K σ F) n) =
      AddMonoidHom.id (Sheaf.H.{w}
        ((etaleAbelianInverseImage.{u, v} (fieldBaseChangeProj X K)).obj F) n) :=
  etaleCohomologyEndo_comp.{u, v, w} (geometricFrobeniusBaseChange X K p f hcard)
    (galoisBaseChange X K σ)
    (frobeniusRestrictionUnit.{u, v} p (isInCharacteristic_fieldBaseChange X K p)
      (ne_zero_of_card_eq_pow hcard) (geometricFrobeniusBaseChange X K p f hcard)
      (galoisBaseChange X K σ)
      (geometricFrobeniusBaseChange_comp_galoisBaseChange X K p f hcard σ hσ).symm)
    _ _ _
    (frobeniusRestrictionConstantCoherence.{u, v} p
      (isInCharacteristic_fieldBaseChange X K p) (ne_zero_of_card_eq_pow hcard)
      (geometricFrobeniusBaseChange X K p f hcard) (galoisBaseChange X K σ)
      (geometricFrobeniusBaseChange_comp_galoisBaseChange X K p f hcard σ hσ).symm
      (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ)))
    (frobeniusRestrictionCoeffCoherence'.{u, v} (fieldBaseChangeProj X K) p
      (isInCharacteristic_of_over X) (isInCharacteristic_fieldBaseChange X K p)
      (ne_zero_of_card_eq_pow hcard) (galoisBaseChange X K σ)
      (geometricFrobeniusBaseChange X K p f hcard) (galoisBaseChange_comp_fst X K σ).symm
      (fieldBaseChangeProj X K ≫
        absoluteFrobeniusPow X.left p (isInCharacteristic_of_over X) f)
      (fieldBaseChangeProj_comp_absoluteFrobeniusPow X K p f hcard) rfl
      (geometricFrobeniusBaseChange_comp_galoisBaseChange X K p f hcard σ hσ).symm F) n

end CohomologyEndo

end Stacks.Frobenius

end
