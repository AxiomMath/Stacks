module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.FieldTheory.InseparableDegreeBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The fibre of a residue-field base change of a morphism of schemes

Let `k` and `k'` be fields, let `Y` be a `k`-scheme and let `Z = Y ×_{Spec k} Spec k'`, with
`N : Z ⟶ Y` the projection. For a point `z` of `Z` with image `y = N z` the scheme-theoretic
fibre of `N` through `z` is the spectrum of `k' ⊗_k κ(y)`, so the local ring of that fibre at
the point determined by `z` is the localization of `k' ⊗_k κ(y)` at a prime `t`, and `κ(z)` is
the residue field at `t`. Combined with the field-theoretic identity
`Field.length_atPrime_mul_finInsepDegree_eq_finInsepDegree` this gives

`length(O) * [κ(z) : k']_i = [κ(y) : k]_i`

whenever `κ(y)` is finite over `k`, `O` being the local ring of the fibre of `N` through `z`.
This is the geometric half of the first paragraph of the proof of Stacks tag `0H5P`, where the
cartesian square is the one of Stacks tag `0H4N` expressing the fibre of a base change as a
residue-field base change of a fibre.

## Main results

* `Stacks.Chow.residueFieldAlgebraMap_comp` — a morphism of schemes over `Spec A` induces a map
  of `A`-algebras on residue fields.
* `Stacks.Chow.residueFieldAlgebraMap_specMap` — restricting the base along `A ⟶ B` restricts
  the induced algebra structure on a residue field.
* `Stacks.Chow.residueFieldAlgebraMap_fiberResidueFieldHom` — the comparison map between the
  residue field at a point and the residue field of a fibre at the corresponding point is a map
  of `A`-algebras for any affine base of the source.
* `Stacks.Chow.surjective_algebraMap_residueField_spec` — at a closed point of an affine scheme
  the ring surjects onto the residue field, with kernel the prime of that point.
* `Stacks.Chow.length_stalk_of_isoSpec` — through an isomorphism with an affine scheme, the local
  ring at a point is the localization at the corresponding prime.
* `Stacks.Chow.exists_surjective_residueField_of_isoSpec` — the residue field at a point whose
  prime is maximal in an affine model is a quotient of the ring of that model, as an algebra over
  any affine base.
* `Stacks.Chow.length_fiberStalk_mul_finInsepDegree_eq` — the displayed identity above.

## Implementation notes

The `A`-algebra structure a morphism `g : Z ⟶ Spec A` puts on a residue field of `Z` is the one
of `AlgebraicGeometry.SpecMap_algebraMap_residueField`, written through global sections and
evaluation; it is never an instance, and every statement introduces the structures it uses in
its own `let` bindings. Each of the three compatibility lemmas takes the structure morphism of
the source as a separate argument together with an equation identifying it with a composite, so
that a caller can present that morphism in whichever form the surrounding development uses: the
algebra structures are definitionally tied to the morphism, so an equation between morphisms
cannot be rewritten inside an instance after the fact.

The identification of the fibre with a spectrum is obtained by pasting the cartesian square
defining the fibre onto the given one and feeding the result to
`AlgebraicGeometry.pullbackSpecIso`. The length is read off through
`AlgebraicGeometry.Spec.stalkIso`, and the residue field through the surjection
`Ideal.algebraMap_residueField_surjective`, which needs the prime to be maximal; it is, because
`k' ⊗_k κ(y)` is a finite `k'`-algebra and hence artinian.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-! ### Algebra structures on residue fields -/

/-- A morphism `m : X ⟶ Y` of schemes over `Spec A` induces a map of `A`-algebras on residue
fields: the `A`-algebra structures are the ones cut out by the two structure morphisms, and
`Scheme.Hom.residueFieldMap` intertwines them. -/
theorem residueFieldAlgebraMap_comp {X Y : Scheme.{u}} {A : CommRingCat.{u}}
    (hY : Y ⟶ Spec A) (hX : X ⟶ Spec A) (m : X ⟶ Y) (hm : m ≫ hY = hX) (x : X) :
    letI : Algebra A (Y.residueField (m x)) :=
      ((Scheme.ΓSpecIso A).inv ≫ hY.appTop ≫ Y.Γevaluation (m x)).hom.toAlgebra
    letI : Algebra A (X.residueField x) :=
      ((Scheme.ΓSpecIso A).inv ≫ hX.appTop ≫ X.Γevaluation x).hom.toAlgebra
    CommRingCat.ofHom (algebraMap A (X.residueField x)) =
      CommRingCat.ofHom (algebraMap A (Y.residueField (m x))) ≫ m.residueFieldMap x := by
  subst hm
  let _ : Algebra A (Y.residueField (m x)) :=
    ((Scheme.ΓSpecIso A).inv ≫ hY.appTop ≫ Y.Γevaluation (m x)).hom.toAlgebra
  let _ : Algebra A (X.residueField x) :=
    ((Scheme.ΓSpecIso A).inv ≫ (m ≫ hY).appTop ≫ X.Γevaluation x).hom.toAlgebra
  apply Spec.map_injective
  rw [Spec.map_comp, SpecMap_algebraMap_residueField hY (m x),
    SpecMap_algebraMap_residueField (m ≫ hY) x, ← Category.assoc, ← Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField m x]

/-- Restricting the base of a residue field along `φ : A ⟶ B` composes the algebra map with
`φ`: the `A`-algebra structure cut out by `hV ≫ Spec φ` is the `B`-algebra structure cut out by
`hV`, read through `φ`. -/
theorem residueFieldAlgebraMap_specMap {V : Scheme.{u}} {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hV : V ⟶ Spec B) (hV' : V ⟶ Spec A) (hφ : hV ≫ Spec.map φ = hV') (v : V) :
    letI : Algebra B (V.residueField v) :=
      ((Scheme.ΓSpecIso B).inv ≫ hV.appTop ≫ V.Γevaluation v).hom.toAlgebra
    letI : Algebra A (V.residueField v) :=
      ((Scheme.ΓSpecIso A).inv ≫ hV'.appTop ≫ V.Γevaluation v).hom.toAlgebra
    CommRingCat.ofHom (algebraMap A (V.residueField v)) =
      φ ≫ CommRingCat.ofHom (algebraMap B (V.residueField v)) := by
  subst hφ
  let _ : Algebra B (V.residueField v) :=
    ((Scheme.ΓSpecIso B).inv ≫ hV.appTop ≫ V.Γevaluation v).hom.toAlgebra
  let _ : Algebra A (V.residueField v) :=
    ((Scheme.ΓSpecIso A).inv ≫ (hV ≫ Spec.map φ).appTop ≫ V.Γevaluation v).hom.toAlgebra
  apply Spec.map_injective
  rw [Spec.map_comp, SpecMap_algebraMap_residueField hV v,
    SpecMap_algebraMap_residueField (hV ≫ Spec.map φ) v, Category.assoc]

/-- The comparison map from the residue field at a point `x` to the residue field of the fibre
of `m` through `x` is a map of `A`-algebras, for the structures cut out on the two residue
fields by a morphism `hX : X ⟶ Spec A` and by its restriction to the fibre. -/
theorem residueFieldAlgebraMap_fiberResidueFieldHom {X Y : Scheme.{u}} {A : CommRingCat.{u}}
    (hX : X ⟶ Spec A) (m : X ⟶ Y) (x : X)
    (hW : m.fiber (m x) ⟶ Spec A) (hmW : m.fiberι (m x) ≫ hX = hW) :
    letI : Algebra A (X.residueField x) :=
      ((Scheme.ΓSpecIso A).inv ≫ hX.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra A ((m.fiber (m x)).residueField (m.asFiber x)) :=
      ((Scheme.ΓSpecIso A).inv ≫ hW.appTop ≫
        (m.fiber (m x)).Γevaluation (m.asFiber x)).hom.toAlgebra
    CommRingCat.ofHom (algebraMap A ((m.fiber (m x)).residueField (m.asFiber x))) =
      CommRingCat.ofHom (algebraMap A (X.residueField x)) ≫ m.fiberResidueFieldHom x := by
  subst hmW
  let _ : Algebra A (X.residueField x) :=
    ((Scheme.ΓSpecIso A).inv ≫ hX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let _ : Algebra A ((m.fiber (m x)).residueField (m.asFiber x)) :=
    ((Scheme.ΓSpecIso A).inv ≫ (m.fiberι (m x) ≫ hX).appTop ≫
      (m.fiber (m x)).Γevaluation (m.asFiber x)).hom.toAlgebra
  apply Spec.map_injective
  rw [Spec.map_comp, SpecMap_algebraMap_residueField hX x,
    SpecMap_algebraMap_residueField (m.fiberι (m x) ≫ hX) (m.asFiber x), ← Category.assoc,
    ← Category.assoc, Scheme.Hom.SpecMap_fiberResidueFieldHom m x]

/-! ### The residue field of an affine scheme at a closed point -/

/-- Evaluating an equation `f = g ≫ h` of ring homomorphisms at an element. -/
private theorem hom_apply_eq_of_eq_comp {A B C : CommRingCat.{u}} {f : A ⟶ C} {g : A ⟶ B}
    {h : B ⟶ C} (H : f = g ≫ h) (a : A) : f.hom a = h.hom (g.hom a) := by
  rw [H]
  rfl

/-- At a closed point of an affine scheme the algebra map from the ring to the residue field is
surjective with kernel the prime of that point: it is the algebra map to `Ideal.ResidueField`
of the prime, followed by an isomorphism. -/
theorem surjective_algebraMap_residueField_spec (R : CommRingCat.{u}) (p : Spec R)
    (hmax : p.asIdeal.IsMaximal) :
    letI : Algebra R ((Spec R).residueField p) :=
      ((Scheme.ΓSpecIso R).inv ≫ Scheme.Hom.appTop (𝟙 (Spec R)) ≫
        (Spec R).Γevaluation p).hom.toAlgebra
    Function.Surjective (algebraMap R ((Spec R).residueField p)) ∧
      RingHom.ker (algebraMap R ((Spec R).residueField p)) = p.asIdeal := by
  let _ : Algebra R ((Spec R).residueField p) :=
    ((Scheme.ΓSpecIso R).inv ≫ Scheme.Hom.appTop (𝟙 (Spec R)) ≫
      (Spec R).Γevaluation p).hom.toAlgebra
  have : p.asIdeal.IsPrime := hmax.isPrime
  have halg : CommRingCat.ofHom (algebraMap R ((Spec R).residueField p)) =
      CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R p).inv := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv R p]
    rfl
  have hbij : Function.Bijective (Scheme.Spec.residueFieldIso R p).inv.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hfun : (algebraMap R ((Spec R).residueField p)) =
      (Scheme.Spec.residueFieldIso R p).inv.hom.comp
        (algebraMap R p.asIdeal.ResidueField) := by
    simpa only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
      using congrArg CommRingCat.Hom.hom halg
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hbij.surjective.comp p.asIdeal.algebraMap_residueField_surjective
  · rw [← Ideal.ker_algebraMap_residueField (I := p.asIdeal), hfun]
    exact RingHom.ker_comp_of_injective _ hbij.injective

/-! ### Reading a residue field and a local ring off an affine model -/

/-- The local ring of a scheme at a point is, through an isomorphism with an affine scheme, the
localization of the ring at the corresponding prime. -/
theorem length_stalk_of_isoSpec (R : Type u) [CommRing R] {W : Scheme.{u}}
    (e : W ≅ Spec (.of R)) (w : W) (q : PrimeSpectrum R) (hq : e.hom w = q) :
    Module.length (W.presheaf.stalk w) (W.presheaf.stalk w) =
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) := by
  subst hq
  have : IsIso (e.hom.stalkMap w) := ((isIso_iff_isIso_stalkMap e.hom).mp inferInstance).2 _
  exact Module.length_self_eq_of_ringEquiv
    ((asIso (e.hom.stalkMap w)).commRingCatIsoToRingEquiv.symm.trans
      (Spec.stalkIso (.of R) (e.hom w)).commRingCatIsoToRingEquiv)

/-- At a point whose prime is maximal in an affine model, the residue field of a scheme is a
quotient of the ring of that model: there is a surjection from the ring onto the residue field
with kernel that prime, and it is a map of `A`-algebras for any affine base `Spec A` of the
scheme over which the model is taken. -/
theorem exists_surjective_residueField_of_isoSpec (R A : Type u) [CommRing R] [CommRing A]
    [Algebra A R] {W : Scheme.{u}} (e : W ≅ Spec (.of R)) (w : W) (hW : W ⟶ Spec (.of A))
    (hfst : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)) = hW)
    (q : PrimeSpectrum R) (hq : e.hom w = q) (hmax : q.asIdeal.IsMaximal) :
    letI : Algebra A (W.residueField w) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ hW.appTop ≫ W.Γevaluation w).hom.toAlgebra
    ∃ φ : R →+* (W.residueField w : Type u), Function.Surjective φ ∧
      RingHom.ker φ = q.asIdeal ∧
      ∀ a : A, φ (algebraMap A R a) = algebraMap A (W.residueField w) a := by
  subst hq
  let _ : Algebra A (W.residueField w) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ hW.appTop ≫ W.Γevaluation w).hom.toAlgebra
  let _ : Algebra R ((Spec (.of R)).residueField (e.hom w)) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Hom.appTop (𝟙 (Spec (.of R))) ≫
      (Spec (.of R)).Γevaluation (e.hom w)).hom.toAlgebra
  let _ : Algebra A ((Spec (.of R)).residueField (e.hom w)) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A R))).appTop ≫
      (Spec (.of R)).Γevaluation (e.hom w)).hom.toAlgebra
  obtain ⟨hsurj0, hker0⟩ :=
    surjective_algebraMap_residueField_spec (.of R) (e.hom w) hmax
  have hbase := residueFieldAlgebraMap_specMap (CommRingCat.ofHom (algebraMap A R)) (𝟙 _)
    (Spec.map (CommRingCat.ofHom (algebraMap A R))) (Category.id_comp _) (e.hom w)
  have hiso := residueFieldAlgebraMap_comp (Spec.map (CommRingCat.ofHom (algebraMap A R))) hW
    e.hom hfst w
  have hrbij : Function.Bijective (e.hom.residueFieldMap w).hom :=
    Scheme.Hom.bijective_residueFieldMap e.hom w
  refine ⟨(e.hom.residueFieldMap w).hom.comp
    (algebraMap R ((Spec (.of R)).residueField (e.hom w))), hrbij.surjective.comp hsurj0,
    ?_, ?_⟩
  · rw [← hker0]
    exact RingHom.ker_comp_of_injective _ hrbij.injective
  · intro a
    have h1 := hom_apply_eq_of_eq_comp hbase a
    have h2 := hom_apply_eq_of_eq_comp hiso a
    simp only [CommRingCat.hom_ofHom] at h1 h2
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← h1, ← h2]

/-! ### The fibre of a residue-field base change -/

/-- **Stacks Project, Tag 0H5P, first paragraph.** Let `Z = Y ×_{Spec k} Spec k'` be a
residue-field base change of a `k`-scheme `Y`, with projection `N : Z ⟶ Y`, and let `z` be a
point of `Z` whose image `y = N z` has residue field finite over `k`. Then the length of the
local ring of the scheme-theoretic fibre of `N` through `z` times the inseparable degree of
`κ(z)` over `k'` is the inseparable degree of `κ(y)` over `k`.

The fibre of `N` through `z` is the spectrum of `k' ⊗_k κ(y)`; the local ring in question is a
localization of that ring at a prime and `κ(z)` is the residue field there, so the identity is
`Field.length_atPrime_mul_finInsepDegree_eq_finInsepDegree`. -/
theorem length_fiberStalk_mul_finInsepDegree_eq {Y Z : Scheme.{u}} (k k' : Type u) [Field k]
    [Field k'] [Algebra k k'] (F : Y ⟶ Spec (.of k)) (p' : Z ⟶ Spec (.of k')) (N : Z ⟶ Y)
    (hsq : IsPullback N p' F (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (z : Z)
    (hfin : letI : Algebra k (Y.residueField (N z)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ F.appTop ≫ Y.Γevaluation (N z)).hom.toAlgebra
      Module.Finite k (Y.residueField (N z))) :
    letI : Algebra k (Y.residueField (N z)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ F.appTop ≫ Y.Γevaluation (N z)).hom.toAlgebra
    letI : Algebra k' (Z.residueField z) :=
      ((Scheme.ΓSpecIso (.of k')).inv ≫ p'.appTop ≫ Z.Γevaluation z).hom.toAlgebra
    (Module.length ((N.fiber (N z)).presheaf.stalk (N.asFiber z))
        ((N.fiber (N z)).presheaf.stalk (N.asFiber z))).toNat *
      Field.finInsepDegree k' (Z.residueField z) =
      Field.finInsepDegree k (Y.residueField (N z)) := by
  let _ : Algebra k (Y.residueField (N z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ F.appTop ≫ Y.Γevaluation (N z)).hom.toAlgebra
  let _ : Algebra k' (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ p'.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  have _ : Module.Finite k (Y.residueField (N z)) := hfin
  -- the fibre of `N` through `z` is the spectrum of `k' ⊗[k] κ(N z)`
  have hpaste : IsPullback (N.fiberToSpecResidueField (N z)) (N.fiberι (N z) ≫ p')
      (Y.fromSpecResidueField (N z) ≫ F)
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    (IsPullback.of_hasPullback N (Y.fromSpecResidueField (N z))).flip.paste_vert hsq
  rw [← SpecMap_algebraMap_residueField F (N z)] at hpaste
  let e : N.fiber (N z) ≅ Spec (.of (k' ⊗[k] (Y.residueField (N z)))) :=
    hpaste.flip.isoPullback ≪≫ pullbackSpecIso k k' (Y.residueField (N z))
  have hfst : e.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k' (k' ⊗[k] (Y.residueField (N z))))) = N.fiberι (N z) ≫ p' := by
    show (hpaste.flip.isoPullback.hom ≫
      (pullbackSpecIso k k' (Y.residueField (N z))).hom) ≫ _ = _
    rw [Category.assoc, pullbackSpecIso_hom_fst' k k' (Y.residueField (N z)),
      hpaste.flip.isoPullback_hom_fst]
  obtain ⟨q, hq⟩ :
      ∃ q : PrimeSpectrum (k' ⊗[k] (Y.residueField (N z))), e.hom (N.asFiber z) = q :=
    ⟨_, rfl⟩
  have : Module.Finite k' (k' ⊗[k] (Y.residueField (N z))) := Module.Finite.base_change k k' _
  have : IsArtinianRing (k' ⊗[k] (Y.residueField (N z))) := IsArtinianRing.of_finite k' _
  have hmax : q.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime q.asIdeal
  let _ : Algebra k' ((N.fiber (N z)).residueField (N.asFiber z)) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ (N.fiberι (N z) ≫ p').appTop ≫
      (N.fiber (N z)).Γevaluation (N.asFiber z)).hom.toAlgebra
  obtain ⟨φ₀, hsurj0, hker0, hcomm0⟩ := exists_surjective_residueField_of_isoSpec
    (k' ⊗[k] (Y.residueField (N z))) k' e (N.asFiber z) (N.fiberι (N z) ≫ p') hfst q hq hmax
  have hfib := residueFieldAlgebraMap_fiberResidueFieldHom p' N z (N.fiberι (N z) ≫ p') rfl
  let ρ : (Z.residueField z : Type u) ≃+*
      ((N.fiber (N z)).residueField (N.asFiber z) : Type u) :=
    RingEquiv.ofBijective (N.fiberResidueFieldHom z).hom (N.bijective_fiberResidueFieldHom z)
  have hker : RingHom.ker (ρ.symm.toRingHom.comp φ₀) = q.asIdeal :=
    (RingHom.ker_comp_of_injective φ₀ (by exact ρ.symm.injective)).trans hker0
  have hcomm : ∀ a : k', (ρ.symm.toRingHom.comp φ₀)
        (algebraMap k' (k' ⊗[k] (Y.residueField (N z))) a) =
      algebraMap k' (Z.residueField z) a := by
    intro a
    have h3 := hom_apply_eq_of_eq_comp hfib a
    simp only [CommRingCat.hom_ofHom] at h3
    simp only [RingHom.coe_comp, Function.comp_apply, hcomm0 a]
    rw [h3]
    exact ρ.symm_apply_apply _
  rw [length_stalk_of_isoSpec (k' ⊗[k] (Y.residueField (N z))) e (N.asFiber z) q hq]
  exact Field.length_atPrime_mul_finInsepDegree_eq_finInsepDegree k k'
    (Y.residueField (N z)) q.asIdeal (Z.residueField z) (ρ.symm.toRingHom.comp φ₀)
    (ρ.symm.surjective.comp hsurj0) hker hcomm

end Stacks.Chow

end
