module

public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilPullbackAxiom

/-!
# De Rham cohomology along an extension of the base field

Let `k ⟶ k'` be an extension of fields, `X` a smooth projective scheme over `k` and `X'` a smooth
projective scheme over `k'` with a morphism `pr : X' ⟶ X` over `Spec k' ⟶ Spec k` (for instance
`X' = X_{k'}`). Pullback along the square of Section 0FL6 gives the base change map
`H^*_{dR}(X/k) ⟶ H^*_{dR}(X'/k')`. Section 0FWC reduces the axioms for de Rham cohomology to an
algebraically closed field through Lemma 0FVT, which takes as input the functorial isomorphisms
`H^*_{dR}(X/k) ⊗_k k' ⟶ H^*_{dR}(X_{k'}/k')` of Lemma 0FM0 compatible with the first Chern classes
(Lemma 0FMD). This file builds the base change map and proves its algebraic properties:

* it is a homomorphism of graded rings, `k`-semilinear along `k ⟶ k'`;
* it is natural in `X`;
* it carries `c₁^{dR}(ℒ)` to `c₁^{dR}(pr^*ℒ)`.

## Main definitions

* `Stacks.DeRhamWeil.baseChangePiece`: the base change map in one degree.
* `Stacks.DeRhamWeil.baseChangeRingHom`: `H^*_{dR}(X/k) ⟶ H^*_{dR}(X'/k')`, a ring homomorphism.

## Main results

* `Stacks.DeRhamWeil.baseChangeRingHom_algebraMap`: it sends `c ∈ k` to its image in `k'`.
* `Stacks.DeRhamWeil.baseChangeRingHom_mem_grade`: it is graded.
* `Stacks.DeRhamWeil.baseChangeRingHom_pullback`: **naturality** in `X`.
* `Stacks.DeRhamWeil.baseChangePiece_firstChernClassPiece`: **compatibility with `c₁^{dR}`**
  (Lemma 0FMD).

## References

* [Stacks Project, Section 0FWC](https://stacks.math.columbia.edu/tag/0FWC)
* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FVT](https://stacks.math.columbia.edu/tag/0FVT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry DirectSum
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.DeRhamWeil

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- The morphism `Spec k' ⟶ Spec k` of an extension of fields. -/
abbrev specMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Spec (.of k') ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

variable {X : (SmoothProjectiveScheme k).FullSubcategory}
  {X' : (SmoothProjectiveScheme k').FullSubcategory}
  (pr : (toScheme k').obj X' ⟶ (toScheme k).obj X)
  (w : pr ≫ X.obj.hom = X'.obj.hom ≫ specMap k k')

/-- **The base change map `H^n_{dR}(X/k) ⟶ H^n_{dR}(X'/k')`**: pullback along the square
`(pr, Spec k' ⟶ Spec k)`. -/
def baseChangePiece (n : ℤ) : piece X n →+ piece X' n :=
  deRhamPullbackSquare pr X'.obj.hom X.obj.hom (specMap k k') w n

/-- The scalar `c ∈ k` is carried to its image in `k'` by the map of base scalars of the square. -/
theorem globalRingHom_scalarHom (c : k) :
    (Stacks.Cohomology.LerayCupPairing.globalRingHom
        (inverseImageBaseMap pr X'.obj.hom X.obj.hom (specMap k k') w)).hom
      (scalarHom X.obj.hom c) = scalarHom X'.obj.hom (algebraMap k k' c) := by
  refine (globalRingHom_inverseImageBaseMap_baseScalarHom X.obj.hom pr X'.obj.hom
    (specMap k k') w _).trans ?_
  exact congrArg (baseScalarHom X'.obj.hom) (congrArg (fun φ => φ.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k k')))).symm

/-- The base change map is semilinear along `k ⟶ k'`. -/
theorem baseChangePiece_smul (n : ℤ) (c : k) (z : piece X n) :
    baseChangePiece pr w n (c • z) = algebraMap k k' c • baseChangePiece pr w n z :=
  (deRhamPullbackSquare_smul _ _ _ _ w n (scalarHom X.obj.hom c) z).trans
    (congrArg (· • _) (globalRingHom_scalarHom pr w c))

/-- The base change map carries the cup product `x ∪ y` to the cup product of the images. -/
theorem baseChangePiece_cup (i j : ℤ) (x : piece X i) (y : piece X j) :
    baseChangePiece pr w (i + j)
        (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X) (differential X) i j
          x y) =
      AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup (algebras X') (differential X') i j
        (baseChangePiece pr w i x) (baseChangePiece pr w j y) :=
  deRhamPullbackSquare_cup _ _ _ _ w i j x y

/-- The base change map carries the unit class of `H^0_{dR}(X/k)` to that of `H^0_{dR}(X'/k')`. -/
theorem baseChangePiece_one :
    baseChangePiece pr w 0 (AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras X)
        (differential X)) =
      AlgebraicGeometry.SheafOfModules.deRhamOneClass (algebras X') (differential X') :=
  deRhamPullbackSquare_one _ _ _ _ w

/-- **The base change map `H^*_{dR}(X/k) ⟶ H^*_{dR}(X'/k')`**, a homomorphism of rings. -/
def baseChangeRingHom : cohomology X →+* cohomology X' :=
  DirectSum.toSemiring (fun n => (DirectSum.of (piece X') n).comp (baseChangePiece pr w n))
    ((congrArg (DirectSum.of (piece X') 0) (baseChangePiece_one pr w)).trans rfl)
    (fun {i j} x y => by
      change DirectSum.of (piece X') (i + j) (baseChangePiece pr w (i + j)
          (AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup _ _ i j x y)) =
        DirectSum.of (piece X') i (baseChangePiece pr w i x) *
          DirectSum.of (piece X') j (baseChangePiece pr w j y)
      rw [baseChangePiece_cup, DirectSum.of_mul_of]
      rfl)

/-- On the summand of degree `n`, `baseChangeRingHom` is `baseChangePiece` in degree `n`. -/
theorem baseChangeRingHom_of (n : ℤ) (x : piece X n) :
    baseChangeRingHom pr w (DirectSum.of (piece X) n x) =
      DirectSum.of (piece X') n (baseChangePiece pr w n x) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The base change map sends `c ∈ k` to its image in `k'`. -/
theorem baseChangeRingHom_algebraMap (c : k) :
    baseChangeRingHom pr w (algebraMap k (cohomology X) c) =
      algebraMap k' (cohomology X') (algebraMap k k' c) := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply, baseChangeRingHom_of]
  change DirectSum.of (piece X') 0 (baseChangePiece pr w 0 (c • _)) = _
  rw [baseChangePiece_smul, baseChangePiece_one]
  rfl

/-- The base change map is graded. -/
theorem baseChangeRingHom_mem_grade (n : ℤ) (a : cohomology X) (ha : a ∈ grade X n) :
    baseChangeRingHom pr w a ∈ grade X' n := by
  obtain ⟨x, rfl⟩ := (DirectSum.mem_rangeGrading k _ n a).1 ha
  rw [baseChangeRingHom_of]
  exact of_mem_grade X' n _

/-- **The base change map is natural**: for `f : X ⟶ Y` over `k` and a lift `f' : X' ⟶ Y'` over
`k'` with `pr_Y ∘ f' = f ∘ pr_X`, base change commutes with pullback. -/
theorem baseChangeRingHom_pullback {Y : (SmoothProjectiveScheme k).FullSubcategory}
    {Y' : (SmoothProjectiveScheme k').FullSubcategory} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (prY : (toScheme k').obj Y' ⟶ (toScheme k).obj Y)
    (wY : prY ≫ Y.obj.hom = Y'.obj.hom ≫ specMap k k')
    (h : (toScheme k').map f' ≫ prY = pr ≫ (toScheme k).map f) (a : cohomology Y) :
    baseChangeRingHom pr w (pullback f a) = pullback f' (baseChangeRingHom prY wY a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | of n y =>
    rw [pullback_of, baseChangeRingHom_of, baseChangeRingHom_of, pullback_of]
    refine congrArg (DirectSum.of (piece X') n) ?_
    refine (deRhamPullbackSquare_comp _ _ _ _ (square_w f) pr X'.obj.hom (specMap k k') w
      (by rw [Category.assoc, square_w f, Category.comp_id, w]; simp) n y).trans ?_
    refine (deRhamPullbackSquare_congr X'.obj.hom Y.obj.hom h.symm
      ((Category.comp_id (specMap k k')).trans (Category.id_comp _).symm) _
      (by rw [Category.assoc, wY, ← Category.assoc, square_w f']; simp) n y).trans ?_
    exact (deRhamPullbackSquare_comp prY Y'.obj.hom Y.obj.hom (specMap k k') wY _ X'.obj.hom
      (𝟙 _) (square_w f') _ n y).symm

/-- **Base change is compatible with the first Chern class** (Lemma 0FMD for the square
`(pr, Spec k' ⟶ Spec k)`): `c₁^{dR}(ℒ)` goes to `c₁^{dR}(pr^*ℒ)`. -/
theorem baseChangePiece_firstChernClassPiece (c : ((toScheme k).obj X).picardGroup) :
    baseChangePiece pr w 2 (firstChernClassPiece X c) =
      firstChernClassPiece X' (Stacks.Picard.schemePullbackClassHom pr c) := by
  have h := Scheme.Hom.deRhamFirstChernClassAbelian_schemePullbackClassHom pr X.obj.hom
    X'.obj.hom (specMap k k') w c
  let eX := AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (algebras X) (differential X) 2
  let eX' := AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (algebras X') (differential X') 2
  let P := Scheme.Hom.deRhamCohomologyPullback pr X.obj.hom X'.obj.hom (specMap k k') w 2
  let z := AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelian (algebras X)
    (differential X) (Stacks.GluePicard.picardModelAddEquiv _ c)
  change eX'.hom.hom (P.hom (eX.inv.hom (eX.hom.hom z))) = eX'.hom.hom _
  rw [Iso.hom_inv_id_apply]
  exact congrArg eX'.hom.hom h.symm

end Stacks.DeRhamWeil

end
