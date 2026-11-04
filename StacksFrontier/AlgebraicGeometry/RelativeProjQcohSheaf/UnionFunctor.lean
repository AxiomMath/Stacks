module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition

/-!
# The functor `F : Sch^{opp} ⟶ Sets` of the display 01NX

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN). Section 01NS attaches to a
test scheme `T` the quadruples `(d, f : T → S, L, ψ)` of a degree `d ≥ 1`, and their classes form
the set

`F(T) = ⋃_{d ≥ 1} F_d(T)`,

fibred over the morphisms `f : T ⟶ S`. The map `F(T) → F(T')` of a morphism `g : T' ⟶ T` of test
schemes is induced by the pullback of a quadruple. This file proves the two functor laws for that
map, and for the map `F_d(T) → F_d(T')` at a fixed degree, and bundles the results as functors
`Sch^{opp} ⟶ Sets`.

Pullback of sheaves of modules along an identity, or along a composite, is only isomorphic to the
identity functor, or to the composite of the pullbacks. So `P.pullback (𝟙 T)` is not equal to `P`,
and `(P.pullback g).pullback g'` is not equal to `P.pullback (g' ≫ g)`; in each case the two
quadruples are *strictly equivalent* (Section 01NS), and so define the same point of `F(T)`.

The functor `F.functor` takes the union for every test scheme. The display defines `F(T)` as this
union only for a quasi-compact `T`, and for a general `T` as the inverse limit of the sets `F(U)`
over the quasi-compact opens `U ⊆ T`; that functor is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limFunctor`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.functor`: the functor
  `F_d : Sch^{opp} ⟶ Sets` of Section 01NS at a fixed degree `d`, with `Fd A d T` on objects and
  `Fd.pullback` on morphisms.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.functor`: the functor
  `F : Sch^{opp} ⟶ Sets` of the display 01NX, with `F A T` on objects and `F.pullback` on
  morphisms.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.pullback_id` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.pullback_comp`: the two functor laws for the
  map `F_d(T) → F_d(T')` of a morphism of test schemes, at a fixed degree.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.pullback_id` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.pullback_comp`: the two functor laws for the
  map `F(T) → F(T')` of a morphism of test schemes.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_pullback_id` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_pullback_comp`: the
  pullback of a quadruple along an identity is strictly equivalent to the quadruple, and the
  pullback along a composite is strictly equivalent to the twice-pulled-back quadruple.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullbackApp_id` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullbackApp_comp`: the same two laws
  for the map `ψ` of a quadruple, up to the degreewise transport of the isomorphism of invertible
  modules.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.pieceIso_hom_eq_laurentPullback`: the two
  comparisons `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` of the integral tensor powers of Tag 01CU agree.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_comp`: the composition law of
  the comparison of the integral tensor powers, at the `laurentPullback` spelling.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.compComparison_id` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.compComparison_assoc`: the unit and
  associativity coherences of the contraction of an iterated pullback.

## Implementation notes

Several proofs below are terms built from `Eq.trans` and `congrArg` rather than `rw`: the goals
mix `Stacks.RingedSpace.structureRingSheaf` with `structureSheafRing`, and the composite
`g' ≫ g ≫ f` of morphisms of schemes with the composite of the underlying morphisms of ringed
spaces. Each pair is equal by `rfl` but not syntactically, so a `rw` either fails to find its
pattern or builds a motive that is not type-correct.

## References

* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentIdentity
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T'' T' T S : Scheme.{u}}

/-! ### The two comparisons of the integral tensor powers with pullback agree -/

section PieceIso

variable (k : T' ⟶ T) (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The successor law for `laurentPullback`: the comparison
`k^*(L^{⊗ (n+1)}) ≅ (k^*L)^{⊗ (n+1)}` is the comparison in degree `n` whiskered by `k^*L`, read
through the successor comparison of Tag 01CU upstairs and downstairs and the comparison of Tag
01CD. -/
theorem laurentPullback_succIso (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ laurentPullback k L (n + 1) =
      pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L ≫
        (laurentPullback k L n ▷ pullbackModule k L) ≫
          (succIso (pullbackModule k L) n).hom :=
  (mapTensorPowerIso_tensorPowerSuccIso T.toRingedSpace.presheaf (isSheafStruct T)
      T'.toRingedSpace.presheaf (isSheafStruct T') (pullbackFunctor (ringedSpaceHom k)) L
      (Stacks.TensorPowerPullback.tensorFactorComparison (ringedSpaceHom k) L)
      (Stacks.TensorPowerPullback.pullbackUnitSheafIso (ringedSpaceHom k)) n).trans
    (congrArg
      (fun z => pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L ≫ z ≫
        (succIso (pullbackModule k L) n).hom)
      (tensorRight_map (laurentPullback k L n) (pullbackModule k L)))

/-- The two comparisons agree in a single degree. -/
private abbrev PieceIsoEq (n : ℤ) : Prop :=
  (pieceIso k L n).hom = laurentPullback k L n

/-- If the two comparisons agree in degree `n`, they agree in degree `n + 1`. -/
private theorem pieceIsoEq_succ {n : ℤ} (h : PieceIsoEq k L n) : PieceIsoEq k L (n + 1) := by
  refine (Iso.cancel_iso_hom_left
    ((pullbackFunctor (ringedSpaceHom k)).mapIso (succIso L n)) _ _).mp ?_
  show (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ _ =
    (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ _
  rw [pieceIso_succIso, laurentPullback_succIso, h]

/-- If the two comparisons agree in degree `n + 1`, they agree in degree `n`. -/
private theorem pieceIsoEq_of_succ {n : ℤ} (h : PieceIsoEq k L (n + 1)) : PieceIsoEq k L n := by
  have h2 : (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫
        (pieceIso k L (n + 1)).hom =
      (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫
        laurentPullback k L (n + 1) :=
    congrArg (fun z => (pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom ≫ z) h
  rw [pieceIso_succIso, laurentPullback_succIso] at h2
  have h3 := (Iso.cancel_iso_hom_left (asIso (pullbackTensorComparison (ringedSpaceHom k)
    ((laurent L).piece n) L)) _ _).mp h2
  have h4 := (Iso.cancel_iso_hom_right _ _ (succIso (pullbackModule k L) n)).mp h3
  refine ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨T'.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ T'.toRingedSpace.presheaf
      (forget₂ CommRingCat RingCat) (isSheafStruct T')⟩).flip.obj
        (pullbackModule k L)).map_injective ?_
  exact (bridge_tensorRight T'.toRingedSpace.presheaf (isSheafStruct T')
      (pieceIso k L n).hom (pullbackModule k L)).trans
    (h4.trans (bridge_tensorRight T'.toRingedSpace.presheaf (isSheafStruct T')
      (laurentPullback k L n) (pullbackModule k L)).symm)

/-- The two comparisons `k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` of the integral tensor powers of Tag 01CU
agree in every integral degree: the one built by recursion on the degree, `pieceIso`, and the
tensor-power comparison `laurentPullback`. -/
theorem pieceIso_hom_eq_laurentPullback (n : ℤ) :
    (pieceIso k L n).hom = laurentPullback k L n := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ i ih => exact pieceIsoEq_succ k L ih
  | pred i ih => exact pieceIsoEq_of_succ k L (n := -(i : ℤ) - 1) (by rwa [sub_add_cancel])

end PieceIso

/-- The composition law for the comparison `laurentPullback` of the integral tensor powers:
comparing along `g` and then along `g'`, and transporting the result along the degreewise
comparison induced by the composition law `g'^*g^*L ≅ (g' ≫ g)^*L`, is contracting the iterated
pullback and comparing along `g' ≫ g`. -/
theorem laurentPullback_comp (g : T' ⟶ T) (g' : T'' ⟶ T')
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom g')).map (laurentPullback g L n) ≫
        laurentPullback g' (pullbackModule g L) n ≫ (congrIso (compCmp g' g L) n).hom =
      (compCmp g' g ((laurent L).piece n)).hom ≫ laurentPullback (g' ≫ g) L n := by
  rw [← pieceIso_hom_eq_laurentPullback, ← pieceIso_hom_eq_laurentPullback,
    ← pieceIso_hom_eq_laurentPullback]
  exact Eq.symm (pieceIso_comp g' g L n)

/-! ### The contraction of an iterated pullback, and its unit and associativity coherences -/

/-- The contraction `(k' ≫ k)^*M ⟶ k'^*(k^*M)` of an iterated pullback is the inverse of the
composition law `k'^*k^*M ≅ (k' ≫ k)^*M` for pullback. -/
theorem compComparison_eq_compCmp_inv (k' : T'' ⟶ T') (k : T' ⟶ T)
    (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    compComparison k' k M = (compCmp k' k M).inv := by
  refine pullback_hom_ext (ringedSpaceHom (k' ≫ k)) (fun U m => ?_)
  exact (Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom k)
      (ringedSpaceHom k') M U m).trans
    (pullbackCompIso_app_inv_pullbackUnit (ringedSpaceHom k') (ringedSpaceHom k) M U m).symm

/-- The contraction of an iterated pullback cancels the composition law for pullback. -/
theorem compComparison_comp_compCmp (k' : T'' ⟶ T') (k : T' ⟶ T)
    (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    compComparison k' k M ≫ (compCmp k' k M).hom =
      CategoryStruct.id ((pullbackFunctor (ringedSpaceHom (k' ≫ k))).obj M) := by
  rw [compComparison_eq_compCmp_inv, Iso.inv_hom_id]

/-- The unit coherence of the contraction of an iterated pullback: contracting
`(𝟙_T ∘ f)^*M = f^*M` into `(𝟙_T)^*(f^*M)` and then applying the identity law `(𝟙_T)^* ≅ 𝟭` for
pullback is the identity of `f^*M`. -/
theorem compComparison_id (f : T ⟶ S)
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    compComparison (𝟙 T) f M ≫
        (pullbackIdIso T.toRingedSpace).hom.app
          ((pullbackFunctor (ringedSpaceHom f)).obj M) =
      CategoryStruct.id ((pullbackFunctor (ringedSpaceHom f)).obj M) := by
  refine pullback_hom_ext (ringedSpaceHom f) (fun U m => ?_)
  exact (congrArg
    (fun z => ((pullbackIdIso T.toRingedSpace).hom.app
      ((pullbackFunctor (ringedSpaceHom f)).obj M)).val.app
        ((opensMap (ringedSpaceHom f)).op.obj U) z)
    (Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom f)
      (ringedSpaceHom (𝟙 T)) M U m)).trans
    (pullbackIdIso_hom_app_pullbackUnit T.toRingedSpace
      ((pullbackFunctor (ringedSpaceHom f)).obj M) ((opensMap (ringedSpaceHom f)).op.obj U)
      (pullbackUnit (ringedSpaceHom f) M U m))

/-- Associativity of the comparison maps `modulePullbackComparison` of iterated pullbacks of
ringed spaces. -/
private theorem modulePullbackComparison_assoc {X X' X'' X''' : RingedSpace.{u, u}}
    (f : X' ⟶ X) (g : X'' ⟶ X') (h : X''' ⟶ X'')
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison f (h ≫ g) M ≫
        Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison g h
          ((modulePullback f).obj M) =
      Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison (g ≫ f) h M ≫
        (modulePullback h).map
          (Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison f g M) := by
  simp only [← Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app]
  exact Stacks.PullbackPseudofunctor.modulePullbackCompIso_assoc f g h M

/-- The associativity coherence of the contraction of an iterated pullback: for
`T'' ⟶ T' ⟶ T ⟶ S` the two ways of contracting `(g' ∘ g ∘ f)^*M` to `g'^*(g^*(f^*M))` — splitting
off `f` first or `g'` last — agree. -/
theorem compComparison_assoc (g' : T'' ⟶ T') (g : T' ⟶ T) (f : T ⟶ S)
    (M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)) :
    compComparison (g' ≫ g) f M ≫
        compComparison g' g ((pullbackFunctor (ringedSpaceHom f)).obj M) =
      compComparison g' (g ≫ f) M ≫
        (pullbackFunctor (ringedSpaceHom g')).map (compComparison g f M) :=
  modulePullbackComparison_assoc (ringedSpaceHom f) (ringedSpaceHom g) (ringedSpaceHom g') M

/-! ### The two laws for the pullback of the map `ψ` of a quadruple -/

namespace Twisting

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The identity law for the pullback of `ψ`: pulling `ψ` back along `𝟙_T` and transporting the
result along the degreewise comparison induced by the identity law `(𝟙_T)^*L ≅ L` returns `ψ`. -/
theorem pullbackApp_id (ψ : Twisting f A d L) (n : ℤ) :
    ψ.pullbackApp (𝟙 T) n ≫ (congrIso (idCmp L) n).hom = ψ.app n := by
  have hp : laurentPullback (𝟙 T) L n ≫ (congrIso (idCmp L) n).hom =
      (pullbackIdIso T.toRingedSpace).hom.app ((laurent L).piece n) :=
    (congrArg (fun z => z ≫ (congrIso (idCmp L) n).hom)
        (pieceIso_hom_eq_laurentPullback (𝟙 T) L n)).symm.trans (pieceIso_id L n)
  have hnat : (pullbackFunctor (ringedSpaceHom (𝟙 T))).map (ψ.app n) ≫
        (pullbackIdIso T.toRingedSpace).hom.app ((laurent L).piece n) =
      (pullbackIdIso T.toRingedSpace).hom.app
          ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d))) ≫ ψ.app n :=
    (pullbackIdIso T.toRingedSpace).hom.naturality (ψ.app n)
  have key : (compComparison (𝟙 T) f (A.piece (n * d)) ≫
        (pullbackFunctor (ringedSpaceHom (𝟙 T))).map (ψ.app n) ≫
          laurentPullback (𝟙 T) L n) ≫ (congrIso (idCmp L) n).hom = ψ.app n := by
    simp only [Category.assoc]
    rw [hp, hnat]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ ψ.app n)
        (compComparison_id f (A.piece (n * d)))).trans (Category.id_comp (ψ.app n)))
  exact key

/-- The composition law for the pullback of `ψ`: pulling `ψ` back along `g` and then along `g'`,
and transporting the result along the degreewise comparison induced by the composition law
`g'^*g^*L ≅ (g' ≫ g)^*L`, returns the pullback of `ψ` along `g' ≫ g`. -/
theorem pullbackApp_comp (ψ : Twisting f A d L) (g : T' ⟶ T) (g' : T'' ⟶ T') (n : ℤ) :
    (ψ.pullback g).pullbackApp g' n ≫ (congrIso (compCmp g' g L) n).hom =
      ψ.pullbackApp (g' ≫ g) n := by
  have hpc := laurentPullback_comp g g' L n
  have hassoc : compComparison g' (g ≫ f) (A.piece (n * d)) ≫
        (pullbackFunctor (ringedSpaceHom g')).map (compComparison g f (A.piece (n * d))) ≫
          (compCmp g' g ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d)))).hom =
      compComparison (g' ≫ g) f (A.piece (n * d)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (compCmp g' g
            ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d)))).hom)
          (compComparison_assoc g' g f (A.piece (n * d))).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => compComparison (g' ≫ g) f (A.piece (n * d)) ≫ z)
              (compComparison_comp_compCmp g' g
                ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d))))).trans
            (Category.comp_id _))))
  have hnat : (pullbackFunctor (ringedSpaceHom g')).map
          ((pullbackFunctor (ringedSpaceHom g)).map (ψ.app n)) ≫
        (compCmp g' g ((laurent L).piece n)).hom =
      (compCmp g' g ((pullbackFunctor (ringedSpaceHom f)).obj (A.piece (n * d)))).hom ≫
        (pullbackFunctor (ringedSpaceHom (g' ≫ g))).map (ψ.app n) :=
    compCmp_naturality g' g (ψ.app n)
  have key : (compComparison g' (g ≫ f) (A.piece (n * d)) ≫
        (pullbackFunctor (ringedSpaceHom g')).map
            (compComparison g f (A.piece (n * d)) ≫
              (pullbackFunctor (ringedSpaceHom g)).map (ψ.app n) ≫ laurentPullback g L n) ≫
          laurentPullback g' (pullbackModule g L) n) ≫ (congrIso (compCmp g' g L) n).hom =
      compComparison (g' ≫ g) f (A.piece (n * d)) ≫
        (pullbackFunctor (ringedSpaceHom (g' ≫ g))).map (ψ.app n) ≫
          laurentPullback (g' ≫ g) L n := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [hpc, reassoc_of% hnat, reassoc_of% hassoc]
    rfl
  exact key

end Twisting

/-! ### The two laws for the pullback of a quadruple -/

namespace Quadruple

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- The pullback of a quadruple along an identity is strictly equivalent to the quadruple. -/
@[stacks 01NS "the pullback of a quadruple along the identity morphism of the test scheme is \
strictly equivalent to the quadruple"]
theorem strictlyEquivalent_pullback_id (P : Quadruple f A d) :
    StrictlyEquivalent (P.pullback (𝟙 T)) P :=
  (strictlyEquivalent_iff_exists_hom _ _).mpr
    ⟨laurentCongrIso (idCmp P.L), fun n => Twisting.pullbackApp_id P.twisting n⟩

/-- The pullback of a quadruple along a composite of morphisms of test schemes is strictly
equivalent to the twice-pulled-back quadruple. -/
@[stacks 01NS "the pullback of a quadruple along a composite of morphisms of test schemes is \
strictly equivalent to the twice-pulled-back quadruple"]
theorem strictlyEquivalent_pullback_comp (P : Quadruple f A d) (g : T' ⟶ T) (g' : T'' ⟶ T') :
    StrictlyEquivalent ((P.pullback g).pullback g') (P.pullback (g' ≫ g)) :=
  (strictlyEquivalent_iff_exists_hom _ _).mpr
    ⟨laurentCongrIso (compCmp g' g P.L), fun n => Twisting.pullbackApp_comp P.twisting g g' n⟩

end Quadruple

/-! ### `F_d` is a functor at a fixed degree -/

variable {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}

/-- The identity law for the map `F_d(T) → F_d(T')` of Section 01NS: the map of the identity
morphism of a test scheme is the identity of `F_d(T)`. -/
theorem Fd.pullback_id {d : ℤ} (ξ : Fd A d T) : Fd.pullback (𝟙 T) ξ = ξ := by
  obtain ⟨f, ⟨P⟩⟩ := ξ
  exact (Fd.mk_eq_mk_iff _ _).mpr (Quadruple.strictlyEquivalent_pullback_id P)

/-- The composition law for the map `F_d(T) → F_d(T')` of Section 01NS: the map of a composite
`g' ≫ g` of morphisms of test schemes is the composite of the two maps. -/
theorem Fd.pullback_comp {d : ℤ} (g : T' ⟶ T) (g' : T'' ⟶ T') (ξ : Fd A d T) :
    Fd.pullback (g' ≫ g) ξ = Fd.pullback g' (Fd.pullback g ξ) := by
  obtain ⟨f, ⟨P⟩⟩ := ξ
  exact ((Fd.mk_eq_mk_iff _ _).mpr (Quadruple.strictlyEquivalent_pullback_comp P g g')).symm

/-- The functor `F_d : Sch^{opp} ⟶ Sets` at a fixed degree `d`. It sends a test scheme `T` to the
set `F_d(T)` of strict equivalence classes of quadruples `(d, f : T → S, L, ψ)` of degree `d`, and
a morphism `g : T' ⟶ T` of test schemes to the map sending the class of a quadruple to the class
of its pullback along `g`. -/
@[stacks 01NS "the functor F_d : Sch^opp -> Sets at a fixed degree d, with both functor laws \
proved (Fd.pullback_id and Fd.pullback_comp): on objects the set F_d(T) of strict equivalence \
classes of quadruples of degree d, on morphisms the pullback of a quadruple. Representability of \
F_d by a scheme is Tag 01NV and is not proved here"]
def Fd.functor (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (d : ℤ) : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := Fd A d T.unop
  map φ := TypeCat.ofHom (Fd.pullback (A := A) (d := d) φ.unop)
  map_id _ := TypeCat.homEquiv.injective (funext fun ξ => Fd.pullback_id ξ)
  map_comp φ χ :=
    TypeCat.homEquiv.injective (funext fun ξ => Fd.pullback_comp φ.unop χ.unop ξ)

/-- The value of `Fd.functor` at a test scheme `T` is `Fd A d T`. -/
@[simp] theorem Fd.functor_obj
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    (T : Scheme.{u}ᵒᵖ) : (Fd.functor A d).obj T = Fd A d T.unop := rfl

/-- The map of `Fd.functor` at a morphism `φ` is the pullback along `φ.unop`. -/
@[simp] theorem Fd.functor_map
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    {X Y : Scheme.{u}ᵒᵖ} (φ : X ⟶ Y) (ξ : Fd A d X.unop) :
    (Fd.functor A d).map φ ξ = Fd.pullback φ.unop ξ := rfl

/-! ### `F` is a functor -/

/-- The identity law for the map `F(T) → F(T')` of the display 01NX: the map of the identity
morphism of a test scheme is the identity of `F(T)`. -/
theorem F.pullback_id (ξ : F A T) : F.pullback (𝟙 T) ξ = ξ := by
  obtain ⟨f, ⟨x⟩⟩ := ξ
  exact F.mk_eq_mk_of_strictlyEquivalent x.1.2 (Quadruple.strictlyEquivalent_pullback_id x.2)

/-- The composition law for the map `F(T) → F(T')` of the display 01NX: the map of a composite
`g' ≫ g` of morphisms of test schemes is the composite of the two maps. -/
theorem F.pullback_comp (g : T' ⟶ T) (g' : T'' ⟶ T') (ξ : F A T) :
    F.pullback (g' ≫ g) ξ = F.pullback g' (F.pullback g ξ) := by
  obtain ⟨f, ⟨x⟩⟩ := ξ
  exact (F.mk_eq_mk_of_strictlyEquivalent x.1.2
    (Quadruple.strictlyEquivalent_pullback_comp x.2 g g')).symm

/-- The functor `F : Sch^{opp} ⟶ Sets` of relative `Proj`: it sends a test scheme `T` to the set
`F(T) = ⋃_{d ≥ 1} F_d(T)` of classes of quadruples `(d, f : T → S, L, ψ)` of positive degree, and
a morphism `g : T' ⟶ T` of test schemes to the map sending the class of a quadruple to the class
of its pullback along `g`.

The set `F(T)` is the quotient of the quadruples of positive degree over `T` by the equivalence
relation generated by strict equivalence inside one degree and equivalence across degrees. It is
the display's `F(T)` for a quasi-compact `T`; for an arbitrary `T` the display's functor is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.F.limFunctor`. -/
def F.functor (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) :
    Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := F A T.unop
  map φ := TypeCat.ofHom (F.pullback (A := A) φ.unop)
  map_id _ := TypeCat.homEquiv.injective (funext fun ξ => F.pullback_id ξ)
  map_comp φ χ :=
    TypeCat.homEquiv.injective (funext fun ξ => F.pullback_comp φ.unop χ.unop ξ)

/-- The value of `F.functor` at a test scheme `T` is `F A T`. -/
@[simp] theorem F.functor_obj
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    (T : Scheme.{u}ᵒᵖ) : (F.functor A).obj T = F A T.unop := rfl

/-- The map of `F.functor` at a morphism `φ` is the pullback along `φ.unop`. -/
@[simp] theorem F.functor_map
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))
    {X Y : Scheme.{u}ᵒᵖ} (φ : X ⟶ Y) (ξ : F A X.unop) :
    (F.functor A).map φ ξ = F.pullback φ.unop ξ := rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
