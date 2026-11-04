module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MatrixActionDerived
public import StacksFrontier.Algebra.Homology.MatrixActionTensor
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

/-!
# Tensoring a bounded flat complex with a truncated resolution: the vanishing gap

Let `A` be a commutative ring and `C` an `A`-linear abelian category with a tensor bifunctor
`T : C ⥤ C ⥤ C` whose unit `U` carries the `A`-action, as in
`StacksFrontier/Algebra/Homology/MatrixActionTensor.lean`.  Let `R` be a bounded above complex of
finite free `A`-modules with chosen bases whose realization `T`-module `U ⊗_A R` has no cohomology
off degree `0`, and let `K` be a complex strictly concentrated in degrees `[a, b]` whose terms `X`
have exact `T(X, -)` (flat terms).  Then for every `k` the total complex `K ⊗_A σ^{≥k}R` of the
matrix action has no cohomology in the degrees `j` with `b + k < j < a`.

## Main results

* `CategoryTheory.MatrixAction.isIso_homologyMap_tot_ιStupidTrunc`: the stupid truncation
  `σ^{≥k}R ⟶ R` induces an isomorphism on the cohomology of `K ⊗_A -` in degrees `> b + k`.
* `CategoryTheory.MatrixAction.kFlatLeft_of_bounded_of_exact`: a bounded complex with flat
  terms is K-flat in the first variable of `T`.
* `CategoryTheory.MatrixAction.isZero_homology_tot_stupidTrunc_of_flat`: the vanishing gap.

## References

* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]

attribute [local instance] Abelian.hasFiniteBiproducts

section Truncation

variable {C : Type u} [Category.{v} C] [Abelian C] [Linear A C]
  [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]

/-- Tensoring a complex `P` strictly bounded above by `b` with the inclusion `σ^{≥k}R ⟶ R` is an
isomorphism in every total degree `≥ b + k`. -/
lemma isIso_tot_ιStupidTrunc_f (P : CochainComplex C ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (R : CochainComplex (Mat_ (SingleObj A)) ℤ) (k n : ℤ) (hn : b + k ≤ n) :
    IsIso ((HomologicalComplex.mapBifunctorMap (𝟙 P)
      (R.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (matrixAction A)
        (ComplexShape.up ℤ)).f n) := by
  refine StacksDraft.TotalComplexQuasiIso.isIso_total_map_f _ n fun p q hpq => ?_
  by_cases hq : k ≤ q
  · have := HomologicalComplex.isIso_ιStupidTrunc_f R (ComplexShape.embeddingUpIntGE k)
      (i := (q - k).toNat) (by change k + ((q - k).toNat : ℤ) = q; omega)
    show IsIso (((matrixAction A).map (𝟙 (P.X p))).app _ ≫
      ((matrixAction A).obj (P.X p)).map ((R.ιStupidTrunc _).f q))
    rw [Functor.map_id, NatTrans.id_app, Category.id_comp]
    exact Functor.map_isIso _ _
  · exact StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero _
      (((matrixAction A).flip.obj _).map_isZero (P.isZero_of_isStrictlyLE b p (by omega)))
      (((matrixAction A).flip.obj _).map_isZero (P.isZero_of_isStrictlyLE b p (by omega)))

/-- **The stupid truncation does not change the cohomology of `P ⊗_A -` above `b + k`.** -/
lemma isIso_homologyMap_tot_ιStupidTrunc (P : CochainComplex C ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (R : CochainComplex (Mat_ (SingleObj A)) ℤ) (k i : ℤ) (hi : b + k < i) :
    IsIso (HomologicalComplex.homologyMap (HomologicalComplex.mapBifunctorMap (𝟙 P)
      (R.ιStupidTrunc (ComplexShape.embeddingUpIntGE k)) (matrixAction A)
        (ComplexShape.up ℤ)) i) :=
  by
  refine StacksDraft.StupidTruncation.isIso_homologyMap_of_isIso_f_prev_next _ i ?_ ?_ ?_ <;>
    exact isIso_tot_ιStupidTrunc_f A P b R k _ (by (try simp); omega)

end Truncation

section Flat

variable {C : Type u} [Category.{v} C] [Abelian C]
  (T : C ⥤ C ⥤ C) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ (K L : CochainComplex C ℤ), HomologicalComplex.HasMapBifunctor K L T (ComplexShape.up ℤ)]

/-- **A bounded complex whose terms are `T`-flat is K-flat in the first variable of `T`.** -/
theorem kFlatLeft_of_bounded_of_exact (K : CochainComplex C ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b]
    (hK : ∀ (p : ℤ) (G : CochainComplex C ℤ), G.Acyclic →
      (((T.obj (K.X p)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).Acyclic) :
    CochainComplex.KFlatBifunctor.KFlatLeft T K := by
  rw [CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip]
  refine CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE_of_isStrictlyGE T.flip K b a
    fun q => CochainComplex.KFlatBifunctor.kFlat_single_of_exact T.flip (K.X q) q fun G hG n =>
      (hK q G hG n).of_iso (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
        (fun _ _ _ => by
          simp [CochainComplex.KFlatBifunctor.rowComplex]))

variable [HasDerivedCategory C]

/-- `Tot(T(K, -))` for a left K-flat `K` inverts quasi-isomorphisms. -/
lemma totalLeft_comp_Q_inverts (K : CochainComplex C ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlatLeft T K) :
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy
      ((T.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj K ⋙ DerivedCategory.Q) := fun _ _ f hf =>
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft T K hK f hf)

/-- **`Tot(T(K, L))` for `K` bounded with flat terms has no cohomology below the lower bound of
`K` as soon as `L` has cohomology only in degree `0`.** -/
theorem isZero_homology_totalLeft_of_flat (K : CochainComplex C ℤ) (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b]
    (hK : ∀ (p : ℤ) (G : CochainComplex C ℤ), G.Acyclic →
      (((T.obj (K.X p)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).Acyclic)
    (L : CochainComplex C ℤ) (hL : ∀ j : ℤ, j ≠ 0 → L.ExactAt j) (j : ℤ) (hj : j < a) :
    IsZero ((HomologicalComplex.mapBifunctor K L T (ComplexShape.up ℤ)).homology j) := by
  let G := (T.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ)).obj K
  have hinv := totalLeft_comp_Q_inverts T K (kFlatLeft_of_bounded_of_exact T K a b hK)
  let Ψ : DerivedCategory C ⥤ DerivedCategory C :=
    Localization.lift _ hinv DerivedCategory.Q
  let eΨ : DerivedCategory.Q ⋙ Ψ ≅ G ⋙ DerivedCategory.Q := Localization.fac _ _ _
  have hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor C i).obj (DerivedCategory.Q.obj L)) := fun i hi =>
    ((L.exactAt_iff_isZero_homology i).1 (hL i hi)).of_iso
      ((DerivedCategory.homologyFunctorFactors C i).app L)
  have hGE : (DerivedCategory.Q.obj L).IsGE 0 :=
    (DerivedCategory.isGE_iff _ 0).2 fun i hi => hzero i (by omega)
  have hLE : (DerivedCategory.Q.obj L).IsLE 0 :=
    (DerivedCategory.isLE_iff _ 0).2 fun i hi => hzero i (by omega)
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj L) 0
  let S := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj N
  let e' : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj S :=
    e ≪≫ (DerivedCategory.singleFunctorIsoCompQ C 0).app N
  have hS : IsZero ((G.obj S).homology j) := by
    refine (HomologicalComplex.ExactAt.of_isZero ?_).isZero_homology
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
    by_cases hq : q = 0
    · subst hq
      exact (((T.flip.obj (S.X 0)).map_isZero
        (K.isZero_of_isStrictlyGE a p (by simp at hpq; omega)))).eq_of_src _ _
    · exact ((T.obj (K.X p)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N q hq)).eq_of_src _ _
  exact hS.of_iso (((DerivedCategory.homologyFunctorFactors C j).app (G.obj L)).symm ≪≫
    (DerivedCategory.homologyFunctor C j).mapIso (eΨ.symm.app L ≪≫ Ψ.mapIso e' ≪≫ eΨ.app S) ≪≫
      (DerivedCategory.homologyFunctorFactors C j).app (G.obj S))

variable [Linear A C]
  [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]
  (U : C) (ρ : T.flip.obj U ≅ 𝟭 C)
  (hT : ∀ (X : C) (a : A), (T.obj X).map (a • 𝟙 U) = a • 𝟙 ((T.obj X).obj U))

include ρ hT in
/-- **The vanishing gap.**  Let `R` be a complex of finite free `A`-modules with chosen bases,
strictly bounded above, whose realization `U ⊗_A R` has cohomology only in degree `0`, and let
`K` be strictly concentrated in degrees `[a, b]` with `T`-flat terms.  Then the total complex
`K ⊗_A σ^{≥k}R` has no cohomology in the degrees `j` with `b + k < j < a`. -/
theorem isZero_homology_tot_stupidTrunc_of_flat
    (R : CochainComplex (Mat_ (SingleObj A)) ℤ)
    (hR : ∀ j : ℤ, j ≠ 0 →
      (((realize A U).mapHomologicalComplex (ComplexShape.up ℤ)).obj R).ExactAt j)
    (K : CochainComplex C ℤ) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ (p : ℤ) (G : CochainComplex C ℤ), G.Acyclic →
      (((T.obj (K.X p)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G).Acyclic)
    (k j : ℤ) (hbk : b + k < j) (hja : j < a) :
    IsZero (((tot A (R.stupidTrunc (ComplexShape.embeddingUpIntGE k))).obj K).homology j) := by
  have h₁ : IsZero (((tot A R).obj K).homology j) :=
    (isZero_homology_totalLeft_of_flat T K a b hK _ hR j hja).of_iso
      (HomologicalComplex.homologyMapIso
        (mapBifunctorTensorRealizeIso A T U ρ hT K R) j).symm
  exact h₁.of_iso (@asIso _ _ _ _ _ (isIso_homologyMap_tot_ιStupidTrunc A K b R k j hbk))

end Flat

end CategoryTheory.MatrixAction

end
