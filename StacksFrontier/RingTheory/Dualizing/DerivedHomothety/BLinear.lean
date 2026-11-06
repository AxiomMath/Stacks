module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.Equivariance
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.FiniteDual

/-!
# The `B`-action on the comparisons behind Tag 0AX0

For a homomorphism of commutative rings `f : A →+* B` and a dualizing complex `ω` over `A`, the
object `RHom_A(B, ω)` of [stacks 0A70] lives in `D(B)`, and
`Dualizing.restrictScalarsDerivedHomIso` identifies it, after restriction of scalars, with the
internal derived Hom `RHom_A(B[0], ω)` of [stacks 0A63]. That identification is built from four
comparisons, and this file proves that multiplication by `b` crosses all four: it starts as
`b • 𝟙` on `RHom_A(B, ω)` in the `B`-linear category `D(B)` and arrives as the derived dual of
multiplication by `b` on `B[0]`.

The crossing is not formal. On the coextension side the `B`-action on `Hom_A(B, M)` is
precomposition with multiplication on `B` (`ModuleCat.CoextendScalars.smul_apply'`), while
`Dualizing.coextendScalarsHomLinearEquiv` presents the same module as maps out of `B[0]`; the two
agree because `B` is commutative, which is the content of
`Dualizing.coextendScalarsHomLinearEquiv_smul`. On the internal-Hom side the crossing is the
naturality of the K-injective model in its first variable,
`Dualizing.derivedInternalHomModelIso₂_naturality_left`.

With the crossing available, the degree-zero half of the Hom computation of [stacks 0AX0] becomes
an identification of `End_{D(B)}(RHom_A(B, ω))` with `Hom_{D(A)}(1, B[0])` carrying `b • φ` to
`φ` postcomposed with multiplication by `b`; that is
`Dualizing.exists_endAddEquiv_hom_derivedTensorUnit`, and it is where the biduality theorem of
[stacks 0A7C] and the adjunction of [stacks 0A70] are consumed.

## Main definitions

* `Dualizing.targetMul` — multiplication by `b`, as an `A`-linear endomorphism of
  `Dualizing.targetAsModule`.
* `Dualizing.postcompAddEquiv` — postcomposition with an isomorphism, additively.

## Main results

* `Dualizing.coextendScalarsHomLinearEquiv_smul`,
  `Dualizing.coextendComplexIsoHomComplexSingle_smul`,
  `Dualizing.restrictScalarsDerivedHomModelIso_smul` — the `B`-action on the three cochain-level
  comparisons.
* `Dualizing.restrictScalarsDerivedHomIso_smul` — the `B`-action on the identification of
  `RHom_A(B, ω)` with `RHom_A(B[0], ω)`.
* `Dualizing.exists_endAddEquiv_hom_derivedTensorUnit` — derived endomorphisms of `RHom_A(B, ω)`
  are the morphisms `1 ⟶ B[0]` of `D(A)`, `B`-equivariantly.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Multiplication by `b`, as an `A`-linear endomorphism of `Dualizing.targetAsModule`. -/
abbrev targetMul (f : A →+* B) (b : B) :
    targetAsModule.{u, v} f ⟶ targetAsModule.{u, v} f :=
  (ModuleCat.restrictScalars.{max v u} f).map
    (b • 𝟙 (ModuleCat.of B (ULift.{max v u} B)))

/-- The `B`-action on `Hom_A(B, M)` is precomposition with multiplication on `B`: the
comparison `Dualizing.coextendScalarsHomLinearEquiv` turns `b • w` into `w` precomposed with
`Dualizing.targetMul`. This is where commutativity of `B` enters: coextension of scalars acts
by *right* multiplication on the source. -/
theorem coextendScalarsHomLinearEquiv_smul (f : A →+* B) (M : ModuleCat.{max v u} A) (b : B)
    (w : ((ModuleCat.restrictScalars.{max v u} f).obj
      ((ModuleCat.coextendScalars.{u, u, max v u} f).obj M) : Type (max v u))) :
    coextendScalarsHomLinearEquiv.{u, v} f M
        (((ModuleCat.restrictScalars.{max v u} f).map
          (b • 𝟙 ((ModuleCat.coextendScalars.{u, u, max v u} f).obj M))).hom w) =
      (coextendScalarsHomLinearEquiv.{u, v} f M w).comp
        (targetMul.{u, v} f b).hom := by
  ext x
  change (ModuleCat.CoextendScalars.equiv f M w) (x.down * b) =
    (ModuleCat.CoextendScalars.equiv f M w) (b * x.down)
  rw [mul_comm]

/-- **The `B`-action crosses the comparison of complexes.** Under
`Dualizing.coextendComplexIsoHomComplexSingle`, multiplication by `b` on the degreewise
coextension `Hom_A(B, I)` becomes precomposition with multiplication by `b` on `B[0]`. -/
theorem coextendComplexIsoHomComplexSingle_smul (f : A →+* B) (b : B)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    ((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (b • 𝟙 ((coextendComplex.{u, u, v} f).obj I)) ≫
        (coextendComplexIsoHomComplexSingle.{u, v} f I).hom =
      (coextendComplexIsoHomComplexSingle.{u, v} f I).hom ≫
        Stacks.HomComplex.TensorHomMap.precomp A
          ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj (targetAsModule.{u, v} f))
          ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).obj (targetAsModule.{u, v} f))
          I
          ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).map
            (targetMul.{u, v} f b)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun w => ?_
  change Cochain.fromSingleMk
      (ModuleCat.ofHom (coextendScalarsHomLinearEquiv.{u, v} f (I.X n)
        (((ModuleCat.restrictScalars.{max v u} f).map
          (b • 𝟙 ((ModuleCat.coextendScalars.{u, u, max v u} f).obj (I.X n)))).hom w)))
      (by omega : (0 : ℤ) + n = n) =
    Cochain.comp (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).map
        (targetMul.{u, v} f b)))
      (Cochain.fromSingleMk
        (ModuleCat.ofHom (coextendScalarsHomLinearEquiv.{u, v} f (I.X n) w))
        (by omega : (0 : ℤ) + n = n)) (zero_add n)
  rw [← Cochain.fromSingleMk_precomp]
  exact congrArg
    (fun φ => Cochain.fromSingleMk (K := I) (ModuleCat.ofHom φ) (show (0 : ℤ) + n = n by omega))
    (coextendScalarsHomLinearEquiv_smul.{u, v} f (I.X n) b w)

/-- **The `B`-action crosses the cochain model of `RHom_A(B, ω)`.** Under
`Dualizing.restrictScalarsDerivedHomModelIso`, multiplication by `b` on `RHom_A(B, ω)` becomes
multiplication by `b` on the degreewise coextension `Hom_A(B, I)`. -/
theorem restrictScalarsDerivedHomModelIso_smul (f : A →+* B) (b : B)
    {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hinj : ∀ i, Injective (I.X i))
    (e : ω ≅ DerivedCategory.Q.obj I) :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) ≫
        (restrictScalarsDerivedHomModelIso.{u, v} f I a hGE hinj e).hom =
      (restrictScalarsDerivedHomModelIso.{u, v} f I a hGE hinj e).hom ≫
        DerivedCategory.Q.map
          (((ModuleCat.restrictScalars.{max v u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (b • 𝟙 ((coextendComplex.{u, u, v} f).obj I))) := by
  have hQ : DerivedCategory.Q.map (b • 𝟙 ((coextendComplex.{u, u, v} f).obj I)) =
      b • 𝟙 (DerivedCategory.Q.obj ((coextendComplex.{u, u, v} f).obj I)) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have hA : (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) ≫
        (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          ((derivedHom.{u, v, u} f).mapIso e ≪≫ derivedHomObjIsoCoextend.{u, v} f I
            (CochainComplex.isKInjective_of_injective I a)).hom =
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          ((derivedHom.{u, v, u} f).mapIso e ≪≫ derivedHomObjIsoCoextend.{u, v} f I
            (CochainComplex.isKInjective_of_injective I a)).hom ≫
        (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          (DerivedCategory.Q.map (b • 𝟙 ((coextendComplex.{u, u, v} f).obj I))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hQ, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  have hB := (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategoryFactors.hom.naturality
    (b • 𝟙 ((coextendComplex.{u, u, v} f).obj I))
  exact (CommSq.vert_comp ⟨hA⟩ ⟨hB⟩).w

/-- Inverting the horizontal maps of a commuting square. -/
theorem square_inv {𝒞 : Type*} [Category 𝒞] {A₀ A₁ B₀ B₁ : 𝒞} (m : A₀ ≅ B₀) (m' : A₁ ≅ B₁)
    {v : A₀ ⟶ A₁} {w : B₀ ⟶ B₁} (h : v ≫ m'.hom = m.hom ≫ w) : w ≫ m'.inv = m.inv ≫ v := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- **The `B`-action crosses the identification of `RHom_A(B, ω)` with `RHom_A(B[0], ω)`.**
Under `Dualizing.restrictScalarsDerivedHomIso`, multiplication by `b` on `RHom_A(B, ω)` becomes
the derived dual of multiplication by `b` on `B[0]`.

This is the point at which the `B`-structure of `RHom_A(B, ω)` is transported to the first
variable of the internal derived Hom, and it is the step the source of [stacks 0AX0] leaves
implicit. -/
theorem restrictScalarsDerivedHomIso_smul [IsNoetherianRing A] (f : A →+* B) (b : B)
    {ω : DerivedCategory (ModuleCat.{max v u} A)}
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (a : ℤ)
    (hGE : I.IsStrictlyGE a) (hinj : ∀ i, Injective (I.X i))
    (e : ω ≅ DerivedCategory.Q.obj I) :
    (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) ≫
        (restrictScalarsDerivedHomIso.{u, v} f I a hGE hinj e).hom =
      (restrictScalarsDerivedHomIso.{u, v} f I a hGE hinj e).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.map
          ((((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
              (targetMul.{u, v} f b)).op, 𝟙 ω) :
            (Opposite.op (targetSingle.{u, v} f), ω) ⟶
              (Opposite.op (targetSingle.{u, v} f), ω)) := by
  have h₁ := restrictScalarsDerivedHomModelIso_smul.{u, v} f b I a hGE hinj e
  have h₂ := congrArg DerivedCategory.Q.map
    (coextendComplexIsoHomComplexSingle_smul.{u, v} f b I)
  simp only [Functor.map_comp] at h₂
  have hphi := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0).hom.naturality
    (targetMul.{u, v} f b)
  have hmodel := derivedInternalHomModelIso₂_naturality_left.{u, max v u}
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0).app
      (targetAsModule.{u, v} f))
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0).app
      (targetAsModule.{u, v} f))
    ((CochainComplex.singleFunctor (ModuleCat.{max v u} A) 0).map (targetMul.{u, v} f b))
    ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map (targetMul.{u, v} f b))
    hphi I a hGE hinj
  have h₃ := square_inv _ _ hmodel
  have h₄ : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.map
          ((((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
              (targetMul.{u, v} f b)).op, 𝟙 (DerivedCategory.Q.obj I)) :
            (Opposite.op (targetSingle.{u, v} f), DerivedCategory.Q.obj I) ⟶
              (Opposite.op (targetSingle.{u, v} f), DerivedCategory.Q.obj I)) ≫
        ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.mapIso
          ((Iso.refl (Opposite.op (targetSingle.{u, v} f))).prod e.symm)).hom =
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.mapIso
          ((Iso.refl (Opposite.op (targetSingle.{u, v} f))).prod e.symm)).hom ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A).hom.map
          ((((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
              (targetMul.{u, v} f b)).op, 𝟙 ω) :
            (Opposite.op (targetSingle.{u, v} f), ω) ⟶
              (Opposite.op (targetSingle.{u, v} f), ω)) := by
    dsimp only [Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.symm_hom]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Prod.ext <;> simp
  exact paste₄ h₁ h₂ h₃ h₄

/-- Transporting a commuting square along a morphism on the left. -/
theorem comp_square_right {𝒞 : Type*} [Category 𝒞] {P Q R : 𝒞} (X : P ⟶ Q) {V : Q ⟶ Q}
    {W : Q ⟶ R} {M : R ⟶ R} (h : V ≫ W = W ≫ M) : (X ≫ V) ≫ W = (X ≫ W) ≫ M := by
  rw [Category.assoc, h, Category.assoc]

/-- Postcomposition with an isomorphism, as an additive equivalence of morphism groups. -/
def postcompAddEquiv {C : Type*} [Category C] [Preadditive C] (W : C) {X Y : C} (e : X ≅ Y) :
    (W ⟶ X) ≃+ (W ⟶ Y) where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := Preadditive.add_comp _ _ _ _ _ _

/-- **The derived endomorphisms of `RHom_A(B, ω)` are the morphisms `1 ⟶ B[0]` in `D(A)`**, and
the `B`-action corresponds to postcomposition with multiplication by `b` on `B[0]`.

The chain is: the adjunction of [stacks 0A70]; the identification
`Dualizing.restrictScalarsDerivedHomIso` of `RHom_A(B, ω)` with `RHom_A(B[0], ω)`, whose
`B`-equivariance is `Dualizing.restrictScalarsDerivedHomIso_smul`; the adjunction-level
description `Dualizing.homUnitAddEquiv` of morphisms into `ω`; and the biduality theorem of
[stacks 0A7C] at `B[0]`, natural by `Dualizing.bidualityMor_naturality`. -/
theorem exists_endAddEquiv_hom_derivedTensorUnit [IsNoetherianRing A] (f : A →+* B)
    (hf : f.Finite) {ω : DerivedCategory (ModuleCat.{max v u} A)} (hω : IsDualizingComplex ω) :
    ∃ E : End ((derivedHom.{u, v, u} f).obj ω) ≃+
        (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A ⟶ targetSingle.{u, v} f),
      ∀ (b : B) (φ : End ((derivedHom.{u, v, u} f).obj ω)),
        E (b • φ) = E φ ≫ (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
          (targetMul.{u, v} f b) := by
  obtain ⟨a, bb, I, hGE, hLE, hinj, ⟨e⟩⟩ := hω.finiteInjectiveDimension
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v, u} f
  have hbid := isIso_dualizingBidualityMor_of_finiteCohomology.{u, max v u} A ω
    (targetSingle.{u, v} f) hω (finite_homology_targetSingle.{u, v} f hf)
  set d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A with hd
  set D₁ := d.hom.obj (Opposite.op (targetSingle.{u, v} f), ω) with hD₁
  set θ := restrictScalarsDerivedHomIso.{u, v} f I a hGE hinj e with hθ
  set bid := @asIso _ _ _ _ (dualizingBidualityMor.{u, max v u} A ω (targetSingle.{u, v} f)) hbid
    with hbid'
  set mb : ∀ b : B, targetSingle.{u, v} f ⟶ targetSingle.{u, v} f := fun b =>
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map (targetMul.{u, v} f b)
    with hmb
  refine ⟨End.addEquiv.trans ((adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm.trans
      ((precompAddEquiv θ ω).symm.trans
        ((homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
            (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).symm.trans
          (postcompAddEquiv _ bid.symm)))), fun b φ => ?_⟩
  set P := d.hom.map (((mb b).op, 𝟙 ω) : (Opposite.op (targetSingle.{u, v} f), ω) ⟶
    (Opposite.op (targetSingle.{u, v} f), ω)) with hP
  set Q := d.hom.map ((P.op, 𝟙 ω) : (Opposite.op D₁, ω) ⟶ (Opposite.op D₁, ω)) with hQ
  -- the four equivariance steps, read off the four naturality statements
  have h₁ : (adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm (b • φ.asHom) =
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
          (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) ≫
        (adj.homAddEquiv ((derivedHom.{u, v, u} f).obj ω) ω).symm φ.asHom := by
    apply (adj.homEquiv ((derivedHom.{u, v, u} f).obj ω) ω).injective
    rw [Adjunction.homAddEquiv_symm_apply, Equiv.apply_symm_apply,
      adj.homEquiv_naturality_left, Adjunction.homAddEquiv_symm_apply,
      Equiv.apply_symm_apply, Linear.smul_comp, Category.id_comp]
  have h₂ : θ.inv ≫ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
        (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) = P ≫ θ.inv :=
    (square_inv θ θ (restrictScalarsDerivedHomIso_smul.{u, v} f b I a hGE hinj e)).symm
  have h₃ := homUnitAddEquiv_naturality d
    (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
    (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A)
    (StacksDraft.DerivedHom.derivedTensorUnitLeft_natural.{u, max v u} A) ω P
  have h₄ : Q ≫ bid.inv = bid.inv ≫ mb b :=
    square_inv bid bid (bidualityMor_naturality
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max v u} A) ω (mb b))
  -- the `B`-action passes through the two equivalences, becoming `P` and then `Q`
  have h₅ : ∀ x, (homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
        (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).symm
        ((precompAddEquiv θ ω).symm
          ((ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory.map
            (b • 𝟙 ((derivedHom.{u, v, u} f).obj ω)) ≫ x)) =
      (homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
        (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).symm
        ((precompAddEquiv θ ω).symm x) ≫ Q := fun x => by
    apply (homUnitAddEquiv d (StacksDraft.DerivedHom.derivedTensorUnit.{u, max v u} A)
      (StacksDraft.DerivedHom.derivedTensorUnitLeft.{u, max v u} A) ω D₁).injective
    rw [AddEquiv.apply_symm_apply, h₃, AddEquiv.apply_symm_apply]
    change θ.inv ≫ _ ≫ _ = _ ≫ θ.inv ≫ _
    rw [← Category.assoc, h₂, Category.assoc]
  dsimp only [AddEquiv.trans_apply, postcompAddEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Iso.symm_hom, End.addEquiv_apply]
  rw [End.smul_asHom, h₁]
  change _ ≫ bid.inv = _
  rw [h₅]
  exact comp_square_right _ h₄

end Dualizing

end
