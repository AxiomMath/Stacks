module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualCoevaluationSectionOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexMono
public import StacksFrontier.Homology.DerivedCategory.Monoidal.DerivedTensorIsoNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract

/-!
# The local retract of Stacks 0FPV, on a ringed site

Let `(C, O)` be a ringed site and let `N` be a left dual of `M` in the monoidal category `D(O)`
of Stacks 0FPT — an exact pairing, Categories, Definition 0FFP. This file produces, for every
object `V` of `C`, a covering family of `V` along each member `W` of which `M|_W` is a **retract**
of `K|_W`, for every morphism of complexes `j : K ⟶ M^•` which stays a monomorphism after
`- ⊗ N^•` in degree `1` and through which finitely many prescribed sections of the terms of `M^•`
over `W` lift.

Writing `η(1) = ∑ᵢ fᵢ ⊗ gᵢ` for the coevaluation, any `K^•` containing the `fᵢ` receives the
coevaluation, so `M` is a direct summand of `K`.

## Main results

* `SheafOfModules.d_zero_of_mono_f_one`: a degree-zero section whose image under a morphism of
  complexes that is a monomorphism in degree one is a cocycle is itself a cocycle.
* `SheafOfModules.cocycleHomOver_comp`: the morphism of complexes `O|_W[0] ⟶ A|_W` attached to a
  degree-zero cocycle section is natural in `A`.
* `AlgebraicGeometry.RingedSite.whiskerRight_f_tensorComplexSection`: whiskering a morphism of
  complexes on the right carries a local pure tensor to the local pure tensor of the image.
* `AlgebraicGeometry.RingedSite.restrictComplexMapAlong_cocycleHomOver`: the chain-level
  representative attached to a cocycle section restricts, along an arrow of the site, to the one
  attached to the restricted section.
* `AlgebraicGeometry.RingedSite.nonempty_retract_restrictOver`: `M|_W` is a retract of `K|_W`
  over an object `W` over which the coevaluation is induced by a cocycle section of the complex
  mapping to `M^• ⊗ N^•`.
* `AlgebraicGeometry.RingedSite.exists_presieve_localRetract`: every object `V` has a covering
  family along each member `W` of which `M|_W` is a retract of `K|_W`.

## Implementation notes

The coevaluation becomes a degree-zero cocycle section of `Tot(M^• ⊗_O N^•)` only on a covering
(`AlgebraicGeometry.RingedSite.exists_coveringSieve_coevaluationSection`), and that section
decomposes as a finite sum of pure tensors only on a further covering
(`AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorComplexSection`), because the degree-zero
term of the total complex is a coproduct of sheafified tensor products. The two coverings are
composed by `restrictComplexMapAlong_cocycleHomOver` together with
`AlgebraicGeometry.RingedSite.mapDerivedCategory_map_eq_restrictComplexMapAlong`: the cocycle
statement restricts along an arrow of the site with its section restricted along that arrow.

The conclusion is a `Presieve`: the existence of the local data over an object is not stable
under precomposition, so it does not define a sieve, but the presieve it defines generates a
covering sieve, by transitivity of the topology.

The derived categories are the standard ones, `HasDerivedCategory.standard`, the model at which
`Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal` is stated.

`tensorComplexSection` lives at `Stacks.SheafOfModules.Tensor.tensorComplex` and the whiskering
`j ▷ N^•` at the tensor product of `HomologicalComplex.monoidalCategory`. The two objects are the
same term, but a `Finset.sum` elaborated against one spelling does not unify against the other,
so the summands are introduced through an ascribed function.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

universe u

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A section of degree zero whose image under a morphism of complexes that is a
monomorphism in degree one is a cocycle is itself a cocycle.** -/
theorem d_zero_of_mono_f_one {A B : CochainComplex (SheafOfModules.{u} R) ℤ} (φ : A ⟶ B)
    [Mono (φ.f 1)] {W : C} (s : (A.X 0).val.obj (op W))
    (hs : (B.d 0 1).val.app (op W) ((φ.f 0).val.app (op W) s) = 0) :
    (A.d 0 1).val.app (op W) s = 0 := by
  refine Stacks.SheafOfModules.injective_app_of_mono (φ.f 1) (op W) ?_
  exact ((congrArg (fun ψ : A.X 0 ⟶ B.X 1 => ψ.val.app (op W) s) (φ.comm 0 1)).symm.trans
    hs).trans (map_zero _).symm

section Cocycle

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{u})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The image of a degree-zero cocycle section under a morphism of complexes is a cocycle. -/
theorem d_zero_val_app_of_d_zero {A B : CochainComplex (SheafOfModules.{u} O) ℤ} {U : C}
    (s : (A.X 0).val.obj (op U)) (hs : (A.d 0 1).val.app (op U) s = 0) (g : A ⟶ B) :
    (B.d 0 1).val.app (op U) ((g.f 0).val.app (op U) s) = 0 :=
  ((congrArg (fun ψ : A.X 0 ⟶ B.X 1 => ψ.val.app (op U) s) (g.comm 0 1)).trans
    (congrArg ((g.f 1).val.app (op U)) hs)).trans (map_zero _)

omit [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{u}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The restriction along an arrow of the site of a degree-zero cocycle section is a cocycle. -/
theorem d_zero_map_of_d_zero {F : CochainComplex (SheafOfModules.{u} O) ℤ} {V W : C} (g : W ⟶ V)
    (t : (F.X 0).val.obj (op V)) (ht : (F.d 0 1).val.app (op V) t = 0) :
    (F.d 0 1).val.app (op W) ((F.X 0).val.map g.op t) = 0 :=
  ((PresheafOfModules.naturality_apply (F.d 0 1).val g.op t).trans
    (congrArg ((F.X 1).val.map g.op) ht)).trans (map_zero _)

/-- **`cocycleHomOver` is natural in the complex.** Postcomposing the morphism of complexes
attached to a degree-zero cocycle section with the restriction of a morphism of complexes gives
the morphism attached to the image of the section. -/
theorem cocycleHomOver_comp {A B : CochainComplex (SheafOfModules.{u} O) ℤ} (U : C)
    (s : (A.X 0).val.obj (op U)) (hs : (A.d 0 1).val.app (op U) s = 0) (g : A ⟶ B) :
    cocycleHomOver O A U s hs ≫
        ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).map g =
      cocycleHomOver O B U ((g.f 0).val.app (op U) s)
        (d_zero_val_app_of_d_zero O s hs g) := by
  refine (eq_cocycleHomOver O _).trans ?_
  have h : cocycleOfOver O (cocycleHomOver O A U s hs ≫
      ((overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).map g) =
      (g.f 0).val.app (op U) s :=
    (cocycleOfOver_comp O (cocycleHomOver O A U s hs) g).trans
      (congrArg ((g.f 0).val.app (op U)) (cocycleOfOver_cocycleHomOver O A U s hs))
  congr 1

end Cocycle

end SheafOfModules

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.DerivedTensor.ExtensionByZero (restriction)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Whiskering a morphism of complexes on the right carries a local pure tensor to the local
pure tensor of the image.** -/
theorem whiskerRight_f_tensorComplexSection
    {K Mc Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O} (j : K ⟶ Mc)
    (t r c : ℤ) (htr : t + r = c) {W : X.C} (k₀ : (K.X t).val.obj (op W))
    (l₀ : (Nc.X r).val.obj (op W)) :
    (((j ▷ Nc : (K ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O) ⟶
          Mc ⊗ Nc).f c)).val.app (op W) (tensorComplexSection X t r c htr k₀ l₀) =
      tensorComplexSection X t r c htr ((j.f t).val.app (op W) k₀) l₀ := by
  have h := tensorComplexMap_tensorComplexSection X j (𝟙 Nc) t r c htr k₀ l₀
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.trans (congrArg (tensorComplexSection X t r c htr _) (id_f_val_app_apply X Nc r W l₀))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The chain-level representative attached to a degree-zero cocycle section restricts, along
an arrow of the site, to the one attached to the restricted section.** -/
theorem restrictComplexMapAlong_cocycleHomOver {V W : X.C} (g : W ⟶ V)
    {F : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O}
    (t : (F.X 0).val.obj (op V)) (ht : (F.d 0 1).val.app (op V) t = 0) :
    restrictComplexMapAlong X g
        ((SheafOfModules.overFunctorUnitComplexIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).hom ≫
          SheafOfModules.cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F V t ht) =
      (SheafOfModules.overFunctorUnitComplexIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).hom ≫
        SheafOfModules.cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F W
          ((F.X 0).val.map g.op t)
          (SheafOfModules.d_zero_map_of_d_zero
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g t ht) := by
  have hsec : SheafOfModules.cocycleOfOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      ((SheafOfModules.overFunctorUnitComplexIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).inv ≫
        restrictComplexMapAlong X g
          ((SheafOfModules.overFunctorUnitComplexIso
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).hom ≫
            SheafOfModules.cocycleHomOver
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F V t ht)) =
      (F.X 0).val.map g.op t := by
    refine (cocycleOfOver_restrictComplexMapAlong X g _).trans ?_
    refine congrArg ((F.X 0).val.map g.op) ?_
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact SheafOfModules.cocycleOfOver_cocycleHomOver _ F V t ht
  refine (Iso.inv_comp_eq _).1 ((SheafOfModules.eq_cocycleHomOver _ _).trans ?_)
  congr 1

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **A local direct-summand criterion over an object of the site.** Let
`s : S ⟶ M^• ⊗ N^•` be a morphism of complexes whose image in `D(O)` is `Q(j) ▷ Q(N^•)` up to an
isomorphism `Q(S) ≅ Q(K) ⊗^L Q(N^•)`. If, over an object `W` of `C`, the coevaluation of
`M ⊣ N` is induced by the cocycle section `s(t)` for a degree-zero cocycle section `t` of `S`
over `W`, then `M|_W` is a retract of `K|_W` in `D(O|_W)`. -/
theorem nonempty_retract_restrictOver (W : X.C)
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N)
    (Mc Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)
    (eM : DerivedCategory.Q.obj Mc ≅ M) (eN : DerivedCategory.Q.obj Nc ≅ N)
    (hM : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Mc)
    (hN : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Nc)
    (K S : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O) (j : K ⟶ Mc) :
    letI := derivedMonoidal X.O
    ∀ (s : S ⟶ (Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O))
      (Θ : DerivedCategory.Q.obj S ≅
        DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj Nc)
      (_ : Θ.hom ≫ (DerivedCategory.Q.map j ▷ DerivedCategory.Q.obj Nc) =
        DerivedCategory.Q.map s ≫
          ((symmetricMonoidalDerived X.O).comparison Mc Nc hM hN).inv)
      (t : (S.X 0).val.obj (op W)) (_ : (S.d 0 1).val.app (op W) t = 0)
      (t₀ : ((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O).X 0).val.obj (op W))
      (ht₀ : ((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O).d
        0 1).val.app (op W) t₀ = 0)
      (_ : (s.f 0).val.app (op W) t = t₀),
      (restriction X W).mapDerivedCategory.map (coevaluationUnitHom X Mc Nc hM hN
          (letI := pair
           η_ M N ≫ (eM.inv ⊗ₘ eN.inv))) ≫
          (restriction X W).mapDerivedCategoryFactors.hom.app (Mc ⊗ Nc) =
        (restriction X W).mapDerivedCategoryFactors.hom.app (structureSheafComplex X) ≫
          DerivedCategory.Q.map
            ((SheafOfModules.overFunctorUnitComplexIso
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).hom ≫
              SheafOfModules.cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                (Mc ⊗ Nc) W t₀ ht₀) →
      Nonempty (Retract ((restriction X W).mapDerivedCategory.obj M)
        ((restriction X W).mapDerivedCategory.obj (DerivedCategory.Q.obj K))) := by
  let := derivedMonoidal X.O
  let := pair
  intro s Θ hΘ t ht t₀ ht₀ hst hβ
  subst hst
  let := derivedMonoidal (X.O.over W)
  let := Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X W
  refine nonempty_retract_map_of_factorization (restriction X W).mapDerivedCategory M N
    (symmetricMonoidalDerived X.O).unitIso eM eN
    ((symmetricMonoidalDerived X.O).comparison Mc Nc hM hN) (DerivedCategory.Q.map j)
    (DerivedCategory.Q.map s) Θ hΘ
    ((restriction X W).mapDerivedCategoryFactors.app (structureSheafComplex X))
    ((restriction X W).mapDerivedCategoryFactors.app S)
    ((restriction X W).mapDerivedCategoryFactors.app (Mc ⊗ Nc))
    (DerivedCategory.Q.map
      (((restriction X W).mapHomologicalComplex (ComplexShape.up ℤ)).map s))
    ((restriction X W).mapDerivedCategoryFactors_hom_naturality s)
    (DerivedCategory.Q.map
      ((SheafOfModules.overFunctorUnitComplexIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).hom ≫
        SheafOfModules.cocycleHomOver (Stacks.SheafOfModules.Tensor.ringSheaf X.O) S W t ht))
    (hβ.trans ?_)
  refine congrArg (_ ≫ ·) ((congrArg DerivedCategory.Q.map ?_).trans
    (DerivedCategory.Q.map_comp _ _))
  exact ((Category.assoc _ _ _).trans (congrArg
    (((SheafOfModules.overFunctorUnitComplexIso
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).hom ≫ ·))
    (SheafOfModules.cocycleHomOver_comp
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W t ht s))).symm

/-- **The local retract of Stacks 0FPV, on a ringed site.** Let `N` be a left dual of `M` in
`D(O)`, represented by K-flat complexes `M^•` and `N^•`, and let `V` be an object of `C`. There
is a covering family of `V` along each member `W` of which there are finitely many sections `a`
of the terms of `M^•` over `W` such that, for every morphism of complexes `j : K ⟶ M^•` which
stays a monomorphism after `- ⊗ N^•` in degree `1` and through which the `a` lift, `M|_W` is a
retract of `K|_W` in `D(O|_W)`. -/
theorem exists_presieve_localRetract (V : X.C)
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N)
    (Mc Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)
    (eM : DerivedCategory.Q.obj Mc ≅ M) (eN : DerivedCategory.Q.obj Nc ≅ N)
    (hM : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Mc)
    (hN : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Nc) :
    letI := derivedMonoidal X.O
    ∃ S : Presieve V, Sieve.generate S ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (h : W ⟶ V), S h →
        ∃ (κ : Type) (_ : Fintype κ) (deg : κ → ℤ)
          (a : ∀ i, (Mc.X (deg i)).val.obj (op W)),
          ∀ (K : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O) (j : K ⟶ Mc),
            Mono ((j ▷ Nc).f 1) →
            (∀ i, ∃ y : (K.X (deg i)).val.obj (op W),
              (j.f (deg i)).val.app (op W) y = a i) →
            Nonempty (Retract ((restriction X W).mapDerivedCategory.obj M)
              ((restriction X W).mapDerivedCategory.obj (DerivedCategory.Q.obj K))) := by
  let := derivedMonoidal X.O
  let := pair
  classical
  obtain ⟨S₁, hS₁, hdata⟩ := exists_coveringSieve_coevaluationSection X V Mc Nc hM hN
    (η_ M N ≫ (eM.inv ⊗ₘ eN.inv))
  refine ⟨fun {W} _ =>
    ∃ (κ : Type) (_ : Fintype κ) (deg : κ → ℤ)
      (a : ∀ i, (Mc.X (deg i)).val.obj (op W)),
      ∀ (K : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O) (j : K ⟶ Mc),
        Mono ((j ▷ Nc).f 1) →
        (∀ i, ∃ y : (K.X (deg i)).val.obj (op W),
          (j.f (deg i)).val.app (op W) y = a i) →
        Nonempty (Retract ((restriction X W).mapDerivedCategory.obj M)
          ((restriction X W).mapDerivedCategory.obj (DerivedCategory.Q.obj K))),
    ?_, fun _ _ hh => hh⟩
  refine X.J.transitive hS₁ _ fun {W₁} f hf => ?_
  obtain ⟨t, ht, hβ₁⟩ := hdata f hf
  obtain ⟨T, hT, hsum⟩ := exists_sieve_sum_tensorComplexSection X Mc Nc 0 W₁ t
  refine X.J.superset_covering (fun {W} g hg => ?_) hT
  obtain ⟨κ, hκ, tdeg, rdeg, hdeg, a, b, hab⟩ := hsum g hg
  refine ⟨W, 𝟙 W, g ≫ f, ⟨κ, hκ, tdeg, a, fun K j hjm hlift => ?_⟩, Category.id_comp _⟩
  choose y hy using hlift
  let := hjm
  obtain ⟨Θ, hΘ⟩ := Stacks.SheafOfModules.DerivedMonoidal.exists_iso_whiskerRight_comp X.O j hM hN
  have hv : ∀ (P : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)
      (c : ∀ i, (P.X (tdeg i)).val.obj (op W)),
      ∃ v : κ → ((P ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O).X 0).val.obj
        (op W), ∀ i, v i = tensorComplexSection X (tdeg i) (rdeg i) 0 (hdeg i) (c i) (b i) :=
    fun P c => ⟨fun i => tensorComplexSection X (tdeg i) (rdeg i) 0 (hdeg i) (c i) (b i),
      fun _ => rfl⟩
  obtain ⟨vK, hvK⟩ := hv K y
  obtain ⟨vM, hvM⟩ := hv Mc a
  have hab' : ((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O).X 0).val.map g.op t
      = ∑ i, vM i :=
    hab.trans (Finset.sum_congr rfl fun i _ => (hvM i).symm)
  have hsu : ((j ▷ Nc : (K ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O) ⟶
          Mc ⊗ Nc).f 0).val.app (op W) (∑ i, vK i) =
      ((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O).X 0).val.map g.op t := by
    rw [hab', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hvK i, hvM i]
    exact (whiskerRight_f_tensorComplexSection X j (tdeg i) (rdeg i) 0 (hdeg i) (y i) (b i)).trans
      (congrArg (fun x => tensorComplexSection X (tdeg i) (rdeg i) 0 (hdeg i) x (b i)) (hy i))
  have hu : ((K ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O).d
      0 1).val.app (op W) (∑ i, vK i) = 0 :=
    SheafOfModules.d_zero_of_mono_f_one (j ▷ Nc) _
      (by rw [hsu]; exact SheafOfModules.d_zero_map_of_d_zero _ g t ht)
  refine nonempty_retract_restrictOver X W M N pair Mc Nc eM eN hM hN K (K ⊗ Nc) j
    (j ▷ Nc) Θ hΘ (∑ i, vK i) hu _
    (SheafOfModules.d_zero_map_of_d_zero (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g t ht)
    hsu ?_
  refine (mapDerivedCategory_map_eq_restrictComplexMapAlong X g
    (coevaluationUnitHom X Mc Nc hM hN (η_ M N ≫ (eM.inv ⊗ₘ eN.inv))) _ hβ₁).trans ?_
  exact congrArg (_ ≫ ·) (congrArg DerivedCategory.Q.map
    (restrictComplexMapAlong_cocycleHomOver X g t ht))

end AlgebraicGeometry.RingedSite

end
