module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomPairing
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.TraceTarget
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings

/-!
# The derived morphism of a pairing into the trace target

Let `R` be a finite ring, `Q` a compact topological group, `S` a ring and `φ : S →+* Rᵐᵒᵖ`. A
pairing `P` (`Stacks.ContinuousCohomology.ComplexPairing`) of a complex `A` of discrete
`S`-`Q`-modules with a complex `E` of discrete `R`-`Q`-modules, valued in the injective resolution
`T` of `ℚ/ℤ[-d]` (`Stacks.ContinuousCohomology.traceTarget`), is a morphism of complexes of
`S[[Q]]`-modules `A ⟶ Hom^•_ℤ(E, T)` (`Stacks.ContinuousCohomology.internalHomComplexOfPairing`).
Since `Hom^•_ℤ(E, ℚ/ℤ[-d]) ⟶ Hom^•_ℤ(E, T)` is a quasi-isomorphism and `Hom^•_ℤ(E, ℚ/ℤ[-d])` is the
contragredient of `E` shifted by `-d`, this gives a morphism in the derived category of
`S[[Q]]`-modules `A ⟶ (E^∨)[-d]`, `E^∨` the derived contragredient over `Rᵐᵒᵖ[[Q]]`, with scalars
restricted along `mapCoeff φ` (`Stacks.ContinuousCohomology.derivedPairing`). It is an isomorphism
as soon as the chain map `A ⟶ Hom^•_ℤ(E, T)` is a quasi-isomorphism
(`Stacks.ContinuousCohomology.isIso_derivedPairing`).

For Tag 03VM: `S = Λ`, `R = Λᵐᵒᵖ`, `φ = RingEquiv.opOp Λ`, `A` computes `RΓ_c(X_k̄, ℱ)`, `E`
computes `RHom(ℱ, μ_n)`, `d = 2`, and the pairing is evaluation followed by the trace.

The chain maps attached to pairings are natural for compatible morphisms of the two arguments
(`Stacks.ContinuousCohomology.internalHomComplexOfPairing_naturality`).

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex Stacks.GroupHomology

universe u u' v w

namespace Stacks.ContinuousCohomology

open InternalHomCochain

section Naturality

variable {R : Type u} [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] {S : Type u'} [Ring S] {φ : S →+* Rᵐᵒᵖ}
  {A₁ A₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{u', v, w} S Q) ℤ}
  {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ}
  {G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ}

/-- **The chain map of a pairing is natural** for a morphism `f : A₁ ⟶ A₂` and a morphism
`g : E₂ ⟶ E₁` that are adjoint for the two pairings, `P₂(f a, e) = P₁(a, g e)`. -/
theorem internalHomComplexOfPairing_naturality (P₁ : ComplexPairing R φ A₁ E₁ G)
    (P₂ : ComplexPairing R φ A₂ E₂ G) (f : A₁ ⟶ A₂) (g : E₂ ⟶ E₁)
    (h : ∀ (n p q : ℤ) (hpq : p + n = q) (a : (A₁.X n).obj.obj.V) (e : (E₂.X p).obj.obj.V),
      P₂.pair n p q hpq ((f.f n).hom.hom.hom.hom a) e =
        P₁.pair n p q hpq a ((g.f p).hom.hom.hom.hom e)) :
    ((discreteToCompletedGroupAlgebra.{u', v, w} S Q).mapHomologicalComplex _).map f ≫
        internalHomComplexOfPairing P₂ =
      internalHomComplexOfPairing P₁ ≫
        ((ModuleCat.restrictScalars
          (CompletedGroupAlgebra.mapCoeff (G := Q) φ)).mapHomologicalComplex _).map
          (internalHomComplexPrecomp R E₁ G g) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun a => ?_
  apply InternalHomCochain.ext
  refine Cochain.ext _ _ fun p q hpq => ?_
  change (toCochain (P₂.cochain n ((f.f n).hom.hom.hom.hom a))).v p q hpq =
    ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map g)).comp
      (toCochain (P₁.cochain n a)) (zero_add n)).v p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun e => h n p q hpq a e)

variable {A : CochainComplex (Stacks.Injectives.ContinuousModule.{u', v, w} S Q) ℤ}
  {E : CochainComplex (Stacks.Injectives.ContinuousModule.{u, v, w} R Q) ℤ}

/-- **A pairing followed by a morphism of complexes** `t : G ⟶ G'` of discrete `ℤ`-`Q`-modules. -/
def ComplexPairing.postcomp (P : ComplexPairing R φ A E G)
    {G' : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ} (t : G ⟶ G') :
    ComplexPairing R φ A E G' where
  pair n p q h := (P.pair n p q h).compr₂ (t.f q).hom.hom.hom.hom.toAddMonoidHom
  galois n p q h σ a e := by
    change (t.f q).hom.hom.hom.hom (P.pair n p q h _ e) =
      ((G'.X q).obj.obj.ρ σ).asHom.hom ((t.f q).hom.hom.hom.hom (P.pair n p q h a _))
    rw [P.galois]
    exact ConcreteCategory.congr_hom ((t.f q).hom.hom.comm σ) _
  balanced n p q h s a e := by
    change (t.f q).hom.hom.hom.hom (P.pair n p q h (s • a) e) =
      (t.f q).hom.hom.hom.hom (P.pair n p q h a _)
    rw [P.balanced]
  leibniz n p q q' h hq a e := by
    change (t.f q').hom.hom.hom.hom (P.pair (n + 1) p q' _ _ e) =
      (G'.d q q').hom.hom.hom.hom ((t.f q).hom.hom.hom.hom (P.pair n p q h a e)) +
        (n + 1).negOnePow • (t.f q').hom.hom.hom.hom (P.pair n (p + 1) q' _ a _)
    rw [P.leibniz n p q q' h hq, map_add, Units.smul_def, Units.smul_def, map_zsmul]
    congr 1
    exact (ConcreteCategory.congr_hom (congrArg (fun x => x.hom.hom.hom) (t.comm q q')) _).symm

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The value of `P.postcomp t` on `a` and `e` is `t` applied to the value of `P`. -/
lemma ComplexPairing.postcomp_pair (P : ComplexPairing R φ A E G)
    {G' : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ} (t : G ⟶ G')
    (n p q : ℤ) (h : p + n = q) (a : (A.X n).obj.obj.V) (e : (E.X p).obj.obj.V) :
    (P.postcomp t).pair n p q h a e = (t.f q).hom.hom.hom.hom (P.pair n p q h a e) := rfl

end Naturality

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] {S : Type} [Ring S] (φ : S →+* Rᵐᵒᵖ)

/-- Restriction of scalars along `mapCoeff φ : S[[Q]] →+* Rᵐᵒᵖ[[Q]]`. -/
abbrev pairingRestrict :
    ModuleCat.{max v w} (CompletedGroupAlgebra Rᵐᵒᵖ Q) ⥤
      ModuleCat.{max v w} (CompletedGroupAlgebra S Q) :=
  ModuleCat.restrictScalars.{max v w} (CompletedGroupAlgebra.mapCoeff (G := Q) φ)

/-- Restriction of scalars along `mapCoeff φ` preserves finite limits. -/
instance pairingRestrict_preservesFiniteLimits :
    PreservesFiniteLimits (pairingRestrict.{v, w} R (Q := Q) φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits _

/-- Restriction of scalars along `mapCoeff φ` preserves finite colimits. -/
instance pairingRestrict_preservesFiniteColimits :
    PreservesFiniteColimits (pairingRestrict.{v, w} R (Q := Q) φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits _

/-- **The internal Hom complex as a contravariant functor** of its first argument, through
precomposition. -/
def internalHomComplexFunctor
    (G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ) :
    (CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} R Q) ℤ)ᵒᵖ ⥤
      CochainComplex (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) ℤ where
  obj E := internalHomComplex R E.unop G
  map g := internalHomComplexPrecomp R _ G g.unop
  map_id E := by
    refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
    apply InternalHomCochain.ext
    change (Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map (𝟙 E.unop))).comp
      (toCochain z) (zero_add n) = toCochain z
    rw [CategoryTheory.Functor.map_id, Cochain.id_comp]
  map_comp f g := by
    refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z => ?_
    apply InternalHomCochain.ext
    change (Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map (g.unop ≫ f.unop))).comp
        (toCochain z) (zero_add n) =
      (Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map g.unop)).comp
        ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map f.unop)).comp
          (toCochain z) (zero_add n)) (zero_add n)
    rw [CategoryTheory.Functor.map_comp, Cochain.ofHom_comp,
      Cochain.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by omega)]

/-- **The identification of the internal Hom complex into `W[-q]` is natural in `E`.** -/
lemma internalHomSingleIso_hom_naturality
    {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} R Q) ℤ} (g : E₂ ⟶ E₁)
    (W : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) (q : ℤ) :
    internalHomComplexPrecomp R E₁ (singleComplex W q) g ≫ (internalHomSingleIso R E₂ W q).hom =
      (internalHomSingleIso R E₁ W q).hom ≫
        ((((internalHom.{0, v, w, w} R Q).flip.obj W).mapHomologicalComplex _).map
          ((CochainComplex.opEquivalence _).functor.map g.op))⟦-q⟧' := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <| LinearMap.ext fun z =>
    AddMonoidHom.ext fun v => ?_
  change (internalHomSingleFun R E₂ W q n (of ((Cochain.ofHom
      (((forgetAb R Q).mapHomologicalComplex _).map g)).comp (toCochain z) (zero_add n)))).hom v =
    (internalHomSingleFun R E₁ W q n z).hom ((g.f (-(n + -q))).hom.hom.hom.hom v)
  unfold internalHomSingleFun
  rw [toCochain_of, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc,
    ← Linear.comp_units_smul]
  rfl

/-- `internalHomSingleIso` as a natural isomorphism in `E`. -/
def internalHomSingleNatIso (W : Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) (q : ℤ) :
    internalHomComplexFunctor R (singleComplex W q) ≅
      (CochainComplex.opEquivalence _).functor ⋙
        ((internalHom.{0, v, w, w} R Q).flip.obj W).mapHomologicalComplex _ ⋙
        shiftFunctor _ (-q) :=
  NatIso.ofComponents (fun E => internalHomSingleIso R E.unop W q)
    (fun g => internalHomSingleIso_hom_naturality R g.unop W q)

/-- **The derived contragredient on complexes**, as a natural isomorphism:
`(Q E)^∨ ≅ Q(E^∨)`, the contragredient of `E` read backwards. -/
def derivedContragredientQNatIso :
    DerivedCategory.Q.op ⋙ derivedContragredient.{0, v, w} R Q ≅
      (CochainComplex.opEquivalence _).functor ⋙
        (contragredient.{0, v, w} R Q).mapHomologicalComplex _ ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
          (Functor.isoWhiskerRight (CochainComplex.opEquivalence
            (Stacks.Injectives.ContinuousModule.{0, v, w} R Q)).unitIso DerivedCategory.Q.op)
          (DerivedCategory.derivedOpEquivalence
            (C := Stacks.Injectives.ContinuousModule.{0, v, w} R Q)).functor ≪≫
        Functor.isoWhiskerLeft (CochainComplex.opEquivalence _).functor
          (DerivedCategory.opQCompDerivedOpEquivalenceFunctorIso
            (C := Stacks.Injectives.ContinuousModule.{0, v, w} R Q)) :
        DerivedCategory.Q.op ⋙ (DerivedCategory.derivedOpEquivalence
            (C := Stacks.Injectives.ContinuousModule.{0, v, w} R Q)).functor ≅
          (CochainComplex.opEquivalence _).functor ⋙ DerivedCategory.Q)
      (contragredient.{0, v, w} R Q).mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (CochainComplex.opEquivalence _).functor
      (contragredient.{0, v, w} R Q).mapDerivedCategoryFactors

variable (d : ℤ)

/-- **The target of the derived pairing**, naturally in `E`: `Hom^•_ℤ(E, ℚ/ℤ[-d])`, with
scalars restricted along `mapCoeff φ`, is the derived contragredient of `E` shifted by `-d`. -/
def derivedPairingTargetNatIso :
    internalHomComplexFunctor R (singleComplex (ratCircle.{v, w} Q) d) ⋙
        (pairingRestrict.{v, w} R φ).mapHomologicalComplex _ ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q.op ⋙ derivedContragredient.{0, v, max v w} R Q ⋙
        (pairingRestrict.{v, w} R φ).mapDerivedCategory ⋙ shiftFunctor _ (-d) :=
  Functor.isoWhiskerRight (internalHomSingleNatIso R (ratCircle.{v, w} Q) d) _ ≪≫
    Functor.isoWhiskerLeft ((CochainComplex.opEquivalence _).functor ⋙
        ((internalHom.{0, v, max v w, max v w} R Q).flip.obj
          (ratCircle.{v, w} Q)).mapHomologicalComplex _)
      (Functor.isoWhiskerRight ((pairingRestrict.{v, w} R φ).mapCochainComplexShiftIso (-d))
          DerivedCategory.Q ≪≫
        Functor.isoWhiskerLeft ((pairingRestrict.{v, w} R φ).mapHomologicalComplex _)
          (DerivedCategory.Q.commShiftIso (-d)) ≪≫
        Functor.isoWhiskerRight (pairingRestrict.{v, w} R φ).mapDerivedCategoryFactors.symm
          (shiftFunctor _ (-d))) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (CochainComplex.opEquivalence _).functor
          (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
            (contragredientULiftIso.{0, v, max v w} R Q) _).symm DerivedCategory.Q) ≪≫
        (derivedContragredientQNatIso.{v, max v w} R).symm)
      ((pairingRestrict.{v, w} R φ).mapDerivedCategory ⋙ shiftFunctor _ (-d))

variable (E : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ)

/-- **The target of the derived pairing**: `Hom^•_ℤ(E, ℚ/ℤ[-d])`, with scalars restricted along
`mapCoeff φ`, is the derived contragredient of `E` shifted by `-d`. -/
def derivedPairingTargetIso :
    DerivedCategory.Q.obj (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).obj
        (internalHomComplex R E (singleComplex (ratCircle.{v, w} Q) d))) ≅
      ((pairingRestrict.{v, w} R φ).mapDerivedCategory.obj
        ((derivedContragredient.{0, v, max v w} R Q).obj
          (Opposite.op (DerivedCategory.Q.obj E))))⟦-d⟧ :=
  (derivedPairingTargetNatIso.{v, w} R φ d).app (Opposite.op E)

variable {R φ}

/-- `Q(g)` is invertible for a quasi-isomorphism `g` after restricting scalars. -/
instance isIso_Q_map_pairingRestrict_map {X Y : CochainComplex
    (ModuleCat.{max v w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) ℤ} (g : X ⟶ Y) [QuasiIso g] :
    IsIso (DerivedCategory.Q.map
      (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map g)) := by
  have h : DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map g) =
      ((pairingRestrict.{v, w} R φ).mapDerivedCategoryFactors.app X).inv ≫
        (pairingRestrict.{v, w} R φ).mapDerivedCategory.map (DerivedCategory.Q.map g) ≫
        ((pairingRestrict.{v, w} R φ).mapDerivedCategoryFactors.app Y).hom := by
    rw [Iso.app_hom, (pairingRestrict.{v, w} R φ).mapDerivedCategoryFactors_hom_naturality g,
      Iso.app_inv, Iso.inv_hom_id_app_assoc]
  rw [h]
  infer_instance

variable (R φ) in
/-- Postcomposition with the augmentation `ℚ/ℤ[-d] ⟶ T`, as an isomorphism in the derived
category of `S[[Q]]`-modules. -/
def derivedPairingPostcompIso :
    DerivedCategory.Q.obj (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).obj
        (internalHomComplex R E (singleComplex (ratCircle.{v, w} Q) d))) ≅
      DerivedCategory.Q.obj (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).obj
        (internalHomComplex R E (traceTarget.{v, w} Q d))) :=
  haveI := quasiIso_postcomp_traceTargetι.{v, w} Q R E d
  asIso (DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
    (internalHomComplexPostcomp R E (traceTargetι.{v, w} Q d))))

/-- Precomposition commutes with the inverse of `derivedPairingPostcompIso`. -/
lemma derivedPairingPostcompIso_inv_naturality
    {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
    (g : E₂ ⟶ E₁) :
    DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
        (internalHomComplexPrecomp R E₁ (traceTarget.{v, w} Q d) g)) ≫
      (derivedPairingPostcompIso.{v, w} R φ d E₂).inv =
      (derivedPairingPostcompIso.{v, w} R φ d E₁).inv ≫
        DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
          (internalHomComplexPrecomp R E₁ (singleComplex (ratCircle.{v, w} Q) d) g)) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  change DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
      (internalHomComplexPostcomp R E₁ (traceTargetι.{v, w} Q d))) ≫ _ = _ ≫
    DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
      (internalHomComplexPostcomp R E₂ (traceTargetι.{v, w} Q d)))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    internalHomComplexPrecomp_postcomp]

variable {A : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ}

/-- **The derived morphism of a pairing into the trace target**:
`A ⟶ Hom^•_ℤ(E, T) ≃ Hom^•_ℤ(E, ℚ/ℤ[-d]) ≅ (E^∨)[-d]` in the derived category of
`S[[Q]]`-modules, `E^∨` the derived contragredient with scalars restricted along `mapCoeff φ`. -/
def derivedPairing (P : ComplexPairing R φ A E (traceTarget.{v, w} Q d)) :
    (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapDerivedCategory.obj
        (DerivedCategory.Q.obj A) ⟶
      ((pairingRestrict.{v, w} R φ).mapDerivedCategory.obj
        ((derivedContragredient.{0, v, max v w} R Q).obj
          (Opposite.op (DerivedCategory.Q.obj E))))⟦-d⟧ :=
  (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapDerivedCategoryFactors.hom.app A ≫
    DerivedCategory.Q.map (internalHomComplexOfPairing P) ≫
    (derivedPairingPostcompIso.{v, w} R φ d E).inv ≫
    (derivedPairingTargetIso.{v, w} R φ d E).hom

/-- The derived pairing is the composite of the comparison isomorphism for `A`, the image of
the chain map of `P`, the inverse of `derivedPairingPostcompIso` and `derivedPairingTargetIso`. -/
lemma derivedPairing_eq (P : ComplexPairing R φ A E (traceTarget.{v, w} Q d)) :
    derivedPairing d E P =
      (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map (internalHomComplexOfPairing P) ≫
        (derivedPairingPostcompIso.{v, w} R φ d E).inv ≫
        (derivedPairingTargetIso.{v, w} R φ d E).hom := rfl

/-- **The derived pairing is an isomorphism when the chain map of the pairing is a
quasi-isomorphism.** -/
theorem isIso_derivedPairing (P : ComplexPairing R φ A E (traceTarget.{v, w} Q d))
    [QuasiIso (internalHomComplexOfPairing P)] : IsIso (derivedPairing d E P) := by
  unfold derivedPairing
  infer_instance

/-- The identification of the target is natural in `E`. -/
lemma derivedPairingTargetIso_hom_naturality
    {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
    (g : E₂ ⟶ E₁) :
    DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
        (internalHomComplexPrecomp R E₁ (singleComplex (ratCircle.{v, w} Q) d) g)) ≫
      (derivedPairingTargetIso.{v, w} R φ d E₂).hom =
      (derivedPairingTargetIso.{v, w} R φ d E₁).hom ≫
        ((pairingRestrict.{v, w} R φ).mapDerivedCategory.map
          ((derivedContragredient.{0, v, max v w} R Q).map (DerivedCategory.Q.map g).op))⟦-d⟧' :=
  (derivedPairingTargetNatIso.{v, w} R φ d).hom.naturality g.op

/-- The part of the derived pairing after the chain map is natural in `E`. -/
lemma derivedPairingPostcompIso_inv_comp_targetIso_hom_naturality
    {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
    (g : E₂ ⟶ E₁) :
    DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
        (internalHomComplexPrecomp R E₁ (traceTarget.{v, w} Q d) g)) ≫
      (derivedPairingPostcompIso.{v, w} R φ d E₂).inv ≫
        (derivedPairingTargetIso.{v, w} R φ d E₂).hom =
      (derivedPairingPostcompIso.{v, w} R φ d E₁).inv ≫
        (derivedPairingTargetIso.{v, w} R φ d E₁).hom ≫
        ((pairingRestrict.{v, w} R φ).mapDerivedCategory.map
          ((derivedContragredient.{0, v, max v w} R Q).map (DerivedCategory.Q.map g).op))⟦-d⟧' := by
  rw [reassoc_of% (derivedPairingPostcompIso_inv_naturality d g),
    derivedPairingTargetIso_hom_naturality]

/-- The chain map of a pairing is natural, read in the derived category. -/
lemma Q_map_internalHomComplexOfPairing_naturality
    {A₁ A₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ}
    {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
    (P₁ : ComplexPairing R φ A₁ E₁ (traceTarget.{v, w} Q d))
    (P₂ : ComplexPairing R φ A₂ E₂ (traceTarget.{v, w} Q d)) (f : A₁ ⟶ A₂) (g : E₂ ⟶ E₁)
    (h : ∀ (n p q : ℤ) (hpq : p + n = q) (a : (A₁.X n).obj.obj.V) (e : (E₂.X p).obj.obj.V),
      P₂.pair n p q hpq ((f.f n).hom.hom.hom.hom a) e =
        P₁.pair n p q hpq a ((g.f p).hom.hom.hom.hom e)) :
    (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapDerivedCategory.map
        (DerivedCategory.Q.map f) ≫
      (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapDerivedCategoryFactors.hom.app A₂ ≫
        DerivedCategory.Q.map (internalHomComplexOfPairing P₂) =
      (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapDerivedCategoryFactors.hom.app A₁ ≫
        DerivedCategory.Q.map (internalHomComplexOfPairing P₁) ≫
        DerivedCategory.Q.map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
          (internalHomComplexPrecomp R E₁ (traceTarget.{v, w} Q d) g)) := by
  rw [← Category.assoc,
    (discreteToCompletedGroupAlgebra.{0, v, max v w}
      S Q).mapDerivedCategoryFactors_hom_naturality f,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun x => _ ≫ DerivedCategory.Q.map x)
    (internalHomComplexOfPairing_naturality P₁ P₂ f g h)

/-- **The derived pairing is natural** for a morphism `f : A₁ ⟶ A₂` and a morphism `g : E₂ ⟶ E₁`
that are adjoint for the two pairings, `P₂(f a, e) = P₁(a, g e)`. -/
theorem derivedPairing_naturality
    {A₁ A₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ}
    {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
    (P₁ : ComplexPairing R φ A₁ E₁ (traceTarget.{v, w} Q d))
    (P₂ : ComplexPairing R φ A₂ E₂ (traceTarget.{v, w} Q d)) (f : A₁ ⟶ A₂) (g : E₂ ⟶ E₁)
    (h : ∀ (n p q : ℤ) (hpq : p + n = q) (a : (A₁.X n).obj.obj.V) (e : (E₂.X p).obj.obj.V),
      P₂.pair n p q hpq ((f.f n).hom.hom.hom.hom a) e =
        P₁.pair n p q hpq a ((g.f p).hom.hom.hom.hom e)) :
    (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapDerivedCategory.map
        (DerivedCategory.Q.map f) ≫ derivedPairing d E₂ P₂ =
      derivedPairing d E₁ P₁ ≫
        ((pairingRestrict.{v, w} R φ).mapDerivedCategory.map
          ((derivedContragredient.{0, v, max v w} R Q).map (DerivedCategory.Q.map g).op))⟦-d⟧' := by
  rw [derivedPairing_eq, derivedPairing_eq,
    reassoc_of% (Q_map_internalHomComplexOfPairing_naturality d P₁ P₂ f g h),
    derivedPairingPostcompIso_inv_comp_targetIso_hom_naturality]
  simp only [Category.assoc]

/-! ### The cohomology of the target -/

variable (R φ) in
/-- **The cohomology of the shifted contragredient**: `H^m((E^∨)[-d]) ≅ (H^{d-m} E)^∨`, with
scalars restricted, naturally in `E`. -/
def derivedPairingTargetHomologyNatIso (m : ℤ) :
    derivedContragredient.{0, v, max v w} R Q ⋙ (pairingRestrict.{v, w} R φ).mapDerivedCategory ⋙
        shiftFunctor _ (-d) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max v w} (CompletedGroupAlgebra S Q)) m ≅
      (DerivedCategory.homologyFunctor
          (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) (d - m)).op ⋙
        contragredient.{0, v, max v w} R Q ⋙ pairingRestrict.{v, w} R φ :=
  Functor.isoWhiskerLeft (derivedContragredient.{0, v, max v w} R Q ⋙
      (pairingRestrict.{v, w} R φ).mapDerivedCategory)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{max v w} (CompletedGroupAlgebra S Q)) 0).shiftIso (-d) m (m - d) (by omega)) ≪≫
    Functor.isoWhiskerLeft (derivedContragredient.{0, v, max v w} R Q)
      ((pairingRestrict.{v, w} R φ).mapDerivedCategoryHomologyFunctorIso (m - d)) ≪≫
    Functor.isoWhiskerRight (derivedContragredientHomologyIso.{0, v, max v w} R Q (m - d) (d - m)
      (by omega)) (pairingRestrict.{v, w} R φ)

variable (R φ) in
/-- `derivedPairingPostcompIso` as a natural isomorphism in `E`. -/
def derivedPairingPostcompNatIso :
    internalHomComplexFunctor R (singleComplex (ratCircle.{v, w} Q) d) ⋙
        (pairingRestrict.{v, w} R φ).mapHomologicalComplex _ ⋙ DerivedCategory.Q ≅
      internalHomComplexFunctor R (traceTarget.{v, w} Q d) ⋙
        (pairingRestrict.{v, w} R φ).mapHomologicalComplex _ ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun E => derivedPairingPostcompIso.{v, w} R φ d E.unop) (fun g => by
    have key := congrArg (fun x => DerivedCategory.Q.map
      (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map x))
      (internalHomComplexPrecomp_postcomp R _ (singleComplex (ratCircle.{v, w} Q) d) g.unop
        (traceTargetι.{v, w} Q d))
    simp only [Functor.map_comp] at key
    exact key)

variable (R φ) in
/-- **The cohomology of `Hom^•_ℤ(E, T)`** in degree `m` is the contragredient of `H^{d-m}(E)`,
with scalars restricted along `mapCoeff φ`, naturally in `E`. -/
def homologyInternalHomComplexTraceTargetNatIso (m : ℤ) :
    internalHomComplexFunctor R (traceTarget.{v, w} Q d) ⋙
        (pairingRestrict.{v, w} R φ).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ m ≅
      (HomologicalComplex.homologyFunctor
          (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) _ (d - m)).op ⋙
        contragredient.{0, v, max v w} R Q ⋙ pairingRestrict.{v, w} R φ :=
  Functor.isoWhiskerLeft (internalHomComplexFunctor R (traceTarget.{v, w} Q d) ⋙
      (pairingRestrict.{v, w} R φ).mapHomologicalComplex _)
      (DerivedCategory.homologyFunctorFactors _ m).symm ≪≫
    Functor.isoWhiskerRight (derivedPairingPostcompNatIso.{v, w} R φ d).symm
      (DerivedCategory.homologyFunctor _ m) ≪≫
    Functor.isoWhiskerRight (derivedPairingTargetNatIso.{v, w} R φ d)
      (DerivedCategory.homologyFunctor _ m) ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q.op
      (derivedPairingTargetHomologyNatIso.{v, w} R φ d m) ≪≫
    Functor.isoWhiskerRight (NatIso.op (DerivedCategory.homologyFunctorFactors
        (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) (d - m))).symm
      (contragredient.{0, v, max v w} R Q ⋙ pairingRestrict.{v, w} R φ)

variable (R φ) in
/-- **The cohomology of `Hom^•_ℤ(E, T)` vanishes in degree `m` when `H^{d-m}(E)` does.** -/
theorem isZero_homology_internalHomComplex_traceTarget
    (E : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ) (m : ℤ)
    (h : IsZero (E.homology (d - m))) :
    IsZero ((((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).obj
        (internalHomComplex R E (traceTarget.{v, w} Q d))).homology m) :=
  IsZero.of_iso ((pairingRestrict.{v, w} R φ).map_isZero
      ((contragredient.{0, v, max v w} R Q).map_isZero h.op))
    ((homologyInternalHomComplexTraceTargetNatIso.{v, w} R φ d m).app (Opposite.op E))

/-- **Precomposition with `g` is zero on the cohomology of `Hom^•_ℤ(-, T)` in degree `m` when
`g` is zero on `H^{d-m}`.** -/
theorem homologyMap_internalHomComplexPrecomp_traceTarget_eq_zero
    {E₁ E₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
    (g : E₂ ⟶ E₁) (m : ℤ) (hg : HomologicalComplex.homologyMap g (d - m) = 0) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{max v w} (CompletedGroupAlgebra S Q))
      (ComplexShape.up ℤ) m).map (((pairingRestrict.{v, w} R φ).mapHomologicalComplex _).map
        (internalHomComplexPrecomp R E₁ (traceTarget.{v, w} Q d) g)) = 0 := by
  have hn := (homologyInternalHomComplexTraceTargetNatIso.{v, w} R φ d m).hom.naturality g.op
  have h0 : ((HomologicalComplex.homologyFunctor
      (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) _ (d - m)).op ⋙
      contragredient.{0, v, max v w} R Q ⋙ pairingRestrict.{v, w} R φ).map g.op = 0 := by
    change (pairingRestrict.{v, w} R φ).map ((contragredient.{0, v, max v w} R Q).map
      (HomologicalComplex.homologyMap g (d - m)).op) = 0
    rw [hg, op_zero, Functor.map_zero, Functor.map_zero]
  rw [h0, comp_zero] at hn
  have h1 := (((homologyInternalHomComplexTraceTargetNatIso.{v, w} R φ d m).app
    (Opposite.op E₂)).eq_comp_inv).2 hn
  exact h1.trans (by simp only [zero_comp]; exact rfl)

end Derived

end Stacks.ContinuousCohomology

end
