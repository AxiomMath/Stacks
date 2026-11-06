module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FieldFundamentalGroup.SeparablePoints

/-!
# The étale fundamental group of a field: the fibre comparison

Let `K` be a field with separable closure `L` and an algebraically closed algebraic extension
`Ω ⊇ L`. Assigning to a scheme finite étale over `Spec K` its `L`-points with their continuous
`Gal(L/K)`-action is an equivalence `FÉt_{Spec K} ≌ ContAction FintypeCat Gal(L/K)`. Extending
an `L`-point along `L → Ω` is a bijection onto the `Ω`-points, so the underlying finite set of
the Galois action is naturally the geometric fibre at the point of `Spec K` determined by `Ω`.

## Main definitions

* `AlgebraicGeometry.algebraicClosureGeometricPoint` — the geometric point of `Spec K` furnished
  by an algebraically closed extension.

## Main results

* `AlgebraicGeometry.finiteEtaleEquivalenceGaloisSets` — finite étale covers of `Spec K` are
  finite continuous `Gal(L/K)`-sets.
* `AlgebraicGeometry.finiteEtaleFiberIso` — the underlying-set functor of that equivalence is
  naturally the geometric fibre, and `AlgebraicGeometry.separableFiberEquiv` identifies a fibre
  with the points over the separable closure.
* `AlgebraicGeometry.finiteEtaleFiberIso_apply`, `AlgebraicGeometry.separableFiberEquiv_map` and
  `AlgebraicGeometry.separableFiberEquiv_smul` — the fibre comparison, its naturality, and the
  absolute Galois action.

## Implementation notes

The equivalence, the fibre comparison and the group isomorphism are named data rather than mere
existential assertions: the fibre and action formulas then characterize the group isomorphism
independently of a choice of categorical equivalence. A separable closure embedded in the
algebraic closure is represented by a scalar tower `K → L → Ω`.

## References

* [Stacks Project, Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete
open scoped CategoryTheory.PreGaloisCategory

universe u v w

namespace AlgebraicGeometry


/-- An equivalence between the small étale site of `Spec K` and continuous `Gal(L/K)`-sets,
compatible with geometric points, restricts to an equivalence between the finite objects and
finite continuous `Gal(L/K)`-sets. -/
public def finiteEtaleSiteGSetEquivalence
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : (Spec (.of K)).Etale ≌ ContinuousGSet Gal(L/K))
    (pointIso : ∀ X : (Spec (.of K)).Etale,
      (E.functor.obj X).obj.obj.V ≃
        (separableClosureGeometricPoint K L ⟶
          (Scheme.Etale.forget (Spec (.of K))).obj X)) :
    finiteEtaleObjectsInEtaleSite (Spec (.of K)) ≌
      FiniteContinuousGSet Gal(L/K) where
  functor := finiteEtaleSiteToFiniteGSet K L E pointIso
  inverse := finiteGSetToFiniteEtaleSite K L E pointIso
  unitIso := NatIso.ofComponents (fun Y =>
    ObjectProperty.isoMk _ (E.unitIso.app Y.1)) (by
      intro Y Z f
      apply ObjectProperty.hom_ext
      exact E.unitIso.hom.naturality f.hom)
  counitIso := NatIso.ofComponents (fun X =>
    ObjectProperty.isoMk _ (E.counitIso.app X.1)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact E.counitIso.hom.naturality f.hom)
  functor_unitIso_comp := by
    intro Y
    apply ObjectProperty.hom_ext
    exact E.functor_unitIso_comp Y.1

/-- Finite étale schemes over `Spec K` are equivalent to continuous actions of `Gal(L/K)` on
finite sets, given an equivalence of the étale site with continuous `Gal(L/K)`-sets compatible
with geometric points. -/
public def finiteEtaleSiteGaloisEquivalence
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (E : (Spec (.of K)).Etale ≌ ContinuousGSet Gal(L/K))
    (pointIso : ∀ X : (Spec (.of K)).Etale,
      (E.functor.obj X).obj.obj.V ≃
        (separableClosureGeometricPoint K L ⟶
          (Scheme.Etale.forget (Spec (.of K))).obj X)) :
    FiniteEtaleOver (Spec (.of K)) ≌
      ContAction FintypeCat.{u} Gal(L/K) :=
  ((finiteEtaleEtaleEquivalence (Spec (.of K))).trans
    (finiteEtaleSiteGSetEquivalence K L E pointIso)).trans
      (finiteContinuousGSetEquivalence (G := Gal(L/K)))

/-- A chosen equivalence between the small étale site of `Spec K` and continuous
`Gal(L/K)`-sets, from `etaleEquivalenceContinuousGSet`. -/
public noncomputable def fieldEtaleEquivalence
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :=
  Classical.choose (etaleEquivalenceContinuousGSet K L)

/-- For each object of the small étale site of `Spec K`, the chosen identification of the
underlying set of its continuous `Gal(L/K)`-set with its `L`-points. -/
public noncomputable def fieldEtalePointIso
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L] :=
  Classical.choose (Classical.choose_spec
    (etaleEquivalenceContinuousGSet K L))

/-- The identification `fieldEtalePointIso` is natural in morphisms of the étale site. -/
theorem fieldEtalePointIso_map
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    {X Z : (Spec (.of K)).Etale} (f : X ⟶ Z)
    (x : ((fieldEtaleEquivalence K L).functor.obj X).obj.obj.V) :
    fieldEtalePointIso K L Z
        (((fieldEtaleEquivalence K L).functor.map f).hom x) =
      fieldEtalePointIso K L X x ≫ (Scheme.Etale.forget (Spec (.of K))).map f :=
  (Classical.choose_spec (Classical.choose_spec
    (etaleEquivalenceContinuousGSet K L))).1 f x

private theorem fieldEtalePointIso_smul
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (X : (Spec (.of K)).Etale) (σ : Gal(L/K))
    (x : ((fieldEtaleEquivalence K L).functor.obj X).obj.obj.V) :
    (fieldEtalePointIso K L X
        (ConcreteCategory.hom
          (((fieldEtaleEquivalence K L).functor.obj X).obj.obj.ρ σ).asHom x)).left =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        (fieldEtalePointIso K L X x).left :=
  (Classical.choose_spec (Classical.choose_spec
    (etaleEquivalenceContinuousGSet K L))).2 X σ x

/-- The underlying set of the continuous `Gal(L/K)`-set attached to a finite étale `K`-scheme
`Y` is the set of `L`-points of `Y` over `K`. -/
public noncomputable def finiteEtalePointEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsSepClosure K L]
    (Y : FiniteEtaleOver (Spec (.of K))) [Etale Y.hom] :
    ((fieldEtaleEquivalence K L).functor.obj (Scheme.Etale.mk Y.hom)).obj.obj.V ≃
      { f : Spec (.of L) ⟶ Y.left //
        f ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) } := by
  let P := separableClosureGeometricPoint K L
  let Q := (Scheme.Etale.forget (Spec (.of K))).obj (Scheme.Etale.mk Y.hom)
  exact (fieldEtalePointIso K L (Scheme.Etale.mk Y.hom)).trans
    (overHomPointEquiv P Q)

/-- For a finite étale `K`-scheme `Y`, extending points along `Spec Ω ⟶ Spec L` identifies
the `L`-points of `Y` with its `Ω`-points. -/
public noncomputable def algebraicPointExtensionEquiv
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (Y : FiniteEtaleOver (Spec (.of K))) :
    {g : Spec (.of L) ⟶ Y.left //
      g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L))} ≃
    {g : Spec (.of Ω) ⟶ Y.left //
      g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω))} := by
  classical
  letI : Etale Y.hom := Y.prop.2
  letI : IsFinite Y.hom := Y.prop.1
  choose I E hField hAlg hFinite hSep e he using
    (etale_iff_iso_coproduct_spectra_finite_separable K Y.hom).mp
      (inferInstance : Etale Y.hom)
  letI : ∀ i, Field (E i) := hField
  letI : ∀ i, Algebra K (E i) := hAlg
  letI : ∀ i, Module.Finite K (E i) := hFinite
  letI : ∀ i, Algebra.IsSeparable K (E i) := hSep
  letI : Finite I := finite_index_of_isFinite K Y.hom I E e he
  exact Equiv.ofBijective (extendSeparablePoint K L Ω Y.hom)
    ⟨point_extension_injective_with_decomposition K L Ω Y.hom I E e he,
      point_extension_surjective_with_decomposition K L Ω Y.hom I E e he⟩

/-- The geometric point of `Spec K` furnished by an algebraically closed
extension. -/
public def algebraicClosureGeometricPoint (K Ω : Type u) [Field K]
    [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    GeometricPoint (Spec (.of K)) :=
  { residueField := Ω
    hom := Spec.map (CommRingCat.ofHom (algebraMap K Ω)) }

/-- Finite étale covers of a field are finite continuous sets for its absolute
Galois group. -/
@[stacks 0BNE "part (1): equivalence", sga "4½ Arcata 2.4.2" "partial", sga "4½ Arcata 2.4.3"]
public noncomputable def finiteEtaleEquivalenceGaloisSets
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] :
    FiniteEtaleOver (Spec (.of K)) ≌
      ContAction FintypeCat.{u} Gal(L/K) := by
  let E := fieldEtaleEquivalence K L
  let pointIso := fieldEtalePointIso K L
  exact finiteEtaleSiteGaloisEquivalence K L E pointIso

/-- The identification `finiteEtalePointEquiv` is natural: it sends the image of a point under
a morphism to the composite of its `L`-point with that morphism. -/
theorem finiteEtalePointEquiv_map
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    {Y Z : FiniteEtaleOver (Spec (.of K))}
    [Etale Y.hom] [Etale Z.hom] (f : Y ⟶ Z)
    (y : ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj) :
    (finiteEtalePointEquiv K L Z
      (ConcreteCategory.hom
        ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.map f) y)).1 =
      (finiteEtalePointEquiv K L Y y).1 ≫ f.left := by
  classical
  let : Etale Y.hom := Y.prop.2
  let : Etale Z.hom := Z.prop.2
  let Y' : (Spec (.of K)).Etale := Scheme.Etale.mk Y.hom
  let Z' : (Spec (.of K)).Etale := Scheme.Etale.mk Z.hom
  let fOver : (Scheme.Etale.forget (Spec (.of K))).obj Y' ⟶
      (Scheme.Etale.forget (Spec (.of K))).obj Z' := Over.homMk f.left f.hom.w
  let f' : Y' ⟶ Z' :=
    (Scheme.Etale.forgetFullyFaithful (Spec (.of K))).preimage fOver
  have hcarrier :
      ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj =
        ((fieldEtaleEquivalence K L).functor.obj Y').obj.obj.V := rfl
  let y' : ((fieldEtaleEquivalence K L).functor.obj Y').obj.obj.V := hcarrier ▸ y
  have h := fieldEtalePointIso_map K L f' y'
  have hmap :
      ConcreteCategory.hom
          ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.map f) y =
        ((fieldEtaleEquivalence K L).functor.map f').hom y' := rfl
  rw [hmap]
  exact congrArg (fun x => x.left) h

/-- The identification `algebraicPointExtensionEquiv` is natural in morphisms of finite étale
`K`-schemes. -/
theorem algebraicPointExtensionEquiv_map
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω]
    [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    {Y Z : FiniteEtaleOver (Spec (.of K))} (f : Y ⟶ Z)
    (p : {g : Spec (.of L) ⟶ Y.left //
      g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L))}) :
    algebraicPointExtensionEquiv K L Ω Z
        ⟨p.1 ≫ f.left, by
          have hcomp : f.left ≫ Z.hom = Y.hom := by simpa using f.hom.w
          calc
            p.1 ≫ f.left ≫ Z.hom = p.1 ≫ (f.left ≫ Z.hom) := by cat_disch
            _ = p.1 ≫ Y.hom := by rw [hcomp]
            _ = _ := p.2⟩ =
      ⟨(algebraicPointExtensionEquiv K L Ω Y p).1 ≫ f.left, by
        have hcomp : f.left ≫ Z.hom = Y.hom := by simpa using f.hom.w
        calc
          ((algebraicPointExtensionEquiv K L Ω Y p).1 ≫ f.left) ≫ Z.hom =
              (algebraicPointExtensionEquiv K L Ω Y p).1 ≫
                (f.left ≫ Z.hom) := by cat_disch
          _ = (algebraicPointExtensionEquiv K L Ω Y p).1 ≫ Y.hom := by rw [hcomp]
          _ = _ := (algebraicPointExtensionEquiv K L Ω Y p).2⟩ :=
  Subtype.ext rfl

/-- The underlying finite Galois set of a cover is naturally its geometric
fibre over the algebraic closure. -/
@[stacks 0BNE "part (1): natural fibre comparison"]
public noncomputable def finiteEtaleFiberIso
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] :
    (finiteEtaleEquivalenceGaloisSets K L Ω).functor ⋙
        forget₂ (ContAction FintypeCat.{u} Gal(L/K)) FintypeCat.{u} ⋙
      forget FintypeCat.{u} ≅
      finiteEtaleFiberFunctor
        (algebraicClosureGeometricPoint K Ω) := by
  let Φ (Y : FiniteEtaleOver (Spec (.of K))) :
      ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj ≃
        (finiteEtaleFiberFunctor
          (algebraicClosureGeometricPoint K Ω)).obj Y := by
    letI : Etale Y.hom := Y.prop.2
    have hcarrier :
        ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj =
          ((fieldEtaleEquivalence K L).functor.obj
            (Scheme.Etale.mk Y.hom)).obj.obj.V := rfl
    simpa only [hcarrier, finiteEtaleFiberFunctor,
      finiteEtaleFiber, algebraicClosureGeometricPoint] using
      (finiteEtalePointEquiv K L Y).trans (algebraicPointExtensionEquiv K L Ω Y)
  refine NatIso.ofComponents (fun Y => Equiv.toIso (Φ Y)) ?_
  intro Y Z f
  let : Etale Y.hom := Y.prop.2
  let : Etale Z.hom := Z.prop.2
  ext y
  change ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj at y
  change (algebraicPointExtensionEquiv K L Ω Z)
      (finiteEtalePointEquiv K L Z
        (ConcreteCategory.hom
          ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.map f) y)) =
    (finiteEtaleFiberFunctor
      (algebraicClosureGeometricPoint K Ω)).map f
      ((algebraicPointExtensionEquiv K L Ω Y)
        ((finiteEtalePointEquiv K L Y) y))
  have hp :
      finiteEtalePointEquiv K L Z
          (ConcreteCategory.hom
            ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.map f) y) =
        ⟨(finiteEtalePointEquiv K L Y y).1 ≫ f.left, by
          rw [Category.assoc, show f.left ≫ Z.hom = Y.hom by simpa using f.hom.w]
          exact (finiteEtalePointEquiv K L Y y).2⟩ :=
    Subtype.ext (finiteEtalePointEquiv_map K L Ω f y)
  rw [hp]
  exact algebraicPointExtensionEquiv_map K L Ω f
    ((finiteEtalePointEquiv K L Y) y)

/-- The geometric fibre of a finite étale cover of a field at a point given by an algebraically
closed extension is finite, because the fibre comparison identifies it with the underlying set of
a finite continuous Galois set. -/
@[sga "4½ Arcata 2.4.2" "Finiteness of Hom_K(A"]
public theorem finite_finiteEtaleFiber_algebraicClosureGeometricPoint
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] (Y : FiniteEtaleOver (Spec (.of K))) :
    Finite ((finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω)).obj Y) :=
  Finite.of_equiv ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj
    ((finiteEtaleFiberIso K L Ω).app Y).toEquiv

/-- The geometric fibre functor at the point given by `Ω`, as a functor to finite sets. -/
public def algebraicClosureFiberFintypeFunctor
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] :
    FiniteEtaleOver (Spec (.of K)) ⥤ FintypeCat.{u} :=
  ObjectProperty.lift Finite (finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω))
    (fun Y => finite_finiteEtaleFiber_algebraicClosureGeometricPoint K L Ω Y)

/-- The fibre comparison `finiteEtaleFiberIso` as an isomorphism of finite-set-valued
functors. -/
public def finiteEtaleFiberActionIso
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] :
    (finiteEtaleEquivalenceGaloisSets K L Ω).functor ⋙
        forget₂ (ContAction FintypeCat.{u} Gal(L/K)) FintypeCat.{u} ≅
      algebraicClosureFiberFintypeFunctor K L Ω :=
  NatIso.ofComponents (fun Y => FintypeCat.equivEquivIso
      (((finiteEtaleFiberIso K L Ω).app Y).toEquiv :
        ((finiteEtaleEquivalenceGaloisSets K L Ω).functor ⋙
          forget₂ (ContAction FintypeCat.{u} Gal(L/K)) FintypeCat.{u} ⋙
            FintypeCat.incl).obj Y ≃
          (finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω)).obj Y)) (by
    intro Y Z f
    apply FintypeCat.hom_ext
    intro x
    exact congrArg (fun g => g x) ((finiteEtaleFiberIso K L Ω).hom.naturality f))

/-- The Galois set attached to a finite étale cover is the set of its points
over the separable closure. -/
@[stacks 0BNE "part (1): separable-closure fibre"]
public noncomputable def separableFiberEquiv
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
  (Y : FiniteEtaleOver (Spec (.of K))) :
    ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V ≃
      { f : Spec (.of L) ⟶ Y.left //
        f ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) } := by
  letI : Etale Y.hom := Y.prop.2
  have hcarrier :
      (((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V).obj =
        ((fieldEtaleEquivalence K L).functor.obj (Scheme.Etale.mk Y.hom)).obj.obj.V := rfl
  simpa only [hcarrier] using finiteEtalePointEquiv K L Y

private theorem separableFiberEquiv_apply_eq_pointEquiv
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (Y : FiniteEtaleOver (Spec (.of K))) [Etale Y.hom]
    (y : ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V) :
    (separableFiberEquiv K L Ω Y y).1 =
      (finiteEtalePointEquiv K L Y
        (show ((fieldEtaleEquivalence K L).functor.obj
          (Scheme.Etale.mk Y.hom)).obj.obj.V from y)).1 := by
  classical
  rfl

/-- The natural fibre comparison is extension of a separable-closure point
to the algebraic closure. -/
@[stacks 0BNE "part (1): fibre comparison formula"]
public theorem finiteEtaleFiberIso_apply
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (Y : FiniteEtaleOver (Spec (.of K)))
    (y : ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V) :
    (((finiteEtaleFiberIso K L Ω).hom.app Y) y).1 =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        (separableFiberEquiv K L Ω Y y).1 := by
  classical
  let : Etale Y.hom := Y.prop.2
  show (algebraicPointExtensionEquiv K L Ω Y
      (finiteEtalePointEquiv K L Y y)).1 = _
  rw [separableFiberEquiv_apply_eq_pointEquiv K L Ω Y]
  rfl

/-- The separable-closure description is natural in a finite étale cover. -/
@[stacks 0BNE "part (1): naturality over the separable closure"]
public theorem separableFiberEquiv_map
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    {Y Z : FiniteEtaleOver (Spec (.of K))} (f : Y ⟶ Z)
    (y : ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V) :
    (separableFiberEquiv K L Ω Z
      (ConcreteCategory.hom
        ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.map f) y)).1 =
      (separableFiberEquiv K L Ω Y y).1 ≫ f.left := by
  let : Etale Y.hom := Y.prop.2
  let : Etale Z.hom := Z.prop.2
  rw [separableFiberEquiv_apply_eq_pointEquiv K L Ω Z,
    separableFiberEquiv_apply_eq_pointEquiv K L Ω Y]
  exact finiteEtalePointEquiv_map K L Ω f y

/-- The Galois action on a separable-closure point is precomposition with
the corresponding field automorphism. -/
@[stacks 0BNE "part (1): Galois action"]
public theorem separableFiberEquiv_smul
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (Y : FiniteEtaleOver (Spec (.of K)))
    (σ : Gal(L/K))
    (y : ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V) :
    (separableFiberEquiv K L Ω Y
      (ConcreteCategory.hom
        (((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.ρ σ).asHom y)).1 =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        (separableFiberEquiv K L Ω Y y).1 := by
  classical
  let : Etale Y.hom := Y.prop.2
  let Y' : (Spec (.of K)).Etale := Scheme.Etale.mk Y.hom
  have hcarrier :
      ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj =
        ((fieldEtaleEquivalence K L).functor.obj Y').obj.obj.V := rfl
  let y' : ((fieldEtaleEquivalence K L).functor.obj Y').obj.obj.V := hcarrier ▸ y
  have h := fieldEtalePointIso_smul K L Y' σ y'
  have hsmul :
      ConcreteCategory.hom
          (((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.ρ σ).asHom y =
        ConcreteCategory.hom
          (((fieldEtaleEquivalence K L).functor.obj Y').obj.obj.ρ σ).asHom y' := rfl
  rw [separableFiberEquiv_apply_eq_pointEquiv K L Ω Y, hsmul,
    separableFiberEquiv_apply_eq_pointEquiv K L Ω Y]
  exact h

end AlgebraicGeometry

end
