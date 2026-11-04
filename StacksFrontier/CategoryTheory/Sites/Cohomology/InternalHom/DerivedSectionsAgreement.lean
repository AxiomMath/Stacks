module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
import StacksCore.Tactic.StacksAttribute

/-! # The two forms of Stacks 08JA agree

Let `(C, O)` be a ringed site. Stacks 08JA has two realizations in this development:

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKFlat`, built directly from a
  K-flat complex `A` and a K-injective complex `I`, using that `SheafHom(A, I)` is then
  K-injective (Stacks 0A96);
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, for arbitrary objects `L`,
  `M` of `D(O)`, obtained from the first at the *chosen* models `kFlatModel X L` and
  `kInjectiveModel X M`.

Since the chosen models are in general different complexes from a given pair representing `L` and
`M`, the agreement of the two is a statement and not a definitional unfolding, and it was listed
as absent in the module note of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects`. This
file supplies it.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply_of_isKFlat`:
  **Stacks 08JA at arbitrary objects is Stacks 08JA at any K-flat/K-injective pair representing
  them**, conjugated by `derivedSheafHomObjectsModelIso` and by the two representing
  isomorphisms. The statement at the chosen models,
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply_assoc`, is the case
  `eA = kFlatModelIso X L`, `eI = kInjectiveModelIso X M`, where it holds by `rfl`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_of_isKFlat`: the same
  statement read as an equality of the two bijections, the comparison being an additive
  isomorphism. This is a different statement from
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat` of
  `…InternalHom.GlobalDerivedHomRepresentativePair`, which is the elementwise identification at
  `L = Q A`, `M = Q I` — the case of the representing isomorphisms being the identity — and
  carries no conjugation.

## Implementation notes

The proof is the two naturalities of the *OfKFlat* form against the two legs of the comparison,
and nothing else. Writing `A₀ = kFlatModel X L`, `I₀ = kInjectiveModel X M` and

`ρ = (kFlatModelIso X L).hom ≫ eA.inv : Q A₀ ⟶ Q A`,
`ψ = eI.hom ≫ (kInjectiveModelIso X M).inv : Q I ⟶ Q I₀`,

the class `x` is carried by the chosen comparison into the image of its `(eA, eI)`-comparison
under the `ψ`-leg followed by the `ρ`-leg. That single identity of `D(O)` is
`derivedSheafHomObjectsModelIso_comp` below, and it holds for an arbitrary bifunctor: it is the
abstract `AlgebraicGeometry.RingedSite.bifunctorConj`, stated with every category, the bifunctor
and all six objects a **variable**, so that the concrete instance is one `isDefEq` rather than a
sequence of keyed rewrites on terms of this size. Applying
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_target` at `ψ` and then
`derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_source` at `ρ` turns the chosen-model value
into `ρ ≫ (value at `A`, `I`) ≫ ψ`, and the two model isomorphisms then cancel.

Both naturalities are needed in their *arbitrary morphism of `D(O)`* form: neither `ρ` nor `ψ` is
the class of a morphism of complexes. For `ψ` that is free — its target is the class of a
K-injective complex — but for `ρ` it is the calculus-of-fractions argument of
`…InternalHom.DerivedSectionsSourceNaturality`.

No tag is attached. Stacks 08JA is the identification itself, which
`derivedSheafHomGlobalSectionsEquiv` and `derivedSheafHomGlobalSectionsEquivOfKFlat` already
carry; that two constructions of it agree is a claim the source text does not make.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

/-- **Two conjugations of a bifunctor by isomorphisms of both of its arguments agree.** Stated
over an abstract bifunctor with every category and all six objects a variable, so that each
concrete instance is a single definitional-equality check: the terms it is used on below are
derived internal Homs of objects of a derived category, on which a keyed rewrite of this identity
exhausts the elaborator's budget. -/
lemma bifunctorConj {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (F : C₁ᵒᵖ ⥤ C₂ ⥤ C₃) {L A A₀ : C₁} {M I I₀ : C₂}
    (eA : A ≅ L) (eI : I ≅ M) (e₀A : A₀ ≅ L) (e₀I : I₀ ≅ M) :
    ((F.map eA.hom.op).app M ≫ (F.obj (op A)).map eI.inv) ≫
        (F.obj (op A)).map (eI.hom ≫ e₀I.inv) ≫
          (F.map (e₀A.hom ≫ eA.inv).op).app I₀ =
      (F.map e₀A.hom.op).app M ≫ (F.obj (op A₀)).map e₀I.inv := by
  have h₁ : (F.obj (op A)).map eI.inv ≫ (F.obj (op A)).map (eI.hom ≫ e₀I.inv) =
      (F.obj (op A)).map e₀I.inv := by
    rw [← Functor.map_comp]
    simp
  have h₂ : (F.obj (op A)).map e₀I.inv ≫ (F.map (e₀A.hom ≫ eA.inv).op).app I₀ =
      (F.map (e₀A.hom ≫ eA.inv).op).app M ≫ (F.obj (op A₀)).map e₀I.inv :=
    (F.map (e₀A.hom ≫ eA.inv).op).naturality e₀I.inv
  have h₃ : (F.map eA.hom.op).app M ≫ (F.map (e₀A.hom ≫ eA.inv).op).app M =
      (F.map e₀A.hom.op).app M := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
    simp
  rw [Category.assoc, reassoc_of% h₁, h₂, ← Category.assoc, h₃]

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (ComplexShape.up ℤ)] in
/-- **The comparison of the derived internal Hom with one pair of representatives factors through
the comparison with another.** The second comparison is the first followed by the covariant leg of
`eI.hom ≫ e₀I.inv` and the contravariant leg of `e₀A.hom ≫ eA.inv`, the two morphisms of `D(O)`
that compare the pairs. -/
theorem derivedSheafHomObjectsModelIso_comp
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I A₀ I₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M)
    (e₀A : DerivedCategory.Q.obj A₀ ≅ L) (e₀I : DerivedCategory.Q.obj I₀ ≅ M) :
    (derivedSheafHomObjectsModelIso X eA eI).hom ≫
        ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
            (eI.hom ≫ e₀I.inv) ≫
          ((derivedSheafHomBifunctor X).map (e₀A.hom ≫ eA.inv).op).app
            (DerivedCategory.Q.obj I₀) =
      (derivedSheafHomObjectsModelIso X e₀A e₀I).hom :=
  bifunctorConj (derivedSheafHomBifunctor X) eA eI e₀A e₀I

/-- **Stacks 08JA at arbitrary objects is Stacks 08JA at any pair of representatives consisting
of a K-flat complex and a K-injective complex.** The identification of the degree-zero global
hypercohomology of `RSheafHom(L, M)` with `Hom_{D(O)}(L, M)` is computed on a class `x` by
comparing `RSheafHom(L, M)` with `RSheafHom(Q A, Q I)`, applying Stacks 08JA at `A` and `I`, and
conjugating the resulting morphism `Q A ⟶ Q I` by the two representing isomorphisms.

The statement at the chosen models, `derivedSheafHomGlobalSectionsEquiv_apply_assoc`, is the case
`eA = kFlatModelIso X L` and `eI = kInjectiveModelIso X M`, where it holds by `rfl`; for an
arbitrary pair it is the two naturalities of the K-flat form, in the source and in the target,
against the comparison of the two pairs. -/
theorem derivedSheafHomGlobalSectionsEquiv_apply_of_isKFlat
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L M x =
      eA.inv ≫
        derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              ((derivedModuleGlobalSections X).map
                (derivedSheafHomObjectsModelIso X eA eI).hom) x) ≫
          eI.hom := by
  -- The class `x` compared with the given pair, and the two legs comparing the pairs.
  obtain ⟨y, hy⟩ : ∃ y, y = (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((derivedModuleGlobalSections X).map (derivedSheafHomObjectsModelIso X eA eI).hom) x := ⟨_, rfl⟩
  have hx : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map
            ((kFlatModelIso X L).hom ≫ eA.inv).op).app
              (DerivedCategory.Q.obj (kInjectiveModel X M))))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
              (eI.hom ≫ (kInjectiveModelIso X M).inv))) y) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)).hom) x := by
    subst hy
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      derivedSheafHomObjectsModelIso_comp]
  -- Stacks 08JA at the given pair, moved to the chosen K-injective model.
  have htgt := derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_target X hA
    (I' := kInjectiveModel X M) (eI.hom ≫ (kInjectiveModelIso X M).inv) y
  -- and then to the chosen K-flat model.
  have hsrc := derivedSheafHomGlobalSectionsEquivOfKFlat_naturality_source X
    (kInjectiveModel X M) hA (isKFlat_kFlatModel X L)
    ((kFlatModelIso X L).hom ≫ eA.inv)
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
          (eI.hom ≫ (kInjectiveModelIso X M).inv))) y)
  -- `hx` is carried into the K-flat clause by `congrArg` rather than by `rw`: a rewrite whose
  -- pattern is one of these hypercohomology classes exhausts the elaborator's budget, while
  -- congruence and transitivity cost nothing.
  have step := ((congrArg (fun z => derivedSheafHomGlobalSectionsEquivOfKFlat X
    (kFlatModel X L) (kInjectiveModel X M) (isKFlat_kFlatModel X L) z) hx).symm.trans
      hsrc).trans (congrArg (fun g => ((kFlatModelIso X L).hom ≫ eA.inv) ≫ g) htgt)
  refine (derivedSheafHomGlobalSectionsEquiv_apply_assoc X L M x).trans ?_
  subst hy
  rw [step]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Stacks 08JA at arbitrary objects, as an equality of the two bijections.** The additive
bijection of `derivedSheafHomGlobalSectionsEquiv` is the one built from a K-flat complex `A`
representing `L` and a K-injective complex `I` representing `M`, composed with the comparison of
the two derived internal Homs and with conjugation by the representing isomorphisms. -/
theorem derivedSheafHomGlobalSectionsEquiv_eq_of_isKFlat
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M) :
    derivedSheafHomGlobalSectionsEquiv X L M =
      (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
            ((derivedModuleGlobalSections X).mapIso
              (derivedSheafHomObjectsModelIso X eA eI))).addCommGroupIsoToAddEquiv).trans
        ((derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA).trans
          (Linear.homCongr ℤ eA eI).toAddEquiv) :=
  AddEquiv.ext fun x => by
    -- `Linear.homCongr` brackets its conjugation to the left, as in
    -- `derivedSheafHomGlobalSectionsEquiv_apply_assoc`.
    refine (derivedSheafHomGlobalSectionsEquiv_apply_of_isKFlat X hA eA eI x).trans ?_
    rw [← Category.assoc]
    rfl

end AlgebraicGeometry.RingedSite

end
