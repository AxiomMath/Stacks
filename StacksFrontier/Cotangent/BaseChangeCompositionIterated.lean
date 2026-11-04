module

public import StacksFrontier.Cotangent.BaseChangeCompositionCounit
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Composing the adjoint functoriality maps along a tower of two extensions of scalars

`CommAlgCat.squareCotangentComplexMap_comp_counit` of
`StacksFrontier/Cotangent/BaseChangeCompositionCounit.lean` composes the adjoint shape
`L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of the functoriality map of [Stacks, Tag 08PN] with the `B'`-linear
map of a second square, the extension of scalars being along the *first* square's map throughout.
This file records the other composition law, the one where each square contributes its own
extension of scalars: the composite

`L_{B/A} ⊗_B B' ⊗_{B'} B'' ⟶ L_{B'/A'} ⊗_{B'} B'' ⟶ L_{B''/A''}`

is the adjoint map of the composite square, read through the cancellation of the two base changes
`(L ⊗_B B') ⊗_{B'} B'' = L ⊗_B B''`.

Everything is proved for an arbitrary pair of composable ring maps and arbitrary complexes; the
cotangent complexes enter only in the last statement, where the general law is instantiated at
the functoriality map of [Stacks, Tag 08PN].

## Main definitions

* `ModuleCat.extendScalarsCompComplexIso`: Mathlib's `ModuleCat.extendScalarsComp`, the
  cancellation `T ⊗_S (S ⊗_R M) = T ⊗_R M` of two base changes, applied degreewise to complexes.
* `ModuleCat.restrictScalarsCompComplexIso`: Mathlib's `ModuleCat.restrictScalarsComp`, which is
  the identity on underlying modules, applied degreewise to complexes.

## Main results

* `ModuleCat.restrictScalarsComp_hom_app_eq_id`: restricting scalars along a composite **is**
  restricting them twice; the comparison is an identity morphism.
* `ModuleCat.extendRestrictScalarsAdj_counit_comp₀` and
  `ModuleCat.extendRestrictScalarsAdj_counit_comp`: **the counits of the two extensions compose
  to the counit of the composite**, through the cancellation isomorphism. On the generator
  `1 ⊗ x` of `T ⊗_R M` both sides are `x`. The second form writes out the comparison of the two
  restrictions of scalars, so that the two spellings do not meet.
* `ModuleCat.extendRestrictScalarsAdjCounitComplex_comp`: the same for complexes.
* `ModuleCat.extendScalarsAdjoint_comp`: **the composition law for adjoint maps of complexes.**
  If `ψ : K ⟶ M` over the composite ring map is `φ : K ⟶ L` followed by `φ' : L ⟶ M`, then the
  composite of the two adjoint maps is the adjoint map of `ψ`, through the cancellation
  isomorphism.
* `CommAlgCat.squareCotangentComplexMap_counit_comp_iterated` and
  `CommAlgCat.squareCotangentComplexMap_counit_comp_iterated'`: the law at the functoriality map
  of [Stacks, Tag 08PN] for a pair of composable squares, with the cancellation isomorphism on
  either side of the equation.

## Implementation notes

The two spellings `ModuleCat.restrictScalars (m'.comp m)` and
`ModuleCat.restrictScalars m ⋙ ModuleCat.restrictScalars m'` of the restriction of scalars along
a composite are definitionally equal — restriction of scalars does not change the underlying
module — but only up to unfolding `Module.compHom`, which `rw` cannot see and which is expensive
to force inside a complex of modules: a goal in which the two spellings meet is reported as not
type-correct at the `implicit` transparency level, and asking the elaborator to identify them
degreewise inside a cochain complex does not terminate in reasonable time.

So the two spellings are kept apart. Wherever they would meet, Mathlib's comparison
`ModuleCat.restrictScalarsComp` is written out, and the single place where they are identified is
`ModuleCat.restrictScalarsComp_hom_app_eq_id`, a statement about one module. Everything above it
is ordinary category theory on wall-free statements, which `rw` handles.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (m : R →+* S) (m' : S →+* T)

/-- **Restricting scalars along a composite is restricting them twice, on the nose.** Mathlib's
comparison `ModuleCat.restrictScalarsComp` is the identity map of the underlying module. This is
the one place in this file where the two spellings of the restriction of scalars along a
composite are identified. -/
theorem restrictScalarsComp_hom_app_eq_id (M : ModuleCat.{u} T) :
    (restrictScalarsComp m m').hom.app M = 𝟙 ((restrictScalars (m'.comp m)).obj M) :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- **The counits of two successive extensions of scalars compose to the counit of the
composite.** For a `T`-module `M` the two maps `T ⊗_R M ⟶ M` — on one side the counit itself, on
the other the cancellation `T ⊗_R M = T ⊗_S (S ⊗_R M)` followed by the counit `S ⊗_R M ⟶ M`
extended along `S → T` and then by the counit `T ⊗_S M ⟶ M` — agree. Both send the generator
`1 ⊗ x` to `x`. -/
theorem extendRestrictScalarsAdj_counit_comp₀ (M : ModuleCat.{u} T) :
    (extendRestrictScalarsAdj (m'.comp m)).counit.app M =
      (extendScalarsComp m m').hom.app ((restrictScalars (m'.comp m)).obj M) ≫
        (extendScalars m').map
            ((extendRestrictScalarsAdj m).counit.app ((restrictScalars m').obj M)) ≫
          (extendRestrictScalarsAdj m').counit.app M := by
  refine ModuleCat.ExtendScalars.hom_ext fun x => ?_
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun z => (extendRestrictScalarsAdj m').counit.app M
      ((extendScalars m').map
        ((extendRestrictScalarsAdj m).counit.app ((restrictScalars m').obj M)) z))
    (extendScalarsComp_hom_app_one_tmul m m' ((restrictScalars (m'.comp m)).obj M) x)).symm
  refine Eq.trans ?_ (congrArg ((extendRestrictScalarsAdj m').counit.app M)
    (ExtendScalars.map_tmul m' ((extendRestrictScalarsAdj m).counit.app
      ((restrictScalars m').obj M)) 1 _)).symm
  refine Eq.trans ?_ (extendRestrictScalarsAdj_counit_app_apply_one_tmul m' M _).symm
  exact (extendRestrictScalarsAdj_counit_app_apply_one_tmul (m'.comp m) M x).trans
    (extendRestrictScalarsAdj_counit_app_apply_one_tmul m ((restrictScalars m').obj M) x).symm

/-- **The counits of two successive extensions of scalars compose to the counit of the
composite**, with the comparison of the two restrictions of scalars written out so that the two
spellings never meet. This is `ModuleCat.extendRestrictScalarsAdj_counit_comp₀` with an identity
morphism inserted. -/
theorem extendRestrictScalarsAdj_counit_comp (M : ModuleCat.{u} T) :
    (extendRestrictScalarsAdj (m'.comp m)).counit.app M =
      (extendScalarsComp m m').hom.app ((restrictScalars (m'.comp m)).obj M) ≫
        (extendScalars m').map
            ((extendScalars m).map ((restrictScalarsComp m m').hom.app M) ≫
              (extendRestrictScalarsAdj m).counit.app ((restrictScalars m').obj M)) ≫
          (extendRestrictScalarsAdj m').counit.app M := by
  have h : (extendScalars m).map ((restrictScalarsComp m m').hom.app M) ≫
        (extendRestrictScalarsAdj m).counit.app ((restrictScalars m').obj M) =
      (extendRestrictScalarsAdj m).counit.app ((restrictScalars m').obj M) :=
    (congrArg (fun z => z ≫ (extendRestrictScalarsAdj m).counit.app
          ((restrictScalars m').obj M))
        ((congrArg (extendScalars m).map (restrictScalarsComp_hom_app_eq_id m m' M)).trans
          ((extendScalars m).map_id _))).trans (Category.id_comp _)
  exact (extendRestrictScalarsAdj_counit_comp₀ m m' M).trans
    (congrArg (fun z => (extendScalarsComp m m').hom.app
        ((restrictScalars (m'.comp m)).obj M) ≫ (extendScalars m').map z ≫
          (extendRestrictScalarsAdj m').counit.app M) h.symm)

variable {ι : Type*} (c : ComplexShape ι)

/-- **The cancellation of two base changes, on complexes.** Extending the scalars of a complex of
`R`-modules along `m : R → S` and then along `m' : S → T` is extending them along `m' ∘ m`; this
is `ModuleCat.extendScalarsComp` applied degreewise. -/
noncomputable def extendScalarsCompComplexIso :
    (extendScalars m).mapHomologicalComplex c ⋙ (extendScalars m').mapHomologicalComplex c ≅
      (extendScalars (m'.comp m)).mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso (extendScalarsComp m m').symm c

/-- In degree `n`, the inverse of `extendScalarsCompComplexIso` at a complex `K` is the component
at `K.X n` of the forward map of `ModuleCat.extendScalarsComp`. -/
@[simp]
theorem extendScalarsCompComplexIso_inv_app_f
    (K : HomologicalComplex (ModuleCat.{u} R) c) (n : ι) :
    ((extendScalarsCompComplexIso m m' c).inv.app K).f n =
      (extendScalarsComp m m').hom.app (K.X n) :=
  rfl

/-- **Restricting scalars along a composite, on complexes.** This is
`ModuleCat.restrictScalarsComp` applied degreewise; every component is the identity map of the
underlying module. -/
noncomputable def restrictScalarsCompComplexIso :
    (restrictScalars m').mapHomologicalComplex c ⋙ (restrictScalars m).mapHomologicalComplex c ≅
      (restrictScalars (m'.comp m)).mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso (restrictScalarsComp m m').symm c

/-- In degree `n`, the inverse of `restrictScalarsCompComplexIso` at a complex `K` is the
component at `K.X n` of the forward map of `ModuleCat.restrictScalarsComp`. -/
@[simp]
theorem restrictScalarsCompComplexIso_inv_app_f
    (K : HomologicalComplex (ModuleCat.{u} T) c) (n : ι) :
    ((restrictScalarsCompComplexIso m m' c).inv.app K).f n =
      (restrictScalarsComp m m').hom.app (K.X n) :=
  rfl

/-- **The counits of two successive extensions of scalars compose to the counit of the
composite**, for complexes: `ModuleCat.extendRestrictScalarsAdj_counit_comp` in every degree. -/
theorem extendRestrictScalarsAdjCounitComplex_comp
    (K : HomologicalComplex (ModuleCat.{u} T) c) :
    extendRestrictScalarsAdjCounitComplex (m'.comp m) c K =
      (extendScalarsCompComplexIso m m' c).inv.app
            (((restrictScalars (m'.comp m)).mapHomologicalComplex c).obj K) ≫
        ((extendScalars m').mapHomologicalComplex c).map
            (((extendScalars m).mapHomologicalComplex c).map
                ((restrictScalarsCompComplexIso m m' c).inv.app K) ≫
              extendRestrictScalarsAdjCounitComplex m c
                (((restrictScalars m').mapHomologicalComplex c).obj K)) ≫
          extendRestrictScalarsAdjCounitComplex m' c K :=
  HomologicalComplex.hom_ext _ _ fun n =>
    extendRestrictScalarsAdj_counit_comp m m' (K.X n)

/-- **The composition law for the adjoint shape of a functoriality map.** Let `φ : K ⟶ L` be a
map of complexes over `m : R → S`, let `φ' : L ⟶ M` be one over `m' : S → T`, and let `ψ` be
their composite, read over `m' ∘ m`. Then the adjoint map `T ⊗_R K ⟶ M` of `ψ` is, through the
cancellation `T ⊗_R K = T ⊗_S (S ⊗_R K)`, the adjoint map `S ⊗_R K ⟶ L` of `φ` extended along
`S → T` followed by the adjoint map `T ⊗_S L ⟶ M` of `φ'`. -/
theorem extendScalarsAdjoint_comp {K : HomologicalComplex (ModuleCat.{u} R) c}
    {L : HomologicalComplex (ModuleCat.{u} S) c} {M : HomologicalComplex (ModuleCat.{u} T) c}
    (φ : K ⟶ ((restrictScalars m).mapHomologicalComplex c).obj L)
    (φ' : L ⟶ ((restrictScalars m').mapHomologicalComplex c).obj M)
    (ψ : K ⟶ ((restrictScalars (m'.comp m)).mapHomologicalComplex c).obj M)
    (hψ : ψ ≫ (restrictScalarsCompComplexIso m m' c).inv.app M =
      φ ≫ ((restrictScalars m).mapHomologicalComplex c).map φ') :
    (extendScalarsCompComplexIso m m' c).inv.app K ≫
          ((extendScalars m').mapHomologicalComplex c).map
            (((extendScalars m).mapHomologicalComplex c).map φ ≫
              extendRestrictScalarsAdjCounitComplex m c L) ≫
        (((extendScalars m').mapHomologicalComplex c).map φ' ≫
          extendRestrictScalarsAdjCounitComplex m' c M) =
      ((extendScalars (m'.comp m)).mapHomologicalComplex c).map ψ ≫
        extendRestrictScalarsAdjCounitComplex (m'.comp m) c M := by
  have key₀ : ((extendScalars m).mapHomologicalComplex c).map ψ ≫
        (((extendScalars m).mapHomologicalComplex c).map
            ((restrictScalarsCompComplexIso m m' c).inv.app M) ≫
          extendRestrictScalarsAdjCounitComplex m c
            (((restrictScalars m').mapHomologicalComplex c).obj M)) =
      (((extendScalars m).mapHomologicalComplex c).map φ ≫
        extendRestrictScalarsAdjCounitComplex m c L) ≫ φ' := by
    rw [← Category.assoc, ← Functor.map_comp, hψ, Functor.map_comp, Category.assoc,
      extendRestrictScalarsAdjCounitComplex_naturality m c φ', ← Category.assoc]
  rw [extendRestrictScalarsAdjCounitComplex_comp m m' c M,
    (extendScalarsCompComplexIso m m' c).inv.naturality_assoc, Functor.comp_map]
  refine congrArg (fun z => (extendScalarsCompComplexIso m m' c).inv.app K ≫ z) ?_
  rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp, key₀]

end ModuleCat

namespace CommAlgCat

variable {A A' A'' : Type u} [CommRing A] [CommRing A'] [CommRing A'']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'} {B'' : CommAlgCat.{u} A''}

/-- **The composition law for the adjoint shape of the functoriality map of [Stacks, Tag 08PN],
with each square contributing its own extension of scalars.** For composable squares `sq` and
`sq'`, the adjoint map `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of `sq` extended along `B' → B''` followed by
the adjoint map `L_{B'/A'} ⊗_{B'} B'' ⟶ L_{B''/A''}` of `sq'` is the adjoint map
`L_{B/A} ⊗_B B'' ⟶ L_{B''/A''}` of the composite square, read through the cancellation
`(L_{B/A} ⊗_B B') ⊗_{B'} B'' = L_{B/A} ⊗_B B''`.

This is `ModuleCat.extendScalarsAdjoint_comp` at the functoriality map, the hypothesis `hψ` being
the composition law `CommAlgCat.squareCotangentComplexMap_comp'` together with
`ModuleCat.restrictScalarsComp_hom_app_eq_id`. -/
theorem squareCotangentComplexMap_counit_comp_iterated (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'') :
    (ModuleCat.extendScalarsCompComplexIso sq.map sq'.map (ComplexShape.up ℤ)).inv.app
            (cotangentComplex.{u, u} A B) ≫
          ((ModuleCat.extendScalars sq'.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
                (squareCotangentComplexMap.{u, u, u} sq) ≫
              ModuleCat.extendRestrictScalarsAdjCounitComplex sq.map (ComplexShape.up ℤ)
                (cotangentComplex.{u, u} A' B')) ≫
        (((ModuleCat.extendScalars sq'.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (squareCotangentComplexMap.{u, u, u} sq') ≫
            ModuleCat.extendRestrictScalarsAdjCounitComplex sq'.map (ComplexShape.up ℤ)
              (cotangentComplex.{u, u} A'' B'')) =
      ((ModuleCat.extendScalars (sq.comp sq').map).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (squareCotangentComplexMap.{u, u, u} (sq.comp sq')) ≫
        ModuleCat.extendRestrictScalarsAdjCounitComplex (sq.comp sq').map (ComplexShape.up ℤ)
          (cotangentComplex.{u, u} A'' B'') := by
  refine ModuleCat.extendScalarsAdjoint_comp sq.map sq'.map (ComplexShape.up ℤ)
    (squareCotangentComplexMap.{u, u, u} sq) (squareCotangentComplexMap.{u, u, u} sq')
    (squareCotangentComplexMap.{u, u, u} (sq.comp sq')) ?_
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine Eq.trans (HomologicalComplex.comp_f _ _ n) ?_
  refine Eq.trans ?_ (HomologicalComplex.comp_f _ _ n).symm
  refine Eq.trans (congrArg
    (fun z => (squareCotangentComplexMap.{u, u, u} (sq.comp sq')).f n ≫ z)
    (ModuleCat.restrictScalarsComp_hom_app_eq_id sq.map sq'.map
      ((cotangentComplex.{u, u} A'' B'').X n))) ?_
  exact (Category.comp_id _).trans
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
      (squareCotangentComplexMap_comp'.{u} sq sq'))


/-- **The composition law for the adjoint shape, with the cancellation isomorphism moved to the
other side.** This is `CommAlgCat.squareCotangentComplexMap_counit_comp_iterated` composed with
the cancellation isomorphism, which is the form the descent of the fundamental triangle
consumes. -/
theorem squareCotangentComplexMap_counit_comp_iterated' (sq : AlgebraSquare.{u, u, u} A A' B B')
    (sq' : AlgebraSquare.{u, u, u} A' A'' B' B'') :
    ((ModuleCat.extendScalars sq'.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((ModuleCat.extendScalars sq.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (squareCotangentComplexMap.{u, u, u} sq) ≫
            ModuleCat.extendRestrictScalarsAdjCounitComplex sq.map (ComplexShape.up ℤ)
              (cotangentComplex.{u, u} A' B')) ≫
        (((ModuleCat.extendScalars sq'.map).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (squareCotangentComplexMap.{u, u, u} sq') ≫
            ModuleCat.extendRestrictScalarsAdjCounitComplex sq'.map (ComplexShape.up ℤ)
              (cotangentComplex.{u, u} A'' B'')) =
      (ModuleCat.extendScalarsCompComplexIso sq.map sq'.map (ComplexShape.up ℤ)).hom.app
            (cotangentComplex.{u, u} A B) ≫
          (((ModuleCat.extendScalars (sq.comp sq').map).mapHomologicalComplex
                (ComplexShape.up ℤ)).map (squareCotangentComplexMap.{u, u, u} (sq.comp sq')) ≫
            ModuleCat.extendRestrictScalarsAdjCounitComplex (sq.comp sq').map
              (ComplexShape.up ℤ) (cotangentComplex.{u, u} A'' B'')) :=
  ((congrArg (fun z => (ModuleCat.extendScalarsCompComplexIso sq.map sq'.map
        (ComplexShape.up ℤ)).hom.app (cotangentComplex.{u, u} A B) ≫ z)
      (squareCotangentComplexMap_counit_comp_iterated.{u} sq sq')).symm.trans
    (Iso.hom_inv_id_app_assoc
      (ModuleCat.extendScalarsCompComplexIso sq.map sq'.map (ComplexShape.up ℤ))
      (cotangentComplex.{u, u} A B) _)).symm

end CommAlgCat

end
