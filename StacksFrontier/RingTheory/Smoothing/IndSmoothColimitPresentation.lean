module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import StacksFrontier.RingTheory.Smoothing.IndSmooth

/-!
# A filtered colimit of smooth algebras, presented over a finitely presented subalgebra

Let `R → Λ` be ind-smooth, that is, let `Λ` be a filtered colimit of smooth `R`-algebras
(`Stacks.Smoothing.IndSmooth`, the conclusion of Popescu's theorem `07GC`), and let `C` be an
`R`-algebra of finite presentation equipped with an `R`-algebra map `C → Λ`. This file produces a
filtered colimit presentation of `Λ` *as a `C`-algebra* whose stages are smooth over `R`, and
shows that tensoring such a presentation with a `C`-algebra `B` presents `B ⊗[C] Λ` as a filtered
colimit of the `B ⊗[C] R'`.

These are the two inputs that the proof of Stacks `0CAW` needs between Popescu's theorem and item
(9) of Stacks `00U2` (`Algebra.Etale.exists_etale_stage_of_isColimit`). In the notation of `0CAW`,
`Λ = R^∧` is the completion of a local `G`-ring, `σ : C → R^∧` is the given map and `B` is a
`C`-algebra; item (9) *consumes* a colimit presentation of `B ⊗_{C, σ} R^∧` and does not produce
one.

## Main results

* `CategoryTheory.Limits.ColimitPresentation.tensorProd`: tensoring preserves colimit
  presentations. If `X = colim Xⱼ` in `R`-algebras then `S ⊗[R] X = colim (S ⊗[R] Xⱼ)` in
  `S`-algebras.
* `Stacks.Smoothing.exists_colimitPresentation_smooth_of_indSmooth`: an ind-smooth `R`-algebra
  `Λ` is, as a `C`-algebra, a filtered colimit of `C`-algebras that are smooth over `R`, whenever
  `C` is of finite presentation over `R`.
* `Stacks.Smoothing.exists_colimitPresentation_tensorProduct_of_indSmooth`: the two combined, in
  the shape item (9) of `00U2` consumes: a filtered colimit presentation of `B ⊗[C] Λ` in
  `CommRingCat` whose stages are the `B ⊗[C] R'` for `R'` smooth over `R`.

## Implementation notes

`IndSmooth R Λ` is `ObjectProperty.ind` of smoothness in `Under (CommRingCat.of R)`, so it already
carries a small filtered index category `J`, a diagram of smooth `R`-algebras and a colimiting
cocone with vertex `Λ`. What it does *not* carry is any relation to `C`: the maps `R' → Λ` are
`R`-algebra maps, not `C`-algebra maps, and there is no reason for a single `R'` to receive `C`.
Producing the presentation over `C` is therefore not a repackaging of `07GC` but needs two further
steps, which are the content of
`Stacks.Smoothing.exists_colimitPresentation_smooth_of_indSmooth`:

* `C` is of finite presentation over `R`, hence a finitely presentable object of
  `Under (CommRingCat.of R)` (Lemma `00QO`, `CommRingCat.isFinitelyPresentable_hom`), so the map
  `C → Λ` factors through one stage `R'_{j₀}` as an `R`-algebra map
  (`MorphismProperty.exists_hom_of_isFinitelyPresentable`);
* the index category is then replaced by the under category `Under j₀`, which is filtered and for
  which `Under.forget j₀` is final, so the colimit is unchanged
  (`Functor.Final.isColimitWhiskerEquiv`). Every stage after `j₀` receives `C`, compatibly, and
  `Under.lift` assembles those maps into a diagram in `Under (CommRingCat.of C)`.

The index category produced is `Under j₀` for the filtered `J` of the given presentation. It is
filtered but in general not a directed poset, which is why item (9) of `00U2` is proved for an
arbitrary `IsFiltered` index category.

The stages are objects of `Under (CommRingCat.of C)`, so their `R`-algebra structure map is the
composite `R → C → R'`; smoothness over `R` is stated as `RingHom.Smooth` of that composite rather
than as `Algebra.Smooth R R'`, which would need an `Algebra R R'` instance that the diagram does
not provide. The cocone legs are morphisms of `Under (CommRingCat.of C)`, which is exactly the
requirement that the smooth stages factor the given map `C → Λ`.

Tensoring is Mathlib's `CommRingCat.tensorProd R S : Under R ⥤ Under S`, whose value at `A` is
literally `S ⊗[R] A`. That it preserves colimits is the natural isomorphism
`CommRingCat.tensorProdIsoPushout` with `Under.pushout`, which is a left adjoint
(`Under.pushoutIsLeftAdjoint`); no filteredness is needed for this half.

An object `A` of `Under R` carries the `Algebra R A` structure `RingHom.toAlgebra A.hom.hom`,
which is not the same term as a pre-existing `Algebra R A` — the difficulty recorded in
`StacksFrontier.Algebra.Category.Ring.UnderPushoutTensor`. It is why
`Stacks.Smoothing.exists_colimitPresentation_smooth_of_indSmooth`, where no tensor product occurs,
is free to take `[Algebra C Λ] [IsScalarTower R C Λ]` as given, while
`Stacks.Smoothing.exists_colimitPresentation_tensorProduct_of_indSmooth` takes the `C`-algebra
structure of `Λ` as an algebra map `σ` and installs `σ.toRingHom.toAlgebra`: that term *is* the
one `Under` manufactures, so the tensor product in its conclusion is the tensor product the
base change functor forms, with no bridge isomorphism between two spellings of `B ⊗[C] Λ`. In the
intended application `σ : C → R^∧` is exactly how the `C`-algebra structure arises.

The final descent from `Under (CommRingCat.of B)` to `CommRingCat` uses that `Under.forget`
preserves filtered colimits. The hypothesis `PreservesColimit F (forget CommRingCat)` of item (9)
of `00U2` is then automatic for the resulting diagram, by
`CommRingCat.FilteredColimits.forget_preservesFilteredColimits`.

## References

* [StacksProject 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [StacksProject 00QO](https://stacks.math.columbia.edu/tag/00QO)
* [StacksProject 00U2](https://stacks.math.columbia.edu/tag/00U2)
* [StacksProject 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

open scoped TensorProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t w u

namespace CommRingCat

/-- **Base change preserves colimits.** The functor `A ↦ S ⊗[R] A` from `R`-algebras to
`S`-algebras preserves colimits, being naturally isomorphic to the pushout functor along
`R → S`, which is a left adjoint. -/
noncomputable instance preservesColimitsOfShape_tensorProd {R S : CommRingCat.{u}} [Algebra R S]
    {J : Type w} [Category.{t} J] : PreservesColimitsOfShape J (tensorProd R S) :=
  preservesColimitsOfShape_of_natIso (tensorProdIsoPushout R S).symm

end CommRingCat

namespace CategoryTheory.Limits.ColimitPresentation

/-- **Tensoring preserves colimit presentations.** If `X` is the colimit of a diagram `Xⱼ` of
`R`-algebras, then `S ⊗[R] X` is the colimit of the diagram `S ⊗[R] Xⱼ` of `S`-algebras, via the
base changed cocone. In particular this holds for filtered diagrams, which is the case used to
turn a presentation of `Λ` as a filtered colimit of smooth algebras into one of `B ⊗[C] Λ`. -/
noncomputable def tensorProd {R S : CommRingCat.{u}} [Algebra R S] {J : Type w} [Category.{t} J]
    {X : Under R} (pres : ColimitPresentation J X) :
    ColimitPresentation J (CommRingCat.mkUnder S (S ⊗[R] X)) :=
  pres.map (CommRingCat.tensorProd R S)

/-- The diagram of `pres.tensorProd` is the diagram of `pres` followed by the base change functor
`A ↦ S ⊗[R] A`. -/
@[simp]
lemma tensorProd_diag {R S : CommRingCat.{u}} [Algebra R S] {J : Type w} [Category.{t} J]
    {X : Under R} (pres : ColimitPresentation J X) :
    pres.tensorProd.diag = pres.diag ⋙ CommRingCat.tensorProd R S :=
  rfl

end CategoryTheory.Limits.ColimitPresentation

namespace Stacks.Smoothing

/-- **An ind-smooth algebra is a filtered colimit of smooth algebras over a finitely presented
subalgebra.** Let `Λ` be a filtered colimit of smooth `R`-algebras and let `C` be an `R`-algebra
of finite presentation with an `R`-algebra map to `Λ`. Then `Λ`, viewed as a `C`-algebra, is a
filtered colimit of `C`-algebras `R'` that are smooth over `R`; the maps `C → R' → Λ` compose to
the given map, since the diagram and the cocone live in `Under (CommRingCat.of C)`.

This is the input that Stacks `0CAW` draws from Popescu's theorem `07GC` together with
Lemma `00QO`: there `Λ = R^∧` and the conclusion is the factorization `C → R' → R^∧` with
`R → R'` smooth, made functorial in `R'` so that it is a colimit presentation and not merely one
factorization. -/
theorem exists_colimitPresentation_smooth_of_indSmooth (R C Λ : Type u) [CommRing R] [CommRing C]
    [CommRing Λ] [Algebra R C] [Algebra R Λ] [Algebra C Λ] [IsScalarTower R C Λ]
    [Algebra.FinitePresentation R C] (h : IndSmooth R Λ) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J (CommRingCat.mkUnder (CommRingCat.of C) Λ)),
      ∀ j, ((pres.diag.obj j).hom.hom.comp (algebraMap R C)).Smooth := by
  obtain ⟨J, _, _, pres, hsmooth⟩ := h
  -- the diagram and the colimiting cocone of underlying rings
  let D : J ⥤ CommRingCat.{u} := pres.diag ⋙ Under.forget (CommRingCat.of R)
  let cD : Cocone D := (Under.forget (CommRingCat.of R)).mapCocone pres.cocone
  have hcD : IsColimit cD := isColimitOfPreserves _ pres.isColimit
  -- the structure maps `R → R'ⱼ`, natural in `j`
  let s : (Functor.const J).obj (CommRingCat.of R) ⟶ D :=
    { app := fun j ↦ (pres.diag.obj j).hom
      naturality := fun j k u ↦ by simp [D] }
  -- `C` is of finite presentation over `R`, so `C → Λ` factors through a stage
  have hfpC : MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u}
      (CommRingCat.ofHom (algebraMap R C)) :=
    CommRingCat.isFinitelyPresentable_hom _
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  obtain ⟨j₀, q, hq₁, hq₂⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable hcD hfpC s
    (CommRingCat.ofHom (algebraMap C Λ)) (fun j ↦ by
      ext r
      exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Under.w (pres.ι.app j))) r).trans
        (IsScalarTower.algebraMap_apply R C Λ r))
  -- restrict the index category to the stages receiving `j₀`
  have : Nonempty (Under j₀) := ⟨Under.mk (𝟙 j₀)⟩
  let c' : Cocone (Under.forget j₀ ⋙ D) := cD.whisker (Under.forget j₀)
  -- every such stage receives `C`, compatibly
  let t : (Functor.const (Under j₀)).obj (CommRingCat.of C) ⟶ Under.forget j₀ ⋙ D :=
    { app := fun k ↦ q ≫ D.map k.hom
      naturality := fun k l a ↦ by
        change 𝟙 _ ≫ q ≫ D.map l.hom = (q ≫ D.map k.hom) ≫ D.map a.right
        rw [Category.id_comp, Category.assoc, ← Functor.map_comp, Under.w a] }
  have hp : ∀ k : Under j₀,
      t.app k ≫ c'.ι.app k = CommRingCat.ofHom (algebraMap C Λ) :=
    fun k ↦ (Category.assoc q (D.map k.hom) (cD.ι.app k.right)).trans
      ((congrArg (fun g ↦ q ≫ g) (cD.w k.hom)).trans hq₂)
  have h1 : ∀ k : Under j₀, (CommRingCat.ofHom (algebraMap R C) ≫ t.app k :
      CommRingCat.of R ⟶ (pres.diag.obj k.right).right) = (pres.diag.obj k.right).hom :=
    fun k ↦ (Category.assoc (CommRingCat.ofHom (algebraMap R C)) q (D.map k.hom)).symm.trans
      ((congrArg (fun g ↦ g ≫ D.map k.hom) hq₁).trans (Under.w (pres.diag.map k.hom)))
  refine ⟨Under j₀, inferInstance, inferInstance,
    { diag := Under.lift (Under.forget j₀ ⋙ D) t
      ι := (Under.liftCocone (Under.forget j₀ ⋙ D) t c'
        (CommRingCat.ofHom (algebraMap C Λ)) hp).ι
      isColimit := Under.isColimitLiftCocone (Under.forget j₀ ⋙ D) t c' _ hp
        ((Functor.Final.isColimitWhiskerEquiv (Under.forget j₀) cD).symm hcD) },
    fun k ↦ ?_⟩
  have h : (pres.diag.obj k.right).hom.hom.Smooth := hsmooth k.right
  rwa [← h1 k] at h

/-- **An ind-smooth algebra base changed along a finitely presented subalgebra is a filtered
colimit.** Let `Λ` be a filtered colimit of smooth `R`-algebras, let `C` be an `R`-algebra of
finite presentation with an `R`-algebra map `σ : C → Λ`, and let `B` be a `C`-algebra. Then
`B ⊗[C] Λ` is a filtered colimit of the `B ⊗[C] R'`, for `R'` running through `C`-algebras smooth
over `R` that factor `σ`.

This is the combination of `Stacks.Smoothing.exists_colimitPresentation_smooth_of_indSmooth` and
`CategoryTheory.Limits.ColimitPresentation.tensorProd` in the shape item (9) of Stacks `00U2`
consumes: `pres.diag`, `pres.cocone` and `pres.isColimit` are its diagram, cocone and colimit
witness, and its remaining hypothesis `PreservesColimit pres.diag (forget CommRingCat)` is
automatic from `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`. In the notation of
Stacks `0CAW`, `Λ = R^∧` and this is the presentation of `B ⊗_{C, σ} R^∧` as the filtered colimit
of the `B ⊗_C R'`. -/
theorem exists_colimitPresentation_tensorProduct_of_indSmooth (R C Λ : Type u) [CommRing R]
    [CommRing C] [CommRing Λ] [Algebra R C] [Algebra R Λ] [Algebra.FinitePresentation R C]
    (σ : C →ₐ[R] Λ) (B : Type u) [CommRing B] [Algebra C B] (h : IndSmooth R Λ) :
    letI : Algebra C Λ := σ.toRingHom.toAlgebra
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (D : J ⥤ Under (CommRingCat.of C)),
      (∀ j, ((D.obj j).hom.hom.comp (algebraMap R C)).Smooth) ∧
        ∃ pres : ColimitPresentation J (CommRingCat.of (B ⊗[C] Λ)),
          pres.diag =
            (D ⋙ CommRingCat.tensorProd (CommRingCat.of C) (CommRingCat.of B)) ⋙
              Under.forget (CommRingCat.of B) := by
  let : Algebra C Λ := σ.toRingHom.toAlgebra
  have : IsScalarTower R C Λ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (σ.commutes r).symm
  obtain ⟨J, instJ, instFiltered, pres, hsmooth⟩ :=
    exists_colimitPresentation_smooth_of_indSmooth R C Λ h
  exact ⟨J, instJ, instFiltered, pres.diag, hsmooth,
    pres.tensorProd.map (Under.forget (CommRingCat.of B)), rfl⟩

end Stacks.Smoothing

end
