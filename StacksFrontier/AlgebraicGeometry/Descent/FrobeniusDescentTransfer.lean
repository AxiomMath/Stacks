module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentFibreCondition
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPower
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Moving Frobenius descent of vector bundles along commutative squares

Let `p` be a prime. For a commutative square of schemes in characteristic `p`

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

and a finite locally free `𝒪_X`-module `ℰ`:

* the fibre condition of [Stacks, Tag 0EXH] on `ℰ` (some Frobenius power pullback of `ℰ` is free on
  every reduced fibre `X_{y,red}`) passes to `g'^*ℰ`, because every reduced fibre `X'_{y',red}`
  maps to the reduced fibre `X_{g(y'),red}` over `X`;
* the conclusion of [Stacks, Tag 0EXH] for `ℰ` (some `F^{n,*}ℰ` is a pullback from `Y`) passes to
  `g'^*ℰ`;
* conversely, when `Y' = Y`, `g = 𝟙` and pullback along `g'` is fully faithful on
  `colim_F Vect`, the conclusion for `g'^*ℰ` gives the conclusion for `ℰ`.

## Main results

* `AlgebraicGeometry.Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius.pullback`: the fibre
  condition passes along a commutative square.
* `AlgebraicGeometry.Scheme.Vect.DescendsAfterFrobenius.pullback`: the conclusion passes along a
  commutative square.
* `AlgebraicGeometry.Scheme.Vect.DescendsAfterFrobenius.of_comp`: the conclusion descends along a
  morphism pullback along which is fully faithful on `colim_F Vect`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime]

/-- The `n`-fold Frobenius pullback commutes with pullback of vector bundles:
`g^* F^{n,*} ℰ ≅ F^{n,*} g^* ℰ`. -/
def frobeniusPullbackIterPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ) (E : Y.Vect) :
    (Scheme.Vect.pullback g).obj ((frobeniusPullbackIter Y p hY n).obj E) ≅
      (frobeniusPullbackIter X p hX n).obj ((Scheme.Vect.pullback g).obj E) :=
  endoIterCommIso (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) n E

/-- **A reduced fibre of the top row of a commutative square maps to the reduced fibre of the
bottom row below it**, over the map of total spaces. -/
theorem exists_reductionι_fiberι_comp {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) (y' : Y') :
    ∃ φ : (f'.fiber y').reduction ⟶ (f.fiber (g y')).reduction,
      φ ≫ (f.fiber (g y')).reductionι ≫ f.fiberι (g y') =
        (f'.fiber y').reductionι ≫ f'.fiberι y' ≫ g' := by
  let φ₀ : f'.fiber y' ⟶ f.fiber (g y') :=
    pullback.lift (f'.fiberι y' ≫ g')
      (f'.fiberToSpecResidueField y' ≫ Spec.map (g.residueFieldMap y'))
      (by
        simp only [Category.assoc, w, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
        rw [← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc])
  obtain ⟨φ, hφ, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι
    ((f'.fiber y').reductionι ≫ φ₀)
  refine ⟨(φ : (f'.fiber y').reduction ⟶ (f.fiber (g y')).reduction), ?_⟩
  change φ ≫ (f.fiber (g y')).nilradical.subschemeι ≫ f.fiberι (g y') = _
  have hφ₀ : φ₀ ≫ f.fiberι (g y') = f'.fiberι y' ≫ g' := pullback.lift_fst _ _ _
  rw [← Category.assoc, hφ, Category.assoc, hφ₀]

namespace Scheme.Vect

variable {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- **`IsFreeOnReducedFibresAfterFrobenius` passes along a commutative square**: if some Frobenius
power pullback of `ℰ` is free on every reduced fibre of `f`, then the same holds for `g'^*ℰ` and
`f'`. -/
theorem IsFreeOnReducedFibresAfterFrobenius.pullback (w : g' ≫ f = f' ≫ g)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p) {E : X.Vect}
    (h : IsFreeOnReducedFibresAfterFrobenius f p hX E) :
    IsFreeOnReducedFibresAfterFrobenius f' p hX' ((Scheme.Vect.pullback g').obj E) := by
  intro y'
  obtain ⟨n, r, ⟨e⟩⟩ := h (g y')
  obtain ⟨φ, hφ⟩ := exists_reductionι_fiberι_comp w y'
  refine ⟨n, r, ⟨?_⟩⟩
  let a' := (f'.fiber y').reductionι ≫ f'.fiberι y'
  let a := (f.fiber (g y')).reductionι ≫ f.fiberι (g y')
  have ha : a' ≫ g' = φ ≫ a := by simp only [a', a, Category.assoc, hφ]
  exact (Scheme.Modules.pullback a').mapIso ((ObjectProperty.ι _).mapIso
      (frobeniusPullbackIterPullbackIso g' p hX' hX n E).symm) ≪≫
    (Scheme.Modules.pullbackComp a' g').app _ ≪≫
    (Scheme.Modules.pullbackCongr ha).app _ ≪≫
    ((Scheme.Modules.pullbackComp φ a).app _).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso e ≪≫
    Scheme.Modules.pullbackFreeIso φ _

/-- **`DescendsAfterFrobenius` is invariant under isomorphism of the module.** -/
theorem DescendsAfterFrobenius.of_iso (hX : IsInCharacteristic X p) {E E' : X.Vect} (e : E ≅ E')
    (h : DescendsAfterFrobenius f p hX E) : DescendsAfterFrobenius f p hX E' := by
  obtain ⟨n, G, ⟨e'⟩⟩ := h
  exact ⟨n, G, ⟨(frobeniusPullbackIter X p hX n).mapIso e.symm ≪≫ e'⟩⟩

/-- **`DescendsAfterFrobenius` passes along a commutative square**: if some `F^{n,*}ℰ` is a
pullback along `f`, then some `F^{n,*} g'^*ℰ` is a pullback along `f'`. -/
theorem DescendsAfterFrobenius.pullback (w : g' ≫ f = f' ≫ g)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p) {E : X.Vect}
    (h : DescendsAfterFrobenius f p hX E) :
    DescendsAfterFrobenius f' p hX' ((Scheme.Vect.pullback g').obj E) := by
  obtain ⟨n, G, ⟨e⟩⟩ := h
  refine ⟨n, (Scheme.Vect.pullback g).obj G, ⟨?_⟩⟩
  exact (frobeniusPullbackIterPullbackIso g' p hX' hX n E).symm ≪≫
    (Scheme.Vect.pullback g').mapIso e ≪≫
    (Scheme.Vect.pullbackComp g' f).app G ≪≫ (Scheme.Vect.pullbackCongr w).app G ≪≫
    ((Scheme.Vect.pullbackComp f' g).app G).symm

/-- **Descending `DescendsAfterFrobenius` from a scheme `X'` over `X`** along which
pullback is fully faithful on `colim_F Vect`: if some `F^{n,*} g'^*ℰ` is a pullback along
`g' ≫ f`, then some `F^{m,*} ℰ` is a pullback along `f`. -/
theorem DescendsAfterFrobenius.of_comp (f : X ⟶ Y) (g' : X' ⟶ X)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p) (hY : IsInCharacteristic Y p)
    (hff : (frobeniusColimitVectModelPullback g' p hX' hX).Full ∧
      (frobeniusColimitVectModelPullback g' p hX' hX).Faithful) {E : X.Vect}
    (h : DescendsAfterFrobenius (g' ≫ f) p hX' ((Scheme.Vect.pullback g').obj E)) :
    DescendsAfterFrobenius f p hX E := by
  obtain ⟨hfull, hfaith⟩ := hff
  obtain ⟨n, G, ⟨e⟩⟩ := h
  let e' : (Scheme.Vect.pullback g').obj ((frobeniusPullbackIter X p hX n).obj E) ≅
      (Scheme.Vect.pullback g').obj ((Scheme.Vect.pullback f).obj G) :=
    frobeniusPullbackIterPullbackIso g' p hX' hX n E ≪≫ e ≪≫
      ((Scheme.Vect.pullbackComp g' f).app G).symm
  let ε : (frobeniusColimitVectModelPullback g' p hX' hX).obj
        ⟨(frobeniusPullbackIter X p hX n).obj E, 0 + n⟩ ≅
      (frobeniusColimitVectModelPullback g' p hX' hX).obj
        ⟨(Scheme.Vect.pullback f).obj G, 0 + n⟩ :=
    (frobeniusColimitVectModelStage X' p hX' (0 + n)).mapIso e'
  have hmem : (frobeniusColimitVectModelPullback f p hX hY).essImage
      (⟨E, 0⟩ : frobeniusColimitVectModel X p hX) :=
    ⟨⟨G, 0 + n⟩, ⟨(Functor.preimageIso _ ε).symm ≪≫
      EndoColim.objShiftIso (frobeniusPullback X p hX) 0 n E⟩⟩
  exact (mem_essImage_frobeniusColimitVectModelPullback_iff f p hX hY _).mp hmem

end Scheme.Vect

end AlgebraicGeometry

end
