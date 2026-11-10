module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullbackFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitComparisonCospan
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMapComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectEssSurj
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleProperCoverDescent

/-!
# The essential image of `colim_F Vect(Y) ⥤ colim_F Vect(X)` descends along proper covers

Let `p` be a prime, `Y` a quasi-compact quasi-separated scheme in characteristic `p`, and
`f : X ⟶ Y` proper and surjective with geometrically connected fibres. For a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` proper, surjective and locally of finite presentation (so that `{g}` is an h covering,
Stacks 0ETW), **an object of `colim_F Vect(X)` whose pullback to `X'` lies in the essential image
of `colim_F Vect(Y') ⥤ colim_F Vect(X')` lies in the essential image of
`colim_F Vect(Y) ⥤ colim_F Vect(X)`**
(`AlgebraicGeometry.mem_essImage_of_mem_essImage_baseChange`).

This is the reduction of the proof of Stacks Tag 0EXH: "by the fully faithfulness already proven
and because of Proposition 0EXE it suffices to construct a descent of `ℰ` after replacing `Y` by
the members of an h covering and `X` by the corresponding base change". The descent itself is
`AlgebraicGeometry.exists_frobeniusColimitVectorBundlesPullback_obj_iso_of_proper_cover`, stated
for finite locally free `colim_F 𝒪`-modules; this file carries it to the model category
`colim_F Vect` through the comparison functor of Stacks Tag 0EXB, and supplies its full
faithfulness hypothesis from part (1) of Stacks Tag 0EXH,
`AlgebraicGeometry.frobeniusColimitVectModelPullback_full_faithful`.

## Main results

* `CategoryTheory.EndoColim.mapIsoMapOfComm`: the two constructions of the functor on colimit
  categories induced by a functor commuting with the endofunctors agree.
* `AlgebraicGeometry.colimVectPullbackIsoFrobeniusColimitVectModelPullback`.
* `AlgebraicGeometry.fullyFaithful_frobeniusColimitVectorBundlesPullback`: part (1) of Stacks
  Tag 0EXH for finite locally free `colim_F 𝒪`-modules.
* `AlgebraicGeometry.mem_essImage_of_mem_essImage_baseChange`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe v u₁ u₂ u

namespace CategoryTheory.EndoColim

variable {C : Type u₁} [Category.{v} C] {C' : Type u₂} [Category.{v} C']
  (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')

/-- The iterated comparison carried by `CategoryTheory.EndoColim.map` is the inverse of the
iterated commutation isomorphism used by `CategoryTheory.EndoColim.mapOfComm`. -/
lemma squareIter_eq_endoIterCommIso_symm :
    ∀ (k : ℕ) (E : C), squareIter F F' Φ α k E = (endoIterCommIso Φ α k E).symm
  | 0, E => by
    ext
    simp [squareIter, endoIterCommIso]
  | k + 1, E => by
    ext
    rw [squareIter_succ_hom, squareIter_eq_endoIterCommIso_symm k E, endoIterCommIso_succ]
    simp

/-- **The two constructions of the functor on colimit categories agree on morphisms**:
`CategoryTheory.EndoColim.map`, the descent of a pseudo-cocone, and
`CategoryTheory.EndoColim.mapOfComm`, defined on presentations of morphisms. -/
theorem map_map_eq_mapOfComm_map {A B : EndoColim F} (u : A ⟶ B) :
    (map F F' Φ α).map u = (mapOfComm Φ α).map u := by
  obtain ⟨E, n⟩ := A
  obtain ⟨G, m⟩ := B
  induction u using Quot.ind with
  | _ x =>
    obtain ⟨k, f⟩ := x
    change (map F F' Φ α).map (Hom.of k f) = (mapOfComm Φ α).map (Hom.of k f)
    rw [map_map_of', mapOfComm_map_of]
    congr 1
    rw [transportHom', squareIter_eq_endoIterCommIso_symm, squareIter_eq_endoIterCommIso_symm]
    rfl

/-- **The two constructions of the functor on colimit categories are isomorphic**, by the
identity on objects. -/
def mapIsoMapOfComm : map F F' Φ α ≅ mapOfComm Φ α :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun u ↦
    (Category.comp_id _).trans ((map_map_eq_mapOfComm_map F F' Φ α u).trans
      (Category.id_comp _).symm))

end CategoryTheory.EndoColim

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)

/-- The functor `colim_F Vect(Y) ⥤ colim_F Vect(X)` of Stacks Tag 0EXH is isomorphic to the
transition functor `AlgebraicGeometry.OneGeneratorSquare.colimVectPullback` of the comparison of
Stacks Tag 0EXB, by the identity on objects. -/
def colimVectPullbackIsoFrobeniusColimitVectModelPullback :
    OneGeneratorSquare.colimVectPullback p hX hY f ≅ frobeniusColimitVectModelPullback f p hX hY :=
  EndoColim.mapIsoMapOfComm _ _ _ _

/-- The comparison functor of Stacks Tag 0EXB is an equivalence for the source of a qcqs morphism
to a qcqs scheme. -/
private theorem isEquivalence_comparison_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) [CompactSpace Y] [QuasiSeparatedSpace Y]
    [QuasiCompact f] [QuasiSeparated f] :
    (frobeniusColimitVectComparison X p hX).IsEquivalence := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact isEquivalence_frobeniusColimitVectComparison X p hX

/-- **Part (1) of Stacks Tag 0EXH for finite locally free `colim_F 𝒪`-modules.** For `f : X ⟶ Y`
proper and surjective with geometrically connected fibres onto a quasi-compact quasi-separated
scheme in characteristic `p`, the transition functor of finite locally free `colim_F 𝒪`-modules
along `f` is fully faithful: it is the transition functor of `colim_F Vect`, which is fully
faithful by part (1), conjugated by the equivalences of Stacks Tag 0EXB. -/
theorem fullyFaithful_frobeniusColimitVectorBundlesPullback [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsProper f] [Surjective f] [GeometricallyConnected f] :
    (frobeniusColimitVectorBundlesPullback p f hX hY).Full ∧
      (frobeniusColimitVectorBundlesPullback p f hX hY).Faithful := by
  have := isEquivalence_frobeniusColimitVectComparison Y p hY
  have := isEquivalence_comparison_of_hom f p hX
  obtain ⟨hfu, hfa⟩ := frobeniusColimitVectModelPullback_full_faithful f p hX hY
  let eY := (frobeniusColimitVectComparison Y p hY).asEquivalence
  let eX := (frobeniusColimitVectComparison X p hX).asEquivalence
  have hM : (OneGeneratorSquare.colimVectPullback p hX hY f).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful (frobeniusColimitVectModelPullback f p hX hY)).ofIso
      (colimVectPullbackIsoFrobeniusColimitVectModelPullback f p hX hY).symm
  let e : frobeniusColimitVectorBundlesPullback p f hX hY ≅
      eY.inverse ⋙ OneGeneratorSquare.colimVectPullback p hX hY f ⋙ eX.functor :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight eY.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft eY.inverse (frobeniusColimitVectComparisonPullbackIso p f hX hY)
  have hff := (eY.symm.fullyFaithfulFunctor.comp (hM.comp eX.fullyFaithfulFunctor)).ofIso e.symm
  exact ⟨hff.full, hff.faithful⟩

/-- The comparison functor of Stacks Tag 0EXB carries the transition functor of `colim_F Vect`
along `a` to that of finite locally free `colim_F 𝒪`-modules, at an object. -/
def frobeniusColimitVectComparisonPullbackObjIso {S T : Scheme.{u}} (a : S ⟶ T)
    (hS : IsInCharacteristic S p) (hT : IsInCharacteristic T p)
    (M : frobeniusColimitVectModel T p hT) :
    (frobeniusColimitVectorBundlesPullback p a hS hT).obj
        ((frobeniusColimitVectComparison T p hT).obj M) ≅
      (frobeniusColimitVectComparison S p hS).obj
        ((frobeniusColimitVectModelPullback a p hS hT).obj M) :=
  (frobeniusColimitVectComparisonPullbackIso p a hS hT).app M ≪≫
    (frobeniusColimitVectComparison S p hS).mapIso
      ((colimVectPullbackIsoFrobeniusColimitVectModelPullback a p hS hT).app M)

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Stacks Tag 0EXH, the reduction to an h covering of the base.** Let `p` be a prime, `Y` a
quasi-compact quasi-separated scheme in characteristic `p`, `f : X ⟶ Y` proper and surjective
with geometrically connected fibres, and `g : Y' ⟶ Y` proper, surjective and locally of finite
presentation, with base change `f' : X' ⟶ Y'`, `g' : X' ⟶ X`. If the pullback to `X'` of an
object `A` of `colim_F Vect(X)` lies in the essential image of
`colim_F Vect(Y') ⥤ colim_F Vect(X')`, then `A` lies in the essential image of
`colim_F Vect(Y) ⥤ colim_F Vect(X)`. -/
theorem mem_essImage_of_mem_essImage_baseChange (sq : IsPullback g' f' f g) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hX' : IsInCharacteristic X' p) (hY' : IsInCharacteristic Y' p) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsProper f] [Surjective f] [GeometricallyConnected f] [IsProper g]
    [Surjective g] [LocallyOfFinitePresentation g] (A : frobeniusColimitVectModel X p hX)
    (hA : (frobeniusColimitVectModelPullback f' p hX' hY').essImage
      ((frobeniusColimitVectModelPullback g' p hX' hX).obj A)) :
    (frobeniusColimitVectModelPullback f p hX hY).essImage A := by
  have := isEquivalence_frobeniusColimitVectComparison Y p hY
  have := isEquivalence_comparison_of_hom f p hX
  obtain ⟨B', ⟨b⟩⟩ := hA
  let e₀ : (frobeniusColimitVectorBundlesPullback p f' hX' hY').obj
        ((frobeniusColimitVectComparison Y' p hY').obj B') ≅
      (frobeniusColimitVectorBundlesPullback p g' hX' hX).obj
        ((frobeniusColimitVectComparison X p hX).obj A) :=
    frobeniusColimitVectComparisonPullbackObjIso p f' hX' hY' B' ≪≫
      (frobeniusColimitVectComparison X' p hX').mapIso b ≪≫
      (frobeniusColimitVectComparisonPullbackObjIso p g' hX' hX A).symm
  obtain ⟨ξ, ⟨eξ⟩⟩ := exists_frobeniusColimitVectorBundlesPullback_obj_iso_of_proper_cover sq p
    hX hY hX' hY' (by
      intro W T a hW hT _ _ _ _ _
      exact fullyFaithful_frobeniusColimitVectorBundlesPullback a p hW hT)
    ((frobeniusColimitVectComparison X p hX).obj A)
    ((frobeniusColimitVectComparison Y' p hY').obj B') e₀
  let eB := (frobeniusColimitVectComparison Y p hY).objObjPreimageIso ξ
  exact ⟨(frobeniusColimitVectComparison Y p hY).objPreimage ξ,
    ⟨(Functor.FullyFaithful.ofFullyFaithful (frobeniusColimitVectComparison X p hX)).preimageIso
      ((frobeniusColimitVectComparisonPullbackObjIso p f hX hY _).symm ≪≫
        (frobeniusColimitVectorBundlesPullback p f hX hY).mapIso eB ≪≫ eξ)⟩⟩

end BaseChange

end AlgebraicGeometry

end
