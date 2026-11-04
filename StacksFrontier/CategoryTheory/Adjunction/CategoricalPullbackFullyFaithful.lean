module

public import StacksFrontier.CategoryTheory.Adjunction.CategoricalPullbackGluing

/-!
# The functor into a two-fibre product with fully faithful legs

Let `Lf : 𝒳 ⥤ 𝒳'`, `Li : 𝒳 ⥤ 𝒵`, `Lj : 𝒳' ⥤ ℰ`, `Lg : 𝒵 ⥤ ℰ` be functors and
`c : Lf ⋙ Lj ≅ Li ⋙ Lg` a natural isomorphism, and consider the canonical functor
`Stacks.CategoryTheory.modificationGluingFunctor c : 𝒳 ⥤ Lj ⊡ Lg` into the two-fibre product,
`F ↦ (Lf F, Li F, c_F)`.

If `Li` and `Lj` are fully faithful, the forgetful functor `(G, H, α) ↦ H` identifies the
two-fibre product with a full subcategory of `𝒵`, and the canonical functor is fully faithful:
a morphism of triples is determined by its second component. Its essential image consists of
the triples whose second entry lies in the essential image of `Li`. This is the formal first
paragraph of the proof of [Stacks, Tag 0DEU].

## Main results

* `Stacks.CategoryTheory.modificationGluingFunctor_faithful`,
  `Stacks.CategoryTheory.modificationGluingFunctor_full` — the canonical functor is fully
  faithful.
* `Stacks.CategoryTheory.modificationGluingFunctor_essImage_of_snd` — a triple whose second
  entry is in the essential image of `Li` is in the essential image of the canonical functor.
* `Stacks.CategoryTheory.modificationGluingFunctor_isEquivalence_of_snd` — the canonical functor
  is an equivalence once the second entry of every triple is in the essential image of `Li`.

## References

* [Stacks Project, Tag 0DEU](https://stacks.math.columbia.edu/tag/0DEU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback

namespace Stacks.CategoryTheory

variable {𝒳 : Type*} {𝒳' : Type*} {𝒵 : Type*} {ℰ : Type*}
  [Category* 𝒳] [Category* 𝒳'] [Category* 𝒵] [Category* ℰ]
  {Lf : 𝒳 ⥤ 𝒳'} {Li : 𝒳 ⥤ 𝒵} {Lj : 𝒳' ⥤ ℰ} {Lg : 𝒵 ⥤ ℰ} (c : Lf ⋙ Lj ≅ Li ⋙ Lg)

/-- **The canonical functor into the two-fibre product is faithful** when `Li` is: a morphism
is recovered from its image under `Li`, which is the second component of its image. -/
theorem modificationGluingFunctor_faithful [Li.Faithful] :
    (modificationGluingFunctor c).Faithful where
  map_injective h :=
    Li.map_injective (congrArg CategoricalPullback.Hom.snd h)

/-- **The canonical functor into the two-fibre product is full** when `Li` is full and `Lj` is
faithful: the second component of a morphism of triples is `Li φ` for some `φ`, and then the
first component is `Lf φ`, because both have the same image under `Lj` by the compatibility
with the structure isomorphisms. -/
theorem modificationGluingFunctor_full [Li.Full] [Lj.Faithful] :
    (modificationGluingFunctor c).Full where
  map_surjective {F F'} m := by
    obtain ⟨φ, hφ⟩ := Li.map_surjective m.snd
    have hc : Lj.map (Lf.map φ) ≫ (c.app F').hom = (c.app F).hom ≫ Lg.map (Li.map φ) :=
      c.hom.naturality φ
    refine ⟨φ, CategoricalPullback.hom_ext (Lj.map_injective ?_) hφ⟩
    exact (cancel_mono (c.app F').hom).1 (hc.trans (hφ ▸ m.w.symm))

/-- **A triple whose second entry is in the essential image of `Li` is in the essential image
of the canonical functor**, when `Lj` is fully faithful. If `e : Li F ≅ H`, the first entry is
recovered as the preimage under `Lj` of the composite `Lj (Lf F) ≅ Lg (Li F) ≅ Lg H ≅ Lj G`. -/
theorem modificationGluingFunctor_essImage_of_snd [Lj.Full] [Lj.Faithful] (T : Lj ⊡ Lg)
    (hT : Li.essImage T.snd) : (modificationGluingFunctor c).essImage T := by
  obtain ⟨F, ⟨e⟩⟩ := hT
  let eₗ : Lf.obj F ≅ T.fst :=
    (Functor.FullyFaithful.ofFullyFaithful Lj).preimageIso
      (c.app F ≪≫ Lg.mapIso e ≪≫ T.iso.symm)
  refine ⟨F, ⟨CategoricalPullback.mkIso eₗ e ?_⟩⟩
  simp [eₗ]

/-- **The canonical functor into the two-fibre product is an equivalence** when `Li` and `Lj`
are fully faithful and the second entry of every triple lies in the essential image of `Li`. -/
theorem modificationGluingFunctor_isEquivalence_of_snd [Li.Full] [Li.Faithful] [Lj.Full]
    [Lj.Faithful] (h : ∀ T : Lj ⊡ Lg, Li.essImage T.snd) :
    (modificationGluingFunctor c).IsEquivalence :=
  have := modificationGluingFunctor_faithful c
  have := modificationGluingFunctor_full c
  have : (modificationGluingFunctor c).EssSurj :=
    ⟨fun T => modificationGluingFunctor_essImage_of_snd c T (h T)⟩
  { }

end Stacks.CategoryTheory
