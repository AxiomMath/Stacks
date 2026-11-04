module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGluedIso
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionOverlapCompatible
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionPairInverse

/-!
# The single isomorphism of schemes of [Stacks, Tag 0GPJ]

`AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible` glues a family of
isomorphisms `f i : V i ≅ U i` of open subschemes into a single isomorphism `Y ≅ X` from two
overlap compatibilities,

* `hVcompat`: `(V i ⊓ V j → V i → U i → X) = (V i ⊓ V j → V j → U j → X)`, and
* `hUcompat`: `(U i ⊓ U j → U i → V i → Y) = (U i ⊓ U j → U j → V j → Y)`, taken with respect to
  the inverses `(f i).inv`.

Both are genuinely needed — the module documentation of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGluedIso.lean` carries a two-point
counterexample to dropping the second.  The first is proved for the charts the reconstruction
produces in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionOverlapCompatible.lean`.  This file
proves the second, and then assembles the single isomorphism.

## The mirror argument

The forward compatibility is deduced from rigidity,
`AlgebraicGeometry.eq_of_iso_pullbackTensorFunctor_of_isInvertible`, applied to the two chart
maps read on `V i ⊓ V j`, with the comparison isomorphism of functors supplied by
`AlgebraicGeometry.pullbackTensorFunctorOverlapIso` and the affine open of the target supplied by
`U i`.  Rigidity asks nothing of its source, so the *same* theorem applies on the mirror side,
with source `U i ⊓ U j`, target `Y`, and the affine open `V i` of `Y` — the `V i` are affine opens
by `AlgebraicGeometry.exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover`.

What has to be produced is therefore the **mirror chart data**: for each `i` an equivalence
`QCoh(𝒪_{V i}) ≌ QCoh(𝒪_{U i})`, an invertible sheaf on `U i`, and the two isomorphisms `α`, `β`
of a chart of [Stacks, Tag 0GPJ], all for the inverse equivalence `e.symm` and the inverse chart
maps `(f i).inv`.  Then `AlgebraicGeometry.homOfLE_comp_eq_of_chartIso_overlap` — stated for an
arbitrary functor between the two quasi-coherent categories, so applicable with the roles of `X`
and `Y` exchanged — delivers `hUcompat`.

The mirror of `α` is formal: a square of functors commuting up to isomorphism, two of whose sides
are equivalences, can be conjugated into the mirror square
(`CategoryTheory.Equivalence.mirrorSquareIso`).

The mirror of `β` is the step that was circular before
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionPairInverse.lean` existed.  It needs
the inverse of `(f i)^*(-) ⊗ L i` to be again of the shape "inverse image along a morphism of
schemes, twisted by an invertible sheaf", for the *inverse* morphism — which is exactly
`AlgebraicGeometry.exists_isInvertible_pullbackTensorFunctor_inverse`.  Granted that, the
computation is again formal: writing `P` for `(f i)^*(-) ⊗ L i`, `T'` for the twisted inverse
image along `(f i).inv`, and `G` for the chart equivalence,

`G.inverse ⋙ ι ≅ G.inverse ⋙ (P ⋙ T') ≅ G.inverse ⋙ ((G.functor ⋙ ι) ⋙ T') ≅ ι ⋙ T'`,

and `ι ⋙ T'` is `(f i).inv^*(-) ⊗ L' i` by `AlgebraicGeometry.pullbackTensorFunctor_eq`.

## Main definitions

* `CategoryTheory.Equivalence.mirrorSquareIso` — conjugating a commuting square of functors by
  equivalences on two opposite sides.
* `CategoryTheory.Equivalence.mirrorCompIso` — the special case used for the tensor factor.

## Main results

* `AlgebraicGeometry.exists_isInvertible_inverseCompIotaIso` — **the mirror of `β`**: the inverse
  of a chart equivalence is again inverse image along the inverse chart map twisted by an
  invertible sheaf.
* `AlgebraicGeometry.exists_isOpenCover_schemeIso_mirrorOverlapCompatible_of_isAffineOpenCover` —
  **both overlap compatibilities for the reconstruction's own charts**, for one and the same
  family of opens `V i`, equivalences `G i`, isomorphisms `f i`, invertible sheaves `L i` and
  chart isomorphisms `α i`, `β i`.  The last two conjuncts are verbatim the hypotheses
  `hVcompat` and `hUcompat` of
  `AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`.
* `AlgebraicGeometry.exists_schemeIso_of_quasicoherentEquivalence_of_isAffineOpenCover` — **the
  single isomorphism of schemes together with the chart data it was glued from**: an equivalence
  `QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` of quasi-compact quasi-separated schemes yields one isomorphism
  `g : Y ≅ X` and the whole family `V, G, f, L, α, β` of charts it restricts to.
* `AlgebraicGeometry.exists_schemeIso_of_quasicoherentEquivalence` — the same with the affine open
  cover of `X` deleted, every scheme being covered by its affine opens.

## What this does and does not give for [Stacks, Tag 0GPJ]

The conclusion of [Stacks, Tag 0GPJ] is a single isomorphism of schemes `Y ≅ X` **together with**
a single invertible `𝒪_Y`-module presenting the equivalence.  The scheme half is complete here.
Gluing the per-chart invertible sheaves `L i` into one invertible `𝒪_Y`-module is a separate
descent problem, reduced but not solved in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGluedModule.lean`, and nothing below
assumes anything about it.

## Implementation notes

The `implicit_reducible` block is the one declared in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`, and it is needed for the
same reason: the structure sheaf of a scheme is named both as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf, and
instance search, which runs at reducible transparency, sees through neither chain.

The chart functors `F i` come with `Functor.IsEquivalence` as a *conjunct* rather than as an
instance, so `(F i).asEquivalence` cannot be written inside a statement quantified over `i`.  The
families are therefore replaced at once by genuine equivalences `G i` with `(G i).functor = F i`,
again by `choose`, which also keeps the families opaque for the reason recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalForm.lean`.

Both compatibilities are proved in the same theorem rather than by citing the existing
`AlgebraicGeometry.exists_isOpenCover_schemeIso_overlapCompatible_of_isAffineOpenCover`, because
the gluing needs them for *one* family: that theorem makes its own existential choice of `V` and
`f`, and nothing identifies it with the choice made here.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 17.23.3 (Tag 0B8L)](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory.Equivalence

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- **Conjugating a commuting square by equivalences on two opposite sides.**  Let
`G : A ≌ B` and `K : C ≌ D` be equivalences, let `R : A ⥤ C` and `S : B ⥤ D`, and suppose
`G.functor ⋙ S ≅ R ⋙ K.functor`.  Then the mirror square commutes too:
`G.inverse ⋙ R ≅ S ⋙ K.inverse`.

Read from the left: `R ≅ R ⋙ K.functor ⋙ K.inverse` by the unit of `K`, the hypothesis replaces
`R ⋙ K.functor` by `G.functor ⋙ S`, and the counit of `G` cancels `G.inverse ⋙ G.functor`. -/
def mirrorSquareIso (G : A ≌ B) (R : A ⥤ C) (S : B ⥤ D) (K : C ≌ D)
    (α : G.functor ⋙ S ≅ R ⋙ K.functor) :
    G.inverse ⋙ R ≅ S ⋙ K.inverse :=
  Functor.isoWhiskerLeft G.inverse
      (R.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft R K.unitIso ≪≫
        (Functor.associator R K.functor K.inverse).symm ≪≫
        Functor.isoWhiskerRight α.symm K.inverse ≪≫
        Functor.associator G.functor S K.inverse) ≪≫
    (Functor.associator G.inverse G.functor (S ⋙ K.inverse)).symm ≪≫
    Functor.isoWhiskerRight G.counitIso (S ⋙ K.inverse) ≪≫
    Functor.leftUnitor (S ⋙ K.inverse)

/-- **Cancelling an equivalence out of the left of a factorisation.**  If `G : A ≌ B` and
`G.functor ⋙ S ≅ P`, then for every `K` one has `G.inverse ⋙ P ⋙ K ≅ S ⋙ K`: substitute the
hypothesis and cancel `G.inverse ⋙ G.functor` by the counit of `G`. -/
def mirrorCompIso (G : A ≌ B) {S : B ⥤ C} {P : A ⥤ C} (β : G.functor ⋙ S ≅ P) (K : C ⥤ D) :
    G.inverse ⋙ P ⋙ K ≅ S ⋙ K :=
  Functor.isoWhiskerLeft G.inverse
      (Functor.isoWhiskerRight β.symm K ≪≫ Functor.associator G.functor S K) ≪≫
    (Functor.associator G.inverse G.functor (S ⋙ K)).symm ≪≫
    Functor.isoWhiskerRight G.counitIso (S ⋙ K) ≪≫ Functor.leftUnitor (S ⋙ K)

end CategoryTheory.Equivalence

namespace AlgebraicGeometry

universe u

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither.  Without this
an invertibility hypothesis spelled with `ringCatSheaf.2` does not deliver
`Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence`.  The same list is declared in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/AffineReconstruction.lean`. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf

/-! ### The mirror of a chart -/

/-- **The inverse of a reconstruction chart is a reconstruction chart for the inverse chart
map.**  Let `V ⊆ Y` and `U ⊆ X` be opens, let `G : QCoh(𝒪_U) ≌ QCoh(𝒪_V)` be an equivalence, let
`f : V ≅ U` be an isomorphism of schemes and let `L` be an invertible sheaf of `𝒪_V`-modules with
`G ≅ f^*(-) ⊗ L`.  Then there is an invertible sheaf `L'` of `𝒪_U`-modules with
`G.inverse ≅ (f^{-1})^*(-) ⊗ L'`, both read in all modules.

The sheaf `L'` and the contraction of the two twisted inverse images are
`AlgebraicGeometry.exists_isInvertible_pullbackTensorFunctor_inverse`; the rest is
`CategoryTheory.Equivalence.mirrorCompIso` and the fact that
`AlgebraicGeometry.pullbackTensorFunctor` is the inclusion of the quasi-coherent modules followed
by `AlgebraicGeometry.twistedPullback` (`AlgebraicGeometry.pullbackTensorFunctor_eq`). -/
theorem exists_isInvertible_inverseCompIotaIso {X Y : Scheme.{u}} {V : Y.Opens} {U : X.Opens}
    (G : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory)
    (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (hL : Stacks.SheafOfModules.IsInvertible V.toScheme.presheaf V.toScheme.ringCatSheaf.2 L)
    (β : G.functor ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor f.hom L) :
    ∃ L' : SheafOfModules.{u} U.toScheme.ringCatSheaf,
      Stacks.SheafOfModules.IsInvertible U.toScheme.presheaf U.toScheme.ringCatSheaf.2 L' ∧
        Nonempty (G.inverse ⋙
            ObjectProperty.ι (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf) ≅
          pullbackTensorFunctor f.inv L') := by
  obtain ⟨L', hL', ⟨hfwd⟩, -⟩ := exists_isInvertible_pullbackTensorFunctor_inverse f L hL
  exact ⟨L', hL', ⟨Functor.isoWhiskerLeft G.inverse hfwd.symm ≪≫
    Equivalence.mirrorCompIso G β (twistedPullback f.inv L')⟩⟩

/-! ### Both overlap compatibilities for the reconstruction's own charts -/

/-- **The two overlap compatibilities `hVcompat` and `hUcompat` for the charts the reconstruction
produces, together with the chart data itself.**  Let `X` and `Y` be quasi-compact and
quasi-separated schemes, let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence and let `U i` be an
affine open cover of `X`.  Then there are affine opens `V i` covering `Y`, equivalences
`G i : QCoh(𝒪_{U i}) ≌ QCoh(𝒪_{V i})`, isomorphisms `f i : V i ≅ U i`, invertible sheaves `L i`
of `𝒪_{V i}`-modules and the two chart isomorphisms

* `α i : e ⋙ (- |_{V i}) ≅ (- |_{U i}) ⋙ G i`, compatibility with the two restrictions, and
* `β i : G i ⋙ ι ≅ (f i)^*(-) ⊗ L i`, the prescribed form of the chart,

such that for every pair `i, j` the two chart maps agree on `V i ⊓ V j` as morphisms into `X`,
**and** the two inverse chart maps agree on `U i ⊓ U j` as morphisms into `Y`.

The last two conjuncts are verbatim the hypotheses `hVcompat` and `hUcompat` of
`AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`, for one and the same
family of charts, which is what gluing them needs.

Both are instances of `AlgebraicGeometry.homOfLE_comp_eq_of_chartIso_overlap`: the first for `e`
and the charts as given, with the affine open `U i` of `X`; the second for `e.symm` and the
mirror charts, with the affine open `V i` of `Y`.  The mirror charts are
`AlgebraicGeometry.exists_isInvertible_inverseCompIotaIso` for the tensor factor and
`CategoryTheory.Equivalence.mirrorSquareIso` for the compatibility with the two restrictions.

`G`, `L`, `α` and `β` are returned rather than discarded because the remaining half of
[Stacks, Tag 0GPJ] — the single invertible `𝒪_Y`-module and the natural isomorphism
`e(𝓕) ≅ g^*𝓕 ⊗ ℳ` — needs them for *this* family of charts, the one the glued `g` restricts to.
Each `β i` is an existential choice, so two of them over a common open differ by an automorphism
of the chart functor; normalising that difference away is what produces the module, and it
cannot even be stated unless the family is in hand. -/
theorem exists_isOpenCover_schemeIso_mirrorOverlapCompatible_of_isAffineOpenCover
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {ι : Type u} (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    ∃ (V : ι → Y.Opens)
      (G : ∀ i, (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).FullSubcategory ≌
        (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf).FullSubcategory)
      (f : ∀ i, (V i).toScheme ≅ (U i).toScheme)
      (L : ∀ i, SheafOfModules.{u} (V i).toScheme.ringCatSheaf)
      (_α : ∀ i, e.functor ⋙ quasicoherentRestriction (V i).ι ≅
        quasicoherentRestriction (U i).ι ⋙ (G i).functor)
      (_β : ∀ i, (G i).functor ⋙
          ObjectProperty.ι (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf) ≅
        pullbackTensorFunctor (f i).hom (L i)),
      IsOpenCover V ∧ (∀ i, IsAffineOpen (V i)) ∧
        (∀ i, Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
          (V i).toScheme.ringCatSheaf.2 (L i)) ∧
        (∀ i j, Y.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ (f i).hom ≫ (U i).ι =
          Y.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ (f j).hom ≫ (U j).ι) ∧
        ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (f i).inv ≫ (V i).ι =
          X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (f j).inv ≫ (V j).ι := by
  obtain ⟨V, hVcover, hV⟩ :=
    exists_isOpenCover_schemeIso_invertibleSheaf_of_isAffineOpenCover e U hUaff hUcover
  choose hVaff hVc F f L hFequiv hLinv hα hβ using hV
  -- Replace the chart functors by genuine equivalences, so that `G i` can be named in a
  -- statement quantified over `i`.
  have hGex : ∀ i, ∃ G :
      (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).FullSubcategory ≌
        (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf).FullSubcategory,
      G.functor = F i := fun i =>
    have := hFequiv i
    ⟨(F i).asEquivalence, rfl⟩
  choose G hG using hGex
  have hαG : ∀ i, Nonempty (e.functor ⋙ quasicoherentRestriction (V i).ι ≅
      quasicoherentRestriction (U i).ι ⋙ (G i).functor) := fun i => by rw [hG i]; exact hα i
  have hβG : ∀ i, Nonempty ((G i).functor ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf) ≅
      pullbackTensorFunctor (f i).hom (L i)) := fun i => by rw [hG i]; exact hβ i
  have hmirror : ∀ i, ∃ L' : SheafOfModules.{u} (U i).toScheme.ringCatSheaf,
      Stacks.SheafOfModules.IsInvertible (U i).toScheme.presheaf
          (U i).toScheme.ringCatSheaf.2 L' ∧
        Nonempty ((G i).inverse ⋙
            ObjectProperty.ι (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf) ≅
          pullbackTensorFunctor (f i).inv L') := fun i =>
    exists_isInvertible_inverseCompIotaIso (G i) (f i) (L i) (hLinv i) (hβG i).some
  choose L' hL'inv hβ' using hmirror
  refine ⟨V, G, f, L, fun i => (hαG i).some, fun i => (hβG i).some, hVcover, hVaff, hLinv,
    fun i j => ?_, fun i j => ?_⟩
  · have := hLinv i
    have := hLinv j
    exact homOfLE_comp_eq_of_chartIso_overlap e.functor (f i) (f j) (L i) (L j)
      (hα i).some (hβ i).some (hα j).some (hβ j).some (hUaff i)
  · have := hL'inv i
    have := hL'inv j
    exact homOfLE_comp_eq_of_chartIso_overlap e.inverse (f i).symm (f j).symm (L' i) (L' j)
      (Equivalence.mirrorSquareIso e (quasicoherentRestriction (U i).ι)
        (quasicoherentRestriction (V i).ι) (G i) (hαG i).some)
      (hβ' i).some
      (Equivalence.mirrorSquareIso e (quasicoherentRestriction (U j).ι)
        (quasicoherentRestriction (V j).ι) (G j) (hαG j).some)
      (hβ' j).some (hVaff i)

/-! ### The single isomorphism of schemes -/

/-- **The scheme half of [Stacks, Tag 0GPJ]: one isomorphism `Y ≅ X`, together with the chart
data it was glued from.**  Let `X` and `Y` be quasi-compact and quasi-separated schemes, let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence of their categories of quasi-coherent modules and
let `U i` be an affine open cover of `X`.  Then there is a **single** isomorphism of schemes
`g : Y ≅ X`, together with affine opens `V i` covering `Y`, equivalences
`G i : QCoh(𝒪_{U i}) ≌ QCoh(𝒪_{V i})`, isomorphisms `f i : V i ≅ U i` to which `g` restricts,
invertible sheaves `L i` of `𝒪_{V i}`-modules, and the two chart isomorphisms
`α i : e ⋙ (- |_{V i}) ≅ (- |_{U i}) ⋙ G i` and `β i : G i ⋙ ι ≅ (f i)^*(-) ⊗ L i`.

Nothing is assumed beyond the equivalence, the cover, and quasi-compactness and
quasi-separatedness of the two schemes.  The two overlap compatibilities are
`AlgebraicGeometry.exists_isOpenCover_schemeIso_mirrorOverlapCompatible_of_isAffineOpenCover` and
the gluing is `AlgebraicGeometry.exists_schemeIso_of_isOpenCover_of_overlapCompatible`.

The point of carrying `G`, `L`, `α` and `β` out alongside `g` is that they are the charts of
*this* `g`: the restriction equation `(V i).ι ≫ g.hom = (f i).hom ≫ (U i).ι` ties them together.
A separate appeal to the chart theorem would make its own existential choice of `V` and `f`, and
nothing would identify it with the choice `g` was glued from.

The invertible `𝒪_Y`-module that [Stacks, Tag 0GPJ] asserts alongside `g` is *not* produced:
gluing the per-chart invertible sheaves `L i` is a separate descent problem. -/
theorem exists_schemeIso_of_quasicoherentEquivalence_of_isAffineOpenCover {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
    {ι : Type u} (U : ι → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (hUcover : IsOpenCover U) :
    ∃ (g : Y ≅ X) (V : ι → Y.Opens)
      (G : ∀ i, (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).FullSubcategory ≌
        (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf).FullSubcategory)
      (f : ∀ i, (V i).toScheme ≅ (U i).toScheme)
      (L : ∀ i, SheafOfModules.{u} (V i).toScheme.ringCatSheaf)
      (_α : ∀ i, e.functor ⋙ quasicoherentRestriction (V i).ι ≅
        quasicoherentRestriction (U i).ι ⋙ (G i).functor)
      (_β : ∀ i, (G i).functor ⋙
          ObjectProperty.ι (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf) ≅
        pullbackTensorFunctor (f i).hom (L i)),
      IsOpenCover V ∧ (∀ i, IsAffineOpen (V i)) ∧
        (∀ i, Stacks.SheafOfModules.IsInvertible (V i).toScheme.presheaf
          (V i).toScheme.ringCatSheaf.2 (L i)) ∧
        ∀ i, (V i).ι ≫ g.hom = (f i).hom ≫ (U i).ι := by
  obtain ⟨V, G, f, L, α, β, hVcover, hVaff, hLinv, hVcompat, hUcompat⟩ :=
    exists_isOpenCover_schemeIso_mirrorOverlapCompatible_of_isAffineOpenCover e U hUaff hUcover
  obtain ⟨g, hg, -⟩ := exists_schemeIso_of_isOpenCover_of_overlapCompatible V U hVcover hUcover f
    hVcompat hUcompat
  exact ⟨g, V, G, f, L, α, β, hVcover, hVaff, hLinv, hg⟩

/-- **The scheme half of [Stacks, Tag 0GPJ] with no cover hypothesised.**  Two quasi-compact
quasi-separated schemes with equivalent categories of quasi-coherent modules are isomorphic.

This is the statement above with the affine open cover of `X` deleted: `X` is covered by its own
affine opens, `AlgebraicGeometry.iSup_affineOpens_eq_top`, and that family is indexed by
`AlgebraicGeometry.Scheme.affineOpens`, a type in the same universe. -/
@[stacks 0GPJ "the SCHEME HALF of the tag's conclusion, unconditionally: `X` and `Y` \
quasi-compact and quasi-separated and an equivalence of their categories of quasi-coherent \
modules give an isomorphism of schemes `Y ≅ X`.  No cover, no affineness, no invertible module \
and no further hypothesis of any kind beyond qcqs.  This is the step the Stacks source dismisses \
with \"We omit the details\", carried out: the charts are matched \
(`ReconstructionGlobalForm.lean`), they cover `Y` (`ReconstructionCover.lean:164`), they agree on \
overlaps in both directions \
(`ReconstructionOverlapCompatible.lean:256`, `ReconstructionGlobalSchemeIso.lean:223`) because \
the matched pair is rigid (`ReconstructionRigidity.lean:141`), and they glue \
(`ReconstructionGluedIso.lean:113`).  The MODULE half — 0GPJ also asserts a single invertible \
`𝒪_Y`-module `L` with `e(F) ≅ f^*F ⊗ L` — is NOT produced here: it is \
`isInvertible_map_quasicoherentUnit_of_quasicoherentEquivalence` \
(`ReconstructionGlobalModule.lean`), the module being `e(𝒪_X)`, and the comparison of functors \
is `exists_natIso_pullbackTensorFunctor_of_quasicoherentEquivalence` \
(`ReconstructionGlobalComparison.lean`).  Nothing in this statement assumes either"]
theorem exists_schemeIso_of_quasicoherentEquivalence {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory) :
    Nonempty (Y ≅ X) := by
  obtain ⟨g, -⟩ := exists_schemeIso_of_quasicoherentEquivalence_of_isAffineOpenCover e
    (fun i : X.affineOpens => (i : X.Opens)) (fun i => i.2) (iSup_affineOpens_eq_top X)
  exact ⟨g⟩

end AlgebraicGeometry

end
