module

public import StacksFrontier.AlgebraicGeometry.HilbertFibreAffineOpen.BaseRestriction
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorTotalPresheaf
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenAmbient
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition

/-!
# The Hilbert functor of points is representable

Let `X` be a scheme over `S` and let `d` be a natural number. If every finite set of points of
`X` lying in a single fibre of `X ⟶ S` is contained in an affine open of `X`, then the degree-`d`
Hilbert functor of points of `X` over `S` is representable by a scheme over `S`.

This is the gluing assembly of Stacks Tag 0B9A. It is stated twice: once with the two things the
source's proof needs of `X ⟶ S` taken as hypotheses — the conclusion of the source's footnote,
`Stacks.Hilbert.FamiliesClosedInAmbient`, and the `d`-tuple form of the fibrewise affineness
hypothesis — and once under the **set form** of the fibrewise affineness hypothesis, which
discharges both and is what all seven cases of Stacks Tag 0B9B establish.

**Nothing in this file carries the `@[stacks 0B9A]` attribute**: the tag is registered on
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`
in `StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`, which supplies
the footnote from separatedness of `X ⟶ S` and so runs under the affine-open hypothesis the tag
itself states, for every `d ≠ 1`, where the tag holds. The set form is strictly stronger than
the tag's `d`-tuple form — the footnote needs `d + 1` points of one fibre — so the theorem in
this file is not the tag; see the module docstring of
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorOpenAmbient.lean`.

## Main definitions

* `Stacks.Hilbert.openOverBase` — an affine open `U ⊆ X` lying over an open `V ⊆ S`, viewed as a
  scheme over `V`.
* `Stacks.Hilbert.ambientBaseIso` — the resulting identification `U ×_V T = U ×_S T`.
* `Stacks.Hilbert.hilbertFamilyBaseEquiv` — hence: degree-`d` Hilbert families in `U` over a
  `V`-scheme `T` are degree-`d` Hilbert families in `U` over `T` read as an `S`-scheme.
* `Stacks.Hilbert.BaseChartIndex` — the index of a chart: an affine open `V ⊆ S` together with
  an affine open `U ⊆ X` lying over it.
* `Stacks.Hilbert.baseChart` — the chart of the criterion attached to such an index.
* `Stacks.Hilbert.chartOpens` — the open of a test object cutting out the image of a chart.

## Main results

* `Stacks.Hilbert.isPullback_comp_mono` — a cartesian square stays cartesian after composing its
  bottom edges with a monomorphism.
* `Stacks.Hilbert.HilbertFamily.extendToAmbient_baseChange` and
  `Stacks.Hilbert.HilbertFamily.extendToAmbient_injective` — extending a family of an open to
  the ambient scheme commutes with base change and is injective.
* `Stacks.Hilbert.injective_baseChart_app` and `Stacks.Hilbert.exists_baseChart_app_iff` —
  conditions (2)(a) and (2)(b) of the criterion of Stacks 01JJ for a chart.
* `Stacks.Hilbert.exists_isAffineOpen_le_mem_supportOpens` and
  `Stacks.Hilbert.locallySurjective_baseChart` — condition (2)(c): the charts cover.
* `Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_familiesClosedInAmbient` — **the
  representability theorem**, from the footnote's conclusion and the `d`-tuple form of the
  fibrewise affineness hypothesis, and
  `Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_hasAffineFinitePointsInFibres` —
  the same under the set form of that hypothesis.

## Implementation notes

*Why Stacks 01LG is not needed.* The source reduces to an affine base before applying the
criterion. That reduction is avoided here by indexing the charts by *pairs*: an affine open
`V ⊆ S` and an affine open `U ⊆ X` lying over `V`. The chart of such a pair is representable by
Stacks 0B99 applied to the affine `U` over the affine `V`, and the base change between `V` and
`S` is absorbed by `Stacks.Hilbert.ambientBaseIso`, which is cartesian only because `V ⊆ S` is a
monomorphism. The same device is used for Stacks Tag 0BL4 in
`StacksFrontier/AlgebraicGeometry/Morphisms/FiniteLocallyFree/Representability.lean`.

*What each chart is.* For a pair `(V, U)` the chart is the morphism from the functor of points
of the scheme representing `Hilb^d_{U/V}` into the total presheaf of `Hilb^d_{X/S}`, classifying
the universal family of `U` read over `S` and extended to `X`. Its image over a test object `T`
carrying a structure morphism `ψ` and a family `Z` is cut out by
`ψ ⁻¹ᵁ V ⊓ Z.supportOpens U`: the base must land in `V` and the family must be supported in `U`.
Injectivity of the chart uses that `V ⊆ S` is a monomorphism for the first component and that
classifying, reading over `S` and extending are injective for the second.

*Where the hypothesis is used.* Twice, as in the source, and the two uses are separate
hypotheses here: the covering condition takes the `d`-tuple form, through
`Stacks.Hilbert.exists_isAffineOpen_mem_supportOpens`, which is all it needs; the identification
of `F_U` with `Hilb^d_{U/S}` takes `Stacks.Hilbert.FamiliesClosedInAmbient`, the conclusion of
the footnote `Stacks.Hilbert.isClosed_range_of_isFinite_comp_structureMorphism`, which the
`d`-tuple form does not give. The
covering condition needs the affine open of `X` to lie over the affine open of `S`, which is
`Stacks.Hilbert.exists_isAffineOpen_le_mem_supportOpens`: the affine open supporting the family
at a point is shrunk into the preimage of `V` by prime avoidance, the fibre of the subscheme
over that point being finite.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B9B](https://stacks.math.columbia.edu/tag/0B9B)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01LG](https://stacks.math.columbia.edu/tag/01LG)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Sites

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-- A cartesian square stays cartesian after composing its bottom edges with a monomorphism. -/
theorem isPullback_comp_mono {P A B C D : Scheme.{u}} {p : P ⟶ A} {q : P ⟶ B} {f : A ⟶ C}
    {g : B ⟶ C} (h : IsPullback p q f g) (i : C ⟶ D) [Mono i] :
    IsPullback p q (f ≫ i) (g ≫ i) where
  w := by rw [← Category.assoc, h.w, Category.assoc]
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst s.snd ((cancel_mono i).1 (by
      rw [Category.assoc, Category.assoc]
      exact s.condition)))
    (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _)
    (fun s m hm₁ hm₂ => h.hom_ext (by rw [hm₁, h.lift_fst]) (by rw [hm₂, h.lift_snd]))⟩

/-! ### An open of the ambient scheme as a scheme over an open of the base -/

section OpenOverBase

variable (X : Over S) (V : S.Opens) (U : X.left.Opens)

/-- The structure morphism of an open `U ⊆ X` lying over an open `V ⊆ S`, as a morphism to `V`. -/
def openOverBaseHom (hUV : U ≤ X.hom ⁻¹ᵁ V) : U.toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (U.ι ≫ X.hom) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨u, rfl⟩
    exact hUV u.2)

/-- An open `U ⊆ X` lying over an open `V ⊆ S`, viewed as a scheme over `V`. -/
def openOverBase (hUV : U ≤ X.hom ⁻¹ᵁ V) : Over V.toScheme :=
  Over.mk (openOverBaseHom X V U hUV)

@[simp]
theorem openOverBase_left (hUV : U ≤ X.hom ⁻¹ᵁ V) :
    (openOverBase X V U hUV).left = U.toScheme :=
  rfl

/-- The structure morphism of `U` over `V`, followed by `V ⊆ S`, is the structure morphism of `U`
over `S`. -/
@[simp]
theorem openOverBase_hom_comp (hUV : U ≤ X.hom ⁻¹ᵁ V) :
    (openOverBase X V U hUV).hom ≫ V.ι = (openAmbient X U).hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The ambient scheme of a family does not change when the base is restricted to an open of
`S` the open `U ⊆ X` lies over**: `U ×_V T` is `U ×_S T`. This is where the fact that `V ⊆ S` is
a monomorphism is used. -/
theorem isPullback_ambientBase (hUV : U ≤ X.hom ⁻¹ᵁ V) (T : Over V.toScheme) :
    IsPullback (familyProjection (openOverBase X V U hUV) T)
      ((Over.pullback T.hom).obj (openOverBase X V U hUV)).hom
      (openAmbient X U).hom ((Over.map V.ι).obj T).hom := by
  have h := isPullback_comp_mono
    (isPullback_structureMorphism (openOverBase X V U hUV) T) V.ι
  rwa [openOverBase_hom_comp] at h

/-- **The comparison isomorphism `U ×_V T ≅ U ×_S T`** of
`Stacks.Hilbert.isPullback_ambientBase`. -/
def ambientBaseIso (hUV : U ≤ X.hom ⁻¹ᵁ V) (T : Over V.toScheme) :
    ((Over.pullback T.hom).obj (openOverBase X V U hUV)).left ≅
      ((Over.pullback ((Over.map V.ι).obj T).hom).obj (openAmbient X U)).left :=
  (isPullback_ambientBase X V U hUV T).isoPullback

@[reassoc (attr := simp)]
theorem ambientBaseIso_hom_comp_familyProjection (hUV : U ≤ X.hom ⁻¹ᵁ V) (T : Over V.toScheme) :
    (ambientBaseIso X V U hUV T).hom ≫
        familyProjection (openAmbient X U) ((Over.map V.ι).obj T) =
      familyProjection (openOverBase X V U hUV) T :=
  (isPullback_ambientBase X V U hUV T).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem ambientBaseIso_hom_comp_structureMorphism (hUV : U ≤ X.hom ⁻¹ᵁ V)
    (T : Over V.toScheme) :
    (ambientBaseIso X V U hUV T).hom ≫
        ((Over.pullback ((Over.map V.ι).obj T).hom).obj (openAmbient X U)).hom =
      ((Over.pullback T.hom).obj (openOverBase X V U hUV)).hom :=
  (isPullback_ambientBase X V U hUV T).isoPullback_hom_snd

end OpenOverBase

/-! ### Transporting an ideal sheaf along an isomorphism -/

section IdealIso

variable {A B : Scheme.{u}}

/-- The comparison morphism from the subscheme cut out by the transport of an ideal sheaf along
an isomorphism to the subscheme cut out by the ideal sheaf itself. -/
def idealComapIsoHom (e : A ≅ B) (I : A.IdealSheafData) :
    (I.comap e.inv).subscheme ⟶ I.subscheme :=
  (I.comapIso e.inv).hom ≫ pullback.snd e.inv I.subschemeι

instance isIso_idealComapIsoHom (e : A ≅ B) (I : A.IdealSheafData) :
    IsIso (idealComapIsoHom e I) := by
  rw [idealComapIsoHom]
  infer_instance

/-- The inclusion of the subscheme cut out by the transported ideal sheaf, read through the
comparison morphism. -/
theorem idealComapIsoHom_comp_subschemeι (e : A ≅ B) (I : A.IdealSheafData) :
    (I.comap e.inv).subschemeι ≫ e.inv = idealComapIsoHom e I ≫ I.subschemeι := by
  rw [idealComapIsoHom, ← Scheme.IdealSheafData.comapIso_hom_fst I e.inv, Category.assoc,
    Category.assoc, pullback.condition]

/-- Transporting an ideal sheaf along an isomorphism and back recovers it. -/
@[simp]
theorem comap_inv_comap_hom (e : A ≅ B) (I : A.IdealSheafData) :
    (I.comap e.inv).comap e.hom = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id]

/-- Transporting an ideal sheaf along the inverse of an isomorphism and back recovers it. -/
@[simp]
theorem comap_hom_comap_inv (e : A ≅ B) (J : B.IdealSheafData) :
    (J.comap e.hom).comap e.inv = J := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- **Finite local freeness of a given rank over a base transports along an isomorphism of
ambient schemes compatible with the structure morphisms to that base.** -/
theorem isFiniteLocallyFreeOfRank_comap_of_iso {T : Scheme.{u}} (e : A ≅ B) {qA : A ⟶ T}
    {qB : B ⟶ T} (hq : e.hom ≫ qB = qA) (I : A.IdealSheafData) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ qA) d] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I.comap e.inv).subschemeι ≫ qB) d := by
  have hqB : e.inv ≫ qA = qB := by rw [← hq, Iso.inv_hom_id_assoc]
  have hfac : idealComapIsoHom e I ≫ I.subschemeι ≫ qA =
      ((I.comap e.inv).subschemeι ≫ qB) ≫ 𝟙 T := by
    rw [Category.comp_id, ← Category.assoc, ← idealComapIsoHom_comp_subschemeι, Category.assoc,
      hqB]
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (f := I.subschemeι ≫ qA) (IsPullback.of_horiz_isIso ⟨hfac⟩)

end IdealIso

/-! ### Families of an open of `X` over `V` are families over `S` -/

section Transport

variable {X : Over S} {V : S.Opens} {U : X.left.Opens} (hUV : U ≤ X.hom ⁻¹ᵁ V) {d : ℕ}

theorem ambientBaseIso_hom_comp_fst (T : Over V.toScheme) :
    (ambientBaseIso X V U hUV T).hom ≫
        pullback.fst (openAmbient X U).hom ((Over.map V.ι).obj T).hom =
      pullback.fst (openOverBase X V U hUV).hom T.hom :=
  (isPullback_ambientBase X V U hUV T).isoPullback_hom_fst

theorem ambientBaseIso_hom_comp_snd (T : Over V.toScheme) :
    (ambientBaseIso X V U hUV T).hom ≫
        pullback.snd (openAmbient X U).hom ((Over.map V.ι).obj T).hom =
      pullback.snd (openOverBase X V U hUV).hom T.hom :=
  (isPullback_ambientBase X V U hUV T).isoPullback_hom_snd

/-- The comparison isomorphism `U ×_V T ≅ U ×_S T` turns the structure morphism of `U ×_S T`
into the one of `U ×_V T`. -/
theorem ambientBaseIso_inv_comp_structureMorphism (T : Over V.toScheme) :
    (ambientBaseIso X V U hUV T).inv ≫
        ((Over.pullback T.hom).obj (openOverBase X V U hUV)).hom =
      ((Over.pullback ((Over.map V.ι).obj T).hom).obj (openAmbient X U)).hom := by
  rw [Iso.inv_comp_eq]
  exact (ambientBaseIso_hom_comp_structureMorphism X V U hUV T).symm

/-- **A degree-`d` Hilbert family in `U` over a `V`-scheme `T`, read as a degree-`d` Hilbert
family in `U` over `T` viewed as an `S`-scheme.** -/
def HilbertFamily.ofBase {T : Over V.toScheme}
    (W : HilbertFamily (openOverBase X V U hUV) T d) :
    HilbertFamily (openAmbient X U) ((Over.map V.ι).obj T) d where
  ideal := W.ideal.comap (ambientBaseIso X V U hUV T).inv
  isFiniteLocallyFreeOfRank :=
    haveI := W.isFiniteLocallyFreeOfRank
    isFiniteLocallyFreeOfRank_comap_of_iso _
      (ambientBaseIso_hom_comp_structureMorphism X V U hUV T) _ _

@[simp]
theorem HilbertFamily.ofBase_ideal {T : Over V.toScheme}
    (W : HilbertFamily (openOverBase X V U hUV) T d) :
    (HilbertFamily.ofBase hUV W).ideal = W.ideal.comap (ambientBaseIso X V U hUV T).inv :=
  rfl

/-- **A degree-`d` Hilbert family in `U` over `T` viewed as an `S`-scheme, read as one over `T`
as a `V`-scheme.** -/
def HilbertFamily.toBase {T : Over V.toScheme}
    (Z : HilbertFamily (openAmbient X U) ((Over.map V.ι).obj T) d) :
    HilbertFamily (openOverBase X V U hUV) T d where
  ideal := Z.ideal.comap (ambientBaseIso X V U hUV T).hom
  isFiniteLocallyFreeOfRank :=
    haveI := Z.isFiniteLocallyFreeOfRank
    isFiniteLocallyFreeOfRank_comap_of_iso (e := (ambientBaseIso X V U hUV T).symm)
      (ambientBaseIso_inv_comp_structureMorphism hUV T) _ _

@[simp]
theorem HilbertFamily.toBase_ideal {T : Over V.toScheme}
    (Z : HilbertFamily (openAmbient X U) ((Over.map V.ι).obj T) d) :
    (HilbertFamily.toBase hUV Z).ideal = Z.ideal.comap (ambientBaseIso X V U hUV T).hom :=
  rfl

/-- **Degree-`d` Hilbert families in `U` over a `V`-scheme `T` are the same thing as degree-`d`
Hilbert families in `U` over `T` viewed as an `S`-scheme.** -/
def hilbertFamilyBaseEquiv (T : Over V.toScheme) :
    HilbertFamily (openOverBase X V U hUV) T d ≃
      HilbertFamily (openAmbient X U) ((Over.map V.ι).obj T) d where
  toFun := HilbertFamily.ofBase hUV
  invFun := HilbertFamily.toBase hUV
  left_inv W := HilbertFamily.ext (comap_inv_comap_hom _ W.ideal)
  right_inv Z := HilbertFamily.ext (comap_hom_comap_inv _ Z.ideal)

/-- The comparison isomorphism `U ×_V T ≅ U ×_S T` is compatible with base change of `T`. -/
theorem ambientBaseIso_hom_comp_familyBaseChangeMap {T' T : Over V.toScheme} (g : T' ⟶ T) :
    (ambientBaseIso X V U hUV T').hom ≫
        familyBaseChangeMap (openAmbient X U) ((Over.map V.ι).map g) =
      familyBaseChangeMap (openOverBase X V U hUV) g ≫ (ambientBaseIso X V U hUV T).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, familyBaseChangeMap_comp_fst, ambientBaseIso_hom_comp_fst,
      Category.assoc, ambientBaseIso_hom_comp_fst]
    exact (familyBaseChangeMap_comp_fst _ _).symm
  · rw [Category.assoc, familyBaseChangeMap_comp_snd, ← Category.assoc,
      ambientBaseIso_hom_comp_snd, Category.assoc, ambientBaseIso_hom_comp_snd]
    exact (familyBaseChangeMap_comp_snd _ _).symm

/-- **The identification of families is natural in the base.** -/
theorem hilbertFamilyBaseEquiv_naturality {T' T : Over V.toScheme} (g : T' ⟶ T)
    (W : HilbertFamily (openOverBase X V U hUV) T d) :
    hilbertFamilyBaseEquiv hUV T' (baseChange (openOverBase X V U hUV) g W) =
      baseChange (openAmbient X U) ((Over.map V.ι).map g) (hilbertFamilyBaseEquiv hUV T W) := by
  refine HilbertFamily.ext ?_
  change (W.ideal.comap (familyBaseChangeMap (openOverBase X V U hUV) g)).comap
      (ambientBaseIso X V U hUV T').inv =
    (W.ideal.comap (ambientBaseIso X V U hUV T).inv).comap
      (familyBaseChangeMap (openAmbient X U) ((Over.map V.ι).map g))
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  refine congrArg (fun m => W.ideal.comap m) ?_
  rw [Iso.inv_comp_eq, ← Category.assoc, ambientBaseIso_hom_comp_familyBaseChangeMap,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Transport

/-! ### Extending a family of an open commutes with base change -/

/-- **Extending a family of an open `U ⊆ X` to `X` commutes with base change of the base.** The
restriction map does, by `Stacks.Hilbert.supportedInEquivOpenAmbient_naturality`, and extension
is its inverse. -/
theorem HilbertFamily.extendToAmbient_baseChange {X : Over S} {U : X.left.Opens} {d : ℕ}
    (hX : FamiliesClosedInAmbient X) {T' T : Over S} (g : T' ⟶ T)
    (W : HilbertFamily (openAmbient X U) T d) :
    HilbertFamily.extendToAmbient hX (baseChange (openAmbient X U) g W) =
      baseChange X g (HilbertFamily.extendToAmbient hX W) := by
  have hsupp := HilbertFamily.extendToAmbient_supportedIn hX W
  have hnat := supportedInEquivOpenAmbient_naturality hX U d g
    (⟨HilbertFamily.extendToAmbient hX W, hsupp⟩ : {Z : HilbertFamily X T d // Z.SupportedIn U})
  rw [supportedInEquivOpenAmbient_apply, supportedInEquivOpenAmbient_apply,
    HilbertFamily.restrictToOpenAmbient_extendToAmbient hX W] at hnat
  calc HilbertFamily.extendToAmbient hX (baseChange (openAmbient X U) g W)
      = HilbertFamily.extendToAmbient hX
          ((baseChange X g (HilbertFamily.extendToAmbient hX W)).restrictToOpenAmbient
            (hsupp.baseChange g)) := by rw [← hnat]
    _ = baseChange X g (HilbertFamily.extendToAmbient hX W) :=
        HilbertFamily.extendToAmbient_restrictToOpenAmbient hX _ _

/-- **Extending a family of an open `U ⊆ X` to `X` is injective**: restricting recovers it. -/
theorem HilbertFamily.extendToAmbient_injective {X : Over S} {U : X.left.Opens} {T : Over S}
    {d : ℕ} (hX : FamiliesClosedInAmbient X)
    {W₁ W₂ : HilbertFamily (openAmbient X U) T d}
    (h : HilbertFamily.extendToAmbient hX W₁ = HilbertFamily.extendToAmbient hX W₂) :
    W₁ = W₂ := by
  rw [← HilbertFamily.restrictToOpenAmbient_extendToAmbient hX W₁,
    ← HilbertFamily.restrictToOpenAmbient_extendToAmbient hX W₂]
  refine HilbertFamily.ext ?_
  rw [HilbertFamily.restrictToOpenAmbient_ideal, HilbertFamily.restrictToOpenAmbient_ideal]
  exact congrArg (fun Z : HilbertFamily X T d => Z.ideal.comap (openAmbientMap X U T)) h

/-! ### The charts of the criterion -/

/-- **The index of a chart in the proof of Stacks Tag 0B9A**: an affine open `V ⊆ S` together
with an affine open `U ⊆ X` lying over it.

Indexing the charts by such *pairs* is what makes the source's reduction to an affine base
unnecessary. -/
structure BaseChartIndex (X : Over S) where
  /-- An affine open of the base. -/
  V : S.Opens
  /-- The affineness of `V`. -/
  hV : IsAffineOpen V
  /-- An affine open of `X` lying over `V`. -/
  U : X.left.Opens
  /-- The affineness of `U`. -/
  hU : IsAffineOpen U
  /-- `U` lies over `V`. -/
  hUV : U ≤ X.hom ⁻¹ᵁ V

namespace BaseChartIndex

variable {X : Over S}

/-- The affine open `U` of the index, as a scheme over the affine open `V`. -/
abbrev ambient (i : BaseChartIndex X) : Over i.V.toScheme :=
  openOverBase X i.V i.U i.hUV

/-- **The representing scheme of the degree-`d` Hilbert functor of `U` over `V`**, which exists
by Stacks Tag 0B99: both `U` and `V` are affine. -/
def representingData (i : BaseChartIndex X) (d : ℕ) :
    Σ H : Over i.V.toScheme, RepresentsHilbertFunctorOfRank i.ambient H d :=
  haveI : IsAffine i.V.toScheme := i.hV
  haveI : IsAffine i.ambient.left := i.hU
  (exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine i.ambient d).some

/-- The representing scheme of the chart, as a scheme over `V`. -/
def scheme (i : BaseChartIndex X) (d : ℕ) : Over i.V.toScheme :=
  (i.representingData d).1

/-- The universal property of the representing scheme of the chart. -/
def represents (i : BaseChartIndex X) (d : ℕ) :
    RepresentsHilbertFunctorOfRank i.ambient (i.scheme d) d :=
  (i.representingData d).2

end BaseChartIndex

section Chart

variable {X : Over S} (hX : FamiliesClosedInAmbient X) (d : ℕ)
  (i : BaseChartIndex X)

/-- **The degree-`d` Hilbert family in `X` classified by a morphism of `V`-schemes into the
representing scheme of the chart**: the family of `U` it classifies, read over `S` and extended
to `X`. -/
def chartFamily {T : Scheme.{u}} {b : T ⟶ i.V.toScheme} (u : Over.mk b ⟶ i.scheme d) :
    HilbertFamily X (Over.mk (b ≫ i.V.ι)) d :=
  HilbertFamily.extendToAmbient hX
    (HilbertFamily.ofBase i.hUV ((i.represents d).family u))

/-- Precomposing the classifying morphism with a morphism of `V`-schemes base changes the
extended family. -/
private theorem extendToAmbient_ofBase_family_comp {T' T : Over i.V.toScheme} (g : T' ⟶ T)
    (u : T ⟶ i.scheme d) :
    HilbertFamily.extendToAmbient hX
        (HilbertFamily.ofBase i.hUV ((i.represents d).family (g ≫ u))) =
      baseChange X ((Over.map i.V.ι).map g)
        (HilbertFamily.extendToAmbient hX
          (HilbertFamily.ofBase i.hUV ((i.represents d).family u))) := by
  rw [show (i.represents d).family (g ≫ u) = baseChange i.ambient g ((i.represents d).family u)
      from HilbertFamily.ext ((i.represents d).naturality _ u),
    show HilbertFamily.ofBase i.hUV (baseChange i.ambient g ((i.represents d).family u)) =
      baseChange (openAmbient X i.U) ((Over.map i.V.ι).map g)
        (HilbertFamily.ofBase i.hUV ((i.represents d).family u)) from
      hilbertFamilyBaseEquiv_naturality i.hUV _ _,
    HilbertFamily.extendToAmbient_baseChange]

/-- **The family classified by a morphism into the chart is natural in the test object.** -/
theorem chartFamily_baseChange {T' T : Scheme.{u}} {b : T ⟶ i.V.toScheme}
    (u : Over.mk b ⟶ i.scheme d) (m : T' ⟶ T) :
    chartFamily hX d i ((Over.homMk m rfl : Over.mk (m ≫ b) ⟶ Over.mk b) ≫ u) =
      baseChange X (Over.homMk m (by
        change (m ≫ b) ≫ i.V.ι = m ≫ b ≫ i.V.ι
        rw [Category.assoc]) :
        Over.mk ((m ≫ b) ≫ i.V.ι) ⟶ Over.mk (b ≫ i.V.ι)) (chartFamily hX d i u) :=
  extendToAmbient_ofBase_family_comp hX d i _ u

/-- The representing scheme of the chart, as a scheme over `S`. -/
def chartOver : Over S :=
  (Over.map i.V.ι).obj (i.scheme d)

/-- **The universal family of the chart, read as a degree-`d` Hilbert family in `X`.** -/
def chartUnivFamily : HilbertFamily X (chartOver d i) d :=
  HilbertFamily.extendToAmbient hX
    (HilbertFamily.ofBase i.hUV ((i.represents d).family (𝟙 (i.scheme d))))

/-- The universal family of the chart, read as a section of the degree-`d` Hilbert functor
rather than as a `Stacks.Hilbert.HilbertFamily`. The two are the same by definition; the
spelling matters only because the dependent pairs of the total presheaf are type-correct without
unfolding the functor only in this one. -/
def chartUnivSection : (hilbertFunctorOfRank X d).obj (op (chartOver d i)) :=
  chartUnivFamily hX d i

/-- **Every family classified by the chart is a base change of its universal family.** -/
theorem chartFamily_eq_baseChange {T : Scheme.{u}} {b : T ⟶ i.V.toScheme}
    (u : Over.mk b ⟶ i.scheme d) :
    chartFamily hX d i u =
      baseChange X ((Over.map i.V.ι).map u) (chartUnivFamily hX d i) := by
  have h := extendToAmbient_ofBase_family_comp hX d i u (𝟙 (i.scheme d))
  rwa [Category.comp_id] at h

/-- **The chart of the criterion of Stacks 01JJ attached to a chart index**: the morphism from
the functor of points of the representing scheme of the degree-`d` Hilbert functor of `U` over
`V` into the total presheaf of the degree-`d` Hilbert functor of `X` over `S`, classifying the
universal family of the chart read as a family in `X`. -/
def baseChart : yoneda.obj (i.scheme d).left ⟶ totalPresheaf (hilbertFunctorOfRank X d) :=
  yonedaEquiv.symm
    (⟨(chartOver d i).hom, chartUnivSection hX d i⟩ :
      (totalPresheaf (hilbertFunctorOfRank X d)).obj (op (i.scheme d).left))

/-- The value of the chart on a morphism of schemes into its representing scheme. -/
theorem baseChart_app_left {T : Scheme.{u}} (k : T ⟶ (i.scheme d).left) :
    (baseChart hX d i).app (op T) k =
      (⟨k ≫ (chartOver d i).hom, (hilbertFunctorOfRank X d).map
        (Over.homMk k rfl : Over.mk (k ≫ (chartOver d i).hom) ⟶ chartOver d i).op
          (chartUnivSection hX d i)⟩ :
        Σ c : T ⟶ S, (hilbertFunctorOfRank X d).obj (op (Over.mk c))) := by
  rw [baseChart, yonedaEquiv_symm_app_apply]
  exact totalPresheafMap_mk (hilbertFunctorOfRank X d) k.op rfl (chartUnivSection hX d i)

/-- The family classified by a morphism into the chart, read as a section of the degree-`d`
Hilbert functor rather than as a `Stacks.Hilbert.HilbertFamily`. -/
def chartFamilySection {T : Scheme.{u}} {b : T ⟶ i.V.toScheme} (u : Over.mk b ⟶ i.scheme d) :
    (hilbertFunctorOfRank X d).obj (op (Over.mk (b ≫ i.V.ι))) :=
  chartFamily hX d i u

/-- **The value of the chart on the underlying morphism of a morphism of `V`-schemes into its
representing scheme**: the family that morphism classifies, paired with the structure morphism
of the test object. -/
theorem baseChart_app {T : Scheme.{u}} {b : T ⟶ i.V.toScheme} (u : Over.mk b ⟶ i.scheme d) :
    (baseChart hX d i).app (op T) u.left =
      (⟨b ≫ i.V.ι, chartFamilySection hX d i u⟩ :
        Σ c : T ⟶ S, (hilbertFunctorOfRank X d).obj (op (Over.mk c))) := by
  refine Eq.trans (baseChart_app_left hX d i u.left)
    (Eq.trans (totalSigmaMk_eq (F := hilbertFunctorOfRank X d) (chartUnivSection hX d i)
      (Over.homMk u.left rfl : Over.mk (u.left ≫ (chartOver d i).hom) ⟶ chartOver d i)
      ((Over.map i.V.ι).map u) rfl) ?_)
  exact congrArg (fun z => (⟨b ≫ i.V.ι, z⟩ :
    Σ c : T ⟶ S, (hilbertFunctorOfRank X d).obj (op (Over.mk c))))
    (chartFamily_eq_baseChange hX d i u).symm

/-- **The chart is injective at every test scheme.** The first components determine the
morphism to `V`, because `V ⊆ S` is a monomorphism, and the second components then determine the
classifying morphism, because extending a family, reading it over `S` and classifying it are all
injective. -/
theorem injective_baseChart_app (T : Scheme.{u}) :
    Function.Injective ((baseChart hX d i).app (op T)) := by
  intro k₁ k₂ h
  have hfst : k₁ ≫ (chartOver d i).hom = k₂ ≫ (chartOver d i).hom :=
    totalSigma_fst_eq (F := hilbertFunctorOfRank X d)
      ((baseChart_app_left hX d i k₁).symm.trans (h.trans (baseChart_app_left hX d i k₂)))
  have hb : k₂ ≫ (i.scheme d).hom = k₁ ≫ (i.scheme d).hom := by
    refine (cancel_mono i.V.ι).1 ?_
    rw [Category.assoc, Category.assoc]
    exact hfst.symm
  have hsnd : chartFamilySection hX d i
        (Over.homMk k₁ rfl : Over.mk (k₁ ≫ (i.scheme d).hom) ⟶ i.scheme d) =
      chartFamilySection hX d i
        (Over.homMk k₂ hb : Over.mk (k₁ ≫ (i.scheme d).hom) ⟶ i.scheme d) :=
    totalSigma_snd_eq (F := hilbertFunctorOfRank X d)
      ((baseChart_app hX d i
          (Over.homMk k₁ rfl : Over.mk (k₁ ≫ (i.scheme d).hom) ⟶ i.scheme d)).symm.trans
        (h.trans (baseChart_app hX d i
          (Over.homMk k₂ hb : Over.mk (k₁ ≫ (i.scheme d).hom) ⟶ i.scheme d))))
  have hfam : ((i.represents d).family
        (Over.homMk k₁ rfl : Over.mk (k₁ ≫ (i.scheme d).hom) ⟶ i.scheme d)) =
      ((i.represents d).family
        (Over.homMk k₂ hb : Over.mk (k₁ ≫ (i.scheme d).hom) ⟶ i.scheme d)) :=
    (hilbertFamilyBaseEquiv i.hUV _).injective
      (HilbertFamily.extendToAmbient_injective hX hsnd)
  have := (i.represents d).family.injective hfam
  exact congrArg (fun v : Over.mk (k₁ ≫ (i.scheme d).hom) ⟶ i.scheme d => v.left) this

/-- **The open of a test object cutting out the image of the chart**: the points whose image in
`S` lies in `V` and over which the given family is supported in `U`. -/
def chartOpens {T : Scheme.{u}} (x : (totalPresheaf (hilbertFunctorOfRank X d)).obj (op T)) :
    T.Opens :=
  (x.1 ⁻¹ᵁ i.V) ⊓ (x.2 : HilbertFamily X (Over.mk x.1) d).supportOpens i.U

/-- **The image of the chart over a test object is cut out by
`Stacks.Hilbert.chartOpens`**, which is condition (2)(b) of the criterion for this chart. -/
theorem exists_baseChart_app_iff {T : Scheme.{u}}
    (x : (totalPresheaf (hilbertFunctorOfRank X d)).obj (op T)) (T' : Scheme.{u})
    (e : T' ⟶ T) :
    (∃ k : T' ⟶ (i.scheme d).left,
        (baseChart hX d i).app (op T') k =
          (totalPresheaf (hilbertFunctorOfRank X d)).map e.op x) ↔
      ∀ t : T', e t ∈ chartOpens d i x := by
  obtain ⟨ψ, Z⟩ := x
  constructor
  · rintro ⟨k, hk⟩
    set b : T' ⟶ i.V.toScheme := k ≫ (i.scheme d).hom with hbdef
    have hfst : e ≫ ψ = b ≫ i.V.ι := by
      rw [hbdef, Category.assoc]
      exact (totalSigma_fst_eq (F := hilbertFunctorOfRank X d)
        ((baseChart_app_left hX d i k).symm.trans
          (hk.trans (totalPresheafMap_mk (hilbertFunctorOfRank X d) e.op rfl Z)))).symm
    -- the second components, compared over the base object `Over.mk (b ≫ V.ι)`
    have hsnd : chartFamilySection hX d i
          (Over.homMk k rfl : Over.mk b ⟶ i.scheme d) =
        baseChange X (Over.homMk e hfst : Over.mk (b ≫ i.V.ι) ⟶ Over.mk ψ) Z :=
      totalSigma_snd_eq (F := hilbertFunctorOfRank X d)
        ((baseChart_app hX d i (Over.homMk k rfl : Over.mk b ⟶ i.scheme d)).symm.trans
          (hk.trans (totalPresheafMap_mk (hilbertFunctorOfRank X d) e.op hfst Z)))
    have hsupp : (baseChange X (Over.homMk e hfst : Over.mk (b ≫ i.V.ι) ⟶ Over.mk ψ) Z).SupportedIn
        i.U := by
      rw [← hsnd]
      exact HilbertFamily.extendToAmbient_supportedIn hX _
    intro t
    refine ⟨?_, (Z.baseChange_supportedIn_iff _ i.U).1 hsupp t⟩
    have hmem : (e ≫ ψ) t ∈ i.V := by
      rw [hfst, Scheme.Hom.comp_apply]
      exact (Scheme.Opens.range_ι i.V).le ⟨b t, rfl⟩
    rwa [Scheme.Hom.comp_apply] at hmem
  · intro ht
    -- the base of the test object factors through `V`
    have hrange : Set.range (e ≫ ψ) ⊆ Set.range i.V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (ht t).1
    set b : T' ⟶ i.V.toScheme := IsOpenImmersion.lift i.V.ι (e ≫ ψ) hrange with hbdef
    have hfst : e ≫ ψ = b ≫ i.V.ι := (IsOpenImmersion.lift_fac _ _ hrange).symm
    set m : Over.mk (b ≫ i.V.ι) ⟶ Over.mk ψ := Over.homMk e hfst with hmdef
    have hsupp : (baseChange X m Z).SupportedIn i.U :=
      (Z.baseChange_supportedIn_iff m i.U).2 fun t => (ht t).2
    set W : HilbertFamily (openAmbient X i.U) ((Over.map i.V.ι).obj (Over.mk b)) d :=
      (baseChange X m Z).restrictToOpenAmbient hsupp with hWdef
    refine ⟨((i.represents d).family.symm (HilbertFamily.toBase i.hUV W)).left, ?_⟩
    refine Eq.trans (baseChart_app hX d i ((i.represents d).family.symm
      (HilbertFamily.toBase i.hUV W))) ?_
    refine Eq.trans ?_ (totalPresheafMap_mk (hilbertFunctorOfRank X d) e.op hfst Z).symm
    refine congrArg (fun z => (⟨b ≫ i.V.ι, z⟩ :
      Σ c : T' ⟶ S, (hilbertFunctorOfRank X d).obj (op (Over.mk c)))) ?_
    change chartFamily hX d i _ = baseChange X m Z
    rw [chartFamily, Equiv.apply_symm_apply,
      show HilbertFamily.ofBase i.hUV (HilbertFamily.toBase i.hUV W) = W from
        (hilbertFamilyBaseEquiv i.hUV (Over.mk b)).apply_symm_apply W,
      hWdef, HilbertFamily.extendToAmbient_restrictToOpenAmbient hX _ hsupp]

end Chart

/-! ### The charts cover -/

/-- A point of the base lies in the open over which a family is supported in `U` exactly when
every point of the subscheme above it maps into `U`. -/
theorem HilbertFamily.mem_supportOpens_iff {X T : Over S} {d : ℕ} (Z : HilbertFamily X T d)
    (U : X.left.Opens) (t : T.left) :
    t ∈ Z.supportOpens U ↔ ∀ z : Z.ideal.subscheme, Z.structural z = t → Z.toAmbient z ∈ U := by
  rw [HilbertFamily.mem_supportOpens]
  constructor
  · intro h z hz
    by_contra hu
    exact h ⟨z, hu, hz⟩
  · rintro h ⟨z, hu, hz⟩
    exact hu (h z hz)

/-- The image in `X` of a point of the subscheme cut out by a family lies over the image in `S`
of the point of the base below it. -/
theorem HilbertFamily.hom_toAmbient {X T : Over S} {d : ℕ} (Z : HilbertFamily X T d)
    (z : Z.ideal.subscheme) : X.hom (Z.toAmbient z) = T.hom (Z.structural z) := by
  rw [HilbertFamily.toAmbient, HilbertFamily.structural]
  simp only [← Scheme.Hom.comp_apply, Category.assoc, familyProjection_comp]

/-- **The covering condition of the criterion, in the form the charts need it**: for a
degree-`d` Hilbert family over any base and any point `t` of that base, there is an affine open
`V ⊆ S` containing the image of `t` and an affine open `U ⊆ X` *lying over `V`* over whose
support-open `t` lies.

This is `Stacks.Hilbert.exists_isAffineOpen_mem_supportOpens` with the affine open of `X` shrunk
into the preimage of `V` by prime avoidance, which is possible because the fibre of the subscheme
over `t` is finite. -/
theorem exists_isAffineOpen_le_mem_supportOpens {X : Over S} (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom.base (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    {T : Over S} (Z : HilbertFamily X T d)
    (t : T.left) {V : S.Opens} (hV : T.hom t ∈ V) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ U ≤ X.hom ⁻¹ᵁ V ∧ t ∈ Z.supportOpens U := by
  obtain ⟨U₀, hU₀, ht₀⟩ := exists_isAffineOpen_mem_supportOpens X d hX Z t
  have hEfin : (Z.toAmbient '' (Z.structural ⁻¹' {t}) : Set X.left).Finite :=
    (Z.structural.finite_preimage_singleton t).image _
  have hEU₀ : (Z.toAmbient '' (Z.structural ⁻¹' {t}) : Set X.left) ⊆ (U₀ : Set X.left) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Z.mem_supportOpens_iff U₀ t).1 ht₀ z hz
  have hEV : (Z.toAmbient '' (Z.structural ⁻¹' {t}) : Set X.left) ⊆
      ((X.hom ⁻¹ᵁ V : X.left.Opens) : Set X.left) := by
    rintro _ ⟨z, hz, rfl⟩
    change X.hom (Z.toAmbient z) ∈ V
    rw [Z.hom_toAmbient z, show Z.structural z = t from hz]
    exact hV
  obtain ⟨r, hrE, hrV⟩ := hU₀.exists_basicOpen_subset_of_finite hEfin hEU₀ (X.hom ⁻¹ᵁ V) hEV
  refine ⟨X.left.basicOpen r, hU₀.basicOpen r, hrV, ?_⟩
  rw [Z.mem_supportOpens_iff]
  intro z hz
  exact hrE ⟨z, hz, rfl⟩

section Cover

variable {X : Over S}

/-- **Every point of a test object lies in the open of some chart**, which is the covering
condition (2)(c) of the criterion of Stacks 01JJ for the family of charts. -/
theorem exists_mem_chartOpens (d : ℕ)
    (hXd : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom.base (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U)
    {T : Scheme.{u}}
    (x : (totalPresheaf (hilbertFunctorOfRank X d)).obj (op T)) (t : T) :
    ∃ i : BaseChartIndex X, t ∈ chartOpens d i x := by
  obtain ⟨ψ, Z⟩ := x
  obtain ⟨V, hV, hsV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ (ψ t))
  obtain ⟨U, hU, hUV, ht⟩ :=
    exists_isAffineOpen_le_mem_supportOpens d hXd (T := Over.mk ψ) Z t (V := V) hsV
  exact ⟨⟨V, hV, U, hU, hUV⟩, ⟨hsV, ht⟩⟩

/-- **Each chart is an open immersion of presheaves**, which is conditions (2)(a) and (2)(b) of
the criterion of Stacks 01JJ: the source is representable by Stacks 0B99 and the image over a
test object is cut out by `Stacks.Hilbert.chartOpens`. -/
theorem isOpenImmersion_presheaf_baseChart (hX : FamiliesClosedInAmbient X) (d : ℕ)
    (i : BaseChartIndex X) :
    IsOpenImmersion.presheaf (baseChart hX d i) :=
  Stacks.Morphisms.openImmersion_presheaf_of_opens _
    (fun T => injective_baseChart_app hX d i T.unop) (fun _ x => chartOpens d i x)
    (fun _ x T' e => exists_baseChart_app_iff hX d i x T' e)

/-- **The charts are jointly locally surjective for the Zariski topology.** -/
theorem locallySurjective_baseChart (hX : FamiliesClosedInAmbient X) (d : ℕ)
    (hXd : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom.base (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology.{u}
      (Sigma.desc (baseChart hX d)) := by
  classical
  constructor
  intro T x
  let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers (BaseChartIndex X)
    (fun i => (chartOpens d i x).toScheme)
    (fun i => (chartOpens d i x).ι)
    (by
      intro t
      obtain ⟨i, hi⟩ := exists_mem_chartOpens d hXd x t
      exact ⟨i, ⟨t, hi⟩, rfl⟩)
  refine Scheme.zariskiTopology.superset_covering ?_ 𝒰.mem_grothendieckTopology
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro - - ⟨i⟩
  obtain ⟨k, hk⟩ := (exists_baseChart_app_iff hX d i x (chartOpens d i x).toScheme
    (chartOpens d i x).ι).2 fun t => t.property
  refine ⟨(Sigma.ι (fun i : BaseChartIndex X => yoneda.obj (i.scheme d).left) i).app _ k, ?_⟩
  have hc := congrArg
    (fun m : yoneda.obj ((BaseChartIndex.scheme i d).left) ⟶
        totalPresheaf (hilbertFunctorOfRank X d) =>
      m.app (op (chartOpens d i x).toScheme) k)
    (Sigma.ι_comp_desc (baseChart hX d) i)
  exact hc.trans hk

end Cover

/-! ### Representability -/

/-- **The degree-`d` Hilbert functor of points of `X` over `S` is representable by a scheme over
`S`**, provided

* every degree-`d` Hilbert family in an open of `X` cuts out a *closed* subscheme of `X ×_S T`,
  which is the content of the footnote to the proof of Stacks Tag 0B9A
  (`Stacks.Hilbert.FamiliesClosedInAmbient`), and
* every `d`-tuple of points of a single fibre of `X ⟶ S` lies in an affine open of `X`, which is
  the hypothesis Stacks Tag 0B9A states.

This is the gluing assembly of Tag 0B9A, with the two things the source's proof needs of
`X ⟶ S` taken as hypotheses so that each way of meeting them is a one-step corollary. The four
conditions of the criterion of Stacks 01JJ are supplied for the charts indexed by a pair of an
affine open `V ⊆ S` and an affine open `U ⊆ X` lying over it: condition (1) is
`Stacks.Hilbert.isSheaf_zariskiTopology_totalPresheaf_hilbertFunctorOfRank`, conditions (2)(a)
and (2)(b) are `Stacks.Hilbert.isOpenImmersion_presheaf_baseChart` — the representability of the
chart being Stacks 0B99 for the affine `U` over the affine `V`, through the identification of
the subfunctor of families supported in `U` with the Hilbert functor of `U` — and condition
(2)(c) is `Stacks.Hilbert.locallySurjective_baseChart`. Indexing the charts by pairs is what
makes the source's reduction to an affine base unnecessary.

The proposition of Tag 0B9A itself, under the hypothesis the tag states and for every `d ≠ 1`,
where the tag holds, is
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`
in `StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`, which is where
the `@[stacks 0B9A]` attribute lives; **no declaration in this file carries it**, each being one
of the inputs to that proposition rather than the proposition. -/
theorem nonempty_representsHilbertFunctorOfRank_of_familiesClosedInAmbient {X : Over S}
    (hX : FamiliesClosedInAmbient X) (d : ℕ)
    (hXd : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom.base (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  let : Presheaf.IsLocallySurjective Scheme.zariskiTopology.{u}
      (Sigma.desc (baseChart hX d)) := locallySurjective_baseChart hX d hXd
  have hrep : (totalPresheaf (hilbertFunctorOfRank X d)).IsRepresentable :=
    Scheme.LocalRepresentability.isRepresentable
      (F := ⟨totalPresheaf (hilbertFunctorOfRank X d),
        (isSheaf_iff_isSheaf_of_type _ _).2
          (isSheaf_zariskiTopology_totalPresheaf_hilbertFunctorOfRank X d)⟩)
      (f := baseChart hX d)
      (isOpenImmersion_presheaf_baseChart hX d)
  obtain ⟨W, ⟨R⟩⟩ := hrep.has_representation
  exact representsHilbertFunctorOfRank_of_representableBy _ d R

/-- **The degree-`d` Hilbert functor of points of `X` over `S` is representable by a scheme over
`S`, provided every finite set of points of `X` lying in a single fibre of `X ⟶ S` is contained
in an affine open of `X`.**

This is the proposition of Stacks Tag 0B9A under the *set* form
`AlgebraicGeometry.HasAffineFinitePointsInFibres` of its fibrewise affineness hypothesis, which
is the form all seven cases of Stacks Tag 0B9B establish. That form is strictly stronger than
the `d`-tuple form the tag states — it is what the footnote to the source's proof consumes — so
**no declaration in this file carries the `@[stacks 0B9A]` attribute**; the tag is registered on
`Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_ne_one`
in `StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`. -/
theorem nonempty_representsHilbertFunctorOfRank_of_hasAffineFinitePointsInFibres {X : Over S}
    (hX : HasAffineFinitePointsInFibres X.hom) (d : ℕ) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) :=
  nonempty_representsHilbertFunctorOfRank_of_familiesClosedInAmbient
    (familiesClosedInAmbient_of_hasAffineFinitePointsInFibres hX) d
    (Stacks.HilbertFibreAffineOpen.exists_isAffineOpen_forall_mem_of_hasAffineFinitePointsInFibres
      hX d)

end Stacks.Hilbert

end
