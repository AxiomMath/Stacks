module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf

/-!
# The affine-over-affine subsite of the small crystalline site is cover-dense

Fix a global crystalline situation `(p, (S, I, γ), X)`.  An object `(U, T, δ)` of the small
crystalline site `Cris(X/S)` of [Stacks, Tag 07IG] comes with a structure morphism `T ⟶ S`, and
the divided power differentials of `T` relative to `S` are computed by the algebra — by the
divided power envelope of a presentation, [Stacks, Tag 07MF] — only when one is allowed to work
with *rings*: when `T` is affine **and** the structure morphism lands in an affine open of `S`,
so that both `Γ(T, 𝒪_T)` and the ring of the affine open of `S` over which it is an algebra are
available.

This file cuts out the full subcategory of those objects and proves it **cover-dense** in
`Cris(X/S)`.  Cover-density, together with fullness, is exactly the hypothesis of Mathlib's
`CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom`: a morphism from an arbitrary presheaf
on `Cris(X/S)` into a *sheaf* on `Cris(X/S)` may be given on the affine-over-affine objects
alone, and is determined by its values there.  That is the comparison lemma of
[Stacks, Tag 00XK] in the only form the differentials need it.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `IsAffineOverAffineObject` — the property cutting out the subcategory: the ambient divided
  power scheme `T` is affine, and the structure morphism `T ⟶ S` factors through an affine open
  of `S`, in the form `⊤ ≤ (T ⟶ S)⁻¹ V` for some affine open `V` of `S`.
* `AffineOverAffineCrystallineThickening` — the objects with that property, the full subcategory
  of `Cris(X/S)` they span, and `affineOverAffineι` the inclusion into `Cris(X/S)`, with
  `fullyFaithfulAffineOverAffineι` its full faithfulness.
* `AffineOverAffineCrystallineThickening.restrictOpen` — the restriction of an object of
  `Cris(X/S)` to an affine open of its ambient scheme lying over an affine open of `S`, which is
  an affine-over-affine object, with `restrictOpenHom` the structure morphism of that restriction
  as a morphism of `Cris(X/S)`.
* `restrictHomEquivHomOfCoefficients`, and its specialisations `restrictHomEquivHom` to abelian
  groups and `restrictHomEquivHomTypes` to sets — restriction along the inclusion is a bijection
  from the morphisms of a presheaf into a sheaf to the morphisms of their restrictions.

## Main results

* `CrystallineThickening.top_le_preimage_restrictOpen` — the structure morphism of the
  restriction of an object to an open `W` of its ambient scheme factors through an open `V` of
  `S` as soon as `W` does; this is the one point at which the new condition has to be checked.
* `CrystallineThickening.exists_isAffineOpen_over_isAffineOpen` — around every point of the
  ambient scheme of an object of `Cris(X/S)` there is an affine open lying over an affine open of
  `S`: the affine opens of `S` are a basis, and so are the affine opens of the preimage of one of
  them.
* `affineOverAffineι_isCoverDense` — **the affine-over-affine objects are cover-dense in
  `Cris(X/S)`**: the restrictions produced by the previous result cover every object.
* `sheafHom_restrict_eq`, `sheafHom_restrict_eq_types` — the morphism produced by
  `restrictHomEquivHom` restricts to the given one.
* `hom_ext_of_whiskerLeft`, `hom_ext_of_app` — **two morphisms from a presheaf on `Cris(X/S)`
  into a sheaf on `Cris(X/S)` that agree on the affine-over-affine objects are equal.**
* `AffineOverAffineCrystallineThickening.exists_isAffineOpen_top_le_preimage` — the three data
  `IsAffineOpen ⊤`, `IsAffineOpen V`, `⊤ ≤ (T ⟶ S)⁻¹ V` carried by an affine-over-affine object,
  in exactly the shape of the hypotheses `hW : IsAffineOpen W`, `h : W ≤ A.toBase.hom ⁻¹ᵁ V` and
  `hV : IsAffineOpen V` of `Crystalline.GlobalCrystallineSituation.bijective_restrictedToSheaf_app`
  with `W = ⊤`.

## Implementation notes

The subcategory is `CategoryTheory.ObjectProperty.FullSubcategory` of `CrystallineThickening S`,
which is itself a full subcategory of `CRIS(X/S)`; an object therefore carries its underlying
object of `Cris(X/S)` in the field `obj` and that one its underlying object of `CRIS(X/S)` in
`obj.obj`.  `Full` and `Faithful` for the inclusion are the generic instances for
`CategoryTheory.ObjectProperty.ι`, and fullness is what supplies Mathlib's
`CategoryTheory.Functor.IsLocallyFull.of_full`, the second hypothesis of
`CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom`.

The condition over `S` is phrased as `⊤ ≤ A.obj.toBase.hom ⁻¹ᵁ V` rather than as a factorisation
of the structure morphism through the open immersion `V ⟶ S`. This is the form of the hypothesis
of `Crystalline.GlobalCrystallineSituation.baseSections` and of
`Crystalline.GlobalCrystallineSituation.bijective_restrictedToSheaf_app`, and it is stable under
passing to a smaller open on the left with no comparison morphism to carry along.

Cover-density is proved exactly as for the subsite of affine objects
(`Crystalline.GlobalCrystallineSituation.SmallSite.affineι_isCoverDense`), with one extra step:
around a point `t` of the ambient scheme `T` one first picks an affine open `V` of `S` containing
the image of `t`, and only then an affine open `W` of `T` containing `t` and contained in the
*open* `(T ⟶ S)⁻¹ V`, both times because affine opens form a basis
(`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset`). The restrictions of the object to these
`W` are affine-over-affine, they form a Zariski covering family of `Cris(X/S)`, and each of them
factors through the inclusion, so `CategoryTheory.Sieve.coverByImage` of the inclusion contains a
covering sieve. As in the affine case the refinement is indexed by the points of `T`, lifted to the
universe `u + 1` over which a covering family of the crystalline site is indexed.

No tag attribute is placed in this file: the subsite itself is not a statement of the source, and
the comparison lemma [Stacks, Tag 00XK] that cover-density feeds is Mathlib's.

## References

* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 07IH](https://stacks.math.columbia.edu/tag/07IH)
* [Stacks Project, Tag 00XK](https://stacks.math.columbia.edu/tag/00XK)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- The property cutting out the affine-over-affine subsite of `Cris(X/S)`: the ambient divided
power scheme `T` of an object `(U, T, δ)` is affine, and its structure morphism `T ⟶ S` factors
through an affine open `V` of `S`, in the form `⊤ ≤ (T ⟶ S)⁻¹ V`. -/
abbrev IsAffineOverAffineObject : ObjectProperty (CrystallineThickening S) := fun A ↦
  IsAffine A.obj.thickening.target.scheme ∧
    ∃ V : S.S.scheme.Opens, IsAffineOpen V ∧
      (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V

/-- **The affine-over-affine subsite of the small crystalline site**: the full subcategory of
`Cris(X/S)` on the objects `(U, T, δ)` with `T` affine and lying over an affine open of `S`. -/
abbrev AffineOverAffineCrystallineThickening (S : GlobalCrystallineSituation.{u}) :=
  (IsAffineOverAffineObject S).FullSubcategory

/-- The inclusion of the affine-over-affine subsite into the small crystalline site. -/
abbrev affineOverAffineι :
    AffineOverAffineCrystallineThickening S ⥤ CrystallineThickening S :=
  (IsAffineOverAffineObject S).ι

/-- The inclusion of the affine-over-affine subsite is fully faithful, being the inclusion of a
full subcategory. -/
abbrev fullyFaithfulAffineOverAffineι : (affineOverAffineι S).FullyFaithful :=
  (IsAffineOverAffineObject S).fullyFaithfulι

/-- The inclusion of the affine-over-affine subsite is full. -/
instance full_affineOverAffineι : (affineOverAffineι S).Full :=
  (fullyFaithfulAffineOverAffineι S).full

/-- The inclusion of the affine-over-affine subsite is faithful. -/
instance faithful_affineOverAffineι : (affineOverAffineι S).Faithful :=
  (fullyFaithfulAffineOverAffineι S).faithful

variable {S}

namespace CrystallineThickening

/-- **The structure morphism of the restriction of an object of `Cris(X/S)` to an open `W` of its
ambient scheme factors through an open `V` of `S` as soon as `W` does.**  The ambient scheme of
the restriction is `W` and its structure morphism is the open immersion of `W` followed by the
structure morphism of the object, so the condition on the whole of `W` is the original condition
read at the points of `W`. -/
theorem top_le_preimage_restrictOpen (A : CrystallineThickening S)
    (W : A.obj.thickening.target.scheme.Opens) {V : S.S.scheme.Opens}
    (h : W ≤ A.obj.toBase.hom ⁻¹ᵁ V) :
    (⊤ : (A.restrictOpen W).obj.thickening.target.scheme.Opens) ≤
      (A.restrictOpen W).obj.toBase.hom ⁻¹ᵁ V := by
  intro x _
  exact h x.2

/-- **Around every point of the ambient scheme of an object of `Cris(X/S)` there is an affine open
lying over an affine open of the divided power base.**  Choose first an affine open `V` of `S`
around the image of the point, the affine opens of `S` being a basis; then an affine open `W`
around the point inside the open `(T ⟶ S)⁻¹ V`, the affine opens of `T` being a basis too. -/
theorem exists_isAffineOpen_over_isAffineOpen (A : CrystallineThickening S)
    (t : A.obj.thickening.target.scheme) :
    ∃ (W : A.obj.thickening.target.scheme.Opens) (V : S.S.scheme.Opens),
      IsAffineOpen W ∧ t ∈ W ∧ IsAffineOpen V ∧ W ≤ A.obj.toBase.hom ⁻¹ᵁ V := by
  obtain ⟨V, hV, htV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := A.obj.toBase.hom.base t) (U := ⊤) trivial
  obtain ⟨W, hW, htW, hWV⟩ :=
    exists_isAffineOpen_mem_and_subset (x := t) (U := A.obj.toBase.hom ⁻¹ᵁ V) htV
  exact ⟨W, V, hW, htW, hV, hWV⟩

end CrystallineThickening

namespace AffineOverAffineCrystallineThickening

/-- **The restriction of an object of `Cris(X/S)` to an affine open of its ambient scheme lying
over an affine open of the divided power base is an affine-over-affine object.**  Its ambient
scheme is that affine open, and its structure morphism factors through the same affine open of
`S` by `CrystallineThickening.top_le_preimage_restrictOpen`. -/
noncomputable def restrictOpen (A : CrystallineThickening S)
    {W : A.obj.thickening.target.scheme.Opens} (hW : IsAffineOpen W)
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V) (h : W ≤ A.obj.toBase.hom ⁻¹ᵁ V) :
    AffineOverAffineCrystallineThickening S :=
  ⟨A.restrictOpen W, hW, V, hV, CrystallineThickening.top_le_preimage_restrictOpen A W h⟩

/-- The underlying object of `Cris(X/S)` of `restrictOpen A hW hV h` is the restriction
`A.restrictOpen W`. -/
@[simp]
theorem restrictOpen_obj (A : CrystallineThickening S)
    {W : A.obj.thickening.target.scheme.Opens} (hW : IsAffineOpen W)
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V) (h : W ≤ A.obj.toBase.hom ⁻¹ᵁ V) :
    (restrictOpen A hW hV h).obj = A.restrictOpen W := rfl

/-- The structure morphism of `AffineOverAffineCrystallineThickening.restrictOpen`, as a morphism
of `Cris(X/S)` out of the image of the inclusion of the affine-over-affine subsite. -/
noncomputable def restrictOpenHom (A : CrystallineThickening S)
    {W : A.obj.thickening.target.scheme.Opens} (hW : IsAffineOpen W)
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V) (h : W ≤ A.obj.toBase.hom ⁻¹ᵁ V) :
    (affineOverAffineι S).obj (restrictOpen A hW hV h) ⟶ A :=
  A.restrictOpenHom W

/-- The morphism `restrictOpenHom A hW hV h` is the structure morphism `A.restrictOpenHom W` of the
restriction of `A` to `W`. -/
@[simp]
theorem restrictOpenHom_eq (A : CrystallineThickening S)
    {W : A.obj.thickening.target.scheme.Opens} (hW : IsAffineOpen W)
    {V : S.S.scheme.Opens} (hV : IsAffineOpen V) (h : W ≤ A.obj.toBase.hom ⁻¹ᵁ V) :
    restrictOpenHom A hW hV h = A.restrictOpenHom W := rfl

/-- **The data an affine-over-affine object supplies to the computation of its divided power
differentials**: an affine open `V` of the divided power base, the affineness of the whole of the
ambient scheme as an open of itself, and the factorisation of the structure morphism through `V`.
These are the hypotheses `(hW : IsAffineOpen W) (h : W ≤ A.toBase.hom ⁻¹ᵁ V) (hV : IsAffineOpen V)`
of `Crystalline.GlobalCrystallineSituation.bijective_restrictedToSheaf_app`, at `W = ⊤`. -/
theorem exists_isAffineOpen_top_le_preimage (A : AffineOverAffineCrystallineThickening S) :
    ∃ V : S.S.scheme.Opens, IsAffineOpen V ∧
      IsAffineOpen (⊤ : A.obj.obj.thickening.target.scheme.Opens) ∧
      (⊤ : A.obj.obj.thickening.target.scheme.Opens) ≤ A.obj.obj.toBase.hom ⁻¹ᵁ V := by
  obtain ⟨hT, V, hV, hle⟩ := A.property
  have : IsAffine A.obj.obj.thickening.target.scheme := hT
  exact ⟨V, hV, isAffineOpen_top _, hle⟩

end AffineOverAffineCrystallineThickening

/-- **The affine-over-affine objects are cover-dense in `Cris(X/S)`**: the morphisms out of
objects whose ambient scheme is affine and lies over an affine open of the divided power base
generate a covering sieve of every object of `Cris(X/S)`.

Around each point of the ambient scheme `T` of an object there is, by
`CrystallineThickening.exists_isAffineOpen_over_isAffineOpen`, an affine open of `T` lying over an
affine open of `S`; the restrictions of the object to these opens are affine-over-affine objects
and they cover it. -/
theorem affineOverAffineι_isCoverDense (S : GlobalCrystallineSituation.{u}) :
    (affineOverAffineι S).IsCoverDense (smallTopology S) := by
  classical
  refine ⟨fun B ↦ ?_⟩
  choose W V hW htW hV hWV using
    CrystallineThickening.exists_isAffineOpen_over_isAffineOpen B
  set U : ULift.{u + 1} B.obj.thickening.target.scheme →
    B.obj.thickening.target.scheme.Opens := fun t ↦ W t.down
  have hcov : ∀ t : B.obj.thickening.target.scheme, ∃ i, t ∈ U i :=
    fun t ↦ ⟨ULift.up t, htW t⟩
  refine (smallTopology S).superset_covering ?_
    (smallZariskiCovering_mem_smallTopology S _
      (CrystallineThickening.isZariskiCovering_restrictOpenCover B U hcov))
  rw [Sieve.generate_le_iff]
  rintro Z k ⟨i⟩
  exact Presieve.in_coverByImage (affineOverAffineι S)
    (AffineOverAffineCrystallineThickening.restrictOpenHom B (hW i.down) (hV i.down)
      (hWV i.down))

/-- Cover-density of the inclusion of the affine-over-affine subsite, as an instance. -/
instance instIsCoverDenseAffineOverAffineι (S : GlobalCrystallineSituation.{u}) :
    (affineOverAffineι S).IsCoverDense (smallTopology S) :=
  affineOverAffineι_isCoverDense S

section Restriction

variable (S) {A : Type*} [Category* A]

/-- **Restriction along the inclusion of the affine-over-affine subsite is a bijection from the
morphisms of a presheaf on `Cris(X/S)` into a sheaf on `Cris(X/S)` to the morphisms of their
restrictions to the subsite**, for arbitrary coefficients.  This is Mathlib's
`CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom` for the cover-dense and full inclusion
`affineOverAffineι`: a morphism into a sheaf may be given on the affine-over-affine objects
alone. -/
noncomputable def restrictHomEquivHomOfCoefficients
    (P : (CrystallineThickening S)ᵒᵖ ⥤ A) (F : Sheaf (smallTopology S) A) :
    ((affineOverAffineι S).op ⋙ P ⟶ (affineOverAffineι S).op ⋙ F.obj) ≃ (P ⟶ F.obj) :=
  Functor.IsCoverDense.restrictHomEquivHom (G := affineOverAffineι S) (K := smallTopology S)
    (ℱ := P) (ℱ' := F)

/-- **The morphism of presheaves produced by `restrictHomEquivHomOfCoefficients` restricts to the
given morphism on the affine-over-affine subsite.** -/
theorem whiskerLeft_restrictHomEquivHomOfCoefficients
    {P : (CrystallineThickening S)ᵒᵖ ⥤ A} {F : Sheaf (smallTopology S) A}
    (α : (affineOverAffineι S).op ⋙ P ⟶ (affineOverAffineι S).op ⋙ F.obj) :
    Functor.whiskerLeft (affineOverAffineι S).op (restrictHomEquivHomOfCoefficients S P F α) = α :=
  (restrictHomEquivHomOfCoefficients S P F).symm_apply_apply α

/-- **Two morphisms from a presheaf on `Cris(X/S)` into a sheaf on `Cris(X/S)` whose restrictions
to the affine-over-affine subsite agree are equal.** -/
theorem hom_ext_of_whiskerLeft {P : (CrystallineThickening S)ᵒᵖ ⥤ A}
    {F : Sheaf (smallTopology S) A} {f g : P ⟶ F.obj}
    (h : Functor.whiskerLeft (affineOverAffineι S).op f =
      Functor.whiskerLeft (affineOverAffineι S).op g) :
    f = g :=
  (restrictHomEquivHomOfCoefficients S P F).symm.injective h

/-- **Two morphisms from a presheaf on `Cris(X/S)` into a sheaf on `Cris(X/S)` that agree on every
affine-over-affine object are equal.** -/
theorem hom_ext_of_app {P : (CrystallineThickening S)ᵒᵖ ⥤ A}
    {F : Sheaf (smallTopology S) A} {f g : P ⟶ F.obj}
    (h : ∀ B : AffineOverAffineCrystallineThickening S,
      f.app (op ((affineOverAffineι S).obj B)) = g.app (op ((affineOverAffineι S).obj B))) :
    f = g :=
  hom_ext_of_whiskerLeft S (NatTrans.ext (funext fun B ↦ h B.unop))

/-- **Restriction to the affine-over-affine subsite is a bijection on morphisms into an abelian
sheaf**, at the coefficient universe `u + 1` at which the cohomology of `Cris(X/S)` is defined. -/
noncomputable def restrictHomEquivHom
    (P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :
    ((affineOverAffineι S).op ⋙ P ⟶ (affineOverAffineι S).op ⋙ F.obj) ≃ (P ⟶ F.obj) :=
  restrictHomEquivHomOfCoefficients S P F

/-- **The morphism of presheaves of abelian groups produced by `restrictHomEquivHom` restricts to
the given morphism on the affine-over-affine subsite.** -/
theorem sheafHom_restrict_eq
    {P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (α : (affineOverAffineι S).op ⋙ P ⟶ (affineOverAffineι S).op ⋙ F.obj) :
    Functor.whiskerLeft (affineOverAffineι S).op (restrictHomEquivHom S P F α) = α :=
  whiskerLeft_restrictHomEquivHomOfCoefficients S α

/-- **Restriction to the affine-over-affine subsite is a bijection on morphisms into a sheaf of
sets**, the coefficients of the crystalline topos `(X/S)_cris`. -/
noncomputable def restrictHomEquivHomTypes
    (P : (CrystallineThickening S)ᵒᵖ ⥤ Type (u + 1)) (F : smallTopos S) :
    ((affineOverAffineι S).op ⋙ P ⟶ (affineOverAffineι S).op ⋙ F.obj) ≃ (P ⟶ F.obj) :=
  restrictHomEquivHomOfCoefficients S P F

/-- **The morphism of presheaves of sets produced by `restrictHomEquivHomTypes` restricts to the
given morphism on the affine-over-affine subsite.** -/
theorem sheafHom_restrict_eq_types {P : (CrystallineThickening S)ᵒᵖ ⥤ Type (u + 1)}
    {F : smallTopos S}
    (α : (affineOverAffineι S).op ⋙ P ⟶ (affineOverAffineι S).op ⋙ F.obj) :
    Functor.whiskerLeft (affineOverAffineι S).op (restrictHomEquivHomTypes S P F α) = α :=
  whiskerLeft_restrictHomEquivHomOfCoefficients S α

end Restriction

end Crystalline.GlobalCrystallineSituation.SmallSite

end
