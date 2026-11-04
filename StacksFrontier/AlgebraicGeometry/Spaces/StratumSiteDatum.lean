module

public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratificationFpqc
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.StratumFibreBound

/-!
# The stratification of Tag 086T read over the field-valued datum of Tag 03JL

Tag 086T states its stratification by an *iff* indexed by the field-valued points of an
algebraic space, in the shape `AlgebraicGeometry.Space.FieldValuedPoint`, whose underlying
scheme is the spectrum of a field *on the nose*. Tag 03JL, the universally bounded fibres which
the proof of Tag 086U feeds to Tag 03JI, quantifies instead over an arbitrary object `T` of the
big fppf site over `S` together with an isomorphism of `(BigFppfOver.toScheme B S hS).obj T`
with a field spectrum. The two data are not interchangeable by substitution, and nothing in
this repository converted one into the other; so the conclusion of Tag 086T could not be fed
to `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_restrict_of_not_presheafFibreDegreeGe`,
which is the step of the proof of Tag 086U between its appeal to Tag 086T and its appeal to
Tag 03JI.

This file supplies the conversion and restates Tag 086T over the converted datum, for an affine
étale chart. Nothing here is a Stacks tag of its own.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_fieldValuedPoint_comp_eq`: an object `T` of the site with an
  isomorphism `e` of its underlying scheme with `Spec k`, together with a section `ξ` of a
  presheaf `X` over `T`, determines a field-valued point of `X` with field `k` and an
  isomorphism of `T` with its site object carrying `ξ` to its section.
* `AlgebraicGeometry.Space.presheafFibreProperty_iff_of_precomp_iso`: the presheaf form of a
  morphism property of schemes, read on the fibre product of a relatively representable
  morphism along a morphism from a representable presheaf, is unchanged when that morphism is
  precomposed with an isomorphism of the representing object.
* `AlgebraicGeometry.Space.exists_antitone_openSubspaces_iff_fibreDegree_ge_siteDatum_of_h086R`:
  Tag 086T for an affine étale chart, with its iff stated over the datum of Tag 03JL and with
  its four morphism hypotheses discharged, carrying Tag 086R alone.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_restrict_of_forall_not_factorsThrough`:
  if no field-valued point of `X` factors through an open subspace whose points are exactly
  those whose fibre has degree at least `n + 1`, then the chart restricted along an open
  immersion of the site has universally bounded fibres, with bound `n`.

## Implementation notes

**Why the conversion is cheap, and where its content sits.** A field-valued point of `X`
records a field `k`, a proof that `Spec k` lies in the chosen big fppf site, a structure
morphism `Spec k ⟶ S` and a section of `X` over the resulting object of the site. Given `T` and
`e`, the structure morphism is `e.inv` composed with that of `T` and the section is transported
along the induced isomorphism of site objects; the one thing that has to be proved is that
`Spec k` lies in the site, that is that its `AlgebraicGeometry.Scheme.size` is below the site's
cutoff. That is `AlgebraicGeometry.Scheme.size_congr`, the invariance of size under
isomorphism, applied to `e` and to the size bound carried by the object `T` itself. No new
cutoff has to be produced and no cardinal arithmetic is done.

**Why the two readings of the fibre-degree disjunction agree.** The conversion produces the
field-valued point only up to an isomorphism `ε` of site objects, so `ξ` is not the section of
the point but its restriction along `ε`. Both sides of the iff of Tag 086T have therefore to be
transported along `ε`. On the left this is composition with `yoneda.map ε.hom` and its inverse.
On the right it is `AlgebraicGeometry.Space.presheafFibreProperty_iff_of_precomp_iso`, whose
proof is `AlgebraicGeometry.Space.presheafFibreProperty_iff_schemeFibreProperty` on both sides
followed by the observation that the two represented fibres differ by an isomorphism of arrows:
the square representing the fibre over `ε.hom ≫ ξ` and the square representing the fibre over
`ξ` with its right-hand leg composed with `ε` are two pullbacks of one cospan.

**The four morphism hypotheses of Tag 086T are free for an affine étale chart.** They are
flatness, local finite presentation, separatedness and local quasi-finiteness, and all four are
proved consequences of étaleness: `AlgebraicGeometry.Space.isFlat_of_isEtale`,
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isEtale`,
`AlgebraicGeometry.Space.isSeparated_of_isEtale_of_isAffine` — which is where affineness of the
chart is used, an affine scheme being separated — and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isEtale`. The hypothesis under which Tag 03JI
and Tag 086U present a chart is the presheaf form of étaleness rather than
`AlgebraicGeometry.Space.IsEtale`, and the two are reconciled by
`AlgebraicGeometry.Space.isEtale_of_presheaf_etale`.

**What is still owed.** `h086R` is Tag 086R, More on Morphisms Lemma 37.45.5, which has no
occurrence of any kind in either Lean tree; discharging it discharges Tag 086T and these
statements with no further work. Beyond that, the hypothesis `hchart` of Tag 03JI remains
unproved, so Tag 086U does not follow from what is here; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus` and of
`StacksFrontier.AlgebraicGeometry.Spaces.ReasonableDenseSchematicLocus`.

**On the hypothesis `hempty` of the last result.** It is not vacuous and it is not stronger
than a degree bound: through the iff of the preceding result it says exactly that no
field-valued fibre of the chart has degree at least `n + 1`, which is the hypothesis of
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_restrict_of_not_presheafFibreDegreeGe`,
and `AlgebraicGeometry.Space.not_presheafFibreDegreeGe_of_rank_le` derives that hypothesis from
the positive fact that the fibre is finite locally free of a rank at most `n`.

## References

* [Stacks Project, Tag 086U](https://stacks.math.columbia.edu/tag/086U)
* [Stacks Project, Tag 086T](https://stacks.math.columbia.edu/tag/086T)
* [Stacks Project, Tag 086R](https://stacks.math.columbia.edu/tag/086R)
* [Stacks Project, Tag 03JI](https://stacks.math.columbia.edu/tag/03JI)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The field-valued point determined by a site object with a field spectrum -/

/-- **From the datum of Tag 03JL to the datum of Tag 086T.** Let `T` be an object of the big
fppf category over `S` whose underlying scheme is isomorphic, by `e`, to the spectrum of a field
`k`, and let `ξ` be a section of a presheaf `X` over `T`. Then there is a field-valued point `p`
of `X` with field `k`, together with an isomorphism `ε` of `T` with the object of the site
determined by `p`, such that `ξ` is the restriction of the section of `p` along `ε`.

Tag 03JL quantifies over the datum `(k, T, e)`, whereas Tag 086T quantifies over
`AlgebraicGeometry.Space.FieldValuedPoint`, whose underlying scheme is `Spec k` on the nose;
this is the passage from the first to the second, and it is what lets the conclusion of
Tag 086T be read as a statement about the fibres which Tag 03JL bounds.

The only thing proved here is that `Spec k` lies in the chosen site, that is that its size is
below the site's cutoff: the object `T` carries that bound for its own underlying scheme, and
`AlgebraicGeometry.Scheme.size_congr` transports it along `e`. Everything else is the
isomorphism of objects of the slice induced by `e` and the functoriality of `X`. -/
theorem exists_fieldValuedPoint_comp_eq
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : Type u} [Field k]
    (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
    (ξ : yoneda.obj T ⟶ X) :
    ∃ (p : FieldValuedPoint B S hS X)
      (ε : T ≅ FieldValuedPoint.siteObject B S hS X p),
      yoneda.map ε.hom ≫ yonedaEquiv.symm p.value = ξ := by
  have hk : B.Contains (Spec (CommRingCat.of k)) := by
    unfold BigFppfSite.Contains
    rw [← Scheme.size_congr e]
    exact T.left.property
  set eB : T.left ≅ B.obj hk :=
    { hom := ⟨e.hom⟩, inv := ⟨e.inv⟩,
      hom_inv_id := by ext; exact e.hom_inv_id,
      inv_hom_id := by ext; exact e.inv_hom_id }
  set A : BigFppfOver B S hS :=
    Over.mk (⟨e.inv ≫ T.hom.hom⟩ : B.obj hk ⟶ B.obj hS)
  have hw : eB.hom ≫ A.hom = T.hom := by
    ext
    show e.hom ≫ e.inv ≫ T.hom.hom = T.hom.hom
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  set ε : T ≅ A := Over.isoMk eB hw
  refine ⟨{ carrier := k, contained := hk, toBase := e.inv ≫ T.hom.hom,
            value := X.map ε.inv.op (yonedaEquiv ξ) }, ε, ?_⟩
  rw [yonedaEquiv_symm_map, Equiv.symm_apply_apply]
  exact (yoneda.mapIso ε).hom_inv_id_assoc ξ

/-! ### Transporting a fibre property along an isomorphism of the indexing object -/

/-- **A fibre property is unchanged by an isomorphism of the object indexing the fibre.** Let
`f : h_V ⟶ X` be a relatively representable morphism of presheaves on the big fppf category
over `S`, let `a : h_A ⟶ X` be a morphism from a representable presheaf and let `i : A' ≅ A` be
an isomorphism of the site. Then a morphism property `P` of schemes which respects isomorphisms
and is stable under base change holds, in its presheaf form, of the fibre product of `f` along
`yoneda.map i.hom ≫ a` exactly when it holds of the fibre product of `f` along `a`.

This is what transports the right-hand side of the iff of Tag 086T along the isomorphism which
`AlgebraicGeometry.Space.exists_fieldValuedPoint_comp_eq` produces. Both sides are rewritten by
`AlgebraicGeometry.Space.presheafFibreProperty_iff_schemeFibreProperty` into statements about
the represented fibre as a morphism of schemes, and those two morphisms differ by an
isomorphism of their sources composed with the isomorphism `i` of their targets: the square
representing the fibre over `a` becomes, after composing its right-hand leg with `i`, a second
pullback of the cospan of which the fibre over `yoneda.map i.hom ≫ a` is the first. -/
theorem presheafFibreProperty_iff_of_precomp_iso
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V A A' : BigFppfOver B S hS}
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso] [P.IsStableUnderBaseChange]
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (a : yoneda.obj A ⟶ X) (i : A' ≅ A) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.fst (yoneda.map i.hom ≫ a) f) ↔
      (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.fst a f) := by
  rw [presheafFibreProperty_iff_schemeFibreProperty B S hS f hf,
    presheafFibreProperty_iff_schemeFibreProperty B S hS f hf]
  have h1 : IsPullback (hf.fst a) (yoneda.map (hf.snd a ≫ i.inv)) f
      (yoneda.map i.hom ≫ a) := by
    refine (hf.isPullback a).of_iso' (Iso.refl _) (Iso.refl _) (yoneda.mapIso i) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    simp [CategoryTheory.Functor.map_comp]
  set ePre := yoneda.preimageIso
    (h1.isoIsPullback _ _ (hf.isPullback (yoneda.map i.hom ≫ a))) with hePre
  have he : ePre.hom ≫ hf.snd (yoneda.map i.hom ≫ a) = hf.snd a ≫ i.inv := by
    apply yoneda.map_injective
    rw [CategoryTheory.Functor.map_comp, hePre,
      CategoryTheory.Functor.preimageIso_hom, CategoryTheory.Functor.map_preimage]
    exact h1.isoIsPullback_hom_snd _ _ (hf.isPullback (yoneda.map i.hom ≫ a))
  have hT : (BigFppfOver.toScheme B S hS).map ePre.hom ≫
      (BigFppfOver.toScheme B S hS).map (hf.snd (yoneda.map i.hom ≫ a)) =
      (BigFppfOver.toScheme B S hS).map (hf.snd a) ≫
        (BigFppfOver.toScheme B S hS).map i.inv := by
    rw [← CategoryTheory.Functor.map_comp, he, CategoryTheory.Functor.map_comp]
  rw [← MorphismProperty.cancel_left_of_respectsIso P
      ((BigFppfOver.toScheme B S hS).map ePre.hom) _, hT,
    MorphismProperty.cancel_right_of_respectsIso P _
      ((BigFppfOver.toScheme B S hS).map i.inv)]

/-! ### Tag 086T for an affine étale chart, over the datum of Tag 03JL -/

/-- **Stacks Project, Tag 086T for an affine étale chart, stated over the field-valued datum of
Tag 03JL and modulo Tag 086R alone.** Let `X` be an algebraic space over `S` and let
`f : h_V ⟶ X` be an étale chart with `V` affine. Then there is a decreasing chain of open
subspaces `X = X₀ ⊇ X₁ ⊇ X₂ ⊇ …` of `X` such that, for every object `T` of the site whose
underlying scheme is isomorphic to the spectrum of a field and every section `ξ` of `X` over
`T`, the section `ξ` factors through `X_d` exactly when the fibre of `f` over `ξ` either fails
to be finite or is finite locally free of some rank at least `d`.

This is `AlgebraicGeometry.Space.exists_antitone_openSubspaces_iff_fibreDegree_ge_of_h086R`
with its four morphism hypotheses discharged from étaleness of the chart and affineness of `V`,
and with its iff transported from `AlgebraicGeometry.Space.FieldValuedPoint` to the datum over
which `AlgebraicGeometry.Space.HasUniversallyBoundedFibers` quantifies, by
`AlgebraicGeometry.Space.exists_fieldValuedPoint_comp_eq` and
`AlgebraicGeometry.Space.presheafFibreProperty_iff_of_precomp_iso`. The remaining hypothesis
`h086R` is Tag 086R, the same stratification for a morphism of schemes. -/
theorem exists_antitone_openSubspaces_iff_fibreDegree_ge_siteDatum_of_h086R
    (h086R : ∀ {Z Y : Scheme.{u}} (g : Z ⟶ Y), Flat g → LocallyOfFinitePresentation g →
      _root_.AlgebraicGeometry.IsSeparated g → LocallyQuasiFinite g →
      ∃ V : ℕ → Y.Opens, V 0 = ⊤ ∧ Antitone V ∧
        ∀ (d : ℕ) (k : Type u) (_ : Field k) (c : Spec (.of k) ⟶ Y),
          (∃ h : Spec (.of k) ⟶ (V d).toScheme, h ≫ (V d).ι = c) ↔
            (¬ _root_.AlgebraicGeometry.IsFinite (pullback.fst c g) ∨
              ∃ r : ℕ, d ≤ r ∧
                Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst c g) r))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (V : BigFppfOver B S hS) (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (f : yoneda.obj V ⟶ X)
    (hfetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    ∃ U : ℕ → Subfunctor X,
      (∀ d, IsOpenSubspace B S hS (U d)) ∧ U 0 = ⊤ ∧ Antitone U ∧
      ∀ (d : ℕ) (k : Type u) (_ : Field k) (T : BigFppfOver B S hS),
        ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
        ∀ ξ : yoneda.obj T ⟶ X,
          (∃ g : yoneda.obj T ⟶ (U d).toFunctor, g ≫ (U d).ι = ξ) ↔
          (¬ (MorphismProperty.inverseImage
                (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
                (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f) ∨
            ∃ r : ℕ, d ≤ r ∧
              (MorphismProperty.inverseImage
                (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
                (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f)) := by
  have hrep : yoneda.relativelyRepresentable f :=
    relativelyRepresentable_of_isAlgebraicSpace B S hS hX f
  have _hfinIso : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}))
  have hEtale : IsEtale B S hS f := isEtale_of_presheaf_etale B S hS hfetale
  obtain ⟨U, hUopen, hU0, hUanti, hUiff⟩ :=
    exists_antitone_openSubspaces_iff_fibreDegree_ge_of_h086R B S hS h086R hX V f
      (isFlat_of_isEtale B S hS hEtale)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hEtale)
      (isSeparated_of_isEtale_of_isAffine B S hS hX V hVaff f hEtale)
      (isLocallyQuasiFinite_of_isEtale' B S hS hEtale)
  refine ⟨U, hUopen, hU0, hUanti, fun d k _ T e ξ => ?_⟩
  obtain ⟨p, ε, hpε⟩ := exists_fieldValuedPoint_comp_eq B S hS T e ξ
  have htrans1 := presheafFibreProperty_iff_of_precomp_iso B S hS
    (P := (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})) f hrep
    (yonedaEquiv.symm p.value) ε
  have htrans2 : ∀ r : ℕ, _ ↔ _ := fun r => presheafFibreProperty_iff_of_precomp_iso B S hS
    (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r) f hrep
    (yonedaEquiv.symm p.value) ε
  rw [← hpε, htrans1]
  simp only [htrans2]
  rw [← hUiff d p]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨yoneda.map ε.inv ≫ g, by
      rw [Category.assoc, hg]; exact (yoneda.mapIso ε).inv_hom_id_assoc _⟩
  · rintro ⟨g, hg⟩
    exact ⟨yoneda.map ε.hom ≫ g, by rw [Category.assoc, hg]⟩

/-! ### An empty stratum bounds the fibres of the restricted chart -/

/-- **A stratum through which no field-valued point factors bounds the fibres of the chart.**
Let `f : h_V ⟶ X` be a relatively representable morphism of presheaves on the big fppf category
over `S`, let `j : W ⟶ V` be a morphism of the site which is an open immersion of underlying
schemes, and let `G` be a subfunctor of `X` through which a section of `X` over a field spectrum
factors exactly when the fibre of `f` over it has degree at least `n + 1`, in the sense of the
disjunction of Tag 086T. If no section of `X` over a field spectrum factors through `G`, then
the chart `f` restricted along `j` has universally bounded fibres, with bound `n`.

Taking for `G` the stratum `X_{n+1}` produced by
`AlgebraicGeometry.Space.exists_antitone_openSubspaces_iff_fibreDegree_ge_siteDatum_of_h086R`,
this is the step of the proof of Tag 086U which turns the stratification of Tag 086T into the
hypothesis `hchart` of Tag 03JI. It is
`AlgebraicGeometry.Space.hasUniversallyBoundedFibers_restrict_of_not_presheafFibreDegreeGe`
with its hypothesis read off the iff rather than supplied directly. -/
theorem hasUniversallyBoundedFibers_restrict_of_forall_not_factorsThrough
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V W : BigFppfOver B S hS}
    (f : yoneda.obj V ⟶ X) (hf : yoneda.relativelyRepresentable f)
    (j : W ⟶ V)
    (hj : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (n : ℕ) (G : Subfunctor X)
    (hG : ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        (∃ g : yoneda.obj T ⟶ G.toFunctor, g ≫ G.ι = ξ) ↔
        (¬ (MorphismProperty.inverseImage
              (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f) ∨
          ∃ r : ℕ, n + 1 ≤ r ∧
            (MorphismProperty.inverseImage
              (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
              (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst ξ f)))
    (hempty : ∀ (k : Type u) (_ : Field k) (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ¬ ∃ g : yoneda.obj T ⟶ G.toFunctor, g ≫ G.ι = ξ) :
    HasUniversallyBoundedFibers B S hS W (yoneda.map j ≫ f) :=
  hasUniversallyBoundedFibers_restrict_of_not_presheafFibreDegreeGe B S hS f hf j hj n
    fun k hk T e ξ hd => hempty k hk T e ξ ((hG k hk T e ξ).2 hd)

end AlgebraicGeometry.Space

end
