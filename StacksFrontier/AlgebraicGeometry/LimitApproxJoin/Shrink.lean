module

public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.FibreProductColimit
public import StacksFrontier.AlgebraicGeometry.LimitApproxJoin.OpensRange
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Shrinking to a finite stage: the covering family of affine basic opens

Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms and let `c` be a limiting cone with quasi-affine vertex.  Suppose finitely many global
sections `g` of the vertex have affine basic opens which cover it.  Then some stage carries lifts
of the `g` whose basic opens are again affine and again cover.

This is the shrinking argument of step (ii) of the one-affine-open step of Tag 07RN.  There the
vertex is the overlap of the affine open being added with the part of the scheme already
approximated, the `g` are the restrictions of the finitely many elements whose standard opens
were chosen inside the overlap and covering it — so that at the vertex both hypotheses hold —
and the stage produced here is the one at which the geometric join
`AlgebraicGeometry.Scheme.opensRange_toSpecΓ_eq_iSup_basicOpen` applies and at which
`AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp_SpecMap_snd` produces the open immersion into the
spectrum of the fibre product.

## What is built, and the route

* `AlgebraicGeometry.SpecMap_preimage_iSup_basicOpen`: the preimage of a union of standard opens
  under the spectrum of a ring map is the union of the standard opens of the images.  Each
  individual case is `AlgebraicGeometry.SpecMap_preimage_basicOpen`, which holds by `rfl`.

* `AlgebraicGeometry.exists_stage_appTop_π_eq`: finitely many global sections of the vertex all
  lift to one stage.  This is Tag 01Z0, Mathlib's
  `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`, fed to
  `Stacks.FibreProduct.exists_app_eq_fin`, which does the induction over the finite family.

* `AlgebraicGeometry.exists_map_opensRange_toSpecΓ_eq_iSup_basicOpen` is the shrinking step
  proper, and it is a *single* application of Tag 01Z4 in the form
  `AlgebraicGeometry.exists_map_preimage_eq_map_preimage` — which rests on
  `AlgebraicGeometry.exists_map_preimage_le_map_preimage` — to the diagram of spectra of the
  rings of sections, `D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec`.  The two opens compared at the given
  stage are the image of the stage in the spectrum of its sections and the union of the standard
  opens of the lifts.  They have the same preimage in the limit: for the first that is Mathlib's
  `AlgebraicGeometry.Scheme.preimage_opensRange_toSpecΓ`, for the second it is the preimage
  statement above, and at the limit the two agree by the geometric join
  `AlgebraicGeometry.Scheme.opensRange_toSpecΓ_eq_iSup_basicOpen`.  So they agree after pulling
  back along some transition morphism, which is the equality at a later stage.

  Running the argument on the *two opens together* rather than on the covering and the affineness
  separately is what keeps it to one application.  Transporting affineness basic open by basic
  open would need Tag 01Z4 once per member of the family and then a cofiltered infimum of the
  resulting stages.

* `AlgebraicGeometry.exists_stage_affine_basicOpen_cover` assembles: it picks a quasi-affine
  stage by Tag 01Z5 (`AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit`), a stage
  carrying the lifts, a common lower bound of the two, then shrinks, and finally reads the two
  hypotheses back off the equality of opens by
  `AlgebraicGeometry.Scheme.isAffineOpen_basicOpen_of_basicOpen_le_opensRange` and the preimage
  of the equality under the map to the spectrum.  Its conclusion mentions no instance, so a
  consumer recovers quasi-affineness of the stage from it by
  `AlgebraicGeometry.Scheme.isQuasiAffine_of_iSup_basicOpen_eq_top`.

## Implementation notes

The index universe is tied to the scheme universe.  This is forced twice over: the diagram of
spectra is a diagram of schemes in that universe, and the colimit of rings of sections used for
the lifting is a filtered colimit of `CommRingCat` in it, which is the restriction recorded for
the restated Tag 06AC.
Mathlib's own file on affine-transition limits ties the index
universe to the scheme universe in its variable block and declares a third index universe that no
declaration there uses; the failure mode for freeing it is a deterministic
`whnf` timeout rather than a type error, since instance search then solves a side condition at a
mismatched universe.  It is not freed here.

Transparency gotchas:

* Quasi-affineness propagates *down* the inverse system, by
  `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom`, so it is available at every stage
  below a quasi-affine one, and this is the only reason the conclusion can speak about a stage
  other than the one Tag 01Z5 produces.  It is not available at every stage of the diagram, so
  it cannot be an ambient instance; where the statement of the shrinking step needs it to write
  the image of the later stage, the instance is introduced in the type itself from the transition
  morphism that the existential has just bound.

* The index of the diagram of spectra is the *same* category as that of `D`, while the colimit of
  rings of sections is indexed by its opposite.  The lifting statement therefore unwraps an
  opposite object, and the cocone handed to `Stacks.FibreProduct.exists_app_eq_fin` is the
  structure-eta form of `AlgebraicGeometry.Scheme.Γ.mapCocone`.

* A union of standard opens written with its type ascribed to the opens of `Spec R` is *not*
  type-correct at reducible transparency, since the members are opens of `PrimeSpectrum R`.  No
  `rw` or `simp` can see inside such a term.  Every step touching one here is either an `exact`
  up to definitional equality or a pointwise argument through
  `TopologicalSpace.Opens.mem_iSup`; the compactness of such a union is proved with the honest
  `TopologicalSpace.Opens` type and passed across by unification.

* `CompactSpace` of the spectrum of the sections of a stage is *not* found by `infer_instance`
  after a `dsimp` reduces the composite functor, even though `IsAffine` of the very same object
  is, and `CompactSpace (Spec R)` is for a bare `R`.  Nothing below needs that instance, so it is
  absent; a later consumer that does need it should introduce `IsAffine` first and let the
  priority-100 instance fire, rather than reading the failure as a missing result.

## What is NOT done here

Nothing here glues.  The hypotheses at the *limit* — that finitely many standard opens of the
affine open being added lie inside the overlap and cover it — are taken as given and are not
derived from quasi-compactness of the overlap.  Nothing in this directory constructs an
inhabitant of `AlgebraicGeometry.Scheme.FiniteTypeApproximation`: the functor on the disjoint
union of the stage indices and the induction over the finitely many affine opens, gaps (b) and
(c) of Tag 07RN, are untouched.  Tag 07RN is not proved and no tag attribute is attached to
anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01Z5](https://stacks.math.columbia.edu/tag/01Z5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry

/-- The preimage of a union of standard opens under the spectrum of a ring map is the union of
the standard opens of the images. -/
lemma SpecMap_preimage_iSup_basicOpen {R S : CommRingCat.{u}} (φ : R ⟶ S) {ι : Type v}
    (a : ι → R) :
    Spec.map φ ⁻¹ᵁ (⨆ l, PrimeSpectrum.basicOpen (a l) : (Spec R).Opens) =
      ⨆ l, PrimeSpectrum.basicOpen (φ (a l)) := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (show (Spec.map φ).base x ∈ _ from hx)
    exact Opens.mem_iSup.mpr ⟨l, hl⟩
  · obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hx
    exact Opens.mem_iSup.mpr ⟨l, hl⟩

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c)

include hc in
/-- **Finitely many global sections of the limit come from one stage.**  This is Tag 01Z0, that
the sections of the limit are the filtered colimit of the sections of the stages, together with
the finite-family form of joint surjectivity. -/
lemma exists_stage_appTop_π_eq [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {n : ℕ} (g : Fin n → Γ(c.pt, ⊤)) :
    ∃ (i : I) (f : Fin n → Γ(D.obj i, ⊤)), ∀ l, (c.π.app i).appTop (f l) = g l := by
  obtain ⟨hcolim⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  obtain ⟨i, f, hf⟩ := Stacks.FibreProduct.exists_app_eq_fin
    (F := D.op ⋙ Scheme.Γ) (R := Γ(c.pt, ⊤)) (τ := (Scheme.Γ.mapCocone c.op).ι) hcolim g
  exact ⟨i.unop, f, hf⟩

include hc in
/-- **The shrinking step.**  If the image of the limit in the spectrum of its sections is the
union of the standard opens of the `g l`, and the `f l` are lifts of the `g l` to a quasi-affine
stage, then at some later stage the image of that stage is the union of the standard opens of
the transported lifts.

This is one application of Tag 01Z4 to the diagram of spectra of the rings of sections. -/
lemma exists_map_opensRange_toSpecΓ_eq_iSup_basicOpen
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [c.pt.IsQuasiAffine] {n : ℕ} (g : Fin n → Γ(c.pt, ⊤))
    (haff : ∀ l, IsAffineOpen (c.pt.basicOpen (g l)))
    (hcov : ⨆ l, c.pt.basicOpen (g l) = ⊤)
    (i : I) [(D.obj i).IsQuasiAffine] (f : Fin n → Γ(D.obj i, ⊤))
    (hf : ∀ l, (c.π.app i).appTop (f l) = g l) :
    ∃ (j : I) (fji : j ⟶ i),
      haveI : (D.obj j).IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom (D.map fji)
      (D.obj j).toSpecΓ.opensRange =
        ⨆ l, PrimeSpectrum.basicOpen ((D.map fji).appTop (f l)) := by
  have hE : ∀ {a b : I} (φ : a ⟶ b),
      IsAffineHom ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).map φ) := by dsimp; infer_instance
  have hlimE := isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc
  have hπ : IsAffineHom (show c.pt ⟶ D.obj i from c.π.app i) := isAffineHom_π_app _ _ hc i
  have hU : IsCompact (((D.obj i).toSpecΓ.opensRange : (Spec Γ(D.obj i, ⊤)).Opens) :
      Set (Spec Γ(D.obj i, ⊤))) :=
    isCompact_range (D.obj i).toSpecΓ.base.hom.continuous
  have hV : IsCompact ((⨆ l, PrimeSpectrum.basicOpen (f l) :
      Opens (PrimeSpectrum Γ(D.obj i, ⊤))) : Set (PrimeSpectrum Γ(D.obj i, ⊤))) := by
    rw [Opens.coe_iSup]
    exact isCompact_iUnion fun l ↦ PrimeSpectrum.isCompact_basicOpen (f l)
  have hgf : ∀ l, (PrimeSpectrum.basicOpen ((c.π.app i).appTop (f l)) :
      (Spec Γ(c.pt, ⊤)).Opens) = PrimeSpectrum.basicOpen (g l) := fun l ↦ by rw [hf l]
  have H := (Scheme.preimage_opensRange_toSpecΓ (show c.pt ⟶ D.obj i from c.π.app i)).trans
    (((c.pt.opensRange_toSpecΓ_eq_iSup_basicOpen g haff hcov).trans
      (iSup_congr hgf).symm).trans (SpecMap_preimage_iSup_basicOpen _ f).symm)
  obtain ⟨j, fji, hji⟩ := exists_map_preimage_eq_map_preimage
    (D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec) _ hlimE hU hV H
  refine ⟨j, fji, ?_⟩
  have : (D.obj j).IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom (D.map fji)
  have hji' : Spec.map (D.map fji).appTop ⁻¹ᵁ
        ((D.obj i).toSpecΓ.opensRange : (Spec Γ(D.obj i, ⊤)).Opens) =
      Spec.map (D.map fji).appTop ⁻¹ᵁ (⨆ l, PrimeSpectrum.basicOpen (f l) :
        (Spec Γ(D.obj i, ⊤)).Opens) := hji
  exact ((Scheme.preimage_opensRange_toSpecΓ (D.map fji)).symm.trans hji').trans
    (SpecMap_preimage_iSup_basicOpen _ f)

include hc in
/-- **Some stage carries a covering family of affine basic opens.**  If finitely many global
sections of the limit have affine basic opens covering it, then some stage carries lifts of them
whose basic opens are affine and cover that stage.

Tag 01Z5 supplies a quasi-affine stage, Tag 01Z0 supplies a stage carrying the lifts, a common
lower bound carries both, and Tag 01Z4 then matches the image of that stage with the union of
the standard opens of the lifts; the two conclusions are read off that equality. -/
lemma exists_stage_affine_basicOpen_cover
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [c.pt.IsQuasiAffine] {n : ℕ} (g : Fin n → Γ(c.pt, ⊤))
    (haff : ∀ l, IsAffineOpen (c.pt.basicOpen (g l)))
    (hcov : ⨆ l, c.pt.basicOpen (g l) = ⊤) :
    ∃ (j : I) (f : Fin n → Γ(D.obj j, ⊤)), (∀ l, (c.π.app j).appTop (f l) = g l) ∧
      (∀ l, IsAffineOpen ((D.obj j).basicOpen (f l))) ∧
      ⨆ l, (D.obj j).basicOpen (f l) = ⊤ := by
  have hlift {a b : I} (uab : a ⟶ b) {x : Γ(D.obj b, ⊤)} {l}
      (h : (c.π.app b).appTop x = g l) : (c.π.app a).appTop ((D.map uab).appTop x) = g l := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, c.w uab, h]
  obtain ⟨i₀, hi₀⟩ := Scheme.exists_isQuasiAffine_of_isLimit D c hc
  obtain ⟨i₁, f₁, hf₁⟩ := exists_stage_appTop_π_eq D c hc g
  obtain ⟨i, u₀, u₁, -⟩ := IsCofilteredOrEmpty.cone_objs i₀ i₁
  have : (D.obj i).IsQuasiAffine :=
    have := hi₀
    Scheme.IsQuasiAffine.of_isAffineHom (D.map u₀)
  set f₂ : Fin n → Γ(D.obj i, ⊤) := fun l ↦ (D.map u₁).appTop (f₁ l)
  obtain ⟨j, fji, hj⟩ := exists_map_opensRange_toSpecΓ_eq_iSup_basicOpen D c hc g haff hcov i f₂
    fun l ↦ hlift u₁ (hf₁ l)
  have : (D.obj j).IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom (D.map fji)
  set f₃ : Fin n → Γ(D.obj j, ⊤) := fun l ↦ (D.map fji).appTop (f₂ l)
  refine ⟨j, f₃, fun l ↦ ?_, fun l ↦ ?_, ?_⟩
  · exact hlift fji (hlift u₁ (hf₁ l))
  · exact (D.obj j).isAffineOpen_basicOpen_of_basicOpen_le_opensRange _
      (hj.ge.trans' (le_iSup (fun l ↦ PrimeSpectrum.basicOpen (f₃ l)) l))
  · refine top_unique fun x _ ↦ Opens.mem_iSup.mpr ?_
    have hx : (D.obj j).toSpecΓ.base x ∈ (D.obj j).toSpecΓ.opensRange := ⟨x, rfl⟩
    rw [hj] at hx
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hx
    exact ⟨l, ((D.obj j).toSpecΓ_preimage_basicOpen (f₃ l)).le hl⟩

end AlgebraicGeometry
