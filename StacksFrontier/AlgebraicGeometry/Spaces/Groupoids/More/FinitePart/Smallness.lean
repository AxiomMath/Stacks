module

public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Preimages of open subspaces, and smallness of the finite open subspaces

An open subspace of an algebraic space is recorded as a subfunctor, which lives one universe
above the presheaves themselves, so the collection of open subspaces of a fixed algebraic
space is a priori too large to be the value of a presheaf of types. It is nevertheless
*essentially* small: an open subspace is determined by its preimage under any surjective étale
chart, and that preimage is an open subset of the underlying scheme of the chart. The same
therefore holds for the pairs of Stacks 04PC over a fixed scheme, which is what allows the
finite part of a morphism to be a presheaf of types.

Along the way: the preimage of a subfunctor is cartesian over it, the preimage of an open
subspace is an open subspace, and a base change of a finite morphism is finite.

## Main results

* `AlgebraicGeometry.Space.small_finiteOpenSubspace`: the pairs of Stacks 04PC over a scheme of
  the site form an essentially small type.

## Implementation notes

Injectivity of the encoding of an open subspace by an open subset of a chart is the only
delicate point. Two open subspaces with the same preimage under a chart `a` are equal because
each is a sheaf, `a` is locally surjective, and a section of the ambient space whose pullback
along `a` lands in a subfunctor already lands in it on a covering, hence lands in it. Local
surjectivity of `a` comes from `AlgebraicGeometry.Space` Stacks 05VM applied to the atlas of
the ambient space: a surjective étale morphism of schemes is flat, locally of finite
presentation and surjective.

The open subset attached to an open subspace `A` and a chart `a` is the range of the
represented base change of the inclusion of `A` along `a`, which is an open immersion of
schemes; two open subspaces whose ranges agree have the same preimage because a morphism to
the chart factors through an open immersion exactly when its range is contained in the range
of that immersion.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 05VM](https://stacks.math.columbia.edu/tag/05VM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-- Two subfunctors of a sheaf whose preimages along a locally surjective morphism are nested
are themselves nested, provided the smaller preimage's subfunctor is a sheaf. -/
private lemma subfunctor_le_of_preimage_le_of_isLocallySurjective
    {C : Type v} [Category.{w, v} C] {J : GrothendieckTopology C} {F G : Cᵒᵖ ⥤ Type u}
    (A A' : Subfunctor F) (hF : Presheaf.IsSheaf J F) (hA' : Presheaf.IsSheaf J A'.toFunctor)
    (q : G ⟶ F) (hls : Presheaf.IsLocallySurjective J q)
    (hpre : A.preimage q ≤ A'.preimage q) : A ≤ A' := by
  intro U x hx
  have hF' := (CategoryTheory.isSheaf_iff_isSheaf_of_type J F).mp hF
  have hA'' := (CategoryTheory.isSheaf_iff_isSheaf_of_type J A'.toFunctor).mp hA'
  apply (A'.isSheaf_iff hF').1 hA'' U x
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J q x)
  rintro V f ⟨y, hy⟩
  have hyA : y ∈ (A.preimage q).obj (op V) := by
    change q.app (op V) y ∈ A.obj (op V)
    rw [hy]
    exact A.map f.op hx
  change F.map f.op x ∈ A'.obj (op V)
  rw [← hy]
  exact hpre _ hyA

/-- A surjective étale chart of an algebraic space is locally surjective for the fppf
topology. -/
private lemma isLocallySurjective_of_isAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a)
    (he : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a := by
  let J := BigFppfOver.topology B S hS
  let Fsh : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  let Ush : Sheaf J (Type u) := ⟨yoneda.obj U, (isAlgebraicSpace_yoneda B S hS U).isSheaf⟩
  let ash : Ush ⟶ Fsh := ⟨a⟩
  have hflat : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage
        ((fun _ _ g => Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g) :
          MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a := by
    refine ⟨he.1, fun V W g fst snd sq => ?_⟩
    have : Etale ((BigFppfOver.toScheme B S hS).map snd) := he.2 g fst snd sq
    exact ⟨inferInstance, inferInstance, ha.2 g fst snd sq⟩
  exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
    B S hS ash hflat

/-- The open subset of a chart cut out by an open subspace: the range of the represented base
change of the inclusion of the subspace along the chart. -/
private noncomputable def openRangeCode (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (A : Subfunctor F) (hA : IsOpenImmersion B S hS A.ι) (g : yoneda.obj U ⟶ F) :
    ((BigFppfOver.toScheme B S hS).obj U).Opens := by
  haveI : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hA.rep.snd g)) :=
    hA.property_snd g
  exact ((BigFppfOver.toScheme B S hS).map (hA.rep.snd g)).opensRange

/-- Two open subspaces cutting out the same open subset of a chart have the same preimage
under that chart. -/
private lemma preimage_eq_of_openRangeCode_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {A A' : Subfunctor F} (hA : IsOpenImmersion B S hS A.ι)
    (hA' : IsOpenImmersion B S hS A'.ι) (g : yoneda.obj U ⟶ F)
    (hcode : openRangeCode B S hS A hA g = openRangeCode B S hS A' hA' g) :
    A.preimage g = A'.preimage g := by
  classical
  let q := BigFppfOver.toScheme B S hS
  let p := hA.rep.snd g
  let p' := hA'.rep.snd g
  have hrange : Set.range (q.map p) = Set.range (q.map p') := by
    have he := congrArg (fun O : (q.obj U).Opens => (O : Set (q.obj U))) hcode
    simpa [openRangeCode, q, Scheme.Hom.coe_opensRange, p, p'] using he
  apply Subfunctor.ext
  funext V
  ext x
  change g.app V x ∈ A.obj V ↔ g.app V x ∈ A'.obj V
  have factor_iff (W : BigFppfOver B S hS) (A : Subfunctor F)
      (hA : IsOpenImmersion B S hS A.ι) (z : (W ⟶ U)) :
      g.app (op W) z ∈ A.obj (op W) ↔
        Set.range (q.map z) ⊆ Set.range (q.map (hA.rep.snd g)) := by
    let R := hA.rep.pullback g
    let P := hA.rep.snd g
    have hR : _root_.AlgebraicGeometry.IsOpenImmersion (q.map P) := hA.property_snd g
    constructor
    · intro hz
      let α : yoneda.obj W ⟶ A.toFunctor := yonedaEquiv.symm ⟨g.app (op W) z, hz⟩
      have hcomm : α ≫ A.ι = yoneda.map z ≫ g := by
        apply yonedaEquiv.injective
        rw [yonedaEquiv_comp]
        change (yonedaEquiv α).val = g.app (op W) (yonedaEquiv (yoneda.map z))
        have hα : yonedaEquiv α = (⟨g.app (op W) z, hz⟩ : A.toFunctor.obj (op W)) :=
          Equiv.apply_symm_apply yonedaEquiv _
        rw [hα, yonedaEquiv_yoneda_map]
      let β := (hA.rep.isPullback g).lift α (yoneda.map z) hcomm
      have hβ : β ≫ yoneda.map P = yoneda.map z := (hA.rep.isPullback g).lift_snd _ _ _
      let l : W ⟶ R := yonedaEquiv β
      have hβ' : β = yoneda.map l := by
        calc β = yonedaEquiv.symm (yonedaEquiv β) := (yonedaEquiv.symm_apply_apply β).symm
          _ = yoneda.map l := by dsimp [l, yonedaEquiv]; rfl
      have hl : l ≫ P = z := by
        apply yoneda.map_injective
        simpa [hβ', Functor.map_comp] using hβ
      calc Set.range (q.map z) = Set.range (q.map (l ≫ P)) := by rw [hl]
        _ = Set.range (q.map P ∘ q.map l) := by simp [Functor.map_comp]
        _ ⊆ Set.range (q.map P) := Set.range_comp_subset_range _ _
    · intro hz
      let lScheme := _root_.AlgebraicGeometry.IsOpenImmersion.lift (q.map P) (q.map z) hz
      have hlScheme : lScheme ≫ q.map P = q.map z :=
        _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hz
      let l₀ := B.inclusion.preimage lScheme
      have hl₀ : B.inclusion.map l₀ = lScheme := B.inclusion.map_preimage _
      have hPover : q.map P ≫ B.inclusion.map U.hom = B.inclusion.map R.hom := by
        change B.inclusion.map (P.left ≫ U.hom) = B.inclusion.map R.hom
        exact congrArg B.inclusion.map (Over.w P)
      let l : W ⟶ R := Over.homMk l₀ (by
        apply B.inclusion.map_injective
        rw [B.inclusion.map_comp, hl₀, ← hPover, reassoc_of% hlScheme]
        change B.inclusion.map z.left ≫ B.inclusion.map U.hom = B.inclusion.map W.hom
        exact congrArg B.inclusion.map (Over.w z))
      have hl : q.map l = lScheme := by simpa [q, l] using hl₀
      have hfac : l ≫ P = z := q.map_injective <| by rwa [Functor.map_comp, hl]
      let α : yoneda.obj W ⟶ A.toFunctor := yoneda.map l ≫ hA.rep.fst g
      have hcomm : α ≫ A.ι = yoneda.map z ≫ g := by
        calc α ≫ A.ι = yoneda.map l ≫ (yoneda.map P ≫ g) := by
              dsimp [α, P]
              rw [Category.assoc, (hA.rep.isPullback g).w]
          _ = yoneda.map (l ≫ P) ≫ g := congrArg (fun t => t ≫ g) (yoneda.map_comp l P).symm
          _ = yoneda.map z ≫ g := by rw [hfac]
      have hzA' : A.ι.app (op W) (yonedaEquiv α) = g.app (op W) z := by
        simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using congrArg yonedaEquiv hcomm
      have hzA : (yonedaEquiv α).val = g.app (op W) z := hzA'
      rw [← hzA]
      exact (yonedaEquiv α).property
  rw [factor_iff V.unop A hA x, factor_iff V.unop A' hA' x, hrange]

/-- The open subspaces of an algebraic space form an essentially small type. -/
private lemma small_openSubspaceSubfunctors (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    Small.{u} {A : Subfunctor F // IsOpenSubspace B S hS A} := by
  classical
  obtain ⟨U, a, ha, he⟩ := hF.exists_atlas
  have hls := isLocallySurjective_of_isAlgebraicSpace B S hS hF a ha he
  apply small_of_injective (f := fun A : {A : Subfunctor F // IsOpenSubspace B S hS A} =>
    openRangeCode B S hS A.1 A.2.2 a)
  intro A A' hAA'
  apply Subtype.ext
  have hpre : A.1.preimage a = A'.1.preimage a :=
    preimage_eq_of_openRangeCode_eq B S hS A.2.2 A'.2.2 a hAA'
  exact le_antisymm
    (subfunctor_le_of_preimage_le_of_isLocallySurjective A.1 A'.1 hF.isSheaf A'.2.1.isSheaf a
      hls hpre.le)
    (subfunctor_le_of_preimage_le_of_isLocallySurjective A'.1 A.1 hF.isSheaf A.2.1.isSheaf a
      hls hpre.ge)

-- `AlgebraicGeometry.Space.isFinite_of_isPullback` is NOT declared here. It is Stacks
-- 03ZS's finite case and is public, in this same namespace, in
-- `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/IntegralFinite.lean`, where it carries
-- `@[stacks 03ZS "finite"]`. Declaring it again here made the `StacksDraft` umbrella --
-- which imports both -- fail with `environment already contains …`.

/-- The pairs of Stacks 04PC over a scheme of the site form an essentially small type: such a
pair consists of a morphism out of a representable presheaf, of which there are only `u`-many,
together with an open subspace of the resulting fibre product. -/
theorem small_finiteOpenSubspace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : BigFppfOver B S hS) :
    Small.{u} (FiniteOpenSubspace B S hS f (schemeSpace T)) := by
  classical
  let base : Type (u + 1) := NatTrans (yoneda.obj T) Y.obj
  let fiber (a : base) : Type (u + 1) :=
    {A : Subfunctor (pullback a f.hom) // IsOpenSubspace B S hS A}
  have hbase : Small.{u} base := small_of_injective (f := yonedaEquiv) yonedaEquiv.injective
  have hfiber (a : base) : Small.{u} (fiber a) := small_openSubspaceSubfunctors B S hS
    (isAlgebraicSpace_pullback B S hS a f.hom (schemeSpace T).property X.property Y.property)
  have : Small.{u} (Σ a, fiber a) := inferInstance
  let encode : FiniteOpenSubspace B S hS f (schemeSpace T) → Σ a : base, fiber a :=
    fun p => ⟨p.toBase.hom, ⟨p.subspace, p.isOpen⟩⟩
  apply small_of_injective (f := encode)
  intro p q hpq
  change encode p = encode q at hpq
  rcases p with ⟨pbase, psub, popen, pfinite⟩
  rcases q with ⟨qbase, qsub, qopen, qfinite⟩
  obtain rfl : pbase = qbase := ObjectProperty.hom_ext _ (congrArg Sigma.fst hpq)
  obtain rfl : psub = qsub := by
    injection hpq with _ hs
    exact congrArg Subtype.val hs
  congr

end AlgebraicGeometry.Space

end
