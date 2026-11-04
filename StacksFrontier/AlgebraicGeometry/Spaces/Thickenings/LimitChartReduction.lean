module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.NilpotentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms

/-!
# Subfunctors contained in every thickening, detected on a limit chart

Let `X` be an algebraic space over `S`, let `f : V ⟶ X` be a surjective étale chart whose source
is the limit `V = lim Vⱼ` of a cofiltered system of objects of the site with affine transition
morphisms, and let `W ⊆ X` be a subfunctor such that for every point `v : T ⟶ V` with
`f ∘ v ∈ W` and every `j`, the composite `T ⟶ V ⟶ Vⱼ` kills the nilpotent functions of `Vⱼ`.
Then `W` is contained in every thickening `G ⊆ X`: the base change of `G` to `V` is a surjective
closed immersion, through which such a `v` factors by
`AlgebraicGeometry.exists_lift_of_isClosedImmersion_of_surjective_of_isLimit`, and `f` is
locally surjective. A reduced closed subspace of a chart is the source of points of this kind.

This is the step of the proof that a thickening of an affine algebraic space is affine which
shows that the limit of the reductions of the stages of a Noetherian approximation lies in the
given thickening.

## Main results

* `AlgebraicGeometry.Space.le_of_isThickening_of_isLimit`: the containment.
* `AlgebraicGeometry.Space.app_eq_zero_of_mem_of_hasEtaleLocalProperty_isReduced`: a point of a
  reduced closed subspace of a representable presheaf kills nilpotent functions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A point of a reduced closed subspace of a representable presheaf kills nilpotent
functions.** Let `P` be a closed subspace of the presheaf represented by `V` which is reduced.
For a point `v : T ⟶ V` lying in `P`, pulling back along `v` kills every nilpotent function on
an open of `V`: `v` factors through the closed subscheme representing `P`, which is reduced. -/
theorem app_eq_zero_of_mem_of_hasEtaleLocalProperty_isReduced {V : BigFppfOver B S hS}
    (P : Subfunctor (yoneda.obj V)) (hP : IsClosedSubspace B S hS P)
    (hred : HasEtaleLocalProperty B S hS P.toFunctor (fun Y : Scheme.{u} => IsReduced Y))
    {T : BigFppfOver B S hS} (v : T ⟶ V) (hv : v ∈ P.obj (op T))
    (U : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (t : ((BigFppfOver.toScheme B S hS).obj V).presheaf.obj (op U)) (ht : IsNilpotent t) :
    ((BigFppfOver.toScheme B S hS).map v).app U t = 0 := by
  obtain ⟨C, c, i, hci⟩ := hP.2.1 (𝟙 (yoneda.obj V))
  have hiso : IsIso i := hci.isIso_fst_of_isIso
  have : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    ⟨fun Y => by
      show _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 Y))
      rw [CategoryTheory.Functor.map_id]
      infer_instance⟩
  have : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hiE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) i :=
    MorphismProperty.presheaf_of_isIso _ i
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj C) :=
    isReduced_of_hasEtaleLocalProperty_isReduced B S hS hred hiE
  -- `v` factors through `c`
  obtain ⟨l, hl⟩ : ∃ l : T ⟶ C, l ≫ c = v := by
    let y : T ⟶ C := (inv i).app (op T) ⟨v, hv⟩
    have h1 := congrFun (congrArg (fun φ => φ.app (op T)) hci.w) y
    have h2 : i.app (op T) y = ⟨v, hv⟩ :=
      congrFun (congrArg (fun φ => φ.app (op T)) (IsIso.inv_hom_id i)) ⟨v, hv⟩
    refine ⟨y, ?_⟩
    have h3 : (yoneda.map c ≫ 𝟙 _).app (op T) y = y ≫ c := rfl
    rw [← h3, ← h1]
    show (P.ι.app (op T)) (i.app (op T) y) = v
    rw [h2]
    rfl
  subst hl
  have key : ((BigFppfOver.toScheme B S hS).map c).app U t = 0 :=
    (ht.map (((BigFppfOver.toScheme B S hS).map c).app U).hom).eq_zero
  have hcomp := congrArg (fun φ => φ.hom t) (Scheme.Hom.comp_app
    ((BigFppfOver.toScheme B S hS).map l) ((BigFppfOver.toScheme B S hS).map c) U)
  show ((BigFppfOver.toScheme B S hS).map l ≫ (BigFppfOver.toScheme B S hS).map c).app U t = 0
  rw [hcomp]
  show ((BigFppfOver.toScheme B S hS).map l).app _
    (((BigFppfOver.toScheme B S hS).map c).app U t) = 0
  rw [key, map_zero]

variable {B S hS}

/-- **A subfunctor detected on a limit chart is contained in every thickening.** Let
`f : V ⟶ X` be a surjective étale chart of an algebraic space whose source is the limit of a
cofiltered system `Vⱼ` with affine transition morphisms, and let `W ⊆ X` be a subfunctor such
that, for every point `v : T ⟶ V` with `f ∘ v ∈ W`, every composite `T ⟶ Vⱼ` kills the
nilpotent functions on affine opens of `Vⱼ`. Then `W` is contained in every thickening `G` of
`X`. -/
theorem le_of_isThickening_of_isLimit {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    (hG : IsThickening B S hS X G) (W : Subfunctor X.1)
    {J : Type u} [Category.{u} J] [IsCofiltered J] (Vs : J ⥤ BigFppfOver B S hS)
    [∀ {i j : J} (g : i ⟶ j),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (Vs.map g))]
    (cV : Cone Vs) (hV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
    (f : yoneda.obj cV.pt ⟶ X.1)
    (hfS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f)
    (hW : ∀ (T : BigFppfOver B S hS) (v : T ⟶ cV.pt), f.app (op T) v ∈ W.obj (op T) →
      ∀ (j : J) (U : ((BigFppfOver.toScheme B S hS).obj (Vs.obj j)).Opens), IsAffineOpen U →
        ∀ t : ((BigFppfOver.toScheme B S hS).obj (Vs.obj j)).presheaf.obj (op U),
          IsNilpotent t → ((BigFppfOver.toScheme B S hS).map (v ≫ cV.π.app j)).app U t = 0) :
    W ≤ G := by
  classical
  let J' := BigFppfOver.topology B S hS
  -- the base change of `G` to the chart
  obtain ⟨C, c, i, hij⟩ := hG.1.2.1 f
  have hcClosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map c) := hG.1.2.2 f i c hij
  have hsurjPoints :
      Function.Surjective (pointsMap B S hS (yoneda.obj C) (yoneda.map c)) := by
    intro x
    obtain ⟨z, hz⟩ := hG.2 (pointsMap B S hS (yoneda.obj cV.pt) f x)
    let Z' : AlgebraicSpaces B S hS := ⟨G.toFunctor, hG.1.1⟩
    let T' : AlgebraicSpaces B S hS := ⟨yoneda.obj cV.pt, isAlgebraicSpace_yoneda B S hS cV.pt⟩
    let P' : AlgebraicSpaces B S hS := ⟨yoneda.obj C, isAlgebraicSpace_yoneda B S hS C⟩
    let zi : Z' ⟶ X := ObjectProperty.homMk G.ι
    let qt : T' ⟶ X := ObjectProperty.homMk f
    let pi : P' ⟶ Z' := ObjectProperty.homMk i
    let pj : P' ⟶ T' := ObjectProperty.homMk (yoneda.map c)
    have hsq : IsPullback pi pj zi qt := IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hij
    obtain ⟨w, -, hw₂⟩ := exists_point_of_isPullback B S hS hsq z x (by simpa [zi, qt] using hz)
    exact ⟨w, by simpa [pj] using hw₂⟩
  have hsurjPresheaf :=
    (surjective_iff_surjective_pointsMap B S hS (yoneda.obj cV.pt)
      (isAlgebraicSpace_yoneda B S hS cV.pt) C (yoneda.map c)).2 hsurjPoints
  have hcSurj : Surjective ((BigFppfOver.toScheme B S hS).map c) :=
    hsurjPresheaf.property (𝟙 (yoneda.obj cV.pt)) (𝟙 (yoneda.obj C)) c IsPullback.of_id_fst
  -- a point of the chart over `W` lies over `G`
  have hmem : ∀ (T : BigFppfOver B S hS) (v : T ⟶ cV.pt), f.app (op T) v ∈ W.obj (op T) →
      f.app (op T) v ∈ G.obj (op T) := by
    intro T v hv
    have : ∀ {i j : J} (a : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
        ((Vs ⋙ BigFppfOver.toScheme B S hS).map a) := fun a =>
      inferInstanceAs (_root_.AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map (Vs.map a)))
    obtain ⟨l, hl⟩ := exists_lift_of_isClosedImmersion_of_surjective_of_isLimit
      (Vs ⋙ BigFppfOver.toScheme B S hS) ((BigFppfOver.toScheme B S hS).mapCone cV) hV
      ((BigFppfOver.toScheme B S hS).map v) ((BigFppfOver.toScheme B S hS).map c)
      (fun j U hU t ht => by
        have := hW T v hv j U hU t ht
        rwa [Functor.map_comp] at this)
    let l' : T ⟶ C := Over.homMk (B.inclusion.preimage l) (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage]
      have hcw : C.hom = c.left ≫ cV.pt.hom := (Over.w c).symm
      rw [hcw, Functor.map_comp, ← Category.assoc]
      show (l ≫ (BigFppfOver.toScheme B S hS).map c) ≫ B.inclusion.map cV.pt.hom = _
      rw [hl]
      show B.inclusion.map (v.left ≫ cV.pt.hom) = _
      rw [Over.w v])
    have hl' : l' ≫ c = v := by
      apply (BigFppfOver.toScheme B S hS).map_injective
      rw [Functor.map_comp]
      show B.inclusion.map (B.inclusion.preimage l) ≫ _ = _
      rw [Functor.map_preimage, hl]
    have h : f.app (op T) (l' ≫ c) = G.ι.app (op T) (i.app (op T) l') :=
      (congrFun (congrArg (fun φ => φ.app (op T)) hij.w) l').symm
    rw [← hl', h]
    exact (i.app (op T) l').2
  -- descend along the locally surjective chart
  have hfLocal : Presheaf.IsLocallySurjective J' f := by
    have hfFppf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        ((fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f ∧ Surjective f) :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f := by
      refine ⟨hfE.1, fun A C' k b c' hbc => ?_⟩
      have : Etale ((BigFppfOver.toScheme B S hS).map c') := hfE.2 k b c' hbc
      exact ⟨inferInstance, inferInstance, hfS.2 k b c' hbc⟩
    exact isLocallySurjective_of_representable_flat_locallyOfFinitePresentation_surjective
      B S hS (F := ⟨yoneda.obj cV.pt, (isAlgebraicSpace_yoneda B S hS cV.pt).isSheaf⟩)
      (G := ⟨X.1, X.2.isSheaf⟩) ⟨f⟩ hfFppf
  let p : (W.preimage f).toFunctor ⟶ W.toFunctor := W.fromPreimage f
  have hpLocal : Presheaf.IsLocallySurjective J' p := by
    refine ⟨fun {U} w => J'.superset_covering ?_ (hfLocal.imageSieve_mem (W.ι.app (op U) w))⟩
    rintro T a ⟨v, hv⟩
    refine ⟨⟨v, ?_⟩, ?_⟩
    · show f.app _ v ∈ W.obj _
      rw [hv]
      exact (W.toFunctor.map a.op w).2
    · exact Subtype.ext hv
  have hg : Subfunctor.range (p ≫ W.ι) ≤ G := by
    rintro ⟨T⟩ _ ⟨⟨v, hv⟩, rfl⟩
    exact hmem T v hv
  obtain ⟨g', hg'⟩ := factorThroughSubfunctor_of_locallySurjective G W.ι p hpLocal
    ((isSheaf_iff_isSheaf_of_type J' X.1).1 X.2.isSheaf)
    ((isSheaf_iff_isSheaf_of_type J' G.toFunctor).1 hG.1.1.isSheaf)
    (Subfunctor.lift (p ≫ W.ι) hg) (Subfunctor.lift_ι _ _)
  intro T w hw
  have h3 : (g'.app T ⟨w, hw⟩).1 = w := congrFun (congrArg (fun φ => φ.app T) hg') ⟨w, hw⟩
  exact h3 ▸ (g'.app T ⟨w, hw⟩).2

end AlgebraicGeometry.Space

end
