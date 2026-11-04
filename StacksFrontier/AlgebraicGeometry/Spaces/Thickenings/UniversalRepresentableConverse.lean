module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalRepresentable

/-!
# A space-level universal first-order thickening of a representable morphism is a scheme-level one

Let `i : V ⟶ V'` and `p : V' ⟶ U` be morphisms of the big fppf category over a scheme `S`, and
suppose the underlying closed immersion of schemes `V ⟶ V'` has square-zero ideal.
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map` says that if
`V ⟶ V'` is a universal first-order thickening of `V` over `U` in the sense of
`Stacks.Thickenings.IsUniversalFirstOrderThickening` — the scheme-level datum of Stacks 0602 —
then the range of `yoneda.map i` is one in the sense of
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening`, the space-level datum.  This file
proves the converse, so that for a morphism of the site the two universal properties agree.

The two are not the same statement, and the space-level one is formally the stronger: its test
objects are arbitrary algebraic spaces over `S`, so arbitrary sheaves on the big fppf site, while
the scheme-level one tests *every* scheme, including those the big site's size cutoff
`AlgebraicGeometry.BigFppfSite.Contains` excludes.  Neither implication is formal.

## Main results

* `Stacks.Thickenings.IsUniversalFirstOrderThickening.ofAmbientIso`: being a universal first-order
  thickening is carried along an isomorphism of the ambient scheme compatible with the inclusion
  and the structure morphism.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_ambientIso`: space-level
  uniqueness of the universal first-order thickening, the uniqueness clause of Stacks 0602.
* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_scheme_of_range_yoneda_map`: **the
  converse**: if the range of `yoneda.map i` is a space-level universal first-order thickening of
  the algebraic space represented by `V` over the one represented by `U`, then `V ⟶ V'` is a
  scheme-level universal first-order thickening of `V` over `U`.
* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map_iff`: the two
  universal properties of a square-zero closed immersion of the site agree.

## Implementation notes

The direct route — take a scheme-level test thickening `T ⊂ T'` and feed it to the space-level
property — is blocked, and no size lemma in the tree unblocks it: the space-level property tests
only algebraic spaces over `S`, so it would need `B.Contains T'` for an arbitrary scheme `T'`
carrying only a morphism `T' ⟶ U`, and every size-reduction lemma available bounds the *source*
of a monomorphism or the pieces of an assembly, never the target of an arbitrary morphism.  What
would unblock it is a spreading-out reduction of the lifting problem to test thickenings of finite
presentation over `U`, which the tree does not have.

The route taken instead is a comparison with the scheme-level universal thickening, and it needs
no new size input.  Formal unramifiedness of the structure morphism, Stacks 0609, holds at the
space level, and transfers to the scheme morphism `V' ⟶ U`; with the inclusion formally unramified
because it is a closed immersion, the composite `V ⟶ U` is formally unramified, so Stacks 04F3
supplies a scheme-level universal first-order thickening `t` of it.  Its ambient is contained in
the big site, by the bound on the size of the ambient of a universal first-order thickening by
the sizes of the source and the base, so
`Stacks.Spaces.UniversalThickening.exists_site_isUniversalFirstOrderThickening` presents `t` by
morphisms of the site, which by the forward implication is a space-level universal first-order
thickening of the same algebraic space over the same base.  Space-level uniqueness,
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.exists_ambientIso`, then gives an
isomorphism of the two ambient *presheaves* compatible with the inclusions and the structure
morphisms; Yoneda is fully faithful, so that isomorphism is the Yoneda image of an isomorphism of
the site, and the scheme-level property transports along it.

Square-zero closedness of the immersion of schemes is a hypothesis rather than a conclusion.  It
is the structural datum of a first-order thickening, not its universal property, and the
space-level predicate records it on the small étale site of `V'`, as
`AlgebraicGeometry.Space.IsFirstOrderThickening` of the subfunctor; identifying that ideal with
`AlgebraicGeometry.Scheme.Hom.ker` of the morphism of schemes is a separate comparison, which the
tree does not have.  Both implications below carry the same hypothesis, so the equivalence of the
two universal properties is unaffected by it.

## References

* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 0603](https://stacks.math.columbia.edu/tag/0603)
* [Stacks Project, Tag 0609](https://stacks.math.columbia.edu/tag/0609)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- **Being a universal first-order thickening is carried along an isomorphism of the ambient
scheme.**  Let `i : Z ⟶ A` and `p : A ⟶ X` make `Z ⊂ A` a universal first-order thickening of `Z`
over `X`, and let `e : A ≅ A'` be an isomorphism carrying `i` to `i'` and `p'` to `p`.  Then
`Z ⊂ A'` is one too, as soon as `i'` is a first-order thickening.

The square-zero condition on `i'` is a hypothesis because the kernel ideal sheaves of `i` and `i'`
live on the two different schemes `A` and `A'`, so they are not compared by
`AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso`, which concerns precomposition with an
isomorphism; nothing else about `i'` is assumed. -/
theorem IsUniversalFirstOrderThickening.ofAmbientIso
    {Z X A A' : AlgebraicGeometry.Scheme.{u}} {h : Z ⟶ X} {i : Z ⟶ A} {p : A ⟶ X}
    {i' : Z ⟶ A'} {p' : A' ⟶ X} (e : A ≅ A')
    (hi : i ≫ e.hom = i') (hp : e.hom ≫ p' = p)
    (hfirst : IsFirstOrderThickening i')
    (hu : IsUniversalFirstOrderThickening h i p) :
    IsUniversalFirstOrderThickening h i' p' where
  isFirstOrderThickening := hfirst
  inclusion_toBase := by
    rw [← hi, Category.assoc, hp]
    exact hu.inclusion_toBase
  existsUnique_lift := by
    intro T T' j hj a b hab
    obtain ⟨c, hc, hcu⟩ := hu.existsUnique_lift j hj a b hab
    refine ⟨c ≫ e.hom, ⟨?_, ?_⟩, fun d hd => ?_⟩
    · rw [← Category.assoc, hc.1, Category.assoc, hi]
    · rw [Category.assoc, hp]
      exact hc.2
    · have hdc : d ≫ e.inv = c := by
        refine hcu (d ≫ e.inv) ⟨?_, ?_⟩
        · rw [← Category.assoc, hd.1, Category.assoc, ← hi, Category.assoc,
            Iso.hom_inv_id, Category.comp_id]
        · rw [Category.assoc, ← hp, Iso.inv_hom_id_assoc]
          exact hd.2
      rw [← hdc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Space-level uniqueness of the universal first-order thickening**, the uniqueness clause of
Stacks 0602.  Let `Y ⊂ Y'` over `X` along `p` and `Z ⊂ Z'` over `X` along `q` be universal
first-order thickenings of algebraic spaces over `S`, and let `e : Z ≅ Y` identify the two
smaller spaces compatibly with their morphisms to `X`.  Then the two ambient presheaves are
isomorphic, compatibly with the inclusions and with the structure morphisms to `X`.

Each universal property lifts the other thickening's ambient across it, and the two lifts are
mutually inverse by the uniqueness of lifts along the identity. -/
theorem IsUniversalFirstOrderThickening.exists_ambientIso
    {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.1} {Z : Subfunctor Z'.1}
    {p : Y' ⟶ X} {q : Z' ⟶ X}
    (hY : IsUniversalFirstOrderThickening B S hS Y p)
    (hZ : IsUniversalFirstOrderThickening B S hS Z q)
    (e : Z.toFunctor ≅ Y.toFunctor) (he : Z.ι ≫ q.hom = e.hom ≫ Y.ι ≫ p.hom) :
    ∃ e' : Z'.1 ≅ Y'.1, Z.ι ≫ e'.hom = e.hom ≫ Y.ι ∧ e'.hom ≫ p.hom = q.hom := by
  obtain ⟨f, hf, _⟩ := hY.existsUnique_lift Z hZ.firstOrder e.hom q.hom he
  have he' : Y.ι ≫ p.hom = e.inv ≫ Z.ι ≫ q.hom := by
    rw [he]
    simp
  obtain ⟨g, hg, _⟩ := hZ.existsUnique_lift Y hY.firstOrder e.inv p.hom he'
  have hfg : f ≫ g = 𝟙 Z'.1 := by
    apply (hZ.existsUnique_lift Z hZ.firstOrder (𝟙 _) q.hom (by simp)).unique
    · constructor
      · simp only [← Category.assoc, hf.1]
        simp only [Category.assoc, hg.1, Iso.hom_inv_id_assoc, Category.id_comp]
      · simp only [Category.assoc, hg.2, hf.2]
    · simp
  have hgf : g ≫ f = 𝟙 Y'.1 := by
    apply (hY.existsUnique_lift Y hY.firstOrder (𝟙 _) p.hom (by simp)).unique
    · constructor
      · simp only [← Category.assoc, hg.1]
        simp only [Category.assoc, hf.1, Iso.inv_hom_id_assoc, Category.id_comp]
      · simp only [Category.assoc, hf.2, hg.2]
    · simp
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

/-- **A space-level universal first-order thickening of a morphism of the site is a scheme-level
one.**  Let `i : V ⟶ V'` and `p : V' ⟶ U` be morphisms of the big fppf category over `S` with
`V ⟶ V'` a square-zero closed immersion of schemes.  If the range of `yoneda.map i` is a universal
first-order thickening of the algebraic space represented by `V` over the one represented by `U`,
then the underlying morphisms of schemes make `V ⟶ V'` a universal first-order thickening of `V`
over `U`.

This is the converse of
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map`, and it is the harder
direction to state: the scheme-level property tests every scheme, including those the size cutoff
of the big site excludes.  The proof compares the given thickening with the one Stacks 04F3
produces at the level of schemes, whose ambient the big site does contain. -/
theorem isUniversalFirstOrderThickening_scheme_of_range_yoneda_map
    {V V' U : BigFppfOver B S hS} (i : V ⟶ V') (p : V' ⟶ U)
    (hi : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i))
    (ht : IsUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map i)) (schemeSpaceMap p)) :
    Stacks.Thickenings.IsUniversalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (i ≫ p))
      ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map p) := by
  classical
  -- The structure morphism of the thickening is formally unramified, by Stacks 0609.
  have hFUp : FormallyUnramified (schemeSpaceMap p).hom :=
    formallyUnramified_of_isUniversalFirstOrderThickening B S hS
      (Subfunctor.range (yoneda.map i)) (schemeSpaceMap p) ht
  have hFUpS : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map p) :=
    (formallyUnramified_yoneda_map_iff_formallyUnramified_map B S hS p).1 hFUp
  have hciS : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map i) := hi.1
  have hmapcomp : (BigFppfOver.toScheme B S hS).map (i ≫ p)
      = (BigFppfOver.toScheme B S hS).map i ≫ (BigFppfOver.toScheme B S hS).map p :=
    (BigFppfOver.toScheme B S hS).map_comp i p
  have hmonoS : Mono ((BigFppfOver.toScheme B S hS).map i) := inferInstance
  have hdiagS : _root_.AlgebraicGeometry.IsOpenImmersion
      (pullback.diagonal ((BigFppfOver.toScheme B S hS).map i)) := inferInstance
  have hFUiS : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map i) := inferInstance
  have hFUcomp : _root_.AlgebraicGeometry.FormallyUnramified
      ((BigFppfOver.toScheme B S hS).map (i ≫ p)) := by
    rw [hmapcomp]
    exact MorphismProperty.comp_mem @_root_.AlgebraicGeometry.FormallyUnramified _ _ hFUiS hFUpS
  -- The scheme-level universal first-order thickening of the composite, and the big site
  -- contains its ambient.
  obtain ⟨t⟩ := Stacks.Thickenings.nonempty_universalFirstOrderThickening
    ((BigFppfOver.toScheme B S hS).map (i ≫ p))
  obtain ⟨W, i₁, p₁, hcomp, -, -, -, hfirst₁, huniv₁, huS₁⟩ :=
    Stacks.Spaces.UniversalThickening.exists_site_isUniversalFirstOrderThickening B S hS (i ≫ p) t
  -- Both thickenings are space-level universal, so their ambient presheaves are isomorphic.
  have hmono : ∀ {A A' : BigFppfOver B S hS} (j : A ⟶ A'),
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map j) →
        Mono (yoneda.map j) := fun j hj =>
    mono_of_isClosedImmersion B S hS (yoneda.map j)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) j).2 hj.1)
  have := hmono i hi
  have := hmono i₁ hfirst₁
  have hIso : IsIso (Subfunctor.toRange (yoneda.map i)) := inferInstance
  have hIso₁ : IsIso (Subfunctor.toRange (yoneda.map i₁)) := inferInstance
  let eIso : (Subfunctor.range (yoneda.map i₁)).toFunctor ≅
      (Subfunctor.range (yoneda.map i)).toFunctor :=
    { hom := inv (Subfunctor.toRange (yoneda.map i₁)) ≫ Subfunctor.toRange (yoneda.map i)
      inv := inv (Subfunctor.toRange (yoneda.map i)) ≫ Subfunctor.toRange (yoneda.map i₁)
      hom_inv_id := by
        rw [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id]
      inv_hom_id := by
        rw [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id] }
  have heh : eIso.hom
      = inv (Subfunctor.toRange (yoneda.map i₁)) ≫ Subfunctor.toRange (yoneda.map i) := rfl
  have he : (Subfunctor.range (yoneda.map i₁)).ι ≫ yoneda.map p₁
      = eIso.hom ≫ (Subfunctor.range (yoneda.map i)).ι ≫ yoneda.map p := by
    rw [heh]
    have hA : Subfunctor.toRange (yoneda.map i₁) ≫
        (Subfunctor.range (yoneda.map i₁)).ι ≫ yoneda.map p₁ = yoneda.map (i₁ ≫ p₁) := by
      rw [← Category.assoc, Subfunctor.toRange_ι, ← yoneda.map_comp]
    have hB : Subfunctor.toRange (yoneda.map i₁) ≫
        (inv (Subfunctor.toRange (yoneda.map i₁)) ≫ Subfunctor.toRange (yoneda.map i)) ≫
          (Subfunctor.range (yoneda.map i)).ι ≫ yoneda.map p = yoneda.map (i ≫ p) := by
      rw [Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc,
        Subfunctor.toRange_ι, ← yoneda.map_comp]
    exact (cancel_epi (Subfunctor.toRange (yoneda.map i₁))).1
      (hA.trans ((congrArg yoneda.map hcomp).trans hB.symm))
  obtain ⟨e', he'i, he'b⟩ := IsUniversalFirstOrderThickening.exists_ambientIso B S hS
    (X := schemeSpace U) (Y' := schemeSpace V') (Z' := schemeSpace W)
    (Y := Subfunctor.range (yoneda.map i)) (Z := Subfunctor.range (yoneda.map i₁))
    (p := schemeSpaceMap p) (q := schemeSpaceMap p₁) ht huniv₁ eIso he
  -- Yoneda is fully faithful, so the isomorphism comes from one of the site.
  have hmapg : yoneda.map (yoneda.preimageIso e').hom = e'.hom :=
    yoneda.map_preimage e'.hom
  have hig : i₁ ≫ (yoneda.preimageIso e').hom = i := by
    have h' : (Subfunctor.range (yoneda.map i₁)).ι ≫ yoneda.map (yoneda.preimageIso e').hom
        = (inv (Subfunctor.toRange (yoneda.map i₁)) ≫ Subfunctor.toRange (yoneda.map i)) ≫
          (Subfunctor.range (yoneda.map i)).ι :=
      (congrArg (fun k => (Subfunctor.range (yoneda.map i₁)).ι ≫ k) hmapg).trans he'i
    have h : Subfunctor.toRange (yoneda.map i₁) ≫ (Subfunctor.range (yoneda.map i₁)).ι ≫
        yoneda.map (yoneda.preimageIso e').hom = yoneda.map i := by
      rw [h', Category.assoc, IsIso.hom_inv_id_assoc, Subfunctor.toRange_ι]
    rw [← Category.assoc, Subfunctor.toRange_ι, ← yoneda.map_comp] at h
    exact yoneda.map_injective h
  have he'b' : yoneda.map (yoneda.preimageIso e').hom ≫ yoneda.map p = yoneda.map p₁ :=
    (congrArg (fun k => k ≫ yoneda.map p) hmapg).trans he'b
  have hpg : (yoneda.preimageIso e').hom ≫ p = p₁ :=
    yoneda.map_injective ((yoneda.map_comp _ _).trans he'b')
  -- Transport the scheme-level property along the isomorphism of ambients.
  have hcompS : (BigFppfOver.toScheme B S hS).map (i₁ ≫ p₁)
      = (BigFppfOver.toScheme B S hS).map (i ≫ p) := congrArg _ hcomp
  refine Stacks.Thickenings.IsUniversalFirstOrderThickening.ofAmbientIso
    (i := (BigFppfOver.toScheme B S hS).map i₁)
    (p := (BigFppfOver.toScheme B S hS).map p₁)
    ((BigFppfOver.toScheme B S hS).mapIso (yoneda.preimageIso e')) ?_ ?_ hi ?_
  · rw [Functor.mapIso_hom, ← Functor.map_comp, hig]
  · rw [Functor.mapIso_hom, ← Functor.map_comp, hpg]
  · rw [← hcompS]
    exact huS₁

/-- **For a square-zero closed immersion of the site, the space-level and the scheme-level
universal first-order thickening properties agree.**  The forward implication is
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_range_yoneda_map` and the backward one is
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_scheme_of_range_yoneda_map`. -/
theorem isUniversalFirstOrderThickening_range_yoneda_map_iff
    {V V' U : BigFppfOver B S hS} (i : V ⟶ V') (p : V' ⟶ U)
    (hi : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i)) :
    IsUniversalFirstOrderThickening B S hS
        (Subfunctor.range (yoneda.map i)) (schemeSpaceMap p) ↔
      Stacks.Thickenings.IsUniversalFirstOrderThickening
        ((BigFppfOver.toScheme B S hS).map (i ≫ p))
        ((BigFppfOver.toScheme B S hS).map i)
        ((BigFppfOver.toScheme B S hS).map p) :=
  ⟨isUniversalFirstOrderThickening_scheme_of_range_yoneda_map B S hS i p hi,
    isUniversalFirstOrderThickening_range_yoneda_map B S hS i p⟩

end AlgebraicGeometry.Space

end
