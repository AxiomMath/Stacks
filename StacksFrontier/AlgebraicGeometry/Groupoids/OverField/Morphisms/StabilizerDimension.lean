module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.BaseFieldUniqueness
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.GlobalSections

/-!
# The arrow scheme and the stabilizer of a groupoid over a field have the same dimension

Let `(U, R, s, t, c)` be a groupoid scheme over a scheme `S` whose object scheme is the spectrum
of a field `k`, and assume `s` and `t` are locally of finite type. Then the arrow scheme `R` and
the stabilizer group scheme `G`, the inverse image of the diagonal of `U` under `(t, s)`, have
the same dimension.

One inequality is formal: because `U` has one point, `U ⟶ S` is separated, so the diagonal of
`U` is a closed immersion and hence so is its base change `G ⟶ R`. For the other, take the
irreducible component `Z` of `R` through the identity, with its reduced induced closed subscheme
structure. The identity section factors through `Z`, so the two morphisms `Z ⟶ Spec k` obtained
from `s` and from `t` admit a common section; they are therefore equal, which exhibits `Z` as a
closed subscheme of `G`. Since `R` is equidimensional with the dimension of each of its
components, this gives `dim R = dim Z ≤ dim G`.

That the two morphisms `Z ⟶ Spec k` are equal is where the ground field enters: the global
sections of `Z` integral over `k` form a field (Stacks tag 04MI), and a common section of the two
morphisms restricts on that field to an injection into `k` fixing both copies of `k`. This needs
the two copies of `k` to lie in *one* such field, which is the independence of the integral
closure from the base field, Stacks tag 04MK
(`AlgebraicGeometry.integralClosure_baseField_toSubring_eq`).

## Main results

* `AlgebraicGeometry.eq_of_common_section_to_spec_field`: two morphisms locally of finite type
  from a connected reduced scheme to the spectrum of a field which admit a common section are
  equal.
* `AlgebraicGeometry.GroupoidScheme.topologicalKrullDim_arrows_eq_stabilizer`: the arrow scheme
  and the stabilizer of a groupoid scheme over a field have the same dimension.

## Implementation notes

That the object scheme is the spectrum of a field is expressed by an isomorphism of schemes, and
the finite type hypotheses are imposed on the underlying morphisms of the source and target of
the groupoid scheme, as in
`StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension`.

The algebra structure on global sections used below is the one induced by the second of the two
morphisms, so that tag 04MI applies to it directly; tag 04MK is then what puts the first copy of
the base field inside the same integral closure.

## References

* [Stacks Project, Tag 04MQ](https://stacks.math.columbia.edu/tag/04MQ)
* [Stacks Project, Tag 04MK](https://stacks.math.columbia.edu/tag/04MK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Stacks tag 04MK, read on elements: on a connected reduced scheme locally of finite type over
each of two fields, a global section integral over the first base field is integral over the
second.

This is `AlgebraicGeometry.integralClosure_baseField_toSubring_eq` with the two integral closures
compared pointwise. Keeping the two fields distinct here is what lets the algebra instances they
induce on global sections be told apart by instance search. -/
private theorem isIntegralElem_baseField_of_isIntegralElem (k₁ k₂ : Type u) [Field k₁] [Field k₂]
    (X : Scheme.{u}) (a : X ⟶ Spec (.of k₁)) (b : X ⟶ Spec (.of k₂))
    [LocallyOfFiniteType a] [LocallyOfFiniteType b] [ConnectedSpace X] [IsReduced X]
    (s : Γ(X, ⊤)) (hs : ((Scheme.ΓSpecIso (.of k₁)).inv ≫ a.appTop).hom.IsIntegralElem s) :
    ((Scheme.ΓSpecIso (.of k₂)).inv ≫ b.appTop).hom.IsIntegralElem s := by
  let _ : Algebra k₁ Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k₁)).inv ≫ a.appTop).hom.toAlgebra
  let _ : Algebra k₂ Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k₂)).inv ≫ b.appTop).hom.toAlgebra
  exact Subalgebra.mem_toSubring.mp
    ((SetLike.ext_iff.mp (integralClosure_baseField_toSubring_eq k₁ k₂ X a b) s).mp
      (Subalgebra.mem_toSubring.mpr hs))

/-- Two morphisms locally of finite type from a connected reduced scheme to the spectrum of a
field which admit a common section are equal.

The elements of the ring of global sections integral over the base field along either morphism
form a field (Stacks tag 04MI), and tag 04MK says these two fields are the same subring; a
common section evaluates injectively on it and fixes both copies of the base field. -/
theorem eq_of_common_section_to_spec_field
    (k : Type u) [Field k] (X : Scheme.{u})
    (f g : X ⟶ Spec (.of k)) (σ : Spec (.of k) ⟶ X) (hσf : σ ≫ f = 𝟙 _) (hσg : σ ≫ g = 𝟙 _)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [ConnectedSpace X] [IsReduced X] :
    f = g := by
  let ψf : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let ψg : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom
  let ev : Γ(X, ⊤) →+* k := (σ.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
  let _ : Algebra k Γ(X, ⊤) := ψg.toAlgebra
  let A : Subalgebra k Γ(X, ⊤) := integralClosure k Γ(X, ⊤)
  have hAfield : IsField A := by
    simpa [A] using AlgebraicGeometry.integralClosure_globalSections_isField k X g
  -- The section evaluates injectively on `A`, since `A` is a field.
  have hker : ∀ c : A, ev c.1 = 0 → c = 0 := by
    intro c hc
    by_contra hne
    obtain ⟨d, hd⟩ := hAfield.mul_inv_cancel hne
    exact one_ne_zero (by simpa [hc] using (congrArg (fun z : A => ev z.1) hd).symm : (1 : k) = 0)
  -- Both copies of `k` land in `A`.
  have hmem (h : X ⟶ Spec (.of k)) [LocallyOfFiniteType h] (a : k) :
      ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop).hom a ∈ A :=
    isIntegralElem_baseField_of_isIntegralElem k k X h g _ (RingHom.isIntegralElem_map _)
  -- Evaluating at the section is the identity on either copy of `k`.
  have eval_comp (h : X ⟶ Spec (.of k)) (hσh : σ ≫ h = 𝟙 _) (a : k) :
      ev (((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop).hom a) = a := by
    have happR : σ.appTop.hom.comp h.appTop.hom = RingHom.id _ :=
      congrArg CommRingCat.Hom.hom (by
        simp only [← Scheme.Hom.comp_appTop, hσh, Scheme.Hom.id_appTop] : h.appTop ≫ σ.appTop = 𝟙 _)
    show ((((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop ≫ σ.appTop ≫
      (Scheme.ΓSpecIso (.of k)).hom).hom) a) = a
    simp [RingHom.comp_assoc, happR]
  -- Hence the two ring maps agree, and so do the two morphisms.
  apply ext_to_Spec
  apply CommRingCat.Hom.ext
  ext a
  show ψf a = ψg a
  have hsub : (⟨ψf a, hmem f a⟩ : A) - ⟨ψg a, hmem g a⟩ = 0 := by
    refine hker _ ?_
    show ev (ψf a - ψg a) = 0
    rw [map_sub, eval_comp f hσf, eval_comp g hσg, sub_self]
  exact congrArg Subtype.val (sub_eq_zero.mp hsub)

namespace GroupoidScheme

/-- **Stacks Project, Tag 04MQ.** The arrow scheme of a groupoid scheme whose object scheme is
the spectrum of a field has the same dimension as its stabilizer group scheme, provided both
structure morphisms are locally of finite type. -/
@[stacks 04MQ]
theorem topologicalKrullDim_arrows_eq_stabilizer
    {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (e : G.objects.left ≅ Spec (.of k))
    [LocallyOfFiniteType G.source.left] [LocallyOfFiniteType G.target.left] :
    topologicalKrullDim G.arrows.left = topologicalKrullDim (stabilizer G).left := by
  have : Subsingleton G.objects.left :=
    ⟨fun _ _ => e.hom.homeomorph.injective (Subsingleton.elim _ _)⟩
  have : IsSeparated G.objects.hom :=
    isSeparated_of_injective G.objects.hom fun a b _ => Subsingleton.elim a b
  have : IsClosedImmersion (stabilizerArrow G) := by
    have hdiag : IsClosedImmersion (diagonal G).left := by
      show IsClosedImmersion (Limits.pullback.diagonal G.objects.hom)
      infer_instance
    exact IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (overFibreProduct_isPullback (sourceTarget G) (diagonal G)).flip hdiag
  have : IsClosedImmersion G.identity.left :=
    isClosedImmersion_of_comp_eq_id G.source.left G.identity.left
      (identity_left_comp_source_left G)
  let p : Spec (.of k) ⟶ G.arrows.left := e.inv ≫ G.identity.left
  have : IsClosedImmersion p := inferInstance
  let x : G.arrows.left := p (default : Spec (.of k))
  have hprange : Set.range p = {x} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨default, rfl⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact congrArg (fun w : Spec (.of k) => p w) (Subsingleton.elim z default)
  let Z : Set G.arrows.left := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents _ := irreducibleComponent_mem_irreducibleComponents x
  let Zc : Closeds G.arrows.left := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let I : G.arrows.left.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Zc
  have hIrange : Set.range I.subschemeι = Z :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Zc
  have : IsReduced I.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal Zc
  have : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme G.arrows.left I (hIrange ▸ hZ.1)
  obtain ⟨σ, hσ⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support
    I p).2 (by
      rw [hprange, Set.singleton_subset_iff, ← I.range_subschemeι, hIrange]
      exact mem_irreducibleComponent)
  have hsection (u : G.arrows.left ⟶ G.objects.left) (hu : G.identity.left ≫ u = 𝟙 _) :
      σ ≫ (I.subschemeι ≫ u ≫ e.hom) = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, hσ]
    simp [p, Category.assoc, hu]
  have hfg : I.subschemeι ≫ G.source.left ≫ e.hom = I.subschemeι ≫ G.target.left ≫ e.hom :=
    eq_of_common_section_to_spec_field k I.subscheme _ _ σ
      (hsection _ (identity_left_comp_source_left G))
      (hsection _ (identity_left_comp_target_left G))
  have hst : I.subschemeι ≫ G.source.left = I.subschemeι ≫ G.target.left :=
    (cancel_mono e.hom).mp (by simpa only [Category.assoc] using hfg)
  let a : Over.mk (I.subschemeι ≫ G.arrows.hom) ⟶ G.arrows := Over.homMk I.subschemeι
  let o := a ≫ G.source
  have htarget : a ≫ G.target = o := Over.OverMorphism.ext hst.symm
  have hpull : a ≫ sourceTarget G = o ≫ diagonal G := by
    apply hom_ext
    · simp only [Category.assoc, sourceTarget, diagonal, lift_fst, Category.comp_id]
      exact htarget
    · simp only [Category.assoc, sourceTarget, diagonal, lift_snd, Category.comp_id]
      rfl
  let q : I.subscheme ⟶ (stabilizer G).left := (pullback.lift a o hpull).left
  have hfactor : q ≫ stabilizerArrow G = I.subschemeι := by
    have h := congrArg Over.Hom.left (pullback.lift_fst a o hpull)
    rw [Over.comp_left] at h
    exact h
  have : IsClosedImmersion q := by
    have : IsClosedImmersion (q ≫ stabilizerArrow G) := hfactor ▸ inferInstance
    exact .of_comp_isClosedImmersion q (stabilizerArrow G)
  have hsubDim : topologicalKrullDim I.subscheme = topologicalKrullDim Z :=
    IsHomeomorph.topologicalKrullDim_eq _
      ((IsPreimmersion.isEmbedding I.subschemeι).toHomeomorph.trans
        (Homeomorph.setCongr hIrange)).isHomeomorph
  refine le_antisymm ?_
    (stabilizerArrow G).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  have hdimZ : topologicalKrullDim G.arrows.left = topologicalKrullDim Z := by
    rw [topologicalKrullDim_arrows_eq_topologicalKrullDimAt G e x,
      topologicalKrullDimAt_eq_iSup_irreducibleComponents k G.arrows.left (G.source.left ≫ e.hom) x]
    refine le_antisymm (iSup₂_le fun W hW => (equidimensional_arrows G e W hW.1 _ hZ).le) ?_
    exact le_iSup_of_le _ (le_iSup_of_le ⟨hZ, mem_irreducibleComponent⟩ le_rfl)
  rw [hdimZ, ← hsubDim]
  exact q.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le

end GroupoidScheme

end AlgebraicGeometry

end
