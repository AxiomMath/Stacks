module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection

/-!
# Standard syntomic refinements of syntomic coverings

Every syntomic covering of an affine scheme admits a finite refinement by affine schemes whose
maps to the target are standard syntomic, and the refining schemes may be chosen as affine open
subschemes of members of the original covering. So the standard syntomic coverings of an affine
scheme are cofinal among its syntomic coverings, which is what makes the big affine syntomic
site a dense subsite of the big syntomic site.

## Main results

* `AlgebraicGeometry.exists_finite_affine_standardSyntomic_refinement` — a finite standard
  syntomic refinement of a syntomic covering of an affine scheme.
* `AlgebraicGeometry.syntomic_of_standardSyntomic` — a standard syntomic morphism is syntomic.
* `AlgebraicGeometry.standardSyntomic_of_sourceIso` — standard syntomicity only depends on the
  source up to isomorphism over the target.
* `AlgebraicGeometry.relativeGCI_of_baseRingEquiv` — being a relative global complete
  intersection is invariant under an isomorphism of the base ring.

## Implementation notes

The original covering is a `CategoryTheory.PreZeroHypercover` together with the syntomic
covering condition, and the refining family is an `AlgebraicGeometry.Scheme.AffineCover`, so its
members are affine by construction. The refinement itself is a morphism of
pre-zero-hypercovers, and requiring each of its components to be an open immersion says that
every refining member is an open affine subscheme of the selected member of the original
covering.

Around each point of the target one affine open of the covering member is chosen on which the
restricted morphism is standard syntomic, which is the affine-local characterization of
syntomicity at a point. Finitely many of those suffice because a syntomic morphism is
universally open, so each chosen piece has open image, and the target is quasi-compact.

Passing from the restriction `U ⟶ V` furnished by that characterization to the morphism
`Spec Γ(X, W) ⟶ T` the refinement needs changes both source and base: the source by an
isomorphism of affine schemes, handled by `standardSyntomic_of_sourceIso`, and the base along
the isomorphism `Γ(⊤, ⊤) ≅ Γ(T, ⊤)`, handled by `relativeGCI_of_baseRingEquiv`, which is the
base change of a relative global complete intersection along a ring isomorphism.

## References

* [Stacks Project, Tag 0228](https://stacks.math.columbia.edu/tag/0228)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- A standard syntomic morphism of affine schemes is syntomic. -/
public lemma syntomic_of_standardSyntomic {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    {f : X ⟶ S} (hf : IsStandardSyntomic f) : Syntomic f := by
  intro x
  rw [syntomicAt_iff]
  refine ⟨⟨⊤, isAffineOpen_top X⟩, by simp, ⟨⊤, isAffineOpen_top S⟩, by simp, ?_⟩
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have hmap : f.appTop = f.appLE (⊤ : S.Opens) (⊤ : X.Opens) le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  let : Algebra.IsRelativeGlobalCompleteIntersection Γ(S, ⊤) Γ(X, ⊤) := hf
  rw [← hmap]
  exact Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection Γ(S, ⊤) Γ(X, ⊤)

/-- Standard syntomicity is transported along an isomorphism of the source commuting with the
two structure morphisms. -/
public lemma standardSyntomic_of_sourceIso {X X' S : Scheme.{u}} [IsAffine X]
    [IsAffine X'] [IsAffine S] (f : X ⟶ S) (g : X' ⟶ S) (e : X ≅ X')
    (heq : e.hom ≫ g = f) (hf : IsStandardSyntomic f) :
    IsStandardSyntomic g := by
  have : IsIso e.hom.appTop := by
    change IsIso (e.hom.app ⊤)
    infer_instance
  let α : Γ(X', ⊤) ≃+* Γ(X, ⊤) := RingEquiv.ofBijective e.hom.appTop.hom
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance)
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(X', ⊤) := g.appTop.hom.toAlgebra
  have hmap : e.hom.appTop.hom.comp g.appTop.hom = f.appTop.hom := by
    have h := congrArg Scheme.Hom.appTop heq
    rw [Scheme.Hom.comp_appTop] at h
    exact congrArg (fun k : CommRingCat.Hom _ _ => k.hom) h
  let ea : Γ(X, ⊤) ≃ₐ[Γ(S, ⊤)] Γ(X', ⊤) :=
    { α.symm with
      commutes' := fun r => by
        apply α.injective
        change α (α.symm (f.appTop.hom r)) = α (g.appTop.hom r)
        rw [α.apply_symm_apply]
        exact (congrArg (fun k => k r) hmap).symm }
  let : Algebra.IsRelativeGlobalCompleteIntersection Γ(S, ⊤) Γ(X, ⊤) := hf
  change Algebra.IsRelativeGlobalCompleteIntersection Γ(S, ⊤) Γ(X', ⊤)
  exact Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv ea

/-- Being a relative global complete intersection is invariant under replacing the base ring by
an isomorphic one. -/
public lemma relativeGCI_of_baseRingEquiv {R₀ R A : Type u} [CommRing R₀]
    [CommRing R] [CommRing A] (e : R₀ ≃+* R) (f₀ : R₀ →+* A) (f : R →+* A)
    (hcomp : f₀ = f.comp e.toRingHom)
    (hf₀ : letI : Algebra R₀ A := f₀.toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection R₀ A) :
    letI : Algebra R A := f.toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection R A := by
  let : Algebra R₀ R := e.toRingHom.toAlgebra
  let : Algebra R₀ A := f₀.toAlgebra
  let : Algebra R A := f.toAlgebra
  let : IsScalarTower R₀ R A := IsScalarTower.of_algebraMap_eq fun x =>
    congrFun (congrArg DFunLike.coe hcomp) x
  let : IsScalarTower R₀ A A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsPushout R₀ A R A :=
    Algebra.IsPushout.of_bijective_left (R := R₀) (A := R) (T := A) e.bijective
  let : Algebra.IsRelativeGlobalCompleteIntersection R₀ A := hf₀
  exact Algebra.IsRelativeGlobalCompleteIntersection.baseChange R₀ A R A

/-- A restriction of `f` to an affine open of the source over the whole of an affine target is
standard syntomic exactly when the corresponding morphism out of the spectrum of that open's
sections is. -/
private lemma standardSyntomic_from_resLE {X T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ T) (W : X.Opens) (hW : IsAffineOpen W)
    [IsAffine W.toScheme] [IsAffine (⊤ : T.Opens).toScheme]
    (hWT : W ≤ f ⁻¹ᵁ (⊤ : T.Opens))
    (hstd : IsStandardSyntomic (f.resLE (⊤ : T.Opens) W hWT)) :
    IsStandardSyntomic (hW.fromSpec ≫ f) := by
  let f₀ := f.resLE (⊤ : T.Opens) W hWT
  let f' := f₀ ≫ T.topIso.hom
  let β : Γ((⊤ : T.Opens).toScheme, ⊤) ≃+* Γ(T, ⊤) :=
    (⊤ : T.Opens).topIso.commRingCatIsoToRingEquiv
  have hbase : f₀.appTop.hom = f'.appTop.hom.comp β.toRingHom := by
    have hcomp : f'.appTop.hom = f₀.appTop.hom.comp T.topIso.hom.appTop.hom := by
      change (f₀ ≫ T.topIso.hom).appTop.hom = _
      rw [Scheme.Hom.comp_appTop]
      rfl
    have htop : T.topIso.hom.appTop = (⊤ : T.Opens).topIso.inv := rfl
    have hT : T.topIso.hom.appTop.hom.comp β.toRingHom = RingHom.id _ := by
      rw [htop]
      change β.symm.toRingHom.comp β.toRingHom = RingHom.id _
      ext x
      exact β.symm_apply_apply x
    rw [hcomp, RingHom.comp_assoc, hT, RingHom.comp_id]
  have hfstd : IsStandardSyntomic f' := by
    let : Algebra Γ(T, ⊤) Γ(W.toScheme, ⊤) := f'.appTop.hom.toAlgebra
    change Algebra.IsRelativeGlobalCompleteIntersection Γ(T, ⊤) Γ(W.toScheme, ⊤)
    exact relativeGCI_of_baseRingEquiv β f₀.appTop.hom f'.appTop.hom hbase hstd
  have heq : hW.isoSpec.hom ≫ (hW.fromSpec ≫ f) = f' := by
    dsimp [f₀, f']
    rw [← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
    exact (Scheme.Hom.resLE_comp_ι f hWT).symm
  exact standardSyntomic_of_sourceIso f' (hW.fromSpec ≫ f) hW.isoSpec heq hfstd

/-- **Stacks Project, Tag 0228.** A syntomic covering of an affine scheme has a finite
refinement by affine schemes which are standard syntomic over the target; each member of the
refinement is an open subscheme of a member of the original covering. -/
@[stacks 0228]
public theorem exists_finite_affine_standardSyntomic_refinement
    {T : Scheme.{u}} [IsAffine T] (U : PreZeroHypercover.{v} T)
    (hU : IsSyntomicCovering U.X U.f) :
    ∃ (V : T.AffineCover.{u} (@Syntomic.{u}))
        (refinement : V.cover.toPreZeroHypercover.Hom U),
      Finite V.I₀ ∧
        (∀ j, IsStandardSyntomic (V.f j)) ∧
          ∀ j, IsOpenImmersion (refinement.h₀ j) := by
  have hcov : ∀ t : T, ∃ i y, U.f i y = t := fun t => by
    simpa only [Set.mem_iUnion, Set.mem_range] using Set.eq_univ_iff_forall.mp hU.2 t
  let i (t : T) : U.I₀ := (hcov t).choose
  let y (t : T) : U.X (i t) := (hcov t).choose_spec.choose
  have hy (t : T) : U.f (i t) (y t) = t := (hcov t).choose_spec.choose_spec
  let data (t : T) :=
    ((syntomicAt_tfae (U.f (i t)) (y t)
      ⟨⊤, isAffineOpen_top T⟩ (by simp)).out 1 2).mp (hU.1 (i t) (y t))
  let W (t : T) : (U.X (i t)).Opens := (data t).choose.1
  let hW (t : T) : IsAffineOpen (W t) := (data t).choose.2
  let hxW (t : T) : y t ∈ W t := (data t).choose_spec.1
  let hWT (t : T) : W t ≤ (U.f (i t)) ⁻¹ᵁ (⊤ : T.Opens) := (data t).choose_spec.2.1
  let : ∀ t : T, IsAffine (W t).toScheme := hW
  let : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
  let hstd (t : T) : IsStandardSyntomic
      ((U.f (i t)).resLE (⊤ : T.Opens) (W t) (hWT t)) :=
    (data t).choose_spec.2.2
  let g (t : T) : Spec Γ(U.X (i t), W t) ⟶ T := (hW t).fromSpec ≫ U.f (i t)
  have hrange (t : T) : Set.range (g t) = U.f (i t) '' (W t : Set (U.X (i t))) := by
    rw [← (hW t).range_fromSpec, ← Set.range_comp]
    rfl
  have hopen (t : T) : IsOpen (Set.range (g t)) := by
    let : UniversallyOpen (U.f (i t)) :=
      universallyOpen_of_syntomic (hU.1 (i t))
    rw [hrange]
    exact (Scheme.Hom.isOpenMap (U.f (i t))) _ (W t).isOpen
  have hmem (t : T) : t ∈ Set.range (g t) := by
    rw [hrange]
    exact ⟨y t, hxW t, hy t⟩
  obtain ⟨s, hsU⟩ := CompactSpace.elim_nhds_subcover
    (fun t : T => Set.range (g t)) (fun t => (hopen t).mem_nhds (hmem t))
  have hs : ∀ t : T, ∃ q : s, t ∈ Set.range (g q.1) := by
    intro t
    have ht : t ∈ (⊤ : Set T) := trivial
    rw [← hsU, Set.mem_iUnion] at ht
    rcases ht with ⟨q, _, ⟨hq, rfl⟩, hqt⟩
    exact ⟨⟨q, hq⟩, hqt⟩
  have hstdg (q : s) : IsStandardSyntomic (g q.1) :=
    standardSyntomic_from_resLE (U.f (i q.1)) (W q.1) (hW q.1) (hWT q.1) (hstd q.1)
  let V : T.AffineCover.{u} (@Syntomic.{u}) :=
    { I₀ := s
      X q := Γ(U.X (i q.1), W q.1)
      f q := g q.1
      idx t := (hs t).choose
      covers t := (hs t).choose_spec
      map_prop q := syntomic_of_standardSyntomic (hstdg q) }
  let refinement : V.cover.toPreZeroHypercover.Hom U :=
    { s₀ q := i q.1
      h₀ q := (hW q.1).fromSpec
      w₀ q := rfl }
  refine ⟨V, refinement, ?_, ?_, ?_⟩
  · dsimp [V]
    infer_instance
  · exact hstdg
  · intro q
    exact (inferInstance : IsOpenImmersion (hW q.1).fromSpec)

end AlgebraicGeometry
