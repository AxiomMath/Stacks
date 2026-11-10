module

public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.Deformation.ArtinCriteria.AlgebraicStackCriterion
public import StacksFrontier.Deformation.ArtinCriteria.VersalShrink
public import StacksFrontier.Deformation.ArtinCriteria.VersalSmoothness

/-!
# A smooth finite-type neighbourhood of a finite-type object

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian
scheme `S`, with diagonal representable by algebraic spaces, satisfying Artin's axioms [1],
[2] and the tangent-space part of [3], all of whose formal objects are effective, with
openness of versality, and let `x₀` be an object of `𝒳` over a quasi-compact finite-type
field point `Spec k ⟶ S` whose image is a point `s` at which the local ring of `S` is a
G-ring.  Then `x₀` extends to an object `x` over a base `U` of finite type over `S` such that
the 1-morphism `(Sch/U)_{fppf} ⟶ 𝒳` attached to `x` by the 2-Yoneda lemma is smooth, and `U`
carries a finite type point `u₀` with residue field `k` at which `x` restricts to `x₀`.

## Main results

* `Deformation.Artin.exists_smooth_finiteType_neighborhood` is **Stacks 07XY**.

## Implementation notes

The three steps of the source proof are the three results composed here: the existence of the
versal finite-type point (`Deformation.Artin.exists_versal_finiteTypePoint`), the shrinking of
its base by openness of versality (`Deformation.Artin.exists_shrink_versal_everywhere`), and
the smoothness of the 2-Yoneda 1-morphism attached to an object versal at every finite type
point (`AlgebraicGeometry.Stack.isRelativelySmooth_of_isVersalAt_finiteTypePoints`).

What the composition has to supply is the transport of the marked point through the shrinking
step.  The arrow `x₀ ⟶ x` produced by the first step factors through the restriction arrow of
the second, because the base of `x₀` is the spectrum of a field whose point lands in the open;
and the residue field of the marked point of the smaller base is identified with `k` by
composing the identification over the larger base with the residue-field isomorphism of the
open immersion.

The openness-of-versality hypothesis is written out rather than named.  It is the body of
`Deformation.Artin.IsOpenVersality (𝒳.val.p ⋙ Over.post B.inclusion) h`, whose second
argument that predicate does not use; but
`Deformation.Artin.not_isFiberedInGroupoids_comp_post` shows that no such `h` exists for a
category fibred in groupoids over the site with a field-valued point, so quantifying over one
would make the statement vacuous.

## References

* [Stacks Project, Tag 07XY](https://stacks.math.columbia.edu/tag/07XY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

/-! ### Transporting a residue-field identification along an open immersion -/

/-- The residue field at a point of an open subscheme, identified with a field through the
identification of the residue field at its image. -/
private def residueFieldEquivOfOpenImmersion {X' X : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (v : X') {k : Type u} [Field k]
    (e : X.residueField (j v) ≃+* k) : X'.residueField v ≃+* k :=
  ((asIso (j.residueFieldMap v)).commRingCatIsoToRingEquiv).symm.trans e

/-- The field-valued point of the open subscheme cut out by
`Deformation.Artin.residueFieldEquivOfOpenImmersion` is the given field-valued point of the
ambient scheme. -/
private theorem residueFieldEquivOfOpenImmersion_spec {X' X : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (v : X') {k : Type u} [Field k]
    (e : X.residueField (j v) ≃+* k) :
    Spec.map (CommRingCat.ofHom (residueFieldEquivOfOpenImmersion j v e).toRingHom) ≫
        X'.fromSpecResidueField v ≫ j =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField (j v) := by
  have hres : j.residueFieldMap v ≫
      CommRingCat.ofHom (residueFieldEquivOfOpenImmersion j v e).toRingHom =
      CommRingCat.ofHom e.toRingHom := by
    ext a
    exact congrArg e
      (((asIso (j.residueFieldMap v)).commRingCatIsoToRingEquiv).symm_apply_apply a)
  have h := congrArg (fun φ => Spec.map φ ≫ X.fromSpecResidueField (j v)) hres
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
  exact h

/-! ### Stacks 07XY -/

/-- **Stacks 07XY.** Let `𝒳` be a category fibred in groupoids over the big fppf site of a
locally Noetherian scheme `S` whose diagonal is representable by algebraic spaces, which is
limit preserving (axiom [1]), satisfies (RS) (axiom [2]) and has finite-dimensional tangent
spaces (the tangent-space half of axiom [3]), all of whose formal objects are effective, for
which versality is open, and let `x₀` be an object of `𝒳` over a quasi-compact finite-type
field point `i₀ : Spec k ⟶ S` whose image is a point `s` at which the local ring of `S` is a
G-ring.

Then there is a base `U = 𝒳.val.p.obj x` of finite type over `S` — locally of finite type and
quasi-compact — an object `x` of `𝒳` over it, and a finite type point `u₀` of `U` with residue
field `k`, such that `x` restricts to `x₀` at `u₀` along a Cartesian arrow `r : x₀ ⟶ x`
realizing that identification of residue fields, and the 1-morphism
`(Sch/U)_{fppf} ⟶ 𝒳` attached to `x` by the 2-Yoneda lemma is smooth.

The proof is the proof of the source: the versal finite-type point of Stacks 07XH, shrunk by
openness of versality, carries a smooth 2-Yoneda 1-morphism by Stacks 0CXM. -/
@[stacks 07XY "the finite-type base, the object over it, its finite type point with residue \
field k, the restriction of that object to x₀ there, and smoothness of the 2-Yoneda morphism \
attached to it"]
public theorem exists_smooth_finiteType_neighborhood
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
      (AlgebraicGeometry.BigFppfOver B S hS))
    (k : Type u) [Field k]
    (i₀ : Spec (.of k) ⟶ S) (x₀ : 𝒳.val.obj)
    (hx₀ : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ = Over.mk i₀)
    (hfinite₀ : LocallyOfFiniteType i₀) (hqc₀ : QuasiCompact i₀)
    (s : S) (hs : i₀ (IsLocalRing.closedPoint k) = s)
    (hdiag : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hlimit : IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳)
    (hRS : SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent :
      ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k]
        (_ : Λ = S.presheaf.stalk s)
        (iΛ : Spec (.of Λ) ⟶ S)
        (_ : HEq iΛ (S.fromSpecStalk s))
        (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = i₀),
        let hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x₀ =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) :=
          hx₀.trans (congrArg Over.mk hbase.symm)
        let D := predeformationCategory iΛ
          (𝒳.val.p ⋙ Over.post B.inclusion) x₀ hx
        letI : Category D.carrier := D.category
        ∀ hD : Deformation.IsDeformationCategory D.projection,
          let 𝓕 := BasedCategory.ofFunctor D.projection
          let hS2 := schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
          letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) :=
            ⟨hD.predeformation⟩
          letI : Fact (Deformation.SchlessingerConditionS2
            (Functor.Elements.π
              (Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
            ⟨hS2⟩
          let F := Deformation.isomorphismClasses 𝓕 hD.predeformation.cofibered
          let T := Deformation.artinianTangentSpace Λ k F
          letI : AddCommGroup T := Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
          letI : Module k T := Deformation.associatedTangentSpaceModuleUnlifted 𝓕
          FiniteDimensional k T)
    (heffective : ∀ ξ : FormalObject B S hS 𝒳.val.p,
      FormalObject.IsEffective B S hS 𝒳.val.p 𝒳.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒳.val.obj) (hy : (𝒳.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : IsGRing (S.presheaf.stalk s)) :
    ∃ (x : 𝒳.val.obj)
      (u₀ : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left)
      (e : ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.residueField u₀ ≃+* k)
      (r : x₀ ⟶ x)
      (f : (AlgebraicGeometry.Stack.schemeFibredCategory B S hS
        (𝒳.val.p.obj x)).val ⥤ᵇ 𝒳.val),
      LocallyOfFiniteType ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom ∧
      QuasiCompact ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).hom ∧
      AlgebraicGeometry.IsFiniteTypePoint u₀ ∧
      𝒳.val.p.IsCartesian (𝒳.val.p.map r) r ∧
      (eqToHom hx₀.symm ≫ (𝒳.val.p ⋙ Over.post B.inclusion).map r).left =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField u₀ ∧
      Nonempty ((Functor.twoYonedaEvaluation 𝒳.val.p (𝒳.val.p.obj x)).obj f ≅
        (⟨x, rfl⟩ : 𝒳.val.p.Fiber (𝒳.val.p.obj x))) ∧
      (∃ hf : AlgebraicGeometry.IsRepresentableByAlgebraicSpaces B S hS f,
        AlgebraicGeometry.Stack.HasRelativePropertyBased.{u, u, u + 1,
            max u v, max (u + 1) v w, u} B S hS
          (AlgebraicGeometry.Space.smoothMorphismProperty B S hS) f hf) := by
  classical
  let : 𝒳.val.p.IsFibered := 𝒳.property.isFibered
  -- Step one: an object over a finite-type base, versal at a finite type point whose residue
  -- field is `k` (Stacks 07XH).
  obtain ⟨x, u₀, e₀, r₀, hfin, hqc, hftp, hb₀, hversal⟩ :=
    exists_versal_finiteTypePoint.{u, v, w} B S hS 𝒳 k i₀ x₀ hx₀ hfinite₀ hqc₀ s hs
      hlimit hRS htangent heffective hG
  -- Step two: shrink the base by openness of versality (Stacks 07XQ).
  obtain ⟨x', rr, v₀, hoi, hvmap, hftp', hfin', hqc', hversal'⟩ :=
    exists_shrink_versal_everywhere.{u, max (u + 1) v w, max u v} B S hS 𝒳.val.p 𝒳.property
      hopen x hfin hqc u₀ hftp hversal
  let : IsOpenImmersion (((𝒳.val.p ⋙ Over.post B.inclusion).map rr).left) := hoi
  have : 𝒳.val.p.IsStronglyCartesian (𝒳.val.p.map rr) rr :=
    𝒳.property.isStronglyCartesian rr
  subst hvmap
  -- The arrow of step one factors through the restriction arrow of step two: the base of `x₀`
  -- is the spectrum of a field whose point is the marked point, which lies in the open.
  obtain ⟨r, hr⟩ := exists_factor_of_closedPoint_mem B hS 𝒳.val.p rr
    (R := k) (eqToIso (congrArg Over.left hx₀)).symm r₀ (by
      have h₁ : (eqToIso (congrArg Over.left hx₀)).symm.hom ≫
          ((𝒳.val.p ⋙ Over.post B.inclusion).map r₀).left =
          (eqToHom hx₀.symm ≫ (𝒳.val.p ⋙ Over.post B.inclusion).map r₀).left := by
        simp only [Over.comp_left, Over.eqToHom_left, Iso.symm_hom, eqToIso.inv]
      rw [h₁, hb₀]
      exact ⟨v₀,
        ((Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)).symm⟩)
  have : 𝒳.val.p.IsStronglyCartesian (𝒳.val.p.map r) r := 𝒳.property.isStronglyCartesian r
  -- Step three: the 2-Yoneda 1-morphism attached to the restricted object is smooth
  -- (Stacks 0CXM, through `isRelativelySmooth_of_isVersalAt_finiteTypePoints`).
  obtain ⟨f, heval, hsmooth⟩ :=
    AlgebraicGeometry.Stack.isRelativelySmooth_of_isVersalAt_finiteTypePoints.{u, v, w}
      B S hS 𝒳 hdiag hRS hlimit x' hfin' hversal'
  refine ⟨x', v₀,
    residueFieldEquivOfOpenImmersion
      (((𝒳.val.p ⋙ Over.post B.inclusion).map rr).left) v₀ e₀,
    r, f, hfin', hqc', hftp', inferInstance, ?_, heval, hsmooth⟩
  -- The base identification for the lifted arrow, read after the monomorphism of step two.
  have hcomp : (eqToHom hx₀.symm ≫ (𝒳.val.p ⋙ Over.post B.inclusion).map r).left ≫
      (((𝒳.val.p ⋙ Over.post B.inclusion).map rr).left) =
      Spec.map (CommRingCat.ofHom e₀.toRingHom) ≫
        ((𝒳.val.p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField
          ((((𝒳.val.p ⋙ Over.post B.inclusion).map rr).left) v₀) := by
    rw [← Over.comp_left, Category.assoc, ← Functor.map_comp, hr]
    exact hb₀
  refine (cancel_mono (((𝒳.val.p ⋙ Over.post B.inclusion).map rr).left)).mp ?_
  rw [hcomp, Category.assoc, residueFieldEquivOfOpenImmersion_spec]

end Deformation.Artin

end
