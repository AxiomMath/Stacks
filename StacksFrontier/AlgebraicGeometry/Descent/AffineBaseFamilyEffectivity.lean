module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineStandardFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectivityAlongFpqcCovering
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityComparison
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent for affine morphisms over an affine base

Let `f i : X i ⟶ S` be an fpqc covering of an affine scheme `S`. Every descent datum relative to
that covering whose structure morphisms are affine is effective.

## Main results

* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isEffective_coproduct`: a descent datum
  for a family is effective as soon as the corresponding descent datum for the morphism out of
  the disjoint union of the family is effective.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_finiteAffineFlat`: a
  descent datum with affine structure morphisms, relative to a finite flat covering of an affine
  scheme by affine schemes, is effective.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_affineBase`: a descent
  datum with affine structure morphisms, relative to an arbitrary fpqc covering of an affine
  scheme, is effective.

## References

* [Stacks Project, Tag 023X](https://stacks.math.columbia.edu/tag/023X)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.DescentData

open CategoryTheory CategoryTheory.Limits

section Universal

variable {I : Type v} [Small.{u} I]

/-- A cofan of schemes which is a colimit is a universal colimit. -/
private lemma cofanIsUniversalColimit {Y : I → Scheme.{u}} {c : Cofan Y} (hc : IsColimit c) :
    IsUniversalColimit c :=
  (sigma_universal Y).of_iso ((coproductIsCoproduct Y).uniqueUpToIso hc)

end Universal

section Comparison

variable {I : Type v} [Small.{u} I] {S : Scheme.{u}} {X : I → Scheme.{u}}

/-- The canonical map `U ×_S X i ⟶ U ×_S (∐ i, X i)` attached to the inclusion of a summand. -/
private def sigmaSummandLift (f : ∀ i, X i ⟶ S) (U : Over S) (i : I) :
    pullback U.hom (f i) ⟶ pullback U.hom (Sigma.desc f) :=
  pullback.lift (pullback.fst U.hom (f i)) (pullback.snd U.hom (f i) ≫ Sigma.ι X i)
    (by rw [Category.assoc, Sigma.ι_desc]; exact pullback.condition)

/-- The summand inclusion map commutes with the projection to `U`. -/
private lemma sigmaSummandLift_fst (f : ∀ i, X i ⟶ S) (U : Over S) (i : I) :
    sigmaSummandLift f U i ≫ pullback.fst U.hom (Sigma.desc f) = pullback.fst U.hom (f i) :=
  pullback.lift_fst _ _ _

/-- The summand inclusion map commutes with the projection to `∐ i, X i`. -/
private lemma sigmaSummandLift_snd (f : ∀ i, X i ⟶ S) (U : Over S) (i : I) :
    sigmaSummandLift f U i ≫ pullback.snd U.hom (Sigma.desc f) =
      pullback.snd U.hom (f i) ≫ Sigma.ι X i :=
  pullback.lift_snd _ _ _

/-- `U ×_S X i` is the fibre product of `U ×_S (∐ i, X i)` and `X i` over `∐ i, X i`. -/
private lemma isPullback_sigmaSummandLift (f : ∀ i, X i ⟶ S) (U : Over S) (i : I) :
    IsPullback (sigmaSummandLift f U i) (pullback.snd U.hom (f i))
      (pullback.snd U.hom (Sigma.desc f)) (Sigma.ι X i) := by
  have ht : IsPullback (pullback.fst U.hom (Sigma.desc f))
      (pullback.snd U.hom (Sigma.desc f)) U.hom (Sigma.desc f) :=
    IsPullback.of_hasPullback _ _
  have hs : IsPullback (sigmaSummandLift f U i ≫ pullback.fst U.hom (Sigma.desc f))
      (pullback.snd U.hom (f i)) U.hom (Sigma.ι X i ≫ Sigma.desc f) := by
    rw [sigmaSummandLift_fst, Sigma.ι_desc]
    exact IsPullback.of_hasPullback _ _
  exact hs.of_right (sigmaSummandLift_snd f U i) ht

/-- The comparison map `∐ i, (U ×_S X i) ⟶ U ×_S (∐ i, X i)`. -/
private def sigmaSummandDesc (f : ∀ i, X i ⟶ S) (U : Over S) :
    (∐ fun i ↦ pullback U.hom (f i)) ⟶ pullback U.hom (Sigma.desc f) :=
  Sigma.desc (sigmaSummandLift f U)

/-- The comparison map preserves the projection to `U` summand by summand. -/
@[reassoc]
private lemma sigmaSummandDesc_fst (f : ∀ i, X i ⟶ S) (U : Over S) (i : I) :
    Sigma.ι (fun i ↦ pullback U.hom (f i)) i ≫ sigmaSummandDesc f U ≫
        pullback.fst U.hom (Sigma.desc f) = pullback.fst U.hom (f i) := by
  rw [← Category.assoc, sigmaSummandDesc, Sigma.ι_desc, sigmaSummandLift_fst]

/-- The comparison map lies over `∐ i, X i`. -/
private lemma sigmaSummandDesc_snd (f : ∀ i, X i ⟶ S) (U : Over S) :
    sigmaSummandDesc f U ≫ pullback.snd U.hom (Sigma.desc f) =
      Limits.Sigma.map (fun i ↦ pullback.snd U.hom (f i)) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, sigmaSummandDesc, Sigma.ι_desc, Limits.Sigma.ι_map,
    sigmaSummandLift_snd]

/-- The comparison map is an isomorphism, since coproducts of schemes are universal. -/
private lemma isIso_sigmaSummandDesc (f : ∀ i, X i ⟶ S) (U : Over S) :
    IsIso (sigmaSummandDesc f U) := by
  apply (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk (pullback U.hom (Sigma.desc f)) (sigmaSummandLift f U))).mp
  exact sigma_universal X
    (Cofan.mk (pullback U.hom (Sigma.desc f)) (sigmaSummandLift f U))
    (Discrete.natTrans (fun i ↦ pullback.snd U.hom (f i.as)))
    (pullback.snd U.hom (Sigma.desc f))
    (by
      refine NatTrans.ext (funext fun i ↦ ?_)
      obtain ⟨i⟩ := i
      exact (sigmaSummandLift_snd f U i).symm)
    (.of_discrete _)
    (fun i ↦ isPullback_sigmaSummandLift f U i.as)

/-- **The coproduct of the base changes of `U` along a family is the base change of `U` along the
morphism out of the disjoint union of the family**, as schemes over `∐ i, X i`. -/
private def sigmaPullbackIso (f : ∀ i, X i ⟶ S) (U : Over S) :
    Over.mk (Limits.Sigma.map (fun i ↦ pullback.snd U.hom (f i))) ≅
      (Over.pullback (Sigma.desc f)).obj U :=
  haveI := isIso_sigmaSummandDesc f U
  Over.isoMk (asIso (sigmaSummandDesc f U)) (sigmaSummandDesc_snd f U)

/-- Two morphisms out of the fibre product on which the gluing isomorphism of the descent datum
for the disjoint union lives agree as soon as they agree on each pairwise fibre product of the
original family. -/
private lemma sourceHomExt {f : ∀ i, X i ⟶ S} (T : FamilyCoproductEquivalence f)
    (D : DescentData f) {Z : Scheme.{u}}
    {p q : pullback (((T.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f)
      (Sigma.desc f) ⟶ Z}
    (h : ∀ i j, T.sourceMap D i j ≫ p = T.sourceMap D i j ≫ q) : p = q := by
  let c := Cofan.mk ((T.equivalence.functor.obj D).obj ()).left
    (fun i ↦ Sigma.ι (fun i ↦ (D.obj i).left) i ≫ (T.objIso D).inv.left)
  have hc : IsColimit c :=
    (coproductIsCoproduct (fun i ↦ (D.obj i).left)).ofIsoColimit
      (Cocone.ext ((Over.forget _).mapIso (T.objIso D)).symm (by intro j; rfl))
  let d := Cofan.mk _ (fun r : I × I ↦ T.sourceMap D r.1 r.2)
  have hd : Nonempty (IsColimit d) :=
    (cofanIsUniversalColimit hc).nonempty_isColimit_prod_of_isPullback
      (sigma_universal X) (fun i ↦ (D.obj i).hom ≫ f i) f
      (((T.equivalence.functor.obj D).obj ()).hom ≫ Sigma.desc f) (Sigma.desc f)
      (fun i j ↦ IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
      (d := d) (Iso.refl _)
      (by intro i; dsimp [c]; simp [Category.assoc, Over.w_assoc])
      (by intro i; simp)
      (by intro i j; simpa [d, c] using T.sourceMap_fst D i j)
      (by intro i j; simpa [d] using T.sourceMap_snd D i j)
  exact Cofan.IsColimit.hom_ext hd.some p q (fun r ↦ h r.1 r.2)

/-- The underlying scheme of the descent datum for the disjoint union obtained from the canonical
descent datum of `U`, identified with `U ×_S (∐ i, X i)`. -/
private def bridgeComponentIso (f : ∀ i, X i ⟶ S) (T : FamilyCoproductEquivalence f)
    (U : Over S) :
    (T.equivalence.functor.obj (CanonicalDatum.datum f U)).obj () ≅
      (Over.pullback (Sigma.desc f)).obj U :=
  T.objIso (CanonicalDatum.datum f U) ≪≫ sigmaPullbackIso f U

/-- The identification of the underlying scheme with `U ×_S (∐ i, X i)`, followed by the
projection to `U`, restricts on the summand `U ×_S X i` to the projection to `U`. -/
private lemma bridgeComponentIso_proj (f : ∀ i, X i ⟶ S) (T : FamilyCoproductEquivalence f)
    (U : Over S) (r : I) :
    Sigma.ι (fun i ↦ ((CanonicalDatum.datum f U).obj i).left) r ≫
        (T.objIso (CanonicalDatum.datum f U)).inv.left ≫
        (bridgeComponentIso f T U).hom.left ≫ pullback.fst U.hom (Sigma.desc f) =
      pullback.fst U.hom (f r) := by
  have hcancel : (T.objIso (CanonicalDatum.datum f U)).inv.left ≫
      (bridgeComponentIso f T U).hom.left ≫ pullback.fst U.hom (Sigma.desc f) =
      (sigmaPullbackIso f U).hom.left ≫ pullback.fst U.hom (Sigma.desc f) :=
    (congrArg (fun k ↦ (T.objIso (CanonicalDatum.datum f U)).inv.left ≫ k)
        (Category.assoc (T.objIso (CanonicalDatum.datum f U)).hom.left
          (sigmaPullbackIso f U).hom.left (pullback.fst U.hom (Sigma.desc f)))).trans
      (Iso.inv_hom_id_assoc ((Over.forget (∐ X)).mapIso (T.objIso (CanonicalDatum.datum f U))) _)
  exact (congrArg
      (fun k ↦ Sigma.ι (fun i ↦ ((CanonicalDatum.datum f U).obj i).left) r ≫ k) hcancel).trans
    (sigmaSummandDesc_fst f U r)

/-- **The canonical descent datum of `U` for a family is carried to the canonical descent datum
of `U` for the morphism out of the disjoint union of the family.** -/
private def bridgeIso (f : ∀ i, X i ⟶ S) (T : FamilyCoproductEquivalence f) (U : Over S) :
    T.equivalence.functor.obj (CanonicalDatum.datum f U) ≅
      CanonicalDatum.datum (fun _ : Unit ↦ Sigma.desc f) U := by
  refine isoCanonicalDatum _ U (fun _ ↦ bridgeComponentIso f T U) fun i j ↦ ?_
  obtain rfl : i = () := Subsingleton.elim _ _
  obtain rfl : j = () := Subsingleton.elim _ _
  refine sourceHomExt T (CanonicalDatum.datum f U) fun p q ↦ ?_
  rw [← Category.assoc, T.gluing (CanonicalDatum.datum f U) p q, Category.assoc,
    reassoc_of% (T.targetMap_snd (CanonicalDatum.datum f U) p q),
    reassoc_of% (T.sourceMap_fst (CanonicalDatum.datum f U) p q),
    bridgeComponentIso_proj f T U q, bridgeComponentIso_proj f T U p]
  exact CanonicalDatum.datum_gluing_proj f U p q

end Comparison

/-- **Effectivity transfers from the disjoint union to the family.** Let `f i : X i ⟶ S` be a
family of morphisms of schemes and let `D` be a descent datum relative to it. If the descent
datum relative to the single morphism `(∐ i, X i) ⟶ S` corresponding to `D` under the
family–coproduct equivalence is effective, then `D` is effective. -/
theorem isFamilyEffective_of_isEffective_coproduct {I : Type v} [Small.{u} I] {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) (T : FamilyCoproductEquivalence f)
    (D : DescentData f) (h : IsEffective (T.equivalence.functor.obj D)) :
    D.IsFamilyEffective := by
  obtain ⟨U, ⟨φ⟩⟩ := isFamilyEffective_of_isEffective h
  exact ⟨U, ⟨(T.equivalence.fullyFaithfulFunctor.preimageIso (bridgeIso f T U ≪≫ φ))⟩⟩

/-- **Effective descent for affine morphisms along a finite flat covering of an affine scheme by
affine schemes.** Let `S` be affine, let `f i : X i ⟶ S` be a finite family of flat morphisms
with affine sources which is an fpqc covering, and let `D` be a descent datum relative to it
whose structure morphisms are affine. Then `D` is effective. -/
@[sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "(ii), special case",
  sga "3 X 5.4" "special case",
  sga "3 XXIV 3.11.2" "special case"]
theorem isFamilyEffective_of_isAffineHom_of_finiteAffineFlat {I : Type u} [Finite I]
    {S : Scheme.{u}} [IsAffine S] {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hX : ∀ i, IsAffine (X i)) (hflat : ∀ i, Flat (f i))
    (hcov : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hD : ∀ i, IsAffineHom (D.obj i).hom) :
    D.IsFamilyEffective := by
  have : ∀ i, IsAffine (X i) := hX
  have : ∀ i, Flat (f i) := hflat
  have : ∀ i, IsAffineHom (D.obj i).hom := hD
  have (i : I) : IsAffine (D.obj i).left := isAffine_of_isAffineHom (f := (D.obj i).hom)
  have hjs : ∀ x : S, ∃ i, x ∈ Set.range (f i) :=
    ((Scheme.ofArrows_mem_precoverage_iff
      (P := (@Flat : MorphismProperty Scheme.{u}))).mp hcov.2).1
  have hsurj : Surjective (Sigma.desc f) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨i, z, hzy⟩ := hjs y
    refine ⟨Sigma.ι X i z, ?_⟩
    rwa [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  let T := familyCoproductEquivalence f
  let F := T.equivalence.functor.obj D
  have hobj : (F.obj ()).left ≅ (∐ fun i ↦ (D.obj i).left) :=
    (Over.forget (∐ X)).mapIso (T.objIso D)
  have : IsAffine (F.obj ()).left := IsAffine.of_isIso hobj.hom
  exact isFamilyEffective_of_isEffective_coproduct f T D
    (DescentDatum.isEffective_of_isAffineHom_of_surjective_of_flat hsurj inferInstance F
      inferInstance)

/-- **Effective descent for affine morphisms over an affine base.** Let `S` be an affine scheme,
let `f i : X i ⟶ S` be an fpqc covering of `S`, and let `D` be a descent datum relative to it
whose structure morphisms are affine. Then `D` is effective: it is the canonical descent datum of
a scheme over `S`. -/
@[sga "1 VIII 7.4" "partial",
  sga "3 IX 2.3" "partial",
  sga "3 VIII 1.7.2" "(ii), special case",
  sga "3 XXIV 3.11.2" "special case"]
theorem isFamilyEffective_of_isAffineHom_of_affineBase {I : Type u} {S : Scheme.{u}} [IsAffine S]
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hcov : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hD : ∀ i, IsAffineHom (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_of_finiteAffineFlat (P := @IsAffineHom)
    (V := { I₀ := I, X := X, f := f }) hcov
    (fun 𝒱 hfin haff hfl hcov' E hE ↦
      have := hfin
      isFamilyEffective_of_isAffineHom_of_finiteAffineFlat 𝒱.f haff hfl hcov' E hE)
    D hD

end AlgebraicGeometry.DescentData

end

end
