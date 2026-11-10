module

public import Mathlib.Basic.Countable.Small
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFinitenessFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.CoproductAlgebraicity
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.DescentDataSheavesEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EffectiveOneMemberCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SheafCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional

/-!
# Effectivity of descent data along a countable fppf covering (Stacks 0ADV, part (1))

Let `{f i : X i ⟶ T}` be an fppf covering of algebraic spaces over `S` with a countable index
type. Every descent datum relative to it is effective. This is part (1) of Stacks 0ADV.

The proof is the source's. By Stacks 0ADT the descent datum `(V i, φ i j)` is the descent datum
of a sheaf `F` over `T` with `X i ×_T F = V i`, namely the image of the datum under the inverse of
`AlgebraicGeometry.Space.Descent.fppfDescentDataSheafEquivalence`, and it suffices to show that
`F` is an algebraic space. The coproduct `Y = ∐ X i`, taken in sheaves, is an algebraic space
because the index type is countable (Stacks 02WQ), and the morphism `Y ⟶ T` is surjective, flat
and locally of finite presentation: surjectivity because the covering is jointly surjective,
flatness and local finite presentation because the summand inclusions are jointly surjective as
morphisms of sheaves and the composites are the members of the covering (Stacks 06NR). So
`{Y ⟶ T}` is a one-member fppf covering, and `Y ×_T F` is the coproduct of the `V i`, again an
algebraic space.
The bootstrap theorem, Stacks 04S6, now makes `F` an algebraic space: the projection
`Y ×_T F ⟶ F` is representable by algebraic spaces, surjective, flat and locally of finite
presentation, being a base change of `Y ⟶ T`.

## Main results

* `AlgebraicGeometry.Space.Descent.isAlgebraicSpace_of_isPullback_of_isAlgebraicSpace_sigma`: a
  sheaf over the target of an fppf covering of any size is an algebraic space as soon as the
  coproduct of the members and the coproduct of the fibre products are algebraic spaces. This
  is the argument of the proof of part (1) with the use of countability isolated.
* `AlgebraicGeometry.Space.Descent.isFppfCovering_sigmaDesc`: the morphism from the coproduct of
  the members of a countable fppf covering is a one-member fppf covering.
* `AlgebraicGeometry.Space.Descent.DescentData.isAlgebraicSpace_descended_of_countable`: the
  sheaf a descent datum along a countable fppf covering descends to is an algebraic space.
* `AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_countable`: **Stacks 0ADV,
  part (1)**.
* `AlgebraicGeometry.Space.Descent.DescentData.isEffective_of_isSurjective`: the same for an
  fppf covering of any size one member of which is surjective.

## References

* [Stacks Project, Tag 0ADV](https://stacks.math.columbia.edu/tag/0ADV)
* [Stacks Project, Tag 0ADT](https://stacks.math.columbia.edu/tag/0ADT)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type v} {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : ∀ i, X i ⟶ T}
    {hT : IsAlgebraicSpace B S hS T} {hX : ∀ i, IsAlgebraicSpace B S hS (X i)}

variable (f hT hX) in
/-- The morphism from the coproduct, in sheaves, of the members of a family to its target. -/
def sigmaDesc [Small.{u} ι] :
    (∐ fun i ↦ spaceSheaf (X i) (hX i)) ⟶ spaceSheaf T hT :=
  Sigma.desc fun i ↦ ObjectProperty.homMk (f i)

/-- The `i`-th summand inclusion followed by `sigmaDesc f hT hX` is the member `f i`, as a map of
presheaves. -/
lemma ι_sigmaDesc_hom [Small.{u} ι] (i : ι) :
    (Sigma.ι (fun i ↦ spaceSheaf (X i) (hX i)) i).hom ≫ (sigmaDesc f hT hX).hom = f i := by
  rw [← ObjectProperty.FullSubcategory.comp_hom, sigmaDesc, Sigma.ι_comp_desc]
  rfl

variable [Countable ι] (hX) in
/-- The coproduct of the members of a countable family of algebraic spaces is an algebraic
space. -/
lemma isAlgebraicSpace_sigma :
    IsAlgebraicSpace B S hS (∐ fun i ↦ spaceSheaf (X i) (hX i)).obj :=
  isAlgebraicSpace_sigma_spaceSheaf X hX

/-- **The morphism from the coproduct of the members of an fppf covering is a one-member fppf
covering, as soon as that coproduct is an algebraic space.** The index type may have any size;
algebraicity of the coproduct is the only place where a bound on it can enter. -/
theorem isFppfCovering_sigmaDesc_of_isAlgebraicSpace [Small.{u} ι]
    (hY : IsAlgebraicSpace B S hS (∐ fun i ↦ spaceSheaf (X i) (hX i)).obj)
    (hcov : IsFppfCovering B S hS X f) :
    IsFppfCovering B S hS (fun _ : PUnit.{1} ↦ (∐ fun i ↦ spaceSheaf (X i) (hX i)).obj)
      (fun _ ↦ (sigmaDesc f hT hX).hom) := by
  let Xs : ι → Sheaf (BigFppfOver.topology B S hS) (Type u) := fun i ↦ spaceSheaf (X i) (hX i)
  have hloc : ∀ (U : BigFppfOver B S hS) (s : (∐ Xs).obj.obj (op U)),
      (⨆ i, Presheaf.imageSieve (Sigma.ι Xs i).hom s) ∈ BigFppfOver.topology B S hS U := by
    intro U s
    obtain ⟨R, hR, hRf⟩ := coproduct_locally_factors Xs (∐ Xs) (Sigma.ι Xs)
      (coproductIsCoproduct Xs) s
    refine (BigFppfOver.topology B S hS).superset_covering (fun V g hg ↦ ?_) hR
    obtain ⟨i, y, hy⟩ := hRf g hg
    exact (le_iSup (fun i ↦ Presheaf.imageSieve (Sigma.ι Xs i).hom s) i) _ ⟨y, hy⟩
  refine ⟨hT, fun _ ↦ hY, fun _ ↦ ?_, fun _ ↦ ?_, ?_⟩
  · exact isFlat_of_comp_of_jointlyLocallySurjective B S hS hX hY _ _
      (fun i ↦ by rw [ι_sigmaDesc_hom]; exact hcov.flat i) hloc
  · exact isLocallyOfFinitePresentation_of_comp_of_jointlyLocallySurjective B S hS hX hY _ _
      (fun i ↦ by rw [ι_sigmaDesc_hom]; exact hcov.locallyOfFinitePresentation i) hloc
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨i, x', hx'⟩ := Set.mem_iUnion.1 (Set.eq_univ_iff_forall.1 hcov.jointly_surjective x)
    refine Set.mem_iUnion.2 ⟨PUnit.unit, pointsMap B S hS _ (Sigma.ι Xs i).hom x', ?_⟩
    rw [← hx', ← ι_sigmaDesc_hom (f := f) (hT := hT) (hX := hX) i, pointsMap_comp]
    rfl

variable [Countable ι] in
/-- **The coproduct of the members of a countable fppf covering is a one-member fppf
covering.** -/
theorem isFppfCovering_sigmaDesc (hcov : IsFppfCovering B S hS X f) :
    IsFppfCovering B S hS (fun _ : PUnit.{1} ↦ (∐ fun i ↦ spaceSheaf (X i) (hX i)).obj)
      (fun _ ↦ (sigmaDesc f hT hX).hom) :=
  isFppfCovering_sigmaDesc_of_isAlgebraicSpace (isAlgebraicSpace_sigma hX) hcov

/-- **A sheaf over the target of an fppf covering is an algebraic space as soon as the
coproduct of the members and the coproduct of the fibre products are algebraic spaces.**

Let `{f i : X i ⟶ T}` be an fppf covering, indexed by a type of any size, and let `π : F ⟶ T`
be a map from a sheaf. Suppose given algebraic spaces `Z i` sitting in pullback squares
`Z i = F ×_T X i`. If the coproducts `∐ X i` and `∐ Z i`, taken in sheaves, are algebraic
spaces, then so is `F`. The morphism `∐ X i ⟶ T` is a one-member fppf covering
(`AlgebraicGeometry.Space.Descent.isFppfCovering_sigmaDesc_of_isAlgebraicSpace`), its fibre
product with `F` is `∐ Z i` because coproducts of sheaves are stable under base change, and the
bootstrap theorem Stacks 04S6 concludes. This is the argument of the source's proof of
Stacks 0ADV part (1), with the two coproducts' algebraicity, which the source obtains from the
countability of the index type, isolated as hypotheses. -/
theorem isAlgebraicSpace_of_isPullback_of_isAlgebraicSpace_sigma [Small.{u} ι]
    (hcov : IsFppfCovering B S hS X f) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ T)
    (Z : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : ∀ i, IsAlgebraicSpace B S hS (Z i))
    (z : ∀ i, Z i ⟶ F) (w : ∀ i, Z i ⟶ X i) (hpb : ∀ i, IsPullback (z i) (w i) π (f i))
    (hY : IsAlgebraicSpace B S hS (∐ fun i ↦ spaceSheaf (X i) (hX i)).obj)
    (hZs : IsAlgebraicSpace B S hS (∐ fun i ↦ spaceSheaf (Z i) (hZ i)).obj) :
    IsAlgebraicSpace B S hS F := by
  let hT := hcov.target_isAlgebraicSpace
  let J := BigFppfOver.topology B S hS
  let Xs : ι → Sheaf J (Type u) := fun i ↦ spaceSheaf (X i) (hX i)
  let Zs : ι → Sheaf J (Type u) := fun i ↦ spaceSheaf (Z i) (hZ i)
  let σ := sigmaDesc f hT hX
  have hcov' := isFppfCovering_sigmaDesc_of_isAlgebraicSpace (hT := hT) hY hcov
  let Fs : Sheaf J (Type u) := ⟨F, hF⟩
  let gG : Fs ⟶ spaceSheaf T hT := ObjectProperty.homMk π
  have : HasPullback gG σ := HasLimitsOfShape.has_limit (C := Sheaf J (Type u)) _
  let A := pullback gG σ
  have hA : IsPullback (pullback.fst gG σ).hom (pullback.snd gG σ).hom π σ.hom :=
    (IsPullback.of_hasPullback gG σ).map (sheafToPresheaf J (Type u))
  let p : ∀ i, Zs i ⟶ A := fun i ↦ pullback.lift (ObjectProperty.homMk (z i))
    (ObjectProperty.homMk (w i) ≫ Sigma.ι Xs i) (by
      ext1
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, gG]
      rw [Category.assoc, ι_sigmaDesc_hom]
      exact (hpb i).w)
  let q : ∀ i, Zs i ⟶ Xs i := fun i ↦ ObjectProperty.homMk (w i)
  have hpb' : ∀ i, IsPullback (p i) (q i) (pullback.snd gG σ) (Sigma.ι Xs i) := by
    intro i
    refine (IsPullback.map_iff (sheafToPresheaf J (Type u)) ?_).1 ?_
    · exact pullback.lift_snd _ _ _
    · refine IsPullback.of_right ?_ ?_ hA
      · have hfst : (sheafToPresheaf J (Type u)).map (p i) ≫ (pullback.fst gG σ).hom = z i :=
          congrArg (sheafToPresheaf J (Type u)).map (pullback.lift_fst _ _ _)
        have hι : (sheafToPresheaf J (Type u)).map (Sigma.ι Xs i) ≫ σ.hom = f i :=
          ι_sigmaDesc_hom i
        rw [hfst, hι]
        exact hpb i
      · change (p i ≫ pullback.snd gG σ).hom = (q i ≫ Sigma.ι Xs i).hom
        rw [pullback.lift_snd]
  obtain ⟨hcolim⟩ := nonempty_isColimit_cofanMk_of_isPullback B S hS (Sigma.ι Xs)
    (coproductIsCoproduct Xs) (pullback.snd gG σ) p q hpb'
  have hAalg : IsAlgebraicSpace B S hS A.obj := hZs.of_iso ((sheafToPresheaf J (Type u)).mapIso
    ((coproductIsCoproduct Zs).coconePointUniqueUpToIso hcolim))
  let F' : SheavesWithSpaceFibres (fun _ : PUnit.{1} ↦ σ.hom) :=
    ⟨Over.mk π, hF, fun _ ↦ hAalg.of_iso hA.isoPullback⟩
  exact (isAlgebraicSpace_iff_isEffective_fibreDescentData _ hT (fun _ ↦ hY) hcov' F').2
    (isEffective_fibreDescentData_of_unique _ hT (fun _ ↦ hY)
      (isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS) hcov' F')

namespace DescentData

variable (D : DescentData f hT hX)

variable [Countable ι] in
/-- **The sheaf a descent datum along a countable fppf covering descends to (Stacks 0ADT) is
an algebraic space.** -/
theorem isAlgebraicSpace_descended_of_countable (hcov : IsFppfCovering B S hS X f) :
    IsAlgebraicSpace B S hS ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.left :=
  isAlgebraicSpace_of_isPullback_of_isAlgebraicSpace_sigma hcov
    ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).property.1
    ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D).obj.hom
    (fun i ↦ (D.obj i).left) D.obj_isAlgebraicSpace (descentInclusion f hcov D)
    (fun i ↦ (D.obj i).hom) (isPullback_descentInclusion f hcov D) (isAlgebraicSpace_sigma hX)
    (isAlgebraicSpace_sigma D.obj_isAlgebraicSpace)

variable [Countable ι] in
/-- **Stacks 0ADV, part (1).** Let `{f i : X i ⟶ T}` be an fppf covering of algebraic spaces
over `S` whose index type is countable. Then every descent datum for algebraic spaces relative
to it is effective. -/
@[stacks 0ADV "part (1): countable index set"]
theorem isEffective_of_countable (hcov : IsFppfCovering B S hS X f) : D.IsEffective :=
  (isAlgebraicSpace_inverse_iff_isEffective f hcov D).1
    (D.isAlgebraicSpace_descended_of_countable hcov)

/-- **A descent datum relative to an fppf covering one member of which is surjective is
effective.** This holds for an index type of any size: the projection `X i ×_T F ⟶ F` of the
sheaf `F` the datum descends to (Stacks 0ADT) is then a single chart, representable by algebraic
spaces, surjective, flat and locally of finite presentation, so `F` is an algebraic space by
Stacks 04S6. -/
theorem isEffective_of_isSurjective (hcov : IsFppfCovering B S hS X f) (i : ι)
    (hsurj : IsSurjective B S hS (f i)) : D.IsEffective :=
  (isAlgebraicSpace_inverse_iff_isEffective f hcov D).1
    ((isAlgebraicSpace_iff_isEffective_fibreDescentData f hT hX hcov
      ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D)).2
      (isEffective_fibreDescentData_of_isSurjective f hT hX
        (isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS) hcov
        ((fppfDescentDataSheafEquivalence f hcov).inverse.obj D) i hsurj))

end DescentData

end AlgebraicGeometry.Space.Descent

end
