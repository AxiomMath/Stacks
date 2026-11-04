module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Gluing in the big fppf site from a bound on the glued scheme

Let `K` be a presheaf on the big fppf site over `S` with a family of relatively representable
open immersions `c i : Ci i ⟶ K` covering `K`, and let `h : H ⟶ K` be a morphism from a sheaf `H`
whose base changes along the `c i` are representable. Then `H` is representable as soon as the
scheme glued from those base changes lies in the site, or as soon as the index type and the
sources `X i` of the base changes are bounded by `size T ^ ℵ₀` for an object `T` of the site.

## Main results

* `AlgebraicGeometry.Space.presheaf_openImmersions_of_isPullback`: the base changes of the
  covering family are again relatively representable open immersions.
* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_of_locally_covering`: the canonical
  morphism from the coproduct of the representables to the sheaf is locally surjective.
* `AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_contains`: the sheaf is
  representable when the glued scheme lies in the site.
* `AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_le_power`: the sheaf is
  representable when `#I ≤ T.size ^ ℵ₀` and every source `X i` of the base changes has size at
  most `T.size ^ ℵ₀`, for `T` an object of the site.

## Implementation notes

The containment hypothesis of
`AlgebraicGeometry.Space.isRepresentable_of_locally_covering_of_contains` is stated against an
explicitly supplied proof `hpopen` that the base changes are open immersions, so that it can name
the glue datum `AlgebraicGeometry.Space.schemeGlueData`. Since
`CategoryTheory.MorphismProperty.presheaf` is a proposition, the glue datum does not depend on
which proof is supplied.

## References

* [Stacks Project, Tag 02WR](https://stacks.math.columbia.edu/tag/02WR)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change of a relatively representable open immersion along a morphism to the
covered presheaf is again one. -/
theorem presheaf_openImmersions_of_isPullback
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : ∀ i, Ci i ⟶ K}
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf (c i))
    {H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {h : H ⟶ K} {X : I → BigFppfOver B S hS}
    {p : ∀ i, yoneda.obj (X i) ⟶ H} {q : ∀ i, yoneda.obj (X i) ⟶ Ci i}
    (hp : ∀ i, IsPullback (p i) (q i) h (c i)) (i : I) :
    (openImmersionOver B S hS).presheaf (p i) :=
  (MorphismProperty.relative_isStableUnderBaseChange (openImmersionOver B S hS)).of_isPullback
    (hp i).flip (hopen i)

/-- The canonical morphism from the coproduct of the representables `X i` to the sheaf `H` is
locally surjective: every section of `H` lies, on a covering sieve, in the image of one of the
base changes `p i` of the covering family. -/
theorem isLocallySurjective_sigmaDesc_of_locally_covering
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K)
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (H : Sheaf (BigFppfOver.topology B S hS) (Type u)) (h : H.obj ⟶ K)
    {X : I → BigFppfOver B S hS}
    (p : ∀ i, yoneda.obj (X i) ⟶ H.obj) (q : ∀ i, yoneda.obj (X i) ⟶ Ci i)
    (hp : ∀ i, IsPullback (p i) (q i) h (c i)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc p) := by
  classical
  constructor
  intro U s
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (sieveOfSection_iSup_range_mem B S hS c hcov (U := op U) (h.app (op U) s))
  rintro W f2 hf2
  have hf2' : K.map f2.op (h.app (op U) s) ∈
      (⨆ i, Subfunctor.range (c i)).obj (op W) := hf2
  rw [Subfunctor.iSup_obj] at hf2'
  obtain ⟨i, y, hy⟩ : ∃ i, ∃ y, (c i).app (op W) y = K.map f2.op (h.app (op U) s) := by
    simpa using hf2'
  let sig : yoneda.obj W ⟶ H.obj := yonedaEquiv.symm (H.obj.map f2.op s)
  let tau : yoneda.obj W ⟶ Ci i := yonedaEquiv.symm y
  have hcomm : sig ≫ h = tau ≫ c i := yonedaEquiv.injective <| by
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hy,
      NatTrans.naturality_apply h f2.op s]
  refine ⟨(Sigma.ι (fun k => yoneda.obj (X k)) i).app (op W)
    (yonedaEquiv ((hp i).lift sig tau hcomm)), ?_⟩
  rw [← FunctorToTypes.comp, Sigma.ι_desc, ← yonedaEquiv_comp, (hp i).lift_fst,
    Equiv.apply_symm_apply]

/-- A sheaf with a morphism to a presheaf `K` whose base changes along a family of representable
open immersions covering `K` are representable is itself representable, as soon as the scheme
glued from those base changes lies in the site. -/
theorem isRepresentable_of_locally_covering_of_contains
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K)
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (H : Sheaf (BigFppfOver.topology B S hS) (Type u)) (h : H.obj ⟶ K)
    {X : I → BigFppfOver B S hS}
    (p : ∀ i, yoneda.obj (X i) ⟶ H.obj) (q : ∀ i, yoneda.obj (X i) ⟶ Ci i)
    (hp : ∀ i, IsPullback (p i) (q i) h (c i))
    (hpopen : ∀ i, (openImmersionOver B S hS).presheaf (p i))
    (hg : B.Contains (schemeGlueData p hpopen).glued) :
    H.obj.IsRepresentable :=
  isRepresentable_of_openCover_of_contains p hpopen hg
    (isLocallySurjective_sigmaDesc_of_locally_covering B S hS c hcov H h p q hp)

/-- A sheaf with a morphism to a presheaf `K` whose base changes along a family of representable
open immersions covering `K` are representable is itself representable, as soon as the index type
and the sources `X i` of the base changes are bounded by `size T ^ ℵ₀` for a single object `T` of
the site. -/
theorem isRepresentable_of_locally_covering_of_le_power
    {K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type u}
    {Ci : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : ∀ i, Ci i ⟶ K)
    (hcov : (⨆ i, Subfunctor.range (c i)).sheafify (BigFppfOver.topology B S hS) = ⊤)
    (hopen : ∀ i, (openImmersionOver B S hS).presheaf (c i))
    (H : Sheaf (BigFppfOver.topology B S hS) (Type u)) (h : H.obj ⟶ K)
    {X : I → BigFppfOver B S hS}
    (p : ∀ i, yoneda.obj (X i) ⟶ H.obj) (q : ∀ i, yoneda.obj (X i) ⟶ Ci i)
    (hp : ∀ i, IsPullback (p i) (q i) h (c i))
    {T : Scheme.{u}} (hT : B.Contains T) (hIT : #I ≤ T.size ^ ℵ₀)
    (hX : ∀ i, ((BigFppfOver.toScheme B S hS).obj (X i)).size ≤ T.size ^ ℵ₀) :
    H.obj.IsRepresentable :=
  isRepresentable_of_openCover_of_le_power p
    (fun i ↦ presheaf_openImmersions_of_isPullback B S hS hopen hp i) hT hIT hX
    (isLocallySurjective_sigmaDesc_of_locally_covering B S hS c hcov H h p q hp)

end AlgebraicGeometry.Space

end
