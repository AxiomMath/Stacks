module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence

/-!
# Sheafification on the big fppf site of a scheme

Presheaves of sets on the big fppf site over a scheme `S` can be sheafified. The site itself
is not small — its objects are schemes of bounded size, a proper class worth of them up to
nothing — but its full subcategory of *affine* objects is essentially small, and that
subcategory is a dense subsite, so sheafification transports from it.

Essential smallness of the affine objects is a counting argument. An affine scheme over `S`
lying in the site is `Spec` of a commutative ring whose carrier has cardinality below the
site's cutoff, and any such ring is isomorphic to one carried by a *subset* of a fixed type of
that cardinality; the rings so presented form a set. The affine objects of the site are
therefore contained, up to isomorphism, in the image of a functor out of an essentially small
category — the comma category of the chosen `Spec` functor over `S` — which is what
`CategoryTheory.ObjectProperty.EssentiallySmall.of_le` needs.

With that, `CategoryTheory.hasSheafifyEssentiallySmallSite` sheafifies on the affine site, and
`CategoryTheory.Functor.IsDenseSubsite.hasSheafify_of_isEquivalence` carries the result across
the dense inclusion of Tag 021V.

## Main results

* `AlgebraicGeometry.essentiallySmall_bigAffineFppf`: the affine objects of the big fppf site
  over `S` form an essentially small category.
* `AlgebraicGeometry.hasSheafifyBigAffineFppf` and
  `AlgebraicGeometry.hasSheafifyBigFppfOver`: presheaves of sets on the big affine fppf site,
  respectively on the big fppf site, over `S` can be sheafified.

## Implementation notes

Essential smallness is left a theorem rather than an instance, as in the source, so that
it does not enter instance search on the site; the two sheafification results are instances,
since they are what later constructions — quotient sheaves above all — need to be found
automatically.

## References

* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A code for a commutative ring of cardinality below `κ`: a subset of a fixed type of
cardinality `κ` of size below `κ`, together with a ring structure on it. -/
private def boundedRingCode (κ : Cardinal.{u}) :=
  Σ A : {A : Set (κ.ord.ToType) // Cardinal.mk A < κ}, CommRing (A.1 : Type u)

/-- The commutative ring presented by a code. -/
private noncomputable def boundedRingCodeObj {κ : Cardinal.{u}}
    (c : boundedRingCode κ) : CommRingCat.{u} := by
  let : CommRing (c.1.1 : Type u) := c.2
  exact CommRingCat.of c.1.1

/-- Every commutative ring whose carrier has cardinality below `κ` is isomorphic to one
presented by a code. -/
private theorem exists_boundedRingCode (κ : Cardinal.{u}) {R : CommRingCat.{u}}
    (hR : Cardinal.mk R.carrier < κ) :
    ∃ c : boundedRingCode κ,
      Nonempty (CommRingCat.of R.carrier ≅ boundedRingCodeObj c) := by
  have hm : Cardinal.mk R.carrier ≤ Cardinal.mk (κ.ord.ToType) := by
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact hR.le
  obtain ⟨e⟩ : Nonempty (R.carrier ↪ κ.ord.ToType) :=
    (Cardinal.lift_mk_le').mp (by simpa using hm)
  classical
  let A : Set (κ.ord.ToType) := Set.range e
  let E : R.carrier ≃ A := Equiv.ofInjective e e.injective
  have hAc : Cardinal.mk A < κ := by rwa [← Cardinal.mk_congr E]
  let hA : CommRing A := E.symm.commRing
  let c : boundedRingCode κ := ⟨⟨A, hAc⟩, hA⟩
  let : CommRing (R : Type u) := R.commRing
  let ψ : A →+* R.carrier := {
    toFun := E.symm
    map_one' := by
      rw [show (1 : A) = E (1 : R.carrier) by rfl]
      exact E.symm_apply_apply _
    map_mul' := by
      intro x y
      rw [show x * y = E (E.symm x * E.symm y) by rfl]
      simp
    map_zero' := by
      rw [show (0 : A) = E (0 : R.carrier) by rfl]
      exact E.symm_apply_apply _
    map_add' := by
      intro x y
      rw [show x + y = E (E.symm x + E.symm y) by rfl]
      simp
  }
  let : CommRing (c.1.1 : Type u) := c.2
  refine ⟨c, ?_⟩
  change Nonempty (CommRingCat.of R.carrier ≅ CommRingCat.of A)
  exact ⟨(RingEquiv.ofBijective ψ E.symm.bijective).symm.toCommRingCatIso⟩

/-- The property of a commutative ring that its carrier has cardinality below `κ`. -/
private def boundedRingProperty (κ : Cardinal.{u}) :
    ObjectProperty CommRingCat.{u} := fun R ↦ Cardinal.mk R.carrier < κ

/-- Commutative rings of cardinality below `κ` form an essentially small subcategory. -/
private theorem boundedRingProperty_essentiallySmall (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (boundedRingProperty κ) := by
  let Q : ObjectProperty CommRingCat.{u} := fun R ↦
    R ∈ Set.range (boundedRingCodeObj (κ := κ))
  have hQ : ObjectProperty.Small.{u} Q := by
    change Small.{u} (Subtype Q)
    refine small_of_surjective
      (f := fun c : boundedRingCode κ ↦
        (⟨boundedRingCodeObj c, Set.mem_range_self c⟩ : Subtype Q)) ?_
    rintro ⟨R, ⟨c, rfl⟩⟩
    exact ⟨c, rfl⟩
  refine ⟨Q, hQ, fun R hR ↦ ?_⟩
  obtain ⟨c, hIso⟩ := exists_boundedRingCode κ hR
  exact ⟨boundedRingCodeObj c, ⟨c, rfl⟩, hIso⟩

/-- `Spec` as a functor from the opposite of the rings of cardinality below the site's cutoff
to the schemes of the site. -/
private noncomputable def boundedSpec (B : BigFppfSite.{u}) :
    (boundedRingProperty B.cutoff).FullSubcategoryᵒᵖ ⥤ B.Schemes where
  obj R := by
    let A := (ObjectProperty.ι (boundedRingProperty B.cutoff)).obj R.unop
    refine ⟨Spec A, ?_⟩
    change (Spec A).size < B.cutoff
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff R.unop.property
  map f := ObjectProperty.homMk <|
    Scheme.Spec.map ((ObjectProperty.ι (boundedRingProperty B.cutoff)).op.map f)
  map_id := by
    intro R
    apply ObjectProperty.hom_ext
    simp
  map_comp := by
    intro R₁ R₂ R₃ f g
    apply ObjectProperty.hom_ext
    simp

/-- The comma category of `boundedSpec` over `S`, an essentially small category mapping onto
the affine objects of the site over `S`. -/
private noncomputable abbrev boundedSpecSlice (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :=
  CostructuredArrow (boundedSpec B) (B.obj hS)

/-- The comparison functor from the comma category to the big fppf site over `S`. -/
private noncomputable def boundedSpecSliceToOver (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    boundedSpecSlice B S hS ⥤ BigFppfOver B S hS :=
  CostructuredArrow.toOver (boundedSpec B) (B.obj hS)

/-- Every affine object of the big fppf site over `S` is isomorphic to one in the image of the
comparison functor. -/
private theorem affineOver_le_boundedSpecSlice_essImage_isoClosure
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsAffineOver B S hS ≤ (boundedSpecSliceToOver B S hS).essImage.isoClosure := by
  intro V hV
  change IsAffine ((BigFppfOver.toScheme B S hS).obj V) at hV
  let X : Scheme.{u} := B.inclusion.obj V.left
  have : IsAffine X := hV
  let R : CommRingCat.{u} := Γ(X, ⊤)
  have hSpec : (Spec R).size < B.cutoff := by
    calc
      (Spec R).size = X.size := (Scheme.size_congr X.isoSpec).symm
      _ = (B.inclusion.obj V.left).size := rfl
      _ < B.cutoff := V.left.property
  have hR : Cardinal.mk R.carrier < B.cutoff := by
    rw [Scheme.size_Spec] at hSpec
    exact (le_max_right _ _).trans_lt hSpec
  let A : (boundedRingProperty B.cutoff).FullSubcategory := ⟨R, hR⟩
  let e : X ≅ Spec R := X.isoSpec
  let f : (boundedSpec B).obj (Opposite.op A) ⟶ B.obj hS :=
    ObjectProperty.homMk (e.inv ≫ B.inclusion.map V.hom)
  let Z : boundedSpecSlice B S hS := CostructuredArrow.mk f
  let eSite : (boundedSpec B).obj (Opposite.op A) ≅ V.left := {
    hom := ObjectProperty.homMk (show Spec R ⟶ B.inclusion.obj V.left from e.inv)
    inv := ObjectProperty.homMk (show B.inclusion.obj V.left ⟶ Spec R from e.hom)
    hom_inv_id := by
      apply ObjectProperty.hom_ext
      exact e.inv_hom_id
    inv_hom_id := by
      apply ObjectProperty.hom_ext
      exact e.hom_inv_id
  }
  have htri : eSite.hom ≫ V.hom = f := by
    apply ObjectProperty.hom_ext
    rfl
  exact ⟨(boundedSpecSliceToOver B S hS).obj Z, ⟨Z, ⟨Iso.refl _⟩⟩,
    ⟨(Over.isoMk eSite htri).symm⟩⟩

/-- The affine objects of the big fppf site over `S` form an essentially small category. -/
theorem essentiallySmall_bigAffineFppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    EssentiallySmall.{u} (BigAffineFppf B S hS) := by
  have : ObjectProperty.EssentiallySmall.{u} (boundedRingProperty B.cutoff) :=
    boundedRingProperty_essentiallySmall B.cutoff
  have : EssentiallySmall.{u} ((boundedRingProperty B.cutoff).FullSubcategoryᵒᵖ) :=
    inferInstance
  have : EssentiallySmall.{u} (boundedSpecSlice B S hS) := inferInstance
  have : ObjectProperty.EssentiallySmall.{u} (IsAffineOver B S hS) :=
    ObjectProperty.EssentiallySmall.of_le
      (affineOver_le_boundedSpecSlice_essImage_isoClosure B S hS)
  infer_instance

/-- Presheaves of sets on the big affine fppf site over `S` can be sheafified. -/
noncomputable instance hasSheafifyBigAffineFppf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (BigAffineFppf.topology B S hS) (Type u) := by
  have : EssentiallySmall.{u} (BigAffineFppf B S hS) := essentiallySmall_bigAffineFppf B S hS
  exact hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

/-- Presheaves of sets on the big fppf site over `S` can be sheafified, by transport along the
dense inclusion of the affine objects. -/
noncomputable instance hasSheafifyBigFppfOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasSheafify (BigFppfOver.topology B S hS) (Type u) := by
  let G := BigAffineFppf.inclusion B S hS
  let J := BigAffineFppf.topology B S hS
  let K := BigFppfOver.topology B S hS
  have : G.IsDenseSubsite J K := bigAffineFppfInclusion_isDenseSubsite B S hS
  have : EssentiallySmall.{u} (BigAffineFppf B S hS) := essentiallySmall_bigAffineFppf B S hS
  have : LocallySmall.{u} (BigFppfOver B S hS) := inferInstance
  have : ∀ X : (BigFppfOver B S hS)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow X G.op) (Type u) := by
    intro X
    apply HasLimitsOfShape.of_essentiallySmall
  have : (G.sheafPushforwardContinuous (Type u) J K).IsEquivalence := inferInstance
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence J K G

end AlgebraicGeometry

end
