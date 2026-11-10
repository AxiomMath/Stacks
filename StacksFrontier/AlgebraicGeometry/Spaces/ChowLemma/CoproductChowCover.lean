module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DisjointProjectiveEmbeddings
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCoproduct

/-!
# Two proper covers with H-quasi-projective sources assemble into one

Two morphisms into an algebraic space `X` from objects of the big fppf site over `S`, which are
proper, whose sources are H-quasi-projective over the base, and whose images cover the points of
`X`, assemble into a Chow scheme cover of `X`: a single proper surjective morphism out of their
coproduct in the big fppf category over `S`, whose underlying scheme is H-quasi-projective over
the base.

## Main definitions

* `AlgebraicGeometry.Space.coprodPairObj` and `AlgebraicGeometry.Space.coprodPairIncl` present a
  binary coproduct of the big fppf category over `S` as a cofan indexed by `ULift Bool`.
* `AlgebraicGeometry.Space.coprodToSchemeIso` identifies the underlying scheme of a binary
  coproduct of the site with the binary coproduct of the underlying schemes.

## Main results

* `AlgebraicGeometry.Space.isColimit_cofan_coprodPair`: that cofan is a colimit.
* `AlgebraicGeometry.Space.isHQuasiProjective_coprod`: the underlying scheme of a binary
  coproduct of the site is H-quasi-projective over the base when both summands are.
* `AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_pair`: two proper morphisms into `X`
  from objects of the site which are H-quasi-projective over the base and whose images cover the
  points of `X` give `AlgebraicGeometry.Space.HasChowSchemeCover` for `X`.

## References

* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A binary coproduct of the site as a two-member cofan -/

/-- A pair of objects of the big fppf category over `S`, read as a family indexed by
`ULift Bool`. -/
def coprodPairObj (X₁ X₂ : BigFppfOver B S hS) : ULift.{u} Bool → BigFppfOver B S hS
  | ⟨false⟩ => X₁
  | ⟨true⟩ => X₂

/-- The two inclusions into a binary coproduct of the big fppf category over `S`, read as a
cofan of `AlgebraicGeometry.Space.coprodPairObj`. -/
def coprodPairIncl (X₁ X₂ : BigFppfOver B S hS) :
    ∀ b, coprodPairObj B S hS X₁ X₂ b ⟶ X₁ ⨿ X₂
  | ⟨false⟩ => coprod.inl
  | ⟨true⟩ => coprod.inr

/-- A binary coproduct of the big fppf category over `S` is the colimit of the two-member cofan
`AlgebraicGeometry.Space.coprodPairIncl`. -/
def isColimit_cofan_coprodPair (X₁ X₂ : BigFppfOver B S hS) :
    IsColimit (Cofan.mk (X₁ ⨿ X₂) (coprodPairIncl B S hS X₁ X₂)) := by
  refine Cofan.IsColimit.mk _ (fun s => coprod.desc (s.inj ⟨false⟩) (s.inj ⟨true⟩)) ?_ ?_
  · rintro s ⟨_ | _⟩
    exacts [coprod.inl_desc _ _, coprod.inr_desc _ _]
  · exact fun s m hm => coprod.hom_ext ((hm ⟨false⟩).trans (coprod.inl_desc _ _).symm)
      ((hm ⟨true⟩).trans (coprod.inr_desc _ _).symm)

/-! ### The underlying scheme of a binary coproduct of the site -/

/-- The comparison isomorphism between the binary coproduct of the underlying schemes of two
objects of the big fppf category over `S` and the underlying scheme of their binary coproduct
in the site. -/
def coprodToSchemeIso (X₁ X₂ : BigFppfOver B S hS) :
    ((BigFppfOver.toScheme B S hS).obj X₁ ⨿ (BigFppfOver.toScheme B S hS).obj X₂) ≅
      (BigFppfOver.toScheme B S hS).obj (X₁ ⨿ X₂) :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (isColimitBinaryCofanToSchemeMap X₁ X₂)

/-- The comparison isomorphism `AlgebraicGeometry.Space.coprodToSchemeIso` carries the left
inclusion of the coproduct of the underlying schemes to the image of the left inclusion of the
coproduct in the site. -/
theorem coprodInl_comp_coprodToSchemeIso_hom (X₁ X₂ : BigFppfOver B S hS) :
    (coprod.inl : (BigFppfOver.toScheme B S hS).obj X₁ ⟶ _) ≫
        (coprodToSchemeIso B S hS X₁ X₂).hom
      = (BigFppfOver.toScheme B S hS).map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod _ _)
    (isColimitBinaryCofanToSchemeMap X₁ X₂) ⟨WalkingPair.left⟩

/-- The comparison isomorphism `AlgebraicGeometry.Space.coprodToSchemeIso` carries the right
inclusion of the coproduct of the underlying schemes to the image of the right inclusion of the
coproduct in the site. -/
theorem coprodInr_comp_coprodToSchemeIso_hom (X₁ X₂ : BigFppfOver B S hS) :
    (coprod.inr : (BigFppfOver.toScheme B S hS).obj X₂ ⟶ _) ≫
        (coprodToSchemeIso B S hS X₁ X₂).hom
      = (BigFppfOver.toScheme B S hS).map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod _ _)
    (isColimitBinaryCofanToSchemeMap X₁ X₂) ⟨WalkingPair.right⟩

/-- The comparison isomorphism is a morphism over the base. -/
theorem coprodToSchemeIso_hom_comp_hom (X₁ X₂ : BigFppfOver B S hS) :
    (coprodToSchemeIso B S hS X₁ X₂).hom ≫
        B.inclusion.map (X₁ ⨿ X₂ : BigFppfOver B S hS).hom
      = coprod.desc (B.inclusion.map X₁.hom) (B.inclusion.map X₂.hom) := by
  refine coprod.hom_ext ?_ ?_
  · rw [← Category.assoc, coprodInl_comp_coprodToSchemeIso_hom, coprod.inl_desc,
      show (BigFppfOver.toScheme B S hS).map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)
        = B.inclusion.map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂).left from rfl,
      ← Functor.map_comp, Over.w]
  · rw [← Category.assoc, coprodInr_comp_coprodToSchemeIso_hom, coprod.inr_desc,
      show (BigFppfOver.toScheme B S hS).map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)
        = B.inclusion.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂).left from rfl,
      ← Functor.map_comp, Over.w]

/-- The underlying scheme of a binary coproduct of the big fppf category over `S` is
H-quasi-projective over the base when both summands are. -/
theorem isHQuasiProjective_coprod (X₁ X₂ : BigFppfOver B S hS)
    (h₁ : IsHQuasiProjective (B.inclusion.map X₁.hom))
    (h₂ : IsHQuasiProjective (B.inclusion.map X₂.hom)) :
    IsHQuasiProjective (B.inclusion.map (X₁ ⨿ X₂ : BigFppfOver B S hS).hom) := by
  obtain ⟨n, i, _, _, hieq⟩ := isHQuasiProjective_coprodDesc' h₁ h₂
  refine ⟨n, (coprodToSchemeIso B S hS X₁ X₂).inv ≫ i, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, hieq, ← coprodToSchemeIso_hom_comp_hom B S hS X₁ X₂,
    Iso.inv_hom_id_assoc]

/-! ### A Chow scheme cover from two proper morphisms -/

/-- Two proper morphisms into an algebraic space `X` from objects of the site which are
H-quasi-projective over the base, and whose images cover the points of `X`, give a Chow scheme
cover of `X`. -/
theorem hasChowSchemeCover_of_isProper_pair
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (X₁ X₂ : BigFppfOver B S hS) (p₁ : yoneda.obj X₁ ⟶ X) (p₂ : yoneda.obj X₂ ⟶ X)
    (hp₁ : IsProper B S hS p₁) (hp₂ : IsProper B S hS p₂)
    (hq₁ : IsHQuasiProjective (B.inclusion.map X₁.hom))
    (hq₂ : IsHQuasiProjective (B.inclusion.map X₂.hom))
    (hcov : ∀ x : points B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj X₁) p₁) ∪
        Set.range (pointsMap B S hS (yoneda.obj X₂) p₂)) :
    HasChowSchemeCover B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let Xs : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  have hV : IsColimit (Cofan.mk (X₁ ⨿ X₂) (coprodPairIncl B S hS X₁ X₂)) :=
    isColimit_cofan_coprodPair B S hS X₁ X₂
  have hY : IsColimit (Cofan.mk (J.yoneda.obj (X₁ ⨿ X₂))
      fun b => J.yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) :=
    BigFppfOver.isColimit_yoneda_cofan B S hS (coprodPairObj B S hS X₁ X₂)
      (coprodPairIncl B S hS X₁ X₂) hV
  let tgt : ∀ b, J.yoneda.obj (coprodPairObj B S hS X₁ X₂ b) ⟶ Xs := fun b =>
    match b with
    | ⟨false⟩ => ⟨p₁⟩
    | ⟨true⟩ => ⟨p₂⟩
  let h : J.yoneda.obj (X₁ ⨿ X₂) ⟶ Xs := Cofan.IsColimit.desc hY tgt
  have hfac₁ : yoneda.map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ h.hom = p₁ :=
    congrArg (fun k : J.yoneda.obj (coprodPairObj B S hS X₁ X₂ ⟨false⟩) ⟶ Xs => k.hom)
      (Cofan.IsColimit.fac hY tgt ⟨false⟩)
  have hfac₂ : yoneda.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ h.hom = p₂ :=
    congrArg (fun k : J.yoneda.obj (coprodPairObj B S hS X₁ X₂ ⟨true⟩) ⟶ Xs => k.hom)
      (Cofan.IsColimit.fac hY tgt ⟨true⟩)
  refine ⟨X₁ ⨿ X₂, h.hom, ?_, ?_, isHQuasiProjective_coprod B S hS X₁ X₂ hq₁ hq₂⟩
  · refine isProper_of_isColimit_cofan B S hS
      (fun b => J.yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) hY
      (fun b => isAlgebraicSpace_yoneda B S hS (coprodPairObj B S hS X₁ X₂ b))
      (isAlgebraicSpace_yoneda B S hS (X₁ ⨿ X₂)) hX h.hom ?_
    rintro ⟨_ | _⟩
    · change IsProper B S hS (yoneda.map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂) ≫ h.hom)
      rwa [hfac₁]
    · change IsProper B S hS (yoneda.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂) ≫ h.hom)
      rwa [hfac₂]
  · intro x
    rcases hcov x with ⟨y, hy⟩ | ⟨y, hy⟩
    · refine ⟨pointsMap B S hS (yoneda.obj X₁)
        (yoneda.map (coprod.inl : X₁ ⟶ X₁ ⨿ X₂)) y, ?_⟩
      rw [← hy, ← hfac₁, pointsMap_comp]
      rfl
    · refine ⟨pointsMap B S hS (yoneda.obj X₂)
        (yoneda.map (coprod.inr : X₂ ⟶ X₁ ⨿ X₂)) y, ?_⟩
      rw [← hy, ← hfac₂, pointsMap_comp]
      rfl

end AlgebraicGeometry.Space

end
