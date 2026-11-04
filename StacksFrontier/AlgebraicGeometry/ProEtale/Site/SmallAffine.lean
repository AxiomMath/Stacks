module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SiteAxioms
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSiteCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine small pro-étale site of a scheme

The full subcategory `S_{affine, proétale}` of the small pro-étale site `S_proétale` of a scheme
`S` on its affine objects, whose coverings are the standard pro-étale coverings, that is the
*finite* small-site covering families. These coverings satisfy the site axioms, and every object
of `S_{affine, proétale}` is quasi-compact.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsAffineSmallProetale`: the object property cutting out the affine
  objects of the small pro-étale site.
* `AlgebraicGeometry.ProEtale.SmallAffineProetale`: the resulting full subcategory, with its
  inclusion into the small pro-étale site and the functor
  `AlgebraicGeometry.ProEtale.SmallAffineProetale.toScheme` to underlying schemes.
* `AlgebraicGeometry.ProEtale.SmallAffineProetale.precoverage` and
  `AlgebraicGeometry.ProEtale.SmallAffineProetale.topology`: the finite small-site covering
  families, and the topology they generate.

## Main results

* `AlgebraicGeometry.ProEtale.SmallAffineProetale.isSite_isCovering`: the standard pro-étale
  covering families of the affine small pro-étale site satisfy the site axioms.
* `AlgebraicGeometry.ProEtale.SmallAffineProetale.isQuasiCompactObject`: every object of the
  affine small pro-étale site is a quasi-compact object of it.

## References

* [Stacks Project, Tag 098W](https://stacks.math.columbia.edu/tag/098W)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object of the small pro-étale site of `S` is *affine* when its underlying scheme is. -/
abbrev IsAffineSmallProetale : ObjectProperty (SmallProetale B S hS) :=
  fun U ↦ IsAffine U.obj.left.obj

/-- The category `S_{affine, proétale}`: the full subcategory of the small pro-étale site of `S`
on its affine objects. -/
abbrev SmallAffineProetale := (IsAffineSmallProetale B S hS).FullSubcategory

namespace SmallAffineProetale

/-- The canonical full inclusion into the small pro-étale site. -/
abbrev inclusion : SmallAffineProetale B S hS ⥤ SmallProetale B S hS :=
  (IsAffineSmallProetale B S hS).ι

/-- The underlying scheme of an affine object of the small pro-étale site. -/
abbrev toScheme : SmallAffineProetale B S hS ⥤ Scheme.{u} :=
  inclusion B S hS ⋙ SmallProetale.toScheme B S hS

/-- Every object of the affine small pro-étale site has affine underlying scheme. -/
instance isAffine_left (U : SmallAffineProetale B S hS) : IsAffine U.obj.obj.left.obj :=
  U.property

/-- The coverings of `S_{affine, proétale}`: the standard pro-étale coverings, that is the finite
small-site covering families. -/
abbrev IsCovering (E : Covering (SmallAffineProetale B S hS)) : Prop :=
  SmallProetale.IsCovering B S hS
      ⟨(inclusion B S hS).obj E.1, E.2.map (inclusion B S hS)⟩ ∧
    Finite E.2.I₀

/-- The precoverage presented by the finite small-site covering families. -/
def precoverage : Precoverage (SmallAffineProetale B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩}

/-- A presieve on the affine small pro-étale site is covering precisely when a finite small-site
covering family presents it. -/
theorem mem_precoverage_iff {X : SmallAffineProetale B S hS} {R : Presieve X} :
    R ∈ precoverage B S hS X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩ := Iff.rfl

/-- The topology of the affine small pro-étale site. -/
abbrev topology : GrothendieckTopology (SmallAffineProetale B S hS) :=
  (precoverage B S hS).toGrothendieck

/-- The standard pro-étale covering families of `S_{affine, proétale}` satisfy the isomorphism,
composition and base change axioms, so they present a site. -/
theorem isSite_isCovering : IsSite (IsCovering B S hS) := by
  let K := inclusion B S hS ⋙ SmallProetale.inclusion B S hS ⋙ BigProetaleOver.forget B S hS
  refine ⟨?_, ?_, ?_⟩
  · intro U V f _
    exact ⟨B.covering_isSite.1 (K.map f), inferInstance⟩
  · intro E hE F hF h
    have hcomp := B.covering_isSite.2.1
      ⟨K.obj E.1, E.2.map K⟩ hE.1
      (fun i ↦ ⟨K.obj (F i).1, (F i).2.map K⟩)
      (fun i ↦ (hF i).1) (fun i ↦ congrArg K.obj (h i))
    refine ⟨?_, ?_⟩
    · simpa [IsCovering, SmallProetale.IsCovering, BigProetaleOver.IsCovering, K,
        PreZeroHypercover.map, PreZeroHypercover.bind,
        PreZeroHypercover.pushforward] using hcomp
    · have hEfin : Finite E.2.I₀ := hE.2
      have hFfin : ∀ i, Finite (F i).2.I₀ := fun i ↦ (hF i).2
      show Finite (Σ i, (F i).2.I₀)
      infer_instance
  · intro E hE V g
    obtain ⟨P, a, b, hpb, hcov⟩ := B.covering_isSite.2.2
      ⟨K.obj E.1, E.2.map K⟩ hE.1 (K.obj V) (K.map g)
    have hPaff (i : E.2.I₀) : IsAffine (B.inclusion.obj (P i)) := by
      have h₁ : IsAffine (B.inclusion.obj (K.obj (E.2.X i))) := (E.2.X i).property
      have h₂ : IsAffine (B.inclusion.obj (K.obj V)) := V.property
      have h₃ : IsAffine (B.inclusion.obj (K.obj E.1)) := E.1.property
      have h₄ : IsAffine (B.inclusion.obj ((E.2.map K).X i)) := (E.2.X i).property
      exact IsAffine.of_isPullback ((hpb i).map B.inclusion)
    have hweak (i : E.2.I₀) : WeaklyEtale (B.inclusion.map (b i ≫ V.obj.obj.hom)) := by
      have hEf : WeaklyEtale (B.inclusion.map (K.map (E.2.f i))) := by
        have hm := hE.1.1
        change ((E.2.map K).map B.inclusion).presieve₀ ∈
          Scheme.proetalePrecoverage _ at hm
        exact ((Scheme.presieve₀_mem_precoverage_iff _).mp hm.2).2 i
      have hbi : WeaklyEtale (B.inclusion.map (b i)) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback ((hpb i).map B.inclusion) hEf
      have hV : WeaklyEtale (B.inclusion.map V.obj.obj.hom) := V.obj.property
      rw [B.inclusion.map_comp]
      infer_instance
    let Q (i : E.2.I₀) : SmallAffineProetale B S hS :=
      ⟨⟨Over.mk (b i ≫ V.obj.obj.hom), hweak i⟩, hPaff i⟩
    let q₁ (i : E.2.I₀) : Q i ⟶ E.2.X i :=
      ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk (a i) (by
        have hi := (hpb i).w
        change a i ≫ (E.2.f i).hom.hom.left = b i ≫ g.hom.hom.left at hi
        calc a i ≫ (E.2.X i).obj.obj.hom
              = a i ≫ ((E.2.f i).hom.hom.left ≫ E.1.obj.obj.hom) :=
                congrArg (fun x ↦ a i ≫ x) (E.2.f i).hom.hom.w.symm
          _ = (a i ≫ (E.2.f i).hom.hom.left) ≫ E.1.obj.obj.hom := (Category.assoc _ _ _).symm
          _ = (b i ≫ g.hom.hom.left) ≫ E.1.obj.obj.hom := by rw [hi]
          _ = b i ≫ (g.hom.hom.left ≫ E.1.obj.obj.hom) := Category.assoc _ _ _
          _ = b i ≫ V.obj.obj.hom := congrArg (fun x ↦ b i ≫ x) g.hom.hom.w)))
    let q₂ (i : E.2.I₀) : Q i ⟶ V :=
      ObjectProperty.homMk (ObjectProperty.homMk (Over.homMk (b i) rfl))
    refine ⟨Q, q₁, q₂, fun i ↦ ?_, ⟨hcov, hE.2⟩⟩
    exact IsPullback.of_map_of_faithful K (hpb i)

/-- Every object of the affine small pro-étale site is a quasi-compact object for its
topology. -/
theorem isQuasiCompactObject (U : SmallAffineProetale B S hS) :
    (topology B S hS).IsQuasiCompactObject U :=
  GrothendieckTopology.isQuasiCompactObject_of_isSite _ (isSite_isCovering B S hS)
    (fun _ h ↦ h.2) _ (fun _ _ ↦ Iff.rfl) U

end SmallAffineProetale

end AlgebraicGeometry.ProEtale

end
