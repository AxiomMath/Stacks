module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Localization.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Inverting a family of sections of the structure sheaf

Let `X` be a ringed site and let `S` be a family of multiplicative subsets `S(U) ⊆ O_X(U)`,
one for each object `U`, stable under restriction. Localizing each ring of sections at its
multiplicative subset gives a presheaf of rings, because a restriction map carries `S(U)` into
`S(V)` and therefore extends to the localizations; the extension is functorial by the
uniqueness in the universal property of localization.

The sheafification of this presheaf is the universal sheaf of rings in which the prescribed
sections become invertible: a morphism `O_X ⟶ A` to a sheaf of rings inverting every section
of `S` factors through it, uniquely, by combining the sectionwise universal property of
localization with that of sheafification.

## Main definitions

* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf`: a restriction-stable family of
  multiplicative subsets of the structure sheaf.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationPresheaf`: the presheaf
  of sectionwise localizations, with `toLocalizationPresheaf` its canonical map.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.toLocalizationSheaf`: the canonical
  map from the structure sheaf to the sheafified localization.

## Main results

* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.isUnit_toLocalizationSheaf`: each
  prescribed section becomes invertible.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.existsUnique_lift_toLocalizationSheaf`:
  the universal property of the sheafified localization.

## Implementation notes

The multiplicative subpresheaf and the sectionwise localization are given for an arbitrary
site, not only for the site of open sets of a space. The factorization equation is an equation
of morphisms of sheaves, so it already includes compatibility with all restriction maps.

## References

* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- A restriction-stable family of multiplicative subsets of the structure sheaf. -/
structure MultiplicativeSubpresheaf (X : RingedSite.{u, v, w}) where
  /-- The multiplicative subset over an object. -/
  obj (U : X.Cᵒᵖ) : Submonoid (X.O.obj.obj U)
  /-- Restriction preserves the multiplicative subsets. -/
  map {U V : X.Cᵒᵖ} (f : U ⟶ V) :
    obj U ≤ (obj V).comap (X.O.obj.map f).hom

namespace MultiplicativeSubpresheaf

variable {X : RingedSite.{u, v, w}}

/-- The presheaf whose sections are the sectionwise localizations. -/
noncomputable def localizationPresheaf (S : MultiplicativeSubpresheaf X) :
    X.Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := CommRingCat.of (Localization (S.obj U))
  map {_ _} f := CommRingCat.ofHom <|
    IsLocalization.map _ (X.O.obj.map f).hom (S.map f)
  map_id U := by
    simp_rw [X.O.obj.map_id]
    ext x
    exact IsLocalization.map_id x
  map_comp {U V W} f g := by
    delta CommRingCat.ofHom CommRingCat.of Bundled.of
    simp_rw [X.O.obj.map_comp]
    ext : 1
    dsimp
    rw [IsLocalization.map_comp_map]

/-- The localization of the sections over `U` is an algebra over the sections over `U`. -/
instance (S : MultiplicativeSubpresheaf X) (U : X.Cᵒᵖ) :
    Algebra (X.O.obj.obj U) (S.localizationPresheaf.obj U) :=
  inferInstanceAs (Algebra (X.O.obj.obj U) (Localization (S.obj U)))

/-- The sections over `U` of `localizationPresheaf` are the localization at `S.obj U`. -/
instance (S : MultiplicativeSubpresheaf X) (U : X.Cᵒᵖ) :
    IsLocalization (S.obj U) (S.localizationPresheaf.obj U) :=
  inferInstanceAs (IsLocalization (S.obj U) (Localization (S.obj U)))

/-- The canonical map into the presheaf of sectionwise localizations. -/
noncomputable def toLocalizationPresheaf (S : MultiplicativeSubpresheaf X) :
    X.O.obj ⟶ S.localizationPresheaf where
  app U := CommRingCat.ofHom <| algebraMap (X.O.obj.obj U) (Localization (S.obj U))
  naturality {U V} f := by
    change X.O.obj.map f ≫
        CommRingCat.ofHom (algebraMap (X.O.obj.obj V) (Localization (S.obj V))) =
      CommRingCat.ofHom (algebraMap (X.O.obj.obj U) (Localization (S.obj U))) ≫
        CommRingCat.ofHom (IsLocalization.map (Localization (S.obj V))
          (X.O.obj.map f).hom (S.map f))
    exact CommRingCat.hom_ext (IsLocalization.map_comp (S.map f)).symm

/-- The canonical map from the ring sheaf to the sheafified localization. -/
@[stacks 0EMC "canonical homomorphism of sheaves of rings"]
noncomputable def toLocalizationSheaf (S : MultiplicativeSubpresheaf X)
    [HasWeakSheafify X.J CommRingCat.{w}] :
    X.O ⟶ (presheafToSheaf X.J CommRingCat.{w}).obj S.localizationPresheaf :=
  (sheafificationIso X.O).hom ≫
    (presheafToSheaf X.J CommRingCat.{w}).map S.toLocalizationPresheaf

/-- The sectionwise lift of a morphism inverting every prescribed section. -/
private noncomputable def localizationPresheafLift
    (S : MultiplicativeSubpresheaf X) (A : Sheaf X.J CommRingCat.{w})
    (f : X.O ⟶ A) (hf : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      IsUnit ((f.hom.app U).hom (s : X.O.obj.obj U))) :
    S.localizationPresheaf ⟶ A.obj where
  app U := CommRingCat.ofHom <| IsLocalization.lift (M := S.obj U) (hf U)
  naturality {U V} α := by
    change CommRingCat.ofHom
        (IsLocalization.map (Localization (S.obj V)) (X.O.obj.map α).hom (S.map α)) ≫
          CommRingCat.ofHom (IsLocalization.lift (M := S.obj V) (hf V)) =
      CommRingCat.ofHom (IsLocalization.lift (M := S.obj U) (hf U)) ≫ A.obj.map α
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (M := S.obj U)
    apply RingHom.ext
    intro x
    have hnat := f.hom.naturality α
    change IsLocalization.lift (M := S.obj V) (hf V)
        (IsLocalization.map (Localization (S.obj V)) (X.O.obj.map α).hom (S.map α)
          (algebraMap (X.O.obj.obj U) (Localization (S.obj U)) x)) =
      (A.obj.map α).hom
        (IsLocalization.lift (M := S.obj U) (hf U)
          (algebraMap (X.O.obj.obj U) (Localization (S.obj U)) x))
    rw [IsLocalization.map_eq, IsLocalization.lift_eq, IsLocalization.lift_eq]
    exact congrArg (fun k : CommRingCat.of (X.O.obj.obj U) ⟶ CommRingCat.of (A.obj.obj V) =>
      k.hom x) hnat

/-- The underlying morphism of presheaves of `toLocalizationSheaf` is the canonical map into the
localization presheaf followed by the sheafification map. -/
private theorem hom_toLocalizationSheaf (S : MultiplicativeSubpresheaf X)
    [HasWeakSheafify X.J CommRingCat.{w}] :
    S.toLocalizationSheaf.hom = S.toLocalizationPresheaf ≫ toSheafify X.J _ := by
  show (sheafificationIso X.O).hom.hom ≫ sheafifyMap X.J S.toLocalizationPresheaf = _
  rw [show (sheafificationIso X.O).hom.hom = toSheafify X.J X.O.obj by simp,
    ← toSheafify_naturality]

/-- The canonical map sends each prescribed section to a unit. -/
@[stacks 0EMC "inversion of the prescribed sections"]
theorem isUnit_toLocalizationSheaf (S : MultiplicativeSubpresheaf X)
    [HasWeakSheafify X.J CommRingCat.{w}]
    (U : X.Cᵒᵖ) (s : S.obj U) :
    IsUnit (((S.toLocalizationSheaf).hom.app U).hom (s : X.O.obj.obj U)) := by
  rw [hom_toLocalizationSheaf]
  exact (IsLocalization.map_units (S.localizationPresheaf.obj U) s).map
    ((toSheafify X.J S.localizationPresheaf).app U).hom

/-- A morphism inverting every prescribed section factors uniquely through the
sheafified sectionwise localization. -/
@[stacks 0EMC "universal property"]
theorem existsUnique_lift_toLocalizationSheaf (S : MultiplicativeSubpresheaf X)
    [HasWeakSheafify X.J CommRingCat.{w}]
    (A : Sheaf X.J CommRingCat.{w}) (f : X.O ⟶ A)
    (hf : ∀ (U : X.Cᵒᵖ) (s : S.obj U),
      IsUnit ((f.hom.app U).hom (s : X.O.obj.obj U))) :
    ∃! g : (presheafToSheaf X.J CommRingCat.{w}).obj S.localizationPresheaf ⟶ A,
      S.toLocalizationSheaf ≫ g = f := by
  have hψ : S.toLocalizationPresheaf ≫ localizationPresheafLift S A f hf = f.hom := by
    apply NatTrans.ext
    funext U
    ext x
    show (IsLocalization.lift (M := S.obj U) (hf U))
      (algebraMap (X.O.obj.obj U) (Localization (S.obj U)) x) = (f.hom.app U).hom x
    rw [IsLocalization.lift_eq]
  refine ⟨⟨sheafifyLift X.J (localizationPresheafLift S A f hf) A.property⟩, ?_, ?_⟩
  · apply Sheaf.hom_ext
    show S.toLocalizationSheaf.hom ≫
      sheafifyLift X.J (localizationPresheafLift S A f hf) A.property = f.hom
    rw [hom_toLocalizationSheaf, Category.assoc, toSheafify_sheafifyLift, hψ]
  · intro g' hg'
    apply Sheaf.hom_ext
    apply sheafifyLift_unique X.J _ A.property g'.hom
    have h : S.toLocalizationPresheaf ≫ toSheafify X.J _ ≫ g'.hom =
        S.toLocalizationPresheaf ≫ localizationPresheafLift S A f hf := by
      rw [← Category.assoc, ← hom_toLocalizationSheaf, hψ]
      exact congrArg (fun k => k.hom) hg'
    exact NatTrans.ext <| funext fun U => CommRingCat.hom_ext <|
      IsLocalization.ringHom_ext (S.obj U) (congrArg (fun k => (k.app U).hom) h)

end MultiplicativeSubpresheaf

end AlgebraicGeometry.RingedSite
