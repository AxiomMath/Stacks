module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStageBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Polarized families along cartesian squares and along isomorphisms of total spaces

Two ways of producing a polarized family (Stacks 0D1M) from another one without choosing a fibre
product:

* `AlgebraicGeometry.PolarizedFamily.ofIsPullback`: the base change of a polarized family along
  a morphism of bases, read on an *arbitrary* cartesian square rather than on the chosen fibre
  product, together with the morphism of polarized families it carries;
* `AlgebraicGeometry.PolarizedFamily.transportTotal`: the same polarized family with its total
  space replaced by an isomorphic scheme, together with the isomorphism of polarized families
  over the identity of the base.

Both are what lets a statement about polarized families be checked on a presentation of the total
spaces chosen for convenience, as in the proof of Stacks 0D44.

## References

* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PolarizedFamily

universe u

variable {B : BigFppfSite.{u}}

/-- The comparison of polarizations of a composite of morphisms of polarized families. -/
theorem comp_lineBundleIso_hom {x y z : PolarizedFamily B} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (φ ≫ ψ).lineBundleIso.hom =
      (Scheme.Modules.pullbackComp φ.totalMap ψ.totalMap).inv.app z.lineBundle ≫
        (Scheme.Modules.pullback φ.totalMap).map ψ.lineBundleIso.hom ≫ φ.lineBundleIso.hom :=
  rfl

/-- Two morphisms of polarized families with the same base map and the same map of total spaces
are equal as soon as their comparisons of polarizations agree up to the transport between the two
pullbacks of the polarization. -/
theorem Hom.ext_of_lineBundleIso_hom {z y : PolarizedFamily B} {φ ψ : z ⟶ y}
    (hb : φ.baseMap = ψ.baseMap) (ht : φ.totalMap = ψ.totalMap)
    (hl : φ.lineBundleIso.hom = eqToHom (congrArg (fun k : z.total ⟶ y.total ↦
      (Scheme.Modules.pullback k).obj y.lineBundle) ht) ≫ ψ.lineBundleIso.hom) : φ = ψ := by
  obtain ⟨b, t, c, l⟩ := φ
  obtain ⟨b', t', c', l'⟩ := ψ
  change b = b' at hb
  change t = t' at ht
  subst hb ht
  have : l = l' := Iso.ext (hl.trans (Category.id_comp _))
  subst this
  rfl

section OfIsPullback

variable (x : PolarizedFamily B) {V : B.Schemes} (k : V ⟶ x.base) {Z : Scheme.{u}}
  {a : Z ⟶ x.total} {b : Z ⟶ B.inclusion.obj V}

/-- The polarization stays invertible after pullback along any morphism of total spaces. -/
theorem isInvertible_pullback_of_hom (a : Z ⟶ x.total) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback a).obj x.lineBundle) :=
  have := x.invertible
  Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback a.toLRSHom.toShHom
    x.lineBundle

/-- **The base change of a polarized family along a cartesian square.** For a cartesian square
with sides `a : Z ⟶ x.total`, `b : Z ⟶ V`, the structure morphism of `x` and `k : V ⟶ x.base`,
the polarized family with base `V`, total space `Z` and polarization pulled back along `a`.
Properness, flatness and finite presentation are stable under base change, and relative
ampleness of the pulled back polarization is Stacks 0893 for an arbitrary cartesian square. -/
@[ega "II 4.6.13" "(iii)"]
abbrev ofIsPullback (hpb : IsPullback a b x.toBase (B.inclusion.map k)) : PolarizedFamily B where
  base := V
  total := Z
  toBase := b
  proper := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    hpb x.proper
  flat := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hpb x.flat
  finitePresentation :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation)
        hpb x.finitePresentation.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
        hpb x.finitePresentation.2.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
        hpb x.finitePresentation.2.2⟩
  lineBundle := (Scheme.Modules.pullback a).obj x.lineBundle
  invertible := x.isInvertible_pullback_of_hom a
  relativelyAmple :=
    have := x.invertible
    have := x.isInvertible_pullback_of_hom a
    Stacks.AmpleBridge.relativelyAmpleBaseChange hpb x.lineBundle x.relativelyAmple

/-- The morphism of polarized families carried by a base change along a cartesian square: the
square itself, with the identity comparison of polarizations. -/
abbrev ofIsPullbackHom (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    x.ofIsPullback k hpb ⟶ x where
  baseMap := k
  totalMap := a
  cartesian := hpb
  lineBundleIso := Iso.refl _

/-- The base of the base change along a cartesian square is the new base. -/
@[simp]
theorem ofIsPullback_base (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    (x.ofIsPullback k hpb).base = V := rfl

/-- The total space of the base change along a cartesian square is the corner of the square. -/
@[simp]
theorem ofIsPullback_total (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    (x.ofIsPullback k hpb).total = Z := rfl

/-- The structure morphism of the base change along a cartesian square is the side `b`. -/
@[simp]
theorem ofIsPullback_toBase (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    (x.ofIsPullback k hpb).toBase = b := rfl

/-- The polarization of the base change along a cartesian square is the pullback along `a`. -/
@[simp]
theorem ofIsPullback_lineBundle (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    (x.ofIsPullback k hpb).lineBundle = (Scheme.Modules.pullback a).obj x.lineBundle := rfl

/-- The base map of the morphism carried by a cartesian square is `k`. -/
@[simp]
theorem ofIsPullbackHom_baseMap (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    (x.ofIsPullbackHom k hpb).baseMap = k := rfl

/-- The map of total spaces of the morphism carried by a cartesian square is `a`. -/
@[simp]
theorem ofIsPullbackHom_totalMap (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    (x.ofIsPullbackHom k hpb).totalMap = a := rfl

/-- The comparison of polarizations of the morphism carried by a cartesian square is the
identity. -/
@[simp]
theorem ofIsPullbackHom_lineBundleIso (hpb : IsPullback a b x.toBase (B.inclusion.map k)) :
    (x.ofIsPullbackHom k hpb).lineBundleIso = Iso.refl _ := rfl

end OfIsPullback

section Transport

variable (x : PolarizedFamily B) {Z : Scheme.{u}} (e : x.total ≅ Z)

/-- **A polarized family with its total space replaced by an isomorphic scheme**: the structure
morphism and the polarization are carried across the isomorphism. -/
abbrev transportTotal : PolarizedFamily B :=
  x.ofIsPullback (𝟙 x.base) (a := e.inv) (b := e.inv ≫ x.toBase)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- Transporting the total space does not change the base. -/
@[simp]
theorem transportTotal_base : (x.transportTotal e).base = x.base := rfl

/-- The total space of the transported family is the new scheme. -/
@[simp]
theorem transportTotal_total : (x.transportTotal e).total = Z := rfl

/-- The structure morphism of the transported family is `e⁻¹` followed by the old one. -/
@[simp]
theorem transportTotal_toBase : (x.transportTotal e).toBase = e.inv ≫ x.toBase := rfl

/-- The polarization of the transported family is the pullback along `e⁻¹`. -/
@[simp]
theorem transportTotal_lineBundle :
    (x.transportTotal e).lineBundle = (Scheme.Modules.pullback e.inv).obj x.lineBundle := rfl

/-- The morphism from a transported polarized family back to the original one, over the identity
of the base. -/
def transportTotalInv : x.transportTotal e ⟶ x :=
  x.ofIsPullbackHom (𝟙 x.base) (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- The base map of the morphism back from the transport is the identity. -/
@[simp]
theorem transportTotalInv_baseMap : (x.transportTotalInv e).baseMap = 𝟙 x.base := rfl

/-- The map of total spaces of the morphism back from the transport is `e⁻¹`. -/
@[simp]
theorem transportTotalInv_totalMap : (x.transportTotalInv e).totalMap = e.inv := rfl

/-- The morphism from a polarized family to its transport, over the identity of the base: the
given isomorphism of total spaces, with the comparison of polarizations
`e^* e⁻¹^* L ≅ (e⁻¹ ∘ e)^* L = L`. -/
def transportTotalHom : x ⟶ x.transportTotal e where
  baseMap := 𝟙 x.base
  totalMap := e.hom
  cartesian := by
    change IsPullback e.hom x.toBase (e.inv ≫ x.toBase) (B.inclusion.map (𝟙 x.base))
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  lineBundleIso :=
    (Scheme.Modules.pullbackComp e.hom e.inv).app x.lineBundle ≪≫
      (Scheme.Modules.pullbackCongr e.hom_inv_id).app x.lineBundle ≪≫
        (Scheme.Modules.pullbackId x.total).app x.lineBundle

/-- The base map of the morphism to the transport is the identity. -/
@[simp]
theorem transportTotalHom_baseMap : (x.transportTotalHom e).baseMap = 𝟙 x.base := rfl

/-- The map of total spaces of the morphism to the transport is `e`. -/
@[simp]
theorem transportTotalHom_totalMap : (x.transportTotalHom e).totalMap = e.hom := rfl

/-- The morphism to a transported polarized family followed by the morphism back is the
identity. -/
@[simp]
theorem transportTotalHom_comp_transportTotalInv :
    x.transportTotalHom e ≫ x.transportTotalInv e = 𝟙 x := by
  refine Hom.ext (Category.comp_id _) e.hom_inv_id ?_
  have hobj : (Scheme.Modules.pullback (e.hom ≫ e.inv)).obj x.lineBundle =
      (Scheme.Modules.pullback (𝟙 x.total)).obj x.lineBundle := by rw [e.hom_inv_id]
  have key : Hom.lineBundleIso (x.transportTotalHom e ≫ x.transportTotalInv e) =
      eqToIso hobj ≪≫ (Scheme.Modules.pullbackId x.total).app x.lineBundle := by
    refine Iso.ext ?_
    change (Scheme.Modules.pullbackComp e.hom e.inv).inv.app x.lineBundle ≫
      (Scheme.Modules.pullback e.hom).map (𝟙 _) ≫
        ((Scheme.Modules.pullbackComp e.hom e.inv).hom.app x.lineBundle ≫
          (Scheme.Modules.pullbackCongr e.hom_inv_id).hom.app x.lineBundle ≫
          (Scheme.Modules.pullbackId x.total).hom.app x.lineBundle) = _
    simp [Scheme.Modules.pullbackCongr]
  exact (heq_of_eq key).trans (eqToIso_trans_heq hobj _)

end Transport

end AlgebraicGeometry.PolarizedFamily

end
