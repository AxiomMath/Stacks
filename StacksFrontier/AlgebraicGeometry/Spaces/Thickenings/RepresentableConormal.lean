module

public import StacksFrontier.AlgebraicGeometry.Conormal.IsoSquare
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedConormalModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningImmersionConormal
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormal

/-!
# The conormal sheaf of a morphism of schemes read as a morphism of algebraic spaces

Let `q : V₀ ⟶ U₀` be a morphism of the big fppf site over a scheme `S` whose underlying morphism
of schemes is formally unramified, and let `s` be a universal first order thickening of the
morphism of algebraic spaces it represents.  Two conormal sheaves are attached to `q`: the one of
[Stacks, Tag 04F4], on the Zariski site of `V₀`, and the one of [Stacks, Tag 0607] of `s`, on the
small étale site of the algebraic space `V₀` represents.  This file shows that the second is
finite locally free whenever the first is, which is the comparison by which statements about the
conormal sheaf of a morphism of algebraic spaces are reduced to schemes by étale localization, as
in [Stacks, Tag 06CB].

The scheme-level universal first order thickening `V₀ ⊂ V'` of `q` has its ambient scheme in the
site, since its size is bounded by those of `V₀` and `U₀`; so `V'` represents a universal first
order thickening of algebraic spaces, canonically isomorphic to `s` ([Stacks, Tag 060A]).  Its
conormal module is that of a closed subspace of the representable algebraic space `V'`, which is
the module associated to the scheme-level conormal sheaf
(`AlgebraicGeometry.Space.conormalModuleRepresentedIso`).

## Main definitions

* `AlgebraicGeometry.Space.siteThickeningObj`, `AlgebraicGeometry.Space.siteThickeningInclusion`
  and `AlgebraicGeometry.Space.siteThickeningToBase`: the universal first order thickening of a
  morphism of the site, as a diagram in the site.

## Main results

* `AlgebraicGeometry.Space.contains_ambient_of_isUniversalFirstOrderThickening` (in
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UniversalExistence.lean`) is the size bound
  used here.
* `Stacks.Thickenings.isFiniteLocallyFree_schemeConormalSheaf_of_iso`: the conormal sheaf of any
  universal first order thickening of a morphism of schemes is finite locally free when that of
  the chosen one is.
* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.comp_iso`: universality is preserved
  by composing the structure morphism with an isomorphism of the base.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme`: **the
  comparison.**

## References

* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 04F4](https://stacks.math.columbia.edu/tag/04F4)
* [Stacks Project, Tag 060A](https://stacks.math.columbia.edu/tag/060A)
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Thickenings

/-- **The conormal sheaf of a universal first order thickening is finite locally free as soon as
that of the chosen one is.**  If `i : Z₁ ⟶ Z'` is identified, by isomorphisms of source and
target, with the inclusion of `Z` into the universal first order thickening
`Stacks.Thickenings.universalFirstOrderThickening h`, then the conormal sheaf of `i` is the
inverse image of the conormal sheaf `Stacks.Thickenings.universalConormalSheaf h` of
[Stacks, Tag 04F4] (`Stacks.ClosedImmersion.conormalSheafIsoOfSquare`), and the inverse image of a
finite locally free module is finite locally free. -/
theorem isFiniteLocallyFree_schemeConormalSheaf_of_iso
    {Z X Z₁ Z' : AlgebraicGeometry.Scheme.{u}}
    (h : Z ⟶ X) [AlgebraicGeometry.FormallyUnramified h] (i : Z₁ ⟶ Z') (a : Z₁ ≅ Z)
    (φ : Z' ≅ (universalFirstOrderThickening h).ambient)
    (hφ : i ≫ φ.hom = a.hom ≫ (universalFirstOrderThickening h).inclusion)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (universalConormalSheaf h)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (schemeConormalSheaf i) := by
  let t₀ := universalFirstOrderThickening h
  let F := AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace ⋙
    AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace
  have h₀ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (schemeConormalSheaf t₀.inclusion) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (h := hF) (Stacks.Immersion.conormalSheafSelfIso t₀.inclusion).symm
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
    (h := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme a.hom _ h₀)
    (Stacks.ClosedImmersion.conormalSheafIsoOfSquare (F.mapIso a) (F.mapIso φ) _ _
      (congrArg (fun k : Z₁ ⟶ t₀.ambient => k.toLRSHom.toShHom) hφ)).symm

end Stacks.Thickenings

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A universal first order thickening over `X` stays universal over `X'` after composing its
structure morphism with an isomorphism `X ≅ X'`. -/
theorem IsUniversalFirstOrderThickening.comp_iso {X X' Z' : AlgebraicSpaces B S hS}
    {Z : Subfunctor Z'.1} {p : Z' ⟶ X} (hp : IsUniversalFirstOrderThickening B S hS Z p)
    (ψ : X ≅ X') : IsUniversalFirstOrderThickening B S hS Z (p ≫ ψ.hom) where
  firstOrder := hp.firstOrder
  existsUnique_lift := by
    intro T' T hT a b hab
    have hab' : T.ι ≫ (b ≫ ψ.inv.hom) = a ≫ Z.ι ≫ p.hom := by
      have h := congrArg (· ≫ ψ.inv.hom) hab
      simp only [Category.assoc] at h
      rw [h, ObjectProperty.FullSubcategory.comp_hom]
      simp [← ObjectProperty.FullSubcategory.comp_hom]
    obtain ⟨c, ⟨hc₁, hc₂⟩, hc⟩ := hp.existsUnique_lift T hT a _ hab'
    refine ⟨c, ⟨hc₁, ?_⟩, fun c' ⟨h₁, h₂⟩ => hc c' ⟨h₁, ?_⟩⟩
    · rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, hc₂, Category.assoc]
      simp [← ObjectProperty.FullSubcategory.comp_hom]
    · rw [← h₂, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
      simp [← ObjectProperty.FullSubcategory.comp_hom]

/-- The ambient scheme of the universal first order thickening of a morphism of the site, as an
object of the site. -/
noncomputable abbrev siteThickeningObj {V₀ U₀ : BigFppfOver B S hS} (q : V₀ ⟶ U₀)
    [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map q)] :
    BigFppfOver B S hS :=
  Over.mk (Y := ⟨(Stacks.Thickenings.universalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q)).ambient,
      contains_ambient_of_isUniversalFirstOrderThickening B V₀.left.property U₀.left.property _ _ _
        (Stacks.Thickenings.universalFirstOrderThickening_isUniversal _)⟩)
    (ObjectProperty.homMk (Stacks.Thickenings.universalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q)).toBase ≫ U₀.hom)

/-- The inclusion of the source into the ambient scheme of its universal first order thickening,
as a morphism of the site. -/
noncomputable abbrev siteThickeningInclusion {V₀ U₀ : BigFppfOver B S hS} (q : V₀ ⟶ U₀)
    [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map q)] :
    V₀ ⟶ siteThickeningObj B S hS q :=
  Over.homMk (ObjectProperty.homMk (Stacks.Thickenings.universalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q)).inclusion) (by
    have h := Stacks.Thickenings.universalFirstOrderThickening_inclusion_comp_toBase
      ((BigFppfOver.toScheme B S hS).map q)
    have hw := Over.w q
    refine Eq.trans ?_ hw
    change _ ≫ (_ ≫ _) = _
    rw [← Category.assoc]
    congr 1
    exact ObjectProperty.hom_ext _ h)

/-- The structure morphism of the universal first order thickening of a morphism of the site, as a
morphism of the site. -/
noncomputable abbrev siteThickeningToBase {V₀ U₀ : BigFppfOver B S hS} (q : V₀ ⟶ U₀)
    [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map q)] :
    siteThickeningObj B S hS q ⟶ U₀ :=
  Over.homMk (ObjectProperty.homMk (Stacks.Thickenings.universalFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map q)).toBase) rfl

/-- The ambient object `AlgebraicGeometry.Space.siteThickeningObj` of the site is a universal
first order thickening of the morphism of schemes underlying `q`. -/
theorem isUniversal_siteThickening {V₀ U₀ : BigFppfOver B S hS} (q : V₀ ⟶ U₀)
    [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map q)] :
    Stacks.Thickenings.IsUniversalFirstOrderThickening ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map (siteThickeningInclusion B S hS q))
      ((BigFppfOver.toScheme B S hS).map (siteThickeningToBase B S hS q)) :=
  Stacks.Thickenings.universalFirstOrderThickening_isUniversal _

/-- **Comparison of the conormal sheaves of a morphism of schemes and of the morphism of algebraic
spaces it represents.**  Let `q : V₀ ⟶ U₀` be a morphism of the big fppf site over `S` whose
underlying morphism of schemes is formally unramified, and let `s` be a universal first order
thickening, in the sense of [Stacks, Tag 0607], of the morphism of algebraic spaces it
represents.  If the conormal sheaf of [Stacks, Tag 04F4] of the morphism of schemes is finite
locally free, then so is the conormal sheaf `𝒞_{V₀/U₀}` of `s` on the small étale site.

The universal first order thickening of the morphism of schemes lies in the site
(`AlgebraicGeometry.Space.contains_ambient_of_isUniversalFirstOrderThickening`), so it represents
a universal first order thickening of algebraic spaces
(`AlgebraicGeometry.Space.UniversalFirstOrderThickening.ofSite`), whose conormal sheaf is that of
`s` (`AlgebraicGeometry.Space.UniversalFirstOrderThickening.conormalSheafIso`).  Its conormal
module is read on the representing scheme by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalModule_of_representable`, and the
closed immersion there is identified with the inclusion of the scheme-level thickening. -/
theorem isFiniteLocallyFreeOnSite_conormalSheaf_of_scheme {V₀ U₀ : BigFppfOver B S hS}
    (q : V₀ ⟶ U₀)
    [_root_.AlgebraicGeometry.FormallyUnramified ((BigFppfOver.toScheme B S hS).map q)]
    (s : UniversalFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map q))
    (hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Thickenings.universalConormalSheaf ((BigFppfOver.toScheme B S hS).map q))) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (conormalSheaf B S hS s) := by
  let i := siteThickeningInclusion B S hS q
  let s₁ := UniversalFirstOrderThickening.ofSite s.formallyUnramified i
    (siteThickeningToBase B S hS q) (isUniversal_siteThickening B S hS q)
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (UniversalFirstOrderThickening.conormalSheafIso s₁ s) ?_
  refine (isFiniteLocallyFreeOnSite_conormalSheaf_iff B S hS s₁).2 ?_
  let V' := siteThickeningObj B S hS q
  let Zc : ClosedSubspaces B S hS (yoneda.obj V') := s₁.closedSub
  let j₀ := representedClosedHom B S hS V' Zc
  let eI : yoneda.obj (representedClosedObj B S hS V' Zc) ≅ Zc.1.toFunctor :=
    @asIso _ _ _ _ (Zc.2.2.rep.fst (idEtaleChart B S hS V').1.hom)
      (isIso_representedClosedMap_hom B S hS V' Zc)
  let aY : yoneda.obj (representedClosedObj B S hS V' Zc) ≅ yoneda.obj V₀ :=
    eI ≪≫ s₁.sourceIso.symm
  let a : representedClosedObj B S hS V' Zc ≅ V₀ := yoneda.preimageIso aY
  have haY : yoneda.map a.hom = aY.hom := yoneda.map_preimage aY.hom
  have ha : a.hom ≫ i = j₀ := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, haY, yoneda_map_representedClosedHom]
    show eI.hom ≫ s₁.sourceIso.inv ≫ yoneda.map i = eI.hom ≫ Zc.1.ι
    congr 1
    refine (Iso.inv_comp_eq _).2 ?_
    exact (Subfunctor.toRange_ι (yoneda.map i)).symm
  refine isFiniteLocallyFreeOnSite_conormalModule_of_representable B S hS V' Zc ?_
  exact Stacks.Thickenings.isFiniteLocallyFree_schemeConormalSheaf_of_iso _ _
    ((BigFppfOver.toScheme B S hS).mapIso a) (Iso.refl _)
    ((Category.comp_id _).trans
      (((BigFppfOver.toScheme B S hS).congr_map ha.symm).trans (Functor.map_comp _ _ _))) hF

end AlgebraicGeometry.Space

end
