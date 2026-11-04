module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsPullbackComposition

/-!
# Transitivity of restriction of sections in the scheme over the base

Let `p : T ⟶ Z` be a morphism of schemes, let `W` be an object of the small étale site of `Z`, and
let `r : T ⟶ W` be a morphism lying over `p`. Restriction of sections
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` carries a section of an abelian étale sheaf
`F` on `Z` over `W` to a global section of `p⁻¹F` on `T`. For a further morphism `c : T' ⟶ T` the
composite `c ≫ r` lies over `c ≫ p`, so the same construction restricts a section over `W` all the
way to a global section of `(c ≫ p)⁻¹F` on `T'`; and the two-step route is to restrict to `T` first
and then restrict global sections along `c`. The two agree, modulo the composition isomorphism
`c⁻¹p⁻¹F ≅ (c ≫ p)⁻¹F`:

`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_base`.

This is the compatibility of `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` with composition
*in the scheme over the base*. It is a different statement from the two compatibilities already in
the library, and neither implies it on its own:
`Stacks.EtaleCohomology.map_comp_smallEtaleSectionsPullbackAb` is transitivity along a morphism of
étale objects of one fixed site, the scheme over the base being held fixed, and
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_app` is the compatibility in the morphism
variable, which factors the restriction through the base change of the étale object.

A consequence is `AlgebraicGeometry.etaleStalkToSectionsAb_comp`: the map
`AlgebraicGeometry.etaleStalkToSectionsAb` from the étale stalk at a geometric point `x` of `X` to
the global sections over a scheme `T` over `Spec 𝒪^{sh}_{X,x}`, formed for
`T' ⟶ T ⟶ Spec 𝒪^{sh}_{X,x}`, is the one formed for `T` followed by restriction of global sections
along `T' ⟶ T`. Since the stalk is the colimit of the sections over the étale neighbourhoods of
`x`, this is the statement above on each germ: the germ-level maps are restrictions of sections,
along the composite of `T ⟶ Spec 𝒪^{sh}_{X,x}` with the unique morphism from the strict
henselization into the neighbourhood, and the morphism for `T'` is the one for `T` precomposed with
`c`.

## The route

The three available compatibilities fit together on the nose. Restriction along `c` is, by
definition of `Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb`, restriction of
sections from the terminal object of the small étale site of `T`; transitivity in the étale object
over `T` turns the restriction to `T` followed by that into restriction from the base change of `W`
along `p`, which is exactly the inner map of the compatibility in the morphism variable; and the
morphism into `W` which the latter produces is `c ≫ r`, because the lift of `T` into the base
change has first projection `r`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_congr_base` — restriction of sections is
  transported along an equality of the structure morphism by the induced identification of the
  inverse-image functors.
* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_base` — restriction of sections along a
  morphism over `c ≫ p` is restriction along the morphism over `p` followed by restriction of
  global sections along `c`.
* `AlgebraicGeometry.etaleStalkSectionsStage_comp` — the same identity on the germ at `x` of a
  section over an étale neighbourhood.
* `AlgebraicGeometry.etaleStalkToSectionsAb_comp` — the map on abelian sheaves out of the étale
  stalk for `T' ⟶ T ⟶ Spec 𝒪^{sh}_{X,x}` is the one for `T` followed by restriction of global
  sections along `T' ⟶ T`.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### A reassociation

The composite of the unit of the inverse-image/direct-image adjunction with a map on sections of
the inverse image is type-correct only after the direct image is unfolded, which stops `simp` from
reassociating such a composite in place. Stating the reassociation for abstract morphisms in an
abstract category and applying it by `exact` makes the elaborator do the unfolding once. -/

section Bookkeeping

variable {C : Type*} [Category C]

/-- The reassociation behind
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_base`: two mutually inverse maps cancel
in the middle of a composite of six, after an identity is removed and a two-fold composite is
contracted. -/
private theorem comp_shuffle_base {A₀ A₁ A₂ A₃ A₄ A₅ : C} (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂)
    (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₂) (a₅ : A₂ ⟶ A₄) (i : A₄ ⟶ A₄) (a₆ : A₄ ⟶ A₅) (b : A₁ ⟶ A₄)
    (h₃₄ : a₃ ≫ a₄ = 𝟙 A₂) (hi : i = 𝟙 A₄) (hb : a₂ ≫ a₅ = b) :
    ((a₁ ≫ a₂) ≫ a₃) ≫ (a₄ ≫ a₅) ≫ i ≫ a₆ = a₁ ≫ b ≫ a₆ := by
  subst hi
  subst hb
  simp only [Category.assoc, Category.id_comp]
  rw [← Category.assoc a₃ a₄, h₃₄, Category.id_comp]

/-- The reassociation behind `AlgebraicGeometry.etaleStalkToSectionsAb_comp`: a composite of three
maps, with the first two contracted. Stated abstractly because the goal it is applied to involves
the étale stalk, whose identification with the fibre of the underlying presheaf is not available
at the transparency level `rw` type-checks under. -/
private theorem comp_contract {A₀ A₁ A₂ A₃ : C} (s : A₀ ⟶ A₁) (a : A₁ ⟶ A₂) (t : A₂ ⟶ A₃)
    (g : A₀ ⟶ A₂) (hg : s ≫ a = g) : g ≫ t = s ≫ a ≫ t := by
  subst hg
  exact Category.assoc _ _ _

/-- The reassociation behind `AlgebraicGeometry.etaleStalkSectionsStage_comp`: a composite of four
maps is transported along a fifth and the last two are contracted. -/
private theorem comp_transport_merge {A₀ A₁ A₂ A₃ A₄ A₅ : C} (lhs : A₀ ⟶ A₅) (mid : A₀ ⟶ A₄)
    (a : A₀ ⟶ A₁) (u : A₁ ⟶ A₂) (v : A₂ ⟶ A₃) (w₁ : A₃ ⟶ A₄) (w₂ : A₄ ⟶ A₅) (w : A₃ ⟶ A₅)
    (h₁ : lhs = mid ≫ w₂) (h₂ : mid = a ≫ u ≫ v ≫ w₁) (hw : w₁ ≫ w₂ = w) :
    lhs = a ≫ u ≫ v ≫ w := by
  subst hw
  subst h₂
  subst h₁
  simp only [Category.assoc]

end Bookkeeping

/-! ### Transport along an equality of structure morphisms -/

section CongrBase

variable {Z T : Scheme.{u}}

/-- Restriction of sections depends on the structure morphism of `T` over `Z` only through the
inverse-image functor it names: for equal structure morphisms and equal morphisms into the étale
object, the two restrictions of sections agree after the identification of the two inverse-image
functors. -/
public theorem smallEtaleSectionsPullbackAb_congr_base {p p' : T ⟶ Z} (W : Z.Etale)
    {r r' : T ⟶ W.left} (hp : p = p') (hr : r = r') (h : r ≫ W.hom = p)
    (h' : r' ≫ W.hom = p') :
    smallEtaleSectionsPullbackAb p' W r' h' =
      smallEtaleSectionsPullbackAb p W r h ≫
        Functor.whiskerRight
          (eqToIso (congrArg (fun m : T ⟶ Z => smallEtalePullbackAb m) hp)).hom
          (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) := by
  subst hp
  subst hr
  simp only [eqToIso_refl, Iso.refl_hom, Functor.whiskerRight_id', Category.comp_id]

end CongrBase

/-! ### Transitivity in the scheme over the base -/

section CompBase

variable {Z T T' : Scheme.{u}} (p : T ⟶ Z) (c : T' ⟶ T) (W : Z.Etale) (r : T ⟶ W.left)

/-- **Restriction of sections is transitive in the scheme over the base.** Restricting a section of
an abelian étale sheaf `F` on `Z` over an étale object `W`, along a morphism `c ≫ r : T' ⟶ W` lying
over `c ≫ p`, is restricting along `r : T ⟶ W` first and then restricting the resulting global
section of `p⁻¹F` on `T` along `c`, read through the composition isomorphism
`c⁻¹p⁻¹F ≅ (c ≫ p)⁻¹F`.

Restriction of global sections along `c` is restriction of sections from the terminal object of the
small étale site of `T`, so the left-hand side is reached by transitivity in the étale object over
`T` followed by the compatibility of restriction with composition in the morphism variable. -/
public theorem smallEtaleSectionsPullbackAb_comp_base (hr : r ≫ W.hom = p)
    (hcr : (c ≫ r) ≫ W.hom = c ≫ p) :
    smallEtaleSectionsPullbackAb (c ≫ p) W (c ≫ r) hcr =
      smallEtaleSectionsPullbackAb p W r hr ≫
        Functor.whiskerLeft (smallEtalePullbackAb p) (smallEtaleGlobalSectionsRestrictionAb c) ≫
          (Functor.associator (smallEtalePullbackAb p) (smallEtalePullbackAb c)
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
            Functor.whiskerRight (smallEtalePullbackAbCompIso c p).hom
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) := by
  have hover := MorphismProperty.Over.w (smallEtaleBaseChangeLift p W r hr)
  have hρ : (c ≫ (smallEtaleBaseChangeLift p W r hr).left) ≫
      ((smallEtaleBaseChange p).obj W).hom = c :=
    (Category.assoc _ _ _).trans
      ((congrArg (c ≫ ·) hover).trans (Category.comp_id c))
  have hlift : (smallEtaleBaseChangeLift p W r hr).left ≫ pullback.fst W.hom p = r :=
    pullback.lift_fst r (𝟙 T) (hr.trans (Category.id_comp p).symm)
  have hfst : c ≫ r =
      (c ≫ (smallEtaleBaseChangeLift p W r hr).left) ≫ pullback.fst W.hom p :=
    (congrArg (c ≫ ·) hlift.symm).trans (Category.assoc _ _ _).symm
  have hcr' : ((c ≫ (smallEtaleBaseChangeLift p W r hr).left) ≫ pullback.fst W.hom p) ≫ W.hom =
      c ≫ p :=
    (congrArg (· ≫ W.hom) hfst.symm).trans hcr
  refine NatTrans.ext (funext fun F => ?_)
  have hb := congrArg (fun σ => NatTrans.app σ ((smallEtalePullbackAb p).obj F))
    (map_comp_smallEtaleSectionsPullbackAb c (Scheme.Etale.mk (𝟙 T)) c
      (smallEtaleBaseChangeLift p W r hr) (Category.comp_id c) hρ)
  refine (congrArg (fun σ => NatTrans.app σ F)
      (smallEtaleSectionsPullbackAb_congr (c ≫ p) W (c ≫ r) hcr hcr' hfst)).trans
    ((smallEtaleSectionsPullbackAb_comp_app c p W
      (c ≫ (smallEtaleBaseChangeLift p W r hr).left) hρ hcr' F).symm.trans ?_)
  exact (comp_shuffle_base
    (((smallEtaleAdjunctionAb p).unit.app F).hom.app (op W))
    (((smallEtalePullbackAb p).obj F).obj.map (smallEtaleBaseChangeLift p W r hr).op)
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).inv.app ((smallEtalePullbackAb p).obj F))
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).hom.app ((smallEtalePullbackAb p).obj F))
    ((smallEtaleSectionsPullbackAb c (Scheme.Etale.mk (𝟙 T)) c (Category.comp_id c)).app
      ((smallEtalePullbackAb p).obj F))
    ((Functor.associator (smallEtalePullbackAb p) (smallEtalePullbackAb c)
      (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv.app F)
    ((Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}).map
      ((smallEtalePullbackAbCompIso c p).hom.app F))
    ((smallEtaleSectionsPullbackAb c ((smallEtaleBaseChange p).obj W)
      (c ≫ (smallEtaleBaseChangeLift p W r hr).left) hρ).app ((smallEtalePullbackAb p).obj F))
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).inv_hom_id_app ((smallEtalePullbackAb p).obj F)) rfl hb).symm

end CompBase

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-! ### The map out of the étale stalk -/

section StalkCompBase

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T T' : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x) (c : T' ⟶ T)

/-- Inverse image along `c : T' ⟶ T` of the inverse image along the structure morphism
`T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ X` is inverse image along the structure morphism of `T'` over `X`: the
composition isomorphism for inverse images, read through the associativity of the composite. -/
public def etaleStalkSectionsRestrictionCompIso :
    smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x) ⋙ smallEtalePullbackAb c ≅
      smallEtalePullbackAb ((c ≫ q) ≫ strictHenselizationToBase B X hX x) :=
  smallEtalePullbackAbCompIso c (q ≫ strictHenselizationToBase B X hX x) ≪≫
    eqToIso (congrArg (fun m : T' ⟶ X => smallEtalePullbackAb m)
      (Category.assoc c q (strictHenselizationToBase B X hX x)).symm)

/-- On the germ at `x` of a section over an étale neighbourhood `W`, the germ-level map for
`T' ⟶ T ⟶ Spec 𝒪^{sh}_{X,x}` is the one for `T` followed by restriction of global sections along
`c : T' ⟶ T`.

Both are restrictions of sections along a morphism into `W`, the one for `T'` being the one for `T`
precomposed with `c`, so this is transitivity of restriction of sections in the scheme over the
base. -/
public theorem etaleStalkSectionsStage_comp (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (W : X.Etale) (v : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    etaleStalkSectionsStage B X hX x (c ≫ q) F W v =
      etaleStalkSectionsStage B X hX x q F W v ≫
        (Functor.whiskerLeft
              (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
              (smallEtaleGlobalSectionsRestrictionAb c) ≫
            (Functor.associator
                (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
                (smallEtalePullbackAb c)
                (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
              Functor.whiskerRight (etaleStalkSectionsRestrictionCompIso B X hX x q c).hom
                (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).app F := by
  have hp : c ≫ q ≫ strictHenselizationToBase B X hX x =
      (c ≫ q) ≫ strictHenselizationToBase B X hX x :=
    (Category.assoc c q (strictHenselizationToBase B X hX x)).symm
  have hlift : ∀ {S : Scheme.{u}} (q : S ⟶ strictHenselization B X hX x),
      (q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ W.hom =
        q ≫ strictHenselizationToBase B X hX x := fun q => by
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]
  have h₃ : (c ≫ q ≫ strictHenselizationNeighborhoodLift B X hX x W v) ≫ W.hom =
      c ≫ q ≫ strictHenselizationToBase B X hX x := by
    rw [Category.assoc, hlift q]
  have hmerge : Functor.whiskerRight
          (smallEtalePullbackAbCompIso c (q ≫ strictHenselizationToBase B X hX x)).hom
          (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) ≫
        Functor.whiskerRight
          (eqToIso (congrArg (fun m : T' ⟶ X => smallEtalePullbackAb m) hp)).hom
          (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) =
      Functor.whiskerRight (etaleStalkSectionsRestrictionCompIso B X hX x q c).hom
        (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) :=
    (Functor.whiskerRight_comp
      (smallEtalePullbackAbCompIso c (q ≫ strictHenselizationToBase B X hX x)).hom
      (eqToIso (congrArg (fun m : T' ⟶ X => smallEtalePullbackAb m) hp)).hom
      (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).symm
  exact congrArg (fun σ => NatTrans.app σ F)
    (comp_transport_merge _ _ _ _ _ _ _ _
      (smallEtaleSectionsPullbackAb_congr_base W hp (Category.assoc _ _ _).symm h₃ (hlift (c ≫ q)))
      (smallEtaleSectionsPullbackAb_comp_base (q ≫ strictHenselizationToBase B X hX x) c W
        (q ≫ strictHenselizationNeighborhoodLift B X hX x W v) (hlift q) h₃)
      hmerge)

/-- **Transitivity of restriction of sections in the scheme over the strict henselization.** For a
morphism `c : T' ⟶ T` of schemes over `Spec 𝒪^{sh}_{X,x}`, the map
`AlgebraicGeometry.etaleStalkToSectionsAb` on abelian étale sheaves for `T'` is the one for `T`
followed by restriction of global sections along `c`, read through the composition isomorphism
identifying the inverse image along the structure morphism of `T'` with the iterated inverse image.

The stalk at `x` is the colimit of the sections over the étale neighbourhoods of `x`, so the
identity is `AlgebraicGeometry.etaleStalkSectionsStage_comp` on each germ. -/
public theorem etaleStalkToSectionsAb_comp :
    etaleStalkToSectionsAb B X hX x (c ≫ q) =
      etaleStalkToSectionsAb B X hX x q ≫
        Functor.whiskerLeft
            (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
            (smallEtaleGlobalSectionsRestrictionAb c) ≫
          (Functor.associator
              (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
              (smallEtalePullbackAb c)
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
            Functor.whiskerRight (etaleStalkSectionsRestrictionCompIso B X hX x q c).hom
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) := by
  refine NatTrans.ext (funext fun F => ?_)
  refine (Scheme.pointSmallEtale x.hom).presheafFiber_hom_ext fun W v => ?_
  exact (etaleStalkToSectionsAb_toPresheafFiber B X hX x (c ≫ q) F W v).trans
    ((etaleStalkSectionsStage_comp B X hX x q c F W v).trans
      (comp_contract _ _ _ _ (etaleStalkToSectionsAb_toPresheafFiber B X hX x q F W v)))

end StalkCompBase

end AlgebraicGeometry

end
