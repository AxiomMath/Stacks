module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsTransitivityOverBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange

/-!
# The map out of an étale stalk under inverse image along a morphism of the ambient scheme

Let `g : X' ⟶ X` be a morphism of schemes, let `x'` be a geometric point of `X'` with image
`x = g(x')` in `X`, and write

`m : Spec 𝒪^{sh}_{X',x'} ⟶ Spec 𝒪^{sh}_{X,x}`

for the induced morphism of strict henselizations, and `β`, `β'` for the morphisms from the strict
henselizations to `X`, `X'`. Let `T` be a scheme over `Spec 𝒪^{sh}_{X,x}` with structure morphism
`q`, let `T'` be a scheme over `Spec 𝒪^{sh}_{X',x'}` with structure morphism `q'`, and let
`ι : T' ⟶ T` be a morphism with `q' ≫ m = ι ≫ q`.

The map `AlgebraicGeometry.etaleStalkToSectionsAb` of Tag 0GJN is then compatible with inverse
image along `g`: the map

`(g⁻¹F)_{x'} ⟶ Γ(T', (q' ≫ β')⁻¹g⁻¹F)`

formed on `X'`, read through the identification `(g⁻¹F)_{x'} = F_x` of
`Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso`, is the map `F_x ⟶ Γ(T, (q ≫ β)⁻¹F)`
formed on `X` followed by restriction of global sections along `ι`. This file proves that, as
`AlgebraicGeometry.etaleStalkToSectionsAb_pullback`.

## Main results

* `Stacks.EtaleCohomology.pointSmallEtaleComapFiberIso_hom_app_left_fst`: the lift of `x'` to a
  base change `W ×_X X'` corresponding to a lift of `x` to `W` has that lift as its projection
  to `W`.
* `AlgebraicGeometry.strictHenselizationNeighborhoodLift_smallEtaleBaseChange`: the morphism
  from the strict henselization at `x'` into the base change of an étale neighbourhood of `x`,
  followed by the projection, is the morphism of strict henselizations followed by the morphism
  into that neighbourhood.
* `AlgebraicGeometry.etaleStalkSectionsStage_pullback`: the compatibility on the germ at `x` of
  a section over an étale neighbourhood.
* `AlgebraicGeometry.etaleStalkToSectionsAb_pullback`: the compatibility of the map of Tag 0GJN
  with inverse image along `g`.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Three reassociations -/

section Bookkeeping

variable {C : Type*} [Category C]

/-- A composite `s ≫ i ≫ a ≫ e ≫ t` equals `v ≫ b ≫ t` when `s ≫ i = v ≫ p`, `p ≫ a = b` and
`e` is an identity. -/
private theorem comp_shuffle_source {A₀ A₁ A₂ A₃ A₄ A₅ : C} (s : A₀ ⟶ A₁) (i : A₁ ⟶ A₂)
    (a : A₂ ⟶ A₃) (e : A₃ ⟶ A₃) (t : A₃ ⟶ A₄) (v : A₀ ⟶ A₅) (p : A₅ ⟶ A₂) (b : A₅ ⟶ A₃)
    (h₁ : s ≫ i = v ≫ p) (h₂ : p ≫ a = b) (he : e = 𝟙 A₃) :
    s ≫ i ≫ a ≫ e ≫ t = v ≫ b ≫ t := by
  subst he
  subst h₂
  simp only [Category.id_comp, ← Category.assoc, h₁]

/-- A composite `s ≫ a ≫ t` equals `b ≫ t` when `s ≫ a = b`. -/
private theorem comp_contract_source {A₀ A₁ A₂ A₃ : C} (s : A₀ ⟶ A₁) (a : A₁ ⟶ A₂) (t : A₂ ⟶ A₃)
    (b : A₀ ⟶ A₂) (hb : s ≫ a = b) : s ≫ a ≫ t = b ≫ t := by
  subst hb
  exact (Category.assoc _ _ _).symm

/-- A composite `(p ≫ a ≫ b ≫ c) ≫ d` equals `p ≫ a ≫ b ≫ cd` when `c ≫ d = cd`. -/
private theorem comp_assoc_tail {A₀ A₁ A₂ A₃ A₄ A₅ : C} (p : A₀ ⟶ A₁) (a : A₁ ⟶ A₂)
    (b : A₂ ⟶ A₃) (c : A₃ ⟶ A₄) (d : A₄ ⟶ A₅) (cd : A₃ ⟶ A₅) (hcd : c ≫ d = cd) :
    (p ≫ a ≫ b ≫ c) ≫ d = p ≫ a ≫ b ≫ cd := by
  subst hcd
  simp only [Category.assoc]

/-- A composite `(s ≫ a) ≫ w` equals `s ≫ b` when `a ≫ w = b`. -/
private theorem comp_comp_eq_comp_of_comp_eq {A₀ A₁ A₂ A₃ : C} (s : A₀ ⟶ A₁) (a : A₁ ⟶ A₂)
    (w : A₂ ⟶ A₃) (b : A₁ ⟶ A₃) (h : a ≫ w = b) : (s ≫ a) ≫ w = s ≫ b := by
  rw [Category.assoc, h]

end Bookkeeping

/-! ### Lifts of a geometric point to a base change -/

section Fiber

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X')

/-- The lift of a geometric point `s` of `X'` to the base change `W ×_X X'` of an étale object
`W` of the small étale site of `X` which corresponds to a lift of `s ≫ g` to `W` has that lift as
its projection to `W`. -/
public theorem pointSmallEtaleComapFiberIso_hom_app_left_fst (W : X.Etale)
    (v : (Scheme.pointSmallEtale (s ≫ g)).fiber.obj W) :
    ((pointSmallEtaleComapFiberIso g s).hom.app W v).left ≫ pullback.fst W.hom g = v.left := by
  simp only [pointSmallEtaleComapFiberIso, pointSmallEtaleBaseChangeFiberIso,
    NatIso.ofComponents_hom_app, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

/-- The lift of a geometric point `s` of `X'` to the base change `W ×_X X'` of an étale object
`W` of the small étale site of `X` lies over `s` itself: its projection to `X'` is `s`. -/
public theorem pointSmallEtaleComapFiberIso_hom_app_left_snd (W : X.Etale)
    (v : (Scheme.pointSmallEtale (s ≫ g)).fiber.obj W) :
    ((pointSmallEtaleComapFiberIso g s).hom.app W v).left ≫ pullback.snd W.hom g = s := by
  simp only [pointSmallEtaleComapFiberIso, pointSmallEtaleBaseChangeFiberIso,
    NatIso.ofComponents_hom_app, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_snd _ _ _

end Fiber

/-! ### Restriction of sections along a composite in the scheme over the base, transported -/

section CompBaseCongr

variable {Z T T' : Scheme.{u}} (p : T ⟶ Z) (c : T' ⟶ T) (W : Z.Etale) (r : T ⟶ W.left)

/-- Restriction of sections along a morphism `r' : T' ⟶ W` which is `c : T' ⟶ T` followed by
`r : T ⟶ W`, over a structure morphism `p' : T' ⟶ Z` which is `c` followed by `p : T ⟶ Z`, is
restriction along `r` followed by restriction of global sections along `c`, read through the
composition isomorphism for inverse image and the identification of the two names of the
structure morphism of `T'`. -/
public theorem smallEtaleSectionsPullbackAb_comp_base_congr {p' : T' ⟶ Z} {r' : T' ⟶ W.left}
    (hr : r ≫ W.hom = p) (hcr : (c ≫ r) ≫ W.hom = c ≫ p) (hp : c ≫ p = p')
    (hrr : c ≫ r = r') (h' : r' ≫ W.hom = p') :
    smallEtaleSectionsPullbackAb p' W r' h' =
      smallEtaleSectionsPullbackAb p W r hr ≫
        (Functor.whiskerLeft (smallEtalePullbackAb p)
              (smallEtaleGlobalSectionsRestrictionAb c) ≫
            (Functor.associator (smallEtalePullbackAb p) (smallEtalePullbackAb c)
                (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
              Functor.whiskerRight ((smallEtalePullbackAbCompIso c p).hom ≫
                (eqToIso (congrArg (fun m : T' ⟶ Z => smallEtalePullbackAb m) hp)).hom)
                (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})) := by
  refine (smallEtaleSectionsPullbackAb_congr_base W hp hrr hcr h').trans ?_
  refine (congrArg (· ≫ Functor.whiskerRight
      (eqToIso (congrArg (fun m : T' ⟶ Z => smallEtalePullbackAb m) hp)).hom
      (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}))
    (smallEtaleSectionsPullbackAb_comp_base p c W r hr hcr)).trans ?_
  exact comp_assoc_tail _ _ _ _ _ _
    (Functor.whiskerRight_comp (smallEtalePullbackAbCompIso c p).hom
      (eqToIso (congrArg (fun m : T' ⟶ Z => smallEtalePullbackAb m) hp)).hom
      (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).symm

end CompBaseCongr

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-! ### The morphism from a strict henselization into a base changed neighbourhood -/

section Lift

variable (B : BigEtaleSite.{u}) {X X' : Scheme.{u}} (hX : B.Contains X) (hX' : B.Contains X')
  (g : X' ⟶ X) (x' : GeometricPoint X')

/-- **The morphism from the strict henselization into a base changed étale neighbourhood.** For
`g : X' ⟶ X`, a geometric point `x'` of `X'` with image `x` in `X`, and an étale neighbourhood
`W` of `x`, the unique morphism from `Spec 𝒪^{sh}_{X',x'}` into the étale neighbourhood
`W ×_X X'` of `x'`, followed by the projection to `W`, is the induced morphism of strict
henselizations followed by the unique morphism from `Spec 𝒪^{sh}_{X,x}` into `W`. -/
public theorem strictHenselizationNeighborhoodLift_smallEtaleBaseChange (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W) :
    strictHenselizationNeighborhoodLift B X' hX' x'
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v) ≫
        pullback.fst W.hom g =
      strictHenselizationSquareMap B hX' hX g x' ≫
        strictHenselizationNeighborhoodLift B X hX (x'.map g) W v := by
  have hlift : strictHenselizationNeighborhoodLift B X hX (x'.map g) W v ≫ W.hom =
      strictHenselizationToBase B X hX (x'.map g) :=
    strictHenselizationNeighborhoodLift_comp B X hX (x'.map g) W v
  have hcond : (strictHenselizationSquareMap B hX' hX g x' ≫
        strictHenselizationNeighborhoodLift B X hX (x'.map g) W v) ≫ W.hom =
      strictHenselizationToBase B X' hX' x' ≫ g :=
    (comp_comp_eq_comp_of_comp_eq _ _ _ _ hlift).trans
      (strictHenselizationSquareMap_comp B hX' hX g x')
  have hL1 : pullback.lift (strictHenselizationSquareMap B hX' hX g x' ≫
          strictHenselizationNeighborhoodLift B X hX (x'.map g) W v)
        (strictHenselizationToBase B X' hX' x') hcond ≫
      ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W).hom =
      strictHenselizationToBase B X' hX' x' :=
    pullback.lift_snd _ _ _
  have hL2 : geometricPointToStrictHenselization B X' hX' x' ≫
        pullback.lift (strictHenselizationSquareMap B hX' hX g x' ≫
            strictHenselizationNeighborhoodLift B X hX (x'.map g) W v)
          (strictHenselizationToBase B X' hX' x') hcond =
      ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v).left := by
    refine pullback.hom_ext ?_ ?_
    · exact (comp_comp_eq_comp_of_comp_eq _ _ _ _ (pullback.lift_fst _ _ hcond)).trans
          (((Category.assoc _ _ _).symm.trans
                (congrArg
                  (· ≫ strictHenselizationNeighborhoodLift B X hX (x'.map g) W v)
                  (geometricPointToStrictHenselization_strictHenselizationSquareMap
                    B hX' hX g x'))).trans
            ((geometricPointToStrictHenselization_comp_neighborhoodLift B X hX (x'.map g)
                  W v).trans
              (pointSmallEtaleComapFiberIso_hom_app_left_fst g x'.hom W v).symm))
    · exact (comp_comp_eq_comp_of_comp_eq _ _ _ _ (pullback.lift_snd _ _ hcond)).trans
          ((geometricPointToStrictHenselization_comp B X' hX' x').trans
            (Over.w ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v)).symm)
  have key := strictHenselizationNeighborhoodLift_eq B X' hX' x'
    ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
    ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v)
    (pullback.lift (strictHenselizationSquareMap B hX' hX g x' ≫
        strictHenselizationNeighborhoodLift B X hX (x'.map g) W v)
      (strictHenselizationToBase B X' hX' x') hcond) hL1 hL2
  exact (congrArg (· ≫ pullback.fst W.hom g) key.symm).trans (pullback.lift_fst _ _ hcond)

end Lift

/-! ### The map out of the étale stalk under inverse image -/

section Pullback

variable (B : BigEtaleSite.{u}) {X X' : Scheme.{u}} (hX : B.Contains X) (hX' : B.Contains X')
  (g : X' ⟶ X) (x' : GeometricPoint X') {T T' : Scheme.{u}}
  (q : T ⟶ strictHenselization B X hX (x'.map g))
  (q' : T' ⟶ strictHenselization B X' hX' x') (ι : T' ⟶ T)

/-- The structure morphism of `T'` over `X'`, followed by `g`, is `ι` followed by the structure
morphism of `T` over `X`. -/
public theorem comp_strictHenselizationToBase_of_comp
    (hι : q' ≫ strictHenselizationSquareMap B hX' hX g x' = ι ≫ q) :
    ι ≫ q ≫ strictHenselizationToBase B X hX (x'.map g) =
      (q' ≫ strictHenselizationToBase B X' hX' x') ≫ g := by
  rw [← Category.assoc ι q, ← hι, Category.assoc, Category.assoc,
    strictHenselizationSquareMap_comp]

/-- The germ-level map of Tag 0GJN is restriction of sections along the structure morphism of `T`
over the strict henselization followed by the morphism from that strict henselization into the
étale neighbourhood, for any proof that this composite lies over the structure morphism of `T`
over `X`. -/
private theorem etaleStalkSectionsStage_eq_sectionsPullbackAb
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W)
    (h : (q ≫ strictHenselizationNeighborhoodLift B X hX (x'.map g) W v) ≫ W.hom =
      q ≫ strictHenselizationToBase B X hX (x'.map g)) :
    etaleStalkSectionsStage B X hX (x'.map g) q F W v =
      (smallEtaleSectionsPullbackAb (q ≫ strictHenselizationToBase B X hX (x'.map g)) W
        (q ≫ strictHenselizationNeighborhoodLift B X hX (x'.map g) W v) h).app F :=
  rfl

/-- The structure morphism of `T'` over the strict henselization at `x'`, followed by the morphism
of that strict henselization into the base changed étale neighbourhood, lies over the structure
morphism of `T'` over `X'`. -/
private theorem comp_baseChangeNeighborhoodLift_comp_hom (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W) :
    (q' ≫ strictHenselizationNeighborhoodLift B X' hX' x'
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v)) ≫
        ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W).hom =
      q' ≫ strictHenselizationToBase B X' hX' x' :=
  comp_comp_eq_comp_of_comp_eq _ _ _ _ (strictHenselizationNeighborhoodLift_comp B X' hX' x'
    ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
    ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v))

/-- The structure morphism of `T` over the strict henselization at `x`, followed by the morphism
of that strict henselization into an étale neighbourhood of `x`, lies over the structure morphism
of `T` over `X`. -/
private theorem comp_neighborhoodLift_comp_hom (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W) :
    (q ≫ strictHenselizationNeighborhoodLift B X hX (x'.map g) W v) ≫ W.hom =
      q ≫ strictHenselizationToBase B X hX (x'.map g) :=
  comp_comp_eq_comp_of_comp_eq _ _ _ _
    (strictHenselizationNeighborhoodLift_comp B X hX (x'.map g) W v)

/-- The same composite, precomposed with `ι : T' ⟶ T`, lies over the structure morphism of `T'`
over `X` read through `T`. -/
private theorem comp_comp_neighborhoodLift_comp_hom (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W) :
    (ι ≫ q ≫ strictHenselizationNeighborhoodLift B X hX (x'.map g) W v) ≫ W.hom =
      ι ≫ q ≫ strictHenselizationToBase B X hX (x'.map g) :=
  comp_comp_eq_comp_of_comp_eq _ _ _ _ (comp_neighborhoodLift_comp_hom B hX g x' q W v)

/-- The morphism `T' ⟶ W` obtained from the base changed étale neighbourhood is the one obtained
from `W` itself through `ι`. -/
private theorem comp_baseChangeNeighborhoodLift_comp_fst
    (hι : q' ≫ strictHenselizationSquareMap B hX' hX g x' = ι ≫ q) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W) :
    (q' ≫ strictHenselizationNeighborhoodLift B X' hX' x'
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v)) ≫ pullback.fst W.hom g =
      ι ≫ q ≫ strictHenselizationNeighborhoodLift B X hX (x'.map g) W v :=
  (comp_comp_eq_comp_of_comp_eq _ _ _ _
      (strictHenselizationNeighborhoodLift_smallEtaleBaseChange B hX hX' g x' W v)).trans
    (by rw [← Category.assoc, hι, Category.assoc])

/-- The morphism `T' ⟶ W` obtained from the base changed étale neighbourhood lies over the
structure morphism of `T'` over `X`, read through `X'`. -/
private theorem comp_baseChangeNeighborhoodLift_comp_fst_comp_hom
    (hι : q' ≫ strictHenselizationSquareMap B hX' hX g x' = ι ≫ q) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W) :
    ((q' ≫ strictHenselizationNeighborhoodLift B X' hX' x'
            ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
            ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v)) ≫
          pullback.fst W.hom g) ≫ W.hom =
      (q' ≫ strictHenselizationToBase B X' hX' x') ≫ g :=
  (congrArg (· ≫ W.hom)
      (comp_baseChangeNeighborhoodLift_comp_fst B hX hX' g x' q q' ι hι W v)).trans
    ((comp_comp_neighborhoodLift_comp_hom B hX g x' q ι W v).trans
      (comp_strictHenselizationToBase_of_comp B hX hX' g x' q q' ι hι))

/-- On the germ at `x` of a section of an abelian étale sheaf `F` over an étale neighbourhood `W`
of `x`, the unit of the inverse-image/direct-image adjunction for `g` followed by the germ-level
map of `T'` over `X'` for the inverse image `g⁻¹F` is the germ-level map of `T` over `X` for `F`
followed by restriction of global sections along `ι`. -/
public theorem etaleStalkSectionsStage_pullback
    (hι : q' ≫ strictHenselizationSquareMap B hX' hX g x' = ι ≫ q)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (x'.map g).hom).fiber.obj W) :
    ((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫
        etaleStalkSectionsStage B X' hX' x' q' ((smallEtalePullbackAb g).obj F)
            ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
            ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v) ≫
          (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}).map
            ((smallEtalePullbackAbCompIso
              (q' ≫ strictHenselizationToBase B X' hX' x') g).hom.app F) =
      etaleStalkSectionsStage B X hX (x'.map g) q F W v ≫
        (Functor.whiskerLeft
              (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX (x'.map g)))
              (smallEtaleGlobalSectionsRestrictionAb ι) ≫
            (Functor.associator
                (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX (x'.map g)))
                (smallEtalePullbackAb ι)
                (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
              Functor.whiskerRight
                ((smallEtalePullbackAbCompIso ι
                    (q ≫ strictHenselizationToBase B X hX (x'.map g))).hom ≫
                  (eqToIso (congrArg (fun m : T' ⟶ X => smallEtalePullbackAb m)
                    (comp_strictHenselizationToBase_of_comp B hX hX' g x' q q' ι hι))).hom)
                (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).app F := by
  refine (smallEtaleSectionsPullbackAb_comp_app
    (q' ≫ strictHenselizationToBase B X' hX' x') g W
    (q' ≫ strictHenselizationNeighborhoodLift B X' hX' x'
      ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
      ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v))
    (comp_baseChangeNeighborhoodLift_comp_hom B hX' g x' q' W v)
    (comp_baseChangeNeighborhoodLift_comp_fst_comp_hom B hX hX' g x' q q' ι hι W v) F).trans ?_
  refine (congrArg (fun σ => NatTrans.app σ F)
    (smallEtaleSectionsPullbackAb_comp_base_congr
      (q ≫ strictHenselizationToBase B X hX (x'.map g)) ι W
      (q ≫ strictHenselizationNeighborhoodLift B X hX (x'.map g) W v)
      (comp_neighborhoodLift_comp_hom B hX g x' q W v)
      (comp_comp_neighborhoodLift_comp_hom B hX g x' q ι W v)
      (comp_strictHenselizationToBase_of_comp B hX hX' g x' q q' ι hι)
      (comp_baseChangeNeighborhoodLift_comp_fst B hX hX' g x' q q' ι hι W v).symm
      (comp_baseChangeNeighborhoodLift_comp_fst_comp_hom B hX hX' g x' q q' ι hι W
        v))).trans ?_
  exact congrArg (· ≫ _) (etaleStalkSectionsStage_eq_sectionsPullbackAb B hX g x' q F W v
    (comp_neighborhoodLift_comp_hom B hX g x' q W v)).symm

/-- **The map of Tag 0GJN under inverse image along a morphism of the ambient scheme.** For
`g : X' ⟶ X`, a geometric point `x'` of `X'` with image `x` in `X`, schemes `T` over
`Spec 𝒪^{sh}_{X,x}` and `T'` over `Spec 𝒪^{sh}_{X',x'}` and a morphism `ι : T' ⟶ T` compatible
with the induced morphism of strict henselizations, the map
`AlgebraicGeometry.etaleStalkToSectionsAb` on abelian étale sheaves formed on `X'` for `T'`, read
through the identification of the stalk of an inverse image with the stalk at the image point, is
the map formed on `X` for `T` followed by restriction of global sections along `ι`.

Both sides are read in the global sections on `T'` of the inverse image along the structure
morphism of `T'` over `X`, which the two composition isomorphisms for inverse image provide. -/
public theorem etaleStalkToSectionsAb_pullback
    (hι : q' ≫ strictHenselizationSquareMap B hX' hX g x' = ι ≫ q) :
    (smallEtaleStalkPullbackAbIso g x'.hom).inv ≫
        Functor.whiskerLeft (smallEtalePullbackAb g)
            (etaleStalkToSectionsAb B X' hX' x' q') ≫
          (Functor.associator (smallEtalePullbackAb g)
              (smallEtalePullbackAb (q' ≫ strictHenselizationToBase B X' hX' x'))
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
            Functor.whiskerRight
              (smallEtalePullbackAbCompIso
                (q' ≫ strictHenselizationToBase B X' hX' x') g).hom
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) =
      etaleStalkToSectionsAb B X hX (x'.map g) q ≫
        Functor.whiskerLeft
            (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX (x'.map g)))
            (smallEtaleGlobalSectionsRestrictionAb ι) ≫
          (Functor.associator
              (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX (x'.map g)))
              (smallEtalePullbackAb ι)
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})).inv ≫
            Functor.whiskerRight
              ((smallEtalePullbackAbCompIso ι
                  (q ≫ strictHenselizationToBase B X hX (x'.map g))).hom ≫
                (eqToIso (congrArg (fun m : T' ⟶ X => smallEtalePullbackAb m)
                  (comp_strictHenselizationToBase_of_comp B hX hX' g x' q q' ι hι))).hom)
              (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}) := by
  refine NatTrans.ext (funext fun F => ?_)
  refine (Scheme.pointSmallEtale (x'.map g).hom).presheafFiber_hom_ext fun W v => ?_
  exact (comp_shuffle_source _ _ _ _ _ _ _ _
      (toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv g x'.hom F W v)
      (etaleStalkToSectionsAb_toPresheafFiber B X' hX' x' q'
        ((smallEtalePullbackAb g).obj F)
        ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
        ((pointSmallEtaleComapFiberIso g x'.hom).hom.app W v)) rfl).trans
    ((etaleStalkSectionsStage_pullback B hX hX' g x' q q' ι hι F W v).trans
      (comp_contract_source _ _ _ _
        (etaleStalkToSectionsAb_toPresheafFiber B X hX (x'.map g) q F W v)).symm)

end Pullback


end AlgebraicGeometry

end
