module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkSectionsTransitivity

/-!
# The two identifications displayed in Stacks 0GJ3

Let `S` be a scheme, `s` a geometric point of `S`, `p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the structure
morphism of the strict henselization of `S` at `s`, and `t` a geometric point of
`Spec(𝒪^{sh}_{S,s})`, so that the image of `t ≫ p` is a specialization of the image of `s`. For
an abelian sheaf `F` on the small étale site of `S` the specialization map

`sp : F_s ⟶ F_{t ≫ p}`

is `AlgebraicGeometry.smallEtaleSpecializationStalkAb`. [Stacks, Tag 0GJ3] describes it
differently: using the two identifications

`F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`  and  `F_{t ≫ p} = Γ(t, t⁻¹p⁻¹F)`,

the first being Theorem 03Q9 applied to `id_S : S ⟶ S` and the second Lemma 03Q1, the
specialization map *is* the map induced between them by pullback of sections along `t`.

This file proves that both displayed identifications are isomorphisms and draws that conclusion.

## Main definitions

* `AlgebraicGeometry.smallEtaleGlobalSectionsToStalkAb` — the comparison `Γ(T, G) ⟶ G_σ` from
  global sections of an abelian étale sheaf on `T` to its stalk at a geometric point `σ` of `T`,
  along a chosen lift of `σ` to the identity object of the small étale site.
* `AlgebraicGeometry.geometricStalkPullbackSectionsAbIso` — **the second identification displayed
  in [Stacks, Tag 0GJ3]**, `F_x ≅ Γ(x, x⁻¹F)`, which is Lemma 03Q1.
* `AlgebraicGeometry.etaleStalkSectionsAbIso` — **the first identification displayed in [Stacks,
  Tag 0GJ3]**, `F_s ≅ Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, which is Theorem 03Q9 applied to
  `id_S : S ⟶ S` in degree zero.

## Main results

* `AlgebraicGeometry.isIso_toPresheafFiber_of_isInitial` — the germ at an initial étale
  neighbourhood is an isomorphism onto the stalk.
* `AlgebraicGeometry.isIso_smallEtaleGlobalSectionsToStalkAb` — global sections are the stalk at a
  geometric point admitting an initial lift to the identity object.
* `AlgebraicGeometry.isIso_stalkToSectionsAb_of_isInitial` — the comparison from the stalk of `F`
  at `x` to the global sections of `g⁻¹F` on a scheme `g : T ⟶ X` is an isomorphism when the
  identity object of the small étale site of `T` is an initial étale neighbourhood of a geometric
  point of `T` over `x`.
* `AlgebraicGeometry.isIso_geometricStalkToPullbackSectionsAb` — **Lemma 03Q1**: the comparison
  `F_x ⟶ Γ(x, x⁻¹F)` is an isomorphism.
* `AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id` — **Theorem 03Q9 applied to `id_S`, in
  degree zero**: the comparison `F_s ⟶ Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is an isomorphism.
* `AlgebraicGeometry.smallEtaleSpecializationStalkAb_eq_sectionsRestrictionAb` — **[Stacks, Tag
  0GJ3]**: under the two identifications, both isomorphisms, the specialization map `sp` is the
  map induced by pullback of sections along `t`.

## References

* [Stacks Project, Tag 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
* [Stacks Project, Tag 0GJ3](https://stacks.math.columbia.edu/tag/0GJ3)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-! ### Stalks and sections over an initial étale neighbourhood -/

section InitialNeighborhood

variable {X T : Scheme.{u}} (g : T ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (σ : Spec (.of Ω) ⟶ T)

/-- **The germ at an initial étale neighbourhood is an isomorphism onto the stalk.** If an étale
neighbourhood `(W₀, v₀)` of a geometric point `σ` of `T` is initial among the étale
neighbourhoods of `σ`, then the filtered colimit computing the stalk at `σ` is attained at
`(W₀, v₀)`, so the germ map there is invertible. -/
theorem isIso_toPresheafFiber_of_isInitial (W₀ : T.Etale)
    (v₀ : (Scheme.pointSmallEtale σ).fiber.obj W₀)
    (hinit : IsInitial (show (Scheme.pointSmallEtale σ).fiber.Elements from ⟨W₀, v₀⟩))
    (P : T.Etaleᵒᵖ ⥤ Ab.{u + 1}) :
    IsIso ((Scheme.pointSmallEtale σ).toPresheafFiber W₀ v₀ P) :=
  ((Scheme.pointSmallEtale σ).isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
    (op ⟨W₀, v₀⟩) hinit.op

/-- The comparison `Γ(T, G) ⟶ G_σ` from the global sections of an abelian sheaf on the small
étale site of `T` to its stalk at a geometric point `σ` of `T`: read a global section as a
section over the identity object of the small étale site, which is terminal, and take its germ at
`σ` along a chosen lift `eσ` of `σ` to that object. -/
def smallEtaleGlobalSectionsToStalkAb
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T))) :
    Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1} ⟶ smallEtaleStalkAb σ :=
  (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} (isTerminalEtaleMkId T)).hom ≫
    Functor.whiskerLeft (sheafToPresheaf (smallEtaleTopology T) Ab.{u + 1})
      ((Scheme.pointSmallEtale σ).toPresheafFiberNatTrans (Scheme.Etale.mk (𝟙 T)) eσ)

/-- On each sheaf, the comparison from global sections to the stalk at `σ` is the identification
of global sections with sections over the identity object, followed by the germ map there. -/
theorem smallEtaleGlobalSectionsToStalkAb_app
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T)))
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtaleGlobalSectionsToStalkAb σ eσ).app G =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
          (isTerminalEtaleMkId T)).hom.app G ≫
        (Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ G.obj :=
  rfl

/-- **Global sections are the stalk at a geometric point admitting an initial lift to the
identity object.** If the identity object of the small étale site of `T`, with a chosen lift `eσ`
of a geometric point `σ`, is an initial étale neighbourhood of `σ`, then the comparison
`Γ(T, G) ⟶ G_σ` is an isomorphism, naturally in the abelian sheaf `G`. -/
theorem isIso_smallEtaleGlobalSectionsToStalkAb
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T)))
    (hinit : IsInitial (show (Scheme.pointSmallEtale σ).fiber.Elements from
      ⟨Scheme.Etale.mk (𝟙 T), eσ⟩)) :
    IsIso (smallEtaleGlobalSectionsToStalkAb σ eσ) := by
  have happ : ∀ G : Sheaf (smallEtaleTopology T) Ab.{u + 1},
      IsIso ((smallEtaleGlobalSectionsToStalkAb σ eσ).app G) := by
    intro G
    have := isIso_toPresheafFiber_of_isInitial σ (Scheme.Etale.mk (𝟙 T)) eσ hinit G.obj
    show IsIso ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
        (isTerminalEtaleMkId T)).hom.app G ≫
      (Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ G.obj)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Two lifts of a geometric point `σ` of `T` to the base change along `g : T ⟶ X` of an étale
object `W` of `X` agree as soon as their projections to `W` agree: the other projection is the
structure morphism of the base change, which every lift respects. -/
theorem pointSmallEtaleBaseChangeFiber_ext (W : X.Etale)
    {a b : (Scheme.pointSmallEtale σ).fiber.obj
      ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)}
    (h : a.left ≫ pullback.fst W.hom g = b.left ≫ pullback.fst W.hom g) : a = b := by
  apply CategoryTheory.Over.OverMorphism.ext
  refine pullback.hom_ext h ?_
  exact (CategoryTheory.Over.w a).trans (CategoryTheory.Over.w b).symm

/-- Restriction of a section over an étale neighbourhood `W` of `σ ≫ g` to a global section of
the inverse image on `T`, followed by the germ at `σ` of that global section, is the unit of the
inverse-image/direct-image adjunction followed by the germ at the lift of `σ` to the base change
`W ×_X T` determined by the chosen lift of `σ ≫ g`. -/
theorem smallEtaleSectionsPullbackAb_comp_toPresheafFiber
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T))) (heσ : eσ.left = σ)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (σ ≫ g)).fiber.obj W)
    (r : T ⟶ W.left) (hr : r ≫ W.hom = g) (hσr : σ ≫ r = v.left) :
    (smallEtaleSectionsPullbackAb g W r hr).app F ≫
        ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
            (isTerminalEtaleMkId T)).hom.app ((smallEtalePullbackAb g).obj F) ≫
          (Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ
            ((smallEtalePullbackAb g).obj F).obj) =
      ((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫
        (Scheme.pointSmallEtale σ).toPresheafFiber
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
          ((Stacks.EtaleCohomology.pointSmallEtaleComapFiberIso g σ).hom.app W v)
          ((smallEtalePullbackAb g).obj F).obj := by
  rw [smallEtaleSectionsPullbackAb, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  have hw : ((smallEtalePullbackAb g).obj F).obj.map
        (Stacks.EtaleCohomology.smallEtaleBaseChangeLift g W r hr).op ≫
      (Scheme.pointSmallEtale σ).toPresheafFiber (Scheme.Etale.mk (𝟙 T)) eσ
        ((smallEtalePullbackAb g).obj F).obj =
      (Scheme.pointSmallEtale σ).toPresheafFiber
        ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj W)
        ((Stacks.EtaleCohomology.pointSmallEtaleComapFiberIso g σ).hom.app W v)
        ((smallEtalePullbackAb g).obj F).obj := by
    refine Eq.trans (GrothendieckTopology.Point.toPresheafFiber_w (Scheme.pointSmallEtale σ)
      (Stacks.EtaleCohomology.smallEtaleBaseChangeLift g W r hr) eσ
      ((smallEtalePullbackAb g).obj F).obj) ?_
    congr 1
    refine pointSmallEtaleBaseChangeFiber_ext g σ W ?_
    have hleft : ((Scheme.pointSmallEtale σ).fiber.map
        (Stacks.EtaleCohomology.smallEtaleBaseChangeLift g W r hr) eσ).left =
        eσ.left ≫ (Stacks.EtaleCohomology.smallEtaleBaseChangeLift g W r hr).left := rfl
    rw [hleft, heσ, Stacks.EtaleCohomology.pointSmallEtaleComapFiberIso_hom_app_left_fst,
      Stacks.EtaleCohomology.smallEtaleBaseChangeLift_left]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => σ ≫ z) (pullback.lift_fst r (𝟙 T)
        (hr.trans (Category.id_comp g).symm))).trans hσr)
  refine Eq.trans (congrArg (fun z => z ≫ (Scheme.pointSmallEtale σ).toPresheafFiber
      (Scheme.Etale.mk (𝟙 T)) eσ ((smallEtalePullbackAb g).obj F).obj)
    (Stacks.Sites.sectionsPullbackComparison_app
      (Stacks.EtaleCohomology.smallEtaleBaseChange g) Ab.{u + 1}
      (smallEtaleTopology X) (smallEtaleTopology T) (smallEtaleAdjunctionAb g)
      (Stacks.EtaleCohomology.smallEtaleBaseChangeLift g W r hr) F)) ?_
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => ((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫ z) hw)

/-- **Stacks 03Q9 at the identity morphism, in the shape of a pro-étale neighbourhood.** Let
`g : T ⟶ X` be a morphism of schemes and `σ` a geometric point of `T` whose image in `X` is `x`,
and suppose that `T` is an *initial* étale neighbourhood of `σ` in its own small étale site: the
identity object, with the lift `eσ` of `σ`, is initial among the étale neighbourhoods of `σ`.
Suppose moreover that each étale neighbourhood `(W, v)` of `x` receives a morphism `ρ W v` from
`T` over `X` carrying `σ` to `v`. Then the canonical map

`A : F_x ⟶ Γ(T, g⁻¹F)`

which restricts the germ at `x` of a section over `(W, v)` along `ρ W v` is an isomorphism. -/
theorem isIso_stalkToSectionsAb_of_isInitial
    (eσ : (Scheme.pointSmallEtale σ).fiber.obj (Scheme.Etale.mk (𝟙 T))) (heσ : eσ.left = σ)
    (hinit : IsInitial (show (Scheme.pointSmallEtale σ).fiber.Elements from
      ⟨Scheme.Etale.mk (𝟙 T), eσ⟩))
    {x : Spec (.of Ω) ⟶ X} (hx : σ ≫ g = x)
    (A : smallEtaleStalkAb x ⟶
      smallEtalePullbackAb g ⋙ Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
    (ρ : ∀ W : X.Etale, (Scheme.pointSmallEtale x).fiber.obj W → (T ⟶ W.left))
    (hρ : ∀ (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W), ρ W v ≫ W.hom = g)
    (hσρ : ∀ (W : X.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj W),
      σ ≫ ρ W v = CategoryTheory.Over.Hom.left v)
    (hA : ∀ (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
      (v : (Scheme.pointSmallEtale x).fiber.obj W),
      (Scheme.pointSmallEtale x).toPresheafFiber W v F.obj ≫ A.app F =
        (smallEtaleSectionsPullbackAb g W (ρ W v) (hρ W v)).app F) :
    IsIso A := by
  subst hx
  have key : A ≫ Functor.whiskerLeft (smallEtalePullbackAb g)
      (smallEtaleGlobalSectionsToStalkAb σ eσ) =
      (Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso g σ).inv := by
    ext F : 2
    refine smallEtaleStalkAb_hom_ext (σ ≫ g) F fun W v => ?_
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (smallEtaleGlobalSectionsToStalkAb σ eσ).app
            ((smallEtalePullbackAb g).obj F)) (hA F W v)).trans
        ((smallEtaleSectionsPullbackAb_comp_toPresheafFiber g σ eσ heσ F W v (ρ W v)
              (hρ W v) (hσρ W v)).trans
          (Stacks.EtaleCohomology.toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv
            g σ F W v).symm))
  have := isIso_smallEtaleGlobalSectionsToStalkAb σ eσ hinit
  have : IsIso (Functor.whiskerLeft (smallEtalePullbackAb g)
      (smallEtaleGlobalSectionsToStalkAb σ eσ)) :=
    NatIso.isIso_of_isIso_app _
  have : IsIso (A ≫ Functor.whiskerLeft (smallEtalePullbackAb g)
      (smallEtaleGlobalSectionsToStalkAb σ eσ)) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_right A (Functor.whiskerLeft (smallEtalePullbackAb g)
    (smallEtaleGlobalSectionsToStalkAb σ eσ))

end InitialNeighborhood

/-! ### The second identification of Stacks 0GJ3 -/

section PullbackSectionsIso

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- **Stacks 03Q1: the stalk at a geometric point is the sections of the inverse image there.**
The canonical map `F_x ⟶ Γ(x, x⁻¹F)` of `AlgebraicGeometry.geometricStalkToPullbackSectionsAb`
is an isomorphism. -/
theorem isIso_geometricStalkToPullbackSectionsAb :
    IsIso (geometricStalkToPullbackSectionsAb x) :=
  isIso_stalkToSectionsAb_of_isInitial x (𝟙 (Spec (.of Ω)))
    (Stacks.EtaleCohomology.pointSmallEtaleIdElement Ω) rfl
    (Stacks.EtaleCohomology.isInitialPointSmallEtaleIdElement Ω) (Category.id_comp x)
    (geometricStalkToPullbackSectionsAb x) (fun _ v => v.left)
    (fun _ v => CategoryTheory.Over.w v) (fun _ v => Category.id_comp v.left)
    (fun F W v => geometricStalkToPullbackSectionsAb_toPresheafFiber x F W v)

/-- **The second identification displayed in Stacks 0GJ3**, `F_x = Γ(x, x⁻¹F)`: the stalk of an
abelian étale sheaf at a geometric point `x` of `X` is the group of global sections of its inverse
image on the spectrum of the residue field of `x`, naturally in the sheaf. The isomorphism is the
canonical map `AlgebraicGeometry.geometricStalkToPullbackSectionsAb`, which Stacks 03Q1 asserts
to be invertible. -/
def geometricStalkPullbackSectionsAbIso :
    smallEtaleStalkAb x ≅
      smallEtalePullbackAb x ⋙ Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1} :=
  letI := isIso_geometricStalkToPullbackSectionsAb x
  asIso (geometricStalkToPullbackSectionsAb x)

/-- The identification `F_x = Γ(x, x⁻¹F)` is the canonical map, on the nose. -/
theorem geometricStalkPullbackSectionsAbIso_hom :
    (geometricStalkPullbackSectionsAbIso x).hom = geometricStalkToPullbackSectionsAb x :=
  rfl

end PullbackSectionsIso

/-! ### The first identification, and the remark -/

section SpecializationIso

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- **Stacks 03Q9 at the identity morphism of `S`.** The canonical map
`F_s ⟶ Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` of `AlgebraicGeometry.etaleStalkToSectionsAb`, taken at the
identity morphism of the strict henselization, is an isomorphism. -/
@[sga "4 VIII 4.8" "special case"]
theorem isIso_etaleStalkToSectionsAb_id :
    IsIso (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s))) :=
  isIso_stalkToSectionsAb_of_isInitial
    (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s)
    (geometricPointToStrictHenselization B S hS s)
    (Stacks.EtaleCohomology.pointSmallEtaleClosedPointElement
      (geometricPointToStrictHenselization B S hS s)) rfl
    (Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement
      (geometricPointToStrictHenselization B S hS s)
      (geometricPointToStrictHenselization_base_default B S hS s))
    (by rw [Category.id_comp]; exact geometricPointToStrictHenselization_comp B S hS s)
    (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)))
    (fun W v => 𝟙 (strictHenselization B S hS s) ≫
      strictHenselizationNeighborhoodLift B S hS s W v)
    (fun W v => by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
    (fun W v => by
      rw [Category.id_comp]
      exact geometricPointToStrictHenselization_comp_neighborhoodLift B S hS s W v)
    (fun F W v => etaleStalkToSectionsAb_toPresheafFiber B S hS s
      (𝟙 (strictHenselization B S hS s)) F W v)

/-- **The first identification displayed in Stacks 0GJ3**, `F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`:
the stalk of an abelian étale sheaf at a geometric point `s` of `S` is the group of global
sections of its inverse image on the strict henselization at `s`, naturally in the sheaf. The
isomorphism is the canonical map `AlgebraicGeometry.etaleStalkToSectionsAb` at the identity
morphism of the strict henselization, which is Stacks 03Q9 applied to `id_S : S ⟶ S` in degree
zero. -/
def etaleStalkSectionsAbIso :
    smallEtaleStalkAb s.hom ≅
      smallEtalePullbackAb
          (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) Ab.{u + 1} :=
  letI := isIso_etaleStalkToSectionsAb_id B S hS s
  asIso (etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)))

/-- The identification `F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is the canonical map, on the nose. -/
theorem etaleStalkSectionsAbIso_hom :
    (etaleStalkSectionsAbIso B S hS s).hom =
      etaleStalkToSectionsAb B S hS s (𝟙 (strictHenselization B S hS s)) :=
  rfl

/-- Let `S` be a scheme, `s` a geometric point of `S`, `p : Spec(𝒪^{sh}_{S,s}) ⟶ S` the
structure morphism of the strict henselization at `s`, and `t` a geometric point of
`Spec(𝒪^{sh}_{S,s})`, so that the image of `t ≫ p` is a specialization of the image of `s`. Use
the two identifications

`F_s = Γ(Spec(𝒪^{sh}_{S,s}), p⁻¹F)`  and  `F_{t ≫ p} = Γ(t, t⁻¹p⁻¹F)`,

the first of which is Theorem 03Q9 applied to `id_S : S ⟶ S` and the second Lemma 03Q1. Then the
specialization map `sp : F_s ⟶ F_{t ≫ p}` of Stacks 0GJ2 *is* the map induced between them by
pullback of sections along `t`, that is, it is the composite of the first identification, the
restriction of sections along `t`, and the inverse of the second.

Here the first identification is `AlgebraicGeometry.etaleStalkSectionsAbIso`, the second is
`AlgebraicGeometry.geometricStalkPullbackSectionsAbIso`, and restriction of sections along `t` is
`Stacks.EtaleCohomology.smallEtaleSectionsRestrictionAb`. -/
@[stacks 0GJ3 "the specialization map is pullback of sections along `t`, read through the two \
identifications F_s = Γ(Spec 𝒪^sh_{S,s}, p⁻¹F) (03Q9 at the identity) and \
F_{t ≫ p} = Γ(t, t⁻¹p⁻¹F) (03Q1), both isomorphisms"]
theorem smallEtaleSpecializationStalkAb_eq_sectionsRestrictionAb :
    smallEtaleSpecializationStalkAb B S hS s t =
      (etaleStalkSectionsAbIso B S hS s).hom ≫
        smallEtaleSectionsRestrictionAb
            (𝟙 (strictHenselization B S hS s) ≫ strictHenselizationToBase B S hS s) t.hom
            (t.hom ≫ strictHenselizationToBase B S hS s)
            ((Category.assoc t.hom (𝟙 (strictHenselization B S hS s))
                (strictHenselizationToBase B S hS s)).symm.trans
              (congrArg (fun y : t.source ⟶ strictHenselization B S hS s =>
                y ≫ strictHenselizationToBase B S hS s) (Category.comp_id t.hom))) ≫
          (geometricStalkPullbackSectionsAbIso
            (t.hom ≫ strictHenselizationToBase B S hS s)).inv :=
  ((Iso.eq_comp_inv _).mpr
      (etaleStalkToSectionsAb_id_comp_sectionsRestrictionAb B S hS s t).symm).trans
    (Category.assoc _ _ _)

end SpecializationIso

end AlgebraicGeometry

end
