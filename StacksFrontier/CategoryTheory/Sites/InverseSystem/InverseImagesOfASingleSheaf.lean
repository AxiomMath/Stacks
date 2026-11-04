module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.SystemTransitionCalculus

/-!
# The system of inverse images of a single abelian sheaf, on an inverse system of sites

Let `D` be an inverse system of sites with finite coverings (Stacks 0A34) and let `S` be a
category — in practice the abelian sheaves on a further site. Suppose every level of `D` carries
a morphism of topoi to `S` compatibly with the transitions of the system: a direct image
`R_i : Sheaf (D.J i) Ab ⥤ S` with a left adjoint `L_i`, together with a comparison
`f_{a,*} ⋙ R_j ≅ R_i` saying that the leg at `i` is the transition `a : i ⟶ j` followed by the
leg at `j`, subject to the unit and cocycle laws of such a comparison. That is the sheaf-level
form of a *cocone* on the inverse system, with the site of `S` as vertex.

For one object `ℱ` of `S` the inverse images `L_i ℱ` then form a system of abelian sheaves on `D`
in the sense of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem`, and the
transition maps of that system are *isomorphisms*: the system is not an arbitrary datum but the
system of inverse images of a single sheaf.

This is the shape in which Stacks 03Q6 takes its sheaves — there the levels are small models of
the affine étale sites of the base changes `Y_i` of a scheme `X`, the vertex is `X` itself, and
the legs are inverse image along `Y_i ⟶ X`. The geometric production of the data below for that
situation is *not* carried out here: see the implementation notes.

## Main definitions

* `CategoryTheory.PushforwardCocone.transitionPushforward` — the transition map of the system,
  written in the direct-image direction, for an arbitrary family of direct images; with
  `transitionPushforward_id` and `transitionPushforward_comp` its two laws.
* `InverseSystemOfFiniteSites.inverseImageTransitionPushforward` — the same at the direct images
  along the transitions of an inverse system of sites.
* `InverseSystemOfFiniteSites.inverseImageSystem` — **the system of inverse images of a single
  sheaf along a cocone of direct images, constructed**, both cocycle conditions discharged.

## Main results

* `InverseSystemOfFiniteSites.inverseImageSystem_map` identifies the transition map of the system
  with Mathlib's comparison `CategoryTheory.Adjunction.leftAdjointCompIso` of the two left
  adjoints of `R_i`, and `InverseSystemOfFiniteSites.isIso_inverseImageSystem_map` concludes that
  it is an isomorphism.

## Implementation notes

The cocone is presented by its *direct* images, and its two coherence laws are stated for them,
because that is where they are checkable: a direct image is in practice restriction along a
functor of sites, for which the comparison along a composite is concrete, while an inverse image
is only determined as a left adjoint. The two cocycle conditions of
`InverseSystemOfFiniteSites.AbelianSheafSystem` are about the inverse images; they are obtained
here by transposition, through
`Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps`.

The left adjoints and the adjunctions are arguments rather than functors of the cocone, for the
reason given in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BoundedSiteBaseChangeComparison.lean`: a left
adjoint of a direct image is determined only up to isomorphism, and each consumer carries its own
representative.

Nothing is assumed of the index category of `D` beyond what an inverse system of sites provides,
and the cocone is not assumed to present its vertex as a limit of the levels.

The comparison isomorphisms and their two coherence laws are *data of the cocone*, exactly as the
legs are; in the geometric situation they are the pseudofunctoriality of inverse image and are
produced, not assumed. That production — identifying the transition functors of the site system of
Stacks 0EYL, at the level of sheaves, with base change along `Y_i ⟶ Y_j` — is the remaining input
of Stacks 03Q6's system of sheaves. Its *site-functor* half is now available: the comparison is
`Stacks.EtaleCohomology.TransitionBaseChange.transitionIso` and its two coherence laws are
`transitionIso_id_hom_app` and `transitionIso_comp_hom_app` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/TransitionBaseChangeCoherence.lean`, and
the passage from there to abelian sheaves on the levels is carried out in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/StageProjectionBaseChangeCoherence.lean`,
where the tag is claimed; so none is claimed here.

The generic form of the construction — an arbitrary family of direct images `P a` with unit and
associativity comparisons in place of the direct images along the transitions of a system of
sites — is `CategoryTheory.PushforwardCocone.transitionPushforward` and its two laws, on which
the three declarations in this namespace are thin wrappers. Nothing about sites or sheaves enters
them, only the adjunctions and the comparisons.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0A34](https://stacks.math.columbia.edu/tag/0A34)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe jv ju tv tu y z v u w t

namespace CategoryTheory.PushforwardCocone

variable {J : Type ju} [Category.{jv} J] {T : J → Type tu} [∀ i, Category.{tv} (T i)]
  {S : Type y} [Category.{z} S]

/-- **The transition map of the system of inverse images of `ℱ`, in the direct-image
direction**, for an arbitrary family of direct images: the map `L_j ℱ ⟶ P_a (L_i ℱ)` transposing
the unit of the leg at `i` read through the comparison `e a`.

This is the content of `InverseSystemOfFiniteSites.inverseImageTransitionPushforward` with the
direct images along the transitions of an inverse system of sites replaced by an arbitrary family
`P` indexed by the arrows of the index category: nothing about sites or sheaves enters, only the
adjunctions and the comparisons. -/
def transitionPushforward {P : ∀ {i j : J}, (i ⟶ j) → (T i ⥤ T j)} {L : ∀ i, S ⥤ T i}
    {R : ∀ i, T i ⥤ S} (adj : ∀ i, L i ⊣ R i)
    (e : ∀ {i j : J} (a : i ⟶ j), P a ⋙ R j ≅ R i) (F : S) {i j : J} (a : i ⟶ j) :
    (L j).obj F ⟶ (P a).obj ((L i).obj F) :=
  ((adj j).homEquiv F _).symm ((adj i).unit.app F ≫ (e a).inv.app ((L i).obj F))

/-- The transpose of the transition map is the unit of the leg at `i` followed by the
comparison. -/
theorem homEquiv_transitionPushforward {P : ∀ {i j : J}, (i ⟶ j) → (T i ⥤ T j)}
    {L : ∀ i, S ⥤ T i} {R : ∀ i, T i ⥤ S} (adj : ∀ i, L i ⊣ R i)
    (e : ∀ {i j : J} (a : i ⟶ j), P a ⋙ R j ≅ R i) (F : S) {i j : J} (a : i ⟶ j) :
    (adj j).homEquiv F _ (transitionPushforward adj e F a) =
      (adj i).unit.app F ≫ (e a).inv.app ((L i).obj F) :=
  Equiv.apply_symm_apply _ _

/-- **The transition map at an identity transition is the canonical identification**, for an
arbitrary family of direct images. -/
theorem transitionPushforward_id {P : ∀ {i j : J}, (i ⟶ j) → (T i ⥤ T j)} {L : ∀ i, S ⥤ T i}
    {R : ∀ i, T i ⥤ S} (adj : ∀ i, L i ⊣ R i) (PId : ∀ i, 𝟭 (T i) ≅ P (𝟙 i))
    (e : ∀ {i j : J} (a : i ⟶ j), P a ⋙ R j ≅ R i)
    (hid : ∀ (i : J) (Z : T i), (e (𝟙 i)).inv.app Z = (R i).map ((PId i).hom.app Z))
    (F : S) (i : J) :
    transitionPushforward adj e F (𝟙 i) = (PId i).hom.app ((L i).obj F) := by
  refine ((adj i).homEquiv F _).injective ?_
  rw [homEquiv_transitionPushforward, Adjunction.homEquiv_unit, hid]

/-- **The transition maps compose, in the direct-image direction**, for an arbitrary family of
direct images. -/
theorem transitionPushforward_comp {P : ∀ {i j : J}, (i ⟶ j) → (T i ⥤ T j)} {L : ∀ i, S ⥤ T i}
    {R : ∀ i, T i ⥤ S} (adj : ∀ i, L i ⊣ R i)
    (PComp : ∀ {i j k : J} (a : i ⟶ j) (b : j ⟶ k), P a ⋙ P b ≅ P (a ≫ b))
    (e : ∀ {i j : J} (a : i ⟶ j), P a ⋙ R j ≅ R i)
    (hcomp : ∀ {i j k : J} (a : i ⟶ j) (b : j ⟶ k) (Z : T i),
      (e (a ≫ b)).inv.app Z =
        (e a).inv.app Z ≫ (e b).inv.app ((P a).obj Z) ≫ (R k).map ((PComp a b).hom.app Z))
    (F : S) {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    transitionPushforward adj e F (a ≫ b) =
      transitionPushforward adj e F b ≫
        (P b).map (transitionPushforward adj e F a) ≫ (PComp a b).hom.app ((L i).obj F) := by
  have hnat := (e b).inv.naturality (transitionPushforward adj e F a)
  have hunit := homEquiv_transitionPushforward adj e F a
  rw [Adjunction.homEquiv_unit] at hunit
  refine ((adj k).homEquiv F _).injective ?_
  rw [homEquiv_transitionPushforward, Adjunction.homEquiv_naturality_right,
    homEquiv_transitionPushforward, hcomp a b, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat, reassoc_of% hunit]

end CategoryTheory.PushforwardCocone

namespace InverseSystemOfFiniteSites

variable {D : InverseSystemOfFiniteSites.{v, u, w}} {S : Type y} [Category.{z} S]
  {L : ∀ i : D.I, S ⥤ Sheaf (D.J i) (Ab.{max u v w t})}
  {R : ∀ i : D.I, Sheaf (D.J i) (Ab.{max u v w t}) ⥤ S}
  (adj : ∀ i : D.I, L i ⊣ R i)
  (e : ∀ {i j : D.I} (a : i ⟶ j),
    abelianSheafPushforward.{v, u, w, t} D a ⋙ R j ≅ R i)

/-- **The transition map of the system of inverse images of `ℱ`, in the direct-image
direction**: the map `L_j ℱ ⟶ f_{a,*} L_i ℱ` transposing the unit of the leg at `i` read through
the comparison `e a`. -/
def inverseImageTransitionPushforward (F : S) {i j : D.I} (a : i ⟶ j) :
    (L j).obj F ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj ((L i).obj F) :=
  CategoryTheory.PushforwardCocone.transitionPushforward adj e F a

/-- The transpose of the transition map is the unit of the leg at `i` followed by the
comparison. -/
theorem homEquiv_inverseImageTransitionPushforward (F : S) {i j : D.I} (a : i ⟶ j) :
    (adj j).homEquiv F _ (inverseImageTransitionPushforward adj e F a) =
      (adj i).unit.app F ≫ (e a).inv.app ((L i).obj F) :=
  CategoryTheory.PushforwardCocone.homEquiv_transitionPushforward adj e F a

variable
  (hid : ∀ (i : D.I) (Z : Sheaf (D.J i) (Ab.{max u v w t})),
    (e (𝟙 i)).inv.app Z =
      (R i).map ((abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app Z))
  (hcomp : ∀ {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k)
      (Z : Sheaf (D.J i) (Ab.{max u v w t})),
    (e (a ≫ b)).inv.app Z =
      (e a).inv.app Z ≫ (e b).inv.app ((abelianSheafPushforward.{v, u, w, t} D a).obj Z) ≫
        (R k).map ((abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app Z))

include hid in
/-- The transition map at an identity transition is the canonical identification. -/
theorem inverseImageTransitionPushforward_id (F : S) (i : D.I) :
    inverseImageTransitionPushforward adj e F (𝟙 i) =
      (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app ((L i).obj F) :=
  CategoryTheory.PushforwardCocone.transitionPushforward_id adj
    (fun i => abelianSheafPushforwardIdIso.{v, u, w, t} D i) e hid F i

include hcomp in
/-- The transition maps of the system of inverse images compose, in the direct-image
direction. -/
theorem inverseImageTransitionPushforward_comp (F : S) {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) :
    inverseImageTransitionPushforward adj e F (a ≫ b) =
      inverseImageTransitionPushforward adj e F b ≫
        (abelianSheafPushforward.{v, u, w, t} D b).map
            (inverseImageTransitionPushforward adj e F a) ≫
          (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app ((L i).obj F) :=
  CategoryTheory.PushforwardCocone.transitionPushforward_comp adj
    (fun a b => abelianSheafPushforwardCompIso.{v, u, w, t} D a b) e hcomp F a b

include hid hcomp in
/-- **The system of inverse images of a single sheaf along a cocone of direct images,
constructed.** For a cocone of direct images on an inverse system of sites and one object `ℱ` of
the vertex, the inverse images `L_i ℱ`, with the comparisons of `f_a^{-1} L_j ℱ` with `L_i ℱ` as
transition maps, form a system of abelian sheaves on the system of sites. Both cocycle conditions
are discharged: they are the transposes of the two coherence laws of the cocone. -/
def inverseImageSystem (F : S) : AbelianSheafSystem.{v, u, w, t} D :=
  Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps.{v, u, w, t} D
    (fun i => (L i).obj F)
    (fun a => inverseImageTransitionPushforward adj e F a)
    (fun i => inverseImageTransitionPushforward_id adj e hid F i)
    (fun a b => inverseImageTransitionPushforward_comp adj e hcomp F a b)

/-- The sheaf of the system at the level `i` is the inverse image of `ℱ` along the leg at `i`. -/
theorem inverseImageSystem_obj (F : S) (i : D.I) :
    (inverseImageSystem adj e hid hcomp F).obj i = (L i).obj F :=
  rfl

/-- **The transition map of the system of inverse images is the canonical comparison of the two
left adjoints of `R_i`.** Both `L_j ⋙ f_a^{-1}` and `L_i` are left adjoint to `R_i`, the first
through the comparison `e a`, and the transition map of the system is the resulting comparison
evaluated at `ℱ`. -/
theorem inverseImageSystem_map (F : S) {i j : D.I} (a : i ⟶ j) :
    (inverseImageSystem adj e hid hcomp F).map a =
      (Adjunction.leftAdjointCompIso (adj j) (abelianSheafAdjunction.{v, u, w, t} D a)
        (adj i) (e a)).hom.app F := by
  have hL : ((adj j).comp (abelianSheafAdjunction.{v, u, w, t} D a)).homEquiv F _
      ((inverseImageSystem adj e hid hcomp F).map a) =
      (adj i).unit.app F ≫ (e a).inv.app ((L i).obj F) := by
    rw [Adjunction.comp_homEquiv]
    refine Eq.trans (congrArg ((adj j).homEquiv F _) ?_)
      (homEquiv_inverseImageTransitionPushforward adj e F a)
    exact Equiv.apply_symm_apply _ _
  have hR : ((adj j).comp (abelianSheafAdjunction.{v, u, w, t} D a)).homEquiv F _
      ((Adjunction.leftAdjointCompIso (adj j) (abelianSheafAdjunction.{v, u, w, t} D a)
        (adj i) (e a)).hom.app F) =
      (adj i).unit.app F ≫ (e a).inv.app ((L i).obj F) := by
    rw [Adjunction.homEquiv_unit]
    exact (unit_conjugateEquiv_symm (adj i)
      ((adj j).comp (abelianSheafAdjunction.{v, u, w, t} D a)) (e a).inv F).symm
  exact (((adj j).comp (abelianSheafAdjunction.{v, u, w, t} D a)).homEquiv F _).injective
    (hL.trans hR.symm)

/-- **The transition maps of the system of inverse images are isomorphisms**: that is what
distinguishes a system of inverse images of one sheaf from an arbitrary system of sheaves. -/
theorem isIso_inverseImageSystem_map (F : S) {i j : D.I} (a : i ⟶ j) :
    IsIso ((inverseImageSystem adj e hid hcomp F).map a) := by
  rw [inverseImageSystem_map]
  exact NatIso.isIso_app_of_isIso _ F

end InverseSystemOfFiniteSites

end
