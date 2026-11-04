module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem

/-!
# The diagram of a system of abelian étale sheaves on the limit site

Let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes with a cone `c`, write `X = c.pt` and
`f_i : X ⟶ X_i` for the projections, and let `F` be a system of abelian sheaves on the small
étale sites of the levels in the sense of [Stacks, Tag 0EZL]
(`Stacks.EtaleCohomology.EtaleSheafSystem`). Put

`L_i = f_i^{-1}F_i`,  a sheaf on the small étale site of `X`.

For a transition `a : i ⟶ j` of the index the comparison
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneInverseImageComp` and the inverse image of
the transition of the system give a map `L_j ⟶ L_i`. This file names that map and proves the two
facts about it that the colimit `colim_i L_i` depends on:

* it is **multiplicative**: the map of a composite transition is the composite of the maps; and
* it is **natural** in a morphism of systems.

Both were already available one level up, on cohomology
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.etaleCohomologyTransition_comp`); what is new
here is the statement on the sheaves themselves, which is what a *diagram* in the sheaf category
is made of.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramMap` — the map `L_j ⟶ L_i`
  attached to a transition `a : i ⟶ j`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem` — the endomorphism
  `e_i : L_i ⟶ L_i` attached to the identity transition of a level. It is an idempotent, and it
  is **not** the identity: `EtaleSheafSystem` follows [Stacks, Tag 0EZL] in imposing only the
  cocycle condition and not the identity law, and base change along `𝟙 X_i` is the functor
  `U ↦ U ×_{X_i} X_i` and not the identity functor.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramMap_comp` — **the
  multiplicativity**: `d_{a ≫ b} = d_b ≫ d_a`. The proof is the associativity pentagon
  `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'_assoc` at the two factorisations
  `f_j = f_i ≫ f_{ji}` and `f_k = f_j ≫ f_{kj}` of the projections, together with the cocycle
  condition of the system read in the constructed inverse image,
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemTransitionMap_comp`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem_idem`,
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem_comp_systemDiagramMap` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramMap_comp_systemDiagramIdem` —
  the identity-transition map is idempotent and acts as the identity on every diagram map, on
  either side. These are the three instances of multiplicativity in which one of the two
  transitions is an identity, and they say exactly that `i ↦ (L_i, e_i)` is a functor into the
  Karoubi envelope.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCompatibleFamily_iff_systemDiagramMap` —
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCompatibleFamily` is the cocone condition
  for this diagram.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramMap_naturality` — a family of
  maps `F_i ⟶ G_i` commuting with the transitions induces a map of diagrams.

## Implementation notes

**Which `≫` the multiplicativity uses.** For `a : i ⟶ j` the map `d_a` goes `L_j ⟶ L_i`, against
the direction of `a`; so `d_{a ≫ b} = d_b ≫ d_a`, and the assignment is a functor on `I` rather
than on `Iᵒᵖ`. That is the direction in which the colimit of the `L_i` is taken.

**`conePi`.** Projections are written `conePi c i` and never `c.π.app i`, as in the files this
one extends: the second spelling has source `((Functor.const Iᵒᵖ).obj c.pt).obj i`, which
typeclass inference does not unfold, so the `HasSheafify` instance for the small étale site of
the limit is not found.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]

/-- **The diagram map of a system on the limit site.** For a transition `a : i ⟶ j` of the index
this is the map `f_j^{-1}F_j ⟶ f_i^{-1}F_i`: the comparison
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneInverseImageComp` of inverse images along
the factorisation `f_j = f_i ≫ f_{ji}`, followed by the inverse image along `f_i` of the
transition `Stacks.EtaleCohomology.systemTransitionMap` of the system. -/
def systemDiagramMap (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c j)).obj (F.obj j) ⟶
      (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) :=
  (coneInverseImageComp (c := c) a).hom.app (F.obj j) ≫
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a)

/-- **A compatible family is a cocone on the diagram.** This is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCompatibleFamily` with its composite named by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramMap`. -/
theorem isCompatibleFamily_iff_systemDiagramMap (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H) :
    IsCompatibleFamily F H τ ↔
      ∀ {i j : Iᵒᵖ} (a : i ⟶ j), systemDiagramMap F a ≫ τ i = τ j := by
  refine ⟨fun h _ _ a => ?_, fun h _ _ a => ?_⟩
  · rw [systemDiagramMap, Category.assoc]
    exact h a
  · rw [← Category.assoc]
    exact h a

/-- **The diagram maps compose.** For transitions `a : i ⟶ j` and `b : j ⟶ k` the map of the
composite is the composite of the maps, in the reverse order — the diagram maps run against the
transitions. -/
theorem systemDiagramMap_comp (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j k : Iᵒᵖ}
    (a : i ⟶ j) (b : j ⟶ k) :
    systemDiagramMap (c := c) F (a ≫ b) = systemDiagramMap F b ≫ systemDiagramMap F a := by
  have hpent := etaleAbelianInverseImageCompIso'_assoc.{u, u + 1}
    (D.map b) (D.map a) (conePi c i) (D.map (a ≫ b)) (D.map_comp a b)
    (conePi c j) (conePi_comp c a).symm (conePi c k) (conePi_comp c b).symm
    (conePi_comp c (a ≫ b)).symm
  have key := NatTrans.congr_app (congrArg Iso.inv hpent) (F.obj k)
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id] at key
  have h1 : systemDiagramMap (c := c) F b ≫ systemDiagramMap F a =
      ((coneInverseImageComp (c := c) b).hom.app (F.obj k) ≫
          (coneInverseImageComp (c := c) a).hom.app
            ((etaleAbelianInverseImage.{u, u + 1} (D.map b)).obj (F.obj k))) ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map
          ((etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (systemTransitionMap F b) ≫
            systemTransitionMap F a) := by
    rw [systemDiagramMap, systemDiagramMap, Functor.map_comp]
    simp only [Category.assoc]
    rw [(coneInverseImageComp (c := c) a).hom.naturality_assoc (systemTransitionMap F b)]
    rfl
  have key' : (coneInverseImageComp (c := c) b).hom.app (F.obj k) ≫
      (coneInverseImageComp (c := c) a).hom.app
          ((etaleAbelianInverseImage.{u, u + 1} (D.map b)).obj (F.obj k)) =
      (coneInverseImageComp (c := c) (a ≫ b)).hom.app (F.obj k) ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map
          ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
            (D.map_comp a b)).hom.app (F.obj k)) := key
  rw [h1, key', Category.assoc, ← Functor.map_comp, systemTransitionMap_comp F a b]
  rfl

/-- **The endomorphism of a level attached to its identity transition.** `EtaleSheafSystem`
imposes no identity law — see the module docstring — so this need not be the identity map. It is
an idempotent, and by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem_comp_systemDiagramMap` it acts
as the identity on every diagram map. -/
def systemDiagramIdem (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) (i : Iᵒᵖ) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶
      (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) :=
  systemDiagramMap F (𝟙 i)

/-- The identity-transition endomorphism is idempotent: it is the diagram map of `𝟙 ≫ 𝟙`. -/
theorem systemDiagramIdem_idem (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) (i : Iᵒᵖ) :
    systemDiagramIdem (c := c) F i ≫ systemDiagramIdem F i = systemDiagramIdem F i := by
  rw [systemDiagramIdem, ← systemDiagramMap_comp F (𝟙 i) (𝟙 i), Category.comp_id]

/-- The identity-transition endomorphism of the source of a diagram map absorbs into it. -/
theorem systemDiagramIdem_comp_systemDiagramMap (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemDiagramIdem (c := c) F j ≫ systemDiagramMap F a = systemDiagramMap F a := by
  rw [systemDiagramIdem, ← systemDiagramMap_comp F a (𝟙 j), Category.comp_id]

/-- The identity-transition endomorphism of the target of a diagram map absorbs into it. -/
theorem systemDiagramMap_comp_systemDiagramIdem (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemDiagramMap (c := c) F a ≫ systemDiagramIdem F i = systemDiagramMap F a := by
  rw [systemDiagramIdem, ← systemDiagramMap_comp F (𝟙 i) a, Category.id_comp]

/-- **A compatible family absorbs the identity-transition endomorphism.** This is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCompatibleFamily` at an identity transition,
and it says that a compatible family is a map out of the formal direct factor the idempotent cuts
out. -/
theorem IsCompatibleFamily.systemDiagramIdem_comp
    {F : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    {H : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ H}
    (hτ : IsCompatibleFamily F H τ) (i : Iᵒᵖ) :
    systemDiagramIdem F i ≫ τ i = τ i :=
  (isCompatibleFamily_iff_systemDiagramMap F H τ).mp hτ (𝟙 i)

/-- **A morphism of systems induces a morphism of diagrams.** If the maps `φ_i : F_i ⟶ G_i`
commute with the transitions of the two systems, then their inverse images commute with the
diagram maps. -/
theorem systemDiagramMap_naturality {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
        systemTransitionMap F a ≫ φ i)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemDiagramMap (c := c) F a ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (φ i) =
      (etaleAbelianInverseImage.{u, u + 1} (conePi c j)).map (φ j) ≫ systemDiagramMap G a := by
  rw [systemDiagramMap, systemDiagramMap, Category.assoc,
    (coneInverseImageComp (c := c) a).hom.naturality_assoc (φ j)
      ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap G a))]
  congr 1
  rw [← Functor.map_comp, Functor.comp_map, ← Functor.map_comp, hφ a]

/-- **A morphism of systems commutes with the identity-transition endomorphisms.** This is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramMap_naturality` at an identity
transition, named because it is the side condition making a morphism of systems a morphism of the
formal direct factors the idempotents cut out. -/
theorem systemDiagramIdem_naturality {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
        systemTransitionMap F a ≫ φ i)
    (i : Iᵒᵖ) :
    systemDiagramIdem (c := c) F i ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (φ i) =
      (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (φ i) ≫ systemDiagramIdem G i :=
  systemDiagramMap_naturality φ hφ (𝟙 i)

/-- **The Karoubi side condition of a morphism of systems.** The inverse image of a level map,
followed by the identity-transition idempotent of the target, is a morphism from the formal
direct factor cut out by the source's idempotent to the one cut out by the target's. -/
theorem systemDiagramIdem_comp_map_comp_systemDiagramIdem
    {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}} (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
        systemTransitionMap F a ≫ φ i)
    (i : Iᵒᵖ) :
    systemDiagramIdem (c := c) F i ≫
        ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (φ i) ≫
          systemDiagramIdem G i) ≫ systemDiagramIdem G i =
      (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (φ i) ≫ systemDiagramIdem G i := by
  rw [Category.assoc, systemDiagramIdem_idem, ← Category.assoc,
    systemDiagramIdem_naturality φ hφ i, Category.assoc, systemDiagramIdem_idem]

/-- **The naturality of a morphism of systems, in the Karoubi form.** -/
theorem systemDiagramMap_comp_map_comp_systemDiagramIdem
    {F G : EtaleSheafSystem D AddCommGrpCat.{u + 1}} (φ : ∀ i : Iᵒᵖ, F.obj i ⟶ G.obj i)
    (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (φ j) ≫ systemTransitionMap G a =
        systemTransitionMap F a ≫ φ i)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemDiagramMap (c := c) F a ≫
        ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (φ i) ≫
          systemDiagramIdem G i) =
      ((etaleAbelianInverseImage.{u, u + 1} (conePi c j)).map (φ j) ≫ systemDiagramIdem G j) ≫
        systemDiagramMap G a := by
  rw [← Category.assoc, systemDiagramMap_naturality φ hφ a]
  simp only [Category.assoc]
  rw [systemDiagramMap_comp_systemDiagramIdem, systemDiagramIdem_comp_systemDiagramMap]

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
