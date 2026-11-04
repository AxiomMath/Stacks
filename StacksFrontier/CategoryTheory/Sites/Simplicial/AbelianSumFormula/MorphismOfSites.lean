module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLargeSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation

/-!
# The pullback of abelian sheaves along a morphism of sites is exact

Let `v : C ⥤ D` be a continuous functor of small sites whose induced functor on sheaves of sets
is left exact, that is, a morphism of sites `f : (D, K) → (C, J)` in the sense of Stacks 00X1.
Stacks 04JC identifies the inverse image of abelian sheaves along a morphism of topoi with the
inverse image of the underlying sheaves of sets carrying the induced group structure, and
deduces that it is exact; in this repository that is
`CategoryTheory.Sites.abelianInverseImage_exact`. What that statement does *not* say is that
the functor it is about is the abelian sheaf pullback `v.sheafPullback Ab J K`, the chosen left
adjoint of `v.sheafPushforwardContinuous Ab J K`, which is the form in which every consumer
assumes exactness. This file supplies the missing identification and the consequences.

The identification is made on the pushforward side, where it is elementary: the direct image of
abelian sheaves is the direct image of sheaves of sets together with its induced group
structure, because the direct image of a continuous functor is restriction along `v.op` and
products of sheaves of sets are computed sectionwise. Uniqueness of left adjoints then transports
that to the pullbacks.

## Main results

* `Stacks.Sites.AbelianPullback.abelianSheafPushforwardIso`: for a continuous `v`, the direct
  image of abelian sheaves is obtained from the direct image of sheaves of sets by internalizing
  the group operations, pushing them forward, and reading them off sectionwise. This needs no
  exactness hypothesis.
* `Stacks.Sites.AbelianPullback.sheafPullbackAbIsoAbelianInverseImage`: for a morphism of sites,
  the abelian sheaf pullback is the canonical abelian inverse image of Stacks 04JC.
* `Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_isMorphismOfSites` and
  `.preservesMonomorphisms_sheafPullback_of_isMorphismOfSites`: it is therefore left exact.
* `Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_transition`: the case of a
  transition functor of a simplicial site, which is a morphism of sites by definition.
* `Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_ab_largeSections` and
  `.preservesMonomorphisms_sheafPullback_ab_largeSections`: the same two statements with the
  coefficient universe larger than the universe of the site. This is the form Stacks 0EXZ needs,
  its systems of abelian sheaves being indexed by a category whose universes are unrelated to
  the site's; the input is
  `CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoiLargeSections`.

## Implementation notes

`CategoryTheory.Sites.abelianInverseImage` is built from `CategoryTheory.Functor.mapCommGrp`
applied to the inverse image of a morphism of topoi. The direct image of abelian sheaves admits
the same description, and the comparison `abelianSheafPushforwardIso` with
`CategoryTheory.Functor.sheafPushforwardContinuous` at `AddCommGrpCat` is proved sectionwise: the
underlying presheaves of types agree on the nose, so the comparison is the identity on sections,
and all that has to be checked is that it is additive. That in turn is the statement that the
isomorphism `v^s ⋙ (- : Sheaf → presheaf) ≅ (- : Sheaf → presheaf) ⋙ (- ⋙ v.op)`, whose
components are identities, is monoidal, which is `CategoryTheory.NatTrans.IsMonoidal.tensor`.
Both monoidal structures are the cartesian ones, supplied as file-local instances exactly as in
`StacksFrontier/CategoryTheory/Sites/Modules/InverseImage/AbelianSheaf.lean`.

Note what is *not* assumed: `CategoryTheory.Functor.RepresentablyFlat v`. The repository's own
form of Stacks 00YT, `CategoryTheory.Functor.isIso_mateEquiv_sheafAdjunctionContinuous` in
`StacksFrontier/CategoryTheory/Sites/Presheaf/AlgebraicStructure/Sheaves.lean`, assumes flatness,
and its implementation notes argue that flatness cannot be weakened away. That argument is about
the presheaf-level proof, where it is correct — the repository's Stacks 00YU counterexample shows
the presheaf-level comparison genuinely fails. The route here is the sheaf-level one of
Stacks 04JC, which goes through group objects and needs only that the set-valued pullback be left
exact.

This does **not** apply to the inclusion of a component of a simplicial site into its total site:
that functor is not a morphism of sites, since its set-valued pullback does not preserve the
terminal object. See
`StacksFrontier/CategoryTheory/Sites/AbelianPullbackExact/SimplicialComponent.lean`.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 00YT](https://stacks.math.columbia.edu/tag/00YT)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites

universe w u₀ v₀ u₁ v₁ u

namespace Stacks.Sites.AbelianPullback

/-- The cartesian monoidal structure on sheaves of types, given by finite products. -/
noncomputable local instance cartesianMonoidalCategorySheaf {E : Type u₀} [Category.{v₀} E]
    (J : GrothendieckTopology E) : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts

/-- The braiding on sheaves of types induced by the cartesian monoidal structure. -/
noncomputable local instance braidedCategorySheaf {E : Type u₀} [Category.{v₀} E]
    (J : GrothendieckTopology E) : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory

/-- The forgetful functor from sheaves of types to presheaves of types is braided for the
cartesian monoidal structures. -/
noncomputable local instance braidedSheafToPresheaf {E : Type u₀} [Category.{v₀} E]
    (J : GrothendieckTopology E) : (sheafToPresheaf J (Type w)).Braided :=
  .ofChosenFiniteProducts _

/-- The direct image of sheaves of types along a continuous functor with a left adjoint
preserves finite limits. -/
noncomputable local instance preservesFiniteLimitsSheafPushforward {E : Type u₀} [Category.{v₀} E]
    {F : Type u₁} [Category.{v₁} F] (v : E ⥤ F) (J : GrothendieckTopology E)
    (K : GrothendieckTopology F) [v.IsContinuous J K]
    [(v.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint] :
    PreservesFiniteLimits (v.sheafPushforwardContinuous (Type w) J K) :=
  letI : PreservesLimitsOfSize.{0, 0} (v.sheafPushforwardContinuous (Type w) J K) :=
    (v.sheafAdjunctionContinuous (Type w) J K).rightAdjoint_preservesLimits
  inferInstance

/-- The direct image of sheaves of types along a continuous functor with a left adjoint is braided
for the cartesian monoidal structures. -/
noncomputable local instance braidedSheafPushforward {E : Type u₀} [Category.{v₀} E]
    {F : Type u₁} [Category.{v₁} F] (v : E ⥤ F) (J : GrothendieckTopology E)
    (K : GrothendieckTopology F) [v.IsContinuous J K]
    [(v.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint] :
    (v.sheafPushforwardContinuous (Type w) J K).Braided := .ofChosenFiniteProducts _

section GeneralUniverses

variable {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Pushing the internal group operations of an abelian sheaf forward along a continuous functor
and then reading them off sectionwise gives the direct image of the abelian sheaf. The two sides
have the same underlying presheaf of sets, so the comparison is the identity on sections; what
has to be checked is that it is additive. -/
noncomputable def externalSheafPushforwardIso (v : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [v.IsContinuous J K]
    [(v.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint] :
    ((v.sheafPushforwardContinuous (Type w) J K).mapCommGrp ⋙ AbelianSheaf.externalSheaf J) ≅
      (AbelianSheaf.externalSheaf K ⋙ v.sheafPushforwardContinuous AddCommGrpCat.{w} J K) := by
  let P := v.sheafPushforwardContinuous (Type w) J K
  let V := sheafToPresheaf J (Type w)
  let W := sheafToPresheaf K (Type w)
  let R := (Functor.whiskeringLeft _ _ (Type w)).obj v.op
  let e : P ⋙ V ≅ W ⋙ R := NatIso.ofComponents (fun _ => Iso.refl _)
  have hmul (G : Sheaf K (Type w)) :
      Functor.LaxMonoidal.μ V (P.obj G) (P.obj G) ≫ V.map (Functor.LaxMonoidal.μ P G G) =
        R.map (Functor.LaxMonoidal.μ W G G) := by
    have h := NatTrans.IsMonoidal.tensor (τ := e.hom) G G
    simp only [Functor.Monoidal.μ_comp, e] at h
    exact h
  refine NatIso.ofComponents (fun G => ?_) ?_
  · refine (fullyFaithfulSheafToPresheaf J _).preimageIso
      (NatIso.ofComponents (fun U => ?_) ?_)
    · let A : AddCommGrpCat.{w} :=
        ((P.mapCommGrp ⋙ AbelianSheaf.externalSheaf J).obj G).obj.obj U
      let B : AddCommGrpCat.{w} := ((AbelianSheaf.externalSheaf K).obj G).obj.obj (v.op.obj U)
      have hadd (x y : A) : @Add.add A A.str.toAdd x y = @Add.add B B.str.toAdd x y := by
        change ((Functor.LaxMonoidal.μ V (P.obj G.X) (P.obj G.X) ≫
          V.map (Functor.LaxMonoidal.μ P G.X G.X ≫ P.map (MonObj.mul (X := G.X)))).app U)
          (x, y) = _
        rw [V.map_comp, ← Category.assoc, hmul]
        rfl
      change A ≅ B
      refine { hom := @AddCommGrpCat.ofHom A B A.str B.str
                 (@AddMonoidHom.mk' A B B.str.toAddGroup A.str.toAddZeroClass id hadd),
               inv := @AddCommGrpCat.ofHom B A B.str A.str
                 (@AddMonoidHom.mk' B A A.str.toAddGroup B.str.toAddZeroClass id
                   (fun x y => (hadd x y).symm)),
               hom_inv_id := ?_, inv_hom_id := ?_ }
      · ext x; rfl
      · ext x; rfl
    · intro U V f; ext x; rfl
  · intro G H f; ext U x; rfl

/-- **Stacks 00YT at the sheaf level, for the underlying-set functor of abelian groups, with no
flatness hypothesis.** For a continuous functor of sites whose set-valued direct image has a left
adjoint, the direct image of abelian sheaves is the direct image of sheaves of sets together with
its induced group structure.

The three universes of the two sites and of the coefficients are independent, which is what makes
this available for the Zariski comparison morphism of Stacks 0DCU, where the coefficient universe
is neither of the two site universes. -/
noncomputable def abelianSheafPushforwardIso (v : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [v.IsContinuous J K]
    [(v.sheafPushforwardContinuous (Type w) J K).IsRightAdjoint] :
    (AbelianSheaf.internalSheaf K ⋙ (v.sheafPushforwardContinuous (Type w) J K).mapCommGrp ⋙
        AbelianSheaf.externalSheaf J) ≅
      v.sheafPushforwardContinuous AddCommGrpCat.{w} J K :=
  Functor.isoWhiskerLeft (AbelianSheaf.internalSheaf K) (externalSheafPushforwardIso v J K) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (AbelianSheaf.internalExternalIso K)
      (v.sheafPushforwardContinuous AddCommGrpCat.{w} J K) ≪≫
    Functor.leftUnitor _

end GeneralUniverses

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] {v : C ⥤ D}
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} [v.IsContinuous J K]

attribute [local implicit_reducible] CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi

/-- The abelian inverse image of Stacks 04JC is left adjoint to the direct image of abelian
sheaves read off through the group-object equivalence. -/
noncomputable def abelianSheafAdjunction (h : v.IsMorphismOfSites J K) :
    abelianInverseImage h.morphismOfTopoi ⊣
      (AbelianSheaf.internalSheaf K ⋙ (v.sheafPushforwardContinuous (Type u) J K).mapCommGrp ⋙
        AbelianSheaf.externalSheaf J) :=
  letI : PreservesFiniteLimits h.morphismOfTopoi.inverseImage :=
    h.morphismOfTopoi.preservesFiniteLimits
  letI : h.morphismOfTopoi.inverseImage.Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits h.morphismOfTopoi.pushforward :=
    preservesFiniteLimitsSheafPushforward v J K
  letI : h.morphismOfTopoi.pushforward.Braided := braidedSheafPushforward v J K
  ((AbelianSheaf.equivalence J).toAdjunction.comp
      (h.morphismOfTopoi.adj.mapCommGrp)).comp (AbelianSheaf.equivalence K).symm.toAdjunction

/-- **The pullback of abelian sheaves along a morphism of sites is the abelian inverse image of
Stacks 04JC.** Both are left adjoint to the direct image of abelian sheaves. -/
noncomputable def sheafPullbackAbIsoAbelianInverseImage (h : v.IsMorphismOfSites J K)
    [HasSheafify K AddCommGrpCat.{u}] :
    v.sheafPullback AddCommGrpCat.{u} J K ≅ abelianInverseImage h.morphismOfTopoi :=
  (v.sheafAdjunctionContinuous AddCommGrpCat.{u} J K).leftAdjointUniq
    ((abelianSheafAdjunction h).ofNatIsoRight (abelianSheafPushforwardIso v J K))

/-- **Stacks 04JC in the form its consumers assume it.** The pullback of abelian sheaves along a
morphism of sites preserves finite limits. -/
theorem preservesFiniteLimits_sheafPullback_of_isMorphismOfSites (h : v.IsMorphismOfSites J K)
    [HasSheafify K AddCommGrpCat.{u}] :
    PreservesFiniteLimits (v.sheafPullback AddCommGrpCat.{u} J K) :=
  preservesFiniteLimits_of_natIso (sheafPullbackAbIsoAbelianInverseImage h).symm

/-- The monomorphism-preservation half of
`Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_of_isMorphismOfSites`. -/
theorem preservesMonomorphisms_sheafPullback_of_isMorphismOfSites (h : v.IsMorphismOfSites J K)
    [HasSheafify K AddCommGrpCat.{u}] :
    (v.sheafPullback AddCommGrpCat.{u} J K).PreservesMonomorphisms := by
  have := preservesFiniteLimits_sheafPullback_of_isMorphismOfSites h
  infer_instance

/-- The transition functors of a simplicial site in case (A) of Stacks 09WE are morphisms of
sites by definition, so the pullback of abelian sheaves along one of them is left exact. -/
theorem preservesMonomorphisms_sheafPullback_transition (Cs : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    [HasSheafify (Cs.coverage n).toGrothendieck AddCommGrpCat.{u}] :
    haveI := (Cs.isMorphismOfSites φ).isContinuous
    (((Cs.underlying.map φ).toFunctor).sheafPullback AddCommGrpCat.{u}
        (Cs.coverage m).toGrothendieck (Cs.coverage n).toGrothendieck).PreservesMonomorphisms :=
  have := (Cs.isMorphismOfSites φ).isContinuous
  preservesMonomorphisms_sheafPullback_of_isMorphismOfSites (Cs.isMorphismOfSites φ)

section MorphismOfTopoi

variable {E : Type u₀} [Category.{v₀} E] {F : Type u₁} [Category.{v₁} F]
  {J : GrothendieckTopology E} {K : GrothendieckTopology F}

/-- The inverse image of a morphism of topoi between categories of sheaves of types is braided
for the cartesian monoidal structures. -/
noncomputable local instance braidedInverseImageOfTopoi
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) : f.inverseImage.Braided :=
  letI : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  .ofChosenFiniteProducts _

/-- The direct image of a morphism of topoi between categories of sheaves of types is braided for
the cartesian monoidal structures. -/
noncomputable local instance braidedPushforwardOfTopoi
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) : f.pushforward.Braided :=
  letI : PreservesLimitsOfSize.{0, 0} f.pushforward := f.adj.rightAdjoint_preservesLimits
  letI : PreservesFiniteLimits f.pushforward := inferInstance
  .ofChosenFiniteProducts _

/-- The abelian inverse image of a morphism of topoi, Stacks 04JC, is left adjoint to the direct
image of abelian sheaves read off through the group-object equivalence.

This is the universe-polymorphic form, for an arbitrary morphism of topoi between sheaf
categories: `abelianSheafAdjunction` is the special case of a morphism of small sites, and the
general one is what the Zariski comparison morphism of Stacks 0DCU needs, its coefficient
universe being neither of its two site universes. -/
noncomputable def abelianAdjunctionOfMorphismOfTopoi
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))) :
    abelianInverseImage f ⊣
      (AbelianSheaf.internalSheaf J ⋙ f.pushforward.mapCommGrp ⋙
        AbelianSheaf.externalSheaf K) :=
  ((AbelianSheaf.equivalence K).toAdjunction.comp (f.adj.mapCommGrp)).comp
    (AbelianSheaf.equivalence J).symm.toAdjunction

end MorphismOfTopoi

section LargeSections

universe q

attribute [local implicit_reducible]
  CategoryTheory.Functor.morphismOfTopoiOfPreservesFiniteLimits

/-- The abelian inverse image of Stacks 04JC along a continuous functor whose set-valued pullback
is left exact at the coefficient universe is left adjoint to the direct image of abelian sheaves
read off through the group-object equivalence. -/
noncomputable def abelianSheafAdjunctionOfPreserves
    [(v.sheafPushforwardContinuous (Type q) J K).IsRightAdjoint]
    (hq : PreservesFiniteLimits (v.sheafPullback (Type q) J K)) :
    CategoryTheory.Sites.abelianInverseImage
        (Functor.morphismOfTopoiOfPreservesFiniteLimits J K v hq) ⊣
      (AbelianSheaf.internalSheaf K ⋙
        (v.sheafPushforwardContinuous (Type q) J K).mapCommGrp ⋙
        AbelianSheaf.externalSheaf J) :=
  letI : PreservesFiniteLimits (v.sheafPullback (Type q) J K) := hq
  letI : (v.sheafPullback (Type q) J K).Braided := .ofChosenFiniteProducts _
  letI : PreservesFiniteLimits (v.sheafPushforwardContinuous (Type q) J K) :=
    preservesFiniteLimitsSheafPushforward v J K
  letI : (v.sheafPushforwardContinuous (Type q) J K).Braided := braidedSheafPushforward v J K
  ((AbelianSheaf.equivalence J).toAdjunction.comp
      ((v.sheafAdjunctionContinuous (Type q) J K).mapCommGrp)).comp
    (AbelianSheaf.equivalence K).symm.toAdjunction

/-- **The pullback of abelian sheaves is the abelian inverse image of Stacks 04JC at any
coefficient universe at which the set-valued pullback is left exact.** Both are left adjoint to
the direct image of abelian sheaves. -/
noncomputable def sheafPullbackAbIsoAbelianInverseImageOfPreserves
    [(v.sheafPushforwardContinuous (Type q) J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous AddCommGrpCat.{q} J K).IsRightAdjoint]
    (hq : PreservesFiniteLimits (v.sheafPullback (Type q) J K)) :
    v.sheafPullback AddCommGrpCat.{q} J K ≅
      CategoryTheory.Sites.abelianInverseImage
        (Functor.morphismOfTopoiOfPreservesFiniteLimits J K v hq) :=
  (v.sheafAdjunctionContinuous AddCommGrpCat.{q} J K).leftAdjointUniq
    ((abelianSheafAdjunctionOfPreserves hq).ofNatIsoRight
      (abelianSheafPushforwardIso v J K))

/-- **Stacks 04JC in the form its consumers assume it, at any coefficient universe at which the
set-valued pullback is left exact.** -/
theorem preservesFiniteLimits_sheafPullback_ab_of_preserves
    [(v.sheafPushforwardContinuous (Type q) J K).IsRightAdjoint]
    [(v.sheafPushforwardContinuous AddCommGrpCat.{q} J K).IsRightAdjoint]
    (hq : PreservesFiniteLimits (v.sheafPullback (Type q) J K)) :
    PreservesFiniteLimits (v.sheafPullback AddCommGrpCat.{q} J K) :=
  preservesFiniteLimits_of_natIso
    (sheafPullbackAbIsoAbelianInverseImageOfPreserves hq).symm

/-- **Stacks 04JC in the form its consumers assume it, with sections in any larger universe.**
The pullback of abelian sheaves along a morphism of sites preserves finite limits even when the
coefficient universe is not the universe of the site. -/
theorem preservesFiniteLimits_sheafPullback_ab_largeSections (h : v.IsMorphismOfSites J K)
    [(v.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).IsRightAdjoint] :
    PreservesFiniteLimits (v.sheafPullback AddCommGrpCat.{max u w} J K) :=
  preservesFiniteLimits_sheafPullback_ab_of_preserves
    (hq := Functor.preservesFiniteLimits_sheafPullback_largeSections h)

/-- The monomorphism-preservation half of
`Stacks.Sites.AbelianPullback.preservesFiniteLimits_sheafPullback_ab_largeSections`. -/
theorem preservesMonomorphisms_sheafPullback_ab_largeSections (h : v.IsMorphismOfSites J K)
    [(v.sheafPushforwardContinuous AddCommGrpCat.{max u w} J K).IsRightAdjoint] :
    (v.sheafPullback AddCommGrpCat.{max u w} J K).PreservesMonomorphisms := by
  have : PreservesFiniteLimits (v.sheafPullback AddCommGrpCat.{max u w} J K) :=
    preservesFiniteLimits_sheafPullback_ab_largeSections h
  infer_instance

end LargeSections

end Stacks.Sites.AbelianPullback

end
