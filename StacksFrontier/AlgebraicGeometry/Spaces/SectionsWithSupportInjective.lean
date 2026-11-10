module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupport
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction

/-!
# Injectivity of the sections with support in a closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. The functor `H_Z`
of `StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupport.lean` sends an abelian sheaf on the
small étale site of `X` to the sections with support in `|Z|`, viewed on the small étale site
of `Z`. It is right adjoint to the direct image `i_*`, because a morphism from `i_*G` lands in
the sections with support in `|Z|` — every section of `i_*G` has support there — and because
direct image along a closed immersion is fully faithful. Granted that adjunction, direct image
is exact, so `H_Z` carries an injective abelian sheaf on `X_étale` to an injective abelian sheaf
on `Z_étale`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianInverseImage` and
  `AlgebraicGeometry.Space.smallEtaleAbelianInverseImageAdjunction`: the inverse image of
  abelian sheaves along a representable morphism of algebraic spaces, and its adjunction with
  the direct image.
* `AlgebraicGeometry.Space.liftToSectionsWithSupport`: the factorization of a morphism out of a
  direct image through the sections with support in `|Z|`.
* `AlgebraicGeometry.Space.UnitIsoOnSupportedSheaves`: the essential-image clause of
  Stacks 04E5, part (2), in the form in which it is used here.
* `AlgebraicGeometry.Space.pushforwardSectionsWithSupportHomEquiv` and
  `AlgebraicGeometry.Space.pushforwardSectionsWithSupportAdjunction`: the hom-set bijection
  `(i_*G ⟶ F) ≃ (G ⟶ H_Z F)` and the adjunction `i_* ⊣ H_Z` it presents.

## Main results

* `AlgebraicGeometry.Space.liftToSectionsWithSupport_comp_inclusion` and
  `AlgebraicGeometry.Space.liftToSectionsWithSupport_unique`: the factorization composes to the
  original morphism and is the only one that does, so composition with the inclusion of the
  sections with support is a bijection on morphisms out of a direct image. This is the source's
  "any section of `i_*G` has support in `Z`".
* `AlgebraicGeometry.Space.pushforwardSectionsWithSupportAdjunction`: the adjunction
  `i_* ⊣ H_Z`, granted the essential-image clause. This is the source's
  `Hom_Z(G, H_Z(F)) = Hom_X(i_*G, F)`.
* `AlgebraicGeometry.Space.preservesFiniteLimits_smallEtaleAbelianPushforward` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_smallEtaleAbelianPushforward_of_adjunction`:
  exactness of the direct image along a closed immersion, the second from the adjunction
  `i_* ⊣ H_Z`.
* `AlgebraicGeometry.Space.injective_sectionsWithSupportInClosedSubspace` and
  `AlgebraicGeometry.Space.injective_sectionsWithSupportInClosedSubspace_of_unitIso`: the
  sections with support in `|Z|` of an injective abelian sheaf on `X_étale` form an injective
  abelian sheaf on `Z_étale`.

## Implementation notes

The coefficient universe is `u + 1` throughout, as in
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupport.lean`: there the small étale site has
sheafification for abelian groups as an instance, so the inverse image is the functor
`CategoryTheory.Functor.sheafPullback` and not a left adjoint chosen from an existence
statement, and it is the universe of the left-inverse clause of Stacks 04E5, part (2).

Exactness of the direct image is *not* taken from the exactness statement of Stacks 0A4K. That
statement is proved in this development, in
`StacksFrontier/AlgebraicGeometry/Spaces/AbelianPushforwardExact.lean`, only under an explicit
surjectivity hypothesis which is not available here. For a closed immersion neither half needs
it: preservation of limits is right-adjointness of the direct image in the adjunction with the
inverse image, which Stacks 04E5, part (2) supplies unconditionally, and preservation of
colimits is left-adjointness of the direct image in the adjunction with `H_Z`.

The hom-set bijection is a composite of three bijections, so no inverse-map computation is
needed: the unique factorization of a morphism out of `i_*G` through the sections with support,
composition with the unit at those sections — invertible by the essential-image clause — and
full faithfulness of the direct image. Both naturality conditions of the adjunction are then
checked after applying the direct image, where the bijection is the factorization composed
with the unit.

## The essential-image clause

The essential-image clause of Stacks 04E5, part (2) — that the unit `A ⟶ i_*i^{-1}A` is an
isomorphism for an abelian sheaf `A` on `X_étale` all of whose sections have support in `|Z|` —
is the one ingredient of the adjunction that is not proved here. It is carried as the hypothesis
`AlgebraicGeometry.Space.UnitIsoOnSupportedSheaves`, which
`StacksFrontier/AlgebraicGeometry/Spaces/ComplexesWithSupport.lean` discharges for every closed
immersion in `AlgebraicGeometry.Space.unitIsoOnSupportedSheaves_of_isClosedImmersion`. The
hypothesis therefore remains here only because that file consumes this one; the unconditional
adjunction is
`AlgebraicGeometry.Space.pushforwardSectionsWithSupportAdjunctionOfIsClosedImmersion` and the
unconditional form of Stacks 0A4M is
`AlgebraicGeometry.Space.injective_sectionsWithSupportInClosedSubspace_of_isClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/InjectiveSectionsWithSupport.lean`, which is where the
tag sits. Nothing in this file carries it: every statement here still mentions the hypothesis.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4M](https://stacks.math.columbia.edu/tag/0A4M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-! ### The inverse image of abelian sheaves -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasWeakSheafify` and `HasLeftKanExtension` on the small étale site is deep
/-- Pushforward of abelian sheaves along base change of étale scheme charts is a right adjoint.
Supplied explicitly because instance search no longer finds it. -/
theorem isRightAdjoint_smallBaseChange_addCommGrp (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom)
    [(smallBaseChange B S hS i hr).IsContinuous (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Z.1)] :
    ((smallBaseChange B S hS i hr).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)).IsRightAdjoint := by
  have h1 : HasWeakSheafify (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1} :=
    inferInstance
  have h2 : ∀ F : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallBaseChange B S hS i hr).op.HasLeftKanExtension F := fun _ => inferInstance
  exact (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).isRightAdjoint

/-- The inverse image of abelian sheaves along a morphism of algebraic spaces with
representable underlying morphism: the left adjoint of restriction along base change of étale
scheme charts. -/
abbrev smallEtaleAbelianInverseImage (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1} :=
  letI := (smallBaseChange_isMorphismOfSites B S hS i hr).toIsContinuous
  haveI := isRightAdjoint_smallBaseChange_addCommGrp B S hS i hr
  (smallBaseChange B S hS i hr).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)

/-- The adjunction between the inverse image and the direct image of abelian sheaves on small
étale sites. -/
abbrev smallEtaleAbelianInverseImageAdjunction (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom) :
    smallEtaleAbelianInverseImage B S hS i hr ⊣
      smallEtaleAbelianPushforward.{u + 1} B S hS i hr :=
  letI := (smallBaseChange_isMorphismOfSites B S hS i hr).toIsContinuous
  haveI := isRightAdjoint_smallBaseChange_addCommGrp B S hS i hr
  (smallBaseChange B S hS i hr).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)

/-- The direct image of abelian sheaves preserves finite limits, being a right adjoint. -/
instance preservesFiniteLimits_smallEtaleAbelianPushforward (i : Z ⟶ X)
    (hr : yoneda.relativelyRepresentable i.hom) :
    PreservesFiniteLimits (smallEtaleAbelianPushforward.{u + 1} B S hS i hr) :=
  haveI : PreservesLimits (smallEtaleAbelianPushforward.{u + 1} B S hS i hr) :=
    (smallEtaleAbelianInverseImageAdjunction B S hS i hr).rightAdjoint_preservesLimits
  inferInstance

/-! ### Morphisms out of a direct image factor through the sections with support -/

variable (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)

/-- **Every morphism out of a direct image along a closed immersion factors through the
sections with support in `|Z|`.**

This is the source's observation that any section of `i_*G` has support in `Z`: a morphism of
abelian sheaves cannot enlarge the support of a section, so the image of a section of `i_*G`
again has support in `|Z|`. -/
def liftToSectionsWithSupport
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (φ : (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶ F) :
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶
      (closedSectionsWithSupport.{u + 1} B S hS i).obj F :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
       { toFun := fun σ ↦ ⟨φ.hom.app U σ,
           sectionSupportedOn_map φ σ
             (sectionSupportedOn_smallEtaleAbelianPushforward B S hS i hi G U.unop σ)⟩
         map_zero' := by ext; exact map_zero _
         map_add' := fun σ τ ↦ by ext; exact map_add _ _ _ }
     naturality := fun {U V} g ↦ by
       ext σ
       refine Subtype.ext ?_
       exact congrArg (fun k ↦ (ConcreteCategory.hom k) σ) (φ.hom.naturality g) }⟩

/-- The factorization through the sections with support composes with the inclusion to the
original morphism. -/
@[reassoc (attr := simp)]
theorem liftToSectionsWithSupport_comp_inclusion
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (φ : (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶ F) :
    liftToSectionsWithSupport B S hS i hi G F φ ≫
        (sectionsWithSupportInclusion.{u + 1} B S hS X.1
          (Set.range (pointsMap B S hS Z.1 i.hom))).app F = φ := by
  refine Sheaf.hom_ext ?_
  ext U σ
  rfl

/-- The factorization through the sections with support is the only morphism composing with
the inclusion to the given one, the inclusion being a monomorphism. -/
theorem liftToSectionsWithSupport_unique
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (φ : (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶ F)
    (ψ : (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶
      (closedSectionsWithSupport.{u + 1} B S hS i).obj F)
    (hψ : ψ ≫ (sectionsWithSupportInclusion.{u + 1} B S hS X.1
      (Set.range (pointsMap B S hS Z.1 i.hom))).app F = φ) :
    ψ = liftToSectionsWithSupport B S hS i hi G F φ :=
  (cancel_mono ((sectionsWithSupportInclusion.{u + 1} B S hS X.1
    (Set.range (pointsMap B S hS Z.1 i.hom))).app F)).1
    (hψ.trans (liftToSectionsWithSupport_comp_inclusion B S hS i hi G F φ).symm)

/-- The factorization through the sections with support is natural in the target sheaf. -/
theorem liftToSectionsWithSupport_comp
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (F F' : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (φ : (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶ F) (g : F ⟶ F') :
    liftToSectionsWithSupport B S hS i hi G F' (φ ≫ g) =
      liftToSectionsWithSupport B S hS i hi G F φ ≫
        (closedSectionsWithSupport.{u + 1} B S hS i).map g :=
  (liftToSectionsWithSupport_unique B S hS i hi G F' (φ ≫ g) _ (by
    rw [Category.assoc, (sectionsWithSupportInclusion.{u + 1} B S hS X.1
      (Set.range (pointsMap B S hS Z.1 i.hom))).naturality g, ← Category.assoc,
      liftToSectionsWithSupport_comp_inclusion]
    rfl)).symm

/-- The factorization through the sections with support is natural in the source sheaf. -/
theorem liftToSectionsWithSupport_comp_left
    (G G' : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) (f : G' ⟶ G)
    (φ : (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶ F) :
    liftToSectionsWithSupport B S hS i hi G' F
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).map f ≫ φ) =
      (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).map f ≫
        liftToSectionsWithSupport B S hS i hi G F φ :=
  (liftToSectionsWithSupport_unique B S hS i hi G' F _ _ (by
    rw [Category.assoc, liftToSectionsWithSupport_comp_inclusion])).symm

/-! ### The adjunction -/

/-- **The essential-image input.** An abelian sheaf on `X_étale` all of whose sections have
support in `|Z|` is in the essential image of the direct image along `i`, in the form that the
unit of the inverse-image/direct-image adjunction is invertible at it.

This is the essential-image clause of Stacks 04E5, part (2). By part (4) of Stacks 04KB the
hypothesis on the sections is the containment of the support of the sheaf in `|Z|`, which is how
the source phrases it. -/
def UnitIsoOnSupportedSheaves : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1},
    (∀ (U : SmallEtale B S hS X.1) (σ : F.obj.obj (op U)),
      SectionSupportedOn B S hS X.1 (Set.range (pointsMap B S hS Z.1 i.hom)) F U σ) →
    IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.app F)

/-- The unit of the inverse-image/direct-image adjunction is invertible at the sections with
support in `|Z|`, granted the essential-image input. -/
theorem isIso_unit_app_closedSectionsWithSupport
    (hess : UnitIsoOnSupportedSheaves B S hS i hi)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :
    IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.app
      ((closedSectionsWithSupport.{u + 1} B S hS i).obj F)) :=
  hess _ (sectionSupportedOn_sectionsWithSupportSheaf B S hS X.1 _ F)

/-- The hom-set bijection `(i_*G ⟶ F) ≃ (G ⟶ H_Z F)` of the adjunction `i_* ⊣ H_Z`, granted
the essential-image input.

It is the composite of three bijections: a morphism out of `i_*G` factors uniquely through the
sections with support in `|Z|`; the unit of the inverse-image/direct-image adjunction at those
sections is invertible; and the direct image is fully faithful by Stacks 04E5, part (2). -/
def pushforwardSectionsWithSupportHomEquiv (hess : UnitIsoOnSupportedSheaves B S hS i hi)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :
    ((smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶ F) ≃
      (G ⟶ (sectionsWithSupportInClosedSubspace B S hS i hi).obj F) :=
  haveI := isIso_unit_app_closedSectionsWithSupport B S hS i hi hess F
  Equiv.trans
    { toFun := liftToSectionsWithSupport B S hS i hi G F
      invFun := fun ψ ↦ ψ ≫ (sectionsWithSupportInclusion.{u + 1} B S hS X.1
        (Set.range (pointsMap B S hS Z.1 i.hom))).app F
      left_inv := fun φ ↦ liftToSectionsWithSupport_comp_inclusion B S hS i hi G F φ
      right_inv := fun ψ ↦
        (liftToSectionsWithSupport_unique B S hS i hi G F _ ψ rfl).symm }
    (Equiv.trans
      { toFun := fun ψ ↦ ψ ≫ (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.app
          ((closedSectionsWithSupport.{u + 1} B S hS i).obj F)
        invFun := fun ψ ↦ ψ ≫ inv ((smallEtaleAbelianInverseImageAdjunction
          B S hS i hi.rep).unit.app ((closedSectionsWithSupport.{u + 1} B S hS i).obj F))
        left_inv := fun ψ ↦ by simp
        right_inv := fun ψ ↦ by simp }
      (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1}
        B S hS i hi).homEquiv.symm)

/-- The hom-set bijection is pinned down by its direct image: that is the factorization through
the sections with support, composed with the unit. -/
theorem map_pushforwardSectionsWithSupportHomEquiv
    (hess : UnitIsoOnSupportedSheaves B S hS i hi)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u + 1})
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
    (φ : (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).obj G ⟶ F) :
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep).map
        (pushforwardSectionsWithSupportHomEquiv B S hS i hi hess G F φ) =
      liftToSectionsWithSupport B S hS i hi G F φ ≫
        (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.app
          ((closedSectionsWithSupport.{u + 1} B S hS i).obj F) :=
  (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1}
    B S hS i hi).map_preimage _

/-- **The adjunction `i_* ⊣ H_Z`**, granted the essential-image input: the direct image along a
closed immersion is left adjoint to the sections with support in `|Z|`.

This is the first assertion of the source's proof of Stacks 0A4M,
`Hom_Z(G, H_Z(F)) = Hom_X(i_*G, F)`. -/
def pushforwardSectionsWithSupportAdjunction
    (hess : UnitIsoOnSupportedSheaves B S hS i hi) :
    smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep ⊣
      sectionsWithSupportInClosedSubspace B S hS i hi :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pushforwardSectionsWithSupportHomEquiv B S hS i hi hess
      homEquiv_naturality_left_symm := fun {G' G F} f ψ ↦ by
        rw [Equiv.symm_apply_eq]
        refine (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1}
          B S hS i hi).map_injective ?_
        rw [Functor.map_comp, map_pushforwardSectionsWithSupportHomEquiv,
          liftToSectionsWithSupport_comp_left, Category.assoc,
          ← map_pushforwardSectionsWithSupportHomEquiv B S hS i hi hess,
          Equiv.apply_symm_apply]
        rfl
      homEquiv_naturality_right := fun {G F F'} φ g ↦ by
        refine (fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1}
          B S hS i hi).map_injective ?_
        rw [map_pushforwardSectionsWithSupportHomEquiv, Functor.map_comp,
          map_pushforwardSectionsWithSupportHomEquiv, liftToSectionsWithSupport_comp]
        simp only [Category.assoc]
        exact congrArg (fun k ↦ liftToSectionsWithSupport B S hS i hi G F φ ≫ k)
          ((smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).unit.naturality
            ((closedSectionsWithSupport.{u + 1} B S hS i).map g)) }

/-! ### Injectivity of the sections with support -/

/-- Granted the adjunction `i_* ⊣ H_Z`, the direct image of abelian sheaves along a closed
immersion preserves finite colimits, being a left adjoint. -/
theorem preservesFiniteColimits_smallEtaleAbelianPushforward_of_adjunction
    (adj : smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep ⊣
      sectionsWithSupportInClosedSubspace B S hS i hi) :
    PreservesFiniteColimits (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep) :=
  have : PreservesColimits (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep) :=
    adj.leftAdjoint_preservesColimits
  inferInstance

/-- **Stacks 0A4M**, granted the adjunction `i_* ⊣ H_Z`: the sections with support in `|Z|`
carry injective abelian sheaves on `X_étale` to injective abelian sheaves on `Z_étale`.

The direct image along a closed immersion is exact — it preserves limits as the right adjoint
of the inverse image and colimits as the left adjoint of `H_Z` — so Stacks 015Z applies to the
adjunction. -/
theorem preservesInjectiveObjects_sectionsWithSupportInClosedSubspace
    (adj : smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep ⊣
      sectionsWithSupportInClosedSubspace B S hS i hi) :
    (sectionsWithSupportInClosedSubspace B S hS i hi).PreservesInjectiveObjects :=
  (preservesInjectiveObjects_of_exact_of_adjunction
    (sectionsWithSupportInClosedSubspace B S hS i hi)
    (smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep) adj).2
    ⟨inferInstance,
      preservesFiniteColimits_smallEtaleAbelianPushforward_of_adjunction B S hS i hi adj⟩

/-- **Stacks 0A4M**, granted the adjunction `i_* ⊣ H_Z`: for an injective abelian sheaf `I` on
the small étale site of `X`, the sheaf `H_Z(I)` of sections with support in `|Z|` is an
injective abelian sheaf on the small étale site of `Z`. -/
theorem injective_sectionsWithSupportInClosedSubspace
    (adj : smallEtaleAbelianPushforward.{u + 1} B S hS i hi.rep ⊣
      sectionsWithSupportInClosedSubspace B S hS i hi)
    (I : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((sectionsWithSupportInClosedSubspace B S hS i hi).obj I) :=
  have := preservesInjectiveObjects_sectionsWithSupportInClosedSubspace B S hS i hi adj
  Functor.injective_obj_of_injective (sectionsWithSupportInClosedSubspace B S hS i hi)
    inferInstance

/-- **Stacks 0A4M**, granted the essential-image clause of Stacks 04E5, part (2): for an
injective abelian sheaf `I` on the small étale site of `X`, the sheaf `H_Z(I)` of sections with
support in `|Z|` is an injective abelian sheaf on the small étale site of `Z`.

This is the source's proof: `Hom_Z(G, H_Z(I)) = Hom_X(i_*G, I)` because every section of `i_*G`
has support in `|Z|`, and `i_*` is exact, so Stacks 015Z applies. -/
theorem injective_sectionsWithSupportInClosedSubspace_of_unitIso
    (hess : UnitIsoOnSupportedSheaves B S hS i hi)
    (I : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((sectionsWithSupportInClosedSubspace B S hS i hi).obj I) :=
  injective_sectionsWithSupportInClosedSubspace B S hS i hi
    (pushforwardSectionsWithSupportAdjunction B S hS i hi hess) I

end AlgebraicGeometry.Space

end
