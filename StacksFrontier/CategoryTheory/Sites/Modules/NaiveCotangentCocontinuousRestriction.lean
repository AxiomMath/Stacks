module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPresentationIso
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex

/-!
# The naive cotangent complex commutes with restriction along a cocontinuous functor

Let `G : C₀ ⥤ C` be a functor of sites which is continuous and cocontinuous (for instance the
inclusion of a dense subsite), and write `G_*` for restriction of sheaves along `G`. For a
homomorphism `a : A ⟶ B` of sheaves of commutative rings on `C`, this file identifies

`G_* NL_{B/A} ≅ NL_{G_*B/G_*A}`

as complexes of sheaves of `G_*B`-modules on `C₀`. The source uses this silently whenever it
computes the naive cotangent complex of a ringed topos on a site of definition of its choice.

## The construction

* Sheafification of presheaves of modules along a locally bijective morphism of rings
  `α : R₀ ⟶ R` commutes with restriction along `G`
  (`Stacks.SheafOfModules.PushforwardSheafification.sheafifyAlongRestrictionIso`): the
  restricted unit is locally bijective because `G` is cocontinuous. This is
  `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso` with `α` in place of
  the identity.
* The free algebra `A[B]` commutes with restriction
  (`Stacks.Sites.FreeAlgebra.freeAlgebraSheafRestrictionIso`): it is the sheafification of the
  objectwise polynomial presheaf, and sheafification of sheaves of rings commutes with restriction
  along `G` (`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility`). The
  identification is one of `G_*A`-algebras over `G_*B`.
* The conormal sequence of a presentation commutes with restriction
  (`Stacks.Sites.Conormal.conormalSequenceRestrictionIso`): its terms are module
  sheafifications of objectwise constructions.
* The two are assembled with the change of presentation isomorphisms
  `Stacks.Sites.Conormal.conormalSheafIsoOfFac` and `Stacks.Sites.Conormal.tensorSheafIsoOfFac`.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentComplexRestrictionIso`: `G_* NL_{B/A} ≅ NL_{G_*B/G_*A}`.

## Implementation notes

The two sites may live in different universes. Both complexes have their sections in the join
`max w u₀ v₀ u v z`: the complex on `C` at the free universe `max u₀ v₀ z`, the one on `C₀` at
`max u v z`.

## References

* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0), restriction to a site of
  definition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t m w v₀ u₀ v u z

/-! ### Module sheafification along a locally bijective morphism commutes with restriction -/

namespace Stacks.SheafOfModules.PushforwardSheafification

section Along

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C) (G : C₀ ⥤ C)
  [G.IsContinuous J₀ J]
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)

/-- The restriction of the sheaf of rings `R` along `G`. -/
abbrev restrictedRing : Sheaf J₀ RingCat.{t} := (G.sheafPushforwardContinuous RingCat.{t} J₀ J).obj
    R

/-- The restriction of `α` along `G`. -/
abbrev restrictedRingMap : G.op ⋙ R₀ ⟶ (restrictedRing J₀ J G (R := R)).obj :=
  Functor.whiskerLeft G.op α

/-- Restriction of sheaves of modules along `G`, with no change of scalars. -/
abbrev sheafRestriction :
    _root_.SheafOfModules.{m} R ⥤ _root_.SheafOfModules.{m} (restrictedRing J₀ J G (R := R)) :=
  _root_.SheafOfModules.pushforward.{m} (𝟙 _)

/-- Restriction of presheaves of modules along `G` is an additive functor. -/
instance pushforward₀_additive : (PresheafOfModules.pushforward₀.{m} G R₀).Additive where
  map_add := rfl

variable [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- The sheafification unit along `α`, restricted along `G`. -/
def sheafifyAlongRestrictionUnit (P : PresheafOfModules.{m} R₀) :
    (PresheafOfModules.pushforward₀.{m} G R₀).obj P ⟶
      (PresheafOfModules.restrictScalars (restrictedRingMap J₀ J G α)).obj
        ((_root_.SheafOfModules.forget (restrictedRing J₀ J G (R := R))).obj
          ((sheafRestriction.{t, m} J₀ J G).obj
            ((PresheafOfModules.sheafification.{m} α).obj P))) where
  app V := ((PresheafOfModules.sheafificationAdjunction.{m} α).unit.app P).app (G.op.obj V)
  naturality f := ((PresheafOfModules.sheafificationAdjunction.{m} α).unit.app P).naturality
    (G.op.map f)

/-- The restricted sheafification unit `sheafifyAlongRestrictionUnit` is natural in the presheaf
of modules. -/
theorem sheafifyAlongRestrictionUnit_naturality {P Q : PresheafOfModules.{m} R₀} (f : P ⟶ Q) :
    (PresheafOfModules.pushforward₀.{m} G R₀).map f ≫
        sheafifyAlongRestrictionUnit.{t, m} J₀ J G α Q =
      sheafifyAlongRestrictionUnit.{t, m} J₀ J G α P ≫
        (PresheafOfModules.restrictScalars (restrictedRingMap J₀ J G α)).map
          ((_root_.SheafOfModules.forget (restrictedRing J₀ J G (R := R))).map
            ((sheafRestriction.{t, m} J₀ J G).map
              ((PresheafOfModules.sheafification.{m} α).map f))) := by
  refine PresheafOfModules.hom_ext (fun V ↦ ?_)
  exact congrArg (fun g ↦ g.app (G.op.obj V))
    ((PresheafOfModules.sheafificationAdjunction.{m} α).unit.naturality f)

variable [G.IsCocontinuous J₀ J]

/-- The restriction along a cocontinuous `G` of a locally injective morphism of rings is locally
injective. -/
instance isLocallyInjective_restrictedRingMap :
    Presheaf.IsLocallyInjective J₀ (restrictedRingMap J₀ J G α) :=
  Presheaf.isLocallyInjective_whisker J₀ J G α

/-- The restriction along a cocontinuous `G` of a locally surjective morphism of rings is locally
surjective. -/
instance isLocallySurjective_restrictedRingMap :
    Presheaf.IsLocallySurjective J₀ (restrictedRingMap J₀ J G α) :=
  Presheaf.isLocallySurjective_whisker J₀ J G α

variable [J₀.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J₀ AddCommGrpCat.{m}]

/-- The comparison morphism from the sheafification of the restriction to the restriction of
the sheafification, adjoint to the restricted unit. -/
def sheafifyAlongRestrictionHom (P : PresheafOfModules.{m} R₀) :
    (PresheafOfModules.sheafification.{m} (restrictedRingMap J₀ J G α)).obj
        ((PresheafOfModules.pushforward₀.{m} G R₀).obj P) ⟶
      (sheafRestriction.{t, m} J₀ J G).obj ((PresheafOfModules.sheafification.{m} α).obj P) :=
  ((PresheafOfModules.sheafificationAdjunction.{m} (restrictedRingMap J₀ J G α)).homEquiv _ _).symm
    (sheafifyAlongRestrictionUnit.{t, m} J₀ J G α P)

/-- The comparison morphism `sheafifyAlongRestrictionHom` is an isomorphism. -/
instance isIso_sheafifyAlongRestrictionHom (P : PresheafOfModules.{m} R₀) :
    IsIso (sheafifyAlongRestrictionHom.{t, m} J₀ J G α P) := by
  have hu : (PresheafOfModules.toPresheaf _).map (sheafifyAlongRestrictionUnit.{t, m} J₀ J G α P)
      = Functor.whiskerLeft G.op (CategoryTheory.toSheafify J P.presheaf) := rfl
  have hinj : Presheaf.IsLocallyInjective J₀
      ((PresheafOfModules.toPresheaf _).map (sheafifyAlongRestrictionUnit.{t, m} J₀ J G α P)) := by
    rw [hu]; exact Presheaf.isLocallyInjective_whisker J₀ J G _
  have hsurj : Presheaf.IsLocallySurjective J₀
      ((PresheafOfModules.toPresheaf _).map (sheafifyAlongRestrictionUnit.{t, m} J₀ J G α P)) := by
    rw [hu]; exact Presheaf.isLocallySurjective_whisker J₀ J G _
  have e : sheafifyAlongRestrictionHom.{t, m} J₀ J G α P =
      (PresheafOfModules.sheafificationHomEquiv _).symm
        (sheafifyAlongRestrictionUnit.{t, m} J₀ J G α P) := by
    refine ((PresheafOfModules.sheafificationHomEquiv _).symm_apply_eq.mpr ?_).symm
    rw [← PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
    exact (Equiv.apply_symm_apply _ _).symm
  rw [e]
  exact SliceSheafification.isIso_sheafificationHomEquiv_symm.{m}
    (restrictedRingMap J₀ J G α) (sheafifyAlongRestrictionUnit.{t, m} J₀ J G α P) hinj hsurj

/-- The comparison morphism `sheafifyAlongRestrictionHom` is natural in the presheaf of modules. -/
theorem sheafifyAlongRestrictionHom_naturality {P Q : PresheafOfModules.{m} R₀} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification.{m} (restrictedRingMap J₀ J G α)).map
        ((PresheafOfModules.pushforward₀.{m} G R₀).map f) ≫
        sheafifyAlongRestrictionHom.{t, m} J₀ J G α Q =
      sheafifyAlongRestrictionHom.{t, m} J₀ J G α P ≫ (sheafRestriction.{t, m} J₀ J G).map
        ((PresheafOfModules.sheafification.{m} α).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{m} (restrictedRingMap J₀ J G α)
  refine (adj.homEquiv_naturality_left_symm _ _).symm.trans ?_
  refine ((congrArg (adj.homEquiv _ _).symm
    (sheafifyAlongRestrictionUnit_naturality.{t, m} J₀ J G α f)).trans ?_)
  exact adj.homEquiv_naturality_right_symm _ _

/-- **Sheafification of presheaves of modules along a locally bijective morphism of rings
commutes with restriction along a continuous and cocontinuous functor**, naturally. -/
def sheafifyAlongRestrictionIso :
    PresheafOfModules.pushforward₀.{m} G R₀ ⋙
        PresheafOfModules.sheafification.{m} (restrictedRingMap J₀ J G α) ≅
      PresheafOfModules.sheafification.{m} α ⋙ sheafRestriction.{t, m} J₀ J G :=
  NatIso.ofComponents (fun P ↦ asIso (sheafifyAlongRestrictionHom.{t, m} J₀ J G α P))
    (fun f ↦ sheafifyAlongRestrictionHom_naturality.{t, m} J₀ J G α f)

end Along

end Stacks.SheafOfModules.PushforwardSheafification

/-! ### The free algebra commutes with restriction -/

namespace Stacks.Sites.FreeAlgebra

section Restriction

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C) (G : C₀ ⥤ C)
  [G.IsContinuous J₀ J] [G.IsCocontinuous J₀ J]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J₀ CommRingCat.{w}]
  [∀ F : C₀ᵒᵖ ⥤ CommRingCat.{w}, G.op.HasPointwiseRightKanExtension F]

/-- **The free algebra commutes with restriction**: `(G_*A)[G_*E] ≅ G_*(A[E])`, the
compatibility of sheafification with restriction along `G` at the polynomial presheaf
`U ↦ A(U)[E(U)]`, whose restriction is the polynomial presheaf of the restrictions. -/
def freeAlgebraSheafRestrictionIso (A : Sheaf J CommRingCat.{w}) (E : Cᵒᵖ ⥤ Type w) :
    freeAlgebraSheaf J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        (G.op ⋙ E) ≅
      (G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj (freeAlgebraSheaf J A E) :=
  (G.pushforwardContinuousSheafificationCompatibility CommRingCat.{w} J₀ J).app
    (polynomialPresheaf J A E)

/-- The identification of the free algebras is one of `G_*A`-algebras. -/
theorem freeAlgebraSheafCoefficientMap_comp_restrictionIso_hom (A : Sheaf J CommRingCat.{w})
    (E : Cᵒᵖ ⥤ Type w) :
    freeAlgebraSheafCoefficientMap J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        (G.op ⋙ E) ≫ (freeAlgebraSheafRestrictionIso J₀ J G A E).hom =
      (G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
        (freeAlgebraSheafCoefficientMap J A E) := by
  have h := G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{w} J₀ J
    (polynomialPresheaf J A E)
  refine Sheaf.hom_ext ?_
  exact (congrArg (fun t ↦ polynomialCoefficientMap J₀
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A) (G.op ⋙ E) ≫ t) h).trans rfl

/-- The identification of the free algebras carries the canonical presentation of `G_*B` over
`G_*A` to the restriction of the canonical presentation of `B` over `A`. -/
theorem freeAlgebraSheafRestrictionIso_hom_comp_canonicalPresentation
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    (freeAlgebraSheafRestrictionIso J₀ J G A (underlyingPresheaf J B)).hom ≫
        (G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (canonicalPresentation J A B a) =
      canonicalPresentation J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) := by
  have h := G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{w} J₀ J
    (polynomialPresheaf J A (underlyingPresheaf J B))
  have h₁ := canonicalPresentation_spec J A B a
  have h₂ := canonicalPresentation_spec J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj
      A)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)
  refine Sheaf.hom_ext (sheafify_hom_ext J₀ _ _
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B).cond ?_)
  refine Eq.trans ?_ h₂.symm
  show toSheafify J₀ (G.op ⋙ polynomialPresheaf J A (underlyingPresheaf J B)) ≫
      (((G.pushforwardContinuousSheafificationCompatibility CommRingCat.{w} J₀ J).hom.app
          (polynomialPresheaf J A (underlyingPresheaf J B))).hom ≫
        Functor.whiskerLeft G.op (canonicalPresentation J A B a).hom) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t ↦ t ≫ Functor.whiskerLeft G.op (canonicalPresentation J A B a).hom)
    h).trans ?_
  exact (Functor.whiskerLeft_comp G.op _ _).symm.trans (congrArg (Functor.whiskerLeft G.op) h₁)

end Restriction

end Stacks.Sites.FreeAlgebra

/-! ### The conormal sequence of a presentation commutes with restriction -/

namespace Stacks.Sites.Conormal

section Restriction

open Stacks.SheafOfModules.PushforwardSheafification

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C) (G : C₀ ⥤ C)
  [G.IsContinuous J₀ J]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Restriction along `G` of sheaves of modules over a sheaf of commutative rings `B`, to
sheaves of modules over the restriction of `B`. -/
abbrev moduleSheafRestriction (B : Sheaf J CommRingCat.{w}) :
    _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⥤
      _root_.SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)) :=
  _root_.SheafOfModules.pushforward.{m}
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)) :
      _ ⟶ (G.sheafPushforwardContinuous RingCat.{w} J₀ J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- Restriction of sheaves of modules along `G` is an additive functor. -/
instance moduleSheafRestriction_additive (B : Sheaf J CommRingCat.{w}) :
    (moduleSheafRestriction.{m} J₀ J G B).Additive where
  map_add := rfl

/-- Restriction of sheaves of modules along `G` preserves zero morphisms. -/
instance moduleSheafRestriction_preservesZeroMorphisms (B : Sheaf J CommRingCat.{w}) :
    (moduleSheafRestriction.{m} J₀ J G B).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

variable [G.IsCocontinuous J₀ J] (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom]

/-- The restriction along a cocontinuous `G` of a locally surjective morphism of sheaves of
commutative rings is locally surjective. -/
instance isLocallySurjective_sheafPushforwardContinuous_map :
    Presheaf.IsLocallySurjective J₀
      ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map φ).hom :=
  Presheaf.isLocallySurjective_whisker J₀ J G φ.hom

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [G.IsCocontinuous J₀ J] [Presheaf.IsLocallySurjective J φ.hom] in
/-- The ring map along which the conormal sequence of the restriction is sheafified is the
restriction of the one for `φ`. -/
theorem quotientToRingSheaf_restriction :
    quotientToRingSheaf J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map φ) =
      Stacks.SheafOfModules.PushforwardSheafification.restrictedRingMap J₀ J G
        (quotientToRingSheaf J A B φ) := rfl

/-- **The conormal sheaf of a presentation commutes with restriction**:
`G_*(I/I²) ≅ I'/I'²` for the conormal sheaf of the restriction `G_*A ⟶ G_*B`. -/
def conormalSheafRestrictionIso :
    (moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B).obj
        (conormalSheaf.{v, u, w, max u₀ v₀ z} J A B φ) ≅
      conormalSheaf.{v₀, u₀, w, max u v z} J₀
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map φ) :=
  letI : HasSheafify J AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max w u v u₀ v₀ z, v, u} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _,
      max w u v u₀ v₀ z} J
  letI : HasSheafify J₀ AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max w u v u₀ v₀ z, v₀,
      u₀} J₀
  letI : J₀.WEqualsLocallyBijective AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v₀, _, u₀, _,
      max w u v u₀ v₀ z} J₀
  ((sheafifyAlongRestrictionIso.{w, max w u v u₀ v₀ z} J₀ J G
      (quotientToRingSheaf J A B φ)).app
    ((liftModules.{v, u, w, max u₀ v₀ z} _).obj (conormalPresheaf φ.hom))).symm

/-- **The tensor-differentials sheaf of a presentation commutes with restriction**:
`G_*(B ⊗[A] Ω[A/R]) ≅ G_*B ⊗[G_*A] Ω[G_*A/G_*R]`. -/
def tensorDifferentialsSheafRestrictionIso :
    (moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B).obj
        (tensorDifferentialsSheaf.{v, u, w, max u₀ v₀ z} J R A B a φ) ≅
      tensorDifferentialsSheaf.{v₀, u₀, w, max u v z} J₀
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj R)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map φ) :=
  letI : HasSheafify J AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max w u v u₀ v₀ z, v, u} J
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _,
      max w u v u₀ v₀ z} J
  letI : HasSheafify J₀ AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max w u v u₀ v₀ z, v₀,
      u₀} J₀
  letI : J₀.WEqualsLocallyBijective AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v₀, _, u₀, _,
      max w u v u₀ v₀ z} J₀
  ((sheafifyAlongRestrictionIso.{w, max w u v u₀ v₀ z} J₀ J G
      (quotientToRingSheaf J A B φ)).app
    ((liftModules.{v, u, w, max u₀ v₀ z} _).obj (tensorPresheaf φ.hom a.hom))).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The two restriction isomorphisms commute with the left-hand maps of the two conormal
sequences. -/
theorem conormalSheafRestrictionIso_hom_comp_conormalSequence_f :
    (moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B).map
        (conormalSequence.{v, u, w, max u₀ v₀ z} J R A B a φ).f ≫
        (tensorDifferentialsSheafRestrictionIso J₀ J G R A B a φ).hom =
      (conormalSheafRestrictionIso J₀ J G A B φ).hom ≫
        (conormalSequence.{v₀, u₀, w, max u v z} J₀
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj R)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map φ)).f := by
  let : HasSheafify J AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max w u v u₀ v₀ z, v, u} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _,
      max w u v u₀ v₀ z} J
  let : HasSheafify J₀ AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max w u v u₀ v₀ z, v₀,
      u₀} J₀
  let : J₀.WEqualsLocallyBijective AddCommGrpCat.{max w u v u₀ v₀ z} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v₀, _, u₀, _,
      max w u v u₀ v₀ z} J₀
  have e₁ : (conormalSequence.{v, u, w, max u₀ v₀ z} J R A B a φ).f =
      (PresheafOfModules.sheafification.{max w u v u₀ v₀ z} (quotientToRingSheaf J A B φ)).map
        ((liftModules.{v, u, w, max u₀ v₀ z} _).map (conormalToTensor φ.hom a.hom)) := rfl
  have e₂ : (conormalSequence.{v₀, u₀, w, max u v z} J₀
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj R)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map φ)).f =
      (PresheafOfModules.sheafification.{max w u v u₀ v₀ z}
          (Stacks.SheafOfModules.PushforwardSheafification.restrictedRingMap J₀ J G
            (quotientToRingSheaf J A B φ))).map
        ((PresheafOfModules.pushforward₀ G _).map
          ((liftModules.{v, u, w, max u₀ v₀ z} _).map (conormalToTensor φ.hom a.hom))) := rfl
  rw [e₁, e₂]
  exact (sheafifyAlongRestrictionIso.{w, max w u v u₀ v₀ z} J₀ J G
      (quotientToRingSheaf J A B φ)).inv.naturality
    ((liftModules.{v, u, w, max u₀ v₀ z} _).map (conormalToTensor φ.hom a.hom))

end Restriction

end Stacks.Sites.Conormal

/-! ### The naive cotangent complex commutes with restriction -/

namespace Stacks.SheafOfModules

section Restriction

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C) (G : C₀ ⥤ C)
  [G.IsContinuous J₀ J] [G.IsCocontinuous J₀ J]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J₀ CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ F : C₀ᵒᵖ ⥤ CommRingCat.{w}, G.op.HasPointwiseRightKanExtension F]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- A commutation of composites of isomorphisms, from the commutation of its pieces: the square
of terms of two two-term complexes built from three isomorphisms in each degree. -/
theorem trans_symm_trans_hom_comp_eq {𝒞 : Type*} [Category* 𝒞]
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : 𝒞} (c₁ : X₁ ≅ Y₁) (t₁ : Z₁ ≅ Y₁) (x : Z₁ ≅ W₁)
    (c₂ : X₂ ≅ Y₂) (t₂ : Z₂ ≅ Y₂) (y : Z₂ ≅ W₂) (s : X₁ ⟶ X₂) (s₀ : Z₁ ⟶ Z₂) (s' : Y₁ ⟶ Y₂)
    (d : W₁ ⟶ W₂) (hd : d = x.inv ≫ s₀ ≫ y.hom) (h₁ : s ≫ c₂.hom = c₁.hom ≫ s')
    (h₂ : t₁.hom ≫ s' = s₀ ≫ t₂.hom) :
    (c₁ ≪≫ t₁.symm ≪≫ x).hom ≫ d = s ≫ (c₂ ≪≫ t₂.symm ≪≫ y).hom := by
  have h₃ : s' ≫ t₂.inv = t₁.inv ≫ s₀ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, h₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hd]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h₁, reassoc_of% h₃]

/-- The canonical presentation is locally surjective, in the form the conormal sequence
uses. -/
theorem isLocallySurjective_canonicalPresentation_hom {C' : Type*} [Category* C']
    (K : GrothendieckTopology C') [HasWeakSheafify K CommRingCat.{w}]
    (A' B' : Sheaf K CommRingCat.{w}) (a' : A' ⟶ B') :
    Presheaf.IsLocallySurjective K (canonicalPresentation K A' B' a').hom := by
  exact canonicalPresentation_isLocallySurjective K A' B' a'

/-- The two presentations of `G_*B`: the canonical one and the restriction of the canonical
presentation of `B`, identified by `Stacks.Sites.FreeAlgebra.freeAlgebraSheafRestrictionIso`. -/
abbrev restrictionPresentationIso :=
  freeAlgebraSheafRestrictionIso J₀ J G A (underlyingPresheaf J B)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The identification `restrictionPresentationIso` carries the canonical presentation of `G_*B`
over `G_*A` to the restriction of the canonical presentation of `B` over `A`. -/
theorem restrictionPresentationIso_hom_comp :
    (restrictionPresentationIso J₀ J G A B).hom ≫
        (G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (canonicalPresentation J A B a) =
      canonicalPresentation J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) :=
  freeAlgebraSheafRestrictionIso_hom_comp_canonicalPresentation J₀ J G A B a

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The identification `restrictionPresentationIso` is one of `G_*A`-algebras. -/
theorem coefficientMap_comp_restrictionPresentationIso_hom :
    freeAlgebraSheafCoefficientMap J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        (underlyingPresheaf J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)) ≫
        (restrictionPresentationIso J₀ J G A B).hom =
      (G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) :=
  freeAlgebraSheafCoefficientMap_comp_restrictionIso_hom J₀ J G A (underlyingPresheaf J B)

/-- The degree `-1` comparison of `Stacks.SheafOfModules.naiveCotangentComplexRestrictionIso`. -/
def naiveCotangentComplexRestrictionNegOneIso :
    (moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B).obj
        (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).X₁ ≅
      (naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).X (-1) :=
  haveI := isLocallySurjective_canonicalPresentation_hom J₀
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)
  haveI := isLocallySurjective_canonicalPresentation_hom J A B a
  conormalSheafRestrictionIso.{w, v₀, u₀, v, u, z} J₀ J G _ B (canonicalPresentation J A B a) ≪≫
    (conormalSheafIsoOfFac.{v₀, u₀, w, max u v z} J₀ ((G.sheafPushforwardContinuous CommRingCat.{w}
        J₀ J).obj B) (freeAlgebraSheaf J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj
        A) (underlyingPresheaf J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj (freeAlgebraSheaf J A
        (underlyingPresheaf J B)))
      (canonicalPresentation J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a))
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (canonicalPresentation J A B a))
      (restrictionPresentationIso J₀ J G A B) (restrictionPresentationIso_hom_comp J₀ J G A B
          a)).symm ≪≫
    (naiveCotangentComplexXNegOneIso.{u₀, v₀, w, max u v z} J₀ _ _ _).symm

/-- The degree `0` comparison of `Stacks.SheafOfModules.naiveCotangentComplexRestrictionIso`. -/
def naiveCotangentComplexRestrictionZeroIso :
    (moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B).obj
        (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).X₂ ≅
      (naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).X 0 :=
  haveI := isLocallySurjective_canonicalPresentation_hom J₀
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)
  haveI := isLocallySurjective_canonicalPresentation_hom J A B a
  tensorDifferentialsSheafRestrictionIso.{w, v₀, u₀, v, u, z} J₀ J G A _ B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a) ≪≫
    (tensorSheafIsoOfFac.{v₀, u₀, w, max u v z} J₀ ((G.sheafPushforwardContinuous CommRingCat.{w}
        J₀ J).obj A) ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B) (freeAlgebraSheaf
        J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A) (underlyingPresheaf J₀
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)))
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj (freeAlgebraSheaf J A
        (underlyingPresheaf J B)))
      (freeAlgebraSheafCoefficientMap J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj
          A) (underlyingPresheaf J₀ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)))
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (freeAlgebraSheafCoefficientMap
          J A (underlyingPresheaf J B))) (canonicalPresentation J₀ ((G.sheafPushforwardContinuous
          CommRingCat.{w} J₀ J).obj A) ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a))
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (canonicalPresentation J A B a))
      (restrictionPresentationIso J₀ J G A B) (restrictionPresentationIso_hom_comp J₀ J G A B a)
      (coefficientMap_comp_restrictionPresentationIso_hom J₀ J G A B)).symm ≪≫
    (naiveCotangentComplexXZeroIso.{u₀, v₀, w, max u v z} J₀ _ _ _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The two comparisons commute with the differentials. -/
theorem naiveCotangentComplexRestriction_comm :
    (naiveCotangentComplexRestrictionNegOneIso J₀ J G A B a).hom ≫
        (naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).d (-1) 0 =
      (moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B).map
          (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).f ≫
        (naiveCotangentComplexRestrictionZeroIso J₀ J G A B a).hom := by
  have := isLocallySurjective_canonicalPresentation_hom J₀
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)
  have := isLocallySurjective_canonicalPresentation_hom J A B a
  have h₂ := conormalSheafIsoOfFac_hom_comp_conormalSequence_f.{v₀, u₀, w, max u v z} J₀ _ _ _ _ _
    _ (canonicalPresentation J₀ _ _ ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a))
    ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (canonicalPresentation J A B a))
    (restrictionPresentationIso J₀ J G A B) (restrictionPresentationIso_hom_comp J₀ J G A B a)
    (coefficientMap_comp_restrictionPresentationIso_hom J₀ J G A B)
  exact trans_symm_trans_hom_comp_eq _ _ _ _ _ _ _ _ _ _
    (naiveCotangentComplex_d_negOne_zero_iso.{u₀, v₀, w, max u v z} J₀ _ _ _)
    (conormalSheafRestrictionIso_hom_comp_conormalSequence_f.{w, v₀, u₀, v, u, z} J₀ J G A _ B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (canonicalPresentation J A B a)) h₂

/-- **The naive cotangent complex commutes with restriction along a continuous and cocontinuous
functor**: `G_* NL_{B/A} ≅ NL_{G_*B/G_*A}`, as complexes of sheaves of `G_*B`-modules. In each
degree it is the restriction of the term of the conormal sequence of `A[B] ⟶ B`
(`Stacks.Sites.Conormal.conormalSheafRestrictionIso`,
`Stacks.Sites.Conormal.tensorDifferentialsSheafRestrictionIso`) followed by the transport along
the identification `(G_*A)[G_*B] ≅ G_*(A[B])` of the two presentations of `G_*B`. -/
def naiveCotangentComplexRestrictionIso :
    ((moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a) ≅
      naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀ ((G.sheafPushforwardContinuous
          CommRingCat.{w} J₀ J).obj A) ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) := by
  letI : HasZeroObject
      (_root_.SheafOfModules.{max w u v u₀ v₀ z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  letI : HasZeroObject
      (_root_.SheafOfModules.{max w u v u₀ v₀ z} (Stacks.SheafOfModules.Tensor.ringSheaf
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B))) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.isoFromMapDouble
    (moduleSheafRestriction.{max w u v u₀ v₀ z} J₀ J G B)
    (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (naiveCotangentComplexRestrictionNegOneIso J₀ J G A B a)
    (naiveCotangentComplexRestrictionZeroIso J₀ J G A B a)
    (naiveCotangentComplexRestriction_comm J₀ J G A B a)
    (fun k _ ↦ by
      rw [naiveCotangentComplex_d_zero_eq_zero.{u₀, v₀, w, max u v z} J₀
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) k,
        Limits.comp_zero])
    (naiveCotangentComplex_isZero_X.{v₀, u₀, w, max u v z} J₀ ((G.sheafPushforwardContinuous
        CommRingCat.{w} J₀ J).obj A) ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((G.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a))

end Restriction

end Stacks.SheafOfModules

end
