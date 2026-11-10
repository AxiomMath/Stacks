module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetCoinduction
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleRingedModules
public import StacksFrontier.AlgebraicGeometry.Topologies.SubcategoryStructureSheafLowerShriek
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare

/-!
# `g_!` on modules agrees with `g_!` on abelian sheaves (Stacks 0789)

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids carrying the site of **Stacks 06TP**, and
let `P` cut out a full subcategory `𝒳'` whose inclusion is continuous and cocontinuous for the
inherited topology. `StacksFrontier/AlgebraicGeometry/Stacks/SubcategoryModuleLowerShriek.lean`
builds the lower shriek `g_! : Mod(𝒳', O_{𝒳'}) ⥤ Mod(𝒳, O_𝒳)` on sheaves of modules, left adjoint
to `g^*`, and proves `g^*g_! = id`. Each clause of **Stacks 0789** asserts besides that `g_!`
*agrees with the functor `g_!` on abelian sheaves*: forgetting the module structure of `g_!M`
gives the lower shriek of the underlying abelian sheaf of `M`. This file proves that assertion,
for every full subsite closed under smooth morphisms, and so for the lisse-étale and the
flat-fppf site of every algebraic stack.

## The proof

The source shows that the maps (0799) of **Stacks 0798** are isomorphisms by **Étale Cohomology,
Lemma 07AJ**, applied to the slices `𝒳'/x ⊆ 𝒳/x ≃ (Sch/U)`. The same mathematics is used here in
the form of
`Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_of_bijective`: the canonical comparison
of Stacks 0798 is an isomorphism as soon as, for every object `x` of `𝒳'`, restriction along
`𝒳'/x ⥤ 𝒳/x` is bijective on morphisms of abelian presheaves out of the structure sheaf of
`𝒳/x`. That is the presheaf half of 07AJ (b) on the slice, and it holds because on `𝒳/x` the
structure sheaf is represented by the affine line over the scheme `U` under `x`, and its square
by the affine plane (`AlgebraicGeometry.Stack.exists_represent_affineSpace`, via the equivalence
`𝒳/x ≃ (Sch/U)` of **Stacks 06W0**); the two lie over smooth morphisms to `U`, hence in `𝒳'/x`.

## Main results

* `AlgebraicGeometry.Stack.bijective_whiskerLeft_overPost_structureSheaf`: Stacks 07AJ (b), at
  the level of presheaves, on the slices of a full subsite closed under smooth morphisms.
* `AlgebraicGeometry.Stack.isIso_lowerShriekForgetComparison_subsite`: the comparison of
  Stacks 0798 is invertible for such a subsite.
* `AlgebraicGeometry.Stack.subsiteModuleLowerShriekForgetIso`: hence
  `forget ∘ g_! ≅ g_!^{Ab} ∘ forget` for `g_! = AlgebraicGeometry.Stack.subsiteModuleLowerShriek`.
* `AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriekForgetIso` and
  `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekForgetIso`: the assertion "it agrees with the
  functor `g_!` on abelian sheaves" of **Stacks 0789** (1) and (2), for every algebraic stack.

## Implementation notes

The abelian sheaves are those with values in `AddCommGrpCat.{u}`, the universe of the sections of
the modules, so that "forgetting the module structure" is `SheafOfModules.toSheaf`. Lower shriek
on them is `CategoryTheory.Functor.sheafPullback`, the left adjoint of restriction of abelian
sheaves along the inclusion, which is the construction of **Stacks 0788** (d) at that coefficient
universe; it exists because the subsite is essentially small
(`AlgebraicGeometry.Stack.hasPointwiseLeftKanExtension_subsite`).

The comparison is stated in `Stacks.SheafOfModules.lowerShriekForgetComparison` for Mathlib's
`SheafOfModules.pullback`, the left adjoint of restriction of modules, and transported to
`subsiteModuleLowerShriek` — the left adjoint of the pullback `g^*` of Stacks 03D6 — through
`g^* = g^{-1}` (`AlgebraicGeometry.Stack.subsiteModulePullbackRestrictionIso`). The two four-field
readings of the morphism of ringed topoi involved there are *equal*
(`AlgebraicGeometry.Stack.toModulesHom_subsiteRingedToposHom`), so that step is an `eqToIso`.

## References

* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 07AJ](https://stacks.math.columbia.edu/tag/07AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

section Representability

include hp in
/-- **Affine `n`-space over the scheme under an object `x` of a category fibred in groupoids is an
object of the slice `𝒳/x`.** There is an object `A ⟶ x` of the slice, lying over a smooth morphism
of schemes, carrying an `n`-tuple of global functions on the scheme under `A` such that a morphism
`V ⟶ A` of the slice is the same thing as an `n`-tuple of global functions on the scheme under
`V`, by pulling back the tuple. -/
theorem exists_represent_affineSpace (x : X) (n : Type u) [Finite n] :
    ∃ (A : Over x) (s : n → Γ((BigFppfOver.toScheme B S hS).obj (p.obj A.left), ⊤)),
      Smooth (B.inclusion.map (p.map A.hom).left) ∧
      ∀ V : Over x, Function.Bijective fun f : V ⟶ A => fun i =>
        ((BigFppfOver.toScheme B S hS).map (p.map f.left)).appTop (s i) := by
  let q := p ⋙ Over.forget (B.obj hS)
  let E := Over.post (X := x) q
  have : E.IsEquivalence := isEquivalence_overPost B S hS p hp x
  let T := q.obj x
  let Y : Scheme.{u} := B.inclusion.obj T
  have hY : B.Contains Y := T.property
  have hA : B.Contains 𝔸(n; Y) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (𝔸(n; Y) ↘ Y) hY
  let L : BigFppfOver B Y hY := BigFppfOver.mk B Y hY hA (𝔸(n; Y) ↘ Y)
  let A := E.objPreimage L
  let iA : E.obj A ≅ L := E.objObjPreimageIso L
  let e : (BigFppfOver.toScheme B Y hY).obj (E.obj A) ≅ 𝔸(n; Y) :=
    (BigFppfOver.toScheme B Y hY).mapIso iA
  have he : e.hom ≫ (𝔸(n; Y) ↘ Y) = BigFppfOver.str B Y hY (E.obj A) := by
    change B.inclusion.map iA.hom.left ≫ B.inclusion.map L.hom = B.inclusion.map (E.obj A).hom
    rw [← B.inclusion.map_comp, Over.w iA.hom]
  refine ⟨A, fun i => e.hom.appTop (AffineSpace.coord Y i), ?_, fun V => ?_⟩
  · have hc : B.inclusion.map (p.map A.hom).left = e.hom ≫ (𝔸(n; Y) ↘ Y) := he.symm
    have : Smooth (𝔸(n; Y) ↘ Y) := affineSpace_smooth_over
    rw [hc]
    exact smooth_comp e.hom _
  · exact (bijective_map_coord e he (E.obj V)).comp ⟨E.map_injective, E.map_surjective⟩

end Representability

section Subsite

open Stacks.SheafOfModules Stacks.SheafOfModules.AbelianCoinduction

variable (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)

variable [EssentiallySmall.{u} X]

/-- The category of presheaves of abelian groups on the slice `X/x` is locally `u`-small. -/
instance locallySmall_overFunctor (x : X) :
    LocallySmall.{u} ((Over x)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  CategoryTheory.locallySmall_functor_of_essentiallySmall _ _

/-- The category of presheaves of abelian groups on the slice over `x` of the full subcategory cut
out by `P` is locally `u`-small. -/
instance locallySmall_overFunctor_subsite (x : P.FullSubcategory) :
    LocallySmall.{u} ((Over x)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  CategoryTheory.locallySmall_functor_of_essentiallySmall _ _

/-- The structure sheaf of **Stacks 06TV**, as a sheaf of rings. -/
abbrev associatedRingSheaf :=
  Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O

include hp in
omit [EssentiallySmall.{u, w, v} X] in
/-- **The structure sheaf of a slice of the site of a category fibred in groupoids is the left
Kan extension of its restriction to the slice of a full subcategory closed under smooth
morphisms.** For an object `V` of the full subcategory `𝒳'` cut out by `P`, restriction along
`Over.post : 𝒳'/V ⥤ 𝒳/V` is bijective on morphisms of abelian presheaves out of the structure
sheaf of `𝒳/V`.

This is the presheaf half of **Stacks 07AJ** (b) on the slice, which the source identifies with
`(Sch/U)_τ` for the scheme `U` under `V`: the structure presheaf of `𝒳/V` is represented by the
affine line over `U`, and its square by the affine plane, and both lie in `𝒳'/V` because they lie
over smooth morphisms to `U`. -/
theorem bijective_whiskerLeft_overPost_structureSheaf
    (hP : ∀ ⦃a b : X⦄ (f : a ⟶ b), Smooth (B.inclusion.map (p.map f).left) → P b → P a)
    (V : P.FullSubcategory) (G : (Over (P.ι.obj V))ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Function.Bijective fun β : (Over.forget (P.ι.obj V)).op ⋙
        ab (associatedRingSheaf B S hS p hp τ hτ).obj ⟶ G =>
      Functor.whiskerLeft (Over.post (X := V) P.ι).op β := by
  obtain ⟨A, s, hsm, hs⟩ := exists_represent_affineSpace B S hS p hp (P.ι.obj V) PUnit.{u + 1}
  obtain ⟨A', s', hsm', hs'⟩ :=
    exists_represent_affineSpace B S hS p hp (P.ι.obj V) AffinePlaneIndex.{u}
  let A₁ : Over V := Over.mk (Y := ⟨A.left, hP A.hom hsm V.property⟩) (ObjectProperty.homMk A.hom)
  let A₂ : Over V :=
    Over.mk (Y := ⟨A'.left, hP A'.hom hsm' V.property⟩) (ObjectProperty.homMk A'.hom)
  refine CategoryTheory.Presheaf.bijective_whiskerLeft (A := A₁) (A' := A₂) (s := s PUnit.unit)
    (x₀ := s' (ULift.up false)) (x₁ := s' (ULift.up true)) (fun W => ?_) (fun W => ?_)
  · exact (Equiv.funUnique PUnit.{u + 1} _).bijective.comp (hs W)
  · exact (affinePlaneIndexArrowEquiv _).bijective.comp (hs' W)

variable [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- The two readings of the morphism of ringed topoi of a full subsite as a four-field morphism of
ringed topoi, the one the pullback `g^*` of **Stacks 03D6** is stated for by
`AlgebraicGeometry.Stack.subsiteModulePullback` and the one
`AlgebraicGeometry.Stack.subsiteModulePullbackIso` identifies with restriction, are equal. -/
theorem toModulesHom_subsiteRingedToposHom :
    (subsiteRingedToposHom B S hS p hp τ hτ P).toModulesHom =
      subsiteRingedToposModulesHom B S hS p hp τ hτ P := by
  refine (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
    (subsiteRingedToposHom B S hS p hp τ hτ P)).trans ?_
  unfold RingedToposHom.toRingedToposModulesHom subsiteRingedToposModulesHom
    Stacks.Sheaves.RingedToposModules.RingedToposHom.ofFSharpInverseImage
  rfl

/-- The restriction of the structure sheaf to the full subsite, as the sheaf of rings that the
pullback `g^*` of sheaves of modules lands over. -/
abbrev subsiteRingSheaf :=
  (P.ι.sheafPushforwardContinuous RingCat.{u} (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ)).obj (associatedRingSheaf B S hS p hp τ hτ)

/-- **`g^* = g^{-1}` on sheaves of modules, for the pullback `g^*` that `g_!` is the left adjoint
of.** `AlgebraicGeometry.Stack.subsiteModulePullbackIso` read at the spelling
`AlgebraicGeometry.Stack.subsiteModulePullback` of the pullback. -/
def subsiteModulePullbackRestrictionIso :
    subsiteModulePullback B S hS p hp τ hτ P ≅
      SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS p hp τ hτ P)) :=
  eqToIso (by
      unfold subsiteModulePullback
      rw [toModulesHom_subsiteRingedToposHom]) ≪≫
    subsiteModulePullbackIso B S hS p hp τ hτ P

/-- Pushforward of sheaves of modules along the identity of the restricted structure sheaf of the
full subsite is a right adjoint. -/
instance isRightAdjoint_pushforward_subsiteRingSheaf :
    (SheafOfModules.pushforward.{u} (𝟙 (subsiteRingSheaf B S hS p hp τ hτ P))).IsRightAdjoint :=
  @Functor.isRightAdjoint_of_iso _ _ _ _ _ _
    (subsiteModulePullbackRestrictionIso B S hS p hp τ hτ P)
    (isRightAdjoint_subsiteModulePullback B S hS p hp τ hτ P)

/-- The lower shriek `g_!` on sheaves of modules of
`AlgebraicGeometry.Stack.subsiteModuleLowerShriek` is Mathlib's `SheafOfModules.pullback` along the
identity of the restricted structure sheaf, the left adjoint of restriction of sheaves of modules
along the inclusion: both are left adjoint to `g^* = g^{-1}`. -/
def subsiteModuleLowerShriekIsoPullback :
    subsiteModuleLowerShriek B S hS p hp τ hτ P ≅
      @SheafOfModules.pullback.{u} _ _ _ _ _ _ _ _ _ _
        (𝟙 (subsiteRingSheaf B S hS p hp τ hτ P))
        (isRightAdjoint_pushforward_subsiteRingSheaf B S hS p hp τ hτ P) :=
  (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).leftAdjointUniq
    ((@SheafOfModules.pullbackPushforwardAdjunction.{u} _ _ _ _ _ _ _ _ _ _
      (𝟙 (subsiteRingSheaf B S hS p hp τ hτ P))
      (isRightAdjoint_pushforward_subsiteRingSheaf B S hS p hp τ hτ P)).ofNatIsoRight
        (subsiteModulePullbackRestrictionIso B S hS p hp τ hτ P).symm)

/-- Restriction of abelian presheaves along the inclusion of a full subsite has pointwise left Kan
extensions, the subsite being essentially small. -/
instance hasPointwiseLeftKanExtension_subsite (G : P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{u}) :
    P.ι.op.HasPointwiseLeftKanExtension G := fun Y => by
  have :=
    hasColimitsOfShape_of_essentiallySmall.{u} (CostructuredArrow P.ι.op Y) AddCommGrpCat.{u}
  infer_instance

/-- **The comparison of Stacks 0798 is an isomorphism for a full subsite closed under smooth
morphisms**: lower shriek of sheaves of modules along the inclusion agrees with lower shriek of
the underlying abelian sheaves. -/
theorem isIso_lowerShriekForgetComparison_subsite
    (hP : ∀ ⦃a b : X⦄ (f : a ⟶ b), Smooth (B.inclusion.map (p.map f).left) → P b → P a) :
    IsIso (lowerShriekForgetComparison P.ι (𝟙 (subsiteRingSheaf B S hS p hp τ hτ P))) :=
  isIso_lowerShriekForgetComparison_of_bijective P.ι (associatedRingSheaf B S hS p hp τ hτ)
    (bijective_whiskerLeft_overPost_structureSheaf B S hS p hp τ hτ P hP)

/-- **`g_!` on sheaves of modules agrees with `g_!` on abelian sheaves**, for a full subsite closed
under smooth morphisms: forgetting the module structure of `g_!M` gives the lower shriek of the
underlying abelian sheaf of `M`, naturally in `M`. The isomorphism is the comparison of
**Stacks 0798**, read through the identification of
`AlgebraicGeometry.Stack.subsiteModuleLowerShriek` with the left adjoint of restriction of
modules. -/
def subsiteModuleLowerShriekForgetIso
    (hP : ∀ ⦃a b : X⦄ (f : a ⟶ b), Smooth (B.inclusion.map (p.map f).left) → P b → P a) :
    SheafOfModules.toSheaf _ ⋙ P.ι.sheafPullback AddCommGrpCat.{u}
        (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ) ≅
      subsiteModuleLowerShriek B S hS p hp τ hτ P ⋙ SheafOfModules.toSheaf _ :=
  @asIso _ _ _ _ (lowerShriekForgetComparison P.ι (𝟙 (subsiteRingSheaf B S hS p hp τ hτ P)))
      (isIso_lowerShriekForgetComparison_subsite B S hS p hp τ hτ P hP) ≪≫
    Functor.isoWhiskerRight (subsiteModuleLowerShriekIsoPullback B S hS p hp τ hτ P).symm _

end Subsite

/-! ### The lisse-étale site -/

namespace LisseEtale

universe t

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Stacks 0789 (1), `g_!` on modules agrees with `g_!` on abelian sheaves.** For the lisse-étale
site of an arbitrary algebraic stack `𝒳`, the underlying abelian sheaf of `g_!M`, for `g_!` the
lower shriek `AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriek` on sheaves of modules, is the
lower shriek of the underlying abelian sheaf of `M`, for `g_!` the left adjoint of restriction of
abelian sheaves along the inclusion of the smooth objects (**Stacks 0788** (1)(d)); naturally in
`M`. The abelian sheaves are taken at the universe of the module sections, which is where the
underlying abelian sheaves of the modules live.

The isomorphism is the canonical comparison of **Stacks 0798**
(`Stacks.SheafOfModules.lowerShriekForgetComparison`), which is invertible here because the
structure sheaf of each slice `𝒳_étale/x` is the left Kan extension of its restriction to
`𝒳_{lisse,étale}/x` (**Stacks 07AJ** on the slice; see
`AlgebraicGeometry.Stack.bijective_whiskerLeft_overPost_structureSheaf`). -/
@[stacks 0789 "part (1), `g_!` on sheaves of modules agrees with `g_!` on abelian sheaves, for \
the lisse-étale site of an arbitrary algebraic stack"]
def moduleLowerShriekForgetIso :
    SheafOfModules.toSheaf _ ⋙ (smoothObject.{u, t} B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u}
        (inclusionTopology.{u, t} B S hS 𝒳)
        (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) ≅
      moduleLowerShriek.{u, t} B S hS 𝒳 ⋙ SheafOfModules.toSheaf _ :=
  subsiteModuleLowerShriekForgetIso B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, t} B S hS 𝒳)
    (closedUnderSmoothMorphisms.{u, t} B S hS 𝒳)

/-- **Stacks 0789 (1)**, the whole part, for the lisse-étale site of an arbitrary algebraic stack
`𝒳`: the pullback `g^*` of sheaves of modules has a left adjoint `g_!`
(`AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriek`, with adjunction
`AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriekAdjunction`); `g_!` agrees with the functor
`g_!` on abelian sheaves, i.e. forgetting the module structure commutes with it
(`AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriekForgetIso`); and `g^*g_! = id`, the unit of
the adjunction being an isomorphism. -/
@[stacks 0789 "part (1), all four assertions, for the lisse-étale site of an arbitrary algebraic \
stack"]
theorem moduleLowerShriek_spec :
    (modulePullback.{u, t} B S hS 𝒳).IsRightAdjoint ∧
      Nonempty (SheafOfModules.toSheaf _ ⋙
          (smoothObject.{u, t} B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u}
            (inclusionTopology.{u, t} B S hS 𝒳)
            (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) ≅
        moduleLowerShriek.{u, t} B S hS 𝒳 ⋙ SheafOfModules.toSheaf _) ∧
      IsIso (moduleLowerShriekAdjunction.{u, t} B S hS 𝒳).unit :=
  ⟨isRightAdjoint_modulePullback.{u, t} B S hS 𝒳, ⟨moduleLowerShriekForgetIso B S hS 𝒳⟩,
    isIso_moduleLowerShriekAdjunction_unit.{u, t} B S hS 𝒳⟩

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

universe t

variable (𝒳 : Stack.AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Stacks 0789 (2), `g_!` on modules agrees with `g_!` on abelian sheaves.** For the flat-fppf
site of an arbitrary algebraic stack `𝒳`, the underlying abelian sheaf of `g_!M`, for `g_!` the
lower shriek `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriek` on sheaves of modules, is the
lower shriek of the underlying abelian sheaf of `M`, for `g_!` the left adjoint of restriction of
abelian sheaves along the inclusion of the flat objects (**Stacks 0788** (2)(d)); naturally in
`M`. The abelian sheaves are taken at the universe of the module sections.

The isomorphism is the canonical comparison of **Stacks 0798**, invertible because the structure
sheaf of each slice `𝒳_fppf/x` is the left Kan extension of its restriction to
`𝒳_{flat,fppf}/x` (**Stacks 07AJ** on the slice): the affine line and plane over a flat object are
flat objects. -/
@[stacks 0789 "part (2), `g_!` on sheaves of modules agrees with `g_!` on abelian sheaves, for \
the flat-fppf site of an arbitrary algebraic stack"]
def moduleLowerShriekForgetIso :
    SheafOfModules.toSheaf _ ⋙ (objectProperty B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u}
        (inclusionTopology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology) ≅
      moduleLowerShriek B S hS 𝒳 ⋙ SheafOfModules.toSheaf _ :=
  subsiteModuleLowerShriekForgetIso B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
    le_rfl (objectProperty B S hS 𝒳)
    (fun _ _ f _ hy => closedUnderFlatMorphisms B S hS 𝒳 f inferInstance inferInstance hy)

/-- **Stacks 0789 (2)**, the whole part, for the flat-fppf site of an arbitrary algebraic stack
`𝒳`: the pullback `g^*` of sheaves of modules has a left adjoint `g_!`
(`AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriek`, with adjunction
`AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekAdjunction`); `g_!` agrees with the functor
`g_!` on abelian sheaves, i.e. forgetting the module structure commutes with it
(`AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekForgetIso`); and `g^*g_! = id`, the unit of
the adjunction being an isomorphism. -/
@[stacks 0789 "part (2), all four assertions, for the flat-fppf site of an arbitrary algebraic \
stack"]
theorem moduleLowerShriek_spec :
    (modulePullback B S hS 𝒳).IsRightAdjoint ∧
      Nonempty (SheafOfModules.toSheaf _ ⋙
          (objectProperty B S hS 𝒳).ι.sheafPullback AddCommGrpCat.{u}
            (inclusionTopology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology) ≅
        moduleLowerShriek B S hS 𝒳 ⋙ SheafOfModules.toSheaf _) ∧
      IsIso (moduleLowerShriekAdjunction B S hS 𝒳).unit :=
  ⟨isRightAdjoint_modulePullback' B S hS 𝒳, ⟨moduleLowerShriekForgetIso B S hS 𝒳⟩,
    isIso_moduleLowerShriekAdjunction_unit B S hS 𝒳⟩

end FlatFppf

end AlgebraicGeometry.Stack
